module imper-nouni where

--
-- TO-DOs
--
-- * change use of =string
-- * prove that =string can't be both tt and ff
-- * prove reverse theorems for passes/fails/chck
-- * prove semantic equivalence for execs and execsTo
--    + this would be s-thm and s-det

open import lib
open import eq-reas-nouni

_=nat_ = _=ℕ_

_-nat_ = _∸_

cross = _×_

equiv = _≡_

bottom = ⊥

bottom-elim = ⊥-elim

--
-- inspect/with-eq idiom
--

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with-eq_ : (y : A) → equiv x y → Singleton x

inspect : forall {a} {A : Set a} (x : A) -> Singleton x
inspect x = x with-eq refl

--
-- variable identifiers
--
Id : Set
Id = string

_=Id_ : Id -> Id -> bool
_=Id_ = _=string_

--
-- values (just natural numbers here)
--

Val : Set
Val = nat

--
-- value and variable expressions
--
data Expn : Set where
  val : Val -> Expn
  var : Id -> Expn
  plus : Expn -> Expn -> Expn
  minus : Expn -> Expn -> Expn
  scaleBy : Expn -> Val -> Expn

--
-- conditions on values and variables
--
data Cond : Set where
  true : Cond
  false : Cond
  and : Cond -> Cond -> Cond
  or : Cond -> Cond -> Cond
  not : Cond -> Cond
  less : Expn -> Expn -> Cond
  equal : Expn -> Expn -> Cond

--
-- stack frames containing variable bindings
--
Frm : Set
Frm = list (cross Id Val)

--
-- program statements that transform a frame
--
data Stmt : Set where
  skip : Stmt
  assign : Id -> Expn -> Stmt
  seq : Stmt -> Stmt -> Stmt
  ifThenElse : Cond -> Stmt -> Stmt -> Stmt
  repeatBy : Id -> Stmt -> Stmt
  returns : Expn -> Stmt

--
-- functional SEMANTICS of frames
--

lkup : Id -> Frm -> Val
lkup x [] = 0
lkup x ((y , w) :: F) = if (x =Id y) then w else (lkup x F)

update : Id -> Val -> Frm -> Frm
update x v [] = (x , v) :: []
update x v ((y , w) :: F)  
          = if (x =Id y)
              then (y , v) :: F
              else (y , w) :: (update x v F)
--
-- functional SEMANTICS of expressions
--
eval : Expn -> Frm -> Val
eval (val v) F = v
eval (var x) F = lkup x F
eval (plus e1 e2) F = (eval e1 F) + (eval e2 F)
eval (minus e1 e2) F = (eval e1 F) -nat (eval e2 F)
eval (scaleBy e1 v2) F = (eval e1 F) * v2

--
-- functional SEMANTICS of conditions
--
chck : Cond -> Frm -> bool
chck true F = tt
chck false F = ff
chck (and c1 c2) F = (chck c1 F) && (chck c2 F)
chck (or c1 c2) F = (chck c1 F) || (chck c2 F)
chck (not c) F = ~ (chck c F)
chck (less e1 e2) F = (eval e1 F) < (eval e2 F)
chck (equal e1 e2) F = (eval e1 F) =nat (eval e2 F)

--
-- functional SEMANTICS of program execution
--
exec : Stmt -> Frm -> Frm
repeatedly : Stmt -> Id -> nat -> Frm -> Frm
repeatedly s x 0 F = F
repeatedly s x (suc n) F = repeatedly s x n (update x n (exec s F))
exec skip F = F
exec (seq s1 s2) F = (exec s2 (exec s1 F))
exec (assign x e) F = (update x (eval e F) F)
exec (ifThenElse c s1 s2) F = if (chck c F) then (exec s1 F) else (exec s2 F)
exec (repeatBy x s) F = repeatedly s x (lkup x F) F
exec (returns e) F = (update "retval" (eval e F) F)

--
-- SEMANTICS of stack bindings as a relation
--
data mapsTo : Frm -> Id -> Val -> Set where

  var-undef : forall {x : Id}
              ----------------
              -> (mapsTo [] x 0)

  var-match : forall {x y : Id} {F : Frm} {v : Val}
              -> (equiv (x =string y) tt)
              ---------------------------
              -> (mapsTo ((y , v) :: F) x v) 

  var-mismatch : forall {x y : Id} {F : Frm} {v w : Val}
                 -> (equiv (x =string y) ff)
                 -> (mapsTo F x v)
                 ----------------------------
                 -> (mapsTo ((y , w) :: F) x v)

--
-- THEOREM: mapsTo agrees with lookup
--
var-thm : forall (x : Id) (F : Frm) -> mapsTo F x (lkup x F)
var-thm x [] = var-undef
var-thm x ((y , w) :: F)
     with (inspect (x =string y))
...     | tt with-eq match =
            let lkup-is-w : (equiv (lkup x ((y , w) :: F)) w)
                lkup-is-w = cong3 if_then_else_ match refl refl
             in cong-pred (mapsTo ((y , w) :: F) x) (sym lkup-is-w) (var-match match)
...     | ff with-eq mismatch = 
            let lkup-is-lkup : (equiv (lkup x ((y , w) :: F)) (lkup x F))
                lkup-is-lkup = cong3 if_then_else_ mismatch refl refl
             in cong-pred (mapsTo ((y , w) :: F) x) (sym lkup-is-lkup) (var-mismatch mismatch (var-thm x F))

postulate
  =Id-det : ∀ {x y : Id} -> (equiv (x =string y) tt) -> (equiv (x =string y) ff) -> bottom
  
var-det : forall{x : Id}{F : Frm}{u1 u2 : Val}
    -> mapsTo F x u1 -> mapsTo F x u2 -> equiv u1 u2
var-det{x}{[]}{u1}{u2} var-undef var-undef =
  refl
var-det{x}{(y , w) :: F}{u1}{u2} (var-match _) (var-match _) =
  refl
var-det{x}{(y , w) :: F}{u1}{u2} (var-mismatch _ lkup-is-u1) (var-mismatch _ lkup-is-u2) =
  var-det lkup-is-u1 lkup-is-u2
var-det{x}{(y , w) :: F}{u1}{u2} (var-match{.x}{.y}{.F}{.u1} same) (var-mismatch{.x}{.y}{.F}{.u2} diff _) =
  bottom-elim (=Id-det{x}{y} same diff)
var-det{x}{(y , w) :: F}{u1}{u2} (var-mismatch{.x}{.y}{.F}{.u1} diff _) (var-match{.x}{.y}{.F}{.u2} same) =
  bottom-elim (=Id-det{x}{y} same diff)

--
-- SEMANTICS of expression evaluation as a relation
--

data evalsTo : Frm -> Expn -> Val -> Set where

  e-val : forall {v : Val} {F : Frm}
            ------------------------
            -> (evalsTo F (val v) v)

  e-var : forall {x : Id} {F : Frm} {v : Val}
          -> (mapsTo F x v)
          ------------------------
          -> (evalsTo F (var x) v) 

  e-add : forall {e1 e2 : Expn} {F : Frm} {v1 v2 : Val}
          -> (evalsTo F e1 v1) 
          -> (evalsTo F e2 v2) 
          -------------------------------------
          -> (evalsTo F (plus e1 e2) (v1 + v2))

  e-sub : forall {e1 e2 : Expn} {F : Frm} {v1 v2 : Val}
          -> (evalsTo F e1 v1) 
          -> (evalsTo F e2 v2) 
          -----------------------------------------
          -> (evalsTo F (minus e1 e2) (v1 -nat v2))

  e-scale : forall {e1 : Expn} {F : Frm} {v1 v2 : Val}
          -> (evalsTo F e1 v1) 
          ----------------------------------------
          -> (evalsTo F (scaleBy e1 v2) (v1 * v2))


e-thm : forall (e : Expn) -> (F : Frm) -> (evalsTo F e (eval e F))
e-thm (val e) F = e-val
e-thm (var x) F = e-var (var-thm x F)
e-thm (plus e1 e2) F = (e-add (e-thm e1 F) (e-thm e2 F))
e-thm (minus e1 e2) F = (e-sub (e-thm e1 F) (e-thm e2 F))
e-thm (scaleBy e1 v2) F = (e-scale (e-thm e1 F))

e-det : forall {e : Expn}{F : Frm}{u w : Val}
  -> (evalsTo F e u) -> (evalsTo F e w) -> (equiv u w)
e-det{val v}{F}{u}{w} e-val e-val =  refl 
e-det{var x}{F}{u}{w} (e-var var-lkup-u) (e-var var-lkup-v) =
  var-det var-lkup-u var-lkup-v
e-det{plus e1 e2}{F}{u}{w} (e-add e-u1 e-u2) (e-add e-w1 e-w2) =
  cong2 _+_ (e-det e-u1 e-w1) (e-det e-u2 e-w2)
e-det{minus e1 e2}{F}{u}{w} (e-sub e-u1 e-u2) (e-sub e-w1 e-w2) =
  cong2 _-nat_ (e-det e-u1 e-w1) (e-det e-u2 e-w2)
e-det{scaleBy e1 v2}{F}{u}{w} (e-scale e-u1) (e-scale e-w1) =
  cong2 _*_ (e-det e-u1 e-w1) refl

e-thm-fwd : forall {e : Expn}{F : Frm}{v : Val}
  -> (evalsTo F e v) -> (equiv v (eval e F))
e-thm-fwd{e}{F}{v} ev =
  let
      p1 : evalsTo F e (eval e F)
      p1 = e-thm e F
   in e-det ev p1 

e-thm-rev : forall {e : Expn}{F : Frm}{v : Val}
  -> (equiv v (eval e F)) -> (evalsTo F e v)
e-thm-rev{e}{F}{v} v-is = cong-pred (evalsTo F e) (sym v-is) (e-thm e F)

--
-- SEMANTICS of conditions as a decidable relation
--

data  passes : Frm -> Cond -> Set
data fails : Frm -> Cond -> Set

data passes where

  c-tt :  forall {F : Frm}
          ----------------
          -> passes F true

  c-and : forall {c1 c2 : Cond} {F : Frm}
          -> passes F c1
          -> passes F c2
          -----------------------
          -> passes F (and c1 c2)

  c-or1 : forall {c1 c2 : Cond} {F : Frm}
          -> passes F c1
          ----------------------
          -> passes F (or c1 c2)

  c-or2 : forall {c1 c2 : Cond} {F : Frm}
          -> passes F c2
          ----------------------
          -> passes F (or c1 c2)

  c-less : forall {e1 e2 : Expn} {F : Frm} {v1 v2 : Val}
           -> equiv (v1 < v2) tt
           -> evalsTo F e1 v1
           -> evalsTo F e2 v2
           -------------------------
           -> passes F (less e1 e2)

  c-eq : forall {e1 e2 : Expn} {F : Frm} {v1 v2 : Val}
           -> equiv (v1 =nat v2) tt
           -> evalsTo F e1 v1
           -> evalsTo F e2 v2
           --------------------------
           -> passes F (equal e1 e2)

  c-not : forall {c : Cond} {F : Frm}
          -> fails F c
          -------------------
          -> passes F (not c)

data fails where

  ~c-ff :  forall {F : Frm}
          ----------------
          -> fails F false

  ~c-or : forall {c1 c2 : Cond} {F : Frm}
          -> fails F c1
          -> fails F c2
          -----------------------
          -> fails F (or c1 c2)

  ~c-and1 : forall {c1 c2 : Cond} {F : Frm}
          -> fails F c1
          ----------------------
          -> fails F (and c1 c2)

  ~c-and2 : forall {c1 c2 : Cond} {F : Frm}
          -> fails F c2
          ----------------------
          -> fails F (and c1 c2)

  ~c-less : forall {e1 e2 : Expn} {F : Frm} {v1 v2 : Val}
           -> equiv (v1 < v2) ff
           -> evalsTo F e1 v1
           -> evalsTo F e2 v2
           -------------------------
           -> fails F (less e1 e2)

  ~c-eq : forall {e1 e2 : Expn} {F : Frm} {v1 v2 : Val}
           -> equiv (v1 =nat v2) ff
           -> evalsTo F e1 v1
           -> evalsTo F e2 v2
           --------------------------
           -> fails F (equal e1 e2)

  ~c-not : forall {c : Cond} {F : Frm}
          -> passes F c
          -------------------
          -> fails F (not c)

c-thm-fwd : forall {c : Cond}{F : Frm} -> (passes F c) -> (equiv (chck c F) tt)
~c-thm-fwd : forall {c : Cond}{F : Frm} -> (fails F c) -> (equiv (chck c F) ff)

c-thm-fwd (c-tt{F}) = refl
c-thm-fwd (c-and{c1}{c2}{F} passes-c1 passes-c2) =
  cong2 _&&_ (c-thm-fwd passes-c1) (c-thm-fwd passes-c2)
c-thm-fwd (c-or1{c1}{c2}{F} passes-c1) =
  cong2 _||_ (c-thm-fwd passes-c1) refl
c-thm-fwd (c-or2{c1}{c2}{F} passes-c2) =
  trans (cong2 _||_ refl (c-thm-fwd passes-c2)) (||-tt (chck c1 F))
c-thm-fwd (c-less{e1}{e2}{F}{v1}{v2} v1-less-v2 evalsTo-e1-v1 evalsTo-e2-v2) =
  let
    eval-e1-is-v1 : (equiv (eval e1 F) v1)
    eval-e1-is-v1 = sym (e-thm-fwd evalsTo-e1-v1)
    eval-e2-is-v2 : (equiv (eval e2 F) v2)
    eval-e2-is-v2 = sym (e-thm-fwd evalsTo-e2-v2)
  in
    begin
      chck (less e1 e2) F
    equiv[ refl ]
      (eval e1 F) < (eval e2 F)
    equiv[ cong2 _<_ eval-e1-is-v1 eval-e2-is-v2 ]
      v1 < v2
    equiv[ v1-less-v2 ]
      tt
    qed
c-thm-fwd (c-eq{e1}{e2}{F}{v1}{v2} v1-equals-v2 evalsTo-e1-v1 evalsTo-e2-v2) =
  let
    eval-e1-is-v1 : (equiv (eval e1 F) v1)
    eval-e1-is-v1 = sym (e-thm-fwd evalsTo-e1-v1)
    eval-e2-is-v2 : (equiv (eval e2 F) v2)
    eval-e2-is-v2 = sym (e-thm-fwd evalsTo-e2-v2)
  in
    begin
      chck (equal e1 e2) F
    equiv[ refl ]
      (eval e1 F) =nat (eval e2 F)
    equiv[ cong2 _=nat_ eval-e1-is-v1 eval-e2-is-v2 ]
      v1 =nat v2
    equiv[ v1-equals-v2 ]
      tt
    qed
c-thm-fwd (c-not{c}{F} c-fails) = cong ~_ (~c-thm-fwd c-fails)

~c-thm-fwd (~c-ff{F}) =
  refl
~c-thm-fwd (~c-or{c1}{c2}{F} fails-c1 fails-c2) =
  cong2 _||_ (~c-thm-fwd fails-c1) (~c-thm-fwd fails-c2)
~c-thm-fwd (~c-and1{c1}{c2}{F} fails-c1) =
  cong2 _&&_ (~c-thm-fwd fails-c1) refl
~c-thm-fwd (~c-and2{c1}{c2}{F} fails-c2) =
  trans (cong2 _&&_ refl (~c-thm-fwd fails-c2)) (&&-ff (chck c1 F))
~c-thm-fwd (~c-less{e1}{e2}{F}{v1}{v2} v1-not-less-v2 evalsTo-e1-v1 evalsTo-e2-v2) =
  let
    eval-e1-is-v1 : (equiv (eval e1 F) v1)
    eval-e1-is-v1 = sym (e-thm-fwd evalsTo-e1-v1)
    eval-e2-is-v2 : (equiv (eval e2 F) v2)
    eval-e2-is-v2 = sym (e-thm-fwd  evalsTo-e2-v2)
  in begin
    chck (less e1 e2) F
  equiv[ refl ]
    (eval e1 F) < (eval e2 F)
  equiv[ cong2 _<_ eval-e1-is-v1 eval-e2-is-v2 ]
    v1 < v2
  equiv[ v1-not-less-v2 ]
    ff
  qed
~c-thm-fwd (~c-eq{e1}{e2}{F}{v1}{v2} v1-not-equals-v2 evalsTo-e1-v1 evalsTo-e2-v2) =
  let
    eval-e1-is-v1 : (equiv (eval e1 F) v1)
    eval-e1-is-v1 = sym (e-thm-fwd evalsTo-e1-v1)
    eval-e2-is-v2 : (equiv (eval e2 F) v2)
    eval-e2-is-v2 = sym (e-thm-fwd evalsTo-e2-v2)
  in
    begin
      chck (equal e1 e2) F
    equiv[ refl ]
      (eval e1 F) =nat (eval e2 F)
    equiv[ cong2 _=nat_ eval-e1-is-v1 eval-e2-is-v2 ]
      v1 =nat v2
    equiv[ v1-not-equals-v2 ]
      ff
    qed
~c-thm-fwd (~c-not{c}{F} c-passes) =
  cong ~_ (c-thm-fwd c-passes)

-- These can probably be shown just by using
-- the contrapositives of ~c-thm-fwd and ~~c-thm-fwd
postulate
  c-thm-rev : forall {c : Cond}{F : Frm} -> (equiv (chck c F) tt) -> (passes F c)
  ~c-thm-rev : forall {c : Cond}{F : Frm} -> (equiv (chck c F) ff) -> (fails F c)

--
-- SEMANTICS of program statements
-- as a state transformation relation
--

data execsTo : Frm -> Stmt -> Frm -> Set where

  s-skip : forall {F : Frm}
    -------------------
    -> execsTo F skip F

  s-assign : forall {x : Id} {e : Expn} {F : Frm}  {v : Val}
    -> evalsTo F e v
    ----------------------------------------
    -> execsTo F (assign x e) (update x v F)

  s-seq : forall {s1 s2 : Stmt} {F0 F1 F2 : Frm}
    -> (execsTo F0 s1 F1)
    -> (execsTo F1 s2 F2)
    ------------------------------
    -> (execsTo F0 (seq s1 s2) F2)

  s-if-then : forall {c : Cond} {s1 s2 : Stmt} {F F' : Frm}
    -> (passes F c)
    -> (execsTo F s1 F')
    --------------------------------------
    -> (execsTo F (ifThenElse c s1 s2) F')

  s-if-else : forall {c : Cond} {s1 s2 : Stmt} {F F' : Frm}
    -> (fails F c)
    -> (execsTo F s2 F')
    --------------------------------------
    -> (execsTo F (ifThenElse c s1 s2) F')

  s-repeat-0 : forall {s : Stmt} {x : Id} {F : Frm}
     -> (mapsTo F x 0)
     -------------------------------
     -> (execsTo F (repeatBy x s) F)

  s-repeat-suc : forall {n : nat} {s : Stmt} {x : Id} {F F' : Frm}
    -> (mapsTo F x (suc n))
    -> (execsTo F (seq (seq s (assign x (val n))) (repeatBy x s)) F')
    -----------------------------------------------------------------
    -> (execsTo F (repeatBy x s) F')

  --
  -- A lil cheat: "returns" is just assign; doesn't exit

  s-return : forall {e : Expn} {F : Frm}  {rv : Val}
    -> (evalsTo F e rv)
    -------------------------------------------------
    -> (execsTo F (returns e) (update "retval" rv F))

postulate
  frm-compare : Frm -> Frm -> bool
  frm-iso : Frm -> Frm -> Set
  frm-not-iso  : Frm -> Frm -> Set

postulate
  s-thm : forall {s : Stmt}{F Ff Fr : Frm}
    -> execsTo F s Fr
    -> equiv (exec s F) Ff
    ----------------------
    -> frm-iso Ff Fr

