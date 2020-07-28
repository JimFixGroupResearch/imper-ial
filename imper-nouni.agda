module imper-nouni where

open import lib
open import eq-reas-nouni

_=nat_ = _=ℕ_

_-nat_ = _∸_

cross = _×_

equiv = _≡_

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

data maps : Frm -> Id -> Val -> Set where

  var-undef : forall {x : Id}
              ----------------
              -> (maps [] x 0)

  var-match : forall {x y : Id} {F : Frm} {v : Val}
              -> (equiv (x =string y) tt)
              ---------------------------
              -> (maps ((y , v) :: F) x v) 

  var-mismatch : forall {x y : Id} {F : Frm} {v w : Val}
                 -> (equiv (x =string y) ff)
                 -> (maps F x v)
                 ----------------------------
                 -> (maps ((y , w) :: F) x v)


if-tt-then : forall{A : Set} {b : bool} {a1 a2 : A}
    -> equiv b tt -> equiv (if b then a1 else a2)  a1
if-tt-then{A}{b}{a1}{a2} b-is-tt =
  begin
    if b then a1 else a2
  equiv[ cong3 if_then_else_ b-is-tt refl refl ]
    if tt then a1 else a2
  equiv[ refl ]
    a1
  qed

if-ff-then : forall{A : Set}{b : bool}{a1 a2 : A}
    -> equiv b ff -> equiv (if b then a1 else a2) a2
if-ff-then{A}{b}{a1}{a2} b-is-ff =
  begin
    if b then a1 else a2
  equiv[ cong3 if_then_else_ b-is-ff refl refl ]
    if ff then a1 else a2
  equiv[ refl ]
    a2
  qed

--
-- THEOREM: maps IMPLIES lookup
--
var-thm-fwd : forall{x : Id}{F : Frm}{v : Val}
  -> maps F x v -> equiv (lkup x F) v
var-thm-fwd{x}{[]}{0} var-undef =
  begin
    lkup x []
  equiv[ refl ]
    0
  qed
var-thm-fwd (var-match{x}{y}{F}{w} x-is-y) =
  begin
    lkup x ((y , w) :: F)
  equiv[ refl ]
    if (x =Id y) then w else (lkup x F)
  equiv[ if-tt-then x-is-y ]
    w
  qed
var-thm-fwd (var-mismatch{x}{y}{F}{v}{w} x-isnt-y maps-x-v) =
  let
    lkup-is-v : equiv (lkup x F) v
    lkup-is-v = var-thm-fwd maps-x-v
  in begin
    lkup x ((y , w) :: F)
  equiv[ refl ]
    if (x =Id y) then w else (lkup x F)
  equiv[ if-ff-then x-isnt-y ]
    lkup x F
  equiv[ lkup-is-v ]
    v
  qed

--
-- THEOREM: lookup IMPLIES maps
--
var-thm-rev : forall{x : Id}{F : Frm}{v : Val}
  -> equiv (lkup x F) v -> maps F x v
var-thm-rev{x}{[]}{v} lookup-is-v =
  let equiv-v-0 : equiv v 0
      equiv-v-0 = begin
                    v
                  equiv[ sym lookup-is-v ]
                    lkup x []
                  equiv[ refl ]
                    0
                  qed
   in cong-pred (\ o -> maps [] x o) (sym equiv-v-0) var-undef 
var-thm-rev{x}{(y , w) :: F}{v} lookup-in-::F-is-v
 with inspect (x =string y)
... | tt with-eq x-is-y =
          let v-is-w : equiv v w
              v-is-w = begin
                      v
                    equiv[ sym lookup-in-::F-is-v ]
                      lkup x ((y , w) :: F)
                    equiv[ refl ]
                      if x =string y then w else (lkup x F)
                    equiv[ cong3 if_then_else_ x-is-y refl refl ]
                      if tt then w else (lkup x F)
                    equiv[ refl ]
                      w
                    qed
           in cong-pred (\ o -> maps ((y , w) :: F) x o) (sym v-is-w) (var-match x-is-y)
... | ff with-eq x-isnt-y =
          let v-is-lookup-in-F : equiv v (lkup x F)
              v-is-lookup-in-F = begin
                      v
                    equiv[ sym lookup-in-::F-is-v ]
                      lkup x ((y , w) :: F)
                    equiv[ refl ]
                      if x =string y then w else (lkup x F)
                    equiv[ cong3 if_then_else_ x-isnt-y refl refl ]
                      if ff then w else (lkup x F)
                    equiv[ refl ]
                      lkup x F
                    qed
           in (var-mismatch x-isnt-y (var-thm-rev (sym v-is-lookup-in-F)))


--
-- SEMANTICS of expression evaluation as a relation
--

data evalsTo : Frm -> Expn -> Val -> Set where

  e-val : forall {v : Val} {F : Frm}
            ------------------------
            -> (evalsTo F (val v) v)

  e-var : forall {x : Id} {F : Frm} {v : Val}
          -> (maps F x v)
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

e-thm-fwd : forall{e : Expn}{F : Frm}{v : Val}
            -> evalsTo F e v -> equiv (eval e F) v
e-thm-fwd (e-val{v}{F}) =
  begin
    eval (val v) F
  equiv[ refl ]
    v
  qed
e-thm-fwd (e-var{x}{F}{v} lookup-is-v) = 
  begin
    eval (var x) F
  equiv[ var-thm-fwd lookup-is-v ]
    v
  qed
e-thm-fwd (e-add{e1}{e2}{F}{v1}{v2} e1-evalsTo-v1 e2-evalsTo-v2) =
  let
    eval-e1-is-v1 = e-thm-fwd e1-evalsTo-v1
    eval-e2-is-v2 = e-thm-fwd e2-evalsTo-v2
  in begin
    eval (plus e1 e2) F
  equiv[ refl ]
    (eval e1 F) + (eval e2 F)
  equiv[ cong2 _+_ eval-e1-is-v1 eval-e2-is-v2 ]
    v1 + v2
  qed
e-thm-fwd (e-sub{e1}{e2}{F}{v1}{v2} e1-evalsTo-v1 e2-evalsTo-v2) =
  let
    eval-e1-is-v1 = e-thm-fwd e1-evalsTo-v1
    eval-e2-is-v2 = e-thm-fwd e2-evalsTo-v2
  in begin
    eval (minus e1 e2) F
  equiv[ refl ]
    (eval e1 F) -nat (eval e2 F)
  equiv[ cong2 _-nat_ eval-e1-is-v1 eval-e2-is-v2 ]
    v1 -nat v2
  qed
e-thm-fwd (e-scale{e1}{F}{v1}{v2} e1-evalsTo-v1) =
  let
    eval-e1-is-v1 = e-thm-fwd e1-evalsTo-v1
  in begin
    eval (scaleBy e1 v2) F
  equiv[ refl ]
    (eval e1 F) * v2
  equiv[ cong2 _*_ eval-e1-is-v1 refl ]
    v1 * v2
  qed

e-thm-rev : forall{e : Expn}{F : Frm}{v : Val}
  -> (equiv (eval e F) v) -> (evalsTo F e v)
e-thm-rev{e}{F}{v} eval-e-is-v
    with e
...    | val w = cong-pred (\ o -> (evalsTo F (val w) o)) eval-e-is-v e-val
...    | var x = let v-is-lookup : (equiv v (lkup x F))
                     v-is-lookup = begin
                                     v
                                   equiv[ sym eval-e-is-v ]
                                     eval (var x) F
                                   equiv[ refl ]
                                     lkup x F
                                   qed
                in  e-var (var-thm-rev (sym v-is-lookup))
...    | plus e1 e2 = {!!}
...    | minus e1 e2 = {!!}
...    | scaleBy e1 v2 = {!!}

--
-- SEMANTICS of conditions as a decidable relation
--

data  isTrue : Frm -> Cond -> Set
data isFalse : Frm -> Cond -> Set

data isTrue where

  c-tt :  forall {F : Frm}
          ----------------
          -> isTrue F true

  c-and : forall {c1 c2 : Cond} {F : Frm}
          -> isTrue F c1
          -> isTrue F c2
          -----------------------
          -> isTrue F (and c1 c2)

  c-or1 : forall {c1 c2 : Cond} {F : Frm}
          -> isTrue F c1
          ----------------------
          -> isTrue F (or c1 c2)

  c-or2 : forall {c1 c2 : Cond} {F : Frm}
          -> isTrue F c2
          ----------------------
          -> isTrue F (or c1 c2)

  c-less : forall {e1 e2 : Expn} {F : Frm} {v1 v2 : Val}
           -> equiv (v1 < v2) tt
           -> evalsTo F e1 v1
           -> evalsTo F e2 v2
           -------------------------
           -> isTrue F (less e1 e2)

  c-eq : forall {e1 e2 : Expn} {F : Frm} {v1 v2 : Val}
           -> equiv (v1 =nat v2) tt
           -> evalsTo F e1 v1
           -> evalsTo F e2 v2
           --------------------------
           -> isTrue F (equal e1 e2)

  c-not : forall {c : Cond} {F : Frm}
          -> isFalse F c
          -------------------
          -> isTrue F (not c)

data isFalse where

  ~c-ff :  forall {F : Frm}
          ----------------
          -> isFalse F false

  ~c-or : forall {c1 c2 : Cond} {F : Frm}
          -> isFalse F c1
          -> isFalse F c2
          -----------------------
          -> isFalse F (or c1 c2)

  ~c-and1 : forall {c1 c2 : Cond} {F : Frm}
          -> isFalse F c1
          ----------------------
          -> isFalse F (and c1 c2)

  ~c-and2 : forall {c1 c2 : Cond} {F : Frm}
          -> isFalse F c2
          ----------------------
          -> isFalse F (and c1 c2)

  ~c-less : forall {e1 e2 : Expn} {F : Frm} {v1 v2 : Val}
           -> equiv (v1 < v2) ff
           -> evalsTo F e1 v1
           -> evalsTo F e2 v2
           -------------------------
           -> isFalse F (less e1 e2)

  ~c-eq : forall {e1 e2 : Expn} {F : Frm} {v1 v2 : Val}
           -> equiv (v1 =nat v2) ff
           -> evalsTo F e1 v1
           -> evalsTo F e2 v2
           --------------------------
           -> isFalse F (equal e1 e2)

  ~c-not : forall {c : Cond} {F : Frm}
          -> isTrue F c
          -------------------
          -> isFalse F (not c)

c-thm-fwd : forall {c : Cond}{F : Frm} -> (isTrue F c) -> (equiv (chck c F) tt)
~c-thm-fwd : forall {c : Cond}{F : Frm} -> (isFalse F c) -> (equiv (chck c F) ff)

c-thm-fwd (c-tt{F}) =
  begin
    chck true F
  equiv[ refl ]
    tt
  qed
c-thm-fwd (c-and{c1}{c2}{F} isTrue-c1 isTrue-c2) =
  let
    chck-c1-is-tt : (equiv (chck c1 F) tt)
    chck-c1-is-tt = c-thm-fwd isTrue-c1 
    chck-c2-is-tt : (equiv (chck c2 F) tt)
    chck-c2-is-tt = c-thm-fwd isTrue-c2 
  in begin
    chck (and c1 c2) F
  equiv[ refl ]
    (chck c1 F) && (chck c2 F)
  equiv[ cong2 _&&_ chck-c1-is-tt chck-c2-is-tt ]
    tt && tt
  equiv[ refl ]
    tt
  qed  
c-thm-fwd (c-or1{c1}{c2}{F} isTrue-c1) =
  let
    chck-c1-is-tt : (equiv (chck c1 F) tt)
    chck-c1-is-tt = c-thm-fwd isTrue-c1 
  in begin
    chck (or c1 c2) F
  equiv[ refl ]
    (chck c1 F) || (chck c2 F)
  equiv[ cong2 _||_ chck-c1-is-tt refl ]
    tt || (chck c2 F)
  equiv[ refl ]
    tt
  qed  
c-thm-fwd (c-or2{c1}{c2}{F} isTrue-c2) =
  let
    chck-c2-is-tt : (equiv (chck c2 F) tt)
    chck-c2-is-tt = c-thm-fwd isTrue-c2 
  in begin
    chck (or c1 c2) F
  equiv[ refl ]
    (chck c1 F) || (chck c2 F)
  equiv[ cong2 _||_ refl chck-c2-is-tt ]
    (chck c1 F) || tt
  equiv[ ||-tt (chck c1 F) ]
    tt
  qed  
c-thm-fwd (c-less{e1}{e2}{F}{v1}{v2} v1-less-v2 evalsTo-e1-v1 evalsTo-e2-v2) =
  let
    eval-e1-is-v1 : (equiv (eval e1 F) v1)
    eval-e1-is-v1 = e-thm-fwd evalsTo-e1-v1
    eval-e2-is-v2 : (equiv (eval e2 F) v2)
    eval-e2-is-v2 = e-thm-fwd evalsTo-e2-v2
  in begin
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
    eval-e1-is-v1 = e-thm-fwd evalsTo-e1-v1
    eval-e2-is-v2 : (equiv (eval e2 F) v2)
    eval-e2-is-v2 = e-thm-fwd evalsTo-e2-v2
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
c-thm-fwd (c-not{c}{F} c-isFalse) =
  let
    chck-c-is-ff : (equiv (chck c F) ff)
    chck-c-is-ff = ~c-thm-fwd c-isFalse
  in 
    begin
      chck (not c) F
    equiv[ refl ]
      ~ (chck c F)
    equiv[ cong ~_ chck-c-is-ff ]
      ~ ff
    equiv[ refl ]
      tt
    qed

~c-thm-fwd (~c-ff{F}) =
  begin
    chck false F
  equiv[ refl ]
    ff
  qed
~c-thm-fwd (~c-or{c1}{c2}{F} isFalse-c1 isFalse-c2) =
  let
    chck-c1-is-ff : (equiv (chck c1 F) ff)
    chck-c1-is-ff = ~c-thm-fwd isFalse-c1 
    chck-c2-is-ff : (equiv (chck c2 F) ff)
    chck-c2-is-ff = ~c-thm-fwd isFalse-c2 
  in begin
    chck (or c1 c2) F
  equiv[ refl ]
    (chck c1 F) || (chck c2 F)
  equiv[ cong2 _||_ chck-c1-is-ff chck-c2-is-ff ]
    ff || ff
  equiv[ refl ]
    ff
  qed  
~c-thm-fwd (~c-and1{c1}{c2}{F} isFalse-c1) =
  let
    chck-c1-is-ff : (equiv (chck c1 F) ff)
    chck-c1-is-ff = ~c-thm-fwd isFalse-c1 
  in begin
    chck (and c1 c2) F
  equiv[ refl ]
    (chck c1 F) && (chck c2 F)
  equiv[ cong2 _&&_ chck-c1-is-ff refl ]
    ff && (chck c2 F)
  equiv[ refl ]
    ff
  qed  
~c-thm-fwd (~c-and2{c1}{c2}{F} isFalse-c2) =
  let
    chck-c2-is-ff : (equiv (chck c2 F) ff)
    chck-c2-is-ff = ~c-thm-fwd isFalse-c2 
  in begin
    chck (and c1 c2) F
  equiv[ refl ]
    (chck c1 F) && (chck c2 F)
  equiv[ cong2 _&&_ refl chck-c2-is-ff ]
    (chck c1 F) && ff
  equiv[ &&-ff (chck c1 F) ]
    ff
  qed  
~c-thm-fwd (~c-less{e1}{e2}{F}{v1}{v2} v1-not-less-v2 evalsTo-e1-v1 evalsTo-e2-v2) =
  let
    eval-e1-is-v1 : (equiv (eval e1 F) v1)
    eval-e1-is-v1 = e-thm-fwd evalsTo-e1-v1
    eval-e2-is-v2 : (equiv (eval e2 F) v2)
    eval-e2-is-v2 = e-thm-fwd evalsTo-e2-v2
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
    eval-e1-is-v1 = e-thm-fwd evalsTo-e1-v1
    eval-e2-is-v2 : (equiv (eval e2 F) v2)
    eval-e2-is-v2 = e-thm-fwd evalsTo-e2-v2
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
~c-thm-fwd (~c-not{c}{F} c-isTrue) =
  let
    chck-c-is-tt : (equiv (chck c F) tt)
    chck-c-is-tt = c-thm-fwd c-isTrue
  in 
    begin
      chck (not c) F
    equiv[ refl ]
      ~ (chck c F)
  equiv[ cong ~_ chck-c-is-tt ]
    ~ tt
  equiv[ refl ]
    ff
  qed

-- These can probably be shown just by using
-- the contrapositives of ~c-thm-fwd and ~~c-thm-fwd
postulate
  c-thm-rev : forall {c : Cond}{F : Frm} -> (equiv (chck c F) tt) -> (isTrue F c)
  ~c-thm-rev : forall {c : Cond}{F : Frm} -> (equiv (chck c F) ff) -> (isFalse F c)


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
    -> (isTrue F c)
    -> (execsTo F s1 F')
    --------------------------------------
    -> (execsTo F (ifThenElse c s1 s2) F')

  s-if-else : forall {c : Cond} {s1 s2 : Stmt} {F F' : Frm}
    -> (isFalse F c)
    -> (execsTo F s2 F')
    --------------------------------------
    -> (execsTo F (ifThenElse c s1 s2) F')

  s-repeat-0 : forall {s : Stmt} {x : Id} {F : Frm}
     -> (maps F x 0)
     -------------------------------
     -> (execsTo F (repeatBy x s) F)

  s-repeat-suc : forall {n : nat} {s : Stmt} {x : Id} {F F' : Frm}
    -> (maps F x (suc n))
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

