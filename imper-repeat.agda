module imper-repeat where

open import lib

-- Unicode notes:
--   I use \Mix, \Mie, \MiF etc for meta-variables 𝑥, 𝑒, 𝐹 etc.
--   I use \mapsto for variable frame bindings and update.
--   I use \| for the frame update operation.
--   The \|- turnstile ⊢ is used for many of the semantics relations.
--   The \|-n is for its negation ⊬
--   I use \d= for code's literal numbers and booleans like (⇓ 42) and (⇓true)
--   This same down arrow is used for the arithmetic large step relation.
--   I use \u= for code variable lookups like (⇑ "x") and (⇑ "y")
--   I superscript arithmetic relations, evaluations, and operators with \^e as ᵉ
--   I superscript logical relations, evaluations, and operators with \^c as ᶜ
--   Programs use ↩ for sequencing. I don't know its emacs \ sequence yet.
--   Assignment is \:: followed by =, obtaining ∷=.


--
-- variable identifiers
--
Id : Set
Id = string

_=Id_ : Id → Id → 𝔹
_=Id_ = _=string_

--
-- values (just natural numbers here)
--
Val : Set
Val = ℕ

--
-- value and variable expressions
--
data Expn : Set where
  ⇓_ : Val → Expn
  ⇑_ : Id → Expn
  _+ᵉ_ : Expn → Expn → Expn
  _-ᵉ_ : Expn → Expn → Expn
  _*ᵉ⇓_ : Expn → Val → Expn

--
-- conditions on values and variables
--
data Cond : Set where
  ⇓true : Cond
  ⇓false : Cond
  _∧ᶜ_ : Cond → Cond → Cond
  _∨ᶜ_ : Cond → Cond → Cond
  ¬ᶜ_ : Cond → Cond
  [_<ᶜ_] : Expn → Expn → Cond
  [_=ᶜ_] : Expn → Expn → Cond

--
-- stack frames containing variable bindings
--
Frm : Set
Frm = 𝕃 (Id × Val)

[_↦_] : Id → Val → Frm
[ 𝑥 ↦ 𝑣 ] = [(𝑥 , 𝑣)]

[-↦0] : Frm
[-↦0] = []

--
-- program statements that transform a frame
--
data Stmt : Set where
  skip : Stmt
  _∷=_ : Id → Expn → Stmt
  _↩_ : Stmt → Stmt → Stmt
  if_then_else_end : Cond → Stmt → Stmt → Stmt
  by_repeat_end : Id → Stmt → Stmt
  returns : Expn → Stmt

infix 10 ⇑_ ⇓_
infix 9 _*ᵉ⇓_
infixl 8 _+ᵉ_ _-ᵉ_
infix 7 ¬ᶜ_
infixl 6 _∨ᶜ_
infixl 5 _∧ᶜ_
infix 4 _∷=_
infix 3 returns
infixl 2 _↩_


--
-- functional SEMANTICS of frames
--

-- lookup is no longer used to (hopefully) keep proofs simple; may bring back
lookup : Id → Frm → Val
lookup 𝑥 [] = 0
lookup 𝑥 ((𝑦 , 𝑤) :: 𝐹) = if (𝑥 =Id 𝑦) then 𝑤 else (lookup 𝑥 𝐹)

_∣_↦_ : Frm → Id → Val → Frm
[] ∣ 𝑥 ↦ 𝑣 = [ 𝑥 ↦ 𝑣 ]
((𝑦 , 𝑤) :: 𝐹) ∣ 𝑥 ↦ 𝑣 = if (𝑥 =Id 𝑦)
                         then (𝑦 , 𝑣) :: 𝐹
                         else (𝑦 , 𝑤) :: (𝐹 ∣ 𝑥 ↦ 𝑣)

--
-- functional SEMANTICS of expressions
--
⟦_⟧ᵉ_ : Expn → Frm → Val
⟦ ⇓ 𝑣 ⟧ᵉ _ = 𝑣
⟦ ⇑ 𝑥 ⟧ᵉ [] = 0
⟦ ⇑ 𝑥 ⟧ᵉ ((𝑦 , 𝑤) :: 𝐹) = if (𝑥 =Id 𝑦) then 𝑤 else ⟦ (⇑ 𝑥) ⟧ᵉ 𝐹
⟦ 𝑒₁ +ᵉ 𝑒₂ ⟧ᵉ 𝐹 = (⟦ 𝑒₁ ⟧ᵉ 𝐹) + (⟦ 𝑒₂ ⟧ᵉ 𝐹)
⟦ 𝑒₁ -ᵉ 𝑒₂ ⟧ᵉ 𝐹 = (⟦ 𝑒₁ ⟧ᵉ 𝐹) ∸ (⟦ 𝑒₂ ⟧ᵉ 𝐹)
⟦ 𝑒₁ *ᵉ⇓ 𝑣₂ ⟧ᵉ 𝐹 = (⟦ 𝑒₁ ⟧ᵉ 𝐹) * 𝑣₂

--
-- functional SEMANTICS of conditions
--
⟦_⟧ᶜ_ : Cond → Frm → 𝔹
⟦ ⇓true ⟧ᶜ _ = tt
⟦ ⇓false ⟧ᶜ _ = ff
⟦ 𝒸₁ ∧ᶜ 𝒸₂ ⟧ᶜ 𝐹 = (⟦ 𝒸₁ ⟧ᶜ 𝐹) && (⟦ 𝒸₂ ⟧ᶜ 𝐹)
⟦ 𝒸₁ ∨ᶜ 𝒸₂ ⟧ᶜ 𝐹 = (⟦ 𝒸₁ ⟧ᶜ 𝐹) || (⟦ 𝒸₂ ⟧ᶜ 𝐹)
⟦ ¬ᶜ 𝒸 ⟧ᶜ 𝐹 = ~ (⟦ 𝒸 ⟧ᶜ 𝐹)
⟦ [ 𝑒₁ <ᶜ 𝑒₂ ] ⟧ᶜ 𝐹 = (⟦ 𝑒₁ ⟧ᵉ 𝐹) < (⟦ 𝑒₂ ⟧ᵉ 𝐹)
⟦ [ 𝑒₁ =ᶜ 𝑒₂ ] ⟧ᶜ 𝐹 = (⟦ 𝑒₁ ⟧ᵉ 𝐹) =ℕ (⟦ 𝑒₂ ⟧ᵉ 𝐹)

repeatedly : Id → ℕ → Stmt → Frm → Frm
⟦_⟧ˢ_ : Stmt → Frm → Frm
repeatedly 𝑥 0 𝑠 𝐹 = 𝐹
repeatedly 𝑥 (suc n) 𝑠 𝐹 = repeatedly 𝑥 n 𝑠 ((⟦ 𝑠 ⟧ˢ 𝐹) ∣ 𝑥 ↦ n )
⟦ skip ⟧ˢ 𝐹 = 𝐹
⟦ 𝑥 ∷= 𝑒 ⟧ˢ 𝐹 = (𝐹 ∣ 𝑥 ↦ (⟦ 𝑒 ⟧ᵉ 𝐹))
⟦ 𝑠₁ ↩ 𝑠₂ ⟧ˢ 𝐹 = (⟦ 𝑠₂ ⟧ˢ (⟦ 𝑠₁ ⟧ˢ 𝐹))
⟦ if 𝒸 then 𝑠₁ else 𝑠₂ end ⟧ˢ 𝐹 = if (⟦ 𝒸 ⟧ᶜ 𝐹) then (⟦ 𝑠₁ ⟧ˢ 𝐹) else (⟦ 𝑠₂ ⟧ˢ 𝐹)
⟦ by 𝑥 repeat 𝑠 end ⟧ˢ 𝐹 = repeatedly 𝑥 (⟦ ⇑ 𝑥 ⟧ᵉ 𝐹) 𝑠 𝐹
⟦ returns 𝑒 ⟧ˢ 𝐹 = 𝐹 ∣ "retval" ↦ (⟦ 𝑒 ⟧ᵉ 𝐹)

arg1 : Id
arg1 = "arg1"

arg2 : Id
arg2 = "arg2"

retval : Id
retval = "retval"

W : Id
W = "w"

X : Id
X = "x"

Y : Id
Y = "y"

Z : Id
Z = "z"

pgm0 : Stmt
pgm0 = X ∷= ⇓ 3 ↩
       Y ∷= ⇓ 1 ↩
       Y ∷= ⇑ Y *ᵉ⇓ 2

pgm1 : Stmt
pgm1 = X ∷= ⇓ 3 ↩
       Y ∷= ⇓ 1 ↩
       by X repeat
         Y ∷= ⇑ Y *ᵉ⇓ 2
       end

Z∷=X*Y = W ∷= ⇑ X ↩
         Z ∷= ⇓ 0 ↩
         by W repeat
           Z ∷= ⇑ Z +ᵉ ⇑ Y
         end


pgm2 = X ∷= ⇓ 3 ↩
       Y ∷= ⇓ 1 ↩
       by X repeat
         Z∷=X*Y ↩
         Y ∷= ⇑ Z
       end


fact-pgm : Stmt
fact-pgm =
  (X ∷= (⇑ arg1)) ↩
  (Y ∷= (⇓ 1)) ↩
  (by X repeat (
    Z∷=X*Y ↩
    (Y ∷= (⇑ Z)))
  end) ↩
  (returns (⇑ Y))


result1 = ⟦ pgm1 ⟧ˢ [-↦0]
result2 = ⟦ pgm2 ⟧ˢ [-↦0]

--
-- SEMANTICS of stack bindings as a relation
--
infixl 7 _⊢ᶠ_↦_
infixl 5 _∣_↦_
infixl 4 _⊢ᵉ_⇓_
infixl 3 _⊢ᶜ_ _⊬ᶜ_ -- _↦_

data _⊢ᶠ_↦_ : Frm → Id → Val → Set where

  var-undef : ∀ {𝑥 : Id}
              ----------------
              → [] ⊢ᶠ 𝑥 ↦ 0

  var-match : ∀ {𝑥 : Id} {𝐹 : Frm} {𝑣 : Val}
              ---------------------------
              → ((𝑥 , 𝑣) :: 𝐹) ⊢ᶠ 𝑥 ↦ 𝑣

  var-mismatch : ∀ {𝑥 𝑦 : Id} {𝐹 : Frm} {𝑣 𝑤 : Val}
                 → (𝑥 =string 𝑦) ≢ ff
                 → 𝐹 ⊢ᶠ 𝑥 ↦ 𝑣
                 -------------------------
                 → ((𝑦 , 𝑤) :: 𝐹) ⊢ᶠ 𝑥 ↦ 𝑣

--
-- SEMANTICS of expression evaluation as a relation
--

data _⊢ᵉ_⇓_ : Frm → Expn → Val → Set where

  e-val : ∀ {𝑣 : Val} {𝐹 : Frm}
            ----------------
            → 𝐹 ⊢ᵉ (⇓ 𝑣) ⇓ 𝑣

  e-var : ∀ {𝑥 : Id} {𝐹 : Frm} {𝑣 : Val}
          → 𝐹 ⊢ᶠ 𝑥 ↦ 𝑣
          ---------------
          → 𝐹 ⊢ᵉ (⇑ 𝑥) ⇓ 𝑣

  e-sum : ∀ {𝑒₁ 𝑒₂ : Expn} {𝐹 : Frm} {𝑣₁ 𝑣₂ : Val}
          → 𝐹 ⊢ᵉ 𝑒₁ ⇓ 𝑣₁
          → 𝐹 ⊢ᵉ 𝑒₂ ⇓ 𝑣₂
          ---------------------------
          → 𝐹 ⊢ᵉ (𝑒₁ +ᵉ 𝑒₂) ⇓ (𝑣₁ + 𝑣₂)

  e-sub : ∀ {𝑒₁ 𝑒₂ : Expn} {𝐹 : Frm} {𝑣₁ 𝑣₂ : Val}
          → 𝐹 ⊢ᵉ 𝑒₁ ⇓ 𝑣₁
          → 𝐹 ⊢ᵉ 𝑒₂ ⇓ 𝑣₂
          ---------------------------
          → 𝐹 ⊢ᵉ (𝑒₁ -ᵉ 𝑒₂) ⇓ (𝑣₁ ∸ 𝑣₂)

  e-scale : ∀ {𝑒₁ : Expn} {𝑣₁ 𝑣₂ : Val} {𝐹 : Frm}
            → 𝐹 ⊢ᵉ 𝑒₁ ⇓ 𝑣₁
            ---------------------------
            → 𝐹 ⊢ᵉ ( 𝑒₁ *ᵉ⇓ 𝑣₂) ⇓ (𝑣₁ * 𝑣₂)


postulate
  e-thm-fwd : ∀ {𝑒 : Expn} {𝐹 : Frm} {𝑣 : Val} → (𝐹 ⊢ᵉ 𝑒 ⇓ 𝑣) → ((⟦ 𝑒 ⟧ᵉ 𝐹) ≡ 𝑣)
--e-thm-fwd e-const = refl
--e-thm-fwd (e-var var-undef) = refl
--e-thm-fwd (e-sum p₁ p₂) = ?
--e-thm-fwd (e-var var-match) = ?
--e-thm-fwd (e-var (var-mismatch p₁ p₂)) = ?

--
-- SEMANTICS of conditions as a decidable relation
--

data _⊢ᶜ_ : Frm → Cond → Set
data _⊬ᶜ_ : Frm → Cond → Set

data _⊢ᶜ_ where

  c-tt :  ∀ {𝐹 : Frm}
          -----------
          → 𝐹 ⊢ᶜ ⇓true

  c-and : ∀ {𝒸₁ 𝒸₂ : Cond} {𝐹 : Frm}
          → 𝐹 ⊢ᶜ 𝒸₁
          → 𝐹 ⊢ᶜ 𝒸₂
          -----------------
          → 𝐹 ⊢ᶜ (𝒸₁ ∧ᶜ 𝒸₂)

  c-or₁ : ∀ {𝒸₁ 𝒸₂ : Cond} {𝐹 : Frm}
          → 𝐹 ⊢ᶜ 𝒸₁
          ---------------
          → 𝐹 ⊢ᶜ (𝒸₁ ∨ᶜ 𝒸₂)

  c-or₂ : ∀ {𝒸₁ 𝒸₂ : Cond} {𝐹 : Frm}
          → 𝐹 ⊢ᶜ 𝒸₂
          ----------------
          → 𝐹 ⊢ᶜ (𝒸₁ ∨ᶜ 𝒸₂)

  c-less : ∀ {𝑒₁ 𝑒₂ : Expn} {𝐹 : Frm} {𝑣₁ 𝑣₂ : Val}
           → 𝑣₁ < 𝑣₂ ≡ tt
           → 𝐹 ⊢ᵉ 𝑒₁ ⇓ 𝑣₁
           → 𝐹 ⊢ᵉ 𝑒₂ ⇓ 𝑣₂
           -------------------
           → 𝐹 ⊢ᶜ [ 𝑒₁ <ᶜ 𝑒₂ ]

  c-eq : ∀ {𝑒₁ 𝑒₂ : Expn} {𝐹 : Frm} {𝑣 : Val}
           → 𝐹 ⊢ᵉ 𝑒₁ ⇓ 𝑣
           → 𝐹 ⊢ᵉ 𝑒₂ ⇓ 𝑣
           -------------------
           → 𝐹 ⊢ᶜ [ 𝑒₁ =ᶜ 𝑒₂ ]

  c-not : ∀ {𝒸 : Cond} {𝐹 : Frm}
          → 𝐹 ⊬ᶜ 𝒸
          -------------
          → 𝐹 ⊢ᶜ (¬ᶜ 𝒸)


data _⊬ᶜ_ where

  ~c-ff :  ∀ {𝐹 : Frm}
           --------------
           → 𝐹 ⊬ᶜ ⇓false

  ~c-or : ∀ {𝒸₁ 𝒸₂ : Cond} {𝐹 : Frm}
          → 𝐹 ⊬ᶜ 𝒸₁
          → 𝐹 ⊬ᶜ 𝒸₂
          ----------------
          → 𝐹 ⊬ᶜ (𝒸₁ ∨ᶜ 𝒸₂)

  ~c-and₁ : ∀ {𝒸₁ 𝒸₂ : Cond} {𝐹 : Frm}
            → 𝐹 ⊬ᶜ 𝒸₁
            -----------------
            → 𝐹 ⊬ᶜ (𝒸₁ ∧ᶜ 𝒸₂)

  ~c-and₂ : ∀ {𝒸₁ 𝒸₂ : Cond} {𝐹 : Frm}
            → 𝐹 ⊬ᶜ 𝒸₂
            -----------------
            → 𝐹 ⊬ᶜ (𝒸₁ ∧ᶜ 𝒸₂)

  ~c-eq : ∀ {𝑒₁ 𝑒₂ : Expn} {𝐹 : Frm} {𝑣₁ 𝑣₂ : Val}
            → 𝑣₁ =ℕ 𝑣₂ ≡ ff
            → 𝐹 ⊢ᵉ 𝑒₁ ⇓ 𝑣₁
            → 𝐹 ⊢ᵉ 𝑒₂ ⇓ 𝑣₂
            -------------------
            → 𝐹 ⊬ᶜ [ 𝑒₁ =ᶜ 𝑒₂ ]

  ~c-less : ∀ {𝑒₁ 𝑒₂ : Expn} {𝐹 : Frm} {𝑣₁ 𝑣₂ : Val}
            → 𝑣₁ < 𝑣₂ ≡ ff
            → 𝐹 ⊢ᵉ 𝑒₁ ⇓ 𝑣₁
            → 𝐹 ⊢ᵉ 𝑒₂ ⇓ 𝑣₂
            -------------------
            → 𝐹 ⊬ᶜ [ 𝑒₁ <ᶜ 𝑒₂ ]

  ~c-not : ∀ {𝒸 : Cond} {𝐹 : Frm}
           → 𝐹 ⊢ᶜ 𝒸
           -------------
           → 𝐹 ⊬ᶜ (¬ᶜ 𝒸)

test3 : [] ⊢ᶜ (⇓true ∧ᶜ (¬ᶜ ⇓false))
test3 = c-and c-tt (c-not ~c-ff)

postulate
  c-thm :  ∀ {𝒸 : Cond}  {𝐹 : Frm} → 𝐹 ⊢ᶜ 𝒸 → (⟦ 𝒸 ⟧ᶜ 𝐹 ≡ tt)
  ~c-thm :  ∀ {𝒸 : Cond}  {𝐹 : Frm} → 𝐹 ⊬ᶜ 𝒸 → (⟦ 𝒸 ⟧ᶜ 𝐹 ≡ ff)

--
-- SEMANTICS of program statements as a state transformation relation
--

data _=[_]⇒_ : Frm → Stmt → Frm → Set where

 s-skip : ∀ {𝐹 : Frm}
          --------------
          → 𝐹 =[ skip ]⇒ 𝐹

 s-assign : ∀ {𝑥 : Id} {𝑒 : Expn} {𝐹 : Frm}  {𝑣 : Val}
            → 𝐹 ⊢ᵉ 𝑒 ⇓ 𝑣
            ------------------------------
            → 𝐹 =[ 𝑥 ∷= 𝑒 ]⇒ (𝐹 ∣ 𝑥 ↦ 𝑣)

 s-seq : ∀ {𝑠₁ 𝑠₂ : Stmt} {𝐹₀ 𝐹₁ 𝐹₂ : Frm}
         → 𝐹₀ =[ 𝑠₁ ]⇒ 𝐹₁
         → 𝐹₁ =[ 𝑠₂ ]⇒ 𝐹₂
         -------------------
         → 𝐹₀ =[ 𝑠₁ ↩ 𝑠₂ ]⇒ 𝐹₂

 s-if-then : ∀ {𝒸 : Cond} {𝑠₁ 𝑠₂ : Stmt} {𝐹 𝐹' : Frm}
             → 𝐹 ⊢ᶜ 𝒸
             → 𝐹 =[ 𝑠₁ ]⇒ 𝐹'
             → 𝐹 =[ 𝑠₂ ]⇒ 𝐹'
             ------------------------------------
             → 𝐹 =[ if 𝒸 then 𝑠₁ else 𝑠₂ end ]⇒ 𝐹'

 s-if-else : ∀ {𝒸 : Cond} {𝑠₁ 𝑠₂ : Stmt} {𝐹 𝐹' : Frm}
             → 𝐹 ⊬ᶜ 𝒸
             → 𝐹 =[ 𝑠₂ ]⇒ 𝐹'
             ------------------------------------
             → 𝐹 =[ if 𝒸 then 𝑠₁ else 𝑠₂ end ]⇒ 𝐹'

 s-repeat-0 : ∀ {𝑠 : Stmt} {𝑥 : Id} {𝐹 : Frm}
              → 𝐹 ⊢ᶠ 𝑥 ↦ 0
              -----------------------------
              → 𝐹 =[ by 𝑥 repeat 𝑠 end ]⇒ 𝐹

 s-repeat-suc : ∀ {𝑛 : ℕ} {𝑠 : Stmt} {𝑥 : Id} {𝐹 𝐹' : Frm}
                → 𝐹 ⊢ᶠ 𝑥 ↦ suc 𝑛
                → 𝐹 =[ 𝑠 ↩ 𝑥 ∷= (⇓ 𝑛) ↩ by 𝑥 repeat 𝑠 end ]⇒ 𝐹'
                ----------------------------------------------
                → 𝐹 =[ by 𝑥 repeat 𝑠 end ]⇒ 𝐹'

 -- I've cheated and treated "returns" as an assignment; doesn't exit

 s-return : ∀ {𝑒 : Expn} {𝐹 : Frm}  {𝑣 : Val}
            → 𝐹 ⊢ᵉ 𝑒 ⇓ 𝑣
            ------------------------------
            → 𝐹 =[ returns 𝑒 ]⇒ (𝐹 ∣ "retval" ↦ 𝑣)

[➊↦_] : Val → Frm
[➊↦ 𝑣 ] = [-↦0] ∣ arg1 ↦ 𝑣

[➊↦_,➋↦_] : Val →  Val → Frm
[➊↦ 𝑣₁ ,➋↦ 𝑣₂ ] = (([-↦0] ∣ arg1 ↦ 𝑣₁) ∣ arg2 ↦ 𝑣₂ )

frame6 = ((((( [➊↦ 3 ] ∣ X ↦ 0) ∣ Y ↦ 6) ∣ W ↦ 0) ∣ Z ↦ 6) ∣ retval ↦ 6)
postulate
  test6 : [➊↦ 3 ] =[ fact-pgm ]⇒ frame6

postulate
  s-thm : ∀ {𝑠 : Stmt } {𝐹 : Frm} → 𝐹 =[ 𝑠 ]⇒ (⟦ 𝑠 ⟧ˢ 𝐹)

postulate
  fact-thm : ∀ {n : ℕ} {𝐹 : Frm} → [➊↦ n ] =[ fact-pgm ]⇒ 𝐹 → 𝐹 ⊢ᶠ retval ↦ (factorial n)
