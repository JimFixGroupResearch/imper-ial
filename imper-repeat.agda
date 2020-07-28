module imper-repeat where

open import lib
open import eq-reasoning

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

-- Unicode notes. I use:
--   \Mix, \Mie, \MiF etc for meta-variables 𝑥, 𝑒, 𝐹 etc.
--   \mapsto for variable frame bindings and update.
--   \| for the frame update operation.
--   \|- turnstile ⊢ is used for the semantics relations.
--   (\|-n for its negation ⊬)
--   \d= for code literal values e.g. ⇓ 42 and ⇓true
--   The down arrow is also used for the eval relation. 
--   \u= for code variable lookups like ⇑ "x" and ⇑ "y"
--   superscripts of items with \^e as ᵉ, \c^c as ᶜ
--   ↩ for sequencing. This is \lefthookarrow.
--   ∷= which is \:: followed by =

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
  returns_ : Expn → Stmt

infix 10 ⇑_ ⇓_
infix 9 _*ᵉ⇓_
infixl 8 _+ᵉ_ _-ᵉ_
infix 7 ¬ᶜ_
infixl 6 _∨ᶜ_
infixl 5 _∧ᶜ_
infix 4 _∷=_
infix 3 returns_
infixl 2 _↩_


--
-- functional SEMANTICS of frames
--

_∥_ : Frm → Id → Val
[] ∥ 𝑥 = 0
((𝑦 , 𝑤) :: 𝐹) ∥ 𝑥  = if (𝑥 =Id 𝑦) then 𝑤 else (𝐹 ∥ 𝑥)

_∣_↦_ : Frm → Id → Val → Frm
[] ∣ 𝑥 ↦ 𝑣 = [ 𝑥 ↦ 𝑣 ]
((𝑦 , 𝑤) :: 𝐹) ∣ 𝑥 ↦ 𝑣
          = if (𝑥 =Id 𝑦)
              then (𝑦 , 𝑣) :: 𝐹
              else (𝑦 , 𝑤) :: (𝐹 ∣ 𝑥 ↦ 𝑣)

--
-- functional SEMANTICS of expressions
--
⟦_⟧ᵉ_ : Expn → Frm → Val
⟦ ⇓ 𝑣 ⟧ᵉ _ = 𝑣
⟦ ⇑ 𝑥 ⟧ᵉ 𝐹 = 𝐹 ∥ 𝑥
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

--
-- functional SEMANTICS of program execution
--
⟦_∣_∷=_…0⟧ˢ_ : Stmt → Id → ℕ → Frm → Frm
⟦_⟧ˢ_ : Stmt → Frm → Frm
⟦ 𝑠 ∣ 𝑥 ∷= 0 …0⟧ˢ 𝐹 = 𝐹
⟦ 𝑠 ∣ 𝑥 ∷= (suc 𝑛) …0⟧ˢ 𝐹
                  = ⟦ 𝑠 ∣ 𝑥 ∷= 𝑛 …0⟧ˢ ((⟦ 𝑠 ⟧ˢ 𝐹) ∣ 𝑥 ↦ 𝑛)
⟦ skip ⟧ˢ 𝐹 = 𝐹
⟦ 𝑥 ∷= 𝑒 ⟧ˢ 𝐹 = (𝐹 ∣ 𝑥 ↦ (⟦ 𝑒 ⟧ᵉ 𝐹))
⟦ 𝑠₁ ↩ 𝑠₂ ⟧ˢ 𝐹 = (⟦ 𝑠₂ ⟧ˢ (⟦ 𝑠₁ ⟧ˢ 𝐹))
⟦ if 𝒸 then 𝑠₁ else 𝑠₂ end ⟧ˢ 𝐹 = if (⟦ 𝒸 ⟧ᶜ 𝐹) then (⟦ 𝑠₁ ⟧ˢ 𝐹) else (⟦ 𝑠₂ ⟧ˢ 𝐹)
⟦ by 𝑥 repeat 𝑠 end ⟧ˢ 𝐹 = ⟦ 𝑠 ∣ 𝑥 ∷= (⟦ ⇑ 𝑥 ⟧ᵉ 𝐹) …0⟧ˢ 𝐹
⟦ returns 𝑒 ⟧ˢ 𝐹 = 𝐹 ∣ "retval" ↦ (⟦ 𝑒 ⟧ᵉ 𝐹)

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

  var-match : ∀ {𝑥 𝑦 : Id} {𝐹 : Frm} {𝑤 : Val}
              → (𝑥 =string 𝑦) ≡ tt
              ---------------------------
              → ((𝑦 , 𝑤) :: 𝐹) ⊢ᶠ 𝑥 ↦ 𝑤

  var-mismatch : ∀ {𝑥 𝑦 : Id} {𝐹 : Frm} {𝑣 𝑤 : Val}
                 → (𝑥 =string 𝑦) ≡ ff
                 → 𝐹 ⊢ᶠ 𝑥 ↦ 𝑣
                 -------------------------
                 → ((𝑦 , 𝑤) :: 𝐹) ⊢ᶠ 𝑥 ↦ 𝑣


if-tt-then : ∀{A : Set} {b : 𝔹} {a1 a2 : A}
    → b ≡ tt → if b then a1 else a2 ≡ a1
if-tt-then{A}{b}{a1}{a2} b≡tt =
  begin
    if b then a1 else a2
  ≡⟨ cong3 if_then_else_ b≡tt refl refl ⟩
    if tt then a1 else a2
  ≡⟨ refl ⟩
    a1
  ∎

postulate
  if-ff-then : ∀{A : Set}{b : 𝔹}{a1 a2 : A}
    → b ≡ ff → if b then a1 else a2 ≡ a2

var-thm-fwd : ∀{x : Id}{F : Frm}{v : Val}
  → F ⊢ᶠ x ↦ v → F ∥ x ≡ v
var-thm-fwd{x}{[]}{0} var-undef =
  begin
    [] ∥ x
  ≡⟨ refl ⟩
    0
  ∎
var-thm-fwd (var-match{x}{y}{F}{w} x≡y) =
  begin
    ((y , w) :: F) ∥ x
  ≡⟨ refl ⟩
    if (x =Id y) then w else (F ∥ x)
  ≡⟨ if-tt-then x≡y ⟩
    w
  ∎
var-thm-fwd (var-mismatch{x}{y}{F}{v}{w} x≢y x↦v) =
  let
    F∥x≡v : F ∥ x ≡ v
    F∥x≡v = var-thm-fwd x↦v
  in begin
    ((y , w) :: F) ∥ x
  ≡⟨ refl ⟩
    if (x =Id y) then w else (F ∥ x)
  ≡⟨ if-ff-then x≢y ⟩
    F ∥ x
  ≡⟨ F∥x≡v ⟩
    v
  ∎

var-thm-rev : ∀{x : Id}{F : Frm}{v : Val}
  → F ∥ x ≡ v → F ⊢ᶠ x ↦ v
var-thm-rev{x}{[]}{v} []∥x≡v =
  let v≡0 : v ≡ 0
      v≡0 = begin
             v
            ≡⟨ sym []∥x≡v ⟩
             [] ∥ x
            ≡⟨ refl ⟩
             0
            ∎
   in cong-pred (λ xxx → [] ⊢ᶠ x ↦ xxx) (sym v≡0) var-undef 
var-thm-rev{x}{(y , w) :: F}{v} y,w::F∥x≡v
 with inspect (x =string y)
... | tt with≡ same =
          let v≡w : v ≡ w
              v≡w = begin
                      v
                    ≡⟨ sym y,w::F∥x≡v ⟩
                      ((y , w) :: F) ∥ x
                    ≡⟨ refl ⟩
                      if x =string y then w else F ∥ x
                    ≡⟨ cong3 if_then_else_ same refl refl ⟩
                      if tt then w else F ∥ x
                    ≡⟨ refl ⟩
                      w
                    ∎
           in cong-pred (λ xxx → ((y , w) :: F) ⊢ᶠ x ↦ xxx) (sym v≡w) (var-match same)
... | ff with≡ diff =
          let v≡F∥x : v ≡ F ∥ x
              v≡F∥x = begin
                      v
                    ≡⟨ sym y,w::F∥x≡v ⟩
                      ((y , w) :: F) ∥ x
                    ≡⟨ refl ⟩
                      if x =string y then w else F ∥ x
                    ≡⟨ cong3 if_then_else_ diff refl refl ⟩
                      if ff then w else F ∥ x
                    ≡⟨ refl ⟩
                      F ∥ x
                    ∎
           in (var-mismatch diff (var-thm-rev (sym v≡F∥x)))

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

  e-add : ∀ {𝑒₁ 𝑒₂ : Expn} {𝐹 : Frm} {𝑣₁ 𝑣₂ : Val}
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

e-thm-fwd : ∀{𝑒 : Expn}{𝐹 : Frm}{𝑣 : Val}
            → (𝐹 ⊢ᵉ 𝑒 ⇓ 𝑣) → ((⟦ 𝑒 ⟧ᵉ 𝐹) ≡ 𝑣)
e-thm-fwd (e-val{v}{F}) =
  begin
    ⟦ ⇓ v ⟧ᵉ F
  ≡⟨ refl ⟩
    v
  ∎
e-thm-fwd (e-var{x}{F}{v} x↦v) = 
  begin
    ⟦ ⇑ x ⟧ᵉ F
  ≡⟨ var-thm-fwd x↦v ⟩
    v
  ∎
e-thm-fwd (e-add{e1}{e2}{F}{v1}{v2} e1⇓v1 e2⇓v2) =
  let
    ⟦e1⟧≡v1 = e-thm-fwd e1⇓v1
    ⟦e2⟧≡v2 = e-thm-fwd e2⇓v2
  in begin
    ⟦ e1 +ᵉ e2 ⟧ᵉ F
  ≡⟨ refl ⟩
    ⟦ e1 ⟧ᵉ F + ⟦ e2 ⟧ᵉ F
  ≡⟨ cong2 _+_ ⟦e1⟧≡v1 ⟦e2⟧≡v2 ⟩
    v1 + v2
  ∎
e-thm-fwd (e-sub{e1}{e2}{F}{v1}{v2} e1⇓v1 e2⇓v2) =
  let
    ⟦e1⟧≡v1 = e-thm-fwd e1⇓v1
    ⟦e2⟧≡v2 = e-thm-fwd e2⇓v2
  in begin
    ⟦ e1 -ᵉ e2 ⟧ᵉ F
  ≡⟨ refl ⟩
    ⟦ e1 ⟧ᵉ F ∸ ⟦ e2 ⟧ᵉ F
  ≡⟨ cong2 _∸_ ⟦e1⟧≡v1 ⟦e2⟧≡v2 ⟩
    v1 ∸ v2
  ∎
e-thm-fwd (e-scale{e1}{v1}{v2}{F} e1⇓v1) =
  let
    ⟦e1⟧≡v1 = e-thm-fwd e1⇓v1
  in begin
    ⟦ e1 *ᵉ⇓ v2 ⟧ᵉ F
  ≡⟨ refl ⟩
    ⟦ e1 ⟧ᵉ F * v2
  ≡⟨ cong2 _*_ ⟦e1⟧≡v1 refl ⟩
    v1 * v2
  ∎


e-thm-rev : ∀{𝑒 : Expn}{𝐹 : Frm}{𝑣 : Val}
  → ((⟦ 𝑒 ⟧ᵉ 𝐹) ≡ 𝑣) → (𝐹 ⊢ᵉ 𝑒 ⇓ 𝑣)
e-thm-rev{e}{F}{v} ⟦e⟧F≡v
    with e
...    | ⇓ w = cong-pred (λ xxx → F ⊢ᵉ (⇓ w) ⇓ xxx) ⟦e⟧F≡v e-val
...    | ⇑ x = let v≡F∥x : v ≡ F ∥ x
                   v≡F∥x = begin
                             v
                           ≡⟨ sym ⟦e⟧F≡v ⟩
                             ⟦ ⇑ x ⟧ᵉ F
                           ≡⟨ refl ⟩
                             F ∥ x
                           ∎
                in  e-var (var-thm-rev (sym v≡F∥x))
...    | e1 +ᵉ e2 = {!!}
...    | e1 -ᵉ e2 = {!!}
...    | e1 *ᵉ⇓ v2 = {!!}


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

  c-eq : ∀ {𝑒₁ 𝑒₂ : Expn} {𝐹 : Frm} {𝑣₁ 𝑣₂ : Val}
           → 𝑣₁ =ℕ 𝑣₂ ≡ tt
           → 𝐹 ⊢ᵉ 𝑒₁ ⇓ 𝑣₁
           → 𝐹 ⊢ᵉ 𝑒₂ ⇓ 𝑣₂
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

c-thm-fwd : ∀{𝒸 : Cond}{𝐹 : Frm} → 𝐹 ⊢ᶜ 𝒸 → (⟦ 𝒸 ⟧ᶜ 𝐹 ≡ tt)
~c-thm-fwd : ∀{𝒸 : Cond}{𝐹 : Frm} → 𝐹 ⊬ᶜ 𝒸 → (⟦ 𝒸 ⟧ᶜ 𝐹 ≡ ff)
c-thm-fwd (c-tt{F}) =
  begin
    ⟦ ⇓true ⟧ᶜ F
  ≡⟨ refl ⟩
    tt
  ∎
c-thm-fwd (c-and{c1}{c2}{F} dat1 dat2) =
  let
    ⟦c1⟧F≡tt : ⟦ c1 ⟧ᶜ F ≡ tt
    ⟦c1⟧F≡tt = c-thm-fwd dat1
    ⟦c2⟧F≡tt : ⟦ c2 ⟧ᶜ F ≡ tt
    ⟦c2⟧F≡tt = c-thm-fwd dat2
  in begin
    ⟦ c1 ∧ᶜ c2 ⟧ᶜ F
  ≡⟨ refl ⟩
    (⟦ c1 ⟧ᶜ F) && (⟦ c2 ⟧ᶜ F)
  ≡⟨ cong2 _&&_ ⟦c1⟧F≡tt ⟦c2⟧F≡tt ⟩
    tt && tt
  ≡⟨ refl ⟩
    tt
  ∎  
c-thm-fwd (c-or₁{c1}{c2}{F} dat1) =
  let
    ⟦c1⟧F≡tt : ⟦ c1 ⟧ᶜ F ≡ tt
    ⟦c1⟧F≡tt = c-thm-fwd dat1
  in begin
    ⟦ c1 ∨ᶜ c2 ⟧ᶜ F
  ≡⟨ refl ⟩
    (⟦ c1 ⟧ᶜ F) || (⟦ c2 ⟧ᶜ F)
  ≡⟨ cong2 _||_ ⟦c1⟧F≡tt refl ⟩
    tt || (⟦ c2 ⟧ᶜ F)
  ≡⟨ refl ⟩
    tt
  ∎
c-thm-fwd (c-or₂{c1}{c2}{F} dat2) =
  let
    ⟦c2⟧F≡tt : ⟦ c2 ⟧ᶜ F ≡ tt
    ⟦c2⟧F≡tt = c-thm-fwd dat2
  in begin
    ⟦ c1 ∨ᶜ c2 ⟧ᶜ F
  ≡⟨ refl ⟩
    (⟦ c1 ⟧ᶜ F) || (⟦ c2 ⟧ᶜ F)
  ≡⟨ cong2 _||_ refl ⟦c2⟧F≡tt ⟩
    (⟦ c1 ⟧ᶜ F) || tt
  ≡⟨ ||-tt (⟦ c1 ⟧ᶜ F) ⟩
    tt
  ∎
c-thm-fwd (c-less{e1}{e2}{F}{v1}{v2} v1<v2 e1⇓v1 e2⇓v2) =
  let
    ⟦e1⟧F≡v1 : ⟦ e1 ⟧ᵉ F ≡ v1
    ⟦e1⟧F≡v1 = e-thm-fwd e1⇓v1
    ⟦e2⟧F≡v2 : ⟦ e2 ⟧ᵉ F ≡ v2
    ⟦e2⟧F≡v2 = e-thm-fwd e2⇓v2
  in
    begin
      ⟦ [ e1 <ᶜ e2 ] ⟧ᶜ F
    ≡⟨ refl ⟩
      ⟦ e1 ⟧ᵉ F < ⟦ e2 ⟧ᵉ F
    ≡⟨ cong2 _<_ ⟦e1⟧F≡v1 ⟦e2⟧F≡v2 ⟩
      v1 < v2
    ≡⟨ v1<v2 ⟩
     tt
   ∎
c-thm-fwd (c-eq{e1}{e2}{F}{v1}{v2} v1≡v2 e1⇓v1 e2⇓v2) =
  let
    ⟦e1⟧F≡v1 : ⟦ e1 ⟧ᵉ F ≡ v1
    ⟦e1⟧F≡v1 = e-thm-fwd e1⇓v1
    ⟦e2⟧F≡v2 : ⟦ e2 ⟧ᵉ F ≡ v2
    ⟦e2⟧F≡v2 = e-thm-fwd e2⇓v2
  in begin
    ⟦ [ e1 =ᶜ e2 ] ⟧ᶜ F
  ≡⟨ refl ⟩
    ⟦ e1 ⟧ᵉ F =ℕ ⟦ e2 ⟧ᵉ F
  ≡⟨ cong2 _=ℕ_ ⟦e1⟧F≡v1 ⟦e2⟧F≡v2 ⟩
    v1 =ℕ v2
  ≡⟨ v1≡v2 ⟩
   tt
  ∎
c-thm-fwd (c-not{c}{F} dat) =
  let
    ⟦c⟧F≡ff : ⟦ c ⟧ᶜ F ≡ ff
    ⟦c⟧F≡ff = ~c-thm-fwd dat
  in begin
  begin
    ⟦ ¬ᶜ c ⟧ᶜ F
  ≡⟨ refl ⟩
    ~ ⟦ c ⟧ᶜ F
  ≡⟨ cong ~_ ⟦c⟧F≡ff ⟩
    ~ ff
  ≡⟨ refl ⟩
    tt
  ∎
~c-thm-fwd (~c-ff{F}) =
  begin
    ⟦ ⇓false ⟧ᶜ F
  ≡⟨ refl ⟩
    ff
  ∎
~c-thm-fwd (~c-or{c1}{c2}{F} dat1 dat2) =
  let
    ⟦c1⟧F≡ff : ⟦ c1 ⟧ᶜ F ≡ ff
    ⟦c1⟧F≡ff = ~c-thm-fwd dat1
    ⟦c2⟧F≡ff : ⟦ c2 ⟧ᶜ F ≡ ff
    ⟦c2⟧F≡ff = ~c-thm-fwd dat2
  in begin
    ⟦ c1 ∨ᶜ c2 ⟧ᶜ F
  ≡⟨ refl ⟩
    (⟦ c1 ⟧ᶜ F) || (⟦ c2 ⟧ᶜ F)
  ≡⟨ cong2 _||_ ⟦c1⟧F≡ff ⟦c2⟧F≡ff ⟩
    ff || ff
  ≡⟨ refl ⟩
    ff
  ∎  
~c-thm-fwd (~c-and₁{c1}{c2}{F} dat1) =
  let
    ⟦c1⟧F≡ff : ⟦ c1 ⟧ᶜ F ≡ ff
    ⟦c1⟧F≡ff = ~c-thm-fwd dat1
  in begin
    ⟦ c1 ∧ᶜ c2 ⟧ᶜ F
  ≡⟨ refl ⟩
    (⟦ c1 ⟧ᶜ F) && (⟦ c2 ⟧ᶜ F)
  ≡⟨ cong2 _&&_ ⟦c1⟧F≡ff refl ⟩
    ff && (⟦ c2 ⟧ᶜ F)
  ≡⟨ refl ⟩
    ff
  ∎
~c-thm-fwd (~c-and₂{c1}{c2}{F} dat2) =
  let
    ⟦c2⟧F≡ff : ⟦ c2 ⟧ᶜ F ≡ ff
    ⟦c2⟧F≡ff = ~c-thm-fwd dat2
  in begin
  begin
    ⟦ c1 ∧ᶜ c2 ⟧ᶜ F
  ≡⟨ refl ⟩
    (⟦ c1 ⟧ᶜ F) && (⟦ c2 ⟧ᶜ F)
  ≡⟨ cong2 _&&_ refl ⟦c2⟧F≡ff ⟩
    (⟦ c1 ⟧ᶜ F) && ff
  ≡⟨ &&-ff (⟦ c1 ⟧ᶜ F) ⟩
    ff
  ∎
~c-thm-fwd (~c-less{e1}{e2}{F}{v1}{v2} v1≮v2 e1⇓v1 e2⇓v2) =
  let
    ⟦e1⟧F≡v1 : ⟦ e1 ⟧ᵉ F ≡ v1
    ⟦e1⟧F≡v1 = e-thm-fwd e1⇓v1
    ⟦e2⟧F≡v2 : ⟦ e2 ⟧ᵉ F ≡ v2
    ⟦e2⟧F≡v2 = e-thm-fwd e2⇓v2
  in
    begin
      ⟦ [ e1 <ᶜ e2 ] ⟧ᶜ F
    ≡⟨ refl ⟩
      ⟦ e1 ⟧ᵉ F < ⟦ e2 ⟧ᵉ F
    ≡⟨ cong2 _<_ ⟦e1⟧F≡v1 ⟦e2⟧F≡v2 ⟩
      v1 < v2
    ≡⟨ v1≮v2 ⟩
     ff
   ∎
~c-thm-fwd (~c-eq{e1}{e2}{F}{v1}{v2} v1≢v2 e1⇓v1 e2⇓v2) =
  let
    ⟦e1⟧F≡v1 : ⟦ e1 ⟧ᵉ F ≡ v1
    ⟦e1⟧F≡v1 = e-thm-fwd e1⇓v1
    ⟦e2⟧F≡v2 : ⟦ e2 ⟧ᵉ F ≡ v2
    ⟦e2⟧F≡v2 = e-thm-fwd e2⇓v2
  in begin
    ⟦ [ e1 =ᶜ e2 ] ⟧ᶜ F
  ≡⟨ refl ⟩
    ⟦ e1 ⟧ᵉ F =ℕ ⟦ e2 ⟧ᵉ F
  ≡⟨ cong2 _=ℕ_ ⟦e1⟧F≡v1 ⟦e2⟧F≡v2 ⟩
    v1 =ℕ v2
  ≡⟨ v1≢v2 ⟩
   ff
  ∎
~c-thm-fwd (~c-not{c}{F} ⊢c) =
  begin
    ⟦ ¬ᶜ c ⟧ᶜ F
  ≡⟨ refl ⟩
    ~ ⟦ c ⟧ᶜ F
  ≡⟨ cong ~_ (c-thm-fwd ⊢c) ⟩
    ~ tt
  ≡⟨ refl ⟩
    ff
  ∎

-- These can probably be shown just by using
-- the contrapositives of c-thm-fwd and ~c-thm-fwd
postulate
  c-thm-rev : ∀{𝒸 : Cond}{𝐹 : Frm} → (⟦ 𝒸 ⟧ᶜ 𝐹 ≡ tt) → 𝐹 ⊢ᶜ 𝒸
  ~c-thm-rev : ∀{𝒸 : Cond}{𝐹 : Frm} → (⟦ 𝒸 ⟧ᶜ 𝐹 ≡ ff) → 𝐹 ⊬ᶜ 𝒸


--
-- SEMANTICS of program statements
-- as a state transformation relation
--

data _=[_]⇒_ : Frm → Stmt → Frm → Set where

  s-skip : ∀ {𝐹 : Frm}
    --------------
    → 𝐹 =[ skip ]⇒ 𝐹

  s-assign : ∀ {𝑥 : Id} {𝑒 : Expn} {𝐹 : Frm}  {𝑣 : Val}
    → 𝐹 ⊢ᵉ 𝑒 ⇓ 𝑣
    ---------------------------
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

  --
  -- A lil cheat: "returns" is just assign; doesn't exit

  s-return : ∀ {𝑒 : Expn} {𝐹 : Frm}  {𝑣 : Val}
    → 𝐹 ⊢ᵉ 𝑒 ⇓ 𝑣
    -------------------------------------
    → 𝐹 =[ returns 𝑒 ]⇒ (𝐹 ∣ "retval" ↦ 𝑣)



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
  X ∷= ⇑ arg1 ↩
  Y ∷= ⇓ 1 ↩
  by X repeat 
    Z∷=X*Y ↩
    Y ∷= ⇑ Z
  end ↩
  returns ⇑ Y

min-pgm : Stmt
min-pgm = if [ ⇑ arg2 <ᶜ ⇑ arg1 ] then
            X ∷= ⇑ arg1 ↩
            arg1 ∷= ⇑ arg2 ↩
            arg2 ∷= ⇑ X
          else
            skip
          end

result1 = ⟦ pgm1 ⟧ˢ [-↦0]
result2 = ⟦ pgm2 ⟧ˢ [-↦0]

[➊↦_] : Val → Frm
[➊↦ 𝑣 ] = [-↦0] ∣ arg1 ↦ 𝑣

[➊↦_,➋↦_] : Val →  Val → Frm
[➊↦ 𝑣₁ ,➋↦ 𝑣₂ ] = (([-↦0] ∣ arg1 ↦ 𝑣₁) ∣ arg2 ↦ 𝑣₂ )

frame6 = ((((( [➊↦ 3 ] ∣ X ↦ 0) ∣ Y ↦ 6) ∣ W ↦ 0) ∣ Z ↦ 6) ∣ retval ↦ 6)
postulate
  test6 : [➊↦ 3 ] =[ fact-pgm ]⇒ frame6

exec : Stmt → Frm
exec 𝑠 = ⟦ 𝑠 ⟧ˢ [-↦0] 

exec1 : Stmt → Val → Frm
exec1 𝑠 𝑣₁ = ⟦ 𝑠 ⟧ˢ [➊↦ 𝑣₁ ]

exec2 : Stmt → Val → Val → Frm
exec2 𝑠 𝑣₁ 𝑣₂ = ⟦ 𝑠 ⟧ˢ [➊↦ 𝑣₁ ,➋↦ 𝑣₂ ]

test7 = exec2 min-pgm 7 5

test7a : (test7 ∥ arg1) ≡ 5
test7a = refl

test7b : (test7 ∥ arg2) ≡ 7
test7b = refl

postulate
  s-thm : ∀ {𝑠 : Stmt } {𝐹 : Frm} → 𝐹 =[ 𝑠 ]⇒ (⟦ 𝑠 ⟧ˢ 𝐹)

postulate
  fact-thm : ∀ {n : ℕ} {𝐹 : Frm} → [➊↦ n ] =[ fact-pgm ]⇒ 𝐹 → 𝐹 ⊢ᶠ retval ↦ (factorial n)
