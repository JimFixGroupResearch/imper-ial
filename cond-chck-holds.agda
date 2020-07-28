
open import level
open import bool
open import bool-thms
open import eq
open import eq-reasoning
open import sum
open import nat

data Lgc : Set where
  ttrue : Lgc
  ffalse : Lgc
  aand : Lgc → Lgc → Lgc
  oor : Lgc → Lgc → Lgc
  nnot : Lgc → Lgc

check_ : Lgc → 𝔹
check ttrue        = tt
check ffalse       = ff
check (aand c1 c2) = (check c1) && (check c2)
check (oor c1 c2)  = (check c1) || (check c2)
check (nnot c)     = ~(check c)

data _isTrue : Lgc → Set
data _isFalse : Lgc → Set

data _isTrue where

  c-tt : 
          -----------
          ttrue isTrue


  c-and : ∀ {c1 c2 : Lgc} 
          → c1 isTrue
          → c2 isTrue
          -----------------
          → (aand c1 c2) isTrue

  c-or₁ : ∀ {c1 c2 : Lgc} 
          → c1 isTrue
          ---------------
          → (oor c1 c2) isTrue

  c-or₂ : ∀ {c1 c2 : Lgc} 
          → c2 isTrue
          ----------------
          → (oor c1 c2) isTrue

  c-not : ∀ {c : Lgc}
          → c isFalse
          -------------
          → (nnot c) isTrue


data _isFalse where

  ~c-ff :
    --------------
    ffalse isFalse

  ~c-or : ∀ {c1 c2 : Lgc}
    → c1 isFalse 
    → c2 isFalse     
    ---------------------
    → (oor c1 c2) isFalse

  ~c-and₁ : ∀ {c1 c2 : Lgc} 
    → c1 isFalse
    ----------------------
    → (aand c1 c2) isFalse

  ~c-and₂ : ∀ {c1 c2 : Lgc}
    → c2 isFalse
    -----------------
    → (aand c1 c2) isFalse

  ~c-not : ∀ {c : Lgc}
    → c isTrue
    -------------
    → (nnot c) isFalse

c-thm :  ∀ {c : Lgc} → c isTrue  → (check c ≡ tt)
~c-thm : ∀ {c : Lgc} → c isFalse → (check c ≡ ff)

c-thm (c-tt) =
  begin
    check ttrue
  ≡⟨ refl ⟩
    tt
  ∎
c-thm (c-and{c1}{c2} dat1 dat2) =
  begin
    check (aand c1 c2)
  ≡⟨ refl ⟩
    (check c1) && (check c2)
  ≡⟨ congf2{f = _&&_}{f' = _&&_} refl (c-thm dat1) (c-thm dat2) ⟩
    tt && tt
  ≡⟨ refl ⟩
    tt
  ∎  
c-thm (c-or₁{c1}{c2} dat1) =
  begin
    check (oor c1 c2)
  ≡⟨ refl ⟩
    (check c1) || (check c2)
  ≡⟨ congf2{f = _||_}{f' = _||_} refl (c-thm dat1) refl ⟩
    tt || (check c2)
  ≡⟨ refl ⟩
    tt
  ∎
c-thm (c-or₂{c1}{c2} dat2) =
  begin
    check (oor c1 c2)
  ≡⟨ refl ⟩
    (check c1) || (check c2)
  ≡⟨ congf2{f = _||_}{f' = _||_} refl refl (c-thm dat2) ⟩
    (check c1) || tt
  ≡⟨ ||-tt (check c1)⟩
    tt
  ∎
c-thm (c-not{c} dat) =
  begin
    check (nnot c)
  ≡⟨ refl ⟩
    ~ (check c)
  ≡⟨ congf{f = ~_}{f' = ~_} refl (~c-thm dat) ⟩
    ~ ff
  ≡⟨ refl ⟩
    tt
  ∎
  
~c-thm (~c-ff) =
  begin
    check ffalse
  ≡⟨ refl ⟩
    ff
  ∎
~c-thm (~c-or{c1}{c2} dat1 dat2) =
  begin
    check (oor c1 c2)
  ≡⟨ refl ⟩
    (check c1) || (check c2)
  ≡⟨ congf2{f = _||_}{f' = _||_} refl (~c-thm dat1) (~c-thm dat2) ⟩
    ff || ff
  ≡⟨ refl ⟩
    ff
  ∎  
~c-thm (~c-and₁{c1}{c2} dat1) =
  begin
    check (aand c1 c2)
  ≡⟨ refl ⟩
    (check c1) && (check c2)
  ≡⟨ congf2{f = _&&_}{f' = _&&_} refl (~c-thm dat1) refl ⟩
    ff && (check c2)
  ≡⟨ refl ⟩
    ff
  ∎
~c-thm (~c-and₂{c1}{c2} dat2) =
  begin
    check (aand c1 c2)
  ≡⟨ refl ⟩
    (check c1) && (check c2)
  ≡⟨ congf2{f = _&&_}{f' = _&&_} refl refl (~c-thm dat2) ⟩
    (check c1) && ff
  ≡⟨ &&-ff (check c1)⟩
    ff
  ∎

~c-thm (~c-not{c} dat) =
  begin
    check (nnot c)
  ≡⟨ refl ⟩
    ~ (check c)
  ≡⟨ congf{f = ~_}{f' = ~_} refl (c-thm dat) ⟩
    ~ tt
  ≡⟨ refl ⟩
    ff
  ∎ 
