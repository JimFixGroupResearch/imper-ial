module eq-reas-nouni {A : Set} where

  open import eq
  
  infix  1 begin_
  infixr 2 _equiv[]_ _equiv[_]_
  infix  3 _qed

  begin_ : ∀ {x y : A}
    → x ≡ y
    -----
    → x ≡ y
  begin x≡y  =  x≡y

  _equiv[]_ : ∀ (x : A) {y : A}
    → x ≡ y
    -----
    → x ≡ y
  x equiv[] x≡y  =  x≡y

  _equiv[_]_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
    -----
    → x ≡ z
  x equiv[ x≡y ] y≡z  =  trans x≡y y≡z

  _qed : ∀ (x : A)
    -----
    → x ≡ x
  x qed  =  refl

