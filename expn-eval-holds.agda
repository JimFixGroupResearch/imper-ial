open import lib
open import eq-reas-nouni

equiv = _≡_

Val = nat

data Expn : Set where
  val : Val -> Expn
  plus : Expn -> Expn -> Expn

eval : Expn -> Val
eval (val v) = v
eval (plus e1 e2) = (eval e1) + (eval e2)

data evalsTo : Expn -> Val -> Set where

  e-val : forall {v : Val}
          ------------------------
          -> (evalsTo (val v) v)

  e-add : forall {e1 e2 : Expn}{v1 v2 : Val}
          -> (evalsTo e1 v1) 
          -> (evalsTo e2 v2) 
          -------------------------------------
          -> (evalsTo (plus e1 e2) (v1 + v2))

e-thm-fwd : forall {e : Expn}{v : Val}
  -> evalsTo e v -> equiv (eval e) v

e-thm-fwd (e-val{v}) =
  begin
    eval (val v)
  equiv[ refl ]
    v
  qed
e-thm-fwd (e-add{e1}{e2}{v1}{v2} e1-evalsTo-v1 e2-evalsTo-v2) =
  let
    eval-e1-is-v1 = e-thm-fwd e1-evalsTo-v1
    eval-e2-is-v2 = e-thm-fwd e2-evalsTo-v2
  in begin
    eval (plus e1 e2)
  equiv[ refl ] 
    (eval e1) + (eval e2)
  equiv[ cong2 _+_ eval-e1-is-v1 eval-e2-is-v2 ]
    v1 + v2
  qed

e-thm-alt : forall (e : Expn) -> evalsTo e (eval e)
e-thm-alt (val v) = e-val
e-thm-alt (plus e1 e2) = (e-add (e-thm-alt e1) (e-thm-alt e2))

     
  

