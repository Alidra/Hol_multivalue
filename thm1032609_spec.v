Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1032609 : forall {A : Type'}, forall add : A -> A -> A, forall mul : A -> A -> A, forall n0 : A, ((forall x : A, (mul n0 x) = n0) /\ ((forall x : A, forall y : A, forall z : A, ((add x y) = (add x z)) = (y = z)) /\ (forall w : A, forall x : A, forall y : A, forall z : A, ((add (mul w y) (mul x z)) = (add (mul w z) (mul x y))) = ((w = x) \/ (y = z))))) -> (forall a : A, forall b : A, forall c : A, forall d : A, ((~ (a = b)) /\ (~ (c = d))) = (~ ((add (mul a c) (mul b d)) = (add (mul a d) (mul b c))))) /\ (forall n : A, forall a : A, forall b : A, forall c : A, forall d : A, (~ (n = n0)) -> ((a = b) /\ (~ (c = d))) -> ~ ((add a (mul n c)) = (add b (mul n d)))).
