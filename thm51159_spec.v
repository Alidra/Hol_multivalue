Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem51159 : forall {A B : Type'} (a0 : A) (a1 : B), a1 = (@ε ((prod A B) -> B) (fun fn : (prod A B) -> B => forall a0' : A, forall a1' : B, (fn (@pair A B a0' a1')) = a1') (@pair A B a0 a1)).
