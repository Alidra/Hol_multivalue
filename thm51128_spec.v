Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem51128 : forall {A B : Type'} (a0 : A) (a1 : B), a0 = (@ε ((prod A B) -> A) (fun fn : (prod A B) -> A => forall a0' : A, forall a1' : B, (fn (@pair A B a0' a1')) = a0') (@pair A B a0 a1)).
