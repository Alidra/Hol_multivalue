Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1065430 : forall {A B : Type'}, forall Fn : nat -> A -> (nat -> recspace A) -> (nat -> B) -> B, exists f : (recspace A) -> B, forall c : nat, forall i : A, forall r : nat -> recspace A, (f (@CONSTR A c i r)) = (Fn c i r (fun n : nat => f (r n))).
