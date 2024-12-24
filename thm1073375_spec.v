Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1073375 : forall {A B : Type'} (x : A) (a : A) (y : B) (b : B), (fun b' : B => ((@pair A B x y) = (@pair A B a b')) = ((x = a) /\ (y = b'))) b.
