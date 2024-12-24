Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3117492 : forall (a : nat) (b : nat), (fun b' : nat => (num_coprime (@pair nat nat a b')) = (int_coprime (@pair int int (int_of_num a) (int_of_num b')))) b.
