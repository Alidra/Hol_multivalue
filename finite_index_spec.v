Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7616152 : forall {_139760 _139770 : Type'}, forall x : cart _139760 _139770, forall i : nat, (@dollar _139760 _139770 x i) = (@dest_cart _139760 _139770 x (@finite_index _139770 i)).
