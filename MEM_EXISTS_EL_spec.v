Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1162240 : forall {_27312 : Type'}, forall l : list _27312, forall x : _27312, (@List.In _27312 x l) = (exists i : nat, (Peano.lt i (@List.length _27312 l)) /\ (x = (@EL _27312 i l))).
