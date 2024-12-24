Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1138200 : forall {_26795 : Type'}, forall n : nat, forall x : _26795, (@List.length _26795 (@repeat_with_perm_args _26795 n x)) = n.
