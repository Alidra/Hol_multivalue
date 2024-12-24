Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem7064097 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (@sum_def _131408). Qed.
