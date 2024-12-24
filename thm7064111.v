Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem7064111 {_131408 : Type'} : (@iterate real _131408 real_add) = (@iterate real _131408 real_add).
Proof. exact (eq_refl (@iterate real _131408 real_add)). Qed.
