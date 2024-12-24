Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Lemma lem6910059 {_126259 : Type'} : (@iterate real _126259 real_mul) = (@iterate real _126259 real_mul).
Proof. exact (eq_refl (@iterate real _126259 real_mul)). Qed.
