Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm534473_term_abbrevs.
Require Import thm534468_spec.
Lemma lem534469 : term0.
Proof. exact (proj2 (@lem534468)). Qed.
Lemma lem534470 (m : nat) : term1 m.
Proof. exact (@lem534469 m). Qed.
Lemma lem534471 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem534472 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem534471 m) (@lem534470 m)). Qed.
Lemma lem534473 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem534472 m n). Qed.
