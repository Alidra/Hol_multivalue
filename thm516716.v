Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516716_term_abbrevs.
Require Import thm516703_spec.
Lemma lem516704 : term0.
Proof. exact (proj2 (@lem516703)). Qed.
Lemma lem516712 : term1.
Proof. exact (proj1 (@lem516704)). Qed.
Lemma lem516713 (m : nat) : term2 m.
Proof. exact (@lem516712 m). Qed.
Lemma lem516714 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem516715 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem516714 m) (@lem516713 m)). Qed.
Lemma lem516716 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem516715 m n). Qed.
