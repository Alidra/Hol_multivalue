Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm515681_term_abbrevs.
Require Import thm515633_spec.
Lemma lem515677 : term0.
Proof. exact (proj2 (@lem515633)). Qed.
Lemma lem515678 (m : nat) : term1 m.
Proof. exact (@lem515677 m). Qed.
Lemma lem515679 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem515680 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem515679 m) (@lem515678 m)). Qed.
Lemma lem515681 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem515680 m n). Qed.
