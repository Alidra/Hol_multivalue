Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516634_term_abbrevs.
Require Import EQ_MULT_LCANCEL_spec.
Lemma lem516628 (m : nat) : term0 m.
Proof. exact (@lem84830 m). Qed.
Lemma lem516629 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem516630 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem516629 m) (@lem516628 m)). Qed.
Lemma lem516631 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem516630 m n). Qed.
Lemma lem516632 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem516633 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem516632 m n) (@lem516631 m n)). Qed.
Lemma lem516634 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem516633 m n p). Qed.
