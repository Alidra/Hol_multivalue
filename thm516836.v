Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516836_term_abbrevs.
Require Import thm516816_spec.
Lemma lem516833 (m : nat) : term0 m.
Proof. exact (@lem516816 m). Qed.
Lemma lem516834 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem516835 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem516834 m) (@lem516833 m)). Qed.
Lemma lem516836 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem516835 m n). Qed.
