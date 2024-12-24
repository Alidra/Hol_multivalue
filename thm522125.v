Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm522125_term_abbrevs.
Require Import LE_EXISTS_spec.
Lemma lem522122 (m : nat) : term0 m.
Proof. exact (@lem99708 m). Qed.
Lemma lem522123 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem522124 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem522123 m) (@lem522122 m)). Qed.
Lemma lem522125 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem522124 m n). Qed.
