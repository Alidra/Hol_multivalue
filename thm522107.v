Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm522107_term_abbrevs.
Require Import ADD_SUB2_spec.
Lemma lem522104 (m : nat) : term0 m.
Proof. exact (@lem135939 m). Qed.
Lemma lem522105 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem522106 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem522105 m) (@lem522104 m)). Qed.
Lemma lem522107 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem522106 m n). Qed.
