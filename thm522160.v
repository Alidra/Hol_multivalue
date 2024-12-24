Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm522160_term_abbrevs.
Require Import thm135075_spec.
Lemma lem522156 : term0.
Proof. exact (proj2 (@lem135075)). Qed.
Lemma lem522157 (m : nat) : term1 m.
Proof. exact (@lem522156 m). Qed.
Lemma lem522158 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem522159 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem522158 m) (@lem522157 m)). Qed.
Lemma lem522160 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem522159 m n). Qed.
