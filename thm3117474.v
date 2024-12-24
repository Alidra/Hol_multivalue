Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3117474_term_abbrevs.
Require Import thm3117317_spec.
Lemma lem3117471 (m : nat) : term0 m.
Proof. exact (@lem3117317 m). Qed.
Lemma lem3117472 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem3117473 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem3117472 m) (@lem3117471 m)). Qed.
Lemma lem3117474 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem3117473 m n). Qed.
