Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3117441_term_abbrevs.
Require Import thm3117397_spec.
Lemma lem3117438 (m : nat) : term0 m.
Proof. exact (@lem3117397 m). Qed.
Lemma lem3117439 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem3117440 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem3117439 m) (@lem3117438 m)). Qed.
Lemma lem3117441 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem3117440 m n). Qed.
