Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3117501_term_abbrevs.
Require Import num_congruent_spec.
Lemma lem3117495 (x : nat) : term0 x.
Proof. exact (@lem2837601 x). Qed.
Lemma lem3117496 (x : nat) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3117497 (x : nat) : term1 x.
Proof. exact (EQ_MP (@lem3117496 x) (@lem3117495 x)). Qed.
Lemma lem3117498 (x : nat) (y : nat) : term2 x y.
Proof. exact (@lem3117497 x y). Qed.
Lemma lem3117499 (x : nat) (y : nat) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem3117500 (x : nat) (y : nat) : term3 x y.
Proof. exact (EQ_MP (@lem3117499 x y) (@lem3117498 x y)). Qed.
Lemma lem3117501 (x : nat) (y : nat) (n : nat) : term4 x y n.
Proof. exact (@lem3117500 x y n). Qed.
