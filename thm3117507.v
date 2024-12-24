Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3117507_term_abbrevs.
Require Import num_divides_spec.
Lemma lem3117504 (a : nat) : term0 a.
Proof. exact (@lem2836659 a). Qed.
Lemma lem3117505 (a : nat) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem3117506 (a : nat) : term1 a.
Proof. exact (EQ_MP (@lem3117505 a) (@lem3117504 a)). Qed.
Lemma lem3117507 (a : nat) (b : nat) : term2 a b.
Proof. exact (@lem3117506 a b). Qed.
