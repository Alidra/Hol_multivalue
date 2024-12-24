Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3117486_term_abbrevs.
Require Import NUM_GCD_spec.
Lemma lem3117483 (a : nat) : term0 a.
Proof. exact (@lem3070443 a). Qed.
Lemma lem3117484 (a : nat) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem3117485 (a : nat) : term1 a.
Proof. exact (EQ_MP (@lem3117484 a) (@lem3117483 a)). Qed.
Lemma lem3117486 (a : nat) (b : nat) : term2 a b.
Proof. exact (@lem3117485 a b). Qed.
