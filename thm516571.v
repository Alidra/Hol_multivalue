Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516571_term_abbrevs.
Require Import EVEN_ADD_spec.
Lemma lem516568 (m : nat) : term0 m.
Proof. exact (@lem125496 m). Qed.
Lemma lem516569 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem516570 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem516569 m) (@lem516568 m)). Qed.
Lemma lem516571 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem516570 m n). Qed.
