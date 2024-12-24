Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516577_term_abbrevs.
Require Import EVEN_MULT_spec.
Lemma lem516574 (m : nat) : term0 m.
Proof. exact (@lem126076 m). Qed.
Lemma lem516575 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem516576 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem516575 m) (@lem516574 m)). Qed.
Lemma lem516577 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem516576 m n). Qed.
