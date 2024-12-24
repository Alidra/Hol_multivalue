Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm538290_term_abbrevs.
Require Import thm538262_spec.
Lemma lem538286 : term0.
Proof. exact (proj1 (@lem538262)). Qed.
Lemma lem538287 (m : nat) : term1 m.
Proof. exact (@lem538286 m). Qed.
Lemma lem538288 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem538289 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem538288 m) (@lem538287 m)). Qed.
Lemma lem538290 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem538289 m n). Qed.
