Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm546193_term_abbrevs.
Require Import thm546188_spec.
Lemma lem546189 : term0.
Proof. exact (proj2 (@lem546188)). Qed.
Lemma lem546190 (m : nat) : term1 m.
Proof. exact (@lem546189 m). Qed.
Lemma lem546191 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem546192 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem546191 m) (@lem546190 m)). Qed.
Lemma lem546193 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem546192 m n). Qed.
