Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm98_term_abbrevs.
Require Import F_DEF_spec.
Lemma lem94 (h1 : False) : False.
Proof. exact (h1). Qed.
Lemma lem95 (h1 : False) : term0.
Proof. exact (EQ_MP (@lem55) (@lem94 h1)). Qed.
Lemma lem96 (P : Prop) (h1 : False) : term1 P.
Proof. exact (@lem95 h1 P). Qed.
Lemma lem97 (P : Prop) : (term1 P) = P.
Proof. exact (eq_refl (term1 P)). Qed.
Lemma lem98 (P : Prop) (h1 : False) : P.
Proof. exact (EQ_MP (@lem97 P) (@lem96 P h1)). Qed.
