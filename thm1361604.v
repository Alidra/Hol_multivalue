Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1361604_term_abbrevs.
Require Import thm10578_spec.
Require Import thm10597_spec.
Lemma lem1361602 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1361603 : (term1 = term2) = term3.
Proof. exact (@lem1361602 (term1 = term2)). Qed.
Lemma lem1361604 : term3 = (term1 = term2).
Proof. exact (SYM (@lem1361603)). Qed.
