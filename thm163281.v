Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm163281_term_abbrevs.
Require Import thm10578_spec.
Require Import thm10597_spec.
Lemma lem163279 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem163280 : term1 = term2.
Proof. exact (@lem163279 term1). Qed.
Lemma lem163281 : term2 = term1.
Proof. exact (SYM (@lem163280)). Qed.
