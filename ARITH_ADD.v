Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARITH_ADD_term_abbrevs.
Require Import thm513870_spec.
Require Import thm514290_spec.
Lemma lem514291 : term0.
Proof. exact (EQ_MP (@lem513870) (@lem514290)). Qed.
