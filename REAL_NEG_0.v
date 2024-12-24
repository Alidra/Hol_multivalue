Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NEG_0_term_abbrevs.
Require Import thm1361604_spec.
Require Import thm1362040_spec.
Lemma lem1362041 : term0 = term1.
Proof. exact (EQ_MP (@lem1361604) (@lem1362040)). Qed.
