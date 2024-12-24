Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SGN_0_term_abbrevs.
Require Import REAL_SGN_0_spec.
Require Import thm2309248_spec.
Lemma lem2309249 : term0 = term1.
Proof. exact (EQ_MP (@lem2309248) (@lem1710423)). Qed.
