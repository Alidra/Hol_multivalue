Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_0_term_abbrevs.
Require Import REAL_ABS_0_spec.
Require Import thm2299969_spec.
Lemma lem2299970 : term0 = term1.
Proof. exact (EQ_MP (@lem2299969) (@lem1528209)). Qed.
