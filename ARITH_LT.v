Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARITH_LT_term_abbrevs.
Require Import thm0_spec.
Require Import thm520356_spec.
Lemma lem520357 : term0.
Proof. exact (EQ_MP (@lem520356) (@lem0)). Qed.
