Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm912931_term_abbrevs.
Require Import thm719529_spec.
Require Import thm719543_spec.
Lemma lem912931 : term0 = term1.
Proof. exact (TRANS (@lem719529) (@lem719543)). Qed.
