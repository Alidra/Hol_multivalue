Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1340073_term_abbrevs.
Require Import TREAL_INV_0_spec.
Require Import thm1340072_spec.
Lemma lem1340073 : term0 = term1.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
