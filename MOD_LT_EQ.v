Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_LT_EQ_term_abbrevs.
Require Import thm163281_spec.
Require Import thm165614_spec.
Lemma lem165615 : term0.
Proof. exact (EQ_MP (@lem163281) (@lem165614)). Qed.
