Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARITH_PRE_term_abbrevs.
Require Import thm513386_spec.
Require Import thm513549_spec.
Lemma lem513550 : term0.
Proof. exact (EQ_MP (@lem513386) (@lem513549)). Qed.
