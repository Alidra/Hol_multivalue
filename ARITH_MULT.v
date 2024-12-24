Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARITH_MULT_term_abbrevs.
Require Import thm514761_spec.
Require Import thm515543_spec.
Lemma lem515544 : term0.
Proof. exact (EQ_MP (@lem514761) (@lem515543)). Qed.
