Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NEUTRAL_REAL_MUL_term_abbrevs.
Require Import thm6910119_spec.
Require Import thm6911417_spec.
Lemma lem6911418 : (@neutral real real_mul) = term0.
Proof. exact (EQ_MP (@lem6910119) (@lem6911417)). Qed.
