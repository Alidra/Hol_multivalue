Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NEUTRAL_MUL_term_abbrevs.
Require Import thm6898643_spec.
Require Import thm6901231_spec.
Lemma lem6901232 : (@neutral nat Nat.mul) = term0.
Proof. exact (EQ_MP (@lem6898643) (@lem6901231)). Qed.
