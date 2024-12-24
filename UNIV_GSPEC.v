Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIV_GSPEC_term_abbrevs.
Require Import thm3399787_spec.
Require Import thm3399835_spec.
Lemma lem3399836 {_88312 : Type'} : (term0 _88312) = (@UNIV _88312).
Proof. exact (EQ_MP (@lem3399787 _88312) (@lem3399835 _88312)). Qed.
