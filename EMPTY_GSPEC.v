Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EMPTY_GSPEC_term_abbrevs.
Require Import thm3399706_spec.
Require Import thm3399757_spec.
Lemma lem3399758 {_88295 : Type'} : (term0 _88295) = (@EMPTY _88295).
Proof. exact (EQ_MP (@lem3399706 _88295) (@lem3399757 _88295)). Qed.
