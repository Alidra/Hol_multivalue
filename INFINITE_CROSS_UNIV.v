Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INFINITE_CROSS_UNIV_term_abbrevs.
Require Import thm4333782_spec.
Require Import thm4334154_spec.
Lemma lem4334155 {A B : Type'} : (@INFINITE (prod A B) (@UNIV (prod A B))) = (term0 A B).
Proof. exact (EQ_MP (@lem4333782 A B) (@lem4334154 A B)). Qed.
