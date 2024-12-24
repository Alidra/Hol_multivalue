Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1070450_term_abbrevs.
Lemma lem1070450 {A : Type'} (NIL' : recspace A) (h1 : NIL' = (term0 A)) : NIL' = (term0 A).
Proof. exact (h1). Qed.
