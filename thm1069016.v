Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1069016_term_abbrevs.
Lemma lem1069016 {A : Type'} (SOME' : type1432 A) (h1 : SOME' = (term0 A)) : SOME' = (term0 A).
Proof. exact (h1). Qed.
