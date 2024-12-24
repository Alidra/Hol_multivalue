Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1070451_term_abbrevs.
Lemma lem1070451 {A : Type'} (CONS' : type1399 A) (h1 : CONS' = (term0 A)) : CONS' = (term0 A).
Proof. exact (h1). Qed.
