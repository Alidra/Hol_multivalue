Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1069015_term_abbrevs.
Lemma lem1069015 {A : Type'} (NONE' : recspace A) (h1 : NONE' = (term0 A)) : NONE' = (term0 A).
Proof. exact (h1). Qed.
