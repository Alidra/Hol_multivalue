Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1069366_term_abbrevs.
Require Import thm1069365_spec.
Lemma lem1069366 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term0 A NONE' SOME')) : term1 A option' NONE' SOME'.
Proof. exact (proj2 (@lem1069365 A option' NONE' SOME' h1)). Qed.
