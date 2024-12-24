Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1069368_term_abbrevs.
Require Import thm1069366_spec.
Lemma lem1069368 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term0 A NONE' SOME')) : term1 A NONE' SOME' option'.
Proof. exact (proj1 (@lem1069366 A option' NONE' SOME' h1)). Qed.
