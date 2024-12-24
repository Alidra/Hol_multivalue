Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1069367_term_abbrevs.
Require Import thm1069365_spec.
Lemma lem1069367 {A : Type'} (option' : type1338 A) (NONE' : recspace A) (SOME' : type1432 A) (h1 : option' = (term0 A NONE' SOME')) : term1 A NONE' option' SOME'.
Proof. exact (proj1 (@lem1069365 A option' NONE' SOME' h1)). Qed.
