Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1069766_term_abbrevs.
Require Import thm1069434_spec.
Require Import thm1069764_spec.
Lemma lem1069765 {A : Type'} (NONE' : recspace A) (h1 : NONE' = (term0 A)) : (term1 A) = (@_mk_option A NONE').
Proof. exact (SYM (@lem1069434 A NONE' h1)). Qed.
Lemma lem1069766 {A : Type'} (NONE' : recspace A) (h1 : NONE' = (term0 A)) : (@None A) = (@_mk_option A NONE').
Proof. exact (TRANS (@lem1069764 A) (@lem1069765 A NONE' h1)). Qed.
