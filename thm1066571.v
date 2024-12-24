Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1066571_term_abbrevs.
Lemma lem1066571 {A B : Type'} (INL' : type1431 A B) (h1 : INL' = (term0 A B)) : INL' = (term0 A B).
Proof. exact (h1). Qed.
