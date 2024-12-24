Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1066572_term_abbrevs.
Lemma lem1066572 {A B : Type'} (INR' : type1479 A B) (h1 : INR' = (term0 A B)) : INR' = (term0 A B).
Proof. exact (h1). Qed.
