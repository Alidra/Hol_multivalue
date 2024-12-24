Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1067670_term_abbrevs.
Require Import thm1067344_spec.
Require Import thm1067668_spec.
Lemma lem1067669 {A B : Type'} (INR' : type1479 A B) (h1 : INR' = (term0 A B)) : (term1 A B) = (term2 A B INR').
Proof. exact (SYM (@lem1067344 A B INR' h1)). Qed.
Lemma lem1067670 {A B : Type'} (INR' : type1479 A B) (h1 : INR' = (term0 A B)) : (@inr A B) = (term2 A B INR').
Proof. exact (TRANS (@lem1067668 A B) (@lem1067669 A B INR' h1)). Qed.
