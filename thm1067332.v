Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1067332_term_abbrevs.
Require Import thm1067008_spec.
Require Import thm1067330_spec.
Lemma lem1067331 {A B : Type'} (INL' : type1431 A B) (h1 : INL' = (term0 A B)) : (term1 A B) = (term2 A B INL').
Proof. exact (SYM (@lem1067008 A B INL' h1)). Qed.
Lemma lem1067332 {A B : Type'} (INL' : type1431 A B) (h1 : INL' = (term0 A B)) : (@inl A B) = (term2 A B INL').
Proof. exact (TRANS (@lem1067330 A B) (@lem1067331 A B INL' h1)). Qed.
