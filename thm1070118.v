Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1070118_term_abbrevs.
Require Import thm1069778_spec.
Require Import thm1070110_spec.
Lemma lem1070111 {A : Type'} (SOME' : type1432 A) (h1 : SOME' = (term0 A)) : (term1 A) = (term2 A SOME').
Proof. exact (SYM (@lem1069778 A SOME' h1)). Qed.
Lemma lem1070112 {A : Type'} (SOME' : type1432 A) (h1 : SOME' = (term0 A)) : (@Some A) = (term2 A SOME').
Proof. exact (TRANS (@lem1070110 A) (@lem1070111 A SOME' h1)). Qed.
Lemma lem1070113 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1070114 {A : Type'} (a : A) (SOME' : type1432 A) (h1 : SOME' = (term0 A)) : (@Some A a) = (term3 A SOME' a).
Proof. exact (MK_COMB (@lem1070112 A SOME' h1) (@lem1070113 A a)). Qed.
Lemma lem1070115 {A : Type'} (SOME' : type1432 A) (a : A) : (term3 A SOME' a) = (term4 A SOME' a).
Proof. exact (eq_refl (term3 A SOME' a)). Qed.
Lemma lem1070116 {A : Type'} (a : A) : (term5 A a) = (term5 A a).
Proof. exact (eq_refl (term5 A a)). Qed.
Lemma lem1070117 {A : Type'} (SOME' : type1432 A) (a : A) : ((@Some A a) = (term3 A SOME' a)) = ((@Some A a) = (term4 A SOME' a)).
Proof. exact (MK_COMB (@lem1070116 A a) (@lem1070115 A SOME' a)). Qed.
Lemma lem1070118 {A : Type'} (a : A) (SOME' : type1432 A) (h1 : SOME' = (term0 A)) : (@Some A a) = (term4 A SOME' a).
Proof. exact (EQ_MP (@lem1070117 A SOME' a) (@lem1070114 A a SOME' h1)). Qed.
