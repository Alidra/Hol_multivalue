Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1067682_term_abbrevs.
Require Import thm1067670_spec.
Lemma lem1067677 {B : Type'} (a : B) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1067678 {A B : Type'} (a : B) (INR' : type1479 A B) (h1 : INR' = (term0 A B)) : (@inr A B a) = (term1 A B INR' a).
Proof. exact (MK_COMB (@lem1067670 A B INR' h1) (@lem1067677 B a)). Qed.
Lemma lem1067679 {A B : Type'} (INR' : type1479 A B) (a : B) : (term1 A B INR' a) = (term2 A B INR' a).
Proof. exact (eq_refl (term1 A B INR' a)). Qed.
Lemma lem1067680 {A B : Type'} (a : B) : (term3 A B a) = (term3 A B a).
Proof. exact (eq_refl (term3 A B a)). Qed.
Lemma lem1067681 {A B : Type'} (INR' : type1479 A B) (a : B) : ((@inr A B a) = (term1 A B INR' a)) = ((@inr A B a) = (term2 A B INR' a)).
Proof. exact (MK_COMB (@lem1067680 A B a) (@lem1067679 A B INR' a)). Qed.
Lemma lem1067682 {A B : Type'} (a : B) (INR' : type1479 A B) (h1 : INR' = (term0 A B)) : (@inr A B a) = (term2 A B INR' a).
Proof. exact (EQ_MP (@lem1067681 A B INR' a) (@lem1067678 A B a INR' h1)). Qed.
