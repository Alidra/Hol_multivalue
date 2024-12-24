Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1066944_term_abbrevs.
Require Import thm1066938_spec.
Lemma lem1066941 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term0 A B INL' INR')) : term1 A B sum' INL'.
Proof. exact (proj1 (@lem1066938 A B sum' INL' INR' h1)). Qed.
Lemma lem1066942 {A B : Type'} (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term0 A B INL' INR')) : term2 A B sum' INL' a.
Proof. exact (@lem1066941 A B sum' INL' INR' h1 a). Qed.
Lemma lem1066943 {A B : Type'} (sum' : type1333 A B) (INL' : type1431 A B) (a : A) : (term2 A B sum' INL' a) = (term3 A B sum' INL' a).
Proof. exact (eq_refl (term2 A B sum' INL' a)). Qed.
Lemma lem1066944 {A B : Type'} (a : A) (sum' : type1333 A B) (INL' : type1431 A B) (INR' : type1479 A B) (h1 : sum' = (term0 A B INL' INR')) : term3 A B sum' INL' a.
Proof. exact (EQ_MP (@lem1066943 A B sum' INL' a) (@lem1066942 A B a sum' INL' INR' h1)). Qed.
