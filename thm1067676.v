Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1067676_term_abbrevs.
Require Import thm1067332_spec.
Lemma lem1067671 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1067672 {A B : Type'} (a : A) (INL' : type1431 A B) (h1 : INL' = (term0 A B)) : (@inl A B a) = (term1 A B INL' a).
Proof. exact (MK_COMB (@lem1067332 A B INL' h1) (@lem1067671 A a)). Qed.
Lemma lem1067673 {A B : Type'} (INL' : type1431 A B) (a : A) : (term1 A B INL' a) = (term2 A B INL' a).
Proof. exact (eq_refl (term1 A B INL' a)). Qed.
Lemma lem1067674 {A B : Type'} (a : A) : (term3 A B a) = (term3 A B a).
Proof. exact (eq_refl (term3 A B a)). Qed.
Lemma lem1067675 {A B : Type'} (INL' : type1431 A B) (a : A) : ((@inl A B a) = (term1 A B INL' a)) = ((@inl A B a) = (term2 A B INL' a)).
Proof. exact (MK_COMB (@lem1067674 A B a) (@lem1067673 A B INL' a)). Qed.
Lemma lem1067676 {A B : Type'} (a : A) (INL' : type1431 A B) (h1 : INL' = (term0 A B)) : (@inl A B a) = (term2 A B INL' a).
Proof. exact (EQ_MP (@lem1067675 A B INL' a) (@lem1067672 A B a INL' h1)). Qed.
