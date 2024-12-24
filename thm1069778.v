Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1069778_term_abbrevs.
Require Import thm1069016_spec.
Lemma lem1069767 {A : Type'} : (term0 A) = (term0 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem1069768 {A : Type'} (SOME' : type1432 A) (h1 : SOME' = (term1 A)) : (term2 A SOME') = (term3 A).
Proof. exact (MK_COMB (@lem1069767 A) (@lem1069016 A SOME' h1)). Qed.
Lemma lem1069769 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem1069770 {A : Type'} (SOME' : type1432 A) : (term5 A SOME') = (term5 A SOME').
Proof. exact (eq_refl (term5 A SOME')). Qed.
Lemma lem1069771 {A : Type'} (SOME' : type1432 A) : ((term2 A SOME') = (term3 A)) = ((term2 A SOME') = (term4 A)).
Proof. exact (MK_COMB (@lem1069770 A SOME') (@lem1069769 A)). Qed.
Lemma lem1069772 {A : Type'} (SOME' : type1432 A) : (term2 A SOME') = (term6 A SOME').
Proof. exact (eq_refl (term2 A SOME')). Qed.
Lemma lem1069773 {A : Type'} : (@eq (A -> option A)) = (@eq (A -> option A)).
Proof. exact (eq_refl (@eq (A -> option A))). Qed.
Lemma lem1069774 {A : Type'} (SOME' : type1432 A) : (term5 A SOME') = (term7 A SOME').
Proof. exact (MK_COMB (@lem1069773 A) (@lem1069772 A SOME')). Qed.
Lemma lem1069775 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (eq_refl (term4 A)). Qed.
Lemma lem1069776 {A : Type'} (SOME' : type1432 A) : ((term2 A SOME') = (term4 A)) = ((term6 A SOME') = (term4 A)).
Proof. exact (MK_COMB (@lem1069774 A SOME') (@lem1069775 A)). Qed.
Lemma lem1069777 {A : Type'} (SOME' : type1432 A) : ((term2 A SOME') = (term3 A)) = ((term6 A SOME') = (term4 A)).
Proof. exact (TRANS (@lem1069771 A SOME') (@lem1069776 A SOME')). Qed.
Lemma lem1069778 {A : Type'} (SOME' : type1432 A) (h1 : SOME' = (term1 A)) : (term6 A SOME') = (term4 A).
Proof. exact (EQ_MP (@lem1069777 A SOME') (@lem1069768 A SOME' h1)). Qed.
