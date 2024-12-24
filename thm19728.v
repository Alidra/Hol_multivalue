Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm19728_term_abbrevs.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem19703 {A : Type'} : (@ex A) = (term0 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem19704 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem19705 {A : Type'} (P : A -> Prop) : (ex P) = (term1 A P).
Proof. exact (MK_COMB (@lem19703 A) (@lem19704 A P)). Qed.
Lemma lem19707 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem19708 {A : Type'} (f : type686 A) (y : A -> Prop) : (term3 A f y) = (f y).
Proof. exact (@lem19707 (A -> Prop) Prop f y). Qed.
Lemma lem19709 {A : Type'} (P : A -> Prop) : (term4 A P) = (term1 A P).
Proof. exact (@lem19708 A (term0 A) P). Qed.
Lemma lem19710 {A : Type'} (P : A -> Prop) : (term1 A P) = (term5 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem19711 {A : Type'} : (term6 A) = (term0 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem19710 A P)). Qed.
Lemma lem19712 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem19713 {A : Type'} (P : A -> Prop) : (term4 A P) = (term1 A P).
Proof. exact (MK_COMB (@lem19711 A) (@lem19712 A P)). Qed.
Lemma lem19714 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem19715 {A : Type'} (P : A -> Prop) : (term7 A P) = (term8 A P).
Proof. exact (MK_COMB (@lem19714) (@lem19713 A P)). Qed.
Lemma lem19716 {A : Type'} (P : A -> Prop) : (term1 A P) = (term5 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem19717 {A : Type'} (P : A -> Prop) : ((term4 A P) = (term1 A P)) = ((term1 A P) = (term5 A P)).
Proof. exact (MK_COMB (@lem19715 A P) (@lem19716 A P)). Qed.
Lemma lem19718 {A : Type'} (P : A -> Prop) : (term1 A P) = (term5 A P).
Proof. exact (EQ_MP (@lem19717 A P) (@lem19709 A P)). Qed.
Lemma lem19719 {A : Type'} (P : A -> Prop) : (ex P) = (term5 A P).
Proof. exact (TRANS (@lem19705 A P) (@lem19718 A P)). Qed.
Lemma lem19720 {A : Type'} (P : A -> Prop) : (term9 A P) = (term9 A P).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem19721 {A : Type'} (P : A -> Prop) : ((term5 A P) = (ex P)) = ((term5 A P) = (term5 A P)).
Proof. exact (MK_COMB (@lem19720 A P) (@lem19719 A P)). Qed.
Lemma lem19723 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem19724 (x : Prop) : (x = x) = True.
Proof. exact (@lem19723 Prop x). Qed.
Lemma lem19725 {A : Type'} (P : A -> Prop) : ((term5 A P) = (term5 A P)) = True.
Proof. exact (@lem19724 (term5 A P)). Qed.
Lemma lem19726 {A : Type'} (P : A -> Prop) : ((term5 A P) = (ex P)) = True.
Proof. exact (TRANS (@lem19721 A P) (@lem19725 A P)). Qed.
Lemma lem19727 {A : Type'} (P : A -> Prop) : True = ((term5 A P) = (ex P)).
Proof. exact (SYM (@lem19726 A P)). Qed.
Lemma lem19728 {A : Type'} (P : A -> Prop) : (term5 A P) = (ex P).
Proof. exact (EQ_MP (@lem19727 A P) (@lem0)). Qed.
