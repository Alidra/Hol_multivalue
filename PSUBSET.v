Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PSUBSET_term_abbrevs.
Lemma lem3195064 {A : Type'} : (@PSUBSET A) = (term0 A).
Proof. exact (@PSUBSET_def A). Qed.
Lemma lem3195065 {A : Type'} (_32821 : A -> Prop) : _32821 = _32821.
Proof. exact (eq_refl _32821). Qed.
Lemma lem3195066 {A : Type'} (_32821 : A -> Prop) : (@PSUBSET A _32821) = (term1 A _32821).
Proof. exact (MK_COMB (@lem3195064 A) (@lem3195065 A _32821)). Qed.
Lemma lem3195067 {A : Type'} (_32821 : A -> Prop) : (term1 A _32821) = (term2 A _32821).
Proof. exact (eq_refl (term1 A _32821)). Qed.
Lemma lem3195068 {A : Type'} (_32821 : A -> Prop) : (@PSUBSET A _32821) = (term2 A _32821).
Proof. exact (TRANS (@lem3195066 A _32821) (@lem3195067 A _32821)). Qed.
Lemma lem3195069 {A : Type'} (_32822 : A -> Prop) : _32822 = _32822.
Proof. exact (eq_refl _32822). Qed.
Lemma lem3195070 {A : Type'} (_32821 : A -> Prop) (_32822 : A -> Prop) : (@PSUBSET A _32821 _32822) = (term3 A _32821 _32822).
Proof. exact (MK_COMB (@lem3195068 A _32821) (@lem3195069 A _32822)). Qed.
Lemma lem3195071 {A : Type'} (_32821 : A -> Prop) (_32822 : A -> Prop) : (term3 A _32821 _32822) = (term4 A _32821 _32822).
Proof. exact (eq_refl (term3 A _32821 _32822)). Qed.
Lemma lem3195072 {A : Type'} (_32821 : A -> Prop) (_32822 : A -> Prop) : (@PSUBSET A _32821 _32822) = (term4 A _32821 _32822).
Proof. exact (TRANS (@lem3195070 A _32821 _32822) (@lem3195071 A _32821 _32822)). Qed.
Lemma lem3195073 {A : Type'} (_32821 : A -> Prop) : term5 A _32821.
Proof. exact (fun _32822 : A -> Prop => @lem3195072 A _32821 _32822). Qed.
Lemma lem3195074 {A : Type'} : term6 A.
Proof. exact (fun _32821 : A -> Prop => @lem3195073 A _32821). Qed.
Lemma lem3195075 {A : Type'} (_32821 : A -> Prop) : term7 A _32821.
Proof. exact (@lem3195074 A _32821). Qed.
Lemma lem3195076 {A : Type'} (_32821 : A -> Prop) : (term7 A _32821) = (term5 A _32821).
Proof. exact (eq_refl (term7 A _32821)). Qed.
Lemma lem3195077 {A : Type'} (_32821 : A -> Prop) : term5 A _32821.
Proof. exact (EQ_MP (@lem3195076 A _32821) (@lem3195075 A _32821)). Qed.
Lemma lem3195078 {A : Type'} (_32821 : A -> Prop) (_32822 : A -> Prop) : term8 A _32821 _32822.
Proof. exact (@lem3195077 A _32821 _32822). Qed.
Lemma lem3195079 {A : Type'} (_32821 : A -> Prop) (_32822 : A -> Prop) : (term8 A _32821 _32822) = ((@PSUBSET A _32821 _32822) = (term4 A _32821 _32822)).
Proof. exact (eq_refl (term8 A _32821 _32822)). Qed.
Lemma lem3195080 {A : Type'} (_32821 : A -> Prop) (_32822 : A -> Prop) : (@PSUBSET A _32821 _32822) = (term4 A _32821 _32822).
Proof. exact (EQ_MP (@lem3195079 A _32821 _32822) (@lem3195078 A _32821 _32822)). Qed.
Lemma lem3195123 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term4 A s t).
Proof. exact (@lem3195080 A s t). Qed.
Lemma lem3195124 {A : Type'} (s : A -> Prop) : term5 A s.
Proof. exact (fun t : A -> Prop => @lem3195123 A s t). Qed.
Lemma lem3195125 {A : Type'} : term6 A.
Proof. exact (fun s : A -> Prop => @lem3195124 A s). Qed.
