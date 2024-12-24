Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIFF_term_abbrevs.
Lemma lem3192015 {A : Type'} : (@DIFF A) = (term0 A).
Proof. exact (@DIFF_def A). Qed.
Lemma lem3192016 {A : Type'} (_32785 : A -> Prop) : _32785 = _32785.
Proof. exact (eq_refl _32785). Qed.
Lemma lem3192017 {A : Type'} (_32785 : A -> Prop) : (@DIFF A _32785) = (term1 A _32785).
Proof. exact (MK_COMB (@lem3192015 A) (@lem3192016 A _32785)). Qed.
Lemma lem3192018 {A : Type'} (_32785 : A -> Prop) : (term1 A _32785) = (term2 A _32785).
Proof. exact (eq_refl (term1 A _32785)). Qed.
Lemma lem3192019 {A : Type'} (_32785 : A -> Prop) : (@DIFF A _32785) = (term2 A _32785).
Proof. exact (TRANS (@lem3192017 A _32785) (@lem3192018 A _32785)). Qed.
Lemma lem3192020 {A : Type'} (_32786 : A -> Prop) : _32786 = _32786.
Proof. exact (eq_refl _32786). Qed.
Lemma lem3192021 {A : Type'} (_32785 : A -> Prop) (_32786 : A -> Prop) : (@DIFF A _32785 _32786) = (term3 A _32785 _32786).
Proof. exact (MK_COMB (@lem3192019 A _32785) (@lem3192020 A _32786)). Qed.
Lemma lem3192022 {A : Type'} (_32785 : A -> Prop) (_32786 : A -> Prop) : (term3 A _32785 _32786) = (term4 A _32785 _32786).
Proof. exact (eq_refl (term3 A _32785 _32786)). Qed.
Lemma lem3192023 {A : Type'} (_32785 : A -> Prop) (_32786 : A -> Prop) : (@DIFF A _32785 _32786) = (term4 A _32785 _32786).
Proof. exact (TRANS (@lem3192021 A _32785 _32786) (@lem3192022 A _32785 _32786)). Qed.
Lemma lem3192024 {A : Type'} (_32785 : A -> Prop) : term5 A _32785.
Proof. exact (fun _32786 : A -> Prop => @lem3192023 A _32785 _32786). Qed.
Lemma lem3192025 {A : Type'} : term6 A.
Proof. exact (fun _32785 : A -> Prop => @lem3192024 A _32785). Qed.
Lemma lem3192026 {A : Type'} (_32785 : A -> Prop) : term7 A _32785.
Proof. exact (@lem3192025 A _32785). Qed.
Lemma lem3192027 {A : Type'} (_32785 : A -> Prop) : (term7 A _32785) = (term5 A _32785).
Proof. exact (eq_refl (term7 A _32785)). Qed.
Lemma lem3192028 {A : Type'} (_32785 : A -> Prop) : term5 A _32785.
Proof. exact (EQ_MP (@lem3192027 A _32785) (@lem3192026 A _32785)). Qed.
Lemma lem3192029 {A : Type'} (_32785 : A -> Prop) (_32786 : A -> Prop) : term8 A _32785 _32786.
Proof. exact (@lem3192028 A _32785 _32786). Qed.
Lemma lem3192030 {A : Type'} (_32785 : A -> Prop) (_32786 : A -> Prop) : (term8 A _32785 _32786) = ((@DIFF A _32785 _32786) = (term4 A _32785 _32786)).
Proof. exact (eq_refl (term8 A _32785 _32786)). Qed.
Lemma lem3192031 {A : Type'} (_32785 : A -> Prop) (_32786 : A -> Prop) : (@DIFF A _32785 _32786) = (term4 A _32785 _32786).
Proof. exact (EQ_MP (@lem3192030 A _32785 _32786) (@lem3192029 A _32785 _32786)). Qed.
Lemma lem3192074 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DIFF A s t) = (term4 A s t).
Proof. exact (@lem3192031 A s t). Qed.
Lemma lem3192075 {A : Type'} (s : A -> Prop) : term5 A s.
Proof. exact (fun t : A -> Prop => @lem3192074 A s t). Qed.
Lemma lem3192076 {A : Type'} : term6 A.
Proof. exact (fun s : A -> Prop => @lem3192075 A s). Qed.
