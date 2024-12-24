Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_term_abbrevs.
Lemma lem3181090 {A : Type'} : (@IN A) = (term0 A).
Proof. exact (@IN_def A). Qed.
Lemma lem3181091 {A : Type'} (_32683 : A) : _32683 = _32683.
Proof. exact (eq_refl _32683). Qed.
Lemma lem3181092 {A : Type'} (_32683 : A) : (@IN A _32683) = (term1 A _32683).
Proof. exact (MK_COMB (@lem3181090 A) (@lem3181091 A _32683)). Qed.
Lemma lem3181093 {A : Type'} (_32683 : A) : (term1 A _32683) = (term2 A _32683).
Proof. exact (eq_refl (term1 A _32683)). Qed.
Lemma lem3181094 {A : Type'} (_32683 : A) : (@IN A _32683) = (term2 A _32683).
Proof. exact (TRANS (@lem3181092 A _32683) (@lem3181093 A _32683)). Qed.
Lemma lem3181095 {A : Type'} (_32684 : A -> Prop) : _32684 = _32684.
Proof. exact (eq_refl _32684). Qed.
Lemma lem3181096 {A : Type'} (_32683 : A) (_32684 : A -> Prop) : (@IN A _32683 _32684) = (term3 A _32683 _32684).
Proof. exact (MK_COMB (@lem3181094 A _32683) (@lem3181095 A _32684)). Qed.
Lemma lem3181097 {A : Type'} (_32684 : A -> Prop) (_32683 : A) : (term3 A _32683 _32684) = (_32684 _32683).
Proof. exact (eq_refl (term3 A _32683 _32684)). Qed.
Lemma lem3181098 {A : Type'} (_32684 : A -> Prop) (_32683 : A) : (@IN A _32683 _32684) = (_32684 _32683).
Proof. exact (TRANS (@lem3181096 A _32683 _32684) (@lem3181097 A _32684 _32683)). Qed.
Lemma lem3181099 {A : Type'} (_32683 : A) : term4 A _32683.
Proof. exact (fun _32684 : A -> Prop => @lem3181098 A _32684 _32683). Qed.
Lemma lem3181100 {A : Type'} : term5 A.
Proof. exact (fun _32683 : A => @lem3181099 A _32683). Qed.
Lemma lem3181101 {A : Type'} (_32683 : A) : term6 A _32683.
Proof. exact (@lem3181100 A _32683). Qed.
Lemma lem3181102 {A : Type'} (_32683 : A) : (term6 A _32683) = (term4 A _32683).
Proof. exact (eq_refl (term6 A _32683)). Qed.
Lemma lem3181103 {A : Type'} (_32683 : A) : term4 A _32683.
Proof. exact (EQ_MP (@lem3181102 A _32683) (@lem3181101 A _32683)). Qed.
Lemma lem3181104 {A : Type'} (_32683 : A) (_32684 : A -> Prop) : term7 A _32683 _32684.
Proof. exact (@lem3181103 A _32683 _32684). Qed.
Lemma lem3181105 {A : Type'} (_32684 : A -> Prop) (_32683 : A) : (term7 A _32683 _32684) = ((@IN A _32683 _32684) = (_32684 _32683)).
Proof. exact (eq_refl (term7 A _32683 _32684)). Qed.
Lemma lem3181106 {A : Type'} (_32684 : A -> Prop) (_32683 : A) : (@IN A _32683 _32684) = (_32684 _32683).
Proof. exact (EQ_MP (@lem3181105 A _32684 _32683) (@lem3181104 A _32683 _32684)). Qed.
Lemma lem3181149 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3181106 A P x). Qed.
Lemma lem3181150 {A : Type'} (P : A -> Prop) : term8 A P.
Proof. exact (fun x : A => @lem3181149 A P x). Qed.
Lemma lem3181151 {A : Type'} : term9 A.
Proof. exact (fun P : A -> Prop => @lem3181150 A P). Qed.
