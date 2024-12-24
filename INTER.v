Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_term_abbrevs.
Lemma lem3190136 {A : Type'} : (@INTER A) = (term0 A).
Proof. exact (@INTER_def A). Qed.
Lemma lem3190137 {A : Type'} (_32768 : A -> Prop) : _32768 = _32768.
Proof. exact (eq_refl _32768). Qed.
Lemma lem3190138 {A : Type'} (_32768 : A -> Prop) : (@INTER A _32768) = (term1 A _32768).
Proof. exact (MK_COMB (@lem3190136 A) (@lem3190137 A _32768)). Qed.
Lemma lem3190139 {A : Type'} (_32768 : A -> Prop) : (term1 A _32768) = (term2 A _32768).
Proof. exact (eq_refl (term1 A _32768)). Qed.
Lemma lem3190140 {A : Type'} (_32768 : A -> Prop) : (@INTER A _32768) = (term2 A _32768).
Proof. exact (TRANS (@lem3190138 A _32768) (@lem3190139 A _32768)). Qed.
Lemma lem3190141 {A : Type'} (_32769 : A -> Prop) : _32769 = _32769.
Proof. exact (eq_refl _32769). Qed.
Lemma lem3190142 {A : Type'} (_32768 : A -> Prop) (_32769 : A -> Prop) : (@INTER A _32768 _32769) = (term3 A _32768 _32769).
Proof. exact (MK_COMB (@lem3190140 A _32768) (@lem3190141 A _32769)). Qed.
Lemma lem3190143 {A : Type'} (_32768 : A -> Prop) (_32769 : A -> Prop) : (term3 A _32768 _32769) = (term4 A _32768 _32769).
Proof. exact (eq_refl (term3 A _32768 _32769)). Qed.
Lemma lem3190144 {A : Type'} (_32768 : A -> Prop) (_32769 : A -> Prop) : (@INTER A _32768 _32769) = (term4 A _32768 _32769).
Proof. exact (TRANS (@lem3190142 A _32768 _32769) (@lem3190143 A _32768 _32769)). Qed.
Lemma lem3190145 {A : Type'} (_32768 : A -> Prop) : term5 A _32768.
Proof. exact (fun _32769 : A -> Prop => @lem3190144 A _32768 _32769). Qed.
Lemma lem3190146 {A : Type'} : term6 A.
Proof. exact (fun _32768 : A -> Prop => @lem3190145 A _32768). Qed.
Lemma lem3190147 {A : Type'} (_32768 : A -> Prop) : term7 A _32768.
Proof. exact (@lem3190146 A _32768). Qed.
Lemma lem3190148 {A : Type'} (_32768 : A -> Prop) : (term7 A _32768) = (term5 A _32768).
Proof. exact (eq_refl (term7 A _32768)). Qed.
Lemma lem3190149 {A : Type'} (_32768 : A -> Prop) : term5 A _32768.
Proof. exact (EQ_MP (@lem3190148 A _32768) (@lem3190147 A _32768)). Qed.
Lemma lem3190150 {A : Type'} (_32768 : A -> Prop) (_32769 : A -> Prop) : term8 A _32768 _32769.
Proof. exact (@lem3190149 A _32768 _32769). Qed.
Lemma lem3190151 {A : Type'} (_32768 : A -> Prop) (_32769 : A -> Prop) : (term8 A _32768 _32769) = ((@INTER A _32768 _32769) = (term4 A _32768 _32769)).
Proof. exact (eq_refl (term8 A _32768 _32769)). Qed.
Lemma lem3190152 {A : Type'} (_32768 : A -> Prop) (_32769 : A -> Prop) : (@INTER A _32768 _32769) = (term4 A _32768 _32769).
Proof. exact (EQ_MP (@lem3190151 A _32768 _32769) (@lem3190150 A _32768 _32769)). Qed.
Lemma lem3190195 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@INTER A s t) = (term4 A s t).
Proof. exact (@lem3190152 A s t). Qed.
Lemma lem3190196 {A : Type'} (s : A -> Prop) : term5 A s.
Proof. exact (fun t : A -> Prop => @lem3190195 A s t). Qed.
Lemma lem3190197 {A : Type'} : term6 A.
Proof. exact (fun s : A -> Prop => @lem3190196 A s). Qed.
