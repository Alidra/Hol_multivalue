Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DELETE_term_abbrevs.
Lemma lem3193118 {A : Type'} : (@DELETE A) = (term0 A).
Proof. exact (@DELETE_def A). Qed.
Lemma lem3193119 {A : Type'} (_32797 : A -> Prop) : _32797 = _32797.
Proof. exact (eq_refl _32797). Qed.
Lemma lem3193120 {A : Type'} (_32797 : A -> Prop) : (@DELETE A _32797) = (term1 A _32797).
Proof. exact (MK_COMB (@lem3193118 A) (@lem3193119 A _32797)). Qed.
Lemma lem3193121 {A : Type'} (_32797 : A -> Prop) : (term1 A _32797) = (term2 A _32797).
Proof. exact (eq_refl (term1 A _32797)). Qed.
Lemma lem3193122 {A : Type'} (_32797 : A -> Prop) : (@DELETE A _32797) = (term2 A _32797).
Proof. exact (TRANS (@lem3193120 A _32797) (@lem3193121 A _32797)). Qed.
Lemma lem3193123 {A : Type'} (_32798 : A) : _32798 = _32798.
Proof. exact (eq_refl _32798). Qed.
Lemma lem3193124 {A : Type'} (_32797 : A -> Prop) (_32798 : A) : (@DELETE A _32797 _32798) = (term3 A _32797 _32798).
Proof. exact (MK_COMB (@lem3193122 A _32797) (@lem3193123 A _32798)). Qed.
Lemma lem3193125 {A : Type'} (_32797 : A -> Prop) (_32798 : A) : (term3 A _32797 _32798) = (term4 A _32797 _32798).
Proof. exact (eq_refl (term3 A _32797 _32798)). Qed.
Lemma lem3193126 {A : Type'} (_32797 : A -> Prop) (_32798 : A) : (@DELETE A _32797 _32798) = (term4 A _32797 _32798).
Proof. exact (TRANS (@lem3193124 A _32797 _32798) (@lem3193125 A _32797 _32798)). Qed.
Lemma lem3193127 {A : Type'} (_32797 : A -> Prop) : term5 A _32797.
Proof. exact (fun _32798 : A => @lem3193126 A _32797 _32798). Qed.
Lemma lem3193128 {A : Type'} : term6 A.
Proof. exact (fun _32797 : A -> Prop => @lem3193127 A _32797). Qed.
Lemma lem3193129 {A : Type'} (_32797 : A -> Prop) : term7 A _32797.
Proof. exact (@lem3193128 A _32797). Qed.
Lemma lem3193130 {A : Type'} (_32797 : A -> Prop) : (term7 A _32797) = (term5 A _32797).
Proof. exact (eq_refl (term7 A _32797)). Qed.
Lemma lem3193131 {A : Type'} (_32797 : A -> Prop) : term5 A _32797.
Proof. exact (EQ_MP (@lem3193130 A _32797) (@lem3193129 A _32797)). Qed.
Lemma lem3193132 {A : Type'} (_32797 : A -> Prop) (_32798 : A) : term8 A _32797 _32798.
Proof. exact (@lem3193131 A _32797 _32798). Qed.
Lemma lem3193133 {A : Type'} (_32797 : A -> Prop) (_32798 : A) : (term8 A _32797 _32798) = ((@DELETE A _32797 _32798) = (term4 A _32797 _32798)).
Proof. exact (eq_refl (term8 A _32797 _32798)). Qed.
Lemma lem3193134 {A : Type'} (_32797 : A -> Prop) (_32798 : A) : (@DELETE A _32797 _32798) = (term4 A _32797 _32798).
Proof. exact (EQ_MP (@lem3193133 A _32797 _32798) (@lem3193132 A _32797 _32798)). Qed.
Lemma lem3193177 {A : Type'} (s : A -> Prop) (x : A) : (@DELETE A s x) = (term4 A s x).
Proof. exact (@lem3193134 A s x). Qed.
Lemma lem3193178 {A : Type'} (s : A -> Prop) : term5 A s.
Proof. exact (fun x : A => @lem3193177 A s x). Qed.
Lemma lem3193179 {A : Type'} : term6 A.
Proof. exact (fun s : A -> Prop => @lem3193178 A s). Qed.
