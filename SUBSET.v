Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_term_abbrevs.
Lemma lem3194087 {A : Type'} : (@SUBSET A) = (term0 A).
Proof. exact (@SUBSET_def A). Qed.
Lemma lem3194088 {A : Type'} (_32809 : A -> Prop) : _32809 = _32809.
Proof. exact (eq_refl _32809). Qed.
Lemma lem3194089 {A : Type'} (_32809 : A -> Prop) : (@SUBSET A _32809) = (term1 A _32809).
Proof. exact (MK_COMB (@lem3194087 A) (@lem3194088 A _32809)). Qed.
Lemma lem3194090 {A : Type'} (_32809 : A -> Prop) : (term1 A _32809) = (term2 A _32809).
Proof. exact (eq_refl (term1 A _32809)). Qed.
Lemma lem3194091 {A : Type'} (_32809 : A -> Prop) : (@SUBSET A _32809) = (term2 A _32809).
Proof. exact (TRANS (@lem3194089 A _32809) (@lem3194090 A _32809)). Qed.
Lemma lem3194092 {A : Type'} (_32810 : A -> Prop) : _32810 = _32810.
Proof. exact (eq_refl _32810). Qed.
Lemma lem3194093 {A : Type'} (_32809 : A -> Prop) (_32810 : A -> Prop) : (@SUBSET A _32809 _32810) = (term3 A _32809 _32810).
Proof. exact (MK_COMB (@lem3194091 A _32809) (@lem3194092 A _32810)). Qed.
Lemma lem3194094 {A : Type'} (_32809 : A -> Prop) (_32810 : A -> Prop) : (term3 A _32809 _32810) = (term4 A _32809 _32810).
Proof. exact (eq_refl (term3 A _32809 _32810)). Qed.
Lemma lem3194095 {A : Type'} (_32809 : A -> Prop) (_32810 : A -> Prop) : (@SUBSET A _32809 _32810) = (term4 A _32809 _32810).
Proof. exact (TRANS (@lem3194093 A _32809 _32810) (@lem3194094 A _32809 _32810)). Qed.
Lemma lem3194096 {A : Type'} (_32809 : A -> Prop) : term5 A _32809.
Proof. exact (fun _32810 : A -> Prop => @lem3194095 A _32809 _32810). Qed.
Lemma lem3194097 {A : Type'} : term6 A.
Proof. exact (fun _32809 : A -> Prop => @lem3194096 A _32809). Qed.
Lemma lem3194098 {A : Type'} (_32809 : A -> Prop) : term7 A _32809.
Proof. exact (@lem3194097 A _32809). Qed.
Lemma lem3194099 {A : Type'} (_32809 : A -> Prop) : (term7 A _32809) = (term5 A _32809).
Proof. exact (eq_refl (term7 A _32809)). Qed.
Lemma lem3194100 {A : Type'} (_32809 : A -> Prop) : term5 A _32809.
Proof. exact (EQ_MP (@lem3194099 A _32809) (@lem3194098 A _32809)). Qed.
Lemma lem3194101 {A : Type'} (_32809 : A -> Prop) (_32810 : A -> Prop) : term8 A _32809 _32810.
Proof. exact (@lem3194100 A _32809 _32810). Qed.
Lemma lem3194102 {A : Type'} (_32809 : A -> Prop) (_32810 : A -> Prop) : (term8 A _32809 _32810) = ((@SUBSET A _32809 _32810) = (term4 A _32809 _32810)).
Proof. exact (eq_refl (term8 A _32809 _32810)). Qed.
Lemma lem3194103 {A : Type'} (_32809 : A -> Prop) (_32810 : A -> Prop) : (@SUBSET A _32809 _32810) = (term4 A _32809 _32810).
Proof. exact (EQ_MP (@lem3194102 A _32809 _32810) (@lem3194101 A _32809 _32810)). Qed.
Lemma lem3194146 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term4 A s t).
Proof. exact (@lem3194103 A s t). Qed.
Lemma lem3194147 {A : Type'} (s : A -> Prop) : term5 A s.
Proof. exact (fun t : A -> Prop => @lem3194146 A s t). Qed.
Lemma lem3194148 {A : Type'} : term6 A.
Proof. exact (fun s : A -> Prop => @lem3194147 A s). Qed.
