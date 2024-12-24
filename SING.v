Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SING_term_abbrevs.
Lemma lem3197042 {A : Type'} : (@SING A) = (term0 A).
Proof. exact (@SING_def A). Qed.
Lemma lem3197043 {A : Type'} (_32845 : A -> Prop) : _32845 = _32845.
Proof. exact (eq_refl _32845). Qed.
Lemma lem3197044 {A : Type'} (_32845 : A -> Prop) : (@SING A _32845) = (term1 A _32845).
Proof. exact (MK_COMB (@lem3197042 A) (@lem3197043 A _32845)). Qed.
Lemma lem3197045 {A : Type'} (_32845 : A -> Prop) : (term1 A _32845) = (term2 A _32845).
Proof. exact (eq_refl (term1 A _32845)). Qed.
Lemma lem3197046 {A : Type'} (_32845 : A -> Prop) : (@SING A _32845) = (term2 A _32845).
Proof. exact (TRANS (@lem3197044 A _32845) (@lem3197045 A _32845)). Qed.
Lemma lem3197047 {A : Type'} : term3 A.
Proof. exact (fun _32845 : A -> Prop => @lem3197046 A _32845). Qed.
Lemma lem3197048 {A : Type'} (_32845 : A -> Prop) : term4 A _32845.
Proof. exact (@lem3197047 A _32845). Qed.
Lemma lem3197049 {A : Type'} (_32845 : A -> Prop) : (term4 A _32845) = ((@SING A _32845) = (term2 A _32845)).
Proof. exact (eq_refl (term4 A _32845)). Qed.
Lemma lem3197050 {A : Type'} (_32845 : A -> Prop) : (@SING A _32845) = (term2 A _32845).
Proof. exact (EQ_MP (@lem3197049 A _32845) (@lem3197048 A _32845)). Qed.
Lemma lem3197080 {A : Type'} (s : A -> Prop) : (@SING A s) = (term2 A s).
Proof. exact (@lem3197050 A s). Qed.
Lemma lem3197081 {A : Type'} : term3 A.
Proof. exact (fun s : A -> Prop => @lem3197080 A s). Qed.
