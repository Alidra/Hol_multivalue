Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERS_term_abbrevs.
Lemma lem3191084 {A : Type'} : (@INTERS A) = (term0 A).
Proof. exact (@INTERS_def A). Qed.
Lemma lem3191085 {A : Type'} (_32780 : type686 A) : _32780 = _32780.
Proof. exact (eq_refl _32780). Qed.
Lemma lem3191086 {A : Type'} (_32780 : type686 A) : (@INTERS A _32780) = (term1 A _32780).
Proof. exact (MK_COMB (@lem3191084 A) (@lem3191085 A _32780)). Qed.
Lemma lem3191087 {A : Type'} (_32780 : type686 A) : (term1 A _32780) = (term2 A _32780).
Proof. exact (eq_refl (term1 A _32780)). Qed.
Lemma lem3191088 {A : Type'} (_32780 : type686 A) : (@INTERS A _32780) = (term2 A _32780).
Proof. exact (TRANS (@lem3191086 A _32780) (@lem3191087 A _32780)). Qed.
Lemma lem3191089 {A : Type'} : term3 A.
Proof. exact (fun _32780 : type686 A => @lem3191088 A _32780). Qed.
Lemma lem3191090 {A : Type'} (_32780 : type686 A) : term4 A _32780.
Proof. exact (@lem3191089 A _32780). Qed.
Lemma lem3191091 {A : Type'} (_32780 : type686 A) : (term4 A _32780) = ((@INTERS A _32780) = (term2 A _32780)).
Proof. exact (eq_refl (term4 A _32780)). Qed.
Lemma lem3191092 {A : Type'} (_32780 : type686 A) : (@INTERS A _32780) = (term2 A _32780).
Proof. exact (EQ_MP (@lem3191091 A _32780) (@lem3191090 A _32780)). Qed.
Lemma lem3191122 {A : Type'} (s : type686 A) : (@INTERS A s) = (term2 A s).
Proof. exact (@lem3191092 A s). Qed.
Lemma lem3191123 {A : Type'} : term3 A.
Proof. exact (fun s : type686 A => @lem3191122 A s). Qed.
