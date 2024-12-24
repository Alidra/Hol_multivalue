Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import GSPEC_term_abbrevs.
Lemma lem3182083 {A : Type'} : (@GSPEC A) = (term0 A).
Proof. exact (@GSPEC_def A). Qed.
Lemma lem3182084 {A : Type'} (_32695 : A -> Prop) : _32695 = _32695.
Proof. exact (eq_refl _32695). Qed.
Lemma lem3182085 {A : Type'} (_32695 : A -> Prop) : (@GSPEC A _32695) = (term1 A _32695).
Proof. exact (MK_COMB (@lem3182083 A) (@lem3182084 A _32695)). Qed.
Lemma lem3182086 {A : Type'} (_32695 : A -> Prop) : (term1 A _32695) = _32695.
Proof. exact (eq_refl (term1 A _32695)). Qed.
Lemma lem3182087 {A : Type'} (_32695 : A -> Prop) : (@GSPEC A _32695) = _32695.
Proof. exact (TRANS (@lem3182085 A _32695) (@lem3182086 A _32695)). Qed.
Lemma lem3182088 {A : Type'} : term2 A.
Proof. exact (fun _32695 : A -> Prop => @lem3182087 A _32695). Qed.
Lemma lem3182089 {A : Type'} (_32695 : A -> Prop) : term3 A _32695.
Proof. exact (@lem3182088 A _32695). Qed.
Lemma lem3182090 {A : Type'} (_32695 : A -> Prop) : (term3 A _32695) = ((@GSPEC A _32695) = _32695).
Proof. exact (eq_refl (term3 A _32695)). Qed.
Lemma lem3182091 {A : Type'} (_32695 : A -> Prop) : (@GSPEC A _32695) = _32695.
Proof. exact (EQ_MP (@lem3182090 A _32695) (@lem3182089 A _32695)). Qed.
Lemma lem3182121 {A : Type'} (p : A -> Prop) : (@GSPEC A p) = p.
Proof. exact (@lem3182091 A p). Qed.
Lemma lem3182122 {A : Type'} : term2 A.
Proof. exact (fun p : A -> Prop => @lem3182121 A p). Qed.
