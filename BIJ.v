Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BIJ_term_abbrevs.
Lemma lem3202595 {A B : Type'} : (@BIJ A B) = (term0 A B).
Proof. exact (@BIJ_def A B). Qed.
Lemma lem3202596 {A B : Type'} (_32913 : A -> B) : _32913 = _32913.
Proof. exact (eq_refl _32913). Qed.
Lemma lem3202597 {A B : Type'} (_32913 : A -> B) : (@BIJ A B _32913) = (term1 A B _32913).
Proof. exact (MK_COMB (@lem3202595 A B) (@lem3202596 A B _32913)). Qed.
Lemma lem3202598 {A B : Type'} (_32913 : A -> B) : (term1 A B _32913) = (term2 A B _32913).
Proof. exact (eq_refl (term1 A B _32913)). Qed.
Lemma lem3202599 {A B : Type'} (_32913 : A -> B) : (@BIJ A B _32913) = (term2 A B _32913).
Proof. exact (TRANS (@lem3202597 A B _32913) (@lem3202598 A B _32913)). Qed.
Lemma lem3202600 {A : Type'} (_32914 : A -> Prop) : _32914 = _32914.
Proof. exact (eq_refl _32914). Qed.
Lemma lem3202601 {A B : Type'} (_32913 : A -> B) (_32914 : A -> Prop) : (@BIJ A B _32913 _32914) = (term3 A B _32913 _32914).
Proof. exact (MK_COMB (@lem3202599 A B _32913) (@lem3202600 A _32914)). Qed.
Lemma lem3202602 {A B : Type'} (_32913 : A -> B) (_32914 : A -> Prop) : (term3 A B _32913 _32914) = (term4 A B _32913 _32914).
Proof. exact (eq_refl (term3 A B _32913 _32914)). Qed.
Lemma lem3202603 {A B : Type'} (_32913 : A -> B) (_32914 : A -> Prop) : (@BIJ A B _32913 _32914) = (term4 A B _32913 _32914).
Proof. exact (TRANS (@lem3202601 A B _32913 _32914) (@lem3202602 A B _32913 _32914)). Qed.
Lemma lem3202604 {B : Type'} (_32915 : B -> Prop) : _32915 = _32915.
Proof. exact (eq_refl _32915). Qed.
Lemma lem3202605 {A B : Type'} (_32913 : A -> B) (_32914 : A -> Prop) (_32915 : B -> Prop) : (@BIJ A B _32913 _32914 _32915) = (term5 A B _32913 _32914 _32915).
Proof. exact (MK_COMB (@lem3202603 A B _32913 _32914) (@lem3202604 B _32915)). Qed.
Lemma lem3202606 {A B : Type'} (_32913 : A -> B) (_32914 : A -> Prop) (_32915 : B -> Prop) : (term5 A B _32913 _32914 _32915) = (term6 A B _32913 _32914 _32915).
Proof. exact (eq_refl (term5 A B _32913 _32914 _32915)). Qed.
Lemma lem3202607 {A B : Type'} (_32913 : A -> B) (_32914 : A -> Prop) (_32915 : B -> Prop) : (@BIJ A B _32913 _32914 _32915) = (term6 A B _32913 _32914 _32915).
Proof. exact (TRANS (@lem3202605 A B _32913 _32914 _32915) (@lem3202606 A B _32913 _32914 _32915)). Qed.
Lemma lem3202608 {A B : Type'} (_32913 : A -> B) (_32914 : A -> Prop) : term7 A B _32913 _32914.
Proof. exact (fun _32915 : B -> Prop => @lem3202607 A B _32913 _32914 _32915). Qed.
Lemma lem3202609 {A B : Type'} (_32913 : A -> B) : term8 A B _32913.
Proof. exact (fun _32914 : A -> Prop => @lem3202608 A B _32913 _32914). Qed.
Lemma lem3202610 {A B : Type'} : term9 A B.
Proof. exact (fun _32913 : A -> B => @lem3202609 A B _32913). Qed.
Lemma lem3202611 {A B : Type'} (_32913 : A -> B) : term10 A B _32913.
Proof. exact (@lem3202610 A B _32913). Qed.
Lemma lem3202612 {A B : Type'} (_32913 : A -> B) : (term10 A B _32913) = (term8 A B _32913).
Proof. exact (eq_refl (term10 A B _32913)). Qed.
Lemma lem3202613 {A B : Type'} (_32913 : A -> B) : term8 A B _32913.
Proof. exact (EQ_MP (@lem3202612 A B _32913) (@lem3202611 A B _32913)). Qed.
Lemma lem3202614 {A B : Type'} (_32913 : A -> B) (_32914 : A -> Prop) : term11 A B _32913 _32914.
Proof. exact (@lem3202613 A B _32913 _32914). Qed.
Lemma lem3202615 {A B : Type'} (_32913 : A -> B) (_32914 : A -> Prop) : (term11 A B _32913 _32914) = (term7 A B _32913 _32914).
Proof. exact (eq_refl (term11 A B _32913 _32914)). Qed.
Lemma lem3202616 {A B : Type'} (_32913 : A -> B) (_32914 : A -> Prop) : term7 A B _32913 _32914.
Proof. exact (EQ_MP (@lem3202615 A B _32913 _32914) (@lem3202614 A B _32913 _32914)). Qed.
Lemma lem3202617 {A B : Type'} (_32913 : A -> B) (_32914 : A -> Prop) (_32915 : B -> Prop) : term12 A B _32913 _32914 _32915.
Proof. exact (@lem3202616 A B _32913 _32914 _32915). Qed.
Lemma lem3202618 {A B : Type'} (_32913 : A -> B) (_32914 : A -> Prop) (_32915 : B -> Prop) : (term12 A B _32913 _32914 _32915) = ((@BIJ A B _32913 _32914 _32915) = (term6 A B _32913 _32914 _32915)).
Proof. exact (eq_refl (term12 A B _32913 _32914 _32915)). Qed.
Lemma lem3202619 {A B : Type'} (_32913 : A -> B) (_32914 : A -> Prop) (_32915 : B -> Prop) : (@BIJ A B _32913 _32914 _32915) = (term6 A B _32913 _32914 _32915).
Proof. exact (EQ_MP (@lem3202618 A B _32913 _32914 _32915) (@lem3202617 A B _32913 _32914 _32915)). Qed.
Lemma lem3202675 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (@BIJ A B f s t) = (term6 A B f s t).
Proof. exact (@lem3202619 A B f s t). Qed.
Lemma lem3202676 {A B : Type'} (f : A -> B) (s : A -> Prop) : term7 A B f s.
Proof. exact (fun t : B -> Prop => @lem3202675 A B f s t). Qed.
Lemma lem3202677 {A B : Type'} (f : A -> B) : term8 A B f.
Proof. exact (fun s : A -> Prop => @lem3202676 A B f s). Qed.
Lemma lem3202678 {A B : Type'} : term9 A B.
Proof. exact (fun f : A -> B => @lem3202677 A B f). Qed.
