Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import support_term_abbrevs.
Lemma lem5716678 {A B : Type'} : (@support A B) = (term0 A B).
Proof. exact (@support_def A B). Qed.
Lemma lem5716679 {B : Type'} (_71694 : type1400 B) : _71694 = _71694.
Proof. exact (eq_refl _71694). Qed.
Lemma lem5716680 {A B : Type'} (_71694 : type1400 B) : (@support A B _71694) = (term1 A B _71694).
Proof. exact (MK_COMB (@lem5716678 A B) (@lem5716679 B _71694)). Qed.
Lemma lem5716681 {A B : Type'} (_71694 : type1400 B) : (term1 A B _71694) = (term2 A B _71694).
Proof. exact (eq_refl (term1 A B _71694)). Qed.
Lemma lem5716682 {A B : Type'} (_71694 : type1400 B) : (@support A B _71694) = (term2 A B _71694).
Proof. exact (TRANS (@lem5716680 A B _71694) (@lem5716681 A B _71694)). Qed.
Lemma lem5716683 {A B : Type'} (_71695 : A -> B) : _71695 = _71695.
Proof. exact (eq_refl _71695). Qed.
Lemma lem5716684 {A B : Type'} (_71694 : type1400 B) (_71695 : A -> B) : (@support A B _71694 _71695) = (term3 A B _71694 _71695).
Proof. exact (MK_COMB (@lem5716682 A B _71694) (@lem5716683 A B _71695)). Qed.
Lemma lem5716685 {A B : Type'} (_71695 : A -> B) (_71694 : type1400 B) : (term3 A B _71694 _71695) = (term4 A B _71695 _71694).
Proof. exact (eq_refl (term3 A B _71694 _71695)). Qed.
Lemma lem5716686 {A B : Type'} (_71695 : A -> B) (_71694 : type1400 B) : (@support A B _71694 _71695) = (term4 A B _71695 _71694).
Proof. exact (TRANS (@lem5716684 A B _71694 _71695) (@lem5716685 A B _71695 _71694)). Qed.
Lemma lem5716687 {A : Type'} (_71696 : A -> Prop) : _71696 = _71696.
Proof. exact (eq_refl _71696). Qed.
Lemma lem5716688 {A B : Type'} (_71695 : A -> B) (_71694 : type1400 B) (_71696 : A -> Prop) : (@support A B _71694 _71695 _71696) = (term5 A B _71695 _71694 _71696).
Proof. exact (MK_COMB (@lem5716686 A B _71695 _71694) (@lem5716687 A _71696)). Qed.
Lemma lem5716689 {A B : Type'} (_71696 : A -> Prop) (_71695 : A -> B) (_71694 : type1400 B) : (term5 A B _71695 _71694 _71696) = (term6 A B _71696 _71695 _71694).
Proof. exact (eq_refl (term5 A B _71695 _71694 _71696)). Qed.
Lemma lem5716690 {A B : Type'} (_71696 : A -> Prop) (_71695 : A -> B) (_71694 : type1400 B) : (@support A B _71694 _71695 _71696) = (term6 A B _71696 _71695 _71694).
Proof. exact (TRANS (@lem5716688 A B _71695 _71694 _71696) (@lem5716689 A B _71696 _71695 _71694)). Qed.
Lemma lem5716691 {A B : Type'} (_71695 : A -> B) (_71694 : type1400 B) : term7 A B _71695 _71694.
Proof. exact (fun _71696 : A -> Prop => @lem5716690 A B _71696 _71695 _71694). Qed.
Lemma lem5716692 {A B : Type'} (_71694 : type1400 B) : term8 A B _71694.
Proof. exact (fun _71695 : A -> B => @lem5716691 A B _71695 _71694). Qed.
Lemma lem5716693 {A B : Type'} : term9 A B.
Proof. exact (fun _71694 : type1400 B => @lem5716692 A B _71694). Qed.
Lemma lem5716694 {A B : Type'} (_71694 : type1400 B) : term10 A B _71694.
Proof. exact (@lem5716693 A B _71694). Qed.
Lemma lem5716695 {A B : Type'} (_71694 : type1400 B) : (term10 A B _71694) = (term8 A B _71694).
Proof. exact (eq_refl (term10 A B _71694)). Qed.
Lemma lem5716696 {A B : Type'} (_71694 : type1400 B) : term8 A B _71694.
Proof. exact (EQ_MP (@lem5716695 A B _71694) (@lem5716694 A B _71694)). Qed.
Lemma lem5716697 {A B : Type'} (_71694 : type1400 B) (_71695 : A -> B) : term11 A B _71694 _71695.
Proof. exact (@lem5716696 A B _71694 _71695). Qed.
Lemma lem5716698 {A B : Type'} (_71695 : A -> B) (_71694 : type1400 B) : (term11 A B _71694 _71695) = (term7 A B _71695 _71694).
Proof. exact (eq_refl (term11 A B _71694 _71695)). Qed.
Lemma lem5716699 {A B : Type'} (_71695 : A -> B) (_71694 : type1400 B) : term7 A B _71695 _71694.
Proof. exact (EQ_MP (@lem5716698 A B _71695 _71694) (@lem5716697 A B _71694 _71695)). Qed.
Lemma lem5716700 {A B : Type'} (_71695 : A -> B) (_71694 : type1400 B) (_71696 : A -> Prop) : term12 A B _71695 _71694 _71696.
Proof. exact (@lem5716699 A B _71695 _71694 _71696). Qed.
Lemma lem5716701 {A B : Type'} (_71696 : A -> Prop) (_71695 : A -> B) (_71694 : type1400 B) : (term12 A B _71695 _71694 _71696) = ((@support A B _71694 _71695 _71696) = (term6 A B _71696 _71695 _71694)).
Proof. exact (eq_refl (term12 A B _71695 _71694 _71696)). Qed.
Lemma lem5716702 {A B : Type'} (_71696 : A -> Prop) (_71695 : A -> B) (_71694 : type1400 B) : (@support A B _71694 _71695 _71696) = (term6 A B _71696 _71695 _71694).
Proof. exact (EQ_MP (@lem5716701 A B _71696 _71695 _71694) (@lem5716700 A B _71695 _71694 _71696)). Qed.
Lemma lem5716758 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term6 A B s f op).
Proof. exact (@lem5716702 A B s f op). Qed.
Lemma lem5716759 {A B : Type'} (s : A -> Prop) (f : A -> B) : term13 A B s f.
Proof. exact (fun op : type1400 B => @lem5716758 A B s f op). Qed.
Lemma lem5716760 {A B : Type'} (s : A -> Prop) : term14 A B s.
Proof. exact (fun f : A -> B => @lem5716759 A B s f). Qed.
Lemma lem5716761 {A B : Type'} : term15 A B.
Proof. exact (fun s : A -> Prop => @lem5716760 A B s). Qed.
