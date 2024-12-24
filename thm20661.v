Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20661_term_abbrevs.
Require Import I_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem20614 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem15584 A x). Qed.
Lemma lem20615 {A : Type'} (x : A) : (term0 A x) = ((@I A x) = x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem20628 {A : Type'} (x : A) : (@I A x) = x.
Proof. exact (EQ_MP (@lem20615 A x) (@lem20614 A x)). Qed.
Lemma lem20629 {A B : Type'} (x : A -> B) : (@I (A -> B) x) = x.
Proof. exact (@lem20628 (A -> B) x). Qed.
Lemma lem20630 {A B : Type'} (f : A -> B) : (@I (A -> B) f) = f.
Proof. exact (@lem20629 A B f). Qed.
Lemma lem20631 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem20632 {A B : Type'} (f : A -> B) (x : A) : (@I (A -> B) f x) = (f x).
Proof. exact (MK_COMB (@lem20630 A B f) (@lem20631 A x)). Qed.
Lemma lem20633 {A B : Type'} (f : A -> B) (x : A) : (term1 A B f x) = (term1 A B f x).
Proof. exact (eq_refl (term1 A B f x)). Qed.
Lemma lem20634 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (@I (A -> B) f x)) = ((f x) = (f x)).
Proof. exact (MK_COMB (@lem20633 A B f x) (@lem20632 A B f x)). Qed.
Lemma lem20636 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem20637 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem20636 B x). Qed.
Lemma lem20638 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (f x)) = True.
Proof. exact (@lem20637 B (f x)). Qed.
Lemma lem20639 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (@I (A -> B) f x)) = True.
Proof. exact (TRANS (@lem20634 A B f x) (@lem20638 A B f x)). Qed.
Lemma lem20640 {A B : Type'} (f : A -> B) : (term2 A B f) = (term3 A).
Proof. exact (fun_ext (fun x : A => @lem20639 A B f x)). Qed.
Lemma lem20641 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem20642 {A B : Type'} (f : A -> B) : (term4 A B f) = (term5 A).
Proof. exact (MK_COMB (@lem20641 A) (@lem20640 A B f)). Qed.
Lemma lem20644 {A : Type'} (t : Prop) : (term6 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem20645 {A : Type'} (t : Prop) : (term6 A t) = t.
Proof. exact (@lem20644 A t). Qed.
Lemma lem20646 {A : Type'} : (term5 A) = True.
Proof. exact (@lem20645 A True). Qed.
Lemma lem20647 {A B : Type'} (f : A -> B) : (term4 A B f) = True.
Proof. exact (TRANS (@lem20642 A B f) (@lem20646 A)). Qed.
Lemma lem20648 {A B : Type'} : (term7 A B) = (term8 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem20647 A B f)). Qed.
Lemma lem20649 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem20650 {A B : Type'} : (term9 A B) = (term10 A B).
Proof. exact (MK_COMB (@lem20649 A B) (@lem20648 A B)). Qed.
Lemma lem20652 {A : Type'} (t : Prop) : (term6 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem20653 {A B : Type'} (t : Prop) : (term11 A B t) = t.
Proof. exact (@lem20652 (A -> B) t). Qed.
Lemma lem20654 {A B : Type'} : (term10 A B) = True.
Proof. exact (@lem20653 A B True). Qed.
Lemma lem20655 {A B : Type'} : (term9 A B) = True.
Proof. exact (TRANS (@lem20650 A B) (@lem20654 A B)). Qed.
Lemma lem20656 {A B : Type'} : True = (term9 A B).
Proof. exact (SYM (@lem20655 A B)). Qed.
Lemma lem20657 {A B : Type'} : term9 A B.
Proof. exact (EQ_MP (@lem20656 A B) (@lem0)). Qed.
Lemma lem20658 {A B : Type'} (f : A -> B) : term12 A B f.
Proof. exact (@lem20657 A B f). Qed.
Lemma lem20659 {A B : Type'} (f : A -> B) : (term12 A B f) = (term4 A B f).
Proof. exact (eq_refl (term12 A B f)). Qed.
Lemma lem20660 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (EQ_MP (@lem20659 A B f) (@lem20658 A B f)). Qed.
Lemma lem20661 {A B : Type'} (f : A -> B) (x : A) : term13 A B f x.
Proof. exact (@lem20660 A B f x). Qed.
