Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4333782_term_abbrevs.
Require Import CROSS_UNIV_spec.
Require Import INFINITE_CROSS_EQ_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import UNIV_NOT_EMPTY_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm82_spec.
Lemma lem4333681 {A B : Type'} (h1 : (@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B))) : (@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B)).
Proof. exact (h1). Qed.
Lemma lem4333682 {A B : Type'} (h1 : (@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B))) : (@UNIV (prod A B)) = (@CROSS B A (@UNIV A) (@UNIV B)).
Proof. exact (SYM (@lem4333681 A B h1)). Qed.
Lemma lem4333683 {A B : Type'} (h1 : (@UNIV (prod A B)) = (@CROSS B A (@UNIV A) (@UNIV B))) : (@UNIV (prod A B)) = (@CROSS B A (@UNIV A) (@UNIV B)).
Proof. exact (h1). Qed.
Lemma lem4333684 {A B : Type'} (h1 : (@UNIV (prod A B)) = (@CROSS B A (@UNIV A) (@UNIV B))) : (@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B)).
Proof. exact (SYM (@lem4333683 A B h1)). Qed.
Lemma lem4333685 {A B : Type'} : ((@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B))) = ((@UNIV (prod A B)) = (@CROSS B A (@UNIV A) (@UNIV B))).
Proof. exact (prop_ext (fun h1 : (@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B)) => @lem4333682 A B h1) (fun h1 : (@UNIV (prod A B)) = (@CROSS B A (@UNIV A) (@UNIV B)) => @lem4333684 A B h1)). Qed.
Lemma lem4333687 {A : Type'} : term0 A.
Proof. exact (@lem82 ((@UNIV A) = (@EMPTY A))). Qed.
Lemma lem4333700 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (@lem4333570 A B s). Qed.
Lemma lem4333701 {A B : Type'} (s : A -> Prop) : (term1 A B s) = (term2 A B s).
Proof. exact (eq_refl (term1 A B s)). Qed.
Lemma lem4333702 {A B : Type'} (s : A -> Prop) : term2 A B s.
Proof. exact (EQ_MP (@lem4333701 A B s) (@lem4333700 A B s)). Qed.
Lemma lem4333703 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term3 A B s t.
Proof. exact (@lem4333702 A B s t). Qed.
Lemma lem4333704 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term3 A B s t) = ((term4 A B s t) = (term5 A B s t)).
Proof. exact (eq_refl (term3 A B s t)). Qed.
Lemma lem4333709 {A B : Type'} : (@UNIV (prod A B)) = (@CROSS B A (@UNIV A) (@UNIV B)).
Proof. exact (EQ_MP (@lem4333685 A B) (@lem4327456 A B)). Qed.
Lemma lem4333714 {A B : Type'} : (@INFINITE (prod A B)) = (@INFINITE (prod A B)).
Proof. exact (eq_refl (@INFINITE (prod A B))). Qed.
Lemma lem4333715 {A B : Type'} : (@INFINITE (prod A B) (@UNIV (prod A B))) = (term6 A B).
Proof. exact (MK_COMB (@lem4333714 A B) (@lem4333709 A B)). Qed.
Lemma lem4333717 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term4 A B s t) = (term5 A B s t).
Proof. exact (EQ_MP (@lem4333704 A B s t) (@lem4333703 A B s t)). Qed.
Lemma lem4333718 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term4 A B s t) = (term5 A B s t).
Proof. exact (@lem4333717 A B s t). Qed.
Lemma lem4333719 {A B : Type'} : (term6 A B) = (term7 A B).
Proof. exact (@lem4333718 A B (@UNIV A) (@UNIV B)). Qed.
Lemma lem4333725 {A : Type'} : ((@UNIV A) = (@EMPTY A)) = False.
Proof. exact (@lem4333687 A (@lem3216430 A)). Qed.
Lemma lem4333726 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4333727 {A : Type'} : (term8 A) = (~ False).
Proof. exact (MK_COMB (@lem4333726) (@lem4333725 A)). Qed.
Lemma lem4333729 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4333730 {A : Type'} : (term8 A) = True.
Proof. exact (TRANS (@lem4333727 A) (@lem4333729)). Qed.
Lemma lem4333731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4333732 {A : Type'} : (term9 A) = (and True).
Proof. exact (MK_COMB (@lem4333731) (@lem4333730 A)). Qed.
Lemma lem4333735 {B : Type'} : (@INFINITE B (@UNIV B)) = (@INFINITE B (@UNIV B)).
Proof. exact (eq_refl (@INFINITE B (@UNIV B))). Qed.
Lemma lem4333736 {A B : Type'} : (term10 A B) = (term11 B).
Proof. exact (MK_COMB (@lem4333732 A) (@lem4333735 B)). Qed.
Lemma lem4333738 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4333739 {B : Type'} : (term11 B) = (@INFINITE B (@UNIV B)).
Proof. exact (@lem4333738 (@INFINITE B (@UNIV B))). Qed.
Lemma lem4333742 {A B : Type'} : (term10 A B) = (@INFINITE B (@UNIV B)).
Proof. exact (TRANS (@lem4333736 A B) (@lem4333739 B)). Qed.
Lemma lem4333743 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4333744 {A B : Type'} : (term12 A B) = (term13 B).
Proof. exact (MK_COMB (@lem4333743) (@lem4333742 A B)). Qed.
Lemma lem4333750 {A : Type'} : ((@UNIV A) = (@EMPTY A)) = False.
Proof. exact (@lem4333687 A (@lem3216430 A)). Qed.
Lemma lem4333751 {B : Type'} : ((@UNIV B) = (@EMPTY B)) = False.
Proof. exact (@lem4333750 B). Qed.
Lemma lem4333752 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4333753 {B : Type'} : (term8 B) = (~ False).
Proof. exact (MK_COMB (@lem4333752) (@lem4333751 B)). Qed.
Lemma lem4333755 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4333756 {B : Type'} : (term8 B) = True.
Proof. exact (TRANS (@lem4333753 B) (@lem4333755)). Qed.
Lemma lem4333757 {A : Type'} : (term14 A) = (term14 A).
Proof. exact (eq_refl (term14 A)). Qed.
Lemma lem4333758 {A B : Type'} : (term15 A B) = (term16 A).
Proof. exact (MK_COMB (@lem4333757 A) (@lem4333756 B)). Qed.
Lemma lem4333760 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4333761 {A : Type'} : (term16 A) = (@INFINITE A (@UNIV A)).
Proof. exact (@lem4333760 (@INFINITE A (@UNIV A))). Qed.
Lemma lem4333764 {A B : Type'} : (term15 A B) = (@INFINITE A (@UNIV A)).
Proof. exact (TRANS (@lem4333758 A B) (@lem4333761 A)). Qed.
Lemma lem4333765 {A B : Type'} : (term7 A B) = (term17 A B).
Proof. exact (MK_COMB (@lem4333744 A B) (@lem4333764 A B)). Qed.
Lemma lem4333768 {A B : Type'} : (term6 A B) = (term17 A B).
Proof. exact (TRANS (@lem4333719 A B) (@lem4333765 A B)). Qed.
Lemma lem4333769 {A B : Type'} : (@INFINITE (prod A B) (@UNIV (prod A B))) = (term17 A B).
Proof. exact (TRANS (@lem4333715 A B) (@lem4333768 A B)). Qed.
Lemma lem4333770 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4333771 {A B : Type'} : (term18 A B) = (term19 A B).
Proof. exact (MK_COMB (@lem4333770) (@lem4333769 A B)). Qed.
Lemma lem4333778 {A B : Type'} : (term20 A B) = (term20 A B).
Proof. exact (eq_refl (term20 A B)). Qed.
Lemma lem4333779 {A B : Type'} : ((@INFINITE (prod A B) (@UNIV (prod A B))) = (term20 A B)) = ((term17 A B) = (term20 A B)).
Proof. exact (MK_COMB (@lem4333771 A B) (@lem4333778 A B)). Qed.
Lemma lem4333782 {A B : Type'} : ((term17 A B) = (term20 A B)) = ((@INFINITE (prod A B) (@UNIV (prod A B))) = (term20 A B)).
Proof. exact (SYM (@lem4333779 A B)). Qed.
