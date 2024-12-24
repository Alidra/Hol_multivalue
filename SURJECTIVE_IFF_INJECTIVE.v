Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SURJECTIVE_IFF_INJECTIVE_term_abbrevs.
Require Import SURJECTIVE_IFF_INJECTIVE_GEN_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4944740 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4944739 A B s). Qed.
Lemma lem4944741 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4944742 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4944741 A B s) (@lem4944740 A B s)). Qed.
Lemma lem4944743 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term2 A B s t.
Proof. exact (@lem4944742 A B s t). Qed.
Lemma lem4944744 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term2 A B s t) = (term3 A B t s).
Proof. exact (eq_refl (term2 A B s t)). Qed.
Lemma lem4944745 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term3 A B t s.
Proof. exact (EQ_MP (@lem4944744 A B t s) (@lem4944743 A B s t)). Qed.
Lemma lem4944746 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term4 A B t s f.
Proof. exact (@lem4944745 A B t s f). Qed.
Lemma lem4944747 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : (term4 A B t s f) = (term5 A B t s f).
Proof. exact (eq_refl (term4 A B t s f)). Qed.
Lemma lem4944748 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term5 A B t s f.
Proof. exact (EQ_MP (@lem4944747 A B t s f) (@lem4944746 A B t s f)). Qed.
Lemma lem4944749 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term6 A B f s t) : term6 A B f s t.
Proof. exact (h1). Qed.
Lemma lem4944750 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (h1 : term6 A B f s t) : (term7 A B t s f) = (term8 A B s f).
Proof. exact (@lem4944748 A B t s f (@lem4944749 A B f s t h1)). Qed.
Lemma lem4944767 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term9 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4944768 (p : Prop) (q : Prop) (p' : Prop) : term10 p q p'.
Proof. exact (fun q' : Prop => @lem4944767 p q p' q'). Qed.
Lemma lem4944769 (p : Prop) (q : Prop) : term11 p q.
Proof. exact (fun p' : Prop => @lem4944768 p q p'). Qed.
Lemma lem4944770 {A : Type'} (s : A -> Prop) (f : A -> A) : term12 A s f.
Proof. exact (@lem4944769 (term13 A f s) ((term14 A s f) = (term15 A s f))). Qed.
Lemma lem4944771 {A : Type'} (s : A -> Prop) (f : A -> A) (p' : Prop) : term16 A s f p'.
Proof. exact (@lem4944770 A s f p'). Qed.
Lemma lem4944772 {A : Type'} (s : A -> Prop) (f : A -> A) (p' : Prop) : (term16 A s f p') = (term17 A s f p').
Proof. exact (eq_refl (term16 A s f p')). Qed.
Lemma lem4944773 {A : Type'} (s : A -> Prop) (f : A -> A) (p' : Prop) : term17 A s f p'.
Proof. exact (EQ_MP (@lem4944772 A s f p') (@lem4944771 A s f p')). Qed.
Lemma lem4944774 {A : Type'} (s : A -> Prop) (f : A -> A) (p' : Prop) (q' : Prop) : term18 A s f p' q'.
Proof. exact (@lem4944773 A s f p' q'). Qed.
Lemma lem4944775 {A : Type'} (s : A -> Prop) (f : A -> A) (p' : Prop) (q' : Prop) : (term18 A s f p' q') = (term19 A s f p' q').
Proof. exact (eq_refl (term18 A s f p' q')). Qed.
Lemma lem4944776 {A : Type'} (s : A -> Prop) (f : A -> A) (p' : Prop) (q' : Prop) : term19 A s f p' q'.
Proof. exact (EQ_MP (@lem4944775 A s f p' q') (@lem4944774 A s f p' q')). Qed.
Lemma lem4944779 {A : Type'} (f : A -> A) (s : A -> Prop) : (term13 A f s) = (term13 A f s).
Proof. exact (eq_refl (term13 A f s)). Qed.
Lemma lem4944780 {A : Type'} (f : A -> A) (s : A -> Prop) (q' : Prop) : term20 A f s q'.
Proof. exact (@lem4944776 A s f (term13 A f s) q'). Qed.
Lemma lem4944781 {A : Type'} (f : A -> A) (s : A -> Prop) (q' : Prop) : term21 A f s q'.
Proof. exact (@lem4944780 A f s q' (@lem4944779 A f s)). Qed.
Lemma lem4944782 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : term13 A f s.
Proof. exact (h1). Qed.
Lemma lem4944783 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : term22 A f s.
Proof. exact (proj2 (@lem4944782 A f s h1)). Qed.
Lemma lem4944784 {A : Type'} (f : A -> A) (s : A -> Prop) : (term22 A f s) = ((term22 A f s) = True).
Proof. exact (@lem7 (term22 A f s)). Qed.
Lemma lem4944786 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : @FINITE A s.
Proof. exact (proj1 (@lem4944782 A f s h1)). Qed.
Lemma lem4944787 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4944792 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) : term5 A B t s f.
Proof. exact (fun h0 : term6 A B f s t => @lem4944750 A B f s t h0). Qed.
Lemma lem4944793 {A : Type'} (t : A -> Prop) (s : A -> Prop) (f : A -> A) : term23 A t s f.
Proof. exact (@lem4944792 A A t s f). Qed.
Lemma lem4944794 {A : Type'} (s : A -> Prop) (f : A -> A) : term24 A s f.
Proof. exact (@lem4944793 A s s f). Qed.
Lemma lem4944798 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4944787 A s) (@lem4944786 A f s h1)). Qed.
Lemma lem4944799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4944800 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : (term25 A s) = (and True).
Proof. exact (MK_COMB (@lem4944799) (@lem4944798 A f s h1)). Qed.
Lemma lem4944804 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4944787 A s) (@lem4944786 A f s h1)). Qed.
Lemma lem4944805 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4944806 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : (term25 A s) = (and True).
Proof. exact (MK_COMB (@lem4944805) (@lem4944804 A f s h1)). Qed.
Lemma lem4944810 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4944811 (x : nat) : (x = x) = True.
Proof. exact (@lem4944810 nat x). Qed.
Lemma lem4944812 {A : Type'} (s : A -> Prop) : ((@CARD A s) = (@CARD A s)) = True.
Proof. exact (@lem4944811 (@CARD A s)). Qed.
Lemma lem4944813 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4944814 {A : Type'} (s : A -> Prop) : (term26 A s) = (and True).
Proof. exact (MK_COMB (@lem4944813) (@lem4944812 A s)). Qed.
Lemma lem4944816 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : (term22 A f s) = True.
Proof. exact (EQ_MP (@lem4944784 A f s) (@lem4944783 A f s h1)). Qed.
Lemma lem4944817 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : (term27 A f s) = (True /\ True).
Proof. exact (MK_COMB (@lem4944814 A s) (@lem4944816 A f s h1)). Qed.
Lemma lem4944819 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4944820 : (True /\ True) = True.
Proof. exact (@lem4944819 True). Qed.
Lemma lem4944821 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : (term27 A f s) = True.
Proof. exact (TRANS (@lem4944817 A f s h1) (@lem4944820)). Qed.
Lemma lem4944822 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : (term28 A f s) = (True /\ True).
Proof. exact (MK_COMB (@lem4944806 A f s h1) (@lem4944821 A f s h1)). Qed.
Lemma lem4944824 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4944825 : (True /\ True) = True.
Proof. exact (@lem4944824 True). Qed.
Lemma lem4944826 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : (term28 A f s) = True.
Proof. exact (TRANS (@lem4944822 A f s h1) (@lem4944825)). Qed.
Lemma lem4944827 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : (term29 A f s) = (True /\ True).
Proof. exact (MK_COMB (@lem4944800 A f s h1) (@lem4944826 A f s h1)). Qed.
Lemma lem4944829 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4944830 : (True /\ True) = True.
Proof. exact (@lem4944829 True). Qed.
Lemma lem4944831 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : (term29 A f s) = True.
Proof. exact (TRANS (@lem4944827 A f s h1) (@lem4944830)). Qed.
Lemma lem4944832 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : True = (term29 A f s).
Proof. exact (SYM (@lem4944831 A f s h1)). Qed.
Lemma lem4944833 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : term29 A f s.
Proof. exact (EQ_MP (@lem4944832 A f s h1) (@lem0)). Qed.
Lemma lem4944834 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : (term14 A s f) = (term15 A s f).
Proof. exact (@lem4944794 A s f (@lem4944833 A f s h1)). Qed.
Lemma lem4944888 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4944889 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : (term30 A s f) = (term31 A s f).
Proof. exact (MK_COMB (@lem4944888) (@lem4944834 A f s h1)). Qed.
Lemma lem4944996 {A : Type'} (s : A -> Prop) (f : A -> A) : (term15 A s f) = (term15 A s f).
Proof. exact (eq_refl (term15 A s f)). Qed.
Lemma lem4944997 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : ((term14 A s f) = (term15 A s f)) = ((term15 A s f) = (term15 A s f)).
Proof. exact (MK_COMB (@lem4944889 A f s h1) (@lem4944996 A s f)). Qed.
Lemma lem4944999 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4945000 (x : Prop) : (x = x) = True.
Proof. exact (@lem4944999 Prop x). Qed.
Lemma lem4945001 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term15 A s f) = (term15 A s f)) = True.
Proof. exact (@lem4945000 (term15 A s f)). Qed.
Lemma lem4945002 {A : Type'} (f : A -> A) (s : A -> Prop) (h1 : term13 A f s) : ((term14 A s f) = (term15 A s f)) = True.
Proof. exact (TRANS (@lem4944997 A f s h1) (@lem4945001 A s f)). Qed.
Lemma lem4945003 {A : Type'} (s : A -> Prop) (f : A -> A) : term32 A s f.
Proof. exact (fun h0 : term13 A f s => @lem4945002 A f s h0). Qed.
Lemma lem4945004 {A : Type'} (f : A -> A) (s : A -> Prop) : term33 A f s.
Proof. exact (@lem4944781 A f s True). Qed.
Lemma lem4945005 {A : Type'} (f : A -> A) (s : A -> Prop) : (term34 A s f) = (term35 A f s).
Proof. exact (@lem4945004 A f s (@lem4945003 A s f)). Qed.
Lemma lem4945007 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4945008 {A : Type'} (f : A -> A) (s : A -> Prop) : (term35 A f s) = True.
Proof. exact (@lem4945007 (term13 A f s)). Qed.
Lemma lem4945009 {A : Type'} (s : A -> Prop) (f : A -> A) : (term34 A s f) = True.
Proof. exact (TRANS (@lem4945005 A f s) (@lem4945008 A f s)). Qed.
Lemma lem4945010 {A : Type'} (s : A -> Prop) : (term36 A s) = (term37 A).
Proof. exact (fun_ext (fun f : A -> A => @lem4945009 A s f)). Qed.
Lemma lem4945011 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem4945012 {A : Type'} (s : A -> Prop) : (term38 A s) = (term39 A).
Proof. exact (MK_COMB (@lem4945011 A) (@lem4945010 A s)). Qed.
Lemma lem4945014 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4945015 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (@lem4945014 (A -> A) t). Qed.
Lemma lem4945016 {A : Type'} : (term39 A) = True.
Proof. exact (@lem4945015 A True). Qed.
Lemma lem4945017 {A : Type'} (s : A -> Prop) : (term38 A s) = True.
Proof. exact (TRANS (@lem4945012 A s) (@lem4945016 A)). Qed.
Lemma lem4945018 {A : Type'} : (term42 A) = (term43 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4945017 A s)). Qed.
Lemma lem4945019 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4945020 {A : Type'} : (term44 A) = (term45 A).
Proof. exact (MK_COMB (@lem4945019 A) (@lem4945018 A)). Qed.
Lemma lem4945022 {A : Type'} (t : Prop) : (term40 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4945023 {A : Type'} (t : Prop) : (term46 A t) = t.
Proof. exact (@lem4945022 (A -> Prop) t). Qed.
Lemma lem4945024 {A : Type'} : (term45 A) = True.
Proof. exact (@lem4945023 A True). Qed.
Lemma lem4945025 {A : Type'} : (term44 A) = True.
Proof. exact (TRANS (@lem4945020 A) (@lem4945024 A)). Qed.
Lemma lem4945026 {A : Type'} : True = (term44 A).
Proof. exact (SYM (@lem4945025 A)). Qed.
Lemma lem4945027 {A : Type'} : term44 A.
Proof. exact (EQ_MP (@lem4945026 A) (@lem0)). Qed.
