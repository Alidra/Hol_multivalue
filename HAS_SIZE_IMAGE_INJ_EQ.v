Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_IMAGE_INJ_EQ_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import CARD_IMAGE_INJ_spec.
Require Import FINITE_IMAGE_INJ_EQ_spec.
Require Import HAS_SIZE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm7_spec.
Lemma lem4018622 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem4018623 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term1 A B f.
Proof. exact (@lem4018622 A B h1 f). Qed.
Lemma lem4018624 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem4018625 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (EQ_MP (@lem4018624 A B f) (@lem4018623 A B f h1)). Qed.
Lemma lem4018626 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term3 A B f s.
Proof. exact (@lem4018625 A B f h1 s). Qed.
Lemma lem4018627 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem4018628 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term4 A B f s.
Proof. exact (EQ_MP (@lem4018627 A B f s) (@lem4018626 A B f s h1)). Qed.
Lemma lem4018629 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term5 A B f s) : term5 A B f s.
Proof. exact (h1). Qed.
Lemma lem4018630 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) (h2 : term5 A B f s) : (term6 A B f s) = (@CARD A s).
Proof. exact (@lem4018628 A B f s h1 (@lem4018629 A B f s h2)). Qed.
Lemma lem4018631 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term5 A B f s) : term7 A B f s.
Proof. exact (fun h0 : term0 A B => @lem4018630 A B f s h0 h1). Qed.
Lemma lem4018632 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (h1). Qed.
Lemma lem4018633 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) (h2 : term5 A B f s) : (term6 A B f s) = (@CARD A s).
Proof. exact (@lem4018631 A B f s h2 (@lem4018632 A B h1)). Qed.
Lemma lem4018634 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term0 A B) : term4 A B f s.
Proof. exact (fun h0 : term5 A B f s => @lem4018633 A B f s h1 h0). Qed.
Lemma lem4018635 {A B : Type'} (f : A -> B) (h1 : term0 A B) : term2 A B f.
Proof. exact (fun s : A -> Prop => @lem4018634 A B f s h1). Qed.
Lemma lem4018636 {A B : Type'} (h1 : term0 A B) : term0 A B.
Proof. exact (fun f : A -> B => @lem4018635 A B f h1). Qed.
Lemma lem4018637 {A B : Type'} : term8 A B.
Proof. exact (fun h0 : term0 A B => @lem4018636 A B h0). Qed.
Lemma lem4018638 {A B : Type'} : term0 A B.
Proof. exact (@lem4018637 A B (@lem3996358 A B)). Qed.
Lemma lem4018639 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem4018638 A B f). Qed.
Lemma lem4018640 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem4018641 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem4018640 A B f) (@lem4018639 A B f)). Qed.
Lemma lem4018642 {A B : Type'} (f : A -> B) (s : A -> Prop) : term3 A B f s.
Proof. exact (@lem4018641 A B f s). Qed.
Lemma lem4018643 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem4018645 {A B : Type'} (h1 : term9 A B) : term9 A B.
Proof. exact (h1). Qed.
Lemma lem4018646 {A B : Type'} (f : A -> B) (h1 : term9 A B) : term10 A B f.
Proof. exact (@lem4018645 A B h1 f). Qed.
Lemma lem4018647 {A B : Type'} (f : A -> B) : (term10 A B f) = (term11 A B f).
Proof. exact (eq_refl (term10 A B f)). Qed.
Lemma lem4018648 {A B : Type'} (f : A -> B) (h1 : term9 A B) : term11 A B f.
Proof. exact (EQ_MP (@lem4018647 A B f) (@lem4018646 A B f h1)). Qed.
Lemma lem4018649 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term9 A B) : term12 A B f s.
Proof. exact (@lem4018648 A B f h1 s). Qed.
Lemma lem4018650 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term12 A B f s) = (term13 A B f s).
Proof. exact (eq_refl (term12 A B f s)). Qed.
Lemma lem4018651 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term9 A B) : term13 A B f s.
Proof. exact (EQ_MP (@lem4018650 A B f s) (@lem4018649 A B f s h1)). Qed.
Lemma lem4018652 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term14 A B s f) : term14 A B s f.
Proof. exact (h1). Qed.
Lemma lem4018653 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term14 A B s f) (h2 : term9 A B) : (term15 A B f s) = (@FINITE A s).
Proof. exact (@lem4018651 A B f s h2 (@lem4018652 A B s f h1)). Qed.
Lemma lem4018654 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term14 A B s f) : term16 A B f s.
Proof. exact (fun h0 : term9 A B => @lem4018653 A B s f h1 h0). Qed.
Lemma lem4018655 {A B : Type'} (h1 : term9 A B) : term9 A B.
Proof. exact (h1). Qed.
Lemma lem4018656 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term14 A B s f) (h2 : term9 A B) : (term15 A B f s) = (@FINITE A s).
Proof. exact (@lem4018654 A B s f h1 (@lem4018655 A B h2)). Qed.
Lemma lem4018657 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term9 A B) : term13 A B f s.
Proof. exact (fun h0 : term14 A B s f => @lem4018656 A B s f h0 h1). Qed.
Lemma lem4018658 {A B : Type'} (f : A -> B) (h1 : term9 A B) : term11 A B f.
Proof. exact (fun s : A -> Prop => @lem4018657 A B f s h1). Qed.
Lemma lem4018659 {A B : Type'} (h1 : term9 A B) : term9 A B.
Proof. exact (fun f : A -> B => @lem4018658 A B f h1). Qed.
Lemma lem4018660 {A B : Type'} : term17 A B.
Proof. exact (fun h0 : term9 A B => @lem4018659 A B h0). Qed.
Lemma lem4018661 {A B : Type'} : term9 A B.
Proof. exact (@lem4018660 A B (@lem3618990 A B)). Qed.
Lemma lem4018662 {A B : Type'} (f : A -> B) : term10 A B f.
Proof. exact (@lem4018661 A B f). Qed.
Lemma lem4018663 {A B : Type'} (f : A -> B) : (term10 A B f) = (term11 A B f).
Proof. exact (eq_refl (term10 A B f)). Qed.
Lemma lem4018664 {A B : Type'} (f : A -> B) : term11 A B f.
Proof. exact (EQ_MP (@lem4018663 A B f) (@lem4018662 A B f)). Qed.
Lemma lem4018665 {A B : Type'} (f : A -> B) (s : A -> Prop) : term12 A B f s.
Proof. exact (@lem4018664 A B f s). Qed.
Lemma lem4018666 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term12 A B f s) = (term13 A B f s).
Proof. exact (eq_refl (term12 A B f s)). Qed.
Lemma lem4018686 (a' : Prop) : term18 a'.
Proof. exact (@lem9851 a'). Qed.
Lemma lem4018687 (a' : Prop) : (term18 a') = (term19 a').
Proof. exact (eq_refl (term18 a')). Qed.
Lemma lem4018688 (a' : Prop) : term19 a'.
Proof. exact (EQ_MP (@lem4018687 a') (@lem4018686 a')). Qed.
Lemma lem4018689 (a' : Prop) (h1 : a' = True) : a' = True.
Proof. exact (h1). Qed.
Lemma lem4018690 (a' : Prop) (h1 : a' = False) : a' = False.
Proof. exact (h1). Qed.
Lemma lem4018709 (b' : Prop) (a : Prop) (b : Prop) : (term20 b' a b) = (term20 b' a b).
Proof. exact (eq_refl (term20 b' a b)). Qed.
Lemma lem4018710 (b' : Prop) (a : Prop) (b : Prop) (a' : Prop) (h1 : a' = True) : (term21 b' a b a') = (term22 b' a b).
Proof. exact (MK_COMB (@lem4018709 b' a b) (@lem4018689 a' h1)). Qed.
Lemma lem4018711 (b' : Prop) (a : Prop) (b : Prop) : (term22 b' a b) = (term23 b' a b).
Proof. exact (eq_refl (term22 b' a b)). Qed.
Lemma lem4018712 (b' : Prop) (a : Prop) (b : Prop) (a' : Prop) : (term24 b' a b a') = (term24 b' a b a').
Proof. exact (eq_refl (term24 b' a b a')). Qed.
Lemma lem4018713 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) : ((term21 b' a b a') = (term22 b' a b)) = ((term21 b' a b a') = (term23 b' a b)).
Proof. exact (MK_COMB (@lem4018712 b' a b a') (@lem4018711 b' a b)). Qed.
Lemma lem4018714 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) : (term21 b' a b a') = (term25 a' b' a b).
Proof. exact (eq_refl (term21 b' a b a')). Qed.
Lemma lem4018715 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4018716 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) : (term24 b' a b a') = (term26 a' b' a b).
Proof. exact (MK_COMB (@lem4018715) (@lem4018714 a' b' a b)). Qed.
Lemma lem4018717 (b' : Prop) (a : Prop) (b : Prop) : (term23 b' a b) = (term23 b' a b).
Proof. exact (eq_refl (term23 b' a b)). Qed.
Lemma lem4018718 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) : ((term21 b' a b a') = (term23 b' a b)) = ((term25 a' b' a b) = (term23 b' a b)).
Proof. exact (MK_COMB (@lem4018716 a' b' a b) (@lem4018717 b' a b)). Qed.
Lemma lem4018719 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) : ((term21 b' a b a') = (term22 b' a b)) = ((term25 a' b' a b) = (term23 b' a b)).
Proof. exact (TRANS (@lem4018713 a' b' a b) (@lem4018718 a' b' a b)). Qed.
Lemma lem4018720 (b' : Prop) (a : Prop) (b : Prop) (a' : Prop) (h1 : a' = True) : (term25 a' b' a b) = (term23 b' a b).
Proof. exact (EQ_MP (@lem4018719 a' b' a b) (@lem4018710 b' a b a' h1)). Qed.
Lemma lem4018721 (b' : Prop) (a : Prop) (b : Prop) (a' : Prop) (h1 : a' = True) : (term23 b' a b) = (term25 a' b' a b).
Proof. exact (SYM (@lem4018720 b' a b a' h1)). Qed.
Lemma lem4018722 (b' : Prop) (a : Prop) (b : Prop) : (term20 b' a b) = (term20 b' a b).
Proof. exact (eq_refl (term20 b' a b)). Qed.
Lemma lem4018723 (b' : Prop) (a : Prop) (b : Prop) (a' : Prop) (h1 : a' = False) : (term21 b' a b a') = (term27 b' a b).
Proof. exact (MK_COMB (@lem4018722 b' a b) (@lem4018690 a' h1)). Qed.
Lemma lem4018724 (b' : Prop) (a : Prop) (b : Prop) : (term27 b' a b) = (term28 b' a b).
Proof. exact (eq_refl (term27 b' a b)). Qed.
Lemma lem4018725 (b' : Prop) (a : Prop) (b : Prop) (a' : Prop) : (term24 b' a b a') = (term24 b' a b a').
Proof. exact (eq_refl (term24 b' a b a')). Qed.
Lemma lem4018726 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) : ((term21 b' a b a') = (term27 b' a b)) = ((term21 b' a b a') = (term28 b' a b)).
Proof. exact (MK_COMB (@lem4018725 b' a b a') (@lem4018724 b' a b)). Qed.
Lemma lem4018727 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) : (term21 b' a b a') = (term25 a' b' a b).
Proof. exact (eq_refl (term21 b' a b a')). Qed.
Lemma lem4018728 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4018729 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) : (term24 b' a b a') = (term26 a' b' a b).
Proof. exact (MK_COMB (@lem4018728) (@lem4018727 a' b' a b)). Qed.
Lemma lem4018730 (b' : Prop) (a : Prop) (b : Prop) : (term28 b' a b) = (term28 b' a b).
Proof. exact (eq_refl (term28 b' a b)). Qed.
Lemma lem4018731 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) : ((term21 b' a b a') = (term28 b' a b)) = ((term25 a' b' a b) = (term28 b' a b)).
Proof. exact (MK_COMB (@lem4018729 a' b' a b) (@lem4018730 b' a b)). Qed.
Lemma lem4018732 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) : ((term21 b' a b a') = (term27 b' a b)) = ((term25 a' b' a b) = (term28 b' a b)).
Proof. exact (TRANS (@lem4018726 a' b' a b) (@lem4018731 a' b' a b)). Qed.
Lemma lem4018733 (b' : Prop) (a : Prop) (b : Prop) (a' : Prop) (h1 : a' = False) : (term25 a' b' a b) = (term28 b' a b).
Proof. exact (EQ_MP (@lem4018732 a' b' a b) (@lem4018723 b' a b a' h1)). Qed.
Lemma lem4018734 (b' : Prop) (a : Prop) (b : Prop) (a' : Prop) (h1 : a' = False) : (term28 b' a b) = (term25 a' b' a b).
Proof. exact (SYM (@lem4018733 b' a b a' h1)). Qed.
Lemma lem4018740 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4018741 (a : Prop) : (True = a) = a.
Proof. exact (@lem4018740 a). Qed.
Lemma lem4018742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4018743 (a : Prop) : (term29 a) = (and a).
Proof. exact (MK_COMB (@lem4018742) (@lem4018741 a)). Qed.
Lemma lem4018748 (a : Prop) (b' : Prop) (b : Prop) : (term30 a b' b) = (term30 a b' b).
Proof. exact (eq_refl (term30 a b' b)). Qed.
Lemma lem4018749 (a : Prop) (b' : Prop) (b : Prop) : (term31 a b' b) = (term32 a b' b).
Proof. exact (MK_COMB (@lem4018743 a) (@lem4018748 a b' b)). Qed.
Lemma lem4018752 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4018753 (a : Prop) (b' : Prop) (b : Prop) : (term33 a b' b) = (term34 a b' b).
Proof. exact (MK_COMB (@lem4018752) (@lem4018749 a b' b)). Qed.
Lemma lem4018757 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4018758 (b' : Prop) : (True /\ b') = b'.
Proof. exact (@lem4018757 b'). Qed.
Lemma lem4018759 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4018760 (b' : Prop) : (term35 b') = (@eq Prop b').
Proof. exact (MK_COMB (@lem4018759) (@lem4018758 b')). Qed.
Lemma lem4018763 (a : Prop) (b : Prop) : (a /\ b) = (a /\ b).
Proof. exact (eq_refl (a /\ b)). Qed.
Lemma lem4018764 (b' : Prop) (a : Prop) (b : Prop) : ((True /\ b') = (a /\ b)) = (b' = (a /\ b)).
Proof. exact (MK_COMB (@lem4018760 b') (@lem4018763 a b)). Qed.
Lemma lem4018767 (b' : Prop) (a : Prop) (b : Prop) : (term23 b' a b) = (term36 b' a b).
Proof. exact (MK_COMB (@lem4018753 a b' b) (@lem4018764 b' a b)). Qed.
Lemma lem4018770 (b' : Prop) (a : Prop) (b : Prop) : (term36 b' a b) = (term23 b' a b).
Proof. exact (SYM (@lem4018767 b' a b)). Qed.
Lemma lem4018771 (a : Prop) : term18 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem4018772 (a : Prop) : (term18 a) = (term19 a).
Proof. exact (eq_refl (term18 a)). Qed.
Lemma lem4018773 (a : Prop) : term19 a.
Proof. exact (EQ_MP (@lem4018772 a) (@lem4018771 a)). Qed.
Lemma lem4018774 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem4018775 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem4018790 (b' : Prop) (b : Prop) : (term37 b' b) = (term37 b' b).
Proof. exact (eq_refl (term37 b' b)). Qed.
Lemma lem4018791 (b' : Prop) (b : Prop) (a : Prop) (h1 : a = True) : (term38 b' b a) = (term39 b' b).
Proof. exact (MK_COMB (@lem4018790 b' b) (@lem4018774 a h1)). Qed.
Lemma lem4018792 (b' : Prop) (b : Prop) : (term39 b' b) = (term40 b' b).
Proof. exact (eq_refl (term39 b' b)). Qed.
Lemma lem4018793 (b' : Prop) (b : Prop) (a : Prop) : (term41 b' b a) = (term41 b' b a).
Proof. exact (eq_refl (term41 b' b a)). Qed.
Lemma lem4018794 (a : Prop) (b' : Prop) (b : Prop) : ((term38 b' b a) = (term39 b' b)) = ((term38 b' b a) = (term40 b' b)).
Proof. exact (MK_COMB (@lem4018793 b' b a) (@lem4018792 b' b)). Qed.
Lemma lem4018795 (b' : Prop) (a : Prop) (b : Prop) : (term38 b' b a) = (term36 b' a b).
Proof. exact (eq_refl (term38 b' b a)). Qed.
Lemma lem4018796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4018797 (b' : Prop) (a : Prop) (b : Prop) : (term41 b' b a) = (term42 b' a b).
Proof. exact (MK_COMB (@lem4018796) (@lem4018795 b' a b)). Qed.
Lemma lem4018798 (b' : Prop) (b : Prop) : (term40 b' b) = (term40 b' b).
Proof. exact (eq_refl (term40 b' b)). Qed.
Lemma lem4018799 (a : Prop) (b' : Prop) (b : Prop) : ((term38 b' b a) = (term40 b' b)) = ((term36 b' a b) = (term40 b' b)).
Proof. exact (MK_COMB (@lem4018797 b' a b) (@lem4018798 b' b)). Qed.
Lemma lem4018800 (a : Prop) (b' : Prop) (b : Prop) : ((term38 b' b a) = (term39 b' b)) = ((term36 b' a b) = (term40 b' b)).
Proof. exact (TRANS (@lem4018794 a b' b) (@lem4018799 a b' b)). Qed.
Lemma lem4018801 (b' : Prop) (b : Prop) (a : Prop) (h1 : a = True) : (term36 b' a b) = (term40 b' b).
Proof. exact (EQ_MP (@lem4018800 a b' b) (@lem4018791 b' b a h1)). Qed.
Lemma lem4018802 (b' : Prop) (b : Prop) (a : Prop) (h1 : a = True) : (term40 b' b) = (term36 b' a b).
Proof. exact (SYM (@lem4018801 b' b a h1)). Qed.
Lemma lem4018803 (b' : Prop) (b : Prop) : (term37 b' b) = (term37 b' b).
Proof. exact (eq_refl (term37 b' b)). Qed.
Lemma lem4018804 (b' : Prop) (b : Prop) (a : Prop) (h1 : a = False) : (term38 b' b a) = (term43 b' b).
Proof. exact (MK_COMB (@lem4018803 b' b) (@lem4018775 a h1)). Qed.
Lemma lem4018805 (b' : Prop) (b : Prop) : (term43 b' b) = (term44 b' b).
Proof. exact (eq_refl (term43 b' b)). Qed.
Lemma lem4018806 (b' : Prop) (b : Prop) (a : Prop) : (term41 b' b a) = (term41 b' b a).
Proof. exact (eq_refl (term41 b' b a)). Qed.
Lemma lem4018807 (a : Prop) (b' : Prop) (b : Prop) : ((term38 b' b a) = (term43 b' b)) = ((term38 b' b a) = (term44 b' b)).
Proof. exact (MK_COMB (@lem4018806 b' b a) (@lem4018805 b' b)). Qed.
Lemma lem4018808 (b' : Prop) (a : Prop) (b : Prop) : (term38 b' b a) = (term36 b' a b).
Proof. exact (eq_refl (term38 b' b a)). Qed.
Lemma lem4018809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4018810 (b' : Prop) (a : Prop) (b : Prop) : (term41 b' b a) = (term42 b' a b).
Proof. exact (MK_COMB (@lem4018809) (@lem4018808 b' a b)). Qed.
Lemma lem4018811 (b' : Prop) (b : Prop) : (term44 b' b) = (term44 b' b).
Proof. exact (eq_refl (term44 b' b)). Qed.
Lemma lem4018812 (a : Prop) (b' : Prop) (b : Prop) : ((term38 b' b a) = (term44 b' b)) = ((term36 b' a b) = (term44 b' b)).
Proof. exact (MK_COMB (@lem4018810 b' a b) (@lem4018811 b' b)). Qed.
Lemma lem4018813 (a : Prop) (b' : Prop) (b : Prop) : ((term38 b' b a) = (term43 b' b)) = ((term36 b' a b) = (term44 b' b)).
Proof. exact (TRANS (@lem4018807 a b' b) (@lem4018812 a b' b)). Qed.
Lemma lem4018814 (b' : Prop) (b : Prop) (a : Prop) (h1 : a = False) : (term36 b' a b) = (term44 b' b).
Proof. exact (EQ_MP (@lem4018813 a b' b) (@lem4018804 b' b a h1)). Qed.
Lemma lem4018815 (b' : Prop) (b : Prop) (a : Prop) (h1 : a = False) : (term44 b' b) = (term36 b' a b).
Proof. exact (SYM (@lem4018814 b' b a h1)). Qed.
Lemma lem4018819 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4018820 (b' : Prop) (b : Prop) : (term45 b' b) = (term46 b' b).
Proof. exact (@lem4018819 (term46 b' b)). Qed.
Lemma lem4018822 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4018823 (b' : Prop) (b : Prop) : (term46 b' b) = (b' = b).
Proof. exact (@lem4018822 (b' = b)). Qed.
Lemma lem4018826 (b' : Prop) (b : Prop) : (term45 b' b) = (b' = b).
Proof. exact (TRANS (@lem4018820 b' b) (@lem4018823 b' b)). Qed.
Lemma lem4018827 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4018828 (b' : Prop) (b : Prop) : (term47 b' b) = (term48 b' b).
Proof. exact (MK_COMB (@lem4018827) (@lem4018826 b' b)). Qed.
Lemma lem4018832 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4018833 (b : Prop) : (True /\ b) = b.
Proof. exact (@lem4018832 b). Qed.
Lemma lem4018834 (b' : Prop) : (@eq Prop b') = (@eq Prop b').
Proof. exact (eq_refl (@eq Prop b')). Qed.
Lemma lem4018835 (b' : Prop) (b : Prop) : (b' = (True /\ b)) = (b' = b).
Proof. exact (MK_COMB (@lem4018834 b') (@lem4018833 b)). Qed.
Lemma lem4018838 (b' : Prop) (b : Prop) : (term40 b' b) = (term49 b' b).
Proof. exact (MK_COMB (@lem4018828 b' b) (@lem4018835 b' b)). Qed.
Lemma lem4018842 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem4018843 (b' : Prop) (b : Prop) : (term49 b' b) = True.
Proof. exact (@lem4018842 (b' = b)). Qed.
Lemma lem4018844 (b' : Prop) (b : Prop) : (term40 b' b) = True.
Proof. exact (TRANS (@lem4018838 b' b) (@lem4018843 b' b)). Qed.
Lemma lem4018845 (b' : Prop) (b : Prop) : True = (term40 b' b).
Proof. exact (SYM (@lem4018844 b' b)). Qed.
Lemma lem4018846 (b' : Prop) (b : Prop) : term40 b' b.
Proof. exact (EQ_MP (@lem4018845 b' b) (@lem0)). Qed.
Lemma lem4018850 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4018851 (b' : Prop) (b : Prop) : (term50 b' b) = False.
Proof. exact (@lem4018850 (term51 b' b)). Qed.
Lemma lem4018852 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4018853 (b' : Prop) (b : Prop) : (term52 b' b) = (imp False).
Proof. exact (MK_COMB (@lem4018852) (@lem4018851 b' b)). Qed.
Lemma lem4018857 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4018858 (b : Prop) : (False /\ b) = False.
Proof. exact (@lem4018857 b). Qed.
Lemma lem4018859 (b' : Prop) : (@eq Prop b') = (@eq Prop b').
Proof. exact (eq_refl (@eq Prop b')). Qed.
Lemma lem4018860 (b : Prop) (b' : Prop) : (b' = (False /\ b)) = (b' = False).
Proof. exact (MK_COMB (@lem4018859 b') (@lem4018858 b)). Qed.
Lemma lem4018862 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4018863 (b' : Prop) : (b' = False) = (~ b').
Proof. exact (@lem4018862 b'). Qed.
Lemma lem4018864 (b : Prop) (b' : Prop) : (b' = (False /\ b)) = (~ b').
Proof. exact (TRANS (@lem4018860 b b') (@lem4018863 b')). Qed.
Lemma lem4018865 (b : Prop) (b' : Prop) : (term44 b' b) = (term53 b').
Proof. exact (MK_COMB (@lem4018853 b' b) (@lem4018864 b b')). Qed.
Lemma lem4018867 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4018868 (b' : Prop) : (term53 b') = True.
Proof. exact (@lem4018867 (~ b')). Qed.
Lemma lem4018869 (b' : Prop) (b : Prop) : (term44 b' b) = True.
Proof. exact (TRANS (@lem4018865 b b') (@lem4018868 b')). Qed.
Lemma lem4018870 (b' : Prop) (b : Prop) : True = (term44 b' b).
Proof. exact (SYM (@lem4018869 b' b)). Qed.
Lemma lem4018871 (b' : Prop) (b : Prop) : term44 b' b.
Proof. exact (EQ_MP (@lem4018870 b' b) (@lem0)). Qed.
Lemma lem4018872 (b' : Prop) (b : Prop) (a : Prop) (h1 : a = False) : term36 b' a b.
Proof. exact (EQ_MP (@lem4018815 b' b a h1) (@lem4018871 b' b)). Qed.
Lemma lem4018873 (b' : Prop) (b : Prop) (a : Prop) (h1 : a = True) : term36 b' a b.
Proof. exact (EQ_MP (@lem4018802 b' b a h1) (@lem4018846 b' b)). Qed.
Lemma lem4018875 (b' : Prop) (a : Prop) (b : Prop) : term36 b' a b.
Proof. exact (or_elim (@lem4018773 a) (fun h0 : a = True => @lem4018873 b' b a h0) (fun h0 : a = False => @lem4018872 b' b a h0)). Qed.
Lemma lem4018876 (b' : Prop) (a : Prop) (b : Prop) : term23 b' a b.
Proof. exact (EQ_MP (@lem4018770 b' a b) (@lem4018875 b' a b)). Qed.
Lemma lem4018882 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4018883 (a : Prop) : (False = a) = (~ a).
Proof. exact (@lem4018882 a). Qed.
Lemma lem4018884 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4018885 (a : Prop) : (term54 a) = (term55 a).
Proof. exact (MK_COMB (@lem4018884) (@lem4018883 a)). Qed.
Lemma lem4018890 (a : Prop) (b' : Prop) (b : Prop) : (term30 a b' b) = (term30 a b' b).
Proof. exact (eq_refl (term30 a b' b)). Qed.
Lemma lem4018891 (a : Prop) (b' : Prop) (b : Prop) : (term56 a b' b) = (term57 a b' b).
Proof. exact (MK_COMB (@lem4018885 a) (@lem4018890 a b' b)). Qed.
Lemma lem4018894 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4018895 (a : Prop) (b' : Prop) (b : Prop) : (term58 a b' b) = (term59 a b' b).
Proof. exact (MK_COMB (@lem4018894) (@lem4018891 a b' b)). Qed.
Lemma lem4018899 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4018900 (b' : Prop) : (False /\ b') = False.
Proof. exact (@lem4018899 b'). Qed.
Lemma lem4018901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4018902 (b' : Prop) : (term60 b') = (@eq Prop False).
Proof. exact (MK_COMB (@lem4018901) (@lem4018900 b')). Qed.
Lemma lem4018905 (a : Prop) (b : Prop) : (a /\ b) = (a /\ b).
Proof. exact (eq_refl (a /\ b)). Qed.
Lemma lem4018906 (b' : Prop) (a : Prop) (b : Prop) : ((False /\ b') = (a /\ b)) = (False = (a /\ b)).
Proof. exact (MK_COMB (@lem4018902 b') (@lem4018905 a b)). Qed.
Lemma lem4018908 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4018909 (a : Prop) (b : Prop) : (False = (a /\ b)) = (term61 a b).
Proof. exact (@lem4018908 (a /\ b)). Qed.
Lemma lem4018912 (b' : Prop) (a : Prop) (b : Prop) : ((False /\ b') = (a /\ b)) = (term61 a b).
Proof. exact (TRANS (@lem4018906 b' a b) (@lem4018909 a b)). Qed.
Lemma lem4018913 (b' : Prop) (a : Prop) (b : Prop) : (term28 b' a b) = (term62 b' a b).
Proof. exact (MK_COMB (@lem4018895 a b' b) (@lem4018912 b' a b)). Qed.
Lemma lem4018916 (b' : Prop) (a : Prop) (b : Prop) : (term62 b' a b) = (term28 b' a b).
Proof. exact (SYM (@lem4018913 b' a b)). Qed.
Lemma lem4018917 (a : Prop) : term18 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem4018918 (a : Prop) : (term18 a) = (term19 a).
Proof. exact (eq_refl (term18 a)). Qed.
Lemma lem4018919 (a : Prop) : term19 a.
Proof. exact (EQ_MP (@lem4018918 a) (@lem4018917 a)). Qed.
Lemma lem4018920 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem4018921 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem4018934 (b' : Prop) (b : Prop) : (term63 b' b) = (term63 b' b).
Proof. exact (eq_refl (term63 b' b)). Qed.
Lemma lem4018935 (b' : Prop) (b : Prop) (a : Prop) (h1 : a = True) : (term64 b' b a) = (term65 b' b).
Proof. exact (MK_COMB (@lem4018934 b' b) (@lem4018920 a h1)). Qed.
Lemma lem4018936 (b' : Prop) (b : Prop) : (term65 b' b) = (term66 b' b).
Proof. exact (eq_refl (term65 b' b)). Qed.
Lemma lem4018937 (b' : Prop) (b : Prop) (a : Prop) : (term67 b' b a) = (term67 b' b a).
Proof. exact (eq_refl (term67 b' b a)). Qed.
Lemma lem4018938 (a : Prop) (b' : Prop) (b : Prop) : ((term64 b' b a) = (term65 b' b)) = ((term64 b' b a) = (term66 b' b)).
Proof. exact (MK_COMB (@lem4018937 b' b a) (@lem4018936 b' b)). Qed.
Lemma lem4018939 (b' : Prop) (a : Prop) (b : Prop) : (term64 b' b a) = (term62 b' a b).
Proof. exact (eq_refl (term64 b' b a)). Qed.
Lemma lem4018940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4018941 (b' : Prop) (a : Prop) (b : Prop) : (term67 b' b a) = (term68 b' a b).
Proof. exact (MK_COMB (@lem4018940) (@lem4018939 b' a b)). Qed.
Lemma lem4018942 (b' : Prop) (b : Prop) : (term66 b' b) = (term66 b' b).
Proof. exact (eq_refl (term66 b' b)). Qed.
Lemma lem4018943 (a : Prop) (b' : Prop) (b : Prop) : ((term64 b' b a) = (term66 b' b)) = ((term62 b' a b) = (term66 b' b)).
Proof. exact (MK_COMB (@lem4018941 b' a b) (@lem4018942 b' b)). Qed.
Lemma lem4018944 (a : Prop) (b' : Prop) (b : Prop) : ((term64 b' b a) = (term65 b' b)) = ((term62 b' a b) = (term66 b' b)).
Proof. exact (TRANS (@lem4018938 a b' b) (@lem4018943 a b' b)). Qed.
Lemma lem4018945 (b' : Prop) (b : Prop) (a : Prop) (h1 : a = True) : (term62 b' a b) = (term66 b' b).
Proof. exact (EQ_MP (@lem4018944 a b' b) (@lem4018935 b' b a h1)). Qed.
Lemma lem4018946 (b' : Prop) (b : Prop) (a : Prop) (h1 : a = True) : (term66 b' b) = (term62 b' a b).
Proof. exact (SYM (@lem4018945 b' b a h1)). Qed.
Lemma lem4018947 (b' : Prop) (b : Prop) : (term63 b' b) = (term63 b' b).
Proof. exact (eq_refl (term63 b' b)). Qed.
Lemma lem4018948 (b' : Prop) (b : Prop) (a : Prop) (h1 : a = False) : (term64 b' b a) = (term69 b' b).
Proof. exact (MK_COMB (@lem4018947 b' b) (@lem4018921 a h1)). Qed.
Lemma lem4018949 (b' : Prop) (b : Prop) : (term69 b' b) = (term70 b' b).
Proof. exact (eq_refl (term69 b' b)). Qed.
Lemma lem4018950 (b' : Prop) (b : Prop) (a : Prop) : (term67 b' b a) = (term67 b' b a).
Proof. exact (eq_refl (term67 b' b a)). Qed.
Lemma lem4018951 (a : Prop) (b' : Prop) (b : Prop) : ((term64 b' b a) = (term69 b' b)) = ((term64 b' b a) = (term70 b' b)).
Proof. exact (MK_COMB (@lem4018950 b' b a) (@lem4018949 b' b)). Qed.
Lemma lem4018952 (b' : Prop) (a : Prop) (b : Prop) : (term64 b' b a) = (term62 b' a b).
Proof. exact (eq_refl (term64 b' b a)). Qed.
Lemma lem4018953 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4018954 (b' : Prop) (a : Prop) (b : Prop) : (term67 b' b a) = (term68 b' a b).
Proof. exact (MK_COMB (@lem4018953) (@lem4018952 b' a b)). Qed.
Lemma lem4018955 (b' : Prop) (b : Prop) : (term70 b' b) = (term70 b' b).
Proof. exact (eq_refl (term70 b' b)). Qed.
Lemma lem4018956 (a : Prop) (b' : Prop) (b : Prop) : ((term64 b' b a) = (term70 b' b)) = ((term62 b' a b) = (term70 b' b)).
Proof. exact (MK_COMB (@lem4018954 b' a b) (@lem4018955 b' b)). Qed.
Lemma lem4018957 (a : Prop) (b' : Prop) (b : Prop) : ((term64 b' b a) = (term69 b' b)) = ((term62 b' a b) = (term70 b' b)).
Proof. exact (TRANS (@lem4018951 a b' b) (@lem4018956 a b' b)). Qed.
Lemma lem4018958 (b' : Prop) (b : Prop) (a : Prop) (h1 : a = False) : (term62 b' a b) = (term70 b' b).
Proof. exact (EQ_MP (@lem4018957 a b' b) (@lem4018948 b' b a h1)). Qed.
Lemma lem4018959 (b' : Prop) (b : Prop) (a : Prop) (h1 : a = False) : (term70 b' b) = (term62 b' a b).
Proof. exact (SYM (@lem4018958 b' b a h1)). Qed.
Lemma lem4018965 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem4018966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4018967 : term71 = (and False).
Proof. exact (MK_COMB (@lem4018966) (@lem4018965)). Qed.
Lemma lem4018969 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4018970 (b' : Prop) (b : Prop) : (term46 b' b) = (b' = b).
Proof. exact (@lem4018969 (b' = b)). Qed.
Lemma lem4018973 (b' : Prop) (b : Prop) : (term72 b' b) = (term73 b' b).
Proof. exact (MK_COMB (@lem4018967) (@lem4018970 b' b)). Qed.
Lemma lem4018975 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4018976 (b' : Prop) (b : Prop) : (term73 b' b) = False.
Proof. exact (@lem4018975 (b' = b)). Qed.
Lemma lem4018977 (b' : Prop) (b : Prop) : (term72 b' b) = False.
Proof. exact (TRANS (@lem4018973 b' b) (@lem4018976 b' b)). Qed.
Lemma lem4018978 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4018979 (b' : Prop) (b : Prop) : (term74 b' b) = (imp False).
Proof. exact (MK_COMB (@lem4018978) (@lem4018977 b' b)). Qed.
Lemma lem4018981 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4018982 (b : Prop) : (True /\ b) = b.
Proof. exact (@lem4018981 b). Qed.
Lemma lem4018983 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4018984 (b : Prop) : (term75 b) = (~ b).
Proof. exact (MK_COMB (@lem4018983) (@lem4018982 b)). Qed.
Lemma lem4018985 (b' : Prop) (b : Prop) : (term66 b' b) = (term53 b).
Proof. exact (MK_COMB (@lem4018979 b' b) (@lem4018984 b)). Qed.
Lemma lem4018987 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4018988 (b : Prop) : (term53 b) = True.
Proof. exact (@lem4018987 (~ b)). Qed.
Lemma lem4018989 (b' : Prop) (b : Prop) : (term66 b' b) = True.
Proof. exact (TRANS (@lem4018985 b' b) (@lem4018988 b)). Qed.
Lemma lem4018990 (b' : Prop) (b : Prop) : True = (term66 b' b).
Proof. exact (SYM (@lem4018989 b' b)). Qed.
Lemma lem4018991 (b' : Prop) (b : Prop) : term66 b' b.
Proof. exact (EQ_MP (@lem4018990 b' b) (@lem0)). Qed.
Lemma lem4018997 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4018998 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4018999 : term76 = (and True).
Proof. exact (MK_COMB (@lem4018998) (@lem4018997)). Qed.
Lemma lem4019001 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4019002 (b' : Prop) (b : Prop) : (term51 b' b) = True.
Proof. exact (@lem4019001 (b' = b)). Qed.
Lemma lem4019003 (b' : Prop) (b : Prop) : (term77 b' b) = (True /\ True).
Proof. exact (MK_COMB (@lem4018999) (@lem4019002 b' b)). Qed.
Lemma lem4019005 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4019006 : (True /\ True) = True.
Proof. exact (@lem4019005 True). Qed.
Lemma lem4019007 (b' : Prop) (b : Prop) : (term77 b' b) = True.
Proof. exact (TRANS (@lem4019003 b' b) (@lem4019006)). Qed.
Lemma lem4019008 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4019009 (b' : Prop) (b : Prop) : (term78 b' b) = (imp True).
Proof. exact (MK_COMB (@lem4019008) (@lem4019007 b' b)). Qed.
Lemma lem4019011 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4019012 (b : Prop) : (False /\ b) = False.
Proof. exact (@lem4019011 b). Qed.
Lemma lem4019013 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4019014 (b : Prop) : (term79 b) = (~ False).
Proof. exact (MK_COMB (@lem4019013) (@lem4019012 b)). Qed.
Lemma lem4019016 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4019017 (b : Prop) : (term79 b) = True.
Proof. exact (TRANS (@lem4019014 b) (@lem4019016)). Qed.
Lemma lem4019018 (b' : Prop) (b : Prop) : (term70 b' b) = (True -> True).
Proof. exact (MK_COMB (@lem4019009 b' b) (@lem4019017 b)). Qed.
Lemma lem4019020 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4019021 : (True -> True) = True.
Proof. exact (@lem4019020 True). Qed.
Lemma lem4019022 (b' : Prop) (b : Prop) : (term70 b' b) = True.
Proof. exact (TRANS (@lem4019018 b' b) (@lem4019021)). Qed.
Lemma lem4019023 (b' : Prop) (b : Prop) : True = (term70 b' b).
Proof. exact (SYM (@lem4019022 b' b)). Qed.
Lemma lem4019024 (b' : Prop) (b : Prop) : term70 b' b.
Proof. exact (EQ_MP (@lem4019023 b' b) (@lem0)). Qed.
Lemma lem4019025 (b' : Prop) (b : Prop) (a : Prop) (h1 : a = False) : term62 b' a b.
Proof. exact (EQ_MP (@lem4018959 b' b a h1) (@lem4019024 b' b)). Qed.
Lemma lem4019026 (b' : Prop) (b : Prop) (a : Prop) (h1 : a = True) : term62 b' a b.
Proof. exact (EQ_MP (@lem4018946 b' b a h1) (@lem4018991 b' b)). Qed.
Lemma lem4019028 (b' : Prop) (a : Prop) (b : Prop) : term62 b' a b.
Proof. exact (or_elim (@lem4018919 a) (fun h0 : a = True => @lem4019026 b' b a h0) (fun h0 : a = False => @lem4019025 b' b a h0)). Qed.
Lemma lem4019029 (b' : Prop) (a : Prop) (b : Prop) : term28 b' a b.
Proof. exact (EQ_MP (@lem4018916 b' a b) (@lem4019028 b' a b)). Qed.
Lemma lem4019030 (b' : Prop) (a : Prop) (b : Prop) (a' : Prop) (h1 : a' = False) : term25 a' b' a b.
Proof. exact (EQ_MP (@lem4018734 b' a b a' h1) (@lem4019029 b' a b)). Qed.
Lemma lem4019031 (b' : Prop) (a : Prop) (b : Prop) (a' : Prop) (h1 : a' = True) : term25 a' b' a b.
Proof. exact (EQ_MP (@lem4018721 b' a b a' h1) (@lem4018876 b' a b)). Qed.
Lemma lem4019034 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) : term25 a' b' a b.
Proof. exact (or_elim (@lem4018688 a') (fun h0 : a' = True => @lem4019031 b' a b a' h0) (fun h0 : a' = False => @lem4019030 b' a b a' h0)). Qed.
Lemma lem4019035 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) (h1 : term25 a' b' a b) : term25 a' b' a b.
Proof. exact (h1). Qed.
Lemma lem4019036 (a' : Prop) (a : Prop) (b' : Prop) (b : Prop) (h1 : term80 a' a b' b) : term80 a' a b' b.
Proof. exact (h1). Qed.
Lemma lem4019037 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) (h1 : term80 a' a b' b) (h2 : term25 a' b' a b) : (a' /\ b') = (a /\ b).
Proof. exact (@lem4019035 a' b' a b h2 (@lem4019036 a' a b' b h1)). Qed.
Lemma lem4019038 (a' : Prop) (a : Prop) (b' : Prop) (b : Prop) (h1 : term80 a' a b' b) : term81 a' b' a b.
Proof. exact (fun h0 : term25 a' b' a b => @lem4019037 a' b' a b h1 h0). Qed.
Lemma lem4019039 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) (h1 : term25 a' b' a b) : term25 a' b' a b.
Proof. exact (h1). Qed.
Lemma lem4019040 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) (h1 : term80 a' a b' b) (h2 : term25 a' b' a b) : (a' /\ b') = (a /\ b).
Proof. exact (@lem4019038 a' a b' b h1 (@lem4019039 a' b' a b h2)). Qed.
Lemma lem4019041 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) (h1 : term25 a' b' a b) : term25 a' b' a b.
Proof. exact (fun h0 : term80 a' a b' b => @lem4019040 a' b' a b h0 h1). Qed.
Lemma lem4019042 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) : term82 a' b' a b.
Proof. exact (fun h0 : term25 a' b' a b => @lem4019041 a' b' a b h0). Qed.
Lemma lem4019044 {_100044 : Type'} (s : _100044 -> Prop) : term83 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem4019045 {_100044 : Type'} (s : _100044 -> Prop) : (term83 _100044 s) = (term84 _100044 s).
Proof. exact (eq_refl (term83 _100044 s)). Qed.
Lemma lem4019046 {_100044 : Type'} (s : _100044 -> Prop) : term84 _100044 s.
Proof. exact (EQ_MP (@lem4019045 _100044 s) (@lem4019044 _100044 s)). Qed.
Lemma lem4019047 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term85 _100044 s n.
Proof. exact (@lem4019046 _100044 s n). Qed.
Lemma lem4019048 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term85 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term86 _100044 s n)).
Proof. exact (eq_refl (term85 _100044 s n)). Qed.
Lemma lem4019050 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : term87 _101850 _101855 s f.
Proof. exact (h1). Qed.
Lemma lem4019054 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term86 _100044 s n).
Proof. exact (EQ_MP (@lem4019048 _100044 s n) (@lem4019047 _100044 s n)). Qed.
Lemma lem4019055 {_101850 : Type'} (s : _101850 -> Prop) (n : nat) : (@HAS_SIZE _101850 s n) = (term86 _101850 s n).
Proof. exact (@lem4019054 _101850 s n). Qed.
Lemma lem4019056 {_101850 _101855 : Type'} (f : _101855 -> _101850) (s : _101855 -> Prop) (n : nat) : (term88 _101850 _101855 f s n) = (term89 _101850 _101855 f s n).
Proof. exact (@lem4019055 _101850 (@IMAGE _101855 _101850 f s) n). Qed.
Lemma lem4019061 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4019062 {_101850 _101855 : Type'} (f : _101855 -> _101850) (s : _101855 -> Prop) (n : nat) : (term90 _101850 _101855 f s n) = (term91 _101850 _101855 f s n).
Proof. exact (MK_COMB (@lem4019061) (@lem4019056 _101850 _101855 f s n)). Qed.
Lemma lem4019064 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term86 _100044 s n).
Proof. exact (EQ_MP (@lem4019048 _100044 s n) (@lem4019047 _100044 s n)). Qed.
Lemma lem4019065 {_101855 : Type'} (s : _101855 -> Prop) (n : nat) : (@HAS_SIZE _101855 s n) = (term86 _101855 s n).
Proof. exact (@lem4019064 _101855 s n). Qed.
Lemma lem4019070 {_101850 _101855 : Type'} (f : _101855 -> _101850) (s : _101855 -> Prop) (n : nat) : ((term88 _101850 _101855 f s n) = (@HAS_SIZE _101855 s n)) = ((term89 _101850 _101855 f s n) = (term86 _101855 s n)).
Proof. exact (MK_COMB (@lem4019062 _101850 _101855 f s n) (@lem4019065 _101855 s n)). Qed.
Lemma lem4019073 {_101850 _101855 : Type'} (f : _101855 -> _101850) (s : _101855 -> Prop) (n : nat) : ((term89 _101850 _101855 f s n) = (term86 _101855 s n)) = ((term88 _101850 _101855 f s n) = (@HAS_SIZE _101855 s n)).
Proof. exact (SYM (@lem4019070 _101850 _101855 f s n)). Qed.
Lemma lem4019075 (a' : Prop) (b' : Prop) (a : Prop) (b : Prop) : term25 a' b' a b.
Proof. exact (@lem4019042 a' b' a b (@lem4019034 a' b' a b)). Qed.
Lemma lem4019076 {_101850 _101855 : Type'} (f : _101855 -> _101850) (s : _101855 -> Prop) (n : nat) : term92 _101850 _101855 f s n.
Proof. exact (@lem4019075 (term93 _101850 _101855 f s) ((term94 _101850 _101855 f s) = n) (@FINITE _101855 s) ((@CARD _101855 s) = n)). Qed.
Lemma lem4019078 {A B : Type'} (f : A -> B) (s : A -> Prop) : term13 A B f s.
Proof. exact (EQ_MP (@lem4018666 A B f s) (@lem4018665 A B f s)). Qed.
Lemma lem4019079 {_101850 _101855 : Type'} (f : _101855 -> _101850) (s : _101855 -> Prop) : term95 _101850 _101855 f s.
Proof. exact (@lem4019078 _101855 _101850 f s). Qed.
Lemma lem4019080 {_101855 : Type'} (s : _101855 -> Prop) (h1 : @FINITE _101855 s) : @FINITE _101855 s.
Proof. exact (h1). Qed.
Lemma lem4019081 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem4019082 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4019084 {A B : Type'} (f : A -> B) (s : A -> Prop) : term4 A B f s.
Proof. exact (EQ_MP (@lem4018643 A B f s) (@lem4018642 A B f s)). Qed.
Lemma lem4019085 {_101850 _101855 : Type'} (f : _101855 -> _101850) (s : _101855 -> Prop) : term96 _101850 _101855 f s.
Proof. exact (@lem4019084 _101855 _101850 f s). Qed.
Lemma lem4019086 {_101850 _101855 : Type'} (x : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : term97 _101850 _101855 s f x.
Proof. exact (@lem4019050 _101850 _101855 s f h1 x). Qed.
Lemma lem4019087 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (x : _101855) : (term97 _101850 _101855 s f x) = (term98 _101850 _101855 s f x).
Proof. exact (eq_refl (term97 _101850 _101855 s f x)). Qed.
Lemma lem4019088 {_101850 _101855 : Type'} (x : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : term98 _101850 _101855 s f x.
Proof. exact (EQ_MP (@lem4019087 _101850 _101855 s f x) (@lem4019086 _101850 _101855 x s f h1)). Qed.
Lemma lem4019089 {_101850 _101855 : Type'} (x : _101855) (y : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : term99 _101850 _101855 s f x y.
Proof. exact (@lem4019088 _101850 _101855 x s f h1 y). Qed.
Lemma lem4019090 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (x : _101855) (y : _101855) : (term99 _101850 _101855 s f x y) = (term100 _101850 _101855 s f x y).
Proof. exact (eq_refl (term99 _101850 _101855 s f x y)). Qed.
Lemma lem4019091 {_101850 _101855 : Type'} (x : _101855) (y : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : term100 _101850 _101855 s f x y.
Proof. exact (EQ_MP (@lem4019090 _101850 _101855 s f x y) (@lem4019089 _101850 _101855 x y s f h1)). Qed.
Lemma lem4019092 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (x : _101855) (y : _101855) : (term100 _101850 _101855 s f x y) = ((term100 _101850 _101855 s f x y) = True).
Proof. exact (@lem7 (term100 _101850 _101855 s f x y)). Qed.
Lemma lem4019103 {_101850 _101855 : Type'} (x : _101855) (y : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term100 _101850 _101855 s f x y) = True.
Proof. exact (EQ_MP (@lem4019092 _101850 _101855 s f x y) (@lem4019091 _101850 _101855 x y s f h1)). Qed.
Lemma lem4019104 {_101850 _101855 : Type'} (x : _101855) (y : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term100 _101850 _101855 s f x y) = True.
Proof. exact (@lem4019103 _101850 _101855 x y s f h1). Qed.
Lemma lem4019105 {_101850 _101855 : Type'} (x : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term101 _101850 _101855 s f x) = (term102 _101855).
Proof. exact (fun_ext (fun y : _101855 => @lem4019104 _101850 _101855 x y s f h1)). Qed.
Lemma lem4019106 {_101855 : Type'} : (@all _101855) = (@all _101855).
Proof. exact (eq_refl (@all _101855)). Qed.
Lemma lem4019107 {_101850 _101855 : Type'} (x : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term98 _101850 _101855 s f x) = (term103 _101855).
Proof. exact (MK_COMB (@lem4019106 _101855) (@lem4019105 _101850 _101855 x s f h1)). Qed.
Lemma lem4019109 {A : Type'} (t : Prop) : (term104 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4019110 {_101855 : Type'} (t : Prop) : (term104 _101855 t) = t.
Proof. exact (@lem4019109 _101855 t). Qed.
Lemma lem4019111 {_101855 : Type'} : (term103 _101855) = True.
Proof. exact (@lem4019110 _101855 True). Qed.
Lemma lem4019112 {_101850 _101855 : Type'} (x : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term98 _101850 _101855 s f x) = True.
Proof. exact (TRANS (@lem4019107 _101850 _101855 x s f h1) (@lem4019111 _101855)). Qed.
Lemma lem4019113 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term105 _101850 _101855 s f) = (term102 _101855).
Proof. exact (fun_ext (fun x : _101855 => @lem4019112 _101850 _101855 x s f h1)). Qed.
Lemma lem4019114 {_101855 : Type'} : (@all _101855) = (@all _101855).
Proof. exact (eq_refl (@all _101855)). Qed.
Lemma lem4019115 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term87 _101850 _101855 s f) = (term103 _101855).
Proof. exact (MK_COMB (@lem4019114 _101855) (@lem4019113 _101850 _101855 s f h1)). Qed.
Lemma lem4019117 {A : Type'} (t : Prop) : (term104 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4019118 {_101855 : Type'} (t : Prop) : (term104 _101855 t) = t.
Proof. exact (@lem4019117 _101855 t). Qed.
Lemma lem4019119 {_101855 : Type'} : (term103 _101855) = True.
Proof. exact (@lem4019118 _101855 True). Qed.
Lemma lem4019120 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term87 _101850 _101855 s f) = True.
Proof. exact (TRANS (@lem4019115 _101850 _101855 s f h1) (@lem4019119 _101855)). Qed.
Lemma lem4019121 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : True = (term87 _101850 _101855 s f).
Proof. exact (SYM (@lem4019120 _101850 _101855 s f h1)). Qed.
Lemma lem4019122 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : term87 _101850 _101855 s f.
Proof. exact (EQ_MP (@lem4019121 _101850 _101855 s f h1) (@lem0)). Qed.
Lemma lem4019123 {_101850 _101855 : Type'} (x : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : term97 _101850 _101855 s f x.
Proof. exact (@lem4019050 _101850 _101855 s f h1 x). Qed.
Lemma lem4019124 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (x : _101855) : (term97 _101850 _101855 s f x) = (term98 _101850 _101855 s f x).
Proof. exact (eq_refl (term97 _101850 _101855 s f x)). Qed.
Lemma lem4019125 {_101850 _101855 : Type'} (x : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : term98 _101850 _101855 s f x.
Proof. exact (EQ_MP (@lem4019124 _101850 _101855 s f x) (@lem4019123 _101850 _101855 x s f h1)). Qed.
Lemma lem4019126 {_101850 _101855 : Type'} (x : _101855) (y : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : term99 _101850 _101855 s f x y.
Proof. exact (@lem4019125 _101850 _101855 x s f h1 y). Qed.
Lemma lem4019127 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (x : _101855) (y : _101855) : (term99 _101850 _101855 s f x y) = (term100 _101850 _101855 s f x y).
Proof. exact (eq_refl (term99 _101850 _101855 s f x y)). Qed.
Lemma lem4019128 {_101850 _101855 : Type'} (x : _101855) (y : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : term100 _101850 _101855 s f x y.
Proof. exact (EQ_MP (@lem4019127 _101850 _101855 s f x y) (@lem4019126 _101850 _101855 x y s f h1)). Qed.
Lemma lem4019129 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (x : _101855) (y : _101855) : (term100 _101850 _101855 s f x y) = ((term100 _101850 _101855 s f x y) = True).
Proof. exact (@lem7 (term100 _101850 _101855 s f x y)). Qed.
Lemma lem4019131 {_101855 : Type'} (s : _101855 -> Prop) : (@FINITE _101855 s) = ((@FINITE _101855 s) = True).
Proof. exact (@lem7 (@FINITE _101855 s)). Qed.
Lemma lem4019144 {_101850 _101855 : Type'} (x : _101855) (y : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term100 _101850 _101855 s f x y) = True.
Proof. exact (EQ_MP (@lem4019129 _101850 _101855 s f x y) (@lem4019128 _101850 _101855 x y s f h1)). Qed.
Lemma lem4019145 {_101850 _101855 : Type'} (x : _101855) (y : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term100 _101850 _101855 s f x y) = True.
Proof. exact (@lem4019144 _101850 _101855 x y s f h1). Qed.
Lemma lem4019146 {_101850 _101855 : Type'} (x : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term101 _101850 _101855 s f x) = (term102 _101855).
Proof. exact (fun_ext (fun y : _101855 => @lem4019145 _101850 _101855 x y s f h1)). Qed.
Lemma lem4019147 {_101855 : Type'} : (@all _101855) = (@all _101855).
Proof. exact (eq_refl (@all _101855)). Qed.
Lemma lem4019148 {_101850 _101855 : Type'} (x : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term98 _101850 _101855 s f x) = (term103 _101855).
Proof. exact (MK_COMB (@lem4019147 _101855) (@lem4019146 _101850 _101855 x s f h1)). Qed.
Lemma lem4019150 {A : Type'} (t : Prop) : (term104 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4019151 {_101855 : Type'} (t : Prop) : (term104 _101855 t) = t.
Proof. exact (@lem4019150 _101855 t). Qed.
Lemma lem4019152 {_101855 : Type'} : (term103 _101855) = True.
Proof. exact (@lem4019151 _101855 True). Qed.
Lemma lem4019153 {_101850 _101855 : Type'} (x : _101855) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term98 _101850 _101855 s f x) = True.
Proof. exact (TRANS (@lem4019148 _101850 _101855 x s f h1) (@lem4019152 _101855)). Qed.
Lemma lem4019154 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term105 _101850 _101855 s f) = (term102 _101855).
Proof. exact (fun_ext (fun x : _101855 => @lem4019153 _101850 _101855 x s f h1)). Qed.
Lemma lem4019155 {_101855 : Type'} : (@all _101855) = (@all _101855).
Proof. exact (eq_refl (@all _101855)). Qed.
Lemma lem4019156 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term87 _101850 _101855 s f) = (term103 _101855).
Proof. exact (MK_COMB (@lem4019155 _101855) (@lem4019154 _101850 _101855 s f h1)). Qed.
Lemma lem4019158 {A : Type'} (t : Prop) : (term104 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4019159 {_101855 : Type'} (t : Prop) : (term104 _101855 t) = t.
Proof. exact (@lem4019158 _101855 t). Qed.
Lemma lem4019160 {_101855 : Type'} : (term103 _101855) = True.
Proof. exact (@lem4019159 _101855 True). Qed.
Lemma lem4019161 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term87 _101850 _101855 s f) = True.
Proof. exact (TRANS (@lem4019156 _101850 _101855 s f h1) (@lem4019160 _101855)). Qed.
Lemma lem4019162 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4019163 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term106 _101850 _101855 s f) = (and True).
Proof. exact (MK_COMB (@lem4019162) (@lem4019161 _101850 _101855 s f h1)). Qed.
Lemma lem4019165 {_101855 : Type'} (s : _101855 -> Prop) (h1 : @FINITE _101855 s) : (@FINITE _101855 s) = True.
Proof. exact (EQ_MP (@lem4019131 _101855 s) (@lem4019080 _101855 s h1)). Qed.
Lemma lem4019166 {_101850 _101855 : Type'} (f : _101855 -> _101850) (s : _101855 -> Prop) (h1 : term87 _101850 _101855 s f) (h2 : @FINITE _101855 s) : (term107 _101850 _101855 f s) = (True /\ True).
Proof. exact (MK_COMB (@lem4019163 _101850 _101855 s f h1) (@lem4019165 _101855 s h2)). Qed.
Lemma lem4019168 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4019169 : (True /\ True) = True.
Proof. exact (@lem4019168 True). Qed.
Lemma lem4019170 {_101850 _101855 : Type'} (f : _101855 -> _101850) (s : _101855 -> Prop) (h1 : term87 _101850 _101855 s f) (h2 : @FINITE _101855 s) : (term107 _101850 _101855 f s) = True.
Proof. exact (TRANS (@lem4019166 _101850 _101855 f s h1 h2) (@lem4019169)). Qed.
Lemma lem4019171 {_101850 _101855 : Type'} (f : _101855 -> _101850) (s : _101855 -> Prop) (h1 : term87 _101850 _101855 s f) (h2 : @FINITE _101855 s) : True = (term107 _101850 _101855 f s).
Proof. exact (SYM (@lem4019170 _101850 _101855 f s h1 h2)). Qed.
Lemma lem4019172 {_101850 _101855 : Type'} (f : _101855 -> _101850) (s : _101855 -> Prop) (h1 : term87 _101850 _101855 s f) (h2 : @FINITE _101855 s) : term107 _101850 _101855 f s.
Proof. exact (EQ_MP (@lem4019171 _101850 _101855 f s h1 h2) (@lem0)). Qed.
Lemma lem4019173 {_101850 _101855 : Type'} (f : _101855 -> _101850) (s : _101855 -> Prop) (h1 : term87 _101850 _101855 s f) (h2 : @FINITE _101855 s) : (term94 _101850 _101855 f s) = (@CARD _101855 s).
Proof. exact (@lem4019085 _101850 _101855 f s (@lem4019172 _101850 _101855 f s h1 h2)). Qed.
Lemma lem4019174 {_101850 _101855 : Type'} (f : _101855 -> _101850) (s : _101855 -> Prop) (h1 : term87 _101850 _101855 s f) (h2 : @FINITE _101855 s) : (term108 _101850 _101855 f s) = (term109 _101855 s).
Proof. exact (MK_COMB (@lem4019082) (@lem4019173 _101850 _101855 f s h1 h2)). Qed.
Lemma lem4019175 {_101850 _101855 : Type'} (n : nat) (f : _101855 -> _101850) (s : _101855 -> Prop) (h1 : term87 _101850 _101855 s f) (h2 : @FINITE _101855 s) : ((term94 _101850 _101855 f s) = n) = ((@CARD _101855 s) = n).
Proof. exact (MK_COMB (@lem4019174 _101850 _101855 f s h1 h2) (@lem4019081 n)). Qed.
Lemma lem4019176 {_101850 _101855 : Type'} (n : nat) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : term110 _101850 _101855 f s n.
Proof. exact (fun h0 : @FINITE _101855 s => @lem4019175 _101850 _101855 n f s h1 h0). Qed.
Lemma lem4019177 {_101850 _101855 : Type'} (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term93 _101850 _101855 f s) = (@FINITE _101855 s).
Proof. exact (@lem4019079 _101850 _101855 f s (@lem4019122 _101850 _101855 s f h1)). Qed.
Lemma lem4019178 {_101850 _101855 : Type'} (n : nat) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : term111 _101850 _101855 f s n.
Proof. exact (conj (@lem4019177 _101850 _101855 s f h1) (@lem4019176 _101850 _101855 n s f h1)). Qed.
Lemma lem4019179 {_101850 _101855 : Type'} (n : nat) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term89 _101850 _101855 f s n) = (term86 _101855 s n).
Proof. exact (@lem4019076 _101850 _101855 f s n (@lem4019178 _101850 _101855 n s f h1)). Qed.
Lemma lem4019180 {_101850 _101855 : Type'} (n : nat) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term88 _101850 _101855 f s n) = (@HAS_SIZE _101855 s n).
Proof. exact (EQ_MP (@lem4019073 _101850 _101855 f s n) (@lem4019179 _101850 _101855 n s f h1)). Qed.
Lemma lem4019181 {_101850 _101855 : Type'} (n : nat) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term87 _101850 _101855 s f) = ((term88 _101850 _101855 f s n) = (@HAS_SIZE _101855 s n)).
Proof. exact (prop_ext (fun h2 : term87 _101850 _101855 s f => @lem4019180 _101850 _101855 n s f h1) (fun h2 : (term88 _101850 _101855 f s n) = (@HAS_SIZE _101855 s n) => @lem4019050 _101850 _101855 s f h1)). Qed.
Lemma lem4019182 {_101850 _101855 : Type'} (n : nat) (s : _101855 -> Prop) (f : _101855 -> _101850) (h1 : term87 _101850 _101855 s f) : (term88 _101850 _101855 f s n) = (@HAS_SIZE _101855 s n).
Proof. exact (EQ_MP (@lem4019181 _101850 _101855 n s f h1) (@lem4019050 _101850 _101855 s f h1)). Qed.
Lemma lem4019183 {_101850 _101855 : Type'} (f : _101855 -> _101850) (s : _101855 -> Prop) (n : nat) : term112 _101850 _101855 f s n.
Proof. exact (fun h0 : term87 _101850 _101855 s f => @lem4019182 _101850 _101855 n s f h0). Qed.
Lemma lem4019188 {_101850 _101855 : Type'} (f : _101855 -> _101850) (s : _101855 -> Prop) : term113 _101850 _101855 f s.
Proof. exact (fun n : nat => @lem4019183 _101850 _101855 f s n). Qed.
Lemma lem4019193 {_101850 _101855 : Type'} (f : _101855 -> _101850) : term114 _101850 _101855 f.
Proof. exact (fun s : _101855 -> Prop => @lem4019188 _101850 _101855 f s). Qed.
Lemma lem4019198 {_101850 _101855 : Type'} : term115 _101850 _101855.
Proof. exact (fun f : _101855 -> _101850 => @lem4019193 _101850 _101855 f). Qed.
