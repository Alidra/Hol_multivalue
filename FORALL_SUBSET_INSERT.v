Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_SUBSET_INSERT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FORALL_SUBSET_UNION_spec.
Require Import UNION_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Lemma lem3247664 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3247665 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3247666 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3247665 t1) (@lem3247664 t1)). Qed.
Lemma lem3247667 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3247666 t1 t2). Qed.
Lemma lem3247668 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3247669 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3247668 t1 t2) (@lem3247667 t1 t2)). Qed.
Lemma lem3247670 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3247669 t1 t2 t3). Qed.
Lemma lem3247671 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3247672 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3247671 t1 t2 t3) (@lem3247670 t1 t2 t3)). Qed.
Lemma lem3247673 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3247672 t1 t2 t3)). Qed.
Lemma lem3247689 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3247690 {_85070 : Type'} (s : _85070 -> Prop) (t : _85070 -> Prop) : (@SUBSET _85070 s t) = (term7 _85070 s t).
Proof. exact (@lem3247689 _85070 s t). Qed.
Lemma lem3247691 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term8 _85070 s a) = (term9 _85070 s a).
Proof. exact (@lem3247690 _85070 s (@INSERT _85070 a (@EMPTY _85070))). Qed.
Lemma lem3247698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3247699 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term10 _85070 s a) = (term11 _85070 s a).
Proof. exact (MK_COMB (@lem3247698) (@lem3247691 _85070 s a)). Qed.
Lemma lem3247705 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term12 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3247706 {_85070 : Type'} (s : _85070 -> Prop) (t : _85070 -> Prop) : (s = t) = (term12 _85070 s t).
Proof. exact (@lem3247705 _85070 s t). Qed.
Lemma lem3247707 {_85070 : Type'} (s : _85070 -> Prop) : (s = (@EMPTY _85070)) = (term13 _85070 s).
Proof. exact (@lem3247706 _85070 s (@EMPTY _85070)). Qed.
Lemma lem3247716 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3247717 {_85070 : Type'} (s : _85070 -> Prop) : (term14 _85070 s) = (term15 _85070 s).
Proof. exact (MK_COMB (@lem3247716) (@lem3247707 _85070 s)). Qed.
Lemma lem3247721 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term12 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3247722 {_85070 : Type'} (s : _85070 -> Prop) (t : _85070 -> Prop) : (s = t) = (term12 _85070 s t).
Proof. exact (@lem3247721 _85070 s t). Qed.
Lemma lem3247723 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (s = (@INSERT _85070 a (@EMPTY _85070))) = (term16 _85070 s a).
Proof. exact (@lem3247722 _85070 s (@INSERT _85070 a (@EMPTY _85070))). Qed.
Lemma lem3247732 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term17 _85070 s a) = (term18 _85070 s a).
Proof. exact (MK_COMB (@lem3247717 _85070 s) (@lem3247723 _85070 s a)). Qed.
Lemma lem3247735 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : ((term8 _85070 s a) = (term17 _85070 s a)) = ((term9 _85070 s a) = (term18 _85070 s a)).
Proof. exact (MK_COMB (@lem3247699 _85070 s a) (@lem3247732 _85070 s a)). Qed.
Lemma lem3247740 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : ((term9 _85070 s a) = (term18 _85070 s a)) = ((term8 _85070 s a) = (term17 _85070 s a)).
Proof. exact (SYM (@lem3247735 _85070 s a)). Qed.
Lemma lem3247750 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3247751 {_85070 : Type'} (P : _85070 -> Prop) (x : _85070) : (@IN _85070 x P) = (P x).
Proof. exact (@lem3247750 _85070 P x). Qed.
Lemma lem3247752 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (@IN _85070 x s) = (s x).
Proof. exact (@lem3247751 _85070 s x). Qed.
Lemma lem3247753 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3247754 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term19 _85070 x s) = (term20 _85070 s x).
Proof. exact (MK_COMB (@lem3247753) (@lem3247752 _85070 s x)). Qed.
Lemma lem3247756 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term21 A x y s) = (term22 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3247757 {_85070 : Type'} (y : _85070) (x : _85070) (s : _85070 -> Prop) : (term21 _85070 x y s) = (term22 _85070 y x s).
Proof. exact (@lem3247756 _85070 y x s). Qed.
Lemma lem3247758 {_85070 : Type'} (a : _85070) (x : _85070) : (term23 _85070 x a) = (term24 _85070 a x).
Proof. exact (@lem3247757 _85070 a x (@EMPTY _85070)). Qed.
Lemma lem3247764 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3247765 {_85070 : Type'} (x : _85070) : (@IN _85070 x (@EMPTY _85070)) = False.
Proof. exact (@lem3247764 _85070 x). Qed.
Lemma lem3247766 {_85070 : Type'} (x : _85070) (a : _85070) : (term25 _85070 x a) = (term25 _85070 x a).
Proof. exact (eq_refl (term25 _85070 x a)). Qed.
Lemma lem3247767 {_85070 : Type'} (x : _85070) (a : _85070) : (term24 _85070 a x) = (term26 _85070 x a).
Proof. exact (MK_COMB (@lem3247766 _85070 x a) (@lem3247765 _85070 x)). Qed.
Lemma lem3247769 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3247770 {_85070 : Type'} (x : _85070) (a : _85070) : (term26 _85070 x a) = (x = a).
Proof. exact (@lem3247769 (x = a)). Qed.
Lemma lem3247773 {_85070 : Type'} (x : _85070) (a : _85070) : (term24 _85070 a x) = (x = a).
Proof. exact (TRANS (@lem3247767 _85070 x a) (@lem3247770 _85070 x a)). Qed.
Lemma lem3247774 {_85070 : Type'} (x : _85070) (a : _85070) : (term23 _85070 x a) = (x = a).
Proof. exact (TRANS (@lem3247758 _85070 a x) (@lem3247773 _85070 x a)). Qed.
Lemma lem3247775 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term27 _85070 s x a) = (term28 _85070 s x a).
Proof. exact (MK_COMB (@lem3247754 _85070 s x) (@lem3247774 _85070 x a)). Qed.
Lemma lem3247778 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term29 _85070 s a) = (term30 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3247775 _85070 s x a)). Qed.
Lemma lem3247779 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3247780 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term9 _85070 s a) = (term31 _85070 s a).
Proof. exact (MK_COMB (@lem3247779 _85070) (@lem3247778 _85070 s a)). Qed.
Lemma lem3247785 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3247786 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term11 _85070 s a) = (term32 _85070 s a).
Proof. exact (MK_COMB (@lem3247785) (@lem3247780 _85070 s a)). Qed.
Lemma lem3247796 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3247797 {_85070 : Type'} (P : _85070 -> Prop) (x : _85070) : (@IN _85070 x P) = (P x).
Proof. exact (@lem3247796 _85070 P x). Qed.
Lemma lem3247798 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (@IN _85070 x s) = (s x).
Proof. exact (@lem3247797 _85070 s x). Qed.
Lemma lem3247799 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3247800 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term33 _85070 x s) = (term34 _85070 s x).
Proof. exact (MK_COMB (@lem3247799) (@lem3247798 _85070 s x)). Qed.
Lemma lem3247802 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3247803 {_85070 : Type'} (x : _85070) : (@IN _85070 x (@EMPTY _85070)) = False.
Proof. exact (@lem3247802 _85070 x). Qed.
Lemma lem3247804 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : ((@IN _85070 x s) = (@IN _85070 x (@EMPTY _85070))) = ((s x) = False).
Proof. exact (MK_COMB (@lem3247800 _85070 s x) (@lem3247803 _85070 x)). Qed.
Lemma lem3247806 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3247807 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : ((s x) = False) = (term35 _85070 s x).
Proof. exact (@lem3247806 (s x)). Qed.
Lemma lem3247808 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : ((@IN _85070 x s) = (@IN _85070 x (@EMPTY _85070))) = (term35 _85070 s x).
Proof. exact (TRANS (@lem3247804 _85070 s x) (@lem3247807 _85070 s x)). Qed.
Lemma lem3247809 {_85070 : Type'} (s : _85070 -> Prop) : (term36 _85070 s) = (term37 _85070 s).
Proof. exact (fun_ext (fun x : _85070 => @lem3247808 _85070 s x)). Qed.
Lemma lem3247810 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3247811 {_85070 : Type'} (s : _85070 -> Prop) : (term13 _85070 s) = (term38 _85070 s).
Proof. exact (MK_COMB (@lem3247810 _85070) (@lem3247809 _85070 s)). Qed.
Lemma lem3247816 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3247817 {_85070 : Type'} (s : _85070 -> Prop) : (term15 _85070 s) = (term39 _85070 s).
Proof. exact (MK_COMB (@lem3247816) (@lem3247811 _85070 s)). Qed.
Lemma lem3247825 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3247826 {_85070 : Type'} (P : _85070 -> Prop) (x : _85070) : (@IN _85070 x P) = (P x).
Proof. exact (@lem3247825 _85070 P x). Qed.
Lemma lem3247827 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (@IN _85070 x s) = (s x).
Proof. exact (@lem3247826 _85070 s x). Qed.
Lemma lem3247828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3247829 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term33 _85070 x s) = (term34 _85070 s x).
Proof. exact (MK_COMB (@lem3247828) (@lem3247827 _85070 s x)). Qed.
Lemma lem3247831 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term21 A x y s) = (term22 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3247832 {_85070 : Type'} (y : _85070) (x : _85070) (s : _85070 -> Prop) : (term21 _85070 x y s) = (term22 _85070 y x s).
Proof. exact (@lem3247831 _85070 y x s). Qed.
Lemma lem3247833 {_85070 : Type'} (a : _85070) (x : _85070) : (term23 _85070 x a) = (term24 _85070 a x).
Proof. exact (@lem3247832 _85070 a x (@EMPTY _85070)). Qed.
Lemma lem3247839 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3247840 {_85070 : Type'} (x : _85070) : (@IN _85070 x (@EMPTY _85070)) = False.
Proof. exact (@lem3247839 _85070 x). Qed.
Lemma lem3247841 {_85070 : Type'} (x : _85070) (a : _85070) : (term25 _85070 x a) = (term25 _85070 x a).
Proof. exact (eq_refl (term25 _85070 x a)). Qed.
Lemma lem3247842 {_85070 : Type'} (x : _85070) (a : _85070) : (term24 _85070 a x) = (term26 _85070 x a).
Proof. exact (MK_COMB (@lem3247841 _85070 x a) (@lem3247840 _85070 x)). Qed.
Lemma lem3247844 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3247845 {_85070 : Type'} (x : _85070) (a : _85070) : (term26 _85070 x a) = (x = a).
Proof. exact (@lem3247844 (x = a)). Qed.
Lemma lem3247848 {_85070 : Type'} (x : _85070) (a : _85070) : (term24 _85070 a x) = (x = a).
Proof. exact (TRANS (@lem3247842 _85070 x a) (@lem3247845 _85070 x a)). Qed.
Lemma lem3247849 {_85070 : Type'} (x : _85070) (a : _85070) : (term23 _85070 x a) = (x = a).
Proof. exact (TRANS (@lem3247833 _85070 a x) (@lem3247848 _85070 x a)). Qed.
Lemma lem3247850 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : ((@IN _85070 x s) = (term23 _85070 x a)) = ((s x) = (x = a)).
Proof. exact (MK_COMB (@lem3247829 _85070 s x) (@lem3247849 _85070 x a)). Qed.
Lemma lem3247853 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term40 _85070 s a) = (term41 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3247850 _85070 s x a)). Qed.
Lemma lem3247854 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3247855 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term16 _85070 s a) = (term42 _85070 s a).
Proof. exact (MK_COMB (@lem3247854 _85070) (@lem3247853 _85070 s a)). Qed.
Lemma lem3247860 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term18 _85070 s a) = (term43 _85070 s a).
Proof. exact (MK_COMB (@lem3247817 _85070 s) (@lem3247855 _85070 s a)). Qed.
Lemma lem3247863 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : ((term9 _85070 s a) = (term18 _85070 s a)) = ((term31 _85070 s a) = (term43 _85070 s a)).
Proof. exact (MK_COMB (@lem3247786 _85070 s a) (@lem3247860 _85070 s a)). Qed.
Lemma lem3247866 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : ((term31 _85070 s a) = (term43 _85070 s a)) = ((term9 _85070 s a) = (term18 _85070 s a)).
Proof. exact (SYM (@lem3247863 _85070 s a)). Qed.
Lemma lem3247868 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3247869 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : ((term31 _85070 s a) = (term43 _85070 s a)) = (term45 _85070 s a).
Proof. exact (@lem3247868 ((term31 _85070 s a) = (term43 _85070 s a))). Qed.
Lemma lem3247870 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term45 _85070 s a) = ((term31 _85070 s a) = (term43 _85070 s a)).
Proof. exact (SYM (@lem3247869 _85070 s a)). Qed.
Lemma lem3247871 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term46 _85070 s a) : term46 _85070 s a.
Proof. exact (h1). Qed.
Lemma lem3247874 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term45 _85070 s a) : term45 _85070 s a.
Proof. exact (h1). Qed.
Lemma lem3247875 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : term47 _85070 s a.
Proof. exact (fun h0 : term45 _85070 s a => @lem3247874 _85070 s a h0). Qed.
Lemma lem3247876 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term47 _85070 s a) : term47 _85070 s a.
Proof. exact (h1). Qed.
Lemma lem3247877 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term45 _85070 s a) : term45 _85070 s a.
Proof. exact (h1). Qed.
Lemma lem3247878 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term45 _85070 s a) (h2 : term47 _85070 s a) : term45 _85070 s a.
Proof. exact (@lem3247876 _85070 s a h2 (@lem3247877 _85070 s a h1)). Qed.
Lemma lem3247879 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term45 _85070 s a) : term48 _85070 s a.
Proof. exact (fun h0 : term47 _85070 s a => @lem3247878 _85070 s a h1 h0). Qed.
Lemma lem3247880 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term47 _85070 s a) : term47 _85070 s a.
Proof. exact (h1). Qed.
Lemma lem3247881 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term45 _85070 s a) (h2 : term47 _85070 s a) : term45 _85070 s a.
Proof. exact (@lem3247879 _85070 s a h1 (@lem3247880 _85070 s a h2)). Qed.
Lemma lem3247882 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term47 _85070 s a) : term47 _85070 s a.
Proof. exact (fun h0 : term45 _85070 s a => @lem3247881 _85070 s a h0 h1). Qed.
Lemma lem3247883 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : term49 _85070 s a.
Proof. exact (fun h0 : term47 _85070 s a => @lem3247882 _85070 s a h0). Qed.
Lemma lem3247886 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : term47 _85070 s a.
Proof. exact (@lem3247883 _85070 s a (@lem3247875 _85070 s a)). Qed.
Lemma lem3247887 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : term47 _85070 s a.
Proof. exact (@lem3247886 _85070 s a). Qed.
Lemma lem3247897 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3247898 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term45 _85070 s a) = (term50 _85070 s a).
Proof. exact (@lem3247897 (term46 _85070 s a)). Qed.
Lemma lem3247900 (t : Prop) : (term51 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3247901 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term50 _85070 s a) = ((term31 _85070 s a) = (term43 _85070 s a)).
Proof. exact (@lem3247900 ((term31 _85070 s a) = (term43 _85070 s a))). Qed.
Lemma lem3247902 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term45 _85070 s a) = ((term31 _85070 s a) = (term43 _85070 s a)).
Proof. exact (TRANS (@lem3247898 _85070 s a) (@lem3247901 _85070 s a)). Qed.
Lemma lem3247919 {_85070 : Type'} (a : _85070) : (term52 _85070 a) = (term53 _85070 a).
Proof. exact (fun_ext (fun s : _85070 -> Prop => @lem3247902 _85070 s a)). Qed.
Lemma lem3247920 {_85070 : Type'} : (@all (_85070 -> Prop)) = (@all (_85070 -> Prop)).
Proof. exact (eq_refl (@all (_85070 -> Prop))). Qed.
Lemma lem3247921 {_85070 : Type'} (a : _85070) : (term54 _85070 a) = (term55 _85070 a).
Proof. exact (MK_COMB (@lem3247920 _85070) (@lem3247919 _85070 a)). Qed.
Lemma lem3247926 {_85070 : Type'} : (term56 _85070) = (term57 _85070).
Proof. exact (fun_ext (fun a : _85070 => @lem3247921 _85070 a)). Qed.
Lemma lem3247927 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3247936 {_85070 : Type'} : (term58 _85070) = (term59 _85070).
Proof. exact (MK_COMB (@lem3247927 _85070) (@lem3247926 _85070)). Qed.
Lemma lem3247941 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : ((s x) = (x = a)) = ((s x) = (x = a)).
Proof. exact (eq_refl ((s x) = (x = a))). Qed.
Lemma lem3247942 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term41 _85070 s a) = (term41 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3247941 _85070 s x a)). Qed.
Lemma lem3247943 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3247944 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term42 _85070 s a) = (term42 _85070 s a).
Proof. exact (MK_COMB (@lem3247943 _85070) (@lem3247942 _85070 s a)). Qed.
Lemma lem3247947 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term35 _85070 s x) = (term35 _85070 s x).
Proof. exact (eq_refl (term35 _85070 s x)). Qed.
Lemma lem3247948 {_85070 : Type'} (s : _85070 -> Prop) : (term37 _85070 s) = (term37 _85070 s).
Proof. exact (fun_ext (fun x : _85070 => @lem3247947 _85070 s x)). Qed.
Lemma lem3247949 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3247950 {_85070 : Type'} (s : _85070 -> Prop) : (term38 _85070 s) = (term38 _85070 s).
Proof. exact (MK_COMB (@lem3247949 _85070) (@lem3247948 _85070 s)). Qed.
Lemma lem3247951 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3247952 {_85070 : Type'} (s : _85070 -> Prop) : (term39 _85070 s) = (term39 _85070 s).
Proof. exact (MK_COMB (@lem3247951) (@lem3247950 _85070 s)). Qed.
Lemma lem3247953 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term43 _85070 s a) = (term43 _85070 s a).
Proof. exact (MK_COMB (@lem3247952 _85070 s) (@lem3247944 _85070 s a)). Qed.
Lemma lem3247958 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term28 _85070 s x a) = (term28 _85070 s x a).
Proof. exact (eq_refl (term28 _85070 s x a)). Qed.
Lemma lem3247959 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term30 _85070 s a) = (term30 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3247958 _85070 s x a)). Qed.
Lemma lem3247960 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3247961 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term31 _85070 s a) = (term31 _85070 s a).
Proof. exact (MK_COMB (@lem3247960 _85070) (@lem3247959 _85070 s a)). Qed.
Lemma lem3247962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3247963 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term32 _85070 s a) = (term32 _85070 s a).
Proof. exact (MK_COMB (@lem3247962) (@lem3247961 _85070 s a)). Qed.
Lemma lem3247964 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : ((term31 _85070 s a) = (term43 _85070 s a)) = ((term31 _85070 s a) = (term43 _85070 s a)).
Proof. exact (MK_COMB (@lem3247963 _85070 s a) (@lem3247953 _85070 s a)). Qed.
Lemma lem3247965 {_85070 : Type'} (a : _85070) : (term53 _85070 a) = (term53 _85070 a).
Proof. exact (fun_ext (fun s : _85070 -> Prop => @lem3247964 _85070 s a)). Qed.
Lemma lem3247966 {_85070 : Type'} : (@all (_85070 -> Prop)) = (@all (_85070 -> Prop)).
Proof. exact (eq_refl (@all (_85070 -> Prop))). Qed.
Lemma lem3247967 {_85070 : Type'} (a : _85070) : (term55 _85070 a) = (term55 _85070 a).
Proof. exact (MK_COMB (@lem3247966 _85070) (@lem3247965 _85070 a)). Qed.
Lemma lem3247968 {_85070 : Type'} : (term57 _85070) = (term57 _85070).
Proof. exact (fun_ext (fun a : _85070 => @lem3247967 _85070 a)). Qed.
Lemma lem3247969 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3247970 {_85070 : Type'} : (term59 _85070) = (term59 _85070).
Proof. exact (MK_COMB (@lem3247969 _85070) (@lem3247968 _85070)). Qed.
Lemma lem3248007 {_85070 : Type'} : (term58 _85070) = (term59 _85070).
Proof. exact (TRANS (@lem3247936 _85070) (@lem3247970 _85070)). Qed.
Lemma lem3248008 {_85070 : Type'} : (term59 _85070) = (term58 _85070).
Proof. exact (SYM (@lem3248007 _85070)). Qed.
Lemma lem3248010 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3248011 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : ((term31 _85070 s a) = (term43 _85070 s a)) = (term45 _85070 s a).
Proof. exact (@lem3248010 ((term31 _85070 s a) = (term43 _85070 s a))). Qed.
Lemma lem3248012 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term45 _85070 s a) = ((term31 _85070 s a) = (term43 _85070 s a)).
Proof. exact (SYM (@lem3248011 _85070 s a)). Qed.
Lemma lem3248013 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term46 _85070 s a) : term46 _85070 s a.
Proof. exact (h1). Qed.
Lemma lem3248022 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term60 _85070 s x a) = (term61 _85070 s x a).
Proof. exact (@lem17362 (s x) (x = a)). Qed.
Lemma lem3248027 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term28 _85070 s x a) = (term62 _85070 s x a).
Proof. exact (@lem17265 (s x) (x = a)). Qed.
Lemma lem3248028 {_85070 : Type'} (P : _85070 -> Prop) : (term63 _85070 P) = (term64 _85070 P).
Proof. exact (@lem18392 _85070 P). Qed.
Lemma lem3248029 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term65 _85070 s a) = (term66 _85070 s a).
Proof. exact (@lem3248028 _85070 (term30 _85070 s a)). Qed.
Lemma lem3248030 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term67 _85070 s a x) = (term28 _85070 s x a).
Proof. exact (eq_refl (term67 _85070 s a x)). Qed.
Lemma lem3248031 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3248032 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term68 _85070 s a x) = (term60 _85070 s x a).
Proof. exact (MK_COMB (@lem3248031) (@lem3248030 _85070 s x a)). Qed.
Lemma lem3248033 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term68 _85070 s a x) = (term61 _85070 s x a).
Proof. exact (TRANS (@lem3248032 _85070 s x a) (@lem3248022 _85070 s x a)). Qed.
Lemma lem3248034 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term69 _85070 s a) = (term70 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248033 _85070 s x a)). Qed.
Lemma lem3248035 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248036 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term66 _85070 s a) = (term71 _85070 s a).
Proof. exact (MK_COMB (@lem3248035 _85070) (@lem3248034 _85070 s a)). Qed.
Lemma lem3248037 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term65 _85070 s a) = (term71 _85070 s a).
Proof. exact (TRANS (@lem3248029 _85070 s a) (@lem3248036 _85070 s a)). Qed.
Lemma lem3248038 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term30 _85070 s a) = (term72 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248027 _85070 s x a)). Qed.
Lemma lem3248039 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3248040 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term31 _85070 s a) = (term73 _85070 s a).
Proof. exact (MK_COMB (@lem3248039 _85070) (@lem3248038 _85070 s a)). Qed.
Lemma lem3248041 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term35 _85070 s x) = (term35 _85070 s x).
Proof. exact (eq_refl (term35 _85070 s x)). Qed.
Lemma lem3248044 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term74 _85070 s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem3248045 {_85070 : Type'} (P : _85070 -> Prop) : (term63 _85070 P) = (term64 _85070 P).
Proof. exact (@lem18392 _85070 P). Qed.
Lemma lem3248046 {_85070 : Type'} (s : _85070 -> Prop) : (term75 _85070 s) = (term76 _85070 s).
Proof. exact (@lem3248045 _85070 (term37 _85070 s)). Qed.
Lemma lem3248047 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term77 _85070 s x) = (term35 _85070 s x).
Proof. exact (eq_refl (term77 _85070 s x)). Qed.
Lemma lem3248048 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3248049 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term78 _85070 s x) = (term74 _85070 s x).
Proof. exact (MK_COMB (@lem3248048) (@lem3248047 _85070 s x)). Qed.
Lemma lem3248050 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term78 _85070 s x) = (s x).
Proof. exact (TRANS (@lem3248049 _85070 s x) (@lem3248044 _85070 s x)). Qed.
Lemma lem3248051 {_85070 : Type'} (s : _85070 -> Prop) : (term79 _85070 s) = (term80 _85070 s).
Proof. exact (fun_ext (fun x : _85070 => @lem3248050 _85070 s x)). Qed.
Lemma lem3248052 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248053 {_85070 : Type'} (s : _85070 -> Prop) : (term76 _85070 s) = (term81 _85070 s).
Proof. exact (MK_COMB (@lem3248052 _85070) (@lem3248051 _85070 s)). Qed.
Lemma lem3248054 {_85070 : Type'} (s : _85070 -> Prop) : (term75 _85070 s) = (term81 _85070 s).
Proof. exact (TRANS (@lem3248046 _85070 s) (@lem3248053 _85070 s)). Qed.
Lemma lem3248055 {_85070 : Type'} (s : _85070 -> Prop) : (term37 _85070 s) = (term37 _85070 s).
Proof. exact (fun_ext (fun x : _85070 => @lem3248041 _85070 s x)). Qed.
Lemma lem3248056 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3248057 {_85070 : Type'} (s : _85070 -> Prop) : (term38 _85070 s) = (term38 _85070 s).
Proof. exact (MK_COMB (@lem3248056 _85070) (@lem3248055 _85070 s)). Qed.
Lemma lem3248072 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term82 _85070 s x a) = (term83 _85070 s x a).
Proof. exact (@lem17930 (s x) (x = a)). Qed.
Lemma lem3248083 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : ((s x) = (x = a)) = (term84 _85070 s x a).
Proof. exact (@lem17784 (s x) (x = a)). Qed.
Lemma lem3248084 {_85070 : Type'} (P : _85070 -> Prop) : (term63 _85070 P) = (term64 _85070 P).
Proof. exact (@lem18392 _85070 P). Qed.
Lemma lem3248085 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term85 _85070 s a) = (term86 _85070 s a).
Proof. exact (@lem3248084 _85070 (term41 _85070 s a)). Qed.
Lemma lem3248086 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term87 _85070 s a x) = ((s x) = (x = a)).
Proof. exact (eq_refl (term87 _85070 s a x)). Qed.
Lemma lem3248087 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3248088 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term88 _85070 s a x) = (term82 _85070 s x a).
Proof. exact (MK_COMB (@lem3248087) (@lem3248086 _85070 s x a)). Qed.
Lemma lem3248089 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term88 _85070 s a x) = (term83 _85070 s x a).
Proof. exact (TRANS (@lem3248088 _85070 s x a) (@lem3248072 _85070 s x a)). Qed.
Lemma lem3248090 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term89 _85070 s a) = (term90 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248089 _85070 s x a)). Qed.
Lemma lem3248091 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248092 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term86 _85070 s a) = (term91 _85070 s a).
Proof. exact (MK_COMB (@lem3248091 _85070) (@lem3248090 _85070 s a)). Qed.
Lemma lem3248093 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term85 _85070 s a) = (term91 _85070 s a).
Proof. exact (TRANS (@lem3248085 _85070 s a) (@lem3248092 _85070 s a)). Qed.
Lemma lem3248094 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term41 _85070 s a) = (term92 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248083 _85070 s x a)). Qed.
Lemma lem3248095 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3248096 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term42 _85070 s a) = (term93 _85070 s a).
Proof. exact (MK_COMB (@lem3248095 _85070) (@lem3248094 _85070 s a)). Qed.
Lemma lem3248097 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3248098 {_85070 : Type'} (s : _85070 -> Prop) : (term94 _85070 s) = (term95 _85070 s).
Proof. exact (MK_COMB (@lem3248097) (@lem3248054 _85070 s)). Qed.
Lemma lem3248099 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term96 _85070 s a) = (term97 _85070 s a).
Proof. exact (MK_COMB (@lem3248098 _85070 s) (@lem3248093 _85070 s a)). Qed.
Lemma lem3248100 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term98 _85070 s a) = (term96 _85070 s a).
Proof. exact (@lem17160 (term38 _85070 s) (term42 _85070 s a)). Qed.
Lemma lem3248101 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term98 _85070 s a) = (term97 _85070 s a).
Proof. exact (TRANS (@lem3248100 _85070 s a) (@lem3248099 _85070 s a)). Qed.
Lemma lem3248102 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3248103 {_85070 : Type'} (s : _85070 -> Prop) : (term39 _85070 s) = (term39 _85070 s).
Proof. exact (MK_COMB (@lem3248102) (@lem3248057 _85070 s)). Qed.
Lemma lem3248104 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term43 _85070 s a) = (term99 _85070 s a).
Proof. exact (MK_COMB (@lem3248103 _85070 s) (@lem3248096 _85070 s a)). Qed.
Lemma lem3248105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3248106 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term100 _85070 s a) = (term101 _85070 s a).
Proof. exact (MK_COMB (@lem3248105) (@lem3248037 _85070 s a)). Qed.
Lemma lem3248107 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term102 _85070 s a) = (term103 _85070 s a).
Proof. exact (MK_COMB (@lem3248106 _85070 s a) (@lem3248104 _85070 s a)). Qed.
Lemma lem3248108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3248109 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term104 _85070 s a) = (term105 _85070 s a).
Proof. exact (MK_COMB (@lem3248108) (@lem3248040 _85070 s a)). Qed.
Lemma lem3248110 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term106 _85070 s a) = (term107 _85070 s a).
Proof. exact (MK_COMB (@lem3248109 _85070 s a) (@lem3248101 _85070 s a)). Qed.
Lemma lem3248111 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3248112 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term108 _85070 s a) = (term109 _85070 s a).
Proof. exact (MK_COMB (@lem3248111) (@lem3248110 _85070 s a)). Qed.
Lemma lem3248113 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term110 _85070 s a) = (term111 _85070 s a).
Proof. exact (MK_COMB (@lem3248112 _85070 s a) (@lem3248107 _85070 s a)). Qed.
Lemma lem3248114 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term46 _85070 s a) = (term110 _85070 s a).
Proof. exact (@lem17646 (term31 _85070 s a) (term43 _85070 s a)). Qed.
Lemma lem3248115 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term46 _85070 s a) = (term111 _85070 s a).
Proof. exact (TRANS (@lem3248114 _85070 s a) (@lem3248113 _85070 s a)). Qed.
Lemma lem3248249 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3248250 {_85070 : Type'} (P : _85070 -> Prop) (Q : _85070 -> Prop) : (term112 _85070 P Q) = (term113 _85070 P Q).
Proof. exact (@lem3248249 _85070 P Q). Qed.
Lemma lem3248251 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term114 _85070 s a) = (term115 _85070 s a).
Proof. exact (@lem3248250 _85070 (term116 _85070 s a) (term72 _85070 s a)). Qed.
Lemma lem3248252 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term117 _85070 s a x) = (term118 _85070 s x a).
Proof. exact (eq_refl (term117 _85070 s a x)). Qed.
Lemma lem3248253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3248254 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term119 _85070 s a x) = (term120 _85070 s x a).
Proof. exact (MK_COMB (@lem3248253) (@lem3248252 _85070 s x a)). Qed.
Lemma lem3248255 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term121 _85070 s a x) = (term62 _85070 s x a).
Proof. exact (eq_refl (term121 _85070 s a x)). Qed.
Lemma lem3248256 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term122 _85070 s a x) = (term84 _85070 s x a).
Proof. exact (MK_COMB (@lem3248254 _85070 s x a) (@lem3248255 _85070 s x a)). Qed.
Lemma lem3248257 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term123 _85070 s a) = (term92 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248256 _85070 s x a)). Qed.
Lemma lem3248258 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3248259 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term114 _85070 s a) = (term93 _85070 s a).
Proof. exact (MK_COMB (@lem3248258 _85070) (@lem3248257 _85070 s a)). Qed.
Lemma lem3248260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3248261 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term124 _85070 s a) = (term125 _85070 s a).
Proof. exact (MK_COMB (@lem3248260) (@lem3248259 _85070 s a)). Qed.
Lemma lem3248262 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term117 _85070 s a x) = (term118 _85070 s x a).
Proof. exact (eq_refl (term117 _85070 s a x)). Qed.
Lemma lem3248263 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term126 _85070 s a) = (term116 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248262 _85070 s x a)). Qed.
Lemma lem3248264 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3248265 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term127 _85070 s a) = (term128 _85070 s a).
Proof. exact (MK_COMB (@lem3248264 _85070) (@lem3248263 _85070 s a)). Qed.
Lemma lem3248266 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3248267 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term129 _85070 s a) = (term130 _85070 s a).
Proof. exact (MK_COMB (@lem3248266) (@lem3248265 _85070 s a)). Qed.
Lemma lem3248268 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term121 _85070 s a x) = (term62 _85070 s x a).
Proof. exact (eq_refl (term121 _85070 s a x)). Qed.
Lemma lem3248269 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term131 _85070 s a) = (term72 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248268 _85070 s x a)). Qed.
Lemma lem3248270 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3248271 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term132 _85070 s a) = (term73 _85070 s a).
Proof. exact (MK_COMB (@lem3248270 _85070) (@lem3248269 _85070 s a)). Qed.
Lemma lem3248272 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term115 _85070 s a) = (term133 _85070 s a).
Proof. exact (MK_COMB (@lem3248267 _85070 s a) (@lem3248271 _85070 s a)). Qed.
Lemma lem3248273 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : ((term114 _85070 s a) = (term115 _85070 s a)) = ((term93 _85070 s a) = (term133 _85070 s a)).
Proof. exact (MK_COMB (@lem3248261 _85070 s a) (@lem3248272 _85070 s a)). Qed.
Lemma lem3248274 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term93 _85070 s a) = (term133 _85070 s a).
Proof. exact (EQ_MP (@lem3248273 _85070 s a) (@lem3248251 _85070 s a)). Qed.
Lemma lem3248351 {_85070 : Type'} (s : _85070 -> Prop) : (term39 _85070 s) = (term39 _85070 s).
Proof. exact (eq_refl (term39 _85070 s)). Qed.
Lemma lem3248352 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term99 _85070 s a) = (term134 _85070 s a).
Proof. exact (MK_COMB (@lem3248351 _85070 s) (@lem3248274 _85070 s a)). Qed.
Lemma lem3248353 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term101 _85070 s a) = (term101 _85070 s a).
Proof. exact (eq_refl (term101 _85070 s a)). Qed.
Lemma lem3248354 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term103 _85070 s a) = (term135 _85070 s a).
Proof. exact (MK_COMB (@lem3248353 _85070 s a) (@lem3248352 _85070 s a)). Qed.
Lemma lem3248355 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term109 _85070 s a) = (term109 _85070 s a).
Proof. exact (eq_refl (term109 _85070 s a)). Qed.
Lemma lem3248356 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term111 _85070 s a) = (term136 _85070 s a).
Proof. exact (MK_COMB (@lem3248355 _85070 s a) (@lem3248354 _85070 s a)). Qed.
Lemma lem3248358 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3248359 {_85070 : Type'} (P : _85070 -> Prop) (Q : Prop) : (term137 _85070 P Q) = (term138 _85070 P Q).
Proof. exact (@lem3248358 _85070 P Q). Qed.
Lemma lem3248360 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term97 _85070 s a) = (term139 _85070 s a).
Proof. exact (@lem3248359 _85070 s (term91 _85070 s a)). Qed.
Lemma lem3248362 {A : Type'} (P : Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3248363 {_85070 : Type'} (P : Prop) (Q : _85070 -> Prop) : (term140 _85070 P Q) = (term141 _85070 P Q).
Proof. exact (@lem3248362 _85070 P Q). Qed.
Lemma lem3248364 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term142 _85070 x s a) = (term143 _85070 x s a).
Proof. exact (@lem3248363 _85070 (s x) (term90 _85070 s a)). Qed.
Lemma lem3248365 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term144 _85070 s a x) = (term83 _85070 s x a).
Proof. exact (eq_refl (term144 _85070 s a x)). Qed.
Lemma lem3248366 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term145 _85070 s a) = (term90 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248365 _85070 s x a)). Qed.
Lemma lem3248367 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248368 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term146 _85070 s a) = (term91 _85070 s a).
Proof. exact (MK_COMB (@lem3248367 _85070) (@lem3248366 _85070 s a)). Qed.
Lemma lem3248369 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term147 _85070 s x) = (term147 _85070 s x).
Proof. exact (eq_refl (term147 _85070 s x)). Qed.
Lemma lem3248370 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term142 _85070 x s a) = (term148 _85070 x s a).
Proof. exact (MK_COMB (@lem3248369 _85070 s x) (@lem3248368 _85070 s a)). Qed.
Lemma lem3248371 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3248372 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term149 _85070 x s a) = (term150 _85070 x s a).
Proof. exact (MK_COMB (@lem3248371) (@lem3248370 _85070 x s a)). Qed.
Lemma lem3248373 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (a : _85070) : (term144 _85070 s a x') = (term83 _85070 s x' a).
Proof. exact (eq_refl (term144 _85070 s a x')). Qed.
Lemma lem3248374 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term147 _85070 s x) = (term147 _85070 s x).
Proof. exact (eq_refl (term147 _85070 s x)). Qed.
Lemma lem3248375 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) : (term151 _85070 x s a x') = (term152 _85070 x s x' a).
Proof. exact (MK_COMB (@lem3248374 _85070 s x) (@lem3248373 _85070 s x' a)). Qed.
Lemma lem3248376 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term153 _85070 x s a) = (term154 _85070 x s a).
Proof. exact (fun_ext (fun x' : _85070 => @lem3248375 _85070 x s x' a)). Qed.
Lemma lem3248377 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248378 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term143 _85070 x s a) = (term155 _85070 x s a).
Proof. exact (MK_COMB (@lem3248377 _85070) (@lem3248376 _85070 x s a)). Qed.
Lemma lem3248379 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : ((term142 _85070 x s a) = (term143 _85070 x s a)) = ((term148 _85070 x s a) = (term155 _85070 x s a)).
Proof. exact (MK_COMB (@lem3248372 _85070 x s a) (@lem3248378 _85070 x s a)). Qed.
Lemma lem3248380 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term148 _85070 x s a) = (term155 _85070 x s a).
Proof. exact (EQ_MP (@lem3248379 _85070 x s a) (@lem3248364 _85070 x s a)). Qed.
Lemma lem3248381 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term156 _85070 s a) = (term157 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248380 _85070 x s a)). Qed.
Lemma lem3248382 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248383 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term139 _85070 s a) = (term158 _85070 s a).
Proof. exact (MK_COMB (@lem3248382 _85070) (@lem3248381 _85070 s a)). Qed.
Lemma lem3248384 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term97 _85070 s a) = (term158 _85070 s a).
Proof. exact (TRANS (@lem3248360 _85070 s a) (@lem3248383 _85070 s a)). Qed.
Lemma lem3248385 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term105 _85070 s a) = (term105 _85070 s a).
Proof. exact (eq_refl (term105 _85070 s a)). Qed.
Lemma lem3248386 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term107 _85070 s a) = (term159 _85070 s a).
Proof. exact (MK_COMB (@lem3248385 _85070 s a) (@lem3248384 _85070 s a)). Qed.
Lemma lem3248388 {A : Type'} (P : Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3248389 {_85070 : Type'} (P : Prop) (Q : _85070 -> Prop) : (term140 _85070 P Q) = (term141 _85070 P Q).
Proof. exact (@lem3248388 _85070 P Q). Qed.
Lemma lem3248390 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term160 _85070 s a) = (term161 _85070 s a).
Proof. exact (@lem3248389 _85070 (term73 _85070 s a) (term157 _85070 s a)). Qed.
Lemma lem3248391 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term162 _85070 s a x) = (term155 _85070 x s a).
Proof. exact (eq_refl (term162 _85070 s a x)). Qed.
Lemma lem3248392 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term163 _85070 s a) = (term157 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248391 _85070 x s a)). Qed.
Lemma lem3248393 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248394 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term164 _85070 s a) = (term158 _85070 s a).
Proof. exact (MK_COMB (@lem3248393 _85070) (@lem3248392 _85070 s a)). Qed.
Lemma lem3248395 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term105 _85070 s a) = (term105 _85070 s a).
Proof. exact (eq_refl (term105 _85070 s a)). Qed.
Lemma lem3248396 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term160 _85070 s a) = (term159 _85070 s a).
Proof. exact (MK_COMB (@lem3248395 _85070 s a) (@lem3248394 _85070 s a)). Qed.
Lemma lem3248397 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3248398 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term165 _85070 s a) = (term166 _85070 s a).
Proof. exact (MK_COMB (@lem3248397) (@lem3248396 _85070 s a)). Qed.
Lemma lem3248399 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term162 _85070 s a x) = (term155 _85070 x s a).
Proof. exact (eq_refl (term162 _85070 s a x)). Qed.
Lemma lem3248400 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term105 _85070 s a) = (term105 _85070 s a).
Proof. exact (eq_refl (term105 _85070 s a)). Qed.
Lemma lem3248401 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term167 _85070 s a x) = (term168 _85070 x s a).
Proof. exact (MK_COMB (@lem3248400 _85070 s a) (@lem3248399 _85070 x s a)). Qed.
Lemma lem3248402 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term169 _85070 s a) = (term170 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248401 _85070 x s a)). Qed.
Lemma lem3248403 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248404 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term161 _85070 s a) = (term171 _85070 s a).
Proof. exact (MK_COMB (@lem3248403 _85070) (@lem3248402 _85070 s a)). Qed.
Lemma lem3248405 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : ((term160 _85070 s a) = (term161 _85070 s a)) = ((term159 _85070 s a) = (term171 _85070 s a)).
Proof. exact (MK_COMB (@lem3248398 _85070 s a) (@lem3248404 _85070 s a)). Qed.
Lemma lem3248406 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term159 _85070 s a) = (term171 _85070 s a).
Proof. exact (EQ_MP (@lem3248405 _85070 s a) (@lem3248390 _85070 s a)). Qed.
Lemma lem3248408 {A : Type'} (P : Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3248409 {_85070 : Type'} (P : Prop) (Q : _85070 -> Prop) : (term140 _85070 P Q) = (term141 _85070 P Q).
Proof. exact (@lem3248408 _85070 P Q). Qed.
Lemma lem3248410 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term172 _85070 x s a) = (term173 _85070 x s a).
Proof. exact (@lem3248409 _85070 (term73 _85070 s a) (term154 _85070 x s a)). Qed.
Lemma lem3248411 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) : (term174 _85070 x s a x') = (term152 _85070 x s x' a).
Proof. exact (eq_refl (term174 _85070 x s a x')). Qed.
Lemma lem3248412 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term175 _85070 x s a) = (term154 _85070 x s a).
Proof. exact (fun_ext (fun x' : _85070 => @lem3248411 _85070 x s x' a)). Qed.
Lemma lem3248413 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248414 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term176 _85070 x s a) = (term155 _85070 x s a).
Proof. exact (MK_COMB (@lem3248413 _85070) (@lem3248412 _85070 x s a)). Qed.
Lemma lem3248415 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term105 _85070 s a) = (term105 _85070 s a).
Proof. exact (eq_refl (term105 _85070 s a)). Qed.
Lemma lem3248416 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term172 _85070 x s a) = (term168 _85070 x s a).
Proof. exact (MK_COMB (@lem3248415 _85070 s a) (@lem3248414 _85070 x s a)). Qed.
Lemma lem3248417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3248418 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term177 _85070 x s a) = (term178 _85070 x s a).
Proof. exact (MK_COMB (@lem3248417) (@lem3248416 _85070 x s a)). Qed.
Lemma lem3248419 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) : (term174 _85070 x s a x') = (term152 _85070 x s x' a).
Proof. exact (eq_refl (term174 _85070 x s a x')). Qed.
Lemma lem3248420 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term105 _85070 s a) = (term105 _85070 s a).
Proof. exact (eq_refl (term105 _85070 s a)). Qed.
Lemma lem3248421 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) : (term179 _85070 x s a x') = (term180 _85070 x s x' a).
Proof. exact (MK_COMB (@lem3248420 _85070 s a) (@lem3248419 _85070 x s x' a)). Qed.
Lemma lem3248422 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term181 _85070 x s a) = (term182 _85070 x s a).
Proof. exact (fun_ext (fun x' : _85070 => @lem3248421 _85070 x s x' a)). Qed.
Lemma lem3248423 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248424 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term173 _85070 x s a) = (term183 _85070 x s a).
Proof. exact (MK_COMB (@lem3248423 _85070) (@lem3248422 _85070 x s a)). Qed.
Lemma lem3248425 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : ((term172 _85070 x s a) = (term173 _85070 x s a)) = ((term168 _85070 x s a) = (term183 _85070 x s a)).
Proof. exact (MK_COMB (@lem3248418 _85070 x s a) (@lem3248424 _85070 x s a)). Qed.
Lemma lem3248426 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term168 _85070 x s a) = (term183 _85070 x s a).
Proof. exact (EQ_MP (@lem3248425 _85070 x s a) (@lem3248410 _85070 x s a)). Qed.
Lemma lem3248427 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term170 _85070 s a) = (term184 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248426 _85070 x s a)). Qed.
Lemma lem3248428 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248429 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term171 _85070 s a) = (term185 _85070 s a).
Proof. exact (MK_COMB (@lem3248428 _85070) (@lem3248427 _85070 s a)). Qed.
Lemma lem3248430 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term159 _85070 s a) = (term185 _85070 s a).
Proof. exact (TRANS (@lem3248406 _85070 s a) (@lem3248429 _85070 s a)). Qed.
Lemma lem3248431 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term107 _85070 s a) = (term185 _85070 s a).
Proof. exact (TRANS (@lem3248386 _85070 s a) (@lem3248430 _85070 s a)). Qed.
Lemma lem3248432 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3248433 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term109 _85070 s a) = (term186 _85070 s a).
Proof. exact (MK_COMB (@lem3248432) (@lem3248431 _85070 s a)). Qed.
Lemma lem3248435 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3248436 {_85070 : Type'} (P : _85070 -> Prop) (Q : Prop) : (term137 _85070 P Q) = (term138 _85070 P Q).
Proof. exact (@lem3248435 _85070 P Q). Qed.
Lemma lem3248437 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term187 _85070 s a) = (term188 _85070 s a).
Proof. exact (@lem3248436 _85070 (term70 _85070 s a) (term134 _85070 s a)). Qed.
Lemma lem3248438 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term189 _85070 s a x) = (term61 _85070 s x a).
Proof. exact (eq_refl (term189 _85070 s a x)). Qed.
Lemma lem3248439 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term190 _85070 s a) = (term70 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248438 _85070 s x a)). Qed.
Lemma lem3248440 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248441 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term191 _85070 s a) = (term71 _85070 s a).
Proof. exact (MK_COMB (@lem3248440 _85070) (@lem3248439 _85070 s a)). Qed.
Lemma lem3248442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3248443 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term192 _85070 s a) = (term101 _85070 s a).
Proof. exact (MK_COMB (@lem3248442) (@lem3248441 _85070 s a)). Qed.
Lemma lem3248444 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term134 _85070 s a) = (term134 _85070 s a).
Proof. exact (eq_refl (term134 _85070 s a)). Qed.
Lemma lem3248445 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term187 _85070 s a) = (term135 _85070 s a).
Proof. exact (MK_COMB (@lem3248443 _85070 s a) (@lem3248444 _85070 s a)). Qed.
Lemma lem3248446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3248447 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term193 _85070 s a) = (term194 _85070 s a).
Proof. exact (MK_COMB (@lem3248446) (@lem3248445 _85070 s a)). Qed.
Lemma lem3248448 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term189 _85070 s a x) = (term61 _85070 s x a).
Proof. exact (eq_refl (term189 _85070 s a x)). Qed.
Lemma lem3248449 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3248450 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term195 _85070 s a x) = (term196 _85070 s x a).
Proof. exact (MK_COMB (@lem3248449) (@lem3248448 _85070 s x a)). Qed.
Lemma lem3248451 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term134 _85070 s a) = (term134 _85070 s a).
Proof. exact (eq_refl (term134 _85070 s a)). Qed.
Lemma lem3248452 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term197 _85070 x s a) = (term198 _85070 x s a).
Proof. exact (MK_COMB (@lem3248450 _85070 s x a) (@lem3248451 _85070 s a)). Qed.
Lemma lem3248453 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term199 _85070 s a) = (term200 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248452 _85070 x s a)). Qed.
Lemma lem3248454 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248455 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term188 _85070 s a) = (term201 _85070 s a).
Proof. exact (MK_COMB (@lem3248454 _85070) (@lem3248453 _85070 s a)). Qed.
Lemma lem3248456 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : ((term187 _85070 s a) = (term188 _85070 s a)) = ((term135 _85070 s a) = (term201 _85070 s a)).
Proof. exact (MK_COMB (@lem3248447 _85070 s a) (@lem3248455 _85070 s a)). Qed.
Lemma lem3248457 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term135 _85070 s a) = (term201 _85070 s a).
Proof. exact (EQ_MP (@lem3248456 _85070 s a) (@lem3248437 _85070 s a)). Qed.
Lemma lem3248458 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term136 _85070 s a) = (term202 _85070 s a).
Proof. exact (MK_COMB (@lem3248433 _85070 s a) (@lem3248457 _85070 s a)). Qed.
Lemma lem3248460 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term203 A P Q) = (term204 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3248461 {_85070 : Type'} (P : _85070 -> Prop) (Q : _85070 -> Prop) : (term203 _85070 P Q) = (term204 _85070 P Q).
Proof. exact (@lem3248460 _85070 P Q). Qed.
Lemma lem3248462 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term205 _85070 s a) = (term206 _85070 s a).
Proof. exact (@lem3248461 _85070 (term184 _85070 s a) (term200 _85070 s a)). Qed.
Lemma lem3248463 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term207 _85070 s a x) = (term183 _85070 x s a).
Proof. exact (eq_refl (term207 _85070 s a x)). Qed.
Lemma lem3248464 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term208 _85070 s a) = (term184 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248463 _85070 x s a)). Qed.
Lemma lem3248465 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248466 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term209 _85070 s a) = (term185 _85070 s a).
Proof. exact (MK_COMB (@lem3248465 _85070) (@lem3248464 _85070 s a)). Qed.
Lemma lem3248467 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3248468 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term210 _85070 s a) = (term186 _85070 s a).
Proof. exact (MK_COMB (@lem3248467) (@lem3248466 _85070 s a)). Qed.
Lemma lem3248469 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term211 _85070 s a x) = (term198 _85070 x s a).
Proof. exact (eq_refl (term211 _85070 s a x)). Qed.
Lemma lem3248470 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term212 _85070 s a) = (term200 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248469 _85070 x s a)). Qed.
Lemma lem3248471 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248472 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term213 _85070 s a) = (term201 _85070 s a).
Proof. exact (MK_COMB (@lem3248471 _85070) (@lem3248470 _85070 s a)). Qed.
Lemma lem3248473 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term205 _85070 s a) = (term202 _85070 s a).
Proof. exact (MK_COMB (@lem3248468 _85070 s a) (@lem3248472 _85070 s a)). Qed.
Lemma lem3248474 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3248475 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term214 _85070 s a) = (term215 _85070 s a).
Proof. exact (MK_COMB (@lem3248474) (@lem3248473 _85070 s a)). Qed.
Lemma lem3248476 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term207 _85070 s a x) = (term183 _85070 x s a).
Proof. exact (eq_refl (term207 _85070 s a x)). Qed.
Lemma lem3248477 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3248478 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term216 _85070 s a x) = (term217 _85070 x s a).
Proof. exact (MK_COMB (@lem3248477) (@lem3248476 _85070 x s a)). Qed.
Lemma lem3248479 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term211 _85070 s a x) = (term198 _85070 x s a).
Proof. exact (eq_refl (term211 _85070 s a x)). Qed.
Lemma lem3248480 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term218 _85070 s a x) = (term219 _85070 x s a).
Proof. exact (MK_COMB (@lem3248478 _85070 x s a) (@lem3248479 _85070 x s a)). Qed.
Lemma lem3248481 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term220 _85070 s a) = (term221 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248480 _85070 x s a)). Qed.
Lemma lem3248482 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248483 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term206 _85070 s a) = (term222 _85070 s a).
Proof. exact (MK_COMB (@lem3248482 _85070) (@lem3248481 _85070 s a)). Qed.
Lemma lem3248484 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : ((term205 _85070 s a) = (term206 _85070 s a)) = ((term202 _85070 s a) = (term222 _85070 s a)).
Proof. exact (MK_COMB (@lem3248475 _85070 s a) (@lem3248483 _85070 s a)). Qed.
Lemma lem3248485 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term202 _85070 s a) = (term222 _85070 s a).
Proof. exact (EQ_MP (@lem3248484 _85070 s a) (@lem3248462 _85070 s a)). Qed.
Lemma lem3248487 {A : Type'} (P : A -> Prop) (Q : Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3248488 {_85070 : Type'} (P : _85070 -> Prop) (Q : Prop) : (term223 _85070 P Q) = (term224 _85070 P Q).
Proof. exact (@lem3248487 _85070 P Q). Qed.
Lemma lem3248489 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term225 _85070 x s a) = (term226 _85070 x s a).
Proof. exact (@lem3248488 _85070 (term182 _85070 x s a) (term198 _85070 x s a)). Qed.
Lemma lem3248490 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) : (term227 _85070 x s a x') = (term180 _85070 x s x' a).
Proof. exact (eq_refl (term227 _85070 x s a x')). Qed.
Lemma lem3248491 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term228 _85070 x s a) = (term182 _85070 x s a).
Proof. exact (fun_ext (fun x' : _85070 => @lem3248490 _85070 x s x' a)). Qed.
Lemma lem3248492 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248493 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term229 _85070 x s a) = (term183 _85070 x s a).
Proof. exact (MK_COMB (@lem3248492 _85070) (@lem3248491 _85070 x s a)). Qed.
Lemma lem3248494 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3248495 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term230 _85070 x s a) = (term217 _85070 x s a).
Proof. exact (MK_COMB (@lem3248494) (@lem3248493 _85070 x s a)). Qed.
Lemma lem3248496 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term198 _85070 x s a) = (term198 _85070 x s a).
Proof. exact (eq_refl (term198 _85070 x s a)). Qed.
Lemma lem3248497 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term225 _85070 x s a) = (term219 _85070 x s a).
Proof. exact (MK_COMB (@lem3248495 _85070 x s a) (@lem3248496 _85070 x s a)). Qed.
Lemma lem3248498 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3248499 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term231 _85070 x s a) = (term232 _85070 x s a).
Proof. exact (MK_COMB (@lem3248498) (@lem3248497 _85070 x s a)). Qed.
Lemma lem3248500 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) : (term227 _85070 x s a x') = (term180 _85070 x s x' a).
Proof. exact (eq_refl (term227 _85070 x s a x')). Qed.
Lemma lem3248501 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3248502 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) : (term233 _85070 x s a x') = (term234 _85070 x s x' a).
Proof. exact (MK_COMB (@lem3248501) (@lem3248500 _85070 x s x' a)). Qed.
Lemma lem3248503 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term198 _85070 x s a) = (term198 _85070 x s a).
Proof. exact (eq_refl (term198 _85070 x s a)). Qed.
Lemma lem3248504 {_85070 : Type'} (x' : _85070) (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term235 _85070 x' x s a) = (term236 _85070 x' x s a).
Proof. exact (MK_COMB (@lem3248502 _85070 x s x' a) (@lem3248503 _85070 x s a)). Qed.
Lemma lem3248505 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term237 _85070 x s a) = (term238 _85070 x s a).
Proof. exact (fun_ext (fun x' : _85070 => @lem3248504 _85070 x' x s a)). Qed.
Lemma lem3248506 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248507 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term226 _85070 x s a) = (term239 _85070 x s a).
Proof. exact (MK_COMB (@lem3248506 _85070) (@lem3248505 _85070 x s a)). Qed.
Lemma lem3248508 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : ((term225 _85070 x s a) = (term226 _85070 x s a)) = ((term219 _85070 x s a) = (term239 _85070 x s a)).
Proof. exact (MK_COMB (@lem3248499 _85070 x s a) (@lem3248507 _85070 x s a)). Qed.
Lemma lem3248509 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term219 _85070 x s a) = (term239 _85070 x s a).
Proof. exact (EQ_MP (@lem3248508 _85070 x s a) (@lem3248489 _85070 x s a)). Qed.
Lemma lem3248510 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term221 _85070 s a) = (term240 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248509 _85070 x s a)). Qed.
Lemma lem3248511 {_85070 : Type'} : (@ex _85070) = (@ex _85070).
Proof. exact (eq_refl (@ex _85070)). Qed.
Lemma lem3248512 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term222 _85070 s a) = (term241 _85070 s a).
Proof. exact (MK_COMB (@lem3248511 _85070) (@lem3248510 _85070 s a)). Qed.
Lemma lem3248513 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term202 _85070 s a) = (term241 _85070 s a).
Proof. exact (TRANS (@lem3248485 _85070 s a) (@lem3248512 _85070 s a)). Qed.
Lemma lem3248514 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term136 _85070 s a) = (term241 _85070 s a).
Proof. exact (TRANS (@lem3248458 _85070 s a) (@lem3248513 _85070 s a)). Qed.
Lemma lem3248515 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term111 _85070 s a) = (term241 _85070 s a).
Proof. exact (TRANS (@lem3248356 _85070 s a) (@lem3248514 _85070 s a)). Qed.
Lemma lem3248516 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term46 _85070 s a) = (term241 _85070 s a).
Proof. exact (TRANS (@lem3248115 _85070 s a) (@lem3248515 _85070 s a)). Qed.
Lemma lem3248517 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term46 _85070 s a) : term241 _85070 s a.
Proof. exact (EQ_MP (@lem3248516 _85070 s a) (@lem3248013 _85070 s a h1)). Qed.
Lemma lem3248518 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term239 _85070 x s a) : term239 _85070 x s a.
Proof. exact (h1). Qed.
Lemma lem3248519 {_85070 : Type'} (x' : _85070) (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term236 _85070 x' x s a) : term236 _85070 x' x s a.
Proof. exact (h1). Qed.
Lemma lem3248532 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term62 _85070 s x a) = (term62 _85070 s x a).
Proof. exact (eq_refl (term62 _85070 s x a)). Qed.
Lemma lem3248533 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term72 _85070 s a) = (term72 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248532 _85070 s x a)). Qed.
Lemma lem3248534 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3248535 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term73 _85070 s a) = (term73 _85070 s a).
Proof. exact (MK_COMB (@lem3248534 _85070) (@lem3248533 _85070 s a)). Qed.
Lemma lem3248548 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term118 _85070 s x a) = (term118 _85070 s x a).
Proof. exact (eq_refl (term118 _85070 s x a)). Qed.
Lemma lem3248549 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term116 _85070 s a) = (term116 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248548 _85070 s x a)). Qed.
Lemma lem3248550 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3248551 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term128 _85070 s a) = (term128 _85070 s a).
Proof. exact (MK_COMB (@lem3248550 _85070) (@lem3248549 _85070 s a)). Qed.
Lemma lem3248552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3248553 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term130 _85070 s a) = (term130 _85070 s a).
Proof. exact (MK_COMB (@lem3248552) (@lem3248551 _85070 s a)). Qed.
Lemma lem3248554 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term133 _85070 s a) = (term133 _85070 s a).
Proof. exact (MK_COMB (@lem3248553 _85070 s a) (@lem3248535 _85070 s a)). Qed.
Lemma lem3248559 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term35 _85070 s x) = (term35 _85070 s x).
Proof. exact (eq_refl (term35 _85070 s x)). Qed.
Lemma lem3248560 {_85070 : Type'} (s : _85070 -> Prop) : (term37 _85070 s) = (term37 _85070 s).
Proof. exact (fun_ext (fun x : _85070 => @lem3248559 _85070 s x)). Qed.
Lemma lem3248561 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3248562 {_85070 : Type'} (s : _85070 -> Prop) : (term38 _85070 s) = (term38 _85070 s).
Proof. exact (MK_COMB (@lem3248561 _85070) (@lem3248560 _85070 s)). Qed.
Lemma lem3248563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3248564 {_85070 : Type'} (s : _85070 -> Prop) : (term39 _85070 s) = (term39 _85070 s).
Proof. exact (MK_COMB (@lem3248563) (@lem3248562 _85070 s)). Qed.
Lemma lem3248565 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term134 _85070 s a) = (term134 _85070 s a).
Proof. exact (MK_COMB (@lem3248564 _85070 s) (@lem3248554 _85070 s a)). Qed.
Lemma lem3248580 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term196 _85070 s x a) = (term196 _85070 s x a).
Proof. exact (eq_refl (term196 _85070 s x a)). Qed.
Lemma lem3248581 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term198 _85070 x s a) = (term198 _85070 x s a).
Proof. exact (MK_COMB (@lem3248580 _85070 s x a) (@lem3248565 _85070 s a)). Qed.
Lemma lem3248616 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) : (term152 _85070 x s x' a) = (term152 _85070 x s x' a).
Proof. exact (eq_refl (term152 _85070 x s x' a)). Qed.
Lemma lem3248629 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term62 _85070 s x a) = (term62 _85070 s x a).
Proof. exact (eq_refl (term62 _85070 s x a)). Qed.
Lemma lem3248630 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term72 _85070 s a) = (term72 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248629 _85070 s x a)). Qed.
Lemma lem3248631 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3248632 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term73 _85070 s a) = (term73 _85070 s a).
Proof. exact (MK_COMB (@lem3248631 _85070) (@lem3248630 _85070 s a)). Qed.
Lemma lem3248633 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3248634 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term105 _85070 s a) = (term105 _85070 s a).
Proof. exact (MK_COMB (@lem3248633) (@lem3248632 _85070 s a)). Qed.
Lemma lem3248635 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) : (term180 _85070 x s x' a) = (term180 _85070 x s x' a).
Proof. exact (MK_COMB (@lem3248634 _85070 s a) (@lem3248616 _85070 x s x' a)). Qed.
Lemma lem3248636 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3248637 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) : (term234 _85070 x s x' a) = (term234 _85070 x s x' a).
Proof. exact (MK_COMB (@lem3248636) (@lem3248635 _85070 x s x' a)). Qed.
Lemma lem3248638 {_85070 : Type'} (x' : _85070) (x : _85070) (s : _85070 -> Prop) (a : _85070) : (term236 _85070 x' x s a) = (term236 _85070 x' x s a).
Proof. exact (MK_COMB (@lem3248637 _85070 x s x' a) (@lem3248581 _85070 x s a)). Qed.
Lemma lem3248639 {_85070 : Type'} (x' : _85070) (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term236 _85070 x' x s a) : term236 _85070 x' x s a.
Proof. exact (EQ_MP (@lem3248638 _85070 x' x s a) (@lem3248519 _85070 x' x s a h1)). Qed.
Lemma lem3248640 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term180 _85070 x s x' a.
Proof. exact (h1). Qed.
Lemma lem3248641 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term198 _85070 x s a) : term198 _85070 x s a.
Proof. exact (h1). Qed.
Lemma lem3248642 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term152 _85070 x s x' a.
Proof. exact (proj2 (@lem3248640 _85070 x s x' a h1)). Qed.
Lemma lem3248643 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term73 _85070 s a.
Proof. exact (proj1 (@lem3248640 _85070 x s x' a h1)). Qed.
Lemma lem3248644 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term83 _85070 s x' a.
Proof. exact (proj2 (@lem3248642 _85070 x s x' a h1)). Qed.
Lemma lem3248646 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term242 _85070 s x' a.
Proof. exact (proj2 (@lem3248644 _85070 x s x' a h1)). Qed.
Lemma lem3248647 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term243 _85070 s x' a.
Proof. exact (proj1 (@lem3248644 _85070 x s x' a h1)). Qed.
Lemma lem3248654 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term198 _85070 x s a) : term134 _85070 s a.
Proof. exact (proj2 (@lem3248641 _85070 x s a h1)). Qed.
Lemma lem3248655 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term198 _85070 x s a) : term61 _85070 s x a.
Proof. exact (proj1 (@lem3248641 _85070 x s a h1)). Qed.
Lemma lem3248658 {_85070 : Type'} (s : _85070 -> Prop) (h1 : term38 _85070 s) : term38 _85070 s.
Proof. exact (h1). Qed.
Lemma lem3248659 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term133 _85070 s a) : term133 _85070 s a.
Proof. exact (h1). Qed.
Lemma lem3248660 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term133 _85070 s a) : term73 _85070 s a.
Proof. exact (proj2 (@lem3248659 _85070 s a h1)). Qed.
Lemma lem3248682 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') : term35 _85070 s x'.
Proof. exact (h1). Qed.
Lemma lem3248686 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3248694 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term62 _85070 s x a) = (term62 _85070 s x a).
Proof. exact (eq_refl (term62 _85070 s x a)). Qed.
Lemma lem3248695 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term72 _85070 s a) = (term72 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248694 _85070 s x a)). Qed.
Lemma lem3248696 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3248698 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term73 _85070 s a) = (term73 _85070 s a).
Proof. exact (MK_COMB (@lem3248696 _85070) (@lem3248695 _85070 s a)). Qed.
Lemma lem3248699 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term73 _85070 s a.
Proof. exact (EQ_MP (@lem3248698 _85070 s a) (@lem3248643 _85070 x s x' a h1)). Qed.
Lemma lem3248707 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') : term35 _85070 s x'.
Proof. exact (h1). Qed.
Lemma lem3248711 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : x' = a) : x' = a.
Proof. exact (h1). Qed.
Lemma lem3248719 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term62 _85070 s x a) = (term62 _85070 s x a).
Proof. exact (eq_refl (term62 _85070 s x a)). Qed.
Lemma lem3248720 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term72 _85070 s a) = (term72 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248719 _85070 s x a)). Qed.
Lemma lem3248721 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3248723 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term73 _85070 s a) = (term73 _85070 s a).
Proof. exact (MK_COMB (@lem3248721 _85070) (@lem3248720 _85070 s a)). Qed.
Lemma lem3248724 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term73 _85070 s a.
Proof. exact (EQ_MP (@lem3248723 _85070 s a) (@lem3248643 _85070 x s x' a h1)). Qed.
Lemma lem3248732 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) : term244 _85070 x' a.
Proof. exact (h1). Qed.
Lemma lem3248736 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3248757 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) : term244 _85070 x' a.
Proof. exact (h1). Qed.
Lemma lem3248761 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : x' = a) : x' = a.
Proof. exact (h1). Qed.
Lemma lem3248771 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term35 _85070 s x) = (term35 _85070 s x).
Proof. exact (eq_refl (term35 _85070 s x)). Qed.
Lemma lem3248772 {_85070 : Type'} (s : _85070 -> Prop) : (term37 _85070 s) = (term37 _85070 s).
Proof. exact (fun_ext (fun x : _85070 => @lem3248771 _85070 s x)). Qed.
Lemma lem3248773 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3248775 {_85070 : Type'} (s : _85070 -> Prop) : (term38 _85070 s) = (term38 _85070 s).
Proof. exact (MK_COMB (@lem3248773 _85070) (@lem3248772 _85070 s)). Qed.
Lemma lem3248776 {_85070 : Type'} (s : _85070 -> Prop) (h1 : term38 _85070 s) : term38 _85070 s.
Proof. exact (EQ_MP (@lem3248775 _85070 s) (@lem3248658 _85070 s h1)). Qed.
Lemma lem3248805 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) (a : _85070) : (term62 _85070 s x a) = (term62 _85070 s x a).
Proof. exact (eq_refl (term62 _85070 s x a)). Qed.
Lemma lem3248806 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term72 _85070 s a) = (term72 _85070 s a).
Proof. exact (fun_ext (fun x : _85070 => @lem3248805 _85070 s x a)). Qed.
Lemma lem3248807 {_85070 : Type'} : (@all _85070) = (@all _85070).
Proof. exact (eq_refl (@all _85070)). Qed.
Lemma lem3248809 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term73 _85070 s a) = (term73 _85070 s a).
Proof. exact (MK_COMB (@lem3248807 _85070) (@lem3248806 _85070 s a)). Qed.
Lemma lem3248810 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term133 _85070 s a) : term73 _85070 s a.
Proof. exact (EQ_MP (@lem3248809 _85070 s a) (@lem3248660 _85070 s a h1)). Qed.
Lemma lem3248814 {_85070 : Type'} (_33254 : _85070) (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term121 _85070 s a _33254.
Proof. exact (@lem3248699 _85070 x s x' a h1 _33254). Qed.
Lemma lem3248815 {_85070 : Type'} (s : _85070 -> Prop) (_33254 : _85070) (a : _85070) : (term121 _85070 s a _33254) = (term62 _85070 s _33254 a).
Proof. exact (eq_refl (term121 _85070 s a _33254)). Qed.
Lemma lem3248817 {_85070 : Type'} (_33255 : _85070) (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term121 _85070 s a _33255.
Proof. exact (@lem3248724 _85070 x s x' a h1 _33255). Qed.
Lemma lem3248818 {_85070 : Type'} (s : _85070 -> Prop) (_33255 : _85070) (a : _85070) : (term121 _85070 s a _33255) = (term62 _85070 s _33255 a).
Proof. exact (eq_refl (term121 _85070 s a _33255)). Qed.
Lemma lem3248823 {_85070 : Type'} (_33257 : _85070) (s : _85070 -> Prop) (h1 : term38 _85070 s) : term77 _85070 s _33257.
Proof. exact (@lem3248776 _85070 s h1 _33257). Qed.
Lemma lem3248824 {_85070 : Type'} (s : _85070 -> Prop) (_33257 : _85070) : (term77 _85070 s _33257) = (term35 _85070 s _33257).
Proof. exact (eq_refl (term77 _85070 s _33257)). Qed.
Lemma lem3248829 {_85070 : Type'} (_33259 : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term133 _85070 s a) : term121 _85070 s a _33259.
Proof. exact (@lem3248810 _85070 s a h1 _33259). Qed.
Lemma lem3248830 {_85070 : Type'} (s : _85070 -> Prop) (_33259 : _85070) (a : _85070) : (term121 _85070 s a _33259) = (term62 _85070 s _33259 a).
Proof. exact (eq_refl (term121 _85070 s a _33259)). Qed.
Lemma lem3248841 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') : term35 _85070 s x'.
Proof. exact (h1). Qed.
Lemma lem3248843 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3248853 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') : term35 _85070 s x'.
Proof. exact (h1). Qed.
Lemma lem3248855 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : x' = a) : x' = a.
Proof. exact (h1). Qed.
Lemma lem3248861 {_85070 : Type'} (_33255 : _85070) (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term62 _85070 s _33255 a.
Proof. exact (EQ_MP (@lem3248818 _85070 s _33255 a) (@lem3248817 _85070 _33255 x s x' a h1)). Qed.
Lemma lem3248865 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) : term244 _85070 x' a.
Proof. exact (h1). Qed.
Lemma lem3248867 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3248877 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) : term244 _85070 x' a.
Proof. exact (h1). Qed.
Lemma lem3248879 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : x' = a) : x' = a.
Proof. exact (h1). Qed.
Lemma lem3248885 {_85070 : Type'} (_33257 : _85070) (s : _85070 -> Prop) (h1 : term38 _85070 s) : term35 _85070 s _33257.
Proof. exact (EQ_MP (@lem3248824 _85070 s _33257) (@lem3248823 _85070 _33257 s h1)). Qed.
Lemma lem3248889 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term198 _85070 x s a) : term244 _85070 x a.
Proof. exact (proj2 (@lem3248655 _85070 x s a h1)). Qed.
Lemma lem3248901 {_85070 : Type'} (_33259 : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term133 _85070 s a) : term62 _85070 s _33259 a.
Proof. exact (EQ_MP (@lem3248830 _85070 s _33259 a) (@lem3248829 _85070 _33259 s a h1)). Qed.
Lemma lem3248929 {_85070 : Type'} (_33254 : _85070) (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term62 _85070 s _33254 a.
Proof. exact (EQ_MP (@lem3248815 _85070 s _33254 a) (@lem3248814 _85070 _33254 x s x' a h1)). Qed.
Lemma lem3248944 {_85070 : Type'} (s : _85070 -> Prop) : (term37 _85070 s) = (term37 _85070 s).
Proof. exact (eq_refl (term37 _85070 s)). Qed.
Lemma lem3248945 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : x' = a) : (term77 _85070 s x') = (term77 _85070 s a).
Proof. exact (MK_COMB (@lem3248944 _85070 s) (@lem3248855 _85070 x' a h1)). Qed.
Lemma lem3248946 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term77 _85070 s a) = (term35 _85070 s a).
Proof. exact (eq_refl (term77 _85070 s a)). Qed.
Lemma lem3248947 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) : (term245 _85070 s x') = (term245 _85070 s x').
Proof. exact (eq_refl (term245 _85070 s x')). Qed.
Lemma lem3248948 {_85070 : Type'} (x' : _85070) (s : _85070 -> Prop) (a : _85070) : ((term77 _85070 s x') = (term77 _85070 s a)) = ((term77 _85070 s x') = (term35 _85070 s a)).
Proof. exact (MK_COMB (@lem3248947 _85070 s x') (@lem3248946 _85070 s a)). Qed.
Lemma lem3248949 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) : (term77 _85070 s x') = (term35 _85070 s x').
Proof. exact (eq_refl (term77 _85070 s x')). Qed.
Lemma lem3248950 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3248951 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) : (term245 _85070 s x') = (term246 _85070 s x').
Proof. exact (MK_COMB (@lem3248950) (@lem3248949 _85070 s x')). Qed.
Lemma lem3248952 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term35 _85070 s a) = (term35 _85070 s a).
Proof. exact (eq_refl (term35 _85070 s a)). Qed.
Lemma lem3248953 {_85070 : Type'} (x' : _85070) (s : _85070 -> Prop) (a : _85070) : ((term77 _85070 s x') = (term35 _85070 s a)) = ((term35 _85070 s x') = (term35 _85070 s a)).
Proof. exact (MK_COMB (@lem3248951 _85070 s x') (@lem3248952 _85070 s a)). Qed.
Lemma lem3248954 {_85070 : Type'} (x' : _85070) (s : _85070 -> Prop) (a : _85070) : ((term77 _85070 s x') = (term77 _85070 s a)) = ((term35 _85070 s x') = (term35 _85070 s a)).
Proof. exact (TRANS (@lem3248948 _85070 x' s a) (@lem3248953 _85070 x' s a)). Qed.
Lemma lem3248955 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : x' = a) : (term35 _85070 s x') = (term35 _85070 s a).
Proof. exact (EQ_MP (@lem3248954 _85070 x' s a) (@lem3248945 _85070 s x' a h1)). Qed.
Lemma lem3248956 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : x' = a) : term35 _85070 s a.
Proof. exact (EQ_MP (@lem3248955 _85070 s x' a h2) (@lem3248853 _85070 s x' h1)). Qed.
Lemma lem3248999 {_85070 : Type'} (a : _85070) : (term247 _85070 a) = (term247 _85070 a).
Proof. exact (eq_refl (term247 _85070 a)). Qed.
Lemma lem3249000 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : x' = a) : (term248 _85070 a x') = (term249 _85070 a).
Proof. exact (MK_COMB (@lem3248999 _85070 a) (@lem3248879 _85070 x' a h1)). Qed.
Lemma lem3249001 {_85070 : Type'} (a : _85070) : (term249 _85070 a) = (term250 _85070 a).
Proof. exact (eq_refl (term249 _85070 a)). Qed.
Lemma lem3249002 {_85070 : Type'} (a : _85070) (x' : _85070) : (term251 _85070 a x') = (term251 _85070 a x').
Proof. exact (eq_refl (term251 _85070 a x')). Qed.
Lemma lem3249003 {_85070 : Type'} (x' : _85070) (a : _85070) : ((term248 _85070 a x') = (term249 _85070 a)) = ((term248 _85070 a x') = (term250 _85070 a)).
Proof. exact (MK_COMB (@lem3249002 _85070 a x') (@lem3249001 _85070 a)). Qed.
Lemma lem3249004 {_85070 : Type'} (x' : _85070) (a : _85070) : (term248 _85070 a x') = (term244 _85070 x' a).
Proof. exact (eq_refl (term248 _85070 a x')). Qed.
Lemma lem3249005 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3249006 {_85070 : Type'} (x' : _85070) (a : _85070) : (term251 _85070 a x') = (term252 _85070 x' a).
Proof. exact (MK_COMB (@lem3249005) (@lem3249004 _85070 x' a)). Qed.
Lemma lem3249007 {_85070 : Type'} (a : _85070) : (term250 _85070 a) = (term250 _85070 a).
Proof. exact (eq_refl (term250 _85070 a)). Qed.
Lemma lem3249008 {_85070 : Type'} (x' : _85070) (a : _85070) : ((term248 _85070 a x') = (term250 _85070 a)) = ((term244 _85070 x' a) = (term250 _85070 a)).
Proof. exact (MK_COMB (@lem3249006 _85070 x' a) (@lem3249007 _85070 a)). Qed.
Lemma lem3249009 {_85070 : Type'} (x' : _85070) (a : _85070) : ((term248 _85070 a x') = (term249 _85070 a)) = ((term244 _85070 x' a) = (term250 _85070 a)).
Proof. exact (TRANS (@lem3249003 _85070 x' a) (@lem3249008 _85070 x' a)). Qed.
Lemma lem3249010 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : x' = a) : (term244 _85070 x' a) = (term250 _85070 a).
Proof. exact (EQ_MP (@lem3249009 _85070 x' a) (@lem3249000 _85070 x' a h1)). Qed.
Lemma lem3249011 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : term250 _85070 a.
Proof. exact (EQ_MP (@lem3249010 _85070 x' a h2) (@lem3248877 _85070 x' a h1)). Qed.
Lemma lem3249027 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3249028 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : s x') : term253 _85070 s x'.
Proof. exact (fun h0 : term35 _85070 s x' => @lem3249027 _85070 s x' h1). Qed.
Lemma lem3249030 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249031 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) : (term253 _85070 s x') = (s x').
Proof. exact (@lem3249030 (s x')). Qed.
Lemma lem3249032 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3249031 _85070 s x') (@lem3249028 _85070 s x' h1)). Qed.
Lemma lem3249035 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3249037 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) : (term35 _85070 s x') = (term255 _85070 s x').
Proof. exact (@lem3249035 (s x')). Qed.
Lemma lem3249040 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') : term255 _85070 s x'.
Proof. exact (EQ_MP (@lem3249037 _85070 s x') (@lem3248841 _85070 s x' h1)). Qed.
Lemma lem3249043 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') (h2 : s x') : False.
Proof. exact (@lem3249040 _85070 s x' h1 (@lem3249032 _85070 s x' h2)). Qed.
Lemma lem3249044 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') (h2 : s x') : term256.
Proof. exact (fun h0 : ~ False => @lem3249043 _85070 s x' h1 h2). Qed.
Lemma lem3249046 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249047 : term256 = False.
Proof. exact (@lem3249046 False). Qed.
Lemma lem3249048 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3249047) (@lem3249044 _85070 s x' h1 h2)). Qed.
Lemma lem3249049 {_85070 : Type'} (s : _85070 -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3249050 {_85070 : Type'} (_33278 : _85070) (_33279 : _85070) (h1 : _33278 = _33279) : _33278 = _33279.
Proof. exact (h1). Qed.
Lemma lem3249051 {_85070 : Type'} (s : _85070 -> Prop) (_33278 : _85070) (_33279 : _85070) (h1 : _33278 = _33279) : (s _33278) = (s _33279).
Proof. exact (MK_COMB (@lem3249049 _85070 s) (@lem3249050 _85070 _33278 _33279 h1)). Qed.
Lemma lem3249053 (b : Prop) (a : Prop) : term257 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3249054 {_85070 : Type'} (_33279 : _85070) (s : _85070 -> Prop) (_33278 : _85070) : term258 _85070 _33279 s _33278.
Proof. exact (@lem3249053 (s _33279) (s _33278)). Qed.
Lemma lem3249055 {_85070 : Type'} (s : _85070 -> Prop) (_33278 : _85070) (_33279 : _85070) (h1 : _33278 = _33279) : term259 _85070 _33279 s _33278.
Proof. exact (@lem3249054 _85070 _33279 s _33278 (@lem3249051 _85070 s _33278 _33279 h1)). Qed.
Lemma lem3249056 {_85070 : Type'} (_33279 : _85070) (s : _85070 -> Prop) (_33278 : _85070) : term260 _85070 _33279 s _33278.
Proof. exact (fun h0 : _33278 = _33279 => @lem3249055 _85070 s _33278 _33279 h0). Qed.
Lemma lem3249058 (a : Prop) (b : Prop) : (a -> b) = (term261 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3249059 {_85070 : Type'} (_33279 : _85070) (s : _85070 -> Prop) (_33278 : _85070) : (term260 _85070 _33279 s _33278) = (term262 _85070 _33279 s _33278).
Proof. exact (@lem3249058 (_33278 = _33279) (term259 _85070 _33279 s _33278)). Qed.
Lemma lem3249060 {_85070 : Type'} (_33279 : _85070) (s : _85070 -> Prop) (_33278 : _85070) : term262 _85070 _33279 s _33278.
Proof. exact (EQ_MP (@lem3249059 _85070 _33279 s _33278) (@lem3249056 _85070 _33279 s _33278)). Qed.
Lemma lem3249064 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : s x.
Proof. exact (proj1 (@lem3248642 _85070 x s x' a h1)). Qed.
Lemma lem3249065 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term253 _85070 s x.
Proof. exact (fun h0 : term35 _85070 s x => @lem3249064 _85070 x s x' a h1). Qed.
Lemma lem3249067 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249068 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term253 _85070 s x) = (s x).
Proof. exact (@lem3249067 (s x)). Qed.
Lemma lem3249069 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : s x.
Proof. exact (EQ_MP (@lem3249068 _85070 s x) (@lem3249065 _85070 x s x' a h1)). Qed.
Lemma lem3249075 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3249076 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33254 : _85070) : (term62 _85070 s _33254 a) = (term263 _85070 a s _33254).
Proof. exact (@lem3249075 (_33254 = a) (term35 _85070 s _33254)). Qed.
Lemma lem3249084 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3249085 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33254 : _85070) : (term264 _85070 s _33254 a) = (term265 _85070 a s _33254).
Proof. exact (MK_COMB (@lem3249084) (@lem3249076 _85070 a s _33254)). Qed.
Lemma lem3249093 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33254 : _85070) : (term263 _85070 a s _33254) = (term263 _85070 a s _33254).
Proof. exact (eq_refl (term263 _85070 a s _33254)). Qed.
Lemma lem3249094 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33254 : _85070) : ((term62 _85070 s _33254 a) = (term263 _85070 a s _33254)) = ((term263 _85070 a s _33254) = (term263 _85070 a s _33254)).
Proof. exact (MK_COMB (@lem3249085 _85070 a s _33254) (@lem3249093 _85070 a s _33254)). Qed.
Lemma lem3249096 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3249097 (x : Prop) : (x = x) = True.
Proof. exact (@lem3249096 Prop x). Qed.
Lemma lem3249098 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33254 : _85070) : ((term263 _85070 a s _33254) = (term263 _85070 a s _33254)) = True.
Proof. exact (@lem3249097 (term263 _85070 a s _33254)). Qed.
Lemma lem3249099 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33254 : _85070) : ((term62 _85070 s _33254 a) = (term263 _85070 a s _33254)) = True.
Proof. exact (TRANS (@lem3249094 _85070 a s _33254) (@lem3249098 _85070 a s _33254)). Qed.
Lemma lem3249100 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33254 : _85070) : True = ((term62 _85070 s _33254 a) = (term263 _85070 a s _33254)).
Proof. exact (SYM (@lem3249099 _85070 a s _33254)). Qed.
Lemma lem3249101 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33254 : _85070) : (term62 _85070 s _33254 a) = (term263 _85070 a s _33254).
Proof. exact (EQ_MP (@lem3249100 _85070 a s _33254) (@lem0)). Qed.
Lemma lem3249102 {_85070 : Type'} (_33254 : _85070) (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term263 _85070 a s _33254.
Proof. exact (EQ_MP (@lem3249101 _85070 a s _33254) (@lem3248929 _85070 _33254 x s x' a h1)). Qed.
Lemma lem3249104 (b : Prop) (a : Prop) : (a \/ b) = (term266 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3249105 {_85070 : Type'} (s : _85070 -> Prop) (_33254 : _85070) (a : _85070) : (term263 _85070 a s _33254) = (term267 _85070 s _33254 a).
Proof. exact (@lem3249104 (term35 _85070 s _33254) (_33254 = a)). Qed.
Lemma lem3249107 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3249108 {_85070 : Type'} (s : _85070 -> Prop) (_33254 : _85070) : (term74 _85070 s _33254) = (s _33254).
Proof. exact (@lem3249107 (s _33254)). Qed.
Lemma lem3249109 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3249110 {_85070 : Type'} (s : _85070 -> Prop) (_33254 : _85070) : (term268 _85070 s _33254) = (term20 _85070 s _33254).
Proof. exact (MK_COMB (@lem3249109) (@lem3249108 _85070 s _33254)). Qed.
Lemma lem3249111 {_85070 : Type'} (_33254 : _85070) (a : _85070) : (_33254 = a) = (_33254 = a).
Proof. exact (eq_refl (_33254 = a)). Qed.
Lemma lem3249112 {_85070 : Type'} (s : _85070 -> Prop) (_33254 : _85070) (a : _85070) : (term267 _85070 s _33254 a) = (term28 _85070 s _33254 a).
Proof. exact (MK_COMB (@lem3249110 _85070 s _33254) (@lem3249111 _85070 _33254 a)). Qed.
Lemma lem3249113 {_85070 : Type'} (s : _85070 -> Prop) (_33254 : _85070) (a : _85070) : (term263 _85070 a s _33254) = (term28 _85070 s _33254 a).
Proof. exact (TRANS (@lem3249105 _85070 s _33254 a) (@lem3249112 _85070 s _33254 a)). Qed.
Lemma lem3249116 {_85070 : Type'} (_33254 : _85070) (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term28 _85070 s _33254 a.
Proof. exact (EQ_MP (@lem3249113 _85070 s _33254 a) (@lem3249102 _85070 _33254 x s x' a h1)). Qed.
Lemma lem3249117 {_85070 : Type'} (_33254 : _85070) (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term28 _85070 s _33254 a.
Proof. exact (@lem3249116 _85070 _33254 x s x' a h1). Qed.
Lemma lem3249118 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term28 _85070 s x a.
Proof. exact (@lem3249117 _85070 x x s x' a h1). Qed.
Lemma lem3249121 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : x = a.
Proof. exact (@lem3249118 _85070 x s x' a h1 (@lem3249069 _85070 x s x' a h1)). Qed.
Lemma lem3249122 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term269 _85070 x a.
Proof. exact (fun h0 : term244 _85070 x a => @lem3249121 _85070 x s x' a h1). Qed.
Lemma lem3249124 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249125 {_85070 : Type'} (x : _85070) (a : _85070) : (term269 _85070 x a) = (x = a).
Proof. exact (@lem3249124 (x = a)). Qed.
Lemma lem3249126 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : x = a.
Proof. exact (EQ_MP (@lem3249125 _85070 x a) (@lem3249122 _85070 x s x' a h1)). Qed.
Lemma lem3249128 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : s x.
Proof. exact (proj1 (@lem3248642 _85070 x s x' a h1)). Qed.
Lemma lem3249129 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term253 _85070 s x.
Proof. exact (fun h0 : term35 _85070 s x => @lem3249128 _85070 x s x' a h1). Qed.
Lemma lem3249131 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249132 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term253 _85070 s x) = (s x).
Proof. exact (@lem3249131 (s x)). Qed.
Lemma lem3249133 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : s x.
Proof. exact (EQ_MP (@lem3249132 _85070 s x) (@lem3249129 _85070 x s x' a h1)). Qed.
Lemma lem3249139 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3249140 {_85070 : Type'} (_33279 : _85070) (s : _85070 -> Prop) (_33278 : _85070) : (term262 _85070 _33279 s _33278) = (term270 _85070 _33279 s _33278).
Proof. exact (@lem3249139 (s _33279) (term244 _85070 _33278 _33279) (term35 _85070 s _33278)). Qed.
Lemma lem3249154 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3249155 {_85070 : Type'} (s : _85070 -> Prop) (_33278 : _85070) (_33279 : _85070) : (term271 _85070 _33279 s _33278) = (term242 _85070 s _33278 _33279).
Proof. exact (@lem3249154 (term35 _85070 s _33278) (term244 _85070 _33278 _33279)). Qed.
Lemma lem3249163 {_85070 : Type'} (s : _85070 -> Prop) (_33279 : _85070) : (term272 _85070 s _33279) = (term272 _85070 s _33279).
Proof. exact (eq_refl (term272 _85070 s _33279)). Qed.
Lemma lem3249164 {_85070 : Type'} (s : _85070 -> Prop) (_33278 : _85070) (_33279 : _85070) : (term270 _85070 _33279 s _33278) = (term273 _85070 s _33278 _33279).
Proof. exact (MK_COMB (@lem3249163 _85070 s _33279) (@lem3249155 _85070 s _33278 _33279)). Qed.
Lemma lem3249175 {_85070 : Type'} (s : _85070 -> Prop) (_33278 : _85070) (_33279 : _85070) : (term262 _85070 _33279 s _33278) = (term273 _85070 s _33278 _33279).
Proof. exact (TRANS (@lem3249140 _85070 _33279 s _33278) (@lem3249164 _85070 s _33278 _33279)). Qed.
Lemma lem3249176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3249177 {_85070 : Type'} (s : _85070 -> Prop) (_33278 : _85070) (_33279 : _85070) : (term274 _85070 _33279 s _33278) = (term275 _85070 s _33278 _33279).
Proof. exact (MK_COMB (@lem3249176) (@lem3249175 _85070 s _33278 _33279)). Qed.
Lemma lem3249191 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3249192 {_85070 : Type'} (s : _85070 -> Prop) (_33278 : _85070) (_33279 : _85070) : (term271 _85070 _33279 s _33278) = (term242 _85070 s _33278 _33279).
Proof. exact (@lem3249191 (term35 _85070 s _33278) (term244 _85070 _33278 _33279)). Qed.
Lemma lem3249200 {_85070 : Type'} (s : _85070 -> Prop) (_33279 : _85070) : (term272 _85070 s _33279) = (term272 _85070 s _33279).
Proof. exact (eq_refl (term272 _85070 s _33279)). Qed.
Lemma lem3249201 {_85070 : Type'} (s : _85070 -> Prop) (_33278 : _85070) (_33279 : _85070) : (term270 _85070 _33279 s _33278) = (term273 _85070 s _33278 _33279).
Proof. exact (MK_COMB (@lem3249200 _85070 s _33279) (@lem3249192 _85070 s _33278 _33279)). Qed.
Lemma lem3249212 {_85070 : Type'} (s : _85070 -> Prop) (_33278 : _85070) (_33279 : _85070) : ((term262 _85070 _33279 s _33278) = (term270 _85070 _33279 s _33278)) = ((term273 _85070 s _33278 _33279) = (term273 _85070 s _33278 _33279)).
Proof. exact (MK_COMB (@lem3249177 _85070 s _33278 _33279) (@lem3249201 _85070 s _33278 _33279)). Qed.
Lemma lem3249214 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3249215 (x : Prop) : (x = x) = True.
Proof. exact (@lem3249214 Prop x). Qed.
Lemma lem3249216 {_85070 : Type'} (s : _85070 -> Prop) (_33278 : _85070) (_33279 : _85070) : ((term273 _85070 s _33278 _33279) = (term273 _85070 s _33278 _33279)) = True.
Proof. exact (@lem3249215 (term273 _85070 s _33278 _33279)). Qed.
Lemma lem3249217 {_85070 : Type'} (_33279 : _85070) (s : _85070 -> Prop) (_33278 : _85070) : ((term262 _85070 _33279 s _33278) = (term270 _85070 _33279 s _33278)) = True.
Proof. exact (TRANS (@lem3249212 _85070 s _33278 _33279) (@lem3249216 _85070 s _33278 _33279)). Qed.
Lemma lem3249218 {_85070 : Type'} (_33279 : _85070) (s : _85070 -> Prop) (_33278 : _85070) : True = ((term262 _85070 _33279 s _33278) = (term270 _85070 _33279 s _33278)).
Proof. exact (SYM (@lem3249217 _85070 _33279 s _33278)). Qed.
Lemma lem3249219 {_85070 : Type'} (_33279 : _85070) (s : _85070 -> Prop) (_33278 : _85070) : (term262 _85070 _33279 s _33278) = (term270 _85070 _33279 s _33278).
Proof. exact (EQ_MP (@lem3249218 _85070 _33279 s _33278) (@lem0)). Qed.
Lemma lem3249220 {_85070 : Type'} (_33279 : _85070) (s : _85070 -> Prop) (_33278 : _85070) : term270 _85070 _33279 s _33278.
Proof. exact (EQ_MP (@lem3249219 _85070 _33279 s _33278) (@lem3249060 _85070 _33279 s _33278)). Qed.
Lemma lem3249222 (b : Prop) (a : Prop) : (a \/ b) = (term266 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3249223 {_85070 : Type'} (_33278 : _85070) (s : _85070 -> Prop) (_33279 : _85070) : (term270 _85070 _33279 s _33278) = (term276 _85070 _33278 s _33279).
Proof. exact (@lem3249222 (term271 _85070 _33279 s _33278) (s _33279)). Qed.
Lemma lem3249225 (a : Prop) (b : Prop) : (term277 a b) = (term278 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3249226 {_85070 : Type'} (_33279 : _85070) (s : _85070 -> Prop) (_33278 : _85070) : (term279 _85070 _33279 s _33278) = (term280 _85070 _33279 s _33278).
Proof. exact (@lem3249225 (term244 _85070 _33278 _33279) (term35 _85070 s _33278)). Qed.
Lemma lem3249228 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3249229 {_85070 : Type'} (_33278 : _85070) (_33279 : _85070) : (term281 _85070 _33278 _33279) = (_33278 = _33279).
Proof. exact (@lem3249228 (_33278 = _33279)). Qed.
Lemma lem3249230 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3249231 {_85070 : Type'} (_33278 : _85070) (_33279 : _85070) : (term282 _85070 _33278 _33279) = (term283 _85070 _33278 _33279).
Proof. exact (MK_COMB (@lem3249230) (@lem3249229 _85070 _33278 _33279)). Qed.
Lemma lem3249233 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3249234 {_85070 : Type'} (s : _85070 -> Prop) (_33278 : _85070) : (term74 _85070 s _33278) = (s _33278).
Proof. exact (@lem3249233 (s _33278)). Qed.
Lemma lem3249235 {_85070 : Type'} (_33279 : _85070) (s : _85070 -> Prop) (_33278 : _85070) : (term280 _85070 _33279 s _33278) = (term284 _85070 _33279 s _33278).
Proof. exact (MK_COMB (@lem3249231 _85070 _33278 _33279) (@lem3249234 _85070 s _33278)). Qed.
Lemma lem3249236 {_85070 : Type'} (_33279 : _85070) (s : _85070 -> Prop) (_33278 : _85070) : (term279 _85070 _33279 s _33278) = (term284 _85070 _33279 s _33278).
Proof. exact (TRANS (@lem3249226 _85070 _33279 s _33278) (@lem3249235 _85070 _33279 s _33278)). Qed.
Lemma lem3249237 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3249238 {_85070 : Type'} (_33279 : _85070) (s : _85070 -> Prop) (_33278 : _85070) : (term285 _85070 _33279 s _33278) = (term286 _85070 _33279 s _33278).
Proof. exact (MK_COMB (@lem3249237) (@lem3249236 _85070 _33279 s _33278)). Qed.
Lemma lem3249239 {_85070 : Type'} (s : _85070 -> Prop) (_33279 : _85070) : (s _33279) = (s _33279).
Proof. exact (eq_refl (s _33279)). Qed.
Lemma lem3249240 {_85070 : Type'} (_33278 : _85070) (s : _85070 -> Prop) (_33279 : _85070) : (term276 _85070 _33278 s _33279) = (term287 _85070 _33278 s _33279).
Proof. exact (MK_COMB (@lem3249238 _85070 _33279 s _33278) (@lem3249239 _85070 s _33279)). Qed.
Lemma lem3249241 {_85070 : Type'} (_33278 : _85070) (s : _85070 -> Prop) (_33279 : _85070) : (term270 _85070 _33279 s _33278) = (term287 _85070 _33278 s _33279).
Proof. exact (TRANS (@lem3249223 _85070 _33278 s _33279) (@lem3249240 _85070 _33278 s _33279)). Qed.
Lemma lem3249243 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term284 _85070 a s x.
Proof. exact (conj (@lem3249126 _85070 x s x' a h1) (@lem3249133 _85070 x s x' a h1)). Qed.
Lemma lem3249245 {_85070 : Type'} (_33278 : _85070) (s : _85070 -> Prop) (_33279 : _85070) : term287 _85070 _33278 s _33279.
Proof. exact (EQ_MP (@lem3249241 _85070 _33278 s _33279) (@lem3249220 _85070 _33279 s _33278)). Qed.
Lemma lem3249246 {_85070 : Type'} (_33278 : _85070) (s : _85070 -> Prop) (_33279 : _85070) : term287 _85070 _33278 s _33279.
Proof. exact (@lem3249245 _85070 _33278 s _33279). Qed.
Lemma lem3249247 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) : term287 _85070 x s a.
Proof. exact (@lem3249246 _85070 x s a). Qed.
Lemma lem3249250 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : s a.
Proof. exact (@lem3249247 _85070 x s a (@lem3249243 _85070 x s x' a h1)). Qed.
Lemma lem3249251 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term253 _85070 s a.
Proof. exact (fun h0 : term35 _85070 s a => @lem3249250 _85070 x s x' a h1). Qed.
Lemma lem3249253 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249254 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term253 _85070 s a) = (s a).
Proof. exact (@lem3249253 (s a)). Qed.
Lemma lem3249255 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : s a.
Proof. exact (EQ_MP (@lem3249254 _85070 s a) (@lem3249251 _85070 x s x' a h1)). Qed.
Lemma lem3249258 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3249260 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term35 _85070 s a) = (term255 _85070 s a).
Proof. exact (@lem3249258 (s a)). Qed.
Lemma lem3249263 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : x' = a) : term255 _85070 s a.
Proof. exact (EQ_MP (@lem3249260 _85070 s a) (@lem3248956 _85070 s x' a h1 h2)). Qed.
Lemma lem3249266 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : term180 _85070 x s x' a) (h3 : x' = a) : False.
Proof. exact (@lem3249263 _85070 s x' a h1 h3 (@lem3249255 _85070 x s x' a h2)). Qed.
Lemma lem3249267 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : term180 _85070 x s x' a) (h3 : x' = a) : term256.
Proof. exact (fun h0 : ~ False => @lem3249266 _85070 x s x' a h1 h2 h3). Qed.
Lemma lem3249269 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249270 : term256 = False.
Proof. exact (@lem3249269 False). Qed.
Lemma lem3249287 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3249288 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : s x') : term253 _85070 s x'.
Proof. exact (fun h0 : term35 _85070 s x' => @lem3249287 _85070 s x' h1). Qed.
Lemma lem3249290 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249291 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) : (term253 _85070 s x') = (s x').
Proof. exact (@lem3249290 (s x')). Qed.
Lemma lem3249292 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3249291 _85070 s x') (@lem3249288 _85070 s x' h1)). Qed.
Lemma lem3249298 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3249299 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33255 : _85070) : (term62 _85070 s _33255 a) = (term263 _85070 a s _33255).
Proof. exact (@lem3249298 (_33255 = a) (term35 _85070 s _33255)). Qed.
Lemma lem3249307 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3249308 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33255 : _85070) : (term264 _85070 s _33255 a) = (term265 _85070 a s _33255).
Proof. exact (MK_COMB (@lem3249307) (@lem3249299 _85070 a s _33255)). Qed.
Lemma lem3249316 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33255 : _85070) : (term263 _85070 a s _33255) = (term263 _85070 a s _33255).
Proof. exact (eq_refl (term263 _85070 a s _33255)). Qed.
Lemma lem3249317 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33255 : _85070) : ((term62 _85070 s _33255 a) = (term263 _85070 a s _33255)) = ((term263 _85070 a s _33255) = (term263 _85070 a s _33255)).
Proof. exact (MK_COMB (@lem3249308 _85070 a s _33255) (@lem3249316 _85070 a s _33255)). Qed.
Lemma lem3249319 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3249320 (x : Prop) : (x = x) = True.
Proof. exact (@lem3249319 Prop x). Qed.
Lemma lem3249321 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33255 : _85070) : ((term263 _85070 a s _33255) = (term263 _85070 a s _33255)) = True.
Proof. exact (@lem3249320 (term263 _85070 a s _33255)). Qed.
Lemma lem3249322 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33255 : _85070) : ((term62 _85070 s _33255 a) = (term263 _85070 a s _33255)) = True.
Proof. exact (TRANS (@lem3249317 _85070 a s _33255) (@lem3249321 _85070 a s _33255)). Qed.
Lemma lem3249323 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33255 : _85070) : True = ((term62 _85070 s _33255 a) = (term263 _85070 a s _33255)).
Proof. exact (SYM (@lem3249322 _85070 a s _33255)). Qed.
Lemma lem3249324 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33255 : _85070) : (term62 _85070 s _33255 a) = (term263 _85070 a s _33255).
Proof. exact (EQ_MP (@lem3249323 _85070 a s _33255) (@lem0)). Qed.
Lemma lem3249325 {_85070 : Type'} (_33255 : _85070) (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term263 _85070 a s _33255.
Proof. exact (EQ_MP (@lem3249324 _85070 a s _33255) (@lem3248861 _85070 _33255 x s x' a h1)). Qed.
Lemma lem3249327 (b : Prop) (a : Prop) : (a \/ b) = (term266 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3249328 {_85070 : Type'} (s : _85070 -> Prop) (_33255 : _85070) (a : _85070) : (term263 _85070 a s _33255) = (term267 _85070 s _33255 a).
Proof. exact (@lem3249327 (term35 _85070 s _33255) (_33255 = a)). Qed.
Lemma lem3249330 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3249331 {_85070 : Type'} (s : _85070 -> Prop) (_33255 : _85070) : (term74 _85070 s _33255) = (s _33255).
Proof. exact (@lem3249330 (s _33255)). Qed.
Lemma lem3249332 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3249333 {_85070 : Type'} (s : _85070 -> Prop) (_33255 : _85070) : (term268 _85070 s _33255) = (term20 _85070 s _33255).
Proof. exact (MK_COMB (@lem3249332) (@lem3249331 _85070 s _33255)). Qed.
Lemma lem3249334 {_85070 : Type'} (_33255 : _85070) (a : _85070) : (_33255 = a) = (_33255 = a).
Proof. exact (eq_refl (_33255 = a)). Qed.
Lemma lem3249335 {_85070 : Type'} (s : _85070 -> Prop) (_33255 : _85070) (a : _85070) : (term267 _85070 s _33255 a) = (term28 _85070 s _33255 a).
Proof. exact (MK_COMB (@lem3249333 _85070 s _33255) (@lem3249334 _85070 _33255 a)). Qed.
Lemma lem3249336 {_85070 : Type'} (s : _85070 -> Prop) (_33255 : _85070) (a : _85070) : (term263 _85070 a s _33255) = (term28 _85070 s _33255 a).
Proof. exact (TRANS (@lem3249328 _85070 s _33255 a) (@lem3249335 _85070 s _33255 a)). Qed.
Lemma lem3249339 {_85070 : Type'} (_33255 : _85070) (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term28 _85070 s _33255 a.
Proof. exact (EQ_MP (@lem3249336 _85070 s _33255 a) (@lem3249325 _85070 _33255 x s x' a h1)). Qed.
Lemma lem3249340 {_85070 : Type'} (_33255 : _85070) (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term28 _85070 s _33255 a.
Proof. exact (@lem3249339 _85070 _33255 x s x' a h1). Qed.
Lemma lem3249341 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : term28 _85070 s x' a.
Proof. exact (@lem3249340 _85070 x' x s x' a h1). Qed.
Lemma lem3249344 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : s x') (h2 : term180 _85070 x s x' a) : x' = a.
Proof. exact (@lem3249341 _85070 x s x' a h2 (@lem3249292 _85070 s x' h1)). Qed.
Lemma lem3249345 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : s x') (h2 : term180 _85070 x s x' a) : term269 _85070 x' a.
Proof. exact (fun h0 : term244 _85070 x' a => @lem3249344 _85070 x s x' a h1 h2). Qed.
Lemma lem3249347 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249348 {_85070 : Type'} (x' : _85070) (a : _85070) : (term269 _85070 x' a) = (x' = a).
Proof. exact (@lem3249347 (x' = a)). Qed.
Lemma lem3249349 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : s x') (h2 : term180 _85070 x s x' a) : x' = a.
Proof. exact (EQ_MP (@lem3249348 _85070 x' a) (@lem3249345 _85070 x s x' a h1 h2)). Qed.
Lemma lem3249352 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3249354 {_85070 : Type'} (x' : _85070) (a : _85070) : (term244 _85070 x' a) = (term288 _85070 x' a).
Proof. exact (@lem3249352 (x' = a)). Qed.
Lemma lem3249357 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) : term288 _85070 x' a.
Proof. exact (EQ_MP (@lem3249354 _85070 x' a) (@lem3248865 _85070 x' a h1)). Qed.
Lemma lem3249360 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : s x') (h3 : term180 _85070 x s x' a) : False.
Proof. exact (@lem3249357 _85070 x' a h1 (@lem3249349 _85070 x s x' a h2 h3)). Qed.
Lemma lem3249361 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : s x') (h3 : term180 _85070 x s x' a) : term256.
Proof. exact (fun h0 : ~ False => @lem3249360 _85070 x s x' a h1 h2 h3). Qed.
Lemma lem3249363 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249364 : term256 = False.
Proof. exact (@lem3249363 False). Qed.
Lemma lem3249365 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : s x') (h3 : term180 _85070 x s x' a) : False.
Proof. exact (EQ_MP (@lem3249364) (@lem3249361 _85070 x s x' a h1 h2 h3)). Qed.
Lemma lem3249381 {_85070 : Type'} (x : _85070) : x = x.
Proof. exact (@lem21386 _85070 x). Qed.
Lemma lem3249382 {_85070 : Type'} (x : _85070) : x = x.
Proof. exact (@lem3249381 _85070 x). Qed.
Lemma lem3249383 {_85070 : Type'} (a : _85070) : a = a.
Proof. exact (@lem3249382 _85070 a). Qed.
Lemma lem3249384 {_85070 : Type'} (a : _85070) : term289 _85070 a.
Proof. exact (fun h0 : term250 _85070 a => @lem3249383 _85070 a). Qed.
Lemma lem3249386 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249387 {_85070 : Type'} (a : _85070) : (term289 _85070 a) = (a = a).
Proof. exact (@lem3249386 (a = a)). Qed.
Lemma lem3249388 {_85070 : Type'} (a : _85070) : a = a.
Proof. exact (EQ_MP (@lem3249387 _85070 a) (@lem3249384 _85070 a)). Qed.
Lemma lem3249391 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3249393 {_85070 : Type'} (a : _85070) : (term250 _85070 a) = (term290 _85070 a).
Proof. exact (@lem3249391 (a = a)). Qed.
Lemma lem3249396 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : term290 _85070 a.
Proof. exact (EQ_MP (@lem3249393 _85070 a) (@lem3249011 _85070 x' a h1 h2)). Qed.
Lemma lem3249399 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : False.
Proof. exact (@lem3249396 _85070 x' a h1 h2 (@lem3249388 _85070 a)). Qed.
Lemma lem3249400 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : term256.
Proof. exact (fun h0 : ~ False => @lem3249399 _85070 x' a h1 h2). Qed.
Lemma lem3249402 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249403 : term256 = False.
Proof. exact (@lem3249402 False). Qed.
Lemma lem3249420 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term198 _85070 x s a) : s x.
Proof. exact (proj1 (@lem3248655 _85070 x s a h1)). Qed.
Lemma lem3249421 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term198 _85070 x s a) : term253 _85070 s x.
Proof. exact (fun h0 : term35 _85070 s x => @lem3249420 _85070 x s a h1). Qed.
Lemma lem3249423 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249424 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term253 _85070 s x) = (s x).
Proof. exact (@lem3249423 (s x)). Qed.
Lemma lem3249425 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term198 _85070 x s a) : s x.
Proof. exact (EQ_MP (@lem3249424 _85070 s x) (@lem3249421 _85070 x s a h1)). Qed.
Lemma lem3249428 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3249430 {_85070 : Type'} (s : _85070 -> Prop) (_33257 : _85070) : (term35 _85070 s _33257) = (term255 _85070 s _33257).
Proof. exact (@lem3249428 (s _33257)). Qed.
Lemma lem3249433 {_85070 : Type'} (_33257 : _85070) (s : _85070 -> Prop) (h1 : term38 _85070 s) : term255 _85070 s _33257.
Proof. exact (EQ_MP (@lem3249430 _85070 s _33257) (@lem3248885 _85070 _33257 s h1)). Qed.
Lemma lem3249434 {_85070 : Type'} (_33257 : _85070) (s : _85070 -> Prop) (h1 : term38 _85070 s) : term255 _85070 s _33257.
Proof. exact (@lem3249433 _85070 _33257 s h1). Qed.
Lemma lem3249435 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (h1 : term38 _85070 s) : term255 _85070 s x.
Proof. exact (@lem3249434 _85070 x s h1). Qed.
Lemma lem3249438 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term38 _85070 s) (h2 : term198 _85070 x s a) : False.
Proof. exact (@lem3249435 _85070 x s h1 (@lem3249425 _85070 x s a h2)). Qed.
Lemma lem3249439 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term38 _85070 s) (h2 : term198 _85070 x s a) : term256.
Proof. exact (fun h0 : ~ False => @lem3249438 _85070 x s a h1 h2). Qed.
Lemma lem3249441 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249442 : term256 = False.
Proof. exact (@lem3249441 False). Qed.
Lemma lem3249443 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term38 _85070 s) (h2 : term198 _85070 x s a) : False.
Proof. exact (EQ_MP (@lem3249442) (@lem3249439 _85070 x s a h1 h2)). Qed.
Lemma lem3249459 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term198 _85070 x s a) : s x.
Proof. exact (proj1 (@lem3248655 _85070 x s a h1)). Qed.
Lemma lem3249460 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term198 _85070 x s a) : term253 _85070 s x.
Proof. exact (fun h0 : term35 _85070 s x => @lem3249459 _85070 x s a h1). Qed.
Lemma lem3249462 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249463 {_85070 : Type'} (s : _85070 -> Prop) (x : _85070) : (term253 _85070 s x) = (s x).
Proof. exact (@lem3249462 (s x)). Qed.
Lemma lem3249464 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term198 _85070 x s a) : s x.
Proof. exact (EQ_MP (@lem3249463 _85070 s x) (@lem3249460 _85070 x s a h1)). Qed.
Lemma lem3249470 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3249471 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33259 : _85070) : (term62 _85070 s _33259 a) = (term263 _85070 a s _33259).
Proof. exact (@lem3249470 (_33259 = a) (term35 _85070 s _33259)). Qed.
Lemma lem3249479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3249480 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33259 : _85070) : (term264 _85070 s _33259 a) = (term265 _85070 a s _33259).
Proof. exact (MK_COMB (@lem3249479) (@lem3249471 _85070 a s _33259)). Qed.
Lemma lem3249488 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33259 : _85070) : (term263 _85070 a s _33259) = (term263 _85070 a s _33259).
Proof. exact (eq_refl (term263 _85070 a s _33259)). Qed.
Lemma lem3249489 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33259 : _85070) : ((term62 _85070 s _33259 a) = (term263 _85070 a s _33259)) = ((term263 _85070 a s _33259) = (term263 _85070 a s _33259)).
Proof. exact (MK_COMB (@lem3249480 _85070 a s _33259) (@lem3249488 _85070 a s _33259)). Qed.
Lemma lem3249491 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3249492 (x : Prop) : (x = x) = True.
Proof. exact (@lem3249491 Prop x). Qed.
Lemma lem3249493 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33259 : _85070) : ((term263 _85070 a s _33259) = (term263 _85070 a s _33259)) = True.
Proof. exact (@lem3249492 (term263 _85070 a s _33259)). Qed.
Lemma lem3249494 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33259 : _85070) : ((term62 _85070 s _33259 a) = (term263 _85070 a s _33259)) = True.
Proof. exact (TRANS (@lem3249489 _85070 a s _33259) (@lem3249493 _85070 a s _33259)). Qed.
Lemma lem3249495 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33259 : _85070) : True = ((term62 _85070 s _33259 a) = (term263 _85070 a s _33259)).
Proof. exact (SYM (@lem3249494 _85070 a s _33259)). Qed.
Lemma lem3249496 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) (_33259 : _85070) : (term62 _85070 s _33259 a) = (term263 _85070 a s _33259).
Proof. exact (EQ_MP (@lem3249495 _85070 a s _33259) (@lem0)). Qed.
Lemma lem3249497 {_85070 : Type'} (_33259 : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term133 _85070 s a) : term263 _85070 a s _33259.
Proof. exact (EQ_MP (@lem3249496 _85070 a s _33259) (@lem3248901 _85070 _33259 s a h1)). Qed.
Lemma lem3249499 (b : Prop) (a : Prop) : (a \/ b) = (term266 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3249500 {_85070 : Type'} (s : _85070 -> Prop) (_33259 : _85070) (a : _85070) : (term263 _85070 a s _33259) = (term267 _85070 s _33259 a).
Proof. exact (@lem3249499 (term35 _85070 s _33259) (_33259 = a)). Qed.
Lemma lem3249502 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3249503 {_85070 : Type'} (s : _85070 -> Prop) (_33259 : _85070) : (term74 _85070 s _33259) = (s _33259).
Proof. exact (@lem3249502 (s _33259)). Qed.
Lemma lem3249504 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3249505 {_85070 : Type'} (s : _85070 -> Prop) (_33259 : _85070) : (term268 _85070 s _33259) = (term20 _85070 s _33259).
Proof. exact (MK_COMB (@lem3249504) (@lem3249503 _85070 s _33259)). Qed.
Lemma lem3249506 {_85070 : Type'} (_33259 : _85070) (a : _85070) : (_33259 = a) = (_33259 = a).
Proof. exact (eq_refl (_33259 = a)). Qed.
Lemma lem3249507 {_85070 : Type'} (s : _85070 -> Prop) (_33259 : _85070) (a : _85070) : (term267 _85070 s _33259 a) = (term28 _85070 s _33259 a).
Proof. exact (MK_COMB (@lem3249505 _85070 s _33259) (@lem3249506 _85070 _33259 a)). Qed.
Lemma lem3249508 {_85070 : Type'} (s : _85070 -> Prop) (_33259 : _85070) (a : _85070) : (term263 _85070 a s _33259) = (term28 _85070 s _33259 a).
Proof. exact (TRANS (@lem3249500 _85070 s _33259 a) (@lem3249507 _85070 s _33259 a)). Qed.
Lemma lem3249511 {_85070 : Type'} (_33259 : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term133 _85070 s a) : term28 _85070 s _33259 a.
Proof. exact (EQ_MP (@lem3249508 _85070 s _33259 a) (@lem3249497 _85070 _33259 s a h1)). Qed.
Lemma lem3249512 {_85070 : Type'} (_33259 : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term133 _85070 s a) : term28 _85070 s _33259 a.
Proof. exact (@lem3249511 _85070 _33259 s a h1). Qed.
Lemma lem3249513 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term133 _85070 s a) : term28 _85070 s x a.
Proof. exact (@lem3249512 _85070 x s a h1). Qed.
Lemma lem3249516 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term133 _85070 s a) (h2 : term198 _85070 x s a) : x = a.
Proof. exact (@lem3249513 _85070 x s a h1 (@lem3249464 _85070 x s a h2)). Qed.
Lemma lem3249517 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term133 _85070 s a) (h2 : term198 _85070 x s a) : term269 _85070 x a.
Proof. exact (fun h0 : term244 _85070 x a => @lem3249516 _85070 x s a h1 h2). Qed.
Lemma lem3249519 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249520 {_85070 : Type'} (x : _85070) (a : _85070) : (term269 _85070 x a) = (x = a).
Proof. exact (@lem3249519 (x = a)). Qed.
Lemma lem3249521 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term133 _85070 s a) (h2 : term198 _85070 x s a) : x = a.
Proof. exact (EQ_MP (@lem3249520 _85070 x a) (@lem3249517 _85070 x s a h1 h2)). Qed.
Lemma lem3249524 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3249526 {_85070 : Type'} (x : _85070) (a : _85070) : (term244 _85070 x a) = (term288 _85070 x a).
Proof. exact (@lem3249524 (x = a)). Qed.
Lemma lem3249529 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term198 _85070 x s a) : term288 _85070 x a.
Proof. exact (EQ_MP (@lem3249526 _85070 x a) (@lem3248889 _85070 x s a h1)). Qed.
Lemma lem3249532 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term133 _85070 s a) (h2 : term198 _85070 x s a) : False.
Proof. exact (@lem3249529 _85070 x s a h2 (@lem3249521 _85070 x s a h1 h2)). Qed.
Lemma lem3249533 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term133 _85070 s a) (h2 : term198 _85070 x s a) : term256.
Proof. exact (fun h0 : ~ False => @lem3249532 _85070 x s a h1 h2). Qed.
Lemma lem3249535 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3249536 : term256 = False.
Proof. exact (@lem3249535 False). Qed.
Lemma lem3249537 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term133 _85070 s a) (h2 : term198 _85070 x s a) : False.
Proof. exact (EQ_MP (@lem3249536) (@lem3249533 _85070 x s a h1 h2)). Qed.
Lemma lem3249538 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem3249403) (@lem3249400 _85070 x' a h1 h2)). Qed.
Lemma lem3249539 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : term180 _85070 x s x' a) (h3 : x' = a) : False.
Proof. exact (EQ_MP (@lem3249270) (@lem3249267 _85070 x s x' a h1 h2 h3)). Qed.
Lemma lem3249540 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : (x' = a) = False.
Proof. exact (prop_ext (fun h3 : x' = a => @lem3249538 _85070 x' a h1 h2) (fun h3 : False => @lem3248879 _85070 x' a h2)). Qed.
Lemma lem3249541 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem3249540 _85070 x' a h1 h2) (@lem3248879 _85070 x' a h2)). Qed.
Lemma lem3249542 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : (term244 _85070 x' a) = False.
Proof. exact (prop_ext (fun h3 : term244 _85070 x' a => @lem3249541 _85070 x' a h1 h2) (fun h3 : False => @lem3248877 _85070 x' a h1)). Qed.
Lemma lem3249543 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem3249542 _85070 x' a h1 h2) (@lem3248877 _85070 x' a h1)). Qed.
Lemma lem3249544 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : s x') (h3 : term180 _85070 x s x' a) : (s x') = False.
Proof. exact (prop_ext (fun h4 : s x' => @lem3249365 _85070 x s x' a h1 h2 h3) (fun h4 : False => @lem3248867 _85070 s x' h2)). Qed.
Lemma lem3249545 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : s x') (h3 : term180 _85070 x s x' a) : False.
Proof. exact (EQ_MP (@lem3249544 _85070 x s x' a h1 h2 h3) (@lem3248867 _85070 s x' h2)). Qed.
Lemma lem3249546 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : s x') (h3 : term180 _85070 x s x' a) : (term244 _85070 x' a) = False.
Proof. exact (prop_ext (fun h4 : term244 _85070 x' a => @lem3249545 _85070 x s x' a h1 h2 h3) (fun h4 : False => @lem3248865 _85070 x' a h1)). Qed.
Lemma lem3249547 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : s x') (h3 : term180 _85070 x s x' a) : False.
Proof. exact (EQ_MP (@lem3249546 _85070 x s x' a h1 h2 h3) (@lem3248865 _85070 x' a h1)). Qed.
Lemma lem3249548 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : term180 _85070 x s x' a) (h3 : x' = a) : (x' = a) = False.
Proof. exact (prop_ext (fun h4 : x' = a => @lem3249539 _85070 x s x' a h1 h2 h3) (fun h4 : False => @lem3248855 _85070 x' a h3)). Qed.
Lemma lem3249549 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : term180 _85070 x s x' a) (h3 : x' = a) : False.
Proof. exact (EQ_MP (@lem3249548 _85070 x s x' a h1 h2 h3) (@lem3248855 _85070 x' a h3)). Qed.
Lemma lem3249550 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : term180 _85070 x s x' a) (h3 : x' = a) : (term35 _85070 s x') = False.
Proof. exact (prop_ext (fun h4 : term35 _85070 s x' => @lem3249549 _85070 x s x' a h1 h2 h3) (fun h4 : False => @lem3248853 _85070 s x' h1)). Qed.
Lemma lem3249551 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : term180 _85070 x s x' a) (h3 : x' = a) : False.
Proof. exact (EQ_MP (@lem3249550 _85070 x s x' a h1 h2 h3) (@lem3248853 _85070 s x' h1)). Qed.
Lemma lem3249552 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3249048 _85070 s x' h1 h2) (fun h3 : False => @lem3248843 _85070 s x' h2)). Qed.
Lemma lem3249553 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3249552 _85070 s x' h1 h2) (@lem3248843 _85070 s x' h2)). Qed.
Lemma lem3249554 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') (h2 : s x') : (term35 _85070 s x') = False.
Proof. exact (prop_ext (fun h3 : term35 _85070 s x' => @lem3249553 _85070 s x' h1 h2) (fun h3 : False => @lem3248841 _85070 s x' h1)). Qed.
Lemma lem3249555 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3249554 _85070 s x' h1 h2) (@lem3248841 _85070 s x' h1)). Qed.
Lemma lem3249556 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : (x' = a) = False.
Proof. exact (prop_ext (fun h3 : x' = a => @lem3249543 _85070 x' a h1 h2) (fun h3 : False => @lem3248761 _85070 x' a h2)). Qed.
Lemma lem3249557 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem3249556 _85070 x' a h1 h2) (@lem3248761 _85070 x' a h2)). Qed.
Lemma lem3249558 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : (term244 _85070 x' a) = False.
Proof. exact (prop_ext (fun h3 : term244 _85070 x' a => @lem3249557 _85070 x' a h1 h2) (fun h3 : False => @lem3248757 _85070 x' a h1)). Qed.
Lemma lem3249559 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem3249558 _85070 x' a h1 h2) (@lem3248757 _85070 x' a h1)). Qed.
Lemma lem3249560 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : s x') (h3 : term180 _85070 x s x' a) : (s x') = False.
Proof. exact (prop_ext (fun h4 : s x' => @lem3249547 _85070 x s x' a h1 h2 h3) (fun h4 : False => @lem3248736 _85070 s x' h2)). Qed.
Lemma lem3249561 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : s x') (h3 : term180 _85070 x s x' a) : False.
Proof. exact (EQ_MP (@lem3249560 _85070 x s x' a h1 h2 h3) (@lem3248736 _85070 s x' h2)). Qed.
Lemma lem3249562 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : s x') (h3 : term180 _85070 x s x' a) : (term244 _85070 x' a) = False.
Proof. exact (prop_ext (fun h4 : term244 _85070 x' a => @lem3249561 _85070 x s x' a h1 h2 h3) (fun h4 : False => @lem3248732 _85070 x' a h1)). Qed.
Lemma lem3249563 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : s x') (h3 : term180 _85070 x s x' a) : False.
Proof. exact (EQ_MP (@lem3249562 _85070 x s x' a h1 h2 h3) (@lem3248732 _85070 x' a h1)). Qed.
Lemma lem3249564 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : term180 _85070 x s x' a) (h3 : x' = a) : (x' = a) = False.
Proof. exact (prop_ext (fun h4 : x' = a => @lem3249551 _85070 x s x' a h1 h2 h3) (fun h4 : False => @lem3248711 _85070 x' a h3)). Qed.
Lemma lem3249565 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : term180 _85070 x s x' a) (h3 : x' = a) : False.
Proof. exact (EQ_MP (@lem3249564 _85070 x s x' a h1 h2 h3) (@lem3248711 _85070 x' a h3)). Qed.
Lemma lem3249566 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : term180 _85070 x s x' a) (h3 : x' = a) : (term35 _85070 s x') = False.
Proof. exact (prop_ext (fun h4 : term35 _85070 s x' => @lem3249565 _85070 x s x' a h1 h2 h3) (fun h4 : False => @lem3248707 _85070 s x' h1)). Qed.
Lemma lem3249567 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : term180 _85070 x s x' a) (h3 : x' = a) : False.
Proof. exact (EQ_MP (@lem3249566 _85070 x s x' a h1 h2 h3) (@lem3248707 _85070 s x' h1)). Qed.
Lemma lem3249568 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3249555 _85070 s x' h1 h2) (fun h3 : False => @lem3248686 _85070 s x' h2)). Qed.
Lemma lem3249569 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3249568 _85070 s x' h1 h2) (@lem3248686 _85070 s x' h2)). Qed.
Lemma lem3249570 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') (h2 : s x') : (term35 _85070 s x') = False.
Proof. exact (prop_ext (fun h3 : term35 _85070 s x' => @lem3249569 _85070 s x' h1 h2) (fun h3 : False => @lem3248682 _85070 s x' h1)). Qed.
Lemma lem3249571 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3249570 _85070 s x' h1 h2) (@lem3248682 _85070 s x' h1)). Qed.
Lemma lem3249572 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term38 _85070 s) (h2 : term198 _85070 x s a) : (term38 _85070 s) = False.
Proof. exact (prop_ext (fun h3 : term38 _85070 s => @lem3249443 _85070 x s a h1 h2) (fun h3 : False => @lem3248776 _85070 s h1)). Qed.
Lemma lem3249573 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term38 _85070 s) (h2 : term198 _85070 x s a) : False.
Proof. exact (EQ_MP (@lem3249572 _85070 x s a h1 h2) (@lem3248776 _85070 s h1)). Qed.
Lemma lem3249574 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : (x' = a) = False.
Proof. exact (prop_ext (fun h3 : x' = a => @lem3249559 _85070 x' a h1 h2) (fun h3 : False => @lem3248761 _85070 x' a h2)). Qed.
Lemma lem3249575 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem3249574 _85070 x' a h1 h2) (@lem3248761 _85070 x' a h2)). Qed.
Lemma lem3249576 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : (term244 _85070 x' a) = False.
Proof. exact (prop_ext (fun h3 : term244 _85070 x' a => @lem3249575 _85070 x' a h1 h2) (fun h3 : False => @lem3248757 _85070 x' a h1)). Qed.
Lemma lem3249577 {_85070 : Type'} (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem3249576 _85070 x' a h1 h2) (@lem3248757 _85070 x' a h1)). Qed.
Lemma lem3249578 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : s x') (h3 : term180 _85070 x s x' a) : (s x') = False.
Proof. exact (prop_ext (fun h4 : s x' => @lem3249563 _85070 x s x' a h1 h2 h3) (fun h4 : False => @lem3248736 _85070 s x' h2)). Qed.
Lemma lem3249579 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : s x') (h3 : term180 _85070 x s x' a) : False.
Proof. exact (EQ_MP (@lem3249578 _85070 x s x' a h1 h2 h3) (@lem3248736 _85070 s x' h2)). Qed.
Lemma lem3249580 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : s x') (h3 : term180 _85070 x s x' a) : (term244 _85070 x' a) = False.
Proof. exact (prop_ext (fun h4 : term244 _85070 x' a => @lem3249579 _85070 x s x' a h1 h2 h3) (fun h4 : False => @lem3248732 _85070 x' a h1)). Qed.
Lemma lem3249581 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : s x') (h3 : term180 _85070 x s x' a) : False.
Proof. exact (EQ_MP (@lem3249580 _85070 x s x' a h1 h2 h3) (@lem3248732 _85070 x' a h1)). Qed.
Lemma lem3249582 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : term180 _85070 x s x' a) (h3 : x' = a) : (x' = a) = False.
Proof. exact (prop_ext (fun h4 : x' = a => @lem3249567 _85070 x s x' a h1 h2 h3) (fun h4 : False => @lem3248711 _85070 x' a h3)). Qed.
Lemma lem3249583 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : term180 _85070 x s x' a) (h3 : x' = a) : False.
Proof. exact (EQ_MP (@lem3249582 _85070 x s x' a h1 h2 h3) (@lem3248711 _85070 x' a h3)). Qed.
Lemma lem3249584 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : term180 _85070 x s x' a) (h3 : x' = a) : (term35 _85070 s x') = False.
Proof. exact (prop_ext (fun h4 : term35 _85070 s x' => @lem3249583 _85070 x s x' a h1 h2 h3) (fun h4 : False => @lem3248707 _85070 s x' h1)). Qed.
Lemma lem3249585 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : term180 _85070 x s x' a) (h3 : x' = a) : False.
Proof. exact (EQ_MP (@lem3249584 _85070 x s x' a h1 h2 h3) (@lem3248707 _85070 s x' h1)). Qed.
Lemma lem3249586 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3249571 _85070 s x' h1 h2) (fun h3 : False => @lem3248686 _85070 s x' h2)). Qed.
Lemma lem3249587 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3249586 _85070 s x' h1 h2) (@lem3248686 _85070 s x' h2)). Qed.
Lemma lem3249588 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') (h2 : s x') : (term35 _85070 s x') = False.
Proof. exact (prop_ext (fun h3 : term35 _85070 s x' => @lem3249587 _85070 s x' h1 h2) (fun h3 : False => @lem3248682 _85070 s x' h1)). Qed.
Lemma lem3249589 {_85070 : Type'} (s : _85070 -> Prop) (x' : _85070) (h1 : term35 _85070 s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3249588 _85070 s x' h1 h2) (@lem3248682 _85070 s x' h1)). Qed.
Lemma lem3249590 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term198 _85070 x s a) : False.
Proof. exact (or_elim (@lem3248654 _85070 x s a h1) (fun h0 : term38 _85070 s => @lem3249573 _85070 x s a h0 h1) (fun h0 : term133 _85070 s a => @lem3249537 _85070 x s a h0 h1)). Qed.
Lemma lem3249591 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term244 _85070 x' a) (h2 : term180 _85070 x s x' a) : False.
Proof. exact (or_elim (@lem3248647 _85070 x s x' a h2) (fun h0 : s x' => @lem3249581 _85070 x s x' a h1 h0 h2) (fun h0 : x' = a => @lem3249577 _85070 x' a h1 h0)). Qed.
Lemma lem3249592 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term35 _85070 s x') (h2 : term180 _85070 x s x' a) : False.
Proof. exact (or_elim (@lem3248647 _85070 x s x' a h2) (fun h0 : s x' => @lem3249589 _85070 s x' h1 h0) (fun h0 : x' = a => @lem3249585 _85070 x s x' a h1 h2 h0)). Qed.
Lemma lem3249593 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (x' : _85070) (a : _85070) (h1 : term180 _85070 x s x' a) : False.
Proof. exact (or_elim (@lem3248646 _85070 x s x' a h1) (fun h0 : term35 _85070 s x' => @lem3249592 _85070 x s x' a h0 h1) (fun h0 : term244 _85070 x' a => @lem3249591 _85070 x s x' a h0 h1)). Qed.
Lemma lem3249594 {_85070 : Type'} (x' : _85070) (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term236 _85070 x' x s a) : False.
Proof. exact (or_elim (@lem3248639 _85070 x' x s a h1) (fun h0 : term180 _85070 x s x' a => @lem3249593 _85070 x s x' a h0) (fun h0 : term198 _85070 x s a => @lem3249590 _85070 x s a h0)). Qed.
Lemma lem3249595 {_85070 : Type'} (x' : _85070) (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term236 _85070 x' x s a) : (term236 _85070 x' x s a) = False.
Proof. exact (prop_ext (fun h2 : term236 _85070 x' x s a => @lem3249594 _85070 x' x s a h1) (fun h2 : False => @lem3248639 _85070 x' x s a h1)). Qed.
Lemma lem3249596 {_85070 : Type'} (x' : _85070) (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term236 _85070 x' x s a) : False.
Proof. exact (EQ_MP (@lem3249595 _85070 x' x s a h1) (@lem3248639 _85070 x' x s a h1)). Qed.
Lemma lem3249597 {_85070 : Type'} (x : _85070) (s : _85070 -> Prop) (a : _85070) (h1 : term239 _85070 x s a) : False.
Proof. exact (ex_elim (@lem3248518 _85070 x s a h1) (fun x' : _85070 => fun h0 : term238 _85070 x s a x' => @lem3249596 _85070 x' x s a h0)). Qed.
Lemma lem3249598 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term46 _85070 s a) : False.
Proof. exact (ex_elim (@lem3248517 _85070 s a h1) (fun x : _85070 => fun h0 : term240 _85070 s a x => @lem3249597 _85070 x s a h0)). Qed.
Lemma lem3249599 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term46 _85070 s a) : (term46 _85070 s a) = False.
Proof. exact (prop_ext (fun h2 : term46 _85070 s a => @lem3249598 _85070 s a h1) (fun h2 : False => @lem3248013 _85070 s a h1)). Qed.
Lemma lem3249600 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term46 _85070 s a) : False.
Proof. exact (EQ_MP (@lem3249599 _85070 s a h1) (@lem3248013 _85070 s a h1)). Qed.
Lemma lem3249601 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : term45 _85070 s a.
Proof. exact (fun h0 : term46 _85070 s a => @lem3249600 _85070 s a h0). Qed.
Lemma lem3249602 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term31 _85070 s a) = (term43 _85070 s a).
Proof. exact (EQ_MP (@lem3248012 _85070 s a) (@lem3249601 _85070 s a)). Qed.
Lemma lem3249607 {_85070 : Type'} (a : _85070) : term55 _85070 a.
Proof. exact (fun s : _85070 -> Prop => @lem3249602 _85070 s a). Qed.
Lemma lem3249612 {_85070 : Type'} : term59 _85070.
Proof. exact (fun a : _85070 => @lem3249607 _85070 a). Qed.
Lemma lem3249613 {_85070 : Type'} : term58 _85070.
Proof. exact (EQ_MP (@lem3248008 _85070) (@lem3249612 _85070)). Qed.
Lemma lem3249614 {_85070 : Type'} (a : _85070) : term291 _85070 a.
Proof. exact (@lem3249613 _85070 a). Qed.
Lemma lem3249615 {_85070 : Type'} (a : _85070) : (term291 _85070 a) = (term54 _85070 a).
Proof. exact (eq_refl (term291 _85070 a)). Qed.
Lemma lem3249616 {_85070 : Type'} (a : _85070) : term54 _85070 a.
Proof. exact (EQ_MP (@lem3249615 _85070 a) (@lem3249614 _85070 a)). Qed.
Lemma lem3249617 {_85070 : Type'} (a : _85070) (s : _85070 -> Prop) : term292 _85070 a s.
Proof. exact (@lem3249616 _85070 a s). Qed.
Lemma lem3249618 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term292 _85070 a s) = (term45 _85070 s a).
Proof. exact (eq_refl (term292 _85070 a s)). Qed.
Lemma lem3249619 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : term45 _85070 s a.
Proof. exact (EQ_MP (@lem3249618 _85070 s a) (@lem3249617 _85070 a s)). Qed.
Lemma lem3249621 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : term45 _85070 s a.
Proof. exact (@lem3247887 _85070 s a (@lem3249619 _85070 s a)). Qed.
Lemma lem3249622 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term46 _85070 s a) : False.
Proof. exact (@lem3249621 _85070 s a (@lem3247871 _85070 s a h1)). Qed.
Lemma lem3249623 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term46 _85070 s a) : (term46 _85070 s a) = False.
Proof. exact (prop_ext (fun h2 : term46 _85070 s a => @lem3249622 _85070 s a h1) (fun h2 : False => @lem3247871 _85070 s a h1)). Qed.
Lemma lem3249624 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) (h1 : term46 _85070 s a) : False.
Proof. exact (EQ_MP (@lem3249623 _85070 s a h1) (@lem3247871 _85070 s a h1)). Qed.
Lemma lem3249625 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : term45 _85070 s a.
Proof. exact (fun h0 : term46 _85070 s a => @lem3249624 _85070 s a h0). Qed.
Lemma lem3249626 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term31 _85070 s a) = (term43 _85070 s a).
Proof. exact (EQ_MP (@lem3247870 _85070 s a) (@lem3249625 _85070 s a)). Qed.
Lemma lem3249627 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term9 _85070 s a) = (term18 _85070 s a).
Proof. exact (EQ_MP (@lem3247866 _85070 s a) (@lem3249626 _85070 s a)). Qed.
Lemma lem3249629 {A : Type'} (P : type686 A) (t : A -> Prop) : term293 A P t.
Proof. exact (@lem3245541 A P t). Qed.
Lemma lem3249630 {A : Type'} (t : A -> Prop) (P : type686 A) : (term293 A P t) = (term294 A t P).
Proof. exact (eq_refl (term293 A P t)). Qed.
Lemma lem3249631 {A : Type'} (t : A -> Prop) (P : type686 A) : term294 A t P.
Proof. exact (EQ_MP (@lem3249630 A t P) (@lem3249629 A P t)). Qed.
Lemma lem3249632 {A : Type'} (t : A -> Prop) (P : type686 A) (u : A -> Prop) : term295 A t P u.
Proof. exact (@lem3249631 A t P u). Qed.
Lemma lem3249633 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term295 A t P u) = ((term296 A t u P) = (term297 A t u P)).
Proof. exact (eq_refl (term295 A t P u)). Qed.
Lemma lem3249648 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term12 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3249649 {_85084 : Type'} (s : _85084 -> Prop) (t : _85084 -> Prop) : (s = t) = (term12 _85084 s t).
Proof. exact (@lem3249648 _85084 s t). Qed.
Lemma lem3249650 {_85084 : Type'} (a : _85084) (s : _85084 -> Prop) : ((@INSERT _85084 a s) = (term298 _85084 a s)) = (term299 _85084 a s).
Proof. exact (@lem3249649 _85084 (@INSERT _85084 a s) (term298 _85084 a s)). Qed.
Lemma lem3249659 {_85084 : Type'} (a : _85084) (s : _85084 -> Prop) : (term299 _85084 a s) = ((@INSERT _85084 a s) = (term298 _85084 a s)).
Proof. exact (SYM (@lem3249650 _85084 a s)). Qed.
Lemma lem3249667 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term21 A x y s) = (term22 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3249668 {_85084 : Type'} (y : _85084) (x : _85084) (s : _85084 -> Prop) : (term21 _85084 x y s) = (term22 _85084 y x s).
Proof. exact (@lem3249667 _85084 y x s). Qed.
Lemma lem3249669 {_85084 : Type'} (a : _85084) (x : _85084) (s : _85084 -> Prop) : (term21 _85084 x a s) = (term22 _85084 a x s).
Proof. exact (@lem3249668 _85084 a x s). Qed.
Lemma lem3249675 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3249676 {_85084 : Type'} (P : _85084 -> Prop) (x : _85084) : (@IN _85084 x P) = (P x).
Proof. exact (@lem3249675 _85084 P x). Qed.
Lemma lem3249677 {_85084 : Type'} (s : _85084 -> Prop) (x : _85084) : (@IN _85084 x s) = (s x).
Proof. exact (@lem3249676 _85084 s x). Qed.
Lemma lem3249678 {_85084 : Type'} (x : _85084) (a : _85084) : (term25 _85084 x a) = (term25 _85084 x a).
Proof. exact (eq_refl (term25 _85084 x a)). Qed.
Lemma lem3249679 {_85084 : Type'} (a : _85084) (s : _85084 -> Prop) (x : _85084) : (term22 _85084 a x s) = (term300 _85084 a s x).
Proof. exact (MK_COMB (@lem3249678 _85084 x a) (@lem3249677 _85084 s x)). Qed.
Lemma lem3249682 {_85084 : Type'} (a : _85084) (s : _85084 -> Prop) (x : _85084) : (term21 _85084 x a s) = (term300 _85084 a s x).
Proof. exact (TRANS (@lem3249669 _85084 a x s) (@lem3249679 _85084 a s x)). Qed.
Lemma lem3249683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3249684 {_85084 : Type'} (a : _85084) (s : _85084 -> Prop) (x : _85084) : (term301 _85084 x a s) = (term302 _85084 a s x).
Proof. exact (MK_COMB (@lem3249683) (@lem3249682 _85084 a s x)). Qed.
Lemma lem3249686 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term303 A x s t) = (term304 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3249687 {_85084 : Type'} (s : _85084 -> Prop) (x : _85084) (t : _85084 -> Prop) : (term303 _85084 x s t) = (term304 _85084 s x t).
Proof. exact (@lem3249686 _85084 s x t). Qed.
Lemma lem3249688 {_85084 : Type'} (a : _85084) (x : _85084) (s : _85084 -> Prop) : (term305 _85084 x a s) = (term306 _85084 a x s).
Proof. exact (@lem3249687 _85084 (@INSERT _85084 a (@EMPTY _85084)) x s). Qed.
Lemma lem3249692 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term21 A x y s) = (term22 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3249693 {_85084 : Type'} (y : _85084) (x : _85084) (s : _85084 -> Prop) : (term21 _85084 x y s) = (term22 _85084 y x s).
Proof. exact (@lem3249692 _85084 y x s). Qed.
Lemma lem3249694 {_85084 : Type'} (a : _85084) (x : _85084) : (term23 _85084 x a) = (term24 _85084 a x).
Proof. exact (@lem3249693 _85084 a x (@EMPTY _85084)). Qed.
Lemma lem3249700 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3249701 {_85084 : Type'} (x : _85084) : (@IN _85084 x (@EMPTY _85084)) = False.
Proof. exact (@lem3249700 _85084 x). Qed.
Lemma lem3249702 {_85084 : Type'} (x : _85084) (a : _85084) : (term25 _85084 x a) = (term25 _85084 x a).
Proof. exact (eq_refl (term25 _85084 x a)). Qed.
Lemma lem3249703 {_85084 : Type'} (x : _85084) (a : _85084) : (term24 _85084 a x) = (term26 _85084 x a).
Proof. exact (MK_COMB (@lem3249702 _85084 x a) (@lem3249701 _85084 x)). Qed.
Lemma lem3249705 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3249706 {_85084 : Type'} (x : _85084) (a : _85084) : (term26 _85084 x a) = (x = a).
Proof. exact (@lem3249705 (x = a)). Qed.
Lemma lem3249709 {_85084 : Type'} (x : _85084) (a : _85084) : (term24 _85084 a x) = (x = a).
Proof. exact (TRANS (@lem3249703 _85084 x a) (@lem3249706 _85084 x a)). Qed.
Lemma lem3249710 {_85084 : Type'} (x : _85084) (a : _85084) : (term23 _85084 x a) = (x = a).
Proof. exact (TRANS (@lem3249694 _85084 a x) (@lem3249709 _85084 x a)). Qed.
Lemma lem3249711 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3249712 {_85084 : Type'} (x : _85084) (a : _85084) : (term307 _85084 x a) = (term25 _85084 x a).
Proof. exact (MK_COMB (@lem3249711) (@lem3249710 _85084 x a)). Qed.
Lemma lem3249714 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3249715 {_85084 : Type'} (P : _85084 -> Prop) (x : _85084) : (@IN _85084 x P) = (P x).
Proof. exact (@lem3249714 _85084 P x). Qed.
Lemma lem3249716 {_85084 : Type'} (s : _85084 -> Prop) (x : _85084) : (@IN _85084 x s) = (s x).
Proof. exact (@lem3249715 _85084 s x). Qed.
Lemma lem3249717 {_85084 : Type'} (a : _85084) (s : _85084 -> Prop) (x : _85084) : (term306 _85084 a x s) = (term300 _85084 a s x).
Proof. exact (MK_COMB (@lem3249712 _85084 x a) (@lem3249716 _85084 s x)). Qed.
Lemma lem3249720 {_85084 : Type'} (a : _85084) (s : _85084 -> Prop) (x : _85084) : (term305 _85084 x a s) = (term300 _85084 a s x).
Proof. exact (TRANS (@lem3249688 _85084 a x s) (@lem3249717 _85084 a s x)). Qed.
Lemma lem3249721 {_85084 : Type'} (a : _85084) (s : _85084 -> Prop) (x : _85084) : ((term21 _85084 x a s) = (term305 _85084 x a s)) = ((term300 _85084 a s x) = (term300 _85084 a s x)).
Proof. exact (MK_COMB (@lem3249684 _85084 a s x) (@lem3249720 _85084 a s x)). Qed.
Lemma lem3249723 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3249724 (x : Prop) : (x = x) = True.
Proof. exact (@lem3249723 Prop x). Qed.
Lemma lem3249725 {_85084 : Type'} (a : _85084) (s : _85084 -> Prop) (x : _85084) : ((term300 _85084 a s x) = (term300 _85084 a s x)) = True.
Proof. exact (@lem3249724 (term300 _85084 a s x)). Qed.
Lemma lem3249726 {_85084 : Type'} (x : _85084) (a : _85084) (s : _85084 -> Prop) : ((term21 _85084 x a s) = (term305 _85084 x a s)) = True.
Proof. exact (TRANS (@lem3249721 _85084 a s x) (@lem3249725 _85084 a s x)). Qed.
Lemma lem3249727 {_85084 : Type'} (a : _85084) (s : _85084 -> Prop) : (term308 _85084 a s) = (term309 _85084).
Proof. exact (fun_ext (fun x : _85084 => @lem3249726 _85084 x a s)). Qed.
Lemma lem3249728 {_85084 : Type'} : (@all _85084) = (@all _85084).
Proof. exact (eq_refl (@all _85084)). Qed.
Lemma lem3249729 {_85084 : Type'} (a : _85084) (s : _85084 -> Prop) : (term299 _85084 a s) = (term310 _85084).
Proof. exact (MK_COMB (@lem3249728 _85084) (@lem3249727 _85084 a s)). Qed.
Lemma lem3249731 {A : Type'} (t : Prop) : (term311 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3249732 {_85084 : Type'} (t : Prop) : (term311 _85084 t) = t.
Proof. exact (@lem3249731 _85084 t). Qed.
Lemma lem3249733 {_85084 : Type'} : (term310 _85084) = True.
Proof. exact (@lem3249732 _85084 True). Qed.
Lemma lem3249734 {_85084 : Type'} (a : _85084) (s : _85084 -> Prop) : (term299 _85084 a s) = True.
Proof. exact (TRANS (@lem3249729 _85084 a s) (@lem3249733 _85084)). Qed.
Lemma lem3249735 {_85084 : Type'} (a : _85084) (s : _85084 -> Prop) : True = (term299 _85084 a s).
Proof. exact (SYM (@lem3249734 _85084 a s)). Qed.
Lemma lem3249736 {_85084 : Type'} (a : _85084) (s : _85084 -> Prop) : term299 _85084 a s.
Proof. exact (EQ_MP (@lem3249735 _85084 a s) (@lem0)). Qed.
Lemma lem3249747 {_85084 : Type'} (a : _85084) (s : _85084 -> Prop) : (@INSERT _85084 a s) = (term298 _85084 a s).
Proof. exact (EQ_MP (@lem3249659 _85084 a s) (@lem3249736 _85084 a s)). Qed.
Lemma lem3249748 {A : Type'} (a : A) (s : A -> Prop) : (@INSERT A a s) = (term298 A a s).
Proof. exact (@lem3249747 A a s). Qed.
Lemma lem3249749 {A : Type'} (a : A) (t : A -> Prop) : (@INSERT A a t) = (term298 A a t).
Proof. exact (@lem3249748 A a t). Qed.
Lemma lem3249750 {A : Type'} (s : A -> Prop) : (@SUBSET A s) = (@SUBSET A s).
Proof. exact (eq_refl (@SUBSET A s)). Qed.
Lemma lem3249751 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term312 A s a t) = (term313 A s a t).
Proof. exact (MK_COMB (@lem3249750 A s) (@lem3249749 A a t)). Qed.
Lemma lem3249752 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3249753 {A : Type'} (s : A -> Prop) (a : A) (t : A -> Prop) : (term314 A s a t) = (term315 A s a t).
Proof. exact (MK_COMB (@lem3249752) (@lem3249751 A s a t)). Qed.
Lemma lem3249754 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem3249755 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (s : A -> Prop) : (term316 A a t P s) = (term317 A a t P s).
Proof. exact (MK_COMB (@lem3249753 A s a t) (@lem3249754 A P s)). Qed.
Lemma lem3249756 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term318 A a t P) = (term319 A a t P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3249755 A a t P s)). Qed.
Lemma lem3249757 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3249758 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term320 A a t P) = (term321 A a t P).
Proof. exact (MK_COMB (@lem3249757 A) (@lem3249756 A a t P)). Qed.
Lemma lem3249759 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3249760 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term322 A a t P) = (term323 A a t P).
Proof. exact (MK_COMB (@lem3249759) (@lem3249758 A a t P)). Qed.
Lemma lem3249770 {_85084 : Type'} (a : _85084) (s : _85084 -> Prop) : (@INSERT _85084 a s) = (term298 _85084 a s).
Proof. exact (EQ_MP (@lem3249659 _85084 a s) (@lem3249736 _85084 a s)). Qed.
Lemma lem3249771 {A : Type'} (a : A) (s : A -> Prop) : (@INSERT A a s) = (term298 A a s).
Proof. exact (@lem3249770 A a s). Qed.
Lemma lem3249772 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3249773 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term324 A P a s) = (term325 A P a s).
Proof. exact (MK_COMB (@lem3249772 A P) (@lem3249771 A a s)). Qed.
Lemma lem3249774 {A : Type'} (P : type686 A) (s : A -> Prop) : (term326 A P s) = (term326 A P s).
Proof. exact (eq_refl (term326 A P s)). Qed.
Lemma lem3249775 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term327 A P a s) = (term328 A P a s).
Proof. exact (MK_COMB (@lem3249774 A P s) (@lem3249773 A P a s)). Qed.
Lemma lem3249776 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term329 A s t) = (term329 A s t).
Proof. exact (eq_refl (term329 A s t)). Qed.
Lemma lem3249777 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term330 A t P a s) = (term331 A t P a s).
Proof. exact (MK_COMB (@lem3249776 A s t) (@lem3249775 A P a s)). Qed.
Lemma lem3249778 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term332 A t P a) = (term333 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3249777 A t P a s)). Qed.
Lemma lem3249779 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3249780 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term334 A t P a) = (term335 A t P a).
Proof. exact (MK_COMB (@lem3249779 A) (@lem3249778 A t P a)). Qed.
Lemma lem3249781 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term320 A a t P) = (term334 A t P a)) = ((term321 A a t P) = (term335 A t P a)).
Proof. exact (MK_COMB (@lem3249760 A a t P) (@lem3249780 A t P a)). Qed.
Lemma lem3249782 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term321 A a t P) = (term335 A t P a)) = ((term320 A a t P) = (term334 A t P a)).
Proof. exact (SYM (@lem3249781 A t P a)). Qed.
Lemma lem3249786 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term296 A t u P) = (term297 A t u P).
Proof. exact (EQ_MP (@lem3249633 A t u P) (@lem3249632 A t P u)). Qed.
Lemma lem3249787 {A : Type'} (t : A -> Prop) (u : A -> Prop) (P : type686 A) : (term296 A t u P) = (term297 A t u P).
Proof. exact (@lem3249786 A t u P). Qed.
Lemma lem3249788 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term321 A a t P) = (term336 A a t P).
Proof. exact (@lem3249787 A (@INSERT A a (@EMPTY A)) t P). Qed.
Lemma lem3249802 {_85070 : Type'} (s : _85070 -> Prop) (a : _85070) : (term8 _85070 s a) = (term17 _85070 s a).
Proof. exact (EQ_MP (@lem3247740 _85070 s a) (@lem3249627 _85070 s a)). Qed.
Lemma lem3249803 {A : Type'} (s : A -> Prop) (a : A) : (term8 A s a) = (term17 A s a).
Proof. exact (@lem3249802 A s a). Qed.
Lemma lem3249804 {A : Type'} (t' : A -> Prop) (a : A) : (term8 A t' a) = (term17 A t' a).
Proof. exact (@lem3249803 A t' a). Qed.
Lemma lem3249811 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3249812 {A : Type'} (t' : A -> Prop) (a : A) : (term337 A t' a) = (term338 A t' a).
Proof. exact (MK_COMB (@lem3249811) (@lem3249804 A t' a)). Qed.
Lemma lem3249813 {A : Type'} (u' : A -> Prop) (t : A -> Prop) : (@SUBSET A u' t) = (@SUBSET A u' t).
Proof. exact (eq_refl (@SUBSET A u' t)). Qed.
Lemma lem3249814 {A : Type'} (t' : A -> Prop) (a : A) (u' : A -> Prop) (t : A -> Prop) : (term339 A t' a u' t) = (term340 A t' a u' t).
Proof. exact (MK_COMB (@lem3249812 A t' a) (@lem3249813 A u' t)). Qed.
Lemma lem3249817 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3249818 {A : Type'} (t' : A -> Prop) (a : A) (u' : A -> Prop) (t : A -> Prop) : (term341 A t' a u' t) = (term342 A t' a u' t).
Proof. exact (MK_COMB (@lem3249817) (@lem3249814 A t' a u' t)). Qed.
Lemma lem3249819 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term343 A P t' u') = (term343 A P t' u').
Proof. exact (eq_refl (term343 A P t' u')). Qed.
Lemma lem3249820 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term344 A a t P t' u') = (term345 A a t P t' u').
Proof. exact (MK_COMB (@lem3249818 A t' a u' t) (@lem3249819 A P t' u')). Qed.
Lemma lem3249823 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term346 A a t P t') = (term347 A a t P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3249820 A a t P t' u')). Qed.
Lemma lem3249824 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3249825 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term348 A a t P t') = (term349 A a t P t').
Proof. exact (MK_COMB (@lem3249824 A) (@lem3249823 A a t P t')). Qed.
Lemma lem3249830 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term350 A a t P) = (term351 A a t P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3249825 A a t P t')). Qed.
Lemma lem3249831 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3249832 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term336 A a t P) = (term352 A a t P).
Proof. exact (MK_COMB (@lem3249831 A) (@lem3249830 A a t P)). Qed.
Lemma lem3249837 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term321 A a t P) = (term352 A a t P).
Proof. exact (TRANS (@lem3249788 A a t P) (@lem3249832 A a t P)). Qed.
Lemma lem3249838 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3249839 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term323 A a t P) = (term353 A a t P).
Proof. exact (MK_COMB (@lem3249838) (@lem3249837 A a t P)). Qed.
Lemma lem3249848 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term335 A t P a) = (term335 A t P a).
Proof. exact (eq_refl (term335 A t P a)). Qed.
Lemma lem3249849 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term321 A a t P) = (term335 A t P a)) = ((term352 A a t P) = (term335 A t P a)).
Proof. exact (MK_COMB (@lem3249839 A a t P) (@lem3249848 A t P a)). Qed.
Lemma lem3249852 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term352 A a t P) = (term335 A t P a)) = ((term321 A a t P) = (term335 A t P a)).
Proof. exact (SYM (@lem3249849 A t P a)). Qed.
Lemma lem3249854 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3249855 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term352 A a t P) = (term335 A t P a)) = (term354 A t P a).
Proof. exact (@lem3249854 ((term352 A a t P) = (term335 A t P a))). Qed.
Lemma lem3249856 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term354 A t P a) = ((term352 A a t P) = (term335 A t P a)).
Proof. exact (SYM (@lem3249855 A t P a)). Qed.
Lemma lem3249857 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term355 A t P a) : term355 A t P a.
Proof. exact (h1). Qed.
Lemma lem3249858 {A : Type'} : term356 A.
Proof. exact (@lem3235853 A). Qed.
Lemma lem3249863 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term357 A t P a) : term357 A t P a.
Proof. exact (h1). Qed.
Lemma lem3249864 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : term358 A t P a.
Proof. exact (fun h0 : term357 A t P a => @lem3249863 A t P a h0). Qed.
Lemma lem3249865 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term358 A t P a) : term358 A t P a.
Proof. exact (h1). Qed.
Lemma lem3249866 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term357 A t P a) : term357 A t P a.
Proof. exact (h1). Qed.
Lemma lem3249867 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term357 A t P a) (h2 : term358 A t P a) : term357 A t P a.
Proof. exact (@lem3249865 A t P a h2 (@lem3249866 A t P a h1)). Qed.
Lemma lem3249868 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term357 A t P a) : term359 A t P a.
Proof. exact (fun h0 : term358 A t P a => @lem3249867 A t P a h1 h0). Qed.
Lemma lem3249869 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term358 A t P a) : term358 A t P a.
Proof. exact (h1). Qed.
Lemma lem3249870 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term357 A t P a) (h2 : term358 A t P a) : term357 A t P a.
Proof. exact (@lem3249868 A t P a h1 (@lem3249869 A t P a h2)). Qed.
Lemma lem3249871 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term358 A t P a) : term358 A t P a.
Proof. exact (fun h0 : term357 A t P a => @lem3249870 A t P a h0 h1). Qed.
Lemma lem3249872 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : term360 A t P a.
Proof. exact (fun h0 : term358 A t P a => @lem3249871 A t P a h0). Qed.
Lemma lem3249875 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : term358 A t P a.
Proof. exact (@lem3249872 A t P a (@lem3249864 A t P a)). Qed.
Lemma lem3249876 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : term358 A t P a.
Proof. exact (@lem3249875 A t P a). Qed.
Lemma lem3249914 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3249915 {A : Type'} : (term361 A) = (term362 A).
Proof. exact (@lem3249914 (term356 A)). Qed.
Lemma lem3249926 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term363 A t P a) = (term363 A t P a).
Proof. exact (eq_refl (term363 A t P a)). Qed.
Lemma lem3249927 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term357 A t P a) = (term364 A t P a).
Proof. exact (MK_COMB (@lem3249926 A t P a) (@lem3249915 A)). Qed.
Lemma lem3249930 {A : Type'} (P : type686 A) (a : A) : (term365 A P a) = (term366 A P a).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3249927 A t P a)). Qed.
Lemma lem3249931 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3249932 {A : Type'} (P : type686 A) (a : A) : (term367 A P a) = (term368 A P a).
Proof. exact (MK_COMB (@lem3249931 A) (@lem3249930 A P a)). Qed.
Lemma lem3249937 {A : Type'} (a : A) : (term369 A a) = (term370 A a).
Proof. exact (fun_ext (fun P : type686 A => @lem3249932 A P a)). Qed.
Lemma lem3249938 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3249939 {A : Type'} (a : A) : (term371 A a) = (term372 A a).
Proof. exact (MK_COMB (@lem3249938 A) (@lem3249937 A a)). Qed.
Lemma lem3249944 {A : Type'} : (term373 A) = (term374 A).
Proof. exact (fun_ext (fun a : A => @lem3249939 A a)). Qed.
Lemma lem3249945 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3249954 {A : Type'} : (term375 A) = (term376 A).
Proof. exact (MK_COMB (@lem3249945 A) (@lem3249944 A)). Qed.
Lemma lem3249955 {A : Type'} (s : A -> Prop) : ((@UNION A s (@EMPTY A)) = s) = ((@UNION A s (@EMPTY A)) = s).
Proof. exact (eq_refl ((@UNION A s (@EMPTY A)) = s)). Qed.
Lemma lem3249956 {A : Type'} : (term377 A) = (term377 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3249955 A s)). Qed.
Lemma lem3249957 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3249958 {A : Type'} : (term378 A) = (term378 A).
Proof. exact (MK_COMB (@lem3249957 A) (@lem3249956 A)). Qed.
Lemma lem3249959 {A : Type'} (s : A -> Prop) : ((@UNION A (@EMPTY A) s) = s) = ((@UNION A (@EMPTY A) s) = s).
Proof. exact (eq_refl ((@UNION A (@EMPTY A) s) = s)). Qed.
Lemma lem3249960 {A : Type'} : (term379 A) = (term379 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3249959 A s)). Qed.
Lemma lem3249961 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3249962 {A : Type'} : (term380 A) = (term380 A).
Proof. exact (MK_COMB (@lem3249961 A) (@lem3249960 A)). Qed.
Lemma lem3249963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3249964 {A : Type'} : (term381 A) = (term381 A).
Proof. exact (MK_COMB (@lem3249963) (@lem3249962 A)). Qed.
Lemma lem3249965 {A : Type'} : (term356 A) = (term356 A).
Proof. exact (MK_COMB (@lem3249964 A) (@lem3249958 A)). Qed.
Lemma lem3249966 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3249967 {A : Type'} : (term362 A) = (term362 A).
Proof. exact (MK_COMB (@lem3249966) (@lem3249965 A)). Qed.
Lemma lem3249976 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term331 A t P a s) = (term331 A t P a s).
Proof. exact (eq_refl (term331 A t P a s)). Qed.
Lemma lem3249977 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term333 A t P a) = (term333 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3249976 A t P a s)). Qed.
Lemma lem3249978 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3249979 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term335 A t P a) = (term335 A t P a).
Proof. exact (MK_COMB (@lem3249978 A) (@lem3249977 A t P a)). Qed.
Lemma lem3249992 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term345 A a t P t' u') = (term345 A a t P t' u').
Proof. exact (eq_refl (term345 A a t P t' u')). Qed.
Lemma lem3249993 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term347 A a t P t') = (term347 A a t P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3249992 A a t P t' u')). Qed.
Lemma lem3249994 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3249995 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term349 A a t P t') = (term349 A a t P t').
Proof. exact (MK_COMB (@lem3249994 A) (@lem3249993 A a t P t')). Qed.
Lemma lem3249996 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term351 A a t P) = (term351 A a t P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3249995 A a t P t')). Qed.
Lemma lem3249997 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3249998 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term352 A a t P) = (term352 A a t P).
Proof. exact (MK_COMB (@lem3249997 A) (@lem3249996 A a t P)). Qed.
Lemma lem3249999 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3250000 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term353 A a t P) = (term353 A a t P).
Proof. exact (MK_COMB (@lem3249999) (@lem3249998 A a t P)). Qed.
Lemma lem3250001 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term352 A a t P) = (term335 A t P a)) = ((term352 A a t P) = (term335 A t P a)).
Proof. exact (MK_COMB (@lem3250000 A a t P) (@lem3249979 A t P a)). Qed.
Lemma lem3250002 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3250003 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term355 A t P a) = (term355 A t P a).
Proof. exact (MK_COMB (@lem3250002) (@lem3250001 A t P a)). Qed.
Lemma lem3250004 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3250005 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term363 A t P a) = (term363 A t P a).
Proof. exact (MK_COMB (@lem3250004) (@lem3250003 A t P a)). Qed.
Lemma lem3250006 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term364 A t P a) = (term364 A t P a).
Proof. exact (MK_COMB (@lem3250005 A t P a) (@lem3249967 A)). Qed.
Lemma lem3250007 {A : Type'} (P : type686 A) (a : A) : (term366 A P a) = (term366 A P a).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3250006 A t P a)). Qed.
Lemma lem3250008 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250009 {A : Type'} (P : type686 A) (a : A) : (term368 A P a) = (term368 A P a).
Proof. exact (MK_COMB (@lem3250008 A) (@lem3250007 A P a)). Qed.
Lemma lem3250010 {A : Type'} (a : A) : (term370 A a) = (term370 A a).
Proof. exact (fun_ext (fun P : type686 A => @lem3250009 A P a)). Qed.
Lemma lem3250011 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3250012 {A : Type'} (a : A) : (term372 A a) = (term372 A a).
Proof. exact (MK_COMB (@lem3250011 A) (@lem3250010 A a)). Qed.
Lemma lem3250013 {A : Type'} : (term374 A) = (term374 A).
Proof. exact (fun_ext (fun a : A => @lem3250012 A a)). Qed.
Lemma lem3250014 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3250015 {A : Type'} : (term376 A) = (term376 A).
Proof. exact (MK_COMB (@lem3250014 A) (@lem3250013 A)). Qed.
Lemma lem3250080 {A : Type'} : (term375 A) = (term376 A).
Proof. exact (TRANS (@lem3249954 A) (@lem3250015 A)). Qed.
Lemma lem3250081 {A : Type'} : (term376 A) = (term375 A).
Proof. exact (SYM (@lem3250080 A)). Qed.
Lemma lem3250082 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term355 A t P a) : term355 A t P a.
Proof. exact (h1). Qed.
Lemma lem3250083 {A : Type'} (h1 : term356 A) : term356 A.
Proof. exact (h1). Qed.
Lemma lem3250092 {A : Type'} (t' : A -> Prop) (a : A) : (term382 A t' a) = (term383 A t' a).
Proof. exact (@lem17160 (t' = (@EMPTY A)) (t' = (@INSERT A a (@EMPTY A)))). Qed.
Lemma lem3250096 {A : Type'} (u' : A -> Prop) (t : A -> Prop) : (term384 A u' t) = (term384 A u' t).
Proof. exact (eq_refl (term384 A u' t)). Qed.
Lemma lem3250098 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3250099 {A : Type'} (t' : A -> Prop) (a : A) : (term385 A t' a) = (term386 A t' a).
Proof. exact (MK_COMB (@lem3250098) (@lem3250092 A t' a)). Qed.
Lemma lem3250100 {A : Type'} (t' : A -> Prop) (a : A) (u' : A -> Prop) (t : A -> Prop) : (term387 A t' a u' t) = (term388 A t' a u' t).
Proof. exact (MK_COMB (@lem3250099 A t' a) (@lem3250096 A u' t)). Qed.
Lemma lem3250101 {A : Type'} (t' : A -> Prop) (a : A) (u' : A -> Prop) (t : A -> Prop) : (term389 A t' a u' t) = (term387 A t' a u' t).
Proof. exact (@lem17045 (term17 A t' a) (@SUBSET A u' t)). Qed.
Lemma lem3250102 {A : Type'} (t' : A -> Prop) (a : A) (u' : A -> Prop) (t : A -> Prop) : (term389 A t' a u' t) = (term388 A t' a u' t).
Proof. exact (TRANS (@lem3250101 A t' a u' t) (@lem3250100 A t' a u' t)). Qed.
Lemma lem3250107 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term343 A P t' u') = (term343 A P t' u').
Proof. exact (eq_refl (term343 A P t' u')). Qed.
Lemma lem3250112 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term390 A a t P t' u') = (term391 A a t P t' u').
Proof. exact (@lem17362 (term340 A t' a u' t) (term343 A P t' u')). Qed.
Lemma lem3250113 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3250114 {A : Type'} (t' : A -> Prop) (a : A) (u' : A -> Prop) (t : A -> Prop) : (term392 A t' a u' t) = (term393 A t' a u' t).
Proof. exact (MK_COMB (@lem3250113) (@lem3250102 A t' a u' t)). Qed.
Lemma lem3250115 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term394 A a t P t' u') = (term395 A a t P t' u').
Proof. exact (MK_COMB (@lem3250114 A t' a u' t) (@lem3250107 A P t' u')). Qed.
Lemma lem3250116 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term345 A a t P t' u') = (term394 A a t P t' u').
Proof. exact (@lem17265 (term340 A t' a u' t) (term343 A P t' u')). Qed.
Lemma lem3250117 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term345 A a t P t' u') = (term395 A a t P t' u').
Proof. exact (TRANS (@lem3250116 A a t P t' u') (@lem3250115 A a t P t' u')). Qed.
Lemma lem3250118 {A : Type'} (P : type686 A) : (term396 A P) = (term397 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3250119 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term398 A a t P t') = (term399 A a t P t').
Proof. exact (@lem3250118 A (term347 A a t P t')). Qed.
Lemma lem3250120 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term400 A a t P t' u') = (term345 A a t P t' u').
Proof. exact (eq_refl (term400 A a t P t' u')). Qed.
Lemma lem3250121 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3250122 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term401 A a t P t' u') = (term390 A a t P t' u').
Proof. exact (MK_COMB (@lem3250121) (@lem3250120 A a t P t' u')). Qed.
Lemma lem3250123 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term401 A a t P t' u') = (term391 A a t P t' u').
Proof. exact (TRANS (@lem3250122 A a t P t' u') (@lem3250112 A a t P t' u')). Qed.
Lemma lem3250124 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term402 A a t P t') = (term403 A a t P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3250123 A a t P t' u')). Qed.
Lemma lem3250125 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3250126 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term399 A a t P t') = (term404 A a t P t').
Proof. exact (MK_COMB (@lem3250125 A) (@lem3250124 A a t P t')). Qed.
Lemma lem3250127 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term398 A a t P t') = (term404 A a t P t').
Proof. exact (TRANS (@lem3250119 A a t P t') (@lem3250126 A a t P t')). Qed.
Lemma lem3250128 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term347 A a t P t') = (term405 A a t P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3250117 A a t P t' u')). Qed.
Lemma lem3250129 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250130 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term349 A a t P t') = (term406 A a t P t').
Proof. exact (MK_COMB (@lem3250129 A) (@lem3250128 A a t P t')). Qed.
Lemma lem3250131 {A : Type'} (P : type686 A) : (term396 A P) = (term397 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3250132 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term407 A a t P) = (term408 A a t P).
Proof. exact (@lem3250131 A (term351 A a t P)). Qed.
Lemma lem3250133 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term409 A a t P t') = (term349 A a t P t').
Proof. exact (eq_refl (term409 A a t P t')). Qed.
Lemma lem3250134 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3250135 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term410 A a t P t') = (term398 A a t P t').
Proof. exact (MK_COMB (@lem3250134) (@lem3250133 A a t P t')). Qed.
Lemma lem3250136 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term410 A a t P t') = (term404 A a t P t').
Proof. exact (TRANS (@lem3250135 A a t P t') (@lem3250127 A a t P t')). Qed.
Lemma lem3250137 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term411 A a t P) = (term412 A a t P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3250136 A a t P t')). Qed.
Lemma lem3250138 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3250139 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term408 A a t P) = (term413 A a t P).
Proof. exact (MK_COMB (@lem3250138 A) (@lem3250137 A a t P)). Qed.
Lemma lem3250140 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term407 A a t P) = (term413 A a t P).
Proof. exact (TRANS (@lem3250132 A a t P) (@lem3250139 A a t P)). Qed.
Lemma lem3250141 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term351 A a t P) = (term414 A a t P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3250130 A a t P t')). Qed.
Lemma lem3250142 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250143 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term352 A a t P) = (term415 A a t P).
Proof. exact (MK_COMB (@lem3250142 A) (@lem3250141 A a t P)). Qed.
Lemma lem3250154 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term416 A P a s) = (term417 A P a s).
Proof. exact (@lem17045 (P s) (term325 A P a s)). Qed.
Lemma lem3250159 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term418 A s t) = (term418 A s t).
Proof. exact (eq_refl (term418 A s t)). Qed.
Lemma lem3250160 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term419 A t P a s) = (term420 A t P a s).
Proof. exact (MK_COMB (@lem3250159 A s t) (@lem3250154 A P a s)). Qed.
Lemma lem3250161 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term421 A t P a s) = (term419 A t P a s).
Proof. exact (@lem17362 (@SUBSET A s t) (term328 A P a s)). Qed.
Lemma lem3250162 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term421 A t P a s) = (term420 A t P a s).
Proof. exact (TRANS (@lem3250161 A t P a s) (@lem3250160 A t P a s)). Qed.
Lemma lem3250167 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term331 A t P a s) = (term422 A t P a s).
Proof. exact (@lem17265 (@SUBSET A s t) (term328 A P a s)). Qed.
Lemma lem3250168 {A : Type'} (P : type686 A) : (term396 A P) = (term397 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3250169 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term423 A t P a) = (term424 A t P a).
Proof. exact (@lem3250168 A (term333 A t P a)). Qed.
Lemma lem3250170 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term425 A t P a s) = (term331 A t P a s).
Proof. exact (eq_refl (term425 A t P a s)). Qed.
Lemma lem3250171 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3250172 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term426 A t P a s) = (term421 A t P a s).
Proof. exact (MK_COMB (@lem3250171) (@lem3250170 A t P a s)). Qed.
Lemma lem3250173 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term426 A t P a s) = (term420 A t P a s).
Proof. exact (TRANS (@lem3250172 A t P a s) (@lem3250162 A t P a s)). Qed.
Lemma lem3250174 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term427 A t P a) = (term428 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250173 A t P a s)). Qed.
Lemma lem3250175 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3250176 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term424 A t P a) = (term429 A t P a).
Proof. exact (MK_COMB (@lem3250175 A) (@lem3250174 A t P a)). Qed.
Lemma lem3250177 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term423 A t P a) = (term429 A t P a).
Proof. exact (TRANS (@lem3250169 A t P a) (@lem3250176 A t P a)). Qed.
Lemma lem3250178 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term333 A t P a) = (term430 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250167 A t P a s)). Qed.
Lemma lem3250179 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250180 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term335 A t P a) = (term431 A t P a).
Proof. exact (MK_COMB (@lem3250179 A) (@lem3250178 A t P a)). Qed.
Lemma lem3250181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3250182 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term432 A a t P) = (term433 A a t P).
Proof. exact (MK_COMB (@lem3250181) (@lem3250140 A a t P)). Qed.
Lemma lem3250183 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term434 A t P a) = (term435 A t P a).
Proof. exact (MK_COMB (@lem3250182 A a t P) (@lem3250180 A t P a)). Qed.
Lemma lem3250184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3250185 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term436 A a t P) = (term437 A a t P).
Proof. exact (MK_COMB (@lem3250184) (@lem3250143 A a t P)). Qed.
Lemma lem3250186 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term438 A t P a) = (term439 A t P a).
Proof. exact (MK_COMB (@lem3250185 A a t P) (@lem3250177 A t P a)). Qed.
Lemma lem3250187 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3250188 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term440 A t P a) = (term441 A t P a).
Proof. exact (MK_COMB (@lem3250187) (@lem3250186 A t P a)). Qed.
Lemma lem3250189 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term442 A t P a) = (term443 A t P a).
Proof. exact (MK_COMB (@lem3250188 A t P a) (@lem3250183 A t P a)). Qed.
Lemma lem3250190 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term355 A t P a) = (term442 A t P a).
Proof. exact (@lem17646 (term352 A a t P) (term335 A t P a)). Qed.
Lemma lem3250191 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term355 A t P a) = (term443 A t P a).
Proof. exact (TRANS (@lem3250190 A t P a) (@lem3250189 A t P a)). Qed.
Lemma lem3250394 {A : Type'} (P : Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3250395 {A : Type'} (P : Prop) (Q : type686 A) : (term444 A P Q) = (term445 A P Q).
Proof. exact (@lem3250394 (A -> Prop) P Q). Qed.
Lemma lem3250396 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term446 A t P a) = (term447 A t P a).
Proof. exact (@lem3250395 A (term415 A a t P) (term428 A t P a)). Qed.
Lemma lem3250397 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term448 A t P a s) = (term420 A t P a s).
Proof. exact (eq_refl (term448 A t P a s)). Qed.
Lemma lem3250398 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term449 A t P a) = (term428 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250397 A t P a s)). Qed.
Lemma lem3250399 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3250400 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term450 A t P a) = (term429 A t P a).
Proof. exact (MK_COMB (@lem3250399 A) (@lem3250398 A t P a)). Qed.
Lemma lem3250401 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term437 A a t P) = (term437 A a t P).
Proof. exact (eq_refl (term437 A a t P)). Qed.
Lemma lem3250402 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term446 A t P a) = (term439 A t P a).
Proof. exact (MK_COMB (@lem3250401 A a t P) (@lem3250400 A t P a)). Qed.
Lemma lem3250403 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3250404 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term451 A t P a) = (term452 A t P a).
Proof. exact (MK_COMB (@lem3250403) (@lem3250402 A t P a)). Qed.
Lemma lem3250405 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term448 A t P a s) = (term420 A t P a s).
Proof. exact (eq_refl (term448 A t P a s)). Qed.
Lemma lem3250406 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term437 A a t P) = (term437 A a t P).
Proof. exact (eq_refl (term437 A a t P)). Qed.
Lemma lem3250407 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term453 A t P a s) = (term454 A t P a s).
Proof. exact (MK_COMB (@lem3250406 A a t P) (@lem3250405 A t P a s)). Qed.
Lemma lem3250408 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term455 A t P a) = (term456 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250407 A t P a s)). Qed.
Lemma lem3250409 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3250410 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term447 A t P a) = (term457 A t P a).
Proof. exact (MK_COMB (@lem3250409 A) (@lem3250408 A t P a)). Qed.
Lemma lem3250411 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term446 A t P a) = (term447 A t P a)) = ((term439 A t P a) = (term457 A t P a)).
Proof. exact (MK_COMB (@lem3250404 A t P a) (@lem3250410 A t P a)). Qed.
Lemma lem3250412 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term439 A t P a) = (term457 A t P a).
Proof. exact (EQ_MP (@lem3250411 A t P a) (@lem3250396 A t P a)). Qed.
Lemma lem3250413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3250414 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term441 A t P a) = (term458 A t P a).
Proof. exact (MK_COMB (@lem3250413) (@lem3250412 A t P a)). Qed.
Lemma lem3250416 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3250417 {A : Type'} (P : type686 A) (Q : Prop) : (term459 A P Q) = (term460 A P Q).
Proof. exact (@lem3250416 (A -> Prop) P Q). Qed.
Lemma lem3250418 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term461 A t P a) = (term462 A t P a).
Proof. exact (@lem3250417 A (term412 A a t P) (term431 A t P a)). Qed.
Lemma lem3250419 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term463 A a t P t') = (term404 A a t P t').
Proof. exact (eq_refl (term463 A a t P t')). Qed.
Lemma lem3250420 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term464 A a t P) = (term412 A a t P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3250419 A a t P t')). Qed.
Lemma lem3250421 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3250422 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term465 A a t P) = (term413 A a t P).
Proof. exact (MK_COMB (@lem3250421 A) (@lem3250420 A a t P)). Qed.
Lemma lem3250423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3250424 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term466 A a t P) = (term433 A a t P).
Proof. exact (MK_COMB (@lem3250423) (@lem3250422 A a t P)). Qed.
Lemma lem3250425 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term431 A t P a) = (term431 A t P a).
Proof. exact (eq_refl (term431 A t P a)). Qed.
Lemma lem3250426 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term461 A t P a) = (term435 A t P a).
Proof. exact (MK_COMB (@lem3250424 A a t P) (@lem3250425 A t P a)). Qed.
Lemma lem3250427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3250428 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term467 A t P a) = (term468 A t P a).
Proof. exact (MK_COMB (@lem3250427) (@lem3250426 A t P a)). Qed.
Lemma lem3250429 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term463 A a t P t') = (term404 A a t P t').
Proof. exact (eq_refl (term463 A a t P t')). Qed.
Lemma lem3250430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3250431 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term469 A a t P t') = (term470 A a t P t').
Proof. exact (MK_COMB (@lem3250430) (@lem3250429 A a t P t')). Qed.
Lemma lem3250432 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term431 A t P a) = (term431 A t P a).
Proof. exact (eq_refl (term431 A t P a)). Qed.
Lemma lem3250433 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term471 A t' t P a) = (term472 A t' t P a).
Proof. exact (MK_COMB (@lem3250431 A a t P t') (@lem3250432 A t P a)). Qed.
Lemma lem3250434 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term473 A t P a) = (term474 A t P a).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3250433 A t' t P a)). Qed.
Lemma lem3250435 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3250436 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term462 A t P a) = (term475 A t P a).
Proof. exact (MK_COMB (@lem3250435 A) (@lem3250434 A t P a)). Qed.
Lemma lem3250437 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term461 A t P a) = (term462 A t P a)) = ((term435 A t P a) = (term475 A t P a)).
Proof. exact (MK_COMB (@lem3250428 A t P a) (@lem3250436 A t P a)). Qed.
Lemma lem3250438 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term435 A t P a) = (term475 A t P a).
Proof. exact (EQ_MP (@lem3250437 A t P a) (@lem3250418 A t P a)). Qed.
Lemma lem3250440 {A : Type'} (P : A -> Prop) (Q : Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3250441 {A : Type'} (P : type686 A) (Q : Prop) : (term459 A P Q) = (term460 A P Q).
Proof. exact (@lem3250440 (A -> Prop) P Q). Qed.
Lemma lem3250442 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term476 A t' t P a) = (term477 A t' t P a).
Proof. exact (@lem3250441 A (term403 A a t P t') (term431 A t P a)). Qed.
Lemma lem3250443 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term478 A a t P t' u') = (term391 A a t P t' u').
Proof. exact (eq_refl (term478 A a t P t' u')). Qed.
Lemma lem3250444 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term479 A a t P t') = (term403 A a t P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3250443 A a t P t' u')). Qed.
Lemma lem3250445 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3250446 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term480 A a t P t') = (term404 A a t P t').
Proof. exact (MK_COMB (@lem3250445 A) (@lem3250444 A a t P t')). Qed.
Lemma lem3250447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3250448 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term481 A a t P t') = (term470 A a t P t').
Proof. exact (MK_COMB (@lem3250447) (@lem3250446 A a t P t')). Qed.
Lemma lem3250449 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term431 A t P a) = (term431 A t P a).
Proof. exact (eq_refl (term431 A t P a)). Qed.
Lemma lem3250450 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term476 A t' t P a) = (term472 A t' t P a).
Proof. exact (MK_COMB (@lem3250448 A a t P t') (@lem3250449 A t P a)). Qed.
Lemma lem3250451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3250452 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term482 A t' t P a) = (term483 A t' t P a).
Proof. exact (MK_COMB (@lem3250451) (@lem3250450 A t' t P a)). Qed.
Lemma lem3250453 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term478 A a t P t' u') = (term391 A a t P t' u').
Proof. exact (eq_refl (term478 A a t P t' u')). Qed.
Lemma lem3250454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3250455 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term484 A a t P t' u') = (term485 A a t P t' u').
Proof. exact (MK_COMB (@lem3250454) (@lem3250453 A a t P t' u')). Qed.
Lemma lem3250456 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term431 A t P a) = (term431 A t P a).
Proof. exact (eq_refl (term431 A t P a)). Qed.
Lemma lem3250457 {A : Type'} (t' : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term486 A t' u' t P a) = (term487 A t' u' t P a).
Proof. exact (MK_COMB (@lem3250455 A a t P t' u') (@lem3250456 A t P a)). Qed.
Lemma lem3250458 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term488 A t' t P a) = (term489 A t' t P a).
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3250457 A t' u' t P a)). Qed.
Lemma lem3250459 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3250460 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term477 A t' t P a) = (term490 A t' t P a).
Proof. exact (MK_COMB (@lem3250459 A) (@lem3250458 A t' t P a)). Qed.
Lemma lem3250461 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : ((term476 A t' t P a) = (term477 A t' t P a)) = ((term472 A t' t P a) = (term490 A t' t P a)).
Proof. exact (MK_COMB (@lem3250452 A t' t P a) (@lem3250460 A t' t P a)). Qed.
Lemma lem3250462 {A : Type'} (t' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term472 A t' t P a) = (term490 A t' t P a).
Proof. exact (EQ_MP (@lem3250461 A t' t P a) (@lem3250442 A t' t P a)). Qed.
Lemma lem3250463 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term474 A t P a) = (term491 A t P a).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3250462 A t' t P a)). Qed.
Lemma lem3250464 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3250465 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term475 A t P a) = (term492 A t P a).
Proof. exact (MK_COMB (@lem3250464 A) (@lem3250463 A t P a)). Qed.
Lemma lem3250466 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term435 A t P a) = (term492 A t P a).
Proof. exact (TRANS (@lem3250438 A t P a) (@lem3250465 A t P a)). Qed.
Lemma lem3250467 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term443 A t P a) = (term493 A t P a).
Proof. exact (MK_COMB (@lem3250414 A t P a) (@lem3250466 A t P a)). Qed.
Lemma lem3250469 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term203 A P Q) = (term204 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3250470 {A : Type'} (P : type686 A) (Q : type686 A) : (term494 A P Q) = (term495 A P Q).
Proof. exact (@lem3250469 (A -> Prop) P Q). Qed.
Lemma lem3250471 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term496 A t P a) = (term497 A t P a).
Proof. exact (@lem3250470 A (term456 A t P a) (term491 A t P a)). Qed.
Lemma lem3250472 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term498 A t P a s) = (term454 A t P a s).
Proof. exact (eq_refl (term498 A t P a s)). Qed.
Lemma lem3250473 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term499 A t P a) = (term456 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250472 A t P a s)). Qed.
Lemma lem3250474 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3250475 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term500 A t P a) = (term457 A t P a).
Proof. exact (MK_COMB (@lem3250474 A) (@lem3250473 A t P a)). Qed.
Lemma lem3250476 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3250477 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term501 A t P a) = (term458 A t P a).
Proof. exact (MK_COMB (@lem3250476) (@lem3250475 A t P a)). Qed.
Lemma lem3250478 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term502 A t P a s) = (term490 A s t P a).
Proof. exact (eq_refl (term502 A t P a s)). Qed.
Lemma lem3250479 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term503 A t P a) = (term491 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250478 A s t P a)). Qed.
Lemma lem3250480 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3250481 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term504 A t P a) = (term492 A t P a).
Proof. exact (MK_COMB (@lem3250480 A) (@lem3250479 A t P a)). Qed.
Lemma lem3250482 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term496 A t P a) = (term493 A t P a).
Proof. exact (MK_COMB (@lem3250477 A t P a) (@lem3250481 A t P a)). Qed.
Lemma lem3250483 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3250484 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term505 A t P a) = (term506 A t P a).
Proof. exact (MK_COMB (@lem3250483) (@lem3250482 A t P a)). Qed.
Lemma lem3250485 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term498 A t P a s) = (term454 A t P a s).
Proof. exact (eq_refl (term498 A t P a s)). Qed.
Lemma lem3250486 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3250487 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term507 A t P a s) = (term508 A t P a s).
Proof. exact (MK_COMB (@lem3250486) (@lem3250485 A t P a s)). Qed.
Lemma lem3250488 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term502 A t P a s) = (term490 A s t P a).
Proof. exact (eq_refl (term502 A t P a s)). Qed.
Lemma lem3250489 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term509 A t P a s) = (term510 A s t P a).
Proof. exact (MK_COMB (@lem3250487 A t P a s) (@lem3250488 A s t P a)). Qed.
Lemma lem3250490 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term511 A t P a) = (term512 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250489 A s t P a)). Qed.
Lemma lem3250491 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3250492 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term497 A t P a) = (term513 A t P a).
Proof. exact (MK_COMB (@lem3250491 A) (@lem3250490 A t P a)). Qed.
Lemma lem3250493 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term496 A t P a) = (term497 A t P a)) = ((term493 A t P a) = (term513 A t P a)).
Proof. exact (MK_COMB (@lem3250484 A t P a) (@lem3250492 A t P a)). Qed.
Lemma lem3250494 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term493 A t P a) = (term513 A t P a).
Proof. exact (EQ_MP (@lem3250493 A t P a) (@lem3250471 A t P a)). Qed.
Lemma lem3250497 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term514 A t P a) = (term514 A t P a).
Proof. exact (eq_refl (term514 A t P a)). Qed.
Lemma lem3250498 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term514 A t P a) = ((term493 A t P a) = (term513 A t P a)).
Proof. exact (eq_refl (term514 A t P a)). Qed.
Lemma lem3250499 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term515 A t P a) = (term515 A t P a).
Proof. exact (eq_refl (term515 A t P a)). Qed.
Lemma lem3250500 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term514 A t P a) = (term514 A t P a)) = ((term514 A t P a) = ((term493 A t P a) = (term513 A t P a))).
Proof. exact (MK_COMB (@lem3250499 A t P a) (@lem3250498 A t P a)). Qed.
Lemma lem3250501 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term514 A t P a) = ((term493 A t P a) = (term513 A t P a)).
Proof. exact (eq_refl (term514 A t P a)). Qed.
Lemma lem3250502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3250503 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term515 A t P a) = (term516 A t P a).
Proof. exact (MK_COMB (@lem3250502) (@lem3250501 A t P a)). Qed.
Lemma lem3250504 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term493 A t P a) = (term513 A t P a)) = ((term493 A t P a) = (term513 A t P a)).
Proof. exact (eq_refl ((term493 A t P a) = (term513 A t P a))). Qed.
Lemma lem3250505 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term514 A t P a) = ((term493 A t P a) = (term513 A t P a))) = (((term493 A t P a) = (term513 A t P a)) = ((term493 A t P a) = (term513 A t P a))).
Proof. exact (MK_COMB (@lem3250503 A t P a) (@lem3250504 A t P a)). Qed.
Lemma lem3250506 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term514 A t P a) = (term514 A t P a)) = (((term493 A t P a) = (term513 A t P a)) = ((term493 A t P a) = (term513 A t P a))).
Proof. exact (TRANS (@lem3250500 A t P a) (@lem3250505 A t P a)). Qed.
Lemma lem3250507 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : ((term493 A t P a) = (term513 A t P a)) = ((term493 A t P a) = (term513 A t P a)).
Proof. exact (EQ_MP (@lem3250506 A t P a) (@lem3250497 A t P a)). Qed.
Lemma lem3250508 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term493 A t P a) = (term513 A t P a).
Proof. exact (EQ_MP (@lem3250507 A t P a) (@lem3250494 A t P a)). Qed.
Lemma lem3250510 {A : Type'} (P : Prop) (Q : A -> Prop) : (term517 A P Q) = (term518 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3250511 {A : Type'} (P : Prop) (Q : type686 A) : (term519 A P Q) = (term520 A P Q).
Proof. exact (@lem3250510 (A -> Prop) P Q). Qed.
Lemma lem3250512 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term521 A s t P a) = (term522 A s t P a).
Proof. exact (@lem3250511 A (term454 A t P a s) (term489 A s t P a)). Qed.
Lemma lem3250513 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term523 A s t P a u') = (term487 A s u' t P a).
Proof. exact (eq_refl (term523 A s t P a u')). Qed.
Lemma lem3250514 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term524 A s t P a) = (term489 A s t P a).
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3250513 A s u' t P a)). Qed.
Lemma lem3250515 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3250516 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term525 A s t P a) = (term490 A s t P a).
Proof. exact (MK_COMB (@lem3250515 A) (@lem3250514 A s t P a)). Qed.
Lemma lem3250517 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term508 A t P a s) = (term508 A t P a s).
Proof. exact (eq_refl (term508 A t P a s)). Qed.
Lemma lem3250518 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term521 A s t P a) = (term510 A s t P a).
Proof. exact (MK_COMB (@lem3250517 A t P a s) (@lem3250516 A s t P a)). Qed.
Lemma lem3250519 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3250520 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term526 A s t P a) = (term527 A s t P a).
Proof. exact (MK_COMB (@lem3250519) (@lem3250518 A s t P a)). Qed.
Lemma lem3250521 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term523 A s t P a u') = (term487 A s u' t P a).
Proof. exact (eq_refl (term523 A s t P a u')). Qed.
Lemma lem3250522 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term508 A t P a s) = (term508 A t P a s).
Proof. exact (eq_refl (term508 A t P a s)). Qed.
Lemma lem3250523 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term528 A s t P a u') = (term529 A s u' t P a).
Proof. exact (MK_COMB (@lem3250522 A t P a s) (@lem3250521 A s u' t P a)). Qed.
Lemma lem3250524 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term530 A s t P a) = (term531 A s t P a).
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3250523 A s u' t P a)). Qed.
Lemma lem3250525 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3250526 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term522 A s t P a) = (term532 A s t P a).
Proof. exact (MK_COMB (@lem3250525 A) (@lem3250524 A s t P a)). Qed.
Lemma lem3250527 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : ((term521 A s t P a) = (term522 A s t P a)) = ((term510 A s t P a) = (term532 A s t P a)).
Proof. exact (MK_COMB (@lem3250520 A s t P a) (@lem3250526 A s t P a)). Qed.
Lemma lem3250528 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term510 A s t P a) = (term532 A s t P a).
Proof. exact (EQ_MP (@lem3250527 A s t P a) (@lem3250512 A s t P a)). Qed.
Lemma lem3250529 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term512 A t P a) = (term533 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250528 A s t P a)). Qed.
Lemma lem3250530 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3250531 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term513 A t P a) = (term534 A t P a).
Proof. exact (MK_COMB (@lem3250530 A) (@lem3250529 A t P a)). Qed.
Lemma lem3250532 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term493 A t P a) = (term534 A t P a).
Proof. exact (TRANS (@lem3250508 A t P a) (@lem3250531 A t P a)). Qed.
Lemma lem3250534 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term443 A t P a) = (term534 A t P a).
Proof. exact (TRANS (@lem3250467 A t P a) (@lem3250532 A t P a)). Qed.
Lemma lem3250535 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term355 A t P a) = (term534 A t P a).
Proof. exact (TRANS (@lem3250191 A t P a) (@lem3250534 A t P a)). Qed.
Lemma lem3250536 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term355 A t P a) : term534 A t P a.
Proof. exact (EQ_MP (@lem3250535 A t P a) (@lem3250082 A t P a h1)). Qed.
Lemma lem3250537 {A : Type'} (s : A -> Prop) : ((@UNION A (@EMPTY A) s) = s) = ((@UNION A (@EMPTY A) s) = s).
Proof. exact (eq_refl ((@UNION A (@EMPTY A) s) = s)). Qed.
Lemma lem3250538 {A : Type'} : (term379 A) = (term379 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250537 A s)). Qed.
Lemma lem3250539 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250540 {A : Type'} : (term380 A) = (term380 A).
Proof. exact (MK_COMB (@lem3250539 A) (@lem3250538 A)). Qed.
Lemma lem3250541 {A : Type'} (s : A -> Prop) : ((@UNION A s (@EMPTY A)) = s) = ((@UNION A s (@EMPTY A)) = s).
Proof. exact (eq_refl ((@UNION A s (@EMPTY A)) = s)). Qed.
Lemma lem3250542 {A : Type'} : (term377 A) = (term377 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250541 A s)). Qed.
Lemma lem3250543 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250544 {A : Type'} : (term378 A) = (term378 A).
Proof. exact (MK_COMB (@lem3250543 A) (@lem3250542 A)). Qed.
Lemma lem3250545 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3250546 {A : Type'} : (term381 A) = (term381 A).
Proof. exact (MK_COMB (@lem3250545) (@lem3250540 A)). Qed.
Lemma lem3250559 {A : Type'} : (term356 A) = (term356 A).
Proof. exact (MK_COMB (@lem3250546 A) (@lem3250544 A)). Qed.
Lemma lem3250560 {A : Type'} (h1 : term356 A) : term356 A.
Proof. exact (EQ_MP (@lem3250559 A) (@lem3250083 A h1)). Qed.
Lemma lem3250561 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term532 A s t P a) : term532 A s t P a.
Proof. exact (h1). Qed.
Lemma lem3250562 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term529 A s u' t P a) : term529 A s u' t P a.
Proof. exact (h1). Qed.
Lemma lem3250571 {A : Type'} (s : A -> Prop) : ((@UNION A s (@EMPTY A)) = s) = ((@UNION A s (@EMPTY A)) = s).
Proof. exact (eq_refl ((@UNION A s (@EMPTY A)) = s)). Qed.
Lemma lem3250572 {A : Type'} : (term377 A) = (term377 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250571 A s)). Qed.
Lemma lem3250573 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250574 {A : Type'} : (term378 A) = (term378 A).
Proof. exact (MK_COMB (@lem3250573 A) (@lem3250572 A)). Qed.
Lemma lem3250583 {A : Type'} (s : A -> Prop) : ((@UNION A (@EMPTY A) s) = s) = ((@UNION A (@EMPTY A) s) = s).
Proof. exact (eq_refl ((@UNION A (@EMPTY A) s) = s)). Qed.
Lemma lem3250584 {A : Type'} : (term379 A) = (term379 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250583 A s)). Qed.
Lemma lem3250585 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250586 {A : Type'} : (term380 A) = (term380 A).
Proof. exact (MK_COMB (@lem3250585 A) (@lem3250584 A)). Qed.
Lemma lem3250587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3250588 {A : Type'} : (term381 A) = (term381 A).
Proof. exact (MK_COMB (@lem3250587) (@lem3250586 A)). Qed.
Lemma lem3250589 {A : Type'} : (term356 A) = (term356 A).
Proof. exact (MK_COMB (@lem3250588 A) (@lem3250574 A)). Qed.
Lemma lem3250590 {A : Type'} (h1 : term356 A) : term356 A.
Proof. exact (EQ_MP (@lem3250589 A) (@lem3250560 A h1)). Qed.
Lemma lem3250617 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term422 A t P a s) = (term422 A t P a s).
Proof. exact (eq_refl (term422 A t P a s)). Qed.
Lemma lem3250618 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term430 A t P a) = (term430 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250617 A t P a s)). Qed.
Lemma lem3250619 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250620 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term431 A t P a) = (term431 A t P a).
Proof. exact (MK_COMB (@lem3250619 A) (@lem3250618 A t P a)). Qed.
Lemma lem3250659 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (s : A -> Prop) (u' : A -> Prop) : (term485 A a t P s u') = (term485 A a t P s u').
Proof. exact (eq_refl (term485 A a t P s u')). Qed.
Lemma lem3250660 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term487 A s u' t P a) = (term487 A s u' t P a).
Proof. exact (MK_COMB (@lem3250659 A a t P s u') (@lem3250620 A t P a)). Qed.
Lemma lem3250689 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term420 A t P a s) = (term420 A t P a s).
Proof. exact (eq_refl (term420 A t P a s)). Qed.
Lemma lem3250730 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term395 A a t P t' u') = (term395 A a t P t' u').
Proof. exact (eq_refl (term395 A a t P t' u')). Qed.
Lemma lem3250731 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term405 A a t P t') = (term405 A a t P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3250730 A a t P t' u')). Qed.
Lemma lem3250732 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250733 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term406 A a t P t') = (term406 A a t P t').
Proof. exact (MK_COMB (@lem3250732 A) (@lem3250731 A a t P t')). Qed.
Lemma lem3250734 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term414 A a t P) = (term414 A a t P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3250733 A a t P t')). Qed.
Lemma lem3250735 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250736 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term415 A a t P) = (term415 A a t P).
Proof. exact (MK_COMB (@lem3250735 A) (@lem3250734 A a t P)). Qed.
Lemma lem3250737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3250738 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term437 A a t P) = (term437 A a t P).
Proof. exact (MK_COMB (@lem3250737) (@lem3250736 A a t P)). Qed.
Lemma lem3250739 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term454 A t P a s) = (term454 A t P a s).
Proof. exact (MK_COMB (@lem3250738 A a t P) (@lem3250689 A t P a s)). Qed.
Lemma lem3250740 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3250741 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term508 A t P a s) = (term508 A t P a s).
Proof. exact (MK_COMB (@lem3250740) (@lem3250739 A t P a s)). Qed.
Lemma lem3250742 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) : (term529 A s u' t P a) = (term529 A s u' t P a).
Proof. exact (MK_COMB (@lem3250741 A t P a s) (@lem3250660 A s u' t P a)). Qed.
Lemma lem3250743 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term529 A s u' t P a) : term529 A s u' t P a.
Proof. exact (EQ_MP (@lem3250742 A s u' t P a) (@lem3250562 A s u' t P a h1)). Qed.
Lemma lem3250745 {A : Type'} (h1 : term356 A) : term380 A.
Proof. exact (proj1 (@lem3250590 A h1)). Qed.
Lemma lem3250746 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term454 A t P a s.
Proof. exact (h1). Qed.
Lemma lem3250747 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term487 A s u' t P a.
Proof. exact (h1). Qed.
Lemma lem3250748 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term420 A t P a s.
Proof. exact (proj2 (@lem3250746 A t P a s h1)). Qed.
Lemma lem3250749 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term415 A a t P.
Proof. exact (proj1 (@lem3250746 A t P a s h1)). Qed.
Lemma lem3250750 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term417 A P a s.
Proof. exact (proj2 (@lem3250748 A t P a s h1)). Qed.
Lemma lem3250754 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term431 A t P a.
Proof. exact (proj2 (@lem3250747 A s u' t P a h1)). Qed.
Lemma lem3250755 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term391 A a t P s u'.
Proof. exact (proj1 (@lem3250747 A s u' t P a h1)). Qed.
Lemma lem3250757 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term340 A s a u' t.
Proof. exact (proj1 (@lem3250755 A s u' t P a h1)). Qed.
Lemma lem3250759 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term17 A s a.
Proof. exact (proj1 (@lem3250757 A s u' t P a h1)). Qed.
Lemma lem3250763 {A : Type'} (s : A -> Prop) : ((@UNION A (@EMPTY A) s) = s) = ((@UNION A (@EMPTY A) s) = s).
Proof. exact (eq_refl ((@UNION A (@EMPTY A) s) = s)). Qed.
Lemma lem3250764 {A : Type'} : (term379 A) = (term379 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250763 A s)). Qed.
Lemma lem3250765 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250767 {A : Type'} : (term380 A) = (term380 A).
Proof. exact (MK_COMB (@lem3250765 A) (@lem3250764 A)). Qed.
Lemma lem3250768 {A : Type'} (h1 : term356 A) : term380 A.
Proof. exact (EQ_MP (@lem3250767 A) (@lem3250745 A h1)). Qed.
Lemma lem3250777 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term343 A P t' u') = (term343 A P t' u').
Proof. exact (eq_refl (term343 A P t' u')). Qed.
Lemma lem3250794 {A : Type'} (t' : A -> Prop) (a : A) (u' : A -> Prop) (t : A -> Prop) : (term388 A t' a u' t) = (term535 A t' a u' t).
Proof. exact (@lem19699 (term536 A t') (term537 A t' a) (term384 A u' t)). Qed.
Lemma lem3250795 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3250796 {A : Type'} (t' : A -> Prop) (a : A) (u' : A -> Prop) (t : A -> Prop) : (term393 A t' a u' t) = (term538 A t' a u' t).
Proof. exact (MK_COMB (@lem3250795) (@lem3250794 A t' a u' t)). Qed.
Lemma lem3250797 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term395 A a t P t' u') = (term539 A a t P t' u').
Proof. exact (MK_COMB (@lem3250796 A t' a u' t) (@lem3250777 A P t' u')). Qed.
Lemma lem3250804 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term539 A a t P t' u') = (term540 A a t P t' u').
Proof. exact (@lem19699 (term541 A t' u' t) (term542 A t' a u' t) (term343 A P t' u')). Qed.
Lemma lem3250805 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term395 A a t P t' u') = (term540 A a t P t' u').
Proof. exact (TRANS (@lem3250797 A a t P t' u') (@lem3250804 A a t P t' u')). Qed.
Lemma lem3250806 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term405 A a t P t') = (term543 A a t P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3250805 A a t P t' u')). Qed.
Lemma lem3250807 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250808 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term406 A a t P t') = (term544 A a t P t').
Proof. exact (MK_COMB (@lem3250807 A) (@lem3250806 A a t P t')). Qed.
Lemma lem3250809 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term414 A a t P) = (term545 A a t P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3250808 A a t P t')). Qed.
Lemma lem3250810 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250812 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term415 A a t P) = (term546 A a t P).
Proof. exact (MK_COMB (@lem3250810 A) (@lem3250809 A a t P)). Qed.
Lemma lem3250813 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term546 A a t P.
Proof. exact (EQ_MP (@lem3250812 A a t P) (@lem3250749 A t P a s h1)). Qed.
Lemma lem3250821 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term547 A P s) : term547 A P s.
Proof. exact (h1). Qed.
Lemma lem3250837 {A : Type'} (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term343 A P t' u') = (term343 A P t' u').
Proof. exact (eq_refl (term343 A P t' u')). Qed.
Lemma lem3250854 {A : Type'} (t' : A -> Prop) (a : A) (u' : A -> Prop) (t : A -> Prop) : (term388 A t' a u' t) = (term535 A t' a u' t).
Proof. exact (@lem19699 (term536 A t') (term537 A t' a) (term384 A u' t)). Qed.
Lemma lem3250855 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3250856 {A : Type'} (t' : A -> Prop) (a : A) (u' : A -> Prop) (t : A -> Prop) : (term393 A t' a u' t) = (term538 A t' a u' t).
Proof. exact (MK_COMB (@lem3250855) (@lem3250854 A t' a u' t)). Qed.
Lemma lem3250857 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term395 A a t P t' u') = (term539 A a t P t' u').
Proof. exact (MK_COMB (@lem3250856 A t' a u' t) (@lem3250837 A P t' u')). Qed.
Lemma lem3250864 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term539 A a t P t' u') = (term540 A a t P t' u').
Proof. exact (@lem19699 (term541 A t' u' t) (term542 A t' a u' t) (term343 A P t' u')). Qed.
Lemma lem3250865 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) (u' : A -> Prop) : (term395 A a t P t' u') = (term540 A a t P t' u').
Proof. exact (TRANS (@lem3250857 A a t P t' u') (@lem3250864 A a t P t' u')). Qed.
Lemma lem3250866 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term405 A a t P t') = (term543 A a t P t').
Proof. exact (fun_ext (fun u' : A -> Prop => @lem3250865 A a t P t' u')). Qed.
Lemma lem3250867 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250868 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (t' : A -> Prop) : (term406 A a t P t') = (term544 A a t P t').
Proof. exact (MK_COMB (@lem3250867 A) (@lem3250866 A a t P t')). Qed.
Lemma lem3250869 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term414 A a t P) = (term545 A a t P).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem3250868 A a t P t')). Qed.
Lemma lem3250870 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250872 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) : (term415 A a t P) = (term546 A a t P).
Proof. exact (MK_COMB (@lem3250870 A) (@lem3250869 A a t P)). Qed.
Lemma lem3250873 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term546 A a t P.
Proof. exact (EQ_MP (@lem3250872 A a t P) (@lem3250749 A t P a s h1)). Qed.
Lemma lem3250881 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) (h1 : term548 A P a s) : term548 A P a s.
Proof. exact (h1). Qed.
Lemma lem3250883 {A : Type'} (s : A -> Prop) : ((@UNION A (@EMPTY A) s) = s) = ((@UNION A (@EMPTY A) s) = s).
Proof. exact (eq_refl ((@UNION A (@EMPTY A) s) = s)). Qed.
Lemma lem3250884 {A : Type'} : (term379 A) = (term379 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250883 A s)). Qed.
Lemma lem3250885 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250887 {A : Type'} : (term380 A) = (term380 A).
Proof. exact (MK_COMB (@lem3250885 A) (@lem3250884 A)). Qed.
Lemma lem3250888 {A : Type'} (h1 : term356 A) : term380 A.
Proof. exact (EQ_MP (@lem3250887 A) (@lem3250745 A h1)). Qed.
Lemma lem3250913 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term422 A t P a s) = (term549 A t P a s).
Proof. exact (@lem19490 (P s) (term384 A s t) (term325 A P a s)). Qed.
Lemma lem3250914 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term430 A t P a) = (term550 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250913 A t P a s)). Qed.
Lemma lem3250915 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250917 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term431 A t P a) = (term551 A t P a).
Proof. exact (MK_COMB (@lem3250915 A) (@lem3250914 A t P a)). Qed.
Lemma lem3250918 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term551 A t P a.
Proof. exact (EQ_MP (@lem3250917 A t P a) (@lem3250754 A s u' t P a h1)). Qed.
Lemma lem3250930 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3250962 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) : (term422 A t P a s) = (term549 A t P a s).
Proof. exact (@lem19490 (P s) (term384 A s t) (term325 A P a s)). Qed.
Lemma lem3250963 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term430 A t P a) = (term550 A t P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3250962 A t P a s)). Qed.
Lemma lem3250964 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3250966 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term431 A t P a) = (term551 A t P a).
Proof. exact (MK_COMB (@lem3250964 A) (@lem3250963 A t P a)). Qed.
Lemma lem3250967 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term551 A t P a.
Proof. exact (EQ_MP (@lem3250966 A t P a) (@lem3250754 A s u' t P a h1)). Qed.
Lemma lem3250979 {A : Type'} (s : A -> Prop) (a : A) (h1 : s = (@INSERT A a (@EMPTY A))) : s = (@INSERT A a (@EMPTY A)).
Proof. exact (h1). Qed.
Lemma lem3250980 {A : Type'} (_33290 : A -> Prop) (h1 : term356 A) : term552 A _33290.
Proof. exact (@lem3250768 A h1 _33290). Qed.
Lemma lem3250981 {A : Type'} (_33290 : A -> Prop) : (term552 A _33290) = ((@UNION A (@EMPTY A) _33290) = _33290).
Proof. exact (eq_refl (term552 A _33290)). Qed.
Lemma lem3250986 {A : Type'} (_33292 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term553 A a t P _33292.
Proof. exact (@lem3250813 A t P a s h1 _33292). Qed.
Lemma lem3250987 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (_33292 : A -> Prop) : (term553 A a t P _33292) = (term544 A a t P _33292).
Proof. exact (eq_refl (term553 A a t P _33292)). Qed.
Lemma lem3250988 {A : Type'} (_33292 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term544 A a t P _33292.
Proof. exact (EQ_MP (@lem3250987 A a t P _33292) (@lem3250986 A _33292 t P a s h1)). Qed.
Lemma lem3250989 {A : Type'} (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term554 A a t P _33292 _33293.
Proof. exact (@lem3250988 A _33292 t P a s h1 _33293). Qed.
Lemma lem3250990 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) : (term554 A a t P _33292 _33293) = (term540 A a t P _33292 _33293).
Proof. exact (eq_refl (term554 A a t P _33292 _33293)). Qed.
Lemma lem3250991 {A : Type'} (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term540 A a t P _33292 _33293.
Proof. exact (EQ_MP (@lem3250990 A a t P _33292 _33293) (@lem3250989 A _33292 _33293 t P a s h1)). Qed.
Lemma lem3250998 {A : Type'} (_33296 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term553 A a t P _33296.
Proof. exact (@lem3250873 A t P a s h1 _33296). Qed.
Lemma lem3250999 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (_33296 : A -> Prop) : (term553 A a t P _33296) = (term544 A a t P _33296).
Proof. exact (eq_refl (term553 A a t P _33296)). Qed.
Lemma lem3251000 {A : Type'} (_33296 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term544 A a t P _33296.
Proof. exact (EQ_MP (@lem3250999 A a t P _33296) (@lem3250998 A _33296 t P a s h1)). Qed.
Lemma lem3251001 {A : Type'} (_33296 : A -> Prop) (_33297 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term554 A a t P _33296 _33297.
Proof. exact (@lem3251000 A _33296 t P a s h1 _33297). Qed.
Lemma lem3251002 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (_33296 : A -> Prop) (_33297 : A -> Prop) : (term554 A a t P _33296 _33297) = (term540 A a t P _33296 _33297).
Proof. exact (eq_refl (term554 A a t P _33296 _33297)). Qed.
Lemma lem3251003 {A : Type'} (_33296 : A -> Prop) (_33297 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term540 A a t P _33296 _33297.
Proof. exact (EQ_MP (@lem3251002 A a t P _33296 _33297) (@lem3251001 A _33296 _33297 t P a s h1)). Qed.
Lemma lem3251004 {A : Type'} (_33298 : A -> Prop) (h1 : term356 A) : term552 A _33298.
Proof. exact (@lem3250888 A h1 _33298). Qed.
Lemma lem3251005 {A : Type'} (_33298 : A -> Prop) : (term552 A _33298) = ((@UNION A (@EMPTY A) _33298) = _33298).
Proof. exact (eq_refl (term552 A _33298)). Qed.
Lemma lem3251010 {A : Type'} (_33300 : A -> Prop) (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term555 A t P a _33300.
Proof. exact (@lem3250918 A s u' t P a h1 _33300). Qed.
Lemma lem3251011 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (_33300 : A -> Prop) : (term555 A t P a _33300) = (term549 A t P a _33300).
Proof. exact (eq_refl (term555 A t P a _33300)). Qed.
Lemma lem3251012 {A : Type'} (_33300 : A -> Prop) (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term549 A t P a _33300.
Proof. exact (EQ_MP (@lem3251011 A t P a _33300) (@lem3251010 A _33300 s u' t P a h1)). Qed.
Lemma lem3251019 {A : Type'} (_33303 : A -> Prop) (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term555 A t P a _33303.
Proof. exact (@lem3250967 A s u' t P a h1 _33303). Qed.
Lemma lem3251020 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (_33303 : A -> Prop) : (term555 A t P a _33303) = (term549 A t P a _33303).
Proof. exact (eq_refl (term555 A t P a _33303)). Qed.
Lemma lem3251021 {A : Type'} (_33303 : A -> Prop) (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term549 A t P a _33303.
Proof. exact (EQ_MP (@lem3251020 A t P a _33303) (@lem3251019 A _33303 s u' t P a h1)). Qed.
Lemma lem3251023 {A : Type'} (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term556 A t P _33292 _33293.
Proof. exact (proj1 (@lem3250991 A _33292 _33293 t P a s h1)). Qed.
Lemma lem3251024 {A : Type'} (_33296 : A -> Prop) (_33297 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term557 A a t P _33296 _33297.
Proof. exact (proj2 (@lem3251003 A _33296 _33297 t P a s h1)). Qed.
Lemma lem3251037 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term547 A P s) : term547 A P s.
Proof. exact (h1). Qed.
Lemma lem3251048 {A : Type'} (t : A -> Prop) (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) : (term556 A t P _33292 _33293) = (term558 A t P _33292 _33293).
Proof. exact (@lem3247673 (term536 A _33292) (term384 A _33293 t) (term343 A P _33292 _33293)). Qed.
Lemma lem3251049 {A : Type'} (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term558 A t P _33292 _33293.
Proof. exact (EQ_MP (@lem3251048 A t P _33292 _33293) (@lem3251023 A _33292 _33293 t P a s h1)). Qed.
Lemma lem3251069 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) (h1 : term548 A P a s) : term548 A P a s.
Proof. exact (h1). Qed.
Lemma lem3251092 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (_33296 : A -> Prop) (_33297 : A -> Prop) : (term557 A a t P _33296 _33297) = (term559 A a t P _33296 _33297).
Proof. exact (@lem3247673 (term537 A _33296 a) (term384 A _33297 t) (term343 A P _33296 _33297)). Qed.
Lemma lem3251093 {A : Type'} (_33296 : A -> Prop) (_33297 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term559 A a t P _33296 _33297.
Proof. exact (EQ_MP (@lem3251092 A a t P _33296 _33297) (@lem3251024 A _33296 _33297 t P a s h1)). Qed.
Lemma lem3251099 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term560 A P s u'.
Proof. exact (proj2 (@lem3250755 A s u' t P a h1)). Qed.
Lemma lem3251103 {A : Type'} (s : A -> Prop) (h1 : s = (@EMPTY A)) : s = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3251121 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term560 A P s u'.
Proof. exact (proj2 (@lem3250755 A s u' t P a h1)). Qed.
Lemma lem3251125 {A : Type'} (s : A -> Prop) (a : A) (h1 : s = (@INSERT A a (@EMPTY A))) : s = (@INSERT A a (@EMPTY A)).
Proof. exact (h1). Qed.
Lemma lem3251180 {A : Type'} (P : type686 A) (u' : A -> Prop) : (term561 A P u') = (term561 A P u').
Proof. exact (eq_refl (term561 A P u')). Qed.
Lemma lem3251181 {A : Type'} (P : type686 A) (u' : A -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term562 A P u' s) = (term563 A P u').
Proof. exact (MK_COMB (@lem3251180 A P u') (@lem3251103 A s h1)). Qed.
Lemma lem3251182 {A : Type'} (P : type686 A) (u' : A -> Prop) : (term563 A P u') = (term564 A P u').
Proof. exact (eq_refl (term563 A P u')). Qed.
Lemma lem3251183 {A : Type'} (P : type686 A) (u' : A -> Prop) (s : A -> Prop) : (term565 A P u' s) = (term565 A P u' s).
Proof. exact (eq_refl (term565 A P u' s)). Qed.
Lemma lem3251184 {A : Type'} (s : A -> Prop) (P : type686 A) (u' : A -> Prop) : ((term562 A P u' s) = (term563 A P u')) = ((term562 A P u' s) = (term564 A P u')).
Proof. exact (MK_COMB (@lem3251183 A P u' s) (@lem3251182 A P u')). Qed.
Lemma lem3251185 {A : Type'} (P : type686 A) (s : A -> Prop) (u' : A -> Prop) : (term562 A P u' s) = (term560 A P s u').
Proof. exact (eq_refl (term562 A P u' s)). Qed.
Lemma lem3251186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3251187 {A : Type'} (P : type686 A) (s : A -> Prop) (u' : A -> Prop) : (term565 A P u' s) = (term566 A P s u').
Proof. exact (MK_COMB (@lem3251186) (@lem3251185 A P s u')). Qed.
Lemma lem3251188 {A : Type'} (P : type686 A) (u' : A -> Prop) : (term564 A P u') = (term564 A P u').
Proof. exact (eq_refl (term564 A P u')). Qed.
Lemma lem3251189 {A : Type'} (s : A -> Prop) (P : type686 A) (u' : A -> Prop) : ((term562 A P u' s) = (term564 A P u')) = ((term560 A P s u') = (term564 A P u')).
Proof. exact (MK_COMB (@lem3251187 A P s u') (@lem3251188 A P u')). Qed.
Lemma lem3251190 {A : Type'} (s : A -> Prop) (P : type686 A) (u' : A -> Prop) : ((term562 A P u' s) = (term563 A P u')) = ((term560 A P s u') = (term564 A P u')).
Proof. exact (TRANS (@lem3251184 A s P u') (@lem3251189 A s P u')). Qed.
Lemma lem3251191 {A : Type'} (P : type686 A) (u' : A -> Prop) (s : A -> Prop) (h1 : s = (@EMPTY A)) : (term560 A P s u') = (term564 A P u').
Proof. exact (EQ_MP (@lem3251190 A s P u') (@lem3251181 A P u' s h1)). Qed.
Lemma lem3251192 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term487 A s u' t P a) (h2 : s = (@EMPTY A)) : term564 A P u'.
Proof. exact (EQ_MP (@lem3251191 A P u' s h2) (@lem3251099 A s u' t P a h1)). Qed.
Lemma lem3251220 {A : Type'} (_33300 : A -> Prop) (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term567 A t P _33300.
Proof. exact (proj1 (@lem3251012 A _33300 s u' t P a h1)). Qed.
Lemma lem3251277 {A : Type'} (P : type686 A) (u' : A -> Prop) : (term561 A P u') = (term561 A P u').
Proof. exact (eq_refl (term561 A P u')). Qed.
Lemma lem3251278 {A : Type'} (P : type686 A) (u' : A -> Prop) (s : A -> Prop) (a : A) (h1 : s = (@INSERT A a (@EMPTY A))) : (term562 A P u' s) = (term568 A P u' a).
Proof. exact (MK_COMB (@lem3251277 A P u') (@lem3251125 A s a h1)). Qed.
Lemma lem3251279 {A : Type'} (P : type686 A) (a : A) (u' : A -> Prop) : (term568 A P u' a) = (term548 A P a u').
Proof. exact (eq_refl (term568 A P u' a)). Qed.
Lemma lem3251280 {A : Type'} (P : type686 A) (u' : A -> Prop) (s : A -> Prop) : (term565 A P u' s) = (term565 A P u' s).
Proof. exact (eq_refl (term565 A P u' s)). Qed.
Lemma lem3251281 {A : Type'} (s : A -> Prop) (P : type686 A) (a : A) (u' : A -> Prop) : ((term562 A P u' s) = (term568 A P u' a)) = ((term562 A P u' s) = (term548 A P a u')).
Proof. exact (MK_COMB (@lem3251280 A P u' s) (@lem3251279 A P a u')). Qed.
Lemma lem3251282 {A : Type'} (P : type686 A) (s : A -> Prop) (u' : A -> Prop) : (term562 A P u' s) = (term560 A P s u').
Proof. exact (eq_refl (term562 A P u' s)). Qed.
Lemma lem3251283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3251284 {A : Type'} (P : type686 A) (s : A -> Prop) (u' : A -> Prop) : (term565 A P u' s) = (term566 A P s u').
Proof. exact (MK_COMB (@lem3251283) (@lem3251282 A P s u')). Qed.
Lemma lem3251285 {A : Type'} (P : type686 A) (a : A) (u' : A -> Prop) : (term548 A P a u') = (term548 A P a u').
Proof. exact (eq_refl (term548 A P a u')). Qed.
Lemma lem3251286 {A : Type'} (s : A -> Prop) (P : type686 A) (a : A) (u' : A -> Prop) : ((term562 A P u' s) = (term548 A P a u')) = ((term560 A P s u') = (term548 A P a u')).
Proof. exact (MK_COMB (@lem3251284 A P s u') (@lem3251285 A P a u')). Qed.
Lemma lem3251287 {A : Type'} (s : A -> Prop) (P : type686 A) (a : A) (u' : A -> Prop) : ((term562 A P u' s) = (term568 A P u' a)) = ((term560 A P s u') = (term548 A P a u')).
Proof. exact (TRANS (@lem3251281 A s P a u') (@lem3251286 A s P a u')). Qed.
Lemma lem3251288 {A : Type'} (P : type686 A) (u' : A -> Prop) (s : A -> Prop) (a : A) (h1 : s = (@INSERT A a (@EMPTY A))) : (term560 A P s u') = (term548 A P a u').
Proof. exact (EQ_MP (@lem3251287 A s P a u') (@lem3251278 A P u' s a h1)). Qed.
Lemma lem3251289 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (s : A -> Prop) (a : A) (h1 : term487 A s u' t P a) (h2 : s = (@INSERT A a (@EMPTY A))) : term548 A P a u'.
Proof. exact (EQ_MP (@lem3251288 A P u' s a h2) (@lem3251121 A s u' t P a h1)). Qed.
Lemma lem3251331 {A : Type'} (_33303 : A -> Prop) (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term569 A t P a _33303.
Proof. exact (proj2 (@lem3251021 A _33303 s u' t P a h1)). Qed.
Lemma lem3251332 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3251333 {A : Type'} (_33332 : A -> Prop) (_33333 : A -> Prop) (h1 : _33332 = _33333) : _33332 = _33333.
Proof. exact (h1). Qed.
Lemma lem3251334 {A : Type'} (P : type686 A) (_33332 : A -> Prop) (_33333 : A -> Prop) (h1 : _33332 = _33333) : (P _33332) = (P _33333).
Proof. exact (MK_COMB (@lem3251332 A P) (@lem3251333 A _33332 _33333 h1)). Qed.
Lemma lem3251336 (b : Prop) (a : Prop) : term257 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3251337 {A : Type'} (_33333 : A -> Prop) (P : type686 A) (_33332 : A -> Prop) : term570 A _33333 P _33332.
Proof. exact (@lem3251336 (P _33333) (P _33332)). Qed.
Lemma lem3251338 {A : Type'} (P : type686 A) (_33332 : A -> Prop) (_33333 : A -> Prop) (h1 : _33332 = _33333) : term571 A _33333 P _33332.
Proof. exact (@lem3251337 A _33333 P _33332 (@lem3251334 A P _33332 _33333 h1)). Qed.
Lemma lem3251339 {A : Type'} (_33333 : A -> Prop) (P : type686 A) (_33332 : A -> Prop) : term572 A _33333 P _33332.
Proof. exact (fun h0 : _33332 = _33333 => @lem3251338 A P _33332 _33333 h0). Qed.
Lemma lem3251341 (a : Prop) (b : Prop) : (a -> b) = (term261 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3251342 {A : Type'} (_33333 : A -> Prop) (P : type686 A) (_33332 : A -> Prop) : (term572 A _33333 P _33332) = (term573 A _33333 P _33332).
Proof. exact (@lem3251341 (_33332 = _33333) (term571 A _33333 P _33332)). Qed.
Lemma lem3251343 {A : Type'} (_33333 : A -> Prop) (P : type686 A) (_33332 : A -> Prop) : term573 A _33333 P _33332.
Proof. exact (EQ_MP (@lem3251342 A _33333 P _33332) (@lem3251339 A _33333 P _33332)). Qed.
Lemma lem3251398 {A : Type'} (_33290 : A -> Prop) (h1 : term356 A) : (@UNION A (@EMPTY A) _33290) = _33290.
Proof. exact (EQ_MP (@lem3250981 A _33290) (@lem3250980 A _33290 h1)). Qed.
Lemma lem3251399 {A : Type'} (_33290 : A -> Prop) (h1 : term356 A) : (@UNION A (@EMPTY A) _33290) = _33290.
Proof. exact (@lem3251398 A _33290 h1). Qed.
Lemma lem3251400 {A : Type'} (s : A -> Prop) (h1 : term356 A) : (@UNION A (@EMPTY A) s) = s.
Proof. exact (@lem3251399 A s h1). Qed.
Lemma lem3251401 {A : Type'} (s : A -> Prop) (h1 : term356 A) : term574 A s.
Proof. exact (fun h0 : term575 A s => @lem3251400 A s h1). Qed.
Lemma lem3251403 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3251404 {A : Type'} (s : A -> Prop) : (term574 A s) = ((@UNION A (@EMPTY A) s) = s).
Proof. exact (@lem3251403 ((@UNION A (@EMPTY A) s) = s)). Qed.
Lemma lem3251405 {A : Type'} (s : A -> Prop) (h1 : term356 A) : (@UNION A (@EMPTY A) s) = s.
Proof. exact (EQ_MP (@lem3251404 A s) (@lem3251401 A s h1)). Qed.
Lemma lem3251407 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem3251408 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem3251407 A x). Qed.
Lemma lem3251409 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (@lem3251408 A (@EMPTY A)). Qed.
Lemma lem3251410 {A : Type'} : term576 A.
Proof. exact (fun h0 : term577 A => @lem3251409 A). Qed.
Lemma lem3251412 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3251413 {A : Type'} : (term576 A) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (@lem3251412 ((@EMPTY A) = (@EMPTY A))). Qed.
Lemma lem3251414 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (EQ_MP (@lem3251413 A) (@lem3251410 A)). Qed.
Lemma lem3251416 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : @SUBSET A s t.
Proof. exact (proj1 (@lem3250748 A t P a s h1)). Qed.
Lemma lem3251417 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term578 A s t.
Proof. exact (fun h0 : term384 A s t => @lem3251416 A t P a s h1). Qed.
Lemma lem3251419 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3251420 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term578 A s t) = (@SUBSET A s t).
Proof. exact (@lem3251419 (@SUBSET A s t)). Qed.
Lemma lem3251421 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : @SUBSET A s t.
Proof. exact (EQ_MP (@lem3251420 A s t) (@lem3251417 A t P a s h1)). Qed.
Lemma lem3251439 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3251440 {A : Type'} (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) : (term579 A t P _33292 _33293) = (term580 A P _33292 _33293 t).
Proof. exact (@lem3251439 (term343 A P _33292 _33293) (term384 A _33293 t)). Qed.
Lemma lem3251446 {A : Type'} (_33292 : A -> Prop) : (term581 A _33292) = (term581 A _33292).
Proof. exact (eq_refl (term581 A _33292)). Qed.
Lemma lem3251447 {A : Type'} (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) : (term558 A t P _33292 _33293) = (term582 A P _33292 _33293 t).
Proof. exact (MK_COMB (@lem3251446 A _33292) (@lem3251440 A P _33292 _33293 t)). Qed.
Lemma lem3251451 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3251452 {A : Type'} (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) : (term582 A P _33292 _33293 t) = (term583 A P _33292 _33293 t).
Proof. exact (@lem3251451 (term343 A P _33292 _33293) (term536 A _33292) (term384 A _33293 t)). Qed.
Lemma lem3251470 {A : Type'} (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) : (term558 A t P _33292 _33293) = (term583 A P _33292 _33293 t).
Proof. exact (TRANS (@lem3251447 A P _33292 _33293 t) (@lem3251452 A P _33292 _33293 t)). Qed.
Lemma lem3251471 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3251472 {A : Type'} (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) : (term584 A t P _33292 _33293) = (term585 A P _33292 _33293 t).
Proof. exact (MK_COMB (@lem3251471) (@lem3251470 A P _33292 _33293 t)). Qed.
Lemma lem3251490 {A : Type'} (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) : (term583 A P _33292 _33293 t) = (term583 A P _33292 _33293 t).
Proof. exact (eq_refl (term583 A P _33292 _33293 t)). Qed.
Lemma lem3251491 {A : Type'} (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) : ((term558 A t P _33292 _33293) = (term583 A P _33292 _33293 t)) = ((term583 A P _33292 _33293 t) = (term583 A P _33292 _33293 t)).
Proof. exact (MK_COMB (@lem3251472 A P _33292 _33293 t) (@lem3251490 A P _33292 _33293 t)). Qed.
Lemma lem3251493 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3251494 (x : Prop) : (x = x) = True.
Proof. exact (@lem3251493 Prop x). Qed.
Lemma lem3251495 {A : Type'} (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) : ((term583 A P _33292 _33293 t) = (term583 A P _33292 _33293 t)) = True.
Proof. exact (@lem3251494 (term583 A P _33292 _33293 t)). Qed.
Lemma lem3251496 {A : Type'} (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) : ((term558 A t P _33292 _33293) = (term583 A P _33292 _33293 t)) = True.
Proof. exact (TRANS (@lem3251491 A P _33292 _33293 t) (@lem3251495 A P _33292 _33293 t)). Qed.
Lemma lem3251497 {A : Type'} (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) : True = ((term558 A t P _33292 _33293) = (term583 A P _33292 _33293 t)).
Proof. exact (SYM (@lem3251496 A P _33292 _33293 t)). Qed.
Lemma lem3251498 {A : Type'} (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) : (term558 A t P _33292 _33293) = (term583 A P _33292 _33293 t).
Proof. exact (EQ_MP (@lem3251497 A P _33292 _33293 t) (@lem0)). Qed.
Lemma lem3251499 {A : Type'} (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term583 A P _33292 _33293 t.
Proof. exact (EQ_MP (@lem3251498 A P _33292 _33293 t) (@lem3251049 A _33292 _33293 t P a s h1)). Qed.
Lemma lem3251501 (b : Prop) (a : Prop) : (a \/ b) = (term266 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3251502 {A : Type'} (t : A -> Prop) (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) : (term583 A P _33292 _33293 t) = (term586 A t P _33292 _33293).
Proof. exact (@lem3251501 (term541 A _33292 _33293 t) (term343 A P _33292 _33293)). Qed.
Lemma lem3251504 (a : Prop) (b : Prop) : (term277 a b) = (term278 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3251505 {A : Type'} (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) : (term587 A _33292 _33293 t) = (term588 A _33292 _33293 t).
Proof. exact (@lem3251504 (term536 A _33292) (term384 A _33293 t)). Qed.
Lemma lem3251507 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3251508 {A : Type'} (_33292 : A -> Prop) : (term589 A _33292) = (_33292 = (@EMPTY A)).
Proof. exact (@lem3251507 (_33292 = (@EMPTY A))). Qed.
Lemma lem3251509 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3251510 {A : Type'} (_33292 : A -> Prop) : (term590 A _33292) = (term591 A _33292).
Proof. exact (MK_COMB (@lem3251509) (@lem3251508 A _33292)). Qed.
Lemma lem3251512 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3251513 {A : Type'} (_33293 : A -> Prop) (t : A -> Prop) : (term592 A _33293 t) = (@SUBSET A _33293 t).
Proof. exact (@lem3251512 (@SUBSET A _33293 t)). Qed.
Lemma lem3251514 {A : Type'} (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) : (term588 A _33292 _33293 t) = (term593 A _33292 _33293 t).
Proof. exact (MK_COMB (@lem3251510 A _33292) (@lem3251513 A _33293 t)). Qed.
Lemma lem3251515 {A : Type'} (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) : (term587 A _33292 _33293 t) = (term593 A _33292 _33293 t).
Proof. exact (TRANS (@lem3251505 A _33292 _33293 t) (@lem3251514 A _33292 _33293 t)). Qed.
Lemma lem3251516 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3251517 {A : Type'} (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) : (term594 A _33292 _33293 t) = (term595 A _33292 _33293 t).
Proof. exact (MK_COMB (@lem3251516) (@lem3251515 A _33292 _33293 t)). Qed.
Lemma lem3251518 {A : Type'} (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) : (term343 A P _33292 _33293) = (term343 A P _33292 _33293).
Proof. exact (eq_refl (term343 A P _33292 _33293)). Qed.
Lemma lem3251519 {A : Type'} (t : A -> Prop) (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) : (term586 A t P _33292 _33293) = (term596 A t P _33292 _33293).
Proof. exact (MK_COMB (@lem3251517 A _33292 _33293 t) (@lem3251518 A P _33292 _33293)). Qed.
Lemma lem3251520 {A : Type'} (t : A -> Prop) (P : type686 A) (_33292 : A -> Prop) (_33293 : A -> Prop) : (term583 A P _33292 _33293 t) = (term596 A t P _33292 _33293).
Proof. exact (TRANS (@lem3251502 A t P _33292 _33293) (@lem3251519 A t P _33292 _33293)). Qed.
Lemma lem3251522 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term597 A s t.
Proof. exact (conj (@lem3251414 A) (@lem3251421 A t P a s h1)). Qed.
Lemma lem3251524 {A : Type'} (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term596 A t P _33292 _33293.
Proof. exact (EQ_MP (@lem3251520 A t P _33292 _33293) (@lem3251499 A _33292 _33293 t P a s h1)). Qed.
Lemma lem3251525 {A : Type'} (_33292 : A -> Prop) (_33293 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term596 A t P _33292 _33293.
Proof. exact (@lem3251524 A _33292 _33293 t P a s h1). Qed.
Lemma lem3251526 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term598 A t P s.
Proof. exact (@lem3251525 A (@EMPTY A) s t P a s h1). Qed.
Lemma lem3251529 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term599 A P s.
Proof. exact (@lem3251526 A t P a s h1 (@lem3251522 A t P a s h1)). Qed.
Lemma lem3251530 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term600 A P s.
Proof. exact (fun h0 : term564 A P s => @lem3251529 A t P a s h1). Qed.
Lemma lem3251532 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3251533 {A : Type'} (P : type686 A) (s : A -> Prop) : (term600 A P s) = (term599 A P s).
Proof. exact (@lem3251532 (term599 A P s)). Qed.
Lemma lem3251534 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term599 A P s.
Proof. exact (EQ_MP (@lem3251533 A P s) (@lem3251530 A t P a s h1)). Qed.
Lemma lem3251540 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3251541 {A : Type'} (_33333 : A -> Prop) (P : type686 A) (_33332 : A -> Prop) : (term573 A _33333 P _33332) = (term601 A _33333 P _33332).
Proof. exact (@lem3251540 (P _33333) (term602 A _33332 _33333) (term547 A P _33332)). Qed.
Lemma lem3251555 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3251556 {A : Type'} (P : type686 A) (_33332 : A -> Prop) (_33333 : A -> Prop) : (term603 A _33333 P _33332) = (term604 A P _33332 _33333).
Proof. exact (@lem3251555 (term547 A P _33332) (term602 A _33332 _33333)). Qed.
Lemma lem3251564 {A : Type'} (P : type686 A) (_33333 : A -> Prop) : (term605 A P _33333) = (term605 A P _33333).
Proof. exact (eq_refl (term605 A P _33333)). Qed.
Lemma lem3251565 {A : Type'} (P : type686 A) (_33332 : A -> Prop) (_33333 : A -> Prop) : (term601 A _33333 P _33332) = (term606 A P _33332 _33333).
Proof. exact (MK_COMB (@lem3251564 A P _33333) (@lem3251556 A P _33332 _33333)). Qed.
Lemma lem3251576 {A : Type'} (P : type686 A) (_33332 : A -> Prop) (_33333 : A -> Prop) : (term573 A _33333 P _33332) = (term606 A P _33332 _33333).
Proof. exact (TRANS (@lem3251541 A _33333 P _33332) (@lem3251565 A P _33332 _33333)). Qed.
Lemma lem3251577 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3251578 {A : Type'} (P : type686 A) (_33332 : A -> Prop) (_33333 : A -> Prop) : (term607 A _33333 P _33332) = (term608 A P _33332 _33333).
Proof. exact (MK_COMB (@lem3251577) (@lem3251576 A P _33332 _33333)). Qed.
Lemma lem3251592 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3251593 {A : Type'} (P : type686 A) (_33332 : A -> Prop) (_33333 : A -> Prop) : (term603 A _33333 P _33332) = (term604 A P _33332 _33333).
Proof. exact (@lem3251592 (term547 A P _33332) (term602 A _33332 _33333)). Qed.
Lemma lem3251601 {A : Type'} (P : type686 A) (_33333 : A -> Prop) : (term605 A P _33333) = (term605 A P _33333).
Proof. exact (eq_refl (term605 A P _33333)). Qed.
Lemma lem3251602 {A : Type'} (P : type686 A) (_33332 : A -> Prop) (_33333 : A -> Prop) : (term601 A _33333 P _33332) = (term606 A P _33332 _33333).
Proof. exact (MK_COMB (@lem3251601 A P _33333) (@lem3251593 A P _33332 _33333)). Qed.
Lemma lem3251613 {A : Type'} (P : type686 A) (_33332 : A -> Prop) (_33333 : A -> Prop) : ((term573 A _33333 P _33332) = (term601 A _33333 P _33332)) = ((term606 A P _33332 _33333) = (term606 A P _33332 _33333)).
Proof. exact (MK_COMB (@lem3251578 A P _33332 _33333) (@lem3251602 A P _33332 _33333)). Qed.
Lemma lem3251615 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3251616 (x : Prop) : (x = x) = True.
Proof. exact (@lem3251615 Prop x). Qed.
Lemma lem3251617 {A : Type'} (P : type686 A) (_33332 : A -> Prop) (_33333 : A -> Prop) : ((term606 A P _33332 _33333) = (term606 A P _33332 _33333)) = True.
Proof. exact (@lem3251616 (term606 A P _33332 _33333)). Qed.
Lemma lem3251618 {A : Type'} (_33333 : A -> Prop) (P : type686 A) (_33332 : A -> Prop) : ((term573 A _33333 P _33332) = (term601 A _33333 P _33332)) = True.
Proof. exact (TRANS (@lem3251613 A P _33332 _33333) (@lem3251617 A P _33332 _33333)). Qed.
Lemma lem3251619 {A : Type'} (_33333 : A -> Prop) (P : type686 A) (_33332 : A -> Prop) : True = ((term573 A _33333 P _33332) = (term601 A _33333 P _33332)).
Proof. exact (SYM (@lem3251618 A _33333 P _33332)). Qed.
Lemma lem3251620 {A : Type'} (_33333 : A -> Prop) (P : type686 A) (_33332 : A -> Prop) : (term573 A _33333 P _33332) = (term601 A _33333 P _33332).
Proof. exact (EQ_MP (@lem3251619 A _33333 P _33332) (@lem0)). Qed.
Lemma lem3251621 {A : Type'} (_33333 : A -> Prop) (P : type686 A) (_33332 : A -> Prop) : term601 A _33333 P _33332.
Proof. exact (EQ_MP (@lem3251620 A _33333 P _33332) (@lem3251343 A _33333 P _33332)). Qed.
Lemma lem3251623 (b : Prop) (a : Prop) : (a \/ b) = (term266 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3251624 {A : Type'} (_33332 : A -> Prop) (P : type686 A) (_33333 : A -> Prop) : (term601 A _33333 P _33332) = (term609 A _33332 P _33333).
Proof. exact (@lem3251623 (term603 A _33333 P _33332) (P _33333)). Qed.
Lemma lem3251626 (a : Prop) (b : Prop) : (term277 a b) = (term278 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3251627 {A : Type'} (_33333 : A -> Prop) (P : type686 A) (_33332 : A -> Prop) : (term610 A _33333 P _33332) = (term611 A _33333 P _33332).
Proof. exact (@lem3251626 (term602 A _33332 _33333) (term547 A P _33332)). Qed.
Lemma lem3251629 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3251630 {A : Type'} (_33332 : A -> Prop) (_33333 : A -> Prop) : (term612 A _33332 _33333) = (_33332 = _33333).
Proof. exact (@lem3251629 (_33332 = _33333)). Qed.
Lemma lem3251631 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3251632 {A : Type'} (_33332 : A -> Prop) (_33333 : A -> Prop) : (term613 A _33332 _33333) = (term614 A _33332 _33333).
Proof. exact (MK_COMB (@lem3251631) (@lem3251630 A _33332 _33333)). Qed.
Lemma lem3251634 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3251635 {A : Type'} (P : type686 A) (_33332 : A -> Prop) : (term615 A P _33332) = (P _33332).
Proof. exact (@lem3251634 (P _33332)). Qed.
Lemma lem3251636 {A : Type'} (_33333 : A -> Prop) (P : type686 A) (_33332 : A -> Prop) : (term611 A _33333 P _33332) = (term616 A _33333 P _33332).
Proof. exact (MK_COMB (@lem3251632 A _33332 _33333) (@lem3251635 A P _33332)). Qed.
Lemma lem3251637 {A : Type'} (_33333 : A -> Prop) (P : type686 A) (_33332 : A -> Prop) : (term610 A _33333 P _33332) = (term616 A _33333 P _33332).
Proof. exact (TRANS (@lem3251627 A _33333 P _33332) (@lem3251636 A _33333 P _33332)). Qed.
Lemma lem3251638 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3251639 {A : Type'} (_33333 : A -> Prop) (P : type686 A) (_33332 : A -> Prop) : (term617 A _33333 P _33332) = (term618 A _33333 P _33332).
Proof. exact (MK_COMB (@lem3251638) (@lem3251637 A _33333 P _33332)). Qed.
Lemma lem3251640 {A : Type'} (P : type686 A) (_33333 : A -> Prop) : (P _33333) = (P _33333).
Proof. exact (eq_refl (P _33333)). Qed.
Lemma lem3251641 {A : Type'} (_33332 : A -> Prop) (P : type686 A) (_33333 : A -> Prop) : (term609 A _33332 P _33333) = (term619 A _33332 P _33333).
Proof. exact (MK_COMB (@lem3251639 A _33333 P _33332) (@lem3251640 A P _33333)). Qed.
Lemma lem3251642 {A : Type'} (_33332 : A -> Prop) (P : type686 A) (_33333 : A -> Prop) : (term601 A _33333 P _33332) = (term619 A _33332 P _33333).
Proof. exact (TRANS (@lem3251624 A _33332 P _33333) (@lem3251641 A _33332 P _33333)). Qed.
Lemma lem3251644 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) (h2 : term356 A) : term620 A P s.
Proof. exact (conj (@lem3251405 A s h2) (@lem3251534 A t P a s h1)). Qed.
Lemma lem3251646 {A : Type'} (_33332 : A -> Prop) (P : type686 A) (_33333 : A -> Prop) : term619 A _33332 P _33333.
Proof. exact (EQ_MP (@lem3251642 A _33332 P _33333) (@lem3251621 A _33333 P _33332)). Qed.
Lemma lem3251647 {A : Type'} (_33332 : A -> Prop) (P : type686 A) (_33333 : A -> Prop) : term619 A _33332 P _33333.
Proof. exact (@lem3251646 A _33332 P _33333). Qed.
Lemma lem3251648 {A : Type'} (P : type686 A) (s : A -> Prop) : term621 A P s.
Proof. exact (@lem3251647 A (@UNION A (@EMPTY A) s) P s). Qed.
Lemma lem3251651 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) (h2 : term356 A) : P s.
Proof. exact (@lem3251648 A P s (@lem3251644 A t P a s h1 h2)). Qed.
Lemma lem3251652 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) (h2 : term356 A) : term622 A P s.
Proof. exact (fun h0 : term547 A P s => @lem3251651 A t P a s h1 h2). Qed.
Lemma lem3251654 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3251655 {A : Type'} (P : type686 A) (s : A -> Prop) : (term622 A P s) = (P s).
Proof. exact (@lem3251654 (P s)). Qed.
Lemma lem3251656 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) (h2 : term356 A) : P s.
Proof. exact (EQ_MP (@lem3251655 A P s) (@lem3251652 A t P a s h1 h2)). Qed.
Lemma lem3251659 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3251661 {A : Type'} (P : type686 A) (s : A -> Prop) : (term547 A P s) = (term623 A P s).
Proof. exact (@lem3251659 (P s)). Qed.
Lemma lem3251664 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term547 A P s) : term623 A P s.
Proof. exact (EQ_MP (@lem3251661 A P s) (@lem3251037 A P s h1)). Qed.
Lemma lem3251667 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term547 A P s) (h2 : term454 A t P a s) (h3 : term356 A) : False.
Proof. exact (@lem3251664 A P s h1 (@lem3251656 A t P a s h2 h3)). Qed.
Lemma lem3251668 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term547 A P s) (h2 : term454 A t P a s) (h3 : term356 A) : term256.
Proof. exact (fun h0 : ~ False => @lem3251667 A t P a s h1 h2 h3). Qed.
Lemma lem3251670 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3251671 : term256 = False.
Proof. exact (@lem3251670 False). Qed.
Lemma lem3251672 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term547 A P s) (h2 : term454 A t P a s) (h3 : term356 A) : False.
Proof. exact (EQ_MP (@lem3251671) (@lem3251668 A t P a s h1 h2 h3)). Qed.
Lemma lem3251739 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem3251740 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem3251739 A x). Qed.
Lemma lem3251741 {A : Type'} (a : A) : (@INSERT A a (@EMPTY A)) = (@INSERT A a (@EMPTY A)).
Proof. exact (@lem3251740 A (@INSERT A a (@EMPTY A))). Qed.
Lemma lem3251742 {A : Type'} (a : A) : term624 A a.
Proof. exact (fun h0 : term625 A a => @lem3251741 A a). Qed.
Lemma lem3251744 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3251745 {A : Type'} (a : A) : (term624 A a) = ((@INSERT A a (@EMPTY A)) = (@INSERT A a (@EMPTY A))).
Proof. exact (@lem3251744 ((@INSERT A a (@EMPTY A)) = (@INSERT A a (@EMPTY A)))). Qed.
Lemma lem3251746 {A : Type'} (a : A) : (@INSERT A a (@EMPTY A)) = (@INSERT A a (@EMPTY A)).
Proof. exact (EQ_MP (@lem3251745 A a) (@lem3251742 A a)). Qed.
Lemma lem3251748 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : @SUBSET A s t.
Proof. exact (proj1 (@lem3250748 A t P a s h1)). Qed.
Lemma lem3251749 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term578 A s t.
Proof. exact (fun h0 : term384 A s t => @lem3251748 A t P a s h1). Qed.
Lemma lem3251751 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3251752 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term578 A s t) = (@SUBSET A s t).
Proof. exact (@lem3251751 (@SUBSET A s t)). Qed.
Lemma lem3251753 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : @SUBSET A s t.
Proof. exact (EQ_MP (@lem3251752 A s t) (@lem3251749 A t P a s h1)). Qed.
Lemma lem3251771 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3251772 {A : Type'} (P : type686 A) (_33296 : A -> Prop) (_33297 : A -> Prop) (t : A -> Prop) : (term579 A t P _33296 _33297) = (term580 A P _33296 _33297 t).
Proof. exact (@lem3251771 (term343 A P _33296 _33297) (term384 A _33297 t)). Qed.
Lemma lem3251778 {A : Type'} (_33296 : A -> Prop) (a : A) : (term626 A _33296 a) = (term626 A _33296 a).
Proof. exact (eq_refl (term626 A _33296 a)). Qed.
Lemma lem3251779 {A : Type'} (a : A) (P : type686 A) (_33296 : A -> Prop) (_33297 : A -> Prop) (t : A -> Prop) : (term559 A a t P _33296 _33297) = (term627 A a P _33296 _33297 t).
Proof. exact (MK_COMB (@lem3251778 A _33296 a) (@lem3251772 A P _33296 _33297 t)). Qed.
Lemma lem3251783 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3251784 {A : Type'} (P : type686 A) (_33296 : A -> Prop) (a : A) (_33297 : A -> Prop) (t : A -> Prop) : (term627 A a P _33296 _33297 t) = (term628 A P _33296 a _33297 t).
Proof. exact (@lem3251783 (term343 A P _33296 _33297) (term537 A _33296 a) (term384 A _33297 t)). Qed.
Lemma lem3251802 {A : Type'} (P : type686 A) (_33296 : A -> Prop) (a : A) (_33297 : A -> Prop) (t : A -> Prop) : (term559 A a t P _33296 _33297) = (term628 A P _33296 a _33297 t).
Proof. exact (TRANS (@lem3251779 A a P _33296 _33297 t) (@lem3251784 A P _33296 a _33297 t)). Qed.
Lemma lem3251803 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3251804 {A : Type'} (P : type686 A) (_33296 : A -> Prop) (a : A) (_33297 : A -> Prop) (t : A -> Prop) : (term629 A a t P _33296 _33297) = (term630 A P _33296 a _33297 t).
Proof. exact (MK_COMB (@lem3251803) (@lem3251802 A P _33296 a _33297 t)). Qed.
Lemma lem3251822 {A : Type'} (P : type686 A) (_33296 : A -> Prop) (a : A) (_33297 : A -> Prop) (t : A -> Prop) : (term628 A P _33296 a _33297 t) = (term628 A P _33296 a _33297 t).
Proof. exact (eq_refl (term628 A P _33296 a _33297 t)). Qed.
Lemma lem3251823 {A : Type'} (P : type686 A) (_33296 : A -> Prop) (a : A) (_33297 : A -> Prop) (t : A -> Prop) : ((term559 A a t P _33296 _33297) = (term628 A P _33296 a _33297 t)) = ((term628 A P _33296 a _33297 t) = (term628 A P _33296 a _33297 t)).
Proof. exact (MK_COMB (@lem3251804 A P _33296 a _33297 t) (@lem3251822 A P _33296 a _33297 t)). Qed.
Lemma lem3251825 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3251826 (x : Prop) : (x = x) = True.
Proof. exact (@lem3251825 Prop x). Qed.
Lemma lem3251827 {A : Type'} (P : type686 A) (_33296 : A -> Prop) (a : A) (_33297 : A -> Prop) (t : A -> Prop) : ((term628 A P _33296 a _33297 t) = (term628 A P _33296 a _33297 t)) = True.
Proof. exact (@lem3251826 (term628 A P _33296 a _33297 t)). Qed.
Lemma lem3251828 {A : Type'} (P : type686 A) (_33296 : A -> Prop) (a : A) (_33297 : A -> Prop) (t : A -> Prop) : ((term559 A a t P _33296 _33297) = (term628 A P _33296 a _33297 t)) = True.
Proof. exact (TRANS (@lem3251823 A P _33296 a _33297 t) (@lem3251827 A P _33296 a _33297 t)). Qed.
Lemma lem3251829 {A : Type'} (P : type686 A) (_33296 : A -> Prop) (a : A) (_33297 : A -> Prop) (t : A -> Prop) : True = ((term559 A a t P _33296 _33297) = (term628 A P _33296 a _33297 t)).
Proof. exact (SYM (@lem3251828 A P _33296 a _33297 t)). Qed.
Lemma lem3251830 {A : Type'} (P : type686 A) (_33296 : A -> Prop) (a : A) (_33297 : A -> Prop) (t : A -> Prop) : (term559 A a t P _33296 _33297) = (term628 A P _33296 a _33297 t).
Proof. exact (EQ_MP (@lem3251829 A P _33296 a _33297 t) (@lem0)). Qed.
Lemma lem3251831 {A : Type'} (_33296 : A -> Prop) (_33297 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term628 A P _33296 a _33297 t.
Proof. exact (EQ_MP (@lem3251830 A P _33296 a _33297 t) (@lem3251093 A _33296 _33297 t P a s h1)). Qed.
Lemma lem3251833 (b : Prop) (a : Prop) : (a \/ b) = (term266 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3251834 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (_33296 : A -> Prop) (_33297 : A -> Prop) : (term628 A P _33296 a _33297 t) = (term631 A a t P _33296 _33297).
Proof. exact (@lem3251833 (term542 A _33296 a _33297 t) (term343 A P _33296 _33297)). Qed.
Lemma lem3251836 (a : Prop) (b : Prop) : (term277 a b) = (term278 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3251837 {A : Type'} (_33296 : A -> Prop) (a : A) (_33297 : A -> Prop) (t : A -> Prop) : (term632 A _33296 a _33297 t) = (term633 A _33296 a _33297 t).
Proof. exact (@lem3251836 (term537 A _33296 a) (term384 A _33297 t)). Qed.
Lemma lem3251839 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3251840 {A : Type'} (_33296 : A -> Prop) (a : A) : (term634 A _33296 a) = (_33296 = (@INSERT A a (@EMPTY A))).
Proof. exact (@lem3251839 (_33296 = (@INSERT A a (@EMPTY A)))). Qed.
Lemma lem3251841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3251842 {A : Type'} (_33296 : A -> Prop) (a : A) : (term635 A _33296 a) = (term636 A _33296 a).
Proof. exact (MK_COMB (@lem3251841) (@lem3251840 A _33296 a)). Qed.
Lemma lem3251844 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3251845 {A : Type'} (_33297 : A -> Prop) (t : A -> Prop) : (term592 A _33297 t) = (@SUBSET A _33297 t).
Proof. exact (@lem3251844 (@SUBSET A _33297 t)). Qed.
Lemma lem3251846 {A : Type'} (_33296 : A -> Prop) (a : A) (_33297 : A -> Prop) (t : A -> Prop) : (term633 A _33296 a _33297 t) = (term637 A _33296 a _33297 t).
Proof. exact (MK_COMB (@lem3251842 A _33296 a) (@lem3251845 A _33297 t)). Qed.
Lemma lem3251847 {A : Type'} (_33296 : A -> Prop) (a : A) (_33297 : A -> Prop) (t : A -> Prop) : (term632 A _33296 a _33297 t) = (term637 A _33296 a _33297 t).
Proof. exact (TRANS (@lem3251837 A _33296 a _33297 t) (@lem3251846 A _33296 a _33297 t)). Qed.
Lemma lem3251848 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3251849 {A : Type'} (_33296 : A -> Prop) (a : A) (_33297 : A -> Prop) (t : A -> Prop) : (term638 A _33296 a _33297 t) = (term639 A _33296 a _33297 t).
Proof. exact (MK_COMB (@lem3251848) (@lem3251847 A _33296 a _33297 t)). Qed.
Lemma lem3251850 {A : Type'} (P : type686 A) (_33296 : A -> Prop) (_33297 : A -> Prop) : (term343 A P _33296 _33297) = (term343 A P _33296 _33297).
Proof. exact (eq_refl (term343 A P _33296 _33297)). Qed.
Lemma lem3251851 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (_33296 : A -> Prop) (_33297 : A -> Prop) : (term631 A a t P _33296 _33297) = (term640 A a t P _33296 _33297).
Proof. exact (MK_COMB (@lem3251849 A _33296 a _33297 t) (@lem3251850 A P _33296 _33297)). Qed.
Lemma lem3251852 {A : Type'} (a : A) (t : A -> Prop) (P : type686 A) (_33296 : A -> Prop) (_33297 : A -> Prop) : (term628 A P _33296 a _33297 t) = (term640 A a t P _33296 _33297).
Proof. exact (TRANS (@lem3251834 A a t P _33296 _33297) (@lem3251851 A a t P _33296 _33297)). Qed.
Lemma lem3251854 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term641 A a s t.
Proof. exact (conj (@lem3251746 A a) (@lem3251753 A t P a s h1)). Qed.
Lemma lem3251856 {A : Type'} (_33296 : A -> Prop) (_33297 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term640 A a t P _33296 _33297.
Proof. exact (EQ_MP (@lem3251852 A a t P _33296 _33297) (@lem3251831 A _33296 _33297 t P a s h1)). Qed.
Lemma lem3251857 {A : Type'} (_33296 : A -> Prop) (_33297 : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term640 A a t P _33296 _33297.
Proof. exact (@lem3251856 A _33296 _33297 t P a s h1). Qed.
Lemma lem3251858 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term642 A t P a s.
Proof. exact (@lem3251857 A (@INSERT A a (@EMPTY A)) s t P a s h1). Qed.
Lemma lem3251861 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term325 A P a s.
Proof. exact (@lem3251858 A t P a s h1 (@lem3251854 A t P a s h1)). Qed.
Lemma lem3251862 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term643 A P a s.
Proof. exact (fun h0 : term548 A P a s => @lem3251861 A t P a s h1). Qed.
Lemma lem3251864 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3251865 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term643 A P a s) = (term325 A P a s).
Proof. exact (@lem3251864 (term325 A P a s)). Qed.
Lemma lem3251866 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) : term325 A P a s.
Proof. exact (EQ_MP (@lem3251865 A P a s) (@lem3251862 A t P a s h1)). Qed.
Lemma lem3251869 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3251871 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term548 A P a s) = (term644 A P a s).
Proof. exact (@lem3251869 (term325 A P a s)). Qed.
Lemma lem3251874 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) (h1 : term548 A P a s) : term644 A P a s.
Proof. exact (EQ_MP (@lem3251871 A P a s) (@lem3251069 A P a s h1)). Qed.
Lemma lem3251877 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term548 A P a s) (h2 : term454 A t P a s) : False.
Proof. exact (@lem3251874 A P a s h1 (@lem3251866 A t P a s h2)). Qed.
Lemma lem3251878 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term548 A P a s) (h2 : term454 A t P a s) : term256.
Proof. exact (fun h0 : ~ False => @lem3251877 A t P a s h1 h2). Qed.
Lemma lem3251880 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3251881 : term256 = False.
Proof. exact (@lem3251880 False). Qed.
Lemma lem3251882 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term548 A P a s) (h2 : term454 A t P a s) : False.
Proof. exact (EQ_MP (@lem3251881) (@lem3251878 A t P a s h1 h2)). Qed.
Lemma lem3251902 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3251903 {A : Type'} (_33364 : A -> Prop) (_33365 : A -> Prop) (h1 : _33364 = _33365) : _33364 = _33365.
Proof. exact (h1). Qed.
Lemma lem3251904 {A : Type'} (P : type686 A) (_33364 : A -> Prop) (_33365 : A -> Prop) (h1 : _33364 = _33365) : (P _33364) = (P _33365).
Proof. exact (MK_COMB (@lem3251902 A P) (@lem3251903 A _33364 _33365 h1)). Qed.
Lemma lem3251906 (b : Prop) (a : Prop) : term257 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3251907 {A : Type'} (_33365 : A -> Prop) (P : type686 A) (_33364 : A -> Prop) : term570 A _33365 P _33364.
Proof. exact (@lem3251906 (P _33365) (P _33364)). Qed.
Lemma lem3251908 {A : Type'} (P : type686 A) (_33364 : A -> Prop) (_33365 : A -> Prop) (h1 : _33364 = _33365) : term571 A _33365 P _33364.
Proof. exact (@lem3251907 A _33365 P _33364 (@lem3251904 A P _33364 _33365 h1)). Qed.
Lemma lem3251909 {A : Type'} (_33365 : A -> Prop) (P : type686 A) (_33364 : A -> Prop) : term572 A _33365 P _33364.
Proof. exact (fun h0 : _33364 = _33365 => @lem3251908 A P _33364 _33365 h0). Qed.
Lemma lem3251911 (a : Prop) (b : Prop) : (a -> b) = (term261 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3251912 {A : Type'} (_33365 : A -> Prop) (P : type686 A) (_33364 : A -> Prop) : (term572 A _33365 P _33364) = (term573 A _33365 P _33364).
Proof. exact (@lem3251911 (_33364 = _33365) (term571 A _33365 P _33364)). Qed.
Lemma lem3251913 {A : Type'} (_33365 : A -> Prop) (P : type686 A) (_33364 : A -> Prop) : term573 A _33365 P _33364.
Proof. exact (EQ_MP (@lem3251912 A _33365 P _33364) (@lem3251909 A _33365 P _33364)). Qed.
Lemma lem3251945 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term645 A x y z.
Proof. exact (@lem21385 (A -> Prop) x y z). Qed.
Lemma lem3251949 {A : Type'} (_33298 : A -> Prop) (h1 : term356 A) : (@UNION A (@EMPTY A) _33298) = _33298.
Proof. exact (EQ_MP (@lem3251005 A _33298) (@lem3251004 A _33298 h1)). Qed.
Lemma lem3251950 {A : Type'} (_33298 : A -> Prop) (h1 : term356 A) : (@UNION A (@EMPTY A) _33298) = _33298.
Proof. exact (@lem3251949 A _33298 h1). Qed.
Lemma lem3251951 {A : Type'} (u' : A -> Prop) (h1 : term356 A) : (@UNION A (@EMPTY A) u') = u'.
Proof. exact (@lem3251950 A u' h1). Qed.
Lemma lem3251952 {A : Type'} (u' : A -> Prop) (h1 : term356 A) : term574 A u'.
Proof. exact (fun h0 : term575 A u' => @lem3251951 A u' h1). Qed.
Lemma lem3251954 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3251955 {A : Type'} (u' : A -> Prop) : (term574 A u') = ((@UNION A (@EMPTY A) u') = u').
Proof. exact (@lem3251954 ((@UNION A (@EMPTY A) u') = u')). Qed.
Lemma lem3251956 {A : Type'} (u' : A -> Prop) (h1 : term356 A) : (@UNION A (@EMPTY A) u') = u'.
Proof. exact (EQ_MP (@lem3251955 A u') (@lem3251952 A u' h1)). Qed.
Lemma lem3251958 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem3251959 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem3251958 A x). Qed.
Lemma lem3251960 {A : Type'} (u' : A -> Prop) : (@UNION A (@EMPTY A) u') = (@UNION A (@EMPTY A) u').
Proof. exact (@lem3251959 A (@UNION A (@EMPTY A) u')). Qed.
Lemma lem3251961 {A : Type'} (u' : A -> Prop) : term646 A u'.
Proof. exact (fun h0 : term647 A u' => @lem3251960 A u'). Qed.
Lemma lem3251963 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3251964 {A : Type'} (u' : A -> Prop) : (term646 A u') = ((@UNION A (@EMPTY A) u') = (@UNION A (@EMPTY A) u')).
Proof. exact (@lem3251963 ((@UNION A (@EMPTY A) u') = (@UNION A (@EMPTY A) u'))). Qed.
Lemma lem3251965 {A : Type'} (u' : A -> Prop) : (@UNION A (@EMPTY A) u') = (@UNION A (@EMPTY A) u').
Proof. exact (EQ_MP (@lem3251964 A u') (@lem3251961 A u')). Qed.
Lemma lem3251983 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3251984 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term648 A x y z) = (term649 A y x z).
Proof. exact (@lem3251983 (y = z) (term602 A x z)). Qed.
Lemma lem3251994 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term650 A x y) = (term650 A x y).
Proof. exact (eq_refl (term650 A x y)). Qed.
Lemma lem3251995 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term645 A x y z) = (term651 A y x z).
Proof. exact (MK_COMB (@lem3251994 A x y) (@lem3251984 A y x z)). Qed.
Lemma lem3251999 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3252000 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term651 A y x z) = (term652 A y x z).
Proof. exact (@lem3251999 (y = z) (term602 A x y) (term602 A x z)). Qed.
Lemma lem3252022 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term645 A x y z) = (term652 A y x z).
Proof. exact (TRANS (@lem3251995 A y x z) (@lem3252000 A y x z)). Qed.
Lemma lem3252023 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3252024 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term653 A x y z) = (term654 A y x z).
Proof. exact (MK_COMB (@lem3252023) (@lem3252022 A y x z)). Qed.
Lemma lem3252046 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term652 A y x z) = (term652 A y x z).
Proof. exact (eq_refl (term652 A y x z)). Qed.
Lemma lem3252047 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : ((term645 A x y z) = (term652 A y x z)) = ((term652 A y x z) = (term652 A y x z)).
Proof. exact (MK_COMB (@lem3252024 A y x z) (@lem3252046 A y x z)). Qed.
Lemma lem3252049 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3252050 (x : Prop) : (x = x) = True.
Proof. exact (@lem3252049 Prop x). Qed.
Lemma lem3252051 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : ((term652 A y x z) = (term652 A y x z)) = True.
Proof. exact (@lem3252050 (term652 A y x z)). Qed.
Lemma lem3252052 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : ((term645 A x y z) = (term652 A y x z)) = True.
Proof. exact (TRANS (@lem3252047 A y x z) (@lem3252051 A y x z)). Qed.
Lemma lem3252053 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : True = ((term645 A x y z) = (term652 A y x z)).
Proof. exact (SYM (@lem3252052 A y x z)). Qed.
Lemma lem3252054 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term645 A x y z) = (term652 A y x z).
Proof. exact (EQ_MP (@lem3252053 A y x z) (@lem0)). Qed.
Lemma lem3252055 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : term652 A y x z.
Proof. exact (EQ_MP (@lem3252054 A y x z) (@lem3251945 A x y z)). Qed.
Lemma lem3252057 (b : Prop) (a : Prop) : (a \/ b) = (term266 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3252058 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term652 A y x z) = (term655 A x y z).
Proof. exact (@lem3252057 (term656 A y x z) (y = z)). Qed.
Lemma lem3252060 (a : Prop) (b : Prop) : (term277 a b) = (term278 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3252061 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term657 A y x z) = (term658 A y x z).
Proof. exact (@lem3252060 (term602 A x y) (term602 A x z)). Qed.
Lemma lem3252063 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3252064 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term612 A x y) = (x = y).
Proof. exact (@lem3252063 (x = y)). Qed.
Lemma lem3252065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3252066 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term613 A x y) = (term614 A x y).
Proof. exact (MK_COMB (@lem3252065) (@lem3252064 A x y)). Qed.
Lemma lem3252068 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3252069 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term612 A x z) = (x = z).
Proof. exact (@lem3252068 (x = z)). Qed.
Lemma lem3252070 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term658 A y x z) = (term659 A y x z).
Proof. exact (MK_COMB (@lem3252066 A x y) (@lem3252069 A x z)). Qed.
Lemma lem3252071 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term657 A y x z) = (term659 A y x z).
Proof. exact (TRANS (@lem3252061 A y x z) (@lem3252070 A y x z)). Qed.
Lemma lem3252072 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3252073 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term660 A y x z) = (term661 A y x z).
Proof. exact (MK_COMB (@lem3252072) (@lem3252071 A y x z)). Qed.
Lemma lem3252074 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3252075 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term655 A x y z) = (term662 A x y z).
Proof. exact (MK_COMB (@lem3252073 A y x z) (@lem3252074 A y z)). Qed.
Lemma lem3252076 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term652 A y x z) = (term662 A x y z).
Proof. exact (TRANS (@lem3252058 A x y z) (@lem3252075 A x y z)). Qed.
Lemma lem3252078 {A : Type'} (u' : A -> Prop) (h1 : term356 A) : term663 A u'.
Proof. exact (conj (@lem3251956 A u' h1) (@lem3251965 A u')). Qed.
Lemma lem3252080 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term662 A x y z.
Proof. exact (EQ_MP (@lem3252076 A x y z) (@lem3252055 A y x z)). Qed.
Lemma lem3252081 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term662 A x y z.
Proof. exact (@lem3252080 A x y z). Qed.
Lemma lem3252082 {A : Type'} (u' : A -> Prop) : term664 A u'.
Proof. exact (@lem3252081 A (@UNION A (@EMPTY A) u') u' (@UNION A (@EMPTY A) u')). Qed.
Lemma lem3252085 {A : Type'} (u' : A -> Prop) (h1 : term356 A) : u' = (@UNION A (@EMPTY A) u').
Proof. exact (@lem3252082 A u' (@lem3252078 A u' h1)). Qed.
Lemma lem3252086 {A : Type'} (u' : A -> Prop) (h1 : term356 A) : u' = (@UNION A (@EMPTY A) u').
Proof. exact (@lem3252085 A u' h1). Qed.
Lemma lem3252087 {A : Type'} (u' : A -> Prop) (h1 : term356 A) : term665 A u'.
Proof. exact (fun h0 : term666 A u' => @lem3252086 A u' h1). Qed.
Lemma lem3252089 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3252090 {A : Type'} (u' : A -> Prop) : (term665 A u') = (u' = (@UNION A (@EMPTY A) u')).
Proof. exact (@lem3252089 (u' = (@UNION A (@EMPTY A) u'))). Qed.
Lemma lem3252091 {A : Type'} (u' : A -> Prop) (h1 : term356 A) : u' = (@UNION A (@EMPTY A) u').
Proof. exact (EQ_MP (@lem3252090 A u') (@lem3252087 A u' h1)). Qed.
Lemma lem3252093 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : @SUBSET A u' t.
Proof. exact (proj2 (@lem3250757 A s u' t P a h1)). Qed.
Lemma lem3252094 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term578 A u' t.
Proof. exact (fun h0 : term384 A u' t => @lem3252093 A s u' t P a h1). Qed.
Lemma lem3252096 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3252097 {A : Type'} (u' : A -> Prop) (t : A -> Prop) : (term578 A u' t) = (@SUBSET A u' t).
Proof. exact (@lem3252096 (@SUBSET A u' t)). Qed.
Lemma lem3252098 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : @SUBSET A u' t.
Proof. exact (EQ_MP (@lem3252097 A u' t) (@lem3252094 A s u' t P a h1)). Qed.
Lemma lem3252104 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3252105 {A : Type'} (P : type686 A) (_33300 : A -> Prop) (t : A -> Prop) : (term567 A t P _33300) = (term667 A P _33300 t).
Proof. exact (@lem3252104 (P _33300) (term384 A _33300 t)). Qed.
Lemma lem3252111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3252112 {A : Type'} (P : type686 A) (_33300 : A -> Prop) (t : A -> Prop) : (term668 A t P _33300) = (term669 A P _33300 t).
Proof. exact (MK_COMB (@lem3252111) (@lem3252105 A P _33300 t)). Qed.
Lemma lem3252118 {A : Type'} (P : type686 A) (_33300 : A -> Prop) (t : A -> Prop) : (term667 A P _33300 t) = (term667 A P _33300 t).
Proof. exact (eq_refl (term667 A P _33300 t)). Qed.
Lemma lem3252119 {A : Type'} (P : type686 A) (_33300 : A -> Prop) (t : A -> Prop) : ((term567 A t P _33300) = (term667 A P _33300 t)) = ((term667 A P _33300 t) = (term667 A P _33300 t)).
Proof. exact (MK_COMB (@lem3252112 A P _33300 t) (@lem3252118 A P _33300 t)). Qed.
Lemma lem3252121 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3252122 (x : Prop) : (x = x) = True.
Proof. exact (@lem3252121 Prop x). Qed.
Lemma lem3252123 {A : Type'} (P : type686 A) (_33300 : A -> Prop) (t : A -> Prop) : ((term667 A P _33300 t) = (term667 A P _33300 t)) = True.
Proof. exact (@lem3252122 (term667 A P _33300 t)). Qed.
Lemma lem3252124 {A : Type'} (P : type686 A) (_33300 : A -> Prop) (t : A -> Prop) : ((term567 A t P _33300) = (term667 A P _33300 t)) = True.
Proof. exact (TRANS (@lem3252119 A P _33300 t) (@lem3252123 A P _33300 t)). Qed.
Lemma lem3252125 {A : Type'} (P : type686 A) (_33300 : A -> Prop) (t : A -> Prop) : True = ((term567 A t P _33300) = (term667 A P _33300 t)).
Proof. exact (SYM (@lem3252124 A P _33300 t)). Qed.
Lemma lem3252126 {A : Type'} (P : type686 A) (_33300 : A -> Prop) (t : A -> Prop) : (term567 A t P _33300) = (term667 A P _33300 t).
Proof. exact (EQ_MP (@lem3252125 A P _33300 t) (@lem0)). Qed.
Lemma lem3252127 {A : Type'} (_33300 : A -> Prop) (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term667 A P _33300 t.
Proof. exact (EQ_MP (@lem3252126 A P _33300 t) (@lem3251220 A _33300 s u' t P a h1)). Qed.
Lemma lem3252129 (b : Prop) (a : Prop) : (a \/ b) = (term266 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3252130 {A : Type'} (t : A -> Prop) (P : type686 A) (_33300 : A -> Prop) : (term667 A P _33300 t) = (term670 A t P _33300).
Proof. exact (@lem3252129 (term384 A _33300 t) (P _33300)). Qed.
Lemma lem3252132 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3252133 {A : Type'} (_33300 : A -> Prop) (t : A -> Prop) : (term592 A _33300 t) = (@SUBSET A _33300 t).
Proof. exact (@lem3252132 (@SUBSET A _33300 t)). Qed.
Lemma lem3252134 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3252135 {A : Type'} (_33300 : A -> Prop) (t : A -> Prop) : (term671 A _33300 t) = (term329 A _33300 t).
Proof. exact (MK_COMB (@lem3252134) (@lem3252133 A _33300 t)). Qed.
Lemma lem3252136 {A : Type'} (P : type686 A) (_33300 : A -> Prop) : (P _33300) = (P _33300).
Proof. exact (eq_refl (P _33300)). Qed.
Lemma lem3252137 {A : Type'} (t : A -> Prop) (P : type686 A) (_33300 : A -> Prop) : (term670 A t P _33300) = (term672 A t P _33300).
Proof. exact (MK_COMB (@lem3252135 A _33300 t) (@lem3252136 A P _33300)). Qed.
Lemma lem3252138 {A : Type'} (t : A -> Prop) (P : type686 A) (_33300 : A -> Prop) : (term667 A P _33300 t) = (term672 A t P _33300).
Proof. exact (TRANS (@lem3252130 A t P _33300) (@lem3252137 A t P _33300)). Qed.
Lemma lem3252141 {A : Type'} (_33300 : A -> Prop) (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term672 A t P _33300.
Proof. exact (EQ_MP (@lem3252138 A t P _33300) (@lem3252127 A _33300 s u' t P a h1)). Qed.
Lemma lem3252142 {A : Type'} (_33300 : A -> Prop) (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term672 A t P _33300.
Proof. exact (@lem3252141 A _33300 s u' t P a h1). Qed.
Lemma lem3252143 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term672 A t P u'.
Proof. exact (@lem3252142 A u' s u' t P a h1). Qed.
Lemma lem3252146 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : P u'.
Proof. exact (@lem3252143 A s u' t P a h1 (@lem3252098 A s u' t P a h1)). Qed.
Lemma lem3252147 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term622 A P u'.
Proof. exact (fun h0 : term547 A P u' => @lem3252146 A s u' t P a h1). Qed.
Lemma lem3252149 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3252150 {A : Type'} (P : type686 A) (u' : A -> Prop) : (term622 A P u') = (P u').
Proof. exact (@lem3252149 (P u')). Qed.
Lemma lem3252151 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : P u'.
Proof. exact (EQ_MP (@lem3252150 A P u') (@lem3252147 A s u' t P a h1)). Qed.
Lemma lem3252157 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3252158 {A : Type'} (_33365 : A -> Prop) (P : type686 A) (_33364 : A -> Prop) : (term573 A _33365 P _33364) = (term601 A _33365 P _33364).
Proof. exact (@lem3252157 (P _33365) (term602 A _33364 _33365) (term547 A P _33364)). Qed.
Lemma lem3252172 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3252173 {A : Type'} (P : type686 A) (_33364 : A -> Prop) (_33365 : A -> Prop) : (term603 A _33365 P _33364) = (term604 A P _33364 _33365).
Proof. exact (@lem3252172 (term547 A P _33364) (term602 A _33364 _33365)). Qed.
Lemma lem3252181 {A : Type'} (P : type686 A) (_33365 : A -> Prop) : (term605 A P _33365) = (term605 A P _33365).
Proof. exact (eq_refl (term605 A P _33365)). Qed.
Lemma lem3252182 {A : Type'} (P : type686 A) (_33364 : A -> Prop) (_33365 : A -> Prop) : (term601 A _33365 P _33364) = (term606 A P _33364 _33365).
Proof. exact (MK_COMB (@lem3252181 A P _33365) (@lem3252173 A P _33364 _33365)). Qed.
Lemma lem3252193 {A : Type'} (P : type686 A) (_33364 : A -> Prop) (_33365 : A -> Prop) : (term573 A _33365 P _33364) = (term606 A P _33364 _33365).
Proof. exact (TRANS (@lem3252158 A _33365 P _33364) (@lem3252182 A P _33364 _33365)). Qed.
Lemma lem3252194 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3252195 {A : Type'} (P : type686 A) (_33364 : A -> Prop) (_33365 : A -> Prop) : (term607 A _33365 P _33364) = (term608 A P _33364 _33365).
Proof. exact (MK_COMB (@lem3252194) (@lem3252193 A P _33364 _33365)). Qed.
Lemma lem3252209 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3252210 {A : Type'} (P : type686 A) (_33364 : A -> Prop) (_33365 : A -> Prop) : (term603 A _33365 P _33364) = (term604 A P _33364 _33365).
Proof. exact (@lem3252209 (term547 A P _33364) (term602 A _33364 _33365)). Qed.
Lemma lem3252218 {A : Type'} (P : type686 A) (_33365 : A -> Prop) : (term605 A P _33365) = (term605 A P _33365).
Proof. exact (eq_refl (term605 A P _33365)). Qed.
Lemma lem3252219 {A : Type'} (P : type686 A) (_33364 : A -> Prop) (_33365 : A -> Prop) : (term601 A _33365 P _33364) = (term606 A P _33364 _33365).
Proof. exact (MK_COMB (@lem3252218 A P _33365) (@lem3252210 A P _33364 _33365)). Qed.
Lemma lem3252230 {A : Type'} (P : type686 A) (_33364 : A -> Prop) (_33365 : A -> Prop) : ((term573 A _33365 P _33364) = (term601 A _33365 P _33364)) = ((term606 A P _33364 _33365) = (term606 A P _33364 _33365)).
Proof. exact (MK_COMB (@lem3252195 A P _33364 _33365) (@lem3252219 A P _33364 _33365)). Qed.
Lemma lem3252232 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3252233 (x : Prop) : (x = x) = True.
Proof. exact (@lem3252232 Prop x). Qed.
Lemma lem3252234 {A : Type'} (P : type686 A) (_33364 : A -> Prop) (_33365 : A -> Prop) : ((term606 A P _33364 _33365) = (term606 A P _33364 _33365)) = True.
Proof. exact (@lem3252233 (term606 A P _33364 _33365)). Qed.
Lemma lem3252235 {A : Type'} (_33365 : A -> Prop) (P : type686 A) (_33364 : A -> Prop) : ((term573 A _33365 P _33364) = (term601 A _33365 P _33364)) = True.
Proof. exact (TRANS (@lem3252230 A P _33364 _33365) (@lem3252234 A P _33364 _33365)). Qed.
Lemma lem3252236 {A : Type'} (_33365 : A -> Prop) (P : type686 A) (_33364 : A -> Prop) : True = ((term573 A _33365 P _33364) = (term601 A _33365 P _33364)).
Proof. exact (SYM (@lem3252235 A _33365 P _33364)). Qed.
Lemma lem3252237 {A : Type'} (_33365 : A -> Prop) (P : type686 A) (_33364 : A -> Prop) : (term573 A _33365 P _33364) = (term601 A _33365 P _33364).
Proof. exact (EQ_MP (@lem3252236 A _33365 P _33364) (@lem0)). Qed.
Lemma lem3252238 {A : Type'} (_33365 : A -> Prop) (P : type686 A) (_33364 : A -> Prop) : term601 A _33365 P _33364.
Proof. exact (EQ_MP (@lem3252237 A _33365 P _33364) (@lem3251913 A _33365 P _33364)). Qed.
Lemma lem3252240 (b : Prop) (a : Prop) : (a \/ b) = (term266 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3252241 {A : Type'} (_33364 : A -> Prop) (P : type686 A) (_33365 : A -> Prop) : (term601 A _33365 P _33364) = (term609 A _33364 P _33365).
Proof. exact (@lem3252240 (term603 A _33365 P _33364) (P _33365)). Qed.
Lemma lem3252243 (a : Prop) (b : Prop) : (term277 a b) = (term278 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3252244 {A : Type'} (_33365 : A -> Prop) (P : type686 A) (_33364 : A -> Prop) : (term610 A _33365 P _33364) = (term611 A _33365 P _33364).
Proof. exact (@lem3252243 (term602 A _33364 _33365) (term547 A P _33364)). Qed.
Lemma lem3252246 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3252247 {A : Type'} (_33364 : A -> Prop) (_33365 : A -> Prop) : (term612 A _33364 _33365) = (_33364 = _33365).
Proof. exact (@lem3252246 (_33364 = _33365)). Qed.
Lemma lem3252248 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3252249 {A : Type'} (_33364 : A -> Prop) (_33365 : A -> Prop) : (term613 A _33364 _33365) = (term614 A _33364 _33365).
Proof. exact (MK_COMB (@lem3252248) (@lem3252247 A _33364 _33365)). Qed.
Lemma lem3252251 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3252252 {A : Type'} (P : type686 A) (_33364 : A -> Prop) : (term615 A P _33364) = (P _33364).
Proof. exact (@lem3252251 (P _33364)). Qed.
Lemma lem3252253 {A : Type'} (_33365 : A -> Prop) (P : type686 A) (_33364 : A -> Prop) : (term611 A _33365 P _33364) = (term616 A _33365 P _33364).
Proof. exact (MK_COMB (@lem3252249 A _33364 _33365) (@lem3252252 A P _33364)). Qed.
Lemma lem3252254 {A : Type'} (_33365 : A -> Prop) (P : type686 A) (_33364 : A -> Prop) : (term610 A _33365 P _33364) = (term616 A _33365 P _33364).
Proof. exact (TRANS (@lem3252244 A _33365 P _33364) (@lem3252253 A _33365 P _33364)). Qed.
Lemma lem3252255 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3252256 {A : Type'} (_33365 : A -> Prop) (P : type686 A) (_33364 : A -> Prop) : (term617 A _33365 P _33364) = (term618 A _33365 P _33364).
Proof. exact (MK_COMB (@lem3252255) (@lem3252254 A _33365 P _33364)). Qed.
Lemma lem3252257 {A : Type'} (P : type686 A) (_33365 : A -> Prop) : (P _33365) = (P _33365).
Proof. exact (eq_refl (P _33365)). Qed.
Lemma lem3252258 {A : Type'} (_33364 : A -> Prop) (P : type686 A) (_33365 : A -> Prop) : (term609 A _33364 P _33365) = (term619 A _33364 P _33365).
Proof. exact (MK_COMB (@lem3252256 A _33365 P _33364) (@lem3252257 A P _33365)). Qed.
Lemma lem3252259 {A : Type'} (_33364 : A -> Prop) (P : type686 A) (_33365 : A -> Prop) : (term601 A _33365 P _33364) = (term619 A _33364 P _33365).
Proof. exact (TRANS (@lem3252241 A _33364 P _33365) (@lem3252258 A _33364 P _33365)). Qed.
Lemma lem3252261 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term356 A) (h2 : term487 A s u' t P a) : term673 A P u'.
Proof. exact (conj (@lem3252091 A u' h1) (@lem3252151 A s u' t P a h2)). Qed.
Lemma lem3252263 {A : Type'} (_33364 : A -> Prop) (P : type686 A) (_33365 : A -> Prop) : term619 A _33364 P _33365.
Proof. exact (EQ_MP (@lem3252259 A _33364 P _33365) (@lem3252238 A _33365 P _33364)). Qed.
Lemma lem3252264 {A : Type'} (_33364 : A -> Prop) (P : type686 A) (_33365 : A -> Prop) : term619 A _33364 P _33365.
Proof. exact (@lem3252263 A _33364 P _33365). Qed.
Lemma lem3252265 {A : Type'} (P : type686 A) (u' : A -> Prop) : term674 A P u'.
Proof. exact (@lem3252264 A u' P (@UNION A (@EMPTY A) u')). Qed.
Lemma lem3252268 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term356 A) (h2 : term487 A s u' t P a) : term599 A P u'.
Proof. exact (@lem3252265 A P u' (@lem3252261 A s u' t P a h1 h2)). Qed.
Lemma lem3252269 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term356 A) (h2 : term487 A s u' t P a) : term600 A P u'.
Proof. exact (fun h0 : term564 A P u' => @lem3252268 A s u' t P a h1 h2). Qed.
Lemma lem3252271 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3252272 {A : Type'} (P : type686 A) (u' : A -> Prop) : (term600 A P u') = (term599 A P u').
Proof. exact (@lem3252271 (term599 A P u')). Qed.
Lemma lem3252273 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term356 A) (h2 : term487 A s u' t P a) : term599 A P u'.
Proof. exact (EQ_MP (@lem3252272 A P u') (@lem3252269 A s u' t P a h1 h2)). Qed.
Lemma lem3252276 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3252278 {A : Type'} (P : type686 A) (u' : A -> Prop) : (term564 A P u') = (term675 A P u').
Proof. exact (@lem3252276 (term599 A P u')). Qed.
Lemma lem3252281 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term487 A s u' t P a) (h2 : s = (@EMPTY A)) : term675 A P u'.
Proof. exact (EQ_MP (@lem3252278 A P u') (@lem3251192 A u' t P a s h1 h2)). Qed.
Lemma lem3252284 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term356 A) (h2 : term487 A s u' t P a) (h3 : s = (@EMPTY A)) : False.
Proof. exact (@lem3252281 A u' t P a s h2 h3 (@lem3252273 A s u' t P a h1 h2)). Qed.
Lemma lem3252285 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term356 A) (h2 : term487 A s u' t P a) (h3 : s = (@EMPTY A)) : term256.
Proof. exact (fun h0 : ~ False => @lem3252284 A u' t P a s h1 h2 h3). Qed.
Lemma lem3252287 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3252288 : term256 = False.
Proof. exact (@lem3252287 False). Qed.
Lemma lem3252356 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : @SUBSET A u' t.
Proof. exact (proj2 (@lem3250757 A s u' t P a h1)). Qed.
Lemma lem3252357 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term578 A u' t.
Proof. exact (fun h0 : term384 A u' t => @lem3252356 A s u' t P a h1). Qed.
Lemma lem3252359 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3252360 {A : Type'} (u' : A -> Prop) (t : A -> Prop) : (term578 A u' t) = (@SUBSET A u' t).
Proof. exact (@lem3252359 (@SUBSET A u' t)). Qed.
Lemma lem3252361 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : @SUBSET A u' t.
Proof. exact (EQ_MP (@lem3252360 A u' t) (@lem3252357 A s u' t P a h1)). Qed.
Lemma lem3252367 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3252368 {A : Type'} (P : type686 A) (a : A) (_33303 : A -> Prop) (t : A -> Prop) : (term569 A t P a _33303) = (term676 A P a _33303 t).
Proof. exact (@lem3252367 (term325 A P a _33303) (term384 A _33303 t)). Qed.
Lemma lem3252374 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3252375 {A : Type'} (P : type686 A) (a : A) (_33303 : A -> Prop) (t : A -> Prop) : (term677 A t P a _33303) = (term678 A P a _33303 t).
Proof. exact (MK_COMB (@lem3252374) (@lem3252368 A P a _33303 t)). Qed.
Lemma lem3252381 {A : Type'} (P : type686 A) (a : A) (_33303 : A -> Prop) (t : A -> Prop) : (term676 A P a _33303 t) = (term676 A P a _33303 t).
Proof. exact (eq_refl (term676 A P a _33303 t)). Qed.
Lemma lem3252382 {A : Type'} (P : type686 A) (a : A) (_33303 : A -> Prop) (t : A -> Prop) : ((term569 A t P a _33303) = (term676 A P a _33303 t)) = ((term676 A P a _33303 t) = (term676 A P a _33303 t)).
Proof. exact (MK_COMB (@lem3252375 A P a _33303 t) (@lem3252381 A P a _33303 t)). Qed.
Lemma lem3252384 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3252385 (x : Prop) : (x = x) = True.
Proof. exact (@lem3252384 Prop x). Qed.
Lemma lem3252386 {A : Type'} (P : type686 A) (a : A) (_33303 : A -> Prop) (t : A -> Prop) : ((term676 A P a _33303 t) = (term676 A P a _33303 t)) = True.
Proof. exact (@lem3252385 (term676 A P a _33303 t)). Qed.
Lemma lem3252387 {A : Type'} (P : type686 A) (a : A) (_33303 : A -> Prop) (t : A -> Prop) : ((term569 A t P a _33303) = (term676 A P a _33303 t)) = True.
Proof. exact (TRANS (@lem3252382 A P a _33303 t) (@lem3252386 A P a _33303 t)). Qed.
Lemma lem3252388 {A : Type'} (P : type686 A) (a : A) (_33303 : A -> Prop) (t : A -> Prop) : True = ((term569 A t P a _33303) = (term676 A P a _33303 t)).
Proof. exact (SYM (@lem3252387 A P a _33303 t)). Qed.
Lemma lem3252389 {A : Type'} (P : type686 A) (a : A) (_33303 : A -> Prop) (t : A -> Prop) : (term569 A t P a _33303) = (term676 A P a _33303 t).
Proof. exact (EQ_MP (@lem3252388 A P a _33303 t) (@lem0)). Qed.
Lemma lem3252390 {A : Type'} (_33303 : A -> Prop) (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term676 A P a _33303 t.
Proof. exact (EQ_MP (@lem3252389 A P a _33303 t) (@lem3251331 A _33303 s u' t P a h1)). Qed.
Lemma lem3252392 (b : Prop) (a : Prop) : (a \/ b) = (term266 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3252393 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (_33303 : A -> Prop) : (term676 A P a _33303 t) = (term679 A t P a _33303).
Proof. exact (@lem3252392 (term384 A _33303 t) (term325 A P a _33303)). Qed.
Lemma lem3252395 (a : Prop) : (term51 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3252396 {A : Type'} (_33303 : A -> Prop) (t : A -> Prop) : (term592 A _33303 t) = (@SUBSET A _33303 t).
Proof. exact (@lem3252395 (@SUBSET A _33303 t)). Qed.
Lemma lem3252397 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3252398 {A : Type'} (_33303 : A -> Prop) (t : A -> Prop) : (term671 A _33303 t) = (term329 A _33303 t).
Proof. exact (MK_COMB (@lem3252397) (@lem3252396 A _33303 t)). Qed.
Lemma lem3252399 {A : Type'} (P : type686 A) (a : A) (_33303 : A -> Prop) : (term325 A P a _33303) = (term325 A P a _33303).
Proof. exact (eq_refl (term325 A P a _33303)). Qed.
Lemma lem3252400 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (_33303 : A -> Prop) : (term679 A t P a _33303) = (term680 A t P a _33303).
Proof. exact (MK_COMB (@lem3252398 A _33303 t) (@lem3252399 A P a _33303)). Qed.
Lemma lem3252401 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (_33303 : A -> Prop) : (term676 A P a _33303 t) = (term680 A t P a _33303).
Proof. exact (TRANS (@lem3252393 A t P a _33303) (@lem3252400 A t P a _33303)). Qed.
Lemma lem3252404 {A : Type'} (_33303 : A -> Prop) (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term680 A t P a _33303.
Proof. exact (EQ_MP (@lem3252401 A t P a _33303) (@lem3252390 A _33303 s u' t P a h1)). Qed.
Lemma lem3252405 {A : Type'} (_33303 : A -> Prop) (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term680 A t P a _33303.
Proof. exact (@lem3252404 A _33303 s u' t P a h1). Qed.
Lemma lem3252406 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term680 A t P a u'.
Proof. exact (@lem3252405 A u' s u' t P a h1). Qed.
Lemma lem3252409 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term325 A P a u'.
Proof. exact (@lem3252406 A s u' t P a h1 (@lem3252361 A s u' t P a h1)). Qed.
Lemma lem3252410 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term643 A P a u'.
Proof. exact (fun h0 : term548 A P a u' => @lem3252409 A s u' t P a h1). Qed.
Lemma lem3252412 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3252413 {A : Type'} (P : type686 A) (a : A) (u' : A -> Prop) : (term643 A P a u') = (term325 A P a u').
Proof. exact (@lem3252412 (term325 A P a u')). Qed.
Lemma lem3252414 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term487 A s u' t P a) : term325 A P a u'.
Proof. exact (EQ_MP (@lem3252413 A P a u') (@lem3252410 A s u' t P a h1)). Qed.
Lemma lem3252417 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3252419 {A : Type'} (P : type686 A) (a : A) (u' : A -> Prop) : (term548 A P a u') = (term644 A P a u').
Proof. exact (@lem3252417 (term325 A P a u')). Qed.
Lemma lem3252422 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (s : A -> Prop) (a : A) (h1 : term487 A s u' t P a) (h2 : s = (@INSERT A a (@EMPTY A))) : term644 A P a u'.
Proof. exact (EQ_MP (@lem3252419 A P a u') (@lem3251289 A u' t P s a h1 h2)). Qed.
Lemma lem3252425 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (s : A -> Prop) (a : A) (h1 : term487 A s u' t P a) (h2 : s = (@INSERT A a (@EMPTY A))) : False.
Proof. exact (@lem3252422 A u' t P s a h1 h2 (@lem3252414 A s u' t P a h1)). Qed.
Lemma lem3252426 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (s : A -> Prop) (a : A) (h1 : term487 A s u' t P a) (h2 : s = (@INSERT A a (@EMPTY A))) : term256.
Proof. exact (fun h0 : ~ False => @lem3252425 A u' t P s a h1 h2). Qed.
Lemma lem3252428 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3252429 : term256 = False.
Proof. exact (@lem3252428 False). Qed.
Lemma lem3252431 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (s : A -> Prop) (a : A) (h1 : term487 A s u' t P a) (h2 : s = (@INSERT A a (@EMPTY A))) : False.
Proof. exact (EQ_MP (@lem3252429) (@lem3252426 A u' t P s a h1 h2)). Qed.
Lemma lem3252432 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term356 A) (h2 : term487 A s u' t P a) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem3252288) (@lem3252285 A u' t P a s h1 h2 h3)). Qed.
Lemma lem3252433 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (s : A -> Prop) (a : A) (h1 : term487 A s u' t P a) (h2 : s = (@INSERT A a (@EMPTY A))) : (s = (@INSERT A a (@EMPTY A))) = False.
Proof. exact (prop_ext (fun h3 : s = (@INSERT A a (@EMPTY A)) => @lem3252431 A u' t P s a h1 h2) (fun h3 : False => @lem3251125 A s a h2)). Qed.
Lemma lem3252434 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (s : A -> Prop) (a : A) (h1 : term487 A s u' t P a) (h2 : s = (@INSERT A a (@EMPTY A))) : False.
Proof. exact (EQ_MP (@lem3252433 A u' t P s a h1 h2) (@lem3251125 A s a h2)). Qed.
Lemma lem3252435 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term356 A) (h2 : term487 A s u' t P a) (h3 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY A) => @lem3252432 A u' t P a s h1 h2 h3) (fun h4 : False => @lem3251103 A s h3)). Qed.
Lemma lem3252436 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term356 A) (h2 : term487 A s u' t P a) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem3252435 A u' t P a s h1 h2 h3) (@lem3251103 A s h3)). Qed.
Lemma lem3252437 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term548 A P a s) (h2 : term454 A t P a s) : (term548 A P a s) = False.
Proof. exact (prop_ext (fun h3 : term548 A P a s => @lem3251882 A t P a s h1 h2) (fun h3 : False => @lem3251069 A P a s h1)). Qed.
Lemma lem3252438 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term548 A P a s) (h2 : term454 A t P a s) : False.
Proof. exact (EQ_MP (@lem3252437 A t P a s h1 h2) (@lem3251069 A P a s h1)). Qed.
Lemma lem3252439 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term547 A P s) (h2 : term454 A t P a s) (h3 : term356 A) : (term547 A P s) = False.
Proof. exact (prop_ext (fun h4 : term547 A P s => @lem3251672 A t P a s h1 h2 h3) (fun h4 : False => @lem3251037 A P s h1)). Qed.
Lemma lem3252440 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term547 A P s) (h2 : term454 A t P a s) (h3 : term356 A) : False.
Proof. exact (EQ_MP (@lem3252439 A t P a s h1 h2 h3) (@lem3251037 A P s h1)). Qed.
Lemma lem3252441 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (s : A -> Prop) (a : A) (h1 : term487 A s u' t P a) (h2 : s = (@INSERT A a (@EMPTY A))) : (s = (@INSERT A a (@EMPTY A))) = False.
Proof. exact (prop_ext (fun h3 : s = (@INSERT A a (@EMPTY A)) => @lem3252434 A u' t P s a h1 h2) (fun h3 : False => @lem3250979 A s a h2)). Qed.
Lemma lem3252442 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (s : A -> Prop) (a : A) (h1 : term487 A s u' t P a) (h2 : s = (@INSERT A a (@EMPTY A))) : False.
Proof. exact (EQ_MP (@lem3252441 A u' t P s a h1 h2) (@lem3250979 A s a h2)). Qed.
Lemma lem3252443 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term356 A) (h2 : term487 A s u' t P a) (h3 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY A) => @lem3252436 A u' t P a s h1 h2 h3) (fun h4 : False => @lem3250930 A s h3)). Qed.
Lemma lem3252444 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term356 A) (h2 : term487 A s u' t P a) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem3252443 A u' t P a s h1 h2 h3) (@lem3250930 A s h3)). Qed.
Lemma lem3252445 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term548 A P a s) (h2 : term454 A t P a s) : (term548 A P a s) = False.
Proof. exact (prop_ext (fun h3 : term548 A P a s => @lem3252438 A t P a s h1 h2) (fun h3 : False => @lem3250881 A P a s h1)). Qed.
Lemma lem3252446 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term548 A P a s) (h2 : term454 A t P a s) : False.
Proof. exact (EQ_MP (@lem3252445 A t P a s h1 h2) (@lem3250881 A P a s h1)). Qed.
Lemma lem3252447 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term547 A P s) (h2 : term454 A t P a s) (h3 : term356 A) : (term547 A P s) = False.
Proof. exact (prop_ext (fun h4 : term547 A P s => @lem3252440 A t P a s h1 h2 h3) (fun h4 : False => @lem3250821 A P s h1)). Qed.
Lemma lem3252448 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term547 A P s) (h2 : term454 A t P a s) (h3 : term356 A) : False.
Proof. exact (EQ_MP (@lem3252447 A t P a s h1 h2 h3) (@lem3250821 A P s h1)). Qed.
Lemma lem3252449 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (s : A -> Prop) (a : A) (h1 : term487 A s u' t P a) (h2 : s = (@INSERT A a (@EMPTY A))) : (s = (@INSERT A a (@EMPTY A))) = False.
Proof. exact (prop_ext (fun h3 : s = (@INSERT A a (@EMPTY A)) => @lem3252442 A u' t P s a h1 h2) (fun h3 : False => @lem3250979 A s a h2)). Qed.
Lemma lem3252450 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (s : A -> Prop) (a : A) (h1 : term487 A s u' t P a) (h2 : s = (@INSERT A a (@EMPTY A))) : False.
Proof. exact (EQ_MP (@lem3252449 A u' t P s a h1 h2) (@lem3250979 A s a h2)). Qed.
Lemma lem3252451 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term356 A) (h2 : term487 A s u' t P a) (h3 : s = (@EMPTY A)) : (s = (@EMPTY A)) = False.
Proof. exact (prop_ext (fun h4 : s = (@EMPTY A) => @lem3252444 A u' t P a s h1 h2 h3) (fun h4 : False => @lem3250930 A s h3)). Qed.
Lemma lem3252452 {A : Type'} (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term356 A) (h2 : term487 A s u' t P a) (h3 : s = (@EMPTY A)) : False.
Proof. exact (EQ_MP (@lem3252451 A u' t P a s h1 h2 h3) (@lem3250930 A s h3)). Qed.
Lemma lem3252453 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term548 A P a s) (h2 : term454 A t P a s) : (term548 A P a s) = False.
Proof. exact (prop_ext (fun h3 : term548 A P a s => @lem3252446 A t P a s h1 h2) (fun h3 : False => @lem3250881 A P a s h1)). Qed.
Lemma lem3252454 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term548 A P a s) (h2 : term454 A t P a s) : False.
Proof. exact (EQ_MP (@lem3252453 A t P a s h1 h2) (@lem3250881 A P a s h1)). Qed.
Lemma lem3252455 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term547 A P s) (h2 : term454 A t P a s) (h3 : term356 A) : (term547 A P s) = False.
Proof. exact (prop_ext (fun h4 : term547 A P s => @lem3252448 A t P a s h1 h2 h3) (fun h4 : False => @lem3250821 A P s h1)). Qed.
Lemma lem3252456 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term547 A P s) (h2 : term454 A t P a s) (h3 : term356 A) : False.
Proof. exact (EQ_MP (@lem3252455 A t P a s h1 h2 h3) (@lem3250821 A P s h1)). Qed.
Lemma lem3252457 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term356 A) (h2 : term487 A s u' t P a) : False.
Proof. exact (or_elim (@lem3250759 A s u' t P a h2) (fun h0 : s = (@EMPTY A) => @lem3252452 A u' t P a s h1 h2 h0) (fun h0 : s = (@INSERT A a (@EMPTY A)) => @lem3252450 A u' t P s a h2 h0)). Qed.
Lemma lem3252458 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (s : A -> Prop) (h1 : term454 A t P a s) (h2 : term356 A) : False.
Proof. exact (or_elim (@lem3250750 A t P a s h1) (fun h0 : term547 A P s => @lem3252456 A t P a s h0 h1 h2) (fun h0 : term548 A P a s => @lem3252454 A t P a s h0 h1)). Qed.
Lemma lem3252459 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term356 A) (h2 : term529 A s u' t P a) : False.
Proof. exact (or_elim (@lem3250743 A s u' t P a h2) (fun h0 : term454 A t P a s => @lem3252458 A t P a s h0 h1) (fun h0 : term487 A s u' t P a => @lem3252457 A s u' t P a h1 h0)). Qed.
Lemma lem3252460 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term356 A) (h2 : term529 A s u' t P a) : (term529 A s u' t P a) = False.
Proof. exact (prop_ext (fun h3 : term529 A s u' t P a => @lem3252459 A s u' t P a h1 h2) (fun h3 : False => @lem3250743 A s u' t P a h2)). Qed.
Lemma lem3252461 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term356 A) (h2 : term529 A s u' t P a) : False.
Proof. exact (EQ_MP (@lem3252460 A s u' t P a h1 h2) (@lem3250743 A s u' t P a h2)). Qed.
Lemma lem3252462 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term356 A) (h2 : term529 A s u' t P a) : (term356 A) = False.
Proof. exact (prop_ext (fun h3 : term356 A => @lem3252461 A s u' t P a h1 h2) (fun h3 : False => @lem3250590 A h1)). Qed.
Lemma lem3252463 {A : Type'} (s : A -> Prop) (u' : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term356 A) (h2 : term529 A s u' t P a) : False.
Proof. exact (EQ_MP (@lem3252462 A s u' t P a h1 h2) (@lem3250590 A h1)). Qed.
Lemma lem3252464 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : type686 A) (a : A) (h1 : term532 A s t P a) (h2 : term356 A) : False.
Proof. exact (ex_elim (@lem3250561 A s t P a h1) (fun u' : A -> Prop => fun h0 : term531 A s t P a u' => @lem3252463 A s u' t P a h2 h0)). Qed.
Lemma lem3252465 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term355 A t P a) (h2 : term356 A) : False.
Proof. exact (ex_elim (@lem3250536 A t P a h1) (fun s : A -> Prop => fun h0 : term533 A t P a s => @lem3252464 A s t P a h0 h2)). Qed.
Lemma lem3252466 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term355 A t P a) (h2 : term356 A) : (term356 A) = False.
Proof. exact (prop_ext (fun h3 : term356 A => @lem3252465 A t P a h1 h2) (fun h3 : False => @lem3250560 A h2)). Qed.
Lemma lem3252467 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term355 A t P a) (h2 : term356 A) : False.
Proof. exact (EQ_MP (@lem3252466 A t P a h1 h2) (@lem3250560 A h2)). Qed.
Lemma lem3252468 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term355 A t P a) : term361 A.
Proof. exact (fun h0 : term356 A => @lem3252467 A t P a h1 h0). Qed.
Lemma lem3252469 {A : Type'} : (term361 A) = (term362 A).
Proof. exact (@lem69 (term356 A)). Qed.
Lemma lem3252470 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term355 A t P a) : term362 A.
Proof. exact (EQ_MP (@lem3252469 A) (@lem3252468 A t P a h1)). Qed.
Lemma lem3252471 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : term364 A t P a.
Proof. exact (fun h0 : term355 A t P a => @lem3252470 A t P a h0). Qed.
Lemma lem3252476 {A : Type'} (P : type686 A) (a : A) : term368 A P a.
Proof. exact (fun t : A -> Prop => @lem3252471 A t P a). Qed.
Lemma lem3252481 {A : Type'} (a : A) : term372 A a.
Proof. exact (fun P : type686 A => @lem3252476 A P a). Qed.
Lemma lem3252486 {A : Type'} : term376 A.
Proof. exact (fun a : A => @lem3252481 A a). Qed.
Lemma lem3252487 {A : Type'} : term375 A.
Proof. exact (EQ_MP (@lem3250081 A) (@lem3252486 A)). Qed.
Lemma lem3252488 {A : Type'} (a : A) : term681 A a.
Proof. exact (@lem3252487 A a). Qed.
Lemma lem3252489 {A : Type'} (a : A) : (term681 A a) = (term371 A a).
Proof. exact (eq_refl (term681 A a)). Qed.
Lemma lem3252490 {A : Type'} (a : A) : term371 A a.
Proof. exact (EQ_MP (@lem3252489 A a) (@lem3252488 A a)). Qed.
Lemma lem3252491 {A : Type'} (a : A) (P : type686 A) : term682 A a P.
Proof. exact (@lem3252490 A a P). Qed.
Lemma lem3252492 {A : Type'} (P : type686 A) (a : A) : (term682 A a P) = (term367 A P a).
Proof. exact (eq_refl (term682 A a P)). Qed.
Lemma lem3252493 {A : Type'} (P : type686 A) (a : A) : term367 A P a.
Proof. exact (EQ_MP (@lem3252492 A P a) (@lem3252491 A a P)). Qed.
Lemma lem3252494 {A : Type'} (P : type686 A) (a : A) (t : A -> Prop) : term683 A P a t.
Proof. exact (@lem3252493 A P a t). Qed.
Lemma lem3252495 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term683 A P a t) = (term357 A t P a).
Proof. exact (eq_refl (term683 A P a t)). Qed.
Lemma lem3252496 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : term357 A t P a.
Proof. exact (EQ_MP (@lem3252495 A t P a) (@lem3252494 A P a t)). Qed.
Lemma lem3252498 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : term357 A t P a.
Proof. exact (@lem3249876 A t P a (@lem3252496 A t P a)). Qed.
Lemma lem3252499 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term355 A t P a) : term361 A.
Proof. exact (@lem3252498 A t P a (@lem3249857 A t P a h1)). Qed.
Lemma lem3252500 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term355 A t P a) : False.
Proof. exact (@lem3252499 A t P a h1 (@lem3249858 A)). Qed.
Lemma lem3252501 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term355 A t P a) : (term355 A t P a) = False.
Proof. exact (prop_ext (fun h2 : term355 A t P a => @lem3252500 A t P a h1) (fun h2 : False => @lem3249857 A t P a h1)). Qed.
Lemma lem3252502 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) (h1 : term355 A t P a) : False.
Proof. exact (EQ_MP (@lem3252501 A t P a h1) (@lem3249857 A t P a h1)). Qed.
Lemma lem3252503 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : term354 A t P a.
Proof. exact (fun h0 : term355 A t P a => @lem3252502 A t P a h0). Qed.
Lemma lem3252504 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term352 A a t P) = (term335 A t P a).
Proof. exact (EQ_MP (@lem3249856 A t P a) (@lem3252503 A t P a)). Qed.
Lemma lem3252505 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term321 A a t P) = (term335 A t P a).
Proof. exact (EQ_MP (@lem3249852 A t P a) (@lem3252504 A t P a)). Qed.
Lemma lem3252506 {A : Type'} (t : A -> Prop) (P : type686 A) (a : A) : (term320 A a t P) = (term334 A t P a).
Proof. exact (EQ_MP (@lem3249782 A t P a) (@lem3252505 A t P a)). Qed.
Lemma lem3252511 {A : Type'} (P : type686 A) (a : A) : term684 A P a.
Proof. exact (fun t : A -> Prop => @lem3252506 A t P a). Qed.
Lemma lem3252516 {A : Type'} (P : type686 A) : term685 A P.
Proof. exact (fun a : A => @lem3252511 A P a). Qed.
