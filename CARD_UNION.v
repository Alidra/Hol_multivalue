Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_UNION_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import BOOL_CASES_AX_spec.
Require Import CARD_CLAUSES_spec.
Require Import EXTENSION_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import FINITE_UNION_IMP_spec.
Require Import INTER_EMPTY_spec.
Require Import IN_INSERT_spec.
Require Import IN_INTER_spec.
Require Import IN_UNION_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import SUC_INJ_spec.
Require Import UNION_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19699_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem3840712 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem3840713 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem3840714 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem3840713 A x) (@lem3840712 A x)). Qed.
Lemma lem3840715 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem3840717 {A : Type'} (s : A -> Prop) : term3 A s.
Proof. exact (@lem3205222 A s). Qed.
Lemma lem3840718 {A : Type'} (s : A -> Prop) : (term3 A s) = (term4 A s).
Proof. exact (eq_refl (term3 A s)). Qed.
Lemma lem3840719 {A : Type'} (s : A -> Prop) : term4 A s.
Proof. exact (EQ_MP (@lem3840718 A s) (@lem3840717 A s)). Qed.
Lemma lem3840720 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term5 A s t.
Proof. exact (@lem3840719 A s t). Qed.
Lemma lem3840721 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term5 A s t) = (term6 A s t).
Proof. exact (eq_refl (term5 A s t)). Qed.
Lemma lem3840722 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term6 A s t.
Proof. exact (EQ_MP (@lem3840721 A s t) (@lem3840720 A s t)). Qed.
Lemma lem3840723 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term7 A s t x.
Proof. exact (@lem3840722 A s t x). Qed.
Lemma lem3840724 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A s t x) = ((term8 A x s t) = (term9 A s x t)).
Proof. exact (eq_refl (term7 A s t x)). Qed.
Lemma lem3840726 {A : Type'} (x : A) : term10 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3840727 {A : Type'} (x : A) : (term10 A x) = (term11 A x).
Proof. exact (eq_refl (term10 A x)). Qed.
Lemma lem3840728 {A : Type'} (x : A) : term11 A x.
Proof. exact (EQ_MP (@lem3840727 A x) (@lem3840726 A x)). Qed.
Lemma lem3840729 {A : Type'} (x : A) (y : A) : term12 A x y.
Proof. exact (@lem3840728 A x y). Qed.
Lemma lem3840730 {A : Type'} (y : A) (x : A) : (term12 A x y) = (term13 A y x).
Proof. exact (eq_refl (term12 A x y)). Qed.
Lemma lem3840731 {A : Type'} (y : A) (x : A) : term13 A y x.
Proof. exact (EQ_MP (@lem3840730 A y x) (@lem3840729 A x y)). Qed.
Lemma lem3840732 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term14 A y x s.
Proof. exact (@lem3840731 A y x s). Qed.
Lemma lem3840733 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term14 A y x s) = ((term15 A x y s) = (term16 A y x s)).
Proof. exact (eq_refl (term14 A y x s)). Qed.
Lemma lem3840735 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3840736 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (eq_refl (term17 A s)). Qed.
Lemma lem3840737 {A : Type'} (s : A -> Prop) : term18 A s.
Proof. exact (EQ_MP (@lem3840736 A s) (@lem3840735 A s)). Qed.
Lemma lem3840738 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term19 A s t.
Proof. exact (@lem3840737 A s t). Qed.
Lemma lem3840739 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = ((s = t) = (term20 A s t)).
Proof. exact (eq_refl (term19 A s t)). Qed.
Lemma lem3840741 {A : Type'} : term21 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem3840742 {A : Type'} : term21 A.
Proof. exact (@lem3840741 A). Qed.
Lemma lem3840743 {A : Type'} (x : A) : term22 A x.
Proof. exact (@lem3840742 A x). Qed.
Lemma lem3840744 {A : Type'} (x : A) : (term22 A x) = (term23 A x).
Proof. exact (eq_refl (term22 A x)). Qed.
Lemma lem3840745 {A : Type'} (x : A) : term23 A x.
Proof. exact (EQ_MP (@lem3840744 A x) (@lem3840743 A x)). Qed.
Lemma lem3840746 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term24 A x s t.
Proof. exact (@lem3840745 A x (@UNION A s t)). Qed.
Lemma lem3840747 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term24 A x s t) = (term25 A x s t).
Proof. exact (eq_refl (term24 A x s t)). Qed.
Lemma lem3840748 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term25 A x s t.
Proof. exact (EQ_MP (@lem3840747 A x s t) (@lem3840746 A x s t)). Qed.
Lemma lem3840749 {A : Type'} : term21 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem3840750 {A : Type'} : term21 A.
Proof. exact (@lem3840749 A). Qed.
Lemma lem3840751 {A : Type'} (x : A) : term22 A x.
Proof. exact (@lem3840750 A x). Qed.
Lemma lem3840752 {A : Type'} (x : A) : (term22 A x) = (term23 A x).
Proof. exact (eq_refl (term22 A x)). Qed.
Lemma lem3840753 {A : Type'} (x : A) : term23 A x.
Proof. exact (EQ_MP (@lem3840752 A x) (@lem3840751 A x)). Qed.
Lemma lem3840754 {A : Type'} (x : A) (s : A -> Prop) : term26 A x s.
Proof. exact (@lem3840753 A x s). Qed.
Lemma lem3840755 {A : Type'} (x : A) (s : A -> Prop) : (term26 A x s) = (term27 A x s).
Proof. exact (eq_refl (term26 A x s)). Qed.
Lemma lem3840756 {A : Type'} (x : A) (s : A -> Prop) : term27 A x s.
Proof. exact (EQ_MP (@lem3840755 A x s) (@lem3840754 A x s)). Qed.
Lemma lem3840757 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (h1). Qed.
Lemma lem3840758 {A : Type'} (s : A -> Prop) (h1 : term28 A) : term29 A s.
Proof. exact (@lem3840757 A h1 s). Qed.
Lemma lem3840759 {A : Type'} (s : A -> Prop) : (term29 A s) = (term30 A s).
Proof. exact (eq_refl (term29 A s)). Qed.
Lemma lem3840760 {A : Type'} (s : A -> Prop) (h1 : term28 A) : term30 A s.
Proof. exact (EQ_MP (@lem3840759 A s) (@lem3840758 A s h1)). Qed.
Lemma lem3840761 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term28 A) : term31 A s t.
Proof. exact (@lem3840760 A s h1 t). Qed.
Lemma lem3840762 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term31 A s t) = (term32 A s t).
Proof. exact (eq_refl (term31 A s t)). Qed.
Lemma lem3840763 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term28 A) : term32 A s t.
Proof. exact (EQ_MP (@lem3840762 A s t) (@lem3840761 A s t h1)). Qed.
Lemma lem3840764 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term33 A s t) : term33 A s t.
Proof. exact (h1). Qed.
Lemma lem3840765 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term28 A) (h2 : term33 A s t) : term34 A s t.
Proof. exact (@lem3840763 A s t h1 (@lem3840764 A s t h2)). Qed.
Lemma lem3840766 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term33 A s t) : term35 A s t.
Proof. exact (fun h0 : term28 A => @lem3840765 A s t h0 h1). Qed.
Lemma lem3840767 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (h1). Qed.
Lemma lem3840768 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term28 A) (h2 : term33 A s t) : term34 A s t.
Proof. exact (@lem3840766 A s t h2 (@lem3840767 A h1)). Qed.
Lemma lem3840769 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term28 A) : term32 A s t.
Proof. exact (fun h0 : term33 A s t => @lem3840768 A s t h1 h0). Qed.
Lemma lem3840770 {A : Type'} (s : A -> Prop) (h1 : term28 A) : term30 A s.
Proof. exact (fun t : A -> Prop => @lem3840769 A s t h1). Qed.
Lemma lem3840771 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (fun s : A -> Prop => @lem3840770 A s h1). Qed.
Lemma lem3840772 {A : Type'} : term36 A.
Proof. exact (fun h0 : term28 A => @lem3840771 A h0). Qed.
Lemma lem3840773 {A : Type'} : term28 A.
Proof. exact (@lem3840772 A (@lem3606091 A)). Qed.
Lemma lem3840774 {A : Type'} (s : A -> Prop) : term29 A s.
Proof. exact (@lem3840773 A s). Qed.
Lemma lem3840775 {A : Type'} (s : A -> Prop) : (term29 A s) = (term30 A s).
Proof. exact (eq_refl (term29 A s)). Qed.
Lemma lem3840776 {A : Type'} (s : A -> Prop) : term30 A s.
Proof. exact (EQ_MP (@lem3840775 A s) (@lem3840774 A s)). Qed.
Lemma lem3840777 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term31 A s t.
Proof. exact (@lem3840776 A s t). Qed.
Lemma lem3840778 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term31 A s t) = (term32 A s t).
Proof. exact (eq_refl (term31 A s t)). Qed.
Lemma lem3840810 : term37.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem3840811 (n : nat) : term38 n.
Proof. exact (@lem3840810 n). Qed.
Lemma lem3840812 (n : nat) : (term38 n) = ((term39 n) = n).
Proof. exact (eq_refl (term38 n)). Qed.
Lemma lem3840818 {A : Type'} : term40 A.
Proof. exact (proj1 (@lem3258370 A)). Qed.
Lemma lem3840819 {A : Type'} (s : A -> Prop) : term41 A s.
Proof. exact (@lem3840818 A s). Qed.
Lemma lem3840820 {A : Type'} (s : A -> Prop) : (term41 A s) = ((@INTER A (@EMPTY A) s) = (@EMPTY A)).
Proof. exact (eq_refl (term41 A s)). Qed.
Lemma lem3840836 {A : Type'} : term42 A.
Proof. exact (proj1 (@lem3235853 A)). Qed.
Lemma lem3840837 {A : Type'} (s : A -> Prop) : term43 A s.
Proof. exact (@lem3840836 A s). Qed.
Lemma lem3840838 {A : Type'} (s : A -> Prop) : (term43 A s) = ((@UNION A (@EMPTY A) s) = s).
Proof. exact (eq_refl (term43 A s)). Qed.
Lemma lem3840840 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (h1). Qed.
Lemma lem3840841 {A : Type'} (P : type686 A) (h1 : term44 A) : term45 A P.
Proof. exact (@lem3840840 A h1 P). Qed.
Lemma lem3840842 {A : Type'} (P : type686 A) : (term45 A P) = (term46 A P).
Proof. exact (eq_refl (term45 A P)). Qed.
Lemma lem3840843 {A : Type'} (P : type686 A) (h1 : term44 A) : term46 A P.
Proof. exact (EQ_MP (@lem3840842 A P) (@lem3840841 A P h1)). Qed.
Lemma lem3840844 {A : Type'} (P : type686 A) (h1 : term47 A P) : term47 A P.
Proof. exact (h1). Qed.
Lemma lem3840845 {A : Type'} (P : type686 A) (h1 : term44 A) (h2 : term47 A P) : term48 A P.
Proof. exact (@lem3840843 A P h1 (@lem3840844 A P h2)). Qed.
Lemma lem3840846 {A : Type'} (P : type686 A) (h1 : term47 A P) : term49 A P.
Proof. exact (fun h0 : term44 A => @lem3840845 A P h0 h1). Qed.
Lemma lem3840847 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (h1). Qed.
Lemma lem3840848 {A : Type'} (P : type686 A) (h1 : term44 A) (h2 : term47 A P) : term48 A P.
Proof. exact (@lem3840846 A P h2 (@lem3840847 A h1)). Qed.
Lemma lem3840849 {A : Type'} (P : type686 A) (h1 : term44 A) : term46 A P.
Proof. exact (fun h0 : term47 A P => @lem3840848 A P h1 h0). Qed.
Lemma lem3840850 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (fun P : type686 A => @lem3840849 A P h1). Qed.
Lemma lem3840851 {A : Type'} : term50 A.
Proof. exact (fun h0 : term44 A => @lem3840850 A h0). Qed.
Lemma lem3840852 {A : Type'} : term44 A.
Proof. exact (@lem3840851 A (@lem3558722 A)). Qed.
Lemma lem3840853 {A : Type'} (P : type686 A) : term45 A P.
Proof. exact (@lem3840852 A P). Qed.
Lemma lem3840854 {A : Type'} (P : type686 A) : (term45 A P) = (term46 A P).
Proof. exact (eq_refl (term45 A P)). Qed.
Lemma lem3840856 {A : Type'} (P : Prop) : term51 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem3840857 {A : Type'} (P : Prop) : (term51 A P) = (term52 A P).
Proof. exact (eq_refl (term51 A P)). Qed.
Lemma lem3840858 {A : Type'} (P : Prop) : term52 A P.
Proof. exact (EQ_MP (@lem3840857 A P) (@lem3840856 A P)). Qed.
Lemma lem3840859 {A : Type'} (P : Prop) (Q : A -> Prop) : term53 A P Q.
Proof. exact (@lem3840858 A P Q). Qed.
Lemma lem3840860 {A : Type'} (P : Prop) (Q : A -> Prop) : (term53 A P Q) = ((term54 A P Q) = (term55 A P Q)).
Proof. exact (eq_refl (term53 A P Q)). Qed.
Lemma lem3840878 (a : Prop) : term56 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem3840879 (a : Prop) : (term56 a) = (term57 a).
Proof. exact (eq_refl (term56 a)). Qed.
Lemma lem3840880 (a : Prop) : term57 a.
Proof. exact (EQ_MP (@lem3840879 a) (@lem3840878 a)). Qed.
Lemma lem3840881 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem3840882 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem3840899 (b : Prop) (c : Prop) (d : Prop) : (term58 b c d) = (term58 b c d).
Proof. exact (eq_refl (term58 b c d)). Qed.
Lemma lem3840900 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = True) : (term59 b c d a) = (term60 b c d).
Proof. exact (MK_COMB (@lem3840899 b c d) (@lem3840881 a h1)). Qed.
Lemma lem3840901 (b : Prop) (c : Prop) (d : Prop) : (term60 b c d) = ((term61 b c d) = (term62 b c d)).
Proof. exact (eq_refl (term60 b c d)). Qed.
Lemma lem3840902 (b : Prop) (c : Prop) (d : Prop) (a : Prop) : (term63 b c d a) = (term63 b c d a).
Proof. exact (eq_refl (term63 b c d a)). Qed.
Lemma lem3840903 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term59 b c d a) = (term60 b c d)) = ((term59 b c d a) = ((term61 b c d) = (term62 b c d))).
Proof. exact (MK_COMB (@lem3840902 b c d a) (@lem3840901 b c d)). Qed.
Lemma lem3840904 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : (term59 b c d a) = ((term64 a b c d) = (term65 a b c d)).
Proof. exact (eq_refl (term59 b c d a)). Qed.
Lemma lem3840905 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3840906 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : (term63 b c d a) = (term66 a b c d).
Proof. exact (MK_COMB (@lem3840905) (@lem3840904 a b c d)). Qed.
Lemma lem3840907 (b : Prop) (c : Prop) (d : Prop) : ((term61 b c d) = (term62 b c d)) = ((term61 b c d) = (term62 b c d)).
Proof. exact (eq_refl ((term61 b c d) = (term62 b c d))). Qed.
Lemma lem3840908 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term59 b c d a) = ((term61 b c d) = (term62 b c d))) = (((term64 a b c d) = (term65 a b c d)) = ((term61 b c d) = (term62 b c d))).
Proof. exact (MK_COMB (@lem3840906 a b c d) (@lem3840907 b c d)). Qed.
Lemma lem3840909 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term59 b c d a) = (term60 b c d)) = (((term64 a b c d) = (term65 a b c d)) = ((term61 b c d) = (term62 b c d))).
Proof. exact (TRANS (@lem3840903 a b c d) (@lem3840908 a b c d)). Qed.
Lemma lem3840910 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = True) : ((term64 a b c d) = (term65 a b c d)) = ((term61 b c d) = (term62 b c d)).
Proof. exact (EQ_MP (@lem3840909 a b c d) (@lem3840900 b c d a h1)). Qed.
Lemma lem3840911 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = True) : ((term61 b c d) = (term62 b c d)) = ((term64 a b c d) = (term65 a b c d)).
Proof. exact (SYM (@lem3840910 b c d a h1)). Qed.
Lemma lem3840912 (b : Prop) (c : Prop) (d : Prop) : (term58 b c d) = (term58 b c d).
Proof. exact (eq_refl (term58 b c d)). Qed.
Lemma lem3840913 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = False) : (term59 b c d a) = (term67 b c d).
Proof. exact (MK_COMB (@lem3840912 b c d) (@lem3840882 a h1)). Qed.
Lemma lem3840914 (b : Prop) (c : Prop) (d : Prop) : (term67 b c d) = ((term68 b c d) = (term69 b c d)).
Proof. exact (eq_refl (term67 b c d)). Qed.
Lemma lem3840915 (b : Prop) (c : Prop) (d : Prop) (a : Prop) : (term63 b c d a) = (term63 b c d a).
Proof. exact (eq_refl (term63 b c d a)). Qed.
Lemma lem3840916 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term59 b c d a) = (term67 b c d)) = ((term59 b c d a) = ((term68 b c d) = (term69 b c d))).
Proof. exact (MK_COMB (@lem3840915 b c d a) (@lem3840914 b c d)). Qed.
Lemma lem3840917 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : (term59 b c d a) = ((term64 a b c d) = (term65 a b c d)).
Proof. exact (eq_refl (term59 b c d a)). Qed.
Lemma lem3840918 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3840919 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : (term63 b c d a) = (term66 a b c d).
Proof. exact (MK_COMB (@lem3840918) (@lem3840917 a b c d)). Qed.
Lemma lem3840920 (b : Prop) (c : Prop) (d : Prop) : ((term68 b c d) = (term69 b c d)) = ((term68 b c d) = (term69 b c d)).
Proof. exact (eq_refl ((term68 b c d) = (term69 b c d))). Qed.
Lemma lem3840921 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term59 b c d a) = ((term68 b c d) = (term69 b c d))) = (((term64 a b c d) = (term65 a b c d)) = ((term68 b c d) = (term69 b c d))).
Proof. exact (MK_COMB (@lem3840919 a b c d) (@lem3840920 b c d)). Qed.
Lemma lem3840922 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term59 b c d a) = (term67 b c d)) = (((term64 a b c d) = (term65 a b c d)) = ((term68 b c d) = (term69 b c d))).
Proof. exact (TRANS (@lem3840916 a b c d) (@lem3840921 a b c d)). Qed.
Lemma lem3840923 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = False) : ((term64 a b c d) = (term65 a b c d)) = ((term68 b c d) = (term69 b c d)).
Proof. exact (EQ_MP (@lem3840922 a b c d) (@lem3840913 b c d a h1)). Qed.
Lemma lem3840924 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = False) : ((term68 b c d) = (term69 b c d)) = ((term64 a b c d) = (term65 a b c d)).
Proof. exact (SYM (@lem3840923 b c d a h1)). Qed.
Lemma lem3840930 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3840931 (b : Prop) (c : Prop) : (term70 b c) = (b /\ c).
Proof. exact (@lem3840930 (b /\ c)). Qed.
Lemma lem3840934 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3840935 (b : Prop) (c : Prop) : (term71 b c) = (term72 b c).
Proof. exact (MK_COMB (@lem3840934) (@lem3840931 b c)). Qed.
Lemma lem3840936 (d : Prop) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem3840937 (b : Prop) (c : Prop) (d : Prop) : (term61 b c d) = (term73 b c d).
Proof. exact (MK_COMB (@lem3840935 b c) (@lem3840936 d)). Qed.
Lemma lem3840940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3840941 (b : Prop) (c : Prop) (d : Prop) : (term74 b c d) = (term75 b c d).
Proof. exact (MK_COMB (@lem3840940) (@lem3840937 b c d)). Qed.
Lemma lem3840943 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3840944 (b : Prop) (c : Prop) (d : Prop) : (term62 b c d) = (term73 b c d).
Proof. exact (@lem3840943 (term73 b c d)). Qed.
Lemma lem3840949 (b : Prop) (c : Prop) (d : Prop) : ((term61 b c d) = (term62 b c d)) = ((term73 b c d) = (term73 b c d)).
Proof. exact (MK_COMB (@lem3840941 b c d) (@lem3840944 b c d)). Qed.
Lemma lem3840951 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3840952 (x : Prop) : (x = x) = True.
Proof. exact (@lem3840951 Prop x). Qed.
Lemma lem3840953 (b : Prop) (c : Prop) (d : Prop) : ((term73 b c d) = (term73 b c d)) = True.
Proof. exact (@lem3840952 (term73 b c d)). Qed.
Lemma lem3840954 (b : Prop) (c : Prop) (d : Prop) : ((term61 b c d) = (term62 b c d)) = True.
Proof. exact (TRANS (@lem3840949 b c d) (@lem3840953 b c d)). Qed.
Lemma lem3840955 (b : Prop) (c : Prop) (d : Prop) : True = ((term61 b c d) = (term62 b c d)).
Proof. exact (SYM (@lem3840954 b c d)). Qed.
Lemma lem3840956 (b : Prop) (c : Prop) (d : Prop) : (term61 b c d) = (term62 b c d).
Proof. exact (EQ_MP (@lem3840955 b c d) (@lem0)). Qed.
Lemma lem3840962 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem3840963 (b : Prop) (c : Prop) : (term76 b c) = False.
Proof. exact (@lem3840962 (b /\ c)). Qed.
Lemma lem3840964 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3840965 (b : Prop) (c : Prop) : (term77 b c) = (imp False).
Proof. exact (MK_COMB (@lem3840964) (@lem3840963 b c)). Qed.
Lemma lem3840966 (d : Prop) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem3840967 (b : Prop) (c : Prop) (d : Prop) : (term68 b c d) = (False -> d).
Proof. exact (MK_COMB (@lem3840965 b c) (@lem3840966 d)). Qed.
Lemma lem3840969 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3840970 (d : Prop) : (False -> d) = True.
Proof. exact (@lem3840969 d). Qed.
Lemma lem3840971 (b : Prop) (c : Prop) (d : Prop) : (term68 b c d) = True.
Proof. exact (TRANS (@lem3840967 b c d) (@lem3840970 d)). Qed.
Lemma lem3840972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3840973 (b : Prop) (c : Prop) (d : Prop) : (term78 b c d) = (@eq Prop True).
Proof. exact (MK_COMB (@lem3840972) (@lem3840971 b c d)). Qed.
Lemma lem3840975 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem3840976 (b : Prop) (c : Prop) (d : Prop) : (term69 b c d) = True.
Proof. exact (@lem3840975 (term73 b c d)). Qed.
Lemma lem3840977 (b : Prop) (c : Prop) (d : Prop) : ((term68 b c d) = (term69 b c d)) = (True = True).
Proof. exact (MK_COMB (@lem3840973 b c d) (@lem3840976 b c d)). Qed.
Lemma lem3840979 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3840980 : (True = True) = True.
Proof. exact (@lem3840979 True). Qed.
Lemma lem3840981 (b : Prop) (c : Prop) (d : Prop) : ((term68 b c d) = (term69 b c d)) = True.
Proof. exact (TRANS (@lem3840977 b c d) (@lem3840980)). Qed.
Lemma lem3840982 (b : Prop) (c : Prop) (d : Prop) : True = ((term68 b c d) = (term69 b c d)).
Proof. exact (SYM (@lem3840981 b c d)). Qed.
Lemma lem3840983 (b : Prop) (c : Prop) (d : Prop) : (term68 b c d) = (term69 b c d).
Proof. exact (EQ_MP (@lem3840982 b c d) (@lem0)). Qed.
Lemma lem3840984 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = False) : (term64 a b c d) = (term65 a b c d).
Proof. exact (EQ_MP (@lem3840924 b c d a h1) (@lem3840983 b c d)). Qed.
Lemma lem3840985 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = True) : (term64 a b c d) = (term65 a b c d).
Proof. exact (EQ_MP (@lem3840911 b c d a h1) (@lem3840956 b c d)). Qed.
Lemma lem3840998 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : (term64 a b c d) = (term65 a b c d).
Proof. exact (or_elim (@lem3840880 a) (fun h0 : a = True => @lem3840985 b c d a h0) (fun h0 : a = False => @lem3840984 b c d a h0)). Qed.
Lemma lem3840999 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term80 A s t).
Proof. exact (@lem3840998 (@FINITE A s) (@FINITE A t) ((@INTER A s t) = (@EMPTY A)) ((term81 A s t) = (term82 A s t))). Qed.
Lemma lem3841010 {A : Type'} (s : A -> Prop) : (term83 A s) = (term84 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3840999 A s t)). Qed.
Lemma lem3841011 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3841012 {A : Type'} (s : A -> Prop) : (term85 A s) = (term86 A s).
Proof. exact (MK_COMB (@lem3841011 A) (@lem3841010 A s)). Qed.
Lemma lem3841017 {A : Type'} : (term87 A) = (term88 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3841012 A s)). Qed.
Lemma lem3841018 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3841019 {A : Type'} : (term89 A) = (term90 A).
Proof. exact (MK_COMB (@lem3841018 A) (@lem3841017 A)). Qed.
Lemma lem3841024 {A : Type'} : (term90 A) = (term89 A).
Proof. exact (SYM (@lem3841019 A)). Qed.
Lemma lem3841030 {A : Type'} (P : Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem3840860 A P Q) (@lem3840859 A P Q)). Qed.
Lemma lem3841031 {A : Type'} (P : Prop) (Q : type686 A) : (term91 A P Q) = (term92 A P Q).
Proof. exact (@lem3841030 (A -> Prop) P Q). Qed.
Lemma lem3841032 {A : Type'} (s : A -> Prop) : (term93 A s) = (term94 A s).
Proof. exact (@lem3841031 A (@FINITE A s) (term95 A s)). Qed.
Lemma lem3841033 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term96 A s t) = (term97 A s t).
Proof. exact (eq_refl (term96 A s t)). Qed.
Lemma lem3841034 {A : Type'} (s : A -> Prop) : (term98 A s) = (term98 A s).
Proof. exact (eq_refl (term98 A s)). Qed.
Lemma lem3841035 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term99 A s t) = (term80 A s t).
Proof. exact (MK_COMB (@lem3841034 A s) (@lem3841033 A s t)). Qed.
Lemma lem3841036 {A : Type'} (s : A -> Prop) : (term100 A s) = (term84 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3841035 A s t)). Qed.
Lemma lem3841037 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3841038 {A : Type'} (s : A -> Prop) : (term93 A s) = (term86 A s).
Proof. exact (MK_COMB (@lem3841037 A) (@lem3841036 A s)). Qed.
Lemma lem3841039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3841040 {A : Type'} (s : A -> Prop) : (term101 A s) = (term102 A s).
Proof. exact (MK_COMB (@lem3841039) (@lem3841038 A s)). Qed.
Lemma lem3841041 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term96 A s t) = (term97 A s t).
Proof. exact (eq_refl (term96 A s t)). Qed.
Lemma lem3841042 {A : Type'} (s : A -> Prop) : (term103 A s) = (term95 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3841041 A s t)). Qed.
Lemma lem3841043 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3841044 {A : Type'} (s : A -> Prop) : (term104 A s) = (term105 A s).
Proof. exact (MK_COMB (@lem3841043 A) (@lem3841042 A s)). Qed.
Lemma lem3841045 {A : Type'} (s : A -> Prop) : (term98 A s) = (term98 A s).
Proof. exact (eq_refl (term98 A s)). Qed.
Lemma lem3841046 {A : Type'} (s : A -> Prop) : (term94 A s) = (term106 A s).
Proof. exact (MK_COMB (@lem3841045 A s) (@lem3841044 A s)). Qed.
Lemma lem3841047 {A : Type'} (s : A -> Prop) : ((term93 A s) = (term94 A s)) = ((term86 A s) = (term106 A s)).
Proof. exact (MK_COMB (@lem3841040 A s) (@lem3841046 A s)). Qed.
Lemma lem3841048 {A : Type'} (s : A -> Prop) : (term86 A s) = (term106 A s).
Proof. exact (EQ_MP (@lem3841047 A s) (@lem3841032 A s)). Qed.
Lemma lem3841083 {A : Type'} : (term88 A) = (term107 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3841048 A s)). Qed.
Lemma lem3841084 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3841085 {A : Type'} : (term90 A) = (term108 A).
Proof. exact (MK_COMB (@lem3841084 A) (@lem3841083 A)). Qed.
Lemma lem3841110 {A : Type'} : (term108 A) = (term90 A).
Proof. exact (SYM (@lem3841085 A)). Qed.
Lemma lem3841112 {A : Type'} (P : type686 A) : term46 A P.
Proof. exact (EQ_MP (@lem3840854 A P) (@lem3840853 A P)). Qed.
Lemma lem3841113 {A : Type'} (P : type686 A) : term46 A P.
Proof. exact (@lem3841112 A P). Qed.
Lemma lem3841114 {A : Type'} : term109 A.
Proof. exact (@lem3841113 A (term110 A)). Qed.
Lemma lem3841115 {A : Type'} : (term111 A) = (term112 A).
Proof. exact (eq_refl (term111 A)). Qed.
Lemma lem3841116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3841117 {A : Type'} : (term113 A) = (term114 A).
Proof. exact (MK_COMB (@lem3841116) (@lem3841115 A)). Qed.
Lemma lem3841118 {A : Type'} (s : A -> Prop) : (term115 A s) = (term105 A s).
Proof. exact (eq_refl (term115 A s)). Qed.
Lemma lem3841119 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3841120 {A : Type'} (s : A -> Prop) : (term116 A s) = (term117 A s).
Proof. exact (MK_COMB (@lem3841119) (@lem3841118 A s)). Qed.
Lemma lem3841121 {A : Type'} (x : A) (s : A -> Prop) : (term118 A x s) = (term118 A x s).
Proof. exact (eq_refl (term118 A x s)). Qed.
Lemma lem3841122 {A : Type'} (x : A) (s : A -> Prop) : (term119 A x s) = (term120 A x s).
Proof. exact (MK_COMB (@lem3841120 A s) (@lem3841121 A x s)). Qed.
Lemma lem3841123 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3841124 {A : Type'} (x : A) (s : A -> Prop) : (term121 A x s) = (term122 A x s).
Proof. exact (MK_COMB (@lem3841123) (@lem3841122 A x s)). Qed.
Lemma lem3841125 {A : Type'} (x : A) (s : A -> Prop) : (term123 A x s) = (term124 A x s).
Proof. exact (eq_refl (term123 A x s)). Qed.
Lemma lem3841126 {A : Type'} (x : A) (s : A -> Prop) : (term125 A x s) = (term126 A x s).
Proof. exact (MK_COMB (@lem3841124 A x s) (@lem3841125 A x s)). Qed.
Lemma lem3841127 {A : Type'} (x : A) : (term127 A x) = (term128 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3841126 A x s)). Qed.
Lemma lem3841128 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3841129 {A : Type'} (x : A) : (term129 A x) = (term130 A x).
Proof. exact (MK_COMB (@lem3841128 A) (@lem3841127 A x)). Qed.
Lemma lem3841130 {A : Type'} : (term131 A) = (term132 A).
Proof. exact (fun_ext (fun x : A => @lem3841129 A x)). Qed.
Lemma lem3841131 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3841132 {A : Type'} : (term133 A) = (term134 A).
Proof. exact (MK_COMB (@lem3841131 A) (@lem3841130 A)). Qed.
Lemma lem3841133 {A : Type'} : (term135 A) = (term136 A).
Proof. exact (MK_COMB (@lem3841117 A) (@lem3841132 A)). Qed.
Lemma lem3841134 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3841135 {A : Type'} : (term137 A) = (term138 A).
Proof. exact (MK_COMB (@lem3841134) (@lem3841133 A)). Qed.
Lemma lem3841136 {A : Type'} (s : A -> Prop) : (term115 A s) = (term105 A s).
Proof. exact (eq_refl (term115 A s)). Qed.
Lemma lem3841137 {A : Type'} (s : A -> Prop) : (term98 A s) = (term98 A s).
Proof. exact (eq_refl (term98 A s)). Qed.
Lemma lem3841138 {A : Type'} (s : A -> Prop) : (term139 A s) = (term106 A s).
Proof. exact (MK_COMB (@lem3841137 A s) (@lem3841136 A s)). Qed.
Lemma lem3841139 {A : Type'} : (term140 A) = (term107 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3841138 A s)). Qed.
Lemma lem3841140 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3841141 {A : Type'} : (term141 A) = (term108 A).
Proof. exact (MK_COMB (@lem3841140 A) (@lem3841139 A)). Qed.
Lemma lem3841142 {A : Type'} : (term109 A) = (term142 A).
Proof. exact (MK_COMB (@lem3841135 A) (@lem3841141 A)). Qed.
Lemma lem3841143 {A : Type'} : term142 A.
Proof. exact (EQ_MP (@lem3841142 A) (@lem3841114 A)). Qed.
Lemma lem3841157 {A : Type'} (s : A -> Prop) : (@INTER A (@EMPTY A) s) = (@EMPTY A).
Proof. exact (EQ_MP (@lem3840820 A s) (@lem3840819 A s)). Qed.
Lemma lem3841158 {A : Type'} (s : A -> Prop) : (@INTER A (@EMPTY A) s) = (@EMPTY A).
Proof. exact (@lem3841157 A s). Qed.
Lemma lem3841159 {A : Type'} (t : A -> Prop) : (@INTER A (@EMPTY A) t) = (@EMPTY A).
Proof. exact (@lem3841158 A t). Qed.
Lemma lem3841160 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem3841161 {A : Type'} (t : A -> Prop) : (term143 A t) = (@eq (A -> Prop) (@EMPTY A)).
Proof. exact (MK_COMB (@lem3841160 A) (@lem3841159 A t)). Qed.
Lemma lem3841162 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem3841163 {A : Type'} (t : A -> Prop) : ((@INTER A (@EMPTY A) t) = (@EMPTY A)) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem3841161 A t) (@lem3841162 A)). Qed.
Lemma lem3841165 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3841166 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem3841165 (A -> Prop) x). Qed.
Lemma lem3841167 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem3841166 A (@EMPTY A)). Qed.
Lemma lem3841168 {A : Type'} (t : A -> Prop) : ((@INTER A (@EMPTY A) t) = (@EMPTY A)) = True.
Proof. exact (TRANS (@lem3841163 A t) (@lem3841167 A)). Qed.
Lemma lem3841169 {A : Type'} (t : A -> Prop) : (term144 A t) = (term144 A t).
Proof. exact (eq_refl (term144 A t)). Qed.
Lemma lem3841170 {A : Type'} (t : A -> Prop) : (term145 A t) = (term146 A t).
Proof. exact (MK_COMB (@lem3841169 A t) (@lem3841168 A t)). Qed.
Lemma lem3841172 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3841173 {A : Type'} (t : A -> Prop) : (term146 A t) = (@FINITE A t).
Proof. exact (@lem3841172 (@FINITE A t)). Qed.
Lemma lem3841174 {A : Type'} (t : A -> Prop) : (term145 A t) = (@FINITE A t).
Proof. exact (TRANS (@lem3841170 A t) (@lem3841173 A t)). Qed.
Lemma lem3841175 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3841176 {A : Type'} (t : A -> Prop) : (term147 A t) = (term98 A t).
Proof. exact (MK_COMB (@lem3841175) (@lem3841174 A t)). Qed.
Lemma lem3841180 {A : Type'} (s : A -> Prop) : (@UNION A (@EMPTY A) s) = s.
Proof. exact (EQ_MP (@lem3840838 A s) (@lem3840837 A s)). Qed.
Lemma lem3841181 {A : Type'} (s : A -> Prop) : (@UNION A (@EMPTY A) s) = s.
Proof. exact (@lem3841180 A s). Qed.
Lemma lem3841182 {A : Type'} (t : A -> Prop) : (@UNION A (@EMPTY A) t) = t.
Proof. exact (@lem3841181 A t). Qed.
Lemma lem3841183 {A : Type'} : (@CARD A) = (@CARD A).
Proof. exact (eq_refl (@CARD A)). Qed.
Lemma lem3841184 {A : Type'} (t : A -> Prop) : (term148 A t) = (@CARD A t).
Proof. exact (MK_COMB (@lem3841183 A) (@lem3841182 A t)). Qed.
Lemma lem3841185 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3841186 {A : Type'} (t : A -> Prop) : (term149 A t) = (term150 A t).
Proof. exact (MK_COMB (@lem3841185) (@lem3841184 A t)). Qed.
Lemma lem3841188 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem3841189 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem3841190 {A : Type'} : (term151 A) = term152.
Proof. exact (MK_COMB (@lem3841189) (@lem3841188 A)). Qed.
Lemma lem3841191 {A : Type'} (t : A -> Prop) : (@CARD A t) = (@CARD A t).
Proof. exact (eq_refl (@CARD A t)). Qed.
Lemma lem3841192 {A : Type'} (t : A -> Prop) : (term153 A t) = (term154 A t).
Proof. exact (MK_COMB (@lem3841190 A) (@lem3841191 A t)). Qed.
Lemma lem3841194 (n : nat) : (term39 n) = n.
Proof. exact (EQ_MP (@lem3840812 n) (@lem3840811 n)). Qed.
Lemma lem3841195 {A : Type'} (t : A -> Prop) : (term154 A t) = (@CARD A t).
Proof. exact (@lem3841194 (@CARD A t)). Qed.
Lemma lem3841196 {A : Type'} (t : A -> Prop) : (term153 A t) = (@CARD A t).
Proof. exact (TRANS (@lem3841192 A t) (@lem3841195 A t)). Qed.
Lemma lem3841197 {A : Type'} (t : A -> Prop) : ((term148 A t) = (term153 A t)) = ((@CARD A t) = (@CARD A t)).
Proof. exact (MK_COMB (@lem3841186 A t) (@lem3841196 A t)). Qed.
Lemma lem3841199 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3841200 (x : nat) : (x = x) = True.
Proof. exact (@lem3841199 nat x). Qed.
Lemma lem3841201 {A : Type'} (t : A -> Prop) : ((@CARD A t) = (@CARD A t)) = True.
Proof. exact (@lem3841200 (@CARD A t)). Qed.
Lemma lem3841202 {A : Type'} (t : A -> Prop) : ((term148 A t) = (term153 A t)) = True.
Proof. exact (TRANS (@lem3841197 A t) (@lem3841201 A t)). Qed.
Lemma lem3841203 {A : Type'} (t : A -> Prop) : (term155 A t) = (term156 A t).
Proof. exact (MK_COMB (@lem3841176 A t) (@lem3841202 A t)). Qed.
Lemma lem3841205 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3841206 {A : Type'} (t : A -> Prop) : (term156 A t) = True.
Proof. exact (@lem3841205 (@FINITE A t)). Qed.
Lemma lem3841207 {A : Type'} (t : A -> Prop) : (term155 A t) = True.
Proof. exact (TRANS (@lem3841203 A t) (@lem3841206 A t)). Qed.
Lemma lem3841208 {A : Type'} : (term157 A) = (term158 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3841207 A t)). Qed.
Lemma lem3841209 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3841210 {A : Type'} : (term112 A) = (term159 A).
Proof. exact (MK_COMB (@lem3841209 A) (@lem3841208 A)). Qed.
Lemma lem3841212 {A : Type'} (t : Prop) : (term160 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3841213 {A : Type'} (t : Prop) : (term161 A t) = t.
Proof. exact (@lem3841212 (A -> Prop) t). Qed.
Lemma lem3841214 {A : Type'} : (term159 A) = True.
Proof. exact (@lem3841213 A True). Qed.
Lemma lem3841215 {A : Type'} : (term112 A) = True.
Proof. exact (TRANS (@lem3841210 A) (@lem3841214 A)). Qed.
Lemma lem3841216 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3841217 {A : Type'} : (term114 A) = (and True).
Proof. exact (MK_COMB (@lem3841216) (@lem3841215 A)). Qed.
Lemma lem3841256 {A : Type'} : (term134 A) = (term134 A).
Proof. exact (eq_refl (term134 A)). Qed.
Lemma lem3841257 {A : Type'} : (term136 A) = (term162 A).
Proof. exact (MK_COMB (@lem3841217 A) (@lem3841256 A)). Qed.
Lemma lem3841259 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3841260 {A : Type'} : (term162 A) = (term134 A).
Proof. exact (@lem3841259 (term134 A)). Qed.
Lemma lem3841299 {A : Type'} : (term136 A) = (term134 A).
Proof. exact (TRANS (@lem3841257 A) (@lem3841260 A)). Qed.
Lemma lem3841300 {A : Type'} : (term134 A) = (term136 A).
Proof. exact (SYM (@lem3841299 A)). Qed.
Lemma lem3841301 {A : Type'} (x : A) (s : A -> Prop) (h1 : term120 A x s) : term120 A x s.
Proof. exact (h1). Qed.
Lemma lem3841302 {A : Type'} (x : A) (s : A -> Prop) (h1 : term118 A x s) : term118 A x s.
Proof. exact (h1). Qed.
Lemma lem3841303 {A : Type'} (s : A -> Prop) (h1 : term105 A s) : term105 A s.
Proof. exact (h1). Qed.
Lemma lem3841304 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3841305 {A : Type'} (x : A) (s : A -> Prop) (h1 : term163 A x s) : term163 A x s.
Proof. exact (h1). Qed.
Lemma lem3841306 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term164 A x s t) : term164 A x s t.
Proof. exact (h1). Qed.
Lemma lem3841307 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : (term165 A x s t) = (@EMPTY A)) : (term165 A x s t) = (@EMPTY A).
Proof. exact (h1). Qed.
Lemma lem3841308 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : @FINITE A t.
Proof. exact (h1). Qed.
Lemma lem3841309 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : (term166 A x s t) = (term167 A x s t)) : (term166 A x s t) = (term167 A x s t).
Proof. exact (h1). Qed.
Lemma lem3841310 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term168 A x s t) = (term168 A x s t).
Proof. exact (eq_refl (term168 A x s t)). Qed.
Lemma lem3841311 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : (term166 A x s t) = (term167 A x s t)) : (term169 A x s t) = (term170 A x s t).
Proof. exact (MK_COMB (@lem3841310 A x s t) (@lem3841309 A x s t h1)). Qed.
Lemma lem3841312 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term170 A x s t) = ((term171 A x s t) = (term172 A x s t)).
Proof. exact (eq_refl (term170 A x s t)). Qed.
Lemma lem3841313 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term173 A x s t) = (term173 A x s t).
Proof. exact (eq_refl (term173 A x s t)). Qed.
Lemma lem3841314 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term169 A x s t) = (term170 A x s t)) = ((term169 A x s t) = ((term171 A x s t) = (term172 A x s t))).
Proof. exact (MK_COMB (@lem3841313 A x s t) (@lem3841312 A x s t)). Qed.
Lemma lem3841315 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term169 A x s t) = ((term174 A x s t) = (term172 A x s t)).
Proof. exact (eq_refl (term169 A x s t)). Qed.
Lemma lem3841316 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3841317 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term173 A x s t) = (term175 A x s t).
Proof. exact (MK_COMB (@lem3841316) (@lem3841315 A x s t)). Qed.
Lemma lem3841318 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term171 A x s t) = (term172 A x s t)) = ((term171 A x s t) = (term172 A x s t)).
Proof. exact (eq_refl ((term171 A x s t) = (term172 A x s t))). Qed.
Lemma lem3841319 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term169 A x s t) = ((term171 A x s t) = (term172 A x s t))) = (((term174 A x s t) = (term172 A x s t)) = ((term171 A x s t) = (term172 A x s t))).
Proof. exact (MK_COMB (@lem3841317 A x s t) (@lem3841318 A x s t)). Qed.
Lemma lem3841320 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term169 A x s t) = (term170 A x s t)) = (((term174 A x s t) = (term172 A x s t)) = ((term171 A x s t) = (term172 A x s t))).
Proof. exact (TRANS (@lem3841314 A x s t) (@lem3841319 A x s t)). Qed.
Lemma lem3841321 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : (term166 A x s t) = (term167 A x s t)) : ((term174 A x s t) = (term172 A x s t)) = ((term171 A x s t) = (term172 A x s t)).
Proof. exact (EQ_MP (@lem3841320 A x s t) (@lem3841311 A x s t h1)). Qed.
Lemma lem3841322 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : (term166 A x s t) = (term167 A x s t)) : ((term171 A x s t) = (term172 A x s t)) = ((term174 A x s t) = (term172 A x s t)).
Proof. exact (SYM (@lem3841321 A x s t h1)). Qed.
Lemma lem3841326 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3841327 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (@lem3841326 A s t). Qed.
Lemma lem3841328 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term166 A x s t) = (term167 A x s t)) = (term176 A x s t).
Proof. exact (@lem3841327 A (term166 A x s t) (term167 A x s t)). Qed.
Lemma lem3841337 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term176 A x s t) = ((term166 A x s t) = (term167 A x s t)).
Proof. exact (SYM (@lem3841328 A x s t)). Qed.
Lemma lem3841345 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term177 A x s t) = (term178 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3841346 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term177 A x s t) = (term178 A s x t).
Proof. exact (@lem3841345 A s x t). Qed.
Lemma lem3841347 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term179 A x' x s t) = (term180 A x s x' t).
Proof. exact (@lem3841346 A (@INSERT A x s) x' t). Qed.
Lemma lem3841351 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3841352 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (@lem3841351 A y x s). Qed.
Lemma lem3841353 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term15 A x' x s) = (term16 A x x' s).
Proof. exact (@lem3841352 A x x' s). Qed.
Lemma lem3841359 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3841360 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3841359 A P x). Qed.
Lemma lem3841361 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3841360 A s x'). Qed.
Lemma lem3841362 {A : Type'} (x' : A) (x : A) : (term181 A x' x) = (term181 A x' x).
Proof. exact (eq_refl (term181 A x' x)). Qed.
Lemma lem3841363 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term16 A x x' s) = (term182 A x s x').
Proof. exact (MK_COMB (@lem3841362 A x' x) (@lem3841361 A s x')). Qed.
Lemma lem3841366 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term15 A x' x s) = (term182 A x s x').
Proof. exact (TRANS (@lem3841353 A x x' s) (@lem3841363 A x s x')). Qed.
Lemma lem3841367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3841368 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term183 A x' x s) = (term184 A x s x').
Proof. exact (MK_COMB (@lem3841367) (@lem3841366 A x s x')). Qed.
Lemma lem3841370 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3841371 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3841370 A P x). Qed.
Lemma lem3841372 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3841371 A t x'). Qed.
Lemma lem3841373 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term180 A x s x' t) = (term185 A x s t x').
Proof. exact (MK_COMB (@lem3841368 A x s x') (@lem3841372 A t x')). Qed.
Lemma lem3841376 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term179 A x' x s t) = (term185 A x s t x').
Proof. exact (TRANS (@lem3841347 A x s x' t) (@lem3841373 A x s t x')). Qed.
Lemma lem3841377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3841378 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term186 A x' x s t) = (term187 A x s t x').
Proof. exact (MK_COMB (@lem3841377) (@lem3841376 A x s t x')). Qed.
Lemma lem3841380 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3841381 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (@lem3841380 A y x s). Qed.
Lemma lem3841382 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) : (term188 A x' x s t) = (term189 A x x' s t).
Proof. exact (@lem3841381 A x x' (@UNION A s t)). Qed.
Lemma lem3841388 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term177 A x s t) = (term178 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3841389 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term177 A x s t) = (term178 A s x t).
Proof. exact (@lem3841388 A s x t). Qed.
Lemma lem3841390 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) : (term177 A x' s t) = (term178 A s x' t).
Proof. exact (@lem3841389 A s x' t). Qed.
Lemma lem3841394 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3841395 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3841394 A P x). Qed.
Lemma lem3841396 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3841395 A s x'). Qed.
Lemma lem3841397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3841398 {A : Type'} (s : A -> Prop) (x' : A) : (term190 A x' s) = (term191 A s x').
Proof. exact (MK_COMB (@lem3841397) (@lem3841396 A s x')). Qed.
Lemma lem3841400 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3841401 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3841400 A P x). Qed.
Lemma lem3841402 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3841401 A t x'). Qed.
Lemma lem3841403 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term178 A s x' t) = (term192 A s t x').
Proof. exact (MK_COMB (@lem3841398 A s x') (@lem3841402 A t x')). Qed.
Lemma lem3841406 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term177 A x' s t) = (term192 A s t x').
Proof. exact (TRANS (@lem3841390 A s x' t) (@lem3841403 A s t x')). Qed.
Lemma lem3841407 {A : Type'} (x' : A) (x : A) : (term181 A x' x) = (term181 A x' x).
Proof. exact (eq_refl (term181 A x' x)). Qed.
Lemma lem3841408 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term189 A x x' s t) = (term193 A x s t x').
Proof. exact (MK_COMB (@lem3841407 A x' x) (@lem3841406 A s t x')). Qed.
Lemma lem3841411 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term188 A x' x s t) = (term193 A x s t x').
Proof. exact (TRANS (@lem3841382 A x x' s t) (@lem3841408 A x s t x')). Qed.
Lemma lem3841412 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term179 A x' x s t) = (term188 A x' x s t)) = ((term185 A x s t x') = (term193 A x s t x')).
Proof. exact (MK_COMB (@lem3841378 A x s t x') (@lem3841411 A x s t x')). Qed.
Lemma lem3841415 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term194 A x s t) = (term195 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3841412 A x s t x')). Qed.
Lemma lem3841416 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3841417 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term176 A x s t) = (term196 A x s t).
Proof. exact (MK_COMB (@lem3841416 A) (@lem3841415 A x s t)). Qed.
Lemma lem3841422 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term196 A x s t) = (term176 A x s t).
Proof. exact (SYM (@lem3841417 A x s t)). Qed.
Lemma lem3841424 (p : Prop) : p = (term197 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3841425 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term196 A x s t) = (term198 A x s t).
Proof. exact (@lem3841424 (term196 A x s t)). Qed.
Lemma lem3841426 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term198 A x s t) = (term196 A x s t).
Proof. exact (SYM (@lem3841425 A x s t)). Qed.
Lemma lem3841427 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term199 A x s t) : term199 A x s t.
Proof. exact (h1). Qed.
Lemma lem3841430 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term198 A x s t) : term198 A x s t.
Proof. exact (h1). Qed.
Lemma lem3841431 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term200 A x s t.
Proof. exact (fun h0 : term198 A x s t => @lem3841430 A x s t h0). Qed.
Lemma lem3841432 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term200 A x s t) : term200 A x s t.
Proof. exact (h1). Qed.
Lemma lem3841433 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term198 A x s t) : term198 A x s t.
Proof. exact (h1). Qed.
Lemma lem3841434 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term198 A x s t) (h2 : term200 A x s t) : term198 A x s t.
Proof. exact (@lem3841432 A x s t h2 (@lem3841433 A x s t h1)). Qed.
Lemma lem3841435 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term198 A x s t) : term201 A x s t.
Proof. exact (fun h0 : term200 A x s t => @lem3841434 A x s t h1 h0). Qed.
Lemma lem3841436 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term200 A x s t) : term200 A x s t.
Proof. exact (h1). Qed.
Lemma lem3841437 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term198 A x s t) (h2 : term200 A x s t) : term198 A x s t.
Proof. exact (@lem3841435 A x s t h1 (@lem3841436 A x s t h2)). Qed.
Lemma lem3841438 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term200 A x s t) : term200 A x s t.
Proof. exact (fun h0 : term198 A x s t => @lem3841437 A x s t h0 h1). Qed.
Lemma lem3841439 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term202 A x s t.
Proof. exact (fun h0 : term200 A x s t => @lem3841438 A x s t h0). Qed.
Lemma lem3841442 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term200 A x s t.
Proof. exact (@lem3841439 A x s t (@lem3841431 A x s t)). Qed.
Lemma lem3841443 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term200 A x s t.
Proof. exact (@lem3841442 A x s t). Qed.
Lemma lem3841457 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3841458 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term198 A x s t) = (term203 A x s t).
Proof. exact (@lem3841457 (term199 A x s t)). Qed.
Lemma lem3841460 (t : Prop) : (term204 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3841461 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term203 A x s t) = (term196 A x s t).
Proof. exact (@lem3841460 (term196 A x s t)). Qed.
Lemma lem3841466 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term198 A x s t) = (term196 A x s t).
Proof. exact (TRANS (@lem3841458 A x s t) (@lem3841461 A x s t)). Qed.
Lemma lem3841475 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term205 A s t) = (term206 A s t).
Proof. exact (fun_ext (fun x : A => @lem3841466 A x s t)). Qed.
Lemma lem3841476 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3841477 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term207 A s t) = (term208 A s t).
Proof. exact (MK_COMB (@lem3841476 A) (@lem3841475 A s t)). Qed.
Lemma lem3841482 {A : Type'} (t : A -> Prop) : (term209 A t) = (term210 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3841477 A s t)). Qed.
Lemma lem3841483 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3841484 {A : Type'} (t : A -> Prop) : (term211 A t) = (term212 A t).
Proof. exact (MK_COMB (@lem3841483 A) (@lem3841482 A t)). Qed.
Lemma lem3841489 {A : Type'} : (term213 A) = (term214 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3841484 A t)). Qed.
Lemma lem3841490 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3841499 {A : Type'} : (term215 A) = (term216 A).
Proof. exact (MK_COMB (@lem3841490 A) (@lem3841489 A)). Qed.
Lemma lem3841520 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term185 A x s t x') = (term193 A x s t x')) = ((term185 A x s t x') = (term193 A x s t x')).
Proof. exact (eq_refl ((term185 A x s t x') = (term193 A x s t x'))). Qed.
Lemma lem3841521 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term195 A x s t) = (term195 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3841520 A x s t x')). Qed.
Lemma lem3841522 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3841523 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term196 A x s t) = (term196 A x s t).
Proof. exact (MK_COMB (@lem3841522 A) (@lem3841521 A x s t)). Qed.
Lemma lem3841524 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term206 A s t) = (term206 A s t).
Proof. exact (fun_ext (fun x : A => @lem3841523 A x s t)). Qed.
Lemma lem3841525 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3841526 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term208 A s t) = (term208 A s t).
Proof. exact (MK_COMB (@lem3841525 A) (@lem3841524 A s t)). Qed.
Lemma lem3841527 {A : Type'} (t : A -> Prop) : (term210 A t) = (term210 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3841526 A s t)). Qed.
Lemma lem3841528 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3841529 {A : Type'} (t : A -> Prop) : (term212 A t) = (term212 A t).
Proof. exact (MK_COMB (@lem3841528 A) (@lem3841527 A t)). Qed.
Lemma lem3841530 {A : Type'} : (term214 A) = (term214 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3841529 A t)). Qed.
Lemma lem3841531 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3841532 {A : Type'} : (term216 A) = (term216 A).
Proof. exact (MK_COMB (@lem3841531 A) (@lem3841530 A)). Qed.
Lemma lem3841567 {A : Type'} : (term215 A) = (term216 A).
Proof. exact (TRANS (@lem3841499 A) (@lem3841532 A)). Qed.
Lemma lem3841568 {A : Type'} : (term216 A) = (term215 A).
Proof. exact (SYM (@lem3841567 A)). Qed.
Lemma lem3841570 (p : Prop) : p = (term197 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3841571 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term185 A x s t x') = (term193 A x s t x')) = (term217 A x s t x').
Proof. exact (@lem3841570 ((term185 A x s t x') = (term193 A x s t x'))). Qed.
Lemma lem3841572 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term217 A x s t x') = ((term185 A x s t x') = (term193 A x s t x')).
Proof. exact (SYM (@lem3841571 A x s t x')). Qed.
Lemma lem3841573 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term218 A x s t x') : term218 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3841582 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term219 A x s x') = (term220 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3841586 {A : Type'} (t : A -> Prop) (x' : A) : (term221 A t x') = (term221 A t x').
Proof. exact (eq_refl (term221 A t x')). Qed.
Lemma lem3841588 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3841589 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term222 A x s x') = (term223 A x s x').
Proof. exact (MK_COMB (@lem3841588) (@lem3841582 A x s x')). Qed.
Lemma lem3841590 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term224 A x s t x') = (term225 A x s t x').
Proof. exact (MK_COMB (@lem3841589 A x s x') (@lem3841586 A t x')). Qed.
Lemma lem3841591 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term226 A x s t x') = (term224 A x s t x').
Proof. exact (@lem17160 (term182 A x s x') (t x')). Qed.
Lemma lem3841592 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term226 A x s t x') = (term225 A x s t x').
Proof. exact (TRANS (@lem3841591 A x s t x') (@lem3841590 A x s t x')). Qed.
Lemma lem3841606 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term227 A s t x') = (term228 A s t x').
Proof. exact (@lem17160 (s x') (t x')). Qed.
Lemma lem3841611 {A : Type'} (x' : A) (x : A) : (term229 A x' x) = (term229 A x' x).
Proof. exact (eq_refl (term229 A x' x)). Qed.
Lemma lem3841612 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term230 A x s t x') = (term231 A x s t x').
Proof. exact (MK_COMB (@lem3841611 A x' x) (@lem3841606 A s t x')). Qed.
Lemma lem3841613 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term232 A x s t x') = (term230 A x s t x').
Proof. exact (@lem17160 (x' = x) (term192 A s t x')). Qed.
Lemma lem3841614 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term232 A x s t x') = (term231 A x s t x').
Proof. exact (TRANS (@lem3841613 A x s t x') (@lem3841612 A x s t x')). Qed.
Lemma lem3841617 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term193 A x s t x') = (term193 A x s t x').
Proof. exact (eq_refl (term193 A x s t x')). Qed.
Lemma lem3841618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3841619 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term233 A x s t x') = (term234 A x s t x').
Proof. exact (MK_COMB (@lem3841618) (@lem3841592 A x s t x')). Qed.
Lemma lem3841620 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term235 A x s t x') = (term236 A x s t x').
Proof. exact (MK_COMB (@lem3841619 A x s t x') (@lem3841617 A x s t x')). Qed.
Lemma lem3841622 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term237 A x s t x') = (term237 A x s t x').
Proof. exact (eq_refl (term237 A x s t x')). Qed.
Lemma lem3841623 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term238 A x s t x') = (term239 A x s t x').
Proof. exact (MK_COMB (@lem3841622 A x s t x') (@lem3841614 A x s t x')). Qed.
Lemma lem3841624 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3841625 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term240 A x s t x') = (term241 A x s t x').
Proof. exact (MK_COMB (@lem3841624) (@lem3841623 A x s t x')). Qed.
Lemma lem3841626 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term242 A x s t x') = (term243 A x s t x').
Proof. exact (MK_COMB (@lem3841625 A x s t x') (@lem3841620 A x s t x')). Qed.
Lemma lem3841627 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term218 A x s t x') = (term242 A x s t x').
Proof. exact (@lem17646 (term185 A x s t x') (term193 A x s t x')). Qed.
Lemma lem3841632 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term218 A x s t x') = (term243 A x s t x').
Proof. exact (TRANS (@lem3841627 A x s t x') (@lem3841626 A x s t x')). Qed.
Lemma lem3841723 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term218 A x s t x') : term243 A x s t x'.
Proof. exact (EQ_MP (@lem3841632 A x s t x') (@lem3841573 A x s t x' h1)). Qed.
Lemma lem3841724 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term239 A x s t x') : term239 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3841725 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term236 A x s t x') : term236 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3841726 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term239 A x s t x') : term231 A x s t x'.
Proof. exact (proj2 (@lem3841724 A x s t x' h1)). Qed.
Lemma lem3841727 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term239 A x s t x') : term185 A x s t x'.
Proof. exact (proj1 (@lem3841724 A x s t x' h1)). Qed.
Lemma lem3841728 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term239 A x s t x') : term228 A s t x'.
Proof. exact (proj2 (@lem3841726 A x s t x' h1)). Qed.
Lemma lem3841732 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term182 A x s x') : term182 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3841736 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term236 A x s t x') : term193 A x s t x'.
Proof. exact (proj2 (@lem3841725 A x s t x' h1)). Qed.
Lemma lem3841737 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term236 A x s t x') : term225 A x s t x'.
Proof. exact (proj1 (@lem3841725 A x s t x' h1)). Qed.
Lemma lem3841739 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term236 A x s t x') : term220 A x s x'.
Proof. exact (proj1 (@lem3841737 A x s t x' h1)). Qed.
Lemma lem3841743 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term192 A s t x') : term192 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3841761 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3841777 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3841793 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3841809 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3841825 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3841841 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3841843 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term239 A x s t x') : term244 A x' x.
Proof. exact (proj1 (@lem3841726 A x s t x' h1)). Qed.
Lemma lem3841849 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3841853 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term239 A x s t x') : term221 A s x'.
Proof. exact (proj1 (@lem3841728 A x s t x' h1)). Qed.
Lemma lem3841857 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3841863 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term239 A x s t x') : term221 A t x'.
Proof. exact (proj2 (@lem3841728 A x s t x' h1)). Qed.
Lemma lem3841865 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3841869 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term236 A x s t x') : term244 A x' x.
Proof. exact (proj1 (@lem3841739 A x s t x' h1)). Qed.
Lemma lem3841873 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3841879 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term236 A x s t x') : term221 A s x'.
Proof. exact (proj2 (@lem3841739 A x s t x' h1)). Qed.
Lemma lem3841881 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3841883 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term236 A x s t x') : term221 A t x'.
Proof. exact (proj2 (@lem3841737 A x s t x' h1)). Qed.
Lemma lem3841889 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3841904 {A : Type'} (x : A) : (term245 A x) = (term245 A x).
Proof. exact (eq_refl (term245 A x)). Qed.
Lemma lem3841905 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term246 A x x') = (term247 A x).
Proof. exact (MK_COMB (@lem3841904 A x) (@lem3841849 A x' x h1)). Qed.
Lemma lem3841906 {A : Type'} (x : A) : (term247 A x) = (term248 A x).
Proof. exact (eq_refl (term247 A x)). Qed.
Lemma lem3841907 {A : Type'} (x : A) (x' : A) : (term249 A x x') = (term249 A x x').
Proof. exact (eq_refl (term249 A x x')). Qed.
Lemma lem3841908 {A : Type'} (x' : A) (x : A) : ((term246 A x x') = (term247 A x)) = ((term246 A x x') = (term248 A x)).
Proof. exact (MK_COMB (@lem3841907 A x x') (@lem3841906 A x)). Qed.
Lemma lem3841909 {A : Type'} (x' : A) (x : A) : (term246 A x x') = (term244 A x' x).
Proof. exact (eq_refl (term246 A x x')). Qed.
Lemma lem3841910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3841911 {A : Type'} (x' : A) (x : A) : (term249 A x x') = (term250 A x' x).
Proof. exact (MK_COMB (@lem3841910) (@lem3841909 A x' x)). Qed.
Lemma lem3841912 {A : Type'} (x : A) : (term248 A x) = (term248 A x).
Proof. exact (eq_refl (term248 A x)). Qed.
Lemma lem3841913 {A : Type'} (x' : A) (x : A) : ((term246 A x x') = (term248 A x)) = ((term244 A x' x) = (term248 A x)).
Proof. exact (MK_COMB (@lem3841911 A x' x) (@lem3841912 A x)). Qed.
Lemma lem3841914 {A : Type'} (x' : A) (x : A) : ((term246 A x x') = (term247 A x)) = ((term244 A x' x) = (term248 A x)).
Proof. exact (TRANS (@lem3841908 A x' x) (@lem3841913 A x' x)). Qed.
Lemma lem3841915 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term244 A x' x) = (term248 A x).
Proof. exact (EQ_MP (@lem3841914 A x' x) (@lem3841905 A x' x h1)). Qed.
Lemma lem3841916 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term239 A x s t x') (h2 : x' = x) : term248 A x.
Proof. exact (EQ_MP (@lem3841915 A x' x h2) (@lem3841843 A x s t x' h1)). Qed.
Lemma lem3841970 {A : Type'} (x : A) : (term245 A x) = (term245 A x).
Proof. exact (eq_refl (term245 A x)). Qed.
Lemma lem3841971 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term246 A x x') = (term247 A x).
Proof. exact (MK_COMB (@lem3841970 A x) (@lem3841873 A x' x h1)). Qed.
Lemma lem3841972 {A : Type'} (x : A) : (term247 A x) = (term248 A x).
Proof. exact (eq_refl (term247 A x)). Qed.
Lemma lem3841973 {A : Type'} (x : A) (x' : A) : (term249 A x x') = (term249 A x x').
Proof. exact (eq_refl (term249 A x x')). Qed.
Lemma lem3841974 {A : Type'} (x' : A) (x : A) : ((term246 A x x') = (term247 A x)) = ((term246 A x x') = (term248 A x)).
Proof. exact (MK_COMB (@lem3841973 A x x') (@lem3841972 A x)). Qed.
Lemma lem3841975 {A : Type'} (x' : A) (x : A) : (term246 A x x') = (term244 A x' x).
Proof. exact (eq_refl (term246 A x x')). Qed.
Lemma lem3841976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3841977 {A : Type'} (x' : A) (x : A) : (term249 A x x') = (term250 A x' x).
Proof. exact (MK_COMB (@lem3841976) (@lem3841975 A x' x)). Qed.
Lemma lem3841978 {A : Type'} (x : A) : (term248 A x) = (term248 A x).
Proof. exact (eq_refl (term248 A x)). Qed.
Lemma lem3841979 {A : Type'} (x' : A) (x : A) : ((term246 A x x') = (term248 A x)) = ((term244 A x' x) = (term248 A x)).
Proof. exact (MK_COMB (@lem3841977 A x' x) (@lem3841978 A x)). Qed.
Lemma lem3841980 {A : Type'} (x' : A) (x : A) : ((term246 A x x') = (term247 A x)) = ((term244 A x' x) = (term248 A x)).
Proof. exact (TRANS (@lem3841974 A x' x) (@lem3841979 A x' x)). Qed.
Lemma lem3841981 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term244 A x' x) = (term248 A x).
Proof. exact (EQ_MP (@lem3841980 A x' x) (@lem3841971 A x' x h1)). Qed.
Lemma lem3841982 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term236 A x s t x') (h2 : x' = x) : term248 A x.
Proof. exact (EQ_MP (@lem3841981 A x' x h2) (@lem3841869 A x s t x' h1)). Qed.
Lemma lem3842023 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3842024 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3842023 A x). Qed.
Lemma lem3842025 {A : Type'} (x : A) : term251 A x.
Proof. exact (fun h0 : term248 A x => @lem3842024 A x). Qed.
Lemma lem3842027 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3842028 {A : Type'} (x : A) : (term251 A x) = (x = x).
Proof. exact (@lem3842027 (x = x)). Qed.
Lemma lem3842029 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3842028 A x) (@lem3842025 A x)). Qed.
Lemma lem3842032 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3842034 {A : Type'} (x : A) : (term248 A x) = (term253 A x).
Proof. exact (@lem3842032 (x = x)). Qed.
Lemma lem3842037 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term239 A x s t x') (h2 : x' = x) : term253 A x.
Proof. exact (EQ_MP (@lem3842034 A x) (@lem3841916 A s t x' x h1 h2)). Qed.
Lemma lem3842040 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term239 A x s t x') (h2 : x' = x) : False.
Proof. exact (@lem3842037 A s t x' x h1 h2 (@lem3842029 A x)). Qed.
Lemma lem3842041 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term239 A x s t x') (h2 : x' = x) : term254.
Proof. exact (fun h0 : ~ False => @lem3842040 A s t x' x h1 h2). Qed.
Lemma lem3842043 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3842044 : term254 = False.
Proof. exact (@lem3842043 False). Qed.
Lemma lem3842073 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3842074 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term255 A s x'.
Proof. exact (fun h0 : term221 A s x' => @lem3842073 A s x' h1). Qed.
Lemma lem3842076 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3842077 {A : Type'} (s : A -> Prop) (x' : A) : (term255 A s x') = (s x').
Proof. exact (@lem3842076 (s x')). Qed.
Lemma lem3842078 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3842077 A s x') (@lem3842074 A s x' h1)). Qed.
Lemma lem3842081 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3842083 {A : Type'} (s : A -> Prop) (x' : A) : (term221 A s x') = (term256 A s x').
Proof. exact (@lem3842081 (s x')). Qed.
Lemma lem3842086 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term239 A x s t x') : term256 A s x'.
Proof. exact (EQ_MP (@lem3842083 A s x') (@lem3841853 A x s t x' h1)). Qed.
Lemma lem3842089 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term239 A x s t x') : False.
Proof. exact (@lem3842086 A x s t x' h2 (@lem3842078 A s x' h1)). Qed.
Lemma lem3842090 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term239 A x s t x') : term254.
Proof. exact (fun h0 : ~ False => @lem3842089 A x s t x' h1 h2). Qed.
Lemma lem3842092 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3842093 : term254 = False.
Proof. exact (@lem3842092 False). Qed.
Lemma lem3842094 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term239 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842093) (@lem3842090 A x s t x' h1 h2)). Qed.
Lemma lem3842122 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3842123 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term255 A t x'.
Proof. exact (fun h0 : term221 A t x' => @lem3842122 A t x' h1). Qed.
Lemma lem3842125 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3842126 {A : Type'} (t : A -> Prop) (x' : A) : (term255 A t x') = (t x').
Proof. exact (@lem3842125 (t x')). Qed.
Lemma lem3842127 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3842126 A t x') (@lem3842123 A t x' h1)). Qed.
Lemma lem3842130 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3842132 {A : Type'} (t : A -> Prop) (x' : A) : (term221 A t x') = (term256 A t x').
Proof. exact (@lem3842130 (t x')). Qed.
Lemma lem3842135 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term239 A x s t x') : term256 A t x'.
Proof. exact (EQ_MP (@lem3842132 A t x') (@lem3841863 A x s t x' h1)). Qed.
Lemma lem3842138 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term239 A x s t x') : False.
Proof. exact (@lem3842135 A x s t x' h2 (@lem3842127 A t x' h1)). Qed.
Lemma lem3842139 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term239 A x s t x') : term254.
Proof. exact (fun h0 : ~ False => @lem3842138 A x s t x' h1 h2). Qed.
Lemma lem3842141 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3842142 : term254 = False.
Proof. exact (@lem3842141 False). Qed.
Lemma lem3842143 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term239 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842142) (@lem3842139 A x s t x' h1 h2)). Qed.
Lemma lem3842171 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3842172 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3842171 A x). Qed.
Lemma lem3842173 {A : Type'} (x : A) : term251 A x.
Proof. exact (fun h0 : term248 A x => @lem3842172 A x). Qed.
Lemma lem3842175 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3842176 {A : Type'} (x : A) : (term251 A x) = (x = x).
Proof. exact (@lem3842175 (x = x)). Qed.
Lemma lem3842177 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3842176 A x) (@lem3842173 A x)). Qed.
Lemma lem3842180 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3842182 {A : Type'} (x : A) : (term248 A x) = (term253 A x).
Proof. exact (@lem3842180 (x = x)). Qed.
Lemma lem3842185 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term236 A x s t x') (h2 : x' = x) : term253 A x.
Proof. exact (EQ_MP (@lem3842182 A x) (@lem3841982 A s t x' x h1 h2)). Qed.
Lemma lem3842188 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term236 A x s t x') (h2 : x' = x) : False.
Proof. exact (@lem3842185 A s t x' x h1 h2 (@lem3842177 A x)). Qed.
Lemma lem3842189 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term236 A x s t x') (h2 : x' = x) : term254.
Proof. exact (fun h0 : ~ False => @lem3842188 A s t x' x h1 h2). Qed.
Lemma lem3842191 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3842192 : term254 = False.
Proof. exact (@lem3842191 False). Qed.
Lemma lem3842221 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3842222 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term255 A s x'.
Proof. exact (fun h0 : term221 A s x' => @lem3842221 A s x' h1). Qed.
Lemma lem3842224 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3842225 {A : Type'} (s : A -> Prop) (x' : A) : (term255 A s x') = (s x').
Proof. exact (@lem3842224 (s x')). Qed.
Lemma lem3842226 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3842225 A s x') (@lem3842222 A s x' h1)). Qed.
Lemma lem3842229 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3842231 {A : Type'} (s : A -> Prop) (x' : A) : (term221 A s x') = (term256 A s x').
Proof. exact (@lem3842229 (s x')). Qed.
Lemma lem3842234 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term236 A x s t x') : term256 A s x'.
Proof. exact (EQ_MP (@lem3842231 A s x') (@lem3841879 A x s t x' h1)). Qed.
Lemma lem3842237 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term236 A x s t x') : False.
Proof. exact (@lem3842234 A x s t x' h2 (@lem3842226 A s x' h1)). Qed.
Lemma lem3842238 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term236 A x s t x') : term254.
Proof. exact (fun h0 : ~ False => @lem3842237 A x s t x' h1 h2). Qed.
Lemma lem3842240 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3842241 : term254 = False.
Proof. exact (@lem3842240 False). Qed.
Lemma lem3842242 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term236 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842241) (@lem3842238 A x s t x' h1 h2)). Qed.
Lemma lem3842270 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3842271 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term255 A t x'.
Proof. exact (fun h0 : term221 A t x' => @lem3842270 A t x' h1). Qed.
Lemma lem3842273 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3842274 {A : Type'} (t : A -> Prop) (x' : A) : (term255 A t x') = (t x').
Proof. exact (@lem3842273 (t x')). Qed.
Lemma lem3842275 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3842274 A t x') (@lem3842271 A t x' h1)). Qed.
Lemma lem3842278 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3842280 {A : Type'} (t : A -> Prop) (x' : A) : (term221 A t x') = (term256 A t x').
Proof. exact (@lem3842278 (t x')). Qed.
Lemma lem3842283 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term236 A x s t x') : term256 A t x'.
Proof. exact (EQ_MP (@lem3842280 A t x') (@lem3841883 A x s t x' h1)). Qed.
Lemma lem3842286 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term236 A x s t x') : False.
Proof. exact (@lem3842283 A x s t x' h2 (@lem3842275 A t x' h1)). Qed.
Lemma lem3842287 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term236 A x s t x') : term254.
Proof. exact (fun h0 : ~ False => @lem3842286 A x s t x' h1 h2). Qed.
Lemma lem3842289 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3842290 : term254 = False.
Proof. exact (@lem3842289 False). Qed.
Lemma lem3842291 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term236 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842290) (@lem3842287 A x s t x' h1 h2)). Qed.
Lemma lem3842292 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term236 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3842192) (@lem3842189 A s t x' x h1 h2)). Qed.
Lemma lem3842293 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term239 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3842044) (@lem3842041 A s t x' x h1 h2)). Qed.
Lemma lem3842294 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term236 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3842291 A x s t x' h1 h2) (fun h3 : False => @lem3841889 A t x' h1)). Qed.
Lemma lem3842295 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term236 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842294 A x s t x' h1 h2) (@lem3841889 A t x' h1)). Qed.
Lemma lem3842296 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term236 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3842242 A x s t x' h1 h2) (fun h3 : False => @lem3841881 A s x' h1)). Qed.
Lemma lem3842297 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term236 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842296 A x s t x' h1 h2) (@lem3841881 A s x' h1)). Qed.
Lemma lem3842298 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term236 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3842292 A s t x' x h1 h2) (fun h3 : False => @lem3841873 A x' x h2)). Qed.
Lemma lem3842299 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term236 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3842298 A s t x' x h1 h2) (@lem3841873 A x' x h2)). Qed.
Lemma lem3842300 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term239 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3842143 A x s t x' h1 h2) (fun h3 : False => @lem3841865 A t x' h1)). Qed.
Lemma lem3842301 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term239 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842300 A x s t x' h1 h2) (@lem3841865 A t x' h1)). Qed.
Lemma lem3842302 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term239 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3842094 A x s t x' h1 h2) (fun h3 : False => @lem3841857 A s x' h1)). Qed.
Lemma lem3842303 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term239 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842302 A x s t x' h1 h2) (@lem3841857 A s x' h1)). Qed.
Lemma lem3842304 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term239 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3842293 A s t x' x h1 h2) (fun h3 : False => @lem3841849 A x' x h2)). Qed.
Lemma lem3842305 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term239 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3842304 A s t x' x h1 h2) (@lem3841849 A x' x h2)). Qed.
Lemma lem3842306 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term236 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3842295 A x s t x' h1 h2) (fun h3 : False => @lem3841841 A t x' h1)). Qed.
Lemma lem3842307 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term236 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842306 A x s t x' h1 h2) (@lem3841841 A t x' h1)). Qed.
Lemma lem3842308 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term236 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3842297 A x s t x' h1 h2) (fun h3 : False => @lem3841825 A s x' h1)). Qed.
Lemma lem3842309 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term236 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842308 A x s t x' h1 h2) (@lem3841825 A s x' h1)). Qed.
Lemma lem3842310 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term236 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3842299 A s t x' x h1 h2) (fun h3 : False => @lem3841809 A x' x h2)). Qed.
Lemma lem3842311 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term236 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3842310 A s t x' x h1 h2) (@lem3841809 A x' x h2)). Qed.
Lemma lem3842312 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term239 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3842301 A x s t x' h1 h2) (fun h3 : False => @lem3841793 A t x' h1)). Qed.
Lemma lem3842313 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term239 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842312 A x s t x' h1 h2) (@lem3841793 A t x' h1)). Qed.
Lemma lem3842314 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term239 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3842303 A x s t x' h1 h2) (fun h3 : False => @lem3841777 A s x' h1)). Qed.
Lemma lem3842315 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term239 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842314 A x s t x' h1 h2) (@lem3841777 A s x' h1)). Qed.
Lemma lem3842316 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term239 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3842305 A s t x' x h1 h2) (fun h3 : False => @lem3841761 A x' x h2)). Qed.
Lemma lem3842317 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term239 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3842316 A s t x' x h1 h2) (@lem3841761 A x' x h2)). Qed.
Lemma lem3842318 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term236 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3842307 A x s t x' h1 h2) (fun h3 : False => @lem3841841 A t x' h1)). Qed.
Lemma lem3842319 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term236 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842318 A x s t x' h1 h2) (@lem3841841 A t x' h1)). Qed.
Lemma lem3842320 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term236 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3842309 A x s t x' h1 h2) (fun h3 : False => @lem3841825 A s x' h1)). Qed.
Lemma lem3842321 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term236 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842320 A x s t x' h1 h2) (@lem3841825 A s x' h1)). Qed.
Lemma lem3842322 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term236 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3842311 A s t x' x h1 h2) (fun h3 : False => @lem3841809 A x' x h2)). Qed.
Lemma lem3842323 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term236 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3842322 A s t x' x h1 h2) (@lem3841809 A x' x h2)). Qed.
Lemma lem3842324 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term239 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3842313 A x s t x' h1 h2) (fun h3 : False => @lem3841793 A t x' h1)). Qed.
Lemma lem3842325 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term239 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842324 A x s t x' h1 h2) (@lem3841793 A t x' h1)). Qed.
Lemma lem3842326 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term239 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3842315 A x s t x' h1 h2) (fun h3 : False => @lem3841777 A s x' h1)). Qed.
Lemma lem3842327 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term239 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842326 A x s t x' h1 h2) (@lem3841777 A s x' h1)). Qed.
Lemma lem3842328 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term239 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3842317 A s t x' x h1 h2) (fun h3 : False => @lem3841761 A x' x h2)). Qed.
Lemma lem3842329 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term239 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3842328 A s t x' x h1 h2) (@lem3841761 A x' x h2)). Qed.
Lemma lem3842330 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term236 A x s t x') (h2 : term192 A s t x') : False.
Proof. exact (or_elim (@lem3841743 A s t x' h2) (fun h0 : s x' => @lem3842321 A x s t x' h0 h1) (fun h0 : t x' => @lem3842319 A x s t x' h0 h1)). Qed.
Lemma lem3842331 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term236 A x s t x') : False.
Proof. exact (or_elim (@lem3841736 A x s t x' h1) (fun h0 : x' = x => @lem3842323 A s t x' x h1 h0) (fun h0 : term192 A s t x' => @lem3842330 A x s t x' h1 h0)). Qed.
Lemma lem3842332 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term239 A x s t x') (h2 : term182 A x s x') : False.
Proof. exact (or_elim (@lem3841732 A x s x' h2) (fun h0 : x' = x => @lem3842329 A s t x' x h1 h0) (fun h0 : s x' => @lem3842327 A x s t x' h0 h1)). Qed.
Lemma lem3842333 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term239 A x s t x') : False.
Proof. exact (or_elim (@lem3841727 A x s t x' h1) (fun h0 : term182 A x s x' => @lem3842332 A t x s x' h1 h0) (fun h0 : t x' => @lem3842325 A x s t x' h0 h1)). Qed.
Lemma lem3842334 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term218 A x s t x') : False.
Proof. exact (or_elim (@lem3841723 A x s t x' h1) (fun h0 : term239 A x s t x' => @lem3842333 A x s t x' h0) (fun h0 : term236 A x s t x' => @lem3842331 A x s t x' h0)). Qed.
Lemma lem3842335 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term218 A x s t x') : (term218 A x s t x') = False.
Proof. exact (prop_ext (fun h2 : term218 A x s t x' => @lem3842334 A x s t x' h1) (fun h2 : False => @lem3841573 A x s t x' h1)). Qed.
Lemma lem3842336 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term218 A x s t x') : False.
Proof. exact (EQ_MP (@lem3842335 A x s t x' h1) (@lem3841573 A x s t x' h1)). Qed.
Lemma lem3842337 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : term217 A x s t x'.
Proof. exact (fun h0 : term218 A x s t x' => @lem3842336 A x s t x' h0). Qed.
Lemma lem3842338 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term185 A x s t x') = (term193 A x s t x').
Proof. exact (EQ_MP (@lem3841572 A x s t x') (@lem3842337 A x s t x')). Qed.
Lemma lem3842343 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term196 A x s t.
Proof. exact (fun x' : A => @lem3842338 A x s t x'). Qed.
Lemma lem3842348 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term208 A s t.
Proof. exact (fun x : A => @lem3842343 A x s t). Qed.
Lemma lem3842353 {A : Type'} (t : A -> Prop) : term212 A t.
Proof. exact (fun s : A -> Prop => @lem3842348 A s t). Qed.
Lemma lem3842358 {A : Type'} : term216 A.
Proof. exact (fun t : A -> Prop => @lem3842353 A t). Qed.
Lemma lem3842359 {A : Type'} : term215 A.
Proof. exact (EQ_MP (@lem3841568 A) (@lem3842358 A)). Qed.
Lemma lem3842360 {A : Type'} (t : A -> Prop) : term257 A t.
Proof. exact (@lem3842359 A t). Qed.
Lemma lem3842361 {A : Type'} (t : A -> Prop) : (term257 A t) = (term211 A t).
Proof. exact (eq_refl (term257 A t)). Qed.
Lemma lem3842362 {A : Type'} (t : A -> Prop) : term211 A t.
Proof. exact (EQ_MP (@lem3842361 A t) (@lem3842360 A t)). Qed.
Lemma lem3842363 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term258 A t s.
Proof. exact (@lem3842362 A t s). Qed.
Lemma lem3842364 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term258 A t s) = (term207 A s t).
Proof. exact (eq_refl (term258 A t s)). Qed.
Lemma lem3842365 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term207 A s t.
Proof. exact (EQ_MP (@lem3842364 A s t) (@lem3842363 A t s)). Qed.
Lemma lem3842366 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term259 A s t x.
Proof. exact (@lem3842365 A s t x). Qed.
Lemma lem3842367 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term259 A s t x) = (term198 A x s t).
Proof. exact (eq_refl (term259 A s t x)). Qed.
Lemma lem3842368 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term198 A x s t.
Proof. exact (EQ_MP (@lem3842367 A x s t) (@lem3842366 A s t x)). Qed.
Lemma lem3842370 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term198 A x s t.
Proof. exact (@lem3841443 A x s t (@lem3842368 A x s t)). Qed.
Lemma lem3842371 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term199 A x s t) : False.
Proof. exact (@lem3842370 A x s t (@lem3841427 A x s t h1)). Qed.
Lemma lem3842372 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term199 A x s t) : (term199 A x s t) = False.
Proof. exact (prop_ext (fun h2 : term199 A x s t => @lem3842371 A x s t h1) (fun h2 : False => @lem3841427 A x s t h1)). Qed.
Lemma lem3842373 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term199 A x s t) : False.
Proof. exact (EQ_MP (@lem3842372 A x s t h1) (@lem3841427 A x s t h1)). Qed.
Lemma lem3842374 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term198 A x s t.
Proof. exact (fun h0 : term199 A x s t => @lem3842373 A x s t h0). Qed.
Lemma lem3842375 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term196 A x s t.
Proof. exact (EQ_MP (@lem3841426 A x s t) (@lem3842374 A x s t)). Qed.
Lemma lem3842376 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term176 A x s t.
Proof. exact (EQ_MP (@lem3841422 A x s t) (@lem3842375 A x s t)). Qed.
Lemma lem3842377 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term166 A x s t) = (term167 A x s t).
Proof. exact (EQ_MP (@lem3841337 A x s t) (@lem3842376 A x s t)). Qed.
Lemma lem3842378 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term260 A t s) : term260 A t s.
Proof. exact (h1). Qed.
Lemma lem3842380 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term34 A s t) : term34 A s t.
Proof. exact (h1). Qed.
Lemma lem3842388 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3842395 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3842388 A s) (@lem3841304 A s h1)). Qed.
Lemma lem3842396 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term261 A s t) = (term261 A s t).
Proof. exact (eq_refl (term261 A s t)). Qed.
Lemma lem3842397 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term260 A t s) = (term262 A s t).
Proof. exact (MK_COMB (@lem3842396 A s t) (@lem3842395 A s h1)). Qed.
Lemma lem3842399 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3842400 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term262 A s t) = (term34 A s t).
Proof. exact (@lem3842399 (term34 A s t)). Qed.
Lemma lem3842401 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term260 A t s) = (term34 A s t).
Proof. exact (TRANS (@lem3842397 A t s h1) (@lem3842400 A s t)). Qed.
Lemma lem3842402 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term34 A s t) = (term260 A t s).
Proof. exact (SYM (@lem3842401 A t s h1)). Qed.
Lemma lem3842404 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term32 A s t.
Proof. exact (EQ_MP (@lem3840778 A s t) (@lem3840777 A s t)). Qed.
Lemma lem3842405 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term32 A s t.
Proof. exact (@lem3842404 A s t). Qed.
Lemma lem3842413 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3842415 {A : Type'} (t : A -> Prop) : (@FINITE A t) = ((@FINITE A t) = True).
Proof. exact (@lem7 (@FINITE A t)). Qed.
Lemma lem3842420 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3842413 A s) (@lem3841304 A s h1)). Qed.
Lemma lem3842421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3842422 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term144 A s) = (and True).
Proof. exact (MK_COMB (@lem3842421) (@lem3842420 A s h1)). Qed.
Lemma lem3842424 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem3842415 A t) (@lem3841308 A t h1)). Qed.
Lemma lem3842425 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : (term33 A s t) = (True /\ True).
Proof. exact (MK_COMB (@lem3842422 A s h1) (@lem3842424 A t h2)). Qed.
Lemma lem3842427 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3842428 : (True /\ True) = True.
Proof. exact (@lem3842427 True). Qed.
Lemma lem3842429 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : (term33 A s t) = True.
Proof. exact (TRANS (@lem3842425 A s t h1 h2) (@lem3842428)). Qed.
Lemma lem3842430 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : True = (term33 A s t).
Proof. exact (SYM (@lem3842429 A s t h1 h2)). Qed.
Lemma lem3842431 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : term33 A s t.
Proof. exact (EQ_MP (@lem3842430 A s t h1 h2) (@lem0)). Qed.
Lemma lem3842432 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : term34 A s t.
Proof. exact (@lem3842405 A s t (@lem3842431 A s t h1 h2)). Qed.
Lemma lem3842433 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A s) (h2 : @FINITE A t) : term260 A t s.
Proof. exact (EQ_MP (@lem3842402 A t s h1) (@lem3842432 A s t h1 h2)). Qed.
Lemma lem3842439 {A : Type'} (x : A) (s : A -> Prop) : term263 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem3842441 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem3842445 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = ((term34 A s t) = True).
Proof. exact (@lem7 (term34 A s t)). Qed.
Lemma lem3842452 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term34 A s t) : (term34 A s t) = True.
Proof. exact (EQ_MP (@lem3842445 A s t) (@lem3842380 A s t h1)). Qed.
Lemma lem3842453 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3842454 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term34 A s t) : (term264 A s t) = (imp True).
Proof. exact (MK_COMB (@lem3842453) (@lem3842452 A s t h1)). Qed.
Lemma lem3842457 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term171 A x s t) = (term265 A x s t)) = ((term171 A x s t) = (term265 A x s t)).
Proof. exact (eq_refl ((term171 A x s t) = (term265 A x s t))). Qed.
Lemma lem3842458 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term34 A s t) : (term25 A x s t) = (term266 A x s t).
Proof. exact (MK_COMB (@lem3842454 A s t h1) (@lem3842457 A x s t)). Qed.
Lemma lem3842460 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3842461 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term266 A x s t) = ((term171 A x s t) = (term265 A x s t)).
Proof. exact (@lem3842460 ((term171 A x s t) = (term265 A x s t))). Qed.
Lemma lem3842464 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term34 A s t) : (term25 A x s t) = ((term171 A x s t) = (term265 A x s t)).
Proof. exact (TRANS (@lem3842458 A x s t h1) (@lem3842461 A x s t)). Qed.
Lemma lem3842465 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3842466 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term34 A s t) : (term267 A x s t) = (term268 A x s t).
Proof. exact (MK_COMB (@lem3842465) (@lem3842464 A x s t h1)). Qed.
Lemma lem3842472 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem3842441 A s) (@lem3841304 A s h1)). Qed.
Lemma lem3842473 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3842474 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term98 A s) = (imp True).
Proof. exact (MK_COMB (@lem3842473) (@lem3842472 A s h1)). Qed.
Lemma lem3842478 {A : Type'} (x : A) (s : A -> Prop) (h1 : term163 A x s) : (@IN A x s) = False.
Proof. exact (@lem3842439 A x s (@lem3841305 A x s h1)). Qed.
Lemma lem3842479 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem3842480 {A : Type'} (x : A) (s : A -> Prop) (h1 : term163 A x s) : (term269 A x s) = (@COND nat False).
Proof. exact (MK_COMB (@lem3842479) (@lem3842478 A x s h1)). Qed.
Lemma lem3842481 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (eq_refl (@CARD A s)). Qed.
Lemma lem3842482 {A : Type'} (x : A) (s : A -> Prop) (h1 : term163 A x s) : (term270 A x s) = (term271 A s).
Proof. exact (MK_COMB (@lem3842480 A x s h1) (@lem3842481 A s)). Qed.
Lemma lem3842483 {A : Type'} (s : A -> Prop) : (term272 A s) = (term272 A s).
Proof. exact (eq_refl (term272 A s)). Qed.
Lemma lem3842484 {A : Type'} (x : A) (s : A -> Prop) (h1 : term163 A x s) : (term273 A x s) = (term274 A s).
Proof. exact (MK_COMB (@lem3842482 A x s h1) (@lem3842483 A s)). Qed.
Lemma lem3842486 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3842487 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem3842486 nat t1 t2). Qed.
Lemma lem3842488 {A : Type'} (s : A -> Prop) : (term274 A s) = (term272 A s).
Proof. exact (@lem3842487 (@CARD A s) (term272 A s)). Qed.
Lemma lem3842489 {A : Type'} (x : A) (s : A -> Prop) (h1 : term163 A x s) : (term273 A x s) = (term272 A s).
Proof. exact (TRANS (@lem3842484 A x s h1) (@lem3842488 A s)). Qed.
Lemma lem3842490 {A : Type'} (x : A) (s : A -> Prop) : (term275 A x s) = (term275 A x s).
Proof. exact (eq_refl (term275 A x s)). Qed.
Lemma lem3842491 {A : Type'} (x : A) (s : A -> Prop) (h1 : term163 A x s) : ((term276 A x s) = (term273 A x s)) = ((term276 A x s) = (term272 A s)).
Proof. exact (MK_COMB (@lem3842490 A x s) (@lem3842489 A x s h1)). Qed.
Lemma lem3842494 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term163 A x s) : (term27 A x s) = (term277 A x s).
Proof. exact (MK_COMB (@lem3842474 A s h1) (@lem3842491 A x s h2)). Qed.
Lemma lem3842496 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3842497 {A : Type'} (x : A) (s : A -> Prop) : (term277 A x s) = ((term276 A x s) = (term272 A s)).
Proof. exact (@lem3842496 ((term276 A x s) = (term272 A s))). Qed.
Lemma lem3842500 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term163 A x s) : (term27 A x s) = ((term276 A x s) = (term272 A s)).
Proof. exact (TRANS (@lem3842494 A x s h1 h2) (@lem3842497 A x s)). Qed.
Lemma lem3842501 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3842502 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term163 A x s) : (term278 A x s) = (term279 A x s).
Proof. exact (MK_COMB (@lem3842501) (@lem3842500 A x s h1 h2)). Qed.
Lemma lem3842505 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term171 A x s t) = (term172 A x s t)) = ((term171 A x s t) = (term172 A x s t)).
Proof. exact (eq_refl ((term171 A x s t) = (term172 A x s t))). Qed.
Lemma lem3842506 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term163 A x s) : (term280 A x s t) = (term281 A x s t).
Proof. exact (MK_COMB (@lem3842502 A x s h1 h2) (@lem3842505 A x s t)). Qed.
Lemma lem3842511 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term34 A s t) (h3 : term163 A x s) : (term282 A x s t) = (term283 A x s t).
Proof. exact (MK_COMB (@lem3842466 A x s t h2) (@lem3842506 A t x s h1 h3)). Qed.
Lemma lem3842516 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term34 A s t) (h3 : term163 A x s) : (term283 A x s t) = (term282 A x s t).
Proof. exact (SYM (@lem3842511 A t x s h1 h2 h3)). Qed.
Lemma lem3842535 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : (term171 A x s t) = (term265 A x s t)) : (term171 A x s t) = (term265 A x s t).
Proof. exact (h1). Qed.
Lemma lem3842536 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3842537 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : (term171 A x s t) = (term265 A x s t)) : (term284 A x s t) = (term285 A x s t).
Proof. exact (MK_COMB (@lem3842536) (@lem3842535 A x s t h1)). Qed.
Lemma lem3842539 {A : Type'} (x : A) (s : A -> Prop) (h1 : (term276 A x s) = (term272 A s)) : (term276 A x s) = (term272 A s).
Proof. exact (h1). Qed.
Lemma lem3842540 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem3842541 {A : Type'} (x : A) (s : A -> Prop) (h1 : (term276 A x s) = (term272 A s)) : (term286 A x s) = (term287 A s).
Proof. exact (MK_COMB (@lem3842540) (@lem3842539 A x s h1)). Qed.
Lemma lem3842542 {A : Type'} (t : A -> Prop) : (@CARD A t) = (@CARD A t).
Proof. exact (eq_refl (@CARD A t)). Qed.
Lemma lem3842543 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : (term276 A x s) = (term272 A s)) : (term172 A x s t) = (term288 A s t).
Proof. exact (MK_COMB (@lem3842541 A x s h1) (@lem3842542 A t)). Qed.
Lemma lem3842544 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : (term276 A x s) = (term272 A s)) (h2 : (term171 A x s t) = (term265 A x s t)) : ((term171 A x s t) = (term172 A x s t)) = ((term265 A x s t) = (term288 A s t)).
Proof. exact (MK_COMB (@lem3842537 A x s t h2) (@lem3842543 A t x s h1)). Qed.
Lemma lem3842547 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : (term276 A x s) = (term272 A s)) (h2 : (term171 A x s t) = (term265 A x s t)) : ((term265 A x s t) = (term288 A s t)) = ((term171 A x s t) = (term172 A x s t)).
Proof. exact (SYM (@lem3842544 A x s t h1 h2)). Qed.
Lemma lem3842548 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term289 A x s t) : term289 A x s t.
Proof. exact (h1). Qed.
Lemma lem3842549 {A : Type'} (s : A -> Prop) : term290 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem3842550 {A : Type'} (s : A -> Prop) : (term290 A s) = (term291 A s).
Proof. exact (eq_refl (term290 A s)). Qed.
Lemma lem3842551 {A : Type'} (s : A -> Prop) : term291 A s.
Proof. exact (EQ_MP (@lem3842550 A s) (@lem3842549 A s)). Qed.
Lemma lem3842552 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term292 A s t.
Proof. exact (@lem3842551 A s t). Qed.
Lemma lem3842553 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term292 A s t) = (term293 A s t).
Proof. exact (eq_refl (term292 A s t)). Qed.
Lemma lem3842554 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term293 A s t.
Proof. exact (EQ_MP (@lem3842553 A s t) (@lem3842552 A s t)). Qed.
Lemma lem3842555 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term294 A s t x.
Proof. exact (@lem3842554 A s t x). Qed.
Lemma lem3842556 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term294 A s t x) = ((term177 A x s t) = (term178 A s x t)).
Proof. exact (eq_refl (term294 A s t x)). Qed.
Lemma lem3842563 {A : Type'} (x : A) (s : A -> Prop) : term263 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem3842572 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term177 A x s t) = (term178 A s x t).
Proof. exact (EQ_MP (@lem3842556 A s x t) (@lem3842555 A s t x)). Qed.
Lemma lem3842573 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term177 A x s t) = (term178 A s x t).
Proof. exact (@lem3842572 A s x t). Qed.
Lemma lem3842577 {A : Type'} (x : A) (s : A -> Prop) (h1 : term163 A x s) : (@IN A x s) = False.
Proof. exact (@lem3842563 A x s (@lem3841305 A x s h1)). Qed.
Lemma lem3842578 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3842579 {A : Type'} (x : A) (s : A -> Prop) (h1 : term163 A x s) : (term190 A x s) = (or False).
Proof. exact (MK_COMB (@lem3842578) (@lem3842577 A x s h1)). Qed.
Lemma lem3842580 {A : Type'} (x : A) (t : A -> Prop) : (@IN A x t) = (@IN A x t).
Proof. exact (eq_refl (@IN A x t)). Qed.
Lemma lem3842581 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term163 A x s) : (term178 A s x t) = (term295 A x t).
Proof. exact (MK_COMB (@lem3842579 A x s h1) (@lem3842580 A x t)). Qed.
Lemma lem3842583 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem3842584 {A : Type'} (x : A) (t : A -> Prop) : (term295 A x t) = (@IN A x t).
Proof. exact (@lem3842583 (@IN A x t)). Qed.
Lemma lem3842585 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term163 A x s) : (term178 A s x t) = (@IN A x t).
Proof. exact (TRANS (@lem3842581 A t x s h1) (@lem3842584 A x t)). Qed.
Lemma lem3842586 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term163 A x s) : (term177 A x s t) = (@IN A x t).
Proof. exact (TRANS (@lem3842573 A s x t) (@lem3842585 A t x s h1)). Qed.
Lemma lem3842587 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3842588 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term163 A x s) : (term289 A x s t) = (term163 A x t).
Proof. exact (MK_COMB (@lem3842587) (@lem3842586 A t x s h1)). Qed.
Lemma lem3842589 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term163 A x s) : (term163 A x t) = (term289 A x s t).
Proof. exact (SYM (@lem3842588 A t x s h1)). Qed.
Lemma lem3842597 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (EQ_MP (@lem3840739 A s t) (@lem3840738 A s t)). Qed.
Lemma lem3842598 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (@lem3842597 A s t). Qed.
Lemma lem3842599 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term165 A x s t) = (@EMPTY A)) = (term296 A x s t).
Proof. exact (@lem3842598 A (term165 A x s t) (@EMPTY A)). Qed.
Lemma lem3842609 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (EQ_MP (@lem3840724 A s x t) (@lem3840723 A s t x)). Qed.
Lemma lem3842610 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (@lem3842609 A s x t). Qed.
Lemma lem3842611 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term297 A x' x s t) = (term298 A x s x' t).
Proof. exact (@lem3842610 A (@INSERT A x s) x' t). Qed.
Lemma lem3842615 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (EQ_MP (@lem3840733 A y x s) (@lem3840732 A y x s)). Qed.
Lemma lem3842616 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (@lem3842615 A y x s). Qed.
Lemma lem3842617 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term15 A x' x s) = (term16 A x x' s).
Proof. exact (@lem3842616 A x x' s). Qed.
Lemma lem3842624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3842625 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term299 A x' x s) = (term300 A x x' s).
Proof. exact (MK_COMB (@lem3842624) (@lem3842617 A x x' s)). Qed.
Lemma lem3842626 {A : Type'} (x' : A) (t : A -> Prop) : (@IN A x' t) = (@IN A x' t).
Proof. exact (eq_refl (@IN A x' t)). Qed.
Lemma lem3842627 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term298 A x s x' t) = (term301 A x s x' t).
Proof. exact (MK_COMB (@lem3842625 A x x' s) (@lem3842626 A x' t)). Qed.
Lemma lem3842630 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term297 A x' x s t) = (term301 A x s x' t).
Proof. exact (TRANS (@lem3842611 A x s x' t) (@lem3842627 A x s x' t)). Qed.
Lemma lem3842631 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3842632 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term302 A x' x s t) = (term303 A x s x' t).
Proof. exact (MK_COMB (@lem3842631) (@lem3842630 A x s x' t)). Qed.
Lemma lem3842634 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3840715 A x (@lem3840714 A x)). Qed.
Lemma lem3842635 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3842634 A x). Qed.
Lemma lem3842636 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem3842635 A x'). Qed.
Lemma lem3842637 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : ((term297 A x' x s t) = (@IN A x' (@EMPTY A))) = ((term301 A x s x' t) = False).
Proof. exact (MK_COMB (@lem3842632 A x s x' t) (@lem3842636 A x')). Qed.
Lemma lem3842639 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3842640 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : ((term301 A x s x' t) = False) = (term304 A x s x' t).
Proof. exact (@lem3842639 (term301 A x s x' t)). Qed.
Lemma lem3842649 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : ((term297 A x' x s t) = (@IN A x' (@EMPTY A))) = (term304 A x s x' t).
Proof. exact (TRANS (@lem3842637 A x s x' t) (@lem3842640 A x s x' t)). Qed.
Lemma lem3842650 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term305 A x s t) = (term306 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3842649 A x s x' t)). Qed.
Lemma lem3842651 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3842652 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term296 A x s t) = (term307 A x s t).
Proof. exact (MK_COMB (@lem3842651 A) (@lem3842650 A x s t)). Qed.
Lemma lem3842657 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term165 A x s t) = (@EMPTY A)) = (term307 A x s t).
Proof. exact (TRANS (@lem3842599 A x s t) (@lem3842652 A x s t)). Qed.
Lemma lem3842658 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3842659 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term308 A x s t) = (term309 A x s t).
Proof. exact (MK_COMB (@lem3842658) (@lem3842657 A x s t)). Qed.
Lemma lem3842660 {A : Type'} (x : A) (t : A -> Prop) : (term163 A x t) = (term163 A x t).
Proof. exact (eq_refl (term163 A x t)). Qed.
Lemma lem3842661 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term310 A s x t) = (term311 A s x t).
Proof. exact (MK_COMB (@lem3842659 A x s t) (@lem3842660 A x t)). Qed.
Lemma lem3842664 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term311 A s x t) = (term310 A s x t).
Proof. exact (SYM (@lem3842661 A s x t)). Qed.
Lemma lem3842666 (p : Prop) : p = (term197 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3842667 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term311 A s x t) = (term312 A s x t).
Proof. exact (@lem3842666 (term311 A s x t)). Qed.
Lemma lem3842668 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term312 A s x t) = (term311 A s x t).
Proof. exact (SYM (@lem3842667 A s x t)). Qed.
Lemma lem3842669 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term313 A s x t) : term313 A s x t.
Proof. exact (h1). Qed.
Lemma lem3842672 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term312 A s x t) : term312 A s x t.
Proof. exact (h1). Qed.
Lemma lem3842673 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : term314 A s x t.
Proof. exact (fun h0 : term312 A s x t => @lem3842672 A s x t h0). Qed.
Lemma lem3842674 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term314 A s x t) : term314 A s x t.
Proof. exact (h1). Qed.
Lemma lem3842675 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term312 A s x t) : term312 A s x t.
Proof. exact (h1). Qed.
Lemma lem3842676 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term312 A s x t) (h2 : term314 A s x t) : term312 A s x t.
Proof. exact (@lem3842674 A s x t h2 (@lem3842675 A s x t h1)). Qed.
Lemma lem3842677 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term312 A s x t) : term315 A s x t.
Proof. exact (fun h0 : term314 A s x t => @lem3842676 A s x t h1 h0). Qed.
Lemma lem3842678 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term314 A s x t) : term314 A s x t.
Proof. exact (h1). Qed.
Lemma lem3842679 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term312 A s x t) (h2 : term314 A s x t) : term312 A s x t.
Proof. exact (@lem3842677 A s x t h1 (@lem3842678 A s x t h2)). Qed.
Lemma lem3842680 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term314 A s x t) : term314 A s x t.
Proof. exact (fun h0 : term312 A s x t => @lem3842679 A s x t h0 h1). Qed.
Lemma lem3842681 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : term316 A s x t.
Proof. exact (fun h0 : term314 A s x t => @lem3842680 A s x t h0). Qed.
Lemma lem3842684 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : term314 A s x t.
Proof. exact (@lem3842681 A s x t (@lem3842673 A s x t)). Qed.
Lemma lem3842685 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : term314 A s x t.
Proof. exact (@lem3842684 A s x t). Qed.
Lemma lem3842699 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3842700 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term312 A s x t) = (term317 A s x t).
Proof. exact (@lem3842699 (term313 A s x t)). Qed.
Lemma lem3842702 (t : Prop) : (term204 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3842703 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term317 A s x t) = (term311 A s x t).
Proof. exact (@lem3842702 (term311 A s x t)). Qed.
Lemma lem3842706 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term312 A s x t) = (term311 A s x t).
Proof. exact (TRANS (@lem3842700 A s x t) (@lem3842703 A s x t)). Qed.
Lemma lem3842715 {A : Type'} (x : A) (t : A -> Prop) : (term318 A x t) = (term319 A x t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3842706 A s x t)). Qed.
Lemma lem3842716 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3842717 {A : Type'} (x : A) (t : A -> Prop) : (term320 A x t) = (term321 A x t).
Proof. exact (MK_COMB (@lem3842716 A) (@lem3842715 A x t)). Qed.
Lemma lem3842722 {A : Type'} (t : A -> Prop) : (term322 A t) = (term323 A t).
Proof. exact (fun_ext (fun x : A => @lem3842717 A x t)). Qed.
Lemma lem3842723 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3842724 {A : Type'} (t : A -> Prop) : (term324 A t) = (term325 A t).
Proof. exact (MK_COMB (@lem3842723 A) (@lem3842722 A t)). Qed.
Lemma lem3842729 {A : Type'} : (term326 A) = (term327 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3842724 A t)). Qed.
Lemma lem3842730 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3842739 {A : Type'} : (term328 A) = (term329 A).
Proof. exact (MK_COMB (@lem3842730 A) (@lem3842729 A)). Qed.
Lemma lem3842742 {A : Type'} (x : A) (t : A -> Prop) : (term163 A x t) = (term163 A x t).
Proof. exact (eq_refl (term163 A x t)). Qed.
Lemma lem3842753 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term304 A x s x' t) = (term304 A x s x' t).
Proof. exact (eq_refl (term304 A x s x' t)). Qed.
Lemma lem3842754 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term306 A x s t) = (term306 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3842753 A x s x' t)). Qed.
Lemma lem3842755 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3842756 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term307 A x s t) = (term307 A x s t).
Proof. exact (MK_COMB (@lem3842755 A) (@lem3842754 A x s t)). Qed.
Lemma lem3842757 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3842758 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term309 A x s t) = (term309 A x s t).
Proof. exact (MK_COMB (@lem3842757) (@lem3842756 A x s t)). Qed.
Lemma lem3842759 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term311 A s x t) = (term311 A s x t).
Proof. exact (MK_COMB (@lem3842758 A x s t) (@lem3842742 A x t)). Qed.
Lemma lem3842760 {A : Type'} (x : A) (t : A -> Prop) : (term319 A x t) = (term319 A x t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3842759 A s x t)). Qed.
Lemma lem3842761 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3842762 {A : Type'} (x : A) (t : A -> Prop) : (term321 A x t) = (term321 A x t).
Proof. exact (MK_COMB (@lem3842761 A) (@lem3842760 A x t)). Qed.
Lemma lem3842763 {A : Type'} (t : A -> Prop) : (term323 A t) = (term323 A t).
Proof. exact (fun_ext (fun x : A => @lem3842762 A x t)). Qed.
Lemma lem3842764 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3842765 {A : Type'} (t : A -> Prop) : (term325 A t) = (term325 A t).
Proof. exact (MK_COMB (@lem3842764 A) (@lem3842763 A t)). Qed.
Lemma lem3842766 {A : Type'} : (term327 A) = (term327 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3842765 A t)). Qed.
Lemma lem3842767 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3842768 {A : Type'} : (term329 A) = (term329 A).
Proof. exact (MK_COMB (@lem3842767 A) (@lem3842766 A)). Qed.
Lemma lem3842801 {A : Type'} : (term328 A) = (term329 A).
Proof. exact (TRANS (@lem3842739 A) (@lem3842768 A)). Qed.
Lemma lem3842802 {A : Type'} : (term329 A) = (term328 A).
Proof. exact (SYM (@lem3842801 A)). Qed.
Lemma lem3842803 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term307 A x s t) : term307 A x s t.
Proof. exact (h1). Qed.
Lemma lem3842811 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term330 A x x' s) = (term331 A x x' s).
Proof. exact (@lem17160 (x' = x) (@IN A x' s)). Qed.
Lemma lem3842812 {A : Type'} (x' : A) (t : A -> Prop) : (term163 A x' t) = (term163 A x' t).
Proof. exact (eq_refl (term163 A x' t)). Qed.
Lemma lem3842813 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3842814 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term332 A x x' s) = (term333 A x x' s).
Proof. exact (MK_COMB (@lem3842813) (@lem3842811 A x x' s)). Qed.
Lemma lem3842815 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term334 A x s x' t) = (term335 A x s x' t).
Proof. exact (MK_COMB (@lem3842814 A x x' s) (@lem3842812 A x' t)). Qed.
Lemma lem3842816 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term304 A x s x' t) = (term334 A x s x' t).
Proof. exact (@lem17045 (term16 A x x' s) (@IN A x' t)). Qed.
Lemma lem3842817 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term304 A x s x' t) = (term335 A x s x' t).
Proof. exact (TRANS (@lem3842816 A x s x' t) (@lem3842815 A x s x' t)). Qed.
Lemma lem3842818 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term306 A x s t) = (term336 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3842817 A x s x' t)). Qed.
Lemma lem3842819 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3842872 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term307 A x s t) = (term337 A x s t).
Proof. exact (MK_COMB (@lem3842819 A) (@lem3842818 A x s t)). Qed.
Lemma lem3842873 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term307 A x s t) : term337 A x s t.
Proof. exact (EQ_MP (@lem3842872 A x s t) (@lem3842803 A x s t h1)). Qed.
Lemma lem3842879 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem3842906 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term335 A x s x' t) = (term335 A x s x' t).
Proof. exact (eq_refl (term335 A x s x' t)). Qed.
Lemma lem3842907 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term336 A x s t) = (term336 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3842906 A x s x' t)). Qed.
Lemma lem3842908 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3842909 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term337 A x s t) = (term337 A x s t).
Proof. exact (MK_COMB (@lem3842908 A) (@lem3842907 A x s t)). Qed.
Lemma lem3842910 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term307 A x s t) : term337 A x s t.
Proof. exact (EQ_MP (@lem3842909 A x s t) (@lem3842873 A x s t h1)). Qed.
Lemma lem3842916 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem3842934 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term335 A x s x' t) = (term338 A x s x' t).
Proof. exact (@lem19699 (term244 A x' x) (term163 A x' s) (term163 A x' t)). Qed.
Lemma lem3842935 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term336 A x s t) = (term339 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3842934 A x s x' t)). Qed.
Lemma lem3842936 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3842938 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term337 A x s t) = (term340 A x s t).
Proof. exact (MK_COMB (@lem3842936 A) (@lem3842935 A x s t)). Qed.
Lemma lem3842939 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term307 A x s t) : term340 A x s t.
Proof. exact (EQ_MP (@lem3842938 A x s t) (@lem3842910 A x s t h1)). Qed.
Lemma lem3842943 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem3842944 {A : Type'} (_44590 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term307 A x s t) : term341 A x s t _44590.
Proof. exact (@lem3842939 A x s t h1 _44590). Qed.
Lemma lem3842945 {A : Type'} (x : A) (s : A -> Prop) (_44590 : A) (t : A -> Prop) : (term341 A x s t _44590) = (term338 A x s _44590 t).
Proof. exact (eq_refl (term341 A x s t _44590)). Qed.
Lemma lem3842946 {A : Type'} (_44590 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term307 A x s t) : term338 A x s _44590 t.
Proof. exact (EQ_MP (@lem3842945 A x s _44590 t) (@lem3842944 A _44590 x s t h1)). Qed.
Lemma lem3842950 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem3842956 {A : Type'} (_44590 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term307 A x s t) : term342 A x _44590 t.
Proof. exact (proj1 (@lem3842946 A _44590 x s t h1)). Qed.
Lemma lem3842987 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3842988 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3842987 A x). Qed.
Lemma lem3842989 {A : Type'} (x : A) : term251 A x.
Proof. exact (fun h0 : term248 A x => @lem3842988 A x). Qed.
Lemma lem3842991 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3842992 {A : Type'} (x : A) : (term251 A x) = (x = x).
Proof. exact (@lem3842991 (x = x)). Qed.
Lemma lem3842993 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3842992 A x) (@lem3842989 A x)). Qed.
Lemma lem3842995 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem3842996 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : term343 A x t.
Proof. exact (fun h0 : term163 A x t => @lem3842995 A x t h1). Qed.
Lemma lem3842998 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3842999 {A : Type'} (x : A) (t : A -> Prop) : (term343 A x t) = (@IN A x t).
Proof. exact (@lem3842998 (@IN A x t)). Qed.
Lemma lem3843000 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (EQ_MP (@lem3842999 A x t) (@lem3842996 A x t h1)). Qed.
Lemma lem3843002 (a : Prop) (b : Prop) : (term344 a b) = (term345 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3843003 {A : Type'} (x : A) (_44590 : A) (t : A -> Prop) : (term342 A x _44590 t) = (term346 A x _44590 t).
Proof. exact (@lem3843002 (_44590 = x) (@IN A _44590 t)). Qed.
Lemma lem3843005 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3843006 {A : Type'} (x : A) (_44590 : A) (t : A -> Prop) : (term346 A x _44590 t) = (term347 A x _44590 t).
Proof. exact (@lem3843005 (term348 A x _44590 t)). Qed.
Lemma lem3843007 {A : Type'} (x : A) (_44590 : A) (t : A -> Prop) : (term342 A x _44590 t) = (term347 A x _44590 t).
Proof. exact (TRANS (@lem3843003 A x _44590 t) (@lem3843006 A x _44590 t)). Qed.
Lemma lem3843009 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : term349 A x t.
Proof. exact (conj (@lem3842993 A x) (@lem3843000 A x t h1)). Qed.
Lemma lem3843011 {A : Type'} (_44590 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term307 A x s t) : term347 A x _44590 t.
Proof. exact (EQ_MP (@lem3843007 A x _44590 t) (@lem3842956 A _44590 x s t h1)). Qed.
Lemma lem3843012 {A : Type'} (_44590 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term307 A x s t) : term347 A x _44590 t.
Proof. exact (@lem3843011 A _44590 x s t h1). Qed.
Lemma lem3843013 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term307 A x s t) : term350 A x t.
Proof. exact (@lem3843012 A x x s t h1). Qed.
Lemma lem3843016 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term307 A x s t) (h2 : @IN A x t) : False.
Proof. exact (@lem3843013 A x s t h1 (@lem3843009 A x t h2)). Qed.
Lemma lem3843017 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term307 A x s t) (h2 : @IN A x t) : term254.
Proof. exact (fun h0 : ~ False => @lem3843016 A s x t h1 h2). Qed.
Lemma lem3843019 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3843020 : term254 = False.
Proof. exact (@lem3843019 False). Qed.
Lemma lem3843021 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term307 A x s t) (h2 : @IN A x t) : False.
Proof. exact (EQ_MP (@lem3843020) (@lem3843017 A s x t h1 h2)). Qed.
Lemma lem3843022 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term307 A x s t) (h2 : @IN A x t) : (@IN A x t) = False.
Proof. exact (prop_ext (fun h3 : @IN A x t => @lem3843021 A s x t h1 h2) (fun h3 : False => @lem3842950 A x t h2)). Qed.
Lemma lem3843023 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term307 A x s t) (h2 : @IN A x t) : False.
Proof. exact (EQ_MP (@lem3843022 A s x t h1 h2) (@lem3842950 A x t h2)). Qed.
Lemma lem3843024 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term307 A x s t) (h2 : @IN A x t) : (@IN A x t) = False.
Proof. exact (prop_ext (fun h3 : @IN A x t => @lem3843023 A s x t h1 h2) (fun h3 : False => @lem3842943 A x t h2)). Qed.
Lemma lem3843025 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term307 A x s t) (h2 : @IN A x t) : False.
Proof. exact (EQ_MP (@lem3843024 A s x t h1 h2) (@lem3842943 A x t h2)). Qed.
Lemma lem3843026 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term307 A x s t) (h2 : @IN A x t) : (@IN A x t) = False.
Proof. exact (prop_ext (fun h3 : @IN A x t => @lem3843025 A s x t h1 h2) (fun h3 : False => @lem3842943 A x t h2)). Qed.
Lemma lem3843027 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term307 A x s t) (h2 : @IN A x t) : False.
Proof. exact (EQ_MP (@lem3843026 A s x t h1 h2) (@lem3842943 A x t h2)). Qed.
Lemma lem3843028 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term307 A x s t) (h2 : @IN A x t) : (@IN A x t) = False.
Proof. exact (prop_ext (fun h3 : @IN A x t => @lem3843027 A s x t h1 h2) (fun h3 : False => @lem3842916 A x t h2)). Qed.
Lemma lem3843029 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term307 A x s t) (h2 : @IN A x t) : False.
Proof. exact (EQ_MP (@lem3843028 A s x t h1 h2) (@lem3842916 A x t h2)). Qed.
Lemma lem3843030 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term307 A x s t) (h2 : @IN A x t) : (@IN A x t) = False.
Proof. exact (prop_ext (fun h3 : @IN A x t => @lem3843029 A s x t h1 h2) (fun h3 : False => @lem3842879 A x t h2)). Qed.
Lemma lem3843031 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term307 A x s t) (h2 : @IN A x t) : False.
Proof. exact (EQ_MP (@lem3843030 A s x t h1 h2) (@lem3842879 A x t h2)). Qed.
Lemma lem3843032 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term307 A x s t) : term351 A x t.
Proof. exact (fun h0 : @IN A x t => @lem3843031 A s x t h1 h0). Qed.
Lemma lem3843033 {A : Type'} (x : A) (t : A -> Prop) : (term351 A x t) = (term163 A x t).
Proof. exact (@lem69 (@IN A x t)). Qed.
Lemma lem3843034 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term307 A x s t) : term163 A x t.
Proof. exact (EQ_MP (@lem3843033 A x t) (@lem3843032 A x s t h1)). Qed.
Lemma lem3843035 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : term311 A s x t.
Proof. exact (fun h0 : term307 A x s t => @lem3843034 A x s t h0). Qed.
Lemma lem3843040 {A : Type'} (x : A) (t : A -> Prop) : term321 A x t.
Proof. exact (fun s : A -> Prop => @lem3843035 A s x t). Qed.
Lemma lem3843045 {A : Type'} (t : A -> Prop) : term325 A t.
Proof. exact (fun x : A => @lem3843040 A x t). Qed.
Lemma lem3843050 {A : Type'} : term329 A.
Proof. exact (fun t : A -> Prop => @lem3843045 A t). Qed.
Lemma lem3843051 {A : Type'} : term328 A.
Proof. exact (EQ_MP (@lem3842802 A) (@lem3843050 A)). Qed.
Lemma lem3843052 {A : Type'} (t : A -> Prop) : term352 A t.
Proof. exact (@lem3843051 A t). Qed.
Lemma lem3843053 {A : Type'} (t : A -> Prop) : (term352 A t) = (term324 A t).
Proof. exact (eq_refl (term352 A t)). Qed.
Lemma lem3843054 {A : Type'} (t : A -> Prop) : term324 A t.
Proof. exact (EQ_MP (@lem3843053 A t) (@lem3843052 A t)). Qed.
Lemma lem3843055 {A : Type'} (t : A -> Prop) (x : A) : term353 A t x.
Proof. exact (@lem3843054 A t x). Qed.
Lemma lem3843056 {A : Type'} (x : A) (t : A -> Prop) : (term353 A t x) = (term320 A x t).
Proof. exact (eq_refl (term353 A t x)). Qed.
Lemma lem3843057 {A : Type'} (x : A) (t : A -> Prop) : term320 A x t.
Proof. exact (EQ_MP (@lem3843056 A x t) (@lem3843055 A t x)). Qed.
Lemma lem3843058 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : term354 A x t s.
Proof. exact (@lem3843057 A x t s). Qed.
Lemma lem3843059 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term354 A x t s) = (term312 A s x t).
Proof. exact (eq_refl (term354 A x t s)). Qed.
Lemma lem3843060 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : term312 A s x t.
Proof. exact (EQ_MP (@lem3843059 A s x t) (@lem3843058 A x t s)). Qed.
Lemma lem3843062 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : term312 A s x t.
Proof. exact (@lem3842685 A s x t (@lem3843060 A s x t)). Qed.
Lemma lem3843063 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term313 A s x t) : False.
Proof. exact (@lem3843062 A s x t (@lem3842669 A s x t h1)). Qed.
Lemma lem3843064 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term313 A s x t) : (term313 A s x t) = False.
Proof. exact (prop_ext (fun h2 : term313 A s x t => @lem3843063 A s x t h1) (fun h2 : False => @lem3842669 A s x t h1)). Qed.
Lemma lem3843065 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term313 A s x t) : False.
Proof. exact (EQ_MP (@lem3843064 A s x t h1) (@lem3842669 A s x t h1)). Qed.
Lemma lem3843066 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : term312 A s x t.
Proof. exact (fun h0 : term313 A s x t => @lem3843065 A s x t h0). Qed.
Lemma lem3843067 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : term311 A s x t.
Proof. exact (EQ_MP (@lem3842668 A s x t) (@lem3843066 A s x t)). Qed.
Lemma lem3843068 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : term310 A s x t.
Proof. exact (EQ_MP (@lem3842664 A s x t) (@lem3843067 A s x t)). Qed.
Lemma lem3843069 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : (term165 A x s t) = (@EMPTY A)) : term163 A x t.
Proof. exact (@lem3843068 A s x t (@lem3841307 A x s t h1)). Qed.
Lemma lem3843070 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term163 A x s) (h2 : (term165 A x s t) = (@EMPTY A)) : term289 A x s t.
Proof. exact (EQ_MP (@lem3842589 A t x s h1) (@lem3843069 A x s t h2)). Qed.
Lemma lem3843071 : term355.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem3843072 : term356.
Proof. exact (proj2 (@lem3843071)). Qed.
Lemma lem3843080 : term357.
Proof. exact (proj1 (@lem3843072)). Qed.
Lemma lem3843081 (m : nat) : term358 m.
Proof. exact (@lem3843080 m). Qed.
Lemma lem3843082 (m : nat) : (term358 m) = (term359 m).
Proof. exact (eq_refl (term358 m)). Qed.
Lemma lem3843083 (m : nat) : term359 m.
Proof. exact (EQ_MP (@lem3843082 m) (@lem3843081 m)). Qed.
Lemma lem3843084 (m : nat) (n : nat) : term360 m n.
Proof. exact (@lem3843083 m n). Qed.
Lemma lem3843085 (m : nat) (n : nat) : (term360 m n) = ((term361 m n) = (term362 m n)).
Proof. exact (eq_refl (term360 m n)). Qed.
Lemma lem3843095 (m : nat) : term363 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem3843096 (m : nat) : (term363 m) = (term364 m).
Proof. exact (eq_refl (term363 m)). Qed.
Lemma lem3843097 (m : nat) : term364 m.
Proof. exact (EQ_MP (@lem3843096 m) (@lem3843095 m)). Qed.
Lemma lem3843098 (m : nat) (n : nat) : term365 m n.
Proof. exact (@lem3843097 m n). Qed.
Lemma lem3843099 (m : nat) (n : nat) : (term365 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term365 m n)). Qed.
Lemma lem3843114 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term366 A x s t.
Proof. exact (@lem82 (term177 A x s t)). Qed.
Lemma lem3843119 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term289 A x s t) : (term177 A x s t) = False.
Proof. exact (@lem3843114 A x s t (@lem3842548 A x s t h1)). Qed.
Lemma lem3843120 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem3843121 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term289 A x s t) : (term367 A x s t) = (@COND nat False).
Proof. exact (MK_COMB (@lem3843120) (@lem3843119 A x s t h1)). Qed.
Lemma lem3843122 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term81 A s t) = (term81 A s t).
Proof. exact (eq_refl (term81 A s t)). Qed.
Lemma lem3843123 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term289 A x s t) : (term368 A x s t) = (term369 A s t).
Proof. exact (MK_COMB (@lem3843121 A x s t h1) (@lem3843122 A s t)). Qed.
Lemma lem3843124 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term370 A s t) = (term370 A s t).
Proof. exact (eq_refl (term370 A s t)). Qed.
Lemma lem3843125 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term289 A x s t) : (term265 A x s t) = (term371 A s t).
Proof. exact (MK_COMB (@lem3843123 A x s t h1) (@lem3843124 A s t)). Qed.
Lemma lem3843127 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem3843128 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem3843127 nat t1 t2). Qed.
Lemma lem3843129 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term371 A s t) = (term370 A s t).
Proof. exact (@lem3843128 (term81 A s t) (term370 A s t)). Qed.
Lemma lem3843130 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term289 A x s t) : (term265 A x s t) = (term370 A s t).
Proof. exact (TRANS (@lem3843125 A x s t h1) (@lem3843129 A s t)). Qed.
Lemma lem3843131 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3843132 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term289 A x s t) : (term285 A x s t) = (term372 A s t).
Proof. exact (MK_COMB (@lem3843131) (@lem3843130 A x s t h1)). Qed.
Lemma lem3843134 (m : nat) (n : nat) : (term361 m n) = (term362 m n).
Proof. exact (EQ_MP (@lem3843085 m n) (@lem3843084 m n)). Qed.
Lemma lem3843135 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term288 A s t) = (term373 A s t).
Proof. exact (@lem3843134 (@CARD A s) (@CARD A t)). Qed.
Lemma lem3843136 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term289 A x s t) : ((term265 A x s t) = (term288 A s t)) = ((term370 A s t) = (term373 A s t)).
Proof. exact (MK_COMB (@lem3843132 A x s t h1) (@lem3843135 A s t)). Qed.
Lemma lem3843138 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem3843099 m n) (@lem3843098 m n)). Qed.
Lemma lem3843139 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term370 A s t) = (term373 A s t)) = ((term81 A s t) = (term82 A s t)).
Proof. exact (@lem3843138 (term81 A s t) (term82 A s t)). Qed.
Lemma lem3843142 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term289 A x s t) : ((term265 A x s t) = (term288 A s t)) = ((term81 A s t) = (term82 A s t)).
Proof. exact (TRANS (@lem3843136 A x s t h1) (@lem3843139 A s t)). Qed.
Lemma lem3843143 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term289 A x s t) : ((term81 A s t) = (term82 A s t)) = ((term265 A x s t) = (term288 A s t)).
Proof. exact (SYM (@lem3843142 A x s t h1)). Qed.
Lemma lem3843144 {A : Type'} (s : A -> Prop) (h1 : term105 A s) : term105 A s.
Proof. exact (h1). Qed.
Lemma lem3843145 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term105 A s) : term96 A s t.
Proof. exact (@lem3843144 A s h1 t). Qed.
Lemma lem3843146 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term96 A s t) = (term97 A s t).
Proof. exact (eq_refl (term96 A s t)). Qed.
Lemma lem3843147 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term105 A s) : term97 A s t.
Proof. exact (EQ_MP (@lem3843146 A s t) (@lem3843145 A t s h1)). Qed.
Lemma lem3843148 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term374 A s t) : term374 A s t.
Proof. exact (h1). Qed.
Lemma lem3843149 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : term374 A s t) : (term81 A s t) = (term82 A s t).
Proof. exact (@lem3843147 A t s h1 (@lem3843148 A s t h2)). Qed.
Lemma lem3843150 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term374 A s t) : term375 A s t.
Proof. exact (fun h0 : term105 A s => @lem3843149 A s t h0 h1). Qed.
Lemma lem3843151 {A : Type'} (s : A -> Prop) (h1 : term105 A s) : term105 A s.
Proof. exact (h1). Qed.
Lemma lem3843152 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : term374 A s t) : (term81 A s t) = (term82 A s t).
Proof. exact (@lem3843150 A s t h2 (@lem3843151 A s h1)). Qed.
Lemma lem3843153 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term105 A s) : term97 A s t.
Proof. exact (fun h0 : term374 A s t => @lem3843152 A s t h1 h0). Qed.
Lemma lem3843154 {A : Type'} (s : A -> Prop) (h1 : term105 A s) : term105 A s.
Proof. exact (fun t : A -> Prop => @lem3843153 A t s h1). Qed.
Lemma lem3843155 {A : Type'} (s : A -> Prop) : term376 A s.
Proof. exact (fun h0 : term105 A s => @lem3843154 A s h0). Qed.
Lemma lem3843156 {A : Type'} (s : A -> Prop) (h1 : term105 A s) : term105 A s.
Proof. exact (@lem3843155 A s (@lem3841303 A s h1)). Qed.
Lemma lem3843157 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term105 A s) : term96 A s t.
Proof. exact (@lem3843156 A s h1 t). Qed.
Lemma lem3843158 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term96 A s t) = (term97 A s t).
Proof. exact (eq_refl (term96 A s t)). Qed.
Lemma lem3843161 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term105 A s) : term97 A s t.
Proof. exact (EQ_MP (@lem3843158 A s t) (@lem3843157 A t s h1)). Qed.
Lemma lem3843162 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term105 A s) : term97 A s t.
Proof. exact (@lem3843161 A t s h1). Qed.
Lemma lem3843172 {A : Type'} (t : A -> Prop) : (@FINITE A t) = ((@FINITE A t) = True).
Proof. exact (@lem7 (@FINITE A t)). Qed.
Lemma lem3843181 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : (@FINITE A t) = True.
Proof. exact (EQ_MP (@lem3843172 A t) (@lem3841308 A t h1)). Qed.
Lemma lem3843182 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3843183 {A : Type'} (t : A -> Prop) (h1 : @FINITE A t) : (term144 A t) = (and True).
Proof. exact (MK_COMB (@lem3843182) (@lem3843181 A t h1)). Qed.
Lemma lem3843186 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@INTER A s t) = (@EMPTY A)) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (eq_refl ((@INTER A s t) = (@EMPTY A))). Qed.
Lemma lem3843187 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) : (term374 A s t) = (term377 A s t).
Proof. exact (MK_COMB (@lem3843183 A t h1) (@lem3843186 A s t)). Qed.
Lemma lem3843189 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3843190 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term377 A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3843189 ((@INTER A s t) = (@EMPTY A))). Qed.
Lemma lem3843193 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) : (term374 A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (TRANS (@lem3843187 A s t h1) (@lem3843190 A s t)). Qed.
Lemma lem3843194 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) : ((@INTER A s t) = (@EMPTY A)) = (term374 A s t).
Proof. exact (SYM (@lem3843193 A s t h1)). Qed.
Lemma lem3843202 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3843203 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (@lem3843202 A s t). Qed.
Lemma lem3843204 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term165 A x s t) = (@EMPTY A)) = (term296 A x s t).
Proof. exact (@lem3843203 A (term165 A x s t) (@EMPTY A)). Qed.
Lemma lem3843213 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3843214 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term308 A x s t) = (term378 A x s t).
Proof. exact (MK_COMB (@lem3843213) (@lem3843204 A x s t)). Qed.
Lemma lem3843218 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3843219 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term20 A s t).
Proof. exact (@lem3843218 A s t). Qed.
Lemma lem3843220 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@INTER A s t) = (@EMPTY A)) = (term379 A s t).
Proof. exact (@lem3843219 A (@INTER A s t) (@EMPTY A)). Qed.
Lemma lem3843229 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term380 A x s t) = (term381 A x s t).
Proof. exact (MK_COMB (@lem3843214 A x s t) (@lem3843220 A s t)). Qed.
Lemma lem3843232 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term381 A x s t) = (term380 A x s t).
Proof. exact (SYM (@lem3843229 A x s t)). Qed.
Lemma lem3843242 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3843243 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (@lem3843242 A s x t). Qed.
Lemma lem3843244 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term297 A x' x s t) = (term298 A x s x' t).
Proof. exact (@lem3843243 A (@INSERT A x s) x' t). Qed.
Lemma lem3843248 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3843249 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (@lem3843248 A y x s). Qed.
Lemma lem3843250 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term15 A x' x s) = (term16 A x x' s).
Proof. exact (@lem3843249 A x x' s). Qed.
Lemma lem3843256 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3843257 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3843256 A P x). Qed.
Lemma lem3843258 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3843257 A s x'). Qed.
Lemma lem3843259 {A : Type'} (x' : A) (x : A) : (term181 A x' x) = (term181 A x' x).
Proof. exact (eq_refl (term181 A x' x)). Qed.
Lemma lem3843260 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term16 A x x' s) = (term182 A x s x').
Proof. exact (MK_COMB (@lem3843259 A x' x) (@lem3843258 A s x')). Qed.
Lemma lem3843263 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term15 A x' x s) = (term182 A x s x').
Proof. exact (TRANS (@lem3843250 A x x' s) (@lem3843260 A x s x')). Qed.
Lemma lem3843264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3843265 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term299 A x' x s) = (term382 A x s x').
Proof. exact (MK_COMB (@lem3843264) (@lem3843263 A x s x')). Qed.
Lemma lem3843267 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3843268 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3843267 A P x). Qed.
Lemma lem3843269 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3843268 A t x'). Qed.
Lemma lem3843270 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term298 A x s x' t) = (term383 A x s t x').
Proof. exact (MK_COMB (@lem3843265 A x s x') (@lem3843269 A t x')). Qed.
Lemma lem3843273 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term297 A x' x s t) = (term383 A x s t x').
Proof. exact (TRANS (@lem3843244 A x s x' t) (@lem3843270 A x s t x')). Qed.
Lemma lem3843274 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3843275 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term302 A x' x s t) = (term384 A x s t x').
Proof. exact (MK_COMB (@lem3843274) (@lem3843273 A x s t x')). Qed.
Lemma lem3843277 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3843278 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3843277 A x). Qed.
Lemma lem3843279 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem3843278 A x'). Qed.
Lemma lem3843280 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term297 A x' x s t) = (@IN A x' (@EMPTY A))) = ((term383 A x s t x') = False).
Proof. exact (MK_COMB (@lem3843275 A x s t x') (@lem3843279 A x')). Qed.
Lemma lem3843282 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3843283 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term383 A x s t x') = False) = (term385 A x s t x').
Proof. exact (@lem3843282 (term383 A x s t x')). Qed.
Lemma lem3843290 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term297 A x' x s t) = (@IN A x' (@EMPTY A))) = (term385 A x s t x').
Proof. exact (TRANS (@lem3843280 A x s t x') (@lem3843283 A x s t x')). Qed.
Lemma lem3843291 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term305 A x s t) = (term386 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3843290 A x s t x')). Qed.
Lemma lem3843292 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3843293 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term296 A x s t) = (term387 A x s t).
Proof. exact (MK_COMB (@lem3843292 A) (@lem3843291 A x s t)). Qed.
Lemma lem3843298 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3843299 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term378 A x s t) = (term388 A x s t).
Proof. exact (MK_COMB (@lem3843298) (@lem3843293 A x s t)). Qed.
Lemma lem3843307 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3843308 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term8 A x s t) = (term9 A s x t).
Proof. exact (@lem3843307 A s x t). Qed.
Lemma lem3843312 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3843313 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3843312 A P x). Qed.
Lemma lem3843314 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3843313 A s x). Qed.
Lemma lem3843315 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3843316 {A : Type'} (s : A -> Prop) (x : A) : (term389 A x s) = (term390 A s x).
Proof. exact (MK_COMB (@lem3843315) (@lem3843314 A s x)). Qed.
Lemma lem3843318 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3843319 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3843318 A P x). Qed.
Lemma lem3843320 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3843319 A t x). Qed.
Lemma lem3843321 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term9 A s x t) = (term391 A s t x).
Proof. exact (MK_COMB (@lem3843316 A s x) (@lem3843320 A t x)). Qed.
Lemma lem3843324 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term8 A x s t) = (term391 A s t x).
Proof. exact (TRANS (@lem3843308 A s x t) (@lem3843321 A s t x)). Qed.
Lemma lem3843325 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3843326 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term392 A x s t) = (term393 A s t x).
Proof. exact (MK_COMB (@lem3843325) (@lem3843324 A s t x)). Qed.
Lemma lem3843328 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3843329 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3843328 A x). Qed.
Lemma lem3843330 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term8 A x s t) = (@IN A x (@EMPTY A))) = ((term391 A s t x) = False).
Proof. exact (MK_COMB (@lem3843326 A s t x) (@lem3843329 A x)). Qed.
Lemma lem3843332 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3843333 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term391 A s t x) = False) = (term394 A s t x).
Proof. exact (@lem3843332 (term391 A s t x)). Qed.
Lemma lem3843336 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((term8 A x s t) = (@IN A x (@EMPTY A))) = (term394 A s t x).
Proof. exact (TRANS (@lem3843330 A s t x) (@lem3843333 A s t x)). Qed.
Lemma lem3843337 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term395 A s t) = (term396 A s t).
Proof. exact (fun_ext (fun x : A => @lem3843336 A s t x)). Qed.
Lemma lem3843338 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3843339 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term379 A s t) = (term397 A s t).
Proof. exact (MK_COMB (@lem3843338 A) (@lem3843337 A s t)). Qed.
Lemma lem3843344 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term381 A x s t) = (term398 A x s t).
Proof. exact (MK_COMB (@lem3843299 A x s t) (@lem3843339 A s t)). Qed.
Lemma lem3843347 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term398 A x s t) = (term381 A x s t).
Proof. exact (SYM (@lem3843344 A x s t)). Qed.
Lemma lem3843349 (p : Prop) : p = (term197 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3843350 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term398 A x s t) = (term399 A x s t).
Proof. exact (@lem3843349 (term398 A x s t)). Qed.
Lemma lem3843351 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term399 A x s t) = (term398 A x s t).
Proof. exact (SYM (@lem3843350 A x s t)). Qed.
Lemma lem3843352 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term400 A x s t) : term400 A x s t.
Proof. exact (h1). Qed.
Lemma lem3843355 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term399 A x s t) : term399 A x s t.
Proof. exact (h1). Qed.
Lemma lem3843356 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term401 A x s t.
Proof. exact (fun h0 : term399 A x s t => @lem3843355 A x s t h0). Qed.
Lemma lem3843357 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term401 A x s t) : term401 A x s t.
Proof. exact (h1). Qed.
Lemma lem3843358 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term399 A x s t) : term399 A x s t.
Proof. exact (h1). Qed.
Lemma lem3843359 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term399 A x s t) (h2 : term401 A x s t) : term399 A x s t.
Proof. exact (@lem3843357 A x s t h2 (@lem3843358 A x s t h1)). Qed.
Lemma lem3843360 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term399 A x s t) : term402 A x s t.
Proof. exact (fun h0 : term401 A x s t => @lem3843359 A x s t h1 h0). Qed.
Lemma lem3843361 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term401 A x s t) : term401 A x s t.
Proof. exact (h1). Qed.
Lemma lem3843362 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term399 A x s t) (h2 : term401 A x s t) : term399 A x s t.
Proof. exact (@lem3843360 A x s t h1 (@lem3843361 A x s t h2)). Qed.
Lemma lem3843363 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term401 A x s t) : term401 A x s t.
Proof. exact (fun h0 : term399 A x s t => @lem3843362 A x s t h0 h1). Qed.
Lemma lem3843364 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term403 A x s t.
Proof. exact (fun h0 : term401 A x s t => @lem3843363 A x s t h0). Qed.
Lemma lem3843367 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term401 A x s t.
Proof. exact (@lem3843364 A x s t (@lem3843356 A x s t)). Qed.
Lemma lem3843368 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term401 A x s t.
Proof. exact (@lem3843367 A x s t). Qed.
Lemma lem3843382 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3843383 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term399 A x s t) = (term404 A x s t).
Proof. exact (@lem3843382 (term400 A x s t)). Qed.
Lemma lem3843385 (t : Prop) : (term204 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3843386 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term404 A x s t) = (term398 A x s t).
Proof. exact (@lem3843385 (term398 A x s t)). Qed.
Lemma lem3843389 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term399 A x s t) = (term398 A x s t).
Proof. exact (TRANS (@lem3843383 A x s t) (@lem3843386 A x s t)). Qed.
Lemma lem3843404 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term405 A s t) = (term406 A s t).
Proof. exact (fun_ext (fun x : A => @lem3843389 A x s t)). Qed.
Lemma lem3843405 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3843406 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term407 A s t) = (term408 A s t).
Proof. exact (MK_COMB (@lem3843405 A) (@lem3843404 A s t)). Qed.
Lemma lem3843411 {A : Type'} (t : A -> Prop) : (term409 A t) = (term410 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3843406 A s t)). Qed.
Lemma lem3843412 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3843413 {A : Type'} (t : A -> Prop) : (term411 A t) = (term412 A t).
Proof. exact (MK_COMB (@lem3843412 A) (@lem3843411 A t)). Qed.
Lemma lem3843418 {A : Type'} : (term413 A) = (term414 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3843413 A t)). Qed.
Lemma lem3843419 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3843428 {A : Type'} : (term415 A) = (term416 A).
Proof. exact (MK_COMB (@lem3843419 A) (@lem3843418 A)). Qed.
Lemma lem3843435 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term394 A s t x) = (term394 A s t x).
Proof. exact (eq_refl (term394 A s t x)). Qed.
Lemma lem3843436 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term396 A s t) = (term396 A s t).
Proof. exact (fun_ext (fun x : A => @lem3843435 A s t x)). Qed.
Lemma lem3843437 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3843438 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term397 A s t) = (term397 A s t).
Proof. exact (MK_COMB (@lem3843437 A) (@lem3843436 A s t)). Qed.
Lemma lem3843449 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term385 A x s t x') = (term385 A x s t x').
Proof. exact (eq_refl (term385 A x s t x')). Qed.
Lemma lem3843450 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term386 A x s t) = (term386 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3843449 A x s t x')). Qed.
Lemma lem3843451 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3843452 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term387 A x s t) = (term387 A x s t).
Proof. exact (MK_COMB (@lem3843451 A) (@lem3843450 A x s t)). Qed.
Lemma lem3843453 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3843454 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term388 A x s t) = (term388 A x s t).
Proof. exact (MK_COMB (@lem3843453) (@lem3843452 A x s t)). Qed.
Lemma lem3843455 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term398 A x s t) = (term398 A x s t).
Proof. exact (MK_COMB (@lem3843454 A x s t) (@lem3843438 A s t)). Qed.
Lemma lem3843456 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term406 A s t) = (term406 A s t).
Proof. exact (fun_ext (fun x : A => @lem3843455 A x s t)). Qed.
Lemma lem3843457 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3843458 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term408 A s t) = (term408 A s t).
Proof. exact (MK_COMB (@lem3843457 A) (@lem3843456 A s t)). Qed.
Lemma lem3843459 {A : Type'} (t : A -> Prop) : (term410 A t) = (term410 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3843458 A s t)). Qed.
Lemma lem3843460 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3843461 {A : Type'} (t : A -> Prop) : (term412 A t) = (term412 A t).
Proof. exact (MK_COMB (@lem3843460 A) (@lem3843459 A t)). Qed.
Lemma lem3843462 {A : Type'} : (term414 A) = (term414 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3843461 A t)). Qed.
Lemma lem3843463 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3843464 {A : Type'} : (term416 A) = (term416 A).
Proof. exact (MK_COMB (@lem3843463 A) (@lem3843462 A)). Qed.
Lemma lem3843505 {A : Type'} : (term415 A) = (term416 A).
Proof. exact (TRANS (@lem3843428 A) (@lem3843464 A)). Qed.
Lemma lem3843506 {A : Type'} : (term416 A) = (term415 A).
Proof. exact (SYM (@lem3843505 A)). Qed.
Lemma lem3843507 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term387 A x s t) : term387 A x s t.
Proof. exact (h1). Qed.
Lemma lem3843515 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term219 A x s x') = (term220 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3843516 {A : Type'} (t : A -> Prop) (x' : A) : (term221 A t x') = (term221 A t x').
Proof. exact (eq_refl (term221 A t x')). Qed.
Lemma lem3843517 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3843518 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term417 A x s x') = (term418 A x s x').
Proof. exact (MK_COMB (@lem3843517) (@lem3843515 A x s x')). Qed.
Lemma lem3843519 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term419 A x s t x') = (term420 A x s t x').
Proof. exact (MK_COMB (@lem3843518 A x s x') (@lem3843516 A t x')). Qed.
Lemma lem3843520 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term385 A x s t x') = (term419 A x s t x').
Proof. exact (@lem17045 (term182 A x s x') (t x')). Qed.
Lemma lem3843521 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term385 A x s t x') = (term420 A x s t x').
Proof. exact (TRANS (@lem3843520 A x s t x') (@lem3843519 A x s t x')). Qed.
Lemma lem3843522 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term386 A x s t) = (term421 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3843521 A x s t x')). Qed.
Lemma lem3843523 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3843576 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term387 A x s t) = (term422 A x s t).
Proof. exact (MK_COMB (@lem3843523 A) (@lem3843522 A x s t)). Qed.
Lemma lem3843577 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term387 A x s t) : term422 A x s t.
Proof. exact (EQ_MP (@lem3843576 A x s t) (@lem3843507 A x s t h1)). Qed.
Lemma lem3843587 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term391 A s t x') : term391 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3843610 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term420 A x s t x') = (term420 A x s t x').
Proof. exact (eq_refl (term420 A x s t x')). Qed.
Lemma lem3843611 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term421 A x s t) = (term421 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3843610 A x s t x')). Qed.
Lemma lem3843612 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3843613 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term422 A x s t) = (term422 A x s t).
Proof. exact (MK_COMB (@lem3843612 A) (@lem3843611 A x s t)). Qed.
Lemma lem3843614 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term387 A x s t) : term422 A x s t.
Proof. exact (EQ_MP (@lem3843613 A x s t) (@lem3843577 A x s t h1)). Qed.
Lemma lem3843624 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term391 A s t x') : term391 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3843644 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term420 A x s t x') = (term423 A x s t x').
Proof. exact (@lem19699 (term244 A x' x) (term221 A s x') (term221 A t x')). Qed.
Lemma lem3843645 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term421 A x s t) = (term424 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3843644 A x s t x')). Qed.
Lemma lem3843646 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3843648 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term422 A x s t) = (term425 A x s t).
Proof. exact (MK_COMB (@lem3843646 A) (@lem3843645 A x s t)). Qed.
Lemma lem3843649 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term387 A x s t) : term425 A x s t.
Proof. exact (EQ_MP (@lem3843648 A x s t) (@lem3843614 A x s t h1)). Qed.
Lemma lem3843658 {A : Type'} (_44595 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term387 A x s t) : term426 A x s t _44595.
Proof. exact (@lem3843649 A x s t h1 _44595). Qed.
Lemma lem3843659 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_44595 : A) : (term426 A x s t _44595) = (term423 A x s t _44595).
Proof. exact (eq_refl (term426 A x s t _44595)). Qed.
Lemma lem3843660 {A : Type'} (_44595 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term387 A x s t) : term423 A x s t _44595.
Proof. exact (EQ_MP (@lem3843659 A x s t _44595) (@lem3843658 A _44595 x s t h1)). Qed.
Lemma lem3843678 {A : Type'} (_44595 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term387 A x s t) : term427 A s t _44595.
Proof. exact (proj2 (@lem3843660 A _44595 x s t h1)). Qed.
Lemma lem3843706 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term391 A s t x') : s x'.
Proof. exact (proj1 (@lem3843624 A s t x' h1)). Qed.
Lemma lem3843707 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term391 A s t x') : term255 A s x'.
Proof. exact (fun h0 : term221 A s x' => @lem3843706 A s t x' h1). Qed.
Lemma lem3843709 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3843710 {A : Type'} (s : A -> Prop) (x' : A) : (term255 A s x') = (s x').
Proof. exact (@lem3843709 (s x')). Qed.
Lemma lem3843711 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term391 A s t x') : s x'.
Proof. exact (EQ_MP (@lem3843710 A s x') (@lem3843707 A s t x' h1)). Qed.
Lemma lem3843713 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term391 A s t x') : t x'.
Proof. exact (proj2 (@lem3843624 A s t x' h1)). Qed.
Lemma lem3843714 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term391 A s t x') : term255 A t x'.
Proof. exact (fun h0 : term221 A t x' => @lem3843713 A s t x' h1). Qed.
Lemma lem3843716 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3843717 {A : Type'} (t : A -> Prop) (x' : A) : (term255 A t x') = (t x').
Proof. exact (@lem3843716 (t x')). Qed.
Lemma lem3843718 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term391 A s t x') : t x'.
Proof. exact (EQ_MP (@lem3843717 A t x') (@lem3843714 A s t x' h1)). Qed.
Lemma lem3843720 (a : Prop) (b : Prop) : (term344 a b) = (term345 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3843721 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_44595 : A) : (term427 A s t _44595) = (term394 A s t _44595).
Proof. exact (@lem3843720 (s _44595) (t _44595)). Qed.
Lemma lem3843723 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3843724 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_44595 : A) : (term394 A s t _44595) = (term428 A s t _44595).
Proof. exact (@lem3843723 (term391 A s t _44595)). Qed.
Lemma lem3843725 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_44595 : A) : (term427 A s t _44595) = (term428 A s t _44595).
Proof. exact (TRANS (@lem3843721 A s t _44595) (@lem3843724 A s t _44595)). Qed.
Lemma lem3843727 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term391 A s t x') : term391 A s t x'.
Proof. exact (conj (@lem3843711 A s t x' h1) (@lem3843718 A s t x' h1)). Qed.
Lemma lem3843729 {A : Type'} (_44595 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term387 A x s t) : term428 A s t _44595.
Proof. exact (EQ_MP (@lem3843725 A s t _44595) (@lem3843678 A _44595 x s t h1)). Qed.
Lemma lem3843730 {A : Type'} (_44595 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term387 A x s t) : term428 A s t _44595.
Proof. exact (@lem3843729 A _44595 x s t h1). Qed.
Lemma lem3843731 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term387 A x s t) : term428 A s t x'.
Proof. exact (@lem3843730 A x' x s t h1). Qed.
Lemma lem3843734 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term387 A x s t) (h2 : term391 A s t x') : False.
Proof. exact (@lem3843731 A x' x s t h1 (@lem3843727 A s t x' h2)). Qed.
Lemma lem3843735 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term387 A x s t) (h2 : term391 A s t x') : term254.
Proof. exact (fun h0 : ~ False => @lem3843734 A x s t x' h1 h2). Qed.
Lemma lem3843737 (p : Prop) : (term252 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3843738 : term254 = False.
Proof. exact (@lem3843737 False). Qed.
Lemma lem3843739 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term387 A x s t) (h2 : term391 A s t x') : False.
Proof. exact (EQ_MP (@lem3843738) (@lem3843735 A x s t x' h1 h2)). Qed.
Lemma lem3843740 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term387 A x s t) (h2 : term391 A s t x') : (term391 A s t x') = False.
Proof. exact (prop_ext (fun h3 : term391 A s t x' => @lem3843739 A x s t x' h1 h2) (fun h3 : False => @lem3843624 A s t x' h2)). Qed.
Lemma lem3843741 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term387 A x s t) (h2 : term391 A s t x') : False.
Proof. exact (EQ_MP (@lem3843740 A x s t x' h1 h2) (@lem3843624 A s t x' h2)). Qed.
Lemma lem3843742 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term387 A x s t) (h2 : term391 A s t x') : (term391 A s t x') = False.
Proof. exact (prop_ext (fun h3 : term391 A s t x' => @lem3843741 A x s t x' h1 h2) (fun h3 : False => @lem3843587 A s t x' h2)). Qed.
Lemma lem3843743 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term387 A x s t) (h2 : term391 A s t x') : False.
Proof. exact (EQ_MP (@lem3843742 A x s t x' h1 h2) (@lem3843587 A s t x' h2)). Qed.
Lemma lem3843744 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term387 A x s t) : term428 A s t x'.
Proof. exact (fun h0 : term391 A s t x' => @lem3843743 A x s t x' h1 h0). Qed.
Lemma lem3843745 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term428 A s t x') = (term394 A s t x').
Proof. exact (@lem69 (term391 A s t x')). Qed.
Lemma lem3843746 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term387 A x s t) : term394 A s t x'.
Proof. exact (EQ_MP (@lem3843745 A s t x') (@lem3843744 A x' x s t h1)). Qed.
Lemma lem3843751 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term387 A x s t) : term397 A s t.
Proof. exact (fun x' : A => @lem3843746 A x' x s t h1). Qed.
Lemma lem3843752 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term398 A x s t.
Proof. exact (fun h0 : term387 A x s t => @lem3843751 A x s t h0). Qed.
Lemma lem3843757 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term408 A s t.
Proof. exact (fun x : A => @lem3843752 A x s t). Qed.
Lemma lem3843762 {A : Type'} (t : A -> Prop) : term412 A t.
Proof. exact (fun s : A -> Prop => @lem3843757 A s t). Qed.
Lemma lem3843767 {A : Type'} : term416 A.
Proof. exact (fun t : A -> Prop => @lem3843762 A t). Qed.
Lemma lem3843768 {A : Type'} : term415 A.
Proof. exact (EQ_MP (@lem3843506 A) (@lem3843767 A)). Qed.
Lemma lem3843769 {A : Type'} (t : A -> Prop) : term429 A t.
Proof. exact (@lem3843768 A t). Qed.
Lemma lem3843770 {A : Type'} (t : A -> Prop) : (term429 A t) = (term411 A t).
Proof. exact (eq_refl (term429 A t)). Qed.
Lemma lem3843771 {A : Type'} (t : A -> Prop) : term411 A t.
Proof. exact (EQ_MP (@lem3843770 A t) (@lem3843769 A t)). Qed.
Lemma lem3843772 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term430 A t s.
Proof. exact (@lem3843771 A t s). Qed.
Lemma lem3843773 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term430 A t s) = (term407 A s t).
Proof. exact (eq_refl (term430 A t s)). Qed.
Lemma lem3843774 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term407 A s t.
Proof. exact (EQ_MP (@lem3843773 A s t) (@lem3843772 A t s)). Qed.
Lemma lem3843775 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term431 A s t x.
Proof. exact (@lem3843774 A s t x). Qed.
Lemma lem3843776 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term431 A s t x) = (term399 A x s t).
Proof. exact (eq_refl (term431 A s t x)). Qed.
Lemma lem3843777 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term399 A x s t.
Proof. exact (EQ_MP (@lem3843776 A x s t) (@lem3843775 A s t x)). Qed.
Lemma lem3843779 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term399 A x s t.
Proof. exact (@lem3843368 A x s t (@lem3843777 A x s t)). Qed.
Lemma lem3843780 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term400 A x s t) : False.
Proof. exact (@lem3843779 A x s t (@lem3843352 A x s t h1)). Qed.
Lemma lem3843781 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term400 A x s t) : (term400 A x s t) = False.
Proof. exact (prop_ext (fun h2 : term400 A x s t => @lem3843780 A x s t h1) (fun h2 : False => @lem3843352 A x s t h1)). Qed.
Lemma lem3843782 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term400 A x s t) : False.
Proof. exact (EQ_MP (@lem3843781 A x s t h1) (@lem3843352 A x s t h1)). Qed.
Lemma lem3843783 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term399 A x s t.
Proof. exact (fun h0 : term400 A x s t => @lem3843782 A x s t h0). Qed.
Lemma lem3843784 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term398 A x s t.
Proof. exact (EQ_MP (@lem3843351 A x s t) (@lem3843783 A x s t)). Qed.
Lemma lem3843785 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term381 A x s t.
Proof. exact (EQ_MP (@lem3843347 A x s t) (@lem3843784 A x s t)). Qed.
Lemma lem3843786 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term380 A x s t.
Proof. exact (EQ_MP (@lem3843232 A x s t) (@lem3843785 A x s t)). Qed.
Lemma lem3843787 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : (term165 A x s t) = (@EMPTY A)) : (@INTER A s t) = (@EMPTY A).
Proof. exact (@lem3843786 A x s t (@lem3841307 A x s t h1)). Qed.
Lemma lem3843788 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : @FINITE A t) (h2 : (term165 A x s t) = (@EMPTY A)) : term374 A s t.
Proof. exact (EQ_MP (@lem3843194 A s t h1) (@lem3843787 A x s t h2)). Qed.
Lemma lem3843789 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A t) (h3 : (term165 A x s t) = (@EMPTY A)) : (term81 A s t) = (term82 A s t).
Proof. exact (@lem3843162 A t s h1 (@lem3843788 A x s t h2 h3)). Qed.
Lemma lem3843790 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A t) (h3 : term289 A x s t) (h4 : (term165 A x s t) = (@EMPTY A)) : (term265 A x s t) = (term288 A s t).
Proof. exact (EQ_MP (@lem3843143 A x s t h3) (@lem3843789 A x s t h1 h2 h4)). Qed.
Lemma lem3843791 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A t) (h3 : term289 A x s t) (h4 : (term165 A x s t) = (@EMPTY A)) : (term289 A x s t) = ((term265 A x s t) = (term288 A s t)).
Proof. exact (prop_ext (fun h5 : term289 A x s t => @lem3843790 A x s t h1 h2 h3 h4) (fun h5 : (term265 A x s t) = (term288 A s t) => @lem3842548 A x s t h3)). Qed.
Lemma lem3843792 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A t) (h3 : term289 A x s t) (h4 : (term165 A x s t) = (@EMPTY A)) : (term265 A x s t) = (term288 A s t).
Proof. exact (EQ_MP (@lem3843791 A x s t h1 h2 h3 h4) (@lem3842548 A x s t h3)). Qed.
Lemma lem3843793 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A t) (h3 : term163 A x s) (h4 : (term165 A x s t) = (@EMPTY A)) : (term289 A x s t) = ((term265 A x s t) = (term288 A s t)).
Proof. exact (prop_ext (fun h5 : term289 A x s t => @lem3843792 A x s t h1 h2 h5 h4) (fun h5 : (term265 A x s t) = (term288 A s t) => @lem3843070 A x s t h3 h4)). Qed.
Lemma lem3843794 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A t) (h3 : term163 A x s) (h4 : (term165 A x s t) = (@EMPTY A)) : (term265 A x s t) = (term288 A s t).
Proof. exact (EQ_MP (@lem3843793 A x s t h1 h2 h3 h4) (@lem3843070 A x s t h3 h4)). Qed.
Lemma lem3843795 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A t) (h3 : term163 A x s) (h4 : (term165 A x s t) = (@EMPTY A)) (h5 : (term276 A x s) = (term272 A s)) (h6 : (term171 A x s t) = (term265 A x s t)) : (term171 A x s t) = (term172 A x s t).
Proof. exact (EQ_MP (@lem3842547 A x s t h5 h6) (@lem3843794 A x s t h1 h2 h3 h4)). Qed.
Lemma lem3843796 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A t) (h3 : term163 A x s) (h4 : (term165 A x s t) = (@EMPTY A)) (h5 : (term171 A x s t) = (term265 A x s t)) : term281 A x s t.
Proof. exact (fun h0 : (term276 A x s) = (term272 A s) => @lem3843795 A x s t h1 h2 h3 h4 h0 h5). Qed.
Lemma lem3843797 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A t) (h3 : term163 A x s) (h4 : (term165 A x s t) = (@EMPTY A)) : term283 A x s t.
Proof. exact (fun h0 : (term171 A x s t) = (term265 A x s t) => @lem3843796 A x s t h1 h2 h3 h4 h0). Qed.
Lemma lem3843798 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : term34 A s t) (h5 : term163 A x s) (h6 : (term165 A x s t) = (@EMPTY A)) : term282 A x s t.
Proof. exact (EQ_MP (@lem3842516 A t x s h2 h4 h5) (@lem3843797 A x s t h1 h3 h5 h6)). Qed.
Lemma lem3843799 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : term34 A s t) (h5 : term163 A x s) (h6 : (term165 A x s t) = (@EMPTY A)) : term280 A x s t.
Proof. exact (@lem3843798 A x s t h1 h2 h3 h4 h5 h6 (@lem3840748 A x s t)). Qed.
Lemma lem3843800 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : term34 A s t) (h5 : term163 A x s) (h6 : (term165 A x s t) = (@EMPTY A)) : (term171 A x s t) = (term172 A x s t).
Proof. exact (@lem3843799 A x s t h1 h2 h3 h4 h5 h6 (@lem3840756 A x s)). Qed.
Lemma lem3843801 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term260 A t s) : @FINITE A s.
Proof. exact (proj2 (@lem3842378 A t s h1)). Qed.
Lemma lem3843802 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term260 A t s) : term34 A s t.
Proof. exact (proj1 (@lem3842378 A t s h1)). Qed.
Lemma lem3843803 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : term34 A s t) (h5 : term163 A x s) (h6 : (term165 A x s t) = (@EMPTY A)) : (term34 A s t) = ((term171 A x s t) = (term172 A x s t)).
Proof. exact (prop_ext (fun h7 : term34 A s t => @lem3843800 A x s t h1 h2 h3 h4 h5 h6) (fun h7 : (term171 A x s t) = (term172 A x s t) => @lem3842380 A s t h4)). Qed.
Lemma lem3843804 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : term34 A s t) (h5 : term163 A x s) (h6 : (term165 A x s t) = (@EMPTY A)) : (term171 A x s t) = (term172 A x s t).
Proof. exact (EQ_MP (@lem3843803 A x s t h1 h2 h3 h4 h5 h6) (@lem3842380 A s t h4)). Qed.
Lemma lem3843805 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A t) (h3 : term34 A s t) (h4 : term163 A x s) (h5 : term260 A t s) (h6 : (term165 A x s t) = (@EMPTY A)) : (@FINITE A s) = ((term171 A x s t) = (term172 A x s t)).
Proof. exact (prop_ext (fun h7 : @FINITE A s => @lem3843804 A x s t h1 h7 h2 h3 h4 h6) (fun h7 : (term171 A x s t) = (term172 A x s t) => @lem3843801 A t s h5)). Qed.
Lemma lem3843806 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A t) (h3 : term34 A s t) (h4 : term163 A x s) (h5 : term260 A t s) (h6 : (term165 A x s t) = (@EMPTY A)) : (term171 A x s t) = (term172 A x s t).
Proof. exact (EQ_MP (@lem3843805 A x s t h1 h2 h3 h4 h5 h6) (@lem3843801 A t s h5)). Qed.
Lemma lem3843807 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A t) (h3 : term163 A x s) (h4 : term260 A t s) (h5 : (term165 A x s t) = (@EMPTY A)) : (term34 A s t) = ((term171 A x s t) = (term172 A x s t)).
Proof. exact (prop_ext (fun h6 : term34 A s t => @lem3843806 A x s t h1 h2 h6 h3 h4 h5) (fun h6 : (term171 A x s t) = (term172 A x s t) => @lem3843802 A t s h4)). Qed.
Lemma lem3843808 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A t) (h3 : term163 A x s) (h4 : term260 A t s) (h5 : (term165 A x s t) = (@EMPTY A)) : (term171 A x s t) = (term172 A x s t).
Proof. exact (EQ_MP (@lem3843807 A x s t h1 h2 h3 h4 h5) (@lem3843802 A t s h4)). Qed.
Lemma lem3843809 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : term163 A x s) (h5 : (term165 A x s t) = (@EMPTY A)) : (term260 A t s) = ((term171 A x s t) = (term172 A x s t)).
Proof. exact (prop_ext (fun h6 : term260 A t s => @lem3843808 A x s t h1 h3 h4 h6 h5) (fun h6 : (term171 A x s t) = (term172 A x s t) => @lem3842433 A s t h2 h3)). Qed.
Lemma lem3843810 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : term163 A x s) (h5 : (term165 A x s t) = (@EMPTY A)) : (term171 A x s t) = (term172 A x s t).
Proof. exact (EQ_MP (@lem3843809 A x s t h1 h2 h3 h4 h5) (@lem3842433 A s t h2 h3)). Qed.
Lemma lem3843811 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : term163 A x s) (h5 : (term165 A x s t) = (@EMPTY A)) (h6 : (term166 A x s t) = (term167 A x s t)) : (term174 A x s t) = (term172 A x s t).
Proof. exact (EQ_MP (@lem3841322 A x s t h6) (@lem3843810 A x s t h1 h2 h3 h4 h5)). Qed.
Lemma lem3843812 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : term163 A x s) (h5 : (term165 A x s t) = (@EMPTY A)) : ((term166 A x s t) = (term167 A x s t)) = ((term174 A x s t) = (term172 A x s t)).
Proof. exact (prop_ext (fun h6 : (term166 A x s t) = (term167 A x s t) => @lem3843811 A x s t h1 h2 h3 h4 h5 h6) (fun h6 : (term174 A x s t) = (term172 A x s t) => @lem3842377 A x s t)). Qed.
Lemma lem3843813 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : term163 A x s) (h5 : (term165 A x s t) = (@EMPTY A)) : (term174 A x s t) = (term172 A x s t).
Proof. exact (EQ_MP (@lem3843812 A x s t h1 h2 h3 h4 h5) (@lem3842377 A x s t)). Qed.
Lemma lem3843814 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term164 A x s t) : (term165 A x s t) = (@EMPTY A).
Proof. exact (proj2 (@lem3841306 A x s t h1)). Qed.
Lemma lem3843815 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term164 A x s t) : @FINITE A t.
Proof. exact (proj1 (@lem3841306 A x s t h1)). Qed.
Lemma lem3843816 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : term163 A x s) (h5 : (term165 A x s t) = (@EMPTY A)) : ((term165 A x s t) = (@EMPTY A)) = ((term174 A x s t) = (term172 A x s t)).
Proof. exact (prop_ext (fun h6 : (term165 A x s t) = (@EMPTY A) => @lem3843813 A x s t h1 h2 h3 h4 h5) (fun h6 : (term174 A x s t) = (term172 A x s t) => @lem3841307 A x s t h5)). Qed.
Lemma lem3843817 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : term163 A x s) (h5 : (term165 A x s t) = (@EMPTY A)) : (term174 A x s t) = (term172 A x s t).
Proof. exact (EQ_MP (@lem3843816 A x s t h1 h2 h3 h4 h5) (@lem3841307 A x s t h5)). Qed.
Lemma lem3843818 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : term163 A x s) (h5 : (term165 A x s t) = (@EMPTY A)) : (@FINITE A t) = ((term174 A x s t) = (term172 A x s t)).
Proof. exact (prop_ext (fun h6 : @FINITE A t => @lem3843817 A x s t h1 h2 h3 h4 h5) (fun h6 : (term174 A x s t) = (term172 A x s t) => @lem3841308 A t h3)). Qed.
Lemma lem3843819 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : term163 A x s) (h5 : (term165 A x s t) = (@EMPTY A)) : (term174 A x s t) = (term172 A x s t).
Proof. exact (EQ_MP (@lem3843818 A x s t h1 h2 h3 h4 h5) (@lem3841308 A t h3)). Qed.
Lemma lem3843820 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : term163 A x s) (h5 : term164 A x s t) : ((term165 A x s t) = (@EMPTY A)) = ((term174 A x s t) = (term172 A x s t)).
Proof. exact (prop_ext (fun h6 : (term165 A x s t) = (@EMPTY A) => @lem3843819 A x s t h1 h2 h3 h4 h6) (fun h6 : (term174 A x s t) = (term172 A x s t) => @lem3843814 A x s t h5)). Qed.
Lemma lem3843821 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : @FINITE A t) (h4 : term163 A x s) (h5 : term164 A x s t) : (term174 A x s t) = (term172 A x s t).
Proof. exact (EQ_MP (@lem3843820 A x s t h1 h2 h3 h4 h5) (@lem3843814 A x s t h5)). Qed.
Lemma lem3843822 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : term163 A x s) (h4 : term164 A x s t) : (@FINITE A t) = ((term174 A x s t) = (term172 A x s t)).
Proof. exact (prop_ext (fun h5 : @FINITE A t => @lem3843821 A x s t h1 h2 h5 h3 h4) (fun h5 : (term174 A x s t) = (term172 A x s t) => @lem3843815 A x s t h4)). Qed.
Lemma lem3843823 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : term163 A x s) (h4 : term164 A x s t) : (term174 A x s t) = (term172 A x s t).
Proof. exact (EQ_MP (@lem3843822 A x s t h1 h2 h3 h4) (@lem3843815 A x s t h4)). Qed.
Lemma lem3843824 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : term163 A x s) : term432 A x s t.
Proof. exact (fun h0 : term164 A x s t => @lem3843823 A x s t h1 h2 h3 h0). Qed.
Lemma lem3843829 {A : Type'} (x : A) (s : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : term163 A x s) : term124 A x s.
Proof. exact (fun t : A -> Prop => @lem3843824 A t x s h1 h2 h3). Qed.
Lemma lem3843830 {A : Type'} (x : A) (s : A -> Prop) (h1 : term120 A x s) : term118 A x s.
Proof. exact (proj2 (@lem3841301 A x s h1)). Qed.
Lemma lem3843831 {A : Type'} (x : A) (s : A -> Prop) (h1 : term120 A x s) : term105 A s.
Proof. exact (proj1 (@lem3841301 A x s h1)). Qed.
Lemma lem3843832 {A : Type'} (x : A) (s : A -> Prop) (h1 : term118 A x s) : @FINITE A s.
Proof. exact (proj2 (@lem3841302 A x s h1)). Qed.
Lemma lem3843833 {A : Type'} (x : A) (s : A -> Prop) (h1 : term118 A x s) : term163 A x s.
Proof. exact (proj1 (@lem3841302 A x s h1)). Qed.
Lemma lem3843834 {A : Type'} (x : A) (s : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : term163 A x s) : (@FINITE A s) = (term124 A x s).
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3843829 A x s h1 h2 h3) (fun h4 : term124 A x s => @lem3841304 A s h2)). Qed.
Lemma lem3843835 {A : Type'} (x : A) (s : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : term163 A x s) : term124 A x s.
Proof. exact (EQ_MP (@lem3843834 A x s h1 h2 h3) (@lem3841304 A s h2)). Qed.
Lemma lem3843836 {A : Type'} (x : A) (s : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : term163 A x s) : (term163 A x s) = (term124 A x s).
Proof. exact (prop_ext (fun h4 : term163 A x s => @lem3843835 A x s h1 h2 h3) (fun h4 : term124 A x s => @lem3841305 A x s h3)). Qed.
Lemma lem3843837 {A : Type'} (x : A) (s : A -> Prop) (h1 : term105 A s) (h2 : @FINITE A s) (h3 : term163 A x s) : term124 A x s.
Proof. exact (EQ_MP (@lem3843836 A x s h1 h2 h3) (@lem3841305 A x s h3)). Qed.
Lemma lem3843838 {A : Type'} (x : A) (s : A -> Prop) (h1 : term105 A s) (h2 : term163 A x s) (h3 : term118 A x s) : (@FINITE A s) = (term124 A x s).
Proof. exact (prop_ext (fun h4 : @FINITE A s => @lem3843837 A x s h1 h4 h2) (fun h4 : term124 A x s => @lem3843832 A x s h3)). Qed.
Lemma lem3843839 {A : Type'} (x : A) (s : A -> Prop) (h1 : term105 A s) (h2 : term163 A x s) (h3 : term118 A x s) : term124 A x s.
Proof. exact (EQ_MP (@lem3843838 A x s h1 h2 h3) (@lem3843832 A x s h3)). Qed.
Lemma lem3843840 {A : Type'} (x : A) (s : A -> Prop) (h1 : term105 A s) (h2 : term118 A x s) : (term163 A x s) = (term124 A x s).
Proof. exact (prop_ext (fun h3 : term163 A x s => @lem3843839 A x s h1 h3 h2) (fun h3 : term124 A x s => @lem3843833 A x s h2)). Qed.
Lemma lem3843841 {A : Type'} (x : A) (s : A -> Prop) (h1 : term105 A s) (h2 : term118 A x s) : term124 A x s.
Proof. exact (EQ_MP (@lem3843840 A x s h1 h2) (@lem3843833 A x s h2)). Qed.
Lemma lem3843842 {A : Type'} (x : A) (s : A -> Prop) (h1 : term105 A s) (h2 : term118 A x s) : (term105 A s) = (term124 A x s).
Proof. exact (prop_ext (fun h3 : term105 A s => @lem3843841 A x s h1 h2) (fun h3 : term124 A x s => @lem3841303 A s h1)). Qed.
Lemma lem3843843 {A : Type'} (x : A) (s : A -> Prop) (h1 : term105 A s) (h2 : term118 A x s) : term124 A x s.
Proof. exact (EQ_MP (@lem3843842 A x s h1 h2) (@lem3841303 A s h1)). Qed.
Lemma lem3843844 {A : Type'} (x : A) (s : A -> Prop) (h1 : term105 A s) (h2 : term120 A x s) : (term118 A x s) = (term124 A x s).
Proof. exact (prop_ext (fun h3 : term118 A x s => @lem3843843 A x s h1 h3) (fun h3 : term124 A x s => @lem3843830 A x s h2)). Qed.
Lemma lem3843845 {A : Type'} (x : A) (s : A -> Prop) (h1 : term105 A s) (h2 : term120 A x s) : term124 A x s.
Proof. exact (EQ_MP (@lem3843844 A x s h1 h2) (@lem3843830 A x s h2)). Qed.
Lemma lem3843846 {A : Type'} (x : A) (s : A -> Prop) (h1 : term120 A x s) : (term105 A s) = (term124 A x s).
Proof. exact (prop_ext (fun h2 : term105 A s => @lem3843845 A x s h2 h1) (fun h2 : term124 A x s => @lem3843831 A x s h1)). Qed.
Lemma lem3843847 {A : Type'} (x : A) (s : A -> Prop) (h1 : term120 A x s) : term124 A x s.
Proof. exact (EQ_MP (@lem3843846 A x s h1) (@lem3843831 A x s h1)). Qed.
Lemma lem3843848 {A : Type'} (x : A) (s : A -> Prop) : term126 A x s.
Proof. exact (fun h0 : term120 A x s => @lem3843847 A x s h0). Qed.
Lemma lem3843853 {A : Type'} (x : A) : term130 A x.
Proof. exact (fun s : A -> Prop => @lem3843848 A x s). Qed.
Lemma lem3843858 {A : Type'} : term134 A.
Proof. exact (fun x : A => @lem3843853 A x). Qed.
Lemma lem3843859 {A : Type'} : term136 A.
Proof. exact (EQ_MP (@lem3841300 A) (@lem3843858 A)). Qed.
Lemma lem3843860 {A : Type'} : term108 A.
Proof. exact (@lem3841143 A (@lem3843859 A)). Qed.
Lemma lem3843861 {A : Type'} : term90 A.
Proof. exact (EQ_MP (@lem3841110 A) (@lem3843860 A)). Qed.
Lemma lem3843862 {A : Type'} : term89 A.
Proof. exact (EQ_MP (@lem3841024 A) (@lem3843861 A)). Qed.
