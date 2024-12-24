Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJOINT_DELETE_SYM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211738_spec.
Require Import thm3211739_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3320764 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3320765 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3320766 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3320765 t1) (@lem3320764 t1)). Qed.
Lemma lem3320767 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3320766 t1 t2). Qed.
Lemma lem3320768 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3320769 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3320768 t1 t2) (@lem3320767 t1 t2)). Qed.
Lemma lem3320770 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3320769 t1 t2 t3). Qed.
Lemma lem3320771 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3320772 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3320771 t1 t2 t3) (@lem3320770 t1 t2 t3)). Qed.
Lemma lem3320773 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3320772 t1 t2 t3)). Qed.
Lemma lem3320791 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem3320792 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3320791 A s t). Qed.
Lemma lem3320793 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A s x t) = ((term8 A s x t) = (@EMPTY A)).
Proof. exact (@lem3320792 A (@DELETE A s x) t). Qed.
Lemma lem3320797 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term9 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3320798 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term9 A s t).
Proof. exact (@lem3320797 A s t). Qed.
Lemma lem3320799 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : ((term8 A s x t) = (@EMPTY A)) = (term10 A s x t).
Proof. exact (@lem3320798 A (term8 A s x t) (@EMPTY A)). Qed.
Lemma lem3320804 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A s x t) = (term10 A s x t).
Proof. exact (TRANS (@lem3320793 A s x t) (@lem3320799 A s x t)). Qed.
Lemma lem3320809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3320810 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A s x t) = (term12 A s x t).
Proof. exact (MK_COMB (@lem3320809) (@lem3320804 A s x t)). Qed.
Lemma lem3320812 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (EQ_MP (@lem3211739 A s t) (@lem3211738 A s t)). Qed.
Lemma lem3320813 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@DISJOINT A s t) = ((@INTER A s t) = (@EMPTY A)).
Proof. exact (@lem3320812 A s t). Qed.
Lemma lem3320814 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term7 A t x s) = ((term8 A t x s) = (@EMPTY A)).
Proof. exact (@lem3320813 A (@DELETE A t x) s). Qed.
Lemma lem3320818 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term9 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3320819 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term9 A s t).
Proof. exact (@lem3320818 A s t). Qed.
Lemma lem3320820 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : ((term8 A t x s) = (@EMPTY A)) = (term10 A t x s).
Proof. exact (@lem3320819 A (term8 A t x s) (@EMPTY A)). Qed.
Lemma lem3320825 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term7 A t x s) = (term10 A t x s).
Proof. exact (TRANS (@lem3320814 A t x s) (@lem3320820 A t x s)). Qed.
Lemma lem3320830 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : ((term7 A s x t) = (term7 A t x s)) = ((term10 A s x t) = (term10 A t x s)).
Proof. exact (MK_COMB (@lem3320810 A s x t) (@lem3320825 A t x s)). Qed.
Lemma lem3320835 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term13 A t s) = (term14 A t s).
Proof. exact (fun_ext (fun x : A => @lem3320830 A t x s)). Qed.
Lemma lem3320836 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3320837 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term15 A t s) = (term16 A t s).
Proof. exact (MK_COMB (@lem3320836 A) (@lem3320835 A t s)). Qed.
Lemma lem3320842 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3320837 A t s)). Qed.
Lemma lem3320843 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3320844 {A : Type'} (s : A -> Prop) : (term19 A s) = (term20 A s).
Proof. exact (MK_COMB (@lem3320843 A) (@lem3320842 A s)). Qed.
Lemma lem3320849 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3320844 A s)). Qed.
Lemma lem3320850 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3320851 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem3320850 A) (@lem3320849 A)). Qed.
Lemma lem3320856 {A : Type'} : (term24 A) = (term23 A).
Proof. exact (SYM (@lem3320851 A)). Qed.
Lemma lem3320878 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3320879 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (@lem3320878 A s x t). Qed.
Lemma lem3320880 {A : Type'} (s : A -> Prop) (x : A) (x' : A) (t : A -> Prop) : (term27 A x' s x t) = (term28 A s x x' t).
Proof. exact (@lem3320879 A (@DELETE A s x) x' t). Qed.
Lemma lem3320884 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term29 A x s y) = (term30 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3320885 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term29 A x s y) = (term30 A s x y).
Proof. exact (@lem3320884 A s x y). Qed.
Lemma lem3320886 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term29 A x' s x) = (term30 A s x' x).
Proof. exact (@lem3320885 A s x' x). Qed.
Lemma lem3320890 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3320891 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3320890 A P x). Qed.
Lemma lem3320892 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3320891 A s x'). Qed.
Lemma lem3320893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3320894 {A : Type'} (s : A -> Prop) (x' : A) : (term31 A x' s) = (term32 A s x').
Proof. exact (MK_COMB (@lem3320893) (@lem3320892 A s x')). Qed.
Lemma lem3320897 {A : Type'} (x' : A) (x : A) : (term33 A x' x) = (term33 A x' x).
Proof. exact (eq_refl (term33 A x' x)). Qed.
Lemma lem3320898 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term30 A s x' x) = (term34 A s x' x).
Proof. exact (MK_COMB (@lem3320894 A s x') (@lem3320897 A x' x)). Qed.
Lemma lem3320901 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term29 A x' s x) = (term34 A s x' x).
Proof. exact (TRANS (@lem3320886 A s x' x) (@lem3320898 A s x' x)). Qed.
Lemma lem3320902 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3320903 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term35 A x' s x) = (term36 A s x' x).
Proof. exact (MK_COMB (@lem3320902) (@lem3320901 A s x' x)). Qed.
Lemma lem3320905 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3320906 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3320905 A P x). Qed.
Lemma lem3320907 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3320906 A t x'). Qed.
Lemma lem3320908 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term28 A s x x' t) = (term37 A s x t x').
Proof. exact (MK_COMB (@lem3320903 A s x' x) (@lem3320907 A t x')). Qed.
Lemma lem3320911 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term27 A x' s x t) = (term37 A s x t x').
Proof. exact (TRANS (@lem3320880 A s x x' t) (@lem3320908 A s x t x')). Qed.
Lemma lem3320912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3320913 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term38 A x' s x t) = (term39 A s x t x').
Proof. exact (MK_COMB (@lem3320912) (@lem3320911 A s x t x')). Qed.
Lemma lem3320915 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3320916 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3320915 A x). Qed.
Lemma lem3320917 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem3320916 A x'). Qed.
Lemma lem3320918 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : ((term27 A x' s x t) = (@IN A x' (@EMPTY A))) = ((term37 A s x t x') = False).
Proof. exact (MK_COMB (@lem3320913 A s x t x') (@lem3320917 A x')). Qed.
Lemma lem3320920 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3320921 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : ((term37 A s x t x') = False) = (term40 A s x t x').
Proof. exact (@lem3320920 (term37 A s x t x')). Qed.
Lemma lem3320928 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : ((term27 A x' s x t) = (@IN A x' (@EMPTY A))) = (term40 A s x t x').
Proof. exact (TRANS (@lem3320918 A s x t x') (@lem3320921 A s x t x')). Qed.
Lemma lem3320929 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term41 A s x t) = (term42 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3320928 A s x t x')). Qed.
Lemma lem3320930 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3320931 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A s x t) = (term43 A s x t).
Proof. exact (MK_COMB (@lem3320930 A) (@lem3320929 A s x t)). Qed.
Lemma lem3320936 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3320937 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A s x t) = (term44 A s x t).
Proof. exact (MK_COMB (@lem3320936) (@lem3320931 A s x t)). Qed.
Lemma lem3320945 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3320946 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term25 A x s t) = (term26 A s x t).
Proof. exact (@lem3320945 A s x t). Qed.
Lemma lem3320947 {A : Type'} (t : A -> Prop) (x : A) (x' : A) (s : A -> Prop) : (term27 A x' t x s) = (term28 A t x x' s).
Proof. exact (@lem3320946 A (@DELETE A t x) x' s). Qed.
Lemma lem3320951 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term29 A x s y) = (term30 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3320952 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term29 A x s y) = (term30 A s x y).
Proof. exact (@lem3320951 A s x y). Qed.
Lemma lem3320953 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term29 A x' t x) = (term30 A t x' x).
Proof. exact (@lem3320952 A t x' x). Qed.
Lemma lem3320957 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3320958 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3320957 A P x). Qed.
Lemma lem3320959 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3320958 A t x'). Qed.
Lemma lem3320960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3320961 {A : Type'} (t : A -> Prop) (x' : A) : (term31 A x' t) = (term32 A t x').
Proof. exact (MK_COMB (@lem3320960) (@lem3320959 A t x')). Qed.
Lemma lem3320964 {A : Type'} (x' : A) (x : A) : (term33 A x' x) = (term33 A x' x).
Proof. exact (eq_refl (term33 A x' x)). Qed.
Lemma lem3320965 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term30 A t x' x) = (term34 A t x' x).
Proof. exact (MK_COMB (@lem3320961 A t x') (@lem3320964 A x' x)). Qed.
Lemma lem3320968 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term29 A x' t x) = (term34 A t x' x).
Proof. exact (TRANS (@lem3320953 A t x' x) (@lem3320965 A t x' x)). Qed.
Lemma lem3320969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3320970 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term35 A x' t x) = (term36 A t x' x).
Proof. exact (MK_COMB (@lem3320969) (@lem3320968 A t x' x)). Qed.
Lemma lem3320972 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3320973 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3320972 A P x). Qed.
Lemma lem3320974 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3320973 A s x'). Qed.
Lemma lem3320975 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term28 A t x x' s) = (term37 A t x s x').
Proof. exact (MK_COMB (@lem3320970 A t x' x) (@lem3320974 A s x')). Qed.
Lemma lem3320978 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term27 A x' t x s) = (term37 A t x s x').
Proof. exact (TRANS (@lem3320947 A t x x' s) (@lem3320975 A t x s x')). Qed.
Lemma lem3320979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3320980 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term38 A x' t x s) = (term39 A t x s x').
Proof. exact (MK_COMB (@lem3320979) (@lem3320978 A t x s x')). Qed.
Lemma lem3320982 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3320983 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3320982 A x). Qed.
Lemma lem3320984 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem3320983 A x'). Qed.
Lemma lem3320985 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : ((term27 A x' t x s) = (@IN A x' (@EMPTY A))) = ((term37 A t x s x') = False).
Proof. exact (MK_COMB (@lem3320980 A t x s x') (@lem3320984 A x')). Qed.
Lemma lem3320987 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3320988 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : ((term37 A t x s x') = False) = (term40 A t x s x').
Proof. exact (@lem3320987 (term37 A t x s x')). Qed.
Lemma lem3320995 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : ((term27 A x' t x s) = (@IN A x' (@EMPTY A))) = (term40 A t x s x').
Proof. exact (TRANS (@lem3320985 A t x s x') (@lem3320988 A t x s x')). Qed.
Lemma lem3320996 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term41 A t x s) = (term42 A t x s).
Proof. exact (fun_ext (fun x' : A => @lem3320995 A t x s x')). Qed.
Lemma lem3320997 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3320998 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term10 A t x s) = (term43 A t x s).
Proof. exact (MK_COMB (@lem3320997 A) (@lem3320996 A t x s)). Qed.
Lemma lem3321003 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : ((term10 A s x t) = (term10 A t x s)) = ((term43 A s x t) = (term43 A t x s)).
Proof. exact (MK_COMB (@lem3320937 A s x t) (@lem3320998 A t x s)). Qed.
Lemma lem3321006 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term14 A t s) = (term45 A t s).
Proof. exact (fun_ext (fun x : A => @lem3321003 A t x s)). Qed.
Lemma lem3321007 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3321008 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term16 A t s) = (term46 A t s).
Proof. exact (MK_COMB (@lem3321007 A) (@lem3321006 A t s)). Qed.
Lemma lem3321013 {A : Type'} (s : A -> Prop) : (term18 A s) = (term47 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3321008 A t s)). Qed.
Lemma lem3321014 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3321015 {A : Type'} (s : A -> Prop) : (term20 A s) = (term48 A s).
Proof. exact (MK_COMB (@lem3321014 A) (@lem3321013 A s)). Qed.
Lemma lem3321020 {A : Type'} : (term22 A) = (term49 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3321015 A s)). Qed.
Lemma lem3321021 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3321022 {A : Type'} : (term24 A) = (term50 A).
Proof. exact (MK_COMB (@lem3321021 A) (@lem3321020 A)). Qed.
Lemma lem3321027 {A : Type'} : (term50 A) = (term24 A).
Proof. exact (SYM (@lem3321022 A)). Qed.
Lemma lem3321029 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3321030 {A : Type'} : (term50 A) = (term52 A).
Proof. exact (@lem3321029 (term50 A)). Qed.
Lemma lem3321031 {A : Type'} : (term52 A) = (term50 A).
Proof. exact (SYM (@lem3321030 A)). Qed.
Lemma lem3321032 {A : Type'} (h1 : term53 A) : term53 A.
Proof. exact (h1). Qed.
Lemma lem3321035 {A : Type'} (h1 : term52 A) : term52 A.
Proof. exact (h1). Qed.
Lemma lem3321036 {A : Type'} : term54 A.
Proof. exact (fun h0 : term52 A => @lem3321035 A h0). Qed.
Lemma lem3321037 {A : Type'} (h1 : term54 A) : term54 A.
Proof. exact (h1). Qed.
Lemma lem3321038 {A : Type'} (h1 : term52 A) : term52 A.
Proof. exact (h1). Qed.
Lemma lem3321039 {A : Type'} (h1 : term52 A) (h2 : term54 A) : term52 A.
Proof. exact (@lem3321037 A h2 (@lem3321038 A h1)). Qed.
Lemma lem3321040 {A : Type'} (h1 : term52 A) : term55 A.
Proof. exact (fun h0 : term54 A => @lem3321039 A h1 h0). Qed.
Lemma lem3321041 {A : Type'} (h1 : term54 A) : term54 A.
Proof. exact (h1). Qed.
Lemma lem3321042 {A : Type'} (h1 : term52 A) (h2 : term54 A) : term52 A.
Proof. exact (@lem3321040 A h1 (@lem3321041 A h2)). Qed.
Lemma lem3321043 {A : Type'} (h1 : term54 A) : term54 A.
Proof. exact (fun h0 : term52 A => @lem3321042 A h0 h1). Qed.
Lemma lem3321044 {A : Type'} : term56 A.
Proof. exact (fun h0 : term54 A => @lem3321043 A h0). Qed.
Lemma lem3321047 {A : Type'} : term54 A.
Proof. exact (@lem3321044 A (@lem3321036 A)). Qed.
Lemma lem3321048 {A : Type'} : term54 A.
Proof. exact (@lem3321047 A). Qed.
Lemma lem3321050 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3321051 {A : Type'} : (term52 A) = (term57 A).
Proof. exact (@lem3321050 (term53 A)). Qed.
Lemma lem3321053 (t : Prop) : (term58 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3321054 {A : Type'} : (term57 A) = (term50 A).
Proof. exact (@lem3321053 (term50 A)). Qed.
Lemma lem3321087 {A : Type'} : (term52 A) = (term50 A).
Proof. exact (TRANS (@lem3321051 A) (@lem3321054 A)). Qed.
Lemma lem3321100 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term40 A t x s x') = (term40 A t x s x').
Proof. exact (eq_refl (term40 A t x s x')). Qed.
Lemma lem3321101 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term42 A t x s) = (term42 A t x s).
Proof. exact (fun_ext (fun x' : A => @lem3321100 A t x s x')). Qed.
Lemma lem3321102 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3321103 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term43 A t x s) = (term43 A t x s).
Proof. exact (MK_COMB (@lem3321102 A) (@lem3321101 A t x s)). Qed.
Lemma lem3321116 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term40 A s x t x') = (term40 A s x t x').
Proof. exact (eq_refl (term40 A s x t x')). Qed.
Lemma lem3321117 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term42 A s x t) = (term42 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3321116 A s x t x')). Qed.
Lemma lem3321118 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3321119 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term43 A s x t) = (term43 A s x t).
Proof. exact (MK_COMB (@lem3321118 A) (@lem3321117 A s x t)). Qed.
Lemma lem3321120 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3321121 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term44 A s x t) = (term44 A s x t).
Proof. exact (MK_COMB (@lem3321120) (@lem3321119 A s x t)). Qed.
Lemma lem3321122 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : ((term43 A s x t) = (term43 A t x s)) = ((term43 A s x t) = (term43 A t x s)).
Proof. exact (MK_COMB (@lem3321121 A s x t) (@lem3321103 A t x s)). Qed.
Lemma lem3321123 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term45 A t s) = (term45 A t s).
Proof. exact (fun_ext (fun x : A => @lem3321122 A t x s)). Qed.
Lemma lem3321124 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3321125 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term46 A t s) = (term46 A t s).
Proof. exact (MK_COMB (@lem3321124 A) (@lem3321123 A t s)). Qed.
Lemma lem3321126 {A : Type'} (s : A -> Prop) : (term47 A s) = (term47 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3321125 A t s)). Qed.
Lemma lem3321127 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3321128 {A : Type'} (s : A -> Prop) : (term48 A s) = (term48 A s).
Proof. exact (MK_COMB (@lem3321127 A) (@lem3321126 A s)). Qed.
Lemma lem3321129 {A : Type'} : (term49 A) = (term49 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3321128 A s)). Qed.
Lemma lem3321130 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3321131 {A : Type'} : (term50 A) = (term50 A).
Proof. exact (MK_COMB (@lem3321130 A) (@lem3321129 A)). Qed.
Lemma lem3321172 {A : Type'} : (term52 A) = (term50 A).
Proof. exact (TRANS (@lem3321087 A) (@lem3321131 A)). Qed.
Lemma lem3321173 {A : Type'} : (term50 A) = (term52 A).
Proof. exact (SYM (@lem3321172 A)). Qed.
Lemma lem3321175 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3321176 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : ((term43 A s x t) = (term43 A t x s)) = (term59 A t x s).
Proof. exact (@lem3321175 ((term43 A s x t) = (term43 A t x s))). Qed.
Lemma lem3321177 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term59 A t x s) = ((term43 A s x t) = (term43 A t x s)).
Proof. exact (SYM (@lem3321176 A t x s)). Qed.
Lemma lem3321178 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term60 A t x s) : term60 A t x s.
Proof. exact (h1). Qed.
Lemma lem3321184 {A : Type'} (x' : A) (x : A) : (term61 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3321186 {A : Type'} (s : A -> Prop) (x' : A) : (term62 A s x') = (term62 A s x').
Proof. exact (eq_refl (term62 A s x')). Qed.
Lemma lem3321187 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term63 A s x' x) = (term64 A s x' x).
Proof. exact (MK_COMB (@lem3321186 A s x') (@lem3321184 A x' x)). Qed.
Lemma lem3321188 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term65 A s x' x) = (term63 A s x' x).
Proof. exact (@lem17045 (s x') (term33 A x' x)). Qed.
Lemma lem3321189 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term65 A s x' x) = (term64 A s x' x).
Proof. exact (TRANS (@lem3321188 A s x' x) (@lem3321187 A s x' x)). Qed.
Lemma lem3321193 {A : Type'} (t : A -> Prop) (x' : A) : (term66 A t x') = (term66 A t x').
Proof. exact (eq_refl (term66 A t x')). Qed.
Lemma lem3321195 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3321196 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term67 A s x' x) = (term68 A s x' x).
Proof. exact (MK_COMB (@lem3321195) (@lem3321189 A s x' x)). Qed.
Lemma lem3321197 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term69 A s x t x') = (term70 A s x t x').
Proof. exact (MK_COMB (@lem3321196 A s x' x) (@lem3321193 A t x')). Qed.
Lemma lem3321198 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term40 A s x t x') = (term69 A s x t x').
Proof. exact (@lem17045 (term34 A s x' x) (t x')). Qed.
Lemma lem3321199 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term40 A s x t x') = (term70 A s x t x').
Proof. exact (TRANS (@lem3321198 A s x t x') (@lem3321197 A s x t x')). Qed.
Lemma lem3321204 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term71 A s x t x') = (term37 A s x t x').
Proof. exact (@lem16933 (term37 A s x t x')). Qed.
Lemma lem3321205 {A : Type'} (P : A -> Prop) : (term72 A P) = (term73 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3321206 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term74 A s x t) = (term75 A s x t).
Proof. exact (@lem3321205 A (term42 A s x t)). Qed.
Lemma lem3321207 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term76 A s x t x') = (term40 A s x t x').
Proof. exact (eq_refl (term76 A s x t x')). Qed.
Lemma lem3321208 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3321209 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term77 A s x t x') = (term71 A s x t x').
Proof. exact (MK_COMB (@lem3321208) (@lem3321207 A s x t x')). Qed.
Lemma lem3321210 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term77 A s x t x') = (term37 A s x t x').
Proof. exact (TRANS (@lem3321209 A s x t x') (@lem3321204 A s x t x')). Qed.
Lemma lem3321211 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term78 A s x t) = (term79 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3321210 A s x t x')). Qed.
Lemma lem3321212 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3321213 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term75 A s x t) = (term80 A s x t).
Proof. exact (MK_COMB (@lem3321212 A) (@lem3321211 A s x t)). Qed.
Lemma lem3321214 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term74 A s x t) = (term80 A s x t).
Proof. exact (TRANS (@lem3321206 A s x t) (@lem3321213 A s x t)). Qed.
Lemma lem3321215 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term42 A s x t) = (term81 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3321199 A s x t x')). Qed.
Lemma lem3321216 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3321217 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term43 A s x t) = (term82 A s x t).
Proof. exact (MK_COMB (@lem3321216 A) (@lem3321215 A s x t)). Qed.
Lemma lem3321223 {A : Type'} (x' : A) (x : A) : (term61 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3321225 {A : Type'} (t : A -> Prop) (x' : A) : (term62 A t x') = (term62 A t x').
Proof. exact (eq_refl (term62 A t x')). Qed.
Lemma lem3321226 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term63 A t x' x) = (term64 A t x' x).
Proof. exact (MK_COMB (@lem3321225 A t x') (@lem3321223 A x' x)). Qed.
Lemma lem3321227 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term65 A t x' x) = (term63 A t x' x).
Proof. exact (@lem17045 (t x') (term33 A x' x)). Qed.
Lemma lem3321228 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term65 A t x' x) = (term64 A t x' x).
Proof. exact (TRANS (@lem3321227 A t x' x) (@lem3321226 A t x' x)). Qed.
Lemma lem3321232 {A : Type'} (s : A -> Prop) (x' : A) : (term66 A s x') = (term66 A s x').
Proof. exact (eq_refl (term66 A s x')). Qed.
Lemma lem3321234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3321235 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term67 A t x' x) = (term68 A t x' x).
Proof. exact (MK_COMB (@lem3321234) (@lem3321228 A t x' x)). Qed.
Lemma lem3321236 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term69 A t x s x') = (term70 A t x s x').
Proof. exact (MK_COMB (@lem3321235 A t x' x) (@lem3321232 A s x')). Qed.
Lemma lem3321237 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term40 A t x s x') = (term69 A t x s x').
Proof. exact (@lem17045 (term34 A t x' x) (s x')). Qed.
Lemma lem3321238 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term40 A t x s x') = (term70 A t x s x').
Proof. exact (TRANS (@lem3321237 A t x s x') (@lem3321236 A t x s x')). Qed.
Lemma lem3321243 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term71 A t x s x') = (term37 A t x s x').
Proof. exact (@lem16933 (term37 A t x s x')). Qed.
Lemma lem3321244 {A : Type'} (P : A -> Prop) : (term72 A P) = (term73 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3321245 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term74 A t x s) = (term75 A t x s).
Proof. exact (@lem3321244 A (term42 A t x s)). Qed.
Lemma lem3321246 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term76 A t x s x') = (term40 A t x s x').
Proof. exact (eq_refl (term76 A t x s x')). Qed.
Lemma lem3321247 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3321248 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term77 A t x s x') = (term71 A t x s x').
Proof. exact (MK_COMB (@lem3321247) (@lem3321246 A t x s x')). Qed.
Lemma lem3321249 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term77 A t x s x') = (term37 A t x s x').
Proof. exact (TRANS (@lem3321248 A t x s x') (@lem3321243 A t x s x')). Qed.
Lemma lem3321250 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term78 A t x s) = (term79 A t x s).
Proof. exact (fun_ext (fun x' : A => @lem3321249 A t x s x')). Qed.
Lemma lem3321251 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3321252 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term75 A t x s) = (term80 A t x s).
Proof. exact (MK_COMB (@lem3321251 A) (@lem3321250 A t x s)). Qed.
Lemma lem3321253 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term74 A t x s) = (term80 A t x s).
Proof. exact (TRANS (@lem3321245 A t x s) (@lem3321252 A t x s)). Qed.
Lemma lem3321254 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term42 A t x s) = (term81 A t x s).
Proof. exact (fun_ext (fun x' : A => @lem3321238 A t x s x')). Qed.
Lemma lem3321255 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3321256 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term43 A t x s) = (term82 A t x s).
Proof. exact (MK_COMB (@lem3321255 A) (@lem3321254 A t x s)). Qed.
Lemma lem3321257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3321258 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term83 A s x t) = (term84 A s x t).
Proof. exact (MK_COMB (@lem3321257) (@lem3321214 A s x t)). Qed.
Lemma lem3321259 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term85 A t x s) = (term86 A t x s).
Proof. exact (MK_COMB (@lem3321258 A s x t) (@lem3321256 A t x s)). Qed.
Lemma lem3321260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3321261 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term87 A s x t) = (term88 A s x t).
Proof. exact (MK_COMB (@lem3321260) (@lem3321217 A s x t)). Qed.
Lemma lem3321262 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term89 A t x s) = (term90 A t x s).
Proof. exact (MK_COMB (@lem3321261 A s x t) (@lem3321253 A t x s)). Qed.
Lemma lem3321263 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3321264 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term91 A t x s) = (term92 A t x s).
Proof. exact (MK_COMB (@lem3321263) (@lem3321262 A t x s)). Qed.
Lemma lem3321265 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term93 A t x s) = (term94 A t x s).
Proof. exact (MK_COMB (@lem3321264 A t x s) (@lem3321259 A t x s)). Qed.
Lemma lem3321266 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term60 A t x s) = (term93 A t x s).
Proof. exact (@lem17646 (term43 A s x t) (term43 A t x s)). Qed.
Lemma lem3321267 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term60 A t x s) = (term94 A t x s).
Proof. exact (TRANS (@lem3321266 A t x s) (@lem3321265 A t x s)). Qed.
Lemma lem3321430 {A : Type'} (P : Prop) (Q : A -> Prop) : (term95 A P Q) = (term96 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3321431 {A : Type'} (P : Prop) (Q : A -> Prop) : (term95 A P Q) = (term96 A P Q).
Proof. exact (@lem3321430 A P Q). Qed.
Lemma lem3321432 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term97 A t x s) = (term98 A t x s).
Proof. exact (@lem3321431 A (term82 A s x t) (term79 A t x s)). Qed.
Lemma lem3321433 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term99 A t x s x') = (term37 A t x s x').
Proof. exact (eq_refl (term99 A t x s x')). Qed.
Lemma lem3321434 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term100 A t x s) = (term79 A t x s).
Proof. exact (fun_ext (fun x' : A => @lem3321433 A t x s x')). Qed.
Lemma lem3321435 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3321436 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term101 A t x s) = (term80 A t x s).
Proof. exact (MK_COMB (@lem3321435 A) (@lem3321434 A t x s)). Qed.
Lemma lem3321437 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term88 A s x t) = (term88 A s x t).
Proof. exact (eq_refl (term88 A s x t)). Qed.
Lemma lem3321438 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term97 A t x s) = (term90 A t x s).
Proof. exact (MK_COMB (@lem3321437 A s x t) (@lem3321436 A t x s)). Qed.
Lemma lem3321439 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3321440 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term102 A t x s) = (term103 A t x s).
Proof. exact (MK_COMB (@lem3321439) (@lem3321438 A t x s)). Qed.
Lemma lem3321441 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term99 A t x s x') = (term37 A t x s x').
Proof. exact (eq_refl (term99 A t x s x')). Qed.
Lemma lem3321442 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term88 A s x t) = (term88 A s x t).
Proof. exact (eq_refl (term88 A s x t)). Qed.
Lemma lem3321443 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term104 A t x s x') = (term105 A t x s x').
Proof. exact (MK_COMB (@lem3321442 A s x t) (@lem3321441 A t x s x')). Qed.
Lemma lem3321444 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term106 A t x s) = (term107 A t x s).
Proof. exact (fun_ext (fun x' : A => @lem3321443 A t x s x')). Qed.
Lemma lem3321445 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3321446 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term98 A t x s) = (term108 A t x s).
Proof. exact (MK_COMB (@lem3321445 A) (@lem3321444 A t x s)). Qed.
Lemma lem3321447 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : ((term97 A t x s) = (term98 A t x s)) = ((term90 A t x s) = (term108 A t x s)).
Proof. exact (MK_COMB (@lem3321440 A t x s) (@lem3321446 A t x s)). Qed.
Lemma lem3321448 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term90 A t x s) = (term108 A t x s).
Proof. exact (EQ_MP (@lem3321447 A t x s) (@lem3321432 A t x s)). Qed.
Lemma lem3321449 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3321450 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term92 A t x s) = (term109 A t x s).
Proof. exact (MK_COMB (@lem3321449) (@lem3321448 A t x s)). Qed.
Lemma lem3321452 {A : Type'} (P : A -> Prop) (Q : Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3321453 {A : Type'} (P : A -> Prop) (Q : Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (@lem3321452 A P Q). Qed.
Lemma lem3321454 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term112 A t x s) = (term113 A t x s).
Proof. exact (@lem3321453 A (term79 A s x t) (term82 A t x s)). Qed.
Lemma lem3321455 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term99 A s x t x') = (term37 A s x t x').
Proof. exact (eq_refl (term99 A s x t x')). Qed.
Lemma lem3321456 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term100 A s x t) = (term79 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3321455 A s x t x')). Qed.
Lemma lem3321457 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3321458 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term101 A s x t) = (term80 A s x t).
Proof. exact (MK_COMB (@lem3321457 A) (@lem3321456 A s x t)). Qed.
Lemma lem3321459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3321460 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term114 A s x t) = (term84 A s x t).
Proof. exact (MK_COMB (@lem3321459) (@lem3321458 A s x t)). Qed.
Lemma lem3321461 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term82 A t x s) = (term82 A t x s).
Proof. exact (eq_refl (term82 A t x s)). Qed.
Lemma lem3321462 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term112 A t x s) = (term86 A t x s).
Proof. exact (MK_COMB (@lem3321460 A s x t) (@lem3321461 A t x s)). Qed.
Lemma lem3321463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3321464 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term115 A t x s) = (term116 A t x s).
Proof. exact (MK_COMB (@lem3321463) (@lem3321462 A t x s)). Qed.
Lemma lem3321465 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term99 A s x t x') = (term37 A s x t x').
Proof. exact (eq_refl (term99 A s x t x')). Qed.
Lemma lem3321466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3321467 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term117 A s x t x') = (term118 A s x t x').
Proof. exact (MK_COMB (@lem3321466) (@lem3321465 A s x t x')). Qed.
Lemma lem3321468 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term82 A t x s) = (term82 A t x s).
Proof. exact (eq_refl (term82 A t x s)). Qed.
Lemma lem3321469 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) : (term119 A x' t x s) = (term120 A x' t x s).
Proof. exact (MK_COMB (@lem3321467 A s x t x') (@lem3321468 A t x s)). Qed.
Lemma lem3321470 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term121 A t x s) = (term122 A t x s).
Proof. exact (fun_ext (fun x' : A => @lem3321469 A x' t x s)). Qed.
Lemma lem3321471 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3321472 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term113 A t x s) = (term123 A t x s).
Proof. exact (MK_COMB (@lem3321471 A) (@lem3321470 A t x s)). Qed.
Lemma lem3321473 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : ((term112 A t x s) = (term113 A t x s)) = ((term86 A t x s) = (term123 A t x s)).
Proof. exact (MK_COMB (@lem3321464 A t x s) (@lem3321472 A t x s)). Qed.
Lemma lem3321474 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term86 A t x s) = (term123 A t x s).
Proof. exact (EQ_MP (@lem3321473 A t x s) (@lem3321454 A t x s)). Qed.
Lemma lem3321475 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term94 A t x s) = (term124 A t x s).
Proof. exact (MK_COMB (@lem3321450 A t x s) (@lem3321474 A t x s)). Qed.
Lemma lem3321477 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term125 A P Q) = (term126 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3321478 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term125 A P Q) = (term126 A P Q).
Proof. exact (@lem3321477 A P Q). Qed.
Lemma lem3321479 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term127 A t x s) = (term128 A t x s).
Proof. exact (@lem3321478 A (term107 A t x s) (term122 A t x s)). Qed.
Lemma lem3321480 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term129 A t x s x') = (term105 A t x s x').
Proof. exact (eq_refl (term129 A t x s x')). Qed.
Lemma lem3321481 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term130 A t x s) = (term107 A t x s).
Proof. exact (fun_ext (fun x' : A => @lem3321480 A t x s x')). Qed.
Lemma lem3321482 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3321483 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term131 A t x s) = (term108 A t x s).
Proof. exact (MK_COMB (@lem3321482 A) (@lem3321481 A t x s)). Qed.
Lemma lem3321484 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3321485 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term132 A t x s) = (term109 A t x s).
Proof. exact (MK_COMB (@lem3321484) (@lem3321483 A t x s)). Qed.
Lemma lem3321486 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) : (term133 A t x s x') = (term120 A x' t x s).
Proof. exact (eq_refl (term133 A t x s x')). Qed.
Lemma lem3321487 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term134 A t x s) = (term122 A t x s).
Proof. exact (fun_ext (fun x' : A => @lem3321486 A x' t x s)). Qed.
Lemma lem3321488 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3321489 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term135 A t x s) = (term123 A t x s).
Proof. exact (MK_COMB (@lem3321488 A) (@lem3321487 A t x s)). Qed.
Lemma lem3321490 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term127 A t x s) = (term124 A t x s).
Proof. exact (MK_COMB (@lem3321485 A t x s) (@lem3321489 A t x s)). Qed.
Lemma lem3321491 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3321492 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term136 A t x s) = (term137 A t x s).
Proof. exact (MK_COMB (@lem3321491) (@lem3321490 A t x s)). Qed.
Lemma lem3321493 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term129 A t x s x') = (term105 A t x s x').
Proof. exact (eq_refl (term129 A t x s x')). Qed.
Lemma lem3321494 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3321495 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term138 A t x s x') = (term139 A t x s x').
Proof. exact (MK_COMB (@lem3321494) (@lem3321493 A t x s x')). Qed.
Lemma lem3321496 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) : (term133 A t x s x') = (term120 A x' t x s).
Proof. exact (eq_refl (term133 A t x s x')). Qed.
Lemma lem3321497 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) : (term140 A t x s x') = (term141 A x' t x s).
Proof. exact (MK_COMB (@lem3321495 A t x s x') (@lem3321496 A x' t x s)). Qed.
Lemma lem3321498 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term142 A t x s) = (term143 A t x s).
Proof. exact (fun_ext (fun x' : A => @lem3321497 A x' t x s)). Qed.
Lemma lem3321499 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3321500 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term128 A t x s) = (term144 A t x s).
Proof. exact (MK_COMB (@lem3321499 A) (@lem3321498 A t x s)). Qed.
Lemma lem3321501 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : ((term127 A t x s) = (term128 A t x s)) = ((term124 A t x s) = (term144 A t x s)).
Proof. exact (MK_COMB (@lem3321492 A t x s) (@lem3321500 A t x s)). Qed.
Lemma lem3321502 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term124 A t x s) = (term144 A t x s).
Proof. exact (EQ_MP (@lem3321501 A t x s) (@lem3321479 A t x s)). Qed.
Lemma lem3321504 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term94 A t x s) = (term144 A t x s).
Proof. exact (TRANS (@lem3321475 A t x s) (@lem3321502 A t x s)). Qed.
Lemma lem3321505 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term60 A t x s) = (term144 A t x s).
Proof. exact (TRANS (@lem3321267 A t x s) (@lem3321504 A t x s)). Qed.
Lemma lem3321506 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term60 A t x s) : term144 A t x s.
Proof. exact (EQ_MP (@lem3321505 A t x s) (@lem3321178 A t x s h1)). Qed.
Lemma lem3321507 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term141 A x' t x s) : term141 A x' t x s.
Proof. exact (h1). Qed.
Lemma lem3321528 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term70 A t x s x') = (term70 A t x s x').
Proof. exact (eq_refl (term70 A t x s x')). Qed.
Lemma lem3321529 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term81 A t x s) = (term81 A t x s).
Proof. exact (fun_ext (fun x' : A => @lem3321528 A t x s x')). Qed.
Lemma lem3321530 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3321531 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term82 A t x s) = (term82 A t x s).
Proof. exact (MK_COMB (@lem3321530 A) (@lem3321529 A t x s)). Qed.
Lemma lem3321552 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term118 A s x t x') = (term118 A s x t x').
Proof. exact (eq_refl (term118 A s x t x')). Qed.
Lemma lem3321553 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) : (term120 A x' t x s) = (term120 A x' t x s).
Proof. exact (MK_COMB (@lem3321552 A s x t x') (@lem3321531 A t x s)). Qed.
Lemma lem3321572 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term37 A t x s x') = (term37 A t x s x').
Proof. exact (eq_refl (term37 A t x s x')). Qed.
Lemma lem3321593 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term70 A s x t x') = (term70 A s x t x').
Proof. exact (eq_refl (term70 A s x t x')). Qed.
Lemma lem3321594 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term81 A s x t) = (term81 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3321593 A s x t x')). Qed.
Lemma lem3321595 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3321596 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term82 A s x t) = (term82 A s x t).
Proof. exact (MK_COMB (@lem3321595 A) (@lem3321594 A s x t)). Qed.
Lemma lem3321597 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3321598 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term88 A s x t) = (term88 A s x t).
Proof. exact (MK_COMB (@lem3321597) (@lem3321596 A s x t)). Qed.
Lemma lem3321599 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term105 A t x s x') = (term105 A t x s x').
Proof. exact (MK_COMB (@lem3321598 A s x t) (@lem3321572 A t x s x')). Qed.
Lemma lem3321600 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3321601 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term139 A t x s x') = (term139 A t x s x').
Proof. exact (MK_COMB (@lem3321600) (@lem3321599 A t x s x')). Qed.
Lemma lem3321602 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) : (term141 A x' t x s) = (term141 A x' t x s).
Proof. exact (MK_COMB (@lem3321601 A t x s x') (@lem3321553 A x' t x s)). Qed.
Lemma lem3321603 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term141 A x' t x s) : term141 A x' t x s.
Proof. exact (EQ_MP (@lem3321602 A x' t x s) (@lem3321507 A x' t x s h1)). Qed.
Lemma lem3321604 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term105 A t x s x'.
Proof. exact (h1). Qed.
Lemma lem3321605 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term120 A x' t x s.
Proof. exact (h1). Qed.
Lemma lem3321606 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term37 A t x s x'.
Proof. exact (proj2 (@lem3321604 A t x s x' h1)). Qed.
Lemma lem3321607 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term82 A s x t.
Proof. exact (proj1 (@lem3321604 A t x s x' h1)). Qed.
Lemma lem3321609 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term34 A t x' x.
Proof. exact (proj1 (@lem3321606 A t x s x' h1)). Qed.
Lemma lem3321612 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term82 A t x s.
Proof. exact (proj2 (@lem3321605 A x' t x s h1)). Qed.
Lemma lem3321613 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term37 A s x t x'.
Proof. exact (proj1 (@lem3321605 A x' t x s h1)). Qed.
Lemma lem3321615 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term34 A s x' x.
Proof. exact (proj1 (@lem3321613 A x' t x s h1)). Qed.
Lemma lem3321631 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (x' : A) : (term70 A s x t x') = (term70 A s x t x').
Proof. exact (eq_refl (term70 A s x t x')). Qed.
Lemma lem3321632 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term81 A s x t) = (term81 A s x t).
Proof. exact (fun_ext (fun x' : A => @lem3321631 A s x t x')). Qed.
Lemma lem3321633 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3321635 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term82 A s x t) = (term82 A s x t).
Proof. exact (MK_COMB (@lem3321633 A) (@lem3321632 A s x t)). Qed.
Lemma lem3321636 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term82 A s x t.
Proof. exact (EQ_MP (@lem3321635 A s x t) (@lem3321607 A t x s x' h1)). Qed.
Lemma lem3321662 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) : (term70 A t x s x') = (term70 A t x s x').
Proof. exact (eq_refl (term70 A t x s x')). Qed.
Lemma lem3321663 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term81 A t x s) = (term81 A t x s).
Proof. exact (fun_ext (fun x' : A => @lem3321662 A t x s x')). Qed.
Lemma lem3321664 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3321666 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term82 A t x s) = (term82 A t x s).
Proof. exact (MK_COMB (@lem3321664 A) (@lem3321663 A t x s)). Qed.
Lemma lem3321667 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term82 A t x s.
Proof. exact (EQ_MP (@lem3321666 A t x s) (@lem3321612 A x' t x s h1)). Qed.
Lemma lem3321680 {A : Type'} (_34454 : A) (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term145 A s x t _34454.
Proof. exact (@lem3321636 A t x s x' h1 _34454). Qed.
Lemma lem3321681 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (_34454 : A) : (term145 A s x t _34454) = (term70 A s x t _34454).
Proof. exact (eq_refl (term145 A s x t _34454)). Qed.
Lemma lem3321682 {A : Type'} (_34454 : A) (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term70 A s x t _34454.
Proof. exact (EQ_MP (@lem3321681 A s x t _34454) (@lem3321680 A _34454 t x s x' h1)). Qed.
Lemma lem3321683 {A : Type'} (_34455 : A) (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term145 A t x s _34455.
Proof. exact (@lem3321667 A x' t x s h1 _34455). Qed.
Lemma lem3321684 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34455 : A) : (term145 A t x s _34455) = (term70 A t x s _34455).
Proof. exact (eq_refl (term145 A t x s _34455)). Qed.
Lemma lem3321685 {A : Type'} (_34455 : A) (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term70 A t x s _34455.
Proof. exact (EQ_MP (@lem3321684 A t x s _34455) (@lem3321683 A _34455 x' t x s h1)). Qed.
Lemma lem3321696 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (_34454 : A) : (term70 A s x t _34454) = (term146 A s x t _34454).
Proof. exact (@lem3320773 (term66 A s _34454) (_34454 = x) (term66 A t _34454)). Qed.
Lemma lem3321697 {A : Type'} (_34454 : A) (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term146 A s x t _34454.
Proof. exact (EQ_MP (@lem3321696 A s x t _34454) (@lem3321682 A _34454 t x s x' h1)). Qed.
Lemma lem3321703 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term33 A x' x.
Proof. exact (proj2 (@lem3321609 A t x s x' h1)). Qed.
Lemma lem3321714 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (_34455 : A) : (term70 A t x s _34455) = (term146 A t x s _34455).
Proof. exact (@lem3320773 (term66 A t _34455) (_34455 = x) (term66 A s _34455)). Qed.
Lemma lem3321715 {A : Type'} (_34455 : A) (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term146 A t x s _34455.
Proof. exact (EQ_MP (@lem3321714 A t x s _34455) (@lem3321685 A _34455 x' t x s h1)). Qed.
Lemma lem3321721 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term33 A x' x.
Proof. exact (proj2 (@lem3321615 A x' t x s h1)). Qed.
Lemma lem3321749 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : s x'.
Proof. exact (proj2 (@lem3321606 A t x s x' h1)). Qed.
Lemma lem3321750 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term147 A s x'.
Proof. exact (fun h0 : term66 A s x' => @lem3321749 A t x s x' h1). Qed.
Lemma lem3321752 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3321753 {A : Type'} (s : A -> Prop) (x' : A) : (term147 A s x') = (s x').
Proof. exact (@lem3321752 (s x')). Qed.
Lemma lem3321754 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : s x'.
Proof. exact (EQ_MP (@lem3321753 A s x') (@lem3321750 A t x s x' h1)). Qed.
Lemma lem3321756 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : t x'.
Proof. exact (proj1 (@lem3321609 A t x s x' h1)). Qed.
Lemma lem3321757 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term147 A t x'.
Proof. exact (fun h0 : term66 A t x' => @lem3321756 A t x s x' h1). Qed.
Lemma lem3321759 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3321760 {A : Type'} (t : A -> Prop) (x' : A) : (term147 A t x') = (t x').
Proof. exact (@lem3321759 (t x')). Qed.
Lemma lem3321761 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : t x'.
Proof. exact (EQ_MP (@lem3321760 A t x') (@lem3321757 A t x s x' h1)). Qed.
Lemma lem3321767 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3321768 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34454 : A) : (term146 A s x t _34454) = (term149 A x s t _34454).
Proof. exact (@lem3321767 (_34454 = x) (term66 A s _34454) (term66 A t _34454)). Qed.
Lemma lem3321786 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3321787 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34454 : A) : (term150 A s x t _34454) = (term151 A x s t _34454).
Proof. exact (MK_COMB (@lem3321786) (@lem3321768 A x s t _34454)). Qed.
Lemma lem3321805 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34454 : A) : (term149 A x s t _34454) = (term149 A x s t _34454).
Proof. exact (eq_refl (term149 A x s t _34454)). Qed.
Lemma lem3321806 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34454 : A) : ((term146 A s x t _34454) = (term149 A x s t _34454)) = ((term149 A x s t _34454) = (term149 A x s t _34454)).
Proof. exact (MK_COMB (@lem3321787 A x s t _34454) (@lem3321805 A x s t _34454)). Qed.
Lemma lem3321808 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3321809 (x : Prop) : (x = x) = True.
Proof. exact (@lem3321808 Prop x). Qed.
Lemma lem3321810 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34454 : A) : ((term149 A x s t _34454) = (term149 A x s t _34454)) = True.
Proof. exact (@lem3321809 (term149 A x s t _34454)). Qed.
Lemma lem3321811 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34454 : A) : ((term146 A s x t _34454) = (term149 A x s t _34454)) = True.
Proof. exact (TRANS (@lem3321806 A x s t _34454) (@lem3321810 A x s t _34454)). Qed.
Lemma lem3321812 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34454 : A) : True = ((term146 A s x t _34454) = (term149 A x s t _34454)).
Proof. exact (SYM (@lem3321811 A x s t _34454)). Qed.
Lemma lem3321813 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34454 : A) : (term146 A s x t _34454) = (term149 A x s t _34454).
Proof. exact (EQ_MP (@lem3321812 A x s t _34454) (@lem0)). Qed.
Lemma lem3321814 {A : Type'} (_34454 : A) (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term149 A x s t _34454.
Proof. exact (EQ_MP (@lem3321813 A x s t _34454) (@lem3321697 A _34454 t x s x' h1)). Qed.
Lemma lem3321816 (b : Prop) (a : Prop) : (a \/ b) = (term152 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3321817 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34454 : A) (x : A) : (term149 A x s t _34454) = (term153 A s t _34454 x).
Proof. exact (@lem3321816 (term154 A s t _34454) (_34454 = x)). Qed.
Lemma lem3321819 (a : Prop) (b : Prop) : (term155 a b) = (term156 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3321820 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34454 : A) : (term157 A s t _34454) = (term158 A s t _34454).
Proof. exact (@lem3321819 (term66 A s _34454) (term66 A t _34454)). Qed.
Lemma lem3321822 (a : Prop) : (term58 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3321823 {A : Type'} (s : A -> Prop) (_34454 : A) : (term159 A s _34454) = (s _34454).
Proof. exact (@lem3321822 (s _34454)). Qed.
Lemma lem3321824 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3321825 {A : Type'} (s : A -> Prop) (_34454 : A) : (term160 A s _34454) = (term32 A s _34454).
Proof. exact (MK_COMB (@lem3321824) (@lem3321823 A s _34454)). Qed.
Lemma lem3321827 (a : Prop) : (term58 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3321828 {A : Type'} (t : A -> Prop) (_34454 : A) : (term159 A t _34454) = (t _34454).
Proof. exact (@lem3321827 (t _34454)). Qed.
Lemma lem3321829 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34454 : A) : (term158 A s t _34454) = (term161 A s t _34454).
Proof. exact (MK_COMB (@lem3321825 A s _34454) (@lem3321828 A t _34454)). Qed.
Lemma lem3321830 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34454 : A) : (term157 A s t _34454) = (term161 A s t _34454).
Proof. exact (TRANS (@lem3321820 A s t _34454) (@lem3321829 A s t _34454)). Qed.
Lemma lem3321831 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3321832 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34454 : A) : (term162 A s t _34454) = (term163 A s t _34454).
Proof. exact (MK_COMB (@lem3321831) (@lem3321830 A s t _34454)). Qed.
Lemma lem3321833 {A : Type'} (_34454 : A) (x : A) : (_34454 = x) = (_34454 = x).
Proof. exact (eq_refl (_34454 = x)). Qed.
Lemma lem3321834 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34454 : A) (x : A) : (term153 A s t _34454 x) = (term164 A s t _34454 x).
Proof. exact (MK_COMB (@lem3321832 A s t _34454) (@lem3321833 A _34454 x)). Qed.
Lemma lem3321835 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34454 : A) (x : A) : (term149 A x s t _34454) = (term164 A s t _34454 x).
Proof. exact (TRANS (@lem3321817 A s t _34454 x) (@lem3321834 A s t _34454 x)). Qed.
Lemma lem3321837 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term161 A s t x'.
Proof. exact (conj (@lem3321754 A t x s x' h1) (@lem3321761 A t x s x' h1)). Qed.
Lemma lem3321839 {A : Type'} (_34454 : A) (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term164 A s t _34454 x.
Proof. exact (EQ_MP (@lem3321835 A s t _34454 x) (@lem3321814 A _34454 t x s x' h1)). Qed.
Lemma lem3321840 {A : Type'} (_34454 : A) (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term164 A s t _34454 x.
Proof. exact (@lem3321839 A _34454 t x s x' h1). Qed.
Lemma lem3321841 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term164 A s t x' x.
Proof. exact (@lem3321840 A x' t x s x' h1). Qed.
Lemma lem3321844 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : x' = x.
Proof. exact (@lem3321841 A t x s x' h1 (@lem3321837 A t x s x' h1)). Qed.
Lemma lem3321845 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term165 A x' x.
Proof. exact (fun h0 : term33 A x' x => @lem3321844 A t x s x' h1). Qed.
Lemma lem3321847 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3321848 {A : Type'} (x' : A) (x : A) : (term165 A x' x) = (x' = x).
Proof. exact (@lem3321847 (x' = x)). Qed.
Lemma lem3321849 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : x' = x.
Proof. exact (EQ_MP (@lem3321848 A x' x) (@lem3321845 A t x s x' h1)). Qed.
Lemma lem3321852 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3321854 {A : Type'} (x' : A) (x : A) : (term33 A x' x) = (term166 A x' x).
Proof. exact (@lem3321852 (x' = x)). Qed.
Lemma lem3321857 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term166 A x' x.
Proof. exact (EQ_MP (@lem3321854 A x' x) (@lem3321703 A t x s x' h1)). Qed.
Lemma lem3321860 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : False.
Proof. exact (@lem3321857 A t x s x' h1 (@lem3321849 A t x s x' h1)). Qed.
Lemma lem3321861 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : term167.
Proof. exact (fun h0 : ~ False => @lem3321860 A t x s x' h1). Qed.
Lemma lem3321863 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3321864 : term167 = False.
Proof. exact (@lem3321863 False). Qed.
Lemma lem3321865 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term105 A t x s x') : False.
Proof. exact (EQ_MP (@lem3321864) (@lem3321861 A t x s x' h1)). Qed.
Lemma lem3321893 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : t x'.
Proof. exact (proj2 (@lem3321613 A x' t x s h1)). Qed.
Lemma lem3321894 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term147 A t x'.
Proof. exact (fun h0 : term66 A t x' => @lem3321893 A x' t x s h1). Qed.
Lemma lem3321896 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3321897 {A : Type'} (t : A -> Prop) (x' : A) : (term147 A t x') = (t x').
Proof. exact (@lem3321896 (t x')). Qed.
Lemma lem3321898 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : t x'.
Proof. exact (EQ_MP (@lem3321897 A t x') (@lem3321894 A x' t x s h1)). Qed.
Lemma lem3321900 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : s x'.
Proof. exact (proj1 (@lem3321615 A x' t x s h1)). Qed.
Lemma lem3321901 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term147 A s x'.
Proof. exact (fun h0 : term66 A s x' => @lem3321900 A x' t x s h1). Qed.
Lemma lem3321903 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3321904 {A : Type'} (s : A -> Prop) (x' : A) : (term147 A s x') = (s x').
Proof. exact (@lem3321903 (s x')). Qed.
Lemma lem3321905 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : s x'.
Proof. exact (EQ_MP (@lem3321904 A s x') (@lem3321901 A x' t x s h1)). Qed.
Lemma lem3321911 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3321912 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (_34455 : A) : (term146 A t x s _34455) = (term149 A x t s _34455).
Proof. exact (@lem3321911 (_34455 = x) (term66 A t _34455) (term66 A s _34455)). Qed.
Lemma lem3321928 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3321929 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34455 : A) : (term154 A t s _34455) = (term154 A s t _34455).
Proof. exact (@lem3321928 (term66 A s _34455) (term66 A t _34455)). Qed.
Lemma lem3321935 {A : Type'} (_34455 : A) (x : A) : (term168 A _34455 x) = (term168 A _34455 x).
Proof. exact (eq_refl (term168 A _34455 x)). Qed.
Lemma lem3321936 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34455 : A) : (term149 A x t s _34455) = (term149 A x s t _34455).
Proof. exact (MK_COMB (@lem3321935 A _34455 x) (@lem3321929 A s t _34455)). Qed.
Lemma lem3321947 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34455 : A) : (term146 A t x s _34455) = (term149 A x s t _34455).
Proof. exact (TRANS (@lem3321912 A x t s _34455) (@lem3321936 A x s t _34455)). Qed.
Lemma lem3321948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3321949 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34455 : A) : (term150 A t x s _34455) = (term151 A x s t _34455).
Proof. exact (MK_COMB (@lem3321948) (@lem3321947 A x s t _34455)). Qed.
Lemma lem3321965 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3321966 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34455 : A) : (term154 A t s _34455) = (term154 A s t _34455).
Proof. exact (@lem3321965 (term66 A s _34455) (term66 A t _34455)). Qed.
Lemma lem3321972 {A : Type'} (_34455 : A) (x : A) : (term168 A _34455 x) = (term168 A _34455 x).
Proof. exact (eq_refl (term168 A _34455 x)). Qed.
Lemma lem3321973 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34455 : A) : (term149 A x t s _34455) = (term149 A x s t _34455).
Proof. exact (MK_COMB (@lem3321972 A _34455 x) (@lem3321966 A s t _34455)). Qed.
Lemma lem3321984 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34455 : A) : ((term146 A t x s _34455) = (term149 A x t s _34455)) = ((term149 A x s t _34455) = (term149 A x s t _34455)).
Proof. exact (MK_COMB (@lem3321949 A x s t _34455) (@lem3321973 A x s t _34455)). Qed.
Lemma lem3321986 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3321987 (x : Prop) : (x = x) = True.
Proof. exact (@lem3321986 Prop x). Qed.
Lemma lem3321988 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (_34455 : A) : ((term149 A x s t _34455) = (term149 A x s t _34455)) = True.
Proof. exact (@lem3321987 (term149 A x s t _34455)). Qed.
Lemma lem3321989 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (_34455 : A) : ((term146 A t x s _34455) = (term149 A x t s _34455)) = True.
Proof. exact (TRANS (@lem3321984 A x s t _34455) (@lem3321988 A x s t _34455)). Qed.
Lemma lem3321990 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (_34455 : A) : True = ((term146 A t x s _34455) = (term149 A x t s _34455)).
Proof. exact (SYM (@lem3321989 A x t s _34455)). Qed.
Lemma lem3321991 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (_34455 : A) : (term146 A t x s _34455) = (term149 A x t s _34455).
Proof. exact (EQ_MP (@lem3321990 A x t s _34455) (@lem0)). Qed.
Lemma lem3321992 {A : Type'} (_34455 : A) (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term149 A x t s _34455.
Proof. exact (EQ_MP (@lem3321991 A x t s _34455) (@lem3321715 A _34455 x' t x s h1)). Qed.
Lemma lem3321994 (b : Prop) (a : Prop) : (a \/ b) = (term152 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3321995 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34455 : A) (x : A) : (term149 A x t s _34455) = (term153 A t s _34455 x).
Proof. exact (@lem3321994 (term154 A t s _34455) (_34455 = x)). Qed.
Lemma lem3321997 (a : Prop) (b : Prop) : (term155 a b) = (term156 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3321998 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34455 : A) : (term157 A t s _34455) = (term158 A t s _34455).
Proof. exact (@lem3321997 (term66 A t _34455) (term66 A s _34455)). Qed.
Lemma lem3322000 (a : Prop) : (term58 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3322001 {A : Type'} (t : A -> Prop) (_34455 : A) : (term159 A t _34455) = (t _34455).
Proof. exact (@lem3322000 (t _34455)). Qed.
Lemma lem3322002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3322003 {A : Type'} (t : A -> Prop) (_34455 : A) : (term160 A t _34455) = (term32 A t _34455).
Proof. exact (MK_COMB (@lem3322002) (@lem3322001 A t _34455)). Qed.
Lemma lem3322005 (a : Prop) : (term58 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3322006 {A : Type'} (s : A -> Prop) (_34455 : A) : (term159 A s _34455) = (s _34455).
Proof. exact (@lem3322005 (s _34455)). Qed.
Lemma lem3322007 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34455 : A) : (term158 A t s _34455) = (term161 A t s _34455).
Proof. exact (MK_COMB (@lem3322003 A t _34455) (@lem3322006 A s _34455)). Qed.
Lemma lem3322008 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34455 : A) : (term157 A t s _34455) = (term161 A t s _34455).
Proof. exact (TRANS (@lem3321998 A t s _34455) (@lem3322007 A t s _34455)). Qed.
Lemma lem3322009 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3322010 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34455 : A) : (term162 A t s _34455) = (term163 A t s _34455).
Proof. exact (MK_COMB (@lem3322009) (@lem3322008 A t s _34455)). Qed.
Lemma lem3322011 {A : Type'} (_34455 : A) (x : A) : (_34455 = x) = (_34455 = x).
Proof. exact (eq_refl (_34455 = x)). Qed.
Lemma lem3322012 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34455 : A) (x : A) : (term153 A t s _34455 x) = (term164 A t s _34455 x).
Proof. exact (MK_COMB (@lem3322010 A t s _34455) (@lem3322011 A _34455 x)). Qed.
Lemma lem3322013 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34455 : A) (x : A) : (term149 A x t s _34455) = (term164 A t s _34455 x).
Proof. exact (TRANS (@lem3321995 A t s _34455 x) (@lem3322012 A t s _34455 x)). Qed.
Lemma lem3322015 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term161 A t s x'.
Proof. exact (conj (@lem3321898 A x' t x s h1) (@lem3321905 A x' t x s h1)). Qed.
Lemma lem3322017 {A : Type'} (_34455 : A) (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term164 A t s _34455 x.
Proof. exact (EQ_MP (@lem3322013 A t s _34455 x) (@lem3321992 A _34455 x' t x s h1)). Qed.
Lemma lem3322018 {A : Type'} (_34455 : A) (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term164 A t s _34455 x.
Proof. exact (@lem3322017 A _34455 x' t x s h1). Qed.
Lemma lem3322019 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term164 A t s x' x.
Proof. exact (@lem3322018 A x' x' t x s h1). Qed.
Lemma lem3322022 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : x' = x.
Proof. exact (@lem3322019 A x' t x s h1 (@lem3322015 A x' t x s h1)). Qed.
Lemma lem3322023 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term165 A x' x.
Proof. exact (fun h0 : term33 A x' x => @lem3322022 A x' t x s h1). Qed.
Lemma lem3322025 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3322026 {A : Type'} (x' : A) (x : A) : (term165 A x' x) = (x' = x).
Proof. exact (@lem3322025 (x' = x)). Qed.
Lemma lem3322027 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : x' = x.
Proof. exact (EQ_MP (@lem3322026 A x' x) (@lem3322023 A x' t x s h1)). Qed.
Lemma lem3322030 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3322032 {A : Type'} (x' : A) (x : A) : (term33 A x' x) = (term166 A x' x).
Proof. exact (@lem3322030 (x' = x)). Qed.
Lemma lem3322035 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term166 A x' x.
Proof. exact (EQ_MP (@lem3322032 A x' x) (@lem3321721 A x' t x s h1)). Qed.
Lemma lem3322038 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : False.
Proof. exact (@lem3322035 A x' t x s h1 (@lem3322027 A x' t x s h1)). Qed.
Lemma lem3322039 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : term167.
Proof. exact (fun h0 : ~ False => @lem3322038 A x' t x s h1). Qed.
Lemma lem3322041 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3322042 : term167 = False.
Proof. exact (@lem3322041 False). Qed.
Lemma lem3322043 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term120 A x' t x s) : False.
Proof. exact (EQ_MP (@lem3322042) (@lem3322039 A x' t x s h1)). Qed.
Lemma lem3322044 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term141 A x' t x s) : False.
Proof. exact (or_elim (@lem3321603 A x' t x s h1) (fun h0 : term105 A t x s x' => @lem3321865 A t x s x' h0) (fun h0 : term120 A x' t x s => @lem3322043 A x' t x s h0)). Qed.
Lemma lem3322045 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term141 A x' t x s) : (term141 A x' t x s) = False.
Proof. exact (prop_ext (fun h2 : term141 A x' t x s => @lem3322044 A x' t x s h1) (fun h2 : False => @lem3321603 A x' t x s h1)). Qed.
Lemma lem3322046 {A : Type'} (x' : A) (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term141 A x' t x s) : False.
Proof. exact (EQ_MP (@lem3322045 A x' t x s h1) (@lem3321603 A x' t x s h1)). Qed.
Lemma lem3322047 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term60 A t x s) : False.
Proof. exact (ex_elim (@lem3321506 A t x s h1) (fun x' : A => fun h0 : term143 A t x s x' => @lem3322046 A x' t x s h0)). Qed.
Lemma lem3322048 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term60 A t x s) : (term60 A t x s) = False.
Proof. exact (prop_ext (fun h2 : term60 A t x s => @lem3322047 A t x s h1) (fun h2 : False => @lem3321178 A t x s h1)). Qed.
Lemma lem3322049 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (h1 : term60 A t x s) : False.
Proof. exact (EQ_MP (@lem3322048 A t x s h1) (@lem3321178 A t x s h1)). Qed.
Lemma lem3322050 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : term59 A t x s.
Proof. exact (fun h0 : term60 A t x s => @lem3322049 A t x s h0). Qed.
Lemma lem3322051 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term43 A s x t) = (term43 A t x s).
Proof. exact (EQ_MP (@lem3321177 A t x s) (@lem3322050 A t x s)). Qed.
Lemma lem3322056 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term46 A t s.
Proof. exact (fun x : A => @lem3322051 A t x s). Qed.
Lemma lem3322061 {A : Type'} (s : A -> Prop) : term48 A s.
Proof. exact (fun t : A -> Prop => @lem3322056 A t s). Qed.
Lemma lem3322066 {A : Type'} : term50 A.
Proof. exact (fun s : A -> Prop => @lem3322061 A s). Qed.
Lemma lem3322067 {A : Type'} : term52 A.
Proof. exact (EQ_MP (@lem3321173 A) (@lem3322066 A)). Qed.
Lemma lem3322069 {A : Type'} : term52 A.
Proof. exact (@lem3321048 A (@lem3322067 A)). Qed.
Lemma lem3322070 {A : Type'} (h1 : term53 A) : False.
Proof. exact (@lem3322069 A (@lem3321032 A h1)). Qed.
Lemma lem3322071 {A : Type'} (h1 : term53 A) : (term53 A) = False.
Proof. exact (prop_ext (fun h2 : term53 A => @lem3322070 A h1) (fun h2 : False => @lem3321032 A h1)). Qed.
Lemma lem3322072 {A : Type'} (h1 : term53 A) : False.
Proof. exact (EQ_MP (@lem3322071 A h1) (@lem3321032 A h1)). Qed.
Lemma lem3322073 {A : Type'} : term52 A.
Proof. exact (fun h0 : term53 A => @lem3322072 A h0). Qed.
Lemma lem3322074 {A : Type'} : term50 A.
Proof. exact (EQ_MP (@lem3321031 A) (@lem3322073 A)). Qed.
Lemma lem3322075 {A : Type'} : term24 A.
Proof. exact (EQ_MP (@lem3321027 A) (@lem3322074 A)). Qed.
Lemma lem3322076 {A : Type'} : term23 A.
Proof. exact (EQ_MP (@lem3320856 A) (@lem3322075 A)). Qed.
