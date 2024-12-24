Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUC_INJ_term_abbrevs.
Require Import NUM_REP_RULES_spec.
Require Import SUC_DEF_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm70828_spec.
Lemma lem72735 : mk_num = mk_num.
Proof. exact (eq_refl mk_num). Qed.
Lemma lem72736 : term0.
Proof. exact (proj2 (@lem71256)). Qed.
Lemma lem72737 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem72738 (i : ind) (h1 : term0) : term1 i.
Proof. exact (@lem72737 h1 i). Qed.
Lemma lem72739 (i : ind) : (term1 i) = (term2 i).
Proof. exact (eq_refl (term1 i)). Qed.
Lemma lem72740 (i : ind) (h1 : term0) : term2 i.
Proof. exact (EQ_MP (@lem72739 i) (@lem72738 i h1)). Qed.
Lemma lem72741 (i : ind) (h1 : NUM_REP i) : NUM_REP i.
Proof. exact (h1). Qed.
Lemma lem72742 (i : ind) (h1 : term0) (h2 : NUM_REP i) : term3 i.
Proof. exact (@lem72740 i h1 (@lem72741 i h2)). Qed.
Lemma lem72743 (i : ind) (h1 : NUM_REP i) : term4 i.
Proof. exact (fun h0 : term0 => @lem72742 i h0 h1). Qed.
Lemma lem72744 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem72745 (i : ind) (h1 : term0) (h2 : NUM_REP i) : term3 i.
Proof. exact (@lem72743 i h2 (@lem72744 h1)). Qed.
Lemma lem72746 (i : ind) (h1 : term0) : term2 i.
Proof. exact (fun h0 : NUM_REP i => @lem72745 i h1 h0). Qed.
Lemma lem72747 (h1 : term0) : term0.
Proof. exact (fun i : ind => @lem72746 i h1). Qed.
Lemma lem72748 : term5.
Proof. exact (fun h0 : term0 => @lem72747 h0). Qed.
Lemma lem72749 : term0.
Proof. exact (@lem72748 (@lem72736)). Qed.
Lemma lem72750 (i : ind) : term1 i.
Proof. exact (@lem72749 i). Qed.
Lemma lem72751 (i : ind) : (term1 i) = (term2 i).
Proof. exact (eq_refl (term1 i)). Qed.
Lemma lem72753 : dest_num = dest_num.
Proof. exact (eq_refl dest_num). Qed.
Lemma lem72754 (n : nat) : term6 n.
Proof. exact (@lem71593 n). Qed.
Lemma lem72755 (n : nat) : (term6 n) = ((S n) = (term7 n)).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem72762 (n : nat) : (S n) = (term7 n).
Proof. exact (EQ_MP (@lem72755 n) (@lem72754 n)). Qed.
Lemma lem72763 (m : nat) : (S m) = (term7 m).
Proof. exact (@lem72762 m). Qed.
Lemma lem72764 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem72765 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem72764) (@lem72763 m)). Qed.
Lemma lem72767 (n : nat) : (S n) = (term7 n).
Proof. exact (EQ_MP (@lem72755 n) (@lem72754 n)). Qed.
Lemma lem72768 (m : nat) (n : nat) : ((S m) = (S n)) = ((term7 m) = (term7 n)).
Proof. exact (MK_COMB (@lem72765 m) (@lem72767 n)). Qed.
Lemma lem72771 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem72772 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem72771) (@lem72768 m n)). Qed.
Lemma lem72775 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem72776 (m : nat) (n : nat) : (((S m) = (S n)) = (m = n)) = (((term7 m) = (term7 n)) = (m = n)).
Proof. exact (MK_COMB (@lem72772 m n) (@lem72775 m n)). Qed.
Lemma lem72779 (m : nat) (n : nat) : (((term7 m) = (term7 n)) = (m = n)) = (((S m) = (S n)) = (m = n)).
Proof. exact (SYM (@lem72776 m n)). Qed.
Lemma lem72780 (m : nat) (n : nat) (h1 : (term7 m) = (term7 n)) : (term7 m) = (term7 n).
Proof. exact (h1). Qed.
Lemma lem72789 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem72790 : dest_num = dest_num.
Proof. exact (eq_refl dest_num). Qed.
Lemma lem72791 (m : nat) (n : nat) (h1 : m = n) : (dest_num m) = (dest_num n).
Proof. exact (MK_COMB (@lem72790) (@lem72789 m n h1)). Qed.
Lemma lem72792 : IND_SUC = IND_SUC.
Proof. exact (eq_refl IND_SUC). Qed.
Lemma lem72793 (m : nat) (n : nat) (h1 : m = n) : (term12 m) = (term12 n).
Proof. exact (MK_COMB (@lem72792) (@lem72791 m n h1)). Qed.
Lemma lem72794 : mk_num = mk_num.
Proof. exact (eq_refl mk_num). Qed.
Lemma lem72795 (m : nat) (n : nat) (h1 : m = n) : (term7 m) = (term7 n).
Proof. exact (MK_COMB (@lem72794) (@lem72793 m n h1)). Qed.
Lemma lem72796 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem72797 (m : nat) (n : nat) (h1 : m = n) : (term9 m) = (term9 n).
Proof. exact (MK_COMB (@lem72796) (@lem72795 m n h1)). Qed.
Lemma lem72798 (n : nat) : (term7 n) = (term7 n).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem72799 (m : nat) (n : nat) (h1 : m = n) : ((term7 m) = (term7 n)) = ((term7 n) = (term7 n)).
Proof. exact (MK_COMB (@lem72797 m n h1) (@lem72798 n)). Qed.
Lemma lem72801 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem72802 (x : nat) : (x = x) = True.
Proof. exact (@lem72801 nat x). Qed.
Lemma lem72803 (n : nat) : ((term7 n) = (term7 n)) = True.
Proof. exact (@lem72802 (term7 n)). Qed.
Lemma lem72804 (m : nat) (n : nat) (h1 : m = n) : ((term7 m) = (term7 n)) = True.
Proof. exact (TRANS (@lem72799 m n h1) (@lem72803 n)). Qed.
Lemma lem72805 (m : nat) (n : nat) (h1 : m = n) : True = ((term7 m) = (term7 n)).
Proof. exact (SYM (@lem72804 m n h1)). Qed.
Lemma lem72806 (m : nat) (n : nat) (h1 : m = n) : (term7 m) = (term7 n).
Proof. exact (EQ_MP (@lem72805 m n h1) (@lem0)). Qed.
Lemma lem72807 (m : nat) (n : nat) (h1 : (term7 m) = (term7 n)) : (term13 m) = (term13 n).
Proof. exact (MK_COMB (@lem72753) (@lem72780 m n h1)). Qed.
Lemma lem72808 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem72810 (i : ind) : term2 i.
Proof. exact (EQ_MP (@lem72751 i) (@lem72750 i)). Qed.
Lemma lem72811 (p : nat) : term15 p.
Proof. exact (@lem72810 (dest_num p)). Qed.
Lemma lem72813 (r : ind) : (NUM_REP r) = ((term16 r) = r).
Proof. exact (@axiom_8 r). Qed.
Lemma lem72814 (p : nat) : (term17 p) = ((term18 p) = (dest_num p)).
Proof. exact (@lem72813 (dest_num p)). Qed.
Lemma lem72818 (a : nat) : (term19 a) = a.
Proof. exact (@axiom_7 a). Qed.
Lemma lem72819 (p : nat) : (term19 p) = p.
Proof. exact (@lem72818 p). Qed.
Lemma lem72820 : dest_num = dest_num.
Proof. exact (eq_refl dest_num). Qed.
Lemma lem72821 (p : nat) : (term18 p) = (dest_num p).
Proof. exact (MK_COMB (@lem72820) (@lem72819 p)). Qed.
Lemma lem72822 : (@eq ind) = (@eq ind).
Proof. exact (eq_refl (@eq ind)). Qed.
Lemma lem72823 (p : nat) : (term20 p) = (term21 p).
Proof. exact (MK_COMB (@lem72822) (@lem72821 p)). Qed.
Lemma lem72824 (p : nat) : (dest_num p) = (dest_num p).
Proof. exact (eq_refl (dest_num p)). Qed.
Lemma lem72825 (p : nat) : ((term18 p) = (dest_num p)) = ((dest_num p) = (dest_num p)).
Proof. exact (MK_COMB (@lem72823 p) (@lem72824 p)). Qed.
Lemma lem72827 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem72828 (x : ind) : (x = x) = True.
Proof. exact (@lem72827 ind x). Qed.
Lemma lem72829 (p : nat) : ((dest_num p) = (dest_num p)) = True.
Proof. exact (@lem72828 (dest_num p)). Qed.
Lemma lem72830 (p : nat) : ((term18 p) = (dest_num p)) = True.
Proof. exact (TRANS (@lem72825 p) (@lem72829 p)). Qed.
Lemma lem72831 (p : nat) : (term17 p) = True.
Proof. exact (TRANS (@lem72814 p) (@lem72830 p)). Qed.
Lemma lem72832 (p : nat) : True = (term17 p).
Proof. exact (SYM (@lem72831 p)). Qed.
Lemma lem72833 (p : nat) : term17 p.
Proof. exact (EQ_MP (@lem72832 p) (@lem0)). Qed.
Lemma lem72841 (r : ind) : (NUM_REP r) = ((term16 r) = r).
Proof. exact (@axiom_8 r). Qed.
Lemma lem72842 (p : nat) : (term22 p) = ((term13 p) = (term12 p)).
Proof. exact (@lem72841 (term12 p)). Qed.
Lemma lem72845 : term23 = term24.
Proof. exact (fun_ext (fun p : nat => @lem72842 p)). Qed.
Lemma lem72846 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem72847 : term14 = term25.
Proof. exact (MK_COMB (@lem72846) (@lem72845)). Qed.
Lemma lem72852 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem72853 : term26 = term27.
Proof. exact (MK_COMB (@lem72852) (@lem72847)). Qed.
Lemma lem72862 (m : nat) (n : nat) : (term28 m n) = (term28 m n).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem72863 (m : nat) (n : nat) : (term29 m n) = (term30 m n).
Proof. exact (MK_COMB (@lem72853) (@lem72862 m n)). Qed.
Lemma lem72866 (m : nat) (n : nat) : (term30 m n) = (term29 m n).
Proof. exact (SYM (@lem72863 m n)). Qed.
Lemma lem72867 (h1 : term25) : term25.
Proof. exact (h1). Qed.
Lemma lem72868 (x1 : ind) : term31 x1.
Proof. exact (@lem70828 x1). Qed.
Lemma lem72869 (x1 : ind) : (term31 x1) = (term32 x1).
Proof. exact (eq_refl (term31 x1)). Qed.
Lemma lem72870 (x1 : ind) : term32 x1.
Proof. exact (EQ_MP (@lem72869 x1) (@lem72868 x1)). Qed.
Lemma lem72871 (x1 : ind) (x2 : ind) : term33 x1 x2.
Proof. exact (@lem72870 x1 x2). Qed.
Lemma lem72872 (x1 : ind) (x2 : ind) : (term33 x1 x2) = (((IND_SUC x1) = (IND_SUC x2)) = (x1 = x2)).
Proof. exact (eq_refl (term33 x1 x2)). Qed.
Lemma lem72874 (p : nat) (h1 : term25) : term34 p.
Proof. exact (@lem72867 h1 p). Qed.
Lemma lem72875 (p : nat) : (term34 p) = ((term13 p) = (term12 p)).
Proof. exact (eq_refl (term34 p)). Qed.
Lemma lem72884 (p : nat) (h1 : term25) : (term13 p) = (term12 p).
Proof. exact (EQ_MP (@lem72875 p) (@lem72874 p h1)). Qed.
Lemma lem72885 (m : nat) (h1 : term25) : (term13 m) = (term12 m).
Proof. exact (@lem72884 m h1). Qed.
Lemma lem72886 : (@eq ind) = (@eq ind).
Proof. exact (eq_refl (@eq ind)). Qed.
Lemma lem72887 (m : nat) (h1 : term25) : (term35 m) = (term36 m).
Proof. exact (MK_COMB (@lem72886) (@lem72885 m h1)). Qed.
Lemma lem72889 (p : nat) (h1 : term25) : (term13 p) = (term12 p).
Proof. exact (EQ_MP (@lem72875 p) (@lem72874 p h1)). Qed.
Lemma lem72890 (n : nat) (h1 : term25) : (term13 n) = (term12 n).
Proof. exact (@lem72889 n h1). Qed.
Lemma lem72891 (m : nat) (n : nat) (h1 : term25) : ((term13 m) = (term13 n)) = ((term12 m) = (term12 n)).
Proof. exact (MK_COMB (@lem72887 m h1) (@lem72890 n h1)). Qed.
Lemma lem72893 (x1 : ind) (x2 : ind) : ((IND_SUC x1) = (IND_SUC x2)) = (x1 = x2).
Proof. exact (EQ_MP (@lem72872 x1 x2) (@lem72871 x1 x2)). Qed.
Lemma lem72894 (m : nat) (n : nat) : ((term12 m) = (term12 n)) = ((dest_num m) = (dest_num n)).
Proof. exact (@lem72893 (dest_num m) (dest_num n)). Qed.
Lemma lem72897 (m : nat) (n : nat) (h1 : term25) : ((term13 m) = (term13 n)) = ((dest_num m) = (dest_num n)).
Proof. exact (TRANS (@lem72891 m n h1) (@lem72894 m n)). Qed.
Lemma lem72898 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem72899 (m : nat) (n : nat) (h1 : term25) : (term37 m n) = (term38 m n).
Proof. exact (MK_COMB (@lem72898) (@lem72897 m n h1)). Qed.
Lemma lem72902 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem72903 (m : nat) (n : nat) (h1 : term25) : (term28 m n) = (term39 m n).
Proof. exact (MK_COMB (@lem72899 m n h1) (@lem72902 m n)). Qed.
Lemma lem72908 (m : nat) (n : nat) (h1 : term25) : (term39 m n) = (term28 m n).
Proof. exact (SYM (@lem72903 m n h1)). Qed.
Lemma lem72909 (m : nat) (n : nat) (h1 : (dest_num m) = (dest_num n)) : (dest_num m) = (dest_num n).
Proof. exact (h1). Qed.
Lemma lem72910 (m : nat) (n : nat) (h1 : (dest_num m) = (dest_num n)) : (term19 m) = (term19 n).
Proof. exact (MK_COMB (@lem72735) (@lem72909 m n h1)). Qed.
Lemma lem72918 (a : nat) : (term19 a) = a.
Proof. exact (@axiom_7 a). Qed.
Lemma lem72919 (m : nat) : (term19 m) = m.
Proof. exact (@lem72918 m). Qed.
Lemma lem72920 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem72921 (m : nat) : (term40 m) = (@eq nat m).
Proof. exact (MK_COMB (@lem72920) (@lem72919 m)). Qed.
Lemma lem72923 (a : nat) : (term19 a) = a.
Proof. exact (@axiom_7 a). Qed.
Lemma lem72924 (n : nat) : (term19 n) = n.
Proof. exact (@lem72923 n). Qed.
Lemma lem72925 (m : nat) (n : nat) : ((term19 m) = (term19 n)) = (m = n).
Proof. exact (MK_COMB (@lem72921 m) (@lem72924 n)). Qed.
Lemma lem72928 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem72929 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (MK_COMB (@lem72928) (@lem72925 m n)). Qed.
Lemma lem72932 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem72933 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (MK_COMB (@lem72929 m n) (@lem72932 m n)). Qed.
Lemma lem72937 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem72938 (m : nat) (n : nat) : (term44 m n) = True.
Proof. exact (@lem72937 (m = n)). Qed.
Lemma lem72939 (m : nat) (n : nat) : (term43 m n) = True.
Proof. exact (TRANS (@lem72933 m n) (@lem72938 m n)). Qed.
Lemma lem72940 (m : nat) (n : nat) : True = (term43 m n).
Proof. exact (SYM (@lem72939 m n)). Qed.
Lemma lem72941 (m : nat) (n : nat) : term43 m n.
Proof. exact (EQ_MP (@lem72940 m n) (@lem0)). Qed.
Lemma lem72942 (m : nat) (n : nat) (h1 : (dest_num m) = (dest_num n)) : m = n.
Proof. exact (@lem72941 m n (@lem72910 m n h1)). Qed.
Lemma lem72943 (m : nat) (n : nat) : term39 m n.
Proof. exact (fun h0 : (dest_num m) = (dest_num n) => @lem72942 m n h0). Qed.
Lemma lem72944 (m : nat) (n : nat) (h1 : term25) : term28 m n.
Proof. exact (EQ_MP (@lem72908 m n h1) (@lem72943 m n)). Qed.
Lemma lem72945 (m : nat) (n : nat) : term30 m n.
Proof. exact (fun h0 : term25 => @lem72944 m n h0). Qed.
Lemma lem72946 (m : nat) (n : nat) : term29 m n.
Proof. exact (EQ_MP (@lem72866 m n) (@lem72945 m n)). Qed.
Lemma lem72947 (p : nat) : term22 p.
Proof. exact (@lem72811 p (@lem72833 p)). Qed.
Lemma lem72952 : term14.
Proof. exact (fun p : nat => @lem72947 p). Qed.
Lemma lem72953 (m : nat) (n : nat) (h1 : term14) : term28 m n.
Proof. exact (@lem72946 m n (@lem72808 h1)). Qed.
Lemma lem72954 (m : nat) (n : nat) : term14 = (term28 m n).
Proof. exact (prop_ext (fun h1 : term14 => @lem72953 m n h1) (fun h1 : term28 m n => @lem72952)). Qed.
Lemma lem72955 (m : nat) (n : nat) : term28 m n.
Proof. exact (EQ_MP (@lem72954 m n) (@lem72952)). Qed.
Lemma lem72957 (m : nat) (n : nat) (h1 : (term7 m) = (term7 n)) : m = n.
Proof. exact (@lem72955 m n (@lem72807 m n h1)). Qed.
Lemma lem72958 (m : nat) (n : nat) : term45 m n.
Proof. exact (fun h0 : m = n => @lem72806 m n h0). Qed.
Lemma lem72959 (m : nat) (n : nat) : term46 m n.
Proof. exact (fun h0 : (term7 m) = (term7 n) => @lem72957 m n h0). Qed.
Lemma lem72960 (m : nat) (n : nat) : term47 m n.
Proof. exact (conj (@lem72959 m n) (@lem72958 m n)). Qed.
Lemma lem72961 (m : nat) (n : nat) : (term47 m n) = (((term7 m) = (term7 n)) = (m = n)).
Proof. exact (@lem32 ((term7 m) = (term7 n)) (m = n)). Qed.
Lemma lem72962 (m : nat) (n : nat) : ((term7 m) = (term7 n)) = (m = n).
Proof. exact (EQ_MP (@lem72961 m n) (@lem72960 m n)). Qed.
Lemma lem72963 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem72779 m n) (@lem72962 m n)). Qed.
Lemma lem72968 (m : nat) : term48 m.
Proof. exact (fun n : nat => @lem72963 m n). Qed.
Lemma lem72973 : term49.
Proof. exact (fun m : nat => @lem72968 m). Qed.
