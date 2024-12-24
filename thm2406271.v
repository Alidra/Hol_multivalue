Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2406271_term_abbrevs.
Require Import INT_ADD_ASSOC_spec.
Require Import INT_ADD_LID_spec.
Require Import INT_ADD_LINV_spec.
Require Import INT_ADD_RINV_spec.
Require Import INT_ADD_SYM_spec.
Require Import INT_NEG_ADD_spec.
Require Import INT_OF_NUM_ADD_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2405814 (x : int) : term0 x.
Proof. exact (@lem2301132 x). Qed.
Lemma lem2405815 (x : int) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2405817 (x : int) : term2 x.
Proof. exact (@lem2301245 x). Qed.
Lemma lem2405818 (x : int) : (term2 x) = ((term3 x) = term4).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem2405820 (x : int) : term0 x.
Proof. exact (@lem2301132 x). Qed.
Lemma lem2405821 (x : int) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2405823 (x : int) : term5 x.
Proof. exact (@lem2301157 x). Qed.
Lemma lem2405824 (x : int) : (term5 x) = ((term6 x) = term4).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem2405826 (x : int) : term7 x.
Proof. exact (@lem2301067 x). Qed.
Lemma lem2405827 (x : int) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2405828 (x : int) : term8 x.
Proof. exact (EQ_MP (@lem2405827 x) (@lem2405826 x)). Qed.
Lemma lem2405829 (x : int) (y : int) : term9 x y.
Proof. exact (@lem2405828 x y). Qed.
Lemma lem2405830 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem2405831 (x : int) (y : int) : term10 x y.
Proof. exact (EQ_MP (@lem2405830 x y) (@lem2405829 x y)). Qed.
Lemma lem2405832 (x : int) (y : int) (z : int) : term11 x y z.
Proof. exact (@lem2405831 x y z). Qed.
Lemma lem2405833 (x : int) (y : int) (z : int) : (term11 x y z) = ((term12 x y z) = (term13 x y z)).
Proof. exact (eq_refl (term11 x y z)). Qed.
Lemma lem2405835 (x : int) : term14 x.
Proof. exact (@lem2301320 x). Qed.
Lemma lem2405836 (x : int) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem2405837 (x : int) : term15 x.
Proof. exact (EQ_MP (@lem2405836 x) (@lem2405835 x)). Qed.
Lemma lem2405838 (x : int) (y : int) : term16 x y.
Proof. exact (@lem2405837 x y). Qed.
Lemma lem2405839 (y : int) (x : int) : (term16 x y) = ((int_add x y) = (int_add y x)).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem2405841 (x : int) : term0 x.
Proof. exact (@lem2301132 x). Qed.
Lemma lem2405842 (x : int) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2405844 (x : int) : term2 x.
Proof. exact (@lem2301245 x). Qed.
Lemma lem2405845 (x : int) : (term2 x) = ((term3 x) = term4).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem2405847 (x : int) : term0 x.
Proof. exact (@lem2301132 x). Qed.
Lemma lem2405848 (x : int) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2405850 (x : int) : term5 x.
Proof. exact (@lem2301157 x). Qed.
Lemma lem2405851 (x : int) : (term5 x) = ((term6 x) = term4).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem2405853 (x : int) : term7 x.
Proof. exact (@lem2301067 x). Qed.
Lemma lem2405854 (x : int) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2405855 (x : int) : term8 x.
Proof. exact (EQ_MP (@lem2405854 x) (@lem2405853 x)). Qed.
Lemma lem2405856 (x : int) (y : int) : term9 x y.
Proof. exact (@lem2405855 x y). Qed.
Lemma lem2405857 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem2405858 (x : int) (y : int) : term10 x y.
Proof. exact (EQ_MP (@lem2405857 x y) (@lem2405856 x y)). Qed.
Lemma lem2405859 (x : int) (y : int) (z : int) : term11 x y z.
Proof. exact (@lem2405858 x y z). Qed.
Lemma lem2405860 (x : int) (y : int) (z : int) : (term11 x y z) = ((term12 x y z) = (term13 x y z)).
Proof. exact (eq_refl (term11 x y z)). Qed.
Lemma lem2405864 (m : nat) (n : nat) (h1 : (term17 m n) = (term18 m n)) : (term17 m n) = (term18 m n).
Proof. exact (h1). Qed.
Lemma lem2405865 (m : nat) (n : nat) (h1 : (term17 m n) = (term18 m n)) : (term18 m n) = (term17 m n).
Proof. exact (SYM (@lem2405864 m n h1)). Qed.
Lemma lem2405866 (m : nat) (n : nat) (h1 : (term18 m n) = (term17 m n)) : (term18 m n) = (term17 m n).
Proof. exact (h1). Qed.
Lemma lem2405867 (m : nat) (n : nat) (h1 : (term18 m n) = (term17 m n)) : (term17 m n) = (term18 m n).
Proof. exact (SYM (@lem2405866 m n h1)). Qed.
Lemma lem2405868 (m : nat) (n : nat) : ((term17 m n) = (term18 m n)) = ((term18 m n) = (term17 m n)).
Proof. exact (prop_ext (fun h1 : (term17 m n) = (term18 m n) => @lem2405865 m n h1) (fun h1 : (term18 m n) = (term17 m n) => @lem2405867 m n h1)). Qed.
Lemma lem2405869 (m : nat) : (term19 m) = (term20 m).
Proof. exact (fun_ext (fun n : nat => @lem2405868 m n)). Qed.
Lemma lem2405870 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2405871 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem2405870) (@lem2405869 m)). Qed.
Lemma lem2405872 : term23 = term24.
Proof. exact (fun_ext (fun m : nat => @lem2405871 m)). Qed.
Lemma lem2405873 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2405874 : term25 = term26.
Proof. exact (MK_COMB (@lem2405873) (@lem2405872)). Qed.
Lemma lem2405875 : term26.
Proof. exact (EQ_MP (@lem2405874) (@lem2306816)). Qed.
Lemma lem2405876 (x : int) : term27 x.
Proof. exact (@lem2306367 x). Qed.
Lemma lem2405877 (x : int) : (term27 x) = (term28 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem2405878 (x : int) : term28 x.
Proof. exact (EQ_MP (@lem2405877 x) (@lem2405876 x)). Qed.
Lemma lem2405879 (x : int) (y : int) : term29 x y.
Proof. exact (@lem2405878 x y). Qed.
Lemma lem2405880 (x : int) (y : int) : (term29 x y) = ((term30 x y) = (term31 x y)).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem2405882 (m : nat) : term32 m.
Proof. exact (@lem2405875 m). Qed.
Lemma lem2405883 (m : nat) : (term32 m) = (term22 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem2405884 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem2405883 m) (@lem2405882 m)). Qed.
Lemma lem2405885 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem2405884 m n). Qed.
Lemma lem2405886 (m : nat) (n : nat) : (term33 m n) = ((term18 m n) = (term17 m n)).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem2405893 (m : nat) (n : nat) : (term18 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem2405886 m n) (@lem2405885 m n)). Qed.
Lemma lem2405894 : int_neg = int_neg.
Proof. exact (eq_refl int_neg). Qed.
Lemma lem2405895 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem2405894) (@lem2405893 m n)). Qed.
Lemma lem2405897 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem2405880 x y) (@lem2405879 x y)). Qed.
Lemma lem2405898 (m : nat) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (@lem2405897 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2405899 (m : nat) (n : nat) : (term34 m n) = (term36 m n).
Proof. exact (TRANS (@lem2405895 m n) (@lem2405898 m n)). Qed.
Lemma lem2405900 (m : nat) (n : nat) : (term37 m n) = (term37 m n).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem2405901 (m : nat) (n : nat) : ((term36 m n) = (term34 m n)) = ((term36 m n) = (term36 m n)).
Proof. exact (MK_COMB (@lem2405900 m n) (@lem2405899 m n)). Qed.
Lemma lem2405903 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2405904 (x : int) : (x = x) = True.
Proof. exact (@lem2405903 int x). Qed.
Lemma lem2405905 (m : nat) (n : nat) : ((term36 m n) = (term36 m n)) = True.
Proof. exact (@lem2405904 (term36 m n)). Qed.
Lemma lem2405906 (m : nat) (n : nat) : ((term36 m n) = (term34 m n)) = True.
Proof. exact (TRANS (@lem2405901 m n) (@lem2405905 m n)). Qed.
Lemma lem2405907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405908 (m : nat) (n : nat) : (term38 m n) = (and True).
Proof. exact (MK_COMB (@lem2405907) (@lem2405906 m n)). Qed.
Lemma lem2405914 (m : nat) (n : nat) : (term18 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem2405886 m n) (@lem2405885 m n)). Qed.
Lemma lem2405915 (m : nat) : (term39 m) = (term39 m).
Proof. exact (eq_refl (term39 m)). Qed.
Lemma lem2405916 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (MK_COMB (@lem2405915 m) (@lem2405914 m n)). Qed.
Lemma lem2405917 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405918 (m : nat) (n : nat) : (term42 m n) = (term43 m n).
Proof. exact (MK_COMB (@lem2405917) (@lem2405916 m n)). Qed.
Lemma lem2405919 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (eq_refl (int_of_num n)). Qed.
Lemma lem2405920 (m : nat) (n : nat) : ((term40 m n) = (int_of_num n)) = ((term41 m n) = (int_of_num n)).
Proof. exact (MK_COMB (@lem2405918 m n) (@lem2405919 n)). Qed.
Lemma lem2405923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405924 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem2405923) (@lem2405920 m n)). Qed.
Lemma lem2405930 (m : nat) (n : nat) : (term18 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem2405886 m n) (@lem2405885 m n)). Qed.
Lemma lem2405931 : int_neg = int_neg.
Proof. exact (eq_refl int_neg). Qed.
Lemma lem2405932 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem2405931) (@lem2405930 m n)). Qed.
Lemma lem2405934 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem2405880 x y) (@lem2405879 x y)). Qed.
Lemma lem2405935 (m : nat) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (@lem2405934 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2405936 (m : nat) (n : nat) : (term34 m n) = (term36 m n).
Proof. exact (TRANS (@lem2405932 m n) (@lem2405935 m n)). Qed.
Lemma lem2405937 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2405938 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (MK_COMB (@lem2405937) (@lem2405936 m n)). Qed.
Lemma lem2405939 (m : nat) : (int_of_num m) = (int_of_num m).
Proof. exact (eq_refl (int_of_num m)). Qed.
Lemma lem2405940 (n : nat) (m : nat) : (term48 n m) = (term49 n m).
Proof. exact (MK_COMB (@lem2405938 m n) (@lem2405939 m)). Qed.
Lemma lem2405941 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405942 (n : nat) (m : nat) : (term50 n m) = (term51 n m).
Proof. exact (MK_COMB (@lem2405941) (@lem2405940 n m)). Qed.
Lemma lem2405943 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem2405944 (m : nat) (n : nat) : ((term48 n m) = (term52 n)) = ((term49 n m) = (term52 n)).
Proof. exact (MK_COMB (@lem2405942 n m) (@lem2405943 n)). Qed.
Lemma lem2405947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405948 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (MK_COMB (@lem2405947) (@lem2405944 m n)). Qed.
Lemma lem2405954 (m : nat) (n : nat) : (term18 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem2405886 m n) (@lem2405885 m n)). Qed.
Lemma lem2405955 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2405956 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem2405955) (@lem2405954 m n)). Qed.
Lemma lem2405957 (m : nat) : (term52 m) = (term52 m).
Proof. exact (eq_refl (term52 m)). Qed.
Lemma lem2405958 (n : nat) (m : nat) : (term57 n m) = (term58 n m).
Proof. exact (MK_COMB (@lem2405956 m n) (@lem2405957 m)). Qed.
Lemma lem2405959 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405960 (n : nat) (m : nat) : (term59 n m) = (term60 n m).
Proof. exact (MK_COMB (@lem2405959) (@lem2405958 n m)). Qed.
Lemma lem2405961 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (eq_refl (int_of_num n)). Qed.
Lemma lem2405962 (m : nat) (n : nat) : ((term57 n m) = (int_of_num n)) = ((term58 n m) = (int_of_num n)).
Proof. exact (MK_COMB (@lem2405960 n m) (@lem2405961 n)). Qed.
Lemma lem2405965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405966 (m : nat) (n : nat) : (term61 m n) = (term62 m n).
Proof. exact (MK_COMB (@lem2405965) (@lem2405962 m n)). Qed.
Lemma lem2405972 (m : nat) (n : nat) : (term18 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem2405886 m n) (@lem2405885 m n)). Qed.
Lemma lem2405973 : int_neg = int_neg.
Proof. exact (eq_refl int_neg). Qed.
Lemma lem2405974 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem2405973) (@lem2405972 m n)). Qed.
Lemma lem2405976 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem2405880 x y) (@lem2405879 x y)). Qed.
Lemma lem2405977 (m : nat) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (@lem2405976 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2405978 (m : nat) (n : nat) : (term34 m n) = (term36 m n).
Proof. exact (TRANS (@lem2405974 m n) (@lem2405977 m n)). Qed.
Lemma lem2405979 (m : nat) : (term63 m) = (term63 m).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem2405980 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (MK_COMB (@lem2405979 m) (@lem2405978 m n)). Qed.
Lemma lem2405981 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2405982 (m : nat) (n : nat) : (term66 m n) = (term67 m n).
Proof. exact (MK_COMB (@lem2405981) (@lem2405980 m n)). Qed.
Lemma lem2405983 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem2405984 (m : nat) (n : nat) : ((term64 m n) = (term52 n)) = ((term65 m n) = (term52 n)).
Proof. exact (MK_COMB (@lem2405982 m n) (@lem2405983 n)). Qed.
Lemma lem2405987 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2405988 (m : nat) (n : nat) : (term68 m n) = (term69 m n).
Proof. exact (MK_COMB (@lem2405987) (@lem2405984 m n)). Qed.
Lemma lem2405992 (m : nat) (n : nat) : (term18 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem2405886 m n) (@lem2405885 m n)). Qed.
Lemma lem2405993 (m : nat) (n : nat) : (term70 m n) = (term70 m n).
Proof. exact (eq_refl (term70 m n)). Qed.
Lemma lem2405994 (m : nat) (n : nat) : ((term17 m n) = (term18 m n)) = ((term17 m n) = (term17 m n)).
Proof. exact (MK_COMB (@lem2405993 m n) (@lem2405992 m n)). Qed.
Lemma lem2405996 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2405997 (x : int) : (x = x) = True.
Proof. exact (@lem2405996 int x). Qed.
Lemma lem2405998 (m : nat) (n : nat) : ((term17 m n) = (term17 m n)) = True.
Proof. exact (@lem2405997 (term17 m n)). Qed.
Lemma lem2405999 (m : nat) (n : nat) : ((term17 m n) = (term18 m n)) = True.
Proof. exact (TRANS (@lem2405994 m n) (@lem2405998 m n)). Qed.
Lemma lem2406000 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (MK_COMB (@lem2405988 m n) (@lem2405999 m n)). Qed.
Lemma lem2406002 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem2406003 (m : nat) (n : nat) : (term72 m n) = ((term65 m n) = (term52 n)).
Proof. exact (@lem2406002 ((term65 m n) = (term52 n))). Qed.
Lemma lem2406006 (m : nat) (n : nat) : (term71 m n) = ((term65 m n) = (term52 n)).
Proof. exact (TRANS (@lem2406000 m n) (@lem2406003 m n)). Qed.
Lemma lem2406007 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (MK_COMB (@lem2405966 m n) (@lem2406006 m n)). Qed.
Lemma lem2406010 (m : nat) (n : nat) : (term75 m n) = (term76 m n).
Proof. exact (MK_COMB (@lem2405948 m n) (@lem2406007 m n)). Qed.
Lemma lem2406013 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem2405924 m n) (@lem2406010 m n)). Qed.
Lemma lem2406016 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (MK_COMB (@lem2405908 m n) (@lem2406013 m n)). Qed.
Lemma lem2406018 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2406019 (m : nat) (n : nat) : (term80 m n) = (term78 m n).
Proof. exact (@lem2406018 (term78 m n)). Qed.
Lemma lem2406034 (m : nat) (n : nat) : (term79 m n) = (term78 m n).
Proof. exact (TRANS (@lem2406016 m n) (@lem2406019 m n)). Qed.
Lemma lem2406035 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (SYM (@lem2406034 m n)). Qed.
Lemma lem2406043 (x : int) (y : int) (z : int) : (term12 x y z) = (term13 x y z).
Proof. exact (EQ_MP (@lem2405860 x y z) (@lem2405859 x y z)). Qed.
Lemma lem2406044 (m : nat) (n : nat) : (term41 m n) = (term81 m n).
Proof. exact (@lem2406043 (term52 m) (int_of_num m) (int_of_num n)). Qed.
Lemma lem2406046 (x : int) : (term6 x) = term4.
Proof. exact (EQ_MP (@lem2405851 x) (@lem2405850 x)). Qed.
Lemma lem2406047 (m : nat) : (term82 m) = term4.
Proof. exact (@lem2406046 (int_of_num m)). Qed.
Lemma lem2406048 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2406049 (m : nat) : (term83 m) = term84.
Proof. exact (MK_COMB (@lem2406048) (@lem2406047 m)). Qed.
Lemma lem2406050 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (eq_refl (int_of_num n)). Qed.
Lemma lem2406051 (m : nat) (n : nat) : (term81 m n) = (term85 n).
Proof. exact (MK_COMB (@lem2406049 m) (@lem2406050 n)). Qed.
Lemma lem2406053 (x : int) : (term1 x) = x.
Proof. exact (EQ_MP (@lem2405848 x) (@lem2405847 x)). Qed.
Lemma lem2406054 (n : nat) : (term85 n) = (int_of_num n).
Proof. exact (@lem2406053 (int_of_num n)). Qed.
Lemma lem2406055 (m : nat) (n : nat) : (term81 m n) = (int_of_num n).
Proof. exact (TRANS (@lem2406051 m n) (@lem2406054 n)). Qed.
Lemma lem2406056 (m : nat) (n : nat) : (term41 m n) = (int_of_num n).
Proof. exact (TRANS (@lem2406044 m n) (@lem2406055 m n)). Qed.
Lemma lem2406057 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2406058 (m : nat) (n : nat) : (term43 m n) = (term86 n).
Proof. exact (MK_COMB (@lem2406057) (@lem2406056 m n)). Qed.
Lemma lem2406059 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (eq_refl (int_of_num n)). Qed.
Lemma lem2406060 (m : nat) (n : nat) : ((term41 m n) = (int_of_num n)) = ((int_of_num n) = (int_of_num n)).
Proof. exact (MK_COMB (@lem2406058 m n) (@lem2406059 n)). Qed.
Lemma lem2406062 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2406063 (x : int) : (x = x) = True.
Proof. exact (@lem2406062 int x). Qed.
Lemma lem2406064 (n : nat) : ((int_of_num n) = (int_of_num n)) = True.
Proof. exact (@lem2406063 (int_of_num n)). Qed.
Lemma lem2406065 (m : nat) (n : nat) : ((term41 m n) = (int_of_num n)) = True.
Proof. exact (TRANS (@lem2406060 m n) (@lem2406064 n)). Qed.
Lemma lem2406066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2406067 (m : nat) (n : nat) : (term45 m n) = (and True).
Proof. exact (MK_COMB (@lem2406066) (@lem2406065 m n)). Qed.
Lemma lem2406081 (x : int) (y : int) (z : int) : (term12 x y z) = (term13 x y z).
Proof. exact (EQ_MP (@lem2405860 x y z) (@lem2405859 x y z)). Qed.
Lemma lem2406082 (m : nat) (n : nat) : (term65 m n) = (term87 m n).
Proof. exact (@lem2406081 (int_of_num m) (term52 m) (term52 n)). Qed.
Lemma lem2406083 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2406084 (m : nat) (n : nat) : (term67 m n) = (term88 m n).
Proof. exact (MK_COMB (@lem2406083) (@lem2406082 m n)). Qed.
Lemma lem2406085 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem2406086 (m : nat) (n : nat) : ((term65 m n) = (term52 n)) = ((term87 m n) = (term52 n)).
Proof. exact (MK_COMB (@lem2406084 m n) (@lem2406085 n)). Qed.
Lemma lem2406089 (m : nat) (n : nat) : (term62 m n) = (term62 m n).
Proof. exact (eq_refl (term62 m n)). Qed.
Lemma lem2406090 (m : nat) (n : nat) : (term74 m n) = (term89 m n).
Proof. exact (MK_COMB (@lem2406089 m n) (@lem2406086 m n)). Qed.
Lemma lem2406093 (m : nat) (n : nat) : (term54 m n) = (term54 m n).
Proof. exact (eq_refl (term54 m n)). Qed.
Lemma lem2406094 (m : nat) (n : nat) : (term76 m n) = (term90 m n).
Proof. exact (MK_COMB (@lem2406093 m n) (@lem2406090 m n)). Qed.
Lemma lem2406097 (m : nat) (n : nat) : (term78 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem2406067 m n) (@lem2406094 m n)). Qed.
Lemma lem2406099 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2406100 (m : nat) (n : nat) : (term91 m n) = (term90 m n).
Proof. exact (@lem2406099 (term90 m n)). Qed.
Lemma lem2406113 (m : nat) (n : nat) : (term78 m n) = (term90 m n).
Proof. exact (TRANS (@lem2406097 m n) (@lem2406100 m n)). Qed.
Lemma lem2406114 (m : nat) (n : nat) : (term90 m n) = (term78 m n).
Proof. exact (SYM (@lem2406113 m n)). Qed.
Lemma lem2406132 (x : int) : (term3 x) = term4.
Proof. exact (EQ_MP (@lem2405845 x) (@lem2405844 x)). Qed.
Lemma lem2406133 (m : nat) : (term92 m) = term4.
Proof. exact (@lem2406132 (int_of_num m)). Qed.
Lemma lem2406134 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2406135 (m : nat) : (term93 m) = term84.
Proof. exact (MK_COMB (@lem2406134) (@lem2406133 m)). Qed.
Lemma lem2406136 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem2406137 (m : nat) (n : nat) : (term87 m n) = (term94 n).
Proof. exact (MK_COMB (@lem2406135 m) (@lem2406136 n)). Qed.
Lemma lem2406139 (x : int) : (term1 x) = x.
Proof. exact (EQ_MP (@lem2405842 x) (@lem2405841 x)). Qed.
Lemma lem2406140 (n : nat) : (term94 n) = (term52 n).
Proof. exact (@lem2406139 (term52 n)). Qed.
Lemma lem2406141 (m : nat) (n : nat) : (term87 m n) = (term52 n).
Proof. exact (TRANS (@lem2406137 m n) (@lem2406140 n)). Qed.
Lemma lem2406142 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2406143 (m : nat) (n : nat) : (term88 m n) = (term95 n).
Proof. exact (MK_COMB (@lem2406142) (@lem2406141 m n)). Qed.
Lemma lem2406144 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem2406145 (m : nat) (n : nat) : ((term87 m n) = (term52 n)) = ((term52 n) = (term52 n)).
Proof. exact (MK_COMB (@lem2406143 m n) (@lem2406144 n)). Qed.
Lemma lem2406147 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2406148 (x : int) : (x = x) = True.
Proof. exact (@lem2406147 int x). Qed.
Lemma lem2406149 (n : nat) : ((term52 n) = (term52 n)) = True.
Proof. exact (@lem2406148 (term52 n)). Qed.
Lemma lem2406150 (m : nat) (n : nat) : ((term87 m n) = (term52 n)) = True.
Proof. exact (TRANS (@lem2406145 m n) (@lem2406149 n)). Qed.
Lemma lem2406151 (m : nat) (n : nat) : (term62 m n) = (term62 m n).
Proof. exact (eq_refl (term62 m n)). Qed.
Lemma lem2406152 (m : nat) (n : nat) : (term89 m n) = (term96 m n).
Proof. exact (MK_COMB (@lem2406151 m n) (@lem2406150 m n)). Qed.
Lemma lem2406154 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem2406155 (m : nat) (n : nat) : (term96 m n) = ((term58 n m) = (int_of_num n)).
Proof. exact (@lem2406154 ((term58 n m) = (int_of_num n))). Qed.
Lemma lem2406160 (m : nat) (n : nat) : (term89 m n) = ((term58 n m) = (int_of_num n)).
Proof. exact (TRANS (@lem2406152 m n) (@lem2406155 m n)). Qed.
Lemma lem2406161 (m : nat) (n : nat) : (term54 m n) = (term54 m n).
Proof. exact (eq_refl (term54 m n)). Qed.
Lemma lem2406162 (m : nat) (n : nat) : (term90 m n) = (term97 m n).
Proof. exact (MK_COMB (@lem2406161 m n) (@lem2406160 m n)). Qed.
Lemma lem2406165 (m : nat) (n : nat) : (term97 m n) = (term90 m n).
Proof. exact (SYM (@lem2406162 m n)). Qed.
Lemma lem2406171 (y : int) (x : int) : (int_add x y) = (int_add y x).
Proof. exact (EQ_MP (@lem2405839 y x) (@lem2405838 x y)). Qed.
Lemma lem2406172 (m : nat) (n : nat) : (term49 n m) = (term65 m n).
Proof. exact (@lem2406171 (int_of_num m) (term36 m n)). Qed.
Lemma lem2406173 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2406174 (m : nat) (n : nat) : (term51 n m) = (term67 m n).
Proof. exact (MK_COMB (@lem2406173) (@lem2406172 m n)). Qed.
Lemma lem2406175 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem2406176 (m : nat) (n : nat) : ((term49 n m) = (term52 n)) = ((term65 m n) = (term52 n)).
Proof. exact (MK_COMB (@lem2406174 m n) (@lem2406175 n)). Qed.
Lemma lem2406177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2406178 (m : nat) (n : nat) : (term54 m n) = (term69 m n).
Proof. exact (MK_COMB (@lem2406177) (@lem2406176 m n)). Qed.
Lemma lem2406182 (y : int) (x : int) : (int_add x y) = (int_add y x).
Proof. exact (EQ_MP (@lem2405839 y x) (@lem2405838 x y)). Qed.
Lemma lem2406183 (m : nat) (n : nat) : (term58 n m) = (term41 m n).
Proof. exact (@lem2406182 (term52 m) (term17 m n)). Qed.
Lemma lem2406184 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2406185 (m : nat) (n : nat) : (term60 n m) = (term43 m n).
Proof. exact (MK_COMB (@lem2406184) (@lem2406183 m n)). Qed.
Lemma lem2406186 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (eq_refl (int_of_num n)). Qed.
Lemma lem2406187 (m : nat) (n : nat) : ((term58 n m) = (int_of_num n)) = ((term41 m n) = (int_of_num n)).
Proof. exact (MK_COMB (@lem2406185 m n) (@lem2406186 n)). Qed.
Lemma lem2406188 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (MK_COMB (@lem2406178 m n) (@lem2406187 m n)). Qed.
Lemma lem2406189 (m : nat) (n : nat) : (term98 m n) = (term97 m n).
Proof. exact (SYM (@lem2406188 m n)). Qed.
Lemma lem2406195 (x : int) (y : int) (z : int) : (term12 x y z) = (term13 x y z).
Proof. exact (EQ_MP (@lem2405833 x y z) (@lem2405832 x y z)). Qed.
Lemma lem2406196 (m : nat) (n : nat) : (term65 m n) = (term87 m n).
Proof. exact (@lem2406195 (int_of_num m) (term52 m) (term52 n)). Qed.
Lemma lem2406197 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2406198 (m : nat) (n : nat) : (term67 m n) = (term88 m n).
Proof. exact (MK_COMB (@lem2406197) (@lem2406196 m n)). Qed.
Lemma lem2406199 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem2406200 (m : nat) (n : nat) : ((term65 m n) = (term52 n)) = ((term87 m n) = (term52 n)).
Proof. exact (MK_COMB (@lem2406198 m n) (@lem2406199 n)). Qed.
Lemma lem2406203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2406204 (m : nat) (n : nat) : (term69 m n) = (term99 m n).
Proof. exact (MK_COMB (@lem2406203) (@lem2406200 m n)). Qed.
Lemma lem2406210 (x : int) (y : int) (z : int) : (term12 x y z) = (term13 x y z).
Proof. exact (EQ_MP (@lem2405833 x y z) (@lem2405832 x y z)). Qed.
Lemma lem2406211 (m : nat) (n : nat) : (term41 m n) = (term81 m n).
Proof. exact (@lem2406210 (term52 m) (int_of_num m) (int_of_num n)). Qed.
Lemma lem2406213 (x : int) : (term6 x) = term4.
Proof. exact (EQ_MP (@lem2405824 x) (@lem2405823 x)). Qed.
Lemma lem2406214 (m : nat) : (term82 m) = term4.
Proof. exact (@lem2406213 (int_of_num m)). Qed.
Lemma lem2406215 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2406216 (m : nat) : (term83 m) = term84.
Proof. exact (MK_COMB (@lem2406215) (@lem2406214 m)). Qed.
Lemma lem2406217 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (eq_refl (int_of_num n)). Qed.
Lemma lem2406218 (m : nat) (n : nat) : (term81 m n) = (term85 n).
Proof. exact (MK_COMB (@lem2406216 m) (@lem2406217 n)). Qed.
Lemma lem2406220 (x : int) : (term1 x) = x.
Proof. exact (EQ_MP (@lem2405821 x) (@lem2405820 x)). Qed.
Lemma lem2406221 (n : nat) : (term85 n) = (int_of_num n).
Proof. exact (@lem2406220 (int_of_num n)). Qed.
Lemma lem2406222 (m : nat) (n : nat) : (term81 m n) = (int_of_num n).
Proof. exact (TRANS (@lem2406218 m n) (@lem2406221 n)). Qed.
Lemma lem2406223 (m : nat) (n : nat) : (term41 m n) = (int_of_num n).
Proof. exact (TRANS (@lem2406211 m n) (@lem2406222 m n)). Qed.
Lemma lem2406224 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2406225 (m : nat) (n : nat) : (term43 m n) = (term86 n).
Proof. exact (MK_COMB (@lem2406224) (@lem2406223 m n)). Qed.
Lemma lem2406226 (n : nat) : (int_of_num n) = (int_of_num n).
Proof. exact (eq_refl (int_of_num n)). Qed.
Lemma lem2406227 (m : nat) (n : nat) : ((term41 m n) = (int_of_num n)) = ((int_of_num n) = (int_of_num n)).
Proof. exact (MK_COMB (@lem2406225 m n) (@lem2406226 n)). Qed.
Lemma lem2406229 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2406230 (x : int) : (x = x) = True.
Proof. exact (@lem2406229 int x). Qed.
Lemma lem2406231 (n : nat) : ((int_of_num n) = (int_of_num n)) = True.
Proof. exact (@lem2406230 (int_of_num n)). Qed.
Lemma lem2406232 (m : nat) (n : nat) : ((term41 m n) = (int_of_num n)) = True.
Proof. exact (TRANS (@lem2406227 m n) (@lem2406231 n)). Qed.
Lemma lem2406233 (m : nat) (n : nat) : (term98 m n) = (term100 m n).
Proof. exact (MK_COMB (@lem2406204 m n) (@lem2406232 m n)). Qed.
Lemma lem2406235 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem2406236 (m : nat) (n : nat) : (term100 m n) = ((term87 m n) = (term52 n)).
Proof. exact (@lem2406235 ((term87 m n) = (term52 n))). Qed.
Lemma lem2406239 (m : nat) (n : nat) : (term98 m n) = ((term87 m n) = (term52 n)).
Proof. exact (TRANS (@lem2406233 m n) (@lem2406236 m n)). Qed.
Lemma lem2406240 (m : nat) (n : nat) : ((term87 m n) = (term52 n)) = (term98 m n).
Proof. exact (SYM (@lem2406239 m n)). Qed.
Lemma lem2406246 (x : int) : (term3 x) = term4.
Proof. exact (EQ_MP (@lem2405818 x) (@lem2405817 x)). Qed.
Lemma lem2406247 (m : nat) : (term92 m) = term4.
Proof. exact (@lem2406246 (int_of_num m)). Qed.
Lemma lem2406248 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2406249 (m : nat) : (term93 m) = term84.
Proof. exact (MK_COMB (@lem2406248) (@lem2406247 m)). Qed.
Lemma lem2406250 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem2406251 (m : nat) (n : nat) : (term87 m n) = (term94 n).
Proof. exact (MK_COMB (@lem2406249 m) (@lem2406250 n)). Qed.
Lemma lem2406253 (x : int) : (term1 x) = x.
Proof. exact (EQ_MP (@lem2405815 x) (@lem2405814 x)). Qed.
Lemma lem2406254 (n : nat) : (term94 n) = (term52 n).
Proof. exact (@lem2406253 (term52 n)). Qed.
Lemma lem2406255 (m : nat) (n : nat) : (term87 m n) = (term52 n).
Proof. exact (TRANS (@lem2406251 m n) (@lem2406254 n)). Qed.
Lemma lem2406256 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2406257 (m : nat) (n : nat) : (term88 m n) = (term95 n).
Proof. exact (MK_COMB (@lem2406256) (@lem2406255 m n)). Qed.
Lemma lem2406258 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem2406259 (m : nat) (n : nat) : ((term87 m n) = (term52 n)) = ((term52 n) = (term52 n)).
Proof. exact (MK_COMB (@lem2406257 m n) (@lem2406258 n)). Qed.
Lemma lem2406261 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2406262 (x : int) : (x = x) = True.
Proof. exact (@lem2406261 int x). Qed.
Lemma lem2406263 (n : nat) : ((term52 n) = (term52 n)) = True.
Proof. exact (@lem2406262 (term52 n)). Qed.
Lemma lem2406264 (m : nat) (n : nat) : ((term87 m n) = (term52 n)) = True.
Proof. exact (TRANS (@lem2406259 m n) (@lem2406263 n)). Qed.
Lemma lem2406265 (m : nat) (n : nat) : True = ((term87 m n) = (term52 n)).
Proof. exact (SYM (@lem2406264 m n)). Qed.
Lemma lem2406266 (m : nat) (n : nat) : (term87 m n) = (term52 n).
Proof. exact (EQ_MP (@lem2406265 m n) (@lem0)). Qed.
Lemma lem2406267 (m : nat) (n : nat) : term98 m n.
Proof. exact (EQ_MP (@lem2406240 m n) (@lem2406266 m n)). Qed.
Lemma lem2406268 (m : nat) (n : nat) : term97 m n.
Proof. exact (EQ_MP (@lem2406189 m n) (@lem2406267 m n)). Qed.
Lemma lem2406269 (m : nat) (n : nat) : term90 m n.
Proof. exact (EQ_MP (@lem2406165 m n) (@lem2406268 m n)). Qed.
Lemma lem2406270 (m : nat) (n : nat) : term78 m n.
Proof. exact (EQ_MP (@lem2406114 m n) (@lem2406269 m n)). Qed.
Lemma lem2406271 (m : nat) (n : nat) : term79 m n.
Proof. exact (EQ_MP (@lem2406035 m n) (@lem2406270 m n)). Qed.
