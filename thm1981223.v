Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1981223_term_abbrevs.
Require Import DECIMAL_spec.
Require Import REAL_INV_DIV_spec.
Require Import REAL_INV_INV_spec.
Require Import REAL_INV_MUL_spec.
Require Import REAL_INV_NEG_spec.
Require Import REAL_MUL_AC_spec.
Require Import REAL_MUL_LNEG_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1338986_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1980878 (x : real) : term0 x.
Proof. exact (@lem1587920 x). Qed.
Lemma lem1980879 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1980881 (x : real) : term2 x.
Proof. exact (@lem1595294 x). Qed.
Lemma lem1980882 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1980883 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1980882 x) (@lem1980881 x)). Qed.
Lemma lem1980884 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1980883 x y). Qed.
Lemma lem1980885 (x : real) (y : real) : (term4 x y) = ((term5 x y) = (term6 x y)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1980887 (x : real) : term7 x.
Proof. exact (@lem1360913 x). Qed.
Lemma lem1980888 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1980889 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem1980888 x) (@lem1980887 x)). Qed.
Lemma lem1980890 (x : real) (y : real) : term9 x y.
Proof. exact (@lem1980889 x y). Qed.
Lemma lem1980891 (x : real) (y : real) : (term9 x y) = ((term10 x y) = (term11 x y)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1980893 (x : real) : term12 x.
Proof. exact (@lem1338986 x). Qed.
Lemma lem1980894 (x : real) : (term12 x) = ((term13 x) = x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1980906 (x : real) : term14 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1980907 (x : real) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1980908 (x : real) : term15 x.
Proof. exact (EQ_MP (@lem1980907 x) (@lem1980906 x)). Qed.
Lemma lem1980909 (x : real) (y : real) : term16 x y.
Proof. exact (@lem1980908 x y). Qed.
Lemma lem1980910 (x : real) (y : real) : (term16 x y) = ((real_div x y) = (term17 x y)).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1980912 (x : real) : term18 x.
Proof. exact (@lem1590208 x). Qed.
Lemma lem1980913 (x : real) : (term18 x) = ((term19 x) = (term20 x)).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1980915 (x : real) : term21 x.
Proof. exact (@lem1595376 x). Qed.
Lemma lem1980916 (x : real) : (term21 x) = (term22 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1980917 (x : real) : term22 x.
Proof. exact (EQ_MP (@lem1980916 x) (@lem1980915 x)). Qed.
Lemma lem1980918 (x : real) (y : real) : term23 x y.
Proof. exact (@lem1980917 x y). Qed.
Lemma lem1980919 (y : real) (x : real) : (term23 x y) = ((term24 x y) = (real_div y x)).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1980921 (x : nat) : term25 x.
Proof. exact (@lem1977711 x). Qed.
Lemma lem1980922 (x : nat) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1980923 (x : nat) : term26 x.
Proof. exact (EQ_MP (@lem1980922 x) (@lem1980921 x)). Qed.
Lemma lem1980924 (x : nat) (y : nat) : term27 x y.
Proof. exact (@lem1980923 x y). Qed.
Lemma lem1980925 (x : nat) (y : nat) : (term27 x y) = ((DECIMAL x y) = (term28 x y)).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1980940 (y : real) (x : real) : (term24 x y) = (real_div y x).
Proof. exact (EQ_MP (@lem1980919 y x) (@lem1980918 x y)). Qed.
Lemma lem1980941 (n : nat) (m : nat) : (term29 m n) = (term28 n m).
Proof. exact (@lem1980940 (real_of_num n) (real_of_num m)). Qed.
Lemma lem1980942 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1980943 (n : nat) (m : nat) : (term30 m n) = (term31 n m).
Proof. exact (MK_COMB (@lem1980942) (@lem1980941 n m)). Qed.
Lemma lem1980944 (n : nat) (m : nat) : (term28 n m) = (term28 n m).
Proof. exact (eq_refl (term28 n m)). Qed.
Lemma lem1980945 (n : nat) (m : nat) : ((term29 m n) = (term28 n m)) = ((term28 n m) = (term28 n m)).
Proof. exact (MK_COMB (@lem1980943 n m) (@lem1980944 n m)). Qed.
Lemma lem1980947 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1980948 (x : real) : (x = x) = True.
Proof. exact (@lem1980947 real x). Qed.
Lemma lem1980949 (n : nat) (m : nat) : ((term28 n m) = (term28 n m)) = True.
Proof. exact (@lem1980948 (term28 n m)). Qed.
Lemma lem1980950 (n : nat) (m : nat) : ((term29 m n) = (term28 n m)) = True.
Proof. exact (TRANS (@lem1980945 n m) (@lem1980949 n m)). Qed.
Lemma lem1980951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1980952 (n : nat) (m : nat) : (term32 n m) = (and True).
Proof. exact (MK_COMB (@lem1980951) (@lem1980950 n m)). Qed.
Lemma lem1980958 (y : real) (x : real) : (term24 x y) = (real_div y x).
Proof. exact (EQ_MP (@lem1980919 y x) (@lem1980918 x y)). Qed.
Lemma lem1980959 (n : nat) (m : nat) : (term33 m n) = (term34 n m).
Proof. exact (@lem1980958 (real_of_num n) (term35 m)). Qed.
Lemma lem1980960 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1980961 (n : nat) (m : nat) : (term36 m n) = (term37 n m).
Proof. exact (MK_COMB (@lem1980960) (@lem1980959 n m)). Qed.
Lemma lem1980962 (n : nat) (m : nat) : (term38 n m) = (term38 n m).
Proof. exact (eq_refl (term38 n m)). Qed.
Lemma lem1980963 (n : nat) (m : nat) : ((term33 m n) = (term38 n m)) = ((term34 n m) = (term38 n m)).
Proof. exact (MK_COMB (@lem1980961 n m) (@lem1980962 n m)). Qed.
Lemma lem1980966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1980967 (n : nat) (m : nat) : (term39 n m) = (term40 n m).
Proof. exact (MK_COMB (@lem1980966) (@lem1980963 n m)). Qed.
Lemma lem1980973 (x : nat) (y : nat) : (DECIMAL x y) = (term28 x y).
Proof. exact (EQ_MP (@lem1980925 x y) (@lem1980924 x y)). Qed.
Lemma lem1980974 (m : nat) (n : nat) : (DECIMAL m n) = (term28 m n).
Proof. exact (@lem1980973 m n). Qed.
Lemma lem1980975 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1980976 (m : nat) (n : nat) : (term41 m n) = (term29 m n).
Proof. exact (MK_COMB (@lem1980975) (@lem1980974 m n)). Qed.
Lemma lem1980978 (y : real) (x : real) : (term24 x y) = (real_div y x).
Proof. exact (EQ_MP (@lem1980919 y x) (@lem1980918 x y)). Qed.
Lemma lem1980979 (n : nat) (m : nat) : (term29 m n) = (term28 n m).
Proof. exact (@lem1980978 (real_of_num n) (real_of_num m)). Qed.
Lemma lem1980980 (n : nat) (m : nat) : (term41 m n) = (term28 n m).
Proof. exact (TRANS (@lem1980976 m n) (@lem1980979 n m)). Qed.
Lemma lem1980981 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1980982 (n : nat) (m : nat) : (term42 m n) = (term31 n m).
Proof. exact (MK_COMB (@lem1980981) (@lem1980980 n m)). Qed.
Lemma lem1980983 (n : nat) (m : nat) : (term28 n m) = (term28 n m).
Proof. exact (eq_refl (term28 n m)). Qed.
Lemma lem1980984 (n : nat) (m : nat) : ((term41 m n) = (term28 n m)) = ((term28 n m) = (term28 n m)).
Proof. exact (MK_COMB (@lem1980982 n m) (@lem1980983 n m)). Qed.
Lemma lem1980986 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1980987 (x : real) : (x = x) = True.
Proof. exact (@lem1980986 real x). Qed.
Lemma lem1980988 (n : nat) (m : nat) : ((term28 n m) = (term28 n m)) = True.
Proof. exact (@lem1980987 (term28 n m)). Qed.
Lemma lem1980989 (n : nat) (m : nat) : ((term41 m n) = (term28 n m)) = True.
Proof. exact (TRANS (@lem1980984 n m) (@lem1980988 n m)). Qed.
Lemma lem1980990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1980991 (n : nat) (m : nat) : (term43 n m) = (and True).
Proof. exact (MK_COMB (@lem1980990) (@lem1980989 n m)). Qed.
Lemma lem1980995 (x : nat) (y : nat) : (DECIMAL x y) = (term28 x y).
Proof. exact (EQ_MP (@lem1980925 x y) (@lem1980924 x y)). Qed.
Lemma lem1980996 (m : nat) (n : nat) : (DECIMAL m n) = (term28 m n).
Proof. exact (@lem1980995 m n). Qed.
Lemma lem1980997 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1980998 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem1980997) (@lem1980996 m n)). Qed.
Lemma lem1980999 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1981000 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (MK_COMB (@lem1980999) (@lem1980998 m n)). Qed.
Lemma lem1981001 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1981002 (m : nat) (n : nat) : (term48 m n) = (term49 m n).
Proof. exact (MK_COMB (@lem1981001) (@lem1981000 m n)). Qed.
Lemma lem1981003 (n : nat) (m : nat) : (term38 n m) = (term38 n m).
Proof. exact (eq_refl (term38 n m)). Qed.
Lemma lem1981004 (n : nat) (m : nat) : ((term46 m n) = (term38 n m)) = ((term47 m n) = (term38 n m)).
Proof. exact (MK_COMB (@lem1981002 m n) (@lem1981003 n m)). Qed.
Lemma lem1981007 (n : nat) (m : nat) : (term50 n m) = (term51 n m).
Proof. exact (MK_COMB (@lem1980991 n m) (@lem1981004 n m)). Qed.
Lemma lem1981009 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1981010 (n : nat) (m : nat) : (term51 n m) = ((term47 m n) = (term38 n m)).
Proof. exact (@lem1981009 ((term47 m n) = (term38 n m))). Qed.
Lemma lem1981013 (n : nat) (m : nat) : (term50 n m) = ((term47 m n) = (term38 n m)).
Proof. exact (TRANS (@lem1981007 n m) (@lem1981010 n m)). Qed.
Lemma lem1981014 (n : nat) (m : nat) : (term52 n m) = (term53 n m).
Proof. exact (MK_COMB (@lem1980967 n m) (@lem1981013 n m)). Qed.
Lemma lem1981017 (n : nat) (m : nat) : (term54 n m) = (term55 n m).
Proof. exact (MK_COMB (@lem1980952 n m) (@lem1981014 n m)). Qed.
Lemma lem1981019 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1981020 (n : nat) (m : nat) : (term55 n m) = (term53 n m).
Proof. exact (@lem1981019 (term53 n m)). Qed.
Lemma lem1981027 (n : nat) (m : nat) : (term54 n m) = (term53 n m).
Proof. exact (TRANS (@lem1981017 n m) (@lem1981020 n m)). Qed.
Lemma lem1981028 (n : nat) : (term56 n) = (term56 n).
Proof. exact (eq_refl (term56 n)). Qed.
Lemma lem1981029 (n : nat) (m : nat) : (term57 n m) = (term58 n m).
Proof. exact (MK_COMB (@lem1981028 n) (@lem1981027 n m)). Qed.
Lemma lem1981032 (n : nat) : (term59 n) = (term59 n).
Proof. exact (eq_refl (term59 n)). Qed.
Lemma lem1981033 (n : nat) (m : nat) : (term60 n m) = (term61 n m).
Proof. exact (MK_COMB (@lem1981032 n) (@lem1981029 n m)). Qed.
Lemma lem1981036 (n : nat) (m : nat) : (term61 n m) = (term60 n m).
Proof. exact (SYM (@lem1981033 n m)). Qed.
Lemma lem1981042 (x : real) (y : real) : (real_div x y) = (term17 x y).
Proof. exact (EQ_MP (@lem1980910 x y) (@lem1980909 x y)). Qed.
Lemma lem1981043 (n : nat) : (term62 n) = (term63 n).
Proof. exact (@lem1981042 term64 (real_of_num n)). Qed.
Lemma lem1981045 (x : real) : (term13 x) = x.
Proof. exact (EQ_MP (@lem1980894 x) (@lem1980893 x)). Qed.
Lemma lem1981046 (n : nat) : (term63 n) = (term65 n).
Proof. exact (@lem1981045 (term65 n)). Qed.
Lemma lem1981047 (n : nat) : (term62 n) = (term65 n).
Proof. exact (TRANS (@lem1981043 n) (@lem1981046 n)). Qed.
Lemma lem1981048 (n : nat) : (term66 n) = (term66 n).
Proof. exact (eq_refl (term66 n)). Qed.
Lemma lem1981049 (n : nat) : ((term65 n) = (term62 n)) = ((term65 n) = (term65 n)).
Proof. exact (MK_COMB (@lem1981048 n) (@lem1981047 n)). Qed.
Lemma lem1981051 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1981052 (x : real) : (x = x) = True.
Proof. exact (@lem1981051 real x). Qed.
Lemma lem1981053 (n : nat) : ((term65 n) = (term65 n)) = True.
Proof. exact (@lem1981052 (term65 n)). Qed.
Lemma lem1981054 (n : nat) : ((term65 n) = (term62 n)) = True.
Proof. exact (TRANS (@lem1981049 n) (@lem1981053 n)). Qed.
Lemma lem1981055 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1981056 (n : nat) : (term59 n) = (and True).
Proof. exact (MK_COMB (@lem1981055) (@lem1981054 n)). Qed.
Lemma lem1981062 (x : real) : (term19 x) = (term20 x).
Proof. exact (EQ_MP (@lem1980913 x) (@lem1980912 x)). Qed.
Lemma lem1981063 (n : nat) : (term67 n) = (term68 n).
Proof. exact (@lem1981062 (real_of_num n)). Qed.
Lemma lem1981064 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1981065 (n : nat) : (term69 n) = (term70 n).
Proof. exact (MK_COMB (@lem1981064) (@lem1981063 n)). Qed.
Lemma lem1981067 (x : real) (y : real) : (real_div x y) = (term17 x y).
Proof. exact (EQ_MP (@lem1980910 x y) (@lem1980909 x y)). Qed.
Lemma lem1981068 (n : nat) : (term71 n) = (term72 n).
Proof. exact (@lem1981067 term73 (real_of_num n)). Qed.
Lemma lem1981070 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem1980891 x y) (@lem1980890 x y)). Qed.
Lemma lem1981071 (n : nat) : (term72 n) = (term74 n).
Proof. exact (@lem1981070 term64 (term65 n)). Qed.
Lemma lem1981072 (n : nat) : (term71 n) = (term74 n).
Proof. exact (TRANS (@lem1981068 n) (@lem1981071 n)). Qed.
Lemma lem1981074 (x : real) : (term13 x) = x.
Proof. exact (EQ_MP (@lem1980894 x) (@lem1980893 x)). Qed.
Lemma lem1981075 (n : nat) : (term63 n) = (term65 n).
Proof. exact (@lem1981074 (term65 n)). Qed.
Lemma lem1981076 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1981077 (n : nat) : (term74 n) = (term68 n).
Proof. exact (MK_COMB (@lem1981076) (@lem1981075 n)). Qed.
Lemma lem1981078 (n : nat) : (term71 n) = (term68 n).
Proof. exact (TRANS (@lem1981072 n) (@lem1981077 n)). Qed.
Lemma lem1981079 (n : nat) : ((term67 n) = (term71 n)) = ((term68 n) = (term68 n)).
Proof. exact (MK_COMB (@lem1981065 n) (@lem1981078 n)). Qed.
Lemma lem1981081 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1981082 (x : real) : (x = x) = True.
Proof. exact (@lem1981081 real x). Qed.
Lemma lem1981083 (n : nat) : ((term68 n) = (term68 n)) = True.
Proof. exact (@lem1981082 (term68 n)). Qed.
Lemma lem1981084 (n : nat) : ((term67 n) = (term71 n)) = True.
Proof. exact (TRANS (@lem1981079 n) (@lem1981083 n)). Qed.
Lemma lem1981085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1981086 (n : nat) : (term56 n) = (and True).
Proof. exact (MK_COMB (@lem1981085) (@lem1981084 n)). Qed.
Lemma lem1981092 (x : real) (y : real) : (real_div x y) = (term17 x y).
Proof. exact (EQ_MP (@lem1980910 x y) (@lem1980909 x y)). Qed.
Lemma lem1981093 (n : nat) (m : nat) : (term34 n m) = (term75 n m).
Proof. exact (@lem1981092 (real_of_num n) (term35 m)). Qed.
Lemma lem1981095 (n : real) (m : real) : (real_mul m n) = (real_mul n m).
Proof. exact (proj1 (@lem1486340 n m (@el real))). Qed.
Lemma lem1981096 (m : nat) (n : nat) : (term75 n m) = (term76 m n).
Proof. exact (@lem1981095 (term67 m) (real_of_num n)). Qed.
Lemma lem1981100 (m : nat) (n : nat) : (term34 n m) = (term76 m n).
Proof. exact (TRANS (@lem1981093 n m) (@lem1981096 m n)). Qed.
Lemma lem1981102 (x : real) : (term19 x) = (term20 x).
Proof. exact (EQ_MP (@lem1980913 x) (@lem1980912 x)). Qed.
Lemma lem1981103 (m : nat) : (term67 m) = (term68 m).
Proof. exact (@lem1981102 (real_of_num m)). Qed.
Lemma lem1981104 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1981105 (m : nat) : (term77 m) = (term78 m).
Proof. exact (MK_COMB (@lem1981104) (@lem1981103 m)). Qed.
Lemma lem1981106 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem1981107 (m : nat) (n : nat) : (term76 m n) = (term79 m n).
Proof. exact (MK_COMB (@lem1981105 m) (@lem1981106 n)). Qed.
Lemma lem1981109 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem1980891 x y) (@lem1980890 x y)). Qed.
Lemma lem1981110 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (@lem1981109 (term65 m) (real_of_num n)). Qed.
Lemma lem1981114 (m : nat) (n : nat) : (term76 m n) = (term80 m n).
Proof. exact (TRANS (@lem1981107 m n) (@lem1981110 m n)). Qed.
Lemma lem1981115 (m : nat) (n : nat) : (term34 n m) = (term80 m n).
Proof. exact (TRANS (@lem1981100 m n) (@lem1981114 m n)). Qed.
Lemma lem1981116 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1981117 (m : nat) (n : nat) : (term37 n m) = (term81 m n).
Proof. exact (MK_COMB (@lem1981116) (@lem1981115 m n)). Qed.
Lemma lem1981119 (x : real) (y : real) : (real_div x y) = (term17 x y).
Proof. exact (EQ_MP (@lem1980910 x y) (@lem1980909 x y)). Qed.
Lemma lem1981120 (n : nat) (m : nat) : (term38 n m) = (term82 n m).
Proof. exact (@lem1981119 (term35 n) (real_of_num m)). Qed.
Lemma lem1981122 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem1980891 x y) (@lem1980890 x y)). Qed.
Lemma lem1981123 (n : nat) (m : nat) : (term82 n m) = (term83 n m).
Proof. exact (@lem1981122 (real_of_num n) (term65 m)). Qed.
Lemma lem1981124 (n : nat) (m : nat) : (term38 n m) = (term83 n m).
Proof. exact (TRANS (@lem1981120 n m) (@lem1981123 n m)). Qed.
Lemma lem1981126 (n : real) (m : real) : (real_mul m n) = (real_mul n m).
Proof. exact (proj1 (@lem1486340 n m (@el real))). Qed.
Lemma lem1981127 (m : nat) (n : nat) : (term84 n m) = (term85 m n).
Proof. exact (@lem1981126 (term65 m) (real_of_num n)). Qed.
Lemma lem1981131 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1981132 (m : nat) (n : nat) : (term83 n m) = (term80 m n).
Proof. exact (MK_COMB (@lem1981131) (@lem1981127 m n)). Qed.
Lemma lem1981133 (m : nat) (n : nat) : (term38 n m) = (term80 m n).
Proof. exact (TRANS (@lem1981124 n m) (@lem1981132 m n)). Qed.
Lemma lem1981134 (m : nat) (n : nat) : ((term34 n m) = (term38 n m)) = ((term80 m n) = (term80 m n)).
Proof. exact (MK_COMB (@lem1981117 m n) (@lem1981133 m n)). Qed.
Lemma lem1981136 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1981137 (x : real) : (x = x) = True.
Proof. exact (@lem1981136 real x). Qed.
Lemma lem1981138 (m : nat) (n : nat) : ((term80 m n) = (term80 m n)) = True.
Proof. exact (@lem1981137 (term80 m n)). Qed.
Lemma lem1981139 (n : nat) (m : nat) : ((term34 n m) = (term38 n m)) = True.
Proof. exact (TRANS (@lem1981134 m n) (@lem1981138 m n)). Qed.
Lemma lem1981140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1981141 (n : nat) (m : nat) : (term40 n m) = (and True).
Proof. exact (MK_COMB (@lem1981140) (@lem1981139 n m)). Qed.
Lemma lem1981145 (x : real) : (term19 x) = (term20 x).
Proof. exact (EQ_MP (@lem1980913 x) (@lem1980912 x)). Qed.
Lemma lem1981146 (m : nat) (n : nat) : (term47 m n) = (term86 m n).
Proof. exact (@lem1981145 (term28 m n)). Qed.
Lemma lem1981148 (x : real) (y : real) : (real_div x y) = (term17 x y).
Proof. exact (EQ_MP (@lem1980910 x y) (@lem1980909 x y)). Qed.
Lemma lem1981149 (m : nat) (n : nat) : (term28 m n) = (term84 m n).
Proof. exact (@lem1981148 (real_of_num m) (real_of_num n)). Qed.
Lemma lem1981151 (n : real) (m : real) : (real_mul m n) = (real_mul n m).
Proof. exact (proj1 (@lem1486340 n m (@el real))). Qed.
Lemma lem1981152 (n : nat) (m : nat) : (term84 m n) = (term85 n m).
Proof. exact (@lem1981151 (term65 n) (real_of_num m)). Qed.
Lemma lem1981156 (n : nat) (m : nat) : (term28 m n) = (term85 n m).
Proof. exact (TRANS (@lem1981149 m n) (@lem1981152 n m)). Qed.
Lemma lem1981157 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1981158 (n : nat) (m : nat) : (term29 m n) = (term87 n m).
Proof. exact (MK_COMB (@lem1981157) (@lem1981156 n m)). Qed.
Lemma lem1981160 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem1980885 x y) (@lem1980884 x y)). Qed.
Lemma lem1981161 (n : nat) (m : nat) : (term87 n m) = (term88 n m).
Proof. exact (@lem1981160 (term65 n) (real_of_num m)). Qed.
Lemma lem1981163 (n : real) (m : real) : (real_mul m n) = (real_mul n m).
Proof. exact (proj1 (@lem1486340 n m (@el real))). Qed.
Lemma lem1981164 (m : nat) (n : nat) : (term88 n m) = (term89 m n).
Proof. exact (@lem1981163 (term65 m) (term90 n)). Qed.
Lemma lem1981169 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1980879 x) (@lem1980878 x)). Qed.
Lemma lem1981170 (n : nat) : (term90 n) = (real_of_num n).
Proof. exact (@lem1981169 (real_of_num n)). Qed.
Lemma lem1981171 (m : nat) : (term91 m) = (term91 m).
Proof. exact (eq_refl (term91 m)). Qed.
Lemma lem1981172 (m : nat) (n : nat) : (term89 m n) = (term85 m n).
Proof. exact (MK_COMB (@lem1981171 m) (@lem1981170 n)). Qed.
Lemma lem1981176 (m : nat) (n : nat) : (term88 n m) = (term85 m n).
Proof. exact (TRANS (@lem1981164 m n) (@lem1981172 m n)). Qed.
Lemma lem1981177 (m : nat) (n : nat) : (term87 n m) = (term85 m n).
Proof. exact (TRANS (@lem1981161 n m) (@lem1981176 m n)). Qed.
Lemma lem1981178 (m : nat) (n : nat) : (term29 m n) = (term85 m n).
Proof. exact (TRANS (@lem1981158 n m) (@lem1981177 m n)). Qed.
Lemma lem1981179 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1981180 (m : nat) (n : nat) : (term86 m n) = (term80 m n).
Proof. exact (MK_COMB (@lem1981179) (@lem1981178 m n)). Qed.
Lemma lem1981181 (m : nat) (n : nat) : (term47 m n) = (term80 m n).
Proof. exact (TRANS (@lem1981146 m n) (@lem1981180 m n)). Qed.
Lemma lem1981182 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1981183 (m : nat) (n : nat) : (term49 m n) = (term81 m n).
Proof. exact (MK_COMB (@lem1981182) (@lem1981181 m n)). Qed.
Lemma lem1981185 (x : real) (y : real) : (real_div x y) = (term17 x y).
Proof. exact (EQ_MP (@lem1980910 x y) (@lem1980909 x y)). Qed.
Lemma lem1981186 (n : nat) (m : nat) : (term38 n m) = (term82 n m).
Proof. exact (@lem1981185 (term35 n) (real_of_num m)). Qed.
Lemma lem1981188 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem1980891 x y) (@lem1980890 x y)). Qed.
Lemma lem1981189 (n : nat) (m : nat) : (term82 n m) = (term83 n m).
Proof. exact (@lem1981188 (real_of_num n) (term65 m)). Qed.
Lemma lem1981190 (n : nat) (m : nat) : (term38 n m) = (term83 n m).
Proof. exact (TRANS (@lem1981186 n m) (@lem1981189 n m)). Qed.
Lemma lem1981192 (n : real) (m : real) : (real_mul m n) = (real_mul n m).
Proof. exact (proj1 (@lem1486340 n m (@el real))). Qed.
Lemma lem1981193 (m : nat) (n : nat) : (term84 n m) = (term85 m n).
Proof. exact (@lem1981192 (term65 m) (real_of_num n)). Qed.
Lemma lem1981197 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1981198 (m : nat) (n : nat) : (term83 n m) = (term80 m n).
Proof. exact (MK_COMB (@lem1981197) (@lem1981193 m n)). Qed.
Lemma lem1981199 (m : nat) (n : nat) : (term38 n m) = (term80 m n).
Proof. exact (TRANS (@lem1981190 n m) (@lem1981198 m n)). Qed.
Lemma lem1981200 (m : nat) (n : nat) : ((term47 m n) = (term38 n m)) = ((term80 m n) = (term80 m n)).
Proof. exact (MK_COMB (@lem1981183 m n) (@lem1981199 m n)). Qed.
Lemma lem1981202 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1981203 (x : real) : (x = x) = True.
Proof. exact (@lem1981202 real x). Qed.
Lemma lem1981204 (m : nat) (n : nat) : ((term80 m n) = (term80 m n)) = True.
Proof. exact (@lem1981203 (term80 m n)). Qed.
Lemma lem1981205 (n : nat) (m : nat) : ((term47 m n) = (term38 n m)) = True.
Proof. exact (TRANS (@lem1981200 m n) (@lem1981204 m n)). Qed.
Lemma lem1981206 (n : nat) (m : nat) : (term53 n m) = (True /\ True).
Proof. exact (MK_COMB (@lem1981141 n m) (@lem1981205 n m)). Qed.
Lemma lem1981208 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1981209 : (True /\ True) = True.
Proof. exact (@lem1981208 True). Qed.
Lemma lem1981210 (n : nat) (m : nat) : (term53 n m) = True.
Proof. exact (TRANS (@lem1981206 n m) (@lem1981209)). Qed.
Lemma lem1981211 (n : nat) (m : nat) : (term58 n m) = (True /\ True).
Proof. exact (MK_COMB (@lem1981086 n) (@lem1981210 n m)). Qed.
Lemma lem1981213 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1981214 : (True /\ True) = True.
Proof. exact (@lem1981213 True). Qed.
Lemma lem1981215 (n : nat) (m : nat) : (term58 n m) = True.
Proof. exact (TRANS (@lem1981211 n m) (@lem1981214)). Qed.
Lemma lem1981216 (n : nat) (m : nat) : (term61 n m) = (True /\ True).
Proof. exact (MK_COMB (@lem1981056 n) (@lem1981215 n m)). Qed.
Lemma lem1981218 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1981219 : (True /\ True) = True.
Proof. exact (@lem1981218 True). Qed.
Lemma lem1981220 (n : nat) (m : nat) : (term61 n m) = True.
Proof. exact (TRANS (@lem1981216 n m) (@lem1981219)). Qed.
Lemma lem1981221 (n : nat) (m : nat) : True = (term61 n m).
Proof. exact (SYM (@lem1981220 n m)). Qed.
Lemma lem1981222 (n : nat) (m : nat) : term61 n m.
Proof. exact (EQ_MP (@lem1981221 n m) (@lem0)). Qed.
Lemma lem1981223 (n : nat) (m : nat) : term60 n m.
Proof. exact (EQ_MP (@lem1981036 n m) (@lem1981222 n m)). Qed.
