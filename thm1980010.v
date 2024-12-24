Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1980010_term_abbrevs.
Require Import DECIMAL_spec.
Require Import REAL_DIV_1_spec.
Require Import REAL_MUL_LNEG_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1979882 (x : real) : term0 x.
Proof. exact (@lem1360913 x). Qed.
Lemma lem1979883 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1979884 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1979883 x) (@lem1979882 x)). Qed.
Lemma lem1979885 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1979884 x y). Qed.
Lemma lem1979886 (x : real) (y : real) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1979888 (x : real) : term5 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1979889 (x : real) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1979890 (x : real) : term6 x.
Proof. exact (EQ_MP (@lem1979889 x) (@lem1979888 x)). Qed.
Lemma lem1979891 (x : real) (y : real) : term7 x y.
Proof. exact (@lem1979890 x y). Qed.
Lemma lem1979892 (x : real) (y : real) : (term7 x y) = ((real_div x y) = (term8 x y)).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1979894 (x : nat) : term9 x.
Proof. exact (@lem1977711 x). Qed.
Lemma lem1979895 (x : nat) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1979896 (x : nat) : term10 x.
Proof. exact (EQ_MP (@lem1979895 x) (@lem1979894 x)). Qed.
Lemma lem1979897 (x : nat) (y : nat) : term11 x y.
Proof. exact (@lem1979896 x y). Qed.
Lemma lem1979898 (x : nat) (y : nat) : (term11 x y) = ((DECIMAL x y) = (term12 x y)).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1979900 (x : real) : term13 x.
Proof. exact (@lem1592965 x). Qed.
Lemma lem1979901 (x : real) : (term13 x) = ((term14 x) = x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1979908 (x : real) : (term14 x) = x.
Proof. exact (EQ_MP (@lem1979901 x) (@lem1979900 x)). Qed.
Lemma lem1979909 (x : nat) : (term15 x) = (real_of_num x).
Proof. exact (@lem1979908 (real_of_num x)). Qed.
Lemma lem1979910 (x : nat) : (term16 x) = (term16 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1979911 (x : nat) : ((real_of_num x) = (term15 x)) = ((real_of_num x) = (real_of_num x)).
Proof. exact (MK_COMB (@lem1979910 x) (@lem1979909 x)). Qed.
Lemma lem1979913 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1979914 (x : real) : (x = x) = True.
Proof. exact (@lem1979913 real x). Qed.
Lemma lem1979915 (x : nat) : ((real_of_num x) = (real_of_num x)) = True.
Proof. exact (@lem1979914 (real_of_num x)). Qed.
Lemma lem1979916 (x : nat) : ((real_of_num x) = (term15 x)) = True.
Proof. exact (TRANS (@lem1979911 x) (@lem1979915 x)). Qed.
Lemma lem1979917 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1979918 (x : nat) : (term17 x) = (and True).
Proof. exact (MK_COMB (@lem1979917) (@lem1979916 x)). Qed.
Lemma lem1979924 (x : real) : (term14 x) = x.
Proof. exact (EQ_MP (@lem1979901 x) (@lem1979900 x)). Qed.
Lemma lem1979925 (x : nat) : (term18 x) = (term19 x).
Proof. exact (@lem1979924 (term19 x)). Qed.
Lemma lem1979926 (x : nat) : (term20 x) = (term20 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1979927 (x : nat) : ((term19 x) = (term18 x)) = ((term19 x) = (term19 x)).
Proof. exact (MK_COMB (@lem1979926 x) (@lem1979925 x)). Qed.
Lemma lem1979929 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1979930 (x : real) : (x = x) = True.
Proof. exact (@lem1979929 real x). Qed.
Lemma lem1979931 (x : nat) : ((term19 x) = (term19 x)) = True.
Proof. exact (@lem1979930 (term19 x)). Qed.
Lemma lem1979932 (x : nat) : ((term19 x) = (term18 x)) = True.
Proof. exact (TRANS (@lem1979927 x) (@lem1979931 x)). Qed.
Lemma lem1979933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1979934 (x : nat) : (term21 x) = (and True).
Proof. exact (MK_COMB (@lem1979933) (@lem1979932 x)). Qed.
Lemma lem1979940 (x : nat) (y : nat) : (DECIMAL x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1979898 x y) (@lem1979897 x y)). Qed.
Lemma lem1979941 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1979942 (x : nat) (y : nat) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1979941) (@lem1979940 x y)). Qed.
Lemma lem1979943 (x : nat) (y : nat) : (term12 x y) = (term12 x y).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1979944 (x : nat) (y : nat) : ((DECIMAL x y) = (term12 x y)) = ((term12 x y) = (term12 x y)).
Proof. exact (MK_COMB (@lem1979942 x y) (@lem1979943 x y)). Qed.
Lemma lem1979946 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1979947 (x : real) : (x = x) = True.
Proof. exact (@lem1979946 real x). Qed.
Lemma lem1979948 (x : nat) (y : nat) : ((term12 x y) = (term12 x y)) = True.
Proof. exact (@lem1979947 (term12 x y)). Qed.
Lemma lem1979949 (x : nat) (y : nat) : ((DECIMAL x y) = (term12 x y)) = True.
Proof. exact (TRANS (@lem1979944 x y) (@lem1979948 x y)). Qed.
Lemma lem1979950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1979951 (x : nat) (y : nat) : (term24 x y) = (and True).
Proof. exact (MK_COMB (@lem1979950) (@lem1979949 x y)). Qed.
Lemma lem1979955 (x : nat) (y : nat) : (DECIMAL x y) = (term12 x y).
Proof. exact (EQ_MP (@lem1979898 x y) (@lem1979897 x y)). Qed.
Lemma lem1979956 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1979957 (x : nat) (y : nat) : (term25 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem1979956) (@lem1979955 x y)). Qed.
Lemma lem1979958 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1979959 (x : nat) (y : nat) : (term27 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1979958) (@lem1979957 x y)). Qed.
Lemma lem1979960 (x : nat) (y : nat) : (term29 x y) = (term29 x y).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem1979961 (x : nat) (y : nat) : ((term25 x y) = (term29 x y)) = ((term26 x y) = (term29 x y)).
Proof. exact (MK_COMB (@lem1979959 x y) (@lem1979960 x y)). Qed.
Lemma lem1979964 (x : nat) (y : nat) : (term30 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1979951 x y) (@lem1979961 x y)). Qed.
Lemma lem1979966 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1979967 (x : nat) (y : nat) : (term31 x y) = ((term26 x y) = (term29 x y)).
Proof. exact (@lem1979966 ((term26 x y) = (term29 x y))). Qed.
Lemma lem1979970 (x : nat) (y : nat) : (term30 x y) = ((term26 x y) = (term29 x y)).
Proof. exact (TRANS (@lem1979964 x y) (@lem1979967 x y)). Qed.
Lemma lem1979971 (x : nat) (y : nat) : (term32 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1979934 x) (@lem1979970 x y)). Qed.
Lemma lem1979973 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1979974 (x : nat) (y : nat) : (term31 x y) = ((term26 x y) = (term29 x y)).
Proof. exact (@lem1979973 ((term26 x y) = (term29 x y))). Qed.
Lemma lem1979977 (x : nat) (y : nat) : (term32 x y) = ((term26 x y) = (term29 x y)).
Proof. exact (TRANS (@lem1979971 x y) (@lem1979974 x y)). Qed.
Lemma lem1979978 (x : nat) (y : nat) : (term33 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1979918 x) (@lem1979977 x y)). Qed.
Lemma lem1979980 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1979981 (x : nat) (y : nat) : (term31 x y) = ((term26 x y) = (term29 x y)).
Proof. exact (@lem1979980 ((term26 x y) = (term29 x y))). Qed.
Lemma lem1979984 (x : nat) (y : nat) : (term33 x y) = ((term26 x y) = (term29 x y)).
Proof. exact (TRANS (@lem1979978 x y) (@lem1979981 x y)). Qed.
Lemma lem1979985 (x : nat) (y : nat) : ((term26 x y) = (term29 x y)) = (term33 x y).
Proof. exact (SYM (@lem1979984 x y)). Qed.
Lemma lem1979989 (x : real) (y : real) : (real_div x y) = (term8 x y).
Proof. exact (EQ_MP (@lem1979892 x y) (@lem1979891 x y)). Qed.
Lemma lem1979990 (x : nat) (y : nat) : (term12 x y) = (term34 x y).
Proof. exact (@lem1979989 (real_of_num x) (real_of_num y)). Qed.
Lemma lem1979991 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1979992 (x : nat) (y : nat) : (term26 x y) = (term35 x y).
Proof. exact (MK_COMB (@lem1979991) (@lem1979990 x y)). Qed.
Lemma lem1979993 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1979994 (x : nat) (y : nat) : (term28 x y) = (term36 x y).
Proof. exact (MK_COMB (@lem1979993) (@lem1979992 x y)). Qed.
Lemma lem1979996 (x : real) (y : real) : (real_div x y) = (term8 x y).
Proof. exact (EQ_MP (@lem1979892 x y) (@lem1979891 x y)). Qed.
Lemma lem1979997 (x : nat) (y : nat) : (term29 x y) = (term37 x y).
Proof. exact (@lem1979996 (term19 x) (real_of_num y)). Qed.
Lemma lem1979999 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem1979886 x y) (@lem1979885 x y)). Qed.
Lemma lem1980000 (x : nat) (y : nat) : (term37 x y) = (term35 x y).
Proof. exact (@lem1979999 (real_of_num x) (term38 y)). Qed.
Lemma lem1980001 (x : nat) (y : nat) : (term29 x y) = (term35 x y).
Proof. exact (TRANS (@lem1979997 x y) (@lem1980000 x y)). Qed.
Lemma lem1980002 (x : nat) (y : nat) : ((term26 x y) = (term29 x y)) = ((term35 x y) = (term35 x y)).
Proof. exact (MK_COMB (@lem1979994 x y) (@lem1980001 x y)). Qed.
Lemma lem1980004 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1980005 (x : real) : (x = x) = True.
Proof. exact (@lem1980004 real x). Qed.
Lemma lem1980006 (x : nat) (y : nat) : ((term35 x y) = (term35 x y)) = True.
Proof. exact (@lem1980005 (term35 x y)). Qed.
Lemma lem1980007 (x : nat) (y : nat) : ((term26 x y) = (term29 x y)) = True.
Proof. exact (TRANS (@lem1980002 x y) (@lem1980006 x y)). Qed.
Lemma lem1980008 (x : nat) (y : nat) : True = ((term26 x y) = (term29 x y)).
Proof. exact (SYM (@lem1980007 x y)). Qed.
Lemma lem1980009 (x : nat) (y : nat) : (term26 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem1980008 x y) (@lem0)). Qed.
Lemma lem1980010 (x : nat) (y : nat) : term33 x y.
Proof. exact (EQ_MP (@lem1979985 x y) (@lem1980009 x y)). Qed.
