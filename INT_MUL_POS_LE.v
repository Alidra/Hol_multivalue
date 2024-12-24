Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MUL_POS_LE_term_abbrevs.
Require Import REAL_MUL_POS_LE_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306042 (x : int) : term0 x.
Proof. exact (@lem1628374 (real_of_int x)). Qed.
Lemma lem2306043 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306044 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2306043 x) (@lem2306042 x)). Qed.
Lemma lem2306045 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2306044 x (real_of_int y)). Qed.
Lemma lem2306046 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2306047 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2306046 x y) (@lem2306045 x y)). Qed.
Lemma lem2306049 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306050 : term6 = term7.
Proof. exact (@lem2306049 (NUMERAL 0)). Qed.
Lemma lem2306051 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2306052 : term8 = term9.
Proof. exact (MK_COMB (@lem2306051) (@lem2306050)). Qed.
Lemma lem2306054 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306055 (x : int) (y : int) : (term3 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2306052) (@lem2306054 x y)). Qed.
Lemma lem2306057 (x : int) (y : int) : (term13 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2306058 (x : int) (y : int) : (term12 x y) = (term14 x y).
Proof. exact (@lem2306057 term15 (int_mul x y)). Qed.
Lemma lem2306059 (x : int) (y : int) : (term3 x y) = (term14 x y).
Proof. exact (TRANS (@lem2306055 x y) (@lem2306058 x y)). Qed.
Lemma lem2306060 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2306061 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem2306060) (@lem2306059 x y)). Qed.
Lemma lem2306063 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306064 : term6 = term7.
Proof. exact (@lem2306063 (NUMERAL 0)). Qed.
Lemma lem2306065 (x : int) : (term18 x) = (term18 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem2306066 (x : int) : ((real_of_int x) = term6) = ((real_of_int x) = term7).
Proof. exact (MK_COMB (@lem2306065 x) (@lem2306064)). Qed.
Lemma lem2306068 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306069 (x : int) : ((real_of_int x) = term7) = (x = term15).
Proof. exact (@lem2306068 x term15). Qed.
Lemma lem2306070 (x : int) : ((real_of_int x) = term6) = (x = term15).
Proof. exact (TRANS (@lem2306066 x) (@lem2306069 x)). Qed.
Lemma lem2306071 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2306072 (x : int) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem2306071) (@lem2306070 x)). Qed.
Lemma lem2306074 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306075 : term6 = term7.
Proof. exact (@lem2306074 (NUMERAL 0)). Qed.
Lemma lem2306076 (y : int) : (term18 y) = (term18 y).
Proof. exact (eq_refl (term18 y)). Qed.
Lemma lem2306077 (y : int) : ((real_of_int y) = term6) = ((real_of_int y) = term7).
Proof. exact (MK_COMB (@lem2306076 y) (@lem2306075)). Qed.
Lemma lem2306079 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306080 (y : int) : ((real_of_int y) = term7) = (y = term15).
Proof. exact (@lem2306079 y term15). Qed.
Lemma lem2306081 (y : int) : ((real_of_int y) = term6) = (y = term15).
Proof. exact (TRANS (@lem2306077 y) (@lem2306080 y)). Qed.
Lemma lem2306082 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2306083 (y : int) : (term19 y) = (term20 y).
Proof. exact (MK_COMB (@lem2306082) (@lem2306081 y)). Qed.
Lemma lem2306085 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306086 : term6 = term7.
Proof. exact (@lem2306085 (NUMERAL 0)). Qed.
Lemma lem2306087 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2306088 : term21 = term22.
Proof. exact (MK_COMB (@lem2306087) (@lem2306086)). Qed.
Lemma lem2306089 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2306090 (x : int) : (term23 x) = (term24 x).
Proof. exact (MK_COMB (@lem2306088) (@lem2306089 x)). Qed.
Lemma lem2306092 (x : int) (y : int) : (term25 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306093 (x : int) : (term24 x) = (term26 x).
Proof. exact (@lem2306092 term15 x). Qed.
Lemma lem2306094 (x : int) : (term23 x) = (term26 x).
Proof. exact (TRANS (@lem2306090 x) (@lem2306093 x)). Qed.
Lemma lem2306095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2306096 (x : int) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem2306095) (@lem2306094 x)). Qed.
Lemma lem2306098 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306099 : term6 = term7.
Proof. exact (@lem2306098 (NUMERAL 0)). Qed.
Lemma lem2306100 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2306101 : term21 = term22.
Proof. exact (MK_COMB (@lem2306100) (@lem2306099)). Qed.
Lemma lem2306102 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2306103 (y : int) : (term23 y) = (term24 y).
Proof. exact (MK_COMB (@lem2306101) (@lem2306102 y)). Qed.
Lemma lem2306105 (x : int) (y : int) : (term25 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306106 (y : int) : (term24 y) = (term26 y).
Proof. exact (@lem2306105 term15 y). Qed.
Lemma lem2306107 (y : int) : (term23 y) = (term26 y).
Proof. exact (TRANS (@lem2306103 y) (@lem2306106 y)). Qed.
Lemma lem2306108 (x : int) (y : int) : (term29 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem2306096 x) (@lem2306107 y)). Qed.
Lemma lem2306109 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2306110 (x : int) (y : int) : (term31 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem2306109) (@lem2306108 x y)). Qed.
Lemma lem2306112 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306113 : term6 = term7.
Proof. exact (@lem2306112 (NUMERAL 0)). Qed.
Lemma lem2306114 (x : int) : (term33 x) = (term33 x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem2306115 (x : int) : (term34 x) = (term35 x).
Proof. exact (MK_COMB (@lem2306114 x) (@lem2306113)). Qed.
Lemma lem2306117 (x : int) (y : int) : (term25 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306118 (x : int) : (term35 x) = (term36 x).
Proof. exact (@lem2306117 x term15). Qed.
Lemma lem2306119 (x : int) : (term34 x) = (term36 x).
Proof. exact (TRANS (@lem2306115 x) (@lem2306118 x)). Qed.
Lemma lem2306120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2306121 (x : int) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem2306120) (@lem2306119 x)). Qed.
Lemma lem2306123 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306124 : term6 = term7.
Proof. exact (@lem2306123 (NUMERAL 0)). Qed.
Lemma lem2306125 (y : int) : (term33 y) = (term33 y).
Proof. exact (eq_refl (term33 y)). Qed.
Lemma lem2306126 (y : int) : (term34 y) = (term35 y).
Proof. exact (MK_COMB (@lem2306125 y) (@lem2306124)). Qed.
Lemma lem2306128 (x : int) (y : int) : (term25 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2306129 (y : int) : (term35 y) = (term36 y).
Proof. exact (@lem2306128 y term15). Qed.
Lemma lem2306130 (y : int) : (term34 y) = (term36 y).
Proof. exact (TRANS (@lem2306126 y) (@lem2306129 y)). Qed.
Lemma lem2306131 (x : int) (y : int) : (term39 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem2306121 x) (@lem2306130 y)). Qed.
Lemma lem2306132 (x : int) (y : int) : (term41 x y) = (term42 x y).
Proof. exact (MK_COMB (@lem2306110 x y) (@lem2306131 x y)). Qed.
Lemma lem2306133 (x : int) (y : int) : (term43 x y) = (term44 x y).
Proof. exact (MK_COMB (@lem2306083 y) (@lem2306132 x y)). Qed.
Lemma lem2306134 (x : int) (y : int) : (term4 x y) = (term45 x y).
Proof. exact (MK_COMB (@lem2306072 x) (@lem2306133 x y)). Qed.
Lemma lem2306135 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term14 x y) = (term45 x y)).
Proof. exact (MK_COMB (@lem2306061 x y) (@lem2306134 x y)). Qed.
Lemma lem2306136 (x : int) (y : int) : (term14 x y) = (term45 x y).
Proof. exact (EQ_MP (@lem2306135 x y) (@lem2306047 x y)). Qed.
Lemma lem2306137 (x : int) : term46 x.
Proof. exact (fun y : int => @lem2306136 x y). Qed.
Lemma lem2306138 : term47.
Proof. exact (fun x : int => @lem2306137 x). Qed.
