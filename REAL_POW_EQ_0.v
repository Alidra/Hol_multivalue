Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_EQ_0_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import REAL_ENTIRE_spec.
Require Import thm0_spec.
Require Import thm1013352_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1366971_spec.
Require Import thm1367254_spec.
Require Import thm1386578_spec.
Require Import thm1483450_spec.
Require Import thm1483519_spec.
Require Import thm1483529_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Lemma lem1629937 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1629938 (x : real) : term1 x.
Proof. exact (@lem1629937 (term2 x)). Qed.
Lemma lem1629939 (x : real) : (term3 x) = (((term4 x) = term5) = (term6 x)).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1629940 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1629941 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1629940) (@lem1629939 x)). Qed.
Lemma lem1629942 (x : real) (n : nat) : (term9 x n) = (((real_pow x n) = term5) = (term10 x n)).
Proof. exact (eq_refl (term9 x n)). Qed.
Lemma lem1629943 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1629944 (x : real) (n : nat) : (term11 x n) = (term12 x n).
Proof. exact (MK_COMB (@lem1629943) (@lem1629942 x n)). Qed.
Lemma lem1629945 (x : real) (n : nat) : (term13 x n) = (((term14 x n) = term5) = (term15 x n)).
Proof. exact (eq_refl (term13 x n)). Qed.
Lemma lem1629946 (x : real) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (MK_COMB (@lem1629944 x n) (@lem1629945 x n)). Qed.
Lemma lem1629947 (x : real) : (term18 x) = (term19 x).
Proof. exact (fun_ext (fun n : nat => @lem1629946 x n)). Qed.
Lemma lem1629948 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1629949 (x : real) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem1629948) (@lem1629947 x)). Qed.
Lemma lem1629950 (x : real) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem1629941 x) (@lem1629949 x)). Qed.
Lemma lem1629951 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1629952 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1629951) (@lem1629950 x)). Qed.
Lemma lem1629953 (x : real) (n : nat) : (term9 x n) = (((real_pow x n) = term5) = (term10 x n)).
Proof. exact (eq_refl (term9 x n)). Qed.
Lemma lem1629954 (x : real) : (term26 x) = (term2 x).
Proof. exact (fun_ext (fun n : nat => @lem1629953 x n)). Qed.
Lemma lem1629955 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1629956 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1629955) (@lem1629954 x)). Qed.
Lemma lem1629957 (x : real) : (term1 x) = (term29 x).
Proof. exact (MK_COMB (@lem1629952 x) (@lem1629956 x)). Qed.
Lemma lem1629958 (x : real) : term29 x.
Proof. exact (EQ_MP (@lem1629957 x) (@lem1629938 x)). Qed.
Lemma lem1629992 (x : real) : (term4 x) = term30.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1629993 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1629994 (x : real) : (term31 x) = term32.
Proof. exact (MK_COMB (@lem1629993) (@lem1629992 x)). Qed.
Lemma lem1629995 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1629996 (x : real) : ((term4 x) = term5) = (term30 = term5).
Proof. exact (MK_COMB (@lem1629994 x) (@lem1629995)). Qed.
Lemma lem1629999 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1630000 (x : real) : (term33 x) = term34.
Proof. exact (MK_COMB (@lem1629999) (@lem1629996 x)). Qed.
Lemma lem1630006 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1630007 (x : nat) : (x = x) = True.
Proof. exact (@lem1630006 nat x). Qed.
Lemma lem1630008 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1630007 (NUMERAL 0)). Qed.
Lemma lem1630009 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1630010 : term35 = (~ True).
Proof. exact (MK_COMB (@lem1630009) (@lem1630008)). Qed.
Lemma lem1630012 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1630013 : term35 = False.
Proof. exact (TRANS (@lem1630010) (@lem1630012)). Qed.
Lemma lem1630014 (x : real) : (term36 x) = (term36 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1630015 (x : real) : (term6 x) = (term37 x).
Proof. exact (MK_COMB (@lem1630014 x) (@lem1630013)). Qed.
Lemma lem1630017 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1630018 (x : real) : (term37 x) = False.
Proof. exact (@lem1630017 (x = term5)). Qed.
Lemma lem1630019 (x : real) : (term6 x) = False.
Proof. exact (TRANS (@lem1630015 x) (@lem1630018 x)). Qed.
Lemma lem1630020 (x : real) : (((term4 x) = term5) = (term6 x)) = ((term30 = term5) = False).
Proof. exact (MK_COMB (@lem1630000 x) (@lem1630019 x)). Qed.
Lemma lem1630022 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem1630023 : ((term30 = term5) = False) = term38.
Proof. exact (@lem1630022 (term30 = term5)). Qed.
Lemma lem1630026 (x : real) : (((term4 x) = term5) = (term6 x)) = term38.
Proof. exact (TRANS (@lem1630020 x) (@lem1630023)). Qed.
Lemma lem1630027 (x : real) : term38 = (((term4 x) = term5) = (term6 x)).
Proof. exact (SYM (@lem1630026 x)). Qed.
Lemma lem1630028 (x : real) : term39 x.
Proof. exact (@lem1382769 x). Qed.
Lemma lem1630029 (x : real) : (term39 x) = (term40 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1630030 (x : real) : term40 x.
Proof. exact (EQ_MP (@lem1630029 x) (@lem1630028 x)). Qed.
Lemma lem1630031 (x : real) (y : real) : term41 x y.
Proof. exact (@lem1630030 x y). Qed.
Lemma lem1630032 (x : real) (y : real) : (term41 x y) = (((real_mul x y) = term5) = (term42 x y)).
Proof. exact (eq_refl (term41 x y)). Qed.
Lemma lem1630034 (x : real) : term43 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1630035 (x : real) (n : nat) : term44 x n.
Proof. exact (@lem1630034 x n). Qed.
Lemma lem1630036 (x : real) (n : nat) : (term44 x n) = ((term14 x n) = (term45 x n)).
Proof. exact (eq_refl (term44 x n)). Qed.
Lemma lem1630039 (n : nat) : term46 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1630040 (n : nat) : (term46 n) = (term47 n).
Proof. exact (eq_refl (term46 n)). Qed.
Lemma lem1630041 (n : nat) : term47 n.
Proof. exact (EQ_MP (@lem1630040 n) (@lem1630039 n)). Qed.
Lemma lem1630042 (n : nat) : term48 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem1630060 (x : real) (n : nat) : (term14 x n) = (term45 x n).
Proof. exact (EQ_MP (@lem1630036 x n) (@lem1630035 x n)). Qed.
Lemma lem1630061 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1630062 (x : real) (n : nat) : (term49 x n) = (term50 x n).
Proof. exact (MK_COMB (@lem1630061) (@lem1630060 x n)). Qed.
Lemma lem1630063 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1630064 (x : real) (n : nat) : ((term14 x n) = term5) = ((term45 x n) = term5).
Proof. exact (MK_COMB (@lem1630062 x n) (@lem1630063)). Qed.
Lemma lem1630066 (x : real) (y : real) : ((real_mul x y) = term5) = (term42 x y).
Proof. exact (EQ_MP (@lem1630032 x y) (@lem1630031 x y)). Qed.
Lemma lem1630067 (x : real) (n : nat) : ((term45 x n) = term5) = (term51 x n).
Proof. exact (@lem1630066 x (real_pow x n)). Qed.
Lemma lem1630073 (x : real) (n : nat) (h1 : ((real_pow x n) = term5) = (term10 x n)) : ((real_pow x n) = term5) = (term10 x n).
Proof. exact (h1). Qed.
Lemma lem1630080 (x : real) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1630081 (x : real) (n : nat) (h1 : ((real_pow x n) = term5) = (term10 x n)) : (term51 x n) = (term53 x n).
Proof. exact (MK_COMB (@lem1630080 x) (@lem1630073 x n h1)). Qed.
Lemma lem1630084 (x : real) (n : nat) (h1 : ((real_pow x n) = term5) = (term10 x n)) : ((term45 x n) = term5) = (term53 x n).
Proof. exact (TRANS (@lem1630067 x n) (@lem1630081 x n h1)). Qed.
Lemma lem1630085 (x : real) (n : nat) (h1 : ((real_pow x n) = term5) = (term10 x n)) : ((term14 x n) = term5) = (term53 x n).
Proof. exact (TRANS (@lem1630064 x n) (@lem1630084 x n h1)). Qed.
Lemma lem1630086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1630087 (x : real) (n : nat) (h1 : ((real_pow x n) = term5) = (term10 x n)) : (term54 x n) = (term55 x n).
Proof. exact (MK_COMB (@lem1630086) (@lem1630085 x n h1)). Qed.
Lemma lem1630093 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1630042 n (@lem1630041 n)). Qed.
Lemma lem1630094 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1630095 (n : nat) : (term47 n) = (~ False).
Proof. exact (MK_COMB (@lem1630094) (@lem1630093 n)). Qed.
Lemma lem1630097 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1630098 (n : nat) : (term47 n) = True.
Proof. exact (TRANS (@lem1630095 n) (@lem1630097)). Qed.
Lemma lem1630099 (x : real) : (term36 x) = (term36 x).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1630100 (n : nat) (x : real) : (term15 x n) = (term56 x).
Proof. exact (MK_COMB (@lem1630099 x) (@lem1630098 n)). Qed.
Lemma lem1630102 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1630103 (x : real) : (term56 x) = (x = term5).
Proof. exact (@lem1630102 (x = term5)). Qed.
Lemma lem1630106 (n : nat) (x : real) : (term15 x n) = (x = term5).
Proof. exact (TRANS (@lem1630100 n x) (@lem1630103 x)). Qed.
Lemma lem1630107 (x : real) (n : nat) (h1 : ((real_pow x n) = term5) = (term10 x n)) : (((term14 x n) = term5) = (term15 x n)) = ((term53 x n) = (x = term5)).
Proof. exact (MK_COMB (@lem1630087 x n h1) (@lem1630106 n x)). Qed.
Lemma lem1630110 (x : real) (n : nat) (h1 : ((real_pow x n) = term5) = (term10 x n)) : ((term53 x n) = (x = term5)) = (((term14 x n) = term5) = (term15 x n)).
Proof. exact (SYM (@lem1630107 x n h1)). Qed.
Lemma lem1630113 (t : Prop) : (term57 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1630119 : term58 = (term30 = term5).
Proof. exact (@lem1630113 (term30 = term5)). Qed.
Lemma lem1630120 : (term30 = term5) = (term59 = term5).
Proof. exact (@lem1483529 term30 term5). Qed.
Lemma lem1630126 : term59 = term60.
Proof. exact (@lem1483519 term30 term5). Qed.
Lemma lem1630128 (x : nat) : (term61 x) = term5.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1630129 : term62 = term5.
Proof. exact (@lem1630128 term63). Qed.
Lemma lem1630130 : term64 = term64.
Proof. exact (eq_refl term64). Qed.
Lemma lem1630131 : term60 = term65.
Proof. exact (MK_COMB (@lem1630130) (@lem1630129)). Qed.
Lemma lem1630132 : term65 = term30.
Proof. exact (@lem1483450 term30). Qed.
Lemma lem1630133 : term60 = term30.
Proof. exact (TRANS (@lem1630131) (@lem1630132)). Qed.
Lemma lem1630135 : term59 = term30.
Proof. exact (TRANS (@lem1630126) (@lem1630133)). Qed.
Lemma lem1630136 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1630137 : term66 = term32.
Proof. exact (MK_COMB (@lem1630136) (@lem1630135)). Qed.
Lemma lem1630138 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem1630139 : (term59 = term5) = (term30 = term5).
Proof. exact (MK_COMB (@lem1630137) (@lem1630138)). Qed.
Lemma lem1630140 : (term30 = term5) = (term30 = term5).
Proof. exact (TRANS (@lem1630120) (@lem1630139)). Qed.
Lemma lem1630149 : term58 = (term30 = term5).
Proof. exact (TRANS (@lem1630119) (@lem1630140)). Qed.
Lemma lem1630153 (h1 : term30 = term5) : term30 = term5.
Proof. exact (h1). Qed.
Lemma lem1630155 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (proj1 (@lem1366971 m n)). Qed.
Lemma lem1630156 : (term30 = term5) = (term63 = (NUMERAL 0)).
Proof. exact (@lem1630155 term63 (NUMERAL 0)). Qed.
Lemma lem1630157 : term67 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1630158 (h1 : term67 = (BIT1 0)) : (term63 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1630159 : (term67 = (BIT1 0)) = ((term63 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term67 = (BIT1 0) => @lem1630158 h1) (fun h1 : (term63 = (NUMERAL 0)) = False => @lem1630157)). Qed.
Lemma lem1630160 : (term63 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1630159) (@lem1630157)). Qed.
Lemma lem1630161 : (term30 = term5) = False.
Proof. exact (TRANS (@lem1630156) (@lem1630160)). Qed.
Lemma lem1630162 (h1 : term30 = term5) : False.
Proof. exact (EQ_MP (@lem1630161) (@lem1630153 h1)). Qed.
Lemma lem1630164 (h1 : term30 = term5) : term30 = term5.
Proof. exact (h1). Qed.
Lemma lem1630165 (h1 : term30 = term5) : (term30 = term5) = False.
Proof. exact (prop_ext (fun h2 : term30 = term5 => @lem1630162 h1) (fun h2 : False => @lem1630164 h1)). Qed.
Lemma lem1630166 (h1 : term30 = term5) : False.
Proof. exact (EQ_MP (@lem1630165 h1) (@lem1630164 h1)). Qed.
Lemma lem1630167 (h1 : term58) : term58.
Proof. exact (h1). Qed.
Lemma lem1630168 (h1 : term58) : term30 = term5.
Proof. exact (EQ_MP (@lem1630149) (@lem1630167 h1)). Qed.
Lemma lem1630169 (h1 : term58) : (term30 = term5) = False.
Proof. exact (prop_ext (fun h2 : term30 = term5 => @lem1630166 h2) (fun h2 : False => @lem1630168 h1)). Qed.
Lemma lem1630170 (h1 : term58) : False.
Proof. exact (EQ_MP (@lem1630169 h1) (@lem1630168 h1)). Qed.
Lemma lem1630171 : term68.
Proof. exact (fun h0 : term58 => @lem1630170 h0). Qed.
Lemma lem1630172 : term69.
Proof. exact (@lem1386578 term38). Qed.
Lemma lem1630173 : term38.
Proof. exact (@lem1630172 (@lem1630171)). Qed.
Lemma lem1630190 (x : real) : term70 x.
Proof. exact (@lem9851 (x = term5)). Qed.
Lemma lem1630191 (x : real) : (term70 x) = (term71 x).
Proof. exact (eq_refl (term70 x)). Qed.
Lemma lem1630192 (x : real) : term71 x.
Proof. exact (EQ_MP (@lem1630191 x) (@lem1630190 x)). Qed.
Lemma lem1630193 (x : real) (h1 : (x = term5) = True) : (x = term5) = True.
Proof. exact (h1). Qed.
Lemma lem1630194 (x : real) (h1 : (x = term5) = False) : (x = term5) = False.
Proof. exact (h1). Qed.
Lemma lem1630211 (n : nat) : (term72 n) = (term72 n).
Proof. exact (eq_refl (term72 n)). Qed.
Lemma lem1630212 (n : nat) (x : real) (h1 : (x = term5) = True) : (term73 n x) = (term74 n).
Proof. exact (MK_COMB (@lem1630211 n) (@lem1630193 x h1)). Qed.
Lemma lem1630213 (n : nat) : (term74 n) = ((term75 n) = True).
Proof. exact (eq_refl (term74 n)). Qed.
Lemma lem1630214 (n : nat) (x : real) : (term76 n x) = (term76 n x).
Proof. exact (eq_refl (term76 n x)). Qed.
Lemma lem1630215 (x : real) (n : nat) : ((term73 n x) = (term74 n)) = ((term73 n x) = ((term75 n) = True)).
Proof. exact (MK_COMB (@lem1630214 n x) (@lem1630213 n)). Qed.
Lemma lem1630216 (n : nat) (x : real) : (term73 n x) = ((term53 x n) = (x = term5)).
Proof. exact (eq_refl (term73 n x)). Qed.
Lemma lem1630217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1630218 (n : nat) (x : real) : (term76 n x) = (term77 n x).
Proof. exact (MK_COMB (@lem1630217) (@lem1630216 n x)). Qed.
Lemma lem1630219 (n : nat) : ((term75 n) = True) = ((term75 n) = True).
Proof. exact (eq_refl ((term75 n) = True)). Qed.
Lemma lem1630220 (x : real) (n : nat) : ((term73 n x) = ((term75 n) = True)) = (((term53 x n) = (x = term5)) = ((term75 n) = True)).
Proof. exact (MK_COMB (@lem1630218 n x) (@lem1630219 n)). Qed.
Lemma lem1630221 (x : real) (n : nat) : ((term73 n x) = (term74 n)) = (((term53 x n) = (x = term5)) = ((term75 n) = True)).
Proof. exact (TRANS (@lem1630215 x n) (@lem1630220 x n)). Qed.
Lemma lem1630222 (n : nat) (x : real) (h1 : (x = term5) = True) : ((term53 x n) = (x = term5)) = ((term75 n) = True).
Proof. exact (EQ_MP (@lem1630221 x n) (@lem1630212 n x h1)). Qed.
Lemma lem1630223 (n : nat) (x : real) (h1 : (x = term5) = True) : ((term75 n) = True) = ((term53 x n) = (x = term5)).
Proof. exact (SYM (@lem1630222 n x h1)). Qed.
Lemma lem1630224 (n : nat) : (term72 n) = (term72 n).
Proof. exact (eq_refl (term72 n)). Qed.
Lemma lem1630225 (n : nat) (x : real) (h1 : (x = term5) = False) : (term73 n x) = (term78 n).
Proof. exact (MK_COMB (@lem1630224 n) (@lem1630194 x h1)). Qed.
Lemma lem1630226 (n : nat) : (term78 n) = ((term79 n) = False).
Proof. exact (eq_refl (term78 n)). Qed.
Lemma lem1630227 (n : nat) (x : real) : (term76 n x) = (term76 n x).
Proof. exact (eq_refl (term76 n x)). Qed.
Lemma lem1630228 (x : real) (n : nat) : ((term73 n x) = (term78 n)) = ((term73 n x) = ((term79 n) = False)).
Proof. exact (MK_COMB (@lem1630227 n x) (@lem1630226 n)). Qed.
Lemma lem1630229 (n : nat) (x : real) : (term73 n x) = ((term53 x n) = (x = term5)).
Proof. exact (eq_refl (term73 n x)). Qed.
Lemma lem1630230 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1630231 (n : nat) (x : real) : (term76 n x) = (term77 n x).
Proof. exact (MK_COMB (@lem1630230) (@lem1630229 n x)). Qed.
Lemma lem1630232 (n : nat) : ((term79 n) = False) = ((term79 n) = False).
Proof. exact (eq_refl ((term79 n) = False)). Qed.
Lemma lem1630233 (x : real) (n : nat) : ((term73 n x) = ((term79 n) = False)) = (((term53 x n) = (x = term5)) = ((term79 n) = False)).
Proof. exact (MK_COMB (@lem1630231 n x) (@lem1630232 n)). Qed.
Lemma lem1630234 (x : real) (n : nat) : ((term73 n x) = (term78 n)) = (((term53 x n) = (x = term5)) = ((term79 n) = False)).
Proof. exact (TRANS (@lem1630228 x n) (@lem1630233 x n)). Qed.
Lemma lem1630235 (n : nat) (x : real) (h1 : (x = term5) = False) : ((term53 x n) = (x = term5)) = ((term79 n) = False).
Proof. exact (EQ_MP (@lem1630234 x n) (@lem1630225 n x h1)). Qed.
Lemma lem1630236 (n : nat) (x : real) (h1 : (x = term5) = False) : ((term79 n) = False) = ((term53 x n) = (x = term5)).
Proof. exact (SYM (@lem1630235 n x h1)). Qed.
Lemma lem1630238 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem1630239 (n : nat) : ((term75 n) = True) = (term75 n).
Proof. exact (@lem1630238 (term75 n)). Qed.
Lemma lem1630241 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1630242 (n : nat) : (term75 n) = True.
Proof. exact (@lem1630241 (term80 n)). Qed.
Lemma lem1630243 (n : nat) : ((term75 n) = True) = True.
Proof. exact (TRANS (@lem1630239 n) (@lem1630242 n)). Qed.
Lemma lem1630244 (n : nat) : True = ((term75 n) = True).
Proof. exact (SYM (@lem1630243 n)). Qed.
Lemma lem1630245 (n : nat) : (term75 n) = True.
Proof. exact (EQ_MP (@lem1630244 n) (@lem0)). Qed.
Lemma lem1630247 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem1630248 (n : nat) : ((term79 n) = False) = (term81 n).
Proof. exact (@lem1630247 (term79 n)). Qed.
Lemma lem1630250 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1630251 (n : nat) : (term79 n) = (term82 n).
Proof. exact (@lem1630250 (term82 n)). Qed.
Lemma lem1630253 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1630254 (n : nat) : (term82 n) = False.
Proof. exact (@lem1630253 (term83 n)). Qed.
Lemma lem1630255 (n : nat) : (term79 n) = False.
Proof. exact (TRANS (@lem1630251 n) (@lem1630254 n)). Qed.
Lemma lem1630256 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1630257 (n : nat) : (term81 n) = (~ False).
Proof. exact (MK_COMB (@lem1630256) (@lem1630255 n)). Qed.
Lemma lem1630259 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1630260 (n : nat) : (term81 n) = True.
Proof. exact (TRANS (@lem1630257 n) (@lem1630259)). Qed.
Lemma lem1630261 (n : nat) : ((term79 n) = False) = True.
Proof. exact (TRANS (@lem1630248 n) (@lem1630260 n)). Qed.
Lemma lem1630262 (n : nat) : True = ((term79 n) = False).
Proof. exact (SYM (@lem1630261 n)). Qed.
Lemma lem1630263 (n : nat) : (term79 n) = False.
Proof. exact (EQ_MP (@lem1630262 n) (@lem0)). Qed.
Lemma lem1630264 (n : nat) (x : real) (h1 : (x = term5) = False) : (term53 x n) = (x = term5).
Proof. exact (EQ_MP (@lem1630236 n x h1) (@lem1630263 n)). Qed.
Lemma lem1630265 (n : nat) (x : real) (h1 : (x = term5) = True) : (term53 x n) = (x = term5).
Proof. exact (EQ_MP (@lem1630223 n x h1) (@lem1630245 n)). Qed.
Lemma lem1630268 (n : nat) (x : real) : (term53 x n) = (x = term5).
Proof. exact (or_elim (@lem1630192 x) (fun h0 : (x = term5) = True => @lem1630265 n x h0) (fun h0 : (x = term5) = False => @lem1630264 n x h0)). Qed.
Lemma lem1630269 (x : real) (n : nat) (h1 : ((real_pow x n) = term5) = (term10 x n)) : ((term14 x n) = term5) = (term15 x n).
Proof. exact (EQ_MP (@lem1630110 x n h1) (@lem1630268 n x)). Qed.
Lemma lem1630270 (x : real) : ((term4 x) = term5) = (term6 x).
Proof. exact (EQ_MP (@lem1630027 x) (@lem1630173)). Qed.
Lemma lem1630271 (x : real) (n : nat) : term17 x n.
Proof. exact (fun h0 : ((real_pow x n) = term5) = (term10 x n) => @lem1630269 x n h0). Qed.
Lemma lem1630276 (x : real) : term21 x.
Proof. exact (fun n : nat => @lem1630271 x n). Qed.
Lemma lem1630277 (x : real) : term23 x.
Proof. exact (conj (@lem1630270 x) (@lem1630276 x)). Qed.
Lemma lem1630278 (x : real) : term28 x.
Proof. exact (@lem1629958 x (@lem1630277 x)). Qed.
Lemma lem1630283 : term84.
Proof. exact (fun x : real => @lem1630278 x). Qed.
