Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2404230_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import INT_LT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm2403913_spec.
Require Import thm2403914_spec.
Require Import thm2403916_spec.
Lemma lem2403922 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (term0 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem2403923 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term0 m n).
Proof. exact (SYM (@lem2403922 n m h1)). Qed.
Lemma lem2403924 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (Peano.lt n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem2403925 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (term0 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem2403924 m n h1)). Qed.
Lemma lem2403926 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt n m) => @lem2403923 n m h1) (fun h1 : (Peano.lt n m) = (term0 m n) => @lem2403925 m n h1)). Qed.
Lemma lem2403927 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem2403926 m n)). Qed.
Lemma lem2403928 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2403929 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem2403928) (@lem2403927 m)). Qed.
Lemma lem2403930 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem2403929 m)). Qed.
Lemma lem2403931 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2403932 : term7 = term8.
Proof. exact (MK_COMB (@lem2403931) (@lem2403930)). Qed.
Lemma lem2403933 : term8.
Proof. exact (EQ_MP (@lem2403932) (@lem97961)). Qed.
Lemma lem2403934 (x : int) : term9 x.
Proof. exact (@lem2318371 x). Qed.
Lemma lem2403935 (x : int) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2403936 (x : int) : term10 x.
Proof. exact (EQ_MP (@lem2403935 x) (@lem2403934 x)). Qed.
Lemma lem2403937 (x : int) (y : int) : term11 x y.
Proof. exact (@lem2403936 x y). Qed.
Lemma lem2403938 (y : int) (x : int) : (term11 x y) = ((int_lt x y) = (term12 y x)).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem2403940 (m : nat) : term13 m.
Proof. exact (@lem2403933 m). Qed.
Lemma lem2403941 (m : nat) : (term13 m) = (term4 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem2403942 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem2403941 m) (@lem2403940 m)). Qed.
Lemma lem2403943 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem2403942 m n). Qed.
Lemma lem2403944 (m : nat) (n : nat) : (term14 m n) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem2403949 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem2403950 (m : nat) (n : nat) : ((term15 m n) = False) = (term16 m n).
Proof. exact (@lem2403949 (term15 m n)). Qed.
Lemma lem2403952 (y : int) (x : int) : (int_lt x y) = (term12 y x).
Proof. exact (EQ_MP (@lem2403938 y x) (@lem2403937 x y)). Qed.
Lemma lem2403953 (n : nat) (m : nat) : (term15 m n) = (term17 n m).
Proof. exact (@lem2403952 (term18 n) (int_of_num m)). Qed.
Lemma lem2403955 (m : nat) (n : nat) : (term19 m n) = True.
Proof. exact (proj1 (@lem2403913 m n)). Qed.
Lemma lem2403956 (n : nat) (m : nat) : (term19 n m) = True.
Proof. exact (@lem2403955 n m). Qed.
Lemma lem2403957 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2403958 (n : nat) (m : nat) : (term17 n m) = (~ True).
Proof. exact (MK_COMB (@lem2403957) (@lem2403956 n m)). Qed.
Lemma lem2403960 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem2403961 (n : nat) (m : nat) : (term17 n m) = False.
Proof. exact (TRANS (@lem2403958 n m) (@lem2403960)). Qed.
Lemma lem2403962 (m : nat) (n : nat) : (term15 m n) = False.
Proof. exact (TRANS (@lem2403953 n m) (@lem2403961 n m)). Qed.
Lemma lem2403963 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2403964 (m : nat) (n : nat) : (term16 m n) = (~ False).
Proof. exact (MK_COMB (@lem2403963) (@lem2403962 m n)). Qed.
Lemma lem2403966 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2403967 (m : nat) (n : nat) : (term16 m n) = True.
Proof. exact (TRANS (@lem2403964 m n) (@lem2403966)). Qed.
Lemma lem2403968 (m : nat) (n : nat) : ((term15 m n) = False) = True.
Proof. exact (TRANS (@lem2403950 m n) (@lem2403967 m n)). Qed.
Lemma lem2403969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2403970 (m : nat) (n : nat) : (term20 m n) = (and True).
Proof. exact (MK_COMB (@lem2403969) (@lem2403968 m n)). Qed.
Lemma lem2403976 (y : int) (x : int) : (int_lt x y) = (term12 y x).
Proof. exact (EQ_MP (@lem2403938 y x) (@lem2403937 x y)). Qed.
Lemma lem2403977 (n : nat) (m : nat) : (term21 m n) = (term22 n m).
Proof. exact (@lem2403976 (int_of_num n) (int_of_num m)). Qed.
Lemma lem2403979 (m : nat) (n : nat) : (term23 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem2403914 m n)). Qed.
Lemma lem2403980 (n : nat) (m : nat) : (term23 n m) = (Peano.le n m).
Proof. exact (@lem2403979 n m). Qed.
Lemma lem2403981 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2403982 (n : nat) (m : nat) : (term22 n m) = (term0 n m).
Proof. exact (MK_COMB (@lem2403981) (@lem2403980 n m)). Qed.
Lemma lem2403983 (n : nat) (m : nat) : (term21 m n) = (term0 n m).
Proof. exact (TRANS (@lem2403977 n m) (@lem2403982 n m)). Qed.
Lemma lem2403984 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2403985 (n : nat) (m : nat) : (term24 m n) = (term25 n m).
Proof. exact (MK_COMB (@lem2403984) (@lem2403983 n m)). Qed.
Lemma lem2403987 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem2403944 m n) (@lem2403943 m n)). Qed.
Lemma lem2403988 (n : nat) (m : nat) : (Peano.lt m n) = (term0 n m).
Proof. exact (@lem2403987 n m). Qed.
Lemma lem2403989 (n : nat) (m : nat) : ((term21 m n) = (Peano.lt m n)) = ((term0 n m) = (term0 n m)).
Proof. exact (MK_COMB (@lem2403985 n m) (@lem2403988 n m)). Qed.
Lemma lem2403991 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2403992 (x : Prop) : (x = x) = True.
Proof. exact (@lem2403991 Prop x). Qed.
Lemma lem2403993 (n : nat) (m : nat) : ((term0 n m) = (term0 n m)) = True.
Proof. exact (@lem2403992 (term0 n m)). Qed.
Lemma lem2403994 (m : nat) (n : nat) : ((term21 m n) = (Peano.lt m n)) = True.
Proof. exact (TRANS (@lem2403989 n m) (@lem2403993 n m)). Qed.
Lemma lem2403995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2403996 (m : nat) (n : nat) : (term26 m n) = (and True).
Proof. exact (MK_COMB (@lem2403995) (@lem2403994 m n)). Qed.
Lemma lem2404002 (y : int) (x : int) : (int_lt x y) = (term12 y x).
Proof. exact (EQ_MP (@lem2403938 y x) (@lem2403937 x y)). Qed.
Lemma lem2404003 (n : nat) (m : nat) : (term27 m n) = (term28 n m).
Proof. exact (@lem2404002 (term18 n) (term18 m)). Qed.
Lemma lem2404005 (n : nat) (m : nat) : (term29 m n) = (Peano.le n m).
Proof. exact (proj1 (@lem2403916 m n)). Qed.
Lemma lem2404006 (m : nat) (n : nat) : (term29 n m) = (Peano.le m n).
Proof. exact (@lem2404005 m n). Qed.
Lemma lem2404007 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2404008 (m : nat) (n : nat) : (term28 n m) = (term0 m n).
Proof. exact (MK_COMB (@lem2404007) (@lem2404006 m n)). Qed.
Lemma lem2404009 (m : nat) (n : nat) : (term27 m n) = (term0 m n).
Proof. exact (TRANS (@lem2404003 n m) (@lem2404008 m n)). Qed.
Lemma lem2404010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2404011 (m : nat) (n : nat) : (term30 m n) = (term25 m n).
Proof. exact (MK_COMB (@lem2404010) (@lem2404009 m n)). Qed.
Lemma lem2404013 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem2403944 m n) (@lem2403943 m n)). Qed.
Lemma lem2404014 (m : nat) (n : nat) : ((term27 m n) = (Peano.lt n m)) = ((term0 m n) = (term0 m n)).
Proof. exact (MK_COMB (@lem2404011 m n) (@lem2404013 m n)). Qed.
Lemma lem2404016 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2404017 (x : Prop) : (x = x) = True.
Proof. exact (@lem2404016 Prop x). Qed.
Lemma lem2404018 (m : nat) (n : nat) : ((term0 m n) = (term0 m n)) = True.
Proof. exact (@lem2404017 (term0 m n)). Qed.
Lemma lem2404019 (n : nat) (m : nat) : ((term27 m n) = (Peano.lt n m)) = True.
Proof. exact (TRANS (@lem2404014 m n) (@lem2404018 m n)). Qed.
Lemma lem2404020 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2404021 (n : nat) (m : nat) : (term31 n m) = (and True).
Proof. exact (MK_COMB (@lem2404020) (@lem2404019 n m)). Qed.
Lemma lem2404025 (y : int) (x : int) : (int_lt x y) = (term12 y x).
Proof. exact (EQ_MP (@lem2403938 y x) (@lem2403937 x y)). Qed.
Lemma lem2404026 (n : nat) (m : nat) : (term32 m n) = (term33 n m).
Proof. exact (@lem2404025 (int_of_num n) (term18 m)). Qed.
Lemma lem2404028 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (proj2 (@lem2403916 m n)). Qed.
Lemma lem2404029 (n : nat) (m : nat) : (term34 n m) = (term35 n m).
Proof. exact (@lem2404028 n m). Qed.
Lemma lem2404036 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2404037 (n : nat) (m : nat) : (term33 n m) = (term36 n m).
Proof. exact (MK_COMB (@lem2404036) (@lem2404029 n m)). Qed.
Lemma lem2404038 (n : nat) (m : nat) : (term32 m n) = (term36 n m).
Proof. exact (TRANS (@lem2404026 n m) (@lem2404037 n m)). Qed.
Lemma lem2404039 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2404040 (n : nat) (m : nat) : (term37 m n) = (term38 n m).
Proof. exact (MK_COMB (@lem2404039) (@lem2404038 n m)). Qed.
Lemma lem2404047 (m : nat) (n : nat) : (term36 m n) = (term36 m n).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem2404048 (m : nat) (n : nat) : ((term32 m n) = (term36 m n)) = ((term36 n m) = (term36 m n)).
Proof. exact (MK_COMB (@lem2404040 n m) (@lem2404047 m n)). Qed.
Lemma lem2404051 (m : nat) (n : nat) : (term39 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem2404021 n m) (@lem2404048 m n)). Qed.
Lemma lem2404053 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2404054 (m : nat) (n : nat) : (term40 m n) = ((term36 n m) = (term36 m n)).
Proof. exact (@lem2404053 ((term36 n m) = (term36 m n))). Qed.
Lemma lem2404069 (m : nat) (n : nat) : (term39 m n) = ((term36 n m) = (term36 m n)).
Proof. exact (TRANS (@lem2404051 m n) (@lem2404054 m n)). Qed.
Lemma lem2404070 (m : nat) (n : nat) : (term41 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem2403996 m n) (@lem2404069 m n)). Qed.
Lemma lem2404072 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2404073 (m : nat) (n : nat) : (term40 m n) = ((term36 n m) = (term36 m n)).
Proof. exact (@lem2404072 ((term36 n m) = (term36 m n))). Qed.
Lemma lem2404088 (m : nat) (n : nat) : (term41 m n) = ((term36 n m) = (term36 m n)).
Proof. exact (TRANS (@lem2404070 m n) (@lem2404073 m n)). Qed.
Lemma lem2404089 (m : nat) (n : nat) : (term42 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem2403970 m n) (@lem2404088 m n)). Qed.
Lemma lem2404091 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2404092 (m : nat) (n : nat) : (term40 m n) = ((term36 n m) = (term36 m n)).
Proof. exact (@lem2404091 ((term36 n m) = (term36 m n))). Qed.
Lemma lem2404107 (m : nat) (n : nat) : (term42 m n) = ((term36 n m) = (term36 m n)).
Proof. exact (TRANS (@lem2404089 m n) (@lem2404092 m n)). Qed.
Lemma lem2404108 (m : nat) (n : nat) : ((term36 n m) = (term36 m n)) = (term42 m n).
Proof. exact (SYM (@lem2404107 m n)). Qed.
Lemma lem2404125 (n : nat) : term43 n.
Proof. exact (@lem9851 (n = (NUMERAL 0))). Qed.
Lemma lem2404126 (n : nat) : (term43 n) = (term44 n).
Proof. exact (eq_refl (term43 n)). Qed.
Lemma lem2404127 (n : nat) : term44 n.
Proof. exact (EQ_MP (@lem2404126 n) (@lem2404125 n)). Qed.
Lemma lem2404128 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (n = (NUMERAL 0)) = True.
Proof. exact (h1). Qed.
Lemma lem2404129 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (n = (NUMERAL 0)) = False.
Proof. exact (h1). Qed.
Lemma lem2404146 (m : nat) : (term45 m) = (term45 m).
Proof. exact (eq_refl (term45 m)). Qed.
Lemma lem2404147 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term46 m n) = (term47 m).
Proof. exact (MK_COMB (@lem2404146 m) (@lem2404128 n h1)). Qed.
Lemma lem2404148 (m : nat) : (term47 m) = ((term48 m) = (term49 m)).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem2404149 (m : nat) (n : nat) : (term50 m n) = (term50 m n).
Proof. exact (eq_refl (term50 m n)). Qed.
Lemma lem2404150 (n : nat) (m : nat) : ((term46 m n) = (term47 m)) = ((term46 m n) = ((term48 m) = (term49 m))).
Proof. exact (MK_COMB (@lem2404149 m n) (@lem2404148 m)). Qed.
Lemma lem2404151 (m : nat) (n : nat) : (term46 m n) = ((term36 n m) = (term36 m n)).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem2404152 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2404153 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (MK_COMB (@lem2404152) (@lem2404151 m n)). Qed.
Lemma lem2404154 (m : nat) : ((term48 m) = (term49 m)) = ((term48 m) = (term49 m)).
Proof. exact (eq_refl ((term48 m) = (term49 m))). Qed.
Lemma lem2404155 (n : nat) (m : nat) : ((term46 m n) = ((term48 m) = (term49 m))) = (((term36 n m) = (term36 m n)) = ((term48 m) = (term49 m))).
Proof. exact (MK_COMB (@lem2404153 m n) (@lem2404154 m)). Qed.
Lemma lem2404156 (n : nat) (m : nat) : ((term46 m n) = (term47 m)) = (((term36 n m) = (term36 m n)) = ((term48 m) = (term49 m))).
Proof. exact (TRANS (@lem2404150 n m) (@lem2404155 n m)). Qed.
Lemma lem2404157 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : ((term36 n m) = (term36 m n)) = ((term48 m) = (term49 m)).
Proof. exact (EQ_MP (@lem2404156 n m) (@lem2404147 m n h1)). Qed.
Lemma lem2404158 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : ((term48 m) = (term49 m)) = ((term36 n m) = (term36 m n)).
Proof. exact (SYM (@lem2404157 m n h1)). Qed.
Lemma lem2404159 (m : nat) : (term45 m) = (term45 m).
Proof. exact (eq_refl (term45 m)). Qed.
Lemma lem2404160 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term46 m n) = (term52 m).
Proof. exact (MK_COMB (@lem2404159 m) (@lem2404129 n h1)). Qed.
Lemma lem2404161 (m : nat) : (term52 m) = ((term53 m) = (term54 m)).
Proof. exact (eq_refl (term52 m)). Qed.
Lemma lem2404162 (m : nat) (n : nat) : (term50 m n) = (term50 m n).
Proof. exact (eq_refl (term50 m n)). Qed.
Lemma lem2404163 (n : nat) (m : nat) : ((term46 m n) = (term52 m)) = ((term46 m n) = ((term53 m) = (term54 m))).
Proof. exact (MK_COMB (@lem2404162 m n) (@lem2404161 m)). Qed.
Lemma lem2404164 (m : nat) (n : nat) : (term46 m n) = ((term36 n m) = (term36 m n)).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem2404165 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2404166 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (MK_COMB (@lem2404165) (@lem2404164 m n)). Qed.
Lemma lem2404167 (m : nat) : ((term53 m) = (term54 m)) = ((term53 m) = (term54 m)).
Proof. exact (eq_refl ((term53 m) = (term54 m))). Qed.
Lemma lem2404168 (n : nat) (m : nat) : ((term46 m n) = ((term53 m) = (term54 m))) = (((term36 n m) = (term36 m n)) = ((term53 m) = (term54 m))).
Proof. exact (MK_COMB (@lem2404166 m n) (@lem2404167 m)). Qed.
Lemma lem2404169 (n : nat) (m : nat) : ((term46 m n) = (term52 m)) = (((term36 n m) = (term36 m n)) = ((term53 m) = (term54 m))).
Proof. exact (TRANS (@lem2404163 n m) (@lem2404168 n m)). Qed.
Lemma lem2404170 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : ((term36 n m) = (term36 m n)) = ((term53 m) = (term54 m)).
Proof. exact (EQ_MP (@lem2404169 n m) (@lem2404160 m n h1)). Qed.
Lemma lem2404171 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : ((term53 m) = (term54 m)) = ((term36 n m) = (term36 m n)).
Proof. exact (SYM (@lem2404170 m n h1)). Qed.
Lemma lem2404175 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2404176 (m : nat) : (term55 m) = (m = (NUMERAL 0)).
Proof. exact (@lem2404175 (m = (NUMERAL 0))). Qed.
Lemma lem2404179 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2404180 (m : nat) : (term48 m) = (term56 m).
Proof. exact (MK_COMB (@lem2404179) (@lem2404176 m)). Qed.
Lemma lem2404181 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2404182 (m : nat) : (term57 m) = (term58 m).
Proof. exact (MK_COMB (@lem2404181) (@lem2404180 m)). Qed.
Lemma lem2404184 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem2404185 (m : nat) : (term59 m) = (m = (NUMERAL 0)).
Proof. exact (@lem2404184 (m = (NUMERAL 0))). Qed.
Lemma lem2404188 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2404189 (m : nat) : (term49 m) = (term56 m).
Proof. exact (MK_COMB (@lem2404188) (@lem2404185 m)). Qed.
Lemma lem2404190 (m : nat) : ((term48 m) = (term49 m)) = ((term56 m) = (term56 m)).
Proof. exact (MK_COMB (@lem2404182 m) (@lem2404189 m)). Qed.
Lemma lem2404192 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2404193 (x : Prop) : (x = x) = True.
Proof. exact (@lem2404192 Prop x). Qed.
Lemma lem2404194 (m : nat) : ((term56 m) = (term56 m)) = True.
Proof. exact (@lem2404193 (term56 m)). Qed.
Lemma lem2404195 (m : nat) : ((term48 m) = (term49 m)) = True.
Proof. exact (TRANS (@lem2404190 m) (@lem2404194 m)). Qed.
Lemma lem2404196 (m : nat) : True = ((term48 m) = (term49 m)).
Proof. exact (SYM (@lem2404195 m)). Qed.
Lemma lem2404197 (m : nat) : (term48 m) = (term49 m).
Proof. exact (EQ_MP (@lem2404196 m) (@lem0)). Qed.
Lemma lem2404201 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem2404202 (m : nat) : (term60 m) = False.
Proof. exact (@lem2404201 (m = (NUMERAL 0))). Qed.
Lemma lem2404203 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2404204 (m : nat) : (term53 m) = (~ False).
Proof. exact (MK_COMB (@lem2404203) (@lem2404202 m)). Qed.
Lemma lem2404206 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2404207 (m : nat) : (term53 m) = True.
Proof. exact (TRANS (@lem2404204 m) (@lem2404206)). Qed.
Lemma lem2404208 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2404209 (m : nat) : (term61 m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem2404208) (@lem2404207 m)). Qed.
Lemma lem2404211 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem2404212 (m : nat) : (term62 m) = False.
Proof. exact (@lem2404211 (m = (NUMERAL 0))). Qed.
Lemma lem2404213 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2404214 (m : nat) : (term54 m) = (~ False).
Proof. exact (MK_COMB (@lem2404213) (@lem2404212 m)). Qed.
Lemma lem2404216 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2404217 (m : nat) : (term54 m) = True.
Proof. exact (TRANS (@lem2404214 m) (@lem2404216)). Qed.
Lemma lem2404218 (m : nat) : ((term53 m) = (term54 m)) = (True = True).
Proof. exact (MK_COMB (@lem2404209 m) (@lem2404217 m)). Qed.
Lemma lem2404220 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem2404221 : (True = True) = True.
Proof. exact (@lem2404220 True). Qed.
Lemma lem2404222 (m : nat) : ((term53 m) = (term54 m)) = True.
Proof. exact (TRANS (@lem2404218 m) (@lem2404221)). Qed.
Lemma lem2404223 (m : nat) : True = ((term53 m) = (term54 m)).
Proof. exact (SYM (@lem2404222 m)). Qed.
Lemma lem2404224 (m : nat) : (term53 m) = (term54 m).
Proof. exact (EQ_MP (@lem2404223 m) (@lem0)). Qed.
Lemma lem2404225 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term36 n m) = (term36 m n).
Proof. exact (EQ_MP (@lem2404171 m n h1) (@lem2404224 m)). Qed.
Lemma lem2404226 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term36 n m) = (term36 m n).
Proof. exact (EQ_MP (@lem2404158 m n h1) (@lem2404197 m)). Qed.
Lemma lem2404229 (m : nat) (n : nat) : (term36 n m) = (term36 m n).
Proof. exact (or_elim (@lem2404127 n) (fun h0 : (n = (NUMERAL 0)) = True => @lem2404226 m n h0) (fun h0 : (n = (NUMERAL 0)) = False => @lem2404225 m n h0)). Qed.
Lemma lem2404230 (m : nat) (n : nat) : term42 m n.
Proof. exact (EQ_MP (@lem2404108 m n) (@lem2404229 m n)). Qed.
