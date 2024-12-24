Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1366270_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import real_gt_spec.
Require Import thm0_spec.
Require Import thm1365720_spec.
Require Import thm1365721_spec.
Require Import thm1365723_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1365994 (y : real) : term0 y.
Proof. exact (@lem1342768 y). Qed.
Lemma lem1365995 (y : real) : (term0 y) = (term1 y).
Proof. exact (eq_refl (term0 y)). Qed.
Lemma lem1365996 (y : real) : term1 y.
Proof. exact (EQ_MP (@lem1365995 y) (@lem1365994 y)). Qed.
Lemma lem1365997 (y : real) (x : real) : term2 y x.
Proof. exact (@lem1365996 y x). Qed.
Lemma lem1365998 (y : real) (x : real) : (term2 y x) = ((real_gt x y) = (real_lt y x)).
Proof. exact (eq_refl (term2 y x)). Qed.
Lemma lem1366003 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem1366004 (m : nat) (n : nat) : ((term3 m n) = False) = (term4 m n).
Proof. exact (@lem1366003 (term3 m n)). Qed.
Lemma lem1366006 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1365998 y x) (@lem1365997 y x)). Qed.
Lemma lem1366007 (n : nat) (m : nat) : (term3 m n) = (term5 n m).
Proof. exact (@lem1366006 (real_of_num n) (term6 m)). Qed.
Lemma lem1366009 (m : nat) (n : nat) : (term5 m n) = False.
Proof. exact (proj1 (@lem1365720 m n)). Qed.
Lemma lem1366010 (n : nat) (m : nat) : (term5 n m) = False.
Proof. exact (@lem1366009 n m). Qed.
Lemma lem1366011 (m : nat) (n : nat) : (term3 m n) = False.
Proof. exact (TRANS (@lem1366007 n m) (@lem1366010 n m)). Qed.
Lemma lem1366012 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1366013 (m : nat) (n : nat) : (term4 m n) = (~ False).
Proof. exact (MK_COMB (@lem1366012) (@lem1366011 m n)). Qed.
Lemma lem1366015 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1366016 (m : nat) (n : nat) : (term4 m n) = True.
Proof. exact (TRANS (@lem1366013 m n) (@lem1366015)). Qed.
Lemma lem1366017 (m : nat) (n : nat) : ((term3 m n) = False) = True.
Proof. exact (TRANS (@lem1366004 m n) (@lem1366016 m n)). Qed.
Lemma lem1366018 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366019 (m : nat) (n : nat) : (term7 m n) = (and True).
Proof. exact (MK_COMB (@lem1366018) (@lem1366017 m n)). Qed.
Lemma lem1366025 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1365998 y x) (@lem1365997 y x)). Qed.
Lemma lem1366026 (n : nat) (m : nat) : (term8 m n) = (term9 n m).
Proof. exact (@lem1366025 (real_of_num n) (real_of_num m)). Qed.
Lemma lem1366028 (m : nat) (n : nat) : (term9 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem1366029 (n : nat) (m : nat) : (term9 n m) = (Peano.lt n m).
Proof. exact (@lem1366028 n m). Qed.
Lemma lem1366030 (n : nat) (m : nat) : (term8 m n) = (Peano.lt n m).
Proof. exact (TRANS (@lem1366026 n m) (@lem1366029 n m)). Qed.
Lemma lem1366031 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366032 (n : nat) (m : nat) : (term10 m n) = (term11 n m).
Proof. exact (MK_COMB (@lem1366031) (@lem1366030 n m)). Qed.
Lemma lem1366033 (n : nat) (m : nat) : (Peano.lt n m) = (Peano.lt n m).
Proof. exact (eq_refl (Peano.lt n m)). Qed.
Lemma lem1366034 (n : nat) (m : nat) : ((term8 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (Peano.lt n m)).
Proof. exact (MK_COMB (@lem1366032 n m) (@lem1366033 n m)). Qed.
Lemma lem1366036 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1366037 (x : Prop) : (x = x) = True.
Proof. exact (@lem1366036 Prop x). Qed.
Lemma lem1366038 (n : nat) (m : nat) : ((Peano.lt n m) = (Peano.lt n m)) = True.
Proof. exact (@lem1366037 (Peano.lt n m)). Qed.
Lemma lem1366039 (n : nat) (m : nat) : ((term8 m n) = (Peano.lt n m)) = True.
Proof. exact (TRANS (@lem1366034 n m) (@lem1366038 n m)). Qed.
Lemma lem1366040 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366041 (n : nat) (m : nat) : (term12 n m) = (and True).
Proof. exact (MK_COMB (@lem1366040) (@lem1366039 n m)). Qed.
Lemma lem1366047 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1365998 y x) (@lem1365997 y x)). Qed.
Lemma lem1366048 (n : nat) (m : nat) : (term13 m n) = (term14 n m).
Proof. exact (@lem1366047 (term6 n) (term6 m)). Qed.
Lemma lem1366050 (n : nat) (m : nat) : (term14 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1365723 m n)). Qed.
Lemma lem1366051 (m : nat) (n : nat) : (term14 n m) = (Peano.lt m n).
Proof. exact (@lem1366050 m n). Qed.
Lemma lem1366052 (m : nat) (n : nat) : (term13 m n) = (Peano.lt m n).
Proof. exact (TRANS (@lem1366048 n m) (@lem1366051 m n)). Qed.
Lemma lem1366053 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366054 (m : nat) (n : nat) : (term15 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem1366053) (@lem1366052 m n)). Qed.
Lemma lem1366055 (m : nat) (n : nat) : (Peano.lt m n) = (Peano.lt m n).
Proof. exact (eq_refl (Peano.lt m n)). Qed.
Lemma lem1366056 (m : nat) (n : nat) : ((term13 m n) = (Peano.lt m n)) = ((Peano.lt m n) = (Peano.lt m n)).
Proof. exact (MK_COMB (@lem1366054 m n) (@lem1366055 m n)). Qed.
Lemma lem1366058 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1366059 (x : Prop) : (x = x) = True.
Proof. exact (@lem1366058 Prop x). Qed.
Lemma lem1366060 (m : nat) (n : nat) : ((Peano.lt m n) = (Peano.lt m n)) = True.
Proof. exact (@lem1366059 (Peano.lt m n)). Qed.
Lemma lem1366061 (m : nat) (n : nat) : ((term13 m n) = (Peano.lt m n)) = True.
Proof. exact (TRANS (@lem1366056 m n) (@lem1366060 m n)). Qed.
Lemma lem1366062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1366063 (m : nat) (n : nat) : (term16 m n) = (and True).
Proof. exact (MK_COMB (@lem1366062) (@lem1366061 m n)). Qed.
Lemma lem1366067 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1365998 y x) (@lem1365997 y x)). Qed.
Lemma lem1366068 (n : nat) (m : nat) : (term17 m n) = (term18 n m).
Proof. exact (@lem1366067 (term6 n) (real_of_num m)). Qed.
Lemma lem1366070 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (proj2 (@lem1365723 m n)). Qed.
Lemma lem1366071 (n : nat) (m : nat) : (term18 n m) = (term19 n m).
Proof. exact (@lem1366070 n m). Qed.
Lemma lem1366072 (n : nat) (m : nat) : (term17 m n) = (term19 n m).
Proof. exact (TRANS (@lem1366068 n m) (@lem1366071 n m)). Qed.
Lemma lem1366079 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366080 (n : nat) (m : nat) : (term20 m n) = (term21 n m).
Proof. exact (MK_COMB (@lem1366079) (@lem1366072 n m)). Qed.
Lemma lem1366087 (m : nat) (n : nat) : (term19 m n) = (term19 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1366088 (m : nat) (n : nat) : ((term17 m n) = (term19 m n)) = ((term19 n m) = (term19 m n)).
Proof. exact (MK_COMB (@lem1366080 n m) (@lem1366087 m n)). Qed.
Lemma lem1366091 (m : nat) (n : nat) : (term22 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem1366063 m n) (@lem1366088 m n)). Qed.
Lemma lem1366093 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1366094 (m : nat) (n : nat) : (term23 m n) = ((term19 n m) = (term19 m n)).
Proof. exact (@lem1366093 ((term19 n m) = (term19 m n))). Qed.
Lemma lem1366109 (m : nat) (n : nat) : (term22 m n) = ((term19 n m) = (term19 m n)).
Proof. exact (TRANS (@lem1366091 m n) (@lem1366094 m n)). Qed.
Lemma lem1366110 (m : nat) (n : nat) : (term24 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem1366041 n m) (@lem1366109 m n)). Qed.
Lemma lem1366112 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1366113 (m : nat) (n : nat) : (term23 m n) = ((term19 n m) = (term19 m n)).
Proof. exact (@lem1366112 ((term19 n m) = (term19 m n))). Qed.
Lemma lem1366128 (m : nat) (n : nat) : (term24 m n) = ((term19 n m) = (term19 m n)).
Proof. exact (TRANS (@lem1366110 m n) (@lem1366113 m n)). Qed.
Lemma lem1366129 (m : nat) (n : nat) : (term25 m n) = (term23 m n).
Proof. exact (MK_COMB (@lem1366019 m n) (@lem1366128 m n)). Qed.
Lemma lem1366131 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1366132 (m : nat) (n : nat) : (term23 m n) = ((term19 n m) = (term19 m n)).
Proof. exact (@lem1366131 ((term19 n m) = (term19 m n))). Qed.
Lemma lem1366147 (m : nat) (n : nat) : (term25 m n) = ((term19 n m) = (term19 m n)).
Proof. exact (TRANS (@lem1366129 m n) (@lem1366132 m n)). Qed.
Lemma lem1366148 (m : nat) (n : nat) : ((term19 n m) = (term19 m n)) = (term25 m n).
Proof. exact (SYM (@lem1366147 m n)). Qed.
Lemma lem1366165 (n : nat) : term26 n.
Proof. exact (@lem9851 (n = (NUMERAL 0))). Qed.
Lemma lem1366166 (n : nat) : (term26 n) = (term27 n).
Proof. exact (eq_refl (term26 n)). Qed.
Lemma lem1366167 (n : nat) : term27 n.
Proof. exact (EQ_MP (@lem1366166 n) (@lem1366165 n)). Qed.
Lemma lem1366168 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (n = (NUMERAL 0)) = True.
Proof. exact (h1). Qed.
Lemma lem1366169 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (n = (NUMERAL 0)) = False.
Proof. exact (h1). Qed.
Lemma lem1366186 (m : nat) : (term28 m) = (term28 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1366187 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term29 m n) = (term30 m).
Proof. exact (MK_COMB (@lem1366186 m) (@lem1366168 n h1)). Qed.
Lemma lem1366188 (m : nat) : (term30 m) = ((term31 m) = (term32 m)).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem1366189 (m : nat) (n : nat) : (term33 m n) = (term33 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1366190 (n : nat) (m : nat) : ((term29 m n) = (term30 m)) = ((term29 m n) = ((term31 m) = (term32 m))).
Proof. exact (MK_COMB (@lem1366189 m n) (@lem1366188 m)). Qed.
Lemma lem1366191 (m : nat) (n : nat) : (term29 m n) = ((term19 n m) = (term19 m n)).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem1366192 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366193 (m : nat) (n : nat) : (term33 m n) = (term34 m n).
Proof. exact (MK_COMB (@lem1366192) (@lem1366191 m n)). Qed.
Lemma lem1366194 (m : nat) : ((term31 m) = (term32 m)) = ((term31 m) = (term32 m)).
Proof. exact (eq_refl ((term31 m) = (term32 m))). Qed.
Lemma lem1366195 (n : nat) (m : nat) : ((term29 m n) = ((term31 m) = (term32 m))) = (((term19 n m) = (term19 m n)) = ((term31 m) = (term32 m))).
Proof. exact (MK_COMB (@lem1366193 m n) (@lem1366194 m)). Qed.
Lemma lem1366196 (n : nat) (m : nat) : ((term29 m n) = (term30 m)) = (((term19 n m) = (term19 m n)) = ((term31 m) = (term32 m))).
Proof. exact (TRANS (@lem1366190 n m) (@lem1366195 n m)). Qed.
Lemma lem1366197 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : ((term19 n m) = (term19 m n)) = ((term31 m) = (term32 m)).
Proof. exact (EQ_MP (@lem1366196 n m) (@lem1366187 m n h1)). Qed.
Lemma lem1366198 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : ((term31 m) = (term32 m)) = ((term19 n m) = (term19 m n)).
Proof. exact (SYM (@lem1366197 m n h1)). Qed.
Lemma lem1366199 (m : nat) : (term28 m) = (term28 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1366200 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term29 m n) = (term35 m).
Proof. exact (MK_COMB (@lem1366199 m) (@lem1366169 n h1)). Qed.
Lemma lem1366201 (m : nat) : (term35 m) = ((term36 m) = (term37 m)).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem1366202 (m : nat) (n : nat) : (term33 m n) = (term33 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1366203 (n : nat) (m : nat) : ((term29 m n) = (term35 m)) = ((term29 m n) = ((term36 m) = (term37 m))).
Proof. exact (MK_COMB (@lem1366202 m n) (@lem1366201 m)). Qed.
Lemma lem1366204 (m : nat) (n : nat) : (term29 m n) = ((term19 n m) = (term19 m n)).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem1366205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366206 (m : nat) (n : nat) : (term33 m n) = (term34 m n).
Proof. exact (MK_COMB (@lem1366205) (@lem1366204 m n)). Qed.
Lemma lem1366207 (m : nat) : ((term36 m) = (term37 m)) = ((term36 m) = (term37 m)).
Proof. exact (eq_refl ((term36 m) = (term37 m))). Qed.
Lemma lem1366208 (n : nat) (m : nat) : ((term29 m n) = ((term36 m) = (term37 m))) = (((term19 n m) = (term19 m n)) = ((term36 m) = (term37 m))).
Proof. exact (MK_COMB (@lem1366206 m n) (@lem1366207 m)). Qed.
Lemma lem1366209 (n : nat) (m : nat) : ((term29 m n) = (term35 m)) = (((term19 n m) = (term19 m n)) = ((term36 m) = (term37 m))).
Proof. exact (TRANS (@lem1366203 n m) (@lem1366208 n m)). Qed.
Lemma lem1366210 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : ((term19 n m) = (term19 m n)) = ((term36 m) = (term37 m)).
Proof. exact (EQ_MP (@lem1366209 n m) (@lem1366200 m n h1)). Qed.
Lemma lem1366211 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : ((term36 m) = (term37 m)) = ((term19 n m) = (term19 m n)).
Proof. exact (SYM (@lem1366210 m n h1)). Qed.
Lemma lem1366215 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1366216 (m : nat) : (term38 m) = (m = (NUMERAL 0)).
Proof. exact (@lem1366215 (m = (NUMERAL 0))). Qed.
Lemma lem1366219 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1366220 (m : nat) : (term31 m) = (term39 m).
Proof. exact (MK_COMB (@lem1366219) (@lem1366216 m)). Qed.
Lemma lem1366221 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366222 (m : nat) : (term40 m) = (term41 m).
Proof. exact (MK_COMB (@lem1366221) (@lem1366220 m)). Qed.
Lemma lem1366224 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1366225 (m : nat) : (term42 m) = (m = (NUMERAL 0)).
Proof. exact (@lem1366224 (m = (NUMERAL 0))). Qed.
Lemma lem1366228 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1366229 (m : nat) : (term32 m) = (term39 m).
Proof. exact (MK_COMB (@lem1366228) (@lem1366225 m)). Qed.
Lemma lem1366230 (m : nat) : ((term31 m) = (term32 m)) = ((term39 m) = (term39 m)).
Proof. exact (MK_COMB (@lem1366222 m) (@lem1366229 m)). Qed.
Lemma lem1366232 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1366233 (x : Prop) : (x = x) = True.
Proof. exact (@lem1366232 Prop x). Qed.
Lemma lem1366234 (m : nat) : ((term39 m) = (term39 m)) = True.
Proof. exact (@lem1366233 (term39 m)). Qed.
Lemma lem1366235 (m : nat) : ((term31 m) = (term32 m)) = True.
Proof. exact (TRANS (@lem1366230 m) (@lem1366234 m)). Qed.
Lemma lem1366236 (m : nat) : True = ((term31 m) = (term32 m)).
Proof. exact (SYM (@lem1366235 m)). Qed.
Lemma lem1366237 (m : nat) : (term31 m) = (term32 m).
Proof. exact (EQ_MP (@lem1366236 m) (@lem0)). Qed.
Lemma lem1366241 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1366242 (m : nat) : (term43 m) = False.
Proof. exact (@lem1366241 (m = (NUMERAL 0))). Qed.
Lemma lem1366243 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1366244 (m : nat) : (term36 m) = (~ False).
Proof. exact (MK_COMB (@lem1366243) (@lem1366242 m)). Qed.
Lemma lem1366246 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1366247 (m : nat) : (term36 m) = True.
Proof. exact (TRANS (@lem1366244 m) (@lem1366246)). Qed.
Lemma lem1366248 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1366249 (m : nat) : (term44 m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1366248) (@lem1366247 m)). Qed.
Lemma lem1366251 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1366252 (m : nat) : (term45 m) = False.
Proof. exact (@lem1366251 (m = (NUMERAL 0))). Qed.
Lemma lem1366253 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1366254 (m : nat) : (term37 m) = (~ False).
Proof. exact (MK_COMB (@lem1366253) (@lem1366252 m)). Qed.
Lemma lem1366256 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1366257 (m : nat) : (term37 m) = True.
Proof. exact (TRANS (@lem1366254 m) (@lem1366256)). Qed.
Lemma lem1366258 (m : nat) : ((term36 m) = (term37 m)) = (True = True).
Proof. exact (MK_COMB (@lem1366249 m) (@lem1366257 m)). Qed.
Lemma lem1366260 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1366261 : (True = True) = True.
Proof. exact (@lem1366260 True). Qed.
Lemma lem1366262 (m : nat) : ((term36 m) = (term37 m)) = True.
Proof. exact (TRANS (@lem1366258 m) (@lem1366261)). Qed.
Lemma lem1366263 (m : nat) : True = ((term36 m) = (term37 m)).
Proof. exact (SYM (@lem1366262 m)). Qed.
Lemma lem1366264 (m : nat) : (term36 m) = (term37 m).
Proof. exact (EQ_MP (@lem1366263 m) (@lem0)). Qed.
Lemma lem1366265 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term19 n m) = (term19 m n).
Proof. exact (EQ_MP (@lem1366211 m n h1) (@lem1366264 m)). Qed.
Lemma lem1366266 (m : nat) (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term19 n m) = (term19 m n).
Proof. exact (EQ_MP (@lem1366198 m n h1) (@lem1366237 m)). Qed.
Lemma lem1366269 (m : nat) (n : nat) : (term19 n m) = (term19 m n).
Proof. exact (or_elim (@lem1366167 n) (fun h0 : (n = (NUMERAL 0)) = True => @lem1366266 m n h0) (fun h0 : (n = (NUMERAL 0)) = False => @lem1366265 m n h0)). Qed.
Lemma lem1366270 (m : nat) (n : nat) : term25 m n.
Proof. exact (EQ_MP (@lem1366148 m n) (@lem1366269 m n)). Qed.
