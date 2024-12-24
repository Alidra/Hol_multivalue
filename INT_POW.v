Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_term_abbrevs.
Require Import thm0_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2317959 (x : real) : term0 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem2317960 (x : real) : (term1 x) = term2.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem2317961 : term3.
Proof. exact (fun x : real => @lem2317960 x). Qed.
Lemma lem2317962 (x : int) : term4 x.
Proof. exact (@lem2317961 (real_of_int x)). Qed.
Lemma lem2317963 (x : int) : (term4 x) = ((term5 x) = term2).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem2317964 (x : int) : (term5 x) = term2.
Proof. exact (EQ_MP (@lem2317963 x) (@lem2317962 x)). Qed.
Lemma lem2317966 (x : int) (n : nat) : (term6 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2317967 (x : int) : (term5 x) = (term8 x).
Proof. exact (@lem2317966 x (NUMERAL 0)). Qed.
Lemma lem2317968 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2317969 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2317968) (@lem2317967 x)). Qed.
Lemma lem2317971 (n : nat) : (real_of_num n) = (term11 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2317972 : term2 = term12.
Proof. exact (@lem2317971 term13). Qed.
Lemma lem2317973 (x : int) : ((term5 x) = term2) = ((term8 x) = term12).
Proof. exact (MK_COMB (@lem2317969 x) (@lem2317972)). Qed.
Lemma lem2317975 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2317976 (x : int) : ((term8 x) = term12) = ((term14 x) = term15).
Proof. exact (@lem2317975 (term14 x) term15). Qed.
Lemma lem2317977 (x : int) : ((term5 x) = term2) = ((term14 x) = term15).
Proof. exact (TRANS (@lem2317973 x) (@lem2317976 x)). Qed.
Lemma lem2317979 : term16.
Proof. exact (fun x : real => @lem2317959 x). Qed.
Lemma lem2317980 (x : int) : term17 x.
Proof. exact (@lem2317979 (real_of_int x)). Qed.
Lemma lem2317981 (x : int) : (term17 x) = (term18 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem2317982 (x : int) : term18 x.
Proof. exact (EQ_MP (@lem2317981 x) (@lem2317980 x)). Qed.
Lemma lem2317983 (x : int) (n : nat) : term19 x n.
Proof. exact (@lem2317982 x n). Qed.
Lemma lem2317984 (x : int) (n : nat) : (term19 x n) = ((term20 x n) = (term21 x n)).
Proof. exact (eq_refl (term19 x n)). Qed.
Lemma lem2317985 (x : int) (n : nat) : (term20 x n) = (term21 x n).
Proof. exact (EQ_MP (@lem2317984 x n) (@lem2317983 x n)). Qed.
Lemma lem2317987 (x : int) (n : nat) : (term6 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2317988 (x : int) (n : nat) : (term20 x n) = (term22 x n).
Proof. exact (@lem2317987 x (S n)). Qed.
Lemma lem2317989 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2317990 (x : int) (n : nat) : (term23 x n) = (term24 x n).
Proof. exact (MK_COMB (@lem2317989) (@lem2317988 x n)). Qed.
Lemma lem2317992 (x : int) (n : nat) : (term6 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2317993 (x : int) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem2317994 (x : int) (n : nat) : (term21 x n) = (term26 x n).
Proof. exact (MK_COMB (@lem2317993 x) (@lem2317992 x n)). Qed.
Lemma lem2317996 (x : int) (y : int) : (term27 x y) = (term28 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2317997 (x : int) (n : nat) : (term26 x n) = (term29 x n).
Proof. exact (@lem2317996 x (int_pow x n)). Qed.
Lemma lem2317998 (x : int) (n : nat) : (term21 x n) = (term29 x n).
Proof. exact (TRANS (@lem2317994 x n) (@lem2317997 x n)). Qed.
Lemma lem2317999 (x : int) (n : nat) : ((term20 x n) = (term21 x n)) = ((term22 x n) = (term29 x n)).
Proof. exact (MK_COMB (@lem2317990 x n) (@lem2317998 x n)). Qed.
Lemma lem2318001 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2318002 (x : int) (n : nat) : ((term22 x n) = (term29 x n)) = ((term30 x n) = (term31 x n)).
Proof. exact (@lem2318001 (term30 x n) (term31 x n)). Qed.
Lemma lem2318003 (x : int) (n : nat) : ((term20 x n) = (term21 x n)) = ((term30 x n) = (term31 x n)).
Proof. exact (TRANS (@lem2317999 x n) (@lem2318002 x n)). Qed.
Lemma lem2318004 (x : int) (n : nat) : (term30 x n) = (term31 x n).
Proof. exact (EQ_MP (@lem2318003 x n) (@lem2317985 x n)). Qed.
Lemma lem2318005 (x : int) : term32 x.
Proof. exact (fun n : nat => @lem2318004 x n). Qed.
Lemma lem2318006 (x : int) (n : nat) : term33 x n.
Proof. exact (@lem2318005 x n). Qed.
Lemma lem2318007 (x : int) (n : nat) : (term33 x n) = ((term30 x n) = (term31 x n)).
Proof. exact (eq_refl (term33 x n)). Qed.
Lemma lem2318014 (x : int) : (term14 x) = term15.
Proof. exact (EQ_MP (@lem2317977 x) (@lem2317964 x)). Qed.
Lemma lem2318015 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2318016 (x : int) : (term34 x) = term35.
Proof. exact (MK_COMB (@lem2318015) (@lem2318014 x)). Qed.
Lemma lem2318017 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem2318018 (x : int) : ((term14 x) = term15) = (term15 = term15).
Proof. exact (MK_COMB (@lem2318016 x) (@lem2318017)). Qed.
Lemma lem2318020 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2318021 (x : int) : (x = x) = True.
Proof. exact (@lem2318020 int x). Qed.
Lemma lem2318022 : (term15 = term15) = True.
Proof. exact (@lem2318021 term15). Qed.
Lemma lem2318023 (x : int) : ((term14 x) = term15) = True.
Proof. exact (TRANS (@lem2318018 x) (@lem2318022)). Qed.
Lemma lem2318024 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2318025 (x : int) : (term36 x) = (and True).
Proof. exact (MK_COMB (@lem2318024) (@lem2318023 x)). Qed.
Lemma lem2318033 (x : int) (n : nat) : (term30 x n) = (term31 x n).
Proof. exact (EQ_MP (@lem2318007 x n) (@lem2318006 x n)). Qed.
Lemma lem2318034 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2318035 (x : int) (n : nat) : (term37 x n) = (term38 x n).
Proof. exact (MK_COMB (@lem2318034) (@lem2318033 x n)). Qed.
Lemma lem2318036 (x : int) (n : nat) : (term31 x n) = (term31 x n).
Proof. exact (eq_refl (term31 x n)). Qed.
Lemma lem2318037 (x : int) (n : nat) : ((term30 x n) = (term31 x n)) = ((term31 x n) = (term31 x n)).
Proof. exact (MK_COMB (@lem2318035 x n) (@lem2318036 x n)). Qed.
Lemma lem2318039 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2318040 (x : int) : (x = x) = True.
Proof. exact (@lem2318039 int x). Qed.
Lemma lem2318041 (x : int) (n : nat) : ((term31 x n) = (term31 x n)) = True.
Proof. exact (@lem2318040 (term31 x n)). Qed.
Lemma lem2318042 (x : int) (n : nat) : ((term30 x n) = (term31 x n)) = True.
Proof. exact (TRANS (@lem2318037 x n) (@lem2318041 x n)). Qed.
Lemma lem2318043 (x : int) : (term39 x) = term40.
Proof. exact (fun_ext (fun n : nat => @lem2318042 x n)). Qed.
Lemma lem2318044 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2318045 (x : int) : (term32 x) = term41.
Proof. exact (MK_COMB (@lem2318044) (@lem2318043 x)). Qed.
Lemma lem2318047 {A : Type'} (t : Prop) : (term42 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2318048 (t : Prop) : (term43 t) = t.
Proof. exact (@lem2318047 nat t). Qed.
Lemma lem2318049 : term41 = True.
Proof. exact (@lem2318048 True). Qed.
Lemma lem2318050 (x : int) : (term32 x) = True.
Proof. exact (TRANS (@lem2318045 x) (@lem2318049)). Qed.
Lemma lem2318051 (x : int) : (term44 x) = (True /\ True).
Proof. exact (MK_COMB (@lem2318025 x) (@lem2318050 x)). Qed.
Lemma lem2318053 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2318054 : (True /\ True) = True.
Proof. exact (@lem2318053 True). Qed.
Lemma lem2318055 (x : int) : (term44 x) = True.
Proof. exact (TRANS (@lem2318051 x) (@lem2318054)). Qed.
Lemma lem2318056 (x : int) : True = (term44 x).
Proof. exact (SYM (@lem2318055 x)). Qed.
Lemma lem2318057 (x : int) : term44 x.
Proof. exact (EQ_MP (@lem2318056 x) (@lem0)). Qed.
