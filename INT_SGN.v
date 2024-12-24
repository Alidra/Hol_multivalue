Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SGN_term_abbrevs.
Require Import real_sgn_spec.
Require Import thm2299672_spec.
Require Import thm2299871_spec.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2308979 (x : int) : term0 x.
Proof. exact (@lem1710164 (real_of_int x)). Qed.
Lemma lem2308980 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2308981 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2308980 x) (@lem2308979 x)). Qed.
Lemma lem2308983 (x : int) : (term1 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2308984 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2308985 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2308984) (@lem2308983 x)). Qed.
Lemma lem2308987 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2308988 : term7 = term8.
Proof. exact (@lem2308987 (NUMERAL 0)). Qed.
Lemma lem2308989 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2308990 : term9 = term10.
Proof. exact (MK_COMB (@lem2308989) (@lem2308988)). Qed.
Lemma lem2308991 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2308992 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2308990) (@lem2308991 x)). Qed.
Lemma lem2308994 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2308995 (x : int) : (term12 x) = (term14 x).
Proof. exact (@lem2308994 term15 x). Qed.
Lemma lem2308996 (x : int) : (term11 x) = (term14 x).
Proof. exact (TRANS (@lem2308992 x) (@lem2308995 x)). Qed.
Lemma lem2308997 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem2308998 (x : int) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem2308997) (@lem2308996 x)). Qed.
Lemma lem2309000 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309001 : term18 = term19.
Proof. exact (@lem2309000 term20). Qed.
Lemma lem2309002 (x : int) : (term21 x) = (term22 x).
Proof. exact (MK_COMB (@lem2308998 x) (@lem2309001)). Qed.
Lemma lem2309004 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309005 : term7 = term8.
Proof. exact (@lem2309004 (NUMERAL 0)). Qed.
Lemma lem2309006 (x : int) : (term23 x) = (term23 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem2309007 (x : int) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem2309006 x) (@lem2309005)). Qed.
Lemma lem2309009 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2309010 (x : int) : (term25 x) = (term26 x).
Proof. exact (@lem2309009 x term15). Qed.
Lemma lem2309011 (x : int) : (term24 x) = (term26 x).
Proof. exact (TRANS (@lem2309007 x) (@lem2309010 x)). Qed.
Lemma lem2309012 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem2309013 (x : int) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem2309012) (@lem2309011 x)). Qed.
Lemma lem2309015 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309016 : term18 = term19.
Proof. exact (@lem2309015 term20). Qed.
Lemma lem2309017 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2309018 : term29 = term30.
Proof. exact (MK_COMB (@lem2309017) (@lem2309016)). Qed.
Lemma lem2309020 (x : int) : (term31 x) = (term32 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2309021 : term30 = term33.
Proof. exact (@lem2309020 term34). Qed.
Lemma lem2309022 : term29 = term33.
Proof. exact (TRANS (@lem2309018) (@lem2309021)). Qed.
Lemma lem2309023 (x : int) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem2309013 x) (@lem2309022)). Qed.
Lemma lem2309025 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309026 : term7 = term8.
Proof. exact (@lem2309025 (NUMERAL 0)). Qed.
Lemma lem2309027 (x : int) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem2309023 x) (@lem2309026)). Qed.
Lemma lem2309029 (b : Prop) (x : int) (y : int) : (term39 b x y) = (term40 b x y).
Proof. exact (EQ_MP (@lem2299871 b x y) (@lem2299672 b x y)). Qed.
Lemma lem2309030 (x : int) : (term38 x) = (term41 x).
Proof. exact (@lem2309029 (term26 x) term42 term15). Qed.
Lemma lem2309031 (x : int) : (term37 x) = (term41 x).
Proof. exact (TRANS (@lem2309027 x) (@lem2309030 x)). Qed.
Lemma lem2309032 (x : int) : (term2 x) = (term43 x).
Proof. exact (MK_COMB (@lem2309002 x) (@lem2309031 x)). Qed.
Lemma lem2309034 (b : Prop) (x : int) (y : int) : (term39 b x y) = (term40 b x y).
Proof. exact (EQ_MP (@lem2299871 b x y) (@lem2299672 b x y)). Qed.
Lemma lem2309035 (x : int) : (term43 x) = (term44 x).
Proof. exact (@lem2309034 (term14 x) term34 (term45 x)). Qed.
Lemma lem2309036 (x : int) : (term2 x) = (term44 x).
Proof. exact (TRANS (@lem2309032 x) (@lem2309035 x)). Qed.
Lemma lem2309037 (x : int) : ((term1 x) = (term2 x)) = ((term3 x) = (term44 x)).
Proof. exact (MK_COMB (@lem2308985 x) (@lem2309036 x)). Qed.
Lemma lem2309039 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309040 (x : int) : ((term3 x) = (term44 x)) = ((int_sgn x) = (term46 x)).
Proof. exact (@lem2309039 (int_sgn x) (term46 x)). Qed.
Lemma lem2309041 (x : int) : ((term1 x) = (term2 x)) = ((int_sgn x) = (term46 x)).
Proof. exact (TRANS (@lem2309037 x) (@lem2309040 x)). Qed.
Lemma lem2309042 (x : int) : (int_sgn x) = (term46 x).
Proof. exact (EQ_MP (@lem2309041 x) (@lem2308981 x)). Qed.
Lemma lem2309043 : term47.
Proof. exact (fun x : int => @lem2309042 x). Qed.
