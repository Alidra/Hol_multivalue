Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_BETWEEN_term_abbrevs.
Require Import REAL_ABS_BETWEEN_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2300013 (x : int) : term0 x.
Proof. exact (@lem1539149 (real_of_int x)). Qed.
Lemma lem2300014 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300015 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2300014 x) (@lem2300013 x)). Qed.
Lemma lem2300016 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2300015 x (real_of_int y)). Qed.
Lemma lem2300017 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2300018 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2300017 y x) (@lem2300016 x y)). Qed.
Lemma lem2300019 (y : int) (x : int) (d : int) : term4 y x d.
Proof. exact (@lem2300018 y x (real_of_int d)). Qed.
Lemma lem2300020 (y : int) (x : int) (d : int) : (term4 y x d) = ((term5 y x d) = (term6 y x d)).
Proof. exact (eq_refl (term4 y x d)). Qed.
Lemma lem2300021 (y : int) (x : int) (d : int) : (term5 y x d) = (term6 y x d).
Proof. exact (EQ_MP (@lem2300020 y x d) (@lem2300019 y x d)). Qed.
Lemma lem2300023 (n : nat) : (real_of_num n) = (term7 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2300024 : term8 = term9.
Proof. exact (@lem2300023 (NUMERAL 0)). Qed.
Lemma lem2300025 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2300026 : term10 = term11.
Proof. exact (MK_COMB (@lem2300025) (@lem2300024)). Qed.
Lemma lem2300027 (d : int) : (real_of_int d) = (real_of_int d).
Proof. exact (eq_refl (real_of_int d)). Qed.
Lemma lem2300028 (d : int) : (term12 d) = (term13 d).
Proof. exact (MK_COMB (@lem2300026) (@lem2300027 d)). Qed.
Lemma lem2300030 (x : int) (y : int) : (term14 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300031 (d : int) : (term13 d) = (term15 d).
Proof. exact (@lem2300030 term16 d). Qed.
Lemma lem2300032 (d : int) : (term12 d) = (term15 d).
Proof. exact (TRANS (@lem2300028 d) (@lem2300031 d)). Qed.
Lemma lem2300033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2300034 (d : int) : (term17 d) = (term18 d).
Proof. exact (MK_COMB (@lem2300033) (@lem2300032 d)). Qed.
Lemma lem2300036 (x : int) (y : int) : (term19 x y) = (term20 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300037 (x : int) (d : int) : (term19 x d) = (term20 x d).
Proof. exact (@lem2300036 x d). Qed.
Lemma lem2300038 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2300039 (x : int) (d : int) : (term21 x d) = (term22 x d).
Proof. exact (MK_COMB (@lem2300038) (@lem2300037 x d)). Qed.
Lemma lem2300040 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2300041 (x : int) (d : int) (y : int) : (term23 x d y) = (term24 x d y).
Proof. exact (MK_COMB (@lem2300039 x d) (@lem2300040 y)). Qed.
Lemma lem2300043 (x : int) (y : int) : (term14 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300044 (x : int) (d : int) (y : int) : (term24 x d y) = (term25 x d y).
Proof. exact (@lem2300043 (int_sub x d) y). Qed.
Lemma lem2300045 (x : int) (d : int) (y : int) : (term23 x d y) = (term25 x d y).
Proof. exact (TRANS (@lem2300041 x d y) (@lem2300044 x d y)). Qed.
Lemma lem2300046 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2300047 (x : int) (d : int) (y : int) : (term26 x d y) = (term27 x d y).
Proof. exact (MK_COMB (@lem2300046) (@lem2300045 x d y)). Qed.
Lemma lem2300049 (x : int) (y : int) : (term28 x y) = (term29 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2300050 (x : int) (d : int) : (term28 x d) = (term29 x d).
Proof. exact (@lem2300049 x d). Qed.
Lemma lem2300051 (y : int) : (term30 y) = (term30 y).
Proof. exact (eq_refl (term30 y)). Qed.
Lemma lem2300052 (y : int) (x : int) (d : int) : (term31 y x d) = (term32 y x d).
Proof. exact (MK_COMB (@lem2300051 y) (@lem2300050 x d)). Qed.
Lemma lem2300054 (x : int) (y : int) : (term14 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300055 (y : int) (x : int) (d : int) : (term32 y x d) = (term33 y x d).
Proof. exact (@lem2300054 y (int_add x d)). Qed.
Lemma lem2300056 (y : int) (x : int) (d : int) : (term31 y x d) = (term33 y x d).
Proof. exact (TRANS (@lem2300052 y x d) (@lem2300055 y x d)). Qed.
Lemma lem2300057 (y : int) (x : int) (d : int) : (term34 y x d) = (term35 y x d).
Proof. exact (MK_COMB (@lem2300047 x d y) (@lem2300056 y x d)). Qed.
Lemma lem2300058 (y : int) (x : int) (d : int) : (term5 y x d) = (term36 y x d).
Proof. exact (MK_COMB (@lem2300034 d) (@lem2300057 y x d)). Qed.
Lemma lem2300059 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2300060 (y : int) (x : int) (d : int) : (term37 y x d) = (term38 y x d).
Proof. exact (MK_COMB (@lem2300059) (@lem2300058 y x d)). Qed.
Lemma lem2300062 (x : int) (y : int) : (term19 x y) = (term20 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300063 (y : int) (x : int) : (term19 y x) = (term20 y x).
Proof. exact (@lem2300062 y x). Qed.
Lemma lem2300064 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300065 (y : int) (x : int) : (term39 y x) = (term40 y x).
Proof. exact (MK_COMB (@lem2300064) (@lem2300063 y x)). Qed.
Lemma lem2300067 (x : int) : (term41 x) = (term42 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300068 (y : int) (x : int) : (term40 y x) = (term43 y x).
Proof. exact (@lem2300067 (int_sub y x)). Qed.
Lemma lem2300069 (y : int) (x : int) : (term39 y x) = (term43 y x).
Proof. exact (TRANS (@lem2300065 y x) (@lem2300068 y x)). Qed.
Lemma lem2300070 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2300071 (y : int) (x : int) : (term44 y x) = (term45 y x).
Proof. exact (MK_COMB (@lem2300070) (@lem2300069 y x)). Qed.
Lemma lem2300072 (d : int) : (real_of_int d) = (real_of_int d).
Proof. exact (eq_refl (real_of_int d)). Qed.
Lemma lem2300073 (y : int) (x : int) (d : int) : (term6 y x d) = (term46 y x d).
Proof. exact (MK_COMB (@lem2300071 y x) (@lem2300072 d)). Qed.
Lemma lem2300075 (x : int) (y : int) : (term14 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300076 (y : int) (x : int) (d : int) : (term46 y x d) = (term47 y x d).
Proof. exact (@lem2300075 (term48 y x) d). Qed.
Lemma lem2300077 (y : int) (x : int) (d : int) : (term6 y x d) = (term47 y x d).
Proof. exact (TRANS (@lem2300073 y x d) (@lem2300076 y x d)). Qed.
Lemma lem2300078 (y : int) (x : int) (d : int) : ((term5 y x d) = (term6 y x d)) = ((term36 y x d) = (term47 y x d)).
Proof. exact (MK_COMB (@lem2300060 y x d) (@lem2300077 y x d)). Qed.
Lemma lem2300079 (y : int) (x : int) (d : int) : (term36 y x d) = (term47 y x d).
Proof. exact (EQ_MP (@lem2300078 y x d) (@lem2300021 y x d)). Qed.
Lemma lem2300080 (y : int) (x : int) : term49 y x.
Proof. exact (fun d : int => @lem2300079 y x d). Qed.
Lemma lem2300081 (x : int) : term50 x.
Proof. exact (fun y : int => @lem2300080 y x). Qed.
Lemma lem2300082 : term51.
Proof. exact (fun x : int => @lem2300081 x). Qed.
