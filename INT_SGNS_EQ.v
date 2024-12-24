Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SGNS_EQ_term_abbrevs.
Require Import REAL_SGNS_EQ_spec.
Require Import thm2299900_spec.
Require Import thm2299901_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299924_spec.
Require Import thm2299925_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2309044 (x : int) : term0 x.
Proof. exact (@lem1843951 (real_of_int x)). Qed.
Lemma lem2309045 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2309046 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2309045 x) (@lem2309044 x)). Qed.
Lemma lem2309047 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2309046 x (real_of_int y)). Qed.
Lemma lem2309048 (x : int) (y : int) : (term2 x y) = (((term3 x) = (term3 y)) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2309049 (x : int) (y : int) : ((term3 x) = (term3 y)) = (term4 x y).
Proof. exact (EQ_MP (@lem2309048 x y) (@lem2309047 x y)). Qed.
Lemma lem2309051 (x : int) : (term3 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309052 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2309053 (x : int) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem2309052) (@lem2309051 x)). Qed.
Lemma lem2309055 (x : int) : (term3 x) = (term5 x).
Proof. exact (EQ_MP (@lem2299901 x) (@lem2299900 x)). Qed.
Lemma lem2309056 (y : int) : (term3 y) = (term5 y).
Proof. exact (@lem2309055 y). Qed.
Lemma lem2309057 (x : int) (y : int) : ((term3 x) = (term3 y)) = ((term5 x) = (term5 y)).
Proof. exact (MK_COMB (@lem2309053 x) (@lem2309056 y)). Qed.
Lemma lem2309059 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309060 (x : int) (y : int) : ((term5 x) = (term5 y)) = ((int_sgn x) = (int_sgn y)).
Proof. exact (@lem2309059 (int_sgn x) (int_sgn y)). Qed.
Lemma lem2309061 (x : int) (y : int) : ((term3 x) = (term3 y)) = ((int_sgn x) = (int_sgn y)).
Proof. exact (TRANS (@lem2309057 x y) (@lem2309060 x y)). Qed.
Lemma lem2309062 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309063 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2309062) (@lem2309061 x y)). Qed.
Lemma lem2309065 (n : nat) : (real_of_num n) = (term10 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309066 : term11 = term12.
Proof. exact (@lem2309065 (NUMERAL 0)). Qed.
Lemma lem2309067 (x : int) : (term13 x) = (term13 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem2309068 (x : int) : ((real_of_int x) = term11) = ((real_of_int x) = term12).
Proof. exact (MK_COMB (@lem2309067 x) (@lem2309066)). Qed.
Lemma lem2309070 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309071 (x : int) : ((real_of_int x) = term12) = (x = term14).
Proof. exact (@lem2309070 x term14). Qed.
Lemma lem2309072 (x : int) : ((real_of_int x) = term11) = (x = term14).
Proof. exact (TRANS (@lem2309068 x) (@lem2309071 x)). Qed.
Lemma lem2309073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309074 (x : int) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem2309073) (@lem2309072 x)). Qed.
Lemma lem2309076 (n : nat) : (real_of_num n) = (term10 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309077 : term11 = term12.
Proof. exact (@lem2309076 (NUMERAL 0)). Qed.
Lemma lem2309078 (y : int) : (term13 y) = (term13 y).
Proof. exact (eq_refl (term13 y)). Qed.
Lemma lem2309079 (y : int) : ((real_of_int y) = term11) = ((real_of_int y) = term12).
Proof. exact (MK_COMB (@lem2309078 y) (@lem2309077)). Qed.
Lemma lem2309081 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2309082 (y : int) : ((real_of_int y) = term12) = (y = term14).
Proof. exact (@lem2309081 y term14). Qed.
Lemma lem2309083 (y : int) : ((real_of_int y) = term11) = (y = term14).
Proof. exact (TRANS (@lem2309079 y) (@lem2309082 y)). Qed.
Lemma lem2309084 (x : int) (y : int) : (((real_of_int x) = term11) = ((real_of_int y) = term11)) = ((x = term14) = (y = term14)).
Proof. exact (MK_COMB (@lem2309074 x) (@lem2309083 y)). Qed.
Lemma lem2309085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2309086 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem2309085) (@lem2309084 x y)). Qed.
Lemma lem2309088 (n : nat) : (real_of_num n) = (term10 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309089 : term11 = term12.
Proof. exact (@lem2309088 (NUMERAL 0)). Qed.
Lemma lem2309090 (x : int) : (term19 x) = (term19 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem2309091 (x : int) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem2309090 x) (@lem2309089)). Qed.
Lemma lem2309093 (x : int) (y : int) : (term22 x y) = (int_gt x y).
Proof. exact (EQ_MP (@lem2299925 x y) (@lem2299924 x y)). Qed.
Lemma lem2309094 (x : int) : (term21 x) = (term23 x).
Proof. exact (@lem2309093 x term14). Qed.
Lemma lem2309095 (x : int) : (term20 x) = (term23 x).
Proof. exact (TRANS (@lem2309091 x) (@lem2309094 x)). Qed.
Lemma lem2309096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309097 (x : int) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem2309096) (@lem2309095 x)). Qed.
Lemma lem2309099 (n : nat) : (real_of_num n) = (term10 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309100 : term11 = term12.
Proof. exact (@lem2309099 (NUMERAL 0)). Qed.
Lemma lem2309101 (y : int) : (term19 y) = (term19 y).
Proof. exact (eq_refl (term19 y)). Qed.
Lemma lem2309102 (y : int) : (term20 y) = (term21 y).
Proof. exact (MK_COMB (@lem2309101 y) (@lem2309100)). Qed.
Lemma lem2309104 (x : int) (y : int) : (term22 x y) = (int_gt x y).
Proof. exact (EQ_MP (@lem2299925 x y) (@lem2299924 x y)). Qed.
Lemma lem2309105 (y : int) : (term21 y) = (term23 y).
Proof. exact (@lem2309104 y term14). Qed.
Lemma lem2309106 (y : int) : (term20 y) = (term23 y).
Proof. exact (TRANS (@lem2309102 y) (@lem2309105 y)). Qed.
Lemma lem2309107 (x : int) (y : int) : ((term20 x) = (term20 y)) = ((term23 x) = (term23 y)).
Proof. exact (MK_COMB (@lem2309097 x) (@lem2309106 y)). Qed.
Lemma lem2309108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2309109 (x : int) (y : int) : (term26 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem2309108) (@lem2309107 x y)). Qed.
Lemma lem2309111 (n : nat) : (real_of_num n) = (term10 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309112 : term11 = term12.
Proof. exact (@lem2309111 (NUMERAL 0)). Qed.
Lemma lem2309113 (x : int) : (term28 x) = (term28 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem2309114 (x : int) : (term29 x) = (term30 x).
Proof. exact (MK_COMB (@lem2309113 x) (@lem2309112)). Qed.
Lemma lem2309116 (x : int) (y : int) : (term31 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2309117 (x : int) : (term30 x) = (term32 x).
Proof. exact (@lem2309116 x term14). Qed.
Lemma lem2309118 (x : int) : (term29 x) = (term32 x).
Proof. exact (TRANS (@lem2309114 x) (@lem2309117 x)). Qed.
Lemma lem2309119 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2309120 (x : int) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem2309119) (@lem2309118 x)). Qed.
Lemma lem2309122 (n : nat) : (real_of_num n) = (term10 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2309123 : term11 = term12.
Proof. exact (@lem2309122 (NUMERAL 0)). Qed.
Lemma lem2309124 (y : int) : (term28 y) = (term28 y).
Proof. exact (eq_refl (term28 y)). Qed.
Lemma lem2309125 (y : int) : (term29 y) = (term30 y).
Proof. exact (MK_COMB (@lem2309124 y) (@lem2309123)). Qed.
Lemma lem2309127 (x : int) (y : int) : (term31 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2309128 (y : int) : (term30 y) = (term32 y).
Proof. exact (@lem2309127 y term14). Qed.
Lemma lem2309129 (y : int) : (term29 y) = (term32 y).
Proof. exact (TRANS (@lem2309125 y) (@lem2309128 y)). Qed.
Lemma lem2309130 (x : int) (y : int) : ((term29 x) = (term29 y)) = ((term32 x) = (term32 y)).
Proof. exact (MK_COMB (@lem2309120 x) (@lem2309129 y)). Qed.
Lemma lem2309131 (x : int) (y : int) : (term35 x y) = (term36 x y).
Proof. exact (MK_COMB (@lem2309109 x y) (@lem2309130 x y)). Qed.
Lemma lem2309132 (x : int) (y : int) : (term4 x y) = (term37 x y).
Proof. exact (MK_COMB (@lem2309086 x y) (@lem2309131 x y)). Qed.
Lemma lem2309133 (x : int) (y : int) : (((term3 x) = (term3 y)) = (term4 x y)) = (((int_sgn x) = (int_sgn y)) = (term37 x y)).
Proof. exact (MK_COMB (@lem2309063 x y) (@lem2309132 x y)). Qed.
Lemma lem2309134 (x : int) (y : int) : ((int_sgn x) = (int_sgn y)) = (term37 x y).
Proof. exact (EQ_MP (@lem2309133 x y) (@lem2309049 x y)). Qed.
Lemma lem2309135 (x : int) : term38 x.
Proof. exact (fun y : int => @lem2309134 x y). Qed.
Lemma lem2309136 : term39.
Proof. exact (fun x : int => @lem2309135 x). Qed.
