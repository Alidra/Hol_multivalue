Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_RCANCEL_IMP_term_abbrevs.
Require Import REAL_LE_RCANCEL_IMP_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303105 (x : int) : term0 x.
Proof. exact (@lem1599119 (real_of_int x)). Qed.
Lemma lem2303106 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303107 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303106 x) (@lem2303105 x)). Qed.
Lemma lem2303108 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303107 x (real_of_int y)). Qed.
Lemma lem2303109 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303110 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2303109 x y) (@lem2303108 x y)). Qed.
Lemma lem2303111 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2303110 x y (real_of_int z)). Qed.
Lemma lem2303112 (z : int) (x : int) (y : int) : (term4 x y z) = (term5 z x y).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2303113 (z : int) (x : int) (y : int) : term5 z x y.
Proof. exact (EQ_MP (@lem2303112 z x y) (@lem2303111 x y z)). Qed.
Lemma lem2303115 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303116 : term7 = term8.
Proof. exact (@lem2303115 (NUMERAL 0)). Qed.
Lemma lem2303117 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2303118 : term9 = term10.
Proof. exact (MK_COMB (@lem2303117) (@lem2303116)). Qed.
Lemma lem2303119 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2303120 (z : int) : (term11 z) = (term12 z).
Proof. exact (MK_COMB (@lem2303118) (@lem2303119 z)). Qed.
Lemma lem2303122 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303123 (z : int) : (term12 z) = (term14 z).
Proof. exact (@lem2303122 term15 z). Qed.
Lemma lem2303124 (z : int) : (term11 z) = (term14 z).
Proof. exact (TRANS (@lem2303120 z) (@lem2303123 z)). Qed.
Lemma lem2303125 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2303126 (z : int) : (term16 z) = (term17 z).
Proof. exact (MK_COMB (@lem2303125) (@lem2303124 z)). Qed.
Lemma lem2303128 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2303129 (x : int) (z : int) : (term18 x z) = (term19 x z).
Proof. exact (@lem2303128 x z). Qed.
Lemma lem2303130 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2303131 (x : int) (z : int) : (term20 x z) = (term21 x z).
Proof. exact (MK_COMB (@lem2303130) (@lem2303129 x z)). Qed.
Lemma lem2303133 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2303134 (y : int) (z : int) : (term18 y z) = (term19 y z).
Proof. exact (@lem2303133 y z). Qed.
Lemma lem2303135 (x : int) (y : int) (z : int) : (term22 x y z) = (term23 x y z).
Proof. exact (MK_COMB (@lem2303131 x z) (@lem2303134 y z)). Qed.
Lemma lem2303137 (x : int) (y : int) : (term24 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303138 (x : int) (y : int) (z : int) : (term23 x y z) = (term25 x y z).
Proof. exact (@lem2303137 (int_mul x z) (int_mul y z)). Qed.
Lemma lem2303139 (x : int) (y : int) (z : int) : (term22 x y z) = (term25 x y z).
Proof. exact (TRANS (@lem2303135 x y z) (@lem2303138 x y z)). Qed.
Lemma lem2303140 (x : int) (y : int) (z : int) : (term26 x y z) = (term27 x y z).
Proof. exact (MK_COMB (@lem2303126 z) (@lem2303139 x y z)). Qed.
Lemma lem2303141 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2303142 (x : int) (y : int) (z : int) : (term28 x y z) = (term29 x y z).
Proof. exact (MK_COMB (@lem2303141) (@lem2303140 x y z)). Qed.
Lemma lem2303144 (x : int) (y : int) : (term24 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303145 (z : int) (x : int) (y : int) : (term5 z x y) = (term30 z x y).
Proof. exact (MK_COMB (@lem2303142 x y z) (@lem2303144 x y)). Qed.
Lemma lem2303146 (z : int) (x : int) (y : int) : term30 z x y.
Proof. exact (EQ_MP (@lem2303145 z x y) (@lem2303113 z x y)). Qed.
Lemma lem2303147 (x : int) (y : int) : term31 x y.
Proof. exact (fun z : int => @lem2303146 z x y). Qed.
Lemma lem2303148 (x : int) : term32 x.
Proof. exact (fun y : int => @lem2303147 x y). Qed.
Lemma lem2303149 : term33.
Proof. exact (fun x : int => @lem2303148 x). Qed.
