Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_LCANCEL_IMP_term_abbrevs.
Require Import REAL_LT_LCANCEL_IMP_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304087 (x : int) : term0 x.
Proof. exact (@lem1598529 (real_of_int x)). Qed.
Lemma lem2304088 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304089 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304088 x) (@lem2304087 x)). Qed.
Lemma lem2304090 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304089 x (real_of_int y)). Qed.
Lemma lem2304091 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304092 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2304091 x y) (@lem2304090 x y)). Qed.
Lemma lem2304093 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2304092 x y (real_of_int z)). Qed.
Lemma lem2304094 (x : int) (y : int) (z : int) : (term4 x y z) = (term5 x y z).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2304095 (x : int) (y : int) (z : int) : term5 x y z.
Proof. exact (EQ_MP (@lem2304094 x y z) (@lem2304093 x y z)). Qed.
Lemma lem2304097 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304098 : term7 = term8.
Proof. exact (@lem2304097 (NUMERAL 0)). Qed.
Lemma lem2304099 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304100 : term9 = term10.
Proof. exact (MK_COMB (@lem2304099) (@lem2304098)). Qed.
Lemma lem2304101 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2304102 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2304100) (@lem2304101 x)). Qed.
Lemma lem2304104 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304105 (x : int) : (term12 x) = (term14 x).
Proof. exact (@lem2304104 term15 x). Qed.
Lemma lem2304106 (x : int) : (term11 x) = (term14 x).
Proof. exact (TRANS (@lem2304102 x) (@lem2304105 x)). Qed.
Lemma lem2304107 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2304108 (x : int) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem2304107) (@lem2304106 x)). Qed.
Lemma lem2304110 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304111 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304112 (x : int) (y : int) : (term20 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem2304111) (@lem2304110 x y)). Qed.
Lemma lem2304114 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304115 (x : int) (z : int) : (term18 x z) = (term19 x z).
Proof. exact (@lem2304114 x z). Qed.
Lemma lem2304116 (y : int) (x : int) (z : int) : (term22 y x z) = (term23 y x z).
Proof. exact (MK_COMB (@lem2304112 x y) (@lem2304115 x z)). Qed.
Lemma lem2304118 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304119 (y : int) (x : int) (z : int) : (term23 y x z) = (term24 y x z).
Proof. exact (@lem2304118 (int_mul x y) (int_mul x z)). Qed.
Lemma lem2304120 (y : int) (x : int) (z : int) : (term22 y x z) = (term24 y x z).
Proof. exact (TRANS (@lem2304116 y x z) (@lem2304119 y x z)). Qed.
Lemma lem2304121 (y : int) (x : int) (z : int) : (term25 y x z) = (term26 y x z).
Proof. exact (MK_COMB (@lem2304108 x) (@lem2304120 y x z)). Qed.
Lemma lem2304122 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2304123 (y : int) (x : int) (z : int) : (term27 y x z) = (term28 y x z).
Proof. exact (MK_COMB (@lem2304122) (@lem2304121 y x z)). Qed.
Lemma lem2304125 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304126 (y : int) (z : int) : (term13 y z) = (int_lt y z).
Proof. exact (@lem2304125 y z). Qed.
Lemma lem2304127 (x : int) (y : int) (z : int) : (term5 x y z) = (term29 x y z).
Proof. exact (MK_COMB (@lem2304123 y x z) (@lem2304126 y z)). Qed.
Lemma lem2304128 (x : int) (y : int) (z : int) : term29 x y z.
Proof. exact (EQ_MP (@lem2304127 x y z) (@lem2304095 x y z)). Qed.
Lemma lem2304129 (x : int) (y : int) : term30 x y.
Proof. exact (fun z : int => @lem2304128 x y z). Qed.
Lemma lem2304130 (x : int) : term31 x.
Proof. exact (fun y : int => @lem2304129 x y). Qed.
Lemma lem2304131 : term32.
Proof. exact (fun x : int => @lem2304130 x). Qed.
