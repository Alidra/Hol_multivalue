Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_BETWEEN1_term_abbrevs.
Require Import REAL_ABS_BETWEEN1_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2300083 (x : int) : term0 x.
Proof. exact (@lem1541398 (real_of_int x)). Qed.
Lemma lem2300084 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300085 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2300084 x) (@lem2300083 x)). Qed.
Lemma lem2300086 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2300085 x (real_of_int y)). Qed.
Lemma lem2300087 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2300088 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2300087 x y) (@lem2300086 x y)). Qed.
Lemma lem2300089 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2300088 x y (real_of_int z)). Qed.
Lemma lem2300090 (x : int) (y : int) (z : int) : (term4 x y z) = (term5 x y z).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2300091 (x : int) (y : int) (z : int) : term5 x y z.
Proof. exact (EQ_MP (@lem2300090 x y z) (@lem2300089 x y z)). Qed.
Lemma lem2300093 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300094 (x : int) (z : int) : (term6 x z) = (int_lt x z).
Proof. exact (@lem2300093 x z). Qed.
Lemma lem2300095 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2300096 (x : int) (z : int) : (term7 x z) = (term8 x z).
Proof. exact (MK_COMB (@lem2300095) (@lem2300094 x z)). Qed.
Lemma lem2300098 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300099 (y : int) (x : int) : (term9 y x) = (term10 y x).
Proof. exact (@lem2300098 y x). Qed.
Lemma lem2300100 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300101 (y : int) (x : int) : (term11 y x) = (term12 y x).
Proof. exact (MK_COMB (@lem2300100) (@lem2300099 y x)). Qed.
Lemma lem2300103 (x : int) : (term13 x) = (term14 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300104 (y : int) (x : int) : (term12 y x) = (term15 y x).
Proof. exact (@lem2300103 (int_sub y x)). Qed.
Lemma lem2300105 (y : int) (x : int) : (term11 y x) = (term15 y x).
Proof. exact (TRANS (@lem2300101 y x) (@lem2300104 y x)). Qed.
Lemma lem2300106 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2300107 (y : int) (x : int) : (term16 y x) = (term17 y x).
Proof. exact (MK_COMB (@lem2300106) (@lem2300105 y x)). Qed.
Lemma lem2300109 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300110 (z : int) (x : int) : (term9 z x) = (term10 z x).
Proof. exact (@lem2300109 z x). Qed.
Lemma lem2300111 (y : int) (z : int) (x : int) : (term18 y z x) = (term19 y z x).
Proof. exact (MK_COMB (@lem2300107 y x) (@lem2300110 z x)). Qed.
Lemma lem2300113 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300114 (y : int) (z : int) (x : int) : (term19 y z x) = (term20 y z x).
Proof. exact (@lem2300113 (term21 y x) (int_sub z x)). Qed.
Lemma lem2300115 (y : int) (z : int) (x : int) : (term18 y z x) = (term20 y z x).
Proof. exact (TRANS (@lem2300111 y z x) (@lem2300114 y z x)). Qed.
Lemma lem2300116 (y : int) (z : int) (x : int) : (term22 y z x) = (term23 y z x).
Proof. exact (MK_COMB (@lem2300096 x z) (@lem2300115 y z x)). Qed.
Lemma lem2300117 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2300118 (y : int) (z : int) (x : int) : (term24 y z x) = (term25 y z x).
Proof. exact (MK_COMB (@lem2300117) (@lem2300116 y z x)). Qed.
Lemma lem2300120 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300121 (y : int) (z : int) : (term6 y z) = (int_lt y z).
Proof. exact (@lem2300120 y z). Qed.
Lemma lem2300122 (x : int) (y : int) (z : int) : (term5 x y z) = (term26 x y z).
Proof. exact (MK_COMB (@lem2300118 y z x) (@lem2300121 y z)). Qed.
Lemma lem2300123 (x : int) (y : int) (z : int) : term26 x y z.
Proof. exact (EQ_MP (@lem2300122 x y z) (@lem2300091 x y z)). Qed.
Lemma lem2300124 (x : int) (y : int) : term27 x y.
Proof. exact (fun z : int => @lem2300123 x y z). Qed.
Lemma lem2300125 (x : int) : term28 x.
Proof. exact (fun y : int => @lem2300124 x y). Qed.
Lemma lem2300126 : term29.
Proof. exact (fun x : int => @lem2300125 x). Qed.
