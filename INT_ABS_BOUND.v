Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_BOUND_term_abbrevs.
Require Import REAL_ABS_BOUND_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2300216 (x : int) : term0 x.
Proof. exact (@lem1539586 (real_of_int x)). Qed.
Lemma lem2300217 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300218 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2300217 x) (@lem2300216 x)). Qed.
Lemma lem2300219 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2300218 x (real_of_int y)). Qed.
Lemma lem2300220 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2300221 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2300220 y x) (@lem2300219 x y)). Qed.
Lemma lem2300222 (y : int) (x : int) (d : int) : term4 y x d.
Proof. exact (@lem2300221 y x (real_of_int d)). Qed.
Lemma lem2300223 (y : int) (x : int) (d : int) : (term4 y x d) = (term5 y x d).
Proof. exact (eq_refl (term4 y x d)). Qed.
Lemma lem2300224 (y : int) (x : int) (d : int) : term5 y x d.
Proof. exact (EQ_MP (@lem2300223 y x d) (@lem2300222 y x d)). Qed.
Lemma lem2300226 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300227 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300228 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2300227) (@lem2300226 x y)). Qed.
Lemma lem2300230 (x : int) : (term10 x) = (term11 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300231 (x : int) (y : int) : (term9 x y) = (term12 x y).
Proof. exact (@lem2300230 (int_sub x y)). Qed.
Lemma lem2300232 (x : int) (y : int) : (term8 x y) = (term12 x y).
Proof. exact (TRANS (@lem2300228 x y) (@lem2300231 x y)). Qed.
Lemma lem2300233 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2300234 (x : int) (y : int) : (term13 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem2300233) (@lem2300232 x y)). Qed.
Lemma lem2300235 (d : int) : (real_of_int d) = (real_of_int d).
Proof. exact (eq_refl (real_of_int d)). Qed.
Lemma lem2300236 (x : int) (y : int) (d : int) : (term15 x y d) = (term16 x y d).
Proof. exact (MK_COMB (@lem2300234 x y) (@lem2300235 d)). Qed.
Lemma lem2300238 (x : int) (y : int) : (term17 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300239 (x : int) (y : int) (d : int) : (term16 x y d) = (term18 x y d).
Proof. exact (@lem2300238 (term19 x y) d). Qed.
Lemma lem2300240 (x : int) (y : int) (d : int) : (term15 x y d) = (term18 x y d).
Proof. exact (TRANS (@lem2300236 x y d) (@lem2300239 x y d)). Qed.
Lemma lem2300241 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2300242 (x : int) (y : int) (d : int) : (term20 x y d) = (term21 x y d).
Proof. exact (MK_COMB (@lem2300241) (@lem2300240 x y d)). Qed.
Lemma lem2300244 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2300245 (x : int) (d : int) : (term22 x d) = (term23 x d).
Proof. exact (@lem2300244 x d). Qed.
Lemma lem2300246 (y : int) : (term24 y) = (term24 y).
Proof. exact (eq_refl (term24 y)). Qed.
Lemma lem2300247 (y : int) (x : int) (d : int) : (term25 y x d) = (term26 y x d).
Proof. exact (MK_COMB (@lem2300246 y) (@lem2300245 x d)). Qed.
Lemma lem2300249 (x : int) (y : int) : (term17 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300250 (y : int) (x : int) (d : int) : (term26 y x d) = (term27 y x d).
Proof. exact (@lem2300249 y (int_add x d)). Qed.
Lemma lem2300251 (y : int) (x : int) (d : int) : (term25 y x d) = (term27 y x d).
Proof. exact (TRANS (@lem2300247 y x d) (@lem2300250 y x d)). Qed.
Lemma lem2300252 (y : int) (x : int) (d : int) : (term5 y x d) = (term28 y x d).
Proof. exact (MK_COMB (@lem2300242 x y d) (@lem2300251 y x d)). Qed.
Lemma lem2300253 (y : int) (x : int) (d : int) : term28 y x d.
Proof. exact (EQ_MP (@lem2300252 y x d) (@lem2300224 y x d)). Qed.
Lemma lem2300254 (y : int) (x : int) : term29 y x.
Proof. exact (fun d : int => @lem2300253 y x d). Qed.
Lemma lem2300255 (x : int) : term30 x.
Proof. exact (fun y : int => @lem2300254 y x). Qed.
Lemma lem2300256 : term31.
Proof. exact (fun x : int => @lem2300255 x). Qed.
