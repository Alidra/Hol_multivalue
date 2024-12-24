Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_LT_term_abbrevs.
Require Import REAL_SUB_LT_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2310254 (x : int) : term0 x.
Proof. exact (@lem1376486 (real_of_int x)). Qed.
Lemma lem2310255 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2310256 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2310255 x) (@lem2310254 x)). Qed.
Lemma lem2310257 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2310256 x (real_of_int y)). Qed.
Lemma lem2310258 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (term4 y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2310259 (y : int) (x : int) : (term3 x y) = (term4 y x).
Proof. exact (EQ_MP (@lem2310258 y x) (@lem2310257 x y)). Qed.
Lemma lem2310261 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2310262 : term6 = term7.
Proof. exact (@lem2310261 (NUMERAL 0)). Qed.
Lemma lem2310263 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2310264 : term8 = term9.
Proof. exact (MK_COMB (@lem2310263) (@lem2310262)). Qed.
Lemma lem2310266 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310267 (x : int) (y : int) : (term3 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2310264) (@lem2310266 x y)). Qed.
Lemma lem2310269 (x : int) (y : int) : (term4 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2310270 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (@lem2310269 term14 (int_sub x y)). Qed.
Lemma lem2310271 (x : int) (y : int) : (term3 x y) = (term13 x y).
Proof. exact (TRANS (@lem2310267 x y) (@lem2310270 x y)). Qed.
Lemma lem2310272 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2310273 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem2310272) (@lem2310271 x y)). Qed.
Lemma lem2310275 (x : int) (y : int) : (term4 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2310276 (y : int) (x : int) : (term4 y x) = (int_lt y x).
Proof. exact (@lem2310275 y x). Qed.
Lemma lem2310277 (y : int) (x : int) : ((term3 x y) = (term4 y x)) = ((term13 x y) = (int_lt y x)).
Proof. exact (MK_COMB (@lem2310273 x y) (@lem2310276 y x)). Qed.
Lemma lem2310278 (y : int) (x : int) : (term13 x y) = (int_lt y x).
Proof. exact (EQ_MP (@lem2310277 y x) (@lem2310259 y x)). Qed.
Lemma lem2310279 (x : int) : term17 x.
Proof. exact (fun y : int => @lem2310278 y x). Qed.
Lemma lem2310280 : term18.
Proof. exact (fun x : int => @lem2310279 x). Qed.
