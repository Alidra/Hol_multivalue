Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_MAX_term_abbrevs.
Require Import REAL_LT_MAX_spec.
Require Import thm2299888_spec.
Require Import thm2299889_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304279 (x : int) : term0 x.
Proof. exact (@lem1563918 (real_of_int x)). Qed.
Lemma lem2304280 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304281 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304280 x) (@lem2304279 x)). Qed.
Lemma lem2304282 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304281 x (real_of_int y)). Qed.
Lemma lem2304283 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304284 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2304283 x y) (@lem2304282 x y)). Qed.
Lemma lem2304285 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2304284 x y (real_of_int z)). Qed.
Lemma lem2304286 (x : int) (z : int) (y : int) : (term4 x y z) = ((term5 z x y) = (term6 x z y)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2304287 (x : int) (z : int) (y : int) : (term5 z x y) = (term6 x z y).
Proof. exact (EQ_MP (@lem2304286 x z y) (@lem2304285 x y z)). Qed.
Lemma lem2304289 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2304290 (z : int) : (term9 z) = (term9 z).
Proof. exact (eq_refl (term9 z)). Qed.
Lemma lem2304291 (z : int) (x : int) (y : int) : (term5 z x y) = (term10 z x y).
Proof. exact (MK_COMB (@lem2304290 z) (@lem2304289 x y)). Qed.
Lemma lem2304293 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304294 (z : int) (x : int) (y : int) : (term10 z x y) = (term12 z x y).
Proof. exact (@lem2304293 z (int_max x y)). Qed.
Lemma lem2304295 (z : int) (x : int) (y : int) : (term5 z x y) = (term12 z x y).
Proof. exact (TRANS (@lem2304291 z x y) (@lem2304294 z x y)). Qed.
Lemma lem2304296 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2304297 (z : int) (x : int) (y : int) : (term13 z x y) = (term14 z x y).
Proof. exact (MK_COMB (@lem2304296) (@lem2304295 z x y)). Qed.
Lemma lem2304299 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304300 (z : int) (x : int) : (term11 z x) = (int_lt z x).
Proof. exact (@lem2304299 z x). Qed.
Lemma lem2304301 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2304302 (z : int) (x : int) : (term15 z x) = (term16 z x).
Proof. exact (MK_COMB (@lem2304301) (@lem2304300 z x)). Qed.
Lemma lem2304304 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304305 (z : int) (y : int) : (term11 z y) = (int_lt z y).
Proof. exact (@lem2304304 z y). Qed.
Lemma lem2304306 (x : int) (z : int) (y : int) : (term6 x z y) = (term17 x z y).
Proof. exact (MK_COMB (@lem2304302 z x) (@lem2304305 z y)). Qed.
Lemma lem2304307 (x : int) (z : int) (y : int) : ((term5 z x y) = (term6 x z y)) = ((term12 z x y) = (term17 x z y)).
Proof. exact (MK_COMB (@lem2304297 z x y) (@lem2304306 x z y)). Qed.
Lemma lem2304308 (x : int) (z : int) (y : int) : (term12 z x y) = (term17 x z y).
Proof. exact (EQ_MP (@lem2304307 x z y) (@lem2304287 x z y)). Qed.
Lemma lem2304309 (x : int) (y : int) : term18 x y.
Proof. exact (fun z : int => @lem2304308 x z y). Qed.
Lemma lem2304310 (x : int) : term19 x.
Proof. exact (fun y : int => @lem2304309 x y). Qed.
Lemma lem2304311 : term20.
Proof. exact (fun x : int => @lem2304310 x). Qed.
