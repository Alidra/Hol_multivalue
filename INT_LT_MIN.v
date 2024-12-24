Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_MIN_term_abbrevs.
Require Import REAL_LT_MIN_spec.
Require Import thm2299882_spec.
Require Import thm2299883_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304312 (x : int) : term0 x.
Proof. exact (@lem1565427 (real_of_int x)). Qed.
Lemma lem2304313 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304314 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304313 x) (@lem2304312 x)). Qed.
Lemma lem2304315 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304314 x (real_of_int y)). Qed.
Lemma lem2304316 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304317 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2304316 x y) (@lem2304315 x y)). Qed.
Lemma lem2304318 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2304317 x y (real_of_int z)). Qed.
Lemma lem2304319 (x : int) (z : int) (y : int) : (term4 x y z) = ((term5 z x y) = (term6 x z y)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2304320 (x : int) (z : int) (y : int) : (term5 z x y) = (term6 x z y).
Proof. exact (EQ_MP (@lem2304319 x z y) (@lem2304318 x y z)). Qed.
Lemma lem2304322 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2304323 (z : int) : (term9 z) = (term9 z).
Proof. exact (eq_refl (term9 z)). Qed.
Lemma lem2304324 (z : int) (x : int) (y : int) : (term5 z x y) = (term10 z x y).
Proof. exact (MK_COMB (@lem2304323 z) (@lem2304322 x y)). Qed.
Lemma lem2304326 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304327 (z : int) (x : int) (y : int) : (term10 z x y) = (term12 z x y).
Proof. exact (@lem2304326 z (int_min x y)). Qed.
Lemma lem2304328 (z : int) (x : int) (y : int) : (term5 z x y) = (term12 z x y).
Proof. exact (TRANS (@lem2304324 z x y) (@lem2304327 z x y)). Qed.
Lemma lem2304329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2304330 (z : int) (x : int) (y : int) : (term13 z x y) = (term14 z x y).
Proof. exact (MK_COMB (@lem2304329) (@lem2304328 z x y)). Qed.
Lemma lem2304332 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304333 (z : int) (x : int) : (term11 z x) = (int_lt z x).
Proof. exact (@lem2304332 z x). Qed.
Lemma lem2304334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2304335 (z : int) (x : int) : (term15 z x) = (term16 z x).
Proof. exact (MK_COMB (@lem2304334) (@lem2304333 z x)). Qed.
Lemma lem2304337 (x : int) (y : int) : (term11 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304338 (z : int) (y : int) : (term11 z y) = (int_lt z y).
Proof. exact (@lem2304337 z y). Qed.
Lemma lem2304339 (x : int) (z : int) (y : int) : (term6 x z y) = (term17 x z y).
Proof. exact (MK_COMB (@lem2304335 z x) (@lem2304338 z y)). Qed.
Lemma lem2304340 (x : int) (z : int) (y : int) : ((term5 z x y) = (term6 x z y)) = ((term12 z x y) = (term17 x z y)).
Proof. exact (MK_COMB (@lem2304330 z x y) (@lem2304339 x z y)). Qed.
Lemma lem2304341 (x : int) (z : int) (y : int) : (term12 z x y) = (term17 x z y).
Proof. exact (EQ_MP (@lem2304340 x z y) (@lem2304320 x z y)). Qed.
Lemma lem2304342 (x : int) (y : int) : term18 x y.
Proof. exact (fun z : int => @lem2304341 x z y). Qed.
Lemma lem2304343 (x : int) : term19 x.
Proof. exact (fun y : int => @lem2304342 x y). Qed.
Lemma lem2304344 : term20.
Proof. exact (fun x : int => @lem2304343 x). Qed.
