Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_ADDL_term_abbrevs.
Require Import REAL_LE_ADDL_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302264 (x : int) : term0 x.
Proof. exact (@lem1510621 (real_of_int x)). Qed.
Lemma lem2302265 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302266 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302265 x) (@lem2302264 x)). Qed.
Lemma lem2302267 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302266 x (real_of_int y)). Qed.
Lemma lem2302268 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (term4 x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302269 (y : int) (x : int) : (term3 x y) = (term4 x).
Proof. exact (EQ_MP (@lem2302268 y x) (@lem2302267 x y)). Qed.
Lemma lem2302271 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2302272 (y : int) : (term7 y) = (term7 y).
Proof. exact (eq_refl (term7 y)). Qed.
Lemma lem2302273 (x : int) (y : int) : (term3 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2302272 y) (@lem2302271 x y)). Qed.
Lemma lem2302275 (x : int) (y : int) : (term9 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302276 (x : int) (y : int) : (term8 x y) = (term10 x y).
Proof. exact (@lem2302275 y (int_add x y)). Qed.
Lemma lem2302277 (x : int) (y : int) : (term3 x y) = (term10 x y).
Proof. exact (TRANS (@lem2302273 x y) (@lem2302276 x y)). Qed.
Lemma lem2302278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2302279 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2302278) (@lem2302277 x y)). Qed.
Lemma lem2302281 (n : nat) : (real_of_num n) = (term13 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302282 : term14 = term15.
Proof. exact (@lem2302281 (NUMERAL 0)). Qed.
Lemma lem2302283 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302284 : term16 = term17.
Proof. exact (MK_COMB (@lem2302283) (@lem2302282)). Qed.
Lemma lem2302285 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2302286 (x : int) : (term4 x) = (term18 x).
Proof. exact (MK_COMB (@lem2302284) (@lem2302285 x)). Qed.
Lemma lem2302288 (x : int) (y : int) : (term9 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302289 (x : int) : (term18 x) = (term19 x).
Proof. exact (@lem2302288 term20 x). Qed.
Lemma lem2302290 (x : int) : (term4 x) = (term19 x).
Proof. exact (TRANS (@lem2302286 x) (@lem2302289 x)). Qed.
Lemma lem2302291 (y : int) (x : int) : ((term3 x y) = (term4 x)) = ((term10 x y) = (term19 x)).
Proof. exact (MK_COMB (@lem2302279 x y) (@lem2302290 x)). Qed.
Lemma lem2302292 (y : int) (x : int) : (term10 x y) = (term19 x).
Proof. exact (EQ_MP (@lem2302291 y x) (@lem2302269 y x)). Qed.
Lemma lem2302293 (x : int) : term21 x.
Proof. exact (fun y : int => @lem2302292 y x). Qed.
Lemma lem2302294 : term22.
Proof. exact (fun x : int => @lem2302293 x). Qed.
