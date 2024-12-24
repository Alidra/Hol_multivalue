Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_LCANCEL_IMP_term_abbrevs.
Require Import REAL_LE_LCANCEL_IMP_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302442 (x : int) : term0 x.
Proof. exact (@lem1599019 (real_of_int x)). Qed.
Lemma lem2302443 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302444 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302443 x) (@lem2302442 x)). Qed.
Lemma lem2302445 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302444 x (real_of_int y)). Qed.
Lemma lem2302446 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302447 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2302446 x y) (@lem2302445 x y)). Qed.
Lemma lem2302448 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2302447 x y (real_of_int z)). Qed.
Lemma lem2302449 (x : int) (y : int) (z : int) : (term4 x y z) = (term5 x y z).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2302450 (x : int) (y : int) (z : int) : term5 x y z.
Proof. exact (EQ_MP (@lem2302449 x y z) (@lem2302448 x y z)). Qed.
Lemma lem2302452 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302453 : term7 = term8.
Proof. exact (@lem2302452 (NUMERAL 0)). Qed.
Lemma lem2302454 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2302455 : term9 = term10.
Proof. exact (MK_COMB (@lem2302454) (@lem2302453)). Qed.
Lemma lem2302456 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2302457 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2302455) (@lem2302456 x)). Qed.
Lemma lem2302459 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2302460 (x : int) : (term12 x) = (term14 x).
Proof. exact (@lem2302459 term15 x). Qed.
Lemma lem2302461 (x : int) : (term11 x) = (term14 x).
Proof. exact (TRANS (@lem2302457 x) (@lem2302460 x)). Qed.
Lemma lem2302462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2302463 (x : int) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem2302462) (@lem2302461 x)). Qed.
Lemma lem2302465 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2302466 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302467 (x : int) (y : int) : (term20 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem2302466) (@lem2302465 x y)). Qed.
Lemma lem2302469 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2302470 (x : int) (z : int) : (term18 x z) = (term19 x z).
Proof. exact (@lem2302469 x z). Qed.
Lemma lem2302471 (y : int) (x : int) (z : int) : (term22 y x z) = (term23 y x z).
Proof. exact (MK_COMB (@lem2302467 x y) (@lem2302470 x z)). Qed.
Lemma lem2302473 (x : int) (y : int) : (term24 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302474 (y : int) (x : int) (z : int) : (term23 y x z) = (term25 y x z).
Proof. exact (@lem2302473 (int_mul x y) (int_mul x z)). Qed.
Lemma lem2302475 (y : int) (x : int) (z : int) : (term22 y x z) = (term25 y x z).
Proof. exact (TRANS (@lem2302471 y x z) (@lem2302474 y x z)). Qed.
Lemma lem2302476 (y : int) (x : int) (z : int) : (term26 y x z) = (term27 y x z).
Proof. exact (MK_COMB (@lem2302463 x) (@lem2302475 y x z)). Qed.
Lemma lem2302477 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2302478 (y : int) (x : int) (z : int) : (term28 y x z) = (term29 y x z).
Proof. exact (MK_COMB (@lem2302477) (@lem2302476 y x z)). Qed.
Lemma lem2302480 (x : int) (y : int) : (term24 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302481 (y : int) (z : int) : (term24 y z) = (int_le y z).
Proof. exact (@lem2302480 y z). Qed.
Lemma lem2302482 (x : int) (y : int) (z : int) : (term5 x y z) = (term30 x y z).
Proof. exact (MK_COMB (@lem2302478 y x z) (@lem2302481 y z)). Qed.
Lemma lem2302483 (x : int) (y : int) (z : int) : term30 x y z.
Proof. exact (EQ_MP (@lem2302482 x y z) (@lem2302450 x y z)). Qed.
Lemma lem2302484 (x : int) (y : int) : term31 x y.
Proof. exact (fun z : int => @lem2302483 x y z). Qed.
Lemma lem2302485 (x : int) : term32 x.
Proof. exact (fun y : int => @lem2302484 x y). Qed.
Lemma lem2302486 : term33.
Proof. exact (fun x : int => @lem2302485 x). Qed.
