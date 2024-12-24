Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EQ_ADD_LCANCEL_0_term_abbrevs.
Require Import REAL_EQ_ADD_LCANCEL_0_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301515 (x : int) : term0 x.
Proof. exact (@lem1488302 (real_of_int x)). Qed.
Lemma lem2301516 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301517 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301516 x) (@lem2301515 x)). Qed.
Lemma lem2301518 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301517 x (real_of_int y)). Qed.
Lemma lem2301519 (x : int) (y : int) : (term2 x y) = (((term3 x y) = (real_of_int x)) = ((real_of_int y) = term4)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301520 (x : int) (y : int) : ((term3 x y) = (real_of_int x)) = ((real_of_int y) = term4).
Proof. exact (EQ_MP (@lem2301519 x y) (@lem2301518 x y)). Qed.
Lemma lem2301522 (x : int) (y : int) : (term3 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301523 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301524 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2301523) (@lem2301522 x y)). Qed.
Lemma lem2301525 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2301526 (y : int) (x : int) : ((term3 x y) = (real_of_int x)) = ((term5 x y) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2301524 x y) (@lem2301525 x)). Qed.
Lemma lem2301528 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301529 (y : int) (x : int) : ((term5 x y) = (real_of_int x)) = ((int_add x y) = x).
Proof. exact (@lem2301528 (int_add x y) x). Qed.
Lemma lem2301530 (y : int) (x : int) : ((term3 x y) = (real_of_int x)) = ((int_add x y) = x).
Proof. exact (TRANS (@lem2301526 y x) (@lem2301529 y x)). Qed.
Lemma lem2301531 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2301532 (y : int) (x : int) : (term8 y x) = (term9 y x).
Proof. exact (MK_COMB (@lem2301531) (@lem2301530 y x)). Qed.
Lemma lem2301534 (n : nat) : (real_of_num n) = (term10 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2301535 : term4 = term11.
Proof. exact (@lem2301534 (NUMERAL 0)). Qed.
Lemma lem2301536 (y : int) : (term12 y) = (term12 y).
Proof. exact (eq_refl (term12 y)). Qed.
Lemma lem2301537 (y : int) : ((real_of_int y) = term4) = ((real_of_int y) = term11).
Proof. exact (MK_COMB (@lem2301536 y) (@lem2301535)). Qed.
Lemma lem2301539 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301540 (y : int) : ((real_of_int y) = term11) = (y = term13).
Proof. exact (@lem2301539 y term13). Qed.
Lemma lem2301541 (y : int) : ((real_of_int y) = term4) = (y = term13).
Proof. exact (TRANS (@lem2301537 y) (@lem2301540 y)). Qed.
Lemma lem2301542 (x : int) (y : int) : (((term3 x y) = (real_of_int x)) = ((real_of_int y) = term4)) = (((int_add x y) = x) = (y = term13)).
Proof. exact (MK_COMB (@lem2301532 y x) (@lem2301541 y)). Qed.
Lemma lem2301543 (x : int) (y : int) : ((int_add x y) = x) = (y = term13).
Proof. exact (EQ_MP (@lem2301542 x y) (@lem2301520 x y)). Qed.
Lemma lem2301544 (x : int) : term14 x.
Proof. exact (fun y : int => @lem2301543 x y). Qed.
Lemma lem2301545 : term15.
Proof. exact (fun x : int => @lem2301544 x). Qed.
