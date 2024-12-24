Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_SIGN_term_abbrevs.
Require Import REAL_ABS_SIGN_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2300614 (x : int) : term0 x.
Proof. exact (@lem1541862 (real_of_int x)). Qed.
Lemma lem2300615 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300616 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2300615 x) (@lem2300614 x)). Qed.
Lemma lem2300617 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2300616 x (real_of_int y)). Qed.
Lemma lem2300618 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2300619 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2300618 y x) (@lem2300617 x y)). Qed.
Lemma lem2300621 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300622 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300623 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2300622) (@lem2300621 x y)). Qed.
Lemma lem2300625 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300626 (x : int) (y : int) : (term7 x y) = (term10 x y).
Proof. exact (@lem2300625 (int_sub x y)). Qed.
Lemma lem2300627 (x : int) (y : int) : (term6 x y) = (term10 x y).
Proof. exact (TRANS (@lem2300623 x y) (@lem2300626 x y)). Qed.
Lemma lem2300628 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2300629 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2300628) (@lem2300627 x y)). Qed.
Lemma lem2300630 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2300631 (x : int) (y : int) : (term13 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem2300629 x y) (@lem2300630 y)). Qed.
Lemma lem2300633 (x : int) (y : int) : (term15 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300634 (x : int) (y : int) : (term14 x y) = (term16 x y).
Proof. exact (@lem2300633 (term17 x y) y). Qed.
Lemma lem2300635 (x : int) (y : int) : (term13 x y) = (term16 x y).
Proof. exact (TRANS (@lem2300631 x y) (@lem2300634 x y)). Qed.
Lemma lem2300636 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2300637 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (MK_COMB (@lem2300636) (@lem2300635 x y)). Qed.
Lemma lem2300639 (n : nat) : (real_of_num n) = (term20 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2300640 : term21 = term22.
Proof. exact (@lem2300639 (NUMERAL 0)). Qed.
Lemma lem2300641 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2300642 : term23 = term24.
Proof. exact (MK_COMB (@lem2300641) (@lem2300640)). Qed.
Lemma lem2300643 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2300644 (x : int) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem2300642) (@lem2300643 x)). Qed.
Lemma lem2300646 (x : int) (y : int) : (term15 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300647 (x : int) : (term26 x) = (term27 x).
Proof. exact (@lem2300646 term28 x). Qed.
Lemma lem2300648 (x : int) : (term25 x) = (term27 x).
Proof. exact (TRANS (@lem2300644 x) (@lem2300647 x)). Qed.
Lemma lem2300649 (y : int) (x : int) : (term3 y x) = (term29 y x).
Proof. exact (MK_COMB (@lem2300637 x y) (@lem2300648 x)). Qed.
Lemma lem2300650 (y : int) (x : int) : term29 y x.
Proof. exact (EQ_MP (@lem2300649 y x) (@lem2300619 y x)). Qed.
Lemma lem2300651 (x : int) : term30 x.
Proof. exact (fun y : int => @lem2300650 y x). Qed.
Lemma lem2300652 : term31.
Proof. exact (fun x : int => @lem2300651 x). Qed.
