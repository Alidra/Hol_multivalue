Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POS_NZ_term_abbrevs.
Require Import REAL_LT_IMP_NZ_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307556 (x : int) : term0 x.
Proof. exact (@lem1523977 (real_of_int x)). Qed.
Lemma lem2307557 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2307558 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2307557 x) (@lem2307556 x)). Qed.
Lemma lem2307560 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307561 : term3 = term4.
Proof. exact (@lem2307560 (NUMERAL 0)). Qed.
Lemma lem2307562 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2307563 : term5 = term6.
Proof. exact (MK_COMB (@lem2307562) (@lem2307561)). Qed.
Lemma lem2307564 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2307565 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2307563) (@lem2307564 x)). Qed.
Lemma lem2307567 (x : int) (y : int) : (term9 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2307568 (x : int) : (term8 x) = (term10 x).
Proof. exact (@lem2307567 term11 x). Qed.
Lemma lem2307569 (x : int) : (term7 x) = (term10 x).
Proof. exact (TRANS (@lem2307565 x) (@lem2307568 x)). Qed.
Lemma lem2307570 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2307571 (x : int) : (term12 x) = (term13 x).
Proof. exact (MK_COMB (@lem2307570) (@lem2307569 x)). Qed.
Lemma lem2307573 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307574 : term3 = term4.
Proof. exact (@lem2307573 (NUMERAL 0)). Qed.
Lemma lem2307575 (x : int) : (term14 x) = (term14 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem2307576 (x : int) : ((real_of_int x) = term3) = ((real_of_int x) = term4).
Proof. exact (MK_COMB (@lem2307575 x) (@lem2307574)). Qed.
Lemma lem2307578 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307579 (x : int) : ((real_of_int x) = term4) = (x = term11).
Proof. exact (@lem2307578 x term11). Qed.
Lemma lem2307580 (x : int) : ((real_of_int x) = term3) = (x = term11).
Proof. exact (TRANS (@lem2307576 x) (@lem2307579 x)). Qed.
Lemma lem2307581 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2307582 (x : int) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem2307581) (@lem2307580 x)). Qed.
Lemma lem2307583 (x : int) : (term1 x) = (term17 x).
Proof. exact (MK_COMB (@lem2307571 x) (@lem2307582 x)). Qed.
Lemma lem2307584 (x : int) : term17 x.
Proof. exact (EQ_MP (@lem2307583 x) (@lem2307558 x)). Qed.
Lemma lem2307585 : term18.
Proof. exact (fun x : int => @lem2307584 x). Qed.
