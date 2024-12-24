Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_NEGTOTAL_term_abbrevs.
Require Import REAL_LT_NEGTOTAL_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2304592 (x : int) : term0 x.
Proof. exact (@lem1499257 (real_of_int x)). Qed.
Lemma lem2304593 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304594 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304593 x) (@lem2304592 x)). Qed.
Lemma lem2304596 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304597 : term3 = term4.
Proof. exact (@lem2304596 (NUMERAL 0)). Qed.
Lemma lem2304598 (x : int) : (term5 x) = (term5 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem2304599 (x : int) : ((real_of_int x) = term3) = ((real_of_int x) = term4).
Proof. exact (MK_COMB (@lem2304598 x) (@lem2304597)). Qed.
Lemma lem2304601 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2304602 (x : int) : ((real_of_int x) = term4) = (x = term6).
Proof. exact (@lem2304601 x term6). Qed.
Lemma lem2304603 (x : int) : ((real_of_int x) = term3) = (x = term6).
Proof. exact (TRANS (@lem2304599 x) (@lem2304602 x)). Qed.
Lemma lem2304604 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2304605 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2304604) (@lem2304603 x)). Qed.
Lemma lem2304607 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304608 : term3 = term4.
Proof. exact (@lem2304607 (NUMERAL 0)). Qed.
Lemma lem2304609 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304610 : term9 = term10.
Proof. exact (MK_COMB (@lem2304609) (@lem2304608)). Qed.
Lemma lem2304611 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2304612 (x : int) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem2304610) (@lem2304611 x)). Qed.
Lemma lem2304614 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304615 (x : int) : (term12 x) = (term14 x).
Proof. exact (@lem2304614 term6 x). Qed.
Lemma lem2304616 (x : int) : (term11 x) = (term14 x).
Proof. exact (TRANS (@lem2304612 x) (@lem2304615 x)). Qed.
Lemma lem2304617 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2304618 (x : int) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem2304617) (@lem2304616 x)). Qed.
Lemma lem2304620 (n : nat) : (real_of_num n) = (term2 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304621 : term3 = term4.
Proof. exact (@lem2304620 (NUMERAL 0)). Qed.
Lemma lem2304622 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304623 : term9 = term10.
Proof. exact (MK_COMB (@lem2304622) (@lem2304621)). Qed.
Lemma lem2304625 (x : int) : (term17 x) = (term18 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2304626 (x : int) : (term19 x) = (term20 x).
Proof. exact (MK_COMB (@lem2304623) (@lem2304625 x)). Qed.
Lemma lem2304628 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304629 (x : int) : (term20 x) = (term21 x).
Proof. exact (@lem2304628 term6 (int_neg x)). Qed.
Lemma lem2304630 (x : int) : (term19 x) = (term21 x).
Proof. exact (TRANS (@lem2304626 x) (@lem2304629 x)). Qed.
Lemma lem2304631 (x : int) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem2304618 x) (@lem2304630 x)). Qed.
Lemma lem2304632 (x : int) : (term1 x) = (term24 x).
Proof. exact (MK_COMB (@lem2304605 x) (@lem2304631 x)). Qed.
Lemma lem2304633 (x : int) : term24 x.
Proof. exact (EQ_MP (@lem2304632 x) (@lem2304594 x)). Qed.
Lemma lem2304634 : term25.
Proof. exact (fun x : int => @lem2304633 x). Qed.
