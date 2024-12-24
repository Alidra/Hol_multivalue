Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_SIGN2_term_abbrevs.
Require Import REAL_ABS_SIGN2_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2300653 (x : int) : term0 x.
Proof. exact (@lem1542348 (real_of_int x)). Qed.
Lemma lem2300654 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300655 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2300654 x) (@lem2300653 x)). Qed.
Lemma lem2300656 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2300655 x (real_of_int y)). Qed.
Lemma lem2300657 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2300658 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2300657 y x) (@lem2300656 x y)). Qed.
Lemma lem2300660 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300661 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300662 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2300661) (@lem2300660 x y)). Qed.
Lemma lem2300664 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300665 (x : int) (y : int) : (term7 x y) = (term10 x y).
Proof. exact (@lem2300664 (int_sub x y)). Qed.
Lemma lem2300666 (x : int) (y : int) : (term6 x y) = (term10 x y).
Proof. exact (TRANS (@lem2300662 x y) (@lem2300665 x y)). Qed.
Lemma lem2300667 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2300668 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2300667) (@lem2300666 x y)). Qed.
Lemma lem2300670 (x : int) : (term13 x) = (term14 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2300671 (y : int) : (term13 y) = (term14 y).
Proof. exact (@lem2300670 y). Qed.
Lemma lem2300672 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem2300668 x y) (@lem2300671 y)). Qed.
Lemma lem2300674 (x : int) (y : int) : (term17 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300675 (x : int) (y : int) : (term16 x y) = (term18 x y).
Proof. exact (@lem2300674 (term19 x y) (int_neg y)). Qed.
Lemma lem2300676 (x : int) (y : int) : (term15 x y) = (term18 x y).
Proof. exact (TRANS (@lem2300672 x y) (@lem2300675 x y)). Qed.
Lemma lem2300677 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2300678 (x : int) (y : int) : (term20 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem2300677) (@lem2300676 x y)). Qed.
Lemma lem2300680 (n : nat) : (real_of_num n) = (term22 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2300681 : term23 = term24.
Proof. exact (@lem2300680 (NUMERAL 0)). Qed.
Lemma lem2300682 (x : int) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem2300683 (x : int) : (term26 x) = (term27 x).
Proof. exact (MK_COMB (@lem2300682 x) (@lem2300681)). Qed.
Lemma lem2300685 (x : int) (y : int) : (term17 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300686 (x : int) : (term27 x) = (term28 x).
Proof. exact (@lem2300685 x term29). Qed.
Lemma lem2300687 (x : int) : (term26 x) = (term28 x).
Proof. exact (TRANS (@lem2300683 x) (@lem2300686 x)). Qed.
Lemma lem2300688 (y : int) (x : int) : (term3 y x) = (term30 y x).
Proof. exact (MK_COMB (@lem2300678 x y) (@lem2300687 x)). Qed.
Lemma lem2300689 (y : int) (x : int) : term30 y x.
Proof. exact (EQ_MP (@lem2300688 y x) (@lem2300658 y x)). Qed.
Lemma lem2300690 (x : int) : term31 x.
Proof. exact (fun y : int => @lem2300689 y x). Qed.
Lemma lem2300691 : term32.
Proof. exact (fun x : int => @lem2300690 x). Qed.
