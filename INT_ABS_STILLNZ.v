Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_STILLNZ_term_abbrevs.
Require Import REAL_ABS_STILLNZ_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2300692 (x : int) : term0 x.
Proof. exact (@lem1540414 (real_of_int x)). Qed.
Lemma lem2300693 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300694 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2300693 x) (@lem2300692 x)). Qed.
Lemma lem2300695 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2300694 x (real_of_int y)). Qed.
Lemma lem2300696 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2300697 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2300696 y x) (@lem2300695 x y)). Qed.
Lemma lem2300699 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2300700 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300701 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2300700) (@lem2300699 x y)). Qed.
Lemma lem2300703 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300704 (x : int) (y : int) : (term7 x y) = (term10 x y).
Proof. exact (@lem2300703 (int_sub x y)). Qed.
Lemma lem2300705 (x : int) (y : int) : (term6 x y) = (term10 x y).
Proof. exact (TRANS (@lem2300701 x y) (@lem2300704 x y)). Qed.
Lemma lem2300706 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2300707 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2300706) (@lem2300705 x y)). Qed.
Lemma lem2300709 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300710 (y : int) : (term8 y) = (term9 y).
Proof. exact (@lem2300709 y). Qed.
Lemma lem2300711 (x : int) (y : int) : (term13 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem2300707 x y) (@lem2300710 y)). Qed.
Lemma lem2300713 (x : int) (y : int) : (term15 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300714 (x : int) (y : int) : (term14 x y) = (term16 x y).
Proof. exact (@lem2300713 (term17 x y) (int_abs y)). Qed.
Lemma lem2300715 (x : int) (y : int) : (term13 x y) = (term16 x y).
Proof. exact (TRANS (@lem2300711 x y) (@lem2300714 x y)). Qed.
Lemma lem2300716 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2300717 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (MK_COMB (@lem2300716) (@lem2300715 x y)). Qed.
Lemma lem2300719 (n : nat) : (real_of_num n) = (term20 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2300720 : term21 = term22.
Proof. exact (@lem2300719 (NUMERAL 0)). Qed.
Lemma lem2300721 (x : int) : (term23 x) = (term23 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem2300722 (x : int) : ((real_of_int x) = term21) = ((real_of_int x) = term22).
Proof. exact (MK_COMB (@lem2300721 x) (@lem2300720)). Qed.
Lemma lem2300724 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2300725 (x : int) : ((real_of_int x) = term22) = (x = term24).
Proof. exact (@lem2300724 x term24). Qed.
Lemma lem2300726 (x : int) : ((real_of_int x) = term21) = (x = term24).
Proof. exact (TRANS (@lem2300722 x) (@lem2300725 x)). Qed.
Lemma lem2300727 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2300728 (x : int) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem2300727) (@lem2300726 x)). Qed.
Lemma lem2300729 (y : int) (x : int) : (term3 y x) = (term27 y x).
Proof. exact (MK_COMB (@lem2300717 x y) (@lem2300728 x)). Qed.
Lemma lem2300730 (y : int) (x : int) : term27 y x.
Proof. exact (EQ_MP (@lem2300729 y x) (@lem2300697 y x)). Qed.
Lemma lem2300731 (x : int) : term28 x.
Proof. exact (fun y : int => @lem2300730 y x). Qed.
Lemma lem2300732 : term29.
Proof. exact (fun x : int => @lem2300731 x). Qed.
