Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_REFL_term_abbrevs.
Require Import REAL_ABS_REFL_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2300557 (x : int) : term0 x.
Proof. exact (@lem1536892 (real_of_int x)). Qed.
Lemma lem2300558 (x : int) : (term0 x) = (((term1 x) = (real_of_int x)) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300559 (x : int) : ((term1 x) = (real_of_int x)) = (term2 x).
Proof. exact (EQ_MP (@lem2300558 x) (@lem2300557 x)). Qed.
Lemma lem2300561 (x : int) : (term1 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300562 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2300563 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2300562) (@lem2300561 x)). Qed.
Lemma lem2300564 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2300565 (x : int) : ((term1 x) = (real_of_int x)) = ((term3 x) = (real_of_int x)).
Proof. exact (MK_COMB (@lem2300563 x) (@lem2300564 x)). Qed.
Lemma lem2300567 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2300568 (x : int) : ((term3 x) = (real_of_int x)) = ((int_abs x) = x).
Proof. exact (@lem2300567 (int_abs x) x). Qed.
Lemma lem2300569 (x : int) : ((term1 x) = (real_of_int x)) = ((int_abs x) = x).
Proof. exact (TRANS (@lem2300565 x) (@lem2300568 x)). Qed.
Lemma lem2300570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2300571 (x : int) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem2300570) (@lem2300569 x)). Qed.
Lemma lem2300573 (n : nat) : (real_of_num n) = (term8 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2300574 : term9 = term10.
Proof. exact (@lem2300573 (NUMERAL 0)). Qed.
Lemma lem2300575 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2300576 : term11 = term12.
Proof. exact (MK_COMB (@lem2300575) (@lem2300574)). Qed.
Lemma lem2300577 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2300578 (x : int) : (term2 x) = (term13 x).
Proof. exact (MK_COMB (@lem2300576) (@lem2300577 x)). Qed.
Lemma lem2300580 (x : int) (y : int) : (term14 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2300581 (x : int) : (term13 x) = (term15 x).
Proof. exact (@lem2300580 term16 x). Qed.
Lemma lem2300582 (x : int) : (term2 x) = (term15 x).
Proof. exact (TRANS (@lem2300578 x) (@lem2300581 x)). Qed.
Lemma lem2300583 (x : int) : (((term1 x) = (real_of_int x)) = (term2 x)) = (((int_abs x) = x) = (term15 x)).
Proof. exact (MK_COMB (@lem2300571 x) (@lem2300582 x)). Qed.
Lemma lem2300584 (x : int) : ((int_abs x) = x) = (term15 x).
Proof. exact (EQ_MP (@lem2300583 x) (@lem2300559 x)). Qed.
Lemma lem2300585 : term17.
Proof. exact (fun x : int => @lem2300584 x). Qed.
