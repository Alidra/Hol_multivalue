Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_ZERO_term_abbrevs.
Require Import REAL_ABS_ZERO_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2300844 (x : int) : term0 x.
Proof. exact (@lem1527966 (real_of_int x)). Qed.
Lemma lem2300845 (x : int) : (term0 x) = (((term1 x) = term2) = ((real_of_int x) = term2)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300846 (x : int) : ((term1 x) = term2) = ((real_of_int x) = term2).
Proof. exact (EQ_MP (@lem2300845 x) (@lem2300844 x)). Qed.
Lemma lem2300848 (x : int) : (term1 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300849 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2300850 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2300849) (@lem2300848 x)). Qed.
Lemma lem2300852 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2300853 : term2 = term7.
Proof. exact (@lem2300852 (NUMERAL 0)). Qed.
Lemma lem2300854 (x : int) : ((term1 x) = term2) = ((term3 x) = term7).
Proof. exact (MK_COMB (@lem2300850 x) (@lem2300853)). Qed.
Lemma lem2300856 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2300857 (x : int) : ((term3 x) = term7) = ((int_abs x) = term8).
Proof. exact (@lem2300856 (int_abs x) term8). Qed.
Lemma lem2300858 (x : int) : ((term1 x) = term2) = ((int_abs x) = term8).
Proof. exact (TRANS (@lem2300854 x) (@lem2300857 x)). Qed.
Lemma lem2300859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2300860 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2300859) (@lem2300858 x)). Qed.
Lemma lem2300862 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2300863 : term2 = term7.
Proof. exact (@lem2300862 (NUMERAL 0)). Qed.
Lemma lem2300864 (x : int) : (term11 x) = (term11 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem2300865 (x : int) : ((real_of_int x) = term2) = ((real_of_int x) = term7).
Proof. exact (MK_COMB (@lem2300864 x) (@lem2300863)). Qed.
Lemma lem2300867 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2300868 (x : int) : ((real_of_int x) = term7) = (x = term8).
Proof. exact (@lem2300867 x term8). Qed.
Lemma lem2300869 (x : int) : ((real_of_int x) = term2) = (x = term8).
Proof. exact (TRANS (@lem2300865 x) (@lem2300868 x)). Qed.
Lemma lem2300870 (x : int) : (((term1 x) = term2) = ((real_of_int x) = term2)) = (((int_abs x) = term8) = (x = term8)).
Proof. exact (MK_COMB (@lem2300860 x) (@lem2300869 x)). Qed.
Lemma lem2300871 (x : int) : ((int_abs x) = term8) = (x = term8).
Proof. exact (EQ_MP (@lem2300870 x) (@lem2300846 x)). Qed.
Lemma lem2300872 : term12.
Proof. exact (fun x : int => @lem2300871 x). Qed.
