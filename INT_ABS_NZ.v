Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_NZ_term_abbrevs.
Require Import REAL_ABS_NZ_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2300475 (x : int) : term0 x.
Proof. exact (@lem1534492 (real_of_int x)). Qed.
Lemma lem2300476 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300477 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2300476 x) (@lem2300475 x)). Qed.
Lemma lem2300479 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2300480 : term4 = term5.
Proof. exact (@lem2300479 (NUMERAL 0)). Qed.
Lemma lem2300481 (x : int) : (term6 x) = (term6 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem2300482 (x : int) : ((real_of_int x) = term4) = ((real_of_int x) = term5).
Proof. exact (MK_COMB (@lem2300481 x) (@lem2300480)). Qed.
Lemma lem2300484 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2300485 (x : int) : ((real_of_int x) = term5) = (x = term7).
Proof. exact (@lem2300484 x term7). Qed.
Lemma lem2300486 (x : int) : ((real_of_int x) = term4) = (x = term7).
Proof. exact (TRANS (@lem2300482 x) (@lem2300485 x)). Qed.
Lemma lem2300487 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2300488 (x : int) : (term1 x) = (term8 x).
Proof. exact (MK_COMB (@lem2300487) (@lem2300486 x)). Qed.
Lemma lem2300489 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2300490 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2300489) (@lem2300488 x)). Qed.
Lemma lem2300492 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2300493 : term4 = term5.
Proof. exact (@lem2300492 (NUMERAL 0)). Qed.
Lemma lem2300494 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2300495 : term11 = term12.
Proof. exact (MK_COMB (@lem2300494) (@lem2300493)). Qed.
Lemma lem2300497 (x : int) : (term13 x) = (term14 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300498 (x : int) : (term2 x) = (term15 x).
Proof. exact (MK_COMB (@lem2300495) (@lem2300497 x)). Qed.
Lemma lem2300500 (x : int) (y : int) : (term16 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2300501 (x : int) : (term15 x) = (term17 x).
Proof. exact (@lem2300500 term7 (int_abs x)). Qed.
Lemma lem2300502 (x : int) : (term2 x) = (term17 x).
Proof. exact (TRANS (@lem2300498 x) (@lem2300501 x)). Qed.
Lemma lem2300503 (x : int) : ((term1 x) = (term2 x)) = ((term8 x) = (term17 x)).
Proof. exact (MK_COMB (@lem2300490 x) (@lem2300502 x)). Qed.
Lemma lem2300504 (x : int) : (term8 x) = (term17 x).
Proof. exact (EQ_MP (@lem2300503 x) (@lem2300477 x)). Qed.
Lemma lem2300505 : term18.
Proof. exact (fun x : int => @lem2300504 x). Qed.
