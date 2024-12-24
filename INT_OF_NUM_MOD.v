Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_MOD_term_abbrevs.
Require Import REAL_OF_NUM_MOD_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307310 (m : nat) : term0 m.
Proof. exact (@lem1669963 m). Qed.
Lemma lem2307311 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2307312 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2307311 m) (@lem2307310 m)). Qed.
Lemma lem2307313 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2307312 m n). Qed.
Lemma lem2307314 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (term4 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2307315 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2307314 m n) (@lem2307313 m n)). Qed.
Lemma lem2307317 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307318 (m : nat) (n : nat) : (term3 m n) = (term6 m n).
Proof. exact (@lem2307317 (Nat.modulo m n)). Qed.
Lemma lem2307319 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307320 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem2307319) (@lem2307318 m n)). Qed.
Lemma lem2307322 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307323 (m : nat) : (real_of_num m) = (term5 m).
Proof. exact (@lem2307322 m). Qed.
Lemma lem2307324 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2307325 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem2307324) (@lem2307323 m)). Qed.
Lemma lem2307327 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307328 (m : nat) (n : nat) : (term11 m n) = (term12 m n).
Proof. exact (@lem2307327 (Nat.div m n)). Qed.
Lemma lem2307329 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2307330 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem2307329) (@lem2307328 m n)). Qed.
Lemma lem2307332 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307333 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (MK_COMB (@lem2307330 m n) (@lem2307332 n)). Qed.
Lemma lem2307335 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2307336 (m : nat) (n : nat) : (term16 m n) = (term19 m n).
Proof. exact (@lem2307335 (term20 m n) (int_of_num n)). Qed.
Lemma lem2307337 (m : nat) (n : nat) : (term15 m n) = (term19 m n).
Proof. exact (TRANS (@lem2307333 m n) (@lem2307336 m n)). Qed.
Lemma lem2307338 (m : nat) (n : nat) : (term4 m n) = (term21 m n).
Proof. exact (MK_COMB (@lem2307325 m) (@lem2307337 m n)). Qed.
Lemma lem2307340 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2307341 (m : nat) (n : nat) : (term21 m n) = (term24 m n).
Proof. exact (@lem2307340 (int_of_num m) (term25 m n)). Qed.
Lemma lem2307342 (m : nat) (n : nat) : (term4 m n) = (term24 m n).
Proof. exact (TRANS (@lem2307338 m n) (@lem2307341 m n)). Qed.
Lemma lem2307343 (m : nat) (n : nat) : ((term3 m n) = (term4 m n)) = ((term6 m n) = (term24 m n)).
Proof. exact (MK_COMB (@lem2307320 m n) (@lem2307342 m n)). Qed.
Lemma lem2307345 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307346 (m : nat) (n : nat) : ((term6 m n) = (term24 m n)) = ((term26 m n) = (term27 m n)).
Proof. exact (@lem2307345 (term26 m n) (term27 m n)). Qed.
Lemma lem2307347 (m : nat) (n : nat) : ((term3 m n) = (term4 m n)) = ((term26 m n) = (term27 m n)).
Proof. exact (TRANS (@lem2307343 m n) (@lem2307346 m n)). Qed.
Lemma lem2307348 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (EQ_MP (@lem2307347 m n) (@lem2307315 m n)). Qed.
Lemma lem2307349 (m : nat) : term28 m.
Proof. exact (fun n : nat => @lem2307348 m n). Qed.
Lemma lem2307350 : term29.
Proof. exact (fun m : nat => @lem2307349 m). Qed.
