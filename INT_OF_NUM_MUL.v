Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_MUL_term_abbrevs.
Require Import thm1340396_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2307351 (m : nat) : term0 m.
Proof. exact (@lem1340396 m). Qed.
Lemma lem2307352 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2307353 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2307352 m) (@lem2307351 m)). Qed.
Lemma lem2307354 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2307353 m n). Qed.
Lemma lem2307355 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (term4 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2307356 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2307355 m n) (@lem2307354 m n)). Qed.
Lemma lem2307358 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307359 (m : nat) : (real_of_num m) = (term5 m).
Proof. exact (@lem2307358 m). Qed.
Lemma lem2307360 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2307361 (m : nat) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem2307360) (@lem2307359 m)). Qed.
Lemma lem2307363 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307364 (m : nat) (n : nat) : (term3 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem2307361 m) (@lem2307363 n)). Qed.
Lemma lem2307366 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2307367 (m : nat) (n : nat) : (term8 m n) = (term11 m n).
Proof. exact (@lem2307366 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2307368 (m : nat) (n : nat) : (term3 m n) = (term11 m n).
Proof. exact (TRANS (@lem2307364 m n) (@lem2307367 m n)). Qed.
Lemma lem2307369 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2307370 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem2307369) (@lem2307368 m n)). Qed.
Lemma lem2307372 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307373 (m : nat) (n : nat) : (term4 m n) = (term14 m n).
Proof. exact (@lem2307372 (Nat.mul m n)). Qed.
Lemma lem2307374 (m : nat) (n : nat) : ((term3 m n) = (term4 m n)) = ((term11 m n) = (term14 m n)).
Proof. exact (MK_COMB (@lem2307370 m n) (@lem2307373 m n)). Qed.
Lemma lem2307376 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2307377 (m : nat) (n : nat) : ((term11 m n) = (term14 m n)) = ((term15 m n) = (term16 m n)).
Proof. exact (@lem2307376 (term15 m n) (term16 m n)). Qed.
Lemma lem2307378 (m : nat) (n : nat) : ((term3 m n) = (term4 m n)) = ((term15 m n) = (term16 m n)).
Proof. exact (TRANS (@lem2307374 m n) (@lem2307377 m n)). Qed.
Lemma lem2307379 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (EQ_MP (@lem2307378 m n) (@lem2307356 m n)). Qed.
Lemma lem2307380 (m : nat) : term17 m.
Proof. exact (fun n : nat => @lem2307379 m n). Qed.
Lemma lem2307381 : term18.
Proof. exact (fun m : nat => @lem2307380 m). Qed.
