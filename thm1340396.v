Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1340396_term_abbrevs.
Require Import TREAL_OF_NUM_MUL_spec.
Require Import thm1337531_spec.
Require Import thm1337536_spec.
Require Import thm1337872_spec.
Require Import thm1337877_spec.
Require Import thm1338112_spec.
Require Import thm1338113_spec.
Lemma lem1340353 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1338113 x y) (@lem1338112 x y)). Qed.
Lemma lem1340354 (m : nat) (n : nat) : (term1 m n) = ((term2 m n) = (term3 m n)).
Proof. exact (@lem1340353 (term4 m n) (term5 m n)). Qed.
Lemma lem1340358 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term6 x1 y1) = (term7 x1 y1).
Proof. exact (EQ_MP (@lem1337877 x1 y1) (@lem1337872 x1 y1)). Qed.
Lemma lem1340359 (m : nat) (n : nat) : (term2 m n) = (term8 m n).
Proof. exact (@lem1340358 (treal_of_num m) (treal_of_num n)). Qed.
Lemma lem1340361 (m : nat) : (term9 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1340362 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1340363 (m : nat) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem1340362) (@lem1340361 m)). Qed.
Lemma lem1340365 (m : nat) : (term9 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1340366 (n : nat) : (term9 n) = (real_of_num n).
Proof. exact (@lem1340365 n). Qed.
Lemma lem1340367 (m : nat) (n : nat) : (term8 m n) = (term12 m n).
Proof. exact (MK_COMB (@lem1340363 m) (@lem1340366 n)). Qed.
Lemma lem1340368 (m : nat) (n : nat) : (term2 m n) = (term12 m n).
Proof. exact (TRANS (@lem1340359 m n) (@lem1340367 m n)). Qed.
Lemma lem1340369 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1340370 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem1340369) (@lem1340368 m n)). Qed.
Lemma lem1340372 (m : nat) : (term9 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1340373 (m : nat) (n : nat) : (term3 m n) = (term15 m n).
Proof. exact (@lem1340372 (Nat.mul m n)). Qed.
Lemma lem1340374 (m : nat) (n : nat) : ((term2 m n) = (term3 m n)) = ((term12 m n) = (term15 m n)).
Proof. exact (MK_COMB (@lem1340370 m n) (@lem1340373 m n)). Qed.
Lemma lem1340377 (m : nat) (n : nat) : (term1 m n) = ((term12 m n) = (term15 m n)).
Proof. exact (TRANS (@lem1340354 m n) (@lem1340374 m n)). Qed.
Lemma lem1340378 (m : nat) : (term16 m) = (term17 m).
Proof. exact (fun_ext (fun n : nat => @lem1340377 m n)). Qed.
Lemma lem1340379 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1340380 (m : nat) : (term18 m) = (term19 m).
Proof. exact (MK_COMB (@lem1340379) (@lem1340378 m)). Qed.
Lemma lem1340387 : term20 = term21.
Proof. exact (fun_ext (fun m : nat => @lem1340380 m)). Qed.
Lemma lem1340388 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1340389 : term22 = term23.
Proof. exact (MK_COMB (@lem1340388) (@lem1340387)). Qed.
Lemma lem1340396 : term23.
Proof. exact (EQ_MP (@lem1340389) (@lem1327326)). Qed.
