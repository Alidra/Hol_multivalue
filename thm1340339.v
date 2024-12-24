Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1340339_term_abbrevs.
Require Import TREAL_OF_NUM_ADD_spec.
Require Import thm1337531_spec.
Require Import thm1337536_spec.
Require Import thm1337747_spec.
Require Import thm1337752_spec.
Require Import thm1338112_spec.
Require Import thm1338113_spec.
Lemma lem1340296 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1338113 x y) (@lem1338112 x y)). Qed.
Lemma lem1340297 (m : nat) (n : nat) : (term1 m n) = ((term2 m n) = (term3 m n)).
Proof. exact (@lem1340296 (term4 m n) (term5 m n)). Qed.
Lemma lem1340301 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (term6 x1 y1) = (term7 x1 y1).
Proof. exact (EQ_MP (@lem1337752 x1 y1) (@lem1337747 x1 y1)). Qed.
Lemma lem1340302 (m : nat) (n : nat) : (term2 m n) = (term8 m n).
Proof. exact (@lem1340301 (treal_of_num m) (treal_of_num n)). Qed.
Lemma lem1340304 (m : nat) : (term9 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1340305 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1340306 (m : nat) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem1340305) (@lem1340304 m)). Qed.
Lemma lem1340308 (m : nat) : (term9 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1340309 (n : nat) : (term9 n) = (real_of_num n).
Proof. exact (@lem1340308 n). Qed.
Lemma lem1340310 (m : nat) (n : nat) : (term8 m n) = (term12 m n).
Proof. exact (MK_COMB (@lem1340306 m) (@lem1340309 n)). Qed.
Lemma lem1340311 (m : nat) (n : nat) : (term2 m n) = (term12 m n).
Proof. exact (TRANS (@lem1340302 m n) (@lem1340310 m n)). Qed.
Lemma lem1340312 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1340313 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem1340312) (@lem1340311 m n)). Qed.
Lemma lem1340315 (m : nat) : (term9 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1340316 (m : nat) (n : nat) : (term3 m n) = (term15 m n).
Proof. exact (@lem1340315 (Nat.add m n)). Qed.
Lemma lem1340317 (m : nat) (n : nat) : ((term2 m n) = (term3 m n)) = ((term12 m n) = (term15 m n)).
Proof. exact (MK_COMB (@lem1340313 m n) (@lem1340316 m n)). Qed.
Lemma lem1340320 (m : nat) (n : nat) : (term1 m n) = ((term12 m n) = (term15 m n)).
Proof. exact (TRANS (@lem1340297 m n) (@lem1340317 m n)). Qed.
Lemma lem1340321 (m : nat) : (term16 m) = (term17 m).
Proof. exact (fun_ext (fun n : nat => @lem1340320 m n)). Qed.
Lemma lem1340322 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1340323 (m : nat) : (term18 m) = (term19 m).
Proof. exact (MK_COMB (@lem1340322) (@lem1340321 m)). Qed.
Lemma lem1340330 : term20 = term21.
Proof. exact (fun_ext (fun m : nat => @lem1340323 m)). Qed.
Lemma lem1340331 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1340332 : term22 = term23.
Proof. exact (MK_COMB (@lem1340331) (@lem1340330)). Qed.
Lemma lem1340339 : term23.
Proof. exact (EQ_MP (@lem1340332) (@lem1327157)). Qed.
