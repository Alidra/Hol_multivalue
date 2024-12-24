Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1340231_term_abbrevs.
Require Import TREAL_OF_NUM_EQ_spec.
Require Import thm1337531_spec.
Require Import thm1337536_spec.
Require Import thm1338112_spec.
Require Import thm1338113_spec.
Lemma lem1340190 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1338113 x y) (@lem1338112 x y)). Qed.
Lemma lem1340191 (m : nat) (n : nat) : (term1 m n) = ((term2 m) = (term2 n)).
Proof. exact (@lem1340190 (treal_of_num m) (treal_of_num n)). Qed.
Lemma lem1340195 (m : nat) : (term2 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1340196 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1340197 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem1340196) (@lem1340195 m)). Qed.
Lemma lem1340199 (m : nat) : (term2 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1340200 (n : nat) : (term2 n) = (real_of_num n).
Proof. exact (@lem1340199 n). Qed.
Lemma lem1340201 (m : nat) (n : nat) : ((term2 m) = (term2 n)) = ((real_of_num m) = (real_of_num n)).
Proof. exact (MK_COMB (@lem1340197 m) (@lem1340200 n)). Qed.
Lemma lem1340204 (m : nat) (n : nat) : (term1 m n) = ((real_of_num m) = (real_of_num n)).
Proof. exact (TRANS (@lem1340191 m n) (@lem1340201 m n)). Qed.
Lemma lem1340205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1340206 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (MK_COMB (@lem1340205) (@lem1340204 m n)). Qed.
Lemma lem1340209 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem1340210 (m : nat) (n : nat) : ((term1 m n) = (m = n)) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (MK_COMB (@lem1340206 m n) (@lem1340209 m n)). Qed.
Lemma lem1340213 (m : nat) : (term7 m) = (term8 m).
Proof. exact (fun_ext (fun n : nat => @lem1340210 m n)). Qed.
Lemma lem1340214 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1340215 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem1340214) (@lem1340213 m)). Qed.
Lemma lem1340222 : term11 = term12.
Proof. exact (fun_ext (fun m : nat => @lem1340215 m)). Qed.
Lemma lem1340223 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1340224 : term13 = term14.
Proof. exact (MK_COMB (@lem1340223) (@lem1340222)). Qed.
Lemma lem1340231 : term14.
Proof. exact (EQ_MP (@lem1340224) (@lem1326943)). Qed.
