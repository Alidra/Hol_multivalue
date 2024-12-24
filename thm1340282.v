Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1340282_term_abbrevs.
Require Import TREAL_OF_NUM_LE_spec.
Require Import thm1337531_spec.
Require Import thm1337536_spec.
Require Import thm1337985_spec.
Require Import thm1337990_spec.
Lemma lem1340247 (x1 : prod hreal hreal) (y1 : prod hreal hreal) : (treal_le x1 y1) = (term0 x1 y1).
Proof. exact (EQ_MP (@lem1337990 x1 y1) (@lem1337985 x1 y1)). Qed.
Lemma lem1340248 (m : nat) (n : nat) : (term1 m n) = (term2 m n).
Proof. exact (@lem1340247 (treal_of_num m) (treal_of_num n)). Qed.
Lemma lem1340250 (m : nat) : (term3 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1340251 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1340252 (m : nat) : (term4 m) = (term5 m).
Proof. exact (MK_COMB (@lem1340251) (@lem1340250 m)). Qed.
Lemma lem1340254 (m : nat) : (term3 m) = (real_of_num m).
Proof. exact (EQ_MP (@lem1337536 m) (@lem1337531 m)). Qed.
Lemma lem1340255 (n : nat) : (term3 n) = (real_of_num n).
Proof. exact (@lem1340254 n). Qed.
Lemma lem1340256 (m : nat) (n : nat) : (term2 m n) = (term6 m n).
Proof. exact (MK_COMB (@lem1340252 m) (@lem1340255 n)). Qed.
Lemma lem1340257 (m : nat) (n : nat) : (term1 m n) = (term6 m n).
Proof. exact (TRANS (@lem1340248 m n) (@lem1340256 m n)). Qed.
Lemma lem1340258 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1340259 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem1340258) (@lem1340257 m n)). Qed.
Lemma lem1340260 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem1340261 (m : nat) (n : nat) : ((term1 m n) = (Peano.le m n)) = ((term6 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem1340259 m n) (@lem1340260 m n)). Qed.
Lemma lem1340264 (m : nat) : (term9 m) = (term10 m).
Proof. exact (fun_ext (fun n : nat => @lem1340261 m n)). Qed.
Lemma lem1340265 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1340266 (m : nat) : (term11 m) = (term12 m).
Proof. exact (MK_COMB (@lem1340265) (@lem1340264 m)). Qed.
Lemma lem1340273 : term13 = term14.
Proof. exact (fun_ext (fun m : nat => @lem1340266 m)). Qed.
Lemma lem1340274 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1340275 : term15 = term16.
Proof. exact (MK_COMB (@lem1340274) (@lem1340273)). Qed.
Lemma lem1340282 : term16.
Proof. exact (EQ_MP (@lem1340275) (@lem1327029)). Qed.
