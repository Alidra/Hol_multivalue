Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_LE_term_abbrevs.
Require Import thm1340282_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2307198 (m : nat) : term0 m.
Proof. exact (@lem1340282 m). Qed.
Lemma lem2307199 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2307200 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2307199 m) (@lem2307198 m)). Qed.
Lemma lem2307201 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2307200 m n). Qed.
Lemma lem2307202 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2307203 (m : nat) (n : nat) : (term3 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem2307202 m n) (@lem2307201 m n)). Qed.
Lemma lem2307205 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307206 (m : nat) : (real_of_num m) = (term4 m).
Proof. exact (@lem2307205 m). Qed.
Lemma lem2307207 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2307208 (m : nat) : (term5 m) = (term6 m).
Proof. exact (MK_COMB (@lem2307207) (@lem2307206 m)). Qed.
Lemma lem2307210 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2307211 (m : nat) (n : nat) : (term3 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem2307208 m) (@lem2307210 n)). Qed.
Lemma lem2307213 (x : int) (y : int) : (term8 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2307214 (m : nat) (n : nat) : (term7 m n) = (term9 m n).
Proof. exact (@lem2307213 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2307215 (m : nat) (n : nat) : (term3 m n) = (term9 m n).
Proof. exact (TRANS (@lem2307211 m n) (@lem2307214 m n)). Qed.
Lemma lem2307216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2307217 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (MK_COMB (@lem2307216) (@lem2307215 m n)). Qed.
Lemma lem2307218 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem2307219 (m : nat) (n : nat) : ((term3 m n) = (Peano.le m n)) = ((term9 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem2307217 m n) (@lem2307218 m n)). Qed.
Lemma lem2307220 (m : nat) (n : nat) : (term9 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem2307219 m n) (@lem2307203 m n)). Qed.
Lemma lem2307221 (m : nat) : term12 m.
Proof. exact (fun n : nat => @lem2307220 m n). Qed.
Lemma lem2307222 : term13.
Proof. exact (fun m : nat => @lem2307221 m). Qed.
