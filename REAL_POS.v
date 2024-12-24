Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POS_term_abbrevs.
Require Import LE_0_spec.
Require Import thm0_spec.
Require Import thm1340282_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1384313 (n : nat) : term0 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem1384314 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1384315 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1384314 n) (@lem1384313 n)). Qed.
Lemma lem1384316 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem1384318 (m : nat) : term2 m.
Proof. exact (@lem1340282 m). Qed.
Lemma lem1384319 (m : nat) : (term2 m) = (term3 m).
Proof. exact (eq_refl (term2 m)). Qed.
Lemma lem1384320 (m : nat) : term3 m.
Proof. exact (EQ_MP (@lem1384319 m) (@lem1384318 m)). Qed.
Lemma lem1384321 (m : nat) (n : nat) : term4 m n.
Proof. exact (@lem1384320 m n). Qed.
Lemma lem1384322 (m : nat) (n : nat) : (term4 m n) = ((term5 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem1384329 (m : nat) (n : nat) : (term5 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1384322 m n) (@lem1384321 m n)). Qed.
Lemma lem1384330 (n : nat) : (term6 n) = (term1 n).
Proof. exact (@lem1384329 (NUMERAL 0) n). Qed.
Lemma lem1384332 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem1384316 n) (@lem1384315 n)). Qed.
Lemma lem1384333 (n : nat) : (term6 n) = True.
Proof. exact (TRANS (@lem1384330 n) (@lem1384332 n)). Qed.
Lemma lem1384334 : term7 = term8.
Proof. exact (fun_ext (fun n : nat => @lem1384333 n)). Qed.
Lemma lem1384335 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1384336 : term9 = term10.
Proof. exact (MK_COMB (@lem1384335) (@lem1384334)). Qed.
Lemma lem1384338 {A : Type'} (t : Prop) : (term11 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1384339 (t : Prop) : (term12 t) = t.
Proof. exact (@lem1384338 nat t). Qed.
Lemma lem1384340 : term10 = True.
Proof. exact (@lem1384339 True). Qed.
Lemma lem1384341 : term9 = True.
Proof. exact (TRANS (@lem1384336) (@lem1384340)). Qed.
Lemma lem1384342 : True = term9.
Proof. exact (SYM (@lem1384341)). Qed.
Lemma lem1384343 : term9.
Proof. exact (EQ_MP (@lem1384342) (@lem0)). Qed.
