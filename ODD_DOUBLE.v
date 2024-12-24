Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ODD_DOUBLE_term_abbrevs.
Require Import EVEN_DOUBLE_spec.
Require Import NOT_ODD_spec.
Require Import thm0_spec.
Require Import thm124616_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem128385 (n : nat) : term0 n.
Proof. exact (@lem128384 n). Qed.
Lemma lem128386 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem128387 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem128386 n) (@lem128385 n)). Qed.
Lemma lem128388 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem128390 (n : nat) : term2 n.
Proof. exact (@lem124808 n). Qed.
Lemma lem128391 (n : nat) : (term2 n) = ((term3 n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem128393 : term4.
Proof. exact (proj2 (@lem124616)). Qed.
Lemma lem128394 (n : nat) : term5 n.
Proof. exact (@lem128393 n). Qed.
Lemma lem128395 (n : nat) : (term5 n) = ((term6 n) = (term3 n)).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem128403 (n : nat) : (term6 n) = (term3 n).
Proof. exact (EQ_MP (@lem128395 n) (@lem128394 n)). Qed.
Lemma lem128404 (n : nat) : (term7 n) = (term8 n).
Proof. exact (@lem128403 (term9 n)). Qed.
Lemma lem128405 : term10 = term11.
Proof. exact (fun_ext (fun n : nat => @lem128404 n)). Qed.
Lemma lem128406 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem128407 : term12 = term13.
Proof. exact (MK_COMB (@lem128406) (@lem128405)). Qed.
Lemma lem128412 : term13 = term12.
Proof. exact (SYM (@lem128407)). Qed.
Lemma lem128418 (n : nat) : (term3 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem128391 n) (@lem128390 n)). Qed.
Lemma lem128419 (n : nat) : (term8 n) = (term1 n).
Proof. exact (@lem128418 (term9 n)). Qed.
Lemma lem128421 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem128388 n) (@lem128387 n)). Qed.
Lemma lem128422 (n : nat) : (term8 n) = True.
Proof. exact (TRANS (@lem128419 n) (@lem128421 n)). Qed.
Lemma lem128423 : term11 = term14.
Proof. exact (fun_ext (fun n : nat => @lem128422 n)). Qed.
Lemma lem128424 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem128425 : term13 = term15.
Proof. exact (MK_COMB (@lem128424) (@lem128423)). Qed.
Lemma lem128427 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem128428 (t : Prop) : (term17 t) = t.
Proof. exact (@lem128427 nat t). Qed.
Lemma lem128429 : term15 = True.
Proof. exact (@lem128428 True). Qed.
Lemma lem128430 : term13 = True.
Proof. exact (TRANS (@lem128425) (@lem128429)). Qed.
Lemma lem128431 : True = term13.
Proof. exact (SYM (@lem128430)). Qed.
Lemma lem128432 : term13.
Proof. exact (EQ_MP (@lem128431) (@lem0)). Qed.
Lemma lem128433 : term12.
Proof. exact (EQ_MP (@lem128412) (@lem128432)). Qed.
