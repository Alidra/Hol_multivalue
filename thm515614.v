Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm515614_term_abbrevs.
Require Import MULT_CLAUSES_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Lemma lem515546 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem515547 : (NUMERAL 0) = 0.
Proof. exact (@lem515546 0). Qed.
Lemma lem515548 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem515549 : term0 = (Nat.mul 0).
Proof. exact (MK_COMB (@lem515548) (@lem515547)). Qed.
Lemma lem515550 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem515551 (n : nat) : (term1 n) = (Nat.mul 0 n).
Proof. exact (MK_COMB (@lem515549) (@lem515550 n)). Qed.
Lemma lem515552 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515553 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem515552) (@lem515551 n)). Qed.
Lemma lem515555 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem515556 : (NUMERAL 0) = 0.
Proof. exact (@lem515555 0). Qed.
Lemma lem515557 (n : nat) : ((term1 n) = (NUMERAL 0)) = ((Nat.mul 0 n) = 0).
Proof. exact (MK_COMB (@lem515553 n) (@lem515556)). Qed.
Lemma lem515558 : term4 = term5.
Proof. exact (fun_ext (fun n : nat => @lem515557 n)). Qed.
Lemma lem515559 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem515560 : term6 = term7.
Proof. exact (MK_COMB (@lem515559) (@lem515558)). Qed.
Lemma lem515561 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem515562 : term8 = term9.
Proof. exact (MK_COMB (@lem515561) (@lem515560)). Qed.
Lemma lem515564 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem515565 : (NUMERAL 0) = 0.
Proof. exact (@lem515564 0). Qed.
Lemma lem515566 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem515567 (m : nat) : (term10 m) = (Nat.mul m 0).
Proof. exact (MK_COMB (@lem515566 m) (@lem515565)). Qed.
Lemma lem515568 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515569 (m : nat) : (term11 m) = (term12 m).
Proof. exact (MK_COMB (@lem515568) (@lem515567 m)). Qed.
Lemma lem515571 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem515572 : (NUMERAL 0) = 0.
Proof. exact (@lem515571 0). Qed.
Lemma lem515573 (m : nat) : ((term10 m) = (NUMERAL 0)) = ((Nat.mul m 0) = 0).
Proof. exact (MK_COMB (@lem515569 m) (@lem515572)). Qed.
Lemma lem515574 : term13 = term14.
Proof. exact (fun_ext (fun m : nat => @lem515573 m)). Qed.
Lemma lem515575 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem515576 : term15 = term16.
Proof. exact (MK_COMB (@lem515575) (@lem515574)). Qed.
Lemma lem515577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem515578 : term17 = term18.
Proof. exact (MK_COMB (@lem515577) (@lem515576)). Qed.
Lemma lem515580 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem515581 : term19 = (BIT1 0).
Proof. exact (@lem515580 (BIT1 0)). Qed.
Lemma lem515582 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem515583 : term20 = term21.
Proof. exact (MK_COMB (@lem515582) (@lem515581)). Qed.
Lemma lem515584 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem515585 (n : nat) : (term22 n) = (term23 n).
Proof. exact (MK_COMB (@lem515583) (@lem515584 n)). Qed.
Lemma lem515586 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515587 (n : nat) : (term24 n) = (term25 n).
Proof. exact (MK_COMB (@lem515586) (@lem515585 n)). Qed.
Lemma lem515588 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem515589 (n : nat) : ((term22 n) = n) = ((term23 n) = n).
Proof. exact (MK_COMB (@lem515587 n) (@lem515588 n)). Qed.
Lemma lem515590 : term26 = term27.
Proof. exact (fun_ext (fun n : nat => @lem515589 n)). Qed.
Lemma lem515591 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem515592 : term28 = term29.
Proof. exact (MK_COMB (@lem515591) (@lem515590)). Qed.
Lemma lem515593 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem515594 : term30 = term31.
Proof. exact (MK_COMB (@lem515593) (@lem515592)). Qed.
Lemma lem515596 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem515597 : term19 = (BIT1 0).
Proof. exact (@lem515596 (BIT1 0)). Qed.
Lemma lem515598 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem515599 (m : nat) : (term32 m) = (term33 m).
Proof. exact (MK_COMB (@lem515598 m) (@lem515597)). Qed.
Lemma lem515600 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515601 (m : nat) : (term34 m) = (term35 m).
Proof. exact (MK_COMB (@lem515600) (@lem515599 m)). Qed.
Lemma lem515602 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem515603 (m : nat) : ((term32 m) = m) = ((term33 m) = m).
Proof. exact (MK_COMB (@lem515601 m) (@lem515602 m)). Qed.
Lemma lem515604 : term36 = term37.
Proof. exact (fun_ext (fun m : nat => @lem515603 m)). Qed.
Lemma lem515605 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem515606 : term38 = term39.
Proof. exact (MK_COMB (@lem515605) (@lem515604)). Qed.
Lemma lem515607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem515608 : term40 = term41.
Proof. exact (MK_COMB (@lem515607) (@lem515606)). Qed.
Lemma lem515609 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem515610 : term43 = term44.
Proof. exact (MK_COMB (@lem515608) (@lem515609)). Qed.
Lemma lem515611 : term45 = term46.
Proof. exact (MK_COMB (@lem515594) (@lem515610)). Qed.
Lemma lem515612 : term47 = term48.
Proof. exact (MK_COMB (@lem515578) (@lem515611)). Qed.
Lemma lem515613 : term49 = term50.
Proof. exact (MK_COMB (@lem515562) (@lem515612)). Qed.
Lemma lem515614 : term50.
Proof. exact (EQ_MP (@lem515613) (@lem81645)). Qed.
