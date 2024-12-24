Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm515633_term_abbrevs.
Require Import EXP_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Lemma lem515616 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem515617 : (NUMERAL 0) = 0.
Proof. exact (@lem515616 0). Qed.
Lemma lem515618 (m : nat) : (Nat.pow m) = (Nat.pow m).
Proof. exact (eq_refl (Nat.pow m)). Qed.
Lemma lem515619 (m : nat) : (term0 m) = (Nat.pow m 0).
Proof. exact (MK_COMB (@lem515618 m) (@lem515617)). Qed.
Lemma lem515620 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem515621 (m : nat) : (term1 m) = (term2 m).
Proof. exact (MK_COMB (@lem515620) (@lem515619 m)). Qed.
Lemma lem515623 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem515624 : term3 = (BIT1 0).
Proof. exact (@lem515623 (BIT1 0)). Qed.
Lemma lem515625 (m : nat) : ((term0 m) = term3) = ((Nat.pow m 0) = (BIT1 0)).
Proof. exact (MK_COMB (@lem515621 m) (@lem515624)). Qed.
Lemma lem515626 : term4 = term5.
Proof. exact (fun_ext (fun m : nat => @lem515625 m)). Qed.
Lemma lem515627 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem515628 : term6 = term7.
Proof. exact (MK_COMB (@lem515627) (@lem515626)). Qed.
Lemma lem515629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem515630 : term8 = term9.
Proof. exact (MK_COMB (@lem515629) (@lem515628)). Qed.
Lemma lem515631 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem515632 : term11 = term12.
Proof. exact (MK_COMB (@lem515630) (@lem515631)). Qed.
Lemma lem515633 : term12.
Proof. exact (EQ_MP (@lem515632) (@lem86202)). Qed.
