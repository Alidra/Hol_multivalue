Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516702_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Lemma lem516670 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem516671 : (NUMERAL 0) = 0.
Proof. exact (@lem516670 0). Qed.
Lemma lem516672 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem516673 : term0 = (Nat.add 0).
Proof. exact (MK_COMB (@lem516672) (@lem516671)). Qed.
Lemma lem516674 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem516675 (n : nat) : (term1 n) = (Nat.add 0 n).
Proof. exact (MK_COMB (@lem516673) (@lem516674 n)). Qed.
Lemma lem516676 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem516677 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem516676) (@lem516675 n)). Qed.
Lemma lem516678 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem516679 (n : nat) : ((term1 n) = n) = ((Nat.add 0 n) = n).
Proof. exact (MK_COMB (@lem516677 n) (@lem516678 n)). Qed.
Lemma lem516680 : term4 = term5.
Proof. exact (fun_ext (fun n : nat => @lem516679 n)). Qed.
Lemma lem516681 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516682 : term6 = term7.
Proof. exact (MK_COMB (@lem516681) (@lem516680)). Qed.
Lemma lem516683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem516684 : term8 = term9.
Proof. exact (MK_COMB (@lem516683) (@lem516682)). Qed.
Lemma lem516686 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem516687 : (NUMERAL 0) = 0.
Proof. exact (@lem516686 0). Qed.
Lemma lem516688 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem516689 (m : nat) : (term10 m) = (Nat.add m 0).
Proof. exact (MK_COMB (@lem516688 m) (@lem516687)). Qed.
Lemma lem516690 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem516691 (m : nat) : (term11 m) = (term12 m).
Proof. exact (MK_COMB (@lem516690) (@lem516689 m)). Qed.
Lemma lem516692 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem516693 (m : nat) : ((term10 m) = m) = ((Nat.add m 0) = m).
Proof. exact (MK_COMB (@lem516691 m) (@lem516692 m)). Qed.
Lemma lem516694 : term13 = term14.
Proof. exact (fun_ext (fun m : nat => @lem516693 m)). Qed.
Lemma lem516695 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516696 : term15 = term16.
Proof. exact (MK_COMB (@lem516695) (@lem516694)). Qed.
Lemma lem516697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem516698 : term17 = term18.
Proof. exact (MK_COMB (@lem516697) (@lem516696)). Qed.
Lemma lem516699 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem516700 : term20 = term21.
Proof. exact (MK_COMB (@lem516698) (@lem516699)). Qed.
Lemma lem516701 : term22 = term23.
Proof. exact (MK_COMB (@lem516684) (@lem516700)). Qed.
Lemma lem516702 : term23.
Proof. exact (EQ_MP (@lem516701) (@lem77629)). Qed.
