Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516816_term_abbrevs.
Require Import MULT_EQ_0_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Lemma lem516790 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem516791 : (NUMERAL 0) = 0.
Proof. exact (@lem516790 0). Qed.
Lemma lem516792 (m : nat) (n : nat) : (term0 m n) = (term0 m n).
Proof. exact (eq_refl (term0 m n)). Qed.
Lemma lem516793 (m : nat) (n : nat) : ((Nat.mul m n) = (NUMERAL 0)) = ((Nat.mul m n) = 0).
Proof. exact (MK_COMB (@lem516792 m n) (@lem516791)). Qed.
Lemma lem516794 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem516795 (m : nat) (n : nat) : (term1 m n) = (term2 m n).
Proof. exact (MK_COMB (@lem516794) (@lem516793 m n)). Qed.
Lemma lem516797 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem516798 : (NUMERAL 0) = 0.
Proof. exact (@lem516797 0). Qed.
Lemma lem516799 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem516800 (m : nat) : (m = (NUMERAL 0)) = (m = 0).
Proof. exact (MK_COMB (@lem516799 m) (@lem516798)). Qed.
Lemma lem516801 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem516802 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem516801) (@lem516800 m)). Qed.
Lemma lem516804 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem516805 : (NUMERAL 0) = 0.
Proof. exact (@lem516804 0). Qed.
Lemma lem516806 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem516807 (n : nat) : (n = (NUMERAL 0)) = (n = 0).
Proof. exact (MK_COMB (@lem516806 n) (@lem516805)). Qed.
Lemma lem516808 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (MK_COMB (@lem516802 m) (@lem516807 n)). Qed.
Lemma lem516809 (m : nat) (n : nat) : (((Nat.mul m n) = (NUMERAL 0)) = (term5 m n)) = (((Nat.mul m n) = 0) = (term6 m n)).
Proof. exact (MK_COMB (@lem516795 m n) (@lem516808 m n)). Qed.
Lemma lem516810 (m : nat) : (term7 m) = (term8 m).
Proof. exact (fun_ext (fun n : nat => @lem516809 m n)). Qed.
Lemma lem516811 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516812 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem516811) (@lem516810 m)). Qed.
Lemma lem516813 : term11 = term12.
Proof. exact (fun_ext (fun m : nat => @lem516812 m)). Qed.
Lemma lem516814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516815 : term13 = term14.
Proof. exact (MK_COMB (@lem516814) (@lem516813)). Qed.
Lemma lem516816 : term14.
Proof. exact (EQ_MP (@lem516815) (@lem83870)). Qed.
