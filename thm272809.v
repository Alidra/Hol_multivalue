Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm272809_term_abbrevs.
Require Import LE_TRANS_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem272798 (p : Prop) (q : Prop) (r : Prop) : (term0 p q r) = (term1 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem272799 (n : nat) (m : nat) (p : nat) : (term2 n m p) = (term3 n m p).
Proof. exact (@lem272798 (Peano.le m n) (Peano.le n p) (Peano.le m p)). Qed.
Lemma lem272800 (n : nat) (m : nat) : (term4 n m) = (term5 n m).
Proof. exact (fun_ext (fun p : nat => @lem272799 n m p)). Qed.
Lemma lem272801 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem272802 (n : nat) (m : nat) : (term6 n m) = (term7 n m).
Proof. exact (MK_COMB (@lem272801) (@lem272800 n m)). Qed.
Lemma lem272803 (m : nat) : (term8 m) = (term9 m).
Proof. exact (fun_ext (fun n : nat => @lem272802 n m)). Qed.
Lemma lem272804 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem272805 (m : nat) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem272804) (@lem272803 m)). Qed.
Lemma lem272806 : term12 = term13.
Proof. exact (fun_ext (fun m : nat => @lem272805 m)). Qed.
Lemma lem272807 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem272808 : term14 = term15.
Proof. exact (MK_COMB (@lem272807) (@lem272806)). Qed.
Lemma lem272809 : term15.
Proof. exact (EQ_MP (@lem272808) (@lem93743)). Qed.
