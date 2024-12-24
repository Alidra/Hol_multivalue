Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1318876_term_abbrevs.
Require Import NADD_OF_NUM_LE_spec.
Require Import thm1317782_spec.
Require Import thm1317787_spec.
Require Import thm1318142_spec.
Require Import thm1318147_spec.
Lemma lem1318841 (x : nadd) (y : nadd) : (nadd_le x y) = (term0 x y).
Proof. exact (EQ_MP (@lem1318147 x y) (@lem1318142 x y)). Qed.
Lemma lem1318842 (m : nat) (n : nat) : (term1 m n) = (term2 m n).
Proof. exact (@lem1318841 (nadd_of_num m) (nadd_of_num n)). Qed.
Lemma lem1318844 (m : nat) : (term3 m) = (hreal_of_num m).
Proof. exact (EQ_MP (@lem1317787 m) (@lem1317782 m)). Qed.
Lemma lem1318845 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1318846 (m : nat) : (term4 m) = (term5 m).
Proof. exact (MK_COMB (@lem1318845) (@lem1318844 m)). Qed.
Lemma lem1318848 (m : nat) : (term3 m) = (hreal_of_num m).
Proof. exact (EQ_MP (@lem1317787 m) (@lem1317782 m)). Qed.
Lemma lem1318849 (n : nat) : (term3 n) = (hreal_of_num n).
Proof. exact (@lem1318848 n). Qed.
Lemma lem1318850 (m : nat) (n : nat) : (term2 m n) = (term6 m n).
Proof. exact (MK_COMB (@lem1318846 m) (@lem1318849 n)). Qed.
Lemma lem1318851 (m : nat) (n : nat) : (term1 m n) = (term6 m n).
Proof. exact (TRANS (@lem1318842 m n) (@lem1318850 m n)). Qed.
Lemma lem1318852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1318853 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem1318852) (@lem1318851 m n)). Qed.
Lemma lem1318854 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem1318855 (m : nat) (n : nat) : ((term1 m n) = (Peano.le m n)) = ((term6 m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem1318853 m n) (@lem1318854 m n)). Qed.
Lemma lem1318858 (m : nat) : (term9 m) = (term10 m).
Proof. exact (fun_ext (fun n : nat => @lem1318855 m n)). Qed.
Lemma lem1318859 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1318860 (m : nat) : (term11 m) = (term12 m).
Proof. exact (MK_COMB (@lem1318859) (@lem1318858 m)). Qed.
Lemma lem1318867 : term13 = term14.
Proof. exact (fun_ext (fun m : nat => @lem1318860 m)). Qed.
Lemma lem1318868 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1318869 : term15 = term16.
Proof. exact (MK_COMB (@lem1318868) (@lem1318867)). Qed.
Lemma lem1318876 : term16.
Proof. exact (EQ_MP (@lem1318869) (@lem1273281)). Qed.
