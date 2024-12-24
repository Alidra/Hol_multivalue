Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1318825_term_abbrevs.
Require Import NADD_OF_NUM_EQ_spec.
Require Import thm1317782_spec.
Require Import thm1317787_spec.
Require Import thm1318766_spec.
Require Import thm1318767_spec.
Lemma lem1318784 (x : nadd) (y : nadd) : (nadd_eq x y) = ((term0 x) = (term0 y)).
Proof. exact (EQ_MP (@lem1318767 x y) (@lem1318766 x y)). Qed.
Lemma lem1318785 (m : nat) (n : nat) : (term1 m n) = ((term2 m) = (term2 n)).
Proof. exact (@lem1318784 (nadd_of_num m) (nadd_of_num n)). Qed.
Lemma lem1318789 (m : nat) : (term2 m) = (hreal_of_num m).
Proof. exact (EQ_MP (@lem1317787 m) (@lem1317782 m)). Qed.
Lemma lem1318790 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1318791 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem1318790) (@lem1318789 m)). Qed.
Lemma lem1318793 (m : nat) : (term2 m) = (hreal_of_num m).
Proof. exact (EQ_MP (@lem1317787 m) (@lem1317782 m)). Qed.
Lemma lem1318794 (n : nat) : (term2 n) = (hreal_of_num n).
Proof. exact (@lem1318793 n). Qed.
Lemma lem1318795 (m : nat) (n : nat) : ((term2 m) = (term2 n)) = ((hreal_of_num m) = (hreal_of_num n)).
Proof. exact (MK_COMB (@lem1318791 m) (@lem1318794 n)). Qed.
Lemma lem1318798 (m : nat) (n : nat) : (term1 m n) = ((hreal_of_num m) = (hreal_of_num n)).
Proof. exact (TRANS (@lem1318785 m n) (@lem1318795 m n)). Qed.
Lemma lem1318799 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1318800 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (MK_COMB (@lem1318799) (@lem1318798 m n)). Qed.
Lemma lem1318803 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem1318804 (m : nat) (n : nat) : ((term1 m n) = (m = n)) = (((hreal_of_num m) = (hreal_of_num n)) = (m = n)).
Proof. exact (MK_COMB (@lem1318800 m n) (@lem1318803 m n)). Qed.
Lemma lem1318807 (m : nat) : (term7 m) = (term8 m).
Proof. exact (fun_ext (fun n : nat => @lem1318804 m n)). Qed.
Lemma lem1318808 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1318809 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem1318808) (@lem1318807 m)). Qed.
Lemma lem1318816 : term11 = term12.
Proof. exact (fun_ext (fun m : nat => @lem1318809 m)). Qed.
Lemma lem1318817 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1318818 : term13 = term14.
Proof. exact (MK_COMB (@lem1318817) (@lem1318816)). Qed.
Lemma lem1318825 : term14.
Proof. exact (EQ_MP (@lem1318818) (@lem1269222)). Qed.
