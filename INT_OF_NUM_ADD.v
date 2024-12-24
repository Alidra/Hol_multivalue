Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_OF_NUM_ADD_term_abbrevs.
Require Import thm1340339_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306786 (m : nat) : term0 m.
Proof. exact (@lem1340339 m). Qed.
Lemma lem2306787 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2306788 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2306787 m) (@lem2306786 m)). Qed.
Lemma lem2306789 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2306788 m n). Qed.
Lemma lem2306790 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (term4 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2306791 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem2306790 m n) (@lem2306789 m n)). Qed.
Lemma lem2306793 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306794 (m : nat) : (real_of_num m) = (term5 m).
Proof. exact (@lem2306793 m). Qed.
Lemma lem2306795 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2306796 (m : nat) : (term6 m) = (term7 m).
Proof. exact (MK_COMB (@lem2306795) (@lem2306794 m)). Qed.
Lemma lem2306798 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306799 (m : nat) (n : nat) : (term3 m n) = (term8 m n).
Proof. exact (MK_COMB (@lem2306796 m) (@lem2306798 n)). Qed.
Lemma lem2306801 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2306802 (m : nat) (n : nat) : (term8 m n) = (term11 m n).
Proof. exact (@lem2306801 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2306803 (m : nat) (n : nat) : (term3 m n) = (term11 m n).
Proof. exact (TRANS (@lem2306799 m n) (@lem2306802 m n)). Qed.
Lemma lem2306804 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306805 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (MK_COMB (@lem2306804) (@lem2306803 m n)). Qed.
Lemma lem2306807 (n : nat) : (real_of_num n) = (term5 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306808 (m : nat) (n : nat) : (term4 m n) = (term14 m n).
Proof. exact (@lem2306807 (Nat.add m n)). Qed.
Lemma lem2306809 (m : nat) (n : nat) : ((term3 m n) = (term4 m n)) = ((term11 m n) = (term14 m n)).
Proof. exact (MK_COMB (@lem2306805 m n) (@lem2306808 m n)). Qed.
Lemma lem2306811 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306812 (m : nat) (n : nat) : ((term11 m n) = (term14 m n)) = ((term15 m n) = (term16 m n)).
Proof. exact (@lem2306811 (term15 m n) (term16 m n)). Qed.
Lemma lem2306813 (m : nat) (n : nat) : ((term3 m n) = (term4 m n)) = ((term15 m n) = (term16 m n)).
Proof. exact (TRANS (@lem2306809 m n) (@lem2306812 m n)). Qed.
Lemma lem2306814 (m : nat) (n : nat) : (term15 m n) = (term16 m n).
Proof. exact (EQ_MP (@lem2306813 m n) (@lem2306791 m n)). Qed.
Lemma lem2306815 (m : nat) : term17 m.
Proof. exact (fun n : nat => @lem2306814 m n). Qed.
Lemma lem2306816 : term18.
Proof. exact (fun m : nat => @lem2306815 m). Qed.
