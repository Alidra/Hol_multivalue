Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2306886_term_abbrevs.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Require Import thm2306824_spec.
Lemma lem2306856 : term0.
Proof. exact (proj1 (@lem2306824)). Qed.
Lemma lem2306857 (m : nat) : term1 m.
Proof. exact (@lem2306856 m). Qed.
Lemma lem2306858 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem2306859 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem2306858 m) (@lem2306857 m)). Qed.
Lemma lem2306860 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem2306859 m n). Qed.
Lemma lem2306861 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2306862 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem2306861 m n) (@lem2306860 m n)). Qed.
Lemma lem2306864 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306865 (m : nat) : (real_of_num m) = (term6 m).
Proof. exact (@lem2306864 m). Qed.
Lemma lem2306866 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2306867 (m : nat) : (term7 m) = (term8 m).
Proof. exact (MK_COMB (@lem2306866) (@lem2306865 m)). Qed.
Lemma lem2306869 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306870 (m : nat) (n : nat) : (term4 m n) = (term9 m n).
Proof. exact (MK_COMB (@lem2306867 m) (@lem2306869 n)). Qed.
Lemma lem2306872 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306873 (m : nat) (n : nat) : (term9 m n) = (term12 m n).
Proof. exact (@lem2306872 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2306874 (m : nat) (n : nat) : (term4 m n) = (term12 m n).
Proof. exact (TRANS (@lem2306870 m n) (@lem2306873 m n)). Qed.
Lemma lem2306875 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306876 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem2306875) (@lem2306874 m n)). Qed.
Lemma lem2306878 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306879 (m : nat) (n : nat) : (term5 m n) = (term15 m n).
Proof. exact (@lem2306878 (Nat.mul m n)). Qed.
Lemma lem2306880 (m : nat) (n : nat) : ((term4 m n) = (term5 m n)) = ((term12 m n) = (term15 m n)).
Proof. exact (MK_COMB (@lem2306876 m n) (@lem2306879 m n)). Qed.
Lemma lem2306882 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306883 (m : nat) (n : nat) : ((term12 m n) = (term15 m n)) = ((term16 m n) = (term17 m n)).
Proof. exact (@lem2306882 (term16 m n) (term17 m n)). Qed.
Lemma lem2306884 (m : nat) (n : nat) : ((term4 m n) = (term5 m n)) = ((term16 m n) = (term17 m n)).
Proof. exact (TRANS (@lem2306880 m n) (@lem2306883 m n)). Qed.
Lemma lem2306885 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem2306884 m n) (@lem2306862 m n)). Qed.
Lemma lem2306886 (m : nat) : term18 m.
Proof. exact (fun n : nat => @lem2306885 m n). Qed.
