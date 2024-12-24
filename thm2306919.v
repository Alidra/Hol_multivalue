Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2306919_term_abbrevs.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Require Import thm2306823_spec.
Lemma lem2306889 : term0.
Proof. exact (proj1 (@lem2306823)). Qed.
Lemma lem2306890 (m : nat) : term1 m.
Proof. exact (@lem2306889 m). Qed.
Lemma lem2306891 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem2306892 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem2306891 m) (@lem2306890 m)). Qed.
Lemma lem2306893 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem2306892 m n). Qed.
Lemma lem2306894 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2306895 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem2306894 m n) (@lem2306893 m n)). Qed.
Lemma lem2306897 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306898 (m : nat) : (real_of_num m) = (term6 m).
Proof. exact (@lem2306897 m). Qed.
Lemma lem2306899 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2306900 (m : nat) : (term7 m) = (term8 m).
Proof. exact (MK_COMB (@lem2306899) (@lem2306898 m)). Qed.
Lemma lem2306902 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306903 (m : nat) (n : nat) : (term4 m n) = (term9 m n).
Proof. exact (MK_COMB (@lem2306900 m) (@lem2306902 n)). Qed.
Lemma lem2306905 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2306906 (m : nat) (n : nat) : (term9 m n) = (term12 m n).
Proof. exact (@lem2306905 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2306907 (m : nat) (n : nat) : (term4 m n) = (term12 m n).
Proof. exact (TRANS (@lem2306903 m n) (@lem2306906 m n)). Qed.
Lemma lem2306908 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306909 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem2306908) (@lem2306907 m n)). Qed.
Lemma lem2306911 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306912 (m : nat) (n : nat) : (term5 m n) = (term15 m n).
Proof. exact (@lem2306911 (Nat.add m n)). Qed.
Lemma lem2306913 (m : nat) (n : nat) : ((term4 m n) = (term5 m n)) = ((term12 m n) = (term15 m n)).
Proof. exact (MK_COMB (@lem2306909 m n) (@lem2306912 m n)). Qed.
Lemma lem2306915 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306916 (m : nat) (n : nat) : ((term12 m n) = (term15 m n)) = ((term16 m n) = (term17 m n)).
Proof. exact (@lem2306915 (term16 m n) (term17 m n)). Qed.
Lemma lem2306917 (m : nat) (n : nat) : ((term4 m n) = (term5 m n)) = ((term16 m n) = (term17 m n)).
Proof. exact (TRANS (@lem2306913 m n) (@lem2306916 m n)). Qed.
Lemma lem2306918 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem2306917 m n) (@lem2306895 m n)). Qed.
Lemma lem2306919 (m : nat) : term18 m.
Proof. exact (fun n : nat => @lem2306918 m n). Qed.
