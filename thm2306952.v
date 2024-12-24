Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2306952_term_abbrevs.
Require Import thm2299882_spec.
Require Import thm2299883_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Require Import thm2306822_spec.
Lemma lem2306922 : term0.
Proof. exact (proj1 (@lem2306822)). Qed.
Lemma lem2306923 (m : nat) : term1 m.
Proof. exact (@lem2306922 m). Qed.
Lemma lem2306924 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem2306925 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem2306924 m) (@lem2306923 m)). Qed.
Lemma lem2306926 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem2306925 m n). Qed.
Lemma lem2306927 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2306928 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem2306927 m n) (@lem2306926 m n)). Qed.
Lemma lem2306930 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306931 (m : nat) : (real_of_num m) = (term6 m).
Proof. exact (@lem2306930 m). Qed.
Lemma lem2306932 : real_min = real_min.
Proof. exact (eq_refl real_min). Qed.
Lemma lem2306933 (m : nat) : (term7 m) = (term8 m).
Proof. exact (MK_COMB (@lem2306932) (@lem2306931 m)). Qed.
Lemma lem2306935 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306936 (m : nat) (n : nat) : (term4 m n) = (term9 m n).
Proof. exact (MK_COMB (@lem2306933 m) (@lem2306935 n)). Qed.
Lemma lem2306938 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2306939 (m : nat) (n : nat) : (term9 m n) = (term12 m n).
Proof. exact (@lem2306938 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2306940 (m : nat) (n : nat) : (term4 m n) = (term12 m n).
Proof. exact (TRANS (@lem2306936 m n) (@lem2306939 m n)). Qed.
Lemma lem2306941 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306942 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem2306941) (@lem2306940 m n)). Qed.
Lemma lem2306944 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306945 (m : nat) (n : nat) : (term5 m n) = (term15 m n).
Proof. exact (@lem2306944 (Nat.min m n)). Qed.
Lemma lem2306946 (m : nat) (n : nat) : ((term4 m n) = (term5 m n)) = ((term12 m n) = (term15 m n)).
Proof. exact (MK_COMB (@lem2306942 m n) (@lem2306945 m n)). Qed.
Lemma lem2306948 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306949 (m : nat) (n : nat) : ((term12 m n) = (term15 m n)) = ((term16 m n) = (term17 m n)).
Proof. exact (@lem2306948 (term16 m n) (term17 m n)). Qed.
Lemma lem2306950 (m : nat) (n : nat) : ((term4 m n) = (term5 m n)) = ((term16 m n) = (term17 m n)).
Proof. exact (TRANS (@lem2306946 m n) (@lem2306949 m n)). Qed.
Lemma lem2306951 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem2306950 m n) (@lem2306928 m n)). Qed.
Lemma lem2306952 (m : nat) : term18 m.
Proof. exact (fun n : nat => @lem2306951 m n). Qed.
