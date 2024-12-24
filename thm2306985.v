Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2306985_term_abbrevs.
Require Import thm2299888_spec.
Require Import thm2299889_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Require Import thm2306821_spec.
Lemma lem2306955 : term0.
Proof. exact (proj1 (@lem2306821)). Qed.
Lemma lem2306956 (m : nat) : term1 m.
Proof. exact (@lem2306955 m). Qed.
Lemma lem2306957 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem2306958 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem2306957 m) (@lem2306956 m)). Qed.
Lemma lem2306959 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem2306958 m n). Qed.
Lemma lem2306960 (m : nat) (n : nat) : (term3 m n) = ((term4 m n) = (term5 m n)).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2306961 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem2306960 m n) (@lem2306959 m n)). Qed.
Lemma lem2306963 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306964 (m : nat) : (real_of_num m) = (term6 m).
Proof. exact (@lem2306963 m). Qed.
Lemma lem2306965 : real_max = real_max.
Proof. exact (eq_refl real_max). Qed.
Lemma lem2306966 (m : nat) : (term7 m) = (term8 m).
Proof. exact (MK_COMB (@lem2306965) (@lem2306964 m)). Qed.
Lemma lem2306968 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306969 (m : nat) (n : nat) : (term4 m n) = (term9 m n).
Proof. exact (MK_COMB (@lem2306966 m) (@lem2306968 n)). Qed.
Lemma lem2306971 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2306972 (m : nat) (n : nat) : (term9 m n) = (term12 m n).
Proof. exact (@lem2306971 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2306973 (m : nat) (n : nat) : (term4 m n) = (term12 m n).
Proof. exact (TRANS (@lem2306969 m n) (@lem2306972 m n)). Qed.
Lemma lem2306974 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306975 (m : nat) (n : nat) : (term13 m n) = (term14 m n).
Proof. exact (MK_COMB (@lem2306974) (@lem2306973 m n)). Qed.
Lemma lem2306977 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2306978 (m : nat) (n : nat) : (term5 m n) = (term15 m n).
Proof. exact (@lem2306977 (Nat.max m n)). Qed.
Lemma lem2306979 (m : nat) (n : nat) : ((term4 m n) = (term5 m n)) = ((term12 m n) = (term15 m n)).
Proof. exact (MK_COMB (@lem2306975 m n) (@lem2306978 m n)). Qed.
Lemma lem2306981 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306982 (m : nat) (n : nat) : ((term12 m n) = (term15 m n)) = ((term16 m n) = (term17 m n)).
Proof. exact (@lem2306981 (term16 m n) (term17 m n)). Qed.
Lemma lem2306983 (m : nat) (n : nat) : ((term4 m n) = (term5 m n)) = ((term16 m n) = (term17 m n)).
Proof. exact (TRANS (@lem2306979 m n) (@lem2306982 m n)). Qed.
Lemma lem2306984 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem2306983 m n) (@lem2306961 m n)). Qed.
Lemma lem2306985 (m : nat) : term18 m.
Proof. exact (fun n : nat => @lem2306984 m n). Qed.
