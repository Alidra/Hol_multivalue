Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUM_OF_INT_OF_NUM_term_abbrevs.
Require Import INT_OF_NUM_EQ_spec.
Require Import num_of_int_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm9523_spec.
Require Import thm9524_spec.
Lemma lem2833939 (m : nat) : term0 m.
Proof. exact (@lem2307147 m). Qed.
Lemma lem2833940 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2833941 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2833940 m) (@lem2833939 m)). Qed.
Lemma lem2833942 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2833941 m n). Qed.
Lemma lem2833943 (m : nat) (n : nat) : (term2 m n) = (((int_of_num m) = (int_of_num n)) = (m = n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2833945 (x : int) : term3 x.
Proof. exact (@lem2833930 x). Qed.
Lemma lem2833946 (x : int) : (term3 x) = ((num_of_int x) = (term4 x)).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem2833955 (x : int) : (num_of_int x) = (term4 x).
Proof. exact (EQ_MP (@lem2833946 x) (@lem2833945 x)). Qed.
Lemma lem2833956 (n : nat) : (term5 n) = (term6 n).
Proof. exact (@lem2833955 (int_of_num n)). Qed.
Lemma lem2833960 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2833943 m n) (@lem2833942 m n)). Qed.
Lemma lem2833961 (n' : nat) (n : nat) : ((int_of_num n') = (int_of_num n)) = (n' = n).
Proof. exact (@lem2833960 n' n). Qed.
Lemma lem2833964 (n : nat) : (term7 n) = (term8 n).
Proof. exact (fun_ext (fun n' : nat => @lem2833961 n' n)). Qed.
Lemma lem2833965 : (@ε nat) = (@ε nat).
Proof. exact (eq_refl (@ε nat)). Qed.
Lemma lem2833966 (n : nat) : (term6 n) = (term9 n).
Proof. exact (MK_COMB (@lem2833965) (@lem2833964 n)). Qed.
Lemma lem2833968 {A : Type'} (x : A) : (term10 A x) = x.
Proof. exact (EQ_MP (@lem9524 A x) (@lem9523 A x)). Qed.
Lemma lem2833969 (x : nat) : (term9 x) = x.
Proof. exact (@lem2833968 nat x). Qed.
Lemma lem2833970 (n : nat) : (term9 n) = n.
Proof. exact (@lem2833969 n). Qed.
Lemma lem2833971 (n : nat) : (term6 n) = n.
Proof. exact (TRANS (@lem2833966 n) (@lem2833970 n)). Qed.
Lemma lem2833972 (n : nat) : (term5 n) = n.
Proof. exact (TRANS (@lem2833956 n) (@lem2833971 n)). Qed.
Lemma lem2833973 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem2833974 (n : nat) : (term11 n) = (@eq nat n).
Proof. exact (MK_COMB (@lem2833973) (@lem2833972 n)). Qed.
Lemma lem2833975 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2833976 (n : nat) : ((term5 n) = n) = (n = n).
Proof. exact (MK_COMB (@lem2833974 n) (@lem2833975 n)). Qed.
Lemma lem2833978 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2833979 (x : nat) : (x = x) = True.
Proof. exact (@lem2833978 nat x). Qed.
Lemma lem2833980 (n : nat) : (n = n) = True.
Proof. exact (@lem2833979 n). Qed.
Lemma lem2833981 (n : nat) : ((term5 n) = n) = True.
Proof. exact (TRANS (@lem2833976 n) (@lem2833980 n)). Qed.
Lemma lem2833982 : term12 = term13.
Proof. exact (fun_ext (fun n : nat => @lem2833981 n)). Qed.
Lemma lem2833983 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2833984 : term14 = term15.
Proof. exact (MK_COMB (@lem2833983) (@lem2833982)). Qed.
Lemma lem2833986 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2833987 (t : Prop) : (term17 t) = t.
Proof. exact (@lem2833986 nat t). Qed.
Lemma lem2833988 : term15 = True.
Proof. exact (@lem2833987 True). Qed.
Lemma lem2833989 : term14 = True.
Proof. exact (TRANS (@lem2833984) (@lem2833988)). Qed.
Lemma lem2833990 : True = term14.
Proof. exact (SYM (@lem2833989)). Qed.
Lemma lem2833991 : term14.
Proof. exact (EQ_MP (@lem2833990) (@lem0)). Qed.
