Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_POW_EQ_EQ_term_abbrevs.
Require Import REAL_POW_EQ_EQ_spec.
Require Import thm2299876_spec.
Require Import thm2299877_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2308009 (n : nat) : term0 n.
Proof. exact (@lem1669003 n). Qed.
Lemma lem2308010 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2308011 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem2308010 n) (@lem2308009 n)). Qed.
Lemma lem2308012 (n : nat) (x : int) : term2 n x.
Proof. exact (@lem2308011 n (real_of_int x)). Qed.
Lemma lem2308013 (n : nat) (x : int) : (term2 n x) = (term3 n x).
Proof. exact (eq_refl (term2 n x)). Qed.
Lemma lem2308014 (n : nat) (x : int) : term3 n x.
Proof. exact (EQ_MP (@lem2308013 n x) (@lem2308012 n x)). Qed.
Lemma lem2308015 (n : nat) (x : int) (y : int) : term4 n x y.
Proof. exact (@lem2308014 n x (real_of_int y)). Qed.
Lemma lem2308016 (n : nat) (x : int) (y : int) : (term4 n x y) = (((term5 x n) = (term5 y n)) = (term6 n x y)).
Proof. exact (eq_refl (term4 n x y)). Qed.
Lemma lem2308017 (n : nat) (x : int) (y : int) : ((term5 x n) = (term5 y n)) = (term6 n x y).
Proof. exact (EQ_MP (@lem2308016 n x y) (@lem2308015 n x y)). Qed.
Lemma lem2308019 (x : int) (n : nat) : (term5 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308020 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2308021 (x : int) (n : nat) : (term8 x n) = (term9 x n).
Proof. exact (MK_COMB (@lem2308020) (@lem2308019 x n)). Qed.
Lemma lem2308023 (x : int) (n : nat) : (term5 x n) = (term7 x n).
Proof. exact (EQ_MP (@lem2299877 x n) (@lem2299876 x n)). Qed.
Lemma lem2308024 (y : int) (n : nat) : (term5 y n) = (term7 y n).
Proof. exact (@lem2308023 y n). Qed.
Lemma lem2308025 (x : int) (y : int) (n : nat) : ((term5 x n) = (term5 y n)) = ((term7 x n) = (term7 y n)).
Proof. exact (MK_COMB (@lem2308021 x n) (@lem2308024 y n)). Qed.
Lemma lem2308027 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308028 (x : int) (y : int) (n : nat) : ((term7 x n) = (term7 y n)) = ((int_pow x n) = (int_pow y n)).
Proof. exact (@lem2308027 (int_pow x n) (int_pow y n)). Qed.
Lemma lem2308029 (x : int) (y : int) (n : nat) : ((term5 x n) = (term5 y n)) = ((int_pow x n) = (int_pow y n)).
Proof. exact (TRANS (@lem2308025 x y n) (@lem2308028 x y n)). Qed.
Lemma lem2308030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2308031 (x : int) (y : int) (n : nat) : (term10 x y n) = (term11 x y n).
Proof. exact (MK_COMB (@lem2308030) (@lem2308029 x y n)). Qed.
Lemma lem2308033 (x : int) : (term12 x) = (term13 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2308034 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2308035 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2308034) (@lem2308033 x)). Qed.
Lemma lem2308037 (x : int) : (term12 x) = (term13 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2308038 (y : int) : (term12 y) = (term13 y).
Proof. exact (@lem2308037 y). Qed.
Lemma lem2308039 (x : int) (y : int) : ((term12 x) = (term12 y)) = ((term13 x) = (term13 y)).
Proof. exact (MK_COMB (@lem2308035 x) (@lem2308038 y)). Qed.
Lemma lem2308041 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308042 (x : int) (y : int) : ((term13 x) = (term13 y)) = ((int_abs x) = (int_abs y)).
Proof. exact (@lem2308041 (int_abs x) (int_abs y)). Qed.
Lemma lem2308043 (x : int) (y : int) : ((term12 x) = (term12 y)) = ((int_abs x) = (int_abs y)).
Proof. exact (TRANS (@lem2308039 x y) (@lem2308042 x y)). Qed.
Lemma lem2308044 (n : nat) : (term16 n) = (term16 n).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem2308045 (n : nat) (x : int) (y : int) : (term17 n x y) = (term18 n x y).
Proof. exact (MK_COMB (@lem2308044 n) (@lem2308043 x y)). Qed.
Lemma lem2308046 (n : nat) : (term19 n) = (term19 n).
Proof. exact (eq_refl (term19 n)). Qed.
Lemma lem2308047 (n : nat) (x : int) (y : int) : (term20 n x y) = (term21 n x y).
Proof. exact (MK_COMB (@lem2308046 n) (@lem2308045 n x y)). Qed.
Lemma lem2308049 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2308050 (n : nat) (x : int) (y : int) : (term6 n x y) = (term22 n x y).
Proof. exact (MK_COMB (@lem2308047 n x y) (@lem2308049 x y)). Qed.
Lemma lem2308051 (n : nat) (x : int) (y : int) : (((term5 x n) = (term5 y n)) = (term6 n x y)) = (((int_pow x n) = (int_pow y n)) = (term22 n x y)).
Proof. exact (MK_COMB (@lem2308031 x y n) (@lem2308050 n x y)). Qed.
Lemma lem2308052 (n : nat) (x : int) (y : int) : ((int_pow x n) = (int_pow y n)) = (term22 n x y).
Proof. exact (EQ_MP (@lem2308051 n x y) (@lem2308017 n x y)). Qed.
Lemma lem2308053 (n : nat) (x : int) : term23 n x.
Proof. exact (fun y : int => @lem2308052 n x y). Qed.
Lemma lem2308054 (n : nat) : term24 n.
Proof. exact (fun x : int => @lem2308053 n x). Qed.
Lemma lem2308055 : term25.
Proof. exact (fun n : nat => @lem2308054 n). Qed.
