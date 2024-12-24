Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5401030_term_abbrevs.
Require Import thm5400767_spec.
Require Import thm5400768_spec.
Require Import thm5400781_spec.
Require Import thm5400782_spec.
Lemma lem5400996 (m : nat) (p : nat) (n : nat) : (term0 p m n) = (term1 m p n).
Proof. exact (EQ_MP (@lem5400782 m p n) (@lem5400781 m n p)). Qed.
Lemma lem5400997 (m : nat) (x : nat) (n : nat) : (term2 x m n) = (term3 m x n).
Proof. exact (@lem5400996 m x (S n)). Qed.
Lemma lem5401000 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5401001 (m : nat) (x : nat) (n : nat) : (term4 x m n) = (term5 m x n).
Proof. exact (MK_COMB (@lem5401000) (@lem5400997 m x n)). Qed.
Lemma lem5401003 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term6 A x y s) = (term7 A y x s).
Proof. exact (EQ_MP (@lem5400768 A y x s) (@lem5400767 A y x s)). Qed.
Lemma lem5401004 (y : nat) (x : nat) (s : nat -> Prop) : (term8 x y s) = (term9 y x s).
Proof. exact (@lem5401003 nat y x s). Qed.
Lemma lem5401005 (x : nat) (m : nat) (n : nat) : (term10 x m n) = (term11 x m n).
Proof. exact (@lem5401004 (S n) x (dotdot m n)). Qed.
Lemma lem5401011 (m : nat) (p : nat) (n : nat) : (term0 p m n) = (term1 m p n).
Proof. exact (EQ_MP (@lem5400782 m p n) (@lem5400781 m n p)). Qed.
Lemma lem5401012 (m : nat) (x : nat) (n : nat) : (term0 x m n) = (term1 m x n).
Proof. exact (@lem5401011 m x n). Qed.
Lemma lem5401015 (x : nat) (n : nat) : (term12 x n) = (term12 x n).
Proof. exact (eq_refl (term12 x n)). Qed.
Lemma lem5401016 (m : nat) (x : nat) (n : nat) : (term11 x m n) = (term13 m x n).
Proof. exact (MK_COMB (@lem5401015 x n) (@lem5401012 m x n)). Qed.
Lemma lem5401019 (m : nat) (x : nat) (n : nat) : (term10 x m n) = (term13 m x n).
Proof. exact (TRANS (@lem5401005 x m n) (@lem5401016 m x n)). Qed.
Lemma lem5401020 (m : nat) (x : nat) (n : nat) : ((term2 x m n) = (term10 x m n)) = ((term3 m x n) = (term13 m x n)).
Proof. exact (MK_COMB (@lem5401001 m x n) (@lem5401019 m x n)). Qed.
Lemma lem5401023 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (fun_ext (fun x : nat => @lem5401020 m x n)). Qed.
Lemma lem5401024 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5401025 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (MK_COMB (@lem5401024) (@lem5401023 m n)). Qed.
Lemma lem5401030 (m : nat) (n : nat) : (term17 m n) = (term16 m n).
Proof. exact (SYM (@lem5401025 m n)). Qed.
