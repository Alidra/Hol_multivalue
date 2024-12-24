Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BIT0_THM_term_abbrevs.
Require Import BIT0_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75543_spec.
Lemma lem80123 (n : nat) : term0 n.
Proof. exact (@lem80084 n). Qed.
Lemma lem80124 (n : nat) : (term0 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem80126 (n : nat) : term1 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem80127 (n : nat) : (term1 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem80136 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem80127 n) (@lem80126 n)). Qed.
Lemma lem80137 (n : nat) : (term2 n) = (BIT0 n).
Proof. exact (@lem80136 (BIT0 n)). Qed.
Lemma lem80139 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem80124 n) (@lem80123 n)). Qed.
Lemma lem80140 (n : nat) : (term2 n) = (Nat.add n n).
Proof. exact (TRANS (@lem80137 n) (@lem80139 n)). Qed.
Lemma lem80141 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem80142 (n : nat) : (term3 n) = (term4 n).
Proof. exact (MK_COMB (@lem80141) (@lem80140 n)). Qed.
Lemma lem80144 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem80127 n) (@lem80126 n)). Qed.
Lemma lem80145 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem80146 (n : nat) : (term5 n) = (Nat.add n).
Proof. exact (MK_COMB (@lem80145) (@lem80144 n)). Qed.
Lemma lem80148 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem80127 n) (@lem80126 n)). Qed.
Lemma lem80149 (n : nat) : (term6 n) = (Nat.add n n).
Proof. exact (MK_COMB (@lem80146 n) (@lem80148 n)). Qed.
Lemma lem80150 (n : nat) : ((term2 n) = (term6 n)) = ((Nat.add n n) = (Nat.add n n)).
Proof. exact (MK_COMB (@lem80142 n) (@lem80149 n)). Qed.
Lemma lem80152 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem80153 (x : nat) : (x = x) = True.
Proof. exact (@lem80152 nat x). Qed.
Lemma lem80154 (n : nat) : ((Nat.add n n) = (Nat.add n n)) = True.
Proof. exact (@lem80153 (Nat.add n n)). Qed.
Lemma lem80155 (n : nat) : ((term2 n) = (term6 n)) = True.
Proof. exact (TRANS (@lem80150 n) (@lem80154 n)). Qed.
Lemma lem80156 : term7 = term8.
Proof. exact (fun_ext (fun n : nat => @lem80155 n)). Qed.
Lemma lem80157 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem80158 : term9 = term10.
Proof. exact (MK_COMB (@lem80157) (@lem80156)). Qed.
Lemma lem80160 {A : Type'} (t : Prop) : (term11 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem80161 (t : Prop) : (term12 t) = t.
Proof. exact (@lem80160 nat t). Qed.
Lemma lem80162 : term10 = True.
Proof. exact (@lem80161 True). Qed.
Lemma lem80163 : term9 = True.
Proof. exact (TRANS (@lem80158) (@lem80162)). Qed.
Lemma lem80164 : True = term9.
Proof. exact (SYM (@lem80163)). Qed.
Lemma lem80165 : term9.
Proof. exact (EQ_MP (@lem80164) (@lem0)). Qed.
