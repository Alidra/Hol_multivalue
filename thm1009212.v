Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1009212_term_abbrevs.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75543_spec.
Lemma lem1009190 (n : nat) : term0 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem1009191 (n : nat) : (term0 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1009196 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1009191 n) (@lem1009190 n)). Qed.
Lemma lem1009197 (m : nat) : (NUMERAL m) = m.
Proof. exact (@lem1009196 m). Qed.
Lemma lem1009198 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem1009199 (m : nat) : (term1 m) = (Nat.pow m).
Proof. exact (MK_COMB (@lem1009198) (@lem1009197 m)). Qed.
Lemma lem1009201 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1009191 n) (@lem1009190 n)). Qed.
Lemma lem1009202 (m : nat) (n : nat) : (term2 m n) = (Nat.pow m n).
Proof. exact (MK_COMB (@lem1009199 m) (@lem1009201 n)). Qed.
Lemma lem1009203 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1009204 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (MK_COMB (@lem1009203) (@lem1009202 m n)). Qed.
Lemma lem1009205 (m : nat) (n : nat) : (Nat.pow m n) = (Nat.pow m n).
Proof. exact (eq_refl (Nat.pow m n)). Qed.
Lemma lem1009206 (m : nat) (n : nat) : ((term2 m n) = (Nat.pow m n)) = ((Nat.pow m n) = (Nat.pow m n)).
Proof. exact (MK_COMB (@lem1009204 m n) (@lem1009205 m n)). Qed.
Lemma lem1009208 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1009209 (x : nat) : (x = x) = True.
Proof. exact (@lem1009208 nat x). Qed.
Lemma lem1009210 (m : nat) (n : nat) : ((Nat.pow m n) = (Nat.pow m n)) = True.
Proof. exact (@lem1009209 (Nat.pow m n)). Qed.
Lemma lem1009211 (m : nat) (n : nat) : ((term2 m n) = (Nat.pow m n)) = True.
Proof. exact (TRANS (@lem1009206 m n) (@lem1009210 m n)). Qed.
Lemma lem1009212 (m : nat) (n : nat) : True = ((term2 m n) = (Nat.pow m n)).
Proof. exact (SYM (@lem1009211 m n)). Qed.
