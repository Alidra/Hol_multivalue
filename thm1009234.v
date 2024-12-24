Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1009234_term_abbrevs.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75543_spec.
Lemma lem1009216 (n : nat) : term0 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem1009217 (n : nat) : (term0 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1009222 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem1009217 n) (@lem1009216 n)). Qed.
Lemma lem1009223 (m : nat) : (NUMERAL m) = m.
Proof. exact (@lem1009222 m). Qed.
Lemma lem1009224 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem1009225 (m : nat) : (m = (NUMERAL m)) = (m = m).
Proof. exact (MK_COMB (@lem1009224 m) (@lem1009223 m)). Qed.
Lemma lem1009227 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1009228 (x : nat) : (x = x) = True.
Proof. exact (@lem1009227 nat x). Qed.
Lemma lem1009229 (m : nat) : (m = m) = True.
Proof. exact (@lem1009228 m). Qed.
Lemma lem1009230 (m : nat) : (m = (NUMERAL m)) = True.
Proof. exact (TRANS (@lem1009225 m) (@lem1009229 m)). Qed.
Lemma lem1009231 (m : nat) : True = (m = (NUMERAL m)).
Proof. exact (SYM (@lem1009230 m)). Qed.
Lemma lem1009234 (m : nat) : m = (NUMERAL m).
Proof. exact (EQ_MP (@lem1009231 m) (@lem0)). Qed.
