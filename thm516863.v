Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516863_term_abbrevs.
Require Import MULT_2_spec.
Lemma lem516855 (n : nat) (h1 : (term0 n) = (Nat.add n n)) : (term0 n) = (Nat.add n n).
Proof. exact (h1). Qed.
Lemma lem516856 (n : nat) (h1 : (term0 n) = (Nat.add n n)) : (Nat.add n n) = (term0 n).
Proof. exact (SYM (@lem516855 n h1)). Qed.
Lemma lem516857 (n : nat) (h1 : (Nat.add n n) = (term0 n)) : (Nat.add n n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem516858 (n : nat) (h1 : (Nat.add n n) = (term0 n)) : (term0 n) = (Nat.add n n).
Proof. exact (SYM (@lem516857 n h1)). Qed.
Lemma lem516859 (n : nat) : ((term0 n) = (Nat.add n n)) = ((Nat.add n n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (Nat.add n n) => @lem516856 n h1) (fun h1 : (Nat.add n n) = (term0 n) => @lem516858 n h1)). Qed.
Lemma lem516860 : term1 = term2.
Proof. exact (fun_ext (fun n : nat => @lem516859 n)). Qed.
Lemma lem516861 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516862 : term3 = term4.
Proof. exact (MK_COMB (@lem516861) (@lem516860)). Qed.
Lemma lem516863 : term4.
Proof. exact (EQ_MP (@lem516862) (@lem84996)). Qed.
