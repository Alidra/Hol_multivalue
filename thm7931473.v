Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7931473_term_abbrevs.
Require Import MULT_2_spec.
Lemma lem7931464 (n : nat) (h1 : (term0 n) = (Nat.add n n)) : (term0 n) = (Nat.add n n).
Proof. exact (h1). Qed.
Lemma lem7931465 (n : nat) (h1 : (term0 n) = (Nat.add n n)) : (Nat.add n n) = (term0 n).
Proof. exact (SYM (@lem7931464 n h1)). Qed.
Lemma lem7931466 (n : nat) (h1 : (Nat.add n n) = (term0 n)) : (Nat.add n n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem7931467 (n : nat) (h1 : (Nat.add n n) = (term0 n)) : (term0 n) = (Nat.add n n).
Proof. exact (SYM (@lem7931466 n h1)). Qed.
Lemma lem7931468 (n : nat) : ((term0 n) = (Nat.add n n)) = ((Nat.add n n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (Nat.add n n) => @lem7931465 n h1) (fun h1 : (Nat.add n n) = (term0 n) => @lem7931467 n h1)). Qed.
Lemma lem7931469 : term1 = term2.
Proof. exact (fun_ext (fun n : nat => @lem7931468 n)). Qed.
Lemma lem7931470 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7931471 : term3 = term4.
Proof. exact (MK_COMB (@lem7931470) (@lem7931469)). Qed.
Lemma lem7931472 : term4.
Proof. exact (EQ_MP (@lem7931471) (@lem84996)). Qed.
Lemma lem7931473 (n : nat) : term5 n.
Proof. exact (@lem7931472 n). Qed.
