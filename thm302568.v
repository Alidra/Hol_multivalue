Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm302568_term_abbrevs.
Require Import MULT_2_spec.
Lemma lem302559 (n : nat) (h1 : (term0 n) = (Nat.add n n)) : (term0 n) = (Nat.add n n).
Proof. exact (h1). Qed.
Lemma lem302560 (n : nat) (h1 : (term0 n) = (Nat.add n n)) : (Nat.add n n) = (term0 n).
Proof. exact (SYM (@lem302559 n h1)). Qed.
Lemma lem302561 (n : nat) (h1 : (Nat.add n n) = (term0 n)) : (Nat.add n n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem302562 (n : nat) (h1 : (Nat.add n n) = (term0 n)) : (term0 n) = (Nat.add n n).
Proof. exact (SYM (@lem302561 n h1)). Qed.
Lemma lem302563 (n : nat) : ((term0 n) = (Nat.add n n)) = ((Nat.add n n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (Nat.add n n) => @lem302560 n h1) (fun h1 : (Nat.add n n) = (term0 n) => @lem302562 n h1)). Qed.
Lemma lem302564 : term1 = term2.
Proof. exact (fun_ext (fun n : nat => @lem302563 n)). Qed.
Lemma lem302565 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem302566 : term3 = term4.
Proof. exact (MK_COMB (@lem302565) (@lem302564)). Qed.
Lemma lem302567 : term4.
Proof. exact (EQ_MP (@lem302566) (@lem84996)). Qed.
Lemma lem302568 (n : nat) : term5 n.
Proof. exact (@lem302567 n). Qed.
