Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7932275_term_abbrevs.
Require Import MULT_2_spec.
Lemma lem7932266 (n : nat) (h1 : (term0 n) = (Nat.add n n)) : (term0 n) = (Nat.add n n).
Proof. exact (h1). Qed.
Lemma lem7932267 (n : nat) (h1 : (term0 n) = (Nat.add n n)) : (Nat.add n n) = (term0 n).
Proof. exact (SYM (@lem7932266 n h1)). Qed.
Lemma lem7932268 (n : nat) (h1 : (Nat.add n n) = (term0 n)) : (Nat.add n n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem7932269 (n : nat) (h1 : (Nat.add n n) = (term0 n)) : (term0 n) = (Nat.add n n).
Proof. exact (SYM (@lem7932268 n h1)). Qed.
Lemma lem7932270 (n : nat) : ((term0 n) = (Nat.add n n)) = ((Nat.add n n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (Nat.add n n) => @lem7932267 n h1) (fun h1 : (Nat.add n n) = (term0 n) => @lem7932269 n h1)). Qed.
Lemma lem7932271 : term1 = term2.
Proof. exact (fun_ext (fun n : nat => @lem7932270 n)). Qed.
Lemma lem7932272 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7932273 : term3 = term4.
Proof. exact (MK_COMB (@lem7932272) (@lem7932271)). Qed.
Lemma lem7932274 : term4.
Proof. exact (EQ_MP (@lem7932273) (@lem84996)). Qed.
Lemma lem7932275 (n : nat) : term5 n.
Proof. exact (@lem7932274 n). Qed.
