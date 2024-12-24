Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm522176_term_abbrevs.
Require Import MULT_2_spec.
Lemma lem522168 (n : nat) (h1 : (term0 n) = (Nat.add n n)) : (term0 n) = (Nat.add n n).
Proof. exact (h1). Qed.
Lemma lem522169 (n : nat) (h1 : (term0 n) = (Nat.add n n)) : (Nat.add n n) = (term0 n).
Proof. exact (SYM (@lem522168 n h1)). Qed.
Lemma lem522170 (n : nat) (h1 : (Nat.add n n) = (term0 n)) : (Nat.add n n) = (term0 n).
Proof. exact (h1). Qed.
Lemma lem522171 (n : nat) (h1 : (Nat.add n n) = (term0 n)) : (term0 n) = (Nat.add n n).
Proof. exact (SYM (@lem522170 n h1)). Qed.
Lemma lem522172 (n : nat) : ((term0 n) = (Nat.add n n)) = ((Nat.add n n) = (term0 n)).
Proof. exact (prop_ext (fun h1 : (term0 n) = (Nat.add n n) => @lem522169 n h1) (fun h1 : (Nat.add n n) = (term0 n) => @lem522171 n h1)). Qed.
Lemma lem522173 : term1 = term2.
Proof. exact (fun_ext (fun n : nat => @lem522172 n)). Qed.
Lemma lem522174 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem522175 : term3 = term4.
Proof. exact (MK_COMB (@lem522174) (@lem522173)). Qed.
Lemma lem522176 : term4.
Proof. exact (EQ_MP (@lem522175) (@lem84996)). Qed.
