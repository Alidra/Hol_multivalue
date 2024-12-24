Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841336_term_abbrevs.
Require Import thm2841242_spec.
Lemma lem2841328 (k : nat) (n : nat) (h1 : (term0 k n) = (term1 k n)) : (term0 k n) = (term1 k n).
Proof. exact (h1). Qed.
Lemma lem2841329 (k : nat) (n : nat) (h1 : (term0 k n) = (term1 k n)) : (term1 k n) = (term0 k n).
Proof. exact (SYM (@lem2841328 k n h1)). Qed.
Lemma lem2841330 (k : nat) (n : nat) (h1 : (term1 k n) = (term0 k n)) : (term1 k n) = (term0 k n).
Proof. exact (h1). Qed.
Lemma lem2841331 (k : nat) (n : nat) (h1 : (term1 k n) = (term0 k n)) : (term0 k n) = (term1 k n).
Proof. exact (SYM (@lem2841330 k n h1)). Qed.
Lemma lem2841332 (k : nat) (n : nat) : ((term0 k n) = (term1 k n)) = ((term1 k n) = (term0 k n)).
Proof. exact (prop_ext (fun h1 : (term0 k n) = (term1 k n) => @lem2841329 k n h1) (fun h1 : (term1 k n) = (term0 k n) => @lem2841331 k n h1)). Qed.
Lemma lem2841333 (k : nat) : (term2 k) = (term3 k).
Proof. exact (fun_ext (fun n : nat => @lem2841332 k n)). Qed.
Lemma lem2841334 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2841335 (k : nat) : (term4 k) = (term5 k).
Proof. exact (MK_COMB (@lem2841334) (@lem2841333 k)). Qed.
Lemma lem2841336 (k : nat) : term5 k.
Proof. exact (EQ_MP (@lem2841335 k) (@lem2841242 k)). Qed.
