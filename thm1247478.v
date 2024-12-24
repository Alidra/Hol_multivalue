Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247478_term_abbrevs.
Lemma lem1247465 (m : nat) (n : nat) (d' : nat) (h1 : m = (Nat.add n d')) : m = (Nat.add n d').
Proof. exact (h1). Qed.
Lemma lem1247466 (d' : nat) (n : nat) (d : nat) : (term0 d' n d) = (term0 d' n d).
Proof. exact (eq_refl (term0 d' n d)). Qed.
Lemma lem1247467 (d : nat) (m : nat) (n : nat) (d' : nat) (h1 : m = (Nat.add n d')) : (term1 d' n d m) = (term2 d n d').
Proof. exact (MK_COMB (@lem1247466 d' n d) (@lem1247465 m n d' h1)). Qed.
Lemma lem1247468 (n : nat) (d' : nat) (d : nat) : (term2 d n d') = (term3 n d' d).
Proof. exact (eq_refl (term2 d n d')). Qed.
Lemma lem1247469 (d' : nat) (n : nat) (d : nat) (m : nat) : (term4 d' n d m) = (term4 d' n d m).
Proof. exact (eq_refl (term4 d' n d m)). Qed.
Lemma lem1247470 (m : nat) (n : nat) (d' : nat) (d : nat) : ((term1 d' n d m) = (term2 d n d')) = ((term1 d' n d m) = (term3 n d' d)).
Proof. exact (MK_COMB (@lem1247469 d' n d m) (@lem1247468 n d' d)). Qed.
Lemma lem1247471 (d' : nat) (n : nat) (m : nat) (d : nat) : (term1 d' n d m) = (term5 d' n m d).
Proof. exact (eq_refl (term1 d' n d m)). Qed.
Lemma lem1247472 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247473 (d' : nat) (n : nat) (m : nat) (d : nat) : (term4 d' n d m) = (term6 d' n m d).
Proof. exact (MK_COMB (@lem1247472) (@lem1247471 d' n m d)). Qed.
Lemma lem1247474 (n : nat) (d' : nat) (d : nat) : (term3 n d' d) = (term3 n d' d).
Proof. exact (eq_refl (term3 n d' d)). Qed.
Lemma lem1247475 (m : nat) (n : nat) (d' : nat) (d : nat) : ((term1 d' n d m) = (term3 n d' d)) = ((term5 d' n m d) = (term3 n d' d)).
Proof. exact (MK_COMB (@lem1247473 d' n m d) (@lem1247474 n d' d)). Qed.
Lemma lem1247476 (m : nat) (n : nat) (d' : nat) (d : nat) : ((term1 d' n d m) = (term2 d n d')) = ((term5 d' n m d) = (term3 n d' d)).
Proof. exact (TRANS (@lem1247470 m n d' d) (@lem1247475 m n d' d)). Qed.
Lemma lem1247477 (d : nat) (m : nat) (n : nat) (d' : nat) (h1 : m = (Nat.add n d')) : (term5 d' n m d) = (term3 n d' d).
Proof. exact (EQ_MP (@lem1247476 m n d' d) (@lem1247467 d m n d' h1)). Qed.
Lemma lem1247478 (d : nat) (m : nat) (n : nat) (d' : nat) (h1 : m = (Nat.add n d')) : (term3 n d' d) = (term5 d' n m d).
Proof. exact (SYM (@lem1247477 d m n d' h1)). Qed.
