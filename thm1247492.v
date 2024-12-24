Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247492_term_abbrevs.
Lemma lem1247479 (n : nat) (m : nat) (d' : nat) (h1 : n = (Nat.add m d')) : n = (Nat.add m d').
Proof. exact (h1). Qed.
Lemma lem1247480 (d' : nat) (m : nat) (d : nat) : (term0 d' m d) = (term0 d' m d).
Proof. exact (eq_refl (term0 d' m d)). Qed.
Lemma lem1247481 (d : nat) (n : nat) (m : nat) (d' : nat) (h1 : n = (Nat.add m d')) : (term1 d' m d n) = (term2 d m d').
Proof. exact (MK_COMB (@lem1247480 d' m d) (@lem1247479 n m d' h1)). Qed.
Lemma lem1247482 (d' : nat) (m : nat) (d : nat) : (term2 d m d') = (term3 d' m d).
Proof. exact (eq_refl (term2 d m d')). Qed.
Lemma lem1247483 (d' : nat) (m : nat) (d : nat) (n : nat) : (term4 d' m d n) = (term4 d' m d n).
Proof. exact (eq_refl (term4 d' m d n)). Qed.
Lemma lem1247484 (n : nat) (d' : nat) (m : nat) (d : nat) : ((term1 d' m d n) = (term2 d m d')) = ((term1 d' m d n) = (term3 d' m d)).
Proof. exact (MK_COMB (@lem1247483 d' m d n) (@lem1247482 d' m d)). Qed.
Lemma lem1247485 (d' : nat) (n : nat) (m : nat) (d : nat) : (term1 d' m d n) = (term5 d' n m d).
Proof. exact (eq_refl (term1 d' m d n)). Qed.
Lemma lem1247486 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247487 (d' : nat) (n : nat) (m : nat) (d : nat) : (term4 d' m d n) = (term6 d' n m d).
Proof. exact (MK_COMB (@lem1247486) (@lem1247485 d' n m d)). Qed.
Lemma lem1247488 (d' : nat) (m : nat) (d : nat) : (term3 d' m d) = (term3 d' m d).
Proof. exact (eq_refl (term3 d' m d)). Qed.
Lemma lem1247489 (n : nat) (d' : nat) (m : nat) (d : nat) : ((term1 d' m d n) = (term3 d' m d)) = ((term5 d' n m d) = (term3 d' m d)).
Proof. exact (MK_COMB (@lem1247487 d' n m d) (@lem1247488 d' m d)). Qed.
Lemma lem1247490 (n : nat) (d' : nat) (m : nat) (d : nat) : ((term1 d' m d n) = (term2 d m d')) = ((term5 d' n m d) = (term3 d' m d)).
Proof. exact (TRANS (@lem1247484 n d' m d) (@lem1247489 n d' m d)). Qed.
Lemma lem1247491 (d : nat) (n : nat) (m : nat) (d' : nat) (h1 : n = (Nat.add m d')) : (term5 d' n m d) = (term3 d' m d).
Proof. exact (EQ_MP (@lem1247490 n d' m d) (@lem1247481 d n m d' h1)). Qed.
Lemma lem1247492 (d : nat) (n : nat) (m : nat) (d' : nat) (h1 : n = (Nat.add m d')) : (term3 d' m d) = (term5 d' n m d).
Proof. exact (SYM (@lem1247491 d n m d' h1)). Qed.
