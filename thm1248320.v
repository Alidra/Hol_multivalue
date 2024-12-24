Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248320_term_abbrevs.
Require Import thm1248182_spec.
Lemma lem1248293 (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : n = (Nat.add q d'').
Proof. exact (h1). Qed.
Lemma lem1248308 (q : nat) (p : nat) (d : nat) (d' : nat) : (term0 q p d d') = (term0 q p d d').
Proof. exact (eq_refl (term0 q p d d')). Qed.
Lemma lem1248309 (p : nat) (d : nat) (d' : nat) (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : (term1 q p d d' n) = (term2 p d d' q d'').
Proof. exact (MK_COMB (@lem1248308 q p d d') (@lem1248293 n q d'' h1)). Qed.
Lemma lem1248310 (p : nat) (d : nat) (q : nat) (d'' : nat) (d' : nat) : (term2 p d d' q d'') = ((Nat.add p q) = (term3 p d q d'' d')).
Proof. exact (eq_refl (term2 p d d' q d'')). Qed.
Lemma lem1248311 (q : nat) (p : nat) (d : nat) (d' : nat) (n : nat) : (term4 q p d d' n) = (term4 q p d d' n).
Proof. exact (eq_refl (term4 q p d d' n)). Qed.
Lemma lem1248312 (n : nat) (p : nat) (d : nat) (q : nat) (d'' : nat) (d' : nat) : ((term1 q p d d' n) = (term2 p d d' q d'')) = ((term1 q p d d' n) = ((Nat.add p q) = (term3 p d q d'' d'))).
Proof. exact (MK_COMB (@lem1248311 q p d d' n) (@lem1248310 p d q d'' d')). Qed.
Lemma lem1248313 (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) : (term1 q p d d' n) = ((Nat.add p q) = (term5 p d n d')).
Proof. exact (eq_refl (term1 q p d d' n)). Qed.
Lemma lem1248314 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248315 (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) : (term4 q p d d' n) = (term6 q p d n d').
Proof. exact (MK_COMB (@lem1248314) (@lem1248313 q p d n d')). Qed.
Lemma lem1248316 (p : nat) (d : nat) (q : nat) (d'' : nat) (d' : nat) : ((Nat.add p q) = (term3 p d q d'' d')) = ((Nat.add p q) = (term3 p d q d'' d')).
Proof. exact (eq_refl ((Nat.add p q) = (term3 p d q d'' d'))). Qed.
Lemma lem1248317 (n : nat) (p : nat) (d : nat) (q : nat) (d'' : nat) (d' : nat) : ((term1 q p d d' n) = ((Nat.add p q) = (term3 p d q d'' d'))) = (((Nat.add p q) = (term5 p d n d')) = ((Nat.add p q) = (term3 p d q d'' d'))).
Proof. exact (MK_COMB (@lem1248315 q p d n d') (@lem1248316 p d q d'' d')). Qed.
Lemma lem1248318 (n : nat) (p : nat) (d : nat) (q : nat) (d'' : nat) (d' : nat) : ((term1 q p d d' n) = (term2 p d d' q d'')) = (((Nat.add p q) = (term5 p d n d')) = ((Nat.add p q) = (term3 p d q d'' d'))).
Proof. exact (TRANS (@lem1248312 n p d q d'' d') (@lem1248317 n p d q d'' d')). Qed.
Lemma lem1248319 (p : nat) (d : nat) (d' : nat) (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : ((Nat.add p q) = (term5 p d n d')) = ((Nat.add p q) = (term3 p d q d'' d')).
Proof. exact (EQ_MP (@lem1248318 n p d q d'' d') (@lem1248309 p d d' n q d'' h1)). Qed.
Lemma lem1248320 (d'' : nat) (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : n = (Nat.add q d'')) (h2 : (Nat.add p q) = (term5 p d n d')) : (Nat.add p q) = (term3 p d q d'' d').
Proof. exact (EQ_MP (@lem1248319 p d d' n q d'' h1) (@lem1248182 q p d n d' h2)). Qed.
