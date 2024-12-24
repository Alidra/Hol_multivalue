Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247366_term_abbrevs.
Require Import thm1247290_spec.
Lemma lem1247339 (n : nat) (p : nat) (d'' : nat) (h1 : n = (Nat.add p d'')) : n = (Nat.add p d'').
Proof. exact (h1). Qed.
Lemma lem1247354 (p : nat) (d : nat) (d' : nat) : (term0 p d d') = (term0 p d d').
Proof. exact (eq_refl (term0 p d d')). Qed.
Lemma lem1247355 (d : nat) (d' : nat) (n : nat) (p : nat) (d'' : nat) (h1 : n = (Nat.add p d'')) : (term1 p d d' n) = (term2 d d' p d'').
Proof. exact (MK_COMB (@lem1247354 p d d') (@lem1247339 n p d'' h1)). Qed.
Lemma lem1247356 (d : nat) (p : nat) (d'' : nat) (d' : nat) : (term2 d d' p d'') = ((Nat.add p d) = (term3 p d'' d')).
Proof. exact (eq_refl (term2 d d' p d'')). Qed.
Lemma lem1247357 (p : nat) (d : nat) (d' : nat) (n : nat) : (term4 p d d' n) = (term4 p d d' n).
Proof. exact (eq_refl (term4 p d d' n)). Qed.
Lemma lem1247358 (n : nat) (d : nat) (p : nat) (d'' : nat) (d' : nat) : ((term1 p d d' n) = (term2 d d' p d'')) = ((term1 p d d' n) = ((Nat.add p d) = (term3 p d'' d'))).
Proof. exact (MK_COMB (@lem1247357 p d d' n) (@lem1247356 d p d'' d')). Qed.
Lemma lem1247359 (p : nat) (d : nat) (n : nat) (d' : nat) : (term1 p d d' n) = ((Nat.add p d) = (Nat.add n d')).
Proof. exact (eq_refl (term1 p d d' n)). Qed.
Lemma lem1247360 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247361 (p : nat) (d : nat) (n : nat) (d' : nat) : (term4 p d d' n) = (term5 p d n d').
Proof. exact (MK_COMB (@lem1247360) (@lem1247359 p d n d')). Qed.
Lemma lem1247362 (d : nat) (p : nat) (d'' : nat) (d' : nat) : ((Nat.add p d) = (term3 p d'' d')) = ((Nat.add p d) = (term3 p d'' d')).
Proof. exact (eq_refl ((Nat.add p d) = (term3 p d'' d'))). Qed.
Lemma lem1247363 (n : nat) (d : nat) (p : nat) (d'' : nat) (d' : nat) : ((term1 p d d' n) = ((Nat.add p d) = (term3 p d'' d'))) = (((Nat.add p d) = (Nat.add n d')) = ((Nat.add p d) = (term3 p d'' d'))).
Proof. exact (MK_COMB (@lem1247361 p d n d') (@lem1247362 d p d'' d')). Qed.
Lemma lem1247364 (n : nat) (d : nat) (p : nat) (d'' : nat) (d' : nat) : ((term1 p d d' n) = (term2 d d' p d'')) = (((Nat.add p d) = (Nat.add n d')) = ((Nat.add p d) = (term3 p d'' d'))).
Proof. exact (TRANS (@lem1247358 n d p d'' d') (@lem1247363 n d p d'' d')). Qed.
Lemma lem1247365 (d : nat) (d' : nat) (n : nat) (p : nat) (d'' : nat) (h1 : n = (Nat.add p d'')) : ((Nat.add p d) = (Nat.add n d')) = ((Nat.add p d) = (term3 p d'' d')).
Proof. exact (EQ_MP (@lem1247364 n d p d'' d') (@lem1247355 d d' n p d'' h1)). Qed.
Lemma lem1247366 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : n = (Nat.add p d'')) (h2 : (Nat.add p d) = (Nat.add n d')) : (Nat.add p d) = (term3 p d'' d').
Proof. exact (EQ_MP (@lem1247365 d d' n p d'' h1) (@lem1247290 p d n d' h2)). Qed.
