Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247394_term_abbrevs.
Require Import thm1247290_spec.
Lemma lem1247367 (p : nat) (n : nat) (d'' : nat) (h1 : p = (Nat.add n d'')) : p = (Nat.add n d'').
Proof. exact (h1). Qed.
Lemma lem1247382 (d : nat) (n : nat) (d' : nat) : (term0 d n d') = (term0 d n d').
Proof. exact (eq_refl (term0 d n d')). Qed.
Lemma lem1247383 (d : nat) (d' : nat) (p : nat) (n : nat) (d'' : nat) (h1 : p = (Nat.add n d'')) : (term1 d n d' p) = (term2 d d' n d'').
Proof. exact (MK_COMB (@lem1247382 d n d') (@lem1247367 p n d'' h1)). Qed.
Lemma lem1247384 (d'' : nat) (d : nat) (n : nat) (d' : nat) : (term2 d d' n d'') = ((term3 n d'' d) = (Nat.add n d')).
Proof. exact (eq_refl (term2 d d' n d'')). Qed.
Lemma lem1247385 (d : nat) (n : nat) (d' : nat) (p : nat) : (term4 d n d' p) = (term4 d n d' p).
Proof. exact (eq_refl (term4 d n d' p)). Qed.
Lemma lem1247386 (p : nat) (d'' : nat) (d : nat) (n : nat) (d' : nat) : ((term1 d n d' p) = (term2 d d' n d'')) = ((term1 d n d' p) = ((term3 n d'' d) = (Nat.add n d'))).
Proof. exact (MK_COMB (@lem1247385 d n d' p) (@lem1247384 d'' d n d')). Qed.
Lemma lem1247387 (p : nat) (d : nat) (n : nat) (d' : nat) : (term1 d n d' p) = ((Nat.add p d) = (Nat.add n d')).
Proof. exact (eq_refl (term1 d n d' p)). Qed.
Lemma lem1247388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247389 (p : nat) (d : nat) (n : nat) (d' : nat) : (term4 d n d' p) = (term5 p d n d').
Proof. exact (MK_COMB (@lem1247388) (@lem1247387 p d n d')). Qed.
Lemma lem1247390 (d'' : nat) (d : nat) (n : nat) (d' : nat) : ((term3 n d'' d) = (Nat.add n d')) = ((term3 n d'' d) = (Nat.add n d')).
Proof. exact (eq_refl ((term3 n d'' d) = (Nat.add n d'))). Qed.
Lemma lem1247391 (p : nat) (d'' : nat) (d : nat) (n : nat) (d' : nat) : ((term1 d n d' p) = ((term3 n d'' d) = (Nat.add n d'))) = (((Nat.add p d) = (Nat.add n d')) = ((term3 n d'' d) = (Nat.add n d'))).
Proof. exact (MK_COMB (@lem1247389 p d n d') (@lem1247390 d'' d n d')). Qed.
Lemma lem1247392 (p : nat) (d'' : nat) (d : nat) (n : nat) (d' : nat) : ((term1 d n d' p) = (term2 d d' n d'')) = (((Nat.add p d) = (Nat.add n d')) = ((term3 n d'' d) = (Nat.add n d'))).
Proof. exact (TRANS (@lem1247386 p d'' d n d') (@lem1247391 p d'' d n d')). Qed.
Lemma lem1247393 (d : nat) (d' : nat) (p : nat) (n : nat) (d'' : nat) (h1 : p = (Nat.add n d'')) : ((Nat.add p d) = (Nat.add n d')) = ((term3 n d'' d) = (Nat.add n d')).
Proof. exact (EQ_MP (@lem1247392 p d'' d n d') (@lem1247383 d d' p n d'' h1)). Qed.
Lemma lem1247394 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : p = (Nat.add n d'')) (h2 : (Nat.add p d) = (Nat.add n d')) : (term3 n d'' d) = (Nat.add n d').
Proof. exact (EQ_MP (@lem1247393 d d' p n d'' h1) (@lem1247290 p d n d' h2)). Qed.
