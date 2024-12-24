Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247318_term_abbrevs.
Lemma lem1247305 (n : nat) (p : nat) (d : nat) (d' : nat) (h1 : n = (term0 p d d')) : n = (term0 p d d').
Proof. exact (h1). Qed.
Lemma lem1247306 (d : nat) (d' : nat) (p : nat) : (term1 d d' p) = (term1 d d' p).
Proof. exact (eq_refl (term1 d d' p)). Qed.
Lemma lem1247307 (n : nat) (p : nat) (d : nat) (d' : nat) (h1 : n = (term0 p d d')) : (term2 d d' p n) = (term3 p d d').
Proof. exact (MK_COMB (@lem1247306 d d' p) (@lem1247305 n p d d' h1)). Qed.
Lemma lem1247308 (d : nat) (d' : nat) (p : nat) : (term3 p d d') = (term4 d d' p).
Proof. exact (eq_refl (term3 p d d')). Qed.
Lemma lem1247309 (d : nat) (d' : nat) (p : nat) (n : nat) : (term5 d d' p n) = (term5 d d' p n).
Proof. exact (eq_refl (term5 d d' p n)). Qed.
Lemma lem1247310 (n : nat) (d : nat) (d' : nat) (p : nat) : ((term2 d d' p n) = (term3 p d d')) = ((term2 d d' p n) = (term4 d d' p)).
Proof. exact (MK_COMB (@lem1247309 d d' p n) (@lem1247308 d d' p)). Qed.
Lemma lem1247311 (d : nat) (d' : nat) (n : nat) (p : nat) : (term2 d d' p n) = (term6 d d' n p).
Proof. exact (eq_refl (term2 d d' p n)). Qed.
Lemma lem1247312 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247313 (d : nat) (d' : nat) (n : nat) (p : nat) : (term5 d d' p n) = (term7 d d' n p).
Proof. exact (MK_COMB (@lem1247312) (@lem1247311 d d' n p)). Qed.
Lemma lem1247314 (d : nat) (d' : nat) (p : nat) : (term4 d d' p) = (term4 d d' p).
Proof. exact (eq_refl (term4 d d' p)). Qed.
Lemma lem1247315 (n : nat) (d : nat) (d' : nat) (p : nat) : ((term2 d d' p n) = (term4 d d' p)) = ((term6 d d' n p) = (term4 d d' p)).
Proof. exact (MK_COMB (@lem1247313 d d' n p) (@lem1247314 d d' p)). Qed.
Lemma lem1247316 (n : nat) (d : nat) (d' : nat) (p : nat) : ((term2 d d' p n) = (term3 p d d')) = ((term6 d d' n p) = (term4 d d' p)).
Proof. exact (TRANS (@lem1247310 n d d' p) (@lem1247315 n d d' p)). Qed.
Lemma lem1247317 (n : nat) (p : nat) (d : nat) (d' : nat) (h1 : n = (term0 p d d')) : (term6 d d' n p) = (term4 d d' p).
Proof. exact (EQ_MP (@lem1247316 n d d' p) (@lem1247307 n p d d' h1)). Qed.
Lemma lem1247318 (n : nat) (p : nat) (d : nat) (d' : nat) (h1 : n = (term0 p d d')) : (term4 d d' p) = (term6 d d' n p).
Proof. exact (SYM (@lem1247317 n p d d' h1)). Qed.
