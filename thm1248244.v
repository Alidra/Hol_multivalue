Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248244_term_abbrevs.
Require Import thm1248167_spec.
Lemma lem1248217 (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : n = (Nat.add q d'').
Proof. exact (h1). Qed.
Lemma lem1248232 (d : nat) (p : nat) (q : nat) (d' : nat) : (term0 d p q d') = (term0 d p q d').
Proof. exact (eq_refl (term0 d p q d')). Qed.
Lemma lem1248233 (d : nat) (p : nat) (d' : nat) (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : (term1 d p q d' n) = (term2 d p d' q d'').
Proof. exact (MK_COMB (@lem1248232 d p q d') (@lem1248217 n q d'' h1)). Qed.
Lemma lem1248234 (d : nat) (d'' : nat) (p : nat) (q : nat) (d' : nat) : (term2 d p d' q d'') = ((term3 p d q d'') = (term4 p q d')).
Proof. exact (eq_refl (term2 d p d' q d'')). Qed.
Lemma lem1248235 (d : nat) (p : nat) (q : nat) (d' : nat) (n : nat) : (term5 d p q d' n) = (term5 d p q d' n).
Proof. exact (eq_refl (term5 d p q d' n)). Qed.
Lemma lem1248236 (n : nat) (d : nat) (d'' : nat) (p : nat) (q : nat) (d' : nat) : ((term1 d p q d' n) = (term2 d p d' q d'')) = ((term1 d p q d' n) = ((term3 p d q d'') = (term4 p q d'))).
Proof. exact (MK_COMB (@lem1248235 d p q d' n) (@lem1248234 d d'' p q d')). Qed.
Lemma lem1248237 (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) : (term1 d p q d' n) = ((term4 p d n) = (term4 p q d')).
Proof. exact (eq_refl (term1 d p q d' n)). Qed.
Lemma lem1248238 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248239 (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) : (term5 d p q d' n) = (term6 d n p q d').
Proof. exact (MK_COMB (@lem1248238) (@lem1248237 d n p q d')). Qed.
Lemma lem1248240 (d : nat) (d'' : nat) (p : nat) (q : nat) (d' : nat) : ((term3 p d q d'') = (term4 p q d')) = ((term3 p d q d'') = (term4 p q d')).
Proof. exact (eq_refl ((term3 p d q d'') = (term4 p q d'))). Qed.
Lemma lem1248241 (n : nat) (d : nat) (d'' : nat) (p : nat) (q : nat) (d' : nat) : ((term1 d p q d' n) = ((term3 p d q d'') = (term4 p q d'))) = (((term4 p d n) = (term4 p q d')) = ((term3 p d q d'') = (term4 p q d'))).
Proof. exact (MK_COMB (@lem1248239 d n p q d') (@lem1248240 d d'' p q d')). Qed.
Lemma lem1248242 (n : nat) (d : nat) (d'' : nat) (p : nat) (q : nat) (d' : nat) : ((term1 d p q d' n) = (term2 d p d' q d'')) = (((term4 p d n) = (term4 p q d')) = ((term3 p d q d'') = (term4 p q d'))).
Proof. exact (TRANS (@lem1248236 n d d'' p q d') (@lem1248241 n d d'' p q d')). Qed.
Lemma lem1248243 (d : nat) (p : nat) (d' : nat) (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : ((term4 p d n) = (term4 p q d')) = ((term3 p d q d'') = (term4 p q d')).
Proof. exact (EQ_MP (@lem1248242 n d d'' p q d') (@lem1248233 d p d' n q d'' h1)). Qed.
Lemma lem1248244 (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : n = (Nat.add q d'')) (h2 : (term4 p d n) = (term4 p q d')) : (term3 p d q d'') = (term4 p q d').
Proof. exact (EQ_MP (@lem1248243 d p d' n q d'' h1) (@lem1248167 d n p q d' h2)). Qed.
