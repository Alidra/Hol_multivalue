Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248348_term_abbrevs.
Require Import thm1248182_spec.
Lemma lem1248321 (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : q = (Nat.add n d'').
Proof. exact (h1). Qed.
Lemma lem1248336 (p : nat) (d : nat) (n : nat) (d' : nat) : (term0 p d n d') = (term0 p d n d').
Proof. exact (eq_refl (term0 p d n d')). Qed.
Lemma lem1248337 (p : nat) (d : nat) (d' : nat) (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : (term1 p d n d' q) = (term2 p d d' n d'').
Proof. exact (MK_COMB (@lem1248336 p d n d') (@lem1248321 q n d'' h1)). Qed.
Lemma lem1248338 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) : (term2 p d d' n d'') = ((term3 p n d'') = (term4 p d n d')).
Proof. exact (eq_refl (term2 p d d' n d'')). Qed.
Lemma lem1248339 (p : nat) (d : nat) (n : nat) (d' : nat) (q : nat) : (term5 p d n d' q) = (term5 p d n d' q).
Proof. exact (eq_refl (term5 p d n d' q)). Qed.
Lemma lem1248340 (q : nat) (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) : ((term1 p d n d' q) = (term2 p d d' n d'')) = ((term1 p d n d' q) = ((term3 p n d'') = (term4 p d n d'))).
Proof. exact (MK_COMB (@lem1248339 p d n d' q) (@lem1248338 d'' p d n d')). Qed.
Lemma lem1248341 (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) : (term1 p d n d' q) = ((Nat.add p q) = (term4 p d n d')).
Proof. exact (eq_refl (term1 p d n d' q)). Qed.
Lemma lem1248342 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248343 (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) : (term5 p d n d' q) = (term6 q p d n d').
Proof. exact (MK_COMB (@lem1248342) (@lem1248341 q p d n d')). Qed.
Lemma lem1248344 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) : ((term3 p n d'') = (term4 p d n d')) = ((term3 p n d'') = (term4 p d n d')).
Proof. exact (eq_refl ((term3 p n d'') = (term4 p d n d'))). Qed.
Lemma lem1248345 (q : nat) (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) : ((term1 p d n d' q) = ((term3 p n d'') = (term4 p d n d'))) = (((Nat.add p q) = (term4 p d n d')) = ((term3 p n d'') = (term4 p d n d'))).
Proof. exact (MK_COMB (@lem1248343 q p d n d') (@lem1248344 d'' p d n d')). Qed.
Lemma lem1248346 (q : nat) (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) : ((term1 p d n d' q) = (term2 p d d' n d'')) = (((Nat.add p q) = (term4 p d n d')) = ((term3 p n d'') = (term4 p d n d'))).
Proof. exact (TRANS (@lem1248340 q d'' p d n d') (@lem1248345 q d'' p d n d')). Qed.
Lemma lem1248347 (p : nat) (d : nat) (d' : nat) (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : ((Nat.add p q) = (term4 p d n d')) = ((term3 p n d'') = (term4 p d n d')).
Proof. exact (EQ_MP (@lem1248346 q d'' p d n d') (@lem1248337 p d d' q n d'' h1)). Qed.
Lemma lem1248348 (d'' : nat) (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : q = (Nat.add n d'')) (h2 : (Nat.add p q) = (term4 p d n d')) : (term3 p n d'') = (term4 p d n d').
Proof. exact (EQ_MP (@lem1248347 p d d' q n d'' h1) (@lem1248182 q p d n d' h2)). Qed.
