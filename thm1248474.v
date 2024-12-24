Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248474_term_abbrevs.
Require Import thm1248369_spec.
Lemma lem1248447 (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : q = (Nat.add n d'').
Proof. exact (h1). Qed.
Lemma lem1248462 (n : nat) (m : nat) (d : nat) (d' : nat) : (term0 n m d d') = (term0 n m d d').
Proof. exact (eq_refl (term0 n m d d')). Qed.
Lemma lem1248463 (m : nat) (d : nat) (d' : nat) (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : (term1 n m d d' q) = (term2 m d d' n d'').
Proof. exact (MK_COMB (@lem1248462 n m d d') (@lem1248447 q n d'' h1)). Qed.
Lemma lem1248464 (m : nat) (d : nat) (n : nat) (d'' : nat) (d' : nat) : (term2 m d d' n d'') = ((Nat.add m n) = (term3 m d n d'' d')).
Proof. exact (eq_refl (term2 m d d' n d'')). Qed.
Lemma lem1248465 (n : nat) (m : nat) (d : nat) (d' : nat) (q : nat) : (term4 n m d d' q) = (term4 n m d d' q).
Proof. exact (eq_refl (term4 n m d d' q)). Qed.
Lemma lem1248466 (q : nat) (m : nat) (d : nat) (n : nat) (d'' : nat) (d' : nat) : ((term1 n m d d' q) = (term2 m d d' n d'')) = ((term1 n m d d' q) = ((Nat.add m n) = (term3 m d n d'' d'))).
Proof. exact (MK_COMB (@lem1248465 n m d d' q) (@lem1248464 m d n d'' d')). Qed.
Lemma lem1248467 (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) : (term1 n m d d' q) = ((Nat.add m n) = (term5 m d q d')).
Proof. exact (eq_refl (term1 n m d d' q)). Qed.
Lemma lem1248468 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248469 (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) : (term4 n m d d' q) = (term6 n m d q d').
Proof. exact (MK_COMB (@lem1248468) (@lem1248467 n m d q d')). Qed.
Lemma lem1248470 (m : nat) (d : nat) (n : nat) (d'' : nat) (d' : nat) : ((Nat.add m n) = (term3 m d n d'' d')) = ((Nat.add m n) = (term3 m d n d'' d')).
Proof. exact (eq_refl ((Nat.add m n) = (term3 m d n d'' d'))). Qed.
Lemma lem1248471 (q : nat) (m : nat) (d : nat) (n : nat) (d'' : nat) (d' : nat) : ((term1 n m d d' q) = ((Nat.add m n) = (term3 m d n d'' d'))) = (((Nat.add m n) = (term5 m d q d')) = ((Nat.add m n) = (term3 m d n d'' d'))).
Proof. exact (MK_COMB (@lem1248469 n m d q d') (@lem1248470 m d n d'' d')). Qed.
Lemma lem1248472 (q : nat) (m : nat) (d : nat) (n : nat) (d'' : nat) (d' : nat) : ((term1 n m d d' q) = (term2 m d d' n d'')) = (((Nat.add m n) = (term5 m d q d')) = ((Nat.add m n) = (term3 m d n d'' d'))).
Proof. exact (TRANS (@lem1248466 q m d n d'' d') (@lem1248471 q m d n d'' d')). Qed.
Lemma lem1248473 (m : nat) (d : nat) (d' : nat) (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : ((Nat.add m n) = (term5 m d q d')) = ((Nat.add m n) = (term3 m d n d'' d')).
Proof. exact (EQ_MP (@lem1248472 q m d n d'' d') (@lem1248463 m d d' q n d'' h1)). Qed.
Lemma lem1248474 (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : q = (Nat.add n d'')) (h2 : (Nat.add m n) = (term5 m d q d')) : (Nat.add m n) = (term3 m d n d'' d').
Proof. exact (EQ_MP (@lem1248473 m d d' q n d'' h1) (@lem1248369 n m d q d' h2)). Qed.
