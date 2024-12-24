Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259299_term_abbrevs.
Require Import thm1249399_spec.
Require Import thm1249427_spec.
Require Import thm1259219_spec.
Require Import thm69_spec.
Lemma lem1259295 (d''' : nat) (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : n = (Nat.add q d'')) (h3 : (term1 p d n) = (term1 p q d')) : False.
Proof. exact (@lem1259219 d''' d'' p q d' (@lem1249427 d''' d'' d n p q d' h1 h2 h3)). Qed.
Lemma lem1259296 (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : term2 d d' d'') (h2 : n = (Nat.add q d'')) (h3 : (term1 p d n) = (term1 p q d')) : False.
Proof. exact (ex_elim (@lem1249399 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259295 d''' d'' d n p q d' h0 h2 h3)). Qed.
Lemma lem1259297 (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : n = (Nat.add q d'')) (h2 : (term1 p d n) = (term1 p q d')) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259296 d'' d n p q d' h0 h1 h2). Qed.
Lemma lem1259298 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259299 (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : n = (Nat.add q d'')) (h2 : (term1 p d n) = (term1 p q d')) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259298 d d' d'') (@lem1259297 d'' d n p q d' h1 h2)). Qed.
