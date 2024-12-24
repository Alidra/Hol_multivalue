Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259289_term_abbrevs.
Require Import thm1249457_spec.
Require Import thm1249485_spec.
Require Import thm1259217_spec.
Require Import thm69_spec.
Lemma lem1259285 (d''' : nat) (d'' : nat) (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : n = (Nat.add q d'')) (h3 : (Nat.add p q) = (term1 p d n d')) : False.
Proof. exact (@lem1259217 p d''' q d'' d' (@lem1249485 d''' d'' q p d n d' h1 h2 h3)). Qed.
Lemma lem1259286 (d'' : nat) (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : term2 d d' d'') (h2 : n = (Nat.add q d'')) (h3 : (Nat.add p q) = (term1 p d n d')) : False.
Proof. exact (ex_elim (@lem1249457 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259285 d''' d'' q p d n d' h0 h2 h3)). Qed.
Lemma lem1259287 (d'' : nat) (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : n = (Nat.add q d'')) (h2 : (Nat.add p q) = (term1 p d n d')) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259286 d'' q p d n d' h0 h1 h2). Qed.
Lemma lem1259288 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259289 (d'' : nat) (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : n = (Nat.add q d'')) (h2 : (Nat.add p q) = (term1 p d n d')) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259288 d d' d'') (@lem1259287 d'' q p d n d' h1 h2)). Qed.
