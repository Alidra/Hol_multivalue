Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259319_term_abbrevs.
Require Import thm1249283_spec.
Require Import thm1249311_spec.
Require Import thm1259223_spec.
Require Import thm69_spec.
Lemma lem1259315 (d''' : nat) (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : d = (term0 d' d'' d''')) (h2 : m = (Nat.add p d')) (h3 : n = (Nat.add q d'')) (h4 : (Nat.add p q) = (term1 m n d)) : False.
Proof. exact (@lem1259223 p q d' d'' d''' (@lem1249311 d''' d' d'' p q m n d h1 h2 h3 h4)). Qed.
Lemma lem1259316 (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : term2 d d' d'') (h2 : m = (Nat.add p d')) (h3 : n = (Nat.add q d'')) (h4 : (Nat.add p q) = (term1 m n d)) : False.
Proof. exact (ex_elim (@lem1249283 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259315 d''' d' d'' p q m n d h0 h2 h3 h4)). Qed.
Lemma lem1259317 (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : n = (Nat.add q d'')) (h3 : (Nat.add p q) = (term1 m n d)) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259316 d' d'' p q m n d h0 h1 h2 h3). Qed.
Lemma lem1259318 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259319 (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : n = (Nat.add q d'')) (h3 : (Nat.add p q) = (term1 m n d)) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259318 d d' d'') (@lem1259317 d' d'' p q m n d h1 h2 h3)). Qed.
