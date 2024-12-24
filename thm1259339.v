Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259339_term_abbrevs.
Require Import thm1249167_spec.
Require Import thm1249195_spec.
Require Import thm1259227_spec.
Require Import thm69_spec.
Lemma lem1259335 (d''' : nat) (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : d = (term0 d' d'' d''')) (h2 : m = (Nat.add p d')) (h3 : n = (Nat.add q d'')) (h4 : (Nat.add m n) = (term1 p q d)) : False.
Proof. exact (@lem1259227 p q d' d'' d''' (@lem1249195 d''' d' d'' m n p q d h1 h2 h3 h4)). Qed.
Lemma lem1259336 (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : term2 d d' d'') (h2 : m = (Nat.add p d')) (h3 : n = (Nat.add q d'')) (h4 : (Nat.add m n) = (term1 p q d)) : False.
Proof. exact (ex_elim (@lem1249167 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259335 d''' d' d'' m n p q d h0 h2 h3 h4)). Qed.
Lemma lem1259337 (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : n = (Nat.add q d'')) (h3 : (Nat.add m n) = (term1 p q d)) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259336 d' d'' m n p q d h0 h1 h2 h3). Qed.
Lemma lem1259338 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259339 (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : n = (Nat.add q d'')) (h3 : (Nat.add m n) = (term1 p q d)) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259338 d d' d'') (@lem1259337 d' d'' m n p q d h1 h2 h3)). Qed.
