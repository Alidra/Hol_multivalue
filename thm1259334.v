Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259334_term_abbrevs.
Require Import thm1249196_spec.
Require Import thm1249224_spec.
Require Import thm1259226_spec.
Require Import thm69_spec.
Lemma lem1259330 (d''' : nat) (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : d = (term0 d' d'' d''')) (h2 : m = (Nat.add p d')) (h3 : q = (Nat.add n d'')) (h4 : (Nat.add m n) = (term1 p q d)) : False.
Proof. exact (@lem1259226 p n d' d'' d''' (@lem1249224 d''' d' d'' m n p q d h1 h2 h3 h4)). Qed.
Lemma lem1259331 (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : term2 d d' d'') (h2 : m = (Nat.add p d')) (h3 : q = (Nat.add n d'')) (h4 : (Nat.add m n) = (term1 p q d)) : False.
Proof. exact (ex_elim (@lem1249196 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259330 d''' d' d'' m n p q d h0 h2 h3 h4)). Qed.
Lemma lem1259332 (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add m n) = (term1 p q d)) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259331 d' d'' m n p q d h0 h1 h2 h3). Qed.
Lemma lem1259333 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259334 (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add m n) = (term1 p q d)) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259333 d d' d'') (@lem1259332 d' d'' m n p q d h1 h2 h3)). Qed.
