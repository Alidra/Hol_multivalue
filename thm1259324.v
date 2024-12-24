Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259324_term_abbrevs.
Require Import thm1249254_spec.
Require Import thm1249282_spec.
Require Import thm1259224_spec.
Require Import thm69_spec.
Lemma lem1259320 (d''' : nat) (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : d = (term0 d' d'' d''')) (h2 : p = (Nat.add m d')) (h3 : q = (Nat.add n d'')) (h4 : (Nat.add m n) = (term1 p q d)) : False.
Proof. exact (@lem1259224 m n d' d'' d''' (@lem1249282 d''' d' d'' m n p q d h1 h2 h3 h4)). Qed.
Lemma lem1259321 (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : term2 d d' d'') (h2 : p = (Nat.add m d')) (h3 : q = (Nat.add n d'')) (h4 : (Nat.add m n) = (term1 p q d)) : False.
Proof. exact (ex_elim (@lem1249254 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259320 d''' d' d'' m n p q d h0 h2 h3 h4)). Qed.
Lemma lem1259322 (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add m n) = (term1 p q d)) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259321 d' d'' m n p q d h0 h1 h2 h3). Qed.
Lemma lem1259323 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259324 (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add m n) = (term1 p q d)) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259323 d d' d'') (@lem1259322 d' d'' m n p q d h1 h2 h3)). Qed.
