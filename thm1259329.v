Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259329_term_abbrevs.
Require Import thm1249225_spec.
Require Import thm1249253_spec.
Require Import thm1259225_spec.
Require Import thm69_spec.
Lemma lem1259325 (d''' : nat) (d'' : nat) (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : d = (term0 d' d'' d''')) (h2 : n = (Nat.add q d'')) (h3 : p = (Nat.add m d')) (h4 : (Nat.add m n) = (term1 p q d)) : False.
Proof. exact (@lem1259225 m q d' d'' d''' (@lem1249253 d''' d'' d' m n p q d h1 h2 h3 h4)). Qed.
Lemma lem1259326 (d'' : nat) (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : term2 d d' d'') (h2 : n = (Nat.add q d'')) (h3 : p = (Nat.add m d')) (h4 : (Nat.add m n) = (term1 p q d)) : False.
Proof. exact (ex_elim (@lem1249225 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259325 d''' d'' d' m n p q d h0 h2 h3 h4)). Qed.
Lemma lem1259327 (d'' : nat) (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : n = (Nat.add q d'')) (h2 : p = (Nat.add m d')) (h3 : (Nat.add m n) = (term1 p q d)) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259326 d'' d' m n p q d h0 h1 h2 h3). Qed.
Lemma lem1259328 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259329 (d'' : nat) (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : n = (Nat.add q d'')) (h2 : p = (Nat.add m d')) (h3 : (Nat.add m n) = (term1 p q d)) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259328 d d' d'') (@lem1259327 d'' d' m n p q d h1 h2 h3)). Qed.
