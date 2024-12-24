Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259304_term_abbrevs.
Require Import thm1249370_spec.
Require Import thm1249398_spec.
Require Import thm1259220_spec.
Require Import thm69_spec.
Lemma lem1259300 (d''' : nat) (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : d = (term0 d' d'' d''')) (h2 : p = (Nat.add m d')) (h3 : q = (Nat.add n d'')) (h4 : (Nat.add p q) = (term1 m n d)) : False.
Proof. exact (@lem1259220 m n d' d'' d''' (@lem1249398 d''' d' d'' p q m n d h1 h2 h3 h4)). Qed.
Lemma lem1259301 (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : term2 d d' d'') (h2 : p = (Nat.add m d')) (h3 : q = (Nat.add n d'')) (h4 : (Nat.add p q) = (term1 m n d)) : False.
Proof. exact (ex_elim (@lem1249370 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259300 d''' d' d'' p q m n d h0 h2 h3 h4)). Qed.
Lemma lem1259302 (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add p q) = (term1 m n d)) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259301 d' d'' p q m n d h0 h1 h2 h3). Qed.
Lemma lem1259303 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259304 (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add p q) = (term1 m n d)) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259303 d d' d'') (@lem1259302 d' d'' p q m n d h1 h2 h3)). Qed.
