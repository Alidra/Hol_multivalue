Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259314_term_abbrevs.
Require Import thm1249312_spec.
Require Import thm1249340_spec.
Require Import thm1259222_spec.
Require Import thm69_spec.
Lemma lem1259310 (d''' : nat) (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : d = (term0 d' d'' d''')) (h2 : m = (Nat.add p d')) (h3 : q = (Nat.add n d'')) (h4 : (Nat.add p q) = (term1 m n d)) : False.
Proof. exact (@lem1259222 p n d' d'' d''' (@lem1249340 d''' d' d'' p q m n d h1 h2 h3 h4)). Qed.
Lemma lem1259311 (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : term2 d d' d'') (h2 : m = (Nat.add p d')) (h3 : q = (Nat.add n d'')) (h4 : (Nat.add p q) = (term1 m n d)) : False.
Proof. exact (ex_elim (@lem1249312 d d' d'' h1) (fun d''' : nat => fun h0 : term3 d d' d'' d''' => @lem1259310 d''' d' d'' p q m n d h0 h2 h3 h4)). Qed.
Lemma lem1259312 (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add p q) = (term1 m n d)) : term4 d d' d''.
Proof. exact (fun h0 : term2 d d' d'' => @lem1259311 d' d'' p q m n d h0 h1 h2 h3). Qed.
Lemma lem1259313 (d : nat) (d' : nat) (d'' : nat) : (term4 d d' d'') = (term5 d d' d'').
Proof. exact (@lem69 (term2 d d' d'')). Qed.
Lemma lem1259314 (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add p q) = (term1 m n d)) : term5 d d' d''.
Proof. exact (EQ_MP (@lem1259313 d d' d'') (@lem1259312 d' d'' p q m n d h1 h2 h3)). Qed.
