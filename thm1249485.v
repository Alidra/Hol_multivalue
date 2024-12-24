Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249485_term_abbrevs.
Require Import thm1248320_spec.
Lemma lem1249458 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249473 (p : nat) (q : nat) (d'' : nat) (d' : nat) : (term1 p q d'' d') = (term1 p q d'' d').
Proof. exact (eq_refl (term1 p q d'' d')). Qed.
Lemma lem1249474 (p : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 p q d'' d' d) = (term3 p q d' d'' d''').
Proof. exact (MK_COMB (@lem1249473 p q d'' d') (@lem1249458 d d' d'' d''' h1)). Qed.
Lemma lem1249475 (p : nat) (d''' : nat) (q : nat) (d'' : nat) (d' : nat) : (term3 p q d' d'' d''') = ((Nat.add p q) = (term4 p d''' q d'' d')).
Proof. exact (eq_refl (term3 p q d' d'' d''')). Qed.
Lemma lem1249476 (p : nat) (q : nat) (d'' : nat) (d' : nat) (d : nat) : (term5 p q d'' d' d) = (term5 p q d'' d' d).
Proof. exact (eq_refl (term5 p q d'' d' d)). Qed.
Lemma lem1249477 (d : nat) (p : nat) (d''' : nat) (q : nat) (d'' : nat) (d' : nat) : ((term2 p q d'' d' d) = (term3 p q d' d'' d''')) = ((term2 p q d'' d' d) = ((Nat.add p q) = (term4 p d''' q d'' d'))).
Proof. exact (MK_COMB (@lem1249476 p q d'' d' d) (@lem1249475 p d''' q d'' d')). Qed.
Lemma lem1249478 (p : nat) (d : nat) (q : nat) (d'' : nat) (d' : nat) : (term2 p q d'' d' d) = ((Nat.add p q) = (term6 p d q d'' d')).
Proof. exact (eq_refl (term2 p q d'' d' d)). Qed.
Lemma lem1249479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249480 (p : nat) (d : nat) (q : nat) (d'' : nat) (d' : nat) : (term5 p q d'' d' d) = (term7 p d q d'' d').
Proof. exact (MK_COMB (@lem1249479) (@lem1249478 p d q d'' d')). Qed.
Lemma lem1249481 (p : nat) (d''' : nat) (q : nat) (d'' : nat) (d' : nat) : ((Nat.add p q) = (term4 p d''' q d'' d')) = ((Nat.add p q) = (term4 p d''' q d'' d')).
Proof. exact (eq_refl ((Nat.add p q) = (term4 p d''' q d'' d'))). Qed.
Lemma lem1249482 (d : nat) (p : nat) (d''' : nat) (q : nat) (d'' : nat) (d' : nat) : ((term2 p q d'' d' d) = ((Nat.add p q) = (term4 p d''' q d'' d'))) = (((Nat.add p q) = (term6 p d q d'' d')) = ((Nat.add p q) = (term4 p d''' q d'' d'))).
Proof. exact (MK_COMB (@lem1249480 p d q d'' d') (@lem1249481 p d''' q d'' d')). Qed.
Lemma lem1249483 (d : nat) (p : nat) (d''' : nat) (q : nat) (d'' : nat) (d' : nat) : ((term2 p q d'' d' d) = (term3 p q d' d'' d''')) = (((Nat.add p q) = (term6 p d q d'' d')) = ((Nat.add p q) = (term4 p d''' q d'' d'))).
Proof. exact (TRANS (@lem1249477 d p d''' q d'' d') (@lem1249482 d p d''' q d'' d')). Qed.
Lemma lem1249484 (p : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((Nat.add p q) = (term6 p d q d'' d')) = ((Nat.add p q) = (term4 p d''' q d'' d')).
Proof. exact (EQ_MP (@lem1249483 d p d''' q d'' d') (@lem1249474 p q d d' d'' d''' h1)). Qed.
Lemma lem1249485 (d''' : nat) (d'' : nat) (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : n = (Nat.add q d'')) (h3 : (Nat.add p q) = (term8 p d n d')) : (Nat.add p q) = (term4 p d''' q d'' d').
Proof. exact (EQ_MP (@lem1249484 p q d d' d'' d''' h1) (@lem1248320 d'' q p d n d' h2 h3)). Qed.
