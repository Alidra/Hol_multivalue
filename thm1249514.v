Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249514_term_abbrevs.
Require Import thm1248348_spec.
Lemma lem1249487 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249502 (d'' : nat) (p : nat) (n : nat) (d' : nat) : (term1 d'' p n d') = (term1 d'' p n d').
Proof. exact (eq_refl (term1 d'' p n d')). Qed.
Lemma lem1249503 (p : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 d'' p n d' d) = (term3 p n d' d'' d''').
Proof. exact (MK_COMB (@lem1249502 d'' p n d') (@lem1249487 d d' d'' d''' h1)). Qed.
Lemma lem1249504 (p : nat) (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : (term3 p n d' d'' d''') = ((term4 p n d'') = (term5 p d'' d''' n d')).
Proof. exact (eq_refl (term3 p n d' d'' d''')). Qed.
Lemma lem1249505 (d'' : nat) (p : nat) (n : nat) (d' : nat) (d : nat) : (term6 d'' p n d' d) = (term6 d'' p n d' d).
Proof. exact (eq_refl (term6 d'' p n d' d)). Qed.
Lemma lem1249506 (d : nat) (p : nat) (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : ((term2 d'' p n d' d) = (term3 p n d' d'' d''')) = ((term2 d'' p n d' d) = ((term4 p n d'') = (term5 p d'' d''' n d'))).
Proof. exact (MK_COMB (@lem1249505 d'' p n d' d) (@lem1249504 p d'' d''' n d')). Qed.
Lemma lem1249507 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) : (term2 d'' p n d' d) = ((term4 p n d'') = (term7 p d n d')).
Proof. exact (eq_refl (term2 d'' p n d' d)). Qed.
Lemma lem1249508 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249509 (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) : (term6 d'' p n d' d) = (term8 d'' p d n d').
Proof. exact (MK_COMB (@lem1249508) (@lem1249507 d'' p d n d')). Qed.
Lemma lem1249510 (p : nat) (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : ((term4 p n d'') = (term5 p d'' d''' n d')) = ((term4 p n d'') = (term5 p d'' d''' n d')).
Proof. exact (eq_refl ((term4 p n d'') = (term5 p d'' d''' n d'))). Qed.
Lemma lem1249511 (d : nat) (p : nat) (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : ((term2 d'' p n d' d) = ((term4 p n d'') = (term5 p d'' d''' n d'))) = (((term4 p n d'') = (term7 p d n d')) = ((term4 p n d'') = (term5 p d'' d''' n d'))).
Proof. exact (MK_COMB (@lem1249509 d'' p d n d') (@lem1249510 p d'' d''' n d')). Qed.
Lemma lem1249512 (d : nat) (p : nat) (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : ((term2 d'' p n d' d) = (term3 p n d' d'' d''')) = (((term4 p n d'') = (term7 p d n d')) = ((term4 p n d'') = (term5 p d'' d''' n d'))).
Proof. exact (TRANS (@lem1249506 d p d'' d''' n d') (@lem1249511 d p d'' d''' n d')). Qed.
Lemma lem1249513 (p : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((term4 p n d'') = (term7 p d n d')) = ((term4 p n d'') = (term5 p d'' d''' n d')).
Proof. exact (EQ_MP (@lem1249512 d p d'' d''' n d') (@lem1249503 p n d d' d'' d''' h1)). Qed.
Lemma lem1249514 (d''' : nat) (d'' : nat) (q : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add p q) = (term7 p d n d')) : (term4 p n d'') = (term5 p d'' d''' n d').
Proof. exact (EQ_MP (@lem1249513 p n d d' d'' d''' h1) (@lem1248348 d'' q p d n d' h2 h3)). Qed.
