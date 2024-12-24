Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249021_term_abbrevs.
Require Import thm1247415_spec.
Lemma lem1248994 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249009 (d' : nat) (p : nat) (d'' : nat) : (term1 d' p d'') = (term1 d' p d'').
Proof. exact (eq_refl (term1 d' p d'')). Qed.
Lemma lem1249010 (p : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 d' p d'' d) = (term3 p d' d'' d''').
Proof. exact (MK_COMB (@lem1249009 d' p d'') (@lem1248994 d d' d'' d''' h1)). Qed.
Lemma lem1249011 (d''' : nat) (d' : nat) (p : nat) (d'' : nat) : (term3 p d' d'' d''') = ((term4 p d'' d''' d') = (Nat.add p d'')).
Proof. exact (eq_refl (term3 p d' d'' d''')). Qed.
Lemma lem1249012 (d' : nat) (p : nat) (d'' : nat) (d : nat) : (term5 d' p d'' d) = (term5 d' p d'' d).
Proof. exact (eq_refl (term5 d' p d'' d)). Qed.
Lemma lem1249013 (d : nat) (d''' : nat) (d' : nat) (p : nat) (d'' : nat) : ((term2 d' p d'' d) = (term3 p d' d'' d''')) = ((term2 d' p d'' d) = ((term4 p d'' d''' d') = (Nat.add p d''))).
Proof. exact (MK_COMB (@lem1249012 d' p d'' d) (@lem1249011 d''' d' p d'')). Qed.
Lemma lem1249014 (d : nat) (d' : nat) (p : nat) (d'' : nat) : (term2 d' p d'' d) = ((term6 p d d') = (Nat.add p d'')).
Proof. exact (eq_refl (term2 d' p d'' d)). Qed.
Lemma lem1249015 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249016 (d : nat) (d' : nat) (p : nat) (d'' : nat) : (term5 d' p d'' d) = (term7 d d' p d'').
Proof. exact (MK_COMB (@lem1249015) (@lem1249014 d d' p d'')). Qed.
Lemma lem1249017 (d''' : nat) (d' : nat) (p : nat) (d'' : nat) : ((term4 p d'' d''' d') = (Nat.add p d'')) = ((term4 p d'' d''' d') = (Nat.add p d'')).
Proof. exact (eq_refl ((term4 p d'' d''' d') = (Nat.add p d''))). Qed.
Lemma lem1249018 (d : nat) (d''' : nat) (d' : nat) (p : nat) (d'' : nat) : ((term2 d' p d'' d) = ((term4 p d'' d''' d') = (Nat.add p d''))) = (((term6 p d d') = (Nat.add p d'')) = ((term4 p d'' d''' d') = (Nat.add p d''))).
Proof. exact (MK_COMB (@lem1249016 d d' p d'') (@lem1249017 d''' d' p d'')). Qed.
Lemma lem1249019 (d : nat) (d''' : nat) (d' : nat) (p : nat) (d'' : nat) : ((term2 d' p d'' d) = (term3 p d' d'' d''')) = (((term6 p d d') = (Nat.add p d'')) = ((term4 p d'' d''' d') = (Nat.add p d''))).
Proof. exact (TRANS (@lem1249013 d d''' d' p d'') (@lem1249018 d d''' d' p d'')). Qed.
Lemma lem1249020 (p : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((term6 p d d') = (Nat.add p d'')) = ((term4 p d'' d''' d') = (Nat.add p d'')).
Proof. exact (EQ_MP (@lem1249019 d d''' d' p d'') (@lem1249010 p d d' d'' d''' h1)). Qed.
Lemma lem1249021 (d''' : nat) (d : nat) (d' : nat) (p : nat) (d'' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : (term6 p d d') = (Nat.add p d'')) : (term4 p d'' d''' d') = (Nat.add p d'').
Proof. exact (EQ_MP (@lem1249020 p d d' d'' d''' h1) (@lem1247415 d d' p d'' h2)). Qed.
