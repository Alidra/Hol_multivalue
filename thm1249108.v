Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249108_term_abbrevs.
Require Import thm1247528_spec.
Lemma lem1249081 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249096 (d' : nat) (n : nat) (d'' : nat) : (term1 d' n d'') = (term1 d' n d'').
Proof. exact (eq_refl (term1 d' n d'')). Qed.
Lemma lem1249097 (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 d' n d'' d) = (term3 n d' d'' d''').
Proof. exact (MK_COMB (@lem1249096 d' n d'') (@lem1249081 d d' d'' d''' h1)). Qed.
Lemma lem1249098 (d' : nat) (d''' : nat) (n : nat) (d'' : nat) : (term3 n d' d'' d''') = ((term4 n d' d'' d''') = (Nat.add n d'')).
Proof. exact (eq_refl (term3 n d' d'' d''')). Qed.
Lemma lem1249099 (d' : nat) (n : nat) (d'' : nat) (d : nat) : (term5 d' n d'' d) = (term5 d' n d'' d).
Proof. exact (eq_refl (term5 d' n d'' d)). Qed.
Lemma lem1249100 (d : nat) (d' : nat) (d''' : nat) (n : nat) (d'' : nat) : ((term2 d' n d'' d) = (term3 n d' d'' d''')) = ((term2 d' n d'' d) = ((term4 n d' d'' d''') = (Nat.add n d''))).
Proof. exact (MK_COMB (@lem1249099 d' n d'' d) (@lem1249098 d' d''' n d'')). Qed.
Lemma lem1249101 (d' : nat) (d : nat) (n : nat) (d'' : nat) : (term2 d' n d'' d) = ((term6 n d' d) = (Nat.add n d'')).
Proof. exact (eq_refl (term2 d' n d'' d)). Qed.
Lemma lem1249102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249103 (d' : nat) (d : nat) (n : nat) (d'' : nat) : (term5 d' n d'' d) = (term7 d' d n d'').
Proof. exact (MK_COMB (@lem1249102) (@lem1249101 d' d n d'')). Qed.
Lemma lem1249104 (d' : nat) (d''' : nat) (n : nat) (d'' : nat) : ((term4 n d' d'' d''') = (Nat.add n d'')) = ((term4 n d' d'' d''') = (Nat.add n d'')).
Proof. exact (eq_refl ((term4 n d' d'' d''') = (Nat.add n d''))). Qed.
Lemma lem1249105 (d : nat) (d' : nat) (d''' : nat) (n : nat) (d'' : nat) : ((term2 d' n d'' d) = ((term4 n d' d'' d''') = (Nat.add n d''))) = (((term6 n d' d) = (Nat.add n d'')) = ((term4 n d' d'' d''') = (Nat.add n d''))).
Proof. exact (MK_COMB (@lem1249103 d' d n d'') (@lem1249104 d' d''' n d'')). Qed.
Lemma lem1249106 (d : nat) (d' : nat) (d''' : nat) (n : nat) (d'' : nat) : ((term2 d' n d'' d) = (term3 n d' d'' d''')) = (((term6 n d' d) = (Nat.add n d'')) = ((term4 n d' d'' d''') = (Nat.add n d''))).
Proof. exact (TRANS (@lem1249100 d d' d''' n d'') (@lem1249105 d d' d''' n d'')). Qed.
Lemma lem1249107 (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((term6 n d' d) = (Nat.add n d'')) = ((term4 n d' d'' d''') = (Nat.add n d'')).
Proof. exact (EQ_MP (@lem1249106 d d' d''' n d'') (@lem1249097 n d d' d'' d''' h1)). Qed.
Lemma lem1249108 (d''' : nat) (d' : nat) (d : nat) (n : nat) (d'' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : (term6 n d' d) = (Nat.add n d'')) : (term4 n d' d'' d''') = (Nat.add n d'').
Proof. exact (EQ_MP (@lem1249107 n d d' d'' d''' h1) (@lem1247528 d' d n d'' h2)). Qed.
