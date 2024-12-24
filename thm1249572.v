Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249572_term_abbrevs.
Require Import thm1248474_spec.
Lemma lem1249545 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249560 (m : nat) (n : nat) (d'' : nat) (d' : nat) : (term1 m n d'' d') = (term1 m n d'' d').
Proof. exact (eq_refl (term1 m n d'' d')). Qed.
Lemma lem1249561 (m : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 m n d'' d' d) = (term3 m n d' d'' d''').
Proof. exact (MK_COMB (@lem1249560 m n d'' d') (@lem1249545 d d' d'' d''' h1)). Qed.
Lemma lem1249562 (m : nat) (d''' : nat) (n : nat) (d'' : nat) (d' : nat) : (term3 m n d' d'' d''') = ((Nat.add m n) = (term4 m d''' n d'' d')).
Proof. exact (eq_refl (term3 m n d' d'' d''')). Qed.
Lemma lem1249563 (m : nat) (n : nat) (d'' : nat) (d' : nat) (d : nat) : (term5 m n d'' d' d) = (term5 m n d'' d' d).
Proof. exact (eq_refl (term5 m n d'' d' d)). Qed.
Lemma lem1249564 (d : nat) (m : nat) (d''' : nat) (n : nat) (d'' : nat) (d' : nat) : ((term2 m n d'' d' d) = (term3 m n d' d'' d''')) = ((term2 m n d'' d' d) = ((Nat.add m n) = (term4 m d''' n d'' d'))).
Proof. exact (MK_COMB (@lem1249563 m n d'' d' d) (@lem1249562 m d''' n d'' d')). Qed.
Lemma lem1249565 (m : nat) (d : nat) (n : nat) (d'' : nat) (d' : nat) : (term2 m n d'' d' d) = ((Nat.add m n) = (term6 m d n d'' d')).
Proof. exact (eq_refl (term2 m n d'' d' d)). Qed.
Lemma lem1249566 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249567 (m : nat) (d : nat) (n : nat) (d'' : nat) (d' : nat) : (term5 m n d'' d' d) = (term7 m d n d'' d').
Proof. exact (MK_COMB (@lem1249566) (@lem1249565 m d n d'' d')). Qed.
Lemma lem1249568 (m : nat) (d''' : nat) (n : nat) (d'' : nat) (d' : nat) : ((Nat.add m n) = (term4 m d''' n d'' d')) = ((Nat.add m n) = (term4 m d''' n d'' d')).
Proof. exact (eq_refl ((Nat.add m n) = (term4 m d''' n d'' d'))). Qed.
Lemma lem1249569 (d : nat) (m : nat) (d''' : nat) (n : nat) (d'' : nat) (d' : nat) : ((term2 m n d'' d' d) = ((Nat.add m n) = (term4 m d''' n d'' d'))) = (((Nat.add m n) = (term6 m d n d'' d')) = ((Nat.add m n) = (term4 m d''' n d'' d'))).
Proof. exact (MK_COMB (@lem1249567 m d n d'' d') (@lem1249568 m d''' n d'' d')). Qed.
Lemma lem1249570 (d : nat) (m : nat) (d''' : nat) (n : nat) (d'' : nat) (d' : nat) : ((term2 m n d'' d' d) = (term3 m n d' d'' d''')) = (((Nat.add m n) = (term6 m d n d'' d')) = ((Nat.add m n) = (term4 m d''' n d'' d'))).
Proof. exact (TRANS (@lem1249564 d m d''' n d'' d') (@lem1249569 d m d''' n d'' d')). Qed.
Lemma lem1249571 (m : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((Nat.add m n) = (term6 m d n d'' d')) = ((Nat.add m n) = (term4 m d''' n d'' d')).
Proof. exact (EQ_MP (@lem1249570 d m d''' n d'' d') (@lem1249561 m n d d' d'' d''' h1)). Qed.
Lemma lem1249572 (d''' : nat) (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add m n) = (term8 m d q d')) : (Nat.add m n) = (term4 m d''' n d'' d').
Proof. exact (EQ_MP (@lem1249571 m n d d' d'' d''' h1) (@lem1248474 d'' n m d q d' h2 h3)). Qed.
