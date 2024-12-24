Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249137_term_abbrevs.
Require Import thm1247563_spec.
Lemma lem1249110 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249125 (d' : nat) (m : nat) (d'' : nat) : (term1 d' m d'') = (term1 d' m d'').
Proof. exact (eq_refl (term1 d' m d'')). Qed.
Lemma lem1249126 (m : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 d' m d'' d) = (term3 m d' d'' d''').
Proof. exact (MK_COMB (@lem1249125 d' m d'') (@lem1249110 d d' d'' d''' h1)). Qed.
Lemma lem1249127 (m : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term3 m d' d'' d''') = ((Nat.add m d') = (term4 m d' d''' d'')).
Proof. exact (eq_refl (term3 m d' d'' d''')). Qed.
Lemma lem1249128 (d' : nat) (m : nat) (d'' : nat) (d : nat) : (term5 d' m d'' d) = (term5 d' m d'' d).
Proof. exact (eq_refl (term5 d' m d'' d)). Qed.
Lemma lem1249129 (d : nat) (m : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term2 d' m d'' d) = (term3 m d' d'' d''')) = ((term2 d' m d'' d) = ((Nat.add m d') = (term4 m d' d''' d''))).
Proof. exact (MK_COMB (@lem1249128 d' m d'' d) (@lem1249127 m d' d''' d'')). Qed.
Lemma lem1249130 (d' : nat) (m : nat) (d : nat) (d'' : nat) : (term2 d' m d'' d) = ((Nat.add m d') = (term6 m d d'')).
Proof. exact (eq_refl (term2 d' m d'' d)). Qed.
Lemma lem1249131 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249132 (d' : nat) (m : nat) (d : nat) (d'' : nat) : (term5 d' m d'' d) = (term7 d' m d d'').
Proof. exact (MK_COMB (@lem1249131) (@lem1249130 d' m d d'')). Qed.
Lemma lem1249133 (m : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((Nat.add m d') = (term4 m d' d''' d'')) = ((Nat.add m d') = (term4 m d' d''' d'')).
Proof. exact (eq_refl ((Nat.add m d') = (term4 m d' d''' d''))). Qed.
Lemma lem1249134 (d : nat) (m : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term2 d' m d'' d) = ((Nat.add m d') = (term4 m d' d''' d''))) = (((Nat.add m d') = (term6 m d d'')) = ((Nat.add m d') = (term4 m d' d''' d''))).
Proof. exact (MK_COMB (@lem1249132 d' m d d'') (@lem1249133 m d' d''' d'')). Qed.
Lemma lem1249135 (d : nat) (m : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term2 d' m d'' d) = (term3 m d' d'' d''')) = (((Nat.add m d') = (term6 m d d'')) = ((Nat.add m d') = (term4 m d' d''' d''))).
Proof. exact (TRANS (@lem1249129 d m d' d''' d'') (@lem1249134 d m d' d''' d'')). Qed.
Lemma lem1249136 (m : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((Nat.add m d') = (term6 m d d'')) = ((Nat.add m d') = (term4 m d' d''' d'')).
Proof. exact (EQ_MP (@lem1249135 d m d' d''' d'') (@lem1249126 m d d' d'' d''' h1)). Qed.
Lemma lem1249137 (d''' : nat) (d' : nat) (m : nat) (d : nat) (d'' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : (Nat.add m d') = (term6 m d d'')) : (Nat.add m d') = (term4 m d' d''' d'').
Proof. exact (EQ_MP (@lem1249136 m d d' d'' d''' h1) (@lem1247563 d' m d d'' h2)). Qed.
