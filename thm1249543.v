Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249543_term_abbrevs.
Require Import thm1248446_spec.
Lemma lem1249516 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249531 (d'' : nat) (m : nat) (q : nat) (d' : nat) : (term1 d'' m q d') = (term1 d'' m q d').
Proof. exact (eq_refl (term1 d'' m q d')). Qed.
Lemma lem1249532 (m : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 d'' m q d' d) = (term3 m q d' d'' d''').
Proof. exact (MK_COMB (@lem1249531 d'' m q d') (@lem1249516 d d' d'' d''' h1)). Qed.
Lemma lem1249533 (m : nat) (d'' : nat) (d''' : nat) (q : nat) (d' : nat) : (term3 m q d' d'' d''') = ((term4 m q d'') = (term5 m d'' d''' q d')).
Proof. exact (eq_refl (term3 m q d' d'' d''')). Qed.
Lemma lem1249534 (d'' : nat) (m : nat) (q : nat) (d' : nat) (d : nat) : (term6 d'' m q d' d) = (term6 d'' m q d' d).
Proof. exact (eq_refl (term6 d'' m q d' d)). Qed.
Lemma lem1249535 (d : nat) (m : nat) (d'' : nat) (d''' : nat) (q : nat) (d' : nat) : ((term2 d'' m q d' d) = (term3 m q d' d'' d''')) = ((term2 d'' m q d' d) = ((term4 m q d'') = (term5 m d'' d''' q d'))).
Proof. exact (MK_COMB (@lem1249534 d'' m q d' d) (@lem1249533 m d'' d''' q d')). Qed.
Lemma lem1249536 (d'' : nat) (m : nat) (d : nat) (q : nat) (d' : nat) : (term2 d'' m q d' d) = ((term4 m q d'') = (term7 m d q d')).
Proof. exact (eq_refl (term2 d'' m q d' d)). Qed.
Lemma lem1249537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249538 (d'' : nat) (m : nat) (d : nat) (q : nat) (d' : nat) : (term6 d'' m q d' d) = (term8 d'' m d q d').
Proof. exact (MK_COMB (@lem1249537) (@lem1249536 d'' m d q d')). Qed.
Lemma lem1249539 (m : nat) (d'' : nat) (d''' : nat) (q : nat) (d' : nat) : ((term4 m q d'') = (term5 m d'' d''' q d')) = ((term4 m q d'') = (term5 m d'' d''' q d')).
Proof. exact (eq_refl ((term4 m q d'') = (term5 m d'' d''' q d'))). Qed.
Lemma lem1249540 (d : nat) (m : nat) (d'' : nat) (d''' : nat) (q : nat) (d' : nat) : ((term2 d'' m q d' d) = ((term4 m q d'') = (term5 m d'' d''' q d'))) = (((term4 m q d'') = (term7 m d q d')) = ((term4 m q d'') = (term5 m d'' d''' q d'))).
Proof. exact (MK_COMB (@lem1249538 d'' m d q d') (@lem1249539 m d'' d''' q d')). Qed.
Lemma lem1249541 (d : nat) (m : nat) (d'' : nat) (d''' : nat) (q : nat) (d' : nat) : ((term2 d'' m q d' d) = (term3 m q d' d'' d''')) = (((term4 m q d'') = (term7 m d q d')) = ((term4 m q d'') = (term5 m d'' d''' q d'))).
Proof. exact (TRANS (@lem1249535 d m d'' d''' q d') (@lem1249540 d m d'' d''' q d')). Qed.
Lemma lem1249542 (m : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((term4 m q d'') = (term7 m d q d')) = ((term4 m q d'') = (term5 m d'' d''' q d')).
Proof. exact (EQ_MP (@lem1249541 d m d'' d''' q d') (@lem1249532 m q d d' d'' d''' h1)). Qed.
Lemma lem1249543 (d''' : nat) (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : n = (Nat.add q d'')) (h3 : (Nat.add m n) = (term7 m d q d')) : (term4 m q d'') = (term5 m d'' d''' q d').
Proof. exact (EQ_MP (@lem1249542 m q d d' d'' d''' h1) (@lem1248446 d'' n m d q d' h2 h3)). Qed.
