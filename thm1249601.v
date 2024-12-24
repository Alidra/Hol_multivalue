Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249601_term_abbrevs.
Require Import thm1248522_spec.
Lemma lem1249574 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249589 (m : nat) (q : nat) (d'' : nat) (d' : nat) : (term1 m q d'' d') = (term1 m q d'' d').
Proof. exact (eq_refl (term1 m q d'' d')). Qed.
Lemma lem1249590 (m : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 m q d'' d' d) = (term3 m q d' d'' d''').
Proof. exact (MK_COMB (@lem1249589 m q d'' d') (@lem1249574 d d' d'' d''' h1)). Qed.
Lemma lem1249591 (d''' : nat) (m : nat) (q : nat) (d'' : nat) (d' : nat) : (term3 m q d' d'' d''') = ((term4 m d' d'' d''' q) = (term5 m q d'' d')).
Proof. exact (eq_refl (term3 m q d' d'' d''')). Qed.
Lemma lem1249592 (m : nat) (q : nat) (d'' : nat) (d' : nat) (d : nat) : (term6 m q d'' d' d) = (term6 m q d'' d' d).
Proof. exact (eq_refl (term6 m q d'' d' d)). Qed.
Lemma lem1249593 (d : nat) (d''' : nat) (m : nat) (q : nat) (d'' : nat) (d' : nat) : ((term2 m q d'' d' d) = (term3 m q d' d'' d''')) = ((term2 m q d'' d' d) = ((term4 m d' d'' d''' q) = (term5 m q d'' d'))).
Proof. exact (MK_COMB (@lem1249592 m q d'' d' d) (@lem1249591 d''' m q d'' d')). Qed.
Lemma lem1249594 (d : nat) (m : nat) (q : nat) (d'' : nat) (d' : nat) : (term2 m q d'' d' d) = ((term7 m d q) = (term5 m q d'' d')).
Proof. exact (eq_refl (term2 m q d'' d' d)). Qed.
Lemma lem1249595 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249596 (d : nat) (m : nat) (q : nat) (d'' : nat) (d' : nat) : (term6 m q d'' d' d) = (term8 d m q d'' d').
Proof. exact (MK_COMB (@lem1249595) (@lem1249594 d m q d'' d')). Qed.
Lemma lem1249597 (d''' : nat) (m : nat) (q : nat) (d'' : nat) (d' : nat) : ((term4 m d' d'' d''' q) = (term5 m q d'' d')) = ((term4 m d' d'' d''' q) = (term5 m q d'' d')).
Proof. exact (eq_refl ((term4 m d' d'' d''' q) = (term5 m q d'' d'))). Qed.
Lemma lem1249598 (d : nat) (d''' : nat) (m : nat) (q : nat) (d'' : nat) (d' : nat) : ((term2 m q d'' d' d) = ((term4 m d' d'' d''' q) = (term5 m q d'' d'))) = (((term7 m d q) = (term5 m q d'' d')) = ((term4 m d' d'' d''' q) = (term5 m q d'' d'))).
Proof. exact (MK_COMB (@lem1249596 d m q d'' d') (@lem1249597 d''' m q d'' d')). Qed.
Lemma lem1249599 (d : nat) (d''' : nat) (m : nat) (q : nat) (d'' : nat) (d' : nat) : ((term2 m q d'' d' d) = (term3 m q d' d'' d''')) = (((term7 m d q) = (term5 m q d'' d')) = ((term4 m d' d'' d''' q) = (term5 m q d'' d'))).
Proof. exact (TRANS (@lem1249593 d d''' m q d'' d') (@lem1249598 d d''' m q d'' d')). Qed.
Lemma lem1249600 (m : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((term7 m d q) = (term5 m q d'' d')) = ((term4 m d' d'' d''' q) = (term5 m q d'' d')).
Proof. exact (EQ_MP (@lem1249599 d d''' m q d'' d') (@lem1249590 m q d d' d'' d''' h1)). Qed.
Lemma lem1249601 (d''' : nat) (d'' : nat) (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : n = (Nat.add q d'')) (h3 : (term7 m d q) = (term7 m n d')) : (term4 m d' d'' d''' q) = (term5 m q d'' d').
Proof. exact (EQ_MP (@lem1249600 m q d d' d'' d''' h1) (@lem1248522 d'' d q m n d' h2 h3)). Qed.
