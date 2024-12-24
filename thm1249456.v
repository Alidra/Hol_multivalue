Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249456_term_abbrevs.
Require Import thm1248272_spec.
Lemma lem1249429 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249444 (p : nat) (n : nat) (d'' : nat) (d' : nat) : (term1 p n d'' d') = (term1 p n d'' d').
Proof. exact (eq_refl (term1 p n d'' d')). Qed.
Lemma lem1249445 (p : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 p n d'' d' d) = (term3 p n d' d'' d''').
Proof. exact (MK_COMB (@lem1249444 p n d'' d') (@lem1249429 d d' d'' d''' h1)). Qed.
Lemma lem1249446 (d''' : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat) : (term3 p n d' d'' d''') = ((term4 p d' d'' d''' n) = (term5 p n d'' d')).
Proof. exact (eq_refl (term3 p n d' d'' d''')). Qed.
Lemma lem1249447 (p : nat) (n : nat) (d'' : nat) (d' : nat) (d : nat) : (term6 p n d'' d' d) = (term6 p n d'' d' d).
Proof. exact (eq_refl (term6 p n d'' d' d)). Qed.
Lemma lem1249448 (d : nat) (d''' : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat) : ((term2 p n d'' d' d) = (term3 p n d' d'' d''')) = ((term2 p n d'' d' d) = ((term4 p d' d'' d''' n) = (term5 p n d'' d'))).
Proof. exact (MK_COMB (@lem1249447 p n d'' d' d) (@lem1249446 d''' p n d'' d')). Qed.
Lemma lem1249449 (d : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat) : (term2 p n d'' d' d) = ((term7 p d n) = (term5 p n d'' d')).
Proof. exact (eq_refl (term2 p n d'' d' d)). Qed.
Lemma lem1249450 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249451 (d : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat) : (term6 p n d'' d' d) = (term8 d p n d'' d').
Proof. exact (MK_COMB (@lem1249450) (@lem1249449 d p n d'' d')). Qed.
Lemma lem1249452 (d''' : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat) : ((term4 p d' d'' d''' n) = (term5 p n d'' d')) = ((term4 p d' d'' d''' n) = (term5 p n d'' d')).
Proof. exact (eq_refl ((term4 p d' d'' d''' n) = (term5 p n d'' d'))). Qed.
Lemma lem1249453 (d : nat) (d''' : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat) : ((term2 p n d'' d' d) = ((term4 p d' d'' d''' n) = (term5 p n d'' d'))) = (((term7 p d n) = (term5 p n d'' d')) = ((term4 p d' d'' d''' n) = (term5 p n d'' d'))).
Proof. exact (MK_COMB (@lem1249451 d p n d'' d') (@lem1249452 d''' p n d'' d')). Qed.
Lemma lem1249454 (d : nat) (d''' : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat) : ((term2 p n d'' d' d) = (term3 p n d' d'' d''')) = (((term7 p d n) = (term5 p n d'' d')) = ((term4 p d' d'' d''' n) = (term5 p n d'' d'))).
Proof. exact (TRANS (@lem1249448 d d''' p n d'' d') (@lem1249453 d d''' p n d'' d')). Qed.
Lemma lem1249455 (p : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((term7 p d n) = (term5 p n d'' d')) = ((term4 p d' d'' d''' n) = (term5 p n d'' d')).
Proof. exact (EQ_MP (@lem1249454 d d''' p n d'' d') (@lem1249445 p n d d' d'' d''' h1)). Qed.
Lemma lem1249456 (d''' : nat) (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : q = (Nat.add n d'')) (h3 : (term7 p d n) = (term7 p q d')) : (term4 p d' d'' d''' n) = (term5 p n d'' d').
Proof. exact (EQ_MP (@lem1249455 p n d d' d'' d''' h1) (@lem1248272 d'' d n p q d' h2 h3)). Qed.
