Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249427_term_abbrevs.
Require Import thm1248244_spec.
Lemma lem1249400 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249415 (d'' : nat) (p : nat) (q : nat) (d' : nat) : (term1 d'' p q d') = (term1 d'' p q d').
Proof. exact (eq_refl (term1 d'' p q d')). Qed.
Lemma lem1249416 (p : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 d'' p q d' d) = (term3 p q d' d'' d''').
Proof. exact (MK_COMB (@lem1249415 d'' p q d') (@lem1249400 d d' d'' d''' h1)). Qed.
Lemma lem1249417 (d''' : nat) (d'' : nat) (p : nat) (q : nat) (d' : nat) : (term3 p q d' d'' d''') = ((term4 p d' d''' q d'') = (term5 p q d')).
Proof. exact (eq_refl (term3 p q d' d'' d''')). Qed.
Lemma lem1249418 (d'' : nat) (p : nat) (q : nat) (d' : nat) (d : nat) : (term6 d'' p q d' d) = (term6 d'' p q d' d).
Proof. exact (eq_refl (term6 d'' p q d' d)). Qed.
Lemma lem1249419 (d : nat) (d''' : nat) (d'' : nat) (p : nat) (q : nat) (d' : nat) : ((term2 d'' p q d' d) = (term3 p q d' d'' d''')) = ((term2 d'' p q d' d) = ((term4 p d' d''' q d'') = (term5 p q d'))).
Proof. exact (MK_COMB (@lem1249418 d'' p q d' d) (@lem1249417 d''' d'' p q d')). Qed.
Lemma lem1249420 (d : nat) (d'' : nat) (p : nat) (q : nat) (d' : nat) : (term2 d'' p q d' d) = ((term7 p d q d'') = (term5 p q d')).
Proof. exact (eq_refl (term2 d'' p q d' d)). Qed.
Lemma lem1249421 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249422 (d : nat) (d'' : nat) (p : nat) (q : nat) (d' : nat) : (term6 d'' p q d' d) = (term8 d d'' p q d').
Proof. exact (MK_COMB (@lem1249421) (@lem1249420 d d'' p q d')). Qed.
Lemma lem1249423 (d''' : nat) (d'' : nat) (p : nat) (q : nat) (d' : nat) : ((term4 p d' d''' q d'') = (term5 p q d')) = ((term4 p d' d''' q d'') = (term5 p q d')).
Proof. exact (eq_refl ((term4 p d' d''' q d'') = (term5 p q d'))). Qed.
Lemma lem1249424 (d : nat) (d''' : nat) (d'' : nat) (p : nat) (q : nat) (d' : nat) : ((term2 d'' p q d' d) = ((term4 p d' d''' q d'') = (term5 p q d'))) = (((term7 p d q d'') = (term5 p q d')) = ((term4 p d' d''' q d'') = (term5 p q d'))).
Proof. exact (MK_COMB (@lem1249422 d d'' p q d') (@lem1249423 d''' d'' p q d')). Qed.
Lemma lem1249425 (d : nat) (d''' : nat) (d'' : nat) (p : nat) (q : nat) (d' : nat) : ((term2 d'' p q d' d) = (term3 p q d' d'' d''')) = (((term7 p d q d'') = (term5 p q d')) = ((term4 p d' d''' q d'') = (term5 p q d'))).
Proof. exact (TRANS (@lem1249419 d d''' d'' p q d') (@lem1249424 d d''' d'' p q d')). Qed.
Lemma lem1249426 (p : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((term7 p d q d'') = (term5 p q d')) = ((term4 p d' d''' q d'') = (term5 p q d')).
Proof. exact (EQ_MP (@lem1249425 d d''' d'' p q d') (@lem1249416 p q d d' d'' d''' h1)). Qed.
Lemma lem1249427 (d''' : nat) (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : n = (Nat.add q d'')) (h3 : (term5 p d n) = (term5 p q d')) : (term4 p d' d''' q d'') = (term5 p q d').
Proof. exact (EQ_MP (@lem1249426 p q d d' d'' d''' h1) (@lem1248244 d'' d n p q d' h2 h3)). Qed.
