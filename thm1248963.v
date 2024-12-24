Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248963_term_abbrevs.
Require Import thm1247366_spec.
Lemma lem1248936 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1248951 (p : nat) (d'' : nat) (d' : nat) : (term1 p d'' d') = (term1 p d'' d').
Proof. exact (eq_refl (term1 p d'' d')). Qed.
Lemma lem1248952 (p : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 p d'' d' d) = (term3 p d' d'' d''').
Proof. exact (MK_COMB (@lem1248951 p d'' d') (@lem1248936 d d' d'' d''' h1)). Qed.
Lemma lem1248953 (d''' : nat) (p : nat) (d'' : nat) (d' : nat) : (term3 p d' d'' d''') = ((term4 p d' d'' d''') = (term5 p d'' d')).
Proof. exact (eq_refl (term3 p d' d'' d''')). Qed.
Lemma lem1248954 (p : nat) (d'' : nat) (d' : nat) (d : nat) : (term6 p d'' d' d) = (term6 p d'' d' d).
Proof. exact (eq_refl (term6 p d'' d' d)). Qed.
Lemma lem1248955 (d : nat) (d''' : nat) (p : nat) (d'' : nat) (d' : nat) : ((term2 p d'' d' d) = (term3 p d' d'' d''')) = ((term2 p d'' d' d) = ((term4 p d' d'' d''') = (term5 p d'' d'))).
Proof. exact (MK_COMB (@lem1248954 p d'' d' d) (@lem1248953 d''' p d'' d')). Qed.
Lemma lem1248956 (d : nat) (p : nat) (d'' : nat) (d' : nat) : (term2 p d'' d' d) = ((Nat.add p d) = (term5 p d'' d')).
Proof. exact (eq_refl (term2 p d'' d' d)). Qed.
Lemma lem1248957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248958 (d : nat) (p : nat) (d'' : nat) (d' : nat) : (term6 p d'' d' d) = (term7 d p d'' d').
Proof. exact (MK_COMB (@lem1248957) (@lem1248956 d p d'' d')). Qed.
Lemma lem1248959 (d''' : nat) (p : nat) (d'' : nat) (d' : nat) : ((term4 p d' d'' d''') = (term5 p d'' d')) = ((term4 p d' d'' d''') = (term5 p d'' d')).
Proof. exact (eq_refl ((term4 p d' d'' d''') = (term5 p d'' d'))). Qed.
Lemma lem1248960 (d : nat) (d''' : nat) (p : nat) (d'' : nat) (d' : nat) : ((term2 p d'' d' d) = ((term4 p d' d'' d''') = (term5 p d'' d'))) = (((Nat.add p d) = (term5 p d'' d')) = ((term4 p d' d'' d''') = (term5 p d'' d'))).
Proof. exact (MK_COMB (@lem1248958 d p d'' d') (@lem1248959 d''' p d'' d')). Qed.
Lemma lem1248961 (d : nat) (d''' : nat) (p : nat) (d'' : nat) (d' : nat) : ((term2 p d'' d' d) = (term3 p d' d'' d''')) = (((Nat.add p d) = (term5 p d'' d')) = ((term4 p d' d'' d''') = (term5 p d'' d'))).
Proof. exact (TRANS (@lem1248955 d d''' p d'' d') (@lem1248960 d d''' p d'' d')). Qed.
Lemma lem1248962 (p : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((Nat.add p d) = (term5 p d'' d')) = ((term4 p d' d'' d''') = (term5 p d'' d')).
Proof. exact (EQ_MP (@lem1248961 d d''' p d'' d') (@lem1248952 p d d' d'' d''' h1)). Qed.
Lemma lem1248963 (d''' : nat) (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : n = (Nat.add p d'')) (h3 : (Nat.add p d) = (Nat.add n d')) : (term4 p d' d'' d''') = (term5 p d'' d').
Proof. exact (EQ_MP (@lem1248962 p d d' d'' d''' h1) (@lem1247366 d'' p d n d' h2 h3)). Qed.
