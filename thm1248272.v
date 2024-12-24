Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248272_term_abbrevs.
Require Import thm1248167_spec.
Lemma lem1248245 (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : q = (Nat.add n d'').
Proof. exact (h1). Qed.
Lemma lem1248260 (d : nat) (n : nat) (p : nat) (d' : nat) : (term0 d n p d') = (term0 d n p d').
Proof. exact (eq_refl (term0 d n p d')). Qed.
Lemma lem1248261 (d : nat) (p : nat) (d' : nat) (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : (term1 d n p d' q) = (term2 d p d' n d'').
Proof. exact (MK_COMB (@lem1248260 d n p d') (@lem1248245 q n d'' h1)). Qed.
Lemma lem1248262 (d : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat) : (term2 d p d' n d'') = ((term3 p d n) = (term4 p n d'' d')).
Proof. exact (eq_refl (term2 d p d' n d'')). Qed.
Lemma lem1248263 (d : nat) (n : nat) (p : nat) (d' : nat) (q : nat) : (term5 d n p d' q) = (term5 d n p d' q).
Proof. exact (eq_refl (term5 d n p d' q)). Qed.
Lemma lem1248264 (q : nat) (d : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat) : ((term1 d n p d' q) = (term2 d p d' n d'')) = ((term1 d n p d' q) = ((term3 p d n) = (term4 p n d'' d'))).
Proof. exact (MK_COMB (@lem1248263 d n p d' q) (@lem1248262 d p n d'' d')). Qed.
Lemma lem1248265 (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) : (term1 d n p d' q) = ((term3 p d n) = (term3 p q d')).
Proof. exact (eq_refl (term1 d n p d' q)). Qed.
Lemma lem1248266 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248267 (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) : (term5 d n p d' q) = (term6 d n p q d').
Proof. exact (MK_COMB (@lem1248266) (@lem1248265 d n p q d')). Qed.
Lemma lem1248268 (d : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat) : ((term3 p d n) = (term4 p n d'' d')) = ((term3 p d n) = (term4 p n d'' d')).
Proof. exact (eq_refl ((term3 p d n) = (term4 p n d'' d'))). Qed.
Lemma lem1248269 (q : nat) (d : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat) : ((term1 d n p d' q) = ((term3 p d n) = (term4 p n d'' d'))) = (((term3 p d n) = (term3 p q d')) = ((term3 p d n) = (term4 p n d'' d'))).
Proof. exact (MK_COMB (@lem1248267 d n p q d') (@lem1248268 d p n d'' d')). Qed.
Lemma lem1248270 (q : nat) (d : nat) (p : nat) (n : nat) (d'' : nat) (d' : nat) : ((term1 d n p d' q) = (term2 d p d' n d'')) = (((term3 p d n) = (term3 p q d')) = ((term3 p d n) = (term4 p n d'' d'))).
Proof. exact (TRANS (@lem1248264 q d p n d'' d') (@lem1248269 q d p n d'' d')). Qed.
Lemma lem1248271 (d : nat) (p : nat) (d' : nat) (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : ((term3 p d n) = (term3 p q d')) = ((term3 p d n) = (term4 p n d'' d')).
Proof. exact (EQ_MP (@lem1248270 q d p n d'' d') (@lem1248261 d p d' q n d'' h1)). Qed.
Lemma lem1248272 (d'' : nat) (d : nat) (n : nat) (p : nat) (q : nat) (d' : nat) (h1 : q = (Nat.add n d'')) (h2 : (term3 p d n) = (term3 p q d')) : (term3 p d n) = (term4 p n d'' d').
Proof. exact (EQ_MP (@lem1248271 d p d' q n d'' h1) (@lem1248167 d n p q d' h2)). Qed.
