Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248446_term_abbrevs.
Require Import thm1248369_spec.
Lemma lem1248419 (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : n = (Nat.add q d'').
Proof. exact (h1). Qed.
Lemma lem1248434 (m : nat) (d : nat) (q : nat) (d' : nat) : (term0 m d q d') = (term0 m d q d').
Proof. exact (eq_refl (term0 m d q d')). Qed.
Lemma lem1248435 (m : nat) (d : nat) (d' : nat) (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : (term1 m d q d' n) = (term2 m d d' q d'').
Proof. exact (MK_COMB (@lem1248434 m d q d') (@lem1248419 n q d'' h1)). Qed.
Lemma lem1248436 (d'' : nat) (m : nat) (d : nat) (q : nat) (d' : nat) : (term2 m d d' q d'') = ((term3 m q d'') = (term4 m d q d')).
Proof. exact (eq_refl (term2 m d d' q d'')). Qed.
Lemma lem1248437 (m : nat) (d : nat) (q : nat) (d' : nat) (n : nat) : (term5 m d q d' n) = (term5 m d q d' n).
Proof. exact (eq_refl (term5 m d q d' n)). Qed.
Lemma lem1248438 (n : nat) (d'' : nat) (m : nat) (d : nat) (q : nat) (d' : nat) : ((term1 m d q d' n) = (term2 m d d' q d'')) = ((term1 m d q d' n) = ((term3 m q d'') = (term4 m d q d'))).
Proof. exact (MK_COMB (@lem1248437 m d q d' n) (@lem1248436 d'' m d q d')). Qed.
Lemma lem1248439 (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) : (term1 m d q d' n) = ((Nat.add m n) = (term4 m d q d')).
Proof. exact (eq_refl (term1 m d q d' n)). Qed.
Lemma lem1248440 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248441 (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) : (term5 m d q d' n) = (term6 n m d q d').
Proof. exact (MK_COMB (@lem1248440) (@lem1248439 n m d q d')). Qed.
Lemma lem1248442 (d'' : nat) (m : nat) (d : nat) (q : nat) (d' : nat) : ((term3 m q d'') = (term4 m d q d')) = ((term3 m q d'') = (term4 m d q d')).
Proof. exact (eq_refl ((term3 m q d'') = (term4 m d q d'))). Qed.
Lemma lem1248443 (n : nat) (d'' : nat) (m : nat) (d : nat) (q : nat) (d' : nat) : ((term1 m d q d' n) = ((term3 m q d'') = (term4 m d q d'))) = (((Nat.add m n) = (term4 m d q d')) = ((term3 m q d'') = (term4 m d q d'))).
Proof. exact (MK_COMB (@lem1248441 n m d q d') (@lem1248442 d'' m d q d')). Qed.
Lemma lem1248444 (n : nat) (d'' : nat) (m : nat) (d : nat) (q : nat) (d' : nat) : ((term1 m d q d' n) = (term2 m d d' q d'')) = (((Nat.add m n) = (term4 m d q d')) = ((term3 m q d'') = (term4 m d q d'))).
Proof. exact (TRANS (@lem1248438 n d'' m d q d') (@lem1248443 n d'' m d q d')). Qed.
Lemma lem1248445 (m : nat) (d : nat) (d' : nat) (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : ((Nat.add m n) = (term4 m d q d')) = ((term3 m q d'') = (term4 m d q d')).
Proof. exact (EQ_MP (@lem1248444 n d'' m d q d') (@lem1248435 m d d' n q d'' h1)). Qed.
Lemma lem1248446 (d'' : nat) (n : nat) (m : nat) (d : nat) (q : nat) (d' : nat) (h1 : n = (Nat.add q d'')) (h2 : (Nat.add m n) = (term4 m d q d')) : (term3 m q d'') = (term4 m d q d').
Proof. exact (EQ_MP (@lem1248445 m d d' n q d'' h1) (@lem1248369 n m d q d' h2)). Qed.
