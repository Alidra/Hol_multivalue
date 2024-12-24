Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247994_term_abbrevs.
Require Import thm1247918_spec.
Lemma lem1247967 (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : n = (Nat.add q d'').
Proof. exact (h1). Qed.
Lemma lem1247982 (q : nat) (p : nat) (d' : nat) (d : nat) : (term0 q p d' d) = (term0 q p d' d).
Proof. exact (eq_refl (term0 q p d' d)). Qed.
Lemma lem1247983 (p : nat) (d' : nat) (d : nat) (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : (term1 q p d' d n) = (term2 p d' d q d'').
Proof. exact (MK_COMB (@lem1247982 q p d' d) (@lem1247967 n q d'' h1)). Qed.
Lemma lem1247984 (p : nat) (d' : nat) (q : nat) (d'' : nat) (d : nat) : (term2 p d' d q d'') = ((Nat.add p q) = (term3 p d' q d'' d)).
Proof. exact (eq_refl (term2 p d' d q d'')). Qed.
Lemma lem1247985 (q : nat) (p : nat) (d' : nat) (d : nat) (n : nat) : (term4 q p d' d n) = (term4 q p d' d n).
Proof. exact (eq_refl (term4 q p d' d n)). Qed.
Lemma lem1247986 (n : nat) (p : nat) (d' : nat) (q : nat) (d'' : nat) (d : nat) : ((term1 q p d' d n) = (term2 p d' d q d'')) = ((term1 q p d' d n) = ((Nat.add p q) = (term3 p d' q d'' d))).
Proof. exact (MK_COMB (@lem1247985 q p d' d n) (@lem1247984 p d' q d'' d)). Qed.
Lemma lem1247987 (q : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : (term1 q p d' d n) = ((Nat.add p q) = (term5 p d' n d)).
Proof. exact (eq_refl (term1 q p d' d n)). Qed.
Lemma lem1247988 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247989 (q : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : (term4 q p d' d n) = (term6 q p d' n d).
Proof. exact (MK_COMB (@lem1247988) (@lem1247987 q p d' n d)). Qed.
Lemma lem1247990 (p : nat) (d' : nat) (q : nat) (d'' : nat) (d : nat) : ((Nat.add p q) = (term3 p d' q d'' d)) = ((Nat.add p q) = (term3 p d' q d'' d)).
Proof. exact (eq_refl ((Nat.add p q) = (term3 p d' q d'' d))). Qed.
Lemma lem1247991 (n : nat) (p : nat) (d' : nat) (q : nat) (d'' : nat) (d : nat) : ((term1 q p d' d n) = ((Nat.add p q) = (term3 p d' q d'' d))) = (((Nat.add p q) = (term5 p d' n d)) = ((Nat.add p q) = (term3 p d' q d'' d))).
Proof. exact (MK_COMB (@lem1247989 q p d' n d) (@lem1247990 p d' q d'' d)). Qed.
Lemma lem1247992 (n : nat) (p : nat) (d' : nat) (q : nat) (d'' : nat) (d : nat) : ((term1 q p d' d n) = (term2 p d' d q d'')) = (((Nat.add p q) = (term5 p d' n d)) = ((Nat.add p q) = (term3 p d' q d'' d))).
Proof. exact (TRANS (@lem1247986 n p d' q d'' d) (@lem1247991 n p d' q d'' d)). Qed.
Lemma lem1247993 (p : nat) (d' : nat) (d : nat) (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : ((Nat.add p q) = (term5 p d' n d)) = ((Nat.add p q) = (term3 p d' q d'' d)).
Proof. exact (EQ_MP (@lem1247992 n p d' q d'' d) (@lem1247983 p d' d n q d'' h1)). Qed.
Lemma lem1247994 (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : n = (Nat.add q d'')) (h3 : (Nat.add p q) = (term7 m n d)) : (Nat.add p q) = (term3 p d' q d'' d).
Proof. exact (EQ_MP (@lem1247993 p d' d n q d'' h2) (@lem1247918 d' p q m n d h1 h3)). Qed.
