Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247794_term_abbrevs.
Require Import thm1247690_spec.
Lemma lem1247767 (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : q = (Nat.add n d'').
Proof. exact (h1). Qed.
Lemma lem1247782 (d' : nat) (n : nat) (p : nat) (d : nat) : (term0 d' n p d) = (term0 d' n p d).
Proof. exact (eq_refl (term0 d' n p d)). Qed.
Lemma lem1247783 (d' : nat) (p : nat) (d : nat) (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : (term1 d' n p d q) = (term2 d' p d n d'').
Proof. exact (MK_COMB (@lem1247782 d' n p d) (@lem1247767 q n d'' h1)). Qed.
Lemma lem1247784 (d' : nat) (p : nat) (n : nat) (d'' : nat) (d : nat) : (term2 d' p d n d'') = ((term3 p d' n) = (term4 p n d'' d)).
Proof. exact (eq_refl (term2 d' p d n d'')). Qed.
Lemma lem1247785 (d' : nat) (n : nat) (p : nat) (d : nat) (q : nat) : (term5 d' n p d q) = (term5 d' n p d q).
Proof. exact (eq_refl (term5 d' n p d q)). Qed.
Lemma lem1247786 (q : nat) (d' : nat) (p : nat) (n : nat) (d'' : nat) (d : nat) : ((term1 d' n p d q) = (term2 d' p d n d'')) = ((term1 d' n p d q) = ((term3 p d' n) = (term4 p n d'' d))).
Proof. exact (MK_COMB (@lem1247785 d' n p d q) (@lem1247784 d' p n d'' d)). Qed.
Lemma lem1247787 (d' : nat) (n : nat) (p : nat) (q : nat) (d : nat) : (term1 d' n p d q) = ((term3 p d' n) = (term3 p q d)).
Proof. exact (eq_refl (term1 d' n p d q)). Qed.
Lemma lem1247788 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247789 (d' : nat) (n : nat) (p : nat) (q : nat) (d : nat) : (term5 d' n p d q) = (term6 d' n p q d).
Proof. exact (MK_COMB (@lem1247788) (@lem1247787 d' n p q d)). Qed.
Lemma lem1247790 (d' : nat) (p : nat) (n : nat) (d'' : nat) (d : nat) : ((term3 p d' n) = (term4 p n d'' d)) = ((term3 p d' n) = (term4 p n d'' d)).
Proof. exact (eq_refl ((term3 p d' n) = (term4 p n d'' d))). Qed.
Lemma lem1247791 (q : nat) (d' : nat) (p : nat) (n : nat) (d'' : nat) (d : nat) : ((term1 d' n p d q) = ((term3 p d' n) = (term4 p n d'' d))) = (((term3 p d' n) = (term3 p q d)) = ((term3 p d' n) = (term4 p n d'' d))).
Proof. exact (MK_COMB (@lem1247789 d' n p q d) (@lem1247790 d' p n d'' d)). Qed.
Lemma lem1247792 (q : nat) (d' : nat) (p : nat) (n : nat) (d'' : nat) (d : nat) : ((term1 d' n p d q) = (term2 d' p d n d'')) = (((term3 p d' n) = (term3 p q d)) = ((term3 p d' n) = (term4 p n d'' d))).
Proof. exact (TRANS (@lem1247786 q d' p n d'' d) (@lem1247791 q d' p n d'' d)). Qed.
Lemma lem1247793 (d' : nat) (p : nat) (d : nat) (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : ((term3 p d' n) = (term3 p q d)) = ((term3 p d' n) = (term4 p n d'' d)).
Proof. exact (EQ_MP (@lem1247792 q d' p n d'' d) (@lem1247783 d' p d q n d'' h1)). Qed.
Lemma lem1247794 (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add m n) = (term3 p q d)) : (term3 p d' n) = (term4 p n d'' d).
Proof. exact (EQ_MP (@lem1247793 d' p d q n d'' h2) (@lem1247690 d' m n p q d h1 h3)). Qed.
