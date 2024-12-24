Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247766_term_abbrevs.
Require Import thm1247690_spec.
Lemma lem1247739 (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : n = (Nat.add q d'').
Proof. exact (h1). Qed.
Lemma lem1247754 (d' : nat) (p : nat) (q : nat) (d : nat) : (term0 d' p q d) = (term0 d' p q d).
Proof. exact (eq_refl (term0 d' p q d)). Qed.
Lemma lem1247755 (d' : nat) (p : nat) (d : nat) (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : (term1 d' p q d n) = (term2 d' p d q d'').
Proof. exact (MK_COMB (@lem1247754 d' p q d) (@lem1247739 n q d'' h1)). Qed.
Lemma lem1247756 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d : nat) : (term2 d' p d q d'') = ((term3 p d' q d'') = (term4 p q d)).
Proof. exact (eq_refl (term2 d' p d q d'')). Qed.
Lemma lem1247757 (d' : nat) (p : nat) (q : nat) (d : nat) (n : nat) : (term5 d' p q d n) = (term5 d' p q d n).
Proof. exact (eq_refl (term5 d' p q d n)). Qed.
Lemma lem1247758 (n : nat) (d' : nat) (d'' : nat) (p : nat) (q : nat) (d : nat) : ((term1 d' p q d n) = (term2 d' p d q d'')) = ((term1 d' p q d n) = ((term3 p d' q d'') = (term4 p q d))).
Proof. exact (MK_COMB (@lem1247757 d' p q d n) (@lem1247756 d' d'' p q d)). Qed.
Lemma lem1247759 (d' : nat) (n : nat) (p : nat) (q : nat) (d : nat) : (term1 d' p q d n) = ((term4 p d' n) = (term4 p q d)).
Proof. exact (eq_refl (term1 d' p q d n)). Qed.
Lemma lem1247760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247761 (d' : nat) (n : nat) (p : nat) (q : nat) (d : nat) : (term5 d' p q d n) = (term6 d' n p q d).
Proof. exact (MK_COMB (@lem1247760) (@lem1247759 d' n p q d)). Qed.
Lemma lem1247762 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d : nat) : ((term3 p d' q d'') = (term4 p q d)) = ((term3 p d' q d'') = (term4 p q d)).
Proof. exact (eq_refl ((term3 p d' q d'') = (term4 p q d))). Qed.
Lemma lem1247763 (n : nat) (d' : nat) (d'' : nat) (p : nat) (q : nat) (d : nat) : ((term1 d' p q d n) = ((term3 p d' q d'') = (term4 p q d))) = (((term4 p d' n) = (term4 p q d)) = ((term3 p d' q d'') = (term4 p q d))).
Proof. exact (MK_COMB (@lem1247761 d' n p q d) (@lem1247762 d' d'' p q d)). Qed.
Lemma lem1247764 (n : nat) (d' : nat) (d'' : nat) (p : nat) (q : nat) (d : nat) : ((term1 d' p q d n) = (term2 d' p d q d'')) = (((term4 p d' n) = (term4 p q d)) = ((term3 p d' q d'') = (term4 p q d))).
Proof. exact (TRANS (@lem1247758 n d' d'' p q d) (@lem1247763 n d' d'' p q d)). Qed.
Lemma lem1247765 (d' : nat) (p : nat) (d : nat) (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : ((term4 p d' n) = (term4 p q d)) = ((term3 p d' q d'') = (term4 p q d)).
Proof. exact (EQ_MP (@lem1247764 n d' d'' p q d) (@lem1247755 d' p d n q d'' h1)). Qed.
Lemma lem1247766 (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : n = (Nat.add q d'')) (h3 : (Nat.add m n) = (term4 p q d)) : (term3 p d' q d'') = (term4 p q d).
Proof. exact (EQ_MP (@lem1247765 d' p d n q d'' h2) (@lem1247690 d' m n p q d h1 h3)). Qed.
