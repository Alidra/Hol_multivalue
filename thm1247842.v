Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247842_term_abbrevs.
Require Import thm1247718_spec.
Lemma lem1247815 (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : n = (Nat.add q d'').
Proof. exact (h1). Qed.
Lemma lem1247830 (m : nat) (d' : nat) (q : nat) (d : nat) : (term0 m d' q d) = (term0 m d' q d).
Proof. exact (eq_refl (term0 m d' q d)). Qed.
Lemma lem1247831 (m : nat) (d' : nat) (d : nat) (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : (term1 m d' q d n) = (term2 m d' d q d'').
Proof. exact (MK_COMB (@lem1247830 m d' q d) (@lem1247815 n q d'' h1)). Qed.
Lemma lem1247832 (d'' : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : (term2 m d' d q d'') = ((term3 m q d'') = (term4 m d' q d)).
Proof. exact (eq_refl (term2 m d' d q d'')). Qed.
Lemma lem1247833 (m : nat) (d' : nat) (q : nat) (d : nat) (n : nat) : (term5 m d' q d n) = (term5 m d' q d n).
Proof. exact (eq_refl (term5 m d' q d n)). Qed.
Lemma lem1247834 (n : nat) (d'' : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : ((term1 m d' q d n) = (term2 m d' d q d'')) = ((term1 m d' q d n) = ((term3 m q d'') = (term4 m d' q d))).
Proof. exact (MK_COMB (@lem1247833 m d' q d n) (@lem1247832 d'' m d' q d)). Qed.
Lemma lem1247835 (n : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : (term1 m d' q d n) = ((Nat.add m n) = (term4 m d' q d)).
Proof. exact (eq_refl (term1 m d' q d n)). Qed.
Lemma lem1247836 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247837 (n : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : (term5 m d' q d n) = (term6 n m d' q d).
Proof. exact (MK_COMB (@lem1247836) (@lem1247835 n m d' q d)). Qed.
Lemma lem1247838 (d'' : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : ((term3 m q d'') = (term4 m d' q d)) = ((term3 m q d'') = (term4 m d' q d)).
Proof. exact (eq_refl ((term3 m q d'') = (term4 m d' q d))). Qed.
Lemma lem1247839 (n : nat) (d'' : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : ((term1 m d' q d n) = ((term3 m q d'') = (term4 m d' q d))) = (((Nat.add m n) = (term4 m d' q d)) = ((term3 m q d'') = (term4 m d' q d))).
Proof. exact (MK_COMB (@lem1247837 n m d' q d) (@lem1247838 d'' m d' q d)). Qed.
Lemma lem1247840 (n : nat) (d'' : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : ((term1 m d' q d n) = (term2 m d' d q d'')) = (((Nat.add m n) = (term4 m d' q d)) = ((term3 m q d'') = (term4 m d' q d))).
Proof. exact (TRANS (@lem1247834 n d'' m d' q d) (@lem1247839 n d'' m d' q d)). Qed.
Lemma lem1247841 (m : nat) (d' : nat) (d : nat) (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : ((Nat.add m n) = (term4 m d' q d)) = ((term3 m q d'') = (term4 m d' q d)).
Proof. exact (EQ_MP (@lem1247840 n d'' m d' q d) (@lem1247831 m d' d n q d'' h1)). Qed.
Lemma lem1247842 (d'' : nat) (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : n = (Nat.add q d'')) (h2 : p = (Nat.add m d')) (h3 : (Nat.add m n) = (term7 p q d)) : (term3 m q d'') = (term4 m d' q d).
Proof. exact (EQ_MP (@lem1247841 m d' d n q d'' h1) (@lem1247718 d' m n p q d h2 h3)). Qed.
