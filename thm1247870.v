Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247870_term_abbrevs.
Require Import thm1247718_spec.
Lemma lem1247843 (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : q = (Nat.add n d'').
Proof. exact (h1). Qed.
Lemma lem1247858 (n : nat) (m : nat) (d' : nat) (d : nat) : (term0 n m d' d) = (term0 n m d' d).
Proof. exact (eq_refl (term0 n m d' d)). Qed.
Lemma lem1247859 (m : nat) (d' : nat) (d : nat) (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : (term1 n m d' d q) = (term2 m d' d n d'').
Proof. exact (MK_COMB (@lem1247858 n m d' d) (@lem1247843 q n d'' h1)). Qed.
Lemma lem1247860 (m : nat) (d' : nat) (n : nat) (d'' : nat) (d : nat) : (term2 m d' d n d'') = ((Nat.add m n) = (term3 m d' n d'' d)).
Proof. exact (eq_refl (term2 m d' d n d'')). Qed.
Lemma lem1247861 (n : nat) (m : nat) (d' : nat) (d : nat) (q : nat) : (term4 n m d' d q) = (term4 n m d' d q).
Proof. exact (eq_refl (term4 n m d' d q)). Qed.
Lemma lem1247862 (q : nat) (m : nat) (d' : nat) (n : nat) (d'' : nat) (d : nat) : ((term1 n m d' d q) = (term2 m d' d n d'')) = ((term1 n m d' d q) = ((Nat.add m n) = (term3 m d' n d'' d))).
Proof. exact (MK_COMB (@lem1247861 n m d' d q) (@lem1247860 m d' n d'' d)). Qed.
Lemma lem1247863 (n : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : (term1 n m d' d q) = ((Nat.add m n) = (term5 m d' q d)).
Proof. exact (eq_refl (term1 n m d' d q)). Qed.
Lemma lem1247864 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247865 (n : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : (term4 n m d' d q) = (term6 n m d' q d).
Proof. exact (MK_COMB (@lem1247864) (@lem1247863 n m d' q d)). Qed.
Lemma lem1247866 (m : nat) (d' : nat) (n : nat) (d'' : nat) (d : nat) : ((Nat.add m n) = (term3 m d' n d'' d)) = ((Nat.add m n) = (term3 m d' n d'' d)).
Proof. exact (eq_refl ((Nat.add m n) = (term3 m d' n d'' d))). Qed.
Lemma lem1247867 (q : nat) (m : nat) (d' : nat) (n : nat) (d'' : nat) (d : nat) : ((term1 n m d' d q) = ((Nat.add m n) = (term3 m d' n d'' d))) = (((Nat.add m n) = (term5 m d' q d)) = ((Nat.add m n) = (term3 m d' n d'' d))).
Proof. exact (MK_COMB (@lem1247865 n m d' q d) (@lem1247866 m d' n d'' d)). Qed.
Lemma lem1247868 (q : nat) (m : nat) (d' : nat) (n : nat) (d'' : nat) (d : nat) : ((term1 n m d' d q) = (term2 m d' d n d'')) = (((Nat.add m n) = (term5 m d' q d)) = ((Nat.add m n) = (term3 m d' n d'' d))).
Proof. exact (TRANS (@lem1247862 q m d' n d'' d) (@lem1247867 q m d' n d'' d)). Qed.
Lemma lem1247869 (m : nat) (d' : nat) (d : nat) (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : ((Nat.add m n) = (term5 m d' q d)) = ((Nat.add m n) = (term3 m d' n d'' d)).
Proof. exact (EQ_MP (@lem1247868 q m d' n d'' d) (@lem1247859 m d' d q n d'' h1)). Qed.
Lemma lem1247870 (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add m n) = (term7 p q d)) : (Nat.add m n) = (term3 m d' n d'' d).
Proof. exact (EQ_MP (@lem1247869 m d' d q n d'' h2) (@lem1247718 d' m n p q d h1 h3)). Qed.
