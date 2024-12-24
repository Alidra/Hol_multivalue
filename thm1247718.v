Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247718_term_abbrevs.
Require Import thm1247613_spec.
Lemma lem1247691 (p : nat) (m : nat) (d' : nat) (h1 : p = (Nat.add m d')) : p = (Nat.add m d').
Proof. exact (h1). Qed.
Lemma lem1247706 (m : nat) (n : nat) (q : nat) (d : nat) : (term0 m n q d) = (term0 m n q d).
Proof. exact (eq_refl (term0 m n q d)). Qed.
Lemma lem1247707 (n : nat) (q : nat) (d : nat) (p : nat) (m : nat) (d' : nat) (h1 : p = (Nat.add m d')) : (term1 m n q d p) = (term2 n q d m d').
Proof. exact (MK_COMB (@lem1247706 m n q d) (@lem1247691 p m d' h1)). Qed.
Lemma lem1247708 (n : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : (term2 n q d m d') = ((Nat.add m n) = (term3 m d' q d)).
Proof. exact (eq_refl (term2 n q d m d')). Qed.
Lemma lem1247709 (m : nat) (n : nat) (q : nat) (d : nat) (p : nat) : (term4 m n q d p) = (term4 m n q d p).
Proof. exact (eq_refl (term4 m n q d p)). Qed.
Lemma lem1247710 (p : nat) (n : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : ((term1 m n q d p) = (term2 n q d m d')) = ((term1 m n q d p) = ((Nat.add m n) = (term3 m d' q d))).
Proof. exact (MK_COMB (@lem1247709 m n q d p) (@lem1247708 n m d' q d)). Qed.
Lemma lem1247711 (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) : (term1 m n q d p) = ((Nat.add m n) = (term5 p q d)).
Proof. exact (eq_refl (term1 m n q d p)). Qed.
Lemma lem1247712 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247713 (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) : (term4 m n q d p) = (term6 m n p q d).
Proof. exact (MK_COMB (@lem1247712) (@lem1247711 m n p q d)). Qed.
Lemma lem1247714 (n : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : ((Nat.add m n) = (term3 m d' q d)) = ((Nat.add m n) = (term3 m d' q d)).
Proof. exact (eq_refl ((Nat.add m n) = (term3 m d' q d))). Qed.
Lemma lem1247715 (p : nat) (n : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : ((term1 m n q d p) = ((Nat.add m n) = (term3 m d' q d))) = (((Nat.add m n) = (term5 p q d)) = ((Nat.add m n) = (term3 m d' q d))).
Proof. exact (MK_COMB (@lem1247713 m n p q d) (@lem1247714 n m d' q d)). Qed.
Lemma lem1247716 (p : nat) (n : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : ((term1 m n q d p) = (term2 n q d m d')) = (((Nat.add m n) = (term5 p q d)) = ((Nat.add m n) = (term3 m d' q d))).
Proof. exact (TRANS (@lem1247710 p n m d' q d) (@lem1247715 p n m d' q d)). Qed.
Lemma lem1247717 (n : nat) (q : nat) (d : nat) (p : nat) (m : nat) (d' : nat) (h1 : p = (Nat.add m d')) : ((Nat.add m n) = (term5 p q d)) = ((Nat.add m n) = (term3 m d' q d)).
Proof. exact (EQ_MP (@lem1247716 p n m d' q d) (@lem1247707 n q d p m d' h1)). Qed.
Lemma lem1247718 (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : (Nat.add m n) = (term5 p q d)) : (Nat.add m n) = (term3 m d' q d).
Proof. exact (EQ_MP (@lem1247717 n q d p m d' h1) (@lem1247613 m n p q d h2)). Qed.
