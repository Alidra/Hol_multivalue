Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247918_term_abbrevs.
Require Import thm1247628_spec.
Lemma lem1247891 (m : nat) (p : nat) (d' : nat) (h1 : m = (Nat.add p d')) : m = (Nat.add p d').
Proof. exact (h1). Qed.
Lemma lem1247906 (p : nat) (q : nat) (n : nat) (d : nat) : (term0 p q n d) = (term0 p q n d).
Proof. exact (eq_refl (term0 p q n d)). Qed.
Lemma lem1247907 (q : nat) (n : nat) (d : nat) (m : nat) (p : nat) (d' : nat) (h1 : m = (Nat.add p d')) : (term1 p q n d m) = (term2 q n d p d').
Proof. exact (MK_COMB (@lem1247906 p q n d) (@lem1247891 m p d' h1)). Qed.
Lemma lem1247908 (q : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : (term2 q n d p d') = ((Nat.add p q) = (term3 p d' n d)).
Proof. exact (eq_refl (term2 q n d p d')). Qed.
Lemma lem1247909 (p : nat) (q : nat) (n : nat) (d : nat) (m : nat) : (term4 p q n d m) = (term4 p q n d m).
Proof. exact (eq_refl (term4 p q n d m)). Qed.
Lemma lem1247910 (m : nat) (q : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : ((term1 p q n d m) = (term2 q n d p d')) = ((term1 p q n d m) = ((Nat.add p q) = (term3 p d' n d))).
Proof. exact (MK_COMB (@lem1247909 p q n d m) (@lem1247908 q p d' n d)). Qed.
Lemma lem1247911 (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) : (term1 p q n d m) = ((Nat.add p q) = (term5 m n d)).
Proof. exact (eq_refl (term1 p q n d m)). Qed.
Lemma lem1247912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247913 (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) : (term4 p q n d m) = (term6 p q m n d).
Proof. exact (MK_COMB (@lem1247912) (@lem1247911 p q m n d)). Qed.
Lemma lem1247914 (q : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : ((Nat.add p q) = (term3 p d' n d)) = ((Nat.add p q) = (term3 p d' n d)).
Proof. exact (eq_refl ((Nat.add p q) = (term3 p d' n d))). Qed.
Lemma lem1247915 (m : nat) (q : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : ((term1 p q n d m) = ((Nat.add p q) = (term3 p d' n d))) = (((Nat.add p q) = (term5 m n d)) = ((Nat.add p q) = (term3 p d' n d))).
Proof. exact (MK_COMB (@lem1247913 p q m n d) (@lem1247914 q p d' n d)). Qed.
Lemma lem1247916 (m : nat) (q : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : ((term1 p q n d m) = (term2 q n d p d')) = (((Nat.add p q) = (term5 m n d)) = ((Nat.add p q) = (term3 p d' n d))).
Proof. exact (TRANS (@lem1247910 m q p d' n d) (@lem1247915 m q p d' n d)). Qed.
Lemma lem1247917 (q : nat) (n : nat) (d : nat) (m : nat) (p : nat) (d' : nat) (h1 : m = (Nat.add p d')) : ((Nat.add p q) = (term5 m n d)) = ((Nat.add p q) = (term3 p d' n d)).
Proof. exact (EQ_MP (@lem1247916 m q p d' n d) (@lem1247907 q n d m p d' h1)). Qed.
Lemma lem1247918 (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : (Nat.add p q) = (term5 m n d)) : (Nat.add p q) = (term3 p d' n d).
Proof. exact (EQ_MP (@lem1247917 q n d m p d' h1) (@lem1247628 p q m n d h2)). Qed.
