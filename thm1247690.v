Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247690_term_abbrevs.
Require Import thm1247613_spec.
Lemma lem1247663 (m : nat) (p : nat) (d' : nat) (h1 : m = (Nat.add p d')) : m = (Nat.add p d').
Proof. exact (h1). Qed.
Lemma lem1247678 (n : nat) (p : nat) (q : nat) (d : nat) : (term0 n p q d) = (term0 n p q d).
Proof. exact (eq_refl (term0 n p q d)). Qed.
Lemma lem1247679 (n : nat) (q : nat) (d : nat) (m : nat) (p : nat) (d' : nat) (h1 : m = (Nat.add p d')) : (term1 n p q d m) = (term2 n q d p d').
Proof. exact (MK_COMB (@lem1247678 n p q d) (@lem1247663 m p d' h1)). Qed.
Lemma lem1247680 (d' : nat) (n : nat) (p : nat) (q : nat) (d : nat) : (term2 n q d p d') = ((term3 p d' n) = (term3 p q d)).
Proof. exact (eq_refl (term2 n q d p d')). Qed.
Lemma lem1247681 (n : nat) (p : nat) (q : nat) (d : nat) (m : nat) : (term4 n p q d m) = (term4 n p q d m).
Proof. exact (eq_refl (term4 n p q d m)). Qed.
Lemma lem1247682 (m : nat) (d' : nat) (n : nat) (p : nat) (q : nat) (d : nat) : ((term1 n p q d m) = (term2 n q d p d')) = ((term1 n p q d m) = ((term3 p d' n) = (term3 p q d))).
Proof. exact (MK_COMB (@lem1247681 n p q d m) (@lem1247680 d' n p q d)). Qed.
Lemma lem1247683 (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) : (term1 n p q d m) = ((Nat.add m n) = (term3 p q d)).
Proof. exact (eq_refl (term1 n p q d m)). Qed.
Lemma lem1247684 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247685 (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) : (term4 n p q d m) = (term5 m n p q d).
Proof. exact (MK_COMB (@lem1247684) (@lem1247683 m n p q d)). Qed.
Lemma lem1247686 (d' : nat) (n : nat) (p : nat) (q : nat) (d : nat) : ((term3 p d' n) = (term3 p q d)) = ((term3 p d' n) = (term3 p q d)).
Proof. exact (eq_refl ((term3 p d' n) = (term3 p q d))). Qed.
Lemma lem1247687 (m : nat) (d' : nat) (n : nat) (p : nat) (q : nat) (d : nat) : ((term1 n p q d m) = ((term3 p d' n) = (term3 p q d))) = (((Nat.add m n) = (term3 p q d)) = ((term3 p d' n) = (term3 p q d))).
Proof. exact (MK_COMB (@lem1247685 m n p q d) (@lem1247686 d' n p q d)). Qed.
Lemma lem1247688 (m : nat) (d' : nat) (n : nat) (p : nat) (q : nat) (d : nat) : ((term1 n p q d m) = (term2 n q d p d')) = (((Nat.add m n) = (term3 p q d)) = ((term3 p d' n) = (term3 p q d))).
Proof. exact (TRANS (@lem1247682 m d' n p q d) (@lem1247687 m d' n p q d)). Qed.
Lemma lem1247689 (n : nat) (q : nat) (d : nat) (m : nat) (p : nat) (d' : nat) (h1 : m = (Nat.add p d')) : ((Nat.add m n) = (term3 p q d)) = ((term3 p d' n) = (term3 p q d)).
Proof. exact (EQ_MP (@lem1247688 m d' n p q d) (@lem1247679 n q d m p d' h1)). Qed.
Lemma lem1247690 (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : (Nat.add m n) = (term3 p q d)) : (term3 p d' n) = (term3 p q d).
Proof. exact (EQ_MP (@lem1247689 n q d m p d' h1) (@lem1247613 m n p q d h2)). Qed.
