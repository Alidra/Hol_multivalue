Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248132_term_abbrevs.
Lemma lem1248119 (m : nat) (p : nat) (d : nat) (h1 : m = (Nat.add p d)) : m = (Nat.add p d).
Proof. exact (h1). Qed.
Lemma lem1248120 (d : nat) (p : nat) (n : nat) (q : nat) : (term0 d p n q) = (term0 d p n q).
Proof. exact (eq_refl (term0 d p n q)). Qed.
Lemma lem1248121 (n : nat) (q : nat) (m : nat) (p : nat) (d : nat) (h1 : m = (Nat.add p d)) : (term1 d p n q m) = (term2 n q p d).
Proof. exact (MK_COMB (@lem1248120 d p n q) (@lem1248119 m p d h1)). Qed.
Lemma lem1248122 (d : nat) (p : nat) (n : nat) (q : nat) : (term2 n q p d) = (term3 d p n q).
Proof. exact (eq_refl (term2 n q p d)). Qed.
Lemma lem1248123 (d : nat) (p : nat) (n : nat) (q : nat) (m : nat) : (term4 d p n q m) = (term4 d p n q m).
Proof. exact (eq_refl (term4 d p n q m)). Qed.
Lemma lem1248124 (m : nat) (d : nat) (p : nat) (n : nat) (q : nat) : ((term1 d p n q m) = (term2 n q p d)) = ((term1 d p n q m) = (term3 d p n q)).
Proof. exact (MK_COMB (@lem1248123 d p n q m) (@lem1248122 d p n q)). Qed.
Lemma lem1248125 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term1 d p n q m) = (term5 d m p n q).
Proof. exact (eq_refl (term1 d p n q m)). Qed.
Lemma lem1248126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248127 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term4 d p n q m) = (term6 d m p n q).
Proof. exact (MK_COMB (@lem1248126) (@lem1248125 d m p n q)). Qed.
Lemma lem1248128 (d : nat) (p : nat) (n : nat) (q : nat) : (term3 d p n q) = (term3 d p n q).
Proof. exact (eq_refl (term3 d p n q)). Qed.
Lemma lem1248129 (m : nat) (d : nat) (p : nat) (n : nat) (q : nat) : ((term1 d p n q m) = (term3 d p n q)) = ((term5 d m p n q) = (term3 d p n q)).
Proof. exact (MK_COMB (@lem1248127 d m p n q) (@lem1248128 d p n q)). Qed.
Lemma lem1248130 (m : nat) (d : nat) (p : nat) (n : nat) (q : nat) : ((term1 d p n q m) = (term2 n q p d)) = ((term5 d m p n q) = (term3 d p n q)).
Proof. exact (TRANS (@lem1248124 m d p n q) (@lem1248129 m d p n q)). Qed.
Lemma lem1248131 (n : nat) (q : nat) (m : nat) (p : nat) (d : nat) (h1 : m = (Nat.add p d)) : (term5 d m p n q) = (term3 d p n q).
Proof. exact (EQ_MP (@lem1248130 m d p n q) (@lem1248121 n q m p d h1)). Qed.
Lemma lem1248132 (n : nat) (q : nat) (m : nat) (p : nat) (d : nat) (h1 : m = (Nat.add p d)) : (term3 d p n q) = (term5 d m p n q).
Proof. exact (SYM (@lem1248131 n q m p d h1)). Qed.
