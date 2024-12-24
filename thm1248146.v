Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248146_term_abbrevs.
Lemma lem1248133 (p : nat) (m : nat) (d : nat) (h1 : p = (Nat.add m d)) : p = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem1248134 (d : nat) (m : nat) (n : nat) (q : nat) : (term0 d m n q) = (term0 d m n q).
Proof. exact (eq_refl (term0 d m n q)). Qed.
Lemma lem1248135 (n : nat) (q : nat) (p : nat) (m : nat) (d : nat) (h1 : p = (Nat.add m d)) : (term1 d m n q p) = (term2 n q m d).
Proof. exact (MK_COMB (@lem1248134 d m n q) (@lem1248133 p m d h1)). Qed.
Lemma lem1248136 (m : nat) (d : nat) (n : nat) (q : nat) : (term2 n q m d) = (term3 m d n q).
Proof. exact (eq_refl (term2 n q m d)). Qed.
Lemma lem1248137 (d : nat) (m : nat) (n : nat) (q : nat) (p : nat) : (term4 d m n q p) = (term4 d m n q p).
Proof. exact (eq_refl (term4 d m n q p)). Qed.
Lemma lem1248138 (p : nat) (m : nat) (d : nat) (n : nat) (q : nat) : ((term1 d m n q p) = (term2 n q m d)) = ((term1 d m n q p) = (term3 m d n q)).
Proof. exact (MK_COMB (@lem1248137 d m n q p) (@lem1248136 m d n q)). Qed.
Lemma lem1248139 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term1 d m n q p) = (term5 d m p n q).
Proof. exact (eq_refl (term1 d m n q p)). Qed.
Lemma lem1248140 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248141 (d : nat) (m : nat) (p : nat) (n : nat) (q : nat) : (term4 d m n q p) = (term6 d m p n q).
Proof. exact (MK_COMB (@lem1248140) (@lem1248139 d m p n q)). Qed.
Lemma lem1248142 (m : nat) (d : nat) (n : nat) (q : nat) : (term3 m d n q) = (term3 m d n q).
Proof. exact (eq_refl (term3 m d n q)). Qed.
Lemma lem1248143 (p : nat) (m : nat) (d : nat) (n : nat) (q : nat) : ((term1 d m n q p) = (term3 m d n q)) = ((term5 d m p n q) = (term3 m d n q)).
Proof. exact (MK_COMB (@lem1248141 d m p n q) (@lem1248142 m d n q)). Qed.
Lemma lem1248144 (p : nat) (m : nat) (d : nat) (n : nat) (q : nat) : ((term1 d m n q p) = (term2 n q m d)) = ((term5 d m p n q) = (term3 m d n q)).
Proof. exact (TRANS (@lem1248138 p m d n q) (@lem1248143 p m d n q)). Qed.
Lemma lem1248145 (n : nat) (q : nat) (p : nat) (m : nat) (d : nat) (h1 : p = (Nat.add m d)) : (term5 d m p n q) = (term3 m d n q).
Proof. exact (EQ_MP (@lem1248144 p m d n q) (@lem1248135 n q p m d h1)). Qed.
Lemma lem1248146 (n : nat) (q : nat) (p : nat) (m : nat) (d : nat) (h1 : p = (Nat.add m d)) : (term3 m d n q) = (term5 d m p n q).
Proof. exact (SYM (@lem1248145 n q p m d h1)). Qed.
