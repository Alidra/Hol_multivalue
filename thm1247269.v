Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247269_term_abbrevs.
Lemma lem1247256 (p : nat) (m : nat) (d : nat) (h1 : p = (Nat.add m d)) : p = (Nat.add m d).
Proof. exact (h1). Qed.
Lemma lem1247257 (d : nat) (m : nat) (n : nat) : (term0 d m n) = (term0 d m n).
Proof. exact (eq_refl (term0 d m n)). Qed.
Lemma lem1247258 (n : nat) (p : nat) (m : nat) (d : nat) (h1 : p = (Nat.add m d)) : (term1 d m n p) = (term2 n m d).
Proof. exact (MK_COMB (@lem1247257 d m n) (@lem1247256 p m d h1)). Qed.
Lemma lem1247259 (n : nat) (m : nat) (d : nat) : (term2 n m d) = (term3 n m d).
Proof. exact (eq_refl (term2 n m d)). Qed.
Lemma lem1247260 (d : nat) (m : nat) (n : nat) (p : nat) : (term4 d m n p) = (term4 d m n p).
Proof. exact (eq_refl (term4 d m n p)). Qed.
Lemma lem1247261 (p : nat) (n : nat) (m : nat) (d : nat) : ((term1 d m n p) = (term2 n m d)) = ((term1 d m n p) = (term3 n m d)).
Proof. exact (MK_COMB (@lem1247260 d m n p) (@lem1247259 n m d)). Qed.
Lemma lem1247262 (d : nat) (m : nat) (n : nat) (p : nat) : (term1 d m n p) = (term5 d m n p).
Proof. exact (eq_refl (term1 d m n p)). Qed.
Lemma lem1247263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247264 (d : nat) (m : nat) (n : nat) (p : nat) : (term4 d m n p) = (term6 d m n p).
Proof. exact (MK_COMB (@lem1247263) (@lem1247262 d m n p)). Qed.
Lemma lem1247265 (n : nat) (m : nat) (d : nat) : (term3 n m d) = (term3 n m d).
Proof. exact (eq_refl (term3 n m d)). Qed.
Lemma lem1247266 (p : nat) (n : nat) (m : nat) (d : nat) : ((term1 d m n p) = (term3 n m d)) = ((term5 d m n p) = (term3 n m d)).
Proof. exact (MK_COMB (@lem1247264 d m n p) (@lem1247265 n m d)). Qed.
Lemma lem1247267 (p : nat) (n : nat) (m : nat) (d : nat) : ((term1 d m n p) = (term2 n m d)) = ((term5 d m n p) = (term3 n m d)).
Proof. exact (TRANS (@lem1247261 p n m d) (@lem1247266 p n m d)). Qed.
Lemma lem1247268 (n : nat) (p : nat) (m : nat) (d : nat) (h1 : p = (Nat.add m d)) : (term5 d m n p) = (term3 n m d).
Proof. exact (EQ_MP (@lem1247267 p n m d) (@lem1247258 n p m d h1)). Qed.
Lemma lem1247269 (n : nat) (p : nat) (m : nat) (d : nat) (h1 : p = (Nat.add m d)) : (term3 n m d) = (term5 d m n p).
Proof. exact (SYM (@lem1247268 n p m d h1)). Qed.
