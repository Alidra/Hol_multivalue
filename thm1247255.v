Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1247255_term_abbrevs.
Lemma lem1247242 (m : nat) (p : nat) (d : nat) (h1 : m = (Nat.add p d)) : m = (Nat.add p d).
Proof. exact (h1). Qed.
Lemma lem1247243 (d : nat) (n : nat) (p : nat) : (term0 d n p) = (term0 d n p).
Proof. exact (eq_refl (term0 d n p)). Qed.
Lemma lem1247244 (n : nat) (m : nat) (p : nat) (d : nat) (h1 : m = (Nat.add p d)) : (term1 d n p m) = (term2 n p d).
Proof. exact (MK_COMB (@lem1247243 d n p) (@lem1247242 m p d h1)). Qed.
Lemma lem1247245 (d : nat) (n : nat) (p : nat) : (term2 n p d) = (term3 d n p).
Proof. exact (eq_refl (term2 n p d)). Qed.
Lemma lem1247246 (d : nat) (n : nat) (p : nat) (m : nat) : (term4 d n p m) = (term4 d n p m).
Proof. exact (eq_refl (term4 d n p m)). Qed.
Lemma lem1247247 (m : nat) (d : nat) (n : nat) (p : nat) : ((term1 d n p m) = (term2 n p d)) = ((term1 d n p m) = (term3 d n p)).
Proof. exact (MK_COMB (@lem1247246 d n p m) (@lem1247245 d n p)). Qed.
Lemma lem1247248 (d : nat) (m : nat) (n : nat) (p : nat) : (term1 d n p m) = (term5 d m n p).
Proof. exact (eq_refl (term1 d n p m)). Qed.
Lemma lem1247249 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1247250 (d : nat) (m : nat) (n : nat) (p : nat) : (term4 d n p m) = (term6 d m n p).
Proof. exact (MK_COMB (@lem1247249) (@lem1247248 d m n p)). Qed.
Lemma lem1247251 (d : nat) (n : nat) (p : nat) : (term3 d n p) = (term3 d n p).
Proof. exact (eq_refl (term3 d n p)). Qed.
Lemma lem1247252 (m : nat) (d : nat) (n : nat) (p : nat) : ((term1 d n p m) = (term3 d n p)) = ((term5 d m n p) = (term3 d n p)).
Proof. exact (MK_COMB (@lem1247250 d m n p) (@lem1247251 d n p)). Qed.
Lemma lem1247253 (m : nat) (d : nat) (n : nat) (p : nat) : ((term1 d n p m) = (term2 n p d)) = ((term5 d m n p) = (term3 d n p)).
Proof. exact (TRANS (@lem1247247 m d n p) (@lem1247252 m d n p)). Qed.
Lemma lem1247254 (n : nat) (m : nat) (p : nat) (d : nat) (h1 : m = (Nat.add p d)) : (term5 d m n p) = (term3 d n p).
Proof. exact (EQ_MP (@lem1247253 m d n p) (@lem1247244 n m p d h1)). Qed.
Lemma lem1247255 (n : nat) (m : nat) (p : nat) (d : nat) (h1 : m = (Nat.add p d)) : (term3 d n p) = (term5 d m n p).
Proof. exact (SYM (@lem1247254 n m p d h1)). Qed.
