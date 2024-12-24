Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248070_term_abbrevs.
Require Import thm1247946_spec.
Lemma lem1248043 (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : n = (Nat.add q d'').
Proof. exact (h1). Qed.
Lemma lem1248058 (d' : nat) (q : nat) (m : nat) (d : nat) : (term0 d' q m d) = (term0 d' q m d).
Proof. exact (eq_refl (term0 d' q m d)). Qed.
Lemma lem1248059 (d' : nat) (m : nat) (d : nat) (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : (term1 d' q m d n) = (term2 d' m d q d'').
Proof. exact (MK_COMB (@lem1248058 d' q m d) (@lem1248043 n q d'' h1)). Qed.
Lemma lem1248060 (d' : nat) (m : nat) (q : nat) (d'' : nat) (d : nat) : (term2 d' m d q d'') = ((term3 m d' q) = (term4 m q d'' d)).
Proof. exact (eq_refl (term2 d' m d q d'')). Qed.
Lemma lem1248061 (d' : nat) (q : nat) (m : nat) (d : nat) (n : nat) : (term5 d' q m d n) = (term5 d' q m d n).
Proof. exact (eq_refl (term5 d' q m d n)). Qed.
Lemma lem1248062 (n : nat) (d' : nat) (m : nat) (q : nat) (d'' : nat) (d : nat) : ((term1 d' q m d n) = (term2 d' m d q d'')) = ((term1 d' q m d n) = ((term3 m d' q) = (term4 m q d'' d))).
Proof. exact (MK_COMB (@lem1248061 d' q m d n) (@lem1248060 d' m q d'' d)). Qed.
Lemma lem1248063 (d' : nat) (q : nat) (m : nat) (n : nat) (d : nat) : (term1 d' q m d n) = ((term3 m d' q) = (term3 m n d)).
Proof. exact (eq_refl (term1 d' q m d n)). Qed.
Lemma lem1248064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248065 (d' : nat) (q : nat) (m : nat) (n : nat) (d : nat) : (term5 d' q m d n) = (term6 d' q m n d).
Proof. exact (MK_COMB (@lem1248064) (@lem1248063 d' q m n d)). Qed.
Lemma lem1248066 (d' : nat) (m : nat) (q : nat) (d'' : nat) (d : nat) : ((term3 m d' q) = (term4 m q d'' d)) = ((term3 m d' q) = (term4 m q d'' d)).
Proof. exact (eq_refl ((term3 m d' q) = (term4 m q d'' d))). Qed.
Lemma lem1248067 (n : nat) (d' : nat) (m : nat) (q : nat) (d'' : nat) (d : nat) : ((term1 d' q m d n) = ((term3 m d' q) = (term4 m q d'' d))) = (((term3 m d' q) = (term3 m n d)) = ((term3 m d' q) = (term4 m q d'' d))).
Proof. exact (MK_COMB (@lem1248065 d' q m n d) (@lem1248066 d' m q d'' d)). Qed.
Lemma lem1248068 (n : nat) (d' : nat) (m : nat) (q : nat) (d'' : nat) (d : nat) : ((term1 d' q m d n) = (term2 d' m d q d'')) = (((term3 m d' q) = (term3 m n d)) = ((term3 m d' q) = (term4 m q d'' d))).
Proof. exact (TRANS (@lem1248062 n d' m q d'' d) (@lem1248067 n d' m q d'' d)). Qed.
Lemma lem1248069 (d' : nat) (m : nat) (d : nat) (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : ((term3 m d' q) = (term3 m n d)) = ((term3 m d' q) = (term4 m q d'' d)).
Proof. exact (EQ_MP (@lem1248068 n d' m q d'' d) (@lem1248059 d' m d n q d'' h1)). Qed.
Lemma lem1248070 (d'' : nat) (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : n = (Nat.add q d'')) (h2 : p = (Nat.add m d')) (h3 : (Nat.add p q) = (term3 m n d)) : (term3 m d' q) = (term4 m q d'' d).
Proof. exact (EQ_MP (@lem1248069 d' m d n q d'' h1) (@lem1247946 d' p q m n d h2 h3)). Qed.
