Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248022_term_abbrevs.
Require Import thm1247918_spec.
Lemma lem1247995 (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : q = (Nat.add n d'').
Proof. exact (h1). Qed.
Lemma lem1248010 (p : nat) (d' : nat) (n : nat) (d : nat) : (term0 p d' n d) = (term0 p d' n d).
Proof. exact (eq_refl (term0 p d' n d)). Qed.
Lemma lem1248011 (p : nat) (d' : nat) (d : nat) (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : (term1 p d' n d q) = (term2 p d' d n d'').
Proof. exact (MK_COMB (@lem1248010 p d' n d) (@lem1247995 q n d'' h1)). Qed.
Lemma lem1248012 (d'' : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : (term2 p d' d n d'') = ((term3 p n d'') = (term4 p d' n d)).
Proof. exact (eq_refl (term2 p d' d n d'')). Qed.
Lemma lem1248013 (p : nat) (d' : nat) (n : nat) (d : nat) (q : nat) : (term5 p d' n d q) = (term5 p d' n d q).
Proof. exact (eq_refl (term5 p d' n d q)). Qed.
Lemma lem1248014 (q : nat) (d'' : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : ((term1 p d' n d q) = (term2 p d' d n d'')) = ((term1 p d' n d q) = ((term3 p n d'') = (term4 p d' n d))).
Proof. exact (MK_COMB (@lem1248013 p d' n d q) (@lem1248012 d'' p d' n d)). Qed.
Lemma lem1248015 (q : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : (term1 p d' n d q) = ((Nat.add p q) = (term4 p d' n d)).
Proof. exact (eq_refl (term1 p d' n d q)). Qed.
Lemma lem1248016 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248017 (q : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : (term5 p d' n d q) = (term6 q p d' n d).
Proof. exact (MK_COMB (@lem1248016) (@lem1248015 q p d' n d)). Qed.
Lemma lem1248018 (d'' : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : ((term3 p n d'') = (term4 p d' n d)) = ((term3 p n d'') = (term4 p d' n d)).
Proof. exact (eq_refl ((term3 p n d'') = (term4 p d' n d))). Qed.
Lemma lem1248019 (q : nat) (d'' : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : ((term1 p d' n d q) = ((term3 p n d'') = (term4 p d' n d))) = (((Nat.add p q) = (term4 p d' n d)) = ((term3 p n d'') = (term4 p d' n d))).
Proof. exact (MK_COMB (@lem1248017 q p d' n d) (@lem1248018 d'' p d' n d)). Qed.
Lemma lem1248020 (q : nat) (d'' : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : ((term1 p d' n d q) = (term2 p d' d n d'')) = (((Nat.add p q) = (term4 p d' n d)) = ((term3 p n d'') = (term4 p d' n d))).
Proof. exact (TRANS (@lem1248014 q d'' p d' n d) (@lem1248019 q d'' p d' n d)). Qed.
Lemma lem1248021 (p : nat) (d' : nat) (d : nat) (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : ((Nat.add p q) = (term4 p d' n d)) = ((term3 p n d'') = (term4 p d' n d)).
Proof. exact (EQ_MP (@lem1248020 q d'' p d' n d) (@lem1248011 p d' d q n d'' h1)). Qed.
Lemma lem1248022 (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : m = (Nat.add p d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add p q) = (term7 m n d)) : (term3 p n d'') = (term4 p d' n d).
Proof. exact (EQ_MP (@lem1248021 p d' d q n d'' h2) (@lem1247918 d' p q m n d h1 h3)). Qed.
