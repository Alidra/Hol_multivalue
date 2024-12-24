Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248098_term_abbrevs.
Require Import thm1247946_spec.
Lemma lem1248071 (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : q = (Nat.add n d'').
Proof. exact (h1). Qed.
Lemma lem1248086 (d' : nat) (m : nat) (n : nat) (d : nat) : (term0 d' m n d) = (term0 d' m n d).
Proof. exact (eq_refl (term0 d' m n d)). Qed.
Lemma lem1248087 (d' : nat) (m : nat) (d : nat) (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : (term1 d' m n d q) = (term2 d' m d n d'').
Proof. exact (MK_COMB (@lem1248086 d' m n d) (@lem1248071 q n d'' h1)). Qed.
Lemma lem1248088 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d : nat) : (term2 d' m d n d'') = ((term3 m d' n d'') = (term4 m n d)).
Proof. exact (eq_refl (term2 d' m d n d'')). Qed.
Lemma lem1248089 (d' : nat) (m : nat) (n : nat) (d : nat) (q : nat) : (term5 d' m n d q) = (term5 d' m n d q).
Proof. exact (eq_refl (term5 d' m n d q)). Qed.
Lemma lem1248090 (q : nat) (d' : nat) (d'' : nat) (m : nat) (n : nat) (d : nat) : ((term1 d' m n d q) = (term2 d' m d n d'')) = ((term1 d' m n d q) = ((term3 m d' n d'') = (term4 m n d))).
Proof. exact (MK_COMB (@lem1248089 d' m n d q) (@lem1248088 d' d'' m n d)). Qed.
Lemma lem1248091 (d' : nat) (q : nat) (m : nat) (n : nat) (d : nat) : (term1 d' m n d q) = ((term4 m d' q) = (term4 m n d)).
Proof. exact (eq_refl (term1 d' m n d q)). Qed.
Lemma lem1248092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248093 (d' : nat) (q : nat) (m : nat) (n : nat) (d : nat) : (term5 d' m n d q) = (term6 d' q m n d).
Proof. exact (MK_COMB (@lem1248092) (@lem1248091 d' q m n d)). Qed.
Lemma lem1248094 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d : nat) : ((term3 m d' n d'') = (term4 m n d)) = ((term3 m d' n d'') = (term4 m n d)).
Proof. exact (eq_refl ((term3 m d' n d'') = (term4 m n d))). Qed.
Lemma lem1248095 (q : nat) (d' : nat) (d'' : nat) (m : nat) (n : nat) (d : nat) : ((term1 d' m n d q) = ((term3 m d' n d'') = (term4 m n d))) = (((term4 m d' q) = (term4 m n d)) = ((term3 m d' n d'') = (term4 m n d))).
Proof. exact (MK_COMB (@lem1248093 d' q m n d) (@lem1248094 d' d'' m n d)). Qed.
Lemma lem1248096 (q : nat) (d' : nat) (d'' : nat) (m : nat) (n : nat) (d : nat) : ((term1 d' m n d q) = (term2 d' m d n d'')) = (((term4 m d' q) = (term4 m n d)) = ((term3 m d' n d'') = (term4 m n d))).
Proof. exact (TRANS (@lem1248090 q d' d'' m n d) (@lem1248095 q d' d'' m n d)). Qed.
Lemma lem1248097 (d' : nat) (m : nat) (d : nat) (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : ((term4 m d' q) = (term4 m n d)) = ((term3 m d' n d'') = (term4 m n d)).
Proof. exact (EQ_MP (@lem1248096 q d' d'' m n d) (@lem1248087 d' m d q n d'' h1)). Qed.
Lemma lem1248098 (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : p = (Nat.add m d')) (h2 : q = (Nat.add n d'')) (h3 : (Nat.add p q) = (term4 m n d)) : (term3 m d' n d'') = (term4 m n d).
Proof. exact (EQ_MP (@lem1248097 d' m d q n d'' h2) (@lem1247946 d' p q m n d h1 h3)). Qed.
