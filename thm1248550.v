Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248550_term_abbrevs.
Require Import thm1248384_spec.
Lemma lem1248523 (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : q = (Nat.add n d'').
Proof. exact (h1). Qed.
Lemma lem1248538 (d : nat) (m : nat) (n : nat) (d' : nat) : (term0 d m n d') = (term0 d m n d').
Proof. exact (eq_refl (term0 d m n d')). Qed.
Lemma lem1248539 (d : nat) (m : nat) (d' : nat) (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : (term1 d m n d' q) = (term2 d m d' n d'').
Proof. exact (MK_COMB (@lem1248538 d m n d') (@lem1248523 q n d'' h1)). Qed.
Lemma lem1248540 (d : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat) : (term2 d m d' n d'') = ((term3 m d n d'') = (term4 m n d')).
Proof. exact (eq_refl (term2 d m d' n d'')). Qed.
Lemma lem1248541 (d : nat) (m : nat) (n : nat) (d' : nat) (q : nat) : (term5 d m n d' q) = (term5 d m n d' q).
Proof. exact (eq_refl (term5 d m n d' q)). Qed.
Lemma lem1248542 (q : nat) (d : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat) : ((term1 d m n d' q) = (term2 d m d' n d'')) = ((term1 d m n d' q) = ((term3 m d n d'') = (term4 m n d'))).
Proof. exact (MK_COMB (@lem1248541 d m n d' q) (@lem1248540 d d'' m n d')). Qed.
Lemma lem1248543 (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) : (term1 d m n d' q) = ((term4 m d q) = (term4 m n d')).
Proof. exact (eq_refl (term1 d m n d' q)). Qed.
Lemma lem1248544 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248545 (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) : (term5 d m n d' q) = (term6 d q m n d').
Proof. exact (MK_COMB (@lem1248544) (@lem1248543 d q m n d')). Qed.
Lemma lem1248546 (d : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat) : ((term3 m d n d'') = (term4 m n d')) = ((term3 m d n d'') = (term4 m n d')).
Proof. exact (eq_refl ((term3 m d n d'') = (term4 m n d'))). Qed.
Lemma lem1248547 (q : nat) (d : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat) : ((term1 d m n d' q) = ((term3 m d n d'') = (term4 m n d'))) = (((term4 m d q) = (term4 m n d')) = ((term3 m d n d'') = (term4 m n d'))).
Proof. exact (MK_COMB (@lem1248545 d q m n d') (@lem1248546 d d'' m n d')). Qed.
Lemma lem1248548 (q : nat) (d : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat) : ((term1 d m n d' q) = (term2 d m d' n d'')) = (((term4 m d q) = (term4 m n d')) = ((term3 m d n d'') = (term4 m n d'))).
Proof. exact (TRANS (@lem1248542 q d d'' m n d') (@lem1248547 q d d'' m n d')). Qed.
Lemma lem1248549 (d : nat) (m : nat) (d' : nat) (q : nat) (n : nat) (d'' : nat) (h1 : q = (Nat.add n d'')) : ((term4 m d q) = (term4 m n d')) = ((term3 m d n d'') = (term4 m n d')).
Proof. exact (EQ_MP (@lem1248548 q d d'' m n d') (@lem1248539 d m d' q n d'' h1)). Qed.
Lemma lem1248550 (d'' : nat) (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : q = (Nat.add n d'')) (h2 : (term4 m d q) = (term4 m n d')) : (term3 m d n d'') = (term4 m n d').
Proof. exact (EQ_MP (@lem1248549 d m d' q n d'' h1) (@lem1248384 d q m n d' h2)). Qed.
