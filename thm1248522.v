Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248522_term_abbrevs.
Require Import thm1248384_spec.
Lemma lem1248495 (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : n = (Nat.add q d'').
Proof. exact (h1). Qed.
Lemma lem1248510 (d : nat) (q : nat) (m : nat) (d' : nat) : (term0 d q m d') = (term0 d q m d').
Proof. exact (eq_refl (term0 d q m d')). Qed.
Lemma lem1248511 (d : nat) (m : nat) (d' : nat) (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : (term1 d q m d' n) = (term2 d m d' q d'').
Proof. exact (MK_COMB (@lem1248510 d q m d') (@lem1248495 n q d'' h1)). Qed.
Lemma lem1248512 (d : nat) (m : nat) (q : nat) (d'' : nat) (d' : nat) : (term2 d m d' q d'') = ((term3 m d q) = (term4 m q d'' d')).
Proof. exact (eq_refl (term2 d m d' q d'')). Qed.
Lemma lem1248513 (d : nat) (q : nat) (m : nat) (d' : nat) (n : nat) : (term5 d q m d' n) = (term5 d q m d' n).
Proof. exact (eq_refl (term5 d q m d' n)). Qed.
Lemma lem1248514 (n : nat) (d : nat) (m : nat) (q : nat) (d'' : nat) (d' : nat) : ((term1 d q m d' n) = (term2 d m d' q d'')) = ((term1 d q m d' n) = ((term3 m d q) = (term4 m q d'' d'))).
Proof. exact (MK_COMB (@lem1248513 d q m d' n) (@lem1248512 d m q d'' d')). Qed.
Lemma lem1248515 (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) : (term1 d q m d' n) = ((term3 m d q) = (term3 m n d')).
Proof. exact (eq_refl (term1 d q m d' n)). Qed.
Lemma lem1248516 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248517 (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) : (term5 d q m d' n) = (term6 d q m n d').
Proof. exact (MK_COMB (@lem1248516) (@lem1248515 d q m n d')). Qed.
Lemma lem1248518 (d : nat) (m : nat) (q : nat) (d'' : nat) (d' : nat) : ((term3 m d q) = (term4 m q d'' d')) = ((term3 m d q) = (term4 m q d'' d')).
Proof. exact (eq_refl ((term3 m d q) = (term4 m q d'' d'))). Qed.
Lemma lem1248519 (n : nat) (d : nat) (m : nat) (q : nat) (d'' : nat) (d' : nat) : ((term1 d q m d' n) = ((term3 m d q) = (term4 m q d'' d'))) = (((term3 m d q) = (term3 m n d')) = ((term3 m d q) = (term4 m q d'' d'))).
Proof. exact (MK_COMB (@lem1248517 d q m n d') (@lem1248518 d m q d'' d')). Qed.
Lemma lem1248520 (n : nat) (d : nat) (m : nat) (q : nat) (d'' : nat) (d' : nat) : ((term1 d q m d' n) = (term2 d m d' q d'')) = (((term3 m d q) = (term3 m n d')) = ((term3 m d q) = (term4 m q d'' d'))).
Proof. exact (TRANS (@lem1248514 n d m q d'' d') (@lem1248519 n d m q d'' d')). Qed.
Lemma lem1248521 (d : nat) (m : nat) (d' : nat) (n : nat) (q : nat) (d'' : nat) (h1 : n = (Nat.add q d'')) : ((term3 m d q) = (term3 m n d')) = ((term3 m d q) = (term4 m q d'' d')).
Proof. exact (EQ_MP (@lem1248520 n d m q d'' d') (@lem1248511 d m d' n q d'' h1)). Qed.
Lemma lem1248522 (d'' : nat) (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : n = (Nat.add q d'')) (h2 : (term3 m d q) = (term3 m n d')) : (term3 m d q) = (term4 m q d'' d').
Proof. exact (EQ_MP (@lem1248521 d m d' n q d'' h1) (@lem1248384 d q m n d' h2)). Qed.
