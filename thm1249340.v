Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249340_term_abbrevs.
Require Import thm1248022_spec.
Lemma lem1249313 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249328 (d'' : nat) (p : nat) (d' : nat) (n : nat) : (term1 d'' p d' n) = (term1 d'' p d' n).
Proof. exact (eq_refl (term1 d'' p d' n)). Qed.
Lemma lem1249329 (p : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 d'' p d' n d) = (term3 p n d' d'' d''').
Proof. exact (MK_COMB (@lem1249328 d'' p d' n) (@lem1249313 d d' d'' d''' h1)). Qed.
Lemma lem1249330 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 p n d' d'' d''') = ((term4 p n d'') = (term5 p n d' d'' d''')).
Proof. exact (eq_refl (term3 p n d' d'' d''')). Qed.
Lemma lem1249331 (d'' : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : (term6 d'' p d' n d) = (term6 d'' p d' n d).
Proof. exact (eq_refl (term6 d'' p d' n d)). Qed.
Lemma lem1249332 (d : nat) (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d'' p d' n d) = (term3 p n d' d'' d''')) = ((term2 d'' p d' n d) = ((term4 p n d'') = (term5 p n d' d'' d'''))).
Proof. exact (MK_COMB (@lem1249331 d'' p d' n d) (@lem1249330 p n d' d'' d''')). Qed.
Lemma lem1249333 (d'' : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : (term2 d'' p d' n d) = ((term4 p n d'') = (term7 p d' n d)).
Proof. exact (eq_refl (term2 d'' p d' n d)). Qed.
Lemma lem1249334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249335 (d'' : nat) (p : nat) (d' : nat) (n : nat) (d : nat) : (term6 d'' p d' n d) = (term8 d'' p d' n d).
Proof. exact (MK_COMB (@lem1249334) (@lem1249333 d'' p d' n d)). Qed.
Lemma lem1249336 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term4 p n d'') = (term5 p n d' d'' d''')) = ((term4 p n d'') = (term5 p n d' d'' d''')).
Proof. exact (eq_refl ((term4 p n d'') = (term5 p n d' d'' d'''))). Qed.
Lemma lem1249337 (d : nat) (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d'' p d' n d) = ((term4 p n d'') = (term5 p n d' d'' d'''))) = (((term4 p n d'') = (term7 p d' n d)) = ((term4 p n d'') = (term5 p n d' d'' d'''))).
Proof. exact (MK_COMB (@lem1249335 d'' p d' n d) (@lem1249336 p n d' d'' d''')). Qed.
Lemma lem1249338 (d : nat) (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d'' p d' n d) = (term3 p n d' d'' d''')) = (((term4 p n d'') = (term7 p d' n d)) = ((term4 p n d'') = (term5 p n d' d'' d'''))).
Proof. exact (TRANS (@lem1249332 d p n d' d'' d''') (@lem1249337 d p n d' d'' d''')). Qed.
Lemma lem1249339 (p : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((term4 p n d'') = (term7 p d' n d)) = ((term4 p n d'') = (term5 p n d' d'' d''')).
Proof. exact (EQ_MP (@lem1249338 d p n d' d'' d''') (@lem1249329 p n d d' d'' d''' h1)). Qed.
Lemma lem1249340 (d''' : nat) (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : d = (term0 d' d'' d''')) (h2 : m = (Nat.add p d')) (h3 : q = (Nat.add n d'')) (h4 : (Nat.add p q) = (term9 m n d)) : (term4 p n d'') = (term5 p n d' d'' d''').
Proof. exact (EQ_MP (@lem1249339 p n d d' d'' d''' h1) (@lem1248022 d' d'' p q m n d h2 h3 h4)). Qed.
