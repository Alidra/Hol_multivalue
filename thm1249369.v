Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249369_term_abbrevs.
Require Import thm1248070_spec.
Lemma lem1249342 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249357 (d' : nat) (m : nat) (q : nat) (d'' : nat) : (term1 d' m q d'') = (term1 d' m q d'').
Proof. exact (eq_refl (term1 d' m q d'')). Qed.
Lemma lem1249358 (m : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 d' m q d'' d) = (term3 m q d' d'' d''').
Proof. exact (MK_COMB (@lem1249357 d' m q d'') (@lem1249342 d d' d'' d''' h1)). Qed.
Lemma lem1249359 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 m q d' d'' d''') = ((term4 m d' q) = (term5 m q d' d'' d''')).
Proof. exact (eq_refl (term3 m q d' d'' d''')). Qed.
Lemma lem1249360 (d' : nat) (m : nat) (q : nat) (d'' : nat) (d : nat) : (term6 d' m q d'' d) = (term6 d' m q d'' d).
Proof. exact (eq_refl (term6 d' m q d'' d)). Qed.
Lemma lem1249361 (d : nat) (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d' m q d'' d) = (term3 m q d' d'' d''')) = ((term2 d' m q d'' d) = ((term4 m d' q) = (term5 m q d' d'' d'''))).
Proof. exact (MK_COMB (@lem1249360 d' m q d'' d) (@lem1249359 m q d' d'' d''')). Qed.
Lemma lem1249362 (d' : nat) (m : nat) (q : nat) (d'' : nat) (d : nat) : (term2 d' m q d'' d) = ((term4 m d' q) = (term7 m q d'' d)).
Proof. exact (eq_refl (term2 d' m q d'' d)). Qed.
Lemma lem1249363 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249364 (d' : nat) (m : nat) (q : nat) (d'' : nat) (d : nat) : (term6 d' m q d'' d) = (term8 d' m q d'' d).
Proof. exact (MK_COMB (@lem1249363) (@lem1249362 d' m q d'' d)). Qed.
Lemma lem1249365 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term4 m d' q) = (term5 m q d' d'' d''')) = ((term4 m d' q) = (term5 m q d' d'' d''')).
Proof. exact (eq_refl ((term4 m d' q) = (term5 m q d' d'' d'''))). Qed.
Lemma lem1249366 (d : nat) (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d' m q d'' d) = ((term4 m d' q) = (term5 m q d' d'' d'''))) = (((term4 m d' q) = (term7 m q d'' d)) = ((term4 m d' q) = (term5 m q d' d'' d'''))).
Proof. exact (MK_COMB (@lem1249364 d' m q d'' d) (@lem1249365 m q d' d'' d''')). Qed.
Lemma lem1249367 (d : nat) (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d' m q d'' d) = (term3 m q d' d'' d''')) = (((term4 m d' q) = (term7 m q d'' d)) = ((term4 m d' q) = (term5 m q d' d'' d'''))).
Proof. exact (TRANS (@lem1249361 d m q d' d'' d''') (@lem1249366 d m q d' d'' d''')). Qed.
Lemma lem1249368 (m : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((term4 m d' q) = (term7 m q d'' d)) = ((term4 m d' q) = (term5 m q d' d'' d''')).
Proof. exact (EQ_MP (@lem1249367 d m q d' d'' d''') (@lem1249358 m q d d' d'' d''' h1)). Qed.
Lemma lem1249369 (d''' : nat) (d'' : nat) (d' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : d = (term0 d' d'' d''')) (h2 : n = (Nat.add q d'')) (h3 : p = (Nat.add m d')) (h4 : (Nat.add p q) = (term4 m n d)) : (term4 m d' q) = (term5 m q d' d'' d''').
Proof. exact (EQ_MP (@lem1249368 m q d d' d'' d''' h1) (@lem1248070 d'' d' p q m n d h2 h3 h4)). Qed.
