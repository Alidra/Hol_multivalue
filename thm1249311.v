Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249311_term_abbrevs.
Require Import thm1247994_spec.
Lemma lem1249284 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249299 (p : nat) (d' : nat) (q : nat) (d'' : nat) : (term1 p d' q d'') = (term1 p d' q d'').
Proof. exact (eq_refl (term1 p d' q d'')). Qed.
Lemma lem1249300 (p : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 p d' q d'' d) = (term3 p q d' d'' d''').
Proof. exact (MK_COMB (@lem1249299 p d' q d'') (@lem1249284 d d' d'' d''' h1)). Qed.
Lemma lem1249301 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 p q d' d'' d''') = ((Nat.add p q) = (term4 p q d' d'' d''')).
Proof. exact (eq_refl (term3 p q d' d'' d''')). Qed.
Lemma lem1249302 (p : nat) (d' : nat) (q : nat) (d'' : nat) (d : nat) : (term5 p d' q d'' d) = (term5 p d' q d'' d).
Proof. exact (eq_refl (term5 p d' q d'' d)). Qed.
Lemma lem1249303 (d : nat) (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 p d' q d'' d) = (term3 p q d' d'' d''')) = ((term2 p d' q d'' d) = ((Nat.add p q) = (term4 p q d' d'' d'''))).
Proof. exact (MK_COMB (@lem1249302 p d' q d'' d) (@lem1249301 p q d' d'' d''')). Qed.
Lemma lem1249304 (p : nat) (d' : nat) (q : nat) (d'' : nat) (d : nat) : (term2 p d' q d'' d) = ((Nat.add p q) = (term6 p d' q d'' d)).
Proof. exact (eq_refl (term2 p d' q d'' d)). Qed.
Lemma lem1249305 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249306 (p : nat) (d' : nat) (q : nat) (d'' : nat) (d : nat) : (term5 p d' q d'' d) = (term7 p d' q d'' d).
Proof. exact (MK_COMB (@lem1249305) (@lem1249304 p d' q d'' d)). Qed.
Lemma lem1249307 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((Nat.add p q) = (term4 p q d' d'' d''')) = ((Nat.add p q) = (term4 p q d' d'' d''')).
Proof. exact (eq_refl ((Nat.add p q) = (term4 p q d' d'' d'''))). Qed.
Lemma lem1249308 (d : nat) (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 p d' q d'' d) = ((Nat.add p q) = (term4 p q d' d'' d'''))) = (((Nat.add p q) = (term6 p d' q d'' d)) = ((Nat.add p q) = (term4 p q d' d'' d'''))).
Proof. exact (MK_COMB (@lem1249306 p d' q d'' d) (@lem1249307 p q d' d'' d''')). Qed.
Lemma lem1249309 (d : nat) (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 p d' q d'' d) = (term3 p q d' d'' d''')) = (((Nat.add p q) = (term6 p d' q d'' d)) = ((Nat.add p q) = (term4 p q d' d'' d'''))).
Proof. exact (TRANS (@lem1249303 d p q d' d'' d''') (@lem1249308 d p q d' d'' d''')). Qed.
Lemma lem1249310 (p : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((Nat.add p q) = (term6 p d' q d'' d)) = ((Nat.add p q) = (term4 p q d' d'' d''')).
Proof. exact (EQ_MP (@lem1249309 d p q d' d'' d''') (@lem1249300 p q d d' d'' d''' h1)). Qed.
Lemma lem1249311 (d''' : nat) (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : d = (term0 d' d'' d''')) (h2 : m = (Nat.add p d')) (h3 : n = (Nat.add q d'')) (h4 : (Nat.add p q) = (term8 m n d)) : (Nat.add p q) = (term4 p q d' d'' d''').
Proof. exact (EQ_MP (@lem1249310 p q d d' d'' d''' h1) (@lem1247994 d' d'' p q m n d h2 h3 h4)). Qed.
