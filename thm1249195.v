Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249195_term_abbrevs.
Require Import thm1247766_spec.
Lemma lem1249168 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249183 (d' : nat) (d'' : nat) (p : nat) (q : nat) : (term1 d' d'' p q) = (term1 d' d'' p q).
Proof. exact (eq_refl (term1 d' d'' p q)). Qed.
Lemma lem1249184 (p : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 d' d'' p q d) = (term3 p q d' d'' d''').
Proof. exact (MK_COMB (@lem1249183 d' d'' p q) (@lem1249168 d d' d'' d''' h1)). Qed.
Lemma lem1249185 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 p q d' d'' d''') = ((term4 p d' q d'') = (term5 p q d' d'' d''')).
Proof. exact (eq_refl (term3 p q d' d'' d''')). Qed.
Lemma lem1249186 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d : nat) : (term6 d' d'' p q d) = (term6 d' d'' p q d).
Proof. exact (eq_refl (term6 d' d'' p q d)). Qed.
Lemma lem1249187 (d : nat) (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d' d'' p q d) = (term3 p q d' d'' d''')) = ((term2 d' d'' p q d) = ((term4 p d' q d'') = (term5 p q d' d'' d'''))).
Proof. exact (MK_COMB (@lem1249186 d' d'' p q d) (@lem1249185 p q d' d'' d''')). Qed.
Lemma lem1249188 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d : nat) : (term2 d' d'' p q d) = ((term4 p d' q d'') = (term7 p q d)).
Proof. exact (eq_refl (term2 d' d'' p q d)). Qed.
Lemma lem1249189 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249190 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d : nat) : (term6 d' d'' p q d) = (term8 d' d'' p q d).
Proof. exact (MK_COMB (@lem1249189) (@lem1249188 d' d'' p q d)). Qed.
Lemma lem1249191 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term4 p d' q d'') = (term5 p q d' d'' d''')) = ((term4 p d' q d'') = (term5 p q d' d'' d''')).
Proof. exact (eq_refl ((term4 p d' q d'') = (term5 p q d' d'' d'''))). Qed.
Lemma lem1249192 (d : nat) (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d' d'' p q d) = ((term4 p d' q d'') = (term5 p q d' d'' d'''))) = (((term4 p d' q d'') = (term7 p q d)) = ((term4 p d' q d'') = (term5 p q d' d'' d'''))).
Proof. exact (MK_COMB (@lem1249190 d' d'' p q d) (@lem1249191 p q d' d'' d''')). Qed.
Lemma lem1249193 (d : nat) (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d' d'' p q d) = (term3 p q d' d'' d''')) = (((term4 p d' q d'') = (term7 p q d)) = ((term4 p d' q d'') = (term5 p q d' d'' d'''))).
Proof. exact (TRANS (@lem1249187 d p q d' d'' d''') (@lem1249192 d p q d' d'' d''')). Qed.
Lemma lem1249194 (p : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((term4 p d' q d'') = (term7 p q d)) = ((term4 p d' q d'') = (term5 p q d' d'' d''')).
Proof. exact (EQ_MP (@lem1249193 d p q d' d'' d''') (@lem1249184 p q d d' d'' d''' h1)). Qed.
Lemma lem1249195 (d''' : nat) (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : d = (term0 d' d'' d''')) (h2 : m = (Nat.add p d')) (h3 : n = (Nat.add q d'')) (h4 : (Nat.add m n) = (term7 p q d)) : (term4 p d' q d'') = (term5 p q d' d'' d''').
Proof. exact (EQ_MP (@lem1249194 p q d d' d'' d''' h1) (@lem1247766 d' d'' m n p q d h2 h3 h4)). Qed.
