Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249253_term_abbrevs.
Require Import thm1247842_spec.
Lemma lem1249226 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249241 (d'' : nat) (m : nat) (d' : nat) (q : nat) : (term1 d'' m d' q) = (term1 d'' m d' q).
Proof. exact (eq_refl (term1 d'' m d' q)). Qed.
Lemma lem1249242 (m : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 d'' m d' q d) = (term3 m q d' d'' d''').
Proof. exact (MK_COMB (@lem1249241 d'' m d' q) (@lem1249226 d d' d'' d''' h1)). Qed.
Lemma lem1249243 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 m q d' d'' d''') = ((term4 m q d'') = (term5 m q d' d'' d''')).
Proof. exact (eq_refl (term3 m q d' d'' d''')). Qed.
Lemma lem1249244 (d'' : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : (term6 d'' m d' q d) = (term6 d'' m d' q d).
Proof. exact (eq_refl (term6 d'' m d' q d)). Qed.
Lemma lem1249245 (d : nat) (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d'' m d' q d) = (term3 m q d' d'' d''')) = ((term2 d'' m d' q d) = ((term4 m q d'') = (term5 m q d' d'' d'''))).
Proof. exact (MK_COMB (@lem1249244 d'' m d' q d) (@lem1249243 m q d' d'' d''')). Qed.
Lemma lem1249246 (d'' : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : (term2 d'' m d' q d) = ((term4 m q d'') = (term7 m d' q d)).
Proof. exact (eq_refl (term2 d'' m d' q d)). Qed.
Lemma lem1249247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249248 (d'' : nat) (m : nat) (d' : nat) (q : nat) (d : nat) : (term6 d'' m d' q d) = (term8 d'' m d' q d).
Proof. exact (MK_COMB (@lem1249247) (@lem1249246 d'' m d' q d)). Qed.
Lemma lem1249249 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term4 m q d'') = (term5 m q d' d'' d''')) = ((term4 m q d'') = (term5 m q d' d'' d''')).
Proof. exact (eq_refl ((term4 m q d'') = (term5 m q d' d'' d'''))). Qed.
Lemma lem1249250 (d : nat) (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d'' m d' q d) = ((term4 m q d'') = (term5 m q d' d'' d'''))) = (((term4 m q d'') = (term7 m d' q d)) = ((term4 m q d'') = (term5 m q d' d'' d'''))).
Proof. exact (MK_COMB (@lem1249248 d'' m d' q d) (@lem1249249 m q d' d'' d''')). Qed.
Lemma lem1249251 (d : nat) (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d'' m d' q d) = (term3 m q d' d'' d''')) = (((term4 m q d'') = (term7 m d' q d)) = ((term4 m q d'') = (term5 m q d' d'' d'''))).
Proof. exact (TRANS (@lem1249245 d m q d' d'' d''') (@lem1249250 d m q d' d'' d''')). Qed.
Lemma lem1249252 (m : nat) (q : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((term4 m q d'') = (term7 m d' q d)) = ((term4 m q d'') = (term5 m q d' d'' d''')).
Proof. exact (EQ_MP (@lem1249251 d m q d' d'' d''') (@lem1249242 m q d d' d'' d''' h1)). Qed.
Lemma lem1249253 (d''' : nat) (d'' : nat) (d' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : d = (term0 d' d'' d''')) (h2 : n = (Nat.add q d'')) (h3 : p = (Nat.add m d')) (h4 : (Nat.add m n) = (term9 p q d)) : (term4 m q d'') = (term5 m q d' d'' d''').
Proof. exact (EQ_MP (@lem1249252 m q d d' d'' d''' h1) (@lem1247842 d'' d' m n p q d h2 h3 h4)). Qed.
