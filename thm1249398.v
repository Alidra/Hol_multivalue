Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249398_term_abbrevs.
Require Import thm1248098_spec.
Lemma lem1249371 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249386 (d' : nat) (d'' : nat) (m : nat) (n : nat) : (term1 d' d'' m n) = (term1 d' d'' m n).
Proof. exact (eq_refl (term1 d' d'' m n)). Qed.
Lemma lem1249387 (m : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 d' d'' m n d) = (term3 m n d' d'' d''').
Proof. exact (MK_COMB (@lem1249386 d' d'' m n) (@lem1249371 d d' d'' d''' h1)). Qed.
Lemma lem1249388 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 m n d' d'' d''') = ((term4 m d' n d'') = (term5 m n d' d'' d''')).
Proof. exact (eq_refl (term3 m n d' d'' d''')). Qed.
Lemma lem1249389 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d : nat) : (term6 d' d'' m n d) = (term6 d' d'' m n d).
Proof. exact (eq_refl (term6 d' d'' m n d)). Qed.
Lemma lem1249390 (d : nat) (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d' d'' m n d) = (term3 m n d' d'' d''')) = ((term2 d' d'' m n d) = ((term4 m d' n d'') = (term5 m n d' d'' d'''))).
Proof. exact (MK_COMB (@lem1249389 d' d'' m n d) (@lem1249388 m n d' d'' d''')). Qed.
Lemma lem1249391 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d : nat) : (term2 d' d'' m n d) = ((term4 m d' n d'') = (term7 m n d)).
Proof. exact (eq_refl (term2 d' d'' m n d)). Qed.
Lemma lem1249392 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249393 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d : nat) : (term6 d' d'' m n d) = (term8 d' d'' m n d).
Proof. exact (MK_COMB (@lem1249392) (@lem1249391 d' d'' m n d)). Qed.
Lemma lem1249394 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term4 m d' n d'') = (term5 m n d' d'' d''')) = ((term4 m d' n d'') = (term5 m n d' d'' d''')).
Proof. exact (eq_refl ((term4 m d' n d'') = (term5 m n d' d'' d'''))). Qed.
Lemma lem1249395 (d : nat) (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d' d'' m n d) = ((term4 m d' n d'') = (term5 m n d' d'' d'''))) = (((term4 m d' n d'') = (term7 m n d)) = ((term4 m d' n d'') = (term5 m n d' d'' d'''))).
Proof. exact (MK_COMB (@lem1249393 d' d'' m n d) (@lem1249394 m n d' d'' d''')). Qed.
Lemma lem1249396 (d : nat) (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d' d'' m n d) = (term3 m n d' d'' d''')) = (((term4 m d' n d'') = (term7 m n d)) = ((term4 m d' n d'') = (term5 m n d' d'' d'''))).
Proof. exact (TRANS (@lem1249390 d m n d' d'' d''') (@lem1249395 d m n d' d'' d''')). Qed.
Lemma lem1249397 (m : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((term4 m d' n d'') = (term7 m n d)) = ((term4 m d' n d'') = (term5 m n d' d'' d''')).
Proof. exact (EQ_MP (@lem1249396 d m n d' d'' d''') (@lem1249387 m n d d' d'' d''' h1)). Qed.
Lemma lem1249398 (d''' : nat) (d' : nat) (d'' : nat) (p : nat) (q : nat) (m : nat) (n : nat) (d : nat) (h1 : d = (term0 d' d'' d''')) (h2 : p = (Nat.add m d')) (h3 : q = (Nat.add n d'')) (h4 : (Nat.add p q) = (term7 m n d)) : (term4 m d' n d'') = (term5 m n d' d'' d''').
Proof. exact (EQ_MP (@lem1249397 m n d d' d'' d''' h1) (@lem1248098 d' d'' p q m n d h2 h3 h4)). Qed.
