Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249630_term_abbrevs.
Require Import thm1248550_spec.
Lemma lem1249603 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249618 (d'' : nat) (m : nat) (n : nat) (d' : nat) : (term1 d'' m n d') = (term1 d'' m n d').
Proof. exact (eq_refl (term1 d'' m n d')). Qed.
Lemma lem1249619 (m : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 d'' m n d' d) = (term3 m n d' d'' d''').
Proof. exact (MK_COMB (@lem1249618 d'' m n d') (@lem1249603 d d' d'' d''' h1)). Qed.
Lemma lem1249620 (d''' : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat) : (term3 m n d' d'' d''') = ((term4 m d' d''' n d'') = (term5 m n d')).
Proof. exact (eq_refl (term3 m n d' d'' d''')). Qed.
Lemma lem1249621 (d'' : nat) (m : nat) (n : nat) (d' : nat) (d : nat) : (term6 d'' m n d' d) = (term6 d'' m n d' d).
Proof. exact (eq_refl (term6 d'' m n d' d)). Qed.
Lemma lem1249622 (d : nat) (d''' : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat) : ((term2 d'' m n d' d) = (term3 m n d' d'' d''')) = ((term2 d'' m n d' d) = ((term4 m d' d''' n d'') = (term5 m n d'))).
Proof. exact (MK_COMB (@lem1249621 d'' m n d' d) (@lem1249620 d''' d'' m n d')). Qed.
Lemma lem1249623 (d : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat) : (term2 d'' m n d' d) = ((term7 m d n d'') = (term5 m n d')).
Proof. exact (eq_refl (term2 d'' m n d' d)). Qed.
Lemma lem1249624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249625 (d : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat) : (term6 d'' m n d' d) = (term8 d d'' m n d').
Proof. exact (MK_COMB (@lem1249624) (@lem1249623 d d'' m n d')). Qed.
Lemma lem1249626 (d''' : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat) : ((term4 m d' d''' n d'') = (term5 m n d')) = ((term4 m d' d''' n d'') = (term5 m n d')).
Proof. exact (eq_refl ((term4 m d' d''' n d'') = (term5 m n d'))). Qed.
Lemma lem1249627 (d : nat) (d''' : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat) : ((term2 d'' m n d' d) = ((term4 m d' d''' n d'') = (term5 m n d'))) = (((term7 m d n d'') = (term5 m n d')) = ((term4 m d' d''' n d'') = (term5 m n d'))).
Proof. exact (MK_COMB (@lem1249625 d d'' m n d') (@lem1249626 d''' d'' m n d')). Qed.
Lemma lem1249628 (d : nat) (d''' : nat) (d'' : nat) (m : nat) (n : nat) (d' : nat) : ((term2 d'' m n d' d) = (term3 m n d' d'' d''')) = (((term7 m d n d'') = (term5 m n d')) = ((term4 m d' d''' n d'') = (term5 m n d'))).
Proof. exact (TRANS (@lem1249622 d d''' d'' m n d') (@lem1249627 d d''' d'' m n d')). Qed.
Lemma lem1249629 (m : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((term7 m d n d'') = (term5 m n d')) = ((term4 m d' d''' n d'') = (term5 m n d')).
Proof. exact (EQ_MP (@lem1249628 d d''' d'' m n d') (@lem1249619 m n d d' d'' d''' h1)). Qed.
Lemma lem1249630 (d''' : nat) (d'' : nat) (d : nat) (q : nat) (m : nat) (n : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : q = (Nat.add n d'')) (h3 : (term5 m d q) = (term5 m n d')) : (term4 m d' d''' n d'') = (term5 m n d').
Proof. exact (EQ_MP (@lem1249629 m n d d' d'' d''' h1) (@lem1248550 d'' d q m n d' h2 h3)). Qed.
