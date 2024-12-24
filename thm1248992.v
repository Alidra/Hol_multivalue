Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1248992_term_abbrevs.
Require Import thm1247394_spec.
Lemma lem1248965 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1248980 (d'' : nat) (n : nat) (d' : nat) : (term1 d'' n d') = (term1 d'' n d').
Proof. exact (eq_refl (term1 d'' n d')). Qed.
Lemma lem1248981 (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 d'' n d' d) = (term3 n d' d'' d''').
Proof. exact (MK_COMB (@lem1248980 d'' n d') (@lem1248965 d d' d'' d''' h1)). Qed.
Lemma lem1248982 (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : (term3 n d' d'' d''') = ((term4 n d' d'' d''') = (Nat.add n d')).
Proof. exact (eq_refl (term3 n d' d'' d''')). Qed.
Lemma lem1248983 (d'' : nat) (n : nat) (d' : nat) (d : nat) : (term5 d'' n d' d) = (term5 d'' n d' d).
Proof. exact (eq_refl (term5 d'' n d' d)). Qed.
Lemma lem1248984 (d : nat) (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : ((term2 d'' n d' d) = (term3 n d' d'' d''')) = ((term2 d'' n d' d) = ((term4 n d' d'' d''') = (Nat.add n d'))).
Proof. exact (MK_COMB (@lem1248983 d'' n d' d) (@lem1248982 d'' d''' n d')). Qed.
Lemma lem1248985 (d'' : nat) (d : nat) (n : nat) (d' : nat) : (term2 d'' n d' d) = ((term6 n d'' d) = (Nat.add n d')).
Proof. exact (eq_refl (term2 d'' n d' d)). Qed.
Lemma lem1248986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1248987 (d'' : nat) (d : nat) (n : nat) (d' : nat) : (term5 d'' n d' d) = (term7 d'' d n d').
Proof. exact (MK_COMB (@lem1248986) (@lem1248985 d'' d n d')). Qed.
Lemma lem1248988 (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : ((term4 n d' d'' d''') = (Nat.add n d')) = ((term4 n d' d'' d''') = (Nat.add n d')).
Proof. exact (eq_refl ((term4 n d' d'' d''') = (Nat.add n d'))). Qed.
Lemma lem1248989 (d : nat) (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : ((term2 d'' n d' d) = ((term4 n d' d'' d''') = (Nat.add n d'))) = (((term6 n d'' d) = (Nat.add n d')) = ((term4 n d' d'' d''') = (Nat.add n d'))).
Proof. exact (MK_COMB (@lem1248987 d'' d n d') (@lem1248988 d'' d''' n d')). Qed.
Lemma lem1248990 (d : nat) (d'' : nat) (d''' : nat) (n : nat) (d' : nat) : ((term2 d'' n d' d) = (term3 n d' d'' d''')) = (((term6 n d'' d) = (Nat.add n d')) = ((term4 n d' d'' d''') = (Nat.add n d'))).
Proof. exact (TRANS (@lem1248984 d d'' d''' n d') (@lem1248989 d d'' d''' n d')). Qed.
Lemma lem1248991 (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((term6 n d'' d) = (Nat.add n d')) = ((term4 n d' d'' d''') = (Nat.add n d')).
Proof. exact (EQ_MP (@lem1248990 d d'' d''' n d') (@lem1248981 n d d' d'' d''' h1)). Qed.
Lemma lem1248992 (d''' : nat) (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : p = (Nat.add n d'')) (h3 : (Nat.add p d) = (Nat.add n d')) : (term4 n d' d'' d''') = (Nat.add n d').
Proof. exact (EQ_MP (@lem1248991 n d d' d'' d''' h1) (@lem1247394 d'' p d n d' h2 h3)). Qed.
