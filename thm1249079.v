Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249079_term_abbrevs.
Require Import thm1247513_spec.
Lemma lem1249052 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249067 (n : nat) (d' : nat) (d'' : nat) : (term1 n d' d'') = (term1 n d' d'').
Proof. exact (eq_refl (term1 n d' d'')). Qed.
Lemma lem1249068 (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 n d' d'' d) = (term3 n d' d'' d''').
Proof. exact (MK_COMB (@lem1249067 n d' d'') (@lem1249052 d d' d'' d''' h1)). Qed.
Lemma lem1249069 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term3 n d' d'' d''') = (n = (term4 n d' d''' d'')).
Proof. exact (eq_refl (term3 n d' d'' d''')). Qed.
Lemma lem1249070 (n : nat) (d' : nat) (d'' : nat) (d : nat) : (term5 n d' d'' d) = (term5 n d' d'' d).
Proof. exact (eq_refl (term5 n d' d'' d)). Qed.
Lemma lem1249071 (d : nat) (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term2 n d' d'' d) = (term3 n d' d'' d''')) = ((term2 n d' d'' d) = (n = (term4 n d' d''' d''))).
Proof. exact (MK_COMB (@lem1249070 n d' d'' d) (@lem1249069 n d' d''' d'')). Qed.
Lemma lem1249072 (n : nat) (d' : nat) (d : nat) (d'' : nat) : (term2 n d' d'' d) = (n = (term6 n d' d d'')).
Proof. exact (eq_refl (term2 n d' d'' d)). Qed.
Lemma lem1249073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249074 (n : nat) (d' : nat) (d : nat) (d'' : nat) : (term5 n d' d'' d) = (term7 n d' d d'').
Proof. exact (MK_COMB (@lem1249073) (@lem1249072 n d' d d'')). Qed.
Lemma lem1249075 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (n = (term4 n d' d''' d'')) = (n = (term4 n d' d''' d'')).
Proof. exact (eq_refl (n = (term4 n d' d''' d''))). Qed.
Lemma lem1249076 (d : nat) (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term2 n d' d'' d) = (n = (term4 n d' d''' d''))) = ((n = (term6 n d' d d'')) = (n = (term4 n d' d''' d''))).
Proof. exact (MK_COMB (@lem1249074 n d' d d'') (@lem1249075 n d' d''' d'')). Qed.
Lemma lem1249077 (d : nat) (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : ((term2 n d' d'' d) = (term3 n d' d'' d''')) = ((n = (term6 n d' d d'')) = (n = (term4 n d' d''' d''))).
Proof. exact (TRANS (@lem1249071 d n d' d''' d'') (@lem1249076 d n d' d''' d'')). Qed.
Lemma lem1249078 (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (n = (term6 n d' d d'')) = (n = (term4 n d' d''' d'')).
Proof. exact (EQ_MP (@lem1249077 d n d' d''' d'') (@lem1249068 n d d' d'' d''' h1)). Qed.
Lemma lem1249079 (d''' : nat) (n : nat) (d' : nat) (d : nat) (d'' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : n = (term6 n d' d d'')) : n = (term4 n d' d''' d'').
Proof. exact (EQ_MP (@lem1249078 n d d' d'' d''' h1) (@lem1247513 n d' d d'' h2)). Qed.
