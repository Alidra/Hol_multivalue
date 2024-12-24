Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249050_term_abbrevs.
Require Import thm1247430_spec.
Lemma lem1249023 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249038 (p : nat) (d' : nat) (d'' : nat) : (term1 p d' d'') = (term1 p d' d'').
Proof. exact (eq_refl (term1 p d' d'')). Qed.
Lemma lem1249039 (p : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 p d' d'' d) = (term3 p d' d'' d''').
Proof. exact (MK_COMB (@lem1249038 p d' d'') (@lem1249023 d d' d'' d''' h1)). Qed.
Lemma lem1249040 (p : nat) (d''' : nat) (d' : nat) (d'' : nat) : (term3 p d' d'' d''') = (p = (term4 p d''' d' d'')).
Proof. exact (eq_refl (term3 p d' d'' d''')). Qed.
Lemma lem1249041 (p : nat) (d' : nat) (d'' : nat) (d : nat) : (term5 p d' d'' d) = (term5 p d' d'' d).
Proof. exact (eq_refl (term5 p d' d'' d)). Qed.
Lemma lem1249042 (d : nat) (p : nat) (d''' : nat) (d' : nat) (d'' : nat) : ((term2 p d' d'' d) = (term3 p d' d'' d''')) = ((term2 p d' d'' d) = (p = (term4 p d''' d' d''))).
Proof. exact (MK_COMB (@lem1249041 p d' d'' d) (@lem1249040 p d''' d' d'')). Qed.
Lemma lem1249043 (p : nat) (d : nat) (d' : nat) (d'' : nat) : (term2 p d' d'' d) = (p = (term6 p d d' d'')).
Proof. exact (eq_refl (term2 p d' d'' d)). Qed.
Lemma lem1249044 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249045 (p : nat) (d : nat) (d' : nat) (d'' : nat) : (term5 p d' d'' d) = (term7 p d d' d'').
Proof. exact (MK_COMB (@lem1249044) (@lem1249043 p d d' d'')). Qed.
Lemma lem1249046 (p : nat) (d''' : nat) (d' : nat) (d'' : nat) : (p = (term4 p d''' d' d'')) = (p = (term4 p d''' d' d'')).
Proof. exact (eq_refl (p = (term4 p d''' d' d''))). Qed.
Lemma lem1249047 (d : nat) (p : nat) (d''' : nat) (d' : nat) (d'' : nat) : ((term2 p d' d'' d) = (p = (term4 p d''' d' d''))) = ((p = (term6 p d d' d'')) = (p = (term4 p d''' d' d''))).
Proof. exact (MK_COMB (@lem1249045 p d d' d'') (@lem1249046 p d''' d' d'')). Qed.
Lemma lem1249048 (d : nat) (p : nat) (d''' : nat) (d' : nat) (d'' : nat) : ((term2 p d' d'' d) = (term3 p d' d'' d''')) = ((p = (term6 p d d' d'')) = (p = (term4 p d''' d' d''))).
Proof. exact (TRANS (@lem1249042 d p d''' d' d'') (@lem1249047 d p d''' d' d'')). Qed.
Lemma lem1249049 (p : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (p = (term6 p d d' d'')) = (p = (term4 p d''' d' d'')).
Proof. exact (EQ_MP (@lem1249048 d p d''' d' d'') (@lem1249039 p d d' d'' d''' h1)). Qed.
Lemma lem1249050 (d''' : nat) (p : nat) (d : nat) (d' : nat) (d'' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : p = (term6 p d d' d'')) : p = (term4 p d''' d' d'').
Proof. exact (EQ_MP (@lem1249049 p d d' d'' d''' h1) (@lem1247430 p d d' d'' h2)). Qed.
