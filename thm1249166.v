Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249166_term_abbrevs.
Require Import thm1247578_spec.
Lemma lem1249139 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249154 (m : nat) (d' : nat) (d'' : nat) : (term1 m d' d'') = (term1 m d' d'').
Proof. exact (eq_refl (term1 m d' d'')). Qed.
Lemma lem1249155 (m : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 m d' d'' d) = (term3 m d' d'' d''').
Proof. exact (MK_COMB (@lem1249154 m d' d'') (@lem1249139 d d' d'' d''' h1)). Qed.
Lemma lem1249156 (d''' : nat) (m : nat) (d' : nat) (d'' : nat) : (term3 m d' d'' d''') = ((term4 m d' d'' d''') = (term5 m d' d'')).
Proof. exact (eq_refl (term3 m d' d'' d''')). Qed.
Lemma lem1249157 (m : nat) (d' : nat) (d'' : nat) (d : nat) : (term6 m d' d'' d) = (term6 m d' d'' d).
Proof. exact (eq_refl (term6 m d' d'' d)). Qed.
Lemma lem1249158 (d : nat) (d''' : nat) (m : nat) (d' : nat) (d'' : nat) : ((term2 m d' d'' d) = (term3 m d' d'' d''')) = ((term2 m d' d'' d) = ((term4 m d' d'' d''') = (term5 m d' d''))).
Proof. exact (MK_COMB (@lem1249157 m d' d'' d) (@lem1249156 d''' m d' d'')). Qed.
Lemma lem1249159 (d : nat) (m : nat) (d' : nat) (d'' : nat) : (term2 m d' d'' d) = ((Nat.add m d) = (term5 m d' d'')).
Proof. exact (eq_refl (term2 m d' d'' d)). Qed.
Lemma lem1249160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249161 (d : nat) (m : nat) (d' : nat) (d'' : nat) : (term6 m d' d'' d) = (term7 d m d' d'').
Proof. exact (MK_COMB (@lem1249160) (@lem1249159 d m d' d'')). Qed.
Lemma lem1249162 (d''' : nat) (m : nat) (d' : nat) (d'' : nat) : ((term4 m d' d'' d''') = (term5 m d' d'')) = ((term4 m d' d'' d''') = (term5 m d' d'')).
Proof. exact (eq_refl ((term4 m d' d'' d''') = (term5 m d' d''))). Qed.
Lemma lem1249163 (d : nat) (d''' : nat) (m : nat) (d' : nat) (d'' : nat) : ((term2 m d' d'' d) = ((term4 m d' d'' d''') = (term5 m d' d''))) = (((Nat.add m d) = (term5 m d' d'')) = ((term4 m d' d'' d''') = (term5 m d' d''))).
Proof. exact (MK_COMB (@lem1249161 d m d' d'') (@lem1249162 d''' m d' d'')). Qed.
Lemma lem1249164 (d : nat) (d''' : nat) (m : nat) (d' : nat) (d'' : nat) : ((term2 m d' d'' d) = (term3 m d' d'' d''')) = (((Nat.add m d) = (term5 m d' d'')) = ((term4 m d' d'' d''') = (term5 m d' d''))).
Proof. exact (TRANS (@lem1249158 d d''' m d' d'') (@lem1249163 d d''' m d' d'')). Qed.
Lemma lem1249165 (m : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((Nat.add m d) = (term5 m d' d'')) = ((term4 m d' d'' d''') = (term5 m d' d'')).
Proof. exact (EQ_MP (@lem1249164 d d''' m d' d'') (@lem1249155 m d d' d'' d''' h1)). Qed.
Lemma lem1249166 (d''' : nat) (d : nat) (m : nat) (d' : nat) (d'' : nat) (h1 : d = (term0 d' d'' d''')) (h2 : (Nat.add m d) = (term5 m d' d'')) : (term4 m d' d'' d''') = (term5 m d' d'').
Proof. exact (EQ_MP (@lem1249165 m d d' d'' d''' h1) (@lem1247578 d m d' d'' h2)). Qed.
