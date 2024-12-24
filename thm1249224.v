Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249224_term_abbrevs.
Require Import thm1247794_spec.
Lemma lem1249197 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249212 (d' : nat) (p : nat) (n : nat) (d'' : nat) : (term1 d' p n d'') = (term1 d' p n d'').
Proof. exact (eq_refl (term1 d' p n d'')). Qed.
Lemma lem1249213 (p : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 d' p n d'' d) = (term3 p n d' d'' d''').
Proof. exact (MK_COMB (@lem1249212 d' p n d'') (@lem1249197 d d' d'' d''' h1)). Qed.
Lemma lem1249214 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 p n d' d'' d''') = ((term4 p d' n) = (term5 p n d' d'' d''')).
Proof. exact (eq_refl (term3 p n d' d'' d''')). Qed.
Lemma lem1249215 (d' : nat) (p : nat) (n : nat) (d'' : nat) (d : nat) : (term6 d' p n d'' d) = (term6 d' p n d'' d).
Proof. exact (eq_refl (term6 d' p n d'' d)). Qed.
Lemma lem1249216 (d : nat) (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d' p n d'' d) = (term3 p n d' d'' d''')) = ((term2 d' p n d'' d) = ((term4 p d' n) = (term5 p n d' d'' d'''))).
Proof. exact (MK_COMB (@lem1249215 d' p n d'' d) (@lem1249214 p n d' d'' d''')). Qed.
Lemma lem1249217 (d' : nat) (p : nat) (n : nat) (d'' : nat) (d : nat) : (term2 d' p n d'' d) = ((term4 p d' n) = (term7 p n d'' d)).
Proof. exact (eq_refl (term2 d' p n d'' d)). Qed.
Lemma lem1249218 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249219 (d' : nat) (p : nat) (n : nat) (d'' : nat) (d : nat) : (term6 d' p n d'' d) = (term8 d' p n d'' d).
Proof. exact (MK_COMB (@lem1249218) (@lem1249217 d' p n d'' d)). Qed.
Lemma lem1249220 (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term4 p d' n) = (term5 p n d' d'' d''')) = ((term4 p d' n) = (term5 p n d' d'' d''')).
Proof. exact (eq_refl ((term4 p d' n) = (term5 p n d' d'' d'''))). Qed.
Lemma lem1249221 (d : nat) (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d' p n d'' d) = ((term4 p d' n) = (term5 p n d' d'' d'''))) = (((term4 p d' n) = (term7 p n d'' d)) = ((term4 p d' n) = (term5 p n d' d'' d'''))).
Proof. exact (MK_COMB (@lem1249219 d' p n d'' d) (@lem1249220 p n d' d'' d''')). Qed.
Lemma lem1249222 (d : nat) (p : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 d' p n d'' d) = (term3 p n d' d'' d''')) = (((term4 p d' n) = (term7 p n d'' d)) = ((term4 p d' n) = (term5 p n d' d'' d'''))).
Proof. exact (TRANS (@lem1249216 d p n d' d'' d''') (@lem1249221 d p n d' d'' d''')). Qed.
Lemma lem1249223 (p : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((term4 p d' n) = (term7 p n d'' d)) = ((term4 p d' n) = (term5 p n d' d'' d''')).
Proof. exact (EQ_MP (@lem1249222 d p n d' d'' d''') (@lem1249213 p n d d' d'' d''' h1)). Qed.
Lemma lem1249224 (d''' : nat) (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : d = (term0 d' d'' d''')) (h2 : m = (Nat.add p d')) (h3 : q = (Nat.add n d'')) (h4 : (Nat.add m n) = (term4 p q d)) : (term4 p d' n) = (term5 p n d' d'' d''').
Proof. exact (EQ_MP (@lem1249223 p n d d' d'' d''' h1) (@lem1247794 d' d'' m n p q d h2 h3 h4)). Qed.
