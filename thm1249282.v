Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249282_term_abbrevs.
Require Import thm1247870_spec.
Lemma lem1249255 (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : d = (term0 d' d'' d''').
Proof. exact (h1). Qed.
Lemma lem1249270 (m : nat) (d' : nat) (n : nat) (d'' : nat) : (term1 m d' n d'') = (term1 m d' n d'').
Proof. exact (eq_refl (term1 m d' n d'')). Qed.
Lemma lem1249271 (m : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : (term2 m d' n d'' d) = (term3 m n d' d'' d''').
Proof. exact (MK_COMB (@lem1249270 m d' n d'') (@lem1249255 d d' d'' d''' h1)). Qed.
Lemma lem1249272 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 m n d' d'' d''') = ((Nat.add m n) = (term4 m n d' d'' d''')).
Proof. exact (eq_refl (term3 m n d' d'' d''')). Qed.
Lemma lem1249273 (m : nat) (d' : nat) (n : nat) (d'' : nat) (d : nat) : (term5 m d' n d'' d) = (term5 m d' n d'' d).
Proof. exact (eq_refl (term5 m d' n d'' d)). Qed.
Lemma lem1249274 (d : nat) (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 m d' n d'' d) = (term3 m n d' d'' d''')) = ((term2 m d' n d'' d) = ((Nat.add m n) = (term4 m n d' d'' d'''))).
Proof. exact (MK_COMB (@lem1249273 m d' n d'' d) (@lem1249272 m n d' d'' d''')). Qed.
Lemma lem1249275 (m : nat) (d' : nat) (n : nat) (d'' : nat) (d : nat) : (term2 m d' n d'' d) = ((Nat.add m n) = (term6 m d' n d'' d)).
Proof. exact (eq_refl (term2 m d' n d'' d)). Qed.
Lemma lem1249276 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1249277 (m : nat) (d' : nat) (n : nat) (d'' : nat) (d : nat) : (term5 m d' n d'' d) = (term7 m d' n d'' d).
Proof. exact (MK_COMB (@lem1249276) (@lem1249275 m d' n d'' d)). Qed.
Lemma lem1249278 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((Nat.add m n) = (term4 m n d' d'' d''')) = ((Nat.add m n) = (term4 m n d' d'' d''')).
Proof. exact (eq_refl ((Nat.add m n) = (term4 m n d' d'' d'''))). Qed.
Lemma lem1249279 (d : nat) (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 m d' n d'' d) = ((Nat.add m n) = (term4 m n d' d'' d'''))) = (((Nat.add m n) = (term6 m d' n d'' d)) = ((Nat.add m n) = (term4 m n d' d'' d'''))).
Proof. exact (MK_COMB (@lem1249277 m d' n d'' d) (@lem1249278 m n d' d'' d''')). Qed.
Lemma lem1249280 (d : nat) (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 m d' n d'' d) = (term3 m n d' d'' d''')) = (((Nat.add m n) = (term6 m d' n d'' d)) = ((Nat.add m n) = (term4 m n d' d'' d'''))).
Proof. exact (TRANS (@lem1249274 d m n d' d'' d''') (@lem1249279 d m n d' d'' d''')). Qed.
Lemma lem1249281 (m : nat) (n : nat) (d : nat) (d' : nat) (d'' : nat) (d''' : nat) (h1 : d = (term0 d' d'' d''')) : ((Nat.add m n) = (term6 m d' n d'' d)) = ((Nat.add m n) = (term4 m n d' d'' d''')).
Proof. exact (EQ_MP (@lem1249280 d m n d' d'' d''') (@lem1249271 m n d d' d'' d''' h1)). Qed.
Lemma lem1249282 (d''' : nat) (d' : nat) (d'' : nat) (m : nat) (n : nat) (p : nat) (q : nat) (d : nat) (h1 : d = (term0 d' d'' d''')) (h2 : p = (Nat.add m d')) (h3 : q = (Nat.add n d'')) (h4 : (Nat.add m n) = (term8 p q d)) : (Nat.add m n) = (term4 m n d' d'' d''').
Proof. exact (EQ_MP (@lem1249281 m n d d' d'' d''' h1) (@lem1247870 d' d'' m n p q d h2 h3 h4)). Qed.
