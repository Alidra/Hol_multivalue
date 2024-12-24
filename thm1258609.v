Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1258609_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246867_spec.
Require Import thm1246868_spec.
Require Import thm1823_spec.
Lemma lem1258569 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1258570 (d'' : nat) (d' : nat) (d''' : nat) : (term0 d'' d' d''') = (term1 d'' d' d''').
Proof. exact (@lem1258569 ((term2 d'' d' d''') = (NUMERAL 0))). Qed.
Lemma lem1258574 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258575 (d' : nat) (d''' : nat) : (term3 d' d''') = (term4 d' d''').
Proof. exact (@lem1258574 d' d'''). Qed.
Lemma lem1258576 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1258577 (d' : nat) (d''' : nat) : (term5 d' d''') = (term6 d' d''').
Proof. exact (MK_COMB (@lem1258576 d') (@lem1258575 d' d''')). Qed.
Lemma lem1258579 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258580 (d' : nat) (d''' : nat) : (term6 d' d''') = (term7 d' d''').
Proof. exact (@lem1258579 d' (Nat.add d' d''')). Qed.
Lemma lem1258581 (d' : nat) (d''' : nat) : (term5 d' d''') = (term7 d' d''').
Proof. exact (TRANS (@lem1258577 d' d''') (@lem1258580 d' d''')). Qed.
Lemma lem1258582 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1258583 (d'' : nat) (d' : nat) (d''' : nat) : (term8 d'' d' d''') = (term9 d'' d' d''').
Proof. exact (MK_COMB (@lem1258582 d'') (@lem1258581 d' d''')). Qed.
Lemma lem1258585 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258586 (d'' : nat) (d' : nat) (d''' : nat) : (term9 d'' d' d''') = (term10 d'' d' d''').
Proof. exact (@lem1258585 d'' (term11 d' d''')). Qed.
Lemma lem1258587 (d'' : nat) (d' : nat) (d''' : nat) : (term8 d'' d' d''') = (term10 d'' d' d''').
Proof. exact (TRANS (@lem1258583 d'' d' d''') (@lem1258586 d'' d' d''')). Qed.
Lemma lem1258588 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1258589 (d'' : nat) (d' : nat) (d''' : nat) : (term2 d'' d' d''') = (term12 d'' d' d''').
Proof. exact (MK_COMB (@lem1258588 d'') (@lem1258587 d'' d' d''')). Qed.
Lemma lem1258591 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258592 (d'' : nat) (d' : nat) (d''' : nat) : (term12 d'' d' d''') = (term13 d'' d' d''').
Proof. exact (@lem1258591 d'' (term14 d'' d' d''')). Qed.
Lemma lem1258593 (d'' : nat) (d' : nat) (d''' : nat) : (term2 d'' d' d''') = (term13 d'' d' d''').
Proof. exact (TRANS (@lem1258589 d'' d' d''') (@lem1258592 d'' d' d''')). Qed.
Lemma lem1258594 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1258595 (d'' : nat) (d' : nat) (d''' : nat) : (term15 d'' d' d''') = (term16 d'' d' d''').
Proof. exact (MK_COMB (@lem1258594) (@lem1258593 d'' d' d''')). Qed.
Lemma lem1258596 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1258597 (d'' : nat) (d' : nat) (d''' : nat) : ((term2 d'' d' d''') = (NUMERAL 0)) = ((term13 d'' d' d''') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1258595 d'' d' d''') (@lem1258596)). Qed.
Lemma lem1258599 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1258600 (d'' : nat) (d' : nat) (d''' : nat) : ((term13 d'' d' d''') = (NUMERAL 0)) = False.
Proof. exact (@lem1258599 (term17 d'' d' d''')). Qed.
Lemma lem1258601 (d'' : nat) (d' : nat) (d''' : nat) : ((term2 d'' d' d''') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1258597 d'' d' d''') (@lem1258600 d'' d' d''')). Qed.
Lemma lem1258602 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1258603 (d'' : nat) (d' : nat) (d''' : nat) : (term1 d'' d' d''') = (~ False).
Proof. exact (MK_COMB (@lem1258602) (@lem1258601 d'' d' d''')). Qed.
Lemma lem1258605 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1258606 (d'' : nat) (d' : nat) (d''' : nat) : (term1 d'' d' d''') = True.
Proof. exact (TRANS (@lem1258603 d'' d' d''') (@lem1258605)). Qed.
Lemma lem1258607 (d'' : nat) (d' : nat) (d''' : nat) : (term0 d'' d' d''') = True.
Proof. exact (TRANS (@lem1258570 d'' d' d''') (@lem1258606 d'' d' d''')). Qed.
Lemma lem1258608 (d'' : nat) (d' : nat) (d''' : nat) : True = (term0 d'' d' d''').
Proof. exact (SYM (@lem1258607 d'' d' d''')). Qed.
Lemma lem1258609 (d'' : nat) (d' : nat) (d''' : nat) : term0 d'' d' d'''.
Proof. exact (EQ_MP (@lem1258608 d'' d' d''') (@lem0)). Qed.
