Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1258775_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246867_spec.
Require Import thm1246868_spec.
Require Import thm1823_spec.
Lemma lem1258747 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1258748 (d'' : nat) (d''' : nat) : (term0 d'' d''') = (term1 d'' d''').
Proof. exact (@lem1258747 ((term2 d'' d''') = (NUMERAL 0))). Qed.
Lemma lem1258752 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258753 (d'' : nat) (d''' : nat) : (term3 d'' d''') = (term4 d'' d''').
Proof. exact (@lem1258752 d'' d'''). Qed.
Lemma lem1258754 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1258755 (d'' : nat) (d''' : nat) : (term2 d'' d''') = (term5 d'' d''').
Proof. exact (MK_COMB (@lem1258754 d'') (@lem1258753 d'' d''')). Qed.
Lemma lem1258757 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258758 (d'' : nat) (d''' : nat) : (term5 d'' d''') = (term6 d'' d''').
Proof. exact (@lem1258757 d'' (Nat.add d'' d''')). Qed.
Lemma lem1258759 (d'' : nat) (d''' : nat) : (term2 d'' d''') = (term6 d'' d''').
Proof. exact (TRANS (@lem1258755 d'' d''') (@lem1258758 d'' d''')). Qed.
Lemma lem1258760 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1258761 (d'' : nat) (d''' : nat) : (term7 d'' d''') = (term8 d'' d''').
Proof. exact (MK_COMB (@lem1258760) (@lem1258759 d'' d''')). Qed.
Lemma lem1258762 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1258763 (d'' : nat) (d''' : nat) : ((term2 d'' d''') = (NUMERAL 0)) = ((term6 d'' d''') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1258761 d'' d''') (@lem1258762)). Qed.
Lemma lem1258765 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1258766 (d'' : nat) (d''' : nat) : ((term6 d'' d''') = (NUMERAL 0)) = False.
Proof. exact (@lem1258765 (term9 d'' d''')). Qed.
Lemma lem1258767 (d'' : nat) (d''' : nat) : ((term2 d'' d''') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1258763 d'' d''') (@lem1258766 d'' d''')). Qed.
Lemma lem1258768 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1258769 (d'' : nat) (d''' : nat) : (term1 d'' d''') = (~ False).
Proof. exact (MK_COMB (@lem1258768) (@lem1258767 d'' d''')). Qed.
Lemma lem1258771 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1258772 (d'' : nat) (d''' : nat) : (term1 d'' d''') = True.
Proof. exact (TRANS (@lem1258769 d'' d''') (@lem1258771)). Qed.
Lemma lem1258773 (d'' : nat) (d''' : nat) : (term0 d'' d''') = True.
Proof. exact (TRANS (@lem1258748 d'' d''') (@lem1258772 d'' d''')). Qed.
Lemma lem1258774 (d'' : nat) (d''' : nat) : True = (term0 d'' d''').
Proof. exact (SYM (@lem1258773 d'' d''')). Qed.
Lemma lem1258775 (d'' : nat) (d''' : nat) : term0 d'' d'''.
Proof. exact (EQ_MP (@lem1258774 d'' d''') (@lem0)). Qed.
