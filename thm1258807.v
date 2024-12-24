Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1258807_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246867_spec.
Require Import thm1246868_spec.
Require Import thm1823_spec.
Lemma lem1258779 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1258780 (d' : nat) (d''' : nat) : (term0 d' d''') = (term1 d' d''').
Proof. exact (@lem1258779 ((term2 d' d''') = (NUMERAL 0))). Qed.
Lemma lem1258784 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258785 (d' : nat) (d''' : nat) : (term3 d' d''') = (term4 d' d''').
Proof. exact (@lem1258784 d' d'''). Qed.
Lemma lem1258786 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1258787 (d' : nat) (d''' : nat) : (term2 d' d''') = (term5 d' d''').
Proof. exact (MK_COMB (@lem1258786 d') (@lem1258785 d' d''')). Qed.
Lemma lem1258789 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258790 (d' : nat) (d''' : nat) : (term5 d' d''') = (term6 d' d''').
Proof. exact (@lem1258789 d' (Nat.add d' d''')). Qed.
Lemma lem1258791 (d' : nat) (d''' : nat) : (term2 d' d''') = (term6 d' d''').
Proof. exact (TRANS (@lem1258787 d' d''') (@lem1258790 d' d''')). Qed.
Lemma lem1258792 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1258793 (d' : nat) (d''' : nat) : (term7 d' d''') = (term8 d' d''').
Proof. exact (MK_COMB (@lem1258792) (@lem1258791 d' d''')). Qed.
Lemma lem1258794 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1258795 (d' : nat) (d''' : nat) : ((term2 d' d''') = (NUMERAL 0)) = ((term6 d' d''') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1258793 d' d''') (@lem1258794)). Qed.
Lemma lem1258797 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1258798 (d' : nat) (d''' : nat) : ((term6 d' d''') = (NUMERAL 0)) = False.
Proof. exact (@lem1258797 (term9 d' d''')). Qed.
Lemma lem1258799 (d' : nat) (d''' : nat) : ((term2 d' d''') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1258795 d' d''') (@lem1258798 d' d''')). Qed.
Lemma lem1258800 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1258801 (d' : nat) (d''' : nat) : (term1 d' d''') = (~ False).
Proof. exact (MK_COMB (@lem1258800) (@lem1258799 d' d''')). Qed.
Lemma lem1258803 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1258804 (d' : nat) (d''' : nat) : (term1 d' d''') = True.
Proof. exact (TRANS (@lem1258801 d' d''') (@lem1258803)). Qed.
Lemma lem1258805 (d' : nat) (d''' : nat) : (term0 d' d''') = True.
Proof. exact (TRANS (@lem1258780 d' d''') (@lem1258804 d' d''')). Qed.
Lemma lem1258806 (d' : nat) (d''' : nat) : True = (term0 d' d''').
Proof. exact (SYM (@lem1258805 d' d''')). Qed.
Lemma lem1258807 (d' : nat) (d''' : nat) : term0 d' d'''.
Proof. exact (EQ_MP (@lem1258806 d' d''') (@lem0)). Qed.
