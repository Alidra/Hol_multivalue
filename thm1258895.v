Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1258895_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246867_spec.
Require Import thm1246868_spec.
Require Import thm1823_spec.
Lemma lem1258855 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1258856 (d'' : nat) (d' : nat) (d''' : nat) : (term0 d'' d' d''') = (term1 d'' d' d''').
Proof. exact (@lem1258855 ((term2 d'' d' d''') = (NUMERAL 0))). Qed.
Lemma lem1258860 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258861 (d' : nat) (d''' : nat) : (term3 d' d''') = (term4 d' d''').
Proof. exact (@lem1258860 d' d'''). Qed.
Lemma lem1258862 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1258863 (d' : nat) (d''' : nat) : (term5 d' d''') = (term6 d' d''').
Proof. exact (MK_COMB (@lem1258862 d') (@lem1258861 d' d''')). Qed.
Lemma lem1258865 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258866 (d' : nat) (d''' : nat) : (term6 d' d''') = (term7 d' d''').
Proof. exact (@lem1258865 d' (Nat.add d' d''')). Qed.
Lemma lem1258867 (d' : nat) (d''' : nat) : (term5 d' d''') = (term7 d' d''').
Proof. exact (TRANS (@lem1258863 d' d''') (@lem1258866 d' d''')). Qed.
Lemma lem1258868 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1258869 (d'' : nat) (d' : nat) (d''' : nat) : (term8 d'' d' d''') = (term9 d'' d' d''').
Proof. exact (MK_COMB (@lem1258868 d'') (@lem1258867 d' d''')). Qed.
Lemma lem1258871 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258872 (d'' : nat) (d' : nat) (d''' : nat) : (term9 d'' d' d''') = (term10 d'' d' d''').
Proof. exact (@lem1258871 d'' (term11 d' d''')). Qed.
Lemma lem1258873 (d'' : nat) (d' : nat) (d''' : nat) : (term8 d'' d' d''') = (term10 d'' d' d''').
Proof. exact (TRANS (@lem1258869 d'' d' d''') (@lem1258872 d'' d' d''')). Qed.
Lemma lem1258874 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1258875 (d'' : nat) (d' : nat) (d''' : nat) : (term2 d'' d' d''') = (term12 d'' d' d''').
Proof. exact (MK_COMB (@lem1258874 d'') (@lem1258873 d'' d' d''')). Qed.
Lemma lem1258877 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258878 (d'' : nat) (d' : nat) (d''' : nat) : (term12 d'' d' d''') = (term13 d'' d' d''').
Proof. exact (@lem1258877 d'' (term14 d'' d' d''')). Qed.
Lemma lem1258879 (d'' : nat) (d' : nat) (d''' : nat) : (term2 d'' d' d''') = (term13 d'' d' d''').
Proof. exact (TRANS (@lem1258875 d'' d' d''') (@lem1258878 d'' d' d''')). Qed.
Lemma lem1258880 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1258881 (d'' : nat) (d' : nat) (d''' : nat) : (term15 d'' d' d''') = (term16 d'' d' d''').
Proof. exact (MK_COMB (@lem1258880) (@lem1258879 d'' d' d''')). Qed.
Lemma lem1258882 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1258883 (d'' : nat) (d' : nat) (d''' : nat) : ((term2 d'' d' d''') = (NUMERAL 0)) = ((term13 d'' d' d''') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1258881 d'' d' d''') (@lem1258882)). Qed.
Lemma lem1258885 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1258886 (d'' : nat) (d' : nat) (d''' : nat) : ((term13 d'' d' d''') = (NUMERAL 0)) = False.
Proof. exact (@lem1258885 (term17 d'' d' d''')). Qed.
Lemma lem1258887 (d'' : nat) (d' : nat) (d''' : nat) : ((term2 d'' d' d''') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1258883 d'' d' d''') (@lem1258886 d'' d' d''')). Qed.
Lemma lem1258888 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1258889 (d'' : nat) (d' : nat) (d''' : nat) : (term1 d'' d' d''') = (~ False).
Proof. exact (MK_COMB (@lem1258888) (@lem1258887 d'' d' d''')). Qed.
Lemma lem1258891 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1258892 (d'' : nat) (d' : nat) (d''' : nat) : (term1 d'' d' d''') = True.
Proof. exact (TRANS (@lem1258889 d'' d' d''') (@lem1258891)). Qed.
Lemma lem1258893 (d'' : nat) (d' : nat) (d''' : nat) : (term0 d'' d' d''') = True.
Proof. exact (TRANS (@lem1258856 d'' d' d''') (@lem1258892 d'' d' d''')). Qed.
Lemma lem1258894 (d'' : nat) (d' : nat) (d''' : nat) : True = (term0 d'' d' d''').
Proof. exact (SYM (@lem1258893 d'' d' d''')). Qed.
Lemma lem1258895 (d'' : nat) (d' : nat) (d''' : nat) : term0 d'' d' d'''.
Proof. exact (EQ_MP (@lem1258894 d'' d' d''') (@lem0)). Qed.
