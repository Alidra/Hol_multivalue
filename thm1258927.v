Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1258927_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246867_spec.
Require Import thm1246868_spec.
Require Import thm1823_spec.
Lemma lem1258899 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1258900 (d' : nat) (d''' : nat) : (term0 d' d''') = (term1 d' d''').
Proof. exact (@lem1258899 ((term2 d' d''') = (NUMERAL 0))). Qed.
Lemma lem1258904 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258905 (d' : nat) (d''' : nat) : (term3 d' d''') = (term4 d' d''').
Proof. exact (@lem1258904 d' d'''). Qed.
Lemma lem1258906 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1258907 (d' : nat) (d''' : nat) : (term2 d' d''') = (term5 d' d''').
Proof. exact (MK_COMB (@lem1258906 d') (@lem1258905 d' d''')). Qed.
Lemma lem1258909 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258910 (d' : nat) (d''' : nat) : (term5 d' d''') = (term6 d' d''').
Proof. exact (@lem1258909 d' (Nat.add d' d''')). Qed.
Lemma lem1258911 (d' : nat) (d''' : nat) : (term2 d' d''') = (term6 d' d''').
Proof. exact (TRANS (@lem1258907 d' d''') (@lem1258910 d' d''')). Qed.
Lemma lem1258912 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1258913 (d' : nat) (d''' : nat) : (term7 d' d''') = (term8 d' d''').
Proof. exact (MK_COMB (@lem1258912) (@lem1258911 d' d''')). Qed.
Lemma lem1258914 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1258915 (d' : nat) (d''' : nat) : ((term2 d' d''') = (NUMERAL 0)) = ((term6 d' d''') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1258913 d' d''') (@lem1258914)). Qed.
Lemma lem1258917 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1258918 (d' : nat) (d''' : nat) : ((term6 d' d''') = (NUMERAL 0)) = False.
Proof. exact (@lem1258917 (term9 d' d''')). Qed.
Lemma lem1258919 (d' : nat) (d''' : nat) : ((term2 d' d''') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1258915 d' d''') (@lem1258918 d' d''')). Qed.
Lemma lem1258920 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1258921 (d' : nat) (d''' : nat) : (term1 d' d''') = (~ False).
Proof. exact (MK_COMB (@lem1258920) (@lem1258919 d' d''')). Qed.
Lemma lem1258923 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1258924 (d' : nat) (d''' : nat) : (term1 d' d''') = True.
Proof. exact (TRANS (@lem1258921 d' d''') (@lem1258923)). Qed.
Lemma lem1258925 (d' : nat) (d''' : nat) : (term0 d' d''') = True.
Proof. exact (TRANS (@lem1258900 d' d''') (@lem1258924 d' d''')). Qed.
Lemma lem1258926 (d' : nat) (d''' : nat) : True = (term0 d' d''').
Proof. exact (SYM (@lem1258925 d' d''')). Qed.
Lemma lem1258927 (d' : nat) (d''' : nat) : term0 d' d'''.
Proof. exact (EQ_MP (@lem1258926 d' d''') (@lem0)). Qed.
