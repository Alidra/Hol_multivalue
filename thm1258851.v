Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1258851_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246867_spec.
Require Import thm1246868_spec.
Require Import thm1823_spec.
Lemma lem1258811 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1258812 (d'' : nat) (d' : nat) (d''' : nat) : (term0 d'' d' d''') = (term1 d'' d' d''').
Proof. exact (@lem1258811 ((term2 d'' d' d''') = (NUMERAL 0))). Qed.
Lemma lem1258816 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258817 (d' : nat) (d''' : nat) : (term3 d' d''') = (term4 d' d''').
Proof. exact (@lem1258816 d' d'''). Qed.
Lemma lem1258818 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1258819 (d' : nat) (d''' : nat) : (term5 d' d''') = (term6 d' d''').
Proof. exact (MK_COMB (@lem1258818 d') (@lem1258817 d' d''')). Qed.
Lemma lem1258821 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258822 (d' : nat) (d''' : nat) : (term6 d' d''') = (term7 d' d''').
Proof. exact (@lem1258821 d' (Nat.add d' d''')). Qed.
Lemma lem1258823 (d' : nat) (d''' : nat) : (term5 d' d''') = (term7 d' d''').
Proof. exact (TRANS (@lem1258819 d' d''') (@lem1258822 d' d''')). Qed.
Lemma lem1258824 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1258825 (d'' : nat) (d' : nat) (d''' : nat) : (term8 d'' d' d''') = (term9 d'' d' d''').
Proof. exact (MK_COMB (@lem1258824 d'') (@lem1258823 d' d''')). Qed.
Lemma lem1258827 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258828 (d'' : nat) (d' : nat) (d''' : nat) : (term9 d'' d' d''') = (term10 d'' d' d''').
Proof. exact (@lem1258827 d'' (term11 d' d''')). Qed.
Lemma lem1258829 (d'' : nat) (d' : nat) (d''' : nat) : (term8 d'' d' d''') = (term10 d'' d' d''').
Proof. exact (TRANS (@lem1258825 d'' d' d''') (@lem1258828 d'' d' d''')). Qed.
Lemma lem1258830 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1258831 (d'' : nat) (d' : nat) (d''' : nat) : (term2 d'' d' d''') = (term12 d'' d' d''').
Proof. exact (MK_COMB (@lem1258830 d'') (@lem1258829 d'' d' d''')). Qed.
Lemma lem1258833 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258834 (d'' : nat) (d' : nat) (d''' : nat) : (term12 d'' d' d''') = (term13 d'' d' d''').
Proof. exact (@lem1258833 d'' (term14 d'' d' d''')). Qed.
Lemma lem1258835 (d'' : nat) (d' : nat) (d''' : nat) : (term2 d'' d' d''') = (term13 d'' d' d''').
Proof. exact (TRANS (@lem1258831 d'' d' d''') (@lem1258834 d'' d' d''')). Qed.
Lemma lem1258836 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1258837 (d'' : nat) (d' : nat) (d''' : nat) : (term15 d'' d' d''') = (term16 d'' d' d''').
Proof. exact (MK_COMB (@lem1258836) (@lem1258835 d'' d' d''')). Qed.
Lemma lem1258838 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1258839 (d'' : nat) (d' : nat) (d''' : nat) : ((term2 d'' d' d''') = (NUMERAL 0)) = ((term13 d'' d' d''') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1258837 d'' d' d''') (@lem1258838)). Qed.
Lemma lem1258841 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1258842 (d'' : nat) (d' : nat) (d''' : nat) : ((term13 d'' d' d''') = (NUMERAL 0)) = False.
Proof. exact (@lem1258841 (term17 d'' d' d''')). Qed.
Lemma lem1258843 (d'' : nat) (d' : nat) (d''' : nat) : ((term2 d'' d' d''') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1258839 d'' d' d''') (@lem1258842 d'' d' d''')). Qed.
Lemma lem1258844 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1258845 (d'' : nat) (d' : nat) (d''' : nat) : (term1 d'' d' d''') = (~ False).
Proof. exact (MK_COMB (@lem1258844) (@lem1258843 d'' d' d''')). Qed.
Lemma lem1258847 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1258848 (d'' : nat) (d' : nat) (d''' : nat) : (term1 d'' d' d''') = True.
Proof. exact (TRANS (@lem1258845 d'' d' d''') (@lem1258847)). Qed.
Lemma lem1258849 (d'' : nat) (d' : nat) (d''' : nat) : (term0 d'' d' d''') = True.
Proof. exact (TRANS (@lem1258812 d'' d' d''') (@lem1258848 d'' d' d''')). Qed.
Lemma lem1258850 (d'' : nat) (d' : nat) (d''' : nat) : True = (term0 d'' d' d''').
Proof. exact (SYM (@lem1258849 d'' d' d''')). Qed.
Lemma lem1258851 (d'' : nat) (d' : nat) (d''' : nat) : term0 d'' d' d'''.
Proof. exact (EQ_MP (@lem1258850 d'' d' d''') (@lem0)). Qed.
