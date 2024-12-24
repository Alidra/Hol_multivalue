Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1258959_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246867_spec.
Require Import thm1246868_spec.
Require Import thm1823_spec.
Lemma lem1258931 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1258932 (d'' : nat) (d''' : nat) : (term0 d'' d''') = (term1 d'' d''').
Proof. exact (@lem1258931 ((term2 d'' d''') = (NUMERAL 0))). Qed.
Lemma lem1258936 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258937 (d'' : nat) (d''' : nat) : (term3 d'' d''') = (term4 d'' d''').
Proof. exact (@lem1258936 d'' d'''). Qed.
Lemma lem1258938 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1258939 (d'' : nat) (d''' : nat) : (term2 d'' d''') = (term5 d'' d''').
Proof. exact (MK_COMB (@lem1258938 d'') (@lem1258937 d'' d''')). Qed.
Lemma lem1258941 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246868 m n) (@lem1246867 m n)). Qed.
Lemma lem1258942 (d'' : nat) (d''' : nat) : (term5 d'' d''') = (term6 d'' d''').
Proof. exact (@lem1258941 d'' (Nat.add d'' d''')). Qed.
Lemma lem1258943 (d'' : nat) (d''' : nat) : (term2 d'' d''') = (term6 d'' d''').
Proof. exact (TRANS (@lem1258939 d'' d''') (@lem1258942 d'' d''')). Qed.
Lemma lem1258944 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1258945 (d'' : nat) (d''' : nat) : (term7 d'' d''') = (term8 d'' d''').
Proof. exact (MK_COMB (@lem1258944) (@lem1258943 d'' d''')). Qed.
Lemma lem1258946 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1258947 (d'' : nat) (d''' : nat) : ((term2 d'' d''') = (NUMERAL 0)) = ((term6 d'' d''') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1258945 d'' d''') (@lem1258946)). Qed.
Lemma lem1258949 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1258950 (d'' : nat) (d''' : nat) : ((term6 d'' d''') = (NUMERAL 0)) = False.
Proof. exact (@lem1258949 (term9 d'' d''')). Qed.
Lemma lem1258951 (d'' : nat) (d''' : nat) : ((term2 d'' d''') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1258947 d'' d''') (@lem1258950 d'' d''')). Qed.
Lemma lem1258952 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1258953 (d'' : nat) (d''' : nat) : (term1 d'' d''') = (~ False).
Proof. exact (MK_COMB (@lem1258952) (@lem1258951 d'' d''')). Qed.
Lemma lem1258955 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1258956 (d'' : nat) (d''' : nat) : (term1 d'' d''') = True.
Proof. exact (TRANS (@lem1258953 d'' d''') (@lem1258955)). Qed.
Lemma lem1258957 (d'' : nat) (d''' : nat) : (term0 d'' d''') = True.
Proof. exact (TRANS (@lem1258932 d'' d''') (@lem1258956 d'' d''')). Qed.
Lemma lem1258958 (d'' : nat) (d''' : nat) : True = (term0 d'' d''').
Proof. exact (SYM (@lem1258957 d'' d''')). Qed.
Lemma lem1258959 (d'' : nat) (d''' : nat) : term0 d'' d'''.
Proof. exact (EQ_MP (@lem1258958 d'' d''') (@lem0)). Qed.
