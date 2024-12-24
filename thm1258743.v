Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1258743_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1823_spec.
Lemma lem1258731 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1258732 (d''' : nat) : (term0 d''') = (term1 d''').
Proof. exact (@lem1258731 ((S d''') = (NUMERAL 0))). Qed.
Lemma lem1258734 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1258735 (d''' : nat) : ((S d''') = (NUMERAL 0)) = False.
Proof. exact (@lem1258734 d'''). Qed.
Lemma lem1258736 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1258737 (d''' : nat) : (term1 d''') = (~ False).
Proof. exact (MK_COMB (@lem1258736) (@lem1258735 d''')). Qed.
Lemma lem1258739 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1258740 (d''' : nat) : (term1 d''') = True.
Proof. exact (TRANS (@lem1258737 d''') (@lem1258739)). Qed.
Lemma lem1258741 (d''' : nat) : (term0 d''') = True.
Proof. exact (TRANS (@lem1258732 d''') (@lem1258740 d''')). Qed.
Lemma lem1258742 (d''' : nat) : True = (term0 d''').
Proof. exact (SYM (@lem1258741 d''')). Qed.
Lemma lem1258743 (d''' : nat) : term0 d'''.
Proof. exact (EQ_MP (@lem1258742 d''') (@lem0)). Qed.
