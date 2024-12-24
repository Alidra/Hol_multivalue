Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1258513_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1823_spec.
Lemma lem1258501 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1258502 (d''' : nat) : (term0 d''') = (term1 d''').
Proof. exact (@lem1258501 ((S d''') = (NUMERAL 0))). Qed.
Lemma lem1258504 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1258505 (d''' : nat) : ((S d''') = (NUMERAL 0)) = False.
Proof. exact (@lem1258504 d'''). Qed.
Lemma lem1258506 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1258507 (d''' : nat) : (term1 d''') = (~ False).
Proof. exact (MK_COMB (@lem1258506) (@lem1258505 d''')). Qed.
Lemma lem1258509 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1258510 (d''' : nat) : (term1 d''') = True.
Proof. exact (TRANS (@lem1258507 d''') (@lem1258509)). Qed.
Lemma lem1258511 (d''' : nat) : (term0 d''') = True.
Proof. exact (TRANS (@lem1258502 d''') (@lem1258510 d''')). Qed.
Lemma lem1258512 (d''' : nat) : True = (term0 d''').
Proof. exact (SYM (@lem1258511 d''')). Qed.
Lemma lem1258513 (d''' : nat) : term0 d'''.
Proof. exact (EQ_MP (@lem1258512 d''') (@lem0)). Qed.
