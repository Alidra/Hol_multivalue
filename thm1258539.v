Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1258539_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1246874_spec.
Require Import thm1246875_spec.
Require Import thm1823_spec.
Lemma lem1258517 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1258518 (d''' : nat) (d'' : nat) : (term0 d''' d'') = (term1 d''' d'').
Proof. exact (@lem1258517 ((term2 d''' d'') = (NUMERAL 0))). Qed.
Lemma lem1258522 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem1246875 m n) (@lem1246874 m n)). Qed.
Lemma lem1258523 (d''' : nat) (d'' : nat) : (term2 d''' d'') = (term5 d''' d'').
Proof. exact (@lem1258522 d''' (Nat.add d'' d'')). Qed.
Lemma lem1258524 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1258525 (d''' : nat) (d'' : nat) : (term6 d''' d'') = (term7 d''' d'').
Proof. exact (MK_COMB (@lem1258524) (@lem1258523 d''' d'')). Qed.
Lemma lem1258526 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1258527 (d''' : nat) (d'' : nat) : ((term2 d''' d'') = (NUMERAL 0)) = ((term5 d''' d'') = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1258525 d''' d'') (@lem1258526)). Qed.
Lemma lem1258529 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1258530 (d''' : nat) (d'' : nat) : ((term5 d''' d'') = (NUMERAL 0)) = False.
Proof. exact (@lem1258529 (term8 d''' d'')). Qed.
Lemma lem1258531 (d''' : nat) (d'' : nat) : ((term2 d''' d'') = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1258527 d''' d'') (@lem1258530 d''' d'')). Qed.
Lemma lem1258532 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1258533 (d''' : nat) (d'' : nat) : (term1 d''' d'') = (~ False).
Proof. exact (MK_COMB (@lem1258532) (@lem1258531 d''' d'')). Qed.
Lemma lem1258535 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1258536 (d''' : nat) (d'' : nat) : (term1 d''' d'') = True.
Proof. exact (TRANS (@lem1258533 d''' d'') (@lem1258535)). Qed.
Lemma lem1258537 (d''' : nat) (d'' : nat) : (term0 d''' d'') = True.
Proof. exact (TRANS (@lem1258518 d''' d'') (@lem1258536 d''' d'')). Qed.
Lemma lem1258538 (d''' : nat) (d'' : nat) : True = (term0 d''' d'').
Proof. exact (SYM (@lem1258537 d''' d'')). Qed.
Lemma lem1258539 (d''' : nat) (d'' : nat) : term0 d''' d''.
Proof. exact (EQ_MP (@lem1258538 d''' d'') (@lem0)). Qed.
