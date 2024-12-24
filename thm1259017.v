Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1259017_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1246847_spec.
Require Import thm1246848_spec.
Require Import thm1823_spec.
Lemma lem1259005 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1259006 (d''' : nat) : (term0 d''') = (term1 d''').
Proof. exact (@lem1259005 ((S d''') = (NUMERAL 0))). Qed.
Lemma lem1259008 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1246848 n (@lem1246847 n)). Qed.
Lemma lem1259009 (d''' : nat) : ((S d''') = (NUMERAL 0)) = False.
Proof. exact (@lem1259008 d'''). Qed.
Lemma lem1259010 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1259011 (d''' : nat) : (term1 d''') = (~ False).
Proof. exact (MK_COMB (@lem1259010) (@lem1259009 d''')). Qed.
Lemma lem1259013 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1259014 (d''' : nat) : (term1 d''') = True.
Proof. exact (TRANS (@lem1259011 d''') (@lem1259013)). Qed.
Lemma lem1259015 (d''' : nat) : (term0 d''') = True.
Proof. exact (TRANS (@lem1259006 d''') (@lem1259014 d''')). Qed.
Lemma lem1259016 (d''' : nat) : True = (term0 d''').
Proof. exact (SYM (@lem1259015 d''')). Qed.
Lemma lem1259017 (d''' : nat) : term0 d'''.
Proof. exact (EQ_MP (@lem1259016 d''') (@lem0)). Qed.
