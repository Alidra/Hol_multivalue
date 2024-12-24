Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm1856_spec.
Lemma lem10179 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem10180 : ((~ False) = True) = (~ False).
Proof. exact (@lem10179 (~ False)). Qed.
Lemma lem10182 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem10183 : ((~ False) = True) = True.
Proof. exact (TRANS (@lem10180) (@lem10182)). Qed.
Lemma lem10184 : True = ((~ False) = True).
Proof. exact (SYM (@lem10183)). Qed.
