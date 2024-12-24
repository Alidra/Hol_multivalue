Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1365059_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Lemma lem1365048 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem1365049 : ((False /\ True) = False) = term0.
Proof. exact (@lem1365048 (False /\ True)). Qed.
Lemma lem1365051 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1365052 : (False /\ True) = False.
Proof. exact (@lem1365051 True). Qed.
Lemma lem1365053 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1365054 : term0 = (~ False).
Proof. exact (MK_COMB (@lem1365053) (@lem1365052)). Qed.
Lemma lem1365056 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1365057 : term0 = True.
Proof. exact (TRANS (@lem1365054) (@lem1365056)). Qed.
Lemma lem1365058 : ((False /\ True) = False) = True.
Proof. exact (TRANS (@lem1365049) (@lem1365057)). Qed.
Lemma lem1365059 : True = ((False /\ True) = False).
Proof. exact (SYM (@lem1365058)). Qed.
