Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm10176_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm1857_spec.
Lemma lem10166 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem10167 : ((~ True) = False) = term0.
Proof. exact (@lem10166 (~ True)). Qed.
Lemma lem10169 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem10170 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem10171 : term0 = (~ False).
Proof. exact (MK_COMB (@lem10170) (@lem10169)). Qed.
Lemma lem10173 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem10174 : term0 = True.
Proof. exact (TRANS (@lem10171) (@lem10173)). Qed.
Lemma lem10175 : ((~ True) = False) = True.
Proof. exact (TRANS (@lem10167) (@lem10174)). Qed.
Lemma lem10176 : True = ((~ True) = False).
Proof. exact (SYM (@lem10175)). Qed.
