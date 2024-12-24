Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21104_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1822_spec.
Require Import thm1855_spec.
Require Import thm21065_spec.
Lemma lem21091 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem21092 : term0 = True.
Proof. exact (@lem21091 (~ False)). Qed.
Lemma lem21093 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem21094 : term1 = (@eq Prop True).
Proof. exact (MK_COMB (@lem21093) (@lem21092)). Qed.
Lemma lem21096 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem21097 : (term0 = (~ False)) = (True = True).
Proof. exact (MK_COMB (@lem21094) (@lem21096)). Qed.
Lemma lem21099 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem21100 : (True = True) = True.
Proof. exact (@lem21099 True). Qed.
Lemma lem21101 : (term0 = (~ False)) = True.
Proof. exact (TRANS (@lem21097) (@lem21100)). Qed.
Lemma lem21102 : True = (term0 = (~ False)).
Proof. exact (SYM (@lem21101)). Qed.
Lemma lem21103 : term0 = (~ False).
Proof. exact (EQ_MP (@lem21102) (@lem0)). Qed.
Lemma lem21104 (p : Prop) (h1 : p = False) : (term2 p) = (~ p).
Proof. exact (EQ_MP (@lem21065 p h1) (@lem21103)). Qed.
