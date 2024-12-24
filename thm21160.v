Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21160_term_abbrevs.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm1856_spec.
Lemma lem21153 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem21154 : (term0 = True) = term0.
Proof. exact (@lem21153 term0). Qed.
Lemma lem21156 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem21157 : term0 = True.
Proof. exact (@lem21156 (~ True)). Qed.
Lemma lem21158 : (term0 = True) = True.
Proof. exact (TRANS (@lem21154) (@lem21157)). Qed.
Lemma lem21159 : True = (term0 = True).
Proof. exact (SYM (@lem21158)). Qed.
Lemma lem21160 : term0 = True.
Proof. exact (EQ_MP (@lem21159) (@lem0)). Qed.
