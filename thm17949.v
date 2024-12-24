Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17949_term_abbrevs.
Require Import NOT_IMP_spec.
Lemma lem17946 (t1 : Prop) : term0 t1.
Proof. exact (@lem10299 t1). Qed.
Lemma lem17947 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem17948 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem17947 t1) (@lem17946 t1)). Qed.
Lemma lem17949 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem17948 t1 t2). Qed.
