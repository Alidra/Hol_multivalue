Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2338243_term_abbrevs.
Require Import CONTRAPOS_THM_spec.
Lemma lem2338240 (t1 : Prop) : term0 t1.
Proof. exact (@lem10414 t1). Qed.
Lemma lem2338241 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem2338242 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem2338241 t1) (@lem2338240 t1)). Qed.
Lemma lem2338243 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem2338242 t1 t2). Qed.
