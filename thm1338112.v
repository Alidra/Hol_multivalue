Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1338112_term_abbrevs.
Require Import thm1338093_spec.
Lemma lem1338108 : term0.
Proof. exact (proj1 (@lem1338093)). Qed.
Lemma lem1338109 (x : prod hreal hreal) : term1 x.
Proof. exact (@lem1338108 x). Qed.
Lemma lem1338110 (x : prod hreal hreal) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1338111 (x : prod hreal hreal) : term2 x.
Proof. exact (EQ_MP (@lem1338110 x) (@lem1338109 x)). Qed.
Lemma lem1338112 (x : prod hreal hreal) (y : prod hreal hreal) : term3 x y.
Proof. exact (@lem1338111 x y). Qed.
