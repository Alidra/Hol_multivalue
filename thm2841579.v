Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841579_term_abbrevs.
Require Import int_mul_th_spec.
Lemma lem2841576 (x : int) : term0 x.
Proof. exact (@lem2287415 x). Qed.
Lemma lem2841577 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2841578 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2841577 x) (@lem2841576 x)). Qed.
Lemma lem2841579 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2841578 x y). Qed.
