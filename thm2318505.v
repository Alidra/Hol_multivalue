Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2318505_term_abbrevs.
Require Import int_min_th_spec.
Lemma lem2318502 (x : int) : term0 x.
Proof. exact (@lem2293297 x). Qed.
Lemma lem2318503 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2318504 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2318503 x) (@lem2318502 x)). Qed.
Lemma lem2318505 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2318504 x y). Qed.
