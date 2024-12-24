Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2318511_term_abbrevs.
Require Import int_max_th_spec.
Lemma lem2318508 (x : int) : term0 x.
Proof. exact (@lem2292408 x). Qed.
Lemma lem2318509 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2318510 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2318509 x) (@lem2318508 x)). Qed.
Lemma lem2318511 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2318510 x y). Qed.
