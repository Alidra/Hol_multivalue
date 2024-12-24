Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2447297_term_abbrevs.
Require Import int_divides_spec.
Lemma lem2447294 (b : int) : term0 b.
Proof. exact (@lem2429416 b). Qed.
Lemma lem2447295 (b : int) : (term0 b) = (term1 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem2447296 (b : int) : term1 b.
Proof. exact (EQ_MP (@lem2447295 b) (@lem2447294 b)). Qed.
Lemma lem2447297 (b : int) (a : int) : term2 b a.
Proof. exact (@lem2447296 b a). Qed.
