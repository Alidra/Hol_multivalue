Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2447306_term_abbrevs.
Require Import int_congruent_spec.
Lemma lem2447300 (x : int) : term0 x.
Proof. exact (@lem2437518 x). Qed.
Lemma lem2447301 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2447302 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2447301 x) (@lem2447300 x)). Qed.
Lemma lem2447303 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2447302 x y). Qed.
Lemma lem2447304 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2447305 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2447304 x y) (@lem2447303 x y)). Qed.
Lemma lem2447306 (x : int) (y : int) (n : int) : term4 x y n.
Proof. exact (@lem2447305 x y n). Qed.
