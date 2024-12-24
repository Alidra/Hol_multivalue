Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1988188_term_abbrevs.
Require Import thm1988118_spec.
Lemma lem1988185 (x : real) : term0 x.
Proof. exact (@lem1988118 x). Qed.
Lemma lem1988186 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1988187 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1988186 x) (@lem1988185 x)). Qed.
Lemma lem1988188 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1988187 x y). Qed.
