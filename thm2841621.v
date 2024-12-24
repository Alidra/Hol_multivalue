Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841621_term_abbrevs.
Require Import int_eq_spec.
Lemma lem2841618 (x : int) : term0 x.
Proof. exact (@lem2268427 x). Qed.
Lemma lem2841619 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2841620 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2841619 x) (@lem2841618 x)). Qed.
Lemma lem2841621 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2841620 x y). Qed.
