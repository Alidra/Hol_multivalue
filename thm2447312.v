Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2447312_term_abbrevs.
Require Import int_coprime_spec.
Lemma lem2447309 (a : int) : term0 a.
Proof. exact (@lem2444012 a). Qed.
Lemma lem2447310 (a : int) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem2447311 (a : int) : term1 a.
Proof. exact (EQ_MP (@lem2447310 a) (@lem2447309 a)). Qed.
Lemma lem2447312 (a : int) (b : int) : term2 a b.
Proof. exact (@lem2447311 a b). Qed.
