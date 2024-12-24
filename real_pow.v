Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import real_pow_term_abbrevs.
Require Import thm1344312_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Lemma lem1344315 (x : real) : term0 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1344316 (x : real) : term1 x.
Proof. exact (conj (@lem1344312 x) (@lem1344315 x)). Qed.
