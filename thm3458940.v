Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3458940_term_abbrevs.
Require Import thm3454209_spec.
Require Import thm3457131_spec.
Lemma lem3458940 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : term0 _89578 _89597 _89598 P f.
Proof. exact (EQ_MP (@lem3454209 _89578 _89597 _89598 P f) (@lem3457131 _89578 _89597 _89598 P f)). Qed.
