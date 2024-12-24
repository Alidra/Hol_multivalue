Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3464376_term_abbrevs.
Require Import thm3459051_spec.
Require Import thm3464373_spec.
Lemma lem3464376 {_89837 _89861 _89862 _89863 : Type'} (P : type1517 _89861 _89862 _89863) (f : type1524 _89837 _89861 _89862 _89863) : (term0 _89837 _89861 _89862 _89863 P f) = (term1 _89837 _89861 _89862 _89863 P f).
Proof. exact (EQ_MP (@lem3459051 _89837 _89861 _89862 _89863 P f) (@lem3464373 _89837 _89861 _89862 _89863 P f)). Qed.
