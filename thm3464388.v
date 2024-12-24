Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3464388_term_abbrevs.
Require Import thm3464376_spec.
Lemma lem3464383 {_89837 _89861 _89862 _89863 : Type'} (P : type1517 _89861 _89862 _89863) : term0 _89837 _89861 _89862 _89863 P.
Proof. exact (fun f : type1524 _89837 _89861 _89862 _89863 => @lem3464376 _89837 _89861 _89862 _89863 P f). Qed.
Lemma lem3464388 {_89837 _89861 _89862 _89863 : Type'} : term1 _89837 _89861 _89862 _89863.
Proof. exact (fun P : type1517 _89861 _89862 _89863 => @lem3464383 _89837 _89861 _89862 _89863 P). Qed.
