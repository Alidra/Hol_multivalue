Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm52757_term_abbrevs.
Require Import thm52751_spec.
Require Import thm52756_spec.
Lemma lem52757 {_5284 _5296 _5299 _5300 _5310 _5326 _5330 _5333 _5334 : Type'} : term0 _5284 _5296 _5299 _5300 _5310 _5326 _5330 _5333 _5334.
Proof. exact (conj (@lem52756 _5284 _5296 _5299 _5300) (@lem52751 _5310 _5326 _5330 _5333 _5334)). Qed.
