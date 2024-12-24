Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184719_term_abbrevs.
Require Import thm3184708_spec.
Require Import thm3184718_spec.
Lemma lem3184719 {_83152 _83169 : Type'} : term0 _83152 _83169.
Proof. exact (conj (@lem3184718 _83152) (@lem3184708 _83169)). Qed.
