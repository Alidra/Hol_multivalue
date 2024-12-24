Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import UNIONS_GSPEC_term_abbrevs.
Require Import thm3458965_spec.
Require Import thm3458970_spec.
Lemma lem3458975 {_89520 _89534 : Type'} : term0 _89520 _89534.
Proof. exact (fun P : _89534 -> Prop => @lem3458970 _89520 _89534 P). Qed.
Lemma lem3458976 {_89520 _89534 _89578 _89597 _89598 _89646 _89670 _89671 _89672 : Type'} : term1 _89520 _89534 _89578 _89597 _89598 _89646 _89670 _89671 _89672.
Proof. exact (conj (@lem3458975 _89520 _89534) (@lem3458965 _89578 _89597 _89598 _89646 _89670 _89671 _89672)). Qed.
