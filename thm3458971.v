Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3458971_term_abbrevs.
Require Import thm3458970_spec.
Lemma lem3458971 {_89520 _89534 : Type'} : term0 _89520 _89534.
Proof. exact (fun P : _89534 -> Prop => @lem3458970 _89520 _89534 P). Qed.
