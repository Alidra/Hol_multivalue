Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3458941_term_abbrevs.
Require Import thm3454059_spec.
Require Import thm3455583_spec.
Lemma lem3458941 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term0 _89520 _89534 P f.
Proof. exact (EQ_MP (@lem3454059 _89520 _89534 P f) (@lem3455583 _89520 _89534 P f)). Qed.