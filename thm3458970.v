Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3458970_term_abbrevs.
Require Import thm3458944_spec.
Lemma lem3458970 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term0 _89520 _89534 P.
Proof. exact (fun f : type1470 _89520 _89534 => @lem3458944 _89520 _89534 P f). Qed.
