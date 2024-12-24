Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1103191_term_abbrevs.
Require Import thm1103188_spec.
Lemma lem1103190 {_25376 : Type'} : term0 _25376.
Proof. exact (proj1 (@lem1103188 _25376)). Qed.
Lemma lem1103191 {_25376 : Type'} (x : _25376) : term1 _25376 x.
Proof. exact (@lem1103190 _25376 x). Qed.
