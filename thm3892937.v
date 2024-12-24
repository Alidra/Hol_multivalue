Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3892937_term_abbrevs.
Require Import thm3888988_spec.
Lemma lem3892937 {_100554 : Type'} (b : _100554) (a : _100554) (cs : _100554 -> Prop) (P : Prop) : term0 _100554 b a cs P.
Proof. exact (proj2 (@lem3888988 _100554 b a cs P)). Qed.
