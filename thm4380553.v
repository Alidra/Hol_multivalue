Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4380553_term_abbrevs.
Require Import thm4380552_spec.
Lemma lem4380553 {_104907 _104908 : Type'} : term0 _104907 _104908.
Proof. exact (fun f : type686 _104907 => @lem4380552 _104907 _104908 f). Qed.
