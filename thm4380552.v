Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4380552_term_abbrevs.
Require Import thm4380526_spec.
Lemma lem4380552 {_104907 _104908 : Type'} (f : type686 _104907) : term0 _104907 _104908 f.
Proof. exact (fun g : type686 _104908 => @lem4380526 _104907 _104908 f g). Qed.
