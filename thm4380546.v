Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4380546_term_abbrevs.
Require Import thm4380502_spec.
Lemma lem4380541 {_104960 _104961 : Type'} (s : _104960 -> Prop) : term0 _104960 _104961 s.
Proof. exact (fun f : type686 _104961 => @lem4380502 _104960 _104961 f s). Qed.
Lemma lem4380546 {_104960 _104961 : Type'} : term1 _104960 _104961.
Proof. exact (fun s : _104960 -> Prop => @lem4380541 _104960 _104961 s). Qed.
