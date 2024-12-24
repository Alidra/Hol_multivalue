Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4380536_term_abbrevs.
Require Import thm4380490_spec.
Lemma lem4380531 {_105011 _105012 : Type'} (f : type686 _105011) : term0 _105011 _105012 f.
Proof. exact (fun t : _105012 -> Prop => @lem4380490 _105011 _105012 f t). Qed.
Lemma lem4380536 {_105011 _105012 : Type'} : term1 _105011 _105012.
Proof. exact (fun f : type686 _105011 => @lem4380531 _105011 _105012 f). Qed.
