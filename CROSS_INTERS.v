Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CROSS_INTERS_term_abbrevs.
Require Import thm4380536_spec.
Require Import thm4380546_spec.
Lemma lem4380559 {_104960 _104961 _105011 _105012 : Type'} : term0 _104960 _104961 _105011 _105012.
Proof. exact (conj (@lem4380546 _104960 _104961) (@lem4380536 _105011 _105012)). Qed.
