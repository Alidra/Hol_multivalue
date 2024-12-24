Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1071333_term_abbrevs.
Require Import thm1070997_spec.
Require Import thm1071331_spec.
Lemma lem1071332 {A : Type'} (NIL' : recspace A) (h1 : NIL' = (term0 A)) : (term1 A) = (@_mk_list A NIL').
Proof. exact (SYM (@lem1070997 A NIL' h1)). Qed.
Lemma lem1071333 {A : Type'} (NIL' : recspace A) (h1 : NIL' = (term0 A)) : (@nil A) = (@_mk_list A NIL').
Proof. exact (TRANS (@lem1071331 A) (@lem1071332 A NIL' h1)). Qed.
