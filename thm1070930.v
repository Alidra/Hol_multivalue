Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1070930_term_abbrevs.
Require Import thm1070927_spec.
Lemma lem1070930 {A : Type'} (list' : type1338 A) (NIL' : recspace A) (CONS' : type1399 A) (h1 : list' = (term0 A NIL' CONS')) : list' NIL'.
Proof. exact (proj1 (@lem1070927 A list' NIL' CONS' h1)). Qed.
