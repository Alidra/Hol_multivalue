Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1240243_term_abbrevs.
Require Import thm1240241_spec.
Lemma lem1240243 (char' : type1335) (_22730' : type1539) (h1 : char' = (term0 _22730')) : term1 _22730' char'.
Proof. exact (proj1 (@lem1240241 char' _22730' h1)). Qed.
