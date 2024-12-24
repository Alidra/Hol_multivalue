Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2841561_term_abbrevs.
Require Import int_abs_th_spec.
Lemma lem2841561 (x : int) : term0 x.
Proof. exact (@lem2288272 x). Qed.
