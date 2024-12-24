Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RAT_LEMMA3_term_abbrevs.
Require Import thm1978411_spec.
Lemma lem1978412 (x1 : real) (x2 : real) (y1 : real) (y2 : real) : term0 x1 x2 y1 y2.
Proof. exact (fun h0 : term1 y1 y2 => @lem1978411 x1 x2 y1 y2 h0). Qed.
