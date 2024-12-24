Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RAT_LEMMA5_term_abbrevs.
Require Import thm1979880_spec.
Lemma lem1979881 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : term0 x1 y2 x2 y1.
Proof. exact (fun h0 : term1 y1 y2 => @lem1979880 x1 x2 y1 y2 h0). Qed.
