Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2267740_term_abbrevs.
Require Import thm2267735_spec.
Lemma lem2267739 : term0.
Proof. exact (fun r : real => @lem2267735 r). Qed.
Lemma lem2267740 (r : real) : term1 r.
Proof. exact (@lem2267739 r). Qed.
