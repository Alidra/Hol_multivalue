Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2267742_term_abbrevs.
Require Import thm2267740_spec.
Require Import thm2267741_spec.
Lemma lem2267742 (r : real) : (integer r) = ((term0 r) = r).
Proof. exact (EQ_MP (@lem2267741 r) (@lem2267740 r)). Qed.
