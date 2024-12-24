Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1240294_term_abbrevs.
Lemma lem1240294 (r : type1678) : (term0 r) = ((term1 r) = r).
Proof. exact (@axiom_18 r). Qed.
