Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2416555_term_abbrevs.
Require Import thm2416552_spec.
Lemma lem2416555 (a : int) (c : int) (b : int) (d : int) : (term0 a b c d) = (term0 a c b d).
Proof. exact (proj1 (@lem2416552 b a c d (@el nat) (@el int) (@el int) (@el int) (@el nat))). Qed.
