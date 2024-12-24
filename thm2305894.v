Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2305894_term_abbrevs.
Require Import thm2305852_spec.
Require Import thm2305893_spec.
Lemma lem2305894 (n : int) (m : int) (p : int) : term0 n m p.
Proof. exact (conj (@lem2305893 m n p) (@lem2305852 n m p)). Qed.
