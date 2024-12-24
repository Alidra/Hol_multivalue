Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2301004_term_abbrevs.
Require Import thm2300962_spec.
Require Import thm2301003_spec.
Lemma lem2301004 (n : int) (m : int) (p : int) : term0 n m p.
Proof. exact (conj (@lem2301003 m n p) (@lem2300962 n m p)). Qed.
