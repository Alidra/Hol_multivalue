Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7928420_term_abbrevs.
Require Import thm7928418_spec.
Lemma lem7928420 {A : Type'} (tybit1' : type1329 A) (_103802' : type39 A) (h1 : tybit1' = (term0 A _103802')) : term1 A _103802' tybit1'.
Proof. exact (proj1 (@lem7928418 A tybit1' _103802' h1)). Qed.
