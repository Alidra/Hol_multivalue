Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7928419_term_abbrevs.
Require Import thm7928417_spec.
Lemma lem7928419 {A : Type'} (tybit1' : type1329 A) (_103802' : type39 A) (h1 : tybit1' = (term0 A _103802')) : term1 A tybit1' _103802'.
Proof. exact (proj1 (@lem7928417 A tybit1' _103802' h1)). Qed.
