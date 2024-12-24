Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7928454_term_abbrevs.
Require Import thm7928437_spec.
Lemma lem7928453 {A : Type'} (r : type1675 A) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem7928454 {A : Type'} (r : type1675 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term0 A)) (h2 : tybit1' = (term1 A _103802')) : (tybit1' r) = (term2 A r).
Proof. exact (MK_COMB (@lem7928437 A tybit1' _103802' h1 h2) (@lem7928453 A r)). Qed.
