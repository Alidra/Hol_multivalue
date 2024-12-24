Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7925099_term_abbrevs.
Require Import thm7925098_spec.
Lemma lem7925099 {A : Type'} (tybit0' : type1331 A) (_103783' : type45 A) (h1 : tybit0' = (term0 A _103783')) : term1 A tybit0' _103783'.
Proof. exact (proj2 (@lem7925098 A tybit0' _103783' h1)). Qed.
