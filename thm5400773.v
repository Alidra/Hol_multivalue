Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm5400773_term_abbrevs.
Require Import thm82_spec.
Lemma lem5400773 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
