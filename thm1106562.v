Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1106562_term_abbrevs.
Require Import thm1106559_spec.
Lemma lem1106561 {_25594 : Type'} : term0 _25594.
Proof. exact (proj1 (@lem1106559 _25594)). Qed.
Lemma lem1106562 {_25594 : Type'} (P : _25594 -> Prop) : term1 _25594 P.
Proof. exact (@lem1106561 _25594 P). Qed.
