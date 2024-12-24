Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184698_term_abbrevs.
Require Import thm3183120_spec.
Require Import thm3184694_spec.
Lemma lem3184698 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term0 _83064 x P) = (term1 _83064 P x).
Proof. exact (EQ_MP (@lem3183120 _83064 P x) (@lem3184694 _83064 P x)). Qed.
