Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184746_term_abbrevs.
Require Import thm3184698_spec.
Lemma lem3184746 {_83064 : Type'} (P : type919 _83064) : term0 _83064 P.
Proof. exact (fun x : _83064 => @lem3184698 _83064 P x). Qed.
