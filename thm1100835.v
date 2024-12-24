Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1100835_term_abbrevs.
Lemma lem1100835 {_25307 : Type'} (P : _25307 -> Prop) : (term0 _25307 P) = ((@List.Forall _25307 P (@nil _25307)) = True).
Proof. exact (eq_refl (term0 _25307 P)). Qed.
