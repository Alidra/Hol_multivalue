Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183075_term_abbrevs.
Lemma lem3183075 {A : Type'} (p : A -> Prop) : (term0 A p) = ((@GSPEC A p) = p).
Proof. exact (eq_refl (term0 A p)). Qed.
