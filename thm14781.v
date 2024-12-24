Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm14781_term_abbrevs.
Lemma lem14781 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : (term0 _2963 g t e g' t' e') = (term0 _2963 g t e g' t' e').
Proof. exact (eq_refl (term0 _2963 g t e g' t' e')). Qed.
