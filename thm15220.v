Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm15220_term_abbrevs.
Require Import thm14821_spec.
Require Import thm14995_spec.
Lemma lem15220 {_2963 : Type'} (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) (g : Prop) (h1 : g = True) : term0 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14821 _2963 t e g' t' e' g h1) (@lem14995 _2963 t e g' t' e')). Qed.
