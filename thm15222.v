Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm15222_term_abbrevs.
Require Import thm14784_spec.
Require Import thm15219_spec.
Require Import thm15220_spec.
Lemma lem15222 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term0 _2963 g t e g' t' e'.
Proof. exact (or_elim (@lem14784 g) (fun h0 : g = True => @lem15220 _2963 t e g' t' e' g h0) (fun h0 : g = False => @lem15219 _2963 t e g' t' e' g h0)). Qed.
