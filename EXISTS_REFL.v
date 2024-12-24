Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_REFL_term_abbrevs.
Lemma lem4357 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4358 {A : Type'} (a : A) : term0 A a.
Proof. exact (ex_intro (term1 A a) a (@lem4357 A a)). Qed.
Lemma lem4363 {A : Type'} : term2 A.
Proof. exact (fun a : A => @lem4358 A a). Qed.
