Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm9127_term_abbrevs.
Require Import ETA_AX_spec.
Lemma lem9122 {A B : Type'} (t : A -> B) : term0 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem9123 {A B : Type'} (t : A -> B) : (term0 A B t) = ((term1 A B t) = t).
Proof. exact (eq_refl (term0 A B t)). Qed.
Lemma lem9126 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (EQ_MP (@lem9123 A B t) (@lem9122 A B t)). Qed.
Lemma lem9127 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (@lem9126 A B t). Qed.
