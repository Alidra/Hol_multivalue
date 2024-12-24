Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3183071_term_abbrevs.
Require Import FUN_EQ_THM_spec.
Lemma lem3183068 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem3183069 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem3183070 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem3183069 A B f) (@lem3183068 A B f)). Qed.
Lemma lem3183071 {A B : Type'} (f : A -> B) (g : A -> B) : term2 A B f g.
Proof. exact (@lem3183070 A B f g). Qed.
