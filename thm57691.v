Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm57691_term_abbrevs.
Require Import LET_DEF_spec.
Lemma lem57688 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem44133 A B f). Qed.
Lemma lem57689 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem57690 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem57689 A B f) (@lem57688 A B f)). Qed.
Lemma lem57691 {A B : Type'} (f : A -> B) (x : A) : term2 A B f x.
Proof. exact (@lem57690 A B f x). Qed.
