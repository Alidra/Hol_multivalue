Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3211744_term_abbrevs.
Require Import PSUBSET_spec.
Lemma lem3211741 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3195125 A s). Qed.
Lemma lem3211742 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3211743 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3211742 A s) (@lem3211741 A s)). Qed.
Lemma lem3211744 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3211743 A s t). Qed.
