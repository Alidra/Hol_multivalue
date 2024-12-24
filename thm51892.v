Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm51892_term_abbrevs.
Require Import FUN_EQ_THM_spec.
Lemma lem51889 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem51890 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem51891 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem51890 A B f) (@lem51889 A B f)). Qed.
Lemma lem51892 {A B : Type'} (f : A -> B) (g : A -> B) : term2 A B f g.
Proof. exact (@lem51891 A B f g). Qed.
