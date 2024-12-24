Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3354637_term_abbrevs.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3354626 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3354627 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3354626 A s t). Qed.
Lemma lem3354628 {A : Type'} : ((@INTERS A (@EMPTY (A -> Prop))) = (@UNIV A)) = (term1 A).
Proof. exact (@lem3354627 A (@INTERS A (@EMPTY (A -> Prop))) (@UNIV A)). Qed.
Lemma lem3354637 {A : Type'} : (term1 A) = ((@INTERS A (@EMPTY (A -> Prop))) = (@UNIV A)).
Proof. exact (SYM (@lem3354628 A)). Qed.
