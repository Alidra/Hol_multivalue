Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3117515_term_abbrevs.
Require Import RIGHT_IMP_FORALL_THM_spec.
Lemma lem3117512 {A : Type'} (P : Prop) : term0 A P.
Proof. exact (@lem6418 A P). Qed.
Lemma lem3117513 {A : Type'} (P : Prop) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem3117514 {A : Type'} (P : Prop) : term1 A P.
Proof. exact (EQ_MP (@lem3117513 A P) (@lem3117512 A P)). Qed.
Lemma lem3117515 {A : Type'} (P : Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem3117514 A P Q). Qed.
