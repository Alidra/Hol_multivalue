Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm15730_term_abbrevs.
Lemma lem15722 (r : Prop) : (term0 r) = ((term1 r) = r).
Proof. exact (@axiom_3 r). Qed.
Lemma lem15725 (r : Prop) : (term0 r) = r.
Proof. exact (eq_refl (term0 r)). Qed.
Lemma lem15726 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem15727 (r : Prop) : (term2 r) = (@eq Prop r).
Proof. exact (MK_COMB (@lem15726) (@lem15725 r)). Qed.
Lemma lem15728 (r : Prop) : ((term1 r) = r) = ((term1 r) = r).
Proof. exact (eq_refl ((term1 r) = r)). Qed.
Lemma lem15729 (r : Prop) : ((term0 r) = ((term1 r) = r)) = (r = ((term1 r) = r)).
Proof. exact (MK_COMB (@lem15727 r) (@lem15728 r)). Qed.
Lemma lem15730 (r : Prop) : r = ((term1 r) = r).
Proof. exact (EQ_MP (@lem15729 r) (@lem15722 r)). Qed.
