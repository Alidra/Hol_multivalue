Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm307612_term_abbrevs.
Require Import WF_spec.
Lemma lem307554 {A : Type'} (lt2 : type1402 A) : term0 A lt2.
Proof. exact (@lem303045 A lt2). Qed.
Lemma lem307555 {A : Type'} (lt2 : type1402 A) : (term0 A lt2) = ((@WF A lt2) = (term1 A lt2)).
Proof. exact (eq_refl (term0 A lt2)). Qed.
Lemma lem307560 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term1 A lt2).
Proof. exact (EQ_MP (@lem307555 A lt2) (@lem307554 A lt2)). Qed.
Lemma lem307561 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term1 A lt2).
Proof. exact (@lem307560 A lt2). Qed.
Lemma lem307584 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem307585 {A : Type'} (lt2 : type1402 A) : (term2 A lt2) = (term3 A lt2).
Proof. exact (MK_COMB (@lem307584) (@lem307561 A lt2)). Qed.
Lemma lem307608 {A : Type'} (lt2 : type1402 A) : (term4 A lt2) = (term4 A lt2).
Proof. exact (eq_refl (term4 A lt2)). Qed.
Lemma lem307609 {A : Type'} (lt2 : type1402 A) : ((@WF A lt2) = (term4 A lt2)) = ((term1 A lt2) = (term4 A lt2)).
Proof. exact (MK_COMB (@lem307585 A lt2) (@lem307608 A lt2)). Qed.
Lemma lem307612 {A : Type'} (lt2 : type1402 A) : ((term1 A lt2) = (term4 A lt2)) = ((@WF A lt2) = (term4 A lt2)).
Proof. exact (SYM (@lem307609 A lt2)). Qed.
