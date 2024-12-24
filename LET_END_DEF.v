Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LET_END_DEF_term_abbrevs.
Lemma lem44134 {A : Type'} : (@LET_END A) = (term0 A).
Proof. exact (@LET_END_def A). Qed.
Lemma lem44135 {A : Type'} (t : A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem44136 {A : Type'} (t : A) : (@LET_END A t) = (term1 A t).
Proof. exact (MK_COMB (@lem44134 A) (@lem44135 A t)). Qed.
Lemma lem44137 {A : Type'} (t : A) : (term1 A t) = t.
Proof. exact (eq_refl (term1 A t)). Qed.
Lemma lem44138 {A : Type'} (t : A) : (@LET_END A t) = t.
Proof. exact (TRANS (@lem44136 A t) (@lem44137 A t)). Qed.
Lemma lem44139 {A : Type'} : term2 A.
Proof. exact (fun t : A => @lem44138 A t). Qed.
