Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import GABS_DEF_term_abbrevs.
Lemma lem44140 {A : Type'} : (@GABS A) = (term0 A).
Proof. exact (@GABS_def A). Qed.
Lemma lem44141 {A : Type'} (P : A -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem44142 {A : Type'} (P : A -> Prop) : (@GABS A P) = (term1 A P).
Proof. exact (MK_COMB (@lem44140 A) (@lem44141 A P)). Qed.
Lemma lem44143 {A : Type'} (P : A -> Prop) : (term1 A P) = (@ε A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem44144 {A : Type'} (P : A -> Prop) : (@GABS A P) = (@ε A P).
Proof. exact (TRANS (@lem44142 A P) (@lem44143 A P)). Qed.
Lemma lem44145 {A : Type'} : term2 A.
Proof. exact (fun P : A -> Prop => @lem44144 A P). Qed.
