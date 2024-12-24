Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ONTO_term_abbrevs.
Lemma lem68713 {A B : Type'} : (@ONTO A B) = (term0 A B).
Proof. exact (@ONTO_def A B). Qed.
Lemma lem68714 {A B : Type'} (_2069 : A -> B) : _2069 = _2069.
Proof. exact (eq_refl _2069). Qed.
Lemma lem68715 {A B : Type'} (_2069 : A -> B) : (@ONTO A B _2069) = (term1 A B _2069).
Proof. exact (MK_COMB (@lem68713 A B) (@lem68714 A B _2069)). Qed.
Lemma lem68716 {A B : Type'} (_2069 : A -> B) : (term1 A B _2069) = (term2 A B _2069).
Proof. exact (eq_refl (term1 A B _2069)). Qed.
Lemma lem68717 {A B : Type'} (_2069 : A -> B) : (@ONTO A B _2069) = (term2 A B _2069).
Proof. exact (TRANS (@lem68715 A B _2069) (@lem68716 A B _2069)). Qed.
Lemma lem68718 {A B : Type'} : term3 A B.
Proof. exact (fun _2069 : A -> B => @lem68717 A B _2069). Qed.
Lemma lem68719 {A B : Type'} (_2069 : A -> B) : term4 A B _2069.
Proof. exact (@lem68718 A B _2069). Qed.
Lemma lem68720 {A B : Type'} (_2069 : A -> B) : (term4 A B _2069) = ((@ONTO A B _2069) = (term2 A B _2069)).
Proof. exact (eq_refl (term4 A B _2069)). Qed.
Lemma lem68721 {A B : Type'} (_2069 : A -> B) : (@ONTO A B _2069) = (term2 A B _2069).
Proof. exact (EQ_MP (@lem68720 A B _2069) (@lem68719 A B _2069)). Qed.
Lemma lem68751 {A B : Type'} (f : A -> B) : (@ONTO A B f) = (term2 A B f).
Proof. exact (@lem68721 A B f). Qed.
Lemma lem68752 {A B : Type'} : term3 A B.
Proof. exact (fun f : A -> B => @lem68751 A B f). Qed.
