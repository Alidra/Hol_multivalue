Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_term_abbrevs.
Lemma lem303006 {A : Type'} : (@WF A) = (term0 A).
Proof. exact (@WF_def A). Qed.
Lemma lem303007 {A : Type'} (_6760 : type1402 A) : _6760 = _6760.
Proof. exact (eq_refl _6760). Qed.
Lemma lem303008 {A : Type'} (_6760 : type1402 A) : (@WF A _6760) = (term1 A _6760).
Proof. exact (MK_COMB (@lem303006 A) (@lem303007 A _6760)). Qed.
Lemma lem303009 {A : Type'} (_6760 : type1402 A) : (term1 A _6760) = (term2 A _6760).
Proof. exact (eq_refl (term1 A _6760)). Qed.
Lemma lem303010 {A : Type'} (_6760 : type1402 A) : (@WF A _6760) = (term2 A _6760).
Proof. exact (TRANS (@lem303008 A _6760) (@lem303009 A _6760)). Qed.
Lemma lem303011 {A : Type'} : term3 A.
Proof. exact (fun _6760 : type1402 A => @lem303010 A _6760). Qed.
Lemma lem303012 {A : Type'} (_6760 : type1402 A) : term4 A _6760.
Proof. exact (@lem303011 A _6760). Qed.
Lemma lem303013 {A : Type'} (_6760 : type1402 A) : (term4 A _6760) = ((@WF A _6760) = (term2 A _6760)).
Proof. exact (eq_refl (term4 A _6760)). Qed.
Lemma lem303014 {A : Type'} (_6760 : type1402 A) : (@WF A _6760) = (term2 A _6760).
Proof. exact (EQ_MP (@lem303013 A _6760) (@lem303012 A _6760)). Qed.
Lemma lem303044 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term2 A lt2).
Proof. exact (@lem303014 A lt2). Qed.
Lemma lem303045 {A : Type'} : term3 A.
Proof. exact (fun lt2 : type1402 A => @lem303044 A lt2). Qed.
