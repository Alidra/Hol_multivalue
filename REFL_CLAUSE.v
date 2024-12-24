Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REFL_CLAUSE_term_abbrevs.
Require Import EQ_REFL_spec.
Require Import thm7_spec.
Lemma lem305 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem304 A x). Qed.
Lemma lem306 {A : Type'} (x : A) : (term0 A x) = (x = x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem307 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem306 A x) (@lem305 A x)). Qed.
Lemma lem308 {A : Type'} (x : A) : (x = x) = ((x = x) = True).
Proof. exact (@lem7 (x = x)). Qed.
Lemma lem311 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem308 A x) (@lem307 A x)). Qed.
Lemma lem312 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem311 A x). Qed.
Lemma lem317 {A : Type'} : term1 A.
Proof. exact (fun x : A => @lem312 A x). Qed.
