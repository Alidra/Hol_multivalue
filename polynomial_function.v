Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import polynomial_function_term_abbrevs.
Lemma lem7553449 : polynomial_function = term0.
Proof. exact (@polynomial_function_def). Qed.
Lemma lem7553450 (_97553 : real -> real) : _97553 = _97553.
Proof. exact (eq_refl _97553). Qed.
Lemma lem7553451 (_97553 : real -> real) : (polynomial_function _97553) = (term1 _97553).
Proof. exact (MK_COMB (@lem7553449) (@lem7553450 _97553)). Qed.
Lemma lem7553452 (_97553 : real -> real) : (term1 _97553) = (term2 _97553).
Proof. exact (eq_refl (term1 _97553)). Qed.
Lemma lem7553453 (_97553 : real -> real) : (polynomial_function _97553) = (term2 _97553).
Proof. exact (TRANS (@lem7553451 _97553) (@lem7553452 _97553)). Qed.
Lemma lem7553454 : term3.
Proof. exact (fun _97553 : real -> real => @lem7553453 _97553). Qed.
Lemma lem7553455 (_97553 : real -> real) : term4 _97553.
Proof. exact (@lem7553454 _97553). Qed.
Lemma lem7553456 (_97553 : real -> real) : (term4 _97553) = ((polynomial_function _97553) = (term2 _97553)).
Proof. exact (eq_refl (term4 _97553)). Qed.
Lemma lem7553457 (_97553 : real -> real) : (polynomial_function _97553) = (term2 _97553).
Proof. exact (EQ_MP (@lem7553456 _97553) (@lem7553455 _97553)). Qed.
Lemma lem7553487 (p : real -> real) : (polynomial_function p) = (term2 p).
Proof. exact (@lem7553457 p). Qed.
Lemma lem7553488 : term3.
Proof. exact (fun p : real -> real => @lem7553487 p). Qed.
