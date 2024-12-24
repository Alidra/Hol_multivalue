Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POLYNOMIAL_FUNCTION_I_term_abbrevs.
Require Import POLYNOMIAL_FUNCTION_ID_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem7555013 : term0 = (term0 = True).
Proof. exact (@lem7 term0). Qed.
Lemma lem7555016 {A : Type'} : (@I A) = (term1 A).
Proof. exact (@I_def A). Qed.
Lemma lem7555017 : (@I real) = term2.
Proof. exact (@lem7555016 real). Qed.
Lemma lem7555018 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7555019 : (polynomial_function (@I real)) = term0.
Proof. exact (MK_COMB (@lem7555018) (@lem7555017)). Qed.
Lemma lem7555021 : term0 = True.
Proof. exact (EQ_MP (@lem7555013) (@lem7555012)). Qed.
Lemma lem7555022 : (polynomial_function (@I real)) = True.
Proof. exact (TRANS (@lem7555019) (@lem7555021)). Qed.
Lemma lem7555023 : True = (polynomial_function (@I real)).
Proof. exact (SYM (@lem7555022)). Qed.
Lemma lem7555024 : polynomial_function (@I real).
Proof. exact (EQ_MP (@lem7555023) (@lem0)). Qed.
