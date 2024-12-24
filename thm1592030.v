Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1592030_term_abbrevs.
Require Import thm0_spec.
Require Import thm1591986_spec.
Require Import thm1591987_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1592018 (x : real) : (term0 x) = x.
Proof. exact (EQ_MP (@lem1591987 x) (@lem1591986 x)). Qed.
Lemma lem1592019 : term1 = term2.
Proof. exact (@lem1592018 term2). Qed.
Lemma lem1592020 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1592021 : term3 = term4.
Proof. exact (MK_COMB (@lem1592020) (@lem1592019)). Qed.
Lemma lem1592022 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1592023 : (term1 = term2) = (term2 = term2).
Proof. exact (MK_COMB (@lem1592021) (@lem1592022)). Qed.
Lemma lem1592025 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1592026 (x : real) : (x = x) = True.
Proof. exact (@lem1592025 real x). Qed.
Lemma lem1592027 : (term2 = term2) = True.
Proof. exact (@lem1592026 term2). Qed.
Lemma lem1592028 : (term1 = term2) = True.
Proof. exact (TRANS (@lem1592023) (@lem1592027)). Qed.
Lemma lem1592029 : True = (term1 = term2).
Proof. exact (SYM (@lem1592028)). Qed.
Lemma lem1592030 : term1 = term2.
Proof. exact (EQ_MP (@lem1592029) (@lem0)). Qed.
