Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1980026_term_abbrevs.
Require Import IMP_CONJ_spec.
Require Import RAT_LEMMA4_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm892_spec.
Lemma lem1980017 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term0 x1 y2 x2 y1) = ((term0 x1 y2 x2 y1) = True).
Proof. exact (@lem7 (term0 x1 y2 x2 y1)). Qed.
Lemma lem1980020 (p : Prop) (q : Prop) (r : Prop) : (term1 p q r) = (term2 p q r).
Proof. exact (EQ_MP (@lem892 p q r) (@lem887 p q r)). Qed.
Lemma lem1980021 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term3 x1 y2 x2 y1) = (term0 x1 y2 x2 y1).
Proof. exact (@lem1980020 (term4 y1) (term4 y2) ((term5 x1 y1 x2 y2) = (term6 x1 y2 x2 y1))). Qed.
Lemma lem1980023 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term0 x1 y2 x2 y1) = True.
Proof. exact (EQ_MP (@lem1980017 x1 y2 x2 y1) (@lem1979407 x1 y2 x2 y1)). Qed.
Lemma lem1980024 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term3 x1 y2 x2 y1) = True.
Proof. exact (TRANS (@lem1980021 x1 y2 x2 y1) (@lem1980023 x1 y2 x2 y1)). Qed.
Lemma lem1980025 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : True = (term3 x1 y2 x2 y1).
Proof. exact (SYM (@lem1980024 x1 y2 x2 y1)). Qed.
Lemma lem1980026 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : term3 x1 y2 x2 y1.
Proof. exact (EQ_MP (@lem1980025 x1 y2 x2 y1) (@lem0)). Qed.
