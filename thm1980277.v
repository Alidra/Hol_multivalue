Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1980277_term_abbrevs.
Require Import IMP_CONJ_spec.
Require Import RAT_LEMMA5_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Require Import thm892_spec.
Lemma lem1980268 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term0 x1 y2 x2 y1) = ((term0 x1 y2 x2 y1) = True).
Proof. exact (@lem7 (term0 x1 y2 x2 y1)). Qed.
Lemma lem1980271 (p : Prop) (q : Prop) (r : Prop) : (term1 p q r) = (term2 p q r).
Proof. exact (EQ_MP (@lem892 p q r) (@lem887 p q r)). Qed.
Lemma lem1980272 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term3 x1 y2 x2 y1) = (term0 x1 y2 x2 y1).
Proof. exact (@lem1980271 (term4 y1) (term4 y2) (((real_div x1 y1) = (real_div x2 y2)) = ((real_mul x1 y2) = (real_mul x2 y1)))). Qed.
Lemma lem1980274 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term0 x1 y2 x2 y1) = True.
Proof. exact (EQ_MP (@lem1980268 x1 y2 x2 y1) (@lem1979881 x1 y2 x2 y1)). Qed.
Lemma lem1980275 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : (term3 x1 y2 x2 y1) = True.
Proof. exact (TRANS (@lem1980272 x1 y2 x2 y1) (@lem1980274 x1 y2 x2 y1)). Qed.
Lemma lem1980276 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : True = (term3 x1 y2 x2 y1).
Proof. exact (SYM (@lem1980275 x1 y2 x2 y1)). Qed.
Lemma lem1980277 (x1 : real) (y2 : real) (x2 : real) (y1 : real) : term3 x1 y2 x2 y1.
Proof. exact (EQ_MP (@lem1980276 x1 y2 x2 y1) (@lem0)). Qed.
