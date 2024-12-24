Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_TOTAL_term_abbrevs.
Require Import REAL_LT_TOTAL_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2305042 (x : int) : term0 x.
Proof. exact (@lem1498801 (real_of_int x)). Qed.
Lemma lem2305043 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305044 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305043 x) (@lem2305042 x)). Qed.
Lemma lem2305045 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305044 x (real_of_int y)). Qed.
Lemma lem2305046 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305047 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2305046 y x) (@lem2305045 x y)). Qed.
Lemma lem2305049 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2305051 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem2305050) (@lem2305049 x y)). Qed.
Lemma lem2305053 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2305054 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2305055 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2305054) (@lem2305053 x y)). Qed.
Lemma lem2305057 (x : int) (y : int) : (term6 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2305058 (y : int) (x : int) : (term6 y x) = (int_lt y x).
Proof. exact (@lem2305057 y x). Qed.
Lemma lem2305059 (y : int) (x : int) : (term9 y x) = (term10 y x).
Proof. exact (MK_COMB (@lem2305055 x y) (@lem2305058 y x)). Qed.
Lemma lem2305060 (y : int) (x : int) : (term3 y x) = (term11 y x).
Proof. exact (MK_COMB (@lem2305051 x y) (@lem2305059 y x)). Qed.
Lemma lem2305061 (y : int) (x : int) : term11 y x.
Proof. exact (EQ_MP (@lem2305060 y x) (@lem2305047 y x)). Qed.
Lemma lem2305062 (x : int) : term12 x.
Proof. exact (fun y : int => @lem2305061 y x). Qed.
Lemma lem2305063 : term13.
Proof. exact (fun x : int => @lem2305062 x). Qed.
