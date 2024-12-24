Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MUL_LNEG_term_abbrevs.
Require Import REAL_MUL_LNEG_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2305982 (x : int) : term0 x.
Proof. exact (@lem1360913 (real_of_int x)). Qed.
Lemma lem2305983 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305984 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305983 x) (@lem2305982 x)). Qed.
Lemma lem2305985 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305984 x (real_of_int y)). Qed.
Lemma lem2305986 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305987 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2305986 x y) (@lem2305985 x y)). Qed.
Lemma lem2305989 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2305990 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2305991 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2305990) (@lem2305989 x)). Qed.
Lemma lem2305992 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2305993 (x : int) (y : int) : (term3 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2305991 x) (@lem2305992 y)). Qed.
Lemma lem2305995 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305996 (x : int) (y : int) : (term9 x y) = (term12 x y).
Proof. exact (@lem2305995 (int_neg x) y). Qed.
Lemma lem2305997 (x : int) (y : int) : (term3 x y) = (term12 x y).
Proof. exact (TRANS (@lem2305993 x y) (@lem2305996 x y)). Qed.
Lemma lem2305998 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305999 (x : int) (y : int) : (term13 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem2305998) (@lem2305997 x y)). Qed.
Lemma lem2306001 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306002 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2306003 (x : int) (y : int) : (term4 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem2306002) (@lem2306001 x y)). Qed.
Lemma lem2306005 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306006 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (@lem2306005 (int_mul x y)). Qed.
Lemma lem2306007 (x : int) (y : int) : (term4 x y) = (term16 x y).
Proof. exact (TRANS (@lem2306003 x y) (@lem2306006 x y)). Qed.
Lemma lem2306008 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term12 x y) = (term16 x y)).
Proof. exact (MK_COMB (@lem2305999 x y) (@lem2306007 x y)). Qed.
Lemma lem2306010 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306011 (x : int) (y : int) : ((term12 x y) = (term16 x y)) = ((term17 x y) = (term18 x y)).
Proof. exact (@lem2306010 (term17 x y) (term18 x y)). Qed.
Lemma lem2306012 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term17 x y) = (term18 x y)).
Proof. exact (TRANS (@lem2306008 x y) (@lem2306011 x y)). Qed.
Lemma lem2306013 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem2306012 x y) (@lem2305987 x y)). Qed.
Lemma lem2306014 (x : int) : term19 x.
Proof. exact (fun y : int => @lem2306013 x y). Qed.
Lemma lem2306015 : term20.
Proof. exact (fun x : int => @lem2306014 x). Qed.
