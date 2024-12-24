Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_ABS_term_abbrevs.
Require Import REAL_ABS_ABS_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2299991 (x : int) : term0 x.
Proof. exact (@lem1535666 (real_of_int x)). Qed.
Lemma lem2299992 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2299993 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2299992 x) (@lem2299991 x)). Qed.
Lemma lem2299995 (x : int) : (term2 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2299996 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2299997 (x : int) : (term1 x) = (term4 x).
Proof. exact (MK_COMB (@lem2299996) (@lem2299995 x)). Qed.
Lemma lem2299999 (x : int) : (term2 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300000 (x : int) : (term4 x) = (term5 x).
Proof. exact (@lem2299999 (int_abs x)). Qed.
Lemma lem2300001 (x : int) : (term1 x) = (term5 x).
Proof. exact (TRANS (@lem2299997 x) (@lem2300000 x)). Qed.
Lemma lem2300002 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2300003 (x : int) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem2300002) (@lem2300001 x)). Qed.
Lemma lem2300005 (x : int) : (term2 x) = (term3 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300006 (x : int) : ((term1 x) = (term2 x)) = ((term5 x) = (term3 x)).
Proof. exact (MK_COMB (@lem2300003 x) (@lem2300005 x)). Qed.
Lemma lem2300008 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2300009 (x : int) : ((term5 x) = (term3 x)) = ((term8 x) = (int_abs x)).
Proof. exact (@lem2300008 (term8 x) (int_abs x)). Qed.
Lemma lem2300010 (x : int) : ((term1 x) = (term2 x)) = ((term8 x) = (int_abs x)).
Proof. exact (TRANS (@lem2300006 x) (@lem2300009 x)). Qed.
Lemma lem2300011 (x : int) : (term8 x) = (int_abs x).
Proof. exact (EQ_MP (@lem2300010 x) (@lem2299993 x)). Qed.
Lemma lem2300012 : term9.
Proof. exact (fun x : int => @lem2300011 x). Qed.
