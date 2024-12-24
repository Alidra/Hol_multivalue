Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_NEG_term_abbrevs.
Require Import REAL_ABS_NEG_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2300431 (x : int) : term0 x.
Proof. exact (@lem1365032 (real_of_int x)). Qed.
Lemma lem2300432 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300433 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2300432 x) (@lem2300431 x)). Qed.
Lemma lem2300435 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2300436 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300437 (x : int) : (term1 x) = (term5 x).
Proof. exact (MK_COMB (@lem2300436) (@lem2300435 x)). Qed.
Lemma lem2300439 (x : int) : (term2 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300440 (x : int) : (term5 x) = (term7 x).
Proof. exact (@lem2300439 (int_neg x)). Qed.
Lemma lem2300441 (x : int) : (term1 x) = (term7 x).
Proof. exact (TRANS (@lem2300437 x) (@lem2300440 x)). Qed.
Lemma lem2300442 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2300443 (x : int) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem2300442) (@lem2300441 x)). Qed.
Lemma lem2300445 (x : int) : (term2 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300446 (x : int) : ((term1 x) = (term2 x)) = ((term7 x) = (term6 x)).
Proof. exact (MK_COMB (@lem2300443 x) (@lem2300445 x)). Qed.
Lemma lem2300448 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2300449 (x : int) : ((term7 x) = (term6 x)) = ((term10 x) = (int_abs x)).
Proof. exact (@lem2300448 (term10 x) (int_abs x)). Qed.
Lemma lem2300450 (x : int) : ((term1 x) = (term2 x)) = ((term10 x) = (int_abs x)).
Proof. exact (TRANS (@lem2300446 x) (@lem2300449 x)). Qed.
Lemma lem2300451 (x : int) : (term10 x) = (int_abs x).
Proof. exact (EQ_MP (@lem2300450 x) (@lem2300433 x)). Qed.
Lemma lem2300452 : term11.
Proof. exact (fun x : int => @lem2300451 x). Qed.
