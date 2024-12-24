Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_REFL_term_abbrevs.
Require Import REAL_SUB_REFL_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2310380 (x : int) : term0 x.
Proof. exact (@lem1505261 (real_of_int x)). Qed.
Lemma lem2310381 (x : int) : (term0 x) = ((term1 x) = term2).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2310382 (x : int) : (term1 x) = term2.
Proof. exact (EQ_MP (@lem2310381 x) (@lem2310380 x)). Qed.
Lemma lem2310384 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310385 (x : int) : (term1 x) = (term5 x).
Proof. exact (@lem2310384 x x). Qed.
Lemma lem2310386 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2310387 (x : int) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem2310386) (@lem2310385 x)). Qed.
Lemma lem2310389 (n : nat) : (real_of_num n) = (term8 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2310390 : term2 = term9.
Proof. exact (@lem2310389 (NUMERAL 0)). Qed.
Lemma lem2310391 (x : int) : ((term1 x) = term2) = ((term5 x) = term9).
Proof. exact (MK_COMB (@lem2310387 x) (@lem2310390)). Qed.
Lemma lem2310393 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310394 (x : int) : ((term5 x) = term9) = ((int_sub x x) = term10).
Proof. exact (@lem2310393 (int_sub x x) term10). Qed.
Lemma lem2310395 (x : int) : ((term1 x) = term2) = ((int_sub x x) = term10).
Proof. exact (TRANS (@lem2310391 x) (@lem2310394 x)). Qed.
Lemma lem2310396 (x : int) : (int_sub x x) = term10.
Proof. exact (EQ_MP (@lem2310395 x) (@lem2310382 x)). Qed.
Lemma lem2310397 : term11.
Proof. exact (fun x : int => @lem2310396 x). Qed.
