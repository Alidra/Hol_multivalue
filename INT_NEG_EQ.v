Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NEG_EQ_term_abbrevs.
Require Import REAL_NEG_EQ_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306368 (x : int) : term0 x.
Proof. exact (@lem1508939 (real_of_int x)). Qed.
Lemma lem2306369 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306370 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2306369 x) (@lem2306368 x)). Qed.
Lemma lem2306371 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2306370 x (real_of_int y)). Qed.
Lemma lem2306372 (x : int) (y : int) : (term2 x y) = (((term3 x) = (real_of_int y)) = ((real_of_int x) = (term3 y))).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2306373 (x : int) (y : int) : ((term3 x) = (real_of_int y)) = ((real_of_int x) = (term3 y)).
Proof. exact (EQ_MP (@lem2306372 x y) (@lem2306371 x y)). Qed.
Lemma lem2306375 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306376 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306377 (x : int) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem2306376) (@lem2306375 x)). Qed.
Lemma lem2306378 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2306379 (x : int) (y : int) : ((term3 x) = (real_of_int y)) = ((term4 x) = (real_of_int y)).
Proof. exact (MK_COMB (@lem2306377 x) (@lem2306378 y)). Qed.
Lemma lem2306381 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306382 (x : int) (y : int) : ((term4 x) = (real_of_int y)) = ((int_neg x) = y).
Proof. exact (@lem2306381 (int_neg x) y). Qed.
Lemma lem2306383 (x : int) (y : int) : ((term3 x) = (real_of_int y)) = ((int_neg x) = y).
Proof. exact (TRANS (@lem2306379 x y) (@lem2306382 x y)). Qed.
Lemma lem2306384 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2306385 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2306384) (@lem2306383 x y)). Qed.
Lemma lem2306387 (x : int) : (term3 x) = (term4 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306388 (y : int) : (term3 y) = (term4 y).
Proof. exact (@lem2306387 y). Qed.
Lemma lem2306389 (x : int) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2306390 (x : int) (y : int) : ((real_of_int x) = (term3 y)) = ((real_of_int x) = (term4 y)).
Proof. exact (MK_COMB (@lem2306389 x) (@lem2306388 y)). Qed.
Lemma lem2306392 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306393 (x : int) (y : int) : ((real_of_int x) = (term4 y)) = (x = (int_neg y)).
Proof. exact (@lem2306392 x (int_neg y)). Qed.
Lemma lem2306394 (x : int) (y : int) : ((real_of_int x) = (term3 y)) = (x = (int_neg y)).
Proof. exact (TRANS (@lem2306390 x y) (@lem2306393 x y)). Qed.
Lemma lem2306395 (x : int) (y : int) : (((term3 x) = (real_of_int y)) = ((real_of_int x) = (term3 y))) = (((int_neg x) = y) = (x = (int_neg y))).
Proof. exact (MK_COMB (@lem2306385 x y) (@lem2306394 x y)). Qed.
Lemma lem2306396 (x : int) (y : int) : ((int_neg x) = y) = (x = (int_neg y)).
Proof. exact (EQ_MP (@lem2306395 x y) (@lem2306373 x y)). Qed.
Lemma lem2306397 (x : int) : term10 x.
Proof. exact (fun y : int => @lem2306396 x y). Qed.
Lemma lem2306398 : term11.
Proof. exact (fun x : int => @lem2306397 x). Qed.
