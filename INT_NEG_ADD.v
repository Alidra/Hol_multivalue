Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NEG_ADD_term_abbrevs.
Require Import REAL_NEG_ADD_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306332 (x : int) : term0 x.
Proof. exact (@lem1361095 (real_of_int x)). Qed.
Lemma lem2306333 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306334 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2306333 x) (@lem2306332 x)). Qed.
Lemma lem2306335 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2306334 x (real_of_int y)). Qed.
Lemma lem2306336 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2306337 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2306336 x y) (@lem2306335 x y)). Qed.
Lemma lem2306339 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2306340 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2306341 (x : int) (y : int) : (term3 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2306340) (@lem2306339 x y)). Qed.
Lemma lem2306343 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306344 (x : int) (y : int) : (term7 x y) = (term10 x y).
Proof. exact (@lem2306343 (int_add x y)). Qed.
Lemma lem2306345 (x : int) (y : int) : (term3 x y) = (term10 x y).
Proof. exact (TRANS (@lem2306341 x y) (@lem2306344 x y)). Qed.
Lemma lem2306346 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306347 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2306346) (@lem2306345 x y)). Qed.
Lemma lem2306349 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306350 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2306351 (x : int) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem2306350) (@lem2306349 x)). Qed.
Lemma lem2306353 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306354 (y : int) : (term8 y) = (term9 y).
Proof. exact (@lem2306353 y). Qed.
Lemma lem2306355 (x : int) (y : int) : (term4 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem2306351 x) (@lem2306354 y)). Qed.
Lemma lem2306357 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2306358 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (@lem2306357 (int_neg x) (int_neg y)). Qed.
Lemma lem2306359 (x : int) (y : int) : (term4 x y) = (term16 x y).
Proof. exact (TRANS (@lem2306355 x y) (@lem2306358 x y)). Qed.
Lemma lem2306360 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term10 x y) = (term16 x y)).
Proof. exact (MK_COMB (@lem2306347 x y) (@lem2306359 x y)). Qed.
Lemma lem2306362 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306363 (x : int) (y : int) : ((term10 x y) = (term16 x y)) = ((term17 x y) = (term18 x y)).
Proof. exact (@lem2306362 (term17 x y) (term18 x y)). Qed.
Lemma lem2306364 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term17 x y) = (term18 x y)).
Proof. exact (TRANS (@lem2306360 x y) (@lem2306363 x y)). Qed.
Lemma lem2306365 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem2306364 x y) (@lem2306337 x y)). Qed.
Lemma lem2306366 (x : int) : term19 x.
Proof. exact (fun y : int => @lem2306365 x y). Qed.
Lemma lem2306367 : term20.
Proof. exact (fun x : int => @lem2306366 x). Qed.
