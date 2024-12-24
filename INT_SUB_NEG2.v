Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_NEG2_term_abbrevs.
Require Import REAL_SUB_NEG2_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2310306 (x : int) : term0 x.
Proof. exact (@lem1519804 (real_of_int x)). Qed.
Lemma lem2310307 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2310308 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2310307 x) (@lem2310306 x)). Qed.
Lemma lem2310309 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2310308 x (real_of_int y)). Qed.
Lemma lem2310310 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (term4 y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2310311 (y : int) (x : int) : (term3 x y) = (term4 y x).
Proof. exact (EQ_MP (@lem2310310 y x) (@lem2310309 x y)). Qed.
Lemma lem2310313 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2310314 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2310315 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2310314) (@lem2310313 x)). Qed.
Lemma lem2310317 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2310318 (y : int) : (term5 y) = (term6 y).
Proof. exact (@lem2310317 y). Qed.
Lemma lem2310319 (x : int) (y : int) : (term3 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2310315 x) (@lem2310318 y)). Qed.
Lemma lem2310321 (x : int) (y : int) : (term4 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310322 (x : int) (y : int) : (term9 x y) = (term11 x y).
Proof. exact (@lem2310321 (int_neg x) (int_neg y)). Qed.
Lemma lem2310323 (x : int) (y : int) : (term3 x y) = (term11 x y).
Proof. exact (TRANS (@lem2310319 x y) (@lem2310322 x y)). Qed.
Lemma lem2310324 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2310325 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2310324) (@lem2310323 x y)). Qed.
Lemma lem2310327 (x : int) (y : int) : (term4 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310328 (y : int) (x : int) : (term4 y x) = (term10 y x).
Proof. exact (@lem2310327 y x). Qed.
Lemma lem2310329 (y : int) (x : int) : ((term3 x y) = (term4 y x)) = ((term11 x y) = (term10 y x)).
Proof. exact (MK_COMB (@lem2310325 x y) (@lem2310328 y x)). Qed.
Lemma lem2310331 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310332 (y : int) (x : int) : ((term11 x y) = (term10 y x)) = ((term14 x y) = (int_sub y x)).
Proof. exact (@lem2310331 (term14 x y) (int_sub y x)). Qed.
Lemma lem2310333 (y : int) (x : int) : ((term3 x y) = (term4 y x)) = ((term14 x y) = (int_sub y x)).
Proof. exact (TRANS (@lem2310329 y x) (@lem2310332 y x)). Qed.
Lemma lem2310334 (y : int) (x : int) : (term14 x y) = (int_sub y x).
Proof. exact (EQ_MP (@lem2310333 y x) (@lem2310311 y x)). Qed.
Lemma lem2310335 (x : int) : term15 x.
Proof. exact (fun y : int => @lem2310334 y x). Qed.
Lemma lem2310336 : term16.
Proof. exact (fun x : int => @lem2310335 x). Qed.
