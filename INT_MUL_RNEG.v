Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MUL_RNEG_term_abbrevs.
Require Import REAL_MUL_RNEG_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306234 (x : int) : term0 x.
Proof. exact (@lem1360282 (real_of_int x)). Qed.
Lemma lem2306235 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306236 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2306235 x) (@lem2306234 x)). Qed.
Lemma lem2306237 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2306236 x (real_of_int y)). Qed.
Lemma lem2306238 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2306239 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2306238 x y) (@lem2306237 x y)). Qed.
Lemma lem2306241 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306242 (y : int) : (term5 y) = (term6 y).
Proof. exact (@lem2306241 y). Qed.
Lemma lem2306243 (x : int) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2306244 (x : int) (y : int) : (term3 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2306243 x) (@lem2306242 y)). Qed.
Lemma lem2306246 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306247 (x : int) (y : int) : (term8 x y) = (term11 x y).
Proof. exact (@lem2306246 x (int_neg y)). Qed.
Lemma lem2306248 (x : int) (y : int) : (term3 x y) = (term11 x y).
Proof. exact (TRANS (@lem2306244 x y) (@lem2306247 x y)). Qed.
Lemma lem2306249 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306250 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2306249) (@lem2306248 x y)). Qed.
Lemma lem2306252 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306253 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2306254 (x : int) (y : int) : (term4 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem2306253) (@lem2306252 x y)). Qed.
Lemma lem2306256 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306257 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (@lem2306256 (int_mul x y)). Qed.
Lemma lem2306258 (x : int) (y : int) : (term4 x y) = (term15 x y).
Proof. exact (TRANS (@lem2306254 x y) (@lem2306257 x y)). Qed.
Lemma lem2306259 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term11 x y) = (term15 x y)).
Proof. exact (MK_COMB (@lem2306250 x y) (@lem2306258 x y)). Qed.
Lemma lem2306261 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306262 (x : int) (y : int) : ((term11 x y) = (term15 x y)) = ((term16 x y) = (term17 x y)).
Proof. exact (@lem2306261 (term16 x y) (term17 x y)). Qed.
Lemma lem2306263 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term16 x y) = (term17 x y)).
Proof. exact (TRANS (@lem2306259 x y) (@lem2306262 x y)). Qed.
Lemma lem2306264 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem2306263 x y) (@lem2306239 x y)). Qed.
Lemma lem2306265 (x : int) : term18 x.
Proof. exact (fun y : int => @lem2306264 x y). Qed.
Lemma lem2306266 : term19.
Proof. exact (fun x : int => @lem2306265 x). Qed.
