Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ADD_SUB2_term_abbrevs.
Require Import REAL_ADD_SUB2_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301273 (x : int) : term0 x.
Proof. exact (@lem1523449 (real_of_int x)). Qed.
Lemma lem2301274 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301275 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301274 x) (@lem2301273 x)). Qed.
Lemma lem2301276 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301275 x (real_of_int y)). Qed.
Lemma lem2301277 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301278 (x : int) (y : int) : (term3 x y) = (term4 y).
Proof. exact (EQ_MP (@lem2301277 x y) (@lem2301276 x y)). Qed.
Lemma lem2301280 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301281 (x : int) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2301282 (x : int) (y : int) : (term3 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2301281 x) (@lem2301280 x y)). Qed.
Lemma lem2301284 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2301285 (x : int) (y : int) : (term8 x y) = (term11 x y).
Proof. exact (@lem2301284 x (int_add x y)). Qed.
Lemma lem2301286 (x : int) (y : int) : (term3 x y) = (term11 x y).
Proof. exact (TRANS (@lem2301282 x y) (@lem2301285 x y)). Qed.
Lemma lem2301287 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301288 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2301287) (@lem2301286 x y)). Qed.
Lemma lem2301290 (x : int) : (term4 x) = (term14 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2301291 (y : int) : (term4 y) = (term14 y).
Proof. exact (@lem2301290 y). Qed.
Lemma lem2301292 (x : int) (y : int) : ((term3 x y) = (term4 y)) = ((term11 x y) = (term14 y)).
Proof. exact (MK_COMB (@lem2301288 x y) (@lem2301291 y)). Qed.
Lemma lem2301294 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301295 (x : int) (y : int) : ((term11 x y) = (term14 y)) = ((term15 x y) = (int_neg y)).
Proof. exact (@lem2301294 (term15 x y) (int_neg y)). Qed.
Lemma lem2301296 (x : int) (y : int) : ((term3 x y) = (term4 y)) = ((term15 x y) = (int_neg y)).
Proof. exact (TRANS (@lem2301292 x y) (@lem2301295 x y)). Qed.
Lemma lem2301297 (x : int) (y : int) : (term15 x y) = (int_neg y).
Proof. exact (EQ_MP (@lem2301296 x y) (@lem2301278 x y)). Qed.
Lemma lem2301298 (x : int) : term16 x.
Proof. exact (fun y : int => @lem2301297 x y). Qed.
Lemma lem2301299 : term17.
Proof. exact (fun x : int => @lem2301298 x). Qed.
