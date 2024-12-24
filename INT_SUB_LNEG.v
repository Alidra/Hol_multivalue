Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_LNEG_term_abbrevs.
Require Import REAL_SUB_LNEG_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2310220 (x : int) : term0 x.
Proof. exact (@lem1519277 (real_of_int x)). Qed.
Lemma lem2310221 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2310222 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2310221 x) (@lem2310220 x)). Qed.
Lemma lem2310223 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2310222 x (real_of_int y)). Qed.
Lemma lem2310224 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2310225 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2310224 x y) (@lem2310223 x y)). Qed.
Lemma lem2310227 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2310228 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2310229 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2310228) (@lem2310227 x)). Qed.
Lemma lem2310230 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2310231 (x : int) (y : int) : (term3 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2310229 x) (@lem2310230 y)). Qed.
Lemma lem2310233 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310234 (x : int) (y : int) : (term9 x y) = (term12 x y).
Proof. exact (@lem2310233 (int_neg x) y). Qed.
Lemma lem2310235 (x : int) (y : int) : (term3 x y) = (term12 x y).
Proof. exact (TRANS (@lem2310231 x y) (@lem2310234 x y)). Qed.
Lemma lem2310236 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2310237 (x : int) (y : int) : (term13 x y) = (term14 x y).
Proof. exact (MK_COMB (@lem2310236) (@lem2310235 x y)). Qed.
Lemma lem2310239 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2310240 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2310241 (x : int) (y : int) : (term4 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem2310240) (@lem2310239 x y)). Qed.
Lemma lem2310243 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2310244 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (@lem2310243 (int_add x y)). Qed.
Lemma lem2310245 (x : int) (y : int) : (term4 x y) = (term18 x y).
Proof. exact (TRANS (@lem2310241 x y) (@lem2310244 x y)). Qed.
Lemma lem2310246 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term12 x y) = (term18 x y)).
Proof. exact (MK_COMB (@lem2310237 x y) (@lem2310245 x y)). Qed.
Lemma lem2310248 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310249 (x : int) (y : int) : ((term12 x y) = (term18 x y)) = ((term19 x y) = (term20 x y)).
Proof. exact (@lem2310248 (term19 x y) (term20 x y)). Qed.
Lemma lem2310250 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term19 x y) = (term20 x y)).
Proof. exact (TRANS (@lem2310246 x y) (@lem2310249 x y)). Qed.
Lemma lem2310251 (x : int) (y : int) : (term19 x y) = (term20 x y).
Proof. exact (EQ_MP (@lem2310250 x y) (@lem2310225 x y)). Qed.
Lemma lem2310252 (x : int) : term21 x.
Proof. exact (fun y : int => @lem2310251 x y). Qed.
Lemma lem2310253 : term22.
Proof. exact (fun x : int => @lem2310252 x). Qed.
