Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_RNEG_term_abbrevs.
Require Import REAL_LE_RNEG_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303248 (x : int) : term0 x.
Proof. exact (@lem1362465 (real_of_int x)). Qed.
Lemma lem2303249 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303250 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303249 x) (@lem2303248 x)). Qed.
Lemma lem2303251 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303250 x (real_of_int y)). Qed.
Lemma lem2303252 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303253 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2303252 x y) (@lem2303251 x y)). Qed.
Lemma lem2303255 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2303256 (y : int) : (term5 y) = (term6 y).
Proof. exact (@lem2303255 y). Qed.
Lemma lem2303257 (x : int) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2303258 (x : int) (y : int) : (term3 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2303257 x) (@lem2303256 y)). Qed.
Lemma lem2303260 (x : int) (y : int) : (term9 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303261 (x : int) (y : int) : (term8 x y) = (term10 x y).
Proof. exact (@lem2303260 x (int_neg y)). Qed.
Lemma lem2303262 (x : int) (y : int) : (term3 x y) = (term10 x y).
Proof. exact (TRANS (@lem2303258 x y) (@lem2303261 x y)). Qed.
Lemma lem2303263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2303264 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2303263) (@lem2303262 x y)). Qed.
Lemma lem2303266 (x : int) (y : int) : (term13 x y) = (term14 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303267 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2303268 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (MK_COMB (@lem2303267) (@lem2303266 x y)). Qed.
Lemma lem2303270 (n : nat) : (real_of_num n) = (term17 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303271 : term18 = term19.
Proof. exact (@lem2303270 (NUMERAL 0)). Qed.
Lemma lem2303272 (x : int) (y : int) : (term4 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem2303268 x y) (@lem2303271)). Qed.
Lemma lem2303274 (x : int) (y : int) : (term9 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303275 (x : int) (y : int) : (term20 x y) = (term21 x y).
Proof. exact (@lem2303274 (int_add x y) term22). Qed.
Lemma lem2303276 (x : int) (y : int) : (term4 x y) = (term21 x y).
Proof. exact (TRANS (@lem2303272 x y) (@lem2303275 x y)). Qed.
Lemma lem2303277 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term10 x y) = (term21 x y)).
Proof. exact (MK_COMB (@lem2303264 x y) (@lem2303276 x y)). Qed.
Lemma lem2303278 (x : int) (y : int) : (term10 x y) = (term21 x y).
Proof. exact (EQ_MP (@lem2303277 x y) (@lem2303253 x y)). Qed.
Lemma lem2303279 (x : int) : term23 x.
Proof. exact (fun y : int => @lem2303278 x y). Qed.
Lemma lem2303280 : term24.
Proof. exact (fun x : int => @lem2303279 x). Qed.
