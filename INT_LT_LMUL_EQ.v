Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_LMUL_EQ_term_abbrevs.
Require Import REAL_LT_LMUL_EQ_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304200 (x : int) : term0 x.
Proof. exact (@lem1602653 (real_of_int x)). Qed.
Lemma lem2304201 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304202 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304201 x) (@lem2304200 x)). Qed.
Lemma lem2304203 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304202 x (real_of_int y)). Qed.
Lemma lem2304204 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304205 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2304204 x y) (@lem2304203 x y)). Qed.
Lemma lem2304206 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2304205 x y (real_of_int z)). Qed.
Lemma lem2304207 (z : int) (x : int) (y : int) : (term4 x y z) = (term5 z x y).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2304208 (z : int) (x : int) (y : int) : term5 z x y.
Proof. exact (EQ_MP (@lem2304207 z x y) (@lem2304206 x y z)). Qed.
Lemma lem2304210 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304211 : term7 = term8.
Proof. exact (@lem2304210 (NUMERAL 0)). Qed.
Lemma lem2304212 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304213 : term9 = term10.
Proof. exact (MK_COMB (@lem2304212) (@lem2304211)). Qed.
Lemma lem2304214 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2304215 (z : int) : (term11 z) = (term12 z).
Proof. exact (MK_COMB (@lem2304213) (@lem2304214 z)). Qed.
Lemma lem2304217 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304218 (z : int) : (term12 z) = (term14 z).
Proof. exact (@lem2304217 term15 z). Qed.
Lemma lem2304219 (z : int) : (term11 z) = (term14 z).
Proof. exact (TRANS (@lem2304215 z) (@lem2304218 z)). Qed.
Lemma lem2304220 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2304221 (z : int) : (term16 z) = (term17 z).
Proof. exact (MK_COMB (@lem2304220) (@lem2304219 z)). Qed.
Lemma lem2304223 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304224 (z : int) (x : int) : (term18 z x) = (term19 z x).
Proof. exact (@lem2304223 z x). Qed.
Lemma lem2304225 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304226 (z : int) (x : int) : (term20 z x) = (term21 z x).
Proof. exact (MK_COMB (@lem2304225) (@lem2304224 z x)). Qed.
Lemma lem2304228 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2304229 (z : int) (y : int) : (term18 z y) = (term19 z y).
Proof. exact (@lem2304228 z y). Qed.
Lemma lem2304230 (x : int) (z : int) (y : int) : (term22 x z y) = (term23 x z y).
Proof. exact (MK_COMB (@lem2304226 z x) (@lem2304229 z y)). Qed.
Lemma lem2304232 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304233 (x : int) (z : int) (y : int) : (term23 x z y) = (term24 x z y).
Proof. exact (@lem2304232 (int_mul z x) (int_mul z y)). Qed.
Lemma lem2304234 (x : int) (z : int) (y : int) : (term22 x z y) = (term24 x z y).
Proof. exact (TRANS (@lem2304230 x z y) (@lem2304233 x z y)). Qed.
Lemma lem2304235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2304236 (x : int) (z : int) (y : int) : (term25 x z y) = (term26 x z y).
Proof. exact (MK_COMB (@lem2304235) (@lem2304234 x z y)). Qed.
Lemma lem2304238 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304239 (z : int) (x : int) (y : int) : ((term22 x z y) = (term13 x y)) = ((term24 x z y) = (int_lt x y)).
Proof. exact (MK_COMB (@lem2304236 x z y) (@lem2304238 x y)). Qed.
Lemma lem2304240 (z : int) (x : int) (y : int) : (term5 z x y) = (term27 z x y).
Proof. exact (MK_COMB (@lem2304221 z) (@lem2304239 z x y)). Qed.
Lemma lem2304241 (z : int) (x : int) (y : int) : term27 z x y.
Proof. exact (EQ_MP (@lem2304240 z x y) (@lem2304208 z x y)). Qed.
Lemma lem2304242 (x : int) (y : int) : term28 x y.
Proof. exact (fun z : int => @lem2304241 z x y). Qed.
Lemma lem2304243 (x : int) : term29 x.
Proof. exact (fun y : int => @lem2304242 x y). Qed.
Lemma lem2304244 : term30.
Proof. exact (fun x : int => @lem2304243 x). Qed.
