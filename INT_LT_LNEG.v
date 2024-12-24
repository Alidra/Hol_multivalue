Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_LNEG_term_abbrevs.
Require Import REAL_LT_LNEG_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Lemma lem2304245 (x : int) : term0 x.
Proof. exact (@lem1502191 (real_of_int x)). Qed.
Lemma lem2304246 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2304247 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2304246 x) (@lem2304245 x)). Qed.
Lemma lem2304248 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2304247 x (real_of_int y)). Qed.
Lemma lem2304249 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2304250 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2304249 x y) (@lem2304248 x y)). Qed.
Lemma lem2304252 (x : int) : (term5 x) = (term6 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2304253 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304254 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem2304253) (@lem2304252 x)). Qed.
Lemma lem2304255 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2304256 (x : int) (y : int) : (term3 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2304254 x) (@lem2304255 y)). Qed.
Lemma lem2304258 (x : int) (y : int) : (term10 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304259 (x : int) (y : int) : (term9 x y) = (term11 x y).
Proof. exact (@lem2304258 (int_neg x) y). Qed.
Lemma lem2304260 (x : int) (y : int) : (term3 x y) = (term11 x y).
Proof. exact (TRANS (@lem2304256 x y) (@lem2304259 x y)). Qed.
Lemma lem2304261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2304262 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2304261) (@lem2304260 x y)). Qed.
Lemma lem2304264 (n : nat) : (real_of_num n) = (term14 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2304265 : term15 = term16.
Proof. exact (@lem2304264 (NUMERAL 0)). Qed.
Lemma lem2304266 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2304267 : term17 = term18.
Proof. exact (MK_COMB (@lem2304266) (@lem2304265)). Qed.
Lemma lem2304269 (x : int) (y : int) : (term19 x y) = (term20 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2304270 (x : int) (y : int) : (term4 x y) = (term21 x y).
Proof. exact (MK_COMB (@lem2304267) (@lem2304269 x y)). Qed.
Lemma lem2304272 (x : int) (y : int) : (term10 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2304273 (x : int) (y : int) : (term21 x y) = (term22 x y).
Proof. exact (@lem2304272 term23 (int_add x y)). Qed.
Lemma lem2304274 (x : int) (y : int) : (term4 x y) = (term22 x y).
Proof. exact (TRANS (@lem2304270 x y) (@lem2304273 x y)). Qed.
Lemma lem2304275 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term11 x y) = (term22 x y)).
Proof. exact (MK_COMB (@lem2304262 x y) (@lem2304274 x y)). Qed.
Lemma lem2304276 (x : int) (y : int) : (term11 x y) = (term22 x y).
Proof. exact (EQ_MP (@lem2304275 x y) (@lem2304250 x y)). Qed.
Lemma lem2304277 (x : int) : term24 x.
Proof. exact (fun y : int => @lem2304276 x y). Qed.
Lemma lem2304278 : term25.
Proof. exact (fun x : int => @lem2304277 x). Qed.
