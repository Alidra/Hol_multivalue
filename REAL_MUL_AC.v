Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MUL_AC_term_abbrevs.
Require Import thm1338712_spec.
Require Import thm1338912_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem1486247 (x : real) : term0 x.
Proof. exact (@lem1338712 x). Qed.
Lemma lem1486248 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1486249 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1486248 x) (@lem1486247 x)). Qed.
Lemma lem1486250 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1486249 x y). Qed.
Lemma lem1486251 (y : real) (x : real) : (term2 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1486252 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1486251 y x) (@lem1486250 x y)). Qed.
Lemma lem1486253 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = (((real_mul x y) = (real_mul y x)) = True).
Proof. exact (@lem7 ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1486255 (x : real) : term3 x.
Proof. exact (@lem1338912 x). Qed.
Lemma lem1486256 (x : real) : (term3 x) = (term4 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1486257 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem1486256 x) (@lem1486255 x)). Qed.
Lemma lem1486258 (x : real) (y : real) : term5 x y.
Proof. exact (@lem1486257 x y). Qed.
Lemma lem1486259 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1486260 (x : real) (y : real) : term6 x y.
Proof. exact (EQ_MP (@lem1486259 x y) (@lem1486258 x y)). Qed.
Lemma lem1486261 (x : real) (y : real) (z : real) : term7 x y z.
Proof. exact (@lem1486260 x y z). Qed.
Lemma lem1486262 (x : real) (y : real) (z : real) : (term7 x y z) = ((term8 x y z) = (term9 x y z)).
Proof. exact (eq_refl (term7 x y z)). Qed.
Lemma lem1486267 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = True.
Proof. exact (EQ_MP (@lem1486253 y x) (@lem1486252 y x)). Qed.
Lemma lem1486268 (n : real) (m : real) : ((real_mul m n) = (real_mul n m)) = True.
Proof. exact (@lem1486267 n m). Qed.
Lemma lem1486269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1486270 (n : real) (m : real) : (term10 n m) = (and True).
Proof. exact (MK_COMB (@lem1486269) (@lem1486268 n m)). Qed.
Lemma lem1486278 (x : real) (y : real) (z : real) : (term8 x y z) = (term9 x y z).
Proof. exact (EQ_MP (@lem1486262 x y z) (@lem1486261 x y z)). Qed.
Lemma lem1486279 (m : real) (n : real) (p : real) : (term8 m n p) = (term9 m n p).
Proof. exact (@lem1486278 m n p). Qed.
Lemma lem1486280 (m : real) (n : real) (p : real) : (term11 m n p) = (term11 m n p).
Proof. exact (eq_refl (term11 m n p)). Qed.
Lemma lem1486281 (m : real) (n : real) (p : real) : ((term9 m n p) = (term8 m n p)) = ((term9 m n p) = (term9 m n p)).
Proof. exact (MK_COMB (@lem1486280 m n p) (@lem1486279 m n p)). Qed.
Lemma lem1486285 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1486286 (x : real) : (x = x) = True.
Proof. exact (@lem1486285 real x). Qed.
Lemma lem1486287 (m : real) (n : real) (p : real) : ((term9 m n p) = (term9 m n p)) = True.
Proof. exact (@lem1486286 (term9 m n p)). Qed.
Lemma lem1486288 (m : real) (n : real) (p : real) : ((term9 m n p) = (term8 m n p)) = True.
Proof. exact (TRANS (@lem1486281 m n p) (@lem1486287 m n p)). Qed.
Lemma lem1486289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1486290 (m : real) (n : real) (p : real) : (term12 m n p) = (and True).
Proof. exact (MK_COMB (@lem1486289) (@lem1486288 m n p)). Qed.
Lemma lem1486296 (x : real) (y : real) (z : real) : (term8 x y z) = (term9 x y z).
Proof. exact (EQ_MP (@lem1486262 x y z) (@lem1486261 x y z)). Qed.
Lemma lem1486297 (m : real) (n : real) (p : real) : (term8 m n p) = (term9 m n p).
Proof. exact (@lem1486296 m n p). Qed.
Lemma lem1486298 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1486299 (m : real) (n : real) (p : real) : (term13 m n p) = (term11 m n p).
Proof. exact (MK_COMB (@lem1486298) (@lem1486297 m n p)). Qed.
Lemma lem1486301 (x : real) (y : real) (z : real) : (term8 x y z) = (term9 x y z).
Proof. exact (EQ_MP (@lem1486262 x y z) (@lem1486261 x y z)). Qed.
Lemma lem1486302 (n : real) (m : real) (p : real) : (term8 n m p) = (term9 n m p).
Proof. exact (@lem1486301 n m p). Qed.
Lemma lem1486303 (n : real) (m : real) (p : real) : ((term8 m n p) = (term8 n m p)) = ((term9 m n p) = (term9 n m p)).
Proof. exact (MK_COMB (@lem1486299 m n p) (@lem1486302 n m p)). Qed.
Lemma lem1486308 (n : real) (m : real) (p : real) : (term14 n m p) = (term15 n m p).
Proof. exact (MK_COMB (@lem1486290 m n p) (@lem1486303 n m p)). Qed.
Lemma lem1486310 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1486311 (n : real) (m : real) (p : real) : (term15 n m p) = ((term9 m n p) = (term9 n m p)).
Proof. exact (@lem1486310 ((term9 m n p) = (term9 n m p))). Qed.
Lemma lem1486316 (n : real) (m : real) (p : real) : (term14 n m p) = ((term9 m n p) = (term9 n m p)).
Proof. exact (TRANS (@lem1486308 n m p) (@lem1486311 n m p)). Qed.
Lemma lem1486317 (n : real) (m : real) (p : real) : (term16 n m p) = (term15 n m p).
Proof. exact (MK_COMB (@lem1486270 n m) (@lem1486316 n m p)). Qed.
Lemma lem1486319 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1486320 (n : real) (m : real) (p : real) : (term15 n m p) = ((term9 m n p) = (term9 n m p)).
Proof. exact (@lem1486319 ((term9 m n p) = (term9 n m p))). Qed.
Lemma lem1486325 (n : real) (m : real) (p : real) : (term16 n m p) = ((term9 m n p) = (term9 n m p)).
Proof. exact (TRANS (@lem1486317 n m p) (@lem1486320 n m p)). Qed.
Lemma lem1486326 (n : real) (m : real) (p : real) : ((term9 m n p) = (term9 n m p)) = (term16 n m p).
Proof. exact (SYM (@lem1486325 n m p)). Qed.
Lemma lem1486327 (p : real) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem1486328 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1486329 (x : real) : term0 x.
Proof. exact (@lem1338712 x). Qed.
Lemma lem1486330 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1486331 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1486330 x) (@lem1486329 x)). Qed.
Lemma lem1486332 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1486331 x y). Qed.
Lemma lem1486333 (y : real) (x : real) : (term2 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1486336 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1486333 y x) (@lem1486332 x y)). Qed.
Lemma lem1486337 (n : real) (m : real) : (real_mul m n) = (real_mul n m).
Proof. exact (@lem1486336 n m). Qed.
Lemma lem1486338 (n : real) (m : real) : (term17 m n) = (term17 n m).
Proof. exact (MK_COMB (@lem1486328) (@lem1486337 n m)). Qed.
Lemma lem1486339 (n : real) (m : real) (p : real) : (term9 m n p) = (term9 n m p).
Proof. exact (MK_COMB (@lem1486338 n m) (@lem1486327 p)). Qed.
Lemma lem1486340 (n : real) (m : real) (p : real) : term16 n m p.
Proof. exact (EQ_MP (@lem1486326 n m p) (@lem1486339 n m p)). Qed.
