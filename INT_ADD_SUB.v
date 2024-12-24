Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ADD_SUB_term_abbrevs.
Require Import REAL_ADD_SUB_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301246 (x : int) : term0 x.
Proof. exact (@lem1507870 (real_of_int x)). Qed.
Lemma lem2301247 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301248 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301247 x) (@lem2301246 x)). Qed.
Lemma lem2301249 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301248 x (real_of_int y)). Qed.
Lemma lem2301250 (x : int) (y : int) : (term2 x y) = ((term3 y x) = (real_of_int y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301251 (x : int) (y : int) : (term3 y x) = (real_of_int y).
Proof. exact (EQ_MP (@lem2301250 x y) (@lem2301249 x y)). Qed.
Lemma lem2301253 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301254 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2301255 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2301254) (@lem2301253 x y)). Qed.
Lemma lem2301256 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2301257 (y : int) (x : int) : (term3 y x) = (term8 y x).
Proof. exact (MK_COMB (@lem2301255 x y) (@lem2301256 x)). Qed.
Lemma lem2301259 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2301260 (y : int) (x : int) : (term8 y x) = (term11 y x).
Proof. exact (@lem2301259 (int_add x y) x). Qed.
Lemma lem2301261 (y : int) (x : int) : (term3 y x) = (term11 y x).
Proof. exact (TRANS (@lem2301257 y x) (@lem2301260 y x)). Qed.
Lemma lem2301262 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301263 (y : int) (x : int) : (term12 y x) = (term13 y x).
Proof. exact (MK_COMB (@lem2301262) (@lem2301261 y x)). Qed.
Lemma lem2301264 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2301265 (x : int) (y : int) : ((term3 y x) = (real_of_int y)) = ((term11 y x) = (real_of_int y)).
Proof. exact (MK_COMB (@lem2301263 y x) (@lem2301264 y)). Qed.
Lemma lem2301267 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301268 (x : int) (y : int) : ((term11 y x) = (real_of_int y)) = ((term14 y x) = y).
Proof. exact (@lem2301267 (term14 y x) y). Qed.
Lemma lem2301269 (x : int) (y : int) : ((term3 y x) = (real_of_int y)) = ((term14 y x) = y).
Proof. exact (TRANS (@lem2301265 x y) (@lem2301268 x y)). Qed.
Lemma lem2301270 (x : int) (y : int) : (term14 y x) = y.
Proof. exact (EQ_MP (@lem2301269 x y) (@lem2301251 x y)). Qed.
Lemma lem2301271 (x : int) : term15 x.
Proof. exact (fun y : int => @lem2301270 x y). Qed.
Lemma lem2301272 : term16.
Proof. exact (fun x : int => @lem2301271 x). Qed.
