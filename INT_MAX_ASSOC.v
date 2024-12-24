Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MAX_ASSOC_term_abbrevs.
Require Import REAL_MAX_ASSOC_spec.
Require Import thm2299888_spec.
Require Import thm2299889_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2305243 (x : int) : term0 x.
Proof. exact (@lem1573168 (real_of_int x)). Qed.
Lemma lem2305244 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305245 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305244 x) (@lem2305243 x)). Qed.
Lemma lem2305246 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305245 x (real_of_int y)). Qed.
Lemma lem2305247 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305248 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2305247 x y) (@lem2305246 x y)). Qed.
Lemma lem2305249 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2305248 x y (real_of_int z)). Qed.
Lemma lem2305250 (x : int) (y : int) (z : int) : (term4 x y z) = ((term5 x y z) = (term6 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2305251 (x : int) (y : int) (z : int) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem2305250 x y z) (@lem2305249 x y z)). Qed.
Lemma lem2305253 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305254 (y : int) (z : int) : (term7 y z) = (term8 y z).
Proof. exact (@lem2305253 y z). Qed.
Lemma lem2305255 (x : int) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2305256 (x : int) (y : int) (z : int) : (term5 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem2305255 x) (@lem2305254 y z)). Qed.
Lemma lem2305258 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305259 (x : int) (y : int) (z : int) : (term10 x y z) = (term11 x y z).
Proof. exact (@lem2305258 x (int_max y z)). Qed.
Lemma lem2305260 (x : int) (y : int) (z : int) : (term5 x y z) = (term11 x y z).
Proof. exact (TRANS (@lem2305256 x y z) (@lem2305259 x y z)). Qed.
Lemma lem2305261 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305262 (x : int) (y : int) (z : int) : (term12 x y z) = (term13 x y z).
Proof. exact (MK_COMB (@lem2305261) (@lem2305260 x y z)). Qed.
Lemma lem2305264 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305265 : real_max = real_max.
Proof. exact (eq_refl real_max). Qed.
Lemma lem2305266 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem2305265) (@lem2305264 x y)). Qed.
Lemma lem2305267 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2305268 (x : int) (y : int) (z : int) : (term6 x y z) = (term16 x y z).
Proof. exact (MK_COMB (@lem2305266 x y) (@lem2305267 z)). Qed.
Lemma lem2305270 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305271 (x : int) (y : int) (z : int) : (term16 x y z) = (term17 x y z).
Proof. exact (@lem2305270 (int_max x y) z). Qed.
Lemma lem2305272 (x : int) (y : int) (z : int) : (term6 x y z) = (term17 x y z).
Proof. exact (TRANS (@lem2305268 x y z) (@lem2305271 x y z)). Qed.
Lemma lem2305273 (x : int) (y : int) (z : int) : ((term5 x y z) = (term6 x y z)) = ((term11 x y z) = (term17 x y z)).
Proof. exact (MK_COMB (@lem2305262 x y z) (@lem2305272 x y z)). Qed.
Lemma lem2305275 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305276 (x : int) (y : int) (z : int) : ((term11 x y z) = (term17 x y z)) = ((term18 x y z) = (term19 x y z)).
Proof. exact (@lem2305275 (term18 x y z) (term19 x y z)). Qed.
Lemma lem2305277 (x : int) (y : int) (z : int) : ((term5 x y z) = (term6 x y z)) = ((term18 x y z) = (term19 x y z)).
Proof. exact (TRANS (@lem2305273 x y z) (@lem2305276 x y z)). Qed.
Lemma lem2305278 (x : int) (y : int) (z : int) : (term18 x y z) = (term19 x y z).
Proof. exact (EQ_MP (@lem2305277 x y z) (@lem2305251 x y z)). Qed.
Lemma lem2305279 (x : int) (y : int) : term20 x y.
Proof. exact (fun z : int => @lem2305278 x y z). Qed.
Lemma lem2305280 (x : int) : term21 x.
Proof. exact (fun y : int => @lem2305279 x y). Qed.
Lemma lem2305281 : term22.
Proof. exact (fun x : int => @lem2305280 x). Qed.
