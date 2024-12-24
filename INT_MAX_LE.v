Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MAX_LE_term_abbrevs.
Require Import REAL_MAX_LE_spec.
Require Import thm2299888_spec.
Require Import thm2299889_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2305282 (x : int) : term0 x.
Proof. exact (@lem1566936 (real_of_int x)). Qed.
Lemma lem2305283 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305284 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305283 x) (@lem2305282 x)). Qed.
Lemma lem2305285 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305284 x (real_of_int y)). Qed.
Lemma lem2305286 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305287 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2305286 x y) (@lem2305285 x y)). Qed.
Lemma lem2305288 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2305287 x y (real_of_int z)). Qed.
Lemma lem2305289 (x : int) (y : int) (z : int) : (term4 x y z) = ((term5 x y z) = (term6 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2305290 (x : int) (y : int) (z : int) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem2305289 x y z) (@lem2305288 x y z)). Qed.
Lemma lem2305292 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299889 x y) (@lem2299888 x y)). Qed.
Lemma lem2305293 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2305294 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2305293) (@lem2305292 x y)). Qed.
Lemma lem2305295 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2305296 (x : int) (y : int) (z : int) : (term5 x y z) = (term11 x y z).
Proof. exact (MK_COMB (@lem2305294 x y) (@lem2305295 z)). Qed.
Lemma lem2305298 (x : int) (y : int) : (term12 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2305299 (x : int) (y : int) (z : int) : (term11 x y z) = (term13 x y z).
Proof. exact (@lem2305298 (int_max x y) z). Qed.
Lemma lem2305300 (x : int) (y : int) (z : int) : (term5 x y z) = (term13 x y z).
Proof. exact (TRANS (@lem2305296 x y z) (@lem2305299 x y z)). Qed.
Lemma lem2305301 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2305302 (x : int) (y : int) (z : int) : (term14 x y z) = (term15 x y z).
Proof. exact (MK_COMB (@lem2305301) (@lem2305300 x y z)). Qed.
Lemma lem2305304 (x : int) (y : int) : (term12 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2305305 (x : int) (z : int) : (term12 x z) = (int_le x z).
Proof. exact (@lem2305304 x z). Qed.
Lemma lem2305306 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2305307 (x : int) (z : int) : (term16 x z) = (term17 x z).
Proof. exact (MK_COMB (@lem2305306) (@lem2305305 x z)). Qed.
Lemma lem2305309 (x : int) (y : int) : (term12 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2305310 (y : int) (z : int) : (term12 y z) = (int_le y z).
Proof. exact (@lem2305309 y z). Qed.
Lemma lem2305311 (x : int) (y : int) (z : int) : (term6 x y z) = (term18 x y z).
Proof. exact (MK_COMB (@lem2305307 x z) (@lem2305310 y z)). Qed.
Lemma lem2305312 (x : int) (y : int) (z : int) : ((term5 x y z) = (term6 x y z)) = ((term13 x y z) = (term18 x y z)).
Proof. exact (MK_COMB (@lem2305302 x y z) (@lem2305311 x y z)). Qed.
Lemma lem2305313 (x : int) (y : int) (z : int) : (term13 x y z) = (term18 x y z).
Proof. exact (EQ_MP (@lem2305312 x y z) (@lem2305290 x y z)). Qed.
Lemma lem2305314 (x : int) (y : int) : term19 x y.
Proof. exact (fun z : int => @lem2305313 x y z). Qed.
Lemma lem2305315 (x : int) : term20 x.
Proof. exact (fun y : int => @lem2305314 x y). Qed.
Lemma lem2305316 : term21.
Proof. exact (fun x : int => @lem2305315 x). Qed.
