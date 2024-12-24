Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_ANTISYM_term_abbrevs.
Require Import thm1339379_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2302326 (x : int) : term0 x.
Proof. exact (@lem1339379 (real_of_int x)). Qed.
Lemma lem2302327 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302328 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302327 x) (@lem2302326 x)). Qed.
Lemma lem2302329 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302328 x (real_of_int y)). Qed.
Lemma lem2302330 (x : int) (y : int) : (term2 x y) = ((term3 y x) = ((real_of_int x) = (real_of_int y))).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302331 (x : int) (y : int) : (term3 y x) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2302330 x y) (@lem2302329 x y)). Qed.
Lemma lem2302333 (x : int) (y : int) : (term4 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2302335 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2302334) (@lem2302333 x y)). Qed.
Lemma lem2302337 (x : int) (y : int) : (term4 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302338 (y : int) (x : int) : (term4 y x) = (int_le y x).
Proof. exact (@lem2302337 y x). Qed.
Lemma lem2302339 (y : int) (x : int) : (term3 y x) = (term7 y x).
Proof. exact (MK_COMB (@lem2302335 x y) (@lem2302338 y x)). Qed.
Lemma lem2302340 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2302341 (y : int) (x : int) : (term8 y x) = (term9 y x).
Proof. exact (MK_COMB (@lem2302340) (@lem2302339 y x)). Qed.
Lemma lem2302343 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2302344 (x : int) (y : int) : ((term3 y x) = ((real_of_int x) = (real_of_int y))) = ((term7 y x) = (x = y)).
Proof. exact (MK_COMB (@lem2302341 y x) (@lem2302343 x y)). Qed.
Lemma lem2302345 (x : int) (y : int) : (term7 y x) = (x = y).
Proof. exact (EQ_MP (@lem2302344 x y) (@lem2302331 x y)). Qed.
Lemma lem2302346 (x : int) : term10 x.
Proof. exact (fun y : int => @lem2302345 x y). Qed.
Lemma lem2302347 : term11.
Proof. exact (fun x : int => @lem2302346 x). Qed.
