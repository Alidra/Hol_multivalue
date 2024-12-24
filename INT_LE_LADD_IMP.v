Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_LADD_IMP_term_abbrevs.
Require Import thm1339889_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302411 (x : int) : term0 x.
Proof. exact (@lem1339889 (real_of_int x)). Qed.
Lemma lem2302412 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302413 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302412 x) (@lem2302411 x)). Qed.
Lemma lem2302414 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302413 x (real_of_int y)). Qed.
Lemma lem2302415 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302416 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2302415 y x) (@lem2302414 x y)). Qed.
Lemma lem2302417 (y : int) (x : int) (z : int) : term4 y x z.
Proof. exact (@lem2302416 y x (real_of_int z)). Qed.
Lemma lem2302418 (y : int) (x : int) (z : int) : (term4 y x z) = (term5 y x z).
Proof. exact (eq_refl (term4 y x z)). Qed.
Lemma lem2302419 (y : int) (x : int) (z : int) : term5 y x z.
Proof. exact (EQ_MP (@lem2302418 y x z) (@lem2302417 y x z)). Qed.
Lemma lem2302421 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302422 (y : int) (z : int) : (term6 y z) = (int_le y z).
Proof. exact (@lem2302421 y z). Qed.
Lemma lem2302423 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2302424 (y : int) (z : int) : (term7 y z) = (term8 y z).
Proof. exact (MK_COMB (@lem2302423) (@lem2302422 y z)). Qed.
Lemma lem2302426 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2302427 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302428 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2302427) (@lem2302426 x y)). Qed.
Lemma lem2302430 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2302431 (x : int) (z : int) : (term9 x z) = (term10 x z).
Proof. exact (@lem2302430 x z). Qed.
Lemma lem2302432 (y : int) (x : int) (z : int) : (term13 y x z) = (term14 y x z).
Proof. exact (MK_COMB (@lem2302428 x y) (@lem2302431 x z)). Qed.
Lemma lem2302434 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302435 (y : int) (x : int) (z : int) : (term14 y x z) = (term15 y x z).
Proof. exact (@lem2302434 (int_add x y) (int_add x z)). Qed.
Lemma lem2302436 (y : int) (x : int) (z : int) : (term13 y x z) = (term15 y x z).
Proof. exact (TRANS (@lem2302432 y x z) (@lem2302435 y x z)). Qed.
Lemma lem2302437 (y : int) (x : int) (z : int) : (term5 y x z) = (term16 y x z).
Proof. exact (MK_COMB (@lem2302424 y z) (@lem2302436 y x z)). Qed.
Lemma lem2302438 (y : int) (x : int) (z : int) : term16 y x z.
Proof. exact (EQ_MP (@lem2302437 y x z) (@lem2302419 y x z)). Qed.
Lemma lem2302439 (y : int) (x : int) : term17 y x.
Proof. exact (fun z : int => @lem2302438 y x z). Qed.
Lemma lem2302440 (x : int) : term18 x.
Proof. exact (fun y : int => @lem2302439 y x). Qed.
Lemma lem2302441 : term19.
Proof. exact (fun x : int => @lem2302440 x). Qed.
