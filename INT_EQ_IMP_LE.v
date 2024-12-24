Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EQ_IMP_LE_term_abbrevs.
Require Import REAL_EQ_IMP_LE_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301608 (x : int) : term0 x.
Proof. exact (@lem1523745 (real_of_int x)). Qed.
Lemma lem2301609 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301610 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301609 x) (@lem2301608 x)). Qed.
Lemma lem2301611 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301610 x (real_of_int y)). Qed.
Lemma lem2301612 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301613 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2301612 x y) (@lem2301611 x y)). Qed.
Lemma lem2301615 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301616 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2301617 (x : int) (y : int) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem2301616) (@lem2301615 x y)). Qed.
Lemma lem2301619 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2301620 (x : int) (y : int) : (term3 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2301617 x y) (@lem2301619 x y)). Qed.
Lemma lem2301621 (x : int) (y : int) : term7 x y.
Proof. exact (EQ_MP (@lem2301620 x y) (@lem2301613 x y)). Qed.
Lemma lem2301622 (x : int) : term8 x.
Proof. exact (fun y : int => @lem2301621 x y). Qed.
Lemma lem2301623 : term9.
Proof. exact (fun x : int => @lem2301622 x). Qed.
