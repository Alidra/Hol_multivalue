Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_TRANS_term_abbrevs.
Require Import thm1339577_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303424 (x : int) : term0 x.
Proof. exact (@lem1339577 (real_of_int x)). Qed.
Lemma lem2303425 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303426 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303425 x) (@lem2303424 x)). Qed.
Lemma lem2303427 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303426 x (real_of_int y)). Qed.
Lemma lem2303428 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303429 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2303428 y x) (@lem2303427 x y)). Qed.
Lemma lem2303430 (y : int) (x : int) (z : int) : term4 y x z.
Proof. exact (@lem2303429 y x (real_of_int z)). Qed.
Lemma lem2303431 (y : int) (x : int) (z : int) : (term4 y x z) = (term5 y x z).
Proof. exact (eq_refl (term4 y x z)). Qed.
Lemma lem2303432 (y : int) (x : int) (z : int) : term5 y x z.
Proof. exact (EQ_MP (@lem2303431 y x z) (@lem2303430 y x z)). Qed.
Lemma lem2303434 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2303436 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2303435) (@lem2303434 x y)). Qed.
Lemma lem2303438 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303439 (y : int) (z : int) : (term6 y z) = (int_le y z).
Proof. exact (@lem2303438 y z). Qed.
Lemma lem2303440 (x : int) (y : int) (z : int) : (term9 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem2303436 x y) (@lem2303439 y z)). Qed.
Lemma lem2303441 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2303442 (x : int) (y : int) (z : int) : (term11 x y z) = (term12 x y z).
Proof. exact (MK_COMB (@lem2303441) (@lem2303440 x y z)). Qed.
Lemma lem2303444 (x : int) (y : int) : (term6 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303445 (x : int) (z : int) : (term6 x z) = (int_le x z).
Proof. exact (@lem2303444 x z). Qed.
Lemma lem2303446 (y : int) (x : int) (z : int) : (term5 y x z) = (term13 y x z).
Proof. exact (MK_COMB (@lem2303442 x y z) (@lem2303445 x z)). Qed.
Lemma lem2303447 (y : int) (x : int) (z : int) : term13 y x z.
Proof. exact (EQ_MP (@lem2303446 y x z) (@lem2303432 y x z)). Qed.
Lemma lem2303448 (y : int) (x : int) : term14 y x.
Proof. exact (fun z : int => @lem2303447 y x z). Qed.
Lemma lem2303449 (x : int) : term15 x.
Proof. exact (fun y : int => @lem2303448 y x). Qed.
Lemma lem2303450 : term16.
Proof. exact (fun x : int => @lem2303449 x). Qed.
