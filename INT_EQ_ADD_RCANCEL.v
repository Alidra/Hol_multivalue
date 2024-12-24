Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EQ_ADD_RCANCEL_term_abbrevs.
Require Import REAL_EQ_ADD_RCANCEL_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301546 (x : int) : term0 x.
Proof. exact (@lem1355147 (real_of_int x)). Qed.
Lemma lem2301547 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301548 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301547 x) (@lem2301546 x)). Qed.
Lemma lem2301549 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301548 x (real_of_int y)). Qed.
Lemma lem2301550 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301551 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2301550 x y) (@lem2301549 x y)). Qed.
Lemma lem2301552 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2301551 x y (real_of_int z)). Qed.
Lemma lem2301553 (z : int) (x : int) (y : int) : (term4 x y z) = (((term5 x z) = (term5 y z)) = ((real_of_int x) = (real_of_int y))).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2301554 (z : int) (x : int) (y : int) : ((term5 x z) = (term5 y z)) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2301553 z x y) (@lem2301552 x y z)). Qed.
Lemma lem2301556 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301557 (x : int) (z : int) : (term5 x z) = (term6 x z).
Proof. exact (@lem2301556 x z). Qed.
Lemma lem2301558 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301559 (x : int) (z : int) : (term7 x z) = (term8 x z).
Proof. exact (MK_COMB (@lem2301558) (@lem2301557 x z)). Qed.
Lemma lem2301561 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301562 (y : int) (z : int) : (term5 y z) = (term6 y z).
Proof. exact (@lem2301561 y z). Qed.
Lemma lem2301563 (x : int) (y : int) (z : int) : ((term5 x z) = (term5 y z)) = ((term6 x z) = (term6 y z)).
Proof. exact (MK_COMB (@lem2301559 x z) (@lem2301562 y z)). Qed.
Lemma lem2301565 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301566 (x : int) (y : int) (z : int) : ((term6 x z) = (term6 y z)) = ((int_add x z) = (int_add y z)).
Proof. exact (@lem2301565 (int_add x z) (int_add y z)). Qed.
Lemma lem2301567 (x : int) (y : int) (z : int) : ((term5 x z) = (term5 y z)) = ((int_add x z) = (int_add y z)).
Proof. exact (TRANS (@lem2301563 x y z) (@lem2301566 x y z)). Qed.
Lemma lem2301568 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2301569 (x : int) (y : int) (z : int) : (term9 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem2301568) (@lem2301567 x y z)). Qed.
Lemma lem2301571 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301572 (z : int) (x : int) (y : int) : (((term5 x z) = (term5 y z)) = ((real_of_int x) = (real_of_int y))) = (((int_add x z) = (int_add y z)) = (x = y)).
Proof. exact (MK_COMB (@lem2301569 x y z) (@lem2301571 x y)). Qed.
Lemma lem2301573 (z : int) (x : int) (y : int) : ((int_add x z) = (int_add y z)) = (x = y).
Proof. exact (EQ_MP (@lem2301572 z x y) (@lem2301554 z x y)). Qed.
Lemma lem2301574 (x : int) (y : int) : term11 x y.
Proof. exact (fun z : int => @lem2301573 z x y). Qed.
Lemma lem2301575 (x : int) : term12 x.
Proof. exact (fun y : int => @lem2301574 x y). Qed.
Lemma lem2301576 : term13.
Proof. exact (fun x : int => @lem2301575 x). Qed.
