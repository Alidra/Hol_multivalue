Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EQ_ADD_LCANCEL_term_abbrevs.
Require Import REAL_EQ_ADD_LCANCEL_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301484 (x : int) : term0 x.
Proof. exact (@lem1353156 (real_of_int x)). Qed.
Lemma lem2301485 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301486 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301485 x) (@lem2301484 x)). Qed.
Lemma lem2301487 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301486 x (real_of_int y)). Qed.
Lemma lem2301488 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301489 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2301488 x y) (@lem2301487 x y)). Qed.
Lemma lem2301490 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2301489 x y (real_of_int z)). Qed.
Lemma lem2301491 (x : int) (y : int) (z : int) : (term4 x y z) = (((term5 x y) = (term5 x z)) = ((real_of_int y) = (real_of_int z))).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2301492 (x : int) (y : int) (z : int) : ((term5 x y) = (term5 x z)) = ((real_of_int y) = (real_of_int z)).
Proof. exact (EQ_MP (@lem2301491 x y z) (@lem2301490 x y z)). Qed.
Lemma lem2301494 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301495 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301496 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2301495) (@lem2301494 x y)). Qed.
Lemma lem2301498 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301499 (x : int) (z : int) : (term5 x z) = (term6 x z).
Proof. exact (@lem2301498 x z). Qed.
Lemma lem2301500 (y : int) (x : int) (z : int) : ((term5 x y) = (term5 x z)) = ((term6 x y) = (term6 x z)).
Proof. exact (MK_COMB (@lem2301496 x y) (@lem2301499 x z)). Qed.
Lemma lem2301502 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301503 (y : int) (x : int) (z : int) : ((term6 x y) = (term6 x z)) = ((int_add x y) = (int_add x z)).
Proof. exact (@lem2301502 (int_add x y) (int_add x z)). Qed.
Lemma lem2301504 (y : int) (x : int) (z : int) : ((term5 x y) = (term5 x z)) = ((int_add x y) = (int_add x z)).
Proof. exact (TRANS (@lem2301500 y x z) (@lem2301503 y x z)). Qed.
Lemma lem2301505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2301506 (y : int) (x : int) (z : int) : (term9 y x z) = (term10 y x z).
Proof. exact (MK_COMB (@lem2301505) (@lem2301504 y x z)). Qed.
Lemma lem2301508 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301509 (y : int) (z : int) : ((real_of_int y) = (real_of_int z)) = (y = z).
Proof. exact (@lem2301508 y z). Qed.
Lemma lem2301510 (x : int) (y : int) (z : int) : (((term5 x y) = (term5 x z)) = ((real_of_int y) = (real_of_int z))) = (((int_add x y) = (int_add x z)) = (y = z)).
Proof. exact (MK_COMB (@lem2301506 y x z) (@lem2301509 y z)). Qed.
Lemma lem2301511 (x : int) (y : int) (z : int) : ((int_add x y) = (int_add x z)) = (y = z).
Proof. exact (EQ_MP (@lem2301510 x y z) (@lem2301492 x y z)). Qed.
Lemma lem2301512 (x : int) (y : int) : term11 x y.
Proof. exact (fun z : int => @lem2301511 x y z). Qed.
Lemma lem2301513 (x : int) : term12 x.
Proof. exact (fun y : int => @lem2301512 x y). Qed.
Lemma lem2301514 : term13.
Proof. exact (fun x : int => @lem2301513 x). Qed.
