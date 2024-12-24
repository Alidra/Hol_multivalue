Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EQ_ADD_RCANCEL_0_term_abbrevs.
Require Import REAL_EQ_ADD_RCANCEL_0_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301577 (x : int) : term0 x.
Proof. exact (@lem1489162 (real_of_int x)). Qed.
Lemma lem2301578 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301579 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301578 x) (@lem2301577 x)). Qed.
Lemma lem2301580 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301579 x (real_of_int y)). Qed.
Lemma lem2301581 (y : int) (x : int) : (term2 x y) = (((term3 x y) = (real_of_int y)) = ((real_of_int x) = term4)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301582 (y : int) (x : int) : ((term3 x y) = (real_of_int y)) = ((real_of_int x) = term4).
Proof. exact (EQ_MP (@lem2301581 y x) (@lem2301580 x y)). Qed.
Lemma lem2301584 (x : int) (y : int) : (term3 x y) = (term5 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2301585 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301586 (x : int) (y : int) : (term6 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2301585) (@lem2301584 x y)). Qed.
Lemma lem2301587 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2301588 (x : int) (y : int) : ((term3 x y) = (real_of_int y)) = ((term5 x y) = (real_of_int y)).
Proof. exact (MK_COMB (@lem2301586 x y) (@lem2301587 y)). Qed.
Lemma lem2301590 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301591 (x : int) (y : int) : ((term5 x y) = (real_of_int y)) = ((int_add x y) = y).
Proof. exact (@lem2301590 (int_add x y) y). Qed.
Lemma lem2301592 (x : int) (y : int) : ((term3 x y) = (real_of_int y)) = ((int_add x y) = y).
Proof. exact (TRANS (@lem2301588 x y) (@lem2301591 x y)). Qed.
Lemma lem2301593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2301594 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2301593) (@lem2301592 x y)). Qed.
Lemma lem2301596 (n : nat) : (real_of_num n) = (term10 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2301597 : term4 = term11.
Proof. exact (@lem2301596 (NUMERAL 0)). Qed.
Lemma lem2301598 (x : int) : (term12 x) = (term12 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem2301599 (x : int) : ((real_of_int x) = term4) = ((real_of_int x) = term11).
Proof. exact (MK_COMB (@lem2301598 x) (@lem2301597)). Qed.
Lemma lem2301601 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301602 (x : int) : ((real_of_int x) = term11) = (x = term13).
Proof. exact (@lem2301601 x term13). Qed.
Lemma lem2301603 (x : int) : ((real_of_int x) = term4) = (x = term13).
Proof. exact (TRANS (@lem2301599 x) (@lem2301602 x)). Qed.
Lemma lem2301604 (y : int) (x : int) : (((term3 x y) = (real_of_int y)) = ((real_of_int x) = term4)) = (((int_add x y) = y) = (x = term13)).
Proof. exact (MK_COMB (@lem2301594 x y) (@lem2301603 x)). Qed.
Lemma lem2301605 (y : int) (x : int) : ((int_add x y) = y) = (x = term13).
Proof. exact (EQ_MP (@lem2301604 y x) (@lem2301582 y x)). Qed.
Lemma lem2301606 (x : int) : term14 x.
Proof. exact (fun y : int => @lem2301605 y x). Qed.
Lemma lem2301607 : term15.
Proof. exact (fun x : int => @lem2301606 x). Qed.
