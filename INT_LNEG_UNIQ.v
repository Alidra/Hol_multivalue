Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LNEG_UNIQ_term_abbrevs.
Require Import REAL_LNEG_UNIQ_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2303451 (x : int) : term0 x.
Proof. exact (@lem1490175 (real_of_int x)). Qed.
Lemma lem2303452 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303453 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303452 x) (@lem2303451 x)). Qed.
Lemma lem2303454 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303453 x (real_of_int y)). Qed.
Lemma lem2303455 (x : int) (y : int) : (term2 x y) = (((term3 x y) = term4) = ((real_of_int x) = (term5 y))).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303456 (x : int) (y : int) : ((term3 x y) = term4) = ((real_of_int x) = (term5 y)).
Proof. exact (EQ_MP (@lem2303455 x y) (@lem2303454 x y)). Qed.
Lemma lem2303458 (x : int) (y : int) : (term3 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303459 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2303460 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2303459) (@lem2303458 x y)). Qed.
Lemma lem2303462 (n : nat) : (real_of_num n) = (term9 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2303463 : term4 = term10.
Proof. exact (@lem2303462 (NUMERAL 0)). Qed.
Lemma lem2303464 (x : int) (y : int) : ((term3 x y) = term4) = ((term6 x y) = term10).
Proof. exact (MK_COMB (@lem2303460 x y) (@lem2303463)). Qed.
Lemma lem2303466 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2303467 (x : int) (y : int) : ((term6 x y) = term10) = ((int_add x y) = term11).
Proof. exact (@lem2303466 (int_add x y) term11). Qed.
Lemma lem2303468 (x : int) (y : int) : ((term3 x y) = term4) = ((int_add x y) = term11).
Proof. exact (TRANS (@lem2303464 x y) (@lem2303467 x y)). Qed.
Lemma lem2303469 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2303470 (x : int) (y : int) : (term12 x y) = (term13 x y).
Proof. exact (MK_COMB (@lem2303469) (@lem2303468 x y)). Qed.
Lemma lem2303472 (x : int) : (term5 x) = (term14 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2303473 (y : int) : (term5 y) = (term14 y).
Proof. exact (@lem2303472 y). Qed.
Lemma lem2303474 (x : int) : (term15 x) = (term15 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem2303475 (x : int) (y : int) : ((real_of_int x) = (term5 y)) = ((real_of_int x) = (term14 y)).
Proof. exact (MK_COMB (@lem2303474 x) (@lem2303473 y)). Qed.
Lemma lem2303477 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2303478 (x : int) (y : int) : ((real_of_int x) = (term14 y)) = (x = (int_neg y)).
Proof. exact (@lem2303477 x (int_neg y)). Qed.
Lemma lem2303479 (x : int) (y : int) : ((real_of_int x) = (term5 y)) = (x = (int_neg y)).
Proof. exact (TRANS (@lem2303475 x y) (@lem2303478 x y)). Qed.
Lemma lem2303480 (x : int) (y : int) : (((term3 x y) = term4) = ((real_of_int x) = (term5 y))) = (((int_add x y) = term11) = (x = (int_neg y))).
Proof. exact (MK_COMB (@lem2303470 x y) (@lem2303479 x y)). Qed.
Lemma lem2303481 (x : int) (y : int) : ((int_add x y) = term11) = (x = (int_neg y)).
Proof. exact (EQ_MP (@lem2303480 x y) (@lem2303456 x y)). Qed.
Lemma lem2303482 (x : int) : term16 x.
Proof. exact (fun y : int => @lem2303481 x y). Qed.
Lemma lem2303483 : term17.
Proof. exact (fun x : int => @lem2303482 x). Qed.
