Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EQ_MUL_LCANCEL_term_abbrevs.
Require Import REAL_EQ_MUL_LCANCEL_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301669 (x : int) : term0 x.
Proof. exact (@lem1586590 (real_of_int x)). Qed.
Lemma lem2301670 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301671 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301670 x) (@lem2301669 x)). Qed.
Lemma lem2301672 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301671 x (real_of_int y)). Qed.
Lemma lem2301673 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301674 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2301673 x y) (@lem2301672 x y)). Qed.
Lemma lem2301675 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2301674 x y (real_of_int z)). Qed.
Lemma lem2301676 (x : int) (y : int) (z : int) : (term4 x y z) = (((term5 x y) = (term5 x z)) = (term6 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2301677 (x : int) (y : int) (z : int) : ((term5 x y) = (term5 x z)) = (term6 x y z).
Proof. exact (EQ_MP (@lem2301676 x y z) (@lem2301675 x y z)). Qed.
Lemma lem2301679 (x : int) (y : int) : (term5 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301680 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301681 (x : int) (y : int) : (term8 x y) = (term9 x y).
Proof. exact (MK_COMB (@lem2301680) (@lem2301679 x y)). Qed.
Lemma lem2301683 (x : int) (y : int) : (term5 x y) = (term7 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301684 (x : int) (z : int) : (term5 x z) = (term7 x z).
Proof. exact (@lem2301683 x z). Qed.
Lemma lem2301685 (y : int) (x : int) (z : int) : ((term5 x y) = (term5 x z)) = ((term7 x y) = (term7 x z)).
Proof. exact (MK_COMB (@lem2301681 x y) (@lem2301684 x z)). Qed.
Lemma lem2301687 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301688 (y : int) (x : int) (z : int) : ((term7 x y) = (term7 x z)) = ((int_mul x y) = (int_mul x z)).
Proof. exact (@lem2301687 (int_mul x y) (int_mul x z)). Qed.
Lemma lem2301689 (y : int) (x : int) (z : int) : ((term5 x y) = (term5 x z)) = ((int_mul x y) = (int_mul x z)).
Proof. exact (TRANS (@lem2301685 y x z) (@lem2301688 y x z)). Qed.
Lemma lem2301690 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2301691 (y : int) (x : int) (z : int) : (term10 y x z) = (term11 y x z).
Proof. exact (MK_COMB (@lem2301690) (@lem2301689 y x z)). Qed.
Lemma lem2301693 (n : nat) : (real_of_num n) = (term12 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2301694 : term13 = term14.
Proof. exact (@lem2301693 (NUMERAL 0)). Qed.
Lemma lem2301695 (x : int) : (term15 x) = (term15 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem2301696 (x : int) : ((real_of_int x) = term13) = ((real_of_int x) = term14).
Proof. exact (MK_COMB (@lem2301695 x) (@lem2301694)). Qed.
Lemma lem2301698 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301699 (x : int) : ((real_of_int x) = term14) = (x = term16).
Proof. exact (@lem2301698 x term16). Qed.
Lemma lem2301700 (x : int) : ((real_of_int x) = term13) = (x = term16).
Proof. exact (TRANS (@lem2301696 x) (@lem2301699 x)). Qed.
Lemma lem2301701 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2301702 (x : int) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem2301701) (@lem2301700 x)). Qed.
Lemma lem2301704 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301705 (y : int) (z : int) : ((real_of_int y) = (real_of_int z)) = (y = z).
Proof. exact (@lem2301704 y z). Qed.
Lemma lem2301706 (x : int) (y : int) (z : int) : (term6 x y z) = (term19 x y z).
Proof. exact (MK_COMB (@lem2301702 x) (@lem2301705 y z)). Qed.
Lemma lem2301707 (x : int) (y : int) (z : int) : (((term5 x y) = (term5 x z)) = (term6 x y z)) = (((int_mul x y) = (int_mul x z)) = (term19 x y z)).
Proof. exact (MK_COMB (@lem2301691 y x z) (@lem2301706 x y z)). Qed.
Lemma lem2301708 (x : int) (y : int) (z : int) : ((int_mul x y) = (int_mul x z)) = (term19 x y z).
Proof. exact (EQ_MP (@lem2301707 x y z) (@lem2301677 x y z)). Qed.
Lemma lem2301709 (x : int) (y : int) : term20 x y.
Proof. exact (fun z : int => @lem2301708 x y z). Qed.
Lemma lem2301710 (x : int) : term21 x.
Proof. exact (fun y : int => @lem2301709 x y). Qed.
Lemma lem2301711 : term22.
Proof. exact (fun x : int => @lem2301710 x). Qed.
