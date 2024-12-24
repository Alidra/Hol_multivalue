Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_LMUL_EQ_term_abbrevs.
Require Import REAL_LE_LMUL_EQ_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302532 (x : int) : term0 x.
Proof. exact (@lem1602377 (real_of_int x)). Qed.
Lemma lem2302533 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302534 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302533 x) (@lem2302532 x)). Qed.
Lemma lem2302535 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302534 x (real_of_int y)). Qed.
Lemma lem2302536 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302537 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2302536 x y) (@lem2302535 x y)). Qed.
Lemma lem2302538 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2302537 x y (real_of_int z)). Qed.
Lemma lem2302539 (z : int) (x : int) (y : int) : (term4 x y z) = (term5 z x y).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2302540 (z : int) (x : int) (y : int) : term5 z x y.
Proof. exact (EQ_MP (@lem2302539 z x y) (@lem2302538 x y z)). Qed.
Lemma lem2302542 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302543 : term7 = term8.
Proof. exact (@lem2302542 (NUMERAL 0)). Qed.
Lemma lem2302544 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2302545 : term9 = term10.
Proof. exact (MK_COMB (@lem2302544) (@lem2302543)). Qed.
Lemma lem2302546 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2302547 (z : int) : (term11 z) = (term12 z).
Proof. exact (MK_COMB (@lem2302545) (@lem2302546 z)). Qed.
Lemma lem2302549 (x : int) (y : int) : (term13 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2302550 (z : int) : (term12 z) = (term14 z).
Proof. exact (@lem2302549 term15 z). Qed.
Lemma lem2302551 (z : int) : (term11 z) = (term14 z).
Proof. exact (TRANS (@lem2302547 z) (@lem2302550 z)). Qed.
Lemma lem2302552 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2302553 (z : int) : (term16 z) = (term17 z).
Proof. exact (MK_COMB (@lem2302552) (@lem2302551 z)). Qed.
Lemma lem2302555 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2302556 (z : int) (x : int) : (term18 z x) = (term19 z x).
Proof. exact (@lem2302555 z x). Qed.
Lemma lem2302557 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302558 (z : int) (x : int) : (term20 z x) = (term21 z x).
Proof. exact (MK_COMB (@lem2302557) (@lem2302556 z x)). Qed.
Lemma lem2302560 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2302561 (z : int) (y : int) : (term18 z y) = (term19 z y).
Proof. exact (@lem2302560 z y). Qed.
Lemma lem2302562 (x : int) (z : int) (y : int) : (term22 x z y) = (term23 x z y).
Proof. exact (MK_COMB (@lem2302558 z x) (@lem2302561 z y)). Qed.
Lemma lem2302564 (x : int) (y : int) : (term24 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302565 (x : int) (z : int) (y : int) : (term23 x z y) = (term25 x z y).
Proof. exact (@lem2302564 (int_mul z x) (int_mul z y)). Qed.
Lemma lem2302566 (x : int) (z : int) (y : int) : (term22 x z y) = (term25 x z y).
Proof. exact (TRANS (@lem2302562 x z y) (@lem2302565 x z y)). Qed.
Lemma lem2302567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2302568 (x : int) (z : int) (y : int) : (term26 x z y) = (term27 x z y).
Proof. exact (MK_COMB (@lem2302567) (@lem2302566 x z y)). Qed.
Lemma lem2302570 (x : int) (y : int) : (term24 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302571 (z : int) (x : int) (y : int) : ((term22 x z y) = (term24 x y)) = ((term25 x z y) = (int_le x y)).
Proof. exact (MK_COMB (@lem2302568 x z y) (@lem2302570 x y)). Qed.
Lemma lem2302572 (z : int) (x : int) (y : int) : (term5 z x y) = (term28 z x y).
Proof. exact (MK_COMB (@lem2302553 z) (@lem2302571 z x y)). Qed.
Lemma lem2302573 (z : int) (x : int) (y : int) : term28 z x y.
Proof. exact (EQ_MP (@lem2302572 z x y) (@lem2302540 z x y)). Qed.
Lemma lem2302574 (x : int) (y : int) : term29 x y.
Proof. exact (fun z : int => @lem2302573 z x y). Qed.
Lemma lem2302575 (x : int) : term30 x.
Proof. exact (fun y : int => @lem2302574 x y). Qed.
Lemma lem2302576 : term31.
Proof. exact (fun x : int => @lem2302575 x). Qed.
