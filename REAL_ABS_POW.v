Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_POW_term_abbrevs.
Require Import REAL_ABS_MUL_spec.
Require Import REAL_ABS_NUM_spec.
Require Import thm0_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1582553 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1582554 (x : real) : term1 x.
Proof. exact (@lem1582553 (term2 x)). Qed.
Lemma lem1582555 (x : real) : (term3 x) = ((term4 x) = (term5 x)).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1582556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1582557 (x : real) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem1582556) (@lem1582555 x)). Qed.
Lemma lem1582558 (x : real) (n : nat) : (term8 x n) = ((term9 x n) = (term10 x n)).
Proof. exact (eq_refl (term8 x n)). Qed.
Lemma lem1582559 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1582560 (x : real) (n : nat) : (term11 x n) = (term12 x n).
Proof. exact (MK_COMB (@lem1582559) (@lem1582558 x n)). Qed.
Lemma lem1582561 (x : real) (n : nat) : (term13 x n) = ((term14 x n) = (term15 x n)).
Proof. exact (eq_refl (term13 x n)). Qed.
Lemma lem1582562 (x : real) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (MK_COMB (@lem1582560 x n) (@lem1582561 x n)). Qed.
Lemma lem1582563 (x : real) : (term18 x) = (term19 x).
Proof. exact (fun_ext (fun n : nat => @lem1582562 x n)). Qed.
Lemma lem1582564 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1582565 (x : real) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem1582564) (@lem1582563 x)). Qed.
Lemma lem1582566 (x : real) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem1582557 x) (@lem1582565 x)). Qed.
Lemma lem1582567 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1582568 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1582567) (@lem1582566 x)). Qed.
Lemma lem1582569 (x : real) (n : nat) : (term8 x n) = ((term9 x n) = (term10 x n)).
Proof. exact (eq_refl (term8 x n)). Qed.
Lemma lem1582570 (x : real) : (term26 x) = (term2 x).
Proof. exact (fun_ext (fun n : nat => @lem1582569 x n)). Qed.
Lemma lem1582571 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1582572 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1582571) (@lem1582570 x)). Qed.
Lemma lem1582573 (x : real) : (term1 x) = (term29 x).
Proof. exact (MK_COMB (@lem1582568 x) (@lem1582572 x)). Qed.
Lemma lem1582574 (x : real) : term29 x.
Proof. exact (EQ_MP (@lem1582573 x) (@lem1582554 x)). Qed.
Lemma lem1582582 (n : nat) : term30 n.
Proof. exact (@lem1362923 n). Qed.
Lemma lem1582583 (n : nat) : (term30 n) = ((term31 n) = (real_of_num n)).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem1582593 (x : real) : (term32 x) = term33.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1582594 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1582595 (x : real) : (term4 x) = term34.
Proof. exact (MK_COMB (@lem1582594) (@lem1582593 x)). Qed.
Lemma lem1582597 (n : nat) : (term31 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem1582583 n) (@lem1582582 n)). Qed.
Lemma lem1582598 : term34 = term33.
Proof. exact (@lem1582597 term35). Qed.
Lemma lem1582599 (x : real) : (term4 x) = term33.
Proof. exact (TRANS (@lem1582595 x) (@lem1582598)). Qed.
Lemma lem1582600 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1582601 (x : real) : (term36 x) = term37.
Proof. exact (MK_COMB (@lem1582600) (@lem1582599 x)). Qed.
Lemma lem1582603 (x : real) : (term32 x) = term33.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1582604 (x : real) : (term5 x) = term33.
Proof. exact (@lem1582603 (real_abs x)). Qed.
Lemma lem1582605 (x : real) : ((term4 x) = (term5 x)) = (term33 = term33).
Proof. exact (MK_COMB (@lem1582601 x) (@lem1582604 x)). Qed.
Lemma lem1582607 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1582608 (x : real) : (x = x) = True.
Proof. exact (@lem1582607 real x). Qed.
Lemma lem1582609 : (term33 = term33) = True.
Proof. exact (@lem1582608 term33). Qed.
Lemma lem1582610 (x : real) : ((term4 x) = (term5 x)) = True.
Proof. exact (TRANS (@lem1582605 x) (@lem1582609)). Qed.
Lemma lem1582611 (x : real) : True = ((term4 x) = (term5 x)).
Proof. exact (SYM (@lem1582610 x)). Qed.
Lemma lem1582612 (x : real) : (term4 x) = (term5 x).
Proof. exact (EQ_MP (@lem1582611 x) (@lem0)). Qed.
Lemma lem1582613 (x : real) : term38 x.
Proof. exact (@lem1582313 x). Qed.
Lemma lem1582614 (x : real) : (term38 x) = (term39 x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1582615 (x : real) : term39 x.
Proof. exact (EQ_MP (@lem1582614 x) (@lem1582613 x)). Qed.
Lemma lem1582616 (x : real) (y : real) : term40 x y.
Proof. exact (@lem1582615 x y). Qed.
Lemma lem1582617 (x : real) (y : real) : (term40 x y) = ((term41 x y) = (term42 x y)).
Proof. exact (eq_refl (term40 x y)). Qed.
Lemma lem1582622 (x : real) : term43 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1582623 (x : real) (n : nat) : term44 x n.
Proof. exact (@lem1582622 x n). Qed.
Lemma lem1582624 (x : real) (n : nat) : (term44 x n) = ((term45 x n) = (term46 x n)).
Proof. exact (eq_refl (term44 x n)). Qed.
Lemma lem1582630 (x : real) (n : nat) : (term45 x n) = (term46 x n).
Proof. exact (EQ_MP (@lem1582624 x n) (@lem1582623 x n)). Qed.
Lemma lem1582631 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem1582632 (x : real) (n : nat) : (term14 x n) = (term47 x n).
Proof. exact (MK_COMB (@lem1582631) (@lem1582630 x n)). Qed.
Lemma lem1582634 (x : real) (y : real) : (term41 x y) = (term42 x y).
Proof. exact (EQ_MP (@lem1582617 x y) (@lem1582616 x y)). Qed.
Lemma lem1582635 (x : real) (n : nat) : (term47 x n) = (term48 x n).
Proof. exact (@lem1582634 x (real_pow x n)). Qed.
Lemma lem1582637 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term9 x n) = (term10 x n).
Proof. exact (h1). Qed.
Lemma lem1582638 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1582639 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term48 x n) = (term50 x n).
Proof. exact (MK_COMB (@lem1582638 x) (@lem1582637 x n h1)). Qed.
Lemma lem1582640 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term47 x n) = (term50 x n).
Proof. exact (TRANS (@lem1582635 x n) (@lem1582639 x n h1)). Qed.
Lemma lem1582641 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term14 x n) = (term50 x n).
Proof. exact (TRANS (@lem1582632 x n) (@lem1582640 x n h1)). Qed.
Lemma lem1582642 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1582643 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term51 x n) = (term52 x n).
Proof. exact (MK_COMB (@lem1582642) (@lem1582641 x n h1)). Qed.
Lemma lem1582645 (x : real) (n : nat) : (term45 x n) = (term46 x n).
Proof. exact (EQ_MP (@lem1582624 x n) (@lem1582623 x n)). Qed.
Lemma lem1582646 (x : real) (n : nat) : (term15 x n) = (term50 x n).
Proof. exact (@lem1582645 (real_abs x) n). Qed.
Lemma lem1582647 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : ((term14 x n) = (term15 x n)) = ((term50 x n) = (term50 x n)).
Proof. exact (MK_COMB (@lem1582643 x n h1) (@lem1582646 x n)). Qed.
Lemma lem1582649 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1582650 (x : real) : (x = x) = True.
Proof. exact (@lem1582649 real x). Qed.
Lemma lem1582651 (x : real) (n : nat) : ((term50 x n) = (term50 x n)) = True.
Proof. exact (@lem1582650 (term50 x n)). Qed.
Lemma lem1582652 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : ((term14 x n) = (term15 x n)) = True.
Proof. exact (TRANS (@lem1582647 x n h1) (@lem1582651 x n)). Qed.
Lemma lem1582653 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : True = ((term14 x n) = (term15 x n)).
Proof. exact (SYM (@lem1582652 x n h1)). Qed.
Lemma lem1582654 (x : real) (n : nat) (h1 : (term9 x n) = (term10 x n)) : (term14 x n) = (term15 x n).
Proof. exact (EQ_MP (@lem1582653 x n h1) (@lem0)). Qed.
Lemma lem1582655 (x : real) (n : nat) : term17 x n.
Proof. exact (fun h0 : (term9 x n) = (term10 x n) => @lem1582654 x n h0). Qed.
Lemma lem1582660 (x : real) : term21 x.
Proof. exact (fun n : nat => @lem1582655 x n). Qed.
Lemma lem1582661 (x : real) : term23 x.
Proof. exact (conj (@lem1582612 x) (@lem1582660 x)). Qed.
Lemma lem1582662 (x : real) : term28 x.
Proof. exact (@lem1582574 x (@lem1582661 x)). Qed.
Lemma lem1582667 : term53.
Proof. exact (fun x : real => @lem1582662 x). Qed.
