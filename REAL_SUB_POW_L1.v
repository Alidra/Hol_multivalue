Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_POW_L1_term_abbrevs.
Require Import REAL_MUL_LNEG_spec.
Require Import REAL_NEG_SUB_spec.
Require Import REAL_SUB_POW_R1_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7332367 (x : real) : term0 x.
Proof. exact (@lem1360913 x). Qed.
Lemma lem7332368 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem7332369 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem7332368 x) (@lem7332367 x)). Qed.
Lemma lem7332370 (x : real) (y : real) : term2 x y.
Proof. exact (@lem7332369 x y). Qed.
Lemma lem7332371 (x : real) (y : real) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem7332373 (x : real) : term5 x.
Proof. exact (@lem7332366 x). Qed.
Lemma lem7332374 (x : real) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem7332375 (x : real) : term6 x.
Proof. exact (EQ_MP (@lem7332374 x) (@lem7332373 x)). Qed.
Lemma lem7332376 (x : real) (n : nat) : term7 x n.
Proof. exact (@lem7332375 x n). Qed.
Lemma lem7332377 (n : nat) (x : real) : (term7 x n) = (term8 n x).
Proof. exact (eq_refl (term7 x n)). Qed.
Lemma lem7332378 (n : nat) (x : real) : term8 n x.
Proof. exact (EQ_MP (@lem7332377 n x) (@lem7332376 x n)). Qed.
Lemma lem7332379 (n : nat) (h1 : term9 n) : term9 n.
Proof. exact (h1). Qed.
Lemma lem7332380 (x : real) (n : nat) (h1 : term9 n) : (term10 x n) = (term11 n x).
Proof. exact (@lem7332378 n x (@lem7332379 n h1)). Qed.
Lemma lem7332388 (y : real) (x : real) (h1 : (term12 x y) = (real_sub y x)) : (term12 x y) = (real_sub y x).
Proof. exact (h1). Qed.
Lemma lem7332389 (y : real) (x : real) (h1 : (term12 x y) = (real_sub y x)) : (real_sub y x) = (term12 x y).
Proof. exact (SYM (@lem7332388 y x h1)). Qed.
Lemma lem7332390 (x : real) (y : real) (h1 : (real_sub y x) = (term12 x y)) : (real_sub y x) = (term12 x y).
Proof. exact (h1). Qed.
Lemma lem7332391 (x : real) (y : real) (h1 : (real_sub y x) = (term12 x y)) : (term12 x y) = (real_sub y x).
Proof. exact (SYM (@lem7332390 x y h1)). Qed.
Lemma lem7332392 (x : real) (y : real) : ((term12 x y) = (real_sub y x)) = ((real_sub y x) = (term12 x y)).
Proof. exact (prop_ext (fun h1 : (term12 x y) = (real_sub y x) => @lem7332389 y x h1) (fun h1 : (real_sub y x) = (term12 x y) => @lem7332391 x y h1)). Qed.
Lemma lem7332393 (x : real) : (term13 x) = (term14 x).
Proof. exact (fun_ext (fun y : real => @lem7332392 x y)). Qed.
Lemma lem7332394 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7332395 (x : real) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem7332394) (@lem7332393 x)). Qed.
Lemma lem7332396 : term17 = term18.
Proof. exact (fun_ext (fun x : real => @lem7332395 x)). Qed.
Lemma lem7332397 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7332398 : term19 = term20.
Proof. exact (MK_COMB (@lem7332397) (@lem7332396)). Qed.
Lemma lem7332399 : term20.
Proof. exact (EQ_MP (@lem7332398) (@lem1374337)). Qed.
Lemma lem7332400 (x : real) : term21 x.
Proof. exact (@lem7332399 x). Qed.
Lemma lem7332401 (x : real) : (term21 x) = (term16 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem7332402 (x : real) : term16 x.
Proof. exact (EQ_MP (@lem7332401 x) (@lem7332400 x)). Qed.
Lemma lem7332403 (x : real) (y : real) : term22 x y.
Proof. exact (@lem7332402 x y). Qed.
Lemma lem7332404 (x : real) (y : real) : (term22 x y) = ((real_sub y x) = (term12 x y)).
Proof. exact (eq_refl (term22 x y)). Qed.
Lemma lem7332419 (x : real) (y : real) : (real_sub y x) = (term12 x y).
Proof. exact (EQ_MP (@lem7332404 x y) (@lem7332403 x y)). Qed.
Lemma lem7332420 (x : real) (n : nat) : (term23 x n) = (term24 x n).
Proof. exact (@lem7332419 (real_pow x n) term25). Qed.
Lemma lem7332421 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7332422 (x : real) (n : nat) : (term26 x n) = (term27 x n).
Proof. exact (MK_COMB (@lem7332421) (@lem7332420 x n)). Qed.
Lemma lem7332424 (x : real) (y : real) : (real_sub y x) = (term12 x y).
Proof. exact (EQ_MP (@lem7332404 x y) (@lem7332403 x y)). Qed.
Lemma lem7332425 (x : real) : (term28 x) = (term29 x).
Proof. exact (@lem7332424 x term25). Qed.
Lemma lem7332426 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7332427 (x : real) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem7332426) (@lem7332425 x)). Qed.
Lemma lem7332428 (n : nat) (x : real) : (term32 n x) = (term32 n x).
Proof. exact (eq_refl (term32 n x)). Qed.
Lemma lem7332429 (n : nat) (x : real) : (term33 n x) = (term34 n x).
Proof. exact (MK_COMB (@lem7332427 x) (@lem7332428 n x)). Qed.
Lemma lem7332430 (n : nat) (x : real) : ((term23 x n) = (term33 n x)) = ((term24 x n) = (term34 n x)).
Proof. exact (MK_COMB (@lem7332422 x n) (@lem7332429 n x)). Qed.
Lemma lem7332431 (n : nat) : (term35 n) = (term35 n).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem7332432 (n : nat) (x : real) : (term36 n x) = (term37 n x).
Proof. exact (MK_COMB (@lem7332431 n) (@lem7332430 n x)). Qed.
Lemma lem7332433 (x : real) : (term38 x) = (term39 x).
Proof. exact (fun_ext (fun n : nat => @lem7332432 n x)). Qed.
Lemma lem7332434 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7332435 (x : real) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem7332434) (@lem7332433 x)). Qed.
Lemma lem7332436 : term42 = term43.
Proof. exact (fun_ext (fun x : real => @lem7332435 x)). Qed.
Lemma lem7332437 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7332438 : term44 = term45.
Proof. exact (MK_COMB (@lem7332437) (@lem7332436)). Qed.
Lemma lem7332439 : term45 = term44.
Proof. exact (SYM (@lem7332438)). Qed.
Lemma lem7332451 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term46 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7332452 (p : Prop) (q : Prop) (p' : Prop) : term47 p q p'.
Proof. exact (fun q' : Prop => @lem7332451 p q p' q'). Qed.
Lemma lem7332453 (p : Prop) (q : Prop) : term48 p q.
Proof. exact (fun p' : Prop => @lem7332452 p q p'). Qed.
Lemma lem7332454 (n : nat) (x : real) : term49 n x.
Proof. exact (@lem7332453 (term9 n) ((term24 x n) = (term34 n x))). Qed.
Lemma lem7332455 (n : nat) (x : real) (p' : Prop) : term50 n x p'.
Proof. exact (@lem7332454 n x p'). Qed.
Lemma lem7332456 (n : nat) (x : real) (p' : Prop) : (term50 n x p') = (term51 n x p').
Proof. exact (eq_refl (term50 n x p')). Qed.
Lemma lem7332457 (n : nat) (x : real) (p' : Prop) : term51 n x p'.
Proof. exact (EQ_MP (@lem7332456 n x p') (@lem7332455 n x p')). Qed.
Lemma lem7332458 (n : nat) (x : real) (p' : Prop) (q' : Prop) : term52 n x p' q'.
Proof. exact (@lem7332457 n x p' q'). Qed.
Lemma lem7332459 (n : nat) (x : real) (p' : Prop) (q' : Prop) : (term52 n x p' q') = (term53 n x p' q').
Proof. exact (eq_refl (term52 n x p' q')). Qed.
Lemma lem7332460 (n : nat) (x : real) (p' : Prop) (q' : Prop) : term53 n x p' q'.
Proof. exact (EQ_MP (@lem7332459 n x p' q') (@lem7332458 n x p' q')). Qed.
Lemma lem7332461 (n : nat) : (term9 n) = (term9 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem7332462 (x : real) (n : nat) (q' : Prop) : term54 x n q'.
Proof. exact (@lem7332460 n x (term9 n) q'). Qed.
Lemma lem7332463 (x : real) (n : nat) (q' : Prop) : term55 x n q'.
Proof. exact (@lem7332462 x n q' (@lem7332461 n)). Qed.
Lemma lem7332464 (n : nat) (h1 : term9 n) : term9 n.
Proof. exact (h1). Qed.
Lemma lem7332465 (n : nat) : (term9 n) = ((term9 n) = True).
Proof. exact (@lem7 (term9 n)). Qed.
Lemma lem7332470 (n : nat) (x : real) : term8 n x.
Proof. exact (fun h0 : term9 n => @lem7332380 x n h0). Qed.
Lemma lem7332472 (n : nat) (h1 : term9 n) : (term9 n) = True.
Proof. exact (EQ_MP (@lem7332465 n) (@lem7332464 n h1)). Qed.
Lemma lem7332473 (n : nat) (h1 : term9 n) : True = (term9 n).
Proof. exact (SYM (@lem7332472 n h1)). Qed.
Lemma lem7332474 (n : nat) (h1 : term9 n) : term9 n.
Proof. exact (EQ_MP (@lem7332473 n h1) (@lem0)). Qed.
Lemma lem7332475 (x : real) (n : nat) (h1 : term9 n) : (term10 x n) = (term11 n x).
Proof. exact (@lem7332470 n x (@lem7332474 n h1)). Qed.
Lemma lem7332591 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7332592 (x : real) (n : nat) (h1 : term9 n) : (term24 x n) = (term56 n x).
Proof. exact (MK_COMB (@lem7332591) (@lem7332475 x n h1)). Qed.
Lemma lem7332708 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7332709 (x : real) (n : nat) (h1 : term9 n) : (term27 x n) = (term57 n x).
Proof. exact (MK_COMB (@lem7332708) (@lem7332592 x n h1)). Qed.
Lemma lem7332940 (n : nat) (x : real) : (term34 n x) = (term34 n x).
Proof. exact (eq_refl (term34 n x)). Qed.
Lemma lem7332941 (x : real) (n : nat) (h1 : term9 n) : ((term24 x n) = (term34 n x)) = ((term56 n x) = (term34 n x)).
Proof. exact (MK_COMB (@lem7332709 x n h1) (@lem7332940 n x)). Qed.
Lemma lem7333174 (n : nat) (x : real) : term58 n x.
Proof. exact (fun h0 : term9 n => @lem7332941 x n h0). Qed.
Lemma lem7333175 (n : nat) (x : real) : term59 n x.
Proof. exact (@lem7332463 x n ((term56 n x) = (term34 n x))). Qed.
Lemma lem7333176 (n : nat) (x : real) : (term37 n x) = (term60 n x).
Proof. exact (@lem7333175 n x (@lem7333174 n x)). Qed.
Lemma lem7333664 (x : real) : (term39 x) = (term61 x).
Proof. exact (fun_ext (fun n : nat => @lem7333176 n x)). Qed.
Lemma lem7334152 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7334153 (x : real) : (term41 x) = (term62 x).
Proof. exact (MK_COMB (@lem7334152) (@lem7333664 x)). Qed.
Lemma lem7334645 : term43 = term63.
Proof. exact (fun_ext (fun x : real => @lem7334153 x)). Qed.
Lemma lem7335137 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7335138 : term45 = term64.
Proof. exact (MK_COMB (@lem7335137) (@lem7334645)). Qed.
Lemma lem7335634 : term64 = term45.
Proof. exact (SYM (@lem7335138)). Qed.
Lemma lem7335648 (x : real) (y : real) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem7332371 x y) (@lem7332370 x y)). Qed.
Lemma lem7335649 (n : nat) (x : real) : (term34 n x) = (term56 n x).
Proof. exact (@lem7335648 (term65 x) (term32 n x)). Qed.
Lemma lem7335650 (n : nat) (x : real) : (term57 n x) = (term57 n x).
Proof. exact (eq_refl (term57 n x)). Qed.
Lemma lem7335651 (n : nat) (x : real) : ((term56 n x) = (term34 n x)) = ((term56 n x) = (term56 n x)).
Proof. exact (MK_COMB (@lem7335650 n x) (@lem7335649 n x)). Qed.
Lemma lem7335653 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7335654 (x : real) : (x = x) = True.
Proof. exact (@lem7335653 real x). Qed.
Lemma lem7335655 (n : nat) (x : real) : ((term56 n x) = (term56 n x)) = True.
Proof. exact (@lem7335654 (term56 n x)). Qed.
Lemma lem7335656 (n : nat) (x : real) : ((term56 n x) = (term34 n x)) = True.
Proof. exact (TRANS (@lem7335651 n x) (@lem7335655 n x)). Qed.
Lemma lem7335657 (n : nat) : (term35 n) = (term35 n).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem7335658 (x : real) (n : nat) : (term60 n x) = (term66 n).
Proof. exact (MK_COMB (@lem7335657 n) (@lem7335656 n x)). Qed.
Lemma lem7335660 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7335661 (n : nat) : (term66 n) = True.
Proof. exact (@lem7335660 (term9 n)). Qed.
Lemma lem7335662 (n : nat) (x : real) : (term60 n x) = True.
Proof. exact (TRANS (@lem7335658 x n) (@lem7335661 n)). Qed.
Lemma lem7335663 (x : real) : (term61 x) = term67.
Proof. exact (fun_ext (fun n : nat => @lem7335662 n x)). Qed.
Lemma lem7335664 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7335665 (x : real) : (term62 x) = term68.
Proof. exact (MK_COMB (@lem7335664) (@lem7335663 x)). Qed.
Lemma lem7335667 {A : Type'} (t : Prop) : (term69 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7335668 (t : Prop) : (term70 t) = t.
Proof. exact (@lem7335667 nat t). Qed.
Lemma lem7335669 : term68 = True.
Proof. exact (@lem7335668 True). Qed.
Lemma lem7335670 (x : real) : (term62 x) = True.
Proof. exact (TRANS (@lem7335665 x) (@lem7335669)). Qed.
Lemma lem7335671 : term63 = term71.
Proof. exact (fun_ext (fun x : real => @lem7335670 x)). Qed.
Lemma lem7335672 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7335673 : term64 = term72.
Proof. exact (MK_COMB (@lem7335672) (@lem7335671)). Qed.
Lemma lem7335675 {A : Type'} (t : Prop) : (term69 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7335676 (t : Prop) : (term73 t) = t.
Proof. exact (@lem7335675 real t). Qed.
Lemma lem7335677 : term72 = True.
Proof. exact (@lem7335676 True). Qed.
Lemma lem7335678 : term64 = True.
Proof. exact (TRANS (@lem7335673) (@lem7335677)). Qed.
Lemma lem7335679 : True = term64.
Proof. exact (SYM (@lem7335678)). Qed.
Lemma lem7335680 : term64.
Proof. exact (EQ_MP (@lem7335679) (@lem0)). Qed.
Lemma lem7335681 : term45.
Proof. exact (EQ_MP (@lem7335634) (@lem7335680)). Qed.
Lemma lem7335682 : term44.
Proof. exact (EQ_MP (@lem7332439) (@lem7335681)). Qed.
