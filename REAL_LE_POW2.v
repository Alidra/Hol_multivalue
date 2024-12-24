Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_POW2_term_abbrevs.
Require Import LE_0_spec.
Require Import REAL_POW_MONO_spec.
Require Import thm0_spec.
Require Import thm1339240_spec.
Require Import thm1339577_spec.
Require Import thm1340282_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm517422_spec.
Require Import thm519779_spec.
Require Import thm520356_spec.
Require Import thm7_spec.
Lemma lem1642682 (x : real) : term0 x.
Proof. exact (@lem1339240 x). Qed.
Lemma lem1642683 (x : real) : (term0 x) = (real_le x x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1642684 (x : real) : real_le x x.
Proof. exact (EQ_MP (@lem1642683 x) (@lem1642682 x)). Qed.
Lemma lem1642685 (x : real) : (real_le x x) = ((real_le x x) = True).
Proof. exact (@lem7 (real_le x x)). Qed.
Lemma lem1642903 : term1.
Proof. exact (EQ_MP (@lem520356) (@lem0)). Qed.
Lemma lem1642904 : term2.
Proof. exact (proj2 (@lem1642903)). Qed.
Lemma lem1642905 : term3.
Proof. exact (proj2 (@lem1642904)). Qed.
Lemma lem1642906 : term4.
Proof. exact (proj2 (@lem1642905)). Qed.
Lemma lem1642907 : term5.
Proof. exact (proj2 (@lem1642906)). Qed.
Lemma lem1642908 : term6.
Proof. exact (proj2 (@lem1642907)). Qed.
Lemma lem1642940 : term7.
Proof. exact (proj1 (@lem1642908)). Qed.
Lemma lem1642941 (n : nat) : term8 n.
Proof. exact (@lem1642940 n). Qed.
Lemma lem1642942 (n : nat) : (term8 n) = ((term9 n) = True).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem1642964 : term10.
Proof. exact (EQ_MP (@lem517422) (@lem519779)). Qed.
Lemma lem1642965 : term11.
Proof. exact (proj2 (@lem1642964)). Qed.
Lemma lem1642966 : term12.
Proof. exact (proj2 (@lem1642965)). Qed.
Lemma lem1642967 : term13.
Proof. exact (proj2 (@lem1642966)). Qed.
Lemma lem1642968 : term14.
Proof. exact (proj2 (@lem1642967)). Qed.
Lemma lem1642969 : term15.
Proof. exact (proj2 (@lem1642968)). Qed.
Lemma lem1642970 : term16.
Proof. exact (proj2 (@lem1642969)). Qed.
Lemma lem1642971 : term17.
Proof. exact (proj2 (@lem1642970)). Qed.
Lemma lem1642972 : term18.
Proof. exact (proj2 (@lem1642971)). Qed.
Lemma lem1642980 : term19.
Proof. exact (proj1 (@lem1642972)). Qed.
Lemma lem1642981 (m : nat) : term20 m.
Proof. exact (@lem1642980 m). Qed.
Lemma lem1642982 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem1642983 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem1642982 m) (@lem1642981 m)). Qed.
Lemma lem1642984 (m : nat) (n : nat) : term22 m n.
Proof. exact (@lem1642983 m n). Qed.
Lemma lem1642985 (m : nat) (n : nat) : (term22 m n) = ((term23 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem1643018 : term24.
Proof. exact (proj1 (@lem1642964)). Qed.
Lemma lem1643019 (m : nat) : term25 m.
Proof. exact (@lem1643018 m). Qed.
Lemma lem1643020 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem1643021 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem1643020 m) (@lem1643019 m)). Qed.
Lemma lem1643022 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem1643021 m n). Qed.
Lemma lem1643023 (m : nat) (n : nat) : (term27 m n) = ((term28 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem1643336 (m : nat) : term29 m.
Proof. exact (@lem1340282 m). Qed.
Lemma lem1643337 (m : nat) : (term29 m) = (term30 m).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem1643338 (m : nat) : term30 m.
Proof. exact (EQ_MP (@lem1643337 m) (@lem1643336 m)). Qed.
Lemma lem1643339 (m : nat) (n : nat) : term31 m n.
Proof. exact (@lem1643338 m n). Qed.
Lemma lem1643340 (m : nat) (n : nat) : (term31 m n) = ((term32 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term31 m n)). Qed.
Lemma lem1643342 (n : nat) : term33 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem1643343 (n : nat) : (term33 n) = (term34 n).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem1643344 (n : nat) : term34 n.
Proof. exact (EQ_MP (@lem1643343 n) (@lem1643342 n)). Qed.
Lemma lem1643345 (n : nat) : (term34 n) = ((term34 n) = True).
Proof. exact (@lem7 (term34 n)). Qed.
Lemma lem1643347 (m : nat) : term35 m.
Proof. exact (@lem1637789 m). Qed.
Lemma lem1643348 (m : nat) : (term35 m) = (term36 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem1643349 (m : nat) : term36 m.
Proof. exact (EQ_MP (@lem1643348 m) (@lem1643347 m)). Qed.
Lemma lem1643350 (m : nat) (n : nat) : term37 m n.
Proof. exact (@lem1643349 m n). Qed.
Lemma lem1643351 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem1643352 (m : nat) (n : nat) : term38 m n.
Proof. exact (EQ_MP (@lem1643351 m n) (@lem1643350 m n)). Qed.
Lemma lem1643353 (m : nat) (n : nat) (x : real) : term39 m n x.
Proof. exact (@lem1643352 m n x). Qed.
Lemma lem1643354 (m : nat) (x : real) (n : nat) : (term39 m n x) = (term40 m x n).
Proof. exact (eq_refl (term39 m n x)). Qed.
Lemma lem1643355 (m : nat) (x : real) (n : nat) : term40 m x n.
Proof. exact (EQ_MP (@lem1643354 m x n) (@lem1643353 m n x)). Qed.
Lemma lem1643356 (x : real) (m : nat) (n : nat) (h1 : term41 x m n) : term41 x m n.
Proof. exact (h1). Qed.
Lemma lem1643357 (x : real) (m : nat) (n : nat) (h1 : term41 x m n) : term42 m x n.
Proof. exact (@lem1643355 m x n (@lem1643356 x m n h1)). Qed.
Lemma lem1643358 (m : nat) (x : real) (n : nat) : (term42 m x n) = ((term42 m x n) = True).
Proof. exact (@lem7 (term42 m x n)). Qed.
Lemma lem1643359 (x : real) (m : nat) (n : nat) (h1 : term41 x m n) : (term42 m x n) = True.
Proof. exact (EQ_MP (@lem1643358 m x n) (@lem1643357 x m n h1)). Qed.
Lemma lem1643365 (h1 : term43) : term43.
Proof. exact (h1). Qed.
Lemma lem1643366 (x : real) (h1 : term43) : term44 x.
Proof. exact (@lem1643365 h1 x). Qed.
Lemma lem1643367 (x : real) : (term44 x) = (term45 x).
Proof. exact (eq_refl (term44 x)). Qed.
Lemma lem1643368 (x : real) (h1 : term43) : term45 x.
Proof. exact (EQ_MP (@lem1643367 x) (@lem1643366 x h1)). Qed.
Lemma lem1643369 (x : real) (y : real) (h1 : term43) : term46 x y.
Proof. exact (@lem1643368 x h1 y). Qed.
Lemma lem1643370 (y : real) (x : real) : (term46 x y) = (term47 y x).
Proof. exact (eq_refl (term46 x y)). Qed.
Lemma lem1643371 (y : real) (x : real) (h1 : term43) : term47 y x.
Proof. exact (EQ_MP (@lem1643370 y x) (@lem1643369 x y h1)). Qed.
Lemma lem1643372 (y : real) (x : real) (z : real) (h1 : term43) : term48 y x z.
Proof. exact (@lem1643371 y x h1 z). Qed.
Lemma lem1643373 (y : real) (x : real) (z : real) : (term48 y x z) = (term49 y x z).
Proof. exact (eq_refl (term48 y x z)). Qed.
Lemma lem1643374 (y : real) (x : real) (z : real) (h1 : term43) : term49 y x z.
Proof. exact (EQ_MP (@lem1643373 y x z) (@lem1643372 y x z h1)). Qed.
Lemma lem1643375 (x : real) (y : real) (z : real) (h1 : term50 x y z) : term50 x y z.
Proof. exact (h1). Qed.
Lemma lem1643376 (x : real) (y : real) (z : real) (h1 : term43) (h2 : term50 x y z) : real_le x z.
Proof. exact (@lem1643374 y x z h1 (@lem1643375 x y z h2)). Qed.
Lemma lem1643377 (x : real) (y : real) (z : real) (h1 : term50 x y z) : term51 x z.
Proof. exact (fun h0 : term43 => @lem1643376 x y z h0 h1). Qed.
Lemma lem1643378 (x : real) (z : real) (h1 : term52 x z) : term52 x z.
Proof. exact (h1). Qed.
Lemma lem1643379 (x : real) (z : real) (h1 : term52 x z) : term51 x z.
Proof. exact (ex_elim (@lem1643378 x z h1) (fun y : real => fun h0 : term53 x z y => @lem1643377 x y z h0)). Qed.
Lemma lem1643380 (h1 : term43) : term43.
Proof. exact (h1). Qed.
Lemma lem1643381 (x : real) (z : real) (h1 : term43) (h2 : term52 x z) : real_le x z.
Proof. exact (@lem1643379 x z h2 (@lem1643380 h1)). Qed.
Lemma lem1643382 (x : real) (z : real) (h1 : term43) : term54 x z.
Proof. exact (fun h0 : term52 x z => @lem1643381 x z h1 h0). Qed.
Lemma lem1643383 (x : real) (h1 : term43) : term55 x.
Proof. exact (fun z : real => @lem1643382 x z h1). Qed.
Lemma lem1643384 (h1 : term43) : term56.
Proof. exact (fun x : real => @lem1643383 x h1). Qed.
Lemma lem1643385 : term57.
Proof. exact (fun h0 : term43 => @lem1643384 h0). Qed.
Lemma lem1643386 : term56.
Proof. exact (@lem1643385 (@lem1339577)). Qed.
Lemma lem1643387 (x : real) : term58 x.
Proof. exact (@lem1643386 x). Qed.
Lemma lem1643388 (x : real) : (term58 x) = (term55 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1643389 (x : real) : term55 x.
Proof. exact (EQ_MP (@lem1643388 x) (@lem1643387 x)). Qed.
Lemma lem1643390 (x : real) (z : real) : term59 x z.
Proof. exact (@lem1643389 x z). Qed.
Lemma lem1643391 (x : real) (z : real) : (term59 x z) = (term54 x z).
Proof. exact (eq_refl (term59 x z)). Qed.
Lemma lem1643394 (x : real) (z : real) : term54 x z.
Proof. exact (EQ_MP (@lem1643391 x z) (@lem1643390 x z)). Qed.
Lemma lem1643395 (n : nat) : term60 n.
Proof. exact (@lem1643394 term61 (term62 n)). Qed.
Lemma lem1643399 (m : nat) (x : real) (n : nat) : term63 m x n.
Proof. exact (fun h0 : term41 x m n => @lem1643359 x m n h0). Qed.
Lemma lem1643400 (n : nat) : term64 n.
Proof. exact (@lem1643399 (NUMERAL 0) term65 n). Qed.
Lemma lem1643404 (m : nat) (n : nat) : (term32 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1643340 m n) (@lem1643339 m n)). Qed.
Lemma lem1643405 : term66 = term67.
Proof. exact (@lem1643404 term68 term69). Qed.
Lemma lem1643407 (m : nat) (n : nat) : (term28 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1643023 m n) (@lem1643022 m n)). Qed.
Lemma lem1643408 : term67 = term70.
Proof. exact (@lem1643407 (BIT1 0) term71). Qed.
Lemma lem1643410 (m : nat) (n : nat) : (term23 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1642985 m n) (@lem1642984 m n)). Qed.
Lemma lem1643411 : term70 = term72.
Proof. exact (@lem1643410 0 (BIT1 0)). Qed.
Lemma lem1643413 (n : nat) : (term9 n) = True.
Proof. exact (EQ_MP (@lem1642942 n) (@lem1642941 n)). Qed.
Lemma lem1643414 : term72 = True.
Proof. exact (@lem1643413 0). Qed.
Lemma lem1643415 : term70 = True.
Proof. exact (TRANS (@lem1643411) (@lem1643414)). Qed.
Lemma lem1643416 : term67 = True.
Proof. exact (TRANS (@lem1643408) (@lem1643415)). Qed.
Lemma lem1643417 : term66 = True.
Proof. exact (TRANS (@lem1643405) (@lem1643416)). Qed.
Lemma lem1643418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1643419 : term73 = (and True).
Proof. exact (MK_COMB (@lem1643418) (@lem1643417)). Qed.
Lemma lem1643421 (n : nat) : (term34 n) = True.
Proof. exact (EQ_MP (@lem1643345 n) (@lem1643344 n)). Qed.
Lemma lem1643422 (n : nat) : (term74 n) = (True /\ True).
Proof. exact (MK_COMB (@lem1643419) (@lem1643421 n)). Qed.
Lemma lem1643424 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1643425 : (True /\ True) = True.
Proof. exact (@lem1643424 True). Qed.
Lemma lem1643426 (n : nat) : (term74 n) = True.
Proof. exact (TRANS (@lem1643422 n) (@lem1643425)). Qed.
Lemma lem1643427 (n : nat) : True = (term74 n).
Proof. exact (SYM (@lem1643426 n)). Qed.
Lemma lem1643428 (n : nat) : term74 n.
Proof. exact (EQ_MP (@lem1643427 n) (@lem0)). Qed.
Lemma lem1643429 (n : nat) : (term75 n) = True.
Proof. exact (@lem1643400 n (@lem1643428 n)). Qed.
Lemma lem1643430 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem1643431 (n : nat) : (term77 n) = term78.
Proof. exact (MK_COMB (@lem1643430) (@lem1643429 n)). Qed.
Lemma lem1643433 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1643434 : term78 = term79.
Proof. exact (@lem1643433 term79). Qed.
Lemma lem1643435 (n : nat) : (term77 n) = term79.
Proof. exact (TRANS (@lem1643431 n) (@lem1643434)). Qed.
Lemma lem1643436 (n : nat) : term79 = (term77 n).
Proof. exact (SYM (@lem1643435 n)). Qed.
Lemma lem1643440 (x : real) : (term80 x) = term61.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1643441 : term81 = term61.
Proof. exact (@lem1643440 term65). Qed.
Lemma lem1643442 : term82 = term82.
Proof. exact (eq_refl term82). Qed.
Lemma lem1643443 : term79 = term83.
Proof. exact (MK_COMB (@lem1643442) (@lem1643441)). Qed.
Lemma lem1643445 (x : real) : (real_le x x) = True.
Proof. exact (EQ_MP (@lem1642685 x) (@lem1642684 x)). Qed.
Lemma lem1643446 : term83 = True.
Proof. exact (@lem1643445 term61). Qed.
Lemma lem1643447 : term79 = True.
Proof. exact (TRANS (@lem1643443) (@lem1643446)). Qed.
Lemma lem1643448 : True = term79.
Proof. exact (SYM (@lem1643447)). Qed.
Lemma lem1643449 : term79.
Proof. exact (EQ_MP (@lem1643448) (@lem0)). Qed.
Lemma lem1643450 (n : nat) : term77 n.
Proof. exact (EQ_MP (@lem1643436 n) (@lem1643449)). Qed.
Lemma lem1643451 (n : nat) : term84 n.
Proof. exact (ex_intro (term85 n) term81 (@lem1643450 n)). Qed.
Lemma lem1643452 (n : nat) : term86 n.
Proof. exact (@lem1643395 n (@lem1643451 n)). Qed.
Lemma lem1643457 : term87.
Proof. exact (fun n : nat => @lem1643452 n). Qed.
