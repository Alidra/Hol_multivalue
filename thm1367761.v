Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1367761_term_abbrevs.
Require Import REAL_ADD_RINV_spec.
Require Import REAL_NEG_ADD_spec.
Require Import thm0_spec.
Require Import thm1338238_spec.
Require Import thm1338438_spec.
Require Import thm1338512_spec.
Require Import thm1338588_spec.
Require Import thm1340339_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1367304 (x : real) : term0 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1367305 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1367307 (x : real) : term2 x.
Proof. exact (@lem1353037 x). Qed.
Lemma lem1367308 (x : real) : (term2 x) = ((term3 x) = term4).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1367310 (x : real) : term0 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1367311 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1367313 (x : real) : term5 x.
Proof. exact (@lem1338588 x). Qed.
Lemma lem1367314 (x : real) : (term5 x) = ((term6 x) = term4).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1367316 (x : real) : term7 x.
Proof. exact (@lem1338438 x). Qed.
Lemma lem1367317 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1367318 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem1367317 x) (@lem1367316 x)). Qed.
Lemma lem1367319 (x : real) (y : real) : term9 x y.
Proof. exact (@lem1367318 x y). Qed.
Lemma lem1367320 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1367321 (x : real) (y : real) : term10 x y.
Proof. exact (EQ_MP (@lem1367320 x y) (@lem1367319 x y)). Qed.
Lemma lem1367322 (x : real) (y : real) (z : real) : term11 x y z.
Proof. exact (@lem1367321 x y z). Qed.
Lemma lem1367323 (x : real) (y : real) (z : real) : (term11 x y z) = ((term12 x y z) = (term13 x y z)).
Proof. exact (eq_refl (term11 x y z)). Qed.
Lemma lem1367325 (x : real) : term14 x.
Proof. exact (@lem1338238 x). Qed.
Lemma lem1367326 (x : real) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1367327 (x : real) : term15 x.
Proof. exact (EQ_MP (@lem1367326 x) (@lem1367325 x)). Qed.
Lemma lem1367328 (x : real) (y : real) : term16 x y.
Proof. exact (@lem1367327 x y). Qed.
Lemma lem1367329 (y : real) (x : real) : (term16 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1367331 (x : real) : term0 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1367332 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1367334 (x : real) : term2 x.
Proof. exact (@lem1353037 x). Qed.
Lemma lem1367335 (x : real) : (term2 x) = ((term3 x) = term4).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1367337 (x : real) : term0 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1367338 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1367340 (x : real) : term5 x.
Proof. exact (@lem1338588 x). Qed.
Lemma lem1367341 (x : real) : (term5 x) = ((term6 x) = term4).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1367343 (x : real) : term7 x.
Proof. exact (@lem1338438 x). Qed.
Lemma lem1367344 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1367345 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem1367344 x) (@lem1367343 x)). Qed.
Lemma lem1367346 (x : real) (y : real) : term9 x y.
Proof. exact (@lem1367345 x y). Qed.
Lemma lem1367347 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1367348 (x : real) (y : real) : term10 x y.
Proof. exact (EQ_MP (@lem1367347 x y) (@lem1367346 x y)). Qed.
Lemma lem1367349 (x : real) (y : real) (z : real) : term11 x y z.
Proof. exact (@lem1367348 x y z). Qed.
Lemma lem1367350 (x : real) (y : real) (z : real) : (term11 x y z) = ((term12 x y z) = (term13 x y z)).
Proof. exact (eq_refl (term11 x y z)). Qed.
Lemma lem1367354 (m : nat) (n : nat) (h1 : (term17 m n) = (term18 m n)) : (term17 m n) = (term18 m n).
Proof. exact (h1). Qed.
Lemma lem1367355 (m : nat) (n : nat) (h1 : (term17 m n) = (term18 m n)) : (term18 m n) = (term17 m n).
Proof. exact (SYM (@lem1367354 m n h1)). Qed.
Lemma lem1367356 (m : nat) (n : nat) (h1 : (term18 m n) = (term17 m n)) : (term18 m n) = (term17 m n).
Proof. exact (h1). Qed.
Lemma lem1367357 (m : nat) (n : nat) (h1 : (term18 m n) = (term17 m n)) : (term17 m n) = (term18 m n).
Proof. exact (SYM (@lem1367356 m n h1)). Qed.
Lemma lem1367358 (m : nat) (n : nat) : ((term17 m n) = (term18 m n)) = ((term18 m n) = (term17 m n)).
Proof. exact (prop_ext (fun h1 : (term17 m n) = (term18 m n) => @lem1367355 m n h1) (fun h1 : (term18 m n) = (term17 m n) => @lem1367357 m n h1)). Qed.
Lemma lem1367359 (m : nat) : (term19 m) = (term20 m).
Proof. exact (fun_ext (fun n : nat => @lem1367358 m n)). Qed.
Lemma lem1367360 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1367361 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem1367360) (@lem1367359 m)). Qed.
Lemma lem1367362 : term23 = term24.
Proof. exact (fun_ext (fun m : nat => @lem1367361 m)). Qed.
Lemma lem1367363 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1367364 : term25 = term26.
Proof. exact (MK_COMB (@lem1367363) (@lem1367362)). Qed.
Lemma lem1367365 : term26.
Proof. exact (EQ_MP (@lem1367364) (@lem1340339)). Qed.
Lemma lem1367366 (x : real) : term27 x.
Proof. exact (@lem1361095 x). Qed.
Lemma lem1367367 (x : real) : (term27 x) = (term28 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1367368 (x : real) : term28 x.
Proof. exact (EQ_MP (@lem1367367 x) (@lem1367366 x)). Qed.
Lemma lem1367369 (x : real) (y : real) : term29 x y.
Proof. exact (@lem1367368 x y). Qed.
Lemma lem1367370 (x : real) (y : real) : (term29 x y) = ((term30 x y) = (term31 x y)).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem1367372 (m : nat) : term32 m.
Proof. exact (@lem1367365 m). Qed.
Lemma lem1367373 (m : nat) : (term32 m) = (term22 m).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem1367374 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1367373 m) (@lem1367372 m)). Qed.
Lemma lem1367375 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem1367374 m n). Qed.
Lemma lem1367376 (m : nat) (n : nat) : (term33 m n) = ((term18 m n) = (term17 m n)).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1367383 (m : nat) (n : nat) : (term18 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem1367376 m n) (@lem1367375 m n)). Qed.
Lemma lem1367384 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1367385 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem1367384) (@lem1367383 m n)). Qed.
Lemma lem1367387 (x : real) (y : real) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem1367370 x y) (@lem1367369 x y)). Qed.
Lemma lem1367388 (m : nat) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (@lem1367387 (real_of_num m) (real_of_num n)). Qed.
Lemma lem1367389 (m : nat) (n : nat) : (term34 m n) = (term36 m n).
Proof. exact (TRANS (@lem1367385 m n) (@lem1367388 m n)). Qed.
Lemma lem1367390 (m : nat) (n : nat) : (term37 m n) = (term37 m n).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem1367391 (m : nat) (n : nat) : ((term36 m n) = (term34 m n)) = ((term36 m n) = (term36 m n)).
Proof. exact (MK_COMB (@lem1367390 m n) (@lem1367389 m n)). Qed.
Lemma lem1367393 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367394 (x : real) : (x = x) = True.
Proof. exact (@lem1367393 real x). Qed.
Lemma lem1367395 (m : nat) (n : nat) : ((term36 m n) = (term36 m n)) = True.
Proof. exact (@lem1367394 (term36 m n)). Qed.
Lemma lem1367396 (m : nat) (n : nat) : ((term36 m n) = (term34 m n)) = True.
Proof. exact (TRANS (@lem1367391 m n) (@lem1367395 m n)). Qed.
Lemma lem1367397 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367398 (m : nat) (n : nat) : (term38 m n) = (and True).
Proof. exact (MK_COMB (@lem1367397) (@lem1367396 m n)). Qed.
Lemma lem1367404 (m : nat) (n : nat) : (term18 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem1367376 m n) (@lem1367375 m n)). Qed.
Lemma lem1367405 (m : nat) : (term39 m) = (term39 m).
Proof. exact (eq_refl (term39 m)). Qed.
Lemma lem1367406 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (MK_COMB (@lem1367405 m) (@lem1367404 m n)). Qed.
Lemma lem1367407 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367408 (m : nat) (n : nat) : (term42 m n) = (term43 m n).
Proof. exact (MK_COMB (@lem1367407) (@lem1367406 m n)). Qed.
Lemma lem1367409 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem1367410 (m : nat) (n : nat) : ((term40 m n) = (real_of_num n)) = ((term41 m n) = (real_of_num n)).
Proof. exact (MK_COMB (@lem1367408 m n) (@lem1367409 n)). Qed.
Lemma lem1367413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367414 (m : nat) (n : nat) : (term44 m n) = (term45 m n).
Proof. exact (MK_COMB (@lem1367413) (@lem1367410 m n)). Qed.
Lemma lem1367420 (m : nat) (n : nat) : (term18 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem1367376 m n) (@lem1367375 m n)). Qed.
Lemma lem1367421 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1367422 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem1367421) (@lem1367420 m n)). Qed.
Lemma lem1367424 (x : real) (y : real) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem1367370 x y) (@lem1367369 x y)). Qed.
Lemma lem1367425 (m : nat) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (@lem1367424 (real_of_num m) (real_of_num n)). Qed.
Lemma lem1367426 (m : nat) (n : nat) : (term34 m n) = (term36 m n).
Proof. exact (TRANS (@lem1367422 m n) (@lem1367425 m n)). Qed.
Lemma lem1367427 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1367428 (m : nat) (n : nat) : (term46 m n) = (term47 m n).
Proof. exact (MK_COMB (@lem1367427) (@lem1367426 m n)). Qed.
Lemma lem1367429 (m : nat) : (real_of_num m) = (real_of_num m).
Proof. exact (eq_refl (real_of_num m)). Qed.
Lemma lem1367430 (n : nat) (m : nat) : (term48 n m) = (term49 n m).
Proof. exact (MK_COMB (@lem1367428 m n) (@lem1367429 m)). Qed.
Lemma lem1367431 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367432 (n : nat) (m : nat) : (term50 n m) = (term51 n m).
Proof. exact (MK_COMB (@lem1367431) (@lem1367430 n m)). Qed.
Lemma lem1367433 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem1367434 (m : nat) (n : nat) : ((term48 n m) = (term52 n)) = ((term49 n m) = (term52 n)).
Proof. exact (MK_COMB (@lem1367432 n m) (@lem1367433 n)). Qed.
Lemma lem1367437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367438 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (MK_COMB (@lem1367437) (@lem1367434 m n)). Qed.
Lemma lem1367444 (m : nat) (n : nat) : (term18 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem1367376 m n) (@lem1367375 m n)). Qed.
Lemma lem1367445 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1367446 (m : nat) (n : nat) : (term55 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem1367445) (@lem1367444 m n)). Qed.
Lemma lem1367447 (m : nat) : (term52 m) = (term52 m).
Proof. exact (eq_refl (term52 m)). Qed.
Lemma lem1367448 (n : nat) (m : nat) : (term57 n m) = (term58 n m).
Proof. exact (MK_COMB (@lem1367446 m n) (@lem1367447 m)). Qed.
Lemma lem1367449 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367450 (n : nat) (m : nat) : (term59 n m) = (term60 n m).
Proof. exact (MK_COMB (@lem1367449) (@lem1367448 n m)). Qed.
Lemma lem1367451 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem1367452 (m : nat) (n : nat) : ((term57 n m) = (real_of_num n)) = ((term58 n m) = (real_of_num n)).
Proof. exact (MK_COMB (@lem1367450 n m) (@lem1367451 n)). Qed.
Lemma lem1367455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367456 (m : nat) (n : nat) : (term61 m n) = (term62 m n).
Proof. exact (MK_COMB (@lem1367455) (@lem1367452 m n)). Qed.
Lemma lem1367462 (m : nat) (n : nat) : (term18 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem1367376 m n) (@lem1367375 m n)). Qed.
Lemma lem1367463 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1367464 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem1367463) (@lem1367462 m n)). Qed.
Lemma lem1367466 (x : real) (y : real) : (term30 x y) = (term31 x y).
Proof. exact (EQ_MP (@lem1367370 x y) (@lem1367369 x y)). Qed.
Lemma lem1367467 (m : nat) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (@lem1367466 (real_of_num m) (real_of_num n)). Qed.
Lemma lem1367468 (m : nat) (n : nat) : (term34 m n) = (term36 m n).
Proof. exact (TRANS (@lem1367464 m n) (@lem1367467 m n)). Qed.
Lemma lem1367469 (m : nat) : (term63 m) = (term63 m).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem1367470 (m : nat) (n : nat) : (term64 m n) = (term65 m n).
Proof. exact (MK_COMB (@lem1367469 m) (@lem1367468 m n)). Qed.
Lemma lem1367471 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367472 (m : nat) (n : nat) : (term66 m n) = (term67 m n).
Proof. exact (MK_COMB (@lem1367471) (@lem1367470 m n)). Qed.
Lemma lem1367473 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem1367474 (m : nat) (n : nat) : ((term64 m n) = (term52 n)) = ((term65 m n) = (term52 n)).
Proof. exact (MK_COMB (@lem1367472 m n) (@lem1367473 n)). Qed.
Lemma lem1367477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367478 (m : nat) (n : nat) : (term68 m n) = (term69 m n).
Proof. exact (MK_COMB (@lem1367477) (@lem1367474 m n)). Qed.
Lemma lem1367482 (m : nat) (n : nat) : (term18 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem1367376 m n) (@lem1367375 m n)). Qed.
Lemma lem1367483 (m : nat) (n : nat) : (term70 m n) = (term70 m n).
Proof. exact (eq_refl (term70 m n)). Qed.
Lemma lem1367484 (m : nat) (n : nat) : ((term17 m n) = (term18 m n)) = ((term17 m n) = (term17 m n)).
Proof. exact (MK_COMB (@lem1367483 m n) (@lem1367482 m n)). Qed.
Lemma lem1367486 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367487 (x : real) : (x = x) = True.
Proof. exact (@lem1367486 real x). Qed.
Lemma lem1367488 (m : nat) (n : nat) : ((term17 m n) = (term17 m n)) = True.
Proof. exact (@lem1367487 (term17 m n)). Qed.
Lemma lem1367489 (m : nat) (n : nat) : ((term17 m n) = (term18 m n)) = True.
Proof. exact (TRANS (@lem1367484 m n) (@lem1367488 m n)). Qed.
Lemma lem1367490 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (MK_COMB (@lem1367478 m n) (@lem1367489 m n)). Qed.
Lemma lem1367492 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1367493 (m : nat) (n : nat) : (term72 m n) = ((term65 m n) = (term52 n)).
Proof. exact (@lem1367492 ((term65 m n) = (term52 n))). Qed.
Lemma lem1367496 (m : nat) (n : nat) : (term71 m n) = ((term65 m n) = (term52 n)).
Proof. exact (TRANS (@lem1367490 m n) (@lem1367493 m n)). Qed.
Lemma lem1367497 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (MK_COMB (@lem1367456 m n) (@lem1367496 m n)). Qed.
Lemma lem1367500 (m : nat) (n : nat) : (term75 m n) = (term76 m n).
Proof. exact (MK_COMB (@lem1367438 m n) (@lem1367497 m n)). Qed.
Lemma lem1367503 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (MK_COMB (@lem1367414 m n) (@lem1367500 m n)). Qed.
Lemma lem1367506 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (MK_COMB (@lem1367398 m n) (@lem1367503 m n)). Qed.
Lemma lem1367508 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1367509 (m : nat) (n : nat) : (term80 m n) = (term78 m n).
Proof. exact (@lem1367508 (term78 m n)). Qed.
Lemma lem1367524 (m : nat) (n : nat) : (term79 m n) = (term78 m n).
Proof. exact (TRANS (@lem1367506 m n) (@lem1367509 m n)). Qed.
Lemma lem1367525 (m : nat) (n : nat) : (term78 m n) = (term79 m n).
Proof. exact (SYM (@lem1367524 m n)). Qed.
Lemma lem1367533 (x : real) (y : real) (z : real) : (term12 x y z) = (term13 x y z).
Proof. exact (EQ_MP (@lem1367350 x y z) (@lem1367349 x y z)). Qed.
Lemma lem1367534 (m : nat) (n : nat) : (term41 m n) = (term81 m n).
Proof. exact (@lem1367533 (term52 m) (real_of_num m) (real_of_num n)). Qed.
Lemma lem1367536 (x : real) : (term6 x) = term4.
Proof. exact (EQ_MP (@lem1367341 x) (@lem1367340 x)). Qed.
Lemma lem1367537 (m : nat) : (term82 m) = term4.
Proof. exact (@lem1367536 (real_of_num m)). Qed.
Lemma lem1367538 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1367539 (m : nat) : (term83 m) = term84.
Proof. exact (MK_COMB (@lem1367538) (@lem1367537 m)). Qed.
Lemma lem1367540 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem1367541 (m : nat) (n : nat) : (term81 m n) = (term85 n).
Proof. exact (MK_COMB (@lem1367539 m) (@lem1367540 n)). Qed.
Lemma lem1367543 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1367338 x) (@lem1367337 x)). Qed.
Lemma lem1367544 (n : nat) : (term85 n) = (real_of_num n).
Proof. exact (@lem1367543 (real_of_num n)). Qed.
Lemma lem1367545 (m : nat) (n : nat) : (term81 m n) = (real_of_num n).
Proof. exact (TRANS (@lem1367541 m n) (@lem1367544 n)). Qed.
Lemma lem1367546 (m : nat) (n : nat) : (term41 m n) = (real_of_num n).
Proof. exact (TRANS (@lem1367534 m n) (@lem1367545 m n)). Qed.
Lemma lem1367547 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367548 (m : nat) (n : nat) : (term43 m n) = (term86 n).
Proof. exact (MK_COMB (@lem1367547) (@lem1367546 m n)). Qed.
Lemma lem1367549 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem1367550 (m : nat) (n : nat) : ((term41 m n) = (real_of_num n)) = ((real_of_num n) = (real_of_num n)).
Proof. exact (MK_COMB (@lem1367548 m n) (@lem1367549 n)). Qed.
Lemma lem1367552 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367553 (x : real) : (x = x) = True.
Proof. exact (@lem1367552 real x). Qed.
Lemma lem1367554 (n : nat) : ((real_of_num n) = (real_of_num n)) = True.
Proof. exact (@lem1367553 (real_of_num n)). Qed.
Lemma lem1367555 (m : nat) (n : nat) : ((term41 m n) = (real_of_num n)) = True.
Proof. exact (TRANS (@lem1367550 m n) (@lem1367554 n)). Qed.
Lemma lem1367556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367557 (m : nat) (n : nat) : (term45 m n) = (and True).
Proof. exact (MK_COMB (@lem1367556) (@lem1367555 m n)). Qed.
Lemma lem1367571 (x : real) (y : real) (z : real) : (term12 x y z) = (term13 x y z).
Proof. exact (EQ_MP (@lem1367350 x y z) (@lem1367349 x y z)). Qed.
Lemma lem1367572 (m : nat) (n : nat) : (term65 m n) = (term87 m n).
Proof. exact (@lem1367571 (real_of_num m) (term52 m) (term52 n)). Qed.
Lemma lem1367573 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367574 (m : nat) (n : nat) : (term67 m n) = (term88 m n).
Proof. exact (MK_COMB (@lem1367573) (@lem1367572 m n)). Qed.
Lemma lem1367575 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem1367576 (m : nat) (n : nat) : ((term65 m n) = (term52 n)) = ((term87 m n) = (term52 n)).
Proof. exact (MK_COMB (@lem1367574 m n) (@lem1367575 n)). Qed.
Lemma lem1367579 (m : nat) (n : nat) : (term62 m n) = (term62 m n).
Proof. exact (eq_refl (term62 m n)). Qed.
Lemma lem1367580 (m : nat) (n : nat) : (term74 m n) = (term89 m n).
Proof. exact (MK_COMB (@lem1367579 m n) (@lem1367576 m n)). Qed.
Lemma lem1367583 (m : nat) (n : nat) : (term54 m n) = (term54 m n).
Proof. exact (eq_refl (term54 m n)). Qed.
Lemma lem1367584 (m : nat) (n : nat) : (term76 m n) = (term90 m n).
Proof. exact (MK_COMB (@lem1367583 m n) (@lem1367580 m n)). Qed.
Lemma lem1367587 (m : nat) (n : nat) : (term78 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem1367557 m n) (@lem1367584 m n)). Qed.
Lemma lem1367589 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1367590 (m : nat) (n : nat) : (term91 m n) = (term90 m n).
Proof. exact (@lem1367589 (term90 m n)). Qed.
Lemma lem1367603 (m : nat) (n : nat) : (term78 m n) = (term90 m n).
Proof. exact (TRANS (@lem1367587 m n) (@lem1367590 m n)). Qed.
Lemma lem1367604 (m : nat) (n : nat) : (term90 m n) = (term78 m n).
Proof. exact (SYM (@lem1367603 m n)). Qed.
Lemma lem1367622 (x : real) : (term3 x) = term4.
Proof. exact (EQ_MP (@lem1367335 x) (@lem1367334 x)). Qed.
Lemma lem1367623 (m : nat) : (term92 m) = term4.
Proof. exact (@lem1367622 (real_of_num m)). Qed.
Lemma lem1367624 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1367625 (m : nat) : (term93 m) = term84.
Proof. exact (MK_COMB (@lem1367624) (@lem1367623 m)). Qed.
Lemma lem1367626 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem1367627 (m : nat) (n : nat) : (term87 m n) = (term94 n).
Proof. exact (MK_COMB (@lem1367625 m) (@lem1367626 n)). Qed.
Lemma lem1367629 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1367332 x) (@lem1367331 x)). Qed.
Lemma lem1367630 (n : nat) : (term94 n) = (term52 n).
Proof. exact (@lem1367629 (term52 n)). Qed.
Lemma lem1367631 (m : nat) (n : nat) : (term87 m n) = (term52 n).
Proof. exact (TRANS (@lem1367627 m n) (@lem1367630 n)). Qed.
Lemma lem1367632 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367633 (m : nat) (n : nat) : (term88 m n) = (term95 n).
Proof. exact (MK_COMB (@lem1367632) (@lem1367631 m n)). Qed.
Lemma lem1367634 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem1367635 (m : nat) (n : nat) : ((term87 m n) = (term52 n)) = ((term52 n) = (term52 n)).
Proof. exact (MK_COMB (@lem1367633 m n) (@lem1367634 n)). Qed.
Lemma lem1367637 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367638 (x : real) : (x = x) = True.
Proof. exact (@lem1367637 real x). Qed.
Lemma lem1367639 (n : nat) : ((term52 n) = (term52 n)) = True.
Proof. exact (@lem1367638 (term52 n)). Qed.
Lemma lem1367640 (m : nat) (n : nat) : ((term87 m n) = (term52 n)) = True.
Proof. exact (TRANS (@lem1367635 m n) (@lem1367639 n)). Qed.
Lemma lem1367641 (m : nat) (n : nat) : (term62 m n) = (term62 m n).
Proof. exact (eq_refl (term62 m n)). Qed.
Lemma lem1367642 (m : nat) (n : nat) : (term89 m n) = (term96 m n).
Proof. exact (MK_COMB (@lem1367641 m n) (@lem1367640 m n)). Qed.
Lemma lem1367644 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1367645 (m : nat) (n : nat) : (term96 m n) = ((term58 n m) = (real_of_num n)).
Proof. exact (@lem1367644 ((term58 n m) = (real_of_num n))). Qed.
Lemma lem1367650 (m : nat) (n : nat) : (term89 m n) = ((term58 n m) = (real_of_num n)).
Proof. exact (TRANS (@lem1367642 m n) (@lem1367645 m n)). Qed.
Lemma lem1367651 (m : nat) (n : nat) : (term54 m n) = (term54 m n).
Proof. exact (eq_refl (term54 m n)). Qed.
Lemma lem1367652 (m : nat) (n : nat) : (term90 m n) = (term97 m n).
Proof. exact (MK_COMB (@lem1367651 m n) (@lem1367650 m n)). Qed.
Lemma lem1367655 (m : nat) (n : nat) : (term97 m n) = (term90 m n).
Proof. exact (SYM (@lem1367652 m n)). Qed.
Lemma lem1367661 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1367329 y x) (@lem1367328 x y)). Qed.
Lemma lem1367662 (m : nat) (n : nat) : (term49 n m) = (term65 m n).
Proof. exact (@lem1367661 (real_of_num m) (term36 m n)). Qed.
Lemma lem1367663 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367664 (m : nat) (n : nat) : (term51 n m) = (term67 m n).
Proof. exact (MK_COMB (@lem1367663) (@lem1367662 m n)). Qed.
Lemma lem1367665 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem1367666 (m : nat) (n : nat) : ((term49 n m) = (term52 n)) = ((term65 m n) = (term52 n)).
Proof. exact (MK_COMB (@lem1367664 m n) (@lem1367665 n)). Qed.
Lemma lem1367667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367668 (m : nat) (n : nat) : (term54 m n) = (term69 m n).
Proof. exact (MK_COMB (@lem1367667) (@lem1367666 m n)). Qed.
Lemma lem1367672 (y : real) (x : real) : (real_add x y) = (real_add y x).
Proof. exact (EQ_MP (@lem1367329 y x) (@lem1367328 x y)). Qed.
Lemma lem1367673 (m : nat) (n : nat) : (term58 n m) = (term41 m n).
Proof. exact (@lem1367672 (term52 m) (term17 m n)). Qed.
Lemma lem1367674 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367675 (m : nat) (n : nat) : (term60 n m) = (term43 m n).
Proof. exact (MK_COMB (@lem1367674) (@lem1367673 m n)). Qed.
Lemma lem1367676 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem1367677 (m : nat) (n : nat) : ((term58 n m) = (real_of_num n)) = ((term41 m n) = (real_of_num n)).
Proof. exact (MK_COMB (@lem1367675 m n) (@lem1367676 n)). Qed.
Lemma lem1367678 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (MK_COMB (@lem1367668 m n) (@lem1367677 m n)). Qed.
Lemma lem1367679 (m : nat) (n : nat) : (term98 m n) = (term97 m n).
Proof. exact (SYM (@lem1367678 m n)). Qed.
Lemma lem1367685 (x : real) (y : real) (z : real) : (term12 x y z) = (term13 x y z).
Proof. exact (EQ_MP (@lem1367323 x y z) (@lem1367322 x y z)). Qed.
Lemma lem1367686 (m : nat) (n : nat) : (term65 m n) = (term87 m n).
Proof. exact (@lem1367685 (real_of_num m) (term52 m) (term52 n)). Qed.
Lemma lem1367687 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367688 (m : nat) (n : nat) : (term67 m n) = (term88 m n).
Proof. exact (MK_COMB (@lem1367687) (@lem1367686 m n)). Qed.
Lemma lem1367689 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem1367690 (m : nat) (n : nat) : ((term65 m n) = (term52 n)) = ((term87 m n) = (term52 n)).
Proof. exact (MK_COMB (@lem1367688 m n) (@lem1367689 n)). Qed.
Lemma lem1367693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1367694 (m : nat) (n : nat) : (term69 m n) = (term99 m n).
Proof. exact (MK_COMB (@lem1367693) (@lem1367690 m n)). Qed.
Lemma lem1367700 (x : real) (y : real) (z : real) : (term12 x y z) = (term13 x y z).
Proof. exact (EQ_MP (@lem1367323 x y z) (@lem1367322 x y z)). Qed.
Lemma lem1367701 (m : nat) (n : nat) : (term41 m n) = (term81 m n).
Proof. exact (@lem1367700 (term52 m) (real_of_num m) (real_of_num n)). Qed.
Lemma lem1367703 (x : real) : (term6 x) = term4.
Proof. exact (EQ_MP (@lem1367314 x) (@lem1367313 x)). Qed.
Lemma lem1367704 (m : nat) : (term82 m) = term4.
Proof. exact (@lem1367703 (real_of_num m)). Qed.
Lemma lem1367705 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1367706 (m : nat) : (term83 m) = term84.
Proof. exact (MK_COMB (@lem1367705) (@lem1367704 m)). Qed.
Lemma lem1367707 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem1367708 (m : nat) (n : nat) : (term81 m n) = (term85 n).
Proof. exact (MK_COMB (@lem1367706 m) (@lem1367707 n)). Qed.
Lemma lem1367710 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1367311 x) (@lem1367310 x)). Qed.
Lemma lem1367711 (n : nat) : (term85 n) = (real_of_num n).
Proof. exact (@lem1367710 (real_of_num n)). Qed.
Lemma lem1367712 (m : nat) (n : nat) : (term81 m n) = (real_of_num n).
Proof. exact (TRANS (@lem1367708 m n) (@lem1367711 n)). Qed.
Lemma lem1367713 (m : nat) (n : nat) : (term41 m n) = (real_of_num n).
Proof. exact (TRANS (@lem1367701 m n) (@lem1367712 m n)). Qed.
Lemma lem1367714 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367715 (m : nat) (n : nat) : (term43 m n) = (term86 n).
Proof. exact (MK_COMB (@lem1367714) (@lem1367713 m n)). Qed.
Lemma lem1367716 (n : nat) : (real_of_num n) = (real_of_num n).
Proof. exact (eq_refl (real_of_num n)). Qed.
Lemma lem1367717 (m : nat) (n : nat) : ((term41 m n) = (real_of_num n)) = ((real_of_num n) = (real_of_num n)).
Proof. exact (MK_COMB (@lem1367715 m n) (@lem1367716 n)). Qed.
Lemma lem1367719 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367720 (x : real) : (x = x) = True.
Proof. exact (@lem1367719 real x). Qed.
Lemma lem1367721 (n : nat) : ((real_of_num n) = (real_of_num n)) = True.
Proof. exact (@lem1367720 (real_of_num n)). Qed.
Lemma lem1367722 (m : nat) (n : nat) : ((term41 m n) = (real_of_num n)) = True.
Proof. exact (TRANS (@lem1367717 m n) (@lem1367721 n)). Qed.
Lemma lem1367723 (m : nat) (n : nat) : (term98 m n) = (term100 m n).
Proof. exact (MK_COMB (@lem1367694 m n) (@lem1367722 m n)). Qed.
Lemma lem1367725 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1367726 (m : nat) (n : nat) : (term100 m n) = ((term87 m n) = (term52 n)).
Proof. exact (@lem1367725 ((term87 m n) = (term52 n))). Qed.
Lemma lem1367729 (m : nat) (n : nat) : (term98 m n) = ((term87 m n) = (term52 n)).
Proof. exact (TRANS (@lem1367723 m n) (@lem1367726 m n)). Qed.
Lemma lem1367730 (m : nat) (n : nat) : ((term87 m n) = (term52 n)) = (term98 m n).
Proof. exact (SYM (@lem1367729 m n)). Qed.
Lemma lem1367736 (x : real) : (term3 x) = term4.
Proof. exact (EQ_MP (@lem1367308 x) (@lem1367307 x)). Qed.
Lemma lem1367737 (m : nat) : (term92 m) = term4.
Proof. exact (@lem1367736 (real_of_num m)). Qed.
Lemma lem1367738 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1367739 (m : nat) : (term93 m) = term84.
Proof. exact (MK_COMB (@lem1367738) (@lem1367737 m)). Qed.
Lemma lem1367740 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem1367741 (m : nat) (n : nat) : (term87 m n) = (term94 n).
Proof. exact (MK_COMB (@lem1367739 m) (@lem1367740 n)). Qed.
Lemma lem1367743 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1367305 x) (@lem1367304 x)). Qed.
Lemma lem1367744 (n : nat) : (term94 n) = (term52 n).
Proof. exact (@lem1367743 (term52 n)). Qed.
Lemma lem1367745 (m : nat) (n : nat) : (term87 m n) = (term52 n).
Proof. exact (TRANS (@lem1367741 m n) (@lem1367744 n)). Qed.
Lemma lem1367746 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1367747 (m : nat) (n : nat) : (term88 m n) = (term95 n).
Proof. exact (MK_COMB (@lem1367746) (@lem1367745 m n)). Qed.
Lemma lem1367748 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem1367749 (m : nat) (n : nat) : ((term87 m n) = (term52 n)) = ((term52 n) = (term52 n)).
Proof. exact (MK_COMB (@lem1367747 m n) (@lem1367748 n)). Qed.
Lemma lem1367751 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1367752 (x : real) : (x = x) = True.
Proof. exact (@lem1367751 real x). Qed.
Lemma lem1367753 (n : nat) : ((term52 n) = (term52 n)) = True.
Proof. exact (@lem1367752 (term52 n)). Qed.
Lemma lem1367754 (m : nat) (n : nat) : ((term87 m n) = (term52 n)) = True.
Proof. exact (TRANS (@lem1367749 m n) (@lem1367753 n)). Qed.
Lemma lem1367755 (m : nat) (n : nat) : True = ((term87 m n) = (term52 n)).
Proof. exact (SYM (@lem1367754 m n)). Qed.
Lemma lem1367756 (m : nat) (n : nat) : (term87 m n) = (term52 n).
Proof. exact (EQ_MP (@lem1367755 m n) (@lem0)). Qed.
Lemma lem1367757 (m : nat) (n : nat) : term98 m n.
Proof. exact (EQ_MP (@lem1367730 m n) (@lem1367756 m n)). Qed.
Lemma lem1367758 (m : nat) (n : nat) : term97 m n.
Proof. exact (EQ_MP (@lem1367679 m n) (@lem1367757 m n)). Qed.
Lemma lem1367759 (m : nat) (n : nat) : term90 m n.
Proof. exact (EQ_MP (@lem1367655 m n) (@lem1367758 m n)). Qed.
Lemma lem1367760 (m : nat) (n : nat) : term78 m n.
Proof. exact (EQ_MP (@lem1367604 m n) (@lem1367759 m n)). Qed.
Lemma lem1367761 (m : nat) (n : nat) : term79 m n.
Proof. exact (EQ_MP (@lem1367525 m n) (@lem1367760 m n)). Qed.
