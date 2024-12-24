Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ZPOW_LT_term_abbrevs.
Require Import FORALL_INT_CASES_spec.
Require Import REAL_LT_INV_EQ_spec.
Require Import REAL_POW_LT_spec.
Require Import REAL_ZPOW_POW_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem3179363 (x : real) : term0 x.
Proof. exact (@lem1582551 x). Qed.
Lemma lem3179364 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3179365 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem3179364 x) (@lem3179363 x)). Qed.
Lemma lem3179366 (x : real) (n : nat) : term2 x n.
Proof. exact (@lem3179365 x n). Qed.
Lemma lem3179367 (x : real) (n : nat) : (term2 x n) = (term3 x n).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem3179368 (x : real) (n : nat) : term3 x n.
Proof. exact (EQ_MP (@lem3179367 x n) (@lem3179366 x n)). Qed.
Lemma lem3179369 (x : real) (h1 : term4 x) : term4 x.
Proof. exact (h1). Qed.
Lemma lem3179370 (n : nat) (x : real) (h1 : term4 x) : term5 x n.
Proof. exact (@lem3179368 x n (@lem3179369 x h1)). Qed.
Lemma lem3179371 (x : real) (n : nat) : (term5 x n) = ((term5 x n) = True).
Proof. exact (@lem7 (term5 x n)). Qed.
Lemma lem3179372 (n : nat) (x : real) (h1 : term4 x) : (term5 x n) = True.
Proof. exact (EQ_MP (@lem3179371 x n) (@lem3179370 n x h1)). Qed.
Lemma lem3179378 (x : real) : term6 x.
Proof. exact (@lem1590037 x). Qed.
Lemma lem3179379 (x : real) : (term6 x) = ((term7 x) = (term4 x)).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem3179381 : term8.
Proof. exact (proj2 (@lem3174260)). Qed.
Lemma lem3179382 (x : real) : term9 x.
Proof. exact (@lem3179381 x). Qed.
Lemma lem3179383 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem3179384 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem3179383 x) (@lem3179382 x)). Qed.
Lemma lem3179385 (x : real) (n : nat) : term11 x n.
Proof. exact (@lem3179384 x n). Qed.
Lemma lem3179386 (x : real) (n : nat) : (term11 x n) = ((term12 x n) = (term13 x n)).
Proof. exact (eq_refl (term11 x n)). Qed.
Lemma lem3179388 : term14.
Proof. exact (proj1 (@lem3174260)). Qed.
Lemma lem3179389 (x : real) : term15 x.
Proof. exact (@lem3179388 x). Qed.
Lemma lem3179390 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem3179391 (x : real) : term16 x.
Proof. exact (EQ_MP (@lem3179390 x) (@lem3179389 x)). Qed.
Lemma lem3179392 (x : real) (n : nat) : term17 x n.
Proof. exact (@lem3179391 x n). Qed.
Lemma lem3179393 (x : real) (n : nat) : (term17 x n) = ((term18 x n) = (real_pow x n)).
Proof. exact (eq_refl (term17 x n)). Qed.
Lemma lem3179395 (P : int -> Prop) : term19 P.
Proof. exact (@lem2296993 P). Qed.
Lemma lem3179396 (P : int -> Prop) : (term19 P) = ((term20 P) = (term21 P)).
Proof. exact (eq_refl (term19 P)). Qed.
Lemma lem3179409 (P : int -> Prop) : (term20 P) = (term21 P).
Proof. exact (EQ_MP (@lem3179396 P) (@lem3179395 P)). Qed.
Lemma lem3179410 (x : real) : (term22 x) = (term23 x).
Proof. exact (@lem3179409 (term24 x)). Qed.
Lemma lem3179411 (x : real) (n : int) : (term25 x n) = (term26 x n).
Proof. exact (eq_refl (term25 x n)). Qed.
Lemma lem3179412 (x : real) : (term27 x) = (term24 x).
Proof. exact (fun_ext (fun n : int => @lem3179411 x n)). Qed.
Lemma lem3179413 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem3179414 (x : real) : (term22 x) = (term28 x).
Proof. exact (MK_COMB (@lem3179413) (@lem3179412 x)). Qed.
Lemma lem3179415 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3179416 (x : real) : (term29 x) = (term30 x).
Proof. exact (MK_COMB (@lem3179415) (@lem3179414 x)). Qed.
Lemma lem3179417 (x : real) (n : nat) : (term31 x n) = (term32 x n).
Proof. exact (eq_refl (term31 x n)). Qed.
Lemma lem3179418 (x : real) : (term33 x) = (term34 x).
Proof. exact (fun_ext (fun n : nat => @lem3179417 x n)). Qed.
Lemma lem3179419 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179420 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem3179419) (@lem3179418 x)). Qed.
Lemma lem3179421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3179422 (x : real) : (term37 x) = (term38 x).
Proof. exact (MK_COMB (@lem3179421) (@lem3179420 x)). Qed.
Lemma lem3179423 (x : real) (n : nat) : (term39 x n) = (term40 x n).
Proof. exact (eq_refl (term39 x n)). Qed.
Lemma lem3179424 (x : real) : (term41 x) = (term42 x).
Proof. exact (fun_ext (fun n : nat => @lem3179423 x n)). Qed.
Lemma lem3179425 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179426 (x : real) : (term43 x) = (term44 x).
Proof. exact (MK_COMB (@lem3179425) (@lem3179424 x)). Qed.
Lemma lem3179427 (x : real) : (term23 x) = (term45 x).
Proof. exact (MK_COMB (@lem3179422 x) (@lem3179426 x)). Qed.
Lemma lem3179428 (x : real) : ((term22 x) = (term23 x)) = ((term28 x) = (term45 x)).
Proof. exact (MK_COMB (@lem3179416 x) (@lem3179427 x)). Qed.
Lemma lem3179429 (x : real) : (term28 x) = (term45 x).
Proof. exact (EQ_MP (@lem3179428 x) (@lem3179410 x)). Qed.
Lemma lem3179441 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term46 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3179442 (p : Prop) (q : Prop) (p' : Prop) : term47 p q p'.
Proof. exact (fun q' : Prop => @lem3179441 p q p' q'). Qed.
Lemma lem3179443 (p : Prop) (q : Prop) : term48 p q.
Proof. exact (fun p' : Prop => @lem3179442 p q p'). Qed.
Lemma lem3179444 (x : real) (n : nat) : term49 x n.
Proof. exact (@lem3179443 (term4 x) (term50 x n)). Qed.
Lemma lem3179445 (x : real) (n : nat) (p' : Prop) : term51 x n p'.
Proof. exact (@lem3179444 x n p'). Qed.
Lemma lem3179446 (x : real) (n : nat) (p' : Prop) : (term51 x n p') = (term52 x n p').
Proof. exact (eq_refl (term51 x n p')). Qed.
Lemma lem3179447 (x : real) (n : nat) (p' : Prop) : term52 x n p'.
Proof. exact (EQ_MP (@lem3179446 x n p') (@lem3179445 x n p')). Qed.
Lemma lem3179448 (x : real) (n : nat) (p' : Prop) (q' : Prop) : term53 x n p' q'.
Proof. exact (@lem3179447 x n p' q'). Qed.
Lemma lem3179449 (x : real) (n : nat) (p' : Prop) (q' : Prop) : (term53 x n p' q') = (term54 x n p' q').
Proof. exact (eq_refl (term53 x n p' q')). Qed.
Lemma lem3179450 (x : real) (n : nat) (p' : Prop) (q' : Prop) : term54 x n p' q'.
Proof. exact (EQ_MP (@lem3179449 x n p' q') (@lem3179448 x n p' q')). Qed.
Lemma lem3179451 (x : real) : (term4 x) = (term4 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem3179452 (n : nat) (x : real) (q' : Prop) : term55 n x q'.
Proof. exact (@lem3179450 x n (term4 x) q'). Qed.
Lemma lem3179453 (n : nat) (x : real) (q' : Prop) : term56 n x q'.
Proof. exact (@lem3179452 n x q' (@lem3179451 x)). Qed.
Lemma lem3179454 (x : real) (h1 : term4 x) : term4 x.
Proof. exact (h1). Qed.
Lemma lem3179455 (x : real) : (term4 x) = ((term4 x) = True).
Proof. exact (@lem7 (term4 x)). Qed.
Lemma lem3179458 (x : real) (n : nat) : (term18 x n) = (real_pow x n).
Proof. exact (EQ_MP (@lem3179393 x n) (@lem3179392 x n)). Qed.
Lemma lem3179459 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem3179460 (x : real) (n : nat) : (term50 x n) = (term5 x n).
Proof. exact (MK_COMB (@lem3179459) (@lem3179458 x n)). Qed.
Lemma lem3179462 (x : real) (n : nat) : term58 x n.
Proof. exact (fun h0 : term4 x => @lem3179372 n x h0). Qed.
Lemma lem3179464 (x : real) (h1 : term4 x) : (term4 x) = True.
Proof. exact (EQ_MP (@lem3179455 x) (@lem3179454 x h1)). Qed.
Lemma lem3179465 (x : real) (h1 : term4 x) : True = (term4 x).
Proof. exact (SYM (@lem3179464 x h1)). Qed.
Lemma lem3179466 (x : real) (h1 : term4 x) : term4 x.
Proof. exact (EQ_MP (@lem3179465 x h1) (@lem0)). Qed.
Lemma lem3179467 (n : nat) (x : real) (h1 : term4 x) : (term5 x n) = True.
Proof. exact (@lem3179462 x n (@lem3179466 x h1)). Qed.
Lemma lem3179468 (n : nat) (x : real) (h1 : term4 x) : (term50 x n) = True.
Proof. exact (TRANS (@lem3179460 x n) (@lem3179467 n x h1)). Qed.
Lemma lem3179469 (x : real) (n : nat) : term59 x n.
Proof. exact (fun h0 : term4 x => @lem3179468 n x h0). Qed.
Lemma lem3179470 (n : nat) (x : real) : term60 n x.
Proof. exact (@lem3179453 n x True). Qed.
Lemma lem3179471 (n : nat) (x : real) : (term32 x n) = (term61 x).
Proof. exact (@lem3179470 n x (@lem3179469 x n)). Qed.
Lemma lem3179473 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3179474 (x : real) : (term61 x) = True.
Proof. exact (@lem3179473 (term4 x)). Qed.
Lemma lem3179475 (x : real) (n : nat) : (term32 x n) = True.
Proof. exact (TRANS (@lem3179471 n x) (@lem3179474 x)). Qed.
Lemma lem3179476 (x : real) : (term34 x) = term62.
Proof. exact (fun_ext (fun n : nat => @lem3179475 x n)). Qed.
Lemma lem3179477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179478 (x : real) : (term36 x) = term63.
Proof. exact (MK_COMB (@lem3179477) (@lem3179476 x)). Qed.
Lemma lem3179480 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3179481 (t : Prop) : (term65 t) = t.
Proof. exact (@lem3179480 nat t). Qed.
Lemma lem3179482 : term63 = True.
Proof. exact (@lem3179481 True). Qed.
Lemma lem3179483 (x : real) : (term36 x) = True.
Proof. exact (TRANS (@lem3179478 x) (@lem3179482)). Qed.
Lemma lem3179484 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3179485 (x : real) : (term38 x) = (and True).
Proof. exact (MK_COMB (@lem3179484) (@lem3179483 x)). Qed.
Lemma lem3179495 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term46 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem3179496 (p : Prop) (q : Prop) (p' : Prop) : term47 p q p'.
Proof. exact (fun q' : Prop => @lem3179495 p q p' q'). Qed.
Lemma lem3179497 (p : Prop) (q : Prop) : term48 p q.
Proof. exact (fun p' : Prop => @lem3179496 p q p'). Qed.
Lemma lem3179498 (x : real) (n : nat) : term66 x n.
Proof. exact (@lem3179497 (term4 x) (term67 x n)). Qed.
Lemma lem3179499 (x : real) (n : nat) (p' : Prop) : term68 x n p'.
Proof. exact (@lem3179498 x n p'). Qed.
Lemma lem3179500 (x : real) (n : nat) (p' : Prop) : (term68 x n p') = (term69 x n p').
Proof. exact (eq_refl (term68 x n p')). Qed.
Lemma lem3179501 (x : real) (n : nat) (p' : Prop) : term69 x n p'.
Proof. exact (EQ_MP (@lem3179500 x n p') (@lem3179499 x n p')). Qed.
Lemma lem3179502 (x : real) (n : nat) (p' : Prop) (q' : Prop) : term70 x n p' q'.
Proof. exact (@lem3179501 x n p' q'). Qed.
Lemma lem3179503 (x : real) (n : nat) (p' : Prop) (q' : Prop) : (term70 x n p' q') = (term71 x n p' q').
Proof. exact (eq_refl (term70 x n p' q')). Qed.
Lemma lem3179504 (x : real) (n : nat) (p' : Prop) (q' : Prop) : term71 x n p' q'.
Proof. exact (EQ_MP (@lem3179503 x n p' q') (@lem3179502 x n p' q')). Qed.
Lemma lem3179505 (x : real) : (term4 x) = (term4 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem3179506 (n : nat) (x : real) (q' : Prop) : term72 n x q'.
Proof. exact (@lem3179504 x n (term4 x) q'). Qed.
Lemma lem3179507 (n : nat) (x : real) (q' : Prop) : term73 n x q'.
Proof. exact (@lem3179506 n x q' (@lem3179505 x)). Qed.
Lemma lem3179508 (x : real) (h1 : term4 x) : term4 x.
Proof. exact (h1). Qed.
Lemma lem3179509 (x : real) : (term4 x) = ((term4 x) = True).
Proof. exact (@lem7 (term4 x)). Qed.
Lemma lem3179512 (x : real) (n : nat) : (term12 x n) = (term13 x n).
Proof. exact (EQ_MP (@lem3179386 x n) (@lem3179385 x n)). Qed.
Lemma lem3179513 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem3179514 (x : real) (n : nat) : (term67 x n) = (term74 x n).
Proof. exact (MK_COMB (@lem3179513) (@lem3179512 x n)). Qed.
Lemma lem3179516 (x : real) : (term7 x) = (term4 x).
Proof. exact (EQ_MP (@lem3179379 x) (@lem3179378 x)). Qed.
Lemma lem3179517 (x : real) (n : nat) : (term74 x n) = (term5 x n).
Proof. exact (@lem3179516 (real_pow x n)). Qed.
Lemma lem3179519 (x : real) (n : nat) : term58 x n.
Proof. exact (fun h0 : term4 x => @lem3179372 n x h0). Qed.
Lemma lem3179521 (x : real) (h1 : term4 x) : (term4 x) = True.
Proof. exact (EQ_MP (@lem3179509 x) (@lem3179508 x h1)). Qed.
Lemma lem3179522 (x : real) (h1 : term4 x) : True = (term4 x).
Proof. exact (SYM (@lem3179521 x h1)). Qed.
Lemma lem3179523 (x : real) (h1 : term4 x) : term4 x.
Proof. exact (EQ_MP (@lem3179522 x h1) (@lem0)). Qed.
Lemma lem3179524 (n : nat) (x : real) (h1 : term4 x) : (term5 x n) = True.
Proof. exact (@lem3179519 x n (@lem3179523 x h1)). Qed.
Lemma lem3179525 (n : nat) (x : real) (h1 : term4 x) : (term74 x n) = True.
Proof. exact (TRANS (@lem3179517 x n) (@lem3179524 n x h1)). Qed.
Lemma lem3179526 (n : nat) (x : real) (h1 : term4 x) : (term67 x n) = True.
Proof. exact (TRANS (@lem3179514 x n) (@lem3179525 n x h1)). Qed.
Lemma lem3179527 (x : real) (n : nat) : term75 x n.
Proof. exact (fun h0 : term4 x => @lem3179526 n x h0). Qed.
Lemma lem3179528 (n : nat) (x : real) : term76 n x.
Proof. exact (@lem3179507 n x True). Qed.
Lemma lem3179529 (n : nat) (x : real) : (term40 x n) = (term61 x).
Proof. exact (@lem3179528 n x (@lem3179527 x n)). Qed.
Lemma lem3179531 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3179532 (x : real) : (term61 x) = True.
Proof. exact (@lem3179531 (term4 x)). Qed.
Lemma lem3179533 (x : real) (n : nat) : (term40 x n) = True.
Proof. exact (TRANS (@lem3179529 n x) (@lem3179532 x)). Qed.
Lemma lem3179534 (x : real) : (term42 x) = term62.
Proof. exact (fun_ext (fun n : nat => @lem3179533 x n)). Qed.
Lemma lem3179535 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3179536 (x : real) : (term44 x) = term63.
Proof. exact (MK_COMB (@lem3179535) (@lem3179534 x)). Qed.
Lemma lem3179538 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3179539 (t : Prop) : (term65 t) = t.
Proof. exact (@lem3179538 nat t). Qed.
Lemma lem3179540 : term63 = True.
Proof. exact (@lem3179539 True). Qed.
Lemma lem3179541 (x : real) : (term44 x) = True.
Proof. exact (TRANS (@lem3179536 x) (@lem3179540)). Qed.
Lemma lem3179542 (x : real) : (term45 x) = (True /\ True).
Proof. exact (MK_COMB (@lem3179485 x) (@lem3179541 x)). Qed.
Lemma lem3179544 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3179545 : (True /\ True) = True.
Proof. exact (@lem3179544 True). Qed.
Lemma lem3179546 (x : real) : (term45 x) = True.
Proof. exact (TRANS (@lem3179542 x) (@lem3179545)). Qed.
Lemma lem3179547 (x : real) : (term28 x) = True.
Proof. exact (TRANS (@lem3179429 x) (@lem3179546 x)). Qed.
Lemma lem3179548 : term77 = term78.
Proof. exact (fun_ext (fun x : real => @lem3179547 x)). Qed.
Lemma lem3179549 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem3179550 : term79 = term80.
Proof. exact (MK_COMB (@lem3179549) (@lem3179548)). Qed.
Lemma lem3179552 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3179553 (t : Prop) : (term81 t) = t.
Proof. exact (@lem3179552 real t). Qed.
Lemma lem3179554 : term80 = True.
Proof. exact (@lem3179553 True). Qed.
Lemma lem3179555 : term79 = True.
Proof. exact (TRANS (@lem3179550) (@lem3179554)). Qed.
Lemma lem3179556 : True = term79.
Proof. exact (SYM (@lem3179555)). Qed.
Lemma lem3179557 : term79.
Proof. exact (EQ_MP (@lem3179556) (@lem0)). Qed.
