Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINREC_UNIQUE_LEMMA_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINREC_SUC_LEMMA_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm3791009_spec.
Require Import thm3791010_spec.
Require Import thm3791024_spec.
Require Import thm3791025_spec.
Require Import thm69_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem3797398 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3797399 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3797400 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3797399 t1) (@lem3797398 t1)). Qed.
Lemma lem3797401 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3797400 t1 t2). Qed.
Lemma lem3797402 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3797403 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3797402 t1 t2) (@lem3797401 t1 t2)). Qed.
Lemma lem3797404 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3797403 t1 t2 t3). Qed.
Lemma lem3797405 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3797406 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3797405 t1 t2 t3) (@lem3797404 t1 t2 t3)). Qed.
Lemma lem3797407 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3797406 t1 t2 t3)). Qed.
Lemma lem3797446 {A B : Type'} (f : type1411 A B) (h1 : term7 A B f) : term7 A B f.
Proof. exact (h1). Qed.
Lemma lem3797448 (P : nat -> Prop) : term8 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem3797449 {A B : Type'} (f : type1411 A B) (b : B) : term9 A B f b.
Proof. exact (@lem3797448 (term10 A B f b)). Qed.
Lemma lem3797450 {A B : Type'} (f : type1411 A B) (b : B) : (term11 A B f b) = (term12 A B f b).
Proof. exact (eq_refl (term11 A B f b)). Qed.
Lemma lem3797451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3797452 {A B : Type'} (f : type1411 A B) (b : B) : (term13 A B f b) = (term14 A B f b).
Proof. exact (MK_COMB (@lem3797451) (@lem3797450 A B f b)). Qed.
Lemma lem3797453 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term15 A B f b n1) = (term16 A B f b n1).
Proof. exact (eq_refl (term15 A B f b n1)). Qed.
Lemma lem3797454 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3797455 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term17 A B f b n1) = (term18 A B f b n1).
Proof. exact (MK_COMB (@lem3797454) (@lem3797453 A B f b n1)). Qed.
Lemma lem3797456 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term19 A B f b n1) = (term20 A B f b n1).
Proof. exact (eq_refl (term19 A B f b n1)). Qed.
Lemma lem3797457 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term21 A B f b n1) = (term22 A B f b n1).
Proof. exact (MK_COMB (@lem3797455 A B f b n1) (@lem3797456 A B f b n1)). Qed.
Lemma lem3797458 {A B : Type'} (f : type1411 A B) (b : B) : (term23 A B f b) = (term24 A B f b).
Proof. exact (fun_ext (fun n1 : nat => @lem3797457 A B f b n1)). Qed.
Lemma lem3797459 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3797460 {A B : Type'} (f : type1411 A B) (b : B) : (term25 A B f b) = (term26 A B f b).
Proof. exact (MK_COMB (@lem3797459) (@lem3797458 A B f b)). Qed.
Lemma lem3797461 {A B : Type'} (f : type1411 A B) (b : B) : (term27 A B f b) = (term28 A B f b).
Proof. exact (MK_COMB (@lem3797452 A B f b) (@lem3797460 A B f b)). Qed.
Lemma lem3797462 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3797463 {A B : Type'} (f : type1411 A B) (b : B) : (term29 A B f b) = (term30 A B f b).
Proof. exact (MK_COMB (@lem3797462) (@lem3797461 A B f b)). Qed.
Lemma lem3797464 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term15 A B f b n1) = (term16 A B f b n1).
Proof. exact (eq_refl (term15 A B f b n1)). Qed.
Lemma lem3797465 {A B : Type'} (f : type1411 A B) (b : B) : (term31 A B f b) = (term10 A B f b).
Proof. exact (fun_ext (fun n1 : nat => @lem3797464 A B f b n1)). Qed.
Lemma lem3797466 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3797467 {A B : Type'} (f : type1411 A B) (b : B) : (term32 A B f b) = (term33 A B f b).
Proof. exact (MK_COMB (@lem3797466) (@lem3797465 A B f b)). Qed.
Lemma lem3797468 {A B : Type'} (f : type1411 A B) (b : B) : (term9 A B f b) = (term34 A B f b).
Proof. exact (MK_COMB (@lem3797463 A B f b) (@lem3797467 A B f b)). Qed.
Lemma lem3797469 {A B : Type'} (f : type1411 A B) (b : B) : term34 A B f b.
Proof. exact (EQ_MP (@lem3797468 A B f b) (@lem3797449 A B f b)). Qed.
Lemma lem3797470 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term16 A B f b n1.
Proof. exact (h1). Qed.
Lemma lem3797472 (P : nat -> Prop) : term8 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem3797473 {A B : Type'} (f : type1411 A B) (b : B) : term35 A B f b.
Proof. exact (@lem3797472 (term36 A B f b)). Qed.
Lemma lem3797474 {A B : Type'} (f : type1411 A B) (b : B) : (term37 A B f b) = (term38 A B f b).
Proof. exact (eq_refl (term37 A B f b)). Qed.
Lemma lem3797475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3797476 {A B : Type'} (f : type1411 A B) (b : B) : (term39 A B f b) = (term40 A B f b).
Proof. exact (MK_COMB (@lem3797475) (@lem3797474 A B f b)). Qed.
Lemma lem3797477 {A B : Type'} (f : type1411 A B) (b : B) (n2 : nat) : (term41 A B f b n2) = (term42 A B f b n2).
Proof. exact (eq_refl (term41 A B f b n2)). Qed.
Lemma lem3797478 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3797479 {A B : Type'} (f : type1411 A B) (b : B) (n2 : nat) : (term43 A B f b n2) = (term44 A B f b n2).
Proof. exact (MK_COMB (@lem3797478) (@lem3797477 A B f b n2)). Qed.
Lemma lem3797480 {A B : Type'} (f : type1411 A B) (b : B) (n2 : nat) : (term45 A B f b n2) = (term46 A B f b n2).
Proof. exact (eq_refl (term45 A B f b n2)). Qed.
Lemma lem3797481 {A B : Type'} (f : type1411 A B) (b : B) (n2 : nat) : (term47 A B f b n2) = (term48 A B f b n2).
Proof. exact (MK_COMB (@lem3797479 A B f b n2) (@lem3797480 A B f b n2)). Qed.
Lemma lem3797482 {A B : Type'} (f : type1411 A B) (b : B) : (term49 A B f b) = (term50 A B f b).
Proof. exact (fun_ext (fun n2 : nat => @lem3797481 A B f b n2)). Qed.
Lemma lem3797483 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3797484 {A B : Type'} (f : type1411 A B) (b : B) : (term51 A B f b) = (term52 A B f b).
Proof. exact (MK_COMB (@lem3797483) (@lem3797482 A B f b)). Qed.
Lemma lem3797485 {A B : Type'} (f : type1411 A B) (b : B) : (term53 A B f b) = (term54 A B f b).
Proof. exact (MK_COMB (@lem3797476 A B f b) (@lem3797484 A B f b)). Qed.
Lemma lem3797486 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3797487 {A B : Type'} (f : type1411 A B) (b : B) : (term55 A B f b) = (term56 A B f b).
Proof. exact (MK_COMB (@lem3797486) (@lem3797485 A B f b)). Qed.
Lemma lem3797488 {A B : Type'} (f : type1411 A B) (b : B) (n2 : nat) : (term41 A B f b n2) = (term42 A B f b n2).
Proof. exact (eq_refl (term41 A B f b n2)). Qed.
Lemma lem3797489 {A B : Type'} (f : type1411 A B) (b : B) : (term57 A B f b) = (term36 A B f b).
Proof. exact (fun_ext (fun n2 : nat => @lem3797488 A B f b n2)). Qed.
Lemma lem3797490 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3797491 {A B : Type'} (f : type1411 A B) (b : B) : (term58 A B f b) = (term12 A B f b).
Proof. exact (MK_COMB (@lem3797490) (@lem3797489 A B f b)). Qed.
Lemma lem3797492 {A B : Type'} (f : type1411 A B) (b : B) : (term35 A B f b) = (term59 A B f b).
Proof. exact (MK_COMB (@lem3797487 A B f b) (@lem3797491 A B f b)). Qed.
Lemma lem3797493 {A B : Type'} (f : type1411 A B) (b : B) : term59 A B f b.
Proof. exact (EQ_MP (@lem3797492 A B f b) (@lem3797473 A B f b)). Qed.
Lemma lem3797496 (P : nat -> Prop) : term8 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem3797497 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : term60 A B f b n1.
Proof. exact (@lem3797496 (term61 A B f b n1)). Qed.
Lemma lem3797498 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term62 A B f b n1) = (term63 A B f b n1).
Proof. exact (eq_refl (term62 A B f b n1)). Qed.
Lemma lem3797499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3797500 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term64 A B f b n1) = (term65 A B f b n1).
Proof. exact (MK_COMB (@lem3797499) (@lem3797498 A B f b n1)). Qed.
Lemma lem3797501 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term66 A B f b n1 n2) = (term67 A B f b n1 n2).
Proof. exact (eq_refl (term66 A B f b n1 n2)). Qed.
Lemma lem3797502 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3797503 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term68 A B f b n1 n2) = (term69 A B f b n1 n2).
Proof. exact (MK_COMB (@lem3797502) (@lem3797501 A B f b n1 n2)). Qed.
Lemma lem3797504 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term70 A B f b n1 n2) = (term71 A B f b n1 n2).
Proof. exact (eq_refl (term70 A B f b n1 n2)). Qed.
Lemma lem3797505 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term72 A B f b n1 n2) = (term73 A B f b n1 n2).
Proof. exact (MK_COMB (@lem3797503 A B f b n1 n2) (@lem3797504 A B f b n1 n2)). Qed.
Lemma lem3797506 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term74 A B f b n1) = (term75 A B f b n1).
Proof. exact (fun_ext (fun n2 : nat => @lem3797505 A B f b n1 n2)). Qed.
Lemma lem3797507 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3797508 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term76 A B f b n1) = (term77 A B f b n1).
Proof. exact (MK_COMB (@lem3797507) (@lem3797506 A B f b n1)). Qed.
Lemma lem3797509 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term78 A B f b n1) = (term79 A B f b n1).
Proof. exact (MK_COMB (@lem3797500 A B f b n1) (@lem3797508 A B f b n1)). Qed.
Lemma lem3797510 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3797511 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term80 A B f b n1) = (term81 A B f b n1).
Proof. exact (MK_COMB (@lem3797510) (@lem3797509 A B f b n1)). Qed.
Lemma lem3797512 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term66 A B f b n1 n2) = (term67 A B f b n1 n2).
Proof. exact (eq_refl (term66 A B f b n1 n2)). Qed.
Lemma lem3797513 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term82 A B f b n1) = (term61 A B f b n1).
Proof. exact (fun_ext (fun n2 : nat => @lem3797512 A B f b n1 n2)). Qed.
Lemma lem3797514 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3797515 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term83 A B f b n1) = (term20 A B f b n1).
Proof. exact (MK_COMB (@lem3797514) (@lem3797513 A B f b n1)). Qed.
Lemma lem3797516 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term60 A B f b n1) = (term84 A B f b n1).
Proof. exact (MK_COMB (@lem3797511 A B f b n1) (@lem3797515 A B f b n1)). Qed.
Lemma lem3797517 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : term84 A B f b n1.
Proof. exact (EQ_MP (@lem3797516 A B f b n1) (@lem3797497 A B f b n1)). Qed.
Lemma lem3797518 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) (h1 : term67 A B f b n1 n2) : term67 A B f b n1 n2.
Proof. exact (h1). Qed.
Lemma lem3797536 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term85 A B f b s a) = (term86 A B s a b).
Proof. exact (EQ_MP (@lem3791010 A B f s a b) (@lem3791009 A B f s a b)). Qed.
Lemma lem3797537 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term85 A B f b s a) = (term86 A B s a b).
Proof. exact (@lem3797536 A B f s a b). Qed.
Lemma lem3797538 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a1 : B) (b : B) : (term85 A B f b s a1) = (term86 A B s a1 b).
Proof. exact (@lem3797537 A B f s a1 b). Qed.
Lemma lem3797545 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3797546 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a1 : B) (b : B) : (term87 A B f b s a1) = (term88 A B s a1 b).
Proof. exact (MK_COMB (@lem3797545) (@lem3797538 A B f s a1 b)). Qed.
Lemma lem3797548 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term85 A B f b s a) = (term86 A B s a b).
Proof. exact (EQ_MP (@lem3791010 A B f s a b) (@lem3791009 A B f s a b)). Qed.
Lemma lem3797549 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term85 A B f b s a) = (term86 A B s a b).
Proof. exact (@lem3797548 A B f s a b). Qed.
Lemma lem3797550 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term85 A B f b s a2) = (term86 A B s a2 b).
Proof. exact (@lem3797549 A B f s a2 b). Qed.
Lemma lem3797557 {A B : Type'} (f : type1411 A B) (a1 : B) (s : A -> Prop) (a2 : B) (b : B) : (term89 A B a1 f b s a2) = (term90 A B a1 s a2 b).
Proof. exact (MK_COMB (@lem3797546 A B f s a1 b) (@lem3797550 A B f s a2 b)). Qed.
Lemma lem3797560 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3797561 {A B : Type'} (f : type1411 A B) (a1 : B) (s : A -> Prop) (a2 : B) (b : B) : (term91 A B a1 f b s a2) = (term92 A B a1 s a2 b).
Proof. exact (MK_COMB (@lem3797560) (@lem3797557 A B f a1 s a2 b)). Qed.
Lemma lem3797567 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3797568 (x : nat) : (x = x) = True.
Proof. exact (@lem3797567 nat x). Qed.
Lemma lem3797569 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem3797568 (NUMERAL 0)). Qed.
Lemma lem3797570 {B : Type'} (a1 : B) (a2 : B) : (term93 B a1 a2) = (term93 B a1 a2).
Proof. exact (eq_refl (term93 B a1 a2)). Qed.
Lemma lem3797571 {B : Type'} (a1 : B) (a2 : B) : (term94 B a1 a2) = (term95 B a1 a2).
Proof. exact (MK_COMB (@lem3797570 B a1 a2) (@lem3797569)). Qed.
Lemma lem3797573 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3797574 {B : Type'} (a1 : B) (a2 : B) : (term95 B a1 a2) = (a1 = a2).
Proof. exact (@lem3797573 (a1 = a2)). Qed.
Lemma lem3797577 {B : Type'} (a1 : B) (a2 : B) : (term94 B a1 a2) = (a1 = a2).
Proof. exact (TRANS (@lem3797571 B a1 a2) (@lem3797574 B a1 a2)). Qed.
Lemma lem3797578 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) : (term96 A B f b s a1 a2) = (term97 A B s b a1 a2).
Proof. exact (MK_COMB (@lem3797561 A B f a1 s a2 b) (@lem3797577 B a1 a2)). Qed.
Lemma lem3797581 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) : (term98 A B f b s a1) = (term99 A B s b a1).
Proof. exact (fun_ext (fun a2 : B => @lem3797578 A B f s b a1 a2)). Qed.
Lemma lem3797582 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3797583 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) : (term100 A B f b s a1) = (term101 A B s b a1).
Proof. exact (MK_COMB (@lem3797582 B) (@lem3797581 A B f s b a1)). Qed.
Lemma lem3797588 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) : (term102 A B f b s) = (term103 A B s b).
Proof. exact (fun_ext (fun a1 : B => @lem3797583 A B f s b a1)). Qed.
Lemma lem3797589 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3797590 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) : (term104 A B f b s) = (term105 A B s b).
Proof. exact (MK_COMB (@lem3797589 B) (@lem3797588 A B f s b)). Qed.
Lemma lem3797595 {A B : Type'} (f : type1411 A B) (b : B) : (term106 A B f b) = (term107 A B b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3797590 A B f s b)). Qed.
Lemma lem3797596 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3797597 {A B : Type'} (f : type1411 A B) (b : B) : (term38 A B f b) = (term108 A B b).
Proof. exact (MK_COMB (@lem3797596 A) (@lem3797595 A B f b)). Qed.
Lemma lem3797602 {A B : Type'} (f : type1411 A B) (b : B) : (term108 A B b) = (term38 A B f b).
Proof. exact (SYM (@lem3797597 A B f b)). Qed.
Lemma lem3797604 (p : Prop) : p = (term109 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3797605 {A B : Type'} (b : B) : (term108 A B b) = (term110 A B b).
Proof. exact (@lem3797604 (term108 A B b)). Qed.
Lemma lem3797606 {A B : Type'} (b : B) : (term110 A B b) = (term108 A B b).
Proof. exact (SYM (@lem3797605 A B b)). Qed.
Lemma lem3797607 {A B : Type'} (b : B) (h1 : term111 A B b) : term111 A B b.
Proof. exact (h1). Qed.
Lemma lem3797608 {A : Type'} : term112 A.
Proof. exact (@lem3204775 A). Qed.
Lemma lem3797611 {A B : Type'} (b : B) (h1 : term113 A B b) : term113 A B b.
Proof. exact (h1). Qed.
Lemma lem3797612 {A B : Type'} (b : B) : term114 A B b.
Proof. exact (fun h0 : term113 A B b => @lem3797611 A B b h0). Qed.
Lemma lem3797613 {A B : Type'} (b : B) (h1 : term114 A B b) : term114 A B b.
Proof. exact (h1). Qed.
Lemma lem3797614 {A B : Type'} (b : B) (h1 : term113 A B b) : term113 A B b.
Proof. exact (h1). Qed.
Lemma lem3797615 {A B : Type'} (b : B) (h1 : term113 A B b) (h2 : term114 A B b) : term113 A B b.
Proof. exact (@lem3797613 A B b h2 (@lem3797614 A B b h1)). Qed.
Lemma lem3797616 {A B : Type'} (b : B) (h1 : term113 A B b) : term115 A B b.
Proof. exact (fun h0 : term114 A B b => @lem3797615 A B b h1 h0). Qed.
Lemma lem3797617 {A B : Type'} (b : B) (h1 : term114 A B b) : term114 A B b.
Proof. exact (h1). Qed.
Lemma lem3797618 {A B : Type'} (b : B) (h1 : term113 A B b) (h2 : term114 A B b) : term113 A B b.
Proof. exact (@lem3797616 A B b h1 (@lem3797617 A B b h2)). Qed.
Lemma lem3797619 {A B : Type'} (b : B) (h1 : term114 A B b) : term114 A B b.
Proof. exact (fun h0 : term113 A B b => @lem3797618 A B b h0 h1). Qed.
Lemma lem3797620 {A B : Type'} (b : B) : term116 A B b.
Proof. exact (fun h0 : term114 A B b => @lem3797619 A B b h0). Qed.
Lemma lem3797623 {A B : Type'} (b : B) : term114 A B b.
Proof. exact (@lem3797620 A B b (@lem3797612 A B b)). Qed.
Lemma lem3797624 {A B : Type'} (b : B) : term114 A B b.
Proof. exact (@lem3797623 A B b). Qed.
Lemma lem3797652 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3797653 {A : Type'} : (term117 A) = (term118 A).
Proof. exact (@lem3797652 (term112 A)). Qed.
Lemma lem3797658 {A B : Type'} (b : B) : (term119 A B b) = (term119 A B b).
Proof. exact (eq_refl (term119 A B b)). Qed.
Lemma lem3797659 {A B : Type'} (b : B) : (term113 A B b) = (term120 A B b).
Proof. exact (MK_COMB (@lem3797658 A B b) (@lem3797653 A)). Qed.
Lemma lem3797662 {A B : Type'} : (term121 A B) = (term122 A B).
Proof. exact (fun_ext (fun b : B => @lem3797659 A B b)). Qed.
Lemma lem3797663 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3797672 {A B : Type'} : (term123 A B) = (term124 A B).
Proof. exact (MK_COMB (@lem3797663 B) (@lem3797662 A B)). Qed.
Lemma lem3797675 {A : Type'} (x : A) : (term125 A x) = (term125 A x).
Proof. exact (eq_refl (term125 A x)). Qed.
Lemma lem3797676 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (fun_ext (fun x : A => @lem3797675 A x)). Qed.
Lemma lem3797677 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3797678 {A : Type'} : (term112 A) = (term112 A).
Proof. exact (MK_COMB (@lem3797677 A) (@lem3797676 A)). Qed.
Lemma lem3797679 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3797680 {A : Type'} : (term118 A) = (term118 A).
Proof. exact (MK_COMB (@lem3797679) (@lem3797678 A)). Qed.
Lemma lem3797697 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) : (term97 A B s b a1 a2) = (term97 A B s b a1 a2).
Proof. exact (eq_refl (term97 A B s b a1 a2)). Qed.
Lemma lem3797698 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) : (term99 A B s b a1) = (term99 A B s b a1).
Proof. exact (fun_ext (fun a2 : B => @lem3797697 A B s b a1 a2)). Qed.
Lemma lem3797699 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3797700 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) : (term101 A B s b a1) = (term101 A B s b a1).
Proof. exact (MK_COMB (@lem3797699 B) (@lem3797698 A B s b a1)). Qed.
Lemma lem3797701 {A B : Type'} (s : A -> Prop) (b : B) : (term103 A B s b) = (term103 A B s b).
Proof. exact (fun_ext (fun a1 : B => @lem3797700 A B s b a1)). Qed.
Lemma lem3797702 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3797703 {A B : Type'} (s : A -> Prop) (b : B) : (term105 A B s b) = (term105 A B s b).
Proof. exact (MK_COMB (@lem3797702 B) (@lem3797701 A B s b)). Qed.
Lemma lem3797704 {A B : Type'} (b : B) : (term107 A B b) = (term107 A B b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3797703 A B s b)). Qed.
Lemma lem3797705 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3797706 {A B : Type'} (b : B) : (term108 A B b) = (term108 A B b).
Proof. exact (MK_COMB (@lem3797705 A) (@lem3797704 A B b)). Qed.
Lemma lem3797707 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3797708 {A B : Type'} (b : B) : (term111 A B b) = (term111 A B b).
Proof. exact (MK_COMB (@lem3797707) (@lem3797706 A B b)). Qed.
Lemma lem3797709 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3797710 {A B : Type'} (b : B) : (term119 A B b) = (term119 A B b).
Proof. exact (MK_COMB (@lem3797709) (@lem3797708 A B b)). Qed.
Lemma lem3797711 {A B : Type'} (b : B) : (term120 A B b) = (term120 A B b).
Proof. exact (MK_COMB (@lem3797710 A B b) (@lem3797680 A)). Qed.
Lemma lem3797712 {A B : Type'} : (term122 A B) = (term122 A B).
Proof. exact (fun_ext (fun b : B => @lem3797711 A B b)). Qed.
Lemma lem3797713 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3797714 {A B : Type'} : (term124 A B) = (term124 A B).
Proof. exact (MK_COMB (@lem3797713 B) (@lem3797712 A B)). Qed.
Lemma lem3797757 {A B : Type'} : (term123 A B) = (term124 A B).
Proof. exact (TRANS (@lem3797672 A B) (@lem3797714 A B)). Qed.
Lemma lem3797758 {A B : Type'} : (term124 A B) = (term123 A B).
Proof. exact (SYM (@lem3797757 A B)). Qed.
Lemma lem3797759 {A B : Type'} (b : B) (h1 : term111 A B b) : term111 A B b.
Proof. exact (h1). Qed.
Lemma lem3797779 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) : (term127 A B s b a1 a2) = (term128 A B s b a1 a2).
Proof. exact (@lem17362 (term90 A B a1 s a2 b) (a1 = a2)). Qed.
Lemma lem3797780 {B : Type'} (P : B -> Prop) : (term129 B P) = (term130 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem3797781 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) : (term131 A B s b a1) = (term132 A B s b a1).
Proof. exact (@lem3797780 B (term99 A B s b a1)). Qed.
Lemma lem3797782 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) : (term133 A B s b a1 a2) = (term97 A B s b a1 a2).
Proof. exact (eq_refl (term133 A B s b a1 a2)). Qed.
Lemma lem3797783 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3797784 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) : (term134 A B s b a1 a2) = (term127 A B s b a1 a2).
Proof. exact (MK_COMB (@lem3797783) (@lem3797782 A B s b a1 a2)). Qed.
Lemma lem3797785 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) : (term134 A B s b a1 a2) = (term128 A B s b a1 a2).
Proof. exact (TRANS (@lem3797784 A B s b a1 a2) (@lem3797779 A B s b a1 a2)). Qed.
Lemma lem3797786 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) : (term135 A B s b a1) = (term136 A B s b a1).
Proof. exact (fun_ext (fun a2 : B => @lem3797785 A B s b a1 a2)). Qed.
Lemma lem3797787 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3797788 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) : (term132 A B s b a1) = (term137 A B s b a1).
Proof. exact (MK_COMB (@lem3797787 B) (@lem3797786 A B s b a1)). Qed.
Lemma lem3797789 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) : (term131 A B s b a1) = (term137 A B s b a1).
Proof. exact (TRANS (@lem3797781 A B s b a1) (@lem3797788 A B s b a1)). Qed.
Lemma lem3797790 {B : Type'} (P : B -> Prop) : (term129 B P) = (term130 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem3797791 {A B : Type'} (s : A -> Prop) (b : B) : (term138 A B s b) = (term139 A B s b).
Proof. exact (@lem3797790 B (term103 A B s b)). Qed.
Lemma lem3797792 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) : (term140 A B s b a1) = (term101 A B s b a1).
Proof. exact (eq_refl (term140 A B s b a1)). Qed.
Lemma lem3797793 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3797794 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) : (term141 A B s b a1) = (term131 A B s b a1).
Proof. exact (MK_COMB (@lem3797793) (@lem3797792 A B s b a1)). Qed.
Lemma lem3797795 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) : (term141 A B s b a1) = (term137 A B s b a1).
Proof. exact (TRANS (@lem3797794 A B s b a1) (@lem3797789 A B s b a1)). Qed.
Lemma lem3797796 {A B : Type'} (s : A -> Prop) (b : B) : (term142 A B s b) = (term143 A B s b).
Proof. exact (fun_ext (fun a1 : B => @lem3797795 A B s b a1)). Qed.
Lemma lem3797797 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3797798 {A B : Type'} (s : A -> Prop) (b : B) : (term139 A B s b) = (term144 A B s b).
Proof. exact (MK_COMB (@lem3797797 B) (@lem3797796 A B s b)). Qed.
Lemma lem3797799 {A B : Type'} (s : A -> Prop) (b : B) : (term138 A B s b) = (term144 A B s b).
Proof. exact (TRANS (@lem3797791 A B s b) (@lem3797798 A B s b)). Qed.
Lemma lem3797800 {A : Type'} (P : type686 A) : (term145 A P) = (term146 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3797801 {A B : Type'} (b : B) : (term111 A B b) = (term147 A B b).
Proof. exact (@lem3797800 A (term107 A B b)). Qed.
Lemma lem3797802 {A B : Type'} (s : A -> Prop) (b : B) : (term148 A B b s) = (term105 A B s b).
Proof. exact (eq_refl (term148 A B b s)). Qed.
Lemma lem3797803 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3797804 {A B : Type'} (s : A -> Prop) (b : B) : (term149 A B b s) = (term138 A B s b).
Proof. exact (MK_COMB (@lem3797803) (@lem3797802 A B s b)). Qed.
Lemma lem3797805 {A B : Type'} (s : A -> Prop) (b : B) : (term149 A B b s) = (term144 A B s b).
Proof. exact (TRANS (@lem3797804 A B s b) (@lem3797799 A B s b)). Qed.
Lemma lem3797806 {A B : Type'} (b : B) : (term150 A B b) = (term151 A B b).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3797805 A B s b)). Qed.
Lemma lem3797807 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3797808 {A B : Type'} (b : B) : (term147 A B b) = (term152 A B b).
Proof. exact (MK_COMB (@lem3797807 A) (@lem3797806 A B b)). Qed.
Lemma lem3797869 {A B : Type'} (b : B) : (term111 A B b) = (term152 A B b).
Proof. exact (TRANS (@lem3797801 A B b) (@lem3797808 A B b)). Qed.
Lemma lem3797870 {A B : Type'} (b : B) (h1 : term111 A B b) : term152 A B b.
Proof. exact (EQ_MP (@lem3797869 A B b) (@lem3797759 A B b h1)). Qed.
Lemma lem3797884 {A B : Type'} (s : A -> Prop) (b : B) (h1 : term144 A B s b) : term144 A B s b.
Proof. exact (h1). Qed.
Lemma lem3797885 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (h1 : term137 A B s b a1) : term137 A B s b a1.
Proof. exact (h1). Qed.
Lemma lem3797937 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : term128 A B s b a1 a2.
Proof. exact (h1). Qed.
Lemma lem3797939 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : term90 A B a1 s a2 b.
Proof. exact (proj1 (@lem3797937 A B s b a1 a2 h1)). Qed.
Lemma lem3797940 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : term86 A B s a2 b.
Proof. exact (proj2 (@lem3797939 A B s b a1 a2 h1)). Qed.
Lemma lem3797941 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : term86 A B s a1 b.
Proof. exact (proj1 (@lem3797939 A B s b a1 a2 h1)). Qed.
Lemma lem3797979 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : term153 B a1 a2.
Proof. exact (proj2 (@lem3797937 A B s b a1 a2 h1)). Qed.
Lemma lem3797987 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : a1 = b.
Proof. exact (proj2 (@lem3797941 A B s b a1 a2 h1)). Qed.
Lemma lem3798016 {B : Type'} (a2 : B) : (term154 B a2) = (term154 B a2).
Proof. exact (eq_refl (term154 B a2)). Qed.
Lemma lem3798017 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : (term155 B a2 a1) = (term155 B a2 b).
Proof. exact (MK_COMB (@lem3798016 B a2) (@lem3797987 A B s b a1 a2 h1)). Qed.
Lemma lem3798018 {B : Type'} (b : B) (a2 : B) : (term155 B a2 b) = (term153 B b a2).
Proof. exact (eq_refl (term155 B a2 b)). Qed.
Lemma lem3798019 {B : Type'} (a2 : B) (a1 : B) : (term156 B a2 a1) = (term156 B a2 a1).
Proof. exact (eq_refl (term156 B a2 a1)). Qed.
Lemma lem3798020 {B : Type'} (a1 : B) (b : B) (a2 : B) : ((term155 B a2 a1) = (term155 B a2 b)) = ((term155 B a2 a1) = (term153 B b a2)).
Proof. exact (MK_COMB (@lem3798019 B a2 a1) (@lem3798018 B b a2)). Qed.
Lemma lem3798021 {B : Type'} (a1 : B) (a2 : B) : (term155 B a2 a1) = (term153 B a1 a2).
Proof. exact (eq_refl (term155 B a2 a1)). Qed.
Lemma lem3798022 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3798023 {B : Type'} (a1 : B) (a2 : B) : (term156 B a2 a1) = (term157 B a1 a2).
Proof. exact (MK_COMB (@lem3798022) (@lem3798021 B a1 a2)). Qed.
Lemma lem3798024 {B : Type'} (b : B) (a2 : B) : (term153 B b a2) = (term153 B b a2).
Proof. exact (eq_refl (term153 B b a2)). Qed.
Lemma lem3798025 {B : Type'} (a1 : B) (b : B) (a2 : B) : ((term155 B a2 a1) = (term153 B b a2)) = ((term153 B a1 a2) = (term153 B b a2)).
Proof. exact (MK_COMB (@lem3798023 B a1 a2) (@lem3798024 B b a2)). Qed.
Lemma lem3798026 {B : Type'} (a1 : B) (b : B) (a2 : B) : ((term155 B a2 a1) = (term155 B a2 b)) = ((term153 B a1 a2) = (term153 B b a2)).
Proof. exact (TRANS (@lem3798020 B a1 b a2) (@lem3798025 B a1 b a2)). Qed.
Lemma lem3798027 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : (term153 B a1 a2) = (term153 B b a2).
Proof. exact (EQ_MP (@lem3798026 B a1 b a2) (@lem3798017 A B s b a1 a2 h1)). Qed.
Lemma lem3798112 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : term153 B b a2.
Proof. exact (EQ_MP (@lem3798027 A B s b a1 a2 h1) (@lem3797979 A B s b a1 a2 h1)). Qed.
Lemma lem3798139 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : a2 = b.
Proof. exact (proj2 (@lem3797940 A B s b a1 a2 h1)). Qed.
Lemma lem3798168 {B : Type'} (b : B) : (term158 B b) = (term158 B b).
Proof. exact (eq_refl (term158 B b)). Qed.
Lemma lem3798169 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : (term159 B b a2) = (term160 B b).
Proof. exact (MK_COMB (@lem3798168 B b) (@lem3798139 A B s b a1 a2 h1)). Qed.
Lemma lem3798170 {B : Type'} (b : B) : (term160 B b) = (term161 B b).
Proof. exact (eq_refl (term160 B b)). Qed.
Lemma lem3798171 {B : Type'} (b : B) (a2 : B) : (term162 B b a2) = (term162 B b a2).
Proof. exact (eq_refl (term162 B b a2)). Qed.
Lemma lem3798172 {B : Type'} (a2 : B) (b : B) : ((term159 B b a2) = (term160 B b)) = ((term159 B b a2) = (term161 B b)).
Proof. exact (MK_COMB (@lem3798171 B b a2) (@lem3798170 B b)). Qed.
Lemma lem3798173 {B : Type'} (b : B) (a2 : B) : (term159 B b a2) = (term153 B b a2).
Proof. exact (eq_refl (term159 B b a2)). Qed.
Lemma lem3798174 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3798175 {B : Type'} (b : B) (a2 : B) : (term162 B b a2) = (term157 B b a2).
Proof. exact (MK_COMB (@lem3798174) (@lem3798173 B b a2)). Qed.
Lemma lem3798176 {B : Type'} (b : B) : (term161 B b) = (term161 B b).
Proof. exact (eq_refl (term161 B b)). Qed.
Lemma lem3798177 {B : Type'} (a2 : B) (b : B) : ((term159 B b a2) = (term161 B b)) = ((term153 B b a2) = (term161 B b)).
Proof. exact (MK_COMB (@lem3798175 B b a2) (@lem3798176 B b)). Qed.
Lemma lem3798178 {B : Type'} (a2 : B) (b : B) : ((term159 B b a2) = (term160 B b)) = ((term153 B b a2) = (term161 B b)).
Proof. exact (TRANS (@lem3798172 B a2 b) (@lem3798177 B a2 b)). Qed.
Lemma lem3798179 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : (term153 B b a2) = (term161 B b).
Proof. exact (EQ_MP (@lem3798178 B a2 b) (@lem3798169 A B s b a1 a2 h1)). Qed.
Lemma lem3798180 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : term161 B b.
Proof. exact (EQ_MP (@lem3798179 A B s b a1 a2 h1) (@lem3798112 A B s b a1 a2 h1)). Qed.
Lemma lem3798221 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3798222 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3798221 B x). Qed.
Lemma lem3798223 {B : Type'} (b : B) : b = b.
Proof. exact (@lem3798222 B b). Qed.
Lemma lem3798224 {B : Type'} (b : B) : term163 B b.
Proof. exact (fun h0 : term161 B b => @lem3798223 B b). Qed.
Lemma lem3798226 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3798227 {B : Type'} (b : B) : (term163 B b) = (b = b).
Proof. exact (@lem3798226 (b = b)). Qed.
Lemma lem3798228 {B : Type'} (b : B) : b = b.
Proof. exact (EQ_MP (@lem3798227 B b) (@lem3798224 B b)). Qed.
Lemma lem3798231 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3798233 {B : Type'} (b : B) : (term161 B b) = (term165 B b).
Proof. exact (@lem3798231 (b = b)). Qed.
Lemma lem3798236 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : term165 B b.
Proof. exact (EQ_MP (@lem3798233 B b) (@lem3798180 A B s b a1 a2 h1)). Qed.
Lemma lem3798239 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : False.
Proof. exact (@lem3798236 A B s b a1 a2 h1 (@lem3798228 B b)). Qed.
Lemma lem3798240 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : term166.
Proof. exact (fun h0 : ~ False => @lem3798239 A B s b a1 a2 h1). Qed.
Lemma lem3798242 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3798243 : term166 = False.
Proof. exact (@lem3798242 False). Qed.
Lemma lem3798247 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : False.
Proof. exact (EQ_MP (@lem3798243) (@lem3798240 A B s b a1 a2 h1)). Qed.
Lemma lem3798248 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : (term128 A B s b a1 a2) = False.
Proof. exact (prop_ext (fun h2 : term128 A B s b a1 a2 => @lem3798247 A B s b a1 a2 h1) (fun h2 : False => @lem3797937 A B s b a1 a2 h1)). Qed.
Lemma lem3798249 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (h1 : term128 A B s b a1 a2) : False.
Proof. exact (EQ_MP (@lem3798248 A B s b a1 a2 h1) (@lem3797937 A B s b a1 a2 h1)). Qed.
Lemma lem3798250 {A B : Type'} (s : A -> Prop) (b : B) (a1 : B) (h1 : term137 A B s b a1) : False.
Proof. exact (ex_elim (@lem3797885 A B s b a1 h1) (fun a2 : B => fun h0 : term136 A B s b a1 a2 => @lem3798249 A B s b a1 a2 h0)). Qed.
Lemma lem3798251 {A B : Type'} (s : A -> Prop) (b : B) (h1 : term144 A B s b) : False.
Proof. exact (ex_elim (@lem3797884 A B s b h1) (fun a1 : B => fun h0 : term143 A B s b a1 => @lem3798250 A B s b a1 h0)). Qed.
Lemma lem3798252 {A B : Type'} (b : B) (h1 : term111 A B b) : False.
Proof. exact (ex_elim (@lem3797870 A B b h1) (fun s : A -> Prop => fun h0 : term151 A B b s => @lem3798251 A B s b h0)). Qed.
Lemma lem3798253 {A B : Type'} (b : B) (h1 : term111 A B b) : term117 A.
Proof. exact (fun h0 : term112 A => @lem3798252 A B b h1). Qed.
Lemma lem3798254 {A : Type'} : (term117 A) = (term118 A).
Proof. exact (@lem69 (term112 A)). Qed.
Lemma lem3798255 {A B : Type'} (b : B) (h1 : term111 A B b) : term118 A.
Proof. exact (EQ_MP (@lem3798254 A) (@lem3798253 A B b h1)). Qed.
Lemma lem3798256 {A B : Type'} (b : B) : term120 A B b.
Proof. exact (fun h0 : term111 A B b => @lem3798255 A B b h0). Qed.
Lemma lem3798261 {A B : Type'} : term124 A B.
Proof. exact (fun b : B => @lem3798256 A B b). Qed.
Lemma lem3798262 {A B : Type'} : term123 A B.
Proof. exact (EQ_MP (@lem3797758 A B) (@lem3798261 A B)). Qed.
Lemma lem3798263 {A B : Type'} (b : B) : term167 A B b.
Proof. exact (@lem3798262 A B b). Qed.
Lemma lem3798264 {A B : Type'} (b : B) : (term167 A B b) = (term113 A B b).
Proof. exact (eq_refl (term167 A B b)). Qed.
Lemma lem3798265 {A B : Type'} (b : B) : term113 A B b.
Proof. exact (EQ_MP (@lem3798264 A B b) (@lem3798263 A B b)). Qed.
Lemma lem3798267 {A B : Type'} (b : B) : term113 A B b.
Proof. exact (@lem3797624 A B b (@lem3798265 A B b)). Qed.
Lemma lem3798268 {A B : Type'} (b : B) (h1 : term111 A B b) : term117 A.
Proof. exact (@lem3798267 A B b (@lem3797607 A B b h1)). Qed.
Lemma lem3798269 {A B : Type'} (b : B) (h1 : term111 A B b) : False.
Proof. exact (@lem3798268 A B b h1 (@lem3797608 A)). Qed.
Lemma lem3798270 {A B : Type'} (b : B) (h1 : term111 A B b) : (term111 A B b) = False.
Proof. exact (prop_ext (fun h2 : term111 A B b => @lem3798269 A B b h1) (fun h2 : False => @lem3797607 A B b h1)). Qed.
Lemma lem3798271 {A B : Type'} (b : B) (h1 : term111 A B b) : False.
Proof. exact (EQ_MP (@lem3798270 A B b h1) (@lem3797607 A B b h1)). Qed.
Lemma lem3798272 {A B : Type'} (b : B) : term110 A B b.
Proof. exact (fun h0 : term111 A B b => @lem3798271 A B b h0). Qed.
Lemma lem3798273 {A B : Type'} (b : B) : term108 A B b.
Proof. exact (EQ_MP (@lem3797606 A B b) (@lem3798272 A B b)). Qed.
Lemma lem3798274 {A B : Type'} (f : type1411 A B) (b : B) : term38 A B f b.
Proof. exact (EQ_MP (@lem3797602 A B f b) (@lem3798273 A B b)). Qed.
Lemma lem3798292 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term85 A B f b s a) = (term86 A B s a b).
Proof. exact (EQ_MP (@lem3791010 A B f s a b) (@lem3791009 A B f s a b)). Qed.
Lemma lem3798293 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term85 A B f b s a) = (term86 A B s a b).
Proof. exact (@lem3798292 A B f s a b). Qed.
Lemma lem3798294 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a1 : B) (b : B) : (term85 A B f b s a1) = (term86 A B s a1 b).
Proof. exact (@lem3798293 A B f s a1 b). Qed.
Lemma lem3798301 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3798302 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a1 : B) (b : B) : (term87 A B f b s a1) = (term88 A B s a1 b).
Proof. exact (MK_COMB (@lem3798301) (@lem3798294 A B f s a1 b)). Qed.
Lemma lem3798304 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term168 A B f b s a n) = (term169 A B b s n a f).
Proof. exact (EQ_MP (@lem3791025 A B b s n a f) (@lem3791024 A B b s n a f)). Qed.
Lemma lem3798305 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term168 A B f b s a n) = (term169 A B b s n a f).
Proof. exact (@lem3798304 A B b s n a f). Qed.
Lemma lem3798306 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term168 A B f b s a2 n2) = (term169 A B b s n2 a2 f).
Proof. exact (@lem3798305 A B b s n2 a2 f). Qed.
Lemma lem3798321 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term170 A B a1 f b s a2 n2) = (term171 A B a1 b s n2 a2 f).
Proof. exact (MK_COMB (@lem3798302 A B f s a1 b) (@lem3798306 A B b s n2 a2 f)). Qed.
Lemma lem3798324 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3798325 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term172 A B a1 f b s a2 n2) = (term173 A B a1 b s n2 a2 f).
Proof. exact (MK_COMB (@lem3798324) (@lem3798321 A B a1 b s n2 a2 f)). Qed.
Lemma lem3798332 {B : Type'} (a1 : B) (a2 : B) (n2 : nat) : (term174 B a1 a2 n2) = (term174 B a1 a2 n2).
Proof. exact (eq_refl (term174 B a1 a2 n2)). Qed.
Lemma lem3798333 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term175 A B f b s a1 a2 n2) = (term176 A B b s f a1 a2 n2).
Proof. exact (MK_COMB (@lem3798325 A B a1 b s n2 a2 f) (@lem3798332 B a1 a2 n2)). Qed.
Lemma lem3798336 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) : (term177 A B f b s a1 n2) = (term178 A B b s f a1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3798333 A B b s f a1 a2 n2)). Qed.
Lemma lem3798337 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3798338 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) : (term179 A B f b s a1 n2) = (term180 A B b s f a1 n2).
Proof. exact (MK_COMB (@lem3798337 B) (@lem3798336 A B b s f a1 n2)). Qed.
Lemma lem3798343 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) : (term181 A B f b s n2) = (term182 A B b s f n2).
Proof. exact (fun_ext (fun a1 : B => @lem3798338 A B b s f a1 n2)). Qed.
Lemma lem3798344 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3798345 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) : (term183 A B f b s n2) = (term184 A B b s f n2).
Proof. exact (MK_COMB (@lem3798344 B) (@lem3798343 A B b s f n2)). Qed.
Lemma lem3798350 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term185 A B f b n2) = (term186 A B b f n2).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3798345 A B b s f n2)). Qed.
Lemma lem3798351 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3798352 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term46 A B f b n2) = (term187 A B b f n2).
Proof. exact (MK_COMB (@lem3798351 A) (@lem3798350 A B b f n2)). Qed.
Lemma lem3798357 {A B : Type'} (f : type1411 A B) (b : B) (n2 : nat) : (term187 A B b f n2) = (term46 A B f b n2).
Proof. exact (SYM (@lem3798352 A B b f n2)). Qed.
Lemma lem3798359 (p : Prop) : p = (term109 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3798360 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term187 A B b f n2) = (term188 A B b f n2).
Proof. exact (@lem3798359 (term187 A B b f n2)). Qed.
Lemma lem3798361 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term188 A B b f n2) = (term187 A B b f n2).
Proof. exact (SYM (@lem3798360 A B b f n2)). Qed.
Lemma lem3798362 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term189 A B b f n2) : term189 A B b f n2.
Proof. exact (h1). Qed.
Lemma lem3798363 {A : Type'} : term112 A.
Proof. exact (@lem3204775 A). Qed.
Lemma lem3798367 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term190 A B b f n2) : term190 A B b f n2.
Proof. exact (h1). Qed.
Lemma lem3798368 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : term191 A B b f n2.
Proof. exact (fun h0 : term190 A B b f n2 => @lem3798367 A B b f n2 h0). Qed.
Lemma lem3798369 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term191 A B b f n2) : term191 A B b f n2.
Proof. exact (h1). Qed.
Lemma lem3798370 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term190 A B b f n2) : term190 A B b f n2.
Proof. exact (h1). Qed.
Lemma lem3798371 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term190 A B b f n2) (h2 : term191 A B b f n2) : term190 A B b f n2.
Proof. exact (@lem3798369 A B b f n2 h2 (@lem3798370 A B b f n2 h1)). Qed.
Lemma lem3798372 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term190 A B b f n2) : term192 A B b f n2.
Proof. exact (fun h0 : term191 A B b f n2 => @lem3798371 A B b f n2 h1 h0). Qed.
Lemma lem3798373 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term191 A B b f n2) : term191 A B b f n2.
Proof. exact (h1). Qed.
Lemma lem3798374 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term190 A B b f n2) (h2 : term191 A B b f n2) : term190 A B b f n2.
Proof. exact (@lem3798372 A B b f n2 h1 (@lem3798373 A B b f n2 h2)). Qed.
Lemma lem3798375 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term191 A B b f n2) : term191 A B b f n2.
Proof. exact (fun h0 : term190 A B b f n2 => @lem3798374 A B b f n2 h0 h1). Qed.
Lemma lem3798376 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : term193 A B b f n2.
Proof. exact (fun h0 : term191 A B b f n2 => @lem3798375 A B b f n2 h0). Qed.
Lemma lem3798379 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : term191 A B b f n2.
Proof. exact (@lem3798376 A B b f n2 (@lem3798368 A B b f n2)). Qed.
Lemma lem3798380 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : term191 A B b f n2.
Proof. exact (@lem3798379 A B b f n2). Qed.
Lemma lem3798418 {A : Type'} (P : Prop) (Q : A -> Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem3798419 {B : Type'} (P : Prop) (Q : B -> Prop) : (term194 B P Q) = (term195 B P Q).
Proof. exact (@lem3798418 B P Q). Qed.
Lemma lem3798420 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term196 A B b s n2 a2 f x) = (term197 A B b s n2 a2 f x).
Proof. exact (@lem3798419 B (@IN A x s) (term198 A B b s n2 a2 f x)). Qed.
Lemma lem3798421 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term199 A B b s n2 a2 f x c) = (term200 A B b s n2 a2 f x c).
Proof. exact (eq_refl (term199 A B b s n2 a2 f x c)). Qed.
Lemma lem3798422 {A : Type'} (x : A) (s : A -> Prop) : (term201 A x s) = (term201 A x s).
Proof. exact (eq_refl (term201 A x s)). Qed.
Lemma lem3798423 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term202 A B b s n2 a2 f x c) = (term203 A B b s n2 a2 f x c).
Proof. exact (MK_COMB (@lem3798422 A x s) (@lem3798421 A B b s n2 a2 f x c)). Qed.
Lemma lem3798424 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term204 A B b s n2 a2 f x) = (term205 A B b s n2 a2 f x).
Proof. exact (fun_ext (fun c : B => @lem3798423 A B b s n2 a2 f x c)). Qed.
Lemma lem3798425 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3798426 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term196 A B b s n2 a2 f x) = (term206 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3798425 B) (@lem3798424 A B b s n2 a2 f x)). Qed.
Lemma lem3798427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3798428 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term207 A B b s n2 a2 f x) = (term208 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3798427) (@lem3798426 A B b s n2 a2 f x)). Qed.
Lemma lem3798429 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term199 A B b s n2 a2 f x c) = (term200 A B b s n2 a2 f x c).
Proof. exact (eq_refl (term199 A B b s n2 a2 f x c)). Qed.
Lemma lem3798430 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term209 A B b s n2 a2 f x) = (term198 A B b s n2 a2 f x).
Proof. exact (fun_ext (fun c : B => @lem3798429 A B b s n2 a2 f x c)). Qed.
Lemma lem3798431 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3798432 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term210 A B b s n2 a2 f x) = (term211 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3798431 B) (@lem3798430 A B b s n2 a2 f x)). Qed.
Lemma lem3798433 {A : Type'} (x : A) (s : A -> Prop) : (term201 A x s) = (term201 A x s).
Proof. exact (eq_refl (term201 A x s)). Qed.
Lemma lem3798434 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term197 A B b s n2 a2 f x) = (term212 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3798433 A x s) (@lem3798432 A B b s n2 a2 f x)). Qed.
Lemma lem3798435 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : ((term196 A B b s n2 a2 f x) = (term197 A B b s n2 a2 f x)) = ((term206 A B b s n2 a2 f x) = (term212 A B b s n2 a2 f x)).
Proof. exact (MK_COMB (@lem3798428 A B b s n2 a2 f x) (@lem3798434 A B b s n2 a2 f x)). Qed.
Lemma lem3798436 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term206 A B b s n2 a2 f x) = (term212 A B b s n2 a2 f x).
Proof. exact (EQ_MP (@lem3798435 A B b s n2 a2 f x) (@lem3798420 A B b s n2 a2 f x)). Qed.
Lemma lem3798489 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term213 A B b s n2 a2 f) = (term214 A B b s n2 a2 f).
Proof. exact (fun_ext (fun x : A => @lem3798436 A B b s n2 a2 f x)). Qed.
Lemma lem3798490 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3798491 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term169 A B b s n2 a2 f) = (term215 A B b s n2 a2 f).
Proof. exact (MK_COMB (@lem3798490 A) (@lem3798489 A B b s n2 a2 f)). Qed.
Lemma lem3798540 {A B : Type'} (s : A -> Prop) (a1 : B) (b : B) : (term88 A B s a1 b) = (term88 A B s a1 b).
Proof. exact (eq_refl (term88 A B s a1 b)). Qed.
Lemma lem3798541 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term171 A B a1 b s n2 a2 f) = (term216 A B a1 b s n2 a2 f).
Proof. exact (MK_COMB (@lem3798540 A B s a1 b) (@lem3798491 A B b s n2 a2 f)). Qed.
Lemma lem3798544 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3798545 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term173 A B a1 b s n2 a2 f) = (term217 A B a1 b s n2 a2 f).
Proof. exact (MK_COMB (@lem3798544) (@lem3798541 A B a1 b s n2 a2 f)). Qed.
Lemma lem3798548 {B : Type'} (a1 : B) (a2 : B) (n2 : nat) : (term174 B a1 a2 n2) = (term174 B a1 a2 n2).
Proof. exact (eq_refl (term174 B a1 a2 n2)). Qed.
Lemma lem3798549 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term176 A B b s f a1 a2 n2) = (term218 A B b s f a1 a2 n2).
Proof. exact (MK_COMB (@lem3798545 A B a1 b s n2 a2 f) (@lem3798548 B a1 a2 n2)). Qed.
Lemma lem3798552 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) : (term178 A B b s f a1 n2) = (term219 A B b s f a1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3798549 A B b s f a1 a2 n2)). Qed.
Lemma lem3798553 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3798554 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) : (term180 A B b s f a1 n2) = (term220 A B b s f a1 n2).
Proof. exact (MK_COMB (@lem3798553 B) (@lem3798552 A B b s f a1 n2)). Qed.
Lemma lem3798559 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) : (term182 A B b s f n2) = (term221 A B b s f n2).
Proof. exact (fun_ext (fun a1 : B => @lem3798554 A B b s f a1 n2)). Qed.
Lemma lem3798560 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3798561 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) : (term184 A B b s f n2) = (term222 A B b s f n2).
Proof. exact (MK_COMB (@lem3798560 B) (@lem3798559 A B b s f n2)). Qed.
Lemma lem3798566 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term186 A B b f n2) = (term223 A B b f n2).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3798561 A B b s f n2)). Qed.
Lemma lem3798567 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3798568 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term187 A B b f n2) = (term224 A B b f n2).
Proof. exact (MK_COMB (@lem3798567 A) (@lem3798566 A B b f n2)). Qed.
Lemma lem3798573 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3798574 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term189 A B b f n2) = (term225 A B b f n2).
Proof. exact (MK_COMB (@lem3798573) (@lem3798568 A B b f n2)). Qed.
Lemma lem3798575 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3798576 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term226 A B b f n2) = (term227 A B b f n2).
Proof. exact (MK_COMB (@lem3798575) (@lem3798574 A B b f n2)). Qed.
Lemma lem3798578 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3798579 {A : Type'} : (term117 A) = (term118 A).
Proof. exact (@lem3798578 (term112 A)). Qed.
Lemma lem3798584 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term190 A B b f n2) = (term228 A B b f n2).
Proof. exact (MK_COMB (@lem3798576 A B b f n2) (@lem3798579 A)). Qed.
Lemma lem3798587 {A B : Type'} (f : type1411 A B) (n2 : nat) : (term229 A B f n2) = (term230 A B f n2).
Proof. exact (fun_ext (fun b : B => @lem3798584 A B b f n2)). Qed.
Lemma lem3798588 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3798589 {A B : Type'} (f : type1411 A B) (n2 : nat) : (term231 A B f n2) = (term232 A B f n2).
Proof. exact (MK_COMB (@lem3798588 B) (@lem3798587 A B f n2)). Qed.
Lemma lem3798594 {A B : Type'} (n2 : nat) : (term233 A B n2) = (term234 A B n2).
Proof. exact (fun_ext (fun f : type1411 A B => @lem3798589 A B f n2)). Qed.
Lemma lem3798595 {A B : Type'} : (@all (A -> B -> B)) = (@all (A -> B -> B)).
Proof. exact (eq_refl (@all (A -> B -> B))). Qed.
Lemma lem3798596 {A B : Type'} (n2 : nat) : (term235 A B n2) = (term236 A B n2).
Proof. exact (MK_COMB (@lem3798595 A B) (@lem3798594 A B n2)). Qed.
Lemma lem3798601 {A B : Type'} : (term237 A B) = (term238 A B).
Proof. exact (fun_ext (fun n2 : nat => @lem3798596 A B n2)). Qed.
Lemma lem3798602 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3798611 {A B : Type'} : (term239 A B) = (term240 A B).
Proof. exact (MK_COMB (@lem3798602) (@lem3798601 A B)). Qed.
Lemma lem3798614 {A : Type'} (x : A) : (term125 A x) = (term125 A x).
Proof. exact (eq_refl (term125 A x)). Qed.
Lemma lem3798615 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (fun_ext (fun x : A => @lem3798614 A x)). Qed.
Lemma lem3798616 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3798617 {A : Type'} : (term112 A) = (term112 A).
Proof. exact (MK_COMB (@lem3798616 A) (@lem3798615 A)). Qed.
Lemma lem3798618 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3798619 {A : Type'} : (term118 A) = (term118 A).
Proof. exact (MK_COMB (@lem3798618) (@lem3798617 A)). Qed.
Lemma lem3798624 {B : Type'} (a1 : B) (a2 : B) (n2 : nat) : (term174 B a1 a2 n2) = (term174 B a1 a2 n2).
Proof. exact (eq_refl (term174 B a1 a2 n2)). Qed.
Lemma lem3798629 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term200 A B b s n2 a2 f x c) = (term200 A B b s n2 a2 f x c).
Proof. exact (eq_refl (term200 A B b s n2 a2 f x c)). Qed.
Lemma lem3798630 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term198 A B b s n2 a2 f x) = (term198 A B b s n2 a2 f x).
Proof. exact (fun_ext (fun c : B => @lem3798629 A B b s n2 a2 f x c)). Qed.
Lemma lem3798631 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3798632 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term211 A B b s n2 a2 f x) = (term211 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3798631 B) (@lem3798630 A B b s n2 a2 f x)). Qed.
Lemma lem3798635 {A : Type'} (x : A) (s : A -> Prop) : (term201 A x s) = (term201 A x s).
Proof. exact (eq_refl (term201 A x s)). Qed.
Lemma lem3798636 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term212 A B b s n2 a2 f x) = (term212 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3798635 A x s) (@lem3798632 A B b s n2 a2 f x)). Qed.
Lemma lem3798637 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term214 A B b s n2 a2 f) = (term214 A B b s n2 a2 f).
Proof. exact (fun_ext (fun x : A => @lem3798636 A B b s n2 a2 f x)). Qed.
Lemma lem3798638 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3798639 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term215 A B b s n2 a2 f) = (term215 A B b s n2 a2 f).
Proof. exact (MK_COMB (@lem3798638 A) (@lem3798637 A B b s n2 a2 f)). Qed.
Lemma lem3798646 {A B : Type'} (s : A -> Prop) (a1 : B) (b : B) : (term88 A B s a1 b) = (term88 A B s a1 b).
Proof. exact (eq_refl (term88 A B s a1 b)). Qed.
Lemma lem3798647 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term216 A B a1 b s n2 a2 f) = (term216 A B a1 b s n2 a2 f).
Proof. exact (MK_COMB (@lem3798646 A B s a1 b) (@lem3798639 A B b s n2 a2 f)). Qed.
Lemma lem3798648 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3798649 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term217 A B a1 b s n2 a2 f) = (term217 A B a1 b s n2 a2 f).
Proof. exact (MK_COMB (@lem3798648) (@lem3798647 A B a1 b s n2 a2 f)). Qed.
Lemma lem3798650 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term218 A B b s f a1 a2 n2) = (term218 A B b s f a1 a2 n2).
Proof. exact (MK_COMB (@lem3798649 A B a1 b s n2 a2 f) (@lem3798624 B a1 a2 n2)). Qed.
Lemma lem3798651 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) : (term219 A B b s f a1 n2) = (term219 A B b s f a1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3798650 A B b s f a1 a2 n2)). Qed.
Lemma lem3798652 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3798653 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) : (term220 A B b s f a1 n2) = (term220 A B b s f a1 n2).
Proof. exact (MK_COMB (@lem3798652 B) (@lem3798651 A B b s f a1 n2)). Qed.
Lemma lem3798654 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) : (term221 A B b s f n2) = (term221 A B b s f n2).
Proof. exact (fun_ext (fun a1 : B => @lem3798653 A B b s f a1 n2)). Qed.
Lemma lem3798655 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3798656 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) : (term222 A B b s f n2) = (term222 A B b s f n2).
Proof. exact (MK_COMB (@lem3798655 B) (@lem3798654 A B b s f n2)). Qed.
Lemma lem3798657 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term223 A B b f n2) = (term223 A B b f n2).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3798656 A B b s f n2)). Qed.
Lemma lem3798658 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3798659 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term224 A B b f n2) = (term224 A B b f n2).
Proof. exact (MK_COMB (@lem3798658 A) (@lem3798657 A B b f n2)). Qed.
Lemma lem3798660 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3798661 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term225 A B b f n2) = (term225 A B b f n2).
Proof. exact (MK_COMB (@lem3798660) (@lem3798659 A B b f n2)). Qed.
Lemma lem3798662 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3798663 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term227 A B b f n2) = (term227 A B b f n2).
Proof. exact (MK_COMB (@lem3798662) (@lem3798661 A B b f n2)). Qed.
Lemma lem3798664 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term228 A B b f n2) = (term228 A B b f n2).
Proof. exact (MK_COMB (@lem3798663 A B b f n2) (@lem3798619 A)). Qed.
Lemma lem3798665 {A B : Type'} (f : type1411 A B) (n2 : nat) : (term230 A B f n2) = (term230 A B f n2).
Proof. exact (fun_ext (fun b : B => @lem3798664 A B b f n2)). Qed.
Lemma lem3798666 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3798667 {A B : Type'} (f : type1411 A B) (n2 : nat) : (term232 A B f n2) = (term232 A B f n2).
Proof. exact (MK_COMB (@lem3798666 B) (@lem3798665 A B f n2)). Qed.
Lemma lem3798668 {A B : Type'} (n2 : nat) : (term234 A B n2) = (term234 A B n2).
Proof. exact (fun_ext (fun f : type1411 A B => @lem3798667 A B f n2)). Qed.
Lemma lem3798669 {A B : Type'} : (@all (A -> B -> B)) = (@all (A -> B -> B)).
Proof. exact (eq_refl (@all (A -> B -> B))). Qed.
Lemma lem3798670 {A B : Type'} (n2 : nat) : (term236 A B n2) = (term236 A B n2).
Proof. exact (MK_COMB (@lem3798669 A B) (@lem3798668 A B n2)). Qed.
Lemma lem3798671 {A B : Type'} : (term238 A B) = (term238 A B).
Proof. exact (fun_ext (fun n2 : nat => @lem3798670 A B n2)). Qed.
Lemma lem3798672 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3798673 {A B : Type'} : (term240 A B) = (term240 A B).
Proof. exact (MK_COMB (@lem3798672) (@lem3798671 A B)). Qed.
Lemma lem3798744 {A B : Type'} : (term239 A B) = (term240 A B).
Proof. exact (TRANS (@lem3798611 A B) (@lem3798673 A B)). Qed.
Lemma lem3798745 {A B : Type'} : (term240 A B) = (term239 A B).
Proof. exact (SYM (@lem3798744 A B)). Qed.
Lemma lem3798746 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term225 A B b f n2) : term225 A B b f n2.
Proof. exact (h1). Qed.
Lemma lem3798747 {A : Type'} (h1 : term112 A) : term112 A.
Proof. exact (h1). Qed.
Lemma lem3798758 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term200 A B b s n2 a2 f x c) = (term200 A B b s n2 a2 f x c).
Proof. exact (eq_refl (term200 A B b s n2 a2 f x c)). Qed.
Lemma lem3798759 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term198 A B b s n2 a2 f x) = (term198 A B b s n2 a2 f x).
Proof. exact (fun_ext (fun c : B => @lem3798758 A B b s n2 a2 f x c)). Qed.
Lemma lem3798760 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3798761 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term211 A B b s n2 a2 f x) = (term211 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3798760 B) (@lem3798759 A B b s n2 a2 f x)). Qed.
Lemma lem3798763 {A : Type'} (x : A) (s : A -> Prop) : (term201 A x s) = (term201 A x s).
Proof. exact (eq_refl (term201 A x s)). Qed.
Lemma lem3798764 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term212 A B b s n2 a2 f x) = (term212 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3798763 A x s) (@lem3798761 A B b s n2 a2 f x)). Qed.
Lemma lem3798765 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term214 A B b s n2 a2 f) = (term214 A B b s n2 a2 f).
Proof. exact (fun_ext (fun x : A => @lem3798764 A B b s n2 a2 f x)). Qed.
Lemma lem3798766 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3798767 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term215 A B b s n2 a2 f) = (term215 A B b s n2 a2 f).
Proof. exact (MK_COMB (@lem3798766 A) (@lem3798765 A B b s n2 a2 f)). Qed.
Lemma lem3798769 {A B : Type'} (s : A -> Prop) (a1 : B) (b : B) : (term88 A B s a1 b) = (term88 A B s a1 b).
Proof. exact (eq_refl (term88 A B s a1 b)). Qed.
Lemma lem3798770 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term216 A B a1 b s n2 a2 f) = (term216 A B a1 b s n2 a2 f).
Proof. exact (MK_COMB (@lem3798769 A B s a1 b) (@lem3798767 A B b s n2 a2 f)). Qed.
Lemma lem3798777 {B : Type'} (a1 : B) (a2 : B) (n2 : nat) : (term241 B a1 a2 n2) = (term242 B a1 a2 n2).
Proof. exact (@lem17045 (a1 = a2) ((NUMERAL 0) = (S n2))). Qed.
Lemma lem3798778 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3798779 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term243 A B a1 b s n2 a2 f) = (term243 A B a1 b s n2 a2 f).
Proof. exact (MK_COMB (@lem3798778) (@lem3798770 A B a1 b s n2 a2 f)). Qed.
Lemma lem3798780 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term244 A B b s f a1 a2 n2) = (term245 A B b s f a1 a2 n2).
Proof. exact (MK_COMB (@lem3798779 A B a1 b s n2 a2 f) (@lem3798777 B a1 a2 n2)). Qed.
Lemma lem3798781 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term246 A B b s f a1 a2 n2) = (term244 A B b s f a1 a2 n2).
Proof. exact (@lem17362 (term216 A B a1 b s n2 a2 f) (term174 B a1 a2 n2)). Qed.
Lemma lem3798782 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term246 A B b s f a1 a2 n2) = (term245 A B b s f a1 a2 n2).
Proof. exact (TRANS (@lem3798781 A B b s f a1 a2 n2) (@lem3798780 A B b s f a1 a2 n2)). Qed.
Lemma lem3798783 {B : Type'} (P : B -> Prop) : (term129 B P) = (term130 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem3798784 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) : (term247 A B b s f a1 n2) = (term248 A B b s f a1 n2).
Proof. exact (@lem3798783 B (term219 A B b s f a1 n2)). Qed.
Lemma lem3798785 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term249 A B b s f a1 n2 a2) = (term218 A B b s f a1 a2 n2).
Proof. exact (eq_refl (term249 A B b s f a1 n2 a2)). Qed.
Lemma lem3798786 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3798787 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term250 A B b s f a1 n2 a2) = (term246 A B b s f a1 a2 n2).
Proof. exact (MK_COMB (@lem3798786) (@lem3798785 A B b s f a1 a2 n2)). Qed.
Lemma lem3798788 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term250 A B b s f a1 n2 a2) = (term245 A B b s f a1 a2 n2).
Proof. exact (TRANS (@lem3798787 A B b s f a1 a2 n2) (@lem3798782 A B b s f a1 a2 n2)). Qed.
Lemma lem3798789 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) : (term251 A B b s f a1 n2) = (term252 A B b s f a1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3798788 A B b s f a1 a2 n2)). Qed.
Lemma lem3798790 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3798791 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) : (term248 A B b s f a1 n2) = (term253 A B b s f a1 n2).
Proof. exact (MK_COMB (@lem3798790 B) (@lem3798789 A B b s f a1 n2)). Qed.
Lemma lem3798792 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) : (term247 A B b s f a1 n2) = (term253 A B b s f a1 n2).
Proof. exact (TRANS (@lem3798784 A B b s f a1 n2) (@lem3798791 A B b s f a1 n2)). Qed.
Lemma lem3798793 {B : Type'} (P : B -> Prop) : (term129 B P) = (term130 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem3798794 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) : (term254 A B b s f n2) = (term255 A B b s f n2).
Proof. exact (@lem3798793 B (term221 A B b s f n2)). Qed.
Lemma lem3798795 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) : (term256 A B b s f n2 a1) = (term220 A B b s f a1 n2).
Proof. exact (eq_refl (term256 A B b s f n2 a1)). Qed.
Lemma lem3798796 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3798797 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) : (term257 A B b s f n2 a1) = (term247 A B b s f a1 n2).
Proof. exact (MK_COMB (@lem3798796) (@lem3798795 A B b s f a1 n2)). Qed.
Lemma lem3798798 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) : (term257 A B b s f n2 a1) = (term253 A B b s f a1 n2).
Proof. exact (TRANS (@lem3798797 A B b s f a1 n2) (@lem3798792 A B b s f a1 n2)). Qed.
Lemma lem3798799 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) : (term258 A B b s f n2) = (term259 A B b s f n2).
Proof. exact (fun_ext (fun a1 : B => @lem3798798 A B b s f a1 n2)). Qed.
Lemma lem3798800 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3798801 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) : (term255 A B b s f n2) = (term260 A B b s f n2).
Proof. exact (MK_COMB (@lem3798800 B) (@lem3798799 A B b s f n2)). Qed.
Lemma lem3798802 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) : (term254 A B b s f n2) = (term260 A B b s f n2).
Proof. exact (TRANS (@lem3798794 A B b s f n2) (@lem3798801 A B b s f n2)). Qed.
Lemma lem3798803 {A : Type'} (P : type686 A) : (term145 A P) = (term146 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3798804 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term225 A B b f n2) = (term261 A B b f n2).
Proof. exact (@lem3798803 A (term223 A B b f n2)). Qed.
Lemma lem3798805 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) : (term262 A B b f n2 s) = (term222 A B b s f n2).
Proof. exact (eq_refl (term262 A B b f n2 s)). Qed.
Lemma lem3798806 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3798807 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) : (term263 A B b f n2 s) = (term254 A B b s f n2).
Proof. exact (MK_COMB (@lem3798806) (@lem3798805 A B b s f n2)). Qed.
Lemma lem3798808 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) : (term263 A B b f n2 s) = (term260 A B b s f n2).
Proof. exact (TRANS (@lem3798807 A B b s f n2) (@lem3798802 A B b s f n2)). Qed.
Lemma lem3798809 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term264 A B b f n2) = (term265 A B b f n2).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3798808 A B b s f n2)). Qed.
Lemma lem3798810 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3798811 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term261 A B b f n2) = (term266 A B b f n2).
Proof. exact (MK_COMB (@lem3798810 A) (@lem3798809 A B b f n2)). Qed.
Lemma lem3798812 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term225 A B b f n2) = (term266 A B b f n2).
Proof. exact (TRANS (@lem3798804 A B b f n2) (@lem3798811 A B b f n2)). Qed.
Lemma lem3798967 {A : Type'} (P : Prop) (Q : A -> Prop) : (term195 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3798968 {B : Type'} (P : Prop) (Q : B -> Prop) : (term195 B P Q) = (term194 B P Q).
Proof. exact (@lem3798967 B P Q). Qed.
Lemma lem3798969 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term197 A B b s n2 a2 f x) = (term196 A B b s n2 a2 f x).
Proof. exact (@lem3798968 B (@IN A x s) (term198 A B b s n2 a2 f x)). Qed.
Lemma lem3798970 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term199 A B b s n2 a2 f x c) = (term200 A B b s n2 a2 f x c).
Proof. exact (eq_refl (term199 A B b s n2 a2 f x c)). Qed.
Lemma lem3798971 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term209 A B b s n2 a2 f x) = (term198 A B b s n2 a2 f x).
Proof. exact (fun_ext (fun c : B => @lem3798970 A B b s n2 a2 f x c)). Qed.
Lemma lem3798972 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3798973 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term210 A B b s n2 a2 f x) = (term211 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3798972 B) (@lem3798971 A B b s n2 a2 f x)). Qed.
Lemma lem3798974 {A : Type'} (x : A) (s : A -> Prop) : (term201 A x s) = (term201 A x s).
Proof. exact (eq_refl (term201 A x s)). Qed.
Lemma lem3798975 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term197 A B b s n2 a2 f x) = (term212 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3798974 A x s) (@lem3798973 A B b s n2 a2 f x)). Qed.
Lemma lem3798976 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3798977 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term267 A B b s n2 a2 f x) = (term268 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3798976) (@lem3798975 A B b s n2 a2 f x)). Qed.
Lemma lem3798978 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term199 A B b s n2 a2 f x c) = (term200 A B b s n2 a2 f x c).
Proof. exact (eq_refl (term199 A B b s n2 a2 f x c)). Qed.
Lemma lem3798979 {A : Type'} (x : A) (s : A -> Prop) : (term201 A x s) = (term201 A x s).
Proof. exact (eq_refl (term201 A x s)). Qed.
Lemma lem3798980 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term202 A B b s n2 a2 f x c) = (term203 A B b s n2 a2 f x c).
Proof. exact (MK_COMB (@lem3798979 A x s) (@lem3798978 A B b s n2 a2 f x c)). Qed.
Lemma lem3798981 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term204 A B b s n2 a2 f x) = (term205 A B b s n2 a2 f x).
Proof. exact (fun_ext (fun c : B => @lem3798980 A B b s n2 a2 f x c)). Qed.
Lemma lem3798982 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3798983 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term196 A B b s n2 a2 f x) = (term206 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3798982 B) (@lem3798981 A B b s n2 a2 f x)). Qed.
Lemma lem3798984 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : ((term197 A B b s n2 a2 f x) = (term196 A B b s n2 a2 f x)) = ((term212 A B b s n2 a2 f x) = (term206 A B b s n2 a2 f x)).
Proof. exact (MK_COMB (@lem3798977 A B b s n2 a2 f x) (@lem3798983 A B b s n2 a2 f x)). Qed.
Lemma lem3798985 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term212 A B b s n2 a2 f x) = (term206 A B b s n2 a2 f x).
Proof. exact (EQ_MP (@lem3798984 A B b s n2 a2 f x) (@lem3798969 A B b s n2 a2 f x)). Qed.
Lemma lem3798986 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term214 A B b s n2 a2 f) = (term213 A B b s n2 a2 f).
Proof. exact (fun_ext (fun x : A => @lem3798985 A B b s n2 a2 f x)). Qed.
Lemma lem3798987 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3798988 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term215 A B b s n2 a2 f) = (term169 A B b s n2 a2 f).
Proof. exact (MK_COMB (@lem3798987 A) (@lem3798986 A B b s n2 a2 f)). Qed.
Lemma lem3798989 {A B : Type'} (s : A -> Prop) (a1 : B) (b : B) : (term88 A B s a1 b) = (term88 A B s a1 b).
Proof. exact (eq_refl (term88 A B s a1 b)). Qed.
Lemma lem3798990 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term216 A B a1 b s n2 a2 f) = (term171 A B a1 b s n2 a2 f).
Proof. exact (MK_COMB (@lem3798989 A B s a1 b) (@lem3798988 A B b s n2 a2 f)). Qed.
Lemma lem3798992 {A : Type'} (P : Prop) (Q : A -> Prop) : (term195 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3798993 {A : Type'} (P : Prop) (Q : A -> Prop) : (term195 A P Q) = (term194 A P Q).
Proof. exact (@lem3798992 A P Q). Qed.
Lemma lem3798994 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term269 A B a1 b s n2 a2 f) = (term270 A B a1 b s n2 a2 f).
Proof. exact (@lem3798993 A (term86 A B s a1 b) (term213 A B b s n2 a2 f)). Qed.
Lemma lem3798995 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term271 A B b s n2 a2 f x) = (term206 A B b s n2 a2 f x).
Proof. exact (eq_refl (term271 A B b s n2 a2 f x)). Qed.
Lemma lem3798996 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term272 A B b s n2 a2 f) = (term213 A B b s n2 a2 f).
Proof. exact (fun_ext (fun x : A => @lem3798995 A B b s n2 a2 f x)). Qed.
Lemma lem3798997 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3798998 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term273 A B b s n2 a2 f) = (term169 A B b s n2 a2 f).
Proof. exact (MK_COMB (@lem3798997 A) (@lem3798996 A B b s n2 a2 f)). Qed.
Lemma lem3798999 {A B : Type'} (s : A -> Prop) (a1 : B) (b : B) : (term88 A B s a1 b) = (term88 A B s a1 b).
Proof. exact (eq_refl (term88 A B s a1 b)). Qed.
Lemma lem3799000 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term269 A B a1 b s n2 a2 f) = (term171 A B a1 b s n2 a2 f).
Proof. exact (MK_COMB (@lem3798999 A B s a1 b) (@lem3798998 A B b s n2 a2 f)). Qed.
Lemma lem3799001 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3799002 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term274 A B a1 b s n2 a2 f) = (term275 A B a1 b s n2 a2 f).
Proof. exact (MK_COMB (@lem3799001) (@lem3799000 A B a1 b s n2 a2 f)). Qed.
Lemma lem3799003 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term271 A B b s n2 a2 f x) = (term206 A B b s n2 a2 f x).
Proof. exact (eq_refl (term271 A B b s n2 a2 f x)). Qed.
Lemma lem3799004 {A B : Type'} (s : A -> Prop) (a1 : B) (b : B) : (term88 A B s a1 b) = (term88 A B s a1 b).
Proof. exact (eq_refl (term88 A B s a1 b)). Qed.
Lemma lem3799005 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term276 A B a1 b s n2 a2 f x) = (term277 A B a1 b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3799004 A B s a1 b) (@lem3799003 A B b s n2 a2 f x)). Qed.
Lemma lem3799006 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term278 A B a1 b s n2 a2 f) = (term279 A B a1 b s n2 a2 f).
Proof. exact (fun_ext (fun x : A => @lem3799005 A B a1 b s n2 a2 f x)). Qed.
Lemma lem3799007 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3799008 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term270 A B a1 b s n2 a2 f) = (term280 A B a1 b s n2 a2 f).
Proof. exact (MK_COMB (@lem3799007 A) (@lem3799006 A B a1 b s n2 a2 f)). Qed.
Lemma lem3799009 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : ((term269 A B a1 b s n2 a2 f) = (term270 A B a1 b s n2 a2 f)) = ((term171 A B a1 b s n2 a2 f) = (term280 A B a1 b s n2 a2 f)).
Proof. exact (MK_COMB (@lem3799002 A B a1 b s n2 a2 f) (@lem3799008 A B a1 b s n2 a2 f)). Qed.
Lemma lem3799010 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term171 A B a1 b s n2 a2 f) = (term280 A B a1 b s n2 a2 f).
Proof. exact (EQ_MP (@lem3799009 A B a1 b s n2 a2 f) (@lem3798994 A B a1 b s n2 a2 f)). Qed.
Lemma lem3799012 {A : Type'} (P : Prop) (Q : A -> Prop) : (term195 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3799013 {B : Type'} (P : Prop) (Q : B -> Prop) : (term195 B P Q) = (term194 B P Q).
Proof. exact (@lem3799012 B P Q). Qed.
Lemma lem3799014 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term281 A B a1 b s n2 a2 f x) = (term282 A B a1 b s n2 a2 f x).
Proof. exact (@lem3799013 B (term86 A B s a1 b) (term205 A B b s n2 a2 f x)). Qed.
Lemma lem3799015 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term283 A B b s n2 a2 f x c) = (term203 A B b s n2 a2 f x c).
Proof. exact (eq_refl (term283 A B b s n2 a2 f x c)). Qed.
Lemma lem3799016 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term284 A B b s n2 a2 f x) = (term205 A B b s n2 a2 f x).
Proof. exact (fun_ext (fun c : B => @lem3799015 A B b s n2 a2 f x c)). Qed.
Lemma lem3799017 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3799018 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term285 A B b s n2 a2 f x) = (term206 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3799017 B) (@lem3799016 A B b s n2 a2 f x)). Qed.
Lemma lem3799019 {A B : Type'} (s : A -> Prop) (a1 : B) (b : B) : (term88 A B s a1 b) = (term88 A B s a1 b).
Proof. exact (eq_refl (term88 A B s a1 b)). Qed.
Lemma lem3799020 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term281 A B a1 b s n2 a2 f x) = (term277 A B a1 b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3799019 A B s a1 b) (@lem3799018 A B b s n2 a2 f x)). Qed.
Lemma lem3799021 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3799022 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term286 A B a1 b s n2 a2 f x) = (term287 A B a1 b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3799021) (@lem3799020 A B a1 b s n2 a2 f x)). Qed.
Lemma lem3799023 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term283 A B b s n2 a2 f x c) = (term203 A B b s n2 a2 f x c).
Proof. exact (eq_refl (term283 A B b s n2 a2 f x c)). Qed.
Lemma lem3799024 {A B : Type'} (s : A -> Prop) (a1 : B) (b : B) : (term88 A B s a1 b) = (term88 A B s a1 b).
Proof. exact (eq_refl (term88 A B s a1 b)). Qed.
Lemma lem3799025 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term288 A B a1 b s n2 a2 f x c) = (term289 A B a1 b s n2 a2 f x c).
Proof. exact (MK_COMB (@lem3799024 A B s a1 b) (@lem3799023 A B b s n2 a2 f x c)). Qed.
Lemma lem3799026 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term290 A B a1 b s n2 a2 f x) = (term291 A B a1 b s n2 a2 f x).
Proof. exact (fun_ext (fun c : B => @lem3799025 A B a1 b s n2 a2 f x c)). Qed.
Lemma lem3799027 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3799028 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term282 A B a1 b s n2 a2 f x) = (term292 A B a1 b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3799027 B) (@lem3799026 A B a1 b s n2 a2 f x)). Qed.
Lemma lem3799029 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : ((term281 A B a1 b s n2 a2 f x) = (term282 A B a1 b s n2 a2 f x)) = ((term277 A B a1 b s n2 a2 f x) = (term292 A B a1 b s n2 a2 f x)).
Proof. exact (MK_COMB (@lem3799022 A B a1 b s n2 a2 f x) (@lem3799028 A B a1 b s n2 a2 f x)). Qed.
Lemma lem3799030 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term277 A B a1 b s n2 a2 f x) = (term292 A B a1 b s n2 a2 f x).
Proof. exact (EQ_MP (@lem3799029 A B a1 b s n2 a2 f x) (@lem3799014 A B a1 b s n2 a2 f x)). Qed.
Lemma lem3799031 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term279 A B a1 b s n2 a2 f) = (term293 A B a1 b s n2 a2 f).
Proof. exact (fun_ext (fun x : A => @lem3799030 A B a1 b s n2 a2 f x)). Qed.
Lemma lem3799032 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3799033 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term280 A B a1 b s n2 a2 f) = (term294 A B a1 b s n2 a2 f).
Proof. exact (MK_COMB (@lem3799032 A) (@lem3799031 A B a1 b s n2 a2 f)). Qed.
Lemma lem3799034 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term171 A B a1 b s n2 a2 f) = (term294 A B a1 b s n2 a2 f).
Proof. exact (TRANS (@lem3799010 A B a1 b s n2 a2 f) (@lem3799033 A B a1 b s n2 a2 f)). Qed.
Lemma lem3799035 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term216 A B a1 b s n2 a2 f) = (term294 A B a1 b s n2 a2 f).
Proof. exact (TRANS (@lem3798990 A B a1 b s n2 a2 f) (@lem3799034 A B a1 b s n2 a2 f)). Qed.
Lemma lem3799036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3799037 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term243 A B a1 b s n2 a2 f) = (term295 A B a1 b s n2 a2 f).
Proof. exact (MK_COMB (@lem3799036) (@lem3799035 A B a1 b s n2 a2 f)). Qed.
Lemma lem3799038 {B : Type'} (a1 : B) (a2 : B) (n2 : nat) : (term242 B a1 a2 n2) = (term242 B a1 a2 n2).
Proof. exact (eq_refl (term242 B a1 a2 n2)). Qed.
Lemma lem3799039 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term245 A B b s f a1 a2 n2) = (term296 A B b s f a1 a2 n2).
Proof. exact (MK_COMB (@lem3799037 A B a1 b s n2 a2 f) (@lem3799038 B a1 a2 n2)). Qed.
Lemma lem3799041 {A : Type'} (P : A -> Prop) (Q : Prop) : (term297 A P Q) = (term298 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3799042 {A : Type'} (P : A -> Prop) (Q : Prop) : (term297 A P Q) = (term298 A P Q).
Proof. exact (@lem3799041 A P Q). Qed.
Lemma lem3799043 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term299 A B b s f a1 a2 n2) = (term300 A B b s f a1 a2 n2).
Proof. exact (@lem3799042 A (term293 A B a1 b s n2 a2 f) (term242 B a1 a2 n2)). Qed.
Lemma lem3799044 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term301 A B a1 b s n2 a2 f x) = (term292 A B a1 b s n2 a2 f x).
Proof. exact (eq_refl (term301 A B a1 b s n2 a2 f x)). Qed.
Lemma lem3799045 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term302 A B a1 b s n2 a2 f) = (term293 A B a1 b s n2 a2 f).
Proof. exact (fun_ext (fun x : A => @lem3799044 A B a1 b s n2 a2 f x)). Qed.
Lemma lem3799046 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3799047 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term303 A B a1 b s n2 a2 f) = (term294 A B a1 b s n2 a2 f).
Proof. exact (MK_COMB (@lem3799046 A) (@lem3799045 A B a1 b s n2 a2 f)). Qed.
Lemma lem3799048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3799049 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term304 A B a1 b s n2 a2 f) = (term295 A B a1 b s n2 a2 f).
Proof. exact (MK_COMB (@lem3799048) (@lem3799047 A B a1 b s n2 a2 f)). Qed.
Lemma lem3799050 {B : Type'} (a1 : B) (a2 : B) (n2 : nat) : (term242 B a1 a2 n2) = (term242 B a1 a2 n2).
Proof. exact (eq_refl (term242 B a1 a2 n2)). Qed.
Lemma lem3799051 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term299 A B b s f a1 a2 n2) = (term296 A B b s f a1 a2 n2).
Proof. exact (MK_COMB (@lem3799049 A B a1 b s n2 a2 f) (@lem3799050 B a1 a2 n2)). Qed.
Lemma lem3799052 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3799053 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term305 A B b s f a1 a2 n2) = (term306 A B b s f a1 a2 n2).
Proof. exact (MK_COMB (@lem3799052) (@lem3799051 A B b s f a1 a2 n2)). Qed.
Lemma lem3799054 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term301 A B a1 b s n2 a2 f x) = (term292 A B a1 b s n2 a2 f x).
Proof. exact (eq_refl (term301 A B a1 b s n2 a2 f x)). Qed.
Lemma lem3799055 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3799056 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term307 A B a1 b s n2 a2 f x) = (term308 A B a1 b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3799055) (@lem3799054 A B a1 b s n2 a2 f x)). Qed.
Lemma lem3799057 {B : Type'} (a1 : B) (a2 : B) (n2 : nat) : (term242 B a1 a2 n2) = (term242 B a1 a2 n2).
Proof. exact (eq_refl (term242 B a1 a2 n2)). Qed.
Lemma lem3799058 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (a1 : B) (a2 : B) (n2 : nat) : (term309 A B b s f x a1 a2 n2) = (term310 A B b s f x a1 a2 n2).
Proof. exact (MK_COMB (@lem3799056 A B a1 b s n2 a2 f x) (@lem3799057 B a1 a2 n2)). Qed.
Lemma lem3799059 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term311 A B b s f a1 a2 n2) = (term312 A B b s f a1 a2 n2).
Proof. exact (fun_ext (fun x : A => @lem3799058 A B b s f x a1 a2 n2)). Qed.
Lemma lem3799060 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3799061 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term300 A B b s f a1 a2 n2) = (term313 A B b s f a1 a2 n2).
Proof. exact (MK_COMB (@lem3799060 A) (@lem3799059 A B b s f a1 a2 n2)). Qed.
Lemma lem3799062 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : ((term299 A B b s f a1 a2 n2) = (term300 A B b s f a1 a2 n2)) = ((term296 A B b s f a1 a2 n2) = (term313 A B b s f a1 a2 n2)).
Proof. exact (MK_COMB (@lem3799053 A B b s f a1 a2 n2) (@lem3799061 A B b s f a1 a2 n2)). Qed.
Lemma lem3799063 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term296 A B b s f a1 a2 n2) = (term313 A B b s f a1 a2 n2).
Proof. exact (EQ_MP (@lem3799062 A B b s f a1 a2 n2) (@lem3799043 A B b s f a1 a2 n2)). Qed.
Lemma lem3799065 {A : Type'} (P : A -> Prop) (Q : Prop) : (term297 A P Q) = (term298 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3799066 {B : Type'} (P : B -> Prop) (Q : Prop) : (term297 B P Q) = (term298 B P Q).
Proof. exact (@lem3799065 B P Q). Qed.
Lemma lem3799067 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (a1 : B) (a2 : B) (n2 : nat) : (term314 A B b s f x a1 a2 n2) = (term315 A B b s f x a1 a2 n2).
Proof. exact (@lem3799066 B (term291 A B a1 b s n2 a2 f x) (term242 B a1 a2 n2)). Qed.
Lemma lem3799068 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term316 A B a1 b s n2 a2 f x c) = (term289 A B a1 b s n2 a2 f x c).
Proof. exact (eq_refl (term316 A B a1 b s n2 a2 f x c)). Qed.
Lemma lem3799069 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term317 A B a1 b s n2 a2 f x) = (term291 A B a1 b s n2 a2 f x).
Proof. exact (fun_ext (fun c : B => @lem3799068 A B a1 b s n2 a2 f x c)). Qed.
Lemma lem3799070 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3799071 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term318 A B a1 b s n2 a2 f x) = (term292 A B a1 b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3799070 B) (@lem3799069 A B a1 b s n2 a2 f x)). Qed.
Lemma lem3799072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3799073 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term319 A B a1 b s n2 a2 f x) = (term308 A B a1 b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3799072) (@lem3799071 A B a1 b s n2 a2 f x)). Qed.
Lemma lem3799074 {B : Type'} (a1 : B) (a2 : B) (n2 : nat) : (term242 B a1 a2 n2) = (term242 B a1 a2 n2).
Proof. exact (eq_refl (term242 B a1 a2 n2)). Qed.
Lemma lem3799075 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (a1 : B) (a2 : B) (n2 : nat) : (term314 A B b s f x a1 a2 n2) = (term310 A B b s f x a1 a2 n2).
Proof. exact (MK_COMB (@lem3799073 A B a1 b s n2 a2 f x) (@lem3799074 B a1 a2 n2)). Qed.
Lemma lem3799076 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3799077 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (a1 : B) (a2 : B) (n2 : nat) : (term320 A B b s f x a1 a2 n2) = (term321 A B b s f x a1 a2 n2).
Proof. exact (MK_COMB (@lem3799076) (@lem3799075 A B b s f x a1 a2 n2)). Qed.
Lemma lem3799078 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term316 A B a1 b s n2 a2 f x c) = (term289 A B a1 b s n2 a2 f x c).
Proof. exact (eq_refl (term316 A B a1 b s n2 a2 f x c)). Qed.
Lemma lem3799079 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3799080 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term322 A B a1 b s n2 a2 f x c) = (term323 A B a1 b s n2 a2 f x c).
Proof. exact (MK_COMB (@lem3799079) (@lem3799078 A B a1 b s n2 a2 f x c)). Qed.
Lemma lem3799081 {B : Type'} (a1 : B) (a2 : B) (n2 : nat) : (term242 B a1 a2 n2) = (term242 B a1 a2 n2).
Proof. exact (eq_refl (term242 B a1 a2 n2)). Qed.
Lemma lem3799082 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) : (term324 A B b s f x c a1 a2 n2) = (term325 A B b s f x c a1 a2 n2).
Proof. exact (MK_COMB (@lem3799080 A B a1 b s n2 a2 f x c) (@lem3799081 B a1 a2 n2)). Qed.
Lemma lem3799083 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (a1 : B) (a2 : B) (n2 : nat) : (term326 A B b s f x a1 a2 n2) = (term327 A B b s f x a1 a2 n2).
Proof. exact (fun_ext (fun c : B => @lem3799082 A B b s f x c a1 a2 n2)). Qed.
Lemma lem3799084 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3799085 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (a1 : B) (a2 : B) (n2 : nat) : (term315 A B b s f x a1 a2 n2) = (term328 A B b s f x a1 a2 n2).
Proof. exact (MK_COMB (@lem3799084 B) (@lem3799083 A B b s f x a1 a2 n2)). Qed.
Lemma lem3799086 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (a1 : B) (a2 : B) (n2 : nat) : ((term314 A B b s f x a1 a2 n2) = (term315 A B b s f x a1 a2 n2)) = ((term310 A B b s f x a1 a2 n2) = (term328 A B b s f x a1 a2 n2)).
Proof. exact (MK_COMB (@lem3799077 A B b s f x a1 a2 n2) (@lem3799085 A B b s f x a1 a2 n2)). Qed.
Lemma lem3799087 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (a1 : B) (a2 : B) (n2 : nat) : (term310 A B b s f x a1 a2 n2) = (term328 A B b s f x a1 a2 n2).
Proof. exact (EQ_MP (@lem3799086 A B b s f x a1 a2 n2) (@lem3799067 A B b s f x a1 a2 n2)). Qed.
Lemma lem3799088 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term312 A B b s f a1 a2 n2) = (term329 A B b s f a1 a2 n2).
Proof. exact (fun_ext (fun x : A => @lem3799087 A B b s f x a1 a2 n2)). Qed.
Lemma lem3799089 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3799090 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term313 A B b s f a1 a2 n2) = (term330 A B b s f a1 a2 n2).
Proof. exact (MK_COMB (@lem3799089 A) (@lem3799088 A B b s f a1 a2 n2)). Qed.
Lemma lem3799091 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term296 A B b s f a1 a2 n2) = (term330 A B b s f a1 a2 n2).
Proof. exact (TRANS (@lem3799063 A B b s f a1 a2 n2) (@lem3799090 A B b s f a1 a2 n2)). Qed.
Lemma lem3799092 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) : (term245 A B b s f a1 a2 n2) = (term330 A B b s f a1 a2 n2).
Proof. exact (TRANS (@lem3799039 A B b s f a1 a2 n2) (@lem3799091 A B b s f a1 a2 n2)). Qed.
Lemma lem3799093 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) : (term252 A B b s f a1 n2) = (term331 A B b s f a1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3799092 A B b s f a1 a2 n2)). Qed.
Lemma lem3799094 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3799095 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) : (term253 A B b s f a1 n2) = (term332 A B b s f a1 n2).
Proof. exact (MK_COMB (@lem3799094 B) (@lem3799093 A B b s f a1 n2)). Qed.
Lemma lem3799096 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) : (term259 A B b s f n2) = (term333 A B b s f n2).
Proof. exact (fun_ext (fun a1 : B => @lem3799095 A B b s f a1 n2)). Qed.
Lemma lem3799097 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3799098 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) : (term260 A B b s f n2) = (term334 A B b s f n2).
Proof. exact (MK_COMB (@lem3799097 B) (@lem3799096 A B b s f n2)). Qed.
Lemma lem3799099 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term265 A B b f n2) = (term335 A B b f n2).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3799098 A B b s f n2)). Qed.
Lemma lem3799100 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3799102 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term266 A B b f n2) = (term336 A B b f n2).
Proof. exact (MK_COMB (@lem3799100 A) (@lem3799099 A B b f n2)). Qed.
Lemma lem3799103 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term225 A B b f n2) = (term336 A B b f n2).
Proof. exact (TRANS (@lem3798812 A B b f n2) (@lem3799102 A B b f n2)). Qed.
Lemma lem3799104 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term225 A B b f n2) : term336 A B b f n2.
Proof. exact (EQ_MP (@lem3799103 A B b f n2) (@lem3798746 A B b f n2 h1)). Qed.
Lemma lem3799105 {A : Type'} (x : A) : (term125 A x) = (term125 A x).
Proof. exact (eq_refl (term125 A x)). Qed.
Lemma lem3799106 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (fun_ext (fun x : A => @lem3799105 A x)). Qed.
Lemma lem3799107 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3799116 {A : Type'} : (term112 A) = (term112 A).
Proof. exact (MK_COMB (@lem3799107 A) (@lem3799106 A)). Qed.
Lemma lem3799117 {A : Type'} (h1 : term112 A) : term112 A.
Proof. exact (EQ_MP (@lem3799116 A) (@lem3798747 A h1)). Qed.
Lemma lem3799118 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) (h1 : term334 A B b s f n2) : term334 A B b s f n2.
Proof. exact (h1). Qed.
Lemma lem3799119 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) (h1 : term332 A B b s f a1 n2) : term332 A B b s f a1 n2.
Proof. exact (h1). Qed.
Lemma lem3799120 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term330 A B b s f a1 a2 n2) : term330 A B b s f a1 a2 n2.
Proof. exact (h1). Qed.
Lemma lem3799121 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (a1 : B) (a2 : B) (n2 : nat) (h1 : term328 A B b s f x a1 a2 n2) : term328 A B b s f x a1 a2 n2.
Proof. exact (h1). Qed.
Lemma lem3799122 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : term325 A B b s f x c a1 a2 n2.
Proof. exact (h1). Qed.
Lemma lem3799129 {A : Type'} (x : A) : (term125 A x) = (term125 A x).
Proof. exact (eq_refl (term125 A x)). Qed.
Lemma lem3799130 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (fun_ext (fun x : A => @lem3799129 A x)). Qed.
Lemma lem3799131 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3799132 {A : Type'} : (term112 A) = (term112 A).
Proof. exact (MK_COMB (@lem3799131 A) (@lem3799130 A)). Qed.
Lemma lem3799133 {A : Type'} (h1 : term112 A) : term112 A.
Proof. exact (EQ_MP (@lem3799132 A) (@lem3799117 A h1)). Qed.
Lemma lem3799154 {B : Type'} (a1 : B) (a2 : B) (n2 : nat) : (term242 B a1 a2 n2) = (term242 B a1 a2 n2).
Proof. exact (eq_refl (term242 B a1 a2 n2)). Qed.
Lemma lem3799163 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3799164 {A B : Type'} (f : type1411 A B) (x : A) : (f x) = (@I (A -> B -> B) f x).
Proof. exact (@lem3799163 A (B -> B) f x). Qed.
Lemma lem3799165 {B : Type'} (c : B) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem3799166 {A B : Type'} (f : type1411 A B) (x : A) (c : B) : (f x c) = (@I (A -> B -> B) f x c).
Proof. exact (MK_COMB (@lem3799164 A B f x) (@lem3799165 B c)). Qed.
Lemma lem3799168 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3799169 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem3799168 B B f x). Qed.
Lemma lem3799170 {A B : Type'} (f : type1411 A B) (x : A) (c : B) : (@I (A -> B -> B) f x c) = (term337 A B f x c).
Proof. exact (@lem3799169 B (@I (A -> B -> B) f x) c). Qed.
Lemma lem3799172 {A B : Type'} (f : type1411 A B) (x : A) (c : B) : (f x c) = (term337 A B f x c).
Proof. exact (TRANS (@lem3799166 A B f x c) (@lem3799170 A B f x c)). Qed.
Lemma lem3799173 {B : Type'} (a2 : B) : (@eq B a2) = (@eq B a2).
Proof. exact (eq_refl (@eq B a2)). Qed.
Lemma lem3799174 {A B : Type'} (a2 : B) (f : type1411 A B) (x : A) (c : B) : (a2 = (f x c)) = (a2 = (term337 A B f x c)).
Proof. exact (MK_COMB (@lem3799173 B a2) (@lem3799172 A B f x c)). Qed.
Lemma lem3799191 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n2 : nat) : (term338 A B f b s x c n2) = (term338 A B f b s x c n2).
Proof. exact (eq_refl (term338 A B f b s x c n2)). Qed.
Lemma lem3799192 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term200 A B b s n2 a2 f x c) = (term339 A B b s n2 a2 f x c).
Proof. exact (MK_COMB (@lem3799191 A B f b s x c n2) (@lem3799174 A B a2 f x c)). Qed.
Lemma lem3799199 {A : Type'} (x : A) (s : A -> Prop) : (term201 A x s) = (term201 A x s).
Proof. exact (eq_refl (term201 A x s)). Qed.
Lemma lem3799200 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term203 A B b s n2 a2 f x c) = (term340 A B b s n2 a2 f x c).
Proof. exact (MK_COMB (@lem3799199 A x s) (@lem3799192 A B b s n2 a2 f x c)). Qed.
Lemma lem3799215 {A B : Type'} (s : A -> Prop) (a1 : B) (b : B) : (term88 A B s a1 b) = (term88 A B s a1 b).
Proof. exact (eq_refl (term88 A B s a1 b)). Qed.
Lemma lem3799216 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term289 A B a1 b s n2 a2 f x c) = (term341 A B a1 b s n2 a2 f x c).
Proof. exact (MK_COMB (@lem3799215 A B s a1 b) (@lem3799200 A B b s n2 a2 f x c)). Qed.
Lemma lem3799217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3799218 {A B : Type'} (a1 : B) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (c : B) : (term323 A B a1 b s n2 a2 f x c) = (term342 A B a1 b s n2 a2 f x c).
Proof. exact (MK_COMB (@lem3799217) (@lem3799216 A B a1 b s n2 a2 f x c)). Qed.
Lemma lem3799219 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) : (term325 A B b s f x c a1 a2 n2) = (term343 A B b s f x c a1 a2 n2).
Proof. exact (MK_COMB (@lem3799218 A B a1 b s n2 a2 f x c) (@lem3799154 B a1 a2 n2)). Qed.
Lemma lem3799220 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : term343 A B b s f x c a1 a2 n2.
Proof. exact (EQ_MP (@lem3799219 A B b s f x c a1 a2 n2) (@lem3799122 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3799221 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : term242 B a1 a2 n2.
Proof. exact (proj2 (@lem3799220 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3799222 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : term341 A B a1 b s n2 a2 f x c.
Proof. exact (proj1 (@lem3799220 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3799223 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : term340 A B b s n2 a2 f x c.
Proof. exact (proj2 (@lem3799222 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3799224 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : term86 A B s a1 b.
Proof. exact (proj1 (@lem3799222 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3799234 {A : Type'} (x : A) : (term125 A x) = (term125 A x).
Proof. exact (eq_refl (term125 A x)). Qed.
Lemma lem3799235 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (fun_ext (fun x : A => @lem3799234 A x)). Qed.
Lemma lem3799236 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3799238 {A : Type'} : (term112 A) = (term112 A).
Proof. exact (MK_COMB (@lem3799236 A) (@lem3799235 A)). Qed.
Lemma lem3799239 {A : Type'} (h1 : term112 A) : term112 A.
Proof. exact (EQ_MP (@lem3799238 A) (@lem3799133 A h1)). Qed.
Lemma lem3799265 {A : Type'} (x : A) : (term125 A x) = (term125 A x).
Proof. exact (eq_refl (term125 A x)). Qed.
Lemma lem3799266 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (fun_ext (fun x : A => @lem3799265 A x)). Qed.
Lemma lem3799267 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3799269 {A : Type'} : (term112 A) = (term112 A).
Proof. exact (MK_COMB (@lem3799267 A) (@lem3799266 A)). Qed.
Lemma lem3799270 {A : Type'} (h1 : term112 A) : term112 A.
Proof. exact (EQ_MP (@lem3799269 A) (@lem3799133 A h1)). Qed.
Lemma lem3799295 {A : Type'} (_43747 : A) (h1 : term112 A) : term344 A _43747.
Proof. exact (@lem3799239 A h1 _43747). Qed.
Lemma lem3799296 {A : Type'} (_43747 : A) : (term344 A _43747) = (term125 A _43747).
Proof. exact (eq_refl (term344 A _43747)). Qed.
Lemma lem3799298 {A : Type'} (_43748 : A) (h1 : term112 A) : term344 A _43748.
Proof. exact (@lem3799270 A h1 _43748). Qed.
Lemma lem3799299 {A : Type'} (_43748 : A) : (term344 A _43748) = (term125 A _43748).
Proof. exact (eq_refl (term344 A _43748)). Qed.
Lemma lem3799370 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : @IN A x s.
Proof. exact (proj1 (@lem3799223 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3799412 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : s = (@EMPTY A).
Proof. exact (proj1 (@lem3799224 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3799454 {A : Type'} (x : A) : (term345 A x) = (term345 A x).
Proof. exact (eq_refl (term345 A x)). Qed.
Lemma lem3799455 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : (term346 A x s) = (term347 A x).
Proof. exact (MK_COMB (@lem3799454 A x) (@lem3799412 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3799456 {A : Type'} (x : A) : (term347 A x) = (@IN A x (@EMPTY A)).
Proof. exact (eq_refl (term347 A x)). Qed.
Lemma lem3799457 {A : Type'} (x : A) (s : A -> Prop) : (term348 A x s) = (term348 A x s).
Proof. exact (eq_refl (term348 A x s)). Qed.
Lemma lem3799458 {A : Type'} (s : A -> Prop) (x : A) : ((term346 A x s) = (term347 A x)) = ((term346 A x s) = (@IN A x (@EMPTY A))).
Proof. exact (MK_COMB (@lem3799457 A x s) (@lem3799456 A x)). Qed.
Lemma lem3799459 {A : Type'} (x : A) (s : A -> Prop) : (term346 A x s) = (@IN A x s).
Proof. exact (eq_refl (term346 A x s)). Qed.
Lemma lem3799460 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3799461 {A : Type'} (x : A) (s : A -> Prop) : (term348 A x s) = (term349 A x s).
Proof. exact (MK_COMB (@lem3799460) (@lem3799459 A x s)). Qed.
Lemma lem3799462 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = (@IN A x (@EMPTY A)).
Proof. exact (eq_refl (@IN A x (@EMPTY A))). Qed.
Lemma lem3799463 {A : Type'} (s : A -> Prop) (x : A) : ((term346 A x s) = (@IN A x (@EMPTY A))) = ((@IN A x s) = (@IN A x (@EMPTY A))).
Proof. exact (MK_COMB (@lem3799461 A x s) (@lem3799462 A x)). Qed.
Lemma lem3799464 {A : Type'} (s : A -> Prop) (x : A) : ((term346 A x s) = (term347 A x)) = ((@IN A x s) = (@IN A x (@EMPTY A))).
Proof. exact (TRANS (@lem3799458 A s x) (@lem3799463 A s x)). Qed.
Lemma lem3799465 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : (@IN A x s) = (@IN A x (@EMPTY A)).
Proof. exact (EQ_MP (@lem3799464 A s x) (@lem3799455 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3799535 {A : Type'} (_43747 : A) (h1 : term112 A) : term125 A _43747.
Proof. exact (EQ_MP (@lem3799296 A _43747) (@lem3799295 A _43747 h1)). Qed.
Lemma lem3799618 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : @IN A x s.
Proof. exact (proj1 (@lem3799223 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3799660 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : s = (@EMPTY A).
Proof. exact (proj1 (@lem3799224 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3799703 {A : Type'} (x : A) : (term345 A x) = (term345 A x).
Proof. exact (eq_refl (term345 A x)). Qed.
Lemma lem3799704 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : (term346 A x s) = (term347 A x).
Proof. exact (MK_COMB (@lem3799703 A x) (@lem3799660 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3799705 {A : Type'} (x : A) : (term347 A x) = (@IN A x (@EMPTY A)).
Proof. exact (eq_refl (term347 A x)). Qed.
Lemma lem3799706 {A : Type'} (x : A) (s : A -> Prop) : (term348 A x s) = (term348 A x s).
Proof. exact (eq_refl (term348 A x s)). Qed.
Lemma lem3799707 {A : Type'} (s : A -> Prop) (x : A) : ((term346 A x s) = (term347 A x)) = ((term346 A x s) = (@IN A x (@EMPTY A))).
Proof. exact (MK_COMB (@lem3799706 A x s) (@lem3799705 A x)). Qed.
Lemma lem3799708 {A : Type'} (x : A) (s : A -> Prop) : (term346 A x s) = (@IN A x s).
Proof. exact (eq_refl (term346 A x s)). Qed.
Lemma lem3799709 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3799710 {A : Type'} (x : A) (s : A -> Prop) : (term348 A x s) = (term349 A x s).
Proof. exact (MK_COMB (@lem3799709) (@lem3799708 A x s)). Qed.
Lemma lem3799711 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = (@IN A x (@EMPTY A)).
Proof. exact (eq_refl (@IN A x (@EMPTY A))). Qed.
Lemma lem3799712 {A : Type'} (s : A -> Prop) (x : A) : ((term346 A x s) = (@IN A x (@EMPTY A))) = ((@IN A x s) = (@IN A x (@EMPTY A))).
Proof. exact (MK_COMB (@lem3799710 A x s) (@lem3799711 A x)). Qed.
Lemma lem3799713 {A : Type'} (s : A -> Prop) (x : A) : ((term346 A x s) = (term347 A x)) = ((@IN A x s) = (@IN A x (@EMPTY A))).
Proof. exact (TRANS (@lem3799707 A s x) (@lem3799712 A s x)). Qed.
Lemma lem3799714 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : (@IN A x s) = (@IN A x (@EMPTY A)).
Proof. exact (EQ_MP (@lem3799713 A s x) (@lem3799704 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3799784 {A : Type'} (_43748 : A) (h1 : term112 A) : term125 A _43748.
Proof. exact (EQ_MP (@lem3799299 A _43748) (@lem3799298 A _43748 h1)). Qed.
Lemma lem3799944 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : @IN A x (@EMPTY A).
Proof. exact (EQ_MP (@lem3799465 A B b s f x c a1 a2 n2 h1) (@lem3799370 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3799945 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : term350 A x.
Proof. exact (fun h0 : term125 A x => @lem3799944 A B b s f x c a1 a2 n2 h1). Qed.
Lemma lem3799947 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3799948 {A : Type'} (x : A) : (term350 A x) = (@IN A x (@EMPTY A)).
Proof. exact (@lem3799947 (@IN A x (@EMPTY A))). Qed.
Lemma lem3799949 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : @IN A x (@EMPTY A).
Proof. exact (EQ_MP (@lem3799948 A x) (@lem3799945 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3799952 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3799954 {A : Type'} (_43747 : A) : (term125 A _43747) = (term351 A _43747).
Proof. exact (@lem3799952 (@IN A _43747 (@EMPTY A))). Qed.
Lemma lem3799957 {A : Type'} (_43747 : A) (h1 : term112 A) : term351 A _43747.
Proof. exact (EQ_MP (@lem3799954 A _43747) (@lem3799535 A _43747 h1)). Qed.
Lemma lem3799958 {A : Type'} (_43747 : A) (h1 : term112 A) : term351 A _43747.
Proof. exact (@lem3799957 A _43747 h1). Qed.
Lemma lem3799959 {A : Type'} (x : A) (h1 : term112 A) : term351 A x.
Proof. exact (@lem3799958 A x h1). Qed.
Lemma lem3799962 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term112 A) (h2 : term325 A B b s f x c a1 a2 n2) : False.
Proof. exact (@lem3799959 A x h1 (@lem3799949 A B b s f x c a1 a2 n2 h2)). Qed.
Lemma lem3799963 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term112 A) (h2 : term325 A B b s f x c a1 a2 n2) : term166.
Proof. exact (fun h0 : ~ False => @lem3799962 A B b s f x c a1 a2 n2 h1 h2). Qed.
Lemma lem3799965 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3799966 : term166 = False.
Proof. exact (@lem3799965 False). Qed.
Lemma lem3800069 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : @IN A x (@EMPTY A).
Proof. exact (EQ_MP (@lem3799714 A B b s f x c a1 a2 n2 h1) (@lem3799618 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3800070 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : term350 A x.
Proof. exact (fun h0 : term125 A x => @lem3800069 A B b s f x c a1 a2 n2 h1). Qed.
Lemma lem3800072 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3800073 {A : Type'} (x : A) : (term350 A x) = (@IN A x (@EMPTY A)).
Proof. exact (@lem3800072 (@IN A x (@EMPTY A))). Qed.
Lemma lem3800074 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term325 A B b s f x c a1 a2 n2) : @IN A x (@EMPTY A).
Proof. exact (EQ_MP (@lem3800073 A x) (@lem3800070 A B b s f x c a1 a2 n2 h1)). Qed.
Lemma lem3800077 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3800079 {A : Type'} (_43748 : A) : (term125 A _43748) = (term351 A _43748).
Proof. exact (@lem3800077 (@IN A _43748 (@EMPTY A))). Qed.
Lemma lem3800082 {A : Type'} (_43748 : A) (h1 : term112 A) : term351 A _43748.
Proof. exact (EQ_MP (@lem3800079 A _43748) (@lem3799784 A _43748 h1)). Qed.
Lemma lem3800083 {A : Type'} (_43748 : A) (h1 : term112 A) : term351 A _43748.
Proof. exact (@lem3800082 A _43748 h1). Qed.
Lemma lem3800084 {A : Type'} (x : A) (h1 : term112 A) : term351 A x.
Proof. exact (@lem3800083 A x h1). Qed.
Lemma lem3800087 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term112 A) (h2 : term325 A B b s f x c a1 a2 n2) : False.
Proof. exact (@lem3800084 A x h1 (@lem3800074 A B b s f x c a1 a2 n2 h2)). Qed.
Lemma lem3800088 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term112 A) (h2 : term325 A B b s f x c a1 a2 n2) : term166.
Proof. exact (fun h0 : ~ False => @lem3800087 A B b s f x c a1 a2 n2 h1 h2). Qed.
Lemma lem3800090 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3800091 : term166 = False.
Proof. exact (@lem3800090 False). Qed.
Lemma lem3800095 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term112 A) (h2 : term325 A B b s f x c a1 a2 n2) : False.
Proof. exact (EQ_MP (@lem3800091) (@lem3800088 A B b s f x c a1 a2 n2 h1 h2)). Qed.
Lemma lem3800098 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term112 A) (h2 : term325 A B b s f x c a1 a2 n2) : False.
Proof. exact (EQ_MP (@lem3799966) (@lem3799963 A B b s f x c a1 a2 n2 h1 h2)). Qed.
Lemma lem3800099 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term112 A) (h2 : term325 A B b s f x c a1 a2 n2) : (term112 A) = False.
Proof. exact (prop_ext (fun h3 : term112 A => @lem3800095 A B b s f x c a1 a2 n2 h1 h2) (fun h3 : False => @lem3799270 A h1)). Qed.
Lemma lem3800100 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term112 A) (h2 : term325 A B b s f x c a1 a2 n2) : False.
Proof. exact (EQ_MP (@lem3800099 A B b s f x c a1 a2 n2 h1 h2) (@lem3799270 A h1)). Qed.
Lemma lem3800101 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term112 A) (h2 : term325 A B b s f x c a1 a2 n2) : (term112 A) = False.
Proof. exact (prop_ext (fun h3 : term112 A => @lem3800098 A B b s f x c a1 a2 n2 h1 h2) (fun h3 : False => @lem3799239 A h1)). Qed.
Lemma lem3800102 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term112 A) (h2 : term325 A B b s f x c a1 a2 n2) : False.
Proof. exact (EQ_MP (@lem3800101 A B b s f x c a1 a2 n2 h1 h2) (@lem3799239 A h1)). Qed.
Lemma lem3800103 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term112 A) (h2 : term325 A B b s f x c a1 a2 n2) : False.
Proof. exact (or_elim (@lem3799221 A B b s f x c a1 a2 n2 h2) (fun h0 : term153 B a1 a2 => @lem3800102 A B b s f x c a1 a2 n2 h1 h2) (fun h0 : term352 n2 => @lem3800100 A B b s f x c a1 a2 n2 h1 h2)). Qed.
Lemma lem3800104 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term112 A) (h2 : term325 A B b s f x c a1 a2 n2) : (term112 A) = False.
Proof. exact (prop_ext (fun h3 : term112 A => @lem3800103 A B b s f x c a1 a2 n2 h1 h2) (fun h3 : False => @lem3799133 A h1)). Qed.
Lemma lem3800105 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term112 A) (h2 : term325 A B b s f x c a1 a2 n2) : False.
Proof. exact (EQ_MP (@lem3800104 A B b s f x c a1 a2 n2 h1 h2) (@lem3799133 A h1)). Qed.
Lemma lem3800106 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (a1 : B) (a2 : B) (n2 : nat) (h1 : term112 A) (h2 : term328 A B b s f x a1 a2 n2) : False.
Proof. exact (ex_elim (@lem3799121 A B b s f x a1 a2 n2 h2) (fun c : B => fun h0 : term327 A B b s f x a1 a2 n2 c => @lem3800105 A B b s f x c a1 a2 n2 h1 h0)). Qed.
Lemma lem3800107 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n2 : nat) (h1 : term112 A) (h2 : term330 A B b s f a1 a2 n2) : False.
Proof. exact (ex_elim (@lem3799120 A B b s f a1 a2 n2 h2) (fun x : A => fun h0 : term329 A B b s f a1 a2 n2 x => @lem3800106 A B b s f x a1 a2 n2 h1 h0)). Qed.
Lemma lem3800108 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (n2 : nat) (h1 : term112 A) (h2 : term332 A B b s f a1 n2) : False.
Proof. exact (ex_elim (@lem3799119 A B b s f a1 n2 h2) (fun a2 : B => fun h0 : term331 A B b s f a1 n2 a2 => @lem3800107 A B b s f a1 a2 n2 h1 h0)). Qed.
Lemma lem3800109 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (n2 : nat) (h1 : term112 A) (h2 : term334 A B b s f n2) : False.
Proof. exact (ex_elim (@lem3799118 A B b s f n2 h2) (fun a1 : B => fun h0 : term333 A B b s f n2 a1 => @lem3800108 A B b s f a1 n2 h1 h0)). Qed.
Lemma lem3800110 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term112 A) (h2 : term225 A B b f n2) : False.
Proof. exact (ex_elim (@lem3799104 A B b f n2 h2) (fun s : A -> Prop => fun h0 : term335 A B b f n2 s => @lem3800109 A B b s f n2 h1 h0)). Qed.
Lemma lem3800111 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term112 A) (h2 : term225 A B b f n2) : (term112 A) = False.
Proof. exact (prop_ext (fun h3 : term112 A => @lem3800110 A B b f n2 h1 h2) (fun h3 : False => @lem3799117 A h1)). Qed.
Lemma lem3800112 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term112 A) (h2 : term225 A B b f n2) : False.
Proof. exact (EQ_MP (@lem3800111 A B b f n2 h1 h2) (@lem3799117 A h1)). Qed.
Lemma lem3800113 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term225 A B b f n2) : term117 A.
Proof. exact (fun h0 : term112 A => @lem3800112 A B b f n2 h0 h1). Qed.
Lemma lem3800114 {A : Type'} : (term117 A) = (term118 A).
Proof. exact (@lem69 (term112 A)). Qed.
Lemma lem3800115 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term225 A B b f n2) : term118 A.
Proof. exact (EQ_MP (@lem3800114 A) (@lem3800113 A B b f n2 h1)). Qed.
Lemma lem3800116 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : term228 A B b f n2.
Proof. exact (fun h0 : term225 A B b f n2 => @lem3800115 A B b f n2 h0). Qed.
Lemma lem3800121 {A B : Type'} (f : type1411 A B) (n2 : nat) : term232 A B f n2.
Proof. exact (fun b : B => @lem3800116 A B b f n2). Qed.
Lemma lem3800126 {A B : Type'} (n2 : nat) : term236 A B n2.
Proof. exact (fun f : type1411 A B => @lem3800121 A B f n2). Qed.
Lemma lem3800131 {A B : Type'} : term240 A B.
Proof. exact (fun n2 : nat => @lem3800126 A B n2). Qed.
Lemma lem3800132 {A B : Type'} : term239 A B.
Proof. exact (EQ_MP (@lem3798745 A B) (@lem3800131 A B)). Qed.
Lemma lem3800133 {A B : Type'} (n2 : nat) : term353 A B n2.
Proof. exact (@lem3800132 A B n2). Qed.
Lemma lem3800134 {A B : Type'} (n2 : nat) : (term353 A B n2) = (term235 A B n2).
Proof. exact (eq_refl (term353 A B n2)). Qed.
Lemma lem3800135 {A B : Type'} (n2 : nat) : term235 A B n2.
Proof. exact (EQ_MP (@lem3800134 A B n2) (@lem3800133 A B n2)). Qed.
Lemma lem3800136 {A B : Type'} (n2 : nat) (f : type1411 A B) : term354 A B n2 f.
Proof. exact (@lem3800135 A B n2 f). Qed.
Lemma lem3800137 {A B : Type'} (f : type1411 A B) (n2 : nat) : (term354 A B n2 f) = (term231 A B f n2).
Proof. exact (eq_refl (term354 A B n2 f)). Qed.
Lemma lem3800138 {A B : Type'} (f : type1411 A B) (n2 : nat) : term231 A B f n2.
Proof. exact (EQ_MP (@lem3800137 A B f n2) (@lem3800136 A B n2 f)). Qed.
Lemma lem3800139 {A B : Type'} (f : type1411 A B) (n2 : nat) (b : B) : term355 A B f n2 b.
Proof. exact (@lem3800138 A B f n2 b). Qed.
Lemma lem3800140 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : (term355 A B f n2 b) = (term190 A B b f n2).
Proof. exact (eq_refl (term355 A B f n2 b)). Qed.
Lemma lem3800141 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : term190 A B b f n2.
Proof. exact (EQ_MP (@lem3800140 A B b f n2) (@lem3800139 A B f n2 b)). Qed.
Lemma lem3800143 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : term190 A B b f n2.
Proof. exact (@lem3798380 A B b f n2 (@lem3800141 A B b f n2)). Qed.
Lemma lem3800144 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term189 A B b f n2) : term117 A.
Proof. exact (@lem3800143 A B b f n2 (@lem3798362 A B b f n2 h1)). Qed.
Lemma lem3800145 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term189 A B b f n2) : False.
Proof. exact (@lem3800144 A B b f n2 h1 (@lem3798363 A)). Qed.
Lemma lem3800146 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term189 A B b f n2) : (term189 A B b f n2) = False.
Proof. exact (prop_ext (fun h2 : term189 A B b f n2 => @lem3800145 A B b f n2 h1) (fun h2 : False => @lem3798362 A B b f n2 h1)). Qed.
Lemma lem3800147 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) (h1 : term189 A B b f n2) : False.
Proof. exact (EQ_MP (@lem3800146 A B b f n2 h1) (@lem3798362 A B b f n2 h1)). Qed.
Lemma lem3800148 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : term188 A B b f n2.
Proof. exact (fun h0 : term189 A B b f n2 => @lem3800147 A B b f n2 h0). Qed.
Lemma lem3800149 {A B : Type'} (b : B) (f : type1411 A B) (n2 : nat) : term187 A B b f n2.
Proof. exact (EQ_MP (@lem3798361 A B b f n2) (@lem3800148 A B b f n2)). Qed.
Lemma lem3800150 {A B : Type'} (f : type1411 A B) (b : B) (n2 : nat) : term46 A B f b n2.
Proof. exact (EQ_MP (@lem3798357 A B f b n2) (@lem3800149 A B b f n2)). Qed.
Lemma lem3800168 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term168 A B f b s a n) = (term169 A B b s n a f).
Proof. exact (EQ_MP (@lem3791025 A B b s n a f) (@lem3791024 A B b s n a f)). Qed.
Lemma lem3800169 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term168 A B f b s a n) = (term169 A B b s n a f).
Proof. exact (@lem3800168 A B b s n a f). Qed.
Lemma lem3800170 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term168 A B f b s a1 n1) = (term169 A B b s n1 a1 f).
Proof. exact (@lem3800169 A B b s n1 a1 f). Qed.
Lemma lem3800185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3800186 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term356 A B f b s a1 n1) = (term357 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3800185) (@lem3800170 A B b s n1 a1 f)). Qed.
Lemma lem3800188 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term85 A B f b s a) = (term86 A B s a b).
Proof. exact (EQ_MP (@lem3791010 A B f s a b) (@lem3791009 A B f s a b)). Qed.
Lemma lem3800189 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a : B) (b : B) : (term85 A B f b s a) = (term86 A B s a b).
Proof. exact (@lem3800188 A B f s a b). Qed.
Lemma lem3800190 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term85 A B f b s a2) = (term86 A B s a2 b).
Proof. exact (@lem3800189 A B f s a2 b). Qed.
Lemma lem3800197 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term358 A B a1 n1 f b s a2) = (term359 A B n1 a1 f s a2 b).
Proof. exact (MK_COMB (@lem3800186 A B b s n1 a1 f) (@lem3800190 A B f s a2 b)). Qed.
Lemma lem3800200 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3800201 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term360 A B a1 n1 f b s a2) = (term361 A B n1 a1 f s a2 b).
Proof. exact (MK_COMB (@lem3800200) (@lem3800197 A B n1 a1 f s a2 b)). Qed.
Lemma lem3800208 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) : (term362 B a1 a2 n1) = (term362 B a1 a2 n1).
Proof. exact (eq_refl (term362 B a1 a2 n1)). Qed.
Lemma lem3800209 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term363 A B f b s a1 a2 n1) = (term364 A B f s b a1 a2 n1).
Proof. exact (MK_COMB (@lem3800201 A B n1 a1 f s a2 b) (@lem3800208 B a1 a2 n1)). Qed.
Lemma lem3800212 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) : (term365 A B f b s a1 n1) = (term366 A B f s b a1 n1).
Proof. exact (fun_ext (fun a2 : B => @lem3800209 A B f s b a1 a2 n1)). Qed.
Lemma lem3800213 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3800214 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) : (term367 A B f b s a1 n1) = (term368 A B f s b a1 n1).
Proof. exact (MK_COMB (@lem3800213 B) (@lem3800212 A B f s b a1 n1)). Qed.
Lemma lem3800219 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) : (term369 A B f b s n1) = (term370 A B f s b n1).
Proof. exact (fun_ext (fun a1 : B => @lem3800214 A B f s b a1 n1)). Qed.
Lemma lem3800220 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3800221 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) : (term371 A B f b s n1) = (term372 A B f s b n1).
Proof. exact (MK_COMB (@lem3800220 B) (@lem3800219 A B f s b n1)). Qed.
Lemma lem3800226 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term373 A B f b n1) = (term374 A B f b n1).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3800221 A B f s b n1)). Qed.
Lemma lem3800227 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3800228 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term63 A B f b n1) = (term375 A B f b n1).
Proof. exact (MK_COMB (@lem3800227 A) (@lem3800226 A B f b n1)). Qed.
Lemma lem3800233 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term375 A B f b n1) = (term63 A B f b n1).
Proof. exact (SYM (@lem3800228 A B f b n1)). Qed.
Lemma lem3800235 (p : Prop) : p = (term109 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3800236 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term375 A B f b n1) = (term376 A B f b n1).
Proof. exact (@lem3800235 (term375 A B f b n1)). Qed.
Lemma lem3800237 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term376 A B f b n1) = (term375 A B f b n1).
Proof. exact (SYM (@lem3800236 A B f b n1)). Qed.
Lemma lem3800238 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term377 A B f b n1) : term377 A B f b n1.
Proof. exact (h1). Qed.
Lemma lem3800239 {A : Type'} : term112 A.
Proof. exact (@lem3204775 A). Qed.
Lemma lem3800243 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term378 A B f b n1) : term378 A B f b n1.
Proof. exact (h1). Qed.
Lemma lem3800244 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : term379 A B f b n1.
Proof. exact (fun h0 : term378 A B f b n1 => @lem3800243 A B f b n1 h0). Qed.
Lemma lem3800245 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term379 A B f b n1) : term379 A B f b n1.
Proof. exact (h1). Qed.
Lemma lem3800246 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term378 A B f b n1) : term378 A B f b n1.
Proof. exact (h1). Qed.
Lemma lem3800247 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term378 A B f b n1) (h2 : term379 A B f b n1) : term378 A B f b n1.
Proof. exact (@lem3800245 A B f b n1 h2 (@lem3800246 A B f b n1 h1)). Qed.
Lemma lem3800248 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term378 A B f b n1) : term380 A B f b n1.
Proof. exact (fun h0 : term379 A B f b n1 => @lem3800247 A B f b n1 h1 h0). Qed.
Lemma lem3800249 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term379 A B f b n1) : term379 A B f b n1.
Proof. exact (h1). Qed.
Lemma lem3800250 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term378 A B f b n1) (h2 : term379 A B f b n1) : term378 A B f b n1.
Proof. exact (@lem3800248 A B f b n1 h1 (@lem3800249 A B f b n1 h2)). Qed.
Lemma lem3800251 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term379 A B f b n1) : term379 A B f b n1.
Proof. exact (fun h0 : term378 A B f b n1 => @lem3800250 A B f b n1 h0 h1). Qed.
Lemma lem3800252 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : term381 A B f b n1.
Proof. exact (fun h0 : term379 A B f b n1 => @lem3800251 A B f b n1 h0). Qed.
Lemma lem3800255 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : term379 A B f b n1.
Proof. exact (@lem3800252 A B f b n1 (@lem3800244 A B f b n1)). Qed.
Lemma lem3800256 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : term379 A B f b n1.
Proof. exact (@lem3800255 A B f b n1). Qed.
Lemma lem3800292 {A : Type'} (P : Prop) (Q : A -> Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem3800293 {B : Type'} (P : Prop) (Q : B -> Prop) : (term194 B P Q) = (term195 B P Q).
Proof. exact (@lem3800292 B P Q). Qed.
Lemma lem3800294 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term196 A B b s n1 a1 f x) = (term197 A B b s n1 a1 f x).
Proof. exact (@lem3800293 B (@IN A x s) (term198 A B b s n1 a1 f x)). Qed.
Lemma lem3800295 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) : (term199 A B b s n1 a1 f x c) = (term200 A B b s n1 a1 f x c).
Proof. exact (eq_refl (term199 A B b s n1 a1 f x c)). Qed.
Lemma lem3800296 {A : Type'} (x : A) (s : A -> Prop) : (term201 A x s) = (term201 A x s).
Proof. exact (eq_refl (term201 A x s)). Qed.
Lemma lem3800297 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) : (term202 A B b s n1 a1 f x c) = (term203 A B b s n1 a1 f x c).
Proof. exact (MK_COMB (@lem3800296 A x s) (@lem3800295 A B b s n1 a1 f x c)). Qed.
Lemma lem3800298 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term204 A B b s n1 a1 f x) = (term205 A B b s n1 a1 f x).
Proof. exact (fun_ext (fun c : B => @lem3800297 A B b s n1 a1 f x c)). Qed.
Lemma lem3800299 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3800300 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term196 A B b s n1 a1 f x) = (term206 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3800299 B) (@lem3800298 A B b s n1 a1 f x)). Qed.
Lemma lem3800301 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3800302 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term207 A B b s n1 a1 f x) = (term208 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3800301) (@lem3800300 A B b s n1 a1 f x)). Qed.
Lemma lem3800303 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) : (term199 A B b s n1 a1 f x c) = (term200 A B b s n1 a1 f x c).
Proof. exact (eq_refl (term199 A B b s n1 a1 f x c)). Qed.
Lemma lem3800304 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term209 A B b s n1 a1 f x) = (term198 A B b s n1 a1 f x).
Proof. exact (fun_ext (fun c : B => @lem3800303 A B b s n1 a1 f x c)). Qed.
Lemma lem3800305 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3800306 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term210 A B b s n1 a1 f x) = (term211 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3800305 B) (@lem3800304 A B b s n1 a1 f x)). Qed.
Lemma lem3800307 {A : Type'} (x : A) (s : A -> Prop) : (term201 A x s) = (term201 A x s).
Proof. exact (eq_refl (term201 A x s)). Qed.
Lemma lem3800308 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term197 A B b s n1 a1 f x) = (term212 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3800307 A x s) (@lem3800306 A B b s n1 a1 f x)). Qed.
Lemma lem3800309 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : ((term196 A B b s n1 a1 f x) = (term197 A B b s n1 a1 f x)) = ((term206 A B b s n1 a1 f x) = (term212 A B b s n1 a1 f x)).
Proof. exact (MK_COMB (@lem3800302 A B b s n1 a1 f x) (@lem3800308 A B b s n1 a1 f x)). Qed.
Lemma lem3800310 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term206 A B b s n1 a1 f x) = (term212 A B b s n1 a1 f x).
Proof. exact (EQ_MP (@lem3800309 A B b s n1 a1 f x) (@lem3800294 A B b s n1 a1 f x)). Qed.
Lemma lem3800363 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term213 A B b s n1 a1 f) = (term214 A B b s n1 a1 f).
Proof. exact (fun_ext (fun x : A => @lem3800310 A B b s n1 a1 f x)). Qed.
Lemma lem3800364 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3800365 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term169 A B b s n1 a1 f) = (term215 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3800364 A) (@lem3800363 A B b s n1 a1 f)). Qed.
Lemma lem3800414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3800415 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term357 A B b s n1 a1 f) = (term382 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3800414) (@lem3800365 A B b s n1 a1 f)). Qed.
Lemma lem3800418 {A B : Type'} (s : A -> Prop) (a2 : B) (b : B) : (term86 A B s a2 b) = (term86 A B s a2 b).
Proof. exact (eq_refl (term86 A B s a2 b)). Qed.
Lemma lem3800419 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term359 A B n1 a1 f s a2 b) = (term383 A B n1 a1 f s a2 b).
Proof. exact (MK_COMB (@lem3800415 A B b s n1 a1 f) (@lem3800418 A B s a2 b)). Qed.
Lemma lem3800422 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3800423 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term361 A B n1 a1 f s a2 b) = (term384 A B n1 a1 f s a2 b).
Proof. exact (MK_COMB (@lem3800422) (@lem3800419 A B n1 a1 f s a2 b)). Qed.
Lemma lem3800426 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) : (term362 B a1 a2 n1) = (term362 B a1 a2 n1).
Proof. exact (eq_refl (term362 B a1 a2 n1)). Qed.
Lemma lem3800427 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term364 A B f s b a1 a2 n1) = (term385 A B f s b a1 a2 n1).
Proof. exact (MK_COMB (@lem3800423 A B n1 a1 f s a2 b) (@lem3800426 B a1 a2 n1)). Qed.
Lemma lem3800430 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) : (term366 A B f s b a1 n1) = (term386 A B f s b a1 n1).
Proof. exact (fun_ext (fun a2 : B => @lem3800427 A B f s b a1 a2 n1)). Qed.
Lemma lem3800431 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3800432 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) : (term368 A B f s b a1 n1) = (term387 A B f s b a1 n1).
Proof. exact (MK_COMB (@lem3800431 B) (@lem3800430 A B f s b a1 n1)). Qed.
Lemma lem3800437 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) : (term370 A B f s b n1) = (term388 A B f s b n1).
Proof. exact (fun_ext (fun a1 : B => @lem3800432 A B f s b a1 n1)). Qed.
Lemma lem3800438 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3800439 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) : (term372 A B f s b n1) = (term389 A B f s b n1).
Proof. exact (MK_COMB (@lem3800438 B) (@lem3800437 A B f s b n1)). Qed.
Lemma lem3800444 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term374 A B f b n1) = (term390 A B f b n1).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3800439 A B f s b n1)). Qed.
Lemma lem3800445 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3800446 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term375 A B f b n1) = (term391 A B f b n1).
Proof. exact (MK_COMB (@lem3800445 A) (@lem3800444 A B f b n1)). Qed.
Lemma lem3800451 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3800452 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term377 A B f b n1) = (term392 A B f b n1).
Proof. exact (MK_COMB (@lem3800451) (@lem3800446 A B f b n1)). Qed.
Lemma lem3800453 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3800454 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term393 A B f b n1) = (term394 A B f b n1).
Proof. exact (MK_COMB (@lem3800453) (@lem3800452 A B f b n1)). Qed.
Lemma lem3800456 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3800457 {A : Type'} : (term117 A) = (term118 A).
Proof. exact (@lem3800456 (term112 A)). Qed.
Lemma lem3800462 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term378 A B f b n1) = (term395 A B f b n1).
Proof. exact (MK_COMB (@lem3800454 A B f b n1) (@lem3800457 A)). Qed.
Lemma lem3800465 {A B : Type'} (b : B) (n1 : nat) : (term396 A B b n1) = (term397 A B b n1).
Proof. exact (fun_ext (fun f : type1411 A B => @lem3800462 A B f b n1)). Qed.
Lemma lem3800466 {A B : Type'} : (@all (A -> B -> B)) = (@all (A -> B -> B)).
Proof. exact (eq_refl (@all (A -> B -> B))). Qed.
Lemma lem3800467 {A B : Type'} (b : B) (n1 : nat) : (term398 A B b n1) = (term399 A B b n1).
Proof. exact (MK_COMB (@lem3800466 A B) (@lem3800465 A B b n1)). Qed.
Lemma lem3800472 {A B : Type'} (n1 : nat) : (term400 A B n1) = (term401 A B n1).
Proof. exact (fun_ext (fun b : B => @lem3800467 A B b n1)). Qed.
Lemma lem3800473 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3800474 {A B : Type'} (n1 : nat) : (term402 A B n1) = (term403 A B n1).
Proof. exact (MK_COMB (@lem3800473 B) (@lem3800472 A B n1)). Qed.
Lemma lem3800479 {A B : Type'} : (term404 A B) = (term405 A B).
Proof. exact (fun_ext (fun n1 : nat => @lem3800474 A B n1)). Qed.
Lemma lem3800480 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3800489 {A B : Type'} : (term406 A B) = (term407 A B).
Proof. exact (MK_COMB (@lem3800480) (@lem3800479 A B)). Qed.
Lemma lem3800492 {A : Type'} (x : A) : (term125 A x) = (term125 A x).
Proof. exact (eq_refl (term125 A x)). Qed.
Lemma lem3800493 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (fun_ext (fun x : A => @lem3800492 A x)). Qed.
Lemma lem3800494 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3800495 {A : Type'} : (term112 A) = (term112 A).
Proof. exact (MK_COMB (@lem3800494 A) (@lem3800493 A)). Qed.
Lemma lem3800496 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3800497 {A : Type'} : (term118 A) = (term118 A).
Proof. exact (MK_COMB (@lem3800496) (@lem3800495 A)). Qed.
Lemma lem3800502 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) : (term362 B a1 a2 n1) = (term362 B a1 a2 n1).
Proof. exact (eq_refl (term362 B a1 a2 n1)). Qed.
Lemma lem3800507 {A B : Type'} (s : A -> Prop) (a2 : B) (b : B) : (term86 A B s a2 b) = (term86 A B s a2 b).
Proof. exact (eq_refl (term86 A B s a2 b)). Qed.
Lemma lem3800512 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) : (term200 A B b s n1 a1 f x c) = (term200 A B b s n1 a1 f x c).
Proof. exact (eq_refl (term200 A B b s n1 a1 f x c)). Qed.
Lemma lem3800513 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term198 A B b s n1 a1 f x) = (term198 A B b s n1 a1 f x).
Proof. exact (fun_ext (fun c : B => @lem3800512 A B b s n1 a1 f x c)). Qed.
Lemma lem3800514 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3800515 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term211 A B b s n1 a1 f x) = (term211 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3800514 B) (@lem3800513 A B b s n1 a1 f x)). Qed.
Lemma lem3800518 {A : Type'} (x : A) (s : A -> Prop) : (term201 A x s) = (term201 A x s).
Proof. exact (eq_refl (term201 A x s)). Qed.
Lemma lem3800519 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term212 A B b s n1 a1 f x) = (term212 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3800518 A x s) (@lem3800515 A B b s n1 a1 f x)). Qed.
Lemma lem3800520 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term214 A B b s n1 a1 f) = (term214 A B b s n1 a1 f).
Proof. exact (fun_ext (fun x : A => @lem3800519 A B b s n1 a1 f x)). Qed.
Lemma lem3800521 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3800522 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term215 A B b s n1 a1 f) = (term215 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3800521 A) (@lem3800520 A B b s n1 a1 f)). Qed.
Lemma lem3800523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3800524 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term382 A B b s n1 a1 f) = (term382 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3800523) (@lem3800522 A B b s n1 a1 f)). Qed.
Lemma lem3800525 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term383 A B n1 a1 f s a2 b) = (term383 A B n1 a1 f s a2 b).
Proof. exact (MK_COMB (@lem3800524 A B b s n1 a1 f) (@lem3800507 A B s a2 b)). Qed.
Lemma lem3800526 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3800527 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term384 A B n1 a1 f s a2 b) = (term384 A B n1 a1 f s a2 b).
Proof. exact (MK_COMB (@lem3800526) (@lem3800525 A B n1 a1 f s a2 b)). Qed.
Lemma lem3800528 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term385 A B f s b a1 a2 n1) = (term385 A B f s b a1 a2 n1).
Proof. exact (MK_COMB (@lem3800527 A B n1 a1 f s a2 b) (@lem3800502 B a1 a2 n1)). Qed.
Lemma lem3800529 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) : (term386 A B f s b a1 n1) = (term386 A B f s b a1 n1).
Proof. exact (fun_ext (fun a2 : B => @lem3800528 A B f s b a1 a2 n1)). Qed.
Lemma lem3800530 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3800531 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) : (term387 A B f s b a1 n1) = (term387 A B f s b a1 n1).
Proof. exact (MK_COMB (@lem3800530 B) (@lem3800529 A B f s b a1 n1)). Qed.
Lemma lem3800532 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) : (term388 A B f s b n1) = (term388 A B f s b n1).
Proof. exact (fun_ext (fun a1 : B => @lem3800531 A B f s b a1 n1)). Qed.
Lemma lem3800533 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3800534 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) : (term389 A B f s b n1) = (term389 A B f s b n1).
Proof. exact (MK_COMB (@lem3800533 B) (@lem3800532 A B f s b n1)). Qed.
Lemma lem3800535 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term390 A B f b n1) = (term390 A B f b n1).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3800534 A B f s b n1)). Qed.
Lemma lem3800536 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3800537 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term391 A B f b n1) = (term391 A B f b n1).
Proof. exact (MK_COMB (@lem3800536 A) (@lem3800535 A B f b n1)). Qed.
Lemma lem3800538 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3800539 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term392 A B f b n1) = (term392 A B f b n1).
Proof. exact (MK_COMB (@lem3800538) (@lem3800537 A B f b n1)). Qed.
Lemma lem3800540 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3800541 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term394 A B f b n1) = (term394 A B f b n1).
Proof. exact (MK_COMB (@lem3800540) (@lem3800539 A B f b n1)). Qed.
Lemma lem3800542 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term395 A B f b n1) = (term395 A B f b n1).
Proof. exact (MK_COMB (@lem3800541 A B f b n1) (@lem3800497 A)). Qed.
Lemma lem3800543 {A B : Type'} (b : B) (n1 : nat) : (term397 A B b n1) = (term397 A B b n1).
Proof. exact (fun_ext (fun f : type1411 A B => @lem3800542 A B f b n1)). Qed.
Lemma lem3800544 {A B : Type'} : (@all (A -> B -> B)) = (@all (A -> B -> B)).
Proof. exact (eq_refl (@all (A -> B -> B))). Qed.
Lemma lem3800545 {A B : Type'} (b : B) (n1 : nat) : (term399 A B b n1) = (term399 A B b n1).
Proof. exact (MK_COMB (@lem3800544 A B) (@lem3800543 A B b n1)). Qed.
Lemma lem3800546 {A B : Type'} (n1 : nat) : (term401 A B n1) = (term401 A B n1).
Proof. exact (fun_ext (fun b : B => @lem3800545 A B b n1)). Qed.
Lemma lem3800547 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3800548 {A B : Type'} (n1 : nat) : (term403 A B n1) = (term403 A B n1).
Proof. exact (MK_COMB (@lem3800547 B) (@lem3800546 A B n1)). Qed.
Lemma lem3800549 {A B : Type'} : (term405 A B) = (term405 A B).
Proof. exact (fun_ext (fun n1 : nat => @lem3800548 A B n1)). Qed.
Lemma lem3800550 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3800551 {A B : Type'} : (term407 A B) = (term407 A B).
Proof. exact (MK_COMB (@lem3800550) (@lem3800549 A B)). Qed.
Lemma lem3800622 {A B : Type'} : (term406 A B) = (term407 A B).
Proof. exact (TRANS (@lem3800489 A B) (@lem3800551 A B)). Qed.
Lemma lem3800623 {A B : Type'} : (term407 A B) = (term406 A B).
Proof. exact (SYM (@lem3800622 A B)). Qed.
Lemma lem3800624 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term392 A B f b n1) : term392 A B f b n1.
Proof. exact (h1). Qed.
Lemma lem3800625 {A : Type'} (h1 : term112 A) : term112 A.
Proof. exact (h1). Qed.
Lemma lem3800631 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) : (term200 A B b s n1 a1 f x c) = (term200 A B b s n1 a1 f x c).
Proof. exact (eq_refl (term200 A B b s n1 a1 f x c)). Qed.
Lemma lem3800632 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term198 A B b s n1 a1 f x) = (term198 A B b s n1 a1 f x).
Proof. exact (fun_ext (fun c : B => @lem3800631 A B b s n1 a1 f x c)). Qed.
Lemma lem3800633 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3800634 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term211 A B b s n1 a1 f x) = (term211 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3800633 B) (@lem3800632 A B b s n1 a1 f x)). Qed.
Lemma lem3800636 {A : Type'} (x : A) (s : A -> Prop) : (term201 A x s) = (term201 A x s).
Proof. exact (eq_refl (term201 A x s)). Qed.
Lemma lem3800637 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term212 A B b s n1 a1 f x) = (term212 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3800636 A x s) (@lem3800634 A B b s n1 a1 f x)). Qed.
Lemma lem3800638 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term214 A B b s n1 a1 f) = (term214 A B b s n1 a1 f).
Proof. exact (fun_ext (fun x : A => @lem3800637 A B b s n1 a1 f x)). Qed.
Lemma lem3800639 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3800640 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term215 A B b s n1 a1 f) = (term215 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3800639 A) (@lem3800638 A B b s n1 a1 f)). Qed.
Lemma lem3800645 {A B : Type'} (s : A -> Prop) (a2 : B) (b : B) : (term86 A B s a2 b) = (term86 A B s a2 b).
Proof. exact (eq_refl (term86 A B s a2 b)). Qed.
Lemma lem3800646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3800647 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term382 A B b s n1 a1 f) = (term382 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3800646) (@lem3800640 A B b s n1 a1 f)). Qed.
Lemma lem3800648 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term383 A B n1 a1 f s a2 b) = (term383 A B n1 a1 f s a2 b).
Proof. exact (MK_COMB (@lem3800647 A B b s n1 a1 f) (@lem3800645 A B s a2 b)). Qed.
Lemma lem3800655 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) : (term408 B a1 a2 n1) = (term409 B a1 a2 n1).
Proof. exact (@lem17045 (a1 = a2) ((S n1) = (NUMERAL 0))). Qed.
Lemma lem3800656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3800657 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term410 A B n1 a1 f s a2 b) = (term410 A B n1 a1 f s a2 b).
Proof. exact (MK_COMB (@lem3800656) (@lem3800648 A B n1 a1 f s a2 b)). Qed.
Lemma lem3800658 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term411 A B f s b a1 a2 n1) = (term412 A B f s b a1 a2 n1).
Proof. exact (MK_COMB (@lem3800657 A B n1 a1 f s a2 b) (@lem3800655 B a1 a2 n1)). Qed.
Lemma lem3800659 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term413 A B f s b a1 a2 n1) = (term411 A B f s b a1 a2 n1).
Proof. exact (@lem17362 (term383 A B n1 a1 f s a2 b) (term362 B a1 a2 n1)). Qed.
Lemma lem3800660 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term413 A B f s b a1 a2 n1) = (term412 A B f s b a1 a2 n1).
Proof. exact (TRANS (@lem3800659 A B f s b a1 a2 n1) (@lem3800658 A B f s b a1 a2 n1)). Qed.
Lemma lem3800661 {B : Type'} (P : B -> Prop) : (term129 B P) = (term130 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem3800662 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) : (term414 A B f s b a1 n1) = (term415 A B f s b a1 n1).
Proof. exact (@lem3800661 B (term386 A B f s b a1 n1)). Qed.
Lemma lem3800663 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term416 A B f s b a1 n1 a2) = (term385 A B f s b a1 a2 n1).
Proof. exact (eq_refl (term416 A B f s b a1 n1 a2)). Qed.
Lemma lem3800664 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3800665 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term417 A B f s b a1 n1 a2) = (term413 A B f s b a1 a2 n1).
Proof. exact (MK_COMB (@lem3800664) (@lem3800663 A B f s b a1 a2 n1)). Qed.
Lemma lem3800666 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term417 A B f s b a1 n1 a2) = (term412 A B f s b a1 a2 n1).
Proof. exact (TRANS (@lem3800665 A B f s b a1 a2 n1) (@lem3800660 A B f s b a1 a2 n1)). Qed.
Lemma lem3800667 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) : (term418 A B f s b a1 n1) = (term419 A B f s b a1 n1).
Proof. exact (fun_ext (fun a2 : B => @lem3800666 A B f s b a1 a2 n1)). Qed.
Lemma lem3800668 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3800669 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) : (term415 A B f s b a1 n1) = (term420 A B f s b a1 n1).
Proof. exact (MK_COMB (@lem3800668 B) (@lem3800667 A B f s b a1 n1)). Qed.
Lemma lem3800670 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) : (term414 A B f s b a1 n1) = (term420 A B f s b a1 n1).
Proof. exact (TRANS (@lem3800662 A B f s b a1 n1) (@lem3800669 A B f s b a1 n1)). Qed.
Lemma lem3800671 {B : Type'} (P : B -> Prop) : (term129 B P) = (term130 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem3800672 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) : (term421 A B f s b n1) = (term422 A B f s b n1).
Proof. exact (@lem3800671 B (term388 A B f s b n1)). Qed.
Lemma lem3800673 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) : (term423 A B f s b n1 a1) = (term387 A B f s b a1 n1).
Proof. exact (eq_refl (term423 A B f s b n1 a1)). Qed.
Lemma lem3800674 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3800675 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) : (term424 A B f s b n1 a1) = (term414 A B f s b a1 n1).
Proof. exact (MK_COMB (@lem3800674) (@lem3800673 A B f s b a1 n1)). Qed.
Lemma lem3800676 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) : (term424 A B f s b n1 a1) = (term420 A B f s b a1 n1).
Proof. exact (TRANS (@lem3800675 A B f s b a1 n1) (@lem3800670 A B f s b a1 n1)). Qed.
Lemma lem3800677 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) : (term425 A B f s b n1) = (term426 A B f s b n1).
Proof. exact (fun_ext (fun a1 : B => @lem3800676 A B f s b a1 n1)). Qed.
Lemma lem3800678 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3800679 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) : (term422 A B f s b n1) = (term427 A B f s b n1).
Proof. exact (MK_COMB (@lem3800678 B) (@lem3800677 A B f s b n1)). Qed.
Lemma lem3800680 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) : (term421 A B f s b n1) = (term427 A B f s b n1).
Proof. exact (TRANS (@lem3800672 A B f s b n1) (@lem3800679 A B f s b n1)). Qed.
Lemma lem3800681 {A : Type'} (P : type686 A) : (term145 A P) = (term146 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3800682 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term392 A B f b n1) = (term428 A B f b n1).
Proof. exact (@lem3800681 A (term390 A B f b n1)). Qed.
Lemma lem3800683 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) : (term429 A B f b n1 s) = (term389 A B f s b n1).
Proof. exact (eq_refl (term429 A B f b n1 s)). Qed.
Lemma lem3800684 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3800685 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) : (term430 A B f b n1 s) = (term421 A B f s b n1).
Proof. exact (MK_COMB (@lem3800684) (@lem3800683 A B f s b n1)). Qed.
Lemma lem3800686 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) : (term430 A B f b n1 s) = (term427 A B f s b n1).
Proof. exact (TRANS (@lem3800685 A B f s b n1) (@lem3800680 A B f s b n1)). Qed.
Lemma lem3800687 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term431 A B f b n1) = (term432 A B f b n1).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3800686 A B f s b n1)). Qed.
Lemma lem3800688 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3800689 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term428 A B f b n1) = (term433 A B f b n1).
Proof. exact (MK_COMB (@lem3800688 A) (@lem3800687 A B f b n1)). Qed.
Lemma lem3800690 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term392 A B f b n1) = (term433 A B f b n1).
Proof. exact (TRANS (@lem3800682 A B f b n1) (@lem3800689 A B f b n1)). Qed.
Lemma lem3800845 {A : Type'} (P : Prop) (Q : A -> Prop) : (term195 A P Q) = (term194 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3800846 {B : Type'} (P : Prop) (Q : B -> Prop) : (term195 B P Q) = (term194 B P Q).
Proof. exact (@lem3800845 B P Q). Qed.
Lemma lem3800847 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term197 A B b s n1 a1 f x) = (term196 A B b s n1 a1 f x).
Proof. exact (@lem3800846 B (@IN A x s) (term198 A B b s n1 a1 f x)). Qed.
Lemma lem3800848 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) : (term199 A B b s n1 a1 f x c) = (term200 A B b s n1 a1 f x c).
Proof. exact (eq_refl (term199 A B b s n1 a1 f x c)). Qed.
Lemma lem3800849 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term209 A B b s n1 a1 f x) = (term198 A B b s n1 a1 f x).
Proof. exact (fun_ext (fun c : B => @lem3800848 A B b s n1 a1 f x c)). Qed.
Lemma lem3800850 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3800851 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term210 A B b s n1 a1 f x) = (term211 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3800850 B) (@lem3800849 A B b s n1 a1 f x)). Qed.
Lemma lem3800852 {A : Type'} (x : A) (s : A -> Prop) : (term201 A x s) = (term201 A x s).
Proof. exact (eq_refl (term201 A x s)). Qed.
Lemma lem3800853 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term197 A B b s n1 a1 f x) = (term212 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3800852 A x s) (@lem3800851 A B b s n1 a1 f x)). Qed.
Lemma lem3800854 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3800855 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term267 A B b s n1 a1 f x) = (term268 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3800854) (@lem3800853 A B b s n1 a1 f x)). Qed.
Lemma lem3800856 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) : (term199 A B b s n1 a1 f x c) = (term200 A B b s n1 a1 f x c).
Proof. exact (eq_refl (term199 A B b s n1 a1 f x c)). Qed.
Lemma lem3800857 {A : Type'} (x : A) (s : A -> Prop) : (term201 A x s) = (term201 A x s).
Proof. exact (eq_refl (term201 A x s)). Qed.
Lemma lem3800858 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) : (term202 A B b s n1 a1 f x c) = (term203 A B b s n1 a1 f x c).
Proof. exact (MK_COMB (@lem3800857 A x s) (@lem3800856 A B b s n1 a1 f x c)). Qed.
Lemma lem3800859 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term204 A B b s n1 a1 f x) = (term205 A B b s n1 a1 f x).
Proof. exact (fun_ext (fun c : B => @lem3800858 A B b s n1 a1 f x c)). Qed.
Lemma lem3800860 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3800861 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term196 A B b s n1 a1 f x) = (term206 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3800860 B) (@lem3800859 A B b s n1 a1 f x)). Qed.
Lemma lem3800862 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : ((term197 A B b s n1 a1 f x) = (term196 A B b s n1 a1 f x)) = ((term212 A B b s n1 a1 f x) = (term206 A B b s n1 a1 f x)).
Proof. exact (MK_COMB (@lem3800855 A B b s n1 a1 f x) (@lem3800861 A B b s n1 a1 f x)). Qed.
Lemma lem3800863 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term212 A B b s n1 a1 f x) = (term206 A B b s n1 a1 f x).
Proof. exact (EQ_MP (@lem3800862 A B b s n1 a1 f x) (@lem3800847 A B b s n1 a1 f x)). Qed.
Lemma lem3800864 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term214 A B b s n1 a1 f) = (term213 A B b s n1 a1 f).
Proof. exact (fun_ext (fun x : A => @lem3800863 A B b s n1 a1 f x)). Qed.
Lemma lem3800865 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3800866 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term215 A B b s n1 a1 f) = (term169 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3800865 A) (@lem3800864 A B b s n1 a1 f)). Qed.
Lemma lem3800867 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3800868 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term382 A B b s n1 a1 f) = (term357 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3800867) (@lem3800866 A B b s n1 a1 f)). Qed.
Lemma lem3800869 {A B : Type'} (s : A -> Prop) (a2 : B) (b : B) : (term86 A B s a2 b) = (term86 A B s a2 b).
Proof. exact (eq_refl (term86 A B s a2 b)). Qed.
Lemma lem3800870 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term383 A B n1 a1 f s a2 b) = (term359 A B n1 a1 f s a2 b).
Proof. exact (MK_COMB (@lem3800868 A B b s n1 a1 f) (@lem3800869 A B s a2 b)). Qed.
Lemma lem3800872 {A : Type'} (P : A -> Prop) (Q : Prop) : (term297 A P Q) = (term298 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3800873 {A : Type'} (P : A -> Prop) (Q : Prop) : (term297 A P Q) = (term298 A P Q).
Proof. exact (@lem3800872 A P Q). Qed.
Lemma lem3800874 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term434 A B n1 a1 f s a2 b) = (term435 A B n1 a1 f s a2 b).
Proof. exact (@lem3800873 A (term213 A B b s n1 a1 f) (term86 A B s a2 b)). Qed.
Lemma lem3800875 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term271 A B b s n1 a1 f x) = (term206 A B b s n1 a1 f x).
Proof. exact (eq_refl (term271 A B b s n1 a1 f x)). Qed.
Lemma lem3800876 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term272 A B b s n1 a1 f) = (term213 A B b s n1 a1 f).
Proof. exact (fun_ext (fun x : A => @lem3800875 A B b s n1 a1 f x)). Qed.
Lemma lem3800877 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3800878 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term273 A B b s n1 a1 f) = (term169 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3800877 A) (@lem3800876 A B b s n1 a1 f)). Qed.
Lemma lem3800879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3800880 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term436 A B b s n1 a1 f) = (term357 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3800879) (@lem3800878 A B b s n1 a1 f)). Qed.
Lemma lem3800881 {A B : Type'} (s : A -> Prop) (a2 : B) (b : B) : (term86 A B s a2 b) = (term86 A B s a2 b).
Proof. exact (eq_refl (term86 A B s a2 b)). Qed.
Lemma lem3800882 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term434 A B n1 a1 f s a2 b) = (term359 A B n1 a1 f s a2 b).
Proof. exact (MK_COMB (@lem3800880 A B b s n1 a1 f) (@lem3800881 A B s a2 b)). Qed.
Lemma lem3800883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3800884 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term437 A B n1 a1 f s a2 b) = (term438 A B n1 a1 f s a2 b).
Proof. exact (MK_COMB (@lem3800883) (@lem3800882 A B n1 a1 f s a2 b)). Qed.
Lemma lem3800885 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term271 A B b s n1 a1 f x) = (term206 A B b s n1 a1 f x).
Proof. exact (eq_refl (term271 A B b s n1 a1 f x)). Qed.
Lemma lem3800886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3800887 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term439 A B b s n1 a1 f x) = (term440 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3800886) (@lem3800885 A B b s n1 a1 f x)). Qed.
Lemma lem3800888 {A B : Type'} (s : A -> Prop) (a2 : B) (b : B) : (term86 A B s a2 b) = (term86 A B s a2 b).
Proof. exact (eq_refl (term86 A B s a2 b)). Qed.
Lemma lem3800889 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (s : A -> Prop) (a2 : B) (b : B) : (term441 A B n1 a1 f x s a2 b) = (term442 A B n1 a1 f x s a2 b).
Proof. exact (MK_COMB (@lem3800887 A B b s n1 a1 f x) (@lem3800888 A B s a2 b)). Qed.
Lemma lem3800890 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term443 A B n1 a1 f s a2 b) = (term444 A B n1 a1 f s a2 b).
Proof. exact (fun_ext (fun x : A => @lem3800889 A B n1 a1 f x s a2 b)). Qed.
Lemma lem3800891 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3800892 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term435 A B n1 a1 f s a2 b) = (term445 A B n1 a1 f s a2 b).
Proof. exact (MK_COMB (@lem3800891 A) (@lem3800890 A B n1 a1 f s a2 b)). Qed.
Lemma lem3800893 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : ((term434 A B n1 a1 f s a2 b) = (term435 A B n1 a1 f s a2 b)) = ((term359 A B n1 a1 f s a2 b) = (term445 A B n1 a1 f s a2 b)).
Proof. exact (MK_COMB (@lem3800884 A B n1 a1 f s a2 b) (@lem3800892 A B n1 a1 f s a2 b)). Qed.
Lemma lem3800894 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term359 A B n1 a1 f s a2 b) = (term445 A B n1 a1 f s a2 b).
Proof. exact (EQ_MP (@lem3800893 A B n1 a1 f s a2 b) (@lem3800874 A B n1 a1 f s a2 b)). Qed.
Lemma lem3800896 {A : Type'} (P : A -> Prop) (Q : Prop) : (term297 A P Q) = (term298 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3800897 {B : Type'} (P : B -> Prop) (Q : Prop) : (term297 B P Q) = (term298 B P Q).
Proof. exact (@lem3800896 B P Q). Qed.
Lemma lem3800898 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (s : A -> Prop) (a2 : B) (b : B) : (term446 A B n1 a1 f x s a2 b) = (term447 A B n1 a1 f x s a2 b).
Proof. exact (@lem3800897 B (term205 A B b s n1 a1 f x) (term86 A B s a2 b)). Qed.
Lemma lem3800899 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) : (term283 A B b s n1 a1 f x c) = (term203 A B b s n1 a1 f x c).
Proof. exact (eq_refl (term283 A B b s n1 a1 f x c)). Qed.
Lemma lem3800900 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term284 A B b s n1 a1 f x) = (term205 A B b s n1 a1 f x).
Proof. exact (fun_ext (fun c : B => @lem3800899 A B b s n1 a1 f x c)). Qed.
Lemma lem3800901 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3800902 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term285 A B b s n1 a1 f x) = (term206 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3800901 B) (@lem3800900 A B b s n1 a1 f x)). Qed.
Lemma lem3800903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3800904 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term448 A B b s n1 a1 f x) = (term440 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3800903) (@lem3800902 A B b s n1 a1 f x)). Qed.
Lemma lem3800905 {A B : Type'} (s : A -> Prop) (a2 : B) (b : B) : (term86 A B s a2 b) = (term86 A B s a2 b).
Proof. exact (eq_refl (term86 A B s a2 b)). Qed.
Lemma lem3800906 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (s : A -> Prop) (a2 : B) (b : B) : (term446 A B n1 a1 f x s a2 b) = (term442 A B n1 a1 f x s a2 b).
Proof. exact (MK_COMB (@lem3800904 A B b s n1 a1 f x) (@lem3800905 A B s a2 b)). Qed.
Lemma lem3800907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3800908 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (s : A -> Prop) (a2 : B) (b : B) : (term449 A B n1 a1 f x s a2 b) = (term450 A B n1 a1 f x s a2 b).
Proof. exact (MK_COMB (@lem3800907) (@lem3800906 A B n1 a1 f x s a2 b)). Qed.
Lemma lem3800909 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) : (term283 A B b s n1 a1 f x c) = (term203 A B b s n1 a1 f x c).
Proof. exact (eq_refl (term283 A B b s n1 a1 f x c)). Qed.
Lemma lem3800910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3800911 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) : (term451 A B b s n1 a1 f x c) = (term452 A B b s n1 a1 f x c).
Proof. exact (MK_COMB (@lem3800910) (@lem3800909 A B b s n1 a1 f x c)). Qed.
Lemma lem3800912 {A B : Type'} (s : A -> Prop) (a2 : B) (b : B) : (term86 A B s a2 b) = (term86 A B s a2 b).
Proof. exact (eq_refl (term86 A B s a2 b)). Qed.
Lemma lem3800913 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (a2 : B) (b : B) : (term453 A B n1 a1 f x c s a2 b) = (term454 A B n1 a1 f x c s a2 b).
Proof. exact (MK_COMB (@lem3800911 A B b s n1 a1 f x c) (@lem3800912 A B s a2 b)). Qed.
Lemma lem3800914 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (s : A -> Prop) (a2 : B) (b : B) : (term455 A B n1 a1 f x s a2 b) = (term456 A B n1 a1 f x s a2 b).
Proof. exact (fun_ext (fun c : B => @lem3800913 A B n1 a1 f x c s a2 b)). Qed.
Lemma lem3800915 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3800916 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (s : A -> Prop) (a2 : B) (b : B) : (term447 A B n1 a1 f x s a2 b) = (term457 A B n1 a1 f x s a2 b).
Proof. exact (MK_COMB (@lem3800915 B) (@lem3800914 A B n1 a1 f x s a2 b)). Qed.
Lemma lem3800917 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (s : A -> Prop) (a2 : B) (b : B) : ((term446 A B n1 a1 f x s a2 b) = (term447 A B n1 a1 f x s a2 b)) = ((term442 A B n1 a1 f x s a2 b) = (term457 A B n1 a1 f x s a2 b)).
Proof. exact (MK_COMB (@lem3800908 A B n1 a1 f x s a2 b) (@lem3800916 A B n1 a1 f x s a2 b)). Qed.
Lemma lem3800918 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (s : A -> Prop) (a2 : B) (b : B) : (term442 A B n1 a1 f x s a2 b) = (term457 A B n1 a1 f x s a2 b).
Proof. exact (EQ_MP (@lem3800917 A B n1 a1 f x s a2 b) (@lem3800898 A B n1 a1 f x s a2 b)). Qed.
Lemma lem3800919 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term444 A B n1 a1 f s a2 b) = (term458 A B n1 a1 f s a2 b).
Proof. exact (fun_ext (fun x : A => @lem3800918 A B n1 a1 f x s a2 b)). Qed.
Lemma lem3800920 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3800921 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term445 A B n1 a1 f s a2 b) = (term459 A B n1 a1 f s a2 b).
Proof. exact (MK_COMB (@lem3800920 A) (@lem3800919 A B n1 a1 f s a2 b)). Qed.
Lemma lem3800922 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term359 A B n1 a1 f s a2 b) = (term459 A B n1 a1 f s a2 b).
Proof. exact (TRANS (@lem3800894 A B n1 a1 f s a2 b) (@lem3800921 A B n1 a1 f s a2 b)). Qed.
Lemma lem3800923 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term383 A B n1 a1 f s a2 b) = (term459 A B n1 a1 f s a2 b).
Proof. exact (TRANS (@lem3800870 A B n1 a1 f s a2 b) (@lem3800922 A B n1 a1 f s a2 b)). Qed.
Lemma lem3800924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3800925 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term410 A B n1 a1 f s a2 b) = (term460 A B n1 a1 f s a2 b).
Proof. exact (MK_COMB (@lem3800924) (@lem3800923 A B n1 a1 f s a2 b)). Qed.
Lemma lem3800926 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) : (term409 B a1 a2 n1) = (term409 B a1 a2 n1).
Proof. exact (eq_refl (term409 B a1 a2 n1)). Qed.
Lemma lem3800927 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term412 A B f s b a1 a2 n1) = (term461 A B f s b a1 a2 n1).
Proof. exact (MK_COMB (@lem3800925 A B n1 a1 f s a2 b) (@lem3800926 B a1 a2 n1)). Qed.
Lemma lem3800929 {A : Type'} (P : A -> Prop) (Q : Prop) : (term297 A P Q) = (term298 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3800930 {A : Type'} (P : A -> Prop) (Q : Prop) : (term297 A P Q) = (term298 A P Q).
Proof. exact (@lem3800929 A P Q). Qed.
Lemma lem3800931 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term462 A B f s b a1 a2 n1) = (term463 A B f s b a1 a2 n1).
Proof. exact (@lem3800930 A (term458 A B n1 a1 f s a2 b) (term409 B a1 a2 n1)). Qed.
Lemma lem3800932 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (s : A -> Prop) (a2 : B) (b : B) : (term464 A B n1 a1 f s a2 b x) = (term457 A B n1 a1 f x s a2 b).
Proof. exact (eq_refl (term464 A B n1 a1 f s a2 b x)). Qed.
Lemma lem3800933 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term465 A B n1 a1 f s a2 b) = (term458 A B n1 a1 f s a2 b).
Proof. exact (fun_ext (fun x : A => @lem3800932 A B n1 a1 f x s a2 b)). Qed.
Lemma lem3800934 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3800935 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term466 A B n1 a1 f s a2 b) = (term459 A B n1 a1 f s a2 b).
Proof. exact (MK_COMB (@lem3800934 A) (@lem3800933 A B n1 a1 f s a2 b)). Qed.
Lemma lem3800936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3800937 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (s : A -> Prop) (a2 : B) (b : B) : (term467 A B n1 a1 f s a2 b) = (term460 A B n1 a1 f s a2 b).
Proof. exact (MK_COMB (@lem3800936) (@lem3800935 A B n1 a1 f s a2 b)). Qed.
Lemma lem3800938 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) : (term409 B a1 a2 n1) = (term409 B a1 a2 n1).
Proof. exact (eq_refl (term409 B a1 a2 n1)). Qed.
Lemma lem3800939 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term462 A B f s b a1 a2 n1) = (term461 A B f s b a1 a2 n1).
Proof. exact (MK_COMB (@lem3800937 A B n1 a1 f s a2 b) (@lem3800938 B a1 a2 n1)). Qed.
Lemma lem3800940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3800941 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term468 A B f s b a1 a2 n1) = (term469 A B f s b a1 a2 n1).
Proof. exact (MK_COMB (@lem3800940) (@lem3800939 A B f s b a1 a2 n1)). Qed.
Lemma lem3800942 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (s : A -> Prop) (a2 : B) (b : B) : (term464 A B n1 a1 f s a2 b x) = (term457 A B n1 a1 f x s a2 b).
Proof. exact (eq_refl (term464 A B n1 a1 f s a2 b x)). Qed.
Lemma lem3800943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3800944 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (s : A -> Prop) (a2 : B) (b : B) : (term470 A B n1 a1 f s a2 b x) = (term471 A B n1 a1 f x s a2 b).
Proof. exact (MK_COMB (@lem3800943) (@lem3800942 A B n1 a1 f x s a2 b)). Qed.
Lemma lem3800945 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) : (term409 B a1 a2 n1) = (term409 B a1 a2 n1).
Proof. exact (eq_refl (term409 B a1 a2 n1)). Qed.
Lemma lem3800946 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term472 A B f s b x a1 a2 n1) = (term473 A B f x s b a1 a2 n1).
Proof. exact (MK_COMB (@lem3800944 A B n1 a1 f x s a2 b) (@lem3800945 B a1 a2 n1)). Qed.
Lemma lem3800947 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term474 A B f s b a1 a2 n1) = (term475 A B f s b a1 a2 n1).
Proof. exact (fun_ext (fun x : A => @lem3800946 A B f x s b a1 a2 n1)). Qed.
Lemma lem3800948 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3800949 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term463 A B f s b a1 a2 n1) = (term476 A B f s b a1 a2 n1).
Proof. exact (MK_COMB (@lem3800948 A) (@lem3800947 A B f s b a1 a2 n1)). Qed.
Lemma lem3800950 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : ((term462 A B f s b a1 a2 n1) = (term463 A B f s b a1 a2 n1)) = ((term461 A B f s b a1 a2 n1) = (term476 A B f s b a1 a2 n1)).
Proof. exact (MK_COMB (@lem3800941 A B f s b a1 a2 n1) (@lem3800949 A B f s b a1 a2 n1)). Qed.
Lemma lem3800951 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term461 A B f s b a1 a2 n1) = (term476 A B f s b a1 a2 n1).
Proof. exact (EQ_MP (@lem3800950 A B f s b a1 a2 n1) (@lem3800931 A B f s b a1 a2 n1)). Qed.
Lemma lem3800953 {A : Type'} (P : A -> Prop) (Q : Prop) : (term297 A P Q) = (term298 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3800954 {B : Type'} (P : B -> Prop) (Q : Prop) : (term297 B P Q) = (term298 B P Q).
Proof. exact (@lem3800953 B P Q). Qed.
Lemma lem3800955 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term477 A B f x s b a1 a2 n1) = (term478 A B f x s b a1 a2 n1).
Proof. exact (@lem3800954 B (term456 A B n1 a1 f x s a2 b) (term409 B a1 a2 n1)). Qed.
Lemma lem3800956 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (a2 : B) (b : B) : (term479 A B n1 a1 f x s a2 b c) = (term454 A B n1 a1 f x c s a2 b).
Proof. exact (eq_refl (term479 A B n1 a1 f x s a2 b c)). Qed.
Lemma lem3800957 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (s : A -> Prop) (a2 : B) (b : B) : (term480 A B n1 a1 f x s a2 b) = (term456 A B n1 a1 f x s a2 b).
Proof. exact (fun_ext (fun c : B => @lem3800956 A B n1 a1 f x c s a2 b)). Qed.
Lemma lem3800958 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3800959 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (s : A -> Prop) (a2 : B) (b : B) : (term481 A B n1 a1 f x s a2 b) = (term457 A B n1 a1 f x s a2 b).
Proof. exact (MK_COMB (@lem3800958 B) (@lem3800957 A B n1 a1 f x s a2 b)). Qed.
Lemma lem3800960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3800961 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (s : A -> Prop) (a2 : B) (b : B) : (term482 A B n1 a1 f x s a2 b) = (term471 A B n1 a1 f x s a2 b).
Proof. exact (MK_COMB (@lem3800960) (@lem3800959 A B n1 a1 f x s a2 b)). Qed.
Lemma lem3800962 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) : (term409 B a1 a2 n1) = (term409 B a1 a2 n1).
Proof. exact (eq_refl (term409 B a1 a2 n1)). Qed.
Lemma lem3800963 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term477 A B f x s b a1 a2 n1) = (term473 A B f x s b a1 a2 n1).
Proof. exact (MK_COMB (@lem3800961 A B n1 a1 f x s a2 b) (@lem3800962 B a1 a2 n1)). Qed.
Lemma lem3800964 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3800965 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term483 A B f x s b a1 a2 n1) = (term484 A B f x s b a1 a2 n1).
Proof. exact (MK_COMB (@lem3800964) (@lem3800963 A B f x s b a1 a2 n1)). Qed.
Lemma lem3800966 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (a2 : B) (b : B) : (term479 A B n1 a1 f x s a2 b c) = (term454 A B n1 a1 f x c s a2 b).
Proof. exact (eq_refl (term479 A B n1 a1 f x s a2 b c)). Qed.
Lemma lem3800967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3800968 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (a2 : B) (b : B) : (term485 A B n1 a1 f x s a2 b c) = (term486 A B n1 a1 f x c s a2 b).
Proof. exact (MK_COMB (@lem3800967) (@lem3800966 A B n1 a1 f x c s a2 b)). Qed.
Lemma lem3800969 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) : (term409 B a1 a2 n1) = (term409 B a1 a2 n1).
Proof. exact (eq_refl (term409 B a1 a2 n1)). Qed.
Lemma lem3800970 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term487 A B f x s b c a1 a2 n1) = (term488 A B f x c s b a1 a2 n1).
Proof. exact (MK_COMB (@lem3800968 A B n1 a1 f x c s a2 b) (@lem3800969 B a1 a2 n1)). Qed.
Lemma lem3800971 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term489 A B f x s b a1 a2 n1) = (term490 A B f x s b a1 a2 n1).
Proof. exact (fun_ext (fun c : B => @lem3800970 A B f x c s b a1 a2 n1)). Qed.
Lemma lem3800972 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3800973 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term478 A B f x s b a1 a2 n1) = (term491 A B f x s b a1 a2 n1).
Proof. exact (MK_COMB (@lem3800972 B) (@lem3800971 A B f x s b a1 a2 n1)). Qed.
Lemma lem3800974 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : ((term477 A B f x s b a1 a2 n1) = (term478 A B f x s b a1 a2 n1)) = ((term473 A B f x s b a1 a2 n1) = (term491 A B f x s b a1 a2 n1)).
Proof. exact (MK_COMB (@lem3800965 A B f x s b a1 a2 n1) (@lem3800973 A B f x s b a1 a2 n1)). Qed.
Lemma lem3800975 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term473 A B f x s b a1 a2 n1) = (term491 A B f x s b a1 a2 n1).
Proof. exact (EQ_MP (@lem3800974 A B f x s b a1 a2 n1) (@lem3800955 A B f x s b a1 a2 n1)). Qed.
Lemma lem3800976 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term475 A B f s b a1 a2 n1) = (term492 A B f s b a1 a2 n1).
Proof. exact (fun_ext (fun x : A => @lem3800975 A B f x s b a1 a2 n1)). Qed.
Lemma lem3800977 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3800978 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term476 A B f s b a1 a2 n1) = (term493 A B f s b a1 a2 n1).
Proof. exact (MK_COMB (@lem3800977 A) (@lem3800976 A B f s b a1 a2 n1)). Qed.
Lemma lem3800979 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term461 A B f s b a1 a2 n1) = (term493 A B f s b a1 a2 n1).
Proof. exact (TRANS (@lem3800951 A B f s b a1 a2 n1) (@lem3800978 A B f s b a1 a2 n1)). Qed.
Lemma lem3800980 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term412 A B f s b a1 a2 n1) = (term493 A B f s b a1 a2 n1).
Proof. exact (TRANS (@lem3800927 A B f s b a1 a2 n1) (@lem3800979 A B f s b a1 a2 n1)). Qed.
Lemma lem3800981 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) : (term419 A B f s b a1 n1) = (term494 A B f s b a1 n1).
Proof. exact (fun_ext (fun a2 : B => @lem3800980 A B f s b a1 a2 n1)). Qed.
Lemma lem3800982 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3800983 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) : (term420 A B f s b a1 n1) = (term495 A B f s b a1 n1).
Proof. exact (MK_COMB (@lem3800982 B) (@lem3800981 A B f s b a1 n1)). Qed.
Lemma lem3800984 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) : (term426 A B f s b n1) = (term496 A B f s b n1).
Proof. exact (fun_ext (fun a1 : B => @lem3800983 A B f s b a1 n1)). Qed.
Lemma lem3800985 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3800986 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) : (term427 A B f s b n1) = (term497 A B f s b n1).
Proof. exact (MK_COMB (@lem3800985 B) (@lem3800984 A B f s b n1)). Qed.
Lemma lem3800987 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term432 A B f b n1) = (term498 A B f b n1).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3800986 A B f s b n1)). Qed.
Lemma lem3800988 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3800990 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term433 A B f b n1) = (term499 A B f b n1).
Proof. exact (MK_COMB (@lem3800988 A) (@lem3800987 A B f b n1)). Qed.
Lemma lem3800991 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term392 A B f b n1) = (term499 A B f b n1).
Proof. exact (TRANS (@lem3800690 A B f b n1) (@lem3800990 A B f b n1)). Qed.
Lemma lem3800992 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term392 A B f b n1) : term499 A B f b n1.
Proof. exact (EQ_MP (@lem3800991 A B f b n1) (@lem3800624 A B f b n1 h1)). Qed.
Lemma lem3800993 {A : Type'} (x : A) : (term125 A x) = (term125 A x).
Proof. exact (eq_refl (term125 A x)). Qed.
Lemma lem3800994 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (fun_ext (fun x : A => @lem3800993 A x)). Qed.
Lemma lem3800995 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3801004 {A : Type'} : (term112 A) = (term112 A).
Proof. exact (MK_COMB (@lem3800995 A) (@lem3800994 A)). Qed.
Lemma lem3801005 {A : Type'} (h1 : term112 A) : term112 A.
Proof. exact (EQ_MP (@lem3801004 A) (@lem3800625 A h1)). Qed.
Lemma lem3801006 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) (h1 : term497 A B f s b n1) : term497 A B f s b n1.
Proof. exact (h1). Qed.
Lemma lem3801007 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) (h1 : term495 A B f s b a1 n1) : term495 A B f s b a1 n1.
Proof. exact (h1). Qed.
Lemma lem3801008 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term493 A B f s b a1 a2 n1) : term493 A B f s b a1 a2 n1.
Proof. exact (h1). Qed.
Lemma lem3801009 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term491 A B f x s b a1 a2 n1) : term491 A B f x s b a1 a2 n1.
Proof. exact (h1). Qed.
Lemma lem3801010 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : term488 A B f x c s b a1 a2 n1.
Proof. exact (h1). Qed.
Lemma lem3801017 {A : Type'} (x : A) : (term125 A x) = (term125 A x).
Proof. exact (eq_refl (term125 A x)). Qed.
Lemma lem3801018 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (fun_ext (fun x : A => @lem3801017 A x)). Qed.
Lemma lem3801019 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3801020 {A : Type'} : (term112 A) = (term112 A).
Proof. exact (MK_COMB (@lem3801019 A) (@lem3801018 A)). Qed.
Lemma lem3801021 {A : Type'} (h1 : term112 A) : term112 A.
Proof. exact (EQ_MP (@lem3801020 A) (@lem3801005 A h1)). Qed.
Lemma lem3801042 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) : (term409 B a1 a2 n1) = (term409 B a1 a2 n1).
Proof. exact (eq_refl (term409 B a1 a2 n1)). Qed.
Lemma lem3801055 {A B : Type'} (s : A -> Prop) (a2 : B) (b : B) : (term86 A B s a2 b) = (term86 A B s a2 b).
Proof. exact (eq_refl (term86 A B s a2 b)). Qed.
Lemma lem3801064 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3801065 {A B : Type'} (f : type1411 A B) (x : A) : (f x) = (@I (A -> B -> B) f x).
Proof. exact (@lem3801064 A (B -> B) f x). Qed.
Lemma lem3801066 {B : Type'} (c : B) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem3801067 {A B : Type'} (f : type1411 A B) (x : A) (c : B) : (f x c) = (@I (A -> B -> B) f x c).
Proof. exact (MK_COMB (@lem3801065 A B f x) (@lem3801066 B c)). Qed.
Lemma lem3801069 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3801070 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem3801069 B B f x). Qed.
Lemma lem3801071 {A B : Type'} (f : type1411 A B) (x : A) (c : B) : (@I (A -> B -> B) f x c) = (term337 A B f x c).
Proof. exact (@lem3801070 B (@I (A -> B -> B) f x) c). Qed.
Lemma lem3801073 {A B : Type'} (f : type1411 A B) (x : A) (c : B) : (f x c) = (term337 A B f x c).
Proof. exact (TRANS (@lem3801067 A B f x c) (@lem3801071 A B f x c)). Qed.
Lemma lem3801074 {B : Type'} (a1 : B) : (@eq B a1) = (@eq B a1).
Proof. exact (eq_refl (@eq B a1)). Qed.
Lemma lem3801075 {A B : Type'} (a1 : B) (f : type1411 A B) (x : A) (c : B) : (a1 = (f x c)) = (a1 = (term337 A B f x c)).
Proof. exact (MK_COMB (@lem3801074 B a1) (@lem3801073 A B f x c)). Qed.
Lemma lem3801092 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) : (term338 A B f b s x c n1) = (term338 A B f b s x c n1).
Proof. exact (eq_refl (term338 A B f b s x c n1)). Qed.
Lemma lem3801093 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) : (term200 A B b s n1 a1 f x c) = (term339 A B b s n1 a1 f x c).
Proof. exact (MK_COMB (@lem3801092 A B f b s x c n1) (@lem3801075 A B a1 f x c)). Qed.
Lemma lem3801100 {A : Type'} (x : A) (s : A -> Prop) : (term201 A x s) = (term201 A x s).
Proof. exact (eq_refl (term201 A x s)). Qed.
Lemma lem3801101 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) : (term203 A B b s n1 a1 f x c) = (term340 A B b s n1 a1 f x c).
Proof. exact (MK_COMB (@lem3801100 A x s) (@lem3801093 A B b s n1 a1 f x c)). Qed.
Lemma lem3801102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3801103 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) : (term452 A B b s n1 a1 f x c) = (term500 A B b s n1 a1 f x c).
Proof. exact (MK_COMB (@lem3801102) (@lem3801101 A B b s n1 a1 f x c)). Qed.
Lemma lem3801104 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (a2 : B) (b : B) : (term454 A B n1 a1 f x c s a2 b) = (term501 A B n1 a1 f x c s a2 b).
Proof. exact (MK_COMB (@lem3801103 A B b s n1 a1 f x c) (@lem3801055 A B s a2 b)). Qed.
Lemma lem3801105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3801106 {A B : Type'} (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (a2 : B) (b : B) : (term486 A B n1 a1 f x c s a2 b) = (term502 A B n1 a1 f x c s a2 b).
Proof. exact (MK_COMB (@lem3801105) (@lem3801104 A B n1 a1 f x c s a2 b)). Qed.
Lemma lem3801107 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) : (term488 A B f x c s b a1 a2 n1) = (term503 A B f x c s b a1 a2 n1).
Proof. exact (MK_COMB (@lem3801106 A B n1 a1 f x c s a2 b) (@lem3801042 B a1 a2 n1)). Qed.
Lemma lem3801108 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : term503 A B f x c s b a1 a2 n1.
Proof. exact (EQ_MP (@lem3801107 A B f x c s b a1 a2 n1) (@lem3801010 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801109 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : term409 B a1 a2 n1.
Proof. exact (proj2 (@lem3801108 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801110 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : term501 A B n1 a1 f x c s a2 b.
Proof. exact (proj1 (@lem3801108 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801111 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : term86 A B s a2 b.
Proof. exact (proj2 (@lem3801110 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801112 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : term340 A B b s n1 a1 f x c.
Proof. exact (proj1 (@lem3801110 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801122 {A : Type'} (x : A) : (term125 A x) = (term125 A x).
Proof. exact (eq_refl (term125 A x)). Qed.
Lemma lem3801123 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (fun_ext (fun x : A => @lem3801122 A x)). Qed.
Lemma lem3801124 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3801126 {A : Type'} : (term112 A) = (term112 A).
Proof. exact (MK_COMB (@lem3801124 A) (@lem3801123 A)). Qed.
Lemma lem3801127 {A : Type'} (h1 : term112 A) : term112 A.
Proof. exact (EQ_MP (@lem3801126 A) (@lem3801021 A h1)). Qed.
Lemma lem3801153 {A : Type'} (x : A) : (term125 A x) = (term125 A x).
Proof. exact (eq_refl (term125 A x)). Qed.
Lemma lem3801154 {A : Type'} : (term126 A) = (term126 A).
Proof. exact (fun_ext (fun x : A => @lem3801153 A x)). Qed.
Lemma lem3801155 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3801157 {A : Type'} : (term112 A) = (term112 A).
Proof. exact (MK_COMB (@lem3801155 A) (@lem3801154 A)). Qed.
Lemma lem3801158 {A : Type'} (h1 : term112 A) : term112 A.
Proof. exact (EQ_MP (@lem3801157 A) (@lem3801021 A h1)). Qed.
Lemma lem3801183 {A : Type'} (_43869 : A) (h1 : term112 A) : term344 A _43869.
Proof. exact (@lem3801127 A h1 _43869). Qed.
Lemma lem3801184 {A : Type'} (_43869 : A) : (term344 A _43869) = (term125 A _43869).
Proof. exact (eq_refl (term344 A _43869)). Qed.
Lemma lem3801186 {A : Type'} (_43870 : A) (h1 : term112 A) : term344 A _43870.
Proof. exact (@lem3801158 A h1 _43870). Qed.
Lemma lem3801187 {A : Type'} (_43870 : A) : (term344 A _43870) = (term125 A _43870).
Proof. exact (eq_refl (term344 A _43870)). Qed.
Lemma lem3801355 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : s = (@EMPTY A).
Proof. exact (proj1 (@lem3801111 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801369 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : @IN A x s.
Proof. exact (proj1 (@lem3801112 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801424 {A : Type'} (_43869 : A) (h1 : term112 A) : term125 A _43869.
Proof. exact (EQ_MP (@lem3801184 A _43869) (@lem3801183 A _43869 h1)). Qed.
Lemma lem3801425 {A : Type'} (x : A) : (term345 A x) = (term345 A x).
Proof. exact (eq_refl (term345 A x)). Qed.
Lemma lem3801426 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : (term346 A x s) = (term347 A x).
Proof. exact (MK_COMB (@lem3801425 A x) (@lem3801355 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801427 {A : Type'} (x : A) : (term347 A x) = (@IN A x (@EMPTY A)).
Proof. exact (eq_refl (term347 A x)). Qed.
Lemma lem3801428 {A : Type'} (x : A) (s : A -> Prop) : (term348 A x s) = (term348 A x s).
Proof. exact (eq_refl (term348 A x s)). Qed.
Lemma lem3801429 {A : Type'} (s : A -> Prop) (x : A) : ((term346 A x s) = (term347 A x)) = ((term346 A x s) = (@IN A x (@EMPTY A))).
Proof. exact (MK_COMB (@lem3801428 A x s) (@lem3801427 A x)). Qed.
Lemma lem3801430 {A : Type'} (x : A) (s : A -> Prop) : (term346 A x s) = (@IN A x s).
Proof. exact (eq_refl (term346 A x s)). Qed.
Lemma lem3801431 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3801432 {A : Type'} (x : A) (s : A -> Prop) : (term348 A x s) = (term349 A x s).
Proof. exact (MK_COMB (@lem3801431) (@lem3801430 A x s)). Qed.
Lemma lem3801433 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = (@IN A x (@EMPTY A)).
Proof. exact (eq_refl (@IN A x (@EMPTY A))). Qed.
Lemma lem3801434 {A : Type'} (s : A -> Prop) (x : A) : ((term346 A x s) = (@IN A x (@EMPTY A))) = ((@IN A x s) = (@IN A x (@EMPTY A))).
Proof. exact (MK_COMB (@lem3801432 A x s) (@lem3801433 A x)). Qed.
Lemma lem3801435 {A : Type'} (s : A -> Prop) (x : A) : ((term346 A x s) = (term347 A x)) = ((@IN A x s) = (@IN A x (@EMPTY A))).
Proof. exact (TRANS (@lem3801429 A s x) (@lem3801434 A s x)). Qed.
Lemma lem3801436 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : (@IN A x s) = (@IN A x (@EMPTY A)).
Proof. exact (EQ_MP (@lem3801435 A s x) (@lem3801426 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801604 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : s = (@EMPTY A).
Proof. exact (proj1 (@lem3801111 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801618 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : @IN A x s.
Proof. exact (proj1 (@lem3801112 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801674 {A : Type'} (_43870 : A) (h1 : term112 A) : term125 A _43870.
Proof. exact (EQ_MP (@lem3801187 A _43870) (@lem3801186 A _43870 h1)). Qed.
Lemma lem3801675 {A : Type'} (x : A) : (term345 A x) = (term345 A x).
Proof. exact (eq_refl (term345 A x)). Qed.
Lemma lem3801676 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : (term346 A x s) = (term347 A x).
Proof. exact (MK_COMB (@lem3801675 A x) (@lem3801604 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801677 {A : Type'} (x : A) : (term347 A x) = (@IN A x (@EMPTY A)).
Proof. exact (eq_refl (term347 A x)). Qed.
Lemma lem3801678 {A : Type'} (x : A) (s : A -> Prop) : (term348 A x s) = (term348 A x s).
Proof. exact (eq_refl (term348 A x s)). Qed.
Lemma lem3801679 {A : Type'} (s : A -> Prop) (x : A) : ((term346 A x s) = (term347 A x)) = ((term346 A x s) = (@IN A x (@EMPTY A))).
Proof. exact (MK_COMB (@lem3801678 A x s) (@lem3801677 A x)). Qed.
Lemma lem3801680 {A : Type'} (x : A) (s : A -> Prop) : (term346 A x s) = (@IN A x s).
Proof. exact (eq_refl (term346 A x s)). Qed.
Lemma lem3801681 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3801682 {A : Type'} (x : A) (s : A -> Prop) : (term348 A x s) = (term349 A x s).
Proof. exact (MK_COMB (@lem3801681) (@lem3801680 A x s)). Qed.
Lemma lem3801683 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = (@IN A x (@EMPTY A)).
Proof. exact (eq_refl (@IN A x (@EMPTY A))). Qed.
Lemma lem3801684 {A : Type'} (s : A -> Prop) (x : A) : ((term346 A x s) = (@IN A x (@EMPTY A))) = ((@IN A x s) = (@IN A x (@EMPTY A))).
Proof. exact (MK_COMB (@lem3801682 A x s) (@lem3801683 A x)). Qed.
Lemma lem3801685 {A : Type'} (s : A -> Prop) (x : A) : ((term346 A x s) = (term347 A x)) = ((@IN A x s) = (@IN A x (@EMPTY A))).
Proof. exact (TRANS (@lem3801679 A s x) (@lem3801684 A s x)). Qed.
Lemma lem3801686 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : (@IN A x s) = (@IN A x (@EMPTY A)).
Proof. exact (EQ_MP (@lem3801685 A s x) (@lem3801676 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801832 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : @IN A x (@EMPTY A).
Proof. exact (EQ_MP (@lem3801436 A B f x c s b a1 a2 n1 h1) (@lem3801369 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801833 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : term350 A x.
Proof. exact (fun h0 : term125 A x => @lem3801832 A B f x c s b a1 a2 n1 h1). Qed.
Lemma lem3801835 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3801836 {A : Type'} (x : A) : (term350 A x) = (@IN A x (@EMPTY A)).
Proof. exact (@lem3801835 (@IN A x (@EMPTY A))). Qed.
Lemma lem3801837 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : @IN A x (@EMPTY A).
Proof. exact (EQ_MP (@lem3801836 A x) (@lem3801833 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801840 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3801842 {A : Type'} (_43869 : A) : (term125 A _43869) = (term351 A _43869).
Proof. exact (@lem3801840 (@IN A _43869 (@EMPTY A))). Qed.
Lemma lem3801845 {A : Type'} (_43869 : A) (h1 : term112 A) : term351 A _43869.
Proof. exact (EQ_MP (@lem3801842 A _43869) (@lem3801424 A _43869 h1)). Qed.
Lemma lem3801846 {A : Type'} (_43869 : A) (h1 : term112 A) : term351 A _43869.
Proof. exact (@lem3801845 A _43869 h1). Qed.
Lemma lem3801847 {A : Type'} (x : A) (h1 : term112 A) : term351 A x.
Proof. exact (@lem3801846 A x h1). Qed.
Lemma lem3801850 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term112 A) (h2 : term488 A B f x c s b a1 a2 n1) : False.
Proof. exact (@lem3801847 A x h1 (@lem3801837 A B f x c s b a1 a2 n1 h2)). Qed.
Lemma lem3801851 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term112 A) (h2 : term488 A B f x c s b a1 a2 n1) : term166.
Proof. exact (fun h0 : ~ False => @lem3801850 A B f x c s b a1 a2 n1 h1 h2). Qed.
Lemma lem3801853 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3801854 : term166 = False.
Proof. exact (@lem3801853 False). Qed.
Lemma lem3801957 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : @IN A x (@EMPTY A).
Proof. exact (EQ_MP (@lem3801686 A B f x c s b a1 a2 n1 h1) (@lem3801618 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801958 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : term350 A x.
Proof. exact (fun h0 : term125 A x => @lem3801957 A B f x c s b a1 a2 n1 h1). Qed.
Lemma lem3801960 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3801961 {A : Type'} (x : A) : (term350 A x) = (@IN A x (@EMPTY A)).
Proof. exact (@lem3801960 (@IN A x (@EMPTY A))). Qed.
Lemma lem3801962 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term488 A B f x c s b a1 a2 n1) : @IN A x (@EMPTY A).
Proof. exact (EQ_MP (@lem3801961 A x) (@lem3801958 A B f x c s b a1 a2 n1 h1)). Qed.
Lemma lem3801965 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3801967 {A : Type'} (_43870 : A) : (term125 A _43870) = (term351 A _43870).
Proof. exact (@lem3801965 (@IN A _43870 (@EMPTY A))). Qed.
Lemma lem3801970 {A : Type'} (_43870 : A) (h1 : term112 A) : term351 A _43870.
Proof. exact (EQ_MP (@lem3801967 A _43870) (@lem3801674 A _43870 h1)). Qed.
Lemma lem3801971 {A : Type'} (_43870 : A) (h1 : term112 A) : term351 A _43870.
Proof. exact (@lem3801970 A _43870 h1). Qed.
Lemma lem3801972 {A : Type'} (x : A) (h1 : term112 A) : term351 A x.
Proof. exact (@lem3801971 A x h1). Qed.
Lemma lem3801975 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term112 A) (h2 : term488 A B f x c s b a1 a2 n1) : False.
Proof. exact (@lem3801972 A x h1 (@lem3801962 A B f x c s b a1 a2 n1 h2)). Qed.
Lemma lem3801976 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term112 A) (h2 : term488 A B f x c s b a1 a2 n1) : term166.
Proof. exact (fun h0 : ~ False => @lem3801975 A B f x c s b a1 a2 n1 h1 h2). Qed.
Lemma lem3801978 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3801979 : term166 = False.
Proof. exact (@lem3801978 False). Qed.
Lemma lem3801983 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term112 A) (h2 : term488 A B f x c s b a1 a2 n1) : False.
Proof. exact (EQ_MP (@lem3801979) (@lem3801976 A B f x c s b a1 a2 n1 h1 h2)). Qed.
Lemma lem3801986 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term112 A) (h2 : term488 A B f x c s b a1 a2 n1) : False.
Proof. exact (EQ_MP (@lem3801854) (@lem3801851 A B f x c s b a1 a2 n1 h1 h2)). Qed.
Lemma lem3801987 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term112 A) (h2 : term488 A B f x c s b a1 a2 n1) : (term112 A) = False.
Proof. exact (prop_ext (fun h3 : term112 A => @lem3801983 A B f x c s b a1 a2 n1 h1 h2) (fun h3 : False => @lem3801158 A h1)). Qed.
Lemma lem3801988 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term112 A) (h2 : term488 A B f x c s b a1 a2 n1) : False.
Proof. exact (EQ_MP (@lem3801987 A B f x c s b a1 a2 n1 h1 h2) (@lem3801158 A h1)). Qed.
Lemma lem3801989 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term112 A) (h2 : term488 A B f x c s b a1 a2 n1) : (term112 A) = False.
Proof. exact (prop_ext (fun h3 : term112 A => @lem3801986 A B f x c s b a1 a2 n1 h1 h2) (fun h3 : False => @lem3801127 A h1)). Qed.
Lemma lem3801990 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term112 A) (h2 : term488 A B f x c s b a1 a2 n1) : False.
Proof. exact (EQ_MP (@lem3801989 A B f x c s b a1 a2 n1 h1 h2) (@lem3801127 A h1)). Qed.
Lemma lem3801991 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term112 A) (h2 : term488 A B f x c s b a1 a2 n1) : False.
Proof. exact (or_elim (@lem3801109 A B f x c s b a1 a2 n1 h2) (fun h0 : term153 B a1 a2 => @lem3801990 A B f x c s b a1 a2 n1 h1 h2) (fun h0 : term504 n1 => @lem3801988 A B f x c s b a1 a2 n1 h1 h2)). Qed.
Lemma lem3801992 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term112 A) (h2 : term488 A B f x c s b a1 a2 n1) : (term112 A) = False.
Proof. exact (prop_ext (fun h3 : term112 A => @lem3801991 A B f x c s b a1 a2 n1 h1 h2) (fun h3 : False => @lem3801021 A h1)). Qed.
Lemma lem3801993 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term112 A) (h2 : term488 A B f x c s b a1 a2 n1) : False.
Proof. exact (EQ_MP (@lem3801992 A B f x c s b a1 a2 n1 h1 h2) (@lem3801021 A h1)). Qed.
Lemma lem3801994 {A B : Type'} (f : type1411 A B) (x : A) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term112 A) (h2 : term491 A B f x s b a1 a2 n1) : False.
Proof. exact (ex_elim (@lem3801009 A B f x s b a1 a2 n1 h2) (fun c : B => fun h0 : term490 A B f x s b a1 a2 n1 c => @lem3801993 A B f x c s b a1 a2 n1 h1 h0)). Qed.
Lemma lem3801995 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (a2 : B) (n1 : nat) (h1 : term112 A) (h2 : term493 A B f s b a1 a2 n1) : False.
Proof. exact (ex_elim (@lem3801008 A B f s b a1 a2 n1 h2) (fun x : A => fun h0 : term492 A B f s b a1 a2 n1 x => @lem3801994 A B f x s b a1 a2 n1 h1 h0)). Qed.
Lemma lem3801996 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (a1 : B) (n1 : nat) (h1 : term112 A) (h2 : term495 A B f s b a1 n1) : False.
Proof. exact (ex_elim (@lem3801007 A B f s b a1 n1 h2) (fun a2 : B => fun h0 : term494 A B f s b a1 n1 a2 => @lem3801995 A B f s b a1 a2 n1 h1 h0)). Qed.
Lemma lem3801997 {A B : Type'} (f : type1411 A B) (s : A -> Prop) (b : B) (n1 : nat) (h1 : term112 A) (h2 : term497 A B f s b n1) : False.
Proof. exact (ex_elim (@lem3801006 A B f s b n1 h2) (fun a1 : B => fun h0 : term496 A B f s b n1 a1 => @lem3801996 A B f s b a1 n1 h1 h0)). Qed.
Lemma lem3801998 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term112 A) (h2 : term392 A B f b n1) : False.
Proof. exact (ex_elim (@lem3800992 A B f b n1 h2) (fun s : A -> Prop => fun h0 : term498 A B f b n1 s => @lem3801997 A B f s b n1 h1 h0)). Qed.
Lemma lem3801999 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term112 A) (h2 : term392 A B f b n1) : (term112 A) = False.
Proof. exact (prop_ext (fun h3 : term112 A => @lem3801998 A B f b n1 h1 h2) (fun h3 : False => @lem3801005 A h1)). Qed.
Lemma lem3802000 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term112 A) (h2 : term392 A B f b n1) : False.
Proof. exact (EQ_MP (@lem3801999 A B f b n1 h1 h2) (@lem3801005 A h1)). Qed.
Lemma lem3802001 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term392 A B f b n1) : term117 A.
Proof. exact (fun h0 : term112 A => @lem3802000 A B f b n1 h0 h1). Qed.
Lemma lem3802002 {A : Type'} : (term117 A) = (term118 A).
Proof. exact (@lem69 (term112 A)). Qed.
Lemma lem3802003 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term392 A B f b n1) : term118 A.
Proof. exact (EQ_MP (@lem3802002 A) (@lem3802001 A B f b n1 h1)). Qed.
Lemma lem3802004 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : term395 A B f b n1.
Proof. exact (fun h0 : term392 A B f b n1 => @lem3802003 A B f b n1 h0). Qed.
Lemma lem3802009 {A B : Type'} (b : B) (n1 : nat) : term399 A B b n1.
Proof. exact (fun f : type1411 A B => @lem3802004 A B f b n1). Qed.
Lemma lem3802014 {A B : Type'} (n1 : nat) : term403 A B n1.
Proof. exact (fun b : B => @lem3802009 A B b n1). Qed.
Lemma lem3802019 {A B : Type'} : term407 A B.
Proof. exact (fun n1 : nat => @lem3802014 A B n1). Qed.
Lemma lem3802020 {A B : Type'} : term406 A B.
Proof. exact (EQ_MP (@lem3800623 A B) (@lem3802019 A B)). Qed.
Lemma lem3802021 {A B : Type'} (n1 : nat) : term505 A B n1.
Proof. exact (@lem3802020 A B n1). Qed.
Lemma lem3802022 {A B : Type'} (n1 : nat) : (term505 A B n1) = (term402 A B n1).
Proof. exact (eq_refl (term505 A B n1)). Qed.
Lemma lem3802023 {A B : Type'} (n1 : nat) : term402 A B n1.
Proof. exact (EQ_MP (@lem3802022 A B n1) (@lem3802021 A B n1)). Qed.
Lemma lem3802024 {A B : Type'} (n1 : nat) (b : B) : term506 A B n1 b.
Proof. exact (@lem3802023 A B n1 b). Qed.
Lemma lem3802025 {A B : Type'} (b : B) (n1 : nat) : (term506 A B n1 b) = (term398 A B b n1).
Proof. exact (eq_refl (term506 A B n1 b)). Qed.
Lemma lem3802026 {A B : Type'} (b : B) (n1 : nat) : term398 A B b n1.
Proof. exact (EQ_MP (@lem3802025 A B b n1) (@lem3802024 A B n1 b)). Qed.
Lemma lem3802027 {A B : Type'} (b : B) (n1 : nat) (f : type1411 A B) : term507 A B b n1 f.
Proof. exact (@lem3802026 A B b n1 f). Qed.
Lemma lem3802028 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term507 A B b n1 f) = (term378 A B f b n1).
Proof. exact (eq_refl (term507 A B b n1 f)). Qed.
Lemma lem3802029 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : term378 A B f b n1.
Proof. exact (EQ_MP (@lem3802028 A B f b n1) (@lem3802027 A B b n1 f)). Qed.
Lemma lem3802031 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : term378 A B f b n1.
Proof. exact (@lem3800256 A B f b n1 (@lem3802029 A B f b n1)). Qed.
Lemma lem3802032 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term377 A B f b n1) : term117 A.
Proof. exact (@lem3802031 A B f b n1 (@lem3800238 A B f b n1 h1)). Qed.
Lemma lem3802033 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term377 A B f b n1) : False.
Proof. exact (@lem3802032 A B f b n1 h1 (@lem3800239 A)). Qed.
Lemma lem3802034 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term377 A B f b n1) : (term377 A B f b n1) = False.
Proof. exact (prop_ext (fun h2 : term377 A B f b n1 => @lem3802033 A B f b n1 h1) (fun h2 : False => @lem3800238 A B f b n1 h1)). Qed.
Lemma lem3802035 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term377 A B f b n1) : False.
Proof. exact (EQ_MP (@lem3802034 A B f b n1 h1) (@lem3800238 A B f b n1 h1)). Qed.
Lemma lem3802036 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : term376 A B f b n1.
Proof. exact (fun h0 : term377 A B f b n1 => @lem3802035 A B f b n1 h0). Qed.
Lemma lem3802037 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : term375 A B f b n1.
Proof. exact (EQ_MP (@lem3800237 A B f b n1) (@lem3802036 A B f b n1)). Qed.
Lemma lem3802038 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : term63 A B f b n1.
Proof. exact (EQ_MP (@lem3800233 A B f b n1) (@lem3802037 A B f b n1)). Qed.
Lemma lem3802039 {A B : Type'} (h1 : term508 A B) : term508 A B.
Proof. exact (h1). Qed.
Lemma lem3802040 {A B : Type'} (f : type1411 A B) (h1 : term508 A B) : term509 A B f.
Proof. exact (@lem3802039 A B h1 f). Qed.
Lemma lem3802041 {A B : Type'} (f : type1411 A B) : (term509 A B f) = (term510 A B f).
Proof. exact (eq_refl (term509 A B f)). Qed.
Lemma lem3802042 {A B : Type'} (f : type1411 A B) (h1 : term508 A B) : term510 A B f.
Proof. exact (EQ_MP (@lem3802041 A B f) (@lem3802040 A B f h1)). Qed.
Lemma lem3802043 {A B : Type'} (f : type1411 A B) (b : B) (h1 : term508 A B) : term511 A B f b.
Proof. exact (@lem3802042 A B f h1 b). Qed.
Lemma lem3802044 {A B : Type'} (b : B) (f : type1411 A B) : (term511 A B f b) = (term512 A B b f).
Proof. exact (eq_refl (term511 A B f b)). Qed.
Lemma lem3802045 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term508 A B) : term512 A B b f.
Proof. exact (EQ_MP (@lem3802044 A B b f) (@lem3802043 A B f b h1)). Qed.
Lemma lem3802046 {A B : Type'} (f : type1411 A B) (h1 : term7 A B f) : term7 A B f.
Proof. exact (h1). Qed.
Lemma lem3802047 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term7 A B f) (h2 : term508 A B) : term513 A B b f.
Proof. exact (@lem3802045 A B b f h2 (@lem3802046 A B f h1)). Qed.
Lemma lem3802048 {A B : Type'} (f : type1411 A B) (h1 : term7 A B f) (h2 : term508 A B) : term514 A B f.
Proof. exact (fun b : B => @lem3802047 A B b f h1 h2). Qed.
Lemma lem3802049 {A B : Type'} (f : type1411 A B) (h1 : term508 A B) : term515 A B f.
Proof. exact (fun h0 : term7 A B f => @lem3802048 A B f h0 h1). Qed.
Lemma lem3802050 {A B : Type'} (h1 : term508 A B) : term516 A B.
Proof. exact (fun f : type1411 A B => @lem3802049 A B f h1). Qed.
Lemma lem3802051 {A B : Type'} : term517 A B.
Proof. exact (fun h0 : term508 A B => @lem3802050 A B h0). Qed.
Lemma lem3802052 {A B : Type'} : term516 A B.
Proof. exact (@lem3802051 A B (@lem3797397 A B)). Qed.
Lemma lem3802053 {A B : Type'} (f : type1411 A B) : term518 A B f.
Proof. exact (@lem3802052 A B f). Qed.
Lemma lem3802054 {A B : Type'} (f : type1411 A B) : (term518 A B f) = (term515 A B f).
Proof. exact (eq_refl (term518 A B f)). Qed.
Lemma lem3802057 {A B : Type'} (f : type1411 A B) : term515 A B f.
Proof. exact (EQ_MP (@lem3802054 A B f) (@lem3802053 A B f)). Qed.
Lemma lem3802058 {A B : Type'} (f : type1411 A B) : term515 A B f.
Proof. exact (@lem3802057 A B f). Qed.
Lemma lem3802059 {A B : Type'} (f : type1411 A B) (h1 : term7 A B f) : term514 A B f.
Proof. exact (@lem3802058 A B f (@lem3797446 A B f h1)). Qed.
Lemma lem3802098 {A B : Type'} (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term519 A B a1 n1 f b s a2 n2) : term519 A B a1 n1 f b s a2 n2.
Proof. exact (h1). Qed.
Lemma lem3802099 {A B : Type'} (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term519 A B a1 n1 f b s a2 n2) : term168 A B f b s a1 n1.
Proof. exact (proj1 (@lem3802098 A B a1 n1 f b s a2 n2 h1)). Qed.
Lemma lem3802100 {A B : Type'} (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term519 A B a1 n1 f b s a2 n2) : term519 A B a1 n1 f b s a2 n2.
Proof. exact (h1). Qed.
Lemma lem3802101 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term168 A B f b s a2 n2) : term168 A B f b s a2 n2.
Proof. exact (h1). Qed.
Lemma lem3802102 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) (h1 : term168 A B f b s a1 n1) : term168 A B f b s a1 n1.
Proof. exact (h1). Qed.
Lemma lem3802154 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term7 A B f) : term520 A B f b.
Proof. exact (@lem3802059 A B f h1 b). Qed.
Lemma lem3802155 {A B : Type'} (b : B) (f : type1411 A B) : (term520 A B f b) = (term513 A B b f).
Proof. exact (eq_refl (term520 A B f b)). Qed.
Lemma lem3802156 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term7 A B f) : term513 A B b f.
Proof. exact (EQ_MP (@lem3802155 A B b f) (@lem3802154 A B b f h1)). Qed.
Lemma lem3802157 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (h1 : term7 A B f) : term521 A B b f n.
Proof. exact (@lem3802156 A B b f h1 n). Qed.
Lemma lem3802158 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term521 A B b f n) = (term522 A B b n f).
Proof. exact (eq_refl (term521 A B b f n)). Qed.
Lemma lem3802159 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (h1 : term7 A B f) : term522 A B b n f.
Proof. exact (EQ_MP (@lem3802158 A B b n f) (@lem3802157 A B b n f h1)). Qed.
Lemma lem3802160 {A B : Type'} (b : B) (n : nat) (s : A -> Prop) (f : type1411 A B) (h1 : term7 A B f) : term523 A B b n f s.
Proof. exact (@lem3802159 A B b n f h1 s). Qed.
Lemma lem3802161 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term523 A B b n f s) = (term524 A B b s n f).
Proof. exact (eq_refl (term523 A B b n f s)). Qed.
Lemma lem3802162 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) (h1 : term7 A B f) : term524 A B b s n f.
Proof. exact (EQ_MP (@lem3802161 A B b s n f) (@lem3802160 A B b n s f h1)). Qed.
Lemma lem3802163 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (h1 : term7 A B f) : term525 A B b s n f z.
Proof. exact (@lem3802162 A B b s n f h1 z). Qed.
Lemma lem3802164 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term525 A B b s n f z) = (term526 A B b s n z f).
Proof. exact (eq_refl (term525 A B b s n f z)). Qed.
Lemma lem3802167 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (h1 : term7 A B f) : term526 A B b s n z f.
Proof. exact (EQ_MP (@lem3802164 A B b s n z f) (@lem3802163 A B b s n z f h1)). Qed.
Lemma lem3802168 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (h1 : term7 A B f) : term526 A B b s n z f.
Proof. exact (@lem3802167 A B b s n z f h1). Qed.
Lemma lem3802169 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (h1 : term7 A B f) : term526 A B b s n1 a1 f.
Proof. exact (@lem3802168 A B b s n1 a1 f h1). Qed.
Lemma lem3802170 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) (h1 : term7 A B f) (h2 : term168 A B f b s a1 n1) : term527 A B b s n1 a1 f.
Proof. exact (@lem3802169 A B b s n1 a1 f h1 (@lem3802102 A B f b s a1 n1 h2)). Qed.
Lemma lem3802222 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term7 A B f) : term520 A B f b.
Proof. exact (@lem3802059 A B f h1 b). Qed.
Lemma lem3802223 {A B : Type'} (b : B) (f : type1411 A B) : (term520 A B f b) = (term513 A B b f).
Proof. exact (eq_refl (term520 A B f b)). Qed.
Lemma lem3802224 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term7 A B f) : term513 A B b f.
Proof. exact (EQ_MP (@lem3802223 A B b f) (@lem3802222 A B b f h1)). Qed.
Lemma lem3802225 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (h1 : term7 A B f) : term521 A B b f n.
Proof. exact (@lem3802224 A B b f h1 n). Qed.
Lemma lem3802226 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term521 A B b f n) = (term522 A B b n f).
Proof. exact (eq_refl (term521 A B b f n)). Qed.
Lemma lem3802227 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (h1 : term7 A B f) : term522 A B b n f.
Proof. exact (EQ_MP (@lem3802226 A B b n f) (@lem3802225 A B b n f h1)). Qed.
Lemma lem3802228 {A B : Type'} (b : B) (n : nat) (s : A -> Prop) (f : type1411 A B) (h1 : term7 A B f) : term523 A B b n f s.
Proof. exact (@lem3802227 A B b n f h1 s). Qed.
Lemma lem3802229 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term523 A B b n f s) = (term524 A B b s n f).
Proof. exact (eq_refl (term523 A B b n f s)). Qed.
Lemma lem3802230 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) (h1 : term7 A B f) : term524 A B b s n f.
Proof. exact (EQ_MP (@lem3802229 A B b s n f) (@lem3802228 A B b n s f h1)). Qed.
Lemma lem3802231 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (h1 : term7 A B f) : term525 A B b s n f z.
Proof. exact (@lem3802230 A B b s n f h1 z). Qed.
Lemma lem3802232 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term525 A B b s n f z) = (term526 A B b s n z f).
Proof. exact (eq_refl (term525 A B b s n f z)). Qed.
Lemma lem3802235 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (h1 : term7 A B f) : term526 A B b s n z f.
Proof. exact (EQ_MP (@lem3802232 A B b s n z f) (@lem3802231 A B b s n z f h1)). Qed.
Lemma lem3802236 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (h1 : term7 A B f) : term526 A B b s n z f.
Proof. exact (@lem3802235 A B b s n z f h1). Qed.
Lemma lem3802237 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (h1 : term7 A B f) : term526 A B b s n2 a2 f.
Proof. exact (@lem3802236 A B b s n2 a2 f h1). Qed.
Lemma lem3802238 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term168 A B f b s a2 n2) : term527 A B b s n2 a2 f.
Proof. exact (@lem3802237 A B b s n2 a2 f h1 (@lem3802101 A B f b s a2 n2 h2)). Qed.
Lemma lem3802247 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term168 A B f b s a n) = (term169 A B b s n a f).
Proof. exact (EQ_MP (@lem3791025 A B b s n a f) (@lem3791024 A B b s n a f)). Qed.
Lemma lem3802248 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (a : B) (f : type1411 A B) : (term168 A B f b s a n) = (term169 A B b s n a f).
Proof. exact (@lem3802247 A B b s n a f). Qed.
Lemma lem3802249 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term168 A B f b s a1 n1) = (term169 A B b s n1 a1 f).
Proof. exact (@lem3802248 A B b s n1 a1 f). Qed.
Lemma lem3802264 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3802265 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term528 A B f b s a1 n1) = (term529 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3802264) (@lem3802249 A B b s n1 a1 f)). Qed.
Lemma lem3802272 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term530 B a1 a2 n1 n2) = (term530 B a1 a2 n1 n2).
Proof. exact (eq_refl (term530 B a1 a2 n1 n2)). Qed.
Lemma lem3802273 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term531 A B f b s a1 a2 n1 n2) = (term532 A B b s f a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802265 A B b s n1 a1 f) (@lem3802272 B a1 a2 n1 n2)). Qed.
Lemma lem3802276 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term532 A B b s f a1 a2 n1 n2) = (term531 A B f b s a1 a2 n1 n2).
Proof. exact (SYM (@lem3802273 A B b s f a1 a2 n1 n2)). Qed.
Lemma lem3802277 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (h1 : term169 A B b s n1 a1 f) : term169 A B b s n1 a1 f.
Proof. exact (h1). Qed.
Lemma lem3802278 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (h1 : term206 A B b s n1 a1 f x) : term206 A B b s n1 a1 f x.
Proof. exact (h1). Qed.
Lemma lem3802279 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) (h1 : term203 A B b s n1 a1 f x c) : term203 A B b s n1 a1 f x c.
Proof. exact (h1). Qed.
Lemma lem3802280 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) (h1 : term200 A B b s n1 a1 f x c) : term200 A B b s n1 a1 f x c.
Proof. exact (h1). Qed.
Lemma lem3802281 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3802282 {A B : Type'} (a1 : B) (f : type1411 A B) (x : A) (c : B) (h1 : a1 = (f x c)) : a1 = (f x c).
Proof. exact (h1). Qed.
Lemma lem3802283 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term533 A B f b s x c n1) : term533 A B f b s x c n1.
Proof. exact (h1). Qed.
Lemma lem3802285 (p : Prop) : p = (term109 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3802286 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term530 B a1 a2 n1 n2) = (term534 B a1 a2 n1 n2).
Proof. exact (@lem3802285 (term530 B a1 a2 n1 n2)). Qed.
Lemma lem3802287 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term534 B a1 a2 n1 n2) = (term530 B a1 a2 n1 n2).
Proof. exact (SYM (@lem3802286 B a1 a2 n1 n2)). Qed.
Lemma lem3802288 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (h1 : term535 B a1 a2 n1 n2) : term535 B a1 a2 n1 n2.
Proof. exact (h1). Qed.
Lemma lem3802291 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (h1 : term536 A B b s f x c a1 a2 n1 n2) : term536 A B b s f x c a1 a2 n1 n2.
Proof. exact (h1). Qed.
Lemma lem3802292 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term537 A B b s f x c a1 a2 n1 n2.
Proof. exact (fun h0 : term536 A B b s f x c a1 a2 n1 n2 => @lem3802291 A B b s f x c a1 a2 n1 n2 h0). Qed.
Lemma lem3802293 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (h1 : term537 A B b s f x c a1 a2 n1 n2) : term537 A B b s f x c a1 a2 n1 n2.
Proof. exact (h1). Qed.
Lemma lem3802294 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (h1 : term536 A B b s f x c a1 a2 n1 n2) : term536 A B b s f x c a1 a2 n1 n2.
Proof. exact (h1). Qed.
Lemma lem3802295 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (h1 : term536 A B b s f x c a1 a2 n1 n2) (h2 : term537 A B b s f x c a1 a2 n1 n2) : term536 A B b s f x c a1 a2 n1 n2.
Proof. exact (@lem3802293 A B b s f x c a1 a2 n1 n2 h2 (@lem3802294 A B b s f x c a1 a2 n1 n2 h1)). Qed.
Lemma lem3802296 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (h1 : term536 A B b s f x c a1 a2 n1 n2) : term538 A B b s f x c a1 a2 n1 n2.
Proof. exact (fun h0 : term537 A B b s f x c a1 a2 n1 n2 => @lem3802295 A B b s f x c a1 a2 n1 n2 h1 h0). Qed.
Lemma lem3802297 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (h1 : term537 A B b s f x c a1 a2 n1 n2) : term537 A B b s f x c a1 a2 n1 n2.
Proof. exact (h1). Qed.
Lemma lem3802298 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (h1 : term536 A B b s f x c a1 a2 n1 n2) (h2 : term537 A B b s f x c a1 a2 n1 n2) : term536 A B b s f x c a1 a2 n1 n2.
Proof. exact (@lem3802296 A B b s f x c a1 a2 n1 n2 h1 (@lem3802297 A B b s f x c a1 a2 n1 n2 h2)). Qed.
Lemma lem3802299 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (h1 : term537 A B b s f x c a1 a2 n1 n2) : term537 A B b s f x c a1 a2 n1 n2.
Proof. exact (fun h0 : term536 A B b s f x c a1 a2 n1 n2 => @lem3802298 A B b s f x c a1 a2 n1 n2 h0 h1). Qed.
Lemma lem3802300 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term539 A B b s f x c a1 a2 n1 n2.
Proof. exact (fun h0 : term537 A B b s f x c a1 a2 n1 n2 => @lem3802299 A B b s f x c a1 a2 n1 n2 h0). Qed.
Lemma lem3802303 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term537 A B b s f x c a1 a2 n1 n2.
Proof. exact (@lem3802300 A B b s f x c a1 a2 n1 n2 (@lem3802292 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802304 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term537 A B b s f x c a1 a2 n1 n2.
Proof. exact (@lem3802303 A B b s f x c a1 a2 n1 n2). Qed.
Lemma lem3802600 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3802601 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term534 B a1 a2 n1 n2) = (term540 B a1 a2 n1 n2).
Proof. exact (@lem3802600 (term535 B a1 a2 n1 n2)). Qed.
Lemma lem3802603 (t : Prop) : (term541 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3802604 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term540 B a1 a2 n1 n2) = (term530 B a1 a2 n1 n2).
Proof. exact (@lem3802603 (term530 B a1 a2 n1 n2)). Qed.
Lemma lem3802607 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term534 B a1 a2 n1 n2) = (term530 B a1 a2 n1 n2).
Proof. exact (TRANS (@lem3802601 B a1 a2 n1 n2) (@lem3802604 B a1 a2 n1 n2)). Qed.
Lemma lem3802608 {A B : Type'} (a1 : B) (f : type1411 A B) (x : A) (c : B) : (term542 A B a1 f x c) = (term542 A B a1 f x c).
Proof. exact (eq_refl (term542 A B a1 f x c)). Qed.
Lemma lem3802609 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term543 A B f x c a1 a2 n1 n2) = (term544 A B f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802608 A B a1 f x c) (@lem3802607 B a1 a2 n1 n2)). Qed.
Lemma lem3802612 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) : (term545 A B f b s x c n1) = (term545 A B f b s x c n1).
Proof. exact (eq_refl (term545 A B f b s x c n1)). Qed.
Lemma lem3802613 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term546 A B b s f x c a1 a2 n1 n2) = (term547 A B b s f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802612 A B f b s x c n1) (@lem3802609 A B f x c a1 a2 n1 n2)). Qed.
Lemma lem3802616 {A : Type'} (x : A) (s : A -> Prop) : (term548 A x s) = (term548 A x s).
Proof. exact (eq_refl (term548 A x s)). Qed.
Lemma lem3802617 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term549 A B b s f x c a1 a2 n1 n2) = (term550 A B b s f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802616 A x s) (@lem3802613 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802620 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term551 A B b s n2 a2 f) = (term551 A B b s n2 a2 f).
Proof. exact (eq_refl (term551 A B b s n2 a2 f)). Qed.
Lemma lem3802621 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term552 A B b s f x c a1 a2 n1 n2) = (term553 A B b s f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802620 A B b s n2 a2 f) (@lem3802617 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802624 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term551 A B b s n1 a1 f) = (term551 A B b s n1 a1 f).
Proof. exact (eq_refl (term551 A B b s n1 a1 f)). Qed.
Lemma lem3802625 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term554 A B b s f x c a1 a2 n1 n2) = (term555 A B b s f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802624 A B b s n1 a1 f) (@lem3802621 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802628 {A B : Type'} (f : type1411 A B) : (term556 A B f) = (term556 A B f).
Proof. exact (eq_refl (term556 A B f)). Qed.
Lemma lem3802629 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term557 A B b s f x c a1 a2 n1 n2) = (term558 A B b s f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802628 A B f) (@lem3802625 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802632 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term69 A B f b n1 n2) = (term69 A B f b n1 n2).
Proof. exact (eq_refl (term69 A B f b n1 n2)). Qed.
Lemma lem3802633 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term559 A B b s f x c a1 a2 n1 n2) = (term560 A B b s f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802632 A B f b n1 n2) (@lem3802629 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802636 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term18 A B f b n1) = (term18 A B f b n1).
Proof. exact (eq_refl (term18 A B f b n1)). Qed.
Lemma lem3802637 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term561 A B b s f x c a1 a2 n1 n2) = (term562 A B b s f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802636 A B f b n1) (@lem3802633 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802640 {A B : Type'} (f : type1411 A B) : (term563 A B f) = (term563 A B f).
Proof. exact (eq_refl (term563 A B f)). Qed.
Lemma lem3802641 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term536 A B b s f x c a1 a2 n1 n2) = (term564 A B b s f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802640 A B f) (@lem3802637 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802644 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term565 A B s f x c a1 a2 n1 n2) = (term566 A B s f x c a1 a2 n1 n2).
Proof. exact (fun_ext (fun b : B => @lem3802641 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802645 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3802646 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term567 A B s f x c a1 a2 n1 n2) = (term568 A B s f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802645 B) (@lem3802644 A B s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802651 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term569 A B f x c a1 a2 n1 n2) = (term570 A B f x c a1 a2 n1 n2).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3802646 A B s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802652 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3802653 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term571 A B f x c a1 a2 n1 n2) = (term572 A B f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802652 A) (@lem3802651 A B f x c a1 a2 n1 n2)). Qed.
Lemma lem3802658 {A B : Type'} (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term573 A B x c a1 a2 n1 n2) = (term574 A B x c a1 a2 n1 n2).
Proof. exact (fun_ext (fun f : type1411 A B => @lem3802653 A B f x c a1 a2 n1 n2)). Qed.
Lemma lem3802659 {A B : Type'} : (@all (A -> B -> B)) = (@all (A -> B -> B)).
Proof. exact (eq_refl (@all (A -> B -> B))). Qed.
Lemma lem3802660 {A B : Type'} (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term575 A B x c a1 a2 n1 n2) = (term576 A B x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802659 A B) (@lem3802658 A B x c a1 a2 n1 n2)). Qed.
Lemma lem3802665 {A B : Type'} (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term577 A B c a1 a2 n1 n2) = (term578 A B c a1 a2 n1 n2).
Proof. exact (fun_ext (fun x : A => @lem3802660 A B x c a1 a2 n1 n2)). Qed.
Lemma lem3802666 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3802667 {A B : Type'} (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term579 A B c a1 a2 n1 n2) = (term580 A B c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802666 A) (@lem3802665 A B c a1 a2 n1 n2)). Qed.
Lemma lem3802672 {A B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term581 A B a1 a2 n1 n2) = (term582 A B a1 a2 n1 n2).
Proof. exact (fun_ext (fun c : B => @lem3802667 A B c a1 a2 n1 n2)). Qed.
Lemma lem3802673 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3802674 {A B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term583 A B a1 a2 n1 n2) = (term584 A B a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802673 B) (@lem3802672 A B a1 a2 n1 n2)). Qed.
Lemma lem3802679 {A B : Type'} (a2 : B) (n1 : nat) (n2 : nat) : (term585 A B a2 n1 n2) = (term586 A B a2 n1 n2).
Proof. exact (fun_ext (fun a1 : B => @lem3802674 A B a1 a2 n1 n2)). Qed.
Lemma lem3802680 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3802681 {A B : Type'} (a2 : B) (n1 : nat) (n2 : nat) : (term587 A B a2 n1 n2) = (term588 A B a2 n1 n2).
Proof. exact (MK_COMB (@lem3802680 B) (@lem3802679 A B a2 n1 n2)). Qed.
Lemma lem3802686 {A B : Type'} (n1 : nat) (n2 : nat) : (term589 A B n1 n2) = (term590 A B n1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3802681 A B a2 n1 n2)). Qed.
Lemma lem3802687 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3802688 {A B : Type'} (n1 : nat) (n2 : nat) : (term591 A B n1 n2) = (term592 A B n1 n2).
Proof. exact (MK_COMB (@lem3802687 B) (@lem3802686 A B n1 n2)). Qed.
Lemma lem3802693 {A B : Type'} (n2 : nat) : (term593 A B n2) = (term594 A B n2).
Proof. exact (fun_ext (fun n1 : nat => @lem3802688 A B n1 n2)). Qed.
Lemma lem3802694 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3802695 {A B : Type'} (n2 : nat) : (term595 A B n2) = (term596 A B n2).
Proof. exact (MK_COMB (@lem3802694) (@lem3802693 A B n2)). Qed.
Lemma lem3802700 {A B : Type'} : (term597 A B) = (term598 A B).
Proof. exact (fun_ext (fun n2 : nat => @lem3802695 A B n2)). Qed.
Lemma lem3802701 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3802710 {A B : Type'} : (term599 A B) = (term600 A B).
Proof. exact (MK_COMB (@lem3802701) (@lem3802700 A B)). Qed.
Lemma lem3802727 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term550 A B b s f x c a1 a2 n1 n2) = (term550 A B b s f x c a1 a2 n1 n2).
Proof. exact (eq_refl (term550 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802732 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (w : B) : (term200 A B b s n2 a2 f x w) = (term200 A B b s n2 a2 f x w).
Proof. exact (eq_refl (term200 A B b s n2 a2 f x w)). Qed.
Lemma lem3802733 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term198 A B b s n2 a2 f x) = (term198 A B b s n2 a2 f x).
Proof. exact (fun_ext (fun w : B => @lem3802732 A B b s n2 a2 f x w)). Qed.
Lemma lem3802734 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3802735 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term211 A B b s n2 a2 f x) = (term211 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3802734 B) (@lem3802733 A B b s n2 a2 f x)). Qed.
Lemma lem3802738 {A : Type'} (x : A) (s : A -> Prop) : (term548 A x s) = (term548 A x s).
Proof. exact (eq_refl (term548 A x s)). Qed.
Lemma lem3802739 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term601 A B b s n2 a2 f x) = (term601 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3802738 A x s) (@lem3802735 A B b s n2 a2 f x)). Qed.
Lemma lem3802740 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term602 A B b s n2 a2 f) = (term602 A B b s n2 a2 f).
Proof. exact (fun_ext (fun x : A => @lem3802739 A B b s n2 a2 f x)). Qed.
Lemma lem3802741 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3802742 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term527 A B b s n2 a2 f) = (term527 A B b s n2 a2 f).
Proof. exact (MK_COMB (@lem3802741 A) (@lem3802740 A B b s n2 a2 f)). Qed.
Lemma lem3802743 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3802744 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term551 A B b s n2 a2 f) = (term551 A B b s n2 a2 f).
Proof. exact (MK_COMB (@lem3802743) (@lem3802742 A B b s n2 a2 f)). Qed.
Lemma lem3802745 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term553 A B b s f x c a1 a2 n1 n2) = (term553 A B b s f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802744 A B b s n2 a2 f) (@lem3802727 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802750 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (w : B) : (term200 A B b s n1 a1 f x w) = (term200 A B b s n1 a1 f x w).
Proof. exact (eq_refl (term200 A B b s n1 a1 f x w)). Qed.
Lemma lem3802751 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term198 A B b s n1 a1 f x) = (term198 A B b s n1 a1 f x).
Proof. exact (fun_ext (fun w : B => @lem3802750 A B b s n1 a1 f x w)). Qed.
Lemma lem3802752 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3802753 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term211 A B b s n1 a1 f x) = (term211 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3802752 B) (@lem3802751 A B b s n1 a1 f x)). Qed.
Lemma lem3802756 {A : Type'} (x : A) (s : A -> Prop) : (term548 A x s) = (term548 A x s).
Proof. exact (eq_refl (term548 A x s)). Qed.
Lemma lem3802757 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term601 A B b s n1 a1 f x) = (term601 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3802756 A x s) (@lem3802753 A B b s n1 a1 f x)). Qed.
Lemma lem3802758 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term602 A B b s n1 a1 f) = (term602 A B b s n1 a1 f).
Proof. exact (fun_ext (fun x : A => @lem3802757 A B b s n1 a1 f x)). Qed.
Lemma lem3802759 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3802760 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term527 A B b s n1 a1 f) = (term527 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3802759 A) (@lem3802758 A B b s n1 a1 f)). Qed.
Lemma lem3802761 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3802762 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term551 A B b s n1 a1 f) = (term551 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3802761) (@lem3802760 A B b s n1 a1 f)). Qed.
Lemma lem3802763 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term555 A B b s f x c a1 a2 n1 n2) = (term555 A B b s f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802762 A B b s n1 a1 f) (@lem3802745 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802768 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) (w : B) : (term200 A B b s n z f x w) = (term200 A B b s n z f x w).
Proof. exact (eq_refl (term200 A B b s n z f x w)). Qed.
Lemma lem3802769 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term198 A B b s n z f x) = (term198 A B b s n z f x).
Proof. exact (fun_ext (fun w : B => @lem3802768 A B b s n z f x w)). Qed.
Lemma lem3802770 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3802771 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term211 A B b s n z f x) = (term211 A B b s n z f x).
Proof. exact (MK_COMB (@lem3802770 B) (@lem3802769 A B b s n z f x)). Qed.
Lemma lem3802774 {A : Type'} (x : A) (s : A -> Prop) : (term548 A x s) = (term548 A x s).
Proof. exact (eq_refl (term548 A x s)). Qed.
Lemma lem3802775 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term601 A B b s n z f x) = (term601 A B b s n z f x).
Proof. exact (MK_COMB (@lem3802774 A x s) (@lem3802771 A B b s n z f x)). Qed.
Lemma lem3802776 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term602 A B b s n z f) = (term602 A B b s n z f).
Proof. exact (fun_ext (fun x : A => @lem3802775 A B b s n z f x)). Qed.
Lemma lem3802777 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3802778 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term527 A B b s n z f) = (term527 A B b s n z f).
Proof. exact (MK_COMB (@lem3802777 A) (@lem3802776 A B b s n z f)). Qed.
Lemma lem3802781 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (z : B) (n : nat) : (term528 A B f b s z n) = (term528 A B f b s z n).
Proof. exact (eq_refl (term528 A B f b s z n)). Qed.
Lemma lem3802782 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term526 A B b s n z f) = (term526 A B b s n z f).
Proof. exact (MK_COMB (@lem3802781 A B f b s z n) (@lem3802778 A B b s n z f)). Qed.
Lemma lem3802783 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term603 A B b s n f) = (term603 A B b s n f).
Proof. exact (fun_ext (fun z : B => @lem3802782 A B b s n z f)). Qed.
Lemma lem3802784 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3802785 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term524 A B b s n f) = (term524 A B b s n f).
Proof. exact (MK_COMB (@lem3802784 B) (@lem3802783 A B b s n f)). Qed.
Lemma lem3802786 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term604 A B b n f) = (term604 A B b n f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3802785 A B b s n f)). Qed.
Lemma lem3802787 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3802788 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term522 A B b n f) = (term522 A B b n f).
Proof. exact (MK_COMB (@lem3802787 A) (@lem3802786 A B b n f)). Qed.
Lemma lem3802789 {A B : Type'} (b : B) (f : type1411 A B) : (term605 A B b f) = (term605 A B b f).
Proof. exact (fun_ext (fun n : nat => @lem3802788 A B b n f)). Qed.
Lemma lem3802790 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3802791 {A B : Type'} (b : B) (f : type1411 A B) : (term513 A B b f) = (term513 A B b f).
Proof. exact (MK_COMB (@lem3802790) (@lem3802789 A B b f)). Qed.
Lemma lem3802792 {A B : Type'} (f : type1411 A B) : (term606 A B f) = (term606 A B f).
Proof. exact (fun_ext (fun b : B => @lem3802791 A B b f)). Qed.
Lemma lem3802793 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3802794 {A B : Type'} (f : type1411 A B) : (term514 A B f) = (term514 A B f).
Proof. exact (MK_COMB (@lem3802793 B) (@lem3802792 A B f)). Qed.
Lemma lem3802795 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3802796 {A B : Type'} (f : type1411 A B) : (term556 A B f) = (term556 A B f).
Proof. exact (MK_COMB (@lem3802795) (@lem3802794 A B f)). Qed.
Lemma lem3802797 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term558 A B b s f x c a1 a2 n1 n2) = (term558 A B b s f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802796 A B f) (@lem3802763 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802810 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term607 A B f b s a1 a2 n1 n2) = (term607 A B f b s a1 a2 n1 n2).
Proof. exact (eq_refl (term607 A B f b s a1 a2 n1 n2)). Qed.
Lemma lem3802811 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) (n2 : nat) : (term608 A B f b s a1 n1 n2) = (term608 A B f b s a1 n1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3802810 A B f b s a1 a2 n1 n2)). Qed.
Lemma lem3802812 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3802813 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) (n2 : nat) : (term609 A B f b s a1 n1 n2) = (term609 A B f b s a1 n1 n2).
Proof. exact (MK_COMB (@lem3802812 B) (@lem3802811 A B f b s a1 n1 n2)). Qed.
Lemma lem3802814 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term610 A B f b s n1 n2) = (term610 A B f b s n1 n2).
Proof. exact (fun_ext (fun a1 : B => @lem3802813 A B f b s a1 n1 n2)). Qed.
Lemma lem3802815 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3802816 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term611 A B f b s n1 n2) = (term611 A B f b s n1 n2).
Proof. exact (MK_COMB (@lem3802815 B) (@lem3802814 A B f b s n1 n2)). Qed.
Lemma lem3802817 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term612 A B f b n1 n2) = (term612 A B f b n1 n2).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3802816 A B f b s n1 n2)). Qed.
Lemma lem3802818 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3802819 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term67 A B f b n1 n2) = (term67 A B f b n1 n2).
Proof. exact (MK_COMB (@lem3802818 A) (@lem3802817 A B f b n1 n2)). Qed.
Lemma lem3802820 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3802821 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term69 A B f b n1 n2) = (term69 A B f b n1 n2).
Proof. exact (MK_COMB (@lem3802820) (@lem3802819 A B f b n1 n2)). Qed.
Lemma lem3802822 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term560 A B b s f x c a1 a2 n1 n2) = (term560 A B b s f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802821 A B f b n1 n2) (@lem3802797 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802835 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term613 A B f b s a1 a2 n1 n2) = (term613 A B f b s a1 a2 n1 n2).
Proof. exact (eq_refl (term613 A B f b s a1 a2 n1 n2)). Qed.
Lemma lem3802836 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) (n2 : nat) : (term614 A B f b s a1 n1 n2) = (term614 A B f b s a1 n1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3802835 A B f b s a1 a2 n1 n2)). Qed.
Lemma lem3802837 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3802838 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) (n2 : nat) : (term615 A B f b s a1 n1 n2) = (term615 A B f b s a1 n1 n2).
Proof. exact (MK_COMB (@lem3802837 B) (@lem3802836 A B f b s a1 n1 n2)). Qed.
Lemma lem3802839 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term616 A B f b s n1 n2) = (term616 A B f b s n1 n2).
Proof. exact (fun_ext (fun a1 : B => @lem3802838 A B f b s a1 n1 n2)). Qed.
Lemma lem3802840 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3802841 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term617 A B f b s n1 n2) = (term617 A B f b s n1 n2).
Proof. exact (MK_COMB (@lem3802840 B) (@lem3802839 A B f b s n1 n2)). Qed.
Lemma lem3802842 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term618 A B f b n1 n2) = (term618 A B f b n1 n2).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3802841 A B f b s n1 n2)). Qed.
Lemma lem3802843 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3802844 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term619 A B f b n1 n2) = (term619 A B f b n1 n2).
Proof. exact (MK_COMB (@lem3802843 A) (@lem3802842 A B f b n1 n2)). Qed.
Lemma lem3802845 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term620 A B f b n1) = (term620 A B f b n1).
Proof. exact (fun_ext (fun n2 : nat => @lem3802844 A B f b n1 n2)). Qed.
Lemma lem3802846 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3802847 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term16 A B f b n1) = (term16 A B f b n1).
Proof. exact (MK_COMB (@lem3802846) (@lem3802845 A B f b n1)). Qed.
Lemma lem3802848 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3802849 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term18 A B f b n1) = (term18 A B f b n1).
Proof. exact (MK_COMB (@lem3802848) (@lem3802847 A B f b n1)). Qed.
Lemma lem3802850 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term562 A B b s f x c a1 a2 n1 n2) = (term562 A B b s f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802849 A B f b n1) (@lem3802822 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802857 {A B : Type'} (y : A) (f : type1411 A B) (x : A) (s : B) : (term621 A B y f x s) = (term621 A B y f x s).
Proof. exact (eq_refl (term621 A B y f x s)). Qed.
Lemma lem3802858 {A B : Type'} (y : A) (f : type1411 A B) (x : A) : (term622 A B y f x) = (term622 A B y f x).
Proof. exact (fun_ext (fun s : B => @lem3802857 A B y f x s)). Qed.
Lemma lem3802859 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3802860 {A B : Type'} (y : A) (f : type1411 A B) (x : A) : (term623 A B y f x) = (term623 A B y f x).
Proof. exact (MK_COMB (@lem3802859 B) (@lem3802858 A B y f x)). Qed.
Lemma lem3802861 {A B : Type'} (f : type1411 A B) (x : A) : (term624 A B f x) = (term624 A B f x).
Proof. exact (fun_ext (fun y : A => @lem3802860 A B y f x)). Qed.
Lemma lem3802862 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3802863 {A B : Type'} (f : type1411 A B) (x : A) : (term625 A B f x) = (term625 A B f x).
Proof. exact (MK_COMB (@lem3802862 A) (@lem3802861 A B f x)). Qed.
Lemma lem3802864 {A B : Type'} (f : type1411 A B) : (term626 A B f) = (term626 A B f).
Proof. exact (fun_ext (fun x : A => @lem3802863 A B f x)). Qed.
Lemma lem3802865 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3802866 {A B : Type'} (f : type1411 A B) : (term7 A B f) = (term7 A B f).
Proof. exact (MK_COMB (@lem3802865 A) (@lem3802864 A B f)). Qed.
Lemma lem3802867 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3802868 {A B : Type'} (f : type1411 A B) : (term563 A B f) = (term563 A B f).
Proof. exact (MK_COMB (@lem3802867) (@lem3802866 A B f)). Qed.
Lemma lem3802869 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term564 A B b s f x c a1 a2 n1 n2) = (term564 A B b s f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802868 A B f) (@lem3802850 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802870 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term566 A B s f x c a1 a2 n1 n2) = (term566 A B s f x c a1 a2 n1 n2).
Proof. exact (fun_ext (fun b : B => @lem3802869 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802871 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3802872 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term568 A B s f x c a1 a2 n1 n2) = (term568 A B s f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802871 B) (@lem3802870 A B s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802873 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term570 A B f x c a1 a2 n1 n2) = (term570 A B f x c a1 a2 n1 n2).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3802872 A B s f x c a1 a2 n1 n2)). Qed.
Lemma lem3802874 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3802875 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term572 A B f x c a1 a2 n1 n2) = (term572 A B f x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802874 A) (@lem3802873 A B f x c a1 a2 n1 n2)). Qed.
Lemma lem3802876 {A B : Type'} (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term574 A B x c a1 a2 n1 n2) = (term574 A B x c a1 a2 n1 n2).
Proof. exact (fun_ext (fun f : type1411 A B => @lem3802875 A B f x c a1 a2 n1 n2)). Qed.
Lemma lem3802877 {A B : Type'} : (@all (A -> B -> B)) = (@all (A -> B -> B)).
Proof. exact (eq_refl (@all (A -> B -> B))). Qed.
Lemma lem3802878 {A B : Type'} (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term576 A B x c a1 a2 n1 n2) = (term576 A B x c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802877 A B) (@lem3802876 A B x c a1 a2 n1 n2)). Qed.
Lemma lem3802879 {A B : Type'} (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term578 A B c a1 a2 n1 n2) = (term578 A B c a1 a2 n1 n2).
Proof. exact (fun_ext (fun x : A => @lem3802878 A B x c a1 a2 n1 n2)). Qed.
Lemma lem3802880 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3802881 {A B : Type'} (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term580 A B c a1 a2 n1 n2) = (term580 A B c a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802880 A) (@lem3802879 A B c a1 a2 n1 n2)). Qed.
Lemma lem3802882 {A B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term582 A B a1 a2 n1 n2) = (term582 A B a1 a2 n1 n2).
Proof. exact (fun_ext (fun c : B => @lem3802881 A B c a1 a2 n1 n2)). Qed.
Lemma lem3802883 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3802884 {A B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term584 A B a1 a2 n1 n2) = (term584 A B a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3802883 B) (@lem3802882 A B a1 a2 n1 n2)). Qed.
Lemma lem3802885 {A B : Type'} (a2 : B) (n1 : nat) (n2 : nat) : (term586 A B a2 n1 n2) = (term586 A B a2 n1 n2).
Proof. exact (fun_ext (fun a1 : B => @lem3802884 A B a1 a2 n1 n2)). Qed.
Lemma lem3802886 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3802887 {A B : Type'} (a2 : B) (n1 : nat) (n2 : nat) : (term588 A B a2 n1 n2) = (term588 A B a2 n1 n2).
Proof. exact (MK_COMB (@lem3802886 B) (@lem3802885 A B a2 n1 n2)). Qed.
Lemma lem3802888 {A B : Type'} (n1 : nat) (n2 : nat) : (term590 A B n1 n2) = (term590 A B n1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3802887 A B a2 n1 n2)). Qed.
Lemma lem3802889 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3802890 {A B : Type'} (n1 : nat) (n2 : nat) : (term592 A B n1 n2) = (term592 A B n1 n2).
Proof. exact (MK_COMB (@lem3802889 B) (@lem3802888 A B n1 n2)). Qed.
Lemma lem3802891 {A B : Type'} (n2 : nat) : (term594 A B n2) = (term594 A B n2).
Proof. exact (fun_ext (fun n1 : nat => @lem3802890 A B n1 n2)). Qed.
Lemma lem3802892 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3802893 {A B : Type'} (n2 : nat) : (term596 A B n2) = (term596 A B n2).
Proof. exact (MK_COMB (@lem3802892) (@lem3802891 A B n2)). Qed.
Lemma lem3802894 {A B : Type'} : (term598 A B) = (term598 A B).
Proof. exact (fun_ext (fun n2 : nat => @lem3802893 A B n2)). Qed.
Lemma lem3802895 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3802896 {A B : Type'} : (term600 A B) = (term600 A B).
Proof. exact (MK_COMB (@lem3802895) (@lem3802894 A B)). Qed.
Lemma lem3803121 {A B : Type'} : (term599 A B) = (term600 A B).
Proof. exact (TRANS (@lem3802710 A B) (@lem3802896 A B)). Qed.
Lemma lem3803122 {A B : Type'} : (term600 A B) = (term599 A B).
Proof. exact (SYM (@lem3803121 A B)). Qed.
Lemma lem3803124 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term16 A B f b n1.
Proof. exact (h1). Qed.
Lemma lem3803126 {A B : Type'} (f : type1411 A B) (h1 : term514 A B f) : term514 A B f.
Proof. exact (h1). Qed.
Lemma lem3803127 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (h1 : term527 A B b s n1 a1 f) : term527 A B b s n1 a1 f.
Proof. exact (h1). Qed.
Lemma lem3803128 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (h1 : term527 A B b s n2 a2 f) : term527 A B b s n2 a2 f.
Proof. exact (h1). Qed.
Lemma lem3803133 (p : Prop) : p = (term109 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3803134 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term530 B a1 a2 n1 n2) = (term534 B a1 a2 n1 n2).
Proof. exact (@lem3803133 (term530 B a1 a2 n1 n2)). Qed.
Lemma lem3803135 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term534 B a1 a2 n1 n2) = (term530 B a1 a2 n1 n2).
Proof. exact (SYM (@lem3803134 B a1 a2 n1 n2)). Qed.
Lemma lem3803136 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (h1 : term535 B a1 a2 n1 n2) : term535 B a1 a2 n1 n2.
Proof. exact (h1). Qed.
Lemma lem3803255 {A B : Type'} (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) : (term627 A B a1 n1 f b s a2 n2) = (term628 A B a1 n1 f b s a2 n2).
Proof. exact (@lem17045 (@FINREC A B f b s a1 n1) (@FINREC A B f b s a2 n2)). Qed.
Lemma lem3803260 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term629 B a1 a2 n1 n2) = (term629 B a1 a2 n1 n2).
Proof. exact (eq_refl (term629 B a1 a2 n1 n2)). Qed.
Lemma lem3803261 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3803262 {A B : Type'} (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) : (term630 A B a1 n1 f b s a2 n2) = (term631 A B a1 n1 f b s a2 n2).
Proof. exact (MK_COMB (@lem3803261) (@lem3803255 A B a1 n1 f b s a2 n2)). Qed.
Lemma lem3803263 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term632 A B f b s a1 a2 n1 n2) = (term633 A B f b s a1 a2 n1 n2).
Proof. exact (MK_COMB (@lem3803262 A B a1 n1 f b s a2 n2) (@lem3803260 B a1 a2 n1 n2)). Qed.
Lemma lem3803264 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term613 A B f b s a1 a2 n1 n2) = (term632 A B f b s a1 a2 n1 n2).
Proof. exact (@lem17265 (term634 A B a1 n1 f b s a2 n2) (term629 B a1 a2 n1 n2)). Qed.
Lemma lem3803265 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term613 A B f b s a1 a2 n1 n2) = (term633 A B f b s a1 a2 n1 n2).
Proof. exact (TRANS (@lem3803264 A B f b s a1 a2 n1 n2) (@lem3803263 A B f b s a1 a2 n1 n2)). Qed.
Lemma lem3803266 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) (n2 : nat) : (term614 A B f b s a1 n1 n2) = (term635 A B f b s a1 n1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3803265 A B f b s a1 a2 n1 n2)). Qed.
Lemma lem3803267 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3803268 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) (n2 : nat) : (term615 A B f b s a1 n1 n2) = (term636 A B f b s a1 n1 n2).
Proof. exact (MK_COMB (@lem3803267 B) (@lem3803266 A B f b s a1 n1 n2)). Qed.
Lemma lem3803269 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term616 A B f b s n1 n2) = (term637 A B f b s n1 n2).
Proof. exact (fun_ext (fun a1 : B => @lem3803268 A B f b s a1 n1 n2)). Qed.
Lemma lem3803270 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3803271 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term617 A B f b s n1 n2) = (term638 A B f b s n1 n2).
Proof. exact (MK_COMB (@lem3803270 B) (@lem3803269 A B f b s n1 n2)). Qed.
Lemma lem3803272 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term618 A B f b n1 n2) = (term639 A B f b n1 n2).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3803271 A B f b s n1 n2)). Qed.
Lemma lem3803273 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3803274 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term619 A B f b n1 n2) = (term640 A B f b n1 n2).
Proof. exact (MK_COMB (@lem3803273 A) (@lem3803272 A B f b n1 n2)). Qed.
Lemma lem3803275 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term620 A B f b n1) = (term641 A B f b n1).
Proof. exact (fun_ext (fun n2 : nat => @lem3803274 A B f b n1 n2)). Qed.
Lemma lem3803276 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3803341 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term16 A B f b n1) = (term642 A B f b n1).
Proof. exact (MK_COMB (@lem3803276) (@lem3803275 A B f b n1)). Qed.
Lemma lem3803342 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term642 A B f b n1.
Proof. exact (EQ_MP (@lem3803341 A B f b n1) (@lem3803124 A B f b n1 h1)). Qed.
Lemma lem3803436 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) (w : B) : (term200 A B b s n z f x w) = (term200 A B b s n z f x w).
Proof. exact (eq_refl (term200 A B b s n z f x w)). Qed.
Lemma lem3803437 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term198 A B b s n z f x) = (term198 A B b s n z f x).
Proof. exact (fun_ext (fun w : B => @lem3803436 A B b s n z f x w)). Qed.
Lemma lem3803438 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3803439 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term211 A B b s n z f x) = (term211 A B b s n z f x).
Proof. exact (MK_COMB (@lem3803438 B) (@lem3803437 A B b s n z f x)). Qed.
Lemma lem3803441 {A : Type'} (x : A) (s : A -> Prop) : (term643 A x s) = (term643 A x s).
Proof. exact (eq_refl (term643 A x s)). Qed.
Lemma lem3803442 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term644 A B b s n z f x) = (term644 A B b s n z f x).
Proof. exact (MK_COMB (@lem3803441 A x s) (@lem3803439 A B b s n z f x)). Qed.
Lemma lem3803443 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term601 A B b s n z f x) = (term644 A B b s n z f x).
Proof. exact (@lem17265 (@IN A x s) (term211 A B b s n z f x)). Qed.
Lemma lem3803444 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term601 A B b s n z f x) = (term644 A B b s n z f x).
Proof. exact (TRANS (@lem3803443 A B b s n z f x) (@lem3803442 A B b s n z f x)). Qed.
Lemma lem3803445 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term602 A B b s n z f) = (term645 A B b s n z f).
Proof. exact (fun_ext (fun x : A => @lem3803444 A B b s n z f x)). Qed.
Lemma lem3803446 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3803447 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term527 A B b s n z f) = (term646 A B b s n z f).
Proof. exact (MK_COMB (@lem3803446 A) (@lem3803445 A B b s n z f)). Qed.
Lemma lem3803449 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (z : B) (n : nat) : (term647 A B f b s z n) = (term647 A B f b s z n).
Proof. exact (eq_refl (term647 A B f b s z n)). Qed.
Lemma lem3803450 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term648 A B b s n z f) = (term649 A B b s n z f).
Proof. exact (MK_COMB (@lem3803449 A B f b s z n) (@lem3803447 A B b s n z f)). Qed.
Lemma lem3803451 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term526 A B b s n z f) = (term648 A B b s n z f).
Proof. exact (@lem17265 (term168 A B f b s z n) (term527 A B b s n z f)). Qed.
Lemma lem3803452 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term526 A B b s n z f) = (term649 A B b s n z f).
Proof. exact (TRANS (@lem3803451 A B b s n z f) (@lem3803450 A B b s n z f)). Qed.
Lemma lem3803453 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term603 A B b s n f) = (term650 A B b s n f).
Proof. exact (fun_ext (fun z : B => @lem3803452 A B b s n z f)). Qed.
Lemma lem3803454 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3803455 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term524 A B b s n f) = (term651 A B b s n f).
Proof. exact (MK_COMB (@lem3803454 B) (@lem3803453 A B b s n f)). Qed.
Lemma lem3803456 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term604 A B b n f) = (term652 A B b n f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3803455 A B b s n f)). Qed.
Lemma lem3803457 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3803458 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term522 A B b n f) = (term653 A B b n f).
Proof. exact (MK_COMB (@lem3803457 A) (@lem3803456 A B b n f)). Qed.
Lemma lem3803459 {A B : Type'} (b : B) (f : type1411 A B) : (term605 A B b f) = (term654 A B b f).
Proof. exact (fun_ext (fun n : nat => @lem3803458 A B b n f)). Qed.
Lemma lem3803460 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3803461 {A B : Type'} (b : B) (f : type1411 A B) : (term513 A B b f) = (term655 A B b f).
Proof. exact (MK_COMB (@lem3803460) (@lem3803459 A B b f)). Qed.
Lemma lem3803462 {A B : Type'} (f : type1411 A B) : (term606 A B f) = (term656 A B f).
Proof. exact (fun_ext (fun b : B => @lem3803461 A B b f)). Qed.
Lemma lem3803463 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3803464 {A B : Type'} (f : type1411 A B) : (term514 A B f) = (term657 A B f).
Proof. exact (MK_COMB (@lem3803463 B) (@lem3803462 A B f)). Qed.
Lemma lem3803623 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3803624 {B : Type'} (P : Prop) (Q : B -> Prop) : (term658 B P Q) = (term659 B P Q).
Proof. exact (@lem3803623 B P Q). Qed.
Lemma lem3803625 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term660 A B b s n z f x) = (term661 A B b s n z f x).
Proof. exact (@lem3803624 B (term662 A x s) (term198 A B b s n z f x)). Qed.
Lemma lem3803626 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) (w : B) : (term199 A B b s n z f x w) = (term200 A B b s n z f x w).
Proof. exact (eq_refl (term199 A B b s n z f x w)). Qed.
Lemma lem3803627 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term209 A B b s n z f x) = (term198 A B b s n z f x).
Proof. exact (fun_ext (fun w : B => @lem3803626 A B b s n z f x w)). Qed.
Lemma lem3803628 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3803629 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term210 A B b s n z f x) = (term211 A B b s n z f x).
Proof. exact (MK_COMB (@lem3803628 B) (@lem3803627 A B b s n z f x)). Qed.
Lemma lem3803630 {A : Type'} (x : A) (s : A -> Prop) : (term643 A x s) = (term643 A x s).
Proof. exact (eq_refl (term643 A x s)). Qed.
Lemma lem3803631 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term660 A B b s n z f x) = (term644 A B b s n z f x).
Proof. exact (MK_COMB (@lem3803630 A x s) (@lem3803629 A B b s n z f x)). Qed.
Lemma lem3803632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3803633 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term663 A B b s n z f x) = (term664 A B b s n z f x).
Proof. exact (MK_COMB (@lem3803632) (@lem3803631 A B b s n z f x)). Qed.
Lemma lem3803634 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) (w : B) : (term199 A B b s n z f x w) = (term200 A B b s n z f x w).
Proof. exact (eq_refl (term199 A B b s n z f x w)). Qed.
Lemma lem3803635 {A : Type'} (x : A) (s : A -> Prop) : (term643 A x s) = (term643 A x s).
Proof. exact (eq_refl (term643 A x s)). Qed.
Lemma lem3803636 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) (w : B) : (term665 A B b s n z f x w) = (term666 A B b s n z f x w).
Proof. exact (MK_COMB (@lem3803635 A x s) (@lem3803634 A B b s n z f x w)). Qed.
Lemma lem3803637 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term667 A B b s n z f x) = (term668 A B b s n z f x).
Proof. exact (fun_ext (fun w : B => @lem3803636 A B b s n z f x w)). Qed.
Lemma lem3803638 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3803639 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term661 A B b s n z f x) = (term669 A B b s n z f x).
Proof. exact (MK_COMB (@lem3803638 B) (@lem3803637 A B b s n z f x)). Qed.
Lemma lem3803640 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : ((term660 A B b s n z f x) = (term661 A B b s n z f x)) = ((term644 A B b s n z f x) = (term669 A B b s n z f x)).
Proof. exact (MK_COMB (@lem3803633 A B b s n z f x) (@lem3803639 A B b s n z f x)). Qed.
Lemma lem3803641 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term644 A B b s n z f x) = (term669 A B b s n z f x).
Proof. exact (EQ_MP (@lem3803640 A B b s n z f x) (@lem3803625 A B b s n z f x)). Qed.
Lemma lem3803642 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term645 A B b s n z f) = (term670 A B b s n z f).
Proof. exact (fun_ext (fun x : A => @lem3803641 A B b s n z f x)). Qed.
Lemma lem3803643 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3803644 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term646 A B b s n z f) = (term671 A B b s n z f).
Proof. exact (MK_COMB (@lem3803643 A) (@lem3803642 A B b s n z f)). Qed.
Lemma lem3803646 {A B : Type'} (P : type1413 A B) : (term672 A B P) = (term673 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3803647 {A B : Type'} (P : type1413 A B) : (term672 A B P) = (term673 A B P).
Proof. exact (@lem3803646 A B P). Qed.
Lemma lem3803648 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term674 A B b s n z f) = (term675 A B b s n z f).
Proof. exact (@lem3803647 A B (term676 A B b s n z f)). Qed.
Lemma lem3803649 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term677 A B b s n z f x) = (term668 A B b s n z f x).
Proof. exact (eq_refl (term677 A B b s n z f x)). Qed.
Lemma lem3803650 {B : Type'} (w : B) : w = w.
Proof. exact (eq_refl w). Qed.
Lemma lem3803651 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) (w : B) : (term678 A B b s n z f x w) = (term679 A B b s n z f x w).
Proof. exact (MK_COMB (@lem3803649 A B b s n z f x) (@lem3803650 B w)). Qed.
Lemma lem3803652 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) (w : B) : (term679 A B b s n z f x w) = (term666 A B b s n z f x w).
Proof. exact (eq_refl (term679 A B b s n z f x w)). Qed.
Lemma lem3803653 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) (w : B) : (term678 A B b s n z f x w) = (term666 A B b s n z f x w).
Proof. exact (TRANS (@lem3803651 A B b s n z f x w) (@lem3803652 A B b s n z f x w)). Qed.
Lemma lem3803654 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term680 A B b s n z f x) = (term668 A B b s n z f x).
Proof. exact (fun_ext (fun w : B => @lem3803653 A B b s n z f x w)). Qed.
Lemma lem3803655 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3803656 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term681 A B b s n z f x) = (term669 A B b s n z f x).
Proof. exact (MK_COMB (@lem3803655 B) (@lem3803654 A B b s n z f x)). Qed.
Lemma lem3803657 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term682 A B b s n z f) = (term670 A B b s n z f).
Proof. exact (fun_ext (fun x : A => @lem3803656 A B b s n z f x)). Qed.
Lemma lem3803658 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3803659 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term674 A B b s n z f) = (term671 A B b s n z f).
Proof. exact (MK_COMB (@lem3803658 A) (@lem3803657 A B b s n z f)). Qed.
Lemma lem3803660 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3803661 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term683 A B b s n z f) = (term684 A B b s n z f).
Proof. exact (MK_COMB (@lem3803660) (@lem3803659 A B b s n z f)). Qed.
Lemma lem3803662 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (x : A) : (term677 A B b s n z f x) = (term668 A B b s n z f x).
Proof. exact (eq_refl (term677 A B b s n z f x)). Qed.
Lemma lem3803663 {A B : Type'} (w : A -> B) (x : A) : (w x) = (w x).
Proof. exact (eq_refl (w x)). Qed.
Lemma lem3803664 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (w : A -> B) (x : A) : (term685 A B b s n z f w x) = (term686 A B b s n z f w x).
Proof. exact (MK_COMB (@lem3803662 A B b s n z f x) (@lem3803663 A B w x)). Qed.
Lemma lem3803665 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (w : A -> B) (x : A) : (term686 A B b s n z f w x) = (term687 A B b s n z f w x).
Proof. exact (eq_refl (term686 A B b s n z f w x)). Qed.
Lemma lem3803666 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (w : A -> B) (x : A) : (term685 A B b s n z f w x) = (term687 A B b s n z f w x).
Proof. exact (TRANS (@lem3803664 A B b s n z f w x) (@lem3803665 A B b s n z f w x)). Qed.
Lemma lem3803667 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (w : A -> B) : (term688 A B b s n z f w) = (term689 A B b s n z f w).
Proof. exact (fun_ext (fun x : A => @lem3803666 A B b s n z f w x)). Qed.
Lemma lem3803668 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3803669 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (w : A -> B) : (term690 A B b s n z f w) = (term691 A B b s n z f w).
Proof. exact (MK_COMB (@lem3803668 A) (@lem3803667 A B b s n z f w)). Qed.
Lemma lem3803670 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term692 A B b s n z f) = (term693 A B b s n z f).
Proof. exact (fun_ext (fun w : A -> B => @lem3803669 A B b s n z f w)). Qed.
Lemma lem3803671 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3803672 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term675 A B b s n z f) = (term694 A B b s n z f).
Proof. exact (MK_COMB (@lem3803671 A B) (@lem3803670 A B b s n z f)). Qed.
Lemma lem3803673 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : ((term674 A B b s n z f) = (term675 A B b s n z f)) = ((term671 A B b s n z f) = (term694 A B b s n z f)).
Proof. exact (MK_COMB (@lem3803661 A B b s n z f) (@lem3803672 A B b s n z f)). Qed.
Lemma lem3803674 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term671 A B b s n z f) = (term694 A B b s n z f).
Proof. exact (EQ_MP (@lem3803673 A B b s n z f) (@lem3803648 A B b s n z f)). Qed.
Lemma lem3803675 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term646 A B b s n z f) = (term694 A B b s n z f).
Proof. exact (TRANS (@lem3803644 A B b s n z f) (@lem3803674 A B b s n z f)). Qed.
Lemma lem3803676 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (z : B) (n : nat) : (term647 A B f b s z n) = (term647 A B f b s z n).
Proof. exact (eq_refl (term647 A B f b s z n)). Qed.
Lemma lem3803677 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term649 A B b s n z f) = (term695 A B b s n z f).
Proof. exact (MK_COMB (@lem3803676 A B f b s z n) (@lem3803675 A B b s n z f)). Qed.
Lemma lem3803679 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3803680 {A B : Type'} (P : Prop) (Q : type572 A B) : (term696 A B P Q) = (term697 A B P Q).
Proof. exact (@lem3803679 (A -> B) P Q). Qed.
Lemma lem3803681 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term698 A B b s n z f) = (term699 A B b s n z f).
Proof. exact (@lem3803680 A B (term700 A B f b s z n) (term693 A B b s n z f)). Qed.
Lemma lem3803682 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (w : A -> B) : (term701 A B b s n z f w) = (term691 A B b s n z f w).
Proof. exact (eq_refl (term701 A B b s n z f w)). Qed.
Lemma lem3803683 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term702 A B b s n z f) = (term693 A B b s n z f).
Proof. exact (fun_ext (fun w : A -> B => @lem3803682 A B b s n z f w)). Qed.
Lemma lem3803684 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3803685 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term703 A B b s n z f) = (term694 A B b s n z f).
Proof. exact (MK_COMB (@lem3803684 A B) (@lem3803683 A B b s n z f)). Qed.
Lemma lem3803686 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (z : B) (n : nat) : (term647 A B f b s z n) = (term647 A B f b s z n).
Proof. exact (eq_refl (term647 A B f b s z n)). Qed.
Lemma lem3803687 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term698 A B b s n z f) = (term695 A B b s n z f).
Proof. exact (MK_COMB (@lem3803686 A B f b s z n) (@lem3803685 A B b s n z f)). Qed.
Lemma lem3803688 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3803689 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term704 A B b s n z f) = (term705 A B b s n z f).
Proof. exact (MK_COMB (@lem3803688) (@lem3803687 A B b s n z f)). Qed.
Lemma lem3803690 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (w : A -> B) : (term701 A B b s n z f w) = (term691 A B b s n z f w).
Proof. exact (eq_refl (term701 A B b s n z f w)). Qed.
Lemma lem3803691 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (z : B) (n : nat) : (term647 A B f b s z n) = (term647 A B f b s z n).
Proof. exact (eq_refl (term647 A B f b s z n)). Qed.
Lemma lem3803692 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (w : A -> B) : (term706 A B b s n z f w) = (term707 A B b s n z f w).
Proof. exact (MK_COMB (@lem3803691 A B f b s z n) (@lem3803690 A B b s n z f w)). Qed.
Lemma lem3803693 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term708 A B b s n z f) = (term709 A B b s n z f).
Proof. exact (fun_ext (fun w : A -> B => @lem3803692 A B b s n z f w)). Qed.
Lemma lem3803694 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3803695 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term699 A B b s n z f) = (term710 A B b s n z f).
Proof. exact (MK_COMB (@lem3803694 A B) (@lem3803693 A B b s n z f)). Qed.
Lemma lem3803696 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : ((term698 A B b s n z f) = (term699 A B b s n z f)) = ((term695 A B b s n z f) = (term710 A B b s n z f)).
Proof. exact (MK_COMB (@lem3803689 A B b s n z f) (@lem3803695 A B b s n z f)). Qed.
Lemma lem3803697 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term695 A B b s n z f) = (term710 A B b s n z f).
Proof. exact (EQ_MP (@lem3803696 A B b s n z f) (@lem3803681 A B b s n z f)). Qed.
Lemma lem3803698 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term649 A B b s n z f) = (term710 A B b s n z f).
Proof. exact (TRANS (@lem3803677 A B b s n z f) (@lem3803697 A B b s n z f)). Qed.
Lemma lem3803699 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term650 A B b s n f) = (term711 A B b s n f).
Proof. exact (fun_ext (fun z : B => @lem3803698 A B b s n z f)). Qed.
Lemma lem3803700 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3803701 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term651 A B b s n f) = (term712 A B b s n f).
Proof. exact (MK_COMB (@lem3803700 B) (@lem3803699 A B b s n f)). Qed.
Lemma lem3803703 {A B : Type'} (P : type1413 A B) : (term672 A B P) = (term673 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3803704 {A B : Type'} (P : type1446 A B) : (term713 A B P) = (term714 A B P).
Proof. exact (@lem3803703 B (A -> B) P). Qed.
Lemma lem3803705 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term715 A B b s n f) = (term716 A B b s n f).
Proof. exact (@lem3803704 A B (term717 A B b s n f)). Qed.
Lemma lem3803706 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term718 A B b s n f z) = (term709 A B b s n z f).
Proof. exact (eq_refl (term718 A B b s n f z)). Qed.
Lemma lem3803707 {A B : Type'} (w : A -> B) : w = w.
Proof. exact (eq_refl w). Qed.
Lemma lem3803708 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (w : A -> B) : (term719 A B b s n f z w) = (term720 A B b s n z f w).
Proof. exact (MK_COMB (@lem3803706 A B b s n z f) (@lem3803707 A B w)). Qed.
Lemma lem3803709 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (w : A -> B) : (term720 A B b s n z f w) = (term707 A B b s n z f w).
Proof. exact (eq_refl (term720 A B b s n z f w)). Qed.
Lemma lem3803710 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) (w : A -> B) : (term719 A B b s n f z w) = (term707 A B b s n z f w).
Proof. exact (TRANS (@lem3803708 A B b s n z f w) (@lem3803709 A B b s n z f w)). Qed.
Lemma lem3803711 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term721 A B b s n f z) = (term709 A B b s n z f).
Proof. exact (fun_ext (fun w : A -> B => @lem3803710 A B b s n z f w)). Qed.
Lemma lem3803712 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3803713 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term722 A B b s n f z) = (term710 A B b s n z f).
Proof. exact (MK_COMB (@lem3803712 A B) (@lem3803711 A B b s n z f)). Qed.
Lemma lem3803714 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term723 A B b s n f) = (term711 A B b s n f).
Proof. exact (fun_ext (fun z : B => @lem3803713 A B b s n z f)). Qed.
Lemma lem3803715 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3803716 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term715 A B b s n f) = (term712 A B b s n f).
Proof. exact (MK_COMB (@lem3803715 B) (@lem3803714 A B b s n f)). Qed.
Lemma lem3803717 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3803718 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term724 A B b s n f) = (term725 A B b s n f).
Proof. exact (MK_COMB (@lem3803717) (@lem3803716 A B b s n f)). Qed.
Lemma lem3803719 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (z : B) (f : type1411 A B) : (term718 A B b s n f z) = (term709 A B b s n z f).
Proof. exact (eq_refl (term718 A B b s n f z)). Qed.
Lemma lem3803720 {A B : Type'} (w : type1468 A B) (z : B) : (w z) = (w z).
Proof. exact (eq_refl (w z)). Qed.
Lemma lem3803721 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) (w : type1468 A B) (z : B) : (term726 A B b s n f w z) = (term727 A B b s n f w z).
Proof. exact (MK_COMB (@lem3803719 A B b s n z f) (@lem3803720 A B w z)). Qed.
Lemma lem3803722 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) (w : type1468 A B) (z : B) : (term727 A B b s n f w z) = (term728 A B b s n f w z).
Proof. exact (eq_refl (term727 A B b s n f w z)). Qed.
Lemma lem3803723 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) (w : type1468 A B) (z : B) : (term726 A B b s n f w z) = (term728 A B b s n f w z).
Proof. exact (TRANS (@lem3803721 A B b s n f w z) (@lem3803722 A B b s n f w z)). Qed.
Lemma lem3803724 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) (w : type1468 A B) : (term729 A B b s n f w) = (term730 A B b s n f w).
Proof. exact (fun_ext (fun z : B => @lem3803723 A B b s n f w z)). Qed.
Lemma lem3803725 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3803726 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) (w : type1468 A B) : (term731 A B b s n f w) = (term732 A B b s n f w).
Proof. exact (MK_COMB (@lem3803725 B) (@lem3803724 A B b s n f w)). Qed.
Lemma lem3803727 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term733 A B b s n f) = (term734 A B b s n f).
Proof. exact (fun_ext (fun w : type1468 A B => @lem3803726 A B b s n f w)). Qed.
Lemma lem3803728 {A B : Type'} : (@ex (B -> A -> B)) = (@ex (B -> A -> B)).
Proof. exact (eq_refl (@ex (B -> A -> B))). Qed.
Lemma lem3803729 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term716 A B b s n f) = (term735 A B b s n f).
Proof. exact (MK_COMB (@lem3803728 A B) (@lem3803727 A B b s n f)). Qed.
Lemma lem3803730 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : ((term715 A B b s n f) = (term716 A B b s n f)) = ((term712 A B b s n f) = (term735 A B b s n f)).
Proof. exact (MK_COMB (@lem3803718 A B b s n f) (@lem3803729 A B b s n f)). Qed.
Lemma lem3803731 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term712 A B b s n f) = (term735 A B b s n f).
Proof. exact (EQ_MP (@lem3803730 A B b s n f) (@lem3803705 A B b s n f)). Qed.
Lemma lem3803732 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term651 A B b s n f) = (term735 A B b s n f).
Proof. exact (TRANS (@lem3803701 A B b s n f) (@lem3803731 A B b s n f)). Qed.
Lemma lem3803733 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term652 A B b n f) = (term736 A B b n f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3803732 A B b s n f)). Qed.
Lemma lem3803734 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3803735 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term653 A B b n f) = (term737 A B b n f).
Proof. exact (MK_COMB (@lem3803734 A) (@lem3803733 A B b n f)). Qed.
Lemma lem3803737 {A B : Type'} (P : type1413 A B) : (term672 A B P) = (term673 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3803738 {A B : Type'} (P : type648 A B) : (term738 A B P) = (term739 A B P).
Proof. exact (@lem3803737 (A -> Prop) (type1468 A B) P). Qed.
Lemma lem3803739 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term740 A B b n f) = (term741 A B b n f).
Proof. exact (@lem3803738 A B (term742 A B b n f)). Qed.
Lemma lem3803740 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term743 A B b n f s) = (term734 A B b s n f).
Proof. exact (eq_refl (term743 A B b n f s)). Qed.
Lemma lem3803741 {A B : Type'} (w : type1468 A B) : w = w.
Proof. exact (eq_refl w). Qed.
Lemma lem3803742 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) (w : type1468 A B) : (term744 A B b n f s w) = (term745 A B b s n f w).
Proof. exact (MK_COMB (@lem3803740 A B b s n f) (@lem3803741 A B w)). Qed.
Lemma lem3803743 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) (w : type1468 A B) : (term745 A B b s n f w) = (term732 A B b s n f w).
Proof. exact (eq_refl (term745 A B b s n f w)). Qed.
Lemma lem3803744 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) (w : type1468 A B) : (term744 A B b n f s w) = (term732 A B b s n f w).
Proof. exact (TRANS (@lem3803742 A B b s n f w) (@lem3803743 A B b s n f w)). Qed.
Lemma lem3803745 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term746 A B b n f s) = (term734 A B b s n f).
Proof. exact (fun_ext (fun w : type1468 A B => @lem3803744 A B b s n f w)). Qed.
Lemma lem3803746 {A B : Type'} : (@ex (B -> A -> B)) = (@ex (B -> A -> B)).
Proof. exact (eq_refl (@ex (B -> A -> B))). Qed.
Lemma lem3803747 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term747 A B b n f s) = (term735 A B b s n f).
Proof. exact (MK_COMB (@lem3803746 A B) (@lem3803745 A B b s n f)). Qed.
Lemma lem3803748 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term748 A B b n f) = (term736 A B b n f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3803747 A B b s n f)). Qed.
Lemma lem3803749 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3803750 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term740 A B b n f) = (term737 A B b n f).
Proof. exact (MK_COMB (@lem3803749 A) (@lem3803748 A B b n f)). Qed.
Lemma lem3803751 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3803752 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term749 A B b n f) = (term750 A B b n f).
Proof. exact (MK_COMB (@lem3803751) (@lem3803750 A B b n f)). Qed.
Lemma lem3803753 {A B : Type'} (b : B) (s : A -> Prop) (n : nat) (f : type1411 A B) : (term743 A B b n f s) = (term734 A B b s n f).
Proof. exact (eq_refl (term743 A B b n f s)). Qed.
Lemma lem3803754 {A B : Type'} (w : type675 A B) (s : A -> Prop) : (w s) = (w s).
Proof. exact (eq_refl (w s)). Qed.
Lemma lem3803755 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (w : type675 A B) (s : A -> Prop) : (term751 A B b n f w s) = (term752 A B b n f w s).
Proof. exact (MK_COMB (@lem3803753 A B b s n f) (@lem3803754 A B w s)). Qed.
Lemma lem3803756 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (w : type675 A B) (s : A -> Prop) : (term752 A B b n f w s) = (term753 A B b n f w s).
Proof. exact (eq_refl (term752 A B b n f w s)). Qed.
Lemma lem3803757 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (w : type675 A B) (s : A -> Prop) : (term751 A B b n f w s) = (term753 A B b n f w s).
Proof. exact (TRANS (@lem3803755 A B b n f w s) (@lem3803756 A B b n f w s)). Qed.
Lemma lem3803758 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (w : type675 A B) : (term754 A B b n f w) = (term755 A B b n f w).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3803757 A B b n f w s)). Qed.
Lemma lem3803759 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3803760 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (w : type675 A B) : (term756 A B b n f w) = (term757 A B b n f w).
Proof. exact (MK_COMB (@lem3803759 A) (@lem3803758 A B b n f w)). Qed.
Lemma lem3803761 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term758 A B b n f) = (term759 A B b n f).
Proof. exact (fun_ext (fun w : type675 A B => @lem3803760 A B b n f w)). Qed.
Lemma lem3803762 {A B : Type'} : (@ex ((A -> Prop) -> B -> A -> B)) = (@ex ((A -> Prop) -> B -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> B -> A -> B))). Qed.
Lemma lem3803763 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term741 A B b n f) = (term760 A B b n f).
Proof. exact (MK_COMB (@lem3803762 A B) (@lem3803761 A B b n f)). Qed.
Lemma lem3803764 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : ((term740 A B b n f) = (term741 A B b n f)) = ((term737 A B b n f) = (term760 A B b n f)).
Proof. exact (MK_COMB (@lem3803752 A B b n f) (@lem3803763 A B b n f)). Qed.
Lemma lem3803765 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term737 A B b n f) = (term760 A B b n f).
Proof. exact (EQ_MP (@lem3803764 A B b n f) (@lem3803739 A B b n f)). Qed.
Lemma lem3803766 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term653 A B b n f) = (term760 A B b n f).
Proof. exact (TRANS (@lem3803735 A B b n f) (@lem3803765 A B b n f)). Qed.
Lemma lem3803767 {A B : Type'} (b : B) (f : type1411 A B) : (term654 A B b f) = (term761 A B b f).
Proof. exact (fun_ext (fun n : nat => @lem3803766 A B b n f)). Qed.
Lemma lem3803768 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3803769 {A B : Type'} (b : B) (f : type1411 A B) : (term655 A B b f) = (term762 A B b f).
Proof. exact (MK_COMB (@lem3803768) (@lem3803767 A B b f)). Qed.
Lemma lem3803771 {A B : Type'} (P : type1413 A B) : (term672 A B P) = (term673 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3803772 {A B : Type'} (P : type1565 A B) : (term763 A B P) = (term764 A B P).
Proof. exact (@lem3803771 nat (type675 A B) P). Qed.
Lemma lem3803773 {A B : Type'} (b : B) (f : type1411 A B) : (term765 A B b f) = (term766 A B b f).
Proof. exact (@lem3803772 A B (term767 A B b f)). Qed.
Lemma lem3803774 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term768 A B b f n) = (term759 A B b n f).
Proof. exact (eq_refl (term768 A B b f n)). Qed.
Lemma lem3803775 {A B : Type'} (w : type675 A B) : w = w.
Proof. exact (eq_refl w). Qed.
Lemma lem3803776 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (w : type675 A B) : (term769 A B b f n w) = (term770 A B b n f w).
Proof. exact (MK_COMB (@lem3803774 A B b n f) (@lem3803775 A B w)). Qed.
Lemma lem3803777 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (w : type675 A B) : (term770 A B b n f w) = (term757 A B b n f w).
Proof. exact (eq_refl (term770 A B b n f w)). Qed.
Lemma lem3803778 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) (w : type675 A B) : (term769 A B b f n w) = (term757 A B b n f w).
Proof. exact (TRANS (@lem3803776 A B b n f w) (@lem3803777 A B b n f w)). Qed.
Lemma lem3803779 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term771 A B b f n) = (term759 A B b n f).
Proof. exact (fun_ext (fun w : type675 A B => @lem3803778 A B b n f w)). Qed.
Lemma lem3803780 {A B : Type'} : (@ex ((A -> Prop) -> B -> A -> B)) = (@ex ((A -> Prop) -> B -> A -> B)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> B -> A -> B))). Qed.
Lemma lem3803781 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term772 A B b f n) = (term760 A B b n f).
Proof. exact (MK_COMB (@lem3803780 A B) (@lem3803779 A B b n f)). Qed.
Lemma lem3803782 {A B : Type'} (b : B) (f : type1411 A B) : (term773 A B b f) = (term761 A B b f).
Proof. exact (fun_ext (fun n : nat => @lem3803781 A B b n f)). Qed.
Lemma lem3803783 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3803784 {A B : Type'} (b : B) (f : type1411 A B) : (term765 A B b f) = (term762 A B b f).
Proof. exact (MK_COMB (@lem3803783) (@lem3803782 A B b f)). Qed.
Lemma lem3803785 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3803786 {A B : Type'} (b : B) (f : type1411 A B) : (term774 A B b f) = (term775 A B b f).
Proof. exact (MK_COMB (@lem3803785) (@lem3803784 A B b f)). Qed.
Lemma lem3803787 {A B : Type'} (b : B) (n : nat) (f : type1411 A B) : (term768 A B b f n) = (term759 A B b n f).
Proof. exact (eq_refl (term768 A B b f n)). Qed.
Lemma lem3803788 {A B : Type'} (w : type1574 A B) (n : nat) : (w n) = (w n).
Proof. exact (eq_refl (w n)). Qed.
Lemma lem3803789 {A B : Type'} (b : B) (f : type1411 A B) (w : type1574 A B) (n : nat) : (term776 A B b f w n) = (term777 A B b f w n).
Proof. exact (MK_COMB (@lem3803787 A B b n f) (@lem3803788 A B w n)). Qed.
Lemma lem3803790 {A B : Type'} (b : B) (f : type1411 A B) (w : type1574 A B) (n : nat) : (term777 A B b f w n) = (term778 A B b f w n).
Proof. exact (eq_refl (term777 A B b f w n)). Qed.
Lemma lem3803791 {A B : Type'} (b : B) (f : type1411 A B) (w : type1574 A B) (n : nat) : (term776 A B b f w n) = (term778 A B b f w n).
Proof. exact (TRANS (@lem3803789 A B b f w n) (@lem3803790 A B b f w n)). Qed.
Lemma lem3803792 {A B : Type'} (b : B) (f : type1411 A B) (w : type1574 A B) : (term779 A B b f w) = (term780 A B b f w).
Proof. exact (fun_ext (fun n : nat => @lem3803791 A B b f w n)). Qed.
Lemma lem3803793 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3803794 {A B : Type'} (b : B) (f : type1411 A B) (w : type1574 A B) : (term781 A B b f w) = (term782 A B b f w).
Proof. exact (MK_COMB (@lem3803793) (@lem3803792 A B b f w)). Qed.
Lemma lem3803795 {A B : Type'} (b : B) (f : type1411 A B) : (term783 A B b f) = (term784 A B b f).
Proof. exact (fun_ext (fun w : type1574 A B => @lem3803794 A B b f w)). Qed.
Lemma lem3803796 {A B : Type'} : (@ex (nat -> (A -> Prop) -> B -> A -> B)) = (@ex (nat -> (A -> Prop) -> B -> A -> B)).
Proof. exact (eq_refl (@ex (nat -> (A -> Prop) -> B -> A -> B))). Qed.
Lemma lem3803797 {A B : Type'} (b : B) (f : type1411 A B) : (term766 A B b f) = (term785 A B b f).
Proof. exact (MK_COMB (@lem3803796 A B) (@lem3803795 A B b f)). Qed.
Lemma lem3803798 {A B : Type'} (b : B) (f : type1411 A B) : ((term765 A B b f) = (term766 A B b f)) = ((term762 A B b f) = (term785 A B b f)).
Proof. exact (MK_COMB (@lem3803786 A B b f) (@lem3803797 A B b f)). Qed.
Lemma lem3803799 {A B : Type'} (b : B) (f : type1411 A B) : (term762 A B b f) = (term785 A B b f).
Proof. exact (EQ_MP (@lem3803798 A B b f) (@lem3803773 A B b f)). Qed.
Lemma lem3803800 {A B : Type'} (b : B) (f : type1411 A B) : (term655 A B b f) = (term785 A B b f).
Proof. exact (TRANS (@lem3803769 A B b f) (@lem3803799 A B b f)). Qed.
Lemma lem3803801 {A B : Type'} (f : type1411 A B) : (term656 A B f) = (term786 A B f).
Proof. exact (fun_ext (fun b : B => @lem3803800 A B b f)). Qed.
Lemma lem3803802 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3803803 {A B : Type'} (f : type1411 A B) : (term657 A B f) = (term787 A B f).
Proof. exact (MK_COMB (@lem3803802 B) (@lem3803801 A B f)). Qed.
Lemma lem3803805 {A B : Type'} (P : type1413 A B) : (term672 A B P) = (term673 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3803806 {A B : Type'} (P : type1456 A B) : (term788 A B P) = (term789 A B P).
Proof. exact (@lem3803805 B (type1574 A B) P). Qed.
Lemma lem3803807 {A B : Type'} (f : type1411 A B) : (term790 A B f) = (term791 A B f).
Proof. exact (@lem3803806 A B (term792 A B f)). Qed.
Lemma lem3803808 {A B : Type'} (b : B) (f : type1411 A B) : (term793 A B f b) = (term784 A B b f).
Proof. exact (eq_refl (term793 A B f b)). Qed.
Lemma lem3803809 {A B : Type'} (w : type1574 A B) : w = w.
Proof. exact (eq_refl w). Qed.
Lemma lem3803810 {A B : Type'} (b : B) (f : type1411 A B) (w : type1574 A B) : (term794 A B f b w) = (term795 A B b f w).
Proof. exact (MK_COMB (@lem3803808 A B b f) (@lem3803809 A B w)). Qed.
Lemma lem3803811 {A B : Type'} (b : B) (f : type1411 A B) (w : type1574 A B) : (term795 A B b f w) = (term782 A B b f w).
Proof. exact (eq_refl (term795 A B b f w)). Qed.
Lemma lem3803812 {A B : Type'} (b : B) (f : type1411 A B) (w : type1574 A B) : (term794 A B f b w) = (term782 A B b f w).
Proof. exact (TRANS (@lem3803810 A B b f w) (@lem3803811 A B b f w)). Qed.
Lemma lem3803813 {A B : Type'} (b : B) (f : type1411 A B) : (term796 A B f b) = (term784 A B b f).
Proof. exact (fun_ext (fun w : type1574 A B => @lem3803812 A B b f w)). Qed.
Lemma lem3803814 {A B : Type'} : (@ex (nat -> (A -> Prop) -> B -> A -> B)) = (@ex (nat -> (A -> Prop) -> B -> A -> B)).
Proof. exact (eq_refl (@ex (nat -> (A -> Prop) -> B -> A -> B))). Qed.
Lemma lem3803815 {A B : Type'} (b : B) (f : type1411 A B) : (term797 A B f b) = (term785 A B b f).
Proof. exact (MK_COMB (@lem3803814 A B) (@lem3803813 A B b f)). Qed.
Lemma lem3803816 {A B : Type'} (f : type1411 A B) : (term798 A B f) = (term786 A B f).
Proof. exact (fun_ext (fun b : B => @lem3803815 A B b f)). Qed.
Lemma lem3803817 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3803818 {A B : Type'} (f : type1411 A B) : (term790 A B f) = (term787 A B f).
Proof. exact (MK_COMB (@lem3803817 B) (@lem3803816 A B f)). Qed.
Lemma lem3803819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3803820 {A B : Type'} (f : type1411 A B) : (term799 A B f) = (term800 A B f).
Proof. exact (MK_COMB (@lem3803819) (@lem3803818 A B f)). Qed.
Lemma lem3803821 {A B : Type'} (b : B) (f : type1411 A B) : (term793 A B f b) = (term784 A B b f).
Proof. exact (eq_refl (term793 A B f b)). Qed.
Lemma lem3803822 {A B : Type'} (w : type1476 A B) (b : B) : (w b) = (w b).
Proof. exact (eq_refl (w b)). Qed.
Lemma lem3803823 {A B : Type'} (f : type1411 A B) (w : type1476 A B) (b : B) : (term801 A B f w b) = (term802 A B f w b).
Proof. exact (MK_COMB (@lem3803821 A B b f) (@lem3803822 A B w b)). Qed.
Lemma lem3803824 {A B : Type'} (f : type1411 A B) (w : type1476 A B) (b : B) : (term802 A B f w b) = (term803 A B f w b).
Proof. exact (eq_refl (term802 A B f w b)). Qed.
Lemma lem3803825 {A B : Type'} (f : type1411 A B) (w : type1476 A B) (b : B) : (term801 A B f w b) = (term803 A B f w b).
Proof. exact (TRANS (@lem3803823 A B f w b) (@lem3803824 A B f w b)). Qed.
Lemma lem3803826 {A B : Type'} (f : type1411 A B) (w : type1476 A B) : (term804 A B f w) = (term805 A B f w).
Proof. exact (fun_ext (fun b : B => @lem3803825 A B f w b)). Qed.
Lemma lem3803827 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3803828 {A B : Type'} (f : type1411 A B) (w : type1476 A B) : (term806 A B f w) = (term807 A B f w).
Proof. exact (MK_COMB (@lem3803827 B) (@lem3803826 A B f w)). Qed.
Lemma lem3803829 {A B : Type'} (f : type1411 A B) : (term808 A B f) = (term809 A B f).
Proof. exact (fun_ext (fun w : type1476 A B => @lem3803828 A B f w)). Qed.
Lemma lem3803830 {A B : Type'} : (@ex (B -> nat -> (A -> Prop) -> B -> A -> B)) = (@ex (B -> nat -> (A -> Prop) -> B -> A -> B)).
Proof. exact (eq_refl (@ex (B -> nat -> (A -> Prop) -> B -> A -> B))). Qed.
Lemma lem3803831 {A B : Type'} (f : type1411 A B) : (term791 A B f) = (term810 A B f).
Proof. exact (MK_COMB (@lem3803830 A B) (@lem3803829 A B f)). Qed.
Lemma lem3803832 {A B : Type'} (f : type1411 A B) : ((term790 A B f) = (term791 A B f)) = ((term787 A B f) = (term810 A B f)).
Proof. exact (MK_COMB (@lem3803820 A B f) (@lem3803831 A B f)). Qed.
Lemma lem3803833 {A B : Type'} (f : type1411 A B) : (term787 A B f) = (term810 A B f).
Proof. exact (EQ_MP (@lem3803832 A B f) (@lem3803807 A B f)). Qed.
Lemma lem3803835 {A B : Type'} (f : type1411 A B) : (term657 A B f) = (term810 A B f).
Proof. exact (TRANS (@lem3803803 A B f) (@lem3803833 A B f)). Qed.
Lemma lem3803836 {A B : Type'} (f : type1411 A B) : (term514 A B f) = (term810 A B f).
Proof. exact (TRANS (@lem3803464 A B f) (@lem3803835 A B f)). Qed.
Lemma lem3803837 {A B : Type'} (f : type1411 A B) (h1 : term514 A B f) : term810 A B f.
Proof. exact (EQ_MP (@lem3803836 A B f) (@lem3803126 A B f h1)). Qed.
Lemma lem3803843 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (w : B) : (term200 A B b s n1 a1 f x w) = (term200 A B b s n1 a1 f x w).
Proof. exact (eq_refl (term200 A B b s n1 a1 f x w)). Qed.
Lemma lem3803844 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term198 A B b s n1 a1 f x) = (term198 A B b s n1 a1 f x).
Proof. exact (fun_ext (fun w : B => @lem3803843 A B b s n1 a1 f x w)). Qed.
Lemma lem3803845 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3803846 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term211 A B b s n1 a1 f x) = (term211 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3803845 B) (@lem3803844 A B b s n1 a1 f x)). Qed.
Lemma lem3803848 {A : Type'} (x : A) (s : A -> Prop) : (term643 A x s) = (term643 A x s).
Proof. exact (eq_refl (term643 A x s)). Qed.
Lemma lem3803849 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term644 A B b s n1 a1 f x) = (term644 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3803848 A x s) (@lem3803846 A B b s n1 a1 f x)). Qed.
Lemma lem3803850 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term601 A B b s n1 a1 f x) = (term644 A B b s n1 a1 f x).
Proof. exact (@lem17265 (@IN A x s) (term211 A B b s n1 a1 f x)). Qed.
Lemma lem3803851 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term601 A B b s n1 a1 f x) = (term644 A B b s n1 a1 f x).
Proof. exact (TRANS (@lem3803850 A B b s n1 a1 f x) (@lem3803849 A B b s n1 a1 f x)). Qed.
Lemma lem3803852 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term602 A B b s n1 a1 f) = (term645 A B b s n1 a1 f).
Proof. exact (fun_ext (fun x : A => @lem3803851 A B b s n1 a1 f x)). Qed.
Lemma lem3803853 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3803854 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term527 A B b s n1 a1 f) = (term646 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3803853 A) (@lem3803852 A B b s n1 a1 f)). Qed.
Lemma lem3803953 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3803954 {B : Type'} (P : Prop) (Q : B -> Prop) : (term658 B P Q) = (term659 B P Q).
Proof. exact (@lem3803953 B P Q). Qed.
Lemma lem3803955 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term660 A B b s n1 a1 f x) = (term661 A B b s n1 a1 f x).
Proof. exact (@lem3803954 B (term662 A x s) (term198 A B b s n1 a1 f x)). Qed.
Lemma lem3803956 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (w : B) : (term199 A B b s n1 a1 f x w) = (term200 A B b s n1 a1 f x w).
Proof. exact (eq_refl (term199 A B b s n1 a1 f x w)). Qed.
Lemma lem3803957 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term209 A B b s n1 a1 f x) = (term198 A B b s n1 a1 f x).
Proof. exact (fun_ext (fun w : B => @lem3803956 A B b s n1 a1 f x w)). Qed.
Lemma lem3803958 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3803959 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term210 A B b s n1 a1 f x) = (term211 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3803958 B) (@lem3803957 A B b s n1 a1 f x)). Qed.
Lemma lem3803960 {A : Type'} (x : A) (s : A -> Prop) : (term643 A x s) = (term643 A x s).
Proof. exact (eq_refl (term643 A x s)). Qed.
Lemma lem3803961 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term660 A B b s n1 a1 f x) = (term644 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3803960 A x s) (@lem3803959 A B b s n1 a1 f x)). Qed.
Lemma lem3803962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3803963 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term663 A B b s n1 a1 f x) = (term664 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3803962) (@lem3803961 A B b s n1 a1 f x)). Qed.
Lemma lem3803964 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (w : B) : (term199 A B b s n1 a1 f x w) = (term200 A B b s n1 a1 f x w).
Proof. exact (eq_refl (term199 A B b s n1 a1 f x w)). Qed.
Lemma lem3803965 {A : Type'} (x : A) (s : A -> Prop) : (term643 A x s) = (term643 A x s).
Proof. exact (eq_refl (term643 A x s)). Qed.
Lemma lem3803966 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (w : B) : (term665 A B b s n1 a1 f x w) = (term666 A B b s n1 a1 f x w).
Proof. exact (MK_COMB (@lem3803965 A x s) (@lem3803964 A B b s n1 a1 f x w)). Qed.
Lemma lem3803967 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term667 A B b s n1 a1 f x) = (term668 A B b s n1 a1 f x).
Proof. exact (fun_ext (fun w : B => @lem3803966 A B b s n1 a1 f x w)). Qed.
Lemma lem3803968 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3803969 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term661 A B b s n1 a1 f x) = (term669 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3803968 B) (@lem3803967 A B b s n1 a1 f x)). Qed.
Lemma lem3803970 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : ((term660 A B b s n1 a1 f x) = (term661 A B b s n1 a1 f x)) = ((term644 A B b s n1 a1 f x) = (term669 A B b s n1 a1 f x)).
Proof. exact (MK_COMB (@lem3803963 A B b s n1 a1 f x) (@lem3803969 A B b s n1 a1 f x)). Qed.
Lemma lem3803971 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term644 A B b s n1 a1 f x) = (term669 A B b s n1 a1 f x).
Proof. exact (EQ_MP (@lem3803970 A B b s n1 a1 f x) (@lem3803955 A B b s n1 a1 f x)). Qed.
Lemma lem3803972 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term645 A B b s n1 a1 f) = (term670 A B b s n1 a1 f).
Proof. exact (fun_ext (fun x : A => @lem3803971 A B b s n1 a1 f x)). Qed.
Lemma lem3803973 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3803974 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term646 A B b s n1 a1 f) = (term671 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3803973 A) (@lem3803972 A B b s n1 a1 f)). Qed.
Lemma lem3803976 {A B : Type'} (P : type1413 A B) : (term672 A B P) = (term673 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3803977 {A B : Type'} (P : type1413 A B) : (term672 A B P) = (term673 A B P).
Proof. exact (@lem3803976 A B P). Qed.
Lemma lem3803978 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term674 A B b s n1 a1 f) = (term675 A B b s n1 a1 f).
Proof. exact (@lem3803977 A B (term676 A B b s n1 a1 f)). Qed.
Lemma lem3803979 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term677 A B b s n1 a1 f x) = (term668 A B b s n1 a1 f x).
Proof. exact (eq_refl (term677 A B b s n1 a1 f x)). Qed.
Lemma lem3803980 {B : Type'} (w : B) : w = w.
Proof. exact (eq_refl w). Qed.
Lemma lem3803981 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (w : B) : (term678 A B b s n1 a1 f x w) = (term679 A B b s n1 a1 f x w).
Proof. exact (MK_COMB (@lem3803979 A B b s n1 a1 f x) (@lem3803980 B w)). Qed.
Lemma lem3803982 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (w : B) : (term679 A B b s n1 a1 f x w) = (term666 A B b s n1 a1 f x w).
Proof. exact (eq_refl (term679 A B b s n1 a1 f x w)). Qed.
Lemma lem3803983 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (w : B) : (term678 A B b s n1 a1 f x w) = (term666 A B b s n1 a1 f x w).
Proof. exact (TRANS (@lem3803981 A B b s n1 a1 f x w) (@lem3803982 A B b s n1 a1 f x w)). Qed.
Lemma lem3803984 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term680 A B b s n1 a1 f x) = (term668 A B b s n1 a1 f x).
Proof. exact (fun_ext (fun w : B => @lem3803983 A B b s n1 a1 f x w)). Qed.
Lemma lem3803985 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3803986 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term681 A B b s n1 a1 f x) = (term669 A B b s n1 a1 f x).
Proof. exact (MK_COMB (@lem3803985 B) (@lem3803984 A B b s n1 a1 f x)). Qed.
Lemma lem3803987 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term682 A B b s n1 a1 f) = (term670 A B b s n1 a1 f).
Proof. exact (fun_ext (fun x : A => @lem3803986 A B b s n1 a1 f x)). Qed.
Lemma lem3803988 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3803989 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term674 A B b s n1 a1 f) = (term671 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3803988 A) (@lem3803987 A B b s n1 a1 f)). Qed.
Lemma lem3803990 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3803991 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term683 A B b s n1 a1 f) = (term684 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3803990) (@lem3803989 A B b s n1 a1 f)). Qed.
Lemma lem3803992 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) : (term677 A B b s n1 a1 f x) = (term668 A B b s n1 a1 f x).
Proof. exact (eq_refl (term677 A B b s n1 a1 f x)). Qed.
Lemma lem3803993 {A B : Type'} (w : A -> B) (x : A) : (w x) = (w x).
Proof. exact (eq_refl (w x)). Qed.
Lemma lem3803994 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (w : A -> B) (x : A) : (term685 A B b s n1 a1 f w x) = (term686 A B b s n1 a1 f w x).
Proof. exact (MK_COMB (@lem3803992 A B b s n1 a1 f x) (@lem3803993 A B w x)). Qed.
Lemma lem3803995 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (w : A -> B) (x : A) : (term686 A B b s n1 a1 f w x) = (term687 A B b s n1 a1 f w x).
Proof. exact (eq_refl (term686 A B b s n1 a1 f w x)). Qed.
Lemma lem3803996 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (w : A -> B) (x : A) : (term685 A B b s n1 a1 f w x) = (term687 A B b s n1 a1 f w x).
Proof. exact (TRANS (@lem3803994 A B b s n1 a1 f w x) (@lem3803995 A B b s n1 a1 f w x)). Qed.
Lemma lem3803997 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (w : A -> B) : (term688 A B b s n1 a1 f w) = (term689 A B b s n1 a1 f w).
Proof. exact (fun_ext (fun x : A => @lem3803996 A B b s n1 a1 f w x)). Qed.
Lemma lem3803998 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3803999 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (w : A -> B) : (term690 A B b s n1 a1 f w) = (term691 A B b s n1 a1 f w).
Proof. exact (MK_COMB (@lem3803998 A) (@lem3803997 A B b s n1 a1 f w)). Qed.
Lemma lem3804000 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term692 A B b s n1 a1 f) = (term693 A B b s n1 a1 f).
Proof. exact (fun_ext (fun w : A -> B => @lem3803999 A B b s n1 a1 f w)). Qed.
Lemma lem3804001 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3804002 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term675 A B b s n1 a1 f) = (term694 A B b s n1 a1 f).
Proof. exact (MK_COMB (@lem3804001 A B) (@lem3804000 A B b s n1 a1 f)). Qed.
Lemma lem3804003 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : ((term674 A B b s n1 a1 f) = (term675 A B b s n1 a1 f)) = ((term671 A B b s n1 a1 f) = (term694 A B b s n1 a1 f)).
Proof. exact (MK_COMB (@lem3803991 A B b s n1 a1 f) (@lem3804002 A B b s n1 a1 f)). Qed.
Lemma lem3804004 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term671 A B b s n1 a1 f) = (term694 A B b s n1 a1 f).
Proof. exact (EQ_MP (@lem3804003 A B b s n1 a1 f) (@lem3803978 A B b s n1 a1 f)). Qed.
Lemma lem3804006 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term646 A B b s n1 a1 f) = (term694 A B b s n1 a1 f).
Proof. exact (TRANS (@lem3803974 A B b s n1 a1 f) (@lem3804004 A B b s n1 a1 f)). Qed.
Lemma lem3804007 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) : (term527 A B b s n1 a1 f) = (term694 A B b s n1 a1 f).
Proof. exact (TRANS (@lem3803854 A B b s n1 a1 f) (@lem3804006 A B b s n1 a1 f)). Qed.
Lemma lem3804008 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (h1 : term527 A B b s n1 a1 f) : term694 A B b s n1 a1 f.
Proof. exact (EQ_MP (@lem3804007 A B b s n1 a1 f) (@lem3803127 A B b s n1 a1 f h1)). Qed.
Lemma lem3804014 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (w : B) : (term200 A B b s n2 a2 f x w) = (term200 A B b s n2 a2 f x w).
Proof. exact (eq_refl (term200 A B b s n2 a2 f x w)). Qed.
Lemma lem3804015 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term198 A B b s n2 a2 f x) = (term198 A B b s n2 a2 f x).
Proof. exact (fun_ext (fun w : B => @lem3804014 A B b s n2 a2 f x w)). Qed.
Lemma lem3804016 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3804017 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term211 A B b s n2 a2 f x) = (term211 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3804016 B) (@lem3804015 A B b s n2 a2 f x)). Qed.
Lemma lem3804019 {A : Type'} (x : A) (s : A -> Prop) : (term643 A x s) = (term643 A x s).
Proof. exact (eq_refl (term643 A x s)). Qed.
Lemma lem3804020 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term644 A B b s n2 a2 f x) = (term644 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3804019 A x s) (@lem3804017 A B b s n2 a2 f x)). Qed.
Lemma lem3804021 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term601 A B b s n2 a2 f x) = (term644 A B b s n2 a2 f x).
Proof. exact (@lem17265 (@IN A x s) (term211 A B b s n2 a2 f x)). Qed.
Lemma lem3804022 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term601 A B b s n2 a2 f x) = (term644 A B b s n2 a2 f x).
Proof. exact (TRANS (@lem3804021 A B b s n2 a2 f x) (@lem3804020 A B b s n2 a2 f x)). Qed.
Lemma lem3804023 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term602 A B b s n2 a2 f) = (term645 A B b s n2 a2 f).
Proof. exact (fun_ext (fun x : A => @lem3804022 A B b s n2 a2 f x)). Qed.
Lemma lem3804024 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3804025 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term527 A B b s n2 a2 f) = (term646 A B b s n2 a2 f).
Proof. exact (MK_COMB (@lem3804024 A) (@lem3804023 A B b s n2 a2 f)). Qed.
Lemma lem3804124 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3804125 {B : Type'} (P : Prop) (Q : B -> Prop) : (term658 B P Q) = (term659 B P Q).
Proof. exact (@lem3804124 B P Q). Qed.
Lemma lem3804126 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term660 A B b s n2 a2 f x) = (term661 A B b s n2 a2 f x).
Proof. exact (@lem3804125 B (term662 A x s) (term198 A B b s n2 a2 f x)). Qed.
Lemma lem3804127 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (w : B) : (term199 A B b s n2 a2 f x w) = (term200 A B b s n2 a2 f x w).
Proof. exact (eq_refl (term199 A B b s n2 a2 f x w)). Qed.
Lemma lem3804128 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term209 A B b s n2 a2 f x) = (term198 A B b s n2 a2 f x).
Proof. exact (fun_ext (fun w : B => @lem3804127 A B b s n2 a2 f x w)). Qed.
Lemma lem3804129 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3804130 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term210 A B b s n2 a2 f x) = (term211 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3804129 B) (@lem3804128 A B b s n2 a2 f x)). Qed.
Lemma lem3804131 {A : Type'} (x : A) (s : A -> Prop) : (term643 A x s) = (term643 A x s).
Proof. exact (eq_refl (term643 A x s)). Qed.
Lemma lem3804132 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term660 A B b s n2 a2 f x) = (term644 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3804131 A x s) (@lem3804130 A B b s n2 a2 f x)). Qed.
Lemma lem3804133 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3804134 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term663 A B b s n2 a2 f x) = (term664 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3804133) (@lem3804132 A B b s n2 a2 f x)). Qed.
Lemma lem3804135 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (w : B) : (term199 A B b s n2 a2 f x w) = (term200 A B b s n2 a2 f x w).
Proof. exact (eq_refl (term199 A B b s n2 a2 f x w)). Qed.
Lemma lem3804136 {A : Type'} (x : A) (s : A -> Prop) : (term643 A x s) = (term643 A x s).
Proof. exact (eq_refl (term643 A x s)). Qed.
Lemma lem3804137 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (w : B) : (term665 A B b s n2 a2 f x w) = (term666 A B b s n2 a2 f x w).
Proof. exact (MK_COMB (@lem3804136 A x s) (@lem3804135 A B b s n2 a2 f x w)). Qed.
Lemma lem3804138 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term667 A B b s n2 a2 f x) = (term668 A B b s n2 a2 f x).
Proof. exact (fun_ext (fun w : B => @lem3804137 A B b s n2 a2 f x w)). Qed.
Lemma lem3804139 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3804140 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term661 A B b s n2 a2 f x) = (term669 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3804139 B) (@lem3804138 A B b s n2 a2 f x)). Qed.
Lemma lem3804141 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : ((term660 A B b s n2 a2 f x) = (term661 A B b s n2 a2 f x)) = ((term644 A B b s n2 a2 f x) = (term669 A B b s n2 a2 f x)).
Proof. exact (MK_COMB (@lem3804134 A B b s n2 a2 f x) (@lem3804140 A B b s n2 a2 f x)). Qed.
Lemma lem3804142 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term644 A B b s n2 a2 f x) = (term669 A B b s n2 a2 f x).
Proof. exact (EQ_MP (@lem3804141 A B b s n2 a2 f x) (@lem3804126 A B b s n2 a2 f x)). Qed.
Lemma lem3804143 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term645 A B b s n2 a2 f) = (term670 A B b s n2 a2 f).
Proof. exact (fun_ext (fun x : A => @lem3804142 A B b s n2 a2 f x)). Qed.
Lemma lem3804144 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3804145 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term646 A B b s n2 a2 f) = (term671 A B b s n2 a2 f).
Proof. exact (MK_COMB (@lem3804144 A) (@lem3804143 A B b s n2 a2 f)). Qed.
Lemma lem3804147 {A B : Type'} (P : type1413 A B) : (term672 A B P) = (term673 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3804148 {A B : Type'} (P : type1413 A B) : (term672 A B P) = (term673 A B P).
Proof. exact (@lem3804147 A B P). Qed.
Lemma lem3804149 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term674 A B b s n2 a2 f) = (term675 A B b s n2 a2 f).
Proof. exact (@lem3804148 A B (term676 A B b s n2 a2 f)). Qed.
Lemma lem3804150 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term677 A B b s n2 a2 f x) = (term668 A B b s n2 a2 f x).
Proof. exact (eq_refl (term677 A B b s n2 a2 f x)). Qed.
Lemma lem3804151 {B : Type'} (w : B) : w = w.
Proof. exact (eq_refl w). Qed.
Lemma lem3804152 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (w : B) : (term678 A B b s n2 a2 f x w) = (term679 A B b s n2 a2 f x w).
Proof. exact (MK_COMB (@lem3804150 A B b s n2 a2 f x) (@lem3804151 B w)). Qed.
Lemma lem3804153 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (w : B) : (term679 A B b s n2 a2 f x w) = (term666 A B b s n2 a2 f x w).
Proof. exact (eq_refl (term679 A B b s n2 a2 f x w)). Qed.
Lemma lem3804154 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) (w : B) : (term678 A B b s n2 a2 f x w) = (term666 A B b s n2 a2 f x w).
Proof. exact (TRANS (@lem3804152 A B b s n2 a2 f x w) (@lem3804153 A B b s n2 a2 f x w)). Qed.
Lemma lem3804155 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term680 A B b s n2 a2 f x) = (term668 A B b s n2 a2 f x).
Proof. exact (fun_ext (fun w : B => @lem3804154 A B b s n2 a2 f x w)). Qed.
Lemma lem3804156 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem3804157 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term681 A B b s n2 a2 f x) = (term669 A B b s n2 a2 f x).
Proof. exact (MK_COMB (@lem3804156 B) (@lem3804155 A B b s n2 a2 f x)). Qed.
Lemma lem3804158 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term682 A B b s n2 a2 f) = (term670 A B b s n2 a2 f).
Proof. exact (fun_ext (fun x : A => @lem3804157 A B b s n2 a2 f x)). Qed.
Lemma lem3804159 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3804160 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term674 A B b s n2 a2 f) = (term671 A B b s n2 a2 f).
Proof. exact (MK_COMB (@lem3804159 A) (@lem3804158 A B b s n2 a2 f)). Qed.
Lemma lem3804161 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3804162 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term683 A B b s n2 a2 f) = (term684 A B b s n2 a2 f).
Proof. exact (MK_COMB (@lem3804161) (@lem3804160 A B b s n2 a2 f)). Qed.
Lemma lem3804163 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (x : A) : (term677 A B b s n2 a2 f x) = (term668 A B b s n2 a2 f x).
Proof. exact (eq_refl (term677 A B b s n2 a2 f x)). Qed.
Lemma lem3804164 {A B : Type'} (w : A -> B) (x : A) : (w x) = (w x).
Proof. exact (eq_refl (w x)). Qed.
Lemma lem3804165 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) : (term685 A B b s n2 a2 f w x) = (term686 A B b s n2 a2 f w x).
Proof. exact (MK_COMB (@lem3804163 A B b s n2 a2 f x) (@lem3804164 A B w x)). Qed.
Lemma lem3804166 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) : (term686 A B b s n2 a2 f w x) = (term687 A B b s n2 a2 f w x).
Proof. exact (eq_refl (term686 A B b s n2 a2 f w x)). Qed.
Lemma lem3804167 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) : (term685 A B b s n2 a2 f w x) = (term687 A B b s n2 a2 f w x).
Proof. exact (TRANS (@lem3804165 A B b s n2 a2 f w x) (@lem3804166 A B b s n2 a2 f w x)). Qed.
Lemma lem3804168 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) : (term688 A B b s n2 a2 f w) = (term689 A B b s n2 a2 f w).
Proof. exact (fun_ext (fun x : A => @lem3804167 A B b s n2 a2 f w x)). Qed.
Lemma lem3804169 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3804170 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) : (term690 A B b s n2 a2 f w) = (term691 A B b s n2 a2 f w).
Proof. exact (MK_COMB (@lem3804169 A) (@lem3804168 A B b s n2 a2 f w)). Qed.
Lemma lem3804171 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term692 A B b s n2 a2 f) = (term693 A B b s n2 a2 f).
Proof. exact (fun_ext (fun w : A -> B => @lem3804170 A B b s n2 a2 f w)). Qed.
Lemma lem3804172 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3804173 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term675 A B b s n2 a2 f) = (term694 A B b s n2 a2 f).
Proof. exact (MK_COMB (@lem3804172 A B) (@lem3804171 A B b s n2 a2 f)). Qed.
Lemma lem3804174 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : ((term674 A B b s n2 a2 f) = (term675 A B b s n2 a2 f)) = ((term671 A B b s n2 a2 f) = (term694 A B b s n2 a2 f)).
Proof. exact (MK_COMB (@lem3804162 A B b s n2 a2 f) (@lem3804173 A B b s n2 a2 f)). Qed.
Lemma lem3804175 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term671 A B b s n2 a2 f) = (term694 A B b s n2 a2 f).
Proof. exact (EQ_MP (@lem3804174 A B b s n2 a2 f) (@lem3804149 A B b s n2 a2 f)). Qed.
Lemma lem3804177 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term646 A B b s n2 a2 f) = (term694 A B b s n2 a2 f).
Proof. exact (TRANS (@lem3804145 A B b s n2 a2 f) (@lem3804175 A B b s n2 a2 f)). Qed.
Lemma lem3804178 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) : (term527 A B b s n2 a2 f) = (term694 A B b s n2 a2 f).
Proof. exact (TRANS (@lem3804025 A B b s n2 a2 f) (@lem3804177 A B b s n2 a2 f)). Qed.
Lemma lem3804179 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (h1 : term527 A B b s n2 a2 f) : term694 A B b s n2 a2 f.
Proof. exact (EQ_MP (@lem3804178 A B b s n2 a2 f) (@lem3803128 A B b s n2 a2 f h1)). Qed.
Lemma lem3804185 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3804191 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term533 A B f b s x c n1) : term533 A B f b s x c n1.
Proof. exact (h1). Qed.
Lemma lem3804197 {A B : Type'} (a1 : B) (f : type1411 A B) (x : A) (c : B) (h1 : a1 = (f x c)) : a1 = (f x c).
Proof. exact (h1). Qed.
Lemma lem3804208 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term535 B a1 a2 n1 n2) = (term811 B a1 a2 n1 n2).
Proof. exact (@lem17045 (a1 = a2) ((S n1) = (S n2))). Qed.
Lemma lem3804210 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term691 A B b s n2 a2 f w.
Proof. exact (h1). Qed.
Lemma lem3804342 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term633 A B f b s a1 a2 n1 n2) = (term633 A B f b s a1 a2 n1 n2).
Proof. exact (eq_refl (term633 A B f b s a1 a2 n1 n2)). Qed.
Lemma lem3804343 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) (n2 : nat) : (term635 A B f b s a1 n1 n2) = (term635 A B f b s a1 n1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3804342 A B f b s a1 a2 n1 n2)). Qed.
Lemma lem3804344 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3804345 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) (n2 : nat) : (term636 A B f b s a1 n1 n2) = (term636 A B f b s a1 n1 n2).
Proof. exact (MK_COMB (@lem3804344 B) (@lem3804343 A B f b s a1 n1 n2)). Qed.
Lemma lem3804346 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term637 A B f b s n1 n2) = (term637 A B f b s n1 n2).
Proof. exact (fun_ext (fun a1 : B => @lem3804345 A B f b s a1 n1 n2)). Qed.
Lemma lem3804347 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3804348 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term638 A B f b s n1 n2) = (term638 A B f b s n1 n2).
Proof. exact (MK_COMB (@lem3804347 B) (@lem3804346 A B f b s n1 n2)). Qed.
Lemma lem3804349 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term639 A B f b n1 n2) = (term639 A B f b n1 n2).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3804348 A B f b s n1 n2)). Qed.
Lemma lem3804350 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3804351 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term640 A B f b n1 n2) = (term640 A B f b n1 n2).
Proof. exact (MK_COMB (@lem3804350 A) (@lem3804349 A B f b n1 n2)). Qed.
Lemma lem3804352 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term641 A B f b n1) = (term641 A B f b n1).
Proof. exact (fun_ext (fun n2 : nat => @lem3804351 A B f b n1 n2)). Qed.
Lemma lem3804353 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3804354 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term642 A B f b n1) = (term642 A B f b n1).
Proof. exact (MK_COMB (@lem3804353) (@lem3804352 A B f b n1)). Qed.
Lemma lem3804355 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term642 A B f b n1.
Proof. exact (EQ_MP (@lem3804354 A B f b n1) (@lem3803342 A B f b n1 h1)). Qed.
Lemma lem3804420 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3804436 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term533 A B f b s x c n1) : term533 A B f b s x c n1.
Proof. exact (h1). Qed.
Lemma lem3804445 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3804446 {A B : Type'} (f : type1411 A B) (x : A) : (f x) = (@I (A -> B -> B) f x).
Proof. exact (@lem3804445 A (B -> B) f x). Qed.
Lemma lem3804447 {B : Type'} (c : B) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem3804448 {A B : Type'} (f : type1411 A B) (x : A) (c : B) : (f x c) = (@I (A -> B -> B) f x c).
Proof. exact (MK_COMB (@lem3804446 A B f x) (@lem3804447 B c)). Qed.
Lemma lem3804450 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3804451 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem3804450 B B f x). Qed.
Lemma lem3804452 {A B : Type'} (f : type1411 A B) (x : A) (c : B) : (@I (A -> B -> B) f x c) = (term337 A B f x c).
Proof. exact (@lem3804451 B (@I (A -> B -> B) f x) c). Qed.
Lemma lem3804454 {A B : Type'} (f : type1411 A B) (x : A) (c : B) : (f x c) = (term337 A B f x c).
Proof. exact (TRANS (@lem3804448 A B f x c) (@lem3804452 A B f x c)). Qed.
Lemma lem3804455 {B : Type'} (a1 : B) : (@eq B a1) = (@eq B a1).
Proof. exact (eq_refl (@eq B a1)). Qed.
Lemma lem3804456 {A B : Type'} (a1 : B) (f : type1411 A B) (x : A) (c : B) : (a1 = (f x c)) = (a1 = (term337 A B f x c)).
Proof. exact (MK_COMB (@lem3804455 B a1) (@lem3804454 A B f x c)). Qed.
Lemma lem3804479 {B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (h1 : term535 B a1 a2 n1 n2) : term811 B a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3804208 B a1 a2 n1 n2) (@lem3803136 B a1 a2 n1 n2 h1)). Qed.
Lemma lem3804490 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3804491 {A B : Type'} (f : type1411 A B) (x : A) : (f x) = (@I (A -> B -> B) f x).
Proof. exact (@lem3804490 A (B -> B) f x). Qed.
Lemma lem3804492 {A B : Type'} (w : A -> B) (x : A) : (w x) = (w x).
Proof. exact (eq_refl (w x)). Qed.
Lemma lem3804493 {A B : Type'} (f : type1411 A B) (w : A -> B) (x : A) : (term812 A B f w x) = (term813 A B f w x).
Proof. exact (MK_COMB (@lem3804491 A B f x) (@lem3804492 A B w x)). Qed.
Lemma lem3804495 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3804496 {B : Type'} (f : B -> B) (x : B) : (f x) = (@I (B -> B) f x).
Proof. exact (@lem3804495 B B f x). Qed.
Lemma lem3804497 {A B : Type'} (f : type1411 A B) (w : A -> B) (x : A) : (term813 A B f w x) = (term814 A B f w x).
Proof. exact (@lem3804496 B (@I (A -> B -> B) f x) (w x)). Qed.
Lemma lem3804499 {A B : Type'} (f : type1411 A B) (w : A -> B) (x : A) : (term812 A B f w x) = (term814 A B f w x).
Proof. exact (TRANS (@lem3804493 A B f w x) (@lem3804497 A B f w x)). Qed.
Lemma lem3804500 {B : Type'} (a2 : B) : (@eq B a2) = (@eq B a2).
Proof. exact (eq_refl (@eq B a2)). Qed.
Lemma lem3804501 {A B : Type'} (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) : (a2 = (term812 A B f w x)) = (a2 = (term814 A B f w x)).
Proof. exact (MK_COMB (@lem3804500 B a2) (@lem3804499 A B f w x)). Qed.
Lemma lem3804520 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (w : A -> B) (x : A) (n2 : nat) : (term815 A B f b s w x n2) = (term815 A B f b s w x n2).
Proof. exact (eq_refl (term815 A B f b s w x n2)). Qed.
Lemma lem3804521 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) : (term816 A B b s n2 a2 f w x) = (term817 A B b s n2 a2 f w x).
Proof. exact (MK_COMB (@lem3804520 A B f b s w x n2) (@lem3804501 A B a2 f w x)). Qed.
Lemma lem3804530 {A : Type'} (x : A) (s : A -> Prop) : (term643 A x s) = (term643 A x s).
Proof. exact (eq_refl (term643 A x s)). Qed.
Lemma lem3804531 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) : (term687 A B b s n2 a2 f w x) = (term818 A B b s n2 a2 f w x).
Proof. exact (MK_COMB (@lem3804530 A x s) (@lem3804521 A B b s n2 a2 f w x)). Qed.
Lemma lem3804532 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) : (term689 A B b s n2 a2 f w) = (term819 A B b s n2 a2 f w).
Proof. exact (fun_ext (fun x : A => @lem3804531 A B b s n2 a2 f w x)). Qed.
Lemma lem3804533 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3804534 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) : (term691 A B b s n2 a2 f w) = (term820 A B b s n2 a2 f w).
Proof. exact (MK_COMB (@lem3804533 A) (@lem3804532 A B b s n2 a2 f w)). Qed.
Lemma lem3804535 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term820 A B b s n2 a2 f w.
Proof. exact (EQ_MP (@lem3804534 A B b s n2 a2 f w) (@lem3804210 A B b s n2 a2 f w h1)). Qed.
Lemma lem3804763 {A B : Type'} (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n1 : nat) (n2 : nat) : (term633 A B f b s a1 a2 n1 n2) = (term821 A B a1 f b s a2 n1 n2).
Proof. exact (@lem19490 (a1 = a2) (term628 A B a1 n1 f b s a2 n2) (n1 = n2)). Qed.
Lemma lem3804764 {A B : Type'} (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term635 A B f b s a1 n1 n2) = (term822 A B a1 f b s n1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3804763 A B a1 f b s a2 n1 n2)). Qed.
Lemma lem3804765 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3804766 {A B : Type'} (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term636 A B f b s a1 n1 n2) = (term823 A B a1 f b s n1 n2).
Proof. exact (MK_COMB (@lem3804765 B) (@lem3804764 A B a1 f b s n1 n2)). Qed.
Lemma lem3804767 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term637 A B f b s n1 n2) = (term824 A B f b s n1 n2).
Proof. exact (fun_ext (fun a1 : B => @lem3804766 A B a1 f b s n1 n2)). Qed.
Lemma lem3804768 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3804769 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term638 A B f b s n1 n2) = (term825 A B f b s n1 n2).
Proof. exact (MK_COMB (@lem3804768 B) (@lem3804767 A B f b s n1 n2)). Qed.
Lemma lem3804770 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term639 A B f b n1 n2) = (term826 A B f b n1 n2).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3804769 A B f b s n1 n2)). Qed.
Lemma lem3804771 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3804772 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term640 A B f b n1 n2) = (term827 A B f b n1 n2).
Proof. exact (MK_COMB (@lem3804771 A) (@lem3804770 A B f b n1 n2)). Qed.
Lemma lem3804773 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term641 A B f b n1) = (term828 A B f b n1).
Proof. exact (fun_ext (fun n2 : nat => @lem3804772 A B f b n1 n2)). Qed.
Lemma lem3804774 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3804776 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term642 A B f b n1) = (term829 A B f b n1).
Proof. exact (MK_COMB (@lem3804774) (@lem3804773 A B f b n1)). Qed.
Lemma lem3804777 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term829 A B f b n1.
Proof. exact (EQ_MP (@lem3804776 A B f b n1) (@lem3804355 A B f b n1 h1)). Qed.
Lemma lem3804816 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3804820 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term533 A B f b s x c n1) : term533 A B f b s x c n1.
Proof. exact (h1). Qed.
Lemma lem3804842 {A B : Type'} (b : B) (n2 : nat) (s : A -> Prop) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) : (term818 A B b s n2 a2 f w x) = (term830 A B b n2 s a2 f w x).
Proof. exact (@lem19490 (term831 A B f b s w x n2) (term662 A x s) (a2 = (term814 A B f w x))). Qed.
Lemma lem3804843 {A B : Type'} (b : B) (n2 : nat) (s : A -> Prop) (a2 : B) (f : type1411 A B) (w : A -> B) : (term819 A B b s n2 a2 f w) = (term832 A B b n2 s a2 f w).
Proof. exact (fun_ext (fun x : A => @lem3804842 A B b n2 s a2 f w x)). Qed.
Lemma lem3804844 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3804846 {A B : Type'} (b : B) (n2 : nat) (s : A -> Prop) (a2 : B) (f : type1411 A B) (w : A -> B) : (term820 A B b s n2 a2 f w) = (term833 A B b n2 s a2 f w).
Proof. exact (MK_COMB (@lem3804844 A) (@lem3804843 A B b n2 s a2 f w)). Qed.
Lemma lem3804847 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term833 A B b n2 s a2 f w.
Proof. exact (EQ_MP (@lem3804846 A B b n2 s a2 f w) (@lem3804535 A B b s n2 a2 f w h1)). Qed.
Lemma lem3804952 {B : Type'} (a1 : B) (a2 : B) (h1 : term153 B a1 a2) : term153 B a1 a2.
Proof. exact (h1). Qed.
Lemma lem3805020 {A B : Type'} (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n1 : nat) (n2 : nat) : (term633 A B f b s a1 a2 n1 n2) = (term821 A B a1 f b s a2 n1 n2).
Proof. exact (@lem19490 (a1 = a2) (term628 A B a1 n1 f b s a2 n2) (n1 = n2)). Qed.
Lemma lem3805021 {A B : Type'} (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term635 A B f b s a1 n1 n2) = (term822 A B a1 f b s n1 n2).
Proof. exact (fun_ext (fun a2 : B => @lem3805020 A B a1 f b s a2 n1 n2)). Qed.
Lemma lem3805022 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3805023 {A B : Type'} (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term636 A B f b s a1 n1 n2) = (term823 A B a1 f b s n1 n2).
Proof. exact (MK_COMB (@lem3805022 B) (@lem3805021 A B a1 f b s n1 n2)). Qed.
Lemma lem3805024 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term637 A B f b s n1 n2) = (term824 A B f b s n1 n2).
Proof. exact (fun_ext (fun a1 : B => @lem3805023 A B a1 f b s n1 n2)). Qed.
Lemma lem3805025 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3805026 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (n1 : nat) (n2 : nat) : (term638 A B f b s n1 n2) = (term825 A B f b s n1 n2).
Proof. exact (MK_COMB (@lem3805025 B) (@lem3805024 A B f b s n1 n2)). Qed.
Lemma lem3805027 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term639 A B f b n1 n2) = (term826 A B f b n1 n2).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3805026 A B f b s n1 n2)). Qed.
Lemma lem3805028 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3805029 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (n2 : nat) : (term640 A B f b n1 n2) = (term827 A B f b n1 n2).
Proof. exact (MK_COMB (@lem3805028 A) (@lem3805027 A B f b n1 n2)). Qed.
Lemma lem3805030 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term641 A B f b n1) = (term828 A B f b n1).
Proof. exact (fun_ext (fun n2 : nat => @lem3805029 A B f b n1 n2)). Qed.
Lemma lem3805031 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3805033 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) : (term642 A B f b n1) = (term829 A B f b n1).
Proof. exact (MK_COMB (@lem3805031) (@lem3805030 A B f b n1)). Qed.
Lemma lem3805034 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term829 A B f b n1.
Proof. exact (EQ_MP (@lem3805033 A B f b n1) (@lem3804355 A B f b n1 h1)). Qed.
Lemma lem3805073 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3805077 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term533 A B f b s x c n1) : term533 A B f b s x c n1.
Proof. exact (h1). Qed.
Lemma lem3805099 {A B : Type'} (b : B) (n2 : nat) (s : A -> Prop) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) : (term818 A B b s n2 a2 f w x) = (term830 A B b n2 s a2 f w x).
Proof. exact (@lem19490 (term831 A B f b s w x n2) (term662 A x s) (a2 = (term814 A B f w x))). Qed.
Lemma lem3805100 {A B : Type'} (b : B) (n2 : nat) (s : A -> Prop) (a2 : B) (f : type1411 A B) (w : A -> B) : (term819 A B b s n2 a2 f w) = (term832 A B b n2 s a2 f w).
Proof. exact (fun_ext (fun x : A => @lem3805099 A B b n2 s a2 f w x)). Qed.
Lemma lem3805101 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3805103 {A B : Type'} (b : B) (n2 : nat) (s : A -> Prop) (a2 : B) (f : type1411 A B) (w : A -> B) : (term820 A B b s n2 a2 f w) = (term833 A B b n2 s a2 f w).
Proof. exact (MK_COMB (@lem3805101 A) (@lem3805100 A B b n2 s a2 f w)). Qed.
Lemma lem3805104 {A B : Type'} (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term833 A B b n2 s a2 f w.
Proof. exact (EQ_MP (@lem3805103 A B b n2 s a2 f w) (@lem3804535 A B b s n2 a2 f w h1)). Qed.
Lemma lem3805209 (n1 : nat) (n2 : nat) (h1 : term834 n1 n2) : term834 n1 n2.
Proof. exact (h1). Qed.
Lemma lem3805219 {A B : Type'} (_43994 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term835 A B f b n1 _43994.
Proof. exact (@lem3804777 A B f b n1 h1 _43994). Qed.
Lemma lem3805220 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (_43994 : nat) : (term835 A B f b n1 _43994) = (term827 A B f b n1 _43994).
Proof. exact (eq_refl (term835 A B f b n1 _43994)). Qed.
Lemma lem3805221 {A B : Type'} (_43994 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term827 A B f b n1 _43994.
Proof. exact (EQ_MP (@lem3805220 A B f b n1 _43994) (@lem3805219 A B _43994 f b n1 h1)). Qed.
Lemma lem3805222 {A B : Type'} (_43994 : nat) (_43995 : A -> Prop) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term836 A B f b n1 _43994 _43995.
Proof. exact (@lem3805221 A B _43994 f b n1 h1 _43995). Qed.
Lemma lem3805223 {A B : Type'} (f : type1411 A B) (b : B) (_43995 : A -> Prop) (n1 : nat) (_43994 : nat) : (term836 A B f b n1 _43994 _43995) = (term825 A B f b _43995 n1 _43994).
Proof. exact (eq_refl (term836 A B f b n1 _43994 _43995)). Qed.
Lemma lem3805224 {A B : Type'} (_43995 : A -> Prop) (_43994 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term825 A B f b _43995 n1 _43994.
Proof. exact (EQ_MP (@lem3805223 A B f b _43995 n1 _43994) (@lem3805222 A B _43994 _43995 f b n1 h1)). Qed.
Lemma lem3805225 {A B : Type'} (_43995 : A -> Prop) (_43994 : nat) (_43996 : B) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term837 A B f b _43995 n1 _43994 _43996.
Proof. exact (@lem3805224 A B _43995 _43994 f b n1 h1 _43996). Qed.
Lemma lem3805226 {A B : Type'} (_43996 : B) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (n1 : nat) (_43994 : nat) : (term837 A B f b _43995 n1 _43994 _43996) = (term823 A B _43996 f b _43995 n1 _43994).
Proof. exact (eq_refl (term837 A B f b _43995 n1 _43994 _43996)). Qed.
Lemma lem3805227 {A B : Type'} (_43996 : B) (_43995 : A -> Prop) (_43994 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term823 A B _43996 f b _43995 n1 _43994.
Proof. exact (EQ_MP (@lem3805226 A B _43996 f b _43995 n1 _43994) (@lem3805225 A B _43995 _43994 _43996 f b n1 h1)). Qed.
Lemma lem3805228 {A B : Type'} (_43996 : B) (_43995 : A -> Prop) (_43994 : nat) (_43997 : B) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term838 A B _43996 f b _43995 n1 _43994 _43997.
Proof. exact (@lem3805227 A B _43996 _43995 _43994 f b n1 h1 _43997). Qed.
Lemma lem3805229 {A B : Type'} (_43996 : B) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (n1 : nat) (_43994 : nat) : (term838 A B _43996 f b _43995 n1 _43994 _43997) = (term821 A B _43996 f b _43995 _43997 n1 _43994).
Proof. exact (eq_refl (term838 A B _43996 f b _43995 n1 _43994 _43997)). Qed.
Lemma lem3805230 {A B : Type'} (_43996 : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term821 A B _43996 f b _43995 _43997 n1 _43994.
Proof. exact (EQ_MP (@lem3805229 A B _43996 f b _43995 _43997 n1 _43994) (@lem3805228 A B _43996 _43995 _43994 _43997 f b n1 h1)). Qed.
Lemma lem3805240 {A B : Type'} (_44001 : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term839 A B b n2 s a2 f w _44001.
Proof. exact (@lem3804847 A B b s n2 a2 f w h1 _44001). Qed.
Lemma lem3805241 {A B : Type'} (b : B) (n2 : nat) (s : A -> Prop) (a2 : B) (f : type1411 A B) (w : A -> B) (_44001 : A) : (term839 A B b n2 s a2 f w _44001) = (term830 A B b n2 s a2 f w _44001).
Proof. exact (eq_refl (term839 A B b n2 s a2 f w _44001)). Qed.
Lemma lem3805242 {A B : Type'} (_44001 : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term830 A B b n2 s a2 f w _44001.
Proof. exact (EQ_MP (@lem3805241 A B b n2 s a2 f w _44001) (@lem3805240 A B _44001 b s n2 a2 f w h1)). Qed.
Lemma lem3805270 {A B : Type'} (_44011 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term835 A B f b n1 _44011.
Proof. exact (@lem3805034 A B f b n1 h1 _44011). Qed.
Lemma lem3805271 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (_44011 : nat) : (term835 A B f b n1 _44011) = (term827 A B f b n1 _44011).
Proof. exact (eq_refl (term835 A B f b n1 _44011)). Qed.
Lemma lem3805272 {A B : Type'} (_44011 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term827 A B f b n1 _44011.
Proof. exact (EQ_MP (@lem3805271 A B f b n1 _44011) (@lem3805270 A B _44011 f b n1 h1)). Qed.
Lemma lem3805273 {A B : Type'} (_44011 : nat) (_44012 : A -> Prop) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term836 A B f b n1 _44011 _44012.
Proof. exact (@lem3805272 A B _44011 f b n1 h1 _44012). Qed.
Lemma lem3805274 {A B : Type'} (f : type1411 A B) (b : B) (_44012 : A -> Prop) (n1 : nat) (_44011 : nat) : (term836 A B f b n1 _44011 _44012) = (term825 A B f b _44012 n1 _44011).
Proof. exact (eq_refl (term836 A B f b n1 _44011 _44012)). Qed.
Lemma lem3805275 {A B : Type'} (_44012 : A -> Prop) (_44011 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term825 A B f b _44012 n1 _44011.
Proof. exact (EQ_MP (@lem3805274 A B f b _44012 n1 _44011) (@lem3805273 A B _44011 _44012 f b n1 h1)). Qed.
Lemma lem3805276 {A B : Type'} (_44012 : A -> Prop) (_44011 : nat) (_44013 : B) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term837 A B f b _44012 n1 _44011 _44013.
Proof. exact (@lem3805275 A B _44012 _44011 f b n1 h1 _44013). Qed.
Lemma lem3805277 {A B : Type'} (_44013 : B) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (n1 : nat) (_44011 : nat) : (term837 A B f b _44012 n1 _44011 _44013) = (term823 A B _44013 f b _44012 n1 _44011).
Proof. exact (eq_refl (term837 A B f b _44012 n1 _44011 _44013)). Qed.
Lemma lem3805278 {A B : Type'} (_44013 : B) (_44012 : A -> Prop) (_44011 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term823 A B _44013 f b _44012 n1 _44011.
Proof. exact (EQ_MP (@lem3805277 A B _44013 f b _44012 n1 _44011) (@lem3805276 A B _44012 _44011 _44013 f b n1 h1)). Qed.
Lemma lem3805279 {A B : Type'} (_44013 : B) (_44012 : A -> Prop) (_44011 : nat) (_44014 : B) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term838 A B _44013 f b _44012 n1 _44011 _44014.
Proof. exact (@lem3805278 A B _44013 _44012 _44011 f b n1 h1 _44014). Qed.
Lemma lem3805280 {A B : Type'} (_44013 : B) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (n1 : nat) (_44011 : nat) : (term838 A B _44013 f b _44012 n1 _44011 _44014) = (term821 A B _44013 f b _44012 _44014 n1 _44011).
Proof. exact (eq_refl (term838 A B _44013 f b _44012 n1 _44011 _44014)). Qed.
Lemma lem3805281 {A B : Type'} (_44013 : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term821 A B _44013 f b _44012 _44014 n1 _44011.
Proof. exact (EQ_MP (@lem3805280 A B _44013 f b _44012 _44014 n1 _44011) (@lem3805279 A B _44013 _44012 _44011 _44014 f b n1 h1)). Qed.
Lemma lem3805291 {A B : Type'} (_44018 : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term839 A B b n2 s a2 f w _44018.
Proof. exact (@lem3805104 A B b s n2 a2 f w h1 _44018). Qed.
Lemma lem3805292 {A B : Type'} (b : B) (n2 : nat) (s : A -> Prop) (a2 : B) (f : type1411 A B) (w : A -> B) (_44018 : A) : (term839 A B b n2 s a2 f w _44018) = (term830 A B b n2 s a2 f w _44018).
Proof. exact (eq_refl (term839 A B b n2 s a2 f w _44018)). Qed.
Lemma lem3805293 {A B : Type'} (_44018 : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term830 A B b n2 s a2 f w _44018.
Proof. exact (EQ_MP (@lem3805292 A B b n2 s a2 f w _44018) (@lem3805291 A B _44018 b s n2 a2 f w h1)). Qed.
Lemma lem3805321 {A B : Type'} (_43995 : A -> Prop) (_43994 : nat) (_43996 : B) (_43997 : B) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term840 A B n1 f b _43995 _43994 _43996 _43997.
Proof. exact (proj1 (@lem3805230 A B _43996 _43995 _43997 _43994 f b n1 h1)). Qed.
Lemma lem3805330 {A B : Type'} (_44013 : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term841 A B _44013 f b _44012 _44014 n1 _44011.
Proof. exact (proj2 (@lem3805281 A B _44013 _44012 _44014 _44011 f b n1 h1)). Qed.
Lemma lem3805339 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3805341 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term533 A B f b s x c n1) : term533 A B f b s x c n1.
Proof. exact (h1). Qed.
Lemma lem3805343 {A B : Type'} (a1 : B) (f : type1411 A B) (x : A) (c : B) (h1 : a1 = (f x c)) : a1 = (term337 A B f x c).
Proof. exact (EQ_MP (@lem3804456 A B a1 f x c) (@lem3804197 A B a1 f x c h1)). Qed.
Lemma lem3805345 {B : Type'} (a1 : B) (a2 : B) (h1 : term153 B a1 a2) : term153 B a1 a2.
Proof. exact (h1). Qed.
Lemma lem3805424 {A B : Type'} (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43994 : nat) (_43996 : B) (_43997 : B) : (term840 A B n1 f b _43995 _43994 _43996 _43997) = (term842 A B n1 f b _43995 _43994 _43996 _43997).
Proof. exact (@lem3797407 (term843 A B f b _43995 _43996 n1) (term843 A B f b _43995 _43997 _43994) (_43996 = _43997)). Qed.
Lemma lem3805445 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3805447 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term533 A B f b s x c n1) : term533 A B f b s x c n1.
Proof. exact (h1). Qed.
Lemma lem3805451 (n1 : nat) (n2 : nat) (h1 : term834 n1 n2) : term834 n1 n2.
Proof. exact (h1). Qed.
Lemma lem3805542 {A B : Type'} (_44013 : B) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (n1 : nat) (_44011 : nat) : (term841 A B _44013 f b _44012 _44014 n1 _44011) = (term844 A B _44013 f b _44012 _44014 n1 _44011).
Proof. exact (@lem3797407 (term843 A B f b _44012 _44013 n1) (term843 A B f b _44012 _44014 _44011) (n1 = _44011)). Qed.
Lemma lem3805585 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3805599 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term533 A B f b s x c n1) : term533 A B f b s x c n1.
Proof. exact (h1). Qed.
Lemma lem3805600 {B : Type'} (a2 : B) : (term154 B a2) = (term154 B a2).
Proof. exact (eq_refl (term154 B a2)). Qed.
Lemma lem3805601 {A B : Type'} (a2 : B) (a1 : B) (f : type1411 A B) (x : A) (c : B) (h1 : a1 = (f x c)) : (term155 B a2 a1) = (term845 A B a2 f x c).
Proof. exact (MK_COMB (@lem3805600 B a2) (@lem3805343 A B a1 f x c h1)). Qed.
Lemma lem3805602 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (a2 : B) : (term845 A B a2 f x c) = (term846 A B f x c a2).
Proof. exact (eq_refl (term845 A B a2 f x c)). Qed.
Lemma lem3805603 {B : Type'} (a2 : B) (a1 : B) : (term156 B a2 a1) = (term156 B a2 a1).
Proof. exact (eq_refl (term156 B a2 a1)). Qed.
Lemma lem3805604 {A B : Type'} (a1 : B) (f : type1411 A B) (x : A) (c : B) (a2 : B) : ((term155 B a2 a1) = (term845 A B a2 f x c)) = ((term155 B a2 a1) = (term846 A B f x c a2)).
Proof. exact (MK_COMB (@lem3805603 B a2 a1) (@lem3805602 A B f x c a2)). Qed.
Lemma lem3805605 {B : Type'} (a1 : B) (a2 : B) : (term155 B a2 a1) = (term153 B a1 a2).
Proof. exact (eq_refl (term155 B a2 a1)). Qed.
Lemma lem3805606 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3805607 {B : Type'} (a1 : B) (a2 : B) : (term156 B a2 a1) = (term157 B a1 a2).
Proof. exact (MK_COMB (@lem3805606) (@lem3805605 B a1 a2)). Qed.
Lemma lem3805608 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (a2 : B) : (term846 A B f x c a2) = (term846 A B f x c a2).
Proof. exact (eq_refl (term846 A B f x c a2)). Qed.
Lemma lem3805609 {A B : Type'} (a1 : B) (f : type1411 A B) (x : A) (c : B) (a2 : B) : ((term155 B a2 a1) = (term846 A B f x c a2)) = ((term153 B a1 a2) = (term846 A B f x c a2)).
Proof. exact (MK_COMB (@lem3805607 B a1 a2) (@lem3805608 A B f x c a2)). Qed.
Lemma lem3805610 {A B : Type'} (a1 : B) (f : type1411 A B) (x : A) (c : B) (a2 : B) : ((term155 B a2 a1) = (term845 A B a2 f x c)) = ((term153 B a1 a2) = (term846 A B f x c a2)).
Proof. exact (TRANS (@lem3805604 A B a1 f x c a2) (@lem3805609 A B a1 f x c a2)). Qed.
Lemma lem3805611 {A B : Type'} (a2 : B) (a1 : B) (f : type1411 A B) (x : A) (c : B) (h1 : a1 = (f x c)) : (term153 B a1 a2) = (term846 A B f x c a2).
Proof. exact (EQ_MP (@lem3805610 A B a1 f x c a2) (@lem3805601 A B a2 a1 f x c h1)). Qed.
Lemma lem3805612 {A B : Type'} (a2 : B) (a1 : B) (f : type1411 A B) (x : A) (c : B) (h1 : term153 B a1 a2) (h2 : a1 = (f x c)) : term846 A B f x c a2.
Proof. exact (EQ_MP (@lem3805611 A B a2 a1 f x c h2) (@lem3805345 B a1 a2 h1)). Qed.
Lemma lem3805681 {A B : Type'} (_44001 : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term847 A B f b s w _44001 n2.
Proof. exact (proj1 (@lem3805242 A B _44001 b s n2 a2 f w h1)). Qed.
Lemma lem3805695 {A B : Type'} (_44001 : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term848 A B s a2 f w _44001.
Proof. exact (proj2 (@lem3805242 A B _44001 b s n2 a2 f w h1)). Qed.
Lemma lem3805737 {A B : Type'} (_43995 : A -> Prop) (_43994 : nat) (_43996 : B) (_43997 : B) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term842 A B n1 f b _43995 _43994 _43996 _43997.
Proof. exact (EQ_MP (@lem3805424 A B n1 f b _43995 _43994 _43996 _43997) (@lem3805321 A B _43995 _43994 _43996 _43997 f b n1 h1)). Qed.
Lemma lem3805793 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3805807 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term533 A B f b s x c n1) : term533 A B f b s x c n1.
Proof. exact (h1). Qed.
Lemma lem3805821 (n1 : nat) (n2 : nat) (h1 : term834 n1 n2) : term834 n1 n2.
Proof. exact (h1). Qed.
Lemma lem3805890 {A B : Type'} (_44018 : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term847 A B f b s w _44018 n2.
Proof. exact (proj1 (@lem3805293 A B _44018 b s n2 a2 f w h1)). Qed.
Lemma lem3805960 {A B : Type'} (_44013 : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term844 A B _44013 f b _44012 _44014 n1 _44011.
Proof. exact (EQ_MP (@lem3805542 A B _44013 f b _44012 _44014 n1 _44011) (@lem3805330 A B _44013 _44012 _44014 _44011 f b n1 h1)). Qed.
Lemma lem3806110 {B : Type'} : (@I (B -> B)) = (@I (B -> B)).
Proof. exact (eq_refl (@I (B -> B))). Qed.
Lemma lem3806111 {B : Type'} (_44123 : B -> B) (_44125 : B -> B) (h1 : _44123 = _44125) : _44123 = _44125.
Proof. exact (h1). Qed.
Lemma lem3806112 {B : Type'} (_44124 : B) (_44126 : B) (h1 : _44124 = _44126) : _44124 = _44126.
Proof. exact (h1). Qed.
Lemma lem3806113 {B : Type'} (_44123 : B -> B) (_44125 : B -> B) (h1 : _44123 = _44125) : (@I (B -> B) _44123) = (@I (B -> B) _44125).
Proof. exact (MK_COMB (@lem3806110 B) (@lem3806111 B _44123 _44125 h1)). Qed.
Lemma lem3806114 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) (h1 : _44124 = _44126) (h2 : _44123 = _44125) : (@I (B -> B) _44123 _44124) = (@I (B -> B) _44125 _44126).
Proof. exact (MK_COMB (@lem3806113 B _44123 _44125 h2) (@lem3806112 B _44124 _44126 h1)). Qed.
Lemma lem3806115 {B : Type'} (_44123 : B -> B) (_44125 : B -> B) (_44124 : B) (_44126 : B) (h1 : _44124 = _44126) : term849 B _44123 _44124 _44125 _44126.
Proof. exact (fun h0 : _44123 = _44125 => @lem3806114 B _44124 _44126 _44123 _44125 h1 h0). Qed.
Lemma lem3806117 (a : Prop) (b : Prop) : (a -> b) = (term850 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3806118 {B : Type'} (_44123 : B -> B) (_44124 : B) (_44125 : B -> B) (_44126 : B) : (term849 B _44123 _44124 _44125 _44126) = (term851 B _44123 _44124 _44125 _44126).
Proof. exact (@lem3806117 (_44123 = _44125) ((@I (B -> B) _44123 _44124) = (@I (B -> B) _44125 _44126))). Qed.
Lemma lem3806119 {B : Type'} (_44123 : B -> B) (_44125 : B -> B) (_44124 : B) (_44126 : B) (h1 : _44124 = _44126) : term851 B _44123 _44124 _44125 _44126.
Proof. exact (EQ_MP (@lem3806118 B _44123 _44124 _44125 _44126) (@lem3806115 B _44123 _44125 _44124 _44126 h1)). Qed.
Lemma lem3806120 {B : Type'} (_44123 : B -> B) (_44124 : B) (_44125 : B -> B) (_44126 : B) : term852 B _44123 _44124 _44125 _44126.
Proof. exact (fun h0 : _44124 = _44126 => @lem3806119 B _44123 _44125 _44124 _44126 h0). Qed.
Lemma lem3806122 (a : Prop) (b : Prop) : (a -> b) = (term850 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3806123 {B : Type'} (_44123 : B -> B) (_44124 : B) (_44125 : B -> B) (_44126 : B) : (term852 B _44123 _44124 _44125 _44126) = (term853 B _44123 _44124 _44125 _44126).
Proof. exact (@lem3806122 (_44124 = _44126) (term851 B _44123 _44124 _44125 _44126)). Qed.
Lemma lem3806124 {B : Type'} (_44123 : B -> B) (_44124 : B) (_44125 : B -> B) (_44126 : B) : term853 B _44123 _44124 _44125 _44126.
Proof. exact (EQ_MP (@lem3806123 B _44123 _44124 _44125 _44126) (@lem3806120 B _44123 _44124 _44125 _44126)). Qed.
Lemma lem3806126 {B : Type'} (x : B) (y : B) (z : B) : term854 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem3806138 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term533 A B f b s x c n1) : term533 A B f b s x c n1.
Proof. exact (h1). Qed.
Lemma lem3806139 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term533 A B f b s x c n1) : term855 A B f b s x c n1.
Proof. exact (fun h0 : term856 A B f b s x c n1 => @lem3806138 A B f b s x c n1 h1). Qed.
Lemma lem3806141 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806142 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) : (term855 A B f b s x c n1) = (term533 A B f b s x c n1).
Proof. exact (@lem3806141 (term533 A B f b s x c n1)). Qed.
Lemma lem3806143 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term533 A B f b s x c n1) : term533 A B f b s x c n1.
Proof. exact (EQ_MP (@lem3806142 A B f b s x c n1) (@lem3806139 A B f b s x c n1 h1)). Qed.
Lemma lem3806145 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3806146 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term857 A x s.
Proof. exact (fun h0 : term662 A x s => @lem3806145 A x s h1). Qed.
Lemma lem3806148 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806149 {A : Type'} (x : A) (s : A -> Prop) : (term857 A x s) = (@IN A x s).
Proof. exact (@lem3806148 (@IN A x s)). Qed.
Lemma lem3806150 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem3806149 A x s) (@lem3806146 A x s h1)). Qed.
Lemma lem3806156 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3806157 {A B : Type'} (f : type1411 A B) (b : B) (w : A -> B) (n2 : nat) (_44001 : A) (s : A -> Prop) : (term847 A B f b s w _44001 n2) = (term858 A B f b w n2 _44001 s).
Proof. exact (@lem3806156 (term831 A B f b s w _44001 n2) (term662 A _44001 s)). Qed.
Lemma lem3806163 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3806164 {A B : Type'} (f : type1411 A B) (b : B) (w : A -> B) (n2 : nat) (_44001 : A) (s : A -> Prop) : (term859 A B f b s w _44001 n2) = (term860 A B f b w n2 _44001 s).
Proof. exact (MK_COMB (@lem3806163) (@lem3806157 A B f b w n2 _44001 s)). Qed.
Lemma lem3806170 {A B : Type'} (f : type1411 A B) (b : B) (w : A -> B) (n2 : nat) (_44001 : A) (s : A -> Prop) : (term858 A B f b w n2 _44001 s) = (term858 A B f b w n2 _44001 s).
Proof. exact (eq_refl (term858 A B f b w n2 _44001 s)). Qed.
Lemma lem3806171 {A B : Type'} (f : type1411 A B) (b : B) (w : A -> B) (n2 : nat) (_44001 : A) (s : A -> Prop) : ((term847 A B f b s w _44001 n2) = (term858 A B f b w n2 _44001 s)) = ((term858 A B f b w n2 _44001 s) = (term858 A B f b w n2 _44001 s)).
Proof. exact (MK_COMB (@lem3806164 A B f b w n2 _44001 s) (@lem3806170 A B f b w n2 _44001 s)). Qed.
Lemma lem3806173 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3806174 (x : Prop) : (x = x) = True.
Proof. exact (@lem3806173 Prop x). Qed.
Lemma lem3806175 {A B : Type'} (f : type1411 A B) (b : B) (w : A -> B) (n2 : nat) (_44001 : A) (s : A -> Prop) : ((term858 A B f b w n2 _44001 s) = (term858 A B f b w n2 _44001 s)) = True.
Proof. exact (@lem3806174 (term858 A B f b w n2 _44001 s)). Qed.
Lemma lem3806176 {A B : Type'} (f : type1411 A B) (b : B) (w : A -> B) (n2 : nat) (_44001 : A) (s : A -> Prop) : ((term847 A B f b s w _44001 n2) = (term858 A B f b w n2 _44001 s)) = True.
Proof. exact (TRANS (@lem3806171 A B f b w n2 _44001 s) (@lem3806175 A B f b w n2 _44001 s)). Qed.
Lemma lem3806177 {A B : Type'} (f : type1411 A B) (b : B) (w : A -> B) (n2 : nat) (_44001 : A) (s : A -> Prop) : True = ((term847 A B f b s w _44001 n2) = (term858 A B f b w n2 _44001 s)).
Proof. exact (SYM (@lem3806176 A B f b w n2 _44001 s)). Qed.
Lemma lem3806178 {A B : Type'} (f : type1411 A B) (b : B) (w : A -> B) (n2 : nat) (_44001 : A) (s : A -> Prop) : (term847 A B f b s w _44001 n2) = (term858 A B f b w n2 _44001 s).
Proof. exact (EQ_MP (@lem3806177 A B f b w n2 _44001 s) (@lem0)). Qed.
Lemma lem3806179 {A B : Type'} (_44001 : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term858 A B f b w n2 _44001 s.
Proof. exact (EQ_MP (@lem3806178 A B f b w n2 _44001 s) (@lem3805681 A B _44001 b s n2 a2 f w h1)). Qed.
Lemma lem3806181 (b : Prop) (a : Prop) : (a \/ b) = (term861 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3806182 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (w : A -> B) (_44001 : A) (n2 : nat) : (term858 A B f b w n2 _44001 s) = (term862 A B f b s w _44001 n2).
Proof. exact (@lem3806181 (term662 A _44001 s) (term831 A B f b s w _44001 n2)). Qed.
Lemma lem3806184 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3806185 {A : Type'} (_44001 : A) (s : A -> Prop) : (term863 A _44001 s) = (@IN A _44001 s).
Proof. exact (@lem3806184 (@IN A _44001 s)). Qed.
Lemma lem3806186 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3806187 {A : Type'} (_44001 : A) (s : A -> Prop) : (term864 A _44001 s) = (term548 A _44001 s).
Proof. exact (MK_COMB (@lem3806186) (@lem3806185 A _44001 s)). Qed.
Lemma lem3806188 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (w : A -> B) (_44001 : A) (n2 : nat) : (term831 A B f b s w _44001 n2) = (term831 A B f b s w _44001 n2).
Proof. exact (eq_refl (term831 A B f b s w _44001 n2)). Qed.
Lemma lem3806189 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (w : A -> B) (_44001 : A) (n2 : nat) : (term862 A B f b s w _44001 n2) = (term865 A B f b s w _44001 n2).
Proof. exact (MK_COMB (@lem3806187 A _44001 s) (@lem3806188 A B f b s w _44001 n2)). Qed.
Lemma lem3806190 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (w : A -> B) (_44001 : A) (n2 : nat) : (term858 A B f b w n2 _44001 s) = (term865 A B f b s w _44001 n2).
Proof. exact (TRANS (@lem3806182 A B f b s w _44001 n2) (@lem3806189 A B f b s w _44001 n2)). Qed.
Lemma lem3806193 {A B : Type'} (_44001 : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term865 A B f b s w _44001 n2.
Proof. exact (EQ_MP (@lem3806190 A B f b s w _44001 n2) (@lem3806179 A B _44001 b s n2 a2 f w h1)). Qed.
Lemma lem3806194 {A B : Type'} (_44001 : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term865 A B f b s w _44001 n2.
Proof. exact (@lem3806193 A B _44001 b s n2 a2 f w h1). Qed.
Lemma lem3806195 {A B : Type'} (x : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term865 A B f b s w x n2.
Proof. exact (@lem3806194 A B x b s n2 a2 f w h1). Qed.
Lemma lem3806198 {A B : Type'} (b : B) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) (s : A -> Prop) (h1 : term691 A B b s n2 a2 f w) (h2 : @IN A x s) : term831 A B f b s w x n2.
Proof. exact (@lem3806195 A B x b s n2 a2 f w h1 (@lem3806150 A x s h2)). Qed.
Lemma lem3806199 {A B : Type'} (b : B) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) (s : A -> Prop) (h1 : term691 A B b s n2 a2 f w) (h2 : @IN A x s) : term866 A B f b s w x n2.
Proof. exact (fun h0 : term867 A B f b s w x n2 => @lem3806198 A B b n2 a2 f w x s h1 h2). Qed.
Lemma lem3806201 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806202 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (w : A -> B) (x : A) (n2 : nat) : (term866 A B f b s w x n2) = (term831 A B f b s w x n2).
Proof. exact (@lem3806201 (term831 A B f b s w x n2)). Qed.
Lemma lem3806203 {A B : Type'} (b : B) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) (s : A -> Prop) (h1 : term691 A B b s n2 a2 f w) (h2 : @IN A x s) : term831 A B f b s w x n2.
Proof. exact (EQ_MP (@lem3806202 A B f b s w x n2) (@lem3806199 A B b n2 a2 f w x s h1 h2)). Qed.
Lemma lem3806219 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3806220 {A B : Type'} (_43996 : B) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) : (term868 A B f b _43995 _43994 _43996 _43997) = (term869 A B _43996 f b _43995 _43997 _43994).
Proof. exact (@lem3806219 (_43996 = _43997) (term843 A B f b _43995 _43997 _43994)). Qed.
Lemma lem3806228 {A B : Type'} (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43996 : B) (n1 : nat) : (term870 A B f b _43995 _43996 n1) = (term870 A B f b _43995 _43996 n1).
Proof. exact (eq_refl (term870 A B f b _43995 _43996 n1)). Qed.
Lemma lem3806229 {A B : Type'} (n1 : nat) (_43996 : B) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) : (term842 A B n1 f b _43995 _43994 _43996 _43997) = (term871 A B n1 _43996 f b _43995 _43997 _43994).
Proof. exact (MK_COMB (@lem3806228 A B f b _43995 _43996 n1) (@lem3806220 A B _43996 f b _43995 _43997 _43994)). Qed.
Lemma lem3806233 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3806234 {A B : Type'} (_43996 : B) (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) : (term871 A B n1 _43996 f b _43995 _43997 _43994) = (term872 A B _43996 n1 f b _43995 _43997 _43994).
Proof. exact (@lem3806233 (_43996 = _43997) (term843 A B f b _43995 _43996 n1) (term843 A B f b _43995 _43997 _43994)). Qed.
Lemma lem3806252 {A B : Type'} (_43996 : B) (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) : (term842 A B n1 f b _43995 _43994 _43996 _43997) = (term872 A B _43996 n1 f b _43995 _43997 _43994).
Proof. exact (TRANS (@lem3806229 A B n1 _43996 f b _43995 _43997 _43994) (@lem3806234 A B _43996 n1 f b _43995 _43997 _43994)). Qed.
Lemma lem3806253 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3806254 {A B : Type'} (_43996 : B) (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) : (term873 A B n1 f b _43995 _43994 _43996 _43997) = (term874 A B _43996 n1 f b _43995 _43997 _43994).
Proof. exact (MK_COMB (@lem3806253) (@lem3806252 A B _43996 n1 f b _43995 _43997 _43994)). Qed.
Lemma lem3806272 {A B : Type'} (_43996 : B) (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) : (term872 A B _43996 n1 f b _43995 _43997 _43994) = (term872 A B _43996 n1 f b _43995 _43997 _43994).
Proof. exact (eq_refl (term872 A B _43996 n1 f b _43995 _43997 _43994)). Qed.
Lemma lem3806273 {A B : Type'} (_43996 : B) (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) : ((term842 A B n1 f b _43995 _43994 _43996 _43997) = (term872 A B _43996 n1 f b _43995 _43997 _43994)) = ((term872 A B _43996 n1 f b _43995 _43997 _43994) = (term872 A B _43996 n1 f b _43995 _43997 _43994)).
Proof. exact (MK_COMB (@lem3806254 A B _43996 n1 f b _43995 _43997 _43994) (@lem3806272 A B _43996 n1 f b _43995 _43997 _43994)). Qed.
Lemma lem3806275 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3806276 (x : Prop) : (x = x) = True.
Proof. exact (@lem3806275 Prop x). Qed.
Lemma lem3806277 {A B : Type'} (_43996 : B) (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) : ((term872 A B _43996 n1 f b _43995 _43997 _43994) = (term872 A B _43996 n1 f b _43995 _43997 _43994)) = True.
Proof. exact (@lem3806276 (term872 A B _43996 n1 f b _43995 _43997 _43994)). Qed.
Lemma lem3806278 {A B : Type'} (_43996 : B) (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) : ((term842 A B n1 f b _43995 _43994 _43996 _43997) = (term872 A B _43996 n1 f b _43995 _43997 _43994)) = True.
Proof. exact (TRANS (@lem3806273 A B _43996 n1 f b _43995 _43997 _43994) (@lem3806277 A B _43996 n1 f b _43995 _43997 _43994)). Qed.
Lemma lem3806279 {A B : Type'} (_43996 : B) (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) : True = ((term842 A B n1 f b _43995 _43994 _43996 _43997) = (term872 A B _43996 n1 f b _43995 _43997 _43994)).
Proof. exact (SYM (@lem3806278 A B _43996 n1 f b _43995 _43997 _43994)). Qed.
Lemma lem3806280 {A B : Type'} (_43996 : B) (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) : (term842 A B n1 f b _43995 _43994 _43996 _43997) = (term872 A B _43996 n1 f b _43995 _43997 _43994).
Proof. exact (EQ_MP (@lem3806279 A B _43996 n1 f b _43995 _43997 _43994) (@lem0)). Qed.
Lemma lem3806281 {A B : Type'} (_43996 : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term872 A B _43996 n1 f b _43995 _43997 _43994.
Proof. exact (EQ_MP (@lem3806280 A B _43996 n1 f b _43995 _43997 _43994) (@lem3805737 A B _43995 _43994 _43996 _43997 f b n1 h1)). Qed.
Lemma lem3806283 (b : Prop) (a : Prop) : (a \/ b) = (term861 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3806284 {A B : Type'} (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43994 : nat) (_43996 : B) (_43997 : B) : (term872 A B _43996 n1 f b _43995 _43997 _43994) = (term875 A B n1 f b _43995 _43994 _43996 _43997).
Proof. exact (@lem3806283 (term628 A B _43996 n1 f b _43995 _43997 _43994) (_43996 = _43997)). Qed.
Lemma lem3806286 (a : Prop) (b : Prop) : (term876 a b) = (term877 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3806287 {A B : Type'} (_43996 : B) (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) : (term878 A B _43996 n1 f b _43995 _43997 _43994) = (term879 A B _43996 n1 f b _43995 _43997 _43994).
Proof. exact (@lem3806286 (term843 A B f b _43995 _43996 n1) (term843 A B f b _43995 _43997 _43994)). Qed.
Lemma lem3806289 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3806290 {A B : Type'} (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43996 : B) (n1 : nat) : (term880 A B f b _43995 _43996 n1) = (@FINREC A B f b _43995 _43996 n1).
Proof. exact (@lem3806289 (@FINREC A B f b _43995 _43996 n1)). Qed.
Lemma lem3806291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3806292 {A B : Type'} (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43996 : B) (n1 : nat) : (term881 A B f b _43995 _43996 n1) = (term882 A B f b _43995 _43996 n1).
Proof. exact (MK_COMB (@lem3806291) (@lem3806290 A B f b _43995 _43996 n1)). Qed.
Lemma lem3806294 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3806295 {A B : Type'} (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) : (term880 A B f b _43995 _43997 _43994) = (@FINREC A B f b _43995 _43997 _43994).
Proof. exact (@lem3806294 (@FINREC A B f b _43995 _43997 _43994)). Qed.
Lemma lem3806296 {A B : Type'} (_43996 : B) (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) : (term879 A B _43996 n1 f b _43995 _43997 _43994) = (term634 A B _43996 n1 f b _43995 _43997 _43994).
Proof. exact (MK_COMB (@lem3806292 A B f b _43995 _43996 n1) (@lem3806295 A B f b _43995 _43997 _43994)). Qed.
Lemma lem3806297 {A B : Type'} (_43996 : B) (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) : (term878 A B _43996 n1 f b _43995 _43997 _43994) = (term634 A B _43996 n1 f b _43995 _43997 _43994).
Proof. exact (TRANS (@lem3806287 A B _43996 n1 f b _43995 _43997 _43994) (@lem3806296 A B _43996 n1 f b _43995 _43997 _43994)). Qed.
Lemma lem3806298 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3806299 {A B : Type'} (_43996 : B) (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43997 : B) (_43994 : nat) : (term883 A B _43996 n1 f b _43995 _43997 _43994) = (term884 A B _43996 n1 f b _43995 _43997 _43994).
Proof. exact (MK_COMB (@lem3806298) (@lem3806297 A B _43996 n1 f b _43995 _43997 _43994)). Qed.
Lemma lem3806300 {B : Type'} (_43996 : B) (_43997 : B) : (_43996 = _43997) = (_43996 = _43997).
Proof. exact (eq_refl (_43996 = _43997)). Qed.
Lemma lem3806301 {A B : Type'} (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43994 : nat) (_43996 : B) (_43997 : B) : (term875 A B n1 f b _43995 _43994 _43996 _43997) = (term885 A B n1 f b _43995 _43994 _43996 _43997).
Proof. exact (MK_COMB (@lem3806299 A B _43996 n1 f b _43995 _43997 _43994) (@lem3806300 B _43996 _43997)). Qed.
Lemma lem3806302 {A B : Type'} (n1 : nat) (f : type1411 A B) (b : B) (_43995 : A -> Prop) (_43994 : nat) (_43996 : B) (_43997 : B) : (term872 A B _43996 n1 f b _43995 _43997 _43994) = (term885 A B n1 f b _43995 _43994 _43996 _43997).
Proof. exact (TRANS (@lem3806284 A B n1 f b _43995 _43994 _43996 _43997) (@lem3806301 A B n1 f b _43995 _43994 _43996 _43997)). Qed.
Lemma lem3806304 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : @IN A x s) (h3 : term533 A B f b s x c n1) : term886 A B c n1 f b s w x n2.
Proof. exact (conj (@lem3806143 A B f b s x c n1 h3) (@lem3806203 A B b n2 a2 f w x s h1 h2)). Qed.
Lemma lem3806306 {A B : Type'} (_43995 : A -> Prop) (_43994 : nat) (_43996 : B) (_43997 : B) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term885 A B n1 f b _43995 _43994 _43996 _43997.
Proof. exact (EQ_MP (@lem3806302 A B n1 f b _43995 _43994 _43996 _43997) (@lem3806281 A B _43996 _43995 _43997 _43994 f b n1 h1)). Qed.
Lemma lem3806307 {A B : Type'} (_43995 : A -> Prop) (_43994 : nat) (_43996 : B) (_43997 : B) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term885 A B n1 f b _43995 _43994 _43996 _43997.
Proof. exact (@lem3806306 A B _43995 _43994 _43996 _43997 f b n1 h1). Qed.
Lemma lem3806308 {A B : Type'} (s : A -> Prop) (n2 : nat) (c : B) (w : A -> B) (x : A) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term887 A B n1 f b s n2 c w x.
Proof. exact (@lem3806307 A B (@DELETE A s x) n2 c (w x) f b n1 h1). Qed.
Lemma lem3806311 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : c = (w x).
Proof. exact (@lem3806308 A B s n2 c w x f b n1 h2 (@lem3806304 A B n2 a2 w f b s x c n1 h1 h3 h4)). Qed.
Lemma lem3806312 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : term888 A B c w x.
Proof. exact (fun h0 : term889 A B c w x => @lem3806311 A B n2 a2 w f b s x c n1 h1 h2 h3 h4). Qed.
Lemma lem3806314 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806315 {A B : Type'} (c : B) (w : A -> B) (x : A) : (term888 A B c w x) = (c = (w x)).
Proof. exact (@lem3806314 (c = (w x))). Qed.
Lemma lem3806316 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : c = (w x).
Proof. exact (EQ_MP (@lem3806315 A B c w x) (@lem3806312 A B n2 a2 w f b s x c n1 h1 h2 h3 h4)). Qed.
Lemma lem3806318 {B : Type'} (x : B -> B) : x = x.
Proof. exact (@lem21386 (B -> B) x). Qed.
Lemma lem3806319 {B : Type'} (x : B -> B) : x = x.
Proof. exact (@lem3806318 B x). Qed.
Lemma lem3806320 {A B : Type'} (f : type1411 A B) (x : A) : (@I (A -> B -> B) f x) = (@I (A -> B -> B) f x).
Proof. exact (@lem3806319 B (@I (A -> B -> B) f x)). Qed.
Lemma lem3806321 {A B : Type'} (f : type1411 A B) (x : A) : term890 A B f x.
Proof. exact (fun h0 : term891 A B f x => @lem3806320 A B f x). Qed.
Lemma lem3806323 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806324 {A B : Type'} (f : type1411 A B) (x : A) : (term890 A B f x) = ((@I (A -> B -> B) f x) = (@I (A -> B -> B) f x)).
Proof. exact (@lem3806323 ((@I (A -> B -> B) f x) = (@I (A -> B -> B) f x))). Qed.
Lemma lem3806325 {A B : Type'} (f : type1411 A B) (x : A) : (@I (A -> B -> B) f x) = (@I (A -> B -> B) f x).
Proof. exact (EQ_MP (@lem3806324 A B f x) (@lem3806321 A B f x)). Qed.
Lemma lem3806343 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3806344 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) : (term851 B _44123 _44124 _44125 _44126) = (term892 B _44124 _44126 _44123 _44125).
Proof. exact (@lem3806343 ((@I (B -> B) _44123 _44124) = (@I (B -> B) _44125 _44126)) (term893 B _44123 _44125)). Qed.
Lemma lem3806354 {B : Type'} (_44124 : B) (_44126 : B) : (term894 B _44124 _44126) = (term894 B _44124 _44126).
Proof. exact (eq_refl (term894 B _44124 _44126)). Qed.
Lemma lem3806355 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) : (term853 B _44123 _44124 _44125 _44126) = (term895 B _44124 _44126 _44123 _44125).
Proof. exact (MK_COMB (@lem3806354 B _44124 _44126) (@lem3806344 B _44124 _44126 _44123 _44125)). Qed.
Lemma lem3806359 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3806360 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) : (term895 B _44124 _44126 _44123 _44125) = (term896 B _44124 _44126 _44123 _44125).
Proof. exact (@lem3806359 ((@I (B -> B) _44123 _44124) = (@I (B -> B) _44125 _44126)) (term153 B _44124 _44126) (term893 B _44123 _44125)). Qed.
Lemma lem3806382 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) : (term853 B _44123 _44124 _44125 _44126) = (term896 B _44124 _44126 _44123 _44125).
Proof. exact (TRANS (@lem3806355 B _44124 _44126 _44123 _44125) (@lem3806360 B _44124 _44126 _44123 _44125)). Qed.
Lemma lem3806383 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3806384 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) : (term897 B _44123 _44124 _44125 _44126) = (term898 B _44124 _44126 _44123 _44125).
Proof. exact (MK_COMB (@lem3806383) (@lem3806382 B _44124 _44126 _44123 _44125)). Qed.
Lemma lem3806406 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) : (term896 B _44124 _44126 _44123 _44125) = (term896 B _44124 _44126 _44123 _44125).
Proof. exact (eq_refl (term896 B _44124 _44126 _44123 _44125)). Qed.
Lemma lem3806407 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) : ((term853 B _44123 _44124 _44125 _44126) = (term896 B _44124 _44126 _44123 _44125)) = ((term896 B _44124 _44126 _44123 _44125) = (term896 B _44124 _44126 _44123 _44125)).
Proof. exact (MK_COMB (@lem3806384 B _44124 _44126 _44123 _44125) (@lem3806406 B _44124 _44126 _44123 _44125)). Qed.
Lemma lem3806409 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3806410 (x : Prop) : (x = x) = True.
Proof. exact (@lem3806409 Prop x). Qed.
Lemma lem3806411 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) : ((term896 B _44124 _44126 _44123 _44125) = (term896 B _44124 _44126 _44123 _44125)) = True.
Proof. exact (@lem3806410 (term896 B _44124 _44126 _44123 _44125)). Qed.
Lemma lem3806412 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) : ((term853 B _44123 _44124 _44125 _44126) = (term896 B _44124 _44126 _44123 _44125)) = True.
Proof. exact (TRANS (@lem3806407 B _44124 _44126 _44123 _44125) (@lem3806411 B _44124 _44126 _44123 _44125)). Qed.
Lemma lem3806413 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) : True = ((term853 B _44123 _44124 _44125 _44126) = (term896 B _44124 _44126 _44123 _44125)).
Proof. exact (SYM (@lem3806412 B _44124 _44126 _44123 _44125)). Qed.
Lemma lem3806414 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) : (term853 B _44123 _44124 _44125 _44126) = (term896 B _44124 _44126 _44123 _44125).
Proof. exact (EQ_MP (@lem3806413 B _44124 _44126 _44123 _44125) (@lem0)). Qed.
Lemma lem3806415 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) : term896 B _44124 _44126 _44123 _44125.
Proof. exact (EQ_MP (@lem3806414 B _44124 _44126 _44123 _44125) (@lem3806124 B _44123 _44124 _44125 _44126)). Qed.
Lemma lem3806417 (b : Prop) (a : Prop) : (a \/ b) = (term861 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3806418 {B : Type'} (_44123 : B -> B) (_44124 : B) (_44125 : B -> B) (_44126 : B) : (term896 B _44124 _44126 _44123 _44125) = (term899 B _44123 _44124 _44125 _44126).
Proof. exact (@lem3806417 (term900 B _44124 _44126 _44123 _44125) ((@I (B -> B) _44123 _44124) = (@I (B -> B) _44125 _44126))). Qed.
Lemma lem3806420 (a : Prop) (b : Prop) : (term876 a b) = (term877 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3806421 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) : (term901 B _44124 _44126 _44123 _44125) = (term902 B _44124 _44126 _44123 _44125).
Proof. exact (@lem3806420 (term153 B _44124 _44126) (term893 B _44123 _44125)). Qed.
Lemma lem3806423 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3806424 {B : Type'} (_44124 : B) (_44126 : B) : (term903 B _44124 _44126) = (_44124 = _44126).
Proof. exact (@lem3806423 (_44124 = _44126)). Qed.
Lemma lem3806425 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3806426 {B : Type'} (_44124 : B) (_44126 : B) : (term904 B _44124 _44126) = (term93 B _44124 _44126).
Proof. exact (MK_COMB (@lem3806425) (@lem3806424 B _44124 _44126)). Qed.
Lemma lem3806428 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3806429 {B : Type'} (_44123 : B -> B) (_44125 : B -> B) : (term905 B _44123 _44125) = (_44123 = _44125).
Proof. exact (@lem3806428 (_44123 = _44125)). Qed.
Lemma lem3806430 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) : (term902 B _44124 _44126 _44123 _44125) = (term906 B _44124 _44126 _44123 _44125).
Proof. exact (MK_COMB (@lem3806426 B _44124 _44126) (@lem3806429 B _44123 _44125)). Qed.
Lemma lem3806431 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) : (term901 B _44124 _44126 _44123 _44125) = (term906 B _44124 _44126 _44123 _44125).
Proof. exact (TRANS (@lem3806421 B _44124 _44126 _44123 _44125) (@lem3806430 B _44124 _44126 _44123 _44125)). Qed.
Lemma lem3806432 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3806433 {B : Type'} (_44124 : B) (_44126 : B) (_44123 : B -> B) (_44125 : B -> B) : (term907 B _44124 _44126 _44123 _44125) = (term908 B _44124 _44126 _44123 _44125).
Proof. exact (MK_COMB (@lem3806432) (@lem3806431 B _44124 _44126 _44123 _44125)). Qed.
Lemma lem3806434 {B : Type'} (_44123 : B -> B) (_44124 : B) (_44125 : B -> B) (_44126 : B) : ((@I (B -> B) _44123 _44124) = (@I (B -> B) _44125 _44126)) = ((@I (B -> B) _44123 _44124) = (@I (B -> B) _44125 _44126)).
Proof. exact (eq_refl ((@I (B -> B) _44123 _44124) = (@I (B -> B) _44125 _44126))). Qed.
Lemma lem3806435 {B : Type'} (_44123 : B -> B) (_44124 : B) (_44125 : B -> B) (_44126 : B) : (term899 B _44123 _44124 _44125 _44126) = (term909 B _44123 _44124 _44125 _44126).
Proof. exact (MK_COMB (@lem3806433 B _44124 _44126 _44123 _44125) (@lem3806434 B _44123 _44124 _44125 _44126)). Qed.
Lemma lem3806436 {B : Type'} (_44123 : B -> B) (_44124 : B) (_44125 : B -> B) (_44126 : B) : (term896 B _44124 _44126 _44123 _44125) = (term909 B _44123 _44124 _44125 _44126).
Proof. exact (TRANS (@lem3806418 B _44123 _44124 _44125 _44126) (@lem3806435 B _44123 _44124 _44125 _44126)). Qed.
Lemma lem3806438 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : term910 A B c w f x.
Proof. exact (conj (@lem3806316 A B n2 a2 w f b s x c n1 h1 h2 h3 h4) (@lem3806325 A B f x)). Qed.
Lemma lem3806440 {B : Type'} (_44123 : B -> B) (_44124 : B) (_44125 : B -> B) (_44126 : B) : term909 B _44123 _44124 _44125 _44126.
Proof. exact (EQ_MP (@lem3806436 B _44123 _44124 _44125 _44126) (@lem3806415 B _44124 _44126 _44123 _44125)). Qed.
Lemma lem3806441 {B : Type'} (_44123 : B -> B) (_44124 : B) (_44125 : B -> B) (_44126 : B) : term909 B _44123 _44124 _44125 _44126.
Proof. exact (@lem3806440 B _44123 _44124 _44125 _44126). Qed.
Lemma lem3806442 {A B : Type'} (c : B) (f : type1411 A B) (w : A -> B) (x : A) : term911 A B c f w x.
Proof. exact (@lem3806441 B (@I (A -> B -> B) f x) c (@I (A -> B -> B) f x) (w x)). Qed.
Lemma lem3806445 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : (term337 A B f x c) = (term814 A B f w x).
Proof. exact (@lem3806442 A B c f w x (@lem3806438 A B n2 a2 w f b s x c n1 h1 h2 h3 h4)). Qed.
Lemma lem3806446 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : term912 A B c f w x.
Proof. exact (fun h0 : term913 A B c f w x => @lem3806445 A B n2 a2 w f b s x c n1 h1 h2 h3 h4). Qed.
Lemma lem3806448 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806449 {A B : Type'} (c : B) (f : type1411 A B) (w : A -> B) (x : A) : (term912 A B c f w x) = ((term337 A B f x c) = (term814 A B f w x)).
Proof. exact (@lem3806448 ((term337 A B f x c) = (term814 A B f w x))). Qed.
Lemma lem3806450 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : (term337 A B f x c) = (term814 A B f w x).
Proof. exact (EQ_MP (@lem3806449 A B c f w x) (@lem3806446 A B n2 a2 w f b s x c n1 h1 h2 h3 h4)). Qed.
Lemma lem3806452 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3806453 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3806452 B x). Qed.
Lemma lem3806454 {A B : Type'} (f : type1411 A B) (x : A) (c : B) : (term337 A B f x c) = (term337 A B f x c).
Proof. exact (@lem3806453 B (term337 A B f x c)). Qed.
Lemma lem3806455 {A B : Type'} (f : type1411 A B) (x : A) (c : B) : term914 A B f x c.
Proof. exact (fun h0 : term915 A B f x c => @lem3806454 A B f x c). Qed.
Lemma lem3806457 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806458 {A B : Type'} (f : type1411 A B) (x : A) (c : B) : (term914 A B f x c) = ((term337 A B f x c) = (term337 A B f x c)).
Proof. exact (@lem3806457 ((term337 A B f x c) = (term337 A B f x c))). Qed.
Lemma lem3806459 {A B : Type'} (f : type1411 A B) (x : A) (c : B) : (term337 A B f x c) = (term337 A B f x c).
Proof. exact (EQ_MP (@lem3806458 A B f x c) (@lem3806455 A B f x c)). Qed.
Lemma lem3806477 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3806478 {B : Type'} (y : B) (x : B) (z : B) : (term916 B x y z) = (term917 B y x z).
Proof. exact (@lem3806477 (y = z) (term153 B x z)). Qed.
Lemma lem3806488 {B : Type'} (x : B) (y : B) : (term894 B x y) = (term894 B x y).
Proof. exact (eq_refl (term894 B x y)). Qed.
Lemma lem3806489 {B : Type'} (y : B) (x : B) (z : B) : (term854 B x y z) = (term918 B y x z).
Proof. exact (MK_COMB (@lem3806488 B x y) (@lem3806478 B y x z)). Qed.
Lemma lem3806493 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3806494 {B : Type'} (y : B) (x : B) (z : B) : (term918 B y x z) = (term919 B y x z).
Proof. exact (@lem3806493 (y = z) (term153 B x y) (term153 B x z)). Qed.
Lemma lem3806516 {B : Type'} (y : B) (x : B) (z : B) : (term854 B x y z) = (term919 B y x z).
Proof. exact (TRANS (@lem3806489 B y x z) (@lem3806494 B y x z)). Qed.
Lemma lem3806517 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3806518 {B : Type'} (y : B) (x : B) (z : B) : (term920 B x y z) = (term921 B y x z).
Proof. exact (MK_COMB (@lem3806517) (@lem3806516 B y x z)). Qed.
Lemma lem3806540 {B : Type'} (y : B) (x : B) (z : B) : (term919 B y x z) = (term919 B y x z).
Proof. exact (eq_refl (term919 B y x z)). Qed.
Lemma lem3806541 {B : Type'} (y : B) (x : B) (z : B) : ((term854 B x y z) = (term919 B y x z)) = ((term919 B y x z) = (term919 B y x z)).
Proof. exact (MK_COMB (@lem3806518 B y x z) (@lem3806540 B y x z)). Qed.
Lemma lem3806543 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3806544 (x : Prop) : (x = x) = True.
Proof. exact (@lem3806543 Prop x). Qed.
Lemma lem3806545 {B : Type'} (y : B) (x : B) (z : B) : ((term919 B y x z) = (term919 B y x z)) = True.
Proof. exact (@lem3806544 (term919 B y x z)). Qed.
Lemma lem3806546 {B : Type'} (y : B) (x : B) (z : B) : ((term854 B x y z) = (term919 B y x z)) = True.
Proof. exact (TRANS (@lem3806541 B y x z) (@lem3806545 B y x z)). Qed.
Lemma lem3806547 {B : Type'} (y : B) (x : B) (z : B) : True = ((term854 B x y z) = (term919 B y x z)).
Proof. exact (SYM (@lem3806546 B y x z)). Qed.
Lemma lem3806548 {B : Type'} (y : B) (x : B) (z : B) : (term854 B x y z) = (term919 B y x z).
Proof. exact (EQ_MP (@lem3806547 B y x z) (@lem0)). Qed.
Lemma lem3806549 {B : Type'} (y : B) (x : B) (z : B) : term919 B y x z.
Proof. exact (EQ_MP (@lem3806548 B y x z) (@lem3806126 B x y z)). Qed.
Lemma lem3806551 (b : Prop) (a : Prop) : (a \/ b) = (term861 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3806552 {B : Type'} (x : B) (y : B) (z : B) : (term919 B y x z) = (term922 B x y z).
Proof. exact (@lem3806551 (term923 B y x z) (y = z)). Qed.
Lemma lem3806554 (a : Prop) (b : Prop) : (term876 a b) = (term877 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3806555 {B : Type'} (y : B) (x : B) (z : B) : (term924 B y x z) = (term925 B y x z).
Proof. exact (@lem3806554 (term153 B x y) (term153 B x z)). Qed.
Lemma lem3806557 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3806558 {B : Type'} (x : B) (y : B) : (term903 B x y) = (x = y).
Proof. exact (@lem3806557 (x = y)). Qed.
Lemma lem3806559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3806560 {B : Type'} (x : B) (y : B) : (term904 B x y) = (term93 B x y).
Proof. exact (MK_COMB (@lem3806559) (@lem3806558 B x y)). Qed.
Lemma lem3806562 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3806563 {B : Type'} (x : B) (z : B) : (term903 B x z) = (x = z).
Proof. exact (@lem3806562 (x = z)). Qed.
Lemma lem3806564 {B : Type'} (y : B) (x : B) (z : B) : (term925 B y x z) = (term926 B y x z).
Proof. exact (MK_COMB (@lem3806560 B x y) (@lem3806563 B x z)). Qed.
Lemma lem3806565 {B : Type'} (y : B) (x : B) (z : B) : (term924 B y x z) = (term926 B y x z).
Proof. exact (TRANS (@lem3806555 B y x z) (@lem3806564 B y x z)). Qed.
Lemma lem3806566 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3806567 {B : Type'} (y : B) (x : B) (z : B) : (term927 B y x z) = (term928 B y x z).
Proof. exact (MK_COMB (@lem3806566) (@lem3806565 B y x z)). Qed.
Lemma lem3806568 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3806569 {B : Type'} (x : B) (y : B) (z : B) : (term922 B x y z) = (term929 B x y z).
Proof. exact (MK_COMB (@lem3806567 B y x z) (@lem3806568 B y z)). Qed.
Lemma lem3806570 {B : Type'} (x : B) (y : B) (z : B) : (term919 B y x z) = (term929 B x y z).
Proof. exact (TRANS (@lem3806552 B x y z) (@lem3806569 B x y z)). Qed.
Lemma lem3806572 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : term930 A B w f x c.
Proof. exact (conj (@lem3806450 A B n2 a2 w f b s x c n1 h1 h2 h3 h4) (@lem3806459 A B f x c)). Qed.
Lemma lem3806574 {B : Type'} (x : B) (y : B) (z : B) : term929 B x y z.
Proof. exact (EQ_MP (@lem3806570 B x y z) (@lem3806549 B y x z)). Qed.
Lemma lem3806575 {B : Type'} (x : B) (y : B) (z : B) : term929 B x y z.
Proof. exact (@lem3806574 B x y z). Qed.
Lemma lem3806576 {A B : Type'} (w : A -> B) (f : type1411 A B) (x : A) (c : B) : term931 A B w f x c.
Proof. exact (@lem3806575 B (term337 A B f x c) (term814 A B f w x) (term337 A B f x c)). Qed.
Lemma lem3806579 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : (term814 A B f w x) = (term337 A B f x c).
Proof. exact (@lem3806576 A B w f x c (@lem3806572 A B n2 a2 w f b s x c n1 h1 h2 h3 h4)). Qed.
Lemma lem3806580 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : term932 A B w f x c.
Proof. exact (fun h0 : term933 A B w f x c => @lem3806579 A B n2 a2 w f b s x c n1 h1 h2 h3 h4). Qed.
Lemma lem3806582 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806583 {A B : Type'} (w : A -> B) (f : type1411 A B) (x : A) (c : B) : (term932 A B w f x c) = ((term814 A B f w x) = (term337 A B f x c)).
Proof. exact (@lem3806582 ((term814 A B f w x) = (term337 A B f x c))). Qed.
Lemma lem3806584 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : (term814 A B f w x) = (term337 A B f x c).
Proof. exact (EQ_MP (@lem3806583 A B w f x c) (@lem3806580 A B n2 a2 w f b s x c n1 h1 h2 h3 h4)). Qed.
Lemma lem3806586 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3806587 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term857 A x s.
Proof. exact (fun h0 : term662 A x s => @lem3806586 A x s h1). Qed.
Lemma lem3806589 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806590 {A : Type'} (x : A) (s : A -> Prop) : (term857 A x s) = (@IN A x s).
Proof. exact (@lem3806589 (@IN A x s)). Qed.
Lemma lem3806591 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem3806590 A x s) (@lem3806587 A x s h1)). Qed.
Lemma lem3806597 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3806598 {A B : Type'} (a2 : B) (f : type1411 A B) (w : A -> B) (_44001 : A) (s : A -> Prop) : (term848 A B s a2 f w _44001) = (term934 A B a2 f w _44001 s).
Proof. exact (@lem3806597 (a2 = (term814 A B f w _44001)) (term662 A _44001 s)). Qed.
Lemma lem3806606 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3806607 {A B : Type'} (a2 : B) (f : type1411 A B) (w : A -> B) (_44001 : A) (s : A -> Prop) : (term935 A B s a2 f w _44001) = (term936 A B a2 f w _44001 s).
Proof. exact (MK_COMB (@lem3806606) (@lem3806598 A B a2 f w _44001 s)). Qed.
Lemma lem3806615 {A B : Type'} (a2 : B) (f : type1411 A B) (w : A -> B) (_44001 : A) (s : A -> Prop) : (term934 A B a2 f w _44001 s) = (term934 A B a2 f w _44001 s).
Proof. exact (eq_refl (term934 A B a2 f w _44001 s)). Qed.
Lemma lem3806616 {A B : Type'} (a2 : B) (f : type1411 A B) (w : A -> B) (_44001 : A) (s : A -> Prop) : ((term848 A B s a2 f w _44001) = (term934 A B a2 f w _44001 s)) = ((term934 A B a2 f w _44001 s) = (term934 A B a2 f w _44001 s)).
Proof. exact (MK_COMB (@lem3806607 A B a2 f w _44001 s) (@lem3806615 A B a2 f w _44001 s)). Qed.
Lemma lem3806618 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3806619 (x : Prop) : (x = x) = True.
Proof. exact (@lem3806618 Prop x). Qed.
Lemma lem3806620 {A B : Type'} (a2 : B) (f : type1411 A B) (w : A -> B) (_44001 : A) (s : A -> Prop) : ((term934 A B a2 f w _44001 s) = (term934 A B a2 f w _44001 s)) = True.
Proof. exact (@lem3806619 (term934 A B a2 f w _44001 s)). Qed.
Lemma lem3806621 {A B : Type'} (a2 : B) (f : type1411 A B) (w : A -> B) (_44001 : A) (s : A -> Prop) : ((term848 A B s a2 f w _44001) = (term934 A B a2 f w _44001 s)) = True.
Proof. exact (TRANS (@lem3806616 A B a2 f w _44001 s) (@lem3806620 A B a2 f w _44001 s)). Qed.
Lemma lem3806622 {A B : Type'} (a2 : B) (f : type1411 A B) (w : A -> B) (_44001 : A) (s : A -> Prop) : True = ((term848 A B s a2 f w _44001) = (term934 A B a2 f w _44001 s)).
Proof. exact (SYM (@lem3806621 A B a2 f w _44001 s)). Qed.
Lemma lem3806623 {A B : Type'} (a2 : B) (f : type1411 A B) (w : A -> B) (_44001 : A) (s : A -> Prop) : (term848 A B s a2 f w _44001) = (term934 A B a2 f w _44001 s).
Proof. exact (EQ_MP (@lem3806622 A B a2 f w _44001 s) (@lem0)). Qed.
Lemma lem3806624 {A B : Type'} (_44001 : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term934 A B a2 f w _44001 s.
Proof. exact (EQ_MP (@lem3806623 A B a2 f w _44001 s) (@lem3805695 A B _44001 b s n2 a2 f w h1)). Qed.
Lemma lem3806626 (b : Prop) (a : Prop) : (a \/ b) = (term861 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3806627 {A B : Type'} (s : A -> Prop) (a2 : B) (f : type1411 A B) (w : A -> B) (_44001 : A) : (term934 A B a2 f w _44001 s) = (term937 A B s a2 f w _44001).
Proof. exact (@lem3806626 (term662 A _44001 s) (a2 = (term814 A B f w _44001))). Qed.
Lemma lem3806629 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3806630 {A : Type'} (_44001 : A) (s : A -> Prop) : (term863 A _44001 s) = (@IN A _44001 s).
Proof. exact (@lem3806629 (@IN A _44001 s)). Qed.
Lemma lem3806631 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3806632 {A : Type'} (_44001 : A) (s : A -> Prop) : (term864 A _44001 s) = (term548 A _44001 s).
Proof. exact (MK_COMB (@lem3806631) (@lem3806630 A _44001 s)). Qed.
Lemma lem3806633 {A B : Type'} (a2 : B) (f : type1411 A B) (w : A -> B) (_44001 : A) : (a2 = (term814 A B f w _44001)) = (a2 = (term814 A B f w _44001)).
Proof. exact (eq_refl (a2 = (term814 A B f w _44001))). Qed.
Lemma lem3806634 {A B : Type'} (s : A -> Prop) (a2 : B) (f : type1411 A B) (w : A -> B) (_44001 : A) : (term937 A B s a2 f w _44001) = (term938 A B s a2 f w _44001).
Proof. exact (MK_COMB (@lem3806632 A _44001 s) (@lem3806633 A B a2 f w _44001)). Qed.
Lemma lem3806635 {A B : Type'} (s : A -> Prop) (a2 : B) (f : type1411 A B) (w : A -> B) (_44001 : A) : (term934 A B a2 f w _44001 s) = (term938 A B s a2 f w _44001).
Proof. exact (TRANS (@lem3806627 A B s a2 f w _44001) (@lem3806634 A B s a2 f w _44001)). Qed.
Lemma lem3806638 {A B : Type'} (_44001 : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term938 A B s a2 f w _44001.
Proof. exact (EQ_MP (@lem3806635 A B s a2 f w _44001) (@lem3806624 A B _44001 b s n2 a2 f w h1)). Qed.
Lemma lem3806639 {A B : Type'} (_44001 : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term938 A B s a2 f w _44001.
Proof. exact (@lem3806638 A B _44001 b s n2 a2 f w h1). Qed.
Lemma lem3806640 {A B : Type'} (x : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term938 A B s a2 f w x.
Proof. exact (@lem3806639 A B x b s n2 a2 f w h1). Qed.
Lemma lem3806643 {A B : Type'} (b : B) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) (s : A -> Prop) (h1 : term691 A B b s n2 a2 f w) (h2 : @IN A x s) : a2 = (term814 A B f w x).
Proof. exact (@lem3806640 A B x b s n2 a2 f w h1 (@lem3806591 A x s h2)). Qed.
Lemma lem3806644 {A B : Type'} (b : B) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) (s : A -> Prop) (h1 : term691 A B b s n2 a2 f w) (h2 : @IN A x s) : term939 A B a2 f w x.
Proof. exact (fun h0 : term940 A B a2 f w x => @lem3806643 A B b n2 a2 f w x s h1 h2). Qed.
Lemma lem3806646 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806647 {A B : Type'} (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) : (term939 A B a2 f w x) = (a2 = (term814 A B f w x)).
Proof. exact (@lem3806646 (a2 = (term814 A B f w x))). Qed.
Lemma lem3806648 {A B : Type'} (b : B) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) (s : A -> Prop) (h1 : term691 A B b s n2 a2 f w) (h2 : @IN A x s) : a2 = (term814 A B f w x).
Proof. exact (EQ_MP (@lem3806647 A B a2 f w x) (@lem3806644 A B b n2 a2 f w x s h1 h2)). Qed.
Lemma lem3806650 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem3806651 {B : Type'} (x : B) : x = x.
Proof. exact (@lem3806650 B x). Qed.
Lemma lem3806652 {B : Type'} (a2 : B) : a2 = a2.
Proof. exact (@lem3806651 B a2). Qed.
Lemma lem3806653 {B : Type'} (a2 : B) : term163 B a2.
Proof. exact (fun h0 : term161 B a2 => @lem3806652 B a2). Qed.
Lemma lem3806655 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806656 {B : Type'} (a2 : B) : (term163 B a2) = (a2 = a2).
Proof. exact (@lem3806655 (a2 = a2)). Qed.
Lemma lem3806657 {B : Type'} (a2 : B) : a2 = a2.
Proof. exact (EQ_MP (@lem3806656 B a2) (@lem3806653 B a2)). Qed.
Lemma lem3806658 {A B : Type'} (b : B) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) (s : A -> Prop) (h1 : term691 A B b s n2 a2 f w) (h2 : @IN A x s) : term941 A B f w x a2.
Proof. exact (conj (@lem3806648 A B b n2 a2 f w x s h1 h2) (@lem3806657 B a2)). Qed.
Lemma lem3806660 {B : Type'} (x : B) (y : B) (z : B) : term929 B x y z.
Proof. exact (EQ_MP (@lem3806570 B x y z) (@lem3806549 B y x z)). Qed.
Lemma lem3806661 {B : Type'} (x : B) (y : B) (z : B) : term929 B x y z.
Proof. exact (@lem3806660 B x y z). Qed.
Lemma lem3806662 {A B : Type'} (f : type1411 A B) (w : A -> B) (x : A) (a2 : B) : term942 A B f w x a2.
Proof. exact (@lem3806661 B a2 (term814 A B f w x) a2). Qed.
Lemma lem3806665 {A B : Type'} (b : B) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) (s : A -> Prop) (h1 : term691 A B b s n2 a2 f w) (h2 : @IN A x s) : (term814 A B f w x) = a2.
Proof. exact (@lem3806662 A B f w x a2 (@lem3806658 A B b n2 a2 f w x s h1 h2)). Qed.
Lemma lem3806666 {A B : Type'} (b : B) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) (s : A -> Prop) (h1 : term691 A B b s n2 a2 f w) (h2 : @IN A x s) : term943 A B f w x a2.
Proof. exact (fun h0 : term944 A B f w x a2 => @lem3806665 A B b n2 a2 f w x s h1 h2). Qed.
Lemma lem3806668 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806669 {A B : Type'} (f : type1411 A B) (w : A -> B) (x : A) (a2 : B) : (term943 A B f w x a2) = ((term814 A B f w x) = a2).
Proof. exact (@lem3806668 ((term814 A B f w x) = a2)). Qed.
Lemma lem3806670 {A B : Type'} (b : B) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) (s : A -> Prop) (h1 : term691 A B b s n2 a2 f w) (h2 : @IN A x s) : (term814 A B f w x) = a2.
Proof. exact (EQ_MP (@lem3806669 A B f w x a2) (@lem3806666 A B b n2 a2 f w x s h1 h2)). Qed.
Lemma lem3806671 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : term945 A B c f w x a2.
Proof. exact (conj (@lem3806584 A B n2 a2 w f b s x c n1 h1 h2 h3 h4) (@lem3806670 A B b n2 a2 f w x s h1 h3)). Qed.
Lemma lem3806673 {B : Type'} (x : B) (y : B) (z : B) : term929 B x y z.
Proof. exact (EQ_MP (@lem3806570 B x y z) (@lem3806549 B y x z)). Qed.
Lemma lem3806674 {B : Type'} (x : B) (y : B) (z : B) : term929 B x y z.
Proof. exact (@lem3806673 B x y z). Qed.
Lemma lem3806675 {A B : Type'} (w : A -> B) (f : type1411 A B) (x : A) (c : B) (a2 : B) : term946 A B w f x c a2.
Proof. exact (@lem3806674 B (term814 A B f w x) (term337 A B f x c) a2). Qed.
Lemma lem3806678 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : (term337 A B f x c) = a2.
Proof. exact (@lem3806675 A B w f x c a2 (@lem3806671 A B n2 a2 w f b s x c n1 h1 h2 h3 h4)). Qed.
Lemma lem3806679 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : term947 A B f x c a2.
Proof. exact (fun h0 : term846 A B f x c a2 => @lem3806678 A B n2 a2 w f b s x c n1 h1 h2 h3 h4). Qed.
Lemma lem3806681 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806682 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (a2 : B) : (term947 A B f x c a2) = ((term337 A B f x c) = a2).
Proof. exact (@lem3806681 ((term337 A B f x c) = a2)). Qed.
Lemma lem3806683 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : (term337 A B f x c) = a2.
Proof. exact (EQ_MP (@lem3806682 A B f x c a2) (@lem3806679 A B n2 a2 w f b s x c n1 h1 h2 h3 h4)). Qed.
Lemma lem3806686 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3806688 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (a2 : B) : (term846 A B f x c a2) = (term948 A B f x c a2).
Proof. exact (@lem3806686 ((term337 A B f x c) = a2)). Qed.
Lemma lem3806691 {A B : Type'} (a2 : B) (a1 : B) (f : type1411 A B) (x : A) (c : B) (h1 : term153 B a1 a2) (h2 : a1 = (f x c)) : term948 A B f x c a2.
Proof. exact (EQ_MP (@lem3806688 A B f x c a2) (@lem3805612 A B a2 a1 f x c h1 h2)). Qed.
Lemma lem3806694 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : False.
Proof. exact (@lem3806691 A B a2 a1 f x c h3 h4 (@lem3806683 A B n2 a2 w f b s x c n1 h1 h2 h5 h6)). Qed.
Lemma lem3806695 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : term166.
Proof. exact (fun h0 : ~ False => @lem3806694 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6). Qed.
Lemma lem3806697 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806698 : term166 = False.
Proof. exact (@lem3806697 False). Qed.
Lemma lem3806699 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3806698) (@lem3806695 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem3806811 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem3806812 (_44155 : nat) (_44156 : nat) (h1 : _44155 = _44156) : _44155 = _44156.
Proof. exact (h1). Qed.
Lemma lem3806813 (_44155 : nat) (_44156 : nat) (h1 : _44155 = _44156) : (S _44155) = (S _44156).
Proof. exact (MK_COMB (@lem3806811) (@lem3806812 _44155 _44156 h1)). Qed.
Lemma lem3806814 (_44155 : nat) (_44156 : nat) : term949 _44155 _44156.
Proof. exact (fun h0 : _44155 = _44156 => @lem3806813 _44155 _44156 h0). Qed.
Lemma lem3806816 (a : Prop) (b : Prop) : (a -> b) = (term850 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3806817 (_44155 : nat) (_44156 : nat) : (term949 _44155 _44156) = (term950 _44155 _44156).
Proof. exact (@lem3806816 (_44155 = _44156) ((S _44155) = (S _44156))). Qed.
Lemma lem3806818 (_44155 : nat) (_44156 : nat) : term950 _44155 _44156.
Proof. exact (EQ_MP (@lem3806817 _44155 _44156) (@lem3806814 _44155 _44156)). Qed.
Lemma lem3806877 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term533 A B f b s x c n1) : term533 A B f b s x c n1.
Proof. exact (h1). Qed.
Lemma lem3806878 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term533 A B f b s x c n1) : term855 A B f b s x c n1.
Proof. exact (fun h0 : term856 A B f b s x c n1 => @lem3806877 A B f b s x c n1 h1). Qed.
Lemma lem3806880 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806881 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) : (term855 A B f b s x c n1) = (term533 A B f b s x c n1).
Proof. exact (@lem3806880 (term533 A B f b s x c n1)). Qed.
Lemma lem3806882 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term533 A B f b s x c n1) : term533 A B f b s x c n1.
Proof. exact (EQ_MP (@lem3806881 A B f b s x c n1) (@lem3806878 A B f b s x c n1 h1)). Qed.
Lemma lem3806884 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3806885 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term857 A x s.
Proof. exact (fun h0 : term662 A x s => @lem3806884 A x s h1). Qed.
Lemma lem3806887 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806888 {A : Type'} (x : A) (s : A -> Prop) : (term857 A x s) = (@IN A x s).
Proof. exact (@lem3806887 (@IN A x s)). Qed.
Lemma lem3806889 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem3806888 A x s) (@lem3806885 A x s h1)). Qed.
Lemma lem3806895 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3806896 {A B : Type'} (f : type1411 A B) (b : B) (w : A -> B) (n2 : nat) (_44018 : A) (s : A -> Prop) : (term847 A B f b s w _44018 n2) = (term858 A B f b w n2 _44018 s).
Proof. exact (@lem3806895 (term831 A B f b s w _44018 n2) (term662 A _44018 s)). Qed.
Lemma lem3806902 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3806903 {A B : Type'} (f : type1411 A B) (b : B) (w : A -> B) (n2 : nat) (_44018 : A) (s : A -> Prop) : (term859 A B f b s w _44018 n2) = (term860 A B f b w n2 _44018 s).
Proof. exact (MK_COMB (@lem3806902) (@lem3806896 A B f b w n2 _44018 s)). Qed.
Lemma lem3806909 {A B : Type'} (f : type1411 A B) (b : B) (w : A -> B) (n2 : nat) (_44018 : A) (s : A -> Prop) : (term858 A B f b w n2 _44018 s) = (term858 A B f b w n2 _44018 s).
Proof. exact (eq_refl (term858 A B f b w n2 _44018 s)). Qed.
Lemma lem3806910 {A B : Type'} (f : type1411 A B) (b : B) (w : A -> B) (n2 : nat) (_44018 : A) (s : A -> Prop) : ((term847 A B f b s w _44018 n2) = (term858 A B f b w n2 _44018 s)) = ((term858 A B f b w n2 _44018 s) = (term858 A B f b w n2 _44018 s)).
Proof. exact (MK_COMB (@lem3806903 A B f b w n2 _44018 s) (@lem3806909 A B f b w n2 _44018 s)). Qed.
Lemma lem3806912 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3806913 (x : Prop) : (x = x) = True.
Proof. exact (@lem3806912 Prop x). Qed.
Lemma lem3806914 {A B : Type'} (f : type1411 A B) (b : B) (w : A -> B) (n2 : nat) (_44018 : A) (s : A -> Prop) : ((term858 A B f b w n2 _44018 s) = (term858 A B f b w n2 _44018 s)) = True.
Proof. exact (@lem3806913 (term858 A B f b w n2 _44018 s)). Qed.
Lemma lem3806915 {A B : Type'} (f : type1411 A B) (b : B) (w : A -> B) (n2 : nat) (_44018 : A) (s : A -> Prop) : ((term847 A B f b s w _44018 n2) = (term858 A B f b w n2 _44018 s)) = True.
Proof. exact (TRANS (@lem3806910 A B f b w n2 _44018 s) (@lem3806914 A B f b w n2 _44018 s)). Qed.
Lemma lem3806916 {A B : Type'} (f : type1411 A B) (b : B) (w : A -> B) (n2 : nat) (_44018 : A) (s : A -> Prop) : True = ((term847 A B f b s w _44018 n2) = (term858 A B f b w n2 _44018 s)).
Proof. exact (SYM (@lem3806915 A B f b w n2 _44018 s)). Qed.
Lemma lem3806917 {A B : Type'} (f : type1411 A B) (b : B) (w : A -> B) (n2 : nat) (_44018 : A) (s : A -> Prop) : (term847 A B f b s w _44018 n2) = (term858 A B f b w n2 _44018 s).
Proof. exact (EQ_MP (@lem3806916 A B f b w n2 _44018 s) (@lem0)). Qed.
Lemma lem3806918 {A B : Type'} (_44018 : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term858 A B f b w n2 _44018 s.
Proof. exact (EQ_MP (@lem3806917 A B f b w n2 _44018 s) (@lem3805890 A B _44018 b s n2 a2 f w h1)). Qed.
Lemma lem3806920 (b : Prop) (a : Prop) : (a \/ b) = (term861 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3806921 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (w : A -> B) (_44018 : A) (n2 : nat) : (term858 A B f b w n2 _44018 s) = (term862 A B f b s w _44018 n2).
Proof. exact (@lem3806920 (term662 A _44018 s) (term831 A B f b s w _44018 n2)). Qed.
Lemma lem3806923 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3806924 {A : Type'} (_44018 : A) (s : A -> Prop) : (term863 A _44018 s) = (@IN A _44018 s).
Proof. exact (@lem3806923 (@IN A _44018 s)). Qed.
Lemma lem3806925 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3806926 {A : Type'} (_44018 : A) (s : A -> Prop) : (term864 A _44018 s) = (term548 A _44018 s).
Proof. exact (MK_COMB (@lem3806925) (@lem3806924 A _44018 s)). Qed.
Lemma lem3806927 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (w : A -> B) (_44018 : A) (n2 : nat) : (term831 A B f b s w _44018 n2) = (term831 A B f b s w _44018 n2).
Proof. exact (eq_refl (term831 A B f b s w _44018 n2)). Qed.
Lemma lem3806928 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (w : A -> B) (_44018 : A) (n2 : nat) : (term862 A B f b s w _44018 n2) = (term865 A B f b s w _44018 n2).
Proof. exact (MK_COMB (@lem3806926 A _44018 s) (@lem3806927 A B f b s w _44018 n2)). Qed.
Lemma lem3806929 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (w : A -> B) (_44018 : A) (n2 : nat) : (term858 A B f b w n2 _44018 s) = (term865 A B f b s w _44018 n2).
Proof. exact (TRANS (@lem3806921 A B f b s w _44018 n2) (@lem3806928 A B f b s w _44018 n2)). Qed.
Lemma lem3806932 {A B : Type'} (_44018 : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term865 A B f b s w _44018 n2.
Proof. exact (EQ_MP (@lem3806929 A B f b s w _44018 n2) (@lem3806918 A B _44018 b s n2 a2 f w h1)). Qed.
Lemma lem3806933 {A B : Type'} (_44018 : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term865 A B f b s w _44018 n2.
Proof. exact (@lem3806932 A B _44018 b s n2 a2 f w h1). Qed.
Lemma lem3806934 {A B : Type'} (x : A) (b : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (h1 : term691 A B b s n2 a2 f w) : term865 A B f b s w x n2.
Proof. exact (@lem3806933 A B x b s n2 a2 f w h1). Qed.
Lemma lem3806937 {A B : Type'} (b : B) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) (s : A -> Prop) (h1 : term691 A B b s n2 a2 f w) (h2 : @IN A x s) : term831 A B f b s w x n2.
Proof. exact (@lem3806934 A B x b s n2 a2 f w h1 (@lem3806889 A x s h2)). Qed.
Lemma lem3806938 {A B : Type'} (b : B) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) (s : A -> Prop) (h1 : term691 A B b s n2 a2 f w) (h2 : @IN A x s) : term866 A B f b s w x n2.
Proof. exact (fun h0 : term867 A B f b s w x n2 => @lem3806937 A B b n2 a2 f w x s h1 h2). Qed.
Lemma lem3806940 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3806941 {A B : Type'} (f : type1411 A B) (b : B) (s : A -> Prop) (w : A -> B) (x : A) (n2 : nat) : (term866 A B f b s w x n2) = (term831 A B f b s w x n2).
Proof. exact (@lem3806940 (term831 A B f b s w x n2)). Qed.
Lemma lem3806942 {A B : Type'} (b : B) (n2 : nat) (a2 : B) (f : type1411 A B) (w : A -> B) (x : A) (s : A -> Prop) (h1 : term691 A B b s n2 a2 f w) (h2 : @IN A x s) : term831 A B f b s w x n2.
Proof. exact (EQ_MP (@lem3806941 A B f b s w x n2) (@lem3806938 A B b n2 a2 f w x s h1 h2)). Qed.
Lemma lem3806958 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3806959 {A B : Type'} (n1 : nat) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) : (term951 A B f b _44012 _44014 n1 _44011) = (term952 A B n1 f b _44012 _44014 _44011).
Proof. exact (@lem3806958 (n1 = _44011) (term843 A B f b _44012 _44014 _44011)). Qed.
Lemma lem3806967 {A B : Type'} (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44013 : B) (n1 : nat) : (term870 A B f b _44012 _44013 n1) = (term870 A B f b _44012 _44013 n1).
Proof. exact (eq_refl (term870 A B f b _44012 _44013 n1)). Qed.
Lemma lem3806968 {A B : Type'} (_44013 : B) (n1 : nat) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) : (term844 A B _44013 f b _44012 _44014 n1 _44011) = (term953 A B _44013 n1 f b _44012 _44014 _44011).
Proof. exact (MK_COMB (@lem3806967 A B f b _44012 _44013 n1) (@lem3806959 A B n1 f b _44012 _44014 _44011)). Qed.
Lemma lem3806972 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3806973 {A B : Type'} (_44013 : B) (n1 : nat) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) : (term953 A B _44013 n1 f b _44012 _44014 _44011) = (term954 A B _44013 n1 f b _44012 _44014 _44011).
Proof. exact (@lem3806972 (n1 = _44011) (term843 A B f b _44012 _44013 n1) (term843 A B f b _44012 _44014 _44011)). Qed.
Lemma lem3806991 {A B : Type'} (_44013 : B) (n1 : nat) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) : (term844 A B _44013 f b _44012 _44014 n1 _44011) = (term954 A B _44013 n1 f b _44012 _44014 _44011).
Proof. exact (TRANS (@lem3806968 A B _44013 n1 f b _44012 _44014 _44011) (@lem3806973 A B _44013 n1 f b _44012 _44014 _44011)). Qed.
Lemma lem3806992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3806993 {A B : Type'} (_44013 : B) (n1 : nat) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) : (term955 A B _44013 f b _44012 _44014 n1 _44011) = (term956 A B _44013 n1 f b _44012 _44014 _44011).
Proof. exact (MK_COMB (@lem3806992) (@lem3806991 A B _44013 n1 f b _44012 _44014 _44011)). Qed.
Lemma lem3807011 {A B : Type'} (_44013 : B) (n1 : nat) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) : (term954 A B _44013 n1 f b _44012 _44014 _44011) = (term954 A B _44013 n1 f b _44012 _44014 _44011).
Proof. exact (eq_refl (term954 A B _44013 n1 f b _44012 _44014 _44011)). Qed.
Lemma lem3807012 {A B : Type'} (_44013 : B) (n1 : nat) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) : ((term844 A B _44013 f b _44012 _44014 n1 _44011) = (term954 A B _44013 n1 f b _44012 _44014 _44011)) = ((term954 A B _44013 n1 f b _44012 _44014 _44011) = (term954 A B _44013 n1 f b _44012 _44014 _44011)).
Proof. exact (MK_COMB (@lem3806993 A B _44013 n1 f b _44012 _44014 _44011) (@lem3807011 A B _44013 n1 f b _44012 _44014 _44011)). Qed.
Lemma lem3807014 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3807015 (x : Prop) : (x = x) = True.
Proof. exact (@lem3807014 Prop x). Qed.
Lemma lem3807016 {A B : Type'} (_44013 : B) (n1 : nat) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) : ((term954 A B _44013 n1 f b _44012 _44014 _44011) = (term954 A B _44013 n1 f b _44012 _44014 _44011)) = True.
Proof. exact (@lem3807015 (term954 A B _44013 n1 f b _44012 _44014 _44011)). Qed.
Lemma lem3807017 {A B : Type'} (_44013 : B) (n1 : nat) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) : ((term844 A B _44013 f b _44012 _44014 n1 _44011) = (term954 A B _44013 n1 f b _44012 _44014 _44011)) = True.
Proof. exact (TRANS (@lem3807012 A B _44013 n1 f b _44012 _44014 _44011) (@lem3807016 A B _44013 n1 f b _44012 _44014 _44011)). Qed.
Lemma lem3807018 {A B : Type'} (_44013 : B) (n1 : nat) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) : True = ((term844 A B _44013 f b _44012 _44014 n1 _44011) = (term954 A B _44013 n1 f b _44012 _44014 _44011)).
Proof. exact (SYM (@lem3807017 A B _44013 n1 f b _44012 _44014 _44011)). Qed.
Lemma lem3807019 {A B : Type'} (_44013 : B) (n1 : nat) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) : (term844 A B _44013 f b _44012 _44014 n1 _44011) = (term954 A B _44013 n1 f b _44012 _44014 _44011).
Proof. exact (EQ_MP (@lem3807018 A B _44013 n1 f b _44012 _44014 _44011) (@lem0)). Qed.
Lemma lem3807020 {A B : Type'} (_44013 : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term954 A B _44013 n1 f b _44012 _44014 _44011.
Proof. exact (EQ_MP (@lem3807019 A B _44013 n1 f b _44012 _44014 _44011) (@lem3805960 A B _44013 _44012 _44014 _44011 f b n1 h1)). Qed.
Lemma lem3807022 (b : Prop) (a : Prop) : (a \/ b) = (term861 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3807023 {A B : Type'} (_44013 : B) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (n1 : nat) (_44011 : nat) : (term954 A B _44013 n1 f b _44012 _44014 _44011) = (term957 A B _44013 f b _44012 _44014 n1 _44011).
Proof. exact (@lem3807022 (term628 A B _44013 n1 f b _44012 _44014 _44011) (n1 = _44011)). Qed.
Lemma lem3807025 (a : Prop) (b : Prop) : (term876 a b) = (term877 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3807026 {A B : Type'} (_44013 : B) (n1 : nat) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) : (term878 A B _44013 n1 f b _44012 _44014 _44011) = (term879 A B _44013 n1 f b _44012 _44014 _44011).
Proof. exact (@lem3807025 (term843 A B f b _44012 _44013 n1) (term843 A B f b _44012 _44014 _44011)). Qed.
Lemma lem3807028 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3807029 {A B : Type'} (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44013 : B) (n1 : nat) : (term880 A B f b _44012 _44013 n1) = (@FINREC A B f b _44012 _44013 n1).
Proof. exact (@lem3807028 (@FINREC A B f b _44012 _44013 n1)). Qed.
Lemma lem3807030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3807031 {A B : Type'} (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44013 : B) (n1 : nat) : (term881 A B f b _44012 _44013 n1) = (term882 A B f b _44012 _44013 n1).
Proof. exact (MK_COMB (@lem3807030) (@lem3807029 A B f b _44012 _44013 n1)). Qed.
Lemma lem3807033 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3807034 {A B : Type'} (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) : (term880 A B f b _44012 _44014 _44011) = (@FINREC A B f b _44012 _44014 _44011).
Proof. exact (@lem3807033 (@FINREC A B f b _44012 _44014 _44011)). Qed.
Lemma lem3807035 {A B : Type'} (_44013 : B) (n1 : nat) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) : (term879 A B _44013 n1 f b _44012 _44014 _44011) = (term634 A B _44013 n1 f b _44012 _44014 _44011).
Proof. exact (MK_COMB (@lem3807031 A B f b _44012 _44013 n1) (@lem3807034 A B f b _44012 _44014 _44011)). Qed.
Lemma lem3807036 {A B : Type'} (_44013 : B) (n1 : nat) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) : (term878 A B _44013 n1 f b _44012 _44014 _44011) = (term634 A B _44013 n1 f b _44012 _44014 _44011).
Proof. exact (TRANS (@lem3807026 A B _44013 n1 f b _44012 _44014 _44011) (@lem3807035 A B _44013 n1 f b _44012 _44014 _44011)). Qed.
Lemma lem3807037 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3807038 {A B : Type'} (_44013 : B) (n1 : nat) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) : (term883 A B _44013 n1 f b _44012 _44014 _44011) = (term884 A B _44013 n1 f b _44012 _44014 _44011).
Proof. exact (MK_COMB (@lem3807037) (@lem3807036 A B _44013 n1 f b _44012 _44014 _44011)). Qed.
Lemma lem3807039 (n1 : nat) (_44011 : nat) : (n1 = _44011) = (n1 = _44011).
Proof. exact (eq_refl (n1 = _44011)). Qed.
Lemma lem3807040 {A B : Type'} (_44013 : B) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (n1 : nat) (_44011 : nat) : (term957 A B _44013 f b _44012 _44014 n1 _44011) = (term958 A B _44013 f b _44012 _44014 n1 _44011).
Proof. exact (MK_COMB (@lem3807038 A B _44013 n1 f b _44012 _44014 _44011) (@lem3807039 n1 _44011)). Qed.
Lemma lem3807041 {A B : Type'} (_44013 : B) (f : type1411 A B) (b : B) (_44012 : A -> Prop) (_44014 : B) (n1 : nat) (_44011 : nat) : (term954 A B _44013 n1 f b _44012 _44014 _44011) = (term958 A B _44013 f b _44012 _44014 n1 _44011).
Proof. exact (TRANS (@lem3807023 A B _44013 f b _44012 _44014 n1 _44011) (@lem3807040 A B _44013 f b _44012 _44014 n1 _44011)). Qed.
Lemma lem3807043 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : @IN A x s) (h3 : term533 A B f b s x c n1) : term886 A B c n1 f b s w x n2.
Proof. exact (conj (@lem3806882 A B f b s x c n1 h3) (@lem3806942 A B b n2 a2 f w x s h1 h2)). Qed.
Lemma lem3807045 {A B : Type'} (_44013 : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term958 A B _44013 f b _44012 _44014 n1 _44011.
Proof. exact (EQ_MP (@lem3807041 A B _44013 f b _44012 _44014 n1 _44011) (@lem3807020 A B _44013 _44012 _44014 _44011 f b n1 h1)). Qed.
Lemma lem3807046 {A B : Type'} (_44013 : B) (_44012 : A -> Prop) (_44014 : B) (_44011 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term958 A B _44013 f b _44012 _44014 n1 _44011.
Proof. exact (@lem3807045 A B _44013 _44012 _44014 _44011 f b n1 h1). Qed.
Lemma lem3807047 {A B : Type'} (c : B) (s : A -> Prop) (w : A -> B) (x : A) (n2 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term959 A B c f b s w x n1 n2.
Proof. exact (@lem3807046 A B c (@DELETE A s x) (w x) n2 f b n1 h1). Qed.
Lemma lem3807050 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : n1 = n2.
Proof. exact (@lem3807047 A B c s w x n2 f b n1 h2 (@lem3807043 A B n2 a2 w f b s x c n1 h1 h3 h4)). Qed.
Lemma lem3807051 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : term960 n1 n2.
Proof. exact (fun h0 : term961 n1 n2 => @lem3807050 A B n2 a2 w f b s x c n1 h1 h2 h3 h4). Qed.
Lemma lem3807053 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3807054 (n1 : nat) (n2 : nat) : (term960 n1 n2) = (n1 = n2).
Proof. exact (@lem3807053 (n1 = n2)). Qed.
Lemma lem3807055 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : n1 = n2.
Proof. exact (EQ_MP (@lem3807054 n1 n2) (@lem3807051 A B n2 a2 w f b s x c n1 h1 h2 h3 h4)). Qed.
Lemma lem3807061 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3807062 (_44155 : nat) (_44156 : nat) : (term950 _44155 _44156) = (term962 _44155 _44156).
Proof. exact (@lem3807061 ((S _44155) = (S _44156)) (term961 _44155 _44156)). Qed.
Lemma lem3807072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3807073 (_44155 : nat) (_44156 : nat) : (term963 _44155 _44156) = (term964 _44155 _44156).
Proof. exact (MK_COMB (@lem3807072) (@lem3807062 _44155 _44156)). Qed.
Lemma lem3807083 (_44155 : nat) (_44156 : nat) : (term962 _44155 _44156) = (term962 _44155 _44156).
Proof. exact (eq_refl (term962 _44155 _44156)). Qed.
Lemma lem3807084 (_44155 : nat) (_44156 : nat) : ((term950 _44155 _44156) = (term962 _44155 _44156)) = ((term962 _44155 _44156) = (term962 _44155 _44156)).
Proof. exact (MK_COMB (@lem3807073 _44155 _44156) (@lem3807083 _44155 _44156)). Qed.
Lemma lem3807086 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3807087 (x : Prop) : (x = x) = True.
Proof. exact (@lem3807086 Prop x). Qed.
Lemma lem3807088 (_44155 : nat) (_44156 : nat) : ((term962 _44155 _44156) = (term962 _44155 _44156)) = True.
Proof. exact (@lem3807087 (term962 _44155 _44156)). Qed.
Lemma lem3807089 (_44155 : nat) (_44156 : nat) : ((term950 _44155 _44156) = (term962 _44155 _44156)) = True.
Proof. exact (TRANS (@lem3807084 _44155 _44156) (@lem3807088 _44155 _44156)). Qed.
Lemma lem3807090 (_44155 : nat) (_44156 : nat) : True = ((term950 _44155 _44156) = (term962 _44155 _44156)).
Proof. exact (SYM (@lem3807089 _44155 _44156)). Qed.
Lemma lem3807091 (_44155 : nat) (_44156 : nat) : (term950 _44155 _44156) = (term962 _44155 _44156).
Proof. exact (EQ_MP (@lem3807090 _44155 _44156) (@lem0)). Qed.
Lemma lem3807092 (_44155 : nat) (_44156 : nat) : term962 _44155 _44156.
Proof. exact (EQ_MP (@lem3807091 _44155 _44156) (@lem3806818 _44155 _44156)). Qed.
Lemma lem3807094 (b : Prop) (a : Prop) : (a \/ b) = (term861 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3807095 (_44155 : nat) (_44156 : nat) : (term962 _44155 _44156) = (term965 _44155 _44156).
Proof. exact (@lem3807094 (term961 _44155 _44156) ((S _44155) = (S _44156))). Qed.
Lemma lem3807097 (a : Prop) : (term541 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3807098 (_44155 : nat) (_44156 : nat) : (term966 _44155 _44156) = (_44155 = _44156).
Proof. exact (@lem3807097 (_44155 = _44156)). Qed.
Lemma lem3807099 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3807100 (_44155 : nat) (_44156 : nat) : (term967 _44155 _44156) = (term968 _44155 _44156).
Proof. exact (MK_COMB (@lem3807099) (@lem3807098 _44155 _44156)). Qed.
Lemma lem3807101 (_44155 : nat) (_44156 : nat) : ((S _44155) = (S _44156)) = ((S _44155) = (S _44156)).
Proof. exact (eq_refl ((S _44155) = (S _44156))). Qed.
Lemma lem3807102 (_44155 : nat) (_44156 : nat) : (term965 _44155 _44156) = (term949 _44155 _44156).
Proof. exact (MK_COMB (@lem3807100 _44155 _44156) (@lem3807101 _44155 _44156)). Qed.
Lemma lem3807103 (_44155 : nat) (_44156 : nat) : (term962 _44155 _44156) = (term949 _44155 _44156).
Proof. exact (TRANS (@lem3807095 _44155 _44156) (@lem3807102 _44155 _44156)). Qed.
Lemma lem3807106 (_44155 : nat) (_44156 : nat) : term949 _44155 _44156.
Proof. exact (EQ_MP (@lem3807103 _44155 _44156) (@lem3807092 _44155 _44156)). Qed.
Lemma lem3807107 (n1 : nat) (n2 : nat) : term949 n1 n2.
Proof. exact (@lem3807106 n1 n2). Qed.
Lemma lem3807110 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : (S n1) = (S n2).
Proof. exact (@lem3807107 n1 n2 (@lem3807055 A B n2 a2 w f b s x c n1 h1 h2 h3 h4)). Qed.
Lemma lem3807111 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : term969 n1 n2.
Proof. exact (fun h0 : term834 n1 n2 => @lem3807110 A B n2 a2 w f b s x c n1 h1 h2 h3 h4). Qed.
Lemma lem3807113 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3807114 (n1 : nat) (n2 : nat) : (term969 n1 n2) = ((S n1) = (S n2)).
Proof. exact (@lem3807113 ((S n1) = (S n2))). Qed.
Lemma lem3807115 {A B : Type'} (n2 : nat) (a2 : B) (w : A -> B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : @IN A x s) (h4 : term533 A B f b s x c n1) : (S n1) = (S n2).
Proof. exact (EQ_MP (@lem3807114 n1 n2) (@lem3807111 A B n2 a2 w f b s x c n1 h1 h2 h3 h4)). Qed.
Lemma lem3807118 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3807120 (n1 : nat) (n2 : nat) : (term834 n1 n2) = (term970 n1 n2).
Proof. exact (@lem3807118 ((S n1) = (S n2))). Qed.
Lemma lem3807123 (n1 : nat) (n2 : nat) (h1 : term834 n1 n2) : term970 n1 n2.
Proof. exact (EQ_MP (@lem3807120 n1 n2) (@lem3805821 n1 n2 h1)). Qed.
Lemma lem3807126 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : False.
Proof. exact (@lem3807123 n1 n2 h3 (@lem3807115 A B n2 a2 w f b s x c n1 h1 h2 h4 h5)). Qed.
Lemma lem3807127 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : term166.
Proof. exact (fun h0 : ~ False => @lem3807126 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5). Qed.
Lemma lem3807129 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3807130 : term166 = False.
Proof. exact (@lem3807129 False). Qed.
Lemma lem3807131 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807130) (@lem3807127 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5)). Qed.
Lemma lem3807132 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : (term834 n1 n2) = False.
Proof. exact (prop_ext (fun h6 : term834 n1 n2 => @lem3807131 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (fun h6 : False => @lem3805821 n1 n2 h3)). Qed.
Lemma lem3807133 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807132 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (@lem3805821 n1 n2 h3)). Qed.
Lemma lem3807134 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : (term533 A B f b s x c n1) = False.
Proof. exact (prop_ext (fun h6 : term533 A B f b s x c n1 => @lem3807133 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (fun h6 : False => @lem3805807 A B f b s x c n1 h5)). Qed.
Lemma lem3807135 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807134 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (@lem3805807 A B f b s x c n1 h5)). Qed.
Lemma lem3807136 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h6 : @IN A x s => @lem3807135 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (fun h6 : False => @lem3805793 A x s h4)). Qed.
Lemma lem3807138 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807136 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (@lem3805793 A x s h4)). Qed.
Lemma lem3807139 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : (term533 A B f b s x c n1) = False.
Proof. exact (prop_ext (fun h7 : term533 A B f b s x c n1 => @lem3806699 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3805599 A B f b s x c n1 h6)). Qed.
Lemma lem3807140 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807139 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (@lem3805599 A B f b s x c n1 h6)). Qed.
Lemma lem3807141 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h7 : @IN A x s => @lem3807140 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3805585 A x s h5)). Qed.
Lemma lem3807143 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807141 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (@lem3805585 A x s h5)). Qed.
Lemma lem3807144 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : (term834 n1 n2) = False.
Proof. exact (prop_ext (fun h6 : term834 n1 n2 => @lem3807138 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (fun h6 : False => @lem3805451 n1 n2 h3)). Qed.
Lemma lem3807145 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807144 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (@lem3805451 n1 n2 h3)). Qed.
Lemma lem3807146 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : (term533 A B f b s x c n1) = False.
Proof. exact (prop_ext (fun h6 : term533 A B f b s x c n1 => @lem3807145 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (fun h6 : False => @lem3805447 A B f b s x c n1 h5)). Qed.
Lemma lem3807147 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807146 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (@lem3805447 A B f b s x c n1 h5)). Qed.
Lemma lem3807148 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h6 : @IN A x s => @lem3807147 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (fun h6 : False => @lem3805445 A x s h4)). Qed.
Lemma lem3807149 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807148 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (@lem3805445 A x s h4)). Qed.
Lemma lem3807150 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : (term153 B a1 a2) = False.
Proof. exact (prop_ext (fun h7 : term153 B a1 a2 => @lem3807143 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3805345 B a1 a2 h3)). Qed.
Lemma lem3807151 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807150 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (@lem3805345 B a1 a2 h3)). Qed.
Lemma lem3807152 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : (term533 A B f b s x c n1) = False.
Proof. exact (prop_ext (fun h7 : term533 A B f b s x c n1 => @lem3807151 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3805341 A B f b s x c n1 h6)). Qed.
Lemma lem3807153 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807152 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (@lem3805341 A B f b s x c n1 h6)). Qed.
Lemma lem3807154 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h7 : @IN A x s => @lem3807153 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3805339 A x s h5)). Qed.
Lemma lem3807155 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807154 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (@lem3805339 A x s h5)). Qed.
Lemma lem3807156 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : (term834 n1 n2) = False.
Proof. exact (prop_ext (fun h6 : term834 n1 n2 => @lem3807149 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (fun h6 : False => @lem3805209 n1 n2 h3)). Qed.
Lemma lem3807157 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807156 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (@lem3805209 n1 n2 h3)). Qed.
Lemma lem3807158 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : (term533 A B f b s x c n1) = False.
Proof. exact (prop_ext (fun h6 : term533 A B f b s x c n1 => @lem3807157 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (fun h6 : False => @lem3805077 A B f b s x c n1 h5)). Qed.
Lemma lem3807159 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807158 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (@lem3805077 A B f b s x c n1 h5)). Qed.
Lemma lem3807160 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h6 : @IN A x s => @lem3807159 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (fun h6 : False => @lem3805073 A x s h4)). Qed.
Lemma lem3807161 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807160 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (@lem3805073 A x s h4)). Qed.
Lemma lem3807162 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : (term153 B a1 a2) = False.
Proof. exact (prop_ext (fun h7 : term153 B a1 a2 => @lem3807155 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3804952 B a1 a2 h3)). Qed.
Lemma lem3807163 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807162 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (@lem3804952 B a1 a2 h3)). Qed.
Lemma lem3807164 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : (term533 A B f b s x c n1) = False.
Proof. exact (prop_ext (fun h7 : term533 A B f b s x c n1 => @lem3807163 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3804820 A B f b s x c n1 h6)). Qed.
Lemma lem3807165 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807164 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (@lem3804820 A B f b s x c n1 h6)). Qed.
Lemma lem3807166 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h7 : @IN A x s => @lem3807165 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3804816 A x s h5)). Qed.
Lemma lem3807167 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807166 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (@lem3804816 A x s h5)). Qed.
Lemma lem3807168 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : (term834 n1 n2) = False.
Proof. exact (prop_ext (fun h6 : term834 n1 n2 => @lem3807161 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (fun h6 : False => @lem3805209 n1 n2 h3)). Qed.
Lemma lem3807169 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807168 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (@lem3805209 n1 n2 h3)). Qed.
Lemma lem3807170 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : (term533 A B f b s x c n1) = False.
Proof. exact (prop_ext (fun h6 : term533 A B f b s x c n1 => @lem3807169 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (fun h6 : False => @lem3805077 A B f b s x c n1 h5)). Qed.
Lemma lem3807171 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807170 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (@lem3805077 A B f b s x c n1 h5)). Qed.
Lemma lem3807172 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h6 : @IN A x s => @lem3807171 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (fun h6 : False => @lem3805073 A x s h4)). Qed.
Lemma lem3807173 {A B : Type'} (a2 : B) (w : A -> B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term834 n1 n2) (h4 : @IN A x s) (h5 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807172 A B a2 w n2 f b s x c n1 h1 h2 h3 h4 h5) (@lem3805073 A x s h4)). Qed.
Lemma lem3807174 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : (term153 B a1 a2) = False.
Proof. exact (prop_ext (fun h7 : term153 B a1 a2 => @lem3807167 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3804952 B a1 a2 h3)). Qed.
Lemma lem3807175 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807174 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (@lem3804952 B a1 a2 h3)). Qed.
Lemma lem3807176 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : (term533 A B f b s x c n1) = False.
Proof. exact (prop_ext (fun h7 : term533 A B f b s x c n1 => @lem3807175 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3804820 A B f b s x c n1 h6)). Qed.
Lemma lem3807177 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807176 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (@lem3804820 A B f b s x c n1 h6)). Qed.
Lemma lem3807178 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h7 : @IN A x s => @lem3807177 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3804816 A x s h5)). Qed.
Lemma lem3807179 {A B : Type'} (n2 : nat) (w : A -> B) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term153 B a1 a2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807178 A B n2 w a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (@lem3804816 A x s h5)). Qed.
Lemma lem3807180 {A B : Type'} (w : A -> B) (a2 : B) (n2 : nat) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term535 B a1 a2 n1 n2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : False.
Proof. exact (or_elim (@lem3804479 B a1 a2 n1 n2 h3) (fun h0 : term153 B a1 a2 => @lem3807179 A B n2 w a2 a1 f b s x c n1 h1 h2 h0 h4 h5 h6) (fun h0 : term834 n1 n2 => @lem3807173 A B a2 w n2 f b s x c n1 h1 h2 h0 h5 h6)). Qed.
Lemma lem3807181 {A B : Type'} (w : A -> B) (a2 : B) (n2 : nat) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term535 B a1 a2 n1 n2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : (term533 A B f b s x c n1) = False.
Proof. exact (prop_ext (fun h7 : term533 A B f b s x c n1 => @lem3807180 A B w a2 n2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3804436 A B f b s x c n1 h6)). Qed.
Lemma lem3807182 {A B : Type'} (w : A -> B) (a2 : B) (n2 : nat) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term535 B a1 a2 n1 n2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807181 A B w a2 n2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (@lem3804436 A B f b s x c n1 h6)). Qed.
Lemma lem3807183 {A B : Type'} (w : A -> B) (a2 : B) (n2 : nat) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term535 B a1 a2 n1 n2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h7 : @IN A x s => @lem3807182 A B w a2 n2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3804420 A x s h5)). Qed.
Lemma lem3807184 {A B : Type'} (w : A -> B) (a2 : B) (n2 : nat) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term16 A B f b n1) (h3 : term535 B a1 a2 n1 n2) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807183 A B w a2 n2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6) (@lem3804420 A x s h5)). Qed.
Lemma lem3807185 {A B : Type'} (w : A -> B) (a2 : B) (n2 : nat) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term691 A B b s n2 a2 f w) (h2 : term514 A B f) (h3 : term16 A B f b n1) (h4 : term535 B a1 a2 n1 n2) (h5 : a1 = (f x c)) (h6 : @IN A x s) (h7 : term533 A B f b s x c n1) : False.
Proof. exact (ex_elim (@lem3803837 A B f h2) (fun w'' : type1476 A B => fun h0 : term809 A B f w'' => @lem3807184 A B w a2 n2 a1 f b s x c n1 h1 h3 h4 h5 h6 h7)). Qed.
Lemma lem3807186 {A B : Type'} (w : A -> B) (a2 : B) (n2 : nat) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term527 A B b s n1 a1 f) (h2 : term691 A B b s n2 a2 f w) (h3 : term514 A B f) (h4 : term16 A B f b n1) (h5 : term535 B a1 a2 n1 n2) (h6 : a1 = (f x c)) (h7 : @IN A x s) (h8 : term533 A B f b s x c n1) : False.
Proof. exact (ex_elim (@lem3804008 A B b s n1 a1 f h1) (fun w' : A -> B => fun h0 : term693 A B b s n1 a1 f w' => @lem3807185 A B w a2 n2 a1 f b s x c n1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem3807187 {A B : Type'} (a2 : B) (n2 : nat) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term527 A B b s n1 a1 f) (h2 : term527 A B b s n2 a2 f) (h3 : term514 A B f) (h4 : term16 A B f b n1) (h5 : term535 B a1 a2 n1 n2) (h6 : a1 = (f x c)) (h7 : @IN A x s) (h8 : term533 A B f b s x c n1) : False.
Proof. exact (ex_elim (@lem3804179 A B b s n2 a2 f h2) (fun w : A -> B => fun h0 : term693 A B b s n2 a2 f w => @lem3807186 A B w a2 n2 a1 f b s x c n1 h1 h0 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem3807188 {A B : Type'} (a2 : B) (n2 : nat) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term527 A B b s n1 a1 f) (h2 : term527 A B b s n2 a2 f) (h3 : term514 A B f) (h4 : term16 A B f b n1) (h5 : term535 B a1 a2 n1 n2) (h6 : a1 = (f x c)) (h7 : @IN A x s) (h8 : term533 A B f b s x c n1) : (a1 = (f x c)) = False.
Proof. exact (prop_ext (fun h9 : a1 = (f x c) => @lem3807187 A B a2 n2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem3804197 A B a1 f x c h6)). Qed.
Lemma lem3807189 {A B : Type'} (a2 : B) (n2 : nat) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term527 A B b s n1 a1 f) (h2 : term527 A B b s n2 a2 f) (h3 : term514 A B f) (h4 : term16 A B f b n1) (h5 : term535 B a1 a2 n1 n2) (h6 : a1 = (f x c)) (h7 : @IN A x s) (h8 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807188 A B a2 n2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8) (@lem3804197 A B a1 f x c h6)). Qed.
Lemma lem3807190 {A B : Type'} (a2 : B) (n2 : nat) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term527 A B b s n1 a1 f) (h2 : term527 A B b s n2 a2 f) (h3 : term514 A B f) (h4 : term16 A B f b n1) (h5 : term535 B a1 a2 n1 n2) (h6 : a1 = (f x c)) (h7 : @IN A x s) (h8 : term533 A B f b s x c n1) : (term533 A B f b s x c n1) = False.
Proof. exact (prop_ext (fun h9 : term533 A B f b s x c n1 => @lem3807189 A B a2 n2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem3804191 A B f b s x c n1 h8)). Qed.
Lemma lem3807191 {A B : Type'} (a2 : B) (n2 : nat) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term527 A B b s n1 a1 f) (h2 : term527 A B b s n2 a2 f) (h3 : term514 A B f) (h4 : term16 A B f b n1) (h5 : term535 B a1 a2 n1 n2) (h6 : a1 = (f x c)) (h7 : @IN A x s) (h8 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807190 A B a2 n2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8) (@lem3804191 A B f b s x c n1 h8)). Qed.
Lemma lem3807192 {A B : Type'} (a2 : B) (n2 : nat) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term527 A B b s n1 a1 f) (h2 : term527 A B b s n2 a2 f) (h3 : term514 A B f) (h4 : term16 A B f b n1) (h5 : term535 B a1 a2 n1 n2) (h6 : a1 = (f x c)) (h7 : @IN A x s) (h8 : term533 A B f b s x c n1) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h9 : @IN A x s => @lem3807191 A B a2 n2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem3804185 A x s h7)). Qed.
Lemma lem3807193 {A B : Type'} (a2 : B) (n2 : nat) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term527 A B b s n1 a1 f) (h2 : term527 A B b s n2 a2 f) (h3 : term514 A B f) (h4 : term16 A B f b n1) (h5 : term535 B a1 a2 n1 n2) (h6 : a1 = (f x c)) (h7 : @IN A x s) (h8 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807192 A B a2 n2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8) (@lem3804185 A x s h7)). Qed.
Lemma lem3807194 {A B : Type'} (a2 : B) (n2 : nat) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term527 A B b s n1 a1 f) (h2 : term527 A B b s n2 a2 f) (h3 : term514 A B f) (h4 : term16 A B f b n1) (h5 : term535 B a1 a2 n1 n2) (h6 : a1 = (f x c)) (h7 : @IN A x s) (h8 : term533 A B f b s x c n1) : (term535 B a1 a2 n1 n2) = False.
Proof. exact (prop_ext (fun h9 : term535 B a1 a2 n1 n2 => @lem3807193 A B a2 n2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem3803136 B a1 a2 n1 n2 h5)). Qed.
Lemma lem3807195 {A B : Type'} (a2 : B) (n2 : nat) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term527 A B b s n1 a1 f) (h2 : term527 A B b s n2 a2 f) (h3 : term514 A B f) (h4 : term16 A B f b n1) (h5 : term535 B a1 a2 n1 n2) (h6 : a1 = (f x c)) (h7 : @IN A x s) (h8 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807194 A B a2 n2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8) (@lem3803136 B a1 a2 n1 n2 h5)). Qed.
Lemma lem3807196 {A B : Type'} (n2 : nat) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term527 A B b s n1 a1 f) (h2 : term527 A B b s n2 a2 f) (h3 : term514 A B f) (h4 : term16 A B f b n1) (h5 : a1 = (f x c)) (h6 : @IN A x s) (h7 : term533 A B f b s x c n1) : term534 B a1 a2 n1 n2.
Proof. exact (fun h0 : term535 B a1 a2 n1 n2 => @lem3807195 A B a2 n2 a1 f b s x c n1 h1 h2 h3 h4 h0 h5 h6 h7). Qed.
Lemma lem3807197 {A B : Type'} (n2 : nat) (a2 : B) (a1 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term527 A B b s n1 a1 f) (h2 : term527 A B b s n2 a2 f) (h3 : term514 A B f) (h4 : term16 A B f b n1) (h5 : a1 = (f x c)) (h6 : @IN A x s) (h7 : term533 A B f b s x c n1) : term530 B a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3803135 B a1 a2 n1 n2) (@lem3807196 A B n2 a2 a1 f b s x c n1 h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem3807198 {A B : Type'} (a1 : B) (n2 : nat) (a2 : B) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term527 A B b s n1 a1 f) (h2 : term527 A B b s n2 a2 f) (h3 : term514 A B f) (h4 : term16 A B f b n1) (h5 : @IN A x s) (h6 : term533 A B f b s x c n1) : term544 A B f x c a1 a2 n1 n2.
Proof. exact (fun h0 : a1 = (f x c) => @lem3807197 A B n2 a2 a1 f b s x c n1 h1 h2 h3 h4 h0 h5 h6). Qed.
Lemma lem3807199 {A B : Type'} (c : B) (a1 : B) (n2 : nat) (a2 : B) (f : type1411 A B) (b : B) (n1 : nat) (x : A) (s : A -> Prop) (h1 : term527 A B b s n1 a1 f) (h2 : term527 A B b s n2 a2 f) (h3 : term514 A B f) (h4 : term16 A B f b n1) (h5 : @IN A x s) : term547 A B b s f x c a1 a2 n1 n2.
Proof. exact (fun h0 : term533 A B f b s x c n1 => @lem3807198 A B a1 n2 a2 f b s x c n1 h1 h2 h3 h4 h5 h0). Qed.
Lemma lem3807200 {A B : Type'} (x : A) (c : B) (a1 : B) (s : A -> Prop) (n2 : nat) (a2 : B) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term527 A B b s n1 a1 f) (h2 : term527 A B b s n2 a2 f) (h3 : term514 A B f) (h4 : term16 A B f b n1) : term550 A B b s f x c a1 a2 n1 n2.
Proof. exact (fun h0 : @IN A x s => @lem3807199 A B c a1 n2 a2 f b n1 x s h1 h2 h3 h4 h0). Qed.
Lemma lem3807201 {A B : Type'} (x : A) (c : B) (a2 : B) (n2 : nat) (s : A -> Prop) (a1 : B) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term527 A B b s n1 a1 f) (h2 : term514 A B f) (h3 : term16 A B f b n1) : term553 A B b s f x c a1 a2 n1 n2.
Proof. exact (fun h0 : term527 A B b s n2 a2 f => @lem3807200 A B x c a1 s n2 a2 f b n1 h1 h0 h2 h3). Qed.
Lemma lem3807202 {A B : Type'} (s : A -> Prop) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term514 A B f) (h2 : term16 A B f b n1) : term555 A B b s f x c a1 a2 n1 n2.
Proof. exact (fun h0 : term527 A B b s n1 a1 f => @lem3807201 A B x c a2 n2 s a1 f b n1 h0 h1 h2). Qed.
Lemma lem3807203 {A B : Type'} (s : A -> Prop) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term558 A B b s f x c a1 a2 n1 n2.
Proof. exact (fun h0 : term514 A B f => @lem3807202 A B s x c a1 a2 n2 f b n1 h0 h1). Qed.
Lemma lem3807204 {A B : Type'} (s : A -> Prop) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term16 A B f b n1) : term560 A B b s f x c a1 a2 n1 n2.
Proof. exact (fun h0 : term67 A B f b n1 n2 => @lem3807203 A B s x c a1 a2 n2 f b n1 h1). Qed.
Lemma lem3807205 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term562 A B b s f x c a1 a2 n1 n2.
Proof. exact (fun h0 : term16 A B f b n1 => @lem3807204 A B s x c a1 a2 n2 f b n1 h0). Qed.
Lemma lem3807206 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term564 A B b s f x c a1 a2 n1 n2.
Proof. exact (fun h0 : term7 A B f => @lem3807205 A B b s f x c a1 a2 n1 n2). Qed.
Lemma lem3807211 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term568 A B s f x c a1 a2 n1 n2.
Proof. exact (fun b : B => @lem3807206 A B b s f x c a1 a2 n1 n2). Qed.
Lemma lem3807216 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term572 A B f x c a1 a2 n1 n2.
Proof. exact (fun s : A -> Prop => @lem3807211 A B s f x c a1 a2 n1 n2). Qed.
Lemma lem3807221 {A B : Type'} (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term576 A B x c a1 a2 n1 n2.
Proof. exact (fun f : type1411 A B => @lem3807216 A B f x c a1 a2 n1 n2). Qed.
Lemma lem3807226 {A B : Type'} (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term580 A B c a1 a2 n1 n2.
Proof. exact (fun x : A => @lem3807221 A B x c a1 a2 n1 n2). Qed.
Lemma lem3807231 {A B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term584 A B a1 a2 n1 n2.
Proof. exact (fun c : B => @lem3807226 A B c a1 a2 n1 n2). Qed.
Lemma lem3807236 {A B : Type'} (a2 : B) (n1 : nat) (n2 : nat) : term588 A B a2 n1 n2.
Proof. exact (fun a1 : B => @lem3807231 A B a1 a2 n1 n2). Qed.
Lemma lem3807241 {A B : Type'} (n1 : nat) (n2 : nat) : term592 A B n1 n2.
Proof. exact (fun a2 : B => @lem3807236 A B a2 n1 n2). Qed.
Lemma lem3807246 {A B : Type'} (n2 : nat) : term596 A B n2.
Proof. exact (fun n1 : nat => @lem3807241 A B n1 n2). Qed.
Lemma lem3807251 {A B : Type'} : term600 A B.
Proof. exact (fun n2 : nat => @lem3807246 A B n2). Qed.
Lemma lem3807252 {A B : Type'} : term599 A B.
Proof. exact (EQ_MP (@lem3803122 A B) (@lem3807251 A B)). Qed.
Lemma lem3807253 {A B : Type'} (n2 : nat) : term971 A B n2.
Proof. exact (@lem3807252 A B n2). Qed.
Lemma lem3807254 {A B : Type'} (n2 : nat) : (term971 A B n2) = (term595 A B n2).
Proof. exact (eq_refl (term971 A B n2)). Qed.
Lemma lem3807255 {A B : Type'} (n2 : nat) : term595 A B n2.
Proof. exact (EQ_MP (@lem3807254 A B n2) (@lem3807253 A B n2)). Qed.
Lemma lem3807256 {A B : Type'} (n2 : nat) (n1 : nat) : term972 A B n2 n1.
Proof. exact (@lem3807255 A B n2 n1). Qed.
Lemma lem3807257 {A B : Type'} (n1 : nat) (n2 : nat) : (term972 A B n2 n1) = (term591 A B n1 n2).
Proof. exact (eq_refl (term972 A B n2 n1)). Qed.
Lemma lem3807258 {A B : Type'} (n1 : nat) (n2 : nat) : term591 A B n1 n2.
Proof. exact (EQ_MP (@lem3807257 A B n1 n2) (@lem3807256 A B n2 n1)). Qed.
Lemma lem3807259 {A B : Type'} (n1 : nat) (n2 : nat) (a2 : B) : term973 A B n1 n2 a2.
Proof. exact (@lem3807258 A B n1 n2 a2). Qed.
Lemma lem3807260 {A B : Type'} (a2 : B) (n1 : nat) (n2 : nat) : (term973 A B n1 n2 a2) = (term587 A B a2 n1 n2).
Proof. exact (eq_refl (term973 A B n1 n2 a2)). Qed.
Lemma lem3807261 {A B : Type'} (a2 : B) (n1 : nat) (n2 : nat) : term587 A B a2 n1 n2.
Proof. exact (EQ_MP (@lem3807260 A B a2 n1 n2) (@lem3807259 A B n1 n2 a2)). Qed.
Lemma lem3807262 {A B : Type'} (a2 : B) (n1 : nat) (n2 : nat) (a1 : B) : term974 A B a2 n1 n2 a1.
Proof. exact (@lem3807261 A B a2 n1 n2 a1). Qed.
Lemma lem3807263 {A B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term974 A B a2 n1 n2 a1) = (term583 A B a1 a2 n1 n2).
Proof. exact (eq_refl (term974 A B a2 n1 n2 a1)). Qed.
Lemma lem3807264 {A B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term583 A B a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3807263 A B a1 a2 n1 n2) (@lem3807262 A B a2 n1 n2 a1)). Qed.
Lemma lem3807265 {A B : Type'} (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (c : B) : term975 A B a1 a2 n1 n2 c.
Proof. exact (@lem3807264 A B a1 a2 n1 n2 c). Qed.
Lemma lem3807266 {A B : Type'} (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term975 A B a1 a2 n1 n2 c) = (term579 A B c a1 a2 n1 n2).
Proof. exact (eq_refl (term975 A B a1 a2 n1 n2 c)). Qed.
Lemma lem3807267 {A B : Type'} (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term579 A B c a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3807266 A B c a1 a2 n1 n2) (@lem3807265 A B a1 a2 n1 n2 c)). Qed.
Lemma lem3807268 {A B : Type'} (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (x : A) : term976 A B c a1 a2 n1 n2 x.
Proof. exact (@lem3807267 A B c a1 a2 n1 n2 x). Qed.
Lemma lem3807269 {A B : Type'} (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term976 A B c a1 a2 n1 n2 x) = (term575 A B x c a1 a2 n1 n2).
Proof. exact (eq_refl (term976 A B c a1 a2 n1 n2 x)). Qed.
Lemma lem3807270 {A B : Type'} (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term575 A B x c a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3807269 A B x c a1 a2 n1 n2) (@lem3807268 A B c a1 a2 n1 n2 x)). Qed.
Lemma lem3807271 {A B : Type'} (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (f : type1411 A B) : term977 A B x c a1 a2 n1 n2 f.
Proof. exact (@lem3807270 A B x c a1 a2 n1 n2 f). Qed.
Lemma lem3807272 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term977 A B x c a1 a2 n1 n2 f) = (term571 A B f x c a1 a2 n1 n2).
Proof. exact (eq_refl (term977 A B x c a1 a2 n1 n2 f)). Qed.
Lemma lem3807273 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term571 A B f x c a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3807272 A B f x c a1 a2 n1 n2) (@lem3807271 A B x c a1 a2 n1 n2 f)). Qed.
Lemma lem3807274 {A B : Type'} (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (s : A -> Prop) : term978 A B f x c a1 a2 n1 n2 s.
Proof. exact (@lem3807273 A B f x c a1 a2 n1 n2 s). Qed.
Lemma lem3807275 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term978 A B f x c a1 a2 n1 n2 s) = (term567 A B s f x c a1 a2 n1 n2).
Proof. exact (eq_refl (term978 A B f x c a1 a2 n1 n2 s)). Qed.
Lemma lem3807276 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term567 A B s f x c a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3807275 A B s f x c a1 a2 n1 n2) (@lem3807274 A B f x c a1 a2 n1 n2 s)). Qed.
Lemma lem3807277 {A B : Type'} (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (b : B) : term979 A B s f x c a1 a2 n1 n2 b.
Proof. exact (@lem3807276 A B s f x c a1 a2 n1 n2 b). Qed.
Lemma lem3807278 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : (term979 A B s f x c a1 a2 n1 n2 b) = (term536 A B b s f x c a1 a2 n1 n2).
Proof. exact (eq_refl (term979 A B s f x c a1 a2 n1 n2 b)). Qed.
Lemma lem3807279 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term536 A B b s f x c a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3807278 A B b s f x c a1 a2 n1 n2) (@lem3807277 A B s f x c a1 a2 n1 n2 b)). Qed.
Lemma lem3807281 {A B : Type'} (b : B) (s : A -> Prop) (f : type1411 A B) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) : term536 A B b s f x c a1 a2 n1 n2.
Proof. exact (@lem3802304 A B b s f x c a1 a2 n1 n2 (@lem3807279 A B b s f x c a1 a2 n1 n2)). Qed.
Lemma lem3807282 {A B : Type'} (b : B) (s : A -> Prop) (x : A) (c : B) (a1 : B) (a2 : B) (n1 : nat) (n2 : nat) (f : type1411 A B) (h1 : term7 A B f) : term561 A B b s f x c a1 a2 n1 n2.
Proof. exact (@lem3807281 A B b s f x c a1 a2 n1 n2 (@lem3797446 A B f h1)). Qed.
Lemma lem3807283 {A B : Type'} (s : A -> Prop) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term7 A B f) (h2 : term16 A B f b n1) : term559 A B b s f x c a1 a2 n1 n2.
Proof. exact (@lem3807282 A B b s x c a1 a2 n1 n2 f h1 (@lem3797470 A B f b n1 h2)). Qed.
Lemma lem3807284 {A B : Type'} (s : A -> Prop) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) : term557 A B b s f x c a1 a2 n1 n2.
Proof. exact (@lem3807283 A B s x c a1 a2 n2 f b n1 h1 h3 (@lem3797518 A B f b n1 n2 h2)). Qed.
Lemma lem3807285 {A B : Type'} (s : A -> Prop) (x : A) (c : B) (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) : term554 A B b s f x c a1 a2 n1 n2.
Proof. exact (@lem3807284 A B s x c a1 a2 n2 f b n1 h1 h2 h3 (@lem3802059 A B f h1)). Qed.
Lemma lem3807286 {A B : Type'} (x : A) (c : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term168 A B f b s a1 n1) : term552 A B b s f x c a1 a2 n1 n2.
Proof. exact (@lem3807285 A B s x c a1 a2 n2 f b n1 h1 h2 h3 (@lem3802170 A B f b s a1 n1 h1 h4)). Qed.
Lemma lem3807287 {A B : Type'} (x : A) (c : B) (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term168 A B f b s a1 n1) (h5 : term168 A B f b s a2 n2) : term549 A B b s f x c a1 a2 n1 n2.
Proof. exact (@lem3807286 A B x c a2 n2 f b s a1 n1 h1 h2 h3 h4 (@lem3802238 A B f b s a2 n2 h1 h5)). Qed.
Lemma lem3807288 {A B : Type'} (c : B) (x : A) (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : @IN A x s) (h5 : term168 A B f b s a1 n1) (h6 : term168 A B f b s a2 n2) : term546 A B b s f x c a1 a2 n1 n2.
Proof. exact (@lem3807287 A B x c a1 n1 f b s a2 n2 h1 h2 h3 h5 h6 (@lem3802281 A x s h4)). Qed.
Lemma lem3807289 {A B : Type'} (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : @IN A x s) (h5 : term168 A B f b s a1 n1) (h6 : term168 A B f b s a2 n2) (h7 : term533 A B f b s x c n1) : term543 A B f x c a1 a2 n1 n2.
Proof. exact (@lem3807288 A B c x a1 n1 f b s a2 n2 h1 h2 h3 h4 h5 h6 (@lem3802283 A B f b s x c n1 h7)). Qed.
Lemma lem3807290 {A B : Type'} (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term168 A B f b s a1 n1) (h7 : term168 A B f b s a2 n2) (h8 : term533 A B f b s x c n1) : term534 B a1 a2 n1 n2.
Proof. exact (@lem3807289 A B a1 a2 n2 f b s x c n1 h1 h2 h3 h5 h6 h7 h8 (@lem3802282 A B a1 f x c h4)). Qed.
Lemma lem3807291 {A B : Type'} (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term535 B a1 a2 n1 n2) (h5 : a1 = (f x c)) (h6 : @IN A x s) (h7 : term168 A B f b s a1 n1) (h8 : term168 A B f b s a2 n2) (h9 : term533 A B f b s x c n1) : False.
Proof. exact (@lem3807290 A B a1 a2 n2 f b s x c n1 h1 h2 h3 h5 h6 h7 h8 h9 (@lem3802288 B a1 a2 n1 n2 h4)). Qed.
Lemma lem3807292 {A B : Type'} (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term535 B a1 a2 n1 n2) (h5 : a1 = (f x c)) (h6 : @IN A x s) (h7 : term168 A B f b s a1 n1) (h8 : term168 A B f b s a2 n2) (h9 : term533 A B f b s x c n1) : (term535 B a1 a2 n1 n2) = False.
Proof. exact (prop_ext (fun h10 : term535 B a1 a2 n1 n2 => @lem3807291 A B a1 a2 n2 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem3802288 B a1 a2 n1 n2 h4)). Qed.
Lemma lem3807293 {A B : Type'} (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term535 B a1 a2 n1 n2) (h5 : a1 = (f x c)) (h6 : @IN A x s) (h7 : term168 A B f b s a1 n1) (h8 : term168 A B f b s a2 n2) (h9 : term533 A B f b s x c n1) : False.
Proof. exact (EQ_MP (@lem3807292 A B a1 a2 n2 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem3802288 B a1 a2 n1 n2 h4)). Qed.
Lemma lem3807294 {A B : Type'} (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term168 A B f b s a1 n1) (h7 : term168 A B f b s a2 n2) (h8 : term533 A B f b s x c n1) : term534 B a1 a2 n1 n2.
Proof. exact (fun h0 : term535 B a1 a2 n1 n2 => @lem3807293 A B a1 a2 n2 f b s x c n1 h1 h2 h3 h0 h4 h5 h6 h7 h8). Qed.
Lemma lem3807295 {A B : Type'} (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term168 A B f b s a1 n1) (h7 : term168 A B f b s a2 n2) (h8 : term533 A B f b s x c n1) : term530 B a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3802287 B a1 a2 n1 n2) (@lem3807294 A B a1 a2 n2 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem3807296 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) (h1 : term203 A B b s n1 a1 f x c) : term200 A B b s n1 a1 f x c.
Proof. exact (proj2 (@lem3802279 A B b s n1 a1 f x c h1)). Qed.
Lemma lem3807297 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) (h1 : term203 A B b s n1 a1 f x c) : @IN A x s.
Proof. exact (proj1 (@lem3802279 A B b s n1 a1 f x c h1)). Qed.
Lemma lem3807298 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) (h1 : term200 A B b s n1 a1 f x c) : a1 = (f x c).
Proof. exact (proj2 (@lem3802280 A B b s n1 a1 f x c h1)). Qed.
Lemma lem3807299 {A B : Type'} (b : B) (s : A -> Prop) (n1 : nat) (a1 : B) (f : type1411 A B) (x : A) (c : B) (h1 : term200 A B b s n1 a1 f x c) : term533 A B f b s x c n1.
Proof. exact (proj1 (@lem3802280 A B b s n1 a1 f x c h1)). Qed.
Lemma lem3807300 {A B : Type'} (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term168 A B f b s a1 n1) (h7 : term168 A B f b s a2 n2) (h8 : term533 A B f b s x c n1) : (a1 = (f x c)) = (term530 B a1 a2 n1 n2).
Proof. exact (prop_ext (fun h9 : a1 = (f x c) => @lem3807295 A B a1 a2 n2 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : term530 B a1 a2 n1 n2 => @lem3802282 A B a1 f x c h4)). Qed.
Lemma lem3807301 {A B : Type'} (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term168 A B f b s a1 n1) (h7 : term168 A B f b s a2 n2) (h8 : term533 A B f b s x c n1) : term530 B a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3807300 A B a1 a2 n2 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8) (@lem3802282 A B a1 f x c h4)). Qed.
Lemma lem3807302 {A B : Type'} (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term168 A B f b s a1 n1) (h7 : term168 A B f b s a2 n2) (h8 : term533 A B f b s x c n1) : (term533 A B f b s x c n1) = (term530 B a1 a2 n1 n2).
Proof. exact (prop_ext (fun h9 : term533 A B f b s x c n1 => @lem3807301 A B a1 a2 n2 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : term530 B a1 a2 n1 n2 => @lem3802283 A B f b s x c n1 h8)). Qed.
Lemma lem3807303 {A B : Type'} (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : a1 = (f x c)) (h5 : @IN A x s) (h6 : term168 A B f b s a1 n1) (h7 : term168 A B f b s a2 n2) (h8 : term533 A B f b s x c n1) : term530 B a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3807302 A B a1 a2 n2 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8) (@lem3802283 A B f b s x c n1 h8)). Qed.
Lemma lem3807304 {A B : Type'} (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term200 A B b s n1 a1 f x c) (h5 : @IN A x s) (h6 : term168 A B f b s a1 n1) (h7 : term168 A B f b s a2 n2) (h8 : term533 A B f b s x c n1) : (a1 = (f x c)) = (term530 B a1 a2 n1 n2).
Proof. exact (prop_ext (fun h9 : a1 = (f x c) => @lem3807303 A B a1 a2 n2 f b s x c n1 h1 h2 h3 h9 h5 h6 h7 h8) (fun h9 : term530 B a1 a2 n1 n2 => @lem3807298 A B b s n1 a1 f x c h4)). Qed.
Lemma lem3807305 {A B : Type'} (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (x : A) (c : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term200 A B b s n1 a1 f x c) (h5 : @IN A x s) (h6 : term168 A B f b s a1 n1) (h7 : term168 A B f b s a2 n2) (h8 : term533 A B f b s x c n1) : term530 B a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3807304 A B a1 a2 n2 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8) (@lem3807298 A B b s n1 a1 f x c h4)). Qed.
Lemma lem3807306 {A B : Type'} (c : B) (x : A) (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term200 A B b s n1 a1 f x c) (h5 : @IN A x s) (h6 : term168 A B f b s a1 n1) (h7 : term168 A B f b s a2 n2) : (term533 A B f b s x c n1) = (term530 B a1 a2 n1 n2).
Proof. exact (prop_ext (fun h8 : term533 A B f b s x c n1 => @lem3807305 A B a1 a2 n2 f b s x c n1 h1 h2 h3 h4 h5 h6 h7 h8) (fun h8 : term530 B a1 a2 n1 n2 => @lem3807299 A B b s n1 a1 f x c h4)). Qed.
Lemma lem3807307 {A B : Type'} (c : B) (x : A) (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term200 A B b s n1 a1 f x c) (h5 : @IN A x s) (h6 : term168 A B f b s a1 n1) (h7 : term168 A B f b s a2 n2) : term530 B a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3807306 A B c x a1 n1 f b s a2 n2 h1 h2 h3 h4 h5 h6 h7) (@lem3807299 A B b s n1 a1 f x c h4)). Qed.
Lemma lem3807308 {A B : Type'} (c : B) (x : A) (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term200 A B b s n1 a1 f x c) (h5 : @IN A x s) (h6 : term168 A B f b s a1 n1) (h7 : term168 A B f b s a2 n2) : (@IN A x s) = (term530 B a1 a2 n1 n2).
Proof. exact (prop_ext (fun h8 : @IN A x s => @lem3807307 A B c x a1 n1 f b s a2 n2 h1 h2 h3 h4 h5 h6 h7) (fun h8 : term530 B a1 a2 n1 n2 => @lem3802281 A x s h5)). Qed.
Lemma lem3807309 {A B : Type'} (c : B) (x : A) (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term200 A B b s n1 a1 f x c) (h5 : @IN A x s) (h6 : term168 A B f b s a1 n1) (h7 : term168 A B f b s a2 n2) : term530 B a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3807308 A B c x a1 n1 f b s a2 n2 h1 h2 h3 h4 h5 h6 h7) (@lem3802281 A x s h5)). Qed.
Lemma lem3807310 {A B : Type'} (c : B) (x : A) (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term203 A B b s n1 a1 f x c) (h5 : @IN A x s) (h6 : term168 A B f b s a1 n1) (h7 : term168 A B f b s a2 n2) : (term200 A B b s n1 a1 f x c) = (term530 B a1 a2 n1 n2).
Proof. exact (prop_ext (fun h8 : term200 A B b s n1 a1 f x c => @lem3807309 A B c x a1 n1 f b s a2 n2 h1 h2 h3 h8 h5 h6 h7) (fun h8 : term530 B a1 a2 n1 n2 => @lem3807296 A B b s n1 a1 f x c h4)). Qed.
Lemma lem3807311 {A B : Type'} (c : B) (x : A) (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term203 A B b s n1 a1 f x c) (h5 : @IN A x s) (h6 : term168 A B f b s a1 n1) (h7 : term168 A B f b s a2 n2) : term530 B a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3807310 A B c x a1 n1 f b s a2 n2 h1 h2 h3 h4 h5 h6 h7) (@lem3807296 A B b s n1 a1 f x c h4)). Qed.
Lemma lem3807312 {A B : Type'} (x : A) (c : B) (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term203 A B b s n1 a1 f x c) (h5 : term168 A B f b s a1 n1) (h6 : term168 A B f b s a2 n2) : (@IN A x s) = (term530 B a1 a2 n1 n2).
Proof. exact (prop_ext (fun h7 : @IN A x s => @lem3807311 A B c x a1 n1 f b s a2 n2 h1 h2 h3 h4 h7 h5 h6) (fun h7 : term530 B a1 a2 n1 n2 => @lem3807297 A B b s n1 a1 f x c h4)). Qed.
Lemma lem3807313 {A B : Type'} (x : A) (c : B) (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term203 A B b s n1 a1 f x c) (h5 : term168 A B f b s a1 n1) (h6 : term168 A B f b s a2 n2) : term530 B a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3807312 A B x c a1 n1 f b s a2 n2 h1 h2 h3 h4 h5 h6) (@lem3807297 A B b s n1 a1 f x c h4)). Qed.
Lemma lem3807314 {A B : Type'} (x : A) (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term206 A B b s n1 a1 f x) (h5 : term168 A B f b s a1 n1) (h6 : term168 A B f b s a2 n2) : term530 B a1 a2 n1 n2.
Proof. exact (ex_elim (@lem3802278 A B b s n1 a1 f x h4) (fun c : B => fun h0 : term205 A B b s n1 a1 f x c => @lem3807313 A B x c a1 n1 f b s a2 n2 h1 h2 h3 h0 h5 h6)). Qed.
Lemma lem3807315 {A B : Type'} (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term169 A B b s n1 a1 f) (h5 : term168 A B f b s a1 n1) (h6 : term168 A B f b s a2 n2) : term530 B a1 a2 n1 n2.
Proof. exact (ex_elim (@lem3802277 A B b s n1 a1 f h4) (fun x : A => fun h0 : term213 A B b s n1 a1 f x => @lem3807314 A B x a1 n1 f b s a2 n2 h1 h2 h3 h0 h5 h6)). Qed.
Lemma lem3807316 {A B : Type'} (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term168 A B f b s a1 n1) (h5 : term168 A B f b s a2 n2) : term532 A B b s f a1 a2 n1 n2.
Proof. exact (fun h0 : term169 A B b s n1 a1 f => @lem3807315 A B a1 n1 f b s a2 n2 h1 h2 h3 h0 h4 h5). Qed.
Lemma lem3807317 {A B : Type'} (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term168 A B f b s a1 n1) (h5 : term168 A B f b s a2 n2) : term531 A B f b s a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3802276 A B f b s a1 a2 n1 n2) (@lem3807316 A B a1 n1 f b s a2 n2 h1 h2 h3 h4 h5)). Qed.
Lemma lem3807318 {A B : Type'} (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term519 A B a1 n1 f b s a2 n2) : term168 A B f b s a2 n2.
Proof. exact (proj2 (@lem3802100 A B a1 n1 f b s a2 n2 h1)). Qed.
Lemma lem3807319 {A B : Type'} (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term519 A B a1 n1 f b s a2 n2) : term168 A B f b s a1 n1.
Proof. exact (proj1 (@lem3802100 A B a1 n1 f b s a2 n2 h1)). Qed.
Lemma lem3807320 {A B : Type'} (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term519 A B a1 n1 f b s a2 n2) (h5 : term168 A B f b s a1 n1) : (term168 A B f b s a2 n2) = (term531 A B f b s a1 a2 n1 n2).
Proof. exact (prop_ext (fun h6 : term168 A B f b s a2 n2 => @lem3807317 A B a1 n1 f b s a2 n2 h1 h2 h3 h5 h6) (fun h6 : term531 A B f b s a1 a2 n1 n2 => @lem3807318 A B a1 n1 f b s a2 n2 h4)). Qed.
Lemma lem3807321 {A B : Type'} (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a1 : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term519 A B a1 n1 f b s a2 n2) (h5 : term168 A B f b s a1 n1) : term531 A B f b s a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3807320 A B a2 n2 f b s a1 n1 h1 h2 h3 h4 h5) (@lem3807318 A B a1 n1 f b s a2 n2 h4)). Qed.
Lemma lem3807322 {A B : Type'} (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term519 A B a1 n1 f b s a2 n2) : (term168 A B f b s a1 n1) = (term531 A B f b s a1 a2 n1 n2).
Proof. exact (prop_ext (fun h5 : term168 A B f b s a1 n1 => @lem3807321 A B a2 n2 f b s a1 n1 h1 h2 h3 h4 h5) (fun h5 : term531 A B f b s a1 a2 n1 n2 => @lem3807319 A B a1 n1 f b s a2 n2 h4)). Qed.
Lemma lem3807323 {A B : Type'} (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term519 A B a1 n1 f b s a2 n2) : term531 A B f b s a1 a2 n1 n2.
Proof. exact (EQ_MP (@lem3807322 A B a1 n1 f b s a2 n2 h1 h2 h3 h4) (@lem3807319 A B a1 n1 f b s a2 n2 h4)). Qed.
Lemma lem3807324 {A B : Type'} (s : A -> Prop) (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) : term980 A B f b s a1 a2 n1 n2.
Proof. exact (fun h0 : term519 A B a1 n1 f b s a2 n2 => @lem3807323 A B a1 n1 f b s a2 n2 h1 h2 h3 h0). Qed.
Lemma lem3807325 {A B : Type'} (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term519 A B a1 n1 f b s a2 n2) : term531 A B f b s a1 a2 n1 n2.
Proof. exact (@lem3807324 A B s a1 a2 n2 f b n1 h1 h2 h3 (@lem3802098 A B a1 n1 f b s a2 n2 h4)). Qed.
Lemma lem3807326 {A B : Type'} (a1 : B) (n1 : nat) (f : type1411 A B) (b : B) (s : A -> Prop) (a2 : B) (n2 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) (h4 : term519 A B a1 n1 f b s a2 n2) : term530 B a1 a2 n1 n2.
Proof. exact (@lem3807325 A B a1 n1 f b s a2 n2 h1 h2 h3 h4 (@lem3802099 A B a1 n1 f b s a2 n2 h4)). Qed.
Lemma lem3807327 {A B : Type'} (s : A -> Prop) (a1 : B) (a2 : B) (n2 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) : term981 A B f b s a1 a2 n1 n2.
Proof. exact (fun h0 : term519 A B a1 n1 f b s a2 n2 => @lem3807326 A B a1 n1 f b s a2 n2 h1 h2 h3 h0). Qed.
Lemma lem3807332 {A B : Type'} (s : A -> Prop) (a1 : B) (n2 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) : term982 A B f b s a1 n1 n2.
Proof. exact (fun a2 : B => @lem3807327 A B s a1 a2 n2 f b n1 h1 h2 h3). Qed.
Lemma lem3807337 {A B : Type'} (s : A -> Prop) (n2 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) : term983 A B f b s n1 n2.
Proof. exact (fun a1 : B => @lem3807332 A B s a1 n2 f b n1 h1 h2 h3). Qed.
Lemma lem3807342 {A B : Type'} (n2 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term7 A B f) (h2 : term67 A B f b n1 n2) (h3 : term16 A B f b n1) : term71 A B f b n1 n2.
Proof. exact (fun s : A -> Prop => @lem3807337 A B s n2 f b n1 h1 h2 h3). Qed.
Lemma lem3807343 {A B : Type'} (n2 : nat) (f : type1411 A B) (b : B) (n1 : nat) (h1 : term7 A B f) (h2 : term16 A B f b n1) : term73 A B f b n1 n2.
Proof. exact (fun h0 : term67 A B f b n1 n2 => @lem3807342 A B n2 f b n1 h1 h0 h2). Qed.
Lemma lem3807348 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term7 A B f) (h2 : term16 A B f b n1) : term77 A B f b n1.
Proof. exact (fun n2 : nat => @lem3807343 A B n2 f b n1 h1 h2). Qed.
Lemma lem3807349 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term7 A B f) (h2 : term16 A B f b n1) : term79 A B f b n1.
Proof. exact (conj (@lem3802038 A B f b n1) (@lem3807348 A B f b n1 h1 h2)). Qed.
Lemma lem3807350 {A B : Type'} (f : type1411 A B) (b : B) (n1 : nat) (h1 : term7 A B f) (h2 : term16 A B f b n1) : term20 A B f b n1.
Proof. exact (@lem3797517 A B f b n1 (@lem3807349 A B f b n1 h1 h2)). Qed.
Lemma lem3807351 {A B : Type'} (f : type1411 A B) (b : B) (n2 : nat) : term48 A B f b n2.
Proof. exact (fun h0 : term42 A B f b n2 => @lem3800150 A B f b n2). Qed.
Lemma lem3807356 {A B : Type'} (f : type1411 A B) (b : B) : term52 A B f b.
Proof. exact (fun n2 : nat => @lem3807351 A B f b n2). Qed.
Lemma lem3807357 {A B : Type'} (f : type1411 A B) (b : B) : term54 A B f b.
Proof. exact (conj (@lem3798274 A B f b) (@lem3807356 A B f b)). Qed.
Lemma lem3807358 {A B : Type'} (f : type1411 A B) (b : B) : term12 A B f b.
Proof. exact (@lem3797493 A B f b (@lem3807357 A B f b)). Qed.
Lemma lem3807359 {A B : Type'} (b : B) (n1 : nat) (f : type1411 A B) (h1 : term7 A B f) : term22 A B f b n1.
Proof. exact (fun h0 : term16 A B f b n1 => @lem3807350 A B f b n1 h1 h0). Qed.
Lemma lem3807364 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term7 A B f) : term26 A B f b.
Proof. exact (fun n1 : nat => @lem3807359 A B b n1 f h1). Qed.
Lemma lem3807365 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term7 A B f) : term28 A B f b.
Proof. exact (conj (@lem3807358 A B f b) (@lem3807364 A B b f h1)). Qed.
Lemma lem3807366 {A B : Type'} (b : B) (f : type1411 A B) (h1 : term7 A B f) : term33 A B f b.
Proof. exact (@lem3797469 A B f b (@lem3807365 A B b f h1)). Qed.
Lemma lem3807367 {A B : Type'} (f : type1411 A B) (b : B) : term984 A B f b.
Proof. exact (fun h0 : term7 A B f => @lem3807366 A B b f h0). Qed.
Lemma lem3807372 {A B : Type'} (f : type1411 A B) : term985 A B f.
Proof. exact (fun b : B => @lem3807367 A B f b). Qed.
Lemma lem3807377 {A B : Type'} : term986 A B.
Proof. exact (fun f : type1411 A B => @lem3807372 A B f). Qed.
