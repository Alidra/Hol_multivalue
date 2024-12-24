Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_CLAUSES_term_abbrevs.
Require Import CARD_spec.
Require Import FINITE_RECURSION_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1823_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3840378 {_99571 : Type'} (s : _99571 -> Prop) : term0 _99571 s.
Proof. exact (@lem3840377 _99571 s). Qed.
Lemma lem3840379 {_99571 : Type'} (s : _99571 -> Prop) : (term0 _99571 s) = ((@CARD _99571 s) = (term1 _99571 s)).
Proof. exact (eq_refl (term0 _99571 s)). Qed.
Lemma lem3840381 {A : Type'} : term2 A.
Proof. exact (@lem3816218 A nat). Qed.
Lemma lem3840382 {A : Type'} : term3 A.
Proof. exact (@lem3840381 A (term4 A)). Qed.
Lemma lem3840383 {A : Type'} : (term3 A) = (term5 A).
Proof. exact (eq_refl (term3 A)). Qed.
Lemma lem3840384 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem3840383 A) (@lem3840382 A)). Qed.
Lemma lem3840385 {A : Type'} : term6 A.
Proof. exact (@lem3840384 A (NUMERAL 0)). Qed.
Lemma lem3840386 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (eq_refl (term6 A)). Qed.
Lemma lem3840387 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem3840386 A) (@lem3840385 A)). Qed.
Lemma lem3840411 {A B : Type'} (f : A -> B) (y : A) : (term8 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3840412 {A : Type'} (f : type1425 A) (y : A) : (term9 A f y) = (f y).
Proof. exact (@lem3840411 A (nat -> nat) f y). Qed.
Lemma lem3840413 {A : Type'} (x : A) : (term10 A x) = (term11 A x).
Proof. exact (@lem3840412 A (term4 A) x). Qed.
Lemma lem3840414 {A : Type'} (x : A) : (term11 A x) = term12.
Proof. exact (eq_refl (term11 A x)). Qed.
Lemma lem3840415 {A : Type'} : (term13 A) = (term4 A).
Proof. exact (fun_ext (fun x : A => @lem3840414 A x)). Qed.
Lemma lem3840416 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3840417 {A : Type'} (x : A) : (term10 A x) = (term11 A x).
Proof. exact (MK_COMB (@lem3840415 A) (@lem3840416 A x)). Qed.
Lemma lem3840418 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem3840419 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (MK_COMB (@lem3840418) (@lem3840417 A x)). Qed.
Lemma lem3840420 {A : Type'} (x : A) : (term11 A x) = term12.
Proof. exact (eq_refl (term11 A x)). Qed.
Lemma lem3840421 {A : Type'} (x : A) : ((term10 A x) = (term11 A x)) = ((term11 A x) = term12).
Proof. exact (MK_COMB (@lem3840419 A x) (@lem3840420 A x)). Qed.
Lemma lem3840422 {A : Type'} (x : A) : (term11 A x) = term12.
Proof. exact (EQ_MP (@lem3840421 A x) (@lem3840413 A x)). Qed.
Lemma lem3840424 {A B : Type'} (f : A -> B) (y : A) : (term8 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3840425 {A : Type'} (f : type1425 A) (y : A) : (term9 A f y) = (f y).
Proof. exact (@lem3840424 A (nat -> nat) f y). Qed.
Lemma lem3840426 {A : Type'} (y : A) : (term10 A y) = (term11 A y).
Proof. exact (@lem3840425 A (term4 A) y). Qed.
Lemma lem3840427 {A : Type'} (x : A) : (term11 A x) = term12.
Proof. exact (eq_refl (term11 A x)). Qed.
Lemma lem3840428 {A : Type'} : (term13 A) = (term4 A).
Proof. exact (fun_ext (fun x : A => @lem3840427 A x)). Qed.
Lemma lem3840429 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3840430 {A : Type'} (y : A) : (term10 A y) = (term11 A y).
Proof. exact (MK_COMB (@lem3840428 A) (@lem3840429 A y)). Qed.
Lemma lem3840431 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem3840432 {A : Type'} (y : A) : (term14 A y) = (term15 A y).
Proof. exact (MK_COMB (@lem3840431) (@lem3840430 A y)). Qed.
Lemma lem3840433 {A : Type'} (y : A) : (term11 A y) = term12.
Proof. exact (eq_refl (term11 A y)). Qed.
Lemma lem3840434 {A : Type'} (y : A) : ((term10 A y) = (term11 A y)) = ((term11 A y) = term12).
Proof. exact (MK_COMB (@lem3840432 A y) (@lem3840433 A y)). Qed.
Lemma lem3840435 {A : Type'} (y : A) : (term11 A y) = term12.
Proof. exact (EQ_MP (@lem3840434 A y) (@lem3840426 A y)). Qed.
Lemma lem3840436 (s : nat) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3840437 {A : Type'} (y : A) (s : nat) : (term16 A y s) = (term17 s).
Proof. exact (MK_COMB (@lem3840435 A y) (@lem3840436 s)). Qed.
Lemma lem3840439 {A B : Type'} (f : A -> B) (y : A) : (term8 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3840440 (f : nat -> nat) (y : nat) : (term18 f y) = (f y).
Proof. exact (@lem3840439 nat nat f y). Qed.
Lemma lem3840441 (s : nat) : (term17 s) = (S s).
Proof. exact (@lem3840440 S s). Qed.
Lemma lem3840442 {A : Type'} (y : A) (s : nat) : (term16 A y s) = (S s).
Proof. exact (TRANS (@lem3840437 A y s) (@lem3840441 s)). Qed.
Lemma lem3840443 {A : Type'} (x : A) (y : A) (s : nat) : (term19 A x y s) = (term20 s).
Proof. exact (MK_COMB (@lem3840422 A x) (@lem3840442 A y s)). Qed.
Lemma lem3840445 {A B : Type'} (f : A -> B) (y : A) : (term8 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3840446 (f : nat -> nat) (y : nat) : (term18 f y) = (f y).
Proof. exact (@lem3840445 nat nat f y). Qed.
Lemma lem3840447 (s : nat) : (term20 s) = (term21 s).
Proof. exact (@lem3840446 S (S s)). Qed.
Lemma lem3840448 {A : Type'} (x : A) (y : A) (s : nat) : (term19 A x y s) = (term21 s).
Proof. exact (TRANS (@lem3840443 A x y s) (@lem3840447 s)). Qed.
Lemma lem3840449 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3840450 {A : Type'} (x : A) (y : A) (s : nat) : (term22 A x y s) = (term23 s).
Proof. exact (MK_COMB (@lem3840449) (@lem3840448 A x y s)). Qed.
Lemma lem3840452 {A B : Type'} (f : A -> B) (y : A) : (term8 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3840453 {A : Type'} (f : type1425 A) (y : A) : (term9 A f y) = (f y).
Proof. exact (@lem3840452 A (nat -> nat) f y). Qed.
Lemma lem3840454 {A : Type'} (y : A) : (term10 A y) = (term11 A y).
Proof. exact (@lem3840453 A (term4 A) y). Qed.
Lemma lem3840455 {A : Type'} (x : A) : (term11 A x) = term12.
Proof. exact (eq_refl (term11 A x)). Qed.
Lemma lem3840456 {A : Type'} : (term13 A) = (term4 A).
Proof. exact (fun_ext (fun x : A => @lem3840455 A x)). Qed.
Lemma lem3840457 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3840458 {A : Type'} (y : A) : (term10 A y) = (term11 A y).
Proof. exact (MK_COMB (@lem3840456 A) (@lem3840457 A y)). Qed.
Lemma lem3840459 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem3840460 {A : Type'} (y : A) : (term14 A y) = (term15 A y).
Proof. exact (MK_COMB (@lem3840459) (@lem3840458 A y)). Qed.
Lemma lem3840461 {A : Type'} (y : A) : (term11 A y) = term12.
Proof. exact (eq_refl (term11 A y)). Qed.
Lemma lem3840462 {A : Type'} (y : A) : ((term10 A y) = (term11 A y)) = ((term11 A y) = term12).
Proof. exact (MK_COMB (@lem3840460 A y) (@lem3840461 A y)). Qed.
Lemma lem3840463 {A : Type'} (y : A) : (term11 A y) = term12.
Proof. exact (EQ_MP (@lem3840462 A y) (@lem3840454 A y)). Qed.
Lemma lem3840465 {A B : Type'} (f : A -> B) (y : A) : (term8 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3840466 {A : Type'} (f : type1425 A) (y : A) : (term9 A f y) = (f y).
Proof. exact (@lem3840465 A (nat -> nat) f y). Qed.
Lemma lem3840467 {A : Type'} (x : A) : (term10 A x) = (term11 A x).
Proof. exact (@lem3840466 A (term4 A) x). Qed.
Lemma lem3840468 {A : Type'} (x : A) : (term11 A x) = term12.
Proof. exact (eq_refl (term11 A x)). Qed.
Lemma lem3840469 {A : Type'} : (term13 A) = (term4 A).
Proof. exact (fun_ext (fun x : A => @lem3840468 A x)). Qed.
Lemma lem3840470 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3840471 {A : Type'} (x : A) : (term10 A x) = (term11 A x).
Proof. exact (MK_COMB (@lem3840469 A) (@lem3840470 A x)). Qed.
Lemma lem3840472 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem3840473 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (MK_COMB (@lem3840472) (@lem3840471 A x)). Qed.
Lemma lem3840474 {A : Type'} (x : A) : (term11 A x) = term12.
Proof. exact (eq_refl (term11 A x)). Qed.
Lemma lem3840475 {A : Type'} (x : A) : ((term10 A x) = (term11 A x)) = ((term11 A x) = term12).
Proof. exact (MK_COMB (@lem3840473 A x) (@lem3840474 A x)). Qed.
Lemma lem3840476 {A : Type'} (x : A) : (term11 A x) = term12.
Proof. exact (EQ_MP (@lem3840475 A x) (@lem3840467 A x)). Qed.
Lemma lem3840477 (s : nat) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem3840478 {A : Type'} (x : A) (s : nat) : (term16 A x s) = (term17 s).
Proof. exact (MK_COMB (@lem3840476 A x) (@lem3840477 s)). Qed.
Lemma lem3840480 {A B : Type'} (f : A -> B) (y : A) : (term8 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3840481 (f : nat -> nat) (y : nat) : (term18 f y) = (f y).
Proof. exact (@lem3840480 nat nat f y). Qed.
Lemma lem3840482 (s : nat) : (term17 s) = (S s).
Proof. exact (@lem3840481 S s). Qed.
Lemma lem3840483 {A : Type'} (x : A) (s : nat) : (term16 A x s) = (S s).
Proof. exact (TRANS (@lem3840478 A x s) (@lem3840482 s)). Qed.
Lemma lem3840484 {A : Type'} (y : A) (x : A) (s : nat) : (term19 A y x s) = (term20 s).
Proof. exact (MK_COMB (@lem3840463 A y) (@lem3840483 A x s)). Qed.
Lemma lem3840486 {A B : Type'} (f : A -> B) (y : A) : (term8 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3840487 (f : nat -> nat) (y : nat) : (term18 f y) = (f y).
Proof. exact (@lem3840486 nat nat f y). Qed.
Lemma lem3840488 (s : nat) : (term20 s) = (term21 s).
Proof. exact (@lem3840487 S (S s)). Qed.
Lemma lem3840489 {A : Type'} (y : A) (x : A) (s : nat) : (term19 A y x s) = (term21 s).
Proof. exact (TRANS (@lem3840484 A y x s) (@lem3840488 s)). Qed.
Lemma lem3840490 {A : Type'} (y : A) (x : A) (s : nat) : ((term19 A x y s) = (term19 A y x s)) = ((term21 s) = (term21 s)).
Proof. exact (MK_COMB (@lem3840450 A x y s) (@lem3840489 A y x s)). Qed.
Lemma lem3840492 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3840493 (x : nat) : (x = x) = True.
Proof. exact (@lem3840492 nat x). Qed.
Lemma lem3840494 (s : nat) : ((term21 s) = (term21 s)) = True.
Proof. exact (@lem3840493 (term21 s)). Qed.
Lemma lem3840495 {A : Type'} (y : A) (x : A) (s : nat) : ((term19 A x y s) = (term19 A y x s)) = True.
Proof. exact (TRANS (@lem3840490 A y x s) (@lem3840494 s)). Qed.
Lemma lem3840496 {A : Type'} (x : A) (y : A) : (term24 A x y) = (term24 A x y).
Proof. exact (eq_refl (term24 A x y)). Qed.
Lemma lem3840497 {A : Type'} (s : nat) (x : A) (y : A) : (term25 A y x s) = (term26 A x y).
Proof. exact (MK_COMB (@lem3840496 A x y) (@lem3840495 A y x s)). Qed.
Lemma lem3840499 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem3840500 {A : Type'} (x : A) (y : A) : (term26 A x y) = True.
Proof. exact (@lem3840499 (term27 A x y)). Qed.
Lemma lem3840501 {A : Type'} (y : A) (x : A) (s : nat) : (term25 A y x s) = True.
Proof. exact (TRANS (@lem3840497 A s x y) (@lem3840500 A x y)). Qed.
Lemma lem3840502 {A : Type'} (y : A) (x : A) : (term28 A y x) = term29.
Proof. exact (fun_ext (fun s : nat => @lem3840501 A y x s)). Qed.
Lemma lem3840503 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3840504 {A : Type'} (y : A) (x : A) : (term30 A y x) = term31.
Proof. exact (MK_COMB (@lem3840503) (@lem3840502 A y x)). Qed.
Lemma lem3840506 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3840507 (t : Prop) : (term33 t) = t.
Proof. exact (@lem3840506 nat t). Qed.
Lemma lem3840508 : term31 = True.
Proof. exact (@lem3840507 True). Qed.
Lemma lem3840509 {A : Type'} (y : A) (x : A) : (term30 A y x) = True.
Proof. exact (TRANS (@lem3840504 A y x) (@lem3840508)). Qed.
Lemma lem3840510 {A : Type'} (x : A) : (term34 A x) = (term35 A).
Proof. exact (fun_ext (fun y : A => @lem3840509 A y x)). Qed.
Lemma lem3840511 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3840512 {A : Type'} (x : A) : (term36 A x) = (term37 A).
Proof. exact (MK_COMB (@lem3840511 A) (@lem3840510 A x)). Qed.
Lemma lem3840514 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3840515 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (@lem3840514 A t). Qed.
Lemma lem3840516 {A : Type'} : (term37 A) = True.
Proof. exact (@lem3840515 A True). Qed.
Lemma lem3840517 {A : Type'} (x : A) : (term36 A x) = True.
Proof. exact (TRANS (@lem3840512 A x) (@lem3840516 A)). Qed.
Lemma lem3840518 {A : Type'} : (term38 A) = (term35 A).
Proof. exact (fun_ext (fun x : A => @lem3840517 A x)). Qed.
Lemma lem3840519 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3840520 {A : Type'} : (term39 A) = (term37 A).
Proof. exact (MK_COMB (@lem3840519 A) (@lem3840518 A)). Qed.
Lemma lem3840522 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3840523 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (@lem3840522 A t). Qed.
Lemma lem3840524 {A : Type'} : (term37 A) = True.
Proof. exact (@lem3840523 A True). Qed.
Lemma lem3840525 {A : Type'} : (term39 A) = True.
Proof. exact (TRANS (@lem3840520 A) (@lem3840524 A)). Qed.
Lemma lem3840526 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3840527 {A : Type'} : (term40 A) = (imp True).
Proof. exact (MK_COMB (@lem3840526) (@lem3840525 A)). Qed.
Lemma lem3840545 {A B : Type'} (f : A -> B) (y : A) : (term8 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3840546 {A : Type'} (f : type1425 A) (y : A) : (term9 A f y) = (f y).
Proof. exact (@lem3840545 A (nat -> nat) f y). Qed.
Lemma lem3840547 {A : Type'} (x : A) : (term10 A x) = (term11 A x).
Proof. exact (@lem3840546 A (term4 A) x). Qed.
Lemma lem3840548 {A : Type'} (x : A) : (term11 A x) = term12.
Proof. exact (eq_refl (term11 A x)). Qed.
Lemma lem3840549 {A : Type'} : (term13 A) = (term4 A).
Proof. exact (fun_ext (fun x : A => @lem3840548 A x)). Qed.
Lemma lem3840550 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3840551 {A : Type'} (x : A) : (term10 A x) = (term11 A x).
Proof. exact (MK_COMB (@lem3840549 A) (@lem3840550 A x)). Qed.
Lemma lem3840552 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem3840553 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (MK_COMB (@lem3840552) (@lem3840551 A x)). Qed.
Lemma lem3840554 {A : Type'} (x : A) : (term11 A x) = term12.
Proof. exact (eq_refl (term11 A x)). Qed.
Lemma lem3840555 {A : Type'} (x : A) : ((term10 A x) = (term11 A x)) = ((term11 A x) = term12).
Proof. exact (MK_COMB (@lem3840553 A x) (@lem3840554 A x)). Qed.
Lemma lem3840556 {A : Type'} (x : A) : (term11 A x) = term12.
Proof. exact (EQ_MP (@lem3840555 A x) (@lem3840547 A x)). Qed.
Lemma lem3840557 {A : Type'} (s : A -> Prop) : (term1 A s) = (term1 A s).
Proof. exact (eq_refl (term1 A s)). Qed.
Lemma lem3840558 {A : Type'} (x : A) (s : A -> Prop) : (term41 A x s) = (term42 A s).
Proof. exact (MK_COMB (@lem3840556 A x) (@lem3840557 A s)). Qed.
Lemma lem3840560 {A B : Type'} (f : A -> B) (y : A) : (term8 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3840561 (f : nat -> nat) (y : nat) : (term18 f y) = (f y).
Proof. exact (@lem3840560 nat nat f y). Qed.
Lemma lem3840562 {A : Type'} (s : A -> Prop) : (term42 A s) = (term43 A s).
Proof. exact (@lem3840561 S (term1 A s)). Qed.
Lemma lem3840563 {A : Type'} (x : A) (s : A -> Prop) : (term41 A x s) = (term43 A s).
Proof. exact (TRANS (@lem3840558 A x s) (@lem3840562 A s)). Qed.
Lemma lem3840564 {A : Type'} (x : A) (s : A -> Prop) : (term44 A x s) = (term44 A x s).
Proof. exact (eq_refl (term44 A x s)). Qed.
Lemma lem3840565 {A : Type'} (x : A) (s : A -> Prop) : (term45 A x s) = (term46 A x s).
Proof. exact (MK_COMB (@lem3840564 A x s) (@lem3840563 A x s)). Qed.
Lemma lem3840566 {A : Type'} (x : A) (s : A -> Prop) : (term47 A x s) = (term47 A x s).
Proof. exact (eq_refl (term47 A x s)). Qed.
Lemma lem3840567 {A : Type'} (x : A) (s : A -> Prop) : ((term48 A x s) = (term45 A x s)) = ((term48 A x s) = (term46 A x s)).
Proof. exact (MK_COMB (@lem3840566 A x s) (@lem3840565 A x s)). Qed.
Lemma lem3840570 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (eq_refl (term49 A s)). Qed.
Lemma lem3840571 {A : Type'} (x : A) (s : A -> Prop) : (term50 A x s) = (term51 A x s).
Proof. exact (MK_COMB (@lem3840570 A s) (@lem3840567 A x s)). Qed.
Lemma lem3840574 {A : Type'} (x : A) : (term52 A x) = (term53 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3840571 A x s)). Qed.
Lemma lem3840575 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3840576 {A : Type'} (x : A) : (term54 A x) = (term55 A x).
Proof. exact (MK_COMB (@lem3840575 A) (@lem3840574 A x)). Qed.
Lemma lem3840581 {A : Type'} : (term56 A) = (term57 A).
Proof. exact (fun_ext (fun x : A => @lem3840576 A x)). Qed.
Lemma lem3840582 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3840583 {A : Type'} : (term58 A) = (term59 A).
Proof. exact (MK_COMB (@lem3840582 A) (@lem3840581 A)). Qed.
Lemma lem3840588 {A : Type'} : (term60 A) = (term60 A).
Proof. exact (eq_refl (term60 A)). Qed.
Lemma lem3840589 {A : Type'} : (term61 A) = (term62 A).
Proof. exact (MK_COMB (@lem3840588 A) (@lem3840583 A)). Qed.
Lemma lem3840592 {A : Type'} : (term7 A) = (term63 A).
Proof. exact (MK_COMB (@lem3840527 A) (@lem3840589 A)). Qed.
Lemma lem3840594 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3840595 {A : Type'} : (term63 A) = (term62 A).
Proof. exact (@lem3840594 (term62 A)). Qed.
Lemma lem3840612 {A : Type'} : (term7 A) = (term62 A).
Proof. exact (TRANS (@lem3840592 A) (@lem3840595 A)). Qed.
Lemma lem3840613 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3840614 {A : Type'} : (term64 A) = (term65 A).
Proof. exact (MK_COMB (@lem3840613) (@lem3840612 A)). Qed.
Lemma lem3840620 {_99571 : Type'} (s : _99571 -> Prop) : (@CARD _99571 s) = (term1 _99571 s).
Proof. exact (EQ_MP (@lem3840379 _99571 s) (@lem3840378 _99571 s)). Qed.
Lemma lem3840621 {A : Type'} (s : A -> Prop) : (@CARD A s) = (term1 A s).
Proof. exact (@lem3840620 A s). Qed.
Lemma lem3840622 {A : Type'} : (@CARD A (@EMPTY A)) = (term66 A).
Proof. exact (@lem3840621 A (@EMPTY A)). Qed.
Lemma lem3840623 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3840624 {A : Type'} : (term67 A) = (term68 A).
Proof. exact (MK_COMB (@lem3840623) (@lem3840622 A)). Qed.
Lemma lem3840625 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem3840626 {A : Type'} : ((@CARD A (@EMPTY A)) = (NUMERAL 0)) = ((term66 A) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem3840624 A) (@lem3840625)). Qed.
Lemma lem3840629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3840630 {A : Type'} : (term69 A) = (term60 A).
Proof. exact (MK_COMB (@lem3840629) (@lem3840626 A)). Qed.
Lemma lem3840644 {_99571 : Type'} (s : _99571 -> Prop) : (@CARD _99571 s) = (term1 _99571 s).
Proof. exact (EQ_MP (@lem3840379 _99571 s) (@lem3840378 _99571 s)). Qed.
Lemma lem3840645 {A : Type'} (s : A -> Prop) : (@CARD A s) = (term1 A s).
Proof. exact (@lem3840644 A s). Qed.
Lemma lem3840646 {A : Type'} (x : A) (s : A -> Prop) : (term70 A x s) = (term48 A x s).
Proof. exact (@lem3840645 A (@INSERT A x s)). Qed.
Lemma lem3840647 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3840648 {A : Type'} (x : A) (s : A -> Prop) : (term71 A x s) = (term47 A x s).
Proof. exact (MK_COMB (@lem3840647) (@lem3840646 A x s)). Qed.
Lemma lem3840650 {_99571 : Type'} (s : _99571 -> Prop) : (@CARD _99571 s) = (term1 _99571 s).
Proof. exact (EQ_MP (@lem3840379 _99571 s) (@lem3840378 _99571 s)). Qed.
Lemma lem3840651 {A : Type'} (s : A -> Prop) : (@CARD A s) = (term1 A s).
Proof. exact (@lem3840650 A s). Qed.
Lemma lem3840652 {A : Type'} (x : A) (s : A -> Prop) : (term72 A x s) = (term72 A x s).
Proof. exact (eq_refl (term72 A x s)). Qed.
Lemma lem3840653 {A : Type'} (x : A) (s : A -> Prop) : (term73 A x s) = (term44 A x s).
Proof. exact (MK_COMB (@lem3840652 A x s) (@lem3840651 A s)). Qed.
Lemma lem3840655 {_99571 : Type'} (s : _99571 -> Prop) : (@CARD _99571 s) = (term1 _99571 s).
Proof. exact (EQ_MP (@lem3840379 _99571 s) (@lem3840378 _99571 s)). Qed.
Lemma lem3840656 {A : Type'} (s : A -> Prop) : (@CARD A s) = (term1 A s).
Proof. exact (@lem3840655 A s). Qed.
Lemma lem3840657 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem3840658 {A : Type'} (s : A -> Prop) : (term74 A s) = (term43 A s).
Proof. exact (MK_COMB (@lem3840657) (@lem3840656 A s)). Qed.
Lemma lem3840659 {A : Type'} (x : A) (s : A -> Prop) : (term75 A x s) = (term46 A x s).
Proof. exact (MK_COMB (@lem3840653 A x s) (@lem3840658 A s)). Qed.
Lemma lem3840660 {A : Type'} (x : A) (s : A -> Prop) : ((term70 A x s) = (term75 A x s)) = ((term48 A x s) = (term46 A x s)).
Proof. exact (MK_COMB (@lem3840648 A x s) (@lem3840659 A x s)). Qed.
Lemma lem3840663 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (eq_refl (term49 A s)). Qed.
Lemma lem3840664 {A : Type'} (x : A) (s : A -> Prop) : (term76 A x s) = (term51 A x s).
Proof. exact (MK_COMB (@lem3840663 A s) (@lem3840660 A x s)). Qed.
Lemma lem3840667 {A : Type'} (x : A) : (term77 A x) = (term53 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3840664 A x s)). Qed.
Lemma lem3840668 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3840669 {A : Type'} (x : A) : (term78 A x) = (term55 A x).
Proof. exact (MK_COMB (@lem3840668 A) (@lem3840667 A x)). Qed.
Lemma lem3840674 {A : Type'} : (term79 A) = (term57 A).
Proof. exact (fun_ext (fun x : A => @lem3840669 A x)). Qed.
Lemma lem3840675 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3840676 {A : Type'} : (term80 A) = (term59 A).
Proof. exact (MK_COMB (@lem3840675 A) (@lem3840674 A)). Qed.
Lemma lem3840681 {A : Type'} : (term81 A) = (term62 A).
Proof. exact (MK_COMB (@lem3840630 A) (@lem3840676 A)). Qed.
Lemma lem3840684 {A : Type'} : (term82 A) = (term83 A).
Proof. exact (MK_COMB (@lem3840614 A) (@lem3840681 A)). Qed.
Lemma lem3840686 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3840687 {A : Type'} : (term83 A) = True.
Proof. exact (@lem3840686 (term62 A)). Qed.
Lemma lem3840688 {A : Type'} : (term82 A) = True.
Proof. exact (TRANS (@lem3840684 A) (@lem3840687 A)). Qed.
Lemma lem3840689 {A : Type'} : True = (term82 A).
Proof. exact (SYM (@lem3840688 A)). Qed.
Lemma lem3840690 {A : Type'} : term82 A.
Proof. exact (EQ_MP (@lem3840689 A) (@lem0)). Qed.
Lemma lem3840691 {A : Type'} : term81 A.
Proof. exact (@lem3840690 A (@lem3840387 A)). Qed.
