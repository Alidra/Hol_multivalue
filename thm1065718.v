Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1065718_term_abbrevs.
Require Import BETA_THM_spec.
Require Import SKOLEM_THM_spec.
Require Import thm75635_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1065452 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem421 A B f). Qed.
Lemma lem1065453 {A B : Type'} (f : A -> B) : (term0 A B f) = (term1 A B f).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem1065454 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (EQ_MP (@lem1065453 A B f) (@lem1065452 A B f)). Qed.
Lemma lem1065455 {A B : Type'} (f : A -> B) (y : A) : term2 A B f y.
Proof. exact (@lem1065454 A B f y). Qed.
Lemma lem1065456 {A B : Type'} (f : A -> B) (y : A) : (term2 A B f y) = ((term3 A B f y) = (f y)).
Proof. exact (eq_refl (term2 A B f y)). Qed.
Lemma lem1065459 {A : Type'} (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : FCONS' = (term4 A _17456).
Proof. exact (h1). Qed.
Lemma lem1065460 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1065461 {A : Type'} (a : A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (FCONS' a) = (term5 A _17456 a).
Proof. exact (MK_COMB (@lem1065459 A FCONS' _17456 h1) (@lem1065460 A a)). Qed.
Lemma lem1065463 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1065456 A B f y) (@lem1065455 A B f y)). Qed.
Lemma lem1065464 {A : Type'} (f : type1380 A) (y : A) : (term6 A f y) = (f y).
Proof. exact (@lem1065463 A (type972 A) f y). Qed.
Lemma lem1065465 {A : Type'} (_17456 : type1593 A) (a : A) : (term7 A _17456 a) = (term5 A _17456 a).
Proof. exact (@lem1065464 A (term4 A _17456) a). Qed.
Lemma lem1065466 {A : Type'} (_17456 : type1593 A) (_17453 : A) : (term5 A _17456 _17453) = (term8 A _17456 _17453).
Proof. exact (eq_refl (term5 A _17456 _17453)). Qed.
Lemma lem1065467 {A : Type'} (_17456 : type1593 A) : (term9 A _17456) = (term4 A _17456).
Proof. exact (fun_ext (fun _17453 : A => @lem1065466 A _17456 _17453)). Qed.
Lemma lem1065468 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1065469 {A : Type'} (_17456 : type1593 A) (a : A) : (term7 A _17456 a) = (term5 A _17456 a).
Proof. exact (MK_COMB (@lem1065467 A _17456) (@lem1065468 A a)). Qed.
Lemma lem1065470 {A : Type'} : (@eq ((nat -> A) -> nat -> A)) = (@eq ((nat -> A) -> nat -> A)).
Proof. exact (eq_refl (@eq ((nat -> A) -> nat -> A))). Qed.
Lemma lem1065471 {A : Type'} (_17456 : type1593 A) (a : A) : (term10 A _17456 a) = (term11 A _17456 a).
Proof. exact (MK_COMB (@lem1065470 A) (@lem1065469 A _17456 a)). Qed.
Lemma lem1065472 {A : Type'} (_17456 : type1593 A) (a : A) : (term5 A _17456 a) = (term8 A _17456 a).
Proof. exact (eq_refl (term5 A _17456 a)). Qed.
Lemma lem1065473 {A : Type'} (_17456 : type1593 A) (a : A) : ((term7 A _17456 a) = (term5 A _17456 a)) = ((term5 A _17456 a) = (term8 A _17456 a)).
Proof. exact (MK_COMB (@lem1065471 A _17456 a) (@lem1065472 A _17456 a)). Qed.
Lemma lem1065474 {A : Type'} (_17456 : type1593 A) (a : A) : (term5 A _17456 a) = (term8 A _17456 a).
Proof. exact (EQ_MP (@lem1065473 A _17456 a) (@lem1065465 A _17456 a)). Qed.
Lemma lem1065475 {A : Type'} (a : A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (FCONS' a) = (term8 A _17456 a).
Proof. exact (TRANS (@lem1065461 A a FCONS' _17456 h1) (@lem1065474 A _17456 a)). Qed.
Lemma lem1065476 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1065477 {A : Type'} (a : A) (f : nat -> A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (FCONS' a f) = (term12 A _17456 a f).
Proof. exact (MK_COMB (@lem1065475 A a FCONS' _17456 h1) (@lem1065476 A f)). Qed.
Lemma lem1065479 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1065456 A B f y) (@lem1065455 A B f y)). Qed.
Lemma lem1065480 {A : Type'} (f : type972 A) (y : nat -> A) : (term13 A f y) = (f y).
Proof. exact (@lem1065479 (nat -> A) (nat -> A) f y). Qed.
Lemma lem1065481 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term14 A _17456 a f) = (term12 A _17456 a f).
Proof. exact (@lem1065480 A (term8 A _17456 a) f). Qed.
Lemma lem1065482 {A : Type'} (_17456 : type1593 A) (a : A) (_17454 : nat -> A) : (term12 A _17456 a _17454) = (term15 A _17456 a _17454).
Proof. exact (eq_refl (term12 A _17456 a _17454)). Qed.
Lemma lem1065483 {A : Type'} (_17456 : type1593 A) (a : A) : (term16 A _17456 a) = (term8 A _17456 a).
Proof. exact (fun_ext (fun _17454 : nat -> A => @lem1065482 A _17456 a _17454)). Qed.
Lemma lem1065484 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1065485 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term14 A _17456 a f) = (term12 A _17456 a f).
Proof. exact (MK_COMB (@lem1065483 A _17456 a) (@lem1065484 A f)). Qed.
Lemma lem1065486 {A : Type'} : (@eq (nat -> A)) = (@eq (nat -> A)).
Proof. exact (eq_refl (@eq (nat -> A))). Qed.
Lemma lem1065487 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term17 A _17456 a f) = (term18 A _17456 a f).
Proof. exact (MK_COMB (@lem1065486 A) (@lem1065485 A _17456 a f)). Qed.
Lemma lem1065488 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term12 A _17456 a f) = (term15 A _17456 a f).
Proof. exact (eq_refl (term12 A _17456 a f)). Qed.
Lemma lem1065489 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : ((term14 A _17456 a f) = (term12 A _17456 a f)) = ((term12 A _17456 a f) = (term15 A _17456 a f)).
Proof. exact (MK_COMB (@lem1065487 A _17456 a f) (@lem1065488 A _17456 a f)). Qed.
Lemma lem1065490 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term12 A _17456 a f) = (term15 A _17456 a f).
Proof. exact (EQ_MP (@lem1065489 A _17456 a f) (@lem1065481 A _17456 a f)). Qed.
Lemma lem1065491 {A : Type'} (a : A) (f : nat -> A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (FCONS' a f) = (term15 A _17456 a f).
Proof. exact (TRANS (@lem1065477 A a f FCONS' _17456 h1) (@lem1065490 A _17456 a f)). Qed.
Lemma lem1065492 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1065493 {A : Type'} (a : A) (f : nat -> A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term19 A FCONS' a f) = (term20 A _17456 a f).
Proof. exact (MK_COMB (@lem1065491 A a f FCONS' _17456 h1) (@lem1065492)). Qed.
Lemma lem1065495 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1065456 A B f y) (@lem1065455 A B f y)). Qed.
Lemma lem1065496 {A : Type'} (f : nat -> A) (y : nat) : (term21 A f y) = (f y).
Proof. exact (@lem1065495 nat A f y). Qed.
Lemma lem1065497 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term22 A _17456 a f) = (term20 A _17456 a f).
Proof. exact (@lem1065496 A (term15 A _17456 a f) (NUMERAL 0)). Qed.
Lemma lem1065498 {A : Type'} (_17456 : type1593 A) (_17455 : nat) (a : A) (f : nat -> A) : (term23 A _17456 a f _17455) = (_17456 _17455 a f).
Proof. exact (eq_refl (term23 A _17456 a f _17455)). Qed.
Lemma lem1065499 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term24 A _17456 a f) = (term15 A _17456 a f).
Proof. exact (fun_ext (fun _17455 : nat => @lem1065498 A _17456 _17455 a f)). Qed.
Lemma lem1065500 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1065501 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term22 A _17456 a f) = (term20 A _17456 a f).
Proof. exact (MK_COMB (@lem1065499 A _17456 a f) (@lem1065500)). Qed.
Lemma lem1065502 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1065503 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term25 A _17456 a f) = (term26 A _17456 a f).
Proof. exact (MK_COMB (@lem1065502 A) (@lem1065501 A _17456 a f)). Qed.
Lemma lem1065504 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term20 A _17456 a f) = (term27 A _17456 a f).
Proof. exact (eq_refl (term20 A _17456 a f)). Qed.
Lemma lem1065505 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : ((term22 A _17456 a f) = (term20 A _17456 a f)) = ((term20 A _17456 a f) = (term27 A _17456 a f)).
Proof. exact (MK_COMB (@lem1065503 A _17456 a f) (@lem1065504 A _17456 a f)). Qed.
Lemma lem1065506 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term20 A _17456 a f) = (term27 A _17456 a f).
Proof. exact (EQ_MP (@lem1065505 A _17456 a f) (@lem1065497 A _17456 a f)). Qed.
Lemma lem1065507 {A : Type'} (a : A) (f : nat -> A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term19 A FCONS' a f) = (term27 A _17456 a f).
Proof. exact (TRANS (@lem1065493 A a f FCONS' _17456 h1) (@lem1065506 A _17456 a f)). Qed.
Lemma lem1065508 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1065509 {A : Type'} (a : A) (f : nat -> A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term28 A FCONS' a f) = (term29 A _17456 a f).
Proof. exact (MK_COMB (@lem1065508 A) (@lem1065507 A a f FCONS' _17456 h1)). Qed.
Lemma lem1065510 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1065511 {A : Type'} (f : nat -> A) (a : A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : ((term19 A FCONS' a f) = a) = ((term27 A _17456 a f) = a).
Proof. exact (MK_COMB (@lem1065509 A a f FCONS' _17456 h1) (@lem1065510 A a)). Qed.
Lemma lem1065512 {A : Type'} (a : A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term30 A FCONS' a) = (term31 A _17456 a).
Proof. exact (fun_ext (fun f : nat -> A => @lem1065511 A f a FCONS' _17456 h1)). Qed.
Lemma lem1065513 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem1065514 {A : Type'} (a : A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term32 A FCONS' a) = (term33 A _17456 a).
Proof. exact (MK_COMB (@lem1065513 A) (@lem1065512 A a FCONS' _17456 h1)). Qed.
Lemma lem1065515 {A : Type'} (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term34 A FCONS') = (term35 A _17456).
Proof. exact (fun_ext (fun a : A => @lem1065514 A a FCONS' _17456 h1)). Qed.
Lemma lem1065516 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1065517 {A : Type'} (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term36 A FCONS') = (term37 A _17456).
Proof. exact (MK_COMB (@lem1065516 A) (@lem1065515 A FCONS' _17456 h1)). Qed.
Lemma lem1065518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1065519 {A : Type'} (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term38 A FCONS') = (term39 A _17456).
Proof. exact (MK_COMB (@lem1065518) (@lem1065517 A FCONS' _17456 h1)). Qed.
Lemma lem1065521 {A : Type'} (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : FCONS' = (term4 A _17456).
Proof. exact (h1). Qed.
Lemma lem1065522 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1065523 {A : Type'} (a : A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (FCONS' a) = (term5 A _17456 a).
Proof. exact (MK_COMB (@lem1065521 A FCONS' _17456 h1) (@lem1065522 A a)). Qed.
Lemma lem1065525 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1065456 A B f y) (@lem1065455 A B f y)). Qed.
Lemma lem1065526 {A : Type'} (f : type1380 A) (y : A) : (term6 A f y) = (f y).
Proof. exact (@lem1065525 A (type972 A) f y). Qed.
Lemma lem1065527 {A : Type'} (_17456 : type1593 A) (a : A) : (term7 A _17456 a) = (term5 A _17456 a).
Proof. exact (@lem1065526 A (term4 A _17456) a). Qed.
Lemma lem1065528 {A : Type'} (_17456 : type1593 A) (_17453 : A) : (term5 A _17456 _17453) = (term8 A _17456 _17453).
Proof. exact (eq_refl (term5 A _17456 _17453)). Qed.
Lemma lem1065529 {A : Type'} (_17456 : type1593 A) : (term9 A _17456) = (term4 A _17456).
Proof. exact (fun_ext (fun _17453 : A => @lem1065528 A _17456 _17453)). Qed.
Lemma lem1065530 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1065531 {A : Type'} (_17456 : type1593 A) (a : A) : (term7 A _17456 a) = (term5 A _17456 a).
Proof. exact (MK_COMB (@lem1065529 A _17456) (@lem1065530 A a)). Qed.
Lemma lem1065532 {A : Type'} : (@eq ((nat -> A) -> nat -> A)) = (@eq ((nat -> A) -> nat -> A)).
Proof. exact (eq_refl (@eq ((nat -> A) -> nat -> A))). Qed.
Lemma lem1065533 {A : Type'} (_17456 : type1593 A) (a : A) : (term10 A _17456 a) = (term11 A _17456 a).
Proof. exact (MK_COMB (@lem1065532 A) (@lem1065531 A _17456 a)). Qed.
Lemma lem1065534 {A : Type'} (_17456 : type1593 A) (a : A) : (term5 A _17456 a) = (term8 A _17456 a).
Proof. exact (eq_refl (term5 A _17456 a)). Qed.
Lemma lem1065535 {A : Type'} (_17456 : type1593 A) (a : A) : ((term7 A _17456 a) = (term5 A _17456 a)) = ((term5 A _17456 a) = (term8 A _17456 a)).
Proof. exact (MK_COMB (@lem1065533 A _17456 a) (@lem1065534 A _17456 a)). Qed.
Lemma lem1065536 {A : Type'} (_17456 : type1593 A) (a : A) : (term5 A _17456 a) = (term8 A _17456 a).
Proof. exact (EQ_MP (@lem1065535 A _17456 a) (@lem1065527 A _17456 a)). Qed.
Lemma lem1065537 {A : Type'} (a : A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (FCONS' a) = (term8 A _17456 a).
Proof. exact (TRANS (@lem1065523 A a FCONS' _17456 h1) (@lem1065536 A _17456 a)). Qed.
Lemma lem1065538 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1065539 {A : Type'} (a : A) (f : nat -> A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (FCONS' a f) = (term12 A _17456 a f).
Proof. exact (MK_COMB (@lem1065537 A a FCONS' _17456 h1) (@lem1065538 A f)). Qed.
Lemma lem1065541 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1065456 A B f y) (@lem1065455 A B f y)). Qed.
Lemma lem1065542 {A : Type'} (f : type972 A) (y : nat -> A) : (term13 A f y) = (f y).
Proof. exact (@lem1065541 (nat -> A) (nat -> A) f y). Qed.
Lemma lem1065543 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term14 A _17456 a f) = (term12 A _17456 a f).
Proof. exact (@lem1065542 A (term8 A _17456 a) f). Qed.
Lemma lem1065544 {A : Type'} (_17456 : type1593 A) (a : A) (_17454 : nat -> A) : (term12 A _17456 a _17454) = (term15 A _17456 a _17454).
Proof. exact (eq_refl (term12 A _17456 a _17454)). Qed.
Lemma lem1065545 {A : Type'} (_17456 : type1593 A) (a : A) : (term16 A _17456 a) = (term8 A _17456 a).
Proof. exact (fun_ext (fun _17454 : nat -> A => @lem1065544 A _17456 a _17454)). Qed.
Lemma lem1065546 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1065547 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term14 A _17456 a f) = (term12 A _17456 a f).
Proof. exact (MK_COMB (@lem1065545 A _17456 a) (@lem1065546 A f)). Qed.
Lemma lem1065548 {A : Type'} : (@eq (nat -> A)) = (@eq (nat -> A)).
Proof. exact (eq_refl (@eq (nat -> A))). Qed.
Lemma lem1065549 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term17 A _17456 a f) = (term18 A _17456 a f).
Proof. exact (MK_COMB (@lem1065548 A) (@lem1065547 A _17456 a f)). Qed.
Lemma lem1065550 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term12 A _17456 a f) = (term15 A _17456 a f).
Proof. exact (eq_refl (term12 A _17456 a f)). Qed.
Lemma lem1065551 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : ((term14 A _17456 a f) = (term12 A _17456 a f)) = ((term12 A _17456 a f) = (term15 A _17456 a f)).
Proof. exact (MK_COMB (@lem1065549 A _17456 a f) (@lem1065550 A _17456 a f)). Qed.
Lemma lem1065552 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term12 A _17456 a f) = (term15 A _17456 a f).
Proof. exact (EQ_MP (@lem1065551 A _17456 a f) (@lem1065543 A _17456 a f)). Qed.
Lemma lem1065553 {A : Type'} (a : A) (f : nat -> A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (FCONS' a f) = (term15 A _17456 a f).
Proof. exact (TRANS (@lem1065539 A a f FCONS' _17456 h1) (@lem1065552 A _17456 a f)). Qed.
Lemma lem1065554 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem1065555 {A : Type'} (a : A) (f : nat -> A) (n : nat) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term40 A FCONS' a f n) = (term41 A _17456 a f n).
Proof. exact (MK_COMB (@lem1065553 A a f FCONS' _17456 h1) (@lem1065554 n)). Qed.
Lemma lem1065557 {A B : Type'} (f : A -> B) (y : A) : (term3 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1065456 A B f y) (@lem1065455 A B f y)). Qed.
Lemma lem1065558 {A : Type'} (f : nat -> A) (y : nat) : (term21 A f y) = (f y).
Proof. exact (@lem1065557 nat A f y). Qed.
Lemma lem1065559 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) (n : nat) : (term42 A _17456 a f n) = (term41 A _17456 a f n).
Proof. exact (@lem1065558 A (term15 A _17456 a f) (S n)). Qed.
Lemma lem1065560 {A : Type'} (_17456 : type1593 A) (_17455 : nat) (a : A) (f : nat -> A) : (term23 A _17456 a f _17455) = (_17456 _17455 a f).
Proof. exact (eq_refl (term23 A _17456 a f _17455)). Qed.
Lemma lem1065561 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term24 A _17456 a f) = (term15 A _17456 a f).
Proof. exact (fun_ext (fun _17455 : nat => @lem1065560 A _17456 _17455 a f)). Qed.
Lemma lem1065562 (n : nat) : (S n) = (S n).
Proof. exact (eq_refl (S n)). Qed.
Lemma lem1065563 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) (n : nat) : (term42 A _17456 a f n) = (term41 A _17456 a f n).
Proof. exact (MK_COMB (@lem1065561 A _17456 a f) (@lem1065562 n)). Qed.
Lemma lem1065564 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1065565 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) (n : nat) : (term43 A _17456 a f n) = (term44 A _17456 a f n).
Proof. exact (MK_COMB (@lem1065564 A) (@lem1065563 A _17456 a f n)). Qed.
Lemma lem1065566 {A : Type'} (_17456 : type1593 A) (n : nat) (a : A) (f : nat -> A) : (term41 A _17456 a f n) = (term45 A _17456 n a f).
Proof. exact (eq_refl (term41 A _17456 a f n)). Qed.
Lemma lem1065567 {A : Type'} (_17456 : type1593 A) (n : nat) (a : A) (f : nat -> A) : ((term42 A _17456 a f n) = (term41 A _17456 a f n)) = ((term41 A _17456 a f n) = (term45 A _17456 n a f)).
Proof. exact (MK_COMB (@lem1065565 A _17456 a f n) (@lem1065566 A _17456 n a f)). Qed.
Lemma lem1065568 {A : Type'} (_17456 : type1593 A) (n : nat) (a : A) (f : nat -> A) : (term41 A _17456 a f n) = (term45 A _17456 n a f).
Proof. exact (EQ_MP (@lem1065567 A _17456 n a f) (@lem1065559 A _17456 a f n)). Qed.
Lemma lem1065569 {A : Type'} (n : nat) (a : A) (f : nat -> A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term40 A FCONS' a f n) = (term45 A _17456 n a f).
Proof. exact (TRANS (@lem1065555 A a f n FCONS' _17456 h1) (@lem1065568 A _17456 n a f)). Qed.
Lemma lem1065570 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1065571 {A : Type'} (n : nat) (a : A) (f : nat -> A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term46 A FCONS' a f n) = (term47 A _17456 n a f).
Proof. exact (MK_COMB (@lem1065570 A) (@lem1065569 A n a f FCONS' _17456 h1)). Qed.
Lemma lem1065572 {A : Type'} (f : nat -> A) (n : nat) : (f n) = (f n).
Proof. exact (eq_refl (f n)). Qed.
Lemma lem1065573 {A : Type'} (a : A) (f : nat -> A) (n : nat) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : ((term40 A FCONS' a f n) = (f n)) = ((term45 A _17456 n a f) = (f n)).
Proof. exact (MK_COMB (@lem1065571 A n a f FCONS' _17456 h1) (@lem1065572 A f n)). Qed.
Lemma lem1065574 {A : Type'} (a : A) (f : nat -> A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term48 A FCONS' a f) = (term49 A _17456 a f).
Proof. exact (fun_ext (fun n : nat => @lem1065573 A a f n FCONS' _17456 h1)). Qed.
Lemma lem1065575 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1065576 {A : Type'} (a : A) (f : nat -> A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term50 A FCONS' a f) = (term51 A _17456 a f).
Proof. exact (MK_COMB (@lem1065575) (@lem1065574 A a f FCONS' _17456 h1)). Qed.
Lemma lem1065577 {A : Type'} (a : A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term52 A FCONS' a) = (term53 A _17456 a).
Proof. exact (fun_ext (fun f : nat -> A => @lem1065576 A a f FCONS' _17456 h1)). Qed.
Lemma lem1065578 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem1065579 {A : Type'} (a : A) (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term54 A FCONS' a) = (term55 A _17456 a).
Proof. exact (MK_COMB (@lem1065578 A) (@lem1065577 A a FCONS' _17456 h1)). Qed.
Lemma lem1065580 {A : Type'} (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term56 A FCONS') = (term57 A _17456).
Proof. exact (fun_ext (fun a : A => @lem1065579 A a FCONS' _17456 h1)). Qed.
Lemma lem1065581 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1065582 {A : Type'} (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term58 A FCONS') = (term59 A _17456).
Proof. exact (MK_COMB (@lem1065581 A) (@lem1065580 A FCONS' _17456 h1)). Qed.
Lemma lem1065583 {A : Type'} (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term60 A FCONS') = (term61 A _17456).
Proof. exact (MK_COMB (@lem1065519 A FCONS' _17456 h1) (@lem1065582 A FCONS' _17456 h1)). Qed.
Lemma lem1065584 {A : Type'} (_17456 : type1593 A) (h1 : (term62 A _17456) = (term63 A)) : (term62 A _17456) = (term63 A).
Proof. exact (h1). Qed.
Lemma lem1065585 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1065586 {A : Type'} (a : A) (_17456 : type1593 A) (h1 : (term62 A _17456) = (term63 A)) : (term64 A _17456 a) = (term65 A a).
Proof. exact (MK_COMB (@lem1065584 A _17456 h1) (@lem1065585 A a)). Qed.
Lemma lem1065587 {A : Type'} (a : A) : (term65 A a) = (term66 A a).
Proof. exact (eq_refl (term65 A a)). Qed.
Lemma lem1065588 {A : Type'} (_17456 : type1593 A) (a : A) : (term67 A _17456 a) = (term67 A _17456 a).
Proof. exact (eq_refl (term67 A _17456 a)). Qed.
Lemma lem1065589 {A : Type'} (_17456 : type1593 A) (a : A) : ((term64 A _17456 a) = (term65 A a)) = ((term64 A _17456 a) = (term66 A a)).
Proof. exact (MK_COMB (@lem1065588 A _17456 a) (@lem1065587 A a)). Qed.
Lemma lem1065590 {A : Type'} (a : A) (_17456 : type1593 A) (h1 : (term62 A _17456) = (term63 A)) : (term64 A _17456 a) = (term66 A a).
Proof. exact (EQ_MP (@lem1065589 A _17456 a) (@lem1065586 A a _17456 h1)). Qed.
Lemma lem1065591 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1065592 {A : Type'} (a : A) (f : nat -> A) (_17456 : type1593 A) (h1 : (term62 A _17456) = (term63 A)) : (term27 A _17456 a f) = (term68 A a f).
Proof. exact (MK_COMB (@lem1065590 A a _17456 h1) (@lem1065591 A f)). Qed.
Lemma lem1065593 {A : Type'} (f : nat -> A) (a : A) : (term68 A a f) = a.
Proof. exact (eq_refl (term68 A a f)). Qed.
Lemma lem1065594 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) : (term29 A _17456 a f) = (term29 A _17456 a f).
Proof. exact (eq_refl (term29 A _17456 a f)). Qed.
Lemma lem1065595 {A : Type'} (_17456 : type1593 A) (f : nat -> A) (a : A) : ((term27 A _17456 a f) = (term68 A a f)) = ((term27 A _17456 a f) = a).
Proof. exact (MK_COMB (@lem1065594 A _17456 a f) (@lem1065593 A f a)). Qed.
Lemma lem1065596 {A : Type'} (f : nat -> A) (a : A) (_17456 : type1593 A) (h1 : (term62 A _17456) = (term63 A)) : (term27 A _17456 a f) = a.
Proof. exact (EQ_MP (@lem1065595 A _17456 f a) (@lem1065592 A a f _17456 h1)). Qed.
Lemma lem1065597 {A : Type'} (a : A) (_17456 : type1593 A) (h1 : (term62 A _17456) = (term63 A)) : term33 A _17456 a.
Proof. exact (fun f : nat -> A => @lem1065596 A f a _17456 h1). Qed.
Lemma lem1065598 {A : Type'} (_17456 : type1593 A) (h1 : (term62 A _17456) = (term63 A)) : term37 A _17456.
Proof. exact (fun a : A => @lem1065597 A a _17456 h1). Qed.
Lemma lem1065599 {A : Type'} (_17456 : type1593 A) (h1 : term69 A _17456) : term69 A _17456.
Proof. exact (h1). Qed.
Lemma lem1065600 {A : Type'} (n : nat) (_17456 : type1593 A) (h1 : term69 A _17456) : term70 A _17456 n.
Proof. exact (@lem1065599 A _17456 h1 n). Qed.
Lemma lem1065601 {A : Type'} (_17456 : type1593 A) (n : nat) : (term70 A _17456 n) = ((term71 A _17456 n) = (term72 A n)).
Proof. exact (eq_refl (term70 A _17456 n)). Qed.
Lemma lem1065602 {A : Type'} (n : nat) (_17456 : type1593 A) (h1 : term69 A _17456) : (term71 A _17456 n) = (term72 A n).
Proof. exact (EQ_MP (@lem1065601 A _17456 n) (@lem1065600 A n _17456 h1)). Qed.
Lemma lem1065603 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1065604 {A : Type'} (n : nat) (a : A) (_17456 : type1593 A) (h1 : term69 A _17456) : (term73 A _17456 n a) = (term74 A n a).
Proof. exact (MK_COMB (@lem1065602 A n _17456 h1) (@lem1065603 A a)). Qed.
Lemma lem1065605 {A : Type'} (a : A) (n : nat) : (term74 A n a) = (term75 A n).
Proof. exact (eq_refl (term74 A n a)). Qed.
Lemma lem1065606 {A : Type'} (_17456 : type1593 A) (n : nat) (a : A) : (term76 A _17456 n a) = (term76 A _17456 n a).
Proof. exact (eq_refl (term76 A _17456 n a)). Qed.
Lemma lem1065607 {A : Type'} (_17456 : type1593 A) (a : A) (n : nat) : ((term73 A _17456 n a) = (term74 A n a)) = ((term73 A _17456 n a) = (term75 A n)).
Proof. exact (MK_COMB (@lem1065606 A _17456 n a) (@lem1065605 A a n)). Qed.
Lemma lem1065608 {A : Type'} (a : A) (n : nat) (_17456 : type1593 A) (h1 : term69 A _17456) : (term73 A _17456 n a) = (term75 A n).
Proof. exact (EQ_MP (@lem1065607 A _17456 a n) (@lem1065604 A n a _17456 h1)). Qed.
Lemma lem1065609 {A : Type'} (f : nat -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem1065610 {A : Type'} (a : A) (n : nat) (f : nat -> A) (_17456 : type1593 A) (h1 : term69 A _17456) : (term45 A _17456 n a f) = (term77 A n f).
Proof. exact (MK_COMB (@lem1065608 A a n _17456 h1) (@lem1065609 A f)). Qed.
Lemma lem1065611 {A : Type'} (f : nat -> A) (n : nat) : (term77 A n f) = (f n).
Proof. exact (eq_refl (term77 A n f)). Qed.
Lemma lem1065612 {A : Type'} (_17456 : type1593 A) (n : nat) (a : A) (f : nat -> A) : (term47 A _17456 n a f) = (term47 A _17456 n a f).
Proof. exact (eq_refl (term47 A _17456 n a f)). Qed.
Lemma lem1065613 {A : Type'} (_17456 : type1593 A) (a : A) (f : nat -> A) (n : nat) : ((term45 A _17456 n a f) = (term77 A n f)) = ((term45 A _17456 n a f) = (f n)).
Proof. exact (MK_COMB (@lem1065612 A _17456 n a f) (@lem1065611 A f n)). Qed.
Lemma lem1065614 {A : Type'} (a : A) (f : nat -> A) (n : nat) (_17456 : type1593 A) (h1 : term69 A _17456) : (term45 A _17456 n a f) = (f n).
Proof. exact (EQ_MP (@lem1065613 A _17456 a f n) (@lem1065610 A a n f _17456 h1)). Qed.
Lemma lem1065615 {A : Type'} (a : A) (f : nat -> A) (_17456 : type1593 A) (h1 : term69 A _17456) : term51 A _17456 a f.
Proof. exact (fun n : nat => @lem1065614 A a f n _17456 h1). Qed.
Lemma lem1065616 {A : Type'} (a : A) (_17456 : type1593 A) (h1 : term69 A _17456) : term55 A _17456 a.
Proof. exact (fun f : nat -> A => @lem1065615 A a f _17456 h1). Qed.
Lemma lem1065617 {A : Type'} (_17456 : type1593 A) (h1 : term69 A _17456) : term59 A _17456.
Proof. exact (fun a : A => @lem1065616 A a _17456 h1). Qed.
Lemma lem1065618 {A : Type'} (_17456 : type1593 A) (h1 : term78 A _17456) : term78 A _17456.
Proof. exact (h1). Qed.
Lemma lem1065619 {A : Type'} (_17456 : type1593 A) (h1 : term78 A _17456) : term69 A _17456.
Proof. exact (proj2 (@lem1065618 A _17456 h1)). Qed.
Lemma lem1065620 {A : Type'} (_17456 : type1593 A) (h1 : term78 A _17456) : (term62 A _17456) = (term63 A).
Proof. exact (proj1 (@lem1065618 A _17456 h1)). Qed.
Lemma lem1065621 {A : Type'} (_17456 : type1593 A) (h1 : term78 A _17456) : ((term62 A _17456) = (term63 A)) = (term37 A _17456).
Proof. exact (prop_ext (fun h2 : (term62 A _17456) = (term63 A) => @lem1065598 A _17456 h2) (fun h2 : term37 A _17456 => @lem1065620 A _17456 h1)). Qed.
Lemma lem1065622 {A : Type'} (_17456 : type1593 A) (h1 : term78 A _17456) : term37 A _17456.
Proof. exact (EQ_MP (@lem1065621 A _17456 h1) (@lem1065620 A _17456 h1)). Qed.
Lemma lem1065623 {A : Type'} (_17456 : type1593 A) (h1 : term78 A _17456) : (term69 A _17456) = (term59 A _17456).
Proof. exact (prop_ext (fun h2 : term69 A _17456 => @lem1065617 A _17456 h2) (fun h2 : term59 A _17456 => @lem1065619 A _17456 h1)). Qed.
Lemma lem1065624 {A : Type'} (_17456 : type1593 A) (h1 : term78 A _17456) : term59 A _17456.
Proof. exact (EQ_MP (@lem1065623 A _17456 h1) (@lem1065619 A _17456 h1)). Qed.
Lemma lem1065625 {A : Type'} (_17456 : type1593 A) (h1 : term78 A _17456) : term61 A _17456.
Proof. exact (conj (@lem1065622 A _17456 h1) (@lem1065624 A _17456 h1)). Qed.
Lemma lem1065626 {A : Type'} (e : A) : term79 A e.
Proof. exact (@lem75635 A e). Qed.
Lemma lem1065627 {A : Type'} (e : A) : (term79 A e) = (term80 A e).
Proof. exact (eq_refl (term79 A e)). Qed.
Lemma lem1065628 {A : Type'} (e : A) : term80 A e.
Proof. exact (EQ_MP (@lem1065627 A e) (@lem1065626 A e)). Qed.
Lemma lem1065629 {A : Type'} (e : A) (f : type1423 A) : term81 A e f.
Proof. exact (@lem1065628 A e f). Qed.
Lemma lem1065630 {A : Type'} (e : A) (f : type1423 A) : (term81 A e f) = (term82 A e f).
Proof. exact (eq_refl (term81 A e f)). Qed.
Lemma lem1065631 {A : Type'} (e : A) (f : type1423 A) : term82 A e f.
Proof. exact (EQ_MP (@lem1065630 A e f) (@lem1065629 A e f)). Qed.
Lemma lem1065632 {A : Type'} (e : type1381 A) (f : type393 A) : term83 A e f.
Proof. exact (@lem1065631 (type1381 A) e f). Qed.
Lemma lem1065633 {A : Type'} : term84 A.
Proof. exact (@lem1065632 A (term63 A) (term85 A)). Qed.
Lemma lem1065634 {A : Type'} (fn : type1593 A) (n : nat) : (term86 A fn n) = (term87 A).
Proof. exact (eq_refl (term86 A fn n)). Qed.
Lemma lem1065635 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1065636 {A : Type'} (fn : type1593 A) (n : nat) : (term88 A fn n) = (term89 A n).
Proof. exact (MK_COMB (@lem1065634 A fn n) (@lem1065635 n)). Qed.
Lemma lem1065637 {A : Type'} (n : nat) : (term89 A n) = (term72 A n).
Proof. exact (eq_refl (term89 A n)). Qed.
Lemma lem1065638 {A : Type'} (fn : type1593 A) (n : nat) : (term88 A fn n) = (term72 A n).
Proof. exact (TRANS (@lem1065636 A fn n) (@lem1065637 A n)). Qed.
Lemma lem1065639 {A : Type'} (fn : type1593 A) (n : nat) : (term90 A fn n) = (term90 A fn n).
Proof. exact (eq_refl (term90 A fn n)). Qed.
Lemma lem1065640 {A : Type'} (fn : type1593 A) (n : nat) : ((term71 A fn n) = (term88 A fn n)) = ((term71 A fn n) = (term72 A n)).
Proof. exact (MK_COMB (@lem1065639 A fn n) (@lem1065638 A fn n)). Qed.
Lemma lem1065641 {A : Type'} (fn : type1593 A) : (term91 A fn) = (term92 A fn).
Proof. exact (fun_ext (fun n : nat => @lem1065640 A fn n)). Qed.
Lemma lem1065642 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1065643 {A : Type'} (fn : type1593 A) : (term93 A fn) = (term69 A fn).
Proof. exact (MK_COMB (@lem1065642) (@lem1065641 A fn)). Qed.
Lemma lem1065644 {A : Type'} (fn : type1593 A) : (term94 A fn) = (term94 A fn).
Proof. exact (eq_refl (term94 A fn)). Qed.
Lemma lem1065645 {A : Type'} (fn : type1593 A) : (term95 A fn) = (term78 A fn).
Proof. exact (MK_COMB (@lem1065644 A fn) (@lem1065643 A fn)). Qed.
Lemma lem1065646 {A : Type'} : (term96 A) = (term97 A).
Proof. exact (fun_ext (fun fn : type1593 A => @lem1065645 A fn)). Qed.
Lemma lem1065647 {A : Type'} : (@ex (nat -> A -> (nat -> A) -> A)) = (@ex (nat -> A -> (nat -> A) -> A)).
Proof. exact (eq_refl (@ex (nat -> A -> (nat -> A) -> A))). Qed.
Lemma lem1065648 {A : Type'} : (term84 A) = (term98 A).
Proof. exact (MK_COMB (@lem1065647 A) (@lem1065646 A)). Qed.
Lemma lem1065649 {A : Type'} : term98 A.
Proof. exact (EQ_MP (@lem1065648 A) (@lem1065633 A)). Qed.
Lemma lem1065650 {A : Type'} (_17456 : type1593 A) (h1 : term78 A _17456) : term78 A _17456.
Proof. exact (h1). Qed.
Lemma lem1065651 {A : Type'} (_17456 : type1593 A) (h1 : term78 A _17456) : term69 A _17456.
Proof. exact (proj2 (@lem1065650 A _17456 h1)). Qed.
Lemma lem1065652 {A : Type'} (_17456 : type1593 A) (h1 : term78 A _17456) : (term62 A _17456) = (term63 A).
Proof. exact (proj1 (@lem1065650 A _17456 h1)). Qed.
Lemma lem1065653 {A : Type'} (_17456 : type1593 A) (h1 : term78 A _17456) : term78 A _17456.
Proof. exact (conj (@lem1065652 A _17456 h1) (@lem1065651 A _17456 h1)). Qed.
Lemma lem1065654 {A : Type'} (_17456 : type1593 A) (h1 : term78 A _17456) : term98 A.
Proof. exact (ex_intro (term97 A) _17456 (@lem1065653 A _17456 h1)). Qed.
Lemma lem1065655 {A : Type'} (h1 : term98 A) : term98 A.
Proof. exact (h1). Qed.
Lemma lem1065656 {A : Type'} (h1 : term98 A) : term98 A.
Proof. exact (ex_elim (@lem1065655 A h1) (fun _17456 : type1593 A => fun h0 : term97 A _17456 => @lem1065654 A _17456 h0)). Qed.
Lemma lem1065657 {A : Type'} : (term98 A) = (term98 A).
Proof. exact (prop_ext (fun h1 : term98 A => @lem1065656 A h1) (fun h1 : term98 A => @lem1065649 A)). Qed.
Lemma lem1065658 {A : Type'} : term98 A.
Proof. exact (EQ_MP (@lem1065657 A) (@lem1065649 A)). Qed.
Lemma lem1065659 {A : Type'} (_17456 : type1593 A) (h1 : term78 A _17456) : term99 A.
Proof. exact (ex_intro (term100 A) _17456 (@lem1065625 A _17456 h1)). Qed.
Lemma lem1065660 {A : Type'} (h1 : term98 A) : term98 A.
Proof. exact (h1). Qed.
Lemma lem1065661 {A : Type'} (h1 : term98 A) : term99 A.
Proof. exact (ex_elim (@lem1065660 A h1) (fun _17456 : type1593 A => fun h0 : term97 A _17456 => @lem1065659 A _17456 h0)). Qed.
Lemma lem1065662 {A : Type'} : (term98 A) = (term99 A).
Proof. exact (prop_ext (fun h1 : term98 A => @lem1065661 A h1) (fun h1 : term99 A => @lem1065658 A)). Qed.
Lemma lem1065663 {A : Type'} : term99 A.
Proof. exact (EQ_MP (@lem1065662 A) (@lem1065658 A)). Qed.
Lemma lem1065664 {A : Type'} (_17456 : type1593 A) (h1 : term61 A _17456) : term61 A _17456.
Proof. exact (h1). Qed.
Lemma lem1065665 {A : Type'} (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : FCONS' = (term4 A _17456)) : (term61 A _17456) = (term60 A FCONS').
Proof. exact (SYM (@lem1065583 A FCONS' _17456 h1)). Qed.
Lemma lem1065666 {A : Type'} (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : term61 A _17456) (h2 : FCONS' = (term4 A _17456)) : term60 A FCONS'.
Proof. exact (EQ_MP (@lem1065665 A FCONS' _17456 h2) (@lem1065664 A _17456 h1)). Qed.
Lemma lem1065667 {A : Type'} (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : term61 A _17456) (h2 : FCONS' = (term4 A _17456)) : term101 A.
Proof. exact (ex_intro (term102 A) FCONS' (@lem1065666 A FCONS' _17456 h1 h2)). Qed.
Lemma lem1065668 {A : Type'} (_17456 : type1593 A) : (term4 A _17456) = (term4 A _17456).
Proof. exact (eq_refl (term4 A _17456)). Qed.
Lemma lem1065669 {A : Type'} (FCONS' : type1380 A) (_17456 : type1593 A) (h1 : term61 A _17456) : term103 A FCONS' _17456.
Proof. exact (fun h0 : FCONS' = (term4 A _17456) => @lem1065667 A FCONS' _17456 h1 h0). Qed.
Lemma lem1065670 {A : Type'} (_17456 : type1593 A) (h1 : term61 A _17456) : term104 A _17456.
Proof. exact (@lem1065669 A (term4 A _17456) _17456 h1). Qed.
Lemma lem1065671 {A : Type'} (_17456 : type1593 A) (h1 : term61 A _17456) : term101 A.
Proof. exact (@lem1065670 A _17456 h1 (@lem1065668 A _17456)). Qed.
Lemma lem1065672 {A : Type'} (h1 : term99 A) : term99 A.
Proof. exact (h1). Qed.
Lemma lem1065673 {A : Type'} (h1 : term99 A) : term101 A.
Proof. exact (ex_elim (@lem1065672 A h1) (fun _17456 : type1593 A => fun h0 : term100 A _17456 => @lem1065671 A _17456 h0)). Qed.
Lemma lem1065674 {A : Type'} : (term99 A) = (term101 A).
Proof. exact (prop_ext (fun h1 : term99 A => @lem1065673 A h1) (fun h1 : term101 A => @lem1065663 A)). Qed.
Lemma lem1065675 {A : Type'} : term101 A.
Proof. exact (EQ_MP (@lem1065674 A) (@lem1065663 A)). Qed.
Lemma lem1065676 {A : Type'} : term105 A.
Proof. exact (fun _17460 : type1672 => @lem1065675 A). Qed.
Lemma lem1065677 {A B : Type'} (P : type1413 A B) : term106 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1065678 {A B : Type'} (P : type1413 A B) : (term106 A B P) = ((term107 A B P) = (term108 A B P)).
Proof. exact (eq_refl (term106 A B P)). Qed.
Lemma lem1065681 {A B : Type'} (P : type1413 A B) : (term107 A B P) = (term108 A B P).
Proof. exact (EQ_MP (@lem1065678 A B P) (@lem1065677 A B P)). Qed.
Lemma lem1065682 {A : Type'} (P : type1273 A) : (term109 A P) = (term110 A P).
Proof. exact (@lem1065681 type1672 (type1380 A) P). Qed.
Lemma lem1065683 {A : Type'} : (term111 A) = (term112 A).
Proof. exact (@lem1065682 A (term113 A)). Qed.
Lemma lem1065684 {A : Type'} (_17460 : type1672) : (term114 A _17460) = (term102 A).
Proof. exact (eq_refl (term114 A _17460)). Qed.
Lemma lem1065685 {A : Type'} (FCONS' : type1380 A) : FCONS' = FCONS'.
Proof. exact (eq_refl FCONS'). Qed.
Lemma lem1065686 {A : Type'} (_17460 : type1672) (FCONS' : type1380 A) : (term115 A _17460 FCONS') = (term116 A FCONS').
Proof. exact (MK_COMB (@lem1065684 A _17460) (@lem1065685 A FCONS')). Qed.
Lemma lem1065687 {A : Type'} (FCONS' : type1380 A) : (term116 A FCONS') = (term60 A FCONS').
Proof. exact (eq_refl (term116 A FCONS')). Qed.
Lemma lem1065688 {A : Type'} (_17460 : type1672) (FCONS' : type1380 A) : (term115 A _17460 FCONS') = (term60 A FCONS').
Proof. exact (TRANS (@lem1065686 A _17460 FCONS') (@lem1065687 A FCONS')). Qed.
Lemma lem1065689 {A : Type'} (_17460 : type1672) : (term117 A _17460) = (term102 A).
Proof. exact (fun_ext (fun FCONS' : type1380 A => @lem1065688 A _17460 FCONS')). Qed.
Lemma lem1065690 {A : Type'} : (@ex (A -> (nat -> A) -> nat -> A)) = (@ex (A -> (nat -> A) -> nat -> A)).
Proof. exact (eq_refl (@ex (A -> (nat -> A) -> nat -> A))). Qed.
Lemma lem1065691 {A : Type'} (_17460 : type1672) : (term118 A _17460) = (term101 A).
Proof. exact (MK_COMB (@lem1065690 A) (@lem1065689 A _17460)). Qed.
Lemma lem1065692 {A : Type'} : (term119 A) = (term120 A).
Proof. exact (fun_ext (fun _17460 : type1672 => @lem1065691 A _17460)). Qed.
Lemma lem1065693 : (@all (prod nat (prod nat (prod nat (prod nat nat))))) = (@all (prod nat (prod nat (prod nat (prod nat nat))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat nat)))))). Qed.
Lemma lem1065694 {A : Type'} : (term111 A) = (term105 A).
Proof. exact (MK_COMB (@lem1065693) (@lem1065692 A)). Qed.
Lemma lem1065695 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1065696 {A : Type'} : (term121 A) = (term122 A).
Proof. exact (MK_COMB (@lem1065695) (@lem1065694 A)). Qed.
Lemma lem1065697 {A : Type'} (_17460 : type1672) : (term114 A _17460) = (term102 A).
Proof. exact (eq_refl (term114 A _17460)). Qed.
Lemma lem1065698 {A : Type'} (FCONS' : type1275 A) (_17460 : type1672) : (FCONS' _17460) = (FCONS' _17460).
Proof. exact (eq_refl (FCONS' _17460)). Qed.
Lemma lem1065699 {A : Type'} (FCONS' : type1275 A) (_17460 : type1672) : (term123 A FCONS' _17460) = (term124 A FCONS' _17460).
Proof. exact (MK_COMB (@lem1065697 A _17460) (@lem1065698 A FCONS' _17460)). Qed.
Lemma lem1065700 {A : Type'} (FCONS' : type1275 A) (_17460 : type1672) : (term124 A FCONS' _17460) = (term125 A FCONS' _17460).
Proof. exact (eq_refl (term124 A FCONS' _17460)). Qed.
Lemma lem1065701 {A : Type'} (FCONS' : type1275 A) (_17460 : type1672) : (term123 A FCONS' _17460) = (term125 A FCONS' _17460).
Proof. exact (TRANS (@lem1065699 A FCONS' _17460) (@lem1065700 A FCONS' _17460)). Qed.
Lemma lem1065702 {A : Type'} (FCONS' : type1275 A) : (term126 A FCONS') = (term127 A FCONS').
Proof. exact (fun_ext (fun _17460 : type1672 => @lem1065701 A FCONS' _17460)). Qed.
Lemma lem1065703 : (@all (prod nat (prod nat (prod nat (prod nat nat))))) = (@all (prod nat (prod nat (prod nat (prod nat nat))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat nat)))))). Qed.
Lemma lem1065704 {A : Type'} (FCONS' : type1275 A) : (term128 A FCONS') = (term129 A FCONS').
Proof. exact (MK_COMB (@lem1065703) (@lem1065702 A FCONS')). Qed.
Lemma lem1065705 {A : Type'} : (term130 A) = (term131 A).
Proof. exact (fun_ext (fun FCONS' : type1275 A => @lem1065704 A FCONS')). Qed.
Lemma lem1065706 {A : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (nat -> A) -> nat -> A)) = (@ex ((prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (nat -> A) -> nat -> A)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (nat -> A) -> nat -> A))). Qed.
Lemma lem1065707 {A : Type'} : (term112 A) = (term132 A).
Proof. exact (MK_COMB (@lem1065706 A) (@lem1065705 A)). Qed.
Lemma lem1065708 {A : Type'} : ((term111 A) = (term112 A)) = ((term105 A) = (term132 A)).
Proof. exact (MK_COMB (@lem1065696 A) (@lem1065707 A)). Qed.
Lemma lem1065709 {A : Type'} : (term105 A) = (term132 A).
Proof. exact (EQ_MP (@lem1065708 A) (@lem1065683 A)). Qed.
Lemma lem1065710 {A : Type'} : term132 A.
Proof. exact (EQ_MP (@lem1065709 A) (@lem1065676 A)). Qed.
Lemma lem1065712 {A : Type'} : (@ex A) = (term133 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1065713 {A : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat nat)))) -> A -> (nat -> A) -> nat -> A)) = (term134 A).
Proof. exact (@lem1065712 (type1275 A)). Qed.
Lemma lem1065714 {A : Type'} : (term131 A) = (term131 A).
Proof. exact (eq_refl (term131 A)). Qed.
Lemma lem1065715 {A : Type'} : (term132 A) = (term135 A).
Proof. exact (MK_COMB (@lem1065713 A) (@lem1065714 A)). Qed.
Lemma lem1065716 {A : Type'} : (term135 A) = (term136 A).
Proof. exact (eq_refl (term135 A)). Qed.
Lemma lem1065717 {A : Type'} : (term132 A) = (term136 A).
Proof. exact (TRANS (@lem1065715 A) (@lem1065716 A)). Qed.
Lemma lem1065718 {A : Type'} : term136 A.
Proof. exact (EQ_MP (@lem1065717 A) (@lem1065710 A)). Qed.
