Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7932948_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
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
Require Import thm69_spec.
Require Import thm7932353_spec.
Require Import thm7932366_spec.
Require Import thm7932367_spec.
Require Import thm7932389_spec.
Require Import thm7932390_spec.
Lemma lem7932406 {A : Type'} (h1 : (@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit)))) : (@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit))).
Proof. exact (h1). Qed.
Lemma lem7932407 {A : Type'} (h1 : (@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit)))) : (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit))) = (@UNIV (tybit1 A)).
Proof. exact (SYM (@lem7932406 A h1)). Qed.
Lemma lem7932408 {A : Type'} (h1 : (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit))) = (@UNIV (tybit1 A))) : (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit))) = (@UNIV (tybit1 A)).
Proof. exact (h1). Qed.
Lemma lem7932409 {A : Type'} (h1 : (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit))) = (@UNIV (tybit1 A))) : (@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit))).
Proof. exact (SYM (@lem7932408 A h1)). Qed.
Lemma lem7932410 {A : Type'} : ((@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit)))) = ((@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit))) = (@UNIV (tybit1 A))).
Proof. exact (prop_ext (fun h1 : (@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit))) => @lem7932407 A h1) (fun h1 : (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit))) = (@UNIV (tybit1 A)) => @lem7932409 A h1)). Qed.
Lemma lem7932411 {A : Type'} : ((@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit))) = (@UNIV (tybit1 A))) = ((@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit)))).
Proof. exact (SYM (@lem7932410 A)). Qed.
Lemma lem7932413 {_88266 _88270 : Type'} (f : _88270 -> _88266) (s : _88270 -> Prop) (t : _88266 -> Prop) : term0 _88266 _88270 f s t.
Proof. exact (EQ_MP (@lem7932390 _88266 _88270 f s t) (@lem7932389 _88266 _88270 f s t)). Qed.
Lemma lem7932414 {A : Type'} (f : type40 A) (s : type42 A) (t : type1351 A) : term1 A f s t.
Proof. exact (@lem7932413 (tybit1 A) (type6 A) f s t). Qed.
Lemma lem7932415 {A : Type'} : term2 A.
Proof. exact (@lem7932414 A (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit)) (@UNIV (tybit1 A))). Qed.
Lemma lem7932425 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7932367 A x) (@lem7932366 A x)). Qed.
Lemma lem7932426 {A : Type'} (x : tybit1 A) : (@IN (tybit1 A) x (@UNIV (tybit1 A))) = True.
Proof. exact (@lem7932425 (tybit1 A) x). Qed.
Lemma lem7932427 {A : Type'} (y : tybit1 A) : (@IN (tybit1 A) y (@UNIV (tybit1 A))) = True.
Proof. exact (@lem7932426 A y). Qed.
Lemma lem7932428 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7932429 {A : Type'} (y : tybit1 A) : (term3 A y) = (imp True).
Proof. exact (MK_COMB (@lem7932428) (@lem7932427 A y)). Qed.
Lemma lem7932436 {A : Type'} (y : tybit1 A) : (term4 A y) = (term4 A y).
Proof. exact (eq_refl (term4 A y)). Qed.
Lemma lem7932437 {A : Type'} (y : tybit1 A) : (term5 A y) = (term6 A y).
Proof. exact (MK_COMB (@lem7932429 A y) (@lem7932436 A y)). Qed.
Lemma lem7932439 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7932440 {A : Type'} (y : tybit1 A) : (term6 A y) = (term4 A y).
Proof. exact (@lem7932439 (term4 A y)). Qed.
Lemma lem7932447 {A : Type'} (y : tybit1 A) : (term5 A y) = (term4 A y).
Proof. exact (TRANS (@lem7932437 A y) (@lem7932440 A y)). Qed.
Lemma lem7932448 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (fun_ext (fun y : tybit1 A => @lem7932447 A y)). Qed.
Lemma lem7932449 {A : Type'} : (@all (tybit1 A)) = (@all (tybit1 A)).
Proof. exact (eq_refl (@all (tybit1 A))). Qed.
Lemma lem7932450 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem7932449 A) (@lem7932448 A)). Qed.
Lemma lem7932455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7932456 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem7932455) (@lem7932450 A)). Qed.
Lemma lem7932464 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7932367 A x) (@lem7932366 A x)). Qed.
Lemma lem7932465 {A : Type'} (x : tybit1 A) : (@IN (tybit1 A) x (@UNIV (tybit1 A))) = True.
Proof. exact (@lem7932464 (tybit1 A) x). Qed.
Lemma lem7932466 {A : Type'} (x : type6 A) : (term13 A x) = True.
Proof. exact (@lem7932465 A (@mktybit1 A x)). Qed.
Lemma lem7932467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7932468 {A : Type'} (x : type6 A) : (term14 A x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem7932467) (@lem7932466 A x)). Qed.
Lemma lem7932470 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7932367 A x) (@lem7932366 A x)). Qed.
Lemma lem7932471 {A : Type'} (x : type6 A) : (@IN (finite_sum (finite_sum A A) unit) x (@UNIV (finite_sum (finite_sum A A) unit))) = True.
Proof. exact (@lem7932470 (type6 A) x). Qed.
Lemma lem7932472 {A : Type'} (x : type6 A) : ((term13 A x) = (@IN (finite_sum (finite_sum A A) unit) x (@UNIV (finite_sum (finite_sum A A) unit)))) = (True = True).
Proof. exact (MK_COMB (@lem7932468 A x) (@lem7932471 A x)). Qed.
Lemma lem7932474 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem7932475 : (True = True) = True.
Proof. exact (@lem7932474 True). Qed.
Lemma lem7932476 {A : Type'} (x : type6 A) : ((term13 A x) = (@IN (finite_sum (finite_sum A A) unit) x (@UNIV (finite_sum (finite_sum A A) unit)))) = True.
Proof. exact (TRANS (@lem7932472 A x) (@lem7932475)). Qed.
Lemma lem7932477 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (fun_ext (fun x : type6 A => @lem7932476 A x)). Qed.
Lemma lem7932478 {A : Type'} : (@all (finite_sum (finite_sum A A) unit)) = (@all (finite_sum (finite_sum A A) unit)).
Proof. exact (eq_refl (@all (finite_sum (finite_sum A A) unit))). Qed.
Lemma lem7932479 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (MK_COMB (@lem7932478 A) (@lem7932477 A)). Qed.
Lemma lem7932481 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7932482 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (@lem7932481 (type6 A) t). Qed.
Lemma lem7932483 {A : Type'} : (term18 A) = True.
Proof. exact (@lem7932482 A True). Qed.
Lemma lem7932484 {A : Type'} : (term17 A) = True.
Proof. exact (TRANS (@lem7932479 A) (@lem7932483 A)). Qed.
Lemma lem7932485 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (MK_COMB (@lem7932456 A) (@lem7932484 A)). Qed.
Lemma lem7932487 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem7932488 {A : Type'} : (term22 A) = (term10 A).
Proof. exact (@lem7932487 (term10 A)). Qed.
Lemma lem7932499 {A : Type'} : (term21 A) = (term10 A).
Proof. exact (TRANS (@lem7932485 A) (@lem7932488 A)). Qed.
Lemma lem7932500 {A : Type'} : (term10 A) = (term21 A).
Proof. exact (SYM (@lem7932499 A)). Qed.
Lemma lem7932502 (p : Prop) : p = (term23 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7932503 {A : Type'} : (term10 A) = (term24 A).
Proof. exact (@lem7932502 (term10 A)). Qed.
Lemma lem7932504 {A : Type'} : (term24 A) = (term10 A).
Proof. exact (SYM (@lem7932503 A)). Qed.
Lemma lem7932505 {A : Type'} (h1 : term25 A) : term25 A.
Proof. exact (h1). Qed.
Lemma lem7932506 {A : Type'} : term26 A.
Proof. exact (@lem7932353 A). Qed.
Lemma lem7932510 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (h1). Qed.
Lemma lem7932511 {A : Type'} : term28 A.
Proof. exact (fun h0 : term27 A => @lem7932510 A h0). Qed.
Lemma lem7932512 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (h1). Qed.
Lemma lem7932513 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (h1). Qed.
Lemma lem7932514 {A : Type'} (h1 : term27 A) (h2 : term28 A) : term27 A.
Proof. exact (@lem7932512 A h2 (@lem7932513 A h1)). Qed.
Lemma lem7932515 {A : Type'} (h1 : term27 A) : term29 A.
Proof. exact (fun h0 : term28 A => @lem7932514 A h1 h0). Qed.
Lemma lem7932516 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (h1). Qed.
Lemma lem7932517 {A : Type'} (h1 : term27 A) (h2 : term28 A) : term27 A.
Proof. exact (@lem7932515 A h1 (@lem7932516 A h2)). Qed.
Lemma lem7932518 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (fun h0 : term27 A => @lem7932517 A h0 h1). Qed.
Lemma lem7932519 {A : Type'} : term30 A.
Proof. exact (fun h0 : term28 A => @lem7932518 A h0). Qed.
Lemma lem7932522 {A : Type'} : term28 A.
Proof. exact (@lem7932519 A (@lem7932511 A)). Qed.
Lemma lem7932523 {A : Type'} : term28 A.
Proof. exact (@lem7932522 A). Qed.
Lemma lem7932535 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7932536 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (@lem7932535 (term26 A)). Qed.
Lemma lem7932545 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (eq_refl (term33 A)). Qed.
Lemma lem7932552 {A : Type'} : (term27 A) = (term34 A).
Proof. exact (MK_COMB (@lem7932545 A) (@lem7932536 A)). Qed.
Lemma lem7932553 {A : Type'} (x : tybit1 A) (a : type6 A) : (x = (@mktybit1 A a)) = (x = (@mktybit1 A a)).
Proof. exact (eq_refl (x = (@mktybit1 A a))). Qed.
Lemma lem7932554 {A : Type'} (x : tybit1 A) : (term35 A x) = (term35 A x).
Proof. exact (fun_ext (fun a : type6 A => @lem7932553 A x a)). Qed.
Lemma lem7932555 {A : Type'} : (@ex (finite_sum (finite_sum A A) unit)) = (@ex (finite_sum (finite_sum A A) unit)).
Proof. exact (eq_refl (@ex (finite_sum (finite_sum A A) unit))). Qed.
Lemma lem7932556 {A : Type'} (x : tybit1 A) : (term36 A x) = (term36 A x).
Proof. exact (MK_COMB (@lem7932555 A) (@lem7932554 A x)). Qed.
Lemma lem7932557 {A : Type'} : (term37 A) = (term37 A).
Proof. exact (fun_ext (fun x : tybit1 A => @lem7932556 A x)). Qed.
Lemma lem7932558 {A : Type'} : (@all (tybit1 A)) = (@all (tybit1 A)).
Proof. exact (eq_refl (@all (tybit1 A))). Qed.
Lemma lem7932559 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem7932558 A) (@lem7932557 A)). Qed.
Lemma lem7932560 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7932561 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (MK_COMB (@lem7932560) (@lem7932559 A)). Qed.
Lemma lem7932562 {A : Type'} (x : type6 A) (y : tybit1 A) : ((@mktybit1 A x) = y) = ((@mktybit1 A x) = y).
Proof. exact (eq_refl ((@mktybit1 A x) = y)). Qed.
Lemma lem7932563 {A : Type'} (y : tybit1 A) : (term38 A y) = (term38 A y).
Proof. exact (fun_ext (fun x : type6 A => @lem7932562 A x y)). Qed.
Lemma lem7932564 {A : Type'} : (@ex (finite_sum (finite_sum A A) unit)) = (@ex (finite_sum (finite_sum A A) unit)).
Proof. exact (eq_refl (@ex (finite_sum (finite_sum A A) unit))). Qed.
Lemma lem7932565 {A : Type'} (y : tybit1 A) : (term4 A y) = (term4 A y).
Proof. exact (MK_COMB (@lem7932564 A) (@lem7932563 A y)). Qed.
Lemma lem7932566 {A : Type'} : (term8 A) = (term8 A).
Proof. exact (fun_ext (fun y : tybit1 A => @lem7932565 A y)). Qed.
Lemma lem7932567 {A : Type'} : (@all (tybit1 A)) = (@all (tybit1 A)).
Proof. exact (eq_refl (@all (tybit1 A))). Qed.
Lemma lem7932568 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem7932567 A) (@lem7932566 A)). Qed.
Lemma lem7932569 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7932570 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (MK_COMB (@lem7932569) (@lem7932568 A)). Qed.
Lemma lem7932571 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7932572 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (MK_COMB (@lem7932571) (@lem7932570 A)). Qed.
Lemma lem7932573 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (MK_COMB (@lem7932572 A) (@lem7932561 A)). Qed.
Lemma lem7932602 {A : Type'} : (term27 A) = (term34 A).
Proof. exact (TRANS (@lem7932552 A) (@lem7932573 A)). Qed.
Lemma lem7932603 {A : Type'} : (term34 A) = (term27 A).
Proof. exact (SYM (@lem7932602 A)). Qed.
Lemma lem7932604 {A : Type'} (h1 : term25 A) : term25 A.
Proof. exact (h1). Qed.
Lemma lem7932605 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem7932607 {A : Type'} (P : type42 A) : (term39 A P) = (term40 A P).
Proof. exact (@lem18394 (type6 A) P). Qed.
Lemma lem7932608 {A : Type'} (y : tybit1 A) : (term41 A y) = (term42 A y).
Proof. exact (@lem7932607 A (term38 A y)). Qed.
Lemma lem7932609 {A : Type'} (x : type6 A) (y : tybit1 A) : (term43 A y x) = ((@mktybit1 A x) = y).
Proof. exact (eq_refl (term43 A y x)). Qed.
Lemma lem7932610 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7932612 {A : Type'} (x : type6 A) (y : tybit1 A) : (term44 A y x) = (term45 A x y).
Proof. exact (MK_COMB (@lem7932610) (@lem7932609 A x y)). Qed.
Lemma lem7932613 {A : Type'} (y : tybit1 A) : (term46 A y) = (term47 A y).
Proof. exact (fun_ext (fun x : type6 A => @lem7932612 A x y)). Qed.
Lemma lem7932614 {A : Type'} : (@all (finite_sum (finite_sum A A) unit)) = (@all (finite_sum (finite_sum A A) unit)).
Proof. exact (eq_refl (@all (finite_sum (finite_sum A A) unit))). Qed.
Lemma lem7932615 {A : Type'} (y : tybit1 A) : (term42 A y) = (term48 A y).
Proof. exact (MK_COMB (@lem7932614 A) (@lem7932613 A y)). Qed.
Lemma lem7932616 {A : Type'} (y : tybit1 A) : (term41 A y) = (term48 A y).
Proof. exact (TRANS (@lem7932608 A y) (@lem7932615 A y)). Qed.
Lemma lem7932617 {A : Type'} (P : type1351 A) : (term49 A P) = (term50 A P).
Proof. exact (@lem18392 (tybit1 A) P). Qed.
Lemma lem7932618 {A : Type'} : (term25 A) = (term51 A).
Proof. exact (@lem7932617 A (term8 A)). Qed.
Lemma lem7932619 {A : Type'} (y : tybit1 A) : (term52 A y) = (term4 A y).
Proof. exact (eq_refl (term52 A y)). Qed.
Lemma lem7932620 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7932621 {A : Type'} (y : tybit1 A) : (term53 A y) = (term41 A y).
Proof. exact (MK_COMB (@lem7932620) (@lem7932619 A y)). Qed.
Lemma lem7932622 {A : Type'} (y : tybit1 A) : (term53 A y) = (term48 A y).
Proof. exact (TRANS (@lem7932621 A y) (@lem7932616 A y)). Qed.
Lemma lem7932623 {A : Type'} : (term54 A) = (term55 A).
Proof. exact (fun_ext (fun y : tybit1 A => @lem7932622 A y)). Qed.
Lemma lem7932624 {A : Type'} : (@ex (tybit1 A)) = (@ex (tybit1 A)).
Proof. exact (eq_refl (@ex (tybit1 A))). Qed.
Lemma lem7932625 {A : Type'} : (term51 A) = (term56 A).
Proof. exact (MK_COMB (@lem7932624 A) (@lem7932623 A)). Qed.
Lemma lem7932638 {A : Type'} : (term25 A) = (term56 A).
Proof. exact (TRANS (@lem7932618 A) (@lem7932625 A)). Qed.
Lemma lem7932639 {A : Type'} (h1 : term25 A) : term56 A.
Proof. exact (EQ_MP (@lem7932638 A) (@lem7932604 A h1)). Qed.
Lemma lem7932640 {A : Type'} (x : tybit1 A) (a : type6 A) : (x = (@mktybit1 A a)) = (x = (@mktybit1 A a)).
Proof. exact (eq_refl (x = (@mktybit1 A a))). Qed.
Lemma lem7932641 {A : Type'} (x : tybit1 A) : (term35 A x) = (term35 A x).
Proof. exact (fun_ext (fun a : type6 A => @lem7932640 A x a)). Qed.
Lemma lem7932642 {A : Type'} : (@ex (finite_sum (finite_sum A A) unit)) = (@ex (finite_sum (finite_sum A A) unit)).
Proof. exact (eq_refl (@ex (finite_sum (finite_sum A A) unit))). Qed.
Lemma lem7932643 {A : Type'} (x : tybit1 A) : (term36 A x) = (term36 A x).
Proof. exact (MK_COMB (@lem7932642 A) (@lem7932641 A x)). Qed.
Lemma lem7932644 {A : Type'} : (term37 A) = (term37 A).
Proof. exact (fun_ext (fun x : tybit1 A => @lem7932643 A x)). Qed.
Lemma lem7932645 {A : Type'} : (@all (tybit1 A)) = (@all (tybit1 A)).
Proof. exact (eq_refl (@all (tybit1 A))). Qed.
Lemma lem7932646 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem7932645 A) (@lem7932644 A)). Qed.
Lemma lem7932657 {A B : Type'} (P : type1413 A B) : (term57 A B P) = (term58 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7932658 {A : Type'} (P : type1349 A) : (term59 A P) = (term60 A P).
Proof. exact (@lem7932657 (tybit1 A) (type6 A) P). Qed.
Lemma lem7932659 {A : Type'} : (term61 A) = (term62 A).
Proof. exact (@lem7932658 A (term63 A)). Qed.
Lemma lem7932660 {A : Type'} (x : tybit1 A) : (term64 A x) = (term35 A x).
Proof. exact (eq_refl (term64 A x)). Qed.
Lemma lem7932661 {A : Type'} (a : type6 A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7932662 {A : Type'} (x : tybit1 A) (a : type6 A) : (term65 A x a) = (term66 A x a).
Proof. exact (MK_COMB (@lem7932660 A x) (@lem7932661 A a)). Qed.
Lemma lem7932663 {A : Type'} (x : tybit1 A) (a : type6 A) : (term66 A x a) = (x = (@mktybit1 A a)).
Proof. exact (eq_refl (term66 A x a)). Qed.
Lemma lem7932664 {A : Type'} (x : tybit1 A) (a : type6 A) : (term65 A x a) = (x = (@mktybit1 A a)).
Proof. exact (TRANS (@lem7932662 A x a) (@lem7932663 A x a)). Qed.
Lemma lem7932665 {A : Type'} (x : tybit1 A) : (term67 A x) = (term35 A x).
Proof. exact (fun_ext (fun a : type6 A => @lem7932664 A x a)). Qed.
Lemma lem7932666 {A : Type'} : (@ex (finite_sum (finite_sum A A) unit)) = (@ex (finite_sum (finite_sum A A) unit)).
Proof. exact (eq_refl (@ex (finite_sum (finite_sum A A) unit))). Qed.
Lemma lem7932667 {A : Type'} (x : tybit1 A) : (term68 A x) = (term36 A x).
Proof. exact (MK_COMB (@lem7932666 A) (@lem7932665 A x)). Qed.
Lemma lem7932668 {A : Type'} : (term69 A) = (term37 A).
Proof. exact (fun_ext (fun x : tybit1 A => @lem7932667 A x)). Qed.
Lemma lem7932669 {A : Type'} : (@all (tybit1 A)) = (@all (tybit1 A)).
Proof. exact (eq_refl (@all (tybit1 A))). Qed.
Lemma lem7932670 {A : Type'} : (term61 A) = (term26 A).
Proof. exact (MK_COMB (@lem7932669 A) (@lem7932668 A)). Qed.
Lemma lem7932671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7932672 {A : Type'} : (term70 A) = (term71 A).
Proof. exact (MK_COMB (@lem7932671) (@lem7932670 A)). Qed.
Lemma lem7932673 {A : Type'} (x : tybit1 A) : (term64 A x) = (term35 A x).
Proof. exact (eq_refl (term64 A x)). Qed.
Lemma lem7932674 {A : Type'} (a : type1348 A) (x : tybit1 A) : (a x) = (a x).
Proof. exact (eq_refl (a x)). Qed.
Lemma lem7932675 {A : Type'} (a : type1348 A) (x : tybit1 A) : (term72 A a x) = (term73 A a x).
Proof. exact (MK_COMB (@lem7932673 A x) (@lem7932674 A a x)). Qed.
Lemma lem7932676 {A : Type'} (a : type1348 A) (x : tybit1 A) : (term73 A a x) = (x = (term74 A a x)).
Proof. exact (eq_refl (term73 A a x)). Qed.
Lemma lem7932677 {A : Type'} (a : type1348 A) (x : tybit1 A) : (term72 A a x) = (x = (term74 A a x)).
Proof. exact (TRANS (@lem7932675 A a x) (@lem7932676 A a x)). Qed.
Lemma lem7932678 {A : Type'} (a : type1348 A) : (term75 A a) = (term76 A a).
Proof. exact (fun_ext (fun x : tybit1 A => @lem7932677 A a x)). Qed.
Lemma lem7932679 {A : Type'} : (@all (tybit1 A)) = (@all (tybit1 A)).
Proof. exact (eq_refl (@all (tybit1 A))). Qed.
Lemma lem7932680 {A : Type'} (a : type1348 A) : (term77 A a) = (term78 A a).
Proof. exact (MK_COMB (@lem7932679 A) (@lem7932678 A a)). Qed.
Lemma lem7932681 {A : Type'} : (term79 A) = (term80 A).
Proof. exact (fun_ext (fun a : type1348 A => @lem7932680 A a)). Qed.
Lemma lem7932682 {A : Type'} : (@ex ((tybit1 A) -> finite_sum (finite_sum A A) unit)) = (@ex ((tybit1 A) -> finite_sum (finite_sum A A) unit)).
Proof. exact (eq_refl (@ex ((tybit1 A) -> finite_sum (finite_sum A A) unit))). Qed.
Lemma lem7932683 {A : Type'} : (term62 A) = (term81 A).
Proof. exact (MK_COMB (@lem7932682 A) (@lem7932681 A)). Qed.
Lemma lem7932684 {A : Type'} : ((term61 A) = (term62 A)) = ((term26 A) = (term81 A)).
Proof. exact (MK_COMB (@lem7932672 A) (@lem7932683 A)). Qed.
Lemma lem7932686 {A : Type'} : (term26 A) = (term81 A).
Proof. exact (EQ_MP (@lem7932684 A) (@lem7932659 A)). Qed.
Lemma lem7932687 {A : Type'} : (term26 A) = (term81 A).
Proof. exact (TRANS (@lem7932646 A) (@lem7932686 A)). Qed.
Lemma lem7932688 {A : Type'} (h1 : term26 A) : term81 A.
Proof. exact (EQ_MP (@lem7932687 A) (@lem7932605 A h1)). Qed.
Lemma lem7932689 {A : Type'} (a : type1348 A) (h1 : term78 A a) : term78 A a.
Proof. exact (h1). Qed.
Lemma lem7932690 {A : Type'} (y : tybit1 A) (h1 : term48 A y) : term48 A y.
Proof. exact (h1). Qed.
Lemma lem7932699 {A : Type'} (a : type1348 A) (x : tybit1 A) : (x = (term74 A a x)) = (x = (term74 A a x)).
Proof. exact (eq_refl (x = (term74 A a x))). Qed.
Lemma lem7932700 {A : Type'} (a : type1348 A) : (term76 A a) = (term76 A a).
Proof. exact (fun_ext (fun x : tybit1 A => @lem7932699 A a x)). Qed.
Lemma lem7932701 {A : Type'} : (@all (tybit1 A)) = (@all (tybit1 A)).
Proof. exact (eq_refl (@all (tybit1 A))). Qed.
Lemma lem7932702 {A : Type'} (a : type1348 A) : (term78 A a) = (term78 A a).
Proof. exact (MK_COMB (@lem7932701 A) (@lem7932700 A a)). Qed.
Lemma lem7932703 {A : Type'} (a : type1348 A) (h1 : term78 A a) : term78 A a.
Proof. exact (EQ_MP (@lem7932702 A a) (@lem7932689 A a h1)). Qed.
Lemma lem7932712 {A : Type'} (x : type6 A) (y : tybit1 A) : (term45 A x y) = (term45 A x y).
Proof. exact (eq_refl (term45 A x y)). Qed.
Lemma lem7932713 {A : Type'} (y : tybit1 A) : (term47 A y) = (term47 A y).
Proof. exact (fun_ext (fun x : type6 A => @lem7932712 A x y)). Qed.
Lemma lem7932714 {A : Type'} : (@all (finite_sum (finite_sum A A) unit)) = (@all (finite_sum (finite_sum A A) unit)).
Proof. exact (eq_refl (@all (finite_sum (finite_sum A A) unit))). Qed.
Lemma lem7932715 {A : Type'} (y : tybit1 A) : (term48 A y) = (term48 A y).
Proof. exact (MK_COMB (@lem7932714 A) (@lem7932713 A y)). Qed.
Lemma lem7932716 {A : Type'} (y : tybit1 A) (h1 : term48 A y) : term48 A y.
Proof. exact (EQ_MP (@lem7932715 A y) (@lem7932690 A y h1)). Qed.
Lemma lem7932718 {A : Type'} (a : type1348 A) (x : tybit1 A) : (x = (term74 A a x)) = (x = (term74 A a x)).
Proof. exact (eq_refl (x = (term74 A a x))). Qed.
Lemma lem7932719 {A : Type'} (a : type1348 A) : (term76 A a) = (term76 A a).
Proof. exact (fun_ext (fun x : tybit1 A => @lem7932718 A a x)). Qed.
Lemma lem7932720 {A : Type'} : (@all (tybit1 A)) = (@all (tybit1 A)).
Proof. exact (eq_refl (@all (tybit1 A))). Qed.
Lemma lem7932722 {A : Type'} (a : type1348 A) : (term78 A a) = (term78 A a).
Proof. exact (MK_COMB (@lem7932720 A) (@lem7932719 A a)). Qed.
Lemma lem7932723 {A : Type'} (a : type1348 A) (h1 : term78 A a) : term78 A a.
Proof. exact (EQ_MP (@lem7932722 A a) (@lem7932703 A a h1)). Qed.
Lemma lem7932725 {A : Type'} (x : type6 A) (y : tybit1 A) : (term45 A x y) = (term45 A x y).
Proof. exact (eq_refl (term45 A x y)). Qed.
Lemma lem7932726 {A : Type'} (y : tybit1 A) : (term47 A y) = (term47 A y).
Proof. exact (fun_ext (fun x : type6 A => @lem7932725 A x y)). Qed.
Lemma lem7932727 {A : Type'} : (@all (finite_sum (finite_sum A A) unit)) = (@all (finite_sum (finite_sum A A) unit)).
Proof. exact (eq_refl (@all (finite_sum (finite_sum A A) unit))). Qed.
Lemma lem7932729 {A : Type'} (y : tybit1 A) : (term48 A y) = (term48 A y).
Proof. exact (MK_COMB (@lem7932727 A) (@lem7932726 A y)). Qed.
Lemma lem7932730 {A : Type'} (y : tybit1 A) (h1 : term48 A y) : term48 A y.
Proof. exact (EQ_MP (@lem7932729 A y) (@lem7932716 A y h1)). Qed.
Lemma lem7932731 {A : Type'} (_103831 : tybit1 A) (a : type1348 A) (h1 : term78 A a) : term82 A a _103831.
Proof. exact (@lem7932723 A a h1 _103831). Qed.
Lemma lem7932732 {A : Type'} (a : type1348 A) (_103831 : tybit1 A) : (term82 A a _103831) = (_103831 = (term74 A a _103831)).
Proof. exact (eq_refl (term82 A a _103831)). Qed.
Lemma lem7932734 {A : Type'} (_103832 : type6 A) (y : tybit1 A) (h1 : term48 A y) : term83 A y _103832.
Proof. exact (@lem7932730 A y h1 _103832). Qed.
Lemma lem7932735 {A : Type'} (_103832 : type6 A) (y : tybit1 A) : (term83 A y _103832) = (term45 A _103832 y).
Proof. exact (eq_refl (term83 A y _103832)). Qed.
Lemma lem7932740 {A : Type'} (_103832 : type6 A) (y : tybit1 A) (h1 : term48 A y) : term45 A _103832 y.
Proof. exact (EQ_MP (@lem7932735 A _103832 y) (@lem7932734 A _103832 y h1)). Qed.
Lemma lem7932758 {A : Type'} (x : tybit1 A) (y : tybit1 A) (z : tybit1 A) : term84 A x y z.
Proof. exact (@lem21385 (tybit1 A) x y z). Qed.
Lemma lem7932762 {A : Type'} (_103831 : tybit1 A) (a : type1348 A) (h1 : term78 A a) : _103831 = (term74 A a _103831).
Proof. exact (EQ_MP (@lem7932732 A a _103831) (@lem7932731 A _103831 a h1)). Qed.
Lemma lem7932763 {A : Type'} (_103831 : tybit1 A) (a : type1348 A) (h1 : term78 A a) : _103831 = (term74 A a _103831).
Proof. exact (@lem7932762 A _103831 a h1). Qed.
Lemma lem7932764 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term78 A a) : y = (term74 A a y).
Proof. exact (@lem7932763 A y a h1). Qed.
Lemma lem7932765 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term78 A a) : term85 A a y.
Proof. exact (fun h0 : term86 A a y => @lem7932764 A y a h1). Qed.
Lemma lem7932767 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7932768 {A : Type'} (a : type1348 A) (y : tybit1 A) : (term85 A a y) = (y = (term74 A a y)).
Proof. exact (@lem7932767 (y = (term74 A a y))). Qed.
Lemma lem7932769 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term78 A a) : y = (term74 A a y).
Proof. exact (EQ_MP (@lem7932768 A a y) (@lem7932765 A y a h1)). Qed.
Lemma lem7932771 {A : Type'} (x : tybit1 A) : x = x.
Proof. exact (@lem21386 (tybit1 A) x). Qed.
Lemma lem7932772 {A : Type'} (x : tybit1 A) : x = x.
Proof. exact (@lem7932771 A x). Qed.
Lemma lem7932773 {A : Type'} (y : tybit1 A) : y = y.
Proof. exact (@lem7932772 A y). Qed.
Lemma lem7932774 {A : Type'} (y : tybit1 A) : term88 A y.
Proof. exact (fun h0 : term89 A y => @lem7932773 A y). Qed.
Lemma lem7932776 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7932777 {A : Type'} (y : tybit1 A) : (term88 A y) = (y = y).
Proof. exact (@lem7932776 (y = y)). Qed.
Lemma lem7932778 {A : Type'} (y : tybit1 A) : y = y.
Proof. exact (EQ_MP (@lem7932777 A y) (@lem7932774 A y)). Qed.
Lemma lem7932796 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7932797 {A : Type'} (y : tybit1 A) (x : tybit1 A) (z : tybit1 A) : (term90 A x y z) = (term91 A y x z).
Proof. exact (@lem7932796 (y = z) (term92 A x z)). Qed.
Lemma lem7932807 {A : Type'} (x : tybit1 A) (y : tybit1 A) : (term93 A x y) = (term93 A x y).
Proof. exact (eq_refl (term93 A x y)). Qed.
Lemma lem7932808 {A : Type'} (y : tybit1 A) (x : tybit1 A) (z : tybit1 A) : (term84 A x y z) = (term94 A y x z).
Proof. exact (MK_COMB (@lem7932807 A x y) (@lem7932797 A y x z)). Qed.
Lemma lem7932812 (q : Prop) (p : Prop) (r : Prop) : (term95 p q r) = (term95 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7932813 {A : Type'} (y : tybit1 A) (x : tybit1 A) (z : tybit1 A) : (term94 A y x z) = (term96 A y x z).
Proof. exact (@lem7932812 (y = z) (term92 A x y) (term92 A x z)). Qed.
Lemma lem7932835 {A : Type'} (y : tybit1 A) (x : tybit1 A) (z : tybit1 A) : (term84 A x y z) = (term96 A y x z).
Proof. exact (TRANS (@lem7932808 A y x z) (@lem7932813 A y x z)). Qed.
Lemma lem7932836 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7932837 {A : Type'} (y : tybit1 A) (x : tybit1 A) (z : tybit1 A) : (term97 A x y z) = (term98 A y x z).
Proof. exact (MK_COMB (@lem7932836) (@lem7932835 A y x z)). Qed.
Lemma lem7932859 {A : Type'} (y : tybit1 A) (x : tybit1 A) (z : tybit1 A) : (term96 A y x z) = (term96 A y x z).
Proof. exact (eq_refl (term96 A y x z)). Qed.
Lemma lem7932860 {A : Type'} (y : tybit1 A) (x : tybit1 A) (z : tybit1 A) : ((term84 A x y z) = (term96 A y x z)) = ((term96 A y x z) = (term96 A y x z)).
Proof. exact (MK_COMB (@lem7932837 A y x z) (@lem7932859 A y x z)). Qed.
Lemma lem7932862 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7932863 (x : Prop) : (x = x) = True.
Proof. exact (@lem7932862 Prop x). Qed.
Lemma lem7932864 {A : Type'} (y : tybit1 A) (x : tybit1 A) (z : tybit1 A) : ((term96 A y x z) = (term96 A y x z)) = True.
Proof. exact (@lem7932863 (term96 A y x z)). Qed.
Lemma lem7932865 {A : Type'} (y : tybit1 A) (x : tybit1 A) (z : tybit1 A) : ((term84 A x y z) = (term96 A y x z)) = True.
Proof. exact (TRANS (@lem7932860 A y x z) (@lem7932864 A y x z)). Qed.
Lemma lem7932866 {A : Type'} (y : tybit1 A) (x : tybit1 A) (z : tybit1 A) : True = ((term84 A x y z) = (term96 A y x z)).
Proof. exact (SYM (@lem7932865 A y x z)). Qed.
Lemma lem7932867 {A : Type'} (y : tybit1 A) (x : tybit1 A) (z : tybit1 A) : (term84 A x y z) = (term96 A y x z).
Proof. exact (EQ_MP (@lem7932866 A y x z) (@lem0)). Qed.
Lemma lem7932868 {A : Type'} (y : tybit1 A) (x : tybit1 A) (z : tybit1 A) : term96 A y x z.
Proof. exact (EQ_MP (@lem7932867 A y x z) (@lem7932758 A x y z)). Qed.
Lemma lem7932870 (b : Prop) (a : Prop) : (a \/ b) = (term99 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7932871 {A : Type'} (x : tybit1 A) (y : tybit1 A) (z : tybit1 A) : (term96 A y x z) = (term100 A x y z).
Proof. exact (@lem7932870 (term101 A y x z) (y = z)). Qed.
Lemma lem7932873 (a : Prop) (b : Prop) : (term102 a b) = (term103 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7932874 {A : Type'} (y : tybit1 A) (x : tybit1 A) (z : tybit1 A) : (term104 A y x z) = (term105 A y x z).
Proof. exact (@lem7932873 (term92 A x y) (term92 A x z)). Qed.
Lemma lem7932876 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7932877 {A : Type'} (x : tybit1 A) (y : tybit1 A) : (term107 A x y) = (x = y).
Proof. exact (@lem7932876 (x = y)). Qed.
Lemma lem7932878 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7932879 {A : Type'} (x : tybit1 A) (y : tybit1 A) : (term108 A x y) = (term109 A x y).
Proof. exact (MK_COMB (@lem7932878) (@lem7932877 A x y)). Qed.
Lemma lem7932881 (a : Prop) : (term106 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7932882 {A : Type'} (x : tybit1 A) (z : tybit1 A) : (term107 A x z) = (x = z).
Proof. exact (@lem7932881 (x = z)). Qed.
Lemma lem7932883 {A : Type'} (y : tybit1 A) (x : tybit1 A) (z : tybit1 A) : (term105 A y x z) = (term110 A y x z).
Proof. exact (MK_COMB (@lem7932879 A x y) (@lem7932882 A x z)). Qed.
Lemma lem7932884 {A : Type'} (y : tybit1 A) (x : tybit1 A) (z : tybit1 A) : (term104 A y x z) = (term110 A y x z).
Proof. exact (TRANS (@lem7932874 A y x z) (@lem7932883 A y x z)). Qed.
Lemma lem7932885 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7932886 {A : Type'} (y : tybit1 A) (x : tybit1 A) (z : tybit1 A) : (term111 A y x z) = (term112 A y x z).
Proof. exact (MK_COMB (@lem7932885) (@lem7932884 A y x z)). Qed.
Lemma lem7932887 {A : Type'} (y : tybit1 A) (z : tybit1 A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7932888 {A : Type'} (x : tybit1 A) (y : tybit1 A) (z : tybit1 A) : (term100 A x y z) = (term113 A x y z).
Proof. exact (MK_COMB (@lem7932886 A y x z) (@lem7932887 A y z)). Qed.
Lemma lem7932889 {A : Type'} (x : tybit1 A) (y : tybit1 A) (z : tybit1 A) : (term96 A y x z) = (term113 A x y z).
Proof. exact (TRANS (@lem7932871 A x y z) (@lem7932888 A x y z)). Qed.
Lemma lem7932891 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term78 A a) : term114 A a y.
Proof. exact (conj (@lem7932769 A y a h1) (@lem7932778 A y)). Qed.
Lemma lem7932893 {A : Type'} (x : tybit1 A) (y : tybit1 A) (z : tybit1 A) : term113 A x y z.
Proof. exact (EQ_MP (@lem7932889 A x y z) (@lem7932868 A y x z)). Qed.
Lemma lem7932894 {A : Type'} (x : tybit1 A) (y : tybit1 A) (z : tybit1 A) : term113 A x y z.
Proof. exact (@lem7932893 A x y z). Qed.
Lemma lem7932895 {A : Type'} (a : type1348 A) (y : tybit1 A) : term115 A a y.
Proof. exact (@lem7932894 A y (term74 A a y) y). Qed.
Lemma lem7932898 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term78 A a) : (term74 A a y) = y.
Proof. exact (@lem7932895 A a y (@lem7932891 A y a h1)). Qed.
Lemma lem7932899 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term78 A a) : (term74 A a y) = y.
Proof. exact (@lem7932898 A y a h1). Qed.
Lemma lem7932900 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term78 A a) : term116 A a y.
Proof. exact (fun h0 : term117 A a y => @lem7932899 A y a h1). Qed.
Lemma lem7932902 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7932903 {A : Type'} (a : type1348 A) (y : tybit1 A) : (term116 A a y) = ((term74 A a y) = y).
Proof. exact (@lem7932902 ((term74 A a y) = y)). Qed.
Lemma lem7932904 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term78 A a) : (term74 A a y) = y.
Proof. exact (EQ_MP (@lem7932903 A a y) (@lem7932900 A y a h1)). Qed.
Lemma lem7932907 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7932909 {A : Type'} (_103832 : type6 A) (y : tybit1 A) : (term45 A _103832 y) = (term118 A _103832 y).
Proof. exact (@lem7932907 ((@mktybit1 A _103832) = y)). Qed.
Lemma lem7932912 {A : Type'} (_103832 : type6 A) (y : tybit1 A) (h1 : term48 A y) : term118 A _103832 y.
Proof. exact (EQ_MP (@lem7932909 A _103832 y) (@lem7932740 A _103832 y h1)). Qed.
Lemma lem7932913 {A : Type'} (_103832 : type6 A) (y : tybit1 A) (h1 : term48 A y) : term118 A _103832 y.
Proof. exact (@lem7932912 A _103832 y h1). Qed.
Lemma lem7932914 {A : Type'} (a : type1348 A) (y : tybit1 A) (h1 : term48 A y) : term119 A a y.
Proof. exact (@lem7932913 A (a y) y h1). Qed.
Lemma lem7932917 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term48 A y) (h2 : term78 A a) : False.
Proof. exact (@lem7932914 A a y h1 (@lem7932904 A y a h2)). Qed.
Lemma lem7932918 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term48 A y) (h2 : term78 A a) : term120.
Proof. exact (fun h0 : ~ False => @lem7932917 A y a h1 h2). Qed.
Lemma lem7932920 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7932921 : term120 = False.
Proof. exact (@lem7932920 False). Qed.
Lemma lem7932922 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term48 A y) (h2 : term78 A a) : False.
Proof. exact (EQ_MP (@lem7932921) (@lem7932918 A y a h1 h2)). Qed.
Lemma lem7932923 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term48 A y) (h2 : term78 A a) : (term48 A y) = False.
Proof. exact (prop_ext (fun h3 : term48 A y => @lem7932922 A y a h1 h2) (fun h3 : False => @lem7932730 A y h1)). Qed.
Lemma lem7932924 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term48 A y) (h2 : term78 A a) : False.
Proof. exact (EQ_MP (@lem7932923 A y a h1 h2) (@lem7932730 A y h1)). Qed.
Lemma lem7932925 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term48 A y) (h2 : term78 A a) : (term78 A a) = False.
Proof. exact (prop_ext (fun h3 : term78 A a => @lem7932924 A y a h1 h2) (fun h3 : False => @lem7932723 A a h2)). Qed.
Lemma lem7932926 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term48 A y) (h2 : term78 A a) : False.
Proof. exact (EQ_MP (@lem7932925 A y a h1 h2) (@lem7932723 A a h2)). Qed.
Lemma lem7932927 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term48 A y) (h2 : term78 A a) : (term48 A y) = False.
Proof. exact (prop_ext (fun h3 : term48 A y => @lem7932926 A y a h1 h2) (fun h3 : False => @lem7932716 A y h1)). Qed.
Lemma lem7932928 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term48 A y) (h2 : term78 A a) : False.
Proof. exact (EQ_MP (@lem7932927 A y a h1 h2) (@lem7932716 A y h1)). Qed.
Lemma lem7932929 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term48 A y) (h2 : term78 A a) : (term78 A a) = False.
Proof. exact (prop_ext (fun h3 : term78 A a => @lem7932928 A y a h1 h2) (fun h3 : False => @lem7932703 A a h2)). Qed.
Lemma lem7932930 {A : Type'} (y : tybit1 A) (a : type1348 A) (h1 : term48 A y) (h2 : term78 A a) : False.
Proof. exact (EQ_MP (@lem7932929 A y a h1 h2) (@lem7932703 A a h2)). Qed.
Lemma lem7932931 {A : Type'} (a : type1348 A) (h1 : term78 A a) (h2 : term25 A) : False.
Proof. exact (ex_elim (@lem7932639 A h2) (fun y : tybit1 A => fun h0 : term55 A y => @lem7932930 A y a h0 h1)). Qed.
Lemma lem7932932 {A : Type'} (h1 : term26 A) (h2 : term25 A) : False.
Proof. exact (ex_elim (@lem7932688 A h1) (fun a : type1348 A => fun h0 : term80 A a => @lem7932931 A a h0 h2)). Qed.
Lemma lem7932933 {A : Type'} (h1 : term25 A) : term31 A.
Proof. exact (fun h0 : term26 A => @lem7932932 A h0 h1). Qed.
Lemma lem7932934 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (@lem69 (term26 A)). Qed.
Lemma lem7932935 {A : Type'} (h1 : term25 A) : term32 A.
Proof. exact (EQ_MP (@lem7932934 A) (@lem7932933 A h1)). Qed.
Lemma lem7932936 {A : Type'} : term34 A.
Proof. exact (fun h0 : term25 A => @lem7932935 A h0). Qed.
Lemma lem7932937 {A : Type'} : term27 A.
Proof. exact (EQ_MP (@lem7932603 A) (@lem7932936 A)). Qed.
Lemma lem7932939 {A : Type'} : term27 A.
Proof. exact (@lem7932523 A (@lem7932937 A)). Qed.
Lemma lem7932940 {A : Type'} (h1 : term25 A) : term31 A.
Proof. exact (@lem7932939 A (@lem7932505 A h1)). Qed.
Lemma lem7932941 {A : Type'} (h1 : term25 A) : False.
Proof. exact (@lem7932940 A h1 (@lem7932506 A)). Qed.
Lemma lem7932942 {A : Type'} (h1 : term25 A) : (term25 A) = False.
Proof. exact (prop_ext (fun h2 : term25 A => @lem7932941 A h1) (fun h2 : False => @lem7932505 A h1)). Qed.
Lemma lem7932943 {A : Type'} (h1 : term25 A) : False.
Proof. exact (EQ_MP (@lem7932942 A h1) (@lem7932505 A h1)). Qed.
Lemma lem7932944 {A : Type'} : term24 A.
Proof. exact (fun h0 : term25 A => @lem7932943 A h0). Qed.
Lemma lem7932945 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem7932504 A) (@lem7932944 A)). Qed.
Lemma lem7932946 {A : Type'} : term21 A.
Proof. exact (EQ_MP (@lem7932500 A) (@lem7932945 A)). Qed.
Lemma lem7932947 {A : Type'} : (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit))) = (@UNIV (tybit1 A)).
Proof. exact (@lem7932415 A (@lem7932946 A)). Qed.
Lemma lem7932948 {A : Type'} : (@UNIV (tybit1 A)) = (@IMAGE (finite_sum (finite_sum A A) unit) (tybit1 A) (@mktybit1 A) (@UNIV (finite_sum (finite_sum A A) unit))).
Proof. exact (EQ_MP (@lem7932411 A) (@lem7932947 A)). Qed.
