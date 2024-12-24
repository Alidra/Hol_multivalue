Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BIJECTIVE_LEFT_RIGHT_INVERSE_term_abbrevs.
Require Import BIJECTIVE_ON_LEFT_RIGHT_INVERSE_spec.
Require Import IN_UNIV_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem3576368 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem3576369 {A : Type'} (x : A) : (term0 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem3576370 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem3576369 A x) (@lem3576368 A x)). Qed.
Lemma lem3576371 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem3576373 {A B : Type'} : term1 A B.
Proof. exact (@lem3570865 B A). Qed.
Lemma lem3576374 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (@lem3576373 A B f). Qed.
Lemma lem3576375 {A B : Type'} (f : A -> B) : (term2 A B f) = (term3 A B f).
Proof. exact (eq_refl (term2 A B f)). Qed.
Lemma lem3576376 {A B : Type'} (f : A -> B) : term3 A B f.
Proof. exact (EQ_MP (@lem3576375 A B f) (@lem3576374 A B f)). Qed.
Lemma lem3576377 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (@lem3576376 A B f (@UNIV A)). Qed.
Lemma lem3576378 {A B : Type'} (f : A -> B) : (term4 A B f) = (term5 A B f).
Proof. exact (eq_refl (term4 A B f)). Qed.
Lemma lem3576379 {A B : Type'} (f : A -> B) : term5 A B f.
Proof. exact (EQ_MP (@lem3576378 A B f) (@lem3576377 A B f)). Qed.
Lemma lem3576380 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (@lem3576379 A B f (@UNIV B)). Qed.
Lemma lem3576381 {A B : Type'} (f : A -> B) : (term6 A B f) = (term7 A B f).
Proof. exact (eq_refl (term6 A B f)). Qed.
Lemma lem3576382 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (EQ_MP (@lem3576381 A B f) (@lem3576380 A B f)). Qed.
Lemma lem3576394 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3576371 A x) (@lem3576370 A x)). Qed.
Lemma lem3576395 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3576394 A x). Qed.
Lemma lem3576396 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3576397 {A : Type'} (x : A) : (term8 A x) = (imp True).
Proof. exact (MK_COMB (@lem3576396) (@lem3576395 A x)). Qed.
Lemma lem3576399 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3576371 A x) (@lem3576370 A x)). Qed.
Lemma lem3576400 {B : Type'} (x : B) : (@IN B x (@UNIV B)) = True.
Proof. exact (@lem3576399 B x). Qed.
Lemma lem3576401 {A B : Type'} (f : A -> B) (x : A) : (term9 A B f x) = True.
Proof. exact (@lem3576400 B (f x)). Qed.
Lemma lem3576402 {A B : Type'} (f : A -> B) (x : A) : (term10 A B f x) = (True -> True).
Proof. exact (MK_COMB (@lem3576397 A x) (@lem3576401 A B f x)). Qed.
Lemma lem3576404 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3576405 : (True -> True) = True.
Proof. exact (@lem3576404 True). Qed.
Lemma lem3576406 {A B : Type'} (f : A -> B) (x : A) : (term10 A B f x) = True.
Proof. exact (TRANS (@lem3576402 A B f x) (@lem3576405)). Qed.
Lemma lem3576407 {A B : Type'} (f : A -> B) : (term11 A B f) = (term12 A).
Proof. exact (fun_ext (fun x : A => @lem3576406 A B f x)). Qed.
Lemma lem3576408 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3576409 {A B : Type'} (f : A -> B) : (term13 A B f) = (term14 A).
Proof. exact (MK_COMB (@lem3576408 A) (@lem3576407 A B f)). Qed.
Lemma lem3576411 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3576412 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (@lem3576411 A t). Qed.
Lemma lem3576413 {A : Type'} : (term14 A) = True.
Proof. exact (@lem3576412 A True). Qed.
Lemma lem3576414 {A B : Type'} (f : A -> B) : (term13 A B f) = True.
Proof. exact (TRANS (@lem3576409 A B f) (@lem3576413 A)). Qed.
Lemma lem3576415 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3576416 {A B : Type'} (f : A -> B) : (term16 A B f) = (imp True).
Proof. exact (MK_COMB (@lem3576415) (@lem3576414 A B f)). Qed.
Lemma lem3576434 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3576371 A x) (@lem3576370 A x)). Qed.
Lemma lem3576435 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3576434 A x). Qed.
Lemma lem3576436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3576437 {A : Type'} (x : A) : (term17 A x) = (and True).
Proof. exact (MK_COMB (@lem3576436) (@lem3576435 A x)). Qed.
Lemma lem3576441 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3576371 A x) (@lem3576370 A x)). Qed.
Lemma lem3576442 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3576441 A x). Qed.
Lemma lem3576443 {A : Type'} (y : A) : (@IN A y (@UNIV A)) = True.
Proof. exact (@lem3576442 A y). Qed.
Lemma lem3576444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3576445 {A : Type'} (y : A) : (term17 A y) = (and True).
Proof. exact (MK_COMB (@lem3576444) (@lem3576443 A y)). Qed.
Lemma lem3576448 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3576449 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term18 A B x f y) = (term19 A B x f y).
Proof. exact (MK_COMB (@lem3576445 A y) (@lem3576448 A B x f y)). Qed.
Lemma lem3576451 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3576452 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term19 A B x f y) = ((f x) = (f y)).
Proof. exact (@lem3576451 ((f x) = (f y))). Qed.
Lemma lem3576455 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term18 A B x f y) = ((f x) = (f y)).
Proof. exact (TRANS (@lem3576449 A B x f y) (@lem3576452 A B x f y)). Qed.
Lemma lem3576456 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term20 A B x f y) = (term19 A B x f y).
Proof. exact (MK_COMB (@lem3576437 A x) (@lem3576455 A B x f y)). Qed.
Lemma lem3576458 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3576459 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term19 A B x f y) = ((f x) = (f y)).
Proof. exact (@lem3576458 ((f x) = (f y))). Qed.
Lemma lem3576462 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term20 A B x f y) = ((f x) = (f y)).
Proof. exact (TRANS (@lem3576456 A B x f y) (@lem3576459 A B x f y)). Qed.
Lemma lem3576463 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3576464 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term21 A B x f y) = (term22 A B x f y).
Proof. exact (MK_COMB (@lem3576463) (@lem3576462 A B x f y)). Qed.
Lemma lem3576467 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3576468 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term23 A B f x y) = (term24 A B f x y).
Proof. exact (MK_COMB (@lem3576464 A B x f y) (@lem3576467 A x y)). Qed.
Lemma lem3576473 {A B : Type'} (f : A -> B) (x : A) : (term25 A B f x) = (term26 A B f x).
Proof. exact (fun_ext (fun y : A => @lem3576468 A B f x y)). Qed.
Lemma lem3576474 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3576475 {A B : Type'} (f : A -> B) (x : A) : (term27 A B f x) = (term28 A B f x).
Proof. exact (MK_COMB (@lem3576474 A) (@lem3576473 A B f x)). Qed.
Lemma lem3576480 {A B : Type'} (f : A -> B) : (term29 A B f) = (term30 A B f).
Proof. exact (fun_ext (fun x : A => @lem3576475 A B f x)). Qed.
Lemma lem3576481 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3576482 {A B : Type'} (f : A -> B) : (term31 A B f) = (term32 A B f).
Proof. exact (MK_COMB (@lem3576481 A) (@lem3576480 A B f)). Qed.
Lemma lem3576487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3576488 {A B : Type'} (f : A -> B) : (term33 A B f) = (term34 A B f).
Proof. exact (MK_COMB (@lem3576487) (@lem3576482 A B f)). Qed.
Lemma lem3576496 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3576371 A x) (@lem3576370 A x)). Qed.
Lemma lem3576497 {B : Type'} (x : B) : (@IN B x (@UNIV B)) = True.
Proof. exact (@lem3576496 B x). Qed.
Lemma lem3576498 {B : Type'} (y : B) : (@IN B y (@UNIV B)) = True.
Proof. exact (@lem3576497 B y). Qed.
Lemma lem3576499 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3576500 {B : Type'} (y : B) : (term8 B y) = (imp True).
Proof. exact (MK_COMB (@lem3576499) (@lem3576498 B y)). Qed.
Lemma lem3576508 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3576371 A x) (@lem3576370 A x)). Qed.
Lemma lem3576509 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3576508 A x). Qed.
Lemma lem3576510 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3576511 {A : Type'} (x : A) : (term17 A x) = (and True).
Proof. exact (MK_COMB (@lem3576510) (@lem3576509 A x)). Qed.
Lemma lem3576514 {A B : Type'} (f : A -> B) (x : A) (y : B) : ((f x) = y) = ((f x) = y).
Proof. exact (eq_refl ((f x) = y)). Qed.
Lemma lem3576515 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term35 A B f x y) = (term36 A B f x y).
Proof. exact (MK_COMB (@lem3576511 A x) (@lem3576514 A B f x y)). Qed.
Lemma lem3576517 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3576518 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term36 A B f x y) = ((f x) = y).
Proof. exact (@lem3576517 ((f x) = y)). Qed.
Lemma lem3576521 {A B : Type'} (f : A -> B) (x : A) (y : B) : (term35 A B f x y) = ((f x) = y).
Proof. exact (TRANS (@lem3576515 A B f x y) (@lem3576518 A B f x y)). Qed.
Lemma lem3576522 {A B : Type'} (f : A -> B) (y : B) : (term37 A B f y) = (term38 A B f y).
Proof. exact (fun_ext (fun x : A => @lem3576521 A B f x y)). Qed.
Lemma lem3576523 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3576524 {A B : Type'} (f : A -> B) (y : B) : (term39 A B f y) = (term40 A B f y).
Proof. exact (MK_COMB (@lem3576523 A) (@lem3576522 A B f y)). Qed.
Lemma lem3576529 {A B : Type'} (f : A -> B) (y : B) : (term41 A B f y) = (term42 A B f y).
Proof. exact (MK_COMB (@lem3576500 B y) (@lem3576524 A B f y)). Qed.
Lemma lem3576531 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3576532 {A B : Type'} (f : A -> B) (y : B) : (term42 A B f y) = (term40 A B f y).
Proof. exact (@lem3576531 (term40 A B f y)). Qed.
Lemma lem3576539 {A B : Type'} (f : A -> B) (y : B) : (term41 A B f y) = (term40 A B f y).
Proof. exact (TRANS (@lem3576529 A B f y) (@lem3576532 A B f y)). Qed.
Lemma lem3576540 {A B : Type'} (f : A -> B) : (term43 A B f) = (term44 A B f).
Proof. exact (fun_ext (fun y : B => @lem3576539 A B f y)). Qed.
Lemma lem3576541 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3576542 {A B : Type'} (f : A -> B) : (term45 A B f) = (term46 A B f).
Proof. exact (MK_COMB (@lem3576541 B) (@lem3576540 A B f)). Qed.
Lemma lem3576547 {A B : Type'} (f : A -> B) : (term47 A B f) = (term48 A B f).
Proof. exact (MK_COMB (@lem3576488 A B f) (@lem3576542 A B f)). Qed.
Lemma lem3576550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3576551 {A B : Type'} (f : A -> B) : (term49 A B f) = (term50 A B f).
Proof. exact (MK_COMB (@lem3576550) (@lem3576547 A B f)). Qed.
Lemma lem3576565 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3576371 A x) (@lem3576370 A x)). Qed.
Lemma lem3576566 {B : Type'} (x : B) : (@IN B x (@UNIV B)) = True.
Proof. exact (@lem3576565 B x). Qed.
Lemma lem3576567 {B : Type'} (y : B) : (@IN B y (@UNIV B)) = True.
Proof. exact (@lem3576566 B y). Qed.
Lemma lem3576568 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3576569 {B : Type'} (y : B) : (term8 B y) = (imp True).
Proof. exact (MK_COMB (@lem3576568) (@lem3576567 B y)). Qed.
Lemma lem3576571 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3576371 A x) (@lem3576370 A x)). Qed.
Lemma lem3576572 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3576571 A x). Qed.
Lemma lem3576573 {A B : Type'} (g : B -> A) (y : B) : (term51 A B g y) = True.
Proof. exact (@lem3576572 A (g y)). Qed.
Lemma lem3576574 {A B : Type'} (g : B -> A) (y : B) : (term52 A B g y) = (True -> True).
Proof. exact (MK_COMB (@lem3576569 B y) (@lem3576573 A B g y)). Qed.
Lemma lem3576576 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3576577 : (True -> True) = True.
Proof. exact (@lem3576576 True). Qed.
Lemma lem3576578 {A B : Type'} (g : B -> A) (y : B) : (term52 A B g y) = True.
Proof. exact (TRANS (@lem3576574 A B g y) (@lem3576577)). Qed.
Lemma lem3576579 {A B : Type'} (g : B -> A) : (term53 A B g) = (term12 B).
Proof. exact (fun_ext (fun y : B => @lem3576578 A B g y)). Qed.
Lemma lem3576580 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3576581 {A B : Type'} (g : B -> A) : (term54 A B g) = (term14 B).
Proof. exact (MK_COMB (@lem3576580 B) (@lem3576579 A B g)). Qed.
Lemma lem3576583 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3576584 {B : Type'} (t : Prop) : (term15 B t) = t.
Proof. exact (@lem3576583 B t). Qed.
Lemma lem3576585 {B : Type'} : (term14 B) = True.
Proof. exact (@lem3576584 B True). Qed.
Lemma lem3576586 {A B : Type'} (g : B -> A) : (term54 A B g) = True.
Proof. exact (TRANS (@lem3576581 A B g) (@lem3576585 B)). Qed.
Lemma lem3576587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3576588 {A B : Type'} (g : B -> A) : (term55 A B g) = (and True).
Proof. exact (MK_COMB (@lem3576587) (@lem3576586 A B g)). Qed.
Lemma lem3576598 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3576371 A x) (@lem3576370 A x)). Qed.
Lemma lem3576599 {B : Type'} (x : B) : (@IN B x (@UNIV B)) = True.
Proof. exact (@lem3576598 B x). Qed.
Lemma lem3576600 {B : Type'} (y : B) : (@IN B y (@UNIV B)) = True.
Proof. exact (@lem3576599 B y). Qed.
Lemma lem3576601 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3576602 {B : Type'} (y : B) : (term8 B y) = (imp True).
Proof. exact (MK_COMB (@lem3576601) (@lem3576600 B y)). Qed.
Lemma lem3576605 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) : ((term56 A B f g y) = y) = ((term56 A B f g y) = y).
Proof. exact (eq_refl ((term56 A B f g y) = y)). Qed.
Lemma lem3576606 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) : (term57 A B f g y) = (term58 A B f g y).
Proof. exact (MK_COMB (@lem3576602 B y) (@lem3576605 A B f g y)). Qed.
Lemma lem3576608 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3576609 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) : (term58 A B f g y) = ((term56 A B f g y) = y).
Proof. exact (@lem3576608 ((term56 A B f g y) = y)). Qed.
Lemma lem3576612 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) : (term57 A B f g y) = ((term56 A B f g y) = y).
Proof. exact (TRANS (@lem3576606 A B f g y) (@lem3576609 A B f g y)). Qed.
Lemma lem3576613 {A B : Type'} (f : A -> B) (g : B -> A) : (term59 A B f g) = (term60 A B f g).
Proof. exact (fun_ext (fun y : B => @lem3576612 A B f g y)). Qed.
Lemma lem3576614 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem3576615 {A B : Type'} (f : A -> B) (g : B -> A) : (term61 A B f g) = (term62 A B f g).
Proof. exact (MK_COMB (@lem3576614 B) (@lem3576613 A B f g)). Qed.
Lemma lem3576620 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3576621 {A B : Type'} (f : A -> B) (g : B -> A) : (term63 A B f g) = (term64 A B f g).
Proof. exact (MK_COMB (@lem3576620) (@lem3576615 A B f g)). Qed.
Lemma lem3576629 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3576371 A x) (@lem3576370 A x)). Qed.
Lemma lem3576630 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3576629 A x). Qed.
Lemma lem3576631 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3576632 {A : Type'} (x : A) : (term8 A x) = (imp True).
Proof. exact (MK_COMB (@lem3576631) (@lem3576630 A x)). Qed.
Lemma lem3576635 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : ((term65 A B g f x) = x) = ((term65 A B g f x) = x).
Proof. exact (eq_refl ((term65 A B g f x) = x)). Qed.
Lemma lem3576636 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term66 A B g f x) = (term67 A B g f x).
Proof. exact (MK_COMB (@lem3576632 A x) (@lem3576635 A B g f x)). Qed.
Lemma lem3576638 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3576639 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term67 A B g f x) = ((term65 A B g f x) = x).
Proof. exact (@lem3576638 ((term65 A B g f x) = x)). Qed.
Lemma lem3576642 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term66 A B g f x) = ((term65 A B g f x) = x).
Proof. exact (TRANS (@lem3576636 A B g f x) (@lem3576639 A B g f x)). Qed.
Lemma lem3576643 {A B : Type'} (g : B -> A) (f : A -> B) : (term68 A B g f) = (term69 A B g f).
Proof. exact (fun_ext (fun x : A => @lem3576642 A B g f x)). Qed.
Lemma lem3576644 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3576645 {A B : Type'} (g : B -> A) (f : A -> B) : (term70 A B g f) = (term71 A B g f).
Proof. exact (MK_COMB (@lem3576644 A) (@lem3576643 A B g f)). Qed.
Lemma lem3576650 {A B : Type'} (g : B -> A) (f : A -> B) : (term72 A B g f) = (term73 A B g f).
Proof. exact (MK_COMB (@lem3576621 A B f g) (@lem3576645 A B g f)). Qed.
Lemma lem3576653 {A B : Type'} (g : B -> A) (f : A -> B) : (term74 A B g f) = (term75 A B g f).
Proof. exact (MK_COMB (@lem3576588 A B g) (@lem3576650 A B g f)). Qed.
Lemma lem3576655 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3576656 {A B : Type'} (g : B -> A) (f : A -> B) : (term75 A B g f) = (term73 A B g f).
Proof. exact (@lem3576655 (term73 A B g f)). Qed.
Lemma lem3576671 {A B : Type'} (g : B -> A) (f : A -> B) : (term74 A B g f) = (term73 A B g f).
Proof. exact (TRANS (@lem3576653 A B g f) (@lem3576656 A B g f)). Qed.
Lemma lem3576672 {A B : Type'} (f : A -> B) : (term76 A B f) = (term77 A B f).
Proof. exact (fun_ext (fun g : B -> A => @lem3576671 A B g f)). Qed.
Lemma lem3576673 {A B : Type'} : (@ex (B -> A)) = (@ex (B -> A)).
Proof. exact (eq_refl (@ex (B -> A))). Qed.
Lemma lem3576674 {A B : Type'} (f : A -> B) : (term78 A B f) = (term79 A B f).
Proof. exact (MK_COMB (@lem3576673 A B) (@lem3576672 A B f)). Qed.
Lemma lem3576679 {A B : Type'} (f : A -> B) : ((term47 A B f) = (term78 A B f)) = ((term48 A B f) = (term79 A B f)).
Proof. exact (MK_COMB (@lem3576551 A B f) (@lem3576674 A B f)). Qed.
Lemma lem3576682 {A B : Type'} (f : A -> B) : (term7 A B f) = (term80 A B f).
Proof. exact (MK_COMB (@lem3576416 A B f) (@lem3576679 A B f)). Qed.
Lemma lem3576684 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3576685 {A B : Type'} (f : A -> B) : (term80 A B f) = ((term48 A B f) = (term79 A B f)).
Proof. exact (@lem3576684 ((term48 A B f) = (term79 A B f))). Qed.
Lemma lem3576734 {A B : Type'} (f : A -> B) : (term7 A B f) = ((term48 A B f) = (term79 A B f)).
Proof. exact (TRANS (@lem3576682 A B f) (@lem3576685 A B f)). Qed.
Lemma lem3576735 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3576736 {A B : Type'} (f : A -> B) : (term81 A B f) = (term82 A B f).
Proof. exact (MK_COMB (@lem3576735) (@lem3576734 A B f)). Qed.
Lemma lem3576785 {A B : Type'} (f : A -> B) : ((term48 A B f) = (term79 A B f)) = ((term48 A B f) = (term79 A B f)).
Proof. exact (eq_refl ((term48 A B f) = (term79 A B f))). Qed.
Lemma lem3576786 {A B : Type'} (f : A -> B) : (term83 A B f) = (term84 A B f).
Proof. exact (MK_COMB (@lem3576736 A B f) (@lem3576785 A B f)). Qed.
Lemma lem3576790 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem3576791 {A B : Type'} (f : A -> B) : (term84 A B f) = True.
Proof. exact (@lem3576790 ((term48 A B f) = (term79 A B f))). Qed.
Lemma lem3576792 {A B : Type'} (f : A -> B) : (term83 A B f) = True.
Proof. exact (TRANS (@lem3576786 A B f) (@lem3576791 A B f)). Qed.
Lemma lem3576793 {A B : Type'} (f : A -> B) : True = (term83 A B f).
Proof. exact (SYM (@lem3576792 A B f)). Qed.
Lemma lem3576794 {A B : Type'} (f : A -> B) : term83 A B f.
Proof. exact (EQ_MP (@lem3576793 A B f) (@lem0)). Qed.
Lemma lem3576795 {A B : Type'} (f : A -> B) : (term48 A B f) = (term79 A B f).
Proof. exact (@lem3576794 A B f (@lem3576382 A B f)). Qed.
Lemma lem3576800 {A B : Type'} : term85 A B.
Proof. exact (fun f : A -> B => @lem3576795 A B f). Qed.
