Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_UNIV_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3258390 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3258391 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3258390 A s t). Qed.
Lemma lem3258392 {A : Type'} (s : A -> Prop) : ((@INTER A (@UNIV A) s) = s) = (term1 A s).
Proof. exact (@lem3258391 A (@INTER A (@UNIV A) s) s). Qed.
Lemma lem3258401 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3258392 A s)). Qed.
Lemma lem3258402 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3258403 {A : Type'} : (term4 A) = (term5 A).
Proof. exact (MK_COMB (@lem3258402 A) (@lem3258401 A)). Qed.
Lemma lem3258408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3258409 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (MK_COMB (@lem3258408) (@lem3258403 A)). Qed.
Lemma lem3258417 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3258418 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3258417 A s t). Qed.
Lemma lem3258419 {A : Type'} (s : A -> Prop) : ((@INTER A s (@UNIV A)) = s) = (term8 A s).
Proof. exact (@lem3258418 A (@INTER A s (@UNIV A)) s). Qed.
Lemma lem3258428 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3258419 A s)). Qed.
Lemma lem3258429 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3258430 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem3258429 A) (@lem3258428 A)). Qed.
Lemma lem3258435 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (MK_COMB (@lem3258409 A) (@lem3258430 A)). Qed.
Lemma lem3258438 {A : Type'} : (term14 A) = (term13 A).
Proof. exact (SYM (@lem3258435 A)). Qed.
Lemma lem3258452 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3258453 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (@lem3258452 A s x t). Qed.
Lemma lem3258454 {A : Type'} (x : A) (s : A -> Prop) : (term17 A x s) = (term18 A x s).
Proof. exact (@lem3258453 A (@UNIV A) x s). Qed.
Lemma lem3258458 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3258459 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3258458 A x). Qed.
Lemma lem3258460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3258461 {A : Type'} (x : A) : (term19 A x) = (and True).
Proof. exact (MK_COMB (@lem3258460) (@lem3258459 A x)). Qed.
Lemma lem3258463 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3258464 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3258463 A P x). Qed.
Lemma lem3258465 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3258464 A s x). Qed.
Lemma lem3258466 {A : Type'} (s : A -> Prop) (x : A) : (term18 A x s) = (term20 A s x).
Proof. exact (MK_COMB (@lem3258461 A x) (@lem3258465 A s x)). Qed.
Lemma lem3258468 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3258469 {A : Type'} (s : A -> Prop) (x : A) : (term20 A s x) = (s x).
Proof. exact (@lem3258468 (s x)). Qed.
Lemma lem3258470 {A : Type'} (s : A -> Prop) (x : A) : (term18 A x s) = (s x).
Proof. exact (TRANS (@lem3258466 A s x) (@lem3258469 A s x)). Qed.
Lemma lem3258471 {A : Type'} (s : A -> Prop) (x : A) : (term17 A x s) = (s x).
Proof. exact (TRANS (@lem3258454 A x s) (@lem3258470 A s x)). Qed.
Lemma lem3258472 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3258473 {A : Type'} (s : A -> Prop) (x : A) : (term21 A x s) = (term22 A s x).
Proof. exact (MK_COMB (@lem3258472) (@lem3258471 A s x)). Qed.
Lemma lem3258475 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3258476 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3258475 A P x). Qed.
Lemma lem3258477 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3258476 A s x). Qed.
Lemma lem3258478 {A : Type'} (s : A -> Prop) (x : A) : ((term17 A x s) = (@IN A x s)) = ((s x) = (s x)).
Proof. exact (MK_COMB (@lem3258473 A s x) (@lem3258477 A s x)). Qed.
Lemma lem3258480 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3258481 (x : Prop) : (x = x) = True.
Proof. exact (@lem3258480 Prop x). Qed.
Lemma lem3258482 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = (s x)) = True.
Proof. exact (@lem3258481 (s x)). Qed.
Lemma lem3258483 {A : Type'} (x : A) (s : A -> Prop) : ((term17 A x s) = (@IN A x s)) = True.
Proof. exact (TRANS (@lem3258478 A s x) (@lem3258482 A s x)). Qed.
Lemma lem3258484 {A : Type'} (s : A -> Prop) : (term23 A s) = (term24 A).
Proof. exact (fun_ext (fun x : A => @lem3258483 A x s)). Qed.
Lemma lem3258485 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3258486 {A : Type'} (s : A -> Prop) : (term1 A s) = (term25 A).
Proof. exact (MK_COMB (@lem3258485 A) (@lem3258484 A s)). Qed.
Lemma lem3258488 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3258489 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (@lem3258488 A t). Qed.
Lemma lem3258490 {A : Type'} : (term25 A) = True.
Proof. exact (@lem3258489 A True). Qed.
Lemma lem3258491 {A : Type'} (s : A -> Prop) : (term1 A s) = True.
Proof. exact (TRANS (@lem3258486 A s) (@lem3258490 A)). Qed.
Lemma lem3258492 {A : Type'} : (term3 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3258491 A s)). Qed.
Lemma lem3258493 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3258494 {A : Type'} : (term5 A) = (term28 A).
Proof. exact (MK_COMB (@lem3258493 A) (@lem3258492 A)). Qed.
Lemma lem3258496 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3258497 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (@lem3258496 (A -> Prop) t). Qed.
Lemma lem3258498 {A : Type'} : (term28 A) = True.
Proof. exact (@lem3258497 A True). Qed.
Lemma lem3258499 {A : Type'} : (term5 A) = True.
Proof. exact (TRANS (@lem3258494 A) (@lem3258498 A)). Qed.
Lemma lem3258500 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3258501 {A : Type'} : (term7 A) = (and True).
Proof. exact (MK_COMB (@lem3258500) (@lem3258499 A)). Qed.
Lemma lem3258513 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3258514 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term15 A x s t) = (term16 A s x t).
Proof. exact (@lem3258513 A s x t). Qed.
Lemma lem3258515 {A : Type'} (s : A -> Prop) (x : A) : (term30 A x s) = (term31 A s x).
Proof. exact (@lem3258514 A s x (@UNIV A)). Qed.
Lemma lem3258519 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3258520 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3258519 A P x). Qed.
Lemma lem3258521 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3258520 A s x). Qed.
Lemma lem3258522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3258523 {A : Type'} (s : A -> Prop) (x : A) : (term32 A x s) = (term33 A s x).
Proof. exact (MK_COMB (@lem3258522) (@lem3258521 A s x)). Qed.
Lemma lem3258525 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3258526 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3258525 A x). Qed.
Lemma lem3258527 {A : Type'} (s : A -> Prop) (x : A) : (term31 A s x) = (term34 A s x).
Proof. exact (MK_COMB (@lem3258523 A s x) (@lem3258526 A x)). Qed.
Lemma lem3258529 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3258530 {A : Type'} (s : A -> Prop) (x : A) : (term34 A s x) = (s x).
Proof. exact (@lem3258529 (s x)). Qed.
Lemma lem3258531 {A : Type'} (s : A -> Prop) (x : A) : (term31 A s x) = (s x).
Proof. exact (TRANS (@lem3258527 A s x) (@lem3258530 A s x)). Qed.
Lemma lem3258532 {A : Type'} (s : A -> Prop) (x : A) : (term30 A x s) = (s x).
Proof. exact (TRANS (@lem3258515 A s x) (@lem3258531 A s x)). Qed.
Lemma lem3258533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3258534 {A : Type'} (s : A -> Prop) (x : A) : (term35 A x s) = (term22 A s x).
Proof. exact (MK_COMB (@lem3258533) (@lem3258532 A s x)). Qed.
Lemma lem3258536 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3258537 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3258536 A P x). Qed.
Lemma lem3258538 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3258537 A s x). Qed.
Lemma lem3258539 {A : Type'} (s : A -> Prop) (x : A) : ((term30 A x s) = (@IN A x s)) = ((s x) = (s x)).
Proof. exact (MK_COMB (@lem3258534 A s x) (@lem3258538 A s x)). Qed.
Lemma lem3258541 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3258542 (x : Prop) : (x = x) = True.
Proof. exact (@lem3258541 Prop x). Qed.
Lemma lem3258543 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = (s x)) = True.
Proof. exact (@lem3258542 (s x)). Qed.
Lemma lem3258544 {A : Type'} (x : A) (s : A -> Prop) : ((term30 A x s) = (@IN A x s)) = True.
Proof. exact (TRANS (@lem3258539 A s x) (@lem3258543 A s x)). Qed.
Lemma lem3258545 {A : Type'} (s : A -> Prop) : (term36 A s) = (term24 A).
Proof. exact (fun_ext (fun x : A => @lem3258544 A x s)). Qed.
Lemma lem3258546 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3258547 {A : Type'} (s : A -> Prop) : (term8 A s) = (term25 A).
Proof. exact (MK_COMB (@lem3258546 A) (@lem3258545 A s)). Qed.
Lemma lem3258549 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3258550 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (@lem3258549 A t). Qed.
Lemma lem3258551 {A : Type'} : (term25 A) = True.
Proof. exact (@lem3258550 A True). Qed.
Lemma lem3258552 {A : Type'} (s : A -> Prop) : (term8 A s) = True.
Proof. exact (TRANS (@lem3258547 A s) (@lem3258551 A)). Qed.
Lemma lem3258553 {A : Type'} : (term10 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3258552 A s)). Qed.
Lemma lem3258554 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3258555 {A : Type'} : (term12 A) = (term28 A).
Proof. exact (MK_COMB (@lem3258554 A) (@lem3258553 A)). Qed.
Lemma lem3258557 {A : Type'} (t : Prop) : (term26 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3258558 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (@lem3258557 (A -> Prop) t). Qed.
Lemma lem3258559 {A : Type'} : (term28 A) = True.
Proof. exact (@lem3258558 A True). Qed.
Lemma lem3258560 {A : Type'} : (term12 A) = True.
Proof. exact (TRANS (@lem3258555 A) (@lem3258559 A)). Qed.
Lemma lem3258561 {A : Type'} : (term14 A) = (True /\ True).
Proof. exact (MK_COMB (@lem3258501 A) (@lem3258560 A)). Qed.
Lemma lem3258563 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3258564 : (True /\ True) = True.
Proof. exact (@lem3258563 True). Qed.
Lemma lem3258565 {A : Type'} : (term14 A) = True.
Proof. exact (TRANS (@lem3258561 A) (@lem3258564)). Qed.
Lemma lem3258566 {A : Type'} : True = (term14 A).
Proof. exact (SYM (@lem3258565 A)). Qed.
Lemma lem3258567 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3258566 A) (@lem0)). Qed.
Lemma lem3258568 {A : Type'} : term13 A.
Proof. exact (EQ_MP (@lem3258438 A) (@lem3258567 A)). Qed.
