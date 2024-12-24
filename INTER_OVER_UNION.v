Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_OVER_UNION_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3262342 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3262343 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3262342 A s t). Qed.
Lemma lem3262344 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : ((term1 A s t u) = (term2 A t s u)) = (term3 A t s u).
Proof. exact (@lem3262343 A (term1 A s t u) (term2 A t s u)). Qed.
Lemma lem3262353 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term4 A t s) = (term5 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3262344 A t s u)). Qed.
Lemma lem3262354 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3262355 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term6 A t s) = (term7 A t s).
Proof. exact (MK_COMB (@lem3262354 A) (@lem3262353 A t s)). Qed.
Lemma lem3262360 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3262355 A t s)). Qed.
Lemma lem3262361 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3262362 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A s).
Proof. exact (MK_COMB (@lem3262361 A) (@lem3262360 A s)). Qed.
Lemma lem3262367 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3262362 A s)). Qed.
Lemma lem3262368 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3262369 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem3262368 A) (@lem3262367 A)). Qed.
Lemma lem3262374 {A : Type'} : (term15 A) = (term14 A).
Proof. exact (SYM (@lem3262369 A)). Qed.
Lemma lem3262394 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3262395 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3262394 A s x t). Qed.
Lemma lem3262396 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (u : A -> Prop) : (term18 A x s t u) = (term19 A s x t u).
Proof. exact (@lem3262395 A s x (@INTER A t u)). Qed.
Lemma lem3262400 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3262401 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3262400 A P x). Qed.
Lemma lem3262402 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3262401 A s x). Qed.
Lemma lem3262403 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3262404 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term21 A s x).
Proof. exact (MK_COMB (@lem3262403) (@lem3262402 A s x)). Qed.
Lemma lem3262406 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term22 A x s t) = (term23 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3262407 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term22 A x s t) = (term23 A s x t).
Proof. exact (@lem3262406 A s x t). Qed.
Lemma lem3262408 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term22 A x t u) = (term23 A t x u).
Proof. exact (@lem3262407 A t x u). Qed.
Lemma lem3262412 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3262413 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3262412 A P x). Qed.
Lemma lem3262414 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3262413 A t x). Qed.
Lemma lem3262415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3262416 {A : Type'} (t : A -> Prop) (x : A) : (term24 A x t) = (term25 A t x).
Proof. exact (MK_COMB (@lem3262415) (@lem3262414 A t x)). Qed.
Lemma lem3262418 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3262419 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3262418 A P x). Qed.
Lemma lem3262420 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3262419 A u x). Qed.
Lemma lem3262421 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term23 A t x u) = (term26 A t u x).
Proof. exact (MK_COMB (@lem3262416 A t x) (@lem3262420 A u x)). Qed.
Lemma lem3262424 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term22 A x t u) = (term26 A t u x).
Proof. exact (TRANS (@lem3262408 A t x u) (@lem3262421 A t u x)). Qed.
Lemma lem3262425 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term19 A s x t u) = (term27 A s t u x).
Proof. exact (MK_COMB (@lem3262404 A s x) (@lem3262424 A t u x)). Qed.
Lemma lem3262428 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term18 A x s t u) = (term27 A s t u x).
Proof. exact (TRANS (@lem3262396 A s x t u) (@lem3262425 A s t u x)). Qed.
Lemma lem3262429 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3262430 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term28 A x s t u) = (term29 A s t u x).
Proof. exact (MK_COMB (@lem3262429) (@lem3262428 A s t u x)). Qed.
Lemma lem3262432 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term22 A x s t) = (term23 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3262433 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term22 A x s t) = (term23 A s x t).
Proof. exact (@lem3262432 A s x t). Qed.
Lemma lem3262434 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (u : A -> Prop) : (term30 A x t s u) = (term31 A t x s u).
Proof. exact (@lem3262433 A (@UNION A s t) x (@UNION A s u)). Qed.
Lemma lem3262438 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3262439 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3262438 A s x t). Qed.
Lemma lem3262443 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3262444 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3262443 A P x). Qed.
Lemma lem3262445 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3262444 A s x). Qed.
Lemma lem3262446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3262447 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term21 A s x).
Proof. exact (MK_COMB (@lem3262446) (@lem3262445 A s x)). Qed.
Lemma lem3262449 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3262450 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3262449 A P x). Qed.
Lemma lem3262451 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3262450 A t x). Qed.
Lemma lem3262452 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term17 A s x t) = (term32 A s t x).
Proof. exact (MK_COMB (@lem3262447 A s x) (@lem3262451 A t x)). Qed.
Lemma lem3262455 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term16 A x s t) = (term32 A s t x).
Proof. exact (TRANS (@lem3262439 A s x t) (@lem3262452 A s t x)). Qed.
Lemma lem3262456 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3262457 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term33 A x s t) = (term34 A s t x).
Proof. exact (MK_COMB (@lem3262456) (@lem3262455 A s t x)). Qed.
Lemma lem3262459 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3262460 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3262459 A s x t). Qed.
Lemma lem3262461 {A : Type'} (s : A -> Prop) (x : A) (u : A -> Prop) : (term16 A x s u) = (term17 A s x u).
Proof. exact (@lem3262460 A s x u). Qed.
Lemma lem3262465 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3262466 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3262465 A P x). Qed.
Lemma lem3262467 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3262466 A s x). Qed.
Lemma lem3262468 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3262469 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term21 A s x).
Proof. exact (MK_COMB (@lem3262468) (@lem3262467 A s x)). Qed.
Lemma lem3262471 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3262472 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3262471 A P x). Qed.
Lemma lem3262473 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3262472 A u x). Qed.
Lemma lem3262474 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term17 A s x u) = (term32 A s u x).
Proof. exact (MK_COMB (@lem3262469 A s x) (@lem3262473 A u x)). Qed.
Lemma lem3262477 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term16 A x s u) = (term32 A s u x).
Proof. exact (TRANS (@lem3262461 A s x u) (@lem3262474 A s u x)). Qed.
Lemma lem3262478 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term31 A t x s u) = (term35 A t s u x).
Proof. exact (MK_COMB (@lem3262457 A s t x) (@lem3262477 A s u x)). Qed.
Lemma lem3262481 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term30 A x t s u) = (term35 A t s u x).
Proof. exact (TRANS (@lem3262434 A t x s u) (@lem3262478 A t s u x)). Qed.
Lemma lem3262482 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : ((term18 A x s t u) = (term30 A x t s u)) = ((term27 A s t u x) = (term35 A t s u x)).
Proof. exact (MK_COMB (@lem3262430 A s t u x) (@lem3262481 A t s u x)). Qed.
Lemma lem3262485 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term36 A t s u) = (term37 A t s u).
Proof. exact (fun_ext (fun x : A => @lem3262482 A t s u x)). Qed.
Lemma lem3262486 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3262487 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term3 A t s u) = (term38 A t s u).
Proof. exact (MK_COMB (@lem3262486 A) (@lem3262485 A t s u)). Qed.
Lemma lem3262492 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term5 A t s) = (term39 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3262487 A t s u)). Qed.
Lemma lem3262493 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3262494 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term7 A t s) = (term40 A t s).
Proof. exact (MK_COMB (@lem3262493 A) (@lem3262492 A t s)). Qed.
Lemma lem3262499 {A : Type'} (s : A -> Prop) : (term9 A s) = (term41 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3262494 A t s)). Qed.
Lemma lem3262500 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3262501 {A : Type'} (s : A -> Prop) : (term11 A s) = (term42 A s).
Proof. exact (MK_COMB (@lem3262500 A) (@lem3262499 A s)). Qed.
Lemma lem3262506 {A : Type'} : (term13 A) = (term43 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3262501 A s)). Qed.
Lemma lem3262507 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3262508 {A : Type'} : (term15 A) = (term44 A).
Proof. exact (MK_COMB (@lem3262507 A) (@lem3262506 A)). Qed.
Lemma lem3262513 {A : Type'} : (term44 A) = (term15 A).
Proof. exact (SYM (@lem3262508 A)). Qed.
Lemma lem3262515 (p : Prop) : p = (term45 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3262516 {A : Type'} : (term44 A) = (term46 A).
Proof. exact (@lem3262515 (term44 A)). Qed.
Lemma lem3262517 {A : Type'} : (term46 A) = (term44 A).
Proof. exact (SYM (@lem3262516 A)). Qed.
Lemma lem3262518 {A : Type'} (h1 : term47 A) : term47 A.
Proof. exact (h1). Qed.
Lemma lem3262521 {A : Type'} (h1 : term46 A) : term46 A.
Proof. exact (h1). Qed.
Lemma lem3262522 {A : Type'} : term48 A.
Proof. exact (fun h0 : term46 A => @lem3262521 A h0). Qed.
Lemma lem3262523 {A : Type'} (h1 : term48 A) : term48 A.
Proof. exact (h1). Qed.
Lemma lem3262524 {A : Type'} (h1 : term46 A) : term46 A.
Proof. exact (h1). Qed.
Lemma lem3262525 {A : Type'} (h1 : term46 A) (h2 : term48 A) : term46 A.
Proof. exact (@lem3262523 A h2 (@lem3262524 A h1)). Qed.
Lemma lem3262526 {A : Type'} (h1 : term46 A) : term49 A.
Proof. exact (fun h0 : term48 A => @lem3262525 A h1 h0). Qed.
Lemma lem3262527 {A : Type'} (h1 : term48 A) : term48 A.
Proof. exact (h1). Qed.
Lemma lem3262528 {A : Type'} (h1 : term46 A) (h2 : term48 A) : term46 A.
Proof. exact (@lem3262526 A h1 (@lem3262527 A h2)). Qed.
Lemma lem3262529 {A : Type'} (h1 : term48 A) : term48 A.
Proof. exact (fun h0 : term46 A => @lem3262528 A h0 h1). Qed.
Lemma lem3262530 {A : Type'} : term50 A.
Proof. exact (fun h0 : term48 A => @lem3262529 A h0). Qed.
Lemma lem3262533 {A : Type'} : term48 A.
Proof. exact (@lem3262530 A (@lem3262522 A)). Qed.
Lemma lem3262534 {A : Type'} : term48 A.
Proof. exact (@lem3262533 A). Qed.
Lemma lem3262536 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3262537 {A : Type'} : (term46 A) = (term51 A).
Proof. exact (@lem3262536 (term47 A)). Qed.
Lemma lem3262539 (t : Prop) : (term52 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3262540 {A : Type'} : (term51 A) = (term44 A).
Proof. exact (@lem3262539 (term44 A)). Qed.
Lemma lem3262571 {A : Type'} : (term46 A) = (term44 A).
Proof. exact (TRANS (@lem3262537 A) (@lem3262540 A)). Qed.
Lemma lem3262596 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : ((term27 A s t u x) = (term35 A t s u x)) = ((term27 A s t u x) = (term35 A t s u x)).
Proof. exact (eq_refl ((term27 A s t u x) = (term35 A t s u x))). Qed.
Lemma lem3262597 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term37 A t s u) = (term37 A t s u).
Proof. exact (fun_ext (fun x : A => @lem3262596 A t s u x)). Qed.
Lemma lem3262598 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3262599 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : (term38 A t s u) = (term38 A t s u).
Proof. exact (MK_COMB (@lem3262598 A) (@lem3262597 A t s u)). Qed.
Lemma lem3262600 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term39 A t s) = (term39 A t s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3262599 A t s u)). Qed.
Lemma lem3262601 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3262602 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term40 A t s) = (term40 A t s).
Proof. exact (MK_COMB (@lem3262601 A) (@lem3262600 A t s)). Qed.
Lemma lem3262603 {A : Type'} (s : A -> Prop) : (term41 A s) = (term41 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3262602 A t s)). Qed.
Lemma lem3262604 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3262605 {A : Type'} (s : A -> Prop) : (term42 A s) = (term42 A s).
Proof. exact (MK_COMB (@lem3262604 A) (@lem3262603 A s)). Qed.
Lemma lem3262606 {A : Type'} : (term43 A) = (term43 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3262605 A s)). Qed.
Lemma lem3262607 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3262608 {A : Type'} : (term44 A) = (term44 A).
Proof. exact (MK_COMB (@lem3262607 A) (@lem3262606 A)). Qed.
Lemma lem3262645 {A : Type'} : (term46 A) = (term44 A).
Proof. exact (TRANS (@lem3262571 A) (@lem3262608 A)). Qed.
Lemma lem3262646 {A : Type'} : (term44 A) = (term46 A).
Proof. exact (SYM (@lem3262645 A)). Qed.
Lemma lem3262648 (p : Prop) : p = (term45 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3262649 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : ((term27 A s t u x) = (term35 A t s u x)) = (term53 A t s u x).
Proof. exact (@lem3262648 ((term27 A s t u x) = (term35 A t s u x))). Qed.
Lemma lem3262650 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term53 A t s u x) = ((term27 A s t u x) = (term35 A t s u x)).
Proof. exact (SYM (@lem3262649 A t s u x)). Qed.
Lemma lem3262651 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term54 A t s u x) : term54 A t s u x.
Proof. exact (h1). Qed.
Lemma lem3262662 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term55 A t u x) = (term56 A t u x).
Proof. exact (@lem17045 (t x) (u x)). Qed.
Lemma lem3262667 {A : Type'} (s : A -> Prop) (x : A) : (term57 A s x) = (term57 A s x).
Proof. exact (eq_refl (term57 A s x)). Qed.
Lemma lem3262668 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term58 A s t u x) = (term59 A s t u x).
Proof. exact (MK_COMB (@lem3262667 A s x) (@lem3262662 A t u x)). Qed.
Lemma lem3262669 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term60 A s t u x) = (term58 A s t u x).
Proof. exact (@lem17160 (s x) (term26 A t u x)). Qed.
Lemma lem3262670 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term60 A s t u x) = (term59 A s t u x).
Proof. exact (TRANS (@lem3262669 A s t u x) (@lem3262668 A s t u x)). Qed.
Lemma lem3262682 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term61 A s t x) = (term62 A s t x).
Proof. exact (@lem17160 (s x) (t x)). Qed.
Lemma lem3262694 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) : (term61 A s u x) = (term62 A s u x).
Proof. exact (@lem17160 (s x) (u x)). Qed.
Lemma lem3262698 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3262699 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term63 A s t x) = (term64 A s t x).
Proof. exact (MK_COMB (@lem3262698) (@lem3262682 A s t x)). Qed.
Lemma lem3262700 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term65 A t s u x) = (term66 A t s u x).
Proof. exact (MK_COMB (@lem3262699 A s t x) (@lem3262694 A s u x)). Qed.
Lemma lem3262701 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term67 A t s u x) = (term65 A t s u x).
Proof. exact (@lem17045 (term32 A s t x) (term32 A s u x)). Qed.
Lemma lem3262702 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term67 A t s u x) = (term66 A t s u x).
Proof. exact (TRANS (@lem3262701 A t s u x) (@lem3262700 A t s u x)). Qed.
Lemma lem3262705 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term35 A t s u x) = (term35 A t s u x).
Proof. exact (eq_refl (term35 A t s u x)). Qed.
Lemma lem3262706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3262707 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term68 A s t u x) = (term69 A s t u x).
Proof. exact (MK_COMB (@lem3262706) (@lem3262670 A s t u x)). Qed.
Lemma lem3262708 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term70 A t s u x) = (term71 A t s u x).
Proof. exact (MK_COMB (@lem3262707 A s t u x) (@lem3262705 A t s u x)). Qed.
Lemma lem3262710 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term72 A s t u x) = (term72 A s t u x).
Proof. exact (eq_refl (term72 A s t u x)). Qed.
Lemma lem3262711 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term73 A t s u x) = (term74 A t s u x).
Proof. exact (MK_COMB (@lem3262710 A s t u x) (@lem3262702 A t s u x)). Qed.
Lemma lem3262712 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3262713 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term75 A t s u x) = (term76 A t s u x).
Proof. exact (MK_COMB (@lem3262712) (@lem3262711 A t s u x)). Qed.
Lemma lem3262714 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term77 A t s u x) = (term78 A t s u x).
Proof. exact (MK_COMB (@lem3262713 A t s u x) (@lem3262708 A t s u x)). Qed.
Lemma lem3262715 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term54 A t s u x) = (term77 A t s u x).
Proof. exact (@lem17646 (term27 A s t u x) (term35 A t s u x)). Qed.
Lemma lem3262720 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term54 A t s u x) = (term78 A t s u x).
Proof. exact (TRANS (@lem3262715 A t s u x) (@lem3262714 A t s u x)). Qed.
Lemma lem3262817 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term54 A t s u x) : term78 A t s u x.
Proof. exact (EQ_MP (@lem3262720 A t s u x) (@lem3262651 A t s u x h1)). Qed.
Lemma lem3262818 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : term74 A t s u x.
Proof. exact (h1). Qed.
Lemma lem3262819 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term71 A t s u x.
Proof. exact (h1). Qed.
Lemma lem3262820 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : term66 A t s u x.
Proof. exact (proj2 (@lem3262818 A t s u x h1)). Qed.
Lemma lem3262821 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : term27 A s t u x.
Proof. exact (proj1 (@lem3262818 A t s u x h1)). Qed.
Lemma lem3262822 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term62 A s t x) : term62 A s t x.
Proof. exact (h1). Qed.
Lemma lem3262823 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term62 A s u x) : term62 A s u x.
Proof. exact (h1). Qed.
Lemma lem3262827 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term26 A t u x) : term26 A t u x.
Proof. exact (h1). Qed.
Lemma lem3262833 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term26 A t u x) : term26 A t u x.
Proof. exact (h1). Qed.
Lemma lem3262836 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term35 A t s u x.
Proof. exact (proj2 (@lem3262819 A t s u x h1)). Qed.
Lemma lem3262837 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term59 A s t u x.
Proof. exact (proj1 (@lem3262819 A t s u x h1)). Qed.
Lemma lem3262838 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term32 A s u x.
Proof. exact (proj2 (@lem3262836 A t s u x h1)). Qed.
Lemma lem3262839 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term32 A s t x.
Proof. exact (proj1 (@lem3262836 A t s u x h1)). Qed.
Lemma lem3262840 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term56 A t u x.
Proof. exact (proj2 (@lem3262837 A t s u x h1)). Qed.
Lemma lem3262867 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3262895 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3262923 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3262927 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3262935 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) : term79 A t x.
Proof. exact (h1). Qed.
Lemma lem3262943 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3262959 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3262967 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) : term79 A t x.
Proof. exact (h1). Qed.
Lemma lem3262975 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3262987 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3262991 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3263003 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3263015 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) : term79 A u x.
Proof. exact (h1). Qed.
Lemma lem3263019 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem3263031 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) : term79 A u x.
Proof. exact (h1). Qed.
Lemma lem3263035 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem3263041 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term62 A s t x) : term79 A s x.
Proof. exact (proj1 (@lem3262822 A s t x h1)). Qed.
Lemma lem3263045 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3263049 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term62 A s t x) : term79 A t x.
Proof. exact (proj2 (@lem3262822 A s t x h1)). Qed.
Lemma lem3263055 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term62 A s u x) : term79 A s x.
Proof. exact (proj1 (@lem3262823 A s u x h1)). Qed.
Lemma lem3263059 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3263063 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term62 A s u x) : term79 A u x.
Proof. exact (proj2 (@lem3262823 A s u x h1)). Qed.
Lemma lem3263069 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term79 A s x.
Proof. exact (proj1 (@lem3262837 A t s u x h1)). Qed.
Lemma lem3263073 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3263075 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3263079 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) : term79 A t x.
Proof. exact (h1). Qed.
Lemma lem3263083 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3263085 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term79 A s x.
Proof. exact (proj1 (@lem3262837 A t s u x h1)). Qed.
Lemma lem3263091 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3263095 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) : term79 A t x.
Proof. exact (h1). Qed.
Lemma lem3263099 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3263101 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term79 A s x.
Proof. exact (proj1 (@lem3262837 A t s u x h1)). Qed.
Lemma lem3263105 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3263107 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3263109 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term79 A s x.
Proof. exact (proj1 (@lem3262837 A t s u x h1)). Qed.
Lemma lem3263113 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3263119 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) : term79 A u x.
Proof. exact (h1). Qed.
Lemma lem3263121 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem3263127 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) : term79 A u x.
Proof. exact (h1). Qed.
Lemma lem3263129 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem3263133 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3263134 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term80 A s x.
Proof. exact (fun h0 : term79 A s x => @lem3263133 A s x h1). Qed.
Lemma lem3263136 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263137 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (s x).
Proof. exact (@lem3263136 (s x)). Qed.
Lemma lem3263138 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3263137 A s x) (@lem3263134 A s x h1)). Qed.
Lemma lem3263141 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3263143 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term82 A s x).
Proof. exact (@lem3263141 (s x)). Qed.
Lemma lem3263146 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term62 A s t x) : term82 A s x.
Proof. exact (EQ_MP (@lem3263143 A s x) (@lem3263041 A s t x h1)). Qed.
Lemma lem3263149 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s t x) : False.
Proof. exact (@lem3263146 A s t x h2 (@lem3263138 A s x h1)). Qed.
Lemma lem3263150 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s t x) : term83.
Proof. exact (fun h0 : ~ False => @lem3263149 A s t x h1 h2). Qed.
Lemma lem3263152 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263153 : term83 = False.
Proof. exact (@lem3263152 False). Qed.
Lemma lem3263154 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s t x) : False.
Proof. exact (EQ_MP (@lem3263153) (@lem3263150 A s t x h1 h2)). Qed.
Lemma lem3263156 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term26 A t u x) : t x.
Proof. exact (proj1 (@lem3262827 A t u x h1)). Qed.
Lemma lem3263157 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term26 A t u x) : term80 A t x.
Proof. exact (fun h0 : term79 A t x => @lem3263156 A t u x h1). Qed.
Lemma lem3263159 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263160 {A : Type'} (t : A -> Prop) (x : A) : (term80 A t x) = (t x).
Proof. exact (@lem3263159 (t x)). Qed.
Lemma lem3263161 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term26 A t u x) : t x.
Proof. exact (EQ_MP (@lem3263160 A t x) (@lem3263157 A t u x h1)). Qed.
Lemma lem3263164 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3263166 {A : Type'} (t : A -> Prop) (x : A) : (term79 A t x) = (term82 A t x).
Proof. exact (@lem3263164 (t x)). Qed.
Lemma lem3263169 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term62 A s t x) : term82 A t x.
Proof. exact (EQ_MP (@lem3263166 A t x) (@lem3263049 A s t x h1)). Qed.
Lemma lem3263172 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term62 A s t x) (h2 : term26 A t u x) : False.
Proof. exact (@lem3263169 A s t x h1 (@lem3263161 A t u x h2)). Qed.
Lemma lem3263173 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term62 A s t x) (h2 : term26 A t u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3263172 A s t u x h1 h2). Qed.
Lemma lem3263175 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263176 : term83 = False.
Proof. exact (@lem3263175 False). Qed.
Lemma lem3263177 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term62 A s t x) (h2 : term26 A t u x) : False.
Proof. exact (EQ_MP (@lem3263176) (@lem3263173 A s t u x h1 h2)). Qed.
Lemma lem3263179 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3263180 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term80 A s x.
Proof. exact (fun h0 : term79 A s x => @lem3263179 A s x h1). Qed.
Lemma lem3263182 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263183 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (s x).
Proof. exact (@lem3263182 (s x)). Qed.
Lemma lem3263184 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3263183 A s x) (@lem3263180 A s x h1)). Qed.
Lemma lem3263187 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3263189 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term82 A s x).
Proof. exact (@lem3263187 (s x)). Qed.
Lemma lem3263192 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term62 A s u x) : term82 A s x.
Proof. exact (EQ_MP (@lem3263189 A s x) (@lem3263055 A s u x h1)). Qed.
Lemma lem3263195 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s u x) : False.
Proof. exact (@lem3263192 A s u x h2 (@lem3263184 A s x h1)). Qed.
Lemma lem3263196 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3263195 A s u x h1 h2). Qed.
Lemma lem3263198 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263199 : term83 = False.
Proof. exact (@lem3263198 False). Qed.
Lemma lem3263200 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s u x) : False.
Proof. exact (EQ_MP (@lem3263199) (@lem3263196 A s u x h1 h2)). Qed.
Lemma lem3263202 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term26 A t u x) : u x.
Proof. exact (proj2 (@lem3262833 A t u x h1)). Qed.
Lemma lem3263203 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term26 A t u x) : term80 A u x.
Proof. exact (fun h0 : term79 A u x => @lem3263202 A t u x h1). Qed.
Lemma lem3263205 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263206 {A : Type'} (u : A -> Prop) (x : A) : (term80 A u x) = (u x).
Proof. exact (@lem3263205 (u x)). Qed.
Lemma lem3263207 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term26 A t u x) : u x.
Proof. exact (EQ_MP (@lem3263206 A u x) (@lem3263203 A t u x h1)). Qed.
Lemma lem3263210 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3263212 {A : Type'} (u : A -> Prop) (x : A) : (term79 A u x) = (term82 A u x).
Proof. exact (@lem3263210 (u x)). Qed.
Lemma lem3263215 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term62 A s u x) : term82 A u x.
Proof. exact (EQ_MP (@lem3263212 A u x) (@lem3263063 A s u x h1)). Qed.
Lemma lem3263218 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term62 A s u x) (h2 : term26 A t u x) : False.
Proof. exact (@lem3263215 A s u x h1 (@lem3263207 A t u x h2)). Qed.
Lemma lem3263219 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term62 A s u x) (h2 : term26 A t u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3263218 A s t u x h1 h2). Qed.
Lemma lem3263221 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263222 : term83 = False.
Proof. exact (@lem3263221 False). Qed.
Lemma lem3263223 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term62 A s u x) (h2 : term26 A t u x) : False.
Proof. exact (EQ_MP (@lem3263222) (@lem3263219 A s t u x h1 h2)). Qed.
Lemma lem3263225 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3263226 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term80 A s x.
Proof. exact (fun h0 : term79 A s x => @lem3263225 A s x h1). Qed.
Lemma lem3263228 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263229 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (s x).
Proof. exact (@lem3263228 (s x)). Qed.
Lemma lem3263230 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3263229 A s x) (@lem3263226 A s x h1)). Qed.
Lemma lem3263233 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3263235 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term82 A s x).
Proof. exact (@lem3263233 (s x)). Qed.
Lemma lem3263238 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term82 A s x.
Proof. exact (EQ_MP (@lem3263235 A s x) (@lem3263069 A t s u x h1)). Qed.
Lemma lem3263241 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (@lem3263238 A t s u x h2 (@lem3263230 A s x h1)). Qed.
Lemma lem3263242 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3263241 A t s u x h1 h2). Qed.
Lemma lem3263244 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263245 : term83 = False.
Proof. exact (@lem3263244 False). Qed.
Lemma lem3263246 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263245) (@lem3263242 A t s u x h1 h2)). Qed.
Lemma lem3263248 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3263249 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term80 A t x.
Proof. exact (fun h0 : term79 A t x => @lem3263248 A t x h1). Qed.
Lemma lem3263251 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263252 {A : Type'} (t : A -> Prop) (x : A) : (term80 A t x) = (t x).
Proof. exact (@lem3263251 (t x)). Qed.
Lemma lem3263253 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3263252 A t x) (@lem3263249 A t x h1)). Qed.
Lemma lem3263256 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3263258 {A : Type'} (t : A -> Prop) (x : A) : (term79 A t x) = (term82 A t x).
Proof. exact (@lem3263256 (t x)). Qed.
Lemma lem3263261 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) : term82 A t x.
Proof. exact (EQ_MP (@lem3263258 A t x) (@lem3263079 A t x h1)). Qed.
Lemma lem3263264 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (@lem3263261 A t x h1 (@lem3263253 A t x h2)). Qed.
Lemma lem3263265 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : term83.
Proof. exact (fun h0 : ~ False => @lem3263264 A t x h1 h2). Qed.
Lemma lem3263267 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263268 : term83 = False.
Proof. exact (@lem3263267 False). Qed.
Lemma lem3263269 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3263268) (@lem3263265 A t x h1 h2)). Qed.
Lemma lem3263271 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3263272 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term80 A s x.
Proof. exact (fun h0 : term79 A s x => @lem3263271 A s x h1). Qed.
Lemma lem3263274 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263275 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (s x).
Proof. exact (@lem3263274 (s x)). Qed.
Lemma lem3263276 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3263275 A s x) (@lem3263272 A s x h1)). Qed.
Lemma lem3263279 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3263281 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term82 A s x).
Proof. exact (@lem3263279 (s x)). Qed.
Lemma lem3263284 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term82 A s x.
Proof. exact (EQ_MP (@lem3263281 A s x) (@lem3263085 A t s u x h1)). Qed.
Lemma lem3263287 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (@lem3263284 A t s u x h2 (@lem3263276 A s x h1)). Qed.
Lemma lem3263288 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3263287 A t s u x h1 h2). Qed.
Lemma lem3263290 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263291 : term83 = False.
Proof. exact (@lem3263290 False). Qed.
Lemma lem3263292 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263291) (@lem3263288 A t s u x h1 h2)). Qed.
Lemma lem3263294 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3263295 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term80 A t x.
Proof. exact (fun h0 : term79 A t x => @lem3263294 A t x h1). Qed.
Lemma lem3263297 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263298 {A : Type'} (t : A -> Prop) (x : A) : (term80 A t x) = (t x).
Proof. exact (@lem3263297 (t x)). Qed.
Lemma lem3263299 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3263298 A t x) (@lem3263295 A t x h1)). Qed.
Lemma lem3263302 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3263304 {A : Type'} (t : A -> Prop) (x : A) : (term79 A t x) = (term82 A t x).
Proof. exact (@lem3263302 (t x)). Qed.
Lemma lem3263307 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) : term82 A t x.
Proof. exact (EQ_MP (@lem3263304 A t x) (@lem3263095 A t x h1)). Qed.
Lemma lem3263310 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (@lem3263307 A t x h1 (@lem3263299 A t x h2)). Qed.
Lemma lem3263311 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : term83.
Proof. exact (fun h0 : ~ False => @lem3263310 A t x h1 h2). Qed.
Lemma lem3263313 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263314 : term83 = False.
Proof. exact (@lem3263313 False). Qed.
Lemma lem3263315 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3263314) (@lem3263311 A t x h1 h2)). Qed.
Lemma lem3263317 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3263318 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term80 A s x.
Proof. exact (fun h0 : term79 A s x => @lem3263317 A s x h1). Qed.
Lemma lem3263320 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263321 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (s x).
Proof. exact (@lem3263320 (s x)). Qed.
Lemma lem3263322 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3263321 A s x) (@lem3263318 A s x h1)). Qed.
Lemma lem3263325 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3263327 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term82 A s x).
Proof. exact (@lem3263325 (s x)). Qed.
Lemma lem3263330 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term82 A s x.
Proof. exact (EQ_MP (@lem3263327 A s x) (@lem3263101 A t s u x h1)). Qed.
Lemma lem3263333 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (@lem3263330 A t s u x h2 (@lem3263322 A s x h1)). Qed.
Lemma lem3263334 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3263333 A t s u x h1 h2). Qed.
Lemma lem3263336 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263337 : term83 = False.
Proof. exact (@lem3263336 False). Qed.
Lemma lem3263338 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263337) (@lem3263334 A t s u x h1 h2)). Qed.
Lemma lem3263340 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3263341 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term80 A s x.
Proof. exact (fun h0 : term79 A s x => @lem3263340 A s x h1). Qed.
Lemma lem3263343 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263344 {A : Type'} (s : A -> Prop) (x : A) : (term80 A s x) = (s x).
Proof. exact (@lem3263343 (s x)). Qed.
Lemma lem3263345 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3263344 A s x) (@lem3263341 A s x h1)). Qed.
Lemma lem3263348 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3263350 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term82 A s x).
Proof. exact (@lem3263348 (s x)). Qed.
Lemma lem3263353 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : term82 A s x.
Proof. exact (EQ_MP (@lem3263350 A s x) (@lem3263109 A t s u x h1)). Qed.
Lemma lem3263356 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (@lem3263353 A t s u x h2 (@lem3263345 A s x h1)). Qed.
Lemma lem3263357 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3263356 A t s u x h1 h2). Qed.
Lemma lem3263359 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263360 : term83 = False.
Proof. exact (@lem3263359 False). Qed.
Lemma lem3263361 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263360) (@lem3263357 A t s u x h1 h2)). Qed.
Lemma lem3263363 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem3263364 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : term80 A u x.
Proof. exact (fun h0 : term79 A u x => @lem3263363 A u x h1). Qed.
Lemma lem3263366 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263367 {A : Type'} (u : A -> Prop) (x : A) : (term80 A u x) = (u x).
Proof. exact (@lem3263366 (u x)). Qed.
Lemma lem3263368 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (EQ_MP (@lem3263367 A u x) (@lem3263364 A u x h1)). Qed.
Lemma lem3263371 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3263373 {A : Type'} (u : A -> Prop) (x : A) : (term79 A u x) = (term82 A u x).
Proof. exact (@lem3263371 (u x)). Qed.
Lemma lem3263376 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) : term82 A u x.
Proof. exact (EQ_MP (@lem3263373 A u x) (@lem3263119 A u x h1)). Qed.
Lemma lem3263379 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (@lem3263376 A u x h1 (@lem3263368 A u x h2)). Qed.
Lemma lem3263380 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3263379 A u x h1 h2). Qed.
Lemma lem3263382 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263383 : term83 = False.
Proof. exact (@lem3263382 False). Qed.
Lemma lem3263384 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3263383) (@lem3263380 A u x h1 h2)). Qed.
Lemma lem3263386 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (h1). Qed.
Lemma lem3263387 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : term80 A u x.
Proof. exact (fun h0 : term79 A u x => @lem3263386 A u x h1). Qed.
Lemma lem3263389 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263390 {A : Type'} (u : A -> Prop) (x : A) : (term80 A u x) = (u x).
Proof. exact (@lem3263389 (u x)). Qed.
Lemma lem3263391 {A : Type'} (u : A -> Prop) (x : A) (h1 : u x) : u x.
Proof. exact (EQ_MP (@lem3263390 A u x) (@lem3263387 A u x h1)). Qed.
Lemma lem3263394 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3263396 {A : Type'} (u : A -> Prop) (x : A) : (term79 A u x) = (term82 A u x).
Proof. exact (@lem3263394 (u x)). Qed.
Lemma lem3263399 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) : term82 A u x.
Proof. exact (EQ_MP (@lem3263396 A u x) (@lem3263127 A u x h1)). Qed.
Lemma lem3263402 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (@lem3263399 A u x h1 (@lem3263391 A u x h2)). Qed.
Lemma lem3263403 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : term83.
Proof. exact (fun h0 : ~ False => @lem3263402 A u x h1 h2). Qed.
Lemma lem3263405 (p : Prop) : (term81 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3263406 : term83 = False.
Proof. exact (@lem3263405 False). Qed.
Lemma lem3263407 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3263406) (@lem3263403 A u x h1 h2)). Qed.
Lemma lem3263408 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem3263407 A u x h1 h2) (fun h3 : False => @lem3263129 A u x h2)). Qed.
Lemma lem3263409 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3263408 A u x h1 h2) (@lem3263129 A u x h2)). Qed.
Lemma lem3263410 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (term79 A u x) = False.
Proof. exact (prop_ext (fun h3 : term79 A u x => @lem3263409 A u x h1 h2) (fun h3 : False => @lem3263127 A u x h1)). Qed.
Lemma lem3263411 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3263410 A u x h1 h2) (@lem3263127 A u x h1)). Qed.
Lemma lem3263412 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem3263384 A u x h1 h2) (fun h3 : False => @lem3263121 A u x h2)). Qed.
Lemma lem3263413 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3263412 A u x h1 h2) (@lem3263121 A u x h2)). Qed.
Lemma lem3263414 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (term79 A u x) = False.
Proof. exact (prop_ext (fun h3 : term79 A u x => @lem3263413 A u x h1 h2) (fun h3 : False => @lem3263119 A u x h1)). Qed.
Lemma lem3263415 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3263414 A u x h1 h2) (@lem3263119 A u x h1)). Qed.
Lemma lem3263416 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263361 A t s u x h1 h2) (fun h3 : False => @lem3263113 A s x h1)). Qed.
Lemma lem3263417 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263416 A t s u x h1 h2) (@lem3263113 A s x h1)). Qed.
Lemma lem3263418 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263338 A t s u x h1 h2) (fun h3 : False => @lem3263107 A s x h1)). Qed.
Lemma lem3263419 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263418 A t s u x h1 h2) (@lem3263107 A s x h1)). Qed.
Lemma lem3263420 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263419 A t s u x h1 h2) (fun h3 : False => @lem3263105 A s x h1)). Qed.
Lemma lem3263421 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263420 A t s u x h1 h2) (@lem3263105 A s x h1)). Qed.
Lemma lem3263422 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3263315 A t x h1 h2) (fun h3 : False => @lem3263099 A t x h2)). Qed.
Lemma lem3263423 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3263422 A t x h1 h2) (@lem3263099 A t x h2)). Qed.
Lemma lem3263424 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (term79 A t x) = False.
Proof. exact (prop_ext (fun h3 : term79 A t x => @lem3263423 A t x h1 h2) (fun h3 : False => @lem3263095 A t x h1)). Qed.
Lemma lem3263425 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3263424 A t x h1 h2) (@lem3263095 A t x h1)). Qed.
Lemma lem3263426 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263292 A t s u x h1 h2) (fun h3 : False => @lem3263091 A s x h1)). Qed.
Lemma lem3263427 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263426 A t s u x h1 h2) (@lem3263091 A s x h1)). Qed.
Lemma lem3263428 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3263269 A t x h1 h2) (fun h3 : False => @lem3263083 A t x h2)). Qed.
Lemma lem3263429 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3263428 A t x h1 h2) (@lem3263083 A t x h2)). Qed.
Lemma lem3263430 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (term79 A t x) = False.
Proof. exact (prop_ext (fun h3 : term79 A t x => @lem3263429 A t x h1 h2) (fun h3 : False => @lem3263079 A t x h1)). Qed.
Lemma lem3263431 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3263430 A t x h1 h2) (@lem3263079 A t x h1)). Qed.
Lemma lem3263432 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263246 A t s u x h1 h2) (fun h3 : False => @lem3263075 A s x h1)). Qed.
Lemma lem3263433 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263432 A t s u x h1 h2) (@lem3263075 A s x h1)). Qed.
Lemma lem3263434 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263433 A t s u x h1 h2) (fun h3 : False => @lem3263073 A s x h1)). Qed.
Lemma lem3263435 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263434 A t s u x h1 h2) (@lem3263073 A s x h1)). Qed.
Lemma lem3263436 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263200 A s u x h1 h2) (fun h3 : False => @lem3263059 A s x h1)). Qed.
Lemma lem3263437 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s u x) : False.
Proof. exact (EQ_MP (@lem3263436 A s u x h1 h2) (@lem3263059 A s x h1)). Qed.
Lemma lem3263438 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263154 A s t x h1 h2) (fun h3 : False => @lem3263045 A s x h1)). Qed.
Lemma lem3263439 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s t x) : False.
Proof. exact (EQ_MP (@lem3263438 A s t x h1 h2) (@lem3263045 A s x h1)). Qed.
Lemma lem3263440 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem3263411 A u x h1 h2) (fun h3 : False => @lem3263035 A u x h2)). Qed.
Lemma lem3263441 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3263440 A u x h1 h2) (@lem3263035 A u x h2)). Qed.
Lemma lem3263442 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (term79 A u x) = False.
Proof. exact (prop_ext (fun h3 : term79 A u x => @lem3263441 A u x h1 h2) (fun h3 : False => @lem3263031 A u x h1)). Qed.
Lemma lem3263443 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3263442 A u x h1 h2) (@lem3263031 A u x h1)). Qed.
Lemma lem3263444 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem3263415 A u x h1 h2) (fun h3 : False => @lem3263019 A u x h2)). Qed.
Lemma lem3263445 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3263444 A u x h1 h2) (@lem3263019 A u x h2)). Qed.
Lemma lem3263446 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (term79 A u x) = False.
Proof. exact (prop_ext (fun h3 : term79 A u x => @lem3263445 A u x h1 h2) (fun h3 : False => @lem3263015 A u x h1)). Qed.
Lemma lem3263447 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3263446 A u x h1 h2) (@lem3263015 A u x h1)). Qed.
Lemma lem3263448 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263417 A t s u x h1 h2) (fun h3 : False => @lem3263003 A s x h1)). Qed.
Lemma lem3263449 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263448 A t s u x h1 h2) (@lem3263003 A s x h1)). Qed.
Lemma lem3263450 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263421 A t s u x h1 h2) (fun h3 : False => @lem3262991 A s x h1)). Qed.
Lemma lem3263451 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263450 A t s u x h1 h2) (@lem3262991 A s x h1)). Qed.
Lemma lem3263452 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263451 A t s u x h1 h2) (fun h3 : False => @lem3262987 A s x h1)). Qed.
Lemma lem3263453 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263452 A t s u x h1 h2) (@lem3262987 A s x h1)). Qed.
Lemma lem3263454 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3263425 A t x h1 h2) (fun h3 : False => @lem3262975 A t x h2)). Qed.
Lemma lem3263455 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3263454 A t x h1 h2) (@lem3262975 A t x h2)). Qed.
Lemma lem3263456 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (term79 A t x) = False.
Proof. exact (prop_ext (fun h3 : term79 A t x => @lem3263455 A t x h1 h2) (fun h3 : False => @lem3262967 A t x h1)). Qed.
Lemma lem3263457 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3263456 A t x h1 h2) (@lem3262967 A t x h1)). Qed.
Lemma lem3263458 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263427 A t s u x h1 h2) (fun h3 : False => @lem3262959 A s x h1)). Qed.
Lemma lem3263459 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263458 A t s u x h1 h2) (@lem3262959 A s x h1)). Qed.
Lemma lem3263460 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3263431 A t x h1 h2) (fun h3 : False => @lem3262943 A t x h2)). Qed.
Lemma lem3263461 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3263460 A t x h1 h2) (@lem3262943 A t x h2)). Qed.
Lemma lem3263462 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (term79 A t x) = False.
Proof. exact (prop_ext (fun h3 : term79 A t x => @lem3263461 A t x h1 h2) (fun h3 : False => @lem3262935 A t x h1)). Qed.
Lemma lem3263463 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3263462 A t x h1 h2) (@lem3262935 A t x h1)). Qed.
Lemma lem3263464 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263435 A t s u x h1 h2) (fun h3 : False => @lem3262927 A s x h1)). Qed.
Lemma lem3263465 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263464 A t s u x h1 h2) (@lem3262927 A s x h1)). Qed.
Lemma lem3263466 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263465 A t s u x h1 h2) (fun h3 : False => @lem3262923 A s x h1)). Qed.
Lemma lem3263467 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263466 A t s u x h1 h2) (@lem3262923 A s x h1)). Qed.
Lemma lem3263468 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263437 A s u x h1 h2) (fun h3 : False => @lem3262895 A s x h1)). Qed.
Lemma lem3263469 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s u x) : False.
Proof. exact (EQ_MP (@lem3263468 A s u x h1 h2) (@lem3262895 A s x h1)). Qed.
Lemma lem3263470 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263439 A s t x h1 h2) (fun h3 : False => @lem3262867 A s x h1)). Qed.
Lemma lem3263471 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s t x) : False.
Proof. exact (EQ_MP (@lem3263470 A s t x h1 h2) (@lem3262867 A s x h1)). Qed.
Lemma lem3263472 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem3263443 A u x h1 h2) (fun h3 : False => @lem3263035 A u x h2)). Qed.
Lemma lem3263473 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3263472 A u x h1 h2) (@lem3263035 A u x h2)). Qed.
Lemma lem3263474 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (term79 A u x) = False.
Proof. exact (prop_ext (fun h3 : term79 A u x => @lem3263473 A u x h1 h2) (fun h3 : False => @lem3263031 A u x h1)). Qed.
Lemma lem3263475 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3263474 A u x h1 h2) (@lem3263031 A u x h1)). Qed.
Lemma lem3263476 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (u x) = False.
Proof. exact (prop_ext (fun h3 : u x => @lem3263447 A u x h1 h2) (fun h3 : False => @lem3263019 A u x h2)). Qed.
Lemma lem3263477 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3263476 A u x h1 h2) (@lem3263019 A u x h2)). Qed.
Lemma lem3263478 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : (term79 A u x) = False.
Proof. exact (prop_ext (fun h3 : term79 A u x => @lem3263477 A u x h1 h2) (fun h3 : False => @lem3263015 A u x h1)). Qed.
Lemma lem3263479 {A : Type'} (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) : False.
Proof. exact (EQ_MP (@lem3263478 A u x h1 h2) (@lem3263015 A u x h1)). Qed.
Lemma lem3263480 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263449 A t s u x h1 h2) (fun h3 : False => @lem3263003 A s x h1)). Qed.
Lemma lem3263481 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263480 A t s u x h1 h2) (@lem3263003 A s x h1)). Qed.
Lemma lem3263482 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263453 A t s u x h1 h2) (fun h3 : False => @lem3262991 A s x h1)). Qed.
Lemma lem3263483 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263482 A t s u x h1 h2) (@lem3262991 A s x h1)). Qed.
Lemma lem3263484 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263483 A t s u x h1 h2) (fun h3 : False => @lem3262987 A s x h1)). Qed.
Lemma lem3263485 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263484 A t s u x h1 h2) (@lem3262987 A s x h1)). Qed.
Lemma lem3263486 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3263457 A t x h1 h2) (fun h3 : False => @lem3262975 A t x h2)). Qed.
Lemma lem3263487 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3263486 A t x h1 h2) (@lem3262975 A t x h2)). Qed.
Lemma lem3263488 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (term79 A t x) = False.
Proof. exact (prop_ext (fun h3 : term79 A t x => @lem3263487 A t x h1 h2) (fun h3 : False => @lem3262967 A t x h1)). Qed.
Lemma lem3263489 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3263488 A t x h1 h2) (@lem3262967 A t x h1)). Qed.
Lemma lem3263490 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263459 A t s u x h1 h2) (fun h3 : False => @lem3262959 A s x h1)). Qed.
Lemma lem3263491 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263490 A t s u x h1 h2) (@lem3262959 A s x h1)). Qed.
Lemma lem3263492 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3263463 A t x h1 h2) (fun h3 : False => @lem3262943 A t x h2)). Qed.
Lemma lem3263493 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3263492 A t x h1 h2) (@lem3262943 A t x h2)). Qed.
Lemma lem3263494 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : (term79 A t x) = False.
Proof. exact (prop_ext (fun h3 : term79 A t x => @lem3263493 A t x h1 h2) (fun h3 : False => @lem3262935 A t x h1)). Qed.
Lemma lem3263495 {A : Type'} (t : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3263494 A t x h1 h2) (@lem3262935 A t x h1)). Qed.
Lemma lem3263496 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263467 A t s u x h1 h2) (fun h3 : False => @lem3262927 A s x h1)). Qed.
Lemma lem3263497 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263496 A t s u x h1 h2) (@lem3262927 A s x h1)). Qed.
Lemma lem3263498 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263497 A t s u x h1 h2) (fun h3 : False => @lem3262923 A s x h1)). Qed.
Lemma lem3263499 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263498 A t s u x h1 h2) (@lem3262923 A s x h1)). Qed.
Lemma lem3263500 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s u x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263469 A s u x h1 h2) (fun h3 : False => @lem3262895 A s x h1)). Qed.
Lemma lem3263501 {A : Type'} (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s u x) : False.
Proof. exact (EQ_MP (@lem3263500 A s u x h1 h2) (@lem3262895 A s x h1)). Qed.
Lemma lem3263502 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s t x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3263471 A s t x h1 h2) (fun h3 : False => @lem3262867 A s x h1)). Qed.
Lemma lem3263503 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term62 A s t x) : False.
Proof. exact (EQ_MP (@lem3263502 A s t x h1 h2) (@lem3262867 A s x h1)). Qed.
Lemma lem3263504 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : u x) (h3 : term71 A t s u x) : False.
Proof. exact (or_elim (@lem3262839 A t s u x h3) (fun h0 : s x => @lem3263479 A u x h1 h2) (fun h0 : t x => @lem3263475 A u x h1 h2)). Qed.
Lemma lem3263505 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : s x) (h2 : term71 A t s u x) : False.
Proof. exact (or_elim (@lem3262839 A t s u x h2) (fun h0 : s x => @lem3263485 A t s u x h1 h2) (fun h0 : t x => @lem3263481 A t s u x h1 h2)). Qed.
Lemma lem3263506 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A u x) (h2 : term71 A t s u x) : False.
Proof. exact (or_elim (@lem3262838 A t s u x h2) (fun h0 : s x => @lem3263505 A t s u x h0 h2) (fun h0 : u x => @lem3263504 A t s u x h1 h0 h2)). Qed.
Lemma lem3263507 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : term71 A t s u x) : False.
Proof. exact (or_elim (@lem3262839 A t s u x h2) (fun h0 : s x => @lem3263491 A t s u x h0 h2) (fun h0 : t x => @lem3263489 A t x h1 h0)). Qed.
Lemma lem3263508 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : term71 A t s u x) : False.
Proof. exact (or_elim (@lem3262839 A t s u x h2) (fun h0 : s x => @lem3263499 A t s u x h0 h2) (fun h0 : t x => @lem3263495 A t x h1 h0)). Qed.
Lemma lem3263509 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term79 A t x) (h2 : term71 A t s u x) : False.
Proof. exact (or_elim (@lem3262838 A t s u x h2) (fun h0 : s x => @lem3263508 A t s u x h1 h2) (fun h0 : u x => @lem3263507 A t s u x h1 h2)). Qed.
Lemma lem3263510 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term71 A t s u x) : False.
Proof. exact (or_elim (@lem3262840 A t s u x h1) (fun h0 : term79 A t x => @lem3263509 A t s u x h0 h1) (fun h0 : term79 A u x => @lem3263506 A t s u x h0 h1)). Qed.
Lemma lem3263511 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term62 A s u x) (h2 : term74 A t s u x) : False.
Proof. exact (or_elim (@lem3262821 A t s u x h2) (fun h0 : s x => @lem3263501 A s u x h0 h1) (fun h0 : term26 A t u x => @lem3263223 A s t u x h1 h0)). Qed.
Lemma lem3263512 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term62 A s t x) (h2 : term74 A t s u x) : False.
Proof. exact (or_elim (@lem3262821 A t s u x h2) (fun h0 : s x => @lem3263503 A s t x h0 h1) (fun h0 : term26 A t u x => @lem3263177 A s t u x h1 h0)). Qed.
Lemma lem3263513 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term74 A t s u x) : False.
Proof. exact (or_elim (@lem3262820 A t s u x h1) (fun h0 : term62 A s t x => @lem3263512 A t s u x h0 h1) (fun h0 : term62 A s u x => @lem3263511 A t s u x h0 h1)). Qed.
Lemma lem3263514 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term54 A t s u x) : False.
Proof. exact (or_elim (@lem3262817 A t s u x h1) (fun h0 : term74 A t s u x => @lem3263513 A t s u x h0) (fun h0 : term71 A t s u x => @lem3263510 A t s u x h0)). Qed.
Lemma lem3263515 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term54 A t s u x) : (term54 A t s u x) = False.
Proof. exact (prop_ext (fun h2 : term54 A t s u x => @lem3263514 A t s u x h1) (fun h2 : False => @lem3262651 A t s u x h1)). Qed.
Lemma lem3263516 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) (h1 : term54 A t s u x) : False.
Proof. exact (EQ_MP (@lem3263515 A t s u x h1) (@lem3262651 A t s u x h1)). Qed.
Lemma lem3263517 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : term53 A t s u x.
Proof. exact (fun h0 : term54 A t s u x => @lem3263516 A t s u x h0). Qed.
Lemma lem3263518 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) (x : A) : (term27 A s t u x) = (term35 A t s u x).
Proof. exact (EQ_MP (@lem3262650 A t s u x) (@lem3263517 A t s u x)). Qed.
Lemma lem3263523 {A : Type'} (t : A -> Prop) (s : A -> Prop) (u : A -> Prop) : term38 A t s u.
Proof. exact (fun x : A => @lem3263518 A t s u x). Qed.
Lemma lem3263528 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term40 A t s.
Proof. exact (fun u : A -> Prop => @lem3263523 A t s u). Qed.
Lemma lem3263533 {A : Type'} (s : A -> Prop) : term42 A s.
Proof. exact (fun t : A -> Prop => @lem3263528 A t s). Qed.
Lemma lem3263538 {A : Type'} : term44 A.
Proof. exact (fun s : A -> Prop => @lem3263533 A s). Qed.
Lemma lem3263539 {A : Type'} : term46 A.
Proof. exact (EQ_MP (@lem3262646 A) (@lem3263538 A)). Qed.
Lemma lem3263541 {A : Type'} : term46 A.
Proof. exact (@lem3262534 A (@lem3263539 A)). Qed.
Lemma lem3263542 {A : Type'} (h1 : term47 A) : False.
Proof. exact (@lem3263541 A (@lem3262518 A h1)). Qed.
Lemma lem3263543 {A : Type'} (h1 : term47 A) : (term47 A) = False.
Proof. exact (prop_ext (fun h2 : term47 A => @lem3263542 A h1) (fun h2 : False => @lem3262518 A h1)). Qed.
Lemma lem3263544 {A : Type'} (h1 : term47 A) : False.
Proof. exact (EQ_MP (@lem3263543 A h1) (@lem3262518 A h1)). Qed.
Lemma lem3263545 {A : Type'} : term46 A.
Proof. exact (fun h0 : term47 A => @lem3263544 A h0). Qed.
Lemma lem3263546 {A : Type'} : term44 A.
Proof. exact (EQ_MP (@lem3262517 A) (@lem3263545 A)). Qed.
Lemma lem3263547 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem3262513 A) (@lem3263546 A)). Qed.
Lemma lem3263548 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3262374 A) (@lem3263547 A)). Qed.
