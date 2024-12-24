Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_COMM_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3255367 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3255368 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3255367 A s t). Qed.
Lemma lem3255369 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((@INTER A s t) = (@INTER A t s)) = (term1 A t s).
Proof. exact (@lem3255368 A (@INTER A s t) (@INTER A t s)). Qed.
Lemma lem3255378 {A : Type'} (s : A -> Prop) : (term2 A s) = (term3 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3255369 A t s)). Qed.
Lemma lem3255379 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3255380 {A : Type'} (s : A -> Prop) : (term4 A s) = (term5 A s).
Proof. exact (MK_COMB (@lem3255379 A) (@lem3255378 A s)). Qed.
Lemma lem3255385 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3255380 A s)). Qed.
Lemma lem3255386 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3255387 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (MK_COMB (@lem3255386 A) (@lem3255385 A)). Qed.
Lemma lem3255392 {A : Type'} : (term9 A) = (term8 A).
Proof. exact (SYM (@lem3255387 A)). Qed.
Lemma lem3255408 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A x s t) = (term11 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3255409 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A x s t) = (term11 A s x t).
Proof. exact (@lem3255408 A s x t). Qed.
Lemma lem3255413 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3255414 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3255413 A P x). Qed.
Lemma lem3255415 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3255414 A s x). Qed.
Lemma lem3255416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3255417 {A : Type'} (s : A -> Prop) (x : A) : (term12 A x s) = (term13 A s x).
Proof. exact (MK_COMB (@lem3255416) (@lem3255415 A s x)). Qed.
Lemma lem3255419 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3255420 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3255419 A P x). Qed.
Lemma lem3255421 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3255420 A t x). Qed.
Lemma lem3255422 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term11 A s x t) = (term14 A s t x).
Proof. exact (MK_COMB (@lem3255417 A s x) (@lem3255421 A t x)). Qed.
Lemma lem3255425 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term10 A x s t) = (term14 A s t x).
Proof. exact (TRANS (@lem3255409 A s x t) (@lem3255422 A s t x)). Qed.
Lemma lem3255426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3255427 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term15 A x s t) = (term16 A s t x).
Proof. exact (MK_COMB (@lem3255426) (@lem3255425 A s t x)). Qed.
Lemma lem3255429 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A x s t) = (term11 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3255430 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term10 A x s t) = (term11 A s x t).
Proof. exact (@lem3255429 A s x t). Qed.
Lemma lem3255431 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term10 A x t s) = (term11 A t x s).
Proof. exact (@lem3255430 A t x s). Qed.
Lemma lem3255435 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3255436 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3255435 A P x). Qed.
Lemma lem3255437 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3255436 A t x). Qed.
Lemma lem3255438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3255439 {A : Type'} (t : A -> Prop) (x : A) : (term12 A x t) = (term13 A t x).
Proof. exact (MK_COMB (@lem3255438) (@lem3255437 A t x)). Qed.
Lemma lem3255441 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3255442 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3255441 A P x). Qed.
Lemma lem3255443 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3255442 A s x). Qed.
Lemma lem3255444 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term11 A t x s) = (term14 A t s x).
Proof. exact (MK_COMB (@lem3255439 A t x) (@lem3255443 A s x)). Qed.
Lemma lem3255447 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term10 A x t s) = (term14 A t s x).
Proof. exact (TRANS (@lem3255431 A t x s) (@lem3255444 A t s x)). Qed.
Lemma lem3255448 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((term10 A x s t) = (term10 A x t s)) = ((term14 A s t x) = (term14 A t s x)).
Proof. exact (MK_COMB (@lem3255427 A s t x) (@lem3255447 A t s x)). Qed.
Lemma lem3255451 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term17 A t s) = (term18 A t s).
Proof. exact (fun_ext (fun x : A => @lem3255448 A t s x)). Qed.
Lemma lem3255452 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3255453 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term1 A t s) = (term19 A t s).
Proof. exact (MK_COMB (@lem3255452 A) (@lem3255451 A t s)). Qed.
Lemma lem3255458 {A : Type'} (s : A -> Prop) : (term3 A s) = (term20 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3255453 A t s)). Qed.
Lemma lem3255459 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3255460 {A : Type'} (s : A -> Prop) : (term5 A s) = (term21 A s).
Proof. exact (MK_COMB (@lem3255459 A) (@lem3255458 A s)). Qed.
Lemma lem3255465 {A : Type'} : (term7 A) = (term22 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3255460 A s)). Qed.
Lemma lem3255466 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3255467 {A : Type'} : (term9 A) = (term23 A).
Proof. exact (MK_COMB (@lem3255466 A) (@lem3255465 A)). Qed.
Lemma lem3255472 {A : Type'} : (term23 A) = (term9 A).
Proof. exact (SYM (@lem3255467 A)). Qed.
Lemma lem3255474 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3255475 {A : Type'} : (term23 A) = (term25 A).
Proof. exact (@lem3255474 (term23 A)). Qed.
Lemma lem3255476 {A : Type'} : (term25 A) = (term23 A).
Proof. exact (SYM (@lem3255475 A)). Qed.
Lemma lem3255477 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem3255480 {A : Type'} (h1 : term25 A) : term25 A.
Proof. exact (h1). Qed.
Lemma lem3255481 {A : Type'} : term27 A.
Proof. exact (fun h0 : term25 A => @lem3255480 A h0). Qed.
Lemma lem3255482 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (h1). Qed.
Lemma lem3255483 {A : Type'} (h1 : term25 A) : term25 A.
Proof. exact (h1). Qed.
Lemma lem3255484 {A : Type'} (h1 : term25 A) (h2 : term27 A) : term25 A.
Proof. exact (@lem3255482 A h2 (@lem3255483 A h1)). Qed.
Lemma lem3255485 {A : Type'} (h1 : term25 A) : term28 A.
Proof. exact (fun h0 : term27 A => @lem3255484 A h1 h0). Qed.
Lemma lem3255486 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (h1). Qed.
Lemma lem3255487 {A : Type'} (h1 : term25 A) (h2 : term27 A) : term25 A.
Proof. exact (@lem3255485 A h1 (@lem3255486 A h2)). Qed.
Lemma lem3255488 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (fun h0 : term25 A => @lem3255487 A h0 h1). Qed.
Lemma lem3255489 {A : Type'} : term29 A.
Proof. exact (fun h0 : term27 A => @lem3255488 A h0). Qed.
Lemma lem3255492 {A : Type'} : term27 A.
Proof. exact (@lem3255489 A (@lem3255481 A)). Qed.
Lemma lem3255493 {A : Type'} : term27 A.
Proof. exact (@lem3255492 A). Qed.
Lemma lem3255495 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3255496 {A : Type'} : (term25 A) = (term30 A).
Proof. exact (@lem3255495 (term26 A)). Qed.
Lemma lem3255498 (t : Prop) : (term31 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3255499 {A : Type'} : (term30 A) = (term23 A).
Proof. exact (@lem3255498 (term23 A)). Qed.
Lemma lem3255520 {A : Type'} : (term25 A) = (term23 A).
Proof. exact (TRANS (@lem3255496 A) (@lem3255499 A)). Qed.
Lemma lem3255533 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((term14 A s t x) = (term14 A t s x)) = ((term14 A s t x) = (term14 A t s x)).
Proof. exact (eq_refl ((term14 A s t x) = (term14 A t s x))). Qed.
Lemma lem3255534 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term18 A t s) = (term18 A t s).
Proof. exact (fun_ext (fun x : A => @lem3255533 A t s x)). Qed.
Lemma lem3255535 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3255536 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term19 A t s) = (term19 A t s).
Proof. exact (MK_COMB (@lem3255535 A) (@lem3255534 A t s)). Qed.
Lemma lem3255537 {A : Type'} (s : A -> Prop) : (term20 A s) = (term20 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3255536 A t s)). Qed.
Lemma lem3255538 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3255539 {A : Type'} (s : A -> Prop) : (term21 A s) = (term21 A s).
Proof. exact (MK_COMB (@lem3255538 A) (@lem3255537 A s)). Qed.
Lemma lem3255540 {A : Type'} : (term22 A) = (term22 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3255539 A s)). Qed.
Lemma lem3255541 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3255542 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (MK_COMB (@lem3255541 A) (@lem3255540 A)). Qed.
Lemma lem3255567 {A : Type'} : (term25 A) = (term23 A).
Proof. exact (TRANS (@lem3255520 A) (@lem3255542 A)). Qed.
Lemma lem3255568 {A : Type'} : (term23 A) = (term25 A).
Proof. exact (SYM (@lem3255567 A)). Qed.
Lemma lem3255570 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3255571 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : ((term14 A s t x) = (term14 A t s x)) = (term32 A t s x).
Proof. exact (@lem3255570 ((term14 A s t x) = (term14 A t s x))). Qed.
Lemma lem3255572 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term32 A t s x) = ((term14 A s t x) = (term14 A t s x)).
Proof. exact (SYM (@lem3255571 A t s x)). Qed.
Lemma lem3255573 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term33 A t s x) : term33 A t s x.
Proof. exact (h1). Qed.
Lemma lem3255582 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term34 A s t x) = (term35 A s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem3255594 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term34 A t s x) = (term35 A t s x).
Proof. exact (@lem17045 (t x) (s x)). Qed.
Lemma lem3255597 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term14 A t s x) = (term14 A t s x).
Proof. exact (eq_refl (term14 A t s x)). Qed.
Lemma lem3255598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3255599 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term36 A s t x) = (term37 A s t x).
Proof. exact (MK_COMB (@lem3255598) (@lem3255582 A s t x)). Qed.
Lemma lem3255600 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term38 A t s x) = (term39 A t s x).
Proof. exact (MK_COMB (@lem3255599 A s t x) (@lem3255597 A t s x)). Qed.
Lemma lem3255602 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term40 A s t x) = (term40 A s t x).
Proof. exact (eq_refl (term40 A s t x)). Qed.
Lemma lem3255603 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term41 A t s x) = (term42 A t s x).
Proof. exact (MK_COMB (@lem3255602 A s t x) (@lem3255594 A t s x)). Qed.
Lemma lem3255604 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3255605 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term43 A t s x) = (term44 A t s x).
Proof. exact (MK_COMB (@lem3255604) (@lem3255603 A t s x)). Qed.
Lemma lem3255606 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term45 A t s x) = (term46 A t s x).
Proof. exact (MK_COMB (@lem3255605 A t s x) (@lem3255600 A t s x)). Qed.
Lemma lem3255607 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term33 A t s x) = (term45 A t s x).
Proof. exact (@lem17646 (term14 A s t x) (term14 A t s x)). Qed.
Lemma lem3255612 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term33 A t s x) = (term46 A t s x).
Proof. exact (TRANS (@lem3255607 A t s x) (@lem3255606 A t s x)). Qed.
Lemma lem3255667 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term33 A t s x) : term46 A t s x.
Proof. exact (EQ_MP (@lem3255612 A t s x) (@lem3255573 A t s x h1)). Qed.
Lemma lem3255668 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : term42 A t s x.
Proof. exact (h1). Qed.
Lemma lem3255669 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : term39 A t s x.
Proof. exact (h1). Qed.
Lemma lem3255670 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : term35 A t s x.
Proof. exact (proj2 (@lem3255668 A t s x h1)). Qed.
Lemma lem3255671 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : term14 A s t x.
Proof. exact (proj1 (@lem3255668 A t s x h1)). Qed.
Lemma lem3255676 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : term14 A t s x.
Proof. exact (proj2 (@lem3255669 A t s x h1)). Qed.
Lemma lem3255677 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : term35 A s t x.
Proof. exact (proj1 (@lem3255669 A t s x h1)). Qed.
Lemma lem3255693 {A : Type'} (t : A -> Prop) (x : A) (h1 : term47 A t x) : term47 A t x.
Proof. exact (h1). Qed.
Lemma lem3255705 {A : Type'} (s : A -> Prop) (x : A) (h1 : term47 A s x) : term47 A s x.
Proof. exact (h1). Qed.
Lemma lem3255717 {A : Type'} (s : A -> Prop) (x : A) (h1 : term47 A s x) : term47 A s x.
Proof. exact (h1). Qed.
Lemma lem3255729 {A : Type'} (t : A -> Prop) (x : A) (h1 : term47 A t x) : term47 A t x.
Proof. exact (h1). Qed.
Lemma lem3255735 {A : Type'} (t : A -> Prop) (x : A) (h1 : term47 A t x) : term47 A t x.
Proof. exact (h1). Qed.
Lemma lem3255741 {A : Type'} (s : A -> Prop) (x : A) (h1 : term47 A s x) : term47 A s x.
Proof. exact (h1). Qed.
Lemma lem3255747 {A : Type'} (s : A -> Prop) (x : A) (h1 : term47 A s x) : term47 A s x.
Proof. exact (h1). Qed.
Lemma lem3255753 {A : Type'} (t : A -> Prop) (x : A) (h1 : term47 A t x) : term47 A t x.
Proof. exact (h1). Qed.
Lemma lem3255755 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : t x.
Proof. exact (proj2 (@lem3255671 A t s x h1)). Qed.
Lemma lem3255756 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : term48 A t x.
Proof. exact (fun h0 : term47 A t x => @lem3255755 A t s x h1). Qed.
Lemma lem3255758 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255759 {A : Type'} (t : A -> Prop) (x : A) : (term48 A t x) = (t x).
Proof. exact (@lem3255758 (t x)). Qed.
Lemma lem3255760 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : t x.
Proof. exact (EQ_MP (@lem3255759 A t x) (@lem3255756 A t s x h1)). Qed.
Lemma lem3255763 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3255765 {A : Type'} (t : A -> Prop) (x : A) : (term47 A t x) = (term50 A t x).
Proof. exact (@lem3255763 (t x)). Qed.
Lemma lem3255768 {A : Type'} (t : A -> Prop) (x : A) (h1 : term47 A t x) : term50 A t x.
Proof. exact (EQ_MP (@lem3255765 A t x) (@lem3255735 A t x h1)). Qed.
Lemma lem3255771 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term42 A t s x) : False.
Proof. exact (@lem3255768 A t x h1 (@lem3255760 A t s x h2)). Qed.
Lemma lem3255772 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term42 A t s x) : term51.
Proof. exact (fun h0 : ~ False => @lem3255771 A t s x h1 h2). Qed.
Lemma lem3255774 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255775 : term51 = False.
Proof. exact (@lem3255774 False). Qed.
Lemma lem3255776 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term42 A t s x) : False.
Proof. exact (EQ_MP (@lem3255775) (@lem3255772 A t s x h1 h2)). Qed.
Lemma lem3255778 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : s x.
Proof. exact (proj1 (@lem3255671 A t s x h1)). Qed.
Lemma lem3255779 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : term48 A s x.
Proof. exact (fun h0 : term47 A s x => @lem3255778 A t s x h1). Qed.
Lemma lem3255781 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255782 {A : Type'} (s : A -> Prop) (x : A) : (term48 A s x) = (s x).
Proof. exact (@lem3255781 (s x)). Qed.
Lemma lem3255783 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : s x.
Proof. exact (EQ_MP (@lem3255782 A s x) (@lem3255779 A t s x h1)). Qed.
Lemma lem3255786 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3255788 {A : Type'} (s : A -> Prop) (x : A) : (term47 A s x) = (term50 A s x).
Proof. exact (@lem3255786 (s x)). Qed.
Lemma lem3255791 {A : Type'} (s : A -> Prop) (x : A) (h1 : term47 A s x) : term50 A s x.
Proof. exact (EQ_MP (@lem3255788 A s x) (@lem3255741 A s x h1)). Qed.
Lemma lem3255794 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term42 A t s x) : False.
Proof. exact (@lem3255791 A s x h1 (@lem3255783 A t s x h2)). Qed.
Lemma lem3255795 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term42 A t s x) : term51.
Proof. exact (fun h0 : ~ False => @lem3255794 A t s x h1 h2). Qed.
Lemma lem3255797 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255798 : term51 = False.
Proof. exact (@lem3255797 False). Qed.
Lemma lem3255799 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term42 A t s x) : False.
Proof. exact (EQ_MP (@lem3255798) (@lem3255795 A t s x h1 h2)). Qed.
Lemma lem3255801 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : s x.
Proof. exact (proj2 (@lem3255676 A t s x h1)). Qed.
Lemma lem3255802 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : term48 A s x.
Proof. exact (fun h0 : term47 A s x => @lem3255801 A t s x h1). Qed.
Lemma lem3255804 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255805 {A : Type'} (s : A -> Prop) (x : A) : (term48 A s x) = (s x).
Proof. exact (@lem3255804 (s x)). Qed.
Lemma lem3255806 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : s x.
Proof. exact (EQ_MP (@lem3255805 A s x) (@lem3255802 A t s x h1)). Qed.
Lemma lem3255809 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3255811 {A : Type'} (s : A -> Prop) (x : A) : (term47 A s x) = (term50 A s x).
Proof. exact (@lem3255809 (s x)). Qed.
Lemma lem3255814 {A : Type'} (s : A -> Prop) (x : A) (h1 : term47 A s x) : term50 A s x.
Proof. exact (EQ_MP (@lem3255811 A s x) (@lem3255747 A s x h1)). Qed.
Lemma lem3255817 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term39 A t s x) : False.
Proof. exact (@lem3255814 A s x h1 (@lem3255806 A t s x h2)). Qed.
Lemma lem3255818 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term39 A t s x) : term51.
Proof. exact (fun h0 : ~ False => @lem3255817 A t s x h1 h2). Qed.
Lemma lem3255820 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255821 : term51 = False.
Proof. exact (@lem3255820 False). Qed.
Lemma lem3255822 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term39 A t s x) : False.
Proof. exact (EQ_MP (@lem3255821) (@lem3255818 A t s x h1 h2)). Qed.
Lemma lem3255824 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : t x.
Proof. exact (proj1 (@lem3255676 A t s x h1)). Qed.
Lemma lem3255825 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : term48 A t x.
Proof. exact (fun h0 : term47 A t x => @lem3255824 A t s x h1). Qed.
Lemma lem3255827 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255828 {A : Type'} (t : A -> Prop) (x : A) : (term48 A t x) = (t x).
Proof. exact (@lem3255827 (t x)). Qed.
Lemma lem3255829 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : t x.
Proof. exact (EQ_MP (@lem3255828 A t x) (@lem3255825 A t s x h1)). Qed.
Lemma lem3255832 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3255834 {A : Type'} (t : A -> Prop) (x : A) : (term47 A t x) = (term50 A t x).
Proof. exact (@lem3255832 (t x)). Qed.
Lemma lem3255837 {A : Type'} (t : A -> Prop) (x : A) (h1 : term47 A t x) : term50 A t x.
Proof. exact (EQ_MP (@lem3255834 A t x) (@lem3255753 A t x h1)). Qed.
Lemma lem3255840 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term39 A t s x) : False.
Proof. exact (@lem3255837 A t x h1 (@lem3255829 A t s x h2)). Qed.
Lemma lem3255841 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term39 A t s x) : term51.
Proof. exact (fun h0 : ~ False => @lem3255840 A t s x h1 h2). Qed.
Lemma lem3255843 (p : Prop) : (term49 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255844 : term51 = False.
Proof. exact (@lem3255843 False). Qed.
Lemma lem3255845 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term39 A t s x) : False.
Proof. exact (EQ_MP (@lem3255844) (@lem3255841 A t s x h1 h2)). Qed.
Lemma lem3255846 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term39 A t s x) : (term47 A t x) = False.
Proof. exact (prop_ext (fun h3 : term47 A t x => @lem3255845 A t s x h1 h2) (fun h3 : False => @lem3255753 A t x h1)). Qed.
Lemma lem3255847 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term39 A t s x) : False.
Proof. exact (EQ_MP (@lem3255846 A t s x h1 h2) (@lem3255753 A t x h1)). Qed.
Lemma lem3255848 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term39 A t s x) : (term47 A s x) = False.
Proof. exact (prop_ext (fun h3 : term47 A s x => @lem3255822 A t s x h1 h2) (fun h3 : False => @lem3255747 A s x h1)). Qed.
Lemma lem3255849 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term39 A t s x) : False.
Proof. exact (EQ_MP (@lem3255848 A t s x h1 h2) (@lem3255747 A s x h1)). Qed.
Lemma lem3255850 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term42 A t s x) : (term47 A s x) = False.
Proof. exact (prop_ext (fun h3 : term47 A s x => @lem3255799 A t s x h1 h2) (fun h3 : False => @lem3255741 A s x h1)). Qed.
Lemma lem3255851 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term42 A t s x) : False.
Proof. exact (EQ_MP (@lem3255850 A t s x h1 h2) (@lem3255741 A s x h1)). Qed.
Lemma lem3255852 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term42 A t s x) : (term47 A t x) = False.
Proof. exact (prop_ext (fun h3 : term47 A t x => @lem3255776 A t s x h1 h2) (fun h3 : False => @lem3255735 A t x h1)). Qed.
Lemma lem3255853 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term42 A t s x) : False.
Proof. exact (EQ_MP (@lem3255852 A t s x h1 h2) (@lem3255735 A t x h1)). Qed.
Lemma lem3255854 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term39 A t s x) : (term47 A t x) = False.
Proof. exact (prop_ext (fun h3 : term47 A t x => @lem3255847 A t s x h1 h2) (fun h3 : False => @lem3255729 A t x h1)). Qed.
Lemma lem3255855 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term39 A t s x) : False.
Proof. exact (EQ_MP (@lem3255854 A t s x h1 h2) (@lem3255729 A t x h1)). Qed.
Lemma lem3255856 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term39 A t s x) : (term47 A s x) = False.
Proof. exact (prop_ext (fun h3 : term47 A s x => @lem3255849 A t s x h1 h2) (fun h3 : False => @lem3255717 A s x h1)). Qed.
Lemma lem3255857 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term39 A t s x) : False.
Proof. exact (EQ_MP (@lem3255856 A t s x h1 h2) (@lem3255717 A s x h1)). Qed.
Lemma lem3255858 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term42 A t s x) : (term47 A s x) = False.
Proof. exact (prop_ext (fun h3 : term47 A s x => @lem3255851 A t s x h1 h2) (fun h3 : False => @lem3255705 A s x h1)). Qed.
Lemma lem3255859 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term42 A t s x) : False.
Proof. exact (EQ_MP (@lem3255858 A t s x h1 h2) (@lem3255705 A s x h1)). Qed.
Lemma lem3255860 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term42 A t s x) : (term47 A t x) = False.
Proof. exact (prop_ext (fun h3 : term47 A t x => @lem3255853 A t s x h1 h2) (fun h3 : False => @lem3255693 A t x h1)). Qed.
Lemma lem3255861 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term42 A t s x) : False.
Proof. exact (EQ_MP (@lem3255860 A t s x h1 h2) (@lem3255693 A t x h1)). Qed.
Lemma lem3255862 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term39 A t s x) : (term47 A t x) = False.
Proof. exact (prop_ext (fun h3 : term47 A t x => @lem3255855 A t s x h1 h2) (fun h3 : False => @lem3255729 A t x h1)). Qed.
Lemma lem3255863 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term39 A t s x) : False.
Proof. exact (EQ_MP (@lem3255862 A t s x h1 h2) (@lem3255729 A t x h1)). Qed.
Lemma lem3255864 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term39 A t s x) : (term47 A s x) = False.
Proof. exact (prop_ext (fun h3 : term47 A s x => @lem3255857 A t s x h1 h2) (fun h3 : False => @lem3255717 A s x h1)). Qed.
Lemma lem3255865 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term39 A t s x) : False.
Proof. exact (EQ_MP (@lem3255864 A t s x h1 h2) (@lem3255717 A s x h1)). Qed.
Lemma lem3255866 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term42 A t s x) : (term47 A s x) = False.
Proof. exact (prop_ext (fun h3 : term47 A s x => @lem3255859 A t s x h1 h2) (fun h3 : False => @lem3255705 A s x h1)). Qed.
Lemma lem3255867 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A s x) (h2 : term42 A t s x) : False.
Proof. exact (EQ_MP (@lem3255866 A t s x h1 h2) (@lem3255705 A s x h1)). Qed.
Lemma lem3255868 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term42 A t s x) : (term47 A t x) = False.
Proof. exact (prop_ext (fun h3 : term47 A t x => @lem3255861 A t s x h1 h2) (fun h3 : False => @lem3255693 A t x h1)). Qed.
Lemma lem3255869 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term47 A t x) (h2 : term42 A t s x) : False.
Proof. exact (EQ_MP (@lem3255868 A t s x h1 h2) (@lem3255693 A t x h1)). Qed.
Lemma lem3255870 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term39 A t s x) : False.
Proof. exact (or_elim (@lem3255677 A t s x h1) (fun h0 : term47 A s x => @lem3255865 A t s x h0 h1) (fun h0 : term47 A t x => @lem3255863 A t s x h0 h1)). Qed.
Lemma lem3255871 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term42 A t s x) : False.
Proof. exact (or_elim (@lem3255670 A t s x h1) (fun h0 : term47 A t x => @lem3255869 A t s x h0 h1) (fun h0 : term47 A s x => @lem3255867 A t s x h0 h1)). Qed.
Lemma lem3255872 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term33 A t s x) : False.
Proof. exact (or_elim (@lem3255667 A t s x h1) (fun h0 : term42 A t s x => @lem3255871 A t s x h0) (fun h0 : term39 A t s x => @lem3255870 A t s x h0)). Qed.
Lemma lem3255873 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term33 A t s x) : (term33 A t s x) = False.
Proof. exact (prop_ext (fun h2 : term33 A t s x => @lem3255872 A t s x h1) (fun h2 : False => @lem3255573 A t s x h1)). Qed.
Lemma lem3255874 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term33 A t s x) : False.
Proof. exact (EQ_MP (@lem3255873 A t s x h1) (@lem3255573 A t s x h1)). Qed.
Lemma lem3255875 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : term32 A t s x.
Proof. exact (fun h0 : term33 A t s x => @lem3255874 A t s x h0). Qed.
Lemma lem3255876 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term14 A s t x) = (term14 A t s x).
Proof. exact (EQ_MP (@lem3255572 A t s x) (@lem3255875 A t s x)). Qed.
Lemma lem3255881 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term19 A t s.
Proof. exact (fun x : A => @lem3255876 A t s x). Qed.
Lemma lem3255886 {A : Type'} (s : A -> Prop) : term21 A s.
Proof. exact (fun t : A -> Prop => @lem3255881 A t s). Qed.
Lemma lem3255891 {A : Type'} : term23 A.
Proof. exact (fun s : A -> Prop => @lem3255886 A s). Qed.
Lemma lem3255892 {A : Type'} : term25 A.
Proof. exact (EQ_MP (@lem3255568 A) (@lem3255891 A)). Qed.
Lemma lem3255894 {A : Type'} : term25 A.
Proof. exact (@lem3255493 A (@lem3255892 A)). Qed.
Lemma lem3255895 {A : Type'} (h1 : term26 A) : False.
Proof. exact (@lem3255894 A (@lem3255477 A h1)). Qed.
Lemma lem3255896 {A : Type'} (h1 : term26 A) : (term26 A) = False.
Proof. exact (prop_ext (fun h2 : term26 A => @lem3255895 A h1) (fun h2 : False => @lem3255477 A h1)). Qed.
Lemma lem3255897 {A : Type'} (h1 : term26 A) : False.
Proof. exact (EQ_MP (@lem3255896 A h1) (@lem3255477 A h1)). Qed.
Lemma lem3255898 {A : Type'} : term25 A.
Proof. exact (fun h0 : term26 A => @lem3255897 A h0). Qed.
Lemma lem3255899 {A : Type'} : term23 A.
Proof. exact (EQ_MP (@lem3255476 A) (@lem3255898 A)). Qed.
Lemma lem3255900 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem3255472 A) (@lem3255899 A)). Qed.
Lemma lem3255901 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem3255392 A) (@lem3255900 A)). Qed.
