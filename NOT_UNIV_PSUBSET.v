Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_UNIV_PSUBSET_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm1820_spec.
Require Import thm18392_spec.
Require Import thm1855_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211744_spec.
Require Import thm3211745_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Lemma lem3228411 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3228412 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (@lem3228411 A s t). Qed.
Lemma lem3228413 {A : Type'} (s : A -> Prop) : (@PSUBSET A (@UNIV A) s) = (term1 A s).
Proof. exact (@lem3228412 A (@UNIV A) s). Qed.
Lemma lem3228417 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term2 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3228418 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term2 A s t).
Proof. exact (@lem3228417 A s t). Qed.
Lemma lem3228419 {A : Type'} (s : A -> Prop) : (@SUBSET A (@UNIV A) s) = (term3 A s).
Proof. exact (@lem3228418 A (@UNIV A) s). Qed.
Lemma lem3228426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3228427 {A : Type'} (s : A -> Prop) : (term4 A s) = (term5 A s).
Proof. exact (MK_COMB (@lem3228426) (@lem3228419 A s)). Qed.
Lemma lem3228431 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term6 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3228432 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term6 A s t).
Proof. exact (@lem3228431 A s t). Qed.
Lemma lem3228433 {A : Type'} (s : A -> Prop) : ((@UNIV A) = s) = (term7 A s).
Proof. exact (@lem3228432 A (@UNIV A) s). Qed.
Lemma lem3228442 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228443 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (MK_COMB (@lem3228442) (@lem3228433 A s)). Qed.
Lemma lem3228444 {A : Type'} (s : A -> Prop) : (term1 A s) = (term10 A s).
Proof. exact (MK_COMB (@lem3228427 A s) (@lem3228443 A s)). Qed.
Lemma lem3228447 {A : Type'} (s : A -> Prop) : (@PSUBSET A (@UNIV A) s) = (term10 A s).
Proof. exact (TRANS (@lem3228413 A s) (@lem3228444 A s)). Qed.
Lemma lem3228448 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228449 {A : Type'} (s : A -> Prop) : (term11 A s) = (term12 A s).
Proof. exact (MK_COMB (@lem3228448) (@lem3228447 A s)). Qed.
Lemma lem3228450 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3228449 A s)). Qed.
Lemma lem3228451 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3228452 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (MK_COMB (@lem3228451 A) (@lem3228450 A)). Qed.
Lemma lem3228457 {A : Type'} : (term16 A) = (term15 A).
Proof. exact (SYM (@lem3228452 A)). Qed.
Lemma lem3228471 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3228472 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3228471 A x). Qed.
Lemma lem3228473 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3228474 {A : Type'} (x : A) : (term17 A x) = (imp True).
Proof. exact (MK_COMB (@lem3228473) (@lem3228472 A x)). Qed.
Lemma lem3228476 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3228477 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3228476 A P x). Qed.
Lemma lem3228478 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3228477 A s x). Qed.
Lemma lem3228479 {A : Type'} (s : A -> Prop) (x : A) : (term18 A x s) = (term19 A s x).
Proof. exact (MK_COMB (@lem3228474 A x) (@lem3228478 A s x)). Qed.
Lemma lem3228481 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem3228482 {A : Type'} (s : A -> Prop) (x : A) : (term19 A s x) = (s x).
Proof. exact (@lem3228481 (s x)). Qed.
Lemma lem3228483 {A : Type'} (s : A -> Prop) (x : A) : (term18 A x s) = (s x).
Proof. exact (TRANS (@lem3228479 A s x) (@lem3228482 A s x)). Qed.
Lemma lem3228484 {A : Type'} (s : A -> Prop) : (term20 A s) = (term21 A s).
Proof. exact (fun_ext (fun x : A => @lem3228483 A s x)). Qed.
Lemma lem3228485 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228486 {A : Type'} (s : A -> Prop) : (term3 A s) = (term22 A s).
Proof. exact (MK_COMB (@lem3228485 A) (@lem3228484 A s)). Qed.
Lemma lem3228491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3228492 {A : Type'} (s : A -> Prop) : (term5 A s) = (term23 A s).
Proof. exact (MK_COMB (@lem3228491) (@lem3228486 A s)). Qed.
Lemma lem3228500 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3228501 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3228500 A x). Qed.
Lemma lem3228502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3228503 {A : Type'} (x : A) : (term24 A x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem3228502) (@lem3228501 A x)). Qed.
Lemma lem3228505 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3228506 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3228505 A P x). Qed.
Lemma lem3228507 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3228506 A s x). Qed.
Lemma lem3228508 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x (@UNIV A)) = (@IN A x s)) = (True = (s x)).
Proof. exact (MK_COMB (@lem3228503 A x) (@lem3228507 A s x)). Qed.
Lemma lem3228510 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem3228511 {A : Type'} (s : A -> Prop) (x : A) : (True = (s x)) = (s x).
Proof. exact (@lem3228510 (s x)). Qed.
Lemma lem3228512 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x (@UNIV A)) = (@IN A x s)) = (s x).
Proof. exact (TRANS (@lem3228508 A s x) (@lem3228511 A s x)). Qed.
Lemma lem3228513 {A : Type'} (s : A -> Prop) : (term25 A s) = (term21 A s).
Proof. exact (fun_ext (fun x : A => @lem3228512 A s x)). Qed.
Lemma lem3228514 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228515 {A : Type'} (s : A -> Prop) : (term7 A s) = (term22 A s).
Proof. exact (MK_COMB (@lem3228514 A) (@lem3228513 A s)). Qed.
Lemma lem3228520 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228521 {A : Type'} (s : A -> Prop) : (term9 A s) = (term26 A s).
Proof. exact (MK_COMB (@lem3228520) (@lem3228515 A s)). Qed.
Lemma lem3228522 {A : Type'} (s : A -> Prop) : (term10 A s) = (term27 A s).
Proof. exact (MK_COMB (@lem3228492 A s) (@lem3228521 A s)). Qed.
Lemma lem3228525 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228526 {A : Type'} (s : A -> Prop) : (term12 A s) = (term28 A s).
Proof. exact (MK_COMB (@lem3228525) (@lem3228522 A s)). Qed.
Lemma lem3228527 {A : Type'} : (term14 A) = (term29 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3228526 A s)). Qed.
Lemma lem3228528 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3228529 {A : Type'} : (term16 A) = (term30 A).
Proof. exact (MK_COMB (@lem3228528 A) (@lem3228527 A)). Qed.
Lemma lem3228534 {A : Type'} : (term30 A) = (term16 A).
Proof. exact (SYM (@lem3228529 A)). Qed.
Lemma lem3228536 (p : Prop) : p = (term31 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3228537 {A : Type'} : (term30 A) = (term32 A).
Proof. exact (@lem3228536 (term30 A)). Qed.
Lemma lem3228538 {A : Type'} : (term32 A) = (term30 A).
Proof. exact (SYM (@lem3228537 A)). Qed.
Lemma lem3228539 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (h1). Qed.
Lemma lem3228542 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem3228543 {A : Type'} : term34 A.
Proof. exact (fun h0 : term32 A => @lem3228542 A h0). Qed.
Lemma lem3228544 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (h1). Qed.
Lemma lem3228545 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem3228546 {A : Type'} (h1 : term32 A) (h2 : term34 A) : term32 A.
Proof. exact (@lem3228544 A h2 (@lem3228545 A h1)). Qed.
Lemma lem3228547 {A : Type'} (h1 : term32 A) : term35 A.
Proof. exact (fun h0 : term34 A => @lem3228546 A h1 h0). Qed.
Lemma lem3228548 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (h1). Qed.
Lemma lem3228549 {A : Type'} (h1 : term32 A) (h2 : term34 A) : term32 A.
Proof. exact (@lem3228547 A h1 (@lem3228548 A h2)). Qed.
Lemma lem3228550 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (fun h0 : term32 A => @lem3228549 A h0 h1). Qed.
Lemma lem3228551 {A : Type'} : term36 A.
Proof. exact (fun h0 : term34 A => @lem3228550 A h0). Qed.
Lemma lem3228554 {A : Type'} : term34 A.
Proof. exact (@lem3228551 A (@lem3228543 A)). Qed.
Lemma lem3228555 {A : Type'} : term34 A.
Proof. exact (@lem3228554 A). Qed.
Lemma lem3228557 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3228558 {A : Type'} : (term32 A) = (term37 A).
Proof. exact (@lem3228557 (term33 A)). Qed.
Lemma lem3228560 (t : Prop) : (term38 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3228561 {A : Type'} : (term37 A) = (term30 A).
Proof. exact (@lem3228560 (term30 A)). Qed.
Lemma lem3228580 {A : Type'} : (term32 A) = (term30 A).
Proof. exact (TRANS (@lem3228558 A) (@lem3228561 A)). Qed.
Lemma lem3228581 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3228582 {A : Type'} (s : A -> Prop) : (term21 A s) = (term21 A s).
Proof. exact (fun_ext (fun x : A => @lem3228581 A s x)). Qed.
Lemma lem3228583 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228584 {A : Type'} (s : A -> Prop) : (term22 A s) = (term22 A s).
Proof. exact (MK_COMB (@lem3228583 A) (@lem3228582 A s)). Qed.
Lemma lem3228585 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228586 {A : Type'} (s : A -> Prop) : (term26 A s) = (term26 A s).
Proof. exact (MK_COMB (@lem3228585) (@lem3228584 A s)). Qed.
Lemma lem3228587 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3228588 {A : Type'} (s : A -> Prop) : (term21 A s) = (term21 A s).
Proof. exact (fun_ext (fun x : A => @lem3228587 A s x)). Qed.
Lemma lem3228589 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228590 {A : Type'} (s : A -> Prop) : (term22 A s) = (term22 A s).
Proof. exact (MK_COMB (@lem3228589 A) (@lem3228588 A s)). Qed.
Lemma lem3228591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3228592 {A : Type'} (s : A -> Prop) : (term23 A s) = (term23 A s).
Proof. exact (MK_COMB (@lem3228591) (@lem3228590 A s)). Qed.
Lemma lem3228593 {A : Type'} (s : A -> Prop) : (term27 A s) = (term27 A s).
Proof. exact (MK_COMB (@lem3228592 A s) (@lem3228586 A s)). Qed.
Lemma lem3228594 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228595 {A : Type'} (s : A -> Prop) : (term28 A s) = (term28 A s).
Proof. exact (MK_COMB (@lem3228594) (@lem3228593 A s)). Qed.
Lemma lem3228596 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3228595 A s)). Qed.
Lemma lem3228597 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3228598 {A : Type'} : (term30 A) = (term30 A).
Proof. exact (MK_COMB (@lem3228597 A) (@lem3228596 A)). Qed.
Lemma lem3228621 {A : Type'} : (term32 A) = (term30 A).
Proof. exact (TRANS (@lem3228580 A) (@lem3228598 A)). Qed.
Lemma lem3228622 {A : Type'} : (term30 A) = (term32 A).
Proof. exact (SYM (@lem3228621 A)). Qed.
Lemma lem3228623 {A : Type'} (s : A -> Prop) (h1 : term27 A s) : term27 A s.
Proof. exact (h1). Qed.
Lemma lem3228624 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3228625 {A : Type'} (s : A -> Prop) : (term21 A s) = (term21 A s).
Proof. exact (fun_ext (fun x : A => @lem3228624 A s x)). Qed.
Lemma lem3228626 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228627 {A : Type'} (s : A -> Prop) : (term22 A s) = (term22 A s).
Proof. exact (MK_COMB (@lem3228626 A) (@lem3228625 A s)). Qed.
Lemma lem3228629 {A : Type'} (P : A -> Prop) : (term39 A P) = (term40 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3228630 {A : Type'} (s : A -> Prop) : (term26 A s) = (term41 A s).
Proof. exact (@lem3228629 A (term21 A s)). Qed.
Lemma lem3228631 {A : Type'} (s : A -> Prop) (x : A) : (term42 A s x) = (s x).
Proof. exact (eq_refl (term42 A s x)). Qed.
Lemma lem3228632 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3228634 {A : Type'} (s : A -> Prop) (x : A) : (term43 A s x) = (term44 A s x).
Proof. exact (MK_COMB (@lem3228632) (@lem3228631 A s x)). Qed.
Lemma lem3228635 {A : Type'} (s : A -> Prop) : (term45 A s) = (term46 A s).
Proof. exact (fun_ext (fun x : A => @lem3228634 A s x)). Qed.
Lemma lem3228636 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3228637 {A : Type'} (s : A -> Prop) : (term41 A s) = (term40 A s).
Proof. exact (MK_COMB (@lem3228636 A) (@lem3228635 A s)). Qed.
Lemma lem3228638 {A : Type'} (s : A -> Prop) : (term26 A s) = (term40 A s).
Proof. exact (TRANS (@lem3228630 A s) (@lem3228637 A s)). Qed.
Lemma lem3228639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3228640 {A : Type'} (s : A -> Prop) : (term23 A s) = (term23 A s).
Proof. exact (MK_COMB (@lem3228639) (@lem3228627 A s)). Qed.
Lemma lem3228641 {A : Type'} (s : A -> Prop) : (term27 A s) = (term47 A s).
Proof. exact (MK_COMB (@lem3228640 A s) (@lem3228638 A s)). Qed.
Lemma lem3228652 {A : Type'} (P : Prop) (Q : A -> Prop) : (term48 A P Q) = (term49 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3228653 {A : Type'} (P : Prop) (Q : A -> Prop) : (term48 A P Q) = (term49 A P Q).
Proof. exact (@lem3228652 A P Q). Qed.
Lemma lem3228654 {A : Type'} (s : A -> Prop) : (term50 A s) = (term51 A s).
Proof. exact (@lem3228653 A (term22 A s) (term46 A s)). Qed.
Lemma lem3228655 {A : Type'} (s : A -> Prop) (x : A) : (term52 A s x) = (term44 A s x).
Proof. exact (eq_refl (term52 A s x)). Qed.
Lemma lem3228656 {A : Type'} (s : A -> Prop) : (term53 A s) = (term46 A s).
Proof. exact (fun_ext (fun x : A => @lem3228655 A s x)). Qed.
Lemma lem3228657 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3228658 {A : Type'} (s : A -> Prop) : (term54 A s) = (term40 A s).
Proof. exact (MK_COMB (@lem3228657 A) (@lem3228656 A s)). Qed.
Lemma lem3228659 {A : Type'} (s : A -> Prop) : (term23 A s) = (term23 A s).
Proof. exact (eq_refl (term23 A s)). Qed.
Lemma lem3228660 {A : Type'} (s : A -> Prop) : (term50 A s) = (term47 A s).
Proof. exact (MK_COMB (@lem3228659 A s) (@lem3228658 A s)). Qed.
Lemma lem3228661 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3228662 {A : Type'} (s : A -> Prop) : (term55 A s) = (term56 A s).
Proof. exact (MK_COMB (@lem3228661) (@lem3228660 A s)). Qed.
Lemma lem3228663 {A : Type'} (s : A -> Prop) (x : A) : (term52 A s x) = (term44 A s x).
Proof. exact (eq_refl (term52 A s x)). Qed.
Lemma lem3228664 {A : Type'} (s : A -> Prop) : (term23 A s) = (term23 A s).
Proof. exact (eq_refl (term23 A s)). Qed.
Lemma lem3228665 {A : Type'} (s : A -> Prop) (x : A) : (term57 A s x) = (term58 A s x).
Proof. exact (MK_COMB (@lem3228664 A s) (@lem3228663 A s x)). Qed.
Lemma lem3228666 {A : Type'} (s : A -> Prop) : (term59 A s) = (term60 A s).
Proof. exact (fun_ext (fun x : A => @lem3228665 A s x)). Qed.
Lemma lem3228667 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3228668 {A : Type'} (s : A -> Prop) : (term51 A s) = (term61 A s).
Proof. exact (MK_COMB (@lem3228667 A) (@lem3228666 A s)). Qed.
Lemma lem3228669 {A : Type'} (s : A -> Prop) : ((term50 A s) = (term51 A s)) = ((term47 A s) = (term61 A s)).
Proof. exact (MK_COMB (@lem3228662 A s) (@lem3228668 A s)). Qed.
Lemma lem3228671 {A : Type'} (s : A -> Prop) : (term47 A s) = (term61 A s).
Proof. exact (EQ_MP (@lem3228669 A s) (@lem3228654 A s)). Qed.
Lemma lem3228672 {A : Type'} (s : A -> Prop) : (term27 A s) = (term61 A s).
Proof. exact (TRANS (@lem3228641 A s) (@lem3228671 A s)). Qed.
Lemma lem3228673 {A : Type'} (s : A -> Prop) (h1 : term27 A s) : term61 A s.
Proof. exact (EQ_MP (@lem3228672 A s) (@lem3228623 A s h1)). Qed.
Lemma lem3228674 {A : Type'} (s : A -> Prop) (x : A) (h1 : term58 A s x) : term58 A s x.
Proof. exact (h1). Qed.
Lemma lem3228679 {A : Type'} (s : A -> Prop) (x : A) : (term44 A s x) = (term44 A s x).
Proof. exact (eq_refl (term44 A s x)). Qed.
Lemma lem3228682 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3228683 {A : Type'} (s : A -> Prop) : (term21 A s) = (term21 A s).
Proof. exact (fun_ext (fun x : A => @lem3228682 A s x)). Qed.
Lemma lem3228684 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228685 {A : Type'} (s : A -> Prop) : (term22 A s) = (term22 A s).
Proof. exact (MK_COMB (@lem3228684 A) (@lem3228683 A s)). Qed.
Lemma lem3228686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3228687 {A : Type'} (s : A -> Prop) : (term23 A s) = (term23 A s).
Proof. exact (MK_COMB (@lem3228686) (@lem3228685 A s)). Qed.
Lemma lem3228688 {A : Type'} (s : A -> Prop) (x : A) : (term58 A s x) = (term58 A s x).
Proof. exact (MK_COMB (@lem3228687 A s) (@lem3228679 A s x)). Qed.
Lemma lem3228689 {A : Type'} (s : A -> Prop) (x : A) (h1 : term58 A s x) : term58 A s x.
Proof. exact (EQ_MP (@lem3228688 A s x) (@lem3228674 A s x h1)). Qed.
Lemma lem3228691 {A : Type'} (s : A -> Prop) (x : A) (h1 : term58 A s x) : term22 A s.
Proof. exact (proj1 (@lem3228689 A s x h1)). Qed.
Lemma lem3228693 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3228694 {A : Type'} (s : A -> Prop) : (term21 A s) = (term21 A s).
Proof. exact (fun_ext (fun x : A => @lem3228693 A s x)). Qed.
Lemma lem3228695 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3228697 {A : Type'} (s : A -> Prop) : (term22 A s) = (term22 A s).
Proof. exact (MK_COMB (@lem3228695 A) (@lem3228694 A s)). Qed.
Lemma lem3228698 {A : Type'} (s : A -> Prop) (x : A) (h1 : term58 A s x) : term22 A s.
Proof. exact (EQ_MP (@lem3228697 A s) (@lem3228691 A s x h1)). Qed.
Lemma lem3228703 {A : Type'} (_33176 : A) (s : A -> Prop) (x : A) (h1 : term58 A s x) : term42 A s _33176.
Proof. exact (@lem3228698 A s x h1 _33176). Qed.
Lemma lem3228704 {A : Type'} (s : A -> Prop) (_33176 : A) : (term42 A s _33176) = (s _33176).
Proof. exact (eq_refl (term42 A s _33176)). Qed.
Lemma lem3228709 {A : Type'} (s : A -> Prop) (x : A) (h1 : term58 A s x) : term44 A s x.
Proof. exact (proj2 (@lem3228689 A s x h1)). Qed.
Lemma lem3228711 {A : Type'} (_33176 : A) (s : A -> Prop) (x : A) (h1 : term58 A s x) : s _33176.
Proof. exact (EQ_MP (@lem3228704 A s _33176) (@lem3228703 A _33176 s x h1)). Qed.
Lemma lem3228712 {A : Type'} (_33176 : A) (s : A -> Prop) (x : A) (h1 : term58 A s x) : s _33176.
Proof. exact (@lem3228711 A _33176 s x h1). Qed.
Lemma lem3228713 {A : Type'} (s : A -> Prop) (x : A) (h1 : term58 A s x) : s x.
Proof. exact (@lem3228712 A x s x h1). Qed.
Lemma lem3228714 {A : Type'} (s : A -> Prop) (x : A) (h1 : term58 A s x) : term62 A s x.
Proof. exact (fun h0 : term44 A s x => @lem3228713 A s x h1). Qed.
Lemma lem3228716 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3228717 {A : Type'} (s : A -> Prop) (x : A) : (term62 A s x) = (s x).
Proof. exact (@lem3228716 (s x)). Qed.
Lemma lem3228718 {A : Type'} (s : A -> Prop) (x : A) (h1 : term58 A s x) : s x.
Proof. exact (EQ_MP (@lem3228717 A s x) (@lem3228714 A s x h1)). Qed.
Lemma lem3228721 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3228723 {A : Type'} (s : A -> Prop) (x : A) : (term44 A s x) = (term64 A s x).
Proof. exact (@lem3228721 (s x)). Qed.
Lemma lem3228726 {A : Type'} (s : A -> Prop) (x : A) (h1 : term58 A s x) : term64 A s x.
Proof. exact (EQ_MP (@lem3228723 A s x) (@lem3228709 A s x h1)). Qed.
Lemma lem3228729 {A : Type'} (s : A -> Prop) (x : A) (h1 : term58 A s x) : False.
Proof. exact (@lem3228726 A s x h1 (@lem3228718 A s x h1)). Qed.
Lemma lem3228730 {A : Type'} (s : A -> Prop) (x : A) (h1 : term58 A s x) : term65.
Proof. exact (fun h0 : ~ False => @lem3228729 A s x h1). Qed.
Lemma lem3228732 (p : Prop) : (term63 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3228733 : term65 = False.
Proof. exact (@lem3228732 False). Qed.
Lemma lem3228734 {A : Type'} (s : A -> Prop) (x : A) (h1 : term58 A s x) : False.
Proof. exact (EQ_MP (@lem3228733) (@lem3228730 A s x h1)). Qed.
Lemma lem3228735 {A : Type'} (s : A -> Prop) (x : A) (h1 : term58 A s x) : (term58 A s x) = False.
Proof. exact (prop_ext (fun h2 : term58 A s x => @lem3228734 A s x h1) (fun h2 : False => @lem3228689 A s x h1)). Qed.
Lemma lem3228736 {A : Type'} (s : A -> Prop) (x : A) (h1 : term58 A s x) : False.
Proof. exact (EQ_MP (@lem3228735 A s x h1) (@lem3228689 A s x h1)). Qed.
Lemma lem3228737 {A : Type'} (s : A -> Prop) (h1 : term27 A s) : False.
Proof. exact (ex_elim (@lem3228673 A s h1) (fun x : A => fun h0 : term60 A s x => @lem3228736 A s x h0)). Qed.
Lemma lem3228738 {A : Type'} (s : A -> Prop) : term66 A s.
Proof. exact (fun h0 : term27 A s => @lem3228737 A s h0). Qed.
Lemma lem3228739 {A : Type'} (s : A -> Prop) : (term66 A s) = (term28 A s).
Proof. exact (@lem69 (term27 A s)). Qed.
Lemma lem3228740 {A : Type'} (s : A -> Prop) : term28 A s.
Proof. exact (EQ_MP (@lem3228739 A s) (@lem3228738 A s)). Qed.
Lemma lem3228745 {A : Type'} : term30 A.
Proof. exact (fun s : A -> Prop => @lem3228740 A s). Qed.
Lemma lem3228746 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem3228622 A) (@lem3228745 A)). Qed.
Lemma lem3228748 {A : Type'} : term32 A.
Proof. exact (@lem3228555 A (@lem3228746 A)). Qed.
Lemma lem3228749 {A : Type'} (h1 : term33 A) : False.
Proof. exact (@lem3228748 A (@lem3228539 A h1)). Qed.
Lemma lem3228750 {A : Type'} (h1 : term33 A) : (term33 A) = False.
Proof. exact (prop_ext (fun h2 : term33 A => @lem3228749 A h1) (fun h2 : False => @lem3228539 A h1)). Qed.
Lemma lem3228751 {A : Type'} (h1 : term33 A) : False.
Proof. exact (EQ_MP (@lem3228750 A h1) (@lem3228539 A h1)). Qed.
Lemma lem3228752 {A : Type'} : term32 A.
Proof. exact (fun h0 : term33 A => @lem3228751 A h0). Qed.
Lemma lem3228753 {A : Type'} : term30 A.
Proof. exact (EQ_MP (@lem3228538 A) (@lem3228752 A)). Qed.
Lemma lem3228754 {A : Type'} : term16 A.
Proof. exact (EQ_MP (@lem3228534 A) (@lem3228753 A)). Qed.
Lemma lem3228755 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem3228457 A) (@lem3228754 A)). Qed.
