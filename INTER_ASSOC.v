Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTER_ASSOC_term_abbrevs.
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
Lemma lem3254449 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3254450 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3254449 A s t). Qed.
Lemma lem3254451 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : ((term1 A s t u) = (term2 A s t u)) = (term3 A s t u).
Proof. exact (@lem3254450 A (term1 A s t u) (term2 A s t u)). Qed.
Lemma lem3254460 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term4 A s t) = (term5 A s t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3254451 A s t u)). Qed.
Lemma lem3254461 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3254462 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term6 A s t) = (term7 A s t).
Proof. exact (MK_COMB (@lem3254461 A) (@lem3254460 A s t)). Qed.
Lemma lem3254467 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3254462 A s t)). Qed.
Lemma lem3254468 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3254469 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A s).
Proof. exact (MK_COMB (@lem3254468 A) (@lem3254467 A s)). Qed.
Lemma lem3254474 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3254469 A s)). Qed.
Lemma lem3254475 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3254476 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem3254475 A) (@lem3254474 A)). Qed.
Lemma lem3254481 {A : Type'} : (term15 A) = (term14 A).
Proof. exact (SYM (@lem3254476 A)). Qed.
Lemma lem3254501 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3254502 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3254501 A s x t). Qed.
Lemma lem3254503 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (u : A -> Prop) : (term18 A x s t u) = (term19 A s t x u).
Proof. exact (@lem3254502 A (@INTER A s t) x u). Qed.
Lemma lem3254507 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3254508 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3254507 A s x t). Qed.
Lemma lem3254512 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3254513 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3254512 A P x). Qed.
Lemma lem3254514 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3254513 A s x). Qed.
Lemma lem3254515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3254516 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term21 A s x).
Proof. exact (MK_COMB (@lem3254515) (@lem3254514 A s x)). Qed.
Lemma lem3254518 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3254519 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3254518 A P x). Qed.
Lemma lem3254520 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3254519 A t x). Qed.
Lemma lem3254521 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term17 A s x t) = (term22 A s t x).
Proof. exact (MK_COMB (@lem3254516 A s x) (@lem3254520 A t x)). Qed.
Lemma lem3254524 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term16 A x s t) = (term22 A s t x).
Proof. exact (TRANS (@lem3254508 A s x t) (@lem3254521 A s t x)). Qed.
Lemma lem3254525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3254526 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term23 A x s t) = (term24 A s t x).
Proof. exact (MK_COMB (@lem3254525) (@lem3254524 A s t x)). Qed.
Lemma lem3254528 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3254529 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3254528 A P x). Qed.
Lemma lem3254530 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3254529 A u x). Qed.
Lemma lem3254531 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term19 A s t x u) = (term25 A s t u x).
Proof. exact (MK_COMB (@lem3254526 A s t x) (@lem3254530 A u x)). Qed.
Lemma lem3254534 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term18 A x s t u) = (term25 A s t u x).
Proof. exact (TRANS (@lem3254503 A s t x u) (@lem3254531 A s t u x)). Qed.
Lemma lem3254535 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3254536 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term26 A x s t u) = (term27 A s t u x).
Proof. exact (MK_COMB (@lem3254535) (@lem3254534 A s t u x)). Qed.
Lemma lem3254538 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3254539 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3254538 A s x t). Qed.
Lemma lem3254540 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (u : A -> Prop) : (term28 A x s t u) = (term29 A s x t u).
Proof. exact (@lem3254539 A s x (@INTER A t u)). Qed.
Lemma lem3254544 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3254545 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3254544 A P x). Qed.
Lemma lem3254546 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3254545 A s x). Qed.
Lemma lem3254547 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3254548 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term21 A s x).
Proof. exact (MK_COMB (@lem3254547) (@lem3254546 A s x)). Qed.
Lemma lem3254550 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3254551 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3254550 A s x t). Qed.
Lemma lem3254552 {A : Type'} (t : A -> Prop) (x : A) (u : A -> Prop) : (term16 A x t u) = (term17 A t x u).
Proof. exact (@lem3254551 A t x u). Qed.
Lemma lem3254556 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3254557 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3254556 A P x). Qed.
Lemma lem3254558 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3254557 A t x). Qed.
Lemma lem3254559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3254560 {A : Type'} (t : A -> Prop) (x : A) : (term20 A x t) = (term21 A t x).
Proof. exact (MK_COMB (@lem3254559) (@lem3254558 A t x)). Qed.
Lemma lem3254562 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3254563 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3254562 A P x). Qed.
Lemma lem3254564 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem3254563 A u x). Qed.
Lemma lem3254565 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term17 A t x u) = (term22 A t u x).
Proof. exact (MK_COMB (@lem3254560 A t x) (@lem3254564 A u x)). Qed.
Lemma lem3254568 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term16 A x t u) = (term22 A t u x).
Proof. exact (TRANS (@lem3254552 A t x u) (@lem3254565 A t u x)). Qed.
Lemma lem3254569 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term29 A s x t u) = (term30 A s t u x).
Proof. exact (MK_COMB (@lem3254548 A s x) (@lem3254568 A t u x)). Qed.
Lemma lem3254572 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term28 A x s t u) = (term30 A s t u x).
Proof. exact (TRANS (@lem3254540 A s x t u) (@lem3254569 A s t u x)). Qed.
Lemma lem3254573 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : ((term18 A x s t u) = (term28 A x s t u)) = ((term25 A s t u x) = (term30 A s t u x)).
Proof. exact (MK_COMB (@lem3254536 A s t u x) (@lem3254572 A s t u x)). Qed.
Lemma lem3254576 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term31 A s t u) = (term32 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3254573 A s t u x)). Qed.
Lemma lem3254577 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3254578 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term3 A s t u) = (term33 A s t u).
Proof. exact (MK_COMB (@lem3254577 A) (@lem3254576 A s t u)). Qed.
Lemma lem3254583 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term5 A s t) = (term34 A s t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3254578 A s t u)). Qed.
Lemma lem3254584 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3254585 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term7 A s t) = (term35 A s t).
Proof. exact (MK_COMB (@lem3254584 A) (@lem3254583 A s t)). Qed.
Lemma lem3254590 {A : Type'} (s : A -> Prop) : (term9 A s) = (term36 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3254585 A s t)). Qed.
Lemma lem3254591 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3254592 {A : Type'} (s : A -> Prop) : (term11 A s) = (term37 A s).
Proof. exact (MK_COMB (@lem3254591 A) (@lem3254590 A s)). Qed.
Lemma lem3254597 {A : Type'} : (term13 A) = (term38 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3254592 A s)). Qed.
Lemma lem3254598 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3254599 {A : Type'} : (term15 A) = (term39 A).
Proof. exact (MK_COMB (@lem3254598 A) (@lem3254597 A)). Qed.
Lemma lem3254604 {A : Type'} : (term39 A) = (term15 A).
Proof. exact (SYM (@lem3254599 A)). Qed.
Lemma lem3254606 (p : Prop) : p = (term40 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3254607 {A : Type'} : (term39 A) = (term41 A).
Proof. exact (@lem3254606 (term39 A)). Qed.
Lemma lem3254608 {A : Type'} : (term41 A) = (term39 A).
Proof. exact (SYM (@lem3254607 A)). Qed.
Lemma lem3254609 {A : Type'} (h1 : term42 A) : term42 A.
Proof. exact (h1). Qed.
Lemma lem3254612 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (h1). Qed.
Lemma lem3254613 {A : Type'} : term43 A.
Proof. exact (fun h0 : term41 A => @lem3254612 A h0). Qed.
Lemma lem3254614 {A : Type'} (h1 : term43 A) : term43 A.
Proof. exact (h1). Qed.
Lemma lem3254615 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (h1). Qed.
Lemma lem3254616 {A : Type'} (h1 : term41 A) (h2 : term43 A) : term41 A.
Proof. exact (@lem3254614 A h2 (@lem3254615 A h1)). Qed.
Lemma lem3254617 {A : Type'} (h1 : term41 A) : term44 A.
Proof. exact (fun h0 : term43 A => @lem3254616 A h1 h0). Qed.
Lemma lem3254618 {A : Type'} (h1 : term43 A) : term43 A.
Proof. exact (h1). Qed.
Lemma lem3254619 {A : Type'} (h1 : term41 A) (h2 : term43 A) : term41 A.
Proof. exact (@lem3254617 A h1 (@lem3254618 A h2)). Qed.
Lemma lem3254620 {A : Type'} (h1 : term43 A) : term43 A.
Proof. exact (fun h0 : term41 A => @lem3254619 A h0 h1). Qed.
Lemma lem3254621 {A : Type'} : term45 A.
Proof. exact (fun h0 : term43 A => @lem3254620 A h0). Qed.
Lemma lem3254624 {A : Type'} : term43 A.
Proof. exact (@lem3254621 A (@lem3254613 A)). Qed.
Lemma lem3254625 {A : Type'} : term43 A.
Proof. exact (@lem3254624 A). Qed.
Lemma lem3254627 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3254628 {A : Type'} : (term41 A) = (term46 A).
Proof. exact (@lem3254627 (term42 A)). Qed.
Lemma lem3254630 (t : Prop) : (term47 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3254631 {A : Type'} : (term46 A) = (term39 A).
Proof. exact (@lem3254630 (term39 A)). Qed.
Lemma lem3254660 {A : Type'} : (term41 A) = (term39 A).
Proof. exact (TRANS (@lem3254628 A) (@lem3254631 A)). Qed.
Lemma lem3254681 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : ((term25 A s t u x) = (term30 A s t u x)) = ((term25 A s t u x) = (term30 A s t u x)).
Proof. exact (eq_refl ((term25 A s t u x) = (term30 A s t u x))). Qed.
Lemma lem3254682 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term32 A s t u) = (term32 A s t u).
Proof. exact (fun_ext (fun x : A => @lem3254681 A s t u x)). Qed.
Lemma lem3254683 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3254684 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : (term33 A s t u) = (term33 A s t u).
Proof. exact (MK_COMB (@lem3254683 A) (@lem3254682 A s t u)). Qed.
Lemma lem3254685 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term34 A s t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem3254684 A s t u)). Qed.
Lemma lem3254686 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3254687 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = (term35 A s t).
Proof. exact (MK_COMB (@lem3254686 A) (@lem3254685 A s t)). Qed.
Lemma lem3254688 {A : Type'} (s : A -> Prop) : (term36 A s) = (term36 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3254687 A s t)). Qed.
Lemma lem3254689 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3254690 {A : Type'} (s : A -> Prop) : (term37 A s) = (term37 A s).
Proof. exact (MK_COMB (@lem3254689 A) (@lem3254688 A s)). Qed.
Lemma lem3254691 {A : Type'} : (term38 A) = (term38 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3254690 A s)). Qed.
Lemma lem3254692 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3254693 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (MK_COMB (@lem3254692 A) (@lem3254691 A)). Qed.
Lemma lem3254728 {A : Type'} : (term41 A) = (term39 A).
Proof. exact (TRANS (@lem3254660 A) (@lem3254693 A)). Qed.
Lemma lem3254729 {A : Type'} : (term39 A) = (term41 A).
Proof. exact (SYM (@lem3254728 A)). Qed.
Lemma lem3254731 (p : Prop) : p = (term40 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3254732 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : ((term25 A s t u x) = (term30 A s t u x)) = (term48 A s t u x).
Proof. exact (@lem3254731 ((term25 A s t u x) = (term30 A s t u x))). Qed.
Lemma lem3254733 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term48 A s t u x) = ((term25 A s t u x) = (term30 A s t u x)).
Proof. exact (SYM (@lem3254732 A s t u x)). Qed.
Lemma lem3254734 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term49 A s t u x) : term49 A s t u x.
Proof. exact (h1). Qed.
Lemma lem3254743 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term50 A s t x) = (term51 A s t x).
Proof. exact (@lem17045 (s x) (t x)). Qed.
Lemma lem3254747 {A : Type'} (u : A -> Prop) (x : A) : (term52 A u x) = (term52 A u x).
Proof. exact (eq_refl (term52 A u x)). Qed.
Lemma lem3254749 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3254750 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term53 A s t x) = (term54 A s t x).
Proof. exact (MK_COMB (@lem3254749) (@lem3254743 A s t x)). Qed.
Lemma lem3254751 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term55 A s t u x) = (term56 A s t u x).
Proof. exact (MK_COMB (@lem3254750 A s t x) (@lem3254747 A u x)). Qed.
Lemma lem3254752 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term57 A s t u x) = (term55 A s t u x).
Proof. exact (@lem17045 (term22 A s t x) (u x)). Qed.
Lemma lem3254753 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term57 A s t u x) = (term56 A s t u x).
Proof. exact (TRANS (@lem3254752 A s t u x) (@lem3254751 A s t u x)). Qed.
Lemma lem3254767 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) : (term50 A t u x) = (term51 A t u x).
Proof. exact (@lem17045 (t x) (u x)). Qed.
Lemma lem3254772 {A : Type'} (s : A -> Prop) (x : A) : (term58 A s x) = (term58 A s x).
Proof. exact (eq_refl (term58 A s x)). Qed.
Lemma lem3254773 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term59 A s t u x) = (term60 A s t u x).
Proof. exact (MK_COMB (@lem3254772 A s x) (@lem3254767 A t u x)). Qed.
Lemma lem3254774 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term61 A s t u x) = (term59 A s t u x).
Proof. exact (@lem17045 (s x) (term22 A t u x)). Qed.
Lemma lem3254775 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term61 A s t u x) = (term60 A s t u x).
Proof. exact (TRANS (@lem3254774 A s t u x) (@lem3254773 A s t u x)). Qed.
Lemma lem3254778 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term30 A s t u x) = (term30 A s t u x).
Proof. exact (eq_refl (term30 A s t u x)). Qed.
Lemma lem3254779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3254780 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term62 A s t u x) = (term63 A s t u x).
Proof. exact (MK_COMB (@lem3254779) (@lem3254753 A s t u x)). Qed.
Lemma lem3254781 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term64 A s t u x) = (term65 A s t u x).
Proof. exact (MK_COMB (@lem3254780 A s t u x) (@lem3254778 A s t u x)). Qed.
Lemma lem3254783 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term66 A s t u x) = (term66 A s t u x).
Proof. exact (eq_refl (term66 A s t u x)). Qed.
Lemma lem3254784 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term67 A s t u x) = (term68 A s t u x).
Proof. exact (MK_COMB (@lem3254783 A s t u x) (@lem3254775 A s t u x)). Qed.
Lemma lem3254785 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3254786 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term69 A s t u x) = (term70 A s t u x).
Proof. exact (MK_COMB (@lem3254785) (@lem3254784 A s t u x)). Qed.
Lemma lem3254787 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term71 A s t u x) = (term72 A s t u x).
Proof. exact (MK_COMB (@lem3254786 A s t u x) (@lem3254781 A s t u x)). Qed.
Lemma lem3254788 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term49 A s t u x) = (term71 A s t u x).
Proof. exact (@lem17646 (term25 A s t u x) (term30 A s t u x)). Qed.
Lemma lem3254793 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term49 A s t u x) = (term72 A s t u x).
Proof. exact (TRANS (@lem3254788 A s t u x) (@lem3254787 A s t u x)). Qed.
Lemma lem3254876 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term49 A s t u x) : term72 A s t u x.
Proof. exact (EQ_MP (@lem3254793 A s t u x) (@lem3254734 A s t u x h1)). Qed.
Lemma lem3254877 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term68 A s t u x.
Proof. exact (h1). Qed.
Lemma lem3254878 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term65 A s t u x.
Proof. exact (h1). Qed.
Lemma lem3254879 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term60 A s t u x.
Proof. exact (proj2 (@lem3254877 A s t u x h1)). Qed.
Lemma lem3254880 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term25 A s t u x.
Proof. exact (proj1 (@lem3254877 A s t u x h1)). Qed.
Lemma lem3254882 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term22 A s t x.
Proof. exact (proj1 (@lem3254880 A s t u x h1)). Qed.
Lemma lem3254886 {A : Type'} (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term51 A t u x) : term51 A t u x.
Proof. exact (h1). Qed.
Lemma lem3254889 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term30 A s t u x.
Proof. exact (proj2 (@lem3254878 A s t u x h1)). Qed.
Lemma lem3254890 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term56 A s t u x.
Proof. exact (proj1 (@lem3254878 A s t u x h1)). Qed.
Lemma lem3254891 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term22 A t u x.
Proof. exact (proj2 (@lem3254889 A s t u x h1)). Qed.
Lemma lem3254895 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term51 A s t x) : term51 A s t x.
Proof. exact (h1). Qed.
Lemma lem3254914 {A : Type'} (s : A -> Prop) (x : A) (h1 : term52 A s x) : term52 A s x.
Proof. exact (h1). Qed.
Lemma lem3254930 {A : Type'} (t : A -> Prop) (x : A) (h1 : term52 A t x) : term52 A t x.
Proof. exact (h1). Qed.
Lemma lem3254946 {A : Type'} (u : A -> Prop) (x : A) (h1 : term52 A u x) : term52 A u x.
Proof. exact (h1). Qed.
Lemma lem3254962 {A : Type'} (s : A -> Prop) (x : A) (h1 : term52 A s x) : term52 A s x.
Proof. exact (h1). Qed.
Lemma lem3254978 {A : Type'} (t : A -> Prop) (x : A) (h1 : term52 A t x) : term52 A t x.
Proof. exact (h1). Qed.
Lemma lem3254994 {A : Type'} (u : A -> Prop) (x : A) (h1 : term52 A u x) : term52 A u x.
Proof. exact (h1). Qed.
Lemma lem3255002 {A : Type'} (s : A -> Prop) (x : A) (h1 : term52 A s x) : term52 A s x.
Proof. exact (h1). Qed.
Lemma lem3255010 {A : Type'} (t : A -> Prop) (x : A) (h1 : term52 A t x) : term52 A t x.
Proof. exact (h1). Qed.
Lemma lem3255018 {A : Type'} (u : A -> Prop) (x : A) (h1 : term52 A u x) : term52 A u x.
Proof. exact (h1). Qed.
Lemma lem3255026 {A : Type'} (s : A -> Prop) (x : A) (h1 : term52 A s x) : term52 A s x.
Proof. exact (h1). Qed.
Lemma lem3255034 {A : Type'} (t : A -> Prop) (x : A) (h1 : term52 A t x) : term52 A t x.
Proof. exact (h1). Qed.
Lemma lem3255042 {A : Type'} (u : A -> Prop) (x : A) (h1 : term52 A u x) : term52 A u x.
Proof. exact (h1). Qed.
Lemma lem3255044 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : s x.
Proof. exact (proj1 (@lem3254882 A s t u x h1)). Qed.
Lemma lem3255045 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term73 A s x.
Proof. exact (fun h0 : term52 A s x => @lem3255044 A s t u x h1). Qed.
Lemma lem3255047 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255048 {A : Type'} (s : A -> Prop) (x : A) : (term73 A s x) = (s x).
Proof. exact (@lem3255047 (s x)). Qed.
Lemma lem3255049 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : s x.
Proof. exact (EQ_MP (@lem3255048 A s x) (@lem3255045 A s t u x h1)). Qed.
Lemma lem3255052 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3255054 {A : Type'} (s : A -> Prop) (x : A) : (term52 A s x) = (term75 A s x).
Proof. exact (@lem3255052 (s x)). Qed.
Lemma lem3255057 {A : Type'} (s : A -> Prop) (x : A) (h1 : term52 A s x) : term75 A s x.
Proof. exact (EQ_MP (@lem3255054 A s x) (@lem3255002 A s x h1)). Qed.
Lemma lem3255060 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term68 A s t u x) : False.
Proof. exact (@lem3255057 A s x h1 (@lem3255049 A s t u x h2)). Qed.
Lemma lem3255061 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term68 A s t u x) : term76.
Proof. exact (fun h0 : ~ False => @lem3255060 A s t u x h1 h2). Qed.
Lemma lem3255063 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255064 : term76 = False.
Proof. exact (@lem3255063 False). Qed.
Lemma lem3255065 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255064) (@lem3255061 A s t u x h1 h2)). Qed.
Lemma lem3255067 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : t x.
Proof. exact (proj2 (@lem3254882 A s t u x h1)). Qed.
Lemma lem3255068 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term73 A t x.
Proof. exact (fun h0 : term52 A t x => @lem3255067 A s t u x h1). Qed.
Lemma lem3255070 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255071 {A : Type'} (t : A -> Prop) (x : A) : (term73 A t x) = (t x).
Proof. exact (@lem3255070 (t x)). Qed.
Lemma lem3255072 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : t x.
Proof. exact (EQ_MP (@lem3255071 A t x) (@lem3255068 A s t u x h1)). Qed.
Lemma lem3255075 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3255077 {A : Type'} (t : A -> Prop) (x : A) : (term52 A t x) = (term75 A t x).
Proof. exact (@lem3255075 (t x)). Qed.
Lemma lem3255080 {A : Type'} (t : A -> Prop) (x : A) (h1 : term52 A t x) : term75 A t x.
Proof. exact (EQ_MP (@lem3255077 A t x) (@lem3255010 A t x h1)). Qed.
Lemma lem3255083 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term68 A s t u x) : False.
Proof. exact (@lem3255080 A t x h1 (@lem3255072 A s t u x h2)). Qed.
Lemma lem3255084 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term68 A s t u x) : term76.
Proof. exact (fun h0 : ~ False => @lem3255083 A s t u x h1 h2). Qed.
Lemma lem3255086 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255087 : term76 = False.
Proof. exact (@lem3255086 False). Qed.
Lemma lem3255088 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255087) (@lem3255084 A s t u x h1 h2)). Qed.
Lemma lem3255090 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : u x.
Proof. exact (proj2 (@lem3254880 A s t u x h1)). Qed.
Lemma lem3255091 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : term73 A u x.
Proof. exact (fun h0 : term52 A u x => @lem3255090 A s t u x h1). Qed.
Lemma lem3255093 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255094 {A : Type'} (u : A -> Prop) (x : A) : (term73 A u x) = (u x).
Proof. exact (@lem3255093 (u x)). Qed.
Lemma lem3255095 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : u x.
Proof. exact (EQ_MP (@lem3255094 A u x) (@lem3255091 A s t u x h1)). Qed.
Lemma lem3255098 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3255100 {A : Type'} (u : A -> Prop) (x : A) : (term52 A u x) = (term75 A u x).
Proof. exact (@lem3255098 (u x)). Qed.
Lemma lem3255103 {A : Type'} (u : A -> Prop) (x : A) (h1 : term52 A u x) : term75 A u x.
Proof. exact (EQ_MP (@lem3255100 A u x) (@lem3255018 A u x h1)). Qed.
Lemma lem3255106 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term68 A s t u x) : False.
Proof. exact (@lem3255103 A u x h1 (@lem3255095 A s t u x h2)). Qed.
Lemma lem3255107 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term68 A s t u x) : term76.
Proof. exact (fun h0 : ~ False => @lem3255106 A s t u x h1 h2). Qed.
Lemma lem3255109 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255110 : term76 = False.
Proof. exact (@lem3255109 False). Qed.
Lemma lem3255111 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255110) (@lem3255107 A s t u x h1 h2)). Qed.
Lemma lem3255113 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : s x.
Proof. exact (proj1 (@lem3254889 A s t u x h1)). Qed.
Lemma lem3255114 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term73 A s x.
Proof. exact (fun h0 : term52 A s x => @lem3255113 A s t u x h1). Qed.
Lemma lem3255116 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255117 {A : Type'} (s : A -> Prop) (x : A) : (term73 A s x) = (s x).
Proof. exact (@lem3255116 (s x)). Qed.
Lemma lem3255118 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : s x.
Proof. exact (EQ_MP (@lem3255117 A s x) (@lem3255114 A s t u x h1)). Qed.
Lemma lem3255121 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3255123 {A : Type'} (s : A -> Prop) (x : A) : (term52 A s x) = (term75 A s x).
Proof. exact (@lem3255121 (s x)). Qed.
Lemma lem3255126 {A : Type'} (s : A -> Prop) (x : A) (h1 : term52 A s x) : term75 A s x.
Proof. exact (EQ_MP (@lem3255123 A s x) (@lem3255026 A s x h1)). Qed.
Lemma lem3255129 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term65 A s t u x) : False.
Proof. exact (@lem3255126 A s x h1 (@lem3255118 A s t u x h2)). Qed.
Lemma lem3255130 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term65 A s t u x) : term76.
Proof. exact (fun h0 : ~ False => @lem3255129 A s t u x h1 h2). Qed.
Lemma lem3255132 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255133 : term76 = False.
Proof. exact (@lem3255132 False). Qed.
Lemma lem3255134 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255133) (@lem3255130 A s t u x h1 h2)). Qed.
Lemma lem3255136 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : t x.
Proof. exact (proj1 (@lem3254891 A s t u x h1)). Qed.
Lemma lem3255137 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term73 A t x.
Proof. exact (fun h0 : term52 A t x => @lem3255136 A s t u x h1). Qed.
Lemma lem3255139 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255140 {A : Type'} (t : A -> Prop) (x : A) : (term73 A t x) = (t x).
Proof. exact (@lem3255139 (t x)). Qed.
Lemma lem3255141 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : t x.
Proof. exact (EQ_MP (@lem3255140 A t x) (@lem3255137 A s t u x h1)). Qed.
Lemma lem3255144 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3255146 {A : Type'} (t : A -> Prop) (x : A) : (term52 A t x) = (term75 A t x).
Proof. exact (@lem3255144 (t x)). Qed.
Lemma lem3255149 {A : Type'} (t : A -> Prop) (x : A) (h1 : term52 A t x) : term75 A t x.
Proof. exact (EQ_MP (@lem3255146 A t x) (@lem3255034 A t x h1)). Qed.
Lemma lem3255152 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term65 A s t u x) : False.
Proof. exact (@lem3255149 A t x h1 (@lem3255141 A s t u x h2)). Qed.
Lemma lem3255153 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term65 A s t u x) : term76.
Proof. exact (fun h0 : ~ False => @lem3255152 A s t u x h1 h2). Qed.
Lemma lem3255155 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255156 : term76 = False.
Proof. exact (@lem3255155 False). Qed.
Lemma lem3255157 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255156) (@lem3255153 A s t u x h1 h2)). Qed.
Lemma lem3255159 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : u x.
Proof. exact (proj2 (@lem3254891 A s t u x h1)). Qed.
Lemma lem3255160 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : term73 A u x.
Proof. exact (fun h0 : term52 A u x => @lem3255159 A s t u x h1). Qed.
Lemma lem3255162 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255163 {A : Type'} (u : A -> Prop) (x : A) : (term73 A u x) = (u x).
Proof. exact (@lem3255162 (u x)). Qed.
Lemma lem3255164 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : u x.
Proof. exact (EQ_MP (@lem3255163 A u x) (@lem3255160 A s t u x h1)). Qed.
Lemma lem3255167 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3255169 {A : Type'} (u : A -> Prop) (x : A) : (term52 A u x) = (term75 A u x).
Proof. exact (@lem3255167 (u x)). Qed.
Lemma lem3255172 {A : Type'} (u : A -> Prop) (x : A) (h1 : term52 A u x) : term75 A u x.
Proof. exact (EQ_MP (@lem3255169 A u x) (@lem3255042 A u x h1)). Qed.
Lemma lem3255175 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term65 A s t u x) : False.
Proof. exact (@lem3255172 A u x h1 (@lem3255164 A s t u x h2)). Qed.
Lemma lem3255176 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term65 A s t u x) : term76.
Proof. exact (fun h0 : ~ False => @lem3255175 A s t u x h1 h2). Qed.
Lemma lem3255178 (p : Prop) : (term74 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3255179 : term76 = False.
Proof. exact (@lem3255178 False). Qed.
Lemma lem3255180 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255179) (@lem3255176 A s t u x h1 h2)). Qed.
Lemma lem3255181 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term65 A s t u x) : (term52 A u x) = False.
Proof. exact (prop_ext (fun h3 : term52 A u x => @lem3255180 A s t u x h1 h2) (fun h3 : False => @lem3255042 A u x h1)). Qed.
Lemma lem3255182 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255181 A s t u x h1 h2) (@lem3255042 A u x h1)). Qed.
Lemma lem3255183 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term65 A s t u x) : (term52 A t x) = False.
Proof. exact (prop_ext (fun h3 : term52 A t x => @lem3255157 A s t u x h1 h2) (fun h3 : False => @lem3255034 A t x h1)). Qed.
Lemma lem3255184 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255183 A s t u x h1 h2) (@lem3255034 A t x h1)). Qed.
Lemma lem3255185 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term65 A s t u x) : (term52 A s x) = False.
Proof. exact (prop_ext (fun h3 : term52 A s x => @lem3255134 A s t u x h1 h2) (fun h3 : False => @lem3255026 A s x h1)). Qed.
Lemma lem3255186 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255185 A s t u x h1 h2) (@lem3255026 A s x h1)). Qed.
Lemma lem3255187 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term68 A s t u x) : (term52 A u x) = False.
Proof. exact (prop_ext (fun h3 : term52 A u x => @lem3255111 A s t u x h1 h2) (fun h3 : False => @lem3255018 A u x h1)). Qed.
Lemma lem3255188 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255187 A s t u x h1 h2) (@lem3255018 A u x h1)). Qed.
Lemma lem3255189 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term68 A s t u x) : (term52 A t x) = False.
Proof. exact (prop_ext (fun h3 : term52 A t x => @lem3255088 A s t u x h1 h2) (fun h3 : False => @lem3255010 A t x h1)). Qed.
Lemma lem3255190 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255189 A s t u x h1 h2) (@lem3255010 A t x h1)). Qed.
Lemma lem3255191 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term68 A s t u x) : (term52 A s x) = False.
Proof. exact (prop_ext (fun h3 : term52 A s x => @lem3255065 A s t u x h1 h2) (fun h3 : False => @lem3255002 A s x h1)). Qed.
Lemma lem3255192 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255191 A s t u x h1 h2) (@lem3255002 A s x h1)). Qed.
Lemma lem3255193 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term65 A s t u x) : (term52 A u x) = False.
Proof. exact (prop_ext (fun h3 : term52 A u x => @lem3255182 A s t u x h1 h2) (fun h3 : False => @lem3254994 A u x h1)). Qed.
Lemma lem3255194 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255193 A s t u x h1 h2) (@lem3254994 A u x h1)). Qed.
Lemma lem3255195 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term65 A s t u x) : (term52 A t x) = False.
Proof. exact (prop_ext (fun h3 : term52 A t x => @lem3255184 A s t u x h1 h2) (fun h3 : False => @lem3254978 A t x h1)). Qed.
Lemma lem3255196 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255195 A s t u x h1 h2) (@lem3254978 A t x h1)). Qed.
Lemma lem3255197 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term65 A s t u x) : (term52 A s x) = False.
Proof. exact (prop_ext (fun h3 : term52 A s x => @lem3255186 A s t u x h1 h2) (fun h3 : False => @lem3254962 A s x h1)). Qed.
Lemma lem3255198 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255197 A s t u x h1 h2) (@lem3254962 A s x h1)). Qed.
Lemma lem3255199 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term68 A s t u x) : (term52 A u x) = False.
Proof. exact (prop_ext (fun h3 : term52 A u x => @lem3255188 A s t u x h1 h2) (fun h3 : False => @lem3254946 A u x h1)). Qed.
Lemma lem3255200 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255199 A s t u x h1 h2) (@lem3254946 A u x h1)). Qed.
Lemma lem3255201 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term68 A s t u x) : (term52 A t x) = False.
Proof. exact (prop_ext (fun h3 : term52 A t x => @lem3255190 A s t u x h1 h2) (fun h3 : False => @lem3254930 A t x h1)). Qed.
Lemma lem3255202 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255201 A s t u x h1 h2) (@lem3254930 A t x h1)). Qed.
Lemma lem3255203 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term68 A s t u x) : (term52 A s x) = False.
Proof. exact (prop_ext (fun h3 : term52 A s x => @lem3255192 A s t u x h1 h2) (fun h3 : False => @lem3254914 A s x h1)). Qed.
Lemma lem3255204 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255203 A s t u x h1 h2) (@lem3254914 A s x h1)). Qed.
Lemma lem3255205 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term65 A s t u x) : (term52 A u x) = False.
Proof. exact (prop_ext (fun h3 : term52 A u x => @lem3255194 A s t u x h1 h2) (fun h3 : False => @lem3254994 A u x h1)). Qed.
Lemma lem3255206 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255205 A s t u x h1 h2) (@lem3254994 A u x h1)). Qed.
Lemma lem3255207 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term65 A s t u x) : (term52 A t x) = False.
Proof. exact (prop_ext (fun h3 : term52 A t x => @lem3255196 A s t u x h1 h2) (fun h3 : False => @lem3254978 A t x h1)). Qed.
Lemma lem3255208 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255207 A s t u x h1 h2) (@lem3254978 A t x h1)). Qed.
Lemma lem3255209 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term65 A s t u x) : (term52 A s x) = False.
Proof. exact (prop_ext (fun h3 : term52 A s x => @lem3255198 A s t u x h1 h2) (fun h3 : False => @lem3254962 A s x h1)). Qed.
Lemma lem3255210 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term65 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255209 A s t u x h1 h2) (@lem3254962 A s x h1)). Qed.
Lemma lem3255211 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term68 A s t u x) : (term52 A u x) = False.
Proof. exact (prop_ext (fun h3 : term52 A u x => @lem3255200 A s t u x h1 h2) (fun h3 : False => @lem3254946 A u x h1)). Qed.
Lemma lem3255212 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A u x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255211 A s t u x h1 h2) (@lem3254946 A u x h1)). Qed.
Lemma lem3255213 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term68 A s t u x) : (term52 A t x) = False.
Proof. exact (prop_ext (fun h3 : term52 A t x => @lem3255202 A s t u x h1 h2) (fun h3 : False => @lem3254930 A t x h1)). Qed.
Lemma lem3255214 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A t x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255213 A s t u x h1 h2) (@lem3254930 A t x h1)). Qed.
Lemma lem3255215 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term68 A s t u x) : (term52 A s x) = False.
Proof. exact (prop_ext (fun h3 : term52 A s x => @lem3255204 A s t u x h1 h2) (fun h3 : False => @lem3254914 A s x h1)). Qed.
Lemma lem3255216 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term52 A s x) (h2 : term68 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255215 A s t u x h1 h2) (@lem3254914 A s x h1)). Qed.
Lemma lem3255217 {A : Type'} (u : A -> Prop) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term65 A s t u x) (h2 : term51 A s t x) : False.
Proof. exact (or_elim (@lem3254895 A s t x h2) (fun h0 : term52 A s x => @lem3255210 A s t u x h0 h1) (fun h0 : term52 A t x => @lem3255208 A s t u x h0 h1)). Qed.
Lemma lem3255218 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term65 A s t u x) : False.
Proof. exact (or_elim (@lem3254890 A s t u x h1) (fun h0 : term51 A s t x => @lem3255217 A u s t x h1 h0) (fun h0 : term52 A u x => @lem3255206 A s t u x h0 h1)). Qed.
Lemma lem3255219 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) (h2 : term51 A t u x) : False.
Proof. exact (or_elim (@lem3254886 A t u x h2) (fun h0 : term52 A t x => @lem3255214 A s t u x h0 h1) (fun h0 : term52 A u x => @lem3255212 A s t u x h0 h1)). Qed.
Lemma lem3255220 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term68 A s t u x) : False.
Proof. exact (or_elim (@lem3254879 A s t u x h1) (fun h0 : term52 A s x => @lem3255216 A s t u x h0 h1) (fun h0 : term51 A t u x => @lem3255219 A s t u x h1 h0)). Qed.
Lemma lem3255221 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term49 A s t u x) : False.
Proof. exact (or_elim (@lem3254876 A s t u x h1) (fun h0 : term68 A s t u x => @lem3255220 A s t u x h0) (fun h0 : term65 A s t u x => @lem3255218 A s t u x h0)). Qed.
Lemma lem3255222 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term49 A s t u x) : (term49 A s t u x) = False.
Proof. exact (prop_ext (fun h2 : term49 A s t u x => @lem3255221 A s t u x h1) (fun h2 : False => @lem3254734 A s t u x h1)). Qed.
Lemma lem3255223 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) (h1 : term49 A s t u x) : False.
Proof. exact (EQ_MP (@lem3255222 A s t u x h1) (@lem3254734 A s t u x h1)). Qed.
Lemma lem3255224 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : term48 A s t u x.
Proof. exact (fun h0 : term49 A s t u x => @lem3255223 A s t u x h0). Qed.
Lemma lem3255225 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) (x : A) : (term25 A s t u x) = (term30 A s t u x).
Proof. exact (EQ_MP (@lem3254733 A s t u x) (@lem3255224 A s t u x)). Qed.
Lemma lem3255230 {A : Type'} (s : A -> Prop) (t : A -> Prop) (u : A -> Prop) : term33 A s t u.
Proof. exact (fun x : A => @lem3255225 A s t u x). Qed.
Lemma lem3255235 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term35 A s t.
Proof. exact (fun u : A -> Prop => @lem3255230 A s t u). Qed.
Lemma lem3255240 {A : Type'} (s : A -> Prop) : term37 A s.
Proof. exact (fun t : A -> Prop => @lem3255235 A s t). Qed.
Lemma lem3255245 {A : Type'} : term39 A.
Proof. exact (fun s : A -> Prop => @lem3255240 A s). Qed.
Lemma lem3255246 {A : Type'} : term41 A.
Proof. exact (EQ_MP (@lem3254729 A) (@lem3255245 A)). Qed.
Lemma lem3255248 {A : Type'} : term41 A.
Proof. exact (@lem3254625 A (@lem3255246 A)). Qed.
Lemma lem3255249 {A : Type'} (h1 : term42 A) : False.
Proof. exact (@lem3255248 A (@lem3254609 A h1)). Qed.
Lemma lem3255250 {A : Type'} (h1 : term42 A) : (term42 A) = False.
Proof. exact (prop_ext (fun h2 : term42 A => @lem3255249 A h1) (fun h2 : False => @lem3254609 A h1)). Qed.
Lemma lem3255251 {A : Type'} (h1 : term42 A) : False.
Proof. exact (EQ_MP (@lem3255250 A h1) (@lem3254609 A h1)). Qed.
Lemma lem3255252 {A : Type'} : term41 A.
Proof. exact (fun h0 : term42 A => @lem3255251 A h0). Qed.
Lemma lem3255253 {A : Type'} : term39 A.
Proof. exact (EQ_MP (@lem3254608 A) (@lem3255252 A)). Qed.
Lemma lem3255254 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem3254604 A) (@lem3255253 A)). Qed.
Lemma lem3255255 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3254481 A) (@lem3255254 A)). Qed.
