Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_ANTISYM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3217421 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3217422 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3217421 A s t). Qed.
Lemma lem3217429 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3217430 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1 A s t) = (term2 A s t).
Proof. exact (MK_COMB (@lem3217429) (@lem3217422 A s t)). Qed.
Lemma lem3217432 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3217433 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3217432 A s t). Qed.
Lemma lem3217434 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term0 A t s).
Proof. exact (@lem3217433 A t s). Qed.
Lemma lem3217441 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term3 A t s) = (term4 A t s).
Proof. exact (MK_COMB (@lem3217430 A s t) (@lem3217434 A t s)). Qed.
Lemma lem3217444 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3217445 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term5 A t s) = (term6 A t s).
Proof. exact (MK_COMB (@lem3217444) (@lem3217441 A t s)). Qed.
Lemma lem3217449 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3217450 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term7 A s t).
Proof. exact (@lem3217449 A s t). Qed.
Lemma lem3217459 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term8 A s t) = (term9 A s t).
Proof. exact (MK_COMB (@lem3217445 A t s) (@lem3217450 A s t)). Qed.
Lemma lem3217462 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3217459 A s t)). Qed.
Lemma lem3217463 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3217464 {A : Type'} (s : A -> Prop) : (term12 A s) = (term13 A s).
Proof. exact (MK_COMB (@lem3217463 A) (@lem3217462 A s)). Qed.
Lemma lem3217469 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3217464 A s)). Qed.
Lemma lem3217470 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3217471 {A : Type'} : (term16 A) = (term17 A).
Proof. exact (MK_COMB (@lem3217470 A) (@lem3217469 A)). Qed.
Lemma lem3217476 {A : Type'} : (term17 A) = (term16 A).
Proof. exact (SYM (@lem3217471 A)). Qed.
Lemma lem3217496 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3217497 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3217496 A P x). Qed.
Lemma lem3217498 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3217497 A s x). Qed.
Lemma lem3217499 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3217500 {A : Type'} (s : A -> Prop) (x : A) : (term18 A x s) = (term19 A s x).
Proof. exact (MK_COMB (@lem3217499) (@lem3217498 A s x)). Qed.
Lemma lem3217502 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3217503 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3217502 A P x). Qed.
Lemma lem3217504 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3217503 A t x). Qed.
Lemma lem3217505 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term20 A s x t) = (term21 A s t x).
Proof. exact (MK_COMB (@lem3217500 A s x) (@lem3217504 A t x)). Qed.
Lemma lem3217508 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term22 A s t) = (term23 A s t).
Proof. exact (fun_ext (fun x : A => @lem3217505 A s t x)). Qed.
Lemma lem3217509 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217510 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term0 A s t) = (term24 A s t).
Proof. exact (MK_COMB (@lem3217509 A) (@lem3217508 A s t)). Qed.
Lemma lem3217515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3217516 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term25 A s t).
Proof. exact (MK_COMB (@lem3217515) (@lem3217510 A s t)). Qed.
Lemma lem3217524 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3217525 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3217524 A P x). Qed.
Lemma lem3217526 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3217525 A t x). Qed.
Lemma lem3217527 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3217528 {A : Type'} (t : A -> Prop) (x : A) : (term18 A x t) = (term19 A t x).
Proof. exact (MK_COMB (@lem3217527) (@lem3217526 A t x)). Qed.
Lemma lem3217530 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3217531 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3217530 A P x). Qed.
Lemma lem3217532 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3217531 A s x). Qed.
Lemma lem3217533 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term20 A t x s) = (term21 A t s x).
Proof. exact (MK_COMB (@lem3217528 A t x) (@lem3217532 A s x)). Qed.
Lemma lem3217536 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term22 A t s) = (term23 A t s).
Proof. exact (fun_ext (fun x : A => @lem3217533 A t s x)). Qed.
Lemma lem3217537 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217538 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term0 A t s) = (term24 A t s).
Proof. exact (MK_COMB (@lem3217537 A) (@lem3217536 A t s)). Qed.
Lemma lem3217543 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term4 A t s) = (term26 A t s).
Proof. exact (MK_COMB (@lem3217516 A s t) (@lem3217538 A t s)). Qed.
Lemma lem3217546 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3217547 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term6 A t s) = (term27 A t s).
Proof. exact (MK_COMB (@lem3217546) (@lem3217543 A t s)). Qed.
Lemma lem3217555 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3217556 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3217555 A P x). Qed.
Lemma lem3217557 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3217556 A s x). Qed.
Lemma lem3217558 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3217559 {A : Type'} (s : A -> Prop) (x : A) : (term28 A x s) = (term29 A s x).
Proof. exact (MK_COMB (@lem3217558) (@lem3217557 A s x)). Qed.
Lemma lem3217561 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3217562 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3217561 A P x). Qed.
Lemma lem3217563 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3217562 A t x). Qed.
Lemma lem3217564 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x t)) = ((s x) = (t x)).
Proof. exact (MK_COMB (@lem3217559 A s x) (@lem3217563 A t x)). Qed.
Lemma lem3217567 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term30 A s t) = (term31 A s t).
Proof. exact (fun_ext (fun x : A => @lem3217564 A s t x)). Qed.
Lemma lem3217568 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217569 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term7 A s t) = (term32 A s t).
Proof. exact (MK_COMB (@lem3217568 A) (@lem3217567 A s t)). Qed.
Lemma lem3217574 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = (term33 A s t).
Proof. exact (MK_COMB (@lem3217547 A t s) (@lem3217569 A s t)). Qed.
Lemma lem3217577 {A : Type'} (s : A -> Prop) : (term11 A s) = (term34 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3217574 A s t)). Qed.
Lemma lem3217578 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3217579 {A : Type'} (s : A -> Prop) : (term13 A s) = (term35 A s).
Proof. exact (MK_COMB (@lem3217578 A) (@lem3217577 A s)). Qed.
Lemma lem3217584 {A : Type'} : (term15 A) = (term36 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3217579 A s)). Qed.
Lemma lem3217585 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3217586 {A : Type'} : (term17 A) = (term37 A).
Proof. exact (MK_COMB (@lem3217585 A) (@lem3217584 A)). Qed.
Lemma lem3217591 {A : Type'} : (term37 A) = (term17 A).
Proof. exact (SYM (@lem3217586 A)). Qed.
Lemma lem3217593 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3217594 {A : Type'} : (term37 A) = (term39 A).
Proof. exact (@lem3217593 (term37 A)). Qed.
Lemma lem3217595 {A : Type'} : (term39 A) = (term37 A).
Proof. exact (SYM (@lem3217594 A)). Qed.
Lemma lem3217596 {A : Type'} (h1 : term40 A) : term40 A.
Proof. exact (h1). Qed.
Lemma lem3217599 {A : Type'} (h1 : term39 A) : term39 A.
Proof. exact (h1). Qed.
Lemma lem3217600 {A : Type'} : term41 A.
Proof. exact (fun h0 : term39 A => @lem3217599 A h0). Qed.
Lemma lem3217601 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (h1). Qed.
Lemma lem3217602 {A : Type'} (h1 : term39 A) : term39 A.
Proof. exact (h1). Qed.
Lemma lem3217603 {A : Type'} (h1 : term39 A) (h2 : term41 A) : term39 A.
Proof. exact (@lem3217601 A h2 (@lem3217602 A h1)). Qed.
Lemma lem3217604 {A : Type'} (h1 : term39 A) : term42 A.
Proof. exact (fun h0 : term41 A => @lem3217603 A h1 h0). Qed.
Lemma lem3217605 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (h1). Qed.
Lemma lem3217606 {A : Type'} (h1 : term39 A) (h2 : term41 A) : term39 A.
Proof. exact (@lem3217604 A h1 (@lem3217605 A h2)). Qed.
Lemma lem3217607 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (fun h0 : term39 A => @lem3217606 A h0 h1). Qed.
Lemma lem3217608 {A : Type'} : term43 A.
Proof. exact (fun h0 : term41 A => @lem3217607 A h0). Qed.
Lemma lem3217611 {A : Type'} : term41 A.
Proof. exact (@lem3217608 A (@lem3217600 A)). Qed.
Lemma lem3217612 {A : Type'} : term41 A.
Proof. exact (@lem3217611 A). Qed.
Lemma lem3217614 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3217615 {A : Type'} : (term39 A) = (term44 A).
Proof. exact (@lem3217614 (term40 A)). Qed.
Lemma lem3217617 (t : Prop) : (term45 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3217618 {A : Type'} : (term44 A) = (term37 A).
Proof. exact (@lem3217617 (term37 A)). Qed.
Lemma lem3217651 {A : Type'} : (term39 A) = (term37 A).
Proof. exact (TRANS (@lem3217615 A) (@lem3217618 A)). Qed.
Lemma lem3217656 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((s x) = (t x)) = ((s x) = (t x)).
Proof. exact (eq_refl ((s x) = (t x))). Qed.
Lemma lem3217657 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term31 A s t) = (term31 A s t).
Proof. exact (fun_ext (fun x : A => @lem3217656 A s t x)). Qed.
Lemma lem3217658 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217659 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = (term32 A s t).
Proof. exact (MK_COMB (@lem3217658 A) (@lem3217657 A s t)). Qed.
Lemma lem3217664 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term21 A t s x) = (term21 A t s x).
Proof. exact (eq_refl (term21 A t s x)). Qed.
Lemma lem3217665 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term23 A t s) = (term23 A t s).
Proof. exact (fun_ext (fun x : A => @lem3217664 A t s x)). Qed.
Lemma lem3217666 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217667 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term24 A t s) = (term24 A t s).
Proof. exact (MK_COMB (@lem3217666 A) (@lem3217665 A t s)). Qed.
Lemma lem3217672 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term21 A s t x) = (term21 A s t x).
Proof. exact (eq_refl (term21 A s t x)). Qed.
Lemma lem3217673 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term23 A s t) = (term23 A s t).
Proof. exact (fun_ext (fun x : A => @lem3217672 A s t x)). Qed.
Lemma lem3217674 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217675 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term24 A s t) = (term24 A s t).
Proof. exact (MK_COMB (@lem3217674 A) (@lem3217673 A s t)). Qed.
Lemma lem3217676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3217677 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term25 A s t) = (term25 A s t).
Proof. exact (MK_COMB (@lem3217676) (@lem3217675 A s t)). Qed.
Lemma lem3217678 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term26 A t s) = (term26 A t s).
Proof. exact (MK_COMB (@lem3217677 A s t) (@lem3217667 A t s)). Qed.
Lemma lem3217679 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3217680 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term27 A t s) = (term27 A t s).
Proof. exact (MK_COMB (@lem3217679) (@lem3217678 A t s)). Qed.
Lemma lem3217681 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term33 A s t).
Proof. exact (MK_COMB (@lem3217680 A t s) (@lem3217659 A s t)). Qed.
Lemma lem3217682 {A : Type'} (s : A -> Prop) : (term34 A s) = (term34 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3217681 A s t)). Qed.
Lemma lem3217683 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3217684 {A : Type'} (s : A -> Prop) : (term35 A s) = (term35 A s).
Proof. exact (MK_COMB (@lem3217683 A) (@lem3217682 A s)). Qed.
Lemma lem3217685 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3217684 A s)). Qed.
Lemma lem3217686 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3217687 {A : Type'} : (term37 A) = (term37 A).
Proof. exact (MK_COMB (@lem3217686 A) (@lem3217685 A)). Qed.
Lemma lem3217728 {A : Type'} : (term39 A) = (term37 A).
Proof. exact (TRANS (@lem3217651 A) (@lem3217687 A)). Qed.
Lemma lem3217729 {A : Type'} : (term37 A) = (term39 A).
Proof. exact (SYM (@lem3217728 A)). Qed.
Lemma lem3217730 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term26 A t s.
Proof. exact (h1). Qed.
Lemma lem3217732 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3217733 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((s x) = (t x)) = (term46 A s t x).
Proof. exact (@lem3217732 ((s x) = (t x))). Qed.
Lemma lem3217734 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term46 A s t x) = ((s x) = (t x)).
Proof. exact (SYM (@lem3217733 A s t x)). Qed.
Lemma lem3217735 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term47 A s t x) : term47 A s t x.
Proof. exact (h1). Qed.
Lemma lem3217742 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term21 A s t x) = (term48 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3217743 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term23 A s t) = (term49 A s t).
Proof. exact (fun_ext (fun x : A => @lem3217742 A s t x)). Qed.
Lemma lem3217744 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217745 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term24 A s t) = (term50 A s t).
Proof. exact (MK_COMB (@lem3217744 A) (@lem3217743 A s t)). Qed.
Lemma lem3217752 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term21 A t s x) = (term48 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem3217753 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term23 A t s) = (term49 A t s).
Proof. exact (fun_ext (fun x : A => @lem3217752 A t s x)). Qed.
Lemma lem3217754 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217755 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term24 A t s) = (term50 A t s).
Proof. exact (MK_COMB (@lem3217754 A) (@lem3217753 A t s)). Qed.
Lemma lem3217756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3217757 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term25 A s t) = (term51 A s t).
Proof. exact (MK_COMB (@lem3217756) (@lem3217745 A s t)). Qed.
Lemma lem3217826 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term26 A t s) = (term52 A t s).
Proof. exact (MK_COMB (@lem3217757 A s t) (@lem3217755 A t s)). Qed.
Lemma lem3217827 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term52 A t s.
Proof. exact (EQ_MP (@lem3217826 A t s) (@lem3217730 A t s h1)). Qed.
Lemma lem3217846 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term47 A s t x) = (term53 A s t x).
Proof. exact (@lem17646 (s x) (t x)). Qed.
Lemma lem3217858 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term48 A t s x) = (term48 A t s x).
Proof. exact (eq_refl (term48 A t s x)). Qed.
Lemma lem3217859 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term49 A t s) = (term49 A t s).
Proof. exact (fun_ext (fun x : A => @lem3217858 A t s x)). Qed.
Lemma lem3217860 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217861 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term50 A t s) = (term50 A t s).
Proof. exact (MK_COMB (@lem3217860 A) (@lem3217859 A t s)). Qed.
Lemma lem3217872 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term48 A s t x) = (term48 A s t x).
Proof. exact (eq_refl (term48 A s t x)). Qed.
Lemma lem3217873 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term49 A s t) = (term49 A s t).
Proof. exact (fun_ext (fun x : A => @lem3217872 A s t x)). Qed.
Lemma lem3217874 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217875 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term50 A s t).
Proof. exact (MK_COMB (@lem3217874 A) (@lem3217873 A s t)). Qed.
Lemma lem3217876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3217877 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term51 A s t) = (term51 A s t).
Proof. exact (MK_COMB (@lem3217876) (@lem3217875 A s t)). Qed.
Lemma lem3217878 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term52 A t s) = (term52 A t s).
Proof. exact (MK_COMB (@lem3217877 A s t) (@lem3217861 A t s)). Qed.
Lemma lem3217879 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term52 A t s.
Proof. exact (EQ_MP (@lem3217878 A t s) (@lem3217827 A t s h1)). Qed.
Lemma lem3217905 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term47 A s t x) : term53 A s t x.
Proof. exact (EQ_MP (@lem3217846 A s t x) (@lem3217735 A s t x h1)). Qed.
Lemma lem3217906 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term50 A t s.
Proof. exact (proj2 (@lem3217879 A t s h1)). Qed.
Lemma lem3217907 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term50 A s t.
Proof. exact (proj1 (@lem3217879 A t s h1)). Qed.
Lemma lem3217908 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term54 A s t x) : term54 A s t x.
Proof. exact (h1). Qed.
Lemma lem3217909 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : term55 A s t x.
Proof. exact (h1). Qed.
Lemma lem3217921 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term48 A s t x) = (term48 A s t x).
Proof. exact (eq_refl (term48 A s t x)). Qed.
Lemma lem3217922 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term49 A s t) = (term49 A s t).
Proof. exact (fun_ext (fun x : A => @lem3217921 A s t x)). Qed.
Lemma lem3217923 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217925 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term50 A s t).
Proof. exact (MK_COMB (@lem3217923 A) (@lem3217922 A s t)). Qed.
Lemma lem3217926 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term50 A s t.
Proof. exact (EQ_MP (@lem3217925 A s t) (@lem3217907 A t s h1)). Qed.
Lemma lem3217968 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term48 A t s x) = (term48 A t s x).
Proof. exact (eq_refl (term48 A t s x)). Qed.
Lemma lem3217969 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term49 A t s) = (term49 A t s).
Proof. exact (fun_ext (fun x : A => @lem3217968 A t s x)). Qed.
Lemma lem3217970 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3217972 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term50 A t s) = (term50 A t s).
Proof. exact (MK_COMB (@lem3217970 A) (@lem3217969 A t s)). Qed.
Lemma lem3217973 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term50 A t s.
Proof. exact (EQ_MP (@lem3217972 A t s) (@lem3217906 A t s h1)). Qed.
Lemma lem3217982 {A : Type'} (_33102 : A) (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term56 A s t _33102.
Proof. exact (@lem3217926 A t s h1 _33102). Qed.
Lemma lem3217983 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33102 : A) : (term56 A s t _33102) = (term48 A s t _33102).
Proof. exact (eq_refl (term56 A s t _33102)). Qed.
Lemma lem3217991 {A : Type'} (_33105 : A) (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term56 A t s _33105.
Proof. exact (@lem3217973 A t s h1 _33105). Qed.
Lemma lem3217992 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33105 : A) : (term56 A t s _33105) = (term48 A t s _33105).
Proof. exact (eq_refl (term56 A t s _33105)). Qed.
Lemma lem3217999 {A : Type'} (_33102 : A) (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term48 A s t _33102.
Proof. exact (EQ_MP (@lem3217983 A s t _33102) (@lem3217982 A _33102 t s h1)). Qed.
Lemma lem3218009 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term54 A s t x) : term57 A t x.
Proof. exact (proj2 (@lem3217908 A s t x h1)). Qed.
Lemma lem3218021 {A : Type'} (_33105 : A) (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term48 A t s _33105.
Proof. exact (EQ_MP (@lem3217992 A t s _33105) (@lem3217991 A _33105 t s h1)). Qed.
Lemma lem3218023 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : term57 A s x.
Proof. exact (proj1 (@lem3217909 A s t x h1)). Qed.
Lemma lem3218027 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term54 A s t x) : s x.
Proof. exact (proj1 (@lem3217908 A s t x h1)). Qed.
Lemma lem3218028 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term54 A s t x) : term58 A s x.
Proof. exact (fun h0 : term57 A s x => @lem3218027 A s t x h1). Qed.
Lemma lem3218030 (p : Prop) : (term59 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3218031 {A : Type'} (s : A -> Prop) (x : A) : (term58 A s x) = (s x).
Proof. exact (@lem3218030 (s x)). Qed.
Lemma lem3218032 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term54 A s t x) : s x.
Proof. exact (EQ_MP (@lem3218031 A s x) (@lem3218028 A s t x h1)). Qed.
Lemma lem3218038 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3218039 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33102 : A) : (term48 A s t _33102) = (term60 A t s _33102).
Proof. exact (@lem3218038 (t _33102) (term57 A s _33102)). Qed.
Lemma lem3218045 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3218046 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33102 : A) : (term61 A s t _33102) = (term62 A t s _33102).
Proof. exact (MK_COMB (@lem3218045) (@lem3218039 A t s _33102)). Qed.
Lemma lem3218052 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33102 : A) : (term60 A t s _33102) = (term60 A t s _33102).
Proof. exact (eq_refl (term60 A t s _33102)). Qed.
Lemma lem3218053 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33102 : A) : ((term48 A s t _33102) = (term60 A t s _33102)) = ((term60 A t s _33102) = (term60 A t s _33102)).
Proof. exact (MK_COMB (@lem3218046 A t s _33102) (@lem3218052 A t s _33102)). Qed.
Lemma lem3218055 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3218056 (x : Prop) : (x = x) = True.
Proof. exact (@lem3218055 Prop x). Qed.
Lemma lem3218057 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33102 : A) : ((term60 A t s _33102) = (term60 A t s _33102)) = True.
Proof. exact (@lem3218056 (term60 A t s _33102)). Qed.
Lemma lem3218058 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33102 : A) : ((term48 A s t _33102) = (term60 A t s _33102)) = True.
Proof. exact (TRANS (@lem3218053 A t s _33102) (@lem3218057 A t s _33102)). Qed.
Lemma lem3218059 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33102 : A) : True = ((term48 A s t _33102) = (term60 A t s _33102)).
Proof. exact (SYM (@lem3218058 A t s _33102)). Qed.
Lemma lem3218060 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33102 : A) : (term48 A s t _33102) = (term60 A t s _33102).
Proof. exact (EQ_MP (@lem3218059 A t s _33102) (@lem0)). Qed.
Lemma lem3218061 {A : Type'} (_33102 : A) (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term60 A t s _33102.
Proof. exact (EQ_MP (@lem3218060 A t s _33102) (@lem3217999 A _33102 t s h1)). Qed.
Lemma lem3218063 (b : Prop) (a : Prop) : (a \/ b) = (term63 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3218064 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33102 : A) : (term60 A t s _33102) = (term64 A s t _33102).
Proof. exact (@lem3218063 (term57 A s _33102) (t _33102)). Qed.
Lemma lem3218066 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3218067 {A : Type'} (s : A -> Prop) (_33102 : A) : (term65 A s _33102) = (s _33102).
Proof. exact (@lem3218066 (s _33102)). Qed.
Lemma lem3218068 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3218069 {A : Type'} (s : A -> Prop) (_33102 : A) : (term66 A s _33102) = (term19 A s _33102).
Proof. exact (MK_COMB (@lem3218068) (@lem3218067 A s _33102)). Qed.
Lemma lem3218070 {A : Type'} (t : A -> Prop) (_33102 : A) : (t _33102) = (t _33102).
Proof. exact (eq_refl (t _33102)). Qed.
Lemma lem3218071 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33102 : A) : (term64 A s t _33102) = (term21 A s t _33102).
Proof. exact (MK_COMB (@lem3218069 A s _33102) (@lem3218070 A t _33102)). Qed.
Lemma lem3218072 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33102 : A) : (term60 A t s _33102) = (term21 A s t _33102).
Proof. exact (TRANS (@lem3218064 A s t _33102) (@lem3218071 A s t _33102)). Qed.
Lemma lem3218075 {A : Type'} (_33102 : A) (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term21 A s t _33102.
Proof. exact (EQ_MP (@lem3218072 A s t _33102) (@lem3218061 A _33102 t s h1)). Qed.
Lemma lem3218076 {A : Type'} (_33102 : A) (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term21 A s t _33102.
Proof. exact (@lem3218075 A _33102 t s h1). Qed.
Lemma lem3218077 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term21 A s t x.
Proof. exact (@lem3218076 A x t s h1). Qed.
Lemma lem3218080 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term26 A t s) (h2 : term54 A s t x) : t x.
Proof. exact (@lem3218077 A x t s h1 (@lem3218032 A s t x h2)). Qed.
Lemma lem3218081 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term26 A t s) (h2 : term54 A s t x) : term58 A t x.
Proof. exact (fun h0 : term57 A t x => @lem3218080 A s t x h1 h2). Qed.
Lemma lem3218083 (p : Prop) : (term59 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3218084 {A : Type'} (t : A -> Prop) (x : A) : (term58 A t x) = (t x).
Proof. exact (@lem3218083 (t x)). Qed.
Lemma lem3218085 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term26 A t s) (h2 : term54 A s t x) : t x.
Proof. exact (EQ_MP (@lem3218084 A t x) (@lem3218081 A s t x h1 h2)). Qed.
Lemma lem3218088 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3218090 {A : Type'} (t : A -> Prop) (x : A) : (term57 A t x) = (term67 A t x).
Proof. exact (@lem3218088 (t x)). Qed.
Lemma lem3218093 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term54 A s t x) : term67 A t x.
Proof. exact (EQ_MP (@lem3218090 A t x) (@lem3218009 A s t x h1)). Qed.
Lemma lem3218096 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term26 A t s) (h2 : term54 A s t x) : False.
Proof. exact (@lem3218093 A s t x h2 (@lem3218085 A s t x h1 h2)). Qed.
Lemma lem3218097 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term26 A t s) (h2 : term54 A s t x) : term68.
Proof. exact (fun h0 : ~ False => @lem3218096 A s t x h1 h2). Qed.
Lemma lem3218099 (p : Prop) : (term59 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3218100 : term68 = False.
Proof. exact (@lem3218099 False). Qed.
Lemma lem3218101 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term26 A t s) (h2 : term54 A s t x) : False.
Proof. exact (EQ_MP (@lem3218100) (@lem3218097 A s t x h1 h2)). Qed.
Lemma lem3218103 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : t x.
Proof. exact (proj2 (@lem3217909 A s t x h1)). Qed.
Lemma lem3218104 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : term58 A t x.
Proof. exact (fun h0 : term57 A t x => @lem3218103 A s t x h1). Qed.
Lemma lem3218106 (p : Prop) : (term59 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3218107 {A : Type'} (t : A -> Prop) (x : A) : (term58 A t x) = (t x).
Proof. exact (@lem3218106 (t x)). Qed.
Lemma lem3218108 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : t x.
Proof. exact (EQ_MP (@lem3218107 A t x) (@lem3218104 A s t x h1)). Qed.
Lemma lem3218114 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3218115 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33105 : A) : (term48 A t s _33105) = (term60 A s t _33105).
Proof. exact (@lem3218114 (s _33105) (term57 A t _33105)). Qed.
Lemma lem3218121 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3218122 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33105 : A) : (term61 A t s _33105) = (term62 A s t _33105).
Proof. exact (MK_COMB (@lem3218121) (@lem3218115 A s t _33105)). Qed.
Lemma lem3218128 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33105 : A) : (term60 A s t _33105) = (term60 A s t _33105).
Proof. exact (eq_refl (term60 A s t _33105)). Qed.
Lemma lem3218129 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33105 : A) : ((term48 A t s _33105) = (term60 A s t _33105)) = ((term60 A s t _33105) = (term60 A s t _33105)).
Proof. exact (MK_COMB (@lem3218122 A s t _33105) (@lem3218128 A s t _33105)). Qed.
Lemma lem3218131 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3218132 (x : Prop) : (x = x) = True.
Proof. exact (@lem3218131 Prop x). Qed.
Lemma lem3218133 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33105 : A) : ((term60 A s t _33105) = (term60 A s t _33105)) = True.
Proof. exact (@lem3218132 (term60 A s t _33105)). Qed.
Lemma lem3218134 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33105 : A) : ((term48 A t s _33105) = (term60 A s t _33105)) = True.
Proof. exact (TRANS (@lem3218129 A s t _33105) (@lem3218133 A s t _33105)). Qed.
Lemma lem3218135 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33105 : A) : True = ((term48 A t s _33105) = (term60 A s t _33105)).
Proof. exact (SYM (@lem3218134 A s t _33105)). Qed.
Lemma lem3218136 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33105 : A) : (term48 A t s _33105) = (term60 A s t _33105).
Proof. exact (EQ_MP (@lem3218135 A s t _33105) (@lem0)). Qed.
Lemma lem3218137 {A : Type'} (_33105 : A) (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term60 A s t _33105.
Proof. exact (EQ_MP (@lem3218136 A s t _33105) (@lem3218021 A _33105 t s h1)). Qed.
Lemma lem3218139 (b : Prop) (a : Prop) : (a \/ b) = (term63 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3218140 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33105 : A) : (term60 A s t _33105) = (term64 A t s _33105).
Proof. exact (@lem3218139 (term57 A t _33105) (s _33105)). Qed.
Lemma lem3218142 (a : Prop) : (term45 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3218143 {A : Type'} (t : A -> Prop) (_33105 : A) : (term65 A t _33105) = (t _33105).
Proof. exact (@lem3218142 (t _33105)). Qed.
Lemma lem3218144 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3218145 {A : Type'} (t : A -> Prop) (_33105 : A) : (term66 A t _33105) = (term19 A t _33105).
Proof. exact (MK_COMB (@lem3218144) (@lem3218143 A t _33105)). Qed.
Lemma lem3218146 {A : Type'} (s : A -> Prop) (_33105 : A) : (s _33105) = (s _33105).
Proof. exact (eq_refl (s _33105)). Qed.
Lemma lem3218147 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33105 : A) : (term64 A t s _33105) = (term21 A t s _33105).
Proof. exact (MK_COMB (@lem3218145 A t _33105) (@lem3218146 A s _33105)). Qed.
Lemma lem3218148 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33105 : A) : (term60 A s t _33105) = (term21 A t s _33105).
Proof. exact (TRANS (@lem3218140 A t s _33105) (@lem3218147 A t s _33105)). Qed.
Lemma lem3218151 {A : Type'} (_33105 : A) (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term21 A t s _33105.
Proof. exact (EQ_MP (@lem3218148 A t s _33105) (@lem3218137 A _33105 t s h1)). Qed.
Lemma lem3218152 {A : Type'} (_33105 : A) (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term21 A t s _33105.
Proof. exact (@lem3218151 A _33105 t s h1). Qed.
Lemma lem3218153 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term21 A t s x.
Proof. exact (@lem3218152 A x t s h1). Qed.
Lemma lem3218156 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term26 A t s) (h2 : term55 A s t x) : s x.
Proof. exact (@lem3218153 A x t s h1 (@lem3218108 A s t x h2)). Qed.
Lemma lem3218157 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term26 A t s) (h2 : term55 A s t x) : term58 A s x.
Proof. exact (fun h0 : term57 A s x => @lem3218156 A s t x h1 h2). Qed.
Lemma lem3218159 (p : Prop) : (term59 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3218160 {A : Type'} (s : A -> Prop) (x : A) : (term58 A s x) = (s x).
Proof. exact (@lem3218159 (s x)). Qed.
Lemma lem3218161 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term26 A t s) (h2 : term55 A s t x) : s x.
Proof. exact (EQ_MP (@lem3218160 A s x) (@lem3218157 A s t x h1 h2)). Qed.
Lemma lem3218164 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3218166 {A : Type'} (s : A -> Prop) (x : A) : (term57 A s x) = (term67 A s x).
Proof. exact (@lem3218164 (s x)). Qed.
Lemma lem3218169 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term55 A s t x) : term67 A s x.
Proof. exact (EQ_MP (@lem3218166 A s x) (@lem3218023 A s t x h1)). Qed.
Lemma lem3218172 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term26 A t s) (h2 : term55 A s t x) : False.
Proof. exact (@lem3218169 A s t x h2 (@lem3218161 A s t x h1 h2)). Qed.
Lemma lem3218173 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term26 A t s) (h2 : term55 A s t x) : term68.
Proof. exact (fun h0 : ~ False => @lem3218172 A s t x h1 h2). Qed.
Lemma lem3218175 (p : Prop) : (term59 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3218176 : term68 = False.
Proof. exact (@lem3218175 False). Qed.
Lemma lem3218177 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term26 A t s) (h2 : term55 A s t x) : False.
Proof. exact (EQ_MP (@lem3218176) (@lem3218173 A s t x h1 h2)). Qed.
Lemma lem3218178 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term47 A s t x) (h2 : term26 A t s) : False.
Proof. exact (or_elim (@lem3217905 A s t x h1) (fun h0 : term54 A s t x => @lem3218101 A s t x h2 h0) (fun h0 : term55 A s t x => @lem3218177 A s t x h2 h0)). Qed.
Lemma lem3218179 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term47 A s t x) (h2 : term26 A t s) : (term47 A s t x) = False.
Proof. exact (prop_ext (fun h3 : term47 A s t x => @lem3218178 A x t s h1 h2) (fun h3 : False => @lem3217735 A s t x h1)). Qed.
Lemma lem3218180 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term47 A s t x) (h2 : term26 A t s) : False.
Proof. exact (EQ_MP (@lem3218179 A x t s h1 h2) (@lem3217735 A s t x h1)). Qed.
Lemma lem3218181 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term46 A s t x.
Proof. exact (fun h0 : term47 A s t x => @lem3218180 A x t s h0 h1). Qed.
Lemma lem3218182 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : (s x) = (t x).
Proof. exact (EQ_MP (@lem3217734 A s t x) (@lem3218181 A x t s h1)). Qed.
Lemma lem3218187 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term26 A t s) : term32 A s t.
Proof. exact (fun x : A => @lem3218182 A x t s h1). Qed.
Lemma lem3218188 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term33 A s t.
Proof. exact (fun h0 : term26 A t s => @lem3218187 A t s h0). Qed.
Lemma lem3218193 {A : Type'} (s : A -> Prop) : term35 A s.
Proof. exact (fun t : A -> Prop => @lem3218188 A s t). Qed.
Lemma lem3218198 {A : Type'} : term37 A.
Proof. exact (fun s : A -> Prop => @lem3218193 A s). Qed.
Lemma lem3218199 {A : Type'} : term39 A.
Proof. exact (EQ_MP (@lem3217729 A) (@lem3218198 A)). Qed.
Lemma lem3218201 {A : Type'} : term39 A.
Proof. exact (@lem3217612 A (@lem3218199 A)). Qed.
Lemma lem3218202 {A : Type'} (h1 : term40 A) : False.
Proof. exact (@lem3218201 A (@lem3217596 A h1)). Qed.
Lemma lem3218203 {A : Type'} (h1 : term40 A) : (term40 A) = False.
Proof. exact (prop_ext (fun h2 : term40 A => @lem3218202 A h1) (fun h2 : False => @lem3217596 A h1)). Qed.
Lemma lem3218204 {A : Type'} (h1 : term40 A) : False.
Proof. exact (EQ_MP (@lem3218203 A h1) (@lem3217596 A h1)). Qed.
Lemma lem3218205 {A : Type'} : term39 A.
Proof. exact (fun h0 : term40 A => @lem3218204 A h0). Qed.
Lemma lem3218206 {A : Type'} : term37 A.
Proof. exact (EQ_MP (@lem3217595 A) (@lem3218205 A)). Qed.
Lemma lem3218207 {A : Type'} : term17 A.
Proof. exact (EQ_MP (@lem3217591 A) (@lem3218206 A)). Qed.
Lemma lem3218208 {A : Type'} : term16 A.
Proof. exact (EQ_MP (@lem3217476 A) (@lem3218207 A)). Qed.
