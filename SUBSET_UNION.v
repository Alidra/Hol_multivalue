Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_UNION_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3233415 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3233416 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3233415 A s t). Qed.
Lemma lem3233417 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1 A s t) = (term2 A s t).
Proof. exact (@lem3233416 A s (@UNION A s t)). Qed.
Lemma lem3233424 {A : Type'} (s : A -> Prop) : (term3 A s) = (term4 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3233417 A s t)). Qed.
Lemma lem3233425 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3233426 {A : Type'} (s : A -> Prop) : (term5 A s) = (term6 A s).
Proof. exact (MK_COMB (@lem3233425 A) (@lem3233424 A s)). Qed.
Lemma lem3233431 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3233426 A s)). Qed.
Lemma lem3233432 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3233433 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem3233432 A) (@lem3233431 A)). Qed.
Lemma lem3233438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3233439 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem3233438) (@lem3233433 A)). Qed.
Lemma lem3233449 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3233450 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3233449 A s t). Qed.
Lemma lem3233451 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term13 A t s) = (term14 A t s).
Proof. exact (@lem3233450 A s (@UNION A t s)). Qed.
Lemma lem3233458 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3233451 A t s)). Qed.
Lemma lem3233459 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3233460 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (MK_COMB (@lem3233459 A) (@lem3233458 A s)). Qed.
Lemma lem3233465 {A : Type'} : (term19 A) = (term20 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3233460 A s)). Qed.
Lemma lem3233466 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3233467 {A : Type'} : (term21 A) = (term22 A).
Proof. exact (MK_COMB (@lem3233466 A) (@lem3233465 A)). Qed.
Lemma lem3233472 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (MK_COMB (@lem3233439 A) (@lem3233467 A)). Qed.
Lemma lem3233475 {A : Type'} : (term24 A) = (term23 A).
Proof. exact (SYM (@lem3233472 A)). Qed.
Lemma lem3233493 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3233494 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3233493 A P x). Qed.
Lemma lem3233495 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3233494 A s x). Qed.
Lemma lem3233496 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3233497 {A : Type'} (s : A -> Prop) (x : A) : (term25 A x s) = (term26 A s x).
Proof. exact (MK_COMB (@lem3233496) (@lem3233495 A s x)). Qed.
Lemma lem3233499 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term27 A x s t) = (term28 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3233500 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term27 A x s t) = (term28 A s x t).
Proof. exact (@lem3233499 A s x t). Qed.
Lemma lem3233504 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3233505 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3233504 A P x). Qed.
Lemma lem3233506 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3233505 A s x). Qed.
Lemma lem3233507 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3233508 {A : Type'} (s : A -> Prop) (x : A) : (term29 A x s) = (term30 A s x).
Proof. exact (MK_COMB (@lem3233507) (@lem3233506 A s x)). Qed.
Lemma lem3233510 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3233511 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3233510 A P x). Qed.
Lemma lem3233512 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3233511 A t x). Qed.
Lemma lem3233513 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term28 A s x t) = (term31 A s t x).
Proof. exact (MK_COMB (@lem3233508 A s x) (@lem3233512 A t x)). Qed.
Lemma lem3233516 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term27 A x s t) = (term31 A s t x).
Proof. exact (TRANS (@lem3233500 A s x t) (@lem3233513 A s t x)). Qed.
Lemma lem3233517 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term32 A x s t) = (term33 A s t x).
Proof. exact (MK_COMB (@lem3233497 A s x) (@lem3233516 A s t x)). Qed.
Lemma lem3233520 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term35 A s t).
Proof. exact (fun_ext (fun x : A => @lem3233517 A s t x)). Qed.
Lemma lem3233521 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3233522 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term36 A s t).
Proof. exact (MK_COMB (@lem3233521 A) (@lem3233520 A s t)). Qed.
Lemma lem3233527 {A : Type'} (s : A -> Prop) : (term4 A s) = (term37 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3233522 A s t)). Qed.
Lemma lem3233528 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3233529 {A : Type'} (s : A -> Prop) : (term6 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem3233528 A) (@lem3233527 A s)). Qed.
Lemma lem3233534 {A : Type'} : (term8 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3233529 A s)). Qed.
Lemma lem3233535 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3233536 {A : Type'} : (term10 A) = (term40 A).
Proof. exact (MK_COMB (@lem3233535 A) (@lem3233534 A)). Qed.
Lemma lem3233541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3233542 {A : Type'} : (term12 A) = (term41 A).
Proof. exact (MK_COMB (@lem3233541) (@lem3233536 A)). Qed.
Lemma lem3233558 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3233559 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3233558 A P x). Qed.
Lemma lem3233560 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3233559 A s x). Qed.
Lemma lem3233561 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3233562 {A : Type'} (s : A -> Prop) (x : A) : (term25 A x s) = (term26 A s x).
Proof. exact (MK_COMB (@lem3233561) (@lem3233560 A s x)). Qed.
Lemma lem3233564 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term27 A x s t) = (term28 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3233565 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term27 A x s t) = (term28 A s x t).
Proof. exact (@lem3233564 A s x t). Qed.
Lemma lem3233566 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) : (term27 A x t s) = (term28 A t x s).
Proof. exact (@lem3233565 A t x s). Qed.
Lemma lem3233570 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3233571 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3233570 A P x). Qed.
Lemma lem3233572 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3233571 A t x). Qed.
Lemma lem3233573 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3233574 {A : Type'} (t : A -> Prop) (x : A) : (term29 A x t) = (term30 A t x).
Proof. exact (MK_COMB (@lem3233573) (@lem3233572 A t x)). Qed.
Lemma lem3233576 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3233577 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3233576 A P x). Qed.
Lemma lem3233578 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3233577 A s x). Qed.
Lemma lem3233579 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term28 A t x s) = (term31 A t s x).
Proof. exact (MK_COMB (@lem3233574 A t x) (@lem3233578 A s x)). Qed.
Lemma lem3233582 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term27 A x t s) = (term31 A t s x).
Proof. exact (TRANS (@lem3233566 A t x s) (@lem3233579 A t s x)). Qed.
Lemma lem3233583 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term42 A x t s) = (term43 A t s x).
Proof. exact (MK_COMB (@lem3233562 A s x) (@lem3233582 A t s x)). Qed.
Lemma lem3233586 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term44 A t s) = (term45 A t s).
Proof. exact (fun_ext (fun x : A => @lem3233583 A t s x)). Qed.
Lemma lem3233587 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3233588 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term14 A t s) = (term46 A t s).
Proof. exact (MK_COMB (@lem3233587 A) (@lem3233586 A t s)). Qed.
Lemma lem3233593 {A : Type'} (s : A -> Prop) : (term16 A s) = (term47 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3233588 A t s)). Qed.
Lemma lem3233594 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3233595 {A : Type'} (s : A -> Prop) : (term18 A s) = (term48 A s).
Proof. exact (MK_COMB (@lem3233594 A) (@lem3233593 A s)). Qed.
Lemma lem3233600 {A : Type'} : (term20 A) = (term49 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3233595 A s)). Qed.
Lemma lem3233601 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3233602 {A : Type'} : (term22 A) = (term50 A).
Proof. exact (MK_COMB (@lem3233601 A) (@lem3233600 A)). Qed.
Lemma lem3233607 {A : Type'} : (term24 A) = (term51 A).
Proof. exact (MK_COMB (@lem3233542 A) (@lem3233602 A)). Qed.
Lemma lem3233610 {A : Type'} : (term51 A) = (term24 A).
Proof. exact (SYM (@lem3233607 A)). Qed.
Lemma lem3233612 (p : Prop) : p = (term52 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3233613 {A : Type'} : (term51 A) = (term53 A).
Proof. exact (@lem3233612 (term51 A)). Qed.
Lemma lem3233614 {A : Type'} : (term53 A) = (term51 A).
Proof. exact (SYM (@lem3233613 A)). Qed.
Lemma lem3233615 {A : Type'} (h1 : term54 A) : term54 A.
Proof. exact (h1). Qed.
Lemma lem3233618 {A : Type'} (h1 : term53 A) : term53 A.
Proof. exact (h1). Qed.
Lemma lem3233619 {A : Type'} : term55 A.
Proof. exact (fun h0 : term53 A => @lem3233618 A h0). Qed.
Lemma lem3233620 {A : Type'} (h1 : term55 A) : term55 A.
Proof. exact (h1). Qed.
Lemma lem3233621 {A : Type'} (h1 : term53 A) : term53 A.
Proof. exact (h1). Qed.
Lemma lem3233622 {A : Type'} (h1 : term53 A) (h2 : term55 A) : term53 A.
Proof. exact (@lem3233620 A h2 (@lem3233621 A h1)). Qed.
Lemma lem3233623 {A : Type'} (h1 : term53 A) : term56 A.
Proof. exact (fun h0 : term55 A => @lem3233622 A h1 h0). Qed.
Lemma lem3233624 {A : Type'} (h1 : term55 A) : term55 A.
Proof. exact (h1). Qed.
Lemma lem3233625 {A : Type'} (h1 : term53 A) (h2 : term55 A) : term53 A.
Proof. exact (@lem3233623 A h1 (@lem3233624 A h2)). Qed.
Lemma lem3233626 {A : Type'} (h1 : term55 A) : term55 A.
Proof. exact (fun h0 : term53 A => @lem3233625 A h0 h1). Qed.
Lemma lem3233627 {A : Type'} : term57 A.
Proof. exact (fun h0 : term55 A => @lem3233626 A h0). Qed.
Lemma lem3233630 {A : Type'} : term55 A.
Proof. exact (@lem3233627 A (@lem3233619 A)). Qed.
Lemma lem3233631 {A : Type'} : term55 A.
Proof. exact (@lem3233630 A). Qed.
Lemma lem3233633 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3233634 {A : Type'} : (term53 A) = (term58 A).
Proof. exact (@lem3233633 (term54 A)). Qed.
Lemma lem3233636 (t : Prop) : (term59 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3233637 {A : Type'} : (term58 A) = (term51 A).
Proof. exact (@lem3233636 (term51 A)). Qed.
Lemma lem3233676 {A : Type'} : (term53 A) = (term51 A).
Proof. exact (TRANS (@lem3233634 A) (@lem3233637 A)). Qed.
Lemma lem3233685 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term43 A t s x) = (term43 A t s x).
Proof. exact (eq_refl (term43 A t s x)). Qed.
Lemma lem3233686 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term45 A t s) = (term45 A t s).
Proof. exact (fun_ext (fun x : A => @lem3233685 A t s x)). Qed.
Lemma lem3233687 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3233688 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term46 A t s) = (term46 A t s).
Proof. exact (MK_COMB (@lem3233687 A) (@lem3233686 A t s)). Qed.
Lemma lem3233689 {A : Type'} (s : A -> Prop) : (term47 A s) = (term47 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3233688 A t s)). Qed.
Lemma lem3233690 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3233691 {A : Type'} (s : A -> Prop) : (term48 A s) = (term48 A s).
Proof. exact (MK_COMB (@lem3233690 A) (@lem3233689 A s)). Qed.
Lemma lem3233692 {A : Type'} : (term49 A) = (term49 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3233691 A s)). Qed.
Lemma lem3233693 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3233694 {A : Type'} : (term50 A) = (term50 A).
Proof. exact (MK_COMB (@lem3233693 A) (@lem3233692 A)). Qed.
Lemma lem3233703 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term33 A s t x) = (term33 A s t x).
Proof. exact (eq_refl (term33 A s t x)). Qed.
Lemma lem3233704 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = (term35 A s t).
Proof. exact (fun_ext (fun x : A => @lem3233703 A s t x)). Qed.
Lemma lem3233705 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3233706 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term36 A s t).
Proof. exact (MK_COMB (@lem3233705 A) (@lem3233704 A s t)). Qed.
Lemma lem3233707 {A : Type'} (s : A -> Prop) : (term37 A s) = (term37 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3233706 A s t)). Qed.
Lemma lem3233708 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3233709 {A : Type'} (s : A -> Prop) : (term38 A s) = (term38 A s).
Proof. exact (MK_COMB (@lem3233708 A) (@lem3233707 A s)). Qed.
Lemma lem3233710 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3233709 A s)). Qed.
Lemma lem3233711 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3233712 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (MK_COMB (@lem3233711 A) (@lem3233710 A)). Qed.
Lemma lem3233713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3233714 {A : Type'} : (term41 A) = (term41 A).
Proof. exact (MK_COMB (@lem3233713) (@lem3233712 A)). Qed.
Lemma lem3233715 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (MK_COMB (@lem3233714 A) (@lem3233694 A)). Qed.
Lemma lem3233764 {A : Type'} : (term53 A) = (term51 A).
Proof. exact (TRANS (@lem3233676 A) (@lem3233715 A)). Qed.
Lemma lem3233765 {A : Type'} : (term51 A) = (term53 A).
Proof. exact (SYM (@lem3233764 A)). Qed.
Lemma lem3233767 (p : Prop) : p = (term52 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3233768 {A : Type'} : (term51 A) = (term53 A).
Proof. exact (@lem3233767 (term51 A)). Qed.
Lemma lem3233769 {A : Type'} : (term53 A) = (term51 A).
Proof. exact (SYM (@lem3233768 A)). Qed.
Lemma lem3233770 {A : Type'} (h1 : term54 A) : term54 A.
Proof. exact (h1). Qed.
Lemma lem3233778 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term60 A s t x) = (term61 A s t x).
Proof. exact (@lem17160 (s x) (t x)). Qed.
Lemma lem3233780 {A : Type'} (s : A -> Prop) (x : A) : (term62 A s x) = (term62 A s x).
Proof. exact (eq_refl (term62 A s x)). Qed.
Lemma lem3233781 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term63 A s t x) = (term64 A s t x).
Proof. exact (MK_COMB (@lem3233780 A s x) (@lem3233778 A s t x)). Qed.
Lemma lem3233782 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term65 A s t x) = (term63 A s t x).
Proof. exact (@lem17362 (s x) (term31 A s t x)). Qed.
Lemma lem3233783 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term65 A s t x) = (term64 A s t x).
Proof. exact (TRANS (@lem3233782 A s t x) (@lem3233781 A s t x)). Qed.
Lemma lem3233784 {A : Type'} (P : A -> Prop) : (term66 A P) = (term67 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3233785 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term68 A s t) = (term69 A s t).
Proof. exact (@lem3233784 A (term35 A s t)). Qed.
Lemma lem3233786 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term70 A s t x) = (term33 A s t x).
Proof. exact (eq_refl (term70 A s t x)). Qed.
Lemma lem3233787 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3233788 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term71 A s t x) = (term65 A s t x).
Proof. exact (MK_COMB (@lem3233787) (@lem3233786 A s t x)). Qed.
Lemma lem3233789 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term71 A s t x) = (term64 A s t x).
Proof. exact (TRANS (@lem3233788 A s t x) (@lem3233783 A s t x)). Qed.
Lemma lem3233790 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term72 A s t) = (term73 A s t).
Proof. exact (fun_ext (fun x : A => @lem3233789 A s t x)). Qed.
Lemma lem3233791 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3233792 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term69 A s t) = (term74 A s t).
Proof. exact (MK_COMB (@lem3233791 A) (@lem3233790 A s t)). Qed.
Lemma lem3233793 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term68 A s t) = (term74 A s t).
Proof. exact (TRANS (@lem3233785 A s t) (@lem3233792 A s t)). Qed.
Lemma lem3233794 {A : Type'} (P : type686 A) : (term75 A P) = (term76 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3233795 {A : Type'} (s : A -> Prop) : (term77 A s) = (term78 A s).
Proof. exact (@lem3233794 A (term37 A s)). Qed.
Lemma lem3233796 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term36 A s t).
Proof. exact (eq_refl (term79 A s t)). Qed.
Lemma lem3233797 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3233798 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term80 A s t) = (term68 A s t).
Proof. exact (MK_COMB (@lem3233797) (@lem3233796 A s t)). Qed.
Lemma lem3233799 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term80 A s t) = (term74 A s t).
Proof. exact (TRANS (@lem3233798 A s t) (@lem3233793 A s t)). Qed.
Lemma lem3233800 {A : Type'} (s : A -> Prop) : (term81 A s) = (term82 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3233799 A s t)). Qed.
Lemma lem3233801 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3233802 {A : Type'} (s : A -> Prop) : (term78 A s) = (term83 A s).
Proof. exact (MK_COMB (@lem3233801 A) (@lem3233800 A s)). Qed.
Lemma lem3233803 {A : Type'} (s : A -> Prop) : (term77 A s) = (term83 A s).
Proof. exact (TRANS (@lem3233795 A s) (@lem3233802 A s)). Qed.
Lemma lem3233804 {A : Type'} (P : type686 A) : (term75 A P) = (term76 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3233805 {A : Type'} : (term84 A) = (term85 A).
Proof. exact (@lem3233804 A (term39 A)). Qed.
Lemma lem3233806 {A : Type'} (s : A -> Prop) : (term86 A s) = (term38 A s).
Proof. exact (eq_refl (term86 A s)). Qed.
Lemma lem3233807 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3233808 {A : Type'} (s : A -> Prop) : (term87 A s) = (term77 A s).
Proof. exact (MK_COMB (@lem3233807) (@lem3233806 A s)). Qed.
Lemma lem3233809 {A : Type'} (s : A -> Prop) : (term87 A s) = (term83 A s).
Proof. exact (TRANS (@lem3233808 A s) (@lem3233803 A s)). Qed.
Lemma lem3233810 {A : Type'} : (term88 A) = (term89 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3233809 A s)). Qed.
Lemma lem3233811 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3233812 {A : Type'} : (term85 A) = (term90 A).
Proof. exact (MK_COMB (@lem3233811 A) (@lem3233810 A)). Qed.
Lemma lem3233813 {A : Type'} : (term84 A) = (term90 A).
Proof. exact (TRANS (@lem3233805 A) (@lem3233812 A)). Qed.
Lemma lem3233821 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term60 A t s x) = (term61 A t s x).
Proof. exact (@lem17160 (t x) (s x)). Qed.
Lemma lem3233823 {A : Type'} (s : A -> Prop) (x : A) : (term62 A s x) = (term62 A s x).
Proof. exact (eq_refl (term62 A s x)). Qed.
Lemma lem3233824 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term91 A t s x) = (term92 A t s x).
Proof. exact (MK_COMB (@lem3233823 A s x) (@lem3233821 A t s x)). Qed.
Lemma lem3233825 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term93 A t s x) = (term91 A t s x).
Proof. exact (@lem17362 (s x) (term31 A t s x)). Qed.
Lemma lem3233826 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term93 A t s x) = (term92 A t s x).
Proof. exact (TRANS (@lem3233825 A t s x) (@lem3233824 A t s x)). Qed.
Lemma lem3233827 {A : Type'} (P : A -> Prop) : (term66 A P) = (term67 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3233828 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term94 A t s) = (term95 A t s).
Proof. exact (@lem3233827 A (term45 A t s)). Qed.
Lemma lem3233829 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term96 A t s x) = (term43 A t s x).
Proof. exact (eq_refl (term96 A t s x)). Qed.
Lemma lem3233830 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3233831 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term97 A t s x) = (term93 A t s x).
Proof. exact (MK_COMB (@lem3233830) (@lem3233829 A t s x)). Qed.
Lemma lem3233832 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term97 A t s x) = (term92 A t s x).
Proof. exact (TRANS (@lem3233831 A t s x) (@lem3233826 A t s x)). Qed.
Lemma lem3233833 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term98 A t s) = (term99 A t s).
Proof. exact (fun_ext (fun x : A => @lem3233832 A t s x)). Qed.
Lemma lem3233834 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3233835 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term95 A t s) = (term100 A t s).
Proof. exact (MK_COMB (@lem3233834 A) (@lem3233833 A t s)). Qed.
Lemma lem3233836 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term94 A t s) = (term100 A t s).
Proof. exact (TRANS (@lem3233828 A t s) (@lem3233835 A t s)). Qed.
Lemma lem3233837 {A : Type'} (P : type686 A) : (term75 A P) = (term76 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3233838 {A : Type'} (s : A -> Prop) : (term101 A s) = (term102 A s).
Proof. exact (@lem3233837 A (term47 A s)). Qed.
Lemma lem3233839 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term103 A s t) = (term46 A t s).
Proof. exact (eq_refl (term103 A s t)). Qed.
Lemma lem3233840 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3233841 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term104 A s t) = (term94 A t s).
Proof. exact (MK_COMB (@lem3233840) (@lem3233839 A t s)). Qed.
Lemma lem3233842 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term104 A s t) = (term100 A t s).
Proof. exact (TRANS (@lem3233841 A t s) (@lem3233836 A t s)). Qed.
Lemma lem3233843 {A : Type'} (s : A -> Prop) : (term105 A s) = (term106 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3233842 A t s)). Qed.
Lemma lem3233844 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3233845 {A : Type'} (s : A -> Prop) : (term102 A s) = (term107 A s).
Proof. exact (MK_COMB (@lem3233844 A) (@lem3233843 A s)). Qed.
Lemma lem3233846 {A : Type'} (s : A -> Prop) : (term101 A s) = (term107 A s).
Proof. exact (TRANS (@lem3233838 A s) (@lem3233845 A s)). Qed.
Lemma lem3233847 {A : Type'} (P : type686 A) : (term75 A P) = (term76 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3233848 {A : Type'} : (term108 A) = (term109 A).
Proof. exact (@lem3233847 A (term49 A)). Qed.
Lemma lem3233849 {A : Type'} (s : A -> Prop) : (term110 A s) = (term48 A s).
Proof. exact (eq_refl (term110 A s)). Qed.
Lemma lem3233850 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3233851 {A : Type'} (s : A -> Prop) : (term111 A s) = (term101 A s).
Proof. exact (MK_COMB (@lem3233850) (@lem3233849 A s)). Qed.
Lemma lem3233852 {A : Type'} (s : A -> Prop) : (term111 A s) = (term107 A s).
Proof. exact (TRANS (@lem3233851 A s) (@lem3233846 A s)). Qed.
Lemma lem3233853 {A : Type'} : (term112 A) = (term113 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3233852 A s)). Qed.
Lemma lem3233854 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3233855 {A : Type'} : (term109 A) = (term114 A).
Proof. exact (MK_COMB (@lem3233854 A) (@lem3233853 A)). Qed.
Lemma lem3233856 {A : Type'} : (term108 A) = (term114 A).
Proof. exact (TRANS (@lem3233848 A) (@lem3233855 A)). Qed.
Lemma lem3233857 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3233858 {A : Type'} : (term115 A) = (term116 A).
Proof. exact (MK_COMB (@lem3233857) (@lem3233813 A)). Qed.
Lemma lem3233859 {A : Type'} : (term117 A) = (term118 A).
Proof. exact (MK_COMB (@lem3233858 A) (@lem3233856 A)). Qed.
Lemma lem3233860 {A : Type'} : (term54 A) = (term117 A).
Proof. exact (@lem17045 (term40 A) (term50 A)). Qed.
Lemma lem3233861 {A : Type'} : (term54 A) = (term118 A).
Proof. exact (TRANS (@lem3233860 A) (@lem3233859 A)). Qed.
Lemma lem3233936 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3233937 {A : Type'} (P : type686 A) (Q : type686 A) : (term121 A P Q) = (term122 A P Q).
Proof. exact (@lem3233936 (A -> Prop) P Q). Qed.
Lemma lem3233938 {A : Type'} : (term123 A) = (term124 A).
Proof. exact (@lem3233937 A (term89 A) (term113 A)). Qed.
Lemma lem3233939 {A : Type'} (s : A -> Prop) : (term125 A s) = (term83 A s).
Proof. exact (eq_refl (term125 A s)). Qed.
Lemma lem3233940 {A : Type'} : (term126 A) = (term89 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3233939 A s)). Qed.
Lemma lem3233941 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3233942 {A : Type'} : (term127 A) = (term90 A).
Proof. exact (MK_COMB (@lem3233941 A) (@lem3233940 A)). Qed.
Lemma lem3233943 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3233944 {A : Type'} : (term128 A) = (term116 A).
Proof. exact (MK_COMB (@lem3233943) (@lem3233942 A)). Qed.
Lemma lem3233945 {A : Type'} (s : A -> Prop) : (term129 A s) = (term107 A s).
Proof. exact (eq_refl (term129 A s)). Qed.
Lemma lem3233946 {A : Type'} : (term130 A) = (term113 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3233945 A s)). Qed.
Lemma lem3233947 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3233948 {A : Type'} : (term131 A) = (term114 A).
Proof. exact (MK_COMB (@lem3233947 A) (@lem3233946 A)). Qed.
Lemma lem3233949 {A : Type'} : (term123 A) = (term118 A).
Proof. exact (MK_COMB (@lem3233944 A) (@lem3233948 A)). Qed.
Lemma lem3233950 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3233951 {A : Type'} : (term132 A) = (term133 A).
Proof. exact (MK_COMB (@lem3233950) (@lem3233949 A)). Qed.
Lemma lem3233952 {A : Type'} (s : A -> Prop) : (term125 A s) = (term83 A s).
Proof. exact (eq_refl (term125 A s)). Qed.
Lemma lem3233953 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3233954 {A : Type'} (s : A -> Prop) : (term134 A s) = (term135 A s).
Proof. exact (MK_COMB (@lem3233953) (@lem3233952 A s)). Qed.
Lemma lem3233955 {A : Type'} (s : A -> Prop) : (term129 A s) = (term107 A s).
Proof. exact (eq_refl (term129 A s)). Qed.
Lemma lem3233956 {A : Type'} (s : A -> Prop) : (term136 A s) = (term137 A s).
Proof. exact (MK_COMB (@lem3233954 A s) (@lem3233955 A s)). Qed.
Lemma lem3233957 {A : Type'} : (term138 A) = (term139 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3233956 A s)). Qed.
Lemma lem3233958 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3233959 {A : Type'} : (term124 A) = (term140 A).
Proof. exact (MK_COMB (@lem3233958 A) (@lem3233957 A)). Qed.
Lemma lem3233960 {A : Type'} : ((term123 A) = (term124 A)) = ((term118 A) = (term140 A)).
Proof. exact (MK_COMB (@lem3233951 A) (@lem3233959 A)). Qed.
Lemma lem3233961 {A : Type'} : (term118 A) = (term140 A).
Proof. exact (EQ_MP (@lem3233960 A) (@lem3233938 A)). Qed.
Lemma lem3233963 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3233964 {A : Type'} (P : type686 A) (Q : type686 A) : (term121 A P Q) = (term122 A P Q).
Proof. exact (@lem3233963 (A -> Prop) P Q). Qed.
Lemma lem3233965 {A : Type'} (s : A -> Prop) : (term141 A s) = (term142 A s).
Proof. exact (@lem3233964 A (term82 A s) (term106 A s)). Qed.
Lemma lem3233966 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term143 A s t) = (term74 A s t).
Proof. exact (eq_refl (term143 A s t)). Qed.
Lemma lem3233967 {A : Type'} (s : A -> Prop) : (term144 A s) = (term82 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3233966 A s t)). Qed.
Lemma lem3233968 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3233969 {A : Type'} (s : A -> Prop) : (term145 A s) = (term83 A s).
Proof. exact (MK_COMB (@lem3233968 A) (@lem3233967 A s)). Qed.
Lemma lem3233970 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3233971 {A : Type'} (s : A -> Prop) : (term146 A s) = (term135 A s).
Proof. exact (MK_COMB (@lem3233970) (@lem3233969 A s)). Qed.
Lemma lem3233972 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term147 A s t) = (term100 A t s).
Proof. exact (eq_refl (term147 A s t)). Qed.
Lemma lem3233973 {A : Type'} (s : A -> Prop) : (term148 A s) = (term106 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3233972 A t s)). Qed.
Lemma lem3233974 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3233975 {A : Type'} (s : A -> Prop) : (term149 A s) = (term107 A s).
Proof. exact (MK_COMB (@lem3233974 A) (@lem3233973 A s)). Qed.
Lemma lem3233976 {A : Type'} (s : A -> Prop) : (term141 A s) = (term137 A s).
Proof. exact (MK_COMB (@lem3233971 A s) (@lem3233975 A s)). Qed.
Lemma lem3233977 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3233978 {A : Type'} (s : A -> Prop) : (term150 A s) = (term151 A s).
Proof. exact (MK_COMB (@lem3233977) (@lem3233976 A s)). Qed.
Lemma lem3233979 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term143 A s t) = (term74 A s t).
Proof. exact (eq_refl (term143 A s t)). Qed.
Lemma lem3233980 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3233981 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term152 A s t) = (term153 A s t).
Proof. exact (MK_COMB (@lem3233980) (@lem3233979 A s t)). Qed.
Lemma lem3233982 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term147 A s t) = (term100 A t s).
Proof. exact (eq_refl (term147 A s t)). Qed.
Lemma lem3233983 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term154 A s t) = (term155 A t s).
Proof. exact (MK_COMB (@lem3233981 A s t) (@lem3233982 A t s)). Qed.
Lemma lem3233984 {A : Type'} (s : A -> Prop) : (term156 A s) = (term157 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3233983 A t s)). Qed.
Lemma lem3233985 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3233986 {A : Type'} (s : A -> Prop) : (term142 A s) = (term158 A s).
Proof. exact (MK_COMB (@lem3233985 A) (@lem3233984 A s)). Qed.
Lemma lem3233987 {A : Type'} (s : A -> Prop) : ((term141 A s) = (term142 A s)) = ((term137 A s) = (term158 A s)).
Proof. exact (MK_COMB (@lem3233978 A s) (@lem3233986 A s)). Qed.
Lemma lem3233988 {A : Type'} (s : A -> Prop) : (term137 A s) = (term158 A s).
Proof. exact (EQ_MP (@lem3233987 A s) (@lem3233965 A s)). Qed.
Lemma lem3233990 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3233991 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (@lem3233990 A P Q). Qed.
Lemma lem3233992 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term159 A t s) = (term160 A t s).
Proof. exact (@lem3233991 A (term73 A s t) (term99 A t s)). Qed.
Lemma lem3233993 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term161 A s t x) = (term64 A s t x).
Proof. exact (eq_refl (term161 A s t x)). Qed.
Lemma lem3233994 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term162 A s t) = (term73 A s t).
Proof. exact (fun_ext (fun x : A => @lem3233993 A s t x)). Qed.
Lemma lem3233995 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3233996 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term163 A s t) = (term74 A s t).
Proof. exact (MK_COMB (@lem3233995 A) (@lem3233994 A s t)). Qed.
Lemma lem3233997 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3233998 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term164 A s t) = (term153 A s t).
Proof. exact (MK_COMB (@lem3233997) (@lem3233996 A s t)). Qed.
Lemma lem3233999 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term165 A t s x) = (term92 A t s x).
Proof. exact (eq_refl (term165 A t s x)). Qed.
Lemma lem3234000 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term166 A t s) = (term99 A t s).
Proof. exact (fun_ext (fun x : A => @lem3233999 A t s x)). Qed.
Lemma lem3234001 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3234002 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term167 A t s) = (term100 A t s).
Proof. exact (MK_COMB (@lem3234001 A) (@lem3234000 A t s)). Qed.
Lemma lem3234003 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term159 A t s) = (term155 A t s).
Proof. exact (MK_COMB (@lem3233998 A s t) (@lem3234002 A t s)). Qed.
Lemma lem3234004 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3234005 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term168 A t s) = (term169 A t s).
Proof. exact (MK_COMB (@lem3234004) (@lem3234003 A t s)). Qed.
Lemma lem3234006 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term161 A s t x) = (term64 A s t x).
Proof. exact (eq_refl (term161 A s t x)). Qed.
Lemma lem3234007 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3234008 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term170 A s t x) = (term171 A s t x).
Proof. exact (MK_COMB (@lem3234007) (@lem3234006 A s t x)). Qed.
Lemma lem3234009 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term165 A t s x) = (term92 A t s x).
Proof. exact (eq_refl (term165 A t s x)). Qed.
Lemma lem3234010 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term172 A t s x) = (term173 A t s x).
Proof. exact (MK_COMB (@lem3234008 A s t x) (@lem3234009 A t s x)). Qed.
Lemma lem3234011 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term174 A t s) = (term175 A t s).
Proof. exact (fun_ext (fun x : A => @lem3234010 A t s x)). Qed.
Lemma lem3234012 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3234013 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term160 A t s) = (term176 A t s).
Proof. exact (MK_COMB (@lem3234012 A) (@lem3234011 A t s)). Qed.
Lemma lem3234014 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term159 A t s) = (term160 A t s)) = ((term155 A t s) = (term176 A t s)).
Proof. exact (MK_COMB (@lem3234005 A t s) (@lem3234013 A t s)). Qed.
Lemma lem3234015 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term155 A t s) = (term176 A t s).
Proof. exact (EQ_MP (@lem3234014 A t s) (@lem3233992 A t s)). Qed.
Lemma lem3234016 {A : Type'} (s : A -> Prop) : (term157 A s) = (term177 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3234015 A t s)). Qed.
Lemma lem3234017 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3234018 {A : Type'} (s : A -> Prop) : (term158 A s) = (term178 A s).
Proof. exact (MK_COMB (@lem3234017 A) (@lem3234016 A s)). Qed.
Lemma lem3234019 {A : Type'} (s : A -> Prop) : (term137 A s) = (term178 A s).
Proof. exact (TRANS (@lem3233988 A s) (@lem3234018 A s)). Qed.
Lemma lem3234020 {A : Type'} : (term139 A) = (term179 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3234019 A s)). Qed.
Lemma lem3234021 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3234022 {A : Type'} : (term140 A) = (term180 A).
Proof. exact (MK_COMB (@lem3234021 A) (@lem3234020 A)). Qed.
Lemma lem3234024 {A : Type'} : (term118 A) = (term180 A).
Proof. exact (TRANS (@lem3233961 A) (@lem3234022 A)). Qed.
Lemma lem3234025 {A : Type'} : (term54 A) = (term180 A).
Proof. exact (TRANS (@lem3233861 A) (@lem3234024 A)). Qed.
Lemma lem3234026 {A : Type'} (h1 : term54 A) : term180 A.
Proof. exact (EQ_MP (@lem3234025 A) (@lem3233770 A h1)). Qed.
Lemma lem3234027 {A : Type'} (s : A -> Prop) (h1 : term178 A s) : term178 A s.
Proof. exact (h1). Qed.
Lemma lem3234028 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term176 A t s) : term176 A t s.
Proof. exact (h1). Qed.
Lemma lem3234071 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term173 A t s x) : term173 A t s x.
Proof. exact (h1). Qed.
Lemma lem3234072 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term64 A s t x) : term64 A s t x.
Proof. exact (h1). Qed.
Lemma lem3234073 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term92 A t s x) : term92 A t s x.
Proof. exact (h1). Qed.
Lemma lem3234074 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term64 A s t x) : term61 A s t x.
Proof. exact (proj2 (@lem3234072 A s t x h1)). Qed.
Lemma lem3234078 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term92 A t s x) : term61 A t s x.
Proof. exact (proj2 (@lem3234073 A t s x h1)). Qed.
Lemma lem3234109 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term64 A s t x) : term181 A s x.
Proof. exact (proj1 (@lem3234074 A s t x h1)). Qed.
Lemma lem3234117 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term92 A t s x) : term181 A s x.
Proof. exact (proj2 (@lem3234078 A t s x h1)). Qed.
Lemma lem3234119 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term64 A s t x) : s x.
Proof. exact (proj1 (@lem3234072 A s t x h1)). Qed.
Lemma lem3234120 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term64 A s t x) : term182 A s x.
Proof. exact (fun h0 : term181 A s x => @lem3234119 A s t x h1). Qed.
Lemma lem3234122 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3234123 {A : Type'} (s : A -> Prop) (x : A) : (term182 A s x) = (s x).
Proof. exact (@lem3234122 (s x)). Qed.
Lemma lem3234124 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term64 A s t x) : s x.
Proof. exact (EQ_MP (@lem3234123 A s x) (@lem3234120 A s t x h1)). Qed.
Lemma lem3234127 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3234129 {A : Type'} (s : A -> Prop) (x : A) : (term181 A s x) = (term184 A s x).
Proof. exact (@lem3234127 (s x)). Qed.
Lemma lem3234132 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term64 A s t x) : term184 A s x.
Proof. exact (EQ_MP (@lem3234129 A s x) (@lem3234109 A s t x h1)). Qed.
Lemma lem3234135 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term64 A s t x) : False.
Proof. exact (@lem3234132 A s t x h1 (@lem3234124 A s t x h1)). Qed.
Lemma lem3234136 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term64 A s t x) : term185.
Proof. exact (fun h0 : ~ False => @lem3234135 A s t x h1). Qed.
Lemma lem3234138 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3234139 : term185 = False.
Proof. exact (@lem3234138 False). Qed.
Lemma lem3234140 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term64 A s t x) : False.
Proof. exact (EQ_MP (@lem3234139) (@lem3234136 A s t x h1)). Qed.
Lemma lem3234142 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term92 A t s x) : s x.
Proof. exact (proj1 (@lem3234073 A t s x h1)). Qed.
Lemma lem3234143 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term92 A t s x) : term182 A s x.
Proof. exact (fun h0 : term181 A s x => @lem3234142 A t s x h1). Qed.
Lemma lem3234145 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3234146 {A : Type'} (s : A -> Prop) (x : A) : (term182 A s x) = (s x).
Proof. exact (@lem3234145 (s x)). Qed.
Lemma lem3234147 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term92 A t s x) : s x.
Proof. exact (EQ_MP (@lem3234146 A s x) (@lem3234143 A t s x h1)). Qed.
Lemma lem3234150 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3234152 {A : Type'} (s : A -> Prop) (x : A) : (term181 A s x) = (term184 A s x).
Proof. exact (@lem3234150 (s x)). Qed.
Lemma lem3234155 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term92 A t s x) : term184 A s x.
Proof. exact (EQ_MP (@lem3234152 A s x) (@lem3234117 A t s x h1)). Qed.
Lemma lem3234158 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term92 A t s x) : False.
Proof. exact (@lem3234155 A t s x h1 (@lem3234147 A t s x h1)). Qed.
Lemma lem3234159 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term92 A t s x) : term185.
Proof. exact (fun h0 : ~ False => @lem3234158 A t s x h1). Qed.
Lemma lem3234161 (p : Prop) : (term183 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3234162 : term185 = False.
Proof. exact (@lem3234161 False). Qed.
Lemma lem3234163 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term92 A t s x) : False.
Proof. exact (EQ_MP (@lem3234162) (@lem3234159 A t s x h1)). Qed.
Lemma lem3234164 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term173 A t s x) : False.
Proof. exact (or_elim (@lem3234071 A t s x h1) (fun h0 : term64 A s t x => @lem3234140 A s t x h0) (fun h0 : term92 A t s x => @lem3234163 A t s x h0)). Qed.
Lemma lem3234165 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term173 A t s x) : (term173 A t s x) = False.
Proof. exact (prop_ext (fun h2 : term173 A t s x => @lem3234164 A t s x h1) (fun h2 : False => @lem3234071 A t s x h1)). Qed.
Lemma lem3234166 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term173 A t s x) : False.
Proof. exact (EQ_MP (@lem3234165 A t s x h1) (@lem3234071 A t s x h1)). Qed.
Lemma lem3234167 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term176 A t s) : False.
Proof. exact (ex_elim (@lem3234028 A t s h1) (fun x : A => fun h0 : term175 A t s x => @lem3234166 A t s x h0)). Qed.
Lemma lem3234168 {A : Type'} (s : A -> Prop) (h1 : term178 A s) : False.
Proof. exact (ex_elim (@lem3234027 A s h1) (fun t : A -> Prop => fun h0 : term177 A s t => @lem3234167 A t s h0)). Qed.
Lemma lem3234169 {A : Type'} (h1 : term54 A) : False.
Proof. exact (ex_elim (@lem3234026 A h1) (fun s : A -> Prop => fun h0 : term179 A s => @lem3234168 A s h0)). Qed.
Lemma lem3234170 {A : Type'} (h1 : term54 A) : (term54 A) = False.
Proof. exact (prop_ext (fun h2 : term54 A => @lem3234169 A h1) (fun h2 : False => @lem3233770 A h1)). Qed.
Lemma lem3234171 {A : Type'} (h1 : term54 A) : False.
Proof. exact (EQ_MP (@lem3234170 A h1) (@lem3233770 A h1)). Qed.
Lemma lem3234172 {A : Type'} : term53 A.
Proof. exact (fun h0 : term54 A => @lem3234171 A h0). Qed.
Lemma lem3234173 {A : Type'} : term51 A.
Proof. exact (EQ_MP (@lem3233769 A) (@lem3234172 A)). Qed.
Lemma lem3234174 {A : Type'} : term53 A.
Proof. exact (EQ_MP (@lem3233765 A) (@lem3234173 A)). Qed.
Lemma lem3234176 {A : Type'} : term53 A.
Proof. exact (@lem3233631 A (@lem3234174 A)). Qed.
Lemma lem3234177 {A : Type'} (h1 : term54 A) : False.
Proof. exact (@lem3234176 A (@lem3233615 A h1)). Qed.
Lemma lem3234178 {A : Type'} (h1 : term54 A) : (term54 A) = False.
Proof. exact (prop_ext (fun h2 : term54 A => @lem3234177 A h1) (fun h2 : False => @lem3233615 A h1)). Qed.
Lemma lem3234179 {A : Type'} (h1 : term54 A) : False.
Proof. exact (EQ_MP (@lem3234178 A h1) (@lem3233615 A h1)). Qed.
Lemma lem3234180 {A : Type'} : term53 A.
Proof. exact (fun h0 : term54 A => @lem3234179 A h0). Qed.
Lemma lem3234181 {A : Type'} : term51 A.
Proof. exact (EQ_MP (@lem3233614 A) (@lem3234180 A)). Qed.
Lemma lem3234182 {A : Type'} : term24 A.
Proof. exact (EQ_MP (@lem3233610 A) (@lem3234181 A)). Qed.
Lemma lem3234183 {A : Type'} : term23 A.
Proof. exact (EQ_MP (@lem3233475 A) (@lem3234182 A)). Qed.
