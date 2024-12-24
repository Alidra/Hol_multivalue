Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PSUBSET_ALT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import PSUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Lemma lem3229325 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3195125 A s). Qed.
Lemma lem3229326 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3229327 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3229326 A s) (@lem3229325 A s)). Qed.
Lemma lem3229328 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3229327 A s t). Qed.
Lemma lem3229329 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = ((@PSUBSET A s t) = (term3 A s t)).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem3229342 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term3 A s t).
Proof. exact (EQ_MP (@lem3229329 A s t) (@lem3229328 A s t)). Qed.
Lemma lem3229343 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term3 A s t).
Proof. exact (@lem3229342 A s t). Qed.
Lemma lem3229348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3229349 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term4 A s t) = (term5 A s t).
Proof. exact (MK_COMB (@lem3229348) (@lem3229343 A s t)). Qed.
Lemma lem3229358 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term6 A t s) = (term6 A t s).
Proof. exact (eq_refl (term6 A t s)). Qed.
Lemma lem3229359 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((@PSUBSET A s t) = (term6 A t s)) = ((term3 A s t) = (term6 A t s)).
Proof. exact (MK_COMB (@lem3229349 A s t) (@lem3229358 A t s)). Qed.
Lemma lem3229362 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3229359 A t s)). Qed.
Lemma lem3229363 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3229364 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (MK_COMB (@lem3229363 A) (@lem3229362 A s)). Qed.
Lemma lem3229369 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3229364 A s)). Qed.
Lemma lem3229370 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3229371 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (MK_COMB (@lem3229370 A) (@lem3229369 A)). Qed.
Lemma lem3229376 {A : Type'} : (term14 A) = (term13 A).
Proof. exact (SYM (@lem3229371 A)). Qed.
Lemma lem3229392 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term15 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3229393 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term15 A s t).
Proof. exact (@lem3229392 A s t). Qed.
Lemma lem3229400 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3229401 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = (term17 A s t).
Proof. exact (MK_COMB (@lem3229400) (@lem3229393 A s t)). Qed.
Lemma lem3229405 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3229406 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term18 A s t).
Proof. exact (@lem3229405 A s t). Qed.
Lemma lem3229415 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3229416 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term19 A s t) = (term20 A s t).
Proof. exact (MK_COMB (@lem3229415) (@lem3229406 A s t)). Qed.
Lemma lem3229417 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term3 A s t) = (term21 A s t).
Proof. exact (MK_COMB (@lem3229401 A s t) (@lem3229416 A s t)). Qed.
Lemma lem3229420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3229421 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term5 A s t) = (term22 A s t).
Proof. exact (MK_COMB (@lem3229420) (@lem3229417 A s t)). Qed.
Lemma lem3229425 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term15 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3229426 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term15 A s t).
Proof. exact (@lem3229425 A s t). Qed.
Lemma lem3229433 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3229434 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = (term17 A s t).
Proof. exact (MK_COMB (@lem3229433) (@lem3229426 A s t)). Qed.
Lemma lem3229441 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term23 A t s) = (term23 A t s).
Proof. exact (eq_refl (term23 A t s)). Qed.
Lemma lem3229442 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term6 A t s) = (term24 A t s).
Proof. exact (MK_COMB (@lem3229434 A s t) (@lem3229441 A t s)). Qed.
Lemma lem3229445 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term3 A s t) = (term6 A t s)) = ((term21 A s t) = (term24 A t s)).
Proof. exact (MK_COMB (@lem3229421 A s t) (@lem3229442 A t s)). Qed.
Lemma lem3229450 {A : Type'} (s : A -> Prop) : (term8 A s) = (term25 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3229445 A t s)). Qed.
Lemma lem3229451 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3229452 {A : Type'} (s : A -> Prop) : (term10 A s) = (term26 A s).
Proof. exact (MK_COMB (@lem3229451 A) (@lem3229450 A s)). Qed.
Lemma lem3229457 {A : Type'} : (term12 A) = (term27 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3229452 A s)). Qed.
Lemma lem3229458 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3229459 {A : Type'} : (term14 A) = (term28 A).
Proof. exact (MK_COMB (@lem3229458 A) (@lem3229457 A)). Qed.
Lemma lem3229464 {A : Type'} : (term28 A) = (term14 A).
Proof. exact (SYM (@lem3229459 A)). Qed.
Lemma lem3229484 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3229485 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3229484 A P x). Qed.
Lemma lem3229486 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3229485 A s x). Qed.
Lemma lem3229487 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3229488 {A : Type'} (s : A -> Prop) (x : A) : (term29 A x s) = (term30 A s x).
Proof. exact (MK_COMB (@lem3229487) (@lem3229486 A s x)). Qed.
Lemma lem3229490 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3229491 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3229490 A P x). Qed.
Lemma lem3229492 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3229491 A t x). Qed.
Lemma lem3229493 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term31 A s x t) = (term32 A s t x).
Proof. exact (MK_COMB (@lem3229488 A s x) (@lem3229492 A t x)). Qed.
Lemma lem3229496 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term34 A s t).
Proof. exact (fun_ext (fun x : A => @lem3229493 A s t x)). Qed.
Lemma lem3229497 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3229498 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term15 A s t) = (term35 A s t).
Proof. exact (MK_COMB (@lem3229497 A) (@lem3229496 A s t)). Qed.
Lemma lem3229503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3229504 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term17 A s t) = (term36 A s t).
Proof. exact (MK_COMB (@lem3229503) (@lem3229498 A s t)). Qed.
Lemma lem3229512 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3229513 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3229512 A P x). Qed.
Lemma lem3229514 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3229513 A s x). Qed.
Lemma lem3229515 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3229516 {A : Type'} (s : A -> Prop) (x : A) : (term37 A x s) = (term38 A s x).
Proof. exact (MK_COMB (@lem3229515) (@lem3229514 A s x)). Qed.
Lemma lem3229518 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3229519 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3229518 A P x). Qed.
Lemma lem3229520 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3229519 A t x). Qed.
Lemma lem3229521 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x t)) = ((s x) = (t x)).
Proof. exact (MK_COMB (@lem3229516 A s x) (@lem3229520 A t x)). Qed.
Lemma lem3229524 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term39 A s t) = (term40 A s t).
Proof. exact (fun_ext (fun x : A => @lem3229521 A s t x)). Qed.
Lemma lem3229525 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3229526 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = (term41 A s t).
Proof. exact (MK_COMB (@lem3229525 A) (@lem3229524 A s t)). Qed.
Lemma lem3229531 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3229532 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term20 A s t) = (term42 A s t).
Proof. exact (MK_COMB (@lem3229531) (@lem3229526 A s t)). Qed.
Lemma lem3229533 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term21 A s t) = (term43 A s t).
Proof. exact (MK_COMB (@lem3229504 A s t) (@lem3229532 A s t)). Qed.
Lemma lem3229536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3229537 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term22 A s t) = (term44 A s t).
Proof. exact (MK_COMB (@lem3229536) (@lem3229533 A s t)). Qed.
Lemma lem3229547 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3229548 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3229547 A P x). Qed.
Lemma lem3229549 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3229548 A s x). Qed.
Lemma lem3229550 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3229551 {A : Type'} (s : A -> Prop) (x : A) : (term29 A x s) = (term30 A s x).
Proof. exact (MK_COMB (@lem3229550) (@lem3229549 A s x)). Qed.
Lemma lem3229553 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3229554 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3229553 A P x). Qed.
Lemma lem3229555 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3229554 A t x). Qed.
Lemma lem3229556 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term31 A s x t) = (term32 A s t x).
Proof. exact (MK_COMB (@lem3229551 A s x) (@lem3229555 A t x)). Qed.
Lemma lem3229559 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term34 A s t).
Proof. exact (fun_ext (fun x : A => @lem3229556 A s t x)). Qed.
Lemma lem3229560 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3229561 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term15 A s t) = (term35 A s t).
Proof. exact (MK_COMB (@lem3229560 A) (@lem3229559 A s t)). Qed.
Lemma lem3229566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3229567 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term17 A s t) = (term36 A s t).
Proof. exact (MK_COMB (@lem3229566) (@lem3229561 A s t)). Qed.
Lemma lem3229575 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3229576 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3229575 A P x). Qed.
Lemma lem3229577 {A : Type'} (t : A -> Prop) (a : A) : (@IN A a t) = (t a).
Proof. exact (@lem3229576 A t a). Qed.
Lemma lem3229578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3229579 {A : Type'} (t : A -> Prop) (a : A) : (term45 A a t) = (term46 A t a).
Proof. exact (MK_COMB (@lem3229578) (@lem3229577 A t a)). Qed.
Lemma lem3229581 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3229582 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3229581 A P x). Qed.
Lemma lem3229583 {A : Type'} (s : A -> Prop) (a : A) : (@IN A a s) = (s a).
Proof. exact (@lem3229582 A s a). Qed.
Lemma lem3229584 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3229585 {A : Type'} (s : A -> Prop) (a : A) : (term47 A a s) = (term48 A s a).
Proof. exact (MK_COMB (@lem3229584) (@lem3229583 A s a)). Qed.
Lemma lem3229586 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term49 A t a s) = (term50 A t s a).
Proof. exact (MK_COMB (@lem3229579 A t a) (@lem3229585 A s a)). Qed.
Lemma lem3229589 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term51 A t s) = (term52 A t s).
Proof. exact (fun_ext (fun a : A => @lem3229586 A t s a)). Qed.
Lemma lem3229590 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3229591 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term23 A t s) = (term53 A t s).
Proof. exact (MK_COMB (@lem3229590 A) (@lem3229589 A t s)). Qed.
Lemma lem3229596 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term24 A t s) = (term54 A t s).
Proof. exact (MK_COMB (@lem3229567 A s t) (@lem3229591 A t s)). Qed.
Lemma lem3229599 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term21 A s t) = (term24 A t s)) = ((term43 A s t) = (term54 A t s)).
Proof. exact (MK_COMB (@lem3229537 A s t) (@lem3229596 A t s)). Qed.
Lemma lem3229602 {A : Type'} (s : A -> Prop) : (term25 A s) = (term55 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3229599 A t s)). Qed.
Lemma lem3229603 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3229604 {A : Type'} (s : A -> Prop) : (term26 A s) = (term56 A s).
Proof. exact (MK_COMB (@lem3229603 A) (@lem3229602 A s)). Qed.
Lemma lem3229609 {A : Type'} : (term27 A) = (term57 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3229604 A s)). Qed.
Lemma lem3229610 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3229611 {A : Type'} : (term28 A) = (term58 A).
Proof. exact (MK_COMB (@lem3229610 A) (@lem3229609 A)). Qed.
Lemma lem3229616 {A : Type'} : (term58 A) = (term28 A).
Proof. exact (SYM (@lem3229611 A)). Qed.
Lemma lem3229618 (p : Prop) : p = (term59 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3229619 {A : Type'} : (term58 A) = (term60 A).
Proof. exact (@lem3229618 (term58 A)). Qed.
Lemma lem3229620 {A : Type'} : (term60 A) = (term58 A).
Proof. exact (SYM (@lem3229619 A)). Qed.
Lemma lem3229621 {A : Type'} (h1 : term61 A) : term61 A.
Proof. exact (h1). Qed.
Lemma lem3229624 {A : Type'} (h1 : term60 A) : term60 A.
Proof. exact (h1). Qed.
Lemma lem3229625 {A : Type'} : term62 A.
Proof. exact (fun h0 : term60 A => @lem3229624 A h0). Qed.
Lemma lem3229626 {A : Type'} (h1 : term62 A) : term62 A.
Proof. exact (h1). Qed.
Lemma lem3229627 {A : Type'} (h1 : term60 A) : term60 A.
Proof. exact (h1). Qed.
Lemma lem3229628 {A : Type'} (h1 : term60 A) (h2 : term62 A) : term60 A.
Proof. exact (@lem3229626 A h2 (@lem3229627 A h1)). Qed.
Lemma lem3229629 {A : Type'} (h1 : term60 A) : term63 A.
Proof. exact (fun h0 : term62 A => @lem3229628 A h1 h0). Qed.
Lemma lem3229630 {A : Type'} (h1 : term62 A) : term62 A.
Proof. exact (h1). Qed.
Lemma lem3229631 {A : Type'} (h1 : term60 A) (h2 : term62 A) : term60 A.
Proof. exact (@lem3229629 A h1 (@lem3229630 A h2)). Qed.
Lemma lem3229632 {A : Type'} (h1 : term62 A) : term62 A.
Proof. exact (fun h0 : term60 A => @lem3229631 A h0 h1). Qed.
Lemma lem3229633 {A : Type'} : term64 A.
Proof. exact (fun h0 : term62 A => @lem3229632 A h0). Qed.
Lemma lem3229636 {A : Type'} : term62 A.
Proof. exact (@lem3229633 A (@lem3229625 A)). Qed.
Lemma lem3229637 {A : Type'} : term62 A.
Proof. exact (@lem3229636 A). Qed.
Lemma lem3229639 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3229640 {A : Type'} : (term60 A) = (term65 A).
Proof. exact (@lem3229639 (term61 A)). Qed.
Lemma lem3229642 (t : Prop) : (term66 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3229643 {A : Type'} : (term65 A) = (term58 A).
Proof. exact (@lem3229642 (term58 A)). Qed.
Lemma lem3229706 {A : Type'} : (term60 A) = (term58 A).
Proof. exact (TRANS (@lem3229640 A) (@lem3229643 A)). Qed.
Lemma lem3229713 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term50 A t s a) = (term50 A t s a).
Proof. exact (eq_refl (term50 A t s a)). Qed.
Lemma lem3229714 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term52 A t s) = (term52 A t s).
Proof. exact (fun_ext (fun a : A => @lem3229713 A t s a)). Qed.
Lemma lem3229715 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3229716 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term53 A t s) = (term53 A t s).
Proof. exact (MK_COMB (@lem3229715 A) (@lem3229714 A t s)). Qed.
Lemma lem3229721 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term32 A s t x) = (term32 A s t x).
Proof. exact (eq_refl (term32 A s t x)). Qed.
Lemma lem3229722 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term34 A s t).
Proof. exact (fun_ext (fun x : A => @lem3229721 A s t x)). Qed.
Lemma lem3229723 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3229724 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = (term35 A s t).
Proof. exact (MK_COMB (@lem3229723 A) (@lem3229722 A s t)). Qed.
Lemma lem3229725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3229726 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term36 A s t).
Proof. exact (MK_COMB (@lem3229725) (@lem3229724 A s t)). Qed.
Lemma lem3229727 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term54 A t s) = (term54 A t s).
Proof. exact (MK_COMB (@lem3229726 A s t) (@lem3229716 A t s)). Qed.
Lemma lem3229732 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((s x) = (t x)) = ((s x) = (t x)).
Proof. exact (eq_refl ((s x) = (t x))). Qed.
Lemma lem3229733 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term40 A s t) = (term40 A s t).
Proof. exact (fun_ext (fun x : A => @lem3229732 A s t x)). Qed.
Lemma lem3229734 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3229735 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term41 A s t) = (term41 A s t).
Proof. exact (MK_COMB (@lem3229734 A) (@lem3229733 A s t)). Qed.
Lemma lem3229736 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3229737 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term42 A s t) = (term42 A s t).
Proof. exact (MK_COMB (@lem3229736) (@lem3229735 A s t)). Qed.
Lemma lem3229742 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term32 A s t x) = (term32 A s t x).
Proof. exact (eq_refl (term32 A s t x)). Qed.
Lemma lem3229743 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term34 A s t).
Proof. exact (fun_ext (fun x : A => @lem3229742 A s t x)). Qed.
Lemma lem3229744 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3229745 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = (term35 A s t).
Proof. exact (MK_COMB (@lem3229744 A) (@lem3229743 A s t)). Qed.
Lemma lem3229746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3229747 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term36 A s t).
Proof. exact (MK_COMB (@lem3229746) (@lem3229745 A s t)). Qed.
Lemma lem3229748 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term43 A s t) = (term43 A s t).
Proof. exact (MK_COMB (@lem3229747 A s t) (@lem3229737 A s t)). Qed.
Lemma lem3229749 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3229750 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term44 A s t) = (term44 A s t).
Proof. exact (MK_COMB (@lem3229749) (@lem3229748 A s t)). Qed.
Lemma lem3229751 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term43 A s t) = (term54 A t s)) = ((term43 A s t) = (term54 A t s)).
Proof. exact (MK_COMB (@lem3229750 A s t) (@lem3229727 A t s)). Qed.
Lemma lem3229752 {A : Type'} (s : A -> Prop) : (term55 A s) = (term55 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3229751 A t s)). Qed.
Lemma lem3229753 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3229754 {A : Type'} (s : A -> Prop) : (term56 A s) = (term56 A s).
Proof. exact (MK_COMB (@lem3229753 A) (@lem3229752 A s)). Qed.
Lemma lem3229755 {A : Type'} : (term57 A) = (term57 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3229754 A s)). Qed.
Lemma lem3229756 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3229757 {A : Type'} : (term58 A) = (term58 A).
Proof. exact (MK_COMB (@lem3229756 A) (@lem3229755 A)). Qed.
Lemma lem3229806 {A : Type'} : (term60 A) = (term58 A).
Proof. exact (TRANS (@lem3229706 A) (@lem3229757 A)). Qed.
Lemma lem3229807 {A : Type'} : (term58 A) = (term60 A).
Proof. exact (SYM (@lem3229806 A)). Qed.
Lemma lem3229809 (p : Prop) : p = (term59 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3229810 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term43 A s t) = (term54 A t s)) = (term67 A t s).
Proof. exact (@lem3229809 ((term43 A s t) = (term54 A t s))). Qed.
Lemma lem3229811 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term67 A t s) = ((term43 A s t) = (term54 A t s)).
Proof. exact (SYM (@lem3229810 A t s)). Qed.
Lemma lem3229812 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term68 A t s) : term68 A t s.
Proof. exact (h1). Qed.
Lemma lem3229821 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term69 A s t x) = (term50 A s t x).
Proof. exact (@lem17362 (s x) (t x)). Qed.
Lemma lem3229826 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term32 A s t x) = (term70 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3229827 {A : Type'} (P : A -> Prop) : (term71 A P) = (term72 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3229828 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term74 A s t).
Proof. exact (@lem3229827 A (term34 A s t)). Qed.
Lemma lem3229829 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term75 A s t x) = (term32 A s t x).
Proof. exact (eq_refl (term75 A s t x)). Qed.
Lemma lem3229830 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3229831 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term76 A s t x) = (term69 A s t x).
Proof. exact (MK_COMB (@lem3229830) (@lem3229829 A s t x)). Qed.
Lemma lem3229832 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term76 A s t x) = (term50 A s t x).
Proof. exact (TRANS (@lem3229831 A s t x) (@lem3229821 A s t x)). Qed.
Lemma lem3229833 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term77 A s t) = (term52 A s t).
Proof. exact (fun_ext (fun x : A => @lem3229832 A s t x)). Qed.
Lemma lem3229834 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3229835 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term74 A s t) = (term53 A s t).
Proof. exact (MK_COMB (@lem3229834 A) (@lem3229833 A s t)). Qed.
Lemma lem3229836 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term53 A s t).
Proof. exact (TRANS (@lem3229828 A s t) (@lem3229835 A s t)). Qed.
Lemma lem3229837 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term78 A s t).
Proof. exact (fun_ext (fun x : A => @lem3229826 A s t x)). Qed.
Lemma lem3229838 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3229839 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = (term79 A s t).
Proof. exact (MK_COMB (@lem3229838 A) (@lem3229837 A s t)). Qed.
Lemma lem3229854 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term80 A s t x) = (term81 A s t x).
Proof. exact (@lem17930 (s x) (t x)). Qed.
Lemma lem3229865 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((s x) = (t x)) = (term82 A s t x).
Proof. exact (@lem17784 (s x) (t x)). Qed.
Lemma lem3229866 {A : Type'} (P : A -> Prop) : (term71 A P) = (term72 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3229867 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term42 A s t) = (term83 A s t).
Proof. exact (@lem3229866 A (term40 A s t)). Qed.
Lemma lem3229868 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term84 A s t x) = ((s x) = (t x)).
Proof. exact (eq_refl (term84 A s t x)). Qed.
Lemma lem3229869 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3229870 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term85 A s t x) = (term80 A s t x).
Proof. exact (MK_COMB (@lem3229869) (@lem3229868 A s t x)). Qed.
Lemma lem3229871 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term85 A s t x) = (term81 A s t x).
Proof. exact (TRANS (@lem3229870 A s t x) (@lem3229854 A s t x)). Qed.
Lemma lem3229872 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term86 A s t) = (term87 A s t).
Proof. exact (fun_ext (fun x : A => @lem3229871 A s t x)). Qed.
Lemma lem3229873 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3229874 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term83 A s t) = (term88 A s t).
Proof. exact (MK_COMB (@lem3229873 A) (@lem3229872 A s t)). Qed.
Lemma lem3229875 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term42 A s t) = (term88 A s t).
Proof. exact (TRANS (@lem3229867 A s t) (@lem3229874 A s t)). Qed.
Lemma lem3229876 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term40 A s t) = (term89 A s t).
Proof. exact (fun_ext (fun x : A => @lem3229865 A s t x)). Qed.
Lemma lem3229877 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3229878 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term41 A s t) = (term90 A s t).
Proof. exact (MK_COMB (@lem3229877 A) (@lem3229876 A s t)). Qed.
Lemma lem3229879 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term91 A s t) = (term41 A s t).
Proof. exact (@lem16933 (term41 A s t)). Qed.
Lemma lem3229880 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term91 A s t) = (term90 A s t).
Proof. exact (TRANS (@lem3229879 A s t) (@lem3229878 A s t)). Qed.
Lemma lem3229881 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3229882 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term92 A s t) = (term93 A s t).
Proof. exact (MK_COMB (@lem3229881) (@lem3229836 A s t)). Qed.
Lemma lem3229883 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term94 A s t) = (term95 A s t).
Proof. exact (MK_COMB (@lem3229882 A s t) (@lem3229880 A s t)). Qed.
Lemma lem3229884 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term96 A s t) = (term94 A s t).
Proof. exact (@lem17045 (term35 A s t) (term42 A s t)). Qed.
Lemma lem3229885 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term96 A s t) = (term95 A s t).
Proof. exact (TRANS (@lem3229884 A s t) (@lem3229883 A s t)). Qed.
Lemma lem3229886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3229887 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term97 A s t).
Proof. exact (MK_COMB (@lem3229886) (@lem3229839 A s t)). Qed.
Lemma lem3229888 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term43 A s t) = (term98 A s t).
Proof. exact (MK_COMB (@lem3229887 A s t) (@lem3229875 A s t)). Qed.
Lemma lem3229897 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term69 A s t x) = (term50 A s t x).
Proof. exact (@lem17362 (s x) (t x)). Qed.
Lemma lem3229902 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term32 A s t x) = (term70 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3229903 {A : Type'} (P : A -> Prop) : (term71 A P) = (term72 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3229904 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term74 A s t).
Proof. exact (@lem3229903 A (term34 A s t)). Qed.
Lemma lem3229905 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term75 A s t x) = (term32 A s t x).
Proof. exact (eq_refl (term75 A s t x)). Qed.
Lemma lem3229906 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3229907 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term76 A s t x) = (term69 A s t x).
Proof. exact (MK_COMB (@lem3229906) (@lem3229905 A s t x)). Qed.
Lemma lem3229908 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term76 A s t x) = (term50 A s t x).
Proof. exact (TRANS (@lem3229907 A s t x) (@lem3229897 A s t x)). Qed.
Lemma lem3229909 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term77 A s t) = (term52 A s t).
Proof. exact (fun_ext (fun x : A => @lem3229908 A s t x)). Qed.
Lemma lem3229910 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3229911 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term74 A s t) = (term53 A s t).
Proof. exact (MK_COMB (@lem3229910 A) (@lem3229909 A s t)). Qed.
Lemma lem3229912 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term53 A s t).
Proof. exact (TRANS (@lem3229904 A s t) (@lem3229911 A s t)). Qed.
Lemma lem3229913 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term78 A s t).
Proof. exact (fun_ext (fun x : A => @lem3229902 A s t x)). Qed.
Lemma lem3229914 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3229915 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = (term79 A s t).
Proof. exact (MK_COMB (@lem3229914 A) (@lem3229913 A s t)). Qed.
Lemma lem3229921 {A : Type'} (s : A -> Prop) (a : A) : (term99 A s a) = (s a).
Proof. exact (@lem16933 (s a)). Qed.
Lemma lem3229923 {A : Type'} (t : A -> Prop) (a : A) : (term100 A t a) = (term100 A t a).
Proof. exact (eq_refl (term100 A t a)). Qed.
Lemma lem3229924 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term101 A t s a) = (term70 A t s a).
Proof. exact (MK_COMB (@lem3229923 A t a) (@lem3229921 A s a)). Qed.
Lemma lem3229925 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term102 A t s a) = (term101 A t s a).
Proof. exact (@lem17045 (t a) (term48 A s a)). Qed.
Lemma lem3229926 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term102 A t s a) = (term70 A t s a).
Proof. exact (TRANS (@lem3229925 A t s a) (@lem3229924 A t s a)). Qed.
Lemma lem3229929 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term50 A t s a) = (term50 A t s a).
Proof. exact (eq_refl (term50 A t s a)). Qed.
Lemma lem3229930 {A : Type'} (P : A -> Prop) : (term103 A P) = (term104 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3229931 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term105 A t s) = (term106 A t s).
Proof. exact (@lem3229930 A (term52 A t s)). Qed.
Lemma lem3229932 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term107 A t s a) = (term50 A t s a).
Proof. exact (eq_refl (term107 A t s a)). Qed.
Lemma lem3229933 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3229934 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term108 A t s a) = (term102 A t s a).
Proof. exact (MK_COMB (@lem3229933) (@lem3229932 A t s a)). Qed.
Lemma lem3229935 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term108 A t s a) = (term70 A t s a).
Proof. exact (TRANS (@lem3229934 A t s a) (@lem3229926 A t s a)). Qed.
Lemma lem3229936 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term109 A t s) = (term78 A t s).
Proof. exact (fun_ext (fun a : A => @lem3229935 A t s a)). Qed.
Lemma lem3229937 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3229938 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term106 A t s) = (term79 A t s).
Proof. exact (MK_COMB (@lem3229937 A) (@lem3229936 A t s)). Qed.
Lemma lem3229939 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term105 A t s) = (term79 A t s).
Proof. exact (TRANS (@lem3229931 A t s) (@lem3229938 A t s)). Qed.
Lemma lem3229940 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term52 A t s) = (term52 A t s).
Proof. exact (fun_ext (fun a : A => @lem3229929 A t s a)). Qed.
Lemma lem3229941 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3229942 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term53 A t s) = (term53 A t s).
Proof. exact (MK_COMB (@lem3229941 A) (@lem3229940 A t s)). Qed.
Lemma lem3229943 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3229944 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term92 A s t) = (term93 A s t).
Proof. exact (MK_COMB (@lem3229943) (@lem3229912 A s t)). Qed.
Lemma lem3229945 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term110 A t s) = (term111 A t s).
Proof. exact (MK_COMB (@lem3229944 A s t) (@lem3229939 A t s)). Qed.
Lemma lem3229946 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term112 A t s) = (term110 A t s).
Proof. exact (@lem17045 (term35 A s t) (term53 A t s)). Qed.
Lemma lem3229947 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term112 A t s) = (term111 A t s).
Proof. exact (TRANS (@lem3229946 A t s) (@lem3229945 A t s)). Qed.
Lemma lem3229948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3229949 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = (term97 A s t).
Proof. exact (MK_COMB (@lem3229948) (@lem3229915 A s t)). Qed.
Lemma lem3229950 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term54 A t s) = (term113 A t s).
Proof. exact (MK_COMB (@lem3229949 A s t) (@lem3229942 A t s)). Qed.
Lemma lem3229951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3229952 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term114 A s t) = (term115 A s t).
Proof. exact (MK_COMB (@lem3229951) (@lem3229885 A s t)). Qed.
Lemma lem3229953 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term116 A t s) = (term117 A t s).
Proof. exact (MK_COMB (@lem3229952 A s t) (@lem3229950 A t s)). Qed.
Lemma lem3229954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3229955 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term118 A s t) = (term119 A s t).
Proof. exact (MK_COMB (@lem3229954) (@lem3229888 A s t)). Qed.
Lemma lem3229956 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term120 A t s) = (term121 A t s).
Proof. exact (MK_COMB (@lem3229955 A s t) (@lem3229947 A t s)). Qed.
Lemma lem3229957 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3229958 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term122 A t s) = (term123 A t s).
Proof. exact (MK_COMB (@lem3229957) (@lem3229956 A t s)). Qed.
Lemma lem3229959 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term124 A t s) = (term125 A t s).
Proof. exact (MK_COMB (@lem3229958 A t s) (@lem3229953 A t s)). Qed.
Lemma lem3229960 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term68 A t s) = (term124 A t s).
Proof. exact (@lem17646 (term43 A s t) (term54 A t s)). Qed.
Lemma lem3229961 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term68 A t s) = (term125 A t s).
Proof. exact (TRANS (@lem3229960 A t s) (@lem3229959 A t s)). Qed.
Lemma lem3230131 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term126 A P Q) = (term127 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3230132 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term126 A P Q) = (term127 A P Q).
Proof. exact (@lem3230131 A P Q). Qed.
Lemma lem3230133 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term128 A s t) = (term129 A s t).
Proof. exact (@lem3230132 A (term130 A s t) (term78 A s t)). Qed.
Lemma lem3230134 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term131 A s t x) = (term132 A s t x).
Proof. exact (eq_refl (term131 A s t x)). Qed.
Lemma lem3230135 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3230136 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term133 A s t x) = (term134 A s t x).
Proof. exact (MK_COMB (@lem3230135) (@lem3230134 A s t x)). Qed.
Lemma lem3230137 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term135 A s t x) = (term70 A s t x).
Proof. exact (eq_refl (term135 A s t x)). Qed.
Lemma lem3230138 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term136 A s t x) = (term82 A s t x).
Proof. exact (MK_COMB (@lem3230136 A s t x) (@lem3230137 A s t x)). Qed.
Lemma lem3230139 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term137 A s t) = (term89 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230138 A s t x)). Qed.
Lemma lem3230140 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3230141 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term128 A s t) = (term90 A s t).
Proof. exact (MK_COMB (@lem3230140 A) (@lem3230139 A s t)). Qed.
Lemma lem3230142 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3230143 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term138 A s t) = (term139 A s t).
Proof. exact (MK_COMB (@lem3230142) (@lem3230141 A s t)). Qed.
Lemma lem3230144 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term131 A s t x) = (term132 A s t x).
Proof. exact (eq_refl (term131 A s t x)). Qed.
Lemma lem3230145 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term140 A s t) = (term130 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230144 A s t x)). Qed.
Lemma lem3230146 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3230147 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term141 A s t) = (term142 A s t).
Proof. exact (MK_COMB (@lem3230146 A) (@lem3230145 A s t)). Qed.
Lemma lem3230148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3230149 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term143 A s t) = (term144 A s t).
Proof. exact (MK_COMB (@lem3230148) (@lem3230147 A s t)). Qed.
Lemma lem3230150 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term135 A s t x) = (term70 A s t x).
Proof. exact (eq_refl (term135 A s t x)). Qed.
Lemma lem3230151 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term145 A s t) = (term78 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230150 A s t x)). Qed.
Lemma lem3230152 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3230153 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term146 A s t) = (term79 A s t).
Proof. exact (MK_COMB (@lem3230152 A) (@lem3230151 A s t)). Qed.
Lemma lem3230154 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term129 A s t) = (term147 A s t).
Proof. exact (MK_COMB (@lem3230149 A s t) (@lem3230153 A s t)). Qed.
Lemma lem3230155 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term128 A s t) = (term129 A s t)) = ((term90 A s t) = (term147 A s t)).
Proof. exact (MK_COMB (@lem3230143 A s t) (@lem3230154 A s t)). Qed.
Lemma lem3230156 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term90 A s t) = (term147 A s t).
Proof. exact (EQ_MP (@lem3230155 A s t) (@lem3230133 A s t)). Qed.
Lemma lem3230217 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term93 A s t) = (term93 A s t).
Proof. exact (eq_refl (term93 A s t)). Qed.
Lemma lem3230218 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term95 A s t) = (term148 A s t).
Proof. exact (MK_COMB (@lem3230217 A s t) (@lem3230156 A s t)). Qed.
Lemma lem3230219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3230220 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term115 A s t) = (term149 A s t).
Proof. exact (MK_COMB (@lem3230219) (@lem3230218 A s t)). Qed.
Lemma lem3230281 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term113 A t s) = (term113 A t s).
Proof. exact (eq_refl (term113 A t s)). Qed.
Lemma lem3230282 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term117 A t s) = (term150 A t s).
Proof. exact (MK_COMB (@lem3230220 A s t) (@lem3230281 A t s)). Qed.
Lemma lem3230283 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term123 A t s) = (term123 A t s).
Proof. exact (eq_refl (term123 A t s)). Qed.
Lemma lem3230284 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term125 A t s) = (term151 A t s).
Proof. exact (MK_COMB (@lem3230283 A t s) (@lem3230282 A t s)). Qed.
Lemma lem3230286 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3230287 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (@lem3230286 A P Q). Qed.
Lemma lem3230288 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term154 A s t) = (term155 A s t).
Proof. exact (@lem3230287 A (term79 A s t) (term87 A s t)). Qed.
Lemma lem3230289 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term156 A s t x) = (term81 A s t x).
Proof. exact (eq_refl (term156 A s t x)). Qed.
Lemma lem3230290 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term157 A s t) = (term87 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230289 A s t x)). Qed.
Lemma lem3230291 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230292 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term158 A s t) = (term88 A s t).
Proof. exact (MK_COMB (@lem3230291 A) (@lem3230290 A s t)). Qed.
Lemma lem3230293 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term97 A s t) = (term97 A s t).
Proof. exact (eq_refl (term97 A s t)). Qed.
Lemma lem3230294 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term154 A s t) = (term98 A s t).
Proof. exact (MK_COMB (@lem3230293 A s t) (@lem3230292 A s t)). Qed.
Lemma lem3230295 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3230296 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term159 A s t) = (term160 A s t).
Proof. exact (MK_COMB (@lem3230295) (@lem3230294 A s t)). Qed.
Lemma lem3230297 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term156 A s t x) = (term81 A s t x).
Proof. exact (eq_refl (term156 A s t x)). Qed.
Lemma lem3230298 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term97 A s t) = (term97 A s t).
Proof. exact (eq_refl (term97 A s t)). Qed.
Lemma lem3230299 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term161 A s t x) = (term162 A s t x).
Proof. exact (MK_COMB (@lem3230298 A s t) (@lem3230297 A s t x)). Qed.
Lemma lem3230300 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term163 A s t) = (term164 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230299 A s t x)). Qed.
Lemma lem3230301 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230302 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term155 A s t) = (term165 A s t).
Proof. exact (MK_COMB (@lem3230301 A) (@lem3230300 A s t)). Qed.
Lemma lem3230303 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term154 A s t) = (term155 A s t)) = ((term98 A s t) = (term165 A s t)).
Proof. exact (MK_COMB (@lem3230296 A s t) (@lem3230302 A s t)). Qed.
Lemma lem3230304 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term98 A s t) = (term165 A s t).
Proof. exact (EQ_MP (@lem3230303 A s t) (@lem3230288 A s t)). Qed.
Lemma lem3230305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3230306 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term119 A s t) = (term166 A s t).
Proof. exact (MK_COMB (@lem3230305) (@lem3230304 A s t)). Qed.
Lemma lem3230308 {A : Type'} (P : A -> Prop) (Q : Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3230309 {A : Type'} (P : A -> Prop) (Q : Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (@lem3230308 A P Q). Qed.
Lemma lem3230310 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term169 A t s) = (term170 A t s).
Proof. exact (@lem3230309 A (term52 A s t) (term79 A t s)). Qed.
Lemma lem3230311 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term107 A s t x) = (term50 A s t x).
Proof. exact (eq_refl (term107 A s t x)). Qed.
Lemma lem3230312 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term171 A s t) = (term52 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230311 A s t x)). Qed.
Lemma lem3230313 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230314 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term172 A s t) = (term53 A s t).
Proof. exact (MK_COMB (@lem3230313 A) (@lem3230312 A s t)). Qed.
Lemma lem3230315 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3230316 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term173 A s t) = (term93 A s t).
Proof. exact (MK_COMB (@lem3230315) (@lem3230314 A s t)). Qed.
Lemma lem3230317 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term79 A t s) = (term79 A t s).
Proof. exact (eq_refl (term79 A t s)). Qed.
Lemma lem3230318 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term169 A t s) = (term111 A t s).
Proof. exact (MK_COMB (@lem3230316 A s t) (@lem3230317 A t s)). Qed.
Lemma lem3230319 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3230320 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term174 A t s) = (term175 A t s).
Proof. exact (MK_COMB (@lem3230319) (@lem3230318 A t s)). Qed.
Lemma lem3230321 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term107 A s t x) = (term50 A s t x).
Proof. exact (eq_refl (term107 A s t x)). Qed.
Lemma lem3230322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3230323 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term176 A s t x) = (term177 A s t x).
Proof. exact (MK_COMB (@lem3230322) (@lem3230321 A s t x)). Qed.
Lemma lem3230324 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term79 A t s) = (term79 A t s).
Proof. exact (eq_refl (term79 A t s)). Qed.
Lemma lem3230325 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term178 A x t s) = (term179 A x t s).
Proof. exact (MK_COMB (@lem3230323 A s t x) (@lem3230324 A t s)). Qed.
Lemma lem3230326 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term180 A t s) = (term181 A t s).
Proof. exact (fun_ext (fun x : A => @lem3230325 A x t s)). Qed.
Lemma lem3230327 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230328 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term170 A t s) = (term182 A t s).
Proof. exact (MK_COMB (@lem3230327 A) (@lem3230326 A t s)). Qed.
Lemma lem3230329 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term169 A t s) = (term170 A t s)) = ((term111 A t s) = (term182 A t s)).
Proof. exact (MK_COMB (@lem3230320 A t s) (@lem3230328 A t s)). Qed.
Lemma lem3230330 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term111 A t s) = (term182 A t s).
Proof. exact (EQ_MP (@lem3230329 A t s) (@lem3230310 A t s)). Qed.
Lemma lem3230331 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term121 A t s) = (term183 A t s).
Proof. exact (MK_COMB (@lem3230306 A s t) (@lem3230330 A t s)). Qed.
Lemma lem3230333 {A : Type'} (P : A -> Prop) (Q : Prop) : (term184 A P Q) = (term185 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3230334 {A : Type'} (P : A -> Prop) (Q : Prop) : (term184 A P Q) = (term185 A P Q).
Proof. exact (@lem3230333 A P Q). Qed.
Lemma lem3230335 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term186 A t s) = (term187 A t s).
Proof. exact (@lem3230334 A (term164 A s t) (term182 A t s)). Qed.
Lemma lem3230336 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term188 A s t x) = (term162 A s t x).
Proof. exact (eq_refl (term188 A s t x)). Qed.
Lemma lem3230337 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term189 A s t) = (term164 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230336 A s t x)). Qed.
Lemma lem3230338 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230339 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term190 A s t) = (term165 A s t).
Proof. exact (MK_COMB (@lem3230338 A) (@lem3230337 A s t)). Qed.
Lemma lem3230340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3230341 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term191 A s t) = (term166 A s t).
Proof. exact (MK_COMB (@lem3230340) (@lem3230339 A s t)). Qed.
Lemma lem3230342 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term182 A t s) = (term182 A t s).
Proof. exact (eq_refl (term182 A t s)). Qed.
Lemma lem3230343 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term186 A t s) = (term183 A t s).
Proof. exact (MK_COMB (@lem3230341 A s t) (@lem3230342 A t s)). Qed.
Lemma lem3230344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3230345 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term192 A t s) = (term193 A t s).
Proof. exact (MK_COMB (@lem3230344) (@lem3230343 A t s)). Qed.
Lemma lem3230346 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term188 A s t x) = (term162 A s t x).
Proof. exact (eq_refl (term188 A s t x)). Qed.
Lemma lem3230347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3230348 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term194 A s t x) = (term195 A s t x).
Proof. exact (MK_COMB (@lem3230347) (@lem3230346 A s t x)). Qed.
Lemma lem3230349 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term182 A t s) = (term182 A t s).
Proof. exact (eq_refl (term182 A t s)). Qed.
Lemma lem3230350 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term196 A x t s) = (term197 A x t s).
Proof. exact (MK_COMB (@lem3230348 A s t x) (@lem3230349 A t s)). Qed.
Lemma lem3230351 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term198 A t s) = (term199 A t s).
Proof. exact (fun_ext (fun x : A => @lem3230350 A x t s)). Qed.
Lemma lem3230352 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230353 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term187 A t s) = (term200 A t s).
Proof. exact (MK_COMB (@lem3230352 A) (@lem3230351 A t s)). Qed.
Lemma lem3230354 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term186 A t s) = (term187 A t s)) = ((term183 A t s) = (term200 A t s)).
Proof. exact (MK_COMB (@lem3230345 A t s) (@lem3230353 A t s)). Qed.
Lemma lem3230355 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term183 A t s) = (term200 A t s).
Proof. exact (EQ_MP (@lem3230354 A t s) (@lem3230335 A t s)). Qed.
Lemma lem3230357 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3230358 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (@lem3230357 A P Q). Qed.
Lemma lem3230359 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term201 A x t s) = (term202 A x t s).
Proof. exact (@lem3230358 A (term162 A s t x) (term181 A t s)). Qed.
Lemma lem3230360 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term203 A t s x) = (term179 A x t s).
Proof. exact (eq_refl (term203 A t s x)). Qed.
Lemma lem3230361 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term204 A t s) = (term181 A t s).
Proof. exact (fun_ext (fun x : A => @lem3230360 A x t s)). Qed.
Lemma lem3230362 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230363 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term205 A t s) = (term182 A t s).
Proof. exact (MK_COMB (@lem3230362 A) (@lem3230361 A t s)). Qed.
Lemma lem3230364 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term195 A s t x) = (term195 A s t x).
Proof. exact (eq_refl (term195 A s t x)). Qed.
Lemma lem3230365 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term201 A x t s) = (term197 A x t s).
Proof. exact (MK_COMB (@lem3230364 A s t x) (@lem3230363 A t s)). Qed.
Lemma lem3230366 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3230367 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term206 A x t s) = (term207 A x t s).
Proof. exact (MK_COMB (@lem3230366) (@lem3230365 A x t s)). Qed.
Lemma lem3230368 {A : Type'} (x' : A) (t : A -> Prop) (s : A -> Prop) : (term203 A t s x') = (term179 A x' t s).
Proof. exact (eq_refl (term203 A t s x')). Qed.
Lemma lem3230369 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term195 A s t x) = (term195 A s t x).
Proof. exact (eq_refl (term195 A s t x)). Qed.
Lemma lem3230370 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) : (term208 A x t s x') = (term209 A x x' t s).
Proof. exact (MK_COMB (@lem3230369 A s t x) (@lem3230368 A x' t s)). Qed.
Lemma lem3230371 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term210 A x t s) = (term211 A x t s).
Proof. exact (fun_ext (fun x' : A => @lem3230370 A x x' t s)). Qed.
Lemma lem3230372 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230373 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term202 A x t s) = (term212 A x t s).
Proof. exact (MK_COMB (@lem3230372 A) (@lem3230371 A x t s)). Qed.
Lemma lem3230374 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : ((term201 A x t s) = (term202 A x t s)) = ((term197 A x t s) = (term212 A x t s)).
Proof. exact (MK_COMB (@lem3230367 A x t s) (@lem3230373 A x t s)). Qed.
Lemma lem3230375 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term197 A x t s) = (term212 A x t s).
Proof. exact (EQ_MP (@lem3230374 A x t s) (@lem3230359 A x t s)). Qed.
Lemma lem3230376 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term199 A t s) = (term213 A t s).
Proof. exact (fun_ext (fun x : A => @lem3230375 A x t s)). Qed.
Lemma lem3230377 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230378 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term200 A t s) = (term214 A t s).
Proof. exact (MK_COMB (@lem3230377 A) (@lem3230376 A t s)). Qed.
Lemma lem3230379 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term183 A t s) = (term214 A t s).
Proof. exact (TRANS (@lem3230355 A t s) (@lem3230378 A t s)). Qed.
Lemma lem3230380 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term121 A t s) = (term214 A t s).
Proof. exact (TRANS (@lem3230331 A t s) (@lem3230379 A t s)). Qed.
Lemma lem3230381 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3230382 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term123 A t s) = (term215 A t s).
Proof. exact (MK_COMB (@lem3230381) (@lem3230380 A t s)). Qed.
Lemma lem3230384 {A : Type'} (P : A -> Prop) (Q : Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3230385 {A : Type'} (P : A -> Prop) (Q : Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (@lem3230384 A P Q). Qed.
Lemma lem3230386 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term216 A s t) = (term217 A s t).
Proof. exact (@lem3230385 A (term52 A s t) (term147 A s t)). Qed.
Lemma lem3230387 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term107 A s t x) = (term50 A s t x).
Proof. exact (eq_refl (term107 A s t x)). Qed.
Lemma lem3230388 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term171 A s t) = (term52 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230387 A s t x)). Qed.
Lemma lem3230389 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230390 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term172 A s t) = (term53 A s t).
Proof. exact (MK_COMB (@lem3230389 A) (@lem3230388 A s t)). Qed.
Lemma lem3230391 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3230392 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term173 A s t) = (term93 A s t).
Proof. exact (MK_COMB (@lem3230391) (@lem3230390 A s t)). Qed.
Lemma lem3230393 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term147 A s t) = (term147 A s t).
Proof. exact (eq_refl (term147 A s t)). Qed.
Lemma lem3230394 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term216 A s t) = (term148 A s t).
Proof. exact (MK_COMB (@lem3230392 A s t) (@lem3230393 A s t)). Qed.
Lemma lem3230395 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3230396 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term218 A s t) = (term219 A s t).
Proof. exact (MK_COMB (@lem3230395) (@lem3230394 A s t)). Qed.
Lemma lem3230397 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term107 A s t x) = (term50 A s t x).
Proof. exact (eq_refl (term107 A s t x)). Qed.
Lemma lem3230398 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3230399 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term176 A s t x) = (term177 A s t x).
Proof. exact (MK_COMB (@lem3230398) (@lem3230397 A s t x)). Qed.
Lemma lem3230400 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term147 A s t) = (term147 A s t).
Proof. exact (eq_refl (term147 A s t)). Qed.
Lemma lem3230401 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term220 A x s t) = (term221 A x s t).
Proof. exact (MK_COMB (@lem3230399 A s t x) (@lem3230400 A s t)). Qed.
Lemma lem3230402 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term222 A s t) = (term223 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230401 A x s t)). Qed.
Lemma lem3230403 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230404 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term217 A s t) = (term224 A s t).
Proof. exact (MK_COMB (@lem3230403 A) (@lem3230402 A s t)). Qed.
Lemma lem3230405 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term216 A s t) = (term217 A s t)) = ((term148 A s t) = (term224 A s t)).
Proof. exact (MK_COMB (@lem3230396 A s t) (@lem3230404 A s t)). Qed.
Lemma lem3230406 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term148 A s t) = (term224 A s t).
Proof. exact (EQ_MP (@lem3230405 A s t) (@lem3230386 A s t)). Qed.
Lemma lem3230407 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3230408 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term149 A s t) = (term225 A s t).
Proof. exact (MK_COMB (@lem3230407) (@lem3230406 A s t)). Qed.
Lemma lem3230410 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3230411 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (@lem3230410 A P Q). Qed.
Lemma lem3230412 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term226 A t s) = (term227 A t s).
Proof. exact (@lem3230411 A (term79 A s t) (term52 A t s)). Qed.
Lemma lem3230413 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term107 A t s a) = (term50 A t s a).
Proof. exact (eq_refl (term107 A t s a)). Qed.
Lemma lem3230414 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term171 A t s) = (term52 A t s).
Proof. exact (fun_ext (fun a : A => @lem3230413 A t s a)). Qed.
Lemma lem3230415 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230416 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term172 A t s) = (term53 A t s).
Proof. exact (MK_COMB (@lem3230415 A) (@lem3230414 A t s)). Qed.
Lemma lem3230417 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term97 A s t) = (term97 A s t).
Proof. exact (eq_refl (term97 A s t)). Qed.
Lemma lem3230418 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term226 A t s) = (term113 A t s).
Proof. exact (MK_COMB (@lem3230417 A s t) (@lem3230416 A t s)). Qed.
Lemma lem3230419 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3230420 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term228 A t s) = (term229 A t s).
Proof. exact (MK_COMB (@lem3230419) (@lem3230418 A t s)). Qed.
Lemma lem3230421 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term107 A t s a) = (term50 A t s a).
Proof. exact (eq_refl (term107 A t s a)). Qed.
Lemma lem3230422 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term97 A s t) = (term97 A s t).
Proof. exact (eq_refl (term97 A s t)). Qed.
Lemma lem3230423 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term230 A t s a) = (term231 A t s a).
Proof. exact (MK_COMB (@lem3230422 A s t) (@lem3230421 A t s a)). Qed.
Lemma lem3230424 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term232 A t s) = (term233 A t s).
Proof. exact (fun_ext (fun a : A => @lem3230423 A t s a)). Qed.
Lemma lem3230425 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230426 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term227 A t s) = (term234 A t s).
Proof. exact (MK_COMB (@lem3230425 A) (@lem3230424 A t s)). Qed.
Lemma lem3230427 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term226 A t s) = (term227 A t s)) = ((term113 A t s) = (term234 A t s)).
Proof. exact (MK_COMB (@lem3230420 A t s) (@lem3230426 A t s)). Qed.
Lemma lem3230428 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term113 A t s) = (term234 A t s).
Proof. exact (EQ_MP (@lem3230427 A t s) (@lem3230412 A t s)). Qed.
Lemma lem3230429 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term150 A t s) = (term235 A t s).
Proof. exact (MK_COMB (@lem3230408 A s t) (@lem3230428 A t s)). Qed.
Lemma lem3230431 {A : Type'} (P : A -> Prop) (Q : Prop) : (term184 A P Q) = (term185 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3230432 {A : Type'} (P : A -> Prop) (Q : Prop) : (term184 A P Q) = (term185 A P Q).
Proof. exact (@lem3230431 A P Q). Qed.
Lemma lem3230433 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term236 A t s) = (term237 A t s).
Proof. exact (@lem3230432 A (term223 A s t) (term234 A t s)). Qed.
Lemma lem3230434 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term238 A s t x) = (term221 A x s t).
Proof. exact (eq_refl (term238 A s t x)). Qed.
Lemma lem3230435 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term239 A s t) = (term223 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230434 A x s t)). Qed.
Lemma lem3230436 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230437 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term240 A s t) = (term224 A s t).
Proof. exact (MK_COMB (@lem3230436 A) (@lem3230435 A s t)). Qed.
Lemma lem3230438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3230439 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term241 A s t) = (term225 A s t).
Proof. exact (MK_COMB (@lem3230438) (@lem3230437 A s t)). Qed.
Lemma lem3230440 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term234 A t s) = (term234 A t s).
Proof. exact (eq_refl (term234 A t s)). Qed.
Lemma lem3230441 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term236 A t s) = (term235 A t s).
Proof. exact (MK_COMB (@lem3230439 A s t) (@lem3230440 A t s)). Qed.
Lemma lem3230442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3230443 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term242 A t s) = (term243 A t s).
Proof. exact (MK_COMB (@lem3230442) (@lem3230441 A t s)). Qed.
Lemma lem3230444 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term238 A s t x) = (term221 A x s t).
Proof. exact (eq_refl (term238 A s t x)). Qed.
Lemma lem3230445 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3230446 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term244 A s t x) = (term245 A x s t).
Proof. exact (MK_COMB (@lem3230445) (@lem3230444 A x s t)). Qed.
Lemma lem3230447 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term234 A t s) = (term234 A t s).
Proof. exact (eq_refl (term234 A t s)). Qed.
Lemma lem3230448 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term246 A x t s) = (term247 A x t s).
Proof. exact (MK_COMB (@lem3230446 A x s t) (@lem3230447 A t s)). Qed.
Lemma lem3230449 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term248 A t s) = (term249 A t s).
Proof. exact (fun_ext (fun x : A => @lem3230448 A x t s)). Qed.
Lemma lem3230450 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230451 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term237 A t s) = (term250 A t s).
Proof. exact (MK_COMB (@lem3230450 A) (@lem3230449 A t s)). Qed.
Lemma lem3230452 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term236 A t s) = (term237 A t s)) = ((term235 A t s) = (term250 A t s)).
Proof. exact (MK_COMB (@lem3230443 A t s) (@lem3230451 A t s)). Qed.
Lemma lem3230453 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term235 A t s) = (term250 A t s).
Proof. exact (EQ_MP (@lem3230452 A t s) (@lem3230433 A t s)). Qed.
Lemma lem3230455 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3230456 {A : Type'} (P : Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (@lem3230455 A P Q). Qed.
Lemma lem3230457 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term251 A x t s) = (term252 A x t s).
Proof. exact (@lem3230456 A (term221 A x s t) (term233 A t s)). Qed.
Lemma lem3230458 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term253 A t s a) = (term231 A t s a).
Proof. exact (eq_refl (term253 A t s a)). Qed.
Lemma lem3230459 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term254 A t s) = (term233 A t s).
Proof. exact (fun_ext (fun a : A => @lem3230458 A t s a)). Qed.
Lemma lem3230460 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230461 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term255 A t s) = (term234 A t s).
Proof. exact (MK_COMB (@lem3230460 A) (@lem3230459 A t s)). Qed.
Lemma lem3230462 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term245 A x s t) = (term245 A x s t).
Proof. exact (eq_refl (term245 A x s t)). Qed.
Lemma lem3230463 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term251 A x t s) = (term247 A x t s).
Proof. exact (MK_COMB (@lem3230462 A x s t) (@lem3230461 A t s)). Qed.
Lemma lem3230464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3230465 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term256 A x t s) = (term257 A x t s).
Proof. exact (MK_COMB (@lem3230464) (@lem3230463 A x t s)). Qed.
Lemma lem3230466 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term253 A t s a) = (term231 A t s a).
Proof. exact (eq_refl (term253 A t s a)). Qed.
Lemma lem3230467 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term245 A x s t) = (term245 A x s t).
Proof. exact (eq_refl (term245 A x s t)). Qed.
Lemma lem3230468 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (a : A) : (term258 A x t s a) = (term259 A x t s a).
Proof. exact (MK_COMB (@lem3230467 A x s t) (@lem3230466 A t s a)). Qed.
Lemma lem3230469 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term260 A x t s) = (term261 A x t s).
Proof. exact (fun_ext (fun a : A => @lem3230468 A x t s a)). Qed.
Lemma lem3230470 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230471 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term252 A x t s) = (term262 A x t s).
Proof. exact (MK_COMB (@lem3230470 A) (@lem3230469 A x t s)). Qed.
Lemma lem3230472 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : ((term251 A x t s) = (term252 A x t s)) = ((term247 A x t s) = (term262 A x t s)).
Proof. exact (MK_COMB (@lem3230465 A x t s) (@lem3230471 A x t s)). Qed.
Lemma lem3230473 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term247 A x t s) = (term262 A x t s).
Proof. exact (EQ_MP (@lem3230472 A x t s) (@lem3230457 A x t s)). Qed.
Lemma lem3230474 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term249 A t s) = (term263 A t s).
Proof. exact (fun_ext (fun x : A => @lem3230473 A x t s)). Qed.
Lemma lem3230475 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230476 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term250 A t s) = (term264 A t s).
Proof. exact (MK_COMB (@lem3230475 A) (@lem3230474 A t s)). Qed.
Lemma lem3230477 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term235 A t s) = (term264 A t s).
Proof. exact (TRANS (@lem3230453 A t s) (@lem3230476 A t s)). Qed.
Lemma lem3230478 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term150 A t s) = (term264 A t s).
Proof. exact (TRANS (@lem3230429 A t s) (@lem3230477 A t s)). Qed.
Lemma lem3230479 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term151 A t s) = (term265 A t s).
Proof. exact (MK_COMB (@lem3230382 A t s) (@lem3230478 A t s)). Qed.
Lemma lem3230481 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3230482 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (@lem3230481 A P Q). Qed.
Lemma lem3230483 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term268 A t s) = (term269 A t s).
Proof. exact (@lem3230482 A (term213 A t s) (term263 A t s)). Qed.
Lemma lem3230484 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term270 A t s x) = (term212 A x t s).
Proof. exact (eq_refl (term270 A t s x)). Qed.
Lemma lem3230485 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term271 A t s) = (term213 A t s).
Proof. exact (fun_ext (fun x : A => @lem3230484 A x t s)). Qed.
Lemma lem3230486 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230487 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term272 A t s) = (term214 A t s).
Proof. exact (MK_COMB (@lem3230486 A) (@lem3230485 A t s)). Qed.
Lemma lem3230488 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3230489 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term273 A t s) = (term215 A t s).
Proof. exact (MK_COMB (@lem3230488) (@lem3230487 A t s)). Qed.
Lemma lem3230490 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term274 A t s x) = (term262 A x t s).
Proof. exact (eq_refl (term274 A t s x)). Qed.
Lemma lem3230491 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term275 A t s) = (term263 A t s).
Proof. exact (fun_ext (fun x : A => @lem3230490 A x t s)). Qed.
Lemma lem3230492 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230493 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term276 A t s) = (term264 A t s).
Proof. exact (MK_COMB (@lem3230492 A) (@lem3230491 A t s)). Qed.
Lemma lem3230494 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term268 A t s) = (term265 A t s).
Proof. exact (MK_COMB (@lem3230489 A t s) (@lem3230493 A t s)). Qed.
Lemma lem3230495 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3230496 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term277 A t s) = (term278 A t s).
Proof. exact (MK_COMB (@lem3230495) (@lem3230494 A t s)). Qed.
Lemma lem3230497 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term270 A t s x) = (term212 A x t s).
Proof. exact (eq_refl (term270 A t s x)). Qed.
Lemma lem3230498 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3230499 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term279 A t s x) = (term280 A x t s).
Proof. exact (MK_COMB (@lem3230498) (@lem3230497 A x t s)). Qed.
Lemma lem3230500 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term274 A t s x) = (term262 A x t s).
Proof. exact (eq_refl (term274 A t s x)). Qed.
Lemma lem3230501 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term281 A t s x) = (term282 A x t s).
Proof. exact (MK_COMB (@lem3230499 A x t s) (@lem3230500 A x t s)). Qed.
Lemma lem3230502 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term283 A t s) = (term284 A t s).
Proof. exact (fun_ext (fun x : A => @lem3230501 A x t s)). Qed.
Lemma lem3230503 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230504 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term269 A t s) = (term285 A t s).
Proof. exact (MK_COMB (@lem3230503 A) (@lem3230502 A t s)). Qed.
Lemma lem3230505 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term268 A t s) = (term269 A t s)) = ((term265 A t s) = (term285 A t s)).
Proof. exact (MK_COMB (@lem3230496 A t s) (@lem3230504 A t s)). Qed.
Lemma lem3230506 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term265 A t s) = (term285 A t s).
Proof. exact (EQ_MP (@lem3230505 A t s) (@lem3230483 A t s)). Qed.
Lemma lem3230508 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3230509 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term266 A P Q) = (term267 A P Q).
Proof. exact (@lem3230508 A P Q). Qed.
Lemma lem3230510 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term286 A x t s) = (term287 A x t s).
Proof. exact (@lem3230509 A (term211 A x t s) (term261 A x t s)). Qed.
Lemma lem3230511 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) : (term288 A x t s x') = (term209 A x x' t s).
Proof. exact (eq_refl (term288 A x t s x')). Qed.
Lemma lem3230512 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term289 A x t s) = (term211 A x t s).
Proof. exact (fun_ext (fun x' : A => @lem3230511 A x x' t s)). Qed.
Lemma lem3230513 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230514 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term290 A x t s) = (term212 A x t s).
Proof. exact (MK_COMB (@lem3230513 A) (@lem3230512 A x t s)). Qed.
Lemma lem3230515 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3230516 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term291 A x t s) = (term280 A x t s).
Proof. exact (MK_COMB (@lem3230515) (@lem3230514 A x t s)). Qed.
Lemma lem3230517 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term292 A x t s x') = (term259 A x t s x').
Proof. exact (eq_refl (term292 A x t s x')). Qed.
Lemma lem3230518 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term293 A x t s) = (term261 A x t s).
Proof. exact (fun_ext (fun x' : A => @lem3230517 A x t s x')). Qed.
Lemma lem3230519 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230520 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term294 A x t s) = (term262 A x t s).
Proof. exact (MK_COMB (@lem3230519 A) (@lem3230518 A x t s)). Qed.
Lemma lem3230521 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term286 A x t s) = (term282 A x t s).
Proof. exact (MK_COMB (@lem3230516 A x t s) (@lem3230520 A x t s)). Qed.
Lemma lem3230522 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3230523 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term295 A x t s) = (term296 A x t s).
Proof. exact (MK_COMB (@lem3230522) (@lem3230521 A x t s)). Qed.
Lemma lem3230524 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) : (term288 A x t s x') = (term209 A x x' t s).
Proof. exact (eq_refl (term288 A x t s x')). Qed.
Lemma lem3230525 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3230526 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) : (term297 A x t s x') = (term298 A x x' t s).
Proof. exact (MK_COMB (@lem3230525) (@lem3230524 A x x' t s)). Qed.
Lemma lem3230527 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term292 A x t s x') = (term259 A x t s x').
Proof. exact (eq_refl (term292 A x t s x')). Qed.
Lemma lem3230528 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term299 A x t s x') = (term300 A x t s x').
Proof. exact (MK_COMB (@lem3230526 A x x' t s) (@lem3230527 A x t s x')). Qed.
Lemma lem3230529 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term301 A x t s) = (term302 A x t s).
Proof. exact (fun_ext (fun x' : A => @lem3230528 A x t s x')). Qed.
Lemma lem3230530 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230531 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term287 A x t s) = (term303 A x t s).
Proof. exact (MK_COMB (@lem3230530 A) (@lem3230529 A x t s)). Qed.
Lemma lem3230532 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : ((term286 A x t s) = (term287 A x t s)) = ((term282 A x t s) = (term303 A x t s)).
Proof. exact (MK_COMB (@lem3230523 A x t s) (@lem3230531 A x t s)). Qed.
Lemma lem3230533 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term282 A x t s) = (term303 A x t s).
Proof. exact (EQ_MP (@lem3230532 A x t s) (@lem3230510 A x t s)). Qed.
Lemma lem3230536 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term304 A x t s) = (term304 A x t s).
Proof. exact (eq_refl (term304 A x t s)). Qed.
Lemma lem3230537 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term304 A x t s) = ((term282 A x t s) = (term303 A x t s)).
Proof. exact (eq_refl (term304 A x t s)). Qed.
Lemma lem3230538 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term305 A x t s) = (term305 A x t s).
Proof. exact (eq_refl (term305 A x t s)). Qed.
Lemma lem3230539 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : ((term304 A x t s) = (term304 A x t s)) = ((term304 A x t s) = ((term282 A x t s) = (term303 A x t s))).
Proof. exact (MK_COMB (@lem3230538 A x t s) (@lem3230537 A x t s)). Qed.
Lemma lem3230540 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term304 A x t s) = ((term282 A x t s) = (term303 A x t s)).
Proof. exact (eq_refl (term304 A x t s)). Qed.
Lemma lem3230541 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3230542 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term305 A x t s) = (term306 A x t s).
Proof. exact (MK_COMB (@lem3230541) (@lem3230540 A x t s)). Qed.
Lemma lem3230543 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : ((term282 A x t s) = (term303 A x t s)) = ((term282 A x t s) = (term303 A x t s)).
Proof. exact (eq_refl ((term282 A x t s) = (term303 A x t s))). Qed.
Lemma lem3230544 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : ((term304 A x t s) = ((term282 A x t s) = (term303 A x t s))) = (((term282 A x t s) = (term303 A x t s)) = ((term282 A x t s) = (term303 A x t s))).
Proof. exact (MK_COMB (@lem3230542 A x t s) (@lem3230543 A x t s)). Qed.
Lemma lem3230545 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : ((term304 A x t s) = (term304 A x t s)) = (((term282 A x t s) = (term303 A x t s)) = ((term282 A x t s) = (term303 A x t s))).
Proof. exact (TRANS (@lem3230539 A x t s) (@lem3230544 A x t s)). Qed.
Lemma lem3230546 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : ((term282 A x t s) = (term303 A x t s)) = ((term282 A x t s) = (term303 A x t s)).
Proof. exact (EQ_MP (@lem3230545 A x t s) (@lem3230536 A x t s)). Qed.
Lemma lem3230547 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) : (term282 A x t s) = (term303 A x t s).
Proof. exact (EQ_MP (@lem3230546 A x t s) (@lem3230533 A x t s)). Qed.
Lemma lem3230548 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term284 A t s) = (term307 A t s).
Proof. exact (fun_ext (fun x : A => @lem3230547 A x t s)). Qed.
Lemma lem3230549 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3230550 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term285 A t s) = (term308 A t s).
Proof. exact (MK_COMB (@lem3230549 A) (@lem3230548 A t s)). Qed.
Lemma lem3230551 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term265 A t s) = (term308 A t s).
Proof. exact (TRANS (@lem3230506 A t s) (@lem3230550 A t s)). Qed.
Lemma lem3230552 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term151 A t s) = (term308 A t s).
Proof. exact (TRANS (@lem3230479 A t s) (@lem3230551 A t s)). Qed.
Lemma lem3230553 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term125 A t s) = (term308 A t s).
Proof. exact (TRANS (@lem3230284 A t s) (@lem3230552 A t s)). Qed.
Lemma lem3230554 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term68 A t s) = (term308 A t s).
Proof. exact (TRANS (@lem3229961 A t s) (@lem3230553 A t s)). Qed.
Lemma lem3230555 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term68 A t s) : term308 A t s.
Proof. exact (EQ_MP (@lem3230554 A t s) (@lem3229812 A t s h1)). Qed.
Lemma lem3230556 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term303 A x t s) : term303 A x t s.
Proof. exact (h1). Qed.
Lemma lem3230557 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term300 A x t s x') : term300 A x t s x'.
Proof. exact (h1). Qed.
Lemma lem3230568 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) : (term50 A t s x') = (term50 A t s x').
Proof. exact (eq_refl (term50 A t s x')). Qed.
Lemma lem3230579 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term70 A s t x) = (term70 A s t x).
Proof. exact (eq_refl (term70 A s t x)). Qed.
Lemma lem3230580 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term78 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230579 A s t x)). Qed.
Lemma lem3230581 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3230582 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term79 A s t).
Proof. exact (MK_COMB (@lem3230581 A) (@lem3230580 A s t)). Qed.
Lemma lem3230583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3230584 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term97 A s t) = (term97 A s t).
Proof. exact (MK_COMB (@lem3230583) (@lem3230582 A s t)). Qed.
Lemma lem3230585 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) : (term231 A t s x') = (term231 A t s x').
Proof. exact (MK_COMB (@lem3230584 A s t) (@lem3230568 A t s x')). Qed.
Lemma lem3230596 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term70 A s t x) = (term70 A s t x).
Proof. exact (eq_refl (term70 A s t x)). Qed.
Lemma lem3230597 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term78 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230596 A s t x)). Qed.
Lemma lem3230598 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3230599 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term79 A s t).
Proof. exact (MK_COMB (@lem3230598 A) (@lem3230597 A s t)). Qed.
Lemma lem3230610 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term132 A s t x) = (term132 A s t x).
Proof. exact (eq_refl (term132 A s t x)). Qed.
Lemma lem3230611 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term130 A s t) = (term130 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230610 A s t x)). Qed.
Lemma lem3230612 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3230613 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term142 A s t) = (term142 A s t).
Proof. exact (MK_COMB (@lem3230612 A) (@lem3230611 A s t)). Qed.
Lemma lem3230614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3230615 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term144 A s t) = (term144 A s t).
Proof. exact (MK_COMB (@lem3230614) (@lem3230613 A s t)). Qed.
Lemma lem3230616 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term147 A s t) = (term147 A s t).
Proof. exact (MK_COMB (@lem3230615 A s t) (@lem3230599 A s t)). Qed.
Lemma lem3230629 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term177 A s t x) = (term177 A s t x).
Proof. exact (eq_refl (term177 A s t x)). Qed.
Lemma lem3230630 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term221 A x s t) = (term221 A x s t).
Proof. exact (MK_COMB (@lem3230629 A s t x) (@lem3230616 A s t)). Qed.
Lemma lem3230631 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3230632 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term245 A x s t) = (term245 A x s t).
Proof. exact (MK_COMB (@lem3230631) (@lem3230630 A x s t)). Qed.
Lemma lem3230633 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term259 A x t s x') = (term259 A x t s x').
Proof. exact (MK_COMB (@lem3230632 A x s t) (@lem3230585 A t s x')). Qed.
Lemma lem3230644 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term70 A t s a) = (term70 A t s a).
Proof. exact (eq_refl (term70 A t s a)). Qed.
Lemma lem3230645 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term78 A t s) = (term78 A t s).
Proof. exact (fun_ext (fun a : A => @lem3230644 A t s a)). Qed.
Lemma lem3230646 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3230647 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term79 A t s) = (term79 A t s).
Proof. exact (MK_COMB (@lem3230646 A) (@lem3230645 A t s)). Qed.
Lemma lem3230660 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term177 A s t x') = (term177 A s t x').
Proof. exact (eq_refl (term177 A s t x')). Qed.
Lemma lem3230661 {A : Type'} (x' : A) (t : A -> Prop) (s : A -> Prop) : (term179 A x' t s) = (term179 A x' t s).
Proof. exact (MK_COMB (@lem3230660 A s t x') (@lem3230647 A t s)). Qed.
Lemma lem3230686 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term81 A s t x) = (term81 A s t x).
Proof. exact (eq_refl (term81 A s t x)). Qed.
Lemma lem3230697 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term70 A s t x) = (term70 A s t x).
Proof. exact (eq_refl (term70 A s t x)). Qed.
Lemma lem3230698 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term78 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230697 A s t x)). Qed.
Lemma lem3230699 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3230700 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term79 A s t).
Proof. exact (MK_COMB (@lem3230699 A) (@lem3230698 A s t)). Qed.
Lemma lem3230701 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3230702 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term97 A s t) = (term97 A s t).
Proof. exact (MK_COMB (@lem3230701) (@lem3230700 A s t)). Qed.
Lemma lem3230703 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term162 A s t x) = (term162 A s t x).
Proof. exact (MK_COMB (@lem3230702 A s t) (@lem3230686 A s t x)). Qed.
Lemma lem3230704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3230705 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term195 A s t x) = (term195 A s t x).
Proof. exact (MK_COMB (@lem3230704) (@lem3230703 A s t x)). Qed.
Lemma lem3230706 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) : (term209 A x x' t s) = (term209 A x x' t s).
Proof. exact (MK_COMB (@lem3230705 A s t x) (@lem3230661 A x' t s)). Qed.
Lemma lem3230707 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3230708 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) : (term298 A x x' t s) = (term298 A x x' t s).
Proof. exact (MK_COMB (@lem3230707) (@lem3230706 A x x' t s)). Qed.
Lemma lem3230709 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term300 A x t s x') = (term300 A x t s x').
Proof. exact (MK_COMB (@lem3230708 A x x' t s) (@lem3230633 A x t s x')). Qed.
Lemma lem3230710 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term300 A x t s x') : term300 A x t s x'.
Proof. exact (EQ_MP (@lem3230709 A x t s x') (@lem3230557 A x t s x' h1)). Qed.
Lemma lem3230711 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term209 A x x' t s.
Proof. exact (h1). Qed.
Lemma lem3230712 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : term259 A x t s x'.
Proof. exact (h1). Qed.
Lemma lem3230713 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term179 A x' t s.
Proof. exact (proj2 (@lem3230711 A x x' t s h1)). Qed.
Lemma lem3230714 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term162 A s t x.
Proof. exact (proj1 (@lem3230711 A x x' t s h1)). Qed.
Lemma lem3230715 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term81 A s t x.
Proof. exact (proj2 (@lem3230714 A x x' t s h1)). Qed.
Lemma lem3230716 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term79 A s t.
Proof. exact (proj1 (@lem3230714 A x x' t s h1)). Qed.
Lemma lem3230717 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term309 A s t x.
Proof. exact (proj2 (@lem3230715 A x x' t s h1)). Qed.
Lemma lem3230718 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term310 A s t x.
Proof. exact (proj1 (@lem3230715 A x x' t s h1)). Qed.
Lemma lem3230727 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term50 A s t x') : term50 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3230728 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term79 A t s) : term79 A t s.
Proof. exact (h1). Qed.
Lemma lem3230733 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term50 A s t x') : term50 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3230741 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : term231 A t s x'.
Proof. exact (proj2 (@lem3230712 A x t s x' h1)). Qed.
Lemma lem3230742 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : term221 A x s t.
Proof. exact (proj1 (@lem3230712 A x t s x' h1)). Qed.
Lemma lem3230743 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : term50 A t s x'.
Proof. exact (proj2 (@lem3230741 A x t s x' h1)). Qed.
Lemma lem3230744 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : term79 A s t.
Proof. exact (proj1 (@lem3230741 A x t s x' h1)). Qed.
Lemma lem3230747 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term50 A s t x) : term50 A s t x.
Proof. exact (h1). Qed.
Lemma lem3230748 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term147 A s t) : term147 A s t.
Proof. exact (h1). Qed.
Lemma lem3230752 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term147 A s t) : term142 A s t.
Proof. exact (proj1 (@lem3230748 A s t h1)). Qed.
Lemma lem3230769 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) : term48 A s x.
Proof. exact (h1). Qed.
Lemma lem3230773 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3230798 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) : term48 A s x.
Proof. exact (h1). Qed.
Lemma lem3230802 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3230823 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term70 A s t x) = (term70 A s t x).
Proof. exact (eq_refl (term70 A s t x)). Qed.
Lemma lem3230824 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term78 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230823 A s t x)). Qed.
Lemma lem3230825 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3230827 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term79 A s t).
Proof. exact (MK_COMB (@lem3230825 A) (@lem3230824 A s t)). Qed.
Lemma lem3230828 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term79 A s t.
Proof. exact (EQ_MP (@lem3230827 A s t) (@lem3230716 A x x' t s h1)). Qed.
Lemma lem3230861 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) : term48 A s x.
Proof. exact (h1). Qed.
Lemma lem3230865 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3230873 {A : Type'} (t : A -> Prop) (s : A -> Prop) (a : A) : (term70 A t s a) = (term70 A t s a).
Proof. exact (eq_refl (term70 A t s a)). Qed.
Lemma lem3230874 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term78 A t s) = (term78 A t s).
Proof. exact (fun_ext (fun a : A => @lem3230873 A t s a)). Qed.
Lemma lem3230875 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3230877 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term79 A t s) = (term79 A t s).
Proof. exact (MK_COMB (@lem3230875 A) (@lem3230874 A t s)). Qed.
Lemma lem3230878 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term79 A t s) : term79 A t s.
Proof. exact (EQ_MP (@lem3230877 A t s) (@lem3230728 A t s h1)). Qed.
Lemma lem3230886 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term70 A s t x) = (term70 A s t x).
Proof. exact (eq_refl (term70 A s t x)). Qed.
Lemma lem3230887 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term78 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230886 A s t x)). Qed.
Lemma lem3230888 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3230890 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term79 A s t).
Proof. exact (MK_COMB (@lem3230888 A) (@lem3230887 A s t)). Qed.
Lemma lem3230891 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term79 A s t.
Proof. exact (EQ_MP (@lem3230890 A s t) (@lem3230716 A x x' t s h1)). Qed.
Lemma lem3230915 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term70 A s t x) = (term70 A s t x).
Proof. exact (eq_refl (term70 A s t x)). Qed.
Lemma lem3230916 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term78 A s t).
Proof. exact (fun_ext (fun x : A => @lem3230915 A s t x)). Qed.
Lemma lem3230917 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3230919 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term79 A s t).
Proof. exact (MK_COMB (@lem3230917 A) (@lem3230916 A s t)). Qed.
Lemma lem3230920 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term79 A s t.
Proof. exact (EQ_MP (@lem3230919 A s t) (@lem3230716 A x x' t s h1)). Qed.
Lemma lem3230924 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) : term48 A t x.
Proof. exact (h1). Qed.
Lemma lem3230928 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3230958 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) : term48 A t x.
Proof. exact (h1). Qed.
Lemma lem3230962 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3230987 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) : term48 A t x.
Proof. exact (h1). Qed.
Lemma lem3230991 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3231012 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term70 A s t x) = (term70 A s t x).
Proof. exact (eq_refl (term70 A s t x)). Qed.
Lemma lem3231013 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term78 A s t) = (term78 A s t).
Proof. exact (fun_ext (fun x : A => @lem3231012 A s t x)). Qed.
Lemma lem3231014 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3231016 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term79 A s t).
Proof. exact (MK_COMB (@lem3231014 A) (@lem3231013 A s t)). Qed.
Lemma lem3231017 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : term79 A s t.
Proof. exact (EQ_MP (@lem3231016 A s t) (@lem3230744 A x t s x' h1)). Qed.
Lemma lem3231062 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term132 A s t x) = (term132 A s t x).
Proof. exact (eq_refl (term132 A s t x)). Qed.
Lemma lem3231063 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term130 A s t) = (term130 A s t).
Proof. exact (fun_ext (fun x : A => @lem3231062 A s t x)). Qed.
Lemma lem3231064 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3231066 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term142 A s t) = (term142 A s t).
Proof. exact (MK_COMB (@lem3231064 A) (@lem3231063 A s t)). Qed.
Lemma lem3231067 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term147 A s t) : term142 A s t.
Proof. exact (EQ_MP (@lem3231066 A s t) (@lem3230752 A s t h1)). Qed.
Lemma lem3231090 {A : Type'} (_33184 : A) (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term135 A s t _33184.
Proof. exact (@lem3230828 A x x' t s h1 _33184). Qed.
Lemma lem3231091 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33184 : A) : (term135 A s t _33184) = (term70 A s t _33184).
Proof. exact (eq_refl (term135 A s t _33184)). Qed.
Lemma lem3231096 {A : Type'} (_33186 : A) (t : A -> Prop) (s : A -> Prop) (h1 : term79 A t s) : term135 A t s _33186.
Proof. exact (@lem3230878 A t s h1 _33186). Qed.
Lemma lem3231097 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33186 : A) : (term135 A t s _33186) = (term70 A t s _33186).
Proof. exact (eq_refl (term135 A t s _33186)). Qed.
Lemma lem3231099 {A : Type'} (_33187 : A) (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term135 A s t _33187.
Proof. exact (@lem3230891 A x x' t s h1 _33187). Qed.
Lemma lem3231100 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33187 : A) : (term135 A s t _33187) = (term70 A s t _33187).
Proof. exact (eq_refl (term135 A s t _33187)). Qed.
Lemma lem3231102 {A : Type'} (_33188 : A) (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term135 A s t _33188.
Proof. exact (@lem3230920 A x x' t s h1 _33188). Qed.
Lemma lem3231103 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33188 : A) : (term135 A s t _33188) = (term70 A s t _33188).
Proof. exact (eq_refl (term135 A s t _33188)). Qed.
Lemma lem3231117 {A : Type'} (_33193 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : term135 A s t _33193.
Proof. exact (@lem3231017 A x t s x' h1 _33193). Qed.
Lemma lem3231118 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33193 : A) : (term135 A s t _33193) = (term70 A s t _33193).
Proof. exact (eq_refl (term135 A s t _33193)). Qed.
Lemma lem3231123 {A : Type'} (_33195 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term147 A s t) : term131 A s t _33195.
Proof. exact (@lem3231067 A s t h1 _33195). Qed.
Lemma lem3231124 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33195 : A) : (term131 A s t _33195) = (term132 A s t _33195).
Proof. exact (eq_refl (term131 A s t _33195)). Qed.
Lemma lem3231136 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) : term48 A s x.
Proof. exact (h1). Qed.
Lemma lem3231138 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3231150 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) : term48 A s x.
Proof. exact (h1). Qed.
Lemma lem3231152 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3231164 {A : Type'} (_33184 : A) (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term70 A s t _33184.
Proof. exact (EQ_MP (@lem3231091 A s t _33184) (@lem3231090 A _33184 x x' t s h1)). Qed.
Lemma lem3231172 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term50 A s t x') : term48 A t x'.
Proof. exact (proj2 (@lem3230727 A s t x' h1)). Qed.
Lemma lem3231180 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) : term48 A s x.
Proof. exact (h1). Qed.
Lemma lem3231182 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3231188 {A : Type'} (_33186 : A) (t : A -> Prop) (s : A -> Prop) (h1 : term79 A t s) : term70 A t s _33186.
Proof. exact (EQ_MP (@lem3231097 A t s _33186) (@lem3231096 A _33186 t s h1)). Qed.
Lemma lem3231194 {A : Type'} (_33187 : A) (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term70 A s t _33187.
Proof. exact (EQ_MP (@lem3231100 A s t _33187) (@lem3231099 A _33187 x x' t s h1)). Qed.
Lemma lem3231202 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term50 A s t x') : term48 A t x'.
Proof. exact (proj2 (@lem3230733 A s t x' h1)). Qed.
Lemma lem3231208 {A : Type'} (_33188 : A) (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term70 A s t _33188.
Proof. exact (EQ_MP (@lem3231103 A s t _33188) (@lem3231102 A _33188 x x' t s h1)). Qed.
Lemma lem3231210 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) : term48 A t x.
Proof. exact (h1). Qed.
Lemma lem3231212 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3231226 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) : term48 A t x.
Proof. exact (h1). Qed.
Lemma lem3231228 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3231240 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) : term48 A t x.
Proof. exact (h1). Qed.
Lemma lem3231242 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3231254 {A : Type'} (_33193 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : term70 A s t _33193.
Proof. exact (EQ_MP (@lem3231118 A s t _33193) (@lem3231117 A _33193 x t s x' h1)). Qed.
Lemma lem3231262 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term50 A s t x) : term48 A t x.
Proof. exact (proj2 (@lem3230747 A s t x h1)). Qed.
Lemma lem3231272 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : term48 A s x'.
Proof. exact (proj2 (@lem3230743 A x t s x' h1)). Qed.
Lemma lem3231278 {A : Type'} (_33195 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term147 A s t) : term132 A s t _33195.
Proof. exact (EQ_MP (@lem3231124 A s t _33195) (@lem3231123 A _33195 s t h1)). Qed.
Lemma lem3231286 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3231287 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term311 A s x.
Proof. exact (fun h0 : term48 A s x => @lem3231286 A s x h1). Qed.
Lemma lem3231289 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231290 {A : Type'} (s : A -> Prop) (x : A) : (term311 A s x) = (s x).
Proof. exact (@lem3231289 (s x)). Qed.
Lemma lem3231291 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3231290 A s x) (@lem3231287 A s x h1)). Qed.
Lemma lem3231294 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3231296 {A : Type'} (s : A -> Prop) (x : A) : (term48 A s x) = (term313 A s x).
Proof. exact (@lem3231294 (s x)). Qed.
Lemma lem3231299 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) : term313 A s x.
Proof. exact (EQ_MP (@lem3231296 A s x) (@lem3231136 A s x h1)). Qed.
Lemma lem3231302 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : False.
Proof. exact (@lem3231299 A s x h1 (@lem3231291 A s x h2)). Qed.
Lemma lem3231303 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : term314.
Proof. exact (fun h0 : ~ False => @lem3231302 A s x h1 h2). Qed.
Lemma lem3231305 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231306 : term314 = False.
Proof. exact (@lem3231305 False). Qed.
Lemma lem3231307 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3231306) (@lem3231303 A s x h1 h2)). Qed.
Lemma lem3231309 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3231310 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term311 A s x.
Proof. exact (fun h0 : term48 A s x => @lem3231309 A s x h1). Qed.
Lemma lem3231312 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231313 {A : Type'} (s : A -> Prop) (x : A) : (term311 A s x) = (s x).
Proof. exact (@lem3231312 (s x)). Qed.
Lemma lem3231314 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3231313 A s x) (@lem3231310 A s x h1)). Qed.
Lemma lem3231317 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3231319 {A : Type'} (s : A -> Prop) (x : A) : (term48 A s x) = (term313 A s x).
Proof. exact (@lem3231317 (s x)). Qed.
Lemma lem3231322 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) : term313 A s x.
Proof. exact (EQ_MP (@lem3231319 A s x) (@lem3231150 A s x h1)). Qed.
Lemma lem3231325 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : False.
Proof. exact (@lem3231322 A s x h1 (@lem3231314 A s x h2)). Qed.
Lemma lem3231326 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : term314.
Proof. exact (fun h0 : ~ False => @lem3231325 A s x h1 h2). Qed.
Lemma lem3231328 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231329 : term314 = False.
Proof. exact (@lem3231328 False). Qed.
Lemma lem3231330 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3231329) (@lem3231326 A s x h1 h2)). Qed.
Lemma lem3231332 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term50 A s t x') : s x'.
Proof. exact (proj1 (@lem3230727 A s t x' h1)). Qed.
Lemma lem3231333 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term50 A s t x') : term311 A s x'.
Proof. exact (fun h0 : term48 A s x' => @lem3231332 A s t x' h1). Qed.
Lemma lem3231335 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231336 {A : Type'} (s : A -> Prop) (x' : A) : (term311 A s x') = (s x').
Proof. exact (@lem3231335 (s x')). Qed.
Lemma lem3231337 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term50 A s t x') : s x'.
Proof. exact (EQ_MP (@lem3231336 A s x') (@lem3231333 A s t x' h1)). Qed.
Lemma lem3231343 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3231344 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33184 : A) : (term70 A s t _33184) = (term132 A t s _33184).
Proof. exact (@lem3231343 (t _33184) (term48 A s _33184)). Qed.
Lemma lem3231350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3231351 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33184 : A) : (term315 A s t _33184) = (term316 A t s _33184).
Proof. exact (MK_COMB (@lem3231350) (@lem3231344 A t s _33184)). Qed.
Lemma lem3231357 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33184 : A) : (term132 A t s _33184) = (term132 A t s _33184).
Proof. exact (eq_refl (term132 A t s _33184)). Qed.
Lemma lem3231358 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33184 : A) : ((term70 A s t _33184) = (term132 A t s _33184)) = ((term132 A t s _33184) = (term132 A t s _33184)).
Proof. exact (MK_COMB (@lem3231351 A t s _33184) (@lem3231357 A t s _33184)). Qed.
Lemma lem3231360 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3231361 (x : Prop) : (x = x) = True.
Proof. exact (@lem3231360 Prop x). Qed.
Lemma lem3231362 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33184 : A) : ((term132 A t s _33184) = (term132 A t s _33184)) = True.
Proof. exact (@lem3231361 (term132 A t s _33184)). Qed.
Lemma lem3231363 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33184 : A) : ((term70 A s t _33184) = (term132 A t s _33184)) = True.
Proof. exact (TRANS (@lem3231358 A t s _33184) (@lem3231362 A t s _33184)). Qed.
Lemma lem3231364 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33184 : A) : True = ((term70 A s t _33184) = (term132 A t s _33184)).
Proof. exact (SYM (@lem3231363 A t s _33184)). Qed.
Lemma lem3231365 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33184 : A) : (term70 A s t _33184) = (term132 A t s _33184).
Proof. exact (EQ_MP (@lem3231364 A t s _33184) (@lem0)). Qed.
Lemma lem3231366 {A : Type'} (_33184 : A) (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term132 A t s _33184.
Proof. exact (EQ_MP (@lem3231365 A t s _33184) (@lem3231164 A _33184 x x' t s h1)). Qed.
Lemma lem3231368 (b : Prop) (a : Prop) : (a \/ b) = (term317 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3231369 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33184 : A) : (term132 A t s _33184) = (term318 A s t _33184).
Proof. exact (@lem3231368 (term48 A s _33184) (t _33184)). Qed.
Lemma lem3231371 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3231372 {A : Type'} (s : A -> Prop) (_33184 : A) : (term99 A s _33184) = (s _33184).
Proof. exact (@lem3231371 (s _33184)). Qed.
Lemma lem3231373 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3231374 {A : Type'} (s : A -> Prop) (_33184 : A) : (term319 A s _33184) = (term30 A s _33184).
Proof. exact (MK_COMB (@lem3231373) (@lem3231372 A s _33184)). Qed.
Lemma lem3231375 {A : Type'} (t : A -> Prop) (_33184 : A) : (t _33184) = (t _33184).
Proof. exact (eq_refl (t _33184)). Qed.
Lemma lem3231376 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33184 : A) : (term318 A s t _33184) = (term32 A s t _33184).
Proof. exact (MK_COMB (@lem3231374 A s _33184) (@lem3231375 A t _33184)). Qed.
Lemma lem3231377 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33184 : A) : (term132 A t s _33184) = (term32 A s t _33184).
Proof. exact (TRANS (@lem3231369 A s t _33184) (@lem3231376 A s t _33184)). Qed.
Lemma lem3231380 {A : Type'} (_33184 : A) (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term32 A s t _33184.
Proof. exact (EQ_MP (@lem3231377 A s t _33184) (@lem3231366 A _33184 x x' t s h1)). Qed.
Lemma lem3231381 {A : Type'} (_33184 : A) (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term32 A s t _33184.
Proof. exact (@lem3231380 A _33184 x x' t s h1). Qed.
Lemma lem3231382 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term32 A s t x'.
Proof. exact (@lem3231381 A x' x x' t s h1). Qed.
Lemma lem3231385 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term50 A s t x') (h2 : term209 A x x' t s) : t x'.
Proof. exact (@lem3231382 A x x' t s h2 (@lem3231337 A s t x' h1)). Qed.
Lemma lem3231386 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term50 A s t x') (h2 : term209 A x x' t s) : term311 A t x'.
Proof. exact (fun h0 : term48 A t x' => @lem3231385 A x x' t s h1 h2). Qed.
Lemma lem3231388 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231389 {A : Type'} (t : A -> Prop) (x' : A) : (term311 A t x') = (t x').
Proof. exact (@lem3231388 (t x')). Qed.
Lemma lem3231390 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term50 A s t x') (h2 : term209 A x x' t s) : t x'.
Proof. exact (EQ_MP (@lem3231389 A t x') (@lem3231386 A x x' t s h1 h2)). Qed.
Lemma lem3231393 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3231395 {A : Type'} (t : A -> Prop) (x' : A) : (term48 A t x') = (term313 A t x').
Proof. exact (@lem3231393 (t x')). Qed.
Lemma lem3231398 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term50 A s t x') : term313 A t x'.
Proof. exact (EQ_MP (@lem3231395 A t x') (@lem3231172 A s t x' h1)). Qed.
Lemma lem3231401 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term50 A s t x') (h2 : term209 A x x' t s) : False.
Proof. exact (@lem3231398 A s t x' h1 (@lem3231390 A x x' t s h1 h2)). Qed.
Lemma lem3231402 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term50 A s t x') (h2 : term209 A x x' t s) : term314.
Proof. exact (fun h0 : ~ False => @lem3231401 A x x' t s h1 h2). Qed.
Lemma lem3231404 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231405 : term314 = False.
Proof. exact (@lem3231404 False). Qed.
Lemma lem3231406 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term50 A s t x') (h2 : term209 A x x' t s) : False.
Proof. exact (EQ_MP (@lem3231405) (@lem3231402 A x x' t s h1 h2)). Qed.
Lemma lem3231408 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3231409 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term311 A t x.
Proof. exact (fun h0 : term48 A t x => @lem3231408 A t x h1). Qed.
Lemma lem3231411 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231412 {A : Type'} (t : A -> Prop) (x : A) : (term311 A t x) = (t x).
Proof. exact (@lem3231411 (t x)). Qed.
Lemma lem3231413 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3231412 A t x) (@lem3231409 A t x h1)). Qed.
Lemma lem3231419 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3231420 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33186 : A) : (term70 A t s _33186) = (term132 A s t _33186).
Proof. exact (@lem3231419 (s _33186) (term48 A t _33186)). Qed.
Lemma lem3231426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3231427 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33186 : A) : (term315 A t s _33186) = (term316 A s t _33186).
Proof. exact (MK_COMB (@lem3231426) (@lem3231420 A s t _33186)). Qed.
Lemma lem3231433 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33186 : A) : (term132 A s t _33186) = (term132 A s t _33186).
Proof. exact (eq_refl (term132 A s t _33186)). Qed.
Lemma lem3231434 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33186 : A) : ((term70 A t s _33186) = (term132 A s t _33186)) = ((term132 A s t _33186) = (term132 A s t _33186)).
Proof. exact (MK_COMB (@lem3231427 A s t _33186) (@lem3231433 A s t _33186)). Qed.
Lemma lem3231436 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3231437 (x : Prop) : (x = x) = True.
Proof. exact (@lem3231436 Prop x). Qed.
Lemma lem3231438 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33186 : A) : ((term132 A s t _33186) = (term132 A s t _33186)) = True.
Proof. exact (@lem3231437 (term132 A s t _33186)). Qed.
Lemma lem3231439 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33186 : A) : ((term70 A t s _33186) = (term132 A s t _33186)) = True.
Proof. exact (TRANS (@lem3231434 A s t _33186) (@lem3231438 A s t _33186)). Qed.
Lemma lem3231440 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33186 : A) : True = ((term70 A t s _33186) = (term132 A s t _33186)).
Proof. exact (SYM (@lem3231439 A s t _33186)). Qed.
Lemma lem3231441 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33186 : A) : (term70 A t s _33186) = (term132 A s t _33186).
Proof. exact (EQ_MP (@lem3231440 A s t _33186) (@lem0)). Qed.
Lemma lem3231442 {A : Type'} (_33186 : A) (t : A -> Prop) (s : A -> Prop) (h1 : term79 A t s) : term132 A s t _33186.
Proof. exact (EQ_MP (@lem3231441 A s t _33186) (@lem3231188 A _33186 t s h1)). Qed.
Lemma lem3231444 (b : Prop) (a : Prop) : (a \/ b) = (term317 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3231445 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33186 : A) : (term132 A s t _33186) = (term318 A t s _33186).
Proof. exact (@lem3231444 (term48 A t _33186) (s _33186)). Qed.
Lemma lem3231447 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3231448 {A : Type'} (t : A -> Prop) (_33186 : A) : (term99 A t _33186) = (t _33186).
Proof. exact (@lem3231447 (t _33186)). Qed.
Lemma lem3231449 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3231450 {A : Type'} (t : A -> Prop) (_33186 : A) : (term319 A t _33186) = (term30 A t _33186).
Proof. exact (MK_COMB (@lem3231449) (@lem3231448 A t _33186)). Qed.
Lemma lem3231451 {A : Type'} (s : A -> Prop) (_33186 : A) : (s _33186) = (s _33186).
Proof. exact (eq_refl (s _33186)). Qed.
Lemma lem3231452 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33186 : A) : (term318 A t s _33186) = (term32 A t s _33186).
Proof. exact (MK_COMB (@lem3231450 A t _33186) (@lem3231451 A s _33186)). Qed.
Lemma lem3231453 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33186 : A) : (term132 A s t _33186) = (term32 A t s _33186).
Proof. exact (TRANS (@lem3231445 A t s _33186) (@lem3231452 A t s _33186)). Qed.
Lemma lem3231456 {A : Type'} (_33186 : A) (t : A -> Prop) (s : A -> Prop) (h1 : term79 A t s) : term32 A t s _33186.
Proof. exact (EQ_MP (@lem3231453 A t s _33186) (@lem3231442 A _33186 t s h1)). Qed.
Lemma lem3231457 {A : Type'} (_33186 : A) (t : A -> Prop) (s : A -> Prop) (h1 : term79 A t s) : term32 A t s _33186.
Proof. exact (@lem3231456 A _33186 t s h1). Qed.
Lemma lem3231458 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term79 A t s) : term32 A t s x.
Proof. exact (@lem3231457 A x t s h1). Qed.
Lemma lem3231461 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : t x) : s x.
Proof. exact (@lem3231458 A x t s h1 (@lem3231413 A t x h2)). Qed.
Lemma lem3231462 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : t x) : term311 A s x.
Proof. exact (fun h0 : term48 A s x => @lem3231461 A s t x h1 h2). Qed.
Lemma lem3231464 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231465 {A : Type'} (s : A -> Prop) (x : A) : (term311 A s x) = (s x).
Proof. exact (@lem3231464 (s x)). Qed.
Lemma lem3231466 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : t x) : s x.
Proof. exact (EQ_MP (@lem3231465 A s x) (@lem3231462 A s t x h1 h2)). Qed.
Lemma lem3231469 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3231471 {A : Type'} (s : A -> Prop) (x : A) : (term48 A s x) = (term313 A s x).
Proof. exact (@lem3231469 (s x)). Qed.
Lemma lem3231474 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) : term313 A s x.
Proof. exact (EQ_MP (@lem3231471 A s x) (@lem3231180 A s x h1)). Qed.
Lemma lem3231477 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : False.
Proof. exact (@lem3231474 A s x h2 (@lem3231466 A s t x h1 h3)). Qed.
Lemma lem3231478 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : term314.
Proof. exact (fun h0 : ~ False => @lem3231477 A s t x h1 h2 h3). Qed.
Lemma lem3231480 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231481 : term314 = False.
Proof. exact (@lem3231480 False). Qed.
Lemma lem3231482 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : False.
Proof. exact (EQ_MP (@lem3231481) (@lem3231478 A s t x h1 h2 h3)). Qed.
Lemma lem3231484 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term50 A s t x') : s x'.
Proof. exact (proj1 (@lem3230733 A s t x' h1)). Qed.
Lemma lem3231485 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term50 A s t x') : term311 A s x'.
Proof. exact (fun h0 : term48 A s x' => @lem3231484 A s t x' h1). Qed.
Lemma lem3231487 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231488 {A : Type'} (s : A -> Prop) (x' : A) : (term311 A s x') = (s x').
Proof. exact (@lem3231487 (s x')). Qed.
Lemma lem3231489 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term50 A s t x') : s x'.
Proof. exact (EQ_MP (@lem3231488 A s x') (@lem3231485 A s t x' h1)). Qed.
Lemma lem3231495 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3231496 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33187 : A) : (term70 A s t _33187) = (term132 A t s _33187).
Proof. exact (@lem3231495 (t _33187) (term48 A s _33187)). Qed.
Lemma lem3231502 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3231503 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33187 : A) : (term315 A s t _33187) = (term316 A t s _33187).
Proof. exact (MK_COMB (@lem3231502) (@lem3231496 A t s _33187)). Qed.
Lemma lem3231509 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33187 : A) : (term132 A t s _33187) = (term132 A t s _33187).
Proof. exact (eq_refl (term132 A t s _33187)). Qed.
Lemma lem3231510 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33187 : A) : ((term70 A s t _33187) = (term132 A t s _33187)) = ((term132 A t s _33187) = (term132 A t s _33187)).
Proof. exact (MK_COMB (@lem3231503 A t s _33187) (@lem3231509 A t s _33187)). Qed.
Lemma lem3231512 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3231513 (x : Prop) : (x = x) = True.
Proof. exact (@lem3231512 Prop x). Qed.
Lemma lem3231514 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33187 : A) : ((term132 A t s _33187) = (term132 A t s _33187)) = True.
Proof. exact (@lem3231513 (term132 A t s _33187)). Qed.
Lemma lem3231515 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33187 : A) : ((term70 A s t _33187) = (term132 A t s _33187)) = True.
Proof. exact (TRANS (@lem3231510 A t s _33187) (@lem3231514 A t s _33187)). Qed.
Lemma lem3231516 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33187 : A) : True = ((term70 A s t _33187) = (term132 A t s _33187)).
Proof. exact (SYM (@lem3231515 A t s _33187)). Qed.
Lemma lem3231517 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33187 : A) : (term70 A s t _33187) = (term132 A t s _33187).
Proof. exact (EQ_MP (@lem3231516 A t s _33187) (@lem0)). Qed.
Lemma lem3231518 {A : Type'} (_33187 : A) (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term132 A t s _33187.
Proof. exact (EQ_MP (@lem3231517 A t s _33187) (@lem3231194 A _33187 x x' t s h1)). Qed.
Lemma lem3231520 (b : Prop) (a : Prop) : (a \/ b) = (term317 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3231521 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33187 : A) : (term132 A t s _33187) = (term318 A s t _33187).
Proof. exact (@lem3231520 (term48 A s _33187) (t _33187)). Qed.
Lemma lem3231523 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3231524 {A : Type'} (s : A -> Prop) (_33187 : A) : (term99 A s _33187) = (s _33187).
Proof. exact (@lem3231523 (s _33187)). Qed.
Lemma lem3231525 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3231526 {A : Type'} (s : A -> Prop) (_33187 : A) : (term319 A s _33187) = (term30 A s _33187).
Proof. exact (MK_COMB (@lem3231525) (@lem3231524 A s _33187)). Qed.
Lemma lem3231527 {A : Type'} (t : A -> Prop) (_33187 : A) : (t _33187) = (t _33187).
Proof. exact (eq_refl (t _33187)). Qed.
Lemma lem3231528 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33187 : A) : (term318 A s t _33187) = (term32 A s t _33187).
Proof. exact (MK_COMB (@lem3231526 A s _33187) (@lem3231527 A t _33187)). Qed.
Lemma lem3231529 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33187 : A) : (term132 A t s _33187) = (term32 A s t _33187).
Proof. exact (TRANS (@lem3231521 A s t _33187) (@lem3231528 A s t _33187)). Qed.
Lemma lem3231532 {A : Type'} (_33187 : A) (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term32 A s t _33187.
Proof. exact (EQ_MP (@lem3231529 A s t _33187) (@lem3231518 A _33187 x x' t s h1)). Qed.
Lemma lem3231533 {A : Type'} (_33187 : A) (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term32 A s t _33187.
Proof. exact (@lem3231532 A _33187 x x' t s h1). Qed.
Lemma lem3231534 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term32 A s t x'.
Proof. exact (@lem3231533 A x' x x' t s h1). Qed.
Lemma lem3231537 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term50 A s t x') (h2 : term209 A x x' t s) : t x'.
Proof. exact (@lem3231534 A x x' t s h2 (@lem3231489 A s t x' h1)). Qed.
Lemma lem3231538 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term50 A s t x') (h2 : term209 A x x' t s) : term311 A t x'.
Proof. exact (fun h0 : term48 A t x' => @lem3231537 A x x' t s h1 h2). Qed.
Lemma lem3231540 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231541 {A : Type'} (t : A -> Prop) (x' : A) : (term311 A t x') = (t x').
Proof. exact (@lem3231540 (t x')). Qed.
Lemma lem3231542 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term50 A s t x') (h2 : term209 A x x' t s) : t x'.
Proof. exact (EQ_MP (@lem3231541 A t x') (@lem3231538 A x x' t s h1 h2)). Qed.
Lemma lem3231545 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3231547 {A : Type'} (t : A -> Prop) (x' : A) : (term48 A t x') = (term313 A t x').
Proof. exact (@lem3231545 (t x')). Qed.
Lemma lem3231550 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term50 A s t x') : term313 A t x'.
Proof. exact (EQ_MP (@lem3231547 A t x') (@lem3231202 A s t x' h1)). Qed.
Lemma lem3231553 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term50 A s t x') (h2 : term209 A x x' t s) : False.
Proof. exact (@lem3231550 A s t x' h1 (@lem3231542 A x x' t s h1 h2)). Qed.
Lemma lem3231554 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term50 A s t x') (h2 : term209 A x x' t s) : term314.
Proof. exact (fun h0 : ~ False => @lem3231553 A x x' t s h1 h2). Qed.
Lemma lem3231556 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231557 : term314 = False.
Proof. exact (@lem3231556 False). Qed.
Lemma lem3231558 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term50 A s t x') (h2 : term209 A x x' t s) : False.
Proof. exact (EQ_MP (@lem3231557) (@lem3231554 A x x' t s h1 h2)). Qed.
Lemma lem3231560 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3231561 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term311 A s x.
Proof. exact (fun h0 : term48 A s x => @lem3231560 A s x h1). Qed.
Lemma lem3231563 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231564 {A : Type'} (s : A -> Prop) (x : A) : (term311 A s x) = (s x).
Proof. exact (@lem3231563 (s x)). Qed.
Lemma lem3231565 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3231564 A s x) (@lem3231561 A s x h1)). Qed.
Lemma lem3231571 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3231572 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33188 : A) : (term70 A s t _33188) = (term132 A t s _33188).
Proof. exact (@lem3231571 (t _33188) (term48 A s _33188)). Qed.
Lemma lem3231578 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3231579 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33188 : A) : (term315 A s t _33188) = (term316 A t s _33188).
Proof. exact (MK_COMB (@lem3231578) (@lem3231572 A t s _33188)). Qed.
Lemma lem3231585 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33188 : A) : (term132 A t s _33188) = (term132 A t s _33188).
Proof. exact (eq_refl (term132 A t s _33188)). Qed.
Lemma lem3231586 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33188 : A) : ((term70 A s t _33188) = (term132 A t s _33188)) = ((term132 A t s _33188) = (term132 A t s _33188)).
Proof. exact (MK_COMB (@lem3231579 A t s _33188) (@lem3231585 A t s _33188)). Qed.
Lemma lem3231588 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3231589 (x : Prop) : (x = x) = True.
Proof. exact (@lem3231588 Prop x). Qed.
Lemma lem3231590 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33188 : A) : ((term132 A t s _33188) = (term132 A t s _33188)) = True.
Proof. exact (@lem3231589 (term132 A t s _33188)). Qed.
Lemma lem3231591 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33188 : A) : ((term70 A s t _33188) = (term132 A t s _33188)) = True.
Proof. exact (TRANS (@lem3231586 A t s _33188) (@lem3231590 A t s _33188)). Qed.
Lemma lem3231592 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33188 : A) : True = ((term70 A s t _33188) = (term132 A t s _33188)).
Proof. exact (SYM (@lem3231591 A t s _33188)). Qed.
Lemma lem3231593 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33188 : A) : (term70 A s t _33188) = (term132 A t s _33188).
Proof. exact (EQ_MP (@lem3231592 A t s _33188) (@lem0)). Qed.
Lemma lem3231594 {A : Type'} (_33188 : A) (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term132 A t s _33188.
Proof. exact (EQ_MP (@lem3231593 A t s _33188) (@lem3231208 A _33188 x x' t s h1)). Qed.
Lemma lem3231596 (b : Prop) (a : Prop) : (a \/ b) = (term317 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3231597 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33188 : A) : (term132 A t s _33188) = (term318 A s t _33188).
Proof. exact (@lem3231596 (term48 A s _33188) (t _33188)). Qed.
Lemma lem3231599 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3231600 {A : Type'} (s : A -> Prop) (_33188 : A) : (term99 A s _33188) = (s _33188).
Proof. exact (@lem3231599 (s _33188)). Qed.
Lemma lem3231601 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3231602 {A : Type'} (s : A -> Prop) (_33188 : A) : (term319 A s _33188) = (term30 A s _33188).
Proof. exact (MK_COMB (@lem3231601) (@lem3231600 A s _33188)). Qed.
Lemma lem3231603 {A : Type'} (t : A -> Prop) (_33188 : A) : (t _33188) = (t _33188).
Proof. exact (eq_refl (t _33188)). Qed.
Lemma lem3231604 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33188 : A) : (term318 A s t _33188) = (term32 A s t _33188).
Proof. exact (MK_COMB (@lem3231602 A s _33188) (@lem3231603 A t _33188)). Qed.
Lemma lem3231605 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33188 : A) : (term132 A t s _33188) = (term32 A s t _33188).
Proof. exact (TRANS (@lem3231597 A s t _33188) (@lem3231604 A s t _33188)). Qed.
Lemma lem3231608 {A : Type'} (_33188 : A) (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term32 A s t _33188.
Proof. exact (EQ_MP (@lem3231605 A s t _33188) (@lem3231594 A _33188 x x' t s h1)). Qed.
Lemma lem3231609 {A : Type'} (_33188 : A) (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term32 A s t _33188.
Proof. exact (@lem3231608 A _33188 x x' t s h1). Qed.
Lemma lem3231610 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : term32 A s t x.
Proof. exact (@lem3231609 A x x x' t s h1). Qed.
Lemma lem3231613 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term209 A x x' t s) : t x.
Proof. exact (@lem3231610 A x x' t s h2 (@lem3231565 A s x h1)). Qed.
Lemma lem3231614 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term209 A x x' t s) : term311 A t x.
Proof. exact (fun h0 : term48 A t x => @lem3231613 A x x' t s h1 h2). Qed.
Lemma lem3231616 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231617 {A : Type'} (t : A -> Prop) (x : A) : (term311 A t x) = (t x).
Proof. exact (@lem3231616 (t x)). Qed.
Lemma lem3231618 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : s x) (h2 : term209 A x x' t s) : t x.
Proof. exact (EQ_MP (@lem3231617 A t x) (@lem3231614 A x x' t s h1 h2)). Qed.
Lemma lem3231621 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3231623 {A : Type'} (t : A -> Prop) (x : A) : (term48 A t x) = (term313 A t x).
Proof. exact (@lem3231621 (t x)). Qed.
Lemma lem3231626 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) : term313 A t x.
Proof. exact (EQ_MP (@lem3231623 A t x) (@lem3231210 A t x h1)). Qed.
Lemma lem3231629 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : s x) (h3 : term209 A x x' t s) : False.
Proof. exact (@lem3231626 A t x h1 (@lem3231618 A x x' t s h2 h3)). Qed.
Lemma lem3231630 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : s x) (h3 : term209 A x x' t s) : term314.
Proof. exact (fun h0 : ~ False => @lem3231629 A x x' t s h1 h2 h3). Qed.
Lemma lem3231632 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231633 : term314 = False.
Proof. exact (@lem3231632 False). Qed.
Lemma lem3231634 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : s x) (h3 : term209 A x x' t s) : False.
Proof. exact (EQ_MP (@lem3231633) (@lem3231630 A x x' t s h1 h2 h3)). Qed.
Lemma lem3231636 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3231637 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term311 A t x.
Proof. exact (fun h0 : term48 A t x => @lem3231636 A t x h1). Qed.
Lemma lem3231639 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231640 {A : Type'} (t : A -> Prop) (x : A) : (term311 A t x) = (t x).
Proof. exact (@lem3231639 (t x)). Qed.
Lemma lem3231641 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3231640 A t x) (@lem3231637 A t x h1)). Qed.
Lemma lem3231644 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3231646 {A : Type'} (t : A -> Prop) (x : A) : (term48 A t x) = (term313 A t x).
Proof. exact (@lem3231644 (t x)). Qed.
Lemma lem3231649 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) : term313 A t x.
Proof. exact (EQ_MP (@lem3231646 A t x) (@lem3231226 A t x h1)). Qed.
Lemma lem3231652 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : False.
Proof. exact (@lem3231649 A t x h1 (@lem3231641 A t x h2)). Qed.
Lemma lem3231653 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : term314.
Proof. exact (fun h0 : ~ False => @lem3231652 A t x h1 h2). Qed.
Lemma lem3231655 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231656 : term314 = False.
Proof. exact (@lem3231655 False). Qed.
Lemma lem3231657 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3231656) (@lem3231653 A t x h1 h2)). Qed.
Lemma lem3231659 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3231660 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term311 A t x.
Proof. exact (fun h0 : term48 A t x => @lem3231659 A t x h1). Qed.
Lemma lem3231662 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231663 {A : Type'} (t : A -> Prop) (x : A) : (term311 A t x) = (t x).
Proof. exact (@lem3231662 (t x)). Qed.
Lemma lem3231664 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3231663 A t x) (@lem3231660 A t x h1)). Qed.
Lemma lem3231667 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3231669 {A : Type'} (t : A -> Prop) (x : A) : (term48 A t x) = (term313 A t x).
Proof. exact (@lem3231667 (t x)). Qed.
Lemma lem3231672 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) : term313 A t x.
Proof. exact (EQ_MP (@lem3231669 A t x) (@lem3231240 A t x h1)). Qed.
Lemma lem3231675 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : False.
Proof. exact (@lem3231672 A t x h1 (@lem3231664 A t x h2)). Qed.
Lemma lem3231676 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : term314.
Proof. exact (fun h0 : ~ False => @lem3231675 A t x h1 h2). Qed.
Lemma lem3231678 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231679 : term314 = False.
Proof. exact (@lem3231678 False). Qed.
Lemma lem3231680 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3231679) (@lem3231676 A t x h1 h2)). Qed.
Lemma lem3231682 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term50 A s t x) : s x.
Proof. exact (proj1 (@lem3230747 A s t x h1)). Qed.
Lemma lem3231683 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term50 A s t x) : term311 A s x.
Proof. exact (fun h0 : term48 A s x => @lem3231682 A s t x h1). Qed.
Lemma lem3231685 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231686 {A : Type'} (s : A -> Prop) (x : A) : (term311 A s x) = (s x).
Proof. exact (@lem3231685 (s x)). Qed.
Lemma lem3231687 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term50 A s t x) : s x.
Proof. exact (EQ_MP (@lem3231686 A s x) (@lem3231683 A s t x h1)). Qed.
Lemma lem3231693 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3231694 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33193 : A) : (term70 A s t _33193) = (term132 A t s _33193).
Proof. exact (@lem3231693 (t _33193) (term48 A s _33193)). Qed.
Lemma lem3231700 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3231701 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33193 : A) : (term315 A s t _33193) = (term316 A t s _33193).
Proof. exact (MK_COMB (@lem3231700) (@lem3231694 A t s _33193)). Qed.
Lemma lem3231707 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33193 : A) : (term132 A t s _33193) = (term132 A t s _33193).
Proof. exact (eq_refl (term132 A t s _33193)). Qed.
Lemma lem3231708 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33193 : A) : ((term70 A s t _33193) = (term132 A t s _33193)) = ((term132 A t s _33193) = (term132 A t s _33193)).
Proof. exact (MK_COMB (@lem3231701 A t s _33193) (@lem3231707 A t s _33193)). Qed.
Lemma lem3231710 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3231711 (x : Prop) : (x = x) = True.
Proof. exact (@lem3231710 Prop x). Qed.
Lemma lem3231712 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33193 : A) : ((term132 A t s _33193) = (term132 A t s _33193)) = True.
Proof. exact (@lem3231711 (term132 A t s _33193)). Qed.
Lemma lem3231713 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33193 : A) : ((term70 A s t _33193) = (term132 A t s _33193)) = True.
Proof. exact (TRANS (@lem3231708 A t s _33193) (@lem3231712 A t s _33193)). Qed.
Lemma lem3231714 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33193 : A) : True = ((term70 A s t _33193) = (term132 A t s _33193)).
Proof. exact (SYM (@lem3231713 A t s _33193)). Qed.
Lemma lem3231715 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33193 : A) : (term70 A s t _33193) = (term132 A t s _33193).
Proof. exact (EQ_MP (@lem3231714 A t s _33193) (@lem0)). Qed.
Lemma lem3231716 {A : Type'} (_33193 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : term132 A t s _33193.
Proof. exact (EQ_MP (@lem3231715 A t s _33193) (@lem3231254 A _33193 x t s x' h1)). Qed.
Lemma lem3231718 (b : Prop) (a : Prop) : (a \/ b) = (term317 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3231719 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33193 : A) : (term132 A t s _33193) = (term318 A s t _33193).
Proof. exact (@lem3231718 (term48 A s _33193) (t _33193)). Qed.
Lemma lem3231721 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3231722 {A : Type'} (s : A -> Prop) (_33193 : A) : (term99 A s _33193) = (s _33193).
Proof. exact (@lem3231721 (s _33193)). Qed.
Lemma lem3231723 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3231724 {A : Type'} (s : A -> Prop) (_33193 : A) : (term319 A s _33193) = (term30 A s _33193).
Proof. exact (MK_COMB (@lem3231723) (@lem3231722 A s _33193)). Qed.
Lemma lem3231725 {A : Type'} (t : A -> Prop) (_33193 : A) : (t _33193) = (t _33193).
Proof. exact (eq_refl (t _33193)). Qed.
Lemma lem3231726 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33193 : A) : (term318 A s t _33193) = (term32 A s t _33193).
Proof. exact (MK_COMB (@lem3231724 A s _33193) (@lem3231725 A t _33193)). Qed.
Lemma lem3231727 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33193 : A) : (term132 A t s _33193) = (term32 A s t _33193).
Proof. exact (TRANS (@lem3231719 A s t _33193) (@lem3231726 A s t _33193)). Qed.
Lemma lem3231730 {A : Type'} (_33193 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : term32 A s t _33193.
Proof. exact (EQ_MP (@lem3231727 A s t _33193) (@lem3231716 A _33193 x t s x' h1)). Qed.
Lemma lem3231731 {A : Type'} (_33193 : A) (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : term32 A s t _33193.
Proof. exact (@lem3231730 A _33193 x t s x' h1). Qed.
Lemma lem3231732 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : term32 A s t x.
Proof. exact (@lem3231731 A x x t s x' h1). Qed.
Lemma lem3231735 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term50 A s t x) (h2 : term259 A x t s x') : t x.
Proof. exact (@lem3231732 A x t s x' h2 (@lem3231687 A s t x h1)). Qed.
Lemma lem3231736 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term50 A s t x) (h2 : term259 A x t s x') : term311 A t x.
Proof. exact (fun h0 : term48 A t x => @lem3231735 A x t s x' h1 h2). Qed.
Lemma lem3231738 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231739 {A : Type'} (t : A -> Prop) (x : A) : (term311 A t x) = (t x).
Proof. exact (@lem3231738 (t x)). Qed.
Lemma lem3231740 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term50 A s t x) (h2 : term259 A x t s x') : t x.
Proof. exact (EQ_MP (@lem3231739 A t x) (@lem3231736 A x t s x' h1 h2)). Qed.
Lemma lem3231743 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3231745 {A : Type'} (t : A -> Prop) (x : A) : (term48 A t x) = (term313 A t x).
Proof. exact (@lem3231743 (t x)). Qed.
Lemma lem3231748 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term50 A s t x) : term313 A t x.
Proof. exact (EQ_MP (@lem3231745 A t x) (@lem3231262 A s t x h1)). Qed.
Lemma lem3231751 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term50 A s t x) (h2 : term259 A x t s x') : False.
Proof. exact (@lem3231748 A s t x h1 (@lem3231740 A x t s x' h1 h2)). Qed.
Lemma lem3231752 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term50 A s t x) (h2 : term259 A x t s x') : term314.
Proof. exact (fun h0 : ~ False => @lem3231751 A x t s x' h1 h2). Qed.
Lemma lem3231754 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231755 : term314 = False.
Proof. exact (@lem3231754 False). Qed.
Lemma lem3231756 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term50 A s t x) (h2 : term259 A x t s x') : False.
Proof. exact (EQ_MP (@lem3231755) (@lem3231752 A x t s x' h1 h2)). Qed.
Lemma lem3231758 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : t x'.
Proof. exact (proj1 (@lem3230743 A x t s x' h1)). Qed.
Lemma lem3231759 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : term311 A t x'.
Proof. exact (fun h0 : term48 A t x' => @lem3231758 A x t s x' h1). Qed.
Lemma lem3231761 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231762 {A : Type'} (t : A -> Prop) (x' : A) : (term311 A t x') = (t x').
Proof. exact (@lem3231761 (t x')). Qed.
Lemma lem3231763 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : t x'.
Proof. exact (EQ_MP (@lem3231762 A t x') (@lem3231759 A x t s x' h1)). Qed.
Lemma lem3231765 (b : Prop) (a : Prop) : (a \/ b) = (term317 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3231766 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33195 : A) : (term132 A s t _33195) = (term318 A t s _33195).
Proof. exact (@lem3231765 (term48 A t _33195) (s _33195)). Qed.
Lemma lem3231768 (a : Prop) : (term66 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3231769 {A : Type'} (t : A -> Prop) (_33195 : A) : (term99 A t _33195) = (t _33195).
Proof. exact (@lem3231768 (t _33195)). Qed.
Lemma lem3231770 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3231771 {A : Type'} (t : A -> Prop) (_33195 : A) : (term319 A t _33195) = (term30 A t _33195).
Proof. exact (MK_COMB (@lem3231770) (@lem3231769 A t _33195)). Qed.
Lemma lem3231772 {A : Type'} (s : A -> Prop) (_33195 : A) : (s _33195) = (s _33195).
Proof. exact (eq_refl (s _33195)). Qed.
Lemma lem3231773 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33195 : A) : (term318 A t s _33195) = (term32 A t s _33195).
Proof. exact (MK_COMB (@lem3231771 A t _33195) (@lem3231772 A s _33195)). Qed.
Lemma lem3231774 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33195 : A) : (term132 A s t _33195) = (term32 A t s _33195).
Proof. exact (TRANS (@lem3231766 A t s _33195) (@lem3231773 A t s _33195)). Qed.
Lemma lem3231777 {A : Type'} (_33195 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term147 A s t) : term32 A t s _33195.
Proof. exact (EQ_MP (@lem3231774 A t s _33195) (@lem3231278 A _33195 s t h1)). Qed.
Lemma lem3231778 {A : Type'} (_33195 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term147 A s t) : term32 A t s _33195.
Proof. exact (@lem3231777 A _33195 s t h1). Qed.
Lemma lem3231779 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term147 A s t) : term32 A t s x'.
Proof. exact (@lem3231778 A x' s t h1). Qed.
Lemma lem3231782 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term147 A s t) (h2 : term259 A x t s x') : s x'.
Proof. exact (@lem3231779 A x' s t h1 (@lem3231763 A x t s x' h2)). Qed.
Lemma lem3231783 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term147 A s t) (h2 : term259 A x t s x') : term311 A s x'.
Proof. exact (fun h0 : term48 A s x' => @lem3231782 A x t s x' h1 h2). Qed.
Lemma lem3231785 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231786 {A : Type'} (s : A -> Prop) (x' : A) : (term311 A s x') = (s x').
Proof. exact (@lem3231785 (s x')). Qed.
Lemma lem3231787 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term147 A s t) (h2 : term259 A x t s x') : s x'.
Proof. exact (EQ_MP (@lem3231786 A s x') (@lem3231783 A x t s x' h1 h2)). Qed.
Lemma lem3231790 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3231792 {A : Type'} (s : A -> Prop) (x' : A) : (term48 A s x') = (term313 A s x').
Proof. exact (@lem3231790 (s x')). Qed.
Lemma lem3231795 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : term313 A s x'.
Proof. exact (EQ_MP (@lem3231792 A s x') (@lem3231272 A x t s x' h1)). Qed.
Lemma lem3231798 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term147 A s t) (h2 : term259 A x t s x') : False.
Proof. exact (@lem3231795 A x t s x' h2 (@lem3231787 A x t s x' h1 h2)). Qed.
Lemma lem3231799 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term147 A s t) (h2 : term259 A x t s x') : term314.
Proof. exact (fun h0 : ~ False => @lem3231798 A x t s x' h1 h2). Qed.
Lemma lem3231801 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3231802 : term314 = False.
Proof. exact (@lem3231801 False). Qed.
Lemma lem3231803 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term147 A s t) (h2 : term259 A x t s x') : False.
Proof. exact (EQ_MP (@lem3231802) (@lem3231799 A x t s x' h1 h2)). Qed.
Lemma lem3231804 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3231680 A t x h1 h2) (fun h3 : False => @lem3231242 A t x h2)). Qed.
Lemma lem3231805 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3231804 A t x h1 h2) (@lem3231242 A t x h2)). Qed.
Lemma lem3231806 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : (term48 A t x) = False.
Proof. exact (prop_ext (fun h3 : term48 A t x => @lem3231805 A t x h1 h2) (fun h3 : False => @lem3231240 A t x h1)). Qed.
Lemma lem3231807 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3231806 A t x h1 h2) (@lem3231240 A t x h1)). Qed.
Lemma lem3231808 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3231657 A t x h1 h2) (fun h3 : False => @lem3231228 A t x h2)). Qed.
Lemma lem3231809 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3231808 A t x h1 h2) (@lem3231228 A t x h2)). Qed.
Lemma lem3231810 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : (term48 A t x) = False.
Proof. exact (prop_ext (fun h3 : term48 A t x => @lem3231809 A t x h1 h2) (fun h3 : False => @lem3231226 A t x h1)). Qed.
Lemma lem3231811 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3231810 A t x h1 h2) (@lem3231226 A t x h1)). Qed.
Lemma lem3231812 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : s x) (h3 : term209 A x x' t s) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3231634 A x x' t s h1 h2 h3) (fun h4 : False => @lem3231212 A s x h2)). Qed.
Lemma lem3231813 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : s x) (h3 : term209 A x x' t s) : False.
Proof. exact (EQ_MP (@lem3231812 A x x' t s h1 h2 h3) (@lem3231212 A s x h2)). Qed.
Lemma lem3231814 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : s x) (h3 : term209 A x x' t s) : (term48 A t x) = False.
Proof. exact (prop_ext (fun h4 : term48 A t x => @lem3231813 A x x' t s h1 h2 h3) (fun h4 : False => @lem3231210 A t x h1)). Qed.
Lemma lem3231815 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : s x) (h3 : term209 A x x' t s) : False.
Proof. exact (EQ_MP (@lem3231814 A x x' t s h1 h2 h3) (@lem3231210 A t x h1)). Qed.
Lemma lem3231816 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3231482 A s t x h1 h2 h3) (fun h4 : False => @lem3231182 A t x h3)). Qed.
Lemma lem3231817 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : False.
Proof. exact (EQ_MP (@lem3231816 A s t x h1 h2 h3) (@lem3231182 A t x h3)). Qed.
Lemma lem3231818 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : (term48 A s x) = False.
Proof. exact (prop_ext (fun h4 : term48 A s x => @lem3231817 A s t x h1 h2 h3) (fun h4 : False => @lem3231180 A s x h2)). Qed.
Lemma lem3231819 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : False.
Proof. exact (EQ_MP (@lem3231818 A s t x h1 h2 h3) (@lem3231180 A s x h2)). Qed.
Lemma lem3231820 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3231330 A s x h1 h2) (fun h3 : False => @lem3231152 A s x h2)). Qed.
Lemma lem3231821 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3231820 A s x h1 h2) (@lem3231152 A s x h2)). Qed.
Lemma lem3231822 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : (term48 A s x) = False.
Proof. exact (prop_ext (fun h3 : term48 A s x => @lem3231821 A s x h1 h2) (fun h3 : False => @lem3231150 A s x h1)). Qed.
Lemma lem3231823 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3231822 A s x h1 h2) (@lem3231150 A s x h1)). Qed.
Lemma lem3231824 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3231307 A s x h1 h2) (fun h3 : False => @lem3231138 A s x h2)). Qed.
Lemma lem3231825 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3231824 A s x h1 h2) (@lem3231138 A s x h2)). Qed.
Lemma lem3231826 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : (term48 A s x) = False.
Proof. exact (prop_ext (fun h3 : term48 A s x => @lem3231825 A s x h1 h2) (fun h3 : False => @lem3231136 A s x h1)). Qed.
Lemma lem3231827 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3231826 A s x h1 h2) (@lem3231136 A s x h1)). Qed.
Lemma lem3231828 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3231807 A t x h1 h2) (fun h3 : False => @lem3230991 A t x h2)). Qed.
Lemma lem3231829 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3231828 A t x h1 h2) (@lem3230991 A t x h2)). Qed.
Lemma lem3231830 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : (term48 A t x) = False.
Proof. exact (prop_ext (fun h3 : term48 A t x => @lem3231829 A t x h1 h2) (fun h3 : False => @lem3230987 A t x h1)). Qed.
Lemma lem3231831 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3231830 A t x h1 h2) (@lem3230987 A t x h1)). Qed.
Lemma lem3231832 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3231811 A t x h1 h2) (fun h3 : False => @lem3230962 A t x h2)). Qed.
Lemma lem3231833 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3231832 A t x h1 h2) (@lem3230962 A t x h2)). Qed.
Lemma lem3231834 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : (term48 A t x) = False.
Proof. exact (prop_ext (fun h3 : term48 A t x => @lem3231833 A t x h1 h2) (fun h3 : False => @lem3230958 A t x h1)). Qed.
Lemma lem3231835 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3231834 A t x h1 h2) (@lem3230958 A t x h1)). Qed.
Lemma lem3231836 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : s x) (h3 : term209 A x x' t s) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3231815 A x x' t s h1 h2 h3) (fun h4 : False => @lem3230928 A s x h2)). Qed.
Lemma lem3231837 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : s x) (h3 : term209 A x x' t s) : False.
Proof. exact (EQ_MP (@lem3231836 A x x' t s h1 h2 h3) (@lem3230928 A s x h2)). Qed.
Lemma lem3231838 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : s x) (h3 : term209 A x x' t s) : (term48 A t x) = False.
Proof. exact (prop_ext (fun h4 : term48 A t x => @lem3231837 A x x' t s h1 h2 h3) (fun h4 : False => @lem3230924 A t x h1)). Qed.
Lemma lem3231839 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : s x) (h3 : term209 A x x' t s) : False.
Proof. exact (EQ_MP (@lem3231838 A x x' t s h1 h2 h3) (@lem3230924 A t x h1)). Qed.
Lemma lem3231840 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3231819 A s t x h1 h2 h3) (fun h4 : False => @lem3230865 A t x h3)). Qed.
Lemma lem3231841 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : False.
Proof. exact (EQ_MP (@lem3231840 A s t x h1 h2 h3) (@lem3230865 A t x h3)). Qed.
Lemma lem3231842 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : (term48 A s x) = False.
Proof. exact (prop_ext (fun h4 : term48 A s x => @lem3231841 A s t x h1 h2 h3) (fun h4 : False => @lem3230861 A s x h2)). Qed.
Lemma lem3231843 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : False.
Proof. exact (EQ_MP (@lem3231842 A s t x h1 h2 h3) (@lem3230861 A s x h2)). Qed.
Lemma lem3231844 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3231823 A s x h1 h2) (fun h3 : False => @lem3230802 A s x h2)). Qed.
Lemma lem3231845 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3231844 A s x h1 h2) (@lem3230802 A s x h2)). Qed.
Lemma lem3231846 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : (term48 A s x) = False.
Proof. exact (prop_ext (fun h3 : term48 A s x => @lem3231845 A s x h1 h2) (fun h3 : False => @lem3230798 A s x h1)). Qed.
Lemma lem3231847 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3231846 A s x h1 h2) (@lem3230798 A s x h1)). Qed.
Lemma lem3231848 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3231827 A s x h1 h2) (fun h3 : False => @lem3230773 A s x h2)). Qed.
Lemma lem3231849 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3231848 A s x h1 h2) (@lem3230773 A s x h2)). Qed.
Lemma lem3231850 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : (term48 A s x) = False.
Proof. exact (prop_ext (fun h3 : term48 A s x => @lem3231849 A s x h1 h2) (fun h3 : False => @lem3230769 A s x h1)). Qed.
Lemma lem3231851 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3231850 A s x h1 h2) (@lem3230769 A s x h1)). Qed.
Lemma lem3231852 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3231831 A t x h1 h2) (fun h3 : False => @lem3230991 A t x h2)). Qed.
Lemma lem3231853 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3231852 A t x h1 h2) (@lem3230991 A t x h2)). Qed.
Lemma lem3231854 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : (term48 A t x) = False.
Proof. exact (prop_ext (fun h3 : term48 A t x => @lem3231853 A t x h1 h2) (fun h3 : False => @lem3230987 A t x h1)). Qed.
Lemma lem3231855 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3231854 A t x h1 h2) (@lem3230987 A t x h1)). Qed.
Lemma lem3231856 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3231835 A t x h1 h2) (fun h3 : False => @lem3230962 A t x h2)). Qed.
Lemma lem3231857 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3231856 A t x h1 h2) (@lem3230962 A t x h2)). Qed.
Lemma lem3231858 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : (term48 A t x) = False.
Proof. exact (prop_ext (fun h3 : term48 A t x => @lem3231857 A t x h1 h2) (fun h3 : False => @lem3230958 A t x h1)). Qed.
Lemma lem3231859 {A : Type'} (t : A -> Prop) (x : A) (h1 : term48 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3231858 A t x h1 h2) (@lem3230958 A t x h1)). Qed.
Lemma lem3231860 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : s x) (h3 : term209 A x x' t s) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3231839 A x x' t s h1 h2 h3) (fun h4 : False => @lem3230928 A s x h2)). Qed.
Lemma lem3231861 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : s x) (h3 : term209 A x x' t s) : False.
Proof. exact (EQ_MP (@lem3231860 A x x' t s h1 h2 h3) (@lem3230928 A s x h2)). Qed.
Lemma lem3231862 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : s x) (h3 : term209 A x x' t s) : (term48 A t x) = False.
Proof. exact (prop_ext (fun h4 : term48 A t x => @lem3231861 A x x' t s h1 h2 h3) (fun h4 : False => @lem3230924 A t x h1)). Qed.
Lemma lem3231863 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : s x) (h3 : term209 A x x' t s) : False.
Proof. exact (EQ_MP (@lem3231862 A x x' t s h1 h2 h3) (@lem3230924 A t x h1)). Qed.
Lemma lem3231864 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : (term79 A t s) = False.
Proof. exact (prop_ext (fun h4 : term79 A t s => @lem3231843 A s t x h1 h2 h3) (fun h4 : False => @lem3230878 A t s h1)). Qed.
Lemma lem3231865 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : False.
Proof. exact (EQ_MP (@lem3231864 A s t x h1 h2 h3) (@lem3230878 A t s h1)). Qed.
Lemma lem3231866 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3231865 A s t x h1 h2 h3) (fun h4 : False => @lem3230865 A t x h3)). Qed.
Lemma lem3231867 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : False.
Proof. exact (EQ_MP (@lem3231866 A s t x h1 h2 h3) (@lem3230865 A t x h3)). Qed.
Lemma lem3231868 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : (term48 A s x) = False.
Proof. exact (prop_ext (fun h4 : term48 A s x => @lem3231867 A s t x h1 h2 h3) (fun h4 : False => @lem3230861 A s x h2)). Qed.
Lemma lem3231869 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term79 A t s) (h2 : term48 A s x) (h3 : t x) : False.
Proof. exact (EQ_MP (@lem3231868 A s t x h1 h2 h3) (@lem3230861 A s x h2)). Qed.
Lemma lem3231870 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3231847 A s x h1 h2) (fun h3 : False => @lem3230802 A s x h2)). Qed.
Lemma lem3231871 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3231870 A s x h1 h2) (@lem3230802 A s x h2)). Qed.
Lemma lem3231872 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : (term48 A s x) = False.
Proof. exact (prop_ext (fun h3 : term48 A s x => @lem3231871 A s x h1 h2) (fun h3 : False => @lem3230798 A s x h1)). Qed.
Lemma lem3231873 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3231872 A s x h1 h2) (@lem3230798 A s x h1)). Qed.
Lemma lem3231874 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3231851 A s x h1 h2) (fun h3 : False => @lem3230773 A s x h2)). Qed.
Lemma lem3231875 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3231874 A s x h1 h2) (@lem3230773 A s x h2)). Qed.
Lemma lem3231876 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : (term48 A s x) = False.
Proof. exact (prop_ext (fun h3 : term48 A s x => @lem3231875 A s x h1 h2) (fun h3 : False => @lem3230769 A s x h1)). Qed.
Lemma lem3231877 {A : Type'} (s : A -> Prop) (x : A) (h1 : term48 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3231876 A s x h1 h2) (@lem3230769 A s x h1)). Qed.
Lemma lem3231878 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term259 A x t s x') : False.
Proof. exact (or_elim (@lem3230742 A x t s x' h1) (fun h0 : term50 A s t x => @lem3231756 A x t s x' h0 h1) (fun h0 : term147 A s t => @lem3231803 A x t s x' h0 h1)). Qed.
Lemma lem3231879 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : t x) (h3 : term209 A x x' t s) : False.
Proof. exact (or_elim (@lem3230713 A x x' t s h3) (fun h0 : term50 A s t x' => @lem3231859 A t x h1 h2) (fun h0 : term79 A t s => @lem3231855 A t x h1 h2)). Qed.
Lemma lem3231880 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : s x) (h3 : term209 A x x' t s) : False.
Proof. exact (or_elim (@lem3230713 A x x' t s h3) (fun h0 : term50 A s t x' => @lem3231558 A x x' t s h0 h3) (fun h0 : term79 A t s => @lem3231863 A x x' t s h1 h2 h3)). Qed.
Lemma lem3231881 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A t x) (h2 : term209 A x x' t s) : False.
Proof. exact (or_elim (@lem3230718 A x x' t s h2) (fun h0 : s x => @lem3231880 A x x' t s h1 h0 h2) (fun h0 : t x => @lem3231879 A x x' t s h1 h0 h2)). Qed.
Lemma lem3231882 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A s x) (h2 : t x) (h3 : term209 A x x' t s) : False.
Proof. exact (or_elim (@lem3230713 A x x' t s h3) (fun h0 : term50 A s t x' => @lem3231406 A x x' t s h0 h3) (fun h0 : term79 A t s => @lem3231869 A s t x h0 h1 h2)). Qed.
Lemma lem3231883 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A s x) (h2 : s x) (h3 : term209 A x x' t s) : False.
Proof. exact (or_elim (@lem3230713 A x x' t s h3) (fun h0 : term50 A s t x' => @lem3231877 A s x h1 h2) (fun h0 : term79 A t s => @lem3231873 A s x h1 h2)). Qed.
Lemma lem3231884 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term48 A s x) (h2 : term209 A x x' t s) : False.
Proof. exact (or_elim (@lem3230718 A x x' t s h2) (fun h0 : s x => @lem3231883 A x x' t s h1 h0 h2) (fun h0 : t x => @lem3231882 A x x' t s h1 h0 h2)). Qed.
Lemma lem3231885 {A : Type'} (x : A) (x' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term209 A x x' t s) : False.
Proof. exact (or_elim (@lem3230717 A x x' t s h1) (fun h0 : term48 A s x => @lem3231884 A x x' t s h0 h1) (fun h0 : term48 A t x => @lem3231881 A x x' t s h0 h1)). Qed.
Lemma lem3231886 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term300 A x t s x') : False.
Proof. exact (or_elim (@lem3230710 A x t s x' h1) (fun h0 : term209 A x x' t s => @lem3231885 A x x' t s h0) (fun h0 : term259 A x t s x' => @lem3231878 A x t s x' h0)). Qed.
Lemma lem3231887 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term300 A x t s x') : (term300 A x t s x') = False.
Proof. exact (prop_ext (fun h2 : term300 A x t s x' => @lem3231886 A x t s x' h1) (fun h2 : False => @lem3230710 A x t s x' h1)). Qed.
Lemma lem3231888 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (x' : A) (h1 : term300 A x t s x') : False.
Proof. exact (EQ_MP (@lem3231887 A x t s x' h1) (@lem3230710 A x t s x' h1)). Qed.
Lemma lem3231889 {A : Type'} (x : A) (t : A -> Prop) (s : A -> Prop) (h1 : term303 A x t s) : False.
Proof. exact (ex_elim (@lem3230556 A x t s h1) (fun x' : A => fun h0 : term302 A x t s x' => @lem3231888 A x t s x' h0)). Qed.
Lemma lem3231890 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term68 A t s) : False.
Proof. exact (ex_elim (@lem3230555 A t s h1) (fun x : A => fun h0 : term307 A t s x => @lem3231889 A x t s h0)). Qed.
Lemma lem3231891 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term68 A t s) : (term68 A t s) = False.
Proof. exact (prop_ext (fun h2 : term68 A t s => @lem3231890 A t s h1) (fun h2 : False => @lem3229812 A t s h1)). Qed.
Lemma lem3231892 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term68 A t s) : False.
Proof. exact (EQ_MP (@lem3231891 A t s h1) (@lem3229812 A t s h1)). Qed.
Lemma lem3231893 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term67 A t s.
Proof. exact (fun h0 : term68 A t s => @lem3231892 A t s h0). Qed.
Lemma lem3231894 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term43 A s t) = (term54 A t s).
Proof. exact (EQ_MP (@lem3229811 A t s) (@lem3231893 A t s)). Qed.
Lemma lem3231899 {A : Type'} (s : A -> Prop) : term56 A s.
Proof. exact (fun t : A -> Prop => @lem3231894 A t s). Qed.
Lemma lem3231904 {A : Type'} : term58 A.
Proof. exact (fun s : A -> Prop => @lem3231899 A s). Qed.
Lemma lem3231905 {A : Type'} : term60 A.
Proof. exact (EQ_MP (@lem3229807 A) (@lem3231904 A)). Qed.
Lemma lem3231907 {A : Type'} : term60 A.
Proof. exact (@lem3229637 A (@lem3231905 A)). Qed.
Lemma lem3231908 {A : Type'} (h1 : term61 A) : False.
Proof. exact (@lem3231907 A (@lem3229621 A h1)). Qed.
Lemma lem3231909 {A : Type'} (h1 : term61 A) : (term61 A) = False.
Proof. exact (prop_ext (fun h2 : term61 A => @lem3231908 A h1) (fun h2 : False => @lem3229621 A h1)). Qed.
Lemma lem3231910 {A : Type'} (h1 : term61 A) : False.
Proof. exact (EQ_MP (@lem3231909 A h1) (@lem3229621 A h1)). Qed.
Lemma lem3231911 {A : Type'} : term60 A.
Proof. exact (fun h0 : term61 A => @lem3231910 A h0). Qed.
Lemma lem3231912 {A : Type'} : term58 A.
Proof. exact (EQ_MP (@lem3229620 A) (@lem3231911 A)). Qed.
Lemma lem3231913 {A : Type'} : term28 A.
Proof. exact (EQ_MP (@lem3229616 A) (@lem3231912 A)). Qed.
Lemma lem3231914 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3229464 A) (@lem3231913 A)). Qed.
Lemma lem3231915 {A : Type'} : term13 A.
Proof. exact (EQ_MP (@lem3229376 A) (@lem3231914 A)). Qed.
