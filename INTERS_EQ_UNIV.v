Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERS_EQ_UNIV_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1856_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3362390 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3362391 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3362390 A s t). Qed.
Lemma lem3362392 {A : Type'} (f : type686 A) : ((@INTERS A f) = (@UNIV A)) = (term1 A f).
Proof. exact (@lem3362391 A (@INTERS A f) (@UNIV A)). Qed.
Lemma lem3362401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3362402 {A : Type'} (f : type686 A) : (term2 A f) = (term3 A f).
Proof. exact (MK_COMB (@lem3362401) (@lem3362392 A f)). Qed.
Lemma lem3362412 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3362413 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3362412 A s t). Qed.
Lemma lem3362414 {A : Type'} (s : A -> Prop) : (s = (@UNIV A)) = (term4 A s).
Proof. exact (@lem3362413 A s (@UNIV A)). Qed.
Lemma lem3362423 {A : Type'} (s : A -> Prop) (f : type686 A) : (term5 A s f) = (term5 A s f).
Proof. exact (eq_refl (term5 A s f)). Qed.
Lemma lem3362424 {A : Type'} (f : type686 A) (s : A -> Prop) : (term6 A f s) = (term7 A f s).
Proof. exact (MK_COMB (@lem3362423 A s f) (@lem3362414 A s)). Qed.
Lemma lem3362427 {A : Type'} (f : type686 A) : (term8 A f) = (term9 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3362424 A f s)). Qed.
Lemma lem3362428 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3362429 {A : Type'} (f : type686 A) : (term10 A f) = (term11 A f).
Proof. exact (MK_COMB (@lem3362428 A) (@lem3362427 A f)). Qed.
Lemma lem3362434 {A : Type'} (f : type686 A) : (((@INTERS A f) = (@UNIV A)) = (term10 A f)) = ((term1 A f) = (term11 A f)).
Proof. exact (MK_COMB (@lem3362402 A f) (@lem3362429 A f)). Qed.
Lemma lem3362439 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (fun_ext (fun f : type686 A => @lem3362434 A f)). Qed.
Lemma lem3362440 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3362441 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem3362440 A) (@lem3362439 A)). Qed.
Lemma lem3362446 {A : Type'} : (term15 A) = (term14 A).
Proof. exact (SYM (@lem3362441 A)). Qed.
Lemma lem3362460 {A : Type'} (s : type686 A) (x : A) : (term16 A x s) = (term17 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3362461 {A : Type'} (s : type686 A) (x : A) : (term16 A x s) = (term17 A s x).
Proof. exact (@lem3362460 A s x). Qed.
Lemma lem3362462 {A : Type'} (f : type686 A) (x : A) : (term16 A x f) = (term17 A f x).
Proof. exact (@lem3362461 A f x). Qed.
Lemma lem3362470 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3362471 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3362470 (A -> Prop) P x). Qed.
Lemma lem3362472 {A : Type'} (f : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t f) = (f t).
Proof. exact (@lem3362471 A f t). Qed.
Lemma lem3362473 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3362474 {A : Type'} (f : type686 A) (t : A -> Prop) : (term5 A t f) = (term18 A f t).
Proof. exact (MK_COMB (@lem3362473) (@lem3362472 A f t)). Qed.
Lemma lem3362476 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3362477 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3362476 A P x). Qed.
Lemma lem3362478 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3362477 A t x). Qed.
Lemma lem3362479 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term19 A f x t) = (term20 A f t x).
Proof. exact (MK_COMB (@lem3362474 A f t) (@lem3362478 A t x)). Qed.
Lemma lem3362482 {A : Type'} (f : type686 A) (x : A) : (term21 A f x) = (term22 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3362479 A f t x)). Qed.
Lemma lem3362483 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3362484 {A : Type'} (f : type686 A) (x : A) : (term17 A f x) = (term23 A f x).
Proof. exact (MK_COMB (@lem3362483 A) (@lem3362482 A f x)). Qed.
Lemma lem3362489 {A : Type'} (f : type686 A) (x : A) : (term16 A x f) = (term23 A f x).
Proof. exact (TRANS (@lem3362462 A f x) (@lem3362484 A f x)). Qed.
Lemma lem3362490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3362491 {A : Type'} (f : type686 A) (x : A) : (term24 A x f) = (term25 A f x).
Proof. exact (MK_COMB (@lem3362490) (@lem3362489 A f x)). Qed.
Lemma lem3362493 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3362494 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3362493 A x). Qed.
Lemma lem3362495 {A : Type'} (f : type686 A) (x : A) : ((term16 A x f) = (@IN A x (@UNIV A))) = ((term23 A f x) = True).
Proof. exact (MK_COMB (@lem3362491 A f x) (@lem3362494 A x)). Qed.
Lemma lem3362497 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem3362498 {A : Type'} (f : type686 A) (x : A) : ((term23 A f x) = True) = (term23 A f x).
Proof. exact (@lem3362497 (term23 A f x)). Qed.
Lemma lem3362505 {A : Type'} (f : type686 A) (x : A) : ((term16 A x f) = (@IN A x (@UNIV A))) = (term23 A f x).
Proof. exact (TRANS (@lem3362495 A f x) (@lem3362498 A f x)). Qed.
Lemma lem3362506 {A : Type'} (f : type686 A) : (term26 A f) = (term27 A f).
Proof. exact (fun_ext (fun x : A => @lem3362505 A f x)). Qed.
Lemma lem3362507 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3362508 {A : Type'} (f : type686 A) : (term1 A f) = (term28 A f).
Proof. exact (MK_COMB (@lem3362507 A) (@lem3362506 A f)). Qed.
Lemma lem3362513 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3362514 {A : Type'} (f : type686 A) : (term3 A f) = (term29 A f).
Proof. exact (MK_COMB (@lem3362513) (@lem3362508 A f)). Qed.
Lemma lem3362522 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3362523 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem3362522 (A -> Prop) P x). Qed.
Lemma lem3362524 {A : Type'} (f : type686 A) (s : A -> Prop) : (@IN (A -> Prop) s f) = (f s).
Proof. exact (@lem3362523 A f s). Qed.
Lemma lem3362525 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3362526 {A : Type'} (f : type686 A) (s : A -> Prop) : (term5 A s f) = (term18 A f s).
Proof. exact (MK_COMB (@lem3362525) (@lem3362524 A f s)). Qed.
Lemma lem3362534 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3362535 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3362534 A P x). Qed.
Lemma lem3362536 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3362535 A s x). Qed.
Lemma lem3362537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3362538 {A : Type'} (s : A -> Prop) (x : A) : (term30 A x s) = (term31 A s x).
Proof. exact (MK_COMB (@lem3362537) (@lem3362536 A s x)). Qed.
Lemma lem3362540 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem3362541 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem3362540 A x). Qed.
Lemma lem3362542 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@UNIV A))) = ((s x) = True).
Proof. exact (MK_COMB (@lem3362538 A s x) (@lem3362541 A x)). Qed.
Lemma lem3362544 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem3362545 {A : Type'} (s : A -> Prop) (x : A) : ((s x) = True) = (s x).
Proof. exact (@lem3362544 (s x)). Qed.
Lemma lem3362546 {A : Type'} (s : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x (@UNIV A))) = (s x).
Proof. exact (TRANS (@lem3362542 A s x) (@lem3362545 A s x)). Qed.
Lemma lem3362547 {A : Type'} (s : A -> Prop) : (term32 A s) = (term33 A s).
Proof. exact (fun_ext (fun x : A => @lem3362546 A s x)). Qed.
Lemma lem3362548 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3362549 {A : Type'} (s : A -> Prop) : (term4 A s) = (term34 A s).
Proof. exact (MK_COMB (@lem3362548 A) (@lem3362547 A s)). Qed.
Lemma lem3362554 {A : Type'} (f : type686 A) (s : A -> Prop) : (term7 A f s) = (term35 A f s).
Proof. exact (MK_COMB (@lem3362526 A f s) (@lem3362549 A s)). Qed.
Lemma lem3362557 {A : Type'} (f : type686 A) : (term9 A f) = (term36 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3362554 A f s)). Qed.
Lemma lem3362558 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3362559 {A : Type'} (f : type686 A) : (term11 A f) = (term37 A f).
Proof. exact (MK_COMB (@lem3362558 A) (@lem3362557 A f)). Qed.
Lemma lem3362564 {A : Type'} (f : type686 A) : ((term1 A f) = (term11 A f)) = ((term28 A f) = (term37 A f)).
Proof. exact (MK_COMB (@lem3362514 A f) (@lem3362559 A f)). Qed.
Lemma lem3362567 {A : Type'} : (term13 A) = (term38 A).
Proof. exact (fun_ext (fun f : type686 A => @lem3362564 A f)). Qed.
Lemma lem3362568 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3362569 {A : Type'} : (term15 A) = (term39 A).
Proof. exact (MK_COMB (@lem3362568 A) (@lem3362567 A)). Qed.
Lemma lem3362574 {A : Type'} : (term39 A) = (term15 A).
Proof. exact (SYM (@lem3362569 A)). Qed.
Lemma lem3362576 (p : Prop) : p = (term40 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3362577 {A : Type'} : (term39 A) = (term41 A).
Proof. exact (@lem3362576 (term39 A)). Qed.
Lemma lem3362578 {A : Type'} : (term41 A) = (term39 A).
Proof. exact (SYM (@lem3362577 A)). Qed.
Lemma lem3362579 {A : Type'} (h1 : term42 A) : term42 A.
Proof. exact (h1). Qed.
Lemma lem3362582 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (h1). Qed.
Lemma lem3362583 {A : Type'} : term43 A.
Proof. exact (fun h0 : term41 A => @lem3362582 A h0). Qed.
Lemma lem3362584 {A : Type'} (h1 : term43 A) : term43 A.
Proof. exact (h1). Qed.
Lemma lem3362585 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (h1). Qed.
Lemma lem3362586 {A : Type'} (h1 : term41 A) (h2 : term43 A) : term41 A.
Proof. exact (@lem3362584 A h2 (@lem3362585 A h1)). Qed.
Lemma lem3362587 {A : Type'} (h1 : term41 A) : term44 A.
Proof. exact (fun h0 : term43 A => @lem3362586 A h1 h0). Qed.
Lemma lem3362588 {A : Type'} (h1 : term43 A) : term43 A.
Proof. exact (h1). Qed.
Lemma lem3362589 {A : Type'} (h1 : term41 A) (h2 : term43 A) : term41 A.
Proof. exact (@lem3362587 A h1 (@lem3362588 A h2)). Qed.
Lemma lem3362590 {A : Type'} (h1 : term43 A) : term43 A.
Proof. exact (fun h0 : term41 A => @lem3362589 A h0 h1). Qed.
Lemma lem3362591 {A : Type'} : term45 A.
Proof. exact (fun h0 : term43 A => @lem3362590 A h0). Qed.
Lemma lem3362594 {A : Type'} : term43 A.
Proof. exact (@lem3362591 A (@lem3362583 A)). Qed.
Lemma lem3362595 {A : Type'} : term43 A.
Proof. exact (@lem3362594 A). Qed.
Lemma lem3362597 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3362598 {A : Type'} : (term41 A) = (term46 A).
Proof. exact (@lem3362597 (term42 A)). Qed.
Lemma lem3362600 (t : Prop) : (term47 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3362601 {A : Type'} : (term46 A) = (term39 A).
Proof. exact (@lem3362600 (term39 A)). Qed.
Lemma lem3362630 {A : Type'} : (term41 A) = (term39 A).
Proof. exact (TRANS (@lem3362598 A) (@lem3362601 A)). Qed.
Lemma lem3362631 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3362632 {A : Type'} (s : A -> Prop) : (term33 A s) = (term33 A s).
Proof. exact (fun_ext (fun x : A => @lem3362631 A s x)). Qed.
Lemma lem3362633 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3362634 {A : Type'} (s : A -> Prop) : (term34 A s) = (term34 A s).
Proof. exact (MK_COMB (@lem3362633 A) (@lem3362632 A s)). Qed.
Lemma lem3362637 {A : Type'} (f : type686 A) (s : A -> Prop) : (term18 A f s) = (term18 A f s).
Proof. exact (eq_refl (term18 A f s)). Qed.
Lemma lem3362638 {A : Type'} (f : type686 A) (s : A -> Prop) : (term35 A f s) = (term35 A f s).
Proof. exact (MK_COMB (@lem3362637 A f s) (@lem3362634 A s)). Qed.
Lemma lem3362639 {A : Type'} (f : type686 A) : (term36 A f) = (term36 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3362638 A f s)). Qed.
Lemma lem3362640 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3362641 {A : Type'} (f : type686 A) : (term37 A f) = (term37 A f).
Proof. exact (MK_COMB (@lem3362640 A) (@lem3362639 A f)). Qed.
Lemma lem3362646 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term20 A f t x) = (term20 A f t x).
Proof. exact (eq_refl (term20 A f t x)). Qed.
Lemma lem3362647 {A : Type'} (f : type686 A) (x : A) : (term22 A f x) = (term22 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3362646 A f t x)). Qed.
Lemma lem3362648 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3362649 {A : Type'} (f : type686 A) (x : A) : (term23 A f x) = (term23 A f x).
Proof. exact (MK_COMB (@lem3362648 A) (@lem3362647 A f x)). Qed.
Lemma lem3362650 {A : Type'} (f : type686 A) : (term27 A f) = (term27 A f).
Proof. exact (fun_ext (fun x : A => @lem3362649 A f x)). Qed.
Lemma lem3362651 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3362652 {A : Type'} (f : type686 A) : (term28 A f) = (term28 A f).
Proof. exact (MK_COMB (@lem3362651 A) (@lem3362650 A f)). Qed.
Lemma lem3362653 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3362654 {A : Type'} (f : type686 A) : (term29 A f) = (term29 A f).
Proof. exact (MK_COMB (@lem3362653) (@lem3362652 A f)). Qed.
Lemma lem3362655 {A : Type'} (f : type686 A) : ((term28 A f) = (term37 A f)) = ((term28 A f) = (term37 A f)).
Proof. exact (MK_COMB (@lem3362654 A f) (@lem3362641 A f)). Qed.
Lemma lem3362656 {A : Type'} : (term38 A) = (term38 A).
Proof. exact (fun_ext (fun f : type686 A => @lem3362655 A f)). Qed.
Lemma lem3362657 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3362658 {A : Type'} : (term39 A) = (term39 A).
Proof. exact (MK_COMB (@lem3362657 A) (@lem3362656 A)). Qed.
Lemma lem3362695 {A : Type'} : (term41 A) = (term39 A).
Proof. exact (TRANS (@lem3362630 A) (@lem3362658 A)). Qed.
Lemma lem3362696 {A : Type'} : (term39 A) = (term41 A).
Proof. exact (SYM (@lem3362695 A)). Qed.
Lemma lem3362698 (p : Prop) : p = (term40 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3362699 {A : Type'} (f : type686 A) : ((term28 A f) = (term37 A f)) = (term48 A f).
Proof. exact (@lem3362698 ((term28 A f) = (term37 A f))). Qed.
Lemma lem3362700 {A : Type'} (f : type686 A) : (term48 A f) = ((term28 A f) = (term37 A f)).
Proof. exact (SYM (@lem3362699 A f)). Qed.
Lemma lem3362701 {A : Type'} (f : type686 A) (h1 : term49 A f) : term49 A f.
Proof. exact (h1). Qed.
Lemma lem3362710 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term50 A f t x) = (term51 A f t x).
Proof. exact (@lem17362 (f t) (t x)). Qed.
Lemma lem3362715 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term20 A f t x) = (term52 A f t x).
Proof. exact (@lem17265 (f t) (t x)). Qed.
Lemma lem3362716 {A : Type'} (P : type686 A) : (term53 A P) = (term54 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3362717 {A : Type'} (f : type686 A) (x : A) : (term55 A f x) = (term56 A f x).
Proof. exact (@lem3362716 A (term22 A f x)). Qed.
Lemma lem3362718 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term57 A f x t) = (term20 A f t x).
Proof. exact (eq_refl (term57 A f x t)). Qed.
Lemma lem3362719 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3362720 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term58 A f x t) = (term50 A f t x).
Proof. exact (MK_COMB (@lem3362719) (@lem3362718 A f t x)). Qed.
Lemma lem3362721 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term58 A f x t) = (term51 A f t x).
Proof. exact (TRANS (@lem3362720 A f t x) (@lem3362710 A f t x)). Qed.
Lemma lem3362722 {A : Type'} (f : type686 A) (x : A) : (term59 A f x) = (term60 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3362721 A f t x)). Qed.
Lemma lem3362723 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3362724 {A : Type'} (f : type686 A) (x : A) : (term56 A f x) = (term61 A f x).
Proof. exact (MK_COMB (@lem3362723 A) (@lem3362722 A f x)). Qed.
Lemma lem3362725 {A : Type'} (f : type686 A) (x : A) : (term55 A f x) = (term61 A f x).
Proof. exact (TRANS (@lem3362717 A f x) (@lem3362724 A f x)). Qed.
Lemma lem3362726 {A : Type'} (f : type686 A) (x : A) : (term22 A f x) = (term62 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3362715 A f t x)). Qed.
Lemma lem3362727 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3362728 {A : Type'} (f : type686 A) (x : A) : (term23 A f x) = (term63 A f x).
Proof. exact (MK_COMB (@lem3362727 A) (@lem3362726 A f x)). Qed.
Lemma lem3362729 {A : Type'} (P : A -> Prop) : (term64 A P) = (term65 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3362730 {A : Type'} (f : type686 A) : (term66 A f) = (term67 A f).
Proof. exact (@lem3362729 A (term27 A f)). Qed.
Lemma lem3362731 {A : Type'} (f : type686 A) (x : A) : (term68 A f x) = (term23 A f x).
Proof. exact (eq_refl (term68 A f x)). Qed.
Lemma lem3362732 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3362733 {A : Type'} (f : type686 A) (x : A) : (term69 A f x) = (term55 A f x).
Proof. exact (MK_COMB (@lem3362732) (@lem3362731 A f x)). Qed.
Lemma lem3362734 {A : Type'} (f : type686 A) (x : A) : (term69 A f x) = (term61 A f x).
Proof. exact (TRANS (@lem3362733 A f x) (@lem3362725 A f x)). Qed.
Lemma lem3362735 {A : Type'} (f : type686 A) : (term70 A f) = (term71 A f).
Proof. exact (fun_ext (fun x : A => @lem3362734 A f x)). Qed.
Lemma lem3362736 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3362737 {A : Type'} (f : type686 A) : (term67 A f) = (term72 A f).
Proof. exact (MK_COMB (@lem3362736 A) (@lem3362735 A f)). Qed.
Lemma lem3362738 {A : Type'} (f : type686 A) : (term66 A f) = (term72 A f).
Proof. exact (TRANS (@lem3362730 A f) (@lem3362737 A f)). Qed.
Lemma lem3362739 {A : Type'} (f : type686 A) : (term27 A f) = (term73 A f).
Proof. exact (fun_ext (fun x : A => @lem3362728 A f x)). Qed.
Lemma lem3362740 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3362741 {A : Type'} (f : type686 A) : (term28 A f) = (term74 A f).
Proof. exact (MK_COMB (@lem3362740 A) (@lem3362739 A f)). Qed.
Lemma lem3362745 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3362746 {A : Type'} (P : A -> Prop) : (term64 A P) = (term65 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3362747 {A : Type'} (s : A -> Prop) : (term75 A s) = (term76 A s).
Proof. exact (@lem3362746 A (term33 A s)). Qed.
Lemma lem3362748 {A : Type'} (s : A -> Prop) (x : A) : (term77 A s x) = (s x).
Proof. exact (eq_refl (term77 A s x)). Qed.
Lemma lem3362749 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3362751 {A : Type'} (s : A -> Prop) (x : A) : (term78 A s x) = (term79 A s x).
Proof. exact (MK_COMB (@lem3362749) (@lem3362748 A s x)). Qed.
Lemma lem3362752 {A : Type'} (s : A -> Prop) : (term80 A s) = (term81 A s).
Proof. exact (fun_ext (fun x : A => @lem3362751 A s x)). Qed.
Lemma lem3362753 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3362754 {A : Type'} (s : A -> Prop) : (term76 A s) = (term65 A s).
Proof. exact (MK_COMB (@lem3362753 A) (@lem3362752 A s)). Qed.
Lemma lem3362755 {A : Type'} (s : A -> Prop) : (term75 A s) = (term65 A s).
Proof. exact (TRANS (@lem3362747 A s) (@lem3362754 A s)). Qed.
Lemma lem3362756 {A : Type'} (s : A -> Prop) : (term33 A s) = (term33 A s).
Proof. exact (fun_ext (fun x : A => @lem3362745 A s x)). Qed.
Lemma lem3362757 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3362758 {A : Type'} (s : A -> Prop) : (term34 A s) = (term34 A s).
Proof. exact (MK_COMB (@lem3362757 A) (@lem3362756 A s)). Qed.
Lemma lem3362760 {A : Type'} (f : type686 A) (s : A -> Prop) : (term82 A f s) = (term82 A f s).
Proof. exact (eq_refl (term82 A f s)). Qed.
Lemma lem3362761 {A : Type'} (f : type686 A) (s : A -> Prop) : (term83 A f s) = (term84 A f s).
Proof. exact (MK_COMB (@lem3362760 A f s) (@lem3362755 A s)). Qed.
Lemma lem3362762 {A : Type'} (f : type686 A) (s : A -> Prop) : (term85 A f s) = (term83 A f s).
Proof. exact (@lem17362 (f s) (term34 A s)). Qed.
Lemma lem3362763 {A : Type'} (f : type686 A) (s : A -> Prop) : (term85 A f s) = (term84 A f s).
Proof. exact (TRANS (@lem3362762 A f s) (@lem3362761 A f s)). Qed.
Lemma lem3362765 {A : Type'} (f : type686 A) (s : A -> Prop) : (term86 A f s) = (term86 A f s).
Proof. exact (eq_refl (term86 A f s)). Qed.
Lemma lem3362766 {A : Type'} (f : type686 A) (s : A -> Prop) : (term87 A f s) = (term87 A f s).
Proof. exact (MK_COMB (@lem3362765 A f s) (@lem3362758 A s)). Qed.
Lemma lem3362767 {A : Type'} (f : type686 A) (s : A -> Prop) : (term35 A f s) = (term87 A f s).
Proof. exact (@lem17265 (f s) (term34 A s)). Qed.
Lemma lem3362768 {A : Type'} (f : type686 A) (s : A -> Prop) : (term35 A f s) = (term87 A f s).
Proof. exact (TRANS (@lem3362767 A f s) (@lem3362766 A f s)). Qed.
Lemma lem3362769 {A : Type'} (P : type686 A) : (term53 A P) = (term54 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3362770 {A : Type'} (f : type686 A) : (term88 A f) = (term89 A f).
Proof. exact (@lem3362769 A (term36 A f)). Qed.
Lemma lem3362771 {A : Type'} (f : type686 A) (s : A -> Prop) : (term90 A f s) = (term35 A f s).
Proof. exact (eq_refl (term90 A f s)). Qed.
Lemma lem3362772 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3362773 {A : Type'} (f : type686 A) (s : A -> Prop) : (term91 A f s) = (term85 A f s).
Proof. exact (MK_COMB (@lem3362772) (@lem3362771 A f s)). Qed.
Lemma lem3362774 {A : Type'} (f : type686 A) (s : A -> Prop) : (term91 A f s) = (term84 A f s).
Proof. exact (TRANS (@lem3362773 A f s) (@lem3362763 A f s)). Qed.
Lemma lem3362775 {A : Type'} (f : type686 A) : (term92 A f) = (term93 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3362774 A f s)). Qed.
Lemma lem3362776 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3362777 {A : Type'} (f : type686 A) : (term89 A f) = (term94 A f).
Proof. exact (MK_COMB (@lem3362776 A) (@lem3362775 A f)). Qed.
Lemma lem3362778 {A : Type'} (f : type686 A) : (term88 A f) = (term94 A f).
Proof. exact (TRANS (@lem3362770 A f) (@lem3362777 A f)). Qed.
Lemma lem3362779 {A : Type'} (f : type686 A) : (term36 A f) = (term95 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3362768 A f s)). Qed.
Lemma lem3362780 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3362781 {A : Type'} (f : type686 A) : (term37 A f) = (term96 A f).
Proof. exact (MK_COMB (@lem3362780 A) (@lem3362779 A f)). Qed.
Lemma lem3362782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3362783 {A : Type'} (f : type686 A) : (term97 A f) = (term98 A f).
Proof. exact (MK_COMB (@lem3362782) (@lem3362738 A f)). Qed.
Lemma lem3362784 {A : Type'} (f : type686 A) : (term99 A f) = (term100 A f).
Proof. exact (MK_COMB (@lem3362783 A f) (@lem3362781 A f)). Qed.
Lemma lem3362785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3362786 {A : Type'} (f : type686 A) : (term101 A f) = (term102 A f).
Proof. exact (MK_COMB (@lem3362785) (@lem3362741 A f)). Qed.
Lemma lem3362787 {A : Type'} (f : type686 A) : (term103 A f) = (term104 A f).
Proof. exact (MK_COMB (@lem3362786 A f) (@lem3362778 A f)). Qed.
Lemma lem3362788 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3362789 {A : Type'} (f : type686 A) : (term105 A f) = (term106 A f).
Proof. exact (MK_COMB (@lem3362788) (@lem3362787 A f)). Qed.
Lemma lem3362790 {A : Type'} (f : type686 A) : (term107 A f) = (term108 A f).
Proof. exact (MK_COMB (@lem3362789 A f) (@lem3362784 A f)). Qed.
Lemma lem3362791 {A : Type'} (f : type686 A) : (term49 A f) = (term107 A f).
Proof. exact (@lem17646 (term28 A f) (term37 A f)). Qed.
Lemma lem3362792 {A : Type'} (f : type686 A) : (term49 A f) = (term108 A f).
Proof. exact (TRANS (@lem3362791 A f) (@lem3362790 A f)). Qed.
Lemma lem3362963 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3362964 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (@lem3362963 A P Q). Qed.
Lemma lem3362965 {A : Type'} (f : type686 A) (s : A -> Prop) : (term111 A f s) = (term112 A f s).
Proof. exact (@lem3362964 A (f s) (term81 A s)). Qed.
Lemma lem3362966 {A : Type'} (s : A -> Prop) (x : A) : (term113 A s x) = (term79 A s x).
Proof. exact (eq_refl (term113 A s x)). Qed.
Lemma lem3362967 {A : Type'} (s : A -> Prop) : (term114 A s) = (term81 A s).
Proof. exact (fun_ext (fun x : A => @lem3362966 A s x)). Qed.
Lemma lem3362968 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3362969 {A : Type'} (s : A -> Prop) : (term115 A s) = (term65 A s).
Proof. exact (MK_COMB (@lem3362968 A) (@lem3362967 A s)). Qed.
Lemma lem3362970 {A : Type'} (f : type686 A) (s : A -> Prop) : (term82 A f s) = (term82 A f s).
Proof. exact (eq_refl (term82 A f s)). Qed.
Lemma lem3362971 {A : Type'} (f : type686 A) (s : A -> Prop) : (term111 A f s) = (term84 A f s).
Proof. exact (MK_COMB (@lem3362970 A f s) (@lem3362969 A s)). Qed.
Lemma lem3362972 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3362973 {A : Type'} (f : type686 A) (s : A -> Prop) : (term116 A f s) = (term117 A f s).
Proof. exact (MK_COMB (@lem3362972) (@lem3362971 A f s)). Qed.
Lemma lem3362974 {A : Type'} (s : A -> Prop) (x : A) : (term113 A s x) = (term79 A s x).
Proof. exact (eq_refl (term113 A s x)). Qed.
Lemma lem3362975 {A : Type'} (f : type686 A) (s : A -> Prop) : (term82 A f s) = (term82 A f s).
Proof. exact (eq_refl (term82 A f s)). Qed.
Lemma lem3362976 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term118 A f s x) = (term51 A f s x).
Proof. exact (MK_COMB (@lem3362975 A f s) (@lem3362974 A s x)). Qed.
Lemma lem3362977 {A : Type'} (f : type686 A) (s : A -> Prop) : (term119 A f s) = (term120 A f s).
Proof. exact (fun_ext (fun x : A => @lem3362976 A f s x)). Qed.
Lemma lem3362978 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3362979 {A : Type'} (f : type686 A) (s : A -> Prop) : (term112 A f s) = (term121 A f s).
Proof. exact (MK_COMB (@lem3362978 A) (@lem3362977 A f s)). Qed.
Lemma lem3362980 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term111 A f s) = (term112 A f s)) = ((term84 A f s) = (term121 A f s)).
Proof. exact (MK_COMB (@lem3362973 A f s) (@lem3362979 A f s)). Qed.
Lemma lem3362981 {A : Type'} (f : type686 A) (s : A -> Prop) : (term84 A f s) = (term121 A f s).
Proof. exact (EQ_MP (@lem3362980 A f s) (@lem3362965 A f s)). Qed.
Lemma lem3362982 {A : Type'} (f : type686 A) : (term93 A f) = (term122 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3362981 A f s)). Qed.
Lemma lem3362983 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3362984 {A : Type'} (f : type686 A) : (term94 A f) = (term123 A f).
Proof. exact (MK_COMB (@lem3362983 A) (@lem3362982 A f)). Qed.
Lemma lem3362985 {A : Type'} (f : type686 A) : (term102 A f) = (term102 A f).
Proof. exact (eq_refl (term102 A f)). Qed.
Lemma lem3362986 {A : Type'} (f : type686 A) : (term104 A f) = (term124 A f).
Proof. exact (MK_COMB (@lem3362985 A f) (@lem3362984 A f)). Qed.
Lemma lem3362988 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3362989 {A : Type'} (P : Prop) (Q : type686 A) : (term125 A P Q) = (term126 A P Q).
Proof. exact (@lem3362988 (A -> Prop) P Q). Qed.
Lemma lem3362990 {A : Type'} (f : type686 A) : (term127 A f) = (term128 A f).
Proof. exact (@lem3362989 A (term74 A f) (term122 A f)). Qed.
Lemma lem3362991 {A : Type'} (f : type686 A) (s : A -> Prop) : (term129 A f s) = (term121 A f s).
Proof. exact (eq_refl (term129 A f s)). Qed.
Lemma lem3362992 {A : Type'} (f : type686 A) : (term130 A f) = (term122 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3362991 A f s)). Qed.
Lemma lem3362993 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3362994 {A : Type'} (f : type686 A) : (term131 A f) = (term123 A f).
Proof. exact (MK_COMB (@lem3362993 A) (@lem3362992 A f)). Qed.
Lemma lem3362995 {A : Type'} (f : type686 A) : (term102 A f) = (term102 A f).
Proof. exact (eq_refl (term102 A f)). Qed.
Lemma lem3362996 {A : Type'} (f : type686 A) : (term127 A f) = (term124 A f).
Proof. exact (MK_COMB (@lem3362995 A f) (@lem3362994 A f)). Qed.
Lemma lem3362997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3362998 {A : Type'} (f : type686 A) : (term132 A f) = (term133 A f).
Proof. exact (MK_COMB (@lem3362997) (@lem3362996 A f)). Qed.
Lemma lem3362999 {A : Type'} (f : type686 A) (s : A -> Prop) : (term129 A f s) = (term121 A f s).
Proof. exact (eq_refl (term129 A f s)). Qed.
Lemma lem3363000 {A : Type'} (f : type686 A) : (term102 A f) = (term102 A f).
Proof. exact (eq_refl (term102 A f)). Qed.
Lemma lem3363001 {A : Type'} (f : type686 A) (s : A -> Prop) : (term134 A f s) = (term135 A f s).
Proof. exact (MK_COMB (@lem3363000 A f) (@lem3362999 A f s)). Qed.
Lemma lem3363002 {A : Type'} (f : type686 A) : (term136 A f) = (term137 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3363001 A f s)). Qed.
Lemma lem3363003 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3363004 {A : Type'} (f : type686 A) : (term128 A f) = (term138 A f).
Proof. exact (MK_COMB (@lem3363003 A) (@lem3363002 A f)). Qed.
Lemma lem3363005 {A : Type'} (f : type686 A) : ((term127 A f) = (term128 A f)) = ((term124 A f) = (term138 A f)).
Proof. exact (MK_COMB (@lem3362998 A f) (@lem3363004 A f)). Qed.
Lemma lem3363006 {A : Type'} (f : type686 A) : (term124 A f) = (term138 A f).
Proof. exact (EQ_MP (@lem3363005 A f) (@lem3362990 A f)). Qed.
Lemma lem3363008 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3363009 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (@lem3363008 A P Q). Qed.
Lemma lem3363010 {A : Type'} (f : type686 A) (s : A -> Prop) : (term139 A f s) = (term140 A f s).
Proof. exact (@lem3363009 A (term74 A f) (term120 A f s)). Qed.
Lemma lem3363011 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term141 A f s x) = (term51 A f s x).
Proof. exact (eq_refl (term141 A f s x)). Qed.
Lemma lem3363012 {A : Type'} (f : type686 A) (s : A -> Prop) : (term142 A f s) = (term120 A f s).
Proof. exact (fun_ext (fun x : A => @lem3363011 A f s x)). Qed.
Lemma lem3363013 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3363014 {A : Type'} (f : type686 A) (s : A -> Prop) : (term143 A f s) = (term121 A f s).
Proof. exact (MK_COMB (@lem3363013 A) (@lem3363012 A f s)). Qed.
Lemma lem3363015 {A : Type'} (f : type686 A) : (term102 A f) = (term102 A f).
Proof. exact (eq_refl (term102 A f)). Qed.
Lemma lem3363016 {A : Type'} (f : type686 A) (s : A -> Prop) : (term139 A f s) = (term135 A f s).
Proof. exact (MK_COMB (@lem3363015 A f) (@lem3363014 A f s)). Qed.
Lemma lem3363017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3363018 {A : Type'} (f : type686 A) (s : A -> Prop) : (term144 A f s) = (term145 A f s).
Proof. exact (MK_COMB (@lem3363017) (@lem3363016 A f s)). Qed.
Lemma lem3363019 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term141 A f s x) = (term51 A f s x).
Proof. exact (eq_refl (term141 A f s x)). Qed.
Lemma lem3363020 {A : Type'} (f : type686 A) : (term102 A f) = (term102 A f).
Proof. exact (eq_refl (term102 A f)). Qed.
Lemma lem3363021 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term146 A f s x) = (term147 A f s x).
Proof. exact (MK_COMB (@lem3363020 A f) (@lem3363019 A f s x)). Qed.
Lemma lem3363022 {A : Type'} (f : type686 A) (s : A -> Prop) : (term148 A f s) = (term149 A f s).
Proof. exact (fun_ext (fun x : A => @lem3363021 A f s x)). Qed.
Lemma lem3363023 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3363024 {A : Type'} (f : type686 A) (s : A -> Prop) : (term140 A f s) = (term150 A f s).
Proof. exact (MK_COMB (@lem3363023 A) (@lem3363022 A f s)). Qed.
Lemma lem3363025 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term139 A f s) = (term140 A f s)) = ((term135 A f s) = (term150 A f s)).
Proof. exact (MK_COMB (@lem3363018 A f s) (@lem3363024 A f s)). Qed.
Lemma lem3363026 {A : Type'} (f : type686 A) (s : A -> Prop) : (term135 A f s) = (term150 A f s).
Proof. exact (EQ_MP (@lem3363025 A f s) (@lem3363010 A f s)). Qed.
Lemma lem3363027 {A : Type'} (f : type686 A) : (term137 A f) = (term151 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3363026 A f s)). Qed.
Lemma lem3363028 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3363029 {A : Type'} (f : type686 A) : (term138 A f) = (term152 A f).
Proof. exact (MK_COMB (@lem3363028 A) (@lem3363027 A f)). Qed.
Lemma lem3363030 {A : Type'} (f : type686 A) : (term124 A f) = (term152 A f).
Proof. exact (TRANS (@lem3363006 A f) (@lem3363029 A f)). Qed.
Lemma lem3363031 {A : Type'} (f : type686 A) : (term104 A f) = (term152 A f).
Proof. exact (TRANS (@lem3362986 A f) (@lem3363030 A f)). Qed.
Lemma lem3363032 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3363033 {A : Type'} (f : type686 A) : (term106 A f) = (term153 A f).
Proof. exact (MK_COMB (@lem3363032) (@lem3363031 A f)). Qed.
Lemma lem3363035 {A : Type'} (P : A -> Prop) (Q : Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3363036 {A : Type'} (P : A -> Prop) (Q : Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (@lem3363035 A P Q). Qed.
Lemma lem3363037 {A : Type'} (f : type686 A) : (term156 A f) = (term157 A f).
Proof. exact (@lem3363036 A (term71 A f) (term96 A f)). Qed.
Lemma lem3363038 {A : Type'} (f : type686 A) (x : A) : (term158 A f x) = (term61 A f x).
Proof. exact (eq_refl (term158 A f x)). Qed.
Lemma lem3363039 {A : Type'} (f : type686 A) : (term159 A f) = (term71 A f).
Proof. exact (fun_ext (fun x : A => @lem3363038 A f x)). Qed.
Lemma lem3363040 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3363041 {A : Type'} (f : type686 A) : (term160 A f) = (term72 A f).
Proof. exact (MK_COMB (@lem3363040 A) (@lem3363039 A f)). Qed.
Lemma lem3363042 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3363043 {A : Type'} (f : type686 A) : (term161 A f) = (term98 A f).
Proof. exact (MK_COMB (@lem3363042) (@lem3363041 A f)). Qed.
Lemma lem3363044 {A : Type'} (f : type686 A) : (term96 A f) = (term96 A f).
Proof. exact (eq_refl (term96 A f)). Qed.
Lemma lem3363045 {A : Type'} (f : type686 A) : (term156 A f) = (term100 A f).
Proof. exact (MK_COMB (@lem3363043 A f) (@lem3363044 A f)). Qed.
Lemma lem3363046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3363047 {A : Type'} (f : type686 A) : (term162 A f) = (term163 A f).
Proof. exact (MK_COMB (@lem3363046) (@lem3363045 A f)). Qed.
Lemma lem3363048 {A : Type'} (f : type686 A) (x : A) : (term158 A f x) = (term61 A f x).
Proof. exact (eq_refl (term158 A f x)). Qed.
Lemma lem3363049 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3363050 {A : Type'} (f : type686 A) (x : A) : (term164 A f x) = (term165 A f x).
Proof. exact (MK_COMB (@lem3363049) (@lem3363048 A f x)). Qed.
Lemma lem3363051 {A : Type'} (f : type686 A) : (term96 A f) = (term96 A f).
Proof. exact (eq_refl (term96 A f)). Qed.
Lemma lem3363052 {A : Type'} (x : A) (f : type686 A) : (term166 A x f) = (term167 A x f).
Proof. exact (MK_COMB (@lem3363050 A f x) (@lem3363051 A f)). Qed.
Lemma lem3363053 {A : Type'} (f : type686 A) : (term168 A f) = (term169 A f).
Proof. exact (fun_ext (fun x : A => @lem3363052 A x f)). Qed.
Lemma lem3363054 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3363055 {A : Type'} (f : type686 A) : (term157 A f) = (term170 A f).
Proof. exact (MK_COMB (@lem3363054 A) (@lem3363053 A f)). Qed.
Lemma lem3363056 {A : Type'} (f : type686 A) : ((term156 A f) = (term157 A f)) = ((term100 A f) = (term170 A f)).
Proof. exact (MK_COMB (@lem3363047 A f) (@lem3363055 A f)). Qed.
Lemma lem3363057 {A : Type'} (f : type686 A) : (term100 A f) = (term170 A f).
Proof. exact (EQ_MP (@lem3363056 A f) (@lem3363037 A f)). Qed.
Lemma lem3363059 {A : Type'} (P : A -> Prop) (Q : Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3363060 {A : Type'} (P : type686 A) (Q : Prop) : (term171 A P Q) = (term172 A P Q).
Proof. exact (@lem3363059 (A -> Prop) P Q). Qed.
Lemma lem3363061 {A : Type'} (x : A) (f : type686 A) : (term173 A x f) = (term174 A x f).
Proof. exact (@lem3363060 A (term60 A f x) (term96 A f)). Qed.
Lemma lem3363062 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term175 A f x t) = (term51 A f t x).
Proof. exact (eq_refl (term175 A f x t)). Qed.
Lemma lem3363063 {A : Type'} (f : type686 A) (x : A) : (term176 A f x) = (term60 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3363062 A f t x)). Qed.
Lemma lem3363064 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3363065 {A : Type'} (f : type686 A) (x : A) : (term177 A f x) = (term61 A f x).
Proof. exact (MK_COMB (@lem3363064 A) (@lem3363063 A f x)). Qed.
Lemma lem3363066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3363067 {A : Type'} (f : type686 A) (x : A) : (term178 A f x) = (term165 A f x).
Proof. exact (MK_COMB (@lem3363066) (@lem3363065 A f x)). Qed.
Lemma lem3363068 {A : Type'} (f : type686 A) : (term96 A f) = (term96 A f).
Proof. exact (eq_refl (term96 A f)). Qed.
Lemma lem3363069 {A : Type'} (x : A) (f : type686 A) : (term173 A x f) = (term167 A x f).
Proof. exact (MK_COMB (@lem3363067 A f x) (@lem3363068 A f)). Qed.
Lemma lem3363070 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3363071 {A : Type'} (x : A) (f : type686 A) : (term179 A x f) = (term180 A x f).
Proof. exact (MK_COMB (@lem3363070) (@lem3363069 A x f)). Qed.
Lemma lem3363072 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term175 A f x t) = (term51 A f t x).
Proof. exact (eq_refl (term175 A f x t)). Qed.
Lemma lem3363073 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3363074 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term181 A f x t) = (term182 A f t x).
Proof. exact (MK_COMB (@lem3363073) (@lem3363072 A f t x)). Qed.
Lemma lem3363075 {A : Type'} (f : type686 A) : (term96 A f) = (term96 A f).
Proof. exact (eq_refl (term96 A f)). Qed.
Lemma lem3363076 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) : (term183 A x t f) = (term184 A t x f).
Proof. exact (MK_COMB (@lem3363074 A f t x) (@lem3363075 A f)). Qed.
Lemma lem3363077 {A : Type'} (x : A) (f : type686 A) : (term185 A x f) = (term186 A x f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3363076 A t x f)). Qed.
Lemma lem3363078 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3363079 {A : Type'} (x : A) (f : type686 A) : (term174 A x f) = (term187 A x f).
Proof. exact (MK_COMB (@lem3363078 A) (@lem3363077 A x f)). Qed.
Lemma lem3363080 {A : Type'} (x : A) (f : type686 A) : ((term173 A x f) = (term174 A x f)) = ((term167 A x f) = (term187 A x f)).
Proof. exact (MK_COMB (@lem3363071 A x f) (@lem3363079 A x f)). Qed.
Lemma lem3363081 {A : Type'} (x : A) (f : type686 A) : (term167 A x f) = (term187 A x f).
Proof. exact (EQ_MP (@lem3363080 A x f) (@lem3363061 A x f)). Qed.
Lemma lem3363082 {A : Type'} (f : type686 A) : (term169 A f) = (term188 A f).
Proof. exact (fun_ext (fun x : A => @lem3363081 A x f)). Qed.
Lemma lem3363083 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3363084 {A : Type'} (f : type686 A) : (term170 A f) = (term189 A f).
Proof. exact (MK_COMB (@lem3363083 A) (@lem3363082 A f)). Qed.
Lemma lem3363085 {A : Type'} (f : type686 A) : (term100 A f) = (term189 A f).
Proof. exact (TRANS (@lem3363057 A f) (@lem3363084 A f)). Qed.
Lemma lem3363086 {A : Type'} (f : type686 A) : (term108 A f) = (term190 A f).
Proof. exact (MK_COMB (@lem3363033 A f) (@lem3363085 A f)). Qed.
Lemma lem3363090 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3363091 {A : Type'} (P : type686 A) (Q : Prop) : (term193 A P Q) = (term194 A P Q).
Proof. exact (@lem3363090 (A -> Prop) P Q). Qed.
Lemma lem3363092 {A : Type'} (f : type686 A) : (term195 A f) = (term196 A f).
Proof. exact (@lem3363091 A (term151 A f) (term189 A f)). Qed.
Lemma lem3363093 {A : Type'} (f : type686 A) (s : A -> Prop) : (term197 A f s) = (term150 A f s).
Proof. exact (eq_refl (term197 A f s)). Qed.
Lemma lem3363094 {A : Type'} (f : type686 A) : (term198 A f) = (term151 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3363093 A f s)). Qed.
Lemma lem3363095 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3363096 {A : Type'} (f : type686 A) : (term199 A f) = (term152 A f).
Proof. exact (MK_COMB (@lem3363095 A) (@lem3363094 A f)). Qed.
Lemma lem3363097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3363098 {A : Type'} (f : type686 A) : (term200 A f) = (term153 A f).
Proof. exact (MK_COMB (@lem3363097) (@lem3363096 A f)). Qed.
Lemma lem3363099 {A : Type'} (f : type686 A) : (term189 A f) = (term189 A f).
Proof. exact (eq_refl (term189 A f)). Qed.
Lemma lem3363100 {A : Type'} (f : type686 A) : (term195 A f) = (term190 A f).
Proof. exact (MK_COMB (@lem3363098 A f) (@lem3363099 A f)). Qed.
Lemma lem3363101 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3363102 {A : Type'} (f : type686 A) : (term201 A f) = (term202 A f).
Proof. exact (MK_COMB (@lem3363101) (@lem3363100 A f)). Qed.
Lemma lem3363103 {A : Type'} (f : type686 A) (s : A -> Prop) : (term197 A f s) = (term150 A f s).
Proof. exact (eq_refl (term197 A f s)). Qed.
Lemma lem3363104 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3363105 {A : Type'} (f : type686 A) (s : A -> Prop) : (term203 A f s) = (term204 A f s).
Proof. exact (MK_COMB (@lem3363104) (@lem3363103 A f s)). Qed.
Lemma lem3363106 {A : Type'} (f : type686 A) : (term189 A f) = (term189 A f).
Proof. exact (eq_refl (term189 A f)). Qed.
Lemma lem3363107 {A : Type'} (s : A -> Prop) (f : type686 A) : (term205 A s f) = (term206 A s f).
Proof. exact (MK_COMB (@lem3363105 A f s) (@lem3363106 A f)). Qed.
Lemma lem3363108 {A : Type'} (f : type686 A) : (term207 A f) = (term208 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3363107 A s f)). Qed.
Lemma lem3363109 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3363110 {A : Type'} (f : type686 A) : (term196 A f) = (term209 A f).
Proof. exact (MK_COMB (@lem3363109 A) (@lem3363108 A f)). Qed.
Lemma lem3363111 {A : Type'} (f : type686 A) : ((term195 A f) = (term196 A f)) = ((term190 A f) = (term209 A f)).
Proof. exact (MK_COMB (@lem3363102 A f) (@lem3363110 A f)). Qed.
Lemma lem3363112 {A : Type'} (f : type686 A) : (term190 A f) = (term209 A f).
Proof. exact (EQ_MP (@lem3363111 A f) (@lem3363092 A f)). Qed.
Lemma lem3363114 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term210 A P Q) = (term211 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3363115 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term210 A P Q) = (term211 A P Q).
Proof. exact (@lem3363114 A P Q). Qed.
Lemma lem3363116 {A : Type'} (s : A -> Prop) (f : type686 A) : (term212 A s f) = (term213 A s f).
Proof. exact (@lem3363115 A (term149 A f s) (term188 A f)). Qed.
Lemma lem3363117 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term214 A f s x) = (term147 A f s x).
Proof. exact (eq_refl (term214 A f s x)). Qed.
Lemma lem3363118 {A : Type'} (f : type686 A) (s : A -> Prop) : (term215 A f s) = (term149 A f s).
Proof. exact (fun_ext (fun x : A => @lem3363117 A f s x)). Qed.
Lemma lem3363119 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3363120 {A : Type'} (f : type686 A) (s : A -> Prop) : (term216 A f s) = (term150 A f s).
Proof. exact (MK_COMB (@lem3363119 A) (@lem3363118 A f s)). Qed.
Lemma lem3363121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3363122 {A : Type'} (f : type686 A) (s : A -> Prop) : (term217 A f s) = (term204 A f s).
Proof. exact (MK_COMB (@lem3363121) (@lem3363120 A f s)). Qed.
Lemma lem3363123 {A : Type'} (x : A) (f : type686 A) : (term218 A f x) = (term187 A x f).
Proof. exact (eq_refl (term218 A f x)). Qed.
Lemma lem3363124 {A : Type'} (f : type686 A) : (term219 A f) = (term188 A f).
Proof. exact (fun_ext (fun x : A => @lem3363123 A x f)). Qed.
Lemma lem3363125 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3363126 {A : Type'} (f : type686 A) : (term220 A f) = (term189 A f).
Proof. exact (MK_COMB (@lem3363125 A) (@lem3363124 A f)). Qed.
Lemma lem3363127 {A : Type'} (s : A -> Prop) (f : type686 A) : (term212 A s f) = (term206 A s f).
Proof. exact (MK_COMB (@lem3363122 A f s) (@lem3363126 A f)). Qed.
Lemma lem3363128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3363129 {A : Type'} (s : A -> Prop) (f : type686 A) : (term221 A s f) = (term222 A s f).
Proof. exact (MK_COMB (@lem3363128) (@lem3363127 A s f)). Qed.
Lemma lem3363130 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term214 A f s x) = (term147 A f s x).
Proof. exact (eq_refl (term214 A f s x)). Qed.
Lemma lem3363131 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3363132 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term223 A f s x) = (term224 A f s x).
Proof. exact (MK_COMB (@lem3363131) (@lem3363130 A f s x)). Qed.
Lemma lem3363133 {A : Type'} (x : A) (f : type686 A) : (term218 A f x) = (term187 A x f).
Proof. exact (eq_refl (term218 A f x)). Qed.
Lemma lem3363134 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) : (term225 A s f x) = (term226 A s x f).
Proof. exact (MK_COMB (@lem3363132 A f s x) (@lem3363133 A x f)). Qed.
Lemma lem3363135 {A : Type'} (s : A -> Prop) (f : type686 A) : (term227 A s f) = (term228 A s f).
Proof. exact (fun_ext (fun x : A => @lem3363134 A s x f)). Qed.
Lemma lem3363136 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3363137 {A : Type'} (s : A -> Prop) (f : type686 A) : (term213 A s f) = (term229 A s f).
Proof. exact (MK_COMB (@lem3363136 A) (@lem3363135 A s f)). Qed.
Lemma lem3363138 {A : Type'} (s : A -> Prop) (f : type686 A) : ((term212 A s f) = (term213 A s f)) = ((term206 A s f) = (term229 A s f)).
Proof. exact (MK_COMB (@lem3363129 A s f) (@lem3363137 A s f)). Qed.
Lemma lem3363139 {A : Type'} (s : A -> Prop) (f : type686 A) : (term206 A s f) = (term229 A s f).
Proof. exact (EQ_MP (@lem3363138 A s f) (@lem3363116 A s f)). Qed.
Lemma lem3363141 {A : Type'} (P : Prop) (Q : A -> Prop) : (term230 A P Q) = (term231 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3363142 {A : Type'} (P : Prop) (Q : type686 A) : (term232 A P Q) = (term233 A P Q).
Proof. exact (@lem3363141 (A -> Prop) P Q). Qed.
Lemma lem3363143 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) : (term234 A s x f) = (term235 A s x f).
Proof. exact (@lem3363142 A (term147 A f s x) (term186 A x f)). Qed.
Lemma lem3363144 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) : (term236 A x f t) = (term184 A t x f).
Proof. exact (eq_refl (term236 A x f t)). Qed.
Lemma lem3363145 {A : Type'} (x : A) (f : type686 A) : (term237 A x f) = (term186 A x f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3363144 A t x f)). Qed.
Lemma lem3363146 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3363147 {A : Type'} (x : A) (f : type686 A) : (term238 A x f) = (term187 A x f).
Proof. exact (MK_COMB (@lem3363146 A) (@lem3363145 A x f)). Qed.
Lemma lem3363148 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term224 A f s x) = (term224 A f s x).
Proof. exact (eq_refl (term224 A f s x)). Qed.
Lemma lem3363149 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) : (term234 A s x f) = (term226 A s x f).
Proof. exact (MK_COMB (@lem3363148 A f s x) (@lem3363147 A x f)). Qed.
Lemma lem3363150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3363151 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) : (term239 A s x f) = (term240 A s x f).
Proof. exact (MK_COMB (@lem3363150) (@lem3363149 A s x f)). Qed.
Lemma lem3363152 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) : (term236 A x f t) = (term184 A t x f).
Proof. exact (eq_refl (term236 A x f t)). Qed.
Lemma lem3363153 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term224 A f s x) = (term224 A f s x).
Proof. exact (eq_refl (term224 A f s x)). Qed.
Lemma lem3363154 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (f : type686 A) : (term241 A s x f t) = (term242 A s t x f).
Proof. exact (MK_COMB (@lem3363153 A f s x) (@lem3363152 A t x f)). Qed.
Lemma lem3363155 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) : (term243 A s x f) = (term244 A s x f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3363154 A s t x f)). Qed.
Lemma lem3363156 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3363157 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) : (term235 A s x f) = (term245 A s x f).
Proof. exact (MK_COMB (@lem3363156 A) (@lem3363155 A s x f)). Qed.
Lemma lem3363158 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) : ((term234 A s x f) = (term235 A s x f)) = ((term226 A s x f) = (term245 A s x f)).
Proof. exact (MK_COMB (@lem3363151 A s x f) (@lem3363157 A s x f)). Qed.
Lemma lem3363159 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) : (term226 A s x f) = (term245 A s x f).
Proof. exact (EQ_MP (@lem3363158 A s x f) (@lem3363143 A s x f)). Qed.
Lemma lem3363160 {A : Type'} (s : A -> Prop) (f : type686 A) : (term228 A s f) = (term246 A s f).
Proof. exact (fun_ext (fun x : A => @lem3363159 A s x f)). Qed.
Lemma lem3363161 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3363162 {A : Type'} (s : A -> Prop) (f : type686 A) : (term229 A s f) = (term247 A s f).
Proof. exact (MK_COMB (@lem3363161 A) (@lem3363160 A s f)). Qed.
Lemma lem3363163 {A : Type'} (s : A -> Prop) (f : type686 A) : (term206 A s f) = (term247 A s f).
Proof. exact (TRANS (@lem3363139 A s f) (@lem3363162 A s f)). Qed.
Lemma lem3363164 {A : Type'} (f : type686 A) : (term208 A f) = (term248 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3363163 A s f)). Qed.
Lemma lem3363165 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3363166 {A : Type'} (f : type686 A) : (term209 A f) = (term249 A f).
Proof. exact (MK_COMB (@lem3363165 A) (@lem3363164 A f)). Qed.
Lemma lem3363167 {A : Type'} (f : type686 A) : (term190 A f) = (term249 A f).
Proof. exact (TRANS (@lem3363112 A f) (@lem3363166 A f)). Qed.
Lemma lem3363169 {A : Type'} (f : type686 A) : (term108 A f) = (term249 A f).
Proof. exact (TRANS (@lem3363086 A f) (@lem3363167 A f)). Qed.
Lemma lem3363170 {A : Type'} (f : type686 A) : (term49 A f) = (term249 A f).
Proof. exact (TRANS (@lem3362792 A f) (@lem3363169 A f)). Qed.
Lemma lem3363171 {A : Type'} (f : type686 A) (h1 : term49 A f) : term249 A f.
Proof. exact (EQ_MP (@lem3363170 A f) (@lem3362701 A f h1)). Qed.
Lemma lem3363172 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term247 A s f) : term247 A s f.
Proof. exact (h1). Qed.
Lemma lem3363173 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (h1 : term245 A s x f) : term245 A s x f.
Proof. exact (h1). Qed.
Lemma lem3363174 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (f : type686 A) (h1 : term242 A s t x f) : term242 A s t x f.
Proof. exact (h1). Qed.
Lemma lem3363179 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3363180 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3363179 A Prop f x). Qed.
Lemma lem3363182 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3363180 A s x). Qed.
Lemma lem3363183 {A : Type'} (s : A -> Prop) : (term33 A s) = (term250 A s).
Proof. exact (fun_ext (fun x : A => @lem3363182 A s x)). Qed.
Lemma lem3363184 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3363185 {A : Type'} (s : A -> Prop) : (term34 A s) = (term251 A s).
Proof. exact (MK_COMB (@lem3363184 A) (@lem3363183 A s)). Qed.
Lemma lem3363186 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3363191 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3363192 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3363191 (A -> Prop) Prop f x). Qed.
Lemma lem3363194 {A : Type'} (f : type686 A) (s : A -> Prop) : (f s) = (@I ((A -> Prop) -> Prop) f s).
Proof. exact (@lem3363192 A f s). Qed.
Lemma lem3363195 {A : Type'} (f : type686 A) (s : A -> Prop) : (term252 A f s) = (term253 A f s).
Proof. exact (MK_COMB (@lem3363186) (@lem3363194 A f s)). Qed.
Lemma lem3363196 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3363197 {A : Type'} (f : type686 A) (s : A -> Prop) : (term86 A f s) = (term254 A f s).
Proof. exact (MK_COMB (@lem3363196) (@lem3363195 A f s)). Qed.
Lemma lem3363198 {A : Type'} (f : type686 A) (s : A -> Prop) : (term87 A f s) = (term255 A f s).
Proof. exact (MK_COMB (@lem3363197 A f s) (@lem3363185 A s)). Qed.
Lemma lem3363199 {A : Type'} (f : type686 A) : (term95 A f) = (term256 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3363198 A f s)). Qed.
Lemma lem3363200 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3363201 {A : Type'} (f : type686 A) : (term96 A f) = (term257 A f).
Proof. exact (MK_COMB (@lem3363200 A) (@lem3363199 A f)). Qed.
Lemma lem3363202 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3363207 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3363208 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3363207 A Prop f x). Qed.
Lemma lem3363210 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3363208 A t x). Qed.
Lemma lem3363211 {A : Type'} (t : A -> Prop) (x : A) : (term79 A t x) = (term258 A t x).
Proof. exact (MK_COMB (@lem3363202) (@lem3363210 A t x)). Qed.
Lemma lem3363216 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3363217 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3363216 (A -> Prop) Prop f x). Qed.
Lemma lem3363219 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3363217 A f t). Qed.
Lemma lem3363220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3363221 {A : Type'} (f : type686 A) (t : A -> Prop) : (term82 A f t) = (term259 A f t).
Proof. exact (MK_COMB (@lem3363220) (@lem3363219 A f t)). Qed.
Lemma lem3363222 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term51 A f t x) = (term260 A f t x).
Proof. exact (MK_COMB (@lem3363221 A f t) (@lem3363211 A t x)). Qed.
Lemma lem3363223 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3363224 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term182 A f t x) = (term261 A f t x).
Proof. exact (MK_COMB (@lem3363223) (@lem3363222 A f t x)). Qed.
Lemma lem3363225 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) : (term184 A t x f) = (term262 A t x f).
Proof. exact (MK_COMB (@lem3363224 A f t x) (@lem3363201 A f)). Qed.
Lemma lem3363226 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3363231 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3363232 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3363231 A Prop f x). Qed.
Lemma lem3363234 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3363232 A s x). Qed.
Lemma lem3363235 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (term258 A s x).
Proof. exact (MK_COMB (@lem3363226) (@lem3363234 A s x)). Qed.
Lemma lem3363240 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3363241 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3363240 (A -> Prop) Prop f x). Qed.
Lemma lem3363243 {A : Type'} (f : type686 A) (s : A -> Prop) : (f s) = (@I ((A -> Prop) -> Prop) f s).
Proof. exact (@lem3363241 A f s). Qed.
Lemma lem3363244 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3363245 {A : Type'} (f : type686 A) (s : A -> Prop) : (term82 A f s) = (term259 A f s).
Proof. exact (MK_COMB (@lem3363244) (@lem3363243 A f s)). Qed.
Lemma lem3363246 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term51 A f s x) = (term260 A f s x).
Proof. exact (MK_COMB (@lem3363245 A f s) (@lem3363235 A s x)). Qed.
Lemma lem3363251 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3363252 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem3363251 A Prop f x). Qed.
Lemma lem3363254 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3363252 A t x). Qed.
Lemma lem3363255 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3363260 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3363261 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem3363260 (A -> Prop) Prop f x). Qed.
Lemma lem3363263 {A : Type'} (f : type686 A) (t : A -> Prop) : (f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3363261 A f t). Qed.
Lemma lem3363264 {A : Type'} (f : type686 A) (t : A -> Prop) : (term252 A f t) = (term253 A f t).
Proof. exact (MK_COMB (@lem3363255) (@lem3363263 A f t)). Qed.
Lemma lem3363265 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3363266 {A : Type'} (f : type686 A) (t : A -> Prop) : (term86 A f t) = (term254 A f t).
Proof. exact (MK_COMB (@lem3363265) (@lem3363264 A f t)). Qed.
Lemma lem3363267 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term52 A f t x) = (term263 A f t x).
Proof. exact (MK_COMB (@lem3363266 A f t) (@lem3363254 A t x)). Qed.
Lemma lem3363268 {A : Type'} (f : type686 A) (x : A) : (term62 A f x) = (term264 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3363267 A f t x)). Qed.
Lemma lem3363269 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3363270 {A : Type'} (f : type686 A) (x : A) : (term63 A f x) = (term265 A f x).
Proof. exact (MK_COMB (@lem3363269 A) (@lem3363268 A f x)). Qed.
Lemma lem3363271 {A : Type'} (f : type686 A) : (term73 A f) = (term266 A f).
Proof. exact (fun_ext (fun x : A => @lem3363270 A f x)). Qed.
Lemma lem3363272 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3363273 {A : Type'} (f : type686 A) : (term74 A f) = (term267 A f).
Proof. exact (MK_COMB (@lem3363272 A) (@lem3363271 A f)). Qed.
Lemma lem3363274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3363275 {A : Type'} (f : type686 A) : (term102 A f) = (term268 A f).
Proof. exact (MK_COMB (@lem3363274) (@lem3363273 A f)). Qed.
Lemma lem3363276 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term147 A f s x) = (term269 A f s x).
Proof. exact (MK_COMB (@lem3363275 A f) (@lem3363246 A f s x)). Qed.
Lemma lem3363277 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3363278 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term224 A f s x) = (term270 A f s x).
Proof. exact (MK_COMB (@lem3363277) (@lem3363276 A f s x)). Qed.
Lemma lem3363279 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (f : type686 A) : (term242 A s t x f) = (term271 A s t x f).
Proof. exact (MK_COMB (@lem3363278 A f s x) (@lem3363225 A t x f)). Qed.
Lemma lem3363280 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (f : type686 A) (h1 : term242 A s t x f) : term271 A s t x f.
Proof. exact (EQ_MP (@lem3363279 A s t x f) (@lem3363174 A s t x f h1)). Qed.
Lemma lem3363281 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term269 A f s x.
Proof. exact (h1). Qed.
Lemma lem3363282 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term262 A t x f.
Proof. exact (h1). Qed.
Lemma lem3363283 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term260 A f s x.
Proof. exact (proj2 (@lem3363281 A f s x h1)). Qed.
Lemma lem3363284 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term267 A f.
Proof. exact (proj1 (@lem3363281 A f s x h1)). Qed.
Lemma lem3363287 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term257 A f.
Proof. exact (proj2 (@lem3363282 A t x f h1)). Qed.
Lemma lem3363288 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term260 A f t x.
Proof. exact (proj1 (@lem3363282 A t x f h1)). Qed.
Lemma lem3363298 {A : Type'} (f : type686 A) (t : A -> Prop) (x : A) : (term263 A f t x) = (term263 A f t x).
Proof. exact (eq_refl (term263 A f t x)). Qed.
Lemma lem3363299 {A : Type'} (f : type686 A) (x : A) : (term264 A f x) = (term264 A f x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3363298 A f t x)). Qed.
Lemma lem3363300 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3363301 {A : Type'} (f : type686 A) (x : A) : (term265 A f x) = (term265 A f x).
Proof. exact (MK_COMB (@lem3363300 A) (@lem3363299 A f x)). Qed.
Lemma lem3363302 {A : Type'} (f : type686 A) : (term266 A f) = (term266 A f).
Proof. exact (fun_ext (fun x : A => @lem3363301 A f x)). Qed.
Lemma lem3363303 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3363305 {A : Type'} (f : type686 A) : (term267 A f) = (term267 A f).
Proof. exact (MK_COMB (@lem3363303 A) (@lem3363302 A f)). Qed.
Lemma lem3363306 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term267 A f.
Proof. exact (EQ_MP (@lem3363305 A f) (@lem3363284 A f s x h1)). Qed.
Lemma lem3363316 {A : Type'} (P : Prop) (Q : A -> Prop) : (term272 A P Q) = (term273 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3363317 {A : Type'} (P : Prop) (Q : A -> Prop) : (term272 A P Q) = (term273 A P Q).
Proof. exact (@lem3363316 A P Q). Qed.
Lemma lem3363318 {A : Type'} (f : type686 A) (s : A -> Prop) : (term274 A f s) = (term275 A f s).
Proof. exact (@lem3363317 A (term253 A f s) (term250 A s)). Qed.
Lemma lem3363319 {A : Type'} (s : A -> Prop) (x : A) : (term276 A s x) = (@I (A -> Prop) s x).
Proof. exact (eq_refl (term276 A s x)). Qed.
Lemma lem3363320 {A : Type'} (s : A -> Prop) : (term277 A s) = (term250 A s).
Proof. exact (fun_ext (fun x : A => @lem3363319 A s x)). Qed.
Lemma lem3363321 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3363322 {A : Type'} (s : A -> Prop) : (term278 A s) = (term251 A s).
Proof. exact (MK_COMB (@lem3363321 A) (@lem3363320 A s)). Qed.
Lemma lem3363323 {A : Type'} (f : type686 A) (s : A -> Prop) : (term254 A f s) = (term254 A f s).
Proof. exact (eq_refl (term254 A f s)). Qed.
Lemma lem3363324 {A : Type'} (f : type686 A) (s : A -> Prop) : (term274 A f s) = (term255 A f s).
Proof. exact (MK_COMB (@lem3363323 A f s) (@lem3363322 A s)). Qed.
Lemma lem3363325 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3363326 {A : Type'} (f : type686 A) (s : A -> Prop) : (term279 A f s) = (term280 A f s).
Proof. exact (MK_COMB (@lem3363325) (@lem3363324 A f s)). Qed.
Lemma lem3363327 {A : Type'} (s : A -> Prop) (x : A) : (term276 A s x) = (@I (A -> Prop) s x).
Proof. exact (eq_refl (term276 A s x)). Qed.
Lemma lem3363328 {A : Type'} (f : type686 A) (s : A -> Prop) : (term254 A f s) = (term254 A f s).
Proof. exact (eq_refl (term254 A f s)). Qed.
Lemma lem3363329 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term281 A f s x) = (term263 A f s x).
Proof. exact (MK_COMB (@lem3363328 A f s) (@lem3363327 A s x)). Qed.
Lemma lem3363330 {A : Type'} (f : type686 A) (s : A -> Prop) : (term282 A f s) = (term283 A f s).
Proof. exact (fun_ext (fun x : A => @lem3363329 A f s x)). Qed.
Lemma lem3363331 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3363332 {A : Type'} (f : type686 A) (s : A -> Prop) : (term275 A f s) = (term284 A f s).
Proof. exact (MK_COMB (@lem3363331 A) (@lem3363330 A f s)). Qed.
Lemma lem3363333 {A : Type'} (f : type686 A) (s : A -> Prop) : ((term274 A f s) = (term275 A f s)) = ((term255 A f s) = (term284 A f s)).
Proof. exact (MK_COMB (@lem3363326 A f s) (@lem3363332 A f s)). Qed.
Lemma lem3363334 {A : Type'} (f : type686 A) (s : A -> Prop) : (term255 A f s) = (term284 A f s).
Proof. exact (EQ_MP (@lem3363333 A f s) (@lem3363318 A f s)). Qed.
Lemma lem3363335 {A : Type'} (f : type686 A) : (term256 A f) = (term285 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3363334 A f s)). Qed.
Lemma lem3363336 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3363337 {A : Type'} (f : type686 A) : (term257 A f) = (term286 A f).
Proof. exact (MK_COMB (@lem3363336 A) (@lem3363335 A f)). Qed.
Lemma lem3363344 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) : (term263 A f s x) = (term263 A f s x).
Proof. exact (eq_refl (term263 A f s x)). Qed.
Lemma lem3363345 {A : Type'} (f : type686 A) (s : A -> Prop) : (term283 A f s) = (term283 A f s).
Proof. exact (fun_ext (fun x : A => @lem3363344 A f s x)). Qed.
Lemma lem3363346 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3363347 {A : Type'} (f : type686 A) (s : A -> Prop) : (term284 A f s) = (term284 A f s).
Proof. exact (MK_COMB (@lem3363346 A) (@lem3363345 A f s)). Qed.
Lemma lem3363348 {A : Type'} (f : type686 A) : (term285 A f) = (term285 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3363347 A f s)). Qed.
Lemma lem3363349 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3363350 {A : Type'} (f : type686 A) : (term286 A f) = (term286 A f).
Proof. exact (MK_COMB (@lem3363349 A) (@lem3363348 A f)). Qed.
Lemma lem3363351 {A : Type'} (f : type686 A) : (term257 A f) = (term286 A f).
Proof. exact (TRANS (@lem3363337 A f) (@lem3363350 A f)). Qed.
Lemma lem3363352 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term286 A f.
Proof. exact (EQ_MP (@lem3363351 A f) (@lem3363287 A t x f h1)). Qed.
Lemma lem3363361 {A : Type'} (_35072 : A) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term287 A f _35072.
Proof. exact (@lem3363306 A f s x h1 _35072). Qed.
Lemma lem3363362 {A : Type'} (f : type686 A) (_35072 : A) : (term287 A f _35072) = (term265 A f _35072).
Proof. exact (eq_refl (term287 A f _35072)). Qed.
Lemma lem3363363 {A : Type'} (_35072 : A) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term265 A f _35072.
Proof. exact (EQ_MP (@lem3363362 A f _35072) (@lem3363361 A _35072 f s x h1)). Qed.
Lemma lem3363364 {A : Type'} (_35072 : A) (_35073 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term288 A f _35072 _35073.
Proof. exact (@lem3363363 A _35072 f s x h1 _35073). Qed.
Lemma lem3363365 {A : Type'} (f : type686 A) (_35073 : A -> Prop) (_35072 : A) : (term288 A f _35072 _35073) = (term263 A f _35073 _35072).
Proof. exact (eq_refl (term288 A f _35072 _35073)). Qed.
Lemma lem3363367 {A : Type'} (_35074 : A -> Prop) (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term289 A f _35074.
Proof. exact (@lem3363352 A t x f h1 _35074). Qed.
Lemma lem3363368 {A : Type'} (f : type686 A) (_35074 : A -> Prop) : (term289 A f _35074) = (term284 A f _35074).
Proof. exact (eq_refl (term289 A f _35074)). Qed.
Lemma lem3363369 {A : Type'} (_35074 : A -> Prop) (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term284 A f _35074.
Proof. exact (EQ_MP (@lem3363368 A f _35074) (@lem3363367 A _35074 t x f h1)). Qed.
Lemma lem3363370 {A : Type'} (_35074 : A -> Prop) (_35075 : A) (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term290 A f _35074 _35075.
Proof. exact (@lem3363369 A _35074 t x f h1 _35075). Qed.
Lemma lem3363371 {A : Type'} (f : type686 A) (_35074 : A -> Prop) (_35075 : A) : (term290 A f _35074 _35075) = (term263 A f _35074 _35075).
Proof. exact (eq_refl (term290 A f _35074 _35075)). Qed.
Lemma lem3363378 {A : Type'} (_35073 : A -> Prop) (_35072 : A) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term263 A f _35073 _35072.
Proof. exact (EQ_MP (@lem3363365 A f _35073 _35072) (@lem3363364 A _35072 _35073 f s x h1)). Qed.
Lemma lem3363382 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term258 A s x.
Proof. exact (proj2 (@lem3363283 A f s x h1)). Qed.
Lemma lem3363388 {A : Type'} (_35074 : A -> Prop) (_35075 : A) (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term263 A f _35074 _35075.
Proof. exact (EQ_MP (@lem3363371 A f _35074 _35075) (@lem3363370 A _35074 _35075 t x f h1)). Qed.
Lemma lem3363392 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term258 A t x.
Proof. exact (proj2 (@lem3363288 A t x f h1)). Qed.
Lemma lem3363394 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : @I ((A -> Prop) -> Prop) f s.
Proof. exact (proj1 (@lem3363283 A f s x h1)). Qed.
Lemma lem3363395 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term291 A f s.
Proof. exact (fun h0 : term253 A f s => @lem3363394 A f s x h1). Qed.
Lemma lem3363397 (p : Prop) : (term292 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3363398 {A : Type'} (f : type686 A) (s : A -> Prop) : (term291 A f s) = (@I ((A -> Prop) -> Prop) f s).
Proof. exact (@lem3363397 (@I ((A -> Prop) -> Prop) f s)). Qed.
Lemma lem3363399 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : @I ((A -> Prop) -> Prop) f s.
Proof. exact (EQ_MP (@lem3363398 A f s) (@lem3363395 A f s x h1)). Qed.
Lemma lem3363405 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3363406 {A : Type'} (_35072 : A) (f : type686 A) (_35073 : A -> Prop) : (term263 A f _35073 _35072) = (term293 A _35072 f _35073).
Proof. exact (@lem3363405 (@I (A -> Prop) _35073 _35072) (term253 A f _35073)). Qed.
Lemma lem3363412 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3363413 {A : Type'} (_35072 : A) (f : type686 A) (_35073 : A -> Prop) : (term294 A f _35073 _35072) = (term295 A _35072 f _35073).
Proof. exact (MK_COMB (@lem3363412) (@lem3363406 A _35072 f _35073)). Qed.
Lemma lem3363419 {A : Type'} (_35072 : A) (f : type686 A) (_35073 : A -> Prop) : (term293 A _35072 f _35073) = (term293 A _35072 f _35073).
Proof. exact (eq_refl (term293 A _35072 f _35073)). Qed.
Lemma lem3363420 {A : Type'} (_35072 : A) (f : type686 A) (_35073 : A -> Prop) : ((term263 A f _35073 _35072) = (term293 A _35072 f _35073)) = ((term293 A _35072 f _35073) = (term293 A _35072 f _35073)).
Proof. exact (MK_COMB (@lem3363413 A _35072 f _35073) (@lem3363419 A _35072 f _35073)). Qed.
Lemma lem3363422 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3363423 (x : Prop) : (x = x) = True.
Proof. exact (@lem3363422 Prop x). Qed.
Lemma lem3363424 {A : Type'} (_35072 : A) (f : type686 A) (_35073 : A -> Prop) : ((term293 A _35072 f _35073) = (term293 A _35072 f _35073)) = True.
Proof. exact (@lem3363423 (term293 A _35072 f _35073)). Qed.
Lemma lem3363425 {A : Type'} (_35072 : A) (f : type686 A) (_35073 : A -> Prop) : ((term263 A f _35073 _35072) = (term293 A _35072 f _35073)) = True.
Proof. exact (TRANS (@lem3363420 A _35072 f _35073) (@lem3363424 A _35072 f _35073)). Qed.
Lemma lem3363426 {A : Type'} (_35072 : A) (f : type686 A) (_35073 : A -> Prop) : True = ((term263 A f _35073 _35072) = (term293 A _35072 f _35073)).
Proof. exact (SYM (@lem3363425 A _35072 f _35073)). Qed.
Lemma lem3363427 {A : Type'} (_35072 : A) (f : type686 A) (_35073 : A -> Prop) : (term263 A f _35073 _35072) = (term293 A _35072 f _35073).
Proof. exact (EQ_MP (@lem3363426 A _35072 f _35073) (@lem0)). Qed.
Lemma lem3363428 {A : Type'} (_35072 : A) (_35073 : A -> Prop) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term293 A _35072 f _35073.
Proof. exact (EQ_MP (@lem3363427 A _35072 f _35073) (@lem3363378 A _35073 _35072 f s x h1)). Qed.
Lemma lem3363430 (b : Prop) (a : Prop) : (a \/ b) = (term296 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3363431 {A : Type'} (f : type686 A) (_35073 : A -> Prop) (_35072 : A) : (term293 A _35072 f _35073) = (term297 A f _35073 _35072).
Proof. exact (@lem3363430 (term253 A f _35073) (@I (A -> Prop) _35073 _35072)). Qed.
Lemma lem3363433 (a : Prop) : (term47 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3363434 {A : Type'} (f : type686 A) (_35073 : A -> Prop) : (term298 A f _35073) = (@I ((A -> Prop) -> Prop) f _35073).
Proof. exact (@lem3363433 (@I ((A -> Prop) -> Prop) f _35073)). Qed.
Lemma lem3363435 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3363436 {A : Type'} (f : type686 A) (_35073 : A -> Prop) : (term299 A f _35073) = (term300 A f _35073).
Proof. exact (MK_COMB (@lem3363435) (@lem3363434 A f _35073)). Qed.
Lemma lem3363437 {A : Type'} (_35073 : A -> Prop) (_35072 : A) : (@I (A -> Prop) _35073 _35072) = (@I (A -> Prop) _35073 _35072).
Proof. exact (eq_refl (@I (A -> Prop) _35073 _35072)). Qed.
Lemma lem3363438 {A : Type'} (f : type686 A) (_35073 : A -> Prop) (_35072 : A) : (term297 A f _35073 _35072) = (term301 A f _35073 _35072).
Proof. exact (MK_COMB (@lem3363436 A f _35073) (@lem3363437 A _35073 _35072)). Qed.
Lemma lem3363439 {A : Type'} (f : type686 A) (_35073 : A -> Prop) (_35072 : A) : (term293 A _35072 f _35073) = (term301 A f _35073 _35072).
Proof. exact (TRANS (@lem3363431 A f _35073 _35072) (@lem3363438 A f _35073 _35072)). Qed.
Lemma lem3363442 {A : Type'} (_35073 : A -> Prop) (_35072 : A) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term301 A f _35073 _35072.
Proof. exact (EQ_MP (@lem3363439 A f _35073 _35072) (@lem3363428 A _35072 _35073 f s x h1)). Qed.
Lemma lem3363443 {A : Type'} (_35073 : A -> Prop) (_35072 : A) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term301 A f _35073 _35072.
Proof. exact (@lem3363442 A _35073 _35072 f s x h1). Qed.
Lemma lem3363444 {A : Type'} (_35072 : A) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term301 A f s _35072.
Proof. exact (@lem3363443 A s _35072 f s x h1). Qed.
Lemma lem3363447 {A : Type'} (_35072 : A) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : @I (A -> Prop) s _35072.
Proof. exact (@lem3363444 A _35072 f s x h1 (@lem3363399 A f s x h1)). Qed.
Lemma lem3363448 {A : Type'} (_35072 : A) (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : @I (A -> Prop) s _35072.
Proof. exact (@lem3363447 A _35072 f s x h1). Qed.
Lemma lem3363449 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : @I (A -> Prop) s x.
Proof. exact (@lem3363448 A x f s x h1). Qed.
Lemma lem3363450 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term302 A s x.
Proof. exact (fun h0 : term258 A s x => @lem3363449 A f s x h1). Qed.
Lemma lem3363452 (p : Prop) : (term292 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3363453 {A : Type'} (s : A -> Prop) (x : A) : (term302 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem3363452 (@I (A -> Prop) s x)). Qed.
Lemma lem3363454 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem3363453 A s x) (@lem3363450 A f s x h1)). Qed.
Lemma lem3363457 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3363459 {A : Type'} (s : A -> Prop) (x : A) : (term258 A s x) = (term303 A s x).
Proof. exact (@lem3363457 (@I (A -> Prop) s x)). Qed.
Lemma lem3363462 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term303 A s x.
Proof. exact (EQ_MP (@lem3363459 A s x) (@lem3363382 A f s x h1)). Qed.
Lemma lem3363465 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : False.
Proof. exact (@lem3363462 A f s x h1 (@lem3363454 A f s x h1)). Qed.
Lemma lem3363466 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : term304.
Proof. exact (fun h0 : ~ False => @lem3363465 A f s x h1). Qed.
Lemma lem3363468 (p : Prop) : (term292 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3363469 : term304 = False.
Proof. exact (@lem3363468 False). Qed.
Lemma lem3363470 {A : Type'} (f : type686 A) (s : A -> Prop) (x : A) (h1 : term269 A f s x) : False.
Proof. exact (EQ_MP (@lem3363469) (@lem3363466 A f s x h1)). Qed.
Lemma lem3363472 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (proj1 (@lem3363288 A t x f h1)). Qed.
Lemma lem3363473 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term291 A f t.
Proof. exact (fun h0 : term253 A f t => @lem3363472 A t x f h1). Qed.
Lemma lem3363475 (p : Prop) : (term292 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3363476 {A : Type'} (f : type686 A) (t : A -> Prop) : (term291 A f t) = (@I ((A -> Prop) -> Prop) f t).
Proof. exact (@lem3363475 (@I ((A -> Prop) -> Prop) f t)). Qed.
Lemma lem3363477 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : @I ((A -> Prop) -> Prop) f t.
Proof. exact (EQ_MP (@lem3363476 A f t) (@lem3363473 A t x f h1)). Qed.
Lemma lem3363483 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3363484 {A : Type'} (_35075 : A) (f : type686 A) (_35074 : A -> Prop) : (term263 A f _35074 _35075) = (term293 A _35075 f _35074).
Proof. exact (@lem3363483 (@I (A -> Prop) _35074 _35075) (term253 A f _35074)). Qed.
Lemma lem3363490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3363491 {A : Type'} (_35075 : A) (f : type686 A) (_35074 : A -> Prop) : (term294 A f _35074 _35075) = (term295 A _35075 f _35074).
Proof. exact (MK_COMB (@lem3363490) (@lem3363484 A _35075 f _35074)). Qed.
Lemma lem3363497 {A : Type'} (_35075 : A) (f : type686 A) (_35074 : A -> Prop) : (term293 A _35075 f _35074) = (term293 A _35075 f _35074).
Proof. exact (eq_refl (term293 A _35075 f _35074)). Qed.
Lemma lem3363498 {A : Type'} (_35075 : A) (f : type686 A) (_35074 : A -> Prop) : ((term263 A f _35074 _35075) = (term293 A _35075 f _35074)) = ((term293 A _35075 f _35074) = (term293 A _35075 f _35074)).
Proof. exact (MK_COMB (@lem3363491 A _35075 f _35074) (@lem3363497 A _35075 f _35074)). Qed.
Lemma lem3363500 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3363501 (x : Prop) : (x = x) = True.
Proof. exact (@lem3363500 Prop x). Qed.
Lemma lem3363502 {A : Type'} (_35075 : A) (f : type686 A) (_35074 : A -> Prop) : ((term293 A _35075 f _35074) = (term293 A _35075 f _35074)) = True.
Proof. exact (@lem3363501 (term293 A _35075 f _35074)). Qed.
Lemma lem3363503 {A : Type'} (_35075 : A) (f : type686 A) (_35074 : A -> Prop) : ((term263 A f _35074 _35075) = (term293 A _35075 f _35074)) = True.
Proof. exact (TRANS (@lem3363498 A _35075 f _35074) (@lem3363502 A _35075 f _35074)). Qed.
Lemma lem3363504 {A : Type'} (_35075 : A) (f : type686 A) (_35074 : A -> Prop) : True = ((term263 A f _35074 _35075) = (term293 A _35075 f _35074)).
Proof. exact (SYM (@lem3363503 A _35075 f _35074)). Qed.
Lemma lem3363505 {A : Type'} (_35075 : A) (f : type686 A) (_35074 : A -> Prop) : (term263 A f _35074 _35075) = (term293 A _35075 f _35074).
Proof. exact (EQ_MP (@lem3363504 A _35075 f _35074) (@lem0)). Qed.
Lemma lem3363506 {A : Type'} (_35075 : A) (_35074 : A -> Prop) (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term293 A _35075 f _35074.
Proof. exact (EQ_MP (@lem3363505 A _35075 f _35074) (@lem3363388 A _35074 _35075 t x f h1)). Qed.
Lemma lem3363508 (b : Prop) (a : Prop) : (a \/ b) = (term296 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3363509 {A : Type'} (f : type686 A) (_35074 : A -> Prop) (_35075 : A) : (term293 A _35075 f _35074) = (term297 A f _35074 _35075).
Proof. exact (@lem3363508 (term253 A f _35074) (@I (A -> Prop) _35074 _35075)). Qed.
Lemma lem3363511 (a : Prop) : (term47 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3363512 {A : Type'} (f : type686 A) (_35074 : A -> Prop) : (term298 A f _35074) = (@I ((A -> Prop) -> Prop) f _35074).
Proof. exact (@lem3363511 (@I ((A -> Prop) -> Prop) f _35074)). Qed.
Lemma lem3363513 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3363514 {A : Type'} (f : type686 A) (_35074 : A -> Prop) : (term299 A f _35074) = (term300 A f _35074).
Proof. exact (MK_COMB (@lem3363513) (@lem3363512 A f _35074)). Qed.
Lemma lem3363515 {A : Type'} (_35074 : A -> Prop) (_35075 : A) : (@I (A -> Prop) _35074 _35075) = (@I (A -> Prop) _35074 _35075).
Proof. exact (eq_refl (@I (A -> Prop) _35074 _35075)). Qed.
Lemma lem3363516 {A : Type'} (f : type686 A) (_35074 : A -> Prop) (_35075 : A) : (term297 A f _35074 _35075) = (term301 A f _35074 _35075).
Proof. exact (MK_COMB (@lem3363514 A f _35074) (@lem3363515 A _35074 _35075)). Qed.
Lemma lem3363517 {A : Type'} (f : type686 A) (_35074 : A -> Prop) (_35075 : A) : (term293 A _35075 f _35074) = (term301 A f _35074 _35075).
Proof. exact (TRANS (@lem3363509 A f _35074 _35075) (@lem3363516 A f _35074 _35075)). Qed.
Lemma lem3363520 {A : Type'} (_35074 : A -> Prop) (_35075 : A) (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term301 A f _35074 _35075.
Proof. exact (EQ_MP (@lem3363517 A f _35074 _35075) (@lem3363506 A _35075 _35074 t x f h1)). Qed.
Lemma lem3363521 {A : Type'} (_35074 : A -> Prop) (_35075 : A) (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term301 A f _35074 _35075.
Proof. exact (@lem3363520 A _35074 _35075 t x f h1). Qed.
Lemma lem3363522 {A : Type'} (_35075 : A) (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term301 A f t _35075.
Proof. exact (@lem3363521 A t _35075 t x f h1). Qed.
Lemma lem3363525 {A : Type'} (_35075 : A) (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : @I (A -> Prop) t _35075.
Proof. exact (@lem3363522 A _35075 t x f h1 (@lem3363477 A t x f h1)). Qed.
Lemma lem3363526 {A : Type'} (_35075 : A) (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : @I (A -> Prop) t _35075.
Proof. exact (@lem3363525 A _35075 t x f h1). Qed.
Lemma lem3363527 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : @I (A -> Prop) t x.
Proof. exact (@lem3363526 A x t x f h1). Qed.
Lemma lem3363528 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term302 A t x.
Proof. exact (fun h0 : term258 A t x => @lem3363527 A t x f h1). Qed.
Lemma lem3363530 (p : Prop) : (term292 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3363531 {A : Type'} (t : A -> Prop) (x : A) : (term302 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem3363530 (@I (A -> Prop) t x)). Qed.
Lemma lem3363532 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem3363531 A t x) (@lem3363528 A t x f h1)). Qed.
Lemma lem3363535 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3363537 {A : Type'} (t : A -> Prop) (x : A) : (term258 A t x) = (term303 A t x).
Proof. exact (@lem3363535 (@I (A -> Prop) t x)). Qed.
Lemma lem3363540 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term303 A t x.
Proof. exact (EQ_MP (@lem3363537 A t x) (@lem3363392 A t x f h1)). Qed.
Lemma lem3363543 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : False.
Proof. exact (@lem3363540 A t x f h1 (@lem3363532 A t x f h1)). Qed.
Lemma lem3363544 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : term304.
Proof. exact (fun h0 : ~ False => @lem3363543 A t x f h1). Qed.
Lemma lem3363546 (p : Prop) : (term292 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3363547 : term304 = False.
Proof. exact (@lem3363546 False). Qed.
Lemma lem3363548 {A : Type'} (t : A -> Prop) (x : A) (f : type686 A) (h1 : term262 A t x f) : False.
Proof. exact (EQ_MP (@lem3363547) (@lem3363544 A t x f h1)). Qed.
Lemma lem3363549 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (f : type686 A) (h1 : term242 A s t x f) : False.
Proof. exact (or_elim (@lem3363280 A s t x f h1) (fun h0 : term269 A f s x => @lem3363470 A f s x h0) (fun h0 : term262 A t x f => @lem3363548 A t x f h0)). Qed.
Lemma lem3363550 {A : Type'} (s : A -> Prop) (x : A) (f : type686 A) (h1 : term245 A s x f) : False.
Proof. exact (ex_elim (@lem3363173 A s x f h1) (fun t : A -> Prop => fun h0 : term244 A s x f t => @lem3363549 A s t x f h0)). Qed.
Lemma lem3363551 {A : Type'} (s : A -> Prop) (f : type686 A) (h1 : term247 A s f) : False.
Proof. exact (ex_elim (@lem3363172 A s f h1) (fun x : A => fun h0 : term246 A s f x => @lem3363550 A s x f h0)). Qed.
Lemma lem3363552 {A : Type'} (f : type686 A) (h1 : term49 A f) : False.
Proof. exact (ex_elim (@lem3363171 A f h1) (fun s : A -> Prop => fun h0 : term248 A f s => @lem3363551 A s f h0)). Qed.
Lemma lem3363553 {A : Type'} (f : type686 A) (h1 : term49 A f) : (term49 A f) = False.
Proof. exact (prop_ext (fun h2 : term49 A f => @lem3363552 A f h1) (fun h2 : False => @lem3362701 A f h1)). Qed.
Lemma lem3363554 {A : Type'} (f : type686 A) (h1 : term49 A f) : False.
Proof. exact (EQ_MP (@lem3363553 A f h1) (@lem3362701 A f h1)). Qed.
Lemma lem3363555 {A : Type'} (f : type686 A) : term48 A f.
Proof. exact (fun h0 : term49 A f => @lem3363554 A f h0). Qed.
Lemma lem3363556 {A : Type'} (f : type686 A) : (term28 A f) = (term37 A f).
Proof. exact (EQ_MP (@lem3362700 A f) (@lem3363555 A f)). Qed.
Lemma lem3363561 {A : Type'} : term39 A.
Proof. exact (fun f : type686 A => @lem3363556 A f). Qed.
Lemma lem3363562 {A : Type'} : term41 A.
Proof. exact (EQ_MP (@lem3362696 A) (@lem3363561 A)). Qed.
Lemma lem3363564 {A : Type'} : term41 A.
Proof. exact (@lem3362595 A (@lem3363562 A)). Qed.
Lemma lem3363565 {A : Type'} (h1 : term42 A) : False.
Proof. exact (@lem3363564 A (@lem3362579 A h1)). Qed.
Lemma lem3363566 {A : Type'} (h1 : term42 A) : (term42 A) = False.
Proof. exact (prop_ext (fun h2 : term42 A => @lem3363565 A h1) (fun h2 : False => @lem3362579 A h1)). Qed.
Lemma lem3363567 {A : Type'} (h1 : term42 A) : False.
Proof. exact (EQ_MP (@lem3363566 A h1) (@lem3362579 A h1)). Qed.
Lemma lem3363568 {A : Type'} : term41 A.
Proof. exact (fun h0 : term42 A => @lem3363567 A h0). Qed.
Lemma lem3363569 {A : Type'} : term39 A.
Proof. exact (EQ_MP (@lem3362578 A) (@lem3363568 A)). Qed.
Lemma lem3363570 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem3362574 A) (@lem3363569 A)). Qed.
Lemma lem3363571 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3362446 A) (@lem3363570 A)). Qed.
