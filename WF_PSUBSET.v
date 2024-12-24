Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_PSUBSET_term_abbrevs.
Require Import CONJ_ASSOC_spec.
Require Import DISJ_ACI_spec.
Require Import FINITE_POWERSET_spec.
Require Import FINITE_SUBSET_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import WF_FINITE_spec.
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
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
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
Require Import thm18970_spec.
Require Import thm18971_spec.
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
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211744_spec.
Require Import thm3211745_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem5113419 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem5113420 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term1 A s.
Proof. exact (@lem5113419 A h1 s). Qed.
Lemma lem5113421 {A : Type'} (s : A -> Prop) : (term1 A s) = (term2 A s).
Proof. exact (eq_refl (term1 A s)). Qed.
Lemma lem5113422 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term2 A s.
Proof. exact (EQ_MP (@lem5113421 A s) (@lem5113420 A s h1)). Qed.
Lemma lem5113423 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) : term3 A s t.
Proof. exact (@lem5113422 A s h1 t). Qed.
Lemma lem5113424 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term3 A s t) = (term4 A t s).
Proof. exact (eq_refl (term3 A s t)). Qed.
Lemma lem5113425 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term0 A) : term4 A t s.
Proof. exact (EQ_MP (@lem5113424 A t s) (@lem5113423 A s t h1)). Qed.
Lemma lem5113426 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term5 A s t.
Proof. exact (h1). Qed.
Lemma lem5113427 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term0 A) (h2 : term5 A s t) : @FINITE A s.
Proof. exact (@lem5113425 A t s h1 (@lem5113426 A s t h2)). Qed.
Lemma lem5113428 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term5 A s t) : term6 A s.
Proof. exact (fun h0 : term0 A => @lem5113427 A s t h0 h1). Qed.
Lemma lem5113429 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term7 A s.
Proof. exact (h1). Qed.
Lemma lem5113430 {A : Type'} (s : A -> Prop) (h1 : term7 A s) : term6 A s.
Proof. exact (ex_elim (@lem5113429 A s h1) (fun t : A -> Prop => fun h0 : term8 A s t => @lem5113428 A s t h0)). Qed.
Lemma lem5113431 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem5113432 {A : Type'} (s : A -> Prop) (h1 : term0 A) (h2 : term7 A s) : @FINITE A s.
Proof. exact (@lem5113430 A s h2 (@lem5113431 A h1)). Qed.
Lemma lem5113433 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term9 A s.
Proof. exact (fun h0 : term7 A s => @lem5113432 A s h1 h0). Qed.
Lemma lem5113434 {A : Type'} (h1 : term0 A) : term10 A.
Proof. exact (fun s : A -> Prop => @lem5113433 A s h1). Qed.
Lemma lem5113435 {A : Type'} : term11 A.
Proof. exact (fun h0 : term0 A => @lem5113434 A h0). Qed.
Lemma lem5113436 {A : Type'} : term10 A.
Proof. exact (@lem5113435 A (@lem3599924 A)). Qed.
Lemma lem5113437 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem5113436 A s). Qed.
Lemma lem5113438 {A : Type'} (s : A -> Prop) : (term12 A s) = (term9 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem5113450 (t1 : Prop) : term13 t1.
Proof. exact (@lem512 t1). Qed.
Lemma lem5113451 (t1 : Prop) : (term13 t1) = (term14 t1).
Proof. exact (eq_refl (term13 t1)). Qed.
Lemma lem5113452 (t1 : Prop) : term14 t1.
Proof. exact (EQ_MP (@lem5113451 t1) (@lem5113450 t1)). Qed.
Lemma lem5113453 (t1 : Prop) (t2 : Prop) : term15 t1 t2.
Proof. exact (@lem5113452 t1 t2). Qed.
Lemma lem5113454 (t1 : Prop) (t2 : Prop) : (term15 t1 t2) = (term16 t1 t2).
Proof. exact (eq_refl (term15 t1 t2)). Qed.
Lemma lem5113455 (t1 : Prop) (t2 : Prop) : term16 t1 t2.
Proof. exact (EQ_MP (@lem5113454 t1 t2) (@lem5113453 t1 t2)). Qed.
Lemma lem5113456 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term17 t1 t2 t3.
Proof. exact (@lem5113455 t1 t2 t3). Qed.
Lemma lem5113457 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term17 t1 t2 t3) = ((term18 t1 t2 t3) = (term19 t1 t2 t3)).
Proof. exact (eq_refl (term17 t1 t2 t3)). Qed.
Lemma lem5113459 {A : Type'} (h1 : term20 A) : term20 A.
Proof. exact (h1). Qed.
Lemma lem5113460 {A : Type'} (lt2 : type1402 A) (h1 : term20 A) : term21 A lt2.
Proof. exact (@lem5113459 A h1 lt2). Qed.
Lemma lem5113461 {A : Type'} (lt2 : type1402 A) : (term21 A lt2) = (term22 A lt2).
Proof. exact (eq_refl (term21 A lt2)). Qed.
Lemma lem5113462 {A : Type'} (lt2 : type1402 A) (h1 : term20 A) : term22 A lt2.
Proof. exact (EQ_MP (@lem5113461 A lt2) (@lem5113460 A lt2 h1)). Qed.
Lemma lem5113463 {A : Type'} (lt2 : type1402 A) (h1 : term23 A lt2) : term23 A lt2.
Proof. exact (h1). Qed.
Lemma lem5113464 {A : Type'} (lt2 : type1402 A) (h1 : term20 A) (h2 : term23 A lt2) : @WF A lt2.
Proof. exact (@lem5113462 A lt2 h1 (@lem5113463 A lt2 h2)). Qed.
Lemma lem5113465 {A : Type'} (lt2 : type1402 A) (h1 : term23 A lt2) : term24 A lt2.
Proof. exact (fun h0 : term20 A => @lem5113464 A lt2 h0 h1). Qed.
Lemma lem5113466 {A : Type'} (h1 : term20 A) : term20 A.
Proof. exact (h1). Qed.
Lemma lem5113467 {A : Type'} (lt2 : type1402 A) (h1 : term20 A) (h2 : term23 A lt2) : @WF A lt2.
Proof. exact (@lem5113465 A lt2 h2 (@lem5113466 A h1)). Qed.
Lemma lem5113468 {A : Type'} (lt2 : type1402 A) (h1 : term20 A) : term22 A lt2.
Proof. exact (fun h0 : term23 A lt2 => @lem5113467 A lt2 h1 h0). Qed.
Lemma lem5113469 {A : Type'} (h1 : term20 A) : term20 A.
Proof. exact (fun lt2 : type1402 A => @lem5113468 A lt2 h1). Qed.
Lemma lem5113470 {A : Type'} : term25 A.
Proof. exact (fun h0 : term20 A => @lem5113469 A h0). Qed.
Lemma lem5113471 {A : Type'} : term20 A.
Proof. exact (@lem5113470 A (@lem5113408 A)). Qed.
Lemma lem5113472 {A : Type'} (lt2 : type1402 A) : term21 A lt2.
Proof. exact (@lem5113471 A lt2). Qed.
Lemma lem5113473 {A : Type'} (lt2 : type1402 A) : (term21 A lt2) = (term22 A lt2).
Proof. exact (eq_refl (term21 A lt2)). Qed.
Lemma lem5113475 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5113477 {A : Type'} (lt2 : type1402 A) : term22 A lt2.
Proof. exact (EQ_MP (@lem5113473 A lt2) (@lem5113472 A lt2)). Qed.
Lemma lem5113478 {A : Type'} (lt2 : type639 A) : term26 A lt2.
Proof. exact (@lem5113477 (A -> Prop) lt2). Qed.
Lemma lem5113479 {A : Type'} (s : A -> Prop) : term27 A s.
Proof. exact (@lem5113478 A (term28 A s)). Qed.
Lemma lem5113481 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term18 t1 t2 t3) = (term19 t1 t2 t3).
Proof. exact (EQ_MP (@lem5113457 t1 t2 t3) (@lem5113456 t1 t2 t3)). Qed.
Lemma lem5113482 {A : Type'} (s : A -> Prop) : (term29 A s) = (term30 A s).
Proof. exact (@lem5113481 (term31 A s) (term32 A s) (term33 A s)). Qed.
Lemma lem5113492 {A B : Type'} (f : A -> B) (y : A) : (term34 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5113493 {A : Type'} (f : type639 A) (y : A -> Prop) : (term35 A f y) = (f y).
Proof. exact (@lem5113492 (A -> Prop) (type686 A) f y). Qed.
Lemma lem5113494 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term36 A s x) = (term37 A s x).
Proof. exact (@lem5113493 A (term28 A s) x). Qed.
Lemma lem5113495 {A : Type'} (t1 : A -> Prop) (s : A -> Prop) : (term37 A s t1) = (term38 A t1 s).
Proof. exact (eq_refl (term37 A s t1)). Qed.
Lemma lem5113496 {A : Type'} (s : A -> Prop) : (term39 A s) = (term28 A s).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem5113495 A t1 s)). Qed.
Lemma lem5113497 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5113498 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term36 A s x) = (term37 A s x).
Proof. exact (MK_COMB (@lem5113496 A s) (@lem5113497 A x)). Qed.
Lemma lem5113499 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem5113500 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term40 A s x) = (term41 A s x).
Proof. exact (MK_COMB (@lem5113499 A) (@lem5113498 A s x)). Qed.
Lemma lem5113501 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term37 A s x) = (term38 A x s).
Proof. exact (eq_refl (term37 A s x)). Qed.
Lemma lem5113502 {A : Type'} (x : A -> Prop) (s : A -> Prop) : ((term36 A s x) = (term37 A s x)) = ((term37 A s x) = (term38 A x s)).
Proof. exact (MK_COMB (@lem5113500 A s x) (@lem5113501 A x s)). Qed.
Lemma lem5113503 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term37 A s x) = (term38 A x s).
Proof. exact (EQ_MP (@lem5113502 A x s) (@lem5113494 A s x)). Qed.
Lemma lem5113506 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5113507 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term42 A s x) = (term43 A s x).
Proof. exact (MK_COMB (@lem5113503 A x s) (@lem5113506 A x)). Qed.
Lemma lem5113509 {A B : Type'} (f : A -> B) (y : A) : (term34 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5113510 {A : Type'} (f : type686 A) (y : A -> Prop) : (term44 A f y) = (f y).
Proof. exact (@lem5113509 (A -> Prop) Prop f y). Qed.
Lemma lem5113511 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term45 A s x) = (term43 A s x).
Proof. exact (@lem5113510 A (term38 A x s) x). Qed.
Lemma lem5113512 {A : Type'} (x : A -> Prop) (t2 : A -> Prop) (s : A -> Prop) : (term46 A x s t2) = (term47 A x t2 s).
Proof. exact (eq_refl (term46 A x s t2)). Qed.
Lemma lem5113513 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term48 A x s) = (term38 A x s).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem5113512 A x t2 s)). Qed.
Lemma lem5113514 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5113515 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term45 A s x) = (term43 A s x).
Proof. exact (MK_COMB (@lem5113513 A x s) (@lem5113514 A x)). Qed.
Lemma lem5113516 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5113517 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term49 A s x) = (term50 A s x).
Proof. exact (MK_COMB (@lem5113516) (@lem5113515 A s x)). Qed.
Lemma lem5113518 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term43 A s x) = (term51 A x s).
Proof. exact (eq_refl (term43 A s x)). Qed.
Lemma lem5113519 {A : Type'} (x : A -> Prop) (s : A -> Prop) : ((term45 A s x) = (term43 A s x)) = ((term43 A s x) = (term51 A x s)).
Proof. exact (MK_COMB (@lem5113517 A s x) (@lem5113518 A x s)). Qed.
Lemma lem5113520 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term43 A s x) = (term51 A x s).
Proof. exact (EQ_MP (@lem5113519 A x s) (@lem5113511 A s x)). Qed.
Lemma lem5113523 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term42 A s x) = (term51 A x s).
Proof. exact (TRANS (@lem5113507 A s x) (@lem5113520 A x s)). Qed.
Lemma lem5113524 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5113525 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term52 A s x) = (term53 A x s).
Proof. exact (MK_COMB (@lem5113524) (@lem5113523 A x s)). Qed.
Lemma lem5113528 {A : Type'} (s : A -> Prop) : (term54 A s) = (term55 A s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem5113525 A x s)). Qed.
Lemma lem5113531 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5113532 {A : Type'} (s : A -> Prop) : (term31 A s) = (term56 A s).
Proof. exact (MK_COMB (@lem5113531 A) (@lem5113528 A s)). Qed.
Lemma lem5113539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5113540 {A : Type'} (s : A -> Prop) : (term57 A s) = (term58 A s).
Proof. exact (MK_COMB (@lem5113539) (@lem5113532 A s)). Qed.
Lemma lem5113562 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term59 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5113563 (p : Prop) (q : Prop) (p' : Prop) : term60 p q p'.
Proof. exact (fun q' : Prop => @lem5113562 p q p' q'). Qed.
Lemma lem5113564 (p : Prop) (q : Prop) : term61 p q.
Proof. exact (fun p' : Prop => @lem5113563 p q p'). Qed.
Lemma lem5113565 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) : term62 A y s x z.
Proof. exact (@lem5113564 (term63 A x s y z) (term64 A s x z)). Qed.
Lemma lem5113566 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) (p' : Prop) : term65 A y s x z p'.
Proof. exact (@lem5113565 A y s x z p'). Qed.
Lemma lem5113567 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) (p' : Prop) : (term65 A y s x z p') = (term66 A y s x z p').
Proof. exact (eq_refl (term65 A y s x z p')). Qed.
Lemma lem5113568 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) (p' : Prop) : term66 A y s x z p'.
Proof. exact (EQ_MP (@lem5113567 A y s x z p') (@lem5113566 A y s x z p')). Qed.
Lemma lem5113569 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) (p' : Prop) (q' : Prop) : term67 A y s x z p' q'.
Proof. exact (@lem5113568 A y s x z p' q'). Qed.
Lemma lem5113570 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) (p' : Prop) (q' : Prop) : (term67 A y s x z p' q') = (term68 A y s x z p' q').
Proof. exact (eq_refl (term67 A y s x z p' q')). Qed.
Lemma lem5113571 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) (p' : Prop) (q' : Prop) : term68 A y s x z p' q'.
Proof. exact (EQ_MP (@lem5113570 A y s x z p' q') (@lem5113569 A y s x z p' q')). Qed.
Lemma lem5113575 {A B : Type'} (f : A -> B) (y : A) : (term34 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5113576 {A : Type'} (f : type639 A) (y : A -> Prop) : (term35 A f y) = (f y).
Proof. exact (@lem5113575 (A -> Prop) (type686 A) f y). Qed.
Lemma lem5113577 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term36 A s x) = (term37 A s x).
Proof. exact (@lem5113576 A (term28 A s) x). Qed.
Lemma lem5113578 {A : Type'} (t1 : A -> Prop) (s : A -> Prop) : (term37 A s t1) = (term38 A t1 s).
Proof. exact (eq_refl (term37 A s t1)). Qed.
Lemma lem5113579 {A : Type'} (s : A -> Prop) : (term39 A s) = (term28 A s).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem5113578 A t1 s)). Qed.
Lemma lem5113580 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5113581 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term36 A s x) = (term37 A s x).
Proof. exact (MK_COMB (@lem5113579 A s) (@lem5113580 A x)). Qed.
Lemma lem5113582 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem5113583 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term40 A s x) = (term41 A s x).
Proof. exact (MK_COMB (@lem5113582 A) (@lem5113581 A s x)). Qed.
Lemma lem5113584 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term37 A s x) = (term38 A x s).
Proof. exact (eq_refl (term37 A s x)). Qed.
Lemma lem5113585 {A : Type'} (x : A -> Prop) (s : A -> Prop) : ((term36 A s x) = (term37 A s x)) = ((term37 A s x) = (term38 A x s)).
Proof. exact (MK_COMB (@lem5113583 A s x) (@lem5113584 A x s)). Qed.
Lemma lem5113586 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term37 A s x) = (term38 A x s).
Proof. exact (EQ_MP (@lem5113585 A x s) (@lem5113577 A s x)). Qed.
Lemma lem5113589 {A : Type'} (y : A -> Prop) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5113590 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) : (term64 A s x y) = (term46 A x s y).
Proof. exact (MK_COMB (@lem5113586 A x s) (@lem5113589 A y)). Qed.
Lemma lem5113592 {A B : Type'} (f : A -> B) (y : A) : (term34 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5113593 {A : Type'} (f : type686 A) (y : A -> Prop) : (term44 A f y) = (f y).
Proof. exact (@lem5113592 (A -> Prop) Prop f y). Qed.
Lemma lem5113594 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) : (term69 A x s y) = (term46 A x s y).
Proof. exact (@lem5113593 A (term38 A x s) y). Qed.
Lemma lem5113595 {A : Type'} (x : A -> Prop) (t2 : A -> Prop) (s : A -> Prop) : (term46 A x s t2) = (term47 A x t2 s).
Proof. exact (eq_refl (term46 A x s t2)). Qed.
Lemma lem5113596 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term48 A x s) = (term38 A x s).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem5113595 A x t2 s)). Qed.
Lemma lem5113597 {A : Type'} (y : A -> Prop) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5113598 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) : (term69 A x s y) = (term46 A x s y).
Proof. exact (MK_COMB (@lem5113596 A x s) (@lem5113597 A y)). Qed.
Lemma lem5113599 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5113600 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) : (term70 A x s y) = (term71 A x s y).
Proof. exact (MK_COMB (@lem5113599) (@lem5113598 A x s y)). Qed.
Lemma lem5113601 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term46 A x s y) = (term47 A x y s).
Proof. exact (eq_refl (term46 A x s y)). Qed.
Lemma lem5113602 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : ((term69 A x s y) = (term46 A x s y)) = ((term46 A x s y) = (term47 A x y s)).
Proof. exact (MK_COMB (@lem5113600 A x s y) (@lem5113601 A x y s)). Qed.
Lemma lem5113603 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term46 A x s y) = (term47 A x y s).
Proof. exact (EQ_MP (@lem5113602 A x y s) (@lem5113594 A x s y)). Qed.
Lemma lem5113606 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term64 A s x y) = (term47 A x y s).
Proof. exact (TRANS (@lem5113590 A x s y) (@lem5113603 A x y s)). Qed.
Lemma lem5113607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5113608 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term72 A s x y) = (term73 A x y s).
Proof. exact (MK_COMB (@lem5113607) (@lem5113606 A x y s)). Qed.
Lemma lem5113612 {A B : Type'} (f : A -> B) (y : A) : (term34 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5113613 {A : Type'} (f : type639 A) (y : A -> Prop) : (term35 A f y) = (f y).
Proof. exact (@lem5113612 (A -> Prop) (type686 A) f y). Qed.
Lemma lem5113614 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term36 A s y) = (term37 A s y).
Proof. exact (@lem5113613 A (term28 A s) y). Qed.
Lemma lem5113615 {A : Type'} (t1 : A -> Prop) (s : A -> Prop) : (term37 A s t1) = (term38 A t1 s).
Proof. exact (eq_refl (term37 A s t1)). Qed.
Lemma lem5113616 {A : Type'} (s : A -> Prop) : (term39 A s) = (term28 A s).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem5113615 A t1 s)). Qed.
Lemma lem5113617 {A : Type'} (y : A -> Prop) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5113618 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term36 A s y) = (term37 A s y).
Proof. exact (MK_COMB (@lem5113616 A s) (@lem5113617 A y)). Qed.
Lemma lem5113619 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem5113620 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term40 A s y) = (term41 A s y).
Proof. exact (MK_COMB (@lem5113619 A) (@lem5113618 A s y)). Qed.
Lemma lem5113621 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term37 A s y) = (term38 A y s).
Proof. exact (eq_refl (term37 A s y)). Qed.
Lemma lem5113622 {A : Type'} (y : A -> Prop) (s : A -> Prop) : ((term36 A s y) = (term37 A s y)) = ((term37 A s y) = (term38 A y s)).
Proof. exact (MK_COMB (@lem5113620 A s y) (@lem5113621 A y s)). Qed.
Lemma lem5113623 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term37 A s y) = (term38 A y s).
Proof. exact (EQ_MP (@lem5113622 A y s) (@lem5113614 A s y)). Qed.
Lemma lem5113626 {A : Type'} (z : A -> Prop) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5113627 {A : Type'} (y : A -> Prop) (s : A -> Prop) (z : A -> Prop) : (term64 A s y z) = (term46 A y s z).
Proof. exact (MK_COMB (@lem5113623 A y s) (@lem5113626 A z)). Qed.
Lemma lem5113629 {A B : Type'} (f : A -> B) (y : A) : (term34 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5113630 {A : Type'} (f : type686 A) (y : A -> Prop) : (term44 A f y) = (f y).
Proof. exact (@lem5113629 (A -> Prop) Prop f y). Qed.
Lemma lem5113631 {A : Type'} (y : A -> Prop) (s : A -> Prop) (z : A -> Prop) : (term69 A y s z) = (term46 A y s z).
Proof. exact (@lem5113630 A (term38 A y s) z). Qed.
Lemma lem5113632 {A : Type'} (y : A -> Prop) (t2 : A -> Prop) (s : A -> Prop) : (term46 A y s t2) = (term47 A y t2 s).
Proof. exact (eq_refl (term46 A y s t2)). Qed.
Lemma lem5113633 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term48 A y s) = (term38 A y s).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem5113632 A y t2 s)). Qed.
Lemma lem5113634 {A : Type'} (z : A -> Prop) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5113635 {A : Type'} (y : A -> Prop) (s : A -> Prop) (z : A -> Prop) : (term69 A y s z) = (term46 A y s z).
Proof. exact (MK_COMB (@lem5113633 A y s) (@lem5113634 A z)). Qed.
Lemma lem5113636 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5113637 {A : Type'} (y : A -> Prop) (s : A -> Prop) (z : A -> Prop) : (term70 A y s z) = (term71 A y s z).
Proof. exact (MK_COMB (@lem5113636) (@lem5113635 A y s z)). Qed.
Lemma lem5113638 {A : Type'} (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term46 A y s z) = (term47 A y z s).
Proof. exact (eq_refl (term46 A y s z)). Qed.
Lemma lem5113639 {A : Type'} (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : ((term69 A y s z) = (term46 A y s z)) = ((term46 A y s z) = (term47 A y z s)).
Proof. exact (MK_COMB (@lem5113637 A y s z) (@lem5113638 A y z s)). Qed.
Lemma lem5113640 {A : Type'} (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term46 A y s z) = (term47 A y z s).
Proof. exact (EQ_MP (@lem5113639 A y z s) (@lem5113631 A y s z)). Qed.
Lemma lem5113643 {A : Type'} (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term64 A s y z) = (term47 A y z s).
Proof. exact (TRANS (@lem5113627 A y s z) (@lem5113640 A y z s)). Qed.
Lemma lem5113644 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term63 A x s y z) = (term74 A x y z s).
Proof. exact (MK_COMB (@lem5113608 A x y s) (@lem5113643 A y z s)). Qed.
Lemma lem5113646 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term18 t1 t2 t3) = (term19 t1 t2 t3).
Proof. exact (EQ_MP (@lem5113457 t1 t2 t3) (@lem5113456 t1 t2 t3)). Qed.
Lemma lem5113647 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term74 A x y z s) = (term75 A x y z s).
Proof. exact (@lem5113646 (term47 A x y s) (@PSUBSET A y z) (@SUBSET A z s)). Qed.
Lemma lem5113654 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term63 A x s y z) = (term75 A x y z s).
Proof. exact (TRANS (@lem5113644 A x y z s) (@lem5113647 A x y z s)). Qed.
Lemma lem5113655 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (q' : Prop) : term76 A x y z s q'.
Proof. exact (@lem5113571 A y s x z (term75 A x y z s) q'). Qed.
Lemma lem5113656 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (q' : Prop) : term77 A x y z s q'.
Proof. exact (@lem5113655 A x y z s q' (@lem5113654 A x y z s)). Qed.
Lemma lem5113657 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (h1 : term75 A x y z s) : term75 A x y z s.
Proof. exact (h1). Qed.
Lemma lem5113658 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (h1 : term75 A x y z s) : @SUBSET A z s.
Proof. exact (proj2 (@lem5113657 A x y z s h1)). Qed.
Lemma lem5113659 {A : Type'} (z : A -> Prop) (s : A -> Prop) : (@SUBSET A z s) = ((@SUBSET A z s) = True).
Proof. exact (@lem7 (@SUBSET A z s)). Qed.
Lemma lem5113673 {A B : Type'} (f : A -> B) (y : A) : (term34 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5113674 {A : Type'} (f : type639 A) (y : A -> Prop) : (term35 A f y) = (f y).
Proof. exact (@lem5113673 (A -> Prop) (type686 A) f y). Qed.
Lemma lem5113675 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term36 A s x) = (term37 A s x).
Proof. exact (@lem5113674 A (term28 A s) x). Qed.
Lemma lem5113676 {A : Type'} (t1 : A -> Prop) (s : A -> Prop) : (term37 A s t1) = (term38 A t1 s).
Proof. exact (eq_refl (term37 A s t1)). Qed.
Lemma lem5113677 {A : Type'} (s : A -> Prop) : (term39 A s) = (term28 A s).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem5113676 A t1 s)). Qed.
Lemma lem5113678 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5113679 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term36 A s x) = (term37 A s x).
Proof. exact (MK_COMB (@lem5113677 A s) (@lem5113678 A x)). Qed.
Lemma lem5113680 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem5113681 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term40 A s x) = (term41 A s x).
Proof. exact (MK_COMB (@lem5113680 A) (@lem5113679 A s x)). Qed.
Lemma lem5113682 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term37 A s x) = (term38 A x s).
Proof. exact (eq_refl (term37 A s x)). Qed.
Lemma lem5113683 {A : Type'} (x : A -> Prop) (s : A -> Prop) : ((term36 A s x) = (term37 A s x)) = ((term37 A s x) = (term38 A x s)).
Proof. exact (MK_COMB (@lem5113681 A s x) (@lem5113682 A x s)). Qed.
Lemma lem5113684 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term37 A s x) = (term38 A x s).
Proof. exact (EQ_MP (@lem5113683 A x s) (@lem5113675 A s x)). Qed.
Lemma lem5113687 {A : Type'} (z : A -> Prop) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5113688 {A : Type'} (x : A -> Prop) (s : A -> Prop) (z : A -> Prop) : (term64 A s x z) = (term46 A x s z).
Proof. exact (MK_COMB (@lem5113684 A x s) (@lem5113687 A z)). Qed.
Lemma lem5113690 {A B : Type'} (f : A -> B) (y : A) : (term34 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5113691 {A : Type'} (f : type686 A) (y : A -> Prop) : (term44 A f y) = (f y).
Proof. exact (@lem5113690 (A -> Prop) Prop f y). Qed.
Lemma lem5113692 {A : Type'} (x : A -> Prop) (s : A -> Prop) (z : A -> Prop) : (term69 A x s z) = (term46 A x s z).
Proof. exact (@lem5113691 A (term38 A x s) z). Qed.
Lemma lem5113693 {A : Type'} (x : A -> Prop) (t2 : A -> Prop) (s : A -> Prop) : (term46 A x s t2) = (term47 A x t2 s).
Proof. exact (eq_refl (term46 A x s t2)). Qed.
Lemma lem5113694 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term48 A x s) = (term38 A x s).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem5113693 A x t2 s)). Qed.
Lemma lem5113695 {A : Type'} (z : A -> Prop) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem5113696 {A : Type'} (x : A -> Prop) (s : A -> Prop) (z : A -> Prop) : (term69 A x s z) = (term46 A x s z).
Proof. exact (MK_COMB (@lem5113694 A x s) (@lem5113695 A z)). Qed.
Lemma lem5113697 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5113698 {A : Type'} (x : A -> Prop) (s : A -> Prop) (z : A -> Prop) : (term70 A x s z) = (term71 A x s z).
Proof. exact (MK_COMB (@lem5113697) (@lem5113696 A x s z)). Qed.
Lemma lem5113699 {A : Type'} (x : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term46 A x s z) = (term47 A x z s).
Proof. exact (eq_refl (term46 A x s z)). Qed.
Lemma lem5113700 {A : Type'} (x : A -> Prop) (z : A -> Prop) (s : A -> Prop) : ((term69 A x s z) = (term46 A x s z)) = ((term46 A x s z) = (term47 A x z s)).
Proof. exact (MK_COMB (@lem5113698 A x s z) (@lem5113699 A x z s)). Qed.
Lemma lem5113701 {A : Type'} (x : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term46 A x s z) = (term47 A x z s).
Proof. exact (EQ_MP (@lem5113700 A x z s) (@lem5113692 A x s z)). Qed.
Lemma lem5113705 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (h1 : term75 A x y z s) : (@SUBSET A z s) = True.
Proof. exact (EQ_MP (@lem5113659 A z s) (@lem5113658 A x y z s h1)). Qed.
Lemma lem5113706 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term78 A x z) = (term78 A x z).
Proof. exact (eq_refl (term78 A x z)). Qed.
Lemma lem5113707 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (h1 : term75 A x y z s) : (term47 A x z s) = (term79 A x z).
Proof. exact (MK_COMB (@lem5113706 A x z) (@lem5113705 A x y z s h1)). Qed.
Lemma lem5113709 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem5113710 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term79 A x z) = (@PSUBSET A x z).
Proof. exact (@lem5113709 (@PSUBSET A x z)). Qed.
Lemma lem5113711 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (h1 : term75 A x y z s) : (term47 A x z s) = (@PSUBSET A x z).
Proof. exact (TRANS (@lem5113707 A x y z s h1) (@lem5113710 A x z)). Qed.
Lemma lem5113712 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (h1 : term75 A x y z s) : (term46 A x s z) = (@PSUBSET A x z).
Proof. exact (TRANS (@lem5113701 A x z s) (@lem5113711 A x y z s h1)). Qed.
Lemma lem5113713 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (h1 : term75 A x y z s) : (term64 A s x z) = (@PSUBSET A x z).
Proof. exact (TRANS (@lem5113688 A x s z) (@lem5113712 A x y z s h1)). Qed.
Lemma lem5113714 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) : term80 A y s x z.
Proof. exact (fun h0 : term75 A x y z s => @lem5113713 A x y z s h0). Qed.
Lemma lem5113715 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) : term81 A y s x z.
Proof. exact (@lem5113656 A x y z s (@PSUBSET A x z)). Qed.
Lemma lem5113716 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term82 A y s x z) = (term83 A y s x z).
Proof. exact (@lem5113715 A y s x z (@lem5113714 A y s x z)). Qed.
Lemma lem5113764 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) : (term84 A y s x) = (term85 A y s x).
Proof. exact (fun_ext (fun z : A -> Prop => @lem5113716 A y s x z)). Qed.
Lemma lem5113812 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5113813 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) : (term86 A y s x) = (term87 A y s x).
Proof. exact (MK_COMB (@lem5113812 A) (@lem5113764 A y s x)). Qed.
Lemma lem5113865 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term88 A s x) = (term89 A s x).
Proof. exact (fun_ext (fun y : A -> Prop => @lem5113813 A y s x)). Qed.
Lemma lem5113917 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5113918 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term90 A s x) = (term91 A s x).
Proof. exact (MK_COMB (@lem5113917 A) (@lem5113865 A s x)). Qed.
Lemma lem5113974 {A : Type'} (s : A -> Prop) : (term92 A s) = (term93 A s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem5113918 A s x)). Qed.
Lemma lem5114030 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5114031 {A : Type'} (s : A -> Prop) : (term32 A s) = (term94 A s).
Proof. exact (MK_COMB (@lem5114030 A) (@lem5113974 A s)). Qed.
Lemma lem5114091 {A : Type'} (s : A -> Prop) : (term95 A s) = (term96 A s).
Proof. exact (MK_COMB (@lem5113540 A s) (@lem5114031 A s)). Qed.
Lemma lem5114159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5114160 {A : Type'} (s : A -> Prop) : (term97 A s) = (term98 A s).
Proof. exact (MK_COMB (@lem5114159) (@lem5114091 A s)). Qed.
Lemma lem5114237 {A B : Type'} (f : A -> B) (y : A) : (term34 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5114238 {A : Type'} (f : type639 A) (y : A -> Prop) : (term35 A f y) = (f y).
Proof. exact (@lem5114237 (A -> Prop) (type686 A) f y). Qed.
Lemma lem5114239 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term36 A s y) = (term37 A s y).
Proof. exact (@lem5114238 A (term28 A s) y). Qed.
Lemma lem5114240 {A : Type'} (t1 : A -> Prop) (s : A -> Prop) : (term37 A s t1) = (term38 A t1 s).
Proof. exact (eq_refl (term37 A s t1)). Qed.
Lemma lem5114241 {A : Type'} (s : A -> Prop) : (term39 A s) = (term28 A s).
Proof. exact (fun_ext (fun t1 : A -> Prop => @lem5114240 A t1 s)). Qed.
Lemma lem5114242 {A : Type'} (y : A -> Prop) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5114243 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term36 A s y) = (term37 A s y).
Proof. exact (MK_COMB (@lem5114241 A s) (@lem5114242 A y)). Qed.
Lemma lem5114244 {A : Type'} : (@eq ((A -> Prop) -> Prop)) = (@eq ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((A -> Prop) -> Prop))). Qed.
Lemma lem5114245 {A : Type'} (s : A -> Prop) (y : A -> Prop) : (term40 A s y) = (term41 A s y).
Proof. exact (MK_COMB (@lem5114244 A) (@lem5114243 A s y)). Qed.
Lemma lem5114246 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term37 A s y) = (term38 A y s).
Proof. exact (eq_refl (term37 A s y)). Qed.
Lemma lem5114247 {A : Type'} (y : A -> Prop) (s : A -> Prop) : ((term36 A s y) = (term37 A s y)) = ((term37 A s y) = (term38 A y s)).
Proof. exact (MK_COMB (@lem5114245 A s y) (@lem5114246 A y s)). Qed.
Lemma lem5114248 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term37 A s y) = (term38 A y s).
Proof. exact (EQ_MP (@lem5114247 A y s) (@lem5114239 A s y)). Qed.
Lemma lem5114251 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5114252 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) : (term64 A s y x) = (term46 A y s x).
Proof. exact (MK_COMB (@lem5114248 A y s) (@lem5114251 A x)). Qed.
Lemma lem5114254 {A B : Type'} (f : A -> B) (y : A) : (term34 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem5114255 {A : Type'} (f : type686 A) (y : A -> Prop) : (term44 A f y) = (f y).
Proof. exact (@lem5114254 (A -> Prop) Prop f y). Qed.
Lemma lem5114256 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) : (term69 A y s x) = (term46 A y s x).
Proof. exact (@lem5114255 A (term38 A y s) x). Qed.
Lemma lem5114257 {A : Type'} (y : A -> Prop) (t2 : A -> Prop) (s : A -> Prop) : (term46 A y s t2) = (term47 A y t2 s).
Proof. exact (eq_refl (term46 A y s t2)). Qed.
Lemma lem5114258 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term48 A y s) = (term38 A y s).
Proof. exact (fun_ext (fun t2 : A -> Prop => @lem5114257 A y t2 s)). Qed.
Lemma lem5114259 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5114260 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) : (term69 A y s x) = (term46 A y s x).
Proof. exact (MK_COMB (@lem5114258 A y s) (@lem5114259 A x)). Qed.
Lemma lem5114261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5114262 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) : (term70 A y s x) = (term71 A y s x).
Proof. exact (MK_COMB (@lem5114261) (@lem5114260 A y s x)). Qed.
Lemma lem5114263 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : A -> Prop) : (term46 A y s x) = (term47 A y x s).
Proof. exact (eq_refl (term46 A y s x)). Qed.
Lemma lem5114264 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : A -> Prop) : ((term69 A y s x) = (term46 A y s x)) = ((term46 A y s x) = (term47 A y x s)).
Proof. exact (MK_COMB (@lem5114262 A y s x) (@lem5114263 A y x s)). Qed.
Lemma lem5114265 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : A -> Prop) : (term46 A y s x) = (term47 A y x s).
Proof. exact (EQ_MP (@lem5114264 A y x s) (@lem5114256 A y s x)). Qed.
Lemma lem5114268 {A : Type'} (y : A -> Prop) (x : A -> Prop) (s : A -> Prop) : (term64 A s y x) = (term47 A y x s).
Proof. exact (TRANS (@lem5114252 A y s x) (@lem5114265 A y x s)). Qed.
Lemma lem5114269 {A : Type'} (GEN_PVAR_227 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_227) = (@SETSPEC (A -> Prop) GEN_PVAR_227).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_227)). Qed.
Lemma lem5114270 {A : Type'} (GEN_PVAR_227 : A -> Prop) (y : A -> Prop) (x : A -> Prop) (s : A -> Prop) : (term99 A GEN_PVAR_227 s y x) = (term100 A GEN_PVAR_227 y x s).
Proof. exact (MK_COMB (@lem5114269 A GEN_PVAR_227) (@lem5114268 A y x s)). Qed.
Lemma lem5114273 {A : Type'} (y : A -> Prop) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5114274 {A : Type'} (GEN_PVAR_227 : A -> Prop) (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) : (term101 A GEN_PVAR_227 s x y) = (term102 A GEN_PVAR_227 x s y).
Proof. exact (MK_COMB (@lem5114270 A GEN_PVAR_227 y x s) (@lem5114273 A y)). Qed.
Lemma lem5114277 {A : Type'} (GEN_PVAR_227 : A -> Prop) (x : A -> Prop) (s : A -> Prop) : (term103 A GEN_PVAR_227 s x) = (term104 A GEN_PVAR_227 x s).
Proof. exact (fun_ext (fun y : A -> Prop => @lem5114274 A GEN_PVAR_227 x s y)). Qed.
Lemma lem5114280 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5114281 {A : Type'} (GEN_PVAR_227 : A -> Prop) (x : A -> Prop) (s : A -> Prop) : (term105 A GEN_PVAR_227 s x) = (term106 A GEN_PVAR_227 x s).
Proof. exact (MK_COMB (@lem5114280 A) (@lem5114277 A GEN_PVAR_227 x s)). Qed.
Lemma lem5114288 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term107 A s x) = (term108 A x s).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A -> Prop => @lem5114281 A GEN_PVAR_227 x s)). Qed.
Lemma lem5114295 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem5114296 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term109 A s x) = (term110 A x s).
Proof. exact (MK_COMB (@lem5114295 A) (@lem5114288 A x s)). Qed.
Lemma lem5114303 {A : Type'} : (@FINITE (A -> Prop)) = (@FINITE (A -> Prop)).
Proof. exact (eq_refl (@FINITE (A -> Prop))). Qed.
Lemma lem5114304 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term111 A s x) = (term112 A x s).
Proof. exact (MK_COMB (@lem5114303 A) (@lem5114296 A x s)). Qed.
Lemma lem5114311 {A : Type'} (s : A -> Prop) : (term113 A s) = (term114 A s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem5114304 A x s)). Qed.
Lemma lem5114318 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5114319 {A : Type'} (s : A -> Prop) : (term33 A s) = (term115 A s).
Proof. exact (MK_COMB (@lem5114318 A) (@lem5114311 A s)). Qed.
Lemma lem5114330 {A : Type'} (s : A -> Prop) : (term30 A s) = (term116 A s).
Proof. exact (MK_COMB (@lem5114160 A s) (@lem5114319 A s)). Qed.
Lemma lem5114410 {A : Type'} (s : A -> Prop) : (term29 A s) = (term116 A s).
Proof. exact (TRANS (@lem5113482 A s) (@lem5114330 A s)). Qed.
Lemma lem5114411 {A : Type'} (s : A -> Prop) : (term116 A s) = (term29 A s).
Proof. exact (SYM (@lem5114410 A s)). Qed.
Lemma lem5114421 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term117 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem5114422 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term117 A s t).
Proof. exact (@lem5114421 A s t). Qed.
Lemma lem5114423 {A : Type'} (x : A -> Prop) : (@PSUBSET A x x) = (term118 A x).
Proof. exact (@lem5114422 A x x). Qed.
Lemma lem5114427 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5114428 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (@lem5114427 A s t). Qed.
Lemma lem5114429 {A : Type'} (x : A -> Prop) : (@SUBSET A x x) = (term120 A x).
Proof. exact (@lem5114428 A x x). Qed.
Lemma lem5114435 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem5114436 {A : Type'} (x : A) (x' : A -> Prop) : (term121 A x x') = True.
Proof. exact (@lem5114435 (@IN A x x')). Qed.
Lemma lem5114437 {A : Type'} (x : A -> Prop) : (term122 A x) = (term123 A).
Proof. exact (fun_ext (fun x' : A => @lem5114436 A x' x)). Qed.
Lemma lem5114438 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5114439 {A : Type'} (x : A -> Prop) : (term120 A x) = (term124 A).
Proof. exact (MK_COMB (@lem5114438 A) (@lem5114437 A x)). Qed.
Lemma lem5114441 {A : Type'} (t : Prop) : (term125 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5114442 {A : Type'} (t : Prop) : (term125 A t) = t.
Proof. exact (@lem5114441 A t). Qed.
Lemma lem5114443 {A : Type'} : (term124 A) = True.
Proof. exact (@lem5114442 A True). Qed.
Lemma lem5114444 {A : Type'} (x : A -> Prop) : (term120 A x) = True.
Proof. exact (TRANS (@lem5114439 A x) (@lem5114443 A)). Qed.
Lemma lem5114445 {A : Type'} (x : A -> Prop) : (@SUBSET A x x) = True.
Proof. exact (TRANS (@lem5114429 A x) (@lem5114444 A x)). Qed.
Lemma lem5114446 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5114447 {A : Type'} (x : A -> Prop) : (term126 A x) = (and True).
Proof. exact (MK_COMB (@lem5114446) (@lem5114445 A x)). Qed.
Lemma lem5114449 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5114450 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem5114449 (A -> Prop) x). Qed.
Lemma lem5114451 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5114452 {A : Type'} (x : A -> Prop) : (term127 A x) = (~ True).
Proof. exact (MK_COMB (@lem5114451) (@lem5114450 A x)). Qed.
Lemma lem5114454 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem5114455 {A : Type'} (x : A -> Prop) : (term127 A x) = False.
Proof. exact (TRANS (@lem5114452 A x) (@lem5114454)). Qed.
Lemma lem5114456 {A : Type'} (x : A -> Prop) : (term118 A x) = (True /\ False).
Proof. exact (MK_COMB (@lem5114447 A x) (@lem5114455 A x)). Qed.
Lemma lem5114458 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5114459 : (True /\ False) = False.
Proof. exact (@lem5114458 False). Qed.
Lemma lem5114460 {A : Type'} (x : A -> Prop) : (term118 A x) = False.
Proof. exact (TRANS (@lem5114456 A x) (@lem5114459)). Qed.
Lemma lem5114461 {A : Type'} (x : A -> Prop) : (@PSUBSET A x x) = False.
Proof. exact (TRANS (@lem5114423 A x) (@lem5114460 A x)). Qed.
Lemma lem5114462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5114463 {A : Type'} (x : A -> Prop) : (term128 A x) = (and False).
Proof. exact (MK_COMB (@lem5114462) (@lem5114461 A x)). Qed.
Lemma lem5114465 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5114466 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (@lem5114465 A s t). Qed.
Lemma lem5114467 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (@SUBSET A x s) = (term119 A x s).
Proof. exact (@lem5114466 A x s). Qed.
Lemma lem5114474 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term51 A x s) = (term129 A x s).
Proof. exact (MK_COMB (@lem5114463 A x) (@lem5114467 A x s)). Qed.
Lemma lem5114476 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem5114477 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term129 A x s) = False.
Proof. exact (@lem5114476 (term119 A x s)). Qed.
Lemma lem5114478 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term51 A x s) = False.
Proof. exact (TRANS (@lem5114474 A x s) (@lem5114477 A x s)). Qed.
Lemma lem5114479 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5114480 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term53 A x s) = (~ False).
Proof. exact (MK_COMB (@lem5114479) (@lem5114478 A x s)). Qed.
Lemma lem5114482 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5114483 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term53 A x s) = True.
Proof. exact (TRANS (@lem5114480 A x s) (@lem5114482)). Qed.
Lemma lem5114484 {A : Type'} (s : A -> Prop) : (term55 A s) = (term130 A).
Proof. exact (fun_ext (fun x : A -> Prop => @lem5114483 A x s)). Qed.
Lemma lem5114485 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5114486 {A : Type'} (s : A -> Prop) : (term56 A s) = (term131 A).
Proof. exact (MK_COMB (@lem5114485 A) (@lem5114484 A s)). Qed.
Lemma lem5114488 {A : Type'} (t : Prop) : (term125 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5114489 {A : Type'} (t : Prop) : (term132 A t) = t.
Proof. exact (@lem5114488 (A -> Prop) t). Qed.
Lemma lem5114490 {A : Type'} : (term131 A) = True.
Proof. exact (@lem5114489 A True). Qed.
Lemma lem5114491 {A : Type'} (s : A -> Prop) : (term56 A s) = True.
Proof. exact (TRANS (@lem5114486 A s) (@lem5114490 A)). Qed.
Lemma lem5114492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5114493 {A : Type'} (s : A -> Prop) : (term58 A s) = (and True).
Proof. exact (MK_COMB (@lem5114492) (@lem5114491 A s)). Qed.
Lemma lem5114515 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term117 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem5114516 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term117 A s t).
Proof. exact (@lem5114515 A s t). Qed.
Lemma lem5114517 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (@PSUBSET A x y) = (term117 A x y).
Proof. exact (@lem5114516 A x y). Qed.
Lemma lem5114521 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5114522 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (@lem5114521 A s t). Qed.
Lemma lem5114523 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (@SUBSET A x y) = (term119 A x y).
Proof. exact (@lem5114522 A x y). Qed.
Lemma lem5114530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5114531 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term133 A x y) = (term134 A x y).
Proof. exact (MK_COMB (@lem5114530) (@lem5114523 A x y)). Qed.
Lemma lem5114535 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term135 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5114536 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term135 A s t).
Proof. exact (@lem5114535 A s t). Qed.
Lemma lem5114537 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (x = y) = (term135 A x y).
Proof. exact (@lem5114536 A x y). Qed.
Lemma lem5114546 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5114547 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term136 A x y) = (term137 A x y).
Proof. exact (MK_COMB (@lem5114546) (@lem5114537 A x y)). Qed.
Lemma lem5114548 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term117 A x y) = (term138 A x y).
Proof. exact (MK_COMB (@lem5114531 A x y) (@lem5114547 A x y)). Qed.
Lemma lem5114551 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (@PSUBSET A x y) = (term138 A x y).
Proof. exact (TRANS (@lem5114517 A x y) (@lem5114548 A x y)). Qed.
Lemma lem5114552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5114553 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term78 A x y) = (term139 A x y).
Proof. exact (MK_COMB (@lem5114552) (@lem5114551 A x y)). Qed.
Lemma lem5114555 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5114556 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (@lem5114555 A s t). Qed.
Lemma lem5114557 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (@SUBSET A y s) = (term119 A y s).
Proof. exact (@lem5114556 A y s). Qed.
Lemma lem5114564 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term47 A x y s) = (term140 A x y s).
Proof. exact (MK_COMB (@lem5114553 A x y) (@lem5114557 A y s)). Qed.
Lemma lem5114567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5114568 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term73 A x y s) = (term141 A x y s).
Proof. exact (MK_COMB (@lem5114567) (@lem5114564 A x y s)). Qed.
Lemma lem5114570 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term117 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem5114571 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term117 A s t).
Proof. exact (@lem5114570 A s t). Qed.
Lemma lem5114572 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (@PSUBSET A y z) = (term117 A y z).
Proof. exact (@lem5114571 A y z). Qed.
Lemma lem5114576 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5114577 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (@lem5114576 A s t). Qed.
Lemma lem5114578 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (@SUBSET A y z) = (term119 A y z).
Proof. exact (@lem5114577 A y z). Qed.
Lemma lem5114585 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5114586 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term133 A y z) = (term134 A y z).
Proof. exact (MK_COMB (@lem5114585) (@lem5114578 A y z)). Qed.
Lemma lem5114590 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term135 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5114591 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term135 A s t).
Proof. exact (@lem5114590 A s t). Qed.
Lemma lem5114592 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (y = z) = (term135 A y z).
Proof. exact (@lem5114591 A y z). Qed.
Lemma lem5114601 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5114602 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term136 A y z) = (term137 A y z).
Proof. exact (MK_COMB (@lem5114601) (@lem5114592 A y z)). Qed.
Lemma lem5114603 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term117 A y z) = (term138 A y z).
Proof. exact (MK_COMB (@lem5114586 A y z) (@lem5114602 A y z)). Qed.
Lemma lem5114606 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (@PSUBSET A y z) = (term138 A y z).
Proof. exact (TRANS (@lem5114572 A y z) (@lem5114603 A y z)). Qed.
Lemma lem5114607 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term142 A x s y z) = (term143 A x s y z).
Proof. exact (MK_COMB (@lem5114568 A x y s) (@lem5114606 A y z)). Qed.
Lemma lem5114610 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5114611 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term144 A x s y z) = (term145 A x s y z).
Proof. exact (MK_COMB (@lem5114610) (@lem5114607 A x s y z)). Qed.
Lemma lem5114613 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5114614 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (@lem5114613 A s t). Qed.
Lemma lem5114615 {A : Type'} (z : A -> Prop) (s : A -> Prop) : (@SUBSET A z s) = (term119 A z s).
Proof. exact (@lem5114614 A z s). Qed.
Lemma lem5114622 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term75 A x y z s) = (term146 A x y z s).
Proof. exact (MK_COMB (@lem5114611 A x s y z) (@lem5114615 A z s)). Qed.
Lemma lem5114625 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5114626 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term147 A x y z s) = (term148 A x y z s).
Proof. exact (MK_COMB (@lem5114625) (@lem5114622 A x y z s)). Qed.
Lemma lem5114628 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term117 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem5114629 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term117 A s t).
Proof. exact (@lem5114628 A s t). Qed.
Lemma lem5114630 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (@PSUBSET A x z) = (term117 A x z).
Proof. exact (@lem5114629 A x z). Qed.
Lemma lem5114634 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5114635 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (@lem5114634 A s t). Qed.
Lemma lem5114636 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (@SUBSET A x z) = (term119 A x z).
Proof. exact (@lem5114635 A x z). Qed.
Lemma lem5114643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5114644 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term133 A x z) = (term134 A x z).
Proof. exact (MK_COMB (@lem5114643) (@lem5114636 A x z)). Qed.
Lemma lem5114648 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term135 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5114649 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term135 A s t).
Proof. exact (@lem5114648 A s t). Qed.
Lemma lem5114650 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (x = z) = (term135 A x z).
Proof. exact (@lem5114649 A x z). Qed.
Lemma lem5114659 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5114660 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term136 A x z) = (term137 A x z).
Proof. exact (MK_COMB (@lem5114659) (@lem5114650 A x z)). Qed.
Lemma lem5114661 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term117 A x z) = (term138 A x z).
Proof. exact (MK_COMB (@lem5114644 A x z) (@lem5114660 A x z)). Qed.
Lemma lem5114664 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (@PSUBSET A x z) = (term138 A x z).
Proof. exact (TRANS (@lem5114630 A x z) (@lem5114661 A x z)). Qed.
Lemma lem5114665 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term83 A y s x z) = (term149 A y s x z).
Proof. exact (MK_COMB (@lem5114626 A x y z s) (@lem5114664 A x z)). Qed.
Lemma lem5114668 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) : (term85 A y s x) = (term150 A y s x).
Proof. exact (fun_ext (fun z : A -> Prop => @lem5114665 A y s x z)). Qed.
Lemma lem5114669 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5114670 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) : (term87 A y s x) = (term151 A y s x).
Proof. exact (MK_COMB (@lem5114669 A) (@lem5114668 A y s x)). Qed.
Lemma lem5114675 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term89 A s x) = (term152 A s x).
Proof. exact (fun_ext (fun y : A -> Prop => @lem5114670 A y s x)). Qed.
Lemma lem5114676 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5114677 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term91 A s x) = (term153 A s x).
Proof. exact (MK_COMB (@lem5114676 A) (@lem5114675 A s x)). Qed.
Lemma lem5114682 {A : Type'} (s : A -> Prop) : (term93 A s) = (term154 A s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem5114677 A s x)). Qed.
Lemma lem5114683 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5114684 {A : Type'} (s : A -> Prop) : (term94 A s) = (term155 A s).
Proof. exact (MK_COMB (@lem5114683 A) (@lem5114682 A s)). Qed.
Lemma lem5114689 {A : Type'} (s : A -> Prop) : (term96 A s) = (term156 A s).
Proof. exact (MK_COMB (@lem5114493 A s) (@lem5114684 A s)). Qed.
Lemma lem5114691 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5114692 {A : Type'} (s : A -> Prop) : (term156 A s) = (term155 A s).
Proof. exact (@lem5114691 (term155 A s)). Qed.
Lemma lem5114773 {A : Type'} (s : A -> Prop) : (term96 A s) = (term155 A s).
Proof. exact (TRANS (@lem5114689 A s) (@lem5114692 A s)). Qed.
Lemma lem5114774 {A : Type'} (s : A -> Prop) : (term155 A s) = (term96 A s).
Proof. exact (SYM (@lem5114773 A s)). Qed.
Lemma lem5114804 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5114805 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5114804 A P x). Qed.
Lemma lem5114806 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem5114805 A x x'). Qed.
Lemma lem5114807 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5114808 {A : Type'} (x : A -> Prop) (x' : A) : (term157 A x' x) = (term158 A x x').
Proof. exact (MK_COMB (@lem5114807) (@lem5114806 A x x')). Qed.
Lemma lem5114810 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5114811 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5114810 A P x). Qed.
Lemma lem5114812 {A : Type'} (y : A -> Prop) (x : A) : (@IN A x y) = (y x).
Proof. exact (@lem5114811 A y x). Qed.
Lemma lem5114813 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term159 A x x' y) = (term160 A x y x').
Proof. exact (MK_COMB (@lem5114808 A x x') (@lem5114812 A y x')). Qed.
Lemma lem5114816 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term161 A x y) = (term162 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5114813 A x y x')). Qed.
Lemma lem5114817 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5114818 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term119 A x y) = (term163 A x y).
Proof. exact (MK_COMB (@lem5114817 A) (@lem5114816 A x y)). Qed.
Lemma lem5114823 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5114824 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term134 A x y) = (term164 A x y).
Proof. exact (MK_COMB (@lem5114823) (@lem5114818 A x y)). Qed.
Lemma lem5114832 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5114833 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5114832 A P x). Qed.
Lemma lem5114834 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem5114833 A x x'). Qed.
Lemma lem5114835 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5114836 {A : Type'} (x : A -> Prop) (x' : A) : (term165 A x' x) = (term166 A x x').
Proof. exact (MK_COMB (@lem5114835) (@lem5114834 A x x')). Qed.
Lemma lem5114838 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5114839 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5114838 A P x). Qed.
Lemma lem5114840 {A : Type'} (y : A -> Prop) (x : A) : (@IN A x y) = (y x).
Proof. exact (@lem5114839 A y x). Qed.
Lemma lem5114841 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : ((@IN A x' x) = (@IN A x' y)) = ((x x') = (y x')).
Proof. exact (MK_COMB (@lem5114836 A x x') (@lem5114840 A y x')). Qed.
Lemma lem5114844 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term167 A x y) = (term168 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5114841 A x y x')). Qed.
Lemma lem5114845 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5114846 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term135 A x y) = (term169 A x y).
Proof. exact (MK_COMB (@lem5114845 A) (@lem5114844 A x y)). Qed.
Lemma lem5114851 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5114852 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term137 A x y) = (term170 A x y).
Proof. exact (MK_COMB (@lem5114851) (@lem5114846 A x y)). Qed.
Lemma lem5114853 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term138 A x y) = (term171 A x y).
Proof. exact (MK_COMB (@lem5114824 A x y) (@lem5114852 A x y)). Qed.
Lemma lem5114856 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5114857 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term139 A x y) = (term172 A x y).
Proof. exact (MK_COMB (@lem5114856) (@lem5114853 A x y)). Qed.
Lemma lem5114865 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5114866 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5114865 A P x). Qed.
Lemma lem5114867 {A : Type'} (y : A -> Prop) (x : A) : (@IN A x y) = (y x).
Proof. exact (@lem5114866 A y x). Qed.
Lemma lem5114868 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5114869 {A : Type'} (y : A -> Prop) (x : A) : (term157 A x y) = (term158 A y x).
Proof. exact (MK_COMB (@lem5114868) (@lem5114867 A y x)). Qed.
Lemma lem5114871 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5114872 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5114871 A P x). Qed.
Lemma lem5114873 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5114872 A s x). Qed.
Lemma lem5114874 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A) : (term159 A y x s) = (term160 A y s x).
Proof. exact (MK_COMB (@lem5114869 A y x) (@lem5114873 A s x)). Qed.
Lemma lem5114877 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term161 A y s) = (term162 A y s).
Proof. exact (fun_ext (fun x : A => @lem5114874 A y s x)). Qed.
Lemma lem5114878 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5114879 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term119 A y s) = (term163 A y s).
Proof. exact (MK_COMB (@lem5114878 A) (@lem5114877 A y s)). Qed.
Lemma lem5114884 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term140 A x y s) = (term173 A x y s).
Proof. exact (MK_COMB (@lem5114857 A x y) (@lem5114879 A y s)). Qed.
Lemma lem5114887 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5114888 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term141 A x y s) = (term174 A x y s).
Proof. exact (MK_COMB (@lem5114887) (@lem5114884 A x y s)). Qed.
Lemma lem5114898 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5114899 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5114898 A P x). Qed.
Lemma lem5114900 {A : Type'} (y : A -> Prop) (x : A) : (@IN A x y) = (y x).
Proof. exact (@lem5114899 A y x). Qed.
Lemma lem5114901 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5114902 {A : Type'} (y : A -> Prop) (x : A) : (term157 A x y) = (term158 A y x).
Proof. exact (MK_COMB (@lem5114901) (@lem5114900 A y x)). Qed.
Lemma lem5114904 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5114905 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5114904 A P x). Qed.
Lemma lem5114906 {A : Type'} (z : A -> Prop) (x : A) : (@IN A x z) = (z x).
Proof. exact (@lem5114905 A z x). Qed.
Lemma lem5114907 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term159 A y x z) = (term160 A y z x).
Proof. exact (MK_COMB (@lem5114902 A y x) (@lem5114906 A z x)). Qed.
Lemma lem5114910 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term161 A y z) = (term162 A y z).
Proof. exact (fun_ext (fun x : A => @lem5114907 A y z x)). Qed.
Lemma lem5114911 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5114912 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term119 A y z) = (term163 A y z).
Proof. exact (MK_COMB (@lem5114911 A) (@lem5114910 A y z)). Qed.
Lemma lem5114917 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5114918 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term134 A y z) = (term164 A y z).
Proof. exact (MK_COMB (@lem5114917) (@lem5114912 A y z)). Qed.
Lemma lem5114926 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5114927 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5114926 A P x). Qed.
Lemma lem5114928 {A : Type'} (y : A -> Prop) (x : A) : (@IN A x y) = (y x).
Proof. exact (@lem5114927 A y x). Qed.
Lemma lem5114929 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5114930 {A : Type'} (y : A -> Prop) (x : A) : (term165 A x y) = (term166 A y x).
Proof. exact (MK_COMB (@lem5114929) (@lem5114928 A y x)). Qed.
Lemma lem5114932 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5114933 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5114932 A P x). Qed.
Lemma lem5114934 {A : Type'} (z : A -> Prop) (x : A) : (@IN A x z) = (z x).
Proof. exact (@lem5114933 A z x). Qed.
Lemma lem5114935 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : ((@IN A x y) = (@IN A x z)) = ((y x) = (z x)).
Proof. exact (MK_COMB (@lem5114930 A y x) (@lem5114934 A z x)). Qed.
Lemma lem5114938 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term167 A y z) = (term168 A y z).
Proof. exact (fun_ext (fun x : A => @lem5114935 A y z x)). Qed.
Lemma lem5114939 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5114940 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term135 A y z) = (term169 A y z).
Proof. exact (MK_COMB (@lem5114939 A) (@lem5114938 A y z)). Qed.
Lemma lem5114945 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5114946 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term137 A y z) = (term170 A y z).
Proof. exact (MK_COMB (@lem5114945) (@lem5114940 A y z)). Qed.
Lemma lem5114947 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term138 A y z) = (term171 A y z).
Proof. exact (MK_COMB (@lem5114918 A y z) (@lem5114946 A y z)). Qed.
Lemma lem5114950 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term143 A x s y z) = (term175 A x s y z).
Proof. exact (MK_COMB (@lem5114888 A x y s) (@lem5114947 A y z)). Qed.
Lemma lem5114953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5114954 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term145 A x s y z) = (term176 A x s y z).
Proof. exact (MK_COMB (@lem5114953) (@lem5114950 A x s y z)). Qed.
Lemma lem5114962 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5114963 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5114962 A P x). Qed.
Lemma lem5114964 {A : Type'} (z : A -> Prop) (x : A) : (@IN A x z) = (z x).
Proof. exact (@lem5114963 A z x). Qed.
Lemma lem5114965 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5114966 {A : Type'} (z : A -> Prop) (x : A) : (term157 A x z) = (term158 A z x).
Proof. exact (MK_COMB (@lem5114965) (@lem5114964 A z x)). Qed.
Lemma lem5114968 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5114969 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5114968 A P x). Qed.
Lemma lem5114970 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5114969 A s x). Qed.
Lemma lem5114971 {A : Type'} (z : A -> Prop) (s : A -> Prop) (x : A) : (term159 A z x s) = (term160 A z s x).
Proof. exact (MK_COMB (@lem5114966 A z x) (@lem5114970 A s x)). Qed.
Lemma lem5114974 {A : Type'} (z : A -> Prop) (s : A -> Prop) : (term161 A z s) = (term162 A z s).
Proof. exact (fun_ext (fun x : A => @lem5114971 A z s x)). Qed.
Lemma lem5114975 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5114976 {A : Type'} (z : A -> Prop) (s : A -> Prop) : (term119 A z s) = (term163 A z s).
Proof. exact (MK_COMB (@lem5114975 A) (@lem5114974 A z s)). Qed.
Lemma lem5114981 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term146 A x y z s) = (term177 A x y z s).
Proof. exact (MK_COMB (@lem5114954 A x s y z) (@lem5114976 A z s)). Qed.
Lemma lem5114984 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5114985 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term148 A x y z s) = (term178 A x y z s).
Proof. exact (MK_COMB (@lem5114984) (@lem5114981 A x y z s)). Qed.
Lemma lem5114995 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5114996 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5114995 A P x). Qed.
Lemma lem5114997 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem5114996 A x x'). Qed.
Lemma lem5114998 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5114999 {A : Type'} (x : A -> Prop) (x' : A) : (term157 A x' x) = (term158 A x x').
Proof. exact (MK_COMB (@lem5114998) (@lem5114997 A x x')). Qed.
Lemma lem5115001 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5115002 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5115001 A P x). Qed.
Lemma lem5115003 {A : Type'} (z : A -> Prop) (x : A) : (@IN A x z) = (z x).
Proof. exact (@lem5115002 A z x). Qed.
Lemma lem5115004 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term159 A x x' z) = (term160 A x z x').
Proof. exact (MK_COMB (@lem5114999 A x x') (@lem5115003 A z x')). Qed.
Lemma lem5115007 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term161 A x z) = (term162 A x z).
Proof. exact (fun_ext (fun x' : A => @lem5115004 A x z x')). Qed.
Lemma lem5115008 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5115009 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term119 A x z) = (term163 A x z).
Proof. exact (MK_COMB (@lem5115008 A) (@lem5115007 A x z)). Qed.
Lemma lem5115014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115015 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term134 A x z) = (term164 A x z).
Proof. exact (MK_COMB (@lem5115014) (@lem5115009 A x z)). Qed.
Lemma lem5115023 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5115024 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5115023 A P x). Qed.
Lemma lem5115025 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem5115024 A x x'). Qed.
Lemma lem5115026 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5115027 {A : Type'} (x : A -> Prop) (x' : A) : (term165 A x' x) = (term166 A x x').
Proof. exact (MK_COMB (@lem5115026) (@lem5115025 A x x')). Qed.
Lemma lem5115029 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5115030 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5115029 A P x). Qed.
Lemma lem5115031 {A : Type'} (z : A -> Prop) (x : A) : (@IN A x z) = (z x).
Proof. exact (@lem5115030 A z x). Qed.
Lemma lem5115032 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : ((@IN A x' x) = (@IN A x' z)) = ((x x') = (z x')).
Proof. exact (MK_COMB (@lem5115027 A x x') (@lem5115031 A z x')). Qed.
Lemma lem5115035 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term167 A x z) = (term168 A x z).
Proof. exact (fun_ext (fun x' : A => @lem5115032 A x z x')). Qed.
Lemma lem5115036 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5115037 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term135 A x z) = (term169 A x z).
Proof. exact (MK_COMB (@lem5115036 A) (@lem5115035 A x z)). Qed.
Lemma lem5115042 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5115043 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term137 A x z) = (term170 A x z).
Proof. exact (MK_COMB (@lem5115042) (@lem5115037 A x z)). Qed.
Lemma lem5115044 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term138 A x z) = (term171 A x z).
Proof. exact (MK_COMB (@lem5115015 A x z) (@lem5115043 A x z)). Qed.
Lemma lem5115047 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term149 A y s x z) = (term179 A y s x z).
Proof. exact (MK_COMB (@lem5114985 A x y z s) (@lem5115044 A x z)). Qed.
Lemma lem5115050 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) : (term150 A y s x) = (term180 A y s x).
Proof. exact (fun_ext (fun z : A -> Prop => @lem5115047 A y s x z)). Qed.
Lemma lem5115051 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5115052 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) : (term151 A y s x) = (term181 A y s x).
Proof. exact (MK_COMB (@lem5115051 A) (@lem5115050 A y s x)). Qed.
Lemma lem5115057 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term152 A s x) = (term182 A s x).
Proof. exact (fun_ext (fun y : A -> Prop => @lem5115052 A y s x)). Qed.
Lemma lem5115058 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5115059 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term153 A s x) = (term183 A s x).
Proof. exact (MK_COMB (@lem5115058 A) (@lem5115057 A s x)). Qed.
Lemma lem5115064 {A : Type'} (s : A -> Prop) : (term154 A s) = (term184 A s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem5115059 A s x)). Qed.
Lemma lem5115065 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5115066 {A : Type'} (s : A -> Prop) : (term155 A s) = (term185 A s).
Proof. exact (MK_COMB (@lem5115065 A) (@lem5115064 A s)). Qed.
Lemma lem5115071 {A : Type'} (s : A -> Prop) : (term185 A s) = (term155 A s).
Proof. exact (SYM (@lem5115066 A s)). Qed.
Lemma lem5115073 (p : Prop) : p = (term186 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5115074 {A : Type'} (s : A -> Prop) : (term185 A s) = (term187 A s).
Proof. exact (@lem5115073 (term185 A s)). Qed.
Lemma lem5115075 {A : Type'} (s : A -> Prop) : (term187 A s) = (term185 A s).
Proof. exact (SYM (@lem5115074 A s)). Qed.
Lemma lem5115076 {A : Type'} (s : A -> Prop) (h1 : term188 A s) : term188 A s.
Proof. exact (h1). Qed.
Lemma lem5115079 {A : Type'} (s : A -> Prop) (h1 : term187 A s) : term187 A s.
Proof. exact (h1). Qed.
Lemma lem5115080 {A : Type'} (s : A -> Prop) : term189 A s.
Proof. exact (fun h0 : term187 A s => @lem5115079 A s h0). Qed.
Lemma lem5115081 {A : Type'} (s : A -> Prop) (h1 : term189 A s) : term189 A s.
Proof. exact (h1). Qed.
Lemma lem5115082 {A : Type'} (s : A -> Prop) (h1 : term187 A s) : term187 A s.
Proof. exact (h1). Qed.
Lemma lem5115083 {A : Type'} (s : A -> Prop) (h1 : term187 A s) (h2 : term189 A s) : term187 A s.
Proof. exact (@lem5115081 A s h2 (@lem5115082 A s h1)). Qed.
Lemma lem5115084 {A : Type'} (s : A -> Prop) (h1 : term187 A s) : term190 A s.
Proof. exact (fun h0 : term189 A s => @lem5115083 A s h1 h0). Qed.
Lemma lem5115085 {A : Type'} (s : A -> Prop) (h1 : term189 A s) : term189 A s.
Proof. exact (h1). Qed.
Lemma lem5115086 {A : Type'} (s : A -> Prop) (h1 : term187 A s) (h2 : term189 A s) : term187 A s.
Proof. exact (@lem5115084 A s h1 (@lem5115085 A s h2)). Qed.
Lemma lem5115087 {A : Type'} (s : A -> Prop) (h1 : term189 A s) : term189 A s.
Proof. exact (fun h0 : term187 A s => @lem5115086 A s h0 h1). Qed.
Lemma lem5115088 {A : Type'} (s : A -> Prop) : term191 A s.
Proof. exact (fun h0 : term189 A s => @lem5115087 A s h0). Qed.
Lemma lem5115091 {A : Type'} (s : A -> Prop) : term189 A s.
Proof. exact (@lem5115088 A s (@lem5115080 A s)). Qed.
Lemma lem5115092 {A : Type'} (s : A -> Prop) : term189 A s.
Proof. exact (@lem5115091 A s). Qed.
Lemma lem5115098 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5115099 {A : Type'} (s : A -> Prop) : (term187 A s) = (term192 A s).
Proof. exact (@lem5115098 (term188 A s)). Qed.
Lemma lem5115101 (t : Prop) : (term193 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5115102 {A : Type'} (s : A -> Prop) : (term192 A s) = (term185 A s).
Proof. exact (@lem5115101 (term185 A s)). Qed.
Lemma lem5115107 {A : Type'} (s : A -> Prop) : (term187 A s) = (term185 A s).
Proof. exact (TRANS (@lem5115099 A s) (@lem5115102 A s)). Qed.
Lemma lem5115172 {A : Type'} : (term194 A) = (term195 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5115107 A s)). Qed.
Lemma lem5115173 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5115182 {A : Type'} : (term196 A) = (term197 A).
Proof. exact (MK_COMB (@lem5115173 A) (@lem5115172 A)). Qed.
Lemma lem5115187 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : ((x x') = (z x')) = ((x x') = (z x')).
Proof. exact (eq_refl ((x x') = (z x'))). Qed.
Lemma lem5115188 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term168 A x z) = (term168 A x z).
Proof. exact (fun_ext (fun x' : A => @lem5115187 A x z x')). Qed.
Lemma lem5115189 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5115190 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term169 A x z) = (term169 A x z).
Proof. exact (MK_COMB (@lem5115189 A) (@lem5115188 A x z)). Qed.
Lemma lem5115191 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5115192 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term170 A x z) = (term170 A x z).
Proof. exact (MK_COMB (@lem5115191) (@lem5115190 A x z)). Qed.
Lemma lem5115197 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term160 A x z x') = (term160 A x z x').
Proof. exact (eq_refl (term160 A x z x')). Qed.
Lemma lem5115198 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term162 A x z) = (term162 A x z).
Proof. exact (fun_ext (fun x' : A => @lem5115197 A x z x')). Qed.
Lemma lem5115199 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5115200 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term163 A x z) = (term163 A x z).
Proof. exact (MK_COMB (@lem5115199 A) (@lem5115198 A x z)). Qed.
Lemma lem5115201 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115202 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term164 A x z) = (term164 A x z).
Proof. exact (MK_COMB (@lem5115201) (@lem5115200 A x z)). Qed.
Lemma lem5115203 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term171 A x z) = (term171 A x z).
Proof. exact (MK_COMB (@lem5115202 A x z) (@lem5115192 A x z)). Qed.
Lemma lem5115208 {A : Type'} (z : A -> Prop) (s : A -> Prop) (x : A) : (term160 A z s x) = (term160 A z s x).
Proof. exact (eq_refl (term160 A z s x)). Qed.
Lemma lem5115209 {A : Type'} (z : A -> Prop) (s : A -> Prop) : (term162 A z s) = (term162 A z s).
Proof. exact (fun_ext (fun x : A => @lem5115208 A z s x)). Qed.
Lemma lem5115210 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5115211 {A : Type'} (z : A -> Prop) (s : A -> Prop) : (term163 A z s) = (term163 A z s).
Proof. exact (MK_COMB (@lem5115210 A) (@lem5115209 A z s)). Qed.
Lemma lem5115216 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : ((y x) = (z x)) = ((y x) = (z x)).
Proof. exact (eq_refl ((y x) = (z x))). Qed.
Lemma lem5115217 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term168 A y z) = (term168 A y z).
Proof. exact (fun_ext (fun x : A => @lem5115216 A y z x)). Qed.
Lemma lem5115218 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5115219 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term169 A y z) = (term169 A y z).
Proof. exact (MK_COMB (@lem5115218 A) (@lem5115217 A y z)). Qed.
Lemma lem5115220 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5115221 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term170 A y z) = (term170 A y z).
Proof. exact (MK_COMB (@lem5115220) (@lem5115219 A y z)). Qed.
Lemma lem5115226 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term160 A y z x) = (term160 A y z x).
Proof. exact (eq_refl (term160 A y z x)). Qed.
Lemma lem5115227 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term162 A y z) = (term162 A y z).
Proof. exact (fun_ext (fun x : A => @lem5115226 A y z x)). Qed.
Lemma lem5115228 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5115229 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term163 A y z) = (term163 A y z).
Proof. exact (MK_COMB (@lem5115228 A) (@lem5115227 A y z)). Qed.
Lemma lem5115230 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115231 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term164 A y z) = (term164 A y z).
Proof. exact (MK_COMB (@lem5115230) (@lem5115229 A y z)). Qed.
Lemma lem5115232 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term171 A y z) = (term171 A y z).
Proof. exact (MK_COMB (@lem5115231 A y z) (@lem5115221 A y z)). Qed.
Lemma lem5115237 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A) : (term160 A y s x) = (term160 A y s x).
Proof. exact (eq_refl (term160 A y s x)). Qed.
Lemma lem5115238 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term162 A y s) = (term162 A y s).
Proof. exact (fun_ext (fun x : A => @lem5115237 A y s x)). Qed.
Lemma lem5115239 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5115240 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term163 A y s) = (term163 A y s).
Proof. exact (MK_COMB (@lem5115239 A) (@lem5115238 A y s)). Qed.
Lemma lem5115245 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : ((x x') = (y x')) = ((x x') = (y x')).
Proof. exact (eq_refl ((x x') = (y x'))). Qed.
Lemma lem5115246 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term168 A x y) = (term168 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5115245 A x y x')). Qed.
Lemma lem5115247 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5115248 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term169 A x y) = (term169 A x y).
Proof. exact (MK_COMB (@lem5115247 A) (@lem5115246 A x y)). Qed.
Lemma lem5115249 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5115250 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term170 A x y) = (term170 A x y).
Proof. exact (MK_COMB (@lem5115249) (@lem5115248 A x y)). Qed.
Lemma lem5115255 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term160 A x y x') = (term160 A x y x').
Proof. exact (eq_refl (term160 A x y x')). Qed.
Lemma lem5115256 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term162 A x y) = (term162 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5115255 A x y x')). Qed.
Lemma lem5115257 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5115258 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term163 A x y) = (term163 A x y).
Proof. exact (MK_COMB (@lem5115257 A) (@lem5115256 A x y)). Qed.
Lemma lem5115259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115260 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term164 A x y) = (term164 A x y).
Proof. exact (MK_COMB (@lem5115259) (@lem5115258 A x y)). Qed.
Lemma lem5115261 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term171 A x y) = (term171 A x y).
Proof. exact (MK_COMB (@lem5115260 A x y) (@lem5115250 A x y)). Qed.
Lemma lem5115262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115263 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term172 A x y) = (term172 A x y).
Proof. exact (MK_COMB (@lem5115262) (@lem5115261 A x y)). Qed.
Lemma lem5115264 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term173 A x y s) = (term173 A x y s).
Proof. exact (MK_COMB (@lem5115263 A x y) (@lem5115240 A y s)). Qed.
Lemma lem5115265 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115266 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term174 A x y s) = (term174 A x y s).
Proof. exact (MK_COMB (@lem5115265) (@lem5115264 A x y s)). Qed.
Lemma lem5115267 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term175 A x s y z) = (term175 A x s y z).
Proof. exact (MK_COMB (@lem5115266 A x y s) (@lem5115232 A y z)). Qed.
Lemma lem5115268 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115269 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term176 A x s y z) = (term176 A x s y z).
Proof. exact (MK_COMB (@lem5115268) (@lem5115267 A x s y z)). Qed.
Lemma lem5115270 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term177 A x y z s) = (term177 A x y z s).
Proof. exact (MK_COMB (@lem5115269 A x s y z) (@lem5115211 A z s)). Qed.
Lemma lem5115271 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5115272 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term178 A x y z s) = (term178 A x y z s).
Proof. exact (MK_COMB (@lem5115271) (@lem5115270 A x y z s)). Qed.
Lemma lem5115273 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term179 A y s x z) = (term179 A y s x z).
Proof. exact (MK_COMB (@lem5115272 A x y z s) (@lem5115203 A x z)). Qed.
Lemma lem5115274 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) : (term180 A y s x) = (term180 A y s x).
Proof. exact (fun_ext (fun z : A -> Prop => @lem5115273 A y s x z)). Qed.
Lemma lem5115275 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5115276 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) : (term181 A y s x) = (term181 A y s x).
Proof. exact (MK_COMB (@lem5115275 A) (@lem5115274 A y s x)). Qed.
Lemma lem5115277 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term182 A s x) = (term182 A s x).
Proof. exact (fun_ext (fun y : A -> Prop => @lem5115276 A y s x)). Qed.
Lemma lem5115278 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5115279 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term183 A s x) = (term183 A s x).
Proof. exact (MK_COMB (@lem5115278 A) (@lem5115277 A s x)). Qed.
Lemma lem5115280 {A : Type'} (s : A -> Prop) : (term184 A s) = (term184 A s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem5115279 A s x)). Qed.
Lemma lem5115281 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5115282 {A : Type'} (s : A -> Prop) : (term185 A s) = (term185 A s).
Proof. exact (MK_COMB (@lem5115281 A) (@lem5115280 A s)). Qed.
Lemma lem5115283 {A : Type'} : (term195 A) = (term195 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5115282 A s)). Qed.
Lemma lem5115284 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5115285 {A : Type'} : (term197 A) = (term197 A).
Proof. exact (MK_COMB (@lem5115284 A) (@lem5115283 A)). Qed.
Lemma lem5115384 {A : Type'} : (term196 A) = (term197 A).
Proof. exact (TRANS (@lem5115182 A) (@lem5115285 A)). Qed.
Lemma lem5115385 {A : Type'} : (term197 A) = (term196 A).
Proof. exact (SYM (@lem5115384 A)). Qed.
Lemma lem5115386 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (h1 : term177 A x y z s) : term177 A x y z s.
Proof. exact (h1). Qed.
Lemma lem5115388 (p : Prop) : p = (term186 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5115389 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term171 A x z) = (term198 A x z).
Proof. exact (@lem5115388 (term171 A x z)). Qed.
Lemma lem5115390 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term198 A x z) = (term171 A x z).
Proof. exact (SYM (@lem5115389 A x z)). Qed.
Lemma lem5115391 {A : Type'} (x : A -> Prop) (z : A -> Prop) (h1 : term199 A x z) : term199 A x z.
Proof. exact (h1). Qed.
Lemma lem5115398 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term160 A x y x') = (term200 A x y x').
Proof. exact (@lem17265 (x x') (y x')). Qed.
Lemma lem5115399 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term162 A x y) = (term201 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5115398 A x y x')). Qed.
Lemma lem5115400 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5115401 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term163 A x y) = (term202 A x y).
Proof. exact (MK_COMB (@lem5115400 A) (@lem5115399 A x y)). Qed.
Lemma lem5115416 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term203 A x y x') = (term204 A x y x').
Proof. exact (@lem17646 (x x') (y x')). Qed.
Lemma lem5115417 {A : Type'} (P : A -> Prop) : (term205 A P) = (term206 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5115418 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term170 A x y) = (term207 A x y).
Proof. exact (@lem5115417 A (term168 A x y)). Qed.
Lemma lem5115419 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term208 A x y x') = ((x x') = (y x')).
Proof. exact (eq_refl (term208 A x y x')). Qed.
Lemma lem5115420 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5115421 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term209 A x y x') = (term203 A x y x').
Proof. exact (MK_COMB (@lem5115420) (@lem5115419 A x y x')). Qed.
Lemma lem5115422 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term209 A x y x') = (term204 A x y x').
Proof. exact (TRANS (@lem5115421 A x y x') (@lem5115416 A x y x')). Qed.
Lemma lem5115423 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term210 A x y) = (term211 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5115422 A x y x')). Qed.
Lemma lem5115424 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115425 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term207 A x y) = (term212 A x y).
Proof. exact (MK_COMB (@lem5115424 A) (@lem5115423 A x y)). Qed.
Lemma lem5115426 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term170 A x y) = (term212 A x y).
Proof. exact (TRANS (@lem5115418 A x y) (@lem5115425 A x y)). Qed.
Lemma lem5115427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115428 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term164 A x y) = (term213 A x y).
Proof. exact (MK_COMB (@lem5115427) (@lem5115401 A x y)). Qed.
Lemma lem5115429 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term171 A x y) = (term214 A x y).
Proof. exact (MK_COMB (@lem5115428 A x y) (@lem5115426 A x y)). Qed.
Lemma lem5115436 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A) : (term160 A y s x) = (term200 A y s x).
Proof. exact (@lem17265 (y x) (s x)). Qed.
Lemma lem5115437 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term162 A y s) = (term201 A y s).
Proof. exact (fun_ext (fun x : A => @lem5115436 A y s x)). Qed.
Lemma lem5115438 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5115439 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term163 A y s) = (term202 A y s).
Proof. exact (MK_COMB (@lem5115438 A) (@lem5115437 A y s)). Qed.
Lemma lem5115440 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115441 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term172 A x y) = (term215 A x y).
Proof. exact (MK_COMB (@lem5115440) (@lem5115429 A x y)). Qed.
Lemma lem5115442 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term173 A x y s) = (term216 A x y s).
Proof. exact (MK_COMB (@lem5115441 A x y) (@lem5115439 A y s)). Qed.
Lemma lem5115449 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term160 A y z x) = (term200 A y z x).
Proof. exact (@lem17265 (y x) (z x)). Qed.
Lemma lem5115450 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term162 A y z) = (term201 A y z).
Proof. exact (fun_ext (fun x : A => @lem5115449 A y z x)). Qed.
Lemma lem5115451 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5115452 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term163 A y z) = (term202 A y z).
Proof. exact (MK_COMB (@lem5115451 A) (@lem5115450 A y z)). Qed.
Lemma lem5115467 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term203 A y z x) = (term204 A y z x).
Proof. exact (@lem17646 (y x) (z x)). Qed.
Lemma lem5115468 {A : Type'} (P : A -> Prop) : (term205 A P) = (term206 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5115469 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term170 A y z) = (term207 A y z).
Proof. exact (@lem5115468 A (term168 A y z)). Qed.
Lemma lem5115470 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term208 A y z x) = ((y x) = (z x)).
Proof. exact (eq_refl (term208 A y z x)). Qed.
Lemma lem5115471 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5115472 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term209 A y z x) = (term203 A y z x).
Proof. exact (MK_COMB (@lem5115471) (@lem5115470 A y z x)). Qed.
Lemma lem5115473 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term209 A y z x) = (term204 A y z x).
Proof. exact (TRANS (@lem5115472 A y z x) (@lem5115467 A y z x)). Qed.
Lemma lem5115474 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term210 A y z) = (term211 A y z).
Proof. exact (fun_ext (fun x : A => @lem5115473 A y z x)). Qed.
Lemma lem5115475 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115476 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term207 A y z) = (term212 A y z).
Proof. exact (MK_COMB (@lem5115475 A) (@lem5115474 A y z)). Qed.
Lemma lem5115477 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term170 A y z) = (term212 A y z).
Proof. exact (TRANS (@lem5115469 A y z) (@lem5115476 A y z)). Qed.
Lemma lem5115478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115479 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term164 A y z) = (term213 A y z).
Proof. exact (MK_COMB (@lem5115478) (@lem5115452 A y z)). Qed.
Lemma lem5115480 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term171 A y z) = (term214 A y z).
Proof. exact (MK_COMB (@lem5115479 A y z) (@lem5115477 A y z)). Qed.
Lemma lem5115481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115482 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term174 A x y s) = (term217 A x y s).
Proof. exact (MK_COMB (@lem5115481) (@lem5115442 A x y s)). Qed.
Lemma lem5115483 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term175 A x s y z) = (term218 A x s y z).
Proof. exact (MK_COMB (@lem5115482 A x y s) (@lem5115480 A y z)). Qed.
Lemma lem5115490 {A : Type'} (z : A -> Prop) (s : A -> Prop) (x : A) : (term160 A z s x) = (term200 A z s x).
Proof. exact (@lem17265 (z x) (s x)). Qed.
Lemma lem5115491 {A : Type'} (z : A -> Prop) (s : A -> Prop) : (term162 A z s) = (term201 A z s).
Proof. exact (fun_ext (fun x : A => @lem5115490 A z s x)). Qed.
Lemma lem5115492 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5115493 {A : Type'} (z : A -> Prop) (s : A -> Prop) : (term163 A z s) = (term202 A z s).
Proof. exact (MK_COMB (@lem5115492 A) (@lem5115491 A z s)). Qed.
Lemma lem5115494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115495 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term176 A x s y z) = (term219 A x s y z).
Proof. exact (MK_COMB (@lem5115494) (@lem5115483 A x s y z)). Qed.
Lemma lem5115496 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term177 A x y z s) = (term220 A x y z s).
Proof. exact (MK_COMB (@lem5115495 A x s y z) (@lem5115493 A z s)). Qed.
Lemma lem5115530 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5115531 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (@lem5115530 A P Q). Qed.
Lemma lem5115532 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term223 A x y) = (term224 A x y).
Proof. exact (@lem5115531 A (term225 A x y) (term226 A x y)). Qed.
Lemma lem5115533 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term227 A x y x') = (term228 A x y x').
Proof. exact (eq_refl (term227 A x y x')). Qed.
Lemma lem5115534 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5115535 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term229 A x y x') = (term230 A x y x').
Proof. exact (MK_COMB (@lem5115534) (@lem5115533 A x y x')). Qed.
Lemma lem5115536 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term231 A x y x') = (term232 A x y x').
Proof. exact (eq_refl (term231 A x y x')). Qed.
Lemma lem5115537 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term233 A x y x') = (term204 A x y x').
Proof. exact (MK_COMB (@lem5115535 A x y x') (@lem5115536 A x y x')). Qed.
Lemma lem5115538 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term234 A x y) = (term211 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5115537 A x y x')). Qed.
Lemma lem5115539 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115540 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term223 A x y) = (term212 A x y).
Proof. exact (MK_COMB (@lem5115539 A) (@lem5115538 A x y)). Qed.
Lemma lem5115541 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5115542 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term235 A x y) = (term236 A x y).
Proof. exact (MK_COMB (@lem5115541) (@lem5115540 A x y)). Qed.
Lemma lem5115543 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term227 A x y x') = (term228 A x y x').
Proof. exact (eq_refl (term227 A x y x')). Qed.
Lemma lem5115544 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term237 A x y) = (term225 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5115543 A x y x')). Qed.
Lemma lem5115545 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115546 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term238 A x y) = (term239 A x y).
Proof. exact (MK_COMB (@lem5115545 A) (@lem5115544 A x y)). Qed.
Lemma lem5115547 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5115548 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term240 A x y) = (term241 A x y).
Proof. exact (MK_COMB (@lem5115547) (@lem5115546 A x y)). Qed.
Lemma lem5115549 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term231 A x y x') = (term232 A x y x').
Proof. exact (eq_refl (term231 A x y x')). Qed.
Lemma lem5115550 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term242 A x y) = (term226 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5115549 A x y x')). Qed.
Lemma lem5115551 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115552 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term243 A x y) = (term244 A x y).
Proof. exact (MK_COMB (@lem5115551 A) (@lem5115550 A x y)). Qed.
Lemma lem5115553 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term224 A x y) = (term245 A x y).
Proof. exact (MK_COMB (@lem5115548 A x y) (@lem5115552 A x y)). Qed.
Lemma lem5115554 {A : Type'} (x : A -> Prop) (y : A -> Prop) : ((term223 A x y) = (term224 A x y)) = ((term212 A x y) = (term245 A x y)).
Proof. exact (MK_COMB (@lem5115542 A x y) (@lem5115553 A x y)). Qed.
Lemma lem5115555 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term212 A x y) = (term245 A x y).
Proof. exact (EQ_MP (@lem5115554 A x y) (@lem5115532 A x y)). Qed.
Lemma lem5115616 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term213 A x y) = (term213 A x y).
Proof. exact (eq_refl (term213 A x y)). Qed.
Lemma lem5115617 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term214 A x y) = (term246 A x y).
Proof. exact (MK_COMB (@lem5115616 A x y) (@lem5115555 A x y)). Qed.
Lemma lem5115618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115619 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term215 A x y) = (term247 A x y).
Proof. exact (MK_COMB (@lem5115618) (@lem5115617 A x y)). Qed.
Lemma lem5115652 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term202 A y s) = (term202 A y s).
Proof. exact (eq_refl (term202 A y s)). Qed.
Lemma lem5115653 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term216 A x y s) = (term248 A x y s).
Proof. exact (MK_COMB (@lem5115619 A x y) (@lem5115652 A y s)). Qed.
Lemma lem5115654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115655 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term217 A x y s) = (term249 A x y s).
Proof. exact (MK_COMB (@lem5115654) (@lem5115653 A x y s)). Qed.
Lemma lem5115689 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5115690 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (@lem5115689 A P Q). Qed.
Lemma lem5115691 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term223 A y z) = (term224 A y z).
Proof. exact (@lem5115690 A (term225 A y z) (term226 A y z)). Qed.
Lemma lem5115692 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term227 A y z x) = (term228 A y z x).
Proof. exact (eq_refl (term227 A y z x)). Qed.
Lemma lem5115693 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5115694 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term229 A y z x) = (term230 A y z x).
Proof. exact (MK_COMB (@lem5115693) (@lem5115692 A y z x)). Qed.
Lemma lem5115695 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term231 A y z x) = (term232 A y z x).
Proof. exact (eq_refl (term231 A y z x)). Qed.
Lemma lem5115696 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term233 A y z x) = (term204 A y z x).
Proof. exact (MK_COMB (@lem5115694 A y z x) (@lem5115695 A y z x)). Qed.
Lemma lem5115697 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term234 A y z) = (term211 A y z).
Proof. exact (fun_ext (fun x : A => @lem5115696 A y z x)). Qed.
Lemma lem5115698 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115699 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term223 A y z) = (term212 A y z).
Proof. exact (MK_COMB (@lem5115698 A) (@lem5115697 A y z)). Qed.
Lemma lem5115700 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5115701 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term235 A y z) = (term236 A y z).
Proof. exact (MK_COMB (@lem5115700) (@lem5115699 A y z)). Qed.
Lemma lem5115702 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term227 A y z x) = (term228 A y z x).
Proof. exact (eq_refl (term227 A y z x)). Qed.
Lemma lem5115703 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term237 A y z) = (term225 A y z).
Proof. exact (fun_ext (fun x : A => @lem5115702 A y z x)). Qed.
Lemma lem5115704 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115705 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term238 A y z) = (term239 A y z).
Proof. exact (MK_COMB (@lem5115704 A) (@lem5115703 A y z)). Qed.
Lemma lem5115706 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5115707 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term240 A y z) = (term241 A y z).
Proof. exact (MK_COMB (@lem5115706) (@lem5115705 A y z)). Qed.
Lemma lem5115708 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term231 A y z x) = (term232 A y z x).
Proof. exact (eq_refl (term231 A y z x)). Qed.
Lemma lem5115709 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term242 A y z) = (term226 A y z).
Proof. exact (fun_ext (fun x : A => @lem5115708 A y z x)). Qed.
Lemma lem5115710 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115711 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term243 A y z) = (term244 A y z).
Proof. exact (MK_COMB (@lem5115710 A) (@lem5115709 A y z)). Qed.
Lemma lem5115712 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term224 A y z) = (term245 A y z).
Proof. exact (MK_COMB (@lem5115707 A y z) (@lem5115711 A y z)). Qed.
Lemma lem5115713 {A : Type'} (y : A -> Prop) (z : A -> Prop) : ((term223 A y z) = (term224 A y z)) = ((term212 A y z) = (term245 A y z)).
Proof. exact (MK_COMB (@lem5115701 A y z) (@lem5115712 A y z)). Qed.
Lemma lem5115714 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term212 A y z) = (term245 A y z).
Proof. exact (EQ_MP (@lem5115713 A y z) (@lem5115691 A y z)). Qed.
Lemma lem5115775 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term213 A y z) = (term213 A y z).
Proof. exact (eq_refl (term213 A y z)). Qed.
Lemma lem5115776 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term214 A y z) = (term246 A y z).
Proof. exact (MK_COMB (@lem5115775 A y z) (@lem5115714 A y z)). Qed.
Lemma lem5115777 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term218 A x s y z) = (term250 A x s y z).
Proof. exact (MK_COMB (@lem5115655 A x y s) (@lem5115776 A y z)). Qed.
Lemma lem5115778 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115779 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term219 A x s y z) = (term251 A x s y z).
Proof. exact (MK_COMB (@lem5115778) (@lem5115777 A x s y z)). Qed.
Lemma lem5115812 {A : Type'} (z : A -> Prop) (s : A -> Prop) : (term202 A z s) = (term202 A z s).
Proof. exact (eq_refl (term202 A z s)). Qed.
Lemma lem5115813 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term220 A x y z s) = (term252 A x y z s).
Proof. exact (MK_COMB (@lem5115779 A x s y z) (@lem5115812 A z s)). Qed.
Lemma lem5115815 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term222 A P Q) = (term221 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5115816 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term222 A P Q) = (term221 A P Q).
Proof. exact (@lem5115815 A P Q). Qed.
Lemma lem5115817 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term224 A x y) = (term223 A x y).
Proof. exact (@lem5115816 A (term225 A x y) (term226 A x y)). Qed.
Lemma lem5115818 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term227 A x y x') = (term228 A x y x').
Proof. exact (eq_refl (term227 A x y x')). Qed.
Lemma lem5115819 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term237 A x y) = (term225 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5115818 A x y x')). Qed.
Lemma lem5115820 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115821 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term238 A x y) = (term239 A x y).
Proof. exact (MK_COMB (@lem5115820 A) (@lem5115819 A x y)). Qed.
Lemma lem5115822 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5115823 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term240 A x y) = (term241 A x y).
Proof. exact (MK_COMB (@lem5115822) (@lem5115821 A x y)). Qed.
Lemma lem5115824 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term231 A x y x') = (term232 A x y x').
Proof. exact (eq_refl (term231 A x y x')). Qed.
Lemma lem5115825 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term242 A x y) = (term226 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5115824 A x y x')). Qed.
Lemma lem5115826 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115827 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term243 A x y) = (term244 A x y).
Proof. exact (MK_COMB (@lem5115826 A) (@lem5115825 A x y)). Qed.
Lemma lem5115828 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term224 A x y) = (term245 A x y).
Proof. exact (MK_COMB (@lem5115823 A x y) (@lem5115827 A x y)). Qed.
Lemma lem5115829 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5115830 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term253 A x y) = (term254 A x y).
Proof. exact (MK_COMB (@lem5115829) (@lem5115828 A x y)). Qed.
Lemma lem5115831 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term227 A x y x') = (term228 A x y x').
Proof. exact (eq_refl (term227 A x y x')). Qed.
Lemma lem5115832 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5115833 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term229 A x y x') = (term230 A x y x').
Proof. exact (MK_COMB (@lem5115832) (@lem5115831 A x y x')). Qed.
Lemma lem5115834 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term231 A x y x') = (term232 A x y x').
Proof. exact (eq_refl (term231 A x y x')). Qed.
Lemma lem5115835 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term233 A x y x') = (term204 A x y x').
Proof. exact (MK_COMB (@lem5115833 A x y x') (@lem5115834 A x y x')). Qed.
Lemma lem5115836 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term234 A x y) = (term211 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5115835 A x y x')). Qed.
Lemma lem5115837 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115838 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term223 A x y) = (term212 A x y).
Proof. exact (MK_COMB (@lem5115837 A) (@lem5115836 A x y)). Qed.
Lemma lem5115839 {A : Type'} (x : A -> Prop) (y : A -> Prop) : ((term224 A x y) = (term223 A x y)) = ((term245 A x y) = (term212 A x y)).
Proof. exact (MK_COMB (@lem5115830 A x y) (@lem5115838 A x y)). Qed.
Lemma lem5115840 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term245 A x y) = (term212 A x y).
Proof. exact (EQ_MP (@lem5115839 A x y) (@lem5115817 A x y)). Qed.
Lemma lem5115841 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term213 A x y) = (term213 A x y).
Proof. exact (eq_refl (term213 A x y)). Qed.
Lemma lem5115842 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term246 A x y) = (term214 A x y).
Proof. exact (MK_COMB (@lem5115841 A x y) (@lem5115840 A x y)). Qed.
Lemma lem5115844 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5115845 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (@lem5115844 A P Q). Qed.
Lemma lem5115846 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term257 A x y) = (term258 A x y).
Proof. exact (@lem5115845 A (term202 A x y) (term211 A x y)). Qed.
Lemma lem5115847 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term259 A x y x') = (term204 A x y x').
Proof. exact (eq_refl (term259 A x y x')). Qed.
Lemma lem5115848 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term260 A x y) = (term211 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5115847 A x y x')). Qed.
Lemma lem5115849 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115850 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term261 A x y) = (term212 A x y).
Proof. exact (MK_COMB (@lem5115849 A) (@lem5115848 A x y)). Qed.
Lemma lem5115851 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term213 A x y) = (term213 A x y).
Proof. exact (eq_refl (term213 A x y)). Qed.
Lemma lem5115852 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term257 A x y) = (term214 A x y).
Proof. exact (MK_COMB (@lem5115851 A x y) (@lem5115850 A x y)). Qed.
Lemma lem5115853 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5115854 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term262 A x y) = (term263 A x y).
Proof. exact (MK_COMB (@lem5115853) (@lem5115852 A x y)). Qed.
Lemma lem5115855 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term259 A x y x') = (term204 A x y x').
Proof. exact (eq_refl (term259 A x y x')). Qed.
Lemma lem5115856 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term213 A x y) = (term213 A x y).
Proof. exact (eq_refl (term213 A x y)). Qed.
Lemma lem5115857 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term264 A x y x') = (term265 A x y x').
Proof. exact (MK_COMB (@lem5115856 A x y) (@lem5115855 A x y x')). Qed.
Lemma lem5115858 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term266 A x y) = (term267 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5115857 A x y x')). Qed.
Lemma lem5115859 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115860 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term258 A x y) = (term268 A x y).
Proof. exact (MK_COMB (@lem5115859 A) (@lem5115858 A x y)). Qed.
Lemma lem5115861 {A : Type'} (x : A -> Prop) (y : A -> Prop) : ((term257 A x y) = (term258 A x y)) = ((term214 A x y) = (term268 A x y)).
Proof. exact (MK_COMB (@lem5115854 A x y) (@lem5115860 A x y)). Qed.
Lemma lem5115862 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term214 A x y) = (term268 A x y).
Proof. exact (EQ_MP (@lem5115861 A x y) (@lem5115846 A x y)). Qed.
Lemma lem5115863 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term246 A x y) = (term268 A x y).
Proof. exact (TRANS (@lem5115842 A x y) (@lem5115862 A x y)). Qed.
Lemma lem5115864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115865 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term247 A x y) = (term269 A x y).
Proof. exact (MK_COMB (@lem5115864) (@lem5115863 A x y)). Qed.
Lemma lem5115866 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term202 A y s) = (term202 A y s).
Proof. exact (eq_refl (term202 A y s)). Qed.
Lemma lem5115867 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term248 A x y s) = (term270 A x y s).
Proof. exact (MK_COMB (@lem5115865 A x y) (@lem5115866 A y s)). Qed.
Lemma lem5115869 {A : Type'} (P : A -> Prop) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5115870 {A : Type'} (P : A -> Prop) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (@lem5115869 A P Q). Qed.
Lemma lem5115871 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term273 A x y s) = (term274 A x y s).
Proof. exact (@lem5115870 A (term267 A x y) (term202 A y s)). Qed.
Lemma lem5115872 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term275 A x y x') = (term265 A x y x').
Proof. exact (eq_refl (term275 A x y x')). Qed.
Lemma lem5115873 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term276 A x y) = (term267 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5115872 A x y x')). Qed.
Lemma lem5115874 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115875 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term277 A x y) = (term268 A x y).
Proof. exact (MK_COMB (@lem5115874 A) (@lem5115873 A x y)). Qed.
Lemma lem5115876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115877 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term278 A x y) = (term269 A x y).
Proof. exact (MK_COMB (@lem5115876) (@lem5115875 A x y)). Qed.
Lemma lem5115878 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term202 A y s) = (term202 A y s).
Proof. exact (eq_refl (term202 A y s)). Qed.
Lemma lem5115879 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term273 A x y s) = (term270 A x y s).
Proof. exact (MK_COMB (@lem5115877 A x y) (@lem5115878 A y s)). Qed.
Lemma lem5115880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5115881 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term279 A x y s) = (term280 A x y s).
Proof. exact (MK_COMB (@lem5115880) (@lem5115879 A x y s)). Qed.
Lemma lem5115882 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term275 A x y x') = (term265 A x y x').
Proof. exact (eq_refl (term275 A x y x')). Qed.
Lemma lem5115883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115884 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term281 A x y x') = (term282 A x y x').
Proof. exact (MK_COMB (@lem5115883) (@lem5115882 A x y x')). Qed.
Lemma lem5115885 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term202 A y s) = (term202 A y s).
Proof. exact (eq_refl (term202 A y s)). Qed.
Lemma lem5115886 {A : Type'} (x : A -> Prop) (x' : A) (y : A -> Prop) (s : A -> Prop) : (term283 A x x' y s) = (term284 A x x' y s).
Proof. exact (MK_COMB (@lem5115884 A x y x') (@lem5115885 A y s)). Qed.
Lemma lem5115887 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term285 A x y s) = (term286 A x y s).
Proof. exact (fun_ext (fun x' : A => @lem5115886 A x x' y s)). Qed.
Lemma lem5115888 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115889 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term274 A x y s) = (term287 A x y s).
Proof. exact (MK_COMB (@lem5115888 A) (@lem5115887 A x y s)). Qed.
Lemma lem5115890 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : ((term273 A x y s) = (term274 A x y s)) = ((term270 A x y s) = (term287 A x y s)).
Proof. exact (MK_COMB (@lem5115881 A x y s) (@lem5115889 A x y s)). Qed.
Lemma lem5115891 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term270 A x y s) = (term287 A x y s).
Proof. exact (EQ_MP (@lem5115890 A x y s) (@lem5115871 A x y s)). Qed.
Lemma lem5115892 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term248 A x y s) = (term287 A x y s).
Proof. exact (TRANS (@lem5115867 A x y s) (@lem5115891 A x y s)). Qed.
Lemma lem5115893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115894 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term249 A x y s) = (term288 A x y s).
Proof. exact (MK_COMB (@lem5115893) (@lem5115892 A x y s)). Qed.
Lemma lem5115896 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term222 A P Q) = (term221 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5115897 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term222 A P Q) = (term221 A P Q).
Proof. exact (@lem5115896 A P Q). Qed.
Lemma lem5115898 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term224 A y z) = (term223 A y z).
Proof. exact (@lem5115897 A (term225 A y z) (term226 A y z)). Qed.
Lemma lem5115899 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term227 A y z x) = (term228 A y z x).
Proof. exact (eq_refl (term227 A y z x)). Qed.
Lemma lem5115900 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term237 A y z) = (term225 A y z).
Proof. exact (fun_ext (fun x : A => @lem5115899 A y z x)). Qed.
Lemma lem5115901 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115902 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term238 A y z) = (term239 A y z).
Proof. exact (MK_COMB (@lem5115901 A) (@lem5115900 A y z)). Qed.
Lemma lem5115903 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5115904 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term240 A y z) = (term241 A y z).
Proof. exact (MK_COMB (@lem5115903) (@lem5115902 A y z)). Qed.
Lemma lem5115905 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term231 A y z x) = (term232 A y z x).
Proof. exact (eq_refl (term231 A y z x)). Qed.
Lemma lem5115906 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term242 A y z) = (term226 A y z).
Proof. exact (fun_ext (fun x : A => @lem5115905 A y z x)). Qed.
Lemma lem5115907 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115908 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term243 A y z) = (term244 A y z).
Proof. exact (MK_COMB (@lem5115907 A) (@lem5115906 A y z)). Qed.
Lemma lem5115909 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term224 A y z) = (term245 A y z).
Proof. exact (MK_COMB (@lem5115904 A y z) (@lem5115908 A y z)). Qed.
Lemma lem5115910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5115911 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term253 A y z) = (term254 A y z).
Proof. exact (MK_COMB (@lem5115910) (@lem5115909 A y z)). Qed.
Lemma lem5115912 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term227 A y z x) = (term228 A y z x).
Proof. exact (eq_refl (term227 A y z x)). Qed.
Lemma lem5115913 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5115914 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term229 A y z x) = (term230 A y z x).
Proof. exact (MK_COMB (@lem5115913) (@lem5115912 A y z x)). Qed.
Lemma lem5115915 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term231 A y z x) = (term232 A y z x).
Proof. exact (eq_refl (term231 A y z x)). Qed.
Lemma lem5115916 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term233 A y z x) = (term204 A y z x).
Proof. exact (MK_COMB (@lem5115914 A y z x) (@lem5115915 A y z x)). Qed.
Lemma lem5115917 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term234 A y z) = (term211 A y z).
Proof. exact (fun_ext (fun x : A => @lem5115916 A y z x)). Qed.
Lemma lem5115918 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115919 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term223 A y z) = (term212 A y z).
Proof. exact (MK_COMB (@lem5115918 A) (@lem5115917 A y z)). Qed.
Lemma lem5115920 {A : Type'} (y : A -> Prop) (z : A -> Prop) : ((term224 A y z) = (term223 A y z)) = ((term245 A y z) = (term212 A y z)).
Proof. exact (MK_COMB (@lem5115911 A y z) (@lem5115919 A y z)). Qed.
Lemma lem5115921 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term245 A y z) = (term212 A y z).
Proof. exact (EQ_MP (@lem5115920 A y z) (@lem5115898 A y z)). Qed.
Lemma lem5115922 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term213 A y z) = (term213 A y z).
Proof. exact (eq_refl (term213 A y z)). Qed.
Lemma lem5115923 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term246 A y z) = (term214 A y z).
Proof. exact (MK_COMB (@lem5115922 A y z) (@lem5115921 A y z)). Qed.
Lemma lem5115925 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5115926 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (@lem5115925 A P Q). Qed.
Lemma lem5115927 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term257 A y z) = (term258 A y z).
Proof. exact (@lem5115926 A (term202 A y z) (term211 A y z)). Qed.
Lemma lem5115928 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term259 A y z x) = (term204 A y z x).
Proof. exact (eq_refl (term259 A y z x)). Qed.
Lemma lem5115929 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term260 A y z) = (term211 A y z).
Proof. exact (fun_ext (fun x : A => @lem5115928 A y z x)). Qed.
Lemma lem5115930 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115931 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term261 A y z) = (term212 A y z).
Proof. exact (MK_COMB (@lem5115930 A) (@lem5115929 A y z)). Qed.
Lemma lem5115932 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term213 A y z) = (term213 A y z).
Proof. exact (eq_refl (term213 A y z)). Qed.
Lemma lem5115933 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term257 A y z) = (term214 A y z).
Proof. exact (MK_COMB (@lem5115932 A y z) (@lem5115931 A y z)). Qed.
Lemma lem5115934 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5115935 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term262 A y z) = (term263 A y z).
Proof. exact (MK_COMB (@lem5115934) (@lem5115933 A y z)). Qed.
Lemma lem5115936 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term259 A y z x) = (term204 A y z x).
Proof. exact (eq_refl (term259 A y z x)). Qed.
Lemma lem5115937 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term213 A y z) = (term213 A y z).
Proof. exact (eq_refl (term213 A y z)). Qed.
Lemma lem5115938 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term264 A y z x) = (term265 A y z x).
Proof. exact (MK_COMB (@lem5115937 A y z) (@lem5115936 A y z x)). Qed.
Lemma lem5115939 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term266 A y z) = (term267 A y z).
Proof. exact (fun_ext (fun x : A => @lem5115938 A y z x)). Qed.
Lemma lem5115940 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115941 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term258 A y z) = (term268 A y z).
Proof. exact (MK_COMB (@lem5115940 A) (@lem5115939 A y z)). Qed.
Lemma lem5115942 {A : Type'} (y : A -> Prop) (z : A -> Prop) : ((term257 A y z) = (term258 A y z)) = ((term214 A y z) = (term268 A y z)).
Proof. exact (MK_COMB (@lem5115935 A y z) (@lem5115941 A y z)). Qed.
Lemma lem5115943 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term214 A y z) = (term268 A y z).
Proof. exact (EQ_MP (@lem5115942 A y z) (@lem5115927 A y z)). Qed.
Lemma lem5115944 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term246 A y z) = (term268 A y z).
Proof. exact (TRANS (@lem5115923 A y z) (@lem5115943 A y z)). Qed.
Lemma lem5115945 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term250 A x s y z) = (term289 A x s y z).
Proof. exact (MK_COMB (@lem5115894 A x y s) (@lem5115944 A y z)). Qed.
Lemma lem5115947 {A : Type'} (P : A -> Prop) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5115948 {A : Type'} (P : A -> Prop) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (@lem5115947 A P Q). Qed.
Lemma lem5115949 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term290 A x s y z) = (term291 A x s y z).
Proof. exact (@lem5115948 A (term286 A x y s) (term268 A y z)). Qed.
Lemma lem5115950 {A : Type'} (x : A -> Prop) (x' : A) (y : A -> Prop) (s : A -> Prop) : (term292 A x y s x') = (term284 A x x' y s).
Proof. exact (eq_refl (term292 A x y s x')). Qed.
Lemma lem5115951 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term293 A x y s) = (term286 A x y s).
Proof. exact (fun_ext (fun x' : A => @lem5115950 A x x' y s)). Qed.
Lemma lem5115952 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115953 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term294 A x y s) = (term287 A x y s).
Proof. exact (MK_COMB (@lem5115952 A) (@lem5115951 A x y s)). Qed.
Lemma lem5115954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115955 {A : Type'} (x : A -> Prop) (y : A -> Prop) (s : A -> Prop) : (term295 A x y s) = (term288 A x y s).
Proof. exact (MK_COMB (@lem5115954) (@lem5115953 A x y s)). Qed.
Lemma lem5115956 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term268 A y z) = (term268 A y z).
Proof. exact (eq_refl (term268 A y z)). Qed.
Lemma lem5115957 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term290 A x s y z) = (term289 A x s y z).
Proof. exact (MK_COMB (@lem5115955 A x y s) (@lem5115956 A y z)). Qed.
Lemma lem5115958 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5115959 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term296 A x s y z) = (term297 A x s y z).
Proof. exact (MK_COMB (@lem5115958) (@lem5115957 A x s y z)). Qed.
Lemma lem5115960 {A : Type'} (x : A -> Prop) (x' : A) (y : A -> Prop) (s : A -> Prop) : (term292 A x y s x') = (term284 A x x' y s).
Proof. exact (eq_refl (term292 A x y s x')). Qed.
Lemma lem5115961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115962 {A : Type'} (x : A -> Prop) (x' : A) (y : A -> Prop) (s : A -> Prop) : (term298 A x y s x') = (term299 A x x' y s).
Proof. exact (MK_COMB (@lem5115961) (@lem5115960 A x x' y s)). Qed.
Lemma lem5115963 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term268 A y z) = (term268 A y z).
Proof. exact (eq_refl (term268 A y z)). Qed.
Lemma lem5115964 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term300 A x s x' y z) = (term301 A x x' s y z).
Proof. exact (MK_COMB (@lem5115962 A x x' y s) (@lem5115963 A y z)). Qed.
Lemma lem5115965 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term302 A x s y z) = (term303 A x s y z).
Proof. exact (fun_ext (fun x' : A => @lem5115964 A x x' s y z)). Qed.
Lemma lem5115966 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115967 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term291 A x s y z) = (term304 A x s y z).
Proof. exact (MK_COMB (@lem5115966 A) (@lem5115965 A x s y z)). Qed.
Lemma lem5115968 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : ((term290 A x s y z) = (term291 A x s y z)) = ((term289 A x s y z) = (term304 A x s y z)).
Proof. exact (MK_COMB (@lem5115959 A x s y z) (@lem5115967 A x s y z)). Qed.
Lemma lem5115969 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term289 A x s y z) = (term304 A x s y z).
Proof. exact (EQ_MP (@lem5115968 A x s y z) (@lem5115949 A x s y z)). Qed.
Lemma lem5115971 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5115972 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (@lem5115971 A P Q). Qed.
Lemma lem5115973 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term305 A x x' s y z) = (term306 A x x' s y z).
Proof. exact (@lem5115972 A (term284 A x x' y s) (term267 A y z)). Qed.
Lemma lem5115974 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term275 A y z x) = (term265 A y z x).
Proof. exact (eq_refl (term275 A y z x)). Qed.
Lemma lem5115975 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term276 A y z) = (term267 A y z).
Proof. exact (fun_ext (fun x : A => @lem5115974 A y z x)). Qed.
Lemma lem5115976 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115977 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term277 A y z) = (term268 A y z).
Proof. exact (MK_COMB (@lem5115976 A) (@lem5115975 A y z)). Qed.
Lemma lem5115978 {A : Type'} (x : A -> Prop) (x' : A) (y : A -> Prop) (s : A -> Prop) : (term299 A x x' y s) = (term299 A x x' y s).
Proof. exact (eq_refl (term299 A x x' y s)). Qed.
Lemma lem5115979 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term305 A x x' s y z) = (term301 A x x' s y z).
Proof. exact (MK_COMB (@lem5115978 A x x' y s) (@lem5115977 A y z)). Qed.
Lemma lem5115980 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5115981 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term307 A x x' s y z) = (term308 A x x' s y z).
Proof. exact (MK_COMB (@lem5115980) (@lem5115979 A x x' s y z)). Qed.
Lemma lem5115982 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x' : A) : (term275 A y z x') = (term265 A y z x').
Proof. exact (eq_refl (term275 A y z x')). Qed.
Lemma lem5115983 {A : Type'} (x : A -> Prop) (x' : A) (y : A -> Prop) (s : A -> Prop) : (term299 A x x' y s) = (term299 A x x' y s).
Proof. exact (eq_refl (term299 A x x' y s)). Qed.
Lemma lem5115984 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x'' : A) : (term309 A x x' s y z x'') = (term310 A x x' s y z x'').
Proof. exact (MK_COMB (@lem5115983 A x x' y s) (@lem5115982 A y z x'')). Qed.
Lemma lem5115985 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term311 A x x' s y z) = (term312 A x x' s y z).
Proof. exact (fun_ext (fun x'' : A => @lem5115984 A x x' s y z x'')). Qed.
Lemma lem5115986 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115987 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term306 A x x' s y z) = (term313 A x x' s y z).
Proof. exact (MK_COMB (@lem5115986 A) (@lem5115985 A x x' s y z)). Qed.
Lemma lem5115988 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : ((term305 A x x' s y z) = (term306 A x x' s y z)) = ((term301 A x x' s y z) = (term313 A x x' s y z)).
Proof. exact (MK_COMB (@lem5115981 A x x' s y z) (@lem5115987 A x x' s y z)). Qed.
Lemma lem5115989 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term301 A x x' s y z) = (term313 A x x' s y z).
Proof. exact (EQ_MP (@lem5115988 A x x' s y z) (@lem5115973 A x x' s y z)). Qed.
Lemma lem5115990 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term303 A x s y z) = (term314 A x s y z).
Proof. exact (fun_ext (fun x' : A => @lem5115989 A x x' s y z)). Qed.
Lemma lem5115991 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5115992 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term304 A x s y z) = (term315 A x s y z).
Proof. exact (MK_COMB (@lem5115991 A) (@lem5115990 A x s y z)). Qed.
Lemma lem5115993 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term289 A x s y z) = (term315 A x s y z).
Proof. exact (TRANS (@lem5115969 A x s y z) (@lem5115992 A x s y z)). Qed.
Lemma lem5115994 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term250 A x s y z) = (term315 A x s y z).
Proof. exact (TRANS (@lem5115945 A x s y z) (@lem5115993 A x s y z)). Qed.
Lemma lem5115995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5115996 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term251 A x s y z) = (term316 A x s y z).
Proof. exact (MK_COMB (@lem5115995) (@lem5115994 A x s y z)). Qed.
Lemma lem5115997 {A : Type'} (z : A -> Prop) (s : A -> Prop) : (term202 A z s) = (term202 A z s).
Proof. exact (eq_refl (term202 A z s)). Qed.
Lemma lem5115998 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term252 A x y z s) = (term317 A x y z s).
Proof. exact (MK_COMB (@lem5115996 A x s y z) (@lem5115997 A z s)). Qed.
Lemma lem5116000 {A : Type'} (P : A -> Prop) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5116001 {A : Type'} (P : A -> Prop) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (@lem5116000 A P Q). Qed.
Lemma lem5116002 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term318 A x y z s) = (term319 A x y z s).
Proof. exact (@lem5116001 A (term314 A x s y z) (term202 A z s)). Qed.
Lemma lem5116003 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term320 A x s y z x') = (term313 A x x' s y z).
Proof. exact (eq_refl (term320 A x s y z x')). Qed.
Lemma lem5116004 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term321 A x s y z) = (term314 A x s y z).
Proof. exact (fun_ext (fun x' : A => @lem5116003 A x x' s y z)). Qed.
Lemma lem5116005 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5116006 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term322 A x s y z) = (term315 A x s y z).
Proof. exact (MK_COMB (@lem5116005 A) (@lem5116004 A x s y z)). Qed.
Lemma lem5116007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5116008 {A : Type'} (x : A -> Prop) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term323 A x s y z) = (term316 A x s y z).
Proof. exact (MK_COMB (@lem5116007) (@lem5116006 A x s y z)). Qed.
Lemma lem5116009 {A : Type'} (z : A -> Prop) (s : A -> Prop) : (term202 A z s) = (term202 A z s).
Proof. exact (eq_refl (term202 A z s)). Qed.
Lemma lem5116010 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term318 A x y z s) = (term317 A x y z s).
Proof. exact (MK_COMB (@lem5116008 A x s y z) (@lem5116009 A z s)). Qed.
Lemma lem5116011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5116012 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term324 A x y z s) = (term325 A x y z s).
Proof. exact (MK_COMB (@lem5116011) (@lem5116010 A x y z s)). Qed.
Lemma lem5116013 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term320 A x s y z x') = (term313 A x x' s y z).
Proof. exact (eq_refl (term320 A x s y z x')). Qed.
Lemma lem5116014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5116015 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term326 A x s y z x') = (term327 A x x' s y z).
Proof. exact (MK_COMB (@lem5116014) (@lem5116013 A x x' s y z)). Qed.
Lemma lem5116016 {A : Type'} (z : A -> Prop) (s : A -> Prop) : (term202 A z s) = (term202 A z s).
Proof. exact (eq_refl (term202 A z s)). Qed.
Lemma lem5116017 {A : Type'} (x : A -> Prop) (x' : A) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term328 A x y x' z s) = (term329 A x x' y z s).
Proof. exact (MK_COMB (@lem5116015 A x x' s y z) (@lem5116016 A z s)). Qed.
Lemma lem5116018 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term330 A x y z s) = (term331 A x y z s).
Proof. exact (fun_ext (fun x' : A => @lem5116017 A x x' y z s)). Qed.
Lemma lem5116019 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5116020 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term319 A x y z s) = (term332 A x y z s).
Proof. exact (MK_COMB (@lem5116019 A) (@lem5116018 A x y z s)). Qed.
Lemma lem5116021 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : ((term318 A x y z s) = (term319 A x y z s)) = ((term317 A x y z s) = (term332 A x y z s)).
Proof. exact (MK_COMB (@lem5116012 A x y z s) (@lem5116020 A x y z s)). Qed.
Lemma lem5116022 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term317 A x y z s) = (term332 A x y z s).
Proof. exact (EQ_MP (@lem5116021 A x y z s) (@lem5116002 A x y z s)). Qed.
Lemma lem5116024 {A : Type'} (P : A -> Prop) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5116025 {A : Type'} (P : A -> Prop) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (@lem5116024 A P Q). Qed.
Lemma lem5116026 {A : Type'} (x : A -> Prop) (x' : A) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term333 A x x' y z s) = (term334 A x x' y z s).
Proof. exact (@lem5116025 A (term312 A x x' s y z) (term202 A z s)). Qed.
Lemma lem5116027 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x'' : A) : (term335 A x x' s y z x'') = (term310 A x x' s y z x'').
Proof. exact (eq_refl (term335 A x x' s y z x'')). Qed.
Lemma lem5116028 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term336 A x x' s y z) = (term312 A x x' s y z).
Proof. exact (fun_ext (fun x'' : A => @lem5116027 A x x' s y z x'')). Qed.
Lemma lem5116029 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5116030 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term337 A x x' s y z) = (term313 A x x' s y z).
Proof. exact (MK_COMB (@lem5116029 A) (@lem5116028 A x x' s y z)). Qed.
Lemma lem5116031 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5116032 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term338 A x x' s y z) = (term327 A x x' s y z).
Proof. exact (MK_COMB (@lem5116031) (@lem5116030 A x x' s y z)). Qed.
Lemma lem5116033 {A : Type'} (z : A -> Prop) (s : A -> Prop) : (term202 A z s) = (term202 A z s).
Proof. exact (eq_refl (term202 A z s)). Qed.
Lemma lem5116034 {A : Type'} (x : A -> Prop) (x' : A) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term333 A x x' y z s) = (term329 A x x' y z s).
Proof. exact (MK_COMB (@lem5116032 A x x' s y z) (@lem5116033 A z s)). Qed.
Lemma lem5116035 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5116036 {A : Type'} (x : A -> Prop) (x' : A) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term339 A x x' y z s) = (term340 A x x' y z s).
Proof. exact (MK_COMB (@lem5116035) (@lem5116034 A x x' y z s)). Qed.
Lemma lem5116037 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x'' : A) : (term335 A x x' s y z x'') = (term310 A x x' s y z x'').
Proof. exact (eq_refl (term335 A x x' s y z x'')). Qed.
Lemma lem5116038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5116039 {A : Type'} (x : A -> Prop) (x' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x'' : A) : (term341 A x x' s y z x'') = (term342 A x x' s y z x'').
Proof. exact (MK_COMB (@lem5116038) (@lem5116037 A x x' s y z x'')). Qed.
Lemma lem5116040 {A : Type'} (z : A -> Prop) (s : A -> Prop) : (term202 A z s) = (term202 A z s).
Proof. exact (eq_refl (term202 A z s)). Qed.
Lemma lem5116041 {A : Type'} (x : A -> Prop) (x' : A) (y : A -> Prop) (x'' : A) (z : A -> Prop) (s : A -> Prop) : (term343 A x x' y x'' z s) = (term344 A x x' y x'' z s).
Proof. exact (MK_COMB (@lem5116039 A x x' s y z x'') (@lem5116040 A z s)). Qed.
Lemma lem5116042 {A : Type'} (x : A -> Prop) (x' : A) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term345 A x x' y z s) = (term346 A x x' y z s).
Proof. exact (fun_ext (fun x'' : A => @lem5116041 A x x' y x'' z s)). Qed.
Lemma lem5116043 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5116044 {A : Type'} (x : A -> Prop) (x' : A) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term334 A x x' y z s) = (term347 A x x' y z s).
Proof. exact (MK_COMB (@lem5116043 A) (@lem5116042 A x x' y z s)). Qed.
Lemma lem5116045 {A : Type'} (x : A -> Prop) (x' : A) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : ((term333 A x x' y z s) = (term334 A x x' y z s)) = ((term329 A x x' y z s) = (term347 A x x' y z s)).
Proof. exact (MK_COMB (@lem5116036 A x x' y z s) (@lem5116044 A x x' y z s)). Qed.
Lemma lem5116046 {A : Type'} (x : A -> Prop) (x' : A) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term329 A x x' y z s) = (term347 A x x' y z s).
Proof. exact (EQ_MP (@lem5116045 A x x' y z s) (@lem5116026 A x x' y z s)). Qed.
Lemma lem5116047 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term331 A x y z s) = (term348 A x y z s).
Proof. exact (fun_ext (fun x' : A => @lem5116046 A x x' y z s)). Qed.
Lemma lem5116048 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5116049 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term332 A x y z s) = (term349 A x y z s).
Proof. exact (MK_COMB (@lem5116048 A) (@lem5116047 A x y z s)). Qed.
Lemma lem5116050 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term317 A x y z s) = (term349 A x y z s).
Proof. exact (TRANS (@lem5116022 A x y z s) (@lem5116049 A x y z s)). Qed.
Lemma lem5116051 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term252 A x y z s) = (term349 A x y z s).
Proof. exact (TRANS (@lem5115998 A x y z s) (@lem5116050 A x y z s)). Qed.
Lemma lem5116052 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term220 A x y z s) = (term349 A x y z s).
Proof. exact (TRANS (@lem5115813 A x y z s) (@lem5116051 A x y z s)). Qed.
Lemma lem5116053 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) : (term177 A x y z s) = (term349 A x y z s).
Proof. exact (TRANS (@lem5115496 A x y z s) (@lem5116052 A x y z s)). Qed.
Lemma lem5116054 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (h1 : term177 A x y z s) : term349 A x y z s.
Proof. exact (EQ_MP (@lem5116053 A x y z s) (@lem5115386 A x y z s h1)). Qed.
Lemma lem5116061 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term350 A x z x') = (term228 A x z x').
Proof. exact (@lem17362 (x x') (z x')). Qed.
Lemma lem5116062 {A : Type'} (P : A -> Prop) : (term205 A P) = (term206 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5116063 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term351 A x z) = (term352 A x z).
Proof. exact (@lem5116062 A (term162 A x z)). Qed.
Lemma lem5116064 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term353 A x z x') = (term160 A x z x').
Proof. exact (eq_refl (term353 A x z x')). Qed.
Lemma lem5116065 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5116066 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term354 A x z x') = (term350 A x z x').
Proof. exact (MK_COMB (@lem5116065) (@lem5116064 A x z x')). Qed.
Lemma lem5116067 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term354 A x z x') = (term228 A x z x').
Proof. exact (TRANS (@lem5116066 A x z x') (@lem5116061 A x z x')). Qed.
Lemma lem5116068 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term355 A x z) = (term225 A x z).
Proof. exact (fun_ext (fun x' : A => @lem5116067 A x z x')). Qed.
Lemma lem5116069 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5116070 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term352 A x z) = (term239 A x z).
Proof. exact (MK_COMB (@lem5116069 A) (@lem5116068 A x z)). Qed.
Lemma lem5116071 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term351 A x z) = (term239 A x z).
Proof. exact (TRANS (@lem5116063 A x z) (@lem5116070 A x z)). Qed.
Lemma lem5116086 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : ((x x') = (z x')) = (term356 A x z x').
Proof. exact (@lem17784 (x x') (z x')). Qed.
Lemma lem5116087 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term168 A x z) = (term357 A x z).
Proof. exact (fun_ext (fun x' : A => @lem5116086 A x z x')). Qed.
Lemma lem5116088 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116089 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term169 A x z) = (term358 A x z).
Proof. exact (MK_COMB (@lem5116088 A) (@lem5116087 A x z)). Qed.
Lemma lem5116090 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term359 A x z) = (term169 A x z).
Proof. exact (@lem16933 (term169 A x z)). Qed.
Lemma lem5116091 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term359 A x z) = (term358 A x z).
Proof. exact (TRANS (@lem5116090 A x z) (@lem5116089 A x z)). Qed.
Lemma lem5116092 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5116093 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term360 A x z) = (term241 A x z).
Proof. exact (MK_COMB (@lem5116092) (@lem5116071 A x z)). Qed.
Lemma lem5116094 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term361 A x z) = (term362 A x z).
Proof. exact (MK_COMB (@lem5116093 A x z) (@lem5116091 A x z)). Qed.
Lemma lem5116095 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term199 A x z) = (term361 A x z).
Proof. exact (@lem17045 (term163 A x z) (term170 A x z)). Qed.
Lemma lem5116096 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term199 A x z) = (term362 A x z).
Proof. exact (TRANS (@lem5116095 A x z) (@lem5116094 A x z)). Qed.
Lemma lem5116126 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term363 A P Q) = (term364 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5116127 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term363 A P Q) = (term364 A P Q).
Proof. exact (@lem5116126 A P Q). Qed.
Lemma lem5116128 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term365 A x z) = (term366 A x z).
Proof. exact (@lem5116127 A (term367 A x z) (term201 A x z)). Qed.
Lemma lem5116129 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term368 A x z x') = (term369 A x z x').
Proof. exact (eq_refl (term368 A x z x')). Qed.
Lemma lem5116130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5116131 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term370 A x z x') = (term371 A x z x').
Proof. exact (MK_COMB (@lem5116130) (@lem5116129 A x z x')). Qed.
Lemma lem5116132 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term372 A x z x') = (term200 A x z x').
Proof. exact (eq_refl (term372 A x z x')). Qed.
Lemma lem5116133 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term373 A x z x') = (term356 A x z x').
Proof. exact (MK_COMB (@lem5116131 A x z x') (@lem5116132 A x z x')). Qed.
Lemma lem5116134 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term374 A x z) = (term357 A x z).
Proof. exact (fun_ext (fun x' : A => @lem5116133 A x z x')). Qed.
Lemma lem5116135 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116136 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term365 A x z) = (term358 A x z).
Proof. exact (MK_COMB (@lem5116135 A) (@lem5116134 A x z)). Qed.
Lemma lem5116137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5116138 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term375 A x z) = (term376 A x z).
Proof. exact (MK_COMB (@lem5116137) (@lem5116136 A x z)). Qed.
Lemma lem5116139 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term368 A x z x') = (term369 A x z x').
Proof. exact (eq_refl (term368 A x z x')). Qed.
Lemma lem5116140 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term377 A x z) = (term367 A x z).
Proof. exact (fun_ext (fun x' : A => @lem5116139 A x z x')). Qed.
Lemma lem5116141 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116142 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term378 A x z) = (term379 A x z).
Proof. exact (MK_COMB (@lem5116141 A) (@lem5116140 A x z)). Qed.
Lemma lem5116143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5116144 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term380 A x z) = (term381 A x z).
Proof. exact (MK_COMB (@lem5116143) (@lem5116142 A x z)). Qed.
Lemma lem5116145 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term372 A x z x') = (term200 A x z x').
Proof. exact (eq_refl (term372 A x z x')). Qed.
Lemma lem5116146 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term382 A x z) = (term201 A x z).
Proof. exact (fun_ext (fun x' : A => @lem5116145 A x z x')). Qed.
Lemma lem5116147 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116148 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term383 A x z) = (term202 A x z).
Proof. exact (MK_COMB (@lem5116147 A) (@lem5116146 A x z)). Qed.
Lemma lem5116149 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term366 A x z) = (term384 A x z).
Proof. exact (MK_COMB (@lem5116144 A x z) (@lem5116148 A x z)). Qed.
Lemma lem5116150 {A : Type'} (x : A -> Prop) (z : A -> Prop) : ((term365 A x z) = (term366 A x z)) = ((term358 A x z) = (term384 A x z)).
Proof. exact (MK_COMB (@lem5116138 A x z) (@lem5116149 A x z)). Qed.
Lemma lem5116151 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term358 A x z) = (term384 A x z).
Proof. exact (EQ_MP (@lem5116150 A x z) (@lem5116128 A x z)). Qed.
Lemma lem5116212 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term241 A x z) = (term241 A x z).
Proof. exact (eq_refl (term241 A x z)). Qed.
Lemma lem5116213 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term362 A x z) = (term385 A x z).
Proof. exact (MK_COMB (@lem5116212 A x z) (@lem5116151 A x z)). Qed.
Lemma lem5116215 {A : Type'} (P : A -> Prop) (Q : Prop) : (term386 A P Q) = (term387 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5116216 {A : Type'} (P : A -> Prop) (Q : Prop) : (term386 A P Q) = (term387 A P Q).
Proof. exact (@lem5116215 A P Q). Qed.
Lemma lem5116217 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term388 A x z) = (term389 A x z).
Proof. exact (@lem5116216 A (term225 A x z) (term384 A x z)). Qed.
Lemma lem5116218 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term227 A x z x') = (term228 A x z x').
Proof. exact (eq_refl (term227 A x z x')). Qed.
Lemma lem5116219 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term237 A x z) = (term225 A x z).
Proof. exact (fun_ext (fun x' : A => @lem5116218 A x z x')). Qed.
Lemma lem5116220 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5116221 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term238 A x z) = (term239 A x z).
Proof. exact (MK_COMB (@lem5116220 A) (@lem5116219 A x z)). Qed.
Lemma lem5116222 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5116223 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term240 A x z) = (term241 A x z).
Proof. exact (MK_COMB (@lem5116222) (@lem5116221 A x z)). Qed.
Lemma lem5116224 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term384 A x z) = (term384 A x z).
Proof. exact (eq_refl (term384 A x z)). Qed.
Lemma lem5116225 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term388 A x z) = (term385 A x z).
Proof. exact (MK_COMB (@lem5116223 A x z) (@lem5116224 A x z)). Qed.
Lemma lem5116226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5116227 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term390 A x z) = (term391 A x z).
Proof. exact (MK_COMB (@lem5116226) (@lem5116225 A x z)). Qed.
Lemma lem5116228 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term227 A x z x') = (term228 A x z x').
Proof. exact (eq_refl (term227 A x z x')). Qed.
Lemma lem5116229 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5116230 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term229 A x z x') = (term230 A x z x').
Proof. exact (MK_COMB (@lem5116229) (@lem5116228 A x z x')). Qed.
Lemma lem5116231 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term384 A x z) = (term384 A x z).
Proof. exact (eq_refl (term384 A x z)). Qed.
Lemma lem5116232 {A : Type'} (x : A) (x' : A -> Prop) (z : A -> Prop) : (term392 A x x' z) = (term393 A x x' z).
Proof. exact (MK_COMB (@lem5116230 A x' z x) (@lem5116231 A x' z)). Qed.
Lemma lem5116233 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term394 A x z) = (term395 A x z).
Proof. exact (fun_ext (fun x' : A => @lem5116232 A x' x z)). Qed.
Lemma lem5116234 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5116235 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term389 A x z) = (term396 A x z).
Proof. exact (MK_COMB (@lem5116234 A) (@lem5116233 A x z)). Qed.
Lemma lem5116236 {A : Type'} (x : A -> Prop) (z : A -> Prop) : ((term388 A x z) = (term389 A x z)) = ((term385 A x z) = (term396 A x z)).
Proof. exact (MK_COMB (@lem5116227 A x z) (@lem5116235 A x z)). Qed.
Lemma lem5116237 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term385 A x z) = (term396 A x z).
Proof. exact (EQ_MP (@lem5116236 A x z) (@lem5116217 A x z)). Qed.
Lemma lem5116238 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term362 A x z) = (term396 A x z).
Proof. exact (TRANS (@lem5116213 A x z) (@lem5116237 A x z)). Qed.
Lemma lem5116239 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term199 A x z) = (term396 A x z).
Proof. exact (TRANS (@lem5116096 A x z) (@lem5116238 A x z)). Qed.
Lemma lem5116240 {A : Type'} (x : A -> Prop) (z : A -> Prop) (h1 : term199 A x z) : term396 A x z.
Proof. exact (EQ_MP (@lem5116239 A x z) (@lem5115391 A x z h1)). Qed.
Lemma lem5116241 {A : Type'} (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term393 A x' x z) : term393 A x' x z.
Proof. exact (h1). Qed.
Lemma lem5116242 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (h1 : term347 A x x'' y z s) : term347 A x x'' y z s.
Proof. exact (h1). Qed.
Lemma lem5116243 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term344 A x x'' y x''' z s.
Proof. exact (h1). Qed.
Lemma lem5116254 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term200 A x z x') = (term200 A x z x').
Proof. exact (eq_refl (term200 A x z x')). Qed.
Lemma lem5116255 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term201 A x z) = (term201 A x z).
Proof. exact (fun_ext (fun x' : A => @lem5116254 A x z x')). Qed.
Lemma lem5116256 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116257 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term202 A x z) = (term202 A x z).
Proof. exact (MK_COMB (@lem5116256 A) (@lem5116255 A x z)). Qed.
Lemma lem5116268 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term369 A x z x') = (term369 A x z x').
Proof. exact (eq_refl (term369 A x z x')). Qed.
Lemma lem5116269 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term367 A x z) = (term367 A x z).
Proof. exact (fun_ext (fun x' : A => @lem5116268 A x z x')). Qed.
Lemma lem5116270 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116271 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term379 A x z) = (term379 A x z).
Proof. exact (MK_COMB (@lem5116270 A) (@lem5116269 A x z)). Qed.
Lemma lem5116272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5116273 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term381 A x z) = (term381 A x z).
Proof. exact (MK_COMB (@lem5116272) (@lem5116271 A x z)). Qed.
Lemma lem5116274 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term384 A x z) = (term384 A x z).
Proof. exact (MK_COMB (@lem5116273 A x z) (@lem5116257 A x z)). Qed.
Lemma lem5116287 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term230 A x z x') = (term230 A x z x').
Proof. exact (eq_refl (term230 A x z x')). Qed.
Lemma lem5116288 {A : Type'} (x' : A) (x : A -> Prop) (z : A -> Prop) : (term393 A x' x z) = (term393 A x' x z).
Proof. exact (MK_COMB (@lem5116287 A x z x') (@lem5116274 A x z)). Qed.
Lemma lem5116289 {A : Type'} (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term393 A x' x z) : term393 A x' x z.
Proof. exact (EQ_MP (@lem5116288 A x' x z) (@lem5116241 A x' x z h1)). Qed.
Lemma lem5116300 {A : Type'} (z : A -> Prop) (s : A -> Prop) (x : A) : (term200 A z s x) = (term200 A z s x).
Proof. exact (eq_refl (term200 A z s x)). Qed.
Lemma lem5116301 {A : Type'} (z : A -> Prop) (s : A -> Prop) : (term201 A z s) = (term201 A z s).
Proof. exact (fun_ext (fun x : A => @lem5116300 A z s x)). Qed.
Lemma lem5116302 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116303 {A : Type'} (z : A -> Prop) (s : A -> Prop) : (term202 A z s) = (term202 A z s).
Proof. exact (MK_COMB (@lem5116302 A) (@lem5116301 A z s)). Qed.
Lemma lem5116328 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) : (term204 A y z x''') = (term204 A y z x''').
Proof. exact (eq_refl (term204 A y z x''')). Qed.
Lemma lem5116339 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term200 A y z x) = (term200 A y z x).
Proof. exact (eq_refl (term200 A y z x)). Qed.
Lemma lem5116340 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term201 A y z) = (term201 A y z).
Proof. exact (fun_ext (fun x : A => @lem5116339 A y z x)). Qed.
Lemma lem5116341 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116342 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term202 A y z) = (term202 A y z).
Proof. exact (MK_COMB (@lem5116341 A) (@lem5116340 A y z)). Qed.
Lemma lem5116343 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5116344 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term213 A y z) = (term213 A y z).
Proof. exact (MK_COMB (@lem5116343) (@lem5116342 A y z)). Qed.
Lemma lem5116345 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) : (term265 A y z x''') = (term265 A y z x''').
Proof. exact (MK_COMB (@lem5116344 A y z) (@lem5116328 A y z x''')). Qed.
Lemma lem5116356 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A) : (term200 A y s x) = (term200 A y s x).
Proof. exact (eq_refl (term200 A y s x)). Qed.
Lemma lem5116357 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term201 A y s) = (term201 A y s).
Proof. exact (fun_ext (fun x : A => @lem5116356 A y s x)). Qed.
Lemma lem5116358 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116359 {A : Type'} (y : A -> Prop) (s : A -> Prop) : (term202 A y s) = (term202 A y s).
Proof. exact (MK_COMB (@lem5116358 A) (@lem5116357 A y s)). Qed.
Lemma lem5116384 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) : (term204 A x y x'') = (term204 A x y x'').
Proof. exact (eq_refl (term204 A x y x'')). Qed.
Lemma lem5116395 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term200 A x y x') = (term200 A x y x').
Proof. exact (eq_refl (term200 A x y x')). Qed.
Lemma lem5116396 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term201 A x y) = (term201 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5116395 A x y x')). Qed.
Lemma lem5116397 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116398 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term202 A x y) = (term202 A x y).
Proof. exact (MK_COMB (@lem5116397 A) (@lem5116396 A x y)). Qed.
Lemma lem5116399 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5116400 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term213 A x y) = (term213 A x y).
Proof. exact (MK_COMB (@lem5116399) (@lem5116398 A x y)). Qed.
Lemma lem5116401 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) : (term265 A x y x'') = (term265 A x y x'').
Proof. exact (MK_COMB (@lem5116400 A x y) (@lem5116384 A x y x'')). Qed.
Lemma lem5116402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5116403 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) : (term282 A x y x'') = (term282 A x y x'').
Proof. exact (MK_COMB (@lem5116402) (@lem5116401 A x y x'')). Qed.
Lemma lem5116404 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (s : A -> Prop) : (term284 A x x'' y s) = (term284 A x x'' y s).
Proof. exact (MK_COMB (@lem5116403 A x y x'') (@lem5116359 A y s)). Qed.
Lemma lem5116405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5116406 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (s : A -> Prop) : (term299 A x x'' y s) = (term299 A x x'' y s).
Proof. exact (MK_COMB (@lem5116405) (@lem5116404 A x x'' y s)). Qed.
Lemma lem5116407 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) : (term310 A x x'' s y z x''') = (term310 A x x'' s y z x''').
Proof. exact (MK_COMB (@lem5116406 A x x'' y s) (@lem5116345 A y z x''')). Qed.
Lemma lem5116408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5116409 {A : Type'} (x : A -> Prop) (x'' : A) (s : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) : (term342 A x x'' s y z x''') = (term342 A x x'' s y z x''').
Proof. exact (MK_COMB (@lem5116408) (@lem5116407 A x x'' s y z x''')). Qed.
Lemma lem5116410 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) : (term344 A x x'' y x''' z s) = (term344 A x x'' y x''' z s).
Proof. exact (MK_COMB (@lem5116409 A x x'' s y z x''') (@lem5116303 A z s)). Qed.
Lemma lem5116411 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term344 A x x'' y x''' z s.
Proof. exact (EQ_MP (@lem5116410 A x x'' y x''' z s) (@lem5116243 A x x'' y x''' z s h1)). Qed.
Lemma lem5116413 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term310 A x x'' s y z x'''.
Proof. exact (proj1 (@lem5116411 A x x'' y x''' z s h1)). Qed.
Lemma lem5116414 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term265 A y z x'''.
Proof. exact (proj2 (@lem5116413 A x x'' y x''' z s h1)). Qed.
Lemma lem5116415 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term284 A x x'' y s.
Proof. exact (proj1 (@lem5116413 A x x'' y x''' z s h1)). Qed.
Lemma lem5116416 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term204 A y z x'''.
Proof. exact (proj2 (@lem5116414 A x x'' y x''' z s h1)). Qed.
Lemma lem5116417 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term202 A y z.
Proof. exact (proj1 (@lem5116414 A x x'' y x''' z s h1)). Qed.
Lemma lem5116419 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term265 A x y x''.
Proof. exact (proj1 (@lem5116415 A x x'' y x''' z s h1)). Qed.
Lemma lem5116420 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term204 A x y x''.
Proof. exact (proj2 (@lem5116419 A x x'' y x''' z s h1)). Qed.
Lemma lem5116421 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term202 A x y.
Proof. exact (proj1 (@lem5116419 A x x'' y x''' z s h1)). Qed.
Lemma lem5116422 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term228 A x y x'') : term228 A x y x''.
Proof. exact (h1). Qed.
Lemma lem5116426 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : term228 A y z x'''.
Proof. exact (h1). Qed.
Lemma lem5116446 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : term228 A y z x'''.
Proof. exact (h1). Qed.
Lemma lem5116447 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term232 A y z x''') : term232 A y z x'''.
Proof. exact (h1). Qed.
Lemma lem5116458 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) (h1 : term228 A x z x') : term228 A x z x'.
Proof. exact (h1). Qed.
Lemma lem5116459 {A : Type'} (x : A -> Prop) (z : A -> Prop) (h1 : term384 A x z) : term384 A x z.
Proof. exact (h1). Qed.
Lemma lem5116463 {A : Type'} (x : A -> Prop) (z : A -> Prop) (h1 : term384 A x z) : term379 A x z.
Proof. exact (proj1 (@lem5116459 A x z h1)). Qed.
Lemma lem5116484 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term200 A y z x) = (term200 A y z x).
Proof. exact (eq_refl (term200 A y z x)). Qed.
Lemma lem5116485 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term201 A y z) = (term201 A y z).
Proof. exact (fun_ext (fun x : A => @lem5116484 A y z x)). Qed.
Lemma lem5116486 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116488 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term202 A y z) = (term202 A y z).
Proof. exact (MK_COMB (@lem5116486 A) (@lem5116485 A y z)). Qed.
Lemma lem5116489 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term202 A y z.
Proof. exact (EQ_MP (@lem5116488 A y z) (@lem5116417 A x x'' y x''' z s h1)). Qed.
Lemma lem5116560 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term200 A y z x) = (term200 A y z x).
Proof. exact (eq_refl (term200 A y z x)). Qed.
Lemma lem5116561 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term201 A y z) = (term201 A y z).
Proof. exact (fun_ext (fun x : A => @lem5116560 A y z x)). Qed.
Lemma lem5116562 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116564 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term202 A y z) = (term202 A y z).
Proof. exact (MK_COMB (@lem5116562 A) (@lem5116561 A y z)). Qed.
Lemma lem5116565 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term202 A y z.
Proof. exact (EQ_MP (@lem5116564 A y z) (@lem5116417 A x x'' y x''' z s h1)). Qed.
Lemma lem5116680 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term200 A x y x') = (term200 A x y x').
Proof. exact (eq_refl (term200 A x y x')). Qed.
Lemma lem5116681 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term201 A x y) = (term201 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5116680 A x y x')). Qed.
Lemma lem5116682 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116684 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term202 A x y) = (term202 A x y).
Proof. exact (MK_COMB (@lem5116682 A) (@lem5116681 A x y)). Qed.
Lemma lem5116685 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term202 A x y.
Proof. exact (EQ_MP (@lem5116684 A x y) (@lem5116421 A x x'' y x''' z s h1)). Qed.
Lemma lem5116756 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term200 A x y x') = (term200 A x y x').
Proof. exact (eq_refl (term200 A x y x')). Qed.
Lemma lem5116757 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term201 A x y) = (term201 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5116756 A x y x')). Qed.
Lemma lem5116758 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116760 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term202 A x y) = (term202 A x y).
Proof. exact (MK_COMB (@lem5116758 A) (@lem5116757 A x y)). Qed.
Lemma lem5116761 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term202 A x y.
Proof. exact (EQ_MP (@lem5116760 A x y) (@lem5116421 A x x'' y x''' z s h1)). Qed.
Lemma lem5116824 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term200 A y z x) = (term200 A y z x).
Proof. exact (eq_refl (term200 A y z x)). Qed.
Lemma lem5116825 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term201 A y z) = (term201 A y z).
Proof. exact (fun_ext (fun x : A => @lem5116824 A y z x)). Qed.
Lemma lem5116826 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116828 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term202 A y z) = (term202 A y z).
Proof. exact (MK_COMB (@lem5116826 A) (@lem5116825 A y z)). Qed.
Lemma lem5116829 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term202 A y z.
Proof. exact (EQ_MP (@lem5116828 A y z) (@lem5116417 A x x'' y x''' z s h1)). Qed.
Lemma lem5116900 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term200 A y z x) = (term200 A y z x).
Proof. exact (eq_refl (term200 A y z x)). Qed.
Lemma lem5116901 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term201 A y z) = (term201 A y z).
Proof. exact (fun_ext (fun x : A => @lem5116900 A y z x)). Qed.
Lemma lem5116902 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116904 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term202 A y z) = (term202 A y z).
Proof. exact (MK_COMB (@lem5116902 A) (@lem5116901 A y z)). Qed.
Lemma lem5116905 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term202 A y z.
Proof. exact (EQ_MP (@lem5116904 A y z) (@lem5116417 A x x'' y x''' z s h1)). Qed.
Lemma lem5116994 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x : A) : (term200 A y z x) = (term200 A y z x).
Proof. exact (eq_refl (term200 A y z x)). Qed.
Lemma lem5116995 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term201 A y z) = (term201 A y z).
Proof. exact (fun_ext (fun x : A => @lem5116994 A y z x)). Qed.
Lemma lem5116996 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5116998 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (term202 A y z) = (term202 A y z).
Proof. exact (MK_COMB (@lem5116996 A) (@lem5116995 A y z)). Qed.
Lemma lem5116999 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term202 A y z.
Proof. exact (EQ_MP (@lem5116998 A y z) (@lem5116417 A x x'' y x''' z s h1)). Qed.
Lemma lem5117020 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term200 A x y x') = (term200 A x y x').
Proof. exact (eq_refl (term200 A x y x')). Qed.
Lemma lem5117021 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term201 A x y) = (term201 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5117020 A x y x')). Qed.
Lemma lem5117022 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5117024 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term202 A x y) = (term202 A x y).
Proof. exact (MK_COMB (@lem5117022 A) (@lem5117021 A x y)). Qed.
Lemma lem5117025 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term202 A x y.
Proof. exact (EQ_MP (@lem5117024 A x y) (@lem5116421 A x x'' y x''' z s h1)). Qed.
Lemma lem5117096 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x' : A) : (term200 A x y x') = (term200 A x y x').
Proof. exact (eq_refl (term200 A x y x')). Qed.
Lemma lem5117097 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term201 A x y) = (term201 A x y).
Proof. exact (fun_ext (fun x' : A => @lem5117096 A x y x')). Qed.
Lemma lem5117098 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5117100 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term202 A x y) = (term202 A x y).
Proof. exact (MK_COMB (@lem5117098 A) (@lem5117097 A x y)). Qed.
Lemma lem5117101 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term202 A x y.
Proof. exact (EQ_MP (@lem5117100 A x y) (@lem5116421 A x x'' y x''' z s h1)). Qed.
Lemma lem5117125 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) : (term369 A x z x') = (term369 A x z x').
Proof. exact (eq_refl (term369 A x z x')). Qed.
Lemma lem5117126 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term367 A x z) = (term367 A x z).
Proof. exact (fun_ext (fun x' : A => @lem5117125 A x z x')). Qed.
Lemma lem5117127 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5117129 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term379 A x z) = (term379 A x z).
Proof. exact (MK_COMB (@lem5117127 A) (@lem5117126 A x z)). Qed.
Lemma lem5117130 {A : Type'} (x : A -> Prop) (z : A -> Prop) (h1 : term384 A x z) : term379 A x z.
Proof. exact (EQ_MP (@lem5117129 A x z) (@lem5116463 A x z h1)). Qed.
Lemma lem5117147 {A : Type'} (_66798 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term372 A y z _66798.
Proof. exact (@lem5116489 A x x'' y x''' z s h1 _66798). Qed.
Lemma lem5117148 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66798 : A) : (term372 A y z _66798) = (term200 A y z _66798).
Proof. exact (eq_refl (term372 A y z _66798)). Qed.
Lemma lem5117159 {A : Type'} (_66802 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term372 A y z _66802.
Proof. exact (@lem5116565 A x x'' y x''' z s h1 _66802). Qed.
Lemma lem5117160 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66802 : A) : (term372 A y z _66802) = (term200 A y z _66802).
Proof. exact (eq_refl (term372 A y z _66802)). Qed.
Lemma lem5117183 {A : Type'} (_66810 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term372 A x y _66810.
Proof. exact (@lem5116685 A x x'' y x''' z s h1 _66810). Qed.
Lemma lem5117184 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_66810 : A) : (term372 A x y _66810) = (term200 A x y _66810).
Proof. exact (eq_refl (term372 A x y _66810)). Qed.
Lemma lem5117195 {A : Type'} (_66814 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term372 A x y _66814.
Proof. exact (@lem5116761 A x x'' y x''' z s h1 _66814). Qed.
Lemma lem5117196 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_66814 : A) : (term372 A x y _66814) = (term200 A x y _66814).
Proof. exact (eq_refl (term372 A x y _66814)). Qed.
Lemma lem5117207 {A : Type'} (_66818 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term372 A y z _66818.
Proof. exact (@lem5116829 A x x'' y x''' z s h1 _66818). Qed.
Lemma lem5117208 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66818 : A) : (term372 A y z _66818) = (term200 A y z _66818).
Proof. exact (eq_refl (term372 A y z _66818)). Qed.
Lemma lem5117219 {A : Type'} (_66822 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term372 A y z _66822.
Proof. exact (@lem5116905 A x x'' y x''' z s h1 _66822). Qed.
Lemma lem5117220 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66822 : A) : (term372 A y z _66822) = (term200 A y z _66822).
Proof. exact (eq_refl (term372 A y z _66822)). Qed.
Lemma lem5117237 {A : Type'} (_66828 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term372 A y z _66828.
Proof. exact (@lem5116999 A x x'' y x''' z s h1 _66828). Qed.
Lemma lem5117238 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66828 : A) : (term372 A y z _66828) = (term200 A y z _66828).
Proof. exact (eq_refl (term372 A y z _66828)). Qed.
Lemma lem5117243 {A : Type'} (_66830 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term372 A x y _66830.
Proof. exact (@lem5117025 A x x'' y x''' z s h1 _66830). Qed.
Lemma lem5117244 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_66830 : A) : (term372 A x y _66830) = (term200 A x y _66830).
Proof. exact (eq_refl (term372 A x y _66830)). Qed.
Lemma lem5117255 {A : Type'} (_66834 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term372 A x y _66834.
Proof. exact (@lem5117101 A x x'' y x''' z s h1 _66834). Qed.
Lemma lem5117256 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_66834 : A) : (term372 A x y _66834) = (term200 A x y _66834).
Proof. exact (eq_refl (term372 A x y _66834)). Qed.
Lemma lem5117258 {A : Type'} (_66835 : A) (x : A -> Prop) (z : A -> Prop) (h1 : term384 A x z) : term368 A x z _66835.
Proof. exact (@lem5117130 A x z h1 _66835). Qed.
Lemma lem5117259 {A : Type'} (x : A -> Prop) (z : A -> Prop) (_66835 : A) : (term368 A x z _66835) = (term369 A x z _66835).
Proof. exact (eq_refl (term368 A x z _66835)). Qed.
Lemma lem5117275 {A : Type'} (_66798 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term200 A y z _66798.
Proof. exact (EQ_MP (@lem5117148 A y z _66798) (@lem5117147 A _66798 x x'' y x''' z s h1)). Qed.
Lemma lem5117295 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : term397 A z x'''.
Proof. exact (proj2 (@lem5116426 A y z x''' h1)). Qed.
Lemma lem5117311 {A : Type'} (_66802 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term200 A y z _66802.
Proof. exact (EQ_MP (@lem5117160 A y z _66802) (@lem5117159 A _66802 x x'' y x''' z s h1)). Qed.
Lemma lem5117331 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : term397 A z x'''.
Proof. exact (proj2 (@lem5116426 A y z x''' h1)). Qed.
Lemma lem5117367 {A : Type'} (_66810 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term200 A x y _66810.
Proof. exact (EQ_MP (@lem5117184 A x y _66810) (@lem5117183 A _66810 x x'' y x''' z s h1)). Qed.
Lemma lem5117371 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term228 A x y x'') : term397 A y x''.
Proof. exact (proj2 (@lem5116422 A x y x'' h1)). Qed.
Lemma lem5117403 {A : Type'} (_66814 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term200 A x y _66814.
Proof. exact (EQ_MP (@lem5117196 A x y _66814) (@lem5117195 A _66814 x x'' y x''' z s h1)). Qed.
Lemma lem5117407 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term228 A x y x'') : term397 A y x''.
Proof. exact (proj2 (@lem5116422 A x y x'' h1)). Qed.
Lemma lem5117435 {A : Type'} (_66818 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term200 A y z _66818.
Proof. exact (EQ_MP (@lem5117208 A y z _66818) (@lem5117207 A _66818 x x'' y x''' z s h1)). Qed.
Lemma lem5117455 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : term397 A z x'''.
Proof. exact (proj2 (@lem5116446 A y z x''' h1)). Qed.
Lemma lem5117471 {A : Type'} (_66822 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term200 A y z _66822.
Proof. exact (EQ_MP (@lem5117220 A y z _66822) (@lem5117219 A _66822 x x'' y x''' z s h1)). Qed.
Lemma lem5117491 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : term397 A z x'''.
Proof. exact (proj2 (@lem5116446 A y z x''' h1)). Qed.
Lemma lem5117515 {A : Type'} (_66828 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term200 A y z _66828.
Proof. exact (EQ_MP (@lem5117238 A y z _66828) (@lem5117237 A _66828 x x'' y x''' z s h1)). Qed.
Lemma lem5117527 {A : Type'} (_66830 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term200 A x y _66830.
Proof. exact (EQ_MP (@lem5117244 A x y _66830) (@lem5117243 A _66830 x x'' y x''' z s h1)). Qed.
Lemma lem5117539 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) (h1 : term228 A x z x') : term397 A z x'.
Proof. exact (proj2 (@lem5116458 A x z x' h1)). Qed.
Lemma lem5117563 {A : Type'} (_66834 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term200 A x y _66834.
Proof. exact (EQ_MP (@lem5117256 A x y _66834) (@lem5117255 A _66834 x x'' y x''' z s h1)). Qed.
Lemma lem5117569 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term232 A y z x''') : term397 A y x'''.
Proof. exact (proj1 (@lem5116447 A y z x''' h1)). Qed.
Lemma lem5117577 {A : Type'} (_66835 : A) (x : A -> Prop) (z : A -> Prop) (h1 : term384 A x z) : term369 A x z _66835.
Proof. exact (EQ_MP (@lem5117259 A x z _66835) (@lem5117258 A _66835 x z h1)). Qed.
Lemma lem5117585 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : y x'''.
Proof. exact (proj1 (@lem5116426 A y z x''' h1)). Qed.
Lemma lem5117586 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : term398 A y x'''.
Proof. exact (fun h0 : term397 A y x''' => @lem5117585 A y z x''' h1). Qed.
Lemma lem5117588 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5117589 {A : Type'} (y : A -> Prop) (x''' : A) : (term398 A y x''') = (y x''').
Proof. exact (@lem5117588 (y x''')). Qed.
Lemma lem5117590 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : y x'''.
Proof. exact (EQ_MP (@lem5117589 A y x''') (@lem5117586 A y z x''' h1)). Qed.
Lemma lem5117596 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5117597 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66798 : A) : (term200 A y z _66798) = (term369 A z y _66798).
Proof. exact (@lem5117596 (z _66798) (term397 A y _66798)). Qed.
Lemma lem5117603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5117604 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66798 : A) : (term400 A y z _66798) = (term401 A z y _66798).
Proof. exact (MK_COMB (@lem5117603) (@lem5117597 A z y _66798)). Qed.
Lemma lem5117610 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66798 : A) : (term369 A z y _66798) = (term369 A z y _66798).
Proof. exact (eq_refl (term369 A z y _66798)). Qed.
Lemma lem5117611 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66798 : A) : ((term200 A y z _66798) = (term369 A z y _66798)) = ((term369 A z y _66798) = (term369 A z y _66798)).
Proof. exact (MK_COMB (@lem5117604 A z y _66798) (@lem5117610 A z y _66798)). Qed.
Lemma lem5117613 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5117614 (x : Prop) : (x = x) = True.
Proof. exact (@lem5117613 Prop x). Qed.
Lemma lem5117615 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66798 : A) : ((term369 A z y _66798) = (term369 A z y _66798)) = True.
Proof. exact (@lem5117614 (term369 A z y _66798)). Qed.
Lemma lem5117616 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66798 : A) : ((term200 A y z _66798) = (term369 A z y _66798)) = True.
Proof. exact (TRANS (@lem5117611 A z y _66798) (@lem5117615 A z y _66798)). Qed.
Lemma lem5117617 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66798 : A) : True = ((term200 A y z _66798) = (term369 A z y _66798)).
Proof. exact (SYM (@lem5117616 A z y _66798)). Qed.
Lemma lem5117618 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66798 : A) : (term200 A y z _66798) = (term369 A z y _66798).
Proof. exact (EQ_MP (@lem5117617 A z y _66798) (@lem0)). Qed.
Lemma lem5117619 {A : Type'} (_66798 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term369 A z y _66798.
Proof. exact (EQ_MP (@lem5117618 A z y _66798) (@lem5117275 A _66798 x x'' y x''' z s h1)). Qed.
Lemma lem5117621 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5117622 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66798 : A) : (term369 A z y _66798) = (term403 A y z _66798).
Proof. exact (@lem5117621 (term397 A y _66798) (z _66798)). Qed.
Lemma lem5117624 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5117625 {A : Type'} (y : A -> Prop) (_66798 : A) : (term404 A y _66798) = (y _66798).
Proof. exact (@lem5117624 (y _66798)). Qed.
Lemma lem5117626 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5117627 {A : Type'} (y : A -> Prop) (_66798 : A) : (term405 A y _66798) = (term158 A y _66798).
Proof. exact (MK_COMB (@lem5117626) (@lem5117625 A y _66798)). Qed.
Lemma lem5117628 {A : Type'} (z : A -> Prop) (_66798 : A) : (z _66798) = (z _66798).
Proof. exact (eq_refl (z _66798)). Qed.
Lemma lem5117629 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66798 : A) : (term403 A y z _66798) = (term160 A y z _66798).
Proof. exact (MK_COMB (@lem5117627 A y _66798) (@lem5117628 A z _66798)). Qed.
Lemma lem5117630 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66798 : A) : (term369 A z y _66798) = (term160 A y z _66798).
Proof. exact (TRANS (@lem5117622 A y z _66798) (@lem5117629 A y z _66798)). Qed.
Lemma lem5117633 {A : Type'} (_66798 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A y z _66798.
Proof. exact (EQ_MP (@lem5117630 A y z _66798) (@lem5117619 A _66798 x x'' y x''' z s h1)). Qed.
Lemma lem5117634 {A : Type'} (_66798 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A y z _66798.
Proof. exact (@lem5117633 A _66798 x x'' y x''' z s h1). Qed.
Lemma lem5117635 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A y z x'''.
Proof. exact (@lem5117634 A x''' x x'' y x''' z s h1). Qed.
Lemma lem5117638 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : z x'''.
Proof. exact (@lem5117635 A x x'' y x''' z s h2 (@lem5117590 A y z x''' h1)). Qed.
Lemma lem5117639 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : term398 A z x'''.
Proof. exact (fun h0 : term397 A z x''' => @lem5117638 A x x'' y x''' z s h1 h2). Qed.
Lemma lem5117641 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5117642 {A : Type'} (z : A -> Prop) (x''' : A) : (term398 A z x''') = (z x''').
Proof. exact (@lem5117641 (z x''')). Qed.
Lemma lem5117643 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : z x'''.
Proof. exact (EQ_MP (@lem5117642 A z x''') (@lem5117639 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5117646 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5117648 {A : Type'} (z : A -> Prop) (x''' : A) : (term397 A z x''') = (term406 A z x''').
Proof. exact (@lem5117646 (z x''')). Qed.
Lemma lem5117651 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : term406 A z x'''.
Proof. exact (EQ_MP (@lem5117648 A z x''') (@lem5117295 A y z x''' h1)). Qed.
Lemma lem5117654 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : False.
Proof. exact (@lem5117651 A y z x''' h1 (@lem5117643 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5117655 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : term407.
Proof. exact (fun h0 : ~ False => @lem5117654 A x x'' y x''' z s h1 h2). Qed.
Lemma lem5117657 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5117658 : term407 = False.
Proof. exact (@lem5117657 False). Qed.
Lemma lem5117659 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : False.
Proof. exact (EQ_MP (@lem5117658) (@lem5117655 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5117661 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : y x'''.
Proof. exact (proj1 (@lem5116426 A y z x''' h1)). Qed.
Lemma lem5117662 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : term398 A y x'''.
Proof. exact (fun h0 : term397 A y x''' => @lem5117661 A y z x''' h1). Qed.
Lemma lem5117664 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5117665 {A : Type'} (y : A -> Prop) (x''' : A) : (term398 A y x''') = (y x''').
Proof. exact (@lem5117664 (y x''')). Qed.
Lemma lem5117666 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : y x'''.
Proof. exact (EQ_MP (@lem5117665 A y x''') (@lem5117662 A y z x''' h1)). Qed.
Lemma lem5117672 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5117673 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66802 : A) : (term200 A y z _66802) = (term369 A z y _66802).
Proof. exact (@lem5117672 (z _66802) (term397 A y _66802)). Qed.
Lemma lem5117679 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5117680 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66802 : A) : (term400 A y z _66802) = (term401 A z y _66802).
Proof. exact (MK_COMB (@lem5117679) (@lem5117673 A z y _66802)). Qed.
Lemma lem5117686 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66802 : A) : (term369 A z y _66802) = (term369 A z y _66802).
Proof. exact (eq_refl (term369 A z y _66802)). Qed.
Lemma lem5117687 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66802 : A) : ((term200 A y z _66802) = (term369 A z y _66802)) = ((term369 A z y _66802) = (term369 A z y _66802)).
Proof. exact (MK_COMB (@lem5117680 A z y _66802) (@lem5117686 A z y _66802)). Qed.
Lemma lem5117689 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5117690 (x : Prop) : (x = x) = True.
Proof. exact (@lem5117689 Prop x). Qed.
Lemma lem5117691 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66802 : A) : ((term369 A z y _66802) = (term369 A z y _66802)) = True.
Proof. exact (@lem5117690 (term369 A z y _66802)). Qed.
Lemma lem5117692 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66802 : A) : ((term200 A y z _66802) = (term369 A z y _66802)) = True.
Proof. exact (TRANS (@lem5117687 A z y _66802) (@lem5117691 A z y _66802)). Qed.
Lemma lem5117693 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66802 : A) : True = ((term200 A y z _66802) = (term369 A z y _66802)).
Proof. exact (SYM (@lem5117692 A z y _66802)). Qed.
Lemma lem5117694 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66802 : A) : (term200 A y z _66802) = (term369 A z y _66802).
Proof. exact (EQ_MP (@lem5117693 A z y _66802) (@lem0)). Qed.
Lemma lem5117695 {A : Type'} (_66802 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term369 A z y _66802.
Proof. exact (EQ_MP (@lem5117694 A z y _66802) (@lem5117311 A _66802 x x'' y x''' z s h1)). Qed.
Lemma lem5117697 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5117698 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66802 : A) : (term369 A z y _66802) = (term403 A y z _66802).
Proof. exact (@lem5117697 (term397 A y _66802) (z _66802)). Qed.
Lemma lem5117700 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5117701 {A : Type'} (y : A -> Prop) (_66802 : A) : (term404 A y _66802) = (y _66802).
Proof. exact (@lem5117700 (y _66802)). Qed.
Lemma lem5117702 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5117703 {A : Type'} (y : A -> Prop) (_66802 : A) : (term405 A y _66802) = (term158 A y _66802).
Proof. exact (MK_COMB (@lem5117702) (@lem5117701 A y _66802)). Qed.
Lemma lem5117704 {A : Type'} (z : A -> Prop) (_66802 : A) : (z _66802) = (z _66802).
Proof. exact (eq_refl (z _66802)). Qed.
Lemma lem5117705 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66802 : A) : (term403 A y z _66802) = (term160 A y z _66802).
Proof. exact (MK_COMB (@lem5117703 A y _66802) (@lem5117704 A z _66802)). Qed.
Lemma lem5117706 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66802 : A) : (term369 A z y _66802) = (term160 A y z _66802).
Proof. exact (TRANS (@lem5117698 A y z _66802) (@lem5117705 A y z _66802)). Qed.
Lemma lem5117709 {A : Type'} (_66802 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A y z _66802.
Proof. exact (EQ_MP (@lem5117706 A y z _66802) (@lem5117695 A _66802 x x'' y x''' z s h1)). Qed.
Lemma lem5117710 {A : Type'} (_66802 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A y z _66802.
Proof. exact (@lem5117709 A _66802 x x'' y x''' z s h1). Qed.
Lemma lem5117711 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A y z x'''.
Proof. exact (@lem5117710 A x''' x x'' y x''' z s h1). Qed.
Lemma lem5117714 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : z x'''.
Proof. exact (@lem5117711 A x x'' y x''' z s h2 (@lem5117666 A y z x''' h1)). Qed.
Lemma lem5117715 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : term398 A z x'''.
Proof. exact (fun h0 : term397 A z x''' => @lem5117714 A x x'' y x''' z s h1 h2). Qed.
Lemma lem5117717 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5117718 {A : Type'} (z : A -> Prop) (x''' : A) : (term398 A z x''') = (z x''').
Proof. exact (@lem5117717 (z x''')). Qed.
Lemma lem5117719 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : z x'''.
Proof. exact (EQ_MP (@lem5117718 A z x''') (@lem5117715 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5117722 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5117724 {A : Type'} (z : A -> Prop) (x''' : A) : (term397 A z x''') = (term406 A z x''').
Proof. exact (@lem5117722 (z x''')). Qed.
Lemma lem5117727 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : term406 A z x'''.
Proof. exact (EQ_MP (@lem5117724 A z x''') (@lem5117331 A y z x''' h1)). Qed.
Lemma lem5117730 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : False.
Proof. exact (@lem5117727 A y z x''' h1 (@lem5117719 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5117731 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : term407.
Proof. exact (fun h0 : ~ False => @lem5117730 A x x'' y x''' z s h1 h2). Qed.
Lemma lem5117733 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5117734 : term407 = False.
Proof. exact (@lem5117733 False). Qed.
Lemma lem5117735 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : False.
Proof. exact (EQ_MP (@lem5117734) (@lem5117731 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5117737 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term228 A x y x'') : x x''.
Proof. exact (proj1 (@lem5116422 A x y x'' h1)). Qed.
Lemma lem5117738 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term228 A x y x'') : term398 A x x''.
Proof. exact (fun h0 : term397 A x x'' => @lem5117737 A x y x'' h1). Qed.
Lemma lem5117740 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5117741 {A : Type'} (x : A -> Prop) (x'' : A) : (term398 A x x'') = (x x'').
Proof. exact (@lem5117740 (x x'')). Qed.
Lemma lem5117742 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term228 A x y x'') : x x''.
Proof. exact (EQ_MP (@lem5117741 A x x'') (@lem5117738 A x y x'' h1)). Qed.
Lemma lem5117748 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5117749 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66810 : A) : (term200 A x y _66810) = (term369 A y x _66810).
Proof. exact (@lem5117748 (y _66810) (term397 A x _66810)). Qed.
Lemma lem5117755 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5117756 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66810 : A) : (term400 A x y _66810) = (term401 A y x _66810).
Proof. exact (MK_COMB (@lem5117755) (@lem5117749 A y x _66810)). Qed.
Lemma lem5117762 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66810 : A) : (term369 A y x _66810) = (term369 A y x _66810).
Proof. exact (eq_refl (term369 A y x _66810)). Qed.
Lemma lem5117763 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66810 : A) : ((term200 A x y _66810) = (term369 A y x _66810)) = ((term369 A y x _66810) = (term369 A y x _66810)).
Proof. exact (MK_COMB (@lem5117756 A y x _66810) (@lem5117762 A y x _66810)). Qed.
Lemma lem5117765 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5117766 (x : Prop) : (x = x) = True.
Proof. exact (@lem5117765 Prop x). Qed.
Lemma lem5117767 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66810 : A) : ((term369 A y x _66810) = (term369 A y x _66810)) = True.
Proof. exact (@lem5117766 (term369 A y x _66810)). Qed.
Lemma lem5117768 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66810 : A) : ((term200 A x y _66810) = (term369 A y x _66810)) = True.
Proof. exact (TRANS (@lem5117763 A y x _66810) (@lem5117767 A y x _66810)). Qed.
Lemma lem5117769 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66810 : A) : True = ((term200 A x y _66810) = (term369 A y x _66810)).
Proof. exact (SYM (@lem5117768 A y x _66810)). Qed.
Lemma lem5117770 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66810 : A) : (term200 A x y _66810) = (term369 A y x _66810).
Proof. exact (EQ_MP (@lem5117769 A y x _66810) (@lem0)). Qed.
Lemma lem5117771 {A : Type'} (_66810 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term369 A y x _66810.
Proof. exact (EQ_MP (@lem5117770 A y x _66810) (@lem5117367 A _66810 x x'' y x''' z s h1)). Qed.
Lemma lem5117773 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5117774 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_66810 : A) : (term369 A y x _66810) = (term403 A x y _66810).
Proof. exact (@lem5117773 (term397 A x _66810) (y _66810)). Qed.
Lemma lem5117776 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5117777 {A : Type'} (x : A -> Prop) (_66810 : A) : (term404 A x _66810) = (x _66810).
Proof. exact (@lem5117776 (x _66810)). Qed.
Lemma lem5117778 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5117779 {A : Type'} (x : A -> Prop) (_66810 : A) : (term405 A x _66810) = (term158 A x _66810).
Proof. exact (MK_COMB (@lem5117778) (@lem5117777 A x _66810)). Qed.
Lemma lem5117780 {A : Type'} (y : A -> Prop) (_66810 : A) : (y _66810) = (y _66810).
Proof. exact (eq_refl (y _66810)). Qed.
Lemma lem5117781 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_66810 : A) : (term403 A x y _66810) = (term160 A x y _66810).
Proof. exact (MK_COMB (@lem5117779 A x _66810) (@lem5117780 A y _66810)). Qed.
Lemma lem5117782 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_66810 : A) : (term369 A y x _66810) = (term160 A x y _66810).
Proof. exact (TRANS (@lem5117774 A x y _66810) (@lem5117781 A x y _66810)). Qed.
Lemma lem5117785 {A : Type'} (_66810 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A x y _66810.
Proof. exact (EQ_MP (@lem5117782 A x y _66810) (@lem5117771 A _66810 x x'' y x''' z s h1)). Qed.
Lemma lem5117786 {A : Type'} (_66810 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A x y _66810.
Proof. exact (@lem5117785 A _66810 x x'' y x''' z s h1). Qed.
Lemma lem5117787 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A x y x''.
Proof. exact (@lem5117786 A x'' x x'' y x''' z s h1). Qed.
Lemma lem5117790 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x y x'') (h2 : term344 A x x'' y x''' z s) : y x''.
Proof. exact (@lem5117787 A x x'' y x''' z s h2 (@lem5117742 A x y x'' h1)). Qed.
Lemma lem5117791 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x y x'') (h2 : term344 A x x'' y x''' z s) : term398 A y x''.
Proof. exact (fun h0 : term397 A y x'' => @lem5117790 A x x'' y x''' z s h1 h2). Qed.
Lemma lem5117793 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5117794 {A : Type'} (y : A -> Prop) (x'' : A) : (term398 A y x'') = (y x'').
Proof. exact (@lem5117793 (y x'')). Qed.
Lemma lem5117795 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x y x'') (h2 : term344 A x x'' y x''' z s) : y x''.
Proof. exact (EQ_MP (@lem5117794 A y x'') (@lem5117791 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5117798 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5117800 {A : Type'} (y : A -> Prop) (x'' : A) : (term397 A y x'') = (term406 A y x'').
Proof. exact (@lem5117798 (y x'')). Qed.
Lemma lem5117803 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term228 A x y x'') : term406 A y x''.
Proof. exact (EQ_MP (@lem5117800 A y x'') (@lem5117371 A x y x'' h1)). Qed.
Lemma lem5117806 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x y x'') (h2 : term344 A x x'' y x''' z s) : False.
Proof. exact (@lem5117803 A x y x'' h1 (@lem5117795 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5117807 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x y x'') (h2 : term344 A x x'' y x''' z s) : term407.
Proof. exact (fun h0 : ~ False => @lem5117806 A x x'' y x''' z s h1 h2). Qed.
Lemma lem5117809 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5117810 : term407 = False.
Proof. exact (@lem5117809 False). Qed.
Lemma lem5117811 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x y x'') (h2 : term344 A x x'' y x''' z s) : False.
Proof. exact (EQ_MP (@lem5117810) (@lem5117807 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5117813 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term228 A x y x'') : x x''.
Proof. exact (proj1 (@lem5116422 A x y x'' h1)). Qed.
Lemma lem5117814 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term228 A x y x'') : term398 A x x''.
Proof. exact (fun h0 : term397 A x x'' => @lem5117813 A x y x'' h1). Qed.
Lemma lem5117816 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5117817 {A : Type'} (x : A -> Prop) (x'' : A) : (term398 A x x'') = (x x'').
Proof. exact (@lem5117816 (x x'')). Qed.
Lemma lem5117818 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term228 A x y x'') : x x''.
Proof. exact (EQ_MP (@lem5117817 A x x'') (@lem5117814 A x y x'' h1)). Qed.
Lemma lem5117824 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5117825 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66814 : A) : (term200 A x y _66814) = (term369 A y x _66814).
Proof. exact (@lem5117824 (y _66814) (term397 A x _66814)). Qed.
Lemma lem5117831 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5117832 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66814 : A) : (term400 A x y _66814) = (term401 A y x _66814).
Proof. exact (MK_COMB (@lem5117831) (@lem5117825 A y x _66814)). Qed.
Lemma lem5117838 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66814 : A) : (term369 A y x _66814) = (term369 A y x _66814).
Proof. exact (eq_refl (term369 A y x _66814)). Qed.
Lemma lem5117839 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66814 : A) : ((term200 A x y _66814) = (term369 A y x _66814)) = ((term369 A y x _66814) = (term369 A y x _66814)).
Proof. exact (MK_COMB (@lem5117832 A y x _66814) (@lem5117838 A y x _66814)). Qed.
Lemma lem5117841 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5117842 (x : Prop) : (x = x) = True.
Proof. exact (@lem5117841 Prop x). Qed.
Lemma lem5117843 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66814 : A) : ((term369 A y x _66814) = (term369 A y x _66814)) = True.
Proof. exact (@lem5117842 (term369 A y x _66814)). Qed.
Lemma lem5117844 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66814 : A) : ((term200 A x y _66814) = (term369 A y x _66814)) = True.
Proof. exact (TRANS (@lem5117839 A y x _66814) (@lem5117843 A y x _66814)). Qed.
Lemma lem5117845 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66814 : A) : True = ((term200 A x y _66814) = (term369 A y x _66814)).
Proof. exact (SYM (@lem5117844 A y x _66814)). Qed.
Lemma lem5117846 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66814 : A) : (term200 A x y _66814) = (term369 A y x _66814).
Proof. exact (EQ_MP (@lem5117845 A y x _66814) (@lem0)). Qed.
Lemma lem5117847 {A : Type'} (_66814 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term369 A y x _66814.
Proof. exact (EQ_MP (@lem5117846 A y x _66814) (@lem5117403 A _66814 x x'' y x''' z s h1)). Qed.
Lemma lem5117849 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5117850 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_66814 : A) : (term369 A y x _66814) = (term403 A x y _66814).
Proof. exact (@lem5117849 (term397 A x _66814) (y _66814)). Qed.
Lemma lem5117852 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5117853 {A : Type'} (x : A -> Prop) (_66814 : A) : (term404 A x _66814) = (x _66814).
Proof. exact (@lem5117852 (x _66814)). Qed.
Lemma lem5117854 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5117855 {A : Type'} (x : A -> Prop) (_66814 : A) : (term405 A x _66814) = (term158 A x _66814).
Proof. exact (MK_COMB (@lem5117854) (@lem5117853 A x _66814)). Qed.
Lemma lem5117856 {A : Type'} (y : A -> Prop) (_66814 : A) : (y _66814) = (y _66814).
Proof. exact (eq_refl (y _66814)). Qed.
Lemma lem5117857 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_66814 : A) : (term403 A x y _66814) = (term160 A x y _66814).
Proof. exact (MK_COMB (@lem5117855 A x _66814) (@lem5117856 A y _66814)). Qed.
Lemma lem5117858 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_66814 : A) : (term369 A y x _66814) = (term160 A x y _66814).
Proof. exact (TRANS (@lem5117850 A x y _66814) (@lem5117857 A x y _66814)). Qed.
Lemma lem5117861 {A : Type'} (_66814 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A x y _66814.
Proof. exact (EQ_MP (@lem5117858 A x y _66814) (@lem5117847 A _66814 x x'' y x''' z s h1)). Qed.
Lemma lem5117862 {A : Type'} (_66814 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A x y _66814.
Proof. exact (@lem5117861 A _66814 x x'' y x''' z s h1). Qed.
Lemma lem5117863 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A x y x''.
Proof. exact (@lem5117862 A x'' x x'' y x''' z s h1). Qed.
Lemma lem5117866 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x y x'') (h2 : term344 A x x'' y x''' z s) : y x''.
Proof. exact (@lem5117863 A x x'' y x''' z s h2 (@lem5117818 A x y x'' h1)). Qed.
Lemma lem5117867 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x y x'') (h2 : term344 A x x'' y x''' z s) : term398 A y x''.
Proof. exact (fun h0 : term397 A y x'' => @lem5117866 A x x'' y x''' z s h1 h2). Qed.
Lemma lem5117869 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5117870 {A : Type'} (y : A -> Prop) (x'' : A) : (term398 A y x'') = (y x'').
Proof. exact (@lem5117869 (y x'')). Qed.
Lemma lem5117871 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x y x'') (h2 : term344 A x x'' y x''' z s) : y x''.
Proof. exact (EQ_MP (@lem5117870 A y x'') (@lem5117867 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5117874 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5117876 {A : Type'} (y : A -> Prop) (x'' : A) : (term397 A y x'') = (term406 A y x'').
Proof. exact (@lem5117874 (y x'')). Qed.
Lemma lem5117879 {A : Type'} (x : A -> Prop) (y : A -> Prop) (x'' : A) (h1 : term228 A x y x'') : term406 A y x''.
Proof. exact (EQ_MP (@lem5117876 A y x'') (@lem5117407 A x y x'' h1)). Qed.
Lemma lem5117882 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x y x'') (h2 : term344 A x x'' y x''' z s) : False.
Proof. exact (@lem5117879 A x y x'' h1 (@lem5117871 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5117883 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x y x'') (h2 : term344 A x x'' y x''' z s) : term407.
Proof. exact (fun h0 : ~ False => @lem5117882 A x x'' y x''' z s h1 h2). Qed.
Lemma lem5117885 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5117886 : term407 = False.
Proof. exact (@lem5117885 False). Qed.
Lemma lem5117887 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x y x'') (h2 : term344 A x x'' y x''' z s) : False.
Proof. exact (EQ_MP (@lem5117886) (@lem5117883 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5117889 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : y x'''.
Proof. exact (proj1 (@lem5116446 A y z x''' h1)). Qed.
Lemma lem5117890 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : term398 A y x'''.
Proof. exact (fun h0 : term397 A y x''' => @lem5117889 A y z x''' h1). Qed.
Lemma lem5117892 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5117893 {A : Type'} (y : A -> Prop) (x''' : A) : (term398 A y x''') = (y x''').
Proof. exact (@lem5117892 (y x''')). Qed.
Lemma lem5117894 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : y x'''.
Proof. exact (EQ_MP (@lem5117893 A y x''') (@lem5117890 A y z x''' h1)). Qed.
Lemma lem5117900 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5117901 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66818 : A) : (term200 A y z _66818) = (term369 A z y _66818).
Proof. exact (@lem5117900 (z _66818) (term397 A y _66818)). Qed.
Lemma lem5117907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5117908 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66818 : A) : (term400 A y z _66818) = (term401 A z y _66818).
Proof. exact (MK_COMB (@lem5117907) (@lem5117901 A z y _66818)). Qed.
Lemma lem5117914 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66818 : A) : (term369 A z y _66818) = (term369 A z y _66818).
Proof. exact (eq_refl (term369 A z y _66818)). Qed.
Lemma lem5117915 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66818 : A) : ((term200 A y z _66818) = (term369 A z y _66818)) = ((term369 A z y _66818) = (term369 A z y _66818)).
Proof. exact (MK_COMB (@lem5117908 A z y _66818) (@lem5117914 A z y _66818)). Qed.
Lemma lem5117917 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5117918 (x : Prop) : (x = x) = True.
Proof. exact (@lem5117917 Prop x). Qed.
Lemma lem5117919 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66818 : A) : ((term369 A z y _66818) = (term369 A z y _66818)) = True.
Proof. exact (@lem5117918 (term369 A z y _66818)). Qed.
Lemma lem5117920 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66818 : A) : ((term200 A y z _66818) = (term369 A z y _66818)) = True.
Proof. exact (TRANS (@lem5117915 A z y _66818) (@lem5117919 A z y _66818)). Qed.
Lemma lem5117921 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66818 : A) : True = ((term200 A y z _66818) = (term369 A z y _66818)).
Proof. exact (SYM (@lem5117920 A z y _66818)). Qed.
Lemma lem5117922 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66818 : A) : (term200 A y z _66818) = (term369 A z y _66818).
Proof. exact (EQ_MP (@lem5117921 A z y _66818) (@lem0)). Qed.
Lemma lem5117923 {A : Type'} (_66818 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term369 A z y _66818.
Proof. exact (EQ_MP (@lem5117922 A z y _66818) (@lem5117435 A _66818 x x'' y x''' z s h1)). Qed.
Lemma lem5117925 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5117926 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66818 : A) : (term369 A z y _66818) = (term403 A y z _66818).
Proof. exact (@lem5117925 (term397 A y _66818) (z _66818)). Qed.
Lemma lem5117928 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5117929 {A : Type'} (y : A -> Prop) (_66818 : A) : (term404 A y _66818) = (y _66818).
Proof. exact (@lem5117928 (y _66818)). Qed.
Lemma lem5117930 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5117931 {A : Type'} (y : A -> Prop) (_66818 : A) : (term405 A y _66818) = (term158 A y _66818).
Proof. exact (MK_COMB (@lem5117930) (@lem5117929 A y _66818)). Qed.
Lemma lem5117932 {A : Type'} (z : A -> Prop) (_66818 : A) : (z _66818) = (z _66818).
Proof. exact (eq_refl (z _66818)). Qed.
Lemma lem5117933 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66818 : A) : (term403 A y z _66818) = (term160 A y z _66818).
Proof. exact (MK_COMB (@lem5117931 A y _66818) (@lem5117932 A z _66818)). Qed.
Lemma lem5117934 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66818 : A) : (term369 A z y _66818) = (term160 A y z _66818).
Proof. exact (TRANS (@lem5117926 A y z _66818) (@lem5117933 A y z _66818)). Qed.
Lemma lem5117937 {A : Type'} (_66818 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A y z _66818.
Proof. exact (EQ_MP (@lem5117934 A y z _66818) (@lem5117923 A _66818 x x'' y x''' z s h1)). Qed.
Lemma lem5117938 {A : Type'} (_66818 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A y z _66818.
Proof. exact (@lem5117937 A _66818 x x'' y x''' z s h1). Qed.
Lemma lem5117939 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A y z x'''.
Proof. exact (@lem5117938 A x''' x x'' y x''' z s h1). Qed.
Lemma lem5117942 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : z x'''.
Proof. exact (@lem5117939 A x x'' y x''' z s h2 (@lem5117894 A y z x''' h1)). Qed.
Lemma lem5117943 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : term398 A z x'''.
Proof. exact (fun h0 : term397 A z x''' => @lem5117942 A x x'' y x''' z s h1 h2). Qed.
Lemma lem5117945 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5117946 {A : Type'} (z : A -> Prop) (x''' : A) : (term398 A z x''') = (z x''').
Proof. exact (@lem5117945 (z x''')). Qed.
Lemma lem5117947 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : z x'''.
Proof. exact (EQ_MP (@lem5117946 A z x''') (@lem5117943 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5117950 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5117952 {A : Type'} (z : A -> Prop) (x''' : A) : (term397 A z x''') = (term406 A z x''').
Proof. exact (@lem5117950 (z x''')). Qed.
Lemma lem5117955 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : term406 A z x'''.
Proof. exact (EQ_MP (@lem5117952 A z x''') (@lem5117455 A y z x''' h1)). Qed.
Lemma lem5117958 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : False.
Proof. exact (@lem5117955 A y z x''' h1 (@lem5117947 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5117959 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : term407.
Proof. exact (fun h0 : ~ False => @lem5117958 A x x'' y x''' z s h1 h2). Qed.
Lemma lem5117961 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5117962 : term407 = False.
Proof. exact (@lem5117961 False). Qed.
Lemma lem5117963 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : False.
Proof. exact (EQ_MP (@lem5117962) (@lem5117959 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5117965 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : y x'''.
Proof. exact (proj1 (@lem5116446 A y z x''' h1)). Qed.
Lemma lem5117966 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : term398 A y x'''.
Proof. exact (fun h0 : term397 A y x''' => @lem5117965 A y z x''' h1). Qed.
Lemma lem5117968 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5117969 {A : Type'} (y : A -> Prop) (x''' : A) : (term398 A y x''') = (y x''').
Proof. exact (@lem5117968 (y x''')). Qed.
Lemma lem5117970 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : y x'''.
Proof. exact (EQ_MP (@lem5117969 A y x''') (@lem5117966 A y z x''' h1)). Qed.
Lemma lem5117976 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5117977 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66822 : A) : (term200 A y z _66822) = (term369 A z y _66822).
Proof. exact (@lem5117976 (z _66822) (term397 A y _66822)). Qed.
Lemma lem5117983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5117984 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66822 : A) : (term400 A y z _66822) = (term401 A z y _66822).
Proof. exact (MK_COMB (@lem5117983) (@lem5117977 A z y _66822)). Qed.
Lemma lem5117990 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66822 : A) : (term369 A z y _66822) = (term369 A z y _66822).
Proof. exact (eq_refl (term369 A z y _66822)). Qed.
Lemma lem5117991 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66822 : A) : ((term200 A y z _66822) = (term369 A z y _66822)) = ((term369 A z y _66822) = (term369 A z y _66822)).
Proof. exact (MK_COMB (@lem5117984 A z y _66822) (@lem5117990 A z y _66822)). Qed.
Lemma lem5117993 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5117994 (x : Prop) : (x = x) = True.
Proof. exact (@lem5117993 Prop x). Qed.
Lemma lem5117995 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66822 : A) : ((term369 A z y _66822) = (term369 A z y _66822)) = True.
Proof. exact (@lem5117994 (term369 A z y _66822)). Qed.
Lemma lem5117996 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66822 : A) : ((term200 A y z _66822) = (term369 A z y _66822)) = True.
Proof. exact (TRANS (@lem5117991 A z y _66822) (@lem5117995 A z y _66822)). Qed.
Lemma lem5117997 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66822 : A) : True = ((term200 A y z _66822) = (term369 A z y _66822)).
Proof. exact (SYM (@lem5117996 A z y _66822)). Qed.
Lemma lem5117998 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66822 : A) : (term200 A y z _66822) = (term369 A z y _66822).
Proof. exact (EQ_MP (@lem5117997 A z y _66822) (@lem0)). Qed.
Lemma lem5117999 {A : Type'} (_66822 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term369 A z y _66822.
Proof. exact (EQ_MP (@lem5117998 A z y _66822) (@lem5117471 A _66822 x x'' y x''' z s h1)). Qed.
Lemma lem5118001 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5118002 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66822 : A) : (term369 A z y _66822) = (term403 A y z _66822).
Proof. exact (@lem5118001 (term397 A y _66822) (z _66822)). Qed.
Lemma lem5118004 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5118005 {A : Type'} (y : A -> Prop) (_66822 : A) : (term404 A y _66822) = (y _66822).
Proof. exact (@lem5118004 (y _66822)). Qed.
Lemma lem5118006 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5118007 {A : Type'} (y : A -> Prop) (_66822 : A) : (term405 A y _66822) = (term158 A y _66822).
Proof. exact (MK_COMB (@lem5118006) (@lem5118005 A y _66822)). Qed.
Lemma lem5118008 {A : Type'} (z : A -> Prop) (_66822 : A) : (z _66822) = (z _66822).
Proof. exact (eq_refl (z _66822)). Qed.
Lemma lem5118009 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66822 : A) : (term403 A y z _66822) = (term160 A y z _66822).
Proof. exact (MK_COMB (@lem5118007 A y _66822) (@lem5118008 A z _66822)). Qed.
Lemma lem5118010 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66822 : A) : (term369 A z y _66822) = (term160 A y z _66822).
Proof. exact (TRANS (@lem5118002 A y z _66822) (@lem5118009 A y z _66822)). Qed.
Lemma lem5118013 {A : Type'} (_66822 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A y z _66822.
Proof. exact (EQ_MP (@lem5118010 A y z _66822) (@lem5117999 A _66822 x x'' y x''' z s h1)). Qed.
Lemma lem5118014 {A : Type'} (_66822 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A y z _66822.
Proof. exact (@lem5118013 A _66822 x x'' y x''' z s h1). Qed.
Lemma lem5118015 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A y z x'''.
Proof. exact (@lem5118014 A x''' x x'' y x''' z s h1). Qed.
Lemma lem5118018 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : z x'''.
Proof. exact (@lem5118015 A x x'' y x''' z s h2 (@lem5117970 A y z x''' h1)). Qed.
Lemma lem5118019 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : term398 A z x'''.
Proof. exact (fun h0 : term397 A z x''' => @lem5118018 A x x'' y x''' z s h1 h2). Qed.
Lemma lem5118021 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5118022 {A : Type'} (z : A -> Prop) (x''' : A) : (term398 A z x''') = (z x''').
Proof. exact (@lem5118021 (z x''')). Qed.
Lemma lem5118023 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : z x'''.
Proof. exact (EQ_MP (@lem5118022 A z x''') (@lem5118019 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5118026 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5118028 {A : Type'} (z : A -> Prop) (x''' : A) : (term397 A z x''') = (term406 A z x''').
Proof. exact (@lem5118026 (z x''')). Qed.
Lemma lem5118031 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term228 A y z x''') : term406 A z x'''.
Proof. exact (EQ_MP (@lem5118028 A z x''') (@lem5117491 A y z x''' h1)). Qed.
Lemma lem5118034 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : False.
Proof. exact (@lem5118031 A y z x''' h1 (@lem5118023 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5118035 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : term407.
Proof. exact (fun h0 : ~ False => @lem5118034 A x x'' y x''' z s h1 h2). Qed.
Lemma lem5118037 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5118038 : term407 = False.
Proof. exact (@lem5118037 False). Qed.
Lemma lem5118039 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) : False.
Proof. exact (EQ_MP (@lem5118038) (@lem5118035 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5118041 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) (h1 : term228 A x z x') : x x'.
Proof. exact (proj1 (@lem5116458 A x z x' h1)). Qed.
Lemma lem5118042 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) (h1 : term228 A x z x') : term398 A x x'.
Proof. exact (fun h0 : term397 A x x' => @lem5118041 A x z x' h1). Qed.
Lemma lem5118044 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5118045 {A : Type'} (x : A -> Prop) (x' : A) : (term398 A x x') = (x x').
Proof. exact (@lem5118044 (x x')). Qed.
Lemma lem5118046 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) (h1 : term228 A x z x') : x x'.
Proof. exact (EQ_MP (@lem5118045 A x x') (@lem5118042 A x z x' h1)). Qed.
Lemma lem5118052 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5118053 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66830 : A) : (term200 A x y _66830) = (term369 A y x _66830).
Proof. exact (@lem5118052 (y _66830) (term397 A x _66830)). Qed.
Lemma lem5118059 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5118060 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66830 : A) : (term400 A x y _66830) = (term401 A y x _66830).
Proof. exact (MK_COMB (@lem5118059) (@lem5118053 A y x _66830)). Qed.
Lemma lem5118066 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66830 : A) : (term369 A y x _66830) = (term369 A y x _66830).
Proof. exact (eq_refl (term369 A y x _66830)). Qed.
Lemma lem5118067 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66830 : A) : ((term200 A x y _66830) = (term369 A y x _66830)) = ((term369 A y x _66830) = (term369 A y x _66830)).
Proof. exact (MK_COMB (@lem5118060 A y x _66830) (@lem5118066 A y x _66830)). Qed.
Lemma lem5118069 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5118070 (x : Prop) : (x = x) = True.
Proof. exact (@lem5118069 Prop x). Qed.
Lemma lem5118071 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66830 : A) : ((term369 A y x _66830) = (term369 A y x _66830)) = True.
Proof. exact (@lem5118070 (term369 A y x _66830)). Qed.
Lemma lem5118072 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66830 : A) : ((term200 A x y _66830) = (term369 A y x _66830)) = True.
Proof. exact (TRANS (@lem5118067 A y x _66830) (@lem5118071 A y x _66830)). Qed.
Lemma lem5118073 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66830 : A) : True = ((term200 A x y _66830) = (term369 A y x _66830)).
Proof. exact (SYM (@lem5118072 A y x _66830)). Qed.
Lemma lem5118074 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66830 : A) : (term200 A x y _66830) = (term369 A y x _66830).
Proof. exact (EQ_MP (@lem5118073 A y x _66830) (@lem0)). Qed.
Lemma lem5118075 {A : Type'} (_66830 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term369 A y x _66830.
Proof. exact (EQ_MP (@lem5118074 A y x _66830) (@lem5117527 A _66830 x x'' y x''' z s h1)). Qed.
Lemma lem5118077 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5118078 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_66830 : A) : (term369 A y x _66830) = (term403 A x y _66830).
Proof. exact (@lem5118077 (term397 A x _66830) (y _66830)). Qed.
Lemma lem5118080 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5118081 {A : Type'} (x : A -> Prop) (_66830 : A) : (term404 A x _66830) = (x _66830).
Proof. exact (@lem5118080 (x _66830)). Qed.
Lemma lem5118082 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5118083 {A : Type'} (x : A -> Prop) (_66830 : A) : (term405 A x _66830) = (term158 A x _66830).
Proof. exact (MK_COMB (@lem5118082) (@lem5118081 A x _66830)). Qed.
Lemma lem5118084 {A : Type'} (y : A -> Prop) (_66830 : A) : (y _66830) = (y _66830).
Proof. exact (eq_refl (y _66830)). Qed.
Lemma lem5118085 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_66830 : A) : (term403 A x y _66830) = (term160 A x y _66830).
Proof. exact (MK_COMB (@lem5118083 A x _66830) (@lem5118084 A y _66830)). Qed.
Lemma lem5118086 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_66830 : A) : (term369 A y x _66830) = (term160 A x y _66830).
Proof. exact (TRANS (@lem5118078 A x y _66830) (@lem5118085 A x y _66830)). Qed.
Lemma lem5118089 {A : Type'} (_66830 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A x y _66830.
Proof. exact (EQ_MP (@lem5118086 A x y _66830) (@lem5118075 A _66830 x x'' y x''' z s h1)). Qed.
Lemma lem5118090 {A : Type'} (_66830 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A x y _66830.
Proof. exact (@lem5118089 A _66830 x x'' y x''' z s h1). Qed.
Lemma lem5118091 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A x y x'.
Proof. exact (@lem5118090 A x' x x'' y x''' z s h1). Qed.
Lemma lem5118094 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x z x') (h2 : term344 A x x'' y x''' z s) : y x'.
Proof. exact (@lem5118091 A x' x x'' y x''' z s h2 (@lem5118046 A x z x' h1)). Qed.
Lemma lem5118095 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x z x') (h2 : term344 A x x'' y x''' z s) : term398 A y x'.
Proof. exact (fun h0 : term397 A y x' => @lem5118094 A x' x x'' y x''' z s h1 h2). Qed.
Lemma lem5118097 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5118098 {A : Type'} (y : A -> Prop) (x' : A) : (term398 A y x') = (y x').
Proof. exact (@lem5118097 (y x')). Qed.
Lemma lem5118099 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x z x') (h2 : term344 A x x'' y x''' z s) : y x'.
Proof. exact (EQ_MP (@lem5118098 A y x') (@lem5118095 A x' x x'' y x''' z s h1 h2)). Qed.
Lemma lem5118105 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5118106 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66828 : A) : (term200 A y z _66828) = (term369 A z y _66828).
Proof. exact (@lem5118105 (z _66828) (term397 A y _66828)). Qed.
Lemma lem5118112 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5118113 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66828 : A) : (term400 A y z _66828) = (term401 A z y _66828).
Proof. exact (MK_COMB (@lem5118112) (@lem5118106 A z y _66828)). Qed.
Lemma lem5118119 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66828 : A) : (term369 A z y _66828) = (term369 A z y _66828).
Proof. exact (eq_refl (term369 A z y _66828)). Qed.
Lemma lem5118120 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66828 : A) : ((term200 A y z _66828) = (term369 A z y _66828)) = ((term369 A z y _66828) = (term369 A z y _66828)).
Proof. exact (MK_COMB (@lem5118113 A z y _66828) (@lem5118119 A z y _66828)). Qed.
Lemma lem5118122 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5118123 (x : Prop) : (x = x) = True.
Proof. exact (@lem5118122 Prop x). Qed.
Lemma lem5118124 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66828 : A) : ((term369 A z y _66828) = (term369 A z y _66828)) = True.
Proof. exact (@lem5118123 (term369 A z y _66828)). Qed.
Lemma lem5118125 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66828 : A) : ((term200 A y z _66828) = (term369 A z y _66828)) = True.
Proof. exact (TRANS (@lem5118120 A z y _66828) (@lem5118124 A z y _66828)). Qed.
Lemma lem5118126 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66828 : A) : True = ((term200 A y z _66828) = (term369 A z y _66828)).
Proof. exact (SYM (@lem5118125 A z y _66828)). Qed.
Lemma lem5118127 {A : Type'} (z : A -> Prop) (y : A -> Prop) (_66828 : A) : (term200 A y z _66828) = (term369 A z y _66828).
Proof. exact (EQ_MP (@lem5118126 A z y _66828) (@lem0)). Qed.
Lemma lem5118128 {A : Type'} (_66828 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term369 A z y _66828.
Proof. exact (EQ_MP (@lem5118127 A z y _66828) (@lem5117515 A _66828 x x'' y x''' z s h1)). Qed.
Lemma lem5118130 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5118131 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66828 : A) : (term369 A z y _66828) = (term403 A y z _66828).
Proof. exact (@lem5118130 (term397 A y _66828) (z _66828)). Qed.
Lemma lem5118133 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5118134 {A : Type'} (y : A -> Prop) (_66828 : A) : (term404 A y _66828) = (y _66828).
Proof. exact (@lem5118133 (y _66828)). Qed.
Lemma lem5118135 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5118136 {A : Type'} (y : A -> Prop) (_66828 : A) : (term405 A y _66828) = (term158 A y _66828).
Proof. exact (MK_COMB (@lem5118135) (@lem5118134 A y _66828)). Qed.
Lemma lem5118137 {A : Type'} (z : A -> Prop) (_66828 : A) : (z _66828) = (z _66828).
Proof. exact (eq_refl (z _66828)). Qed.
Lemma lem5118138 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66828 : A) : (term403 A y z _66828) = (term160 A y z _66828).
Proof. exact (MK_COMB (@lem5118136 A y _66828) (@lem5118137 A z _66828)). Qed.
Lemma lem5118139 {A : Type'} (y : A -> Prop) (z : A -> Prop) (_66828 : A) : (term369 A z y _66828) = (term160 A y z _66828).
Proof. exact (TRANS (@lem5118131 A y z _66828) (@lem5118138 A y z _66828)). Qed.
Lemma lem5118142 {A : Type'} (_66828 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A y z _66828.
Proof. exact (EQ_MP (@lem5118139 A y z _66828) (@lem5118128 A _66828 x x'' y x''' z s h1)). Qed.
Lemma lem5118143 {A : Type'} (_66828 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A y z _66828.
Proof. exact (@lem5118142 A _66828 x x'' y x''' z s h1). Qed.
Lemma lem5118144 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A y z x'.
Proof. exact (@lem5118143 A x' x x'' y x''' z s h1). Qed.
Lemma lem5118147 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x z x') (h2 : term344 A x x'' y x''' z s) : z x'.
Proof. exact (@lem5118144 A x' x x'' y x''' z s h2 (@lem5118099 A x' x x'' y x''' z s h1 h2)). Qed.
Lemma lem5118148 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x z x') (h2 : term344 A x x'' y x''' z s) : term398 A z x'.
Proof. exact (fun h0 : term397 A z x' => @lem5118147 A x' x x'' y x''' z s h1 h2). Qed.
Lemma lem5118150 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5118151 {A : Type'} (z : A -> Prop) (x' : A) : (term398 A z x') = (z x').
Proof. exact (@lem5118150 (z x')). Qed.
Lemma lem5118152 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x z x') (h2 : term344 A x x'' y x''' z s) : z x'.
Proof. exact (EQ_MP (@lem5118151 A z x') (@lem5118148 A x' x x'' y x''' z s h1 h2)). Qed.
Lemma lem5118155 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5118157 {A : Type'} (z : A -> Prop) (x' : A) : (term397 A z x') = (term406 A z x').
Proof. exact (@lem5118155 (z x')). Qed.
Lemma lem5118160 {A : Type'} (x : A -> Prop) (z : A -> Prop) (x' : A) (h1 : term228 A x z x') : term406 A z x'.
Proof. exact (EQ_MP (@lem5118157 A z x') (@lem5117539 A x z x' h1)). Qed.
Lemma lem5118163 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x z x') (h2 : term344 A x x'' y x''' z s) : False.
Proof. exact (@lem5118160 A x z x' h1 (@lem5118152 A x' x x'' y x''' z s h1 h2)). Qed.
Lemma lem5118164 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x z x') (h2 : term344 A x x'' y x''' z s) : term407.
Proof. exact (fun h0 : ~ False => @lem5118163 A x' x x'' y x''' z s h1 h2). Qed.
Lemma lem5118166 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5118167 : term407 = False.
Proof. exact (@lem5118166 False). Qed.
Lemma lem5118168 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term228 A x z x') (h2 : term344 A x x'' y x''' z s) : False.
Proof. exact (EQ_MP (@lem5118167) (@lem5118164 A x' x x'' y x''' z s h1 h2)). Qed.
Lemma lem5118170 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term232 A y z x''') : z x'''.
Proof. exact (proj2 (@lem5116447 A y z x''' h1)). Qed.
Lemma lem5118171 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term232 A y z x''') : term398 A z x'''.
Proof. exact (fun h0 : term397 A z x''' => @lem5118170 A y z x''' h1). Qed.
Lemma lem5118173 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5118174 {A : Type'} (z : A -> Prop) (x''' : A) : (term398 A z x''') = (z x''').
Proof. exact (@lem5118173 (z x''')). Qed.
Lemma lem5118175 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term232 A y z x''') : z x'''.
Proof. exact (EQ_MP (@lem5118174 A z x''') (@lem5118171 A y z x''' h1)). Qed.
Lemma lem5118177 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5118178 {A : Type'} (z : A -> Prop) (x : A -> Prop) (_66835 : A) : (term369 A x z _66835) = (term403 A z x _66835).
Proof. exact (@lem5118177 (term397 A z _66835) (x _66835)). Qed.
Lemma lem5118180 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5118181 {A : Type'} (z : A -> Prop) (_66835 : A) : (term404 A z _66835) = (z _66835).
Proof. exact (@lem5118180 (z _66835)). Qed.
Lemma lem5118182 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5118183 {A : Type'} (z : A -> Prop) (_66835 : A) : (term405 A z _66835) = (term158 A z _66835).
Proof. exact (MK_COMB (@lem5118182) (@lem5118181 A z _66835)). Qed.
Lemma lem5118184 {A : Type'} (x : A -> Prop) (_66835 : A) : (x _66835) = (x _66835).
Proof. exact (eq_refl (x _66835)). Qed.
Lemma lem5118185 {A : Type'} (z : A -> Prop) (x : A -> Prop) (_66835 : A) : (term403 A z x _66835) = (term160 A z x _66835).
Proof. exact (MK_COMB (@lem5118183 A z _66835) (@lem5118184 A x _66835)). Qed.
Lemma lem5118186 {A : Type'} (z : A -> Prop) (x : A -> Prop) (_66835 : A) : (term369 A x z _66835) = (term160 A z x _66835).
Proof. exact (TRANS (@lem5118178 A z x _66835) (@lem5118185 A z x _66835)). Qed.
Lemma lem5118189 {A : Type'} (_66835 : A) (x : A -> Prop) (z : A -> Prop) (h1 : term384 A x z) : term160 A z x _66835.
Proof. exact (EQ_MP (@lem5118186 A z x _66835) (@lem5117577 A _66835 x z h1)). Qed.
Lemma lem5118190 {A : Type'} (_66835 : A) (x : A -> Prop) (z : A -> Prop) (h1 : term384 A x z) : term160 A z x _66835.
Proof. exact (@lem5118189 A _66835 x z h1). Qed.
Lemma lem5118191 {A : Type'} (x''' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term384 A x z) : term160 A z x x'''.
Proof. exact (@lem5118190 A x''' x z h1). Qed.
Lemma lem5118194 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term384 A x z) (h2 : term232 A y z x''') : x x'''.
Proof. exact (@lem5118191 A x''' x z h1 (@lem5118175 A y z x''' h2)). Qed.
Lemma lem5118195 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term384 A x z) (h2 : term232 A y z x''') : term398 A x x'''.
Proof. exact (fun h0 : term397 A x x''' => @lem5118194 A x y z x''' h1 h2). Qed.
Lemma lem5118197 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5118198 {A : Type'} (x : A -> Prop) (x''' : A) : (term398 A x x''') = (x x''').
Proof. exact (@lem5118197 (x x''')). Qed.
Lemma lem5118199 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term384 A x z) (h2 : term232 A y z x''') : x x'''.
Proof. exact (EQ_MP (@lem5118198 A x x''') (@lem5118195 A x y z x''' h1 h2)). Qed.
Lemma lem5118205 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5118206 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66834 : A) : (term200 A x y _66834) = (term369 A y x _66834).
Proof. exact (@lem5118205 (y _66834) (term397 A x _66834)). Qed.
Lemma lem5118212 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5118213 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66834 : A) : (term400 A x y _66834) = (term401 A y x _66834).
Proof. exact (MK_COMB (@lem5118212) (@lem5118206 A y x _66834)). Qed.
Lemma lem5118219 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66834 : A) : (term369 A y x _66834) = (term369 A y x _66834).
Proof. exact (eq_refl (term369 A y x _66834)). Qed.
Lemma lem5118220 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66834 : A) : ((term200 A x y _66834) = (term369 A y x _66834)) = ((term369 A y x _66834) = (term369 A y x _66834)).
Proof. exact (MK_COMB (@lem5118213 A y x _66834) (@lem5118219 A y x _66834)). Qed.
Lemma lem5118222 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5118223 (x : Prop) : (x = x) = True.
Proof. exact (@lem5118222 Prop x). Qed.
Lemma lem5118224 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66834 : A) : ((term369 A y x _66834) = (term369 A y x _66834)) = True.
Proof. exact (@lem5118223 (term369 A y x _66834)). Qed.
Lemma lem5118225 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66834 : A) : ((term200 A x y _66834) = (term369 A y x _66834)) = True.
Proof. exact (TRANS (@lem5118220 A y x _66834) (@lem5118224 A y x _66834)). Qed.
Lemma lem5118226 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66834 : A) : True = ((term200 A x y _66834) = (term369 A y x _66834)).
Proof. exact (SYM (@lem5118225 A y x _66834)). Qed.
Lemma lem5118227 {A : Type'} (y : A -> Prop) (x : A -> Prop) (_66834 : A) : (term200 A x y _66834) = (term369 A y x _66834).
Proof. exact (EQ_MP (@lem5118226 A y x _66834) (@lem0)). Qed.
Lemma lem5118228 {A : Type'} (_66834 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term369 A y x _66834.
Proof. exact (EQ_MP (@lem5118227 A y x _66834) (@lem5117563 A _66834 x x'' y x''' z s h1)). Qed.
Lemma lem5118230 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5118231 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_66834 : A) : (term369 A y x _66834) = (term403 A x y _66834).
Proof. exact (@lem5118230 (term397 A x _66834) (y _66834)). Qed.
Lemma lem5118233 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5118234 {A : Type'} (x : A -> Prop) (_66834 : A) : (term404 A x _66834) = (x _66834).
Proof. exact (@lem5118233 (x _66834)). Qed.
Lemma lem5118235 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5118236 {A : Type'} (x : A -> Prop) (_66834 : A) : (term405 A x _66834) = (term158 A x _66834).
Proof. exact (MK_COMB (@lem5118235) (@lem5118234 A x _66834)). Qed.
Lemma lem5118237 {A : Type'} (y : A -> Prop) (_66834 : A) : (y _66834) = (y _66834).
Proof. exact (eq_refl (y _66834)). Qed.
Lemma lem5118238 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_66834 : A) : (term403 A x y _66834) = (term160 A x y _66834).
Proof. exact (MK_COMB (@lem5118236 A x _66834) (@lem5118237 A y _66834)). Qed.
Lemma lem5118239 {A : Type'} (x : A -> Prop) (y : A -> Prop) (_66834 : A) : (term369 A y x _66834) = (term160 A x y _66834).
Proof. exact (TRANS (@lem5118231 A x y _66834) (@lem5118238 A x y _66834)). Qed.
Lemma lem5118242 {A : Type'} (_66834 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A x y _66834.
Proof. exact (EQ_MP (@lem5118239 A x y _66834) (@lem5118228 A _66834 x x'' y x''' z s h1)). Qed.
Lemma lem5118243 {A : Type'} (_66834 : A) (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A x y _66834.
Proof. exact (@lem5118242 A _66834 x x'' y x''' z s h1). Qed.
Lemma lem5118244 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term344 A x x'' y x''' z s) : term160 A x y x'''.
Proof. exact (@lem5118243 A x''' x x'' y x''' z s h1). Qed.
Lemma lem5118247 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term384 A x z) (h2 : term232 A y z x''') (h3 : term344 A x x'' y x''' z s) : y x'''.
Proof. exact (@lem5118244 A x x'' y x''' z s h3 (@lem5118199 A x y z x''' h1 h2)). Qed.
Lemma lem5118248 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term384 A x z) (h2 : term232 A y z x''') (h3 : term344 A x x'' y x''' z s) : term398 A y x'''.
Proof. exact (fun h0 : term397 A y x''' => @lem5118247 A x x'' y x''' z s h1 h2 h3). Qed.
Lemma lem5118250 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5118251 {A : Type'} (y : A -> Prop) (x''' : A) : (term398 A y x''') = (y x''').
Proof. exact (@lem5118250 (y x''')). Qed.
Lemma lem5118252 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term384 A x z) (h2 : term232 A y z x''') (h3 : term344 A x x'' y x''' z s) : y x'''.
Proof. exact (EQ_MP (@lem5118251 A y x''') (@lem5118248 A x x'' y x''' z s h1 h2 h3)). Qed.
Lemma lem5118255 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5118257 {A : Type'} (y : A -> Prop) (x''' : A) : (term397 A y x''') = (term406 A y x''').
Proof. exact (@lem5118255 (y x''')). Qed.
Lemma lem5118260 {A : Type'} (y : A -> Prop) (z : A -> Prop) (x''' : A) (h1 : term232 A y z x''') : term406 A y x'''.
Proof. exact (EQ_MP (@lem5118257 A y x''') (@lem5117569 A y z x''' h1)). Qed.
Lemma lem5118263 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term384 A x z) (h2 : term232 A y z x''') (h3 : term344 A x x'' y x''' z s) : False.
Proof. exact (@lem5118260 A y z x''' h2 (@lem5118252 A x x'' y x''' z s h1 h2 h3)). Qed.
Lemma lem5118264 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term384 A x z) (h2 : term232 A y z x''') (h3 : term344 A x x'' y x''' z s) : term407.
Proof. exact (fun h0 : ~ False => @lem5118263 A x x'' y x''' z s h1 h2 h3). Qed.
Lemma lem5118266 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5118267 : term407 = False.
Proof. exact (@lem5118266 False). Qed.
Lemma lem5118268 {A : Type'} (x : A -> Prop) (x'' : A) (y : A -> Prop) (x''' : A) (z : A -> Prop) (s : A -> Prop) (h1 : term384 A x z) (h2 : term232 A y z x''') (h3 : term344 A x x'' y x''' z s) : False.
Proof. exact (EQ_MP (@lem5118267) (@lem5118264 A x x'' y x''' z s h1 h2 h3)). Qed.
Lemma lem5118269 {A : Type'} (x'' : A) (y : A -> Prop) (x''' : A) (s : A -> Prop) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term232 A y z x''') (h2 : term344 A x x'' y x''' z s) (h3 : term393 A x' x z) : False.
Proof. exact (or_elim (@lem5116289 A x' x z h3) (fun h0 : term228 A x z x' => @lem5118168 A x' x x'' y x''' z s h0 h2) (fun h0 : term384 A x z => @lem5118268 A x x'' y x''' z s h0 h1 h2)). Qed.
Lemma lem5118270 {A : Type'} (x'' : A) (y : A -> Prop) (x''' : A) (s : A -> Prop) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) (h3 : term393 A x' x z) : False.
Proof. exact (or_elim (@lem5116289 A x' x z h3) (fun h0 : term228 A x z x' => @lem5117963 A x x'' y x''' z s h1 h2) (fun h0 : term384 A x z => @lem5118039 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5118271 {A : Type'} (x'' : A) (y : A -> Prop) (x''' : A) (s : A -> Prop) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term344 A x x'' y x''' z s) (h2 : term393 A x' x z) : False.
Proof. exact (or_elim (@lem5116416 A x x'' y x''' z s h1) (fun h0 : term228 A y z x''' => @lem5118270 A x'' y x''' s x' x z h0 h1 h2) (fun h0 : term232 A y z x''' => @lem5118269 A x'' y x''' s x' x z h0 h1 h2)). Qed.
Lemma lem5118272 {A : Type'} (x'' : A) (y : A -> Prop) (x''' : A) (s : A -> Prop) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term228 A x y x'') (h2 : term344 A x x'' y x''' z s) (h3 : term393 A x' x z) : False.
Proof. exact (or_elim (@lem5116289 A x' x z h3) (fun h0 : term228 A x z x' => @lem5117811 A x x'' y x''' z s h1 h2) (fun h0 : term384 A x z => @lem5117887 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5118273 {A : Type'} (x'' : A) (y : A -> Prop) (x''' : A) (s : A -> Prop) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term228 A y z x''') (h2 : term344 A x x'' y x''' z s) (h3 : term393 A x' x z) : False.
Proof. exact (or_elim (@lem5116289 A x' x z h3) (fun h0 : term228 A x z x' => @lem5117659 A x x'' y x''' z s h1 h2) (fun h0 : term384 A x z => @lem5117735 A x x'' y x''' z s h1 h2)). Qed.
Lemma lem5118274 {A : Type'} (x'' : A) (y : A -> Prop) (x''' : A) (s : A -> Prop) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term228 A x y x'') (h2 : term344 A x x'' y x''' z s) (h3 : term393 A x' x z) : False.
Proof. exact (or_elim (@lem5116416 A x x'' y x''' z s h2) (fun h0 : term228 A y z x''' => @lem5118273 A x'' y x''' s x' x z h0 h2 h3) (fun h0 : term232 A y z x''' => @lem5118272 A x'' y x''' s x' x z h1 h2 h3)). Qed.
Lemma lem5118275 {A : Type'} (x'' : A) (y : A -> Prop) (x''' : A) (s : A -> Prop) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term344 A x x'' y x''' z s) (h2 : term393 A x' x z) : False.
Proof. exact (or_elim (@lem5116420 A x x'' y x''' z s h1) (fun h0 : term228 A x y x'' => @lem5118274 A x'' y x''' s x' x z h0 h1 h2) (fun h0 : term232 A x y x'' => @lem5118271 A x'' y x''' s x' x z h1 h2)). Qed.
Lemma lem5118276 {A : Type'} (x'' : A) (y : A -> Prop) (x''' : A) (s : A -> Prop) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term344 A x x'' y x''' z s) (h2 : term393 A x' x z) : (term344 A x x'' y x''' z s) = False.
Proof. exact (prop_ext (fun h3 : term344 A x x'' y x''' z s => @lem5118275 A x'' y x''' s x' x z h1 h2) (fun h3 : False => @lem5116411 A x x'' y x''' z s h1)). Qed.
Lemma lem5118277 {A : Type'} (x'' : A) (y : A -> Prop) (x''' : A) (s : A -> Prop) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term344 A x x'' y x''' z s) (h2 : term393 A x' x z) : False.
Proof. exact (EQ_MP (@lem5118276 A x'' y x''' s x' x z h1 h2) (@lem5116411 A x x'' y x''' z s h1)). Qed.
Lemma lem5118278 {A : Type'} (x'' : A) (y : A -> Prop) (x''' : A) (s : A -> Prop) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term344 A x x'' y x''' z s) (h2 : term393 A x' x z) : (term393 A x' x z) = False.
Proof. exact (prop_ext (fun h3 : term393 A x' x z => @lem5118277 A x'' y x''' s x' x z h1 h2) (fun h3 : False => @lem5116289 A x' x z h2)). Qed.
Lemma lem5118279 {A : Type'} (x'' : A) (y : A -> Prop) (x''' : A) (s : A -> Prop) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term344 A x x'' y x''' z s) (h2 : term393 A x' x z) : False.
Proof. exact (EQ_MP (@lem5118278 A x'' y x''' s x' x z h1 h2) (@lem5116289 A x' x z h2)). Qed.
Lemma lem5118280 {A : Type'} (x'' : A) (y : A -> Prop) (s : A -> Prop) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term347 A x x'' y z s) (h2 : term393 A x' x z) : False.
Proof. exact (ex_elim (@lem5116242 A x x'' y z s h1) (fun x''' : A => fun h0 : term346 A x x'' y z s x''' => @lem5118279 A x'' y x''' s x' x z h0 h2)). Qed.
Lemma lem5118281 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x' : A) (x : A -> Prop) (z : A -> Prop) (h1 : term177 A x y z s) (h2 : term393 A x' x z) : False.
Proof. exact (ex_elim (@lem5116054 A x y z s h1) (fun x'' : A => fun h0 : term348 A x y z s x'' => @lem5118280 A x'' y s x' x z h0 h2)). Qed.
Lemma lem5118282 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (h1 : term199 A x z) (h2 : term177 A x y z s) : False.
Proof. exact (ex_elim (@lem5116240 A x z h1) (fun x' : A => fun h0 : term395 A x z x' => @lem5118281 A y s x' x z h2 h0)). Qed.
Lemma lem5118283 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (h1 : term199 A x z) (h2 : term177 A x y z s) : (term199 A x z) = False.
Proof. exact (prop_ext (fun h3 : term199 A x z => @lem5118282 A x y z s h1 h2) (fun h3 : False => @lem5115391 A x z h1)). Qed.
Lemma lem5118284 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (h1 : term199 A x z) (h2 : term177 A x y z s) : False.
Proof. exact (EQ_MP (@lem5118283 A x y z s h1 h2) (@lem5115391 A x z h1)). Qed.
Lemma lem5118285 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (h1 : term177 A x y z s) : term198 A x z.
Proof. exact (fun h0 : term199 A x z => @lem5118284 A x y z s h0 h1). Qed.
Lemma lem5118286 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) (s : A -> Prop) (h1 : term177 A x y z s) : term171 A x z.
Proof. exact (EQ_MP (@lem5115390 A x z) (@lem5118285 A x y z s h1)). Qed.
Lemma lem5118287 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) (z : A -> Prop) : term179 A y s x z.
Proof. exact (fun h0 : term177 A x y z s => @lem5118286 A x y z s h0). Qed.
Lemma lem5118292 {A : Type'} (y : A -> Prop) (s : A -> Prop) (x : A -> Prop) : term181 A y s x.
Proof. exact (fun z : A -> Prop => @lem5118287 A y s x z). Qed.
Lemma lem5118297 {A : Type'} (s : A -> Prop) (x : A -> Prop) : term183 A s x.
Proof. exact (fun y : A -> Prop => @lem5118292 A y s x). Qed.
Lemma lem5118302 {A : Type'} (s : A -> Prop) : term185 A s.
Proof. exact (fun x : A -> Prop => @lem5118297 A s x). Qed.
Lemma lem5118307 {A : Type'} : term197 A.
Proof. exact (fun s : A -> Prop => @lem5118302 A s). Qed.
Lemma lem5118308 {A : Type'} : term196 A.
Proof. exact (EQ_MP (@lem5115385 A) (@lem5118307 A)). Qed.
Lemma lem5118309 {A : Type'} (s : A -> Prop) : term408 A s.
Proof. exact (@lem5118308 A s). Qed.
Lemma lem5118310 {A : Type'} (s : A -> Prop) : (term408 A s) = (term187 A s).
Proof. exact (eq_refl (term408 A s)). Qed.
Lemma lem5118311 {A : Type'} (s : A -> Prop) : term187 A s.
Proof. exact (EQ_MP (@lem5118310 A s) (@lem5118309 A s)). Qed.
Lemma lem5118313 {A : Type'} (s : A -> Prop) : term187 A s.
Proof. exact (@lem5115092 A s (@lem5118311 A s)). Qed.
Lemma lem5118314 {A : Type'} (s : A -> Prop) (h1 : term188 A s) : False.
Proof. exact (@lem5118313 A s (@lem5115076 A s h1)). Qed.
Lemma lem5118315 {A : Type'} (s : A -> Prop) (h1 : term188 A s) : (term188 A s) = False.
Proof. exact (prop_ext (fun h2 : term188 A s => @lem5118314 A s h1) (fun h2 : False => @lem5115076 A s h1)). Qed.
Lemma lem5118316 {A : Type'} (s : A -> Prop) (h1 : term188 A s) : False.
Proof. exact (EQ_MP (@lem5118315 A s h1) (@lem5115076 A s h1)). Qed.
Lemma lem5118317 {A : Type'} (s : A -> Prop) : term187 A s.
Proof. exact (fun h0 : term188 A s => @lem5118316 A s h0). Qed.
Lemma lem5118318 {A : Type'} (s : A -> Prop) : term185 A s.
Proof. exact (EQ_MP (@lem5115075 A s) (@lem5118317 A s)). Qed.
Lemma lem5118319 {A : Type'} (s : A -> Prop) : term155 A s.
Proof. exact (EQ_MP (@lem5115071 A s) (@lem5118318 A s)). Qed.
Lemma lem5118320 {A : Type'} (s : A -> Prop) : term96 A s.
Proof. exact (EQ_MP (@lem5114774 A s) (@lem5118319 A s)). Qed.
Lemma lem5118322 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (EQ_MP (@lem5113438 A s) (@lem5113437 A s)). Qed.
Lemma lem5118323 {A : Type'} (s : type686 A) : term409 A s.
Proof. exact (@lem5118322 (A -> Prop) s). Qed.
Lemma lem5118324 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term410 A t s.
Proof. exact (@lem5118323 A (term110 A t s)). Qed.
Lemma lem5118325 {A : Type'} (s : A -> Prop) : term411 A s.
Proof. exact (@lem4603107 A s). Qed.
Lemma lem5118326 {A : Type'} (s : A -> Prop) : (term411 A s) = (term412 A s).
Proof. exact (eq_refl (term411 A s)). Qed.
Lemma lem5118327 {A : Type'} (s : A -> Prop) : term412 A s.
Proof. exact (EQ_MP (@lem5118326 A s) (@lem5118325 A s)). Qed.
Lemma lem5118328 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5118329 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term413 A s.
Proof. exact (@lem5118327 A s (@lem5118328 A s h1)). Qed.
Lemma lem5118330 {A : Type'} (s : A -> Prop) : (term413 A s) = ((term413 A s) = True).
Proof. exact (@lem7 (term413 A s)). Qed.
Lemma lem5118331 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term413 A s) = True.
Proof. exact (EQ_MP (@lem5118330 A s) (@lem5118329 A s h1)). Qed.
Lemma lem5118337 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem5118342 {A : Type'} (s : A -> Prop) : term414 A s.
Proof. exact (fun h0 : @FINITE A s => @lem5118331 A s h0). Qed.
Lemma lem5118343 {A : Type'} (s : A -> Prop) : term414 A s.
Proof. exact (@lem5118342 A s). Qed.
Lemma lem5118345 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem5118337 A s) (@lem5113475 A s h1)). Qed.
Lemma lem5118346 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : True = (@FINITE A s).
Proof. exact (SYM (@lem5118345 A s h1)). Qed.
Lemma lem5118347 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem5118346 A s h1) (@lem0)). Qed.
Lemma lem5118348 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term413 A s) = True.
Proof. exact (@lem5118343 A s (@lem5118347 A s h1)). Qed.
Lemma lem5118349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5118350 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term415 A s) = (and True).
Proof. exact (MK_COMB (@lem5118349) (@lem5118348 A s h1)). Qed.
Lemma lem5118361 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term416 A t s) = (term416 A t s).
Proof. exact (eq_refl (term416 A t s)). Qed.
Lemma lem5118362 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term417 A t s) = (term418 A t s).
Proof. exact (MK_COMB (@lem5118350 A s h1) (@lem5118361 A t s)). Qed.
Lemma lem5118364 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5118365 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term418 A t s) = (term416 A t s).
Proof. exact (@lem5118364 (term416 A t s)). Qed.
Lemma lem5118376 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term417 A t s) = (term416 A t s).
Proof. exact (TRANS (@lem5118362 A t s h1) (@lem5118365 A t s)). Qed.
Lemma lem5118377 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term416 A t s) = (term417 A t s).
Proof. exact (SYM (@lem5118376 A t s h1)). Qed.
Lemma lem5118379 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5118380 {A : Type'} (s : type686 A) (t : type686 A) : (@SUBSET (A -> Prop) s t) = (term419 A s t).
Proof. exact (@lem5118379 (A -> Prop) s t). Qed.
Lemma lem5118381 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term416 A t s) = (term420 A t s).
Proof. exact (@lem5118380 A (term110 A t s) (term421 A s)). Qed.
Lemma lem5118395 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term117 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem5118396 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term117 A s t).
Proof. exact (@lem5118395 A s t). Qed.
Lemma lem5118397 {A : Type'} (y : A -> Prop) (t : A -> Prop) : (@PSUBSET A y t) = (term117 A y t).
Proof. exact (@lem5118396 A y t). Qed.
Lemma lem5118401 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5118402 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (@lem5118401 A s t). Qed.
Lemma lem5118403 {A : Type'} (y : A -> Prop) (t : A -> Prop) : (@SUBSET A y t) = (term119 A y t).
Proof. exact (@lem5118402 A y t). Qed.
Lemma lem5118410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5118411 {A : Type'} (y : A -> Prop) (t : A -> Prop) : (term133 A y t) = (term134 A y t).
Proof. exact (MK_COMB (@lem5118410) (@lem5118403 A y t)). Qed.
Lemma lem5118415 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term135 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem5118416 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term135 A s t).
Proof. exact (@lem5118415 A s t). Qed.
Lemma lem5118417 {A : Type'} (y : A -> Prop) (t : A -> Prop) : (y = t) = (term135 A y t).
Proof. exact (@lem5118416 A y t). Qed.
Lemma lem5118426 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5118427 {A : Type'} (y : A -> Prop) (t : A -> Prop) : (term136 A y t) = (term137 A y t).
Proof. exact (MK_COMB (@lem5118426) (@lem5118417 A y t)). Qed.
Lemma lem5118428 {A : Type'} (y : A -> Prop) (t : A -> Prop) : (term117 A y t) = (term138 A y t).
Proof. exact (MK_COMB (@lem5118411 A y t) (@lem5118427 A y t)). Qed.
Lemma lem5118431 {A : Type'} (y : A -> Prop) (t : A -> Prop) : (@PSUBSET A y t) = (term138 A y t).
Proof. exact (TRANS (@lem5118397 A y t) (@lem5118428 A y t)). Qed.
Lemma lem5118432 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5118433 {A : Type'} (y : A -> Prop) (t : A -> Prop) : (term78 A y t) = (term139 A y t).
Proof. exact (MK_COMB (@lem5118432) (@lem5118431 A y t)). Qed.
Lemma lem5118435 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5118436 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (@lem5118435 A s t). Qed.
Lemma lem5118437 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term119 A t s).
Proof. exact (@lem5118436 A t s). Qed.
Lemma lem5118444 {A : Type'} (y : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term47 A y t s) = (term140 A y t s).
Proof. exact (MK_COMB (@lem5118433 A y t) (@lem5118437 A t s)). Qed.
Lemma lem5118447 {A : Type'} (GEN_PVAR_227 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_227) = (@SETSPEC (A -> Prop) GEN_PVAR_227).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_227)). Qed.
Lemma lem5118448 {A : Type'} (GEN_PVAR_227 : A -> Prop) (y : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term100 A GEN_PVAR_227 y t s) = (term422 A GEN_PVAR_227 y t s).
Proof. exact (MK_COMB (@lem5118447 A GEN_PVAR_227) (@lem5118444 A y t s)). Qed.
Lemma lem5118449 {A : Type'} (y : A -> Prop) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5118450 {A : Type'} (GEN_PVAR_227 : A -> Prop) (t : A -> Prop) (s : A -> Prop) (y : A -> Prop) : (term102 A GEN_PVAR_227 t s y) = (term423 A GEN_PVAR_227 t s y).
Proof. exact (MK_COMB (@lem5118448 A GEN_PVAR_227 y t s) (@lem5118449 A y)). Qed.
Lemma lem5118451 {A : Type'} (GEN_PVAR_227 : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term104 A GEN_PVAR_227 t s) = (term424 A GEN_PVAR_227 t s).
Proof. exact (fun_ext (fun y : A -> Prop => @lem5118450 A GEN_PVAR_227 t s y)). Qed.
Lemma lem5118452 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5118453 {A : Type'} (GEN_PVAR_227 : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term106 A GEN_PVAR_227 t s) = (term425 A GEN_PVAR_227 t s).
Proof. exact (MK_COMB (@lem5118452 A) (@lem5118451 A GEN_PVAR_227 t s)). Qed.
Lemma lem5118458 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term108 A t s) = (term426 A t s).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A -> Prop => @lem5118453 A GEN_PVAR_227 t s)). Qed.
Lemma lem5118459 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem5118460 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term110 A t s) = (term427 A t s).
Proof. exact (MK_COMB (@lem5118459 A) (@lem5118458 A t s)). Qed.
Lemma lem5118461 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem5118462 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term428 A x t s) = (term429 A x t s).
Proof. exact (MK_COMB (@lem5118461 A x) (@lem5118460 A t s)). Qed.
Lemma lem5118463 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5118464 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term430 A x t s) = (term431 A x t s).
Proof. exact (MK_COMB (@lem5118463) (@lem5118462 A x t s)). Qed.
Lemma lem5118470 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem5118471 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term119 A s t).
Proof. exact (@lem5118470 A s t). Qed.
Lemma lem5118472 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term119 A t s).
Proof. exact (@lem5118471 A t s). Qed.
Lemma lem5118479 {A : Type'} (GEN_PVAR_228 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_228) = (@SETSPEC (A -> Prop) GEN_PVAR_228).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_228)). Qed.
Lemma lem5118480 {A : Type'} (GEN_PVAR_228 : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term432 A GEN_PVAR_228 t s) = (term433 A GEN_PVAR_228 t s).
Proof. exact (MK_COMB (@lem5118479 A GEN_PVAR_228) (@lem5118472 A t s)). Qed.
Lemma lem5118481 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5118482 {A : Type'} (GEN_PVAR_228 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term434 A GEN_PVAR_228 s t) = (term435 A GEN_PVAR_228 s t).
Proof. exact (MK_COMB (@lem5118480 A GEN_PVAR_228 t s) (@lem5118481 A t)). Qed.
Lemma lem5118483 {A : Type'} (GEN_PVAR_228 : A -> Prop) (s : A -> Prop) : (term436 A GEN_PVAR_228 s) = (term437 A GEN_PVAR_228 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5118482 A GEN_PVAR_228 s t)). Qed.
Lemma lem5118484 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5118485 {A : Type'} (GEN_PVAR_228 : A -> Prop) (s : A -> Prop) : (term438 A GEN_PVAR_228 s) = (term439 A GEN_PVAR_228 s).
Proof. exact (MK_COMB (@lem5118484 A) (@lem5118483 A GEN_PVAR_228 s)). Qed.
Lemma lem5118490 {A : Type'} (s : A -> Prop) : (term440 A s) = (term441 A s).
Proof. exact (fun_ext (fun GEN_PVAR_228 : A -> Prop => @lem5118485 A GEN_PVAR_228 s)). Qed.
Lemma lem5118491 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem5118492 {A : Type'} (s : A -> Prop) : (term421 A s) = (term442 A s).
Proof. exact (MK_COMB (@lem5118491 A) (@lem5118490 A s)). Qed.
Lemma lem5118493 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem5118494 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term443 A x s) = (term444 A x s).
Proof. exact (MK_COMB (@lem5118493 A x) (@lem5118492 A s)). Qed.
Lemma lem5118495 {A : Type'} (t : A -> Prop) (x : A -> Prop) (s : A -> Prop) : (term445 A t x s) = (term446 A t x s).
Proof. exact (MK_COMB (@lem5118464 A x t s) (@lem5118494 A x s)). Qed.
Lemma lem5118498 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term447 A t s) = (term448 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem5118495 A t x s)). Qed.
Lemma lem5118499 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5118500 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term420 A t s) = (term449 A t s).
Proof. exact (MK_COMB (@lem5118499 A) (@lem5118498 A t s)). Qed.
Lemma lem5118505 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term416 A t s) = (term449 A t s).
Proof. exact (TRANS (@lem5118381 A t s) (@lem5118500 A t s)). Qed.
Lemma lem5118506 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term449 A t s) = (term416 A t s).
Proof. exact (SYM (@lem5118505 A t s)). Qed.
Lemma lem5118514 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term450 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem5118515 {A : Type'} (p : type686 A) (x : A -> Prop) : (term451 A x p) = (p x).
Proof. exact (@lem5118514 (A -> Prop) p x). Qed.
Lemma lem5118516 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A -> Prop) : (term452 A x t s) = (term453 A t s x).
Proof. exact (@lem5118515 A (term454 A t s) x). Qed.
Lemma lem5118517 {A : Type'} (y : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term453 A t s y) = (term140 A y t s).
Proof. exact (eq_refl (term453 A t s y)). Qed.
Lemma lem5118518 {A : Type'} (GEN_PVAR_227 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_227) = (@SETSPEC (A -> Prop) GEN_PVAR_227).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_227)). Qed.
Lemma lem5118519 {A : Type'} (GEN_PVAR_227 : A -> Prop) (y : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term455 A GEN_PVAR_227 t s y) = (term422 A GEN_PVAR_227 y t s).
Proof. exact (MK_COMB (@lem5118518 A GEN_PVAR_227) (@lem5118517 A y t s)). Qed.
Lemma lem5118520 {A : Type'} (y : A -> Prop) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5118521 {A : Type'} (GEN_PVAR_227 : A -> Prop) (t : A -> Prop) (s : A -> Prop) (y : A -> Prop) : (term456 A GEN_PVAR_227 t s y) = (term423 A GEN_PVAR_227 t s y).
Proof. exact (MK_COMB (@lem5118519 A GEN_PVAR_227 y t s) (@lem5118520 A y)). Qed.
Lemma lem5118522 {A : Type'} (GEN_PVAR_227 : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term457 A GEN_PVAR_227 t s) = (term424 A GEN_PVAR_227 t s).
Proof. exact (fun_ext (fun y : A -> Prop => @lem5118521 A GEN_PVAR_227 t s y)). Qed.
Lemma lem5118523 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5118524 {A : Type'} (GEN_PVAR_227 : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term458 A GEN_PVAR_227 t s) = (term425 A GEN_PVAR_227 t s).
Proof. exact (MK_COMB (@lem5118523 A) (@lem5118522 A GEN_PVAR_227 t s)). Qed.
Lemma lem5118525 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term459 A t s) = (term426 A t s).
Proof. exact (fun_ext (fun GEN_PVAR_227 : A -> Prop => @lem5118524 A GEN_PVAR_227 t s)). Qed.
Lemma lem5118526 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem5118527 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term460 A t s) = (term427 A t s).
Proof. exact (MK_COMB (@lem5118526 A) (@lem5118525 A t s)). Qed.
Lemma lem5118528 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem5118529 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term452 A x t s) = (term429 A x t s).
Proof. exact (MK_COMB (@lem5118528 A x) (@lem5118527 A t s)). Qed.
Lemma lem5118530 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5118531 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term461 A x t s) = (term462 A x t s).
Proof. exact (MK_COMB (@lem5118530) (@lem5118529 A x t s)). Qed.
Lemma lem5118532 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term453 A t s x) = (term140 A x t s).
Proof. exact (eq_refl (term453 A t s x)). Qed.
Lemma lem5118533 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : ((term452 A x t s) = (term453 A t s x)) = ((term429 A x t s) = (term140 A x t s)).
Proof. exact (MK_COMB (@lem5118531 A x t s) (@lem5118532 A x t s)). Qed.
Lemma lem5118534 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term429 A x t s) = (term140 A x t s).
Proof. exact (EQ_MP (@lem5118533 A x t s) (@lem5118516 A t s x)). Qed.
Lemma lem5118546 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5118547 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5118546 A P x). Qed.
Lemma lem5118548 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem5118547 A x x'). Qed.
Lemma lem5118549 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5118550 {A : Type'} (x : A -> Prop) (x' : A) : (term157 A x' x) = (term158 A x x').
Proof. exact (MK_COMB (@lem5118549) (@lem5118548 A x x')). Qed.
Lemma lem5118552 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5118553 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5118552 A P x). Qed.
Lemma lem5118554 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem5118553 A t x). Qed.
Lemma lem5118555 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term159 A x x' t) = (term160 A x t x').
Proof. exact (MK_COMB (@lem5118550 A x x') (@lem5118554 A t x')). Qed.
Lemma lem5118558 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term161 A x t) = (term162 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5118555 A x t x')). Qed.
Lemma lem5118559 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5118560 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term119 A x t) = (term163 A x t).
Proof. exact (MK_COMB (@lem5118559 A) (@lem5118558 A x t)). Qed.
Lemma lem5118565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5118566 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term134 A x t) = (term164 A x t).
Proof. exact (MK_COMB (@lem5118565) (@lem5118560 A x t)). Qed.
Lemma lem5118574 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5118575 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5118574 A P x). Qed.
Lemma lem5118576 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem5118575 A x x'). Qed.
Lemma lem5118577 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5118578 {A : Type'} (x : A -> Prop) (x' : A) : (term165 A x' x) = (term166 A x x').
Proof. exact (MK_COMB (@lem5118577) (@lem5118576 A x x')). Qed.
Lemma lem5118580 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5118581 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5118580 A P x). Qed.
Lemma lem5118582 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem5118581 A t x). Qed.
Lemma lem5118583 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : ((@IN A x' x) = (@IN A x' t)) = ((x x') = (t x')).
Proof. exact (MK_COMB (@lem5118578 A x x') (@lem5118582 A t x')). Qed.
Lemma lem5118586 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term167 A x t) = (term168 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5118583 A x t x')). Qed.
Lemma lem5118587 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5118588 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term135 A x t) = (term169 A x t).
Proof. exact (MK_COMB (@lem5118587 A) (@lem5118586 A x t)). Qed.
Lemma lem5118593 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5118594 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term137 A x t) = (term170 A x t).
Proof. exact (MK_COMB (@lem5118593) (@lem5118588 A x t)). Qed.
Lemma lem5118595 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term138 A x t) = (term171 A x t).
Proof. exact (MK_COMB (@lem5118566 A x t) (@lem5118594 A x t)). Qed.
Lemma lem5118598 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5118599 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term139 A x t) = (term172 A x t).
Proof. exact (MK_COMB (@lem5118598) (@lem5118595 A x t)). Qed.
Lemma lem5118607 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5118608 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5118607 A P x). Qed.
Lemma lem5118609 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem5118608 A t x). Qed.
Lemma lem5118610 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5118611 {A : Type'} (t : A -> Prop) (x : A) : (term157 A x t) = (term158 A t x).
Proof. exact (MK_COMB (@lem5118610) (@lem5118609 A t x)). Qed.
Lemma lem5118613 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5118614 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5118613 A P x). Qed.
Lemma lem5118615 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5118614 A s x). Qed.
Lemma lem5118616 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term159 A t x s) = (term160 A t s x).
Proof. exact (MK_COMB (@lem5118611 A t x) (@lem5118615 A s x)). Qed.
Lemma lem5118619 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term161 A t s) = (term162 A t s).
Proof. exact (fun_ext (fun x : A => @lem5118616 A t s x)). Qed.
Lemma lem5118620 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5118621 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term119 A t s) = (term163 A t s).
Proof. exact (MK_COMB (@lem5118620 A) (@lem5118619 A t s)). Qed.
Lemma lem5118626 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term140 A x t s) = (term173 A x t s).
Proof. exact (MK_COMB (@lem5118599 A x t) (@lem5118621 A t s)). Qed.
Lemma lem5118629 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term429 A x t s) = (term173 A x t s).
Proof. exact (TRANS (@lem5118534 A x t s) (@lem5118626 A x t s)). Qed.
Lemma lem5118630 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5118631 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term431 A x t s) = (term463 A x t s).
Proof. exact (MK_COMB (@lem5118630) (@lem5118629 A x t s)). Qed.
Lemma lem5118633 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term450 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem5118634 {A : Type'} (p : type686 A) (x : A -> Prop) : (term451 A x p) = (p x).
Proof. exact (@lem5118633 (A -> Prop) p x). Qed.
Lemma lem5118635 {A : Type'} (s : A -> Prop) (x : A -> Prop) : (term464 A x s) = (term465 A s x).
Proof. exact (@lem5118634 A (term466 A s) x). Qed.
Lemma lem5118636 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term465 A s t) = (term119 A t s).
Proof. exact (eq_refl (term465 A s t)). Qed.
Lemma lem5118637 {A : Type'} (GEN_PVAR_228 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_228) = (@SETSPEC (A -> Prop) GEN_PVAR_228).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_228)). Qed.
Lemma lem5118638 {A : Type'} (GEN_PVAR_228 : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term467 A GEN_PVAR_228 s t) = (term433 A GEN_PVAR_228 t s).
Proof. exact (MK_COMB (@lem5118637 A GEN_PVAR_228) (@lem5118636 A t s)). Qed.
Lemma lem5118639 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem5118640 {A : Type'} (GEN_PVAR_228 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term468 A GEN_PVAR_228 s t) = (term435 A GEN_PVAR_228 s t).
Proof. exact (MK_COMB (@lem5118638 A GEN_PVAR_228 t s) (@lem5118639 A t)). Qed.
Lemma lem5118641 {A : Type'} (GEN_PVAR_228 : A -> Prop) (s : A -> Prop) : (term469 A GEN_PVAR_228 s) = (term437 A GEN_PVAR_228 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5118640 A GEN_PVAR_228 s t)). Qed.
Lemma lem5118642 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem5118643 {A : Type'} (GEN_PVAR_228 : A -> Prop) (s : A -> Prop) : (term470 A GEN_PVAR_228 s) = (term439 A GEN_PVAR_228 s).
Proof. exact (MK_COMB (@lem5118642 A) (@lem5118641 A GEN_PVAR_228 s)). Qed.
Lemma lem5118644 {A : Type'} (s : A -> Prop) : (term471 A s) = (term441 A s).
Proof. exact (fun_ext (fun GEN_PVAR_228 : A -> Prop => @lem5118643 A GEN_PVAR_228 s)). Qed.
Lemma lem5118645 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem5118646 {A : Type'} (s : A -> Prop) : (term472 A s) = (term442 A s).
Proof. exact (MK_COMB (@lem5118645 A) (@lem5118644 A s)). Qed.
Lemma lem5118647 {A : Type'} (x : A -> Prop) : (@IN (A -> Prop) x) = (@IN (A -> Prop) x).
Proof. exact (eq_refl (@IN (A -> Prop) x)). Qed.
Lemma lem5118648 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term464 A x s) = (term444 A x s).
Proof. exact (MK_COMB (@lem5118647 A x) (@lem5118646 A s)). Qed.
Lemma lem5118649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5118650 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term473 A x s) = (term474 A x s).
Proof. exact (MK_COMB (@lem5118649) (@lem5118648 A x s)). Qed.
Lemma lem5118651 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term465 A s x) = (term119 A x s).
Proof. exact (eq_refl (term465 A s x)). Qed.
Lemma lem5118652 {A : Type'} (x : A -> Prop) (s : A -> Prop) : ((term464 A x s) = (term465 A s x)) = ((term444 A x s) = (term119 A x s)).
Proof. exact (MK_COMB (@lem5118650 A x s) (@lem5118651 A x s)). Qed.
Lemma lem5118653 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term444 A x s) = (term119 A x s).
Proof. exact (EQ_MP (@lem5118652 A x s) (@lem5118635 A s x)). Qed.
Lemma lem5118661 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5118662 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5118661 A P x). Qed.
Lemma lem5118663 {A : Type'} (x : A -> Prop) (x' : A) : (@IN A x' x) = (x x').
Proof. exact (@lem5118662 A x x'). Qed.
Lemma lem5118664 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5118665 {A : Type'} (x : A -> Prop) (x' : A) : (term157 A x' x) = (term158 A x x').
Proof. exact (MK_COMB (@lem5118664) (@lem5118663 A x x')). Qed.
Lemma lem5118667 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem5118668 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem5118667 A P x). Qed.
Lemma lem5118669 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem5118668 A s x). Qed.
Lemma lem5118670 {A : Type'} (x : A -> Prop) (s : A -> Prop) (x' : A) : (term159 A x x' s) = (term160 A x s x').
Proof. exact (MK_COMB (@lem5118665 A x x') (@lem5118669 A s x')). Qed.
Lemma lem5118673 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term161 A x s) = (term162 A x s).
Proof. exact (fun_ext (fun x' : A => @lem5118670 A x s x')). Qed.
Lemma lem5118674 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5118675 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term119 A x s) = (term163 A x s).
Proof. exact (MK_COMB (@lem5118674 A) (@lem5118673 A x s)). Qed.
Lemma lem5118680 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term444 A x s) = (term163 A x s).
Proof. exact (TRANS (@lem5118653 A x s) (@lem5118675 A x s)). Qed.
Lemma lem5118681 {A : Type'} (t : A -> Prop) (x : A -> Prop) (s : A -> Prop) : (term446 A t x s) = (term475 A t x s).
Proof. exact (MK_COMB (@lem5118631 A x t s) (@lem5118680 A x s)). Qed.
Lemma lem5118684 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term448 A t s) = (term476 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem5118681 A t x s)). Qed.
Lemma lem5118685 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5118686 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term449 A t s) = (term477 A t s).
Proof. exact (MK_COMB (@lem5118685 A) (@lem5118684 A t s)). Qed.
Lemma lem5118691 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term477 A t s) = (term449 A t s).
Proof. exact (SYM (@lem5118686 A t s)). Qed.
Lemma lem5118693 (p : Prop) : p = (term186 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5118694 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term477 A t s) = (term478 A t s).
Proof. exact (@lem5118693 (term477 A t s)). Qed.
Lemma lem5118695 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term478 A t s) = (term477 A t s).
Proof. exact (SYM (@lem5118694 A t s)). Qed.
Lemma lem5118696 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term479 A t s) : term479 A t s.
Proof. exact (h1). Qed.
Lemma lem5118699 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term478 A t s) : term478 A t s.
Proof. exact (h1). Qed.
Lemma lem5118700 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term480 A t s.
Proof. exact (fun h0 : term478 A t s => @lem5118699 A t s h0). Qed.
Lemma lem5118701 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term480 A t s) : term480 A t s.
Proof. exact (h1). Qed.
Lemma lem5118702 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term478 A t s) : term478 A t s.
Proof. exact (h1). Qed.
Lemma lem5118703 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term478 A t s) (h2 : term480 A t s) : term478 A t s.
Proof. exact (@lem5118701 A t s h2 (@lem5118702 A t s h1)). Qed.
Lemma lem5118704 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term478 A t s) : term481 A t s.
Proof. exact (fun h0 : term480 A t s => @lem5118703 A t s h1 h0). Qed.
Lemma lem5118705 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term480 A t s) : term480 A t s.
Proof. exact (h1). Qed.
Lemma lem5118706 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term478 A t s) (h2 : term480 A t s) : term478 A t s.
Proof. exact (@lem5118704 A t s h1 (@lem5118705 A t s h2)). Qed.
Lemma lem5118707 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term480 A t s) : term480 A t s.
Proof. exact (fun h0 : term478 A t s => @lem5118706 A t s h0 h1). Qed.
Lemma lem5118708 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term482 A t s.
Proof. exact (fun h0 : term480 A t s => @lem5118707 A t s h0). Qed.
Lemma lem5118711 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term480 A t s.
Proof. exact (@lem5118708 A t s (@lem5118700 A t s)). Qed.
Lemma lem5118712 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term480 A t s.
Proof. exact (@lem5118711 A t s). Qed.
Lemma lem5118722 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5118723 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term478 A t s) = (term483 A t s).
Proof. exact (@lem5118722 (term479 A t s)). Qed.
Lemma lem5118725 (t : Prop) : (term193 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5118726 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term483 A t s) = (term477 A t s).
Proof. exact (@lem5118725 (term477 A t s)). Qed.
Lemma lem5118731 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term478 A t s) = (term477 A t s).
Proof. exact (TRANS (@lem5118723 A t s) (@lem5118726 A t s)). Qed.
Lemma lem5118760 {A : Type'} (s : A -> Prop) : (term484 A s) = (term485 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5118731 A t s)). Qed.
Lemma lem5118761 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5118762 {A : Type'} (s : A -> Prop) : (term486 A s) = (term487 A s).
Proof. exact (MK_COMB (@lem5118761 A) (@lem5118760 A s)). Qed.
Lemma lem5118767 {A : Type'} : (term488 A) = (term489 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5118762 A s)). Qed.
Lemma lem5118768 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5118777 {A : Type'} : (term490 A) = (term491 A).
Proof. exact (MK_COMB (@lem5118768 A) (@lem5118767 A)). Qed.
Lemma lem5118782 {A : Type'} (x : A -> Prop) (s : A -> Prop) (x' : A) : (term160 A x s x') = (term160 A x s x').
Proof. exact (eq_refl (term160 A x s x')). Qed.
Lemma lem5118783 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term162 A x s) = (term162 A x s).
Proof. exact (fun_ext (fun x' : A => @lem5118782 A x s x')). Qed.
Lemma lem5118784 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5118785 {A : Type'} (x : A -> Prop) (s : A -> Prop) : (term163 A x s) = (term163 A x s).
Proof. exact (MK_COMB (@lem5118784 A) (@lem5118783 A x s)). Qed.
Lemma lem5118790 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term160 A t s x) = (term160 A t s x).
Proof. exact (eq_refl (term160 A t s x)). Qed.
Lemma lem5118791 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term162 A t s) = (term162 A t s).
Proof. exact (fun_ext (fun x : A => @lem5118790 A t s x)). Qed.
Lemma lem5118792 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5118793 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term163 A t s) = (term163 A t s).
Proof. exact (MK_COMB (@lem5118792 A) (@lem5118791 A t s)). Qed.
Lemma lem5118798 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : ((x x') = (t x')) = ((x x') = (t x')).
Proof. exact (eq_refl ((x x') = (t x'))). Qed.
Lemma lem5118799 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term168 A x t) = (term168 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5118798 A x t x')). Qed.
Lemma lem5118800 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5118801 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term169 A x t) = (term169 A x t).
Proof. exact (MK_COMB (@lem5118800 A) (@lem5118799 A x t)). Qed.
Lemma lem5118802 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5118803 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term170 A x t) = (term170 A x t).
Proof. exact (MK_COMB (@lem5118802) (@lem5118801 A x t)). Qed.
Lemma lem5118808 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term160 A x t x') = (term160 A x t x').
Proof. exact (eq_refl (term160 A x t x')). Qed.
Lemma lem5118809 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term162 A x t) = (term162 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5118808 A x t x')). Qed.
Lemma lem5118810 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5118811 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term163 A x t) = (term163 A x t).
Proof. exact (MK_COMB (@lem5118810 A) (@lem5118809 A x t)). Qed.
Lemma lem5118812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5118813 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term164 A x t) = (term164 A x t).
Proof. exact (MK_COMB (@lem5118812) (@lem5118811 A x t)). Qed.
Lemma lem5118814 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term171 A x t) = (term171 A x t).
Proof. exact (MK_COMB (@lem5118813 A x t) (@lem5118803 A x t)). Qed.
Lemma lem5118815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5118816 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term172 A x t) = (term172 A x t).
Proof. exact (MK_COMB (@lem5118815) (@lem5118814 A x t)). Qed.
Lemma lem5118817 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term173 A x t s) = (term173 A x t s).
Proof. exact (MK_COMB (@lem5118816 A x t) (@lem5118793 A t s)). Qed.
Lemma lem5118818 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5118819 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term463 A x t s) = (term463 A x t s).
Proof. exact (MK_COMB (@lem5118818) (@lem5118817 A x t s)). Qed.
Lemma lem5118820 {A : Type'} (t : A -> Prop) (x : A -> Prop) (s : A -> Prop) : (term475 A t x s) = (term475 A t x s).
Proof. exact (MK_COMB (@lem5118819 A x t s) (@lem5118785 A x s)). Qed.
Lemma lem5118821 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term476 A t s) = (term476 A t s).
Proof. exact (fun_ext (fun x : A -> Prop => @lem5118820 A t x s)). Qed.
Lemma lem5118822 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5118823 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term477 A t s) = (term477 A t s).
Proof. exact (MK_COMB (@lem5118822 A) (@lem5118821 A t s)). Qed.
Lemma lem5118824 {A : Type'} (s : A -> Prop) : (term485 A s) = (term485 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5118823 A t s)). Qed.
Lemma lem5118825 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5118826 {A : Type'} (s : A -> Prop) : (term487 A s) = (term487 A s).
Proof. exact (MK_COMB (@lem5118825 A) (@lem5118824 A s)). Qed.
Lemma lem5118827 {A : Type'} : (term489 A) = (term489 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5118826 A s)). Qed.
Lemma lem5118828 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5118829 {A : Type'} : (term491 A) = (term491 A).
Proof. exact (MK_COMB (@lem5118828 A) (@lem5118827 A)). Qed.
Lemma lem5118886 {A : Type'} : (term490 A) = (term491 A).
Proof. exact (TRANS (@lem5118777 A) (@lem5118829 A)). Qed.
Lemma lem5118887 {A : Type'} : (term491 A) = (term490 A).
Proof. exact (SYM (@lem5118886 A)). Qed.
Lemma lem5118888 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) (h1 : term173 A x t s) : term173 A x t s.
Proof. exact (h1). Qed.
Lemma lem5118891 (p : Prop) : p = (term186 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5118892 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (term492 A s x').
Proof. exact (@lem5118891 (s x')). Qed.
Lemma lem5118893 {A : Type'} (s : A -> Prop) (x' : A) : (term492 A s x') = (s x').
Proof. exact (SYM (@lem5118892 A s x')). Qed.
Lemma lem5118894 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term397 A s x') : term397 A s x'.
Proof. exact (h1). Qed.
Lemma lem5118901 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term160 A x t x') = (term200 A x t x').
Proof. exact (@lem17265 (x x') (t x')). Qed.
Lemma lem5118902 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term162 A x t) = (term201 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5118901 A x t x')). Qed.
Lemma lem5118903 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5118904 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term163 A x t) = (term202 A x t).
Proof. exact (MK_COMB (@lem5118903 A) (@lem5118902 A x t)). Qed.
Lemma lem5118919 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term203 A x t x') = (term204 A x t x').
Proof. exact (@lem17646 (x x') (t x')). Qed.
Lemma lem5118920 {A : Type'} (P : A -> Prop) : (term205 A P) = (term206 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5118921 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term170 A x t) = (term207 A x t).
Proof. exact (@lem5118920 A (term168 A x t)). Qed.
Lemma lem5118922 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term208 A x t x') = ((x x') = (t x')).
Proof. exact (eq_refl (term208 A x t x')). Qed.
Lemma lem5118923 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5118924 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term209 A x t x') = (term203 A x t x').
Proof. exact (MK_COMB (@lem5118923) (@lem5118922 A x t x')). Qed.
Lemma lem5118925 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term209 A x t x') = (term204 A x t x').
Proof. exact (TRANS (@lem5118924 A x t x') (@lem5118919 A x t x')). Qed.
Lemma lem5118926 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term210 A x t) = (term211 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5118925 A x t x')). Qed.
Lemma lem5118927 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5118928 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term207 A x t) = (term212 A x t).
Proof. exact (MK_COMB (@lem5118927 A) (@lem5118926 A x t)). Qed.
Lemma lem5118929 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term170 A x t) = (term212 A x t).
Proof. exact (TRANS (@lem5118921 A x t) (@lem5118928 A x t)). Qed.
Lemma lem5118930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5118931 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term164 A x t) = (term213 A x t).
Proof. exact (MK_COMB (@lem5118930) (@lem5118904 A x t)). Qed.
Lemma lem5118932 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term171 A x t) = (term214 A x t).
Proof. exact (MK_COMB (@lem5118931 A x t) (@lem5118929 A x t)). Qed.
Lemma lem5118939 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term160 A t s x) = (term200 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem5118940 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term162 A t s) = (term201 A t s).
Proof. exact (fun_ext (fun x : A => @lem5118939 A t s x)). Qed.
Lemma lem5118941 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5118942 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term163 A t s) = (term202 A t s).
Proof. exact (MK_COMB (@lem5118941 A) (@lem5118940 A t s)). Qed.
Lemma lem5118943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5118944 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term172 A x t) = (term215 A x t).
Proof. exact (MK_COMB (@lem5118943) (@lem5118932 A x t)). Qed.
Lemma lem5118945 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term173 A x t s) = (term216 A x t s).
Proof. exact (MK_COMB (@lem5118944 A x t) (@lem5118942 A t s)). Qed.
Lemma lem5118979 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5118980 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (@lem5118979 A P Q). Qed.
Lemma lem5118981 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term223 A x t) = (term224 A x t).
Proof. exact (@lem5118980 A (term225 A x t) (term226 A x t)). Qed.
Lemma lem5118982 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term227 A x t x') = (term228 A x t x').
Proof. exact (eq_refl (term227 A x t x')). Qed.
Lemma lem5118983 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5118984 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term229 A x t x') = (term230 A x t x').
Proof. exact (MK_COMB (@lem5118983) (@lem5118982 A x t x')). Qed.
Lemma lem5118985 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term231 A x t x') = (term232 A x t x').
Proof. exact (eq_refl (term231 A x t x')). Qed.
Lemma lem5118986 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term233 A x t x') = (term204 A x t x').
Proof. exact (MK_COMB (@lem5118984 A x t x') (@lem5118985 A x t x')). Qed.
Lemma lem5118987 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term234 A x t) = (term211 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5118986 A x t x')). Qed.
Lemma lem5118988 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5118989 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term223 A x t) = (term212 A x t).
Proof. exact (MK_COMB (@lem5118988 A) (@lem5118987 A x t)). Qed.
Lemma lem5118990 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5118991 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term235 A x t) = (term236 A x t).
Proof. exact (MK_COMB (@lem5118990) (@lem5118989 A x t)). Qed.
Lemma lem5118992 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term227 A x t x') = (term228 A x t x').
Proof. exact (eq_refl (term227 A x t x')). Qed.
Lemma lem5118993 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term237 A x t) = (term225 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5118992 A x t x')). Qed.
Lemma lem5118994 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5118995 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term238 A x t) = (term239 A x t).
Proof. exact (MK_COMB (@lem5118994 A) (@lem5118993 A x t)). Qed.
Lemma lem5118996 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5118997 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term240 A x t) = (term241 A x t).
Proof. exact (MK_COMB (@lem5118996) (@lem5118995 A x t)). Qed.
Lemma lem5118998 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term231 A x t x') = (term232 A x t x').
Proof. exact (eq_refl (term231 A x t x')). Qed.
Lemma lem5118999 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term242 A x t) = (term226 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5118998 A x t x')). Qed.
Lemma lem5119000 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5119001 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term243 A x t) = (term244 A x t).
Proof. exact (MK_COMB (@lem5119000 A) (@lem5118999 A x t)). Qed.
Lemma lem5119002 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term224 A x t) = (term245 A x t).
Proof. exact (MK_COMB (@lem5118997 A x t) (@lem5119001 A x t)). Qed.
Lemma lem5119003 {A : Type'} (x : A -> Prop) (t : A -> Prop) : ((term223 A x t) = (term224 A x t)) = ((term212 A x t) = (term245 A x t)).
Proof. exact (MK_COMB (@lem5118991 A x t) (@lem5119002 A x t)). Qed.
Lemma lem5119004 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term212 A x t) = (term245 A x t).
Proof. exact (EQ_MP (@lem5119003 A x t) (@lem5118981 A x t)). Qed.
Lemma lem5119065 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term213 A x t) = (term213 A x t).
Proof. exact (eq_refl (term213 A x t)). Qed.
Lemma lem5119066 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term214 A x t) = (term246 A x t).
Proof. exact (MK_COMB (@lem5119065 A x t) (@lem5119004 A x t)). Qed.
Lemma lem5119067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5119068 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term215 A x t) = (term247 A x t).
Proof. exact (MK_COMB (@lem5119067) (@lem5119066 A x t)). Qed.
Lemma lem5119101 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term202 A t s) = (term202 A t s).
Proof. exact (eq_refl (term202 A t s)). Qed.
Lemma lem5119102 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term216 A x t s) = (term248 A x t s).
Proof. exact (MK_COMB (@lem5119068 A x t) (@lem5119101 A t s)). Qed.
Lemma lem5119104 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term222 A P Q) = (term221 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5119105 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term222 A P Q) = (term221 A P Q).
Proof. exact (@lem5119104 A P Q). Qed.
Lemma lem5119106 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term224 A x t) = (term223 A x t).
Proof. exact (@lem5119105 A (term225 A x t) (term226 A x t)). Qed.
Lemma lem5119107 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term227 A x t x') = (term228 A x t x').
Proof. exact (eq_refl (term227 A x t x')). Qed.
Lemma lem5119108 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term237 A x t) = (term225 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5119107 A x t x')). Qed.
Lemma lem5119109 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5119110 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term238 A x t) = (term239 A x t).
Proof. exact (MK_COMB (@lem5119109 A) (@lem5119108 A x t)). Qed.
Lemma lem5119111 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5119112 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term240 A x t) = (term241 A x t).
Proof. exact (MK_COMB (@lem5119111) (@lem5119110 A x t)). Qed.
Lemma lem5119113 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term231 A x t x') = (term232 A x t x').
Proof. exact (eq_refl (term231 A x t x')). Qed.
Lemma lem5119114 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term242 A x t) = (term226 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5119113 A x t x')). Qed.
Lemma lem5119115 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5119116 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term243 A x t) = (term244 A x t).
Proof. exact (MK_COMB (@lem5119115 A) (@lem5119114 A x t)). Qed.
Lemma lem5119117 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term224 A x t) = (term245 A x t).
Proof. exact (MK_COMB (@lem5119112 A x t) (@lem5119116 A x t)). Qed.
Lemma lem5119118 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5119119 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term253 A x t) = (term254 A x t).
Proof. exact (MK_COMB (@lem5119118) (@lem5119117 A x t)). Qed.
Lemma lem5119120 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term227 A x t x') = (term228 A x t x').
Proof. exact (eq_refl (term227 A x t x')). Qed.
Lemma lem5119121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5119122 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term229 A x t x') = (term230 A x t x').
Proof. exact (MK_COMB (@lem5119121) (@lem5119120 A x t x')). Qed.
Lemma lem5119123 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term231 A x t x') = (term232 A x t x').
Proof. exact (eq_refl (term231 A x t x')). Qed.
Lemma lem5119124 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term233 A x t x') = (term204 A x t x').
Proof. exact (MK_COMB (@lem5119122 A x t x') (@lem5119123 A x t x')). Qed.
Lemma lem5119125 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term234 A x t) = (term211 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5119124 A x t x')). Qed.
Lemma lem5119126 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5119127 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term223 A x t) = (term212 A x t).
Proof. exact (MK_COMB (@lem5119126 A) (@lem5119125 A x t)). Qed.
Lemma lem5119128 {A : Type'} (x : A -> Prop) (t : A -> Prop) : ((term224 A x t) = (term223 A x t)) = ((term245 A x t) = (term212 A x t)).
Proof. exact (MK_COMB (@lem5119119 A x t) (@lem5119127 A x t)). Qed.
Lemma lem5119129 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term245 A x t) = (term212 A x t).
Proof. exact (EQ_MP (@lem5119128 A x t) (@lem5119106 A x t)). Qed.
Lemma lem5119130 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term213 A x t) = (term213 A x t).
Proof. exact (eq_refl (term213 A x t)). Qed.
Lemma lem5119131 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term246 A x t) = (term214 A x t).
Proof. exact (MK_COMB (@lem5119130 A x t) (@lem5119129 A x t)). Qed.
Lemma lem5119133 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5119134 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (@lem5119133 A P Q). Qed.
Lemma lem5119135 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term257 A x t) = (term258 A x t).
Proof. exact (@lem5119134 A (term202 A x t) (term211 A x t)). Qed.
Lemma lem5119136 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term259 A x t x') = (term204 A x t x').
Proof. exact (eq_refl (term259 A x t x')). Qed.
Lemma lem5119137 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term260 A x t) = (term211 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5119136 A x t x')). Qed.
Lemma lem5119138 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5119139 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term261 A x t) = (term212 A x t).
Proof. exact (MK_COMB (@lem5119138 A) (@lem5119137 A x t)). Qed.
Lemma lem5119140 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term213 A x t) = (term213 A x t).
Proof. exact (eq_refl (term213 A x t)). Qed.
Lemma lem5119141 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term257 A x t) = (term214 A x t).
Proof. exact (MK_COMB (@lem5119140 A x t) (@lem5119139 A x t)). Qed.
Lemma lem5119142 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5119143 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term262 A x t) = (term263 A x t).
Proof. exact (MK_COMB (@lem5119142) (@lem5119141 A x t)). Qed.
Lemma lem5119144 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term259 A x t x') = (term204 A x t x').
Proof. exact (eq_refl (term259 A x t x')). Qed.
Lemma lem5119145 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term213 A x t) = (term213 A x t).
Proof. exact (eq_refl (term213 A x t)). Qed.
Lemma lem5119146 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term264 A x t x') = (term265 A x t x').
Proof. exact (MK_COMB (@lem5119145 A x t) (@lem5119144 A x t x')). Qed.
Lemma lem5119147 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term266 A x t) = (term267 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5119146 A x t x')). Qed.
Lemma lem5119148 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5119149 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term258 A x t) = (term268 A x t).
Proof. exact (MK_COMB (@lem5119148 A) (@lem5119147 A x t)). Qed.
Lemma lem5119150 {A : Type'} (x : A -> Prop) (t : A -> Prop) : ((term257 A x t) = (term258 A x t)) = ((term214 A x t) = (term268 A x t)).
Proof. exact (MK_COMB (@lem5119143 A x t) (@lem5119149 A x t)). Qed.
Lemma lem5119151 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term214 A x t) = (term268 A x t).
Proof. exact (EQ_MP (@lem5119150 A x t) (@lem5119135 A x t)). Qed.
Lemma lem5119152 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term246 A x t) = (term268 A x t).
Proof. exact (TRANS (@lem5119131 A x t) (@lem5119151 A x t)). Qed.
Lemma lem5119153 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5119154 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term247 A x t) = (term269 A x t).
Proof. exact (MK_COMB (@lem5119153) (@lem5119152 A x t)). Qed.
Lemma lem5119155 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term202 A t s) = (term202 A t s).
Proof. exact (eq_refl (term202 A t s)). Qed.
Lemma lem5119156 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term248 A x t s) = (term270 A x t s).
Proof. exact (MK_COMB (@lem5119154 A x t) (@lem5119155 A t s)). Qed.
Lemma lem5119158 {A : Type'} (P : A -> Prop) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5119159 {A : Type'} (P : A -> Prop) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (@lem5119158 A P Q). Qed.
Lemma lem5119160 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term273 A x t s) = (term274 A x t s).
Proof. exact (@lem5119159 A (term267 A x t) (term202 A t s)). Qed.
Lemma lem5119161 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term275 A x t x') = (term265 A x t x').
Proof. exact (eq_refl (term275 A x t x')). Qed.
Lemma lem5119162 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term276 A x t) = (term267 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5119161 A x t x')). Qed.
Lemma lem5119163 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5119164 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term277 A x t) = (term268 A x t).
Proof. exact (MK_COMB (@lem5119163 A) (@lem5119162 A x t)). Qed.
Lemma lem5119165 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5119166 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term278 A x t) = (term269 A x t).
Proof. exact (MK_COMB (@lem5119165) (@lem5119164 A x t)). Qed.
Lemma lem5119167 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term202 A t s) = (term202 A t s).
Proof. exact (eq_refl (term202 A t s)). Qed.
Lemma lem5119168 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term273 A x t s) = (term270 A x t s).
Proof. exact (MK_COMB (@lem5119166 A x t) (@lem5119167 A t s)). Qed.
Lemma lem5119169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5119170 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term279 A x t s) = (term280 A x t s).
Proof. exact (MK_COMB (@lem5119169) (@lem5119168 A x t s)). Qed.
Lemma lem5119171 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term275 A x t x') = (term265 A x t x').
Proof. exact (eq_refl (term275 A x t x')). Qed.
Lemma lem5119172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5119173 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term281 A x t x') = (term282 A x t x').
Proof. exact (MK_COMB (@lem5119172) (@lem5119171 A x t x')). Qed.
Lemma lem5119174 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term202 A t s) = (term202 A t s).
Proof. exact (eq_refl (term202 A t s)). Qed.
Lemma lem5119175 {A : Type'} (x : A -> Prop) (x' : A) (t : A -> Prop) (s : A -> Prop) : (term283 A x x' t s) = (term284 A x x' t s).
Proof. exact (MK_COMB (@lem5119173 A x t x') (@lem5119174 A t s)). Qed.
Lemma lem5119176 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term285 A x t s) = (term286 A x t s).
Proof. exact (fun_ext (fun x' : A => @lem5119175 A x x' t s)). Qed.
Lemma lem5119177 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5119178 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term274 A x t s) = (term287 A x t s).
Proof. exact (MK_COMB (@lem5119177 A) (@lem5119176 A x t s)). Qed.
Lemma lem5119179 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : ((term273 A x t s) = (term274 A x t s)) = ((term270 A x t s) = (term287 A x t s)).
Proof. exact (MK_COMB (@lem5119170 A x t s) (@lem5119178 A x t s)). Qed.
Lemma lem5119180 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term270 A x t s) = (term287 A x t s).
Proof. exact (EQ_MP (@lem5119179 A x t s) (@lem5119160 A x t s)). Qed.
Lemma lem5119181 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term248 A x t s) = (term287 A x t s).
Proof. exact (TRANS (@lem5119156 A x t s) (@lem5119180 A x t s)). Qed.
Lemma lem5119182 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term216 A x t s) = (term287 A x t s).
Proof. exact (TRANS (@lem5119102 A x t s) (@lem5119181 A x t s)). Qed.
Lemma lem5119183 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) : (term173 A x t s) = (term287 A x t s).
Proof. exact (TRANS (@lem5118945 A x t s) (@lem5119182 A x t s)). Qed.
Lemma lem5119184 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) (h1 : term173 A x t s) : term287 A x t s.
Proof. exact (EQ_MP (@lem5119183 A x t s) (@lem5118888 A x t s h1)). Qed.
Lemma lem5119190 {A : Type'} (x : A -> Prop) (x' : A) (h1 : x x') : x x'.
Proof. exact (h1). Qed.
Lemma lem5119196 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term397 A s x') : term397 A s x'.
Proof. exact (h1). Qed.
Lemma lem5119197 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term284 A x x'' t s.
Proof. exact (h1). Qed.
Lemma lem5119201 {A : Type'} (x : A -> Prop) (x' : A) (h1 : x x') : x x'.
Proof. exact (h1). Qed.
Lemma lem5119207 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term397 A s x') : term397 A s x'.
Proof. exact (h1). Qed.
Lemma lem5119218 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term200 A t s x) = (term200 A t s x).
Proof. exact (eq_refl (term200 A t s x)). Qed.
Lemma lem5119219 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term201 A t s) = (term201 A t s).
Proof. exact (fun_ext (fun x : A => @lem5119218 A t s x)). Qed.
Lemma lem5119220 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5119221 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term202 A t s) = (term202 A t s).
Proof. exact (MK_COMB (@lem5119220 A) (@lem5119219 A t s)). Qed.
Lemma lem5119246 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x'' : A) : (term204 A x t x'') = (term204 A x t x'').
Proof. exact (eq_refl (term204 A x t x'')). Qed.
Lemma lem5119257 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term200 A x t x') = (term200 A x t x').
Proof. exact (eq_refl (term200 A x t x')). Qed.
Lemma lem5119258 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term201 A x t) = (term201 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5119257 A x t x')). Qed.
Lemma lem5119259 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5119260 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term202 A x t) = (term202 A x t).
Proof. exact (MK_COMB (@lem5119259 A) (@lem5119258 A x t)). Qed.
Lemma lem5119261 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5119262 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term213 A x t) = (term213 A x t).
Proof. exact (MK_COMB (@lem5119261) (@lem5119260 A x t)). Qed.
Lemma lem5119263 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x'' : A) : (term265 A x t x'') = (term265 A x t x'').
Proof. exact (MK_COMB (@lem5119262 A x t) (@lem5119246 A x t x'')). Qed.
Lemma lem5119264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5119265 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x'' : A) : (term282 A x t x'') = (term282 A x t x'').
Proof. exact (MK_COMB (@lem5119264) (@lem5119263 A x t x'')). Qed.
Lemma lem5119266 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) : (term284 A x x'' t s) = (term284 A x x'' t s).
Proof. exact (MK_COMB (@lem5119265 A x t x'') (@lem5119221 A t s)). Qed.
Lemma lem5119267 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term284 A x x'' t s.
Proof. exact (EQ_MP (@lem5119266 A x x'' t s) (@lem5119197 A x x'' t s h1)). Qed.
Lemma lem5119268 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term202 A t s.
Proof. exact (proj2 (@lem5119267 A x x'' t s h1)). Qed.
Lemma lem5119269 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term265 A x t x''.
Proof. exact (proj1 (@lem5119267 A x x'' t s h1)). Qed.
Lemma lem5119270 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term204 A x t x''.
Proof. exact (proj2 (@lem5119269 A x x'' t s h1)). Qed.
Lemma lem5119271 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term202 A x t.
Proof. exact (proj1 (@lem5119269 A x x'' t s h1)). Qed.
Lemma lem5119272 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x'' : A) (h1 : term228 A x t x'') : term228 A x t x''.
Proof. exact (h1). Qed.
Lemma lem5119306 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term200 A x t x') = (term200 A x t x').
Proof. exact (eq_refl (term200 A x t x')). Qed.
Lemma lem5119307 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term201 A x t) = (term201 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5119306 A x t x')). Qed.
Lemma lem5119308 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5119310 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term202 A x t) = (term202 A x t).
Proof. exact (MK_COMB (@lem5119308 A) (@lem5119307 A x t)). Qed.
Lemma lem5119311 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term202 A x t.
Proof. exact (EQ_MP (@lem5119310 A x t) (@lem5119271 A x x'' t s h1)). Qed.
Lemma lem5119323 {A : Type'} (x : A -> Prop) (x' : A) (h1 : x x') : x x'.
Proof. exact (h1). Qed.
Lemma lem5119327 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term397 A s x') : term397 A s x'.
Proof. exact (h1). Qed.
Lemma lem5119335 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term200 A t s x) = (term200 A t s x).
Proof. exact (eq_refl (term200 A t s x)). Qed.
Lemma lem5119336 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term201 A t s) = (term201 A t s).
Proof. exact (fun_ext (fun x : A => @lem5119335 A t s x)). Qed.
Lemma lem5119337 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5119339 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term202 A t s) = (term202 A t s).
Proof. exact (MK_COMB (@lem5119337 A) (@lem5119336 A t s)). Qed.
Lemma lem5119340 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term202 A t s.
Proof. exact (EQ_MP (@lem5119339 A t s) (@lem5119268 A x x'' t s h1)). Qed.
Lemma lem5119348 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x' : A) : (term200 A x t x') = (term200 A x t x').
Proof. exact (eq_refl (term200 A x t x')). Qed.
Lemma lem5119349 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term201 A x t) = (term201 A x t).
Proof. exact (fun_ext (fun x' : A => @lem5119348 A x t x')). Qed.
Lemma lem5119350 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5119352 {A : Type'} (x : A -> Prop) (t : A -> Prop) : (term202 A x t) = (term202 A x t).
Proof. exact (MK_COMB (@lem5119350 A) (@lem5119349 A x t)). Qed.
Lemma lem5119353 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term202 A x t.
Proof. exact (EQ_MP (@lem5119352 A x t) (@lem5119271 A x x'' t s h1)). Qed.
Lemma lem5119365 {A : Type'} (_66838 : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term372 A x t _66838.
Proof. exact (@lem5119311 A x x'' t s h1 _66838). Qed.
Lemma lem5119366 {A : Type'} (x : A -> Prop) (t : A -> Prop) (_66838 : A) : (term372 A x t _66838) = (term200 A x t _66838).
Proof. exact (eq_refl (term372 A x t _66838)). Qed.
Lemma lem5119368 {A : Type'} (_66839 : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term372 A t s _66839.
Proof. exact (@lem5119340 A x x'' t s h1 _66839). Qed.
Lemma lem5119369 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_66839 : A) : (term372 A t s _66839) = (term200 A t s _66839).
Proof. exact (eq_refl (term372 A t s _66839)). Qed.
Lemma lem5119371 {A : Type'} (_66840 : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term372 A x t _66840.
Proof. exact (@lem5119353 A x x'' t s h1 _66840). Qed.
Lemma lem5119372 {A : Type'} (x : A -> Prop) (t : A -> Prop) (_66840 : A) : (term372 A x t _66840) = (term200 A x t _66840).
Proof. exact (eq_refl (term372 A x t _66840)). Qed.
Lemma lem5119389 {A : Type'} (_66838 : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term200 A x t _66838.
Proof. exact (EQ_MP (@lem5119366 A x t _66838) (@lem5119365 A _66838 x x'' t s h1)). Qed.
Lemma lem5119393 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x'' : A) (h1 : term228 A x t x'') : term397 A t x''.
Proof. exact (proj2 (@lem5119272 A x t x'' h1)). Qed.
Lemma lem5119395 {A : Type'} (x : A -> Prop) (x' : A) (h1 : x x') : x x'.
Proof. exact (h1). Qed.
Lemma lem5119397 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term397 A s x') : term397 A s x'.
Proof. exact (h1). Qed.
Lemma lem5119403 {A : Type'} (_66839 : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term200 A t s _66839.
Proof. exact (EQ_MP (@lem5119369 A t s _66839) (@lem5119368 A _66839 x x'' t s h1)). Qed.
Lemma lem5119409 {A : Type'} (_66840 : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term200 A x t _66840.
Proof. exact (EQ_MP (@lem5119372 A x t _66840) (@lem5119371 A _66840 x x'' t s h1)). Qed.
Lemma lem5119415 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x'' : A) (h1 : term228 A x t x'') : x x''.
Proof. exact (proj1 (@lem5119272 A x t x'' h1)). Qed.
Lemma lem5119416 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x'' : A) (h1 : term228 A x t x'') : term398 A x x''.
Proof. exact (fun h0 : term397 A x x'' => @lem5119415 A x t x'' h1). Qed.
Lemma lem5119418 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5119419 {A : Type'} (x : A -> Prop) (x'' : A) : (term398 A x x'') = (x x'').
Proof. exact (@lem5119418 (x x'')). Qed.
Lemma lem5119420 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x'' : A) (h1 : term228 A x t x'') : x x''.
Proof. exact (EQ_MP (@lem5119419 A x x'') (@lem5119416 A x t x'' h1)). Qed.
Lemma lem5119426 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5119427 {A : Type'} (t : A -> Prop) (x : A -> Prop) (_66838 : A) : (term200 A x t _66838) = (term369 A t x _66838).
Proof. exact (@lem5119426 (t _66838) (term397 A x _66838)). Qed.
Lemma lem5119433 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5119434 {A : Type'} (t : A -> Prop) (x : A -> Prop) (_66838 : A) : (term400 A x t _66838) = (term401 A t x _66838).
Proof. exact (MK_COMB (@lem5119433) (@lem5119427 A t x _66838)). Qed.
Lemma lem5119440 {A : Type'} (t : A -> Prop) (x : A -> Prop) (_66838 : A) : (term369 A t x _66838) = (term369 A t x _66838).
Proof. exact (eq_refl (term369 A t x _66838)). Qed.
Lemma lem5119441 {A : Type'} (t : A -> Prop) (x : A -> Prop) (_66838 : A) : ((term200 A x t _66838) = (term369 A t x _66838)) = ((term369 A t x _66838) = (term369 A t x _66838)).
Proof. exact (MK_COMB (@lem5119434 A t x _66838) (@lem5119440 A t x _66838)). Qed.
Lemma lem5119443 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5119444 (x : Prop) : (x = x) = True.
Proof. exact (@lem5119443 Prop x). Qed.
Lemma lem5119445 {A : Type'} (t : A -> Prop) (x : A -> Prop) (_66838 : A) : ((term369 A t x _66838) = (term369 A t x _66838)) = True.
Proof. exact (@lem5119444 (term369 A t x _66838)). Qed.
Lemma lem5119446 {A : Type'} (t : A -> Prop) (x : A -> Prop) (_66838 : A) : ((term200 A x t _66838) = (term369 A t x _66838)) = True.
Proof. exact (TRANS (@lem5119441 A t x _66838) (@lem5119445 A t x _66838)). Qed.
Lemma lem5119447 {A : Type'} (t : A -> Prop) (x : A -> Prop) (_66838 : A) : True = ((term200 A x t _66838) = (term369 A t x _66838)).
Proof. exact (SYM (@lem5119446 A t x _66838)). Qed.
Lemma lem5119448 {A : Type'} (t : A -> Prop) (x : A -> Prop) (_66838 : A) : (term200 A x t _66838) = (term369 A t x _66838).
Proof. exact (EQ_MP (@lem5119447 A t x _66838) (@lem0)). Qed.
Lemma lem5119449 {A : Type'} (_66838 : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term369 A t x _66838.
Proof. exact (EQ_MP (@lem5119448 A t x _66838) (@lem5119389 A _66838 x x'' t s h1)). Qed.
Lemma lem5119451 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5119452 {A : Type'} (x : A -> Prop) (t : A -> Prop) (_66838 : A) : (term369 A t x _66838) = (term403 A x t _66838).
Proof. exact (@lem5119451 (term397 A x _66838) (t _66838)). Qed.
Lemma lem5119454 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5119455 {A : Type'} (x : A -> Prop) (_66838 : A) : (term404 A x _66838) = (x _66838).
Proof. exact (@lem5119454 (x _66838)). Qed.
Lemma lem5119456 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5119457 {A : Type'} (x : A -> Prop) (_66838 : A) : (term405 A x _66838) = (term158 A x _66838).
Proof. exact (MK_COMB (@lem5119456) (@lem5119455 A x _66838)). Qed.
Lemma lem5119458 {A : Type'} (t : A -> Prop) (_66838 : A) : (t _66838) = (t _66838).
Proof. exact (eq_refl (t _66838)). Qed.
Lemma lem5119459 {A : Type'} (x : A -> Prop) (t : A -> Prop) (_66838 : A) : (term403 A x t _66838) = (term160 A x t _66838).
Proof. exact (MK_COMB (@lem5119457 A x _66838) (@lem5119458 A t _66838)). Qed.
Lemma lem5119460 {A : Type'} (x : A -> Prop) (t : A -> Prop) (_66838 : A) : (term369 A t x _66838) = (term160 A x t _66838).
Proof. exact (TRANS (@lem5119452 A x t _66838) (@lem5119459 A x t _66838)). Qed.
Lemma lem5119463 {A : Type'} (_66838 : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term160 A x t _66838.
Proof. exact (EQ_MP (@lem5119460 A x t _66838) (@lem5119449 A _66838 x x'' t s h1)). Qed.
Lemma lem5119464 {A : Type'} (_66838 : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term160 A x t _66838.
Proof. exact (@lem5119463 A _66838 x x'' t s h1). Qed.
Lemma lem5119465 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term160 A x t x''.
Proof. exact (@lem5119464 A x'' x x'' t s h1). Qed.
Lemma lem5119468 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term228 A x t x'') (h2 : term284 A x x'' t s) : t x''.
Proof. exact (@lem5119465 A x x'' t s h2 (@lem5119420 A x t x'' h1)). Qed.
Lemma lem5119469 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term228 A x t x'') (h2 : term284 A x x'' t s) : term398 A t x''.
Proof. exact (fun h0 : term397 A t x'' => @lem5119468 A x x'' t s h1 h2). Qed.
Lemma lem5119471 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5119472 {A : Type'} (t : A -> Prop) (x'' : A) : (term398 A t x'') = (t x'').
Proof. exact (@lem5119471 (t x'')). Qed.
Lemma lem5119473 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term228 A x t x'') (h2 : term284 A x x'' t s) : t x''.
Proof. exact (EQ_MP (@lem5119472 A t x'') (@lem5119469 A x x'' t s h1 h2)). Qed.
Lemma lem5119476 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5119478 {A : Type'} (t : A -> Prop) (x'' : A) : (term397 A t x'') = (term406 A t x'').
Proof. exact (@lem5119476 (t x'')). Qed.
Lemma lem5119481 {A : Type'} (x : A -> Prop) (t : A -> Prop) (x'' : A) (h1 : term228 A x t x'') : term406 A t x''.
Proof. exact (EQ_MP (@lem5119478 A t x'') (@lem5119393 A x t x'' h1)). Qed.
Lemma lem5119484 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term228 A x t x'') (h2 : term284 A x x'' t s) : False.
Proof. exact (@lem5119481 A x t x'' h1 (@lem5119473 A x x'' t s h1 h2)). Qed.
Lemma lem5119485 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term228 A x t x'') (h2 : term284 A x x'' t s) : term407.
Proof. exact (fun h0 : ~ False => @lem5119484 A x x'' t s h1 h2). Qed.
Lemma lem5119487 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5119488 : term407 = False.
Proof. exact (@lem5119487 False). Qed.
Lemma lem5119489 {A : Type'} (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term228 A x t x'') (h2 : term284 A x x'' t s) : False.
Proof. exact (EQ_MP (@lem5119488) (@lem5119485 A x x'' t s h1 h2)). Qed.
Lemma lem5119491 {A : Type'} (x : A -> Prop) (x' : A) (h1 : x x') : x x'.
Proof. exact (h1). Qed.
Lemma lem5119492 {A : Type'} (x : A -> Prop) (x' : A) (h1 : x x') : term398 A x x'.
Proof. exact (fun h0 : term397 A x x' => @lem5119491 A x x' h1). Qed.
Lemma lem5119494 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5119495 {A : Type'} (x : A -> Prop) (x' : A) : (term398 A x x') = (x x').
Proof. exact (@lem5119494 (x x')). Qed.
Lemma lem5119496 {A : Type'} (x : A -> Prop) (x' : A) (h1 : x x') : x x'.
Proof. exact (EQ_MP (@lem5119495 A x x') (@lem5119492 A x x' h1)). Qed.
Lemma lem5119502 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5119503 {A : Type'} (t : A -> Prop) (x : A -> Prop) (_66840 : A) : (term200 A x t _66840) = (term369 A t x _66840).
Proof. exact (@lem5119502 (t _66840) (term397 A x _66840)). Qed.
Lemma lem5119509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5119510 {A : Type'} (t : A -> Prop) (x : A -> Prop) (_66840 : A) : (term400 A x t _66840) = (term401 A t x _66840).
Proof. exact (MK_COMB (@lem5119509) (@lem5119503 A t x _66840)). Qed.
Lemma lem5119516 {A : Type'} (t : A -> Prop) (x : A -> Prop) (_66840 : A) : (term369 A t x _66840) = (term369 A t x _66840).
Proof. exact (eq_refl (term369 A t x _66840)). Qed.
Lemma lem5119517 {A : Type'} (t : A -> Prop) (x : A -> Prop) (_66840 : A) : ((term200 A x t _66840) = (term369 A t x _66840)) = ((term369 A t x _66840) = (term369 A t x _66840)).
Proof. exact (MK_COMB (@lem5119510 A t x _66840) (@lem5119516 A t x _66840)). Qed.
Lemma lem5119519 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5119520 (x : Prop) : (x = x) = True.
Proof. exact (@lem5119519 Prop x). Qed.
Lemma lem5119521 {A : Type'} (t : A -> Prop) (x : A -> Prop) (_66840 : A) : ((term369 A t x _66840) = (term369 A t x _66840)) = True.
Proof. exact (@lem5119520 (term369 A t x _66840)). Qed.
Lemma lem5119522 {A : Type'} (t : A -> Prop) (x : A -> Prop) (_66840 : A) : ((term200 A x t _66840) = (term369 A t x _66840)) = True.
Proof. exact (TRANS (@lem5119517 A t x _66840) (@lem5119521 A t x _66840)). Qed.
Lemma lem5119523 {A : Type'} (t : A -> Prop) (x : A -> Prop) (_66840 : A) : True = ((term200 A x t _66840) = (term369 A t x _66840)).
Proof. exact (SYM (@lem5119522 A t x _66840)). Qed.
Lemma lem5119524 {A : Type'} (t : A -> Prop) (x : A -> Prop) (_66840 : A) : (term200 A x t _66840) = (term369 A t x _66840).
Proof. exact (EQ_MP (@lem5119523 A t x _66840) (@lem0)). Qed.
Lemma lem5119525 {A : Type'} (_66840 : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term369 A t x _66840.
Proof. exact (EQ_MP (@lem5119524 A t x _66840) (@lem5119409 A _66840 x x'' t s h1)). Qed.
Lemma lem5119527 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5119528 {A : Type'} (x : A -> Prop) (t : A -> Prop) (_66840 : A) : (term369 A t x _66840) = (term403 A x t _66840).
Proof. exact (@lem5119527 (term397 A x _66840) (t _66840)). Qed.
Lemma lem5119530 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5119531 {A : Type'} (x : A -> Prop) (_66840 : A) : (term404 A x _66840) = (x _66840).
Proof. exact (@lem5119530 (x _66840)). Qed.
Lemma lem5119532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5119533 {A : Type'} (x : A -> Prop) (_66840 : A) : (term405 A x _66840) = (term158 A x _66840).
Proof. exact (MK_COMB (@lem5119532) (@lem5119531 A x _66840)). Qed.
Lemma lem5119534 {A : Type'} (t : A -> Prop) (_66840 : A) : (t _66840) = (t _66840).
Proof. exact (eq_refl (t _66840)). Qed.
Lemma lem5119535 {A : Type'} (x : A -> Prop) (t : A -> Prop) (_66840 : A) : (term403 A x t _66840) = (term160 A x t _66840).
Proof. exact (MK_COMB (@lem5119533 A x _66840) (@lem5119534 A t _66840)). Qed.
Lemma lem5119536 {A : Type'} (x : A -> Prop) (t : A -> Prop) (_66840 : A) : (term369 A t x _66840) = (term160 A x t _66840).
Proof. exact (TRANS (@lem5119528 A x t _66840) (@lem5119535 A x t _66840)). Qed.
Lemma lem5119539 {A : Type'} (_66840 : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term160 A x t _66840.
Proof. exact (EQ_MP (@lem5119536 A x t _66840) (@lem5119525 A _66840 x x'' t s h1)). Qed.
Lemma lem5119540 {A : Type'} (_66840 : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term160 A x t _66840.
Proof. exact (@lem5119539 A _66840 x x'' t s h1). Qed.
Lemma lem5119541 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term160 A x t x'.
Proof. exact (@lem5119540 A x' x x'' t s h1). Qed.
Lemma lem5119544 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : x x') (h2 : term284 A x x'' t s) : t x'.
Proof. exact (@lem5119541 A x' x x'' t s h2 (@lem5119496 A x x' h1)). Qed.
Lemma lem5119545 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : x x') (h2 : term284 A x x'' t s) : term398 A t x'.
Proof. exact (fun h0 : term397 A t x' => @lem5119544 A x' x x'' t s h1 h2). Qed.
Lemma lem5119547 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5119548 {A : Type'} (t : A -> Prop) (x' : A) : (term398 A t x') = (t x').
Proof. exact (@lem5119547 (t x')). Qed.
Lemma lem5119549 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : x x') (h2 : term284 A x x'' t s) : t x'.
Proof. exact (EQ_MP (@lem5119548 A t x') (@lem5119545 A x' x x'' t s h1 h2)). Qed.
Lemma lem5119555 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5119556 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_66839 : A) : (term200 A t s _66839) = (term369 A s t _66839).
Proof. exact (@lem5119555 (s _66839) (term397 A t _66839)). Qed.
Lemma lem5119562 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5119563 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_66839 : A) : (term400 A t s _66839) = (term401 A s t _66839).
Proof. exact (MK_COMB (@lem5119562) (@lem5119556 A s t _66839)). Qed.
Lemma lem5119569 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_66839 : A) : (term369 A s t _66839) = (term369 A s t _66839).
Proof. exact (eq_refl (term369 A s t _66839)). Qed.
Lemma lem5119570 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_66839 : A) : ((term200 A t s _66839) = (term369 A s t _66839)) = ((term369 A s t _66839) = (term369 A s t _66839)).
Proof. exact (MK_COMB (@lem5119563 A s t _66839) (@lem5119569 A s t _66839)). Qed.
Lemma lem5119572 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5119573 (x : Prop) : (x = x) = True.
Proof. exact (@lem5119572 Prop x). Qed.
Lemma lem5119574 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_66839 : A) : ((term369 A s t _66839) = (term369 A s t _66839)) = True.
Proof. exact (@lem5119573 (term369 A s t _66839)). Qed.
Lemma lem5119575 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_66839 : A) : ((term200 A t s _66839) = (term369 A s t _66839)) = True.
Proof. exact (TRANS (@lem5119570 A s t _66839) (@lem5119574 A s t _66839)). Qed.
Lemma lem5119576 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_66839 : A) : True = ((term200 A t s _66839) = (term369 A s t _66839)).
Proof. exact (SYM (@lem5119575 A s t _66839)). Qed.
Lemma lem5119577 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_66839 : A) : (term200 A t s _66839) = (term369 A s t _66839).
Proof. exact (EQ_MP (@lem5119576 A s t _66839) (@lem0)). Qed.
Lemma lem5119578 {A : Type'} (_66839 : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term369 A s t _66839.
Proof. exact (EQ_MP (@lem5119577 A s t _66839) (@lem5119403 A _66839 x x'' t s h1)). Qed.
Lemma lem5119580 (b : Prop) (a : Prop) : (a \/ b) = (term402 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5119581 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_66839 : A) : (term369 A s t _66839) = (term403 A t s _66839).
Proof. exact (@lem5119580 (term397 A t _66839) (s _66839)). Qed.
Lemma lem5119583 (a : Prop) : (term193 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5119584 {A : Type'} (t : A -> Prop) (_66839 : A) : (term404 A t _66839) = (t _66839).
Proof. exact (@lem5119583 (t _66839)). Qed.
Lemma lem5119585 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5119586 {A : Type'} (t : A -> Prop) (_66839 : A) : (term405 A t _66839) = (term158 A t _66839).
Proof. exact (MK_COMB (@lem5119585) (@lem5119584 A t _66839)). Qed.
Lemma lem5119587 {A : Type'} (s : A -> Prop) (_66839 : A) : (s _66839) = (s _66839).
Proof. exact (eq_refl (s _66839)). Qed.
Lemma lem5119588 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_66839 : A) : (term403 A t s _66839) = (term160 A t s _66839).
Proof. exact (MK_COMB (@lem5119586 A t _66839) (@lem5119587 A s _66839)). Qed.
Lemma lem5119589 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_66839 : A) : (term369 A s t _66839) = (term160 A t s _66839).
Proof. exact (TRANS (@lem5119581 A t s _66839) (@lem5119588 A t s _66839)). Qed.
Lemma lem5119592 {A : Type'} (_66839 : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term160 A t s _66839.
Proof. exact (EQ_MP (@lem5119589 A t s _66839) (@lem5119578 A _66839 x x'' t s h1)). Qed.
Lemma lem5119593 {A : Type'} (_66839 : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term160 A t s _66839.
Proof. exact (@lem5119592 A _66839 x x'' t s h1). Qed.
Lemma lem5119594 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term284 A x x'' t s) : term160 A t s x'.
Proof. exact (@lem5119593 A x' x x'' t s h1). Qed.
Lemma lem5119597 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : x x') (h2 : term284 A x x'' t s) : s x'.
Proof. exact (@lem5119594 A x' x x'' t s h2 (@lem5119549 A x' x x'' t s h1 h2)). Qed.
Lemma lem5119598 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : x x') (h2 : term284 A x x'' t s) : term398 A s x'.
Proof. exact (fun h0 : term397 A s x' => @lem5119597 A x' x x'' t s h1 h2). Qed.
Lemma lem5119600 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5119601 {A : Type'} (s : A -> Prop) (x' : A) : (term398 A s x') = (s x').
Proof. exact (@lem5119600 (s x')). Qed.
Lemma lem5119602 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : x x') (h2 : term284 A x x'' t s) : s x'.
Proof. exact (EQ_MP (@lem5119601 A s x') (@lem5119598 A x' x x'' t s h1 h2)). Qed.
Lemma lem5119605 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5119607 {A : Type'} (s : A -> Prop) (x' : A) : (term397 A s x') = (term406 A s x').
Proof. exact (@lem5119605 (s x')). Qed.
Lemma lem5119610 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term397 A s x') : term406 A s x'.
Proof. exact (EQ_MP (@lem5119607 A s x') (@lem5119397 A s x' h1)). Qed.
Lemma lem5119613 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : False.
Proof. exact (@lem5119610 A s x' h1 (@lem5119602 A x' x x'' t s h2 h3)). Qed.
Lemma lem5119614 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : term407.
Proof. exact (fun h0 : ~ False => @lem5119613 A x' x x'' t s h1 h2 h3). Qed.
Lemma lem5119616 (p : Prop) : (term399 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5119617 : term407 = False.
Proof. exact (@lem5119616 False). Qed.
Lemma lem5119618 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : False.
Proof. exact (EQ_MP (@lem5119617) (@lem5119614 A x' x x'' t s h1 h2 h3)). Qed.
Lemma lem5119619 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : (term397 A s x') = False.
Proof. exact (prop_ext (fun h4 : term397 A s x' => @lem5119618 A x' x x'' t s h1 h2 h3) (fun h4 : False => @lem5119397 A s x' h1)). Qed.
Lemma lem5119620 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : False.
Proof. exact (EQ_MP (@lem5119619 A x' x x'' t s h1 h2 h3) (@lem5119397 A s x' h1)). Qed.
Lemma lem5119621 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : (x x') = False.
Proof. exact (prop_ext (fun h4 : x x' => @lem5119620 A x' x x'' t s h1 h2 h3) (fun h4 : False => @lem5119395 A x x' h2)). Qed.
Lemma lem5119622 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : False.
Proof. exact (EQ_MP (@lem5119621 A x' x x'' t s h1 h2 h3) (@lem5119395 A x x' h2)). Qed.
Lemma lem5119623 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : (term397 A s x') = False.
Proof. exact (prop_ext (fun h4 : term397 A s x' => @lem5119622 A x' x x'' t s h1 h2 h3) (fun h4 : False => @lem5119327 A s x' h1)). Qed.
Lemma lem5119624 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : False.
Proof. exact (EQ_MP (@lem5119623 A x' x x'' t s h1 h2 h3) (@lem5119327 A s x' h1)). Qed.
Lemma lem5119625 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : (x x') = False.
Proof. exact (prop_ext (fun h4 : x x' => @lem5119624 A x' x x'' t s h1 h2 h3) (fun h4 : False => @lem5119323 A x x' h2)). Qed.
Lemma lem5119626 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : False.
Proof. exact (EQ_MP (@lem5119625 A x' x x'' t s h1 h2 h3) (@lem5119323 A x x' h2)). Qed.
Lemma lem5119627 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : (term397 A s x') = False.
Proof. exact (prop_ext (fun h4 : term397 A s x' => @lem5119626 A x' x x'' t s h1 h2 h3) (fun h4 : False => @lem5119327 A s x' h1)). Qed.
Lemma lem5119628 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : False.
Proof. exact (EQ_MP (@lem5119627 A x' x x'' t s h1 h2 h3) (@lem5119327 A s x' h1)). Qed.
Lemma lem5119629 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : (x x') = False.
Proof. exact (prop_ext (fun h4 : x x' => @lem5119628 A x' x x'' t s h1 h2 h3) (fun h4 : False => @lem5119323 A x x' h2)). Qed.
Lemma lem5119630 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : False.
Proof. exact (EQ_MP (@lem5119629 A x' x x'' t s h1 h2 h3) (@lem5119323 A x x' h2)). Qed.
Lemma lem5119631 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : False.
Proof. exact (or_elim (@lem5119270 A x x'' t s h3) (fun h0 : term228 A x t x'' => @lem5119489 A x x'' t s h0 h3) (fun h0 : term232 A x t x'' => @lem5119630 A x' x x'' t s h1 h2 h3)). Qed.
Lemma lem5119632 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : (term284 A x x'' t s) = False.
Proof. exact (prop_ext (fun h4 : term284 A x x'' t s => @lem5119631 A x' x x'' t s h1 h2 h3) (fun h4 : False => @lem5119267 A x x'' t s h3)). Qed.
Lemma lem5119633 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : False.
Proof. exact (EQ_MP (@lem5119632 A x' x x'' t s h1 h2 h3) (@lem5119267 A x x'' t s h3)). Qed.
Lemma lem5119634 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : (term397 A s x') = False.
Proof. exact (prop_ext (fun h4 : term397 A s x' => @lem5119633 A x' x x'' t s h1 h2 h3) (fun h4 : False => @lem5119207 A s x' h1)). Qed.
Lemma lem5119635 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : False.
Proof. exact (EQ_MP (@lem5119634 A x' x x'' t s h1 h2 h3) (@lem5119207 A s x' h1)). Qed.
Lemma lem5119636 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : (x x') = False.
Proof. exact (prop_ext (fun h4 : x x' => @lem5119635 A x' x x'' t s h1 h2 h3) (fun h4 : False => @lem5119201 A x x' h2)). Qed.
Lemma lem5119637 {A : Type'} (x' : A) (x : A -> Prop) (x'' : A) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term284 A x x'' t s) : False.
Proof. exact (EQ_MP (@lem5119636 A x' x x'' t s h1 h2 h3) (@lem5119201 A x x' h2)). Qed.
Lemma lem5119638 {A : Type'} (x' : A) (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term173 A x t s) : False.
Proof. exact (ex_elim (@lem5119184 A x t s h3) (fun x'' : A => fun h0 : term286 A x t s x'' => @lem5119637 A x' x x'' t s h1 h2 h0)). Qed.
Lemma lem5119639 {A : Type'} (x' : A) (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term173 A x t s) : (term397 A s x') = False.
Proof. exact (prop_ext (fun h4 : term397 A s x' => @lem5119638 A x' x t s h1 h2 h3) (fun h4 : False => @lem5119196 A s x' h1)). Qed.
Lemma lem5119640 {A : Type'} (x' : A) (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term173 A x t s) : False.
Proof. exact (EQ_MP (@lem5119639 A x' x t s h1 h2 h3) (@lem5119196 A s x' h1)). Qed.
Lemma lem5119641 {A : Type'} (x' : A) (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term173 A x t s) : (x x') = False.
Proof. exact (prop_ext (fun h4 : x x' => @lem5119640 A x' x t s h1 h2 h3) (fun h4 : False => @lem5119190 A x x' h2)). Qed.
Lemma lem5119642 {A : Type'} (x' : A) (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term173 A x t s) : False.
Proof. exact (EQ_MP (@lem5119641 A x' x t s h1 h2 h3) (@lem5119190 A x x' h2)). Qed.
Lemma lem5119643 {A : Type'} (x' : A) (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term173 A x t s) : (term397 A s x') = False.
Proof. exact (prop_ext (fun h4 : term397 A s x' => @lem5119642 A x' x t s h1 h2 h3) (fun h4 : False => @lem5118894 A s x' h1)). Qed.
Lemma lem5119644 {A : Type'} (x' : A) (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) (h1 : term397 A s x') (h2 : x x') (h3 : term173 A x t s) : False.
Proof. exact (EQ_MP (@lem5119643 A x' x t s h1 h2 h3) (@lem5118894 A s x' h1)). Qed.
Lemma lem5119645 {A : Type'} (x' : A) (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) (h1 : x x') (h2 : term173 A x t s) : term492 A s x'.
Proof. exact (fun h0 : term397 A s x' => @lem5119644 A x' x t s h0 h1 h2). Qed.
Lemma lem5119646 {A : Type'} (x' : A) (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) (h1 : x x') (h2 : term173 A x t s) : s x'.
Proof. exact (EQ_MP (@lem5118893 A s x') (@lem5119645 A x' x t s h1 h2)). Qed.
Lemma lem5119647 {A : Type'} (x' : A) (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) (h1 : term173 A x t s) : term160 A x s x'.
Proof. exact (fun h0 : x x' => @lem5119646 A x' x t s h0 h1). Qed.
Lemma lem5119652 {A : Type'} (x : A -> Prop) (t : A -> Prop) (s : A -> Prop) (h1 : term173 A x t s) : term163 A x s.
Proof. exact (fun x' : A => @lem5119647 A x' x t s h1). Qed.
Lemma lem5119653 {A : Type'} (t : A -> Prop) (x : A -> Prop) (s : A -> Prop) : term475 A t x s.
Proof. exact (fun h0 : term173 A x t s => @lem5119652 A x t s h0). Qed.
Lemma lem5119658 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term477 A t s.
Proof. exact (fun x : A -> Prop => @lem5119653 A t x s). Qed.
Lemma lem5119663 {A : Type'} (s : A -> Prop) : term487 A s.
Proof. exact (fun t : A -> Prop => @lem5119658 A t s). Qed.
Lemma lem5119668 {A : Type'} : term491 A.
Proof. exact (fun s : A -> Prop => @lem5119663 A s). Qed.
Lemma lem5119669 {A : Type'} : term490 A.
Proof. exact (EQ_MP (@lem5118887 A) (@lem5119668 A)). Qed.
Lemma lem5119670 {A : Type'} (s : A -> Prop) : term493 A s.
Proof. exact (@lem5119669 A s). Qed.
Lemma lem5119671 {A : Type'} (s : A -> Prop) : (term493 A s) = (term486 A s).
Proof. exact (eq_refl (term493 A s)). Qed.
Lemma lem5119672 {A : Type'} (s : A -> Prop) : term486 A s.
Proof. exact (EQ_MP (@lem5119671 A s) (@lem5119670 A s)). Qed.
Lemma lem5119673 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term494 A s t.
Proof. exact (@lem5119672 A s t). Qed.
Lemma lem5119674 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term494 A s t) = (term478 A t s).
Proof. exact (eq_refl (term494 A s t)). Qed.
Lemma lem5119675 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term478 A t s.
Proof. exact (EQ_MP (@lem5119674 A t s) (@lem5119673 A s t)). Qed.
Lemma lem5119677 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term478 A t s.
Proof. exact (@lem5118712 A t s (@lem5119675 A t s)). Qed.
Lemma lem5119678 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term479 A t s) : False.
Proof. exact (@lem5119677 A t s (@lem5118696 A t s h1)). Qed.
Lemma lem5119679 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term479 A t s) : (term479 A t s) = False.
Proof. exact (prop_ext (fun h2 : term479 A t s => @lem5119678 A t s h1) (fun h2 : False => @lem5118696 A t s h1)). Qed.
Lemma lem5119680 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term479 A t s) : False.
Proof. exact (EQ_MP (@lem5119679 A t s h1) (@lem5118696 A t s h1)). Qed.
Lemma lem5119681 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term478 A t s.
Proof. exact (fun h0 : term479 A t s => @lem5119680 A t s h0). Qed.
Lemma lem5119682 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term477 A t s.
Proof. exact (EQ_MP (@lem5118695 A t s) (@lem5119681 A t s)). Qed.
Lemma lem5119683 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term449 A t s.
Proof. exact (EQ_MP (@lem5118691 A t s) (@lem5119682 A t s)). Qed.
Lemma lem5119684 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term416 A t s.
Proof. exact (EQ_MP (@lem5118506 A t s) (@lem5119683 A t s)). Qed.
Lemma lem5119685 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term417 A t s.
Proof. exact (EQ_MP (@lem5118377 A t s h1) (@lem5119684 A t s)). Qed.
Lemma lem5119686 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term495 A t s.
Proof. exact (ex_intro (term496 A t s) (term421 A s) (@lem5119685 A t s h1)). Qed.
Lemma lem5119687 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term112 A t s.
Proof. exact (@lem5118324 A t s (@lem5119686 A t s h1)). Qed.
Lemma lem5119692 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term115 A s.
Proof. exact (fun t : A -> Prop => @lem5119687 A t s h1). Qed.
Lemma lem5119693 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term116 A s.
Proof. exact (conj (@lem5118320 A s) (@lem5119692 A s h1)). Qed.
Lemma lem5119694 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term29 A s.
Proof. exact (EQ_MP (@lem5114411 A s) (@lem5119693 A s h1)). Qed.
Lemma lem5119695 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term497 A s.
Proof. exact (@lem5113479 A s (@lem5119694 A s h1)). Qed.
Lemma lem5119696 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = (term497 A s).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem5119695 A s h1) (fun h2 : term497 A s => @lem5113475 A s h1)). Qed.
Lemma lem5119697 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term497 A s.
Proof. exact (EQ_MP (@lem5119696 A s h1) (@lem5113475 A s h1)). Qed.
Lemma lem5119698 {A : Type'} (s : A -> Prop) : term498 A s.
Proof. exact (fun h0 : @FINITE A s => @lem5119697 A s h0). Qed.
Lemma lem5119703 {A : Type'} : term499 A.
Proof. exact (fun s : A -> Prop => @lem5119698 A s). Qed.
