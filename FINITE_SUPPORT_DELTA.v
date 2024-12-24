Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_SUPPORT_DELTA_term_abbrevs.
Require Import FINITE_RULES_spec.
Require Import FINITE_SUPPORT_spec.
Require Import SUPPORT_DELTA_spec.
Require Import thm0_spec.
Require Import thm13473_spec.
Require Import thm7_spec.
Lemma lem5737459 {_119939 _119945 : Type'} (op : type1400 _119945) : term0 _119939 _119945 op.
Proof. exact (@lem5720601 _119939 _119945 op). Qed.
Lemma lem5737460 {_119939 _119945 : Type'} (op : type1400 _119945) : (term0 _119939 _119945 op) = (term1 _119939 _119945 op).
Proof. exact (eq_refl (term0 _119939 _119945 op)). Qed.
Lemma lem5737461 {_119939 _119945 : Type'} (op : type1400 _119945) : term1 _119939 _119945 op.
Proof. exact (EQ_MP (@lem5737460 _119939 _119945 op) (@lem5737459 _119939 _119945 op)). Qed.
Lemma lem5737462 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : term2 _119939 _119945 op f.
Proof. exact (@lem5737461 _119939 _119945 op f). Qed.
Lemma lem5737463 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term2 _119939 _119945 op f) = (term3 _119939 _119945 op f).
Proof. exact (eq_refl (term2 _119939 _119945 op f)). Qed.
Lemma lem5737464 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : term3 _119939 _119945 op f.
Proof. exact (EQ_MP (@lem5737463 _119939 _119945 op f) (@lem5737462 _119939 _119945 op f)). Qed.
Lemma lem5737465 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : term4 _119939 _119945 op f s.
Proof. exact (@lem5737464 _119939 _119945 op f s). Qed.
Lemma lem5737466 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term4 _119939 _119945 op f s) = (term5 _119939 _119945 op f s).
Proof. exact (eq_refl (term4 _119939 _119945 op f s)). Qed.
Lemma lem5737467 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : term5 _119939 _119945 op f s.
Proof. exact (EQ_MP (@lem5737466 _119939 _119945 op f s) (@lem5737465 _119939 _119945 op f s)). Qed.
Lemma lem5737468 {_119939 : Type'} (s : _119939 -> Prop) (h1 : @FINITE _119939 s) : @FINITE _119939 s.
Proof. exact (h1). Qed.
Lemma lem5737469 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : @FINITE _119939 s) : term6 _119939 _119945 op f s.
Proof. exact (@lem5737467 _119939 _119945 op f s (@lem5737468 _119939 s h1)). Qed.
Lemma lem5737470 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term6 _119939 _119945 op f s) = ((term6 _119939 _119945 op f s) = True).
Proof. exact (@lem7 (term6 _119939 _119945 op f s)). Qed.
Lemma lem5737471 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : @FINITE _119939 s) : (term6 _119939 _119945 op f s) = True.
Proof. exact (EQ_MP (@lem5737470 _119939 _119945 op f s) (@lem5737469 _119939 _119945 op f s h1)). Qed.
Lemma lem5737477 {A : Type'} : term7 A.
Proof. exact (proj2 (@lem3197565 A)). Qed.
Lemma lem5737478 {A : Type'} (x : A) : term8 A x.
Proof. exact (@lem5737477 A x). Qed.
Lemma lem5737479 {A : Type'} (x : A) : (term8 A x) = (term9 A x).
Proof. exact (eq_refl (term8 A x)). Qed.
Lemma lem5737480 {A : Type'} (x : A) : term9 A x.
Proof. exact (EQ_MP (@lem5737479 A x) (@lem5737478 A x)). Qed.
Lemma lem5737481 {A : Type'} (x : A) (s : A -> Prop) : term10 A x s.
Proof. exact (@lem5737480 A x s). Qed.
Lemma lem5737482 {A : Type'} (x : A) (s : A -> Prop) : (term10 A x s) = (term11 A x s).
Proof. exact (eq_refl (term10 A x s)). Qed.
Lemma lem5737483 {A : Type'} (x : A) (s : A -> Prop) : term11 A x s.
Proof. exact (EQ_MP (@lem5737482 A x s) (@lem5737481 A x s)). Qed.
Lemma lem5737484 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem5737485 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term12 A x s.
Proof. exact (@lem5737483 A x s (@lem5737484 A s h1)). Qed.
Lemma lem5737486 {A : Type'} (x : A) (s : A -> Prop) : (term12 A x s) = ((term12 A x s) = True).
Proof. exact (@lem7 (term12 A x s)). Qed.
Lemma lem5737487 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term12 A x s) = True.
Proof. exact (EQ_MP (@lem5737486 A x s) (@lem5737485 A x s h1)). Qed.
Lemma lem5737493 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem5737494 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem5737496 {_120222 _120250 : Type'} (op : type1400 _120222) : term13 _120222 _120250 op.
Proof. exact (@lem5737458 _120222 _120250 op). Qed.
Lemma lem5737497 {_120222 _120250 : Type'} (op : type1400 _120222) : (term13 _120222 _120250 op) = (term14 _120222 _120250 op).
Proof. exact (eq_refl (term13 _120222 _120250 op)). Qed.
Lemma lem5737498 {_120222 _120250 : Type'} (op : type1400 _120222) : term14 _120222 _120250 op.
Proof. exact (EQ_MP (@lem5737497 _120222 _120250 op) (@lem5737496 _120222 _120250 op)). Qed.
Lemma lem5737499 {_120222 _120250 : Type'} (op : type1400 _120222) (s : _120250 -> Prop) : term15 _120222 _120250 op s.
Proof. exact (@lem5737498 _120222 _120250 op s). Qed.
Lemma lem5737500 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) : (term15 _120222 _120250 op s) = (term16 _120222 _120250 s op).
Proof. exact (eq_refl (term15 _120222 _120250 op s)). Qed.
Lemma lem5737501 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) : term16 _120222 _120250 s op.
Proof. exact (EQ_MP (@lem5737500 _120222 _120250 s op) (@lem5737499 _120222 _120250 op s)). Qed.
Lemma lem5737502 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (f : _120250 -> _120222) : term17 _120222 _120250 s op f.
Proof. exact (@lem5737501 _120222 _120250 s op f). Qed.
Lemma lem5737503 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (f : _120250 -> _120222) : (term17 _120222 _120250 s op f) = (term18 _120222 _120250 s op f).
Proof. exact (eq_refl (term17 _120222 _120250 s op f)). Qed.
Lemma lem5737504 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (f : _120250 -> _120222) : term18 _120222 _120250 s op f.
Proof. exact (EQ_MP (@lem5737503 _120222 _120250 s op f) (@lem5737502 _120222 _120250 s op f)). Qed.
Lemma lem5737505 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (f : _120250 -> _120222) (a : _120250) : term19 _120222 _120250 s op f a.
Proof. exact (@lem5737504 _120222 _120250 s op f a). Qed.
Lemma lem5737506 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (f : _120250 -> _120222) (a : _120250) : (term19 _120222 _120250 s op f a) = ((term20 _120222 _120250 a f op s) = (term21 _120222 _120250 s op f a)).
Proof. exact (eq_refl (term19 _120222 _120250 s op f a)). Qed.
Lemma lem5737521 {_120222 _120250 : Type'} (s : _120250 -> Prop) (op : type1400 _120222) (f : _120250 -> _120222) (a : _120250) : (term20 _120222 _120250 a f op s) = (term21 _120222 _120250 s op f a).
Proof. exact (EQ_MP (@lem5737506 _120222 _120250 s op f a) (@lem5737505 _120222 _120250 s op f a)). Qed.
Lemma lem5737522 {_120271 _120280 : Type'} (s : _120280 -> Prop) (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) : (term20 _120271 _120280 a f op s) = (term21 _120271 _120280 s op f a).
Proof. exact (@lem5737521 _120271 _120280 s op f a). Qed.
Lemma lem5737523 {_120280 : Type'} : (@FINITE _120280) = (@FINITE _120280).
Proof. exact (eq_refl (@FINITE _120280)). Qed.
Lemma lem5737524 {_120271 _120280 : Type'} (s : _120280 -> Prop) (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) : (term22 _120271 _120280 a f op s) = (term23 _120271 _120280 s op f a).
Proof. exact (MK_COMB (@lem5737523 _120280) (@lem5737522 _120271 _120280 s op f a)). Qed.
Lemma lem5737525 {_120271 _120280 : Type'} (s : _120280 -> Prop) (op : type1400 _120271) (f : _120280 -> _120271) : (term24 _120271 _120280 f op s) = (term25 _120271 _120280 s op f).
Proof. exact (fun_ext (fun a : _120280 => @lem5737524 _120271 _120280 s op f a)). Qed.
Lemma lem5737526 {_120280 : Type'} : (@all _120280) = (@all _120280).
Proof. exact (eq_refl (@all _120280)). Qed.
Lemma lem5737527 {_120271 _120280 : Type'} (s : _120280 -> Prop) (op : type1400 _120271) (f : _120280 -> _120271) : (term26 _120271 _120280 f op s) = (term27 _120271 _120280 s op f).
Proof. exact (MK_COMB (@lem5737526 _120280) (@lem5737525 _120271 _120280 s op f)). Qed.
Lemma lem5737532 {_120271 _120280 : Type'} (s : _120280 -> Prop) (op : type1400 _120271) : (term28 _120271 _120280 op s) = (term29 _120271 _120280 s op).
Proof. exact (fun_ext (fun f : _120280 -> _120271 => @lem5737527 _120271 _120280 s op f)). Qed.
Lemma lem5737533 {_120271 _120280 : Type'} : (@all (_120280 -> _120271)) = (@all (_120280 -> _120271)).
Proof. exact (eq_refl (@all (_120280 -> _120271))). Qed.
Lemma lem5737534 {_120271 _120280 : Type'} (s : _120280 -> Prop) (op : type1400 _120271) : (term30 _120271 _120280 op s) = (term31 _120271 _120280 s op).
Proof. exact (MK_COMB (@lem5737533 _120271 _120280) (@lem5737532 _120271 _120280 s op)). Qed.
Lemma lem5737539 {_120271 _120280 : Type'} (s : _120280 -> Prop) : (term32 _120271 _120280 s) = (term33 _120271 _120280 s).
Proof. exact (fun_ext (fun op : type1400 _120271 => @lem5737534 _120271 _120280 s op)). Qed.
Lemma lem5737540 {_120271 : Type'} : (@all (_120271 -> _120271 -> _120271)) = (@all (_120271 -> _120271 -> _120271)).
Proof. exact (eq_refl (@all (_120271 -> _120271 -> _120271))). Qed.
Lemma lem5737541 {_120271 _120280 : Type'} (s : _120280 -> Prop) : (term34 _120271 _120280 s) = (term35 _120271 _120280 s).
Proof. exact (MK_COMB (@lem5737540 _120271) (@lem5737539 _120271 _120280 s)). Qed.
Lemma lem5737546 {_120271 _120280 : Type'} (s : _120280 -> Prop) : (term35 _120271 _120280 s) = (term34 _120271 _120280 s).
Proof. exact (SYM (@lem5737541 _120271 _120280 s)). Qed.
Lemma lem5737547 {_120280 : Type'} (_474 : _120280 -> Prop) (_475 : Prop) (_476 : type686 _120280) (_477 : _120280 -> Prop) : (term36 _120280 _476 _475 _474 _477) = (term37 _120280 _474 _475 _476 _477).
Proof. exact (@lem13473 (_120280 -> Prop) _474 _475 _476 _477). Qed.
Lemma lem5737548 {_120280 : Type'} (_474 : _120280 -> Prop) (_475 : Prop) (_477 : _120280 -> Prop) : (term38 _120280 _475 _474 _477) = (term39 _120280 _474 _475 _477).
Proof. exact (@lem5737547 _120280 _474 _475 (term40 _120280) _477). Qed.
Lemma lem5737549 {_120271 _120280 : Type'} (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) (s : _120280 -> Prop) : (term41 _120271 _120280 s op f a) = (term42 _120271 _120280 op f a s).
Proof. exact (@lem5737548 _120280 (term43 _120271 _120280 op f a) (@IN _120280 a s) (@EMPTY _120280)). Qed.
Lemma lem5737550 {_120280 : Type'} : (term44 _120280) = (@FINITE _120280 (@EMPTY _120280)).
Proof. exact (eq_refl (term44 _120280)). Qed.
Lemma lem5737551 {_120280 : Type'} (a : _120280) (s : _120280 -> Prop) : (term45 _120280 a s) = (term45 _120280 a s).
Proof. exact (eq_refl (term45 _120280 a s)). Qed.
Lemma lem5737552 {_120280 : Type'} (a : _120280) (s : _120280 -> Prop) : (term46 _120280 a s) = (term47 _120280 a s).
Proof. exact (MK_COMB (@lem5737551 _120280 a s) (@lem5737550 _120280)). Qed.
Lemma lem5737553 {_120271 _120280 : Type'} (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) : (term48 _120271 _120280 op f a) = (term49 _120271 _120280 op f a).
Proof. exact (eq_refl (term48 _120271 _120280 op f a)). Qed.
Lemma lem5737554 {_120280 : Type'} (a : _120280) (s : _120280 -> Prop) : (term50 _120280 a s) = (term50 _120280 a s).
Proof. exact (eq_refl (term50 _120280 a s)). Qed.
Lemma lem5737555 {_120271 _120280 : Type'} (s : _120280 -> Prop) (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) : (term51 _120271 _120280 s op f a) = (term52 _120271 _120280 s op f a).
Proof. exact (MK_COMB (@lem5737554 _120280 a s) (@lem5737553 _120271 _120280 op f a)). Qed.
Lemma lem5737556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5737557 {_120271 _120280 : Type'} (s : _120280 -> Prop) (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) : (term53 _120271 _120280 s op f a) = (term54 _120271 _120280 s op f a).
Proof. exact (MK_COMB (@lem5737556) (@lem5737555 _120271 _120280 s op f a)). Qed.
Lemma lem5737558 {_120271 _120280 : Type'} (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) (s : _120280 -> Prop) : (term42 _120271 _120280 op f a s) = (term55 _120271 _120280 op f a s).
Proof. exact (MK_COMB (@lem5737557 _120271 _120280 s op f a) (@lem5737552 _120280 a s)). Qed.
Lemma lem5737559 {_120271 _120280 : Type'} (s : _120280 -> Prop) (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) : (term41 _120271 _120280 s op f a) = (term23 _120271 _120280 s op f a).
Proof. exact (eq_refl (term41 _120271 _120280 s op f a)). Qed.
Lemma lem5737560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5737561 {_120271 _120280 : Type'} (s : _120280 -> Prop) (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) : (term56 _120271 _120280 s op f a) = (term57 _120271 _120280 s op f a).
Proof. exact (MK_COMB (@lem5737560) (@lem5737559 _120271 _120280 s op f a)). Qed.
Lemma lem5737562 {_120271 _120280 : Type'} (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) (s : _120280 -> Prop) : ((term41 _120271 _120280 s op f a) = (term42 _120271 _120280 op f a s)) = ((term23 _120271 _120280 s op f a) = (term55 _120271 _120280 op f a s)).
Proof. exact (MK_COMB (@lem5737561 _120271 _120280 s op f a) (@lem5737558 _120271 _120280 op f a s)). Qed.
Lemma lem5737563 {_120271 _120280 : Type'} (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) (s : _120280 -> Prop) : (term23 _120271 _120280 s op f a) = (term55 _120271 _120280 op f a s).
Proof. exact (EQ_MP (@lem5737562 _120271 _120280 op f a s) (@lem5737549 _120271 _120280 op f a s)). Qed.
Lemma lem5737564 {_120271 _120280 : Type'} (s : _120280 -> Prop) (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) : (term55 _120271 _120280 op f a s) = (term23 _120271 _120280 s op f a).
Proof. exact (SYM (@lem5737563 _120271 _120280 op f a s)). Qed.
Lemma lem5737600 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : term58 _119939 _119945 op f s.
Proof. exact (fun h0 : @FINITE _119939 s => @lem5737471 _119939 _119945 op f s h0). Qed.
Lemma lem5737601 {_120271 _120280 : Type'} (op : type1400 _120271) (f : _120280 -> _120271) (s : _120280 -> Prop) : term59 _120271 _120280 op f s.
Proof. exact (@lem5737600 _120280 _120271 op f s). Qed.
Lemma lem5737602 {_120271 _120280 : Type'} (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) : term60 _120271 _120280 op f a.
Proof. exact (@lem5737601 _120271 _120280 op f (@INSERT _120280 a (@EMPTY _120280))). Qed.
Lemma lem5737604 {A : Type'} (x : A) (s : A -> Prop) : term61 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem5737487 A x s h0). Qed.
Lemma lem5737605 {_120280 : Type'} (x : _120280) (s : _120280 -> Prop) : term61 _120280 x s.
Proof. exact (@lem5737604 _120280 x s). Qed.
Lemma lem5737606 {_120280 : Type'} (a : _120280) : term62 _120280 a.
Proof. exact (@lem5737605 _120280 a (@EMPTY _120280)). Qed.
Lemma lem5737608 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem5737494 A) (@lem5737493 A)). Qed.
Lemma lem5737609 {_120280 : Type'} : (@FINITE _120280 (@EMPTY _120280)) = True.
Proof. exact (@lem5737608 _120280). Qed.
Lemma lem5737610 {_120280 : Type'} : True = (@FINITE _120280 (@EMPTY _120280)).
Proof. exact (SYM (@lem5737609 _120280)). Qed.
Lemma lem5737611 {_120280 : Type'} : @FINITE _120280 (@EMPTY _120280).
Proof. exact (EQ_MP (@lem5737610 _120280) (@lem0)). Qed.
Lemma lem5737612 {_120280 : Type'} (a : _120280) : (term63 _120280 a) = True.
Proof. exact (@lem5737606 _120280 a (@lem5737611 _120280)). Qed.
Lemma lem5737613 {_120280 : Type'} (a : _120280) : True = (term63 _120280 a).
Proof. exact (SYM (@lem5737612 _120280 a)). Qed.
Lemma lem5737614 {_120280 : Type'} (a : _120280) : term63 _120280 a.
Proof. exact (EQ_MP (@lem5737613 _120280 a) (@lem0)). Qed.
Lemma lem5737615 {_120271 _120280 : Type'} (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) : (term49 _120271 _120280 op f a) = True.
Proof. exact (@lem5737602 _120271 _120280 op f a (@lem5737614 _120280 a)). Qed.
Lemma lem5737616 {_120271 _120280 : Type'} (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) : True = (term49 _120271 _120280 op f a).
Proof. exact (SYM (@lem5737615 _120271 _120280 op f a)). Qed.
Lemma lem5737619 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem5737494 A) (@lem5737493 A)). Qed.
Lemma lem5737620 {_120280 : Type'} : (@FINITE _120280 (@EMPTY _120280)) = True.
Proof. exact (@lem5737619 _120280). Qed.
Lemma lem5737621 {_120280 : Type'} : True = (@FINITE _120280 (@EMPTY _120280)).
Proof. exact (SYM (@lem5737620 _120280)). Qed.
Lemma lem5737623 {_120280 : Type'} : @FINITE _120280 (@EMPTY _120280).
Proof. exact (EQ_MP (@lem5737621 _120280) (@lem0)). Qed.
Lemma lem5737624 {_120280 : Type'} (a : _120280) (s : _120280 -> Prop) : term47 _120280 a s.
Proof. exact (fun h0 : term64 _120280 a s => @lem5737623 _120280). Qed.
Lemma lem5737625 {_120271 _120280 : Type'} (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) : term49 _120271 _120280 op f a.
Proof. exact (EQ_MP (@lem5737616 _120271 _120280 op f a) (@lem0)). Qed.
Lemma lem5737626 {_120271 _120280 : Type'} (s : _120280 -> Prop) (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) : term52 _120271 _120280 s op f a.
Proof. exact (fun h0 : @IN _120280 a s => @lem5737625 _120271 _120280 op f a). Qed.
Lemma lem5737627 {_120271 _120280 : Type'} (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) (s : _120280 -> Prop) : term55 _120271 _120280 op f a s.
Proof. exact (conj (@lem5737626 _120271 _120280 s op f a) (@lem5737624 _120280 a s)). Qed.
Lemma lem5737628 {_120271 _120280 : Type'} (s : _120280 -> Prop) (op : type1400 _120271) (f : _120280 -> _120271) (a : _120280) : term23 _120271 _120280 s op f a.
Proof. exact (EQ_MP (@lem5737564 _120271 _120280 s op f a) (@lem5737627 _120271 _120280 op f a s)). Qed.
Lemma lem5737633 {_120271 _120280 : Type'} (s : _120280 -> Prop) (op : type1400 _120271) (f : _120280 -> _120271) : term27 _120271 _120280 s op f.
Proof. exact (fun a : _120280 => @lem5737628 _120271 _120280 s op f a). Qed.
Lemma lem5737638 {_120271 _120280 : Type'} (s : _120280 -> Prop) (op : type1400 _120271) : term31 _120271 _120280 s op.
Proof. exact (fun f : _120280 -> _120271 => @lem5737633 _120271 _120280 s op f). Qed.
Lemma lem5737643 {_120271 _120280 : Type'} (s : _120280 -> Prop) : term35 _120271 _120280 s.
Proof. exact (fun op : type1400 _120271 => @lem5737638 _120271 _120280 s op). Qed.
Lemma lem5737644 {_120271 _120280 : Type'} (s : _120280 -> Prop) : term34 _120271 _120280 s.
Proof. exact (EQ_MP (@lem5737546 _120271 _120280 s) (@lem5737643 _120271 _120280 s)). Qed.
