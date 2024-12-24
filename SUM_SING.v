Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_SING_term_abbrevs.
Require Import FINITE_RULES_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import REAL_ADD_RID_spec.
Require Import SUM_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem7123385 (x : real) : term0 x.
Proof. exact (@lem1361590 x). Qed.
Lemma lem7123386 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem7123388 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem7123389 {A : Type'} (x : A) : (term2 A x) = (term3 A x).
Proof. exact (eq_refl (term2 A x)). Qed.
Lemma lem7123390 {A : Type'} (x : A) : term3 A x.
Proof. exact (EQ_MP (@lem7123389 A x) (@lem7123388 A x)). Qed.
Lemma lem7123391 {A : Type'} (x : A) : term4 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem7123409 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem7123410 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem7123412 {_131524 : Type'} : term5 _131524.
Proof. exact (proj2 (@lem7067645 Prop _131524)). Qed.
Lemma lem7123413 {_131524 : Type'} (x : _131524) : term6 _131524 x.
Proof. exact (@lem7123412 _131524 x). Qed.
Lemma lem7123414 {_131524 : Type'} (x : _131524) : (term6 _131524 x) = (term7 _131524 x).
Proof. exact (eq_refl (term6 _131524 x)). Qed.
Lemma lem7123415 {_131524 : Type'} (x : _131524) : term7 _131524 x.
Proof. exact (EQ_MP (@lem7123414 _131524 x) (@lem7123413 _131524 x)). Qed.
Lemma lem7123416 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term8 _131524 x f.
Proof. exact (@lem7123415 _131524 x f). Qed.
Lemma lem7123417 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term8 _131524 x f) = (term9 _131524 x f).
Proof. exact (eq_refl (term8 _131524 x f)). Qed.
Lemma lem7123418 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term9 _131524 x f.
Proof. exact (EQ_MP (@lem7123417 _131524 x f) (@lem7123416 _131524 x f)). Qed.
Lemma lem7123419 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) : term10 _131524 x f s.
Proof. exact (@lem7123418 _131524 x f s). Qed.
Lemma lem7123420 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term10 _131524 x f s) = (term11 _131524 x s f).
Proof. exact (eq_refl (term10 _131524 x f s)). Qed.
Lemma lem7123421 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term11 _131524 x s f.
Proof. exact (EQ_MP (@lem7123420 _131524 x s f) (@lem7123419 _131524 x f s)). Qed.
Lemma lem7123422 {_131524 : Type'} (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : @FINITE _131524 s.
Proof. exact (h1). Qed.
Lemma lem7123423 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : (term12 _131524 x s f) = (term13 _131524 x s f).
Proof. exact (@lem7123421 _131524 x s f (@lem7123422 _131524 s h1)). Qed.
Lemma lem7123429 {_131483 : Type'} : term14 _131483.
Proof. exact (proj1 (@lem7067645 _131483 Prop)). Qed.
Lemma lem7123430 {_131483 : Type'} (f : _131483 -> real) : term15 _131483 f.
Proof. exact (@lem7123429 _131483 f). Qed.
Lemma lem7123431 {_131483 : Type'} (f : _131483 -> real) : (term15 _131483 f) = ((@sum _131483 (@EMPTY _131483) f) = term16).
Proof. exact (eq_refl (term15 _131483 f)). Qed.
Lemma lem7123444 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term11 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7123423 _131524 x f s h0). Qed.
Lemma lem7123445 {_133036 : Type'} (x : _133036) (s : _133036 -> Prop) (f : _133036 -> real) : term11 _133036 x s f.
Proof. exact (@lem7123444 _133036 x s f). Qed.
Lemma lem7123446 {_133036 : Type'} (x : _133036) (f : _133036 -> real) : term17 _133036 x f.
Proof. exact (@lem7123445 _133036 x (@EMPTY _133036) f). Qed.
Lemma lem7123448 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem7123410 A) (@lem7123409 A)). Qed.
Lemma lem7123449 {_133036 : Type'} : (@FINITE _133036 (@EMPTY _133036)) = True.
Proof. exact (@lem7123448 _133036). Qed.
Lemma lem7123450 {_133036 : Type'} : True = (@FINITE _133036 (@EMPTY _133036)).
Proof. exact (SYM (@lem7123449 _133036)). Qed.
Lemma lem7123451 {_133036 : Type'} : @FINITE _133036 (@EMPTY _133036).
Proof. exact (EQ_MP (@lem7123450 _133036) (@lem0)). Qed.
Lemma lem7123452 {_133036 : Type'} (x : _133036) (f : _133036 -> real) : (term18 _133036 x f) = (term19 _133036 x f).
Proof. exact (@lem7123446 _133036 x f (@lem7123451 _133036)). Qed.
Lemma lem7123454 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term20 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7123455 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term21 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7123454 _2963 g t e g' t' e'). Qed.
Lemma lem7123456 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term22 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7123455 _2963 g t e g' t'). Qed.
Lemma lem7123457 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term23 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7123456 _2963 g t e g'). Qed.
Lemma lem7123458 (g : Prop) (t : real) (e : real) : term24 g t e.
Proof. exact (@lem7123457 real g t e). Qed.
Lemma lem7123459 {_133036 : Type'} (x : _133036) (f : _133036 -> real) : term25 _133036 x f.
Proof. exact (@lem7123458 (@IN _133036 x (@EMPTY _133036)) (@sum _133036 (@EMPTY _133036) f) (term26 _133036 x f)). Qed.
Lemma lem7123460 {_133036 : Type'} (x : _133036) (f : _133036 -> real) (g' : Prop) : term27 _133036 x f g'.
Proof. exact (@lem7123459 _133036 x f g'). Qed.
Lemma lem7123461 {_133036 : Type'} (x : _133036) (f : _133036 -> real) (g' : Prop) : (term27 _133036 x f g') = (term28 _133036 x f g').
Proof. exact (eq_refl (term27 _133036 x f g')). Qed.
Lemma lem7123462 {_133036 : Type'} (x : _133036) (f : _133036 -> real) (g' : Prop) : term28 _133036 x f g'.
Proof. exact (EQ_MP (@lem7123461 _133036 x f g') (@lem7123460 _133036 x f g')). Qed.
Lemma lem7123463 {_133036 : Type'} (x : _133036) (f : _133036 -> real) (g' : Prop) (t' : real) : term29 _133036 x f g' t'.
Proof. exact (@lem7123462 _133036 x f g' t'). Qed.
Lemma lem7123464 {_133036 : Type'} (x : _133036) (f : _133036 -> real) (g' : Prop) (t' : real) : (term29 _133036 x f g' t') = (term30 _133036 x f g' t').
Proof. exact (eq_refl (term29 _133036 x f g' t')). Qed.
Lemma lem7123465 {_133036 : Type'} (x : _133036) (f : _133036 -> real) (g' : Prop) (t' : real) : term30 _133036 x f g' t'.
Proof. exact (EQ_MP (@lem7123464 _133036 x f g' t') (@lem7123463 _133036 x f g' t')). Qed.
Lemma lem7123466 {_133036 : Type'} (x : _133036) (f : _133036 -> real) (g' : Prop) (t' : real) (e' : real) : term31 _133036 x f g' t' e'.
Proof. exact (@lem7123465 _133036 x f g' t' e'). Qed.
Lemma lem7123467 {_133036 : Type'} (x : _133036) (f : _133036 -> real) (g' : Prop) (t' : real) (e' : real) : (term31 _133036 x f g' t' e') = (term32 _133036 x f g' t' e').
Proof. exact (eq_refl (term31 _133036 x f g' t' e')). Qed.
Lemma lem7123468 {_133036 : Type'} (x : _133036) (f : _133036 -> real) (g' : Prop) (t' : real) (e' : real) : term32 _133036 x f g' t' e'.
Proof. exact (EQ_MP (@lem7123467 _133036 x f g' t' e') (@lem7123466 _133036 x f g' t' e')). Qed.
Lemma lem7123470 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem7123391 A x (@lem7123390 A x)). Qed.
Lemma lem7123471 {_133036 : Type'} (x : _133036) : (@IN _133036 x (@EMPTY _133036)) = False.
Proof. exact (@lem7123470 _133036 x). Qed.
Lemma lem7123472 {_133036 : Type'} (x : _133036) (f : _133036 -> real) (t' : real) (e' : real) : term33 _133036 x f t' e'.
Proof. exact (@lem7123468 _133036 x f False t' e'). Qed.
Lemma lem7123473 {_133036 : Type'} (x : _133036) (f : _133036 -> real) (t' : real) (e' : real) : term34 _133036 x f t' e'.
Proof. exact (@lem7123472 _133036 x f t' e' (@lem7123471 _133036 x)). Qed.
Lemma lem7123478 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = term16.
Proof. exact (EQ_MP (@lem7123431 _131483 f) (@lem7123430 _131483 f)). Qed.
Lemma lem7123479 {_133036 : Type'} (f : _133036 -> real) : (@sum _133036 (@EMPTY _133036) f) = term16.
Proof. exact (@lem7123478 _133036 f). Qed.
Lemma lem7123480 {_133036 : Type'} (f : _133036 -> real) : term35 _133036 f.
Proof. exact (fun h0 : False => @lem7123479 _133036 f). Qed.
Lemma lem7123481 {_133036 : Type'} (x : _133036) (f : _133036 -> real) (e' : real) : term36 _133036 x f e'.
Proof. exact (@lem7123473 _133036 x f term16 e'). Qed.
Lemma lem7123482 {_133036 : Type'} (x : _133036) (f : _133036 -> real) (e' : real) : term37 _133036 x f e'.
Proof. exact (@lem7123481 _133036 x f e' (@lem7123480 _133036 f)). Qed.
Lemma lem7123489 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = term16.
Proof. exact (EQ_MP (@lem7123431 _131483 f) (@lem7123430 _131483 f)). Qed.
Lemma lem7123490 {_133036 : Type'} (f : _133036 -> real) : (@sum _133036 (@EMPTY _133036) f) = term16.
Proof. exact (@lem7123489 _133036 f). Qed.
Lemma lem7123491 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : (term38 _133036 f x) = (term38 _133036 f x).
Proof. exact (eq_refl (term38 _133036 f x)). Qed.
Lemma lem7123492 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : (term26 _133036 x f) = (term39 _133036 f x).
Proof. exact (MK_COMB (@lem7123491 _133036 f x) (@lem7123490 _133036 f)). Qed.
Lemma lem7123494 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem7123386 x) (@lem7123385 x)). Qed.
Lemma lem7123495 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : (term39 _133036 f x) = (f x).
Proof. exact (@lem7123494 (f x)). Qed.
Lemma lem7123496 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : (term26 _133036 x f) = (f x).
Proof. exact (TRANS (@lem7123492 _133036 f x) (@lem7123495 _133036 f x)). Qed.
Lemma lem7123497 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : term40 _133036 f x.
Proof. exact (fun h0 : ~ False => @lem7123496 _133036 f x). Qed.
Lemma lem7123498 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : term41 _133036 f x.
Proof. exact (@lem7123482 _133036 x f (f x)). Qed.
Lemma lem7123499 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : (term19 _133036 x f) = (term42 _133036 f x).
Proof. exact (@lem7123498 _133036 f x (@lem7123497 _133036 f x)). Qed.
Lemma lem7123501 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7123502 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7123501 real t1 t2). Qed.
Lemma lem7123503 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : (term42 _133036 f x) = (f x).
Proof. exact (@lem7123502 term16 (f x)). Qed.
Lemma lem7123504 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : (term19 _133036 x f) = (f x).
Proof. exact (TRANS (@lem7123499 _133036 f x) (@lem7123503 _133036 f x)). Qed.
Lemma lem7123505 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : (term18 _133036 x f) = (f x).
Proof. exact (TRANS (@lem7123452 _133036 x f) (@lem7123504 _133036 f x)). Qed.
Lemma lem7123506 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7123507 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : (term43 _133036 x f) = (term44 _133036 f x).
Proof. exact (MK_COMB (@lem7123506) (@lem7123505 _133036 f x)). Qed.
Lemma lem7123508 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem7123509 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : ((term18 _133036 x f) = (f x)) = ((f x) = (f x)).
Proof. exact (MK_COMB (@lem7123507 _133036 f x) (@lem7123508 _133036 f x)). Qed.
Lemma lem7123511 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7123512 (x : real) : (x = x) = True.
Proof. exact (@lem7123511 real x). Qed.
Lemma lem7123513 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : ((f x) = (f x)) = True.
Proof. exact (@lem7123512 (f x)). Qed.
Lemma lem7123514 {_133036 : Type'} (f : _133036 -> real) (x : _133036) : ((term18 _133036 x f) = (f x)) = True.
Proof. exact (TRANS (@lem7123509 _133036 f x) (@lem7123513 _133036 f x)). Qed.
Lemma lem7123515 {_133036 : Type'} (f : _133036 -> real) : (term45 _133036 f) = (term46 _133036).
Proof. exact (fun_ext (fun x : _133036 => @lem7123514 _133036 f x)). Qed.
Lemma lem7123516 {_133036 : Type'} : (@all _133036) = (@all _133036).
Proof. exact (eq_refl (@all _133036)). Qed.
Lemma lem7123517 {_133036 : Type'} (f : _133036 -> real) : (term47 _133036 f) = (term48 _133036).
Proof. exact (MK_COMB (@lem7123516 _133036) (@lem7123515 _133036 f)). Qed.
Lemma lem7123519 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7123520 {_133036 : Type'} (t : Prop) : (term49 _133036 t) = t.
Proof. exact (@lem7123519 _133036 t). Qed.
Lemma lem7123521 {_133036 : Type'} : (term48 _133036) = True.
Proof. exact (@lem7123520 _133036 True). Qed.
Lemma lem7123522 {_133036 : Type'} (f : _133036 -> real) : (term47 _133036 f) = True.
Proof. exact (TRANS (@lem7123517 _133036 f) (@lem7123521 _133036)). Qed.
Lemma lem7123523 {_133036 : Type'} : (term50 _133036) = (term51 _133036).
Proof. exact (fun_ext (fun f : _133036 -> real => @lem7123522 _133036 f)). Qed.
Lemma lem7123524 {_133036 : Type'} : (@all (_133036 -> real)) = (@all (_133036 -> real)).
Proof. exact (eq_refl (@all (_133036 -> real))). Qed.
Lemma lem7123525 {_133036 : Type'} : (term52 _133036) = (term53 _133036).
Proof. exact (MK_COMB (@lem7123524 _133036) (@lem7123523 _133036)). Qed.
Lemma lem7123527 {A : Type'} (t : Prop) : (term49 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7123528 {_133036 : Type'} (t : Prop) : (term54 _133036 t) = t.
Proof. exact (@lem7123527 (_133036 -> real) t). Qed.
Lemma lem7123529 {_133036 : Type'} : (term53 _133036) = True.
Proof. exact (@lem7123528 _133036 True). Qed.
Lemma lem7123530 {_133036 : Type'} : (term52 _133036) = True.
Proof. exact (TRANS (@lem7123525 _133036) (@lem7123529 _133036)). Qed.
Lemma lem7123531 {_133036 : Type'} : True = (term52 _133036).
Proof. exact (SYM (@lem7123530 _133036)). Qed.
Lemma lem7123532 {_133036 : Type'} : term52 _133036.
Proof. exact (EQ_MP (@lem7123531 _133036) (@lem0)). Qed.
