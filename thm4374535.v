Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4374535_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4372173_spec.
Lemma lem4374303 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4374304 {_104907 : Type'} (s : type686 _104907) (t : type686 _104907) : (s = t) = (term1 _104907 s t).
Proof. exact (@lem4374303 (_104907 -> Prop) s t). Qed.
Lemma lem4374305 {_104907 : Type'} (f : type686 _104907) : (f = (@EMPTY (_104907 -> Prop))) = (term2 _104907 f).
Proof. exact (@lem4374304 _104907 f (@EMPTY (_104907 -> Prop))). Qed.
Lemma lem4374314 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4374315 {_104907 : Type'} (f : type686 _104907) : (term3 _104907 f) = (term4 _104907 f).
Proof. exact (MK_COMB (@lem4374314) (@lem4374305 _104907 f)). Qed.
Lemma lem4374338 {_104907 _104908 : Type'} (g : type686 _104908) : (term5 _104907 _104908 g) = (term5 _104907 _104908 g).
Proof. exact (eq_refl (term5 _104907 _104908 g)). Qed.
Lemma lem4374339 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term6 _104907 _104908 f g) = (term7 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4374315 _104907 f) (@lem4374338 _104907 _104908 g)). Qed.
Lemma lem4374342 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term7 _104907 _104908 f g) = (term6 _104907 _104908 f g).
Proof. exact (SYM (@lem4374339 _104907 _104908 f g)). Qed.
Lemma lem4374352 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4374353 {_104907 : Type'} (P : type686 _104907) (x : _104907 -> Prop) : (@IN (_104907 -> Prop) x P) = (P x).
Proof. exact (@lem4374352 (_104907 -> Prop) P x). Qed.
Lemma lem4374354 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : (@IN (_104907 -> Prop) x f) = (f x).
Proof. exact (@lem4374353 _104907 f x). Qed.
Lemma lem4374355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4374356 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : (term8 _104907 x f) = (term9 _104907 f x).
Proof. exact (MK_COMB (@lem4374355) (@lem4374354 _104907 f x)). Qed.
Lemma lem4374358 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4374359 {_104907 : Type'} (x : _104907 -> Prop) : (@IN (_104907 -> Prop) x (@EMPTY (_104907 -> Prop))) = False.
Proof. exact (@lem4374358 (_104907 -> Prop) x). Qed.
Lemma lem4374360 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : ((@IN (_104907 -> Prop) x f) = (@IN (_104907 -> Prop) x (@EMPTY (_104907 -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem4374356 _104907 f x) (@lem4374359 _104907 x)). Qed.
Lemma lem4374362 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4374363 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : ((f x) = False) = (term10 _104907 f x).
Proof. exact (@lem4374362 (f x)). Qed.
Lemma lem4374364 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : ((@IN (_104907 -> Prop) x f) = (@IN (_104907 -> Prop) x (@EMPTY (_104907 -> Prop)))) = (term10 _104907 f x).
Proof. exact (TRANS (@lem4374360 _104907 f x) (@lem4374363 _104907 f x)). Qed.
Lemma lem4374365 {_104907 : Type'} (f : type686 _104907) : (term11 _104907 f) = (term12 _104907 f).
Proof. exact (fun_ext (fun x : _104907 -> Prop => @lem4374364 _104907 f x)). Qed.
Lemma lem4374366 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4374367 {_104907 : Type'} (f : type686 _104907) : (term2 _104907 f) = (term13 _104907 f).
Proof. exact (MK_COMB (@lem4374366 _104907) (@lem4374365 _104907 f)). Qed.
Lemma lem4374372 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4374373 {_104907 : Type'} (f : type686 _104907) : (term4 _104907 f) = (term14 _104907 f).
Proof. exact (MK_COMB (@lem4374372) (@lem4374367 _104907 f)). Qed.
Lemma lem4374387 {A : Type'} (s : type686 A) (x : A) : (term15 A x s) = (term16 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem4374388 {_104907 : Type'} (s : type686 _104907) (x : _104907) : (term15 _104907 x s) = (term16 _104907 s x).
Proof. exact (@lem4374387 _104907 s x). Qed.
Lemma lem4374389 {_104907 : Type'} (p1 : _104907) : (term17 _104907 p1) = (term18 _104907 p1).
Proof. exact (@lem4374388 _104907 (@EMPTY (_104907 -> Prop)) p1). Qed.
Lemma lem4374397 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4374398 {_104907 : Type'} (x : _104907 -> Prop) : (@IN (_104907 -> Prop) x (@EMPTY (_104907 -> Prop))) = False.
Proof. exact (@lem4374397 (_104907 -> Prop) x). Qed.
Lemma lem4374399 {_104907 : Type'} (t : _104907 -> Prop) : (@IN (_104907 -> Prop) t (@EMPTY (_104907 -> Prop))) = False.
Proof. exact (@lem4374398 _104907 t). Qed.
Lemma lem4374400 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4374401 {_104907 : Type'} (t : _104907 -> Prop) : (term19 _104907 t) = (imp False).
Proof. exact (MK_COMB (@lem4374400) (@lem4374399 _104907 t)). Qed.
Lemma lem4374403 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4374404 {_104907 : Type'} (P : _104907 -> Prop) (x : _104907) : (@IN _104907 x P) = (P x).
Proof. exact (@lem4374403 _104907 P x). Qed.
Lemma lem4374405 {_104907 : Type'} (t : _104907 -> Prop) (p1 : _104907) : (@IN _104907 p1 t) = (t p1).
Proof. exact (@lem4374404 _104907 t p1). Qed.
Lemma lem4374406 {_104907 : Type'} (t : _104907 -> Prop) (p1 : _104907) : (term20 _104907 p1 t) = (term21 _104907 t p1).
Proof. exact (MK_COMB (@lem4374401 _104907 t) (@lem4374405 _104907 t p1)). Qed.
Lemma lem4374408 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4374409 {_104907 : Type'} (t : _104907 -> Prop) (p1 : _104907) : (term21 _104907 t p1) = True.
Proof. exact (@lem4374408 (t p1)). Qed.
Lemma lem4374410 {_104907 : Type'} (p1 : _104907) (t : _104907 -> Prop) : (term20 _104907 p1 t) = True.
Proof. exact (TRANS (@lem4374406 _104907 t p1) (@lem4374409 _104907 t p1)). Qed.
Lemma lem4374411 {_104907 : Type'} (p1 : _104907) : (term22 _104907 p1) = (term23 _104907).
Proof. exact (fun_ext (fun t : _104907 -> Prop => @lem4374410 _104907 p1 t)). Qed.
Lemma lem4374412 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4374413 {_104907 : Type'} (p1 : _104907) : (term18 _104907 p1) = (term24 _104907).
Proof. exact (MK_COMB (@lem4374412 _104907) (@lem4374411 _104907 p1)). Qed.
Lemma lem4374415 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4374416 {_104907 : Type'} (t : Prop) : (term26 _104907 t) = t.
Proof. exact (@lem4374415 (_104907 -> Prop) t). Qed.
Lemma lem4374417 {_104907 : Type'} : (term24 _104907) = True.
Proof. exact (@lem4374416 _104907 True). Qed.
Lemma lem4374418 {_104907 : Type'} (p1 : _104907) : (term18 _104907 p1) = True.
Proof. exact (TRANS (@lem4374413 _104907 p1) (@lem4374417 _104907)). Qed.
Lemma lem4374419 {_104907 : Type'} (p1 : _104907) : (term17 _104907 p1) = True.
Proof. exact (TRANS (@lem4374389 _104907 p1) (@lem4374418 _104907 p1)). Qed.
Lemma lem4374420 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4374421 {_104907 : Type'} (p1 : _104907) : (term27 _104907 p1) = (and True).
Proof. exact (MK_COMB (@lem4374420) (@lem4374419 _104907 p1)). Qed.
Lemma lem4374423 {A : Type'} (s : type686 A) (x : A) : (term15 A x s) = (term16 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem4374424 {_104908 : Type'} (s : type686 _104908) (x : _104908) : (term15 _104908 x s) = (term16 _104908 s x).
Proof. exact (@lem4374423 _104908 s x). Qed.
Lemma lem4374425 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term15 _104908 p2 g) = (term16 _104908 g p2).
Proof. exact (@lem4374424 _104908 g p2). Qed.
Lemma lem4374433 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4374434 {_104908 : Type'} (P : type686 _104908) (x : _104908 -> Prop) : (@IN (_104908 -> Prop) x P) = (P x).
Proof. exact (@lem4374433 (_104908 -> Prop) P x). Qed.
Lemma lem4374435 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (@IN (_104908 -> Prop) t g) = (g t).
Proof. exact (@lem4374434 _104908 g t). Qed.
Lemma lem4374436 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4374437 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (term28 _104908 t g) = (term29 _104908 g t).
Proof. exact (MK_COMB (@lem4374436) (@lem4374435 _104908 g t)). Qed.
Lemma lem4374439 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4374440 {_104908 : Type'} (P : _104908 -> Prop) (x : _104908) : (@IN _104908 x P) = (P x).
Proof. exact (@lem4374439 _104908 P x). Qed.
Lemma lem4374441 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (@IN _104908 p2 t) = (t p2).
Proof. exact (@lem4374440 _104908 t p2). Qed.
Lemma lem4374442 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term30 _104908 g p2 t) = (term31 _104908 g t p2).
Proof. exact (MK_COMB (@lem4374437 _104908 g t) (@lem4374441 _104908 t p2)). Qed.
Lemma lem4374445 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term32 _104908 g p2) = (term33 _104908 g p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4374442 _104908 g t p2)). Qed.
Lemma lem4374446 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4374447 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term16 _104908 g p2) = (term34 _104908 g p2).
Proof. exact (MK_COMB (@lem4374446 _104908) (@lem4374445 _104908 g p2)). Qed.
Lemma lem4374452 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term15 _104908 p2 g) = (term34 _104908 g p2).
Proof. exact (TRANS (@lem4374425 _104908 g p2) (@lem4374447 _104908 g p2)). Qed.
Lemma lem4374453 {_104907 _104908 : Type'} (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term35 _104907 _104908 p1 p2 g) = (term36 _104908 g p2).
Proof. exact (MK_COMB (@lem4374421 _104907 p1) (@lem4374452 _104908 g p2)). Qed.
Lemma lem4374455 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4374456 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term36 _104908 g p2) = (term34 _104908 g p2).
Proof. exact (@lem4374455 (term34 _104908 g p2)). Qed.
Lemma lem4374463 {_104907 _104908 : Type'} (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term35 _104907 _104908 p1 p2 g) = (term34 _104908 g p2).
Proof. exact (TRANS (@lem4374453 _104907 _104908 p1 g p2) (@lem4374456 _104908 g p2)). Qed.
Lemma lem4374464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4374465 {_104907 _104908 : Type'} (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term37 _104907 _104908 p1 p2 g) = (term38 _104908 g p2).
Proof. exact (MK_COMB (@lem4374464) (@lem4374463 _104907 _104908 p1 g p2)). Qed.
Lemma lem4374473 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4374474 {_104908 : Type'} (P : type686 _104908) (x : _104908 -> Prop) : (@IN (_104908 -> Prop) x P) = (P x).
Proof. exact (@lem4374473 (_104908 -> Prop) P x). Qed.
Lemma lem4374475 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (@IN (_104908 -> Prop) t g) = (g t).
Proof. exact (@lem4374474 _104908 g t). Qed.
Lemma lem4374476 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4374477 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (term28 _104908 t g) = (term29 _104908 g t).
Proof. exact (MK_COMB (@lem4374476) (@lem4374475 _104908 g t)). Qed.
Lemma lem4374481 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem4374482 {_104907 : Type'} (x : _104907) : (@IN _104907 x (@UNIV _104907)) = True.
Proof. exact (@lem4374481 _104907 x). Qed.
Lemma lem4374483 {_104907 : Type'} (p1 : _104907) : (@IN _104907 p1 (@UNIV _104907)) = True.
Proof. exact (@lem4374482 _104907 p1). Qed.
Lemma lem4374484 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4374485 {_104907 : Type'} (p1 : _104907) : (term39 _104907 p1) = (and True).
Proof. exact (MK_COMB (@lem4374484) (@lem4374483 _104907 p1)). Qed.
Lemma lem4374487 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4374488 {_104908 : Type'} (P : _104908 -> Prop) (x : _104908) : (@IN _104908 x P) = (P x).
Proof. exact (@lem4374487 _104908 P x). Qed.
Lemma lem4374489 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (@IN _104908 p2 t) = (t p2).
Proof. exact (@lem4374488 _104908 t p2). Qed.
Lemma lem4374490 {_104907 _104908 : Type'} (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term40 _104907 _104908 p1 p2 t) = (term41 _104908 t p2).
Proof. exact (MK_COMB (@lem4374485 _104907 p1) (@lem4374489 _104908 t p2)). Qed.
Lemma lem4374492 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4374493 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (term41 _104908 t p2) = (t p2).
Proof. exact (@lem4374492 (t p2)). Qed.
Lemma lem4374494 {_104907 _104908 : Type'} (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term40 _104907 _104908 p1 p2 t) = (t p2).
Proof. exact (TRANS (@lem4374490 _104907 _104908 p1 t p2) (@lem4374493 _104908 t p2)). Qed.
Lemma lem4374495 {_104907 _104908 : Type'} (p1 : _104907) (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term42 _104907 _104908 g p1 p2 t) = (term31 _104908 g t p2).
Proof. exact (MK_COMB (@lem4374477 _104908 g t) (@lem4374494 _104907 _104908 p1 t p2)). Qed.
Lemma lem4374498 {_104907 _104908 : Type'} (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term43 _104907 _104908 g p1 p2) = (term33 _104908 g p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4374495 _104907 _104908 p1 g t p2)). Qed.
Lemma lem4374499 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4374500 {_104907 _104908 : Type'} (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term44 _104907 _104908 g p1 p2) = (term34 _104908 g p2).
Proof. exact (MK_COMB (@lem4374499 _104908) (@lem4374498 _104907 _104908 p1 g p2)). Qed.
Lemma lem4374505 {_104907 _104908 : Type'} (p1 : _104907) (g : type686 _104908) (p2 : _104908) : ((term35 _104907 _104908 p1 p2 g) = (term44 _104907 _104908 g p1 p2)) = ((term34 _104908 g p2) = (term34 _104908 g p2)).
Proof. exact (MK_COMB (@lem4374465 _104907 _104908 p1 g p2) (@lem4374500 _104907 _104908 p1 g p2)). Qed.
Lemma lem4374507 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4374508 (x : Prop) : (x = x) = True.
Proof. exact (@lem4374507 Prop x). Qed.
Lemma lem4374509 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : ((term34 _104908 g p2) = (term34 _104908 g p2)) = True.
Proof. exact (@lem4374508 (term34 _104908 g p2)). Qed.
Lemma lem4374510 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term35 _104907 _104908 p1 p2 g) = (term44 _104907 _104908 g p1 p2)) = True.
Proof. exact (TRANS (@lem4374505 _104907 _104908 p1 g p2) (@lem4374509 _104908 g p2)). Qed.
Lemma lem4374511 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) : (term45 _104907 _104908 g p1) = (term46 _104908).
Proof. exact (fun_ext (fun p2 : _104908 => @lem4374510 _104907 _104908 g p1 p2)). Qed.
Lemma lem4374512 {_104908 : Type'} : (@all _104908) = (@all _104908).
Proof. exact (eq_refl (@all _104908)). Qed.
Lemma lem4374513 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) : (term47 _104907 _104908 g p1) = (term48 _104908).
Proof. exact (MK_COMB (@lem4374512 _104908) (@lem4374511 _104907 _104908 g p1)). Qed.
Lemma lem4374515 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4374516 {_104908 : Type'} (t : Prop) : (term25 _104908 t) = t.
Proof. exact (@lem4374515 _104908 t). Qed.
Lemma lem4374517 {_104908 : Type'} : (term48 _104908) = True.
Proof. exact (@lem4374516 _104908 True). Qed.
Lemma lem4374518 {_104907 _104908 : Type'} (g : type686 _104908) (p1 : _104907) : (term47 _104907 _104908 g p1) = True.
Proof. exact (TRANS (@lem4374513 _104907 _104908 g p1) (@lem4374517 _104908)). Qed.
Lemma lem4374519 {_104907 _104908 : Type'} (g : type686 _104908) : (term49 _104907 _104908 g) = (term46 _104907).
Proof. exact (fun_ext (fun p1 : _104907 => @lem4374518 _104907 _104908 g p1)). Qed.
Lemma lem4374520 {_104907 : Type'} : (@all _104907) = (@all _104907).
Proof. exact (eq_refl (@all _104907)). Qed.
Lemma lem4374521 {_104907 _104908 : Type'} (g : type686 _104908) : (term5 _104907 _104908 g) = (term48 _104907).
Proof. exact (MK_COMB (@lem4374520 _104907) (@lem4374519 _104907 _104908 g)). Qed.
Lemma lem4374523 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4374524 {_104907 : Type'} (t : Prop) : (term25 _104907 t) = t.
Proof. exact (@lem4374523 _104907 t). Qed.
Lemma lem4374525 {_104907 : Type'} : (term48 _104907) = True.
Proof. exact (@lem4374524 _104907 True). Qed.
Lemma lem4374526 {_104907 _104908 : Type'} (g : type686 _104908) : (term5 _104907 _104908 g) = True.
Proof. exact (TRANS (@lem4374521 _104907 _104908 g) (@lem4374525 _104907)). Qed.
Lemma lem4374527 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term7 _104907 _104908 f g) = (term50 _104907 f).
Proof. exact (MK_COMB (@lem4374373 _104907 f) (@lem4374526 _104907 _104908 g)). Qed.
Lemma lem4374529 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4374530 {_104907 : Type'} (f : type686 _104907) : (term50 _104907 f) = True.
Proof. exact (@lem4374529 (term13 _104907 f)). Qed.
Lemma lem4374531 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term7 _104907 _104908 f g) = True.
Proof. exact (TRANS (@lem4374527 _104907 _104908 g f) (@lem4374530 _104907 f)). Qed.
Lemma lem4374532 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : True = (term7 _104907 _104908 f g).
Proof. exact (SYM (@lem4374531 _104907 _104908 f g)). Qed.
Lemma lem4374533 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : term7 _104907 _104908 f g.
Proof. exact (EQ_MP (@lem4374532 _104907 _104908 f g) (@lem0)). Qed.
Lemma lem4374534 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : term6 _104907 _104908 f g.
Proof. exact (EQ_MP (@lem4374342 _104907 _104908 f g) (@lem4374533 _104907 _104908 f g)). Qed.
Lemma lem4374535 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : f = (@EMPTY (_104907 -> Prop))) : term5 _104907 _104908 g.
Proof. exact (@lem4374534 _104907 _104908 f g (@lem4372173 _104907 f h1)). Qed.
