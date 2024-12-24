Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_BOUND_term_abbrevs.
Require Import NSUM_CONST_spec.
Require Import NSUM_LE_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem6970345 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) (h1 : (term0 _127196 s c) = (term1 _127196 s c)) : (term0 _127196 s c) = (term1 _127196 s c).
Proof. exact (h1). Qed.
Lemma lem6970346 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) (h1 : (term0 _127196 s c) = (term1 _127196 s c)) : (term1 _127196 s c) = (term0 _127196 s c).
Proof. exact (SYM (@lem6970345 _127196 s c h1)). Qed.
Lemma lem6970347 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) (h1 : (term1 _127196 s c) = (term0 _127196 s c)) : (term1 _127196 s c) = (term0 _127196 s c).
Proof. exact (h1). Qed.
Lemma lem6970348 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) (h1 : (term1 _127196 s c) = (term0 _127196 s c)) : (term0 _127196 s c) = (term1 _127196 s c).
Proof. exact (SYM (@lem6970347 _127196 s c h1)). Qed.
Lemma lem6970349 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : ((term0 _127196 s c) = (term1 _127196 s c)) = ((term1 _127196 s c) = (term0 _127196 s c)).
Proof. exact (prop_ext (fun h1 : (term0 _127196 s c) = (term1 _127196 s c) => @lem6970346 _127196 s c h1) (fun h1 : (term1 _127196 s c) = (term0 _127196 s c) => @lem6970348 _127196 s c h1)). Qed.
Lemma lem6970350 {_127196 : Type'} (s : _127196 -> Prop) : (term2 _127196 s) = (term2 _127196 s).
Proof. exact (eq_refl (term2 _127196 s)). Qed.
Lemma lem6970351 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term3 _127196 s c) = (term4 _127196 s c).
Proof. exact (MK_COMB (@lem6970350 _127196 s) (@lem6970349 _127196 s c)). Qed.
Lemma lem6970352 {_127196 : Type'} (c : nat) : (term5 _127196 c) = (term6 _127196 c).
Proof. exact (fun_ext (fun s : _127196 -> Prop => @lem6970351 _127196 s c)). Qed.
Lemma lem6970353 {_127196 : Type'} : (@all (_127196 -> Prop)) = (@all (_127196 -> Prop)).
Proof. exact (eq_refl (@all (_127196 -> Prop))). Qed.
Lemma lem6970354 {_127196 : Type'} (c : nat) : (term7 _127196 c) = (term8 _127196 c).
Proof. exact (MK_COMB (@lem6970353 _127196) (@lem6970352 _127196 c)). Qed.
Lemma lem6970355 {_127196 : Type'} : (term9 _127196) = (term10 _127196).
Proof. exact (fun_ext (fun c : nat => @lem6970354 _127196 c)). Qed.
Lemma lem6970356 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6970357 {_127196 : Type'} : (term11 _127196) = (term12 _127196).
Proof. exact (MK_COMB (@lem6970356) (@lem6970355 _127196)). Qed.
Lemma lem6970358 {_127196 : Type'} : term12 _127196.
Proof. exact (EQ_MP (@lem6970357 _127196) (@lem6940531 _127196)). Qed.
Lemma lem6970359 {_127006 : Type'} (f : _127006 -> nat) : term13 _127006 f.
Proof. exact (@lem6933015 _127006 f). Qed.
Lemma lem6970360 {_127006 : Type'} (f : _127006 -> nat) : (term13 _127006 f) = (term14 _127006 f).
Proof. exact (eq_refl (term13 _127006 f)). Qed.
Lemma lem6970361 {_127006 : Type'} (f : _127006 -> nat) : term14 _127006 f.
Proof. exact (EQ_MP (@lem6970360 _127006 f) (@lem6970359 _127006 f)). Qed.
Lemma lem6970362 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : term15 _127006 f g.
Proof. exact (@lem6970361 _127006 f g). Qed.
Lemma lem6970363 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : (term15 _127006 f g) = (term16 _127006 f g).
Proof. exact (eq_refl (term15 _127006 f g)). Qed.
Lemma lem6970364 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) : term16 _127006 f g.
Proof. exact (EQ_MP (@lem6970363 _127006 f g) (@lem6970362 _127006 f g)). Qed.
Lemma lem6970365 {_127006 : Type'} (f : _127006 -> nat) (g : _127006 -> nat) (s : _127006 -> Prop) : term17 _127006 f g s.
Proof. exact (@lem6970364 _127006 f g s). Qed.
Lemma lem6970366 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : (term17 _127006 f g s) = (term18 _127006 f s g).
Proof. exact (eq_refl (term17 _127006 f g s)). Qed.
Lemma lem6970367 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : term18 _127006 f s g.
Proof. exact (EQ_MP (@lem6970366 _127006 f s g) (@lem6970365 _127006 f g s)). Qed.
Lemma lem6970368 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term19 _127006 s f g) : term19 _127006 s f g.
Proof. exact (h1). Qed.
Lemma lem6970369 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term19 _127006 s f g) : term20 _127006 f s g.
Proof. exact (@lem6970367 _127006 f s g (@lem6970368 _127006 s f g h1)). Qed.
Lemma lem6970370 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : (term20 _127006 f s g) = ((term20 _127006 f s g) = True).
Proof. exact (@lem7 (term20 _127006 f s g)). Qed.
Lemma lem6970371 {_127006 : Type'} (s : _127006 -> Prop) (f : _127006 -> nat) (g : _127006 -> nat) (h1 : term19 _127006 s f g) : (term20 _127006 f s g) = True.
Proof. exact (EQ_MP (@lem6970370 _127006 f s g) (@lem6970369 _127006 s f g h1)). Qed.
Lemma lem6970377 {_127196 : Type'} (c : nat) : term21 _127196 c.
Proof. exact (@lem6970358 _127196 c). Qed.
Lemma lem6970378 {_127196 : Type'} (c : nat) : (term21 _127196 c) = (term8 _127196 c).
Proof. exact (eq_refl (term21 _127196 c)). Qed.
Lemma lem6970379 {_127196 : Type'} (c : nat) : term8 _127196 c.
Proof. exact (EQ_MP (@lem6970378 _127196 c) (@lem6970377 _127196 c)). Qed.
Lemma lem6970380 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) : term22 _127196 c s.
Proof. exact (@lem6970379 _127196 c s). Qed.
Lemma lem6970381 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : (term22 _127196 c s) = (term4 _127196 s c).
Proof. exact (eq_refl (term22 _127196 c s)). Qed.
Lemma lem6970382 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : term4 _127196 s c.
Proof. exact (EQ_MP (@lem6970381 _127196 s c) (@lem6970380 _127196 c s)). Qed.
Lemma lem6970383 {_127196 : Type'} (s : _127196 -> Prop) (h1 : @FINITE _127196 s) : @FINITE _127196 s.
Proof. exact (h1). Qed.
Lemma lem6970384 {_127196 : Type'} (c : nat) (s : _127196 -> Prop) (h1 : @FINITE _127196 s) : (term1 _127196 s c) = (term0 _127196 s c).
Proof. exact (@lem6970382 _127196 s c (@lem6970383 _127196 s h1)). Qed.
Lemma lem6970405 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term23 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6970406 (p : Prop) (q : Prop) (p' : Prop) : term24 p q p'.
Proof. exact (fun q' : Prop => @lem6970405 p q p' q'). Qed.
Lemma lem6970407 (p : Prop) (q : Prop) : term25 p q.
Proof. exact (fun p' : Prop => @lem6970406 p q p'). Qed.
Lemma lem6970408 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : term26 A f s b.
Proof. exact (@lem6970407 (term27 A s f b) (term28 A f s b)). Qed.
Lemma lem6970409 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) (p' : Prop) : term29 A f s b p'.
Proof. exact (@lem6970408 A f s b p'). Qed.
Lemma lem6970410 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) (p' : Prop) : (term29 A f s b p') = (term30 A f s b p').
Proof. exact (eq_refl (term29 A f s b p')). Qed.
Lemma lem6970411 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) (p' : Prop) : term30 A f s b p'.
Proof. exact (EQ_MP (@lem6970410 A f s b p') (@lem6970409 A f s b p')). Qed.
Lemma lem6970412 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) (p' : Prop) (q' : Prop) : term31 A f s b p' q'.
Proof. exact (@lem6970411 A f s b p' q'). Qed.
Lemma lem6970413 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) (p' : Prop) (q' : Prop) : (term31 A f s b p' q') = (term32 A f s b p' q').
Proof. exact (eq_refl (term31 A f s b p' q')). Qed.
Lemma lem6970414 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) (p' : Prop) (q' : Prop) : term32 A f s b p' q'.
Proof. exact (EQ_MP (@lem6970413 A f s b p' q') (@lem6970412 A f s b p' q')). Qed.
Lemma lem6970444 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term27 A s f b) = (term27 A s f b).
Proof. exact (eq_refl (term27 A s f b)). Qed.
Lemma lem6970445 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (q' : Prop) : term33 A s f b q'.
Proof. exact (@lem6970414 A f s b (term27 A s f b) q'). Qed.
Lemma lem6970446 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (q' : Prop) : term34 A s f b q'.
Proof. exact (@lem6970445 A s f b q' (@lem6970444 A s f b)). Qed.
Lemma lem6970447 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : term27 A s f b.
Proof. exact (h1). Qed.
Lemma lem6970448 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : term35 A s f b.
Proof. exact (proj2 (@lem6970447 A s f b h1)). Qed.
Lemma lem6970449 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : term36 A s f b x.
Proof. exact (@lem6970448 A s f b h1 x). Qed.
Lemma lem6970450 {A : Type'} (s : A -> Prop) (f : A -> nat) (x : A) (b : nat) : (term36 A s f b x) = (term37 A s f x b).
Proof. exact (eq_refl (term36 A s f b x)). Qed.
Lemma lem6970451 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : term37 A s f x b.
Proof. exact (EQ_MP (@lem6970450 A s f x b) (@lem6970449 A x s f b h1)). Qed.
Lemma lem6970452 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem6970453 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term27 A s f b) (h2 : @IN A x s) : term38 A f x b.
Proof. exact (@lem6970451 A x s f b h1 (@lem6970452 A x s h2)). Qed.
Lemma lem6970454 {A : Type'} (f : A -> nat) (x : A) (b : nat) : (term38 A f x b) = ((term38 A f x b) = True).
Proof. exact (@lem7 (term38 A f x b)). Qed.
Lemma lem6970455 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term27 A s f b) (h2 : @IN A x s) : (term38 A f x b) = True.
Proof. exact (EQ_MP (@lem6970454 A f x b) (@lem6970453 A f b x s h1 h2)). Qed.
Lemma lem6970461 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : @FINITE A s.
Proof. exact (proj1 (@lem6970447 A s f b h1)). Qed.
Lemma lem6970462 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem6970465 {_127196 : Type'} (s : _127196 -> Prop) (c : nat) : term4 _127196 s c.
Proof. exact (fun h0 : @FINITE _127196 s => @lem6970384 _127196 c s h0). Qed.
Lemma lem6970466 {A : Type'} (s : A -> Prop) (c : nat) : term4 A s c.
Proof. exact (@lem6970465 A s c). Qed.
Lemma lem6970467 {A : Type'} (s : A -> Prop) (b : nat) : term4 A s b.
Proof. exact (@lem6970466 A s b). Qed.
Lemma lem6970469 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6970462 A s) (@lem6970461 A s f b h1)). Qed.
Lemma lem6970470 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : True = (@FINITE A s).
Proof. exact (SYM (@lem6970469 A s f b h1)). Qed.
Lemma lem6970471 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : @FINITE A s.
Proof. exact (EQ_MP (@lem6970470 A s f b h1) (@lem0)). Qed.
Lemma lem6970472 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : (term1 A s b) = (term0 A s b).
Proof. exact (@lem6970467 A s b (@lem6970471 A s f b h1)). Qed.
Lemma lem6970473 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term39 A s f) = (term39 A s f).
Proof. exact (eq_refl (term39 A s f)). Qed.
Lemma lem6970474 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : (term28 A f s b) = (term40 A f s b).
Proof. exact (MK_COMB (@lem6970473 A s f) (@lem6970472 A s f b h1)). Qed.
Lemma lem6970476 {_127006 : Type'} (f : _127006 -> nat) (s : _127006 -> Prop) (g : _127006 -> nat) : term41 _127006 f s g.
Proof. exact (fun h0 : term19 _127006 s f g => @lem6970371 _127006 s f g h0). Qed.
Lemma lem6970477 {A : Type'} (f : A -> nat) (s : A -> Prop) (g : A -> nat) : term41 A f s g.
Proof. exact (@lem6970476 A f s g). Qed.
Lemma lem6970478 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : term42 A f s b.
Proof. exact (@lem6970477 A f s (term43 A b)). Qed.
Lemma lem6970482 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem6970462 A s) (@lem6970461 A s f b h1)). Qed.
Lemma lem6970483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6970484 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : (term44 A s) = (and True).
Proof. exact (MK_COMB (@lem6970483) (@lem6970482 A s f b h1)). Qed.
Lemma lem6970492 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term23 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6970493 (p : Prop) (q : Prop) (p' : Prop) : term24 p q p'.
Proof. exact (fun q' : Prop => @lem6970492 p q p' q'). Qed.
Lemma lem6970494 (p : Prop) (q : Prop) : term25 p q.
Proof. exact (fun p' : Prop => @lem6970493 p q p'). Qed.
Lemma lem6970495 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x : A) : term45 A s f b x.
Proof. exact (@lem6970494 (@IN A x s) (term46 A f b x)). Qed.
Lemma lem6970496 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x : A) (p' : Prop) : term47 A s f b x p'.
Proof. exact (@lem6970495 A s f b x p'). Qed.
Lemma lem6970497 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x : A) (p' : Prop) : (term47 A s f b x p') = (term48 A s f b x p').
Proof. exact (eq_refl (term47 A s f b x p')). Qed.
Lemma lem6970498 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x : A) (p' : Prop) : term48 A s f b x p'.
Proof. exact (EQ_MP (@lem6970497 A s f b x p') (@lem6970496 A s f b x p')). Qed.
Lemma lem6970499 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x : A) (p' : Prop) (q' : Prop) : term49 A s f b x p' q'.
Proof. exact (@lem6970498 A s f b x p' q'). Qed.
Lemma lem6970500 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x : A) (p' : Prop) (q' : Prop) : (term49 A s f b x p' q') = (term50 A s f b x p' q').
Proof. exact (eq_refl (term49 A s f b x p' q')). Qed.
Lemma lem6970501 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (x : A) (p' : Prop) (q' : Prop) : term50 A s f b x p' q'.
Proof. exact (EQ_MP (@lem6970500 A s f b x p' q') (@lem6970499 A s f b x p' q')). Qed.
Lemma lem6970502 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem6970503 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (q' : Prop) : term51 A f b x s q'.
Proof. exact (@lem6970501 A s f b x (@IN A x s) q'). Qed.
Lemma lem6970504 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (q' : Prop) : term52 A f b x s q'.
Proof. exact (@lem6970503 A f b x s q' (@lem6970502 A x s)). Qed.
Lemma lem6970505 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem6970506 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem6970509 {A B : Type'} (f : A -> B) (y : A) : (term53 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem6970510 {A : Type'} (f : A -> nat) (y : A) : (term54 A f y) = (f y).
Proof. exact (@lem6970509 A nat f y). Qed.
Lemma lem6970511 {A : Type'} (b : nat) (x : A) : (term55 A b x) = (term56 A b x).
Proof. exact (@lem6970510 A (term43 A b) x). Qed.
Lemma lem6970512 {A : Type'} (n : A) (b : nat) : (term56 A b n) = b.
Proof. exact (eq_refl (term56 A b n)). Qed.
Lemma lem6970513 {A : Type'} (b : nat) : (term57 A b) = (term43 A b).
Proof. exact (fun_ext (fun n : A => @lem6970512 A n b)). Qed.
Lemma lem6970514 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6970515 {A : Type'} (b : nat) (x : A) : (term55 A b x) = (term56 A b x).
Proof. exact (MK_COMB (@lem6970513 A b) (@lem6970514 A x)). Qed.
Lemma lem6970516 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6970517 {A : Type'} (b : nat) (x : A) : (term58 A b x) = (term59 A b x).
Proof. exact (MK_COMB (@lem6970516) (@lem6970515 A b x)). Qed.
Lemma lem6970518 {A : Type'} (x : A) (b : nat) : (term56 A b x) = b.
Proof. exact (eq_refl (term56 A b x)). Qed.
Lemma lem6970519 {A : Type'} (x : A) (b : nat) : ((term55 A b x) = (term56 A b x)) = ((term56 A b x) = b).
Proof. exact (MK_COMB (@lem6970517 A b x) (@lem6970518 A x b)). Qed.
Lemma lem6970520 {A : Type'} (x : A) (b : nat) : (term56 A b x) = b.
Proof. exact (EQ_MP (@lem6970519 A x b) (@lem6970511 A b x)). Qed.
Lemma lem6970521 {A : Type'} (f : A -> nat) (x : A) : (term60 A f x) = (term60 A f x).
Proof. exact (eq_refl (term60 A f x)). Qed.
Lemma lem6970522 {A : Type'} (f : A -> nat) (x : A) (b : nat) : (term46 A f b x) = (term38 A f x b).
Proof. exact (MK_COMB (@lem6970521 A f x) (@lem6970520 A x b)). Qed.
Lemma lem6970524 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : term61 A s f x b.
Proof. exact (fun h0 : @IN A x s => @lem6970455 A f b x s h1 h0). Qed.
Lemma lem6970525 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : term61 A s f x b.
Proof. exact (@lem6970524 A x s f b h1). Qed.
Lemma lem6970527 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem6970506 A x s) (@lem6970505 A x s h1)). Qed.
Lemma lem6970528 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : True = (@IN A x s).
Proof. exact (SYM (@lem6970527 A x s h1)). Qed.
Lemma lem6970529 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem6970528 A x s h1) (@lem0)). Qed.
Lemma lem6970530 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term27 A s f b) (h2 : @IN A x s) : (term38 A f x b) = True.
Proof. exact (@lem6970525 A x s f b h1 (@lem6970529 A x s h2)). Qed.
Lemma lem6970531 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) (h1 : term27 A s f b) (h2 : @IN A x s) : (term46 A f b x) = True.
Proof. exact (TRANS (@lem6970522 A f x b) (@lem6970530 A f b x s h1 h2)). Qed.
Lemma lem6970532 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : term62 A s f b x.
Proof. exact (fun h0 : @IN A x s => @lem6970531 A f b x s h1 h0). Qed.
Lemma lem6970533 {A : Type'} (f : A -> nat) (b : nat) (x : A) (s : A -> Prop) : term63 A f b x s.
Proof. exact (@lem6970504 A f b x s True). Qed.
Lemma lem6970534 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : (term64 A s f b x) = (term65 A x s).
Proof. exact (@lem6970533 A f b x s (@lem6970532 A x s f b h1)). Qed.
Lemma lem6970536 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6970537 {A : Type'} (x : A) (s : A -> Prop) : (term65 A x s) = True.
Proof. exact (@lem6970536 (@IN A x s)). Qed.
Lemma lem6970538 {A : Type'} (x : A) (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : (term64 A s f b x) = True.
Proof. exact (TRANS (@lem6970534 A x s f b h1) (@lem6970537 A x s)). Qed.
Lemma lem6970539 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : (term66 A s f b) = (term67 A).
Proof. exact (fun_ext (fun x : A => @lem6970538 A x s f b h1)). Qed.
Lemma lem6970540 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6970541 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : (term68 A s f b) = (term69 A).
Proof. exact (MK_COMB (@lem6970540 A) (@lem6970539 A s f b h1)). Qed.
Lemma lem6970543 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6970544 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (@lem6970543 A t). Qed.
Lemma lem6970545 {A : Type'} : (term69 A) = True.
Proof. exact (@lem6970544 A True). Qed.
Lemma lem6970546 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : (term68 A s f b) = True.
Proof. exact (TRANS (@lem6970541 A s f b h1) (@lem6970545 A)). Qed.
Lemma lem6970547 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : (term71 A s f b) = (True /\ True).
Proof. exact (MK_COMB (@lem6970484 A s f b h1) (@lem6970546 A s f b h1)). Qed.
Lemma lem6970549 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6970550 : (True /\ True) = True.
Proof. exact (@lem6970549 True). Qed.
Lemma lem6970551 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : (term71 A s f b) = True.
Proof. exact (TRANS (@lem6970547 A s f b h1) (@lem6970550)). Qed.
Lemma lem6970552 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : True = (term71 A s f b).
Proof. exact (SYM (@lem6970551 A s f b h1)). Qed.
Lemma lem6970553 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : term71 A s f b.
Proof. exact (EQ_MP (@lem6970552 A s f b h1) (@lem0)). Qed.
Lemma lem6970554 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : (term40 A f s b) = True.
Proof. exact (@lem6970478 A f s b (@lem6970553 A s f b h1)). Qed.
Lemma lem6970555 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) (h1 : term27 A s f b) : (term28 A f s b) = True.
Proof. exact (TRANS (@lem6970474 A s f b h1) (@lem6970554 A s f b h1)). Qed.
Lemma lem6970556 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : term72 A f s b.
Proof. exact (fun h0 : term27 A s f b => @lem6970555 A s f b h0). Qed.
Lemma lem6970557 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : term73 A s f b.
Proof. exact (@lem6970446 A s f b True). Qed.
Lemma lem6970558 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term74 A f s b) = (term75 A s f b).
Proof. exact (@lem6970557 A s f b (@lem6970556 A f s b)). Qed.
Lemma lem6970560 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6970561 {A : Type'} (s : A -> Prop) (f : A -> nat) (b : nat) : (term75 A s f b) = True.
Proof. exact (@lem6970560 (term27 A s f b)). Qed.
Lemma lem6970562 {A : Type'} (f : A -> nat) (s : A -> Prop) (b : nat) : (term74 A f s b) = True.
Proof. exact (TRANS (@lem6970558 A s f b) (@lem6970561 A s f b)). Qed.
Lemma lem6970563 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term76 A f s) = term77.
Proof. exact (fun_ext (fun b : nat => @lem6970562 A f s b)). Qed.
Lemma lem6970564 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6970565 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term78 A f s) = term79.
Proof. exact (MK_COMB (@lem6970564) (@lem6970563 A f s)). Qed.
Lemma lem6970567 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6970568 (t : Prop) : (term80 t) = t.
Proof. exact (@lem6970567 nat t). Qed.
Lemma lem6970569 : term79 = True.
Proof. exact (@lem6970568 True). Qed.
Lemma lem6970570 {A : Type'} (f : A -> nat) (s : A -> Prop) : (term78 A f s) = True.
Proof. exact (TRANS (@lem6970565 A f s) (@lem6970569)). Qed.
Lemma lem6970571 {A : Type'} (s : A -> Prop) : (term81 A s) = (term82 A).
Proof. exact (fun_ext (fun f : A -> nat => @lem6970570 A f s)). Qed.
Lemma lem6970572 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem6970573 {A : Type'} (s : A -> Prop) : (term83 A s) = (term84 A).
Proof. exact (MK_COMB (@lem6970572 A) (@lem6970571 A s)). Qed.
Lemma lem6970575 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6970576 {A : Type'} (t : Prop) : (term85 A t) = t.
Proof. exact (@lem6970575 (A -> nat) t). Qed.
Lemma lem6970577 {A : Type'} : (term84 A) = True.
Proof. exact (@lem6970576 A True). Qed.
Lemma lem6970578 {A : Type'} (s : A -> Prop) : (term83 A s) = True.
Proof. exact (TRANS (@lem6970573 A s) (@lem6970577 A)). Qed.
Lemma lem6970579 {A : Type'} : (term86 A) = (term87 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem6970578 A s)). Qed.
Lemma lem6970580 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6970581 {A : Type'} : (term88 A) = (term89 A).
Proof. exact (MK_COMB (@lem6970580 A) (@lem6970579 A)). Qed.
Lemma lem6970583 {A : Type'} (t : Prop) : (term70 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6970584 {A : Type'} (t : Prop) : (term90 A t) = t.
Proof. exact (@lem6970583 (A -> Prop) t). Qed.
Lemma lem6970585 {A : Type'} : (term89 A) = True.
Proof. exact (@lem6970584 A True). Qed.
Lemma lem6970586 {A : Type'} : (term88 A) = True.
Proof. exact (TRANS (@lem6970581 A) (@lem6970585 A)). Qed.
Lemma lem6970587 {A : Type'} : True = (term88 A).
Proof. exact (SYM (@lem6970586 A)). Qed.
Lemma lem6970588 {A : Type'} : term88 A.
Proof. exact (EQ_MP (@lem6970587 A) (@lem0)). Qed.
