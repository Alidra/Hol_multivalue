Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_OFFSET_term_abbrevs.
Require Import EQ_ADD_RCANCEL_spec.
Require Import NSUM_IMAGE_spec.
Require Import NUMSEG_OFFSET_IMAGE_spec.
Require Import o_DEF_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Lemma lem7048326 {A B C : Type'} (f : B -> C) : term0 A B C f.
Proof. exact (@lem15397 A B C f). Qed.
Lemma lem7048327 {A B C : Type'} (f : B -> C) : (term0 A B C f) = (term1 A B C f).
Proof. exact (eq_refl (term0 A B C f)). Qed.
Lemma lem7048328 {A B C : Type'} (f : B -> C) : term1 A B C f.
Proof. exact (EQ_MP (@lem7048327 A B C f) (@lem7048326 A B C f)). Qed.
Lemma lem7048329 {A B C : Type'} (f : B -> C) (g : A -> B) : term2 A B C f g.
Proof. exact (@lem7048328 A B C f g). Qed.
Lemma lem7048330 {A B C : Type'} (f : B -> C) (g : A -> B) : (term2 A B C f g) = ((@o A B C f g) = (term3 A B C f g)).
Proof. exact (eq_refl (term2 A B C f g)). Qed.
Lemma lem7048340 (m : nat) : term4 m.
Proof. exact (@lem79714 m). Qed.
Lemma lem7048341 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem7048342 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem7048341 m) (@lem7048340 m)). Qed.
Lemma lem7048343 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem7048342 m n). Qed.
Lemma lem7048344 (m : nat) (n : nat) : (term6 m n) = (term7 m n).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem7048345 (m : nat) (n : nat) : term7 m n.
Proof. exact (EQ_MP (@lem7048344 m n) (@lem7048343 m n)). Qed.
Lemma lem7048346 (m : nat) (n : nat) (p : nat) : term8 m n p.
Proof. exact (@lem7048345 m n p). Qed.
Lemma lem7048347 (p : nat) (m : nat) (n : nat) : (term8 m n p) = (((Nat.add m p) = (Nat.add n p)) = (m = n)).
Proof. exact (eq_refl (term8 m n p)). Qed.
Lemma lem7048349 {_127560 _127584 : Type'} (f : _127584 -> _127560) : term9 _127560 _127584 f.
Proof. exact (@lem6961680 _127560 _127584 f). Qed.
Lemma lem7048350 {_127560 _127584 : Type'} (f : _127584 -> _127560) : (term9 _127560 _127584 f) = (term10 _127560 _127584 f).
Proof. exact (eq_refl (term9 _127560 _127584 f)). Qed.
Lemma lem7048351 {_127560 _127584 : Type'} (f : _127584 -> _127560) : term10 _127560 _127584 f.
Proof. exact (EQ_MP (@lem7048350 _127560 _127584 f) (@lem7048349 _127560 _127584 f)). Qed.
Lemma lem7048352 {_127560 _127584 : Type'} (f : _127584 -> _127560) (g : _127560 -> nat) : term11 _127560 _127584 f g.
Proof. exact (@lem7048351 _127560 _127584 f g). Qed.
Lemma lem7048353 {_127560 _127584 : Type'} (g : _127560 -> nat) (f : _127584 -> _127560) : (term11 _127560 _127584 f g) = (term12 _127560 _127584 g f).
Proof. exact (eq_refl (term11 _127560 _127584 f g)). Qed.
Lemma lem7048354 {_127560 _127584 : Type'} (g : _127560 -> nat) (f : _127584 -> _127560) : term12 _127560 _127584 g f.
Proof. exact (EQ_MP (@lem7048353 _127560 _127584 g f) (@lem7048352 _127560 _127584 f g)). Qed.
Lemma lem7048355 {_127560 _127584 : Type'} (g : _127560 -> nat) (f : _127584 -> _127560) (s : _127584 -> Prop) : term13 _127560 _127584 g f s.
Proof. exact (@lem7048354 _127560 _127584 g f s). Qed.
Lemma lem7048356 {_127560 _127584 : Type'} (s : _127584 -> Prop) (g : _127560 -> nat) (f : _127584 -> _127560) : (term13 _127560 _127584 g f s) = (term14 _127560 _127584 s g f).
Proof. exact (eq_refl (term13 _127560 _127584 g f s)). Qed.
Lemma lem7048357 {_127560 _127584 : Type'} (s : _127584 -> Prop) (g : _127560 -> nat) (f : _127584 -> _127560) : term14 _127560 _127584 s g f.
Proof. exact (EQ_MP (@lem7048356 _127560 _127584 s g f) (@lem7048355 _127560 _127584 g f s)). Qed.
Lemma lem7048358 {_127560 _127584 : Type'} (s : _127584 -> Prop) (f : _127584 -> _127560) (h1 : term15 _127560 _127584 s f) : term15 _127560 _127584 s f.
Proof. exact (h1). Qed.
Lemma lem7048359 {_127560 _127584 : Type'} (g : _127560 -> nat) (s : _127584 -> Prop) (f : _127584 -> _127560) (h1 : term15 _127560 _127584 s f) : (term16 _127560 _127584 f s g) = (term17 _127560 _127584 s g f).
Proof. exact (@lem7048357 _127560 _127584 s g f (@lem7048358 _127560 _127584 s f h1)). Qed.
Lemma lem7048365 (m : nat) : term18 m.
Proof. exact (@lem5470571 m). Qed.
Lemma lem7048366 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem7048367 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem7048366 m) (@lem7048365 m)). Qed.
Lemma lem7048368 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem7048367 m n). Qed.
Lemma lem7048369 (m : nat) (n : nat) : (term20 m n) = (term21 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem7048370 (m : nat) (n : nat) : term21 m n.
Proof. exact (EQ_MP (@lem7048369 m n) (@lem7048368 m n)). Qed.
Lemma lem7048371 (m : nat) (n : nat) (p : nat) : term22 m n p.
Proof. exact (@lem7048370 m n p). Qed.
Lemma lem7048372 (p : nat) (m : nat) (n : nat) : (term22 m n p) = ((term23 m n p) = (term24 p m n)).
Proof. exact (eq_refl (term22 m n p)). Qed.
Lemma lem7048393 (p : nat) (m : nat) (n : nat) : (term23 m n p) = (term24 p m n).
Proof. exact (EQ_MP (@lem7048372 p m n) (@lem7048371 m n p)). Qed.
Lemma lem7048394 : (@nsum nat) = (@nsum nat).
Proof. exact (eq_refl (@nsum nat)). Qed.
Lemma lem7048395 (p : nat) (m : nat) (n : nat) : (term25 m n p) = (term26 p m n).
Proof. exact (MK_COMB (@lem7048394) (@lem7048393 p m n)). Qed.
Lemma lem7048396 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7048397 (p : nat) (m : nat) (n : nat) (f : nat -> nat) : (term27 m n p f) = (term28 p m n f).
Proof. exact (MK_COMB (@lem7048395 p m n) (@lem7048396 f)). Qed.
Lemma lem7048399 {_127560 _127584 : Type'} (s : _127584 -> Prop) (g : _127560 -> nat) (f : _127584 -> _127560) : term14 _127560 _127584 s g f.
Proof. exact (fun h0 : term15 _127560 _127584 s f => @lem7048359 _127560 _127584 g s f h0). Qed.
Lemma lem7048400 (s : nat -> Prop) (g : nat -> nat) (f : nat -> nat) : term29 s g f.
Proof. exact (@lem7048399 nat nat s g f). Qed.
Lemma lem7048401 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : term30 m n f p.
Proof. exact (@lem7048400 (dotdot m n) f (term31 p)). Qed.
Lemma lem7048413 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term32 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7048414 (p : Prop) (q : Prop) (p' : Prop) : term33 p q p'.
Proof. exact (fun q' : Prop => @lem7048413 p q p' q'). Qed.
Lemma lem7048415 (p : Prop) (q : Prop) : term34 p q.
Proof. exact (fun p' : Prop => @lem7048414 p q p'). Qed.
Lemma lem7048416 (m : nat) (n : nat) (p : nat) (x : nat) (y : nat) : term35 m n p x y.
Proof. exact (@lem7048415 (term36 m n x p y) (x = y)). Qed.
Lemma lem7048417 (m : nat) (n : nat) (p : nat) (x : nat) (y : nat) (p' : Prop) : term37 m n p x y p'.
Proof. exact (@lem7048416 m n p x y p'). Qed.
Lemma lem7048418 (m : nat) (n : nat) (p : nat) (x : nat) (y : nat) (p' : Prop) : (term37 m n p x y p') = (term38 m n p x y p').
Proof. exact (eq_refl (term37 m n p x y p')). Qed.
Lemma lem7048419 (m : nat) (n : nat) (p : nat) (x : nat) (y : nat) (p' : Prop) : term38 m n p x y p'.
Proof. exact (EQ_MP (@lem7048418 m n p x y p') (@lem7048417 m n p x y p')). Qed.
Lemma lem7048420 (m : nat) (n : nat) (p : nat) (x : nat) (y : nat) (p' : Prop) (q' : Prop) : term39 m n p x y p' q'.
Proof. exact (@lem7048419 m n p x y p' q'). Qed.
Lemma lem7048421 (m : nat) (n : nat) (p : nat) (x : nat) (y : nat) (p' : Prop) (q' : Prop) : (term39 m n p x y p' q') = (term40 m n p x y p' q').
Proof. exact (eq_refl (term39 m n p x y p' q')). Qed.
Lemma lem7048422 (m : nat) (n : nat) (p : nat) (x : nat) (y : nat) (p' : Prop) (q' : Prop) : term40 m n p x y p' q'.
Proof. exact (EQ_MP (@lem7048421 m n p x y p' q') (@lem7048420 m n p x y p' q')). Qed.
Lemma lem7048430 {A B : Type'} (f : A -> B) (y : A) : (term41 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7048431 (f : nat -> nat) (y : nat) : (term42 f y) = (f y).
Proof. exact (@lem7048430 nat nat f y). Qed.
Lemma lem7048432 (p : nat) (x : nat) : (term43 p x) = (term44 p x).
Proof. exact (@lem7048431 (term31 p) x). Qed.
Lemma lem7048433 (i : nat) (p : nat) : (term44 p i) = (Nat.add i p).
Proof. exact (eq_refl (term44 p i)). Qed.
Lemma lem7048434 (p : nat) : (term45 p) = (term31 p).
Proof. exact (fun_ext (fun i : nat => @lem7048433 i p)). Qed.
Lemma lem7048435 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7048436 (p : nat) (x : nat) : (term43 p x) = (term44 p x).
Proof. exact (MK_COMB (@lem7048434 p) (@lem7048435 x)). Qed.
Lemma lem7048437 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7048438 (p : nat) (x : nat) : (term46 p x) = (term47 p x).
Proof. exact (MK_COMB (@lem7048437) (@lem7048436 p x)). Qed.
Lemma lem7048439 (x : nat) (p : nat) : (term44 p x) = (Nat.add x p).
Proof. exact (eq_refl (term44 p x)). Qed.
Lemma lem7048440 (x : nat) (p : nat) : ((term43 p x) = (term44 p x)) = ((term44 p x) = (Nat.add x p)).
Proof. exact (MK_COMB (@lem7048438 p x) (@lem7048439 x p)). Qed.
Lemma lem7048441 (x : nat) (p : nat) : (term44 p x) = (Nat.add x p).
Proof. exact (EQ_MP (@lem7048440 x p) (@lem7048432 p x)). Qed.
Lemma lem7048442 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7048443 (x : nat) (p : nat) : (term47 p x) = (term48 x p).
Proof. exact (MK_COMB (@lem7048442) (@lem7048441 x p)). Qed.
Lemma lem7048445 {A B : Type'} (f : A -> B) (y : A) : (term41 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7048446 (f : nat -> nat) (y : nat) : (term42 f y) = (f y).
Proof. exact (@lem7048445 nat nat f y). Qed.
Lemma lem7048447 (p : nat) (y : nat) : (term43 p y) = (term44 p y).
Proof. exact (@lem7048446 (term31 p) y). Qed.
Lemma lem7048448 (i : nat) (p : nat) : (term44 p i) = (Nat.add i p).
Proof. exact (eq_refl (term44 p i)). Qed.
Lemma lem7048449 (p : nat) : (term45 p) = (term31 p).
Proof. exact (fun_ext (fun i : nat => @lem7048448 i p)). Qed.
Lemma lem7048450 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7048451 (p : nat) (y : nat) : (term43 p y) = (term44 p y).
Proof. exact (MK_COMB (@lem7048449 p) (@lem7048450 y)). Qed.
Lemma lem7048452 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7048453 (p : nat) (y : nat) : (term46 p y) = (term47 p y).
Proof. exact (MK_COMB (@lem7048452) (@lem7048451 p y)). Qed.
Lemma lem7048454 (y : nat) (p : nat) : (term44 p y) = (Nat.add y p).
Proof. exact (eq_refl (term44 p y)). Qed.
Lemma lem7048455 (y : nat) (p : nat) : ((term43 p y) = (term44 p y)) = ((term44 p y) = (Nat.add y p)).
Proof. exact (MK_COMB (@lem7048453 p y) (@lem7048454 y p)). Qed.
Lemma lem7048456 (y : nat) (p : nat) : (term44 p y) = (Nat.add y p).
Proof. exact (EQ_MP (@lem7048455 y p) (@lem7048447 p y)). Qed.
Lemma lem7048457 (x : nat) (y : nat) (p : nat) : ((term44 p x) = (term44 p y)) = ((Nat.add x p) = (Nat.add y p)).
Proof. exact (MK_COMB (@lem7048443 x p) (@lem7048456 y p)). Qed.
Lemma lem7048459 (p : nat) (m : nat) (n : nat) : ((Nat.add m p) = (Nat.add n p)) = (m = n).
Proof. exact (EQ_MP (@lem7048347 p m n) (@lem7048346 m n p)). Qed.
Lemma lem7048460 (p : nat) (x : nat) (y : nat) : ((Nat.add x p) = (Nat.add y p)) = (x = y).
Proof. exact (@lem7048459 p x y). Qed.
Lemma lem7048463 (p : nat) (x : nat) (y : nat) : ((term44 p x) = (term44 p y)) = (x = y).
Proof. exact (TRANS (@lem7048457 x y p) (@lem7048460 p x y)). Qed.
Lemma lem7048464 (y : nat) (m : nat) (n : nat) : (term49 y m n) = (term49 y m n).
Proof. exact (eq_refl (term49 y m n)). Qed.
Lemma lem7048465 (p : nat) (m : nat) (n : nat) (x : nat) (y : nat) : (term50 m n x p y) = (term51 m n x y).
Proof. exact (MK_COMB (@lem7048464 y m n) (@lem7048463 p x y)). Qed.
Lemma lem7048470 (x : nat) (m : nat) (n : nat) : (term49 x m n) = (term49 x m n).
Proof. exact (eq_refl (term49 x m n)). Qed.
Lemma lem7048471 (p : nat) (m : nat) (n : nat) (x : nat) (y : nat) : (term36 m n x p y) = (term52 m n x y).
Proof. exact (MK_COMB (@lem7048470 x m n) (@lem7048465 p m n x y)). Qed.
Lemma lem7048478 (p : nat) (m : nat) (n : nat) (x : nat) (y : nat) (q' : Prop) : term53 p m n x y q'.
Proof. exact (@lem7048422 m n p x y (term52 m n x y) q'). Qed.
Lemma lem7048479 (p : nat) (m : nat) (n : nat) (x : nat) (y : nat) (q' : Prop) : term54 p m n x y q'.
Proof. exact (@lem7048478 p m n x y q' (@lem7048471 p m n x y)). Qed.
Lemma lem7048480 (m : nat) (n : nat) (x : nat) (y : nat) (h1 : term52 m n x y) : term52 m n x y.
Proof. exact (h1). Qed.
Lemma lem7048481 (m : nat) (n : nat) (x : nat) (y : nat) (h1 : term52 m n x y) : term51 m n x y.
Proof. exact (proj2 (@lem7048480 m n x y h1)). Qed.
Lemma lem7048492 (m : nat) (n : nat) (x : nat) (y : nat) (h1 : term52 m n x y) : x = y.
Proof. exact (proj2 (@lem7048481 m n x y h1)). Qed.
Lemma lem7048493 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7048494 (m : nat) (n : nat) (x : nat) (y : nat) (h1 : term52 m n x y) : (@eq nat x) = (@eq nat y).
Proof. exact (MK_COMB (@lem7048493) (@lem7048492 m n x y h1)). Qed.
Lemma lem7048495 (y : nat) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7048496 (m : nat) (n : nat) (x : nat) (y : nat) (h1 : term52 m n x y) : (x = y) = (y = y).
Proof. exact (MK_COMB (@lem7048494 m n x y h1) (@lem7048495 y)). Qed.
Lemma lem7048498 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7048499 (x : nat) : (x = x) = True.
Proof. exact (@lem7048498 nat x). Qed.
Lemma lem7048500 (y : nat) : (y = y) = True.
Proof. exact (@lem7048499 y). Qed.
Lemma lem7048501 (m : nat) (n : nat) (x : nat) (y : nat) (h1 : term52 m n x y) : (x = y) = True.
Proof. exact (TRANS (@lem7048496 m n x y h1) (@lem7048500 y)). Qed.
Lemma lem7048502 (m : nat) (n : nat) (x : nat) (y : nat) : term55 m n x y.
Proof. exact (fun h0 : term52 m n x y => @lem7048501 m n x y h0). Qed.
Lemma lem7048503 (p : nat) (m : nat) (n : nat) (x : nat) (y : nat) : term56 p m n x y.
Proof. exact (@lem7048479 p m n x y True). Qed.
Lemma lem7048504 (p : nat) (m : nat) (n : nat) (x : nat) (y : nat) : (term57 m n p x y) = (term58 m n x y).
Proof. exact (@lem7048503 p m n x y (@lem7048502 m n x y)). Qed.
Lemma lem7048506 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7048507 (m : nat) (n : nat) (x : nat) (y : nat) : (term58 m n x y) = True.
Proof. exact (@lem7048506 (term52 m n x y)). Qed.
Lemma lem7048508 (m : nat) (n : nat) (p : nat) (x : nat) (y : nat) : (term57 m n p x y) = True.
Proof. exact (TRANS (@lem7048504 p m n x y) (@lem7048507 m n x y)). Qed.
Lemma lem7048509 (m : nat) (n : nat) (p : nat) (x : nat) : (term59 m n p x) = term60.
Proof. exact (fun_ext (fun y : nat => @lem7048508 m n p x y)). Qed.
Lemma lem7048510 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048511 (m : nat) (n : nat) (p : nat) (x : nat) : (term61 m n p x) = term62.
Proof. exact (MK_COMB (@lem7048510) (@lem7048509 m n p x)). Qed.
Lemma lem7048513 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7048514 (t : Prop) : (term64 t) = t.
Proof. exact (@lem7048513 nat t). Qed.
Lemma lem7048515 : term62 = True.
Proof. exact (@lem7048514 True). Qed.
Lemma lem7048516 (m : nat) (n : nat) (p : nat) (x : nat) : (term61 m n p x) = True.
Proof. exact (TRANS (@lem7048511 m n p x) (@lem7048515)). Qed.
Lemma lem7048517 (m : nat) (n : nat) (p : nat) : (term65 m n p) = term60.
Proof. exact (fun_ext (fun x : nat => @lem7048516 m n p x)). Qed.
Lemma lem7048518 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048519 (m : nat) (n : nat) (p : nat) : (term66 m n p) = term62.
Proof. exact (MK_COMB (@lem7048518) (@lem7048517 m n p)). Qed.
Lemma lem7048521 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7048522 (t : Prop) : (term64 t) = t.
Proof. exact (@lem7048521 nat t). Qed.
Lemma lem7048523 : term62 = True.
Proof. exact (@lem7048522 True). Qed.
Lemma lem7048524 (m : nat) (n : nat) (p : nat) : (term66 m n p) = True.
Proof. exact (TRANS (@lem7048519 m n p) (@lem7048523)). Qed.
Lemma lem7048525 (m : nat) (n : nat) (p : nat) : True = (term66 m n p).
Proof. exact (SYM (@lem7048524 m n p)). Qed.
Lemma lem7048526 (m : nat) (n : nat) (p : nat) : term66 m n p.
Proof. exact (EQ_MP (@lem7048525 m n p) (@lem0)). Qed.
Lemma lem7048527 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : (term28 p m n f) = (term67 m n f p).
Proof. exact (@lem7048401 m n f p (@lem7048526 m n p)). Qed.
Lemma lem7048528 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : (term27 m n p f) = (term67 m n f p).
Proof. exact (TRANS (@lem7048397 p m n f) (@lem7048527 m n f p)). Qed.
Lemma lem7048529 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7048530 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : (term68 m n p f) = (term69 m n f p).
Proof. exact (MK_COMB (@lem7048529) (@lem7048528 m n f p)). Qed.
Lemma lem7048531 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : (term70 m n f p) = (term70 m n f p).
Proof. exact (eq_refl (term70 m n f p)). Qed.
Lemma lem7048532 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : ((term27 m n p f) = (term70 m n f p)) = ((term67 m n f p) = (term70 m n f p)).
Proof. exact (MK_COMB (@lem7048530 m n f p) (@lem7048531 m n f p)). Qed.
Lemma lem7048535 (m : nat) (f : nat -> nat) (p : nat) : (term71 m f p) = (term72 m f p).
Proof. exact (fun_ext (fun n : nat => @lem7048532 m n f p)). Qed.
Lemma lem7048538 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048539 (m : nat) (f : nat -> nat) (p : nat) : (term73 m f p) = (term74 m f p).
Proof. exact (MK_COMB (@lem7048538) (@lem7048535 m f p)). Qed.
Lemma lem7048546 (f : nat -> nat) (p : nat) : (term75 f p) = (term76 f p).
Proof. exact (fun_ext (fun m : nat => @lem7048539 m f p)). Qed.
Lemma lem7048553 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048554 (f : nat -> nat) (p : nat) : (term77 f p) = (term78 f p).
Proof. exact (MK_COMB (@lem7048553) (@lem7048546 f p)). Qed.
Lemma lem7048565 (p : nat) : (term79 p) = (term80 p).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7048554 f p)). Qed.
Lemma lem7048576 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7048577 (p : nat) : (term81 p) = (term82 p).
Proof. exact (MK_COMB (@lem7048576) (@lem7048565 p)). Qed.
Lemma lem7048592 : term83 = term84.
Proof. exact (fun_ext (fun p : nat => @lem7048577 p)). Qed.
Lemma lem7048607 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048608 : term85 = term86.
Proof. exact (MK_COMB (@lem7048607) (@lem7048592)). Qed.
Lemma lem7048627 : term86 = term85.
Proof. exact (SYM (@lem7048608)). Qed.
Lemma lem7048647 {A B C : Type'} (f : B -> C) (g : A -> B) : (@o A B C f g) = (term3 A B C f g).
Proof. exact (EQ_MP (@lem7048330 A B C f g) (@lem7048329 A B C f g)). Qed.
Lemma lem7048648 (f : nat -> nat) (g : nat -> nat) : (@o nat nat nat f g) = (term87 f g).
Proof. exact (@lem7048647 nat nat nat f g). Qed.
Lemma lem7048649 (f : nat -> nat) (p : nat) : (term88 f p) = (term89 f p).
Proof. exact (@lem7048648 f (term31 p)). Qed.
Lemma lem7048651 {A B : Type'} (f : A -> B) (y : A) : (term41 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7048652 (f : nat -> nat) (y : nat) : (term42 f y) = (f y).
Proof. exact (@lem7048651 nat nat f y). Qed.
Lemma lem7048653 (p : nat) (x : nat) : (term43 p x) = (term44 p x).
Proof. exact (@lem7048652 (term31 p) x). Qed.
Lemma lem7048654 (i : nat) (p : nat) : (term44 p i) = (Nat.add i p).
Proof. exact (eq_refl (term44 p i)). Qed.
Lemma lem7048655 (p : nat) : (term45 p) = (term31 p).
Proof. exact (fun_ext (fun i : nat => @lem7048654 i p)). Qed.
Lemma lem7048656 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7048657 (p : nat) (x : nat) : (term43 p x) = (term44 p x).
Proof. exact (MK_COMB (@lem7048655 p) (@lem7048656 x)). Qed.
Lemma lem7048658 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7048659 (p : nat) (x : nat) : (term46 p x) = (term47 p x).
Proof. exact (MK_COMB (@lem7048658) (@lem7048657 p x)). Qed.
Lemma lem7048660 (x : nat) (p : nat) : (term44 p x) = (Nat.add x p).
Proof. exact (eq_refl (term44 p x)). Qed.
Lemma lem7048661 (x : nat) (p : nat) : ((term43 p x) = (term44 p x)) = ((term44 p x) = (Nat.add x p)).
Proof. exact (MK_COMB (@lem7048659 p x) (@lem7048660 x p)). Qed.
Lemma lem7048662 (x : nat) (p : nat) : (term44 p x) = (Nat.add x p).
Proof. exact (EQ_MP (@lem7048661 x p) (@lem7048653 p x)). Qed.
Lemma lem7048663 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7048664 (f : nat -> nat) (x : nat) (p : nat) : (term90 f p x) = (term91 f x p).
Proof. exact (MK_COMB (@lem7048663 f) (@lem7048662 x p)). Qed.
Lemma lem7048665 (f : nat -> nat) (p : nat) : (term89 f p) = (term92 f p).
Proof. exact (fun_ext (fun x : nat => @lem7048664 f x p)). Qed.
Lemma lem7048666 (f : nat -> nat) (p : nat) : (term88 f p) = (term92 f p).
Proof. exact (TRANS (@lem7048649 f p) (@lem7048665 f p)). Qed.
Lemma lem7048667 (m : nat) (n : nat) : (term93 m n) = (term93 m n).
Proof. exact (eq_refl (term93 m n)). Qed.
Lemma lem7048668 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : (term67 m n f p) = (term70 m n f p).
Proof. exact (MK_COMB (@lem7048667 m n) (@lem7048666 f p)). Qed.
Lemma lem7048669 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7048670 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : (term69 m n f p) = (term94 m n f p).
Proof. exact (MK_COMB (@lem7048669) (@lem7048668 m n f p)). Qed.
Lemma lem7048671 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : (term70 m n f p) = (term70 m n f p).
Proof. exact (eq_refl (term70 m n f p)). Qed.
Lemma lem7048672 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : ((term67 m n f p) = (term70 m n f p)) = ((term70 m n f p) = (term70 m n f p)).
Proof. exact (MK_COMB (@lem7048670 m n f p) (@lem7048671 m n f p)). Qed.
Lemma lem7048674 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7048675 (x : nat) : (x = x) = True.
Proof. exact (@lem7048674 nat x). Qed.
Lemma lem7048676 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : ((term70 m n f p) = (term70 m n f p)) = True.
Proof. exact (@lem7048675 (term70 m n f p)). Qed.
Lemma lem7048679 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : (term95 m n f p) = (term95 m n f p).
Proof. exact (eq_refl (term95 m n f p)). Qed.
Lemma lem7048680 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : (term95 m n f p) = (((term70 m n f p) = (term70 m n f p)) = True).
Proof. exact (eq_refl (term95 m n f p)). Qed.
Lemma lem7048681 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : (term96 m n f p) = (term96 m n f p).
Proof. exact (eq_refl (term96 m n f p)). Qed.
Lemma lem7048682 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : ((term95 m n f p) = (term95 m n f p)) = ((term95 m n f p) = (((term70 m n f p) = (term70 m n f p)) = True)).
Proof. exact (MK_COMB (@lem7048681 m n f p) (@lem7048680 m n f p)). Qed.
Lemma lem7048683 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : (term95 m n f p) = (((term70 m n f p) = (term70 m n f p)) = True).
Proof. exact (eq_refl (term95 m n f p)). Qed.
Lemma lem7048684 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7048685 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : (term96 m n f p) = (term97 m n f p).
Proof. exact (MK_COMB (@lem7048684) (@lem7048683 m n f p)). Qed.
Lemma lem7048686 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : (((term70 m n f p) = (term70 m n f p)) = True) = (((term70 m n f p) = (term70 m n f p)) = True).
Proof. exact (eq_refl (((term70 m n f p) = (term70 m n f p)) = True)). Qed.
Lemma lem7048687 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : ((term95 m n f p) = (((term70 m n f p) = (term70 m n f p)) = True)) = ((((term70 m n f p) = (term70 m n f p)) = True) = (((term70 m n f p) = (term70 m n f p)) = True)).
Proof. exact (MK_COMB (@lem7048685 m n f p) (@lem7048686 m n f p)). Qed.
Lemma lem7048688 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : ((term95 m n f p) = (term95 m n f p)) = ((((term70 m n f p) = (term70 m n f p)) = True) = (((term70 m n f p) = (term70 m n f p)) = True)).
Proof. exact (TRANS (@lem7048682 m n f p) (@lem7048687 m n f p)). Qed.
Lemma lem7048689 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : (((term70 m n f p) = (term70 m n f p)) = True) = (((term70 m n f p) = (term70 m n f p)) = True).
Proof. exact (EQ_MP (@lem7048688 m n f p) (@lem7048679 m n f p)). Qed.
Lemma lem7048690 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : ((term70 m n f p) = (term70 m n f p)) = True.
Proof. exact (EQ_MP (@lem7048689 m n f p) (@lem7048676 m n f p)). Qed.
Lemma lem7048691 (m : nat) (n : nat) (f : nat -> nat) (p : nat) : ((term67 m n f p) = (term70 m n f p)) = True.
Proof. exact (TRANS (@lem7048672 m n f p) (@lem7048690 m n f p)). Qed.
Lemma lem7048692 (m : nat) (f : nat -> nat) (p : nat) : (term72 m f p) = term60.
Proof. exact (fun_ext (fun n : nat => @lem7048691 m n f p)). Qed.
Lemma lem7048693 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048694 (m : nat) (f : nat -> nat) (p : nat) : (term74 m f p) = term62.
Proof. exact (MK_COMB (@lem7048693) (@lem7048692 m f p)). Qed.
Lemma lem7048696 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7048697 (t : Prop) : (term64 t) = t.
Proof. exact (@lem7048696 nat t). Qed.
Lemma lem7048698 : term62 = True.
Proof. exact (@lem7048697 True). Qed.
Lemma lem7048699 (m : nat) (f : nat -> nat) (p : nat) : (term74 m f p) = True.
Proof. exact (TRANS (@lem7048694 m f p) (@lem7048698)). Qed.
Lemma lem7048700 (f : nat -> nat) (p : nat) : (term76 f p) = term60.
Proof. exact (fun_ext (fun m : nat => @lem7048699 m f p)). Qed.
Lemma lem7048701 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048702 (f : nat -> nat) (p : nat) : (term78 f p) = term62.
Proof. exact (MK_COMB (@lem7048701) (@lem7048700 f p)). Qed.
Lemma lem7048704 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7048705 (t : Prop) : (term64 t) = t.
Proof. exact (@lem7048704 nat t). Qed.
Lemma lem7048706 : term62 = True.
Proof. exact (@lem7048705 True). Qed.
Lemma lem7048707 (f : nat -> nat) (p : nat) : (term78 f p) = True.
Proof. exact (TRANS (@lem7048702 f p) (@lem7048706)). Qed.
Lemma lem7048708 (p : nat) : (term80 p) = term98.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7048707 f p)). Qed.
Lemma lem7048709 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7048710 (p : nat) : (term82 p) = term99.
Proof. exact (MK_COMB (@lem7048709) (@lem7048708 p)). Qed.
Lemma lem7048712 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7048713 (t : Prop) : (term100 t) = t.
Proof. exact (@lem7048712 (nat -> nat) t). Qed.
Lemma lem7048714 : term99 = True.
Proof. exact (@lem7048713 True). Qed.
Lemma lem7048715 (p : nat) : (term82 p) = True.
Proof. exact (TRANS (@lem7048710 p) (@lem7048714)). Qed.
Lemma lem7048716 : term84 = term60.
Proof. exact (fun_ext (fun p : nat => @lem7048715 p)). Qed.
Lemma lem7048717 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7048718 : term86 = term62.
Proof. exact (MK_COMB (@lem7048717) (@lem7048716)). Qed.
Lemma lem7048720 {A : Type'} (t : Prop) : (term63 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7048721 (t : Prop) : (term64 t) = t.
Proof. exact (@lem7048720 nat t). Qed.
Lemma lem7048722 : term62 = True.
Proof. exact (@lem7048721 True). Qed.
Lemma lem7048723 : term86 = True.
Proof. exact (TRANS (@lem7048718) (@lem7048722)). Qed.
Lemma lem7048724 : True = term86.
Proof. exact (SYM (@lem7048723)). Qed.
Lemma lem7048725 : term86.
Proof. exact (EQ_MP (@lem7048724) (@lem0)). Qed.
Lemma lem7048726 : term85.
Proof. exact (EQ_MP (@lem7048627) (@lem7048725)). Qed.
