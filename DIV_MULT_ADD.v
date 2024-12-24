Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_MULT_ADD_term_abbrevs.
Require Import ADD_AC_spec.
Require Import ADD_ASSOC_spec.
Require Import BOOL_CASES_AX_spec.
Require Import DISJ_ACI_spec.
Require Import DIVISION_spec.
Require Import DIV_UNIQ_spec.
Require Import MULT_AC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Lemma lem207325 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem207326 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem207325 m n p h1)). Qed.
Lemma lem207327 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem207328 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem207327 m n p h1)). Qed.
Lemma lem207329 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem207326 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem207328 m n p h1)). Qed.
Lemma lem207330 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem207329 m n p)). Qed.
Lemma lem207331 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem207332 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem207331) (@lem207330 m n)). Qed.
Lemma lem207333 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem207332 m n)). Qed.
Lemma lem207334 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem207335 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem207334) (@lem207333 m)). Qed.
Lemma lem207336 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem207335 m)). Qed.
Lemma lem207337 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem207338 : term12 = term13.
Proof. exact (MK_COMB (@lem207337) (@lem207336)). Qed.
Lemma lem207339 : term13.
Proof. exact (EQ_MP (@lem207338) (@lem77960)). Qed.
Lemma lem207340 (m : nat) : term14 m.
Proof. exact (@lem207339 m). Qed.
Lemma lem207341 (m : nat) : (term14 m) = (term9 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem207342 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem207341 m) (@lem207340 m)). Qed.
Lemma lem207343 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem207342 m n). Qed.
Lemma lem207344 (m : nat) (n : nat) : (term15 m n) = (term5 m n).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem207345 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem207344 m n) (@lem207343 m n)). Qed.
Lemma lem207346 (m : nat) (n : nat) (p : nat) : term16 m n p.
Proof. exact (@lem207345 m n p). Qed.
Lemma lem207347 (m : nat) (n : nat) (p : nat) : (term16 m n p) = ((term1 m n p) = (term0 m n p)).
Proof. exact (eq_refl (term16 m n p)). Qed.
Lemma lem207349 (m : nat) : term17 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem207350 (m : nat) : (term17 m) = (term18 m).
Proof. exact (eq_refl (term17 m)). Qed.
Lemma lem207351 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem207350 m) (@lem207349 m)). Qed.
Lemma lem207352 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem207351 m n). Qed.
Lemma lem207353 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem207354 (m : nat) (n : nat) : term20 m n.
Proof. exact (EQ_MP (@lem207353 m n) (@lem207352 m n)). Qed.
Lemma lem207355 (m : nat) (n : nat) (p : nat) : term21 m n p.
Proof. exact (@lem207354 m n p). Qed.
Lemma lem207356 (m : nat) (n : nat) (p : nat) : (term21 m n p) = ((term22 m n p) = (term23 m n p)).
Proof. exact (eq_refl (term21 m n p)). Qed.
Lemma lem207358 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem207359 (m : nat) (h1 : term24) : term25 m.
Proof. exact (@lem207358 h1 m). Qed.
Lemma lem207360 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem207361 (m : nat) (h1 : term24) : term26 m.
Proof. exact (EQ_MP (@lem207360 m) (@lem207359 m h1)). Qed.
Lemma lem207362 (m : nat) (n : nat) (h1 : term24) : term27 m n.
Proof. exact (@lem207361 m h1 n). Qed.
Lemma lem207363 (m : nat) (n : nat) : (term27 m n) = (term28 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem207364 (m : nat) (n : nat) (h1 : term24) : term28 m n.
Proof. exact (EQ_MP (@lem207363 m n) (@lem207362 m n h1)). Qed.
Lemma lem207365 (m : nat) (n : nat) (q : nat) (h1 : term24) : term29 m n q.
Proof. exact (@lem207364 m n h1 q). Qed.
Lemma lem207366 (m : nat) (n : nat) (q : nat) : (term29 m n q) = (term30 m n q).
Proof. exact (eq_refl (term29 m n q)). Qed.
Lemma lem207367 (m : nat) (n : nat) (q : nat) (h1 : term24) : term30 m n q.
Proof. exact (EQ_MP (@lem207366 m n q) (@lem207365 m n q h1)). Qed.
Lemma lem207368 (m : nat) (n : nat) (q : nat) (r : nat) (h1 : term24) : term31 m n q r.
Proof. exact (@lem207367 m n q h1 r). Qed.
Lemma lem207369 (r : nat) (m : nat) (n : nat) (q : nat) : (term31 m n q r) = (term32 r m n q).
Proof. exact (eq_refl (term31 m n q r)). Qed.
Lemma lem207370 (r : nat) (m : nat) (n : nat) (q : nat) (h1 : term24) : term32 r m n q.
Proof. exact (EQ_MP (@lem207369 r m n q) (@lem207368 m n q r h1)). Qed.
Lemma lem207371 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term33 m q r n) : term33 m q r n.
Proof. exact (h1). Qed.
Lemma lem207372 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term24) (h2 : term33 m q r n) : (Nat.div m n) = q.
Proof. exact (@lem207370 r m n q h1 (@lem207371 m q r n h2)). Qed.
Lemma lem207373 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term33 m q r n) : term34 m n q.
Proof. exact (fun h0 : term24 => @lem207372 m q r n h0 h1). Qed.
Lemma lem207374 (m : nat) (q : nat) (n : nat) (h1 : term35 m q n) : term35 m q n.
Proof. exact (h1). Qed.
Lemma lem207375 (m : nat) (q : nat) (n : nat) (h1 : term35 m q n) : term34 m n q.
Proof. exact (ex_elim (@lem207374 m q n h1) (fun r : nat => fun h0 : term36 m q n r => @lem207373 m q r n h0)). Qed.
Lemma lem207376 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem207377 (m : nat) (q : nat) (n : nat) (h1 : term24) (h2 : term35 m q n) : (Nat.div m n) = q.
Proof. exact (@lem207375 m q n h2 (@lem207376 h1)). Qed.
Lemma lem207378 (m : nat) (n : nat) (q : nat) (h1 : term24) : term37 m n q.
Proof. exact (fun h0 : term35 m q n => @lem207377 m q n h1 h0). Qed.
Lemma lem207379 (m : nat) (n : nat) (h1 : term24) : term38 m n.
Proof. exact (fun q : nat => @lem207378 m n q h1). Qed.
Lemma lem207380 (m : nat) (h1 : term24) : term39 m.
Proof. exact (fun n : nat => @lem207379 m n h1). Qed.
Lemma lem207381 (h1 : term24) : term40.
Proof. exact (fun m : nat => @lem207380 m h1). Qed.
Lemma lem207382 : term41.
Proof. exact (fun h0 : term24 => @lem207381 h0). Qed.
Lemma lem207383 : term40.
Proof. exact (@lem207382 (@lem169759)). Qed.
Lemma lem207384 (m : nat) : term42 m.
Proof. exact (@lem207383 m). Qed.
Lemma lem207385 (m : nat) : (term42 m) = (term39 m).
Proof. exact (eq_refl (term42 m)). Qed.
Lemma lem207386 (m : nat) : term39 m.
Proof. exact (EQ_MP (@lem207385 m) (@lem207384 m)). Qed.
Lemma lem207387 (m : nat) (n : nat) : term43 m n.
Proof. exact (@lem207386 m n). Qed.
Lemma lem207388 (m : nat) (n : nat) : (term43 m n) = (term38 m n).
Proof. exact (eq_refl (term43 m n)). Qed.
Lemma lem207389 (m : nat) (n : nat) : term38 m n.
Proof. exact (EQ_MP (@lem207388 m n) (@lem207387 m n)). Qed.
Lemma lem207390 (m : nat) (n : nat) (q : nat) : term44 m n q.
Proof. exact (@lem207389 m n q). Qed.
Lemma lem207391 (m : nat) (n : nat) (q : nat) : (term44 m n q) = (term37 m n q).
Proof. exact (eq_refl (term44 m n q)). Qed.
Lemma lem207411 (p : Prop) : term45 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem207412 (p : Prop) : (term45 p) = (term46 p).
Proof. exact (eq_refl (term45 p)). Qed.
Lemma lem207413 (p : Prop) : term46 p.
Proof. exact (EQ_MP (@lem207412 p) (@lem207411 p)). Qed.
Lemma lem207414 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem207415 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem207426 (q : Prop) : (term47 q) = (term47 q).
Proof. exact (eq_refl (term47 q)). Qed.
Lemma lem207427 (q : Prop) (p : Prop) (h1 : p = True) : (term48 q p) = (term49 q).
Proof. exact (MK_COMB (@lem207426 q) (@lem207414 p h1)). Qed.
Lemma lem207428 (q : Prop) : (term49 q) = (term50 q).
Proof. exact (eq_refl (term49 q)). Qed.
Lemma lem207429 (q : Prop) (p : Prop) : (term51 q p) = (term51 q p).
Proof. exact (eq_refl (term51 q p)). Qed.
Lemma lem207430 (p : Prop) (q : Prop) : ((term48 q p) = (term49 q)) = ((term48 q p) = (term50 q)).
Proof. exact (MK_COMB (@lem207429 q p) (@lem207428 q)). Qed.
Lemma lem207431 (p : Prop) (q : Prop) : (term48 q p) = (term52 p q).
Proof. exact (eq_refl (term48 q p)). Qed.
Lemma lem207432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem207433 (p : Prop) (q : Prop) : (term51 q p) = (term53 p q).
Proof. exact (MK_COMB (@lem207432) (@lem207431 p q)). Qed.
Lemma lem207434 (q : Prop) : (term50 q) = (term50 q).
Proof. exact (eq_refl (term50 q)). Qed.
Lemma lem207435 (p : Prop) (q : Prop) : ((term48 q p) = (term50 q)) = ((term52 p q) = (term50 q)).
Proof. exact (MK_COMB (@lem207433 p q) (@lem207434 q)). Qed.
Lemma lem207436 (p : Prop) (q : Prop) : ((term48 q p) = (term49 q)) = ((term52 p q) = (term50 q)).
Proof. exact (TRANS (@lem207430 p q) (@lem207435 p q)). Qed.
Lemma lem207437 (q : Prop) (p : Prop) (h1 : p = True) : (term52 p q) = (term50 q).
Proof. exact (EQ_MP (@lem207436 p q) (@lem207427 q p h1)). Qed.
Lemma lem207438 (q : Prop) (p : Prop) (h1 : p = True) : (term50 q) = (term52 p q).
Proof. exact (SYM (@lem207437 q p h1)). Qed.
Lemma lem207439 (q : Prop) : (term47 q) = (term47 q).
Proof. exact (eq_refl (term47 q)). Qed.
Lemma lem207440 (q : Prop) (p : Prop) (h1 : p = False) : (term48 q p) = (term54 q).
Proof. exact (MK_COMB (@lem207439 q) (@lem207415 p h1)). Qed.
Lemma lem207441 (q : Prop) : (term54 q) = (term55 q).
Proof. exact (eq_refl (term54 q)). Qed.
Lemma lem207442 (q : Prop) (p : Prop) : (term51 q p) = (term51 q p).
Proof. exact (eq_refl (term51 q p)). Qed.
Lemma lem207443 (p : Prop) (q : Prop) : ((term48 q p) = (term54 q)) = ((term48 q p) = (term55 q)).
Proof. exact (MK_COMB (@lem207442 q p) (@lem207441 q)). Qed.
Lemma lem207444 (p : Prop) (q : Prop) : (term48 q p) = (term52 p q).
Proof. exact (eq_refl (term48 q p)). Qed.
Lemma lem207445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem207446 (p : Prop) (q : Prop) : (term51 q p) = (term53 p q).
Proof. exact (MK_COMB (@lem207445) (@lem207444 p q)). Qed.
Lemma lem207447 (q : Prop) : (term55 q) = (term55 q).
Proof. exact (eq_refl (term55 q)). Qed.
Lemma lem207448 (p : Prop) (q : Prop) : ((term48 q p) = (term55 q)) = ((term52 p q) = (term55 q)).
Proof. exact (MK_COMB (@lem207446 p q) (@lem207447 q)). Qed.
Lemma lem207449 (p : Prop) (q : Prop) : ((term48 q p) = (term54 q)) = ((term52 p q) = (term55 q)).
Proof. exact (TRANS (@lem207443 p q) (@lem207448 p q)). Qed.
Lemma lem207450 (q : Prop) (p : Prop) (h1 : p = False) : (term52 p q) = (term55 q).
Proof. exact (EQ_MP (@lem207449 p q) (@lem207440 q p h1)). Qed.
Lemma lem207451 (q : Prop) (p : Prop) (h1 : p = False) : (term55 q) = (term52 p q).
Proof. exact (SYM (@lem207450 q p h1)). Qed.
Lemma lem207455 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem207456 (q : Prop) : (term56 q) = (True -> q).
Proof. exact (@lem207455 (True -> q)). Qed.
Lemma lem207458 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem207459 (q : Prop) : (True -> q) = q.
Proof. exact (@lem207458 q). Qed.
Lemma lem207460 (q : Prop) : (term56 q) = q.
Proof. exact (TRANS (@lem207456 q) (@lem207459 q)). Qed.
Lemma lem207461 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem207462 (q : Prop) : (term57 q) = (imp q).
Proof. exact (MK_COMB (@lem207461) (@lem207460 q)). Qed.
Lemma lem207464 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem207465 (q : Prop) : (True /\ q) = q.
Proof. exact (@lem207464 q). Qed.
Lemma lem207466 (q : Prop) : (term50 q) = (q -> q).
Proof. exact (MK_COMB (@lem207462 q) (@lem207465 q)). Qed.
Lemma lem207468 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem207469 (q : Prop) : (q -> q) = True.
Proof. exact (@lem207468 q). Qed.
Lemma lem207470 (q : Prop) : (term50 q) = True.
Proof. exact (TRANS (@lem207466 q) (@lem207469 q)). Qed.
Lemma lem207471 (q : Prop) : True = (term50 q).
Proof. exact (SYM (@lem207470 q)). Qed.
Lemma lem207472 (q : Prop) : term50 q.
Proof. exact (EQ_MP (@lem207471 q) (@lem0)). Qed.
Lemma lem207476 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem207477 (q : Prop) : (term58 q) = False.
Proof. exact (@lem207476 (False -> q)). Qed.
Lemma lem207478 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem207479 (q : Prop) : (term59 q) = (imp False).
Proof. exact (MK_COMB (@lem207478) (@lem207477 q)). Qed.
Lemma lem207481 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem207482 (q : Prop) : (False /\ q) = False.
Proof. exact (@lem207481 q). Qed.
Lemma lem207483 (q : Prop) : (term55 q) = (False -> False).
Proof. exact (MK_COMB (@lem207479 q) (@lem207482 q)). Qed.
Lemma lem207485 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem207486 : (False -> False) = True.
Proof. exact (@lem207485 False). Qed.
Lemma lem207487 (q : Prop) : (term55 q) = True.
Proof. exact (TRANS (@lem207483 q) (@lem207486)). Qed.
Lemma lem207488 (q : Prop) : True = (term55 q).
Proof. exact (SYM (@lem207487 q)). Qed.
Lemma lem207489 (q : Prop) : term55 q.
Proof. exact (EQ_MP (@lem207488 q) (@lem0)). Qed.
Lemma lem207490 (q : Prop) (p : Prop) (h1 : p = False) : term52 p q.
Proof. exact (EQ_MP (@lem207451 q p h1) (@lem207489 q)). Qed.
Lemma lem207491 (q : Prop) (p : Prop) (h1 : p = True) : term52 p q.
Proof. exact (EQ_MP (@lem207438 q p h1) (@lem207472 q)). Qed.
Lemma lem207494 (p : Prop) (q : Prop) : term52 p q.
Proof. exact (or_elim (@lem207413 p) (fun h0 : p = True => @lem207491 q p h0) (fun h0 : p = False => @lem207490 q p h0)). Qed.
Lemma lem207495 (p : Prop) (q : Prop) (h1 : term52 p q) : term52 p q.
Proof. exact (h1). Qed.
Lemma lem207496 (q : Prop) (p : Prop) (h1 : term60 q p) : term60 q p.
Proof. exact (h1). Qed.
Lemma lem207497 (p : Prop) (q : Prop) (h1 : term60 q p) (h2 : term52 p q) : p /\ q.
Proof. exact (@lem207495 p q h2 (@lem207496 q p h1)). Qed.
Lemma lem207498 (q : Prop) (p : Prop) (h1 : term60 q p) : term61 p q.
Proof. exact (fun h0 : term52 p q => @lem207497 p q h1 h0). Qed.
Lemma lem207499 (p : Prop) (q : Prop) (h1 : term52 p q) : term52 p q.
Proof. exact (h1). Qed.
Lemma lem207500 (p : Prop) (q : Prop) (h1 : term60 q p) (h2 : term52 p q) : p /\ q.
Proof. exact (@lem207498 q p h1 (@lem207499 p q h2)). Qed.
Lemma lem207501 (p : Prop) (q : Prop) (h1 : term52 p q) : term52 p q.
Proof. exact (fun h0 : term60 q p => @lem207500 p q h0 h1). Qed.
Lemma lem207502 (p : Prop) (q : Prop) : term62 p q.
Proof. exact (fun h0 : term52 p q => @lem207501 p q h0). Qed.
Lemma lem207505 (p : Prop) (q : Prop) : term52 p q.
Proof. exact (@lem207502 p q (@lem207494 p q)). Qed.
Lemma lem207506 : term63.
Proof. exact (@lem207505 term64 term65). Qed.
Lemma lem207510 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term66 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem207511 (p : Prop) (q : Prop) (p' : Prop) : term67 p q p'.
Proof. exact (fun q' : Prop => @lem207510 p q p' q'). Qed.
Lemma lem207512 (p : Prop) (q : Prop) : term68 p q.
Proof. exact (fun p' : Prop => @lem207511 p q p'). Qed.
Lemma lem207513 : term69.
Proof. exact (@lem207512 term64 term65). Qed.
Lemma lem207514 (p' : Prop) : term70 p'.
Proof. exact (@lem207513 p'). Qed.
Lemma lem207515 (p' : Prop) : (term70 p') = (term71 p').
Proof. exact (eq_refl (term70 p')). Qed.
Lemma lem207516 (p' : Prop) : term71 p'.
Proof. exact (EQ_MP (@lem207515 p') (@lem207514 p')). Qed.
Lemma lem207517 (p' : Prop) (q' : Prop) : term72 p' q'.
Proof. exact (@lem207516 p' q'). Qed.
Lemma lem207518 (p' : Prop) (q' : Prop) : (term72 p' q') = (term73 p' q').
Proof. exact (eq_refl (term72 p' q')). Qed.
Lemma lem207519 (p' : Prop) (q' : Prop) : term73 p' q'.
Proof. exact (EQ_MP (@lem207518 p' q') (@lem207517 p' q')). Qed.
Lemma lem207535 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term66 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem207536 (p : Prop) (q : Prop) (p' : Prop) : term67 p q p'.
Proof. exact (fun q' : Prop => @lem207535 p q p' q'). Qed.
Lemma lem207537 (p : Prop) (q : Prop) : term68 p q.
Proof. exact (fun p' : Prop => @lem207536 p q p'). Qed.
Lemma lem207538 (a : nat) (b : nat) (n : nat) : term74 a b n.
Proof. exact (@lem207537 (term75 n) ((term76 a b n) = (term77 a b n))). Qed.
Lemma lem207539 (a : nat) (b : nat) (n : nat) (p' : Prop) : term78 a b n p'.
Proof. exact (@lem207538 a b n p'). Qed.
Lemma lem207540 (a : nat) (b : nat) (n : nat) (p' : Prop) : (term78 a b n p') = (term79 a b n p').
Proof. exact (eq_refl (term78 a b n p')). Qed.
Lemma lem207541 (a : nat) (b : nat) (n : nat) (p' : Prop) : term79 a b n p'.
Proof. exact (EQ_MP (@lem207540 a b n p') (@lem207539 a b n p')). Qed.
Lemma lem207542 (a : nat) (b : nat) (n : nat) (p' : Prop) (q' : Prop) : term80 a b n p' q'.
Proof. exact (@lem207541 a b n p' q'). Qed.
Lemma lem207543 (a : nat) (b : nat) (n : nat) (p' : Prop) (q' : Prop) : (term80 a b n p' q') = (term81 a b n p' q').
Proof. exact (eq_refl (term80 a b n p' q')). Qed.
Lemma lem207544 (a : nat) (b : nat) (n : nat) (p' : Prop) (q' : Prop) : term81 a b n p' q'.
Proof. exact (EQ_MP (@lem207543 a b n p' q') (@lem207542 a b n p' q')). Qed.
Lemma lem207547 (n : nat) : (term75 n) = (term75 n).
Proof. exact (eq_refl (term75 n)). Qed.
Lemma lem207548 (a : nat) (b : nat) (n : nat) (q' : Prop) : term82 a b n q'.
Proof. exact (@lem207544 a b n (term75 n) q'). Qed.
Lemma lem207549 (a : nat) (b : nat) (n : nat) (q' : Prop) : term83 a b n q'.
Proof. exact (@lem207548 a b n q' (@lem207547 n)). Qed.
Lemma lem207567 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem207568 (b : nat) (a : nat) (n : nat) : (term84 a n b) = (term85 b a n).
Proof. exact (@lem207567 b (Nat.mul a n)). Qed.
Lemma lem207575 : Nat.div = Nat.div.
Proof. exact (eq_refl Nat.div). Qed.
Lemma lem207576 (b : nat) (a : nat) (n : nat) : (term86 a n b) = (term87 b a n).
Proof. exact (MK_COMB (@lem207575) (@lem207568 b a n)). Qed.
Lemma lem207583 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem207584 (b : nat) (a : nat) (n : nat) : (term76 a b n) = (term88 b a n).
Proof. exact (MK_COMB (@lem207576 b a n) (@lem207583 n)). Qed.
Lemma lem207591 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem207592 (b : nat) (a : nat) (n : nat) : (term89 a b n) = (term90 b a n).
Proof. exact (MK_COMB (@lem207591) (@lem207584 b a n)). Qed.
Lemma lem207602 (a : nat) (b : nat) (n : nat) : (term77 a b n) = (term77 a b n).
Proof. exact (eq_refl (term77 a b n)). Qed.
Lemma lem207603 (a : nat) (b : nat) (n : nat) : ((term76 a b n) = (term77 a b n)) = ((term88 b a n) = (term77 a b n)).
Proof. exact (MK_COMB (@lem207592 b a n) (@lem207602 a b n)). Qed.
Lemma lem207615 (a : nat) (b : nat) (n : nat) : term91 a b n.
Proof. exact (fun h0 : term75 n => @lem207603 a b n). Qed.
Lemma lem207616 (a : nat) (b : nat) (n : nat) : term92 a b n.
Proof. exact (@lem207549 a b n ((term88 b a n) = (term77 a b n))). Qed.
Lemma lem207617 (a : nat) (b : nat) (n : nat) : (term93 a b n) = (term94 a b n).
Proof. exact (@lem207616 a b n (@lem207615 a b n)). Qed.
Lemma lem207678 (a : nat) (b : nat) : (term95 a b) = (term96 a b).
Proof. exact (fun_ext (fun n : nat => @lem207617 a b n)). Qed.
Lemma lem207739 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem207740 (a : nat) (b : nat) : (term97 a b) = (term98 a b).
Proof. exact (MK_COMB (@lem207739) (@lem207678 a b)). Qed.
Lemma lem207805 (a : nat) : (term99 a) = (term100 a).
Proof. exact (fun_ext (fun b : nat => @lem207740 a b)). Qed.
Lemma lem207870 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem207871 (a : nat) : (term101 a) = (term102 a).
Proof. exact (MK_COMB (@lem207870) (@lem207805 a)). Qed.
Lemma lem207940 : term103 = term104.
Proof. exact (fun_ext (fun a : nat => @lem207871 a)). Qed.
Lemma lem208009 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208010 : term64 = term105.
Proof. exact (MK_COMB (@lem208009) (@lem207940)). Qed.
Lemma lem208083 (q' : Prop) : term106 q'.
Proof. exact (@lem207519 term105 q'). Qed.
Lemma lem208084 (q' : Prop) : term107 q'.
Proof. exact (@lem208083 q' (@lem208010)). Qed.
Lemma lem208085 (h1 : term105) : term105.
Proof. exact (h1). Qed.
Lemma lem208086 (a : nat) (h1 : term105) : term108 a.
Proof. exact (@lem208085 h1 a). Qed.
Lemma lem208087 (a : nat) : (term108 a) = (term102 a).
Proof. exact (eq_refl (term108 a)). Qed.
Lemma lem208088 (a : nat) (h1 : term105) : term102 a.
Proof. exact (EQ_MP (@lem208087 a) (@lem208086 a h1)). Qed.
Lemma lem208089 (a : nat) (b : nat) (h1 : term105) : term109 a b.
Proof. exact (@lem208088 a h1 b). Qed.
Lemma lem208090 (a : nat) (b : nat) : (term109 a b) = (term98 a b).
Proof. exact (eq_refl (term109 a b)). Qed.
Lemma lem208091 (a : nat) (b : nat) (h1 : term105) : term98 a b.
Proof. exact (EQ_MP (@lem208090 a b) (@lem208089 a b h1)). Qed.
Lemma lem208092 (a : nat) (b : nat) (n : nat) (h1 : term105) : term110 a b n.
Proof. exact (@lem208091 a b h1 n). Qed.
Lemma lem208093 (a : nat) (b : nat) (n : nat) : (term110 a b n) = (term94 a b n).
Proof. exact (eq_refl (term110 a b n)). Qed.
Lemma lem208094 (a : nat) (b : nat) (n : nat) (h1 : term105) : term94 a b n.
Proof. exact (EQ_MP (@lem208093 a b n) (@lem208092 a b n h1)). Qed.
Lemma lem208095 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (h1). Qed.
Lemma lem208096 (a : nat) (b : nat) (n : nat) (h1 : term105) (h2 : term75 n) : (term88 b a n) = (term77 a b n).
Proof. exact (@lem208094 a b n h1 (@lem208095 n h2)). Qed.
Lemma lem208119 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term66 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem208120 (p : Prop) (q : Prop) (p' : Prop) : term67 p q p'.
Proof. exact (fun q' : Prop => @lem208119 p q p' q'). Qed.
Lemma lem208121 (p : Prop) (q : Prop) : term68 p q.
Proof. exact (fun p' : Prop => @lem208120 p q p'). Qed.
Lemma lem208122 (a : nat) (b : nat) (n : nat) : term111 a b n.
Proof. exact (@lem208121 (term75 n) ((term112 a b n) = (term77 a b n))). Qed.
Lemma lem208123 (a : nat) (b : nat) (n : nat) (p' : Prop) : term113 a b n p'.
Proof. exact (@lem208122 a b n p'). Qed.
Lemma lem208124 (a : nat) (b : nat) (n : nat) (p' : Prop) : (term113 a b n p') = (term114 a b n p').
Proof. exact (eq_refl (term113 a b n p')). Qed.
Lemma lem208125 (a : nat) (b : nat) (n : nat) (p' : Prop) : term114 a b n p'.
Proof. exact (EQ_MP (@lem208124 a b n p') (@lem208123 a b n p')). Qed.
Lemma lem208126 (a : nat) (b : nat) (n : nat) (p' : Prop) (q' : Prop) : term115 a b n p' q'.
Proof. exact (@lem208125 a b n p' q'). Qed.
Lemma lem208127 (a : nat) (b : nat) (n : nat) (p' : Prop) (q' : Prop) : (term115 a b n p' q') = (term116 a b n p' q').
Proof. exact (eq_refl (term115 a b n p' q')). Qed.
Lemma lem208128 (a : nat) (b : nat) (n : nat) (p' : Prop) (q' : Prop) : term116 a b n p' q'.
Proof. exact (EQ_MP (@lem208127 a b n p' q') (@lem208126 a b n p' q')). Qed.
Lemma lem208131 (n : nat) : (term75 n) = (term75 n).
Proof. exact (eq_refl (term75 n)). Qed.
Lemma lem208132 (a : nat) (b : nat) (n : nat) (q' : Prop) : term117 a b n q'.
Proof. exact (@lem208128 a b n (term75 n) q'). Qed.
Lemma lem208133 (a : nat) (b : nat) (n : nat) (q' : Prop) : term118 a b n q'.
Proof. exact (@lem208132 a b n q' (@lem208131 n)). Qed.
Lemma lem208134 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (h1). Qed.
Lemma lem208135 (n : nat) : term119 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem208151 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem208152 (b : nat) (n : nat) (a : nat) : (term84 n a b) = (term85 b n a).
Proof. exact (@lem208151 b (Nat.mul n a)). Qed.
Lemma lem208157 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem208158 (a : nat) (n : nat) : (Nat.mul n a) = (Nat.mul a n).
Proof. exact (@lem208157 a n). Qed.
Lemma lem208162 (b : nat) : (Nat.add b) = (Nat.add b).
Proof. exact (eq_refl (Nat.add b)). Qed.
Lemma lem208163 (b : nat) (a : nat) (n : nat) : (term85 b n a) = (term85 b a n).
Proof. exact (MK_COMB (@lem208162 b) (@lem208158 a n)). Qed.
Lemma lem208170 (b : nat) (a : nat) (n : nat) : (term84 n a b) = (term85 b a n).
Proof. exact (TRANS (@lem208152 b n a) (@lem208163 b a n)). Qed.
Lemma lem208171 : Nat.div = Nat.div.
Proof. exact (eq_refl Nat.div). Qed.
Lemma lem208172 (b : nat) (a : nat) (n : nat) : (term86 n a b) = (term87 b a n).
Proof. exact (MK_COMB (@lem208171) (@lem208170 b a n)). Qed.
Lemma lem208179 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem208180 (b : nat) (a : nat) (n : nat) : (term112 a b n) = (term88 b a n).
Proof. exact (MK_COMB (@lem208172 b a n) (@lem208179 n)). Qed.
Lemma lem208182 (a : nat) (b : nat) (n : nat) (h1 : term105) : term94 a b n.
Proof. exact (fun h0 : term75 n => @lem208096 a b n h1 h0). Qed.
Lemma lem208184 (n : nat) (h1 : term75 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem208135 n (@lem208134 n h1)). Qed.
Lemma lem208185 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem208186 (n : nat) (h1 : term75 n) : (term75 n) = (~ False).
Proof. exact (MK_COMB (@lem208185) (@lem208184 n h1)). Qed.
Lemma lem208188 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem208189 (n : nat) (h1 : term75 n) : (term75 n) = True.
Proof. exact (TRANS (@lem208186 n h1) (@lem208188)). Qed.
Lemma lem208190 (n : nat) (h1 : term75 n) : True = (term75 n).
Proof. exact (SYM (@lem208189 n h1)). Qed.
Lemma lem208191 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (EQ_MP (@lem208190 n h1) (@lem0)). Qed.
Lemma lem208192 (a : nat) (b : nat) (n : nat) (h1 : term105) (h2 : term75 n) : (term88 b a n) = (term77 a b n).
Proof. exact (@lem208182 a b n h1 (@lem208191 n h2)). Qed.
Lemma lem208196 (a : nat) (b : nat) (n : nat) (h1 : term105) (h2 : term75 n) : (term112 a b n) = (term77 a b n).
Proof. exact (TRANS (@lem208180 b a n) (@lem208192 a b n h1 h2)). Qed.
Lemma lem208197 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem208198 (a : nat) (b : nat) (n : nat) (h1 : term105) (h2 : term75 n) : (term120 a b n) = (term121 a b n).
Proof. exact (MK_COMB (@lem208197) (@lem208196 a b n h1 h2)). Qed.
Lemma lem208205 (a : nat) (b : nat) (n : nat) : (term77 a b n) = (term77 a b n).
Proof. exact (eq_refl (term77 a b n)). Qed.
Lemma lem208206 (a : nat) (b : nat) (n : nat) (h1 : term105) (h2 : term75 n) : ((term112 a b n) = (term77 a b n)) = ((term77 a b n) = (term77 a b n)).
Proof. exact (MK_COMB (@lem208198 a b n h1 h2) (@lem208205 a b n)). Qed.
Lemma lem208208 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem208209 (x : nat) : (x = x) = True.
Proof. exact (@lem208208 nat x). Qed.
Lemma lem208210 (a : nat) (b : nat) (n : nat) : ((term77 a b n) = (term77 a b n)) = True.
Proof. exact (@lem208209 (term77 a b n)). Qed.
Lemma lem208211 (a : nat) (b : nat) (n : nat) (h1 : term105) (h2 : term75 n) : ((term112 a b n) = (term77 a b n)) = True.
Proof. exact (TRANS (@lem208206 a b n h1 h2) (@lem208210 a b n)). Qed.
Lemma lem208212 (a : nat) (b : nat) (n : nat) (h1 : term105) : term122 a b n.
Proof. exact (fun h0 : term75 n => @lem208211 a b n h1 h0). Qed.
Lemma lem208213 (a : nat) (b : nat) (n : nat) : term123 a b n.
Proof. exact (@lem208133 a b n True). Qed.
Lemma lem208214 (a : nat) (b : nat) (n : nat) (h1 : term105) : (term124 a b n) = (term125 n).
Proof. exact (@lem208213 a b n (@lem208212 a b n h1)). Qed.
Lemma lem208216 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem208217 (n : nat) : (term125 n) = True.
Proof. exact (@lem208216 (term75 n)). Qed.
Lemma lem208218 (a : nat) (b : nat) (n : nat) (h1 : term105) : (term124 a b n) = True.
Proof. exact (TRANS (@lem208214 a b n h1) (@lem208217 n)). Qed.
Lemma lem208219 (a : nat) (b : nat) (h1 : term105) : (term126 a b) = term127.
Proof. exact (fun_ext (fun n : nat => @lem208218 a b n h1)). Qed.
Lemma lem208220 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208221 (a : nat) (b : nat) (h1 : term105) : (term128 a b) = term129.
Proof. exact (MK_COMB (@lem208220) (@lem208219 a b h1)). Qed.
Lemma lem208223 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem208224 (t : Prop) : (term131 t) = t.
Proof. exact (@lem208223 nat t). Qed.
Lemma lem208225 : term129 = True.
Proof. exact (@lem208224 True). Qed.
Lemma lem208226 (a : nat) (b : nat) (h1 : term105) : (term128 a b) = True.
Proof. exact (TRANS (@lem208221 a b h1) (@lem208225)). Qed.
Lemma lem208227 (a : nat) (h1 : term105) : (term132 a) = term127.
Proof. exact (fun_ext (fun b : nat => @lem208226 a b h1)). Qed.
Lemma lem208228 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208229 (a : nat) (h1 : term105) : (term133 a) = term129.
Proof. exact (MK_COMB (@lem208228) (@lem208227 a h1)). Qed.
Lemma lem208231 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem208232 (t : Prop) : (term131 t) = t.
Proof. exact (@lem208231 nat t). Qed.
Lemma lem208233 : term129 = True.
Proof. exact (@lem208232 True). Qed.
Lemma lem208234 (a : nat) (h1 : term105) : (term133 a) = True.
Proof. exact (TRANS (@lem208229 a h1) (@lem208233)). Qed.
Lemma lem208235 (h1 : term105) : term134 = term127.
Proof. exact (fun_ext (fun a : nat => @lem208234 a h1)). Qed.
Lemma lem208236 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208237 (h1 : term105) : term135 = term129.
Proof. exact (MK_COMB (@lem208236) (@lem208235 h1)). Qed.
Lemma lem208239 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem208240 (t : Prop) : (term131 t) = t.
Proof. exact (@lem208239 nat t). Qed.
Lemma lem208241 : term129 = True.
Proof. exact (@lem208240 True). Qed.
Lemma lem208242 (h1 : term105) : term135 = True.
Proof. exact (TRANS (@lem208237 h1) (@lem208241)). Qed.
Lemma lem208243 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem208244 (h1 : term105) : term136 = (and True).
Proof. exact (MK_COMB (@lem208243) (@lem208242 h1)). Qed.
Lemma lem208262 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term66 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem208263 (p : Prop) (q : Prop) (p' : Prop) : term67 p q p'.
Proof. exact (fun q' : Prop => @lem208262 p q p' q'). Qed.
Lemma lem208264 (p : Prop) (q : Prop) : term68 p q.
Proof. exact (fun p' : Prop => @lem208263 p q p'). Qed.
Lemma lem208265 (b : nat) (n : nat) (a : nat) : term137 b n a.
Proof. exact (@lem208264 (term75 n) ((term88 b a n) = (term138 b n a))). Qed.
Lemma lem208266 (b : nat) (n : nat) (a : nat) (p' : Prop) : term139 b n a p'.
Proof. exact (@lem208265 b n a p'). Qed.
Lemma lem208267 (b : nat) (n : nat) (a : nat) (p' : Prop) : (term139 b n a p') = (term140 b n a p').
Proof. exact (eq_refl (term139 b n a p')). Qed.
Lemma lem208268 (b : nat) (n : nat) (a : nat) (p' : Prop) : term140 b n a p'.
Proof. exact (EQ_MP (@lem208267 b n a p') (@lem208266 b n a p')). Qed.
Lemma lem208269 (b : nat) (n : nat) (a : nat) (p' : Prop) (q' : Prop) : term141 b n a p' q'.
Proof. exact (@lem208268 b n a p' q'). Qed.
Lemma lem208270 (b : nat) (n : nat) (a : nat) (p' : Prop) (q' : Prop) : (term141 b n a p' q') = (term142 b n a p' q').
Proof. exact (eq_refl (term141 b n a p' q')). Qed.
Lemma lem208271 (b : nat) (n : nat) (a : nat) (p' : Prop) (q' : Prop) : term142 b n a p' q'.
Proof. exact (EQ_MP (@lem208270 b n a p' q') (@lem208269 b n a p' q')). Qed.
Lemma lem208274 (n : nat) : (term75 n) = (term75 n).
Proof. exact (eq_refl (term75 n)). Qed.
Lemma lem208275 (b : nat) (a : nat) (n : nat) (q' : Prop) : term143 b a n q'.
Proof. exact (@lem208271 b n a (term75 n) q'). Qed.
Lemma lem208276 (b : nat) (a : nat) (n : nat) (q' : Prop) : term144 b a n q'.
Proof. exact (@lem208275 b a n q' (@lem208274 n)). Qed.
Lemma lem208277 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (h1). Qed.
Lemma lem208278 (n : nat) : term119 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem208294 (a : nat) (b : nat) (n : nat) (h1 : term105) : term94 a b n.
Proof. exact (fun h0 : term75 n => @lem208096 a b n h1 h0). Qed.
Lemma lem208296 (n : nat) (h1 : term75 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem208278 n (@lem208277 n h1)). Qed.
Lemma lem208297 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem208298 (n : nat) (h1 : term75 n) : (term75 n) = (~ False).
Proof. exact (MK_COMB (@lem208297) (@lem208296 n h1)). Qed.
Lemma lem208300 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem208301 (n : nat) (h1 : term75 n) : (term75 n) = True.
Proof. exact (TRANS (@lem208298 n h1) (@lem208300)). Qed.
Lemma lem208302 (n : nat) (h1 : term75 n) : True = (term75 n).
Proof. exact (SYM (@lem208301 n h1)). Qed.
Lemma lem208303 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (EQ_MP (@lem208302 n h1) (@lem0)). Qed.
Lemma lem208304 (a : nat) (b : nat) (n : nat) (h1 : term105) (h2 : term75 n) : (term88 b a n) = (term77 a b n).
Proof. exact (@lem208294 a b n h1 (@lem208303 n h2)). Qed.
Lemma lem208308 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem208309 (a : nat) (b : nat) (n : nat) (h1 : term105) (h2 : term75 n) : (term90 b a n) = (term121 a b n).
Proof. exact (MK_COMB (@lem208308) (@lem208304 a b n h1 h2)). Qed.
Lemma lem208314 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem208315 (a : nat) (b : nat) (n : nat) : (term138 b n a) = (term77 a b n).
Proof. exact (@lem208314 a (Nat.div b n)). Qed.
Lemma lem208319 (a : nat) (b : nat) (n : nat) (h1 : term105) (h2 : term75 n) : ((term88 b a n) = (term138 b n a)) = ((term77 a b n) = (term77 a b n)).
Proof. exact (MK_COMB (@lem208309 a b n h1 h2) (@lem208315 a b n)). Qed.
Lemma lem208321 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem208322 (x : nat) : (x = x) = True.
Proof. exact (@lem208321 nat x). Qed.
Lemma lem208323 (a : nat) (b : nat) (n : nat) : ((term77 a b n) = (term77 a b n)) = True.
Proof. exact (@lem208322 (term77 a b n)). Qed.
Lemma lem208324 (b : nat) (a : nat) (n : nat) (h1 : term105) (h2 : term75 n) : ((term88 b a n) = (term138 b n a)) = True.
Proof. exact (TRANS (@lem208319 a b n h1 h2) (@lem208323 a b n)). Qed.
Lemma lem208325 (b : nat) (n : nat) (a : nat) (h1 : term105) : term145 b n a.
Proof. exact (fun h0 : term75 n => @lem208324 b a n h1 h0). Qed.
Lemma lem208326 (b : nat) (a : nat) (n : nat) : term146 b a n.
Proof. exact (@lem208276 b a n True). Qed.
Lemma lem208327 (b : nat) (a : nat) (n : nat) (h1 : term105) : (term147 b n a) = (term125 n).
Proof. exact (@lem208326 b a n (@lem208325 b n a h1)). Qed.
Lemma lem208329 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem208330 (n : nat) : (term125 n) = True.
Proof. exact (@lem208329 (term75 n)). Qed.
Lemma lem208331 (b : nat) (n : nat) (a : nat) (h1 : term105) : (term147 b n a) = True.
Proof. exact (TRANS (@lem208327 b a n h1) (@lem208330 n)). Qed.
Lemma lem208332 (b : nat) (a : nat) (h1 : term105) : (term148 b a) = term127.
Proof. exact (fun_ext (fun n : nat => @lem208331 b n a h1)). Qed.
Lemma lem208333 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208334 (b : nat) (a : nat) (h1 : term105) : (term149 b a) = term129.
Proof. exact (MK_COMB (@lem208333) (@lem208332 b a h1)). Qed.
Lemma lem208336 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem208337 (t : Prop) : (term131 t) = t.
Proof. exact (@lem208336 nat t). Qed.
Lemma lem208338 : term129 = True.
Proof. exact (@lem208337 True). Qed.
Lemma lem208339 (b : nat) (a : nat) (h1 : term105) : (term149 b a) = True.
Proof. exact (TRANS (@lem208334 b a h1) (@lem208338)). Qed.
Lemma lem208340 (a : nat) (h1 : term105) : (term150 a) = term127.
Proof. exact (fun_ext (fun b : nat => @lem208339 b a h1)). Qed.
Lemma lem208341 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208342 (a : nat) (h1 : term105) : (term151 a) = term129.
Proof. exact (MK_COMB (@lem208341) (@lem208340 a h1)). Qed.
Lemma lem208344 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem208345 (t : Prop) : (term131 t) = t.
Proof. exact (@lem208344 nat t). Qed.
Lemma lem208346 : term129 = True.
Proof. exact (@lem208345 True). Qed.
Lemma lem208347 (a : nat) (h1 : term105) : (term151 a) = True.
Proof. exact (TRANS (@lem208342 a h1) (@lem208346)). Qed.
Lemma lem208348 (h1 : term105) : term152 = term127.
Proof. exact (fun_ext (fun a : nat => @lem208347 a h1)). Qed.
Lemma lem208349 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208350 (h1 : term105) : term153 = term129.
Proof. exact (MK_COMB (@lem208349) (@lem208348 h1)). Qed.
Lemma lem208352 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem208353 (t : Prop) : (term131 t) = t.
Proof. exact (@lem208352 nat t). Qed.
Lemma lem208354 : term129 = True.
Proof. exact (@lem208353 True). Qed.
Lemma lem208355 (h1 : term105) : term153 = True.
Proof. exact (TRANS (@lem208350 h1) (@lem208354)). Qed.
Lemma lem208356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem208357 (h1 : term105) : term154 = (and True).
Proof. exact (MK_COMB (@lem208356) (@lem208355 h1)). Qed.
Lemma lem208373 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term66 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem208374 (p : Prop) (q : Prop) (p' : Prop) : term67 p q p'.
Proof. exact (fun q' : Prop => @lem208373 p q p' q'). Qed.
Lemma lem208375 (p : Prop) (q : Prop) : term68 p q.
Proof. exact (fun p' : Prop => @lem208374 p q p'). Qed.
Lemma lem208376 (b : nat) (n : nat) (a : nat) : term155 b n a.
Proof. exact (@lem208375 (term75 n) ((term156 b a n) = (term138 b n a))). Qed.
Lemma lem208377 (b : nat) (n : nat) (a : nat) (p' : Prop) : term157 b n a p'.
Proof. exact (@lem208376 b n a p'). Qed.
Lemma lem208378 (b : nat) (n : nat) (a : nat) (p' : Prop) : (term157 b n a p') = (term158 b n a p').
Proof. exact (eq_refl (term157 b n a p')). Qed.
Lemma lem208379 (b : nat) (n : nat) (a : nat) (p' : Prop) : term158 b n a p'.
Proof. exact (EQ_MP (@lem208378 b n a p') (@lem208377 b n a p')). Qed.
Lemma lem208380 (b : nat) (n : nat) (a : nat) (p' : Prop) (q' : Prop) : term159 b n a p' q'.
Proof. exact (@lem208379 b n a p' q'). Qed.
Lemma lem208381 (b : nat) (n : nat) (a : nat) (p' : Prop) (q' : Prop) : (term159 b n a p' q') = (term160 b n a p' q').
Proof. exact (eq_refl (term159 b n a p' q')). Qed.
Lemma lem208382 (b : nat) (n : nat) (a : nat) (p' : Prop) (q' : Prop) : term160 b n a p' q'.
Proof. exact (EQ_MP (@lem208381 b n a p' q') (@lem208380 b n a p' q')). Qed.
Lemma lem208385 (n : nat) : (term75 n) = (term75 n).
Proof. exact (eq_refl (term75 n)). Qed.
Lemma lem208386 (b : nat) (a : nat) (n : nat) (q' : Prop) : term161 b a n q'.
Proof. exact (@lem208382 b n a (term75 n) q'). Qed.
Lemma lem208387 (b : nat) (a : nat) (n : nat) (q' : Prop) : term162 b a n q'.
Proof. exact (@lem208386 b a n q' (@lem208385 n)). Qed.
Lemma lem208388 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (h1). Qed.
Lemma lem208389 (n : nat) : term119 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem208410 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (proj1 (@lem83517 n m (@el nat))). Qed.
Lemma lem208411 (a : nat) (n : nat) : (Nat.mul n a) = (Nat.mul a n).
Proof. exact (@lem208410 a n). Qed.
Lemma lem208415 (b : nat) : (Nat.add b) = (Nat.add b).
Proof. exact (eq_refl (Nat.add b)). Qed.
Lemma lem208416 (b : nat) (a : nat) (n : nat) : (term85 b n a) = (term85 b a n).
Proof. exact (MK_COMB (@lem208415 b) (@lem208411 a n)). Qed.
Lemma lem208423 : Nat.div = Nat.div.
Proof. exact (eq_refl Nat.div). Qed.
Lemma lem208424 (b : nat) (a : nat) (n : nat) : (term87 b n a) = (term87 b a n).
Proof. exact (MK_COMB (@lem208423) (@lem208416 b a n)). Qed.
Lemma lem208431 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem208432 (b : nat) (a : nat) (n : nat) : (term156 b a n) = (term88 b a n).
Proof. exact (MK_COMB (@lem208424 b a n) (@lem208431 n)). Qed.
Lemma lem208434 (a : nat) (b : nat) (n : nat) (h1 : term105) : term94 a b n.
Proof. exact (fun h0 : term75 n => @lem208096 a b n h1 h0). Qed.
Lemma lem208436 (n : nat) (h1 : term75 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem208389 n (@lem208388 n h1)). Qed.
Lemma lem208437 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem208438 (n : nat) (h1 : term75 n) : (term75 n) = (~ False).
Proof. exact (MK_COMB (@lem208437) (@lem208436 n h1)). Qed.
Lemma lem208440 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem208441 (n : nat) (h1 : term75 n) : (term75 n) = True.
Proof. exact (TRANS (@lem208438 n h1) (@lem208440)). Qed.
Lemma lem208442 (n : nat) (h1 : term75 n) : True = (term75 n).
Proof. exact (SYM (@lem208441 n h1)). Qed.
Lemma lem208443 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (EQ_MP (@lem208442 n h1) (@lem0)). Qed.
Lemma lem208444 (a : nat) (b : nat) (n : nat) (h1 : term105) (h2 : term75 n) : (term88 b a n) = (term77 a b n).
Proof. exact (@lem208434 a b n h1 (@lem208443 n h2)). Qed.
Lemma lem208448 (a : nat) (b : nat) (n : nat) (h1 : term105) (h2 : term75 n) : (term156 b a n) = (term77 a b n).
Proof. exact (TRANS (@lem208432 b a n) (@lem208444 a b n h1 h2)). Qed.
Lemma lem208449 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem208450 (a : nat) (b : nat) (n : nat) (h1 : term105) (h2 : term75 n) : (term163 b a n) = (term121 a b n).
Proof. exact (MK_COMB (@lem208449) (@lem208448 a b n h1 h2)). Qed.
Lemma lem208455 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem208456 (a : nat) (b : nat) (n : nat) : (term138 b n a) = (term77 a b n).
Proof. exact (@lem208455 a (Nat.div b n)). Qed.
Lemma lem208460 (a : nat) (b : nat) (n : nat) (h1 : term105) (h2 : term75 n) : ((term156 b a n) = (term138 b n a)) = ((term77 a b n) = (term77 a b n)).
Proof. exact (MK_COMB (@lem208450 a b n h1 h2) (@lem208456 a b n)). Qed.
Lemma lem208462 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem208463 (x : nat) : (x = x) = True.
Proof. exact (@lem208462 nat x). Qed.
Lemma lem208464 (a : nat) (b : nat) (n : nat) : ((term77 a b n) = (term77 a b n)) = True.
Proof. exact (@lem208463 (term77 a b n)). Qed.
Lemma lem208465 (b : nat) (a : nat) (n : nat) (h1 : term105) (h2 : term75 n) : ((term156 b a n) = (term138 b n a)) = True.
Proof. exact (TRANS (@lem208460 a b n h1 h2) (@lem208464 a b n)). Qed.
Lemma lem208466 (b : nat) (n : nat) (a : nat) (h1 : term105) : term164 b n a.
Proof. exact (fun h0 : term75 n => @lem208465 b a n h1 h0). Qed.
Lemma lem208467 (b : nat) (a : nat) (n : nat) : term165 b a n.
Proof. exact (@lem208387 b a n True). Qed.
Lemma lem208468 (b : nat) (a : nat) (n : nat) (h1 : term105) : (term166 b n a) = (term125 n).
Proof. exact (@lem208467 b a n (@lem208466 b n a h1)). Qed.
Lemma lem208470 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem208471 (n : nat) : (term125 n) = True.
Proof. exact (@lem208470 (term75 n)). Qed.
Lemma lem208472 (b : nat) (n : nat) (a : nat) (h1 : term105) : (term166 b n a) = True.
Proof. exact (TRANS (@lem208468 b a n h1) (@lem208471 n)). Qed.
Lemma lem208473 (b : nat) (a : nat) (h1 : term105) : (term167 b a) = term127.
Proof. exact (fun_ext (fun n : nat => @lem208472 b n a h1)). Qed.
Lemma lem208474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208475 (b : nat) (a : nat) (h1 : term105) : (term168 b a) = term129.
Proof. exact (MK_COMB (@lem208474) (@lem208473 b a h1)). Qed.
Lemma lem208477 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem208478 (t : Prop) : (term131 t) = t.
Proof. exact (@lem208477 nat t). Qed.
Lemma lem208479 : term129 = True.
Proof. exact (@lem208478 True). Qed.
Lemma lem208480 (b : nat) (a : nat) (h1 : term105) : (term168 b a) = True.
Proof. exact (TRANS (@lem208475 b a h1) (@lem208479)). Qed.
Lemma lem208481 (a : nat) (h1 : term105) : (term169 a) = term127.
Proof. exact (fun_ext (fun b : nat => @lem208480 b a h1)). Qed.
Lemma lem208482 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208483 (a : nat) (h1 : term105) : (term170 a) = term129.
Proof. exact (MK_COMB (@lem208482) (@lem208481 a h1)). Qed.
Lemma lem208485 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem208486 (t : Prop) : (term131 t) = t.
Proof. exact (@lem208485 nat t). Qed.
Lemma lem208487 : term129 = True.
Proof. exact (@lem208486 True). Qed.
Lemma lem208488 (a : nat) (h1 : term105) : (term170 a) = True.
Proof. exact (TRANS (@lem208483 a h1) (@lem208487)). Qed.
Lemma lem208489 (h1 : term105) : term171 = term127.
Proof. exact (fun_ext (fun a : nat => @lem208488 a h1)). Qed.
Lemma lem208490 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208491 (h1 : term105) : term172 = term129.
Proof. exact (MK_COMB (@lem208490) (@lem208489 h1)). Qed.
Lemma lem208493 {A : Type'} (t : Prop) : (term130 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem208494 (t : Prop) : (term131 t) = t.
Proof. exact (@lem208493 nat t). Qed.
Lemma lem208495 : term129 = True.
Proof. exact (@lem208494 True). Qed.
Lemma lem208496 (h1 : term105) : term172 = True.
Proof. exact (TRANS (@lem208491 h1) (@lem208495)). Qed.
Lemma lem208497 (h1 : term105) : term173 = (True /\ True).
Proof. exact (MK_COMB (@lem208357 h1) (@lem208496 h1)). Qed.
Lemma lem208499 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem208500 : (True /\ True) = True.
Proof. exact (@lem208499 True). Qed.
Lemma lem208501 (h1 : term105) : term173 = True.
Proof. exact (TRANS (@lem208497 h1) (@lem208500)). Qed.
Lemma lem208502 (h1 : term105) : term65 = (True /\ True).
Proof. exact (MK_COMB (@lem208244 h1) (@lem208501 h1)). Qed.
Lemma lem208504 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem208505 : (True /\ True) = True.
Proof. exact (@lem208504 True). Qed.
Lemma lem208506 (h1 : term105) : term65 = True.
Proof. exact (TRANS (@lem208502 h1) (@lem208505)). Qed.
Lemma lem208507 : term174.
Proof. exact (fun h0 : term105 => @lem208506 h0). Qed.
Lemma lem208508 : term175.
Proof. exact (@lem208084 True). Qed.
Lemma lem208509 : term176 = term177.
Proof. exact (@lem208508 (@lem208507)). Qed.
Lemma lem208511 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem208512 : term177 = True.
Proof. exact (@lem208511 term105). Qed.
Lemma lem208513 : term176 = True.
Proof. exact (TRANS (@lem208509) (@lem208512)). Qed.
Lemma lem208514 : True = term176.
Proof. exact (SYM (@lem208513)). Qed.
Lemma lem208515 : term176.
Proof. exact (EQ_MP (@lem208514) (@lem0)). Qed.
Lemma lem208516 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (h1). Qed.
Lemma lem208518 (m : nat) (n : nat) (q : nat) : term37 m n q.
Proof. exact (EQ_MP (@lem207391 m n q) (@lem207390 m n q)). Qed.
Lemma lem208519 (a : nat) (b : nat) (n : nat) : term178 a b n.
Proof. exact (@lem208518 (term84 a n b) n (term77 a b n)). Qed.
Lemma lem208525 (m : nat) (n : nat) (p : nat) : (term22 m n p) = (term23 m n p).
Proof. exact (EQ_MP (@lem207356 m n p) (@lem207355 m n p)). Qed.
Lemma lem208526 (a : nat) (b : nat) (n : nat) : (term179 a b n) = (term180 a b n).
Proof. exact (@lem208525 a (Nat.div b n) n). Qed.
Lemma lem208527 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem208528 (a : nat) (b : nat) (n : nat) : (term181 a b n) = (term182 a b n).
Proof. exact (MK_COMB (@lem208527) (@lem208526 a b n)). Qed.
Lemma lem208529 (b : nat) (n : nat) : (Nat.modulo b n) = (Nat.modulo b n).
Proof. exact (eq_refl (Nat.modulo b n)). Qed.
Lemma lem208530 (a : nat) (b : nat) (n : nat) : (term183 a b n) = (term184 a b n).
Proof. exact (MK_COMB (@lem208528 a b n) (@lem208529 b n)). Qed.
Lemma lem208532 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem207347 m n p) (@lem207346 m n p)). Qed.
Lemma lem208533 (a : nat) (b : nat) (n : nat) : (term184 a b n) = (term185 a b n).
Proof. exact (@lem208532 (Nat.mul a n) (term186 b n) (Nat.modulo b n)). Qed.
Lemma lem208534 (a : nat) (b : nat) (n : nat) : (term183 a b n) = (term185 a b n).
Proof. exact (TRANS (@lem208530 a b n) (@lem208533 a b n)). Qed.
Lemma lem208535 (a : nat) (n : nat) (b : nat) : (term187 a n b) = (term187 a n b).
Proof. exact (eq_refl (term187 a n b)). Qed.
Lemma lem208536 (a : nat) (b : nat) (n : nat) : ((term84 a n b) = (term183 a b n)) = ((term84 a n b) = (term185 a b n)).
Proof. exact (MK_COMB (@lem208535 a n b) (@lem208534 a b n)). Qed.
Lemma lem208539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem208540 (a : nat) (b : nat) (n : nat) : (term188 a b n) = (term189 a b n).
Proof. exact (MK_COMB (@lem208539) (@lem208536 a b n)). Qed.
Lemma lem208541 (b : nat) (n : nat) : (term190 b n) = (term190 b n).
Proof. exact (eq_refl (term190 b n)). Qed.
Lemma lem208542 (a : nat) (b : nat) (n : nat) : (term191 a b n) = (term192 a b n).
Proof. exact (MK_COMB (@lem208540 a b n) (@lem208541 b n)). Qed.
Lemma lem208545 (a : nat) (b : nat) (n : nat) : (term192 a b n) = (term191 a b n).
Proof. exact (SYM (@lem208542 a b n)). Qed.
Lemma lem208547 (p : Prop) : p = (term193 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem208548 (a : nat) (b : nat) (n : nat) : (term192 a b n) = (term194 a b n).
Proof. exact (@lem208547 (term192 a b n)). Qed.
Lemma lem208549 (a : nat) (b : nat) (n : nat) : (term194 a b n) = (term192 a b n).
Proof. exact (SYM (@lem208548 a b n)). Qed.
Lemma lem208550 (a : nat) (b : nat) (n : nat) (h1 : term195 a b n) : term195 a b n.
Proof. exact (h1). Qed.
Lemma lem208553 (a : nat) (b : nat) (n : nat) (h1 : term196 a b n) : term196 a b n.
Proof. exact (h1). Qed.
Lemma lem208554 (a : nat) (b : nat) (n : nat) : term197 a b n.
Proof. exact (fun h0 : term196 a b n => @lem208553 a b n h0). Qed.
Lemma lem208555 (a : nat) (b : nat) (n : nat) (h1 : term197 a b n) : term197 a b n.
Proof. exact (h1). Qed.
Lemma lem208556 (a : nat) (b : nat) (n : nat) (h1 : term196 a b n) : term196 a b n.
Proof. exact (h1). Qed.
Lemma lem208557 (a : nat) (b : nat) (n : nat) (h1 : term196 a b n) (h2 : term197 a b n) : term196 a b n.
Proof. exact (@lem208555 a b n h2 (@lem208556 a b n h1)). Qed.
Lemma lem208558 (a : nat) (b : nat) (n : nat) (h1 : term196 a b n) : term198 a b n.
Proof. exact (fun h0 : term197 a b n => @lem208557 a b n h1 h0). Qed.
Lemma lem208559 (a : nat) (b : nat) (n : nat) (h1 : term197 a b n) : term197 a b n.
Proof. exact (h1). Qed.
Lemma lem208560 (a : nat) (b : nat) (n : nat) (h1 : term196 a b n) (h2 : term197 a b n) : term196 a b n.
Proof. exact (@lem208558 a b n h1 (@lem208559 a b n h2)). Qed.
Lemma lem208561 (a : nat) (b : nat) (n : nat) (h1 : term197 a b n) : term197 a b n.
Proof. exact (fun h0 : term196 a b n => @lem208560 a b n h0 h1). Qed.
Lemma lem208562 (a : nat) (b : nat) (n : nat) : term199 a b n.
Proof. exact (fun h0 : term197 a b n => @lem208561 a b n h0). Qed.
Lemma lem208565 (a : nat) (b : nat) (n : nat) : term197 a b n.
Proof. exact (@lem208562 a b n (@lem208554 a b n)). Qed.
Lemma lem208585 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem208586 : term200 = term201.
Proof. exact (@lem208585 term202). Qed.
Lemma lem208599 (a : nat) (b : nat) (n : nat) : (term203 a b n) = (term203 a b n).
Proof. exact (eq_refl (term203 a b n)). Qed.
Lemma lem208600 (a : nat) (b : nat) (n : nat) : (term204 a b n) = (term205 a b n).
Proof. exact (MK_COMB (@lem208599 a b n) (@lem208586)). Qed.
Lemma lem208603 (n : nat) : (term206 n) = (term206 n).
Proof. exact (eq_refl (term206 n)). Qed.
Lemma lem208604 (a : nat) (b : nat) (n : nat) : (term196 a b n) = (term207 a b n).
Proof. exact (MK_COMB (@lem208603 n) (@lem208600 a b n)). Qed.
Lemma lem208607 (b : nat) (n : nat) : (term208 b n) = (term209 b n).
Proof. exact (fun_ext (fun a : nat => @lem208604 a b n)). Qed.
Lemma lem208608 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208609 (b : nat) (n : nat) : (term210 b n) = (term211 b n).
Proof. exact (MK_COMB (@lem208608) (@lem208607 b n)). Qed.
Lemma lem208614 (n : nat) : (term212 n) = (term213 n).
Proof. exact (fun_ext (fun b : nat => @lem208609 b n)). Qed.
Lemma lem208615 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208616 (n : nat) : (term214 n) = (term215 n).
Proof. exact (MK_COMB (@lem208615) (@lem208614 n)). Qed.
Lemma lem208621 : term216 = term217.
Proof. exact (fun_ext (fun n : nat => @lem208616 n)). Qed.
Lemma lem208622 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208631 : term218 = term219.
Proof. exact (MK_COMB (@lem208622) (@lem208621)). Qed.
Lemma lem208642 (m : nat) (n : nat) : (term220 m n) = (term220 m n).
Proof. exact (eq_refl (term220 m n)). Qed.
Lemma lem208643 (m : nat) : (term221 m) = (term221 m).
Proof. exact (fun_ext (fun n : nat => @lem208642 m n)). Qed.
Lemma lem208644 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208645 (m : nat) : (term222 m) = (term222 m).
Proof. exact (MK_COMB (@lem208644) (@lem208643 m)). Qed.
Lemma lem208646 : term223 = term223.
Proof. exact (fun_ext (fun m : nat => @lem208645 m)). Qed.
Lemma lem208647 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208648 : term202 = term202.
Proof. exact (MK_COMB (@lem208647) (@lem208646)). Qed.
Lemma lem208649 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem208650 : term201 = term201.
Proof. exact (MK_COMB (@lem208649) (@lem208648)). Qed.
Lemma lem208659 (a : nat) (b : nat) (n : nat) : (term203 a b n) = (term203 a b n).
Proof. exact (eq_refl (term203 a b n)). Qed.
Lemma lem208660 (a : nat) (b : nat) (n : nat) : (term205 a b n) = (term205 a b n).
Proof. exact (MK_COMB (@lem208659 a b n) (@lem208650)). Qed.
Lemma lem208665 (n : nat) : (term206 n) = (term206 n).
Proof. exact (eq_refl (term206 n)). Qed.
Lemma lem208666 (a : nat) (b : nat) (n : nat) : (term207 a b n) = (term207 a b n).
Proof. exact (MK_COMB (@lem208665 n) (@lem208660 a b n)). Qed.
Lemma lem208667 (b : nat) (n : nat) : (term209 b n) = (term209 b n).
Proof. exact (fun_ext (fun a : nat => @lem208666 a b n)). Qed.
Lemma lem208668 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208669 (b : nat) (n : nat) : (term211 b n) = (term211 b n).
Proof. exact (MK_COMB (@lem208668) (@lem208667 b n)). Qed.
Lemma lem208670 (n : nat) : (term213 n) = (term213 n).
Proof. exact (fun_ext (fun b : nat => @lem208669 b n)). Qed.
Lemma lem208671 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208672 (n : nat) : (term215 n) = (term215 n).
Proof. exact (MK_COMB (@lem208671) (@lem208670 n)). Qed.
Lemma lem208673 : term217 = term217.
Proof. exact (fun_ext (fun n : nat => @lem208672 n)). Qed.
Lemma lem208674 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208675 : term219 = term219.
Proof. exact (MK_COMB (@lem208674) (@lem208673)). Qed.
Lemma lem208718 : term218 = term219.
Proof. exact (TRANS (@lem208631) (@lem208675)). Qed.
Lemma lem208719 : term219 = term218.
Proof. exact (SYM (@lem208718)). Qed.
Lemma lem208721 (a : nat) (b : nat) (n : nat) (h1 : term195 a b n) : term195 a b n.
Proof. exact (h1). Qed.
Lemma lem208722 (h1 : term202) : term202.
Proof. exact (h1). Qed.
Lemma lem208728 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (h1). Qed.
Lemma lem208739 (a : nat) (b : nat) (n : nat) : (term195 a b n) = (term224 a b n).
Proof. exact (@lem17045 ((term84 a n b) = (term185 a b n)) (term190 b n)). Qed.
Lemma lem208743 (n : nat) : (term225 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem208748 (m : nat) (n : nat) : (term226 m n) = (term226 m n).
Proof. exact (eq_refl (term226 m n)). Qed.
Lemma lem208749 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem208750 (n : nat) : (term227 n) = (term228 n).
Proof. exact (MK_COMB (@lem208749) (@lem208743 n)). Qed.
Lemma lem208751 (m : nat) (n : nat) : (term229 m n) = (term230 m n).
Proof. exact (MK_COMB (@lem208750 n) (@lem208748 m n)). Qed.
Lemma lem208752 (m : nat) (n : nat) : (term220 m n) = (term229 m n).
Proof. exact (@lem17265 (term75 n) (term226 m n)). Qed.
Lemma lem208753 (m : nat) (n : nat) : (term220 m n) = (term230 m n).
Proof. exact (TRANS (@lem208752 m n) (@lem208751 m n)). Qed.
Lemma lem208754 (m : nat) : (term221 m) = (term231 m).
Proof. exact (fun_ext (fun n : nat => @lem208753 m n)). Qed.
Lemma lem208755 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208756 (m : nat) : (term222 m) = (term232 m).
Proof. exact (MK_COMB (@lem208755) (@lem208754 m)). Qed.
Lemma lem208757 : term223 = term233.
Proof. exact (fun_ext (fun m : nat => @lem208756 m)). Qed.
Lemma lem208758 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208815 : term202 = term234.
Proof. exact (MK_COMB (@lem208758) (@lem208757)). Qed.
Lemma lem208816 (h1 : term202) : term234.
Proof. exact (EQ_MP (@lem208815) (@lem208722 h1)). Qed.
Lemma lem208826 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (h1). Qed.
Lemma lem208880 (a : nat) (b : nat) (n : nat) (h1 : term195 a b n) : term224 a b n.
Proof. exact (EQ_MP (@lem208739 a b n) (@lem208721 a b n h1)). Qed.
Lemma lem208923 (m : nat) (n : nat) : (term230 m n) = (term230 m n).
Proof. exact (eq_refl (term230 m n)). Qed.
Lemma lem208924 (m : nat) : (term231 m) = (term231 m).
Proof. exact (fun_ext (fun n : nat => @lem208923 m n)). Qed.
Lemma lem208925 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208926 (m : nat) : (term232 m) = (term232 m).
Proof. exact (MK_COMB (@lem208925) (@lem208924 m)). Qed.
Lemma lem208927 : term233 = term233.
Proof. exact (fun_ext (fun m : nat => @lem208926 m)). Qed.
Lemma lem208928 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208929 : term234 = term234.
Proof. exact (MK_COMB (@lem208928) (@lem208927)). Qed.
Lemma lem208930 (h1 : term202) : term234.
Proof. exact (EQ_MP (@lem208929) (@lem208816 h1)). Qed.
Lemma lem208936 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (h1). Qed.
Lemma lem208954 (m : nat) (n : nat) : (term230 m n) = (term235 m n).
Proof. exact (@lem19490 (m = (term236 m n)) (n = (NUMERAL 0)) (term190 m n)). Qed.
Lemma lem208955 (m : nat) : (term231 m) = (term237 m).
Proof. exact (fun_ext (fun n : nat => @lem208954 m n)). Qed.
Lemma lem208956 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208957 (m : nat) : (term232 m) = (term238 m).
Proof. exact (MK_COMB (@lem208956) (@lem208955 m)). Qed.
Lemma lem208958 : term233 = term239.
Proof. exact (fun_ext (fun m : nat => @lem208957 m)). Qed.
Lemma lem208959 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208961 : term234 = term240.
Proof. exact (MK_COMB (@lem208959) (@lem208958)). Qed.
Lemma lem208962 (h1 : term202) : term240.
Proof. exact (EQ_MP (@lem208961) (@lem208930 h1)). Qed.
Lemma lem208966 (a : nat) (b : nat) (n : nat) (h1 : term241 a b n) : term241 a b n.
Proof. exact (h1). Qed.
Lemma lem208970 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (h1). Qed.
Lemma lem208988 (m : nat) (n : nat) : (term230 m n) = (term235 m n).
Proof. exact (@lem19490 (m = (term236 m n)) (n = (NUMERAL 0)) (term190 m n)). Qed.
Lemma lem208989 (m : nat) : (term231 m) = (term237 m).
Proof. exact (fun_ext (fun n : nat => @lem208988 m n)). Qed.
Lemma lem208990 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208991 (m : nat) : (term232 m) = (term238 m).
Proof. exact (MK_COMB (@lem208990) (@lem208989 m)). Qed.
Lemma lem208992 : term233 = term239.
Proof. exact (fun_ext (fun m : nat => @lem208991 m)). Qed.
Lemma lem208993 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem208995 : term234 = term240.
Proof. exact (MK_COMB (@lem208993) (@lem208992)). Qed.
Lemma lem208996 (h1 : term202) : term240.
Proof. exact (EQ_MP (@lem208995) (@lem208930 h1)). Qed.
Lemma lem209000 (b : nat) (n : nat) (h1 : term242 b n) : term242 b n.
Proof. exact (h1). Qed.
Lemma lem209001 (_4191 : nat) (h1 : term202) : term243 _4191.
Proof. exact (@lem208962 h1 _4191). Qed.
Lemma lem209002 (_4191 : nat) : (term243 _4191) = (term238 _4191).
Proof. exact (eq_refl (term243 _4191)). Qed.
Lemma lem209003 (_4191 : nat) (h1 : term202) : term238 _4191.
Proof. exact (EQ_MP (@lem209002 _4191) (@lem209001 _4191 h1)). Qed.
Lemma lem209004 (_4191 : nat) (_4192 : nat) (h1 : term202) : term244 _4191 _4192.
Proof. exact (@lem209003 _4191 h1 _4192). Qed.
Lemma lem209005 (_4191 : nat) (_4192 : nat) : (term244 _4191 _4192) = (term235 _4191 _4192).
Proof. exact (eq_refl (term244 _4191 _4192)). Qed.
Lemma lem209006 (_4191 : nat) (_4192 : nat) (h1 : term202) : term235 _4191 _4192.
Proof. exact (EQ_MP (@lem209005 _4191 _4192) (@lem209004 _4191 _4192 h1)). Qed.
Lemma lem209007 (_4193 : nat) (h1 : term202) : term243 _4193.
Proof. exact (@lem208996 h1 _4193). Qed.
Lemma lem209008 (_4193 : nat) : (term243 _4193) = (term238 _4193).
Proof. exact (eq_refl (term243 _4193)). Qed.
Lemma lem209009 (_4193 : nat) (h1 : term202) : term238 _4193.
Proof. exact (EQ_MP (@lem209008 _4193) (@lem209007 _4193 h1)). Qed.
Lemma lem209010 (_4193 : nat) (_4194 : nat) (h1 : term202) : term244 _4193 _4194.
Proof. exact (@lem209009 _4193 h1 _4194). Qed.
Lemma lem209011 (_4193 : nat) (_4194 : nat) : (term244 _4193 _4194) = (term235 _4193 _4194).
Proof. exact (eq_refl (term244 _4193 _4194)). Qed.
Lemma lem209012 (_4193 : nat) (_4194 : nat) (h1 : term202) : term235 _4193 _4194.
Proof. exact (EQ_MP (@lem209011 _4193 _4194) (@lem209010 _4193 _4194 h1)). Qed.
Lemma lem209018 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (h1). Qed.
Lemma lem209020 (a : nat) (b : nat) (n : nat) (h1 : term241 a b n) : term241 a b n.
Proof. exact (h1). Qed.
Lemma lem209026 (_4191 : nat) (_4192 : nat) (h1 : term202) : term245 _4191 _4192.
Proof. exact (proj1 (@lem209006 _4191 _4192 h1)). Qed.
Lemma lem209034 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (h1). Qed.
Lemma lem209036 (b : nat) (n : nat) (h1 : term242 b n) : term242 b n.
Proof. exact (h1). Qed.
Lemma lem209048 (_4193 : nat) (_4194 : nat) (h1 : term202) : term246 _4193 _4194.
Proof. exact (proj2 (@lem209012 _4193 _4194 h1)). Qed.
Lemma lem209113 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem209114 (_4211 : nat) (_4213 : nat) (h1 : _4211 = _4213) : _4211 = _4213.
Proof. exact (h1). Qed.
Lemma lem209115 (_4212 : nat) (_4214 : nat) (h1 : _4212 = _4214) : _4212 = _4214.
Proof. exact (h1). Qed.
Lemma lem209116 (_4211 : nat) (_4213 : nat) (h1 : _4211 = _4213) : (Nat.add _4211) = (Nat.add _4213).
Proof. exact (MK_COMB (@lem209113) (@lem209114 _4211 _4213 h1)). Qed.
Lemma lem209117 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) (h1 : _4211 = _4213) (h2 : _4212 = _4214) : (Nat.add _4211 _4212) = (Nat.add _4213 _4214).
Proof. exact (MK_COMB (@lem209116 _4211 _4213 h1) (@lem209115 _4212 _4214 h2)). Qed.
Lemma lem209118 (_4212 : nat) (_4214 : nat) (_4211 : nat) (_4213 : nat) (h1 : _4211 = _4213) : term247 _4211 _4212 _4213 _4214.
Proof. exact (fun h0 : _4212 = _4214 => @lem209117 _4211 _4213 _4212 _4214 h1 h0). Qed.
Lemma lem209120 (a : Prop) (b : Prop) : (a -> b) = (term248 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem209121 (_4211 : nat) (_4212 : nat) (_4213 : nat) (_4214 : nat) : (term247 _4211 _4212 _4213 _4214) = (term249 _4211 _4212 _4213 _4214).
Proof. exact (@lem209120 (_4212 = _4214) ((Nat.add _4211 _4212) = (Nat.add _4213 _4214))). Qed.
Lemma lem209122 (_4212 : nat) (_4214 : nat) (_4211 : nat) (_4213 : nat) (h1 : _4211 = _4213) : term249 _4211 _4212 _4213 _4214.
Proof. exact (EQ_MP (@lem209121 _4211 _4212 _4213 _4214) (@lem209118 _4212 _4214 _4211 _4213 h1)). Qed.
Lemma lem209123 (_4211 : nat) (_4212 : nat) (_4213 : nat) (_4214 : nat) : term250 _4211 _4212 _4213 _4214.
Proof. exact (fun h0 : _4211 = _4213 => @lem209122 _4212 _4214 _4211 _4213 h0). Qed.
Lemma lem209125 (a : Prop) (b : Prop) : (a -> b) = (term248 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem209126 (_4211 : nat) (_4212 : nat) (_4213 : nat) (_4214 : nat) : (term250 _4211 _4212 _4213 _4214) = (term251 _4211 _4212 _4213 _4214).
Proof. exact (@lem209125 (_4211 = _4213) (term249 _4211 _4212 _4213 _4214)). Qed.
Lemma lem209127 (_4211 : nat) (_4212 : nat) (_4213 : nat) (_4214 : nat) : term251 _4211 _4212 _4213 _4214.
Proof. exact (EQ_MP (@lem209126 _4211 _4212 _4213 _4214) (@lem209123 _4211 _4212 _4213 _4214)). Qed.
Lemma lem209139 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem209140 (a : nat) (n : nat) : (Nat.mul a n) = (Nat.mul a n).
Proof. exact (@lem209139 (Nat.mul a n)). Qed.
Lemma lem209141 (a : nat) (n : nat) : term252 a n.
Proof. exact (fun h0 : term253 a n => @lem209140 a n). Qed.
Lemma lem209143 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem209144 (a : nat) (n : nat) : (term252 a n) = ((Nat.mul a n) = (Nat.mul a n)).
Proof. exact (@lem209143 ((Nat.mul a n) = (Nat.mul a n))). Qed.
Lemma lem209145 (a : nat) (n : nat) : (Nat.mul a n) = (Nat.mul a n).
Proof. exact (EQ_MP (@lem209144 a n) (@lem209141 a n)). Qed.
Lemma lem209147 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (h1). Qed.
Lemma lem209148 (n : nat) (h1 : term75 n) : term255 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem209147 n h1). Qed.
Lemma lem209150 (p : Prop) : (term256 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem209151 (n : nat) : (term255 n) = (term75 n).
Proof. exact (@lem209150 (n = (NUMERAL 0))). Qed.
Lemma lem209152 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (EQ_MP (@lem209151 n) (@lem209148 n h1)). Qed.
Lemma lem209158 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem209159 (_4191 : nat) (_4192 : nat) : (term245 _4191 _4192) = (term257 _4191 _4192).
Proof. exact (@lem209158 (_4191 = (term236 _4191 _4192)) (_4192 = (NUMERAL 0))). Qed.
Lemma lem209169 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem209170 (_4191 : nat) (_4192 : nat) : (term258 _4191 _4192) = (term259 _4191 _4192).
Proof. exact (MK_COMB (@lem209169) (@lem209159 _4191 _4192)). Qed.
Lemma lem209180 (_4191 : nat) (_4192 : nat) : (term257 _4191 _4192) = (term257 _4191 _4192).
Proof. exact (eq_refl (term257 _4191 _4192)). Qed.
Lemma lem209181 (_4191 : nat) (_4192 : nat) : ((term245 _4191 _4192) = (term257 _4191 _4192)) = ((term257 _4191 _4192) = (term257 _4191 _4192)).
Proof. exact (MK_COMB (@lem209170 _4191 _4192) (@lem209180 _4191 _4192)). Qed.
Lemma lem209183 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem209184 (x : Prop) : (x = x) = True.
Proof. exact (@lem209183 Prop x). Qed.
Lemma lem209185 (_4191 : nat) (_4192 : nat) : ((term257 _4191 _4192) = (term257 _4191 _4192)) = True.
Proof. exact (@lem209184 (term257 _4191 _4192)). Qed.
Lemma lem209186 (_4191 : nat) (_4192 : nat) : ((term245 _4191 _4192) = (term257 _4191 _4192)) = True.
Proof. exact (TRANS (@lem209181 _4191 _4192) (@lem209185 _4191 _4192)). Qed.
Lemma lem209187 (_4191 : nat) (_4192 : nat) : True = ((term245 _4191 _4192) = (term257 _4191 _4192)).
Proof. exact (SYM (@lem209186 _4191 _4192)). Qed.
Lemma lem209188 (_4191 : nat) (_4192 : nat) : (term245 _4191 _4192) = (term257 _4191 _4192).
Proof. exact (EQ_MP (@lem209187 _4191 _4192) (@lem0)). Qed.
Lemma lem209189 (_4191 : nat) (_4192 : nat) (h1 : term202) : term257 _4191 _4192.
Proof. exact (EQ_MP (@lem209188 _4191 _4192) (@lem209026 _4191 _4192 h1)). Qed.
Lemma lem209191 (b : Prop) (a : Prop) : (a \/ b) = (term260 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem209194 (_4191 : nat) (_4192 : nat) : (term257 _4191 _4192) = (term261 _4191 _4192).
Proof. exact (@lem209191 (_4192 = (NUMERAL 0)) (_4191 = (term236 _4191 _4192))). Qed.
Lemma lem209197 (_4191 : nat) (_4192 : nat) (h1 : term202) : term261 _4191 _4192.
Proof. exact (EQ_MP (@lem209194 _4191 _4192) (@lem209189 _4191 _4192 h1)). Qed.
Lemma lem209198 (_4191 : nat) (n : nat) (h1 : term202) : term261 _4191 n.
Proof. exact (@lem209197 _4191 n h1). Qed.
Lemma lem209201 (_4191 : nat) (n : nat) (h1 : term202) (h2 : term75 n) : _4191 = (term236 _4191 n).
Proof. exact (@lem209198 _4191 n h1 (@lem209152 n h2)). Qed.
Lemma lem209202 (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) : b = (term236 b n).
Proof. exact (@lem209201 b n h1 h2). Qed.
Lemma lem209203 (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) : term262 b n.
Proof. exact (fun h0 : term263 b n => @lem209202 b n h1 h2). Qed.
Lemma lem209205 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem209206 (b : nat) (n : nat) : (term262 b n) = (b = (term236 b n)).
Proof. exact (@lem209205 (b = (term236 b n))). Qed.
Lemma lem209207 (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) : b = (term236 b n).
Proof. exact (EQ_MP (@lem209206 b n) (@lem209203 b n h1 h2)). Qed.
Lemma lem209225 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem209226 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) : (term249 _4211 _4212 _4213 _4214) = (term264 _4211 _4213 _4212 _4214).
Proof. exact (@lem209225 ((Nat.add _4211 _4212) = (Nat.add _4213 _4214)) (term265 _4212 _4214)). Qed.
Lemma lem209236 (_4211 : nat) (_4213 : nat) : (term266 _4211 _4213) = (term266 _4211 _4213).
Proof. exact (eq_refl (term266 _4211 _4213)). Qed.
Lemma lem209237 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) : (term251 _4211 _4212 _4213 _4214) = (term267 _4211 _4213 _4212 _4214).
Proof. exact (MK_COMB (@lem209236 _4211 _4213) (@lem209226 _4211 _4213 _4212 _4214)). Qed.
Lemma lem209241 (q : Prop) (p : Prop) (r : Prop) : (term268 p q r) = (term268 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem209242 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) : (term267 _4211 _4213 _4212 _4214) = (term269 _4211 _4213 _4212 _4214).
Proof. exact (@lem209241 ((Nat.add _4211 _4212) = (Nat.add _4213 _4214)) (term265 _4211 _4213) (term265 _4212 _4214)). Qed.
Lemma lem209264 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) : (term251 _4211 _4212 _4213 _4214) = (term269 _4211 _4213 _4212 _4214).
Proof. exact (TRANS (@lem209237 _4211 _4213 _4212 _4214) (@lem209242 _4211 _4213 _4212 _4214)). Qed.
Lemma lem209265 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem209266 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) : (term270 _4211 _4212 _4213 _4214) = (term271 _4211 _4213 _4212 _4214).
Proof. exact (MK_COMB (@lem209265) (@lem209264 _4211 _4213 _4212 _4214)). Qed.
Lemma lem209288 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) : (term269 _4211 _4213 _4212 _4214) = (term269 _4211 _4213 _4212 _4214).
Proof. exact (eq_refl (term269 _4211 _4213 _4212 _4214)). Qed.
Lemma lem209289 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) : ((term251 _4211 _4212 _4213 _4214) = (term269 _4211 _4213 _4212 _4214)) = ((term269 _4211 _4213 _4212 _4214) = (term269 _4211 _4213 _4212 _4214)).
Proof. exact (MK_COMB (@lem209266 _4211 _4213 _4212 _4214) (@lem209288 _4211 _4213 _4212 _4214)). Qed.
Lemma lem209291 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem209292 (x : Prop) : (x = x) = True.
Proof. exact (@lem209291 Prop x). Qed.
Lemma lem209293 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) : ((term269 _4211 _4213 _4212 _4214) = (term269 _4211 _4213 _4212 _4214)) = True.
Proof. exact (@lem209292 (term269 _4211 _4213 _4212 _4214)). Qed.
Lemma lem209294 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) : ((term251 _4211 _4212 _4213 _4214) = (term269 _4211 _4213 _4212 _4214)) = True.
Proof. exact (TRANS (@lem209289 _4211 _4213 _4212 _4214) (@lem209293 _4211 _4213 _4212 _4214)). Qed.
Lemma lem209295 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) : True = ((term251 _4211 _4212 _4213 _4214) = (term269 _4211 _4213 _4212 _4214)).
Proof. exact (SYM (@lem209294 _4211 _4213 _4212 _4214)). Qed.
Lemma lem209296 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) : (term251 _4211 _4212 _4213 _4214) = (term269 _4211 _4213 _4212 _4214).
Proof. exact (EQ_MP (@lem209295 _4211 _4213 _4212 _4214) (@lem0)). Qed.
Lemma lem209297 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) : term269 _4211 _4213 _4212 _4214.
Proof. exact (EQ_MP (@lem209296 _4211 _4213 _4212 _4214) (@lem209127 _4211 _4212 _4213 _4214)). Qed.
Lemma lem209299 (b : Prop) (a : Prop) : (a \/ b) = (term260 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem209300 (_4211 : nat) (_4212 : nat) (_4213 : nat) (_4214 : nat) : (term269 _4211 _4213 _4212 _4214) = (term272 _4211 _4212 _4213 _4214).
Proof. exact (@lem209299 (term273 _4211 _4213 _4212 _4214) ((Nat.add _4211 _4212) = (Nat.add _4213 _4214))). Qed.
Lemma lem209302 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem209303 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) : (term276 _4211 _4213 _4212 _4214) = (term277 _4211 _4213 _4212 _4214).
Proof. exact (@lem209302 (term265 _4211 _4213) (term265 _4212 _4214)). Qed.
Lemma lem209305 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem209306 (_4211 : nat) (_4213 : nat) : (term279 _4211 _4213) = (_4211 = _4213).
Proof. exact (@lem209305 (_4211 = _4213)). Qed.
Lemma lem209307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem209308 (_4211 : nat) (_4213 : nat) : (term280 _4211 _4213) = (term281 _4211 _4213).
Proof. exact (MK_COMB (@lem209307) (@lem209306 _4211 _4213)). Qed.
Lemma lem209310 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem209311 (_4212 : nat) (_4214 : nat) : (term279 _4212 _4214) = (_4212 = _4214).
Proof. exact (@lem209310 (_4212 = _4214)). Qed.
Lemma lem209312 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) : (term277 _4211 _4213 _4212 _4214) = (term282 _4211 _4213 _4212 _4214).
Proof. exact (MK_COMB (@lem209308 _4211 _4213) (@lem209311 _4212 _4214)). Qed.
Lemma lem209313 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) : (term276 _4211 _4213 _4212 _4214) = (term282 _4211 _4213 _4212 _4214).
Proof. exact (TRANS (@lem209303 _4211 _4213 _4212 _4214) (@lem209312 _4211 _4213 _4212 _4214)). Qed.
Lemma lem209314 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem209315 (_4211 : nat) (_4213 : nat) (_4212 : nat) (_4214 : nat) : (term283 _4211 _4213 _4212 _4214) = (term284 _4211 _4213 _4212 _4214).
Proof. exact (MK_COMB (@lem209314) (@lem209313 _4211 _4213 _4212 _4214)). Qed.
Lemma lem209316 (_4211 : nat) (_4212 : nat) (_4213 : nat) (_4214 : nat) : ((Nat.add _4211 _4212) = (Nat.add _4213 _4214)) = ((Nat.add _4211 _4212) = (Nat.add _4213 _4214)).
Proof. exact (eq_refl ((Nat.add _4211 _4212) = (Nat.add _4213 _4214))). Qed.
Lemma lem209317 (_4211 : nat) (_4212 : nat) (_4213 : nat) (_4214 : nat) : (term272 _4211 _4212 _4213 _4214) = (term285 _4211 _4212 _4213 _4214).
Proof. exact (MK_COMB (@lem209315 _4211 _4213 _4212 _4214) (@lem209316 _4211 _4212 _4213 _4214)). Qed.
Lemma lem209318 (_4211 : nat) (_4212 : nat) (_4213 : nat) (_4214 : nat) : (term269 _4211 _4213 _4212 _4214) = (term285 _4211 _4212 _4213 _4214).
Proof. exact (TRANS (@lem209300 _4211 _4212 _4213 _4214) (@lem209317 _4211 _4212 _4213 _4214)). Qed.
Lemma lem209320 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) : term286 a b n.
Proof. exact (conj (@lem209145 a n) (@lem209207 b n h1 h2)). Qed.
Lemma lem209322 (_4211 : nat) (_4212 : nat) (_4213 : nat) (_4214 : nat) : term285 _4211 _4212 _4213 _4214.
Proof. exact (EQ_MP (@lem209318 _4211 _4212 _4213 _4214) (@lem209297 _4211 _4213 _4212 _4214)). Qed.
Lemma lem209323 (a : nat) (b : nat) (n : nat) : term287 a b n.
Proof. exact (@lem209322 (Nat.mul a n) b (Nat.mul a n) (term236 b n)). Qed.
Lemma lem209326 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) : (term84 a n b) = (term185 a b n).
Proof. exact (@lem209323 a b n (@lem209320 a b n h1 h2)). Qed.
Lemma lem209327 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) : term288 a b n.
Proof. exact (fun h0 : term241 a b n => @lem209326 a b n h1 h2). Qed.
Lemma lem209329 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem209330 (a : nat) (b : nat) (n : nat) : (term288 a b n) = ((term84 a n b) = (term185 a b n)).
Proof. exact (@lem209329 ((term84 a n b) = (term185 a b n))). Qed.
Lemma lem209331 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) : (term84 a n b) = (term185 a b n).
Proof. exact (EQ_MP (@lem209330 a b n) (@lem209327 a b n h1 h2)). Qed.
Lemma lem209334 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem209336 (a : nat) (b : nat) (n : nat) : (term241 a b n) = (term289 a b n).
Proof. exact (@lem209334 ((term84 a n b) = (term185 a b n))). Qed.
Lemma lem209339 (a : nat) (b : nat) (n : nat) (h1 : term241 a b n) : term289 a b n.
Proof. exact (EQ_MP (@lem209336 a b n) (@lem209020 a b n h1)). Qed.
Lemma lem209342 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) (h3 : term241 a b n) : False.
Proof. exact (@lem209339 a b n h3 (@lem209331 a b n h1 h2)). Qed.
Lemma lem209343 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) (h3 : term241 a b n) : term290.
Proof. exact (fun h0 : ~ False => @lem209342 a b n h1 h2 h3). Qed.
Lemma lem209345 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem209346 : term290 = False.
Proof. exact (@lem209345 False). Qed.
Lemma lem209347 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) (h3 : term241 a b n) : False.
Proof. exact (EQ_MP (@lem209346) (@lem209343 a b n h1 h2 h3)). Qed.
Lemma lem209438 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (h1). Qed.
Lemma lem209439 (n : nat) (h1 : term75 n) : term255 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem209438 n h1). Qed.
Lemma lem209441 (p : Prop) : (term256 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem209442 (n : nat) : (term255 n) = (term75 n).
Proof. exact (@lem209441 (n = (NUMERAL 0))). Qed.
Lemma lem209443 (n : nat) (h1 : term75 n) : term75 n.
Proof. exact (EQ_MP (@lem209442 n) (@lem209439 n h1)). Qed.
Lemma lem209449 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem209450 (_4193 : nat) (_4194 : nat) : (term246 _4193 _4194) = (term291 _4193 _4194).
Proof. exact (@lem209449 (term190 _4193 _4194) (_4194 = (NUMERAL 0))). Qed.
Lemma lem209458 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem209459 (_4193 : nat) (_4194 : nat) : (term292 _4193 _4194) = (term293 _4193 _4194).
Proof. exact (MK_COMB (@lem209458) (@lem209450 _4193 _4194)). Qed.
Lemma lem209467 (_4193 : nat) (_4194 : nat) : (term291 _4193 _4194) = (term291 _4193 _4194).
Proof. exact (eq_refl (term291 _4193 _4194)). Qed.
Lemma lem209468 (_4193 : nat) (_4194 : nat) : ((term246 _4193 _4194) = (term291 _4193 _4194)) = ((term291 _4193 _4194) = (term291 _4193 _4194)).
Proof. exact (MK_COMB (@lem209459 _4193 _4194) (@lem209467 _4193 _4194)). Qed.
Lemma lem209470 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem209471 (x : Prop) : (x = x) = True.
Proof. exact (@lem209470 Prop x). Qed.
Lemma lem209472 (_4193 : nat) (_4194 : nat) : ((term291 _4193 _4194) = (term291 _4193 _4194)) = True.
Proof. exact (@lem209471 (term291 _4193 _4194)). Qed.
Lemma lem209473 (_4193 : nat) (_4194 : nat) : ((term246 _4193 _4194) = (term291 _4193 _4194)) = True.
Proof. exact (TRANS (@lem209468 _4193 _4194) (@lem209472 _4193 _4194)). Qed.
Lemma lem209474 (_4193 : nat) (_4194 : nat) : True = ((term246 _4193 _4194) = (term291 _4193 _4194)).
Proof. exact (SYM (@lem209473 _4193 _4194)). Qed.
Lemma lem209475 (_4193 : nat) (_4194 : nat) : (term246 _4193 _4194) = (term291 _4193 _4194).
Proof. exact (EQ_MP (@lem209474 _4193 _4194) (@lem0)). Qed.
Lemma lem209476 (_4193 : nat) (_4194 : nat) (h1 : term202) : term291 _4193 _4194.
Proof. exact (EQ_MP (@lem209475 _4193 _4194) (@lem209048 _4193 _4194 h1)). Qed.
Lemma lem209478 (b : Prop) (a : Prop) : (a \/ b) = (term260 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem209481 (_4193 : nat) (_4194 : nat) : (term291 _4193 _4194) = (term294 _4193 _4194).
Proof. exact (@lem209478 (_4194 = (NUMERAL 0)) (term190 _4193 _4194)). Qed.
Lemma lem209484 (_4193 : nat) (_4194 : nat) (h1 : term202) : term294 _4193 _4194.
Proof. exact (EQ_MP (@lem209481 _4193 _4194) (@lem209476 _4193 _4194 h1)). Qed.
Lemma lem209485 (_4193 : nat) (n : nat) (h1 : term202) : term294 _4193 n.
Proof. exact (@lem209484 _4193 n h1). Qed.
Lemma lem209488 (_4193 : nat) (n : nat) (h1 : term202) (h2 : term75 n) : term190 _4193 n.
Proof. exact (@lem209485 _4193 n h1 (@lem209443 n h2)). Qed.
Lemma lem209489 (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) : term190 b n.
Proof. exact (@lem209488 b n h1 h2). Qed.
Lemma lem209490 (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) : term295 b n.
Proof. exact (fun h0 : term242 b n => @lem209489 b n h1 h2). Qed.
Lemma lem209492 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem209493 (b : nat) (n : nat) : (term295 b n) = (term190 b n).
Proof. exact (@lem209492 (term190 b n)). Qed.
Lemma lem209494 (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) : term190 b n.
Proof. exact (EQ_MP (@lem209493 b n) (@lem209490 b n h1 h2)). Qed.
Lemma lem209497 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem209499 (b : nat) (n : nat) : (term242 b n) = (term296 b n).
Proof. exact (@lem209497 (term190 b n)). Qed.
Lemma lem209502 (b : nat) (n : nat) (h1 : term242 b n) : term296 b n.
Proof. exact (EQ_MP (@lem209499 b n) (@lem209036 b n h1)). Qed.
Lemma lem209505 (b : nat) (n : nat) (h1 : term202) (h2 : term242 b n) (h3 : term75 n) : False.
Proof. exact (@lem209502 b n h2 (@lem209494 b n h1 h3)). Qed.
Lemma lem209506 (b : nat) (n : nat) (h1 : term202) (h2 : term242 b n) (h3 : term75 n) : term290.
Proof. exact (fun h0 : ~ False => @lem209505 b n h1 h2 h3). Qed.
Lemma lem209508 (p : Prop) : (term254 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem209509 : term290 = False.
Proof. exact (@lem209508 False). Qed.
Lemma lem209510 (b : nat) (n : nat) (h1 : term202) (h2 : term242 b n) (h3 : term75 n) : False.
Proof. exact (EQ_MP (@lem209509) (@lem209506 b n h1 h2 h3)). Qed.
Lemma lem209511 (b : nat) (n : nat) (h1 : term202) (h2 : term242 b n) (h3 : term75 n) : (term242 b n) = False.
Proof. exact (prop_ext (fun h4 : term242 b n => @lem209510 b n h1 h2 h3) (fun h4 : False => @lem209036 b n h2)). Qed.
Lemma lem209512 (b : nat) (n : nat) (h1 : term202) (h2 : term242 b n) (h3 : term75 n) : False.
Proof. exact (EQ_MP (@lem209511 b n h1 h2 h3) (@lem209036 b n h2)). Qed.
Lemma lem209513 (b : nat) (n : nat) (h1 : term202) (h2 : term242 b n) (h3 : term75 n) : (term75 n) = False.
Proof. exact (prop_ext (fun h4 : term75 n => @lem209512 b n h1 h2 h3) (fun h4 : False => @lem209034 n h3)). Qed.
Lemma lem209514 (b : nat) (n : nat) (h1 : term202) (h2 : term242 b n) (h3 : term75 n) : False.
Proof. exact (EQ_MP (@lem209513 b n h1 h2 h3) (@lem209034 n h3)). Qed.
Lemma lem209515 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) (h3 : term241 a b n) : (term241 a b n) = False.
Proof. exact (prop_ext (fun h4 : term241 a b n => @lem209347 a b n h1 h2 h3) (fun h4 : False => @lem209020 a b n h3)). Qed.
Lemma lem209516 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) (h3 : term241 a b n) : False.
Proof. exact (EQ_MP (@lem209515 a b n h1 h2 h3) (@lem209020 a b n h3)). Qed.
Lemma lem209517 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) (h3 : term241 a b n) : (term75 n) = False.
Proof. exact (prop_ext (fun h4 : term75 n => @lem209516 a b n h1 h2 h3) (fun h4 : False => @lem209018 n h2)). Qed.
Lemma lem209518 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) (h3 : term241 a b n) : False.
Proof. exact (EQ_MP (@lem209517 a b n h1 h2 h3) (@lem209018 n h2)). Qed.
Lemma lem209519 (b : nat) (n : nat) (h1 : term202) (h2 : term242 b n) (h3 : term75 n) : (term242 b n) = False.
Proof. exact (prop_ext (fun h4 : term242 b n => @lem209514 b n h1 h2 h3) (fun h4 : False => @lem209000 b n h2)). Qed.
Lemma lem209520 (b : nat) (n : nat) (h1 : term202) (h2 : term242 b n) (h3 : term75 n) : False.
Proof. exact (EQ_MP (@lem209519 b n h1 h2 h3) (@lem209000 b n h2)). Qed.
Lemma lem209521 (b : nat) (n : nat) (h1 : term202) (h2 : term242 b n) (h3 : term75 n) : (term75 n) = False.
Proof. exact (prop_ext (fun h4 : term75 n => @lem209520 b n h1 h2 h3) (fun h4 : False => @lem208970 n h3)). Qed.
Lemma lem209522 (b : nat) (n : nat) (h1 : term202) (h2 : term242 b n) (h3 : term75 n) : False.
Proof. exact (EQ_MP (@lem209521 b n h1 h2 h3) (@lem208970 n h3)). Qed.
Lemma lem209523 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) (h3 : term241 a b n) : (term241 a b n) = False.
Proof. exact (prop_ext (fun h4 : term241 a b n => @lem209518 a b n h1 h2 h3) (fun h4 : False => @lem208966 a b n h3)). Qed.
Lemma lem209524 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) (h3 : term241 a b n) : False.
Proof. exact (EQ_MP (@lem209523 a b n h1 h2 h3) (@lem208966 a b n h3)). Qed.
Lemma lem209525 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) (h3 : term241 a b n) : (term75 n) = False.
Proof. exact (prop_ext (fun h4 : term75 n => @lem209524 a b n h1 h2 h3) (fun h4 : False => @lem208936 n h2)). Qed.
Lemma lem209526 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) (h3 : term241 a b n) : False.
Proof. exact (EQ_MP (@lem209525 a b n h1 h2 h3) (@lem208936 n h2)). Qed.
Lemma lem209527 (b : nat) (n : nat) (h1 : term202) (h2 : term242 b n) (h3 : term75 n) : (term242 b n) = False.
Proof. exact (prop_ext (fun h4 : term242 b n => @lem209522 b n h1 h2 h3) (fun h4 : False => @lem209000 b n h2)). Qed.
Lemma lem209528 (b : nat) (n : nat) (h1 : term202) (h2 : term242 b n) (h3 : term75 n) : False.
Proof. exact (EQ_MP (@lem209527 b n h1 h2 h3) (@lem209000 b n h2)). Qed.
Lemma lem209529 (b : nat) (n : nat) (h1 : term202) (h2 : term242 b n) (h3 : term75 n) : (term75 n) = False.
Proof. exact (prop_ext (fun h4 : term75 n => @lem209528 b n h1 h2 h3) (fun h4 : False => @lem208970 n h3)). Qed.
Lemma lem209530 (b : nat) (n : nat) (h1 : term202) (h2 : term242 b n) (h3 : term75 n) : False.
Proof. exact (EQ_MP (@lem209529 b n h1 h2 h3) (@lem208970 n h3)). Qed.
Lemma lem209531 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) (h3 : term241 a b n) : (term241 a b n) = False.
Proof. exact (prop_ext (fun h4 : term241 a b n => @lem209526 a b n h1 h2 h3) (fun h4 : False => @lem208966 a b n h3)). Qed.
Lemma lem209532 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) (h3 : term241 a b n) : False.
Proof. exact (EQ_MP (@lem209531 a b n h1 h2 h3) (@lem208966 a b n h3)). Qed.
Lemma lem209533 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) (h3 : term241 a b n) : (term75 n) = False.
Proof. exact (prop_ext (fun h4 : term75 n => @lem209532 a b n h1 h2 h3) (fun h4 : False => @lem208936 n h2)). Qed.
Lemma lem209534 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term75 n) (h3 : term241 a b n) : False.
Proof. exact (EQ_MP (@lem209533 a b n h1 h2 h3) (@lem208936 n h2)). Qed.
Lemma lem209535 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term195 a b n) (h3 : term75 n) : False.
Proof. exact (or_elim (@lem208880 a b n h2) (fun h0 : term241 a b n => @lem209534 a b n h1 h3 h0) (fun h0 : term242 b n => @lem209530 b n h1 h0 h3)). Qed.
Lemma lem209536 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term195 a b n) (h3 : term75 n) : (term75 n) = False.
Proof. exact (prop_ext (fun h4 : term75 n => @lem209535 a b n h1 h2 h3) (fun h4 : False => @lem208826 n h3)). Qed.
Lemma lem209537 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term195 a b n) (h3 : term75 n) : False.
Proof. exact (EQ_MP (@lem209536 a b n h1 h2 h3) (@lem208826 n h3)). Qed.
Lemma lem209538 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term195 a b n) (h3 : term75 n) : (term75 n) = False.
Proof. exact (prop_ext (fun h4 : term75 n => @lem209537 a b n h1 h2 h3) (fun h4 : False => @lem208728 n h3)). Qed.
Lemma lem209539 (a : nat) (b : nat) (n : nat) (h1 : term202) (h2 : term195 a b n) (h3 : term75 n) : False.
Proof. exact (EQ_MP (@lem209538 a b n h1 h2 h3) (@lem208728 n h3)). Qed.
Lemma lem209540 (a : nat) (b : nat) (n : nat) (h1 : term195 a b n) (h2 : term75 n) : term200.
Proof. exact (fun h0 : term202 => @lem209539 a b n h0 h1 h2). Qed.
Lemma lem209541 : term200 = term201.
Proof. exact (@lem69 term202). Qed.
Lemma lem209542 (a : nat) (b : nat) (n : nat) (h1 : term195 a b n) (h2 : term75 n) : term201.
Proof. exact (EQ_MP (@lem209541) (@lem209540 a b n h1 h2)). Qed.
Lemma lem209543 (a : nat) (b : nat) (n : nat) (h1 : term75 n) : term205 a b n.
Proof. exact (fun h0 : term195 a b n => @lem209542 a b n h0 h1). Qed.
Lemma lem209544 (a : nat) (b : nat) (n : nat) : term207 a b n.
Proof. exact (fun h0 : term75 n => @lem209543 a b n h0). Qed.
Lemma lem209549 (b : nat) (n : nat) : term211 b n.
Proof. exact (fun a : nat => @lem209544 a b n). Qed.
Lemma lem209554 (n : nat) : term215 n.
Proof. exact (fun b : nat => @lem209549 b n). Qed.
Lemma lem209559 : term219.
Proof. exact (fun n : nat => @lem209554 n). Qed.
Lemma lem209560 : term218.
Proof. exact (EQ_MP (@lem208719) (@lem209559)). Qed.
Lemma lem209561 (n : nat) : term297 n.
Proof. exact (@lem209560 n). Qed.
Lemma lem209562 (n : nat) : (term297 n) = (term214 n).
Proof. exact (eq_refl (term297 n)). Qed.
Lemma lem209563 (n : nat) : term214 n.
Proof. exact (EQ_MP (@lem209562 n) (@lem209561 n)). Qed.
Lemma lem209564 (n : nat) (b : nat) : term298 n b.
Proof. exact (@lem209563 n b). Qed.
Lemma lem209565 (b : nat) (n : nat) : (term298 n b) = (term210 b n).
Proof. exact (eq_refl (term298 n b)). Qed.
Lemma lem209566 (b : nat) (n : nat) : term210 b n.
Proof. exact (EQ_MP (@lem209565 b n) (@lem209564 n b)). Qed.
Lemma lem209567 (b : nat) (n : nat) (a : nat) : term299 b n a.
Proof. exact (@lem209566 b n a). Qed.
Lemma lem209568 (a : nat) (b : nat) (n : nat) : (term299 b n a) = (term196 a b n).
Proof. exact (eq_refl (term299 b n a)). Qed.
Lemma lem209569 (a : nat) (b : nat) (n : nat) : term196 a b n.
Proof. exact (EQ_MP (@lem209568 a b n) (@lem209567 b n a)). Qed.
Lemma lem209571 (a : nat) (b : nat) (n : nat) : term196 a b n.
Proof. exact (@lem208565 a b n (@lem209569 a b n)). Qed.
Lemma lem209572 (a : nat) (b : nat) (n : nat) (h1 : term75 n) : term204 a b n.
Proof. exact (@lem209571 a b n (@lem208516 n h1)). Qed.
Lemma lem209573 (a : nat) (b : nat) (n : nat) (h1 : term195 a b n) (h2 : term75 n) : term200.
Proof. exact (@lem209572 a b n h2 (@lem208550 a b n h1)). Qed.
Lemma lem209574 (a : nat) (b : nat) (n : nat) (h1 : term195 a b n) (h2 : term75 n) : False.
Proof. exact (@lem209573 a b n h1 h2 (@lem157261)). Qed.
Lemma lem209575 (a : nat) (b : nat) (n : nat) (h1 : term195 a b n) (h2 : term75 n) : (term195 a b n) = False.
Proof. exact (prop_ext (fun h3 : term195 a b n => @lem209574 a b n h1 h2) (fun h3 : False => @lem208550 a b n h1)). Qed.
Lemma lem209576 (a : nat) (b : nat) (n : nat) (h1 : term195 a b n) (h2 : term75 n) : False.
Proof. exact (EQ_MP (@lem209575 a b n h1 h2) (@lem208550 a b n h1)). Qed.
Lemma lem209577 (a : nat) (b : nat) (n : nat) (h1 : term75 n) : term194 a b n.
Proof. exact (fun h0 : term195 a b n => @lem209576 a b n h0 h1). Qed.
Lemma lem209578 (a : nat) (b : nat) (n : nat) (h1 : term75 n) : term192 a b n.
Proof. exact (EQ_MP (@lem208549 a b n) (@lem209577 a b n h1)). Qed.
Lemma lem209579 (a : nat) (b : nat) (n : nat) (h1 : term75 n) : term191 a b n.
Proof. exact (EQ_MP (@lem208545 a b n) (@lem209578 a b n h1)). Qed.
Lemma lem209580 (a : nat) (b : nat) (n : nat) (h1 : term75 n) : term300 a b n.
Proof. exact (ex_intro (term301 a b n) (Nat.modulo b n) (@lem209579 a b n h1)). Qed.
Lemma lem209581 (a : nat) (b : nat) (n : nat) (h1 : term75 n) : (term76 a b n) = (term77 a b n).
Proof. exact (@lem208519 a b n (@lem209580 a b n h1)). Qed.
Lemma lem209582 (a : nat) (b : nat) (n : nat) (h1 : term75 n) : (term75 n) = ((term76 a b n) = (term77 a b n)).
Proof. exact (prop_ext (fun h2 : term75 n => @lem209581 a b n h1) (fun h2 : (term76 a b n) = (term77 a b n) => @lem208516 n h1)). Qed.
Lemma lem209583 (a : nat) (b : nat) (n : nat) (h1 : term75 n) : (term76 a b n) = (term77 a b n).
Proof. exact (EQ_MP (@lem209582 a b n h1) (@lem208516 n h1)). Qed.
Lemma lem209584 (a : nat) (b : nat) (n : nat) : term93 a b n.
Proof. exact (fun h0 : term75 n => @lem209583 a b n h0). Qed.
Lemma lem209589 (a : nat) (b : nat) : term97 a b.
Proof. exact (fun n : nat => @lem209584 a b n). Qed.
Lemma lem209594 (a : nat) : term101 a.
Proof. exact (fun b : nat => @lem209589 a b). Qed.
Lemma lem209599 : term64.
Proof. exact (fun a : nat => @lem209594 a). Qed.
Lemma lem209600 : term302.
Proof. exact (conj (@lem208515) (@lem209599)). Qed.
Lemma lem209601 : term303.
Proof. exact (@lem207506 (@lem209600)). Qed.
