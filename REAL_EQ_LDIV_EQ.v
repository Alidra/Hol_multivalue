Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_LDIV_EQ_term_abbrevs.
Require Import REAL_LE_LDIV_EQ_spec.
Require Import REAL_LE_RDIV_EQ_spec.
Require Import thm0_spec.
Require Import thm1339379_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem1629271 (x : real) : term0 x.
Proof. exact (@lem1628775 x). Qed.
Lemma lem1629272 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1629273 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1629272 x) (@lem1629271 x)). Qed.
Lemma lem1629274 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1629273 x y). Qed.
Lemma lem1629275 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1629276 (x : real) (y : real) : term3 x y.
Proof. exact (EQ_MP (@lem1629275 x y) (@lem1629274 x y)). Qed.
Lemma lem1629277 (x : real) (y : real) (z : real) : term4 x y z.
Proof. exact (@lem1629276 x y z). Qed.
Lemma lem1629278 (x : real) (y : real) (z : real) : (term4 x y z) = (term5 x y z).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem1629279 (x : real) (y : real) (z : real) : term5 x y z.
Proof. exact (EQ_MP (@lem1629278 x y z) (@lem1629277 x y z)). Qed.
Lemma lem1629280 (z : real) (h1 : term6 z) : term6 z.
Proof. exact (h1). Qed.
Lemma lem1629281 (x : real) (y : real) (z : real) (h1 : term6 z) : (term7 x z y) = (term8 x y z).
Proof. exact (@lem1629279 x y z (@lem1629280 z h1)). Qed.
Lemma lem1629287 (x : real) : term9 x.
Proof. exact (@lem1628574 x). Qed.
Lemma lem1629288 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1629289 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem1629288 x) (@lem1629287 x)). Qed.
Lemma lem1629290 (x : real) (y : real) : term11 x y.
Proof. exact (@lem1629289 x y). Qed.
Lemma lem1629291 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1629292 (x : real) (y : real) : term12 x y.
Proof. exact (EQ_MP (@lem1629291 x y) (@lem1629290 x y)). Qed.
Lemma lem1629293 (x : real) (y : real) (z : real) : term13 x y z.
Proof. exact (@lem1629292 x y z). Qed.
Lemma lem1629294 (x : real) (z : real) (y : real) : (term13 x y z) = (term14 x z y).
Proof. exact (eq_refl (term13 x y z)). Qed.
Lemma lem1629295 (x : real) (z : real) (y : real) : term14 x z y.
Proof. exact (EQ_MP (@lem1629294 x z y) (@lem1629293 x y z)). Qed.
Lemma lem1629296 (z : real) (h1 : term6 z) : term6 z.
Proof. exact (h1). Qed.
Lemma lem1629297 (x : real) (y : real) (z : real) (h1 : term6 z) : (term15 x y z) = (term16 x z y).
Proof. exact (@lem1629295 x z y (@lem1629296 z h1)). Qed.
Lemma lem1629305 (x : real) (y : real) (h1 : (term17 y x) = (x = y)) : (term17 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem1629306 (x : real) (y : real) (h1 : (term17 y x) = (x = y)) : (x = y) = (term17 y x).
Proof. exact (SYM (@lem1629305 x y h1)). Qed.
Lemma lem1629307 (y : real) (x : real) (h1 : (x = y) = (term17 y x)) : (x = y) = (term17 y x).
Proof. exact (h1). Qed.
Lemma lem1629308 (y : real) (x : real) (h1 : (x = y) = (term17 y x)) : (term17 y x) = (x = y).
Proof. exact (SYM (@lem1629307 y x h1)). Qed.
Lemma lem1629309 (y : real) (x : real) : ((term17 y x) = (x = y)) = ((x = y) = (term17 y x)).
Proof. exact (prop_ext (fun h1 : (term17 y x) = (x = y) => @lem1629306 x y h1) (fun h1 : (x = y) = (term17 y x) => @lem1629308 y x h1)). Qed.
Lemma lem1629310 (x : real) : (term18 x) = (term19 x).
Proof. exact (fun_ext (fun y : real => @lem1629309 y x)). Qed.
Lemma lem1629311 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629312 (x : real) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem1629311) (@lem1629310 x)). Qed.
Lemma lem1629313 : term22 = term23.
Proof. exact (fun_ext (fun x : real => @lem1629312 x)). Qed.
Lemma lem1629314 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629315 : term24 = term25.
Proof. exact (MK_COMB (@lem1629314) (@lem1629313)). Qed.
Lemma lem1629316 : term25.
Proof. exact (EQ_MP (@lem1629315) (@lem1339379)). Qed.
Lemma lem1629317 (x : real) : term26 x.
Proof. exact (@lem1629316 x). Qed.
Lemma lem1629318 (x : real) : (term26 x) = (term21 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1629319 (x : real) : term21 x.
Proof. exact (EQ_MP (@lem1629318 x) (@lem1629317 x)). Qed.
Lemma lem1629320 (x : real) (y : real) : term27 x y.
Proof. exact (@lem1629319 x y). Qed.
Lemma lem1629321 (y : real) (x : real) : (term27 x y) = ((x = y) = (term17 y x)).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1629344 (y : real) (x : real) : (x = y) = (term17 y x).
Proof. exact (EQ_MP (@lem1629321 y x) (@lem1629320 x y)). Qed.
Lemma lem1629345 (y : real) (x : real) (z : real) : ((real_div x z) = y) = (term28 y x z).
Proof. exact (@lem1629344 y (real_div x z)). Qed.
Lemma lem1629348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1629349 (y : real) (x : real) (z : real) : (term29 x z y) = (term30 y x z).
Proof. exact (MK_COMB (@lem1629348) (@lem1629345 y x z)). Qed.
Lemma lem1629353 (y : real) (x : real) : (x = y) = (term17 y x).
Proof. exact (EQ_MP (@lem1629321 y x) (@lem1629320 x y)). Qed.
Lemma lem1629354 (y : real) (z : real) (x : real) : (x = (real_mul y z)) = (term31 y z x).
Proof. exact (@lem1629353 (real_mul y z) x). Qed.
Lemma lem1629357 (y : real) (z : real) (x : real) : (((real_div x z) = y) = (x = (real_mul y z))) = ((term28 y x z) = (term31 y z x)).
Proof. exact (MK_COMB (@lem1629349 y x z) (@lem1629354 y z x)). Qed.
Lemma lem1629362 (z : real) : (term32 z) = (term32 z).
Proof. exact (eq_refl (term32 z)). Qed.
Lemma lem1629363 (y : real) (z : real) (x : real) : (term33 x y z) = (term34 y z x).
Proof. exact (MK_COMB (@lem1629362 z) (@lem1629357 y z x)). Qed.
Lemma lem1629366 (y : real) (x : real) : (term35 x y) = (term36 y x).
Proof. exact (fun_ext (fun z : real => @lem1629363 y z x)). Qed.
Lemma lem1629367 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629368 (y : real) (x : real) : (term37 x y) = (term38 y x).
Proof. exact (MK_COMB (@lem1629367) (@lem1629366 y x)). Qed.
Lemma lem1629373 (x : real) : (term39 x) = (term40 x).
Proof. exact (fun_ext (fun y : real => @lem1629368 y x)). Qed.
Lemma lem1629374 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629375 (x : real) : (term41 x) = (term42 x).
Proof. exact (MK_COMB (@lem1629374) (@lem1629373 x)). Qed.
Lemma lem1629380 : term43 = term44.
Proof. exact (fun_ext (fun x : real => @lem1629375 x)). Qed.
Lemma lem1629381 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629382 : term45 = term46.
Proof. exact (MK_COMB (@lem1629381) (@lem1629380)). Qed.
Lemma lem1629387 : term46 = term45.
Proof. exact (SYM (@lem1629382)). Qed.
Lemma lem1629403 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term47 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1629404 (p : Prop) (q : Prop) (p' : Prop) : term48 p q p'.
Proof. exact (fun q' : Prop => @lem1629403 p q p' q'). Qed.
Lemma lem1629405 (p : Prop) (q : Prop) : term49 p q.
Proof. exact (fun p' : Prop => @lem1629404 p q p'). Qed.
Lemma lem1629406 (y : real) (z : real) (x : real) : term50 y z x.
Proof. exact (@lem1629405 (term6 z) ((term28 y x z) = (term31 y z x))). Qed.
Lemma lem1629407 (y : real) (z : real) (x : real) (p' : Prop) : term51 y z x p'.
Proof. exact (@lem1629406 y z x p'). Qed.
Lemma lem1629408 (y : real) (z : real) (x : real) (p' : Prop) : (term51 y z x p') = (term52 y z x p').
Proof. exact (eq_refl (term51 y z x p')). Qed.
Lemma lem1629409 (y : real) (z : real) (x : real) (p' : Prop) : term52 y z x p'.
Proof. exact (EQ_MP (@lem1629408 y z x p') (@lem1629407 y z x p')). Qed.
Lemma lem1629410 (y : real) (z : real) (x : real) (p' : Prop) (q' : Prop) : term53 y z x p' q'.
Proof. exact (@lem1629409 y z x p' q'). Qed.
Lemma lem1629411 (y : real) (z : real) (x : real) (p' : Prop) (q' : Prop) : (term53 y z x p' q') = (term54 y z x p' q').
Proof. exact (eq_refl (term53 y z x p' q')). Qed.
Lemma lem1629412 (y : real) (z : real) (x : real) (p' : Prop) (q' : Prop) : term54 y z x p' q'.
Proof. exact (EQ_MP (@lem1629411 y z x p' q') (@lem1629410 y z x p' q')). Qed.
Lemma lem1629413 (z : real) : (term6 z) = (term6 z).
Proof. exact (eq_refl (term6 z)). Qed.
Lemma lem1629414 (y : real) (x : real) (z : real) (q' : Prop) : term55 y x z q'.
Proof. exact (@lem1629412 y z x (term6 z) q'). Qed.
Lemma lem1629415 (y : real) (x : real) (z : real) (q' : Prop) : term56 y x z q'.
Proof. exact (@lem1629414 y x z q' (@lem1629413 z)). Qed.
Lemma lem1629416 (z : real) (h1 : term6 z) : term6 z.
Proof. exact (h1). Qed.
Lemma lem1629417 (z : real) : (term6 z) = ((term6 z) = True).
Proof. exact (@lem7 (term6 z)). Qed.
Lemma lem1629424 (x : real) (y : real) (z : real) : term5 x y z.
Proof. exact (fun h0 : term6 z => @lem1629281 x y z h0). Qed.
Lemma lem1629426 (z : real) (h1 : term6 z) : (term6 z) = True.
Proof. exact (EQ_MP (@lem1629417 z) (@lem1629416 z h1)). Qed.
Lemma lem1629427 (z : real) (h1 : term6 z) : True = (term6 z).
Proof. exact (SYM (@lem1629426 z h1)). Qed.
Lemma lem1629428 (z : real) (h1 : term6 z) : term6 z.
Proof. exact (EQ_MP (@lem1629427 z h1) (@lem0)). Qed.
Lemma lem1629429 (x : real) (y : real) (z : real) (h1 : term6 z) : (term7 x z y) = (term8 x y z).
Proof. exact (@lem1629424 x y z (@lem1629428 z h1)). Qed.
Lemma lem1629430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1629431 (x : real) (y : real) (z : real) (h1 : term6 z) : (term57 x z y) = (term58 x y z).
Proof. exact (MK_COMB (@lem1629430) (@lem1629429 x y z h1)). Qed.
Lemma lem1629433 (x : real) (z : real) (y : real) : term14 x z y.
Proof. exact (fun h0 : term6 z => @lem1629297 x y z h0). Qed.
Lemma lem1629434 (y : real) (z : real) (x : real) : term14 y z x.
Proof. exact (@lem1629433 y z x). Qed.
Lemma lem1629436 (z : real) (h1 : term6 z) : (term6 z) = True.
Proof. exact (EQ_MP (@lem1629417 z) (@lem1629416 z h1)). Qed.
Lemma lem1629437 (z : real) (h1 : term6 z) : True = (term6 z).
Proof. exact (SYM (@lem1629436 z h1)). Qed.
Lemma lem1629438 (z : real) (h1 : term6 z) : term6 z.
Proof. exact (EQ_MP (@lem1629437 z h1) (@lem0)). Qed.
Lemma lem1629439 (y : real) (x : real) (z : real) (h1 : term6 z) : (term15 y x z) = (term16 y z x).
Proof. exact (@lem1629434 y z x (@lem1629438 z h1)). Qed.
Lemma lem1629440 (y : real) (x : real) (z : real) (h1 : term6 z) : (term28 y x z) = (term31 y z x).
Proof. exact (MK_COMB (@lem1629431 x y z h1) (@lem1629439 y x z h1)). Qed.
Lemma lem1629443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1629444 (y : real) (x : real) (z : real) (h1 : term6 z) : (term30 y x z) = (term59 y z x).
Proof. exact (MK_COMB (@lem1629443) (@lem1629440 y x z h1)). Qed.
Lemma lem1629449 (y : real) (z : real) (x : real) : (term31 y z x) = (term31 y z x).
Proof. exact (eq_refl (term31 y z x)). Qed.
Lemma lem1629450 (y : real) (x : real) (z : real) (h1 : term6 z) : ((term28 y x z) = (term31 y z x)) = ((term31 y z x) = (term31 y z x)).
Proof. exact (MK_COMB (@lem1629444 y x z h1) (@lem1629449 y z x)). Qed.
Lemma lem1629452 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1629453 (x : Prop) : (x = x) = True.
Proof. exact (@lem1629452 Prop x). Qed.
Lemma lem1629454 (y : real) (z : real) (x : real) : ((term31 y z x) = (term31 y z x)) = True.
Proof. exact (@lem1629453 (term31 y z x)). Qed.
Lemma lem1629455 (y : real) (x : real) (z : real) (h1 : term6 z) : ((term28 y x z) = (term31 y z x)) = True.
Proof. exact (TRANS (@lem1629450 y x z h1) (@lem1629454 y z x)). Qed.
Lemma lem1629456 (y : real) (z : real) (x : real) : term60 y z x.
Proof. exact (fun h0 : term6 z => @lem1629455 y x z h0). Qed.
Lemma lem1629457 (y : real) (x : real) (z : real) : term61 y x z.
Proof. exact (@lem1629415 y x z True). Qed.
Lemma lem1629458 (y : real) (x : real) (z : real) : (term34 y z x) = (term62 z).
Proof. exact (@lem1629457 y x z (@lem1629456 y z x)). Qed.
Lemma lem1629460 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1629461 (z : real) : (term62 z) = True.
Proof. exact (@lem1629460 (term6 z)). Qed.
Lemma lem1629462 (y : real) (z : real) (x : real) : (term34 y z x) = True.
Proof. exact (TRANS (@lem1629458 y x z) (@lem1629461 z)). Qed.
Lemma lem1629463 (y : real) (x : real) : (term36 y x) = term63.
Proof. exact (fun_ext (fun z : real => @lem1629462 y z x)). Qed.
Lemma lem1629464 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629465 (y : real) (x : real) : (term38 y x) = term64.
Proof. exact (MK_COMB (@lem1629464) (@lem1629463 y x)). Qed.
Lemma lem1629467 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1629468 (t : Prop) : (term66 t) = t.
Proof. exact (@lem1629467 real t). Qed.
Lemma lem1629469 : term64 = True.
Proof. exact (@lem1629468 True). Qed.
Lemma lem1629470 (y : real) (x : real) : (term38 y x) = True.
Proof. exact (TRANS (@lem1629465 y x) (@lem1629469)). Qed.
Lemma lem1629471 (x : real) : (term40 x) = term63.
Proof. exact (fun_ext (fun y : real => @lem1629470 y x)). Qed.
Lemma lem1629472 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629473 (x : real) : (term42 x) = term64.
Proof. exact (MK_COMB (@lem1629472) (@lem1629471 x)). Qed.
Lemma lem1629475 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1629476 (t : Prop) : (term66 t) = t.
Proof. exact (@lem1629475 real t). Qed.
Lemma lem1629477 : term64 = True.
Proof. exact (@lem1629476 True). Qed.
Lemma lem1629478 (x : real) : (term42 x) = True.
Proof. exact (TRANS (@lem1629473 x) (@lem1629477)). Qed.
Lemma lem1629479 : term44 = term63.
Proof. exact (fun_ext (fun x : real => @lem1629478 x)). Qed.
Lemma lem1629480 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1629481 : term46 = term64.
Proof. exact (MK_COMB (@lem1629480) (@lem1629479)). Qed.
Lemma lem1629483 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1629484 (t : Prop) : (term66 t) = t.
Proof. exact (@lem1629483 real t). Qed.
Lemma lem1629485 : term64 = True.
Proof. exact (@lem1629484 True). Qed.
Lemma lem1629486 : term46 = True.
Proof. exact (TRANS (@lem1629481) (@lem1629485)). Qed.
Lemma lem1629487 : True = term46.
Proof. exact (SYM (@lem1629486)). Qed.
Lemma lem1629488 : term46.
Proof. exact (EQ_MP (@lem1629487) (@lem0)). Qed.
Lemma lem1629489 : term45.
Proof. exact (EQ_MP (@lem1629387) (@lem1629488)). Qed.
