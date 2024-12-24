Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_LE2_term_abbrevs.
Require Import REAL_LE_MUL2_spec.
Require Import REAL_POW_LE_spec.
Require Import thm0_spec.
Require Import thm1339240_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1636367 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1636368 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1636367 h1 x). Qed.
Lemma lem1636369 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1636370 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1636369 x) (@lem1636368 x h1)). Qed.
Lemma lem1636371 (x : real) (n : nat) (h1 : term0) : term3 x n.
Proof. exact (@lem1636370 x h1 n). Qed.
Lemma lem1636372 (x : real) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (eq_refl (term3 x n)). Qed.
Lemma lem1636373 (x : real) (n : nat) (h1 : term0) : term4 x n.
Proof. exact (EQ_MP (@lem1636372 x n) (@lem1636371 x n h1)). Qed.
Lemma lem1636374 (x : real) (h1 : term5 x) : term5 x.
Proof. exact (h1). Qed.
Lemma lem1636375 (n : nat) (x : real) (h1 : term0) (h2 : term5 x) : term6 x n.
Proof. exact (@lem1636373 x n h1 (@lem1636374 x h2)). Qed.
Lemma lem1636376 (n : nat) (x : real) (h1 : term5 x) : term7 x n.
Proof. exact (fun h0 : term0 => @lem1636375 n x h0 h1). Qed.
Lemma lem1636377 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1636378 (n : nat) (x : real) (h1 : term0) (h2 : term5 x) : term6 x n.
Proof. exact (@lem1636376 n x h2 (@lem1636377 h1)). Qed.
Lemma lem1636379 (x : real) (n : nat) (h1 : term0) : term4 x n.
Proof. exact (fun h0 : term5 x => @lem1636378 n x h1 h0). Qed.
Lemma lem1636380 (x : real) (h1 : term0) : term2 x.
Proof. exact (fun n : nat => @lem1636379 x n h1). Qed.
Lemma lem1636381 (h1 : term0) : term0.
Proof. exact (fun x : real => @lem1636380 x h1). Qed.
Lemma lem1636382 : term8.
Proof. exact (fun h0 : term0 => @lem1636381 h0). Qed.
Lemma lem1636383 : term0.
Proof. exact (@lem1636382 (@lem1582434)). Qed.
Lemma lem1636384 (x : real) : term1 x.
Proof. exact (@lem1636383 x). Qed.
Lemma lem1636385 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1636386 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1636385 x) (@lem1636384 x)). Qed.
Lemma lem1636387 (x : real) (n : nat) : term3 x n.
Proof. exact (@lem1636386 x n). Qed.
Lemma lem1636388 (x : real) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (eq_refl (term3 x n)). Qed.
Lemma lem1636390 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem1636391 (w : real) (h1 : term9) : term10 w.
Proof. exact (@lem1636390 h1 w). Qed.
Lemma lem1636392 (w : real) : (term10 w) = (term11 w).
Proof. exact (eq_refl (term10 w)). Qed.
Lemma lem1636393 (w : real) (h1 : term9) : term11 w.
Proof. exact (EQ_MP (@lem1636392 w) (@lem1636391 w h1)). Qed.
Lemma lem1636394 (w : real) (x : real) (h1 : term9) : term12 w x.
Proof. exact (@lem1636393 w h1 x). Qed.
Lemma lem1636395 (w : real) (x : real) : (term12 w x) = (term13 w x).
Proof. exact (eq_refl (term12 w x)). Qed.
Lemma lem1636396 (w : real) (x : real) (h1 : term9) : term13 w x.
Proof. exact (EQ_MP (@lem1636395 w x) (@lem1636394 w x h1)). Qed.
Lemma lem1636397 (w : real) (x : real) (y : real) (h1 : term9) : term14 w x y.
Proof. exact (@lem1636396 w x h1 y). Qed.
Lemma lem1636398 (w : real) (y : real) (x : real) : (term14 w x y) = (term15 w y x).
Proof. exact (eq_refl (term14 w x y)). Qed.
Lemma lem1636399 (w : real) (y : real) (x : real) (h1 : term9) : term15 w y x.
Proof. exact (EQ_MP (@lem1636398 w y x) (@lem1636397 w x y h1)). Qed.
Lemma lem1636400 (w : real) (y : real) (x : real) (z : real) (h1 : term9) : term16 w y x z.
Proof. exact (@lem1636399 w y x h1 z). Qed.
Lemma lem1636401 (w : real) (y : real) (x : real) (z : real) : (term16 w y x z) = (term17 w y x z).
Proof. exact (eq_refl (term16 w y x z)). Qed.
Lemma lem1636402 (w : real) (y : real) (x : real) (z : real) (h1 : term9) : term17 w y x z.
Proof. exact (EQ_MP (@lem1636401 w y x z) (@lem1636400 w y x z h1)). Qed.
Lemma lem1636403 (w : real) (x : real) (y : real) (z : real) (h1 : term18 w x y z) : term18 w x y z.
Proof. exact (h1). Qed.
Lemma lem1636404 (w : real) (x : real) (y : real) (z : real) (h1 : term9) (h2 : term18 w x y z) : term19 w y x z.
Proof. exact (@lem1636402 w y x z h1 (@lem1636403 w x y z h2)). Qed.
Lemma lem1636405 (w : real) (x : real) (y : real) (z : real) (h1 : term18 w x y z) : term20 w y x z.
Proof. exact (fun h0 : term9 => @lem1636404 w x y z h0 h1). Qed.
Lemma lem1636406 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem1636407 (w : real) (x : real) (y : real) (z : real) (h1 : term9) (h2 : term18 w x y z) : term19 w y x z.
Proof. exact (@lem1636405 w x y z h2 (@lem1636406 h1)). Qed.
Lemma lem1636408 (w : real) (y : real) (x : real) (z : real) (h1 : term9) : term17 w y x z.
Proof. exact (fun h0 : term18 w x y z => @lem1636407 w x y z h1 h0). Qed.
Lemma lem1636409 (w : real) (y : real) (x : real) (h1 : term9) : term15 w y x.
Proof. exact (fun z : real => @lem1636408 w y x z h1). Qed.
Lemma lem1636410 (w : real) (y : real) (h1 : term9) : term21 w y.
Proof. exact (fun x : real => @lem1636409 w y x h1). Qed.
Lemma lem1636411 (w : real) (h1 : term9) : term22 w.
Proof. exact (fun y : real => @lem1636410 w y h1). Qed.
Lemma lem1636412 (h1 : term9) : term23.
Proof. exact (fun w : real => @lem1636411 w h1). Qed.
Lemma lem1636413 : term24.
Proof. exact (fun h0 : term9 => @lem1636412 h0). Qed.
Lemma lem1636414 : term23.
Proof. exact (@lem1636413 (@lem1630540)). Qed.
Lemma lem1636415 (w : real) : term25 w.
Proof. exact (@lem1636414 w). Qed.
Lemma lem1636416 (w : real) : (term25 w) = (term22 w).
Proof. exact (eq_refl (term25 w)). Qed.
Lemma lem1636417 (w : real) : term22 w.
Proof. exact (EQ_MP (@lem1636416 w) (@lem1636415 w)). Qed.
Lemma lem1636418 (w : real) (y : real) : term26 w y.
Proof. exact (@lem1636417 w y). Qed.
Lemma lem1636419 (w : real) (y : real) : (term26 w y) = (term21 w y).
Proof. exact (eq_refl (term26 w y)). Qed.
Lemma lem1636420 (w : real) (y : real) : term21 w y.
Proof. exact (EQ_MP (@lem1636419 w y) (@lem1636418 w y)). Qed.
Lemma lem1636421 (w : real) (y : real) (x : real) : term27 w y x.
Proof. exact (@lem1636420 w y x). Qed.
Lemma lem1636422 (w : real) (y : real) (x : real) : (term27 w y x) = (term15 w y x).
Proof. exact (eq_refl (term27 w y x)). Qed.
Lemma lem1636423 (w : real) (y : real) (x : real) : term15 w y x.
Proof. exact (EQ_MP (@lem1636422 w y x) (@lem1636421 w y x)). Qed.
Lemma lem1636424 (w : real) (y : real) (x : real) (z : real) : term16 w y x z.
Proof. exact (@lem1636423 w y x z). Qed.
Lemma lem1636425 (w : real) (y : real) (x : real) (z : real) : (term16 w y x z) = (term17 w y x z).
Proof. exact (eq_refl (term16 w y x z)). Qed.
Lemma lem1636427 (x : real) : term28 x.
Proof. exact (@lem1339240 x). Qed.
Lemma lem1636428 (x : real) : (term28 x) = (real_le x x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1636429 (x : real) : real_le x x.
Proof. exact (EQ_MP (@lem1636428 x) (@lem1636427 x)). Qed.
Lemma lem1636430 (x : real) : (real_le x x) = ((real_le x x) = True).
Proof. exact (@lem7 (real_le x x)). Qed.
Lemma lem1636432 (x : real) : term29 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1636433 (x : real) (n : nat) : term30 x n.
Proof. exact (@lem1636432 x n). Qed.
Lemma lem1636434 (x : real) (n : nat) : (term30 x n) = ((term31 x n) = (term32 x n)).
Proof. exact (eq_refl (term30 x n)). Qed.
Lemma lem1636438 (P : nat -> Prop) : term33 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1636439 : term34.
Proof. exact (@lem1636438 term35). Qed.
Lemma lem1636440 : term36 = term37.
Proof. exact (eq_refl term36). Qed.
Lemma lem1636441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1636442 : term38 = term39.
Proof. exact (MK_COMB (@lem1636441) (@lem1636440)). Qed.
Lemma lem1636443 (n : nat) : (term40 n) = (term41 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem1636444 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1636445 (n : nat) : (term42 n) = (term43 n).
Proof. exact (MK_COMB (@lem1636444) (@lem1636443 n)). Qed.
Lemma lem1636446 (n : nat) : (term44 n) = (term45 n).
Proof. exact (eq_refl (term44 n)). Qed.
Lemma lem1636447 (n : nat) : (term46 n) = (term47 n).
Proof. exact (MK_COMB (@lem1636445 n) (@lem1636446 n)). Qed.
Lemma lem1636448 : term48 = term49.
Proof. exact (fun_ext (fun n : nat => @lem1636447 n)). Qed.
Lemma lem1636449 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1636450 : term50 = term51.
Proof. exact (MK_COMB (@lem1636449) (@lem1636448)). Qed.
Lemma lem1636451 : term52 = term53.
Proof. exact (MK_COMB (@lem1636442) (@lem1636450)). Qed.
Lemma lem1636452 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1636453 : term54 = term55.
Proof. exact (MK_COMB (@lem1636452) (@lem1636451)). Qed.
Lemma lem1636454 (n : nat) : (term40 n) = (term41 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem1636455 : term56 = term35.
Proof. exact (fun_ext (fun n : nat => @lem1636454 n)). Qed.
Lemma lem1636456 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1636457 : term57 = term58.
Proof. exact (MK_COMB (@lem1636456) (@lem1636455)). Qed.
Lemma lem1636458 : term34 = term59.
Proof. exact (MK_COMB (@lem1636453) (@lem1636457)). Qed.
Lemma lem1636459 : term59.
Proof. exact (EQ_MP (@lem1636458) (@lem1636439)). Qed.
Lemma lem1636460 (n : nat) (h1 : term41 n) : term41 n.
Proof. exact (h1). Qed.
Lemma lem1636480 (x : real) : (term60 x) = term61.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1636481 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1636482 (x : real) : (term62 x) = term63.
Proof. exact (MK_COMB (@lem1636481) (@lem1636480 x)). Qed.
Lemma lem1636484 (x : real) : (term60 x) = term61.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1636485 (y : real) : (term60 y) = term61.
Proof. exact (@lem1636484 y). Qed.
Lemma lem1636486 (x : real) (y : real) : (term64 x y) = term65.
Proof. exact (MK_COMB (@lem1636482 x) (@lem1636485 y)). Qed.
Lemma lem1636488 (x : real) : (real_le x x) = True.
Proof. exact (EQ_MP (@lem1636430 x) (@lem1636429 x)). Qed.
Lemma lem1636489 : term65 = True.
Proof. exact (@lem1636488 term61). Qed.
Lemma lem1636490 (x : real) (y : real) : (term64 x y) = True.
Proof. exact (TRANS (@lem1636486 x y) (@lem1636489)). Qed.
Lemma lem1636491 (x : real) (y : real) : (term66 x y) = (term66 x y).
Proof. exact (eq_refl (term66 x y)). Qed.
Lemma lem1636492 (x : real) (y : real) : (term67 x y) = (term68 x y).
Proof. exact (MK_COMB (@lem1636491 x y) (@lem1636490 x y)). Qed.
Lemma lem1636494 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1636495 (x : real) (y : real) : (term68 x y) = True.
Proof. exact (@lem1636494 (term69 x y)). Qed.
Lemma lem1636496 (x : real) (y : real) : (term67 x y) = True.
Proof. exact (TRANS (@lem1636492 x y) (@lem1636495 x y)). Qed.
Lemma lem1636497 (x : real) : (term70 x) = term71.
Proof. exact (fun_ext (fun y : real => @lem1636496 x y)). Qed.
Lemma lem1636498 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1636499 (x : real) : (term72 x) = term73.
Proof. exact (MK_COMB (@lem1636498) (@lem1636497 x)). Qed.
Lemma lem1636501 {A : Type'} (t : Prop) : (term74 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1636502 (t : Prop) : (term75 t) = t.
Proof. exact (@lem1636501 real t). Qed.
Lemma lem1636503 : term73 = True.
Proof. exact (@lem1636502 True). Qed.
Lemma lem1636504 (x : real) : (term72 x) = True.
Proof. exact (TRANS (@lem1636499 x) (@lem1636503)). Qed.
Lemma lem1636505 : term76 = term71.
Proof. exact (fun_ext (fun x : real => @lem1636504 x)). Qed.
Lemma lem1636506 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1636507 : term37 = term73.
Proof. exact (MK_COMB (@lem1636506) (@lem1636505)). Qed.
Lemma lem1636509 {A : Type'} (t : Prop) : (term74 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1636510 (t : Prop) : (term75 t) = t.
Proof. exact (@lem1636509 real t). Qed.
Lemma lem1636511 : term73 = True.
Proof. exact (@lem1636510 True). Qed.
Lemma lem1636512 : term37 = True.
Proof. exact (TRANS (@lem1636507) (@lem1636511)). Qed.
Lemma lem1636513 : True = term37.
Proof. exact (SYM (@lem1636512)). Qed.
Lemma lem1636514 : term37.
Proof. exact (EQ_MP (@lem1636513) (@lem0)). Qed.
Lemma lem1636534 (x : real) (n : nat) : (term31 x n) = (term32 x n).
Proof. exact (EQ_MP (@lem1636434 x n) (@lem1636433 x n)). Qed.
Lemma lem1636535 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1636536 (x : real) (n : nat) : (term77 x n) = (term78 x n).
Proof. exact (MK_COMB (@lem1636535) (@lem1636534 x n)). Qed.
Lemma lem1636538 (x : real) (n : nat) : (term31 x n) = (term32 x n).
Proof. exact (EQ_MP (@lem1636434 x n) (@lem1636433 x n)). Qed.
Lemma lem1636539 (y : real) (n : nat) : (term31 y n) = (term32 y n).
Proof. exact (@lem1636538 y n). Qed.
Lemma lem1636540 (x : real) (y : real) (n : nat) : (term79 x y n) = (term80 x y n).
Proof. exact (MK_COMB (@lem1636536 x n) (@lem1636539 y n)). Qed.
Lemma lem1636543 (x : real) (y : real) : (term66 x y) = (term66 x y).
Proof. exact (eq_refl (term66 x y)). Qed.
Lemma lem1636544 (x : real) (y : real) (n : nat) : (term81 x y n) = (term82 x y n).
Proof. exact (MK_COMB (@lem1636543 x y) (@lem1636540 x y n)). Qed.
Lemma lem1636547 (x : real) (n : nat) : (term83 x n) = (term84 x n).
Proof. exact (fun_ext (fun y : real => @lem1636544 x y n)). Qed.
Lemma lem1636548 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1636549 (x : real) (n : nat) : (term85 x n) = (term86 x n).
Proof. exact (MK_COMB (@lem1636548) (@lem1636547 x n)). Qed.
Lemma lem1636554 (n : nat) : (term87 n) = (term88 n).
Proof. exact (fun_ext (fun x : real => @lem1636549 x n)). Qed.
Lemma lem1636555 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1636556 (n : nat) : (term45 n) = (term89 n).
Proof. exact (MK_COMB (@lem1636555) (@lem1636554 n)). Qed.
Lemma lem1636561 (n : nat) : (term89 n) = (term45 n).
Proof. exact (SYM (@lem1636556 n)). Qed.
Lemma lem1636562 (x : real) (y : real) (h1 : term69 x y) : term69 x y.
Proof. exact (h1). Qed.
Lemma lem1636563 (x : real) (y : real) (h1 : real_le x y) : real_le x y.
Proof. exact (h1). Qed.
Lemma lem1636564 (x : real) (h1 : term5 x) : term5 x.
Proof. exact (h1). Qed.
Lemma lem1636566 (w : real) (y : real) (x : real) (z : real) : term17 w y x z.
Proof. exact (EQ_MP (@lem1636425 w y x z) (@lem1636424 w y x z)). Qed.
Lemma lem1636567 (x : real) (y : real) (n : nat) : term90 x y n.
Proof. exact (@lem1636566 x (real_pow x n) y (real_pow y n)). Qed.
Lemma lem1636576 (x : real) : (term5 x) = ((term5 x) = True).
Proof. exact (@lem7 (term5 x)). Qed.
Lemma lem1636578 (x : real) (y : real) : (real_le x y) = ((real_le x y) = True).
Proof. exact (@lem7 (real_le x y)). Qed.
Lemma lem1636583 (x : real) (h1 : term5 x) : (term5 x) = True.
Proof. exact (EQ_MP (@lem1636576 x) (@lem1636564 x h1)). Qed.
Lemma lem1636584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1636585 (x : real) (h1 : term5 x) : (term91 x) = (and True).
Proof. exact (MK_COMB (@lem1636584) (@lem1636583 x h1)). Qed.
Lemma lem1636589 (x : real) (y : real) (h1 : real_le x y) : (real_le x y) = True.
Proof. exact (EQ_MP (@lem1636578 x y) (@lem1636563 x y h1)). Qed.
Lemma lem1636590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1636591 (x : real) (y : real) (h1 : real_le x y) : (term92 x y) = (and True).
Proof. exact (MK_COMB (@lem1636590) (@lem1636589 x y h1)). Qed.
Lemma lem1636594 (x : real) (y : real) (n : nat) : (term93 x y n) = (term93 x y n).
Proof. exact (eq_refl (term93 x y n)). Qed.
Lemma lem1636595 (n : nat) (x : real) (y : real) (h1 : real_le x y) : (term94 x y n) = (term95 x y n).
Proof. exact (MK_COMB (@lem1636591 x y h1) (@lem1636594 x y n)). Qed.
Lemma lem1636597 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1636598 (x : real) (y : real) (n : nat) : (term95 x y n) = (term93 x y n).
Proof. exact (@lem1636597 (term93 x y n)). Qed.
Lemma lem1636601 (n : nat) (x : real) (y : real) (h1 : real_le x y) : (term94 x y n) = (term93 x y n).
Proof. exact (TRANS (@lem1636595 n x y h1) (@lem1636598 x y n)). Qed.
Lemma lem1636602 (n : nat) (y : real) (x : real) (h1 : real_le x y) (h2 : term5 x) : (term96 x y n) = (term95 x y n).
Proof. exact (MK_COMB (@lem1636585 x h2) (@lem1636601 n x y h1)). Qed.
Lemma lem1636604 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1636605 (x : real) (y : real) (n : nat) : (term95 x y n) = (term93 x y n).
Proof. exact (@lem1636604 (term93 x y n)). Qed.
Lemma lem1636608 (n : nat) (y : real) (x : real) (h1 : real_le x y) (h2 : term5 x) : (term96 x y n) = (term93 x y n).
Proof. exact (TRANS (@lem1636602 n y x h1 h2) (@lem1636605 x y n)). Qed.
Lemma lem1636609 (n : nat) (y : real) (x : real) (h1 : real_le x y) (h2 : term5 x) : (term93 x y n) = (term96 x y n).
Proof. exact (SYM (@lem1636608 n y x h1 h2)). Qed.
Lemma lem1636611 (x : real) (n : nat) : term4 x n.
Proof. exact (EQ_MP (@lem1636388 x n) (@lem1636387 x n)). Qed.
Lemma lem1636620 (x : real) : (term5 x) = ((term5 x) = True).
Proof. exact (@lem7 (term5 x)). Qed.
Lemma lem1636625 (x : real) (h1 : term5 x) : (term5 x) = True.
Proof. exact (EQ_MP (@lem1636620 x) (@lem1636564 x h1)). Qed.
Lemma lem1636626 (x : real) (h1 : term5 x) : True = (term5 x).
Proof. exact (SYM (@lem1636625 x h1)). Qed.
Lemma lem1636627 (x : real) (h1 : term5 x) : term5 x.
Proof. exact (EQ_MP (@lem1636626 x h1) (@lem0)). Qed.
Lemma lem1636628 (n : nat) (x : real) (h1 : term5 x) : term6 x n.
Proof. exact (@lem1636611 x n (@lem1636627 x h1)). Qed.
Lemma lem1636629 (n : nat) (h1 : term41 n) : term41 n.
Proof. exact (h1). Qed.
Lemma lem1636630 (x : real) (n : nat) (h1 : term41 n) : term97 n x.
Proof. exact (@lem1636629 n h1 x). Qed.
Lemma lem1636631 (x : real) (n : nat) : (term97 n x) = (term98 x n).
Proof. exact (eq_refl (term97 n x)). Qed.
Lemma lem1636632 (x : real) (n : nat) (h1 : term41 n) : term98 x n.
Proof. exact (EQ_MP (@lem1636631 x n) (@lem1636630 x n h1)). Qed.
Lemma lem1636633 (x : real) (y : real) (n : nat) (h1 : term41 n) : term99 x n y.
Proof. exact (@lem1636632 x n h1 y). Qed.
Lemma lem1636634 (x : real) (y : real) (n : nat) : (term99 x n y) = (term100 x y n).
Proof. exact (eq_refl (term99 x n y)). Qed.
Lemma lem1636635 (x : real) (y : real) (n : nat) (h1 : term41 n) : term100 x y n.
Proof. exact (EQ_MP (@lem1636634 x y n) (@lem1636633 x y n h1)). Qed.
Lemma lem1636636 (x : real) (y : real) (h1 : term69 x y) : term69 x y.
Proof. exact (h1). Qed.
Lemma lem1636637 (n : nat) (x : real) (y : real) (h1 : term41 n) (h2 : term69 x y) : term101 x y n.
Proof. exact (@lem1636635 x y n h1 (@lem1636636 x y h2)). Qed.
Lemma lem1636638 (n : nat) (x : real) (y : real) (h1 : term69 x y) : term102 x y n.
Proof. exact (fun h0 : term41 n => @lem1636637 n x y h0 h1). Qed.
Lemma lem1636639 (n : nat) (h1 : term41 n) : term41 n.
Proof. exact (h1). Qed.
Lemma lem1636640 (n : nat) (x : real) (y : real) (h1 : term41 n) (h2 : term69 x y) : term101 x y n.
Proof. exact (@lem1636638 n x y h2 (@lem1636639 n h1)). Qed.
Lemma lem1636641 (x : real) (y : real) (n : nat) (h1 : term41 n) : term100 x y n.
Proof. exact (fun h0 : term69 x y => @lem1636640 n x y h1 h0). Qed.
Lemma lem1636642 (x : real) (n : nat) (h1 : term41 n) : term98 x n.
Proof. exact (fun y : real => @lem1636641 x y n h1). Qed.
Lemma lem1636643 (n : nat) (h1 : term41 n) : term41 n.
Proof. exact (fun x : real => @lem1636642 x n h1). Qed.
Lemma lem1636644 (n : nat) : term103 n.
Proof. exact (fun h0 : term41 n => @lem1636643 n h0). Qed.
Lemma lem1636645 (n : nat) (h1 : term41 n) : term41 n.
Proof. exact (@lem1636644 n (@lem1636460 n h1)). Qed.
Lemma lem1636646 (x : real) (n : nat) (h1 : term41 n) : term97 n x.
Proof. exact (@lem1636645 n h1 x). Qed.
Lemma lem1636647 (x : real) (n : nat) : (term97 n x) = (term98 x n).
Proof. exact (eq_refl (term97 n x)). Qed.
Lemma lem1636648 (x : real) (n : nat) (h1 : term41 n) : term98 x n.
Proof. exact (EQ_MP (@lem1636647 x n) (@lem1636646 x n h1)). Qed.
Lemma lem1636649 (x : real) (y : real) (n : nat) (h1 : term41 n) : term99 x n y.
Proof. exact (@lem1636648 x n h1 y). Qed.
Lemma lem1636650 (x : real) (y : real) (n : nat) : (term99 x n y) = (term100 x y n).
Proof. exact (eq_refl (term99 x n y)). Qed.
Lemma lem1636653 (x : real) (y : real) (n : nat) (h1 : term41 n) : term100 x y n.
Proof. exact (EQ_MP (@lem1636650 x y n) (@lem1636649 x y n h1)). Qed.
Lemma lem1636662 (x : real) : (term5 x) = ((term5 x) = True).
Proof. exact (@lem7 (term5 x)). Qed.
Lemma lem1636664 (x : real) (y : real) : (real_le x y) = ((real_le x y) = True).
Proof. exact (@lem7 (real_le x y)). Qed.
Lemma lem1636669 (x : real) (h1 : term5 x) : (term5 x) = True.
Proof. exact (EQ_MP (@lem1636662 x) (@lem1636564 x h1)). Qed.
Lemma lem1636670 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1636671 (x : real) (h1 : term5 x) : (term91 x) = (and True).
Proof. exact (MK_COMB (@lem1636670) (@lem1636669 x h1)). Qed.
Lemma lem1636673 (x : real) (y : real) (h1 : real_le x y) : (real_le x y) = True.
Proof. exact (EQ_MP (@lem1636664 x y) (@lem1636563 x y h1)). Qed.
Lemma lem1636674 (y : real) (x : real) (h1 : real_le x y) (h2 : term5 x) : (term69 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1636671 x h2) (@lem1636673 x y h1)). Qed.
Lemma lem1636676 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1636677 : (True /\ True) = True.
Proof. exact (@lem1636676 True). Qed.
Lemma lem1636678 (y : real) (x : real) (h1 : real_le x y) (h2 : term5 x) : (term69 x y) = True.
Proof. exact (TRANS (@lem1636674 y x h1 h2) (@lem1636677)). Qed.
Lemma lem1636679 (y : real) (x : real) (h1 : real_le x y) (h2 : term5 x) : True = (term69 x y).
Proof. exact (SYM (@lem1636678 y x h1 h2)). Qed.
Lemma lem1636680 (y : real) (x : real) (h1 : real_le x y) (h2 : term5 x) : term69 x y.
Proof. exact (EQ_MP (@lem1636679 y x h1 h2) (@lem0)). Qed.
Lemma lem1636681 (n : nat) (y : real) (x : real) (h1 : term41 n) (h2 : real_le x y) (h3 : term5 x) : term101 x y n.
Proof. exact (@lem1636653 x y n h1 (@lem1636680 y x h2 h3)). Qed.
Lemma lem1636682 (n : nat) (y : real) (x : real) (h1 : term41 n) (h2 : real_le x y) (h3 : term5 x) : term93 x y n.
Proof. exact (conj (@lem1636628 n x h3) (@lem1636681 n y x h1 h2 h3)). Qed.
Lemma lem1636683 (n : nat) (y : real) (x : real) (h1 : term41 n) (h2 : real_le x y) (h3 : term5 x) : term96 x y n.
Proof. exact (EQ_MP (@lem1636609 n y x h2 h3) (@lem1636682 n y x h1 h2 h3)). Qed.
Lemma lem1636684 (n : nat) (y : real) (x : real) (h1 : term41 n) (h2 : real_le x y) (h3 : term5 x) : term80 x y n.
Proof. exact (@lem1636567 x y n (@lem1636683 n y x h1 h2 h3)). Qed.
Lemma lem1636685 (x : real) (y : real) (h1 : term69 x y) : real_le x y.
Proof. exact (proj2 (@lem1636562 x y h1)). Qed.
Lemma lem1636686 (x : real) (y : real) (h1 : term69 x y) : term5 x.
Proof. exact (proj1 (@lem1636562 x y h1)). Qed.
Lemma lem1636687 (n : nat) (y : real) (x : real) (h1 : term41 n) (h2 : real_le x y) (h3 : term5 x) : (real_le x y) = (term80 x y n).
Proof. exact (prop_ext (fun h4 : real_le x y => @lem1636684 n y x h1 h2 h3) (fun h4 : term80 x y n => @lem1636563 x y h2)). Qed.
Lemma lem1636688 (n : nat) (y : real) (x : real) (h1 : term41 n) (h2 : real_le x y) (h3 : term5 x) : term80 x y n.
Proof. exact (EQ_MP (@lem1636687 n y x h1 h2 h3) (@lem1636563 x y h2)). Qed.
Lemma lem1636689 (n : nat) (y : real) (x : real) (h1 : term41 n) (h2 : real_le x y) (h3 : term5 x) : (term5 x) = (term80 x y n).
Proof. exact (prop_ext (fun h4 : term5 x => @lem1636688 n y x h1 h2 h3) (fun h4 : term80 x y n => @lem1636564 x h3)). Qed.
Lemma lem1636690 (n : nat) (y : real) (x : real) (h1 : term41 n) (h2 : real_le x y) (h3 : term5 x) : term80 x y n.
Proof. exact (EQ_MP (@lem1636689 n y x h1 h2 h3) (@lem1636564 x h3)). Qed.
Lemma lem1636691 (n : nat) (y : real) (x : real) (h1 : term41 n) (h2 : term69 x y) (h3 : term5 x) : (real_le x y) = (term80 x y n).
Proof. exact (prop_ext (fun h4 : real_le x y => @lem1636690 n y x h1 h4 h3) (fun h4 : term80 x y n => @lem1636685 x y h2)). Qed.
Lemma lem1636692 (n : nat) (y : real) (x : real) (h1 : term41 n) (h2 : term69 x y) (h3 : term5 x) : term80 x y n.
Proof. exact (EQ_MP (@lem1636691 n y x h1 h2 h3) (@lem1636685 x y h2)). Qed.
Lemma lem1636693 (n : nat) (x : real) (y : real) (h1 : term41 n) (h2 : term69 x y) : (term5 x) = (term80 x y n).
Proof. exact (prop_ext (fun h3 : term5 x => @lem1636692 n y x h1 h2 h3) (fun h3 : term80 x y n => @lem1636686 x y h2)). Qed.
Lemma lem1636694 (n : nat) (x : real) (y : real) (h1 : term41 n) (h2 : term69 x y) : term80 x y n.
Proof. exact (EQ_MP (@lem1636693 n x y h1 h2) (@lem1636686 x y h2)). Qed.
Lemma lem1636695 (x : real) (y : real) (n : nat) (h1 : term41 n) : term82 x y n.
Proof. exact (fun h0 : term69 x y => @lem1636694 n x y h1 h0). Qed.
Lemma lem1636700 (x : real) (n : nat) (h1 : term41 n) : term86 x n.
Proof. exact (fun y : real => @lem1636695 x y n h1). Qed.
Lemma lem1636705 (n : nat) (h1 : term41 n) : term89 n.
Proof. exact (fun x : real => @lem1636700 x n h1). Qed.
Lemma lem1636706 (n : nat) (h1 : term41 n) : term45 n.
Proof. exact (EQ_MP (@lem1636561 n) (@lem1636705 n h1)). Qed.
Lemma lem1636707 (n : nat) : term47 n.
Proof. exact (fun h0 : term41 n => @lem1636706 n h0). Qed.
Lemma lem1636712 : term51.
Proof. exact (fun n : nat => @lem1636707 n). Qed.
Lemma lem1636713 : term53.
Proof. exact (conj (@lem1636514) (@lem1636712)). Qed.
Lemma lem1636714 : term58.
Proof. exact (@lem1636459 (@lem1636713)). Qed.
