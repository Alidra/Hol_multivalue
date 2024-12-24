Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_CONVEX_BOUND2_LT_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import REAL_LE_LMUL_spec.
Require Import REAL_LTE_ADD2_spec.
Require Import REAL_LT_IMP_LE_spec.
Require Import REAL_LT_LMUL_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1338512_spec.
Require Import thm1365105_spec.
Require Import thm1365990_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483486_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483523_spec.
Require Import thm1483529_spec.
Require Import thm1483531_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483572_spec.
Require Import thm1483574_spec.
Require Import thm1483584_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1670411 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1670412 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1670411 h1 x). Qed.
Lemma lem1670413 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1670414 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1670413 x) (@lem1670412 x h1)). Qed.
Lemma lem1670415 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1670414 x h1 y). Qed.
Lemma lem1670416 (y : real) (x : real) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1670417 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1670416 y x) (@lem1670415 x y h1)). Qed.
Lemma lem1670418 (y : real) (x : real) (z : real) (h1 : term0) : term5 y x z.
Proof. exact (@lem1670417 y x h1 z). Qed.
Lemma lem1670419 (y : real) (x : real) (z : real) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1670420 (y : real) (x : real) (z : real) (h1 : term0) : term6 y x z.
Proof. exact (EQ_MP (@lem1670419 y x z) (@lem1670418 y x z h1)). Qed.
Lemma lem1670421 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term7 x y z.
Proof. exact (h1). Qed.
Lemma lem1670422 (x : real) (y : real) (z : real) (h1 : term0) (h2 : term7 x y z) : term8 y x z.
Proof. exact (@lem1670420 y x z h1 (@lem1670421 x y z h2)). Qed.
Lemma lem1670423 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term9 y x z.
Proof. exact (fun h0 : term0 => @lem1670422 x y z h0 h1). Qed.
Lemma lem1670424 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1670425 (x : real) (y : real) (z : real) (h1 : term0) (h2 : term7 x y z) : term8 y x z.
Proof. exact (@lem1670423 x y z h2 (@lem1670424 h1)). Qed.
Lemma lem1670426 (y : real) (x : real) (z : real) (h1 : term0) : term6 y x z.
Proof. exact (fun h0 : term7 x y z => @lem1670425 x y z h1 h0). Qed.
Lemma lem1670427 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (fun z : real => @lem1670426 y x z h1). Qed.
Lemma lem1670428 (y : real) (h1 : term0) : term10 y.
Proof. exact (fun x : real => @lem1670427 y x h1). Qed.
Lemma lem1670429 (h1 : term0) : term11.
Proof. exact (fun y : real => @lem1670428 y h1). Qed.
Lemma lem1670430 : term12.
Proof. exact (fun h0 : term0 => @lem1670429 h0). Qed.
Lemma lem1670431 : term11.
Proof. exact (@lem1670430 (@lem1584766)). Qed.
Lemma lem1670432 (y : real) : term13 y.
Proof. exact (@lem1670431 y). Qed.
Lemma lem1670433 (y : real) : (term13 y) = (term10 y).
Proof. exact (eq_refl (term13 y)). Qed.
Lemma lem1670434 (y : real) : term10 y.
Proof. exact (EQ_MP (@lem1670433 y) (@lem1670432 y)). Qed.
Lemma lem1670435 (y : real) (x : real) : term14 y x.
Proof. exact (@lem1670434 y x). Qed.
Lemma lem1670436 (y : real) (x : real) : (term14 y x) = (term4 y x).
Proof. exact (eq_refl (term14 y x)). Qed.
Lemma lem1670437 (y : real) (x : real) : term4 y x.
Proof. exact (EQ_MP (@lem1670436 y x) (@lem1670435 y x)). Qed.
Lemma lem1670438 (y : real) (x : real) (z : real) : term5 y x z.
Proof. exact (@lem1670437 y x z). Qed.
Lemma lem1670439 (y : real) (x : real) (z : real) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1670441 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem1670442 (w : real) (h1 : term15) : term16 w.
Proof. exact (@lem1670441 h1 w). Qed.
Lemma lem1670443 (w : real) : (term16 w) = (term17 w).
Proof. exact (eq_refl (term16 w)). Qed.
Lemma lem1670444 (w : real) (h1 : term15) : term17 w.
Proof. exact (EQ_MP (@lem1670443 w) (@lem1670442 w h1)). Qed.
Lemma lem1670445 (w : real) (x : real) (h1 : term15) : term18 w x.
Proof. exact (@lem1670444 w h1 x). Qed.
Lemma lem1670446 (w : real) (x : real) : (term18 w x) = (term19 w x).
Proof. exact (eq_refl (term18 w x)). Qed.
Lemma lem1670447 (w : real) (x : real) (h1 : term15) : term19 w x.
Proof. exact (EQ_MP (@lem1670446 w x) (@lem1670445 w x h1)). Qed.
Lemma lem1670448 (w : real) (x : real) (y : real) (h1 : term15) : term20 w x y.
Proof. exact (@lem1670447 w x h1 y). Qed.
Lemma lem1670449 (w : real) (y : real) (x : real) : (term20 w x y) = (term21 w y x).
Proof. exact (eq_refl (term20 w x y)). Qed.
Lemma lem1670450 (w : real) (y : real) (x : real) (h1 : term15) : term21 w y x.
Proof. exact (EQ_MP (@lem1670449 w y x) (@lem1670448 w x y h1)). Qed.
Lemma lem1670451 (w : real) (y : real) (x : real) (z : real) (h1 : term15) : term22 w y x z.
Proof. exact (@lem1670450 w y x h1 z). Qed.
Lemma lem1670452 (w : real) (y : real) (x : real) (z : real) : (term22 w y x z) = (term23 w y x z).
Proof. exact (eq_refl (term22 w y x z)). Qed.
Lemma lem1670453 (w : real) (y : real) (x : real) (z : real) (h1 : term15) : term23 w y x z.
Proof. exact (EQ_MP (@lem1670452 w y x z) (@lem1670451 w y x z h1)). Qed.
Lemma lem1670454 (w : real) (x : real) (y : real) (z : real) (h1 : term24 w x y z) : term24 w x y z.
Proof. exact (h1). Qed.
Lemma lem1670455 (w : real) (x : real) (y : real) (z : real) (h1 : term15) (h2 : term24 w x y z) : term25 w y x z.
Proof. exact (@lem1670453 w y x z h1 (@lem1670454 w x y z h2)). Qed.
Lemma lem1670456 (w : real) (x : real) (y : real) (z : real) (h1 : term24 w x y z) : term26 w y x z.
Proof. exact (fun h0 : term15 => @lem1670455 w x y z h0 h1). Qed.
Lemma lem1670457 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem1670458 (w : real) (x : real) (y : real) (z : real) (h1 : term15) (h2 : term24 w x y z) : term25 w y x z.
Proof. exact (@lem1670456 w x y z h2 (@lem1670457 h1)). Qed.
Lemma lem1670459 (w : real) (y : real) (x : real) (z : real) (h1 : term15) : term23 w y x z.
Proof. exact (fun h0 : term24 w x y z => @lem1670458 w x y z h1 h0). Qed.
Lemma lem1670460 (w : real) (y : real) (x : real) (h1 : term15) : term21 w y x.
Proof. exact (fun z : real => @lem1670459 w y x z h1). Qed.
Lemma lem1670461 (w : real) (y : real) (h1 : term15) : term27 w y.
Proof. exact (fun x : real => @lem1670460 w y x h1). Qed.
Lemma lem1670462 (w : real) (h1 : term15) : term28 w.
Proof. exact (fun y : real => @lem1670461 w y h1). Qed.
Lemma lem1670463 (h1 : term15) : term29.
Proof. exact (fun w : real => @lem1670462 w h1). Qed.
Lemma lem1670464 : term30.
Proof. exact (fun h0 : term15 => @lem1670463 h0). Qed.
Lemma lem1670465 : term29.
Proof. exact (@lem1670464 (@lem1519000)). Qed.
Lemma lem1670466 (w : real) : term31 w.
Proof. exact (@lem1670465 w). Qed.
Lemma lem1670467 (w : real) : (term31 w) = (term28 w).
Proof. exact (eq_refl (term31 w)). Qed.
Lemma lem1670468 (w : real) : term28 w.
Proof. exact (EQ_MP (@lem1670467 w) (@lem1670466 w)). Qed.
Lemma lem1670469 (w : real) (y : real) : term32 w y.
Proof. exact (@lem1670468 w y). Qed.
Lemma lem1670470 (w : real) (y : real) : (term32 w y) = (term27 w y).
Proof. exact (eq_refl (term32 w y)). Qed.
Lemma lem1670471 (w : real) (y : real) : term27 w y.
Proof. exact (EQ_MP (@lem1670470 w y) (@lem1670469 w y)). Qed.
Lemma lem1670472 (w : real) (y : real) (x : real) : term33 w y x.
Proof. exact (@lem1670471 w y x). Qed.
Lemma lem1670473 (w : real) (y : real) (x : real) : (term33 w y x) = (term21 w y x).
Proof. exact (eq_refl (term33 w y x)). Qed.
Lemma lem1670474 (w : real) (y : real) (x : real) : term21 w y x.
Proof. exact (EQ_MP (@lem1670473 w y x) (@lem1670472 w y x)). Qed.
Lemma lem1670475 (w : real) (y : real) (x : real) (z : real) : term22 w y x z.
Proof. exact (@lem1670474 w y x z). Qed.
Lemma lem1670476 (w : real) (y : real) (x : real) (z : real) : (term22 w y x z) = (term23 w y x z).
Proof. exact (eq_refl (term22 w y x z)). Qed.
Lemma lem1670478 (u : real) : term34 u.
Proof. exact (@lem9784 (u = term35)). Qed.
Lemma lem1670479 (u : real) : (term34 u) = (term36 u).
Proof. exact (eq_refl (term34 u)). Qed.
Lemma lem1670480 (u : real) : term36 u.
Proof. exact (EQ_MP (@lem1670479 u) (@lem1670478 u)). Qed.
Lemma lem1670481 (u : real) (h1 : u = term35) : u = term35.
Proof. exact (h1). Qed.
Lemma lem1670482 (u : real) (h1 : term37 u) : term37 u.
Proof. exact (h1). Qed.
Lemma lem1670483 (x : real) : term38 x.
Proof. exact (@lem1338512 x). Qed.
Lemma lem1670484 (x : real) : (term38 x) = ((term39 x) = x).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1670486 (x : real) : term40 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem1670487 (x : real) : (term40 x) = ((term41 x) = term35).
Proof. exact (eq_refl (term40 x)). Qed.
Lemma lem1670498 (u : real) (h1 : u = term35) : u = term35.
Proof. exact (h1). Qed.
Lemma lem1670499 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem1670500 (u : real) (h1 : u = term35) : (term43 u) = term44.
Proof. exact (MK_COMB (@lem1670499) (@lem1670498 u h1)). Qed.
Lemma lem1670501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1670502 (u : real) (h1 : u = term35) : (term45 u) = term46.
Proof. exact (MK_COMB (@lem1670501) (@lem1670500 u h1)). Qed.
Lemma lem1670508 (u : real) (h1 : u = term35) : u = term35.
Proof. exact (h1). Qed.
Lemma lem1670509 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1670510 (u : real) (h1 : u = term35) : (real_add u) = term47.
Proof. exact (MK_COMB (@lem1670509) (@lem1670508 u h1)). Qed.
Lemma lem1670511 (v : real) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem1670512 (v : real) (u : real) (h1 : u = term35) : (real_add u v) = (term39 v).
Proof. exact (MK_COMB (@lem1670510 u h1) (@lem1670511 v)). Qed.
Lemma lem1670514 (x : real) : (term39 x) = x.
Proof. exact (EQ_MP (@lem1670484 x) (@lem1670483 x)). Qed.
Lemma lem1670515 (v : real) : (term39 v) = v.
Proof. exact (@lem1670514 v). Qed.
Lemma lem1670516 (v : real) (u : real) (h1 : u = term35) : (real_add u v) = v.
Proof. exact (TRANS (@lem1670512 v u h1) (@lem1670515 v)). Qed.
Lemma lem1670517 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1670518 (v : real) (u : real) (h1 : u = term35) : (term48 u v) = (@eq real v).
Proof. exact (MK_COMB (@lem1670517) (@lem1670516 v u h1)). Qed.
Lemma lem1670519 : term49 = term49.
Proof. exact (eq_refl term49). Qed.
Lemma lem1670520 (v : real) (u : real) (h1 : u = term35) : ((real_add u v) = term49) = (v = term49).
Proof. exact (MK_COMB (@lem1670518 v u h1) (@lem1670519)). Qed.
Lemma lem1670523 (v : real) : (term45 v) = (term45 v).
Proof. exact (eq_refl (term45 v)). Qed.
Lemma lem1670524 (v : real) (u : real) (h1 : u = term35) : (term50 u v) = (term51 v).
Proof. exact (MK_COMB (@lem1670523 v) (@lem1670520 v u h1)). Qed.
Lemma lem1670527 (v : real) (u : real) (h1 : u = term35) : (term52 u v) = (term53 v).
Proof. exact (MK_COMB (@lem1670502 u h1) (@lem1670524 v u h1)). Qed.
Lemma lem1670530 (y : real) (b : real) : (term54 y b) = (term54 y b).
Proof. exact (eq_refl (term54 y b)). Qed.
Lemma lem1670531 (y : real) (b : real) (v : real) (u : real) (h1 : u = term35) : (term55 y b u v) = (term56 y b v).
Proof. exact (MK_COMB (@lem1670530 y b) (@lem1670527 v u h1)). Qed.
Lemma lem1670534 (x : real) (a : real) : (term54 x a) = (term54 x a).
Proof. exact (eq_refl (term54 x a)). Qed.
Lemma lem1670535 (x : real) (a : real) (y : real) (b : real) (v : real) (u : real) (h1 : u = term35) : (term57 x a y b u v) = (term58 x a y b v).
Proof. exact (MK_COMB (@lem1670534 x a) (@lem1670531 y b v u h1)). Qed.
Lemma lem1670538 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1670539 (x : real) (a : real) (y : real) (b : real) (v : real) (u : real) (h1 : u = term35) : (term59 x a y b u v) = (term60 x a y b v).
Proof. exact (MK_COMB (@lem1670538) (@lem1670535 x a y b v u h1)). Qed.
Lemma lem1670541 (u : real) (h1 : u = term35) : u = term35.
Proof. exact (h1). Qed.
Lemma lem1670542 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1670543 (u : real) (h1 : u = term35) : (real_mul u) = term61.
Proof. exact (MK_COMB (@lem1670542) (@lem1670541 u h1)). Qed.
Lemma lem1670544 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1670545 (x : real) (u : real) (h1 : u = term35) : (real_mul u x) = (term41 x).
Proof. exact (MK_COMB (@lem1670543 u h1) (@lem1670544 x)). Qed.
Lemma lem1670547 (x : real) : (term41 x) = term35.
Proof. exact (EQ_MP (@lem1670487 x) (@lem1670486 x)). Qed.
Lemma lem1670548 (x : real) (u : real) (h1 : u = term35) : (real_mul u x) = term35.
Proof. exact (TRANS (@lem1670545 x u h1) (@lem1670547 x)). Qed.
Lemma lem1670549 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1670550 (x : real) (u : real) (h1 : u = term35) : (term62 u x) = term47.
Proof. exact (MK_COMB (@lem1670549) (@lem1670548 x u h1)). Qed.
Lemma lem1670551 (v : real) (y : real) : (real_mul v y) = (real_mul v y).
Proof. exact (eq_refl (real_mul v y)). Qed.
Lemma lem1670552 (x : real) (v : real) (y : real) (u : real) (h1 : u = term35) : (term63 u x v y) = (term64 v y).
Proof. exact (MK_COMB (@lem1670550 x u h1) (@lem1670551 v y)). Qed.
Lemma lem1670554 (x : real) : (term39 x) = x.
Proof. exact (EQ_MP (@lem1670484 x) (@lem1670483 x)). Qed.
Lemma lem1670555 (v : real) (y : real) : (term64 v y) = (real_mul v y).
Proof. exact (@lem1670554 (real_mul v y)). Qed.
Lemma lem1670556 (x : real) (v : real) (y : real) (u : real) (h1 : u = term35) : (term63 u x v y) = (real_mul v y).
Proof. exact (TRANS (@lem1670552 x v y u h1) (@lem1670555 v y)). Qed.
Lemma lem1670557 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1670558 (x : real) (v : real) (y : real) (u : real) (h1 : u = term35) : (term65 u x v y) = (term66 v y).
Proof. exact (MK_COMB (@lem1670557) (@lem1670556 x v y u h1)). Qed.
Lemma lem1670560 (u : real) (h1 : u = term35) : u = term35.
Proof. exact (h1). Qed.
Lemma lem1670561 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1670562 (u : real) (h1 : u = term35) : (real_mul u) = term61.
Proof. exact (MK_COMB (@lem1670561) (@lem1670560 u h1)). Qed.
Lemma lem1670563 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1670564 (a : real) (u : real) (h1 : u = term35) : (real_mul u a) = (term41 a).
Proof. exact (MK_COMB (@lem1670562 u h1) (@lem1670563 a)). Qed.
Lemma lem1670566 (x : real) : (term41 x) = term35.
Proof. exact (EQ_MP (@lem1670487 x) (@lem1670486 x)). Qed.
Lemma lem1670567 (a : real) : (term41 a) = term35.
Proof. exact (@lem1670566 a). Qed.
Lemma lem1670568 (a : real) (u : real) (h1 : u = term35) : (real_mul u a) = term35.
Proof. exact (TRANS (@lem1670564 a u h1) (@lem1670567 a)). Qed.
Lemma lem1670569 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1670570 (a : real) (u : real) (h1 : u = term35) : (term62 u a) = term47.
Proof. exact (MK_COMB (@lem1670569) (@lem1670568 a u h1)). Qed.
Lemma lem1670571 (v : real) (b : real) : (real_mul v b) = (real_mul v b).
Proof. exact (eq_refl (real_mul v b)). Qed.
Lemma lem1670572 (a : real) (v : real) (b : real) (u : real) (h1 : u = term35) : (term63 u a v b) = (term64 v b).
Proof. exact (MK_COMB (@lem1670570 a u h1) (@lem1670571 v b)). Qed.
Lemma lem1670574 (x : real) : (term39 x) = x.
Proof. exact (EQ_MP (@lem1670484 x) (@lem1670483 x)). Qed.
Lemma lem1670575 (v : real) (b : real) : (term64 v b) = (real_mul v b).
Proof. exact (@lem1670574 (real_mul v b)). Qed.
Lemma lem1670576 (a : real) (v : real) (b : real) (u : real) (h1 : u = term35) : (term63 u a v b) = (real_mul v b).
Proof. exact (TRANS (@lem1670572 a v b u h1) (@lem1670575 v b)). Qed.
Lemma lem1670577 (x : real) (a : real) (y : real) (v : real) (b : real) (u : real) (h1 : u = term35) : (term67 x y u a v b) = (term8 y v b).
Proof. exact (MK_COMB (@lem1670558 x v y u h1) (@lem1670576 a v b u h1)). Qed.
Lemma lem1670578 (x : real) (a : real) (y : real) (v : real) (b : real) (u : real) (h1 : u = term35) : (term68 x y u a v b) = (term69 x a y v b).
Proof. exact (MK_COMB (@lem1670539 x a y b v u h1) (@lem1670577 x a y v b u h1)). Qed.
Lemma lem1670581 (x : real) (y : real) (a : real) (v : real) (b : real) (u : real) (h1 : u = term35) : (term69 x a y v b) = (term68 x y u a v b).
Proof. exact (SYM (@lem1670578 x a y v b u h1)). Qed.
Lemma lem1670582 (x : real) (a : real) (y : real) (b : real) (v : real) (h1 : term58 x a y b v) : term58 x a y b v.
Proof. exact (h1). Qed.
Lemma lem1670583 (y : real) (b : real) (v : real) (h1 : term56 y b v) : term56 y b v.
Proof. exact (h1). Qed.
Lemma lem1670584 (x : real) (a : real) (h1 : real_lt x a) : real_lt x a.
Proof. exact (h1). Qed.
Lemma lem1670585 (v : real) (h1 : term53 v) : term53 v.
Proof. exact (h1). Qed.
Lemma lem1670586 (y : real) (b : real) (h1 : real_lt y b) : real_lt y b.
Proof. exact (h1). Qed.
Lemma lem1670587 (v : real) (h1 : term51 v) : term51 v.
Proof. exact (h1). Qed.
Lemma lem1670588 (h1 : term44) : term44.
Proof. exact (h1). Qed.
Lemma lem1670589 (v : real) (h1 : v = term49) : v = term49.
Proof. exact (h1). Qed.
Lemma lem1670590 (v : real) (h1 : term43 v) : term43 v.
Proof. exact (h1). Qed.
Lemma lem1670591 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : term57 x a y b u v) : term57 x a y b u v.
Proof. exact (h1). Qed.
Lemma lem1670592 (y : real) (b : real) (u : real) (v : real) (h1 : term55 y b u v) : term55 y b u v.
Proof. exact (h1). Qed.
Lemma lem1670593 (x : real) (a : real) (h1 : real_lt x a) : real_lt x a.
Proof. exact (h1). Qed.
Lemma lem1670594 (u : real) (v : real) (h1 : term52 u v) : term52 u v.
Proof. exact (h1). Qed.
Lemma lem1670595 (y : real) (b : real) (h1 : real_lt y b) : real_lt y b.
Proof. exact (h1). Qed.
Lemma lem1670596 (u : real) (v : real) (h1 : term50 u v) : term50 u v.
Proof. exact (h1). Qed.
Lemma lem1670597 (u : real) (h1 : term43 u) : term43 u.
Proof. exact (h1). Qed.
Lemma lem1670598 (u : real) (v : real) (h1 : (real_add u v) = term49) : (real_add u v) = term49.
Proof. exact (h1). Qed.
Lemma lem1670599 (v : real) (h1 : term43 v) : term43 v.
Proof. exact (h1). Qed.
Lemma lem1670601 (w : real) (y : real) (x : real) (z : real) : term23 w y x z.
Proof. exact (EQ_MP (@lem1670476 w y x z) (@lem1670475 w y x z)). Qed.
Lemma lem1670602 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : term70 x y u a v b.
Proof. exact (@lem1670601 (real_mul u x) (real_mul v y) (real_mul u a) (real_mul v b)). Qed.
Lemma lem1670603 (x : real) : term71 x.
Proof. exact (@lem1369133 x). Qed.
Lemma lem1670604 (x : real) : (term71 x) = (term72 x).
Proof. exact (eq_refl (term71 x)). Qed.
Lemma lem1670605 (x : real) : term72 x.
Proof. exact (EQ_MP (@lem1670604 x) (@lem1670603 x)). Qed.
Lemma lem1670606 (x : real) (y : real) : term73 x y.
Proof. exact (@lem1670605 x y). Qed.
Lemma lem1670607 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (eq_refl (term73 x y)). Qed.
Lemma lem1670608 (x : real) (y : real) : term74 x y.
Proof. exact (EQ_MP (@lem1670607 x y) (@lem1670606 x y)). Qed.
Lemma lem1670609 (x : real) (y : real) (h1 : real_lt x y) : real_lt x y.
Proof. exact (h1). Qed.
Lemma lem1670610 (x : real) (y : real) (h1 : real_lt x y) : real_le x y.
Proof. exact (@lem1670608 x y (@lem1670609 x y h1)). Qed.
Lemma lem1670611 (x : real) (y : real) : (real_le x y) = ((real_le x y) = True).
Proof. exact (@lem7 (real_le x y)). Qed.
Lemma lem1670612 (x : real) (y : real) (h1 : real_lt x y) : (real_le x y) = True.
Proof. exact (EQ_MP (@lem1670611 x y) (@lem1670610 x y h1)). Qed.
Lemma lem1670618 (x : real) : term75 x.
Proof. exact (@lem1583207 x). Qed.
Lemma lem1670619 (x : real) : (term75 x) = (term76 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem1670620 (x : real) : term76 x.
Proof. exact (EQ_MP (@lem1670619 x) (@lem1670618 x)). Qed.
Lemma lem1670621 (x : real) (y : real) : term77 x y.
Proof. exact (@lem1670620 x y). Qed.
Lemma lem1670622 (y : real) (x : real) : (term77 x y) = (term78 y x).
Proof. exact (eq_refl (term77 x y)). Qed.
Lemma lem1670623 (y : real) (x : real) : term78 y x.
Proof. exact (EQ_MP (@lem1670622 y x) (@lem1670621 x y)). Qed.
Lemma lem1670624 (y : real) (x : real) (z : real) : term79 y x z.
Proof. exact (@lem1670623 y x z). Qed.
Lemma lem1670625 (y : real) (x : real) (z : real) : (term79 y x z) = (term80 y x z).
Proof. exact (eq_refl (term79 y x z)). Qed.
Lemma lem1670626 (y : real) (x : real) (z : real) : term80 y x z.
Proof. exact (EQ_MP (@lem1670625 y x z) (@lem1670624 y x z)). Qed.
Lemma lem1670627 (x : real) (y : real) (z : real) (h1 : term81 x y z) : term81 x y z.
Proof. exact (h1). Qed.
Lemma lem1670628 (x : real) (y : real) (z : real) (h1 : term81 x y z) : term82 y x z.
Proof. exact (@lem1670626 y x z (@lem1670627 x y z h1)). Qed.
Lemma lem1670629 (y : real) (x : real) (z : real) : (term82 y x z) = ((term82 y x z) = True).
Proof. exact (@lem7 (term82 y x z)). Qed.
Lemma lem1670630 (x : real) (y : real) (z : real) (h1 : term81 x y z) : (term82 y x z) = True.
Proof. exact (EQ_MP (@lem1670629 y x z) (@lem1670628 x y z h1)). Qed.
Lemma lem1670651 (y : real) (b : real) : (real_lt y b) = ((real_lt y b) = True).
Proof. exact (@lem7 (real_lt y b)). Qed.
Lemma lem1670655 (v : real) : (term43 v) = ((term43 v) = True).
Proof. exact (@lem7 (term43 v)). Qed.
Lemma lem1670660 (y : real) (x : real) (z : real) : term83 y x z.
Proof. exact (fun h0 : term81 x y z => @lem1670630 x y z h0). Qed.
Lemma lem1670661 (y : real) (v : real) (b : real) : term83 y v b.
Proof. exact (@lem1670660 y v b). Qed.
Lemma lem1670665 (v : real) (h1 : term43 v) : (term43 v) = True.
Proof. exact (EQ_MP (@lem1670655 v) (@lem1670599 v h1)). Qed.
Lemma lem1670666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1670667 (v : real) (h1 : term43 v) : (term45 v) = (and True).
Proof. exact (MK_COMB (@lem1670666) (@lem1670665 v h1)). Qed.
Lemma lem1670669 (x : real) (y : real) : term84 x y.
Proof. exact (fun h0 : real_lt x y => @lem1670612 x y h0). Qed.
Lemma lem1670670 (y : real) (b : real) : term84 y b.
Proof. exact (@lem1670669 y b). Qed.
Lemma lem1670672 (y : real) (b : real) (h1 : real_lt y b) : (real_lt y b) = True.
Proof. exact (EQ_MP (@lem1670651 y b) (@lem1670595 y b h1)). Qed.
Lemma lem1670673 (y : real) (b : real) (h1 : real_lt y b) : True = (real_lt y b).
Proof. exact (SYM (@lem1670672 y b h1)). Qed.
Lemma lem1670674 (y : real) (b : real) (h1 : real_lt y b) : real_lt y b.
Proof. exact (EQ_MP (@lem1670673 y b h1) (@lem0)). Qed.
Lemma lem1670675 (y : real) (b : real) (h1 : real_lt y b) : (real_le y b) = True.
Proof. exact (@lem1670670 y b (@lem1670674 y b h1)). Qed.
Lemma lem1670676 (v : real) (y : real) (b : real) (h1 : term43 v) (h2 : real_lt y b) : (term81 v y b) = (True /\ True).
Proof. exact (MK_COMB (@lem1670667 v h1) (@lem1670675 y b h2)). Qed.
Lemma lem1670678 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1670679 : (True /\ True) = True.
Proof. exact (@lem1670678 True). Qed.
Lemma lem1670680 (v : real) (y : real) (b : real) (h1 : term43 v) (h2 : real_lt y b) : (term81 v y b) = True.
Proof. exact (TRANS (@lem1670676 v y b h1 h2) (@lem1670679)). Qed.
Lemma lem1670681 (v : real) (y : real) (b : real) (h1 : term43 v) (h2 : real_lt y b) : True = (term81 v y b).
Proof. exact (SYM (@lem1670680 v y b h1 h2)). Qed.
Lemma lem1670682 (v : real) (y : real) (b : real) (h1 : term43 v) (h2 : real_lt y b) : term81 v y b.
Proof. exact (EQ_MP (@lem1670681 v y b h1 h2) (@lem0)). Qed.
Lemma lem1670683 (v : real) (y : real) (b : real) (h1 : term43 v) (h2 : real_lt y b) : (term82 y v b) = True.
Proof. exact (@lem1670661 y v b (@lem1670682 v y b h1 h2)). Qed.
Lemma lem1670684 (x : real) (u : real) (a : real) : (term85 x u a) = (term85 x u a).
Proof. exact (eq_refl (term85 x u a)). Qed.
Lemma lem1670685 (x : real) (u : real) (a : real) (v : real) (y : real) (b : real) (h1 : term43 v) (h2 : real_lt y b) : (term86 x u a y v b) = (term87 x u a).
Proof. exact (MK_COMB (@lem1670684 x u a) (@lem1670683 v y b h1 h2)). Qed.
Lemma lem1670687 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1670688 (x : real) (u : real) (a : real) : (term87 x u a) = (term8 x u a).
Proof. exact (@lem1670687 (term8 x u a)). Qed.
Lemma lem1670689 (x : real) (u : real) (a : real) (v : real) (y : real) (b : real) (h1 : term43 v) (h2 : real_lt y b) : (term86 x u a y v b) = (term8 x u a).
Proof. exact (TRANS (@lem1670685 x u a v y b h1 h2) (@lem1670688 x u a)). Qed.
Lemma lem1670690 (x : real) (u : real) (a : real) (v : real) (y : real) (b : real) (h1 : term43 v) (h2 : real_lt y b) : (term8 x u a) = (term86 x u a y v b).
Proof. exact (SYM (@lem1670689 x u a v y b h1 h2)). Qed.
Lemma lem1670692 (y : real) (x : real) (z : real) : term6 y x z.
Proof. exact (EQ_MP (@lem1670439 y x z) (@lem1670438 y x z)). Qed.
Lemma lem1670693 (y : real) (v : real) (b : real) : term6 y v b.
Proof. exact (@lem1670692 y v b). Qed.
Lemma lem1670695 (y : real) (x : real) (z : real) : term6 y x z.
Proof. exact (EQ_MP (@lem1670439 y x z) (@lem1670438 y x z)). Qed.
Lemma lem1670696 (x : real) (u : real) (a : real) : term6 x u a.
Proof. exact (@lem1670695 x u a). Qed.
Lemma lem1670726 (v : real) (y : real) (b : real) : (term88 v y b) = (term89 v y b).
Proof. exact (@lem17045 (term90 v) (real_lt y b)). Qed.
Lemma lem1670728 (v : real) : (term91 v) = (term91 v).
Proof. exact (eq_refl (term91 v)). Qed.
Lemma lem1670729 (v : real) (y : real) (b : real) : (term92 v y b) = (term93 v y b).
Proof. exact (MK_COMB (@lem1670728 v) (@lem1670726 v y b)). Qed.
Lemma lem1670730 (v : real) (y : real) (b : real) : (term94 v y b) = (term92 v y b).
Proof. exact (@lem17362 (v = term49) (term7 v y b)). Qed.
Lemma lem1670731 (v : real) (y : real) (b : real) : (term94 v y b) = (term93 v y b).
Proof. exact (TRANS (@lem1670730 v y b) (@lem1670729 v y b)). Qed.
Lemma lem1670733 (v : real) : (term45 v) = (term45 v).
Proof. exact (eq_refl (term45 v)). Qed.
Lemma lem1670734 (v : real) (y : real) (b : real) : (term95 v y b) = (term96 v y b).
Proof. exact (MK_COMB (@lem1670733 v) (@lem1670731 v y b)). Qed.
Lemma lem1670735 (v : real) (y : real) (b : real) : (term97 v y b) = (term95 v y b).
Proof. exact (@lem17362 (term43 v) (term98 v y b)). Qed.
Lemma lem1670736 (v : real) (y : real) (b : real) : (term97 v y b) = (term96 v y b).
Proof. exact (TRANS (@lem1670735 v y b) (@lem1670734 v y b)). Qed.
Lemma lem1670738 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem1670739 (v : real) (y : real) (b : real) : (term99 v y b) = (term100 v y b).
Proof. exact (MK_COMB (@lem1670738) (@lem1670736 v y b)). Qed.
Lemma lem1670740 (v : real) (y : real) (b : real) : (term101 v y b) = (term99 v y b).
Proof. exact (@lem17362 term44 (term102 v y b)). Qed.
Lemma lem1670741 (v : real) (y : real) (b : real) : (term101 v y b) = (term100 v y b).
Proof. exact (TRANS (@lem1670740 v y b) (@lem1670739 v y b)). Qed.
Lemma lem1670743 (y : real) (b : real) : (term54 y b) = (term54 y b).
Proof. exact (eq_refl (term54 y b)). Qed.
Lemma lem1670744 (v : real) (y : real) (b : real) : (term103 v y b) = (term104 v y b).
Proof. exact (MK_COMB (@lem1670743 y b) (@lem1670741 v y b)). Qed.
Lemma lem1670745 (v : real) (y : real) (b : real) : (term105 v y b) = (term103 v y b).
Proof. exact (@lem17362 (real_lt y b) (term106 v y b)). Qed.
Lemma lem1670746 (v : real) (y : real) (b : real) : (term105 v y b) = (term104 v y b).
Proof. exact (TRANS (@lem1670745 v y b) (@lem1670744 v y b)). Qed.
Lemma lem1670748 (x : real) (a : real) : (term54 x a) = (term54 x a).
Proof. exact (eq_refl (term54 x a)). Qed.
Lemma lem1670749 (x : real) (a : real) (v : real) (y : real) (b : real) : (term107 x a v y b) = (term108 x a v y b).
Proof. exact (MK_COMB (@lem1670748 x a) (@lem1670746 v y b)). Qed.
Lemma lem1670750 (x : real) (a : real) (v : real) (y : real) (b : real) : (term109 x a v y b) = (term107 x a v y b).
Proof. exact (@lem17362 (real_lt x a) (term110 v y b)). Qed.
Lemma lem1670751 (x : real) (a : real) (v : real) (y : real) (b : real) : (term109 x a v y b) = (term108 x a v y b).
Proof. exact (TRANS (@lem1670750 x a v y b) (@lem1670749 x a v y b)). Qed.
Lemma lem1670753 (u : real) : (term111 u) = (term111 u).
Proof. exact (eq_refl (term111 u)). Qed.
Lemma lem1670754 (u : real) (x : real) (a : real) (v : real) (y : real) (b : real) : (term112 u x a v y b) = (term113 u x a v y b).
Proof. exact (MK_COMB (@lem1670753 u) (@lem1670751 x a v y b)). Qed.
Lemma lem1670755 (u : real) (x : real) (a : real) (v : real) (y : real) (b : real) : (term114 u x a v y b) = (term112 u x a v y b).
Proof. exact (@lem17362 (u = term35) (term115 x a v y b)). Qed.
Lemma lem1670791 (u : real) (x : real) (a : real) (v : real) (y : real) (b : real) : (term114 u x a v y b) = (term113 u x a v y b).
Proof. exact (TRANS (@lem1670755 u x a v y b) (@lem1670754 u x a v y b)). Qed.
Lemma lem1670792 (u : real) : (u = term35) = ((term116 u) = term35).
Proof. exact (@lem1483529 u term35). Qed.
Lemma lem1670798 (u : real) : (term116 u) = (term117 u).
Proof. exact (@lem1483519 u term35). Qed.
Lemma lem1670800 (x : nat) : (term118 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1670801 : term119 = term35.
Proof. exact (@lem1670800 term120). Qed.
Lemma lem1670802 (u : real) : (real_add u) = (real_add u).
Proof. exact (eq_refl (real_add u)). Qed.
Lemma lem1670803 (u : real) : (term117 u) = (term121 u).
Proof. exact (MK_COMB (@lem1670802 u) (@lem1670801)). Qed.
Lemma lem1670804 (u : real) : (term121 u) = u.
Proof. exact (@lem1483450 u). Qed.
Lemma lem1670805 (u : real) : (term117 u) = u.
Proof. exact (TRANS (@lem1670803 u) (@lem1670804 u)). Qed.
Lemma lem1670807 (u : real) : (term116 u) = u.
Proof. exact (TRANS (@lem1670798 u) (@lem1670805 u)). Qed.
Lemma lem1670808 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1670809 (u : real) : (term122 u) = (@eq real u).
Proof. exact (MK_COMB (@lem1670808) (@lem1670807 u)). Qed.
Lemma lem1670810 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1670811 (u : real) : ((term116 u) = term35) = (u = term35).
Proof. exact (MK_COMB (@lem1670809 u) (@lem1670810)). Qed.
Lemma lem1670812 (u : real) : (u = term35) = (u = term35).
Proof. exact (TRANS (@lem1670792 u) (@lem1670811 u)). Qed.
Lemma lem1670813 (a : real) (x : real) : (real_lt x a) = (term123 a x).
Proof. exact (@lem1483521 a x). Qed.
Lemma lem1670826 (a : real) (x : real) : (real_sub a x) = (term124 a x).
Proof. exact (@lem1483519 a x). Qed.
Lemma lem1670827 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1670828 (a : real) (x : real) : (term125 a x) = (term126 a x).
Proof. exact (MK_COMB (@lem1670827) (@lem1670826 a x)). Qed.
Lemma lem1670829 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1670830 (a : real) (x : real) : (term123 a x) = (term127 a x).
Proof. exact (MK_COMB (@lem1670828 a x) (@lem1670829)). Qed.
Lemma lem1670831 (a : real) (x : real) : (real_lt x a) = (term127 a x).
Proof. exact (TRANS (@lem1670813 a x) (@lem1670830 a x)). Qed.
Lemma lem1670832 (b : real) (y : real) : (real_lt y b) = (term123 b y).
Proof. exact (@lem1483521 b y). Qed.
Lemma lem1670845 (b : real) (y : real) : (real_sub b y) = (term124 b y).
Proof. exact (@lem1483519 b y). Qed.
Lemma lem1670846 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1670847 (b : real) (y : real) : (term125 b y) = (term126 b y).
Proof. exact (MK_COMB (@lem1670846) (@lem1670845 b y)). Qed.
Lemma lem1670848 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1670849 (b : real) (y : real) : (term123 b y) = (term127 b y).
Proof. exact (MK_COMB (@lem1670847 b y) (@lem1670848)). Qed.
Lemma lem1670850 (b : real) (y : real) : (real_lt y b) = (term127 b y).
Proof. exact (TRANS (@lem1670832 b y) (@lem1670849 b y)). Qed.
Lemma lem1670851 : term44 = term128.
Proof. exact (@lem1483523 term35 term35). Qed.
Lemma lem1670857 : term129 = term130.
Proof. exact (@lem1483519 term35 term35). Qed.
Lemma lem1670859 (x : nat) : (term118 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1670860 : term119 = term35.
Proof. exact (@lem1670859 term120). Qed.
Lemma lem1670861 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1670862 : term130 = term131.
Proof. exact (MK_COMB (@lem1670861) (@lem1670860)). Qed.
Lemma lem1670863 : term131 = term35.
Proof. exact (@lem1483448 term35). Qed.
Lemma lem1670864 : term130 = term35.
Proof. exact (TRANS (@lem1670862) (@lem1670863)). Qed.
Lemma lem1670866 : term129 = term35.
Proof. exact (TRANS (@lem1670857) (@lem1670864)). Qed.
Lemma lem1670867 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1670868 : term132 = term133.
Proof. exact (MK_COMB (@lem1670867) (@lem1670866)). Qed.
Lemma lem1670869 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1670870 : term128 = term134.
Proof. exact (MK_COMB (@lem1670868) (@lem1670869)). Qed.
Lemma lem1670871 : term44 = term134.
Proof. exact (TRANS (@lem1670851) (@lem1670870)). Qed.
Lemma lem1670872 (v : real) : (term43 v) = (term135 v).
Proof. exact (@lem1483523 v term35). Qed.
Lemma lem1670878 (v : real) : (term116 v) = (term117 v).
Proof. exact (@lem1483519 v term35). Qed.
Lemma lem1670880 (x : nat) : (term118 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1670881 : term119 = term35.
Proof. exact (@lem1670880 term120). Qed.
Lemma lem1670882 (v : real) : (real_add v) = (real_add v).
Proof. exact (eq_refl (real_add v)). Qed.
Lemma lem1670883 (v : real) : (term117 v) = (term121 v).
Proof. exact (MK_COMB (@lem1670882 v) (@lem1670881)). Qed.
Lemma lem1670884 (v : real) : (term121 v) = v.
Proof. exact (@lem1483450 v). Qed.
Lemma lem1670885 (v : real) : (term117 v) = v.
Proof. exact (TRANS (@lem1670883 v) (@lem1670884 v)). Qed.
Lemma lem1670887 (v : real) : (term116 v) = v.
Proof. exact (TRANS (@lem1670878 v) (@lem1670885 v)). Qed.
Lemma lem1670888 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1670889 (v : real) : (term136 v) = (real_ge v).
Proof. exact (MK_COMB (@lem1670888) (@lem1670887 v)). Qed.
Lemma lem1670890 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1670891 (v : real) : (term135 v) = (term137 v).
Proof. exact (MK_COMB (@lem1670889 v) (@lem1670890)). Qed.
Lemma lem1670892 (v : real) : (term43 v) = (term137 v).
Proof. exact (TRANS (@lem1670872 v) (@lem1670891 v)). Qed.
Lemma lem1670893 (v : real) : (v = term49) = ((term138 v) = term35).
Proof. exact (@lem1483529 v term49). Qed.
Lemma lem1670899 (v : real) : (term138 v) = (term139 v).
Proof. exact (@lem1483519 v term49). Qed.
Lemma lem1670901 (m : nat) (n : nat) : (term140 m n) = (term141 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1670902 : term142 = term143.
Proof. exact (@lem1670901 term120 term120). Qed.
Lemma lem1670903 : (term144 = (BIT1 0)) = (term145 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1670904 : term145 = term120.
Proof. exact (EQ_MP (@lem1670903) (@lem940073)). Qed.
Lemma lem1670905 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1670906 : term146 = term49.
Proof. exact (MK_COMB (@lem1670905) (@lem1670904)). Qed.
Lemma lem1670907 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1670908 : term143 = term147.
Proof. exact (MK_COMB (@lem1670907) (@lem1670906)). Qed.
Lemma lem1670909 : term142 = term147.
Proof. exact (TRANS (@lem1670902) (@lem1670908)). Qed.
Lemma lem1670910 (v : real) : (real_add v) = (real_add v).
Proof. exact (eq_refl (real_add v)). Qed.
Lemma lem1670913 (v : real) : (term139 v) = (term148 v).
Proof. exact (MK_COMB (@lem1670910 v) (@lem1670909)). Qed.
Lemma lem1670915 (v : real) : (term138 v) = (term148 v).
Proof. exact (TRANS (@lem1670899 v) (@lem1670913 v)). Qed.
Lemma lem1670916 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1670917 (v : real) : (term149 v) = (term150 v).
Proof. exact (MK_COMB (@lem1670916) (@lem1670915 v)). Qed.
Lemma lem1670918 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1670919 (v : real) : ((term138 v) = term35) = ((term148 v) = term35).
Proof. exact (MK_COMB (@lem1670917 v) (@lem1670918)). Qed.
Lemma lem1670920 (v : real) : (v = term49) = ((term148 v) = term35).
Proof. exact (TRANS (@lem1670893 v) (@lem1670919 v)). Qed.
Lemma lem1670921 (v : real) : (term151 v) = (term152 v).
Proof. exact (@lem1483531 term35 v). Qed.
Lemma lem1670927 (v : real) : (term153 v) = (term154 v).
Proof. exact (@lem1483519 term35 v). Qed.
Lemma lem1670932 (v : real) : (term154 v) = (term155 v).
Proof. exact (@lem1483448 (term155 v)). Qed.
Lemma lem1670934 (v : real) : (term153 v) = (term155 v).
Proof. exact (TRANS (@lem1670927 v) (@lem1670932 v)). Qed.
Lemma lem1670935 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1670936 (v : real) : (term156 v) = (term157 v).
Proof. exact (MK_COMB (@lem1670935) (@lem1670934 v)). Qed.
Lemma lem1670937 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1670938 (v : real) : (term152 v) = (term158 v).
Proof. exact (MK_COMB (@lem1670936 v) (@lem1670937)). Qed.
Lemma lem1670939 (v : real) : (term151 v) = (term158 v).
Proof. exact (TRANS (@lem1670921 v) (@lem1670938 v)). Qed.
Lemma lem1670940 (y : real) (b : real) : (term159 y b) = (term160 y b).
Proof. exact (@lem1483531 y b). Qed.
Lemma lem1670946 (y : real) (b : real) : (real_sub y b) = (term124 y b).
Proof. exact (@lem1483519 y b). Qed.
Lemma lem1670951 (b : real) (y : real) : (term124 y b) = (term161 b y).
Proof. exact (@lem1483488 (term155 b) y). Qed.
Lemma lem1670953 (b : real) (y : real) : (real_sub y b) = (term161 b y).
Proof. exact (TRANS (@lem1670946 y b) (@lem1670951 b y)). Qed.
Lemma lem1670954 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1670955 (b : real) (y : real) : (term162 y b) = (term163 b y).
Proof. exact (MK_COMB (@lem1670954) (@lem1670953 b y)). Qed.
Lemma lem1670956 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1670957 (b : real) (y : real) : (term160 y b) = (term164 b y).
Proof. exact (MK_COMB (@lem1670955 b y) (@lem1670956)). Qed.
Lemma lem1670958 (b : real) (y : real) : (term159 y b) = (term164 b y).
Proof. exact (TRANS (@lem1670940 y b) (@lem1670957 b y)). Qed.
Lemma lem1670959 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1670960 (v : real) : (term165 v) = (term166 v).
Proof. exact (MK_COMB (@lem1670959) (@lem1670939 v)). Qed.
Lemma lem1670961 (v : real) (b : real) (y : real) : (term89 v y b) = (term167 v b y).
Proof. exact (MK_COMB (@lem1670960 v) (@lem1670958 b y)). Qed.
Lemma lem1670962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1670963 (v : real) : (term91 v) = (term168 v).
Proof. exact (MK_COMB (@lem1670962) (@lem1670920 v)). Qed.
Lemma lem1670964 (v : real) (b : real) (y : real) : (term93 v y b) = (term169 v b y).
Proof. exact (MK_COMB (@lem1670963 v) (@lem1670961 v b y)). Qed.
Lemma lem1670965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1670966 (v : real) : (term45 v) = (term170 v).
Proof. exact (MK_COMB (@lem1670965) (@lem1670892 v)). Qed.
Lemma lem1670967 (v : real) (b : real) (y : real) : (term96 v y b) = (term171 v b y).
Proof. exact (MK_COMB (@lem1670966 v) (@lem1670964 v b y)). Qed.
Lemma lem1670968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1670969 : term46 = term172.
Proof. exact (MK_COMB (@lem1670968) (@lem1670871)). Qed.
Lemma lem1670970 (v : real) (b : real) (y : real) : (term100 v y b) = (term173 v b y).
Proof. exact (MK_COMB (@lem1670969) (@lem1670967 v b y)). Qed.
Lemma lem1670971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1670972 (b : real) (y : real) : (term54 y b) = (term174 b y).
Proof. exact (MK_COMB (@lem1670971) (@lem1670850 b y)). Qed.
Lemma lem1670973 (v : real) (b : real) (y : real) : (term104 v y b) = (term175 v b y).
Proof. exact (MK_COMB (@lem1670972 b y) (@lem1670970 v b y)). Qed.
Lemma lem1670974 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1670975 (a : real) (x : real) : (term54 x a) = (term174 a x).
Proof. exact (MK_COMB (@lem1670974) (@lem1670831 a x)). Qed.
Lemma lem1670976 (a : real) (x : real) (v : real) (b : real) (y : real) : (term108 x a v y b) = (term176 a x v b y).
Proof. exact (MK_COMB (@lem1670975 a x) (@lem1670973 v b y)). Qed.
Lemma lem1670977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1670978 (u : real) : (term111 u) = (term111 u).
Proof. exact (MK_COMB (@lem1670977) (@lem1670812 u)). Qed.
Lemma lem1670979 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) : (term113 u x a v y b) = (term177 u a x v b y).
Proof. exact (MK_COMB (@lem1670978 u) (@lem1670976 a x v b y)). Qed.
Lemma lem1670986 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) : (term114 u x a v y b) = (term177 u a x v b y).
Proof. exact (TRANS (@lem1670791 u x a v y b) (@lem1670979 u a x v b y)). Qed.
Lemma lem1671003 (v : real) (b : real) (y : real) : (term169 v b y) = (term178 v b y).
Proof. exact (@lem19158 (term158 v) ((term148 v) = term35) (term164 b y)). Qed.
Lemma lem1671006 (v : real) : (term170 v) = (term170 v).
Proof. exact (eq_refl (term170 v)). Qed.
Lemma lem1671007 (v : real) (b : real) (y : real) : (term171 v b y) = (term179 v b y).
Proof. exact (MK_COMB (@lem1671006 v) (@lem1671003 v b y)). Qed.
Lemma lem1671014 (v : real) (b : real) (y : real) : (term179 v b y) = (term180 v b y).
Proof. exact (@lem19158 (term181 v) (term137 v) (term182 v b y)). Qed.
Lemma lem1671015 (v : real) (b : real) (y : real) : (term171 v b y) = (term180 v b y).
Proof. exact (TRANS (@lem1671007 v b y) (@lem1671014 v b y)). Qed.
Lemma lem1671018 : term172 = term172.
Proof. exact (eq_refl term172). Qed.
Lemma lem1671019 (v : real) (b : real) (y : real) : (term173 v b y) = (term183 v b y).
Proof. exact (MK_COMB (@lem1671018) (@lem1671015 v b y)). Qed.
Lemma lem1671026 (v : real) (b : real) (y : real) : (term183 v b y) = (term184 v b y).
Proof. exact (@lem19158 (term185 v) term134 (term186 v b y)). Qed.
Lemma lem1671027 (v : real) (b : real) (y : real) : (term173 v b y) = (term184 v b y).
Proof. exact (TRANS (@lem1671019 v b y) (@lem1671026 v b y)). Qed.
Lemma lem1671030 (b : real) (y : real) : (term174 b y) = (term174 b y).
Proof. exact (eq_refl (term174 b y)). Qed.
Lemma lem1671031 (v : real) (b : real) (y : real) : (term175 v b y) = (term187 v b y).
Proof. exact (MK_COMB (@lem1671030 b y) (@lem1671027 v b y)). Qed.
Lemma lem1671038 (v : real) (b : real) (y : real) : (term187 v b y) = (term188 v b y).
Proof. exact (@lem19158 (term189 v) (term127 b y) (term190 v b y)). Qed.
Lemma lem1671039 (v : real) (b : real) (y : real) : (term175 v b y) = (term188 v b y).
Proof. exact (TRANS (@lem1671031 v b y) (@lem1671038 v b y)). Qed.
Lemma lem1671042 (a : real) (x : real) : (term174 a x) = (term174 a x).
Proof. exact (eq_refl (term174 a x)). Qed.
Lemma lem1671043 (a : real) (x : real) (v : real) (b : real) (y : real) : (term176 a x v b y) = (term191 a x v b y).
Proof. exact (MK_COMB (@lem1671042 a x) (@lem1671039 v b y)). Qed.
Lemma lem1671050 (a : real) (x : real) (v : real) (b : real) (y : real) : (term191 a x v b y) = (term192 a x v b y).
Proof. exact (@lem19158 (term193 b y v) (term127 a x) (term194 v b y)). Qed.
Lemma lem1671051 (a : real) (x : real) (v : real) (b : real) (y : real) : (term176 a x v b y) = (term192 a x v b y).
Proof. exact (TRANS (@lem1671043 a x v b y) (@lem1671050 a x v b y)). Qed.
Lemma lem1671054 (u : real) : (term111 u) = (term111 u).
Proof. exact (eq_refl (term111 u)). Qed.
Lemma lem1671055 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) : (term177 u a x v b y) = (term195 u a x v b y).
Proof. exact (MK_COMB (@lem1671054 u) (@lem1671051 a x v b y)). Qed.
Lemma lem1671062 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) : (term195 u a x v b y) = (term196 u a x v b y).
Proof. exact (@lem19158 (term197 a x b y v) (u = term35) (term198 a x v b y)). Qed.
Lemma lem1671063 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) : (term177 u a x v b y) = (term196 u a x v b y).
Proof. exact (TRANS (@lem1671055 u a x v b y) (@lem1671062 u a x v b y)). Qed.
Lemma lem1671064 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) : (term114 u x a v y b) = (term196 u a x v b y).
Proof. exact (TRANS (@lem1670986 u a x v b y) (@lem1671063 u a x v b y)). Qed.
Lemma lem1671074 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term196 u a x v b y) : term196 u a x v b y.
Proof. exact (h1). Qed.
Lemma lem1671075 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : term199 u a x b y v.
Proof. exact (h1). Qed.
Lemma lem1671076 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : term197 a x b y v.
Proof. exact (proj2 (@lem1671075 u a x b y v h1)). Qed.
Lemma lem1671078 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : term193 b y v.
Proof. exact (proj2 (@lem1671076 u a x b y v h1)). Qed.
Lemma lem1671080 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : term189 v.
Proof. exact (proj2 (@lem1671078 u a x b y v h1)). Qed.
Lemma lem1671082 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : term185 v.
Proof. exact (proj2 (@lem1671080 u a x b y v h1)). Qed.
Lemma lem1671084 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : term181 v.
Proof. exact (proj2 (@lem1671082 u a x b y v h1)). Qed.
Lemma lem1671086 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : term158 v.
Proof. exact (proj2 (@lem1671084 u a x b y v h1)). Qed.
Lemma lem1671087 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : (term148 v) = term35.
Proof. exact (proj1 (@lem1671084 u a x b y v h1)). Qed.
Lemma lem1671089 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1671090 : term201 = term202.
Proof. exact (@lem1671089 (NUMERAL 0) term120). Qed.
Lemma lem1671091 : term203 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1671092 (h1 : term203 = (BIT1 0)) : term202 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1671093 : (term203 = (BIT1 0)) = (term202 = True).
Proof. exact (prop_ext (fun h1 : term203 = (BIT1 0) => @lem1671092 h1) (fun h1 : term202 = True => @lem1671091)). Qed.
Lemma lem1671094 : term202 = True.
Proof. exact (EQ_MP (@lem1671093) (@lem1671091)). Qed.
Lemma lem1671095 : term201 = True.
Proof. exact (TRANS (@lem1671090) (@lem1671094)). Qed.
Lemma lem1671096 : True = term201.
Proof. exact (SYM (@lem1671095)). Qed.
Lemma lem1671097 : term201.
Proof. exact (EQ_MP (@lem1671096) (@lem0)). Qed.
Lemma lem1671098 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : term204 v.
Proof. exact (conj (@lem1671097) (@lem1671086 u a x b y v h1)). Qed.
Lemma lem1671100 (x : real) (y : real) : term205 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1671101 (v : real) : term206 v.
Proof. exact (@lem1671100 term49 (term155 v)). Qed.
Lemma lem1671102 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : term207 v.
Proof. exact (@lem1671101 v (@lem1671098 u a x b y v h1)). Qed.
Lemma lem1671103 (v : real) : (term208 v) = (term155 v).
Proof. exact (@lem1483460 (term155 v)). Qed.
Lemma lem1671104 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1671105 (v : real) : (term209 v) = (term157 v).
Proof. exact (MK_COMB (@lem1671104) (@lem1671103 v)). Qed.
Lemma lem1671106 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671107 (v : real) : (term207 v) = (term158 v).
Proof. exact (MK_COMB (@lem1671105 v) (@lem1671106)). Qed.
Lemma lem1671108 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : term158 v.
Proof. exact (EQ_MP (@lem1671107 v) (@lem1671102 u a x b y v h1)). Qed.
Lemma lem1671110 (y : real) : term210 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1671111 (v : real) : term211 v.
Proof. exact (@lem1671110 (term148 v)). Qed.
Lemma lem1671112 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : term212 v.
Proof. exact (@lem1671111 v (@lem1671087 u a x b y v h1)). Qed.
Lemma lem1671113 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : term213 v.
Proof. exact (@lem1671112 u a x b y v h1 term49). Qed.
Lemma lem1671114 (v : real) : (term213 v) = ((term214 v) = term35).
Proof. exact (eq_refl (term213 v)). Qed.
Lemma lem1671115 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : (term214 v) = term35.
Proof. exact (EQ_MP (@lem1671114 v) (@lem1671113 u a x b y v h1)). Qed.
Lemma lem1671116 (v : real) : (term214 v) = (term148 v).
Proof. exact (@lem1483460 (term148 v)). Qed.
Lemma lem1671117 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1671118 (v : real) : (term215 v) = (term150 v).
Proof. exact (MK_COMB (@lem1671117) (@lem1671116 v)). Qed.
Lemma lem1671119 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671120 (v : real) : ((term214 v) = term35) = ((term148 v) = term35).
Proof. exact (MK_COMB (@lem1671118 v) (@lem1671119)). Qed.
Lemma lem1671121 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : (term148 v) = term35.
Proof. exact (EQ_MP (@lem1671120 v) (@lem1671115 u a x b y v h1)). Qed.
Lemma lem1671122 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : term181 v.
Proof. exact (conj (@lem1671121 u a x b y v h1) (@lem1671108 u a x b y v h1)). Qed.
Lemma lem1671124 (x : real) (y : real) : term216 x y.
Proof. exact (proj1 (@lem1483572 x y)). Qed.
Lemma lem1671125 (v : real) : term217 v.
Proof. exact (@lem1671124 (term148 v) (term155 v)). Qed.
Lemma lem1671126 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : term218 v.
Proof. exact (@lem1671125 v (@lem1671122 u a x b y v h1)). Qed.
Lemma lem1671127 (v : real) : (term219 v) = (term220 v).
Proof. exact (@lem1483486 v (term155 v) term147). Qed.
Lemma lem1671128 (v : real) : (term221 v) = (term222 v).
Proof. exact (@lem1483442 term147 v). Qed.
Lemma lem1671130 (m : nat) : (term223 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1671131 : term224 = term35.
Proof. exact (@lem1671130 term120). Qed.
Lemma lem1671132 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1671133 : term225 = term61.
Proof. exact (MK_COMB (@lem1671132) (@lem1671131)). Qed.
Lemma lem1671134 (v : real) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem1671135 (v : real) : (term222 v) = (term41 v).
Proof. exact (MK_COMB (@lem1671133) (@lem1671134 v)). Qed.
Lemma lem1671136 (v : real) : (term221 v) = (term41 v).
Proof. exact (TRANS (@lem1671128 v) (@lem1671135 v)). Qed.
Lemma lem1671137 (v : real) : (term41 v) = term35.
Proof. exact (@lem1483446 v). Qed.
Lemma lem1671138 (v : real) : (term221 v) = term35.
Proof. exact (TRANS (@lem1671136 v) (@lem1671137 v)). Qed.
Lemma lem1671139 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1671140 (v : real) : (term226 v) = term47.
Proof. exact (MK_COMB (@lem1671139) (@lem1671138 v)). Qed.
Lemma lem1671141 : term147 = term147.
Proof. exact (eq_refl term147). Qed.
Lemma lem1671142 (v : real) : (term220 v) = term227.
Proof. exact (MK_COMB (@lem1671140 v) (@lem1671141)). Qed.
Lemma lem1671143 (v : real) : (term219 v) = term227.
Proof. exact (TRANS (@lem1671127 v) (@lem1671142 v)). Qed.
Lemma lem1671144 : term227 = term147.
Proof. exact (@lem1483448 term147). Qed.
Lemma lem1671145 (v : real) : (term219 v) = term147.
Proof. exact (TRANS (@lem1671143 v) (@lem1671144)). Qed.
Lemma lem1671146 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1671147 (v : real) : (term228 v) = term229.
Proof. exact (MK_COMB (@lem1671146) (@lem1671145 v)). Qed.
Lemma lem1671148 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671149 (v : real) : (term218 v) = term230.
Proof. exact (MK_COMB (@lem1671147 v) (@lem1671148)). Qed.
Lemma lem1671150 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : term230.
Proof. exact (EQ_MP (@lem1671149 v) (@lem1671126 u a x b y v h1)). Qed.
Lemma lem1671152 (m : nat) (n : nat) : (term231 m n) = (term232 m n).
Proof. exact (proj2 (@lem1365990 m n)). Qed.
Lemma lem1671153 : term230 = term233.
Proof. exact (@lem1671152 term120 (NUMERAL 0)). Qed.
Lemma lem1671154 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1671155 : term203 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1671156 (h1 : term203 = (BIT1 0)) : (term120 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem1671157 : (term203 = (BIT1 0)) = ((term120 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term203 = (BIT1 0) => @lem1671156 h1) (fun h1 : (term120 = (NUMERAL 0)) = False => @lem1671155)). Qed.
Lemma lem1671158 : (term120 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1671157) (@lem1671155)). Qed.
Lemma lem1671159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1671160 : term234 = (and False).
Proof. exact (MK_COMB (@lem1671159) (@lem1671158)). Qed.
Lemma lem1671161 : term233 = (False /\ True).
Proof. exact (MK_COMB (@lem1671160) (@lem1671154)). Qed.
Lemma lem1671163 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1671164 : term233 = False.
Proof. exact (TRANS (@lem1671161) (@lem1671163)). Qed.
Lemma lem1671165 : term230 = False.
Proof. exact (TRANS (@lem1671153) (@lem1671164)). Qed.
Lemma lem1671166 (u : real) (a : real) (x : real) (b : real) (y : real) (v : real) (h1 : term199 u a x b y v) : False.
Proof. exact (EQ_MP (@lem1671165) (@lem1671150 u a x b y v h1)). Qed.
Lemma lem1671167 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term235 u a x v b y.
Proof. exact (h1). Qed.
Lemma lem1671168 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term198 a x v b y.
Proof. exact (proj2 (@lem1671167 u a x v b y h1)). Qed.
Lemma lem1671170 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term194 v b y.
Proof. exact (proj2 (@lem1671168 u a x v b y h1)). Qed.
Lemma lem1671172 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term190 v b y.
Proof. exact (proj2 (@lem1671170 u a x v b y h1)). Qed.
Lemma lem1671173 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term127 b y.
Proof. exact (proj1 (@lem1671170 u a x v b y h1)). Qed.
Lemma lem1671174 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term186 v b y.
Proof. exact (proj2 (@lem1671172 u a x v b y h1)). Qed.
Lemma lem1671176 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term182 v b y.
Proof. exact (proj2 (@lem1671174 u a x v b y h1)). Qed.
Lemma lem1671178 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term164 b y.
Proof. exact (proj2 (@lem1671176 u a x v b y h1)). Qed.
Lemma lem1671181 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1671182 : term201 = term202.
Proof. exact (@lem1671181 (NUMERAL 0) term120). Qed.
Lemma lem1671183 : term203 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1671184 (h1 : term203 = (BIT1 0)) : term202 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1671185 : (term203 = (BIT1 0)) = (term202 = True).
Proof. exact (prop_ext (fun h1 : term203 = (BIT1 0) => @lem1671184 h1) (fun h1 : term202 = True => @lem1671183)). Qed.
Lemma lem1671186 : term202 = True.
Proof. exact (EQ_MP (@lem1671185) (@lem1671183)). Qed.
Lemma lem1671187 : term201 = True.
Proof. exact (TRANS (@lem1671182) (@lem1671186)). Qed.
Lemma lem1671188 : True = term201.
Proof. exact (SYM (@lem1671187)). Qed.
Lemma lem1671189 : term201.
Proof. exact (EQ_MP (@lem1671188) (@lem0)). Qed.
Lemma lem1671190 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term236 b y.
Proof. exact (conj (@lem1671189) (@lem1671178 u a x v b y h1)). Qed.
Lemma lem1671192 (x : real) (y : real) : term205 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1671193 (b : real) (y : real) : term237 b y.
Proof. exact (@lem1671192 term49 (term161 b y)). Qed.
Lemma lem1671194 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term238 b y.
Proof. exact (@lem1671193 b y (@lem1671190 u a x v b y h1)). Qed.
Lemma lem1671195 (b : real) (y : real) : (term239 b y) = (term161 b y).
Proof. exact (@lem1483460 (term161 b y)). Qed.
Lemma lem1671196 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1671197 (b : real) (y : real) : (term240 b y) = (term163 b y).
Proof. exact (MK_COMB (@lem1671196) (@lem1671195 b y)). Qed.
Lemma lem1671198 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671199 (b : real) (y : real) : (term238 b y) = (term164 b y).
Proof. exact (MK_COMB (@lem1671197 b y) (@lem1671198)). Qed.
Lemma lem1671200 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term164 b y.
Proof. exact (EQ_MP (@lem1671199 b y) (@lem1671194 u a x v b y h1)). Qed.
Lemma lem1671202 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1671203 : term201 = term202.
Proof. exact (@lem1671202 (NUMERAL 0) term120). Qed.
Lemma lem1671204 : term203 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1671205 (h1 : term203 = (BIT1 0)) : term202 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1671206 : (term203 = (BIT1 0)) = (term202 = True).
Proof. exact (prop_ext (fun h1 : term203 = (BIT1 0) => @lem1671205 h1) (fun h1 : term202 = True => @lem1671204)). Qed.
Lemma lem1671207 : term202 = True.
Proof. exact (EQ_MP (@lem1671206) (@lem1671204)). Qed.
Lemma lem1671208 : term201 = True.
Proof. exact (TRANS (@lem1671203) (@lem1671207)). Qed.
Lemma lem1671209 : True = term201.
Proof. exact (SYM (@lem1671208)). Qed.
Lemma lem1671210 : term201.
Proof. exact (EQ_MP (@lem1671209) (@lem0)). Qed.
Lemma lem1671211 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term241 b y.
Proof. exact (conj (@lem1671210) (@lem1671173 u a x v b y h1)). Qed.
Lemma lem1671213 (x : real) (y : real) : term242 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1671214 (b : real) (y : real) : term243 b y.
Proof. exact (@lem1671213 term49 (term124 b y)). Qed.
Lemma lem1671215 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term244 b y.
Proof. exact (@lem1671214 b y (@lem1671211 u a x v b y h1)). Qed.
Lemma lem1671216 (b : real) (y : real) : (term245 b y) = (term124 b y).
Proof. exact (@lem1483460 (term124 b y)). Qed.
Lemma lem1671217 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1671218 (b : real) (y : real) : (term246 b y) = (term126 b y).
Proof. exact (MK_COMB (@lem1671217) (@lem1671216 b y)). Qed.
Lemma lem1671219 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671220 (b : real) (y : real) : (term244 b y) = (term127 b y).
Proof. exact (MK_COMB (@lem1671218 b y) (@lem1671219)). Qed.
Lemma lem1671221 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term127 b y.
Proof. exact (EQ_MP (@lem1671220 b y) (@lem1671215 u a x v b y h1)). Qed.
Lemma lem1671222 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term247 b y.
Proof. exact (conj (@lem1671221 u a x v b y h1) (@lem1671200 u a x v b y h1)). Qed.
Lemma lem1671224 (x : real) (y : real) : term248 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1671225 (b : real) (y : real) : term249 b y.
Proof. exact (@lem1671224 (term124 b y) (term161 b y)). Qed.
Lemma lem1671226 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term250 b y.
Proof. exact (@lem1671225 b y (@lem1671222 u a x v b y h1)). Qed.
Lemma lem1671227 (b : real) (y : real) : (term251 b y) = (term252 b y).
Proof. exact (@lem1483480 b (term155 b) (term155 y) y). Qed.
Lemma lem1671228 (b : real) : (term221 b) = (term222 b).
Proof. exact (@lem1483442 term147 b). Qed.
Lemma lem1671230 (m : nat) : (term223 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1671231 : term224 = term35.
Proof. exact (@lem1671230 term120). Qed.
Lemma lem1671232 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1671233 : term225 = term61.
Proof. exact (MK_COMB (@lem1671232) (@lem1671231)). Qed.
Lemma lem1671234 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1671235 (b : real) : (term222 b) = (term41 b).
Proof. exact (MK_COMB (@lem1671233) (@lem1671234 b)). Qed.
Lemma lem1671236 (b : real) : (term221 b) = (term41 b).
Proof. exact (TRANS (@lem1671228 b) (@lem1671235 b)). Qed.
Lemma lem1671237 (b : real) : (term41 b) = term35.
Proof. exact (@lem1483446 b). Qed.
Lemma lem1671238 (b : real) : (term221 b) = term35.
Proof. exact (TRANS (@lem1671236 b) (@lem1671237 b)). Qed.
Lemma lem1671239 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1671240 (b : real) : (term226 b) = term47.
Proof. exact (MK_COMB (@lem1671239) (@lem1671238 b)). Qed.
Lemma lem1671241 (y : real) : (term253 y) = (term222 y).
Proof. exact (@lem1483440 term147 y). Qed.
Lemma lem1671243 (m : nat) : (term223 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1671244 : term224 = term35.
Proof. exact (@lem1671243 term120). Qed.
Lemma lem1671245 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1671246 : term225 = term61.
Proof. exact (MK_COMB (@lem1671245) (@lem1671244)). Qed.
Lemma lem1671247 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1671248 (y : real) : (term222 y) = (term41 y).
Proof. exact (MK_COMB (@lem1671246) (@lem1671247 y)). Qed.
Lemma lem1671249 (y : real) : (term253 y) = (term41 y).
Proof. exact (TRANS (@lem1671241 y) (@lem1671248 y)). Qed.
Lemma lem1671250 (y : real) : (term41 y) = term35.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1671251 (y : real) : (term253 y) = term35.
Proof. exact (TRANS (@lem1671249 y) (@lem1671250 y)). Qed.
Lemma lem1671252 (b : real) (y : real) : (term252 b y) = term131.
Proof. exact (MK_COMB (@lem1671240 b) (@lem1671251 y)). Qed.
Lemma lem1671253 (b : real) (y : real) : (term251 b y) = term131.
Proof. exact (TRANS (@lem1671227 b y) (@lem1671252 b y)). Qed.
Lemma lem1671254 : term131 = term35.
Proof. exact (@lem1483448 term35). Qed.
Lemma lem1671255 (b : real) (y : real) : (term251 b y) = term35.
Proof. exact (TRANS (@lem1671253 b y) (@lem1671254)). Qed.
Lemma lem1671256 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1671257 (b : real) (y : real) : (term254 b y) = term255.
Proof. exact (MK_COMB (@lem1671256) (@lem1671255 b y)). Qed.
Lemma lem1671258 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671259 (b : real) (y : real) : (term250 b y) = term256.
Proof. exact (MK_COMB (@lem1671257 b y) (@lem1671258)). Qed.
Lemma lem1671260 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : term256.
Proof. exact (EQ_MP (@lem1671259 b y) (@lem1671226 u a x v b y h1)). Qed.
Lemma lem1671262 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1671263 : term256 = term257.
Proof. exact (@lem1671262 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1671264 : term257 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1671265 : term256 = False.
Proof. exact (TRANS (@lem1671263) (@lem1671264)). Qed.
Lemma lem1671266 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term235 u a x v b y) : False.
Proof. exact (EQ_MP (@lem1671265) (@lem1671260 u a x v b y h1)). Qed.
Lemma lem1671267 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term196 u a x v b y) : False.
Proof. exact (or_elim (@lem1671074 u a x v b y h1) (fun h0 : term199 u a x b y v => @lem1671166 u a x b y v h0) (fun h0 : term235 u a x v b y => @lem1671266 u a x v b y h0)). Qed.
Lemma lem1671269 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term196 u a x v b y) : term196 u a x v b y.
Proof. exact (h1). Qed.
Lemma lem1671270 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term196 u a x v b y) : (term196 u a x v b y) = False.
Proof. exact (prop_ext (fun h2 : term196 u a x v b y => @lem1671267 u a x v b y h1) (fun h2 : False => @lem1671269 u a x v b y h1)). Qed.
Lemma lem1671271 (u : real) (a : real) (x : real) (v : real) (b : real) (y : real) (h1 : term196 u a x v b y) : False.
Proof. exact (EQ_MP (@lem1671270 u a x v b y h1) (@lem1671269 u a x v b y h1)). Qed.
Lemma lem1671272 (u : real) (x : real) (a : real) (v : real) (y : real) (b : real) (h1 : term114 u x a v y b) : term114 u x a v y b.
Proof. exact (h1). Qed.
Lemma lem1671273 (u : real) (x : real) (a : real) (v : real) (y : real) (b : real) (h1 : term114 u x a v y b) : term196 u a x v b y.
Proof. exact (EQ_MP (@lem1671064 u a x v b y) (@lem1671272 u x a v y b h1)). Qed.
Lemma lem1671274 (u : real) (x : real) (a : real) (v : real) (y : real) (b : real) (h1 : term114 u x a v y b) : (term196 u a x v b y) = False.
Proof. exact (prop_ext (fun h2 : term196 u a x v b y => @lem1671271 u a x v b y h2) (fun h2 : False => @lem1671273 u x a v y b h1)). Qed.
Lemma lem1671275 (u : real) (x : real) (a : real) (v : real) (y : real) (b : real) (h1 : term114 u x a v y b) : False.
Proof. exact (EQ_MP (@lem1671274 u x a v y b h1) (@lem1671273 u x a v y b h1)). Qed.
Lemma lem1671276 (u : real) (x : real) (a : real) (v : real) (y : real) (b : real) : term258 u x a v y b.
Proof. exact (fun h0 : term114 u x a v y b => @lem1671275 u x a v y b h0). Qed.
Lemma lem1671277 (u : real) (x : real) (a : real) (v : real) (y : real) (b : real) : term259 u x a v y b.
Proof. exact (@lem1386578 (term260 u x a v y b)). Qed.
Lemma lem1671278 (u : real) (x : real) (a : real) (v : real) (y : real) (b : real) : term260 u x a v y b.
Proof. exact (@lem1671277 u x a v y b (@lem1671276 u x a v y b)). Qed.
Lemma lem1671308 (u : real) (x : real) (a : real) : (term88 u x a) = (term89 u x a).
Proof. exact (@lem17045 (term90 u) (real_lt x a)). Qed.
Lemma lem1671310 (u : real) (v : real) : (term261 u v) = (term261 u v).
Proof. exact (eq_refl (term261 u v)). Qed.
Lemma lem1671311 (v : real) (u : real) (x : real) (a : real) : (term262 v u x a) = (term263 v u x a).
Proof. exact (MK_COMB (@lem1671310 u v) (@lem1671308 u x a)). Qed.
Lemma lem1671312 (v : real) (u : real) (x : real) (a : real) : (term264 v u x a) = (term262 v u x a).
Proof. exact (@lem17362 ((real_add u v) = term49) (term7 u x a)). Qed.
Lemma lem1671313 (v : real) (u : real) (x : real) (a : real) : (term264 v u x a) = (term263 v u x a).
Proof. exact (TRANS (@lem1671312 v u x a) (@lem1671311 v u x a)). Qed.
Lemma lem1671315 (v : real) : (term45 v) = (term45 v).
Proof. exact (eq_refl (term45 v)). Qed.
Lemma lem1671316 (v : real) (u : real) (x : real) (a : real) : (term265 v u x a) = (term266 v u x a).
Proof. exact (MK_COMB (@lem1671315 v) (@lem1671313 v u x a)). Qed.
Lemma lem1671317 (v : real) (u : real) (x : real) (a : real) : (term267 v u x a) = (term265 v u x a).
Proof. exact (@lem17362 (term43 v) (term268 v u x a)). Qed.
Lemma lem1671318 (v : real) (u : real) (x : real) (a : real) : (term267 v u x a) = (term266 v u x a).
Proof. exact (TRANS (@lem1671317 v u x a) (@lem1671316 v u x a)). Qed.
Lemma lem1671320 (u : real) : (term45 u) = (term45 u).
Proof. exact (eq_refl (term45 u)). Qed.
Lemma lem1671321 (v : real) (u : real) (x : real) (a : real) : (term269 v u x a) = (term270 v u x a).
Proof. exact (MK_COMB (@lem1671320 u) (@lem1671318 v u x a)). Qed.
Lemma lem1671322 (v : real) (u : real) (x : real) (a : real) : (term271 v u x a) = (term269 v u x a).
Proof. exact (@lem17362 (term43 u) (term272 v u x a)). Qed.
Lemma lem1671323 (v : real) (u : real) (x : real) (a : real) : (term271 v u x a) = (term270 v u x a).
Proof. exact (TRANS (@lem1671322 v u x a) (@lem1671321 v u x a)). Qed.
Lemma lem1671325 (y : real) (b : real) : (term54 y b) = (term54 y b).
Proof. exact (eq_refl (term54 y b)). Qed.
Lemma lem1671326 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : (term273 y b v u x a) = (term274 y b v u x a).
Proof. exact (MK_COMB (@lem1671325 y b) (@lem1671323 v u x a)). Qed.
Lemma lem1671327 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : (term275 y b v u x a) = (term273 y b v u x a).
Proof. exact (@lem17362 (real_lt y b) (term276 v u x a)). Qed.
Lemma lem1671328 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : (term275 y b v u x a) = (term274 y b v u x a).
Proof. exact (TRANS (@lem1671327 y b v u x a) (@lem1671326 y b v u x a)). Qed.
Lemma lem1671330 (x : real) (a : real) : (term54 x a) = (term54 x a).
Proof. exact (eq_refl (term54 x a)). Qed.
Lemma lem1671331 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : (term277 y b v u x a) = (term278 y b v u x a).
Proof. exact (MK_COMB (@lem1671330 x a) (@lem1671328 y b v u x a)). Qed.
Lemma lem1671332 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : (term279 y b v u x a) = (term277 y b v u x a).
Proof. exact (@lem17362 (real_lt x a) (term280 y b v u x a)). Qed.
Lemma lem1671333 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : (term279 y b v u x a) = (term278 y b v u x a).
Proof. exact (TRANS (@lem1671332 y b v u x a) (@lem1671331 y b v u x a)). Qed.
Lemma lem1671335 (u : real) : (term281 u) = (term281 u).
Proof. exact (eq_refl (term281 u)). Qed.
Lemma lem1671336 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : (term282 y b v u x a) = (term283 y b v u x a).
Proof. exact (MK_COMB (@lem1671335 u) (@lem1671333 y b v u x a)). Qed.
Lemma lem1671337 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : (term284 y b v u x a) = (term282 y b v u x a).
Proof. exact (@lem17362 (term37 u) (term285 y b v u x a)). Qed.
Lemma lem1671375 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : (term284 y b v u x a) = (term283 y b v u x a).
Proof. exact (TRANS (@lem1671337 y b v u x a) (@lem1671336 y b v u x a)). Qed.
Lemma lem1671376 (u : real) : (term37 u) = (term286 u).
Proof. exact (@lem1483554 u term35). Qed.
Lemma lem1671382 (u : real) : (term116 u) = (term117 u).
Proof. exact (@lem1483519 u term35). Qed.
Lemma lem1671384 (x : nat) : (term118 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1671385 : term119 = term35.
Proof. exact (@lem1671384 term120). Qed.
Lemma lem1671386 (u : real) : (real_add u) = (real_add u).
Proof. exact (eq_refl (real_add u)). Qed.
Lemma lem1671387 (u : real) : (term117 u) = (term121 u).
Proof. exact (MK_COMB (@lem1671386 u) (@lem1671385)). Qed.
Lemma lem1671388 (u : real) : (term121 u) = u.
Proof. exact (@lem1483450 u). Qed.
Lemma lem1671389 (u : real) : (term117 u) = u.
Proof. exact (TRANS (@lem1671387 u) (@lem1671388 u)). Qed.
Lemma lem1671391 (u : real) : (term116 u) = u.
Proof. exact (TRANS (@lem1671382 u) (@lem1671389 u)). Qed.
Lemma lem1671392 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1671393 (u : real) : (term287 u) = (real_neg u).
Proof. exact (MK_COMB (@lem1671392) (@lem1671391 u)). Qed.
Lemma lem1671396 (u : real) : (real_neg u) = (term155 u).
Proof. exact (@lem1483512 u). Qed.
Lemma lem1671397 (u : real) : (term288 u) = (term288 u).
Proof. exact (eq_refl (term288 u)). Qed.
Lemma lem1671398 (u : real) : ((term287 u) = (real_neg u)) = ((term287 u) = (term155 u)).
Proof. exact (MK_COMB (@lem1671397 u) (@lem1671396 u)). Qed.
Lemma lem1671399 (u : real) : (term287 u) = (term155 u).
Proof. exact (EQ_MP (@lem1671398 u) (@lem1671393 u)). Qed.
Lemma lem1671400 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1671401 (u : real) : (term289 u) = (term290 u).
Proof. exact (MK_COMB (@lem1671400) (@lem1671399 u)). Qed.
Lemma lem1671402 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671403 (u : real) : (term291 u) = (term292 u).
Proof. exact (MK_COMB (@lem1671401 u) (@lem1671402)). Qed.
Lemma lem1671404 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1671405 (u : real) : (term293 u) = (real_gt u).
Proof. exact (MK_COMB (@lem1671404) (@lem1671391 u)). Qed.
Lemma lem1671406 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671407 (u : real) : (term294 u) = (term295 u).
Proof. exact (MK_COMB (@lem1671405 u) (@lem1671406)). Qed.
Lemma lem1671408 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1671409 (u : real) : (term296 u) = (term297 u).
Proof. exact (MK_COMB (@lem1671408) (@lem1671407 u)). Qed.
Lemma lem1671410 (u : real) : (term286 u) = (term298 u).
Proof. exact (MK_COMB (@lem1671409 u) (@lem1671403 u)). Qed.
Lemma lem1671411 (u : real) : (term37 u) = (term298 u).
Proof. exact (TRANS (@lem1671376 u) (@lem1671410 u)). Qed.
Lemma lem1671412 (a : real) (x : real) : (real_lt x a) = (term123 a x).
Proof. exact (@lem1483521 a x). Qed.
Lemma lem1671425 (a : real) (x : real) : (real_sub a x) = (term124 a x).
Proof. exact (@lem1483519 a x). Qed.
Lemma lem1671426 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1671427 (a : real) (x : real) : (term125 a x) = (term126 a x).
Proof. exact (MK_COMB (@lem1671426) (@lem1671425 a x)). Qed.
Lemma lem1671428 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671429 (a : real) (x : real) : (term123 a x) = (term127 a x).
Proof. exact (MK_COMB (@lem1671427 a x) (@lem1671428)). Qed.
Lemma lem1671430 (a : real) (x : real) : (real_lt x a) = (term127 a x).
Proof. exact (TRANS (@lem1671412 a x) (@lem1671429 a x)). Qed.
Lemma lem1671431 (b : real) (y : real) : (real_lt y b) = (term123 b y).
Proof. exact (@lem1483521 b y). Qed.
Lemma lem1671444 (b : real) (y : real) : (real_sub b y) = (term124 b y).
Proof. exact (@lem1483519 b y). Qed.
Lemma lem1671445 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1671446 (b : real) (y : real) : (term125 b y) = (term126 b y).
Proof. exact (MK_COMB (@lem1671445) (@lem1671444 b y)). Qed.
Lemma lem1671447 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671448 (b : real) (y : real) : (term123 b y) = (term127 b y).
Proof. exact (MK_COMB (@lem1671446 b y) (@lem1671447)). Qed.
Lemma lem1671449 (b : real) (y : real) : (real_lt y b) = (term127 b y).
Proof. exact (TRANS (@lem1671431 b y) (@lem1671448 b y)). Qed.
Lemma lem1671450 (u : real) : (term43 u) = (term135 u).
Proof. exact (@lem1483523 u term35). Qed.
Lemma lem1671456 (u : real) : (term116 u) = (term117 u).
Proof. exact (@lem1483519 u term35). Qed.
Lemma lem1671458 (x : nat) : (term118 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1671459 : term119 = term35.
Proof. exact (@lem1671458 term120). Qed.
Lemma lem1671460 (u : real) : (real_add u) = (real_add u).
Proof. exact (eq_refl (real_add u)). Qed.
Lemma lem1671461 (u : real) : (term117 u) = (term121 u).
Proof. exact (MK_COMB (@lem1671460 u) (@lem1671459)). Qed.
Lemma lem1671462 (u : real) : (term121 u) = u.
Proof. exact (@lem1483450 u). Qed.
Lemma lem1671463 (u : real) : (term117 u) = u.
Proof. exact (TRANS (@lem1671461 u) (@lem1671462 u)). Qed.
Lemma lem1671465 (u : real) : (term116 u) = u.
Proof. exact (TRANS (@lem1671456 u) (@lem1671463 u)). Qed.
Lemma lem1671466 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1671467 (u : real) : (term136 u) = (real_ge u).
Proof. exact (MK_COMB (@lem1671466) (@lem1671465 u)). Qed.
Lemma lem1671468 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671469 (u : real) : (term135 u) = (term137 u).
Proof. exact (MK_COMB (@lem1671467 u) (@lem1671468)). Qed.
Lemma lem1671470 (u : real) : (term43 u) = (term137 u).
Proof. exact (TRANS (@lem1671450 u) (@lem1671469 u)). Qed.
Lemma lem1671471 (v : real) : (term43 v) = (term135 v).
Proof. exact (@lem1483523 v term35). Qed.
Lemma lem1671477 (v : real) : (term116 v) = (term117 v).
Proof. exact (@lem1483519 v term35). Qed.
Lemma lem1671479 (x : nat) : (term118 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1671480 : term119 = term35.
Proof. exact (@lem1671479 term120). Qed.
Lemma lem1671481 (v : real) : (real_add v) = (real_add v).
Proof. exact (eq_refl (real_add v)). Qed.
Lemma lem1671482 (v : real) : (term117 v) = (term121 v).
Proof. exact (MK_COMB (@lem1671481 v) (@lem1671480)). Qed.
Lemma lem1671483 (v : real) : (term121 v) = v.
Proof. exact (@lem1483450 v). Qed.
Lemma lem1671484 (v : real) : (term117 v) = v.
Proof. exact (TRANS (@lem1671482 v) (@lem1671483 v)). Qed.
Lemma lem1671486 (v : real) : (term116 v) = v.
Proof. exact (TRANS (@lem1671477 v) (@lem1671484 v)). Qed.
Lemma lem1671487 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1671488 (v : real) : (term136 v) = (real_ge v).
Proof. exact (MK_COMB (@lem1671487) (@lem1671486 v)). Qed.
Lemma lem1671489 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671490 (v : real) : (term135 v) = (term137 v).
Proof. exact (MK_COMB (@lem1671488 v) (@lem1671489)). Qed.
Lemma lem1671491 (v : real) : (term43 v) = (term137 v).
Proof. exact (TRANS (@lem1671471 v) (@lem1671490 v)). Qed.
Lemma lem1671492 (u : real) (v : real) : ((real_add u v) = term49) = ((term299 u v) = term35).
Proof. exact (@lem1483529 (real_add u v) term49). Qed.
Lemma lem1671504 (u : real) (v : real) : (term299 u v) = (term300 u v).
Proof. exact (@lem1483519 (real_add u v) term49). Qed.
Lemma lem1671506 (m : nat) (n : nat) : (term140 m n) = (term141 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1671507 : term142 = term143.
Proof. exact (@lem1671506 term120 term120). Qed.
Lemma lem1671508 : (term144 = (BIT1 0)) = (term145 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1671509 : term145 = term120.
Proof. exact (EQ_MP (@lem1671508) (@lem940073)). Qed.
Lemma lem1671510 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1671511 : term146 = term49.
Proof. exact (MK_COMB (@lem1671510) (@lem1671509)). Qed.
Lemma lem1671512 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1671513 : term143 = term147.
Proof. exact (MK_COMB (@lem1671512) (@lem1671511)). Qed.
Lemma lem1671514 : term142 = term147.
Proof. exact (TRANS (@lem1671507) (@lem1671513)). Qed.
Lemma lem1671515 (u : real) (v : real) : (term301 u v) = (term301 u v).
Proof. exact (eq_refl (term301 u v)). Qed.
Lemma lem1671516 (u : real) (v : real) : (term300 u v) = (term302 u v).
Proof. exact (MK_COMB (@lem1671515 u v) (@lem1671514)). Qed.
Lemma lem1671521 (u : real) (v : real) : (term302 u v) = (term303 u v).
Proof. exact (@lem1483482 u v term147). Qed.
Lemma lem1671522 (u : real) (v : real) : (term300 u v) = (term303 u v).
Proof. exact (TRANS (@lem1671516 u v) (@lem1671521 u v)). Qed.
Lemma lem1671524 (u : real) (v : real) : (term299 u v) = (term303 u v).
Proof. exact (TRANS (@lem1671504 u v) (@lem1671522 u v)). Qed.
Lemma lem1671525 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1671526 (u : real) (v : real) : (term304 u v) = (term305 u v).
Proof. exact (MK_COMB (@lem1671525) (@lem1671524 u v)). Qed.
Lemma lem1671527 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671528 (u : real) (v : real) : ((term299 u v) = term35) = ((term303 u v) = term35).
Proof. exact (MK_COMB (@lem1671526 u v) (@lem1671527)). Qed.
Lemma lem1671529 (u : real) (v : real) : ((real_add u v) = term49) = ((term303 u v) = term35).
Proof. exact (TRANS (@lem1671492 u v) (@lem1671528 u v)). Qed.
Lemma lem1671530 (u : real) : (term151 u) = (term152 u).
Proof. exact (@lem1483531 term35 u). Qed.
Lemma lem1671536 (u : real) : (term153 u) = (term154 u).
Proof. exact (@lem1483519 term35 u). Qed.
Lemma lem1671541 (u : real) : (term154 u) = (term155 u).
Proof. exact (@lem1483448 (term155 u)). Qed.
Lemma lem1671543 (u : real) : (term153 u) = (term155 u).
Proof. exact (TRANS (@lem1671536 u) (@lem1671541 u)). Qed.
Lemma lem1671544 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1671545 (u : real) : (term156 u) = (term157 u).
Proof. exact (MK_COMB (@lem1671544) (@lem1671543 u)). Qed.
Lemma lem1671546 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671547 (u : real) : (term152 u) = (term158 u).
Proof. exact (MK_COMB (@lem1671545 u) (@lem1671546)). Qed.
Lemma lem1671548 (u : real) : (term151 u) = (term158 u).
Proof. exact (TRANS (@lem1671530 u) (@lem1671547 u)). Qed.
Lemma lem1671549 (x : real) (a : real) : (term159 x a) = (term160 x a).
Proof. exact (@lem1483531 x a). Qed.
Lemma lem1671555 (x : real) (a : real) : (real_sub x a) = (term124 x a).
Proof. exact (@lem1483519 x a). Qed.
Lemma lem1671560 (a : real) (x : real) : (term124 x a) = (term161 a x).
Proof. exact (@lem1483488 (term155 a) x). Qed.
Lemma lem1671562 (a : real) (x : real) : (real_sub x a) = (term161 a x).
Proof. exact (TRANS (@lem1671555 x a) (@lem1671560 a x)). Qed.
Lemma lem1671563 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1671564 (a : real) (x : real) : (term162 x a) = (term163 a x).
Proof. exact (MK_COMB (@lem1671563) (@lem1671562 a x)). Qed.
Lemma lem1671565 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671566 (a : real) (x : real) : (term160 x a) = (term164 a x).
Proof. exact (MK_COMB (@lem1671564 a x) (@lem1671565)). Qed.
Lemma lem1671567 (a : real) (x : real) : (term159 x a) = (term164 a x).
Proof. exact (TRANS (@lem1671549 x a) (@lem1671566 a x)). Qed.
Lemma lem1671568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1671569 (u : real) : (term165 u) = (term166 u).
Proof. exact (MK_COMB (@lem1671568) (@lem1671548 u)). Qed.
Lemma lem1671570 (u : real) (a : real) (x : real) : (term89 u x a) = (term167 u a x).
Proof. exact (MK_COMB (@lem1671569 u) (@lem1671567 a x)). Qed.
Lemma lem1671571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1671572 (u : real) (v : real) : (term261 u v) = (term306 u v).
Proof. exact (MK_COMB (@lem1671571) (@lem1671529 u v)). Qed.
Lemma lem1671573 (v : real) (u : real) (a : real) (x : real) : (term263 v u x a) = (term307 v u a x).
Proof. exact (MK_COMB (@lem1671572 u v) (@lem1671570 u a x)). Qed.
Lemma lem1671574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1671575 (v : real) : (term45 v) = (term170 v).
Proof. exact (MK_COMB (@lem1671574) (@lem1671491 v)). Qed.
Lemma lem1671576 (v : real) (u : real) (a : real) (x : real) : (term266 v u x a) = (term308 v u a x).
Proof. exact (MK_COMB (@lem1671575 v) (@lem1671573 v u a x)). Qed.
Lemma lem1671577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1671578 (u : real) : (term45 u) = (term170 u).
Proof. exact (MK_COMB (@lem1671577) (@lem1671470 u)). Qed.
Lemma lem1671579 (v : real) (u : real) (a : real) (x : real) : (term270 v u x a) = (term309 v u a x).
Proof. exact (MK_COMB (@lem1671578 u) (@lem1671576 v u a x)). Qed.
Lemma lem1671580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1671581 (b : real) (y : real) : (term54 y b) = (term174 b y).
Proof. exact (MK_COMB (@lem1671580) (@lem1671449 b y)). Qed.
Lemma lem1671582 (b : real) (y : real) (v : real) (u : real) (a : real) (x : real) : (term274 y b v u x a) = (term310 b y v u a x).
Proof. exact (MK_COMB (@lem1671581 b y) (@lem1671579 v u a x)). Qed.
Lemma lem1671583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1671584 (a : real) (x : real) : (term54 x a) = (term174 a x).
Proof. exact (MK_COMB (@lem1671583) (@lem1671430 a x)). Qed.
Lemma lem1671585 (b : real) (y : real) (v : real) (u : real) (a : real) (x : real) : (term278 y b v u x a) = (term311 b y v u a x).
Proof. exact (MK_COMB (@lem1671584 a x) (@lem1671582 b y v u a x)). Qed.
Lemma lem1671586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1671587 (u : real) : (term281 u) = (term312 u).
Proof. exact (MK_COMB (@lem1671586) (@lem1671411 u)). Qed.
Lemma lem1671588 (b : real) (y : real) (v : real) (u : real) (a : real) (x : real) : (term283 y b v u x a) = (term313 b y v u a x).
Proof. exact (MK_COMB (@lem1671587 u) (@lem1671585 b y v u a x)). Qed.
Lemma lem1671595 (b : real) (y : real) (v : real) (u : real) (a : real) (x : real) : (term284 y b v u x a) = (term313 b y v u a x).
Proof. exact (TRANS (@lem1671375 y b v u x a) (@lem1671588 b y v u a x)). Qed.
Lemma lem1671612 (u : real) (v : real) (a : real) (x : real) : (term307 v u a x) = (term314 u v a x).
Proof. exact (@lem19158 (term158 u) ((term303 u v) = term35) (term164 a x)). Qed.
Lemma lem1671615 (v : real) : (term170 v) = (term170 v).
Proof. exact (eq_refl (term170 v)). Qed.
Lemma lem1671616 (u : real) (v : real) (a : real) (x : real) : (term308 v u a x) = (term315 u v a x).
Proof. exact (MK_COMB (@lem1671615 v) (@lem1671612 u v a x)). Qed.
Lemma lem1671623 (u : real) (v : real) (a : real) (x : real) : (term315 u v a x) = (term316 u v a x).
Proof. exact (@lem19158 (term317 v u) (term137 v) (term318 u v a x)). Qed.
Lemma lem1671624 (u : real) (v : real) (a : real) (x : real) : (term308 v u a x) = (term316 u v a x).
Proof. exact (TRANS (@lem1671616 u v a x) (@lem1671623 u v a x)). Qed.
Lemma lem1671627 (u : real) : (term170 u) = (term170 u).
Proof. exact (eq_refl (term170 u)). Qed.
Lemma lem1671628 (u : real) (v : real) (a : real) (x : real) : (term309 v u a x) = (term319 u v a x).
Proof. exact (MK_COMB (@lem1671627 u) (@lem1671624 u v a x)). Qed.
Lemma lem1671635 (u : real) (v : real) (a : real) (x : real) : (term319 u v a x) = (term320 u v a x).
Proof. exact (@lem19158 (term321 v u) (term137 u) (term322 u v a x)). Qed.
Lemma lem1671636 (u : real) (v : real) (a : real) (x : real) : (term309 v u a x) = (term320 u v a x).
Proof. exact (TRANS (@lem1671628 u v a x) (@lem1671635 u v a x)). Qed.
Lemma lem1671639 (b : real) (y : real) : (term174 b y) = (term174 b y).
Proof. exact (eq_refl (term174 b y)). Qed.
Lemma lem1671640 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term310 b y v u a x) = (term323 b y u v a x).
Proof. exact (MK_COMB (@lem1671639 b y) (@lem1671636 u v a x)). Qed.
Lemma lem1671647 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term323 b y u v a x) = (term324 b y u v a x).
Proof. exact (@lem19158 (term325 v u) (term127 b y) (term326 u v a x)). Qed.
Lemma lem1671648 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term310 b y v u a x) = (term324 b y u v a x).
Proof. exact (TRANS (@lem1671640 b y u v a x) (@lem1671647 b y u v a x)). Qed.
Lemma lem1671651 (a : real) (x : real) : (term174 a x) = (term174 a x).
Proof. exact (eq_refl (term174 a x)). Qed.
Lemma lem1671652 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term311 b y v u a x) = (term327 b y u v a x).
Proof. exact (MK_COMB (@lem1671651 a x) (@lem1671648 b y u v a x)). Qed.
Lemma lem1671659 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term327 b y u v a x) = (term328 b y u v a x).
Proof. exact (@lem19158 (term329 b y v u) (term127 a x) (term330 b y u v a x)). Qed.
Lemma lem1671660 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term311 b y v u a x) = (term328 b y u v a x).
Proof. exact (TRANS (@lem1671652 b y u v a x) (@lem1671659 b y u v a x)). Qed.
Lemma lem1671667 (u : real) : (term312 u) = (term312 u).
Proof. exact (eq_refl (term312 u)). Qed.
Lemma lem1671668 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term313 b y v u a x) = (term331 b y u v a x).
Proof. exact (MK_COMB (@lem1671667 u) (@lem1671660 b y u v a x)). Qed.
Lemma lem1671669 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term331 b y u v a x) = (term332 b y u v a x).
Proof. exact (@lem19158 (term333 a x b y v u) (term298 u) (term334 b y u v a x)). Qed.
Lemma lem1671676 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term335 b y u v a x) = (term336 b y u v a x).
Proof. exact (@lem19367 (term295 u) (term292 u) (term334 b y u v a x)). Qed.
Lemma lem1671683 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) : (term337 a x b y v u) = (term338 a x b y v u).
Proof. exact (@lem19367 (term295 u) (term292 u) (term333 a x b y v u)). Qed.
Lemma lem1671684 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1671685 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) : (term339 a x b y v u) = (term340 a x b y v u).
Proof. exact (MK_COMB (@lem1671684) (@lem1671683 a x b y v u)). Qed.
Lemma lem1671686 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term332 b y u v a x) = (term341 b y u v a x).
Proof. exact (MK_COMB (@lem1671685 a x b y v u) (@lem1671676 b y u v a x)). Qed.
Lemma lem1671687 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term331 b y u v a x) = (term341 b y u v a x).
Proof. exact (TRANS (@lem1671669 b y u v a x) (@lem1671686 b y u v a x)). Qed.
Lemma lem1671688 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term313 b y v u a x) = (term341 b y u v a x).
Proof. exact (TRANS (@lem1671668 b y u v a x) (@lem1671687 b y u v a x)). Qed.
Lemma lem1671689 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term284 y b v u x a) = (term341 b y u v a x).
Proof. exact (TRANS (@lem1671595 b y v u a x) (@lem1671688 b y u v a x)). Qed.
Lemma lem1671711 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term341 b y u v a x) : term341 b y u v a x.
Proof. exact (h1). Qed.
Lemma lem1671712 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term338 a x b y v u) : term338 a x b y v u.
Proof. exact (h1). Qed.
Lemma lem1671713 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term342 a x b y v u.
Proof. exact (h1). Qed.
Lemma lem1671714 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term333 a x b y v u.
Proof. exact (proj2 (@lem1671713 a x b y v u h1)). Qed.
Lemma lem1671715 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term295 u.
Proof. exact (proj1 (@lem1671713 a x b y v u h1)). Qed.
Lemma lem1671716 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term329 b y v u.
Proof. exact (proj2 (@lem1671714 a x b y v u h1)). Qed.
Lemma lem1671718 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term325 v u.
Proof. exact (proj2 (@lem1671716 a x b y v u h1)). Qed.
Lemma lem1671720 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term321 v u.
Proof. exact (proj2 (@lem1671718 a x b y v u h1)). Qed.
Lemma lem1671722 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term317 v u.
Proof. exact (proj2 (@lem1671720 a x b y v u h1)). Qed.
Lemma lem1671724 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term158 u.
Proof. exact (proj2 (@lem1671722 a x b y v u h1)). Qed.
Lemma lem1671725 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : (term303 u v) = term35.
Proof. exact (proj1 (@lem1671722 a x b y v u h1)). Qed.
Lemma lem1671727 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1671728 : term201 = term202.
Proof. exact (@lem1671727 (NUMERAL 0) term120). Qed.
Lemma lem1671729 : term203 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1671730 (h1 : term203 = (BIT1 0)) : term202 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1671731 : (term203 = (BIT1 0)) = (term202 = True).
Proof. exact (prop_ext (fun h1 : term203 = (BIT1 0) => @lem1671730 h1) (fun h1 : term202 = True => @lem1671729)). Qed.
Lemma lem1671732 : term202 = True.
Proof. exact (EQ_MP (@lem1671731) (@lem1671729)). Qed.
Lemma lem1671733 : term201 = True.
Proof. exact (TRANS (@lem1671728) (@lem1671732)). Qed.
Lemma lem1671734 : True = term201.
Proof. exact (SYM (@lem1671733)). Qed.
Lemma lem1671735 : term201.
Proof. exact (EQ_MP (@lem1671734) (@lem0)). Qed.
Lemma lem1671736 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term204 u.
Proof. exact (conj (@lem1671735) (@lem1671724 a x b y v u h1)). Qed.
Lemma lem1671738 (x : real) (y : real) : term205 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1671739 (u : real) : term206 u.
Proof. exact (@lem1671738 term49 (term155 u)). Qed.
Lemma lem1671740 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term207 u.
Proof. exact (@lem1671739 u (@lem1671736 a x b y v u h1)). Qed.
Lemma lem1671741 (u : real) : (term208 u) = (term155 u).
Proof. exact (@lem1483460 (term155 u)). Qed.
Lemma lem1671742 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1671743 (u : real) : (term209 u) = (term157 u).
Proof. exact (MK_COMB (@lem1671742) (@lem1671741 u)). Qed.
Lemma lem1671744 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671745 (u : real) : (term207 u) = (term158 u).
Proof. exact (MK_COMB (@lem1671743 u) (@lem1671744)). Qed.
Lemma lem1671746 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term158 u.
Proof. exact (EQ_MP (@lem1671745 u) (@lem1671740 a x b y v u h1)). Qed.
Lemma lem1671748 (y : real) : term210 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1671749 (u : real) (v : real) : term343 u v.
Proof. exact (@lem1671748 (term303 u v)). Qed.
Lemma lem1671750 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term344 u v.
Proof. exact (@lem1671749 u v (@lem1671725 a x b y v u h1)). Qed.
Lemma lem1671751 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term345 u v.
Proof. exact (@lem1671750 a x b y v u h1 term49). Qed.
Lemma lem1671752 (u : real) (v : real) : (term345 u v) = ((term346 u v) = term35).
Proof. exact (eq_refl (term345 u v)). Qed.
Lemma lem1671753 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : (term346 u v) = term35.
Proof. exact (EQ_MP (@lem1671752 u v) (@lem1671751 a x b y v u h1)). Qed.
Lemma lem1671754 (u : real) (v : real) : (term346 u v) = (term303 u v).
Proof. exact (@lem1483460 (term303 u v)). Qed.
Lemma lem1671755 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1671756 (u : real) (v : real) : (term347 u v) = (term305 u v).
Proof. exact (MK_COMB (@lem1671755) (@lem1671754 u v)). Qed.
Lemma lem1671757 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671758 (u : real) (v : real) : ((term346 u v) = term35) = ((term303 u v) = term35).
Proof. exact (MK_COMB (@lem1671756 u v) (@lem1671757)). Qed.
Lemma lem1671759 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : (term303 u v) = term35.
Proof. exact (EQ_MP (@lem1671758 u v) (@lem1671753 a x b y v u h1)). Qed.
Lemma lem1671760 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term317 v u.
Proof. exact (conj (@lem1671759 a x b y v u h1) (@lem1671746 a x b y v u h1)). Qed.
Lemma lem1671762 (x : real) (y : real) : term216 x y.
Proof. exact (proj1 (@lem1483572 x y)). Qed.
Lemma lem1671763 (v : real) (u : real) : term348 v u.
Proof. exact (@lem1671762 (term303 u v) (term155 u)). Qed.
Lemma lem1671764 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term349 v u.
Proof. exact (@lem1671763 v u (@lem1671760 a x b y v u h1)). Qed.
Lemma lem1671765 (u : real) (v : real) : (term350 v u) = (term351 u v).
Proof. exact (@lem1483486 u (term155 u) (term148 v)). Qed.
Lemma lem1671766 (u : real) : (term221 u) = (term222 u).
Proof. exact (@lem1483442 term147 u). Qed.
Lemma lem1671768 (m : nat) : (term223 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1671769 : term224 = term35.
Proof. exact (@lem1671768 term120). Qed.
Lemma lem1671770 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1671771 : term225 = term61.
Proof. exact (MK_COMB (@lem1671770) (@lem1671769)). Qed.
Lemma lem1671772 (u : real) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem1671773 (u : real) : (term222 u) = (term41 u).
Proof. exact (MK_COMB (@lem1671771) (@lem1671772 u)). Qed.
Lemma lem1671774 (u : real) : (term221 u) = (term41 u).
Proof. exact (TRANS (@lem1671766 u) (@lem1671773 u)). Qed.
Lemma lem1671775 (u : real) : (term41 u) = term35.
Proof. exact (@lem1483446 u). Qed.
Lemma lem1671776 (u : real) : (term221 u) = term35.
Proof. exact (TRANS (@lem1671774 u) (@lem1671775 u)). Qed.
Lemma lem1671777 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1671778 (u : real) : (term226 u) = term47.
Proof. exact (MK_COMB (@lem1671777) (@lem1671776 u)). Qed.
Lemma lem1671779 (v : real) : (term148 v) = (term148 v).
Proof. exact (eq_refl (term148 v)). Qed.
Lemma lem1671780 (u : real) (v : real) : (term351 u v) = (term352 v).
Proof. exact (MK_COMB (@lem1671778 u) (@lem1671779 v)). Qed.
Lemma lem1671781 (u : real) (v : real) : (term350 v u) = (term352 v).
Proof. exact (TRANS (@lem1671765 u v) (@lem1671780 u v)). Qed.
Lemma lem1671782 (v : real) : (term352 v) = (term148 v).
Proof. exact (@lem1483448 (term148 v)). Qed.
Lemma lem1671783 (u : real) (v : real) : (term350 v u) = (term148 v).
Proof. exact (TRANS (@lem1671781 u v) (@lem1671782 v)). Qed.
Lemma lem1671784 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1671785 (u : real) (v : real) : (term353 v u) = (term354 v).
Proof. exact (MK_COMB (@lem1671784) (@lem1671783 u v)). Qed.
Lemma lem1671786 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671787 (u : real) (v : real) : (term349 v u) = (term355 v).
Proof. exact (MK_COMB (@lem1671785 u v) (@lem1671786)). Qed.
Lemma lem1671788 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term355 v.
Proof. exact (EQ_MP (@lem1671787 u v) (@lem1671764 a x b y v u h1)). Qed.
Lemma lem1671790 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1671791 : term201 = term202.
Proof. exact (@lem1671790 (NUMERAL 0) term120). Qed.
Lemma lem1671792 : term203 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1671793 (h1 : term203 = (BIT1 0)) : term202 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1671794 : (term203 = (BIT1 0)) = (term202 = True).
Proof. exact (prop_ext (fun h1 : term203 = (BIT1 0) => @lem1671793 h1) (fun h1 : term202 = True => @lem1671792)). Qed.
Lemma lem1671795 : term202 = True.
Proof. exact (EQ_MP (@lem1671794) (@lem1671792)). Qed.
Lemma lem1671796 : term201 = True.
Proof. exact (TRANS (@lem1671791) (@lem1671795)). Qed.
Lemma lem1671797 : True = term201.
Proof. exact (SYM (@lem1671796)). Qed.
Lemma lem1671798 : term201.
Proof. exact (EQ_MP (@lem1671797) (@lem0)). Qed.
Lemma lem1671799 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term356 v.
Proof. exact (conj (@lem1671798) (@lem1671788 a x b y v u h1)). Qed.
Lemma lem1671801 (x : real) (y : real) : term205 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1671802 (v : real) : term357 v.
Proof. exact (@lem1671801 term49 (term148 v)). Qed.
Lemma lem1671803 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term358 v.
Proof. exact (@lem1671802 v (@lem1671799 a x b y v u h1)). Qed.
Lemma lem1671804 (v : real) : (term214 v) = (term148 v).
Proof. exact (@lem1483460 (term148 v)). Qed.
Lemma lem1671805 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1671806 (v : real) : (term359 v) = (term354 v).
Proof. exact (MK_COMB (@lem1671805) (@lem1671804 v)). Qed.
Lemma lem1671807 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671808 (v : real) : (term358 v) = (term355 v).
Proof. exact (MK_COMB (@lem1671806 v) (@lem1671807)). Qed.
Lemma lem1671809 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term355 v.
Proof. exact (EQ_MP (@lem1671808 v) (@lem1671803 a x b y v u h1)). Qed.
Lemma lem1671811 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1671812 : term201 = term202.
Proof. exact (@lem1671811 (NUMERAL 0) term120). Qed.
Lemma lem1671813 : term203 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1671814 (h1 : term203 = (BIT1 0)) : term202 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1671815 : (term203 = (BIT1 0)) = (term202 = True).
Proof. exact (prop_ext (fun h1 : term203 = (BIT1 0) => @lem1671814 h1) (fun h1 : term202 = True => @lem1671813)). Qed.
Lemma lem1671816 : term202 = True.
Proof. exact (EQ_MP (@lem1671815) (@lem1671813)). Qed.
Lemma lem1671817 : term201 = True.
Proof. exact (TRANS (@lem1671812) (@lem1671816)). Qed.
Lemma lem1671818 : True = term201.
Proof. exact (SYM (@lem1671817)). Qed.
Lemma lem1671819 : term201.
Proof. exact (EQ_MP (@lem1671818) (@lem0)). Qed.
Lemma lem1671820 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term360 u.
Proof. exact (conj (@lem1671819) (@lem1671715 a x b y v u h1)). Qed.
Lemma lem1671822 (x : real) (y : real) : term242 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1671823 (u : real) : term361 u.
Proof. exact (@lem1671822 term49 u). Qed.
Lemma lem1671824 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term362 u.
Proof. exact (@lem1671823 u (@lem1671820 a x b y v u h1)). Qed.
Lemma lem1671825 (u : real) : (term363 u) = u.
Proof. exact (@lem1483460 u). Qed.
Lemma lem1671826 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1671827 (u : real) : (term364 u) = (real_gt u).
Proof. exact (MK_COMB (@lem1671826) (@lem1671825 u)). Qed.
Lemma lem1671828 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671829 (u : real) : (term362 u) = (term295 u).
Proof. exact (MK_COMB (@lem1671827 u) (@lem1671828)). Qed.
Lemma lem1671830 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term295 u.
Proof. exact (EQ_MP (@lem1671829 u) (@lem1671824 a x b y v u h1)). Qed.
Lemma lem1671832 (y : real) : term210 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1671833 (u : real) (v : real) : term343 u v.
Proof. exact (@lem1671832 (term303 u v)). Qed.
Lemma lem1671834 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term344 u v.
Proof. exact (@lem1671833 u v (@lem1671725 a x b y v u h1)). Qed.
Lemma lem1671835 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term365 u v.
Proof. exact (@lem1671834 a x b y v u h1 term147). Qed.
Lemma lem1671836 (u : real) (v : real) : (term365 u v) = ((term366 u v) = term35).
Proof. exact (eq_refl (term365 u v)). Qed.
Lemma lem1671837 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : (term366 u v) = term35.
Proof. exact (EQ_MP (@lem1671836 u v) (@lem1671835 a x b y v u h1)). Qed.
Lemma lem1671838 (u : real) (v : real) : (term366 u v) = (term367 u v).
Proof. exact (@lem1483508 u term147 (term148 v)). Qed.
Lemma lem1671839 (v : real) : (term368 v) = (term369 v).
Proof. exact (@lem1483508 v term147 term147). Qed.
Lemma lem1671841 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1671842 : term372 = term146.
Proof. exact (@lem1671841 term120 term120). Qed.
Lemma lem1671843 : (term144 = (BIT1 0)) = (term145 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1671844 : term145 = term120.
Proof. exact (EQ_MP (@lem1671843) (@lem940073)). Qed.
Lemma lem1671845 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1671846 : term146 = term49.
Proof. exact (MK_COMB (@lem1671845) (@lem1671844)). Qed.
Lemma lem1671847 : term372 = term49.
Proof. exact (TRANS (@lem1671842) (@lem1671846)). Qed.
Lemma lem1671850 (v : real) : (term373 v) = (term373 v).
Proof. exact (eq_refl (term373 v)). Qed.
Lemma lem1671851 (v : real) : (term369 v) = (term374 v).
Proof. exact (MK_COMB (@lem1671850 v) (@lem1671847)). Qed.
Lemma lem1671852 (v : real) : (term368 v) = (term374 v).
Proof. exact (TRANS (@lem1671839 v) (@lem1671851 v)). Qed.
Lemma lem1671855 (u : real) : (term373 u) = (term373 u).
Proof. exact (eq_refl (term373 u)). Qed.
Lemma lem1671856 (u : real) (v : real) : (term367 u v) = (term375 u v).
Proof. exact (MK_COMB (@lem1671855 u) (@lem1671852 v)). Qed.
Lemma lem1671857 (u : real) (v : real) : (term366 u v) = (term375 u v).
Proof. exact (TRANS (@lem1671838 u v) (@lem1671856 u v)). Qed.
Lemma lem1671858 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1671859 (u : real) (v : real) : (term376 u v) = (term377 u v).
Proof. exact (MK_COMB (@lem1671858) (@lem1671857 u v)). Qed.
Lemma lem1671860 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671861 (u : real) (v : real) : ((term366 u v) = term35) = ((term375 u v) = term35).
Proof. exact (MK_COMB (@lem1671859 u v) (@lem1671860)). Qed.
Lemma lem1671862 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : (term375 u v) = term35.
Proof. exact (EQ_MP (@lem1671861 u v) (@lem1671837 a x b y v u h1)). Qed.
Lemma lem1671863 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term378 v u.
Proof. exact (conj (@lem1671862 a x b y v u h1) (@lem1671830 a x b y v u h1)). Qed.
Lemma lem1671865 (x : real) (y : real) : term379 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1671866 (v : real) (u : real) : term380 v u.
Proof. exact (@lem1671865 (term375 u v) u). Qed.
Lemma lem1671867 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term381 v u.
Proof. exact (@lem1671866 v u (@lem1671863 a x b y v u h1)). Qed.
Lemma lem1671868 (u : real) (v : real) : (term382 v u) = (term383 u v).
Proof. exact (@lem1483486 (term155 u) u (term374 v)). Qed.
Lemma lem1671869 (u : real) : (term253 u) = (term222 u).
Proof. exact (@lem1483440 term147 u). Qed.
Lemma lem1671871 (m : nat) : (term223 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1671872 : term224 = term35.
Proof. exact (@lem1671871 term120). Qed.
Lemma lem1671873 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1671874 : term225 = term61.
Proof. exact (MK_COMB (@lem1671873) (@lem1671872)). Qed.
Lemma lem1671875 (u : real) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem1671876 (u : real) : (term222 u) = (term41 u).
Proof. exact (MK_COMB (@lem1671874) (@lem1671875 u)). Qed.
Lemma lem1671877 (u : real) : (term253 u) = (term41 u).
Proof. exact (TRANS (@lem1671869 u) (@lem1671876 u)). Qed.
Lemma lem1671878 (u : real) : (term41 u) = term35.
Proof. exact (@lem1483446 u). Qed.
Lemma lem1671879 (u : real) : (term253 u) = term35.
Proof. exact (TRANS (@lem1671877 u) (@lem1671878 u)). Qed.
Lemma lem1671880 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1671881 (u : real) : (term384 u) = term47.
Proof. exact (MK_COMB (@lem1671880) (@lem1671879 u)). Qed.
Lemma lem1671882 (v : real) : (term374 v) = (term374 v).
Proof. exact (eq_refl (term374 v)). Qed.
Lemma lem1671883 (u : real) (v : real) : (term383 u v) = (term385 v).
Proof. exact (MK_COMB (@lem1671881 u) (@lem1671882 v)). Qed.
Lemma lem1671884 (u : real) (v : real) : (term382 v u) = (term385 v).
Proof. exact (TRANS (@lem1671868 u v) (@lem1671883 u v)). Qed.
Lemma lem1671885 (v : real) : (term385 v) = (term374 v).
Proof. exact (@lem1483448 (term374 v)). Qed.
Lemma lem1671886 (u : real) (v : real) : (term382 v u) = (term374 v).
Proof. exact (TRANS (@lem1671884 u v) (@lem1671885 v)). Qed.
Lemma lem1671887 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1671888 (u : real) (v : real) : (term386 v u) = (term387 v).
Proof. exact (MK_COMB (@lem1671887) (@lem1671886 u v)). Qed.
Lemma lem1671889 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671890 (u : real) (v : real) : (term381 v u) = (term388 v).
Proof. exact (MK_COMB (@lem1671888 u v) (@lem1671889)). Qed.
Lemma lem1671891 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term388 v.
Proof. exact (EQ_MP (@lem1671890 u v) (@lem1671867 a x b y v u h1)). Qed.
Lemma lem1671893 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1671894 : term201 = term202.
Proof. exact (@lem1671893 (NUMERAL 0) term120). Qed.
Lemma lem1671895 : term203 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1671896 (h1 : term203 = (BIT1 0)) : term202 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1671897 : (term203 = (BIT1 0)) = (term202 = True).
Proof. exact (prop_ext (fun h1 : term203 = (BIT1 0) => @lem1671896 h1) (fun h1 : term202 = True => @lem1671895)). Qed.
Lemma lem1671898 : term202 = True.
Proof. exact (EQ_MP (@lem1671897) (@lem1671895)). Qed.
Lemma lem1671899 : term201 = True.
Proof. exact (TRANS (@lem1671894) (@lem1671898)). Qed.
Lemma lem1671900 : True = term201.
Proof. exact (SYM (@lem1671899)). Qed.
Lemma lem1671901 : term201.
Proof. exact (EQ_MP (@lem1671900) (@lem0)). Qed.
Lemma lem1671902 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term389 v.
Proof. exact (conj (@lem1671901) (@lem1671891 a x b y v u h1)). Qed.
Lemma lem1671904 (x : real) (y : real) : term242 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1671905 (v : real) : term390 v.
Proof. exact (@lem1671904 term49 (term374 v)). Qed.
Lemma lem1671906 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term391 v.
Proof. exact (@lem1671905 v (@lem1671902 a x b y v u h1)). Qed.
Lemma lem1671907 (v : real) : (term392 v) = (term374 v).
Proof. exact (@lem1483460 (term374 v)). Qed.
Lemma lem1671908 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1671909 (v : real) : (term393 v) = (term387 v).
Proof. exact (MK_COMB (@lem1671908) (@lem1671907 v)). Qed.
Lemma lem1671910 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671911 (v : real) : (term391 v) = (term388 v).
Proof. exact (MK_COMB (@lem1671909 v) (@lem1671910)). Qed.
Lemma lem1671912 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term388 v.
Proof. exact (EQ_MP (@lem1671911 v) (@lem1671906 a x b y v u h1)). Qed.
Lemma lem1671913 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term394 v.
Proof. exact (conj (@lem1671912 a x b y v u h1) (@lem1671809 a x b y v u h1)). Qed.
Lemma lem1671915 (x : real) (y : real) : term248 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1671916 (v : real) : term395 v.
Proof. exact (@lem1671915 (term374 v) (term148 v)). Qed.
Lemma lem1671917 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term396 v.
Proof. exact (@lem1671916 v (@lem1671913 a x b y v u h1)). Qed.
Lemma lem1671918 (v : real) : (term397 v) = (term398 v).
Proof. exact (@lem1483480 (term155 v) v term49 term147). Qed.
Lemma lem1671919 (v : real) : (term253 v) = (term222 v).
Proof. exact (@lem1483440 term147 v). Qed.
Lemma lem1671921 (m : nat) : (term223 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1671922 : term224 = term35.
Proof. exact (@lem1671921 term120). Qed.
Lemma lem1671923 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1671924 : term225 = term61.
Proof. exact (MK_COMB (@lem1671923) (@lem1671922)). Qed.
Lemma lem1671925 (v : real) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem1671926 (v : real) : (term222 v) = (term41 v).
Proof. exact (MK_COMB (@lem1671924) (@lem1671925 v)). Qed.
Lemma lem1671927 (v : real) : (term253 v) = (term41 v).
Proof. exact (TRANS (@lem1671919 v) (@lem1671926 v)). Qed.
Lemma lem1671928 (v : real) : (term41 v) = term35.
Proof. exact (@lem1483446 v). Qed.
Lemma lem1671929 (v : real) : (term253 v) = term35.
Proof. exact (TRANS (@lem1671927 v) (@lem1671928 v)). Qed.
Lemma lem1671930 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1671931 (v : real) : (term384 v) = term47.
Proof. exact (MK_COMB (@lem1671930) (@lem1671929 v)). Qed.
Lemma lem1671933 (m : nat) : (term399 m) = term35.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1671934 : term400 = term35.
Proof. exact (@lem1671933 term120). Qed.
Lemma lem1671935 (v : real) : (term398 v) = term131.
Proof. exact (MK_COMB (@lem1671931 v) (@lem1671934)). Qed.
Lemma lem1671936 (v : real) : (term397 v) = term131.
Proof. exact (TRANS (@lem1671918 v) (@lem1671935 v)). Qed.
Lemma lem1671937 : term131 = term35.
Proof. exact (@lem1483448 term35). Qed.
Lemma lem1671938 (v : real) : (term397 v) = term35.
Proof. exact (TRANS (@lem1671936 v) (@lem1671937)). Qed.
Lemma lem1671939 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1671940 (v : real) : (term401 v) = term255.
Proof. exact (MK_COMB (@lem1671939) (@lem1671938 v)). Qed.
Lemma lem1671941 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671942 (v : real) : (term396 v) = term256.
Proof. exact (MK_COMB (@lem1671940 v) (@lem1671941)). Qed.
Lemma lem1671943 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : term256.
Proof. exact (EQ_MP (@lem1671942 v) (@lem1671917 a x b y v u h1)). Qed.
Lemma lem1671945 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1671946 : term256 = term257.
Proof. exact (@lem1671945 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1671947 : term257 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1671948 : term256 = False.
Proof. exact (TRANS (@lem1671946) (@lem1671947)). Qed.
Lemma lem1671949 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term342 a x b y v u) : False.
Proof. exact (EQ_MP (@lem1671948) (@lem1671943 a x b y v u h1)). Qed.
Lemma lem1671950 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term402 a x b y v u.
Proof. exact (h1). Qed.
Lemma lem1671951 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term333 a x b y v u.
Proof. exact (proj2 (@lem1671950 a x b y v u h1)). Qed.
Lemma lem1671952 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term292 u.
Proof. exact (proj1 (@lem1671950 a x b y v u h1)). Qed.
Lemma lem1671953 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term329 b y v u.
Proof. exact (proj2 (@lem1671951 a x b y v u h1)). Qed.
Lemma lem1671955 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term325 v u.
Proof. exact (proj2 (@lem1671953 a x b y v u h1)). Qed.
Lemma lem1671957 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term321 v u.
Proof. exact (proj2 (@lem1671955 a x b y v u h1)). Qed.
Lemma lem1671958 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term137 u.
Proof. exact (proj1 (@lem1671955 a x b y v u h1)). Qed.
Lemma lem1671959 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term317 v u.
Proof. exact (proj2 (@lem1671957 a x b y v u h1)). Qed.
Lemma lem1671962 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : (term303 u v) = term35.
Proof. exact (proj1 (@lem1671959 a x b y v u h1)). Qed.
Lemma lem1671964 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1671965 : term201 = term202.
Proof. exact (@lem1671964 (NUMERAL 0) term120). Qed.
Lemma lem1671966 : term203 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1671967 (h1 : term203 = (BIT1 0)) : term202 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1671968 : (term203 = (BIT1 0)) = (term202 = True).
Proof. exact (prop_ext (fun h1 : term203 = (BIT1 0) => @lem1671967 h1) (fun h1 : term202 = True => @lem1671966)). Qed.
Lemma lem1671969 : term202 = True.
Proof. exact (EQ_MP (@lem1671968) (@lem1671966)). Qed.
Lemma lem1671970 : term201 = True.
Proof. exact (TRANS (@lem1671965) (@lem1671969)). Qed.
Lemma lem1671971 : True = term201.
Proof. exact (SYM (@lem1671970)). Qed.
Lemma lem1671972 : term201.
Proof. exact (EQ_MP (@lem1671971) (@lem0)). Qed.
Lemma lem1671973 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term403 u.
Proof. exact (conj (@lem1671972) (@lem1671958 a x b y v u h1)). Qed.
Lemma lem1671975 (x : real) (y : real) : term205 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1671976 (u : real) : term404 u.
Proof. exact (@lem1671975 term49 u). Qed.
Lemma lem1671977 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term405 u.
Proof. exact (@lem1671976 u (@lem1671973 a x b y v u h1)). Qed.
Lemma lem1671978 (u : real) : (term363 u) = u.
Proof. exact (@lem1483460 u). Qed.
Lemma lem1671979 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1671980 (u : real) : (term406 u) = (real_ge u).
Proof. exact (MK_COMB (@lem1671979) (@lem1671978 u)). Qed.
Lemma lem1671981 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1671982 (u : real) : (term405 u) = (term137 u).
Proof. exact (MK_COMB (@lem1671980 u) (@lem1671981)). Qed.
Lemma lem1671983 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term137 u.
Proof. exact (EQ_MP (@lem1671982 u) (@lem1671977 a x b y v u h1)). Qed.
Lemma lem1671985 (y : real) : term210 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1671986 (u : real) (v : real) : term343 u v.
Proof. exact (@lem1671985 (term303 u v)). Qed.
Lemma lem1671987 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term344 u v.
Proof. exact (@lem1671986 u v (@lem1671962 a x b y v u h1)). Qed.
Lemma lem1671988 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term365 u v.
Proof. exact (@lem1671987 a x b y v u h1 term147). Qed.
Lemma lem1671989 (u : real) (v : real) : (term365 u v) = ((term366 u v) = term35).
Proof. exact (eq_refl (term365 u v)). Qed.
Lemma lem1671990 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : (term366 u v) = term35.
Proof. exact (EQ_MP (@lem1671989 u v) (@lem1671988 a x b y v u h1)). Qed.
Lemma lem1671991 (u : real) (v : real) : (term366 u v) = (term367 u v).
Proof. exact (@lem1483508 u term147 (term148 v)). Qed.
Lemma lem1671992 (v : real) : (term368 v) = (term369 v).
Proof. exact (@lem1483508 v term147 term147). Qed.
Lemma lem1671994 (m : nat) (n : nat) : (term370 m n) = (term371 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1671995 : term372 = term146.
Proof. exact (@lem1671994 term120 term120). Qed.
Lemma lem1671996 : (term144 = (BIT1 0)) = (term145 = term120).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1671997 : term145 = term120.
Proof. exact (EQ_MP (@lem1671996) (@lem940073)). Qed.
Lemma lem1671998 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1671999 : term146 = term49.
Proof. exact (MK_COMB (@lem1671998) (@lem1671997)). Qed.
Lemma lem1672000 : term372 = term49.
Proof. exact (TRANS (@lem1671995) (@lem1671999)). Qed.
Lemma lem1672003 (v : real) : (term373 v) = (term373 v).
Proof. exact (eq_refl (term373 v)). Qed.
Lemma lem1672004 (v : real) : (term369 v) = (term374 v).
Proof. exact (MK_COMB (@lem1672003 v) (@lem1672000)). Qed.
Lemma lem1672005 (v : real) : (term368 v) = (term374 v).
Proof. exact (TRANS (@lem1671992 v) (@lem1672004 v)). Qed.
Lemma lem1672008 (u : real) : (term373 u) = (term373 u).
Proof. exact (eq_refl (term373 u)). Qed.
Lemma lem1672009 (u : real) (v : real) : (term367 u v) = (term375 u v).
Proof. exact (MK_COMB (@lem1672008 u) (@lem1672005 v)). Qed.
Lemma lem1672010 (u : real) (v : real) : (term366 u v) = (term375 u v).
Proof. exact (TRANS (@lem1671991 u v) (@lem1672009 u v)). Qed.
Lemma lem1672011 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1672012 (u : real) (v : real) : (term376 u v) = (term377 u v).
Proof. exact (MK_COMB (@lem1672011) (@lem1672010 u v)). Qed.
Lemma lem1672013 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1672014 (u : real) (v : real) : ((term366 u v) = term35) = ((term375 u v) = term35).
Proof. exact (MK_COMB (@lem1672012 u v) (@lem1672013)). Qed.
Lemma lem1672015 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : (term375 u v) = term35.
Proof. exact (EQ_MP (@lem1672014 u v) (@lem1671990 a x b y v u h1)). Qed.
Lemma lem1672016 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term407 v u.
Proof. exact (conj (@lem1672015 a x b y v u h1) (@lem1671983 a x b y v u h1)). Qed.
Lemma lem1672018 (x : real) (y : real) : term216 x y.
Proof. exact (proj1 (@lem1483572 x y)). Qed.
Lemma lem1672019 (v : real) (u : real) : term408 v u.
Proof. exact (@lem1672018 (term375 u v) u). Qed.
Lemma lem1672020 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term409 v u.
Proof. exact (@lem1672019 v u (@lem1672016 a x b y v u h1)). Qed.
Lemma lem1672021 (u : real) (v : real) : (term382 v u) = (term383 u v).
Proof. exact (@lem1483486 (term155 u) u (term374 v)). Qed.
Lemma lem1672022 (u : real) : (term253 u) = (term222 u).
Proof. exact (@lem1483440 term147 u). Qed.
Lemma lem1672024 (m : nat) : (term223 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1672025 : term224 = term35.
Proof. exact (@lem1672024 term120). Qed.
Lemma lem1672026 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1672027 : term225 = term61.
Proof. exact (MK_COMB (@lem1672026) (@lem1672025)). Qed.
Lemma lem1672028 (u : real) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem1672029 (u : real) : (term222 u) = (term41 u).
Proof. exact (MK_COMB (@lem1672027) (@lem1672028 u)). Qed.
Lemma lem1672030 (u : real) : (term253 u) = (term41 u).
Proof. exact (TRANS (@lem1672022 u) (@lem1672029 u)). Qed.
Lemma lem1672031 (u : real) : (term41 u) = term35.
Proof. exact (@lem1483446 u). Qed.
Lemma lem1672032 (u : real) : (term253 u) = term35.
Proof. exact (TRANS (@lem1672030 u) (@lem1672031 u)). Qed.
Lemma lem1672033 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1672034 (u : real) : (term384 u) = term47.
Proof. exact (MK_COMB (@lem1672033) (@lem1672032 u)). Qed.
Lemma lem1672035 (v : real) : (term374 v) = (term374 v).
Proof. exact (eq_refl (term374 v)). Qed.
Lemma lem1672036 (u : real) (v : real) : (term383 u v) = (term385 v).
Proof. exact (MK_COMB (@lem1672034 u) (@lem1672035 v)). Qed.
Lemma lem1672037 (u : real) (v : real) : (term382 v u) = (term385 v).
Proof. exact (TRANS (@lem1672021 u v) (@lem1672036 u v)). Qed.
Lemma lem1672038 (v : real) : (term385 v) = (term374 v).
Proof. exact (@lem1483448 (term374 v)). Qed.
Lemma lem1672039 (u : real) (v : real) : (term382 v u) = (term374 v).
Proof. exact (TRANS (@lem1672037 u v) (@lem1672038 v)). Qed.
Lemma lem1672040 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1672041 (u : real) (v : real) : (term410 v u) = (term411 v).
Proof. exact (MK_COMB (@lem1672040) (@lem1672039 u v)). Qed.
Lemma lem1672042 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1672043 (u : real) (v : real) : (term409 v u) = (term412 v).
Proof. exact (MK_COMB (@lem1672041 u v) (@lem1672042)). Qed.
Lemma lem1672044 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term412 v.
Proof. exact (EQ_MP (@lem1672043 u v) (@lem1672020 a x b y v u h1)). Qed.
Lemma lem1672046 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1672047 : term201 = term202.
Proof. exact (@lem1672046 (NUMERAL 0) term120). Qed.
Lemma lem1672048 : term203 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1672049 (h1 : term203 = (BIT1 0)) : term202 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1672050 : (term203 = (BIT1 0)) = (term202 = True).
Proof. exact (prop_ext (fun h1 : term203 = (BIT1 0) => @lem1672049 h1) (fun h1 : term202 = True => @lem1672048)). Qed.
Lemma lem1672051 : term202 = True.
Proof. exact (EQ_MP (@lem1672050) (@lem1672048)). Qed.
Lemma lem1672052 : term201 = True.
Proof. exact (TRANS (@lem1672047) (@lem1672051)). Qed.
Lemma lem1672053 : True = term201.
Proof. exact (SYM (@lem1672052)). Qed.
Lemma lem1672054 : term201.
Proof. exact (EQ_MP (@lem1672053) (@lem0)). Qed.
Lemma lem1672055 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term413 v.
Proof. exact (conj (@lem1672054) (@lem1672044 a x b y v u h1)). Qed.
Lemma lem1672057 (x : real) (y : real) : term205 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1672058 (v : real) : term414 v.
Proof. exact (@lem1672057 term49 (term374 v)). Qed.
Lemma lem1672059 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term415 v.
Proof. exact (@lem1672058 v (@lem1672055 a x b y v u h1)). Qed.
Lemma lem1672060 (v : real) : (term392 v) = (term374 v).
Proof. exact (@lem1483460 (term374 v)). Qed.
Lemma lem1672061 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1672062 (v : real) : (term416 v) = (term411 v).
Proof. exact (MK_COMB (@lem1672061) (@lem1672060 v)). Qed.
Lemma lem1672063 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1672064 (v : real) : (term415 v) = (term412 v).
Proof. exact (MK_COMB (@lem1672062 v) (@lem1672063)). Qed.
Lemma lem1672065 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term412 v.
Proof. exact (EQ_MP (@lem1672064 v) (@lem1672059 a x b y v u h1)). Qed.
Lemma lem1672067 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1672068 : term201 = term202.
Proof. exact (@lem1672067 (NUMERAL 0) term120). Qed.
Lemma lem1672069 : term203 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1672070 (h1 : term203 = (BIT1 0)) : term202 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1672071 : (term203 = (BIT1 0)) = (term202 = True).
Proof. exact (prop_ext (fun h1 : term203 = (BIT1 0) => @lem1672070 h1) (fun h1 : term202 = True => @lem1672069)). Qed.
Lemma lem1672072 : term202 = True.
Proof. exact (EQ_MP (@lem1672071) (@lem1672069)). Qed.
Lemma lem1672073 : term201 = True.
Proof. exact (TRANS (@lem1672068) (@lem1672072)). Qed.
Lemma lem1672074 : True = term201.
Proof. exact (SYM (@lem1672073)). Qed.
Lemma lem1672075 : term201.
Proof. exact (EQ_MP (@lem1672074) (@lem0)). Qed.
Lemma lem1672076 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term417 u.
Proof. exact (conj (@lem1672075) (@lem1671952 a x b y v u h1)). Qed.
Lemma lem1672078 (x : real) (y : real) : term242 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1672079 (u : real) : term418 u.
Proof. exact (@lem1672078 term49 (term155 u)). Qed.
Lemma lem1672080 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term419 u.
Proof. exact (@lem1672079 u (@lem1672076 a x b y v u h1)). Qed.
Lemma lem1672081 (u : real) : (term208 u) = (term155 u).
Proof. exact (@lem1483460 (term155 u)). Qed.
Lemma lem1672082 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1672083 (u : real) : (term420 u) = (term290 u).
Proof. exact (MK_COMB (@lem1672082) (@lem1672081 u)). Qed.
Lemma lem1672084 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1672085 (u : real) : (term419 u) = (term292 u).
Proof. exact (MK_COMB (@lem1672083 u) (@lem1672084)). Qed.
Lemma lem1672086 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term292 u.
Proof. exact (EQ_MP (@lem1672085 u) (@lem1672080 a x b y v u h1)). Qed.
Lemma lem1672088 (y : real) : term210 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1672089 (u : real) (v : real) : term343 u v.
Proof. exact (@lem1672088 (term303 u v)). Qed.
Lemma lem1672090 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term344 u v.
Proof. exact (@lem1672089 u v (@lem1671962 a x b y v u h1)). Qed.
Lemma lem1672091 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term345 u v.
Proof. exact (@lem1672090 a x b y v u h1 term49). Qed.
Lemma lem1672092 (u : real) (v : real) : (term345 u v) = ((term346 u v) = term35).
Proof. exact (eq_refl (term345 u v)). Qed.
Lemma lem1672093 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : (term346 u v) = term35.
Proof. exact (EQ_MP (@lem1672092 u v) (@lem1672091 a x b y v u h1)). Qed.
Lemma lem1672094 (u : real) (v : real) : (term346 u v) = (term303 u v).
Proof. exact (@lem1483460 (term303 u v)). Qed.
Lemma lem1672095 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1672096 (u : real) (v : real) : (term347 u v) = (term305 u v).
Proof. exact (MK_COMB (@lem1672095) (@lem1672094 u v)). Qed.
Lemma lem1672097 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1672098 (u : real) (v : real) : ((term346 u v) = term35) = ((term303 u v) = term35).
Proof. exact (MK_COMB (@lem1672096 u v) (@lem1672097)). Qed.
Lemma lem1672099 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : (term303 u v) = term35.
Proof. exact (EQ_MP (@lem1672098 u v) (@lem1672093 a x b y v u h1)). Qed.
Lemma lem1672100 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term421 v u.
Proof. exact (conj (@lem1672099 a x b y v u h1) (@lem1672086 a x b y v u h1)). Qed.
Lemma lem1672102 (x : real) (y : real) : term379 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1672103 (v : real) (u : real) : term422 v u.
Proof. exact (@lem1672102 (term303 u v) (term155 u)). Qed.
Lemma lem1672104 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term423 v u.
Proof. exact (@lem1672103 v u (@lem1672100 a x b y v u h1)). Qed.
Lemma lem1672105 (u : real) (v : real) : (term350 v u) = (term351 u v).
Proof. exact (@lem1483486 u (term155 u) (term148 v)). Qed.
Lemma lem1672106 (u : real) : (term221 u) = (term222 u).
Proof. exact (@lem1483442 term147 u). Qed.
Lemma lem1672108 (m : nat) : (term223 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1672109 : term224 = term35.
Proof. exact (@lem1672108 term120). Qed.
Lemma lem1672110 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1672111 : term225 = term61.
Proof. exact (MK_COMB (@lem1672110) (@lem1672109)). Qed.
Lemma lem1672112 (u : real) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem1672113 (u : real) : (term222 u) = (term41 u).
Proof. exact (MK_COMB (@lem1672111) (@lem1672112 u)). Qed.
Lemma lem1672114 (u : real) : (term221 u) = (term41 u).
Proof. exact (TRANS (@lem1672106 u) (@lem1672113 u)). Qed.
Lemma lem1672115 (u : real) : (term41 u) = term35.
Proof. exact (@lem1483446 u). Qed.
Lemma lem1672116 (u : real) : (term221 u) = term35.
Proof. exact (TRANS (@lem1672114 u) (@lem1672115 u)). Qed.
Lemma lem1672117 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1672118 (u : real) : (term226 u) = term47.
Proof. exact (MK_COMB (@lem1672117) (@lem1672116 u)). Qed.
Lemma lem1672119 (v : real) : (term148 v) = (term148 v).
Proof. exact (eq_refl (term148 v)). Qed.
Lemma lem1672120 (u : real) (v : real) : (term351 u v) = (term352 v).
Proof. exact (MK_COMB (@lem1672118 u) (@lem1672119 v)). Qed.
Lemma lem1672121 (u : real) (v : real) : (term350 v u) = (term352 v).
Proof. exact (TRANS (@lem1672105 u v) (@lem1672120 u v)). Qed.
Lemma lem1672122 (v : real) : (term352 v) = (term148 v).
Proof. exact (@lem1483448 (term148 v)). Qed.
Lemma lem1672123 (u : real) (v : real) : (term350 v u) = (term148 v).
Proof. exact (TRANS (@lem1672121 u v) (@lem1672122 v)). Qed.
Lemma lem1672124 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1672125 (u : real) (v : real) : (term424 v u) = (term425 v).
Proof. exact (MK_COMB (@lem1672124) (@lem1672123 u v)). Qed.
Lemma lem1672126 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1672127 (u : real) (v : real) : (term423 v u) = (term426 v).
Proof. exact (MK_COMB (@lem1672125 u v) (@lem1672126)). Qed.
Lemma lem1672128 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term426 v.
Proof. exact (EQ_MP (@lem1672127 u v) (@lem1672104 a x b y v u h1)). Qed.
Lemma lem1672130 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1672131 : term201 = term202.
Proof. exact (@lem1672130 (NUMERAL 0) term120). Qed.
Lemma lem1672132 : term203 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1672133 (h1 : term203 = (BIT1 0)) : term202 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1672134 : (term203 = (BIT1 0)) = (term202 = True).
Proof. exact (prop_ext (fun h1 : term203 = (BIT1 0) => @lem1672133 h1) (fun h1 : term202 = True => @lem1672132)). Qed.
Lemma lem1672135 : term202 = True.
Proof. exact (EQ_MP (@lem1672134) (@lem1672132)). Qed.
Lemma lem1672136 : term201 = True.
Proof. exact (TRANS (@lem1672131) (@lem1672135)). Qed.
Lemma lem1672137 : True = term201.
Proof. exact (SYM (@lem1672136)). Qed.
Lemma lem1672138 : term201.
Proof. exact (EQ_MP (@lem1672137) (@lem0)). Qed.
Lemma lem1672139 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term427 v.
Proof. exact (conj (@lem1672138) (@lem1672128 a x b y v u h1)). Qed.
Lemma lem1672141 (x : real) (y : real) : term242 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1672142 (v : real) : term428 v.
Proof. exact (@lem1672141 term49 (term148 v)). Qed.
Lemma lem1672143 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term429 v.
Proof. exact (@lem1672142 v (@lem1672139 a x b y v u h1)). Qed.
Lemma lem1672144 (v : real) : (term214 v) = (term148 v).
Proof. exact (@lem1483460 (term148 v)). Qed.
Lemma lem1672145 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1672146 (v : real) : (term430 v) = (term425 v).
Proof. exact (MK_COMB (@lem1672145) (@lem1672144 v)). Qed.
Lemma lem1672147 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1672148 (v : real) : (term429 v) = (term426 v).
Proof. exact (MK_COMB (@lem1672146 v) (@lem1672147)). Qed.
Lemma lem1672149 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term426 v.
Proof. exact (EQ_MP (@lem1672148 v) (@lem1672143 a x b y v u h1)). Qed.
Lemma lem1672150 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term431 v.
Proof. exact (conj (@lem1672149 a x b y v u h1) (@lem1672065 a x b y v u h1)). Qed.
Lemma lem1672152 (x : real) (y : real) : term248 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1672153 (v : real) : term432 v.
Proof. exact (@lem1672152 (term148 v) (term374 v)). Qed.
Lemma lem1672154 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term433 v.
Proof. exact (@lem1672153 v (@lem1672150 a x b y v u h1)). Qed.
Lemma lem1672155 (v : real) : (term434 v) = (term435 v).
Proof. exact (@lem1483480 v (term155 v) term147 term49). Qed.
Lemma lem1672156 (v : real) : (term221 v) = (term222 v).
Proof. exact (@lem1483442 term147 v). Qed.
Lemma lem1672158 (m : nat) : (term223 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1672159 : term224 = term35.
Proof. exact (@lem1672158 term120). Qed.
Lemma lem1672160 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1672161 : term225 = term61.
Proof. exact (MK_COMB (@lem1672160) (@lem1672159)). Qed.
Lemma lem1672162 (v : real) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem1672163 (v : real) : (term222 v) = (term41 v).
Proof. exact (MK_COMB (@lem1672161) (@lem1672162 v)). Qed.
Lemma lem1672164 (v : real) : (term221 v) = (term41 v).
Proof. exact (TRANS (@lem1672156 v) (@lem1672163 v)). Qed.
Lemma lem1672165 (v : real) : (term41 v) = term35.
Proof. exact (@lem1483446 v). Qed.
Lemma lem1672166 (v : real) : (term221 v) = term35.
Proof. exact (TRANS (@lem1672164 v) (@lem1672165 v)). Qed.
Lemma lem1672167 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1672168 (v : real) : (term226 v) = term47.
Proof. exact (MK_COMB (@lem1672167) (@lem1672166 v)). Qed.
Lemma lem1672170 (m : nat) : (term223 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1672171 : term224 = term35.
Proof. exact (@lem1672170 term120). Qed.
Lemma lem1672172 (v : real) : (term435 v) = term131.
Proof. exact (MK_COMB (@lem1672168 v) (@lem1672171)). Qed.
Lemma lem1672173 (v : real) : (term434 v) = term131.
Proof. exact (TRANS (@lem1672155 v) (@lem1672172 v)). Qed.
Lemma lem1672174 : term131 = term35.
Proof. exact (@lem1483448 term35). Qed.
Lemma lem1672175 (v : real) : (term434 v) = term35.
Proof. exact (TRANS (@lem1672173 v) (@lem1672174)). Qed.
Lemma lem1672176 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1672177 (v : real) : (term436 v) = term255.
Proof. exact (MK_COMB (@lem1672176) (@lem1672175 v)). Qed.
Lemma lem1672178 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1672179 (v : real) : (term433 v) = term256.
Proof. exact (MK_COMB (@lem1672177 v) (@lem1672178)). Qed.
Lemma lem1672180 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : term256.
Proof. exact (EQ_MP (@lem1672179 v) (@lem1672154 a x b y v u h1)). Qed.
Lemma lem1672182 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1672183 : term256 = term257.
Proof. exact (@lem1672182 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1672184 : term257 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1672185 : term256 = False.
Proof. exact (TRANS (@lem1672183) (@lem1672184)). Qed.
Lemma lem1672186 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term402 a x b y v u) : False.
Proof. exact (EQ_MP (@lem1672185) (@lem1672180 a x b y v u h1)). Qed.
Lemma lem1672187 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term338 a x b y v u) : False.
Proof. exact (or_elim (@lem1671712 a x b y v u h1) (fun h0 : term342 a x b y v u => @lem1671949 a x b y v u h0) (fun h0 : term402 a x b y v u => @lem1672186 a x b y v u h0)). Qed.
Lemma lem1672188 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term336 b y u v a x) : term336 b y u v a x.
Proof. exact (h1). Qed.
Lemma lem1672189 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term437 b y u v a x.
Proof. exact (h1). Qed.
Lemma lem1672190 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term334 b y u v a x.
Proof. exact (proj2 (@lem1672189 b y u v a x h1)). Qed.
Lemma lem1672192 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term330 b y u v a x.
Proof. exact (proj2 (@lem1672190 b y u v a x h1)). Qed.
Lemma lem1672193 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term127 a x.
Proof. exact (proj1 (@lem1672190 b y u v a x h1)). Qed.
Lemma lem1672194 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term326 u v a x.
Proof. exact (proj2 (@lem1672192 b y u v a x h1)). Qed.
Lemma lem1672196 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term322 u v a x.
Proof. exact (proj2 (@lem1672194 b y u v a x h1)). Qed.
Lemma lem1672198 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term318 u v a x.
Proof. exact (proj2 (@lem1672196 b y u v a x h1)). Qed.
Lemma lem1672200 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term164 a x.
Proof. exact (proj2 (@lem1672198 b y u v a x h1)). Qed.
Lemma lem1672203 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1672204 : term201 = term202.
Proof. exact (@lem1672203 (NUMERAL 0) term120). Qed.
Lemma lem1672205 : term203 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1672206 (h1 : term203 = (BIT1 0)) : term202 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1672207 : (term203 = (BIT1 0)) = (term202 = True).
Proof. exact (prop_ext (fun h1 : term203 = (BIT1 0) => @lem1672206 h1) (fun h1 : term202 = True => @lem1672205)). Qed.
Lemma lem1672208 : term202 = True.
Proof. exact (EQ_MP (@lem1672207) (@lem1672205)). Qed.
Lemma lem1672209 : term201 = True.
Proof. exact (TRANS (@lem1672204) (@lem1672208)). Qed.
Lemma lem1672210 : True = term201.
Proof. exact (SYM (@lem1672209)). Qed.
Lemma lem1672211 : term201.
Proof. exact (EQ_MP (@lem1672210) (@lem0)). Qed.
Lemma lem1672212 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term236 a x.
Proof. exact (conj (@lem1672211) (@lem1672200 b y u v a x h1)). Qed.
Lemma lem1672214 (x : real) (y : real) : term205 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1672215 (a : real) (x : real) : term237 a x.
Proof. exact (@lem1672214 term49 (term161 a x)). Qed.
Lemma lem1672216 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term238 a x.
Proof. exact (@lem1672215 a x (@lem1672212 b y u v a x h1)). Qed.
Lemma lem1672217 (a : real) (x : real) : (term239 a x) = (term161 a x).
Proof. exact (@lem1483460 (term161 a x)). Qed.
Lemma lem1672218 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1672219 (a : real) (x : real) : (term240 a x) = (term163 a x).
Proof. exact (MK_COMB (@lem1672218) (@lem1672217 a x)). Qed.
Lemma lem1672220 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1672221 (a : real) (x : real) : (term238 a x) = (term164 a x).
Proof. exact (MK_COMB (@lem1672219 a x) (@lem1672220)). Qed.
Lemma lem1672222 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term164 a x.
Proof. exact (EQ_MP (@lem1672221 a x) (@lem1672216 b y u v a x h1)). Qed.
Lemma lem1672224 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1672225 : term201 = term202.
Proof. exact (@lem1672224 (NUMERAL 0) term120). Qed.
Lemma lem1672226 : term203 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1672227 (h1 : term203 = (BIT1 0)) : term202 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1672228 : (term203 = (BIT1 0)) = (term202 = True).
Proof. exact (prop_ext (fun h1 : term203 = (BIT1 0) => @lem1672227 h1) (fun h1 : term202 = True => @lem1672226)). Qed.
Lemma lem1672229 : term202 = True.
Proof. exact (EQ_MP (@lem1672228) (@lem1672226)). Qed.
Lemma lem1672230 : term201 = True.
Proof. exact (TRANS (@lem1672225) (@lem1672229)). Qed.
Lemma lem1672231 : True = term201.
Proof. exact (SYM (@lem1672230)). Qed.
Lemma lem1672232 : term201.
Proof. exact (EQ_MP (@lem1672231) (@lem0)). Qed.
Lemma lem1672233 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term241 a x.
Proof. exact (conj (@lem1672232) (@lem1672193 b y u v a x h1)). Qed.
Lemma lem1672235 (x : real) (y : real) : term242 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1672236 (a : real) (x : real) : term243 a x.
Proof. exact (@lem1672235 term49 (term124 a x)). Qed.
Lemma lem1672237 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term244 a x.
Proof. exact (@lem1672236 a x (@lem1672233 b y u v a x h1)). Qed.
Lemma lem1672238 (a : real) (x : real) : (term245 a x) = (term124 a x).
Proof. exact (@lem1483460 (term124 a x)). Qed.
Lemma lem1672239 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1672240 (a : real) (x : real) : (term246 a x) = (term126 a x).
Proof. exact (MK_COMB (@lem1672239) (@lem1672238 a x)). Qed.
Lemma lem1672241 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1672242 (a : real) (x : real) : (term244 a x) = (term127 a x).
Proof. exact (MK_COMB (@lem1672240 a x) (@lem1672241)). Qed.
Lemma lem1672243 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term127 a x.
Proof. exact (EQ_MP (@lem1672242 a x) (@lem1672237 b y u v a x h1)). Qed.
Lemma lem1672244 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term247 a x.
Proof. exact (conj (@lem1672243 b y u v a x h1) (@lem1672222 b y u v a x h1)). Qed.
Lemma lem1672246 (x : real) (y : real) : term248 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1672247 (a : real) (x : real) : term249 a x.
Proof. exact (@lem1672246 (term124 a x) (term161 a x)). Qed.
Lemma lem1672248 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term250 a x.
Proof. exact (@lem1672247 a x (@lem1672244 b y u v a x h1)). Qed.
Lemma lem1672249 (a : real) (x : real) : (term251 a x) = (term252 a x).
Proof. exact (@lem1483480 a (term155 a) (term155 x) x). Qed.
Lemma lem1672250 (a : real) : (term221 a) = (term222 a).
Proof. exact (@lem1483442 term147 a). Qed.
Lemma lem1672252 (m : nat) : (term223 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1672253 : term224 = term35.
Proof. exact (@lem1672252 term120). Qed.
Lemma lem1672254 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1672255 : term225 = term61.
Proof. exact (MK_COMB (@lem1672254) (@lem1672253)). Qed.
Lemma lem1672256 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1672257 (a : real) : (term222 a) = (term41 a).
Proof. exact (MK_COMB (@lem1672255) (@lem1672256 a)). Qed.
Lemma lem1672258 (a : real) : (term221 a) = (term41 a).
Proof. exact (TRANS (@lem1672250 a) (@lem1672257 a)). Qed.
Lemma lem1672259 (a : real) : (term41 a) = term35.
Proof. exact (@lem1483446 a). Qed.
Lemma lem1672260 (a : real) : (term221 a) = term35.
Proof. exact (TRANS (@lem1672258 a) (@lem1672259 a)). Qed.
Lemma lem1672261 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1672262 (a : real) : (term226 a) = term47.
Proof. exact (MK_COMB (@lem1672261) (@lem1672260 a)). Qed.
Lemma lem1672263 (x : real) : (term253 x) = (term222 x).
Proof. exact (@lem1483440 term147 x). Qed.
Lemma lem1672265 (m : nat) : (term223 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1672266 : term224 = term35.
Proof. exact (@lem1672265 term120). Qed.
Lemma lem1672267 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1672268 : term225 = term61.
Proof. exact (MK_COMB (@lem1672267) (@lem1672266)). Qed.
Lemma lem1672269 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1672270 (x : real) : (term222 x) = (term41 x).
Proof. exact (MK_COMB (@lem1672268) (@lem1672269 x)). Qed.
Lemma lem1672271 (x : real) : (term253 x) = (term41 x).
Proof. exact (TRANS (@lem1672263 x) (@lem1672270 x)). Qed.
Lemma lem1672272 (x : real) : (term41 x) = term35.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1672273 (x : real) : (term253 x) = term35.
Proof. exact (TRANS (@lem1672271 x) (@lem1672272 x)). Qed.
Lemma lem1672274 (a : real) (x : real) : (term252 a x) = term131.
Proof. exact (MK_COMB (@lem1672262 a) (@lem1672273 x)). Qed.
Lemma lem1672275 (a : real) (x : real) : (term251 a x) = term131.
Proof. exact (TRANS (@lem1672249 a x) (@lem1672274 a x)). Qed.
Lemma lem1672276 : term131 = term35.
Proof. exact (@lem1483448 term35). Qed.
Lemma lem1672277 (a : real) (x : real) : (term251 a x) = term35.
Proof. exact (TRANS (@lem1672275 a x) (@lem1672276)). Qed.
Lemma lem1672278 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1672279 (a : real) (x : real) : (term254 a x) = term255.
Proof. exact (MK_COMB (@lem1672278) (@lem1672277 a x)). Qed.
Lemma lem1672280 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1672281 (a : real) (x : real) : (term250 a x) = term256.
Proof. exact (MK_COMB (@lem1672279 a x) (@lem1672280)). Qed.
Lemma lem1672282 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : term256.
Proof. exact (EQ_MP (@lem1672281 a x) (@lem1672248 b y u v a x h1)). Qed.
Lemma lem1672284 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1672285 : term256 = term257.
Proof. exact (@lem1672284 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1672286 : term257 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1672287 : term256 = False.
Proof. exact (TRANS (@lem1672285) (@lem1672286)). Qed.
Lemma lem1672288 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term437 b y u v a x) : False.
Proof. exact (EQ_MP (@lem1672287) (@lem1672282 b y u v a x h1)). Qed.
Lemma lem1672289 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term438 b y u v a x.
Proof. exact (h1). Qed.
Lemma lem1672290 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term334 b y u v a x.
Proof. exact (proj2 (@lem1672289 b y u v a x h1)). Qed.
Lemma lem1672292 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term330 b y u v a x.
Proof. exact (proj2 (@lem1672290 b y u v a x h1)). Qed.
Lemma lem1672293 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term127 a x.
Proof. exact (proj1 (@lem1672290 b y u v a x h1)). Qed.
Lemma lem1672294 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term326 u v a x.
Proof. exact (proj2 (@lem1672292 b y u v a x h1)). Qed.
Lemma lem1672296 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term322 u v a x.
Proof. exact (proj2 (@lem1672294 b y u v a x h1)). Qed.
Lemma lem1672298 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term318 u v a x.
Proof. exact (proj2 (@lem1672296 b y u v a x h1)). Qed.
Lemma lem1672300 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term164 a x.
Proof. exact (proj2 (@lem1672298 b y u v a x h1)). Qed.
Lemma lem1672303 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1672304 : term201 = term202.
Proof. exact (@lem1672303 (NUMERAL 0) term120). Qed.
Lemma lem1672305 : term203 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1672306 (h1 : term203 = (BIT1 0)) : term202 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1672307 : (term203 = (BIT1 0)) = (term202 = True).
Proof. exact (prop_ext (fun h1 : term203 = (BIT1 0) => @lem1672306 h1) (fun h1 : term202 = True => @lem1672305)). Qed.
Lemma lem1672308 : term202 = True.
Proof. exact (EQ_MP (@lem1672307) (@lem1672305)). Qed.
Lemma lem1672309 : term201 = True.
Proof. exact (TRANS (@lem1672304) (@lem1672308)). Qed.
Lemma lem1672310 : True = term201.
Proof. exact (SYM (@lem1672309)). Qed.
Lemma lem1672311 : term201.
Proof. exact (EQ_MP (@lem1672310) (@lem0)). Qed.
Lemma lem1672312 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term236 a x.
Proof. exact (conj (@lem1672311) (@lem1672300 b y u v a x h1)). Qed.
Lemma lem1672314 (x : real) (y : real) : term205 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1672315 (a : real) (x : real) : term237 a x.
Proof. exact (@lem1672314 term49 (term161 a x)). Qed.
Lemma lem1672316 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term238 a x.
Proof. exact (@lem1672315 a x (@lem1672312 b y u v a x h1)). Qed.
Lemma lem1672317 (a : real) (x : real) : (term239 a x) = (term161 a x).
Proof. exact (@lem1483460 (term161 a x)). Qed.
Lemma lem1672318 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1672319 (a : real) (x : real) : (term240 a x) = (term163 a x).
Proof. exact (MK_COMB (@lem1672318) (@lem1672317 a x)). Qed.
Lemma lem1672320 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1672321 (a : real) (x : real) : (term238 a x) = (term164 a x).
Proof. exact (MK_COMB (@lem1672319 a x) (@lem1672320)). Qed.
Lemma lem1672322 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term164 a x.
Proof. exact (EQ_MP (@lem1672321 a x) (@lem1672316 b y u v a x h1)). Qed.
Lemma lem1672324 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1672325 : term201 = term202.
Proof. exact (@lem1672324 (NUMERAL 0) term120). Qed.
Lemma lem1672326 : term203 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1672327 (h1 : term203 = (BIT1 0)) : term202 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1672328 : (term203 = (BIT1 0)) = (term202 = True).
Proof. exact (prop_ext (fun h1 : term203 = (BIT1 0) => @lem1672327 h1) (fun h1 : term202 = True => @lem1672326)). Qed.
Lemma lem1672329 : term202 = True.
Proof. exact (EQ_MP (@lem1672328) (@lem1672326)). Qed.
Lemma lem1672330 : term201 = True.
Proof. exact (TRANS (@lem1672325) (@lem1672329)). Qed.
Lemma lem1672331 : True = term201.
Proof. exact (SYM (@lem1672330)). Qed.
Lemma lem1672332 : term201.
Proof. exact (EQ_MP (@lem1672331) (@lem0)). Qed.
Lemma lem1672333 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term241 a x.
Proof. exact (conj (@lem1672332) (@lem1672293 b y u v a x h1)). Qed.
Lemma lem1672335 (x : real) (y : real) : term242 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1672336 (a : real) (x : real) : term243 a x.
Proof. exact (@lem1672335 term49 (term124 a x)). Qed.
Lemma lem1672337 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term244 a x.
Proof. exact (@lem1672336 a x (@lem1672333 b y u v a x h1)). Qed.
Lemma lem1672338 (a : real) (x : real) : (term245 a x) = (term124 a x).
Proof. exact (@lem1483460 (term124 a x)). Qed.
Lemma lem1672339 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1672340 (a : real) (x : real) : (term246 a x) = (term126 a x).
Proof. exact (MK_COMB (@lem1672339) (@lem1672338 a x)). Qed.
Lemma lem1672341 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1672342 (a : real) (x : real) : (term244 a x) = (term127 a x).
Proof. exact (MK_COMB (@lem1672340 a x) (@lem1672341)). Qed.
Lemma lem1672343 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term127 a x.
Proof. exact (EQ_MP (@lem1672342 a x) (@lem1672337 b y u v a x h1)). Qed.
Lemma lem1672344 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term247 a x.
Proof. exact (conj (@lem1672343 b y u v a x h1) (@lem1672322 b y u v a x h1)). Qed.
Lemma lem1672346 (x : real) (y : real) : term248 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1672347 (a : real) (x : real) : term249 a x.
Proof. exact (@lem1672346 (term124 a x) (term161 a x)). Qed.
Lemma lem1672348 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term250 a x.
Proof. exact (@lem1672347 a x (@lem1672344 b y u v a x h1)). Qed.
Lemma lem1672349 (a : real) (x : real) : (term251 a x) = (term252 a x).
Proof. exact (@lem1483480 a (term155 a) (term155 x) x). Qed.
Lemma lem1672350 (a : real) : (term221 a) = (term222 a).
Proof. exact (@lem1483442 term147 a). Qed.
Lemma lem1672352 (m : nat) : (term223 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1672353 : term224 = term35.
Proof. exact (@lem1672352 term120). Qed.
Lemma lem1672354 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1672355 : term225 = term61.
Proof. exact (MK_COMB (@lem1672354) (@lem1672353)). Qed.
Lemma lem1672356 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1672357 (a : real) : (term222 a) = (term41 a).
Proof. exact (MK_COMB (@lem1672355) (@lem1672356 a)). Qed.
Lemma lem1672358 (a : real) : (term221 a) = (term41 a).
Proof. exact (TRANS (@lem1672350 a) (@lem1672357 a)). Qed.
Lemma lem1672359 (a : real) : (term41 a) = term35.
Proof. exact (@lem1483446 a). Qed.
Lemma lem1672360 (a : real) : (term221 a) = term35.
Proof. exact (TRANS (@lem1672358 a) (@lem1672359 a)). Qed.
Lemma lem1672361 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1672362 (a : real) : (term226 a) = term47.
Proof. exact (MK_COMB (@lem1672361) (@lem1672360 a)). Qed.
Lemma lem1672363 (x : real) : (term253 x) = (term222 x).
Proof. exact (@lem1483440 term147 x). Qed.
Lemma lem1672365 (m : nat) : (term223 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1672366 : term224 = term35.
Proof. exact (@lem1672365 term120). Qed.
Lemma lem1672367 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1672368 : term225 = term61.
Proof. exact (MK_COMB (@lem1672367) (@lem1672366)). Qed.
Lemma lem1672369 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1672370 (x : real) : (term222 x) = (term41 x).
Proof. exact (MK_COMB (@lem1672368) (@lem1672369 x)). Qed.
Lemma lem1672371 (x : real) : (term253 x) = (term41 x).
Proof. exact (TRANS (@lem1672363 x) (@lem1672370 x)). Qed.
Lemma lem1672372 (x : real) : (term41 x) = term35.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1672373 (x : real) : (term253 x) = term35.
Proof. exact (TRANS (@lem1672371 x) (@lem1672372 x)). Qed.
Lemma lem1672374 (a : real) (x : real) : (term252 a x) = term131.
Proof. exact (MK_COMB (@lem1672362 a) (@lem1672373 x)). Qed.
Lemma lem1672375 (a : real) (x : real) : (term251 a x) = term131.
Proof. exact (TRANS (@lem1672349 a x) (@lem1672374 a x)). Qed.
Lemma lem1672376 : term131 = term35.
Proof. exact (@lem1483448 term35). Qed.
Lemma lem1672377 (a : real) (x : real) : (term251 a x) = term35.
Proof. exact (TRANS (@lem1672375 a x) (@lem1672376)). Qed.
Lemma lem1672378 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1672379 (a : real) (x : real) : (term254 a x) = term255.
Proof. exact (MK_COMB (@lem1672378) (@lem1672377 a x)). Qed.
Lemma lem1672380 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1672381 (a : real) (x : real) : (term250 a x) = term256.
Proof. exact (MK_COMB (@lem1672379 a x) (@lem1672380)). Qed.
Lemma lem1672382 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : term256.
Proof. exact (EQ_MP (@lem1672381 a x) (@lem1672348 b y u v a x h1)). Qed.
Lemma lem1672384 (n : nat) (m : nat) : (term200 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1672385 : term256 = term257.
Proof. exact (@lem1672384 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1672386 : term257 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1672387 : term256 = False.
Proof. exact (TRANS (@lem1672385) (@lem1672386)). Qed.
Lemma lem1672388 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term438 b y u v a x) : False.
Proof. exact (EQ_MP (@lem1672387) (@lem1672382 b y u v a x h1)). Qed.
Lemma lem1672389 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term336 b y u v a x) : False.
Proof. exact (or_elim (@lem1672188 b y u v a x h1) (fun h0 : term437 b y u v a x => @lem1672288 b y u v a x h0) (fun h0 : term438 b y u v a x => @lem1672388 b y u v a x h0)). Qed.
Lemma lem1672390 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term341 b y u v a x) : False.
Proof. exact (or_elim (@lem1671711 b y u v a x h1) (fun h0 : term338 a x b y v u => @lem1672187 a x b y v u h0) (fun h0 : term336 b y u v a x => @lem1672389 b y u v a x h0)). Qed.
Lemma lem1672392 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term341 b y u v a x) : term341 b y u v a x.
Proof. exact (h1). Qed.
Lemma lem1672393 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term341 b y u v a x) : (term341 b y u v a x) = False.
Proof. exact (prop_ext (fun h2 : term341 b y u v a x => @lem1672390 b y u v a x h1) (fun h2 : False => @lem1672392 b y u v a x h1)). Qed.
Lemma lem1672394 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term341 b y u v a x) : False.
Proof. exact (EQ_MP (@lem1672393 b y u v a x h1) (@lem1672392 b y u v a x h1)). Qed.
Lemma lem1672395 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) (h1 : term284 y b v u x a) : term284 y b v u x a.
Proof. exact (h1). Qed.
Lemma lem1672396 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) (h1 : term284 y b v u x a) : term341 b y u v a x.
Proof. exact (EQ_MP (@lem1671689 b y u v a x) (@lem1672395 y b v u x a h1)). Qed.
Lemma lem1672397 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) (h1 : term284 y b v u x a) : (term341 b y u v a x) = False.
Proof. exact (prop_ext (fun h2 : term341 b y u v a x => @lem1672394 b y u v a x h2) (fun h2 : False => @lem1672396 y b v u x a h1)). Qed.
Lemma lem1672398 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) (h1 : term284 y b v u x a) : False.
Proof. exact (EQ_MP (@lem1672397 y b v u x a h1) (@lem1672396 y b v u x a h1)). Qed.
Lemma lem1672399 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : term439 y b v u x a.
Proof. exact (fun h0 : term284 y b v u x a => @lem1672398 y b v u x a h0). Qed.
Lemma lem1672400 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : term440 y b v u x a.
Proof. exact (@lem1386578 (term441 y b v u x a)). Qed.
Lemma lem1672401 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : term441 y b v u x a.
Proof. exact (@lem1672400 y b v u x a (@lem1672399 y b v u x a)). Qed.
Lemma lem1672402 (y : real) (b : real) (v : real) (x : real) (a : real) (u : real) (h1 : term37 u) : term285 y b v u x a.
Proof. exact (@lem1672401 y b v u x a (@lem1670482 u h1)). Qed.
Lemma lem1672403 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) (h1 : term37 u) (h2 : real_lt x a) : term280 y b v u x a.
Proof. exact (@lem1672402 y b v x a u h1 (@lem1670593 x a h2)). Qed.
Lemma lem1672404 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : real_lt x a) (h3 : real_lt y b) : term276 v u x a.
Proof. exact (@lem1672403 y b v u x a h1 h2 (@lem1670595 y b h3)). Qed.
Lemma lem1672405 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : term43 u) (h3 : real_lt x a) (h4 : real_lt y b) : term272 v u x a.
Proof. exact (@lem1672404 v u x a y b h1 h3 h4 (@lem1670597 u h2)). Qed.
Lemma lem1672406 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : term43 u) (h3 : term43 v) (h4 : real_lt x a) (h5 : real_lt y b) : term268 v u x a.
Proof. exact (@lem1672405 v u x a y b h1 h2 h4 h5 (@lem1670599 v h3)). Qed.
Lemma lem1672407 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : (real_add u v) = term49) (h3 : term43 u) (h4 : term43 v) (h5 : real_lt x a) (h6 : real_lt y b) : term7 u x a.
Proof. exact (@lem1672406 u v x a y b h1 h3 h4 h5 h6 (@lem1670598 u v h2)). Qed.
Lemma lem1672408 (x : real) (a : real) (v : real) (y : real) (b : real) (u : real) (h1 : u = term35) : term115 x a v y b.
Proof. exact (@lem1671278 u x a v y b (@lem1670481 u h1)). Qed.
Lemma lem1672409 (v : real) (y : real) (b : real) (u : real) (x : real) (a : real) (h1 : u = term35) (h2 : real_lt x a) : term110 v y b.
Proof. exact (@lem1672408 x a v y b u h1 (@lem1670584 x a h2)). Qed.
Lemma lem1672410 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : u = term35) (h2 : real_lt x a) (h3 : real_lt y b) : term106 v y b.
Proof. exact (@lem1672409 v y b u x a h1 h2 (@lem1670586 y b h3)). Qed.
Lemma lem1672411 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : u = term35) (h2 : term44) (h3 : real_lt x a) (h4 : real_lt y b) : term102 v y b.
Proof. exact (@lem1672410 v u x a y b h1 h3 h4 (@lem1670588 h2)). Qed.
Lemma lem1672412 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : u = term35) (h2 : term43 v) (h3 : term44) (h4 : real_lt x a) (h5 : real_lt y b) : term98 v y b.
Proof. exact (@lem1672411 v u x a y b h1 h3 h4 h5 (@lem1670590 v h2)). Qed.
Lemma lem1672413 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : u = term35) (h2 : v = term49) (h3 : term43 v) (h4 : term44) (h5 : real_lt x a) (h6 : real_lt y b) : term7 v y b.
Proof. exact (@lem1672412 u v x a y b h1 h3 h4 h5 h6 (@lem1670589 v h2)). Qed.
Lemma lem1672414 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : (real_add u v) = term49) (h3 : term43 u) (h4 : term43 v) (h5 : real_lt x a) (h6 : real_lt y b) : term8 x u a.
Proof. exact (@lem1670696 x u a (@lem1672407 u v x a y b h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1672415 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : u = term35) (h2 : v = term49) (h3 : term43 v) (h4 : term44) (h5 : real_lt x a) (h6 : real_lt y b) : term8 y v b.
Proof. exact (@lem1670693 y v b (@lem1672413 u v x a y b h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1672416 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : (real_add u v) = term49) (h3 : term43 u) (h4 : term43 v) (h5 : real_lt x a) (h6 : real_lt y b) : term86 x u a y v b.
Proof. exact (EQ_MP (@lem1670690 x u a v y b h4 h6) (@lem1672414 u v x a y b h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1672417 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : (real_add u v) = term49) (h3 : term43 u) (h4 : term43 v) (h5 : real_lt x a) (h6 : real_lt y b) : term67 x y u a v b.
Proof. exact (@lem1670602 x y u a v b (@lem1672416 u v x a y b h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1672418 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : term57 x a y b u v) : term55 y b u v.
Proof. exact (proj2 (@lem1670591 x a y b u v h1)). Qed.
Lemma lem1672419 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : term57 x a y b u v) : real_lt x a.
Proof. exact (proj1 (@lem1670591 x a y b u v h1)). Qed.
Lemma lem1672420 (y : real) (b : real) (u : real) (v : real) (h1 : term55 y b u v) : term52 u v.
Proof. exact (proj2 (@lem1670592 y b u v h1)). Qed.
Lemma lem1672421 (y : real) (b : real) (u : real) (v : real) (h1 : term55 y b u v) : real_lt y b.
Proof. exact (proj1 (@lem1670592 y b u v h1)). Qed.
Lemma lem1672422 (u : real) (v : real) (h1 : term52 u v) : term50 u v.
Proof. exact (proj2 (@lem1670594 u v h1)). Qed.
Lemma lem1672423 (u : real) (v : real) (h1 : term52 u v) : term43 u.
Proof. exact (proj1 (@lem1670594 u v h1)). Qed.
Lemma lem1672424 (u : real) (v : real) (h1 : term50 u v) : (real_add u v) = term49.
Proof. exact (proj2 (@lem1670596 u v h1)). Qed.
Lemma lem1672425 (u : real) (v : real) (h1 : term50 u v) : term43 v.
Proof. exact (proj1 (@lem1670596 u v h1)). Qed.
Lemma lem1672426 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : (real_add u v) = term49) (h3 : term43 u) (h4 : term43 v) (h5 : real_lt x a) (h6 : real_lt y b) : ((real_add u v) = term49) = (term67 x y u a v b).
Proof. exact (prop_ext (fun h7 : (real_add u v) = term49 => @lem1672417 u v x a y b h1 h2 h3 h4 h5 h6) (fun h7 : term67 x y u a v b => @lem1670598 u v h2)). Qed.
Lemma lem1672427 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : (real_add u v) = term49) (h3 : term43 u) (h4 : term43 v) (h5 : real_lt x a) (h6 : real_lt y b) : term67 x y u a v b.
Proof. exact (EQ_MP (@lem1672426 u v x a y b h1 h2 h3 h4 h5 h6) (@lem1670598 u v h2)). Qed.
Lemma lem1672428 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : (real_add u v) = term49) (h3 : term43 u) (h4 : term43 v) (h5 : real_lt x a) (h6 : real_lt y b) : (term43 v) = (term67 x y u a v b).
Proof. exact (prop_ext (fun h7 : term43 v => @lem1672427 u v x a y b h1 h2 h3 h4 h5 h6) (fun h7 : term67 x y u a v b => @lem1670599 v h4)). Qed.
Lemma lem1672429 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : (real_add u v) = term49) (h3 : term43 u) (h4 : term43 v) (h5 : real_lt x a) (h6 : real_lt y b) : term67 x y u a v b.
Proof. exact (EQ_MP (@lem1672428 u v x a y b h1 h2 h3 h4 h5 h6) (@lem1670599 v h4)). Qed.
Lemma lem1672430 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : term50 u v) (h3 : term43 u) (h4 : term43 v) (h5 : real_lt x a) (h6 : real_lt y b) : ((real_add u v) = term49) = (term67 x y u a v b).
Proof. exact (prop_ext (fun h7 : (real_add u v) = term49 => @lem1672429 u v x a y b h1 h7 h3 h4 h5 h6) (fun h7 : term67 x y u a v b => @lem1672424 u v h2)). Qed.
Lemma lem1672431 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : term50 u v) (h3 : term43 u) (h4 : term43 v) (h5 : real_lt x a) (h6 : real_lt y b) : term67 x y u a v b.
Proof. exact (EQ_MP (@lem1672430 u v x a y b h1 h2 h3 h4 h5 h6) (@lem1672424 u v h2)). Qed.
Lemma lem1672432 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : term50 u v) (h3 : term43 u) (h4 : real_lt x a) (h5 : real_lt y b) : (term43 v) = (term67 x y u a v b).
Proof. exact (prop_ext (fun h6 : term43 v => @lem1672431 u v x a y b h1 h2 h3 h6 h4 h5) (fun h6 : term67 x y u a v b => @lem1672425 u v h2)). Qed.
Lemma lem1672433 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : term50 u v) (h3 : term43 u) (h4 : real_lt x a) (h5 : real_lt y b) : term67 x y u a v b.
Proof. exact (EQ_MP (@lem1672432 v u x a y b h1 h2 h3 h4 h5) (@lem1672425 u v h2)). Qed.
Lemma lem1672434 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : term50 u v) (h3 : term43 u) (h4 : real_lt x a) (h5 : real_lt y b) : (term43 u) = (term67 x y u a v b).
Proof. exact (prop_ext (fun h6 : term43 u => @lem1672433 v u x a y b h1 h2 h3 h4 h5) (fun h6 : term67 x y u a v b => @lem1670597 u h3)). Qed.
Lemma lem1672435 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : term50 u v) (h3 : term43 u) (h4 : real_lt x a) (h5 : real_lt y b) : term67 x y u a v b.
Proof. exact (EQ_MP (@lem1672434 v u x a y b h1 h2 h3 h4 h5) (@lem1670597 u h3)). Qed.
Lemma lem1672436 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : term52 u v) (h3 : term43 u) (h4 : real_lt x a) (h5 : real_lt y b) : (term50 u v) = (term67 x y u a v b).
Proof. exact (prop_ext (fun h6 : term50 u v => @lem1672435 v u x a y b h1 h6 h3 h4 h5) (fun h6 : term67 x y u a v b => @lem1672422 u v h2)). Qed.
Lemma lem1672437 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : term52 u v) (h3 : term43 u) (h4 : real_lt x a) (h5 : real_lt y b) : term67 x y u a v b.
Proof. exact (EQ_MP (@lem1672436 v u x a y b h1 h2 h3 h4 h5) (@lem1672422 u v h2)). Qed.
Lemma lem1672438 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : term52 u v) (h3 : real_lt x a) (h4 : real_lt y b) : (term43 u) = (term67 x y u a v b).
Proof. exact (prop_ext (fun h5 : term43 u => @lem1672437 v u x a y b h1 h2 h5 h3 h4) (fun h5 : term67 x y u a v b => @lem1672423 u v h2)). Qed.
Lemma lem1672439 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : term52 u v) (h3 : real_lt x a) (h4 : real_lt y b) : term67 x y u a v b.
Proof. exact (EQ_MP (@lem1672438 u v x a y b h1 h2 h3 h4) (@lem1672423 u v h2)). Qed.
Lemma lem1672440 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : term52 u v) (h3 : real_lt x a) (h4 : real_lt y b) : (real_lt y b) = (term67 x y u a v b).
Proof. exact (prop_ext (fun h5 : real_lt y b => @lem1672439 u v x a y b h1 h2 h3 h4) (fun h5 : term67 x y u a v b => @lem1670595 y b h4)). Qed.
Lemma lem1672441 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : term52 u v) (h3 : real_lt x a) (h4 : real_lt y b) : term67 x y u a v b.
Proof. exact (EQ_MP (@lem1672440 u v x a y b h1 h2 h3 h4) (@lem1670595 y b h4)). Qed.
Lemma lem1672442 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : term55 y b u v) (h3 : real_lt x a) (h4 : real_lt y b) : (term52 u v) = (term67 x y u a v b).
Proof. exact (prop_ext (fun h5 : term52 u v => @lem1672441 u v x a y b h1 h5 h3 h4) (fun h5 : term67 x y u a v b => @lem1672420 y b u v h2)). Qed.
Lemma lem1672443 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term37 u) (h2 : term55 y b u v) (h3 : real_lt x a) (h4 : real_lt y b) : term67 x y u a v b.
Proof. exact (EQ_MP (@lem1672442 u v x a y b h1 h2 h3 h4) (@lem1672420 y b u v h2)). Qed.
Lemma lem1672444 (y : real) (b : real) (u : real) (v : real) (x : real) (a : real) (h1 : term37 u) (h2 : term55 y b u v) (h3 : real_lt x a) : (real_lt y b) = (term67 x y u a v b).
Proof. exact (prop_ext (fun h4 : real_lt y b => @lem1672443 u v x a y b h1 h2 h3 h4) (fun h4 : term67 x y u a v b => @lem1672421 y b u v h2)). Qed.
Lemma lem1672445 (y : real) (b : real) (u : real) (v : real) (x : real) (a : real) (h1 : term37 u) (h2 : term55 y b u v) (h3 : real_lt x a) : term67 x y u a v b.
Proof. exact (EQ_MP (@lem1672444 y b u v x a h1 h2 h3) (@lem1672421 y b u v h2)). Qed.
Lemma lem1672446 (y : real) (b : real) (u : real) (v : real) (x : real) (a : real) (h1 : term37 u) (h2 : term55 y b u v) (h3 : real_lt x a) : (real_lt x a) = (term67 x y u a v b).
Proof. exact (prop_ext (fun h4 : real_lt x a => @lem1672445 y b u v x a h1 h2 h3) (fun h4 : term67 x y u a v b => @lem1670593 x a h3)). Qed.
Lemma lem1672447 (y : real) (b : real) (u : real) (v : real) (x : real) (a : real) (h1 : term37 u) (h2 : term55 y b u v) (h3 : real_lt x a) : term67 x y u a v b.
Proof. exact (EQ_MP (@lem1672446 y b u v x a h1 h2 h3) (@lem1670593 x a h3)). Qed.
Lemma lem1672448 (y : real) (b : real) (u : real) (v : real) (x : real) (a : real) (h1 : term37 u) (h2 : term57 x a y b u v) (h3 : real_lt x a) : (term55 y b u v) = (term67 x y u a v b).
Proof. exact (prop_ext (fun h4 : term55 y b u v => @lem1672447 y b u v x a h1 h4 h3) (fun h4 : term67 x y u a v b => @lem1672418 x a y b u v h2)). Qed.
Lemma lem1672449 (y : real) (b : real) (u : real) (v : real) (x : real) (a : real) (h1 : term37 u) (h2 : term57 x a y b u v) (h3 : real_lt x a) : term67 x y u a v b.
Proof. exact (EQ_MP (@lem1672448 y b u v x a h1 h2 h3) (@lem1672418 x a y b u v h2)). Qed.
Lemma lem1672450 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : term37 u) (h2 : term57 x a y b u v) : (real_lt x a) = (term67 x y u a v b).
Proof. exact (prop_ext (fun h3 : real_lt x a => @lem1672449 y b u v x a h1 h2 h3) (fun h3 : term67 x y u a v b => @lem1672419 x a y b u v h2)). Qed.
Lemma lem1672451 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : term37 u) (h2 : term57 x a y b u v) : term67 x y u a v b.
Proof. exact (EQ_MP (@lem1672450 x a y b u v h1 h2) (@lem1672419 x a y b u v h2)). Qed.
Lemma lem1672452 (x : real) (y : real) (a : real) (v : real) (b : real) (u : real) (h1 : term37 u) : term68 x y u a v b.
Proof. exact (fun h0 : term57 x a y b u v => @lem1672451 x a y b u v h1 h0). Qed.
Lemma lem1672453 (x : real) (a : real) (y : real) (b : real) (v : real) (h1 : term58 x a y b v) : term56 y b v.
Proof. exact (proj2 (@lem1670582 x a y b v h1)). Qed.
Lemma lem1672454 (x : real) (a : real) (y : real) (b : real) (v : real) (h1 : term58 x a y b v) : real_lt x a.
Proof. exact (proj1 (@lem1670582 x a y b v h1)). Qed.
Lemma lem1672455 (y : real) (b : real) (v : real) (h1 : term56 y b v) : term53 v.
Proof. exact (proj2 (@lem1670583 y b v h1)). Qed.
Lemma lem1672456 (y : real) (b : real) (v : real) (h1 : term56 y b v) : real_lt y b.
Proof. exact (proj1 (@lem1670583 y b v h1)). Qed.
Lemma lem1672457 (v : real) (h1 : term53 v) : term51 v.
Proof. exact (proj2 (@lem1670585 v h1)). Qed.
Lemma lem1672458 (v : real) (h1 : term53 v) : term44.
Proof. exact (proj1 (@lem1670585 v h1)). Qed.
Lemma lem1672459 (v : real) (h1 : term51 v) : v = term49.
Proof. exact (proj2 (@lem1670587 v h1)). Qed.
Lemma lem1672460 (v : real) (h1 : term51 v) : term43 v.
Proof. exact (proj1 (@lem1670587 v h1)). Qed.
Lemma lem1672461 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : u = term35) (h2 : v = term49) (h3 : term43 v) (h4 : term44) (h5 : real_lt x a) (h6 : real_lt y b) : (v = term49) = (term8 y v b).
Proof. exact (prop_ext (fun h7 : v = term49 => @lem1672415 u v x a y b h1 h2 h3 h4 h5 h6) (fun h7 : term8 y v b => @lem1670589 v h2)). Qed.
Lemma lem1672462 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : u = term35) (h2 : v = term49) (h3 : term43 v) (h4 : term44) (h5 : real_lt x a) (h6 : real_lt y b) : term8 y v b.
Proof. exact (EQ_MP (@lem1672461 u v x a y b h1 h2 h3 h4 h5 h6) (@lem1670589 v h2)). Qed.
Lemma lem1672463 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : u = term35) (h2 : v = term49) (h3 : term43 v) (h4 : term44) (h5 : real_lt x a) (h6 : real_lt y b) : (term43 v) = (term8 y v b).
Proof. exact (prop_ext (fun h7 : term43 v => @lem1672462 u v x a y b h1 h2 h3 h4 h5 h6) (fun h7 : term8 y v b => @lem1670590 v h3)). Qed.
Lemma lem1672464 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : u = term35) (h2 : v = term49) (h3 : term43 v) (h4 : term44) (h5 : real_lt x a) (h6 : real_lt y b) : term8 y v b.
Proof. exact (EQ_MP (@lem1672463 u v x a y b h1 h2 h3 h4 h5 h6) (@lem1670590 v h3)). Qed.
Lemma lem1672465 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term51 v) (h2 : u = term35) (h3 : term43 v) (h4 : term44) (h5 : real_lt x a) (h6 : real_lt y b) : (v = term49) = (term8 y v b).
Proof. exact (prop_ext (fun h7 : v = term49 => @lem1672464 u v x a y b h2 h7 h3 h4 h5 h6) (fun h7 : term8 y v b => @lem1672459 v h1)). Qed.
Lemma lem1672466 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term51 v) (h2 : u = term35) (h3 : term43 v) (h4 : term44) (h5 : real_lt x a) (h6 : real_lt y b) : term8 y v b.
Proof. exact (EQ_MP (@lem1672465 u v x a y b h1 h2 h3 h4 h5 h6) (@lem1672459 v h1)). Qed.
Lemma lem1672467 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term51 v) (h2 : u = term35) (h3 : term44) (h4 : real_lt x a) (h5 : real_lt y b) : (term43 v) = (term8 y v b).
Proof. exact (prop_ext (fun h6 : term43 v => @lem1672466 u v x a y b h1 h2 h6 h3 h4 h5) (fun h6 : term8 y v b => @lem1672460 v h1)). Qed.
Lemma lem1672468 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term51 v) (h2 : u = term35) (h3 : term44) (h4 : real_lt x a) (h5 : real_lt y b) : term8 y v b.
Proof. exact (EQ_MP (@lem1672467 v u x a y b h1 h2 h3 h4 h5) (@lem1672460 v h1)). Qed.
Lemma lem1672469 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term51 v) (h2 : u = term35) (h3 : term44) (h4 : real_lt x a) (h5 : real_lt y b) : term44 = (term8 y v b).
Proof. exact (prop_ext (fun h6 : term44 => @lem1672468 v u x a y b h1 h2 h3 h4 h5) (fun h6 : term8 y v b => @lem1670588 h3)). Qed.
Lemma lem1672470 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term51 v) (h2 : u = term35) (h3 : term44) (h4 : real_lt x a) (h5 : real_lt y b) : term8 y v b.
Proof. exact (EQ_MP (@lem1672469 v u x a y b h1 h2 h3 h4 h5) (@lem1670588 h3)). Qed.
Lemma lem1672471 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term53 v) (h2 : u = term35) (h3 : term44) (h4 : real_lt x a) (h5 : real_lt y b) : (term51 v) = (term8 y v b).
Proof. exact (prop_ext (fun h6 : term51 v => @lem1672470 v u x a y b h6 h2 h3 h4 h5) (fun h6 : term8 y v b => @lem1672457 v h1)). Qed.
Lemma lem1672472 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term53 v) (h2 : u = term35) (h3 : term44) (h4 : real_lt x a) (h5 : real_lt y b) : term8 y v b.
Proof. exact (EQ_MP (@lem1672471 v u x a y b h1 h2 h3 h4 h5) (@lem1672457 v h1)). Qed.
Lemma lem1672473 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term53 v) (h2 : u = term35) (h3 : real_lt x a) (h4 : real_lt y b) : term44 = (term8 y v b).
Proof. exact (prop_ext (fun h5 : term44 => @lem1672472 v u x a y b h1 h2 h5 h3 h4) (fun h5 : term8 y v b => @lem1672458 v h1)). Qed.
Lemma lem1672474 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term53 v) (h2 : u = term35) (h3 : real_lt x a) (h4 : real_lt y b) : term8 y v b.
Proof. exact (EQ_MP (@lem1672473 v u x a y b h1 h2 h3 h4) (@lem1672458 v h1)). Qed.
Lemma lem1672475 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term53 v) (h2 : u = term35) (h3 : real_lt x a) (h4 : real_lt y b) : (real_lt y b) = (term8 y v b).
Proof. exact (prop_ext (fun h5 : real_lt y b => @lem1672474 v u x a y b h1 h2 h3 h4) (fun h5 : term8 y v b => @lem1670586 y b h4)). Qed.
Lemma lem1672476 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term53 v) (h2 : u = term35) (h3 : real_lt x a) (h4 : real_lt y b) : term8 y v b.
Proof. exact (EQ_MP (@lem1672475 v u x a y b h1 h2 h3 h4) (@lem1670586 y b h4)). Qed.
Lemma lem1672477 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term56 y b v) (h2 : u = term35) (h3 : real_lt x a) (h4 : real_lt y b) : (term53 v) = (term8 y v b).
Proof. exact (prop_ext (fun h5 : term53 v => @lem1672476 v u x a y b h5 h2 h3 h4) (fun h5 : term8 y v b => @lem1672455 y b v h1)). Qed.
Lemma lem1672478 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : term56 y b v) (h2 : u = term35) (h3 : real_lt x a) (h4 : real_lt y b) : term8 y v b.
Proof. exact (EQ_MP (@lem1672477 v u x a y b h1 h2 h3 h4) (@lem1672455 y b v h1)). Qed.
Lemma lem1672479 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) (h1 : term56 y b v) (h2 : u = term35) (h3 : real_lt x a) : (real_lt y b) = (term8 y v b).
Proof. exact (prop_ext (fun h4 : real_lt y b => @lem1672478 v u x a y b h1 h2 h3 h4) (fun h4 : term8 y v b => @lem1672456 y b v h1)). Qed.
Lemma lem1672480 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) (h1 : term56 y b v) (h2 : u = term35) (h3 : real_lt x a) : term8 y v b.
Proof. exact (EQ_MP (@lem1672479 y b v u x a h1 h2 h3) (@lem1672456 y b v h1)). Qed.
Lemma lem1672481 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) (h1 : term56 y b v) (h2 : u = term35) (h3 : real_lt x a) : (real_lt x a) = (term8 y v b).
Proof. exact (prop_ext (fun h4 : real_lt x a => @lem1672480 y b v u x a h1 h2 h3) (fun h4 : term8 y v b => @lem1670584 x a h3)). Qed.
Lemma lem1672482 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) (h1 : term56 y b v) (h2 : u = term35) (h3 : real_lt x a) : term8 y v b.
Proof. exact (EQ_MP (@lem1672481 y b v u x a h1 h2 h3) (@lem1670584 x a h3)). Qed.
Lemma lem1672483 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) (h1 : term58 x a y b v) (h2 : u = term35) (h3 : real_lt x a) : (term56 y b v) = (term8 y v b).
Proof. exact (prop_ext (fun h4 : term56 y b v => @lem1672482 y b v u x a h4 h2 h3) (fun h4 : term8 y v b => @lem1672453 x a y b v h1)). Qed.
Lemma lem1672484 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) (h1 : term58 x a y b v) (h2 : u = term35) (h3 : real_lt x a) : term8 y v b.
Proof. exact (EQ_MP (@lem1672483 y b v u x a h1 h2 h3) (@lem1672453 x a y b v h1)). Qed.
Lemma lem1672485 (x : real) (a : real) (y : real) (b : real) (v : real) (u : real) (h1 : term58 x a y b v) (h2 : u = term35) : (real_lt x a) = (term8 y v b).
Proof. exact (prop_ext (fun h3 : real_lt x a => @lem1672484 y b v u x a h1 h2 h3) (fun h3 : term8 y v b => @lem1672454 x a y b v h1)). Qed.
Lemma lem1672486 (x : real) (a : real) (y : real) (b : real) (v : real) (u : real) (h1 : term58 x a y b v) (h2 : u = term35) : term8 y v b.
Proof. exact (EQ_MP (@lem1672485 x a y b v u h1 h2) (@lem1672454 x a y b v h1)). Qed.
Lemma lem1672487 (x : real) (a : real) (y : real) (v : real) (b : real) (u : real) (h1 : u = term35) : term69 x a y v b.
Proof. exact (fun h0 : term58 x a y b v => @lem1672486 x a y b v u h0 h1). Qed.
Lemma lem1672488 (x : real) (y : real) (a : real) (v : real) (b : real) (u : real) (h1 : u = term35) : term68 x y u a v b.
Proof. exact (EQ_MP (@lem1670581 x y a v b u h1) (@lem1672487 x a y v b u h1)). Qed.
Lemma lem1672489 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : term68 x y u a v b.
Proof. exact (or_elim (@lem1670480 u) (fun h0 : u = term35 => @lem1672488 x y a v b u h0) (fun h0 : term37 u => @lem1672452 x y a v b u h0)). Qed.
Lemma lem1672494 (x : real) (y : real) (u : real) (a : real) (b : real) : term442 x y u a b.
Proof. exact (fun v : real => @lem1672489 x y u a v b). Qed.
Lemma lem1672499 (x : real) (y : real) (a : real) (b : real) : term443 x y a b.
Proof. exact (fun u : real => @lem1672494 x y u a b). Qed.
Lemma lem1672504 (x : real) (y : real) (b : real) : term444 x y b.
Proof. exact (fun a : real => @lem1672499 x y a b). Qed.
Lemma lem1672509 (x : real) (b : real) : term445 x b.
Proof. exact (fun y : real => @lem1672504 x y b). Qed.
Lemma lem1672514 (b : real) : term446 b.
Proof. exact (fun x : real => @lem1672509 x b). Qed.
