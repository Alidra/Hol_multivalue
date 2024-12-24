Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SGN_ABS_term_abbrevs.
Require Import real_sgn_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm12653_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1482704_spec.
Require Import thm1482981_spec.
Require Import thm1483436_spec.
Require Import thm1483438_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483444_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483456_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483531_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm20234_spec.
Require Import thm20420_spec.
Require Import thm20421_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Lemma lem1715401 (x : real) : term0 x.
Proof. exact (@lem1710164 x). Qed.
Lemma lem1715402 (x : real) : (term0 x) = ((real_sgn x) = (term1 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1715411 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1715402 x) (@lem1715401 x)). Qed.
Lemma lem1715412 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1715413 (x : real) : (term2 x) = (term3 x).
Proof. exact (MK_COMB (@lem1715412) (@lem1715411 x)). Qed.
Lemma lem1715414 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1715415 (x : real) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem1715413 x) (@lem1715414 x)). Qed.
Lemma lem1715416 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1715417 (x : real) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem1715416) (@lem1715415 x)). Qed.
Lemma lem1715418 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1715419 (x : real) : ((term4 x) = x) = ((term5 x) = x).
Proof. exact (MK_COMB (@lem1715417 x) (@lem1715418 x)). Qed.
Lemma lem1715422 : term8 = term9.
Proof. exact (fun_ext (fun x : real => @lem1715419 x)). Qed.
Lemma lem1715423 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1715424 : term10 = term11.
Proof. exact (MK_COMB (@lem1715423) (@lem1715422)). Qed.
Lemma lem1715429 : term11 = term10.
Proof. exact (SYM (@lem1715424)). Qed.
Lemma lem1715438 (P : real -> Prop) : (term12 P) = (term13 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1715439 : term14 = term15.
Proof. exact (@lem1715438 term9). Qed.
Lemma lem1715440 (x : real) : (term16 x) = ((term5 x) = x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1715441 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1715443 (x : real) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1715441) (@lem1715440 x)). Qed.
Lemma lem1715444 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1715443 x)). Qed.
Lemma lem1715445 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1715446 : term15 = term21.
Proof. exact (MK_COMB (@lem1715445) (@lem1715444)). Qed.
Lemma lem1715448 : term14 = term21.
Proof. exact (TRANS (@lem1715439) (@lem1715446)). Qed.
Lemma lem1715452 (x : real) (h1 : (term22 x) = False) : (term22 x) = False.
Proof. exact (h1). Qed.
Lemma lem1715453 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1715454 (x : real) (h1 : (term22 x) = False) : (term23 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1715453) (@lem1715452 x h1)). Qed.
Lemma lem1715455 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1715456 (x : real) (h1 : (term22 x) = False) : (term25 x) = term26.
Proof. exact (MK_COMB (@lem1715454 x h1) (@lem1715455)). Qed.
Lemma lem1715457 (x : real) : (term27 x) = (term27 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1715458 (x : real) (h1 : (term22 x) = False) : (term1 x) = (term28 x).
Proof. exact (MK_COMB (@lem1715456 x h1) (@lem1715457 x)). Qed.
Lemma lem1715460 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1715461 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1715460 real t1 t2). Qed.
Lemma lem1715462 (x : real) : (term28 x) = (term27 x).
Proof. exact (@lem1715461 term24 (term27 x)). Qed.
Lemma lem1715463 (x : real) (h1 : (term22 x) = False) : (term1 x) = (term27 x).
Proof. exact (TRANS (@lem1715458 x h1) (@lem1715462 x)). Qed.
Lemma lem1715464 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1715465 (x : real) (h1 : (term22 x) = False) : (term3 x) = (term29 x).
Proof. exact (MK_COMB (@lem1715464) (@lem1715463 x h1)). Qed.
Lemma lem1715466 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1715467 (x : real) (h1 : (term22 x) = False) : (term5 x) = (term30 x).
Proof. exact (MK_COMB (@lem1715465 x h1) (@lem1715466 x)). Qed.
Lemma lem1715468 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1715469 (x : real) (h1 : (term22 x) = False) : (term7 x) = (term31 x).
Proof. exact (MK_COMB (@lem1715468) (@lem1715467 x h1)). Qed.
Lemma lem1715470 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1715471 (x : real) (h1 : (term22 x) = False) : ((term5 x) = x) = ((term30 x) = x).
Proof. exact (MK_COMB (@lem1715469 x h1) (@lem1715470 x)). Qed.
Lemma lem1715474 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1715475 (x : real) (h1 : (term22 x) = False) : (term18 x) = (term32 x).
Proof. exact (MK_COMB (@lem1715474) (@lem1715471 x h1)). Qed.
Lemma lem1715476 (x : real) : term33 x.
Proof. exact (fun h0 : (term22 x) = False => @lem1715475 x h0). Qed.
Lemma lem1715478 (x : real) (h1 : (term22 x) = True) : (term22 x) = True.
Proof. exact (h1). Qed.
Lemma lem1715479 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1715480 (x : real) (h1 : (term22 x) = True) : (term23 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1715479) (@lem1715478 x h1)). Qed.
Lemma lem1715481 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1715482 (x : real) (h1 : (term22 x) = True) : (term25 x) = term34.
Proof. exact (MK_COMB (@lem1715480 x h1) (@lem1715481)). Qed.
Lemma lem1715483 (x : real) : (term27 x) = (term27 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1715484 (x : real) (h1 : (term22 x) = True) : (term1 x) = (term35 x).
Proof. exact (MK_COMB (@lem1715482 x h1) (@lem1715483 x)). Qed.
Lemma lem1715486 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1715487 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1715486 real t2 t1). Qed.
Lemma lem1715488 (x : real) : (term35 x) = term24.
Proof. exact (@lem1715487 (term27 x) term24). Qed.
Lemma lem1715489 (x : real) (h1 : (term22 x) = True) : (term1 x) = term24.
Proof. exact (TRANS (@lem1715484 x h1) (@lem1715488 x)). Qed.
Lemma lem1715490 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1715491 (x : real) (h1 : (term22 x) = True) : (term3 x) = term36.
Proof. exact (MK_COMB (@lem1715490) (@lem1715489 x h1)). Qed.
Lemma lem1715492 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1715493 (x : real) (h1 : (term22 x) = True) : (term5 x) = (term37 x).
Proof. exact (MK_COMB (@lem1715491 x h1) (@lem1715492 x)). Qed.
Lemma lem1715494 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1715495 (x : real) (h1 : (term22 x) = True) : (term7 x) = (term38 x).
Proof. exact (MK_COMB (@lem1715494) (@lem1715493 x h1)). Qed.
Lemma lem1715496 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1715497 (x : real) (h1 : (term22 x) = True) : ((term5 x) = x) = ((term37 x) = x).
Proof. exact (MK_COMB (@lem1715495 x h1) (@lem1715496 x)). Qed.
Lemma lem1715500 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1715501 (x : real) (h1 : (term22 x) = True) : (term18 x) = (term39 x).
Proof. exact (MK_COMB (@lem1715500) (@lem1715497 x h1)). Qed.
Lemma lem1715502 (x : real) : term40 x.
Proof. exact (fun h0 : (term22 x) = True => @lem1715501 x h0). Qed.
Lemma lem1715503 (x : real) : term41 x.
Proof. exact (conj (@lem1715476 x) (@lem1715502 x)). Qed.
Lemma lem1715505 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term42 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1715506 (x : real) : term43 x.
Proof. exact (@lem1715505 (term18 x) (term39 x) (term22 x) (term32 x)). Qed.
Lemma lem1715521 (x : real) : (term18 x) = (term44 x).
Proof. exact (@lem1715506 x (@lem1715503 x)). Qed.
Lemma lem1715529 (x : real) (h1 : (term45 x) = False) : (term45 x) = False.
Proof. exact (h1). Qed.
Lemma lem1715530 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1715531 (x : real) (h1 : (term45 x) = False) : (term46 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1715530) (@lem1715529 x h1)). Qed.
Lemma lem1715532 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1715533 (x : real) (h1 : (term45 x) = False) : (term48 x) = term49.
Proof. exact (MK_COMB (@lem1715531 x h1) (@lem1715532)). Qed.
Lemma lem1715534 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1715535 (x : real) (h1 : (term45 x) = False) : (term27 x) = term51.
Proof. exact (MK_COMB (@lem1715533 x h1) (@lem1715534)). Qed.
Lemma lem1715537 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1715538 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1715537 real t1 t2). Qed.
Lemma lem1715539 : term51 = term50.
Proof. exact (@lem1715538 term47 term50). Qed.
Lemma lem1715540 (x : real) (h1 : (term45 x) = False) : (term27 x) = term50.
Proof. exact (TRANS (@lem1715535 x h1) (@lem1715539)). Qed.
Lemma lem1715541 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1715542 (x : real) (h1 : (term45 x) = False) : (term29 x) = term52.
Proof. exact (MK_COMB (@lem1715541) (@lem1715540 x h1)). Qed.
Lemma lem1715543 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1715544 (x : real) (h1 : (term45 x) = False) : (term30 x) = (term53 x).
Proof. exact (MK_COMB (@lem1715542 x h1) (@lem1715543 x)). Qed.
Lemma lem1715545 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1715546 (x : real) (h1 : (term45 x) = False) : (term31 x) = (term54 x).
Proof. exact (MK_COMB (@lem1715545) (@lem1715544 x h1)). Qed.
Lemma lem1715547 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1715548 (x : real) (h1 : (term45 x) = False) : ((term30 x) = x) = ((term53 x) = x).
Proof. exact (MK_COMB (@lem1715546 x h1) (@lem1715547 x)). Qed.
Lemma lem1715551 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1715552 (x : real) (h1 : (term45 x) = False) : (term32 x) = (term55 x).
Proof. exact (MK_COMB (@lem1715551) (@lem1715548 x h1)). Qed.
Lemma lem1715553 (x : real) : (term56 x) = (term56 x).
Proof. exact (eq_refl (term56 x)). Qed.
Lemma lem1715554 (x : real) (h1 : (term45 x) = False) : (term57 x) = (term58 x).
Proof. exact (MK_COMB (@lem1715553 x) (@lem1715552 x h1)). Qed.
Lemma lem1715557 (x : real) : (term59 x) = (term59 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1715558 (x : real) (h1 : (term45 x) = False) : (term44 x) = (term60 x).
Proof. exact (MK_COMB (@lem1715557 x) (@lem1715554 x h1)). Qed.
Lemma lem1715561 (x : real) : term61 x.
Proof. exact (fun h0 : (term45 x) = False => @lem1715558 x h0). Qed.
Lemma lem1715567 (x : real) (h1 : (term45 x) = True) : (term45 x) = True.
Proof. exact (h1). Qed.
Lemma lem1715568 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1715569 (x : real) (h1 : (term45 x) = True) : (term46 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1715568) (@lem1715567 x h1)). Qed.
Lemma lem1715570 : term47 = term47.
Proof. exact (eq_refl term47). Qed.
Lemma lem1715571 (x : real) (h1 : (term45 x) = True) : (term48 x) = term62.
Proof. exact (MK_COMB (@lem1715569 x h1) (@lem1715570)). Qed.
Lemma lem1715572 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1715573 (x : real) (h1 : (term45 x) = True) : (term27 x) = term63.
Proof. exact (MK_COMB (@lem1715571 x h1) (@lem1715572)). Qed.
Lemma lem1715575 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1715576 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1715575 real t2 t1). Qed.
Lemma lem1715577 : term63 = term47.
Proof. exact (@lem1715576 term50 term47). Qed.
Lemma lem1715578 (x : real) (h1 : (term45 x) = True) : (term27 x) = term47.
Proof. exact (TRANS (@lem1715573 x h1) (@lem1715577)). Qed.
Lemma lem1715579 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1715580 (x : real) (h1 : (term45 x) = True) : (term29 x) = term64.
Proof. exact (MK_COMB (@lem1715579) (@lem1715578 x h1)). Qed.
Lemma lem1715581 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1715582 (x : real) (h1 : (term45 x) = True) : (term30 x) = (term65 x).
Proof. exact (MK_COMB (@lem1715580 x h1) (@lem1715581 x)). Qed.
Lemma lem1715583 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1715584 (x : real) (h1 : (term45 x) = True) : (term31 x) = (term66 x).
Proof. exact (MK_COMB (@lem1715583) (@lem1715582 x h1)). Qed.
Lemma lem1715585 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1715586 (x : real) (h1 : (term45 x) = True) : ((term30 x) = x) = ((term65 x) = x).
Proof. exact (MK_COMB (@lem1715584 x h1) (@lem1715585 x)). Qed.
Lemma lem1715589 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1715590 (x : real) (h1 : (term45 x) = True) : (term32 x) = (term67 x).
Proof. exact (MK_COMB (@lem1715589) (@lem1715586 x h1)). Qed.
Lemma lem1715591 (x : real) : (term56 x) = (term56 x).
Proof. exact (eq_refl (term56 x)). Qed.
Lemma lem1715592 (x : real) (h1 : (term45 x) = True) : (term57 x) = (term68 x).
Proof. exact (MK_COMB (@lem1715591 x) (@lem1715590 x h1)). Qed.
Lemma lem1715595 (x : real) : (term59 x) = (term59 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1715596 (x : real) (h1 : (term45 x) = True) : (term44 x) = (term69 x).
Proof. exact (MK_COMB (@lem1715595 x) (@lem1715592 x h1)). Qed.
Lemma lem1715599 (x : real) : term70 x.
Proof. exact (fun h0 : (term45 x) = True => @lem1715596 x h0). Qed.
Lemma lem1715600 (x : real) : term71 x.
Proof. exact (conj (@lem1715561 x) (@lem1715599 x)). Qed.
Lemma lem1715602 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term42 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1715603 (x : real) : term72 x.
Proof. exact (@lem1715602 (term44 x) (term69 x) (term45 x) (term60 x)). Qed.
Lemma lem1715672 (x : real) : (term44 x) = (term73 x).
Proof. exact (@lem1715603 x (@lem1715600 x)). Qed.
Lemma lem1715673 (x : real) : (term74 x) = (term74 x).
Proof. exact (eq_refl (term74 x)). Qed.
Lemma lem1715674 (x : real) : ((term18 x) = (term44 x)) = ((term18 x) = (term73 x)).
Proof. exact (MK_COMB (@lem1715673 x) (@lem1715672 x)). Qed.
Lemma lem1715675 (x : real) : (term18 x) = (term73 x).
Proof. exact (EQ_MP (@lem1715674 x) (@lem1715521 x)). Qed.
Lemma lem1715676 : term20 = term75.
Proof. exact (fun_ext (fun x : real => @lem1715675 x)). Qed.
Lemma lem1715677 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1715678 : term21 = term76.
Proof. exact (MK_COMB (@lem1715677) (@lem1715676)). Qed.
Lemma lem1715679 : term14 = term76.
Proof. exact (TRANS (@lem1715448) (@lem1715678)). Qed.
Lemma lem1715680 (x : real) : (term45 x) = (term77 x).
Proof. exact (@lem1483521 term50 x). Qed.
Lemma lem1715686 (x : real) : (term78 x) = (term79 x).
Proof. exact (@lem1483519 term50 x). Qed.
Lemma lem1715691 (x : real) : (term79 x) = (term80 x).
Proof. exact (@lem1483448 (term80 x)). Qed.
Lemma lem1715693 (x : real) : (term78 x) = (term80 x).
Proof. exact (TRANS (@lem1715686 x) (@lem1715691 x)). Qed.
Lemma lem1715694 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715695 (x : real) : (term81 x) = (term82 x).
Proof. exact (MK_COMB (@lem1715694) (@lem1715693 x)). Qed.
Lemma lem1715696 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1715697 (x : real) : (term77 x) = (term83 x).
Proof. exact (MK_COMB (@lem1715695 x) (@lem1715696)). Qed.
Lemma lem1715698 (x : real) : (term45 x) = (term83 x).
Proof. exact (TRANS (@lem1715680 x) (@lem1715697 x)). Qed.
Lemma lem1715699 (x : real) : (term22 x) = (term84 x).
Proof. exact (@lem1483521 x term50). Qed.
Lemma lem1715705 (x : real) : (term85 x) = (term86 x).
Proof. exact (@lem1483519 x term50). Qed.
Lemma lem1715707 (x : nat) : (term87 x) = term50.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1715708 : term88 = term50.
Proof. exact (@lem1715707 term89). Qed.
Lemma lem1715709 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1715710 (x : real) : (term86 x) = (term90 x).
Proof. exact (MK_COMB (@lem1715709 x) (@lem1715708)). Qed.
Lemma lem1715711 (x : real) : (term90 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1715712 (x : real) : (term86 x) = x.
Proof. exact (TRANS (@lem1715710 x) (@lem1715711 x)). Qed.
Lemma lem1715714 (x : real) : (term85 x) = x.
Proof. exact (TRANS (@lem1715705 x) (@lem1715712 x)). Qed.
Lemma lem1715715 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715716 (x : real) : (term91 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1715715) (@lem1715714 x)). Qed.
Lemma lem1715717 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1715718 (x : real) : (term84 x) = (term92 x).
Proof. exact (MK_COMB (@lem1715716 x) (@lem1715717)). Qed.
Lemma lem1715719 (x : real) : (term22 x) = (term92 x).
Proof. exact (TRANS (@lem1715699 x) (@lem1715718 x)). Qed.
Lemma lem1715720 (x : real) : (term39 x) = (term93 x).
Proof. exact (@lem1483554 (term37 x) x). Qed.
Lemma lem1715721 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1715728 (x : real) : (term37 x) = (real_abs x).
Proof. exact (@lem1483460 (real_abs x)). Qed.
Lemma lem1715729 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1715730 (x : real) : (term94 x) = (term95 x).
Proof. exact (MK_COMB (@lem1715729) (@lem1715728 x)). Qed.
Lemma lem1715731 (x : real) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem1715730 x) (@lem1715721 x)). Qed.
Lemma lem1715732 (x : real) : (term97 x) = (term98 x).
Proof. exact (@lem1483519 (real_abs x) x). Qed.
Lemma lem1715737 (x : real) : (term98 x) = (term99 x).
Proof. exact (@lem1483488 (term80 x) (real_abs x)). Qed.
Lemma lem1715738 (x : real) : (term97 x) = (term99 x).
Proof. exact (TRANS (@lem1715732 x) (@lem1715737 x)). Qed.
Lemma lem1715739 (x : real) : (term96 x) = (term99 x).
Proof. exact (TRANS (@lem1715731 x) (@lem1715738 x)). Qed.
Lemma lem1715740 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1715741 (x : real) : (term100 x) = (term101 x).
Proof. exact (MK_COMB (@lem1715740) (@lem1715739 x)). Qed.
Lemma lem1715742 (x : real) : (term101 x) = (term102 x).
Proof. exact (@lem1483512 (term99 x)). Qed.
Lemma lem1715743 (x : real) : (term102 x) = (term103 x).
Proof. exact (@lem1483508 (term80 x) term47 (real_abs x)). Qed.
Lemma lem1715744 (x : real) : (term65 x) = (term65 x).
Proof. exact (eq_refl (term65 x)). Qed.
Lemma lem1715745 (x : real) : (term104 x) = (term105 x).
Proof. exact (@lem1483476 term47 term47 x). Qed.
Lemma lem1715747 (m : nat) (n : nat) : (term106 m n) = (term107 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1715748 : term108 = term109.
Proof. exact (@lem1715747 term89 term89). Qed.
Lemma lem1715749 : (term110 = (BIT1 0)) = (term111 = term89).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1715750 : term111 = term89.
Proof. exact (EQ_MP (@lem1715749) (@lem940073)). Qed.
Lemma lem1715751 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1715752 : term109 = term24.
Proof. exact (MK_COMB (@lem1715751) (@lem1715750)). Qed.
Lemma lem1715753 : term108 = term24.
Proof. exact (TRANS (@lem1715748) (@lem1715752)). Qed.
Lemma lem1715754 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1715755 : term112 = term36.
Proof. exact (MK_COMB (@lem1715754) (@lem1715753)). Qed.
Lemma lem1715756 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1715757 (x : real) : (term105 x) = (term113 x).
Proof. exact (MK_COMB (@lem1715755) (@lem1715756 x)). Qed.
Lemma lem1715758 (x : real) : (term104 x) = (term113 x).
Proof. exact (TRANS (@lem1715745 x) (@lem1715757 x)). Qed.
Lemma lem1715759 (x : real) : (term113 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1715760 (x : real) : (term104 x) = x.
Proof. exact (TRANS (@lem1715758 x) (@lem1715759 x)). Qed.
Lemma lem1715761 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1715762 (x : real) : (term114 x) = (real_add x).
Proof. exact (MK_COMB (@lem1715761) (@lem1715760 x)). Qed.
Lemma lem1715763 (x : real) : (term103 x) = (term115 x).
Proof. exact (MK_COMB (@lem1715762 x) (@lem1715744 x)). Qed.
Lemma lem1715764 (x : real) : (term102 x) = (term115 x).
Proof. exact (TRANS (@lem1715743 x) (@lem1715763 x)). Qed.
Lemma lem1715765 (x : real) : (term101 x) = (term115 x).
Proof. exact (TRANS (@lem1715742 x) (@lem1715764 x)). Qed.
Lemma lem1715766 (x : real) : (term116 x) = (term116 x).
Proof. exact (eq_refl (term116 x)). Qed.
Lemma lem1715767 (x : real) : ((term100 x) = (term101 x)) = ((term100 x) = (term115 x)).
Proof. exact (MK_COMB (@lem1715766 x) (@lem1715765 x)). Qed.
Lemma lem1715768 (x : real) : (term100 x) = (term115 x).
Proof. exact (EQ_MP (@lem1715767 x) (@lem1715741 x)). Qed.
Lemma lem1715769 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715770 (x : real) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1715769) (@lem1715768 x)). Qed.
Lemma lem1715771 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1715772 (x : real) : (term119 x) = (term120 x).
Proof. exact (MK_COMB (@lem1715770 x) (@lem1715771)). Qed.
Lemma lem1715773 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715774 (x : real) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem1715773) (@lem1715739 x)). Qed.
Lemma lem1715775 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1715776 (x : real) : (term123 x) = (term124 x).
Proof. exact (MK_COMB (@lem1715774 x) (@lem1715775)). Qed.
Lemma lem1715777 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1715778 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1715777) (@lem1715776 x)). Qed.
Lemma lem1715779 (x : real) : (term93 x) = (term127 x).
Proof. exact (MK_COMB (@lem1715778 x) (@lem1715772 x)). Qed.
Lemma lem1715780 (x : real) : (term39 x) = (term127 x).
Proof. exact (TRANS (@lem1715720 x) (@lem1715779 x)). Qed.
Lemma lem1715781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1715782 (x : real) : (term128 x) = (term129 x).
Proof. exact (MK_COMB (@lem1715781) (@lem1715719 x)). Qed.
Lemma lem1715783 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1715782 x) (@lem1715780 x)). Qed.
Lemma lem1715784 (x : real) : (term132 x) = (term133 x).
Proof. exact (@lem1483531 term50 x). Qed.
Lemma lem1715790 (x : real) : (term78 x) = (term79 x).
Proof. exact (@lem1483519 term50 x). Qed.
Lemma lem1715795 (x : real) : (term79 x) = (term80 x).
Proof. exact (@lem1483448 (term80 x)). Qed.
Lemma lem1715797 (x : real) : (term78 x) = (term80 x).
Proof. exact (TRANS (@lem1715790 x) (@lem1715795 x)). Qed.
Lemma lem1715798 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1715799 (x : real) : (term134 x) = (term135 x).
Proof. exact (MK_COMB (@lem1715798) (@lem1715797 x)). Qed.
Lemma lem1715800 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1715801 (x : real) : (term133 x) = (term136 x).
Proof. exact (MK_COMB (@lem1715799 x) (@lem1715800)). Qed.
Lemma lem1715802 (x : real) : (term132 x) = (term136 x).
Proof. exact (TRANS (@lem1715784 x) (@lem1715801 x)). Qed.
Lemma lem1715803 (x : real) : (term67 x) = (term137 x).
Proof. exact (@lem1483554 (term65 x) x). Qed.
Lemma lem1715815 (x : real) : (term138 x) = (term139 x).
Proof. exact (@lem1483519 (term65 x) x). Qed.
Lemma lem1715820 (x : real) : (term139 x) = (term140 x).
Proof. exact (@lem1483488 (term80 x) (term65 x)). Qed.
Lemma lem1715822 (x : real) : (term138 x) = (term140 x).
Proof. exact (TRANS (@lem1715815 x) (@lem1715820 x)). Qed.
Lemma lem1715823 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1715824 (x : real) : (term141 x) = (term142 x).
Proof. exact (MK_COMB (@lem1715823) (@lem1715822 x)). Qed.
Lemma lem1715825 (x : real) : (term142 x) = (term143 x).
Proof. exact (@lem1483512 (term140 x)). Qed.
Lemma lem1715826 (x : real) : (term143 x) = (term144 x).
Proof. exact (@lem1483508 (term80 x) term47 (term65 x)). Qed.
Lemma lem1715827 (x : real) : (term145 x) = (term146 x).
Proof. exact (@lem1483476 term47 term47 (real_abs x)). Qed.
Lemma lem1715829 (m : nat) (n : nat) : (term106 m n) = (term107 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1715830 : term108 = term109.
Proof. exact (@lem1715829 term89 term89). Qed.
Lemma lem1715831 : (term110 = (BIT1 0)) = (term111 = term89).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1715832 : term111 = term89.
Proof. exact (EQ_MP (@lem1715831) (@lem940073)). Qed.
Lemma lem1715833 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1715834 : term109 = term24.
Proof. exact (MK_COMB (@lem1715833) (@lem1715832)). Qed.
Lemma lem1715835 : term108 = term24.
Proof. exact (TRANS (@lem1715830) (@lem1715834)). Qed.
Lemma lem1715836 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1715837 : term112 = term36.
Proof. exact (MK_COMB (@lem1715836) (@lem1715835)). Qed.
Lemma lem1715838 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1715839 (x : real) : (term146 x) = (term37 x).
Proof. exact (MK_COMB (@lem1715837) (@lem1715838 x)). Qed.
Lemma lem1715840 (x : real) : (term145 x) = (term37 x).
Proof. exact (TRANS (@lem1715827 x) (@lem1715839 x)). Qed.
Lemma lem1715841 (x : real) : (term37 x) = (real_abs x).
Proof. exact (@lem1483436 (real_abs x)). Qed.
Lemma lem1715842 (x : real) : (term145 x) = (real_abs x).
Proof. exact (TRANS (@lem1715840 x) (@lem1715841 x)). Qed.
Lemma lem1715843 (x : real) : (term104 x) = (term105 x).
Proof. exact (@lem1483476 term47 term47 x). Qed.
Lemma lem1715845 (m : nat) (n : nat) : (term106 m n) = (term107 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1715846 : term108 = term109.
Proof. exact (@lem1715845 term89 term89). Qed.
Lemma lem1715847 : (term110 = (BIT1 0)) = (term111 = term89).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1715848 : term111 = term89.
Proof. exact (EQ_MP (@lem1715847) (@lem940073)). Qed.
Lemma lem1715849 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1715850 : term109 = term24.
Proof. exact (MK_COMB (@lem1715849) (@lem1715848)). Qed.
Lemma lem1715851 : term108 = term24.
Proof. exact (TRANS (@lem1715846) (@lem1715850)). Qed.
Lemma lem1715852 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1715853 : term112 = term36.
Proof. exact (MK_COMB (@lem1715852) (@lem1715851)). Qed.
Lemma lem1715854 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1715855 (x : real) : (term105 x) = (term113 x).
Proof. exact (MK_COMB (@lem1715853) (@lem1715854 x)). Qed.
Lemma lem1715856 (x : real) : (term104 x) = (term113 x).
Proof. exact (TRANS (@lem1715843 x) (@lem1715855 x)). Qed.
Lemma lem1715857 (x : real) : (term113 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1715858 (x : real) : (term104 x) = x.
Proof. exact (TRANS (@lem1715856 x) (@lem1715857 x)). Qed.
Lemma lem1715859 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1715860 (x : real) : (term114 x) = (real_add x).
Proof. exact (MK_COMB (@lem1715859) (@lem1715858 x)). Qed.
Lemma lem1715861 (x : real) : (term144 x) = (term147 x).
Proof. exact (MK_COMB (@lem1715860 x) (@lem1715842 x)). Qed.
Lemma lem1715862 (x : real) : (term143 x) = (term147 x).
Proof. exact (TRANS (@lem1715826 x) (@lem1715861 x)). Qed.
Lemma lem1715863 (x : real) : (term142 x) = (term147 x).
Proof. exact (TRANS (@lem1715825 x) (@lem1715862 x)). Qed.
Lemma lem1715864 (x : real) : (term148 x) = (term148 x).
Proof. exact (eq_refl (term148 x)). Qed.
Lemma lem1715865 (x : real) : ((term141 x) = (term142 x)) = ((term141 x) = (term147 x)).
Proof. exact (MK_COMB (@lem1715864 x) (@lem1715863 x)). Qed.
Lemma lem1715866 (x : real) : (term141 x) = (term147 x).
Proof. exact (EQ_MP (@lem1715865 x) (@lem1715824 x)). Qed.
Lemma lem1715867 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715868 (x : real) : (term149 x) = (term150 x).
Proof. exact (MK_COMB (@lem1715867) (@lem1715866 x)). Qed.
Lemma lem1715869 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1715870 (x : real) : (term151 x) = (term152 x).
Proof. exact (MK_COMB (@lem1715868 x) (@lem1715869)). Qed.
Lemma lem1715871 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715872 (x : real) : (term153 x) = (term154 x).
Proof. exact (MK_COMB (@lem1715871) (@lem1715822 x)). Qed.
Lemma lem1715873 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1715874 (x : real) : (term155 x) = (term156 x).
Proof. exact (MK_COMB (@lem1715872 x) (@lem1715873)). Qed.
Lemma lem1715875 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1715876 (x : real) : (term157 x) = (term158 x).
Proof. exact (MK_COMB (@lem1715875) (@lem1715874 x)). Qed.
Lemma lem1715877 (x : real) : (term137 x) = (term159 x).
Proof. exact (MK_COMB (@lem1715876 x) (@lem1715870 x)). Qed.
Lemma lem1715878 (x : real) : (term67 x) = (term159 x).
Proof. exact (TRANS (@lem1715803 x) (@lem1715877 x)). Qed.
Lemma lem1715879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1715880 (x : real) : (term56 x) = (term160 x).
Proof. exact (MK_COMB (@lem1715879) (@lem1715802 x)). Qed.
Lemma lem1715881 (x : real) : (term68 x) = (term161 x).
Proof. exact (MK_COMB (@lem1715880 x) (@lem1715878 x)). Qed.
Lemma lem1715882 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1715883 (x : real) : (term59 x) = (term162 x).
Proof. exact (MK_COMB (@lem1715882) (@lem1715783 x)). Qed.
Lemma lem1715884 (x : real) : (term69 x) = (term163 x).
Proof. exact (MK_COMB (@lem1715883 x) (@lem1715881 x)). Qed.
Lemma lem1715885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1715886 (x : real) : (term164 x) = (term165 x).
Proof. exact (MK_COMB (@lem1715885) (@lem1715698 x)). Qed.
Lemma lem1715887 (x : real) : (term166 x) = (term167 x).
Proof. exact (MK_COMB (@lem1715886 x) (@lem1715884 x)). Qed.
Lemma lem1715888 (x : real) : (term168 x) = (term169 x).
Proof. exact (@lem1483531 x term50). Qed.
Lemma lem1715894 (x : real) : (term85 x) = (term86 x).
Proof. exact (@lem1483519 x term50). Qed.
Lemma lem1715896 (x : nat) : (term87 x) = term50.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1715897 : term88 = term50.
Proof. exact (@lem1715896 term89). Qed.
Lemma lem1715898 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1715899 (x : real) : (term86 x) = (term90 x).
Proof. exact (MK_COMB (@lem1715898 x) (@lem1715897)). Qed.
Lemma lem1715900 (x : real) : (term90 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1715901 (x : real) : (term86 x) = x.
Proof. exact (TRANS (@lem1715899 x) (@lem1715900 x)). Qed.
Lemma lem1715903 (x : real) : (term85 x) = x.
Proof. exact (TRANS (@lem1715894 x) (@lem1715901 x)). Qed.
Lemma lem1715904 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1715905 (x : real) : (term170 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1715904) (@lem1715903 x)). Qed.
Lemma lem1715906 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1715907 (x : real) : (term169 x) = (term171 x).
Proof. exact (MK_COMB (@lem1715905 x) (@lem1715906)). Qed.
Lemma lem1715908 (x : real) : (term168 x) = (term171 x).
Proof. exact (TRANS (@lem1715888 x) (@lem1715907 x)). Qed.
Lemma lem1715909 (x : real) : (term22 x) = (term84 x).
Proof. exact (@lem1483521 x term50). Qed.
Lemma lem1715915 (x : real) : (term85 x) = (term86 x).
Proof. exact (@lem1483519 x term50). Qed.
Lemma lem1715917 (x : nat) : (term87 x) = term50.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1715918 : term88 = term50.
Proof. exact (@lem1715917 term89). Qed.
Lemma lem1715919 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1715920 (x : real) : (term86 x) = (term90 x).
Proof. exact (MK_COMB (@lem1715919 x) (@lem1715918)). Qed.
Lemma lem1715921 (x : real) : (term90 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1715922 (x : real) : (term86 x) = x.
Proof. exact (TRANS (@lem1715920 x) (@lem1715921 x)). Qed.
Lemma lem1715924 (x : real) : (term85 x) = x.
Proof. exact (TRANS (@lem1715915 x) (@lem1715922 x)). Qed.
Lemma lem1715925 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715926 (x : real) : (term91 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1715925) (@lem1715924 x)). Qed.
Lemma lem1715927 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1715928 (x : real) : (term84 x) = (term92 x).
Proof. exact (MK_COMB (@lem1715926 x) (@lem1715927)). Qed.
Lemma lem1715929 (x : real) : (term22 x) = (term92 x).
Proof. exact (TRANS (@lem1715909 x) (@lem1715928 x)). Qed.
Lemma lem1715930 (x : real) : (term39 x) = (term93 x).
Proof. exact (@lem1483554 (term37 x) x). Qed.
Lemma lem1715931 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1715938 (x : real) : (term37 x) = (real_abs x).
Proof. exact (@lem1483460 (real_abs x)). Qed.
Lemma lem1715939 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1715940 (x : real) : (term94 x) = (term95 x).
Proof. exact (MK_COMB (@lem1715939) (@lem1715938 x)). Qed.
Lemma lem1715941 (x : real) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem1715940 x) (@lem1715931 x)). Qed.
Lemma lem1715942 (x : real) : (term97 x) = (term98 x).
Proof. exact (@lem1483519 (real_abs x) x). Qed.
Lemma lem1715947 (x : real) : (term98 x) = (term99 x).
Proof. exact (@lem1483488 (term80 x) (real_abs x)). Qed.
Lemma lem1715948 (x : real) : (term97 x) = (term99 x).
Proof. exact (TRANS (@lem1715942 x) (@lem1715947 x)). Qed.
Lemma lem1715949 (x : real) : (term96 x) = (term99 x).
Proof. exact (TRANS (@lem1715941 x) (@lem1715948 x)). Qed.
Lemma lem1715950 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1715951 (x : real) : (term100 x) = (term101 x).
Proof. exact (MK_COMB (@lem1715950) (@lem1715949 x)). Qed.
Lemma lem1715952 (x : real) : (term101 x) = (term102 x).
Proof. exact (@lem1483512 (term99 x)). Qed.
Lemma lem1715953 (x : real) : (term102 x) = (term103 x).
Proof. exact (@lem1483508 (term80 x) term47 (real_abs x)). Qed.
Lemma lem1715954 (x : real) : (term65 x) = (term65 x).
Proof. exact (eq_refl (term65 x)). Qed.
Lemma lem1715955 (x : real) : (term104 x) = (term105 x).
Proof. exact (@lem1483476 term47 term47 x). Qed.
Lemma lem1715957 (m : nat) (n : nat) : (term106 m n) = (term107 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1715958 : term108 = term109.
Proof. exact (@lem1715957 term89 term89). Qed.
Lemma lem1715959 : (term110 = (BIT1 0)) = (term111 = term89).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1715960 : term111 = term89.
Proof. exact (EQ_MP (@lem1715959) (@lem940073)). Qed.
Lemma lem1715961 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1715962 : term109 = term24.
Proof. exact (MK_COMB (@lem1715961) (@lem1715960)). Qed.
Lemma lem1715963 : term108 = term24.
Proof. exact (TRANS (@lem1715958) (@lem1715962)). Qed.
Lemma lem1715964 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1715965 : term112 = term36.
Proof. exact (MK_COMB (@lem1715964) (@lem1715963)). Qed.
Lemma lem1715966 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1715967 (x : real) : (term105 x) = (term113 x).
Proof. exact (MK_COMB (@lem1715965) (@lem1715966 x)). Qed.
Lemma lem1715968 (x : real) : (term104 x) = (term113 x).
Proof. exact (TRANS (@lem1715955 x) (@lem1715967 x)). Qed.
Lemma lem1715969 (x : real) : (term113 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1715970 (x : real) : (term104 x) = x.
Proof. exact (TRANS (@lem1715968 x) (@lem1715969 x)). Qed.
Lemma lem1715971 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1715972 (x : real) : (term114 x) = (real_add x).
Proof. exact (MK_COMB (@lem1715971) (@lem1715970 x)). Qed.
Lemma lem1715973 (x : real) : (term103 x) = (term115 x).
Proof. exact (MK_COMB (@lem1715972 x) (@lem1715954 x)). Qed.
Lemma lem1715974 (x : real) : (term102 x) = (term115 x).
Proof. exact (TRANS (@lem1715953 x) (@lem1715973 x)). Qed.
Lemma lem1715975 (x : real) : (term101 x) = (term115 x).
Proof. exact (TRANS (@lem1715952 x) (@lem1715974 x)). Qed.
Lemma lem1715976 (x : real) : (term116 x) = (term116 x).
Proof. exact (eq_refl (term116 x)). Qed.
Lemma lem1715977 (x : real) : ((term100 x) = (term101 x)) = ((term100 x) = (term115 x)).
Proof. exact (MK_COMB (@lem1715976 x) (@lem1715975 x)). Qed.
Lemma lem1715978 (x : real) : (term100 x) = (term115 x).
Proof. exact (EQ_MP (@lem1715977 x) (@lem1715951 x)). Qed.
Lemma lem1715979 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715980 (x : real) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1715979) (@lem1715978 x)). Qed.
Lemma lem1715981 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1715982 (x : real) : (term119 x) = (term120 x).
Proof. exact (MK_COMB (@lem1715980 x) (@lem1715981)). Qed.
Lemma lem1715983 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715984 (x : real) : (term121 x) = (term122 x).
Proof. exact (MK_COMB (@lem1715983) (@lem1715949 x)). Qed.
Lemma lem1715985 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1715986 (x : real) : (term123 x) = (term124 x).
Proof. exact (MK_COMB (@lem1715984 x) (@lem1715985)). Qed.
Lemma lem1715987 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1715988 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1715987) (@lem1715986 x)). Qed.
Lemma lem1715989 (x : real) : (term93 x) = (term127 x).
Proof. exact (MK_COMB (@lem1715988 x) (@lem1715982 x)). Qed.
Lemma lem1715990 (x : real) : (term39 x) = (term127 x).
Proof. exact (TRANS (@lem1715930 x) (@lem1715989 x)). Qed.
Lemma lem1715991 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1715992 (x : real) : (term128 x) = (term129 x).
Proof. exact (MK_COMB (@lem1715991) (@lem1715929 x)). Qed.
Lemma lem1715993 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1715992 x) (@lem1715990 x)). Qed.
Lemma lem1715994 (x : real) : (term132 x) = (term133 x).
Proof. exact (@lem1483531 term50 x). Qed.
Lemma lem1716000 (x : real) : (term78 x) = (term79 x).
Proof. exact (@lem1483519 term50 x). Qed.
Lemma lem1716005 (x : real) : (term79 x) = (term80 x).
Proof. exact (@lem1483448 (term80 x)). Qed.
Lemma lem1716007 (x : real) : (term78 x) = (term80 x).
Proof. exact (TRANS (@lem1716000 x) (@lem1716005 x)). Qed.
Lemma lem1716008 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1716009 (x : real) : (term134 x) = (term135 x).
Proof. exact (MK_COMB (@lem1716008) (@lem1716007 x)). Qed.
Lemma lem1716010 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716011 (x : real) : (term133 x) = (term136 x).
Proof. exact (MK_COMB (@lem1716009 x) (@lem1716010)). Qed.
Lemma lem1716012 (x : real) : (term132 x) = (term136 x).
Proof. exact (TRANS (@lem1715994 x) (@lem1716011 x)). Qed.
Lemma lem1716013 (x : real) : (term55 x) = (term172 x).
Proof. exact (@lem1483554 (term53 x) x). Qed.
Lemma lem1716014 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1716021 (x : real) : (term53 x) = term50.
Proof. exact (@lem1483456 (real_abs x)). Qed.
Lemma lem1716022 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1716023 (x : real) : (term173 x) = term174.
Proof. exact (MK_COMB (@lem1716022) (@lem1716021 x)). Qed.
Lemma lem1716024 (x : real) : (term175 x) = (term78 x).
Proof. exact (MK_COMB (@lem1716023 x) (@lem1716014 x)). Qed.
Lemma lem1716025 (x : real) : (term78 x) = (term79 x).
Proof. exact (@lem1483519 term50 x). Qed.
Lemma lem1716030 (x : real) : (term79 x) = (term80 x).
Proof. exact (@lem1483448 (term80 x)). Qed.
Lemma lem1716031 (x : real) : (term78 x) = (term80 x).
Proof. exact (TRANS (@lem1716025 x) (@lem1716030 x)). Qed.
Lemma lem1716032 (x : real) : (term175 x) = (term80 x).
Proof. exact (TRANS (@lem1716024 x) (@lem1716031 x)). Qed.
Lemma lem1716033 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1716034 (x : real) : (term176 x) = (term177 x).
Proof. exact (MK_COMB (@lem1716033) (@lem1716032 x)). Qed.
Lemma lem1716035 (x : real) : (term177 x) = (term104 x).
Proof. exact (@lem1483512 (term80 x)). Qed.
Lemma lem1716036 (x : real) : (term104 x) = (term105 x).
Proof. exact (@lem1483476 term47 term47 x). Qed.
Lemma lem1716038 (m : nat) (n : nat) : (term106 m n) = (term107 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1716039 : term108 = term109.
Proof. exact (@lem1716038 term89 term89). Qed.
Lemma lem1716040 : (term110 = (BIT1 0)) = (term111 = term89).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1716041 : term111 = term89.
Proof. exact (EQ_MP (@lem1716040) (@lem940073)). Qed.
Lemma lem1716042 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1716043 : term109 = term24.
Proof. exact (MK_COMB (@lem1716042) (@lem1716041)). Qed.
Lemma lem1716044 : term108 = term24.
Proof. exact (TRANS (@lem1716039) (@lem1716043)). Qed.
Lemma lem1716045 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1716046 : term112 = term36.
Proof. exact (MK_COMB (@lem1716045) (@lem1716044)). Qed.
Lemma lem1716047 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1716048 (x : real) : (term105 x) = (term113 x).
Proof. exact (MK_COMB (@lem1716046) (@lem1716047 x)). Qed.
Lemma lem1716049 (x : real) : (term104 x) = (term113 x).
Proof. exact (TRANS (@lem1716036 x) (@lem1716048 x)). Qed.
Lemma lem1716050 (x : real) : (term113 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1716051 (x : real) : (term104 x) = x.
Proof. exact (TRANS (@lem1716049 x) (@lem1716050 x)). Qed.
Lemma lem1716052 (x : real) : (term177 x) = x.
Proof. exact (TRANS (@lem1716035 x) (@lem1716051 x)). Qed.
Lemma lem1716053 (x : real) : (term178 x) = (term178 x).
Proof. exact (eq_refl (term178 x)). Qed.
Lemma lem1716054 (x : real) : ((term176 x) = (term177 x)) = ((term176 x) = x).
Proof. exact (MK_COMB (@lem1716053 x) (@lem1716052 x)). Qed.
Lemma lem1716055 (x : real) : (term176 x) = x.
Proof. exact (EQ_MP (@lem1716054 x) (@lem1716034 x)). Qed.
Lemma lem1716056 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1716057 (x : real) : (term179 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1716056) (@lem1716055 x)). Qed.
Lemma lem1716058 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716059 (x : real) : (term180 x) = (term92 x).
Proof. exact (MK_COMB (@lem1716057 x) (@lem1716058)). Qed.
Lemma lem1716060 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1716061 (x : real) : (term181 x) = (term82 x).
Proof. exact (MK_COMB (@lem1716060) (@lem1716032 x)). Qed.
Lemma lem1716062 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716063 (x : real) : (term182 x) = (term83 x).
Proof. exact (MK_COMB (@lem1716061 x) (@lem1716062)). Qed.
Lemma lem1716064 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716065 (x : real) : (term183 x) = (term184 x).
Proof. exact (MK_COMB (@lem1716064) (@lem1716063 x)). Qed.
Lemma lem1716066 (x : real) : (term172 x) = (term185 x).
Proof. exact (MK_COMB (@lem1716065 x) (@lem1716059 x)). Qed.
Lemma lem1716067 (x : real) : (term55 x) = (term185 x).
Proof. exact (TRANS (@lem1716013 x) (@lem1716066 x)). Qed.
Lemma lem1716068 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716069 (x : real) : (term56 x) = (term160 x).
Proof. exact (MK_COMB (@lem1716068) (@lem1716012 x)). Qed.
Lemma lem1716070 (x : real) : (term58 x) = (term186 x).
Proof. exact (MK_COMB (@lem1716069 x) (@lem1716067 x)). Qed.
Lemma lem1716071 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716072 (x : real) : (term59 x) = (term162 x).
Proof. exact (MK_COMB (@lem1716071) (@lem1715993 x)). Qed.
Lemma lem1716073 (x : real) : (term60 x) = (term187 x).
Proof. exact (MK_COMB (@lem1716072 x) (@lem1716070 x)). Qed.
Lemma lem1716074 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716075 (x : real) : (term188 x) = (term189 x).
Proof. exact (MK_COMB (@lem1716074) (@lem1715908 x)). Qed.
Lemma lem1716076 (x : real) : (term190 x) = (term191 x).
Proof. exact (MK_COMB (@lem1716075 x) (@lem1716073 x)). Qed.
Lemma lem1716077 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716078 (x : real) : (term192 x) = (term193 x).
Proof. exact (MK_COMB (@lem1716077) (@lem1715887 x)). Qed.
Lemma lem1716079 (x : real) : (term73 x) = (term194 x).
Proof. exact (MK_COMB (@lem1716078 x) (@lem1716076 x)). Qed.
Lemma lem1716080 : term75 = term195.
Proof. exact (fun_ext (fun x : real => @lem1716079 x)). Qed.
Lemma lem1716081 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1716082 : term76 = term196.
Proof. exact (MK_COMB (@lem1716081) (@lem1716080)). Qed.
Lemma lem1716083 : term14 = term196.
Proof. exact (TRANS (@lem1715679) (@lem1716082)). Qed.
Lemma lem1716085 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1716086 (P : real -> Prop) (Q : real -> Prop) : (term199 P Q) = (term200 P Q).
Proof. exact (@lem1716085 real P Q). Qed.
Lemma lem1716087 : term201 = term202.
Proof. exact (@lem1716086 term203 term204). Qed.
Lemma lem1716088 (x : real) : (term205 x) = (term167 x).
Proof. exact (eq_refl (term205 x)). Qed.
Lemma lem1716089 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716090 (x : real) : (term206 x) = (term193 x).
Proof. exact (MK_COMB (@lem1716089) (@lem1716088 x)). Qed.
Lemma lem1716091 (x : real) : (term207 x) = (term191 x).
Proof. exact (eq_refl (term207 x)). Qed.
Lemma lem1716092 (x : real) : (term208 x) = (term194 x).
Proof. exact (MK_COMB (@lem1716090 x) (@lem1716091 x)). Qed.
Lemma lem1716093 : term209 = term195.
Proof. exact (fun_ext (fun x : real => @lem1716092 x)). Qed.
Lemma lem1716094 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1716095 : term201 = term196.
Proof. exact (MK_COMB (@lem1716094) (@lem1716093)). Qed.
Lemma lem1716096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1716097 : term210 = term211.
Proof. exact (MK_COMB (@lem1716096) (@lem1716095)). Qed.
Lemma lem1716098 (x : real) : (term205 x) = (term167 x).
Proof. exact (eq_refl (term205 x)). Qed.
Lemma lem1716099 : term212 = term203.
Proof. exact (fun_ext (fun x : real => @lem1716098 x)). Qed.
Lemma lem1716100 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1716101 : term213 = term214.
Proof. exact (MK_COMB (@lem1716100) (@lem1716099)). Qed.
Lemma lem1716102 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716103 : term215 = term216.
Proof. exact (MK_COMB (@lem1716102) (@lem1716101)). Qed.
Lemma lem1716104 (x : real) : (term207 x) = (term191 x).
Proof. exact (eq_refl (term207 x)). Qed.
Lemma lem1716105 : term217 = term204.
Proof. exact (fun_ext (fun x : real => @lem1716104 x)). Qed.
Lemma lem1716106 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1716107 : term218 = term219.
Proof. exact (MK_COMB (@lem1716106) (@lem1716105)). Qed.
Lemma lem1716108 : term202 = term220.
Proof. exact (MK_COMB (@lem1716103) (@lem1716107)). Qed.
Lemma lem1716109 : (term201 = term202) = (term196 = term220).
Proof. exact (MK_COMB (@lem1716097) (@lem1716108)). Qed.
Lemma lem1716110 : term196 = term220.
Proof. exact (EQ_MP (@lem1716109) (@lem1716087)). Qed.
Lemma lem1716208 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term198 A P Q) = (term197 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1716209 (P : real -> Prop) (Q : real -> Prop) : (term200 P Q) = (term199 P Q).
Proof. exact (@lem1716208 real P Q). Qed.
Lemma lem1716210 : term202 = term201.
Proof. exact (@lem1716209 term203 term204). Qed.
Lemma lem1716211 (x : real) : (term205 x) = (term167 x).
Proof. exact (eq_refl (term205 x)). Qed.
Lemma lem1716212 : term212 = term203.
Proof. exact (fun_ext (fun x : real => @lem1716211 x)). Qed.
Lemma lem1716213 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1716214 : term213 = term214.
Proof. exact (MK_COMB (@lem1716213) (@lem1716212)). Qed.
Lemma lem1716215 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716216 : term215 = term216.
Proof. exact (MK_COMB (@lem1716215) (@lem1716214)). Qed.
Lemma lem1716217 (x : real) : (term207 x) = (term191 x).
Proof. exact (eq_refl (term207 x)). Qed.
Lemma lem1716218 : term217 = term204.
Proof. exact (fun_ext (fun x : real => @lem1716217 x)). Qed.
Lemma lem1716219 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1716220 : term218 = term219.
Proof. exact (MK_COMB (@lem1716219) (@lem1716218)). Qed.
Lemma lem1716221 : term202 = term220.
Proof. exact (MK_COMB (@lem1716216) (@lem1716220)). Qed.
Lemma lem1716222 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1716223 : term221 = term222.
Proof. exact (MK_COMB (@lem1716222) (@lem1716221)). Qed.
Lemma lem1716224 (x : real) : (term205 x) = (term167 x).
Proof. exact (eq_refl (term205 x)). Qed.
Lemma lem1716225 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716226 (x : real) : (term206 x) = (term193 x).
Proof. exact (MK_COMB (@lem1716225) (@lem1716224 x)). Qed.
Lemma lem1716227 (x : real) : (term207 x) = (term191 x).
Proof. exact (eq_refl (term207 x)). Qed.
Lemma lem1716228 (x : real) : (term208 x) = (term194 x).
Proof. exact (MK_COMB (@lem1716226 x) (@lem1716227 x)). Qed.
Lemma lem1716229 : term209 = term195.
Proof. exact (fun_ext (fun x : real => @lem1716228 x)). Qed.
Lemma lem1716230 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1716231 : term201 = term196.
Proof. exact (MK_COMB (@lem1716230) (@lem1716229)). Qed.
Lemma lem1716232 : (term202 = term201) = (term220 = term196).
Proof. exact (MK_COMB (@lem1716223) (@lem1716231)). Qed.
Lemma lem1716233 : term220 = term196.
Proof. exact (EQ_MP (@lem1716232) (@lem1716210)). Qed.
Lemma lem1716234 : term196 = term196.
Proof. exact (TRANS (@lem1716110) (@lem1716233)). Qed.
Lemma lem1716237 : term14 = term196.
Proof. exact (TRANS (@lem1716083) (@lem1716234)). Qed.
Lemma lem1716254 (x : real) : (term186 x) = (term223 x).
Proof. exact (@lem19158 (term83 x) (term136 x) (term92 x)). Qed.
Lemma lem1716271 (x : real) : (term131 x) = (term224 x).
Proof. exact (@lem19158 (term124 x) (term92 x) (term120 x)). Qed.
Lemma lem1716272 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716273 (x : real) : (term162 x) = (term225 x).
Proof. exact (MK_COMB (@lem1716272) (@lem1716271 x)). Qed.
Lemma lem1716274 (x : real) : (term187 x) = (term226 x).
Proof. exact (MK_COMB (@lem1716273 x) (@lem1716254 x)). Qed.
Lemma lem1716277 (x : real) : (term189 x) = (term189 x).
Proof. exact (eq_refl (term189 x)). Qed.
Lemma lem1716278 (x : real) : (term191 x) = (term227 x).
Proof. exact (MK_COMB (@lem1716277 x) (@lem1716274 x)). Qed.
Lemma lem1716279 (x : real) : (term227 x) = (term228 x).
Proof. exact (@lem19158 (term224 x) (term171 x) (term223 x)). Qed.
Lemma lem1716286 (x : real) : (term229 x) = (term230 x).
Proof. exact (@lem19158 (term231 x) (term171 x) (term232 x)). Qed.
Lemma lem1716293 (x : real) : (term233 x) = (term234 x).
Proof. exact (@lem19158 (term235 x) (term171 x) (term236 x)). Qed.
Lemma lem1716294 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716295 (x : real) : (term237 x) = (term238 x).
Proof. exact (MK_COMB (@lem1716294) (@lem1716293 x)). Qed.
Lemma lem1716296 (x : real) : (term228 x) = (term239 x).
Proof. exact (MK_COMB (@lem1716295 x) (@lem1716286 x)). Qed.
Lemma lem1716297 (x : real) : (term227 x) = (term239 x).
Proof. exact (TRANS (@lem1716279 x) (@lem1716296 x)). Qed.
Lemma lem1716298 (x : real) : (term191 x) = (term239 x).
Proof. exact (TRANS (@lem1716278 x) (@lem1716297 x)). Qed.
Lemma lem1716315 (x : real) : (term161 x) = (term240 x).
Proof. exact (@lem19158 (term156 x) (term136 x) (term152 x)). Qed.
Lemma lem1716332 (x : real) : (term131 x) = (term224 x).
Proof. exact (@lem19158 (term124 x) (term92 x) (term120 x)). Qed.
Lemma lem1716333 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716334 (x : real) : (term162 x) = (term225 x).
Proof. exact (MK_COMB (@lem1716333) (@lem1716332 x)). Qed.
Lemma lem1716335 (x : real) : (term163 x) = (term241 x).
Proof. exact (MK_COMB (@lem1716334 x) (@lem1716315 x)). Qed.
Lemma lem1716338 (x : real) : (term165 x) = (term165 x).
Proof. exact (eq_refl (term165 x)). Qed.
Lemma lem1716339 (x : real) : (term167 x) = (term242 x).
Proof. exact (MK_COMB (@lem1716338 x) (@lem1716335 x)). Qed.
Lemma lem1716340 (x : real) : (term242 x) = (term243 x).
Proof. exact (@lem19158 (term224 x) (term83 x) (term240 x)). Qed.
Lemma lem1716347 (x : real) : (term244 x) = (term245 x).
Proof. exact (@lem19158 (term246 x) (term83 x) (term247 x)). Qed.
Lemma lem1716354 (x : real) : (term248 x) = (term249 x).
Proof. exact (@lem19158 (term235 x) (term83 x) (term236 x)). Qed.
Lemma lem1716355 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716356 (x : real) : (term250 x) = (term251 x).
Proof. exact (MK_COMB (@lem1716355) (@lem1716354 x)). Qed.
Lemma lem1716357 (x : real) : (term243 x) = (term252 x).
Proof. exact (MK_COMB (@lem1716356 x) (@lem1716347 x)). Qed.
Lemma lem1716358 (x : real) : (term242 x) = (term252 x).
Proof. exact (TRANS (@lem1716340 x) (@lem1716357 x)). Qed.
Lemma lem1716359 (x : real) : (term167 x) = (term252 x).
Proof. exact (TRANS (@lem1716339 x) (@lem1716358 x)). Qed.
Lemma lem1716360 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716361 (x : real) : (term193 x) = (term253 x).
Proof. exact (MK_COMB (@lem1716360) (@lem1716359 x)). Qed.
Lemma lem1716362 (x : real) : (term194 x) = (term254 x).
Proof. exact (MK_COMB (@lem1716361 x) (@lem1716298 x)). Qed.
Lemma lem1716363 : term195 = term255.
Proof. exact (fun_ext (fun x : real => @lem1716362 x)). Qed.
Lemma lem1716364 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1716365 : term196 = term256.
Proof. exact (MK_COMB (@lem1716364) (@lem1716363)). Qed.
Lemma lem1716366 : term14 = term256.
Proof. exact (TRANS (@lem1716237) (@lem1716365)). Qed.
Lemma lem1716368 (x : real) : (term257 x) = (term258 x).
Proof. exact (eq_refl (term257 x)). Qed.
Lemma lem1716369 (x : real) : (term258 x) = (term257 x).
Proof. exact (SYM (@lem1716368 x)). Qed.
Lemma lem1716370 (x : real) : (term257 x) = (term259 x).
Proof. exact (@lem1482981 (term260 x) x). Qed.
Lemma lem1716371 (x : real) : (term258 x) = (term259 x).
Proof. exact (TRANS (@lem1716369 x) (@lem1716370 x)). Qed.
Lemma lem1716372 (x : real) : (term261 x) = (term262 x).
Proof. exact (eq_refl (term261 x)). Qed.
Lemma lem1716373 (x : real) : (term263 x) = (term263 x).
Proof. exact (eq_refl (term263 x)). Qed.
Lemma lem1716374 (x : real) : (term264 x) = (term265 x).
Proof. exact (MK_COMB (@lem1716373 x) (@lem1716372 x)). Qed.
Lemma lem1716375 (x : real) : (term266 x) = (term267 x).
Proof. exact (eq_refl (term266 x)). Qed.
Lemma lem1716376 (x : real) : (term189 x) = (term189 x).
Proof. exact (eq_refl (term189 x)). Qed.
Lemma lem1716377 (x : real) : (term268 x) = (term269 x).
Proof. exact (MK_COMB (@lem1716376 x) (@lem1716375 x)). Qed.
Lemma lem1716378 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716379 (x : real) : (term270 x) = (term271 x).
Proof. exact (MK_COMB (@lem1716378) (@lem1716377 x)). Qed.
Lemma lem1716380 (x : real) : (term259 x) = (term272 x).
Proof. exact (MK_COMB (@lem1716379 x) (@lem1716374 x)). Qed.
Lemma lem1716381 (x : real) : (term273 x) = (term273 x).
Proof. exact (eq_refl (term273 x)). Qed.
Lemma lem1716382 (x : real) : ((term258 x) = (term259 x)) = ((term258 x) = (term272 x)).
Proof. exact (MK_COMB (@lem1716381 x) (@lem1716380 x)). Qed.
Lemma lem1716383 (x : real) : (term258 x) = (term272 x).
Proof. exact (EQ_MP (@lem1716382 x) (@lem1716371 x)). Qed.
Lemma lem1716384 (x : real) : (term171 x) = (term169 x).
Proof. exact (@lem1483527 x term50). Qed.
Lemma lem1716390 (x : real) : (term85 x) = (term86 x).
Proof. exact (@lem1483519 x term50). Qed.
Lemma lem1716392 (x : nat) : (term87 x) = term50.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1716393 : term88 = term50.
Proof. exact (@lem1716392 term89). Qed.
Lemma lem1716394 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1716395 (x : real) : (term86 x) = (term90 x).
Proof. exact (MK_COMB (@lem1716394 x) (@lem1716393)). Qed.
Lemma lem1716396 (x : real) : (term90 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1716397 (x : real) : (term86 x) = x.
Proof. exact (TRANS (@lem1716395 x) (@lem1716396 x)). Qed.
Lemma lem1716399 (x : real) : (term85 x) = x.
Proof. exact (TRANS (@lem1716390 x) (@lem1716397 x)). Qed.
Lemma lem1716400 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1716401 (x : real) : (term170 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1716400) (@lem1716399 x)). Qed.
Lemma lem1716402 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716403 (x : real) : (term169 x) = (term171 x).
Proof. exact (MK_COMB (@lem1716401 x) (@lem1716402)). Qed.
Lemma lem1716404 (x : real) : (term171 x) = (term171 x).
Proof. exact (TRANS (@lem1716384 x) (@lem1716403 x)). Qed.
Lemma lem1716405 (x : real) : (term83 x) = (term274 x).
Proof. exact (@lem1483525 (term80 x) term50). Qed.
Lemma lem1716417 (x : real) : (term275 x) = (term276 x).
Proof. exact (@lem1483519 (term80 x) term50). Qed.
Lemma lem1716419 (x : nat) : (term87 x) = term50.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1716420 : term88 = term50.
Proof. exact (@lem1716419 term89). Qed.
Lemma lem1716421 (x : real) : (term277 x) = (term277 x).
Proof. exact (eq_refl (term277 x)). Qed.
Lemma lem1716422 (x : real) : (term276 x) = (term278 x).
Proof. exact (MK_COMB (@lem1716421 x) (@lem1716420)). Qed.
Lemma lem1716423 (x : real) : (term278 x) = (term80 x).
Proof. exact (@lem1483450 (term80 x)). Qed.
Lemma lem1716424 (x : real) : (term276 x) = (term80 x).
Proof. exact (TRANS (@lem1716422 x) (@lem1716423 x)). Qed.
Lemma lem1716426 (x : real) : (term275 x) = (term80 x).
Proof. exact (TRANS (@lem1716417 x) (@lem1716424 x)). Qed.
Lemma lem1716427 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1716428 (x : real) : (term279 x) = (term82 x).
Proof. exact (MK_COMB (@lem1716427) (@lem1716426 x)). Qed.
Lemma lem1716429 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716430 (x : real) : (term274 x) = (term83 x).
Proof. exact (MK_COMB (@lem1716428 x) (@lem1716429)). Qed.
Lemma lem1716431 (x : real) : (term83 x) = (term83 x).
Proof. exact (TRANS (@lem1716405 x) (@lem1716430 x)). Qed.
Lemma lem1716432 (x : real) : (term92 x) = (term84 x).
Proof. exact (@lem1483525 x term50). Qed.
Lemma lem1716438 (x : real) : (term85 x) = (term86 x).
Proof. exact (@lem1483519 x term50). Qed.
Lemma lem1716440 (x : nat) : (term87 x) = term50.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1716441 : term88 = term50.
Proof. exact (@lem1716440 term89). Qed.
Lemma lem1716442 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1716443 (x : real) : (term86 x) = (term90 x).
Proof. exact (MK_COMB (@lem1716442 x) (@lem1716441)). Qed.
Lemma lem1716444 (x : real) : (term90 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1716445 (x : real) : (term86 x) = x.
Proof. exact (TRANS (@lem1716443 x) (@lem1716444 x)). Qed.
Lemma lem1716447 (x : real) : (term85 x) = x.
Proof. exact (TRANS (@lem1716438 x) (@lem1716445 x)). Qed.
Lemma lem1716448 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1716449 (x : real) : (term91 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1716448) (@lem1716447 x)). Qed.
Lemma lem1716450 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716451 (x : real) : (term84 x) = (term92 x).
Proof. exact (MK_COMB (@lem1716449 x) (@lem1716450)). Qed.
Lemma lem1716452 (x : real) : (term92 x) = (term92 x).
Proof. exact (TRANS (@lem1716432 x) (@lem1716451 x)). Qed.
Lemma lem1716453 (x : real) : (term280 x) = (term281 x).
Proof. exact (@lem1483525 (term282 x) term50). Qed.
Lemma lem1716454 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716466 (x : real) : (term282 x) = (term283 x).
Proof. exact (@lem1483440 term47 x). Qed.
Lemma lem1716468 (m : nat) : (term284 m) = term50.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1716469 : term285 = term50.
Proof. exact (@lem1716468 term89). Qed.
Lemma lem1716470 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1716471 : term286 = term52.
Proof. exact (MK_COMB (@lem1716470) (@lem1716469)). Qed.
Lemma lem1716472 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1716473 (x : real) : (term283 x) = (term287 x).
Proof. exact (MK_COMB (@lem1716471) (@lem1716472 x)). Qed.
Lemma lem1716474 (x : real) : (term282 x) = (term287 x).
Proof. exact (TRANS (@lem1716466 x) (@lem1716473 x)). Qed.
Lemma lem1716475 (x : real) : (term287 x) = term50.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1716477 (x : real) : (term282 x) = term50.
Proof. exact (TRANS (@lem1716474 x) (@lem1716475 x)). Qed.
Lemma lem1716478 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1716479 (x : real) : (term288 x) = term174.
Proof. exact (MK_COMB (@lem1716478) (@lem1716477 x)). Qed.
Lemma lem1716480 (x : real) : (term289 x) = term290.
Proof. exact (MK_COMB (@lem1716479 x) (@lem1716454)). Qed.
Lemma lem1716481 : term290 = term291.
Proof. exact (@lem1483519 term50 term50). Qed.
Lemma lem1716483 (x : nat) : (term87 x) = term50.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1716484 : term88 = term50.
Proof. exact (@lem1716483 term89). Qed.
Lemma lem1716485 : term292 = term292.
Proof. exact (eq_refl term292). Qed.
Lemma lem1716486 : term291 = term293.
Proof. exact (MK_COMB (@lem1716485) (@lem1716484)). Qed.
Lemma lem1716487 : term293 = term50.
Proof. exact (@lem1483448 term50). Qed.
Lemma lem1716488 : term291 = term50.
Proof. exact (TRANS (@lem1716486) (@lem1716487)). Qed.
Lemma lem1716489 : term290 = term50.
Proof. exact (TRANS (@lem1716481) (@lem1716488)). Qed.
Lemma lem1716490 (x : real) : (term289 x) = term50.
Proof. exact (TRANS (@lem1716480 x) (@lem1716489)). Qed.
Lemma lem1716491 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1716492 (x : real) : (term294 x) = term295.
Proof. exact (MK_COMB (@lem1716491) (@lem1716490 x)). Qed.
Lemma lem1716493 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716494 (x : real) : (term281 x) = term296.
Proof. exact (MK_COMB (@lem1716492 x) (@lem1716493)). Qed.
Lemma lem1716495 (x : real) : (term280 x) = term296.
Proof. exact (TRANS (@lem1716453 x) (@lem1716494 x)). Qed.
Lemma lem1716496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716497 (x : real) : (term129 x) = (term129 x).
Proof. exact (MK_COMB (@lem1716496) (@lem1716452 x)). Qed.
Lemma lem1716498 (x : real) : (term297 x) = (term298 x).
Proof. exact (MK_COMB (@lem1716497 x) (@lem1716495 x)). Qed.
Lemma lem1716499 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716500 (x : real) : (term165 x) = (term165 x).
Proof. exact (MK_COMB (@lem1716499) (@lem1716431 x)). Qed.
Lemma lem1716501 (x : real) : (term267 x) = (term299 x).
Proof. exact (MK_COMB (@lem1716500 x) (@lem1716498 x)). Qed.
Lemma lem1716502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716503 (x : real) : (term189 x) = (term189 x).
Proof. exact (MK_COMB (@lem1716502) (@lem1716404 x)). Qed.
Lemma lem1716504 (x : real) : (term269 x) = (term300 x).
Proof. exact (MK_COMB (@lem1716503 x) (@lem1716501 x)). Qed.
Lemma lem1716505 (x : real) : (term301 x) = (term77 x).
Proof. exact (@lem1483525 term50 x). Qed.
Lemma lem1716511 (x : real) : (term78 x) = (term79 x).
Proof. exact (@lem1483519 term50 x). Qed.
Lemma lem1716516 (x : real) : (term79 x) = (term80 x).
Proof. exact (@lem1483448 (term80 x)). Qed.
Lemma lem1716518 (x : real) : (term78 x) = (term80 x).
Proof. exact (TRANS (@lem1716511 x) (@lem1716516 x)). Qed.
Lemma lem1716519 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1716520 (x : real) : (term81 x) = (term82 x).
Proof. exact (MK_COMB (@lem1716519) (@lem1716518 x)). Qed.
Lemma lem1716521 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716522 (x : real) : (term77 x) = (term83 x).
Proof. exact (MK_COMB (@lem1716520 x) (@lem1716521)). Qed.
Lemma lem1716523 (x : real) : (term301 x) = (term83 x).
Proof. exact (TRANS (@lem1716505 x) (@lem1716522 x)). Qed.
Lemma lem1716524 (x : real) : (term302 x) = (term303 x).
Proof. exact (@lem1483525 (term304 x) term50). Qed.
Lemma lem1716525 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716532 (x : real) : (real_neg x) = (term80 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1716541 (x : real) : (term277 x) = (term277 x).
Proof. exact (eq_refl (term277 x)). Qed.
Lemma lem1716542 (x : real) : (term304 x) = (term305 x).
Proof. exact (MK_COMB (@lem1716541 x) (@lem1716532 x)). Qed.
Lemma lem1716543 (x : real) : (term305 x) = (term306 x).
Proof. exact (@lem1483438 term47 term47 x). Qed.
Lemma lem1716544 : term307 = term308.
Proof. exact (@lem1367763 term89 term89). Qed.
Lemma lem1716545 : term309 = term310.
Proof. exact (@lem706885). Qed.
Lemma lem1716546 : (term309 = term310) = (term311 = term312).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term310). Qed.
Lemma lem1716547 : term311 = term312.
Proof. exact (EQ_MP (@lem1716546) (@lem1716545)). Qed.
Lemma lem1716548 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1716549 : term313 = term314.
Proof. exact (MK_COMB (@lem1716548) (@lem1716547)). Qed.
Lemma lem1716550 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1716551 : term308 = term315.
Proof. exact (MK_COMB (@lem1716550) (@lem1716549)). Qed.
Lemma lem1716552 : term307 = term315.
Proof. exact (TRANS (@lem1716544) (@lem1716551)). Qed.
Lemma lem1716553 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1716554 : term316 = term317.
Proof. exact (MK_COMB (@lem1716553) (@lem1716552)). Qed.
Lemma lem1716555 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1716556 (x : real) : (term306 x) = (term318 x).
Proof. exact (MK_COMB (@lem1716554) (@lem1716555 x)). Qed.
Lemma lem1716557 (x : real) : (term305 x) = (term318 x).
Proof. exact (TRANS (@lem1716543 x) (@lem1716556 x)). Qed.
Lemma lem1716558 (x : real) : (term304 x) = (term318 x).
Proof. exact (TRANS (@lem1716542 x) (@lem1716557 x)). Qed.
Lemma lem1716559 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1716560 (x : real) : (term319 x) = (term320 x).
Proof. exact (MK_COMB (@lem1716559) (@lem1716558 x)). Qed.
Lemma lem1716561 (x : real) : (term321 x) = (term322 x).
Proof. exact (MK_COMB (@lem1716560 x) (@lem1716525)). Qed.
Lemma lem1716562 (x : real) : (term322 x) = (term323 x).
Proof. exact (@lem1483519 (term318 x) term50). Qed.
Lemma lem1716564 (x : nat) : (term87 x) = term50.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1716565 : term88 = term50.
Proof. exact (@lem1716564 term89). Qed.
Lemma lem1716566 (x : real) : (term324 x) = (term324 x).
Proof. exact (eq_refl (term324 x)). Qed.
Lemma lem1716567 (x : real) : (term323 x) = (term325 x).
Proof. exact (MK_COMB (@lem1716566 x) (@lem1716565)). Qed.
Lemma lem1716568 (x : real) : (term325 x) = (term318 x).
Proof. exact (@lem1483450 (term318 x)). Qed.
Lemma lem1716569 (x : real) : (term323 x) = (term318 x).
Proof. exact (TRANS (@lem1716567 x) (@lem1716568 x)). Qed.
Lemma lem1716570 (x : real) : (term322 x) = (term318 x).
Proof. exact (TRANS (@lem1716562 x) (@lem1716569 x)). Qed.
Lemma lem1716571 (x : real) : (term321 x) = (term318 x).
Proof. exact (TRANS (@lem1716561 x) (@lem1716570 x)). Qed.
Lemma lem1716572 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1716573 (x : real) : (term326 x) = (term327 x).
Proof. exact (MK_COMB (@lem1716572) (@lem1716571 x)). Qed.
Lemma lem1716574 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716575 (x : real) : (term303 x) = (term328 x).
Proof. exact (MK_COMB (@lem1716573 x) (@lem1716574)). Qed.
Lemma lem1716576 (x : real) : (term302 x) = (term328 x).
Proof. exact (TRANS (@lem1716524 x) (@lem1716575 x)). Qed.
Lemma lem1716577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716578 (x : real) : (term129 x) = (term129 x).
Proof. exact (MK_COMB (@lem1716577) (@lem1716452 x)). Qed.
Lemma lem1716579 (x : real) : (term329 x) = (term330 x).
Proof. exact (MK_COMB (@lem1716578 x) (@lem1716576 x)). Qed.
Lemma lem1716580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716581 (x : real) : (term165 x) = (term165 x).
Proof. exact (MK_COMB (@lem1716580) (@lem1716431 x)). Qed.
Lemma lem1716582 (x : real) : (term262 x) = (term331 x).
Proof. exact (MK_COMB (@lem1716581 x) (@lem1716579 x)). Qed.
Lemma lem1716583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716584 (x : real) : (term263 x) = (term165 x).
Proof. exact (MK_COMB (@lem1716583) (@lem1716523 x)). Qed.
Lemma lem1716585 (x : real) : (term265 x) = (term332 x).
Proof. exact (MK_COMB (@lem1716584 x) (@lem1716582 x)). Qed.
Lemma lem1716586 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716587 (x : real) : (term271 x) = (term333 x).
Proof. exact (MK_COMB (@lem1716586) (@lem1716504 x)). Qed.
Lemma lem1716588 (x : real) : (term272 x) = (term334 x).
Proof. exact (MK_COMB (@lem1716587 x) (@lem1716585 x)). Qed.
Lemma lem1716600 (x : real) : (term258 x) = (term334 x).
Proof. exact (TRANS (@lem1716383 x) (@lem1716588 x)). Qed.
Lemma lem1716602 (a : real) (x : real) (r : real) : (term335 a x r) = (term336 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1716603 (x : real) : (term120 x) = (term337 x).
Proof. exact (@lem1716602 x x term50). Qed.
Lemma lem1716610 (x : real) : (term113 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1716613 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1716614 (x : real) : (term338 x) = (real_add x x).
Proof. exact (MK_COMB (@lem1716613 x) (@lem1716610 x)). Qed.
Lemma lem1716615 (x : real) : (real_add x x) = (term339 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1716616 : term340 = term313.
Proof. exact (@lem1367770 term89 term89). Qed.
Lemma lem1716617 : term309 = term310.
Proof. exact (@lem706885). Qed.
Lemma lem1716618 : (term309 = term310) = (term311 = term312).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term310). Qed.
Lemma lem1716619 : term311 = term312.
Proof. exact (EQ_MP (@lem1716618) (@lem1716617)). Qed.
Lemma lem1716620 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1716621 : term313 = term314.
Proof. exact (MK_COMB (@lem1716620) (@lem1716619)). Qed.
Lemma lem1716622 : term340 = term314.
Proof. exact (TRANS (@lem1716616) (@lem1716621)). Qed.
Lemma lem1716623 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1716624 : term341 = term342.
Proof. exact (MK_COMB (@lem1716623) (@lem1716622)). Qed.
Lemma lem1716625 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1716626 (x : real) : (term339 x) = (term343 x).
Proof. exact (MK_COMB (@lem1716624) (@lem1716625 x)). Qed.
Lemma lem1716627 (x : real) : (real_add x x) = (term343 x).
Proof. exact (TRANS (@lem1716615 x) (@lem1716626 x)). Qed.
Lemma lem1716628 (x : real) : (term338 x) = (term343 x).
Proof. exact (TRANS (@lem1716614 x) (@lem1716627 x)). Qed.
Lemma lem1716629 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1716630 (x : real) : (term344 x) = (term345 x).
Proof. exact (MK_COMB (@lem1716629) (@lem1716628 x)). Qed.
Lemma lem1716631 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716632 (x : real) : (term346 x) = (term347 x).
Proof. exact (MK_COMB (@lem1716630 x) (@lem1716631)). Qed.
Lemma lem1716644 (x : real) : (term348 x) = (term283 x).
Proof. exact (@lem1483442 term47 x). Qed.
Lemma lem1716646 (m : nat) : (term284 m) = term50.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1716647 : term285 = term50.
Proof. exact (@lem1716646 term89). Qed.
Lemma lem1716648 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1716649 : term286 = term52.
Proof. exact (MK_COMB (@lem1716648) (@lem1716647)). Qed.
Lemma lem1716650 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1716651 (x : real) : (term283 x) = (term287 x).
Proof. exact (MK_COMB (@lem1716649) (@lem1716650 x)). Qed.
Lemma lem1716652 (x : real) : (term348 x) = (term287 x).
Proof. exact (TRANS (@lem1716644 x) (@lem1716651 x)). Qed.
Lemma lem1716653 (x : real) : (term287 x) = term50.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1716655 (x : real) : (term348 x) = term50.
Proof. exact (TRANS (@lem1716652 x) (@lem1716653 x)). Qed.
Lemma lem1716656 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1716657 (x : real) : (term349 x) = term295.
Proof. exact (MK_COMB (@lem1716656) (@lem1716655 x)). Qed.
Lemma lem1716658 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716659 (x : real) : (term350 x) = term296.
Proof. exact (MK_COMB (@lem1716657 x) (@lem1716658)). Qed.
Lemma lem1716660 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716661 (x : real) : (term351 x) = term352.
Proof. exact (MK_COMB (@lem1716660) (@lem1716659 x)). Qed.
Lemma lem1716662 (x : real) : (term337 x) = (term353 x).
Proof. exact (MK_COMB (@lem1716661 x) (@lem1716632 x)). Qed.
Lemma lem1716663 (x : real) : (term120 x) = (term353 x).
Proof. exact (TRANS (@lem1716603 x) (@lem1716662 x)). Qed.
Lemma lem1716664 (x : real) : (term129 x) = (term129 x).
Proof. exact (eq_refl (term129 x)). Qed.
Lemma lem1716665 (x : real) : (term236 x) = (term354 x).
Proof. exact (MK_COMB (@lem1716664 x) (@lem1716663 x)). Qed.
Lemma lem1716666 (x : real) : (term165 x) = (term165 x).
Proof. exact (eq_refl (term165 x)). Qed.
Lemma lem1716669 (x : real) : (term355 x) = (term356 x).
Proof. exact (MK_COMB (@lem1716666 x) (@lem1716665 x)). Qed.
Lemma lem1716670 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716671 (x : real) : (term357 x) = (term358 x).
Proof. exact (MK_COMB (@lem1716670) (@lem1716600 x)). Qed.
Lemma lem1716672 (x : real) : (term249 x) = (term359 x).
Proof. exact (MK_COMB (@lem1716671 x) (@lem1716669 x)). Qed.
Lemma lem1716674 (a : real) (x : real) (r : real) : (term335 a x r) = (term336 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1716675 (x : real) : (term156 x) = (term360 x).
Proof. exact (@lem1716674 (term80 x) x term50). Qed.
Lemma lem1716682 (x : real) : (term113 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1716691 (x : real) : (term277 x) = (term277 x).
Proof. exact (eq_refl (term277 x)). Qed.
Lemma lem1716692 (x : real) : (term361 x) = (term282 x).
Proof. exact (MK_COMB (@lem1716691 x) (@lem1716682 x)). Qed.
Lemma lem1716693 (x : real) : (term282 x) = (term283 x).
Proof. exact (@lem1483440 term47 x). Qed.
Lemma lem1716695 (m : nat) : (term284 m) = term50.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1716696 : term285 = term50.
Proof. exact (@lem1716695 term89). Qed.
Lemma lem1716697 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1716698 : term286 = term52.
Proof. exact (MK_COMB (@lem1716697) (@lem1716696)). Qed.
Lemma lem1716699 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1716700 (x : real) : (term283 x) = (term287 x).
Proof. exact (MK_COMB (@lem1716698) (@lem1716699 x)). Qed.
Lemma lem1716701 (x : real) : (term282 x) = (term287 x).
Proof. exact (TRANS (@lem1716693 x) (@lem1716700 x)). Qed.
Lemma lem1716702 (x : real) : (term287 x) = term50.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1716703 (x : real) : (term282 x) = term50.
Proof. exact (TRANS (@lem1716701 x) (@lem1716702 x)). Qed.
Lemma lem1716704 (x : real) : (term361 x) = term50.
Proof. exact (TRANS (@lem1716692 x) (@lem1716703 x)). Qed.
Lemma lem1716705 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1716706 (x : real) : (term362 x) = term295.
Proof. exact (MK_COMB (@lem1716705) (@lem1716704 x)). Qed.
Lemma lem1716707 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716708 (x : real) : (term363 x) = term296.
Proof. exact (MK_COMB (@lem1716706 x) (@lem1716707)). Qed.
Lemma lem1716726 (x : real) : (term305 x) = (term306 x).
Proof. exact (@lem1483438 term47 term47 x). Qed.
Lemma lem1716727 : term307 = term308.
Proof. exact (@lem1367763 term89 term89). Qed.
Lemma lem1716728 : term309 = term310.
Proof. exact (@lem706885). Qed.
Lemma lem1716729 : (term309 = term310) = (term311 = term312).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term310). Qed.
Lemma lem1716730 : term311 = term312.
Proof. exact (EQ_MP (@lem1716729) (@lem1716728)). Qed.
Lemma lem1716731 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1716732 : term313 = term314.
Proof. exact (MK_COMB (@lem1716731) (@lem1716730)). Qed.
Lemma lem1716733 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1716734 : term308 = term315.
Proof. exact (MK_COMB (@lem1716733) (@lem1716732)). Qed.
Lemma lem1716735 : term307 = term315.
Proof. exact (TRANS (@lem1716727) (@lem1716734)). Qed.
Lemma lem1716736 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1716737 : term316 = term317.
Proof. exact (MK_COMB (@lem1716736) (@lem1716735)). Qed.
Lemma lem1716738 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1716739 (x : real) : (term306 x) = (term318 x).
Proof. exact (MK_COMB (@lem1716737) (@lem1716738 x)). Qed.
Lemma lem1716741 (x : real) : (term305 x) = (term318 x).
Proof. exact (TRANS (@lem1716726 x) (@lem1716739 x)). Qed.
Lemma lem1716742 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1716743 (x : real) : (term364 x) = (term327 x).
Proof. exact (MK_COMB (@lem1716742) (@lem1716741 x)). Qed.
Lemma lem1716744 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716745 (x : real) : (term365 x) = (term328 x).
Proof. exact (MK_COMB (@lem1716743 x) (@lem1716744)). Qed.
Lemma lem1716746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716747 (x : real) : (term366 x) = (term367 x).
Proof. exact (MK_COMB (@lem1716746) (@lem1716745 x)). Qed.
Lemma lem1716748 (x : real) : (term360 x) = (term368 x).
Proof. exact (MK_COMB (@lem1716747 x) (@lem1716708 x)). Qed.
Lemma lem1716749 (x : real) : (term156 x) = (term368 x).
Proof. exact (TRANS (@lem1716675 x) (@lem1716748 x)). Qed.
Lemma lem1716750 (x : real) : (term160 x) = (term160 x).
Proof. exact (eq_refl (term160 x)). Qed.
Lemma lem1716751 (x : real) : (term246 x) = (term369 x).
Proof. exact (MK_COMB (@lem1716750 x) (@lem1716749 x)). Qed.
Lemma lem1716752 (x : real) : (term165 x) = (term165 x).
Proof. exact (eq_refl (term165 x)). Qed.
Lemma lem1716755 (x : real) : (term370 x) = (term371 x).
Proof. exact (MK_COMB (@lem1716752 x) (@lem1716751 x)). Qed.
Lemma lem1716757 (x : real) : (term372 x) = (term373 x).
Proof. exact (eq_refl (term372 x)). Qed.
Lemma lem1716758 (x : real) : (term373 x) = (term372 x).
Proof. exact (SYM (@lem1716757 x)). Qed.
Lemma lem1716759 (x : real) : (term372 x) = (term374 x).
Proof. exact (@lem1482981 (term375 x) x). Qed.
Lemma lem1716760 (x : real) : (term373 x) = (term374 x).
Proof. exact (TRANS (@lem1716758 x) (@lem1716759 x)). Qed.
Lemma lem1716761 (x : real) : (term376 x) = (term377 x).
Proof. exact (eq_refl (term376 x)). Qed.
Lemma lem1716762 (x : real) : (term263 x) = (term263 x).
Proof. exact (eq_refl (term263 x)). Qed.
Lemma lem1716763 (x : real) : (term378 x) = (term379 x).
Proof. exact (MK_COMB (@lem1716762 x) (@lem1716761 x)). Qed.
Lemma lem1716764 (x : real) : (term380 x) = (term381 x).
Proof. exact (eq_refl (term380 x)). Qed.
Lemma lem1716765 (x : real) : (term189 x) = (term189 x).
Proof. exact (eq_refl (term189 x)). Qed.
Lemma lem1716766 (x : real) : (term382 x) = (term383 x).
Proof. exact (MK_COMB (@lem1716765 x) (@lem1716764 x)). Qed.
Lemma lem1716767 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716768 (x : real) : (term384 x) = (term385 x).
Proof. exact (MK_COMB (@lem1716767) (@lem1716766 x)). Qed.
Lemma lem1716769 (x : real) : (term374 x) = (term386 x).
Proof. exact (MK_COMB (@lem1716768 x) (@lem1716763 x)). Qed.
Lemma lem1716770 (x : real) : (term387 x) = (term387 x).
Proof. exact (eq_refl (term387 x)). Qed.
Lemma lem1716771 (x : real) : ((term373 x) = (term374 x)) = ((term373 x) = (term386 x)).
Proof. exact (MK_COMB (@lem1716770 x) (@lem1716769 x)). Qed.
Lemma lem1716772 (x : real) : (term373 x) = (term386 x).
Proof. exact (EQ_MP (@lem1716771 x) (@lem1716760 x)). Qed.
Lemma lem1716773 (x : real) : (term136 x) = (term388 x).
Proof. exact (@lem1483527 (term80 x) term50). Qed.
Lemma lem1716785 (x : real) : (term275 x) = (term276 x).
Proof. exact (@lem1483519 (term80 x) term50). Qed.
Lemma lem1716787 (x : nat) : (term87 x) = term50.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1716788 : term88 = term50.
Proof. exact (@lem1716787 term89). Qed.
Lemma lem1716789 (x : real) : (term277 x) = (term277 x).
Proof. exact (eq_refl (term277 x)). Qed.
Lemma lem1716790 (x : real) : (term276 x) = (term278 x).
Proof. exact (MK_COMB (@lem1716789 x) (@lem1716788)). Qed.
Lemma lem1716791 (x : real) : (term278 x) = (term80 x).
Proof. exact (@lem1483450 (term80 x)). Qed.
Lemma lem1716792 (x : real) : (term276 x) = (term80 x).
Proof. exact (TRANS (@lem1716790 x) (@lem1716791 x)). Qed.
Lemma lem1716794 (x : real) : (term275 x) = (term80 x).
Proof. exact (TRANS (@lem1716785 x) (@lem1716792 x)). Qed.
Lemma lem1716795 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1716796 (x : real) : (term389 x) = (term135 x).
Proof. exact (MK_COMB (@lem1716795) (@lem1716794 x)). Qed.
Lemma lem1716797 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716798 (x : real) : (term388 x) = (term136 x).
Proof. exact (MK_COMB (@lem1716796 x) (@lem1716797)). Qed.
Lemma lem1716799 (x : real) : (term136 x) = (term136 x).
Proof. exact (TRANS (@lem1716773 x) (@lem1716798 x)). Qed.
Lemma lem1716800 (x : real) : (term390 x) = (term391 x).
Proof. exact (@lem1483525 (real_add x x) term50). Qed.
Lemma lem1716801 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716807 (x : real) : (real_add x x) = (term339 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1716808 : term340 = term313.
Proof. exact (@lem1367770 term89 term89). Qed.
Lemma lem1716809 : term309 = term310.
Proof. exact (@lem706885). Qed.
Lemma lem1716810 : (term309 = term310) = (term311 = term312).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term310). Qed.
Lemma lem1716811 : term311 = term312.
Proof. exact (EQ_MP (@lem1716810) (@lem1716809)). Qed.
Lemma lem1716812 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1716813 : term313 = term314.
Proof. exact (MK_COMB (@lem1716812) (@lem1716811)). Qed.
Lemma lem1716814 : term340 = term314.
Proof. exact (TRANS (@lem1716808) (@lem1716813)). Qed.
Lemma lem1716815 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1716816 : term341 = term342.
Proof. exact (MK_COMB (@lem1716815) (@lem1716814)). Qed.
Lemma lem1716817 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1716818 (x : real) : (term339 x) = (term343 x).
Proof. exact (MK_COMB (@lem1716816) (@lem1716817 x)). Qed.
Lemma lem1716820 (x : real) : (real_add x x) = (term343 x).
Proof. exact (TRANS (@lem1716807 x) (@lem1716818 x)). Qed.
Lemma lem1716821 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1716822 (x : real) : (term392 x) = (term393 x).
Proof. exact (MK_COMB (@lem1716821) (@lem1716820 x)). Qed.
Lemma lem1716823 (x : real) : (term394 x) = (term395 x).
Proof. exact (MK_COMB (@lem1716822 x) (@lem1716801)). Qed.
Lemma lem1716824 (x : real) : (term395 x) = (term396 x).
Proof. exact (@lem1483519 (term343 x) term50). Qed.
Lemma lem1716826 (x : nat) : (term87 x) = term50.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1716827 : term88 = term50.
Proof. exact (@lem1716826 term89). Qed.
Lemma lem1716828 (x : real) : (term397 x) = (term397 x).
Proof. exact (eq_refl (term397 x)). Qed.
Lemma lem1716829 (x : real) : (term396 x) = (term398 x).
Proof. exact (MK_COMB (@lem1716828 x) (@lem1716827)). Qed.
Lemma lem1716830 (x : real) : (term398 x) = (term343 x).
Proof. exact (@lem1483450 (term343 x)). Qed.
Lemma lem1716831 (x : real) : (term396 x) = (term343 x).
Proof. exact (TRANS (@lem1716829 x) (@lem1716830 x)). Qed.
Lemma lem1716832 (x : real) : (term395 x) = (term343 x).
Proof. exact (TRANS (@lem1716824 x) (@lem1716831 x)). Qed.
Lemma lem1716833 (x : real) : (term394 x) = (term343 x).
Proof. exact (TRANS (@lem1716823 x) (@lem1716832 x)). Qed.
Lemma lem1716834 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1716835 (x : real) : (term399 x) = (term345 x).
Proof. exact (MK_COMB (@lem1716834) (@lem1716833 x)). Qed.
Lemma lem1716836 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716837 (x : real) : (term391 x) = (term347 x).
Proof. exact (MK_COMB (@lem1716835 x) (@lem1716836)). Qed.
Lemma lem1716838 (x : real) : (term390 x) = (term347 x).
Proof. exact (TRANS (@lem1716800 x) (@lem1716837 x)). Qed.
Lemma lem1716839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716840 (x : real) : (term160 x) = (term160 x).
Proof. exact (MK_COMB (@lem1716839) (@lem1716799 x)). Qed.
Lemma lem1716841 (x : real) : (term400 x) = (term401 x).
Proof. exact (MK_COMB (@lem1716840 x) (@lem1716838 x)). Qed.
Lemma lem1716842 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716843 (x : real) : (term165 x) = (term165 x).
Proof. exact (MK_COMB (@lem1716842) (@lem1716431 x)). Qed.
Lemma lem1716844 (x : real) : (term381 x) = (term402 x).
Proof. exact (MK_COMB (@lem1716843 x) (@lem1716841 x)). Qed.
Lemma lem1716845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716846 (x : real) : (term189 x) = (term189 x).
Proof. exact (MK_COMB (@lem1716845) (@lem1716404 x)). Qed.
Lemma lem1716847 (x : real) : (term383 x) = (term403 x).
Proof. exact (MK_COMB (@lem1716846 x) (@lem1716844 x)). Qed.
Lemma lem1716848 (x : real) : (term404 x) = (term405 x).
Proof. exact (@lem1483525 (term406 x) term50). Qed.
Lemma lem1716849 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716856 (x : real) : (real_neg x) = (term80 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1716859 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1716860 (x : real) : (term406 x) = (term348 x).
Proof. exact (MK_COMB (@lem1716859 x) (@lem1716856 x)). Qed.
Lemma lem1716861 (x : real) : (term348 x) = (term283 x).
Proof. exact (@lem1483442 term47 x). Qed.
Lemma lem1716863 (m : nat) : (term284 m) = term50.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1716864 : term285 = term50.
Proof. exact (@lem1716863 term89). Qed.
Lemma lem1716865 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1716866 : term286 = term52.
Proof. exact (MK_COMB (@lem1716865) (@lem1716864)). Qed.
Lemma lem1716867 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1716868 (x : real) : (term283 x) = (term287 x).
Proof. exact (MK_COMB (@lem1716866) (@lem1716867 x)). Qed.
Lemma lem1716869 (x : real) : (term348 x) = (term287 x).
Proof. exact (TRANS (@lem1716861 x) (@lem1716868 x)). Qed.
Lemma lem1716870 (x : real) : (term287 x) = term50.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1716871 (x : real) : (term348 x) = term50.
Proof. exact (TRANS (@lem1716869 x) (@lem1716870 x)). Qed.
Lemma lem1716872 (x : real) : (term406 x) = term50.
Proof. exact (TRANS (@lem1716860 x) (@lem1716871 x)). Qed.
Lemma lem1716873 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1716874 (x : real) : (term407 x) = term174.
Proof. exact (MK_COMB (@lem1716873) (@lem1716872 x)). Qed.
Lemma lem1716875 (x : real) : (term408 x) = term290.
Proof. exact (MK_COMB (@lem1716874 x) (@lem1716849)). Qed.
Lemma lem1716876 : term290 = term291.
Proof. exact (@lem1483519 term50 term50). Qed.
Lemma lem1716878 (x : nat) : (term87 x) = term50.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1716879 : term88 = term50.
Proof. exact (@lem1716878 term89). Qed.
Lemma lem1716880 : term292 = term292.
Proof. exact (eq_refl term292). Qed.
Lemma lem1716881 : term291 = term293.
Proof. exact (MK_COMB (@lem1716880) (@lem1716879)). Qed.
Lemma lem1716882 : term293 = term50.
Proof. exact (@lem1483448 term50). Qed.
Lemma lem1716883 : term291 = term50.
Proof. exact (TRANS (@lem1716881) (@lem1716882)). Qed.
Lemma lem1716884 : term290 = term50.
Proof. exact (TRANS (@lem1716876) (@lem1716883)). Qed.
Lemma lem1716885 (x : real) : (term408 x) = term50.
Proof. exact (TRANS (@lem1716875 x) (@lem1716884)). Qed.
Lemma lem1716886 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1716887 (x : real) : (term409 x) = term295.
Proof. exact (MK_COMB (@lem1716886) (@lem1716885 x)). Qed.
Lemma lem1716888 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1716889 (x : real) : (term405 x) = term296.
Proof. exact (MK_COMB (@lem1716887 x) (@lem1716888)). Qed.
Lemma lem1716890 (x : real) : (term404 x) = term296.
Proof. exact (TRANS (@lem1716848 x) (@lem1716889 x)). Qed.
Lemma lem1716891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716892 (x : real) : (term160 x) = (term160 x).
Proof. exact (MK_COMB (@lem1716891) (@lem1716799 x)). Qed.
Lemma lem1716893 (x : real) : (term410 x) = (term411 x).
Proof. exact (MK_COMB (@lem1716892 x) (@lem1716890 x)). Qed.
Lemma lem1716894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716895 (x : real) : (term165 x) = (term165 x).
Proof. exact (MK_COMB (@lem1716894) (@lem1716431 x)). Qed.
Lemma lem1716896 (x : real) : (term377 x) = (term412 x).
Proof. exact (MK_COMB (@lem1716895 x) (@lem1716893 x)). Qed.
Lemma lem1716897 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716898 (x : real) : (term263 x) = (term165 x).
Proof. exact (MK_COMB (@lem1716897) (@lem1716523 x)). Qed.
Lemma lem1716899 (x : real) : (term379 x) = (term413 x).
Proof. exact (MK_COMB (@lem1716898 x) (@lem1716896 x)). Qed.
Lemma lem1716900 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716901 (x : real) : (term385 x) = (term414 x).
Proof. exact (MK_COMB (@lem1716900) (@lem1716847 x)). Qed.
Lemma lem1716902 (x : real) : (term386 x) = (term415 x).
Proof. exact (MK_COMB (@lem1716901 x) (@lem1716899 x)). Qed.
Lemma lem1716914 (x : real) : (term373 x) = (term415 x).
Proof. exact (TRANS (@lem1716772 x) (@lem1716902 x)). Qed.
Lemma lem1716915 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716916 (x : real) : (term416 x) = (term417 x).
Proof. exact (MK_COMB (@lem1716915) (@lem1716755 x)). Qed.
Lemma lem1716917 (x : real) : (term245 x) = (term418 x).
Proof. exact (MK_COMB (@lem1716916 x) (@lem1716914 x)). Qed.
Lemma lem1716918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716919 (x : real) : (term251 x) = (term419 x).
Proof. exact (MK_COMB (@lem1716918) (@lem1716672 x)). Qed.
Lemma lem1716920 (x : real) : (term252 x) = (term420 x).
Proof. exact (MK_COMB (@lem1716919 x) (@lem1716917 x)). Qed.
Lemma lem1716922 (x : real) : (term421 x) = (term422 x).
Proof. exact (eq_refl (term421 x)). Qed.
Lemma lem1716923 (x : real) : (term422 x) = (term421 x).
Proof. exact (SYM (@lem1716922 x)). Qed.
Lemma lem1716924 (x : real) : (term421 x) = (term423 x).
Proof. exact (@lem1482981 (term424 x) x). Qed.
Lemma lem1716925 (x : real) : (term422 x) = (term423 x).
Proof. exact (TRANS (@lem1716923 x) (@lem1716924 x)). Qed.
Lemma lem1716926 (x : real) : (term425 x) = (term426 x).
Proof. exact (eq_refl (term425 x)). Qed.
Lemma lem1716927 (x : real) : (term263 x) = (term263 x).
Proof. exact (eq_refl (term263 x)). Qed.
Lemma lem1716928 (x : real) : (term427 x) = (term428 x).
Proof. exact (MK_COMB (@lem1716927 x) (@lem1716926 x)). Qed.
Lemma lem1716929 (x : real) : (term429 x) = (term430 x).
Proof. exact (eq_refl (term429 x)). Qed.
Lemma lem1716930 (x : real) : (term189 x) = (term189 x).
Proof. exact (eq_refl (term189 x)). Qed.
Lemma lem1716931 (x : real) : (term431 x) = (term432 x).
Proof. exact (MK_COMB (@lem1716930 x) (@lem1716929 x)). Qed.
Lemma lem1716932 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716933 (x : real) : (term433 x) = (term434 x).
Proof. exact (MK_COMB (@lem1716932) (@lem1716931 x)). Qed.
Lemma lem1716934 (x : real) : (term423 x) = (term435 x).
Proof. exact (MK_COMB (@lem1716933 x) (@lem1716928 x)). Qed.
Lemma lem1716935 (x : real) : (term436 x) = (term436 x).
Proof. exact (eq_refl (term436 x)). Qed.
Lemma lem1716936 (x : real) : ((term422 x) = (term423 x)) = ((term422 x) = (term435 x)).
Proof. exact (MK_COMB (@lem1716935 x) (@lem1716934 x)). Qed.
Lemma lem1716937 (x : real) : (term422 x) = (term435 x).
Proof. exact (EQ_MP (@lem1716936 x) (@lem1716925 x)). Qed.
Lemma lem1716938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716939 (x : real) : (term129 x) = (term129 x).
Proof. exact (MK_COMB (@lem1716938) (@lem1716452 x)). Qed.
Lemma lem1716940 (x : real) : (term297 x) = (term298 x).
Proof. exact (MK_COMB (@lem1716939 x) (@lem1716495 x)). Qed.
Lemma lem1716941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716942 (x : real) : (term189 x) = (term189 x).
Proof. exact (MK_COMB (@lem1716941) (@lem1716404 x)). Qed.
Lemma lem1716943 (x : real) : (term430 x) = (term437 x).
Proof. exact (MK_COMB (@lem1716942 x) (@lem1716940 x)). Qed.
Lemma lem1716944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716945 (x : real) : (term189 x) = (term189 x).
Proof. exact (MK_COMB (@lem1716944) (@lem1716404 x)). Qed.
Lemma lem1716946 (x : real) : (term432 x) = (term438 x).
Proof. exact (MK_COMB (@lem1716945 x) (@lem1716943 x)). Qed.
Lemma lem1716947 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716948 (x : real) : (term129 x) = (term129 x).
Proof. exact (MK_COMB (@lem1716947) (@lem1716452 x)). Qed.
Lemma lem1716949 (x : real) : (term329 x) = (term330 x).
Proof. exact (MK_COMB (@lem1716948 x) (@lem1716576 x)). Qed.
Lemma lem1716950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716951 (x : real) : (term189 x) = (term189 x).
Proof. exact (MK_COMB (@lem1716950) (@lem1716404 x)). Qed.
Lemma lem1716952 (x : real) : (term426 x) = (term439 x).
Proof. exact (MK_COMB (@lem1716951 x) (@lem1716949 x)). Qed.
Lemma lem1716953 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1716954 (x : real) : (term263 x) = (term165 x).
Proof. exact (MK_COMB (@lem1716953) (@lem1716523 x)). Qed.
Lemma lem1716955 (x : real) : (term428 x) = (term440 x).
Proof. exact (MK_COMB (@lem1716954 x) (@lem1716952 x)). Qed.
Lemma lem1716956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1716957 (x : real) : (term434 x) = (term441 x).
Proof. exact (MK_COMB (@lem1716956) (@lem1716946 x)). Qed.
Lemma lem1716958 (x : real) : (term435 x) = (term442 x).
Proof. exact (MK_COMB (@lem1716957 x) (@lem1716955 x)). Qed.
Lemma lem1716970 (x : real) : (term422 x) = (term442 x).
Proof. exact (TRANS (@lem1716937 x) (@lem1716958 x)). Qed.
Lemma lem1716972 (a : real) (x : real) (r : real) : (term335 a x r) = (term336 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1716973 (x : real) : (term120 x) = (term337 x).
Proof. exact (@lem1716972 x x term50). Qed.
Lemma lem1716980 (x : real) : (term113 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1716983 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1716984 (x : real) : (term338 x) = (real_add x x).
Proof. exact (MK_COMB (@lem1716983 x) (@lem1716980 x)). Qed.
Lemma lem1716985 (x : real) : (real_add x x) = (term339 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1716986 : term340 = term313.
Proof. exact (@lem1367770 term89 term89). Qed.
Lemma lem1716987 : term309 = term310.
Proof. exact (@lem706885). Qed.
Lemma lem1716988 : (term309 = term310) = (term311 = term312).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term310). Qed.
Lemma lem1716989 : term311 = term312.
Proof. exact (EQ_MP (@lem1716988) (@lem1716987)). Qed.
Lemma lem1716990 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1716991 : term313 = term314.
Proof. exact (MK_COMB (@lem1716990) (@lem1716989)). Qed.
Lemma lem1716992 : term340 = term314.
Proof. exact (TRANS (@lem1716986) (@lem1716991)). Qed.
Lemma lem1716993 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1716994 : term341 = term342.
Proof. exact (MK_COMB (@lem1716993) (@lem1716992)). Qed.
Lemma lem1716995 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1716996 (x : real) : (term339 x) = (term343 x).
Proof. exact (MK_COMB (@lem1716994) (@lem1716995 x)). Qed.
Lemma lem1716997 (x : real) : (real_add x x) = (term343 x).
Proof. exact (TRANS (@lem1716985 x) (@lem1716996 x)). Qed.
Lemma lem1716998 (x : real) : (term338 x) = (term343 x).
Proof. exact (TRANS (@lem1716984 x) (@lem1716997 x)). Qed.
Lemma lem1716999 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717000 (x : real) : (term344 x) = (term345 x).
Proof. exact (MK_COMB (@lem1716999) (@lem1716998 x)). Qed.
Lemma lem1717001 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1717002 (x : real) : (term346 x) = (term347 x).
Proof. exact (MK_COMB (@lem1717000 x) (@lem1717001)). Qed.
Lemma lem1717014 (x : real) : (term348 x) = (term283 x).
Proof. exact (@lem1483442 term47 x). Qed.
Lemma lem1717016 (m : nat) : (term284 m) = term50.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1717017 : term285 = term50.
Proof. exact (@lem1717016 term89). Qed.
Lemma lem1717018 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1717019 : term286 = term52.
Proof. exact (MK_COMB (@lem1717018) (@lem1717017)). Qed.
Lemma lem1717020 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1717021 (x : real) : (term283 x) = (term287 x).
Proof. exact (MK_COMB (@lem1717019) (@lem1717020 x)). Qed.
Lemma lem1717022 (x : real) : (term348 x) = (term287 x).
Proof. exact (TRANS (@lem1717014 x) (@lem1717021 x)). Qed.
Lemma lem1717023 (x : real) : (term287 x) = term50.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1717025 (x : real) : (term348 x) = term50.
Proof. exact (TRANS (@lem1717022 x) (@lem1717023 x)). Qed.
Lemma lem1717026 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717027 (x : real) : (term349 x) = term295.
Proof. exact (MK_COMB (@lem1717026) (@lem1717025 x)). Qed.
Lemma lem1717028 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1717029 (x : real) : (term350 x) = term296.
Proof. exact (MK_COMB (@lem1717027 x) (@lem1717028)). Qed.
Lemma lem1717030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1717031 (x : real) : (term351 x) = term352.
Proof. exact (MK_COMB (@lem1717030) (@lem1717029 x)). Qed.
Lemma lem1717032 (x : real) : (term337 x) = (term353 x).
Proof. exact (MK_COMB (@lem1717031 x) (@lem1717002 x)). Qed.
Lemma lem1717033 (x : real) : (term120 x) = (term353 x).
Proof. exact (TRANS (@lem1716973 x) (@lem1717032 x)). Qed.
Lemma lem1717034 (x : real) : (term129 x) = (term129 x).
Proof. exact (eq_refl (term129 x)). Qed.
Lemma lem1717035 (x : real) : (term236 x) = (term354 x).
Proof. exact (MK_COMB (@lem1717034 x) (@lem1717033 x)). Qed.
Lemma lem1717036 (x : real) : (term189 x) = (term189 x).
Proof. exact (eq_refl (term189 x)). Qed.
Lemma lem1717039 (x : real) : (term443 x) = (term444 x).
Proof. exact (MK_COMB (@lem1717036 x) (@lem1717035 x)). Qed.
Lemma lem1717040 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1717041 (x : real) : (term445 x) = (term446 x).
Proof. exact (MK_COMB (@lem1717040) (@lem1716970 x)). Qed.
Lemma lem1717042 (x : real) : (term234 x) = (term447 x).
Proof. exact (MK_COMB (@lem1717041 x) (@lem1717039 x)). Qed.
Lemma lem1717051 (x : real) : (term230 x) = (term230 x).
Proof. exact (eq_refl (term230 x)). Qed.
Lemma lem1717052 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1717053 (x : real) : (term238 x) = (term448 x).
Proof. exact (MK_COMB (@lem1717052) (@lem1717042 x)). Qed.
Lemma lem1717054 (x : real) : (term239 x) = (term449 x).
Proof. exact (MK_COMB (@lem1717053 x) (@lem1717051 x)). Qed.
Lemma lem1717055 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1717056 (x : real) : (term253 x) = (term450 x).
Proof. exact (MK_COMB (@lem1717055) (@lem1716920 x)). Qed.
Lemma lem1717057 (x : real) : (term254 x) = (term451 x).
Proof. exact (MK_COMB (@lem1717056 x) (@lem1717054 x)). Qed.
Lemma lem1717058 (x : real) (h1 : term451 x) : term451 x.
Proof. exact (h1). Qed.
Lemma lem1717059 (x : real) (h1 : term420 x) : term420 x.
Proof. exact (h1). Qed.
Lemma lem1717060 (x : real) (h1 : term359 x) : term359 x.
Proof. exact (h1). Qed.
Lemma lem1717061 (x : real) (h1 : term334 x) : term334 x.
Proof. exact (h1). Qed.
Lemma lem1717062 (x : real) (h1 : term300 x) : term300 x.
Proof. exact (h1). Qed.
Lemma lem1717063 (x : real) (h1 : term300 x) : term299 x.
Proof. exact (proj2 (@lem1717062 x h1)). Qed.
Lemma lem1717065 (x : real) (h1 : term300 x) : term298 x.
Proof. exact (proj2 (@lem1717063 x h1)). Qed.
Lemma lem1717067 (x : real) (h1 : term300 x) : term296.
Proof. exact (proj2 (@lem1717065 x h1)). Qed.
Lemma lem1717070 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717071 : term296 = term453.
Proof. exact (@lem1717070 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1717072 : term453 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1717073 : term296 = False.
Proof. exact (TRANS (@lem1717071) (@lem1717072)). Qed.
Lemma lem1717074 (x : real) (h1 : term300 x) : False.
Proof. exact (EQ_MP (@lem1717073) (@lem1717067 x h1)). Qed.
Lemma lem1717075 (x : real) (h1 : term332 x) : term332 x.
Proof. exact (h1). Qed.
Lemma lem1717076 (x : real) (h1 : term332 x) : term331 x.
Proof. exact (proj2 (@lem1717075 x h1)). Qed.
Lemma lem1717078 (x : real) (h1 : term332 x) : term330 x.
Proof. exact (proj2 (@lem1717076 x h1)). Qed.
Lemma lem1717080 (x : real) (h1 : term332 x) : term328 x.
Proof. exact (proj2 (@lem1717078 x h1)). Qed.
Lemma lem1717081 (x : real) (h1 : term332 x) : term92 x.
Proof. exact (proj1 (@lem1717078 x h1)). Qed.
Lemma lem1717083 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717084 : term454 = term455.
Proof. exact (@lem1717083 (NUMERAL 0) term312). Qed.
Lemma lem1717085 : term456 = term310.
Proof. exact (@lem912803). Qed.
Lemma lem1717086 (h1 : term456 = term310) : term455 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term310 h1). Qed.
Lemma lem1717087 : (term456 = term310) = (term455 = True).
Proof. exact (prop_ext (fun h1 : term456 = term310 => @lem1717086 h1) (fun h1 : term455 = True => @lem1717085)). Qed.
Lemma lem1717088 : term455 = True.
Proof. exact (EQ_MP (@lem1717087) (@lem1717085)). Qed.
Lemma lem1717089 : term454 = True.
Proof. exact (TRANS (@lem1717084) (@lem1717088)). Qed.
Lemma lem1717090 : True = term454.
Proof. exact (SYM (@lem1717089)). Qed.
Lemma lem1717091 : term454.
Proof. exact (EQ_MP (@lem1717090) (@lem0)). Qed.
Lemma lem1717092 (x : real) (h1 : term332 x) : term457 x.
Proof. exact (conj (@lem1717091) (@lem1717081 x h1)). Qed.
Lemma lem1717094 (x : real) (y : real) : term458 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1717095 (x : real) : term459 x.
Proof. exact (@lem1717094 term314 x). Qed.
Lemma lem1717102 (x : real) (h1 : term332 x) : term347 x.
Proof. exact (@lem1717095 x (@lem1717092 x h1)). Qed.
Lemma lem1717104 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717105 : term460 = term461.
Proof. exact (@lem1717104 (NUMERAL 0) term89). Qed.
Lemma lem1717106 : term462 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1717107 (h1 : term462 = (BIT1 0)) : term461 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1717108 : (term462 = (BIT1 0)) = (term461 = True).
Proof. exact (prop_ext (fun h1 : term462 = (BIT1 0) => @lem1717107 h1) (fun h1 : term461 = True => @lem1717106)). Qed.
Lemma lem1717109 : term461 = True.
Proof. exact (EQ_MP (@lem1717108) (@lem1717106)). Qed.
Lemma lem1717110 : term460 = True.
Proof. exact (TRANS (@lem1717105) (@lem1717109)). Qed.
Lemma lem1717111 : True = term460.
Proof. exact (SYM (@lem1717110)). Qed.
Lemma lem1717112 : term460.
Proof. exact (EQ_MP (@lem1717111) (@lem0)). Qed.
Lemma lem1717113 (x : real) (h1 : term332 x) : term463 x.
Proof. exact (conj (@lem1717112) (@lem1717080 x h1)). Qed.
Lemma lem1717115 (x : real) (y : real) : term458 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1717116 (x : real) : term464 x.
Proof. exact (@lem1717115 term24 (term318 x)). Qed.
Lemma lem1717117 (x : real) (h1 : term332 x) : term465 x.
Proof. exact (@lem1717116 x (@lem1717113 x h1)). Qed.
Lemma lem1717118 (x : real) : (term466 x) = (term318 x).
Proof. exact (@lem1483460 (term318 x)). Qed.
Lemma lem1717119 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717120 (x : real) : (term467 x) = (term327 x).
Proof. exact (MK_COMB (@lem1717119) (@lem1717118 x)). Qed.
Lemma lem1717121 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1717122 (x : real) : (term465 x) = (term328 x).
Proof. exact (MK_COMB (@lem1717120 x) (@lem1717121)). Qed.
Lemma lem1717123 (x : real) (h1 : term332 x) : term328 x.
Proof. exact (EQ_MP (@lem1717122 x) (@lem1717117 x h1)). Qed.
Lemma lem1717124 (x : real) (h1 : term332 x) : term468 x.
Proof. exact (conj (@lem1717123 x h1) (@lem1717102 x h1)). Qed.
Lemma lem1717126 (x : real) (y : real) : term469 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1717127 (x : real) : term470 x.
Proof. exact (@lem1717126 (term318 x) (term343 x)). Qed.
Lemma lem1717128 (x : real) (h1 : term332 x) : term471 x.
Proof. exact (@lem1717127 x (@lem1717124 x h1)). Qed.
Lemma lem1717129 (x : real) : (term472 x) = (term473 x).
Proof. exact (@lem1483438 term315 term314 x). Qed.
Lemma lem1717131 (m : nat) : (term284 m) = term50.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1717132 : term474 = term50.
Proof. exact (@lem1717131 term312). Qed.
Lemma lem1717133 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1717134 : term475 = term52.
Proof. exact (MK_COMB (@lem1717133) (@lem1717132)). Qed.
Lemma lem1717135 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1717136 (x : real) : (term473 x) = (term287 x).
Proof. exact (MK_COMB (@lem1717134) (@lem1717135 x)). Qed.
Lemma lem1717137 (x : real) : (term472 x) = (term287 x).
Proof. exact (TRANS (@lem1717129 x) (@lem1717136 x)). Qed.
Lemma lem1717138 (x : real) : (term287 x) = term50.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1717139 (x : real) : (term472 x) = term50.
Proof. exact (TRANS (@lem1717137 x) (@lem1717138 x)). Qed.
Lemma lem1717140 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717141 (x : real) : (term476 x) = term295.
Proof. exact (MK_COMB (@lem1717140) (@lem1717139 x)). Qed.
Lemma lem1717142 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1717143 (x : real) : (term471 x) = term296.
Proof. exact (MK_COMB (@lem1717141 x) (@lem1717142)). Qed.
Lemma lem1717144 (x : real) (h1 : term332 x) : term296.
Proof. exact (EQ_MP (@lem1717143 x) (@lem1717128 x h1)). Qed.
Lemma lem1717146 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717147 : term296 = term453.
Proof. exact (@lem1717146 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1717148 : term453 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1717149 : term296 = False.
Proof. exact (TRANS (@lem1717147) (@lem1717148)). Qed.
Lemma lem1717150 (x : real) (h1 : term332 x) : False.
Proof. exact (EQ_MP (@lem1717149) (@lem1717144 x h1)). Qed.
Lemma lem1717151 (x : real) (h1 : term334 x) : False.
Proof. exact (or_elim (@lem1717061 x h1) (fun h0 : term300 x => @lem1717074 x h0) (fun h0 : term332 x => @lem1717150 x h0)). Qed.
Lemma lem1717152 (x : real) (h1 : term356 x) : term356 x.
Proof. exact (h1). Qed.
Lemma lem1717153 (x : real) (h1 : term356 x) : term354 x.
Proof. exact (proj2 (@lem1717152 x h1)). Qed.
Lemma lem1717155 (x : real) (h1 : term356 x) : term353 x.
Proof. exact (proj2 (@lem1717153 x h1)). Qed.
Lemma lem1717158 (x : real) (h1 : term356 x) : term296.
Proof. exact (proj1 (@lem1717155 x h1)). Qed.
Lemma lem1717160 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717161 : term296 = term453.
Proof. exact (@lem1717160 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1717162 : term453 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1717163 : term296 = False.
Proof. exact (TRANS (@lem1717161) (@lem1717162)). Qed.
Lemma lem1717164 (x : real) (h1 : term356 x) : False.
Proof. exact (EQ_MP (@lem1717163) (@lem1717158 x h1)). Qed.
Lemma lem1717165 (x : real) (h1 : term359 x) : False.
Proof. exact (or_elim (@lem1717060 x h1) (fun h0 : term334 x => @lem1717151 x h0) (fun h0 : term356 x => @lem1717164 x h0)). Qed.
Lemma lem1717166 (x : real) (h1 : term418 x) : term418 x.
Proof. exact (h1). Qed.
Lemma lem1717167 (x : real) (h1 : term371 x) : term371 x.
Proof. exact (h1). Qed.
Lemma lem1717168 (x : real) (h1 : term371 x) : term369 x.
Proof. exact (proj2 (@lem1717167 x h1)). Qed.
Lemma lem1717170 (x : real) (h1 : term371 x) : term368 x.
Proof. exact (proj2 (@lem1717168 x h1)). Qed.
Lemma lem1717172 (x : real) (h1 : term371 x) : term296.
Proof. exact (proj2 (@lem1717170 x h1)). Qed.
Lemma lem1717175 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717176 : term296 = term453.
Proof. exact (@lem1717175 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1717177 : term453 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1717178 : term296 = False.
Proof. exact (TRANS (@lem1717176) (@lem1717177)). Qed.
Lemma lem1717179 (x : real) (h1 : term371 x) : False.
Proof. exact (EQ_MP (@lem1717178) (@lem1717172 x h1)). Qed.
Lemma lem1717180 (x : real) (h1 : term415 x) : term415 x.
Proof. exact (h1). Qed.
Lemma lem1717181 (x : real) (h1 : term403 x) : term403 x.
Proof. exact (h1). Qed.
Lemma lem1717182 (x : real) (h1 : term403 x) : term402 x.
Proof. exact (proj2 (@lem1717181 x h1)). Qed.
Lemma lem1717183 (x : real) (h1 : term403 x) : term171 x.
Proof. exact (proj1 (@lem1717181 x h1)). Qed.
Lemma lem1717185 (x : real) (h1 : term403 x) : term83 x.
Proof. exact (proj1 (@lem1717182 x h1)). Qed.
Lemma lem1717189 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717190 : term460 = term461.
Proof. exact (@lem1717189 (NUMERAL 0) term89). Qed.
Lemma lem1717191 : term462 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1717192 (h1 : term462 = (BIT1 0)) : term461 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1717193 : (term462 = (BIT1 0)) = (term461 = True).
Proof. exact (prop_ext (fun h1 : term462 = (BIT1 0) => @lem1717192 h1) (fun h1 : term461 = True => @lem1717191)). Qed.
Lemma lem1717194 : term461 = True.
Proof. exact (EQ_MP (@lem1717193) (@lem1717191)). Qed.
Lemma lem1717195 : term460 = True.
Proof. exact (TRANS (@lem1717190) (@lem1717194)). Qed.
Lemma lem1717196 : True = term460.
Proof. exact (SYM (@lem1717195)). Qed.
Lemma lem1717197 : term460.
Proof. exact (EQ_MP (@lem1717196) (@lem0)). Qed.
Lemma lem1717198 (x : real) (h1 : term403 x) : term477 x.
Proof. exact (conj (@lem1717197) (@lem1717183 x h1)). Qed.
Lemma lem1717200 (x : real) (y : real) : term478 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1717201 (x : real) : term479 x.
Proof. exact (@lem1717200 term24 x). Qed.
Lemma lem1717202 (x : real) (h1 : term403 x) : term480 x.
Proof. exact (@lem1717201 x (@lem1717198 x h1)). Qed.
Lemma lem1717203 (x : real) : (term113 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1717204 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1717205 (x : real) : (term481 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1717204) (@lem1717203 x)). Qed.
Lemma lem1717206 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1717207 (x : real) : (term480 x) = (term171 x).
Proof. exact (MK_COMB (@lem1717205 x) (@lem1717206)). Qed.
Lemma lem1717208 (x : real) (h1 : term403 x) : term171 x.
Proof. exact (EQ_MP (@lem1717207 x) (@lem1717202 x h1)). Qed.
Lemma lem1717210 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717211 : term460 = term461.
Proof. exact (@lem1717210 (NUMERAL 0) term89). Qed.
Lemma lem1717212 : term462 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1717213 (h1 : term462 = (BIT1 0)) : term461 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1717214 : (term462 = (BIT1 0)) = (term461 = True).
Proof. exact (prop_ext (fun h1 : term462 = (BIT1 0) => @lem1717213 h1) (fun h1 : term461 = True => @lem1717212)). Qed.
Lemma lem1717215 : term461 = True.
Proof. exact (EQ_MP (@lem1717214) (@lem1717212)). Qed.
Lemma lem1717216 : term460 = True.
Proof. exact (TRANS (@lem1717211) (@lem1717215)). Qed.
Lemma lem1717217 : True = term460.
Proof. exact (SYM (@lem1717216)). Qed.
Lemma lem1717218 : term460.
Proof. exact (EQ_MP (@lem1717217) (@lem0)). Qed.
Lemma lem1717219 (x : real) (h1 : term403 x) : term482 x.
Proof. exact (conj (@lem1717218) (@lem1717185 x h1)). Qed.
Lemma lem1717221 (x : real) (y : real) : term458 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1717222 (x : real) : term483 x.
Proof. exact (@lem1717221 term24 (term80 x)). Qed.
Lemma lem1717223 (x : real) (h1 : term403 x) : term484 x.
Proof. exact (@lem1717222 x (@lem1717219 x h1)). Qed.
Lemma lem1717224 (x : real) : (term485 x) = (term80 x).
Proof. exact (@lem1483460 (term80 x)). Qed.
Lemma lem1717225 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717226 (x : real) : (term486 x) = (term82 x).
Proof. exact (MK_COMB (@lem1717225) (@lem1717224 x)). Qed.
Lemma lem1717227 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1717228 (x : real) : (term484 x) = (term83 x).
Proof. exact (MK_COMB (@lem1717226 x) (@lem1717227)). Qed.
Lemma lem1717229 (x : real) (h1 : term403 x) : term83 x.
Proof. exact (EQ_MP (@lem1717228 x) (@lem1717223 x h1)). Qed.
Lemma lem1717230 (x : real) (h1 : term403 x) : term487 x.
Proof. exact (conj (@lem1717229 x h1) (@lem1717208 x h1)). Qed.
Lemma lem1717232 (x : real) (y : real) : term488 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1717233 (x : real) : term489 x.
Proof. exact (@lem1717232 (term80 x) x). Qed.
Lemma lem1717234 (x : real) (h1 : term403 x) : term280 x.
Proof. exact (@lem1717233 x (@lem1717230 x h1)). Qed.
Lemma lem1717235 (x : real) : (term282 x) = (term283 x).
Proof. exact (@lem1483440 term47 x). Qed.
Lemma lem1717237 (m : nat) : (term284 m) = term50.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1717238 : term285 = term50.
Proof. exact (@lem1717237 term89). Qed.
Lemma lem1717239 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1717240 : term286 = term52.
Proof. exact (MK_COMB (@lem1717239) (@lem1717238)). Qed.
Lemma lem1717241 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1717242 (x : real) : (term283 x) = (term287 x).
Proof. exact (MK_COMB (@lem1717240) (@lem1717241 x)). Qed.
Lemma lem1717243 (x : real) : (term282 x) = (term287 x).
Proof. exact (TRANS (@lem1717235 x) (@lem1717242 x)). Qed.
Lemma lem1717244 (x : real) : (term287 x) = term50.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1717245 (x : real) : (term282 x) = term50.
Proof. exact (TRANS (@lem1717243 x) (@lem1717244 x)). Qed.
Lemma lem1717246 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717247 (x : real) : (term490 x) = term295.
Proof. exact (MK_COMB (@lem1717246) (@lem1717245 x)). Qed.
Lemma lem1717248 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1717249 (x : real) : (term280 x) = term296.
Proof. exact (MK_COMB (@lem1717247 x) (@lem1717248)). Qed.
Lemma lem1717250 (x : real) (h1 : term403 x) : term296.
Proof. exact (EQ_MP (@lem1717249 x) (@lem1717234 x h1)). Qed.
Lemma lem1717252 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717253 : term296 = term453.
Proof. exact (@lem1717252 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1717254 : term453 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1717255 : term296 = False.
Proof. exact (TRANS (@lem1717253) (@lem1717254)). Qed.
Lemma lem1717256 (x : real) (h1 : term403 x) : False.
Proof. exact (EQ_MP (@lem1717255) (@lem1717250 x h1)). Qed.
Lemma lem1717257 (x : real) (h1 : term413 x) : term413 x.
Proof. exact (h1). Qed.
Lemma lem1717258 (x : real) (h1 : term413 x) : term412 x.
Proof. exact (proj2 (@lem1717257 x h1)). Qed.
Lemma lem1717260 (x : real) (h1 : term413 x) : term411 x.
Proof. exact (proj2 (@lem1717258 x h1)). Qed.
Lemma lem1717262 (x : real) (h1 : term413 x) : term296.
Proof. exact (proj2 (@lem1717260 x h1)). Qed.
Lemma lem1717265 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717266 : term296 = term453.
Proof. exact (@lem1717265 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1717267 : term453 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1717268 : term296 = False.
Proof. exact (TRANS (@lem1717266) (@lem1717267)). Qed.
Lemma lem1717269 (x : real) (h1 : term413 x) : False.
Proof. exact (EQ_MP (@lem1717268) (@lem1717262 x h1)). Qed.
Lemma lem1717270 (x : real) (h1 : term415 x) : False.
Proof. exact (or_elim (@lem1717180 x h1) (fun h0 : term403 x => @lem1717256 x h0) (fun h0 : term413 x => @lem1717269 x h0)). Qed.
Lemma lem1717271 (x : real) (h1 : term418 x) : False.
Proof. exact (or_elim (@lem1717166 x h1) (fun h0 : term371 x => @lem1717179 x h0) (fun h0 : term415 x => @lem1717270 x h0)). Qed.
Lemma lem1717272 (x : real) (h1 : term420 x) : False.
Proof. exact (or_elim (@lem1717059 x h1) (fun h0 : term359 x => @lem1717165 x h0) (fun h0 : term418 x => @lem1717271 x h0)). Qed.
Lemma lem1717273 (x : real) (h1 : term449 x) : term449 x.
Proof. exact (h1). Qed.
Lemma lem1717274 (x : real) (h1 : term447 x) : term447 x.
Proof. exact (h1). Qed.
Lemma lem1717275 (x : real) (h1 : term442 x) : term442 x.
Proof. exact (h1). Qed.
Lemma lem1717276 (x : real) (h1 : term438 x) : term438 x.
Proof. exact (h1). Qed.
Lemma lem1717277 (x : real) (h1 : term438 x) : term437 x.
Proof. exact (proj2 (@lem1717276 x h1)). Qed.
Lemma lem1717279 (x : real) (h1 : term438 x) : term298 x.
Proof. exact (proj2 (@lem1717277 x h1)). Qed.
Lemma lem1717281 (x : real) (h1 : term438 x) : term296.
Proof. exact (proj2 (@lem1717279 x h1)). Qed.
Lemma lem1717284 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717285 : term296 = term453.
Proof. exact (@lem1717284 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1717286 : term453 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1717287 : term296 = False.
Proof. exact (TRANS (@lem1717285) (@lem1717286)). Qed.
Lemma lem1717288 (x : real) (h1 : term438 x) : False.
Proof. exact (EQ_MP (@lem1717287) (@lem1717281 x h1)). Qed.
Lemma lem1717289 (x : real) (h1 : term440 x) : term440 x.
Proof. exact (h1). Qed.
Lemma lem1717290 (x : real) (h1 : term440 x) : term439 x.
Proof. exact (proj2 (@lem1717289 x h1)). Qed.
Lemma lem1717292 (x : real) (h1 : term440 x) : term330 x.
Proof. exact (proj2 (@lem1717290 x h1)). Qed.
Lemma lem1717293 (x : real) (h1 : term440 x) : term171 x.
Proof. exact (proj1 (@lem1717290 x h1)). Qed.
Lemma lem1717294 (x : real) (h1 : term440 x) : term328 x.
Proof. exact (proj2 (@lem1717292 x h1)). Qed.
Lemma lem1717297 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717298 : term454 = term455.
Proof. exact (@lem1717297 (NUMERAL 0) term312). Qed.
Lemma lem1717299 : term456 = term310.
Proof. exact (@lem912803). Qed.
Lemma lem1717300 (h1 : term456 = term310) : term455 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term310 h1). Qed.
Lemma lem1717301 : (term456 = term310) = (term455 = True).
Proof. exact (prop_ext (fun h1 : term456 = term310 => @lem1717300 h1) (fun h1 : term455 = True => @lem1717299)). Qed.
Lemma lem1717302 : term455 = True.
Proof. exact (EQ_MP (@lem1717301) (@lem1717299)). Qed.
Lemma lem1717303 : term454 = True.
Proof. exact (TRANS (@lem1717298) (@lem1717302)). Qed.
Lemma lem1717304 : True = term454.
Proof. exact (SYM (@lem1717303)). Qed.
Lemma lem1717305 : term454.
Proof. exact (EQ_MP (@lem1717304) (@lem0)). Qed.
Lemma lem1717306 (x : real) (h1 : term440 x) : term491 x.
Proof. exact (conj (@lem1717305) (@lem1717293 x h1)). Qed.
Lemma lem1717308 (x : real) (y : real) : term478 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1717309 (x : real) : term492 x.
Proof. exact (@lem1717308 term314 x). Qed.
Lemma lem1717316 (x : real) (h1 : term440 x) : term493 x.
Proof. exact (@lem1717309 x (@lem1717306 x h1)). Qed.
Lemma lem1717318 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717319 : term460 = term461.
Proof. exact (@lem1717318 (NUMERAL 0) term89). Qed.
Lemma lem1717320 : term462 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1717321 (h1 : term462 = (BIT1 0)) : term461 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1717322 : (term462 = (BIT1 0)) = (term461 = True).
Proof. exact (prop_ext (fun h1 : term462 = (BIT1 0) => @lem1717321 h1) (fun h1 : term461 = True => @lem1717320)). Qed.
Lemma lem1717323 : term461 = True.
Proof. exact (EQ_MP (@lem1717322) (@lem1717320)). Qed.
Lemma lem1717324 : term460 = True.
Proof. exact (TRANS (@lem1717319) (@lem1717323)). Qed.
Lemma lem1717325 : True = term460.
Proof. exact (SYM (@lem1717324)). Qed.
Lemma lem1717326 : term460.
Proof. exact (EQ_MP (@lem1717325) (@lem0)). Qed.
Lemma lem1717327 (x : real) (h1 : term440 x) : term463 x.
Proof. exact (conj (@lem1717326) (@lem1717294 x h1)). Qed.
Lemma lem1717329 (x : real) (y : real) : term458 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1717330 (x : real) : term464 x.
Proof. exact (@lem1717329 term24 (term318 x)). Qed.
Lemma lem1717331 (x : real) (h1 : term440 x) : term465 x.
Proof. exact (@lem1717330 x (@lem1717327 x h1)). Qed.
Lemma lem1717332 (x : real) : (term466 x) = (term318 x).
Proof. exact (@lem1483460 (term318 x)). Qed.
Lemma lem1717333 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717334 (x : real) : (term467 x) = (term327 x).
Proof. exact (MK_COMB (@lem1717333) (@lem1717332 x)). Qed.
Lemma lem1717335 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1717336 (x : real) : (term465 x) = (term328 x).
Proof. exact (MK_COMB (@lem1717334 x) (@lem1717335)). Qed.
Lemma lem1717337 (x : real) (h1 : term440 x) : term328 x.
Proof. exact (EQ_MP (@lem1717336 x) (@lem1717331 x h1)). Qed.
Lemma lem1717338 (x : real) (h1 : term440 x) : term494 x.
Proof. exact (conj (@lem1717337 x h1) (@lem1717316 x h1)). Qed.
Lemma lem1717340 (x : real) (y : real) : term488 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1717341 (x : real) : term495 x.
Proof. exact (@lem1717340 (term318 x) (term343 x)). Qed.
Lemma lem1717342 (x : real) (h1 : term440 x) : term471 x.
Proof. exact (@lem1717341 x (@lem1717338 x h1)). Qed.
Lemma lem1717343 (x : real) : (term472 x) = (term473 x).
Proof. exact (@lem1483438 term315 term314 x). Qed.
Lemma lem1717345 (m : nat) : (term284 m) = term50.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1717346 : term474 = term50.
Proof. exact (@lem1717345 term312). Qed.
Lemma lem1717347 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1717348 : term475 = term52.
Proof. exact (MK_COMB (@lem1717347) (@lem1717346)). Qed.
Lemma lem1717349 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1717350 (x : real) : (term473 x) = (term287 x).
Proof. exact (MK_COMB (@lem1717348) (@lem1717349 x)). Qed.
Lemma lem1717351 (x : real) : (term472 x) = (term287 x).
Proof. exact (TRANS (@lem1717343 x) (@lem1717350 x)). Qed.
Lemma lem1717352 (x : real) : (term287 x) = term50.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1717353 (x : real) : (term472 x) = term50.
Proof. exact (TRANS (@lem1717351 x) (@lem1717352 x)). Qed.
Lemma lem1717354 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717355 (x : real) : (term476 x) = term295.
Proof. exact (MK_COMB (@lem1717354) (@lem1717353 x)). Qed.
Lemma lem1717356 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1717357 (x : real) : (term471 x) = term296.
Proof. exact (MK_COMB (@lem1717355 x) (@lem1717356)). Qed.
Lemma lem1717358 (x : real) (h1 : term440 x) : term296.
Proof. exact (EQ_MP (@lem1717357 x) (@lem1717342 x h1)). Qed.
Lemma lem1717360 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717361 : term296 = term453.
Proof. exact (@lem1717360 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1717362 : term453 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1717363 : term296 = False.
Proof. exact (TRANS (@lem1717361) (@lem1717362)). Qed.
Lemma lem1717364 (x : real) (h1 : term440 x) : False.
Proof. exact (EQ_MP (@lem1717363) (@lem1717358 x h1)). Qed.
Lemma lem1717365 (x : real) (h1 : term442 x) : False.
Proof. exact (or_elim (@lem1717275 x h1) (fun h0 : term438 x => @lem1717288 x h0) (fun h0 : term440 x => @lem1717364 x h0)). Qed.
Lemma lem1717366 (x : real) (h1 : term444 x) : term444 x.
Proof. exact (h1). Qed.
Lemma lem1717367 (x : real) (h1 : term444 x) : term354 x.
Proof. exact (proj2 (@lem1717366 x h1)). Qed.
Lemma lem1717369 (x : real) (h1 : term444 x) : term353 x.
Proof. exact (proj2 (@lem1717367 x h1)). Qed.
Lemma lem1717372 (x : real) (h1 : term444 x) : term296.
Proof. exact (proj1 (@lem1717369 x h1)). Qed.
Lemma lem1717374 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717375 : term296 = term453.
Proof. exact (@lem1717374 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1717376 : term453 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1717377 : term296 = False.
Proof. exact (TRANS (@lem1717375) (@lem1717376)). Qed.
Lemma lem1717378 (x : real) (h1 : term444 x) : False.
Proof. exact (EQ_MP (@lem1717377) (@lem1717372 x h1)). Qed.
Lemma lem1717379 (x : real) (h1 : term447 x) : False.
Proof. exact (or_elim (@lem1717274 x h1) (fun h0 : term442 x => @lem1717365 x h0) (fun h0 : term444 x => @lem1717378 x h0)). Qed.
Lemma lem1717380 (x : real) (h1 : term230 x) : term230 x.
Proof. exact (h1). Qed.
Lemma lem1717381 (x : real) (h1 : term496 x) : term496 x.
Proof. exact (h1). Qed.
Lemma lem1717382 (x : real) (h1 : term496 x) : term231 x.
Proof. exact (proj2 (@lem1717381 x h1)). Qed.
Lemma lem1717383 (x : real) (h1 : term496 x) : term171 x.
Proof. exact (proj1 (@lem1717381 x h1)). Qed.
Lemma lem1717384 (x : real) (h1 : term496 x) : term83 x.
Proof. exact (proj2 (@lem1717382 x h1)). Qed.
Lemma lem1717387 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717388 : term460 = term461.
Proof. exact (@lem1717387 (NUMERAL 0) term89). Qed.
Lemma lem1717389 : term462 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1717390 (h1 : term462 = (BIT1 0)) : term461 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1717391 : (term462 = (BIT1 0)) = (term461 = True).
Proof. exact (prop_ext (fun h1 : term462 = (BIT1 0) => @lem1717390 h1) (fun h1 : term461 = True => @lem1717389)). Qed.
Lemma lem1717392 : term461 = True.
Proof. exact (EQ_MP (@lem1717391) (@lem1717389)). Qed.
Lemma lem1717393 : term460 = True.
Proof. exact (TRANS (@lem1717388) (@lem1717392)). Qed.
Lemma lem1717394 : True = term460.
Proof. exact (SYM (@lem1717393)). Qed.
Lemma lem1717395 : term460.
Proof. exact (EQ_MP (@lem1717394) (@lem0)). Qed.
Lemma lem1717396 (x : real) (h1 : term496 x) : term477 x.
Proof. exact (conj (@lem1717395) (@lem1717383 x h1)). Qed.
Lemma lem1717398 (x : real) (y : real) : term478 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1717399 (x : real) : term479 x.
Proof. exact (@lem1717398 term24 x). Qed.
Lemma lem1717400 (x : real) (h1 : term496 x) : term480 x.
Proof. exact (@lem1717399 x (@lem1717396 x h1)). Qed.
Lemma lem1717401 (x : real) : (term113 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1717402 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1717403 (x : real) : (term481 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1717402) (@lem1717401 x)). Qed.
Lemma lem1717404 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1717405 (x : real) : (term480 x) = (term171 x).
Proof. exact (MK_COMB (@lem1717403 x) (@lem1717404)). Qed.
Lemma lem1717406 (x : real) (h1 : term496 x) : term171 x.
Proof. exact (EQ_MP (@lem1717405 x) (@lem1717400 x h1)). Qed.
Lemma lem1717408 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717409 : term460 = term461.
Proof. exact (@lem1717408 (NUMERAL 0) term89). Qed.
Lemma lem1717410 : term462 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1717411 (h1 : term462 = (BIT1 0)) : term461 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1717412 : (term462 = (BIT1 0)) = (term461 = True).
Proof. exact (prop_ext (fun h1 : term462 = (BIT1 0) => @lem1717411 h1) (fun h1 : term461 = True => @lem1717410)). Qed.
Lemma lem1717413 : term461 = True.
Proof. exact (EQ_MP (@lem1717412) (@lem1717410)). Qed.
Lemma lem1717414 : term460 = True.
Proof. exact (TRANS (@lem1717409) (@lem1717413)). Qed.
Lemma lem1717415 : True = term460.
Proof. exact (SYM (@lem1717414)). Qed.
Lemma lem1717416 : term460.
Proof. exact (EQ_MP (@lem1717415) (@lem0)). Qed.
Lemma lem1717417 (x : real) (h1 : term496 x) : term482 x.
Proof. exact (conj (@lem1717416) (@lem1717384 x h1)). Qed.
Lemma lem1717419 (x : real) (y : real) : term458 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1717420 (x : real) : term483 x.
Proof. exact (@lem1717419 term24 (term80 x)). Qed.
Lemma lem1717421 (x : real) (h1 : term496 x) : term484 x.
Proof. exact (@lem1717420 x (@lem1717417 x h1)). Qed.
Lemma lem1717422 (x : real) : (term485 x) = (term80 x).
Proof. exact (@lem1483460 (term80 x)). Qed.
Lemma lem1717423 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717424 (x : real) : (term486 x) = (term82 x).
Proof. exact (MK_COMB (@lem1717423) (@lem1717422 x)). Qed.
Lemma lem1717425 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1717426 (x : real) : (term484 x) = (term83 x).
Proof. exact (MK_COMB (@lem1717424 x) (@lem1717425)). Qed.
Lemma lem1717427 (x : real) (h1 : term496 x) : term83 x.
Proof. exact (EQ_MP (@lem1717426 x) (@lem1717421 x h1)). Qed.
Lemma lem1717428 (x : real) (h1 : term496 x) : term487 x.
Proof. exact (conj (@lem1717427 x h1) (@lem1717406 x h1)). Qed.
Lemma lem1717430 (x : real) (y : real) : term488 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1717431 (x : real) : term489 x.
Proof. exact (@lem1717430 (term80 x) x). Qed.
Lemma lem1717432 (x : real) (h1 : term496 x) : term280 x.
Proof. exact (@lem1717431 x (@lem1717428 x h1)). Qed.
Lemma lem1717433 (x : real) : (term282 x) = (term283 x).
Proof. exact (@lem1483440 term47 x). Qed.
Lemma lem1717435 (m : nat) : (term284 m) = term50.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1717436 : term285 = term50.
Proof. exact (@lem1717435 term89). Qed.
Lemma lem1717437 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1717438 : term286 = term52.
Proof. exact (MK_COMB (@lem1717437) (@lem1717436)). Qed.
Lemma lem1717439 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1717440 (x : real) : (term283 x) = (term287 x).
Proof. exact (MK_COMB (@lem1717438) (@lem1717439 x)). Qed.
Lemma lem1717441 (x : real) : (term282 x) = (term287 x).
Proof. exact (TRANS (@lem1717433 x) (@lem1717440 x)). Qed.
Lemma lem1717442 (x : real) : (term287 x) = term50.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1717443 (x : real) : (term282 x) = term50.
Proof. exact (TRANS (@lem1717441 x) (@lem1717442 x)). Qed.
Lemma lem1717444 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717445 (x : real) : (term490 x) = term295.
Proof. exact (MK_COMB (@lem1717444) (@lem1717443 x)). Qed.
Lemma lem1717446 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1717447 (x : real) : (term280 x) = term296.
Proof. exact (MK_COMB (@lem1717445 x) (@lem1717446)). Qed.
Lemma lem1717448 (x : real) (h1 : term496 x) : term296.
Proof. exact (EQ_MP (@lem1717447 x) (@lem1717432 x h1)). Qed.
Lemma lem1717450 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717451 : term296 = term453.
Proof. exact (@lem1717450 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1717452 : term453 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1717453 : term296 = False.
Proof. exact (TRANS (@lem1717451) (@lem1717452)). Qed.
Lemma lem1717454 (x : real) (h1 : term496 x) : False.
Proof. exact (EQ_MP (@lem1717453) (@lem1717448 x h1)). Qed.
Lemma lem1717455 (x : real) (h1 : term497 x) : term497 x.
Proof. exact (h1). Qed.
Lemma lem1717456 (x : real) (h1 : term497 x) : term232 x.
Proof. exact (proj2 (@lem1717455 x h1)). Qed.
Lemma lem1717458 (x : real) (h1 : term497 x) : term92 x.
Proof. exact (proj2 (@lem1717456 x h1)). Qed.
Lemma lem1717459 (x : real) (h1 : term497 x) : term136 x.
Proof. exact (proj1 (@lem1717456 x h1)). Qed.
Lemma lem1717461 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717462 : term460 = term461.
Proof. exact (@lem1717461 (NUMERAL 0) term89). Qed.
Lemma lem1717463 : term462 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1717464 (h1 : term462 = (BIT1 0)) : term461 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1717465 : (term462 = (BIT1 0)) = (term461 = True).
Proof. exact (prop_ext (fun h1 : term462 = (BIT1 0) => @lem1717464 h1) (fun h1 : term461 = True => @lem1717463)). Qed.
Lemma lem1717466 : term461 = True.
Proof. exact (EQ_MP (@lem1717465) (@lem1717463)). Qed.
Lemma lem1717467 : term460 = True.
Proof. exact (TRANS (@lem1717462) (@lem1717466)). Qed.
Lemma lem1717468 : True = term460.
Proof. exact (SYM (@lem1717467)). Qed.
Lemma lem1717469 : term460.
Proof. exact (EQ_MP (@lem1717468) (@lem0)). Qed.
Lemma lem1717470 (x : real) (h1 : term497 x) : term498 x.
Proof. exact (conj (@lem1717469) (@lem1717459 x h1)). Qed.
Lemma lem1717472 (x : real) (y : real) : term478 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1717473 (x : real) : term499 x.
Proof. exact (@lem1717472 term24 (term80 x)). Qed.
Lemma lem1717474 (x : real) (h1 : term497 x) : term500 x.
Proof. exact (@lem1717473 x (@lem1717470 x h1)). Qed.
Lemma lem1717475 (x : real) : (term485 x) = (term80 x).
Proof. exact (@lem1483460 (term80 x)). Qed.
Lemma lem1717476 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1717477 (x : real) : (term501 x) = (term135 x).
Proof. exact (MK_COMB (@lem1717476) (@lem1717475 x)). Qed.
Lemma lem1717478 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1717479 (x : real) : (term500 x) = (term136 x).
Proof. exact (MK_COMB (@lem1717477 x) (@lem1717478)). Qed.
Lemma lem1717480 (x : real) (h1 : term497 x) : term136 x.
Proof. exact (EQ_MP (@lem1717479 x) (@lem1717474 x h1)). Qed.
Lemma lem1717482 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717483 : term460 = term461.
Proof. exact (@lem1717482 (NUMERAL 0) term89). Qed.
Lemma lem1717484 : term462 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1717485 (h1 : term462 = (BIT1 0)) : term461 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1717486 : (term462 = (BIT1 0)) = (term461 = True).
Proof. exact (prop_ext (fun h1 : term462 = (BIT1 0) => @lem1717485 h1) (fun h1 : term461 = True => @lem1717484)). Qed.
Lemma lem1717487 : term461 = True.
Proof. exact (EQ_MP (@lem1717486) (@lem1717484)). Qed.
Lemma lem1717488 : term460 = True.
Proof. exact (TRANS (@lem1717483) (@lem1717487)). Qed.
Lemma lem1717489 : True = term460.
Proof. exact (SYM (@lem1717488)). Qed.
Lemma lem1717490 : term460.
Proof. exact (EQ_MP (@lem1717489) (@lem0)). Qed.
Lemma lem1717491 (x : real) (h1 : term497 x) : term502 x.
Proof. exact (conj (@lem1717490) (@lem1717458 x h1)). Qed.
Lemma lem1717493 (x : real) (y : real) : term458 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1717494 (x : real) : term503 x.
Proof. exact (@lem1717493 term24 x). Qed.
Lemma lem1717495 (x : real) (h1 : term497 x) : term504 x.
Proof. exact (@lem1717494 x (@lem1717491 x h1)). Qed.
Lemma lem1717496 (x : real) : (term113 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1717497 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717498 (x : real) : (term505 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1717497) (@lem1717496 x)). Qed.
Lemma lem1717499 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1717500 (x : real) : (term504 x) = (term92 x).
Proof. exact (MK_COMB (@lem1717498 x) (@lem1717499)). Qed.
Lemma lem1717501 (x : real) (h1 : term497 x) : term92 x.
Proof. exact (EQ_MP (@lem1717500 x) (@lem1717495 x h1)). Qed.
Lemma lem1717502 (x : real) (h1 : term497 x) : term506 x.
Proof. exact (conj (@lem1717501 x h1) (@lem1717480 x h1)). Qed.
Lemma lem1717504 (x : real) (y : real) : term488 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1717505 (x : real) : term507 x.
Proof. exact (@lem1717504 x (term80 x)). Qed.
Lemma lem1717506 (x : real) (h1 : term497 x) : term350 x.
Proof. exact (@lem1717505 x (@lem1717502 x h1)). Qed.
Lemma lem1717507 (x : real) : (term348 x) = (term283 x).
Proof. exact (@lem1483442 term47 x). Qed.
Lemma lem1717509 (m : nat) : (term284 m) = term50.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1717510 : term285 = term50.
Proof. exact (@lem1717509 term89). Qed.
Lemma lem1717511 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1717512 : term286 = term52.
Proof. exact (MK_COMB (@lem1717511) (@lem1717510)). Qed.
Lemma lem1717513 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1717514 (x : real) : (term283 x) = (term287 x).
Proof. exact (MK_COMB (@lem1717512) (@lem1717513 x)). Qed.
Lemma lem1717515 (x : real) : (term348 x) = (term287 x).
Proof. exact (TRANS (@lem1717507 x) (@lem1717514 x)). Qed.
Lemma lem1717516 (x : real) : (term287 x) = term50.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1717517 (x : real) : (term348 x) = term50.
Proof. exact (TRANS (@lem1717515 x) (@lem1717516 x)). Qed.
Lemma lem1717518 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717519 (x : real) : (term349 x) = term295.
Proof. exact (MK_COMB (@lem1717518) (@lem1717517 x)). Qed.
Lemma lem1717520 : term50 = term50.
Proof. exact (eq_refl term50). Qed.
Lemma lem1717521 (x : real) : (term350 x) = term296.
Proof. exact (MK_COMB (@lem1717519 x) (@lem1717520)). Qed.
Lemma lem1717522 (x : real) (h1 : term497 x) : term296.
Proof. exact (EQ_MP (@lem1717521 x) (@lem1717506 x h1)). Qed.
Lemma lem1717524 (n : nat) (m : nat) : (term452 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1717525 : term296 = term453.
Proof. exact (@lem1717524 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1717526 : term453 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1717527 : term296 = False.
Proof. exact (TRANS (@lem1717525) (@lem1717526)). Qed.
Lemma lem1717528 (x : real) (h1 : term497 x) : False.
Proof. exact (EQ_MP (@lem1717527) (@lem1717522 x h1)). Qed.
Lemma lem1717529 (x : real) (h1 : term230 x) : False.
Proof. exact (or_elim (@lem1717380 x h1) (fun h0 : term496 x => @lem1717454 x h0) (fun h0 : term497 x => @lem1717528 x h0)). Qed.
Lemma lem1717530 (x : real) (h1 : term449 x) : False.
Proof. exact (or_elim (@lem1717273 x h1) (fun h0 : term447 x => @lem1717379 x h0) (fun h0 : term230 x => @lem1717529 x h0)). Qed.
Lemma lem1717531 (x : real) (h1 : term451 x) : False.
Proof. exact (or_elim (@lem1717058 x h1) (fun h0 : term420 x => @lem1717272 x h0) (fun h0 : term449 x => @lem1717530 x h0)). Qed.
Lemma lem1717532 (x : real) (h1 : term254 x) : term254 x.
Proof. exact (h1). Qed.
Lemma lem1717533 (x : real) (h1 : term254 x) : term451 x.
Proof. exact (EQ_MP (@lem1717057 x) (@lem1717532 x h1)). Qed.
Lemma lem1717534 (x : real) (h1 : term254 x) : (term451 x) = False.
Proof. exact (prop_ext (fun h2 : term451 x => @lem1717531 x h2) (fun h2 : False => @lem1717533 x h1)). Qed.
Lemma lem1717535 (x : real) (h1 : term254 x) : False.
Proof. exact (EQ_MP (@lem1717534 x h1) (@lem1717533 x h1)). Qed.
Lemma lem1717536 (h1 : term256) : term256.
Proof. exact (h1). Qed.
Lemma lem1717537 (h1 : term256) : False.
Proof. exact (ex_elim (@lem1717536 h1) (fun x : real => fun h0 : term255 x => @lem1717535 x h0)). Qed.
Lemma lem1717538 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1717539 (h1 : term14) : term256.
Proof. exact (EQ_MP (@lem1716366) (@lem1717538 h1)). Qed.
Lemma lem1717540 (h1 : term14) : term256 = False.
Proof. exact (prop_ext (fun h2 : term256 => @lem1717537 h2) (fun h2 : False => @lem1717539 h1)). Qed.
Lemma lem1717541 (h1 : term14) : False.
Proof. exact (EQ_MP (@lem1717540 h1) (@lem1717539 h1)). Qed.
Lemma lem1717542 : term508.
Proof. exact (fun h0 : term14 => @lem1717541 h0). Qed.
Lemma lem1717543 : term509.
Proof. exact (@lem1386578 term11). Qed.
Lemma lem1717544 : term11.
Proof. exact (@lem1717543 (@lem1717542)). Qed.
Lemma lem1717545 : term10.
Proof. exact (EQ_MP (@lem1715429) (@lem1717544)). Qed.
