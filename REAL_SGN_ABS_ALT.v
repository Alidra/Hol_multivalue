Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SGN_ABS_ALT_term_abbrevs.
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
Require Import thm1482702_spec.
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
Require Import thm19158_spec.
Require Import thm20234_spec.
Require Import thm20420_spec.
Require Import thm20421_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Lemma lem1717546 (x : real) : term0 x.
Proof. exact (@lem1710164 x). Qed.
Lemma lem1717547 (x : real) : (term0 x) = ((real_sgn x) = (term1 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1717552 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1717547 x) (@lem1717546 x)). Qed.
Lemma lem1717553 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1717554 (x : real) : (term2 x) = (term3 x).
Proof. exact (MK_COMB (@lem1717553) (@lem1717552 x)). Qed.
Lemma lem1717555 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1717556 (x : real) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem1717554 x) (@lem1717555 x)). Qed.
Lemma lem1717557 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1717558 (x : real) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem1717557) (@lem1717556 x)). Qed.
Lemma lem1717559 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1717560 (x : real) : ((term4 x) = (real_abs x)) = ((term5 x) = (real_abs x)).
Proof. exact (MK_COMB (@lem1717558 x) (@lem1717559 x)). Qed.
Lemma lem1717563 (x : real) : ((term5 x) = (real_abs x)) = ((term4 x) = (real_abs x)).
Proof. exact (SYM (@lem1717560 x)). Qed.
Lemma lem1717572 (x : real) (h1 : (term8 x) = False) : (term8 x) = False.
Proof. exact (h1). Qed.
Lemma lem1717573 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1717574 (x : real) (h1 : (term8 x) = False) : (term9 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1717573) (@lem1717572 x h1)). Qed.
Lemma lem1717575 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem1717576 (x : real) (h1 : (term8 x) = False) : (term11 x) = term12.
Proof. exact (MK_COMB (@lem1717574 x h1) (@lem1717575)). Qed.
Lemma lem1717577 (x : real) : (term13 x) = (term13 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1717578 (x : real) (h1 : (term8 x) = False) : (term1 x) = (term14 x).
Proof. exact (MK_COMB (@lem1717576 x h1) (@lem1717577 x)). Qed.
Lemma lem1717580 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1717581 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1717580 real t1 t2). Qed.
Lemma lem1717582 (x : real) : (term14 x) = (term13 x).
Proof. exact (@lem1717581 term10 (term13 x)). Qed.
Lemma lem1717583 (x : real) (h1 : (term8 x) = False) : (term1 x) = (term13 x).
Proof. exact (TRANS (@lem1717578 x h1) (@lem1717582 x)). Qed.
Lemma lem1717584 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1717585 (x : real) (h1 : (term8 x) = False) : (term3 x) = (term15 x).
Proof. exact (MK_COMB (@lem1717584) (@lem1717583 x h1)). Qed.
Lemma lem1717586 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1717587 (x : real) (h1 : (term8 x) = False) : (term5 x) = (term16 x).
Proof. exact (MK_COMB (@lem1717585 x h1) (@lem1717586 x)). Qed.
Lemma lem1717588 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1717589 (x : real) (h1 : (term8 x) = False) : (term7 x) = (term17 x).
Proof. exact (MK_COMB (@lem1717588) (@lem1717587 x h1)). Qed.
Lemma lem1717590 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1717591 (x : real) (h1 : (term8 x) = False) : ((term5 x) = (real_abs x)) = ((term16 x) = (real_abs x)).
Proof. exact (MK_COMB (@lem1717589 x h1) (@lem1717590 x)). Qed.
Lemma lem1717594 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1717595 (x : real) (h1 : (term8 x) = False) : (term18 x) = (term19 x).
Proof. exact (MK_COMB (@lem1717594) (@lem1717591 x h1)). Qed.
Lemma lem1717596 (x : real) : term20 x.
Proof. exact (fun h0 : (term8 x) = False => @lem1717595 x h0). Qed.
Lemma lem1717598 (x : real) (h1 : (term8 x) = True) : (term8 x) = True.
Proof. exact (h1). Qed.
Lemma lem1717599 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1717600 (x : real) (h1 : (term8 x) = True) : (term9 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1717599) (@lem1717598 x h1)). Qed.
Lemma lem1717601 : term10 = term10.
Proof. exact (eq_refl term10). Qed.
Lemma lem1717602 (x : real) (h1 : (term8 x) = True) : (term11 x) = term21.
Proof. exact (MK_COMB (@lem1717600 x h1) (@lem1717601)). Qed.
Lemma lem1717603 (x : real) : (term13 x) = (term13 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1717604 (x : real) (h1 : (term8 x) = True) : (term1 x) = (term22 x).
Proof. exact (MK_COMB (@lem1717602 x h1) (@lem1717603 x)). Qed.
Lemma lem1717606 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1717607 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1717606 real t2 t1). Qed.
Lemma lem1717608 (x : real) : (term22 x) = term10.
Proof. exact (@lem1717607 (term13 x) term10). Qed.
Lemma lem1717609 (x : real) (h1 : (term8 x) = True) : (term1 x) = term10.
Proof. exact (TRANS (@lem1717604 x h1) (@lem1717608 x)). Qed.
Lemma lem1717610 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1717611 (x : real) (h1 : (term8 x) = True) : (term3 x) = term23.
Proof. exact (MK_COMB (@lem1717610) (@lem1717609 x h1)). Qed.
Lemma lem1717612 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1717613 (x : real) (h1 : (term8 x) = True) : (term5 x) = (term24 x).
Proof. exact (MK_COMB (@lem1717611 x h1) (@lem1717612 x)). Qed.
Lemma lem1717614 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1717615 (x : real) (h1 : (term8 x) = True) : (term7 x) = (term25 x).
Proof. exact (MK_COMB (@lem1717614) (@lem1717613 x h1)). Qed.
Lemma lem1717616 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1717617 (x : real) (h1 : (term8 x) = True) : ((term5 x) = (real_abs x)) = ((term24 x) = (real_abs x)).
Proof. exact (MK_COMB (@lem1717615 x h1) (@lem1717616 x)). Qed.
Lemma lem1717620 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1717621 (x : real) (h1 : (term8 x) = True) : (term18 x) = (term26 x).
Proof. exact (MK_COMB (@lem1717620) (@lem1717617 x h1)). Qed.
Lemma lem1717622 (x : real) : term27 x.
Proof. exact (fun h0 : (term8 x) = True => @lem1717621 x h0). Qed.
Lemma lem1717623 (x : real) : term28 x.
Proof. exact (conj (@lem1717596 x) (@lem1717622 x)). Qed.
Lemma lem1717625 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term29 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1717626 (x : real) : term30 x.
Proof. exact (@lem1717625 (term18 x) (term26 x) (term8 x) (term19 x)). Qed.
Lemma lem1717641 (x : real) : (term18 x) = (term31 x).
Proof. exact (@lem1717626 x (@lem1717623 x)). Qed.
Lemma lem1717649 (x : real) (h1 : (term32 x) = False) : (term32 x) = False.
Proof. exact (h1). Qed.
Lemma lem1717650 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1717651 (x : real) (h1 : (term32 x) = False) : (term33 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1717650) (@lem1717649 x h1)). Qed.
Lemma lem1717652 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1717653 (x : real) (h1 : (term32 x) = False) : (term35 x) = term36.
Proof. exact (MK_COMB (@lem1717651 x h1) (@lem1717652)). Qed.
Lemma lem1717654 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1717655 (x : real) (h1 : (term32 x) = False) : (term13 x) = term38.
Proof. exact (MK_COMB (@lem1717653 x h1) (@lem1717654)). Qed.
Lemma lem1717657 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1717658 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1717657 real t1 t2). Qed.
Lemma lem1717659 : term38 = term37.
Proof. exact (@lem1717658 term34 term37). Qed.
Lemma lem1717660 (x : real) (h1 : (term32 x) = False) : (term13 x) = term37.
Proof. exact (TRANS (@lem1717655 x h1) (@lem1717659)). Qed.
Lemma lem1717661 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1717662 (x : real) (h1 : (term32 x) = False) : (term15 x) = term39.
Proof. exact (MK_COMB (@lem1717661) (@lem1717660 x h1)). Qed.
Lemma lem1717663 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1717664 (x : real) (h1 : (term32 x) = False) : (term16 x) = (term40 x).
Proof. exact (MK_COMB (@lem1717662 x h1) (@lem1717663 x)). Qed.
Lemma lem1717665 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1717666 (x : real) (h1 : (term32 x) = False) : (term17 x) = (term41 x).
Proof. exact (MK_COMB (@lem1717665) (@lem1717664 x h1)). Qed.
Lemma lem1717667 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1717668 (x : real) (h1 : (term32 x) = False) : ((term16 x) = (real_abs x)) = ((term40 x) = (real_abs x)).
Proof. exact (MK_COMB (@lem1717666 x h1) (@lem1717667 x)). Qed.
Lemma lem1717671 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1717672 (x : real) (h1 : (term32 x) = False) : (term19 x) = (term42 x).
Proof. exact (MK_COMB (@lem1717671) (@lem1717668 x h1)). Qed.
Lemma lem1717673 (x : real) : (term43 x) = (term43 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1717674 (x : real) (h1 : (term32 x) = False) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem1717673 x) (@lem1717672 x h1)). Qed.
Lemma lem1717677 (x : real) : (term46 x) = (term46 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1717678 (x : real) (h1 : (term32 x) = False) : (term31 x) = (term47 x).
Proof. exact (MK_COMB (@lem1717677 x) (@lem1717674 x h1)). Qed.
Lemma lem1717681 (x : real) : term48 x.
Proof. exact (fun h0 : (term32 x) = False => @lem1717678 x h0). Qed.
Lemma lem1717687 (x : real) (h1 : (term32 x) = True) : (term32 x) = True.
Proof. exact (h1). Qed.
Lemma lem1717688 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1717689 (x : real) (h1 : (term32 x) = True) : (term33 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1717688) (@lem1717687 x h1)). Qed.
Lemma lem1717690 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1717691 (x : real) (h1 : (term32 x) = True) : (term35 x) = term49.
Proof. exact (MK_COMB (@lem1717689 x h1) (@lem1717690)). Qed.
Lemma lem1717692 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1717693 (x : real) (h1 : (term32 x) = True) : (term13 x) = term50.
Proof. exact (MK_COMB (@lem1717691 x h1) (@lem1717692)). Qed.
Lemma lem1717695 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1717696 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1717695 real t2 t1). Qed.
Lemma lem1717697 : term50 = term34.
Proof. exact (@lem1717696 term37 term34). Qed.
Lemma lem1717698 (x : real) (h1 : (term32 x) = True) : (term13 x) = term34.
Proof. exact (TRANS (@lem1717693 x h1) (@lem1717697)). Qed.
Lemma lem1717699 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1717700 (x : real) (h1 : (term32 x) = True) : (term15 x) = term51.
Proof. exact (MK_COMB (@lem1717699) (@lem1717698 x h1)). Qed.
Lemma lem1717701 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1717702 (x : real) (h1 : (term32 x) = True) : (term16 x) = (term52 x).
Proof. exact (MK_COMB (@lem1717700 x h1) (@lem1717701 x)). Qed.
Lemma lem1717703 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1717704 (x : real) (h1 : (term32 x) = True) : (term17 x) = (term53 x).
Proof. exact (MK_COMB (@lem1717703) (@lem1717702 x h1)). Qed.
Lemma lem1717705 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1717706 (x : real) (h1 : (term32 x) = True) : ((term16 x) = (real_abs x)) = ((term52 x) = (real_abs x)).
Proof. exact (MK_COMB (@lem1717704 x h1) (@lem1717705 x)). Qed.
Lemma lem1717709 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1717710 (x : real) (h1 : (term32 x) = True) : (term19 x) = (term54 x).
Proof. exact (MK_COMB (@lem1717709) (@lem1717706 x h1)). Qed.
Lemma lem1717711 (x : real) : (term43 x) = (term43 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1717712 (x : real) (h1 : (term32 x) = True) : (term44 x) = (term55 x).
Proof. exact (MK_COMB (@lem1717711 x) (@lem1717710 x h1)). Qed.
Lemma lem1717715 (x : real) : (term46 x) = (term46 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1717716 (x : real) (h1 : (term32 x) = True) : (term31 x) = (term56 x).
Proof. exact (MK_COMB (@lem1717715 x) (@lem1717712 x h1)). Qed.
Lemma lem1717719 (x : real) : term57 x.
Proof. exact (fun h0 : (term32 x) = True => @lem1717716 x h0). Qed.
Lemma lem1717720 (x : real) : term58 x.
Proof. exact (conj (@lem1717681 x) (@lem1717719 x)). Qed.
Lemma lem1717722 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term29 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1717723 (x : real) : term59 x.
Proof. exact (@lem1717722 (term31 x) (term56 x) (term32 x) (term47 x)). Qed.
Lemma lem1717792 (x : real) : (term31 x) = (term60 x).
Proof. exact (@lem1717723 x (@lem1717720 x)). Qed.
Lemma lem1717793 (x : real) : (term61 x) = (term61 x).
Proof. exact (eq_refl (term61 x)). Qed.
Lemma lem1717794 (x : real) : ((term18 x) = (term31 x)) = ((term18 x) = (term60 x)).
Proof. exact (MK_COMB (@lem1717793 x) (@lem1717792 x)). Qed.
Lemma lem1717796 (x : real) : (term18 x) = (term60 x).
Proof. exact (EQ_MP (@lem1717794 x) (@lem1717641 x)). Qed.
Lemma lem1717797 (x : real) : (term32 x) = (term62 x).
Proof. exact (@lem1483521 term37 x). Qed.
Lemma lem1717803 (x : real) : (term63 x) = (term64 x).
Proof. exact (@lem1483519 term37 x). Qed.
Lemma lem1717808 (x : real) : (term64 x) = (term52 x).
Proof. exact (@lem1483448 (term52 x)). Qed.
Lemma lem1717810 (x : real) : (term63 x) = (term52 x).
Proof. exact (TRANS (@lem1717803 x) (@lem1717808 x)). Qed.
Lemma lem1717811 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717812 (x : real) : (term65 x) = (term66 x).
Proof. exact (MK_COMB (@lem1717811) (@lem1717810 x)). Qed.
Lemma lem1717813 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1717814 (x : real) : (term62 x) = (term67 x).
Proof. exact (MK_COMB (@lem1717812 x) (@lem1717813)). Qed.
Lemma lem1717815 (x : real) : (term32 x) = (term67 x).
Proof. exact (TRANS (@lem1717797 x) (@lem1717814 x)). Qed.
Lemma lem1717816 (x : real) : (term8 x) = (term68 x).
Proof. exact (@lem1483521 x term37). Qed.
Lemma lem1717822 (x : real) : (term69 x) = (term70 x).
Proof. exact (@lem1483519 x term37). Qed.
Lemma lem1717824 (x : nat) : (term71 x) = term37.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1717825 : term72 = term37.
Proof. exact (@lem1717824 term73). Qed.
Lemma lem1717826 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1717827 (x : real) : (term70 x) = (term74 x).
Proof. exact (MK_COMB (@lem1717826 x) (@lem1717825)). Qed.
Lemma lem1717828 (x : real) : (term74 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1717829 (x : real) : (term70 x) = x.
Proof. exact (TRANS (@lem1717827 x) (@lem1717828 x)). Qed.
Lemma lem1717831 (x : real) : (term69 x) = x.
Proof. exact (TRANS (@lem1717822 x) (@lem1717829 x)). Qed.
Lemma lem1717832 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717833 (x : real) : (term75 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1717832) (@lem1717831 x)). Qed.
Lemma lem1717834 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1717835 (x : real) : (term68 x) = (term76 x).
Proof. exact (MK_COMB (@lem1717833 x) (@lem1717834)). Qed.
Lemma lem1717836 (x : real) : (term8 x) = (term76 x).
Proof. exact (TRANS (@lem1717816 x) (@lem1717835 x)). Qed.
Lemma lem1717837 (x : real) : (term26 x) = (term77 x).
Proof. exact (@lem1483554 (term24 x) (real_abs x)). Qed.
Lemma lem1717838 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1717845 (x : real) : (term24 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1717846 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1717847 (x : real) : (term78 x) = (real_sub x).
Proof. exact (MK_COMB (@lem1717846) (@lem1717845 x)). Qed.
Lemma lem1717848 (x : real) : (term79 x) = (term80 x).
Proof. exact (MK_COMB (@lem1717847 x) (@lem1717838 x)). Qed.
Lemma lem1717855 (x : real) : (term80 x) = (term81 x).
Proof. exact (@lem1483519 x (real_abs x)). Qed.
Lemma lem1717856 (x : real) : (term79 x) = (term81 x).
Proof. exact (TRANS (@lem1717848 x) (@lem1717855 x)). Qed.
Lemma lem1717857 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1717858 (x : real) : (term82 x) = (term83 x).
Proof. exact (MK_COMB (@lem1717857) (@lem1717856 x)). Qed.
Lemma lem1717859 (x : real) : (term83 x) = (term84 x).
Proof. exact (@lem1483512 (term81 x)). Qed.
Lemma lem1717860 (x : real) : (term84 x) = (term85 x).
Proof. exact (@lem1483508 x term34 (term86 x)). Qed.
Lemma lem1717861 (x : real) : (term87 x) = (term88 x).
Proof. exact (@lem1483476 term34 term34 (real_abs x)). Qed.
Lemma lem1717863 (m : nat) (n : nat) : (term89 m n) = (term90 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1717864 : term91 = term92.
Proof. exact (@lem1717863 term73 term73). Qed.
Lemma lem1717865 : (term93 = (BIT1 0)) = (term94 = term73).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1717866 : term94 = term73.
Proof. exact (EQ_MP (@lem1717865) (@lem940073)). Qed.
Lemma lem1717867 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1717868 : term92 = term10.
Proof. exact (MK_COMB (@lem1717867) (@lem1717866)). Qed.
Lemma lem1717869 : term91 = term10.
Proof. exact (TRANS (@lem1717864) (@lem1717868)). Qed.
Lemma lem1717870 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1717871 : term95 = term23.
Proof. exact (MK_COMB (@lem1717870) (@lem1717869)). Qed.
Lemma lem1717872 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1717873 (x : real) : (term88 x) = (term96 x).
Proof. exact (MK_COMB (@lem1717871) (@lem1717872 x)). Qed.
Lemma lem1717874 (x : real) : (term87 x) = (term96 x).
Proof. exact (TRANS (@lem1717861 x) (@lem1717873 x)). Qed.
Lemma lem1717875 (x : real) : (term96 x) = (real_abs x).
Proof. exact (@lem1483436 (real_abs x)). Qed.
Lemma lem1717876 (x : real) : (term87 x) = (real_abs x).
Proof. exact (TRANS (@lem1717874 x) (@lem1717875 x)). Qed.
Lemma lem1717879 (x : real) : (term97 x) = (term97 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem1717880 (x : real) : (term85 x) = (term98 x).
Proof. exact (MK_COMB (@lem1717879 x) (@lem1717876 x)). Qed.
Lemma lem1717881 (x : real) : (term84 x) = (term98 x).
Proof. exact (TRANS (@lem1717860 x) (@lem1717880 x)). Qed.
Lemma lem1717882 (x : real) : (term83 x) = (term98 x).
Proof. exact (TRANS (@lem1717859 x) (@lem1717881 x)). Qed.
Lemma lem1717883 (x : real) : (term99 x) = (term99 x).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1717884 (x : real) : ((term82 x) = (term83 x)) = ((term82 x) = (term98 x)).
Proof. exact (MK_COMB (@lem1717883 x) (@lem1717882 x)). Qed.
Lemma lem1717885 (x : real) : (term82 x) = (term98 x).
Proof. exact (EQ_MP (@lem1717884 x) (@lem1717858 x)). Qed.
Lemma lem1717886 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717887 (x : real) : (term100 x) = (term101 x).
Proof. exact (MK_COMB (@lem1717886) (@lem1717885 x)). Qed.
Lemma lem1717888 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1717889 (x : real) : (term102 x) = (term103 x).
Proof. exact (MK_COMB (@lem1717887 x) (@lem1717888)). Qed.
Lemma lem1717890 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717891 (x : real) : (term104 x) = (term105 x).
Proof. exact (MK_COMB (@lem1717890) (@lem1717856 x)). Qed.
Lemma lem1717892 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1717893 (x : real) : (term106 x) = (term107 x).
Proof. exact (MK_COMB (@lem1717891 x) (@lem1717892)). Qed.
Lemma lem1717894 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1717895 (x : real) : (term108 x) = (term109 x).
Proof. exact (MK_COMB (@lem1717894) (@lem1717893 x)). Qed.
Lemma lem1717896 (x : real) : (term77 x) = (term110 x).
Proof. exact (MK_COMB (@lem1717895 x) (@lem1717889 x)). Qed.
Lemma lem1717897 (x : real) : (term26 x) = (term110 x).
Proof. exact (TRANS (@lem1717837 x) (@lem1717896 x)). Qed.
Lemma lem1717898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1717899 (x : real) : (term111 x) = (term112 x).
Proof. exact (MK_COMB (@lem1717898) (@lem1717836 x)). Qed.
Lemma lem1717900 (x : real) : (term113 x) = (term114 x).
Proof. exact (MK_COMB (@lem1717899 x) (@lem1717897 x)). Qed.
Lemma lem1717901 (x : real) : (term115 x) = (term116 x).
Proof. exact (@lem1483531 term37 x). Qed.
Lemma lem1717907 (x : real) : (term63 x) = (term64 x).
Proof. exact (@lem1483519 term37 x). Qed.
Lemma lem1717912 (x : real) : (term64 x) = (term52 x).
Proof. exact (@lem1483448 (term52 x)). Qed.
Lemma lem1717914 (x : real) : (term63 x) = (term52 x).
Proof. exact (TRANS (@lem1717907 x) (@lem1717912 x)). Qed.
Lemma lem1717915 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1717916 (x : real) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1717915) (@lem1717914 x)). Qed.
Lemma lem1717917 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1717918 (x : real) : (term116 x) = (term119 x).
Proof. exact (MK_COMB (@lem1717916 x) (@lem1717917)). Qed.
Lemma lem1717919 (x : real) : (term115 x) = (term119 x).
Proof. exact (TRANS (@lem1717901 x) (@lem1717918 x)). Qed.
Lemma lem1717920 (x : real) : (term54 x) = (term120 x).
Proof. exact (@lem1483554 (term52 x) (real_abs x)). Qed.
Lemma lem1717939 (x : real) : (term121 x) = (term122 x).
Proof. exact (@lem1483519 (term52 x) (real_abs x)). Qed.
Lemma lem1717940 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1717941 (x : real) : (term123 x) = (term124 x).
Proof. exact (MK_COMB (@lem1717940) (@lem1717939 x)). Qed.
Lemma lem1717942 (x : real) : (term124 x) = (term125 x).
Proof. exact (@lem1483512 (term122 x)). Qed.
Lemma lem1717943 (x : real) : (term125 x) = (term126 x).
Proof. exact (@lem1483508 (term52 x) term34 (term86 x)). Qed.
Lemma lem1717944 (x : real) : (term87 x) = (term88 x).
Proof. exact (@lem1483476 term34 term34 (real_abs x)). Qed.
Lemma lem1717946 (m : nat) (n : nat) : (term89 m n) = (term90 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1717947 : term91 = term92.
Proof. exact (@lem1717946 term73 term73). Qed.
Lemma lem1717948 : (term93 = (BIT1 0)) = (term94 = term73).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1717949 : term94 = term73.
Proof. exact (EQ_MP (@lem1717948) (@lem940073)). Qed.
Lemma lem1717950 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1717951 : term92 = term10.
Proof. exact (MK_COMB (@lem1717950) (@lem1717949)). Qed.
Lemma lem1717952 : term91 = term10.
Proof. exact (TRANS (@lem1717947) (@lem1717951)). Qed.
Lemma lem1717953 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1717954 : term95 = term23.
Proof. exact (MK_COMB (@lem1717953) (@lem1717952)). Qed.
Lemma lem1717955 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1717956 (x : real) : (term88 x) = (term96 x).
Proof. exact (MK_COMB (@lem1717954) (@lem1717955 x)). Qed.
Lemma lem1717957 (x : real) : (term87 x) = (term96 x).
Proof. exact (TRANS (@lem1717944 x) (@lem1717956 x)). Qed.
Lemma lem1717958 (x : real) : (term96 x) = (real_abs x).
Proof. exact (@lem1483436 (real_abs x)). Qed.
Lemma lem1717959 (x : real) : (term87 x) = (real_abs x).
Proof. exact (TRANS (@lem1717957 x) (@lem1717958 x)). Qed.
Lemma lem1717960 (x : real) : (term127 x) = (term128 x).
Proof. exact (@lem1483476 term34 term34 x). Qed.
Lemma lem1717962 (m : nat) (n : nat) : (term89 m n) = (term90 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1717963 : term91 = term92.
Proof. exact (@lem1717962 term73 term73). Qed.
Lemma lem1717964 : (term93 = (BIT1 0)) = (term94 = term73).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1717965 : term94 = term73.
Proof. exact (EQ_MP (@lem1717964) (@lem940073)). Qed.
Lemma lem1717966 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1717967 : term92 = term10.
Proof. exact (MK_COMB (@lem1717966) (@lem1717965)). Qed.
Lemma lem1717968 : term91 = term10.
Proof. exact (TRANS (@lem1717963) (@lem1717967)). Qed.
Lemma lem1717969 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1717970 : term95 = term23.
Proof. exact (MK_COMB (@lem1717969) (@lem1717968)). Qed.
Lemma lem1717971 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1717972 (x : real) : (term128 x) = (term24 x).
Proof. exact (MK_COMB (@lem1717970) (@lem1717971 x)). Qed.
Lemma lem1717973 (x : real) : (term127 x) = (term24 x).
Proof. exact (TRANS (@lem1717960 x) (@lem1717972 x)). Qed.
Lemma lem1717974 (x : real) : (term24 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1717975 (x : real) : (term127 x) = x.
Proof. exact (TRANS (@lem1717973 x) (@lem1717974 x)). Qed.
Lemma lem1717976 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1717977 (x : real) : (term129 x) = (real_add x).
Proof. exact (MK_COMB (@lem1717976) (@lem1717975 x)). Qed.
Lemma lem1717978 (x : real) : (term126 x) = (term130 x).
Proof. exact (MK_COMB (@lem1717977 x) (@lem1717959 x)). Qed.
Lemma lem1717979 (x : real) : (term125 x) = (term130 x).
Proof. exact (TRANS (@lem1717943 x) (@lem1717978 x)). Qed.
Lemma lem1717980 (x : real) : (term124 x) = (term130 x).
Proof. exact (TRANS (@lem1717942 x) (@lem1717979 x)). Qed.
Lemma lem1717981 (x : real) : (term131 x) = (term131 x).
Proof. exact (eq_refl (term131 x)). Qed.
Lemma lem1717982 (x : real) : ((term123 x) = (term124 x)) = ((term123 x) = (term130 x)).
Proof. exact (MK_COMB (@lem1717981 x) (@lem1717980 x)). Qed.
Lemma lem1717983 (x : real) : (term123 x) = (term130 x).
Proof. exact (EQ_MP (@lem1717982 x) (@lem1717941 x)). Qed.
Lemma lem1717984 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717985 (x : real) : (term132 x) = (term133 x).
Proof. exact (MK_COMB (@lem1717984) (@lem1717983 x)). Qed.
Lemma lem1717986 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1717987 (x : real) : (term134 x) = (term135 x).
Proof. exact (MK_COMB (@lem1717985 x) (@lem1717986)). Qed.
Lemma lem1717988 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1717989 (x : real) : (term136 x) = (term137 x).
Proof. exact (MK_COMB (@lem1717988) (@lem1717939 x)). Qed.
Lemma lem1717990 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1717991 (x : real) : (term138 x) = (term139 x).
Proof. exact (MK_COMB (@lem1717989 x) (@lem1717990)). Qed.
Lemma lem1717992 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1717993 (x : real) : (term140 x) = (term141 x).
Proof. exact (MK_COMB (@lem1717992) (@lem1717991 x)). Qed.
Lemma lem1717994 (x : real) : (term120 x) = (term142 x).
Proof. exact (MK_COMB (@lem1717993 x) (@lem1717987 x)). Qed.
Lemma lem1717995 (x : real) : (term54 x) = (term142 x).
Proof. exact (TRANS (@lem1717920 x) (@lem1717994 x)). Qed.
Lemma lem1717996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1717997 (x : real) : (term43 x) = (term143 x).
Proof. exact (MK_COMB (@lem1717996) (@lem1717919 x)). Qed.
Lemma lem1717998 (x : real) : (term55 x) = (term144 x).
Proof. exact (MK_COMB (@lem1717997 x) (@lem1717995 x)). Qed.
Lemma lem1717999 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718000 (x : real) : (term46 x) = (term145 x).
Proof. exact (MK_COMB (@lem1717999) (@lem1717900 x)). Qed.
Lemma lem1718001 (x : real) : (term56 x) = (term146 x).
Proof. exact (MK_COMB (@lem1718000 x) (@lem1717998 x)). Qed.
Lemma lem1718002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718003 (x : real) : (term147 x) = (term148 x).
Proof. exact (MK_COMB (@lem1718002) (@lem1717815 x)). Qed.
Lemma lem1718004 (x : real) : (term149 x) = (term150 x).
Proof. exact (MK_COMB (@lem1718003 x) (@lem1718001 x)). Qed.
Lemma lem1718005 (x : real) : (term151 x) = (term152 x).
Proof. exact (@lem1483531 x term37). Qed.
Lemma lem1718011 (x : real) : (term69 x) = (term70 x).
Proof. exact (@lem1483519 x term37). Qed.
Lemma lem1718013 (x : nat) : (term71 x) = term37.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1718014 : term72 = term37.
Proof. exact (@lem1718013 term73). Qed.
Lemma lem1718015 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1718016 (x : real) : (term70 x) = (term74 x).
Proof. exact (MK_COMB (@lem1718015 x) (@lem1718014)). Qed.
Lemma lem1718017 (x : real) : (term74 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1718018 (x : real) : (term70 x) = x.
Proof. exact (TRANS (@lem1718016 x) (@lem1718017 x)). Qed.
Lemma lem1718020 (x : real) : (term69 x) = x.
Proof. exact (TRANS (@lem1718011 x) (@lem1718018 x)). Qed.
Lemma lem1718021 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1718022 (x : real) : (term153 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1718021) (@lem1718020 x)). Qed.
Lemma lem1718023 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718024 (x : real) : (term152 x) = (term154 x).
Proof. exact (MK_COMB (@lem1718022 x) (@lem1718023)). Qed.
Lemma lem1718025 (x : real) : (term151 x) = (term154 x).
Proof. exact (TRANS (@lem1718005 x) (@lem1718024 x)). Qed.
Lemma lem1718026 (x : real) : (term8 x) = (term68 x).
Proof. exact (@lem1483521 x term37). Qed.
Lemma lem1718032 (x : real) : (term69 x) = (term70 x).
Proof. exact (@lem1483519 x term37). Qed.
Lemma lem1718034 (x : nat) : (term71 x) = term37.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1718035 : term72 = term37.
Proof. exact (@lem1718034 term73). Qed.
Lemma lem1718036 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1718037 (x : real) : (term70 x) = (term74 x).
Proof. exact (MK_COMB (@lem1718036 x) (@lem1718035)). Qed.
Lemma lem1718038 (x : real) : (term74 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1718039 (x : real) : (term70 x) = x.
Proof. exact (TRANS (@lem1718037 x) (@lem1718038 x)). Qed.
Lemma lem1718041 (x : real) : (term69 x) = x.
Proof. exact (TRANS (@lem1718032 x) (@lem1718039 x)). Qed.
Lemma lem1718042 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718043 (x : real) : (term75 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1718042) (@lem1718041 x)). Qed.
Lemma lem1718044 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718045 (x : real) : (term68 x) = (term76 x).
Proof. exact (MK_COMB (@lem1718043 x) (@lem1718044)). Qed.
Lemma lem1718046 (x : real) : (term8 x) = (term76 x).
Proof. exact (TRANS (@lem1718026 x) (@lem1718045 x)). Qed.
Lemma lem1718047 (x : real) : (term26 x) = (term77 x).
Proof. exact (@lem1483554 (term24 x) (real_abs x)). Qed.
Lemma lem1718048 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1718055 (x : real) : (term24 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1718056 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1718057 (x : real) : (term78 x) = (real_sub x).
Proof. exact (MK_COMB (@lem1718056) (@lem1718055 x)). Qed.
Lemma lem1718058 (x : real) : (term79 x) = (term80 x).
Proof. exact (MK_COMB (@lem1718057 x) (@lem1718048 x)). Qed.
Lemma lem1718065 (x : real) : (term80 x) = (term81 x).
Proof. exact (@lem1483519 x (real_abs x)). Qed.
Lemma lem1718066 (x : real) : (term79 x) = (term81 x).
Proof. exact (TRANS (@lem1718058 x) (@lem1718065 x)). Qed.
Lemma lem1718067 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1718068 (x : real) : (term82 x) = (term83 x).
Proof. exact (MK_COMB (@lem1718067) (@lem1718066 x)). Qed.
Lemma lem1718069 (x : real) : (term83 x) = (term84 x).
Proof. exact (@lem1483512 (term81 x)). Qed.
Lemma lem1718070 (x : real) : (term84 x) = (term85 x).
Proof. exact (@lem1483508 x term34 (term86 x)). Qed.
Lemma lem1718071 (x : real) : (term87 x) = (term88 x).
Proof. exact (@lem1483476 term34 term34 (real_abs x)). Qed.
Lemma lem1718073 (m : nat) (n : nat) : (term89 m n) = (term90 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1718074 : term91 = term92.
Proof. exact (@lem1718073 term73 term73). Qed.
Lemma lem1718075 : (term93 = (BIT1 0)) = (term94 = term73).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1718076 : term94 = term73.
Proof. exact (EQ_MP (@lem1718075) (@lem940073)). Qed.
Lemma lem1718077 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1718078 : term92 = term10.
Proof. exact (MK_COMB (@lem1718077) (@lem1718076)). Qed.
Lemma lem1718079 : term91 = term10.
Proof. exact (TRANS (@lem1718074) (@lem1718078)). Qed.
Lemma lem1718080 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1718081 : term95 = term23.
Proof. exact (MK_COMB (@lem1718080) (@lem1718079)). Qed.
Lemma lem1718082 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1718083 (x : real) : (term88 x) = (term96 x).
Proof. exact (MK_COMB (@lem1718081) (@lem1718082 x)). Qed.
Lemma lem1718084 (x : real) : (term87 x) = (term96 x).
Proof. exact (TRANS (@lem1718071 x) (@lem1718083 x)). Qed.
Lemma lem1718085 (x : real) : (term96 x) = (real_abs x).
Proof. exact (@lem1483436 (real_abs x)). Qed.
Lemma lem1718086 (x : real) : (term87 x) = (real_abs x).
Proof. exact (TRANS (@lem1718084 x) (@lem1718085 x)). Qed.
Lemma lem1718089 (x : real) : (term97 x) = (term97 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem1718090 (x : real) : (term85 x) = (term98 x).
Proof. exact (MK_COMB (@lem1718089 x) (@lem1718086 x)). Qed.
Lemma lem1718091 (x : real) : (term84 x) = (term98 x).
Proof. exact (TRANS (@lem1718070 x) (@lem1718090 x)). Qed.
Lemma lem1718092 (x : real) : (term83 x) = (term98 x).
Proof. exact (TRANS (@lem1718069 x) (@lem1718091 x)). Qed.
Lemma lem1718093 (x : real) : (term99 x) = (term99 x).
Proof. exact (eq_refl (term99 x)). Qed.
Lemma lem1718094 (x : real) : ((term82 x) = (term83 x)) = ((term82 x) = (term98 x)).
Proof. exact (MK_COMB (@lem1718093 x) (@lem1718092 x)). Qed.
Lemma lem1718095 (x : real) : (term82 x) = (term98 x).
Proof. exact (EQ_MP (@lem1718094 x) (@lem1718068 x)). Qed.
Lemma lem1718096 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718097 (x : real) : (term100 x) = (term101 x).
Proof. exact (MK_COMB (@lem1718096) (@lem1718095 x)). Qed.
Lemma lem1718098 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718099 (x : real) : (term102 x) = (term103 x).
Proof. exact (MK_COMB (@lem1718097 x) (@lem1718098)). Qed.
Lemma lem1718100 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718101 (x : real) : (term104 x) = (term105 x).
Proof. exact (MK_COMB (@lem1718100) (@lem1718066 x)). Qed.
Lemma lem1718102 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718103 (x : real) : (term106 x) = (term107 x).
Proof. exact (MK_COMB (@lem1718101 x) (@lem1718102)). Qed.
Lemma lem1718104 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718105 (x : real) : (term108 x) = (term109 x).
Proof. exact (MK_COMB (@lem1718104) (@lem1718103 x)). Qed.
Lemma lem1718106 (x : real) : (term77 x) = (term110 x).
Proof. exact (MK_COMB (@lem1718105 x) (@lem1718099 x)). Qed.
Lemma lem1718107 (x : real) : (term26 x) = (term110 x).
Proof. exact (TRANS (@lem1718047 x) (@lem1718106 x)). Qed.
Lemma lem1718108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718109 (x : real) : (term111 x) = (term112 x).
Proof. exact (MK_COMB (@lem1718108) (@lem1718046 x)). Qed.
Lemma lem1718110 (x : real) : (term113 x) = (term114 x).
Proof. exact (MK_COMB (@lem1718109 x) (@lem1718107 x)). Qed.
Lemma lem1718111 (x : real) : (term115 x) = (term116 x).
Proof. exact (@lem1483531 term37 x). Qed.
Lemma lem1718117 (x : real) : (term63 x) = (term64 x).
Proof. exact (@lem1483519 term37 x). Qed.
Lemma lem1718122 (x : real) : (term64 x) = (term52 x).
Proof. exact (@lem1483448 (term52 x)). Qed.
Lemma lem1718124 (x : real) : (term63 x) = (term52 x).
Proof. exact (TRANS (@lem1718117 x) (@lem1718122 x)). Qed.
Lemma lem1718125 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1718126 (x : real) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1718125) (@lem1718124 x)). Qed.
Lemma lem1718127 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718128 (x : real) : (term116 x) = (term119 x).
Proof. exact (MK_COMB (@lem1718126 x) (@lem1718127)). Qed.
Lemma lem1718129 (x : real) : (term115 x) = (term119 x).
Proof. exact (TRANS (@lem1718111 x) (@lem1718128 x)). Qed.
Lemma lem1718130 (x : real) : (term42 x) = (term155 x).
Proof. exact (@lem1483554 (term40 x) (real_abs x)). Qed.
Lemma lem1718131 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1718138 (x : real) : (term40 x) = term37.
Proof. exact (@lem1483456 x). Qed.
Lemma lem1718139 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1718140 (x : real) : (term156 x) = term157.
Proof. exact (MK_COMB (@lem1718139) (@lem1718138 x)). Qed.
Lemma lem1718141 (x : real) : (term158 x) = (term159 x).
Proof. exact (MK_COMB (@lem1718140 x) (@lem1718131 x)). Qed.
Lemma lem1718142 (x : real) : (term159 x) = (term160 x).
Proof. exact (@lem1483519 term37 (real_abs x)). Qed.
Lemma lem1718147 (x : real) : (term160 x) = (term86 x).
Proof. exact (@lem1483448 (term86 x)). Qed.
Lemma lem1718148 (x : real) : (term159 x) = (term86 x).
Proof. exact (TRANS (@lem1718142 x) (@lem1718147 x)). Qed.
Lemma lem1718149 (x : real) : (term158 x) = (term86 x).
Proof. exact (TRANS (@lem1718141 x) (@lem1718148 x)). Qed.
Lemma lem1718150 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1718151 (x : real) : (term161 x) = (term162 x).
Proof. exact (MK_COMB (@lem1718150) (@lem1718149 x)). Qed.
Lemma lem1718152 (x : real) : (term162 x) = (term87 x).
Proof. exact (@lem1483512 (term86 x)). Qed.
Lemma lem1718153 (x : real) : (term87 x) = (term88 x).
Proof. exact (@lem1483476 term34 term34 (real_abs x)). Qed.
Lemma lem1718155 (m : nat) (n : nat) : (term89 m n) = (term90 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1718156 : term91 = term92.
Proof. exact (@lem1718155 term73 term73). Qed.
Lemma lem1718157 : (term93 = (BIT1 0)) = (term94 = term73).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1718158 : term94 = term73.
Proof. exact (EQ_MP (@lem1718157) (@lem940073)). Qed.
Lemma lem1718159 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1718160 : term92 = term10.
Proof. exact (MK_COMB (@lem1718159) (@lem1718158)). Qed.
Lemma lem1718161 : term91 = term10.
Proof. exact (TRANS (@lem1718156) (@lem1718160)). Qed.
Lemma lem1718162 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1718163 : term95 = term23.
Proof. exact (MK_COMB (@lem1718162) (@lem1718161)). Qed.
Lemma lem1718164 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1718165 (x : real) : (term88 x) = (term96 x).
Proof. exact (MK_COMB (@lem1718163) (@lem1718164 x)). Qed.
Lemma lem1718166 (x : real) : (term87 x) = (term96 x).
Proof. exact (TRANS (@lem1718153 x) (@lem1718165 x)). Qed.
Lemma lem1718167 (x : real) : (term96 x) = (real_abs x).
Proof. exact (@lem1483436 (real_abs x)). Qed.
Lemma lem1718168 (x : real) : (term87 x) = (real_abs x).
Proof. exact (TRANS (@lem1718166 x) (@lem1718167 x)). Qed.
Lemma lem1718169 (x : real) : (term162 x) = (real_abs x).
Proof. exact (TRANS (@lem1718152 x) (@lem1718168 x)). Qed.
Lemma lem1718170 (x : real) : (term163 x) = (term163 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem1718171 (x : real) : ((term161 x) = (term162 x)) = ((term161 x) = (real_abs x)).
Proof. exact (MK_COMB (@lem1718170 x) (@lem1718169 x)). Qed.
Lemma lem1718172 (x : real) : (term161 x) = (real_abs x).
Proof. exact (EQ_MP (@lem1718171 x) (@lem1718151 x)). Qed.
Lemma lem1718173 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718174 (x : real) : (term164 x) = (term165 x).
Proof. exact (MK_COMB (@lem1718173) (@lem1718172 x)). Qed.
Lemma lem1718175 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718176 (x : real) : (term166 x) = (term167 x).
Proof. exact (MK_COMB (@lem1718174 x) (@lem1718175)). Qed.
Lemma lem1718177 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718178 (x : real) : (term168 x) = (term169 x).
Proof. exact (MK_COMB (@lem1718177) (@lem1718149 x)). Qed.
Lemma lem1718179 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718180 (x : real) : (term170 x) = (term171 x).
Proof. exact (MK_COMB (@lem1718178 x) (@lem1718179)). Qed.
Lemma lem1718181 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718182 (x : real) : (term172 x) = (term173 x).
Proof. exact (MK_COMB (@lem1718181) (@lem1718180 x)). Qed.
Lemma lem1718183 (x : real) : (term155 x) = (term174 x).
Proof. exact (MK_COMB (@lem1718182 x) (@lem1718176 x)). Qed.
Lemma lem1718184 (x : real) : (term42 x) = (term174 x).
Proof. exact (TRANS (@lem1718130 x) (@lem1718183 x)). Qed.
Lemma lem1718185 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718186 (x : real) : (term43 x) = (term143 x).
Proof. exact (MK_COMB (@lem1718185) (@lem1718129 x)). Qed.
Lemma lem1718187 (x : real) : (term45 x) = (term175 x).
Proof. exact (MK_COMB (@lem1718186 x) (@lem1718184 x)). Qed.
Lemma lem1718188 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718189 (x : real) : (term46 x) = (term145 x).
Proof. exact (MK_COMB (@lem1718188) (@lem1718110 x)). Qed.
Lemma lem1718190 (x : real) : (term47 x) = (term176 x).
Proof. exact (MK_COMB (@lem1718189 x) (@lem1718187 x)). Qed.
Lemma lem1718191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718192 (x : real) : (term177 x) = (term178 x).
Proof. exact (MK_COMB (@lem1718191) (@lem1718025 x)). Qed.
Lemma lem1718193 (x : real) : (term179 x) = (term180 x).
Proof. exact (MK_COMB (@lem1718192 x) (@lem1718190 x)). Qed.
Lemma lem1718194 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718195 (x : real) : (term181 x) = (term182 x).
Proof. exact (MK_COMB (@lem1718194) (@lem1718004 x)). Qed.
Lemma lem1718196 (x : real) : (term60 x) = (term183 x).
Proof. exact (MK_COMB (@lem1718195 x) (@lem1718193 x)). Qed.
Lemma lem1718203 (x : real) : (term18 x) = (term183 x).
Proof. exact (TRANS (@lem1717796 x) (@lem1718196 x)). Qed.
Lemma lem1718220 (x : real) : (term175 x) = (term184 x).
Proof. exact (@lem19158 (term171 x) (term119 x) (term167 x)). Qed.
Lemma lem1718237 (x : real) : (term114 x) = (term185 x).
Proof. exact (@lem19158 (term107 x) (term76 x) (term103 x)). Qed.
Lemma lem1718238 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718239 (x : real) : (term145 x) = (term186 x).
Proof. exact (MK_COMB (@lem1718238) (@lem1718237 x)). Qed.
Lemma lem1718240 (x : real) : (term176 x) = (term187 x).
Proof. exact (MK_COMB (@lem1718239 x) (@lem1718220 x)). Qed.
Lemma lem1718243 (x : real) : (term178 x) = (term178 x).
Proof. exact (eq_refl (term178 x)). Qed.
Lemma lem1718244 (x : real) : (term180 x) = (term188 x).
Proof. exact (MK_COMB (@lem1718243 x) (@lem1718240 x)). Qed.
Lemma lem1718245 (x : real) : (term188 x) = (term189 x).
Proof. exact (@lem19158 (term185 x) (term154 x) (term184 x)). Qed.
Lemma lem1718252 (x : real) : (term190 x) = (term191 x).
Proof. exact (@lem19158 (term192 x) (term154 x) (term193 x)). Qed.
Lemma lem1718259 (x : real) : (term194 x) = (term195 x).
Proof. exact (@lem19158 (term196 x) (term154 x) (term197 x)). Qed.
Lemma lem1718260 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718261 (x : real) : (term198 x) = (term199 x).
Proof. exact (MK_COMB (@lem1718260) (@lem1718259 x)). Qed.
Lemma lem1718262 (x : real) : (term189 x) = (term200 x).
Proof. exact (MK_COMB (@lem1718261 x) (@lem1718252 x)). Qed.
Lemma lem1718263 (x : real) : (term188 x) = (term200 x).
Proof. exact (TRANS (@lem1718245 x) (@lem1718262 x)). Qed.
Lemma lem1718264 (x : real) : (term180 x) = (term200 x).
Proof. exact (TRANS (@lem1718244 x) (@lem1718263 x)). Qed.
Lemma lem1718281 (x : real) : (term144 x) = (term201 x).
Proof. exact (@lem19158 (term139 x) (term119 x) (term135 x)). Qed.
Lemma lem1718298 (x : real) : (term114 x) = (term185 x).
Proof. exact (@lem19158 (term107 x) (term76 x) (term103 x)). Qed.
Lemma lem1718299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718300 (x : real) : (term145 x) = (term186 x).
Proof. exact (MK_COMB (@lem1718299) (@lem1718298 x)). Qed.
Lemma lem1718301 (x : real) : (term146 x) = (term202 x).
Proof. exact (MK_COMB (@lem1718300 x) (@lem1718281 x)). Qed.
Lemma lem1718304 (x : real) : (term148 x) = (term148 x).
Proof. exact (eq_refl (term148 x)). Qed.
Lemma lem1718305 (x : real) : (term150 x) = (term203 x).
Proof. exact (MK_COMB (@lem1718304 x) (@lem1718301 x)). Qed.
Lemma lem1718306 (x : real) : (term203 x) = (term204 x).
Proof. exact (@lem19158 (term185 x) (term67 x) (term201 x)). Qed.
Lemma lem1718313 (x : real) : (term205 x) = (term206 x).
Proof. exact (@lem19158 (term207 x) (term67 x) (term208 x)). Qed.
Lemma lem1718320 (x : real) : (term209 x) = (term210 x).
Proof. exact (@lem19158 (term196 x) (term67 x) (term197 x)). Qed.
Lemma lem1718321 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718322 (x : real) : (term211 x) = (term212 x).
Proof. exact (MK_COMB (@lem1718321) (@lem1718320 x)). Qed.
Lemma lem1718323 (x : real) : (term204 x) = (term213 x).
Proof. exact (MK_COMB (@lem1718322 x) (@lem1718313 x)). Qed.
Lemma lem1718324 (x : real) : (term203 x) = (term213 x).
Proof. exact (TRANS (@lem1718306 x) (@lem1718323 x)). Qed.
Lemma lem1718325 (x : real) : (term150 x) = (term213 x).
Proof. exact (TRANS (@lem1718305 x) (@lem1718324 x)). Qed.
Lemma lem1718326 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718327 (x : real) : (term182 x) = (term214 x).
Proof. exact (MK_COMB (@lem1718326) (@lem1718325 x)). Qed.
Lemma lem1718328 (x : real) : (term183 x) = (term215 x).
Proof. exact (MK_COMB (@lem1718327 x) (@lem1718264 x)). Qed.
Lemma lem1718329 (x : real) : (term18 x) = (term215 x).
Proof. exact (TRANS (@lem1718203 x) (@lem1718328 x)). Qed.
Lemma lem1718331 (a : real) (x : real) (r : real) : (term216 a x r) = (term217 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1718332 (x : real) : (term107 x) = (term218 x).
Proof. exact (@lem1718331 x x term37). Qed.
Lemma lem1718339 (x : real) : (term24 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1718342 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1718343 (x : real) : (term219 x) = (real_add x x).
Proof. exact (MK_COMB (@lem1718342 x) (@lem1718339 x)). Qed.
Lemma lem1718344 (x : real) : (real_add x x) = (term220 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1718345 : term221 = term222.
Proof. exact (@lem1367770 term73 term73). Qed.
Lemma lem1718346 : term223 = term224.
Proof. exact (@lem706885). Qed.
Lemma lem1718347 : (term223 = term224) = (term225 = term226).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term224). Qed.
Lemma lem1718348 : term225 = term226.
Proof. exact (EQ_MP (@lem1718347) (@lem1718346)). Qed.
Lemma lem1718349 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1718350 : term222 = term227.
Proof. exact (MK_COMB (@lem1718349) (@lem1718348)). Qed.
Lemma lem1718351 : term221 = term227.
Proof. exact (TRANS (@lem1718345) (@lem1718350)). Qed.
Lemma lem1718352 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1718353 : term228 = term229.
Proof. exact (MK_COMB (@lem1718352) (@lem1718351)). Qed.
Lemma lem1718354 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1718355 (x : real) : (term220 x) = (term230 x).
Proof. exact (MK_COMB (@lem1718353) (@lem1718354 x)). Qed.
Lemma lem1718356 (x : real) : (real_add x x) = (term230 x).
Proof. exact (TRANS (@lem1718344 x) (@lem1718355 x)). Qed.
Lemma lem1718357 (x : real) : (term219 x) = (term230 x).
Proof. exact (TRANS (@lem1718343 x) (@lem1718356 x)). Qed.
Lemma lem1718358 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718359 (x : real) : (term231 x) = (term232 x).
Proof. exact (MK_COMB (@lem1718358) (@lem1718357 x)). Qed.
Lemma lem1718360 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718361 (x : real) : (term233 x) = (term234 x).
Proof. exact (MK_COMB (@lem1718359 x) (@lem1718360)). Qed.
Lemma lem1718373 (x : real) : (term235 x) = (term236 x).
Proof. exact (@lem1483442 term34 x). Qed.
Lemma lem1718375 (m : nat) : (term237 m) = term37.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1718376 : term238 = term37.
Proof. exact (@lem1718375 term73). Qed.
Lemma lem1718377 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1718378 : term239 = term39.
Proof. exact (MK_COMB (@lem1718377) (@lem1718376)). Qed.
Lemma lem1718379 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1718380 (x : real) : (term236 x) = (term40 x).
Proof. exact (MK_COMB (@lem1718378) (@lem1718379 x)). Qed.
Lemma lem1718381 (x : real) : (term235 x) = (term40 x).
Proof. exact (TRANS (@lem1718373 x) (@lem1718380 x)). Qed.
Lemma lem1718382 (x : real) : (term40 x) = term37.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1718384 (x : real) : (term235 x) = term37.
Proof. exact (TRANS (@lem1718381 x) (@lem1718382 x)). Qed.
Lemma lem1718385 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718386 (x : real) : (term240 x) = term241.
Proof. exact (MK_COMB (@lem1718385) (@lem1718384 x)). Qed.
Lemma lem1718387 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718388 (x : real) : (term242 x) = term243.
Proof. exact (MK_COMB (@lem1718386 x) (@lem1718387)). Qed.
Lemma lem1718389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718390 (x : real) : (term244 x) = term245.
Proof. exact (MK_COMB (@lem1718389) (@lem1718388 x)). Qed.
Lemma lem1718391 (x : real) : (term218 x) = (term246 x).
Proof. exact (MK_COMB (@lem1718390 x) (@lem1718361 x)). Qed.
Lemma lem1718392 (x : real) : (term107 x) = (term246 x).
Proof. exact (TRANS (@lem1718332 x) (@lem1718391 x)). Qed.
Lemma lem1718393 (x : real) : (term112 x) = (term112 x).
Proof. exact (eq_refl (term112 x)). Qed.
Lemma lem1718394 (x : real) : (term196 x) = (term247 x).
Proof. exact (MK_COMB (@lem1718393 x) (@lem1718392 x)). Qed.
Lemma lem1718395 (x : real) : (term148 x) = (term148 x).
Proof. exact (eq_refl (term148 x)). Qed.
Lemma lem1718398 (x : real) : (term248 x) = (term249 x).
Proof. exact (MK_COMB (@lem1718395 x) (@lem1718394 x)). Qed.
Lemma lem1718400 (x : real) : (term250 x) = (term251 x).
Proof. exact (eq_refl (term250 x)). Qed.
Lemma lem1718401 (x : real) : (term251 x) = (term250 x).
Proof. exact (SYM (@lem1718400 x)). Qed.
Lemma lem1718402 (x : real) : (term250 x) = (term252 x).
Proof. exact (@lem1482981 (term253 x) x). Qed.
Lemma lem1718403 (x : real) : (term251 x) = (term252 x).
Proof. exact (TRANS (@lem1718401 x) (@lem1718402 x)). Qed.
Lemma lem1718404 (x : real) : (term254 x) = (term255 x).
Proof. exact (eq_refl (term254 x)). Qed.
Lemma lem1718405 (x : real) : (term256 x) = (term256 x).
Proof. exact (eq_refl (term256 x)). Qed.
Lemma lem1718406 (x : real) : (term257 x) = (term258 x).
Proof. exact (MK_COMB (@lem1718405 x) (@lem1718404 x)). Qed.
Lemma lem1718407 (x : real) : (term259 x) = (term260 x).
Proof. exact (eq_refl (term259 x)). Qed.
Lemma lem1718408 (x : real) : (term178 x) = (term178 x).
Proof. exact (eq_refl (term178 x)). Qed.
Lemma lem1718409 (x : real) : (term261 x) = (term262 x).
Proof. exact (MK_COMB (@lem1718408 x) (@lem1718407 x)). Qed.
Lemma lem1718410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718411 (x : real) : (term263 x) = (term264 x).
Proof. exact (MK_COMB (@lem1718410) (@lem1718409 x)). Qed.
Lemma lem1718412 (x : real) : (term252 x) = (term265 x).
Proof. exact (MK_COMB (@lem1718411 x) (@lem1718406 x)). Qed.
Lemma lem1718413 (x : real) : (term266 x) = (term266 x).
Proof. exact (eq_refl (term266 x)). Qed.
Lemma lem1718414 (x : real) : ((term251 x) = (term252 x)) = ((term251 x) = (term265 x)).
Proof. exact (MK_COMB (@lem1718413 x) (@lem1718412 x)). Qed.
Lemma lem1718415 (x : real) : (term251 x) = (term265 x).
Proof. exact (EQ_MP (@lem1718414 x) (@lem1718403 x)). Qed.
Lemma lem1718416 (x : real) : (term154 x) = (term152 x).
Proof. exact (@lem1483527 x term37). Qed.
Lemma lem1718422 (x : real) : (term69 x) = (term70 x).
Proof. exact (@lem1483519 x term37). Qed.
Lemma lem1718424 (x : nat) : (term71 x) = term37.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1718425 : term72 = term37.
Proof. exact (@lem1718424 term73). Qed.
Lemma lem1718426 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1718427 (x : real) : (term70 x) = (term74 x).
Proof. exact (MK_COMB (@lem1718426 x) (@lem1718425)). Qed.
Lemma lem1718428 (x : real) : (term74 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1718429 (x : real) : (term70 x) = x.
Proof. exact (TRANS (@lem1718427 x) (@lem1718428 x)). Qed.
Lemma lem1718431 (x : real) : (term69 x) = x.
Proof. exact (TRANS (@lem1718422 x) (@lem1718429 x)). Qed.
Lemma lem1718432 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1718433 (x : real) : (term153 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1718432) (@lem1718431 x)). Qed.
Lemma lem1718434 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718435 (x : real) : (term152 x) = (term154 x).
Proof. exact (MK_COMB (@lem1718433 x) (@lem1718434)). Qed.
Lemma lem1718436 (x : real) : (term154 x) = (term154 x).
Proof. exact (TRANS (@lem1718416 x) (@lem1718435 x)). Qed.
Lemma lem1718437 (x : real) : (term67 x) = (term267 x).
Proof. exact (@lem1483525 (term52 x) term37). Qed.
Lemma lem1718449 (x : real) : (term268 x) = (term269 x).
Proof. exact (@lem1483519 (term52 x) term37). Qed.
Lemma lem1718451 (x : nat) : (term71 x) = term37.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1718452 : term72 = term37.
Proof. exact (@lem1718451 term73). Qed.
Lemma lem1718453 (x : real) : (term97 x) = (term97 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem1718454 (x : real) : (term269 x) = (term270 x).
Proof. exact (MK_COMB (@lem1718453 x) (@lem1718452)). Qed.
Lemma lem1718455 (x : real) : (term270 x) = (term52 x).
Proof. exact (@lem1483450 (term52 x)). Qed.
Lemma lem1718456 (x : real) : (term269 x) = (term52 x).
Proof. exact (TRANS (@lem1718454 x) (@lem1718455 x)). Qed.
Lemma lem1718458 (x : real) : (term268 x) = (term52 x).
Proof. exact (TRANS (@lem1718449 x) (@lem1718456 x)). Qed.
Lemma lem1718459 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718460 (x : real) : (term271 x) = (term66 x).
Proof. exact (MK_COMB (@lem1718459) (@lem1718458 x)). Qed.
Lemma lem1718461 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718462 (x : real) : (term267 x) = (term67 x).
Proof. exact (MK_COMB (@lem1718460 x) (@lem1718461)). Qed.
Lemma lem1718463 (x : real) : (term67 x) = (term67 x).
Proof. exact (TRANS (@lem1718437 x) (@lem1718462 x)). Qed.
Lemma lem1718464 (x : real) : (term76 x) = (term68 x).
Proof. exact (@lem1483525 x term37). Qed.
Lemma lem1718470 (x : real) : (term69 x) = (term70 x).
Proof. exact (@lem1483519 x term37). Qed.
Lemma lem1718472 (x : nat) : (term71 x) = term37.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1718473 : term72 = term37.
Proof. exact (@lem1718472 term73). Qed.
Lemma lem1718474 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1718475 (x : real) : (term70 x) = (term74 x).
Proof. exact (MK_COMB (@lem1718474 x) (@lem1718473)). Qed.
Lemma lem1718476 (x : real) : (term74 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1718477 (x : real) : (term70 x) = x.
Proof. exact (TRANS (@lem1718475 x) (@lem1718476 x)). Qed.
Lemma lem1718479 (x : real) : (term69 x) = x.
Proof. exact (TRANS (@lem1718470 x) (@lem1718477 x)). Qed.
Lemma lem1718480 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718481 (x : real) : (term75 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1718480) (@lem1718479 x)). Qed.
Lemma lem1718482 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718483 (x : real) : (term68 x) = (term76 x).
Proof. exact (MK_COMB (@lem1718481 x) (@lem1718482)). Qed.
Lemma lem1718484 (x : real) : (term76 x) = (term76 x).
Proof. exact (TRANS (@lem1718464 x) (@lem1718483 x)). Qed.
Lemma lem1718485 (x : real) : (term272 x) = (term273 x).
Proof. exact (@lem1483525 (term274 x) term37). Qed.
Lemma lem1718486 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718498 (x : real) : (term274 x) = (term236 x).
Proof. exact (@lem1483440 term34 x). Qed.
Lemma lem1718500 (m : nat) : (term237 m) = term37.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1718501 : term238 = term37.
Proof. exact (@lem1718500 term73). Qed.
Lemma lem1718502 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1718503 : term239 = term39.
Proof. exact (MK_COMB (@lem1718502) (@lem1718501)). Qed.
Lemma lem1718504 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1718505 (x : real) : (term236 x) = (term40 x).
Proof. exact (MK_COMB (@lem1718503) (@lem1718504 x)). Qed.
Lemma lem1718506 (x : real) : (term274 x) = (term40 x).
Proof. exact (TRANS (@lem1718498 x) (@lem1718505 x)). Qed.
Lemma lem1718507 (x : real) : (term40 x) = term37.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1718509 (x : real) : (term274 x) = term37.
Proof. exact (TRANS (@lem1718506 x) (@lem1718507 x)). Qed.
Lemma lem1718510 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1718511 (x : real) : (term275 x) = term157.
Proof. exact (MK_COMB (@lem1718510) (@lem1718509 x)). Qed.
Lemma lem1718512 (x : real) : (term276 x) = term277.
Proof. exact (MK_COMB (@lem1718511 x) (@lem1718486)). Qed.
Lemma lem1718513 : term277 = term278.
Proof. exact (@lem1483519 term37 term37). Qed.
Lemma lem1718515 (x : nat) : (term71 x) = term37.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1718516 : term72 = term37.
Proof. exact (@lem1718515 term73). Qed.
Lemma lem1718517 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem1718518 : term278 = term280.
Proof. exact (MK_COMB (@lem1718517) (@lem1718516)). Qed.
Lemma lem1718519 : term280 = term37.
Proof. exact (@lem1483448 term37). Qed.
Lemma lem1718520 : term278 = term37.
Proof. exact (TRANS (@lem1718518) (@lem1718519)). Qed.
Lemma lem1718521 : term277 = term37.
Proof. exact (TRANS (@lem1718513) (@lem1718520)). Qed.
Lemma lem1718522 (x : real) : (term276 x) = term37.
Proof. exact (TRANS (@lem1718512 x) (@lem1718521)). Qed.
Lemma lem1718523 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718524 (x : real) : (term281 x) = term241.
Proof. exact (MK_COMB (@lem1718523) (@lem1718522 x)). Qed.
Lemma lem1718525 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718526 (x : real) : (term273 x) = term243.
Proof. exact (MK_COMB (@lem1718524 x) (@lem1718525)). Qed.
Lemma lem1718527 (x : real) : (term272 x) = term243.
Proof. exact (TRANS (@lem1718485 x) (@lem1718526 x)). Qed.
Lemma lem1718528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718529 (x : real) : (term112 x) = (term112 x).
Proof. exact (MK_COMB (@lem1718528) (@lem1718484 x)). Qed.
Lemma lem1718530 (x : real) : (term282 x) = (term283 x).
Proof. exact (MK_COMB (@lem1718529 x) (@lem1718527 x)). Qed.
Lemma lem1718531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718532 (x : real) : (term148 x) = (term148 x).
Proof. exact (MK_COMB (@lem1718531) (@lem1718463 x)). Qed.
Lemma lem1718533 (x : real) : (term260 x) = (term284 x).
Proof. exact (MK_COMB (@lem1718532 x) (@lem1718530 x)). Qed.
Lemma lem1718534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718535 (x : real) : (term178 x) = (term178 x).
Proof. exact (MK_COMB (@lem1718534) (@lem1718436 x)). Qed.
Lemma lem1718536 (x : real) : (term262 x) = (term285 x).
Proof. exact (MK_COMB (@lem1718535 x) (@lem1718533 x)). Qed.
Lemma lem1718537 (x : real) : (term286 x) = (term62 x).
Proof. exact (@lem1483525 term37 x). Qed.
Lemma lem1718543 (x : real) : (term63 x) = (term64 x).
Proof. exact (@lem1483519 term37 x). Qed.
Lemma lem1718548 (x : real) : (term64 x) = (term52 x).
Proof. exact (@lem1483448 (term52 x)). Qed.
Lemma lem1718550 (x : real) : (term63 x) = (term52 x).
Proof. exact (TRANS (@lem1718543 x) (@lem1718548 x)). Qed.
Lemma lem1718551 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718552 (x : real) : (term65 x) = (term66 x).
Proof. exact (MK_COMB (@lem1718551) (@lem1718550 x)). Qed.
Lemma lem1718553 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718554 (x : real) : (term62 x) = (term67 x).
Proof. exact (MK_COMB (@lem1718552 x) (@lem1718553)). Qed.
Lemma lem1718555 (x : real) : (term286 x) = (term67 x).
Proof. exact (TRANS (@lem1718537 x) (@lem1718554 x)). Qed.
Lemma lem1718556 (x : real) : (term287 x) = (term288 x).
Proof. exact (@lem1483525 (term289 x) term37). Qed.
Lemma lem1718557 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718564 (x : real) : (real_neg x) = (term52 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1718573 (x : real) : (term97 x) = (term97 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem1718574 (x : real) : (term289 x) = (term290 x).
Proof. exact (MK_COMB (@lem1718573 x) (@lem1718564 x)). Qed.
Lemma lem1718575 (x : real) : (term290 x) = (term291 x).
Proof. exact (@lem1483438 term34 term34 x). Qed.
Lemma lem1718576 : term292 = term293.
Proof. exact (@lem1367763 term73 term73). Qed.
Lemma lem1718577 : term223 = term224.
Proof. exact (@lem706885). Qed.
Lemma lem1718578 : (term223 = term224) = (term225 = term226).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term224). Qed.
Lemma lem1718579 : term225 = term226.
Proof. exact (EQ_MP (@lem1718578) (@lem1718577)). Qed.
Lemma lem1718580 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1718581 : term222 = term227.
Proof. exact (MK_COMB (@lem1718580) (@lem1718579)). Qed.
Lemma lem1718582 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1718583 : term293 = term294.
Proof. exact (MK_COMB (@lem1718582) (@lem1718581)). Qed.
Lemma lem1718584 : term292 = term294.
Proof. exact (TRANS (@lem1718576) (@lem1718583)). Qed.
Lemma lem1718585 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1718586 : term295 = term296.
Proof. exact (MK_COMB (@lem1718585) (@lem1718584)). Qed.
Lemma lem1718587 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1718588 (x : real) : (term291 x) = (term297 x).
Proof. exact (MK_COMB (@lem1718586) (@lem1718587 x)). Qed.
Lemma lem1718589 (x : real) : (term290 x) = (term297 x).
Proof. exact (TRANS (@lem1718575 x) (@lem1718588 x)). Qed.
Lemma lem1718590 (x : real) : (term289 x) = (term297 x).
Proof. exact (TRANS (@lem1718574 x) (@lem1718589 x)). Qed.
Lemma lem1718591 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1718592 (x : real) : (term298 x) = (term299 x).
Proof. exact (MK_COMB (@lem1718591) (@lem1718590 x)). Qed.
Lemma lem1718593 (x : real) : (term300 x) = (term301 x).
Proof. exact (MK_COMB (@lem1718592 x) (@lem1718557)). Qed.
Lemma lem1718594 (x : real) : (term301 x) = (term302 x).
Proof. exact (@lem1483519 (term297 x) term37). Qed.
Lemma lem1718596 (x : nat) : (term71 x) = term37.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1718597 : term72 = term37.
Proof. exact (@lem1718596 term73). Qed.
Lemma lem1718598 (x : real) : (term303 x) = (term303 x).
Proof. exact (eq_refl (term303 x)). Qed.
Lemma lem1718599 (x : real) : (term302 x) = (term304 x).
Proof. exact (MK_COMB (@lem1718598 x) (@lem1718597)). Qed.
Lemma lem1718600 (x : real) : (term304 x) = (term297 x).
Proof. exact (@lem1483450 (term297 x)). Qed.
Lemma lem1718601 (x : real) : (term302 x) = (term297 x).
Proof. exact (TRANS (@lem1718599 x) (@lem1718600 x)). Qed.
Lemma lem1718602 (x : real) : (term301 x) = (term297 x).
Proof. exact (TRANS (@lem1718594 x) (@lem1718601 x)). Qed.
Lemma lem1718603 (x : real) : (term300 x) = (term297 x).
Proof. exact (TRANS (@lem1718593 x) (@lem1718602 x)). Qed.
Lemma lem1718604 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718605 (x : real) : (term305 x) = (term306 x).
Proof. exact (MK_COMB (@lem1718604) (@lem1718603 x)). Qed.
Lemma lem1718606 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718607 (x : real) : (term288 x) = (term307 x).
Proof. exact (MK_COMB (@lem1718605 x) (@lem1718606)). Qed.
Lemma lem1718608 (x : real) : (term287 x) = (term307 x).
Proof. exact (TRANS (@lem1718556 x) (@lem1718607 x)). Qed.
Lemma lem1718609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718610 (x : real) : (term112 x) = (term112 x).
Proof. exact (MK_COMB (@lem1718609) (@lem1718484 x)). Qed.
Lemma lem1718611 (x : real) : (term308 x) = (term309 x).
Proof. exact (MK_COMB (@lem1718610 x) (@lem1718608 x)). Qed.
Lemma lem1718612 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718613 (x : real) : (term148 x) = (term148 x).
Proof. exact (MK_COMB (@lem1718612) (@lem1718463 x)). Qed.
Lemma lem1718614 (x : real) : (term255 x) = (term310 x).
Proof. exact (MK_COMB (@lem1718613 x) (@lem1718611 x)). Qed.
Lemma lem1718615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718616 (x : real) : (term256 x) = (term148 x).
Proof. exact (MK_COMB (@lem1718615) (@lem1718555 x)). Qed.
Lemma lem1718617 (x : real) : (term258 x) = (term311 x).
Proof. exact (MK_COMB (@lem1718616 x) (@lem1718614 x)). Qed.
Lemma lem1718618 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718619 (x : real) : (term264 x) = (term312 x).
Proof. exact (MK_COMB (@lem1718618) (@lem1718536 x)). Qed.
Lemma lem1718620 (x : real) : (term265 x) = (term313 x).
Proof. exact (MK_COMB (@lem1718619 x) (@lem1718617 x)). Qed.
Lemma lem1718632 (x : real) : (term251 x) = (term313 x).
Proof. exact (TRANS (@lem1718415 x) (@lem1718620 x)). Qed.
Lemma lem1718633 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718634 (x : real) : (term314 x) = (term315 x).
Proof. exact (MK_COMB (@lem1718633) (@lem1718398 x)). Qed.
Lemma lem1718635 (x : real) : (term210 x) = (term316 x).
Proof. exact (MK_COMB (@lem1718634 x) (@lem1718632 x)). Qed.
Lemma lem1718637 (a : real) (x : real) (r : real) : (term216 a x r) = (term217 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1718638 (x : real) : (term139 x) = (term317 x).
Proof. exact (@lem1718637 (term52 x) x term37). Qed.
Lemma lem1718645 (x : real) : (term24 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1718654 (x : real) : (term97 x) = (term97 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem1718655 (x : real) : (term318 x) = (term274 x).
Proof. exact (MK_COMB (@lem1718654 x) (@lem1718645 x)). Qed.
Lemma lem1718656 (x : real) : (term274 x) = (term236 x).
Proof. exact (@lem1483440 term34 x). Qed.
Lemma lem1718658 (m : nat) : (term237 m) = term37.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1718659 : term238 = term37.
Proof. exact (@lem1718658 term73). Qed.
Lemma lem1718660 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1718661 : term239 = term39.
Proof. exact (MK_COMB (@lem1718660) (@lem1718659)). Qed.
Lemma lem1718662 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1718663 (x : real) : (term236 x) = (term40 x).
Proof. exact (MK_COMB (@lem1718661) (@lem1718662 x)). Qed.
Lemma lem1718664 (x : real) : (term274 x) = (term40 x).
Proof. exact (TRANS (@lem1718656 x) (@lem1718663 x)). Qed.
Lemma lem1718665 (x : real) : (term40 x) = term37.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1718666 (x : real) : (term274 x) = term37.
Proof. exact (TRANS (@lem1718664 x) (@lem1718665 x)). Qed.
Lemma lem1718667 (x : real) : (term318 x) = term37.
Proof. exact (TRANS (@lem1718655 x) (@lem1718666 x)). Qed.
Lemma lem1718668 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718669 (x : real) : (term319 x) = term241.
Proof. exact (MK_COMB (@lem1718668) (@lem1718667 x)). Qed.
Lemma lem1718670 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718671 (x : real) : (term320 x) = term243.
Proof. exact (MK_COMB (@lem1718669 x) (@lem1718670)). Qed.
Lemma lem1718689 (x : real) : (term290 x) = (term291 x).
Proof. exact (@lem1483438 term34 term34 x). Qed.
Lemma lem1718690 : term292 = term293.
Proof. exact (@lem1367763 term73 term73). Qed.
Lemma lem1718691 : term223 = term224.
Proof. exact (@lem706885). Qed.
Lemma lem1718692 : (term223 = term224) = (term225 = term226).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term224). Qed.
Lemma lem1718693 : term225 = term226.
Proof. exact (EQ_MP (@lem1718692) (@lem1718691)). Qed.
Lemma lem1718694 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1718695 : term222 = term227.
Proof. exact (MK_COMB (@lem1718694) (@lem1718693)). Qed.
Lemma lem1718696 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1718697 : term293 = term294.
Proof. exact (MK_COMB (@lem1718696) (@lem1718695)). Qed.
Lemma lem1718698 : term292 = term294.
Proof. exact (TRANS (@lem1718690) (@lem1718697)). Qed.
Lemma lem1718699 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1718700 : term295 = term296.
Proof. exact (MK_COMB (@lem1718699) (@lem1718698)). Qed.
Lemma lem1718701 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1718702 (x : real) : (term291 x) = (term297 x).
Proof. exact (MK_COMB (@lem1718700) (@lem1718701 x)). Qed.
Lemma lem1718704 (x : real) : (term290 x) = (term297 x).
Proof. exact (TRANS (@lem1718689 x) (@lem1718702 x)). Qed.
Lemma lem1718705 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718706 (x : real) : (term321 x) = (term306 x).
Proof. exact (MK_COMB (@lem1718705) (@lem1718704 x)). Qed.
Lemma lem1718707 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718708 (x : real) : (term322 x) = (term307 x).
Proof. exact (MK_COMB (@lem1718706 x) (@lem1718707)). Qed.
Lemma lem1718709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718710 (x : real) : (term323 x) = (term324 x).
Proof. exact (MK_COMB (@lem1718709) (@lem1718708 x)). Qed.
Lemma lem1718711 (x : real) : (term317 x) = (term325 x).
Proof. exact (MK_COMB (@lem1718710 x) (@lem1718671 x)). Qed.
Lemma lem1718712 (x : real) : (term139 x) = (term325 x).
Proof. exact (TRANS (@lem1718638 x) (@lem1718711 x)). Qed.
Lemma lem1718713 (x : real) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem1718714 (x : real) : (term207 x) = (term326 x).
Proof. exact (MK_COMB (@lem1718713 x) (@lem1718712 x)). Qed.
Lemma lem1718715 (x : real) : (term148 x) = (term148 x).
Proof. exact (eq_refl (term148 x)). Qed.
Lemma lem1718718 (x : real) : (term327 x) = (term328 x).
Proof. exact (MK_COMB (@lem1718715 x) (@lem1718714 x)). Qed.
Lemma lem1718720 (x : real) : (term329 x) = (term330 x).
Proof. exact (eq_refl (term329 x)). Qed.
Lemma lem1718721 (x : real) : (term330 x) = (term329 x).
Proof. exact (SYM (@lem1718720 x)). Qed.
Lemma lem1718722 (x : real) : (term329 x) = (term331 x).
Proof. exact (@lem1482981 (term332 x) x). Qed.
Lemma lem1718723 (x : real) : (term330 x) = (term331 x).
Proof. exact (TRANS (@lem1718721 x) (@lem1718722 x)). Qed.
Lemma lem1718724 (x : real) : (term333 x) = (term334 x).
Proof. exact (eq_refl (term333 x)). Qed.
Lemma lem1718725 (x : real) : (term256 x) = (term256 x).
Proof. exact (eq_refl (term256 x)). Qed.
Lemma lem1718726 (x : real) : (term335 x) = (term336 x).
Proof. exact (MK_COMB (@lem1718725 x) (@lem1718724 x)). Qed.
Lemma lem1718727 (x : real) : (term337 x) = (term338 x).
Proof. exact (eq_refl (term337 x)). Qed.
Lemma lem1718728 (x : real) : (term178 x) = (term178 x).
Proof. exact (eq_refl (term178 x)). Qed.
Lemma lem1718729 (x : real) : (term339 x) = (term340 x).
Proof. exact (MK_COMB (@lem1718728 x) (@lem1718727 x)). Qed.
Lemma lem1718730 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718731 (x : real) : (term341 x) = (term342 x).
Proof. exact (MK_COMB (@lem1718730) (@lem1718729 x)). Qed.
Lemma lem1718732 (x : real) : (term331 x) = (term343 x).
Proof. exact (MK_COMB (@lem1718731 x) (@lem1718726 x)). Qed.
Lemma lem1718733 (x : real) : (term344 x) = (term344 x).
Proof. exact (eq_refl (term344 x)). Qed.
Lemma lem1718734 (x : real) : ((term330 x) = (term331 x)) = ((term330 x) = (term343 x)).
Proof. exact (MK_COMB (@lem1718733 x) (@lem1718732 x)). Qed.
Lemma lem1718735 (x : real) : (term330 x) = (term343 x).
Proof. exact (EQ_MP (@lem1718734 x) (@lem1718723 x)). Qed.
Lemma lem1718736 (x : real) : (term119 x) = (term345 x).
Proof. exact (@lem1483527 (term52 x) term37). Qed.
Lemma lem1718748 (x : real) : (term268 x) = (term269 x).
Proof. exact (@lem1483519 (term52 x) term37). Qed.
Lemma lem1718750 (x : nat) : (term71 x) = term37.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1718751 : term72 = term37.
Proof. exact (@lem1718750 term73). Qed.
Lemma lem1718752 (x : real) : (term97 x) = (term97 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem1718753 (x : real) : (term269 x) = (term270 x).
Proof. exact (MK_COMB (@lem1718752 x) (@lem1718751)). Qed.
Lemma lem1718754 (x : real) : (term270 x) = (term52 x).
Proof. exact (@lem1483450 (term52 x)). Qed.
Lemma lem1718755 (x : real) : (term269 x) = (term52 x).
Proof. exact (TRANS (@lem1718753 x) (@lem1718754 x)). Qed.
Lemma lem1718757 (x : real) : (term268 x) = (term52 x).
Proof. exact (TRANS (@lem1718748 x) (@lem1718755 x)). Qed.
Lemma lem1718758 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1718759 (x : real) : (term346 x) = (term118 x).
Proof. exact (MK_COMB (@lem1718758) (@lem1718757 x)). Qed.
Lemma lem1718760 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718761 (x : real) : (term345 x) = (term119 x).
Proof. exact (MK_COMB (@lem1718759 x) (@lem1718760)). Qed.
Lemma lem1718762 (x : real) : (term119 x) = (term119 x).
Proof. exact (TRANS (@lem1718736 x) (@lem1718761 x)). Qed.
Lemma lem1718763 (x : real) : (term347 x) = (term348 x).
Proof. exact (@lem1483525 (real_add x x) term37). Qed.
Lemma lem1718764 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718770 (x : real) : (real_add x x) = (term220 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1718771 : term221 = term222.
Proof. exact (@lem1367770 term73 term73). Qed.
Lemma lem1718772 : term223 = term224.
Proof. exact (@lem706885). Qed.
Lemma lem1718773 : (term223 = term224) = (term225 = term226).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term224). Qed.
Lemma lem1718774 : term225 = term226.
Proof. exact (EQ_MP (@lem1718773) (@lem1718772)). Qed.
Lemma lem1718775 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1718776 : term222 = term227.
Proof. exact (MK_COMB (@lem1718775) (@lem1718774)). Qed.
Lemma lem1718777 : term221 = term227.
Proof. exact (TRANS (@lem1718771) (@lem1718776)). Qed.
Lemma lem1718778 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1718779 : term228 = term229.
Proof. exact (MK_COMB (@lem1718778) (@lem1718777)). Qed.
Lemma lem1718780 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1718781 (x : real) : (term220 x) = (term230 x).
Proof. exact (MK_COMB (@lem1718779) (@lem1718780 x)). Qed.
Lemma lem1718783 (x : real) : (real_add x x) = (term230 x).
Proof. exact (TRANS (@lem1718770 x) (@lem1718781 x)). Qed.
Lemma lem1718784 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1718785 (x : real) : (term349 x) = (term350 x).
Proof. exact (MK_COMB (@lem1718784) (@lem1718783 x)). Qed.
Lemma lem1718786 (x : real) : (term351 x) = (term352 x).
Proof. exact (MK_COMB (@lem1718785 x) (@lem1718764)). Qed.
Lemma lem1718787 (x : real) : (term352 x) = (term353 x).
Proof. exact (@lem1483519 (term230 x) term37). Qed.
Lemma lem1718789 (x : nat) : (term71 x) = term37.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1718790 : term72 = term37.
Proof. exact (@lem1718789 term73). Qed.
Lemma lem1718791 (x : real) : (term354 x) = (term354 x).
Proof. exact (eq_refl (term354 x)). Qed.
Lemma lem1718792 (x : real) : (term353 x) = (term355 x).
Proof. exact (MK_COMB (@lem1718791 x) (@lem1718790)). Qed.
Lemma lem1718793 (x : real) : (term355 x) = (term230 x).
Proof. exact (@lem1483450 (term230 x)). Qed.
Lemma lem1718794 (x : real) : (term353 x) = (term230 x).
Proof. exact (TRANS (@lem1718792 x) (@lem1718793 x)). Qed.
Lemma lem1718795 (x : real) : (term352 x) = (term230 x).
Proof. exact (TRANS (@lem1718787 x) (@lem1718794 x)). Qed.
Lemma lem1718796 (x : real) : (term351 x) = (term230 x).
Proof. exact (TRANS (@lem1718786 x) (@lem1718795 x)). Qed.
Lemma lem1718797 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718798 (x : real) : (term356 x) = (term232 x).
Proof. exact (MK_COMB (@lem1718797) (@lem1718796 x)). Qed.
Lemma lem1718799 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718800 (x : real) : (term348 x) = (term234 x).
Proof. exact (MK_COMB (@lem1718798 x) (@lem1718799)). Qed.
Lemma lem1718801 (x : real) : (term347 x) = (term234 x).
Proof. exact (TRANS (@lem1718763 x) (@lem1718800 x)). Qed.
Lemma lem1718802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718803 (x : real) : (term143 x) = (term143 x).
Proof. exact (MK_COMB (@lem1718802) (@lem1718762 x)). Qed.
Lemma lem1718804 (x : real) : (term357 x) = (term358 x).
Proof. exact (MK_COMB (@lem1718803 x) (@lem1718801 x)). Qed.
Lemma lem1718805 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718806 (x : real) : (term148 x) = (term148 x).
Proof. exact (MK_COMB (@lem1718805) (@lem1718463 x)). Qed.
Lemma lem1718807 (x : real) : (term338 x) = (term359 x).
Proof. exact (MK_COMB (@lem1718806 x) (@lem1718804 x)). Qed.
Lemma lem1718808 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718809 (x : real) : (term178 x) = (term178 x).
Proof. exact (MK_COMB (@lem1718808) (@lem1718436 x)). Qed.
Lemma lem1718810 (x : real) : (term340 x) = (term360 x).
Proof. exact (MK_COMB (@lem1718809 x) (@lem1718807 x)). Qed.
Lemma lem1718811 (x : real) : (term361 x) = (term362 x).
Proof. exact (@lem1483525 (term363 x) term37). Qed.
Lemma lem1718812 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718819 (x : real) : (real_neg x) = (term52 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1718822 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1718823 (x : real) : (term363 x) = (term235 x).
Proof. exact (MK_COMB (@lem1718822 x) (@lem1718819 x)). Qed.
Lemma lem1718824 (x : real) : (term235 x) = (term236 x).
Proof. exact (@lem1483442 term34 x). Qed.
Lemma lem1718826 (m : nat) : (term237 m) = term37.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1718827 : term238 = term37.
Proof. exact (@lem1718826 term73). Qed.
Lemma lem1718828 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1718829 : term239 = term39.
Proof. exact (MK_COMB (@lem1718828) (@lem1718827)). Qed.
Lemma lem1718830 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1718831 (x : real) : (term236 x) = (term40 x).
Proof. exact (MK_COMB (@lem1718829) (@lem1718830 x)). Qed.
Lemma lem1718832 (x : real) : (term235 x) = (term40 x).
Proof. exact (TRANS (@lem1718824 x) (@lem1718831 x)). Qed.
Lemma lem1718833 (x : real) : (term40 x) = term37.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1718834 (x : real) : (term235 x) = term37.
Proof. exact (TRANS (@lem1718832 x) (@lem1718833 x)). Qed.
Lemma lem1718835 (x : real) : (term363 x) = term37.
Proof. exact (TRANS (@lem1718823 x) (@lem1718834 x)). Qed.
Lemma lem1718836 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1718837 (x : real) : (term364 x) = term157.
Proof. exact (MK_COMB (@lem1718836) (@lem1718835 x)). Qed.
Lemma lem1718838 (x : real) : (term365 x) = term277.
Proof. exact (MK_COMB (@lem1718837 x) (@lem1718812)). Qed.
Lemma lem1718839 : term277 = term278.
Proof. exact (@lem1483519 term37 term37). Qed.
Lemma lem1718841 (x : nat) : (term71 x) = term37.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1718842 : term72 = term37.
Proof. exact (@lem1718841 term73). Qed.
Lemma lem1718843 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem1718844 : term278 = term280.
Proof. exact (MK_COMB (@lem1718843) (@lem1718842)). Qed.
Lemma lem1718845 : term280 = term37.
Proof. exact (@lem1483448 term37). Qed.
Lemma lem1718846 : term278 = term37.
Proof. exact (TRANS (@lem1718844) (@lem1718845)). Qed.
Lemma lem1718847 : term277 = term37.
Proof. exact (TRANS (@lem1718839) (@lem1718846)). Qed.
Lemma lem1718848 (x : real) : (term365 x) = term37.
Proof. exact (TRANS (@lem1718838 x) (@lem1718847)). Qed.
Lemma lem1718849 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718850 (x : real) : (term366 x) = term241.
Proof. exact (MK_COMB (@lem1718849) (@lem1718848 x)). Qed.
Lemma lem1718851 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718852 (x : real) : (term362 x) = term243.
Proof. exact (MK_COMB (@lem1718850 x) (@lem1718851)). Qed.
Lemma lem1718853 (x : real) : (term361 x) = term243.
Proof. exact (TRANS (@lem1718811 x) (@lem1718852 x)). Qed.
Lemma lem1718854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718855 (x : real) : (term143 x) = (term143 x).
Proof. exact (MK_COMB (@lem1718854) (@lem1718762 x)). Qed.
Lemma lem1718856 (x : real) : (term367 x) = (term368 x).
Proof. exact (MK_COMB (@lem1718855 x) (@lem1718853 x)). Qed.
Lemma lem1718857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718858 (x : real) : (term148 x) = (term148 x).
Proof. exact (MK_COMB (@lem1718857) (@lem1718463 x)). Qed.
Lemma lem1718859 (x : real) : (term334 x) = (term369 x).
Proof. exact (MK_COMB (@lem1718858 x) (@lem1718856 x)). Qed.
Lemma lem1718860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718861 (x : real) : (term256 x) = (term148 x).
Proof. exact (MK_COMB (@lem1718860) (@lem1718555 x)). Qed.
Lemma lem1718862 (x : real) : (term336 x) = (term370 x).
Proof. exact (MK_COMB (@lem1718861 x) (@lem1718859 x)). Qed.
Lemma lem1718863 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718864 (x : real) : (term342 x) = (term371 x).
Proof. exact (MK_COMB (@lem1718863) (@lem1718810 x)). Qed.
Lemma lem1718865 (x : real) : (term343 x) = (term372 x).
Proof. exact (MK_COMB (@lem1718864 x) (@lem1718862 x)). Qed.
Lemma lem1718877 (x : real) : (term330 x) = (term372 x).
Proof. exact (TRANS (@lem1718735 x) (@lem1718865 x)). Qed.
Lemma lem1718878 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718879 (x : real) : (term373 x) = (term374 x).
Proof. exact (MK_COMB (@lem1718878) (@lem1718718 x)). Qed.
Lemma lem1718880 (x : real) : (term206 x) = (term375 x).
Proof. exact (MK_COMB (@lem1718879 x) (@lem1718877 x)). Qed.
Lemma lem1718881 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718882 (x : real) : (term212 x) = (term376 x).
Proof. exact (MK_COMB (@lem1718881) (@lem1718635 x)). Qed.
Lemma lem1718883 (x : real) : (term213 x) = (term377 x).
Proof. exact (MK_COMB (@lem1718882 x) (@lem1718880 x)). Qed.
Lemma lem1718885 (a : real) (x : real) (r : real) : (term216 a x r) = (term217 a x r).
Proof. exact (proj1 (@lem1482704 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1718886 (x : real) : (term107 x) = (term218 x).
Proof. exact (@lem1718885 x x term37). Qed.
Lemma lem1718893 (x : real) : (term24 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1718896 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1718897 (x : real) : (term219 x) = (real_add x x).
Proof. exact (MK_COMB (@lem1718896 x) (@lem1718893 x)). Qed.
Lemma lem1718898 (x : real) : (real_add x x) = (term220 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1718899 : term221 = term222.
Proof. exact (@lem1367770 term73 term73). Qed.
Lemma lem1718900 : term223 = term224.
Proof. exact (@lem706885). Qed.
Lemma lem1718901 : (term223 = term224) = (term225 = term226).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term224). Qed.
Lemma lem1718902 : term225 = term226.
Proof. exact (EQ_MP (@lem1718901) (@lem1718900)). Qed.
Lemma lem1718903 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1718904 : term222 = term227.
Proof. exact (MK_COMB (@lem1718903) (@lem1718902)). Qed.
Lemma lem1718905 : term221 = term227.
Proof. exact (TRANS (@lem1718899) (@lem1718904)). Qed.
Lemma lem1718906 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1718907 : term228 = term229.
Proof. exact (MK_COMB (@lem1718906) (@lem1718905)). Qed.
Lemma lem1718908 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1718909 (x : real) : (term220 x) = (term230 x).
Proof. exact (MK_COMB (@lem1718907) (@lem1718908 x)). Qed.
Lemma lem1718910 (x : real) : (real_add x x) = (term230 x).
Proof. exact (TRANS (@lem1718898 x) (@lem1718909 x)). Qed.
Lemma lem1718911 (x : real) : (term219 x) = (term230 x).
Proof. exact (TRANS (@lem1718897 x) (@lem1718910 x)). Qed.
Lemma lem1718912 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718913 (x : real) : (term231 x) = (term232 x).
Proof. exact (MK_COMB (@lem1718912) (@lem1718911 x)). Qed.
Lemma lem1718914 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718915 (x : real) : (term233 x) = (term234 x).
Proof. exact (MK_COMB (@lem1718913 x) (@lem1718914)). Qed.
Lemma lem1718927 (x : real) : (term235 x) = (term236 x).
Proof. exact (@lem1483442 term34 x). Qed.
Lemma lem1718929 (m : nat) : (term237 m) = term37.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1718930 : term238 = term37.
Proof. exact (@lem1718929 term73). Qed.
Lemma lem1718931 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1718932 : term239 = term39.
Proof. exact (MK_COMB (@lem1718931) (@lem1718930)). Qed.
Lemma lem1718933 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1718934 (x : real) : (term236 x) = (term40 x).
Proof. exact (MK_COMB (@lem1718932) (@lem1718933 x)). Qed.
Lemma lem1718935 (x : real) : (term235 x) = (term40 x).
Proof. exact (TRANS (@lem1718927 x) (@lem1718934 x)). Qed.
Lemma lem1718936 (x : real) : (term40 x) = term37.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1718938 (x : real) : (term235 x) = term37.
Proof. exact (TRANS (@lem1718935 x) (@lem1718936 x)). Qed.
Lemma lem1718939 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1718940 (x : real) : (term240 x) = term241.
Proof. exact (MK_COMB (@lem1718939) (@lem1718938 x)). Qed.
Lemma lem1718941 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1718942 (x : real) : (term242 x) = term243.
Proof. exact (MK_COMB (@lem1718940 x) (@lem1718941)). Qed.
Lemma lem1718943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718944 (x : real) : (term244 x) = term245.
Proof. exact (MK_COMB (@lem1718943) (@lem1718942 x)). Qed.
Lemma lem1718945 (x : real) : (term218 x) = (term246 x).
Proof. exact (MK_COMB (@lem1718944 x) (@lem1718915 x)). Qed.
Lemma lem1718946 (x : real) : (term107 x) = (term246 x).
Proof. exact (TRANS (@lem1718886 x) (@lem1718945 x)). Qed.
Lemma lem1718947 (x : real) : (term112 x) = (term112 x).
Proof. exact (eq_refl (term112 x)). Qed.
Lemma lem1718948 (x : real) : (term196 x) = (term247 x).
Proof. exact (MK_COMB (@lem1718947 x) (@lem1718946 x)). Qed.
Lemma lem1718949 (x : real) : (term178 x) = (term178 x).
Proof. exact (eq_refl (term178 x)). Qed.
Lemma lem1718952 (x : real) : (term378 x) = (term379 x).
Proof. exact (MK_COMB (@lem1718949 x) (@lem1718948 x)). Qed.
Lemma lem1718954 (x : real) : (term380 x) = (term381 x).
Proof. exact (eq_refl (term380 x)). Qed.
Lemma lem1718955 (x : real) : (term381 x) = (term380 x).
Proof. exact (SYM (@lem1718954 x)). Qed.
Lemma lem1718956 (x : real) : (term380 x) = (term382 x).
Proof. exact (@lem1482981 (term383 x) x). Qed.
Lemma lem1718957 (x : real) : (term381 x) = (term382 x).
Proof. exact (TRANS (@lem1718955 x) (@lem1718956 x)). Qed.
Lemma lem1718958 (x : real) : (term384 x) = (term385 x).
Proof. exact (eq_refl (term384 x)). Qed.
Lemma lem1718959 (x : real) : (term256 x) = (term256 x).
Proof. exact (eq_refl (term256 x)). Qed.
Lemma lem1718960 (x : real) : (term386 x) = (term387 x).
Proof. exact (MK_COMB (@lem1718959 x) (@lem1718958 x)). Qed.
Lemma lem1718961 (x : real) : (term388 x) = (term389 x).
Proof. exact (eq_refl (term388 x)). Qed.
Lemma lem1718962 (x : real) : (term178 x) = (term178 x).
Proof. exact (eq_refl (term178 x)). Qed.
Lemma lem1718963 (x : real) : (term390 x) = (term391 x).
Proof. exact (MK_COMB (@lem1718962 x) (@lem1718961 x)). Qed.
Lemma lem1718964 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718965 (x : real) : (term392 x) = (term393 x).
Proof. exact (MK_COMB (@lem1718964) (@lem1718963 x)). Qed.
Lemma lem1718966 (x : real) : (term382 x) = (term394 x).
Proof. exact (MK_COMB (@lem1718965 x) (@lem1718960 x)). Qed.
Lemma lem1718967 (x : real) : (term395 x) = (term395 x).
Proof. exact (eq_refl (term395 x)). Qed.
Lemma lem1718968 (x : real) : ((term381 x) = (term382 x)) = ((term381 x) = (term394 x)).
Proof. exact (MK_COMB (@lem1718967 x) (@lem1718966 x)). Qed.
Lemma lem1718969 (x : real) : (term381 x) = (term394 x).
Proof. exact (EQ_MP (@lem1718968 x) (@lem1718957 x)). Qed.
Lemma lem1718970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718971 (x : real) : (term112 x) = (term112 x).
Proof. exact (MK_COMB (@lem1718970) (@lem1718484 x)). Qed.
Lemma lem1718972 (x : real) : (term282 x) = (term283 x).
Proof. exact (MK_COMB (@lem1718971 x) (@lem1718527 x)). Qed.
Lemma lem1718973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718974 (x : real) : (term178 x) = (term178 x).
Proof. exact (MK_COMB (@lem1718973) (@lem1718436 x)). Qed.
Lemma lem1718975 (x : real) : (term389 x) = (term396 x).
Proof. exact (MK_COMB (@lem1718974 x) (@lem1718972 x)). Qed.
Lemma lem1718976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718977 (x : real) : (term178 x) = (term178 x).
Proof. exact (MK_COMB (@lem1718976) (@lem1718436 x)). Qed.
Lemma lem1718978 (x : real) : (term391 x) = (term397 x).
Proof. exact (MK_COMB (@lem1718977 x) (@lem1718975 x)). Qed.
Lemma lem1718979 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718980 (x : real) : (term112 x) = (term112 x).
Proof. exact (MK_COMB (@lem1718979) (@lem1718484 x)). Qed.
Lemma lem1718981 (x : real) : (term308 x) = (term309 x).
Proof. exact (MK_COMB (@lem1718980 x) (@lem1718608 x)). Qed.
Lemma lem1718982 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718983 (x : real) : (term178 x) = (term178 x).
Proof. exact (MK_COMB (@lem1718982) (@lem1718436 x)). Qed.
Lemma lem1718984 (x : real) : (term385 x) = (term398 x).
Proof. exact (MK_COMB (@lem1718983 x) (@lem1718981 x)). Qed.
Lemma lem1718985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1718986 (x : real) : (term256 x) = (term148 x).
Proof. exact (MK_COMB (@lem1718985) (@lem1718555 x)). Qed.
Lemma lem1718987 (x : real) : (term387 x) = (term399 x).
Proof. exact (MK_COMB (@lem1718986 x) (@lem1718984 x)). Qed.
Lemma lem1718988 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1718989 (x : real) : (term393 x) = (term400 x).
Proof. exact (MK_COMB (@lem1718988) (@lem1718978 x)). Qed.
Lemma lem1718990 (x : real) : (term394 x) = (term401 x).
Proof. exact (MK_COMB (@lem1718989 x) (@lem1718987 x)). Qed.
Lemma lem1719002 (x : real) : (term381 x) = (term401 x).
Proof. exact (TRANS (@lem1718969 x) (@lem1718990 x)). Qed.
Lemma lem1719003 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1719004 (x : real) : (term402 x) = (term403 x).
Proof. exact (MK_COMB (@lem1719003) (@lem1718952 x)). Qed.
Lemma lem1719005 (x : real) : (term195 x) = (term404 x).
Proof. exact (MK_COMB (@lem1719004 x) (@lem1719002 x)). Qed.
Lemma lem1719007 (x : real) (r : real) : (term405 x r) = (term406 x r).
Proof. exact (proj1 (@lem1482702 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1719008 (x : real) : (term171 x) = (term407 x).
Proof. exact (@lem1719007 x term37). Qed.
Lemma lem1719015 (x : real) : (term24 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1719016 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1719017 (x : real) : (term408 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1719016) (@lem1719015 x)). Qed.
Lemma lem1719018 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719019 (x : real) : (term409 x) = (term76 x).
Proof. exact (MK_COMB (@lem1719017 x) (@lem1719018)). Qed.
Lemma lem1719032 (x : real) : (term148 x) = (term148 x).
Proof. exact (eq_refl (term148 x)). Qed.
Lemma lem1719033 (x : real) : (term407 x) = (term410 x).
Proof. exact (MK_COMB (@lem1719032 x) (@lem1719019 x)). Qed.
Lemma lem1719034 (x : real) : (term171 x) = (term410 x).
Proof. exact (TRANS (@lem1719008 x) (@lem1719033 x)). Qed.
Lemma lem1719035 (x : real) : (term143 x) = (term143 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem1719036 (x : real) : (term192 x) = (term411 x).
Proof. exact (MK_COMB (@lem1719035 x) (@lem1719034 x)). Qed.
Lemma lem1719037 (x : real) : (term178 x) = (term178 x).
Proof. exact (eq_refl (term178 x)). Qed.
Lemma lem1719040 (x : real) : (term412 x) = (term413 x).
Proof. exact (MK_COMB (@lem1719037 x) (@lem1719036 x)). Qed.
Lemma lem1719042 (x : real) : (term414 x) = (term415 x).
Proof. exact (eq_refl (term414 x)). Qed.
Lemma lem1719043 (x : real) : (term415 x) = (term414 x).
Proof. exact (SYM (@lem1719042 x)). Qed.
Lemma lem1719044 (x : real) : (term414 x) = (term416 x).
Proof. exact (@lem1482981 (term417 x) x). Qed.
Lemma lem1719045 (x : real) : (term415 x) = (term416 x).
Proof. exact (TRANS (@lem1719043 x) (@lem1719044 x)). Qed.
Lemma lem1719046 (x : real) : (term418 x) = (term419 x).
Proof. exact (eq_refl (term418 x)). Qed.
Lemma lem1719047 (x : real) : (term256 x) = (term256 x).
Proof. exact (eq_refl (term256 x)). Qed.
Lemma lem1719048 (x : real) : (term420 x) = (term421 x).
Proof. exact (MK_COMB (@lem1719047 x) (@lem1719046 x)). Qed.
Lemma lem1719049 (x : real) : (term422 x) = (term423 x).
Proof. exact (eq_refl (term422 x)). Qed.
Lemma lem1719050 (x : real) : (term178 x) = (term178 x).
Proof. exact (eq_refl (term178 x)). Qed.
Lemma lem1719051 (x : real) : (term424 x) = (term425 x).
Proof. exact (MK_COMB (@lem1719050 x) (@lem1719049 x)). Qed.
Lemma lem1719052 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1719053 (x : real) : (term426 x) = (term427 x).
Proof. exact (MK_COMB (@lem1719052) (@lem1719051 x)). Qed.
Lemma lem1719054 (x : real) : (term416 x) = (term428 x).
Proof. exact (MK_COMB (@lem1719053 x) (@lem1719048 x)). Qed.
Lemma lem1719055 (x : real) : (term429 x) = (term429 x).
Proof. exact (eq_refl (term429 x)). Qed.
Lemma lem1719056 (x : real) : ((term415 x) = (term416 x)) = ((term415 x) = (term428 x)).
Proof. exact (MK_COMB (@lem1719055 x) (@lem1719054 x)). Qed.
Lemma lem1719057 (x : real) : (term415 x) = (term428 x).
Proof. exact (EQ_MP (@lem1719056 x) (@lem1719045 x)). Qed.
Lemma lem1719058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1719059 (x : real) : (term143 x) = (term143 x).
Proof. exact (MK_COMB (@lem1719058) (@lem1718762 x)). Qed.
Lemma lem1719060 (x : real) : (term430 x) = (term430 x).
Proof. exact (MK_COMB (@lem1719059 x) (@lem1718484 x)). Qed.
Lemma lem1719061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1719062 (x : real) : (term178 x) = (term178 x).
Proof. exact (MK_COMB (@lem1719061) (@lem1718436 x)). Qed.
Lemma lem1719063 (x : real) : (term423 x) = (term423 x).
Proof. exact (MK_COMB (@lem1719062 x) (@lem1719060 x)). Qed.
Lemma lem1719064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1719065 (x : real) : (term178 x) = (term178 x).
Proof. exact (MK_COMB (@lem1719064) (@lem1718436 x)). Qed.
Lemma lem1719066 (x : real) : (term425 x) = (term425 x).
Proof. exact (MK_COMB (@lem1719065 x) (@lem1719063 x)). Qed.
Lemma lem1719067 (x : real) : (term431 x) = (term432 x).
Proof. exact (@lem1483525 (real_neg x) term37). Qed.
Lemma lem1719068 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719075 (x : real) : (real_neg x) = (term52 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1719076 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1719077 (x : real) : (term433 x) = (term434 x).
Proof. exact (MK_COMB (@lem1719076) (@lem1719075 x)). Qed.
Lemma lem1719078 (x : real) : (term435 x) = (term268 x).
Proof. exact (MK_COMB (@lem1719077 x) (@lem1719068)). Qed.
Lemma lem1719079 (x : real) : (term268 x) = (term269 x).
Proof. exact (@lem1483519 (term52 x) term37). Qed.
Lemma lem1719081 (x : nat) : (term71 x) = term37.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1719082 : term72 = term37.
Proof. exact (@lem1719081 term73). Qed.
Lemma lem1719083 (x : real) : (term97 x) = (term97 x).
Proof. exact (eq_refl (term97 x)). Qed.
Lemma lem1719084 (x : real) : (term269 x) = (term270 x).
Proof. exact (MK_COMB (@lem1719083 x) (@lem1719082)). Qed.
Lemma lem1719085 (x : real) : (term270 x) = (term52 x).
Proof. exact (@lem1483450 (term52 x)). Qed.
Lemma lem1719086 (x : real) : (term269 x) = (term52 x).
Proof. exact (TRANS (@lem1719084 x) (@lem1719085 x)). Qed.
Lemma lem1719087 (x : real) : (term268 x) = (term52 x).
Proof. exact (TRANS (@lem1719079 x) (@lem1719086 x)). Qed.
Lemma lem1719088 (x : real) : (term435 x) = (term52 x).
Proof. exact (TRANS (@lem1719078 x) (@lem1719087 x)). Qed.
Lemma lem1719089 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1719090 (x : real) : (term436 x) = (term66 x).
Proof. exact (MK_COMB (@lem1719089) (@lem1719088 x)). Qed.
Lemma lem1719091 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719092 (x : real) : (term432 x) = (term67 x).
Proof. exact (MK_COMB (@lem1719090 x) (@lem1719091)). Qed.
Lemma lem1719093 (x : real) : (term431 x) = (term67 x).
Proof. exact (TRANS (@lem1719067 x) (@lem1719092 x)). Qed.
Lemma lem1719094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1719095 (x : real) : (term143 x) = (term143 x).
Proof. exact (MK_COMB (@lem1719094) (@lem1718762 x)). Qed.
Lemma lem1719096 (x : real) : (term437 x) = (term438 x).
Proof. exact (MK_COMB (@lem1719095 x) (@lem1719093 x)). Qed.
Lemma lem1719097 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1719098 (x : real) : (term178 x) = (term178 x).
Proof. exact (MK_COMB (@lem1719097) (@lem1718436 x)). Qed.
Lemma lem1719099 (x : real) : (term419 x) = (term439 x).
Proof. exact (MK_COMB (@lem1719098 x) (@lem1719096 x)). Qed.
Lemma lem1719100 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1719101 (x : real) : (term256 x) = (term148 x).
Proof. exact (MK_COMB (@lem1719100) (@lem1718555 x)). Qed.
Lemma lem1719102 (x : real) : (term421 x) = (term440 x).
Proof. exact (MK_COMB (@lem1719101 x) (@lem1719099 x)). Qed.
Lemma lem1719103 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1719104 (x : real) : (term427 x) = (term427 x).
Proof. exact (MK_COMB (@lem1719103) (@lem1719066 x)). Qed.
Lemma lem1719105 (x : real) : (term428 x) = (term441 x).
Proof. exact (MK_COMB (@lem1719104 x) (@lem1719102 x)). Qed.
Lemma lem1719117 (x : real) : (term415 x) = (term441 x).
Proof. exact (TRANS (@lem1719057 x) (@lem1719105 x)). Qed.
Lemma lem1719118 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1719119 (x : real) : (term442 x) = (term443 x).
Proof. exact (MK_COMB (@lem1719118) (@lem1719040 x)). Qed.
Lemma lem1719120 (x : real) : (term191 x) = (term444 x).
Proof. exact (MK_COMB (@lem1719119 x) (@lem1719117 x)). Qed.
Lemma lem1719121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1719122 (x : real) : (term199 x) = (term445 x).
Proof. exact (MK_COMB (@lem1719121) (@lem1719005 x)). Qed.
Lemma lem1719123 (x : real) : (term200 x) = (term446 x).
Proof. exact (MK_COMB (@lem1719122 x) (@lem1719120 x)). Qed.
Lemma lem1719124 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1719125 (x : real) : (term214 x) = (term447 x).
Proof. exact (MK_COMB (@lem1719124) (@lem1718883 x)). Qed.
Lemma lem1719126 (x : real) : (term215 x) = (term448 x).
Proof. exact (MK_COMB (@lem1719125 x) (@lem1719123 x)). Qed.
Lemma lem1719127 (x : real) (h1 : term448 x) : term448 x.
Proof. exact (h1). Qed.
Lemma lem1719128 (x : real) (h1 : term377 x) : term377 x.
Proof. exact (h1). Qed.
Lemma lem1719129 (x : real) (h1 : term316 x) : term316 x.
Proof. exact (h1). Qed.
Lemma lem1719130 (x : real) (h1 : term249 x) : term249 x.
Proof. exact (h1). Qed.
Lemma lem1719131 (x : real) (h1 : term249 x) : term247 x.
Proof. exact (proj2 (@lem1719130 x h1)). Qed.
Lemma lem1719133 (x : real) (h1 : term249 x) : term246 x.
Proof. exact (proj2 (@lem1719131 x h1)). Qed.
Lemma lem1719136 (x : real) (h1 : term249 x) : term243.
Proof. exact (proj1 (@lem1719133 x h1)). Qed.
Lemma lem1719138 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719139 : term243 = term450.
Proof. exact (@lem1719138 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1719140 : term450 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1719141 : term243 = False.
Proof. exact (TRANS (@lem1719139) (@lem1719140)). Qed.
Lemma lem1719142 (x : real) (h1 : term249 x) : False.
Proof. exact (EQ_MP (@lem1719141) (@lem1719136 x h1)). Qed.
Lemma lem1719143 (x : real) (h1 : term313 x) : term313 x.
Proof. exact (h1). Qed.
Lemma lem1719144 (x : real) (h1 : term285 x) : term285 x.
Proof. exact (h1). Qed.
Lemma lem1719145 (x : real) (h1 : term285 x) : term284 x.
Proof. exact (proj2 (@lem1719144 x h1)). Qed.
Lemma lem1719147 (x : real) (h1 : term285 x) : term283 x.
Proof. exact (proj2 (@lem1719145 x h1)). Qed.
Lemma lem1719149 (x : real) (h1 : term285 x) : term243.
Proof. exact (proj2 (@lem1719147 x h1)). Qed.
Lemma lem1719152 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719153 : term243 = term450.
Proof. exact (@lem1719152 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1719154 : term450 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1719155 : term243 = False.
Proof. exact (TRANS (@lem1719153) (@lem1719154)). Qed.
Lemma lem1719156 (x : real) (h1 : term285 x) : False.
Proof. exact (EQ_MP (@lem1719155) (@lem1719149 x h1)). Qed.
Lemma lem1719157 (x : real) (h1 : term311 x) : term311 x.
Proof. exact (h1). Qed.
Lemma lem1719158 (x : real) (h1 : term311 x) : term310 x.
Proof. exact (proj2 (@lem1719157 x h1)). Qed.
Lemma lem1719160 (x : real) (h1 : term311 x) : term309 x.
Proof. exact (proj2 (@lem1719158 x h1)). Qed.
Lemma lem1719162 (x : real) (h1 : term311 x) : term307 x.
Proof. exact (proj2 (@lem1719160 x h1)). Qed.
Lemma lem1719163 (x : real) (h1 : term311 x) : term76 x.
Proof. exact (proj1 (@lem1719160 x h1)). Qed.
Lemma lem1719165 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719166 : term451 = term452.
Proof. exact (@lem1719165 (NUMERAL 0) term226). Qed.
Lemma lem1719167 : term453 = term224.
Proof. exact (@lem912803). Qed.
Lemma lem1719168 (h1 : term453 = term224) : term452 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term224 h1). Qed.
Lemma lem1719169 : (term453 = term224) = (term452 = True).
Proof. exact (prop_ext (fun h1 : term453 = term224 => @lem1719168 h1) (fun h1 : term452 = True => @lem1719167)). Qed.
Lemma lem1719170 : term452 = True.
Proof. exact (EQ_MP (@lem1719169) (@lem1719167)). Qed.
Lemma lem1719171 : term451 = True.
Proof. exact (TRANS (@lem1719166) (@lem1719170)). Qed.
Lemma lem1719172 : True = term451.
Proof. exact (SYM (@lem1719171)). Qed.
Lemma lem1719173 : term451.
Proof. exact (EQ_MP (@lem1719172) (@lem0)). Qed.
Lemma lem1719174 (x : real) (h1 : term311 x) : term454 x.
Proof. exact (conj (@lem1719173) (@lem1719163 x h1)). Qed.
Lemma lem1719176 (x : real) (y : real) : term455 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1719177 (x : real) : term456 x.
Proof. exact (@lem1719176 term227 x). Qed.
Lemma lem1719184 (x : real) (h1 : term311 x) : term234 x.
Proof. exact (@lem1719177 x (@lem1719174 x h1)). Qed.
Lemma lem1719186 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719187 : term457 = term458.
Proof. exact (@lem1719186 (NUMERAL 0) term73). Qed.
Lemma lem1719188 : term459 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1719189 (h1 : term459 = (BIT1 0)) : term458 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1719190 : (term459 = (BIT1 0)) = (term458 = True).
Proof. exact (prop_ext (fun h1 : term459 = (BIT1 0) => @lem1719189 h1) (fun h1 : term458 = True => @lem1719188)). Qed.
Lemma lem1719191 : term458 = True.
Proof. exact (EQ_MP (@lem1719190) (@lem1719188)). Qed.
Lemma lem1719192 : term457 = True.
Proof. exact (TRANS (@lem1719187) (@lem1719191)). Qed.
Lemma lem1719193 : True = term457.
Proof. exact (SYM (@lem1719192)). Qed.
Lemma lem1719194 : term457.
Proof. exact (EQ_MP (@lem1719193) (@lem0)). Qed.
Lemma lem1719195 (x : real) (h1 : term311 x) : term460 x.
Proof. exact (conj (@lem1719194) (@lem1719162 x h1)). Qed.
Lemma lem1719197 (x : real) (y : real) : term455 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1719198 (x : real) : term461 x.
Proof. exact (@lem1719197 term10 (term297 x)). Qed.
Lemma lem1719199 (x : real) (h1 : term311 x) : term462 x.
Proof. exact (@lem1719198 x (@lem1719195 x h1)). Qed.
Lemma lem1719200 (x : real) : (term463 x) = (term297 x).
Proof. exact (@lem1483460 (term297 x)). Qed.
Lemma lem1719201 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1719202 (x : real) : (term464 x) = (term306 x).
Proof. exact (MK_COMB (@lem1719201) (@lem1719200 x)). Qed.
Lemma lem1719203 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719204 (x : real) : (term462 x) = (term307 x).
Proof. exact (MK_COMB (@lem1719202 x) (@lem1719203)). Qed.
Lemma lem1719205 (x : real) (h1 : term311 x) : term307 x.
Proof. exact (EQ_MP (@lem1719204 x) (@lem1719199 x h1)). Qed.
Lemma lem1719206 (x : real) (h1 : term311 x) : term465 x.
Proof. exact (conj (@lem1719205 x h1) (@lem1719184 x h1)). Qed.
Lemma lem1719208 (x : real) (y : real) : term466 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1719209 (x : real) : term467 x.
Proof. exact (@lem1719208 (term297 x) (term230 x)). Qed.
Lemma lem1719210 (x : real) (h1 : term311 x) : term468 x.
Proof. exact (@lem1719209 x (@lem1719206 x h1)). Qed.
Lemma lem1719211 (x : real) : (term469 x) = (term470 x).
Proof. exact (@lem1483438 term294 term227 x). Qed.
Lemma lem1719213 (m : nat) : (term237 m) = term37.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1719214 : term471 = term37.
Proof. exact (@lem1719213 term226). Qed.
Lemma lem1719215 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1719216 : term472 = term39.
Proof. exact (MK_COMB (@lem1719215) (@lem1719214)). Qed.
Lemma lem1719217 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1719218 (x : real) : (term470 x) = (term40 x).
Proof. exact (MK_COMB (@lem1719216) (@lem1719217 x)). Qed.
Lemma lem1719219 (x : real) : (term469 x) = (term40 x).
Proof. exact (TRANS (@lem1719211 x) (@lem1719218 x)). Qed.
Lemma lem1719220 (x : real) : (term40 x) = term37.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1719221 (x : real) : (term469 x) = term37.
Proof. exact (TRANS (@lem1719219 x) (@lem1719220 x)). Qed.
Lemma lem1719222 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1719223 (x : real) : (term473 x) = term241.
Proof. exact (MK_COMB (@lem1719222) (@lem1719221 x)). Qed.
Lemma lem1719224 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719225 (x : real) : (term468 x) = term243.
Proof. exact (MK_COMB (@lem1719223 x) (@lem1719224)). Qed.
Lemma lem1719226 (x : real) (h1 : term311 x) : term243.
Proof. exact (EQ_MP (@lem1719225 x) (@lem1719210 x h1)). Qed.
Lemma lem1719228 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719229 : term243 = term450.
Proof. exact (@lem1719228 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1719230 : term450 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1719231 : term243 = False.
Proof. exact (TRANS (@lem1719229) (@lem1719230)). Qed.
Lemma lem1719232 (x : real) (h1 : term311 x) : False.
Proof. exact (EQ_MP (@lem1719231) (@lem1719226 x h1)). Qed.
Lemma lem1719233 (x : real) (h1 : term313 x) : False.
Proof. exact (or_elim (@lem1719143 x h1) (fun h0 : term285 x => @lem1719156 x h0) (fun h0 : term311 x => @lem1719232 x h0)). Qed.
Lemma lem1719234 (x : real) (h1 : term316 x) : False.
Proof. exact (or_elim (@lem1719129 x h1) (fun h0 : term249 x => @lem1719142 x h0) (fun h0 : term313 x => @lem1719233 x h0)). Qed.
Lemma lem1719235 (x : real) (h1 : term375 x) : term375 x.
Proof. exact (h1). Qed.
Lemma lem1719236 (x : real) (h1 : term328 x) : term328 x.
Proof. exact (h1). Qed.
Lemma lem1719237 (x : real) (h1 : term328 x) : term326 x.
Proof. exact (proj2 (@lem1719236 x h1)). Qed.
Lemma lem1719239 (x : real) (h1 : term328 x) : term325 x.
Proof. exact (proj2 (@lem1719237 x h1)). Qed.
Lemma lem1719241 (x : real) (h1 : term328 x) : term243.
Proof. exact (proj2 (@lem1719239 x h1)). Qed.
Lemma lem1719244 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719245 : term243 = term450.
Proof. exact (@lem1719244 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1719246 : term450 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1719247 : term243 = False.
Proof. exact (TRANS (@lem1719245) (@lem1719246)). Qed.
Lemma lem1719248 (x : real) (h1 : term328 x) : False.
Proof. exact (EQ_MP (@lem1719247) (@lem1719241 x h1)). Qed.
Lemma lem1719249 (x : real) (h1 : term372 x) : term372 x.
Proof. exact (h1). Qed.
Lemma lem1719250 (x : real) (h1 : term360 x) : term360 x.
Proof. exact (h1). Qed.
Lemma lem1719251 (x : real) (h1 : term360 x) : term359 x.
Proof. exact (proj2 (@lem1719250 x h1)). Qed.
Lemma lem1719252 (x : real) (h1 : term360 x) : term154 x.
Proof. exact (proj1 (@lem1719250 x h1)). Qed.
Lemma lem1719254 (x : real) (h1 : term360 x) : term67 x.
Proof. exact (proj1 (@lem1719251 x h1)). Qed.
Lemma lem1719258 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719259 : term457 = term458.
Proof. exact (@lem1719258 (NUMERAL 0) term73). Qed.
Lemma lem1719260 : term459 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1719261 (h1 : term459 = (BIT1 0)) : term458 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1719262 : (term459 = (BIT1 0)) = (term458 = True).
Proof. exact (prop_ext (fun h1 : term459 = (BIT1 0) => @lem1719261 h1) (fun h1 : term458 = True => @lem1719260)). Qed.
Lemma lem1719263 : term458 = True.
Proof. exact (EQ_MP (@lem1719262) (@lem1719260)). Qed.
Lemma lem1719264 : term457 = True.
Proof. exact (TRANS (@lem1719259) (@lem1719263)). Qed.
Lemma lem1719265 : True = term457.
Proof. exact (SYM (@lem1719264)). Qed.
Lemma lem1719266 : term457.
Proof. exact (EQ_MP (@lem1719265) (@lem0)). Qed.
Lemma lem1719267 (x : real) (h1 : term360 x) : term474 x.
Proof. exact (conj (@lem1719266) (@lem1719252 x h1)). Qed.
Lemma lem1719269 (x : real) (y : real) : term475 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1719270 (x : real) : term476 x.
Proof. exact (@lem1719269 term10 x). Qed.
Lemma lem1719271 (x : real) (h1 : term360 x) : term477 x.
Proof. exact (@lem1719270 x (@lem1719267 x h1)). Qed.
Lemma lem1719272 (x : real) : (term24 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1719273 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1719274 (x : real) : (term478 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1719273) (@lem1719272 x)). Qed.
Lemma lem1719275 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719276 (x : real) : (term477 x) = (term154 x).
Proof. exact (MK_COMB (@lem1719274 x) (@lem1719275)). Qed.
Lemma lem1719277 (x : real) (h1 : term360 x) : term154 x.
Proof. exact (EQ_MP (@lem1719276 x) (@lem1719271 x h1)). Qed.
Lemma lem1719279 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719280 : term457 = term458.
Proof. exact (@lem1719279 (NUMERAL 0) term73). Qed.
Lemma lem1719281 : term459 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1719282 (h1 : term459 = (BIT1 0)) : term458 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1719283 : (term459 = (BIT1 0)) = (term458 = True).
Proof. exact (prop_ext (fun h1 : term459 = (BIT1 0) => @lem1719282 h1) (fun h1 : term458 = True => @lem1719281)). Qed.
Lemma lem1719284 : term458 = True.
Proof. exact (EQ_MP (@lem1719283) (@lem1719281)). Qed.
Lemma lem1719285 : term457 = True.
Proof. exact (TRANS (@lem1719280) (@lem1719284)). Qed.
Lemma lem1719286 : True = term457.
Proof. exact (SYM (@lem1719285)). Qed.
Lemma lem1719287 : term457.
Proof. exact (EQ_MP (@lem1719286) (@lem0)). Qed.
Lemma lem1719288 (x : real) (h1 : term360 x) : term479 x.
Proof. exact (conj (@lem1719287) (@lem1719254 x h1)). Qed.
Lemma lem1719290 (x : real) (y : real) : term455 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1719291 (x : real) : term480 x.
Proof. exact (@lem1719290 term10 (term52 x)). Qed.
Lemma lem1719292 (x : real) (h1 : term360 x) : term481 x.
Proof. exact (@lem1719291 x (@lem1719288 x h1)). Qed.
Lemma lem1719293 (x : real) : (term482 x) = (term52 x).
Proof. exact (@lem1483460 (term52 x)). Qed.
Lemma lem1719294 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1719295 (x : real) : (term483 x) = (term66 x).
Proof. exact (MK_COMB (@lem1719294) (@lem1719293 x)). Qed.
Lemma lem1719296 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719297 (x : real) : (term481 x) = (term67 x).
Proof. exact (MK_COMB (@lem1719295 x) (@lem1719296)). Qed.
Lemma lem1719298 (x : real) (h1 : term360 x) : term67 x.
Proof. exact (EQ_MP (@lem1719297 x) (@lem1719292 x h1)). Qed.
Lemma lem1719299 (x : real) (h1 : term360 x) : term484 x.
Proof. exact (conj (@lem1719298 x h1) (@lem1719277 x h1)). Qed.
Lemma lem1719301 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1719302 (x : real) : term486 x.
Proof. exact (@lem1719301 (term52 x) x). Qed.
Lemma lem1719303 (x : real) (h1 : term360 x) : term272 x.
Proof. exact (@lem1719302 x (@lem1719299 x h1)). Qed.
Lemma lem1719304 (x : real) : (term274 x) = (term236 x).
Proof. exact (@lem1483440 term34 x). Qed.
Lemma lem1719306 (m : nat) : (term237 m) = term37.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1719307 : term238 = term37.
Proof. exact (@lem1719306 term73). Qed.
Lemma lem1719308 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1719309 : term239 = term39.
Proof. exact (MK_COMB (@lem1719308) (@lem1719307)). Qed.
Lemma lem1719310 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1719311 (x : real) : (term236 x) = (term40 x).
Proof. exact (MK_COMB (@lem1719309) (@lem1719310 x)). Qed.
Lemma lem1719312 (x : real) : (term274 x) = (term40 x).
Proof. exact (TRANS (@lem1719304 x) (@lem1719311 x)). Qed.
Lemma lem1719313 (x : real) : (term40 x) = term37.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1719314 (x : real) : (term274 x) = term37.
Proof. exact (TRANS (@lem1719312 x) (@lem1719313 x)). Qed.
Lemma lem1719315 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1719316 (x : real) : (term487 x) = term241.
Proof. exact (MK_COMB (@lem1719315) (@lem1719314 x)). Qed.
Lemma lem1719317 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719318 (x : real) : (term272 x) = term243.
Proof. exact (MK_COMB (@lem1719316 x) (@lem1719317)). Qed.
Lemma lem1719319 (x : real) (h1 : term360 x) : term243.
Proof. exact (EQ_MP (@lem1719318 x) (@lem1719303 x h1)). Qed.
Lemma lem1719321 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719322 : term243 = term450.
Proof. exact (@lem1719321 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1719323 : term450 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1719324 : term243 = False.
Proof. exact (TRANS (@lem1719322) (@lem1719323)). Qed.
Lemma lem1719325 (x : real) (h1 : term360 x) : False.
Proof. exact (EQ_MP (@lem1719324) (@lem1719319 x h1)). Qed.
Lemma lem1719326 (x : real) (h1 : term370 x) : term370 x.
Proof. exact (h1). Qed.
Lemma lem1719327 (x : real) (h1 : term370 x) : term369 x.
Proof. exact (proj2 (@lem1719326 x h1)). Qed.
Lemma lem1719329 (x : real) (h1 : term370 x) : term368 x.
Proof. exact (proj2 (@lem1719327 x h1)). Qed.
Lemma lem1719331 (x : real) (h1 : term370 x) : term243.
Proof. exact (proj2 (@lem1719329 x h1)). Qed.
Lemma lem1719334 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719335 : term243 = term450.
Proof. exact (@lem1719334 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1719336 : term450 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1719337 : term243 = False.
Proof. exact (TRANS (@lem1719335) (@lem1719336)). Qed.
Lemma lem1719338 (x : real) (h1 : term370 x) : False.
Proof. exact (EQ_MP (@lem1719337) (@lem1719331 x h1)). Qed.
Lemma lem1719339 (x : real) (h1 : term372 x) : False.
Proof. exact (or_elim (@lem1719249 x h1) (fun h0 : term360 x => @lem1719325 x h0) (fun h0 : term370 x => @lem1719338 x h0)). Qed.
Lemma lem1719340 (x : real) (h1 : term375 x) : False.
Proof. exact (or_elim (@lem1719235 x h1) (fun h0 : term328 x => @lem1719248 x h0) (fun h0 : term372 x => @lem1719339 x h0)). Qed.
Lemma lem1719341 (x : real) (h1 : term377 x) : False.
Proof. exact (or_elim (@lem1719128 x h1) (fun h0 : term316 x => @lem1719234 x h0) (fun h0 : term375 x => @lem1719340 x h0)). Qed.
Lemma lem1719342 (x : real) (h1 : term446 x) : term446 x.
Proof. exact (h1). Qed.
Lemma lem1719343 (x : real) (h1 : term404 x) : term404 x.
Proof. exact (h1). Qed.
Lemma lem1719344 (x : real) (h1 : term379 x) : term379 x.
Proof. exact (h1). Qed.
Lemma lem1719345 (x : real) (h1 : term379 x) : term247 x.
Proof. exact (proj2 (@lem1719344 x h1)). Qed.
Lemma lem1719347 (x : real) (h1 : term379 x) : term246 x.
Proof. exact (proj2 (@lem1719345 x h1)). Qed.
Lemma lem1719350 (x : real) (h1 : term379 x) : term243.
Proof. exact (proj1 (@lem1719347 x h1)). Qed.
Lemma lem1719352 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719353 : term243 = term450.
Proof. exact (@lem1719352 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1719354 : term450 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1719355 : term243 = False.
Proof. exact (TRANS (@lem1719353) (@lem1719354)). Qed.
Lemma lem1719356 (x : real) (h1 : term379 x) : False.
Proof. exact (EQ_MP (@lem1719355) (@lem1719350 x h1)). Qed.
Lemma lem1719357 (x : real) (h1 : term401 x) : term401 x.
Proof. exact (h1). Qed.
Lemma lem1719358 (x : real) (h1 : term397 x) : term397 x.
Proof. exact (h1). Qed.
Lemma lem1719359 (x : real) (h1 : term397 x) : term396 x.
Proof. exact (proj2 (@lem1719358 x h1)). Qed.
Lemma lem1719361 (x : real) (h1 : term397 x) : term283 x.
Proof. exact (proj2 (@lem1719359 x h1)). Qed.
Lemma lem1719363 (x : real) (h1 : term397 x) : term243.
Proof. exact (proj2 (@lem1719361 x h1)). Qed.
Lemma lem1719366 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719367 : term243 = term450.
Proof. exact (@lem1719366 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1719368 : term450 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1719369 : term243 = False.
Proof. exact (TRANS (@lem1719367) (@lem1719368)). Qed.
Lemma lem1719370 (x : real) (h1 : term397 x) : False.
Proof. exact (EQ_MP (@lem1719369) (@lem1719363 x h1)). Qed.
Lemma lem1719371 (x : real) (h1 : term399 x) : term399 x.
Proof. exact (h1). Qed.
Lemma lem1719372 (x : real) (h1 : term399 x) : term398 x.
Proof. exact (proj2 (@lem1719371 x h1)). Qed.
Lemma lem1719374 (x : real) (h1 : term399 x) : term309 x.
Proof. exact (proj2 (@lem1719372 x h1)). Qed.
Lemma lem1719375 (x : real) (h1 : term399 x) : term154 x.
Proof. exact (proj1 (@lem1719372 x h1)). Qed.
Lemma lem1719376 (x : real) (h1 : term399 x) : term307 x.
Proof. exact (proj2 (@lem1719374 x h1)). Qed.
Lemma lem1719379 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719380 : term451 = term452.
Proof. exact (@lem1719379 (NUMERAL 0) term226). Qed.
Lemma lem1719381 : term453 = term224.
Proof. exact (@lem912803). Qed.
Lemma lem1719382 (h1 : term453 = term224) : term452 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term224 h1). Qed.
Lemma lem1719383 : (term453 = term224) = (term452 = True).
Proof. exact (prop_ext (fun h1 : term453 = term224 => @lem1719382 h1) (fun h1 : term452 = True => @lem1719381)). Qed.
Lemma lem1719384 : term452 = True.
Proof. exact (EQ_MP (@lem1719383) (@lem1719381)). Qed.
Lemma lem1719385 : term451 = True.
Proof. exact (TRANS (@lem1719380) (@lem1719384)). Qed.
Lemma lem1719386 : True = term451.
Proof. exact (SYM (@lem1719385)). Qed.
Lemma lem1719387 : term451.
Proof. exact (EQ_MP (@lem1719386) (@lem0)). Qed.
Lemma lem1719388 (x : real) (h1 : term399 x) : term488 x.
Proof. exact (conj (@lem1719387) (@lem1719375 x h1)). Qed.
Lemma lem1719390 (x : real) (y : real) : term475 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1719391 (x : real) : term489 x.
Proof. exact (@lem1719390 term227 x). Qed.
Lemma lem1719398 (x : real) (h1 : term399 x) : term490 x.
Proof. exact (@lem1719391 x (@lem1719388 x h1)). Qed.
Lemma lem1719400 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719401 : term457 = term458.
Proof. exact (@lem1719400 (NUMERAL 0) term73). Qed.
Lemma lem1719402 : term459 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1719403 (h1 : term459 = (BIT1 0)) : term458 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1719404 : (term459 = (BIT1 0)) = (term458 = True).
Proof. exact (prop_ext (fun h1 : term459 = (BIT1 0) => @lem1719403 h1) (fun h1 : term458 = True => @lem1719402)). Qed.
Lemma lem1719405 : term458 = True.
Proof. exact (EQ_MP (@lem1719404) (@lem1719402)). Qed.
Lemma lem1719406 : term457 = True.
Proof. exact (TRANS (@lem1719401) (@lem1719405)). Qed.
Lemma lem1719407 : True = term457.
Proof. exact (SYM (@lem1719406)). Qed.
Lemma lem1719408 : term457.
Proof. exact (EQ_MP (@lem1719407) (@lem0)). Qed.
Lemma lem1719409 (x : real) (h1 : term399 x) : term460 x.
Proof. exact (conj (@lem1719408) (@lem1719376 x h1)). Qed.
Lemma lem1719411 (x : real) (y : real) : term455 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1719412 (x : real) : term461 x.
Proof. exact (@lem1719411 term10 (term297 x)). Qed.
Lemma lem1719413 (x : real) (h1 : term399 x) : term462 x.
Proof. exact (@lem1719412 x (@lem1719409 x h1)). Qed.
Lemma lem1719414 (x : real) : (term463 x) = (term297 x).
Proof. exact (@lem1483460 (term297 x)). Qed.
Lemma lem1719415 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1719416 (x : real) : (term464 x) = (term306 x).
Proof. exact (MK_COMB (@lem1719415) (@lem1719414 x)). Qed.
Lemma lem1719417 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719418 (x : real) : (term462 x) = (term307 x).
Proof. exact (MK_COMB (@lem1719416 x) (@lem1719417)). Qed.
Lemma lem1719419 (x : real) (h1 : term399 x) : term307 x.
Proof. exact (EQ_MP (@lem1719418 x) (@lem1719413 x h1)). Qed.
Lemma lem1719420 (x : real) (h1 : term399 x) : term491 x.
Proof. exact (conj (@lem1719419 x h1) (@lem1719398 x h1)). Qed.
Lemma lem1719422 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1719423 (x : real) : term492 x.
Proof. exact (@lem1719422 (term297 x) (term230 x)). Qed.
Lemma lem1719424 (x : real) (h1 : term399 x) : term468 x.
Proof. exact (@lem1719423 x (@lem1719420 x h1)). Qed.
Lemma lem1719425 (x : real) : (term469 x) = (term470 x).
Proof. exact (@lem1483438 term294 term227 x). Qed.
Lemma lem1719427 (m : nat) : (term237 m) = term37.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1719428 : term471 = term37.
Proof. exact (@lem1719427 term226). Qed.
Lemma lem1719429 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1719430 : term472 = term39.
Proof. exact (MK_COMB (@lem1719429) (@lem1719428)). Qed.
Lemma lem1719431 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1719432 (x : real) : (term470 x) = (term40 x).
Proof. exact (MK_COMB (@lem1719430) (@lem1719431 x)). Qed.
Lemma lem1719433 (x : real) : (term469 x) = (term40 x).
Proof. exact (TRANS (@lem1719425 x) (@lem1719432 x)). Qed.
Lemma lem1719434 (x : real) : (term40 x) = term37.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1719435 (x : real) : (term469 x) = term37.
Proof. exact (TRANS (@lem1719433 x) (@lem1719434 x)). Qed.
Lemma lem1719436 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1719437 (x : real) : (term473 x) = term241.
Proof. exact (MK_COMB (@lem1719436) (@lem1719435 x)). Qed.
Lemma lem1719438 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719439 (x : real) : (term468 x) = term243.
Proof. exact (MK_COMB (@lem1719437 x) (@lem1719438)). Qed.
Lemma lem1719440 (x : real) (h1 : term399 x) : term243.
Proof. exact (EQ_MP (@lem1719439 x) (@lem1719424 x h1)). Qed.
Lemma lem1719442 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719443 : term243 = term450.
Proof. exact (@lem1719442 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1719444 : term450 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1719445 : term243 = False.
Proof. exact (TRANS (@lem1719443) (@lem1719444)). Qed.
Lemma lem1719446 (x : real) (h1 : term399 x) : False.
Proof. exact (EQ_MP (@lem1719445) (@lem1719440 x h1)). Qed.
Lemma lem1719447 (x : real) (h1 : term401 x) : False.
Proof. exact (or_elim (@lem1719357 x h1) (fun h0 : term397 x => @lem1719370 x h0) (fun h0 : term399 x => @lem1719446 x h0)). Qed.
Lemma lem1719448 (x : real) (h1 : term404 x) : False.
Proof. exact (or_elim (@lem1719343 x h1) (fun h0 : term379 x => @lem1719356 x h0) (fun h0 : term401 x => @lem1719447 x h0)). Qed.
Lemma lem1719449 (x : real) (h1 : term444 x) : term444 x.
Proof. exact (h1). Qed.
Lemma lem1719450 (x : real) (h1 : term413 x) : term413 x.
Proof. exact (h1). Qed.
Lemma lem1719451 (x : real) (h1 : term413 x) : term411 x.
Proof. exact (proj2 (@lem1719450 x h1)). Qed.
Lemma lem1719452 (x : real) (h1 : term413 x) : term154 x.
Proof. exact (proj1 (@lem1719450 x h1)). Qed.
Lemma lem1719453 (x : real) (h1 : term413 x) : term410 x.
Proof. exact (proj2 (@lem1719451 x h1)). Qed.
Lemma lem1719456 (x : real) (h1 : term413 x) : term67 x.
Proof. exact (proj1 (@lem1719453 x h1)). Qed.
Lemma lem1719458 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719459 : term457 = term458.
Proof. exact (@lem1719458 (NUMERAL 0) term73). Qed.
Lemma lem1719460 : term459 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1719461 (h1 : term459 = (BIT1 0)) : term458 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1719462 : (term459 = (BIT1 0)) = (term458 = True).
Proof. exact (prop_ext (fun h1 : term459 = (BIT1 0) => @lem1719461 h1) (fun h1 : term458 = True => @lem1719460)). Qed.
Lemma lem1719463 : term458 = True.
Proof. exact (EQ_MP (@lem1719462) (@lem1719460)). Qed.
Lemma lem1719464 : term457 = True.
Proof. exact (TRANS (@lem1719459) (@lem1719463)). Qed.
Lemma lem1719465 : True = term457.
Proof. exact (SYM (@lem1719464)). Qed.
Lemma lem1719466 : term457.
Proof. exact (EQ_MP (@lem1719465) (@lem0)). Qed.
Lemma lem1719467 (x : real) (h1 : term413 x) : term474 x.
Proof. exact (conj (@lem1719466) (@lem1719452 x h1)). Qed.
Lemma lem1719469 (x : real) (y : real) : term475 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1719470 (x : real) : term476 x.
Proof. exact (@lem1719469 term10 x). Qed.
Lemma lem1719471 (x : real) (h1 : term413 x) : term477 x.
Proof. exact (@lem1719470 x (@lem1719467 x h1)). Qed.
Lemma lem1719472 (x : real) : (term24 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1719473 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1719474 (x : real) : (term478 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1719473) (@lem1719472 x)). Qed.
Lemma lem1719475 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719476 (x : real) : (term477 x) = (term154 x).
Proof. exact (MK_COMB (@lem1719474 x) (@lem1719475)). Qed.
Lemma lem1719477 (x : real) (h1 : term413 x) : term154 x.
Proof. exact (EQ_MP (@lem1719476 x) (@lem1719471 x h1)). Qed.
Lemma lem1719479 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719480 : term457 = term458.
Proof. exact (@lem1719479 (NUMERAL 0) term73). Qed.
Lemma lem1719481 : term459 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1719482 (h1 : term459 = (BIT1 0)) : term458 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1719483 : (term459 = (BIT1 0)) = (term458 = True).
Proof. exact (prop_ext (fun h1 : term459 = (BIT1 0) => @lem1719482 h1) (fun h1 : term458 = True => @lem1719481)). Qed.
Lemma lem1719484 : term458 = True.
Proof. exact (EQ_MP (@lem1719483) (@lem1719481)). Qed.
Lemma lem1719485 : term457 = True.
Proof. exact (TRANS (@lem1719480) (@lem1719484)). Qed.
Lemma lem1719486 : True = term457.
Proof. exact (SYM (@lem1719485)). Qed.
Lemma lem1719487 : term457.
Proof. exact (EQ_MP (@lem1719486) (@lem0)). Qed.
Lemma lem1719488 (x : real) (h1 : term413 x) : term479 x.
Proof. exact (conj (@lem1719487) (@lem1719456 x h1)). Qed.
Lemma lem1719490 (x : real) (y : real) : term455 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1719491 (x : real) : term480 x.
Proof. exact (@lem1719490 term10 (term52 x)). Qed.
Lemma lem1719492 (x : real) (h1 : term413 x) : term481 x.
Proof. exact (@lem1719491 x (@lem1719488 x h1)). Qed.
Lemma lem1719493 (x : real) : (term482 x) = (term52 x).
Proof. exact (@lem1483460 (term52 x)). Qed.
Lemma lem1719494 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1719495 (x : real) : (term483 x) = (term66 x).
Proof. exact (MK_COMB (@lem1719494) (@lem1719493 x)). Qed.
Lemma lem1719496 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719497 (x : real) : (term481 x) = (term67 x).
Proof. exact (MK_COMB (@lem1719495 x) (@lem1719496)). Qed.
Lemma lem1719498 (x : real) (h1 : term413 x) : term67 x.
Proof. exact (EQ_MP (@lem1719497 x) (@lem1719492 x h1)). Qed.
Lemma lem1719499 (x : real) (h1 : term413 x) : term484 x.
Proof. exact (conj (@lem1719498 x h1) (@lem1719477 x h1)). Qed.
Lemma lem1719501 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1719502 (x : real) : term486 x.
Proof. exact (@lem1719501 (term52 x) x). Qed.
Lemma lem1719503 (x : real) (h1 : term413 x) : term272 x.
Proof. exact (@lem1719502 x (@lem1719499 x h1)). Qed.
Lemma lem1719504 (x : real) : (term274 x) = (term236 x).
Proof. exact (@lem1483440 term34 x). Qed.
Lemma lem1719506 (m : nat) : (term237 m) = term37.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1719507 : term238 = term37.
Proof. exact (@lem1719506 term73). Qed.
Lemma lem1719508 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1719509 : term239 = term39.
Proof. exact (MK_COMB (@lem1719508) (@lem1719507)). Qed.
Lemma lem1719510 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1719511 (x : real) : (term236 x) = (term40 x).
Proof. exact (MK_COMB (@lem1719509) (@lem1719510 x)). Qed.
Lemma lem1719512 (x : real) : (term274 x) = (term40 x).
Proof. exact (TRANS (@lem1719504 x) (@lem1719511 x)). Qed.
Lemma lem1719513 (x : real) : (term40 x) = term37.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1719514 (x : real) : (term274 x) = term37.
Proof. exact (TRANS (@lem1719512 x) (@lem1719513 x)). Qed.
Lemma lem1719515 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1719516 (x : real) : (term487 x) = term241.
Proof. exact (MK_COMB (@lem1719515) (@lem1719514 x)). Qed.
Lemma lem1719517 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719518 (x : real) : (term272 x) = term243.
Proof. exact (MK_COMB (@lem1719516 x) (@lem1719517)). Qed.
Lemma lem1719519 (x : real) (h1 : term413 x) : term243.
Proof. exact (EQ_MP (@lem1719518 x) (@lem1719503 x h1)). Qed.
Lemma lem1719521 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719522 : term243 = term450.
Proof. exact (@lem1719521 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1719523 : term450 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1719524 : term243 = False.
Proof. exact (TRANS (@lem1719522) (@lem1719523)). Qed.
Lemma lem1719525 (x : real) (h1 : term413 x) : False.
Proof. exact (EQ_MP (@lem1719524) (@lem1719519 x h1)). Qed.
Lemma lem1719526 (x : real) (h1 : term441 x) : term441 x.
Proof. exact (h1). Qed.
Lemma lem1719527 (x : real) (h1 : term425 x) : term425 x.
Proof. exact (h1). Qed.
Lemma lem1719528 (x : real) (h1 : term425 x) : term423 x.
Proof. exact (proj2 (@lem1719527 x h1)). Qed.
Lemma lem1719530 (x : real) (h1 : term425 x) : term430 x.
Proof. exact (proj2 (@lem1719528 x h1)). Qed.
Lemma lem1719532 (x : real) (h1 : term425 x) : term76 x.
Proof. exact (proj2 (@lem1719530 x h1)). Qed.
Lemma lem1719533 (x : real) (h1 : term425 x) : term119 x.
Proof. exact (proj1 (@lem1719530 x h1)). Qed.
Lemma lem1719535 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719536 : term457 = term458.
Proof. exact (@lem1719535 (NUMERAL 0) term73). Qed.
Lemma lem1719537 : term459 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1719538 (h1 : term459 = (BIT1 0)) : term458 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1719539 : (term459 = (BIT1 0)) = (term458 = True).
Proof. exact (prop_ext (fun h1 : term459 = (BIT1 0) => @lem1719538 h1) (fun h1 : term458 = True => @lem1719537)). Qed.
Lemma lem1719540 : term458 = True.
Proof. exact (EQ_MP (@lem1719539) (@lem1719537)). Qed.
Lemma lem1719541 : term457 = True.
Proof. exact (TRANS (@lem1719536) (@lem1719540)). Qed.
Lemma lem1719542 : True = term457.
Proof. exact (SYM (@lem1719541)). Qed.
Lemma lem1719543 : term457.
Proof. exact (EQ_MP (@lem1719542) (@lem0)). Qed.
Lemma lem1719544 (x : real) (h1 : term425 x) : term493 x.
Proof. exact (conj (@lem1719543) (@lem1719533 x h1)). Qed.
Lemma lem1719546 (x : real) (y : real) : term475 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1719547 (x : real) : term494 x.
Proof. exact (@lem1719546 term10 (term52 x)). Qed.
Lemma lem1719548 (x : real) (h1 : term425 x) : term495 x.
Proof. exact (@lem1719547 x (@lem1719544 x h1)). Qed.
Lemma lem1719549 (x : real) : (term482 x) = (term52 x).
Proof. exact (@lem1483460 (term52 x)). Qed.
Lemma lem1719550 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1719551 (x : real) : (term496 x) = (term118 x).
Proof. exact (MK_COMB (@lem1719550) (@lem1719549 x)). Qed.
Lemma lem1719552 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719553 (x : real) : (term495 x) = (term119 x).
Proof. exact (MK_COMB (@lem1719551 x) (@lem1719552)). Qed.
Lemma lem1719554 (x : real) (h1 : term425 x) : term119 x.
Proof. exact (EQ_MP (@lem1719553 x) (@lem1719548 x h1)). Qed.
Lemma lem1719556 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719557 : term457 = term458.
Proof. exact (@lem1719556 (NUMERAL 0) term73). Qed.
Lemma lem1719558 : term459 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1719559 (h1 : term459 = (BIT1 0)) : term458 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1719560 : (term459 = (BIT1 0)) = (term458 = True).
Proof. exact (prop_ext (fun h1 : term459 = (BIT1 0) => @lem1719559 h1) (fun h1 : term458 = True => @lem1719558)). Qed.
Lemma lem1719561 : term458 = True.
Proof. exact (EQ_MP (@lem1719560) (@lem1719558)). Qed.
Lemma lem1719562 : term457 = True.
Proof. exact (TRANS (@lem1719557) (@lem1719561)). Qed.
Lemma lem1719563 : True = term457.
Proof. exact (SYM (@lem1719562)). Qed.
Lemma lem1719564 : term457.
Proof. exact (EQ_MP (@lem1719563) (@lem0)). Qed.
Lemma lem1719565 (x : real) (h1 : term425 x) : term497 x.
Proof. exact (conj (@lem1719564) (@lem1719532 x h1)). Qed.
Lemma lem1719567 (x : real) (y : real) : term455 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1719568 (x : real) : term498 x.
Proof. exact (@lem1719567 term10 x). Qed.
Lemma lem1719569 (x : real) (h1 : term425 x) : term409 x.
Proof. exact (@lem1719568 x (@lem1719565 x h1)). Qed.
Lemma lem1719570 (x : real) : (term24 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1719571 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1719572 (x : real) : (term408 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1719571) (@lem1719570 x)). Qed.
Lemma lem1719573 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719574 (x : real) : (term409 x) = (term76 x).
Proof. exact (MK_COMB (@lem1719572 x) (@lem1719573)). Qed.
Lemma lem1719575 (x : real) (h1 : term425 x) : term76 x.
Proof. exact (EQ_MP (@lem1719574 x) (@lem1719569 x h1)). Qed.
Lemma lem1719576 (x : real) (h1 : term425 x) : term499 x.
Proof. exact (conj (@lem1719575 x h1) (@lem1719554 x h1)). Qed.
Lemma lem1719578 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1719579 (x : real) : term500 x.
Proof. exact (@lem1719578 x (term52 x)). Qed.
Lemma lem1719580 (x : real) (h1 : term425 x) : term242 x.
Proof. exact (@lem1719579 x (@lem1719576 x h1)). Qed.
Lemma lem1719581 (x : real) : (term235 x) = (term236 x).
Proof. exact (@lem1483442 term34 x). Qed.
Lemma lem1719583 (m : nat) : (term237 m) = term37.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1719584 : term238 = term37.
Proof. exact (@lem1719583 term73). Qed.
Lemma lem1719585 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1719586 : term239 = term39.
Proof. exact (MK_COMB (@lem1719585) (@lem1719584)). Qed.
Lemma lem1719587 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1719588 (x : real) : (term236 x) = (term40 x).
Proof. exact (MK_COMB (@lem1719586) (@lem1719587 x)). Qed.
Lemma lem1719589 (x : real) : (term235 x) = (term40 x).
Proof. exact (TRANS (@lem1719581 x) (@lem1719588 x)). Qed.
Lemma lem1719590 (x : real) : (term40 x) = term37.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1719591 (x : real) : (term235 x) = term37.
Proof. exact (TRANS (@lem1719589 x) (@lem1719590 x)). Qed.
Lemma lem1719592 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1719593 (x : real) : (term240 x) = term241.
Proof. exact (MK_COMB (@lem1719592) (@lem1719591 x)). Qed.
Lemma lem1719594 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719595 (x : real) : (term242 x) = term243.
Proof. exact (MK_COMB (@lem1719593 x) (@lem1719594)). Qed.
Lemma lem1719596 (x : real) (h1 : term425 x) : term243.
Proof. exact (EQ_MP (@lem1719595 x) (@lem1719580 x h1)). Qed.
Lemma lem1719598 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719599 : term243 = term450.
Proof. exact (@lem1719598 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1719600 : term450 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1719601 : term243 = False.
Proof. exact (TRANS (@lem1719599) (@lem1719600)). Qed.
Lemma lem1719602 (x : real) (h1 : term425 x) : False.
Proof. exact (EQ_MP (@lem1719601) (@lem1719596 x h1)). Qed.
Lemma lem1719603 (x : real) (h1 : term440 x) : term440 x.
Proof. exact (h1). Qed.
Lemma lem1719604 (x : real) (h1 : term440 x) : term439 x.
Proof. exact (proj2 (@lem1719603 x h1)). Qed.
Lemma lem1719606 (x : real) (h1 : term440 x) : term438 x.
Proof. exact (proj2 (@lem1719604 x h1)). Qed.
Lemma lem1719607 (x : real) (h1 : term440 x) : term154 x.
Proof. exact (proj1 (@lem1719604 x h1)). Qed.
Lemma lem1719608 (x : real) (h1 : term440 x) : term67 x.
Proof. exact (proj2 (@lem1719606 x h1)). Qed.
Lemma lem1719611 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719612 : term457 = term458.
Proof. exact (@lem1719611 (NUMERAL 0) term73). Qed.
Lemma lem1719613 : term459 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1719614 (h1 : term459 = (BIT1 0)) : term458 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1719615 : (term459 = (BIT1 0)) = (term458 = True).
Proof. exact (prop_ext (fun h1 : term459 = (BIT1 0) => @lem1719614 h1) (fun h1 : term458 = True => @lem1719613)). Qed.
Lemma lem1719616 : term458 = True.
Proof. exact (EQ_MP (@lem1719615) (@lem1719613)). Qed.
Lemma lem1719617 : term457 = True.
Proof. exact (TRANS (@lem1719612) (@lem1719616)). Qed.
Lemma lem1719618 : True = term457.
Proof. exact (SYM (@lem1719617)). Qed.
Lemma lem1719619 : term457.
Proof. exact (EQ_MP (@lem1719618) (@lem0)). Qed.
Lemma lem1719620 (x : real) (h1 : term440 x) : term474 x.
Proof. exact (conj (@lem1719619) (@lem1719607 x h1)). Qed.
Lemma lem1719622 (x : real) (y : real) : term475 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1719623 (x : real) : term476 x.
Proof. exact (@lem1719622 term10 x). Qed.
Lemma lem1719624 (x : real) (h1 : term440 x) : term477 x.
Proof. exact (@lem1719623 x (@lem1719620 x h1)). Qed.
Lemma lem1719625 (x : real) : (term24 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1719626 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1719627 (x : real) : (term478 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1719626) (@lem1719625 x)). Qed.
Lemma lem1719628 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719629 (x : real) : (term477 x) = (term154 x).
Proof. exact (MK_COMB (@lem1719627 x) (@lem1719628)). Qed.
Lemma lem1719630 (x : real) (h1 : term440 x) : term154 x.
Proof. exact (EQ_MP (@lem1719629 x) (@lem1719624 x h1)). Qed.
Lemma lem1719632 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719633 : term457 = term458.
Proof. exact (@lem1719632 (NUMERAL 0) term73). Qed.
Lemma lem1719634 : term459 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1719635 (h1 : term459 = (BIT1 0)) : term458 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1719636 : (term459 = (BIT1 0)) = (term458 = True).
Proof. exact (prop_ext (fun h1 : term459 = (BIT1 0) => @lem1719635 h1) (fun h1 : term458 = True => @lem1719634)). Qed.
Lemma lem1719637 : term458 = True.
Proof. exact (EQ_MP (@lem1719636) (@lem1719634)). Qed.
Lemma lem1719638 : term457 = True.
Proof. exact (TRANS (@lem1719633) (@lem1719637)). Qed.
Lemma lem1719639 : True = term457.
Proof. exact (SYM (@lem1719638)). Qed.
Lemma lem1719640 : term457.
Proof. exact (EQ_MP (@lem1719639) (@lem0)). Qed.
Lemma lem1719641 (x : real) (h1 : term440 x) : term479 x.
Proof. exact (conj (@lem1719640) (@lem1719608 x h1)). Qed.
Lemma lem1719643 (x : real) (y : real) : term455 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1719644 (x : real) : term480 x.
Proof. exact (@lem1719643 term10 (term52 x)). Qed.
Lemma lem1719645 (x : real) (h1 : term440 x) : term481 x.
Proof. exact (@lem1719644 x (@lem1719641 x h1)). Qed.
Lemma lem1719646 (x : real) : (term482 x) = (term52 x).
Proof. exact (@lem1483460 (term52 x)). Qed.
Lemma lem1719647 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1719648 (x : real) : (term483 x) = (term66 x).
Proof. exact (MK_COMB (@lem1719647) (@lem1719646 x)). Qed.
Lemma lem1719649 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719650 (x : real) : (term481 x) = (term67 x).
Proof. exact (MK_COMB (@lem1719648 x) (@lem1719649)). Qed.
Lemma lem1719651 (x : real) (h1 : term440 x) : term67 x.
Proof. exact (EQ_MP (@lem1719650 x) (@lem1719645 x h1)). Qed.
Lemma lem1719652 (x : real) (h1 : term440 x) : term484 x.
Proof. exact (conj (@lem1719651 x h1) (@lem1719630 x h1)). Qed.
Lemma lem1719654 (x : real) (y : real) : term485 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1719655 (x : real) : term486 x.
Proof. exact (@lem1719654 (term52 x) x). Qed.
Lemma lem1719656 (x : real) (h1 : term440 x) : term272 x.
Proof. exact (@lem1719655 x (@lem1719652 x h1)). Qed.
Lemma lem1719657 (x : real) : (term274 x) = (term236 x).
Proof. exact (@lem1483440 term34 x). Qed.
Lemma lem1719659 (m : nat) : (term237 m) = term37.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1719660 : term238 = term37.
Proof. exact (@lem1719659 term73). Qed.
Lemma lem1719661 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1719662 : term239 = term39.
Proof. exact (MK_COMB (@lem1719661) (@lem1719660)). Qed.
Lemma lem1719663 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1719664 (x : real) : (term236 x) = (term40 x).
Proof. exact (MK_COMB (@lem1719662) (@lem1719663 x)). Qed.
Lemma lem1719665 (x : real) : (term274 x) = (term40 x).
Proof. exact (TRANS (@lem1719657 x) (@lem1719664 x)). Qed.
Lemma lem1719666 (x : real) : (term40 x) = term37.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1719667 (x : real) : (term274 x) = term37.
Proof. exact (TRANS (@lem1719665 x) (@lem1719666 x)). Qed.
Lemma lem1719668 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1719669 (x : real) : (term487 x) = term241.
Proof. exact (MK_COMB (@lem1719668) (@lem1719667 x)). Qed.
Lemma lem1719670 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1719671 (x : real) : (term272 x) = term243.
Proof. exact (MK_COMB (@lem1719669 x) (@lem1719670)). Qed.
Lemma lem1719672 (x : real) (h1 : term440 x) : term243.
Proof. exact (EQ_MP (@lem1719671 x) (@lem1719656 x h1)). Qed.
Lemma lem1719674 (n : nat) (m : nat) : (term449 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1719675 : term243 = term450.
Proof. exact (@lem1719674 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1719676 : term450 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1719677 : term243 = False.
Proof. exact (TRANS (@lem1719675) (@lem1719676)). Qed.
Lemma lem1719678 (x : real) (h1 : term440 x) : False.
Proof. exact (EQ_MP (@lem1719677) (@lem1719672 x h1)). Qed.
Lemma lem1719679 (x : real) (h1 : term441 x) : False.
Proof. exact (or_elim (@lem1719526 x h1) (fun h0 : term425 x => @lem1719602 x h0) (fun h0 : term440 x => @lem1719678 x h0)). Qed.
Lemma lem1719680 (x : real) (h1 : term444 x) : False.
Proof. exact (or_elim (@lem1719449 x h1) (fun h0 : term413 x => @lem1719525 x h0) (fun h0 : term441 x => @lem1719679 x h0)). Qed.
Lemma lem1719681 (x : real) (h1 : term446 x) : False.
Proof. exact (or_elim (@lem1719342 x h1) (fun h0 : term404 x => @lem1719448 x h0) (fun h0 : term444 x => @lem1719680 x h0)). Qed.
Lemma lem1719682 (x : real) (h1 : term448 x) : False.
Proof. exact (or_elim (@lem1719127 x h1) (fun h0 : term377 x => @lem1719341 x h0) (fun h0 : term446 x => @lem1719681 x h0)). Qed.
Lemma lem1719683 (x : real) (h1 : term215 x) : term215 x.
Proof. exact (h1). Qed.
Lemma lem1719684 (x : real) (h1 : term215 x) : term448 x.
Proof. exact (EQ_MP (@lem1719126 x) (@lem1719683 x h1)). Qed.
Lemma lem1719685 (x : real) (h1 : term215 x) : (term448 x) = False.
Proof. exact (prop_ext (fun h2 : term448 x => @lem1719682 x h2) (fun h2 : False => @lem1719684 x h1)). Qed.
Lemma lem1719686 (x : real) (h1 : term215 x) : False.
Proof. exact (EQ_MP (@lem1719685 x h1) (@lem1719684 x h1)). Qed.
Lemma lem1719687 (x : real) (h1 : term18 x) : term18 x.
Proof. exact (h1). Qed.
Lemma lem1719688 (x : real) (h1 : term18 x) : term215 x.
Proof. exact (EQ_MP (@lem1718329 x) (@lem1719687 x h1)). Qed.
Lemma lem1719689 (x : real) (h1 : term18 x) : (term215 x) = False.
Proof. exact (prop_ext (fun h2 : term215 x => @lem1719686 x h2) (fun h2 : False => @lem1719688 x h1)). Qed.
Lemma lem1719690 (x : real) (h1 : term18 x) : False.
Proof. exact (EQ_MP (@lem1719689 x h1) (@lem1719688 x h1)). Qed.
Lemma lem1719691 (x : real) : term501 x.
Proof. exact (fun h0 : term18 x => @lem1719690 x h0). Qed.
Lemma lem1719692 (x : real) : term502 x.
Proof. exact (@lem1386578 ((term5 x) = (real_abs x))). Qed.
Lemma lem1719693 (x : real) : (term5 x) = (real_abs x).
Proof. exact (@lem1719692 x (@lem1719691 x)). Qed.
Lemma lem1719694 (x : real) : (term4 x) = (real_abs x).
Proof. exact (EQ_MP (@lem1717563 x) (@lem1719693 x)). Qed.
Lemma lem1719699 : term503.
Proof. exact (fun x : real => @lem1719694 x). Qed.
