Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_MONO_LT_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_LTE_TRANS_spec.
Require Import REAL_NOT_LE_spec.
Require Import REAL_POW_LT2_REV_spec.
Require Import SQRT_LE_0_spec.
Require Import SQRT_NEG_spec.
Require Import SQRT_WORKS_GEN_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm1482680_spec.
Require Import thm1482981_spec.
Require Import thm1483436_spec.
Require Import thm1483438_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483523_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483531_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1842_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Lemma lem1948490 (x : real) : term0 x.
Proof. exact (@lem1921835 x). Qed.
Lemma lem1948491 (x : real) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1948495 (y : real) (x : real) (h1 : (term3 x y) = (real_lt y x)) : (term3 x y) = (real_lt y x).
Proof. exact (h1). Qed.
Lemma lem1948496 (y : real) (x : real) (h1 : (term3 x y) = (real_lt y x)) : (real_lt y x) = (term3 x y).
Proof. exact (SYM (@lem1948495 y x h1)). Qed.
Lemma lem1948497 (x : real) (y : real) (h1 : (real_lt y x) = (term3 x y)) : (real_lt y x) = (term3 x y).
Proof. exact (h1). Qed.
Lemma lem1948498 (x : real) (y : real) (h1 : (real_lt y x) = (term3 x y)) : (term3 x y) = (real_lt y x).
Proof. exact (SYM (@lem1948497 x y h1)). Qed.
Lemma lem1948499 (x : real) (y : real) : ((term3 x y) = (real_lt y x)) = ((real_lt y x) = (term3 x y)).
Proof. exact (prop_ext (fun h1 : (term3 x y) = (real_lt y x) => @lem1948496 y x h1) (fun h1 : (real_lt y x) = (term3 x y) => @lem1948498 x y h1)). Qed.
Lemma lem1948500 (x : real) : (term4 x) = (term5 x).
Proof. exact (fun_ext (fun y : real => @lem1948499 x y)). Qed.
Lemma lem1948501 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1948502 (x : real) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem1948501) (@lem1948500 x)). Qed.
Lemma lem1948503 : term8 = term9.
Proof. exact (fun_ext (fun x : real => @lem1948502 x)). Qed.
Lemma lem1948504 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1948505 : term10 = term11.
Proof. exact (MK_COMB (@lem1948504) (@lem1948503)). Qed.
Lemma lem1948506 : term11.
Proof. exact (EQ_MP (@lem1948505) (@lem1495933)). Qed.
Lemma lem1948507 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1948508 (x : real) (h1 : term12) : term13 x.
Proof. exact (@lem1948507 h1 x). Qed.
Lemma lem1948509 (x : real) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1948510 (x : real) (h1 : term12) : term14 x.
Proof. exact (EQ_MP (@lem1948509 x) (@lem1948508 x h1)). Qed.
Lemma lem1948511 (x : real) (y : real) (h1 : term12) : term15 x y.
Proof. exact (@lem1948510 x h1 y). Qed.
Lemma lem1948512 (y : real) (x : real) : (term15 x y) = (term16 y x).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1948513 (y : real) (x : real) (h1 : term12) : term16 y x.
Proof. exact (EQ_MP (@lem1948512 y x) (@lem1948511 x y h1)). Qed.
Lemma lem1948514 (y : real) (x : real) (z : real) (h1 : term12) : term17 y x z.
Proof. exact (@lem1948513 y x h1 z). Qed.
Lemma lem1948515 (y : real) (x : real) (z : real) : (term17 y x z) = (term18 y x z).
Proof. exact (eq_refl (term17 y x z)). Qed.
Lemma lem1948516 (y : real) (x : real) (z : real) (h1 : term12) : term18 y x z.
Proof. exact (EQ_MP (@lem1948515 y x z) (@lem1948514 y x z h1)). Qed.
Lemma lem1948517 (x : real) (y : real) (z : real) (h1 : term19 x y z) : term19 x y z.
Proof. exact (h1). Qed.
Lemma lem1948518 (x : real) (y : real) (z : real) (h1 : term12) (h2 : term19 x y z) : real_lt x z.
Proof. exact (@lem1948516 y x z h1 (@lem1948517 x y z h2)). Qed.
Lemma lem1948519 (x : real) (y : real) (z : real) (h1 : term19 x y z) : term20 x z.
Proof. exact (fun h0 : term12 => @lem1948518 x y z h0 h1). Qed.
Lemma lem1948520 (x : real) (z : real) (h1 : term21 x z) : term21 x z.
Proof. exact (h1). Qed.
Lemma lem1948521 (x : real) (z : real) (h1 : term21 x z) : term20 x z.
Proof. exact (ex_elim (@lem1948520 x z h1) (fun y : real => fun h0 : term22 x z y => @lem1948519 x y z h0)). Qed.
Lemma lem1948522 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1948523 (x : real) (z : real) (h1 : term12) (h2 : term21 x z) : real_lt x z.
Proof. exact (@lem1948521 x z h2 (@lem1948522 h1)). Qed.
Lemma lem1948524 (x : real) (z : real) (h1 : term12) : term23 x z.
Proof. exact (fun h0 : term21 x z => @lem1948523 x z h1 h0). Qed.
Lemma lem1948525 (x : real) (h1 : term12) : term24 x.
Proof. exact (fun z : real => @lem1948524 x z h1). Qed.
Lemma lem1948526 (h1 : term12) : term25.
Proof. exact (fun x : real => @lem1948525 x h1). Qed.
Lemma lem1948527 : term26.
Proof. exact (fun h0 : term12 => @lem1948526 h0). Qed.
Lemma lem1948528 : term25.
Proof. exact (@lem1948527 (@lem1370312)). Qed.
Lemma lem1948529 (x : real) : term27 x.
Proof. exact (@lem1948528 x). Qed.
Lemma lem1948530 (x : real) : (term27 x) = (term24 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1948531 (x : real) : term24 x.
Proof. exact (EQ_MP (@lem1948530 x) (@lem1948529 x)). Qed.
Lemma lem1948532 (x : real) (z : real) : term28 x z.
Proof. exact (@lem1948531 x z). Qed.
Lemma lem1948533 (x : real) (z : real) : (term28 x z) = (term23 x z).
Proof. exact (eq_refl (term28 x z)). Qed.
Lemma lem1948535 (y : real) : term29 y.
Proof. exact (@lem9784 (term30 y)). Qed.
Lemma lem1948536 (y : real) : (term29 y) = (term31 y).
Proof. exact (eq_refl (term29 y)). Qed.
Lemma lem1948537 (y : real) : term31 y.
Proof. exact (EQ_MP (@lem1948536 y) (@lem1948535 y)). Qed.
Lemma lem1948538 (y : real) (h1 : term30 y) : term30 y.
Proof. exact (h1). Qed.
Lemma lem1948539 (y : real) (h1 : term32 y) : term32 y.
Proof. exact (h1). Qed.
Lemma lem1948540 (x : real) : term29 x.
Proof. exact (@lem9784 (term30 x)). Qed.
Lemma lem1948541 (x : real) : (term29 x) = (term31 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1948542 (x : real) : term31 x.
Proof. exact (EQ_MP (@lem1948541 x) (@lem1948540 x)). Qed.
Lemma lem1948543 (x : real) (h1 : term30 x) : term30 x.
Proof. exact (h1). Qed.
Lemma lem1948544 (x : real) (h1 : term32 x) : term32 x.
Proof. exact (h1). Qed.
Lemma lem1948545 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1948546 (n : nat) (h1 : term33) : term34 n.
Proof. exact (@lem1948545 h1 n). Qed.
Lemma lem1948547 (n : nat) : (term34 n) = (term35 n).
Proof. exact (eq_refl (term34 n)). Qed.
Lemma lem1948548 (n : nat) (h1 : term33) : term35 n.
Proof. exact (EQ_MP (@lem1948547 n) (@lem1948546 n h1)). Qed.
Lemma lem1948549 (n : nat) (x : real) (h1 : term33) : term36 n x.
Proof. exact (@lem1948548 n h1 x). Qed.
Lemma lem1948550 (n : nat) (x : real) : (term36 n x) = (term37 n x).
Proof. exact (eq_refl (term36 n x)). Qed.
Lemma lem1948551 (n : nat) (x : real) (h1 : term33) : term37 n x.
Proof. exact (EQ_MP (@lem1948550 n x) (@lem1948549 n x h1)). Qed.
Lemma lem1948552 (n : nat) (x : real) (y : real) (h1 : term33) : term38 n x y.
Proof. exact (@lem1948551 n x h1 y). Qed.
Lemma lem1948553 (n : nat) (x : real) (y : real) : (term38 n x y) = (term39 n x y).
Proof. exact (eq_refl (term38 n x y)). Qed.
Lemma lem1948554 (n : nat) (x : real) (y : real) (h1 : term33) : term39 n x y.
Proof. exact (EQ_MP (@lem1948553 n x y) (@lem1948552 n x y h1)). Qed.
Lemma lem1948555 (x : real) (y : real) (n : nat) (h1 : term40 x y n) : term40 x y n.
Proof. exact (h1). Qed.
Lemma lem1948556 (x : real) (y : real) (n : nat) (h1 : term33) (h2 : term40 x y n) : real_lt x y.
Proof. exact (@lem1948554 n x y h1 (@lem1948555 x y n h2)). Qed.
Lemma lem1948557 (x : real) (y : real) (n : nat) (h1 : term40 x y n) : term41 x y.
Proof. exact (fun h0 : term33 => @lem1948556 x y n h0 h1). Qed.
Lemma lem1948558 (x : real) (y : real) (h1 : term42 x y) : term42 x y.
Proof. exact (h1). Qed.
Lemma lem1948559 (x : real) (y : real) (h1 : term42 x y) : term41 x y.
Proof. exact (ex_elim (@lem1948558 x y h1) (fun n : nat => fun h0 : term43 x y n => @lem1948557 x y n h0)). Qed.
Lemma lem1948560 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1948561 (x : real) (y : real) (h1 : term33) (h2 : term42 x y) : real_lt x y.
Proof. exact (@lem1948559 x y h2 (@lem1948560 h1)). Qed.
Lemma lem1948562 (x : real) (y : real) (h1 : term33) : term44 x y.
Proof. exact (fun h0 : term42 x y => @lem1948561 x y h1 h0). Qed.
Lemma lem1948563 (x : real) (h1 : term33) : term45 x.
Proof. exact (fun y : real => @lem1948562 x y h1). Qed.
Lemma lem1948564 (h1 : term33) : term46.
Proof. exact (fun x : real => @lem1948563 x h1). Qed.
Lemma lem1948565 : term47.
Proof. exact (fun h0 : term33 => @lem1948564 h0). Qed.
Lemma lem1948566 : term46.
Proof. exact (@lem1948565 (@lem1651996)). Qed.
Lemma lem1948567 (x : real) : term48 x.
Proof. exact (@lem1948566 x). Qed.
Lemma lem1948568 (x : real) : (term48 x) = (term45 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1948569 (x : real) : term45 x.
Proof. exact (EQ_MP (@lem1948568 x) (@lem1948567 x)). Qed.
Lemma lem1948570 (x : real) (y : real) : term49 x y.
Proof. exact (@lem1948569 x y). Qed.
Lemma lem1948571 (x : real) (y : real) : (term49 x y) = (term44 x y).
Proof. exact (eq_refl (term49 x y)). Qed.
Lemma lem1948573 (h1 : term50) : term50.
Proof. exact (h1). Qed.
Lemma lem1948574 (x : real) (y : real) (h1 : term51 x y) : term51 x y.
Proof. exact (h1). Qed.
Lemma lem1948575 (x : real) (y : real) (h1 : real_lt x y) : real_lt x y.
Proof. exact (h1). Qed.
Lemma lem1948576 (x : real) (h1 : term30 x) : term30 x.
Proof. exact (h1). Qed.
Lemma lem1948578 (x : real) (y : real) : term44 x y.
Proof. exact (EQ_MP (@lem1948571 x y) (@lem1948570 x y)). Qed.
Lemma lem1948579 (x : real) (y : real) : term52 x y.
Proof. exact (@lem1948578 (sqrt x) (sqrt y)). Qed.
Lemma lem1948580 (x : real) : term53 x.
Proof. exact (@lem1948346 x). Qed.
Lemma lem1948581 (x : real) : (term53 x) = ((term54 x) = (term30 x)).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1948583 (x : real) : term55 x.
Proof. exact (@lem1919069 x). Qed.
Lemma lem1948584 (x : real) : (term55 x) = (term56 x).
Proof. exact (eq_refl (term55 x)). Qed.
Lemma lem1948585 (x : real) : term56 x.
Proof. exact (EQ_MP (@lem1948584 x) (@lem1948583 x)). Qed.
Lemma lem1948595 (x : real) : (term54 x) = (term30 x).
Proof. exact (EQ_MP (@lem1948581 x) (@lem1948580 x)). Qed.
Lemma lem1948596 (y : real) : (term54 y) = (term30 y).
Proof. exact (@lem1948595 y). Qed.
Lemma lem1948597 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1948598 (y : real) : (term57 y) = (term58 y).
Proof. exact (MK_COMB (@lem1948597) (@lem1948596 y)). Qed.
Lemma lem1948600 (x : real) : (term59 x) = (real_abs x).
Proof. exact (proj2 (@lem1948585 x)). Qed.
Lemma lem1948601 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1948602 (x : real) : (term60 x) = (term61 x).
Proof. exact (MK_COMB (@lem1948601) (@lem1948600 x)). Qed.
Lemma lem1948604 (x : real) : (term59 x) = (real_abs x).
Proof. exact (proj2 (@lem1948585 x)). Qed.
Lemma lem1948605 (y : real) : (term59 y) = (real_abs y).
Proof. exact (@lem1948604 y). Qed.
Lemma lem1948606 (x : real) (y : real) : (term62 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1948602 x) (@lem1948605 y)). Qed.
Lemma lem1948607 (x : real) (y : real) : (term64 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1948598 y) (@lem1948606 x y)). Qed.
Lemma lem1948610 (x : real) (y : real) : (term65 x y) = (term64 x y).
Proof. exact (SYM (@lem1948607 x y)). Qed.
Lemma lem1948628 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (@lem17045 (term30 y) (term63 x y)). Qed.
Lemma lem1948630 (x : real) (y : real) : (term68 x y) = (term68 x y).
Proof. exact (eq_refl (term68 x y)). Qed.
Lemma lem1948631 (x : real) (y : real) : (term69 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem1948630 x y) (@lem1948628 x y)). Qed.
Lemma lem1948632 (x : real) (y : real) : (term71 x y) = (term69 x y).
Proof. exact (@lem17362 (real_lt x y) (term65 x y)). Qed.
Lemma lem1948633 (x : real) (y : real) : (term71 x y) = (term70 x y).
Proof. exact (TRANS (@lem1948632 x y) (@lem1948631 x y)). Qed.
Lemma lem1948635 (x : real) : (term58 x) = (term58 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1948636 (x : real) (y : real) : (term72 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem1948635 x) (@lem1948633 x y)). Qed.
Lemma lem1948637 (x : real) (y : real) : (term74 x y) = (term72 x y).
Proof. exact (@lem17362 (term30 x) (term75 x y)). Qed.
Lemma lem1948657 (x : real) (y : real) : (term74 x y) = (term73 x y).
Proof. exact (TRANS (@lem1948637 x y) (@lem1948636 x y)). Qed.
Lemma lem1948658 (x : real) : (term30 x) = (term76 x).
Proof. exact (@lem1483523 x term77). Qed.
Lemma lem1948664 (x : real) : (term78 x) = (term79 x).
Proof. exact (@lem1483519 x term77). Qed.
Lemma lem1948666 (x : nat) : (term80 x) = term77.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1948667 : term81 = term77.
Proof. exact (@lem1948666 term82). Qed.
Lemma lem1948668 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1948669 (x : real) : (term79 x) = (term83 x).
Proof. exact (MK_COMB (@lem1948668 x) (@lem1948667)). Qed.
Lemma lem1948670 (x : real) : (term83 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1948671 (x : real) : (term79 x) = x.
Proof. exact (TRANS (@lem1948669 x) (@lem1948670 x)). Qed.
Lemma lem1948673 (x : real) : (term78 x) = x.
Proof. exact (TRANS (@lem1948664 x) (@lem1948671 x)). Qed.
Lemma lem1948674 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1948675 (x : real) : (term84 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1948674) (@lem1948673 x)). Qed.
Lemma lem1948676 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1948677 (x : real) : (term76 x) = (term85 x).
Proof. exact (MK_COMB (@lem1948675 x) (@lem1948676)). Qed.
Lemma lem1948678 (x : real) : (term30 x) = (term85 x).
Proof. exact (TRANS (@lem1948658 x) (@lem1948677 x)). Qed.
Lemma lem1948679 (y : real) (x : real) : (real_lt x y) = (term86 y x).
Proof. exact (@lem1483521 y x). Qed.
Lemma lem1948685 (y : real) (x : real) : (real_sub y x) = (term87 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1948690 (x : real) (y : real) : (term87 y x) = (term88 x y).
Proof. exact (@lem1483488 (term89 x) y). Qed.
Lemma lem1948692 (x : real) (y : real) : (real_sub y x) = (term88 x y).
Proof. exact (TRANS (@lem1948685 y x) (@lem1948690 x y)). Qed.
Lemma lem1948693 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1948694 (x : real) (y : real) : (term90 y x) = (term91 x y).
Proof. exact (MK_COMB (@lem1948693) (@lem1948692 x y)). Qed.
Lemma lem1948695 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1948696 (x : real) (y : real) : (term86 y x) = (term92 x y).
Proof. exact (MK_COMB (@lem1948694 x y) (@lem1948695)). Qed.
Lemma lem1948697 (x : real) (y : real) : (real_lt x y) = (term92 x y).
Proof. exact (TRANS (@lem1948679 y x) (@lem1948696 x y)). Qed.
Lemma lem1948698 (y : real) : (term32 y) = (term93 y).
Proof. exact (@lem1483533 term77 y). Qed.
Lemma lem1948704 (y : real) : (term94 y) = (term95 y).
Proof. exact (@lem1483519 term77 y). Qed.
Lemma lem1948709 (y : real) : (term95 y) = (term89 y).
Proof. exact (@lem1483448 (term89 y)). Qed.
Lemma lem1948711 (y : real) : (term94 y) = (term89 y).
Proof. exact (TRANS (@lem1948704 y) (@lem1948709 y)). Qed.
Lemma lem1948712 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1948713 (y : real) : (term96 y) = (term97 y).
Proof. exact (MK_COMB (@lem1948712) (@lem1948711 y)). Qed.
Lemma lem1948714 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1948715 (y : real) : (term93 y) = (term98 y).
Proof. exact (MK_COMB (@lem1948713 y) (@lem1948714)). Qed.
Lemma lem1948716 (y : real) : (term32 y) = (term98 y).
Proof. exact (TRANS (@lem1948698 y) (@lem1948715 y)). Qed.
Lemma lem1948717 (x : real) (y : real) : (term99 x y) = (term100 x y).
Proof. exact (@lem1483531 (real_abs x) (real_abs y)). Qed.
Lemma lem1948730 (x : real) (y : real) : (term101 x y) = (term102 x y).
Proof. exact (@lem1483519 (real_abs x) (real_abs y)). Qed.
Lemma lem1948731 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1948732 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1948731) (@lem1948730 x y)). Qed.
Lemma lem1948733 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1948734 (x : real) (y : real) : (term100 x y) = (term105 x y).
Proof. exact (MK_COMB (@lem1948732 x y) (@lem1948733)). Qed.
Lemma lem1948735 (x : real) (y : real) : (term99 x y) = (term105 x y).
Proof. exact (TRANS (@lem1948717 x y) (@lem1948734 x y)). Qed.
Lemma lem1948736 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1948737 (y : real) : (term106 y) = (term107 y).
Proof. exact (MK_COMB (@lem1948736) (@lem1948716 y)). Qed.
Lemma lem1948738 (x : real) (y : real) : (term67 x y) = (term108 x y).
Proof. exact (MK_COMB (@lem1948737 y) (@lem1948735 x y)). Qed.
Lemma lem1948739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1948740 (x : real) (y : real) : (term68 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1948739) (@lem1948697 x y)). Qed.
Lemma lem1948741 (x : real) (y : real) : (term70 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1948740 x y) (@lem1948738 x y)). Qed.
Lemma lem1948742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1948743 (x : real) : (term58 x) = (term111 x).
Proof. exact (MK_COMB (@lem1948742) (@lem1948678 x)). Qed.
Lemma lem1948744 (x : real) (y : real) : (term73 x y) = (term112 x y).
Proof. exact (MK_COMB (@lem1948743 x) (@lem1948741 x y)). Qed.
Lemma lem1948751 (x : real) (y : real) : (term74 x y) = (term112 x y).
Proof. exact (TRANS (@lem1948657 x y) (@lem1948744 x y)). Qed.
Lemma lem1948768 (x : real) (y : real) : (term110 x y) = (term113 x y).
Proof. exact (@lem19158 (term98 y) (term92 x y) (term105 x y)). Qed.
Lemma lem1948771 (x : real) : (term111 x) = (term111 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem1948772 (x : real) (y : real) : (term112 x y) = (term114 x y).
Proof. exact (MK_COMB (@lem1948771 x) (@lem1948768 x y)). Qed.
Lemma lem1948779 (x : real) (y : real) : (term114 x y) = (term115 x y).
Proof. exact (@lem19158 (term116 x y) (term85 x) (term117 x y)). Qed.
Lemma lem1948780 (x : real) (y : real) : (term112 x y) = (term115 x y).
Proof. exact (TRANS (@lem1948772 x y) (@lem1948779 x y)). Qed.
Lemma lem1948781 (x : real) (y : real) : (term74 x y) = (term115 x y).
Proof. exact (TRANS (@lem1948751 x y) (@lem1948780 x y)). Qed.
Lemma lem1948786 (a : real) (x : real) (r : real) : (term118 a x r) = (term119 a x r).
Proof. exact (proj1 (@lem1482680 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1948787 (x : real) (y : real) : (term105 x y) = (term120 x y).
Proof. exact (@lem1948786 (real_abs x) y term77). Qed.
Lemma lem1948794 (y : real) : (term121 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1948797 (x : real) : (term122 x) = (term122 x).
Proof. exact (eq_refl (term122 x)). Qed.
Lemma lem1948798 (x : real) (y : real) : (term123 x y) = (term124 x y).
Proof. exact (MK_COMB (@lem1948797 x) (@lem1948794 y)). Qed.
Lemma lem1948799 (y : real) (x : real) : (term124 x y) = (term125 y x).
Proof. exact (@lem1483488 y (real_abs x)). Qed.
Lemma lem1948800 (y : real) (x : real) : (term123 x y) = (term125 y x).
Proof. exact (TRANS (@lem1948798 x y) (@lem1948799 y x)). Qed.
Lemma lem1948801 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1948802 (y : real) (x : real) : (term126 x y) = (term127 y x).
Proof. exact (MK_COMB (@lem1948801) (@lem1948800 y x)). Qed.
Lemma lem1948803 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1948804 (y : real) (x : real) : (term128 x y) = (term129 y x).
Proof. exact (MK_COMB (@lem1948802 y x) (@lem1948803)). Qed.
Lemma lem1948817 (y : real) (x : real) : (term130 x y) = (term131 y x).
Proof. exact (@lem1483488 (term89 y) (real_abs x)). Qed.
Lemma lem1948818 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1948819 (y : real) (x : real) : (term132 x y) = (term133 y x).
Proof. exact (MK_COMB (@lem1948818) (@lem1948817 y x)). Qed.
Lemma lem1948820 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1948821 (y : real) (x : real) : (term134 x y) = (term135 y x).
Proof. exact (MK_COMB (@lem1948819 y x) (@lem1948820)). Qed.
Lemma lem1948822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1948823 (y : real) (x : real) : (term136 x y) = (term137 y x).
Proof. exact (MK_COMB (@lem1948822) (@lem1948821 y x)). Qed.
Lemma lem1948824 (y : real) (x : real) : (term120 x y) = (term138 y x).
Proof. exact (MK_COMB (@lem1948823 y x) (@lem1948804 y x)). Qed.
Lemma lem1948825 (y : real) (x : real) : (term105 x y) = (term138 y x).
Proof. exact (TRANS (@lem1948787 x y) (@lem1948824 y x)). Qed.
Lemma lem1948826 (x : real) (y : real) : (term109 x y) = (term109 x y).
Proof. exact (eq_refl (term109 x y)). Qed.
Lemma lem1948827 (y : real) (x : real) : (term117 x y) = (term139 y x).
Proof. exact (MK_COMB (@lem1948826 x y) (@lem1948825 y x)). Qed.
Lemma lem1948828 (x : real) : (term111 x) = (term111 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem1948829 (y : real) (x : real) : (term140 x y) = (term141 y x).
Proof. exact (MK_COMB (@lem1948828 x) (@lem1948827 y x)). Qed.
Lemma lem1948830 (y : real) (x : real) : (term142 y x) = (term141 y x).
Proof. exact (eq_refl (term142 y x)). Qed.
Lemma lem1948831 (y : real) (x : real) : (term141 y x) = (term142 y x).
Proof. exact (SYM (@lem1948830 y x)). Qed.
Lemma lem1948832 (y : real) (x : real) : (term142 y x) = (term143 y x).
Proof. exact (@lem1482981 (term144 x y) x). Qed.
Lemma lem1948833 (y : real) (x : real) : (term141 y x) = (term143 y x).
Proof. exact (TRANS (@lem1948831 y x) (@lem1948832 y x)). Qed.
Lemma lem1948834 (y : real) (x : real) : (term145 y x) = (term146 y x).
Proof. exact (eq_refl (term145 y x)). Qed.
Lemma lem1948835 (x : real) : (term147 x) = (term147 x).
Proof. exact (eq_refl (term147 x)). Qed.
Lemma lem1948836 (y : real) (x : real) : (term148 y x) = (term149 y x).
Proof. exact (MK_COMB (@lem1948835 x) (@lem1948834 y x)). Qed.
Lemma lem1948837 (y : real) (x : real) : (term150 y x) = (term151 y x).
Proof. exact (eq_refl (term150 y x)). Qed.
Lemma lem1948838 (x : real) : (term111 x) = (term111 x).
Proof. exact (eq_refl (term111 x)). Qed.
Lemma lem1948839 (y : real) (x : real) : (term152 y x) = (term153 y x).
Proof. exact (MK_COMB (@lem1948838 x) (@lem1948837 y x)). Qed.
Lemma lem1948840 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1948841 (y : real) (x : real) : (term154 y x) = (term155 y x).
Proof. exact (MK_COMB (@lem1948840) (@lem1948839 y x)). Qed.
Lemma lem1948842 (y : real) (x : real) : (term143 y x) = (term156 y x).
Proof. exact (MK_COMB (@lem1948841 y x) (@lem1948836 y x)). Qed.
Lemma lem1948843 (y : real) (x : real) : (term157 y x) = (term157 y x).
Proof. exact (eq_refl (term157 y x)). Qed.
Lemma lem1948844 (y : real) (x : real) : ((term141 y x) = (term143 y x)) = ((term141 y x) = (term156 y x)).
Proof. exact (MK_COMB (@lem1948843 y x) (@lem1948842 y x)). Qed.
Lemma lem1948845 (y : real) (x : real) : (term141 y x) = (term156 y x).
Proof. exact (EQ_MP (@lem1948844 y x) (@lem1948833 y x)). Qed.
Lemma lem1948846 (x : real) : (term85 x) = (term76 x).
Proof. exact (@lem1483527 x term77). Qed.
Lemma lem1948852 (x : real) : (term78 x) = (term79 x).
Proof. exact (@lem1483519 x term77). Qed.
Lemma lem1948854 (x : nat) : (term80 x) = term77.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1948855 : term81 = term77.
Proof. exact (@lem1948854 term82). Qed.
Lemma lem1948856 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1948857 (x : real) : (term79 x) = (term83 x).
Proof. exact (MK_COMB (@lem1948856 x) (@lem1948855)). Qed.
Lemma lem1948858 (x : real) : (term83 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1948859 (x : real) : (term79 x) = x.
Proof. exact (TRANS (@lem1948857 x) (@lem1948858 x)). Qed.
Lemma lem1948861 (x : real) : (term78 x) = x.
Proof. exact (TRANS (@lem1948852 x) (@lem1948859 x)). Qed.
Lemma lem1948862 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1948863 (x : real) : (term84 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1948862) (@lem1948861 x)). Qed.
Lemma lem1948864 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1948865 (x : real) : (term76 x) = (term85 x).
Proof. exact (MK_COMB (@lem1948863 x) (@lem1948864)). Qed.
Lemma lem1948866 (x : real) : (term85 x) = (term85 x).
Proof. exact (TRANS (@lem1948846 x) (@lem1948865 x)). Qed.
Lemma lem1948867 (x : real) (y : real) : (term92 x y) = (term158 x y).
Proof. exact (@lem1483525 (term88 x y) term77). Qed.
Lemma lem1948885 (x : real) (y : real) : (term159 x y) = (term160 x y).
Proof. exact (@lem1483519 (term88 x y) term77). Qed.
Lemma lem1948887 (x : nat) : (term80 x) = term77.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1948888 : term81 = term77.
Proof. exact (@lem1948887 term82). Qed.
Lemma lem1948889 (x : real) (y : real) : (term161 x y) = (term161 x y).
Proof. exact (eq_refl (term161 x y)). Qed.
Lemma lem1948890 (x : real) (y : real) : (term160 x y) = (term162 x y).
Proof. exact (MK_COMB (@lem1948889 x y) (@lem1948888)). Qed.
Lemma lem1948891 (x : real) (y : real) : (term162 x y) = (term88 x y).
Proof. exact (@lem1483450 (term88 x y)). Qed.
Lemma lem1948892 (x : real) (y : real) : (term160 x y) = (term88 x y).
Proof. exact (TRANS (@lem1948890 x y) (@lem1948891 x y)). Qed.
Lemma lem1948894 (x : real) (y : real) : (term159 x y) = (term88 x y).
Proof. exact (TRANS (@lem1948885 x y) (@lem1948892 x y)). Qed.
Lemma lem1948895 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1948896 (x : real) (y : real) : (term163 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1948895) (@lem1948894 x y)). Qed.
Lemma lem1948897 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1948898 (x : real) (y : real) : (term158 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem1948896 x y) (@lem1948897)). Qed.
Lemma lem1948899 (x : real) (y : real) : (term92 x y) = (term92 x y).
Proof. exact (TRANS (@lem1948867 x y) (@lem1948898 x y)). Qed.
Lemma lem1948900 (y : real) (x : real) : (term164 y x) = (term165 y x).
Proof. exact (@lem1483527 (term88 y x) term77). Qed.
Lemma lem1948901 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1948914 (x : real) (y : real) : (term88 y x) = (term87 x y).
Proof. exact (@lem1483488 x (term89 y)). Qed.
Lemma lem1948915 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1948916 (x : real) (y : real) : (term166 y x) = (term167 x y).
Proof. exact (MK_COMB (@lem1948915) (@lem1948914 x y)). Qed.
Lemma lem1948917 (x : real) (y : real) : (term159 y x) = (term168 x y).
Proof. exact (MK_COMB (@lem1948916 x y) (@lem1948901)). Qed.
Lemma lem1948918 (x : real) (y : real) : (term168 x y) = (term169 x y).
Proof. exact (@lem1483519 (term87 x y) term77). Qed.
Lemma lem1948920 (x : nat) : (term80 x) = term77.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1948921 : term81 = term77.
Proof. exact (@lem1948920 term82). Qed.
Lemma lem1948922 (x : real) (y : real) : (term170 x y) = (term170 x y).
Proof. exact (eq_refl (term170 x y)). Qed.
Lemma lem1948923 (x : real) (y : real) : (term169 x y) = (term171 x y).
Proof. exact (MK_COMB (@lem1948922 x y) (@lem1948921)). Qed.
Lemma lem1948924 (x : real) (y : real) : (term171 x y) = (term87 x y).
Proof. exact (@lem1483450 (term87 x y)). Qed.
Lemma lem1948925 (x : real) (y : real) : (term169 x y) = (term87 x y).
Proof. exact (TRANS (@lem1948923 x y) (@lem1948924 x y)). Qed.
Lemma lem1948926 (x : real) (y : real) : (term168 x y) = (term87 x y).
Proof. exact (TRANS (@lem1948918 x y) (@lem1948925 x y)). Qed.
Lemma lem1948927 (x : real) (y : real) : (term159 y x) = (term87 x y).
Proof. exact (TRANS (@lem1948917 x y) (@lem1948926 x y)). Qed.
Lemma lem1948928 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1948929 (x : real) (y : real) : (term172 y x) = (term173 x y).
Proof. exact (MK_COMB (@lem1948928) (@lem1948927 x y)). Qed.
Lemma lem1948930 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1948931 (x : real) (y : real) : (term165 y x) = (term174 x y).
Proof. exact (MK_COMB (@lem1948929 x y) (@lem1948930)). Qed.
Lemma lem1948932 (x : real) (y : real) : (term164 y x) = (term174 x y).
Proof. exact (TRANS (@lem1948900 y x) (@lem1948931 x y)). Qed.
Lemma lem1948933 (y : real) (x : real) : (term175 y x) = (term176 y x).
Proof. exact (@lem1483527 (real_add y x) term77). Qed.
Lemma lem1948934 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1948941 (x : real) (y : real) : (real_add y x) = (real_add x y).
Proof. exact (@lem1483488 x y). Qed.
Lemma lem1948942 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1948943 (x : real) (y : real) : (term177 y x) = (term177 x y).
Proof. exact (MK_COMB (@lem1948942) (@lem1948941 x y)). Qed.
Lemma lem1948944 (x : real) (y : real) : (term178 y x) = (term178 x y).
Proof. exact (MK_COMB (@lem1948943 x y) (@lem1948934)). Qed.
Lemma lem1948945 (x : real) (y : real) : (term178 x y) = (term179 x y).
Proof. exact (@lem1483519 (real_add x y) term77). Qed.
Lemma lem1948947 (x : nat) : (term80 x) = term77.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1948948 : term81 = term77.
Proof. exact (@lem1948947 term82). Qed.
Lemma lem1948949 (x : real) (y : real) : (term180 x y) = (term180 x y).
Proof. exact (eq_refl (term180 x y)). Qed.
Lemma lem1948950 (x : real) (y : real) : (term179 x y) = (term181 x y).
Proof. exact (MK_COMB (@lem1948949 x y) (@lem1948948)). Qed.
Lemma lem1948951 (x : real) (y : real) : (term181 x y) = (real_add x y).
Proof. exact (@lem1483450 (real_add x y)). Qed.
Lemma lem1948952 (x : real) (y : real) : (term179 x y) = (real_add x y).
Proof. exact (TRANS (@lem1948950 x y) (@lem1948951 x y)). Qed.
Lemma lem1948953 (x : real) (y : real) : (term178 x y) = (real_add x y).
Proof. exact (TRANS (@lem1948945 x y) (@lem1948952 x y)). Qed.
Lemma lem1948954 (x : real) (y : real) : (term178 y x) = (real_add x y).
Proof. exact (TRANS (@lem1948944 x y) (@lem1948953 x y)). Qed.
Lemma lem1948955 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1948956 (x : real) (y : real) : (term182 y x) = (term183 x y).
Proof. exact (MK_COMB (@lem1948955) (@lem1948954 x y)). Qed.
Lemma lem1948957 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1948958 (x : real) (y : real) : (term176 y x) = (term175 x y).
Proof. exact (MK_COMB (@lem1948956 x y) (@lem1948957)). Qed.
Lemma lem1948959 (x : real) (y : real) : (term175 y x) = (term175 x y).
Proof. exact (TRANS (@lem1948933 y x) (@lem1948958 x y)). Qed.
Lemma lem1948960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1948961 (x : real) (y : real) : (term184 y x) = (term185 x y).
Proof. exact (MK_COMB (@lem1948960) (@lem1948932 x y)). Qed.
Lemma lem1948962 (x : real) (y : real) : (term186 y x) = (term187 x y).
Proof. exact (MK_COMB (@lem1948961 x y) (@lem1948959 x y)). Qed.
Lemma lem1948963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1948964 (x : real) (y : real) : (term109 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1948963) (@lem1948899 x y)). Qed.
Lemma lem1948965 (x : real) (y : real) : (term188 y x) = (term189 x y).
Proof. exact (MK_COMB (@lem1948964 x y) (@lem1948962 x y)). Qed.
Lemma lem1948966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1948967 (x : real) : (term111 x) = (term111 x).
Proof. exact (MK_COMB (@lem1948966) (@lem1948866 x)). Qed.
Lemma lem1948968 (x : real) (y : real) : (term151 y x) = (term190 x y).
Proof. exact (MK_COMB (@lem1948967 x) (@lem1948965 x y)). Qed.
Lemma lem1948969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1948970 (x : real) : (term111 x) = (term111 x).
Proof. exact (MK_COMB (@lem1948969) (@lem1948866 x)). Qed.
Lemma lem1948971 (x : real) (y : real) : (term153 y x) = (term191 x y).
Proof. exact (MK_COMB (@lem1948970 x) (@lem1948968 x y)). Qed.
Lemma lem1948972 (x : real) : (term192 x) = (term93 x).
Proof. exact (@lem1483525 term77 x). Qed.
Lemma lem1948978 (x : real) : (term94 x) = (term95 x).
Proof. exact (@lem1483519 term77 x). Qed.
Lemma lem1948983 (x : real) : (term95 x) = (term89 x).
Proof. exact (@lem1483448 (term89 x)). Qed.
Lemma lem1948985 (x : real) : (term94 x) = (term89 x).
Proof. exact (TRANS (@lem1948978 x) (@lem1948983 x)). Qed.
Lemma lem1948986 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1948987 (x : real) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem1948986) (@lem1948985 x)). Qed.
Lemma lem1948988 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1948989 (x : real) : (term93 x) = (term98 x).
Proof. exact (MK_COMB (@lem1948987 x) (@lem1948988)). Qed.
Lemma lem1948990 (x : real) : (term192 x) = (term98 x).
Proof. exact (TRANS (@lem1948972 x) (@lem1948989 x)). Qed.
Lemma lem1948991 (y : real) (x : real) : (term193 y x) = (term194 y x).
Proof. exact (@lem1483527 (term195 y x) term77). Qed.
Lemma lem1948992 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1948999 (x : real) : (real_neg x) = (term89 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1949008 (y : real) : (term196 y) = (term196 y).
Proof. exact (eq_refl (term196 y)). Qed.
Lemma lem1949009 (y : real) (x : real) : (term195 y x) = (term197 y x).
Proof. exact (MK_COMB (@lem1949008 y) (@lem1948999 x)). Qed.
Lemma lem1949010 (x : real) (y : real) : (term197 y x) = (term197 x y).
Proof. exact (@lem1483488 (term89 x) (term89 y)). Qed.
Lemma lem1949011 (x : real) (y : real) : (term195 y x) = (term197 x y).
Proof. exact (TRANS (@lem1949009 y x) (@lem1949010 x y)). Qed.
Lemma lem1949012 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1949013 (x : real) (y : real) : (term198 y x) = (term199 x y).
Proof. exact (MK_COMB (@lem1949012) (@lem1949011 x y)). Qed.
Lemma lem1949014 (x : real) (y : real) : (term200 y x) = (term201 x y).
Proof. exact (MK_COMB (@lem1949013 x y) (@lem1948992)). Qed.
Lemma lem1949015 (x : real) (y : real) : (term201 x y) = (term202 x y).
Proof. exact (@lem1483519 (term197 x y) term77). Qed.
Lemma lem1949017 (x : nat) : (term80 x) = term77.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1949018 : term81 = term77.
Proof. exact (@lem1949017 term82). Qed.
Lemma lem1949019 (x : real) (y : real) : (term203 x y) = (term203 x y).
Proof. exact (eq_refl (term203 x y)). Qed.
Lemma lem1949020 (x : real) (y : real) : (term202 x y) = (term204 x y).
Proof. exact (MK_COMB (@lem1949019 x y) (@lem1949018)). Qed.
Lemma lem1949021 (x : real) (y : real) : (term204 x y) = (term197 x y).
Proof. exact (@lem1483450 (term197 x y)). Qed.
Lemma lem1949022 (x : real) (y : real) : (term202 x y) = (term197 x y).
Proof. exact (TRANS (@lem1949020 x y) (@lem1949021 x y)). Qed.
Lemma lem1949023 (x : real) (y : real) : (term201 x y) = (term197 x y).
Proof. exact (TRANS (@lem1949015 x y) (@lem1949022 x y)). Qed.
Lemma lem1949024 (x : real) (y : real) : (term200 y x) = (term197 x y).
Proof. exact (TRANS (@lem1949014 x y) (@lem1949023 x y)). Qed.
Lemma lem1949025 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1949026 (x : real) (y : real) : (term205 y x) = (term206 x y).
Proof. exact (MK_COMB (@lem1949025) (@lem1949024 x y)). Qed.
Lemma lem1949027 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949028 (x : real) (y : real) : (term194 y x) = (term207 x y).
Proof. exact (MK_COMB (@lem1949026 x y) (@lem1949027)). Qed.
Lemma lem1949029 (x : real) (y : real) : (term193 y x) = (term207 x y).
Proof. exact (TRANS (@lem1948991 y x) (@lem1949028 x y)). Qed.
Lemma lem1949030 (y : real) (x : real) : (term208 y x) = (term209 y x).
Proof. exact (@lem1483527 (term210 y x) term77). Qed.
Lemma lem1949031 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949038 (x : real) : (real_neg x) = (term89 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1949041 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1949042 (y : real) (x : real) : (term210 y x) = (term87 y x).
Proof. exact (MK_COMB (@lem1949041 y) (@lem1949038 x)). Qed.
Lemma lem1949043 (x : real) (y : real) : (term87 y x) = (term88 x y).
Proof. exact (@lem1483488 (term89 x) y). Qed.
Lemma lem1949044 (x : real) (y : real) : (term210 y x) = (term88 x y).
Proof. exact (TRANS (@lem1949042 y x) (@lem1949043 x y)). Qed.
Lemma lem1949045 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1949046 (x : real) (y : real) : (term211 y x) = (term166 x y).
Proof. exact (MK_COMB (@lem1949045) (@lem1949044 x y)). Qed.
Lemma lem1949047 (x : real) (y : real) : (term212 y x) = (term159 x y).
Proof. exact (MK_COMB (@lem1949046 x y) (@lem1949031)). Qed.
Lemma lem1949048 (x : real) (y : real) : (term159 x y) = (term160 x y).
Proof. exact (@lem1483519 (term88 x y) term77). Qed.
Lemma lem1949050 (x : nat) : (term80 x) = term77.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1949051 : term81 = term77.
Proof. exact (@lem1949050 term82). Qed.
Lemma lem1949052 (x : real) (y : real) : (term161 x y) = (term161 x y).
Proof. exact (eq_refl (term161 x y)). Qed.
Lemma lem1949053 (x : real) (y : real) : (term160 x y) = (term162 x y).
Proof. exact (MK_COMB (@lem1949052 x y) (@lem1949051)). Qed.
Lemma lem1949054 (x : real) (y : real) : (term162 x y) = (term88 x y).
Proof. exact (@lem1483450 (term88 x y)). Qed.
Lemma lem1949055 (x : real) (y : real) : (term160 x y) = (term88 x y).
Proof. exact (TRANS (@lem1949053 x y) (@lem1949054 x y)). Qed.
Lemma lem1949056 (x : real) (y : real) : (term159 x y) = (term88 x y).
Proof. exact (TRANS (@lem1949048 x y) (@lem1949055 x y)). Qed.
Lemma lem1949057 (x : real) (y : real) : (term212 y x) = (term88 x y).
Proof. exact (TRANS (@lem1949047 x y) (@lem1949056 x y)). Qed.
Lemma lem1949058 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1949059 (x : real) (y : real) : (term213 y x) = (term214 x y).
Proof. exact (MK_COMB (@lem1949058) (@lem1949057 x y)). Qed.
Lemma lem1949060 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949061 (x : real) (y : real) : (term209 y x) = (term164 x y).
Proof. exact (MK_COMB (@lem1949059 x y) (@lem1949060)). Qed.
Lemma lem1949062 (x : real) (y : real) : (term208 y x) = (term164 x y).
Proof. exact (TRANS (@lem1949030 y x) (@lem1949061 x y)). Qed.
Lemma lem1949063 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1949064 (x : real) (y : real) : (term215 y x) = (term216 x y).
Proof. exact (MK_COMB (@lem1949063) (@lem1949029 x y)). Qed.
Lemma lem1949065 (x : real) (y : real) : (term217 y x) = (term218 x y).
Proof. exact (MK_COMB (@lem1949064 x y) (@lem1949062 x y)). Qed.
Lemma lem1949066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1949067 (x : real) (y : real) : (term109 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1949066) (@lem1948899 x y)). Qed.
Lemma lem1949068 (x : real) (y : real) : (term219 y x) = (term220 x y).
Proof. exact (MK_COMB (@lem1949067 x y) (@lem1949065 x y)). Qed.
Lemma lem1949069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1949070 (x : real) : (term111 x) = (term111 x).
Proof. exact (MK_COMB (@lem1949069) (@lem1948866 x)). Qed.
Lemma lem1949071 (x : real) (y : real) : (term146 y x) = (term221 x y).
Proof. exact (MK_COMB (@lem1949070 x) (@lem1949068 x y)). Qed.
Lemma lem1949072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1949073 (x : real) : (term147 x) = (term222 x).
Proof. exact (MK_COMB (@lem1949072) (@lem1948990 x)). Qed.
Lemma lem1949074 (x : real) (y : real) : (term149 y x) = (term223 x y).
Proof. exact (MK_COMB (@lem1949073 x) (@lem1949071 x y)). Qed.
Lemma lem1949075 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1949076 (x : real) (y : real) : (term155 y x) = (term224 x y).
Proof. exact (MK_COMB (@lem1949075) (@lem1948971 x y)). Qed.
Lemma lem1949077 (x : real) (y : real) : (term156 y x) = (term225 x y).
Proof. exact (MK_COMB (@lem1949076 x y) (@lem1949074 x y)). Qed.
Lemma lem1949088 (x : real) (y : real) : (term141 y x) = (term225 x y).
Proof. exact (TRANS (@lem1948845 y x) (@lem1949077 x y)). Qed.
Lemma lem1949089 (x : real) (y : real) : (term140 x y) = (term225 x y).
Proof. exact (TRANS (@lem1948829 y x) (@lem1949088 x y)). Qed.
Lemma lem1949091 (x : real) (y : real) : (term226 x y) = (term226 x y).
Proof. exact (eq_refl (term226 x y)). Qed.
Lemma lem1949092 (x : real) (y : real) : (term115 x y) = (term227 x y).
Proof. exact (MK_COMB (@lem1949091 x y) (@lem1949089 x y)). Qed.
Lemma lem1949093 (x : real) (y : real) (h1 : term227 x y) : term227 x y.
Proof. exact (h1). Qed.
Lemma lem1949094 (x : real) (y : real) (h1 : term228 x y) : term228 x y.
Proof. exact (h1). Qed.
Lemma lem1949095 (x : real) (y : real) (h1 : term228 x y) : term116 x y.
Proof. exact (proj2 (@lem1949094 x y h1)). Qed.
Lemma lem1949096 (x : real) (y : real) (h1 : term228 x y) : term85 x.
Proof. exact (proj1 (@lem1949094 x y h1)). Qed.
Lemma lem1949097 (x : real) (y : real) (h1 : term228 x y) : term98 y.
Proof. exact (proj2 (@lem1949095 x y h1)). Qed.
Lemma lem1949098 (x : real) (y : real) (h1 : term228 x y) : term92 x y.
Proof. exact (proj1 (@lem1949095 x y h1)). Qed.
Lemma lem1949100 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1949101 : term230 = term231.
Proof. exact (@lem1949100 (NUMERAL 0) term82). Qed.
Lemma lem1949102 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1949103 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1949104 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1949103 h1) (fun h1 : term231 = True => @lem1949102)). Qed.
Lemma lem1949105 : term231 = True.
Proof. exact (EQ_MP (@lem1949104) (@lem1949102)). Qed.
Lemma lem1949106 : term230 = True.
Proof. exact (TRANS (@lem1949101) (@lem1949105)). Qed.
Lemma lem1949107 : True = term230.
Proof. exact (SYM (@lem1949106)). Qed.
Lemma lem1949108 : term230.
Proof. exact (EQ_MP (@lem1949107) (@lem0)). Qed.
Lemma lem1949109 (x : real) (y : real) (h1 : term228 x y) : term233 x.
Proof. exact (conj (@lem1949108) (@lem1949096 x y h1)). Qed.
Lemma lem1949111 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1949112 (x : real) : term235 x.
Proof. exact (@lem1949111 term236 x). Qed.
Lemma lem1949113 (x : real) (y : real) (h1 : term228 x y) : term237 x.
Proof. exact (@lem1949112 x (@lem1949109 x y h1)). Qed.
Lemma lem1949114 (x : real) : (term121 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1949115 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1949116 (x : real) : (term238 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1949115) (@lem1949114 x)). Qed.
Lemma lem1949117 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949118 (x : real) : (term237 x) = (term85 x).
Proof. exact (MK_COMB (@lem1949116 x) (@lem1949117)). Qed.
Lemma lem1949119 (x : real) (y : real) (h1 : term228 x y) : term85 x.
Proof. exact (EQ_MP (@lem1949118 x) (@lem1949113 x y h1)). Qed.
Lemma lem1949121 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1949122 : term230 = term231.
Proof. exact (@lem1949121 (NUMERAL 0) term82). Qed.
Lemma lem1949123 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1949124 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1949125 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1949124 h1) (fun h1 : term231 = True => @lem1949123)). Qed.
Lemma lem1949126 : term231 = True.
Proof. exact (EQ_MP (@lem1949125) (@lem1949123)). Qed.
Lemma lem1949127 : term230 = True.
Proof. exact (TRANS (@lem1949122) (@lem1949126)). Qed.
Lemma lem1949128 : True = term230.
Proof. exact (SYM (@lem1949127)). Qed.
Lemma lem1949129 : term230.
Proof. exact (EQ_MP (@lem1949128) (@lem0)). Qed.
Lemma lem1949130 (x : real) (y : real) (h1 : term228 x y) : term239 x y.
Proof. exact (conj (@lem1949129) (@lem1949098 x y h1)). Qed.
Lemma lem1949132 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1949133 (x : real) (y : real) : term241 x y.
Proof. exact (@lem1949132 term236 (term88 x y)). Qed.
Lemma lem1949134 (x : real) (y : real) (h1 : term228 x y) : term242 x y.
Proof. exact (@lem1949133 x y (@lem1949130 x y h1)). Qed.
Lemma lem1949135 (x : real) (y : real) : (term243 x y) = (term88 x y).
Proof. exact (@lem1483460 (term88 x y)). Qed.
Lemma lem1949136 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1949137 (x : real) (y : real) : (term244 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1949136) (@lem1949135 x y)). Qed.
Lemma lem1949138 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949139 (x : real) (y : real) : (term242 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem1949137 x y) (@lem1949138)). Qed.
Lemma lem1949140 (x : real) (y : real) (h1 : term228 x y) : term92 x y.
Proof. exact (EQ_MP (@lem1949139 x y) (@lem1949134 x y h1)). Qed.
Lemma lem1949142 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1949143 : term230 = term231.
Proof. exact (@lem1949142 (NUMERAL 0) term82). Qed.
Lemma lem1949144 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1949145 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1949146 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1949145 h1) (fun h1 : term231 = True => @lem1949144)). Qed.
Lemma lem1949147 : term231 = True.
Proof. exact (EQ_MP (@lem1949146) (@lem1949144)). Qed.
Lemma lem1949148 : term230 = True.
Proof. exact (TRANS (@lem1949143) (@lem1949147)). Qed.
Lemma lem1949149 : True = term230.
Proof. exact (SYM (@lem1949148)). Qed.
Lemma lem1949150 : term230.
Proof. exact (EQ_MP (@lem1949149) (@lem0)). Qed.
Lemma lem1949151 (x : real) (y : real) (h1 : term228 x y) : term245 y.
Proof. exact (conj (@lem1949150) (@lem1949097 x y h1)). Qed.
Lemma lem1949153 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1949154 (y : real) : term246 y.
Proof. exact (@lem1949153 term236 (term89 y)). Qed.
Lemma lem1949155 (x : real) (y : real) (h1 : term228 x y) : term247 y.
Proof. exact (@lem1949154 y (@lem1949151 x y h1)). Qed.
Lemma lem1949156 (y : real) : (term248 y) = (term89 y).
Proof. exact (@lem1483460 (term89 y)). Qed.
Lemma lem1949157 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1949158 (y : real) : (term249 y) = (term97 y).
Proof. exact (MK_COMB (@lem1949157) (@lem1949156 y)). Qed.
Lemma lem1949159 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949160 (y : real) : (term247 y) = (term98 y).
Proof. exact (MK_COMB (@lem1949158 y) (@lem1949159)). Qed.
Lemma lem1949161 (x : real) (y : real) (h1 : term228 x y) : term98 y.
Proof. exact (EQ_MP (@lem1949160 y) (@lem1949155 x y h1)). Qed.
Lemma lem1949162 (x : real) (y : real) (h1 : term228 x y) : term250 x y.
Proof. exact (conj (@lem1949161 x y h1) (@lem1949140 x y h1)). Qed.
Lemma lem1949164 (x : real) (y : real) : term251 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1949165 (x : real) (y : real) : term252 x y.
Proof. exact (@lem1949164 (term89 y) (term88 x y)). Qed.
Lemma lem1949166 (x : real) (y : real) (h1 : term228 x y) : term253 x y.
Proof. exact (@lem1949165 x y (@lem1949162 x y h1)). Qed.
Lemma lem1949167 (x : real) (y : real) : (term254 x y) = (term255 x y).
Proof. exact (@lem1483484 (term89 x) (term89 y) y). Qed.
Lemma lem1949168 (y : real) : (term256 y) = (term257 y).
Proof. exact (@lem1483440 term258 y). Qed.
Lemma lem1949170 (m : nat) : (term259 m) = term77.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1949171 : term260 = term77.
Proof. exact (@lem1949170 term82). Qed.
Lemma lem1949172 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1949173 : term261 = term262.
Proof. exact (MK_COMB (@lem1949172) (@lem1949171)). Qed.
Lemma lem1949174 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1949175 (y : real) : (term257 y) = (term263 y).
Proof. exact (MK_COMB (@lem1949173) (@lem1949174 y)). Qed.
Lemma lem1949176 (y : real) : (term256 y) = (term263 y).
Proof. exact (TRANS (@lem1949168 y) (@lem1949175 y)). Qed.
Lemma lem1949177 (y : real) : (term263 y) = term77.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1949178 (y : real) : (term256 y) = term77.
Proof. exact (TRANS (@lem1949176 y) (@lem1949177 y)). Qed.
Lemma lem1949179 (x : real) : (term196 x) = (term196 x).
Proof. exact (eq_refl (term196 x)). Qed.
Lemma lem1949180 (y : real) (x : real) : (term255 x y) = (term264 x).
Proof. exact (MK_COMB (@lem1949179 x) (@lem1949178 y)). Qed.
Lemma lem1949181 (y : real) (x : real) : (term254 x y) = (term264 x).
Proof. exact (TRANS (@lem1949167 x y) (@lem1949180 y x)). Qed.
Lemma lem1949182 (x : real) : (term264 x) = (term89 x).
Proof. exact (@lem1483450 (term89 x)). Qed.
Lemma lem1949183 (y : real) (x : real) : (term254 x y) = (term89 x).
Proof. exact (TRANS (@lem1949181 y x) (@lem1949182 x)). Qed.
Lemma lem1949184 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1949185 (y : real) (x : real) : (term265 x y) = (term97 x).
Proof. exact (MK_COMB (@lem1949184) (@lem1949183 y x)). Qed.
Lemma lem1949186 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949187 (y : real) (x : real) : (term253 x y) = (term98 x).
Proof. exact (MK_COMB (@lem1949185 y x) (@lem1949186)). Qed.
Lemma lem1949188 (x : real) (y : real) (h1 : term228 x y) : term98 x.
Proof. exact (EQ_MP (@lem1949187 y x) (@lem1949166 x y h1)). Qed.
Lemma lem1949190 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1949191 : term230 = term231.
Proof. exact (@lem1949190 (NUMERAL 0) term82). Qed.
Lemma lem1949192 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1949193 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1949194 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1949193 h1) (fun h1 : term231 = True => @lem1949192)). Qed.
Lemma lem1949195 : term231 = True.
Proof. exact (EQ_MP (@lem1949194) (@lem1949192)). Qed.
Lemma lem1949196 : term230 = True.
Proof. exact (TRANS (@lem1949191) (@lem1949195)). Qed.
Lemma lem1949197 : True = term230.
Proof. exact (SYM (@lem1949196)). Qed.
Lemma lem1949198 : term230.
Proof. exact (EQ_MP (@lem1949197) (@lem0)). Qed.
Lemma lem1949199 (x : real) (y : real) (h1 : term228 x y) : term245 x.
Proof. exact (conj (@lem1949198) (@lem1949188 x y h1)). Qed.
Lemma lem1949201 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1949202 (x : real) : term246 x.
Proof. exact (@lem1949201 term236 (term89 x)). Qed.
Lemma lem1949203 (x : real) (y : real) (h1 : term228 x y) : term247 x.
Proof. exact (@lem1949202 x (@lem1949199 x y h1)). Qed.
Lemma lem1949204 (x : real) : (term248 x) = (term89 x).
Proof. exact (@lem1483460 (term89 x)). Qed.
Lemma lem1949205 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1949206 (x : real) : (term249 x) = (term97 x).
Proof. exact (MK_COMB (@lem1949205) (@lem1949204 x)). Qed.
Lemma lem1949207 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949208 (x : real) : (term247 x) = (term98 x).
Proof. exact (MK_COMB (@lem1949206 x) (@lem1949207)). Qed.
Lemma lem1949209 (x : real) (y : real) (h1 : term228 x y) : term98 x.
Proof. exact (EQ_MP (@lem1949208 x) (@lem1949203 x y h1)). Qed.
Lemma lem1949210 (x : real) (y : real) (h1 : term228 x y) : term266 x.
Proof. exact (conj (@lem1949209 x y h1) (@lem1949119 x y h1)). Qed.
Lemma lem1949212 (x : real) (y : real) : term267 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1949213 (x : real) : term268 x.
Proof. exact (@lem1949212 (term89 x) x). Qed.
Lemma lem1949214 (x : real) (y : real) (h1 : term228 x y) : term269 x.
Proof. exact (@lem1949213 x (@lem1949210 x y h1)). Qed.
Lemma lem1949215 (x : real) : (term256 x) = (term257 x).
Proof. exact (@lem1483440 term258 x). Qed.
Lemma lem1949217 (m : nat) : (term259 m) = term77.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1949218 : term260 = term77.
Proof. exact (@lem1949217 term82). Qed.
Lemma lem1949219 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1949220 : term261 = term262.
Proof. exact (MK_COMB (@lem1949219) (@lem1949218)). Qed.
Lemma lem1949221 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1949222 (x : real) : (term257 x) = (term263 x).
Proof. exact (MK_COMB (@lem1949220) (@lem1949221 x)). Qed.
Lemma lem1949223 (x : real) : (term256 x) = (term263 x).
Proof. exact (TRANS (@lem1949215 x) (@lem1949222 x)). Qed.
Lemma lem1949224 (x : real) : (term263 x) = term77.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1949225 (x : real) : (term256 x) = term77.
Proof. exact (TRANS (@lem1949223 x) (@lem1949224 x)). Qed.
Lemma lem1949226 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1949227 (x : real) : (term270 x) = term271.
Proof. exact (MK_COMB (@lem1949226) (@lem1949225 x)). Qed.
Lemma lem1949228 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949229 (x : real) : (term269 x) = term272.
Proof. exact (MK_COMB (@lem1949227 x) (@lem1949228)). Qed.
Lemma lem1949230 (x : real) (y : real) (h1 : term228 x y) : term272.
Proof. exact (EQ_MP (@lem1949229 x) (@lem1949214 x y h1)). Qed.
Lemma lem1949232 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1949233 : term272 = term273.
Proof. exact (@lem1949232 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1949234 : term273 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1949235 : term272 = False.
Proof. exact (TRANS (@lem1949233) (@lem1949234)). Qed.
Lemma lem1949236 (x : real) (y : real) (h1 : term228 x y) : False.
Proof. exact (EQ_MP (@lem1949235) (@lem1949230 x y h1)). Qed.
Lemma lem1949237 (x : real) (y : real) (h1 : term225 x y) : term225 x y.
Proof. exact (h1). Qed.
Lemma lem1949238 (x : real) (y : real) (h1 : term191 x y) : term191 x y.
Proof. exact (h1). Qed.
Lemma lem1949239 (x : real) (y : real) (h1 : term191 x y) : term190 x y.
Proof. exact (proj2 (@lem1949238 x y h1)). Qed.
Lemma lem1949241 (x : real) (y : real) (h1 : term191 x y) : term189 x y.
Proof. exact (proj2 (@lem1949239 x y h1)). Qed.
Lemma lem1949243 (x : real) (y : real) (h1 : term191 x y) : term187 x y.
Proof. exact (proj2 (@lem1949241 x y h1)). Qed.
Lemma lem1949244 (x : real) (y : real) (h1 : term191 x y) : term92 x y.
Proof. exact (proj1 (@lem1949241 x y h1)). Qed.
Lemma lem1949246 (x : real) (y : real) (h1 : term191 x y) : term174 x y.
Proof. exact (proj1 (@lem1949243 x y h1)). Qed.
Lemma lem1949248 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1949249 : term230 = term231.
Proof. exact (@lem1949248 (NUMERAL 0) term82). Qed.
Lemma lem1949250 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1949251 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1949252 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1949251 h1) (fun h1 : term231 = True => @lem1949250)). Qed.
Lemma lem1949253 : term231 = True.
Proof. exact (EQ_MP (@lem1949252) (@lem1949250)). Qed.
Lemma lem1949254 : term230 = True.
Proof. exact (TRANS (@lem1949249) (@lem1949253)). Qed.
Lemma lem1949255 : True = term230.
Proof. exact (SYM (@lem1949254)). Qed.
Lemma lem1949256 : term230.
Proof. exact (EQ_MP (@lem1949255) (@lem0)). Qed.
Lemma lem1949257 (x : real) (y : real) (h1 : term191 x y) : term274 x y.
Proof. exact (conj (@lem1949256) (@lem1949246 x y h1)). Qed.
Lemma lem1949259 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1949260 (x : real) (y : real) : term275 x y.
Proof. exact (@lem1949259 term236 (term87 x y)). Qed.
Lemma lem1949261 (x : real) (y : real) (h1 : term191 x y) : term276 x y.
Proof. exact (@lem1949260 x y (@lem1949257 x y h1)). Qed.
Lemma lem1949262 (x : real) (y : real) : (term277 x y) = (term87 x y).
Proof. exact (@lem1483460 (term87 x y)). Qed.
Lemma lem1949263 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1949264 (x : real) (y : real) : (term278 x y) = (term173 x y).
Proof. exact (MK_COMB (@lem1949263) (@lem1949262 x y)). Qed.
Lemma lem1949265 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949266 (x : real) (y : real) : (term276 x y) = (term174 x y).
Proof. exact (MK_COMB (@lem1949264 x y) (@lem1949265)). Qed.
Lemma lem1949267 (x : real) (y : real) (h1 : term191 x y) : term174 x y.
Proof. exact (EQ_MP (@lem1949266 x y) (@lem1949261 x y h1)). Qed.
Lemma lem1949269 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1949270 : term230 = term231.
Proof. exact (@lem1949269 (NUMERAL 0) term82). Qed.
Lemma lem1949271 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1949272 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1949273 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1949272 h1) (fun h1 : term231 = True => @lem1949271)). Qed.
Lemma lem1949274 : term231 = True.
Proof. exact (EQ_MP (@lem1949273) (@lem1949271)). Qed.
Lemma lem1949275 : term230 = True.
Proof. exact (TRANS (@lem1949270) (@lem1949274)). Qed.
Lemma lem1949276 : True = term230.
Proof. exact (SYM (@lem1949275)). Qed.
Lemma lem1949277 : term230.
Proof. exact (EQ_MP (@lem1949276) (@lem0)). Qed.
Lemma lem1949278 (x : real) (y : real) (h1 : term191 x y) : term239 x y.
Proof. exact (conj (@lem1949277) (@lem1949244 x y h1)). Qed.
Lemma lem1949280 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1949281 (x : real) (y : real) : term241 x y.
Proof. exact (@lem1949280 term236 (term88 x y)). Qed.
Lemma lem1949282 (x : real) (y : real) (h1 : term191 x y) : term242 x y.
Proof. exact (@lem1949281 x y (@lem1949278 x y h1)). Qed.
Lemma lem1949283 (x : real) (y : real) : (term243 x y) = (term88 x y).
Proof. exact (@lem1483460 (term88 x y)). Qed.
Lemma lem1949284 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1949285 (x : real) (y : real) : (term244 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1949284) (@lem1949283 x y)). Qed.
Lemma lem1949286 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949287 (x : real) (y : real) : (term242 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem1949285 x y) (@lem1949286)). Qed.
Lemma lem1949288 (x : real) (y : real) (h1 : term191 x y) : term92 x y.
Proof. exact (EQ_MP (@lem1949287 x y) (@lem1949282 x y h1)). Qed.
Lemma lem1949289 (x : real) (y : real) (h1 : term191 x y) : term279 x y.
Proof. exact (conj (@lem1949288 x y h1) (@lem1949267 x y h1)). Qed.
Lemma lem1949291 (x : real) (y : real) : term267 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1949292 (x : real) (y : real) : term280 x y.
Proof. exact (@lem1949291 (term88 x y) (term87 x y)). Qed.
Lemma lem1949293 (x : real) (y : real) (h1 : term191 x y) : term281 x y.
Proof. exact (@lem1949292 x y (@lem1949289 x y h1)). Qed.
Lemma lem1949294 (x : real) (y : real) : (term282 x y) = (term283 x y).
Proof. exact (@lem1483480 (term89 x) x y (term89 y)). Qed.
Lemma lem1949295 (x : real) : (term256 x) = (term257 x).
Proof. exact (@lem1483440 term258 x). Qed.
Lemma lem1949297 (m : nat) : (term259 m) = term77.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1949298 : term260 = term77.
Proof. exact (@lem1949297 term82). Qed.
Lemma lem1949299 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1949300 : term261 = term262.
Proof. exact (MK_COMB (@lem1949299) (@lem1949298)). Qed.
Lemma lem1949301 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1949302 (x : real) : (term257 x) = (term263 x).
Proof. exact (MK_COMB (@lem1949300) (@lem1949301 x)). Qed.
Lemma lem1949303 (x : real) : (term256 x) = (term263 x).
Proof. exact (TRANS (@lem1949295 x) (@lem1949302 x)). Qed.
Lemma lem1949304 (x : real) : (term263 x) = term77.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1949305 (x : real) : (term256 x) = term77.
Proof. exact (TRANS (@lem1949303 x) (@lem1949304 x)). Qed.
Lemma lem1949306 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1949307 (x : real) : (term284 x) = term285.
Proof. exact (MK_COMB (@lem1949306) (@lem1949305 x)). Qed.
Lemma lem1949308 (y : real) : (term286 y) = (term257 y).
Proof. exact (@lem1483442 term258 y). Qed.
Lemma lem1949310 (m : nat) : (term259 m) = term77.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1949311 : term260 = term77.
Proof. exact (@lem1949310 term82). Qed.
Lemma lem1949312 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1949313 : term261 = term262.
Proof. exact (MK_COMB (@lem1949312) (@lem1949311)). Qed.
Lemma lem1949314 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1949315 (y : real) : (term257 y) = (term263 y).
Proof. exact (MK_COMB (@lem1949313) (@lem1949314 y)). Qed.
Lemma lem1949316 (y : real) : (term286 y) = (term263 y).
Proof. exact (TRANS (@lem1949308 y) (@lem1949315 y)). Qed.
Lemma lem1949317 (y : real) : (term263 y) = term77.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1949318 (y : real) : (term286 y) = term77.
Proof. exact (TRANS (@lem1949316 y) (@lem1949317 y)). Qed.
Lemma lem1949319 (x : real) (y : real) : (term283 x y) = term287.
Proof. exact (MK_COMB (@lem1949307 x) (@lem1949318 y)). Qed.
Lemma lem1949320 (x : real) (y : real) : (term282 x y) = term287.
Proof. exact (TRANS (@lem1949294 x y) (@lem1949319 x y)). Qed.
Lemma lem1949321 : term287 = term77.
Proof. exact (@lem1483448 term77). Qed.
Lemma lem1949322 (x : real) (y : real) : (term282 x y) = term77.
Proof. exact (TRANS (@lem1949320 x y) (@lem1949321)). Qed.
Lemma lem1949323 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1949324 (x : real) (y : real) : (term288 x y) = term271.
Proof. exact (MK_COMB (@lem1949323) (@lem1949322 x y)). Qed.
Lemma lem1949325 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949326 (x : real) (y : real) : (term281 x y) = term272.
Proof. exact (MK_COMB (@lem1949324 x y) (@lem1949325)). Qed.
Lemma lem1949327 (x : real) (y : real) (h1 : term191 x y) : term272.
Proof. exact (EQ_MP (@lem1949326 x y) (@lem1949293 x y h1)). Qed.
Lemma lem1949329 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1949330 : term272 = term273.
Proof. exact (@lem1949329 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1949331 : term273 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1949332 : term272 = False.
Proof. exact (TRANS (@lem1949330) (@lem1949331)). Qed.
Lemma lem1949333 (x : real) (y : real) (h1 : term191 x y) : False.
Proof. exact (EQ_MP (@lem1949332) (@lem1949327 x y h1)). Qed.
Lemma lem1949334 (x : real) (y : real) (h1 : term223 x y) : term223 x y.
Proof. exact (h1). Qed.
Lemma lem1949335 (x : real) (y : real) (h1 : term223 x y) : term221 x y.
Proof. exact (proj2 (@lem1949334 x y h1)). Qed.
Lemma lem1949337 (x : real) (y : real) (h1 : term223 x y) : term220 x y.
Proof. exact (proj2 (@lem1949335 x y h1)). Qed.
Lemma lem1949338 (x : real) (y : real) (h1 : term223 x y) : term85 x.
Proof. exact (proj1 (@lem1949335 x y h1)). Qed.
Lemma lem1949339 (x : real) (y : real) (h1 : term223 x y) : term218 x y.
Proof. exact (proj2 (@lem1949337 x y h1)). Qed.
Lemma lem1949340 (x : real) (y : real) (h1 : term223 x y) : term92 x y.
Proof. exact (proj1 (@lem1949337 x y h1)). Qed.
Lemma lem1949342 (x : real) (y : real) (h1 : term223 x y) : term207 x y.
Proof. exact (proj1 (@lem1949339 x y h1)). Qed.
Lemma lem1949344 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1949345 : term289 = term290.
Proof. exact (@lem1949344 (NUMERAL 0) term291). Qed.
Lemma lem1949346 : term292 = term293.
Proof. exact (@lem912803). Qed.
Lemma lem1949347 (h1 : term292 = term293) : term290 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term293 h1). Qed.
Lemma lem1949348 : (term292 = term293) = (term290 = True).
Proof. exact (prop_ext (fun h1 : term292 = term293 => @lem1949347 h1) (fun h1 : term290 = True => @lem1949346)). Qed.
Lemma lem1949349 : term290 = True.
Proof. exact (EQ_MP (@lem1949348) (@lem1949346)). Qed.
Lemma lem1949350 : term289 = True.
Proof. exact (TRANS (@lem1949345) (@lem1949349)). Qed.
Lemma lem1949351 : True = term289.
Proof. exact (SYM (@lem1949350)). Qed.
Lemma lem1949352 : term289.
Proof. exact (EQ_MP (@lem1949351) (@lem0)). Qed.
Lemma lem1949353 (x : real) (y : real) (h1 : term223 x y) : term294 x.
Proof. exact (conj (@lem1949352) (@lem1949338 x y h1)). Qed.
Lemma lem1949355 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1949356 (x : real) : term295 x.
Proof. exact (@lem1949355 term296 x). Qed.
Lemma lem1949363 (x : real) (y : real) (h1 : term223 x y) : term297 x.
Proof. exact (@lem1949356 x (@lem1949353 x y h1)). Qed.
Lemma lem1949365 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1949366 : term230 = term231.
Proof. exact (@lem1949365 (NUMERAL 0) term82). Qed.
Lemma lem1949367 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1949368 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1949369 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1949368 h1) (fun h1 : term231 = True => @lem1949367)). Qed.
Lemma lem1949370 : term231 = True.
Proof. exact (EQ_MP (@lem1949369) (@lem1949367)). Qed.
Lemma lem1949371 : term230 = True.
Proof. exact (TRANS (@lem1949366) (@lem1949370)). Qed.
Lemma lem1949372 : True = term230.
Proof. exact (SYM (@lem1949371)). Qed.
Lemma lem1949373 : term230.
Proof. exact (EQ_MP (@lem1949372) (@lem0)). Qed.
Lemma lem1949374 (x : real) (y : real) (h1 : term223 x y) : term298 x y.
Proof. exact (conj (@lem1949373) (@lem1949342 x y h1)). Qed.
Lemma lem1949376 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1949377 (x : real) (y : real) : term299 x y.
Proof. exact (@lem1949376 term236 (term197 x y)). Qed.
Lemma lem1949378 (x : real) (y : real) (h1 : term223 x y) : term300 x y.
Proof. exact (@lem1949377 x y (@lem1949374 x y h1)). Qed.
Lemma lem1949379 (x : real) (y : real) : (term301 x y) = (term197 x y).
Proof. exact (@lem1483460 (term197 x y)). Qed.
Lemma lem1949380 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1949381 (x : real) (y : real) : (term302 x y) = (term206 x y).
Proof. exact (MK_COMB (@lem1949380) (@lem1949379 x y)). Qed.
Lemma lem1949382 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949383 (x : real) (y : real) : (term300 x y) = (term207 x y).
Proof. exact (MK_COMB (@lem1949381 x y) (@lem1949382)). Qed.
Lemma lem1949384 (x : real) (y : real) (h1 : term223 x y) : term207 x y.
Proof. exact (EQ_MP (@lem1949383 x y) (@lem1949378 x y h1)). Qed.
Lemma lem1949386 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1949387 : term230 = term231.
Proof. exact (@lem1949386 (NUMERAL 0) term82). Qed.
Lemma lem1949388 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1949389 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1949390 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1949389 h1) (fun h1 : term231 = True => @lem1949388)). Qed.
Lemma lem1949391 : term231 = True.
Proof. exact (EQ_MP (@lem1949390) (@lem1949388)). Qed.
Lemma lem1949392 : term230 = True.
Proof. exact (TRANS (@lem1949387) (@lem1949391)). Qed.
Lemma lem1949393 : True = term230.
Proof. exact (SYM (@lem1949392)). Qed.
Lemma lem1949394 : term230.
Proof. exact (EQ_MP (@lem1949393) (@lem0)). Qed.
Lemma lem1949395 (x : real) (y : real) (h1 : term223 x y) : term239 x y.
Proof. exact (conj (@lem1949394) (@lem1949340 x y h1)). Qed.
Lemma lem1949397 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1949398 (x : real) (y : real) : term241 x y.
Proof. exact (@lem1949397 term236 (term88 x y)). Qed.
Lemma lem1949399 (x : real) (y : real) (h1 : term223 x y) : term242 x y.
Proof. exact (@lem1949398 x y (@lem1949395 x y h1)). Qed.
Lemma lem1949400 (x : real) (y : real) : (term243 x y) = (term88 x y).
Proof. exact (@lem1483460 (term88 x y)). Qed.
Lemma lem1949401 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1949402 (x : real) (y : real) : (term244 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1949401) (@lem1949400 x y)). Qed.
Lemma lem1949403 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949404 (x : real) (y : real) : (term242 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem1949402 x y) (@lem1949403)). Qed.
Lemma lem1949405 (x : real) (y : real) (h1 : term223 x y) : term92 x y.
Proof. exact (EQ_MP (@lem1949404 x y) (@lem1949399 x y h1)). Qed.
Lemma lem1949406 (x : real) (y : real) (h1 : term223 x y) : term303 x y.
Proof. exact (conj (@lem1949405 x y h1) (@lem1949384 x y h1)). Qed.
Lemma lem1949408 (x : real) (y : real) : term267 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1949409 (x : real) (y : real) : term304 x y.
Proof. exact (@lem1949408 (term88 x y) (term197 x y)). Qed.
Lemma lem1949410 (x : real) (y : real) (h1 : term223 x y) : term305 x y.
Proof. exact (@lem1949409 x y (@lem1949406 x y h1)). Qed.
Lemma lem1949411 (x : real) (y : real) : (term306 x y) = (term307 x y).
Proof. exact (@lem1483480 (term89 x) (term89 x) y (term89 y)). Qed.
Lemma lem1949412 (x : real) : (term308 x) = (term309 x).
Proof. exact (@lem1483438 term258 term258 x). Qed.
Lemma lem1949413 : term310 = term311.
Proof. exact (@lem1367763 term82 term82). Qed.
Lemma lem1949414 : term312 = term293.
Proof. exact (@lem706885). Qed.
Lemma lem1949415 : (term312 = term293) = (term313 = term291).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term293). Qed.
Lemma lem1949416 : term313 = term291.
Proof. exact (EQ_MP (@lem1949415) (@lem1949414)). Qed.
Lemma lem1949417 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1949418 : term314 = term296.
Proof. exact (MK_COMB (@lem1949417) (@lem1949416)). Qed.
Lemma lem1949419 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1949420 : term311 = term315.
Proof. exact (MK_COMB (@lem1949419) (@lem1949418)). Qed.
Lemma lem1949421 : term310 = term315.
Proof. exact (TRANS (@lem1949413) (@lem1949420)). Qed.
Lemma lem1949422 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1949423 : term316 = term317.
Proof. exact (MK_COMB (@lem1949422) (@lem1949421)). Qed.
Lemma lem1949424 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1949425 (x : real) : (term309 x) = (term318 x).
Proof. exact (MK_COMB (@lem1949423) (@lem1949424 x)). Qed.
Lemma lem1949426 (x : real) : (term308 x) = (term318 x).
Proof. exact (TRANS (@lem1949412 x) (@lem1949425 x)). Qed.
Lemma lem1949427 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1949428 (x : real) : (term319 x) = (term320 x).
Proof. exact (MK_COMB (@lem1949427) (@lem1949426 x)). Qed.
Lemma lem1949429 (y : real) : (term286 y) = (term257 y).
Proof. exact (@lem1483442 term258 y). Qed.
Lemma lem1949431 (m : nat) : (term259 m) = term77.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1949432 : term260 = term77.
Proof. exact (@lem1949431 term82). Qed.
Lemma lem1949433 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1949434 : term261 = term262.
Proof. exact (MK_COMB (@lem1949433) (@lem1949432)). Qed.
Lemma lem1949435 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1949436 (y : real) : (term257 y) = (term263 y).
Proof. exact (MK_COMB (@lem1949434) (@lem1949435 y)). Qed.
Lemma lem1949437 (y : real) : (term286 y) = (term263 y).
Proof. exact (TRANS (@lem1949429 y) (@lem1949436 y)). Qed.
Lemma lem1949438 (y : real) : (term263 y) = term77.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1949439 (y : real) : (term286 y) = term77.
Proof. exact (TRANS (@lem1949437 y) (@lem1949438 y)). Qed.
Lemma lem1949440 (y : real) (x : real) : (term307 x y) = (term321 x).
Proof. exact (MK_COMB (@lem1949428 x) (@lem1949439 y)). Qed.
Lemma lem1949441 (y : real) (x : real) : (term306 x y) = (term321 x).
Proof. exact (TRANS (@lem1949411 x y) (@lem1949440 y x)). Qed.
Lemma lem1949442 (x : real) : (term321 x) = (term318 x).
Proof. exact (@lem1483450 (term318 x)). Qed.
Lemma lem1949443 (y : real) (x : real) : (term306 x y) = (term318 x).
Proof. exact (TRANS (@lem1949441 y x) (@lem1949442 x)). Qed.
Lemma lem1949444 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1949445 (y : real) (x : real) : (term322 x y) = (term323 x).
Proof. exact (MK_COMB (@lem1949444) (@lem1949443 y x)). Qed.
Lemma lem1949446 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949447 (y : real) (x : real) : (term305 x y) = (term324 x).
Proof. exact (MK_COMB (@lem1949445 y x) (@lem1949446)). Qed.
Lemma lem1949448 (x : real) (y : real) (h1 : term223 x y) : term324 x.
Proof. exact (EQ_MP (@lem1949447 y x) (@lem1949410 x y h1)). Qed.
Lemma lem1949450 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1949451 : term230 = term231.
Proof. exact (@lem1949450 (NUMERAL 0) term82). Qed.
Lemma lem1949452 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1949453 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1949454 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1949453 h1) (fun h1 : term231 = True => @lem1949452)). Qed.
Lemma lem1949455 : term231 = True.
Proof. exact (EQ_MP (@lem1949454) (@lem1949452)). Qed.
Lemma lem1949456 : term230 = True.
Proof. exact (TRANS (@lem1949451) (@lem1949455)). Qed.
Lemma lem1949457 : True = term230.
Proof. exact (SYM (@lem1949456)). Qed.
Lemma lem1949458 : term230.
Proof. exact (EQ_MP (@lem1949457) (@lem0)). Qed.
Lemma lem1949459 (x : real) (y : real) (h1 : term223 x y) : term325 x.
Proof. exact (conj (@lem1949458) (@lem1949448 x y h1)). Qed.
Lemma lem1949461 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1949462 (x : real) : term326 x.
Proof. exact (@lem1949461 term236 (term318 x)). Qed.
Lemma lem1949463 (x : real) (y : real) (h1 : term223 x y) : term327 x.
Proof. exact (@lem1949462 x (@lem1949459 x y h1)). Qed.
Lemma lem1949464 (x : real) : (term328 x) = (term318 x).
Proof. exact (@lem1483460 (term318 x)). Qed.
Lemma lem1949465 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1949466 (x : real) : (term329 x) = (term323 x).
Proof. exact (MK_COMB (@lem1949465) (@lem1949464 x)). Qed.
Lemma lem1949467 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949468 (x : real) : (term327 x) = (term324 x).
Proof. exact (MK_COMB (@lem1949466 x) (@lem1949467)). Qed.
Lemma lem1949469 (x : real) (y : real) (h1 : term223 x y) : term324 x.
Proof. exact (EQ_MP (@lem1949468 x) (@lem1949463 x y h1)). Qed.
Lemma lem1949470 (x : real) (y : real) (h1 : term223 x y) : term330 x.
Proof. exact (conj (@lem1949469 x y h1) (@lem1949363 x y h1)). Qed.
Lemma lem1949472 (x : real) (y : real) : term267 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1949473 (x : real) : term331 x.
Proof. exact (@lem1949472 (term318 x) (term332 x)). Qed.
Lemma lem1949474 (x : real) (y : real) (h1 : term223 x y) : term333 x.
Proof. exact (@lem1949473 x (@lem1949470 x y h1)). Qed.
Lemma lem1949475 (x : real) : (term334 x) = (term335 x).
Proof. exact (@lem1483438 term315 term296 x). Qed.
Lemma lem1949477 (m : nat) : (term259 m) = term77.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1949478 : term336 = term77.
Proof. exact (@lem1949477 term291). Qed.
Lemma lem1949479 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1949480 : term337 = term262.
Proof. exact (MK_COMB (@lem1949479) (@lem1949478)). Qed.
Lemma lem1949481 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1949482 (x : real) : (term335 x) = (term263 x).
Proof. exact (MK_COMB (@lem1949480) (@lem1949481 x)). Qed.
Lemma lem1949483 (x : real) : (term334 x) = (term263 x).
Proof. exact (TRANS (@lem1949475 x) (@lem1949482 x)). Qed.
Lemma lem1949484 (x : real) : (term263 x) = term77.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1949485 (x : real) : (term334 x) = term77.
Proof. exact (TRANS (@lem1949483 x) (@lem1949484 x)). Qed.
Lemma lem1949486 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1949487 (x : real) : (term338 x) = term271.
Proof. exact (MK_COMB (@lem1949486) (@lem1949485 x)). Qed.
Lemma lem1949488 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949489 (x : real) : (term333 x) = term272.
Proof. exact (MK_COMB (@lem1949487 x) (@lem1949488)). Qed.
Lemma lem1949490 (x : real) (y : real) (h1 : term223 x y) : term272.
Proof. exact (EQ_MP (@lem1949489 x) (@lem1949474 x y h1)). Qed.
Lemma lem1949492 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1949493 : term272 = term273.
Proof. exact (@lem1949492 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1949494 : term273 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1949495 : term272 = False.
Proof. exact (TRANS (@lem1949493) (@lem1949494)). Qed.
Lemma lem1949496 (x : real) (y : real) (h1 : term223 x y) : False.
Proof. exact (EQ_MP (@lem1949495) (@lem1949490 x y h1)). Qed.
Lemma lem1949497 (x : real) (y : real) (h1 : term225 x y) : False.
Proof. exact (or_elim (@lem1949237 x y h1) (fun h0 : term191 x y => @lem1949333 x y h0) (fun h0 : term223 x y => @lem1949496 x y h0)). Qed.
Lemma lem1949498 (x : real) (y : real) (h1 : term227 x y) : False.
Proof. exact (or_elim (@lem1949093 x y h1) (fun h0 : term228 x y => @lem1949236 x y h0) (fun h0 : term225 x y => @lem1949497 x y h0)). Qed.
Lemma lem1949499 (x : real) (y : real) (h1 : term115 x y) : term115 x y.
Proof. exact (h1). Qed.
Lemma lem1949500 (x : real) (y : real) (h1 : term115 x y) : term227 x y.
Proof. exact (EQ_MP (@lem1949092 x y) (@lem1949499 x y h1)). Qed.
Lemma lem1949501 (x : real) (y : real) (h1 : term115 x y) : (term227 x y) = False.
Proof. exact (prop_ext (fun h2 : term227 x y => @lem1949498 x y h2) (fun h2 : False => @lem1949500 x y h1)). Qed.
Lemma lem1949502 (x : real) (y : real) (h1 : term115 x y) : False.
Proof. exact (EQ_MP (@lem1949501 x y h1) (@lem1949500 x y h1)). Qed.
Lemma lem1949503 (x : real) (y : real) (h1 : term74 x y) : term74 x y.
Proof. exact (h1). Qed.
Lemma lem1949504 (x : real) (y : real) (h1 : term74 x y) : term115 x y.
Proof. exact (EQ_MP (@lem1948781 x y) (@lem1949503 x y h1)). Qed.
Lemma lem1949505 (x : real) (y : real) (h1 : term74 x y) : (term115 x y) = False.
Proof. exact (prop_ext (fun h2 : term115 x y => @lem1949502 x y h2) (fun h2 : False => @lem1949504 x y h1)). Qed.
Lemma lem1949506 (x : real) (y : real) (h1 : term74 x y) : False.
Proof. exact (EQ_MP (@lem1949505 x y h1) (@lem1949504 x y h1)). Qed.
Lemma lem1949507 (x : real) (y : real) : term339 x y.
Proof. exact (fun h0 : term74 x y => @lem1949506 x y h0). Qed.
Lemma lem1949508 (x : real) (y : real) : term340 x y.
Proof. exact (@lem1386578 (term341 x y)). Qed.
Lemma lem1949509 (x : real) (y : real) : term341 x y.
Proof. exact (@lem1949508 x y (@lem1949507 x y)). Qed.
Lemma lem1949510 (y : real) (x : real) (h1 : term30 x) : term75 x y.
Proof. exact (@lem1949509 x y (@lem1948576 x h1)). Qed.
Lemma lem1949511 (x : real) (y : real) (h1 : term30 x) (h2 : real_lt x y) : term65 x y.
Proof. exact (@lem1949510 y x h1 (@lem1948575 x y h2)). Qed.
Lemma lem1949512 (x : real) (y : real) (h1 : term30 x) (h2 : real_lt x y) : term64 x y.
Proof. exact (EQ_MP (@lem1948610 x y) (@lem1949511 x y h1 h2)). Qed.
Lemma lem1949513 (x : real) (y : real) (h1 : term30 x) (h2 : real_lt x y) : term342 x y.
Proof. exact (ex_intro (term343 x y) term291 (@lem1949512 x y h1 h2)). Qed.
Lemma lem1949514 (x : real) (y : real) (h1 : term30 x) (h2 : real_lt x y) : term344 x y.
Proof. exact (@lem1948579 x y (@lem1949513 x y h1 h2)). Qed.
Lemma lem1949515 (x : real) (y : real) (h1 : term51 x y) : real_lt x y.
Proof. exact (proj2 (@lem1948574 x y h1)). Qed.
Lemma lem1949516 (x : real) (y : real) (h1 : term51 x y) : term30 x.
Proof. exact (proj1 (@lem1948574 x y h1)). Qed.
Lemma lem1949517 (x : real) (y : real) (h1 : term30 x) (h2 : real_lt x y) : (real_lt x y) = (term344 x y).
Proof. exact (prop_ext (fun h3 : real_lt x y => @lem1949514 x y h1 h2) (fun h3 : term344 x y => @lem1948575 x y h2)). Qed.
Lemma lem1949518 (x : real) (y : real) (h1 : term30 x) (h2 : real_lt x y) : term344 x y.
Proof. exact (EQ_MP (@lem1949517 x y h1 h2) (@lem1948575 x y h2)). Qed.
Lemma lem1949519 (x : real) (y : real) (h1 : term30 x) (h2 : real_lt x y) : (term30 x) = (term344 x y).
Proof. exact (prop_ext (fun h3 : term30 x => @lem1949518 x y h1 h2) (fun h3 : term344 x y => @lem1948576 x h1)). Qed.
Lemma lem1949520 (x : real) (y : real) (h1 : term30 x) (h2 : real_lt x y) : term344 x y.
Proof. exact (EQ_MP (@lem1949519 x y h1 h2) (@lem1948576 x h1)). Qed.
Lemma lem1949521 (y : real) (x : real) (h1 : term51 x y) (h2 : term30 x) : (real_lt x y) = (term344 x y).
Proof. exact (prop_ext (fun h3 : real_lt x y => @lem1949520 x y h2 h3) (fun h3 : term344 x y => @lem1949515 x y h1)). Qed.
Lemma lem1949522 (y : real) (x : real) (h1 : term51 x y) (h2 : term30 x) : term344 x y.
Proof. exact (EQ_MP (@lem1949521 y x h1 h2) (@lem1949515 x y h1)). Qed.
Lemma lem1949523 (x : real) (y : real) (h1 : term51 x y) : (term30 x) = (term344 x y).
Proof. exact (prop_ext (fun h2 : term30 x => @lem1949522 y x h1 h2) (fun h2 : term344 x y => @lem1949516 x y h1)). Qed.
Lemma lem1949524 (x : real) (y : real) (h1 : term51 x y) : term344 x y.
Proof. exact (EQ_MP (@lem1949523 x y h1) (@lem1949516 x y h1)). Qed.
Lemma lem1949525 (x : real) (y : real) : term345 x y.
Proof. exact (fun h0 : term51 x y => @lem1949524 x y h0). Qed.
Lemma lem1949530 (x : real) : term346 x.
Proof. exact (fun y : real => @lem1949525 x y). Qed.
Lemma lem1949535 : term50.
Proof. exact (fun x : real => @lem1949530 x). Qed.
Lemma lem1949536 (x : real) (y : real) (h1 : real_lt x y) : real_lt x y.
Proof. exact (h1). Qed.
Lemma lem1949537 (x : real) (h1 : term50) : term347 x.
Proof. exact (@lem1948573 h1 x). Qed.
Lemma lem1949538 (x : real) : (term347 x) = (term346 x).
Proof. exact (eq_refl (term347 x)). Qed.
Lemma lem1949539 (x : real) (h1 : term50) : term346 x.
Proof. exact (EQ_MP (@lem1949538 x) (@lem1949537 x h1)). Qed.
Lemma lem1949540 (x : real) (y : real) (h1 : term50) : term348 x y.
Proof. exact (@lem1949539 x h1 y). Qed.
Lemma lem1949541 (x : real) (y : real) : (term348 x y) = (term345 x y).
Proof. exact (eq_refl (term348 x y)). Qed.
Lemma lem1949542 (x : real) (y : real) (h1 : term50) : term345 x y.
Proof. exact (EQ_MP (@lem1949541 x y) (@lem1949540 x y h1)). Qed.
Lemma lem1949543 (x : real) (y : real) (h1 : term51 x y) : term51 x y.
Proof. exact (h1). Qed.
Lemma lem1949544 (x : real) (y : real) (h1 : term50) (h2 : term51 x y) : term344 x y.
Proof. exact (@lem1949542 x y h1 (@lem1949543 x y h2)). Qed.
Lemma lem1949545 (x : real) (y : real) : (term344 x y) = ((term344 x y) = True).
Proof. exact (@lem7 (term344 x y)). Qed.
Lemma lem1949546 (x : real) (y : real) (h1 : term50) (h2 : term51 x y) : (term344 x y) = True.
Proof. exact (EQ_MP (@lem1949545 x y) (@lem1949544 x y h1 h2)). Qed.
Lemma lem1949552 (x : real) (y : real) : (real_lt x y) = ((real_lt x y) = True).
Proof. exact (@lem7 (real_lt x y)). Qed.
Lemma lem1949554 (x : real) : (term30 x) = ((term30 x) = True).
Proof. exact (@lem7 (term30 x)). Qed.
Lemma lem1949557 (x : real) (y : real) (h1 : term50) : term349 x y.
Proof. exact (fun h0 : term51 x y => @lem1949546 x y h1 h0). Qed.
Lemma lem1949561 (x : real) (h1 : term30 x) : (term30 x) = True.
Proof. exact (EQ_MP (@lem1949554 x) (@lem1948543 x h1)). Qed.
Lemma lem1949562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1949563 (x : real) (h1 : term30 x) : (term58 x) = (and True).
Proof. exact (MK_COMB (@lem1949562) (@lem1949561 x h1)). Qed.
Lemma lem1949565 (x : real) (y : real) (h1 : real_lt x y) : (real_lt x y) = True.
Proof. exact (EQ_MP (@lem1949552 x y) (@lem1949536 x y h1)). Qed.
Lemma lem1949566 (x : real) (y : real) (h1 : term30 x) (h2 : real_lt x y) : (term51 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1949563 x h1) (@lem1949565 x y h2)). Qed.
Lemma lem1949568 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1949569 : (True /\ True) = True.
Proof. exact (@lem1949568 True). Qed.
Lemma lem1949570 (x : real) (y : real) (h1 : term30 x) (h2 : real_lt x y) : (term51 x y) = True.
Proof. exact (TRANS (@lem1949566 x y h1 h2) (@lem1949569)). Qed.
Lemma lem1949571 (x : real) (y : real) (h1 : term30 x) (h2 : real_lt x y) : True = (term51 x y).
Proof. exact (SYM (@lem1949570 x y h1 h2)). Qed.
Lemma lem1949572 (x : real) (y : real) (h1 : term30 x) (h2 : real_lt x y) : term51 x y.
Proof. exact (EQ_MP (@lem1949571 x y h1 h2) (@lem0)). Qed.
Lemma lem1949573 (x : real) (y : real) (h1 : term50) (h2 : term30 x) (h3 : real_lt x y) : (term344 x y) = True.
Proof. exact (@lem1949557 x y h1 (@lem1949572 x y h2 h3)). Qed.
Lemma lem1949574 (x : real) (y : real) (h1 : term50) (h2 : term30 x) (h3 : real_lt x y) : True = (term344 x y).
Proof. exact (SYM (@lem1949573 x y h1 h2 h3)). Qed.
Lemma lem1949575 (x : real) (y : real) (h1 : term50) (h2 : term30 x) (h3 : real_lt x y) : term344 x y.
Proof. exact (EQ_MP (@lem1949574 x y h1 h2 h3) (@lem0)). Qed.
Lemma lem1949614 (x : real) (z : real) : term23 x z.
Proof. exact (EQ_MP (@lem1948533 x z) (@lem1948532 x z)). Qed.
Lemma lem1949615 (x : real) (y : real) : term350 x y.
Proof. exact (@lem1949614 (sqrt x) (sqrt y)). Qed.
Lemma lem1949616 (x : real) : term53 x.
Proof. exact (@lem1948346 x). Qed.
Lemma lem1949617 (x : real) : (term53 x) = ((term54 x) = (term30 x)).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1949619 (x : real) : term351 x.
Proof. exact (@lem1948506 x). Qed.
Lemma lem1949620 (x : real) : (term351 x) = (term7 x).
Proof. exact (eq_refl (term351 x)). Qed.
Lemma lem1949621 (x : real) : term7 x.
Proof. exact (EQ_MP (@lem1949620 x) (@lem1949619 x)). Qed.
Lemma lem1949622 (x : real) (y : real) : term352 x y.
Proof. exact (@lem1949621 x y). Qed.
Lemma lem1949623 (x : real) (y : real) : (term352 x y) = ((real_lt y x) = (term3 x y)).
Proof. exact (eq_refl (term352 x y)). Qed.
Lemma lem1949635 (x : real) : term353 x.
Proof. exact (@lem82 (term30 x)). Qed.
Lemma lem1949637 (y : real) : (term30 y) = ((term30 y) = True).
Proof. exact (@lem7 (term30 y)). Qed.
Lemma lem1949642 (x : real) (y : real) : (real_lt y x) = (term3 x y).
Proof. exact (EQ_MP (@lem1949623 x y) (@lem1949622 x y)). Qed.
Lemma lem1949643 (x : real) : (term354 x) = (term355 x).
Proof. exact (@lem1949642 term77 (sqrt x)). Qed.
Lemma lem1949645 (x : real) : (term54 x) = (term30 x).
Proof. exact (EQ_MP (@lem1949617 x) (@lem1949616 x)). Qed.
Lemma lem1949647 (x : real) (h1 : term32 x) : (term30 x) = False.
Proof. exact (@lem1949635 x (@lem1948544 x h1)). Qed.
Lemma lem1949648 (x : real) (h1 : term32 x) : (term54 x) = False.
Proof. exact (TRANS (@lem1949645 x) (@lem1949647 x h1)). Qed.
Lemma lem1949649 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1949650 (x : real) (h1 : term32 x) : (term355 x) = (~ False).
Proof. exact (MK_COMB (@lem1949649) (@lem1949648 x h1)). Qed.
Lemma lem1949652 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1949653 (x : real) (h1 : term32 x) : (term355 x) = True.
Proof. exact (TRANS (@lem1949650 x h1) (@lem1949652)). Qed.
Lemma lem1949654 (x : real) (h1 : term32 x) : (term354 x) = True.
Proof. exact (TRANS (@lem1949643 x) (@lem1949653 x h1)). Qed.
Lemma lem1949655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1949656 (x : real) (h1 : term32 x) : (term356 x) = (and True).
Proof. exact (MK_COMB (@lem1949655) (@lem1949654 x h1)). Qed.
Lemma lem1949658 (x : real) : (term54 x) = (term30 x).
Proof. exact (EQ_MP (@lem1949617 x) (@lem1949616 x)). Qed.
Lemma lem1949659 (y : real) : (term54 y) = (term30 y).
Proof. exact (@lem1949658 y). Qed.
Lemma lem1949661 (y : real) (h1 : term30 y) : (term30 y) = True.
Proof. exact (EQ_MP (@lem1949637 y) (@lem1948538 y h1)). Qed.
Lemma lem1949662 (y : real) (h1 : term30 y) : (term54 y) = True.
Proof. exact (TRANS (@lem1949659 y) (@lem1949661 y h1)). Qed.
Lemma lem1949663 (x : real) (y : real) (h1 : term32 x) (h2 : term30 y) : (term357 x y) = (True /\ True).
Proof. exact (MK_COMB (@lem1949656 x h1) (@lem1949662 y h2)). Qed.
Lemma lem1949665 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1949666 : (True /\ True) = True.
Proof. exact (@lem1949665 True). Qed.
Lemma lem1949667 (x : real) (y : real) (h1 : term32 x) (h2 : term30 y) : (term357 x y) = True.
Proof. exact (TRANS (@lem1949663 x y h1 h2) (@lem1949666)). Qed.
Lemma lem1949668 (x : real) (y : real) (h1 : term32 x) (h2 : term30 y) : True = (term357 x y).
Proof. exact (SYM (@lem1949667 x y h1 h2)). Qed.
Lemma lem1949669 (x : real) (y : real) (h1 : term32 x) (h2 : term30 y) : term357 x y.
Proof. exact (EQ_MP (@lem1949668 x y h1 h2) (@lem0)). Qed.
Lemma lem1949670 (x : real) (y : real) (h1 : term32 x) (h2 : term30 y) : term358 x y.
Proof. exact (ex_intro (term359 x y) term77 (@lem1949669 x y h1 h2)). Qed.
Lemma lem1949671 (x : real) (y : real) (h1 : term32 x) (h2 : term30 y) : term344 x y.
Proof. exact (@lem1949615 x y (@lem1949670 x y h1 h2)). Qed.
Lemma lem1949672 (y : real) (h1 : term50) : term360 y.
Proof. exact (@lem1948573 h1 (real_neg y)). Qed.
Lemma lem1949673 (y : real) : (term360 y) = (term361 y).
Proof. exact (eq_refl (term360 y)). Qed.
Lemma lem1949674 (y : real) (h1 : term50) : term361 y.
Proof. exact (EQ_MP (@lem1949673 y) (@lem1949672 y h1)). Qed.
Lemma lem1949675 (y : real) (x : real) (h1 : term50) : term362 y x.
Proof. exact (@lem1949674 y h1 (real_neg x)). Qed.
Lemma lem1949676 (y : real) (x : real) : (term362 y x) = (term363 y x).
Proof. exact (eq_refl (term362 y x)). Qed.
Lemma lem1949677 (y : real) (x : real) (h1 : term50) : term363 y x.
Proof. exact (EQ_MP (@lem1949676 y x) (@lem1949675 y x h1)). Qed.
Lemma lem1949685 (x : real) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem1948491 x) (@lem1948490 x)). Qed.
Lemma lem1949686 (y : real) : (term1 y) = (term2 y).
Proof. exact (@lem1949685 y). Qed.
Lemma lem1949687 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1949688 (y : real) : (term364 y) = (term365 y).
Proof. exact (MK_COMB (@lem1949687) (@lem1949686 y)). Qed.
Lemma lem1949690 (x : real) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem1948491 x) (@lem1948490 x)). Qed.
Lemma lem1949691 (y : real) (x : real) : (term366 y x) = (term367 y x).
Proof. exact (MK_COMB (@lem1949688 y) (@lem1949690 x)). Qed.
Lemma lem1949692 (y : real) (x : real) : (term368 y x) = (term368 y x).
Proof. exact (eq_refl (term368 y x)). Qed.
Lemma lem1949693 (y : real) (x : real) : (term363 y x) = (term369 y x).
Proof. exact (MK_COMB (@lem1949692 y x) (@lem1949691 y x)). Qed.
Lemma lem1949696 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1949697 (y : real) (x : real) : (term370 y x) = (term371 y x).
Proof. exact (MK_COMB (@lem1949696) (@lem1949693 y x)). Qed.
Lemma lem1949698 (x : real) (y : real) : (term344 x y) = (term344 x y).
Proof. exact (eq_refl (term344 x y)). Qed.
Lemma lem1949699 (x : real) (y : real) : (term372 x y) = (term373 x y).
Proof. exact (MK_COMB (@lem1949697 y x) (@lem1949698 x y)). Qed.
Lemma lem1949702 (x : real) (y : real) : (term373 x y) = (term372 x y).
Proof. exact (SYM (@lem1949699 x y)). Qed.
Lemma lem1949727 (y : real) (x : real) : (term374 y x) = (term375 y x).
Proof. exact (@lem17045 (term376 y) (term377 y x)). Qed.
Lemma lem1949728 (y : real) (x : real) : (term367 y x) = (term367 y x).
Proof. exact (eq_refl (term367 y x)). Qed.
Lemma lem1949729 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1949730 (y : real) (x : real) : (term378 y x) = (term379 y x).
Proof. exact (MK_COMB (@lem1949729) (@lem1949727 y x)). Qed.
Lemma lem1949731 (y : real) (x : real) : (term380 y x) = (term381 y x).
Proof. exact (MK_COMB (@lem1949730 y x) (@lem1949728 y x)). Qed.
Lemma lem1949732 (y : real) (x : real) : (term369 y x) = (term380 y x).
Proof. exact (@lem17265 (term382 y x) (term367 y x)). Qed.
Lemma lem1949733 (y : real) (x : real) : (term369 y x) = (term381 y x).
Proof. exact (TRANS (@lem1949732 y x) (@lem1949731 y x)). Qed.
Lemma lem1949734 (x : real) (y : real) : (term383 x y) = (term383 x y).
Proof. exact (eq_refl (term383 x y)). Qed.
Lemma lem1949735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1949736 (y : real) (x : real) : (term384 y x) = (term385 y x).
Proof. exact (MK_COMB (@lem1949735) (@lem1949733 y x)). Qed.
Lemma lem1949737 (x : real) (y : real) : (term386 x y) = (term387 x y).
Proof. exact (MK_COMB (@lem1949736 y x) (@lem1949734 x y)). Qed.
Lemma lem1949738 (x : real) (y : real) : (term388 x y) = (term386 x y).
Proof. exact (@lem17362 (term369 y x) (term344 x y)). Qed.
Lemma lem1949739 (x : real) (y : real) : (term388 x y) = (term387 x y).
Proof. exact (TRANS (@lem1949738 x y) (@lem1949737 x y)). Qed.
Lemma lem1949741 (y : real) : (term389 y) = (term389 y).
Proof. exact (eq_refl (term389 y)). Qed.
Lemma lem1949742 (x : real) (y : real) : (term390 x y) = (term391 x y).
Proof. exact (MK_COMB (@lem1949741 y) (@lem1949739 x y)). Qed.
Lemma lem1949743 (x : real) (y : real) : (term392 x y) = (term390 x y).
Proof. exact (@lem17362 (term32 y) (term373 x y)). Qed.
Lemma lem1949744 (x : real) (y : real) : (term392 x y) = (term391 x y).
Proof. exact (TRANS (@lem1949743 x y) (@lem1949742 x y)). Qed.
Lemma lem1949746 (x : real) : (term389 x) = (term389 x).
Proof. exact (eq_refl (term389 x)). Qed.
Lemma lem1949747 (x : real) (y : real) : (term393 x y) = (term394 x y).
Proof. exact (MK_COMB (@lem1949746 x) (@lem1949744 x y)). Qed.
Lemma lem1949748 (x : real) (y : real) : (term395 x y) = (term393 x y).
Proof. exact (@lem17362 (term32 x) (term396 x y)). Qed.
Lemma lem1949749 (x : real) (y : real) : (term395 x y) = (term394 x y).
Proof. exact (TRANS (@lem1949748 x y) (@lem1949747 x y)). Qed.
Lemma lem1949751 (x : real) (y : real) : (term68 x y) = (term68 x y).
Proof. exact (eq_refl (term68 x y)). Qed.
Lemma lem1949752 (x : real) (y : real) : (term397 x y) = (term398 x y).
Proof. exact (MK_COMB (@lem1949751 x y) (@lem1949749 x y)). Qed.
Lemma lem1949753 (x : real) (y : real) : (term399 x y) = (term397 x y).
Proof. exact (@lem17362 (real_lt x y) (term400 x y)). Qed.
Lemma lem1949791 (x : real) (y : real) : (term399 x y) = (term398 x y).
Proof. exact (TRANS (@lem1949753 x y) (@lem1949752 x y)). Qed.
Lemma lem1949792 (y : real) (x : real) : (real_lt x y) = (term86 y x).
Proof. exact (@lem1483521 y x). Qed.
Lemma lem1949798 (y : real) (x : real) : (real_sub y x) = (term87 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1949803 (x : real) (y : real) : (term87 y x) = (term88 x y).
Proof. exact (@lem1483488 (term89 x) y). Qed.
Lemma lem1949805 (x : real) (y : real) : (real_sub y x) = (term88 x y).
Proof. exact (TRANS (@lem1949798 y x) (@lem1949803 x y)). Qed.
Lemma lem1949806 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1949807 (x : real) (y : real) : (term90 y x) = (term91 x y).
Proof. exact (MK_COMB (@lem1949806) (@lem1949805 x y)). Qed.
Lemma lem1949808 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949809 (x : real) (y : real) : (term86 y x) = (term92 x y).
Proof. exact (MK_COMB (@lem1949807 x y) (@lem1949808)). Qed.
Lemma lem1949810 (x : real) (y : real) : (real_lt x y) = (term92 x y).
Proof. exact (TRANS (@lem1949792 y x) (@lem1949809 x y)). Qed.
Lemma lem1949811 (x : real) : (term32 x) = (term93 x).
Proof. exact (@lem1483533 term77 x). Qed.
Lemma lem1949817 (x : real) : (term94 x) = (term95 x).
Proof. exact (@lem1483519 term77 x). Qed.
Lemma lem1949822 (x : real) : (term95 x) = (term89 x).
Proof. exact (@lem1483448 (term89 x)). Qed.
Lemma lem1949824 (x : real) : (term94 x) = (term89 x).
Proof. exact (TRANS (@lem1949817 x) (@lem1949822 x)). Qed.
Lemma lem1949825 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1949826 (x : real) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem1949825) (@lem1949824 x)). Qed.
Lemma lem1949827 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949828 (x : real) : (term93 x) = (term98 x).
Proof. exact (MK_COMB (@lem1949826 x) (@lem1949827)). Qed.
Lemma lem1949829 (x : real) : (term32 x) = (term98 x).
Proof. exact (TRANS (@lem1949811 x) (@lem1949828 x)). Qed.
Lemma lem1949830 (y : real) : (term32 y) = (term93 y).
Proof. exact (@lem1483533 term77 y). Qed.
Lemma lem1949836 (y : real) : (term94 y) = (term95 y).
Proof. exact (@lem1483519 term77 y). Qed.
Lemma lem1949841 (y : real) : (term95 y) = (term89 y).
Proof. exact (@lem1483448 (term89 y)). Qed.
Lemma lem1949843 (y : real) : (term94 y) = (term89 y).
Proof. exact (TRANS (@lem1949836 y) (@lem1949841 y)). Qed.
Lemma lem1949844 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1949845 (y : real) : (term96 y) = (term97 y).
Proof. exact (MK_COMB (@lem1949844) (@lem1949843 y)). Qed.
Lemma lem1949846 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949847 (y : real) : (term93 y) = (term98 y).
Proof. exact (MK_COMB (@lem1949845 y) (@lem1949846)). Qed.
Lemma lem1949848 (y : real) : (term32 y) = (term98 y).
Proof. exact (TRANS (@lem1949830 y) (@lem1949847 y)). Qed.
Lemma lem1949849 (y : real) : (term401 y) = (term402 y).
Proof. exact (@lem1483533 term77 (real_neg y)). Qed.
Lemma lem1949856 (y : real) : (real_neg y) = (term89 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1949859 : term403 = term403.
Proof. exact (eq_refl term403). Qed.
Lemma lem1949860 (y : real) : (term404 y) = (term405 y).
Proof. exact (MK_COMB (@lem1949859) (@lem1949856 y)). Qed.
Lemma lem1949861 (y : real) : (term405 y) = (term406 y).
Proof. exact (@lem1483519 term77 (term89 y)). Qed.
Lemma lem1949862 (y : real) : (term407 y) = (term408 y).
Proof. exact (@lem1483476 term258 term258 y). Qed.
Lemma lem1949864 (m : nat) (n : nat) : (term409 m n) = (term410 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1949865 : term411 = term412.
Proof. exact (@lem1949864 term82 term82). Qed.
Lemma lem1949866 : (term413 = (BIT1 0)) = (term414 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1949867 : term414 = term82.
Proof. exact (EQ_MP (@lem1949866) (@lem940073)). Qed.
Lemma lem1949868 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1949869 : term412 = term236.
Proof. exact (MK_COMB (@lem1949868) (@lem1949867)). Qed.
Lemma lem1949870 : term411 = term236.
Proof. exact (TRANS (@lem1949865) (@lem1949869)). Qed.
Lemma lem1949871 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1949872 : term415 = term416.
Proof. exact (MK_COMB (@lem1949871) (@lem1949870)). Qed.
Lemma lem1949873 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1949874 (y : real) : (term408 y) = (term121 y).
Proof. exact (MK_COMB (@lem1949872) (@lem1949873 y)). Qed.
Lemma lem1949875 (y : real) : (term407 y) = (term121 y).
Proof. exact (TRANS (@lem1949862 y) (@lem1949874 y)). Qed.
Lemma lem1949876 (y : real) : (term121 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1949877 (y : real) : (term407 y) = y.
Proof. exact (TRANS (@lem1949875 y) (@lem1949876 y)). Qed.
Lemma lem1949878 : term285 = term285.
Proof. exact (eq_refl term285). Qed.
Lemma lem1949879 (y : real) : (term406 y) = (term417 y).
Proof. exact (MK_COMB (@lem1949878) (@lem1949877 y)). Qed.
Lemma lem1949880 (y : real) : (term417 y) = y.
Proof. exact (@lem1483448 y). Qed.
Lemma lem1949881 (y : real) : (term406 y) = y.
Proof. exact (TRANS (@lem1949879 y) (@lem1949880 y)). Qed.
Lemma lem1949882 (y : real) : (term405 y) = y.
Proof. exact (TRANS (@lem1949861 y) (@lem1949881 y)). Qed.
Lemma lem1949883 (y : real) : (term404 y) = y.
Proof. exact (TRANS (@lem1949860 y) (@lem1949882 y)). Qed.
Lemma lem1949884 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1949885 (y : real) : (term418 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1949884) (@lem1949883 y)). Qed.
Lemma lem1949886 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949887 (y : real) : (term402 y) = (term419 y).
Proof. exact (MK_COMB (@lem1949885 y) (@lem1949886)). Qed.
Lemma lem1949888 (y : real) : (term401 y) = (term419 y).
Proof. exact (TRANS (@lem1949849 y) (@lem1949887 y)). Qed.
Lemma lem1949889 (y : real) (x : real) : (term420 y x) = (term421 y x).
Proof. exact (@lem1483531 (real_neg y) (real_neg x)). Qed.
Lemma lem1949896 (x : real) : (real_neg x) = (term89 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1949903 (y : real) : (real_neg y) = (term89 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1949904 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1949905 (y : real) : (term422 y) = (term423 y).
Proof. exact (MK_COMB (@lem1949904) (@lem1949903 y)). Qed.
Lemma lem1949906 (y : real) (x : real) : (term424 y x) = (term425 y x).
Proof. exact (MK_COMB (@lem1949905 y) (@lem1949896 x)). Qed.
Lemma lem1949907 (y : real) (x : real) : (term425 y x) = (term426 y x).
Proof. exact (@lem1483519 (term89 y) (term89 x)). Qed.
Lemma lem1949908 (x : real) : (term407 x) = (term408 x).
Proof. exact (@lem1483476 term258 term258 x). Qed.
Lemma lem1949910 (m : nat) (n : nat) : (term409 m n) = (term410 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1949911 : term411 = term412.
Proof. exact (@lem1949910 term82 term82). Qed.
Lemma lem1949912 : (term413 = (BIT1 0)) = (term414 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1949913 : term414 = term82.
Proof. exact (EQ_MP (@lem1949912) (@lem940073)). Qed.
Lemma lem1949914 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1949915 : term412 = term236.
Proof. exact (MK_COMB (@lem1949914) (@lem1949913)). Qed.
Lemma lem1949916 : term411 = term236.
Proof. exact (TRANS (@lem1949911) (@lem1949915)). Qed.
Lemma lem1949917 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1949918 : term415 = term416.
Proof. exact (MK_COMB (@lem1949917) (@lem1949916)). Qed.
Lemma lem1949919 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1949920 (x : real) : (term408 x) = (term121 x).
Proof. exact (MK_COMB (@lem1949918) (@lem1949919 x)). Qed.
Lemma lem1949921 (x : real) : (term407 x) = (term121 x).
Proof. exact (TRANS (@lem1949908 x) (@lem1949920 x)). Qed.
Lemma lem1949922 (x : real) : (term121 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1949923 (x : real) : (term407 x) = x.
Proof. exact (TRANS (@lem1949921 x) (@lem1949922 x)). Qed.
Lemma lem1949924 (y : real) : (term196 y) = (term196 y).
Proof. exact (eq_refl (term196 y)). Qed.
Lemma lem1949925 (y : real) (x : real) : (term426 y x) = (term88 y x).
Proof. exact (MK_COMB (@lem1949924 y) (@lem1949923 x)). Qed.
Lemma lem1949926 (x : real) (y : real) : (term88 y x) = (term87 x y).
Proof. exact (@lem1483488 x (term89 y)). Qed.
Lemma lem1949927 (x : real) (y : real) : (term426 y x) = (term87 x y).
Proof. exact (TRANS (@lem1949925 y x) (@lem1949926 x y)). Qed.
Lemma lem1949928 (x : real) (y : real) : (term425 y x) = (term87 x y).
Proof. exact (TRANS (@lem1949907 y x) (@lem1949927 x y)). Qed.
Lemma lem1949929 (x : real) (y : real) : (term424 y x) = (term87 x y).
Proof. exact (TRANS (@lem1949906 y x) (@lem1949928 x y)). Qed.
Lemma lem1949930 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1949931 (x : real) (y : real) : (term427 y x) = (term173 x y).
Proof. exact (MK_COMB (@lem1949930) (@lem1949929 x y)). Qed.
Lemma lem1949932 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949933 (x : real) (y : real) : (term421 y x) = (term174 x y).
Proof. exact (MK_COMB (@lem1949931 x y) (@lem1949932)). Qed.
Lemma lem1949934 (x : real) (y : real) : (term420 y x) = (term174 x y).
Proof. exact (TRANS (@lem1949889 y x) (@lem1949933 x y)). Qed.
Lemma lem1949935 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1949936 (y : real) : (term428 y) = (term429 y).
Proof. exact (MK_COMB (@lem1949935) (@lem1949888 y)). Qed.
Lemma lem1949937 (x : real) (y : real) : (term375 y x) = (term430 x y).
Proof. exact (MK_COMB (@lem1949936 y) (@lem1949934 x y)). Qed.
Lemma lem1949938 (x : real) (y : real) : (term367 y x) = (term431 x y).
Proof. exact (@lem1483521 (term2 x) (term2 y)). Qed.
Lemma lem1949945 (y : real) : (term2 y) = (term432 y).
Proof. exact (@lem1483512 (sqrt y)). Qed.
Lemma lem1949952 (x : real) : (term2 x) = (term432 x).
Proof. exact (@lem1483512 (sqrt x)). Qed.
Lemma lem1949953 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1949954 (x : real) : (term433 x) = (term434 x).
Proof. exact (MK_COMB (@lem1949953) (@lem1949952 x)). Qed.
Lemma lem1949955 (x : real) (y : real) : (term435 x y) = (term436 x y).
Proof. exact (MK_COMB (@lem1949954 x) (@lem1949945 y)). Qed.
Lemma lem1949956 (x : real) (y : real) : (term436 x y) = (term437 x y).
Proof. exact (@lem1483519 (term432 x) (term432 y)). Qed.
Lemma lem1949957 (y : real) : (term438 y) = (term439 y).
Proof. exact (@lem1483476 term258 term258 (sqrt y)). Qed.
Lemma lem1949959 (m : nat) (n : nat) : (term409 m n) = (term410 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1949960 : term411 = term412.
Proof. exact (@lem1949959 term82 term82). Qed.
Lemma lem1949961 : (term413 = (BIT1 0)) = (term414 = term82).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1949962 : term414 = term82.
Proof. exact (EQ_MP (@lem1949961) (@lem940073)). Qed.
Lemma lem1949963 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1949964 : term412 = term236.
Proof. exact (MK_COMB (@lem1949963) (@lem1949962)). Qed.
Lemma lem1949965 : term411 = term236.
Proof. exact (TRANS (@lem1949960) (@lem1949964)). Qed.
Lemma lem1949966 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1949967 : term415 = term416.
Proof. exact (MK_COMB (@lem1949966) (@lem1949965)). Qed.
Lemma lem1949968 (y : real) : (sqrt y) = (sqrt y).
Proof. exact (eq_refl (sqrt y)). Qed.
Lemma lem1949969 (y : real) : (term439 y) = (term440 y).
Proof. exact (MK_COMB (@lem1949967) (@lem1949968 y)). Qed.
Lemma lem1949970 (y : real) : (term438 y) = (term440 y).
Proof. exact (TRANS (@lem1949957 y) (@lem1949969 y)). Qed.
Lemma lem1949971 (y : real) : (term440 y) = (sqrt y).
Proof. exact (@lem1483436 (sqrt y)). Qed.
Lemma lem1949972 (y : real) : (term438 y) = (sqrt y).
Proof. exact (TRANS (@lem1949970 y) (@lem1949971 y)). Qed.
Lemma lem1949973 (x : real) : (term441 x) = (term441 x).
Proof. exact (eq_refl (term441 x)). Qed.
Lemma lem1949976 (x : real) (y : real) : (term437 x y) = (term442 x y).
Proof. exact (MK_COMB (@lem1949973 x) (@lem1949972 y)). Qed.
Lemma lem1949977 (x : real) (y : real) : (term436 x y) = (term442 x y).
Proof. exact (TRANS (@lem1949956 x y) (@lem1949976 x y)). Qed.
Lemma lem1949978 (x : real) (y : real) : (term435 x y) = (term442 x y).
Proof. exact (TRANS (@lem1949955 x y) (@lem1949977 x y)). Qed.
Lemma lem1949979 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1949980 (x : real) (y : real) : (term443 x y) = (term444 x y).
Proof. exact (MK_COMB (@lem1949979) (@lem1949978 x y)). Qed.
Lemma lem1949981 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1949982 (x : real) (y : real) : (term431 x y) = (term445 x y).
Proof. exact (MK_COMB (@lem1949980 x y) (@lem1949981)). Qed.
Lemma lem1949983 (x : real) (y : real) : (term367 y x) = (term445 x y).
Proof. exact (TRANS (@lem1949938 x y) (@lem1949982 x y)). Qed.
Lemma lem1949984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1949985 (x : real) (y : real) : (term379 y x) = (term446 x y).
Proof. exact (MK_COMB (@lem1949984) (@lem1949937 x y)). Qed.
Lemma lem1949986 (x : real) (y : real) : (term381 y x) = (term447 x y).
Proof. exact (MK_COMB (@lem1949985 x y) (@lem1949983 x y)). Qed.
Lemma lem1949987 (x : real) (y : real) : (term383 x y) = (term448 x y).
Proof. exact (@lem1483531 (sqrt x) (sqrt y)). Qed.
Lemma lem1950000 (x : real) (y : real) : (term449 x y) = (term450 x y).
Proof. exact (@lem1483519 (sqrt x) (sqrt y)). Qed.
Lemma lem1950001 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1950002 (x : real) (y : real) : (term451 x y) = (term452 x y).
Proof. exact (MK_COMB (@lem1950001) (@lem1950000 x y)). Qed.
Lemma lem1950003 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1950004 (x : real) (y : real) : (term448 x y) = (term453 x y).
Proof. exact (MK_COMB (@lem1950002 x y) (@lem1950003)). Qed.
Lemma lem1950005 (x : real) (y : real) : (term383 x y) = (term453 x y).
Proof. exact (TRANS (@lem1949987 x y) (@lem1950004 x y)). Qed.
Lemma lem1950006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1950007 (x : real) (y : real) : (term385 y x) = (term454 x y).
Proof. exact (MK_COMB (@lem1950006) (@lem1949986 x y)). Qed.
Lemma lem1950008 (x : real) (y : real) : (term387 x y) = (term455 x y).
Proof. exact (MK_COMB (@lem1950007 x y) (@lem1950005 x y)). Qed.
Lemma lem1950009 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1950010 (y : real) : (term389 y) = (term222 y).
Proof. exact (MK_COMB (@lem1950009) (@lem1949848 y)). Qed.
Lemma lem1950011 (x : real) (y : real) : (term391 x y) = (term456 x y).
Proof. exact (MK_COMB (@lem1950010 y) (@lem1950008 x y)). Qed.
Lemma lem1950012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1950013 (x : real) : (term389 x) = (term222 x).
Proof. exact (MK_COMB (@lem1950012) (@lem1949829 x)). Qed.
Lemma lem1950014 (x : real) (y : real) : (term394 x y) = (term457 x y).
Proof. exact (MK_COMB (@lem1950013 x) (@lem1950011 x y)). Qed.
Lemma lem1950015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1950016 (x : real) (y : real) : (term68 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1950015) (@lem1949810 x y)). Qed.
Lemma lem1950017 (x : real) (y : real) : (term398 x y) = (term458 x y).
Proof. exact (MK_COMB (@lem1950016 x y) (@lem1950014 x y)). Qed.
Lemma lem1950024 (x : real) (y : real) : (term399 x y) = (term458 x y).
Proof. exact (TRANS (@lem1949791 x y) (@lem1950017 x y)). Qed.
Lemma lem1950038 (x : real) (y : real) : (term455 x y) = (term459 x y).
Proof. exact (@lem19367 (term430 x y) (term445 x y) (term453 x y)). Qed.
Lemma lem1950039 (x : real) (y : real) : (term460 x y) = (term460 x y).
Proof. exact (eq_refl (term460 x y)). Qed.
Lemma lem1950046 (x : real) (y : real) : (term461 x y) = (term462 x y).
Proof. exact (@lem19367 (term419 y) (term174 x y) (term453 x y)). Qed.
Lemma lem1950047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1950048 (x : real) (y : real) : (term463 x y) = (term464 x y).
Proof. exact (MK_COMB (@lem1950047) (@lem1950046 x y)). Qed.
Lemma lem1950049 (x : real) (y : real) : (term459 x y) = (term465 x y).
Proof. exact (MK_COMB (@lem1950048 x y) (@lem1950039 x y)). Qed.
Lemma lem1950051 (x : real) (y : real) : (term455 x y) = (term465 x y).
Proof. exact (TRANS (@lem1950038 x y) (@lem1950049 x y)). Qed.
Lemma lem1950054 (y : real) : (term222 y) = (term222 y).
Proof. exact (eq_refl (term222 y)). Qed.
Lemma lem1950055 (x : real) (y : real) : (term456 x y) = (term466 x y).
Proof. exact (MK_COMB (@lem1950054 y) (@lem1950051 x y)). Qed.
Lemma lem1950056 (x : real) (y : real) : (term466 x y) = (term467 x y).
Proof. exact (@lem19158 (term462 x y) (term98 y) (term460 x y)). Qed.
Lemma lem1950057 (x : real) (y : real) : (term468 x y) = (term468 x y).
Proof. exact (eq_refl (term468 x y)). Qed.
Lemma lem1950064 (x : real) (y : real) : (term469 x y) = (term470 x y).
Proof. exact (@lem19158 (term471 x y) (term98 y) (term472 x y)). Qed.
Lemma lem1950065 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1950066 (x : real) (y : real) : (term473 x y) = (term474 x y).
Proof. exact (MK_COMB (@lem1950065) (@lem1950064 x y)). Qed.
Lemma lem1950067 (x : real) (y : real) : (term467 x y) = (term475 x y).
Proof. exact (MK_COMB (@lem1950066 x y) (@lem1950057 x y)). Qed.
Lemma lem1950068 (x : real) (y : real) : (term466 x y) = (term475 x y).
Proof. exact (TRANS (@lem1950056 x y) (@lem1950067 x y)). Qed.
Lemma lem1950069 (x : real) (y : real) : (term456 x y) = (term475 x y).
Proof. exact (TRANS (@lem1950055 x y) (@lem1950068 x y)). Qed.
Lemma lem1950072 (x : real) : (term222 x) = (term222 x).
Proof. exact (eq_refl (term222 x)). Qed.
Lemma lem1950073 (x : real) (y : real) : (term457 x y) = (term476 x y).
Proof. exact (MK_COMB (@lem1950072 x) (@lem1950069 x y)). Qed.
Lemma lem1950074 (x : real) (y : real) : (term476 x y) = (term477 x y).
Proof. exact (@lem19158 (term470 x y) (term98 x) (term468 x y)). Qed.
Lemma lem1950075 (x : real) (y : real) : (term478 x y) = (term478 x y).
Proof. exact (eq_refl (term478 x y)). Qed.
Lemma lem1950082 (x : real) (y : real) : (term479 x y) = (term480 x y).
Proof. exact (@lem19158 (term481 x y) (term98 x) (term482 x y)). Qed.
Lemma lem1950083 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1950084 (x : real) (y : real) : (term483 x y) = (term484 x y).
Proof. exact (MK_COMB (@lem1950083) (@lem1950082 x y)). Qed.
Lemma lem1950085 (x : real) (y : real) : (term477 x y) = (term485 x y).
Proof. exact (MK_COMB (@lem1950084 x y) (@lem1950075 x y)). Qed.
Lemma lem1950086 (x : real) (y : real) : (term476 x y) = (term485 x y).
Proof. exact (TRANS (@lem1950074 x y) (@lem1950085 x y)). Qed.
Lemma lem1950087 (x : real) (y : real) : (term457 x y) = (term485 x y).
Proof. exact (TRANS (@lem1950073 x y) (@lem1950086 x y)). Qed.
Lemma lem1950090 (x : real) (y : real) : (term109 x y) = (term109 x y).
Proof. exact (eq_refl (term109 x y)). Qed.
Lemma lem1950091 (x : real) (y : real) : (term458 x y) = (term486 x y).
Proof. exact (MK_COMB (@lem1950090 x y) (@lem1950087 x y)). Qed.
Lemma lem1950092 (x : real) (y : real) : (term486 x y) = (term487 x y).
Proof. exact (@lem19158 (term480 x y) (term92 x y) (term478 x y)). Qed.
Lemma lem1950093 (x : real) (y : real) : (term488 x y) = (term488 x y).
Proof. exact (eq_refl (term488 x y)). Qed.
Lemma lem1950100 (x : real) (y : real) : (term489 x y) = (term490 x y).
Proof. exact (@lem19158 (term491 x y) (term92 x y) (term492 x y)). Qed.
Lemma lem1950101 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1950102 (x : real) (y : real) : (term493 x y) = (term494 x y).
Proof. exact (MK_COMB (@lem1950101) (@lem1950100 x y)). Qed.
Lemma lem1950103 (x : real) (y : real) : (term487 x y) = (term495 x y).
Proof. exact (MK_COMB (@lem1950102 x y) (@lem1950093 x y)). Qed.
Lemma lem1950104 (x : real) (y : real) : (term486 x y) = (term495 x y).
Proof. exact (TRANS (@lem1950092 x y) (@lem1950103 x y)). Qed.
Lemma lem1950105 (x : real) (y : real) : (term458 x y) = (term495 x y).
Proof. exact (TRANS (@lem1950091 x y) (@lem1950104 x y)). Qed.
Lemma lem1950106 (x : real) (y : real) : (term399 x y) = (term495 x y).
Proof. exact (TRANS (@lem1950024 x y) (@lem1950105 x y)). Qed.
Lemma lem1950122 (x : real) (y : real) (h1 : term495 x y) : term495 x y.
Proof. exact (h1). Qed.
Lemma lem1950123 (x : real) (y : real) (h1 : term490 x y) : term490 x y.
Proof. exact (h1). Qed.
Lemma lem1950124 (x : real) (y : real) (h1 : term496 x y) : term496 x y.
Proof. exact (h1). Qed.
Lemma lem1950125 (x : real) (y : real) (h1 : term496 x y) : term491 x y.
Proof. exact (proj2 (@lem1950124 x y h1)). Qed.
Lemma lem1950127 (x : real) (y : real) (h1 : term496 x y) : term481 x y.
Proof. exact (proj2 (@lem1950125 x y h1)). Qed.
Lemma lem1950129 (x : real) (y : real) (h1 : term496 x y) : term471 x y.
Proof. exact (proj2 (@lem1950127 x y h1)). Qed.
Lemma lem1950130 (x : real) (y : real) (h1 : term496 x y) : term98 y.
Proof. exact (proj1 (@lem1950127 x y h1)). Qed.
Lemma lem1950132 (x : real) (y : real) (h1 : term496 x y) : term419 y.
Proof. exact (proj1 (@lem1950129 x y h1)). Qed.
Lemma lem1950134 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1950135 : term230 = term231.
Proof. exact (@lem1950134 (NUMERAL 0) term82). Qed.
Lemma lem1950136 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1950137 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1950138 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1950137 h1) (fun h1 : term231 = True => @lem1950136)). Qed.
Lemma lem1950139 : term231 = True.
Proof. exact (EQ_MP (@lem1950138) (@lem1950136)). Qed.
Lemma lem1950140 : term230 = True.
Proof. exact (TRANS (@lem1950135) (@lem1950139)). Qed.
Lemma lem1950141 : True = term230.
Proof. exact (SYM (@lem1950140)). Qed.
Lemma lem1950142 : term230.
Proof. exact (EQ_MP (@lem1950141) (@lem0)). Qed.
Lemma lem1950143 (x : real) (y : real) (h1 : term496 x y) : term497 y.
Proof. exact (conj (@lem1950142) (@lem1950132 x y h1)). Qed.
Lemma lem1950145 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1950146 (y : real) : term498 y.
Proof. exact (@lem1950145 term236 y). Qed.
Lemma lem1950147 (x : real) (y : real) (h1 : term496 x y) : term499 y.
Proof. exact (@lem1950146 y (@lem1950143 x y h1)). Qed.
Lemma lem1950148 (y : real) : (term121 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1950149 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1950150 (y : real) : (term500 y) = (real_gt y).
Proof. exact (MK_COMB (@lem1950149) (@lem1950148 y)). Qed.
Lemma lem1950151 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1950152 (y : real) : (term499 y) = (term419 y).
Proof. exact (MK_COMB (@lem1950150 y) (@lem1950151)). Qed.
Lemma lem1950153 (x : real) (y : real) (h1 : term496 x y) : term419 y.
Proof. exact (EQ_MP (@lem1950152 y) (@lem1950147 x y h1)). Qed.
Lemma lem1950155 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1950156 : term230 = term231.
Proof. exact (@lem1950155 (NUMERAL 0) term82). Qed.
Lemma lem1950157 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1950158 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1950159 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1950158 h1) (fun h1 : term231 = True => @lem1950157)). Qed.
Lemma lem1950160 : term231 = True.
Proof. exact (EQ_MP (@lem1950159) (@lem1950157)). Qed.
Lemma lem1950161 : term230 = True.
Proof. exact (TRANS (@lem1950156) (@lem1950160)). Qed.
Lemma lem1950162 : True = term230.
Proof. exact (SYM (@lem1950161)). Qed.
Lemma lem1950163 : term230.
Proof. exact (EQ_MP (@lem1950162) (@lem0)). Qed.
Lemma lem1950164 (x : real) (y : real) (h1 : term496 x y) : term245 y.
Proof. exact (conj (@lem1950163) (@lem1950130 x y h1)). Qed.
Lemma lem1950166 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1950167 (y : real) : term246 y.
Proof. exact (@lem1950166 term236 (term89 y)). Qed.
Lemma lem1950168 (x : real) (y : real) (h1 : term496 x y) : term247 y.
Proof. exact (@lem1950167 y (@lem1950164 x y h1)). Qed.
Lemma lem1950169 (y : real) : (term248 y) = (term89 y).
Proof. exact (@lem1483460 (term89 y)). Qed.
Lemma lem1950170 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1950171 (y : real) : (term249 y) = (term97 y).
Proof. exact (MK_COMB (@lem1950170) (@lem1950169 y)). Qed.
Lemma lem1950172 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1950173 (y : real) : (term247 y) = (term98 y).
Proof. exact (MK_COMB (@lem1950171 y) (@lem1950172)). Qed.
Lemma lem1950174 (x : real) (y : real) (h1 : term496 x y) : term98 y.
Proof. exact (EQ_MP (@lem1950173 y) (@lem1950168 x y h1)). Qed.
Lemma lem1950175 (x : real) (y : real) (h1 : term496 x y) : term501 y.
Proof. exact (conj (@lem1950174 x y h1) (@lem1950153 x y h1)). Qed.
Lemma lem1950177 (x : real) (y : real) : term251 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1950178 (y : real) : term502 y.
Proof. exact (@lem1950177 (term89 y) y). Qed.
Lemma lem1950179 (x : real) (y : real) (h1 : term496 x y) : term269 y.
Proof. exact (@lem1950178 y (@lem1950175 x y h1)). Qed.
Lemma lem1950180 (y : real) : (term256 y) = (term257 y).
Proof. exact (@lem1483440 term258 y). Qed.
Lemma lem1950182 (m : nat) : (term259 m) = term77.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1950183 : term260 = term77.
Proof. exact (@lem1950182 term82). Qed.
Lemma lem1950184 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1950185 : term261 = term262.
Proof. exact (MK_COMB (@lem1950184) (@lem1950183)). Qed.
Lemma lem1950186 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1950187 (y : real) : (term257 y) = (term263 y).
Proof. exact (MK_COMB (@lem1950185) (@lem1950186 y)). Qed.
Lemma lem1950188 (y : real) : (term256 y) = (term263 y).
Proof. exact (TRANS (@lem1950180 y) (@lem1950187 y)). Qed.
Lemma lem1950189 (y : real) : (term263 y) = term77.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1950190 (y : real) : (term256 y) = term77.
Proof. exact (TRANS (@lem1950188 y) (@lem1950189 y)). Qed.
Lemma lem1950191 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1950192 (y : real) : (term270 y) = term271.
Proof. exact (MK_COMB (@lem1950191) (@lem1950190 y)). Qed.
Lemma lem1950193 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1950194 (y : real) : (term269 y) = term272.
Proof. exact (MK_COMB (@lem1950192 y) (@lem1950193)). Qed.
Lemma lem1950195 (x : real) (y : real) (h1 : term496 x y) : term272.
Proof. exact (EQ_MP (@lem1950194 y) (@lem1950179 x y h1)). Qed.
Lemma lem1950197 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1950198 : term272 = term273.
Proof. exact (@lem1950197 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1950199 : term273 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1950200 : term272 = False.
Proof. exact (TRANS (@lem1950198) (@lem1950199)). Qed.
Lemma lem1950201 (x : real) (y : real) (h1 : term496 x y) : False.
Proof. exact (EQ_MP (@lem1950200) (@lem1950195 x y h1)). Qed.
Lemma lem1950202 (x : real) (y : real) (h1 : term503 x y) : term503 x y.
Proof. exact (h1). Qed.
Lemma lem1950203 (x : real) (y : real) (h1 : term503 x y) : term492 x y.
Proof. exact (proj2 (@lem1950202 x y h1)). Qed.
Lemma lem1950204 (x : real) (y : real) (h1 : term503 x y) : term92 x y.
Proof. exact (proj1 (@lem1950202 x y h1)). Qed.
Lemma lem1950205 (x : real) (y : real) (h1 : term503 x y) : term482 x y.
Proof. exact (proj2 (@lem1950203 x y h1)). Qed.
Lemma lem1950207 (x : real) (y : real) (h1 : term503 x y) : term472 x y.
Proof. exact (proj2 (@lem1950205 x y h1)). Qed.
Lemma lem1950210 (x : real) (y : real) (h1 : term503 x y) : term174 x y.
Proof. exact (proj1 (@lem1950207 x y h1)). Qed.
Lemma lem1950212 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1950213 : term230 = term231.
Proof. exact (@lem1950212 (NUMERAL 0) term82). Qed.
Lemma lem1950214 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1950215 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1950216 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1950215 h1) (fun h1 : term231 = True => @lem1950214)). Qed.
Lemma lem1950217 : term231 = True.
Proof. exact (EQ_MP (@lem1950216) (@lem1950214)). Qed.
Lemma lem1950218 : term230 = True.
Proof. exact (TRANS (@lem1950213) (@lem1950217)). Qed.
Lemma lem1950219 : True = term230.
Proof. exact (SYM (@lem1950218)). Qed.
Lemma lem1950220 : term230.
Proof. exact (EQ_MP (@lem1950219) (@lem0)). Qed.
Lemma lem1950221 (x : real) (y : real) (h1 : term503 x y) : term274 x y.
Proof. exact (conj (@lem1950220) (@lem1950210 x y h1)). Qed.
Lemma lem1950223 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1950224 (x : real) (y : real) : term275 x y.
Proof. exact (@lem1950223 term236 (term87 x y)). Qed.
Lemma lem1950225 (x : real) (y : real) (h1 : term503 x y) : term276 x y.
Proof. exact (@lem1950224 x y (@lem1950221 x y h1)). Qed.
Lemma lem1950226 (x : real) (y : real) : (term277 x y) = (term87 x y).
Proof. exact (@lem1483460 (term87 x y)). Qed.
Lemma lem1950227 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1950228 (x : real) (y : real) : (term278 x y) = (term173 x y).
Proof. exact (MK_COMB (@lem1950227) (@lem1950226 x y)). Qed.
Lemma lem1950229 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1950230 (x : real) (y : real) : (term276 x y) = (term174 x y).
Proof. exact (MK_COMB (@lem1950228 x y) (@lem1950229)). Qed.
Lemma lem1950231 (x : real) (y : real) (h1 : term503 x y) : term174 x y.
Proof. exact (EQ_MP (@lem1950230 x y) (@lem1950225 x y h1)). Qed.
Lemma lem1950233 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1950234 : term230 = term231.
Proof. exact (@lem1950233 (NUMERAL 0) term82). Qed.
Lemma lem1950235 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1950236 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1950237 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1950236 h1) (fun h1 : term231 = True => @lem1950235)). Qed.
Lemma lem1950238 : term231 = True.
Proof. exact (EQ_MP (@lem1950237) (@lem1950235)). Qed.
Lemma lem1950239 : term230 = True.
Proof. exact (TRANS (@lem1950234) (@lem1950238)). Qed.
Lemma lem1950240 : True = term230.
Proof. exact (SYM (@lem1950239)). Qed.
Lemma lem1950241 : term230.
Proof. exact (EQ_MP (@lem1950240) (@lem0)). Qed.
Lemma lem1950242 (x : real) (y : real) (h1 : term503 x y) : term239 x y.
Proof. exact (conj (@lem1950241) (@lem1950204 x y h1)). Qed.
Lemma lem1950244 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1950245 (x : real) (y : real) : term241 x y.
Proof. exact (@lem1950244 term236 (term88 x y)). Qed.
Lemma lem1950246 (x : real) (y : real) (h1 : term503 x y) : term242 x y.
Proof. exact (@lem1950245 x y (@lem1950242 x y h1)). Qed.
Lemma lem1950247 (x : real) (y : real) : (term243 x y) = (term88 x y).
Proof. exact (@lem1483460 (term88 x y)). Qed.
Lemma lem1950248 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1950249 (x : real) (y : real) : (term244 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1950248) (@lem1950247 x y)). Qed.
Lemma lem1950250 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1950251 (x : real) (y : real) : (term242 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem1950249 x y) (@lem1950250)). Qed.
Lemma lem1950252 (x : real) (y : real) (h1 : term503 x y) : term92 x y.
Proof. exact (EQ_MP (@lem1950251 x y) (@lem1950246 x y h1)). Qed.
Lemma lem1950253 (x : real) (y : real) (h1 : term503 x y) : term279 x y.
Proof. exact (conj (@lem1950252 x y h1) (@lem1950231 x y h1)). Qed.
Lemma lem1950255 (x : real) (y : real) : term267 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1950256 (x : real) (y : real) : term280 x y.
Proof. exact (@lem1950255 (term88 x y) (term87 x y)). Qed.
Lemma lem1950257 (x : real) (y : real) (h1 : term503 x y) : term281 x y.
Proof. exact (@lem1950256 x y (@lem1950253 x y h1)). Qed.
Lemma lem1950258 (x : real) (y : real) : (term282 x y) = (term283 x y).
Proof. exact (@lem1483480 (term89 x) x y (term89 y)). Qed.
Lemma lem1950259 (x : real) : (term256 x) = (term257 x).
Proof. exact (@lem1483440 term258 x). Qed.
Lemma lem1950261 (m : nat) : (term259 m) = term77.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1950262 : term260 = term77.
Proof. exact (@lem1950261 term82). Qed.
Lemma lem1950263 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1950264 : term261 = term262.
Proof. exact (MK_COMB (@lem1950263) (@lem1950262)). Qed.
Lemma lem1950265 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1950266 (x : real) : (term257 x) = (term263 x).
Proof. exact (MK_COMB (@lem1950264) (@lem1950265 x)). Qed.
Lemma lem1950267 (x : real) : (term256 x) = (term263 x).
Proof. exact (TRANS (@lem1950259 x) (@lem1950266 x)). Qed.
Lemma lem1950268 (x : real) : (term263 x) = term77.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1950269 (x : real) : (term256 x) = term77.
Proof. exact (TRANS (@lem1950267 x) (@lem1950268 x)). Qed.
Lemma lem1950270 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1950271 (x : real) : (term284 x) = term285.
Proof. exact (MK_COMB (@lem1950270) (@lem1950269 x)). Qed.
Lemma lem1950272 (y : real) : (term286 y) = (term257 y).
Proof. exact (@lem1483442 term258 y). Qed.
Lemma lem1950274 (m : nat) : (term259 m) = term77.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1950275 : term260 = term77.
Proof. exact (@lem1950274 term82). Qed.
Lemma lem1950276 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1950277 : term261 = term262.
Proof. exact (MK_COMB (@lem1950276) (@lem1950275)). Qed.
Lemma lem1950278 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1950279 (y : real) : (term257 y) = (term263 y).
Proof. exact (MK_COMB (@lem1950277) (@lem1950278 y)). Qed.
Lemma lem1950280 (y : real) : (term286 y) = (term263 y).
Proof. exact (TRANS (@lem1950272 y) (@lem1950279 y)). Qed.
Lemma lem1950281 (y : real) : (term263 y) = term77.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1950282 (y : real) : (term286 y) = term77.
Proof. exact (TRANS (@lem1950280 y) (@lem1950281 y)). Qed.
Lemma lem1950283 (x : real) (y : real) : (term283 x y) = term287.
Proof. exact (MK_COMB (@lem1950271 x) (@lem1950282 y)). Qed.
Lemma lem1950284 (x : real) (y : real) : (term282 x y) = term287.
Proof. exact (TRANS (@lem1950258 x y) (@lem1950283 x y)). Qed.
Lemma lem1950285 : term287 = term77.
Proof. exact (@lem1483448 term77). Qed.
Lemma lem1950286 (x : real) (y : real) : (term282 x y) = term77.
Proof. exact (TRANS (@lem1950284 x y) (@lem1950285)). Qed.
Lemma lem1950287 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1950288 (x : real) (y : real) : (term288 x y) = term271.
Proof. exact (MK_COMB (@lem1950287) (@lem1950286 x y)). Qed.
Lemma lem1950289 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1950290 (x : real) (y : real) : (term281 x y) = term272.
Proof. exact (MK_COMB (@lem1950288 x y) (@lem1950289)). Qed.
Lemma lem1950291 (x : real) (y : real) (h1 : term503 x y) : term272.
Proof. exact (EQ_MP (@lem1950290 x y) (@lem1950257 x y h1)). Qed.
Lemma lem1950293 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1950294 : term272 = term273.
Proof. exact (@lem1950293 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1950295 : term273 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1950296 : term272 = False.
Proof. exact (TRANS (@lem1950294) (@lem1950295)). Qed.
Lemma lem1950297 (x : real) (y : real) (h1 : term503 x y) : False.
Proof. exact (EQ_MP (@lem1950296) (@lem1950291 x y h1)). Qed.
Lemma lem1950298 (x : real) (y : real) (h1 : term490 x y) : False.
Proof. exact (or_elim (@lem1950123 x y h1) (fun h0 : term496 x y => @lem1950201 x y h0) (fun h0 : term503 x y => @lem1950297 x y h0)). Qed.
Lemma lem1950299 (x : real) (y : real) (h1 : term488 x y) : term488 x y.
Proof. exact (h1). Qed.
Lemma lem1950300 (x : real) (y : real) (h1 : term488 x y) : term478 x y.
Proof. exact (proj2 (@lem1950299 x y h1)). Qed.
Lemma lem1950302 (x : real) (y : real) (h1 : term488 x y) : term468 x y.
Proof. exact (proj2 (@lem1950300 x y h1)). Qed.
Lemma lem1950304 (x : real) (y : real) (h1 : term488 x y) : term460 x y.
Proof. exact (proj2 (@lem1950302 x y h1)). Qed.
Lemma lem1950306 (x : real) (y : real) (h1 : term488 x y) : term453 x y.
Proof. exact (proj2 (@lem1950304 x y h1)). Qed.
Lemma lem1950307 (x : real) (y : real) (h1 : term488 x y) : term445 x y.
Proof. exact (proj1 (@lem1950304 x y h1)). Qed.
Lemma lem1950309 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1950310 : term230 = term231.
Proof. exact (@lem1950309 (NUMERAL 0) term82). Qed.
Lemma lem1950311 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1950312 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1950313 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1950312 h1) (fun h1 : term231 = True => @lem1950311)). Qed.
Lemma lem1950314 : term231 = True.
Proof. exact (EQ_MP (@lem1950313) (@lem1950311)). Qed.
Lemma lem1950315 : term230 = True.
Proof. exact (TRANS (@lem1950310) (@lem1950314)). Qed.
Lemma lem1950316 : True = term230.
Proof. exact (SYM (@lem1950315)). Qed.
Lemma lem1950317 : term230.
Proof. exact (EQ_MP (@lem1950316) (@lem0)). Qed.
Lemma lem1950318 (x : real) (y : real) (h1 : term488 x y) : term504 x y.
Proof. exact (conj (@lem1950317) (@lem1950306 x y h1)). Qed.
Lemma lem1950320 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1950321 (x : real) (y : real) : term505 x y.
Proof. exact (@lem1950320 term236 (term450 x y)). Qed.
Lemma lem1950322 (x : real) (y : real) (h1 : term488 x y) : term506 x y.
Proof. exact (@lem1950321 x y (@lem1950318 x y h1)). Qed.
Lemma lem1950323 (x : real) (y : real) : (term507 x y) = (term450 x y).
Proof. exact (@lem1483460 (term450 x y)). Qed.
Lemma lem1950324 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1950325 (x : real) (y : real) : (term508 x y) = (term452 x y).
Proof. exact (MK_COMB (@lem1950324) (@lem1950323 x y)). Qed.
Lemma lem1950326 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1950327 (x : real) (y : real) : (term506 x y) = (term453 x y).
Proof. exact (MK_COMB (@lem1950325 x y) (@lem1950326)). Qed.
Lemma lem1950328 (x : real) (y : real) (h1 : term488 x y) : term453 x y.
Proof. exact (EQ_MP (@lem1950327 x y) (@lem1950322 x y h1)). Qed.
Lemma lem1950330 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1950331 : term230 = term231.
Proof. exact (@lem1950330 (NUMERAL 0) term82). Qed.
Lemma lem1950332 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1950333 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1950334 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1950333 h1) (fun h1 : term231 = True => @lem1950332)). Qed.
Lemma lem1950335 : term231 = True.
Proof. exact (EQ_MP (@lem1950334) (@lem1950332)). Qed.
Lemma lem1950336 : term230 = True.
Proof. exact (TRANS (@lem1950331) (@lem1950335)). Qed.
Lemma lem1950337 : True = term230.
Proof. exact (SYM (@lem1950336)). Qed.
Lemma lem1950338 : term230.
Proof. exact (EQ_MP (@lem1950337) (@lem0)). Qed.
Lemma lem1950339 (x : real) (y : real) (h1 : term488 x y) : term509 x y.
Proof. exact (conj (@lem1950338) (@lem1950307 x y h1)). Qed.
Lemma lem1950341 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1950342 (x : real) (y : real) : term510 x y.
Proof. exact (@lem1950341 term236 (term442 x y)). Qed.
Lemma lem1950343 (x : real) (y : real) (h1 : term488 x y) : term511 x y.
Proof. exact (@lem1950342 x y (@lem1950339 x y h1)). Qed.
Lemma lem1950344 (x : real) (y : real) : (term512 x y) = (term442 x y).
Proof. exact (@lem1483460 (term442 x y)). Qed.
Lemma lem1950345 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1950346 (x : real) (y : real) : (term513 x y) = (term444 x y).
Proof. exact (MK_COMB (@lem1950345) (@lem1950344 x y)). Qed.
Lemma lem1950347 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1950348 (x : real) (y : real) : (term511 x y) = (term445 x y).
Proof. exact (MK_COMB (@lem1950346 x y) (@lem1950347)). Qed.
Lemma lem1950349 (x : real) (y : real) (h1 : term488 x y) : term445 x y.
Proof. exact (EQ_MP (@lem1950348 x y) (@lem1950343 x y h1)). Qed.
Lemma lem1950350 (x : real) (y : real) (h1 : term488 x y) : term460 x y.
Proof. exact (conj (@lem1950349 x y h1) (@lem1950328 x y h1)). Qed.
Lemma lem1950352 (x : real) (y : real) : term267 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1950353 (x : real) (y : real) : term514 x y.
Proof. exact (@lem1950352 (term442 x y) (term450 x y)). Qed.
Lemma lem1950354 (x : real) (y : real) (h1 : term488 x y) : term515 x y.
Proof. exact (@lem1950353 x y (@lem1950350 x y h1)). Qed.
Lemma lem1950355 (x : real) (y : real) : (term516 x y) = (term517 x y).
Proof. exact (@lem1483480 (term432 x) (sqrt x) (sqrt y) (term432 y)). Qed.
Lemma lem1950356 (x : real) : (term518 x) = (term519 x).
Proof. exact (@lem1483440 term258 (sqrt x)). Qed.
Lemma lem1950358 (m : nat) : (term259 m) = term77.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1950359 : term260 = term77.
Proof. exact (@lem1950358 term82). Qed.
Lemma lem1950360 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1950361 : term261 = term262.
Proof. exact (MK_COMB (@lem1950360) (@lem1950359)). Qed.
Lemma lem1950362 (x : real) : (sqrt x) = (sqrt x).
Proof. exact (eq_refl (sqrt x)). Qed.
Lemma lem1950363 (x : real) : (term519 x) = (term520 x).
Proof. exact (MK_COMB (@lem1950361) (@lem1950362 x)). Qed.
Lemma lem1950364 (x : real) : (term518 x) = (term520 x).
Proof. exact (TRANS (@lem1950356 x) (@lem1950363 x)). Qed.
Lemma lem1950365 (x : real) : (term520 x) = term77.
Proof. exact (@lem1483446 (sqrt x)). Qed.
Lemma lem1950366 (x : real) : (term518 x) = term77.
Proof. exact (TRANS (@lem1950364 x) (@lem1950365 x)). Qed.
Lemma lem1950367 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1950368 (x : real) : (term521 x) = term285.
Proof. exact (MK_COMB (@lem1950367) (@lem1950366 x)). Qed.
Lemma lem1950369 (y : real) : (term522 y) = (term519 y).
Proof. exact (@lem1483442 term258 (sqrt y)). Qed.
Lemma lem1950371 (m : nat) : (term259 m) = term77.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1950372 : term260 = term77.
Proof. exact (@lem1950371 term82). Qed.
Lemma lem1950373 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1950374 : term261 = term262.
Proof. exact (MK_COMB (@lem1950373) (@lem1950372)). Qed.
Lemma lem1950375 (y : real) : (sqrt y) = (sqrt y).
Proof. exact (eq_refl (sqrt y)). Qed.
Lemma lem1950376 (y : real) : (term519 y) = (term520 y).
Proof. exact (MK_COMB (@lem1950374) (@lem1950375 y)). Qed.
Lemma lem1950377 (y : real) : (term522 y) = (term520 y).
Proof. exact (TRANS (@lem1950369 y) (@lem1950376 y)). Qed.
Lemma lem1950378 (y : real) : (term520 y) = term77.
Proof. exact (@lem1483446 (sqrt y)). Qed.
Lemma lem1950379 (y : real) : (term522 y) = term77.
Proof. exact (TRANS (@lem1950377 y) (@lem1950378 y)). Qed.
Lemma lem1950380 (x : real) (y : real) : (term517 x y) = term287.
Proof. exact (MK_COMB (@lem1950368 x) (@lem1950379 y)). Qed.
Lemma lem1950381 (x : real) (y : real) : (term516 x y) = term287.
Proof. exact (TRANS (@lem1950355 x y) (@lem1950380 x y)). Qed.
Lemma lem1950382 : term287 = term77.
Proof. exact (@lem1483448 term77). Qed.
Lemma lem1950383 (x : real) (y : real) : (term516 x y) = term77.
Proof. exact (TRANS (@lem1950381 x y) (@lem1950382)). Qed.
Lemma lem1950384 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1950385 (x : real) (y : real) : (term523 x y) = term271.
Proof. exact (MK_COMB (@lem1950384) (@lem1950383 x y)). Qed.
Lemma lem1950386 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1950387 (x : real) (y : real) : (term515 x y) = term272.
Proof. exact (MK_COMB (@lem1950385 x y) (@lem1950386)). Qed.
Lemma lem1950388 (x : real) (y : real) (h1 : term488 x y) : term272.
Proof. exact (EQ_MP (@lem1950387 x y) (@lem1950354 x y h1)). Qed.
Lemma lem1950390 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1950391 : term272 = term273.
Proof. exact (@lem1950390 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1950392 : term273 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1950393 : term272 = False.
Proof. exact (TRANS (@lem1950391) (@lem1950392)). Qed.
Lemma lem1950394 (x : real) (y : real) (h1 : term488 x y) : False.
Proof. exact (EQ_MP (@lem1950393) (@lem1950388 x y h1)). Qed.
Lemma lem1950395 (x : real) (y : real) (h1 : term495 x y) : False.
Proof. exact (or_elim (@lem1950122 x y h1) (fun h0 : term490 x y => @lem1950298 x y h0) (fun h0 : term488 x y => @lem1950394 x y h0)). Qed.
Lemma lem1950397 (x : real) (y : real) (h1 : term495 x y) : term495 x y.
Proof. exact (h1). Qed.
Lemma lem1950398 (x : real) (y : real) (h1 : term495 x y) : (term495 x y) = False.
Proof. exact (prop_ext (fun h2 : term495 x y => @lem1950395 x y h1) (fun h2 : False => @lem1950397 x y h1)). Qed.
Lemma lem1950399 (x : real) (y : real) (h1 : term495 x y) : False.
Proof. exact (EQ_MP (@lem1950398 x y h1) (@lem1950397 x y h1)). Qed.
Lemma lem1950400 (x : real) (y : real) (h1 : term399 x y) : term399 x y.
Proof. exact (h1). Qed.
Lemma lem1950401 (x : real) (y : real) (h1 : term399 x y) : term495 x y.
Proof. exact (EQ_MP (@lem1950106 x y) (@lem1950400 x y h1)). Qed.
Lemma lem1950402 (x : real) (y : real) (h1 : term399 x y) : (term495 x y) = False.
Proof. exact (prop_ext (fun h2 : term495 x y => @lem1950399 x y h2) (fun h2 : False => @lem1950401 x y h1)). Qed.
Lemma lem1950403 (x : real) (y : real) (h1 : term399 x y) : False.
Proof. exact (EQ_MP (@lem1950402 x y h1) (@lem1950401 x y h1)). Qed.
Lemma lem1950404 (x : real) (y : real) : term524 x y.
Proof. exact (fun h0 : term399 x y => @lem1950403 x y h0). Qed.
Lemma lem1950405 (x : real) (y : real) : term525 x y.
Proof. exact (@lem1386578 (term526 x y)). Qed.
Lemma lem1950406 (x : real) (y : real) : term526 x y.
Proof. exact (@lem1950405 x y (@lem1950404 x y)). Qed.
Lemma lem1950407 (x : real) (y : real) (h1 : real_lt x y) : term400 x y.
Proof. exact (@lem1950406 x y (@lem1949536 x y h1)). Qed.
Lemma lem1950408 (x : real) (y : real) (h1 : term32 x) (h2 : real_lt x y) : term396 x y.
Proof. exact (@lem1950407 x y h2 (@lem1948544 x h1)). Qed.
Lemma lem1950409 (x : real) (y : real) (h1 : term32 x) (h2 : term32 y) (h3 : real_lt x y) : term373 x y.
Proof. exact (@lem1950408 x y h1 h3 (@lem1948539 y h2)). Qed.
Lemma lem1950410 (x : real) (y : real) (h1 : term32 x) (h2 : term32 y) (h3 : real_lt x y) : term372 x y.
Proof. exact (EQ_MP (@lem1949702 x y) (@lem1950409 x y h1 h2 h3)). Qed.
Lemma lem1950411 (x : real) (y : real) (h1 : term50) (h2 : term32 x) (h3 : term32 y) (h4 : real_lt x y) : term344 x y.
Proof. exact (@lem1950410 x y h2 h3 h4 (@lem1949677 y x h1)). Qed.
Lemma lem1950413 (x : real) (y : real) (h1 : term50) (h2 : term32 x) (h3 : real_lt x y) : term344 x y.
Proof. exact (or_elim (@lem1948537 y) (fun h0 : term30 y => @lem1949671 x y h2 h0) (fun h0 : term32 y => @lem1950411 x y h1 h2 h0 h3)). Qed.
Lemma lem1950414 (x : real) (y : real) (h1 : term50) (h2 : real_lt x y) : term344 x y.
Proof. exact (or_elim (@lem1948542 x) (fun h0 : term30 x => @lem1949575 x y h1 h0 h2) (fun h0 : term32 x => @lem1950413 x y h1 h0 h2)). Qed.
Lemma lem1950415 (x : real) (y : real) (h1 : term50) (h2 : real_lt x y) : (real_lt x y) = (term344 x y).
Proof. exact (prop_ext (fun h3 : real_lt x y => @lem1950414 x y h1 h2) (fun h3 : term344 x y => @lem1949536 x y h2)). Qed.
Lemma lem1950416 (x : real) (y : real) (h1 : term50) (h2 : real_lt x y) : term344 x y.
Proof. exact (EQ_MP (@lem1950415 x y h1 h2) (@lem1949536 x y h2)). Qed.
Lemma lem1950417 (x : real) (y : real) (h1 : term50) : term527 x y.
Proof. exact (fun h0 : real_lt x y => @lem1950416 x y h1 h0). Qed.
Lemma lem1950422 (x : real) (h1 : term50) : term528 x.
Proof. exact (fun y : real => @lem1950417 x y h1). Qed.
Lemma lem1950427 (h1 : term50) : term529.
Proof. exact (fun x : real => @lem1950422 x h1). Qed.
Lemma lem1950428 (h1 : term50) : term50 = term529.
Proof. exact (prop_ext (fun h2 : term50 => @lem1950427 h1) (fun h2 : term529 => @lem1948573 h1)). Qed.
Lemma lem1950429 (h1 : term50) : term529.
Proof. exact (EQ_MP (@lem1950428 h1) (@lem1948573 h1)). Qed.
Lemma lem1950430 : term50 = term529.
Proof. exact (prop_ext (fun h1 : term50 => @lem1950429 h1) (fun h1 : term529 => @lem1949535)). Qed.
Lemma lem1950431 : term529.
Proof. exact (EQ_MP (@lem1950430) (@lem1949535)). Qed.
