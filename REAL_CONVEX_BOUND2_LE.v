Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_CONVEX_BOUND2_LE_term_abbrevs.
Require Import REAL_LE_ADD2_spec.
Require Import REAL_LE_LMUL_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
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
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483529_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483572_spec.
Require Import thm1483574_spec.
Require Import thm1483584_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm19158_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1672515 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1672516 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1672515 h1 x). Qed.
Lemma lem1672517 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1672518 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1672517 x) (@lem1672516 x h1)). Qed.
Lemma lem1672519 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1672518 x h1 y). Qed.
Lemma lem1672520 (y : real) (x : real) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1672521 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1672520 y x) (@lem1672519 x y h1)). Qed.
Lemma lem1672522 (y : real) (x : real) (z : real) (h1 : term0) : term5 y x z.
Proof. exact (@lem1672521 y x h1 z). Qed.
Lemma lem1672523 (y : real) (x : real) (z : real) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1672524 (y : real) (x : real) (z : real) (h1 : term0) : term6 y x z.
Proof. exact (EQ_MP (@lem1672523 y x z) (@lem1672522 y x z h1)). Qed.
Lemma lem1672525 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term7 x y z.
Proof. exact (h1). Qed.
Lemma lem1672526 (x : real) (y : real) (z : real) (h1 : term0) (h2 : term7 x y z) : term8 y x z.
Proof. exact (@lem1672524 y x z h1 (@lem1672525 x y z h2)). Qed.
Lemma lem1672527 (x : real) (y : real) (z : real) (h1 : term7 x y z) : term9 y x z.
Proof. exact (fun h0 : term0 => @lem1672526 x y z h0 h1). Qed.
Lemma lem1672528 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1672529 (x : real) (y : real) (z : real) (h1 : term0) (h2 : term7 x y z) : term8 y x z.
Proof. exact (@lem1672527 x y z h2 (@lem1672528 h1)). Qed.
Lemma lem1672530 (y : real) (x : real) (z : real) (h1 : term0) : term6 y x z.
Proof. exact (fun h0 : term7 x y z => @lem1672529 x y z h1 h0). Qed.
Lemma lem1672531 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (fun z : real => @lem1672530 y x z h1). Qed.
Lemma lem1672532 (y : real) (h1 : term0) : term10 y.
Proof. exact (fun x : real => @lem1672531 y x h1). Qed.
Lemma lem1672533 (h1 : term0) : term11.
Proof. exact (fun y : real => @lem1672532 y h1). Qed.
Lemma lem1672534 : term12.
Proof. exact (fun h0 : term0 => @lem1672533 h0). Qed.
Lemma lem1672535 : term11.
Proof. exact (@lem1672534 (@lem1583207)). Qed.
Lemma lem1672536 (y : real) : term13 y.
Proof. exact (@lem1672535 y). Qed.
Lemma lem1672537 (y : real) : (term13 y) = (term10 y).
Proof. exact (eq_refl (term13 y)). Qed.
Lemma lem1672538 (y : real) : term10 y.
Proof. exact (EQ_MP (@lem1672537 y) (@lem1672536 y)). Qed.
Lemma lem1672539 (y : real) (x : real) : term14 y x.
Proof. exact (@lem1672538 y x). Qed.
Lemma lem1672540 (y : real) (x : real) : (term14 y x) = (term4 y x).
Proof. exact (eq_refl (term14 y x)). Qed.
Lemma lem1672541 (y : real) (x : real) : term4 y x.
Proof. exact (EQ_MP (@lem1672540 y x) (@lem1672539 y x)). Qed.
Lemma lem1672542 (y : real) (x : real) (z : real) : term5 y x z.
Proof. exact (@lem1672541 y x z). Qed.
Lemma lem1672543 (y : real) (x : real) (z : real) : (term5 y x z) = (term6 y x z).
Proof. exact (eq_refl (term5 y x z)). Qed.
Lemma lem1672545 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem1672546 (w : real) (h1 : term15) : term16 w.
Proof. exact (@lem1672545 h1 w). Qed.
Lemma lem1672547 (w : real) : (term16 w) = (term17 w).
Proof. exact (eq_refl (term16 w)). Qed.
Lemma lem1672548 (w : real) (h1 : term15) : term17 w.
Proof. exact (EQ_MP (@lem1672547 w) (@lem1672546 w h1)). Qed.
Lemma lem1672549 (w : real) (x : real) (h1 : term15) : term18 w x.
Proof. exact (@lem1672548 w h1 x). Qed.
Lemma lem1672550 (w : real) (x : real) : (term18 w x) = (term19 w x).
Proof. exact (eq_refl (term18 w x)). Qed.
Lemma lem1672551 (w : real) (x : real) (h1 : term15) : term19 w x.
Proof. exact (EQ_MP (@lem1672550 w x) (@lem1672549 w x h1)). Qed.
Lemma lem1672552 (w : real) (x : real) (y : real) (h1 : term15) : term20 w x y.
Proof. exact (@lem1672551 w x h1 y). Qed.
Lemma lem1672553 (w : real) (y : real) (x : real) : (term20 w x y) = (term21 w y x).
Proof. exact (eq_refl (term20 w x y)). Qed.
Lemma lem1672554 (w : real) (y : real) (x : real) (h1 : term15) : term21 w y x.
Proof. exact (EQ_MP (@lem1672553 w y x) (@lem1672552 w x y h1)). Qed.
Lemma lem1672555 (w : real) (y : real) (x : real) (z : real) (h1 : term15) : term22 w y x z.
Proof. exact (@lem1672554 w y x h1 z). Qed.
Lemma lem1672556 (w : real) (y : real) (x : real) (z : real) : (term22 w y x z) = (term23 w y x z).
Proof. exact (eq_refl (term22 w y x z)). Qed.
Lemma lem1672557 (w : real) (y : real) (x : real) (z : real) (h1 : term15) : term23 w y x z.
Proof. exact (EQ_MP (@lem1672556 w y x z) (@lem1672555 w y x z h1)). Qed.
Lemma lem1672558 (w : real) (x : real) (y : real) (z : real) (h1 : term24 w x y z) : term24 w x y z.
Proof. exact (h1). Qed.
Lemma lem1672559 (w : real) (x : real) (y : real) (z : real) (h1 : term15) (h2 : term24 w x y z) : term25 w y x z.
Proof. exact (@lem1672557 w y x z h1 (@lem1672558 w x y z h2)). Qed.
Lemma lem1672560 (w : real) (x : real) (y : real) (z : real) (h1 : term24 w x y z) : term26 w y x z.
Proof. exact (fun h0 : term15 => @lem1672559 w x y z h0 h1). Qed.
Lemma lem1672561 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem1672562 (w : real) (x : real) (y : real) (z : real) (h1 : term15) (h2 : term24 w x y z) : term25 w y x z.
Proof. exact (@lem1672560 w x y z h2 (@lem1672561 h1)). Qed.
Lemma lem1672563 (w : real) (y : real) (x : real) (z : real) (h1 : term15) : term23 w y x z.
Proof. exact (fun h0 : term24 w x y z => @lem1672562 w x y z h1 h0). Qed.
Lemma lem1672564 (w : real) (y : real) (x : real) (h1 : term15) : term21 w y x.
Proof. exact (fun z : real => @lem1672563 w y x z h1). Qed.
Lemma lem1672565 (w : real) (y : real) (h1 : term15) : term27 w y.
Proof. exact (fun x : real => @lem1672564 w y x h1). Qed.
Lemma lem1672566 (w : real) (h1 : term15) : term28 w.
Proof. exact (fun y : real => @lem1672565 w y h1). Qed.
Lemma lem1672567 (h1 : term15) : term29.
Proof. exact (fun w : real => @lem1672566 w h1). Qed.
Lemma lem1672568 : term30.
Proof. exact (fun h0 : term15 => @lem1672567 h0). Qed.
Lemma lem1672569 : term29.
Proof. exact (@lem1672568 (@lem1502113)). Qed.
Lemma lem1672570 (w : real) : term31 w.
Proof. exact (@lem1672569 w). Qed.
Lemma lem1672571 (w : real) : (term31 w) = (term28 w).
Proof. exact (eq_refl (term31 w)). Qed.
Lemma lem1672572 (w : real) : term28 w.
Proof. exact (EQ_MP (@lem1672571 w) (@lem1672570 w)). Qed.
Lemma lem1672573 (w : real) (y : real) : term32 w y.
Proof. exact (@lem1672572 w y). Qed.
Lemma lem1672574 (w : real) (y : real) : (term32 w y) = (term27 w y).
Proof. exact (eq_refl (term32 w y)). Qed.
Lemma lem1672575 (w : real) (y : real) : term27 w y.
Proof. exact (EQ_MP (@lem1672574 w y) (@lem1672573 w y)). Qed.
Lemma lem1672576 (w : real) (y : real) (x : real) : term33 w y x.
Proof. exact (@lem1672575 w y x). Qed.
Lemma lem1672577 (w : real) (y : real) (x : real) : (term33 w y x) = (term21 w y x).
Proof. exact (eq_refl (term33 w y x)). Qed.
Lemma lem1672578 (w : real) (y : real) (x : real) : term21 w y x.
Proof. exact (EQ_MP (@lem1672577 w y x) (@lem1672576 w y x)). Qed.
Lemma lem1672579 (w : real) (y : real) (x : real) (z : real) : term22 w y x z.
Proof. exact (@lem1672578 w y x z). Qed.
Lemma lem1672580 (w : real) (y : real) (x : real) (z : real) : (term22 w y x z) = (term23 w y x z).
Proof. exact (eq_refl (term22 w y x z)). Qed.
Lemma lem1672582 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : term34 x a y b u v) : term34 x a y b u v.
Proof. exact (h1). Qed.
Lemma lem1672583 (y : real) (b : real) (u : real) (v : real) (h1 : term35 y b u v) : term35 y b u v.
Proof. exact (h1). Qed.
Lemma lem1672584 (x : real) (a : real) (h1 : real_le x a) : real_le x a.
Proof. exact (h1). Qed.
Lemma lem1672585 (u : real) (v : real) (h1 : term36 u v) : term36 u v.
Proof. exact (h1). Qed.
Lemma lem1672586 (y : real) (b : real) (h1 : real_le y b) : real_le y b.
Proof. exact (h1). Qed.
Lemma lem1672587 (u : real) (v : real) (h1 : term37 u v) : term37 u v.
Proof. exact (h1). Qed.
Lemma lem1672588 (u : real) (h1 : term38 u) : term38 u.
Proof. exact (h1). Qed.
Lemma lem1672589 (u : real) (v : real) (h1 : (real_add u v) = term39) : (real_add u v) = term39.
Proof. exact (h1). Qed.
Lemma lem1672590 (v : real) (h1 : term38 v) : term38 v.
Proof. exact (h1). Qed.
Lemma lem1672592 (w : real) (y : real) (x : real) (z : real) : term23 w y x z.
Proof. exact (EQ_MP (@lem1672580 w y x z) (@lem1672579 w y x z)). Qed.
Lemma lem1672593 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : term40 x y u a v b.
Proof. exact (@lem1672592 (real_mul u x) (real_mul v y) (real_mul u a) (real_mul v b)). Qed.
Lemma lem1672595 (y : real) (x : real) (z : real) : term6 y x z.
Proof. exact (EQ_MP (@lem1672543 y x z) (@lem1672542 y x z)). Qed.
Lemma lem1672596 (x : real) (u : real) (a : real) : term6 x u a.
Proof. exact (@lem1672595 x u a). Qed.
Lemma lem1672598 (y : real) (x : real) (z : real) : term6 y x z.
Proof. exact (EQ_MP (@lem1672543 y x z) (@lem1672542 y x z)). Qed.
Lemma lem1672599 (y : real) (v : real) (b : real) : term6 y v b.
Proof. exact (@lem1672598 y v b). Qed.
Lemma lem1672626 (u : real) (x : real) (a : real) : (term41 u x a) = (term42 u x a).
Proof. exact (@lem17045 (term38 u) (real_le x a)). Qed.
Lemma lem1672628 (u : real) (v : real) : (term43 u v) = (term43 u v).
Proof. exact (eq_refl (term43 u v)). Qed.
Lemma lem1672629 (v : real) (u : real) (x : real) (a : real) : (term44 v u x a) = (term45 v u x a).
Proof. exact (MK_COMB (@lem1672628 u v) (@lem1672626 u x a)). Qed.
Lemma lem1672630 (v : real) (u : real) (x : real) (a : real) : (term46 v u x a) = (term44 v u x a).
Proof. exact (@lem17362 ((real_add u v) = term39) (term7 u x a)). Qed.
Lemma lem1672631 (v : real) (u : real) (x : real) (a : real) : (term46 v u x a) = (term45 v u x a).
Proof. exact (TRANS (@lem1672630 v u x a) (@lem1672629 v u x a)). Qed.
Lemma lem1672633 (v : real) : (term47 v) = (term47 v).
Proof. exact (eq_refl (term47 v)). Qed.
Lemma lem1672634 (v : real) (u : real) (x : real) (a : real) : (term48 v u x a) = (term49 v u x a).
Proof. exact (MK_COMB (@lem1672633 v) (@lem1672631 v u x a)). Qed.
Lemma lem1672635 (v : real) (u : real) (x : real) (a : real) : (term50 v u x a) = (term48 v u x a).
Proof. exact (@lem17362 (term38 v) (term51 v u x a)). Qed.
Lemma lem1672636 (v : real) (u : real) (x : real) (a : real) : (term50 v u x a) = (term49 v u x a).
Proof. exact (TRANS (@lem1672635 v u x a) (@lem1672634 v u x a)). Qed.
Lemma lem1672638 (u : real) : (term47 u) = (term47 u).
Proof. exact (eq_refl (term47 u)). Qed.
Lemma lem1672639 (v : real) (u : real) (x : real) (a : real) : (term52 v u x a) = (term53 v u x a).
Proof. exact (MK_COMB (@lem1672638 u) (@lem1672636 v u x a)). Qed.
Lemma lem1672640 (v : real) (u : real) (x : real) (a : real) : (term54 v u x a) = (term52 v u x a).
Proof. exact (@lem17362 (term38 u) (term55 v u x a)). Qed.
Lemma lem1672641 (v : real) (u : real) (x : real) (a : real) : (term54 v u x a) = (term53 v u x a).
Proof. exact (TRANS (@lem1672640 v u x a) (@lem1672639 v u x a)). Qed.
Lemma lem1672643 (y : real) (b : real) : (term56 y b) = (term56 y b).
Proof. exact (eq_refl (term56 y b)). Qed.
Lemma lem1672644 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : (term57 y b v u x a) = (term58 y b v u x a).
Proof. exact (MK_COMB (@lem1672643 y b) (@lem1672641 v u x a)). Qed.
Lemma lem1672645 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : (term59 y b v u x a) = (term57 y b v u x a).
Proof. exact (@lem17362 (real_le y b) (term60 v u x a)). Qed.
Lemma lem1672646 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : (term59 y b v u x a) = (term58 y b v u x a).
Proof. exact (TRANS (@lem1672645 y b v u x a) (@lem1672644 y b v u x a)). Qed.
Lemma lem1672648 (x : real) (a : real) : (term56 x a) = (term56 x a).
Proof. exact (eq_refl (term56 x a)). Qed.
Lemma lem1672649 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : (term61 y b v u x a) = (term62 y b v u x a).
Proof. exact (MK_COMB (@lem1672648 x a) (@lem1672646 y b v u x a)). Qed.
Lemma lem1672650 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : (term63 y b v u x a) = (term61 y b v u x a).
Proof. exact (@lem17362 (real_le x a) (term64 y b v u x a)). Qed.
Lemma lem1672682 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : (term63 y b v u x a) = (term62 y b v u x a).
Proof. exact (TRANS (@lem1672650 y b v u x a) (@lem1672649 y b v u x a)). Qed.
Lemma lem1672683 (a : real) (x : real) : (real_le x a) = (term65 a x).
Proof. exact (@lem1483523 a x). Qed.
Lemma lem1672696 (a : real) (x : real) : (real_sub a x) = (term66 a x).
Proof. exact (@lem1483519 a x). Qed.
Lemma lem1672697 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1672698 (a : real) (x : real) : (term67 a x) = (term68 a x).
Proof. exact (MK_COMB (@lem1672697) (@lem1672696 a x)). Qed.
Lemma lem1672699 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1672700 (a : real) (x : real) : (term65 a x) = (term70 a x).
Proof. exact (MK_COMB (@lem1672698 a x) (@lem1672699)). Qed.
Lemma lem1672701 (a : real) (x : real) : (real_le x a) = (term70 a x).
Proof. exact (TRANS (@lem1672683 a x) (@lem1672700 a x)). Qed.
Lemma lem1672702 (b : real) (y : real) : (real_le y b) = (term65 b y).
Proof. exact (@lem1483523 b y). Qed.
Lemma lem1672715 (b : real) (y : real) : (real_sub b y) = (term66 b y).
Proof. exact (@lem1483519 b y). Qed.
Lemma lem1672716 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1672717 (b : real) (y : real) : (term67 b y) = (term68 b y).
Proof. exact (MK_COMB (@lem1672716) (@lem1672715 b y)). Qed.
Lemma lem1672718 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1672719 (b : real) (y : real) : (term65 b y) = (term70 b y).
Proof. exact (MK_COMB (@lem1672717 b y) (@lem1672718)). Qed.
Lemma lem1672720 (b : real) (y : real) : (real_le y b) = (term70 b y).
Proof. exact (TRANS (@lem1672702 b y) (@lem1672719 b y)). Qed.
Lemma lem1672721 (u : real) : (term38 u) = (term71 u).
Proof. exact (@lem1483523 u term69). Qed.
Lemma lem1672727 (u : real) : (term72 u) = (term73 u).
Proof. exact (@lem1483519 u term69). Qed.
Lemma lem1672729 (x : nat) : (term74 x) = term69.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1672730 : term75 = term69.
Proof. exact (@lem1672729 term76). Qed.
Lemma lem1672731 (u : real) : (real_add u) = (real_add u).
Proof. exact (eq_refl (real_add u)). Qed.
Lemma lem1672732 (u : real) : (term73 u) = (term77 u).
Proof. exact (MK_COMB (@lem1672731 u) (@lem1672730)). Qed.
Lemma lem1672733 (u : real) : (term77 u) = u.
Proof. exact (@lem1483450 u). Qed.
Lemma lem1672734 (u : real) : (term73 u) = u.
Proof. exact (TRANS (@lem1672732 u) (@lem1672733 u)). Qed.
Lemma lem1672736 (u : real) : (term72 u) = u.
Proof. exact (TRANS (@lem1672727 u) (@lem1672734 u)). Qed.
Lemma lem1672737 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1672738 (u : real) : (term78 u) = (real_ge u).
Proof. exact (MK_COMB (@lem1672737) (@lem1672736 u)). Qed.
Lemma lem1672739 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1672740 (u : real) : (term71 u) = (term79 u).
Proof. exact (MK_COMB (@lem1672738 u) (@lem1672739)). Qed.
Lemma lem1672741 (u : real) : (term38 u) = (term79 u).
Proof. exact (TRANS (@lem1672721 u) (@lem1672740 u)). Qed.
Lemma lem1672742 (v : real) : (term38 v) = (term71 v).
Proof. exact (@lem1483523 v term69). Qed.
Lemma lem1672748 (v : real) : (term72 v) = (term73 v).
Proof. exact (@lem1483519 v term69). Qed.
Lemma lem1672750 (x : nat) : (term74 x) = term69.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1672751 : term75 = term69.
Proof. exact (@lem1672750 term76). Qed.
Lemma lem1672752 (v : real) : (real_add v) = (real_add v).
Proof. exact (eq_refl (real_add v)). Qed.
Lemma lem1672753 (v : real) : (term73 v) = (term77 v).
Proof. exact (MK_COMB (@lem1672752 v) (@lem1672751)). Qed.
Lemma lem1672754 (v : real) : (term77 v) = v.
Proof. exact (@lem1483450 v). Qed.
Lemma lem1672755 (v : real) : (term73 v) = v.
Proof. exact (TRANS (@lem1672753 v) (@lem1672754 v)). Qed.
Lemma lem1672757 (v : real) : (term72 v) = v.
Proof. exact (TRANS (@lem1672748 v) (@lem1672755 v)). Qed.
Lemma lem1672758 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1672759 (v : real) : (term78 v) = (real_ge v).
Proof. exact (MK_COMB (@lem1672758) (@lem1672757 v)). Qed.
Lemma lem1672760 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1672761 (v : real) : (term71 v) = (term79 v).
Proof. exact (MK_COMB (@lem1672759 v) (@lem1672760)). Qed.
Lemma lem1672762 (v : real) : (term38 v) = (term79 v).
Proof. exact (TRANS (@lem1672742 v) (@lem1672761 v)). Qed.
Lemma lem1672763 (u : real) (v : real) : ((real_add u v) = term39) = ((term80 u v) = term69).
Proof. exact (@lem1483529 (real_add u v) term39). Qed.
Lemma lem1672775 (u : real) (v : real) : (term80 u v) = (term81 u v).
Proof. exact (@lem1483519 (real_add u v) term39). Qed.
Lemma lem1672777 (m : nat) (n : nat) : (term82 m n) = (term83 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1672778 : term84 = term85.
Proof. exact (@lem1672777 term76 term76). Qed.
Lemma lem1672779 : (term86 = (BIT1 0)) = (term87 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1672780 : term87 = term76.
Proof. exact (EQ_MP (@lem1672779) (@lem940073)). Qed.
Lemma lem1672781 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1672782 : term88 = term39.
Proof. exact (MK_COMB (@lem1672781) (@lem1672780)). Qed.
Lemma lem1672783 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1672784 : term85 = term89.
Proof. exact (MK_COMB (@lem1672783) (@lem1672782)). Qed.
Lemma lem1672785 : term84 = term89.
Proof. exact (TRANS (@lem1672778) (@lem1672784)). Qed.
Lemma lem1672786 (u : real) (v : real) : (term90 u v) = (term90 u v).
Proof. exact (eq_refl (term90 u v)). Qed.
Lemma lem1672787 (u : real) (v : real) : (term81 u v) = (term91 u v).
Proof. exact (MK_COMB (@lem1672786 u v) (@lem1672785)). Qed.
Lemma lem1672792 (u : real) (v : real) : (term91 u v) = (term92 u v).
Proof. exact (@lem1483482 u v term89). Qed.
Lemma lem1672793 (u : real) (v : real) : (term81 u v) = (term92 u v).
Proof. exact (TRANS (@lem1672787 u v) (@lem1672792 u v)). Qed.
Lemma lem1672795 (u : real) (v : real) : (term80 u v) = (term92 u v).
Proof. exact (TRANS (@lem1672775 u v) (@lem1672793 u v)). Qed.
Lemma lem1672796 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1672797 (u : real) (v : real) : (term93 u v) = (term94 u v).
Proof. exact (MK_COMB (@lem1672796) (@lem1672795 u v)). Qed.
Lemma lem1672798 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1672799 (u : real) (v : real) : ((term80 u v) = term69) = ((term92 u v) = term69).
Proof. exact (MK_COMB (@lem1672797 u v) (@lem1672798)). Qed.
Lemma lem1672800 (u : real) (v : real) : ((real_add u v) = term39) = ((term92 u v) = term69).
Proof. exact (TRANS (@lem1672763 u v) (@lem1672799 u v)). Qed.
Lemma lem1672801 (u : real) : (term95 u) = (term96 u).
Proof. exact (@lem1483533 term69 u). Qed.
Lemma lem1672807 (u : real) : (term97 u) = (term98 u).
Proof. exact (@lem1483519 term69 u). Qed.
Lemma lem1672812 (u : real) : (term98 u) = (term99 u).
Proof. exact (@lem1483448 (term99 u)). Qed.
Lemma lem1672814 (u : real) : (term97 u) = (term99 u).
Proof. exact (TRANS (@lem1672807 u) (@lem1672812 u)). Qed.
Lemma lem1672815 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1672816 (u : real) : (term100 u) = (term101 u).
Proof. exact (MK_COMB (@lem1672815) (@lem1672814 u)). Qed.
Lemma lem1672817 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1672818 (u : real) : (term96 u) = (term102 u).
Proof. exact (MK_COMB (@lem1672816 u) (@lem1672817)). Qed.
Lemma lem1672819 (u : real) : (term95 u) = (term102 u).
Proof. exact (TRANS (@lem1672801 u) (@lem1672818 u)). Qed.
Lemma lem1672820 (x : real) (a : real) : (term103 x a) = (term104 x a).
Proof. exact (@lem1483533 x a). Qed.
Lemma lem1672826 (x : real) (a : real) : (real_sub x a) = (term66 x a).
Proof. exact (@lem1483519 x a). Qed.
Lemma lem1672831 (a : real) (x : real) : (term66 x a) = (term105 a x).
Proof. exact (@lem1483488 (term99 a) x). Qed.
Lemma lem1672833 (a : real) (x : real) : (real_sub x a) = (term105 a x).
Proof. exact (TRANS (@lem1672826 x a) (@lem1672831 a x)). Qed.
Lemma lem1672834 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1672835 (a : real) (x : real) : (term106 x a) = (term107 a x).
Proof. exact (MK_COMB (@lem1672834) (@lem1672833 a x)). Qed.
Lemma lem1672836 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1672837 (a : real) (x : real) : (term104 x a) = (term108 a x).
Proof. exact (MK_COMB (@lem1672835 a x) (@lem1672836)). Qed.
Lemma lem1672838 (a : real) (x : real) : (term103 x a) = (term108 a x).
Proof. exact (TRANS (@lem1672820 x a) (@lem1672837 a x)). Qed.
Lemma lem1672839 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1672840 (u : real) : (term109 u) = (term110 u).
Proof. exact (MK_COMB (@lem1672839) (@lem1672819 u)). Qed.
Lemma lem1672841 (u : real) (a : real) (x : real) : (term42 u x a) = (term111 u a x).
Proof. exact (MK_COMB (@lem1672840 u) (@lem1672838 a x)). Qed.
Lemma lem1672842 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1672843 (u : real) (v : real) : (term43 u v) = (term112 u v).
Proof. exact (MK_COMB (@lem1672842) (@lem1672800 u v)). Qed.
Lemma lem1672844 (v : real) (u : real) (a : real) (x : real) : (term45 v u x a) = (term113 v u a x).
Proof. exact (MK_COMB (@lem1672843 u v) (@lem1672841 u a x)). Qed.
Lemma lem1672845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1672846 (v : real) : (term47 v) = (term114 v).
Proof. exact (MK_COMB (@lem1672845) (@lem1672762 v)). Qed.
Lemma lem1672847 (v : real) (u : real) (a : real) (x : real) : (term49 v u x a) = (term115 v u a x).
Proof. exact (MK_COMB (@lem1672846 v) (@lem1672844 v u a x)). Qed.
Lemma lem1672848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1672849 (u : real) : (term47 u) = (term114 u).
Proof. exact (MK_COMB (@lem1672848) (@lem1672741 u)). Qed.
Lemma lem1672850 (v : real) (u : real) (a : real) (x : real) : (term53 v u x a) = (term116 v u a x).
Proof. exact (MK_COMB (@lem1672849 u) (@lem1672847 v u a x)). Qed.
Lemma lem1672851 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1672852 (b : real) (y : real) : (term56 y b) = (term117 b y).
Proof. exact (MK_COMB (@lem1672851) (@lem1672720 b y)). Qed.
Lemma lem1672853 (b : real) (y : real) (v : real) (u : real) (a : real) (x : real) : (term58 y b v u x a) = (term118 b y v u a x).
Proof. exact (MK_COMB (@lem1672852 b y) (@lem1672850 v u a x)). Qed.
Lemma lem1672854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1672855 (a : real) (x : real) : (term56 x a) = (term117 a x).
Proof. exact (MK_COMB (@lem1672854) (@lem1672701 a x)). Qed.
Lemma lem1672856 (b : real) (y : real) (v : real) (u : real) (a : real) (x : real) : (term62 y b v u x a) = (term119 b y v u a x).
Proof. exact (MK_COMB (@lem1672855 a x) (@lem1672853 b y v u a x)). Qed.
Lemma lem1672863 (b : real) (y : real) (v : real) (u : real) (a : real) (x : real) : (term63 y b v u x a) = (term119 b y v u a x).
Proof. exact (TRANS (@lem1672682 y b v u x a) (@lem1672856 b y v u a x)). Qed.
Lemma lem1672880 (u : real) (v : real) (a : real) (x : real) : (term113 v u a x) = (term120 u v a x).
Proof. exact (@lem19158 (term102 u) ((term92 u v) = term69) (term108 a x)). Qed.
Lemma lem1672883 (v : real) : (term114 v) = (term114 v).
Proof. exact (eq_refl (term114 v)). Qed.
Lemma lem1672884 (u : real) (v : real) (a : real) (x : real) : (term115 v u a x) = (term121 u v a x).
Proof. exact (MK_COMB (@lem1672883 v) (@lem1672880 u v a x)). Qed.
Lemma lem1672891 (u : real) (v : real) (a : real) (x : real) : (term121 u v a x) = (term122 u v a x).
Proof. exact (@lem19158 (term123 v u) (term79 v) (term124 u v a x)). Qed.
Lemma lem1672892 (u : real) (v : real) (a : real) (x : real) : (term115 v u a x) = (term122 u v a x).
Proof. exact (TRANS (@lem1672884 u v a x) (@lem1672891 u v a x)). Qed.
Lemma lem1672895 (u : real) : (term114 u) = (term114 u).
Proof. exact (eq_refl (term114 u)). Qed.
Lemma lem1672896 (u : real) (v : real) (a : real) (x : real) : (term116 v u a x) = (term125 u v a x).
Proof. exact (MK_COMB (@lem1672895 u) (@lem1672892 u v a x)). Qed.
Lemma lem1672903 (u : real) (v : real) (a : real) (x : real) : (term125 u v a x) = (term126 u v a x).
Proof. exact (@lem19158 (term127 v u) (term79 u) (term128 u v a x)). Qed.
Lemma lem1672904 (u : real) (v : real) (a : real) (x : real) : (term116 v u a x) = (term126 u v a x).
Proof. exact (TRANS (@lem1672896 u v a x) (@lem1672903 u v a x)). Qed.
Lemma lem1672907 (b : real) (y : real) : (term117 b y) = (term117 b y).
Proof. exact (eq_refl (term117 b y)). Qed.
Lemma lem1672908 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term118 b y v u a x) = (term129 b y u v a x).
Proof. exact (MK_COMB (@lem1672907 b y) (@lem1672904 u v a x)). Qed.
Lemma lem1672915 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term129 b y u v a x) = (term130 b y u v a x).
Proof. exact (@lem19158 (term131 v u) (term70 b y) (term132 u v a x)). Qed.
Lemma lem1672916 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term118 b y v u a x) = (term130 b y u v a x).
Proof. exact (TRANS (@lem1672908 b y u v a x) (@lem1672915 b y u v a x)). Qed.
Lemma lem1672919 (a : real) (x : real) : (term117 a x) = (term117 a x).
Proof. exact (eq_refl (term117 a x)). Qed.
Lemma lem1672920 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term119 b y v u a x) = (term133 b y u v a x).
Proof. exact (MK_COMB (@lem1672919 a x) (@lem1672916 b y u v a x)). Qed.
Lemma lem1672927 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term133 b y u v a x) = (term134 b y u v a x).
Proof. exact (@lem19158 (term135 b y v u) (term70 a x) (term136 b y u v a x)). Qed.
Lemma lem1672928 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term119 b y v u a x) = (term134 b y u v a x).
Proof. exact (TRANS (@lem1672920 b y u v a x) (@lem1672927 b y u v a x)). Qed.
Lemma lem1672929 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) : (term63 y b v u x a) = (term134 b y u v a x).
Proof. exact (TRANS (@lem1672863 b y v u a x) (@lem1672928 b y u v a x)). Qed.
Lemma lem1672939 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term134 b y u v a x) : term134 b y u v a x.
Proof. exact (h1). Qed.
Lemma lem1672940 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term137 a x b y v u.
Proof. exact (h1). Qed.
Lemma lem1672941 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term135 b y v u.
Proof. exact (proj2 (@lem1672940 a x b y v u h1)). Qed.
Lemma lem1672943 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term131 v u.
Proof. exact (proj2 (@lem1672941 a x b y v u h1)). Qed.
Lemma lem1672945 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term127 v u.
Proof. exact (proj2 (@lem1672943 a x b y v u h1)). Qed.
Lemma lem1672946 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term79 u.
Proof. exact (proj1 (@lem1672943 a x b y v u h1)). Qed.
Lemma lem1672947 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term123 v u.
Proof. exact (proj2 (@lem1672945 a x b y v u h1)). Qed.
Lemma lem1672949 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term102 u.
Proof. exact (proj2 (@lem1672947 a x b y v u h1)). Qed.
Lemma lem1672950 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : (term92 u v) = term69.
Proof. exact (proj1 (@lem1672947 a x b y v u h1)). Qed.
Lemma lem1672952 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1672953 : term139 = term140.
Proof. exact (@lem1672952 (NUMERAL 0) term76). Qed.
Lemma lem1672954 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1672955 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1672956 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1672955 h1) (fun h1 : term140 = True => @lem1672954)). Qed.
Lemma lem1672957 : term140 = True.
Proof. exact (EQ_MP (@lem1672956) (@lem1672954)). Qed.
Lemma lem1672958 : term139 = True.
Proof. exact (TRANS (@lem1672953) (@lem1672957)). Qed.
Lemma lem1672959 : True = term139.
Proof. exact (SYM (@lem1672958)). Qed.
Lemma lem1672960 : term139.
Proof. exact (EQ_MP (@lem1672959) (@lem0)). Qed.
Lemma lem1672961 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term142 u.
Proof. exact (conj (@lem1672960) (@lem1672946 a x b y v u h1)). Qed.
Lemma lem1672963 (x : real) (y : real) : term143 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1672964 (u : real) : term144 u.
Proof. exact (@lem1672963 term39 u). Qed.
Lemma lem1672965 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term145 u.
Proof. exact (@lem1672964 u (@lem1672961 a x b y v u h1)). Qed.
Lemma lem1672966 (u : real) : (term146 u) = u.
Proof. exact (@lem1483460 u). Qed.
Lemma lem1672967 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1672968 (u : real) : (term147 u) = (real_ge u).
Proof. exact (MK_COMB (@lem1672967) (@lem1672966 u)). Qed.
Lemma lem1672969 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1672970 (u : real) : (term145 u) = (term79 u).
Proof. exact (MK_COMB (@lem1672968 u) (@lem1672969)). Qed.
Lemma lem1672971 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term79 u.
Proof. exact (EQ_MP (@lem1672970 u) (@lem1672965 a x b y v u h1)). Qed.
Lemma lem1672973 (y : real) : term148 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1672974 (u : real) (v : real) : term149 u v.
Proof. exact (@lem1672973 (term92 u v)). Qed.
Lemma lem1672975 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term150 u v.
Proof. exact (@lem1672974 u v (@lem1672950 a x b y v u h1)). Qed.
Lemma lem1672976 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term151 u v.
Proof. exact (@lem1672975 a x b y v u h1 term89). Qed.
Lemma lem1672977 (u : real) (v : real) : (term151 u v) = ((term152 u v) = term69).
Proof. exact (eq_refl (term151 u v)). Qed.
Lemma lem1672978 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : (term152 u v) = term69.
Proof. exact (EQ_MP (@lem1672977 u v) (@lem1672976 a x b y v u h1)). Qed.
Lemma lem1672979 (u : real) (v : real) : (term152 u v) = (term153 u v).
Proof. exact (@lem1483508 u term89 (term154 v)). Qed.
Lemma lem1672980 (v : real) : (term155 v) = (term156 v).
Proof. exact (@lem1483508 v term89 term89). Qed.
Lemma lem1672982 (m : nat) (n : nat) : (term157 m n) = (term158 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1672983 : term159 = term88.
Proof. exact (@lem1672982 term76 term76). Qed.
Lemma lem1672984 : (term86 = (BIT1 0)) = (term87 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1672985 : term87 = term76.
Proof. exact (EQ_MP (@lem1672984) (@lem940073)). Qed.
Lemma lem1672986 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1672987 : term88 = term39.
Proof. exact (MK_COMB (@lem1672986) (@lem1672985)). Qed.
Lemma lem1672988 : term159 = term39.
Proof. exact (TRANS (@lem1672983) (@lem1672987)). Qed.
Lemma lem1672991 (v : real) : (term160 v) = (term160 v).
Proof. exact (eq_refl (term160 v)). Qed.
Lemma lem1672992 (v : real) : (term156 v) = (term161 v).
Proof. exact (MK_COMB (@lem1672991 v) (@lem1672988)). Qed.
Lemma lem1672993 (v : real) : (term155 v) = (term161 v).
Proof. exact (TRANS (@lem1672980 v) (@lem1672992 v)). Qed.
Lemma lem1672996 (u : real) : (term160 u) = (term160 u).
Proof. exact (eq_refl (term160 u)). Qed.
Lemma lem1672997 (u : real) (v : real) : (term153 u v) = (term162 u v).
Proof. exact (MK_COMB (@lem1672996 u) (@lem1672993 v)). Qed.
Lemma lem1672998 (u : real) (v : real) : (term152 u v) = (term162 u v).
Proof. exact (TRANS (@lem1672979 u v) (@lem1672997 u v)). Qed.
Lemma lem1672999 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1673000 (u : real) (v : real) : (term163 u v) = (term164 u v).
Proof. exact (MK_COMB (@lem1672999) (@lem1672998 u v)). Qed.
Lemma lem1673001 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673002 (u : real) (v : real) : ((term152 u v) = term69) = ((term162 u v) = term69).
Proof. exact (MK_COMB (@lem1673000 u v) (@lem1673001)). Qed.
Lemma lem1673003 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : (term162 u v) = term69.
Proof. exact (EQ_MP (@lem1673002 u v) (@lem1672978 a x b y v u h1)). Qed.
Lemma lem1673004 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term165 v u.
Proof. exact (conj (@lem1673003 a x b y v u h1) (@lem1672971 a x b y v u h1)). Qed.
Lemma lem1673006 (x : real) (y : real) : term166 x y.
Proof. exact (proj1 (@lem1483572 x y)). Qed.
Lemma lem1673007 (v : real) (u : real) : term167 v u.
Proof. exact (@lem1673006 (term162 u v) u). Qed.
Lemma lem1673008 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term168 v u.
Proof. exact (@lem1673007 v u (@lem1673004 a x b y v u h1)). Qed.
Lemma lem1673009 (u : real) (v : real) : (term169 v u) = (term170 u v).
Proof. exact (@lem1483486 (term99 u) u (term161 v)). Qed.
Lemma lem1673010 (u : real) : (term171 u) = (term172 u).
Proof. exact (@lem1483440 term89 u). Qed.
Lemma lem1673012 (m : nat) : (term173 m) = term69.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1673013 : term174 = term69.
Proof. exact (@lem1673012 term76). Qed.
Lemma lem1673014 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1673015 : term175 = term176.
Proof. exact (MK_COMB (@lem1673014) (@lem1673013)). Qed.
Lemma lem1673016 (u : real) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem1673017 (u : real) : (term172 u) = (term177 u).
Proof. exact (MK_COMB (@lem1673015) (@lem1673016 u)). Qed.
Lemma lem1673018 (u : real) : (term171 u) = (term177 u).
Proof. exact (TRANS (@lem1673010 u) (@lem1673017 u)). Qed.
Lemma lem1673019 (u : real) : (term177 u) = term69.
Proof. exact (@lem1483446 u). Qed.
Lemma lem1673020 (u : real) : (term171 u) = term69.
Proof. exact (TRANS (@lem1673018 u) (@lem1673019 u)). Qed.
Lemma lem1673021 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1673022 (u : real) : (term178 u) = term179.
Proof. exact (MK_COMB (@lem1673021) (@lem1673020 u)). Qed.
Lemma lem1673023 (v : real) : (term161 v) = (term161 v).
Proof. exact (eq_refl (term161 v)). Qed.
Lemma lem1673024 (u : real) (v : real) : (term170 u v) = (term180 v).
Proof. exact (MK_COMB (@lem1673022 u) (@lem1673023 v)). Qed.
Lemma lem1673025 (u : real) (v : real) : (term169 v u) = (term180 v).
Proof. exact (TRANS (@lem1673009 u v) (@lem1673024 u v)). Qed.
Lemma lem1673026 (v : real) : (term180 v) = (term161 v).
Proof. exact (@lem1483448 (term161 v)). Qed.
Lemma lem1673027 (u : real) (v : real) : (term169 v u) = (term161 v).
Proof. exact (TRANS (@lem1673025 u v) (@lem1673026 v)). Qed.
Lemma lem1673028 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1673029 (u : real) (v : real) : (term181 v u) = (term182 v).
Proof. exact (MK_COMB (@lem1673028) (@lem1673027 u v)). Qed.
Lemma lem1673030 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673031 (u : real) (v : real) : (term168 v u) = (term183 v).
Proof. exact (MK_COMB (@lem1673029 u v) (@lem1673030)). Qed.
Lemma lem1673032 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term183 v.
Proof. exact (EQ_MP (@lem1673031 u v) (@lem1673008 a x b y v u h1)). Qed.
Lemma lem1673034 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1673035 : term139 = term140.
Proof. exact (@lem1673034 (NUMERAL 0) term76). Qed.
Lemma lem1673036 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1673037 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1673038 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1673037 h1) (fun h1 : term140 = True => @lem1673036)). Qed.
Lemma lem1673039 : term140 = True.
Proof. exact (EQ_MP (@lem1673038) (@lem1673036)). Qed.
Lemma lem1673040 : term139 = True.
Proof. exact (TRANS (@lem1673035) (@lem1673039)). Qed.
Lemma lem1673041 : True = term139.
Proof. exact (SYM (@lem1673040)). Qed.
Lemma lem1673042 : term139.
Proof. exact (EQ_MP (@lem1673041) (@lem0)). Qed.
Lemma lem1673043 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term184 v.
Proof. exact (conj (@lem1673042) (@lem1673032 a x b y v u h1)). Qed.
Lemma lem1673045 (x : real) (y : real) : term143 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1673046 (v : real) : term185 v.
Proof. exact (@lem1673045 term39 (term161 v)). Qed.
Lemma lem1673047 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term186 v.
Proof. exact (@lem1673046 v (@lem1673043 a x b y v u h1)). Qed.
Lemma lem1673048 (v : real) : (term187 v) = (term161 v).
Proof. exact (@lem1483460 (term161 v)). Qed.
Lemma lem1673049 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1673050 (v : real) : (term188 v) = (term182 v).
Proof. exact (MK_COMB (@lem1673049) (@lem1673048 v)). Qed.
Lemma lem1673051 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673052 (v : real) : (term186 v) = (term183 v).
Proof. exact (MK_COMB (@lem1673050 v) (@lem1673051)). Qed.
Lemma lem1673053 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term183 v.
Proof. exact (EQ_MP (@lem1673052 v) (@lem1673047 a x b y v u h1)). Qed.
Lemma lem1673055 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1673056 : term139 = term140.
Proof. exact (@lem1673055 (NUMERAL 0) term76). Qed.
Lemma lem1673057 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1673058 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1673059 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1673058 h1) (fun h1 : term140 = True => @lem1673057)). Qed.
Lemma lem1673060 : term140 = True.
Proof. exact (EQ_MP (@lem1673059) (@lem1673057)). Qed.
Lemma lem1673061 : term139 = True.
Proof. exact (TRANS (@lem1673056) (@lem1673060)). Qed.
Lemma lem1673062 : True = term139.
Proof. exact (SYM (@lem1673061)). Qed.
Lemma lem1673063 : term139.
Proof. exact (EQ_MP (@lem1673062) (@lem0)). Qed.
Lemma lem1673064 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term189 u.
Proof. exact (conj (@lem1673063) (@lem1672949 a x b y v u h1)). Qed.
Lemma lem1673066 (x : real) (y : real) : term190 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1673067 (u : real) : term191 u.
Proof. exact (@lem1673066 term39 (term99 u)). Qed.
Lemma lem1673068 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term192 u.
Proof. exact (@lem1673067 u (@lem1673064 a x b y v u h1)). Qed.
Lemma lem1673069 (u : real) : (term193 u) = (term99 u).
Proof. exact (@lem1483460 (term99 u)). Qed.
Lemma lem1673070 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1673071 (u : real) : (term194 u) = (term101 u).
Proof. exact (MK_COMB (@lem1673070) (@lem1673069 u)). Qed.
Lemma lem1673072 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673073 (u : real) : (term192 u) = (term102 u).
Proof. exact (MK_COMB (@lem1673071 u) (@lem1673072)). Qed.
Lemma lem1673074 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term102 u.
Proof. exact (EQ_MP (@lem1673073 u) (@lem1673068 a x b y v u h1)). Qed.
Lemma lem1673076 (y : real) : term148 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem1673077 (u : real) (v : real) : term149 u v.
Proof. exact (@lem1673076 (term92 u v)). Qed.
Lemma lem1673078 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term150 u v.
Proof. exact (@lem1673077 u v (@lem1672950 a x b y v u h1)). Qed.
Lemma lem1673079 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term195 u v.
Proof. exact (@lem1673078 a x b y v u h1 term39). Qed.
Lemma lem1673080 (u : real) (v : real) : (term195 u v) = ((term196 u v) = term69).
Proof. exact (eq_refl (term195 u v)). Qed.
Lemma lem1673081 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : (term196 u v) = term69.
Proof. exact (EQ_MP (@lem1673080 u v) (@lem1673079 a x b y v u h1)). Qed.
Lemma lem1673082 (u : real) (v : real) : (term196 u v) = (term92 u v).
Proof. exact (@lem1483460 (term92 u v)). Qed.
Lemma lem1673083 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1673084 (u : real) (v : real) : (term197 u v) = (term94 u v).
Proof. exact (MK_COMB (@lem1673083) (@lem1673082 u v)). Qed.
Lemma lem1673085 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673086 (u : real) (v : real) : ((term196 u v) = term69) = ((term92 u v) = term69).
Proof. exact (MK_COMB (@lem1673084 u v) (@lem1673085)). Qed.
Lemma lem1673087 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : (term92 u v) = term69.
Proof. exact (EQ_MP (@lem1673086 u v) (@lem1673081 a x b y v u h1)). Qed.
Lemma lem1673088 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term123 v u.
Proof. exact (conj (@lem1673087 a x b y v u h1) (@lem1673074 a x b y v u h1)). Qed.
Lemma lem1673090 (x : real) (y : real) : term198 x y.
Proof. exact (proj1 (@lem1483574 x y)). Qed.
Lemma lem1673091 (v : real) (u : real) : term199 v u.
Proof. exact (@lem1673090 (term92 u v) (term99 u)). Qed.
Lemma lem1673092 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term200 v u.
Proof. exact (@lem1673091 v u (@lem1673088 a x b y v u h1)). Qed.
Lemma lem1673093 (u : real) (v : real) : (term201 v u) = (term202 u v).
Proof. exact (@lem1483486 u (term99 u) (term154 v)). Qed.
Lemma lem1673094 (u : real) : (term203 u) = (term172 u).
Proof. exact (@lem1483442 term89 u). Qed.
Lemma lem1673096 (m : nat) : (term173 m) = term69.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1673097 : term174 = term69.
Proof. exact (@lem1673096 term76). Qed.
Lemma lem1673098 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1673099 : term175 = term176.
Proof. exact (MK_COMB (@lem1673098) (@lem1673097)). Qed.
Lemma lem1673100 (u : real) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem1673101 (u : real) : (term172 u) = (term177 u).
Proof. exact (MK_COMB (@lem1673099) (@lem1673100 u)). Qed.
Lemma lem1673102 (u : real) : (term203 u) = (term177 u).
Proof. exact (TRANS (@lem1673094 u) (@lem1673101 u)). Qed.
Lemma lem1673103 (u : real) : (term177 u) = term69.
Proof. exact (@lem1483446 u). Qed.
Lemma lem1673104 (u : real) : (term203 u) = term69.
Proof. exact (TRANS (@lem1673102 u) (@lem1673103 u)). Qed.
Lemma lem1673105 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1673106 (u : real) : (term204 u) = term179.
Proof. exact (MK_COMB (@lem1673105) (@lem1673104 u)). Qed.
Lemma lem1673107 (v : real) : (term154 v) = (term154 v).
Proof. exact (eq_refl (term154 v)). Qed.
Lemma lem1673108 (u : real) (v : real) : (term202 u v) = (term205 v).
Proof. exact (MK_COMB (@lem1673106 u) (@lem1673107 v)). Qed.
Lemma lem1673109 (u : real) (v : real) : (term201 v u) = (term205 v).
Proof. exact (TRANS (@lem1673093 u v) (@lem1673108 u v)). Qed.
Lemma lem1673110 (v : real) : (term205 v) = (term154 v).
Proof. exact (@lem1483448 (term154 v)). Qed.
Lemma lem1673111 (u : real) (v : real) : (term201 v u) = (term154 v).
Proof. exact (TRANS (@lem1673109 u v) (@lem1673110 v)). Qed.
Lemma lem1673112 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1673113 (u : real) (v : real) : (term206 v u) = (term207 v).
Proof. exact (MK_COMB (@lem1673112) (@lem1673111 u v)). Qed.
Lemma lem1673114 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673115 (u : real) (v : real) : (term200 v u) = (term208 v).
Proof. exact (MK_COMB (@lem1673113 u v) (@lem1673114)). Qed.
Lemma lem1673116 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term208 v.
Proof. exact (EQ_MP (@lem1673115 u v) (@lem1673092 a x b y v u h1)). Qed.
Lemma lem1673118 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1673119 : term139 = term140.
Proof. exact (@lem1673118 (NUMERAL 0) term76). Qed.
Lemma lem1673120 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1673121 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1673122 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1673121 h1) (fun h1 : term140 = True => @lem1673120)). Qed.
Lemma lem1673123 : term140 = True.
Proof. exact (EQ_MP (@lem1673122) (@lem1673120)). Qed.
Lemma lem1673124 : term139 = True.
Proof. exact (TRANS (@lem1673119) (@lem1673123)). Qed.
Lemma lem1673125 : True = term139.
Proof. exact (SYM (@lem1673124)). Qed.
Lemma lem1673126 : term139.
Proof. exact (EQ_MP (@lem1673125) (@lem0)). Qed.
Lemma lem1673127 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term209 v.
Proof. exact (conj (@lem1673126) (@lem1673116 a x b y v u h1)). Qed.
Lemma lem1673129 (x : real) (y : real) : term190 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1673130 (v : real) : term210 v.
Proof. exact (@lem1673129 term39 (term154 v)). Qed.
Lemma lem1673131 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term211 v.
Proof. exact (@lem1673130 v (@lem1673127 a x b y v u h1)). Qed.
Lemma lem1673132 (v : real) : (term212 v) = (term154 v).
Proof. exact (@lem1483460 (term154 v)). Qed.
Lemma lem1673133 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1673134 (v : real) : (term213 v) = (term207 v).
Proof. exact (MK_COMB (@lem1673133) (@lem1673132 v)). Qed.
Lemma lem1673135 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673136 (v : real) : (term211 v) = (term208 v).
Proof. exact (MK_COMB (@lem1673134 v) (@lem1673135)). Qed.
Lemma lem1673137 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term208 v.
Proof. exact (EQ_MP (@lem1673136 v) (@lem1673131 a x b y v u h1)). Qed.
Lemma lem1673138 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term214 v.
Proof. exact (conj (@lem1673137 a x b y v u h1) (@lem1673053 a x b y v u h1)). Qed.
Lemma lem1673140 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1673141 (v : real) : term216 v.
Proof. exact (@lem1673140 (term154 v) (term161 v)). Qed.
Lemma lem1673142 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term217 v.
Proof. exact (@lem1673141 v (@lem1673138 a x b y v u h1)). Qed.
Lemma lem1673143 (v : real) : (term218 v) = (term219 v).
Proof. exact (@lem1483480 v (term99 v) term89 term39). Qed.
Lemma lem1673144 (v : real) : (term203 v) = (term172 v).
Proof. exact (@lem1483442 term89 v). Qed.
Lemma lem1673146 (m : nat) : (term173 m) = term69.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1673147 : term174 = term69.
Proof. exact (@lem1673146 term76). Qed.
Lemma lem1673148 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1673149 : term175 = term176.
Proof. exact (MK_COMB (@lem1673148) (@lem1673147)). Qed.
Lemma lem1673150 (v : real) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem1673151 (v : real) : (term172 v) = (term177 v).
Proof. exact (MK_COMB (@lem1673149) (@lem1673150 v)). Qed.
Lemma lem1673152 (v : real) : (term203 v) = (term177 v).
Proof. exact (TRANS (@lem1673144 v) (@lem1673151 v)). Qed.
Lemma lem1673153 (v : real) : (term177 v) = term69.
Proof. exact (@lem1483446 v). Qed.
Lemma lem1673154 (v : real) : (term203 v) = term69.
Proof. exact (TRANS (@lem1673152 v) (@lem1673153 v)). Qed.
Lemma lem1673155 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1673156 (v : real) : (term204 v) = term179.
Proof. exact (MK_COMB (@lem1673155) (@lem1673154 v)). Qed.
Lemma lem1673158 (m : nat) : (term173 m) = term69.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1673159 : term174 = term69.
Proof. exact (@lem1673158 term76). Qed.
Lemma lem1673160 (v : real) : (term219 v) = term220.
Proof. exact (MK_COMB (@lem1673156 v) (@lem1673159)). Qed.
Lemma lem1673161 (v : real) : (term218 v) = term220.
Proof. exact (TRANS (@lem1673143 v) (@lem1673160 v)). Qed.
Lemma lem1673162 : term220 = term69.
Proof. exact (@lem1483448 term69). Qed.
Lemma lem1673163 (v : real) : (term218 v) = term69.
Proof. exact (TRANS (@lem1673161 v) (@lem1673162)). Qed.
Lemma lem1673164 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1673165 (v : real) : (term221 v) = term222.
Proof. exact (MK_COMB (@lem1673164) (@lem1673163 v)). Qed.
Lemma lem1673166 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673167 (v : real) : (term217 v) = term223.
Proof. exact (MK_COMB (@lem1673165 v) (@lem1673166)). Qed.
Lemma lem1673168 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : term223.
Proof. exact (EQ_MP (@lem1673167 v) (@lem1673142 a x b y v u h1)). Qed.
Lemma lem1673170 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1673171 : term223 = term224.
Proof. exact (@lem1673170 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1673172 : term224 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1673173 : term223 = False.
Proof. exact (TRANS (@lem1673171) (@lem1673172)). Qed.
Lemma lem1673174 (a : real) (x : real) (b : real) (y : real) (v : real) (u : real) (h1 : term137 a x b y v u) : False.
Proof. exact (EQ_MP (@lem1673173) (@lem1673168 a x b y v u h1)). Qed.
Lemma lem1673175 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : term225 b y u v a x.
Proof. exact (h1). Qed.
Lemma lem1673176 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : term136 b y u v a x.
Proof. exact (proj2 (@lem1673175 b y u v a x h1)). Qed.
Lemma lem1673177 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : term70 a x.
Proof. exact (proj1 (@lem1673175 b y u v a x h1)). Qed.
Lemma lem1673178 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : term132 u v a x.
Proof. exact (proj2 (@lem1673176 b y u v a x h1)). Qed.
Lemma lem1673180 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : term128 u v a x.
Proof. exact (proj2 (@lem1673178 b y u v a x h1)). Qed.
Lemma lem1673182 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : term124 u v a x.
Proof. exact (proj2 (@lem1673180 b y u v a x h1)). Qed.
Lemma lem1673184 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : term108 a x.
Proof. exact (proj2 (@lem1673182 b y u v a x h1)). Qed.
Lemma lem1673187 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1673188 : term139 = term140.
Proof. exact (@lem1673187 (NUMERAL 0) term76). Qed.
Lemma lem1673189 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1673190 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1673191 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1673190 h1) (fun h1 : term140 = True => @lem1673189)). Qed.
Lemma lem1673192 : term140 = True.
Proof. exact (EQ_MP (@lem1673191) (@lem1673189)). Qed.
Lemma lem1673193 : term139 = True.
Proof. exact (TRANS (@lem1673188) (@lem1673192)). Qed.
Lemma lem1673194 : True = term139.
Proof. exact (SYM (@lem1673193)). Qed.
Lemma lem1673195 : term139.
Proof. exact (EQ_MP (@lem1673194) (@lem0)). Qed.
Lemma lem1673196 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : term226 a x.
Proof. exact (conj (@lem1673195) (@lem1673177 b y u v a x h1)). Qed.
Lemma lem1673198 (x : real) (y : real) : term143 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1673199 (a : real) (x : real) : term227 a x.
Proof. exact (@lem1673198 term39 (term66 a x)). Qed.
Lemma lem1673200 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : term228 a x.
Proof. exact (@lem1673199 a x (@lem1673196 b y u v a x h1)). Qed.
Lemma lem1673201 (a : real) (x : real) : (term229 a x) = (term66 a x).
Proof. exact (@lem1483460 (term66 a x)). Qed.
Lemma lem1673202 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1673203 (a : real) (x : real) : (term230 a x) = (term68 a x).
Proof. exact (MK_COMB (@lem1673202) (@lem1673201 a x)). Qed.
Lemma lem1673204 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673205 (a : real) (x : real) : (term228 a x) = (term70 a x).
Proof. exact (MK_COMB (@lem1673203 a x) (@lem1673204)). Qed.
Lemma lem1673206 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : term70 a x.
Proof. exact (EQ_MP (@lem1673205 a x) (@lem1673200 b y u v a x h1)). Qed.
Lemma lem1673208 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1673209 : term139 = term140.
Proof. exact (@lem1673208 (NUMERAL 0) term76). Qed.
Lemma lem1673210 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1673211 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1673212 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1673211 h1) (fun h1 : term140 = True => @lem1673210)). Qed.
Lemma lem1673213 : term140 = True.
Proof. exact (EQ_MP (@lem1673212) (@lem1673210)). Qed.
Lemma lem1673214 : term139 = True.
Proof. exact (TRANS (@lem1673209) (@lem1673213)). Qed.
Lemma lem1673215 : True = term139.
Proof. exact (SYM (@lem1673214)). Qed.
Lemma lem1673216 : term139.
Proof. exact (EQ_MP (@lem1673215) (@lem0)). Qed.
Lemma lem1673217 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : term231 a x.
Proof. exact (conj (@lem1673216) (@lem1673184 b y u v a x h1)). Qed.
Lemma lem1673219 (x : real) (y : real) : term190 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1673220 (a : real) (x : real) : term232 a x.
Proof. exact (@lem1673219 term39 (term105 a x)). Qed.
Lemma lem1673221 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : term233 a x.
Proof. exact (@lem1673220 a x (@lem1673217 b y u v a x h1)). Qed.
Lemma lem1673222 (a : real) (x : real) : (term234 a x) = (term105 a x).
Proof. exact (@lem1483460 (term105 a x)). Qed.
Lemma lem1673223 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1673224 (a : real) (x : real) : (term235 a x) = (term107 a x).
Proof. exact (MK_COMB (@lem1673223) (@lem1673222 a x)). Qed.
Lemma lem1673225 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673226 (a : real) (x : real) : (term233 a x) = (term108 a x).
Proof. exact (MK_COMB (@lem1673224 a x) (@lem1673225)). Qed.
Lemma lem1673227 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : term108 a x.
Proof. exact (EQ_MP (@lem1673226 a x) (@lem1673221 b y u v a x h1)). Qed.
Lemma lem1673228 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : term236 a x.
Proof. exact (conj (@lem1673227 b y u v a x h1) (@lem1673206 b y u v a x h1)). Qed.
Lemma lem1673230 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1673231 (a : real) (x : real) : term237 a x.
Proof. exact (@lem1673230 (term105 a x) (term66 a x)). Qed.
Lemma lem1673232 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : term238 a x.
Proof. exact (@lem1673231 a x (@lem1673228 b y u v a x h1)). Qed.
Lemma lem1673233 (a : real) (x : real) : (term239 a x) = (term240 a x).
Proof. exact (@lem1483480 (term99 a) a x (term99 x)). Qed.
Lemma lem1673234 (a : real) : (term171 a) = (term172 a).
Proof. exact (@lem1483440 term89 a). Qed.
Lemma lem1673236 (m : nat) : (term173 m) = term69.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1673237 : term174 = term69.
Proof. exact (@lem1673236 term76). Qed.
Lemma lem1673238 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1673239 : term175 = term176.
Proof. exact (MK_COMB (@lem1673238) (@lem1673237)). Qed.
Lemma lem1673240 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1673241 (a : real) : (term172 a) = (term177 a).
Proof. exact (MK_COMB (@lem1673239) (@lem1673240 a)). Qed.
Lemma lem1673242 (a : real) : (term171 a) = (term177 a).
Proof. exact (TRANS (@lem1673234 a) (@lem1673241 a)). Qed.
Lemma lem1673243 (a : real) : (term177 a) = term69.
Proof. exact (@lem1483446 a). Qed.
Lemma lem1673244 (a : real) : (term171 a) = term69.
Proof. exact (TRANS (@lem1673242 a) (@lem1673243 a)). Qed.
Lemma lem1673245 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1673246 (a : real) : (term178 a) = term179.
Proof. exact (MK_COMB (@lem1673245) (@lem1673244 a)). Qed.
Lemma lem1673247 (x : real) : (term203 x) = (term172 x).
Proof. exact (@lem1483442 term89 x). Qed.
Lemma lem1673249 (m : nat) : (term173 m) = term69.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1673250 : term174 = term69.
Proof. exact (@lem1673249 term76). Qed.
Lemma lem1673251 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1673252 : term175 = term176.
Proof. exact (MK_COMB (@lem1673251) (@lem1673250)). Qed.
Lemma lem1673253 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1673254 (x : real) : (term172 x) = (term177 x).
Proof. exact (MK_COMB (@lem1673252) (@lem1673253 x)). Qed.
Lemma lem1673255 (x : real) : (term203 x) = (term177 x).
Proof. exact (TRANS (@lem1673247 x) (@lem1673254 x)). Qed.
Lemma lem1673256 (x : real) : (term177 x) = term69.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1673257 (x : real) : (term203 x) = term69.
Proof. exact (TRANS (@lem1673255 x) (@lem1673256 x)). Qed.
Lemma lem1673258 (a : real) (x : real) : (term240 a x) = term220.
Proof. exact (MK_COMB (@lem1673246 a) (@lem1673257 x)). Qed.
Lemma lem1673259 (a : real) (x : real) : (term239 a x) = term220.
Proof. exact (TRANS (@lem1673233 a x) (@lem1673258 a x)). Qed.
Lemma lem1673260 : term220 = term69.
Proof. exact (@lem1483448 term69). Qed.
Lemma lem1673261 (a : real) (x : real) : (term239 a x) = term69.
Proof. exact (TRANS (@lem1673259 a x) (@lem1673260)). Qed.
Lemma lem1673262 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1673263 (a : real) (x : real) : (term241 a x) = term222.
Proof. exact (MK_COMB (@lem1673262) (@lem1673261 a x)). Qed.
Lemma lem1673264 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673265 (a : real) (x : real) : (term238 a x) = term223.
Proof. exact (MK_COMB (@lem1673263 a x) (@lem1673264)). Qed.
Lemma lem1673266 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : term223.
Proof. exact (EQ_MP (@lem1673265 a x) (@lem1673232 b y u v a x h1)). Qed.
Lemma lem1673268 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1673269 : term223 = term224.
Proof. exact (@lem1673268 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1673270 : term224 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1673271 : term223 = False.
Proof. exact (TRANS (@lem1673269) (@lem1673270)). Qed.
Lemma lem1673272 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term225 b y u v a x) : False.
Proof. exact (EQ_MP (@lem1673271) (@lem1673266 b y u v a x h1)). Qed.
Lemma lem1673273 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term134 b y u v a x) : False.
Proof. exact (or_elim (@lem1672939 b y u v a x h1) (fun h0 : term137 a x b y v u => @lem1673174 a x b y v u h0) (fun h0 : term225 b y u v a x => @lem1673272 b y u v a x h0)). Qed.
Lemma lem1673275 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term134 b y u v a x) : term134 b y u v a x.
Proof. exact (h1). Qed.
Lemma lem1673276 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term134 b y u v a x) : (term134 b y u v a x) = False.
Proof. exact (prop_ext (fun h2 : term134 b y u v a x => @lem1673273 b y u v a x h1) (fun h2 : False => @lem1673275 b y u v a x h1)). Qed.
Lemma lem1673277 (b : real) (y : real) (u : real) (v : real) (a : real) (x : real) (h1 : term134 b y u v a x) : False.
Proof. exact (EQ_MP (@lem1673276 b y u v a x h1) (@lem1673275 b y u v a x h1)). Qed.
Lemma lem1673278 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) (h1 : term63 y b v u x a) : term63 y b v u x a.
Proof. exact (h1). Qed.
Lemma lem1673279 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) (h1 : term63 y b v u x a) : term134 b y u v a x.
Proof. exact (EQ_MP (@lem1672929 b y u v a x) (@lem1673278 y b v u x a h1)). Qed.
Lemma lem1673280 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) (h1 : term63 y b v u x a) : (term134 b y u v a x) = False.
Proof. exact (prop_ext (fun h2 : term134 b y u v a x => @lem1673277 b y u v a x h2) (fun h2 : False => @lem1673279 y b v u x a h1)). Qed.
Lemma lem1673281 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) (h1 : term63 y b v u x a) : False.
Proof. exact (EQ_MP (@lem1673280 y b v u x a h1) (@lem1673279 y b v u x a h1)). Qed.
Lemma lem1673282 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : term242 y b v u x a.
Proof. exact (fun h0 : term63 y b v u x a => @lem1673281 y b v u x a h0). Qed.
Lemma lem1673283 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : term243 y b v u x a.
Proof. exact (@lem1386578 (term244 y b v u x a)). Qed.
Lemma lem1673284 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) : term244 y b v u x a.
Proof. exact (@lem1673283 y b v u x a (@lem1673282 y b v u x a)). Qed.
Lemma lem1673311 (v : real) (y : real) (b : real) : (term41 v y b) = (term42 v y b).
Proof. exact (@lem17045 (term38 v) (real_le y b)). Qed.
Lemma lem1673313 (u : real) (v : real) : (term43 u v) = (term43 u v).
Proof. exact (eq_refl (term43 u v)). Qed.
Lemma lem1673314 (u : real) (v : real) (y : real) (b : real) : (term245 u v y b) = (term246 u v y b).
Proof. exact (MK_COMB (@lem1673313 u v) (@lem1673311 v y b)). Qed.
Lemma lem1673315 (u : real) (v : real) (y : real) (b : real) : (term247 u v y b) = (term245 u v y b).
Proof. exact (@lem17362 ((real_add u v) = term39) (term7 v y b)). Qed.
Lemma lem1673316 (u : real) (v : real) (y : real) (b : real) : (term247 u v y b) = (term246 u v y b).
Proof. exact (TRANS (@lem1673315 u v y b) (@lem1673314 u v y b)). Qed.
Lemma lem1673318 (v : real) : (term47 v) = (term47 v).
Proof. exact (eq_refl (term47 v)). Qed.
Lemma lem1673319 (u : real) (v : real) (y : real) (b : real) : (term248 u v y b) = (term249 u v y b).
Proof. exact (MK_COMB (@lem1673318 v) (@lem1673316 u v y b)). Qed.
Lemma lem1673320 (u : real) (v : real) (y : real) (b : real) : (term250 u v y b) = (term248 u v y b).
Proof. exact (@lem17362 (term38 v) (term251 u v y b)). Qed.
Lemma lem1673321 (u : real) (v : real) (y : real) (b : real) : (term250 u v y b) = (term249 u v y b).
Proof. exact (TRANS (@lem1673320 u v y b) (@lem1673319 u v y b)). Qed.
Lemma lem1673323 (u : real) : (term47 u) = (term47 u).
Proof. exact (eq_refl (term47 u)). Qed.
Lemma lem1673324 (u : real) (v : real) (y : real) (b : real) : (term252 u v y b) = (term253 u v y b).
Proof. exact (MK_COMB (@lem1673323 u) (@lem1673321 u v y b)). Qed.
Lemma lem1673325 (u : real) (v : real) (y : real) (b : real) : (term254 u v y b) = (term252 u v y b).
Proof. exact (@lem17362 (term38 u) (term255 u v y b)). Qed.
Lemma lem1673326 (u : real) (v : real) (y : real) (b : real) : (term254 u v y b) = (term253 u v y b).
Proof. exact (TRANS (@lem1673325 u v y b) (@lem1673324 u v y b)). Qed.
Lemma lem1673328 (y : real) (b : real) : (term56 y b) = (term56 y b).
Proof. exact (eq_refl (term56 y b)). Qed.
Lemma lem1673329 (u : real) (v : real) (y : real) (b : real) : (term256 u v y b) = (term257 u v y b).
Proof. exact (MK_COMB (@lem1673328 y b) (@lem1673326 u v y b)). Qed.
Lemma lem1673330 (u : real) (v : real) (y : real) (b : real) : (term258 u v y b) = (term256 u v y b).
Proof. exact (@lem17362 (real_le y b) (term259 u v y b)). Qed.
Lemma lem1673331 (u : real) (v : real) (y : real) (b : real) : (term258 u v y b) = (term257 u v y b).
Proof. exact (TRANS (@lem1673330 u v y b) (@lem1673329 u v y b)). Qed.
Lemma lem1673333 (x : real) (a : real) : (term56 x a) = (term56 x a).
Proof. exact (eq_refl (term56 x a)). Qed.
Lemma lem1673334 (x : real) (a : real) (u : real) (v : real) (y : real) (b : real) : (term260 x a u v y b) = (term261 x a u v y b).
Proof. exact (MK_COMB (@lem1673333 x a) (@lem1673331 u v y b)). Qed.
Lemma lem1673335 (x : real) (a : real) (u : real) (v : real) (y : real) (b : real) : (term262 x a u v y b) = (term260 x a u v y b).
Proof. exact (@lem17362 (real_le x a) (term263 u v y b)). Qed.
Lemma lem1673367 (x : real) (a : real) (u : real) (v : real) (y : real) (b : real) : (term262 x a u v y b) = (term261 x a u v y b).
Proof. exact (TRANS (@lem1673335 x a u v y b) (@lem1673334 x a u v y b)). Qed.
Lemma lem1673368 (a : real) (x : real) : (real_le x a) = (term65 a x).
Proof. exact (@lem1483523 a x). Qed.
Lemma lem1673381 (a : real) (x : real) : (real_sub a x) = (term66 a x).
Proof. exact (@lem1483519 a x). Qed.
Lemma lem1673382 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1673383 (a : real) (x : real) : (term67 a x) = (term68 a x).
Proof. exact (MK_COMB (@lem1673382) (@lem1673381 a x)). Qed.
Lemma lem1673384 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673385 (a : real) (x : real) : (term65 a x) = (term70 a x).
Proof. exact (MK_COMB (@lem1673383 a x) (@lem1673384)). Qed.
Lemma lem1673386 (a : real) (x : real) : (real_le x a) = (term70 a x).
Proof. exact (TRANS (@lem1673368 a x) (@lem1673385 a x)). Qed.
Lemma lem1673387 (b : real) (y : real) : (real_le y b) = (term65 b y).
Proof. exact (@lem1483523 b y). Qed.
Lemma lem1673400 (b : real) (y : real) : (real_sub b y) = (term66 b y).
Proof. exact (@lem1483519 b y). Qed.
Lemma lem1673401 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1673402 (b : real) (y : real) : (term67 b y) = (term68 b y).
Proof. exact (MK_COMB (@lem1673401) (@lem1673400 b y)). Qed.
Lemma lem1673403 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673404 (b : real) (y : real) : (term65 b y) = (term70 b y).
Proof. exact (MK_COMB (@lem1673402 b y) (@lem1673403)). Qed.
Lemma lem1673405 (b : real) (y : real) : (real_le y b) = (term70 b y).
Proof. exact (TRANS (@lem1673387 b y) (@lem1673404 b y)). Qed.
Lemma lem1673406 (u : real) : (term38 u) = (term71 u).
Proof. exact (@lem1483523 u term69). Qed.
Lemma lem1673412 (u : real) : (term72 u) = (term73 u).
Proof. exact (@lem1483519 u term69). Qed.
Lemma lem1673414 (x : nat) : (term74 x) = term69.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1673415 : term75 = term69.
Proof. exact (@lem1673414 term76). Qed.
Lemma lem1673416 (u : real) : (real_add u) = (real_add u).
Proof. exact (eq_refl (real_add u)). Qed.
Lemma lem1673417 (u : real) : (term73 u) = (term77 u).
Proof. exact (MK_COMB (@lem1673416 u) (@lem1673415)). Qed.
Lemma lem1673418 (u : real) : (term77 u) = u.
Proof. exact (@lem1483450 u). Qed.
Lemma lem1673419 (u : real) : (term73 u) = u.
Proof. exact (TRANS (@lem1673417 u) (@lem1673418 u)). Qed.
Lemma lem1673421 (u : real) : (term72 u) = u.
Proof. exact (TRANS (@lem1673412 u) (@lem1673419 u)). Qed.
Lemma lem1673422 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1673423 (u : real) : (term78 u) = (real_ge u).
Proof. exact (MK_COMB (@lem1673422) (@lem1673421 u)). Qed.
Lemma lem1673424 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673425 (u : real) : (term71 u) = (term79 u).
Proof. exact (MK_COMB (@lem1673423 u) (@lem1673424)). Qed.
Lemma lem1673426 (u : real) : (term38 u) = (term79 u).
Proof. exact (TRANS (@lem1673406 u) (@lem1673425 u)). Qed.
Lemma lem1673427 (v : real) : (term38 v) = (term71 v).
Proof. exact (@lem1483523 v term69). Qed.
Lemma lem1673433 (v : real) : (term72 v) = (term73 v).
Proof. exact (@lem1483519 v term69). Qed.
Lemma lem1673435 (x : nat) : (term74 x) = term69.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1673436 : term75 = term69.
Proof. exact (@lem1673435 term76). Qed.
Lemma lem1673437 (v : real) : (real_add v) = (real_add v).
Proof. exact (eq_refl (real_add v)). Qed.
Lemma lem1673438 (v : real) : (term73 v) = (term77 v).
Proof. exact (MK_COMB (@lem1673437 v) (@lem1673436)). Qed.
Lemma lem1673439 (v : real) : (term77 v) = v.
Proof. exact (@lem1483450 v). Qed.
Lemma lem1673440 (v : real) : (term73 v) = v.
Proof. exact (TRANS (@lem1673438 v) (@lem1673439 v)). Qed.
Lemma lem1673442 (v : real) : (term72 v) = v.
Proof. exact (TRANS (@lem1673433 v) (@lem1673440 v)). Qed.
Lemma lem1673443 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1673444 (v : real) : (term78 v) = (real_ge v).
Proof. exact (MK_COMB (@lem1673443) (@lem1673442 v)). Qed.
Lemma lem1673445 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673446 (v : real) : (term71 v) = (term79 v).
Proof. exact (MK_COMB (@lem1673444 v) (@lem1673445)). Qed.
Lemma lem1673447 (v : real) : (term38 v) = (term79 v).
Proof. exact (TRANS (@lem1673427 v) (@lem1673446 v)). Qed.
Lemma lem1673448 (u : real) (v : real) : ((real_add u v) = term39) = ((term80 u v) = term69).
Proof. exact (@lem1483529 (real_add u v) term39). Qed.
Lemma lem1673460 (u : real) (v : real) : (term80 u v) = (term81 u v).
Proof. exact (@lem1483519 (real_add u v) term39). Qed.
Lemma lem1673462 (m : nat) (n : nat) : (term82 m n) = (term83 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1673463 : term84 = term85.
Proof. exact (@lem1673462 term76 term76). Qed.
Lemma lem1673464 : (term86 = (BIT1 0)) = (term87 = term76).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1673465 : term87 = term76.
Proof. exact (EQ_MP (@lem1673464) (@lem940073)). Qed.
Lemma lem1673466 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1673467 : term88 = term39.
Proof. exact (MK_COMB (@lem1673466) (@lem1673465)). Qed.
Lemma lem1673468 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1673469 : term85 = term89.
Proof. exact (MK_COMB (@lem1673468) (@lem1673467)). Qed.
Lemma lem1673470 : term84 = term89.
Proof. exact (TRANS (@lem1673463) (@lem1673469)). Qed.
Lemma lem1673471 (u : real) (v : real) : (term90 u v) = (term90 u v).
Proof. exact (eq_refl (term90 u v)). Qed.
Lemma lem1673472 (u : real) (v : real) : (term81 u v) = (term91 u v).
Proof. exact (MK_COMB (@lem1673471 u v) (@lem1673470)). Qed.
Lemma lem1673477 (u : real) (v : real) : (term91 u v) = (term92 u v).
Proof. exact (@lem1483482 u v term89). Qed.
Lemma lem1673478 (u : real) (v : real) : (term81 u v) = (term92 u v).
Proof. exact (TRANS (@lem1673472 u v) (@lem1673477 u v)). Qed.
Lemma lem1673480 (u : real) (v : real) : (term80 u v) = (term92 u v).
Proof. exact (TRANS (@lem1673460 u v) (@lem1673478 u v)). Qed.
Lemma lem1673481 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1673482 (u : real) (v : real) : (term93 u v) = (term94 u v).
Proof. exact (MK_COMB (@lem1673481) (@lem1673480 u v)). Qed.
Lemma lem1673483 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673484 (u : real) (v : real) : ((term80 u v) = term69) = ((term92 u v) = term69).
Proof. exact (MK_COMB (@lem1673482 u v) (@lem1673483)). Qed.
Lemma lem1673485 (u : real) (v : real) : ((real_add u v) = term39) = ((term92 u v) = term69).
Proof. exact (TRANS (@lem1673448 u v) (@lem1673484 u v)). Qed.
Lemma lem1673486 (v : real) : (term95 v) = (term96 v).
Proof. exact (@lem1483533 term69 v). Qed.
Lemma lem1673492 (v : real) : (term97 v) = (term98 v).
Proof. exact (@lem1483519 term69 v). Qed.
Lemma lem1673497 (v : real) : (term98 v) = (term99 v).
Proof. exact (@lem1483448 (term99 v)). Qed.
Lemma lem1673499 (v : real) : (term97 v) = (term99 v).
Proof. exact (TRANS (@lem1673492 v) (@lem1673497 v)). Qed.
Lemma lem1673500 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1673501 (v : real) : (term100 v) = (term101 v).
Proof. exact (MK_COMB (@lem1673500) (@lem1673499 v)). Qed.
Lemma lem1673502 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673503 (v : real) : (term96 v) = (term102 v).
Proof. exact (MK_COMB (@lem1673501 v) (@lem1673502)). Qed.
Lemma lem1673504 (v : real) : (term95 v) = (term102 v).
Proof. exact (TRANS (@lem1673486 v) (@lem1673503 v)). Qed.
Lemma lem1673505 (y : real) (b : real) : (term103 y b) = (term104 y b).
Proof. exact (@lem1483533 y b). Qed.
Lemma lem1673511 (y : real) (b : real) : (real_sub y b) = (term66 y b).
Proof. exact (@lem1483519 y b). Qed.
Lemma lem1673516 (b : real) (y : real) : (term66 y b) = (term105 b y).
Proof. exact (@lem1483488 (term99 b) y). Qed.
Lemma lem1673518 (b : real) (y : real) : (real_sub y b) = (term105 b y).
Proof. exact (TRANS (@lem1673511 y b) (@lem1673516 b y)). Qed.
Lemma lem1673519 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1673520 (b : real) (y : real) : (term106 y b) = (term107 b y).
Proof. exact (MK_COMB (@lem1673519) (@lem1673518 b y)). Qed.
Lemma lem1673521 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673522 (b : real) (y : real) : (term104 y b) = (term108 b y).
Proof. exact (MK_COMB (@lem1673520 b y) (@lem1673521)). Qed.
Lemma lem1673523 (b : real) (y : real) : (term103 y b) = (term108 b y).
Proof. exact (TRANS (@lem1673505 y b) (@lem1673522 b y)). Qed.
Lemma lem1673524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1673525 (v : real) : (term109 v) = (term110 v).
Proof. exact (MK_COMB (@lem1673524) (@lem1673504 v)). Qed.
Lemma lem1673526 (v : real) (b : real) (y : real) : (term42 v y b) = (term111 v b y).
Proof. exact (MK_COMB (@lem1673525 v) (@lem1673523 b y)). Qed.
Lemma lem1673527 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1673528 (u : real) (v : real) : (term43 u v) = (term112 u v).
Proof. exact (MK_COMB (@lem1673527) (@lem1673485 u v)). Qed.
Lemma lem1673529 (u : real) (v : real) (b : real) (y : real) : (term246 u v y b) = (term264 u v b y).
Proof. exact (MK_COMB (@lem1673528 u v) (@lem1673526 v b y)). Qed.
Lemma lem1673530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1673531 (v : real) : (term47 v) = (term114 v).
Proof. exact (MK_COMB (@lem1673530) (@lem1673447 v)). Qed.
Lemma lem1673532 (u : real) (v : real) (b : real) (y : real) : (term249 u v y b) = (term265 u v b y).
Proof. exact (MK_COMB (@lem1673531 v) (@lem1673529 u v b y)). Qed.
Lemma lem1673533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1673534 (u : real) : (term47 u) = (term114 u).
Proof. exact (MK_COMB (@lem1673533) (@lem1673426 u)). Qed.
Lemma lem1673535 (u : real) (v : real) (b : real) (y : real) : (term253 u v y b) = (term266 u v b y).
Proof. exact (MK_COMB (@lem1673534 u) (@lem1673532 u v b y)). Qed.
Lemma lem1673536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1673537 (b : real) (y : real) : (term56 y b) = (term117 b y).
Proof. exact (MK_COMB (@lem1673536) (@lem1673405 b y)). Qed.
Lemma lem1673538 (u : real) (v : real) (b : real) (y : real) : (term257 u v y b) = (term267 u v b y).
Proof. exact (MK_COMB (@lem1673537 b y) (@lem1673535 u v b y)). Qed.
Lemma lem1673539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1673540 (a : real) (x : real) : (term56 x a) = (term117 a x).
Proof. exact (MK_COMB (@lem1673539) (@lem1673386 a x)). Qed.
Lemma lem1673541 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) : (term261 x a u v y b) = (term268 a x u v b y).
Proof. exact (MK_COMB (@lem1673540 a x) (@lem1673538 u v b y)). Qed.
Lemma lem1673548 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) : (term262 x a u v y b) = (term268 a x u v b y).
Proof. exact (TRANS (@lem1673367 x a u v y b) (@lem1673541 a x u v b y)). Qed.
Lemma lem1673565 (u : real) (v : real) (b : real) (y : real) : (term264 u v b y) = (term269 u v b y).
Proof. exact (@lem19158 (term102 v) ((term92 u v) = term69) (term108 b y)). Qed.
Lemma lem1673568 (v : real) : (term114 v) = (term114 v).
Proof. exact (eq_refl (term114 v)). Qed.
Lemma lem1673569 (u : real) (v : real) (b : real) (y : real) : (term265 u v b y) = (term270 u v b y).
Proof. exact (MK_COMB (@lem1673568 v) (@lem1673565 u v b y)). Qed.
Lemma lem1673576 (u : real) (v : real) (b : real) (y : real) : (term270 u v b y) = (term271 u v b y).
Proof. exact (@lem19158 (term272 u v) (term79 v) (term124 u v b y)). Qed.
Lemma lem1673577 (u : real) (v : real) (b : real) (y : real) : (term265 u v b y) = (term271 u v b y).
Proof. exact (TRANS (@lem1673569 u v b y) (@lem1673576 u v b y)). Qed.
Lemma lem1673580 (u : real) : (term114 u) = (term114 u).
Proof. exact (eq_refl (term114 u)). Qed.
Lemma lem1673581 (u : real) (v : real) (b : real) (y : real) : (term266 u v b y) = (term273 u v b y).
Proof. exact (MK_COMB (@lem1673580 u) (@lem1673577 u v b y)). Qed.
Lemma lem1673588 (u : real) (v : real) (b : real) (y : real) : (term273 u v b y) = (term274 u v b y).
Proof. exact (@lem19158 (term275 u v) (term79 u) (term128 u v b y)). Qed.
Lemma lem1673589 (u : real) (v : real) (b : real) (y : real) : (term266 u v b y) = (term274 u v b y).
Proof. exact (TRANS (@lem1673581 u v b y) (@lem1673588 u v b y)). Qed.
Lemma lem1673592 (b : real) (y : real) : (term117 b y) = (term117 b y).
Proof. exact (eq_refl (term117 b y)). Qed.
Lemma lem1673593 (u : real) (v : real) (b : real) (y : real) : (term267 u v b y) = (term276 u v b y).
Proof. exact (MK_COMB (@lem1673592 b y) (@lem1673589 u v b y)). Qed.
Lemma lem1673600 (u : real) (v : real) (b : real) (y : real) : (term276 u v b y) = (term277 u v b y).
Proof. exact (@lem19158 (term278 u v) (term70 b y) (term132 u v b y)). Qed.
Lemma lem1673601 (u : real) (v : real) (b : real) (y : real) : (term267 u v b y) = (term277 u v b y).
Proof. exact (TRANS (@lem1673593 u v b y) (@lem1673600 u v b y)). Qed.
Lemma lem1673604 (a : real) (x : real) : (term117 a x) = (term117 a x).
Proof. exact (eq_refl (term117 a x)). Qed.
Lemma lem1673605 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) : (term268 a x u v b y) = (term279 a x u v b y).
Proof. exact (MK_COMB (@lem1673604 a x) (@lem1673601 u v b y)). Qed.
Lemma lem1673612 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) : (term279 a x u v b y) = (term280 a x u v b y).
Proof. exact (@lem19158 (term281 b y u v) (term70 a x) (term282 u v b y)). Qed.
Lemma lem1673613 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) : (term268 a x u v b y) = (term280 a x u v b y).
Proof. exact (TRANS (@lem1673605 a x u v b y) (@lem1673612 a x u v b y)). Qed.
Lemma lem1673614 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) : (term262 x a u v y b) = (term280 a x u v b y).
Proof. exact (TRANS (@lem1673548 a x u v b y) (@lem1673613 a x u v b y)). Qed.
Lemma lem1673624 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term280 a x u v b y) : term280 a x u v b y.
Proof. exact (h1). Qed.
Lemma lem1673625 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : term283 a x b y u v.
Proof. exact (h1). Qed.
Lemma lem1673626 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : term281 b y u v.
Proof. exact (proj2 (@lem1673625 a x b y u v h1)). Qed.
Lemma lem1673628 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : term278 u v.
Proof. exact (proj2 (@lem1673626 a x b y u v h1)). Qed.
Lemma lem1673630 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : term275 u v.
Proof. exact (proj2 (@lem1673628 a x b y u v h1)). Qed.
Lemma lem1673632 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : term272 u v.
Proof. exact (proj2 (@lem1673630 a x b y u v h1)). Qed.
Lemma lem1673633 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : term79 v.
Proof. exact (proj1 (@lem1673630 a x b y u v h1)). Qed.
Lemma lem1673634 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : term102 v.
Proof. exact (proj2 (@lem1673632 a x b y u v h1)). Qed.
Lemma lem1673637 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1673638 : term139 = term140.
Proof. exact (@lem1673637 (NUMERAL 0) term76). Qed.
Lemma lem1673639 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1673640 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1673641 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1673640 h1) (fun h1 : term140 = True => @lem1673639)). Qed.
Lemma lem1673642 : term140 = True.
Proof. exact (EQ_MP (@lem1673641) (@lem1673639)). Qed.
Lemma lem1673643 : term139 = True.
Proof. exact (TRANS (@lem1673638) (@lem1673642)). Qed.
Lemma lem1673644 : True = term139.
Proof. exact (SYM (@lem1673643)). Qed.
Lemma lem1673645 : term139.
Proof. exact (EQ_MP (@lem1673644) (@lem0)). Qed.
Lemma lem1673646 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : term142 v.
Proof. exact (conj (@lem1673645) (@lem1673633 a x b y u v h1)). Qed.
Lemma lem1673648 (x : real) (y : real) : term143 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1673649 (v : real) : term144 v.
Proof. exact (@lem1673648 term39 v). Qed.
Lemma lem1673650 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : term145 v.
Proof. exact (@lem1673649 v (@lem1673646 a x b y u v h1)). Qed.
Lemma lem1673651 (v : real) : (term146 v) = v.
Proof. exact (@lem1483460 v). Qed.
Lemma lem1673652 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1673653 (v : real) : (term147 v) = (real_ge v).
Proof. exact (MK_COMB (@lem1673652) (@lem1673651 v)). Qed.
Lemma lem1673654 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673655 (v : real) : (term145 v) = (term79 v).
Proof. exact (MK_COMB (@lem1673653 v) (@lem1673654)). Qed.
Lemma lem1673656 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : term79 v.
Proof. exact (EQ_MP (@lem1673655 v) (@lem1673650 a x b y u v h1)). Qed.
Lemma lem1673658 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1673659 : term139 = term140.
Proof. exact (@lem1673658 (NUMERAL 0) term76). Qed.
Lemma lem1673660 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1673661 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1673662 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1673661 h1) (fun h1 : term140 = True => @lem1673660)). Qed.
Lemma lem1673663 : term140 = True.
Proof. exact (EQ_MP (@lem1673662) (@lem1673660)). Qed.
Lemma lem1673664 : term139 = True.
Proof. exact (TRANS (@lem1673659) (@lem1673663)). Qed.
Lemma lem1673665 : True = term139.
Proof. exact (SYM (@lem1673664)). Qed.
Lemma lem1673666 : term139.
Proof. exact (EQ_MP (@lem1673665) (@lem0)). Qed.
Lemma lem1673667 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : term189 v.
Proof. exact (conj (@lem1673666) (@lem1673634 a x b y u v h1)). Qed.
Lemma lem1673669 (x : real) (y : real) : term190 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1673670 (v : real) : term191 v.
Proof. exact (@lem1673669 term39 (term99 v)). Qed.
Lemma lem1673671 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : term192 v.
Proof. exact (@lem1673670 v (@lem1673667 a x b y u v h1)). Qed.
Lemma lem1673672 (v : real) : (term193 v) = (term99 v).
Proof. exact (@lem1483460 (term99 v)). Qed.
Lemma lem1673673 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1673674 (v : real) : (term194 v) = (term101 v).
Proof. exact (MK_COMB (@lem1673673) (@lem1673672 v)). Qed.
Lemma lem1673675 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673676 (v : real) : (term192 v) = (term102 v).
Proof. exact (MK_COMB (@lem1673674 v) (@lem1673675)). Qed.
Lemma lem1673677 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : term102 v.
Proof. exact (EQ_MP (@lem1673676 v) (@lem1673671 a x b y u v h1)). Qed.
Lemma lem1673678 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : term284 v.
Proof. exact (conj (@lem1673677 a x b y u v h1) (@lem1673656 a x b y u v h1)). Qed.
Lemma lem1673680 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1673681 (v : real) : term285 v.
Proof. exact (@lem1673680 (term99 v) v). Qed.
Lemma lem1673682 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : term286 v.
Proof. exact (@lem1673681 v (@lem1673678 a x b y u v h1)). Qed.
Lemma lem1673683 (v : real) : (term171 v) = (term172 v).
Proof. exact (@lem1483440 term89 v). Qed.
Lemma lem1673685 (m : nat) : (term173 m) = term69.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1673686 : term174 = term69.
Proof. exact (@lem1673685 term76). Qed.
Lemma lem1673687 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1673688 : term175 = term176.
Proof. exact (MK_COMB (@lem1673687) (@lem1673686)). Qed.
Lemma lem1673689 (v : real) : v = v.
Proof. exact (eq_refl v). Qed.
Lemma lem1673690 (v : real) : (term172 v) = (term177 v).
Proof. exact (MK_COMB (@lem1673688) (@lem1673689 v)). Qed.
Lemma lem1673691 (v : real) : (term171 v) = (term177 v).
Proof. exact (TRANS (@lem1673683 v) (@lem1673690 v)). Qed.
Lemma lem1673692 (v : real) : (term177 v) = term69.
Proof. exact (@lem1483446 v). Qed.
Lemma lem1673693 (v : real) : (term171 v) = term69.
Proof. exact (TRANS (@lem1673691 v) (@lem1673692 v)). Qed.
Lemma lem1673694 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1673695 (v : real) : (term287 v) = term222.
Proof. exact (MK_COMB (@lem1673694) (@lem1673693 v)). Qed.
Lemma lem1673696 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673697 (v : real) : (term286 v) = term223.
Proof. exact (MK_COMB (@lem1673695 v) (@lem1673696)). Qed.
Lemma lem1673698 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : term223.
Proof. exact (EQ_MP (@lem1673697 v) (@lem1673682 a x b y u v h1)). Qed.
Lemma lem1673700 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1673701 : term223 = term224.
Proof. exact (@lem1673700 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1673702 : term224 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1673703 : term223 = False.
Proof. exact (TRANS (@lem1673701) (@lem1673702)). Qed.
Lemma lem1673704 (a : real) (x : real) (b : real) (y : real) (u : real) (v : real) (h1 : term283 a x b y u v) : False.
Proof. exact (EQ_MP (@lem1673703) (@lem1673698 a x b y u v h1)). Qed.
Lemma lem1673705 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : term288 a x u v b y.
Proof. exact (h1). Qed.
Lemma lem1673706 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : term282 u v b y.
Proof. exact (proj2 (@lem1673705 a x u v b y h1)). Qed.
Lemma lem1673708 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : term132 u v b y.
Proof. exact (proj2 (@lem1673706 a x u v b y h1)). Qed.
Lemma lem1673709 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : term70 b y.
Proof. exact (proj1 (@lem1673706 a x u v b y h1)). Qed.
Lemma lem1673710 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : term128 u v b y.
Proof. exact (proj2 (@lem1673708 a x u v b y h1)). Qed.
Lemma lem1673712 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : term124 u v b y.
Proof. exact (proj2 (@lem1673710 a x u v b y h1)). Qed.
Lemma lem1673714 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : term108 b y.
Proof. exact (proj2 (@lem1673712 a x u v b y h1)). Qed.
Lemma lem1673717 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1673718 : term139 = term140.
Proof. exact (@lem1673717 (NUMERAL 0) term76). Qed.
Lemma lem1673719 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1673720 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1673721 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1673720 h1) (fun h1 : term140 = True => @lem1673719)). Qed.
Lemma lem1673722 : term140 = True.
Proof. exact (EQ_MP (@lem1673721) (@lem1673719)). Qed.
Lemma lem1673723 : term139 = True.
Proof. exact (TRANS (@lem1673718) (@lem1673722)). Qed.
Lemma lem1673724 : True = term139.
Proof. exact (SYM (@lem1673723)). Qed.
Lemma lem1673725 : term139.
Proof. exact (EQ_MP (@lem1673724) (@lem0)). Qed.
Lemma lem1673726 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : term226 b y.
Proof. exact (conj (@lem1673725) (@lem1673709 a x u v b y h1)). Qed.
Lemma lem1673728 (x : real) (y : real) : term143 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1673729 (b : real) (y : real) : term227 b y.
Proof. exact (@lem1673728 term39 (term66 b y)). Qed.
Lemma lem1673730 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : term228 b y.
Proof. exact (@lem1673729 b y (@lem1673726 a x u v b y h1)). Qed.
Lemma lem1673731 (b : real) (y : real) : (term229 b y) = (term66 b y).
Proof. exact (@lem1483460 (term66 b y)). Qed.
Lemma lem1673732 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1673733 (b : real) (y : real) : (term230 b y) = (term68 b y).
Proof. exact (MK_COMB (@lem1673732) (@lem1673731 b y)). Qed.
Lemma lem1673734 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673735 (b : real) (y : real) : (term228 b y) = (term70 b y).
Proof. exact (MK_COMB (@lem1673733 b y) (@lem1673734)). Qed.
Lemma lem1673736 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : term70 b y.
Proof. exact (EQ_MP (@lem1673735 b y) (@lem1673730 a x u v b y h1)). Qed.
Lemma lem1673738 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1673739 : term139 = term140.
Proof. exact (@lem1673738 (NUMERAL 0) term76). Qed.
Lemma lem1673740 : term141 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1673741 (h1 : term141 = (BIT1 0)) : term140 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1673742 : (term141 = (BIT1 0)) = (term140 = True).
Proof. exact (prop_ext (fun h1 : term141 = (BIT1 0) => @lem1673741 h1) (fun h1 : term140 = True => @lem1673740)). Qed.
Lemma lem1673743 : term140 = True.
Proof. exact (EQ_MP (@lem1673742) (@lem1673740)). Qed.
Lemma lem1673744 : term139 = True.
Proof. exact (TRANS (@lem1673739) (@lem1673743)). Qed.
Lemma lem1673745 : True = term139.
Proof. exact (SYM (@lem1673744)). Qed.
Lemma lem1673746 : term139.
Proof. exact (EQ_MP (@lem1673745) (@lem0)). Qed.
Lemma lem1673747 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : term231 b y.
Proof. exact (conj (@lem1673746) (@lem1673714 a x u v b y h1)). Qed.
Lemma lem1673749 (x : real) (y : real) : term190 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1673750 (b : real) (y : real) : term232 b y.
Proof. exact (@lem1673749 term39 (term105 b y)). Qed.
Lemma lem1673751 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : term233 b y.
Proof. exact (@lem1673750 b y (@lem1673747 a x u v b y h1)). Qed.
Lemma lem1673752 (b : real) (y : real) : (term234 b y) = (term105 b y).
Proof. exact (@lem1483460 (term105 b y)). Qed.
Lemma lem1673753 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1673754 (b : real) (y : real) : (term235 b y) = (term107 b y).
Proof. exact (MK_COMB (@lem1673753) (@lem1673752 b y)). Qed.
Lemma lem1673755 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673756 (b : real) (y : real) : (term233 b y) = (term108 b y).
Proof. exact (MK_COMB (@lem1673754 b y) (@lem1673755)). Qed.
Lemma lem1673757 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : term108 b y.
Proof. exact (EQ_MP (@lem1673756 b y) (@lem1673751 a x u v b y h1)). Qed.
Lemma lem1673758 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : term236 b y.
Proof. exact (conj (@lem1673757 a x u v b y h1) (@lem1673736 a x u v b y h1)). Qed.
Lemma lem1673760 (x : real) (y : real) : term215 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1673761 (b : real) (y : real) : term237 b y.
Proof. exact (@lem1673760 (term105 b y) (term66 b y)). Qed.
Lemma lem1673762 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : term238 b y.
Proof. exact (@lem1673761 b y (@lem1673758 a x u v b y h1)). Qed.
Lemma lem1673763 (b : real) (y : real) : (term239 b y) = (term240 b y).
Proof. exact (@lem1483480 (term99 b) b y (term99 y)). Qed.
Lemma lem1673764 (b : real) : (term171 b) = (term172 b).
Proof. exact (@lem1483440 term89 b). Qed.
Lemma lem1673766 (m : nat) : (term173 m) = term69.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1673767 : term174 = term69.
Proof. exact (@lem1673766 term76). Qed.
Lemma lem1673768 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1673769 : term175 = term176.
Proof. exact (MK_COMB (@lem1673768) (@lem1673767)). Qed.
Lemma lem1673770 (b : real) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem1673771 (b : real) : (term172 b) = (term177 b).
Proof. exact (MK_COMB (@lem1673769) (@lem1673770 b)). Qed.
Lemma lem1673772 (b : real) : (term171 b) = (term177 b).
Proof. exact (TRANS (@lem1673764 b) (@lem1673771 b)). Qed.
Lemma lem1673773 (b : real) : (term177 b) = term69.
Proof. exact (@lem1483446 b). Qed.
Lemma lem1673774 (b : real) : (term171 b) = term69.
Proof. exact (TRANS (@lem1673772 b) (@lem1673773 b)). Qed.
Lemma lem1673775 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1673776 (b : real) : (term178 b) = term179.
Proof. exact (MK_COMB (@lem1673775) (@lem1673774 b)). Qed.
Lemma lem1673777 (y : real) : (term203 y) = (term172 y).
Proof. exact (@lem1483442 term89 y). Qed.
Lemma lem1673779 (m : nat) : (term173 m) = term69.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1673780 : term174 = term69.
Proof. exact (@lem1673779 term76). Qed.
Lemma lem1673781 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1673782 : term175 = term176.
Proof. exact (MK_COMB (@lem1673781) (@lem1673780)). Qed.
Lemma lem1673783 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1673784 (y : real) : (term172 y) = (term177 y).
Proof. exact (MK_COMB (@lem1673782) (@lem1673783 y)). Qed.
Lemma lem1673785 (y : real) : (term203 y) = (term177 y).
Proof. exact (TRANS (@lem1673777 y) (@lem1673784 y)). Qed.
Lemma lem1673786 (y : real) : (term177 y) = term69.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1673787 (y : real) : (term203 y) = term69.
Proof. exact (TRANS (@lem1673785 y) (@lem1673786 y)). Qed.
Lemma lem1673788 (b : real) (y : real) : (term240 b y) = term220.
Proof. exact (MK_COMB (@lem1673776 b) (@lem1673787 y)). Qed.
Lemma lem1673789 (b : real) (y : real) : (term239 b y) = term220.
Proof. exact (TRANS (@lem1673763 b y) (@lem1673788 b y)). Qed.
Lemma lem1673790 : term220 = term69.
Proof. exact (@lem1483448 term69). Qed.
Lemma lem1673791 (b : real) (y : real) : (term239 b y) = term69.
Proof. exact (TRANS (@lem1673789 b y) (@lem1673790)). Qed.
Lemma lem1673792 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1673793 (b : real) (y : real) : (term241 b y) = term222.
Proof. exact (MK_COMB (@lem1673792) (@lem1673791 b y)). Qed.
Lemma lem1673794 : term69 = term69.
Proof. exact (eq_refl term69). Qed.
Lemma lem1673795 (b : real) (y : real) : (term238 b y) = term223.
Proof. exact (MK_COMB (@lem1673793 b y) (@lem1673794)). Qed.
Lemma lem1673796 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : term223.
Proof. exact (EQ_MP (@lem1673795 b y) (@lem1673762 a x u v b y h1)). Qed.
Lemma lem1673798 (n : nat) (m : nat) : (term138 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1673799 : term223 = term224.
Proof. exact (@lem1673798 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1673800 : term224 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1673801 : term223 = False.
Proof. exact (TRANS (@lem1673799) (@lem1673800)). Qed.
Lemma lem1673802 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term288 a x u v b y) : False.
Proof. exact (EQ_MP (@lem1673801) (@lem1673796 a x u v b y h1)). Qed.
Lemma lem1673803 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term280 a x u v b y) : False.
Proof. exact (or_elim (@lem1673624 a x u v b y h1) (fun h0 : term283 a x b y u v => @lem1673704 a x b y u v h0) (fun h0 : term288 a x u v b y => @lem1673802 a x u v b y h0)). Qed.
Lemma lem1673805 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term280 a x u v b y) : term280 a x u v b y.
Proof. exact (h1). Qed.
Lemma lem1673806 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term280 a x u v b y) : (term280 a x u v b y) = False.
Proof. exact (prop_ext (fun h2 : term280 a x u v b y => @lem1673803 a x u v b y h1) (fun h2 : False => @lem1673805 a x u v b y h1)). Qed.
Lemma lem1673807 (a : real) (x : real) (u : real) (v : real) (b : real) (y : real) (h1 : term280 a x u v b y) : False.
Proof. exact (EQ_MP (@lem1673806 a x u v b y h1) (@lem1673805 a x u v b y h1)). Qed.
Lemma lem1673808 (x : real) (a : real) (u : real) (v : real) (y : real) (b : real) (h1 : term262 x a u v y b) : term262 x a u v y b.
Proof. exact (h1). Qed.
Lemma lem1673809 (x : real) (a : real) (u : real) (v : real) (y : real) (b : real) (h1 : term262 x a u v y b) : term280 a x u v b y.
Proof. exact (EQ_MP (@lem1673614 a x u v b y) (@lem1673808 x a u v y b h1)). Qed.
Lemma lem1673810 (x : real) (a : real) (u : real) (v : real) (y : real) (b : real) (h1 : term262 x a u v y b) : (term280 a x u v b y) = False.
Proof. exact (prop_ext (fun h2 : term280 a x u v b y => @lem1673807 a x u v b y h2) (fun h2 : False => @lem1673809 x a u v y b h1)). Qed.
Lemma lem1673811 (x : real) (a : real) (u : real) (v : real) (y : real) (b : real) (h1 : term262 x a u v y b) : False.
Proof. exact (EQ_MP (@lem1673810 x a u v y b h1) (@lem1673809 x a u v y b h1)). Qed.
Lemma lem1673812 (x : real) (a : real) (u : real) (v : real) (y : real) (b : real) : term289 x a u v y b.
Proof. exact (fun h0 : term262 x a u v y b => @lem1673811 x a u v y b h0). Qed.
Lemma lem1673813 (x : real) (a : real) (u : real) (v : real) (y : real) (b : real) : term290 x a u v y b.
Proof. exact (@lem1386578 (term291 x a u v y b)). Qed.
Lemma lem1673814 (x : real) (a : real) (u : real) (v : real) (y : real) (b : real) : term291 x a u v y b.
Proof. exact (@lem1673813 x a u v y b (@lem1673812 x a u v y b)). Qed.
Lemma lem1673815 (u : real) (v : real) (y : real) (b : real) (x : real) (a : real) (h1 : real_le x a) : term263 u v y b.
Proof. exact (@lem1673814 x a u v y b (@lem1672584 x a h1)). Qed.
Lemma lem1673816 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : real_le x a) (h2 : real_le y b) : term259 u v y b.
Proof. exact (@lem1673815 u v y b x a h1 (@lem1672586 y b h2)). Qed.
Lemma lem1673817 (v : real) (x : real) (a : real) (y : real) (b : real) (u : real) (h1 : real_le x a) (h2 : real_le y b) (h3 : term38 u) : term255 u v y b.
Proof. exact (@lem1673816 u v x a y b h1 h2 (@lem1672588 u h3)). Qed.
Lemma lem1673818 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : real_le x a) (h2 : real_le y b) (h3 : term38 u) (h4 : term38 v) : term251 u v y b.
Proof. exact (@lem1673817 v x a y b u h1 h2 h3 (@lem1672590 v h4)). Qed.
Lemma lem1673819 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : (real_add u v) = term39) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) (h5 : term38 v) : term7 v y b.
Proof. exact (@lem1673818 x a y b u v h2 h3 h4 h5 (@lem1672589 u v h1)). Qed.
Lemma lem1673820 (y : real) (b : real) (v : real) (u : real) (x : real) (a : real) (h1 : real_le x a) : term64 y b v u x a.
Proof. exact (@lem1673284 y b v u x a (@lem1672584 x a h1)). Qed.
Lemma lem1673821 (v : real) (u : real) (x : real) (a : real) (y : real) (b : real) (h1 : real_le x a) (h2 : real_le y b) : term60 v u x a.
Proof. exact (@lem1673820 y b v u x a h1 (@lem1672586 y b h2)). Qed.
Lemma lem1673822 (v : real) (x : real) (a : real) (y : real) (b : real) (u : real) (h1 : real_le x a) (h2 : real_le y b) (h3 : term38 u) : term55 v u x a.
Proof. exact (@lem1673821 v u x a y b h1 h2 (@lem1672588 u h3)). Qed.
Lemma lem1673823 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : real_le x a) (h2 : real_le y b) (h3 : term38 u) (h4 : term38 v) : term51 v u x a.
Proof. exact (@lem1673822 v x a y b u h1 h2 h3 (@lem1672590 v h4)). Qed.
Lemma lem1673824 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : (real_add u v) = term39) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) (h5 : term38 v) : term7 u x a.
Proof. exact (@lem1673823 x a y b u v h2 h3 h4 h5 (@lem1672589 u v h1)). Qed.
Lemma lem1673825 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : (real_add u v) = term39) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) (h5 : term38 v) : term8 y v b.
Proof. exact (@lem1672599 y v b (@lem1673819 x a y b u v h1 h2 h3 h4 h5)). Qed.
Lemma lem1673826 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : (real_add u v) = term39) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) (h5 : term38 v) : term8 x u a.
Proof. exact (@lem1672596 x u a (@lem1673824 x a y b u v h1 h2 h3 h4 h5)). Qed.
Lemma lem1673827 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : (real_add u v) = term39) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) (h5 : term38 v) : term292 x u a y v b.
Proof. exact (conj (@lem1673826 x a y b u v h1 h2 h3 h4 h5) (@lem1673825 x a y b u v h1 h2 h3 h4 h5)). Qed.
Lemma lem1673828 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : (real_add u v) = term39) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) (h5 : term38 v) : term293 x y u a v b.
Proof. exact (@lem1672593 x y u a v b (@lem1673827 x a y b u v h1 h2 h3 h4 h5)). Qed.
Lemma lem1673829 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : term34 x a y b u v) : term35 y b u v.
Proof. exact (proj2 (@lem1672582 x a y b u v h1)). Qed.
Lemma lem1673830 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : term34 x a y b u v) : real_le x a.
Proof. exact (proj1 (@lem1672582 x a y b u v h1)). Qed.
Lemma lem1673831 (y : real) (b : real) (u : real) (v : real) (h1 : term35 y b u v) : term36 u v.
Proof. exact (proj2 (@lem1672583 y b u v h1)). Qed.
Lemma lem1673832 (y : real) (b : real) (u : real) (v : real) (h1 : term35 y b u v) : real_le y b.
Proof. exact (proj1 (@lem1672583 y b u v h1)). Qed.
Lemma lem1673833 (u : real) (v : real) (h1 : term36 u v) : term37 u v.
Proof. exact (proj2 (@lem1672585 u v h1)). Qed.
Lemma lem1673834 (u : real) (v : real) (h1 : term36 u v) : term38 u.
Proof. exact (proj1 (@lem1672585 u v h1)). Qed.
Lemma lem1673835 (u : real) (v : real) (h1 : term37 u v) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1672587 u v h1)). Qed.
Lemma lem1673836 (u : real) (v : real) (h1 : term37 u v) : term38 v.
Proof. exact (proj1 (@lem1672587 u v h1)). Qed.
Lemma lem1673837 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : (real_add u v) = term39) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) (h5 : term38 v) : ((real_add u v) = term39) = (term293 x y u a v b).
Proof. exact (prop_ext (fun h6 : (real_add u v) = term39 => @lem1673828 x a y b u v h1 h2 h3 h4 h5) (fun h6 : term293 x y u a v b => @lem1672589 u v h1)). Qed.
Lemma lem1673838 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : (real_add u v) = term39) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) (h5 : term38 v) : term293 x y u a v b.
Proof. exact (EQ_MP (@lem1673837 x a y b u v h1 h2 h3 h4 h5) (@lem1672589 u v h1)). Qed.
Lemma lem1673839 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : (real_add u v) = term39) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) (h5 : term38 v) : (term38 v) = (term293 x y u a v b).
Proof. exact (prop_ext (fun h6 : term38 v => @lem1673838 x a y b u v h1 h2 h3 h4 h5) (fun h6 : term293 x y u a v b => @lem1672590 v h5)). Qed.
Lemma lem1673840 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : (real_add u v) = term39) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) (h5 : term38 v) : term293 x y u a v b.
Proof. exact (EQ_MP (@lem1673839 x a y b u v h1 h2 h3 h4 h5) (@lem1672590 v h5)). Qed.
Lemma lem1673841 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : term37 u v) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) (h5 : term38 v) : ((real_add u v) = term39) = (term293 x y u a v b).
Proof. exact (prop_ext (fun h6 : (real_add u v) = term39 => @lem1673840 x a y b u v h6 h2 h3 h4 h5) (fun h6 : term293 x y u a v b => @lem1673835 u v h1)). Qed.
Lemma lem1673842 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : term37 u v) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) (h5 : term38 v) : term293 x y u a v b.
Proof. exact (EQ_MP (@lem1673841 x a y b u v h1 h2 h3 h4 h5) (@lem1673835 u v h1)). Qed.
Lemma lem1673843 (v : real) (x : real) (a : real) (y : real) (b : real) (u : real) (h1 : term37 u v) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) : (term38 v) = (term293 x y u a v b).
Proof. exact (prop_ext (fun h5 : term38 v => @lem1673842 x a y b u v h1 h2 h3 h4 h5) (fun h5 : term293 x y u a v b => @lem1673836 u v h1)). Qed.
Lemma lem1673844 (v : real) (x : real) (a : real) (y : real) (b : real) (u : real) (h1 : term37 u v) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) : term293 x y u a v b.
Proof. exact (EQ_MP (@lem1673843 v x a y b u h1 h2 h3 h4) (@lem1673836 u v h1)). Qed.
Lemma lem1673845 (v : real) (x : real) (a : real) (y : real) (b : real) (u : real) (h1 : term37 u v) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) : (term38 u) = (term293 x y u a v b).
Proof. exact (prop_ext (fun h5 : term38 u => @lem1673844 v x a y b u h1 h2 h3 h4) (fun h5 : term293 x y u a v b => @lem1672588 u h4)). Qed.
Lemma lem1673846 (v : real) (x : real) (a : real) (y : real) (b : real) (u : real) (h1 : term37 u v) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) : term293 x y u a v b.
Proof. exact (EQ_MP (@lem1673845 v x a y b u h1 h2 h3 h4) (@lem1672588 u h4)). Qed.
Lemma lem1673847 (v : real) (x : real) (a : real) (y : real) (b : real) (u : real) (h1 : term36 u v) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) : (term37 u v) = (term293 x y u a v b).
Proof. exact (prop_ext (fun h5 : term37 u v => @lem1673846 v x a y b u h5 h2 h3 h4) (fun h5 : term293 x y u a v b => @lem1673833 u v h1)). Qed.
Lemma lem1673848 (v : real) (x : real) (a : real) (y : real) (b : real) (u : real) (h1 : term36 u v) (h2 : real_le x a) (h3 : real_le y b) (h4 : term38 u) : term293 x y u a v b.
Proof. exact (EQ_MP (@lem1673847 v x a y b u h1 h2 h3 h4) (@lem1673833 u v h1)). Qed.
Lemma lem1673849 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term36 u v) (h2 : real_le x a) (h3 : real_le y b) : (term38 u) = (term293 x y u a v b).
Proof. exact (prop_ext (fun h4 : term38 u => @lem1673848 v x a y b u h1 h2 h3 h4) (fun h4 : term293 x y u a v b => @lem1673834 u v h1)). Qed.
Lemma lem1673850 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term36 u v) (h2 : real_le x a) (h3 : real_le y b) : term293 x y u a v b.
Proof. exact (EQ_MP (@lem1673849 u v x a y b h1 h2 h3) (@lem1673834 u v h1)). Qed.
Lemma lem1673851 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term36 u v) (h2 : real_le x a) (h3 : real_le y b) : (real_le y b) = (term293 x y u a v b).
Proof. exact (prop_ext (fun h4 : real_le y b => @lem1673850 u v x a y b h1 h2 h3) (fun h4 : term293 x y u a v b => @lem1672586 y b h3)). Qed.
Lemma lem1673852 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term36 u v) (h2 : real_le x a) (h3 : real_le y b) : term293 x y u a v b.
Proof. exact (EQ_MP (@lem1673851 u v x a y b h1 h2 h3) (@lem1672586 y b h3)). Qed.
Lemma lem1673853 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term35 y b u v) (h2 : real_le x a) (h3 : real_le y b) : (term36 u v) = (term293 x y u a v b).
Proof. exact (prop_ext (fun h4 : term36 u v => @lem1673852 u v x a y b h4 h2 h3) (fun h4 : term293 x y u a v b => @lem1673831 y b u v h1)). Qed.
Lemma lem1673854 (u : real) (v : real) (x : real) (a : real) (y : real) (b : real) (h1 : term35 y b u v) (h2 : real_le x a) (h3 : real_le y b) : term293 x y u a v b.
Proof. exact (EQ_MP (@lem1673853 u v x a y b h1 h2 h3) (@lem1673831 y b u v h1)). Qed.
Lemma lem1673855 (y : real) (b : real) (u : real) (v : real) (x : real) (a : real) (h1 : term35 y b u v) (h2 : real_le x a) : (real_le y b) = (term293 x y u a v b).
Proof. exact (prop_ext (fun h3 : real_le y b => @lem1673854 u v x a y b h1 h2 h3) (fun h3 : term293 x y u a v b => @lem1673832 y b u v h1)). Qed.
Lemma lem1673856 (y : real) (b : real) (u : real) (v : real) (x : real) (a : real) (h1 : term35 y b u v) (h2 : real_le x a) : term293 x y u a v b.
Proof. exact (EQ_MP (@lem1673855 y b u v x a h1 h2) (@lem1673832 y b u v h1)). Qed.
Lemma lem1673857 (y : real) (b : real) (u : real) (v : real) (x : real) (a : real) (h1 : term35 y b u v) (h2 : real_le x a) : (real_le x a) = (term293 x y u a v b).
Proof. exact (prop_ext (fun h3 : real_le x a => @lem1673856 y b u v x a h1 h2) (fun h3 : term293 x y u a v b => @lem1672584 x a h2)). Qed.
Lemma lem1673858 (y : real) (b : real) (u : real) (v : real) (x : real) (a : real) (h1 : term35 y b u v) (h2 : real_le x a) : term293 x y u a v b.
Proof. exact (EQ_MP (@lem1673857 y b u v x a h1 h2) (@lem1672584 x a h2)). Qed.
Lemma lem1673859 (y : real) (b : real) (u : real) (v : real) (x : real) (a : real) (h1 : term34 x a y b u v) (h2 : real_le x a) : (term35 y b u v) = (term293 x y u a v b).
Proof. exact (prop_ext (fun h3 : term35 y b u v => @lem1673858 y b u v x a h3 h2) (fun h3 : term293 x y u a v b => @lem1673829 x a y b u v h1)). Qed.
Lemma lem1673860 (y : real) (b : real) (u : real) (v : real) (x : real) (a : real) (h1 : term34 x a y b u v) (h2 : real_le x a) : term293 x y u a v b.
Proof. exact (EQ_MP (@lem1673859 y b u v x a h1 h2) (@lem1673829 x a y b u v h1)). Qed.
Lemma lem1673861 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : term34 x a y b u v) : (real_le x a) = (term293 x y u a v b).
Proof. exact (prop_ext (fun h2 : real_le x a => @lem1673860 y b u v x a h1 h2) (fun h2 : term293 x y u a v b => @lem1673830 x a y b u v h1)). Qed.
Lemma lem1673862 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) (h1 : term34 x a y b u v) : term293 x y u a v b.
Proof. exact (EQ_MP (@lem1673861 x a y b u v h1) (@lem1673830 x a y b u v h1)). Qed.
Lemma lem1673863 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : term294 x y u a v b.
Proof. exact (fun h0 : term34 x a y b u v => @lem1673862 x a y b u v h0). Qed.
Lemma lem1673868 (x : real) (y : real) (u : real) (a : real) (b : real) : term295 x y u a b.
Proof. exact (fun v : real => @lem1673863 x y u a v b). Qed.
Lemma lem1673873 (x : real) (y : real) (a : real) (b : real) : term296 x y a b.
Proof. exact (fun u : real => @lem1673868 x y u a b). Qed.
Lemma lem1673878 (x : real) (y : real) (b : real) : term297 x y b.
Proof. exact (fun a : real => @lem1673873 x y a b). Qed.
Lemma lem1673883 (x : real) (b : real) : term298 x b.
Proof. exact (fun y : real => @lem1673878 x y b). Qed.
Lemma lem1673888 (b : real) : term299 b.
Proof. exact (fun x : real => @lem1673883 x b). Qed.
