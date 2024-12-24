Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_INF_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_INF_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import REAL_NOT_LE_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1367765_spec.
Require Import thm1367771_spec.
Require Import thm1386578_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19158_spec.
Require Import thm19490_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981223_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982711_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982725_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1982796_spec.
Require Import thm1982797_spec.
Require Import thm1988285_spec.
Require Import thm1988287_spec.
Require Import thm1988295_spec.
Require Import thm1988332_spec.
Require Import thm1988348_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm940532_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem5319393 (x : real) : term0 x.
Proof. exact (@lem1495933 x). Qed.
Lemma lem5319394 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem5319395 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem5319394 x) (@lem5319393 x)). Qed.
Lemma lem5319396 (x : real) (y : real) : term2 x y.
Proof. exact (@lem5319395 x y). Qed.
Lemma lem5319397 (y : real) (x : real) : (term2 x y) = ((term3 x y) = (real_lt y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem5319399 (s : real -> Prop) : term4 s.
Proof. exact (@lem5315196 s). Qed.
Lemma lem5319400 (s : real -> Prop) : (term4 s) = (term5 s).
Proof. exact (eq_refl (term4 s)). Qed.
Lemma lem5319401 (s : real -> Prop) : term5 s.
Proof. exact (EQ_MP (@lem5319400 s) (@lem5319399 s)). Qed.
Lemma lem5319402 (s : real -> Prop) (l : real) : term6 s l.
Proof. exact (@lem5319401 s l). Qed.
Lemma lem5319403 (l : real) (s : real -> Prop) : (term6 s l) = ((has_inf s l) = (term7 l s)).
Proof. exact (eq_refl (term6 s l)). Qed.
Lemma lem5319405 (s : real -> Prop) : term4 s.
Proof. exact (@lem5315196 s). Qed.
Lemma lem5319406 (s : real -> Prop) : (term4 s) = (term5 s).
Proof. exact (eq_refl (term4 s)). Qed.
Lemma lem5319407 (s : real -> Prop) : term5 s.
Proof. exact (EQ_MP (@lem5319406 s) (@lem5319405 s)). Qed.
Lemma lem5319408 (s : real -> Prop) (l : real) : term6 s l.
Proof. exact (@lem5319407 s l). Qed.
Lemma lem5319409 (l : real) (s : real -> Prop) : (term6 s l) = ((has_inf s l) = (term7 l s)).
Proof. exact (eq_refl (term6 s l)). Qed.
Lemma lem5319419 (l : real) (m : real) (t : real -> Prop) (s : real -> Prop) (h1 : term8 l m t s) : term8 l m t s.
Proof. exact (h1). Qed.
Lemma lem5319420 (m : real) (t : real -> Prop) (s : real -> Prop) (h1 : term9 m t s) : term9 m t s.
Proof. exact (h1). Qed.
Lemma lem5319421 (s : real -> Prop) (l : real) (h1 : has_inf s l) : has_inf s l.
Proof. exact (h1). Qed.
Lemma lem5319422 (t : real -> Prop) (s : real -> Prop) (h1 : term10 t s) : term10 t s.
Proof. exact (h1). Qed.
Lemma lem5319423 (t : real -> Prop) (m : real) (h1 : has_inf t m) : has_inf t m.
Proof. exact (h1). Qed.
Lemma lem5319425 (l : real) (s : real -> Prop) : (has_inf s l) = (term7 l s).
Proof. exact (EQ_MP (@lem5319409 l s) (@lem5319408 s l)). Qed.
Lemma lem5319450 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term7 l s.
Proof. exact (EQ_MP (@lem5319425 l s) (@lem5319421 s l h1)). Qed.
Lemma lem5319451 (l : real) (s : real -> Prop) (h1 : term11 l s) : term11 l s.
Proof. exact (h1). Qed.
Lemma lem5319452 (s : real -> Prop) (h1 : term12 s) : term12 s.
Proof. exact (h1). Qed.
Lemma lem5319454 (s : real -> Prop) (l : real) (h1 : term13 s l) : term13 s l.
Proof. exact (h1). Qed.
Lemma lem5319456 (l : real) (s : real -> Prop) : (has_inf s l) = (term7 l s).
Proof. exact (EQ_MP (@lem5319403 l s) (@lem5319402 s l)). Qed.
Lemma lem5319457 (m : real) (t : real -> Prop) : (has_inf t m) = (term7 m t).
Proof. exact (@lem5319456 m t). Qed.
Lemma lem5319482 (t : real -> Prop) (m : real) (h1 : has_inf t m) : term7 m t.
Proof. exact (EQ_MP (@lem5319457 m t) (@lem5319423 t m h1)). Qed.
Lemma lem5319483 (m : real) (t : real -> Prop) (h1 : term11 m t) : term11 m t.
Proof. exact (h1). Qed.
Lemma lem5319484 (t : real -> Prop) (h1 : term12 t) : term12 t.
Proof. exact (h1). Qed.
Lemma lem5319485 (m : real) (t : real -> Prop) (h1 : term14 m t) : term14 m t.
Proof. exact (h1). Qed.
Lemma lem5319488 (p : Prop) : p = (term15 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5319489 (l : real) (m : real) : (real_le l m) = (term16 l m).
Proof. exact (@lem5319488 (real_le l m)). Qed.
Lemma lem5319490 (l : real) (m : real) : (term16 l m) = (real_le l m).
Proof. exact (SYM (@lem5319489 l m)). Qed.
Lemma lem5319491 (l : real) (m : real) (h1 : term3 l m) : term3 l m.
Proof. exact (h1). Qed.
Lemma lem5319493 (y : real) (x : real) : (term3 x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem5319397 y x) (@lem5319396 x y)). Qed.
Lemma lem5319494 (m : real) (l : real) : (term3 l m) = (real_lt m l).
Proof. exact (@lem5319493 m l). Qed.
Lemma lem5319495 (l : real) (m : real) (h1 : term3 l m) : real_lt m l.
Proof. exact (EQ_MP (@lem5319494 m l) (@lem5319491 l m h1)). Qed.
Lemma lem5319496 (m : real) (l : real) (h1 : term17 m l) : term17 m l.
Proof. exact (h1). Qed.
Lemma lem5319497 (m : real) (c : real) (l : real) (h1 : term18 m c l) : term18 m c l.
Proof. exact (h1). Qed.
Lemma lem5319498 (c : real) (l : real) (h1 : real_lt c l) : real_lt c l.
Proof. exact (h1). Qed.
Lemma lem5319499 (m : real) (c : real) (h1 : real_lt m c) : real_lt m c.
Proof. exact (h1). Qed.
Lemma lem5319521 (m : real) (l : real) : (term19 m l) = (term20 m l).
Proof. exact (@lem17045 (term21 l m) (term22 m l)). Qed.
Lemma lem5319523 (m : real) (l : real) : (term23 m l) = (term23 m l).
Proof. exact (eq_refl (term23 m l)). Qed.
Lemma lem5319524 (m : real) (l : real) : (term24 m l) = (term25 m l).
Proof. exact (MK_COMB (@lem5319523 m l) (@lem5319521 m l)). Qed.
Lemma lem5319525 (m : real) (l : real) : (term26 m l) = (term24 m l).
Proof. exact (@lem17362 (real_lt m l) (term27 m l)). Qed.
Lemma lem5319526 (m : real) (l : real) : (term26 m l) = (term25 m l).
Proof. exact (TRANS (@lem5319525 m l) (@lem5319524 m l)). Qed.
Lemma lem5319528 (t : real -> Prop) : (term28 t) = (term28 t).
Proof. exact (eq_refl (term28 t)). Qed.
Lemma lem5319529 (t : real -> Prop) (m : real) (l : real) : (term29 t m l) = (term30 t m l).
Proof. exact (MK_COMB (@lem5319528 t) (@lem5319526 m l)). Qed.
Lemma lem5319530 (t : real -> Prop) (m : real) (l : real) : (term31 t m l) = (term29 t m l).
Proof. exact (@lem17362 (term12 t) (term32 m l)). Qed.
Lemma lem5319531 (t : real -> Prop) (m : real) (l : real) : (term31 t m l) = (term30 t m l).
Proof. exact (TRANS (@lem5319530 t m l) (@lem5319529 t m l)). Qed.
Lemma lem5319533 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5319534 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) : (term33 s t m l) = (term34 s t m l).
Proof. exact (MK_COMB (@lem5319533 s) (@lem5319531 t m l)). Qed.
Lemma lem5319535 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) : (term35 s t m l) = (term33 s t m l).
Proof. exact (@lem17362 (term12 s) (term36 t m l)). Qed.
Lemma lem5319563 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) : (term35 s t m l) = (term34 s t m l).
Proof. exact (TRANS (@lem5319535 s t m l) (@lem5319534 s t m l)). Qed.
Lemma lem5319566 (l : real) (m : real) : (real_lt m l) = (term37 l m).
Proof. exact (@lem1988285 l m). Qed.
Lemma lem5319579 (l : real) (m : real) : (real_sub l m) = (term38 l m).
Proof. exact (@lem1982792 l m). Qed.
Lemma lem5319580 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5319581 (l : real) (m : real) : (term39 l m) = (term40 l m).
Proof. exact (MK_COMB (@lem5319580) (@lem5319579 l m)). Qed.
Lemma lem5319582 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5319583 (l : real) (m : real) : (term37 l m) = (term42 l m).
Proof. exact (MK_COMB (@lem5319581 l m) (@lem5319582)). Qed.
Lemma lem5319584 (l : real) (m : real) : (real_lt m l) = (term42 l m).
Proof. exact (TRANS (@lem5319566 l m) (@lem5319583 l m)). Qed.
Lemma lem5319585 (l : real) (m : real) : (term43 l m) = (term44 l m).
Proof. exact (@lem1988295 m (term45 l m)). Qed.
Lemma lem5319587 (x : real) (y : real) : (real_div x y) = (term46 x y).
Proof. exact (EQ_MP (@lem1982797 x y) (@lem1982796 x y)). Qed.
Lemma lem5319588 (l : real) (m : real) : (term45 l m) = (term47 l m).
Proof. exact (@lem5319587 (real_add l m) term48). Qed.
Lemma lem5319593 (n : nat) : (term49 n) = (term50 n).
Proof. exact (proj1 (@lem1981223 n (@el nat))). Qed.
Lemma lem5319595 : term51 = term52.
Proof. exact (@lem5319593 term53). Qed.
Lemma lem5319604 (l : real) (m : real) : (term54 l m) = (term54 l m).
Proof. exact (eq_refl (term54 l m)). Qed.
Lemma lem5319605 (l : real) (m : real) : (term47 l m) = (term55 l m).
Proof. exact (MK_COMB (@lem5319604 l m) (@lem5319595)). Qed.
Lemma lem5319606 (l : real) (m : real) : (term55 l m) = (term56 l m).
Proof. exact (@lem1982725 term52 (real_add l m)). Qed.
Lemma lem5319613 (l : real) (m : real) : (term56 l m) = (term57 l m).
Proof. exact (@lem1982781 l term52 m). Qed.
Lemma lem5319614 (l : real) (m : real) : (term55 l m) = (term57 l m).
Proof. exact (TRANS (@lem5319606 l m) (@lem5319613 l m)). Qed.
Lemma lem5319615 (l : real) (m : real) : (term47 l m) = (term57 l m).
Proof. exact (TRANS (@lem5319605 l m) (@lem5319614 l m)). Qed.
Lemma lem5319616 (l : real) (m : real) : (term45 l m) = (term57 l m).
Proof. exact (TRANS (@lem5319588 l m) (@lem5319615 l m)). Qed.
Lemma lem5319619 (m : real) : (real_sub m) = (real_sub m).
Proof. exact (eq_refl (real_sub m)). Qed.
Lemma lem5319620 (l : real) (m : real) : (term58 l m) = (term59 l m).
Proof. exact (MK_COMB (@lem5319619 m) (@lem5319616 l m)). Qed.
Lemma lem5319621 (l : real) (m : real) : (term59 l m) = (term60 l m).
Proof. exact (@lem1982792 m (term57 l m)). Qed.
Lemma lem5319622 (l : real) (m : real) : (term61 l m) = (term62 l m).
Proof. exact (@lem1982781 (term63 l) term64 (term63 m)). Qed.
Lemma lem5319623 (m : real) : (term65 m) = (term66 m).
Proof. exact (@lem1982749 term64 term52 m). Qed.
Lemma lem5319624 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem5319626 (x : nat) : (term67 x) = (term68 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5319627 : term64 = term69.
Proof. exact (@lem5319626 term70). Qed.
Lemma lem5319628 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5319629 : term71 = term72.
Proof. exact (MK_COMB (@lem5319628) (@lem5319627)). Qed.
Lemma lem5319630 : term73 = term74.
Proof. exact (MK_COMB (@lem5319629) (@lem5319624)). Qed.
Lemma lem5319631 : term74 = term75.
Proof. exact (@lem1981613 term64 term76 term76 term48). Qed.
Lemma lem5319633 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5319634 : term79 = term80.
Proof. exact (@lem5319633 term70 term53). Qed.
Lemma lem5319635 : term81 = term82.
Proof. exact (@lem996238 term82). Qed.
Lemma lem5319636 : (term81 = term82) = (term83 = term53).
Proof. exact (@lem1007663 (BIT1 0) term82 term82). Qed.
Lemma lem5319637 : term83 = term53.
Proof. exact (EQ_MP (@lem5319636) (@lem5319635)). Qed.
Lemma lem5319638 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319639 : term80 = term48.
Proof. exact (MK_COMB (@lem5319638) (@lem5319637)). Qed.
Lemma lem5319640 : term79 = term48.
Proof. exact (TRANS (@lem5319634) (@lem5319639)). Qed.
Lemma lem5319642 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5319643 : term86 = term87.
Proof. exact (@lem5319642 term70 term70). Qed.
Lemma lem5319644 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5319645 : term89 = term70.
Proof. exact (EQ_MP (@lem5319644) (@lem940073)). Qed.
Lemma lem5319646 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319647 : term90 = term76.
Proof. exact (MK_COMB (@lem5319646) (@lem5319645)). Qed.
Lemma lem5319648 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5319649 : term87 = term64.
Proof. exact (MK_COMB (@lem5319648) (@lem5319647)). Qed.
Lemma lem5319650 : term86 = term64.
Proof. exact (TRANS (@lem5319643) (@lem5319649)). Qed.
Lemma lem5319651 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5319652 : term91 = term92.
Proof. exact (MK_COMB (@lem5319651) (@lem5319650)). Qed.
Lemma lem5319653 : term75 = term93.
Proof. exact (MK_COMB (@lem5319652) (@lem5319640)). Qed.
Lemma lem5319654 : term74 = term93.
Proof. exact (TRANS (@lem5319631) (@lem5319653)). Qed.
Lemma lem5319657 : term73 = term93.
Proof. exact (TRANS (@lem5319630) (@lem5319654)). Qed.
Lemma lem5319658 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5319659 : term94 = term95.
Proof. exact (MK_COMB (@lem5319658) (@lem5319657)). Qed.
Lemma lem5319660 (m : real) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem5319661 (m : real) : (term66 m) = (term96 m).
Proof. exact (MK_COMB (@lem5319659) (@lem5319660 m)). Qed.
Lemma lem5319662 (m : real) : (term65 m) = (term96 m).
Proof. exact (TRANS (@lem5319623 m) (@lem5319661 m)). Qed.
Lemma lem5319663 (l : real) : (term65 l) = (term66 l).
Proof. exact (@lem1982749 term64 term52 l). Qed.
Lemma lem5319664 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem5319666 (x : nat) : (term67 x) = (term68 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5319667 : term64 = term69.
Proof. exact (@lem5319666 term70). Qed.
Lemma lem5319668 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5319669 : term71 = term72.
Proof. exact (MK_COMB (@lem5319668) (@lem5319667)). Qed.
Lemma lem5319670 : term73 = term74.
Proof. exact (MK_COMB (@lem5319669) (@lem5319664)). Qed.
Lemma lem5319671 : term74 = term75.
Proof. exact (@lem1981613 term64 term76 term76 term48). Qed.
Lemma lem5319673 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5319674 : term79 = term80.
Proof. exact (@lem5319673 term70 term53). Qed.
Lemma lem5319675 : term81 = term82.
Proof. exact (@lem996238 term82). Qed.
Lemma lem5319676 : (term81 = term82) = (term83 = term53).
Proof. exact (@lem1007663 (BIT1 0) term82 term82). Qed.
Lemma lem5319677 : term83 = term53.
Proof. exact (EQ_MP (@lem5319676) (@lem5319675)). Qed.
Lemma lem5319678 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319679 : term80 = term48.
Proof. exact (MK_COMB (@lem5319678) (@lem5319677)). Qed.
Lemma lem5319680 : term79 = term48.
Proof. exact (TRANS (@lem5319674) (@lem5319679)). Qed.
Lemma lem5319682 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5319683 : term86 = term87.
Proof. exact (@lem5319682 term70 term70). Qed.
Lemma lem5319684 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5319685 : term89 = term70.
Proof. exact (EQ_MP (@lem5319684) (@lem940073)). Qed.
Lemma lem5319686 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319687 : term90 = term76.
Proof. exact (MK_COMB (@lem5319686) (@lem5319685)). Qed.
Lemma lem5319688 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5319689 : term87 = term64.
Proof. exact (MK_COMB (@lem5319688) (@lem5319687)). Qed.
Lemma lem5319690 : term86 = term64.
Proof. exact (TRANS (@lem5319683) (@lem5319689)). Qed.
Lemma lem5319691 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5319692 : term91 = term92.
Proof. exact (MK_COMB (@lem5319691) (@lem5319690)). Qed.
Lemma lem5319693 : term75 = term93.
Proof. exact (MK_COMB (@lem5319692) (@lem5319680)). Qed.
Lemma lem5319694 : term74 = term93.
Proof. exact (TRANS (@lem5319671) (@lem5319693)). Qed.
Lemma lem5319697 : term73 = term93.
Proof. exact (TRANS (@lem5319670) (@lem5319694)). Qed.
Lemma lem5319698 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5319699 : term94 = term95.
Proof. exact (MK_COMB (@lem5319698) (@lem5319697)). Qed.
Lemma lem5319700 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5319701 (l : real) : (term66 l) = (term96 l).
Proof. exact (MK_COMB (@lem5319699) (@lem5319700 l)). Qed.
Lemma lem5319702 (l : real) : (term65 l) = (term96 l).
Proof. exact (TRANS (@lem5319663 l) (@lem5319701 l)). Qed.
Lemma lem5319703 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5319704 (l : real) : (term97 l) = (term98 l).
Proof. exact (MK_COMB (@lem5319703) (@lem5319702 l)). Qed.
Lemma lem5319705 (l : real) (m : real) : (term62 l m) = (term99 l m).
Proof. exact (MK_COMB (@lem5319704 l) (@lem5319662 m)). Qed.
Lemma lem5319706 (l : real) (m : real) : (term61 l m) = (term99 l m).
Proof. exact (TRANS (@lem5319622 l m) (@lem5319705 l m)). Qed.
Lemma lem5319707 (m : real) : (real_add m) = (real_add m).
Proof. exact (eq_refl (real_add m)). Qed.
Lemma lem5319708 (l : real) (m : real) : (term60 l m) = (term100 l m).
Proof. exact (MK_COMB (@lem5319707 m) (@lem5319706 l m)). Qed.
Lemma lem5319709 (l : real) (m : real) : (term100 l m) = (term101 l m).
Proof. exact (@lem1982757 (term96 l) m (term96 m)). Qed.
Lemma lem5319710 (m : real) : (term102 m) = (term103 m).
Proof. exact (@lem1982715 term93 m). Qed.
Lemma lem5319712 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5319713 : term76 = term105.
Proof. exact (@lem5319712 term70). Qed.
Lemma lem5319716 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem5319717 : term107 = term108.
Proof. exact (MK_COMB (@lem5319716) (@lem5319713)). Qed.
Lemma lem5319718 : term109.
Proof. exact (@lem1981473 term64 term48 term76 term76 term76 term48). Qed.
Lemma lem5319720 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5319721 : term111 = term112.
Proof. exact (@lem5319720 (NUMERAL 0) term53). Qed.
Lemma lem5319722 : term113 = term82.
Proof. exact (@lem912803). Qed.
Lemma lem5319723 (h1 : term113 = term82) : term112 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term82 h1). Qed.
Lemma lem5319724 : (term113 = term82) = (term112 = True).
Proof. exact (prop_ext (fun h1 : term113 = term82 => @lem5319723 h1) (fun h1 : term112 = True => @lem5319722)). Qed.
Lemma lem5319725 : term112 = True.
Proof. exact (EQ_MP (@lem5319724) (@lem5319722)). Qed.
Lemma lem5319726 : term111 = True.
Proof. exact (TRANS (@lem5319721) (@lem5319725)). Qed.
Lemma lem5319727 : True = term111.
Proof. exact (SYM (@lem5319726)). Qed.
Lemma lem5319728 : term111.
Proof. exact (EQ_MP (@lem5319727) (@lem0)). Qed.
Lemma lem5319729 : term114.
Proof. exact (@lem5319718 (@lem5319728)). Qed.
Lemma lem5319731 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5319732 : term115 = term116.
Proof. exact (@lem5319731 (NUMERAL 0) term70). Qed.
Lemma lem5319733 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5319734 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5319735 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5319734 h1) (fun h1 : term116 = True => @lem5319733)). Qed.
Lemma lem5319736 : term116 = True.
Proof. exact (EQ_MP (@lem5319735) (@lem5319733)). Qed.
Lemma lem5319737 : term115 = True.
Proof. exact (TRANS (@lem5319732) (@lem5319736)). Qed.
Lemma lem5319738 : True = term115.
Proof. exact (SYM (@lem5319737)). Qed.
Lemma lem5319739 : term115.
Proof. exact (EQ_MP (@lem5319738) (@lem0)). Qed.
Lemma lem5319740 : term118.
Proof. exact (@lem5319729 (@lem5319739)). Qed.
Lemma lem5319742 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5319743 : term111 = term112.
Proof. exact (@lem5319742 (NUMERAL 0) term53). Qed.
Lemma lem5319744 : term113 = term82.
Proof. exact (@lem912803). Qed.
Lemma lem5319745 (h1 : term113 = term82) : term112 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term82 h1). Qed.
Lemma lem5319746 : (term113 = term82) = (term112 = True).
Proof. exact (prop_ext (fun h1 : term113 = term82 => @lem5319745 h1) (fun h1 : term112 = True => @lem5319744)). Qed.
Lemma lem5319747 : term112 = True.
Proof. exact (EQ_MP (@lem5319746) (@lem5319744)). Qed.
Lemma lem5319748 : term111 = True.
Proof. exact (TRANS (@lem5319743) (@lem5319747)). Qed.
Lemma lem5319749 : True = term111.
Proof. exact (SYM (@lem5319748)). Qed.
Lemma lem5319750 : term111.
Proof. exact (EQ_MP (@lem5319749) (@lem0)). Qed.
Lemma lem5319751 : term119.
Proof. exact (@lem5319740 (@lem5319750)). Qed.
Lemma lem5319753 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5319754 : term79 = term80.
Proof. exact (@lem5319753 term70 term53). Qed.
Lemma lem5319755 : term81 = term82.
Proof. exact (@lem996238 term82). Qed.
Lemma lem5319756 : (term81 = term82) = (term83 = term53).
Proof. exact (@lem1007663 (BIT1 0) term82 term82). Qed.
Lemma lem5319757 : term83 = term53.
Proof. exact (EQ_MP (@lem5319756) (@lem5319755)). Qed.
Lemma lem5319758 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319759 : term80 = term48.
Proof. exact (MK_COMB (@lem5319758) (@lem5319757)). Qed.
Lemma lem5319760 : term79 = term48.
Proof. exact (TRANS (@lem5319754) (@lem5319759)). Qed.
Lemma lem5319762 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5319763 : term86 = term87.
Proof. exact (@lem5319762 term70 term70). Qed.
Lemma lem5319764 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5319765 : term89 = term70.
Proof. exact (EQ_MP (@lem5319764) (@lem940073)). Qed.
Lemma lem5319766 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319767 : term90 = term76.
Proof. exact (MK_COMB (@lem5319766) (@lem5319765)). Qed.
Lemma lem5319768 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5319769 : term87 = term64.
Proof. exact (MK_COMB (@lem5319768) (@lem5319767)). Qed.
Lemma lem5319770 : term86 = term64.
Proof. exact (TRANS (@lem5319763) (@lem5319769)). Qed.
Lemma lem5319771 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5319772 : term120 = term121.
Proof. exact (MK_COMB (@lem5319771) (@lem5319770)). Qed.
Lemma lem5319773 : term122 = term123.
Proof. exact (MK_COMB (@lem5319772) (@lem5319760)). Qed.
Lemma lem5319776 : term124 = term76.
Proof. exact (@lem1367765 term70 term70). Qed.
Lemma lem5319777 : term125 = term82.
Proof. exact (@lem706885). Qed.
Lemma lem5319778 : (term125 = term82) = (term126 = term53).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term82). Qed.
Lemma lem5319779 : term126 = term53.
Proof. exact (EQ_MP (@lem5319778) (@lem5319777)). Qed.
Lemma lem5319780 : term53 = term126.
Proof. exact (SYM (@lem5319779)). Qed.
Lemma lem5319781 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319782 : term48 = term127.
Proof. exact (MK_COMB (@lem5319781) (@lem5319780)). Qed.
Lemma lem5319783 : term121 = term121.
Proof. exact (eq_refl term121). Qed.
Lemma lem5319784 : term123 = term124.
Proof. exact (MK_COMB (@lem5319783) (@lem5319782)). Qed.
Lemma lem5319785 : term123 = term76.
Proof. exact (TRANS (@lem5319784) (@lem5319776)). Qed.
Lemma lem5319786 : term122 = term76.
Proof. exact (TRANS (@lem5319773) (@lem5319785)). Qed.
Lemma lem5319787 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5319788 : term128 = term129.
Proof. exact (MK_COMB (@lem5319787) (@lem5319786)). Qed.
Lemma lem5319789 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem5319790 : term130 = term79.
Proof. exact (MK_COMB (@lem5319788) (@lem5319789)). Qed.
Lemma lem5319792 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5319793 : term79 = term80.
Proof. exact (@lem5319792 term70 term53). Qed.
Lemma lem5319794 : term81 = term82.
Proof. exact (@lem996238 term82). Qed.
Lemma lem5319795 : (term81 = term82) = (term83 = term53).
Proof. exact (@lem1007663 (BIT1 0) term82 term82). Qed.
Lemma lem5319796 : term83 = term53.
Proof. exact (EQ_MP (@lem5319795) (@lem5319794)). Qed.
Lemma lem5319797 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319798 : term80 = term48.
Proof. exact (MK_COMB (@lem5319797) (@lem5319796)). Qed.
Lemma lem5319799 : term79 = term48.
Proof. exact (TRANS (@lem5319793) (@lem5319798)). Qed.
Lemma lem5319800 : term130 = term48.
Proof. exact (TRANS (@lem5319790) (@lem5319799)). Qed.
Lemma lem5319802 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5319803 : term131 = term132.
Proof. exact (@lem5319802 term53 term70). Qed.
Lemma lem5319804 : term133 = term82.
Proof. exact (@lem996237 term82). Qed.
Lemma lem5319805 : (term133 = term82) = (term134 = term53).
Proof. exact (@lem1007663 term82 (BIT1 0) term82). Qed.
Lemma lem5319806 : term134 = term53.
Proof. exact (EQ_MP (@lem5319805) (@lem5319804)). Qed.
Lemma lem5319807 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319808 : term132 = term48.
Proof. exact (MK_COMB (@lem5319807) (@lem5319806)). Qed.
Lemma lem5319809 : term131 = term48.
Proof. exact (TRANS (@lem5319803) (@lem5319808)). Qed.
Lemma lem5319810 : term129 = term129.
Proof. exact (eq_refl term129). Qed.
Lemma lem5319811 : term135 = term79.
Proof. exact (MK_COMB (@lem5319810) (@lem5319809)). Qed.
Lemma lem5319813 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5319814 : term79 = term80.
Proof. exact (@lem5319813 term70 term53). Qed.
Lemma lem5319815 : term81 = term82.
Proof. exact (@lem996238 term82). Qed.
Lemma lem5319816 : (term81 = term82) = (term83 = term53).
Proof. exact (@lem1007663 (BIT1 0) term82 term82). Qed.
Lemma lem5319817 : term83 = term53.
Proof. exact (EQ_MP (@lem5319816) (@lem5319815)). Qed.
Lemma lem5319818 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319819 : term80 = term48.
Proof. exact (MK_COMB (@lem5319818) (@lem5319817)). Qed.
Lemma lem5319820 : term79 = term48.
Proof. exact (TRANS (@lem5319814) (@lem5319819)). Qed.
Lemma lem5319821 : term135 = term48.
Proof. exact (TRANS (@lem5319811) (@lem5319820)). Qed.
Lemma lem5319822 : term48 = term135.
Proof. exact (SYM (@lem5319821)). Qed.
Lemma lem5319823 : term130 = term135.
Proof. exact (TRANS (@lem5319800) (@lem5319822)). Qed.
Lemma lem5319824 : term108 = term52.
Proof. exact (@lem5319751 (@lem5319823)). Qed.
Lemma lem5319827 : term107 = term52.
Proof. exact (TRANS (@lem5319717) (@lem5319824)). Qed.
Lemma lem5319828 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5319829 : term136 = term137.
Proof. exact (MK_COMB (@lem5319828) (@lem5319827)). Qed.
Lemma lem5319830 (m : real) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem5319831 (m : real) : (term103 m) = (term63 m).
Proof. exact (MK_COMB (@lem5319829) (@lem5319830 m)). Qed.
Lemma lem5319832 (m : real) : (term102 m) = (term63 m).
Proof. exact (TRANS (@lem5319710 m) (@lem5319831 m)). Qed.
Lemma lem5319833 (l : real) : (term98 l) = (term98 l).
Proof. exact (eq_refl (term98 l)). Qed.
Lemma lem5319834 (l : real) (m : real) : (term101 l m) = (term138 l m).
Proof. exact (MK_COMB (@lem5319833 l) (@lem5319832 m)). Qed.
Lemma lem5319835 (l : real) (m : real) : (term100 l m) = (term138 l m).
Proof. exact (TRANS (@lem5319709 l m) (@lem5319834 l m)). Qed.
Lemma lem5319836 (l : real) (m : real) : (term60 l m) = (term138 l m).
Proof. exact (TRANS (@lem5319708 l m) (@lem5319835 l m)). Qed.
Lemma lem5319837 (l : real) (m : real) : (term59 l m) = (term138 l m).
Proof. exact (TRANS (@lem5319621 l m) (@lem5319836 l m)). Qed.
Lemma lem5319838 (l : real) (m : real) : (term58 l m) = (term138 l m).
Proof. exact (TRANS (@lem5319620 l m) (@lem5319837 l m)). Qed.
Lemma lem5319839 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5319840 (l : real) (m : real) : (term139 l m) = (term140 l m).
Proof. exact (MK_COMB (@lem5319839) (@lem5319838 l m)). Qed.
Lemma lem5319841 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5319842 (l : real) (m : real) : (term44 l m) = (term141 l m).
Proof. exact (MK_COMB (@lem5319840 l m) (@lem5319841)). Qed.
Lemma lem5319843 (l : real) (m : real) : (term43 l m) = (term141 l m).
Proof. exact (TRANS (@lem5319585 l m) (@lem5319842 l m)). Qed.
Lemma lem5319844 (m : real) (l : real) : (term142 m l) = (term143 m l).
Proof. exact (@lem1988295 (term45 l m) l). Qed.
Lemma lem5319845 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5319847 (x : real) (y : real) : (real_div x y) = (term46 x y).
Proof. exact (EQ_MP (@lem1982797 x y) (@lem1982796 x y)). Qed.
Lemma lem5319848 (l : real) (m : real) : (term45 l m) = (term47 l m).
Proof. exact (@lem5319847 (real_add l m) term48). Qed.
Lemma lem5319853 (n : nat) : (term49 n) = (term50 n).
Proof. exact (proj1 (@lem1981223 n (@el nat))). Qed.
Lemma lem5319855 : term51 = term52.
Proof. exact (@lem5319853 term53). Qed.
Lemma lem5319864 (l : real) (m : real) : (term54 l m) = (term54 l m).
Proof. exact (eq_refl (term54 l m)). Qed.
Lemma lem5319865 (l : real) (m : real) : (term47 l m) = (term55 l m).
Proof. exact (MK_COMB (@lem5319864 l m) (@lem5319855)). Qed.
Lemma lem5319866 (l : real) (m : real) : (term55 l m) = (term56 l m).
Proof. exact (@lem1982725 term52 (real_add l m)). Qed.
Lemma lem5319873 (l : real) (m : real) : (term56 l m) = (term57 l m).
Proof. exact (@lem1982781 l term52 m). Qed.
Lemma lem5319874 (l : real) (m : real) : (term55 l m) = (term57 l m).
Proof. exact (TRANS (@lem5319866 l m) (@lem5319873 l m)). Qed.
Lemma lem5319875 (l : real) (m : real) : (term47 l m) = (term57 l m).
Proof. exact (TRANS (@lem5319865 l m) (@lem5319874 l m)). Qed.
Lemma lem5319876 (l : real) (m : real) : (term45 l m) = (term57 l m).
Proof. exact (TRANS (@lem5319848 l m) (@lem5319875 l m)). Qed.
Lemma lem5319877 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5319878 (l : real) (m : real) : (term144 l m) = (term145 l m).
Proof. exact (MK_COMB (@lem5319877) (@lem5319876 l m)). Qed.
Lemma lem5319879 (m : real) (l : real) : (term146 m l) = (term147 m l).
Proof. exact (MK_COMB (@lem5319878 l m) (@lem5319845 l)). Qed.
Lemma lem5319880 (m : real) (l : real) : (term147 m l) = (term148 m l).
Proof. exact (@lem1982792 (term57 l m) l). Qed.
Lemma lem5319884 (l : real) (m : real) : (term148 m l) = (term149 l m).
Proof. exact (@lem1982759 (term63 l) (term150 l) (term63 m)). Qed.
Lemma lem5319885 (l : real) : (term151 l) = (term152 l).
Proof. exact (@lem1982711 term52 term64 l). Qed.
Lemma lem5319887 (x : nat) : (term67 x) = (term68 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5319888 : term64 = term69.
Proof. exact (@lem5319887 term70). Qed.
Lemma lem5319891 : term153 = term153.
Proof. exact (eq_refl term153). Qed.
Lemma lem5319892 : term154 = term155.
Proof. exact (MK_COMB (@lem5319891) (@lem5319888)). Qed.
Lemma lem5319893 : term156.
Proof. exact (@lem1981473 term76 term48 term64 term76 term64 term48). Qed.
Lemma lem5319895 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5319896 : term111 = term112.
Proof. exact (@lem5319895 (NUMERAL 0) term53). Qed.
Lemma lem5319897 : term113 = term82.
Proof. exact (@lem912803). Qed.
Lemma lem5319898 (h1 : term113 = term82) : term112 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term82 h1). Qed.
Lemma lem5319899 : (term113 = term82) = (term112 = True).
Proof. exact (prop_ext (fun h1 : term113 = term82 => @lem5319898 h1) (fun h1 : term112 = True => @lem5319897)). Qed.
Lemma lem5319900 : term112 = True.
Proof. exact (EQ_MP (@lem5319899) (@lem5319897)). Qed.
Lemma lem5319901 : term111 = True.
Proof. exact (TRANS (@lem5319896) (@lem5319900)). Qed.
Lemma lem5319902 : True = term111.
Proof. exact (SYM (@lem5319901)). Qed.
Lemma lem5319903 : term111.
Proof. exact (EQ_MP (@lem5319902) (@lem0)). Qed.
Lemma lem5319904 : term157.
Proof. exact (@lem5319893 (@lem5319903)). Qed.
Lemma lem5319906 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5319907 : term115 = term116.
Proof. exact (@lem5319906 (NUMERAL 0) term70). Qed.
Lemma lem5319908 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5319909 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5319910 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5319909 h1) (fun h1 : term116 = True => @lem5319908)). Qed.
Lemma lem5319911 : term116 = True.
Proof. exact (EQ_MP (@lem5319910) (@lem5319908)). Qed.
Lemma lem5319912 : term115 = True.
Proof. exact (TRANS (@lem5319907) (@lem5319911)). Qed.
Lemma lem5319913 : True = term115.
Proof. exact (SYM (@lem5319912)). Qed.
Lemma lem5319914 : term115.
Proof. exact (EQ_MP (@lem5319913) (@lem0)). Qed.
Lemma lem5319915 : term158.
Proof. exact (@lem5319904 (@lem5319914)). Qed.
Lemma lem5319917 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5319918 : term111 = term112.
Proof. exact (@lem5319917 (NUMERAL 0) term53). Qed.
Lemma lem5319919 : term113 = term82.
Proof. exact (@lem912803). Qed.
Lemma lem5319920 (h1 : term113 = term82) : term112 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term82 h1). Qed.
Lemma lem5319921 : (term113 = term82) = (term112 = True).
Proof. exact (prop_ext (fun h1 : term113 = term82 => @lem5319920 h1) (fun h1 : term112 = True => @lem5319919)). Qed.
Lemma lem5319922 : term112 = True.
Proof. exact (EQ_MP (@lem5319921) (@lem5319919)). Qed.
Lemma lem5319923 : term111 = True.
Proof. exact (TRANS (@lem5319918) (@lem5319922)). Qed.
Lemma lem5319924 : True = term111.
Proof. exact (SYM (@lem5319923)). Qed.
Lemma lem5319925 : term111.
Proof. exact (EQ_MP (@lem5319924) (@lem0)). Qed.
Lemma lem5319926 : term159.
Proof. exact (@lem5319915 (@lem5319925)). Qed.
Lemma lem5319928 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5319929 : term160 = term161.
Proof. exact (@lem5319928 term70 term53). Qed.
Lemma lem5319930 : term81 = term82.
Proof. exact (@lem996238 term82). Qed.
Lemma lem5319931 : (term81 = term82) = (term83 = term53).
Proof. exact (@lem1007663 (BIT1 0) term82 term82). Qed.
Lemma lem5319932 : term83 = term53.
Proof. exact (EQ_MP (@lem5319931) (@lem5319930)). Qed.
Lemma lem5319933 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319934 : term80 = term48.
Proof. exact (MK_COMB (@lem5319933) (@lem5319932)). Qed.
Lemma lem5319935 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5319936 : term161 = term162.
Proof. exact (MK_COMB (@lem5319935) (@lem5319934)). Qed.
Lemma lem5319937 : term160 = term162.
Proof. exact (TRANS (@lem5319929) (@lem5319936)). Qed.
Lemma lem5319939 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5319940 : term163 = term90.
Proof. exact (@lem5319939 term70 term70). Qed.
Lemma lem5319941 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5319942 : term89 = term70.
Proof. exact (EQ_MP (@lem5319941) (@lem940073)). Qed.
Lemma lem5319943 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319944 : term90 = term76.
Proof. exact (MK_COMB (@lem5319943) (@lem5319942)). Qed.
Lemma lem5319945 : term163 = term76.
Proof. exact (TRANS (@lem5319940) (@lem5319944)). Qed.
Lemma lem5319946 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5319947 : term164 = term165.
Proof. exact (MK_COMB (@lem5319946) (@lem5319945)). Qed.
Lemma lem5319948 : term166 = term167.
Proof. exact (MK_COMB (@lem5319947) (@lem5319937)). Qed.
Lemma lem5319951 : term168 = term64.
Proof. exact (@lem1367771 term70 term70). Qed.
Lemma lem5319952 : term125 = term82.
Proof. exact (@lem706885). Qed.
Lemma lem5319953 : (term125 = term82) = (term126 = term53).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term82). Qed.
Lemma lem5319954 : term126 = term53.
Proof. exact (EQ_MP (@lem5319953) (@lem5319952)). Qed.
Lemma lem5319955 : term53 = term126.
Proof. exact (SYM (@lem5319954)). Qed.
Lemma lem5319956 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319957 : term48 = term127.
Proof. exact (MK_COMB (@lem5319956) (@lem5319955)). Qed.
Lemma lem5319958 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5319959 : term162 = term169.
Proof. exact (MK_COMB (@lem5319958) (@lem5319957)). Qed.
Lemma lem5319960 : term165 = term165.
Proof. exact (eq_refl term165). Qed.
Lemma lem5319961 : term167 = term168.
Proof. exact (MK_COMB (@lem5319960) (@lem5319959)). Qed.
Lemma lem5319962 : term167 = term64.
Proof. exact (TRANS (@lem5319961) (@lem5319951)). Qed.
Lemma lem5319963 : term166 = term64.
Proof. exact (TRANS (@lem5319948) (@lem5319962)). Qed.
Lemma lem5319964 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5319965 : term170 = term71.
Proof. exact (MK_COMB (@lem5319964) (@lem5319963)). Qed.
Lemma lem5319966 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem5319967 : term171 = term160.
Proof. exact (MK_COMB (@lem5319965) (@lem5319966)). Qed.
Lemma lem5319969 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5319970 : term160 = term161.
Proof. exact (@lem5319969 term70 term53). Qed.
Lemma lem5319971 : term81 = term82.
Proof. exact (@lem996238 term82). Qed.
Lemma lem5319972 : (term81 = term82) = (term83 = term53).
Proof. exact (@lem1007663 (BIT1 0) term82 term82). Qed.
Lemma lem5319973 : term83 = term53.
Proof. exact (EQ_MP (@lem5319972) (@lem5319971)). Qed.
Lemma lem5319974 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319975 : term80 = term48.
Proof. exact (MK_COMB (@lem5319974) (@lem5319973)). Qed.
Lemma lem5319976 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5319977 : term161 = term162.
Proof. exact (MK_COMB (@lem5319976) (@lem5319975)). Qed.
Lemma lem5319978 : term160 = term162.
Proof. exact (TRANS (@lem5319970) (@lem5319977)). Qed.
Lemma lem5319979 : term171 = term162.
Proof. exact (TRANS (@lem5319967) (@lem5319978)). Qed.
Lemma lem5319981 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5319982 : term131 = term132.
Proof. exact (@lem5319981 term53 term70). Qed.
Lemma lem5319983 : term133 = term82.
Proof. exact (@lem996237 term82). Qed.
Lemma lem5319984 : (term133 = term82) = (term134 = term53).
Proof. exact (@lem1007663 term82 (BIT1 0) term82). Qed.
Lemma lem5319985 : term134 = term53.
Proof. exact (EQ_MP (@lem5319984) (@lem5319983)). Qed.
Lemma lem5319986 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319987 : term132 = term48.
Proof. exact (MK_COMB (@lem5319986) (@lem5319985)). Qed.
Lemma lem5319988 : term131 = term48.
Proof. exact (TRANS (@lem5319982) (@lem5319987)). Qed.
Lemma lem5319989 : term71 = term71.
Proof. exact (eq_refl term71). Qed.
Lemma lem5319990 : term172 = term160.
Proof. exact (MK_COMB (@lem5319989) (@lem5319988)). Qed.
Lemma lem5319992 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5319993 : term160 = term161.
Proof. exact (@lem5319992 term70 term53). Qed.
Lemma lem5319994 : term81 = term82.
Proof. exact (@lem996238 term82). Qed.
Lemma lem5319995 : (term81 = term82) = (term83 = term53).
Proof. exact (@lem1007663 (BIT1 0) term82 term82). Qed.
Lemma lem5319996 : term83 = term53.
Proof. exact (EQ_MP (@lem5319995) (@lem5319994)). Qed.
Lemma lem5319997 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5319998 : term80 = term48.
Proof. exact (MK_COMB (@lem5319997) (@lem5319996)). Qed.
Lemma lem5319999 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5320000 : term161 = term162.
Proof. exact (MK_COMB (@lem5319999) (@lem5319998)). Qed.
Lemma lem5320001 : term160 = term162.
Proof. exact (TRANS (@lem5319993) (@lem5320000)). Qed.
Lemma lem5320002 : term172 = term162.
Proof. exact (TRANS (@lem5319990) (@lem5320001)). Qed.
Lemma lem5320003 : term162 = term172.
Proof. exact (SYM (@lem5320002)). Qed.
Lemma lem5320004 : term171 = term172.
Proof. exact (TRANS (@lem5319979) (@lem5320003)). Qed.
Lemma lem5320005 : term155 = term93.
Proof. exact (@lem5319926 (@lem5320004)). Qed.
Lemma lem5320008 : term154 = term93.
Proof. exact (TRANS (@lem5319892) (@lem5320005)). Qed.
Lemma lem5320009 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5320010 : term173 = term95.
Proof. exact (MK_COMB (@lem5320009) (@lem5320008)). Qed.
Lemma lem5320011 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5320012 (l : real) : (term152 l) = (term96 l).
Proof. exact (MK_COMB (@lem5320010) (@lem5320011 l)). Qed.
Lemma lem5320013 (l : real) : (term151 l) = (term96 l).
Proof. exact (TRANS (@lem5319885 l) (@lem5320012 l)). Qed.
Lemma lem5320014 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5320015 (l : real) : (term174 l) = (term98 l).
Proof. exact (MK_COMB (@lem5320014) (@lem5320013 l)). Qed.
Lemma lem5320016 (m : real) : (term63 m) = (term63 m).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem5320017 (l : real) (m : real) : (term149 l m) = (term138 l m).
Proof. exact (MK_COMB (@lem5320015 l) (@lem5320016 m)). Qed.
Lemma lem5320019 (l : real) (m : real) : (term148 m l) = (term138 l m).
Proof. exact (TRANS (@lem5319884 l m) (@lem5320017 l m)). Qed.
Lemma lem5320020 (l : real) (m : real) : (term147 m l) = (term138 l m).
Proof. exact (TRANS (@lem5319880 m l) (@lem5320019 l m)). Qed.
Lemma lem5320021 (l : real) (m : real) : (term146 m l) = (term138 l m).
Proof. exact (TRANS (@lem5319879 m l) (@lem5320020 l m)). Qed.
Lemma lem5320022 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5320023 (l : real) (m : real) : (term175 m l) = (term140 l m).
Proof. exact (MK_COMB (@lem5320022) (@lem5320021 l m)). Qed.
Lemma lem5320024 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5320025 (l : real) (m : real) : (term143 m l) = (term141 l m).
Proof. exact (MK_COMB (@lem5320023 l m) (@lem5320024)). Qed.
Lemma lem5320026 (l : real) (m : real) : (term142 m l) = (term141 l m).
Proof. exact (TRANS (@lem5319844 m l) (@lem5320025 l m)). Qed.
Lemma lem5320027 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5320028 (l : real) (m : real) : (term176 l m) = (term177 l m).
Proof. exact (MK_COMB (@lem5320027) (@lem5319843 l m)). Qed.
Lemma lem5320029 (l : real) (m : real) : (term20 m l) = (term178 l m).
Proof. exact (MK_COMB (@lem5320028 l m) (@lem5320026 l m)). Qed.
Lemma lem5320030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5320031 (l : real) (m : real) : (term23 m l) = (term179 l m).
Proof. exact (MK_COMB (@lem5320030) (@lem5319584 l m)). Qed.
Lemma lem5320032 (l : real) (m : real) : (term25 m l) = (term180 l m).
Proof. exact (MK_COMB (@lem5320031 l m) (@lem5320029 l m)). Qed.
Lemma lem5320034 (t : real -> Prop) : (term28 t) = (term28 t).
Proof. exact (eq_refl (term28 t)). Qed.
Lemma lem5320035 (t : real -> Prop) (l : real) (m : real) : (term30 t m l) = (term181 t l m).
Proof. exact (MK_COMB (@lem5320034 t) (@lem5320032 l m)). Qed.
Lemma lem5320037 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5320038 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : (term34 s t m l) = (term182 s t l m).
Proof. exact (MK_COMB (@lem5320037 s) (@lem5320035 t l m)). Qed.
Lemma lem5320045 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : (term35 s t m l) = (term182 s t l m).
Proof. exact (TRANS (@lem5319563 s t m l) (@lem5320038 s t l m)). Qed.
Lemma lem5320062 (l : real) (m : real) : (term180 l m) = (term183 l m).
Proof. exact (@lem19158 (term141 l m) (term42 l m) (term141 l m)). Qed.
Lemma lem5320065 (t : real -> Prop) : (term28 t) = (term28 t).
Proof. exact (eq_refl (term28 t)). Qed.
Lemma lem5320066 (t : real -> Prop) (l : real) (m : real) : (term181 t l m) = (term184 t l m).
Proof. exact (MK_COMB (@lem5320065 t) (@lem5320062 l m)). Qed.
Lemma lem5320073 (t : real -> Prop) (l : real) (m : real) : (term184 t l m) = (term185 t l m).
Proof. exact (@lem19158 (term186 l m) (term12 t) (term186 l m)). Qed.
Lemma lem5320074 (t : real -> Prop) (l : real) (m : real) : (term181 t l m) = (term185 t l m).
Proof. exact (TRANS (@lem5320066 t l m) (@lem5320073 t l m)). Qed.
Lemma lem5320077 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5320078 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : (term182 s t l m) = (term187 s t l m).
Proof. exact (MK_COMB (@lem5320077 s) (@lem5320074 t l m)). Qed.
Lemma lem5320085 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : (term187 s t l m) = (term188 s t l m).
Proof. exact (@lem19158 (term189 t l m) (term12 s) (term189 t l m)). Qed.
Lemma lem5320086 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : (term182 s t l m) = (term188 s t l m).
Proof. exact (TRANS (@lem5320078 s t l m) (@lem5320085 s t l m)). Qed.
Lemma lem5320087 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) : (term35 s t m l) = (term188 s t l m).
Proof. exact (TRANS (@lem5320045 s t l m) (@lem5320086 s t l m)). Qed.
Lemma lem5320097 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term188 s t l m) : term188 s t l m.
Proof. exact (h1). Qed.
Lemma lem5320098 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term190 s t l m.
Proof. exact (h1). Qed.
Lemma lem5320099 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term189 t l m.
Proof. exact (proj2 (@lem5320098 s t l m h1)). Qed.
Lemma lem5320101 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term186 l m.
Proof. exact (proj2 (@lem5320099 s t l m h1)). Qed.
Lemma lem5320103 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term141 l m.
Proof. exact (proj2 (@lem5320101 s t l m h1)). Qed.
Lemma lem5320104 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term42 l m.
Proof. exact (proj1 (@lem5320101 s t l m h1)). Qed.
Lemma lem5320106 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5320107 : term191 = term115.
Proof. exact (@lem5320106 term41 term76). Qed.
Lemma lem5320109 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5320110 : term76 = term105.
Proof. exact (@lem5320109 term70). Qed.
Lemma lem5320112 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5320113 : term41 = term192.
Proof. exact (@lem5320112 (NUMERAL 0)). Qed.
Lemma lem5320114 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5320115 : term193 = term194.
Proof. exact (MK_COMB (@lem5320114) (@lem5320113)). Qed.
Lemma lem5320116 : term115 = term195.
Proof. exact (MK_COMB (@lem5320115) (@lem5320110)). Qed.
Lemma lem5320117 : term196.
Proof. exact (@lem1980255 term41 term76 term76 term76). Qed.
Lemma lem5320119 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320120 : term115 = term116.
Proof. exact (@lem5320119 (NUMERAL 0) term70). Qed.
Lemma lem5320121 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5320122 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5320123 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5320122 h1) (fun h1 : term116 = True => @lem5320121)). Qed.
Lemma lem5320124 : term116 = True.
Proof. exact (EQ_MP (@lem5320123) (@lem5320121)). Qed.
Lemma lem5320125 : term115 = True.
Proof. exact (TRANS (@lem5320120) (@lem5320124)). Qed.
Lemma lem5320126 : True = term115.
Proof. exact (SYM (@lem5320125)). Qed.
Lemma lem5320127 : term115.
Proof. exact (EQ_MP (@lem5320126) (@lem0)). Qed.
Lemma lem5320128 : term197.
Proof. exact (@lem5320117 (@lem5320127)). Qed.
Lemma lem5320130 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320131 : term115 = term116.
Proof. exact (@lem5320130 (NUMERAL 0) term70). Qed.
Lemma lem5320132 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5320133 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5320134 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5320133 h1) (fun h1 : term116 = True => @lem5320132)). Qed.
Lemma lem5320135 : term116 = True.
Proof. exact (EQ_MP (@lem5320134) (@lem5320132)). Qed.
Lemma lem5320136 : term115 = True.
Proof. exact (TRANS (@lem5320131) (@lem5320135)). Qed.
Lemma lem5320137 : True = term115.
Proof. exact (SYM (@lem5320136)). Qed.
Lemma lem5320138 : term115.
Proof. exact (EQ_MP (@lem5320137) (@lem0)). Qed.
Lemma lem5320139 : term195 = term198.
Proof. exact (@lem5320128 (@lem5320138)). Qed.
Lemma lem5320141 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5320142 : term163 = term90.
Proof. exact (@lem5320141 term70 term70). Qed.
Lemma lem5320143 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5320144 : term89 = term70.
Proof. exact (EQ_MP (@lem5320143) (@lem940073)). Qed.
Lemma lem5320145 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320146 : term90 = term76.
Proof. exact (MK_COMB (@lem5320145) (@lem5320144)). Qed.
Lemma lem5320147 : term163 = term76.
Proof. exact (TRANS (@lem5320142) (@lem5320146)). Qed.
Lemma lem5320149 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5320150 : term200 = term41.
Proof. exact (@lem5320149 term70). Qed.
Lemma lem5320151 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5320152 : term201 = term193.
Proof. exact (MK_COMB (@lem5320151) (@lem5320150)). Qed.
Lemma lem5320153 : term198 = term115.
Proof. exact (MK_COMB (@lem5320152) (@lem5320147)). Qed.
Lemma lem5320155 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320156 : term115 = term116.
Proof. exact (@lem5320155 (NUMERAL 0) term70). Qed.
Lemma lem5320157 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5320158 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5320159 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5320158 h1) (fun h1 : term116 = True => @lem5320157)). Qed.
Lemma lem5320160 : term116 = True.
Proof. exact (EQ_MP (@lem5320159) (@lem5320157)). Qed.
Lemma lem5320161 : term115 = True.
Proof. exact (TRANS (@lem5320156) (@lem5320160)). Qed.
Lemma lem5320162 : term198 = True.
Proof. exact (TRANS (@lem5320153) (@lem5320161)). Qed.
Lemma lem5320163 : term195 = True.
Proof. exact (TRANS (@lem5320139) (@lem5320162)). Qed.
Lemma lem5320164 : term115 = True.
Proof. exact (TRANS (@lem5320116) (@lem5320163)). Qed.
Lemma lem5320165 : term191 = True.
Proof. exact (TRANS (@lem5320107) (@lem5320164)). Qed.
Lemma lem5320166 : True = term191.
Proof. exact (SYM (@lem5320165)). Qed.
Lemma lem5320167 : term191.
Proof. exact (EQ_MP (@lem5320166) (@lem0)). Qed.
Lemma lem5320168 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term202 l m.
Proof. exact (conj (@lem5320167) (@lem5320103 s t l m h1)). Qed.
Lemma lem5320170 (x : real) (y : real) : term203 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5320171 (l : real) (m : real) : term204 l m.
Proof. exact (@lem5320170 term76 (term138 l m)). Qed.
Lemma lem5320172 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term205 l m.
Proof. exact (@lem5320171 l m (@lem5320168 s t l m h1)). Qed.
Lemma lem5320173 (l : real) (m : real) : (term206 l m) = (term138 l m).
Proof. exact (@lem1982733 (term138 l m)). Qed.
Lemma lem5320174 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5320175 (l : real) (m : real) : (term207 l m) = (term140 l m).
Proof. exact (MK_COMB (@lem5320174) (@lem5320173 l m)). Qed.
Lemma lem5320176 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5320177 (l : real) (m : real) : (term205 l m) = (term141 l m).
Proof. exact (MK_COMB (@lem5320175 l m) (@lem5320176)). Qed.
Lemma lem5320178 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term141 l m.
Proof. exact (EQ_MP (@lem5320177 l m) (@lem5320172 s t l m h1)). Qed.
Lemma lem5320180 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5320181 : term208 = term209.
Proof. exact (@lem5320180 term41 term52). Qed.
Lemma lem5320182 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem5320184 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5320185 : term41 = term192.
Proof. exact (@lem5320184 (NUMERAL 0)). Qed.
Lemma lem5320186 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5320187 : term193 = term194.
Proof. exact (MK_COMB (@lem5320186) (@lem5320185)). Qed.
Lemma lem5320188 : term209 = term210.
Proof. exact (MK_COMB (@lem5320187) (@lem5320182)). Qed.
Lemma lem5320189 : term211.
Proof. exact (@lem1980255 term41 term48 term76 term76). Qed.
Lemma lem5320191 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320192 : term115 = term116.
Proof. exact (@lem5320191 (NUMERAL 0) term70). Qed.
Lemma lem5320193 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5320194 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5320195 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5320194 h1) (fun h1 : term116 = True => @lem5320193)). Qed.
Lemma lem5320196 : term116 = True.
Proof. exact (EQ_MP (@lem5320195) (@lem5320193)). Qed.
Lemma lem5320197 : term115 = True.
Proof. exact (TRANS (@lem5320192) (@lem5320196)). Qed.
Lemma lem5320198 : True = term115.
Proof. exact (SYM (@lem5320197)). Qed.
Lemma lem5320199 : term115.
Proof. exact (EQ_MP (@lem5320198) (@lem0)). Qed.
Lemma lem5320200 : term212.
Proof. exact (@lem5320189 (@lem5320199)). Qed.
Lemma lem5320202 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320203 : term111 = term112.
Proof. exact (@lem5320202 (NUMERAL 0) term53). Qed.
Lemma lem5320204 : term113 = term82.
Proof. exact (@lem912803). Qed.
Lemma lem5320205 (h1 : term113 = term82) : term112 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term82 h1). Qed.
Lemma lem5320206 : (term113 = term82) = (term112 = True).
Proof. exact (prop_ext (fun h1 : term113 = term82 => @lem5320205 h1) (fun h1 : term112 = True => @lem5320204)). Qed.
Lemma lem5320207 : term112 = True.
Proof. exact (EQ_MP (@lem5320206) (@lem5320204)). Qed.
Lemma lem5320208 : term111 = True.
Proof. exact (TRANS (@lem5320203) (@lem5320207)). Qed.
Lemma lem5320209 : True = term111.
Proof. exact (SYM (@lem5320208)). Qed.
Lemma lem5320210 : term111.
Proof. exact (EQ_MP (@lem5320209) (@lem0)). Qed.
Lemma lem5320211 : term210 = term213.
Proof. exact (@lem5320200 (@lem5320210)). Qed.
Lemma lem5320213 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5320214 : term163 = term90.
Proof. exact (@lem5320213 term70 term70). Qed.
Lemma lem5320215 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5320216 : term89 = term70.
Proof. exact (EQ_MP (@lem5320215) (@lem940073)). Qed.
Lemma lem5320217 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320218 : term90 = term76.
Proof. exact (MK_COMB (@lem5320217) (@lem5320216)). Qed.
Lemma lem5320219 : term163 = term76.
Proof. exact (TRANS (@lem5320214) (@lem5320218)). Qed.
Lemma lem5320221 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5320222 : term214 = term41.
Proof. exact (@lem5320221 term53). Qed.
Lemma lem5320223 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5320224 : term215 = term193.
Proof. exact (MK_COMB (@lem5320223) (@lem5320222)). Qed.
Lemma lem5320225 : term213 = term115.
Proof. exact (MK_COMB (@lem5320224) (@lem5320219)). Qed.
Lemma lem5320227 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320228 : term115 = term116.
Proof. exact (@lem5320227 (NUMERAL 0) term70). Qed.
Lemma lem5320229 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5320230 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5320231 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5320230 h1) (fun h1 : term116 = True => @lem5320229)). Qed.
Lemma lem5320232 : term116 = True.
Proof. exact (EQ_MP (@lem5320231) (@lem5320229)). Qed.
Lemma lem5320233 : term115 = True.
Proof. exact (TRANS (@lem5320228) (@lem5320232)). Qed.
Lemma lem5320234 : term213 = True.
Proof. exact (TRANS (@lem5320225) (@lem5320233)). Qed.
Lemma lem5320235 : term210 = True.
Proof. exact (TRANS (@lem5320211) (@lem5320234)). Qed.
Lemma lem5320236 : term209 = True.
Proof. exact (TRANS (@lem5320188) (@lem5320235)). Qed.
Lemma lem5320237 : term208 = True.
Proof. exact (TRANS (@lem5320181) (@lem5320236)). Qed.
Lemma lem5320238 : True = term208.
Proof. exact (SYM (@lem5320237)). Qed.
Lemma lem5320239 : term208.
Proof. exact (EQ_MP (@lem5320238) (@lem0)). Qed.
Lemma lem5320240 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term216 l m.
Proof. exact (conj (@lem5320239) (@lem5320104 s t l m h1)). Qed.
Lemma lem5320242 (x : real) (y : real) : term217 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5320243 (l : real) (m : real) : term218 l m.
Proof. exact (@lem5320242 term52 (term38 l m)). Qed.
Lemma lem5320244 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term219 l m.
Proof. exact (@lem5320243 l m (@lem5320240 s t l m h1)). Qed.
Lemma lem5320245 (l : real) (m : real) : (term220 l m) = (term221 l m).
Proof. exact (@lem1982781 l term52 (term150 m)). Qed.
Lemma lem5320246 (m : real) : (term222 m) = (term223 m).
Proof. exact (@lem1982749 term52 term64 m). Qed.
Lemma lem5320248 (x : nat) : (term67 x) = (term68 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5320249 : term64 = term69.
Proof. exact (@lem5320248 term70). Qed.
Lemma lem5320252 : term137 = term137.
Proof. exact (eq_refl term137). Qed.
Lemma lem5320253 : term224 = term225.
Proof. exact (MK_COMB (@lem5320252) (@lem5320249)). Qed.
Lemma lem5320254 : term225 = term226.
Proof. exact (@lem1981613 term76 term64 term48 term76). Qed.
Lemma lem5320256 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5320257 : term131 = term132.
Proof. exact (@lem5320256 term53 term70). Qed.
Lemma lem5320258 : term133 = term82.
Proof. exact (@lem996237 term82). Qed.
Lemma lem5320259 : (term133 = term82) = (term134 = term53).
Proof. exact (@lem1007663 term82 (BIT1 0) term82). Qed.
Lemma lem5320260 : term134 = term53.
Proof. exact (EQ_MP (@lem5320259) (@lem5320258)). Qed.
Lemma lem5320261 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320262 : term132 = term48.
Proof. exact (MK_COMB (@lem5320261) (@lem5320260)). Qed.
Lemma lem5320263 : term131 = term48.
Proof. exact (TRANS (@lem5320257) (@lem5320262)). Qed.
Lemma lem5320265 (m : nat) (n : nat) : (term227 m n) = (term85 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem5320266 : term228 = term87.
Proof. exact (@lem5320265 term70 term70). Qed.
Lemma lem5320267 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5320268 : term89 = term70.
Proof. exact (EQ_MP (@lem5320267) (@lem940073)). Qed.
Lemma lem5320269 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320270 : term90 = term76.
Proof. exact (MK_COMB (@lem5320269) (@lem5320268)). Qed.
Lemma lem5320271 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5320272 : term87 = term64.
Proof. exact (MK_COMB (@lem5320271) (@lem5320270)). Qed.
Lemma lem5320273 : term228 = term64.
Proof. exact (TRANS (@lem5320266) (@lem5320272)). Qed.
Lemma lem5320274 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5320275 : term229 = term92.
Proof. exact (MK_COMB (@lem5320274) (@lem5320273)). Qed.
Lemma lem5320276 : term226 = term93.
Proof. exact (MK_COMB (@lem5320275) (@lem5320263)). Qed.
Lemma lem5320277 : term225 = term93.
Proof. exact (TRANS (@lem5320254) (@lem5320276)). Qed.
Lemma lem5320280 : term224 = term93.
Proof. exact (TRANS (@lem5320253) (@lem5320277)). Qed.
Lemma lem5320281 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5320282 : term230 = term95.
Proof. exact (MK_COMB (@lem5320281) (@lem5320280)). Qed.
Lemma lem5320283 (m : real) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem5320284 (m : real) : (term223 m) = (term96 m).
Proof. exact (MK_COMB (@lem5320282) (@lem5320283 m)). Qed.
Lemma lem5320285 (m : real) : (term222 m) = (term96 m).
Proof. exact (TRANS (@lem5320246 m) (@lem5320284 m)). Qed.
Lemma lem5320288 (l : real) : (term231 l) = (term231 l).
Proof. exact (eq_refl (term231 l)). Qed.
Lemma lem5320289 (l : real) (m : real) : (term221 l m) = (term232 l m).
Proof. exact (MK_COMB (@lem5320288 l) (@lem5320285 m)). Qed.
Lemma lem5320290 (l : real) (m : real) : (term220 l m) = (term232 l m).
Proof. exact (TRANS (@lem5320245 l m) (@lem5320289 l m)). Qed.
Lemma lem5320291 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5320292 (l : real) (m : real) : (term233 l m) = (term234 l m).
Proof. exact (MK_COMB (@lem5320291) (@lem5320290 l m)). Qed.
Lemma lem5320293 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5320294 (l : real) (m : real) : (term219 l m) = (term235 l m).
Proof. exact (MK_COMB (@lem5320292 l m) (@lem5320293)). Qed.
Lemma lem5320295 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term235 l m.
Proof. exact (EQ_MP (@lem5320294 l m) (@lem5320244 s t l m h1)). Qed.
Lemma lem5320296 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term236 l m.
Proof. exact (conj (@lem5320295 s t l m h1) (@lem5320178 s t l m h1)). Qed.
Lemma lem5320298 (x : real) (y : real) : term237 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5320299 (l : real) (m : real) : term238 l m.
Proof. exact (@lem5320298 (term232 l m) (term138 l m)). Qed.
Lemma lem5320300 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term239 l m.
Proof. exact (@lem5320299 l m (@lem5320296 s t l m h1)). Qed.
Lemma lem5320301 (l : real) (m : real) : (term240 l m) = (term241 l m).
Proof. exact (@lem1982753 (term63 l) (term96 l) (term96 m) (term63 m)). Qed.
Lemma lem5320302 (l : real) : (term242 l) = (term243 l).
Proof. exact (@lem1982711 term52 term93 l). Qed.
Lemma lem5320308 : term244.
Proof. exact (@lem1981473 term76 term48 term64 term48 term41 term76). Qed.
Lemma lem5320310 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320311 : term111 = term112.
Proof. exact (@lem5320310 (NUMERAL 0) term53). Qed.
Lemma lem5320312 : term113 = term82.
Proof. exact (@lem912803). Qed.
Lemma lem5320313 (h1 : term113 = term82) : term112 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term82 h1). Qed.
Lemma lem5320314 : (term113 = term82) = (term112 = True).
Proof. exact (prop_ext (fun h1 : term113 = term82 => @lem5320313 h1) (fun h1 : term112 = True => @lem5320312)). Qed.
Lemma lem5320315 : term112 = True.
Proof. exact (EQ_MP (@lem5320314) (@lem5320312)). Qed.
Lemma lem5320316 : term111 = True.
Proof. exact (TRANS (@lem5320311) (@lem5320315)). Qed.
Lemma lem5320317 : True = term111.
Proof. exact (SYM (@lem5320316)). Qed.
Lemma lem5320318 : term111.
Proof. exact (EQ_MP (@lem5320317) (@lem0)). Qed.
Lemma lem5320319 : term245.
Proof. exact (@lem5320308 (@lem5320318)). Qed.
Lemma lem5320321 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320322 : term111 = term112.
Proof. exact (@lem5320321 (NUMERAL 0) term53). Qed.
Lemma lem5320323 : term113 = term82.
Proof. exact (@lem912803). Qed.
Lemma lem5320324 (h1 : term113 = term82) : term112 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term82 h1). Qed.
Lemma lem5320325 : (term113 = term82) = (term112 = True).
Proof. exact (prop_ext (fun h1 : term113 = term82 => @lem5320324 h1) (fun h1 : term112 = True => @lem5320323)). Qed.
Lemma lem5320326 : term112 = True.
Proof. exact (EQ_MP (@lem5320325) (@lem5320323)). Qed.
Lemma lem5320327 : term111 = True.
Proof. exact (TRANS (@lem5320322) (@lem5320326)). Qed.
Lemma lem5320328 : True = term111.
Proof. exact (SYM (@lem5320327)). Qed.
Lemma lem5320329 : term111.
Proof. exact (EQ_MP (@lem5320328) (@lem0)). Qed.
Lemma lem5320330 : term246.
Proof. exact (@lem5320319 (@lem5320329)). Qed.
Lemma lem5320332 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320333 : term115 = term116.
Proof. exact (@lem5320332 (NUMERAL 0) term70). Qed.
Lemma lem5320334 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5320335 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5320336 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5320335 h1) (fun h1 : term116 = True => @lem5320334)). Qed.
Lemma lem5320337 : term116 = True.
Proof. exact (EQ_MP (@lem5320336) (@lem5320334)). Qed.
Lemma lem5320338 : term115 = True.
Proof. exact (TRANS (@lem5320333) (@lem5320337)). Qed.
Lemma lem5320339 : True = term115.
Proof. exact (SYM (@lem5320338)). Qed.
Lemma lem5320340 : term115.
Proof. exact (EQ_MP (@lem5320339) (@lem0)). Qed.
Lemma lem5320341 : term247.
Proof. exact (@lem5320330 (@lem5320340)). Qed.
Lemma lem5320343 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5320344 : term160 = term161.
Proof. exact (@lem5320343 term70 term53). Qed.
Lemma lem5320345 : term81 = term82.
Proof. exact (@lem996238 term82). Qed.
Lemma lem5320346 : (term81 = term82) = (term83 = term53).
Proof. exact (@lem1007663 (BIT1 0) term82 term82). Qed.
Lemma lem5320347 : term83 = term53.
Proof. exact (EQ_MP (@lem5320346) (@lem5320345)). Qed.
Lemma lem5320348 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320349 : term80 = term48.
Proof. exact (MK_COMB (@lem5320348) (@lem5320347)). Qed.
Lemma lem5320350 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5320351 : term161 = term162.
Proof. exact (MK_COMB (@lem5320350) (@lem5320349)). Qed.
Lemma lem5320352 : term160 = term162.
Proof. exact (TRANS (@lem5320344) (@lem5320351)). Qed.
Lemma lem5320354 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5320355 : term79 = term80.
Proof. exact (@lem5320354 term70 term53). Qed.
Lemma lem5320356 : term81 = term82.
Proof. exact (@lem996238 term82). Qed.
Lemma lem5320357 : (term81 = term82) = (term83 = term53).
Proof. exact (@lem1007663 (BIT1 0) term82 term82). Qed.
Lemma lem5320358 : term83 = term53.
Proof. exact (EQ_MP (@lem5320357) (@lem5320356)). Qed.
Lemma lem5320359 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320360 : term80 = term48.
Proof. exact (MK_COMB (@lem5320359) (@lem5320358)). Qed.
Lemma lem5320361 : term79 = term48.
Proof. exact (TRANS (@lem5320355) (@lem5320360)). Qed.
Lemma lem5320362 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5320363 : term248 = term249.
Proof. exact (MK_COMB (@lem5320362) (@lem5320361)). Qed.
Lemma lem5320364 : term250 = term251.
Proof. exact (MK_COMB (@lem5320363) (@lem5320352)). Qed.
Lemma lem5320366 (m : nat) : (term252 m) = term41.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5320367 : term251 = term41.
Proof. exact (@lem5320366 term53). Qed.
Lemma lem5320368 : term250 = term41.
Proof. exact (TRANS (@lem5320364) (@lem5320367)). Qed.
Lemma lem5320369 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5320370 : term253 = term254.
Proof. exact (MK_COMB (@lem5320369) (@lem5320368)). Qed.
Lemma lem5320371 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem5320372 : term255 = term200.
Proof. exact (MK_COMB (@lem5320370) (@lem5320371)). Qed.
Lemma lem5320374 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5320375 : term200 = term41.
Proof. exact (@lem5320374 term70). Qed.
Lemma lem5320376 : term255 = term41.
Proof. exact (TRANS (@lem5320372) (@lem5320375)). Qed.
Lemma lem5320378 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5320379 : term256 = term257.
Proof. exact (@lem5320378 term53 term53). Qed.
Lemma lem5320380 : (term88 = (BIT1 0)) = (term258 = term259).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5320381 : term258 = term259.
Proof. exact (EQ_MP (@lem5320380) (@lem940073)). Qed.
Lemma lem5320382 : (term258 = term259) = (term260 = term261).
Proof. exact (@lem1008952 term82 term259). Qed.
Lemma lem5320383 : term260 = term261.
Proof. exact (EQ_MP (@lem5320382) (@lem5320381)). Qed.
Lemma lem5320384 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320385 : term257 = term262.
Proof. exact (MK_COMB (@lem5320384) (@lem5320383)). Qed.
Lemma lem5320386 : term256 = term262.
Proof. exact (TRANS (@lem5320379) (@lem5320385)). Qed.
Lemma lem5320387 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5320388 : term263 = term264.
Proof. exact (MK_COMB (@lem5320387) (@lem5320386)). Qed.
Lemma lem5320390 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5320391 : term264 = term41.
Proof. exact (@lem5320390 term261). Qed.
Lemma lem5320392 : term263 = term41.
Proof. exact (TRANS (@lem5320388) (@lem5320391)). Qed.
Lemma lem5320393 : term41 = term263.
Proof. exact (SYM (@lem5320392)). Qed.
Lemma lem5320394 : term255 = term263.
Proof. exact (TRANS (@lem5320376) (@lem5320393)). Qed.
Lemma lem5320396 : term265 = term192.
Proof. exact (@lem5320341 (@lem5320394)). Qed.
Lemma lem5320398 (x : real) : (term266 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5320399 : term192 = term41.
Proof. exact (@lem5320398 term41). Qed.
Lemma lem5320400 : term265 = term41.
Proof. exact (TRANS (@lem5320396) (@lem5320399)). Qed.
Lemma lem5320401 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5320402 : term267 = term254.
Proof. exact (MK_COMB (@lem5320401) (@lem5320400)). Qed.
Lemma lem5320403 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5320404 (l : real) : (term243 l) = (term268 l).
Proof. exact (MK_COMB (@lem5320402) (@lem5320403 l)). Qed.
Lemma lem5320405 (l : real) : (term242 l) = (term268 l).
Proof. exact (TRANS (@lem5320302 l) (@lem5320404 l)). Qed.
Lemma lem5320406 (l : real) : (term268 l) = term41.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5320407 (l : real) : (term242 l) = term41.
Proof. exact (TRANS (@lem5320405 l) (@lem5320406 l)). Qed.
Lemma lem5320408 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5320409 (l : real) : (term269 l) = term270.
Proof. exact (MK_COMB (@lem5320408) (@lem5320407 l)). Qed.
Lemma lem5320410 (m : real) : (term271 m) = (term272 m).
Proof. exact (@lem1982711 term93 term52 m). Qed.
Lemma lem5320416 : term273.
Proof. exact (@lem1981473 term64 term48 term76 term48 term41 term76). Qed.
Lemma lem5320418 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320419 : term111 = term112.
Proof. exact (@lem5320418 (NUMERAL 0) term53). Qed.
Lemma lem5320420 : term113 = term82.
Proof. exact (@lem912803). Qed.
Lemma lem5320421 (h1 : term113 = term82) : term112 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term82 h1). Qed.
Lemma lem5320422 : (term113 = term82) = (term112 = True).
Proof. exact (prop_ext (fun h1 : term113 = term82 => @lem5320421 h1) (fun h1 : term112 = True => @lem5320420)). Qed.
Lemma lem5320423 : term112 = True.
Proof. exact (EQ_MP (@lem5320422) (@lem5320420)). Qed.
Lemma lem5320424 : term111 = True.
Proof. exact (TRANS (@lem5320419) (@lem5320423)). Qed.
Lemma lem5320425 : True = term111.
Proof. exact (SYM (@lem5320424)). Qed.
Lemma lem5320426 : term111.
Proof. exact (EQ_MP (@lem5320425) (@lem0)). Qed.
Lemma lem5320427 : term274.
Proof. exact (@lem5320416 (@lem5320426)). Qed.
Lemma lem5320429 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320430 : term111 = term112.
Proof. exact (@lem5320429 (NUMERAL 0) term53). Qed.
Lemma lem5320431 : term113 = term82.
Proof. exact (@lem912803). Qed.
Lemma lem5320432 (h1 : term113 = term82) : term112 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term82 h1). Qed.
Lemma lem5320433 : (term113 = term82) = (term112 = True).
Proof. exact (prop_ext (fun h1 : term113 = term82 => @lem5320432 h1) (fun h1 : term112 = True => @lem5320431)). Qed.
Lemma lem5320434 : term112 = True.
Proof. exact (EQ_MP (@lem5320433) (@lem5320431)). Qed.
Lemma lem5320435 : term111 = True.
Proof. exact (TRANS (@lem5320430) (@lem5320434)). Qed.
Lemma lem5320436 : True = term111.
Proof. exact (SYM (@lem5320435)). Qed.
Lemma lem5320437 : term111.
Proof. exact (EQ_MP (@lem5320436) (@lem0)). Qed.
Lemma lem5320438 : term275.
Proof. exact (@lem5320427 (@lem5320437)). Qed.
Lemma lem5320440 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320441 : term115 = term116.
Proof. exact (@lem5320440 (NUMERAL 0) term70). Qed.
Lemma lem5320442 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5320443 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5320444 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5320443 h1) (fun h1 : term116 = True => @lem5320442)). Qed.
Lemma lem5320445 : term116 = True.
Proof. exact (EQ_MP (@lem5320444) (@lem5320442)). Qed.
Lemma lem5320446 : term115 = True.
Proof. exact (TRANS (@lem5320441) (@lem5320445)). Qed.
Lemma lem5320447 : True = term115.
Proof. exact (SYM (@lem5320446)). Qed.
Lemma lem5320448 : term115.
Proof. exact (EQ_MP (@lem5320447) (@lem0)). Qed.
Lemma lem5320449 : term276.
Proof. exact (@lem5320438 (@lem5320448)). Qed.
Lemma lem5320451 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5320452 : term79 = term80.
Proof. exact (@lem5320451 term70 term53). Qed.
Lemma lem5320453 : term81 = term82.
Proof. exact (@lem996238 term82). Qed.
Lemma lem5320454 : (term81 = term82) = (term83 = term53).
Proof. exact (@lem1007663 (BIT1 0) term82 term82). Qed.
Lemma lem5320455 : term83 = term53.
Proof. exact (EQ_MP (@lem5320454) (@lem5320453)). Qed.
Lemma lem5320456 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320457 : term80 = term48.
Proof. exact (MK_COMB (@lem5320456) (@lem5320455)). Qed.
Lemma lem5320458 : term79 = term48.
Proof. exact (TRANS (@lem5320452) (@lem5320457)). Qed.
Lemma lem5320460 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5320461 : term160 = term161.
Proof. exact (@lem5320460 term70 term53). Qed.
Lemma lem5320462 : term81 = term82.
Proof. exact (@lem996238 term82). Qed.
Lemma lem5320463 : (term81 = term82) = (term83 = term53).
Proof. exact (@lem1007663 (BIT1 0) term82 term82). Qed.
Lemma lem5320464 : term83 = term53.
Proof. exact (EQ_MP (@lem5320463) (@lem5320462)). Qed.
Lemma lem5320465 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320466 : term80 = term48.
Proof. exact (MK_COMB (@lem5320465) (@lem5320464)). Qed.
Lemma lem5320467 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5320468 : term161 = term162.
Proof. exact (MK_COMB (@lem5320467) (@lem5320466)). Qed.
Lemma lem5320469 : term160 = term162.
Proof. exact (TRANS (@lem5320461) (@lem5320468)). Qed.
Lemma lem5320470 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5320471 : term277 = term278.
Proof. exact (MK_COMB (@lem5320470) (@lem5320469)). Qed.
Lemma lem5320472 : term279 = term280.
Proof. exact (MK_COMB (@lem5320471) (@lem5320458)). Qed.
Lemma lem5320474 (m : nat) : (term281 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5320475 : term280 = term41.
Proof. exact (@lem5320474 term53). Qed.
Lemma lem5320476 : term279 = term41.
Proof. exact (TRANS (@lem5320472) (@lem5320475)). Qed.
Lemma lem5320477 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5320478 : term282 = term254.
Proof. exact (MK_COMB (@lem5320477) (@lem5320476)). Qed.
Lemma lem5320479 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem5320480 : term283 = term200.
Proof. exact (MK_COMB (@lem5320478) (@lem5320479)). Qed.
Lemma lem5320482 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5320483 : term200 = term41.
Proof. exact (@lem5320482 term70). Qed.
Lemma lem5320484 : term283 = term41.
Proof. exact (TRANS (@lem5320480) (@lem5320483)). Qed.
Lemma lem5320486 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5320487 : term256 = term257.
Proof. exact (@lem5320486 term53 term53). Qed.
Lemma lem5320488 : (term88 = (BIT1 0)) = (term258 = term259).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5320489 : term258 = term259.
Proof. exact (EQ_MP (@lem5320488) (@lem940073)). Qed.
Lemma lem5320490 : (term258 = term259) = (term260 = term261).
Proof. exact (@lem1008952 term82 term259). Qed.
Lemma lem5320491 : term260 = term261.
Proof. exact (EQ_MP (@lem5320490) (@lem5320489)). Qed.
Lemma lem5320492 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320493 : term257 = term262.
Proof. exact (MK_COMB (@lem5320492) (@lem5320491)). Qed.
Lemma lem5320494 : term256 = term262.
Proof. exact (TRANS (@lem5320487) (@lem5320493)). Qed.
Lemma lem5320495 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5320496 : term263 = term264.
Proof. exact (MK_COMB (@lem5320495) (@lem5320494)). Qed.
Lemma lem5320498 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5320499 : term264 = term41.
Proof. exact (@lem5320498 term261). Qed.
Lemma lem5320500 : term263 = term41.
Proof. exact (TRANS (@lem5320496) (@lem5320499)). Qed.
Lemma lem5320501 : term41 = term263.
Proof. exact (SYM (@lem5320500)). Qed.
Lemma lem5320502 : term283 = term263.
Proof. exact (TRANS (@lem5320484) (@lem5320501)). Qed.
Lemma lem5320504 : term284 = term192.
Proof. exact (@lem5320449 (@lem5320502)). Qed.
Lemma lem5320506 (x : real) : (term266 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5320507 : term192 = term41.
Proof. exact (@lem5320506 term41). Qed.
Lemma lem5320508 : term284 = term41.
Proof. exact (TRANS (@lem5320504) (@lem5320507)). Qed.
Lemma lem5320509 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5320510 : term285 = term254.
Proof. exact (MK_COMB (@lem5320509) (@lem5320508)). Qed.
Lemma lem5320511 (m : real) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem5320512 (m : real) : (term272 m) = (term268 m).
Proof. exact (MK_COMB (@lem5320510) (@lem5320511 m)). Qed.
Lemma lem5320513 (m : real) : (term271 m) = (term268 m).
Proof. exact (TRANS (@lem5320410 m) (@lem5320512 m)). Qed.
Lemma lem5320514 (m : real) : (term268 m) = term41.
Proof. exact (@lem1982719 m). Qed.
Lemma lem5320515 (m : real) : (term271 m) = term41.
Proof. exact (TRANS (@lem5320513 m) (@lem5320514 m)). Qed.
Lemma lem5320516 (l : real) (m : real) : (term241 l m) = term286.
Proof. exact (MK_COMB (@lem5320409 l) (@lem5320515 m)). Qed.
Lemma lem5320517 (l : real) (m : real) : (term240 l m) = term286.
Proof. exact (TRANS (@lem5320301 l m) (@lem5320516 l m)). Qed.
Lemma lem5320518 : term286 = term41.
Proof. exact (@lem1982721 term41). Qed.
Lemma lem5320519 (l : real) (m : real) : (term240 l m) = term41.
Proof. exact (TRANS (@lem5320517 l m) (@lem5320518)). Qed.
Lemma lem5320520 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5320521 (l : real) (m : real) : (term287 l m) = term288.
Proof. exact (MK_COMB (@lem5320520) (@lem5320519 l m)). Qed.
Lemma lem5320522 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5320523 (l : real) (m : real) : (term239 l m) = term289.
Proof. exact (MK_COMB (@lem5320521 l m) (@lem5320522)). Qed.
Lemma lem5320524 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term289.
Proof. exact (EQ_MP (@lem5320523 l m) (@lem5320300 s t l m h1)). Qed.
Lemma lem5320526 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5320527 : term289 = term290.
Proof. exact (@lem5320526 term41 term41). Qed.
Lemma lem5320529 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5320530 : term41 = term192.
Proof. exact (@lem5320529 (NUMERAL 0)). Qed.
Lemma lem5320532 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5320533 : term41 = term192.
Proof. exact (@lem5320532 (NUMERAL 0)). Qed.
Lemma lem5320534 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5320535 : term193 = term194.
Proof. exact (MK_COMB (@lem5320534) (@lem5320533)). Qed.
Lemma lem5320536 : term290 = term291.
Proof. exact (MK_COMB (@lem5320535) (@lem5320530)). Qed.
Lemma lem5320537 : term292.
Proof. exact (@lem1980255 term41 term76 term41 term76). Qed.
Lemma lem5320539 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320540 : term115 = term116.
Proof. exact (@lem5320539 (NUMERAL 0) term70). Qed.
Lemma lem5320541 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5320542 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5320543 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5320542 h1) (fun h1 : term116 = True => @lem5320541)). Qed.
Lemma lem5320544 : term116 = True.
Proof. exact (EQ_MP (@lem5320543) (@lem5320541)). Qed.
Lemma lem5320545 : term115 = True.
Proof. exact (TRANS (@lem5320540) (@lem5320544)). Qed.
Lemma lem5320546 : True = term115.
Proof. exact (SYM (@lem5320545)). Qed.
Lemma lem5320547 : term115.
Proof. exact (EQ_MP (@lem5320546) (@lem0)). Qed.
Lemma lem5320548 : term293.
Proof. exact (@lem5320537 (@lem5320547)). Qed.
Lemma lem5320550 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320551 : term115 = term116.
Proof. exact (@lem5320550 (NUMERAL 0) term70). Qed.
Lemma lem5320552 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5320553 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5320554 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5320553 h1) (fun h1 : term116 = True => @lem5320552)). Qed.
Lemma lem5320555 : term116 = True.
Proof. exact (EQ_MP (@lem5320554) (@lem5320552)). Qed.
Lemma lem5320556 : term115 = True.
Proof. exact (TRANS (@lem5320551) (@lem5320555)). Qed.
Lemma lem5320557 : True = term115.
Proof. exact (SYM (@lem5320556)). Qed.
Lemma lem5320558 : term115.
Proof. exact (EQ_MP (@lem5320557) (@lem0)). Qed.
Lemma lem5320559 : term291 = term294.
Proof. exact (@lem5320548 (@lem5320558)). Qed.
Lemma lem5320561 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5320562 : term200 = term41.
Proof. exact (@lem5320561 term70). Qed.
Lemma lem5320564 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5320565 : term200 = term41.
Proof. exact (@lem5320564 term70). Qed.
Lemma lem5320566 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5320567 : term201 = term193.
Proof. exact (MK_COMB (@lem5320566) (@lem5320565)). Qed.
Lemma lem5320568 : term294 = term290.
Proof. exact (MK_COMB (@lem5320567) (@lem5320562)). Qed.
Lemma lem5320570 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320571 : term290 = term295.
Proof. exact (@lem5320570 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5320572 : term295 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5320573 : term290 = False.
Proof. exact (TRANS (@lem5320571) (@lem5320572)). Qed.
Lemma lem5320574 : term294 = False.
Proof. exact (TRANS (@lem5320568) (@lem5320573)). Qed.
Lemma lem5320575 : term291 = False.
Proof. exact (TRANS (@lem5320559) (@lem5320574)). Qed.
Lemma lem5320576 : term290 = False.
Proof. exact (TRANS (@lem5320536) (@lem5320575)). Qed.
Lemma lem5320577 : term289 = False.
Proof. exact (TRANS (@lem5320527) (@lem5320576)). Qed.
Lemma lem5320578 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : False.
Proof. exact (EQ_MP (@lem5320577) (@lem5320524 s t l m h1)). Qed.
Lemma lem5320579 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term190 s t l m.
Proof. exact (h1). Qed.
Lemma lem5320580 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term189 t l m.
Proof. exact (proj2 (@lem5320579 s t l m h1)). Qed.
Lemma lem5320582 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term186 l m.
Proof. exact (proj2 (@lem5320580 s t l m h1)). Qed.
Lemma lem5320584 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term141 l m.
Proof. exact (proj2 (@lem5320582 s t l m h1)). Qed.
Lemma lem5320585 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term42 l m.
Proof. exact (proj1 (@lem5320582 s t l m h1)). Qed.
Lemma lem5320587 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5320588 : term191 = term115.
Proof. exact (@lem5320587 term41 term76). Qed.
Lemma lem5320590 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5320591 : term76 = term105.
Proof. exact (@lem5320590 term70). Qed.
Lemma lem5320593 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5320594 : term41 = term192.
Proof. exact (@lem5320593 (NUMERAL 0)). Qed.
Lemma lem5320595 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5320596 : term193 = term194.
Proof. exact (MK_COMB (@lem5320595) (@lem5320594)). Qed.
Lemma lem5320597 : term115 = term195.
Proof. exact (MK_COMB (@lem5320596) (@lem5320591)). Qed.
Lemma lem5320598 : term196.
Proof. exact (@lem1980255 term41 term76 term76 term76). Qed.
Lemma lem5320600 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320601 : term115 = term116.
Proof. exact (@lem5320600 (NUMERAL 0) term70). Qed.
Lemma lem5320602 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5320603 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5320604 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5320603 h1) (fun h1 : term116 = True => @lem5320602)). Qed.
Lemma lem5320605 : term116 = True.
Proof. exact (EQ_MP (@lem5320604) (@lem5320602)). Qed.
Lemma lem5320606 : term115 = True.
Proof. exact (TRANS (@lem5320601) (@lem5320605)). Qed.
Lemma lem5320607 : True = term115.
Proof. exact (SYM (@lem5320606)). Qed.
Lemma lem5320608 : term115.
Proof. exact (EQ_MP (@lem5320607) (@lem0)). Qed.
Lemma lem5320609 : term197.
Proof. exact (@lem5320598 (@lem5320608)). Qed.
Lemma lem5320611 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320612 : term115 = term116.
Proof. exact (@lem5320611 (NUMERAL 0) term70). Qed.
Lemma lem5320613 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5320614 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5320615 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5320614 h1) (fun h1 : term116 = True => @lem5320613)). Qed.
Lemma lem5320616 : term116 = True.
Proof. exact (EQ_MP (@lem5320615) (@lem5320613)). Qed.
Lemma lem5320617 : term115 = True.
Proof. exact (TRANS (@lem5320612) (@lem5320616)). Qed.
Lemma lem5320618 : True = term115.
Proof. exact (SYM (@lem5320617)). Qed.
Lemma lem5320619 : term115.
Proof. exact (EQ_MP (@lem5320618) (@lem0)). Qed.
Lemma lem5320620 : term195 = term198.
Proof. exact (@lem5320609 (@lem5320619)). Qed.
Lemma lem5320622 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5320623 : term163 = term90.
Proof. exact (@lem5320622 term70 term70). Qed.
Lemma lem5320624 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5320625 : term89 = term70.
Proof. exact (EQ_MP (@lem5320624) (@lem940073)). Qed.
Lemma lem5320626 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320627 : term90 = term76.
Proof. exact (MK_COMB (@lem5320626) (@lem5320625)). Qed.
Lemma lem5320628 : term163 = term76.
Proof. exact (TRANS (@lem5320623) (@lem5320627)). Qed.
Lemma lem5320630 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5320631 : term200 = term41.
Proof. exact (@lem5320630 term70). Qed.
Lemma lem5320632 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5320633 : term201 = term193.
Proof. exact (MK_COMB (@lem5320632) (@lem5320631)). Qed.
Lemma lem5320634 : term198 = term115.
Proof. exact (MK_COMB (@lem5320633) (@lem5320628)). Qed.
Lemma lem5320636 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320637 : term115 = term116.
Proof. exact (@lem5320636 (NUMERAL 0) term70). Qed.
Lemma lem5320638 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5320639 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5320640 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5320639 h1) (fun h1 : term116 = True => @lem5320638)). Qed.
Lemma lem5320641 : term116 = True.
Proof. exact (EQ_MP (@lem5320640) (@lem5320638)). Qed.
Lemma lem5320642 : term115 = True.
Proof. exact (TRANS (@lem5320637) (@lem5320641)). Qed.
Lemma lem5320643 : term198 = True.
Proof. exact (TRANS (@lem5320634) (@lem5320642)). Qed.
Lemma lem5320644 : term195 = True.
Proof. exact (TRANS (@lem5320620) (@lem5320643)). Qed.
Lemma lem5320645 : term115 = True.
Proof. exact (TRANS (@lem5320597) (@lem5320644)). Qed.
Lemma lem5320646 : term191 = True.
Proof. exact (TRANS (@lem5320588) (@lem5320645)). Qed.
Lemma lem5320647 : True = term191.
Proof. exact (SYM (@lem5320646)). Qed.
Lemma lem5320648 : term191.
Proof. exact (EQ_MP (@lem5320647) (@lem0)). Qed.
Lemma lem5320649 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term202 l m.
Proof. exact (conj (@lem5320648) (@lem5320584 s t l m h1)). Qed.
Lemma lem5320651 (x : real) (y : real) : term203 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5320652 (l : real) (m : real) : term204 l m.
Proof. exact (@lem5320651 term76 (term138 l m)). Qed.
Lemma lem5320653 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term205 l m.
Proof. exact (@lem5320652 l m (@lem5320649 s t l m h1)). Qed.
Lemma lem5320654 (l : real) (m : real) : (term206 l m) = (term138 l m).
Proof. exact (@lem1982733 (term138 l m)). Qed.
Lemma lem5320655 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5320656 (l : real) (m : real) : (term207 l m) = (term140 l m).
Proof. exact (MK_COMB (@lem5320655) (@lem5320654 l m)). Qed.
Lemma lem5320657 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5320658 (l : real) (m : real) : (term205 l m) = (term141 l m).
Proof. exact (MK_COMB (@lem5320656 l m) (@lem5320657)). Qed.
Lemma lem5320659 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term141 l m.
Proof. exact (EQ_MP (@lem5320658 l m) (@lem5320653 s t l m h1)). Qed.
Lemma lem5320661 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5320662 : term208 = term209.
Proof. exact (@lem5320661 term41 term52). Qed.
Lemma lem5320663 : term52 = term52.
Proof. exact (eq_refl term52). Qed.
Lemma lem5320665 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5320666 : term41 = term192.
Proof. exact (@lem5320665 (NUMERAL 0)). Qed.
Lemma lem5320667 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5320668 : term193 = term194.
Proof. exact (MK_COMB (@lem5320667) (@lem5320666)). Qed.
Lemma lem5320669 : term209 = term210.
Proof. exact (MK_COMB (@lem5320668) (@lem5320663)). Qed.
Lemma lem5320670 : term211.
Proof. exact (@lem1980255 term41 term48 term76 term76). Qed.
Lemma lem5320672 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320673 : term115 = term116.
Proof. exact (@lem5320672 (NUMERAL 0) term70). Qed.
Lemma lem5320674 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5320675 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5320676 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5320675 h1) (fun h1 : term116 = True => @lem5320674)). Qed.
Lemma lem5320677 : term116 = True.
Proof. exact (EQ_MP (@lem5320676) (@lem5320674)). Qed.
Lemma lem5320678 : term115 = True.
Proof. exact (TRANS (@lem5320673) (@lem5320677)). Qed.
Lemma lem5320679 : True = term115.
Proof. exact (SYM (@lem5320678)). Qed.
Lemma lem5320680 : term115.
Proof. exact (EQ_MP (@lem5320679) (@lem0)). Qed.
Lemma lem5320681 : term212.
Proof. exact (@lem5320670 (@lem5320680)). Qed.
Lemma lem5320683 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320684 : term111 = term112.
Proof. exact (@lem5320683 (NUMERAL 0) term53). Qed.
Lemma lem5320685 : term113 = term82.
Proof. exact (@lem912803). Qed.
Lemma lem5320686 (h1 : term113 = term82) : term112 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term82 h1). Qed.
Lemma lem5320687 : (term113 = term82) = (term112 = True).
Proof. exact (prop_ext (fun h1 : term113 = term82 => @lem5320686 h1) (fun h1 : term112 = True => @lem5320685)). Qed.
Lemma lem5320688 : term112 = True.
Proof. exact (EQ_MP (@lem5320687) (@lem5320685)). Qed.
Lemma lem5320689 : term111 = True.
Proof. exact (TRANS (@lem5320684) (@lem5320688)). Qed.
Lemma lem5320690 : True = term111.
Proof. exact (SYM (@lem5320689)). Qed.
Lemma lem5320691 : term111.
Proof. exact (EQ_MP (@lem5320690) (@lem0)). Qed.
Lemma lem5320692 : term210 = term213.
Proof. exact (@lem5320681 (@lem5320691)). Qed.
Lemma lem5320694 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5320695 : term163 = term90.
Proof. exact (@lem5320694 term70 term70). Qed.
Lemma lem5320696 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5320697 : term89 = term70.
Proof. exact (EQ_MP (@lem5320696) (@lem940073)). Qed.
Lemma lem5320698 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320699 : term90 = term76.
Proof. exact (MK_COMB (@lem5320698) (@lem5320697)). Qed.
Lemma lem5320700 : term163 = term76.
Proof. exact (TRANS (@lem5320695) (@lem5320699)). Qed.
Lemma lem5320702 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5320703 : term214 = term41.
Proof. exact (@lem5320702 term53). Qed.
Lemma lem5320704 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5320705 : term215 = term193.
Proof. exact (MK_COMB (@lem5320704) (@lem5320703)). Qed.
Lemma lem5320706 : term213 = term115.
Proof. exact (MK_COMB (@lem5320705) (@lem5320700)). Qed.
Lemma lem5320708 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320709 : term115 = term116.
Proof. exact (@lem5320708 (NUMERAL 0) term70). Qed.
Lemma lem5320710 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5320711 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5320712 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5320711 h1) (fun h1 : term116 = True => @lem5320710)). Qed.
Lemma lem5320713 : term116 = True.
Proof. exact (EQ_MP (@lem5320712) (@lem5320710)). Qed.
Lemma lem5320714 : term115 = True.
Proof. exact (TRANS (@lem5320709) (@lem5320713)). Qed.
Lemma lem5320715 : term213 = True.
Proof. exact (TRANS (@lem5320706) (@lem5320714)). Qed.
Lemma lem5320716 : term210 = True.
Proof. exact (TRANS (@lem5320692) (@lem5320715)). Qed.
Lemma lem5320717 : term209 = True.
Proof. exact (TRANS (@lem5320669) (@lem5320716)). Qed.
Lemma lem5320718 : term208 = True.
Proof. exact (TRANS (@lem5320662) (@lem5320717)). Qed.
Lemma lem5320719 : True = term208.
Proof. exact (SYM (@lem5320718)). Qed.
Lemma lem5320720 : term208.
Proof. exact (EQ_MP (@lem5320719) (@lem0)). Qed.
Lemma lem5320721 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term216 l m.
Proof. exact (conj (@lem5320720) (@lem5320585 s t l m h1)). Qed.
Lemma lem5320723 (x : real) (y : real) : term217 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5320724 (l : real) (m : real) : term218 l m.
Proof. exact (@lem5320723 term52 (term38 l m)). Qed.
Lemma lem5320725 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term219 l m.
Proof. exact (@lem5320724 l m (@lem5320721 s t l m h1)). Qed.
Lemma lem5320726 (l : real) (m : real) : (term220 l m) = (term221 l m).
Proof. exact (@lem1982781 l term52 (term150 m)). Qed.
Lemma lem5320727 (m : real) : (term222 m) = (term223 m).
Proof. exact (@lem1982749 term52 term64 m). Qed.
Lemma lem5320729 (x : nat) : (term67 x) = (term68 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5320730 : term64 = term69.
Proof. exact (@lem5320729 term70). Qed.
Lemma lem5320733 : term137 = term137.
Proof. exact (eq_refl term137). Qed.
Lemma lem5320734 : term224 = term225.
Proof. exact (MK_COMB (@lem5320733) (@lem5320730)). Qed.
Lemma lem5320735 : term225 = term226.
Proof. exact (@lem1981613 term76 term64 term48 term76). Qed.
Lemma lem5320737 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5320738 : term131 = term132.
Proof. exact (@lem5320737 term53 term70). Qed.
Lemma lem5320739 : term133 = term82.
Proof. exact (@lem996237 term82). Qed.
Lemma lem5320740 : (term133 = term82) = (term134 = term53).
Proof. exact (@lem1007663 term82 (BIT1 0) term82). Qed.
Lemma lem5320741 : term134 = term53.
Proof. exact (EQ_MP (@lem5320740) (@lem5320739)). Qed.
Lemma lem5320742 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320743 : term132 = term48.
Proof. exact (MK_COMB (@lem5320742) (@lem5320741)). Qed.
Lemma lem5320744 : term131 = term48.
Proof. exact (TRANS (@lem5320738) (@lem5320743)). Qed.
Lemma lem5320746 (m : nat) (n : nat) : (term227 m n) = (term85 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem5320747 : term228 = term87.
Proof. exact (@lem5320746 term70 term70). Qed.
Lemma lem5320748 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5320749 : term89 = term70.
Proof. exact (EQ_MP (@lem5320748) (@lem940073)). Qed.
Lemma lem5320750 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320751 : term90 = term76.
Proof. exact (MK_COMB (@lem5320750) (@lem5320749)). Qed.
Lemma lem5320752 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5320753 : term87 = term64.
Proof. exact (MK_COMB (@lem5320752) (@lem5320751)). Qed.
Lemma lem5320754 : term228 = term64.
Proof. exact (TRANS (@lem5320747) (@lem5320753)). Qed.
Lemma lem5320755 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5320756 : term229 = term92.
Proof. exact (MK_COMB (@lem5320755) (@lem5320754)). Qed.
Lemma lem5320757 : term226 = term93.
Proof. exact (MK_COMB (@lem5320756) (@lem5320744)). Qed.
Lemma lem5320758 : term225 = term93.
Proof. exact (TRANS (@lem5320735) (@lem5320757)). Qed.
Lemma lem5320761 : term224 = term93.
Proof. exact (TRANS (@lem5320734) (@lem5320758)). Qed.
Lemma lem5320762 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5320763 : term230 = term95.
Proof. exact (MK_COMB (@lem5320762) (@lem5320761)). Qed.
Lemma lem5320764 (m : real) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem5320765 (m : real) : (term223 m) = (term96 m).
Proof. exact (MK_COMB (@lem5320763) (@lem5320764 m)). Qed.
Lemma lem5320766 (m : real) : (term222 m) = (term96 m).
Proof. exact (TRANS (@lem5320727 m) (@lem5320765 m)). Qed.
Lemma lem5320769 (l : real) : (term231 l) = (term231 l).
Proof. exact (eq_refl (term231 l)). Qed.
Lemma lem5320770 (l : real) (m : real) : (term221 l m) = (term232 l m).
Proof. exact (MK_COMB (@lem5320769 l) (@lem5320766 m)). Qed.
Lemma lem5320771 (l : real) (m : real) : (term220 l m) = (term232 l m).
Proof. exact (TRANS (@lem5320726 l m) (@lem5320770 l m)). Qed.
Lemma lem5320772 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5320773 (l : real) (m : real) : (term233 l m) = (term234 l m).
Proof. exact (MK_COMB (@lem5320772) (@lem5320771 l m)). Qed.
Lemma lem5320774 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5320775 (l : real) (m : real) : (term219 l m) = (term235 l m).
Proof. exact (MK_COMB (@lem5320773 l m) (@lem5320774)). Qed.
Lemma lem5320776 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term235 l m.
Proof. exact (EQ_MP (@lem5320775 l m) (@lem5320725 s t l m h1)). Qed.
Lemma lem5320777 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term236 l m.
Proof. exact (conj (@lem5320776 s t l m h1) (@lem5320659 s t l m h1)). Qed.
Lemma lem5320779 (x : real) (y : real) : term237 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5320780 (l : real) (m : real) : term238 l m.
Proof. exact (@lem5320779 (term232 l m) (term138 l m)). Qed.
Lemma lem5320781 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term239 l m.
Proof. exact (@lem5320780 l m (@lem5320777 s t l m h1)). Qed.
Lemma lem5320782 (l : real) (m : real) : (term240 l m) = (term241 l m).
Proof. exact (@lem1982753 (term63 l) (term96 l) (term96 m) (term63 m)). Qed.
Lemma lem5320783 (l : real) : (term242 l) = (term243 l).
Proof. exact (@lem1982711 term52 term93 l). Qed.
Lemma lem5320789 : term244.
Proof. exact (@lem1981473 term76 term48 term64 term48 term41 term76). Qed.
Lemma lem5320791 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320792 : term111 = term112.
Proof. exact (@lem5320791 (NUMERAL 0) term53). Qed.
Lemma lem5320793 : term113 = term82.
Proof. exact (@lem912803). Qed.
Lemma lem5320794 (h1 : term113 = term82) : term112 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term82 h1). Qed.
Lemma lem5320795 : (term113 = term82) = (term112 = True).
Proof. exact (prop_ext (fun h1 : term113 = term82 => @lem5320794 h1) (fun h1 : term112 = True => @lem5320793)). Qed.
Lemma lem5320796 : term112 = True.
Proof. exact (EQ_MP (@lem5320795) (@lem5320793)). Qed.
Lemma lem5320797 : term111 = True.
Proof. exact (TRANS (@lem5320792) (@lem5320796)). Qed.
Lemma lem5320798 : True = term111.
Proof. exact (SYM (@lem5320797)). Qed.
Lemma lem5320799 : term111.
Proof. exact (EQ_MP (@lem5320798) (@lem0)). Qed.
Lemma lem5320800 : term245.
Proof. exact (@lem5320789 (@lem5320799)). Qed.
Lemma lem5320802 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320803 : term111 = term112.
Proof. exact (@lem5320802 (NUMERAL 0) term53). Qed.
Lemma lem5320804 : term113 = term82.
Proof. exact (@lem912803). Qed.
Lemma lem5320805 (h1 : term113 = term82) : term112 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term82 h1). Qed.
Lemma lem5320806 : (term113 = term82) = (term112 = True).
Proof. exact (prop_ext (fun h1 : term113 = term82 => @lem5320805 h1) (fun h1 : term112 = True => @lem5320804)). Qed.
Lemma lem5320807 : term112 = True.
Proof. exact (EQ_MP (@lem5320806) (@lem5320804)). Qed.
Lemma lem5320808 : term111 = True.
Proof. exact (TRANS (@lem5320803) (@lem5320807)). Qed.
Lemma lem5320809 : True = term111.
Proof. exact (SYM (@lem5320808)). Qed.
Lemma lem5320810 : term111.
Proof. exact (EQ_MP (@lem5320809) (@lem0)). Qed.
Lemma lem5320811 : term246.
Proof. exact (@lem5320800 (@lem5320810)). Qed.
Lemma lem5320813 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320814 : term115 = term116.
Proof. exact (@lem5320813 (NUMERAL 0) term70). Qed.
Lemma lem5320815 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5320816 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5320817 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5320816 h1) (fun h1 : term116 = True => @lem5320815)). Qed.
Lemma lem5320818 : term116 = True.
Proof. exact (EQ_MP (@lem5320817) (@lem5320815)). Qed.
Lemma lem5320819 : term115 = True.
Proof. exact (TRANS (@lem5320814) (@lem5320818)). Qed.
Lemma lem5320820 : True = term115.
Proof. exact (SYM (@lem5320819)). Qed.
Lemma lem5320821 : term115.
Proof. exact (EQ_MP (@lem5320820) (@lem0)). Qed.
Lemma lem5320822 : term247.
Proof. exact (@lem5320811 (@lem5320821)). Qed.
Lemma lem5320824 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5320825 : term160 = term161.
Proof. exact (@lem5320824 term70 term53). Qed.
Lemma lem5320826 : term81 = term82.
Proof. exact (@lem996238 term82). Qed.
Lemma lem5320827 : (term81 = term82) = (term83 = term53).
Proof. exact (@lem1007663 (BIT1 0) term82 term82). Qed.
Lemma lem5320828 : term83 = term53.
Proof. exact (EQ_MP (@lem5320827) (@lem5320826)). Qed.
Lemma lem5320829 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320830 : term80 = term48.
Proof. exact (MK_COMB (@lem5320829) (@lem5320828)). Qed.
Lemma lem5320831 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5320832 : term161 = term162.
Proof. exact (MK_COMB (@lem5320831) (@lem5320830)). Qed.
Lemma lem5320833 : term160 = term162.
Proof. exact (TRANS (@lem5320825) (@lem5320832)). Qed.
Lemma lem5320835 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5320836 : term79 = term80.
Proof. exact (@lem5320835 term70 term53). Qed.
Lemma lem5320837 : term81 = term82.
Proof. exact (@lem996238 term82). Qed.
Lemma lem5320838 : (term81 = term82) = (term83 = term53).
Proof. exact (@lem1007663 (BIT1 0) term82 term82). Qed.
Lemma lem5320839 : term83 = term53.
Proof. exact (EQ_MP (@lem5320838) (@lem5320837)). Qed.
Lemma lem5320840 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320841 : term80 = term48.
Proof. exact (MK_COMB (@lem5320840) (@lem5320839)). Qed.
Lemma lem5320842 : term79 = term48.
Proof. exact (TRANS (@lem5320836) (@lem5320841)). Qed.
Lemma lem5320843 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5320844 : term248 = term249.
Proof. exact (MK_COMB (@lem5320843) (@lem5320842)). Qed.
Lemma lem5320845 : term250 = term251.
Proof. exact (MK_COMB (@lem5320844) (@lem5320833)). Qed.
Lemma lem5320847 (m : nat) : (term252 m) = term41.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5320848 : term251 = term41.
Proof. exact (@lem5320847 term53). Qed.
Lemma lem5320849 : term250 = term41.
Proof. exact (TRANS (@lem5320845) (@lem5320848)). Qed.
Lemma lem5320850 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5320851 : term253 = term254.
Proof. exact (MK_COMB (@lem5320850) (@lem5320849)). Qed.
Lemma lem5320852 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem5320853 : term255 = term200.
Proof. exact (MK_COMB (@lem5320851) (@lem5320852)). Qed.
Lemma lem5320855 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5320856 : term200 = term41.
Proof. exact (@lem5320855 term70). Qed.
Lemma lem5320857 : term255 = term41.
Proof. exact (TRANS (@lem5320853) (@lem5320856)). Qed.
Lemma lem5320859 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5320860 : term256 = term257.
Proof. exact (@lem5320859 term53 term53). Qed.
Lemma lem5320861 : (term88 = (BIT1 0)) = (term258 = term259).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5320862 : term258 = term259.
Proof. exact (EQ_MP (@lem5320861) (@lem940073)). Qed.
Lemma lem5320863 : (term258 = term259) = (term260 = term261).
Proof. exact (@lem1008952 term82 term259). Qed.
Lemma lem5320864 : term260 = term261.
Proof. exact (EQ_MP (@lem5320863) (@lem5320862)). Qed.
Lemma lem5320865 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320866 : term257 = term262.
Proof. exact (MK_COMB (@lem5320865) (@lem5320864)). Qed.
Lemma lem5320867 : term256 = term262.
Proof. exact (TRANS (@lem5320860) (@lem5320866)). Qed.
Lemma lem5320868 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5320869 : term263 = term264.
Proof. exact (MK_COMB (@lem5320868) (@lem5320867)). Qed.
Lemma lem5320871 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5320872 : term264 = term41.
Proof. exact (@lem5320871 term261). Qed.
Lemma lem5320873 : term263 = term41.
Proof. exact (TRANS (@lem5320869) (@lem5320872)). Qed.
Lemma lem5320874 : term41 = term263.
Proof. exact (SYM (@lem5320873)). Qed.
Lemma lem5320875 : term255 = term263.
Proof. exact (TRANS (@lem5320857) (@lem5320874)). Qed.
Lemma lem5320877 : term265 = term192.
Proof. exact (@lem5320822 (@lem5320875)). Qed.
Lemma lem5320879 (x : real) : (term266 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5320880 : term192 = term41.
Proof. exact (@lem5320879 term41). Qed.
Lemma lem5320881 : term265 = term41.
Proof. exact (TRANS (@lem5320877) (@lem5320880)). Qed.
Lemma lem5320882 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5320883 : term267 = term254.
Proof. exact (MK_COMB (@lem5320882) (@lem5320881)). Qed.
Lemma lem5320884 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5320885 (l : real) : (term243 l) = (term268 l).
Proof. exact (MK_COMB (@lem5320883) (@lem5320884 l)). Qed.
Lemma lem5320886 (l : real) : (term242 l) = (term268 l).
Proof. exact (TRANS (@lem5320783 l) (@lem5320885 l)). Qed.
Lemma lem5320887 (l : real) : (term268 l) = term41.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5320888 (l : real) : (term242 l) = term41.
Proof. exact (TRANS (@lem5320886 l) (@lem5320887 l)). Qed.
Lemma lem5320889 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5320890 (l : real) : (term269 l) = term270.
Proof. exact (MK_COMB (@lem5320889) (@lem5320888 l)). Qed.
Lemma lem5320891 (m : real) : (term271 m) = (term272 m).
Proof. exact (@lem1982711 term93 term52 m). Qed.
Lemma lem5320897 : term273.
Proof. exact (@lem1981473 term64 term48 term76 term48 term41 term76). Qed.
Lemma lem5320899 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320900 : term111 = term112.
Proof. exact (@lem5320899 (NUMERAL 0) term53). Qed.
Lemma lem5320901 : term113 = term82.
Proof. exact (@lem912803). Qed.
Lemma lem5320902 (h1 : term113 = term82) : term112 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term82 h1). Qed.
Lemma lem5320903 : (term113 = term82) = (term112 = True).
Proof. exact (prop_ext (fun h1 : term113 = term82 => @lem5320902 h1) (fun h1 : term112 = True => @lem5320901)). Qed.
Lemma lem5320904 : term112 = True.
Proof. exact (EQ_MP (@lem5320903) (@lem5320901)). Qed.
Lemma lem5320905 : term111 = True.
Proof. exact (TRANS (@lem5320900) (@lem5320904)). Qed.
Lemma lem5320906 : True = term111.
Proof. exact (SYM (@lem5320905)). Qed.
Lemma lem5320907 : term111.
Proof. exact (EQ_MP (@lem5320906) (@lem0)). Qed.
Lemma lem5320908 : term274.
Proof. exact (@lem5320897 (@lem5320907)). Qed.
Lemma lem5320910 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320911 : term111 = term112.
Proof. exact (@lem5320910 (NUMERAL 0) term53). Qed.
Lemma lem5320912 : term113 = term82.
Proof. exact (@lem912803). Qed.
Lemma lem5320913 (h1 : term113 = term82) : term112 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term82 h1). Qed.
Lemma lem5320914 : (term113 = term82) = (term112 = True).
Proof. exact (prop_ext (fun h1 : term113 = term82 => @lem5320913 h1) (fun h1 : term112 = True => @lem5320912)). Qed.
Lemma lem5320915 : term112 = True.
Proof. exact (EQ_MP (@lem5320914) (@lem5320912)). Qed.
Lemma lem5320916 : term111 = True.
Proof. exact (TRANS (@lem5320911) (@lem5320915)). Qed.
Lemma lem5320917 : True = term111.
Proof. exact (SYM (@lem5320916)). Qed.
Lemma lem5320918 : term111.
Proof. exact (EQ_MP (@lem5320917) (@lem0)). Qed.
Lemma lem5320919 : term275.
Proof. exact (@lem5320908 (@lem5320918)). Qed.
Lemma lem5320921 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5320922 : term115 = term116.
Proof. exact (@lem5320921 (NUMERAL 0) term70). Qed.
Lemma lem5320923 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5320924 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5320925 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5320924 h1) (fun h1 : term116 = True => @lem5320923)). Qed.
Lemma lem5320926 : term116 = True.
Proof. exact (EQ_MP (@lem5320925) (@lem5320923)). Qed.
Lemma lem5320927 : term115 = True.
Proof. exact (TRANS (@lem5320922) (@lem5320926)). Qed.
Lemma lem5320928 : True = term115.
Proof. exact (SYM (@lem5320927)). Qed.
Lemma lem5320929 : term115.
Proof. exact (EQ_MP (@lem5320928) (@lem0)). Qed.
Lemma lem5320930 : term276.
Proof. exact (@lem5320919 (@lem5320929)). Qed.
Lemma lem5320932 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5320933 : term79 = term80.
Proof. exact (@lem5320932 term70 term53). Qed.
Lemma lem5320934 : term81 = term82.
Proof. exact (@lem996238 term82). Qed.
Lemma lem5320935 : (term81 = term82) = (term83 = term53).
Proof. exact (@lem1007663 (BIT1 0) term82 term82). Qed.
Lemma lem5320936 : term83 = term53.
Proof. exact (EQ_MP (@lem5320935) (@lem5320934)). Qed.
Lemma lem5320937 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320938 : term80 = term48.
Proof. exact (MK_COMB (@lem5320937) (@lem5320936)). Qed.
Lemma lem5320939 : term79 = term48.
Proof. exact (TRANS (@lem5320933) (@lem5320938)). Qed.
Lemma lem5320941 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5320942 : term160 = term161.
Proof. exact (@lem5320941 term70 term53). Qed.
Lemma lem5320943 : term81 = term82.
Proof. exact (@lem996238 term82). Qed.
Lemma lem5320944 : (term81 = term82) = (term83 = term53).
Proof. exact (@lem1007663 (BIT1 0) term82 term82). Qed.
Lemma lem5320945 : term83 = term53.
Proof. exact (EQ_MP (@lem5320944) (@lem5320943)). Qed.
Lemma lem5320946 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320947 : term80 = term48.
Proof. exact (MK_COMB (@lem5320946) (@lem5320945)). Qed.
Lemma lem5320948 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5320949 : term161 = term162.
Proof. exact (MK_COMB (@lem5320948) (@lem5320947)). Qed.
Lemma lem5320950 : term160 = term162.
Proof. exact (TRANS (@lem5320942) (@lem5320949)). Qed.
Lemma lem5320951 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5320952 : term277 = term278.
Proof. exact (MK_COMB (@lem5320951) (@lem5320950)). Qed.
Lemma lem5320953 : term279 = term280.
Proof. exact (MK_COMB (@lem5320952) (@lem5320939)). Qed.
Lemma lem5320955 (m : nat) : (term281 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5320956 : term280 = term41.
Proof. exact (@lem5320955 term53). Qed.
Lemma lem5320957 : term279 = term41.
Proof. exact (TRANS (@lem5320953) (@lem5320956)). Qed.
Lemma lem5320958 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5320959 : term282 = term254.
Proof. exact (MK_COMB (@lem5320958) (@lem5320957)). Qed.
Lemma lem5320960 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem5320961 : term283 = term200.
Proof. exact (MK_COMB (@lem5320959) (@lem5320960)). Qed.
Lemma lem5320963 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5320964 : term200 = term41.
Proof. exact (@lem5320963 term70). Qed.
Lemma lem5320965 : term283 = term41.
Proof. exact (TRANS (@lem5320961) (@lem5320964)). Qed.
Lemma lem5320967 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5320968 : term256 = term257.
Proof. exact (@lem5320967 term53 term53). Qed.
Lemma lem5320969 : (term88 = (BIT1 0)) = (term258 = term259).
Proof. exact (@lem940532 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5320970 : term258 = term259.
Proof. exact (EQ_MP (@lem5320969) (@lem940073)). Qed.
Lemma lem5320971 : (term258 = term259) = (term260 = term261).
Proof. exact (@lem1008952 term82 term259). Qed.
Lemma lem5320972 : term260 = term261.
Proof. exact (EQ_MP (@lem5320971) (@lem5320970)). Qed.
Lemma lem5320973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5320974 : term257 = term262.
Proof. exact (MK_COMB (@lem5320973) (@lem5320972)). Qed.
Lemma lem5320975 : term256 = term262.
Proof. exact (TRANS (@lem5320968) (@lem5320974)). Qed.
Lemma lem5320976 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5320977 : term263 = term264.
Proof. exact (MK_COMB (@lem5320976) (@lem5320975)). Qed.
Lemma lem5320979 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5320980 : term264 = term41.
Proof. exact (@lem5320979 term261). Qed.
Lemma lem5320981 : term263 = term41.
Proof. exact (TRANS (@lem5320977) (@lem5320980)). Qed.
Lemma lem5320982 : term41 = term263.
Proof. exact (SYM (@lem5320981)). Qed.
Lemma lem5320983 : term283 = term263.
Proof. exact (TRANS (@lem5320965) (@lem5320982)). Qed.
Lemma lem5320985 : term284 = term192.
Proof. exact (@lem5320930 (@lem5320983)). Qed.
Lemma lem5320987 (x : real) : (term266 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5320988 : term192 = term41.
Proof. exact (@lem5320987 term41). Qed.
Lemma lem5320989 : term284 = term41.
Proof. exact (TRANS (@lem5320985) (@lem5320988)). Qed.
Lemma lem5320990 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5320991 : term285 = term254.
Proof. exact (MK_COMB (@lem5320990) (@lem5320989)). Qed.
Lemma lem5320992 (m : real) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem5320993 (m : real) : (term272 m) = (term268 m).
Proof. exact (MK_COMB (@lem5320991) (@lem5320992 m)). Qed.
Lemma lem5320994 (m : real) : (term271 m) = (term268 m).
Proof. exact (TRANS (@lem5320891 m) (@lem5320993 m)). Qed.
Lemma lem5320995 (m : real) : (term268 m) = term41.
Proof. exact (@lem1982719 m). Qed.
Lemma lem5320996 (m : real) : (term271 m) = term41.
Proof. exact (TRANS (@lem5320994 m) (@lem5320995 m)). Qed.
Lemma lem5320997 (l : real) (m : real) : (term241 l m) = term286.
Proof. exact (MK_COMB (@lem5320890 l) (@lem5320996 m)). Qed.
Lemma lem5320998 (l : real) (m : real) : (term240 l m) = term286.
Proof. exact (TRANS (@lem5320782 l m) (@lem5320997 l m)). Qed.
Lemma lem5320999 : term286 = term41.
Proof. exact (@lem1982721 term41). Qed.
Lemma lem5321000 (l : real) (m : real) : (term240 l m) = term41.
Proof. exact (TRANS (@lem5320998 l m) (@lem5320999)). Qed.
Lemma lem5321001 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5321002 (l : real) (m : real) : (term287 l m) = term288.
Proof. exact (MK_COMB (@lem5321001) (@lem5321000 l m)). Qed.
Lemma lem5321003 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5321004 (l : real) (m : real) : (term239 l m) = term289.
Proof. exact (MK_COMB (@lem5321002 l m) (@lem5321003)). Qed.
Lemma lem5321005 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : term289.
Proof. exact (EQ_MP (@lem5321004 l m) (@lem5320781 s t l m h1)). Qed.
Lemma lem5321007 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5321008 : term289 = term290.
Proof. exact (@lem5321007 term41 term41). Qed.
Lemma lem5321010 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5321011 : term41 = term192.
Proof. exact (@lem5321010 (NUMERAL 0)). Qed.
Lemma lem5321013 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5321014 : term41 = term192.
Proof. exact (@lem5321013 (NUMERAL 0)). Qed.
Lemma lem5321015 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5321016 : term193 = term194.
Proof. exact (MK_COMB (@lem5321015) (@lem5321014)). Qed.
Lemma lem5321017 : term290 = term291.
Proof. exact (MK_COMB (@lem5321016) (@lem5321011)). Qed.
Lemma lem5321018 : term292.
Proof. exact (@lem1980255 term41 term76 term41 term76). Qed.
Lemma lem5321020 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5321021 : term115 = term116.
Proof. exact (@lem5321020 (NUMERAL 0) term70). Qed.
Lemma lem5321022 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5321023 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5321024 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5321023 h1) (fun h1 : term116 = True => @lem5321022)). Qed.
Lemma lem5321025 : term116 = True.
Proof. exact (EQ_MP (@lem5321024) (@lem5321022)). Qed.
Lemma lem5321026 : term115 = True.
Proof. exact (TRANS (@lem5321021) (@lem5321025)). Qed.
Lemma lem5321027 : True = term115.
Proof. exact (SYM (@lem5321026)). Qed.
Lemma lem5321028 : term115.
Proof. exact (EQ_MP (@lem5321027) (@lem0)). Qed.
Lemma lem5321029 : term293.
Proof. exact (@lem5321018 (@lem5321028)). Qed.
Lemma lem5321031 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5321032 : term115 = term116.
Proof. exact (@lem5321031 (NUMERAL 0) term70). Qed.
Lemma lem5321033 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5321034 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5321035 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5321034 h1) (fun h1 : term116 = True => @lem5321033)). Qed.
Lemma lem5321036 : term116 = True.
Proof. exact (EQ_MP (@lem5321035) (@lem5321033)). Qed.
Lemma lem5321037 : term115 = True.
Proof. exact (TRANS (@lem5321032) (@lem5321036)). Qed.
Lemma lem5321038 : True = term115.
Proof. exact (SYM (@lem5321037)). Qed.
Lemma lem5321039 : term115.
Proof. exact (EQ_MP (@lem5321038) (@lem0)). Qed.
Lemma lem5321040 : term291 = term294.
Proof. exact (@lem5321029 (@lem5321039)). Qed.
Lemma lem5321042 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5321043 : term200 = term41.
Proof. exact (@lem5321042 term70). Qed.
Lemma lem5321045 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5321046 : term200 = term41.
Proof. exact (@lem5321045 term70). Qed.
Lemma lem5321047 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5321048 : term201 = term193.
Proof. exact (MK_COMB (@lem5321047) (@lem5321046)). Qed.
Lemma lem5321049 : term294 = term290.
Proof. exact (MK_COMB (@lem5321048) (@lem5321043)). Qed.
Lemma lem5321051 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5321052 : term290 = term295.
Proof. exact (@lem5321051 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5321053 : term295 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5321054 : term290 = False.
Proof. exact (TRANS (@lem5321052) (@lem5321053)). Qed.
Lemma lem5321055 : term294 = False.
Proof. exact (TRANS (@lem5321049) (@lem5321054)). Qed.
Lemma lem5321056 : term291 = False.
Proof. exact (TRANS (@lem5321040) (@lem5321055)). Qed.
Lemma lem5321057 : term290 = False.
Proof. exact (TRANS (@lem5321017) (@lem5321056)). Qed.
Lemma lem5321058 : term289 = False.
Proof. exact (TRANS (@lem5321008) (@lem5321057)). Qed.
Lemma lem5321059 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term190 s t l m) : False.
Proof. exact (EQ_MP (@lem5321058) (@lem5321005 s t l m h1)). Qed.
Lemma lem5321060 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term188 s t l m) : False.
Proof. exact (or_elim (@lem5320097 s t l m h1) (fun h0 : term190 s t l m => @lem5320578 s t l m h0) (fun h0 : term190 s t l m => @lem5321059 s t l m h0)). Qed.
Lemma lem5321062 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term188 s t l m) : term188 s t l m.
Proof. exact (h1). Qed.
Lemma lem5321063 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term188 s t l m) : (term188 s t l m) = False.
Proof. exact (prop_ext (fun h2 : term188 s t l m => @lem5321060 s t l m h1) (fun h2 : False => @lem5321062 s t l m h1)). Qed.
Lemma lem5321064 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term188 s t l m) : False.
Proof. exact (EQ_MP (@lem5321063 s t l m h1) (@lem5321062 s t l m h1)). Qed.
Lemma lem5321065 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (h1 : term35 s t m l) : term35 s t m l.
Proof. exact (h1). Qed.
Lemma lem5321066 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (h1 : term35 s t m l) : term188 s t l m.
Proof. exact (EQ_MP (@lem5320087 s t l m) (@lem5321065 s t m l h1)). Qed.
Lemma lem5321067 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (h1 : term35 s t m l) : (term188 s t l m) = False.
Proof. exact (prop_ext (fun h2 : term188 s t l m => @lem5321064 s t l m h2) (fun h2 : False => @lem5321066 s t m l h1)). Qed.
Lemma lem5321068 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) (h1 : term35 s t m l) : False.
Proof. exact (EQ_MP (@lem5321067 s t m l h1) (@lem5321066 s t m l h1)). Qed.
Lemma lem5321069 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) : term296 s t m l.
Proof. exact (fun h0 : term35 s t m l => @lem5321068 s t m l h0). Qed.
Lemma lem5321070 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) : term297 s t m l.
Proof. exact (@lem1386578 (term298 s t m l)). Qed.
Lemma lem5321073 (s : real -> Prop) (t : real -> Prop) (m : real) (l : real) : term298 s t m l.
Proof. exact (@lem5321070 s t m l (@lem5321069 s t m l)). Qed.
Lemma lem5321074 (t : real -> Prop) (m : real) (l : real) (s : real -> Prop) (h1 : term12 s) : term36 t m l.
Proof. exact (@lem5321073 s t m l (@lem5319452 s h1)). Qed.
Lemma lem5321075 (m : real) (l : real) (s : real -> Prop) (t : real -> Prop) (h1 : term12 s) (h2 : term12 t) : term32 m l.
Proof. exact (@lem5321074 t m l s h1 (@lem5319484 t h2)). Qed.
Lemma lem5321076 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 l m) : term27 m l.
Proof. exact (@lem5321075 m l s t h1 h2 (@lem5319495 l m h3)). Qed.
Lemma lem5321077 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 l m) : term17 m l.
Proof. exact (ex_intro (term299 m l) (term45 l m) (@lem5321076 s t l m h1 h2 h3)). Qed.
Lemma lem5321078 (c : real) (m : real) (t : real -> Prop) (h1 : term14 m t) : term300 m t c.
Proof. exact (@lem5319485 m t h1 c). Qed.
Lemma lem5321079 (m : real) (t : real -> Prop) (c : real) : (term300 m t c) = (term301 m t c).
Proof. exact (eq_refl (term300 m t c)). Qed.
Lemma lem5321080 (c : real) (m : real) (t : real -> Prop) (h1 : term14 m t) : term301 m t c.
Proof. exact (EQ_MP (@lem5321079 m t c) (@lem5321078 c m t h1)). Qed.
Lemma lem5321081 {A : Type'} (P : A -> Prop) : term302 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem5321082 {A : Type'} (P : A -> Prop) : (term302 A P) = ((term303 A P) = (term304 A P)).
Proof. exact (eq_refl (term302 A P)). Qed.
Lemma lem5321132 (m : real) (c : real) : (real_lt m c) = ((real_lt m c) = True).
Proof. exact (@lem7 (real_lt m c)). Qed.
Lemma lem5321137 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem5321138 (m : real) (t : real -> Prop) (c : real) : (term305 m t c) = (term306 m t c).
Proof. exact (@lem5321137 (term301 m t c)). Qed.
Lemma lem5321142 (m : real) (c : real) (h1 : real_lt m c) : (real_lt m c) = True.
Proof. exact (EQ_MP (@lem5321132 m c) (@lem5319499 m c h1)). Qed.
Lemma lem5321143 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5321144 (m : real) (c : real) (h1 : real_lt m c) : (term307 m c) = (imp True).
Proof. exact (MK_COMB (@lem5321143) (@lem5321142 m c h1)). Qed.
Lemma lem5321151 (t : real -> Prop) (c : real) : (term308 t c) = (term308 t c).
Proof. exact (eq_refl (term308 t c)). Qed.
Lemma lem5321152 (t : real -> Prop) (m : real) (c : real) (h1 : real_lt m c) : (term301 m t c) = (term309 t c).
Proof. exact (MK_COMB (@lem5321144 m c h1) (@lem5321151 t c)). Qed.
Lemma lem5321154 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5321155 (t : real -> Prop) (c : real) : (term309 t c) = (term308 t c).
Proof. exact (@lem5321154 (term308 t c)). Qed.
Lemma lem5321162 (t : real -> Prop) (m : real) (c : real) (h1 : real_lt m c) : (term301 m t c) = (term308 t c).
Proof. exact (TRANS (@lem5321152 t m c h1) (@lem5321155 t c)). Qed.
Lemma lem5321163 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5321164 (t : real -> Prop) (m : real) (c : real) (h1 : real_lt m c) : (term306 m t c) = (term310 t c).
Proof. exact (MK_COMB (@lem5321163) (@lem5321162 t m c h1)). Qed.
Lemma lem5321166 {A : Type'} (P : A -> Prop) : (term303 A P) = (term304 A P).
Proof. exact (EQ_MP (@lem5321082 A P) (@lem5321081 A P)). Qed.
Lemma lem5321167 (P : real -> Prop) : (term311 P) = (term312 P).
Proof. exact (@lem5321166 real P). Qed.
Lemma lem5321168 (t : real -> Prop) (c : real) : (term313 t c) = (term314 t c).
Proof. exact (@lem5321167 (term315 t c)). Qed.
Lemma lem5321169 (t : real -> Prop) (x : real) (c : real) : (term316 t c x) = (term317 t x c).
Proof. exact (eq_refl (term316 t c x)). Qed.
Lemma lem5321170 (t : real -> Prop) (c : real) : (term318 t c) = (term315 t c).
Proof. exact (fun_ext (fun x : real => @lem5321169 t x c)). Qed.
Lemma lem5321171 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5321172 (t : real -> Prop) (c : real) : (term319 t c) = (term308 t c).
Proof. exact (MK_COMB (@lem5321171) (@lem5321170 t c)). Qed.
Lemma lem5321173 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5321174 (t : real -> Prop) (c : real) : (term313 t c) = (term310 t c).
Proof. exact (MK_COMB (@lem5321173) (@lem5321172 t c)). Qed.
Lemma lem5321175 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5321176 (t : real -> Prop) (c : real) : (term320 t c) = (term321 t c).
Proof. exact (MK_COMB (@lem5321175) (@lem5321174 t c)). Qed.
Lemma lem5321177 (t : real -> Prop) (x : real) (c : real) : (term316 t c x) = (term317 t x c).
Proof. exact (eq_refl (term316 t c x)). Qed.
Lemma lem5321178 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5321179 (t : real -> Prop) (x : real) (c : real) : (term322 t c x) = (term323 t x c).
Proof. exact (MK_COMB (@lem5321178) (@lem5321177 t x c)). Qed.
Lemma lem5321180 (t : real -> Prop) (c : real) : (term324 t c) = (term325 t c).
Proof. exact (fun_ext (fun x : real => @lem5321179 t x c)). Qed.
Lemma lem5321181 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5321182 (t : real -> Prop) (c : real) : (term314 t c) = (term326 t c).
Proof. exact (MK_COMB (@lem5321181) (@lem5321180 t c)). Qed.
Lemma lem5321183 (t : real -> Prop) (c : real) : ((term313 t c) = (term314 t c)) = ((term310 t c) = (term326 t c)).
Proof. exact (MK_COMB (@lem5321176 t c) (@lem5321182 t c)). Qed.
Lemma lem5321184 (t : real -> Prop) (c : real) : (term310 t c) = (term326 t c).
Proof. exact (EQ_MP (@lem5321183 t c) (@lem5321168 t c)). Qed.
Lemma lem5321191 (t : real -> Prop) (m : real) (c : real) (h1 : real_lt m c) : (term306 m t c) = (term326 t c).
Proof. exact (TRANS (@lem5321164 t m c h1) (@lem5321184 t c)). Qed.
Lemma lem5321192 (t : real -> Prop) (m : real) (c : real) (h1 : real_lt m c) : (term305 m t c) = (term326 t c).
Proof. exact (TRANS (@lem5321138 m t c) (@lem5321191 t m c h1)). Qed.
Lemma lem5321193 (t : real -> Prop) (m : real) (c : real) (h1 : real_lt m c) : (term326 t c) = (term305 m t c).
Proof. exact (SYM (@lem5321192 t m c h1)). Qed.
Lemma lem5321196 (t : real -> Prop) (x : real) (c : real) (h1 : term317 t x c) : term317 t x c.
Proof. exact (h1). Qed.
Lemma lem5321197 (x : real) (c : real) (h1 : real_lt x c) : real_lt x c.
Proof. exact (h1). Qed.
Lemma lem5321198 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (h1). Qed.
Lemma lem5321199 (s : real -> Prop) (x : real) (h1 : term327 s x) : term327 s x.
Proof. exact (h1). Qed.
Lemma lem5321200 (s : real -> Prop) (y : real) (x : real) (h1 : term328 s y x) : term328 s y x.
Proof. exact (h1). Qed.
Lemma lem5321201 (y : real) (x : real) (h1 : real_le y x) : real_le y x.
Proof. exact (h1). Qed.
Lemma lem5321202 (y : real) (s : real -> Prop) (h1 : @IN real y s) : @IN real y s.
Proof. exact (h1). Qed.
Lemma lem5321214 (p : Prop) : p = (term15 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5321215 (s : real -> Prop) (x : real) : (term327 s x) = (term329 s x).
Proof. exact (@lem5321214 (term327 s x)). Qed.
Lemma lem5321216 (s : real -> Prop) (x : real) : (term329 s x) = (term327 s x).
Proof. exact (SYM (@lem5321215 s x)). Qed.
Lemma lem5321217 (s : real -> Prop) (x : real) (h1 : term330 s x) : term330 s x.
Proof. exact (h1). Qed.
Lemma lem5321220 (x : real) (t : real -> Prop) (s : real -> Prop) (h1 : term331 x t s) : term331 x t s.
Proof. exact (h1). Qed.
Lemma lem5321221 (x : real) (t : real -> Prop) (s : real -> Prop) : term332 x t s.
Proof. exact (fun h0 : term331 x t s => @lem5321220 x t s h0). Qed.
Lemma lem5321222 (x : real) (t : real -> Prop) (s : real -> Prop) (h1 : term332 x t s) : term332 x t s.
Proof. exact (h1). Qed.
Lemma lem5321223 (x : real) (t : real -> Prop) (s : real -> Prop) (h1 : term331 x t s) : term331 x t s.
Proof. exact (h1). Qed.
Lemma lem5321224 (x : real) (t : real -> Prop) (s : real -> Prop) (h1 : term331 x t s) (h2 : term332 x t s) : term331 x t s.
Proof. exact (@lem5321222 x t s h2 (@lem5321223 x t s h1)). Qed.
Lemma lem5321225 (x : real) (t : real -> Prop) (s : real -> Prop) (h1 : term331 x t s) : term333 x t s.
Proof. exact (fun h0 : term332 x t s => @lem5321224 x t s h1 h0). Qed.
Lemma lem5321226 (x : real) (t : real -> Prop) (s : real -> Prop) (h1 : term332 x t s) : term332 x t s.
Proof. exact (h1). Qed.
Lemma lem5321227 (x : real) (t : real -> Prop) (s : real -> Prop) (h1 : term331 x t s) (h2 : term332 x t s) : term331 x t s.
Proof. exact (@lem5321225 x t s h1 (@lem5321226 x t s h2)). Qed.
Lemma lem5321228 (x : real) (t : real -> Prop) (s : real -> Prop) (h1 : term332 x t s) : term332 x t s.
Proof. exact (fun h0 : term331 x t s => @lem5321227 x t s h0 h1). Qed.
Lemma lem5321229 (x : real) (t : real -> Prop) (s : real -> Prop) : term334 x t s.
Proof. exact (fun h0 : term332 x t s => @lem5321228 x t s h0). Qed.
Lemma lem5321232 (x : real) (t : real -> Prop) (s : real -> Prop) : term332 x t s.
Proof. exact (@lem5321229 x t s (@lem5321221 x t s)). Qed.
Lemma lem5321300 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5321301 (t : real -> Prop) (s : real -> Prop) : (term335 t s) = (term336 t s).
Proof. exact (@lem5321300 (term10 t s)). Qed.
Lemma lem5321358 (x : real) (t : real -> Prop) : (term337 x t) = (term337 x t).
Proof. exact (eq_refl (term337 x t)). Qed.
Lemma lem5321359 (x : real) (t : real -> Prop) (s : real -> Prop) : (term338 x t s) = (term339 x t s).
Proof. exact (MK_COMB (@lem5321358 x t) (@lem5321301 t s)). Qed.
Lemma lem5321362 (s : real -> Prop) (x : real) : (term340 s x) = (term340 s x).
Proof. exact (eq_refl (term340 s x)). Qed.
Lemma lem5321363 (x : real) (t : real -> Prop) (s : real -> Prop) : (term331 x t s) = (term341 x t s).
Proof. exact (MK_COMB (@lem5321362 s x) (@lem5321359 x t s)). Qed.
Lemma lem5321366 (t : real -> Prop) (s : real -> Prop) : (term342 t s) = (term343 t s).
Proof. exact (fun_ext (fun x : real => @lem5321363 x t s)). Qed.
Lemma lem5321367 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5321368 (t : real -> Prop) (s : real -> Prop) : (term344 t s) = (term345 t s).
Proof. exact (MK_COMB (@lem5321367) (@lem5321366 t s)). Qed.
Lemma lem5321373 (s : real -> Prop) : (term346 s) = (term347 s).
Proof. exact (fun_ext (fun t : real -> Prop => @lem5321368 t s)). Qed.
Lemma lem5321374 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5321375 (s : real -> Prop) : (term348 s) = (term349 s).
Proof. exact (MK_COMB (@lem5321374) (@lem5321373 s)). Qed.
Lemma lem5321380 : term350 = term351.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5321375 s)). Qed.
Lemma lem5321381 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5321390 : term352 = term353.
Proof. exact (MK_COMB (@lem5321381) (@lem5321380)). Qed.
Lemma lem5321395 (s : real -> Prop) (x : real) (y : real) : (term328 s x y) = (term328 s x y).
Proof. exact (eq_refl (term328 s x y)). Qed.
Lemma lem5321396 (s : real -> Prop) (y : real) : (term354 s y) = (term354 s y).
Proof. exact (fun_ext (fun x : real => @lem5321395 s x y)). Qed.
Lemma lem5321397 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5321398 (s : real -> Prop) (y : real) : (term327 s y) = (term327 s y).
Proof. exact (MK_COMB (@lem5321397) (@lem5321396 s y)). Qed.
Lemma lem5321401 (y : real) (t : real -> Prop) : (term337 y t) = (term337 y t).
Proof. exact (eq_refl (term337 y t)). Qed.
Lemma lem5321402 (t : real -> Prop) (s : real -> Prop) (y : real) : (term355 t s y) = (term355 t s y).
Proof. exact (MK_COMB (@lem5321401 y t) (@lem5321398 s y)). Qed.
Lemma lem5321403 (t : real -> Prop) (s : real -> Prop) : (term356 t s) = (term356 t s).
Proof. exact (fun_ext (fun y : real => @lem5321402 t s y)). Qed.
Lemma lem5321404 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5321405 (t : real -> Prop) (s : real -> Prop) : (term10 t s) = (term10 t s).
Proof. exact (MK_COMB (@lem5321404) (@lem5321403 t s)). Qed.
Lemma lem5321406 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5321407 (t : real -> Prop) (s : real -> Prop) : (term336 t s) = (term336 t s).
Proof. exact (MK_COMB (@lem5321406) (@lem5321405 t s)). Qed.
Lemma lem5321410 (x : real) (t : real -> Prop) : (term337 x t) = (term337 x t).
Proof. exact (eq_refl (term337 x t)). Qed.
Lemma lem5321411 (x : real) (t : real -> Prop) (s : real -> Prop) : (term339 x t s) = (term339 x t s).
Proof. exact (MK_COMB (@lem5321410 x t) (@lem5321407 t s)). Qed.
Lemma lem5321416 (s : real -> Prop) (y : real) (x : real) : (term328 s y x) = (term328 s y x).
Proof. exact (eq_refl (term328 s y x)). Qed.
Lemma lem5321417 (s : real -> Prop) (x : real) : (term354 s x) = (term354 s x).
Proof. exact (fun_ext (fun y : real => @lem5321416 s y x)). Qed.
Lemma lem5321418 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5321419 (s : real -> Prop) (x : real) : (term327 s x) = (term327 s x).
Proof. exact (MK_COMB (@lem5321418) (@lem5321417 s x)). Qed.
Lemma lem5321420 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5321421 (s : real -> Prop) (x : real) : (term330 s x) = (term330 s x).
Proof. exact (MK_COMB (@lem5321420) (@lem5321419 s x)). Qed.
Lemma lem5321422 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5321423 (s : real -> Prop) (x : real) : (term340 s x) = (term340 s x).
Proof. exact (MK_COMB (@lem5321422) (@lem5321421 s x)). Qed.
Lemma lem5321424 (x : real) (t : real -> Prop) (s : real -> Prop) : (term341 x t s) = (term341 x t s).
Proof. exact (MK_COMB (@lem5321423 s x) (@lem5321411 x t s)). Qed.
Lemma lem5321425 (t : real -> Prop) (s : real -> Prop) : (term343 t s) = (term343 t s).
Proof. exact (fun_ext (fun x : real => @lem5321424 x t s)). Qed.
Lemma lem5321426 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5321427 (t : real -> Prop) (s : real -> Prop) : (term345 t s) = (term345 t s).
Proof. exact (MK_COMB (@lem5321426) (@lem5321425 t s)). Qed.
Lemma lem5321428 (s : real -> Prop) : (term347 s) = (term347 s).
Proof. exact (fun_ext (fun t : real -> Prop => @lem5321427 t s)). Qed.
Lemma lem5321429 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5321430 (s : real -> Prop) : (term349 s) = (term349 s).
Proof. exact (MK_COMB (@lem5321429) (@lem5321428 s)). Qed.
Lemma lem5321431 : term351 = term351.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5321430 s)). Qed.
Lemma lem5321432 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5321433 : term353 = term353.
Proof. exact (MK_COMB (@lem5321432) (@lem5321431)). Qed.
Lemma lem5321482 : term352 = term353.
Proof. exact (TRANS (@lem5321390) (@lem5321433)). Qed.
Lemma lem5321483 : term353 = term352.
Proof. exact (SYM (@lem5321482)). Qed.
Lemma lem5321484 (s : real -> Prop) (x : real) (h1 : term330 s x) : term330 s x.
Proof. exact (h1). Qed.
Lemma lem5321486 (t : real -> Prop) (s : real -> Prop) (h1 : term10 t s) : term10 t s.
Proof. exact (h1). Qed.
Lemma lem5321493 (s : real -> Prop) (y : real) (x : real) : (term357 s y x) = (term358 s y x).
Proof. exact (@lem17045 (@IN real y s) (real_le y x)). Qed.
Lemma lem5321494 (P : real -> Prop) : (term359 P) = (term312 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5321495 (s : real -> Prop) (x : real) : (term330 s x) = (term360 s x).
Proof. exact (@lem5321494 (term354 s x)). Qed.
Lemma lem5321496 (s : real -> Prop) (y : real) (x : real) : (term361 s x y) = (term328 s y x).
Proof. exact (eq_refl (term361 s x y)). Qed.
Lemma lem5321497 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5321498 (s : real -> Prop) (y : real) (x : real) : (term362 s x y) = (term357 s y x).
Proof. exact (MK_COMB (@lem5321497) (@lem5321496 s y x)). Qed.
Lemma lem5321499 (s : real -> Prop) (y : real) (x : real) : (term362 s x y) = (term358 s y x).
Proof. exact (TRANS (@lem5321498 s y x) (@lem5321493 s y x)). Qed.
Lemma lem5321500 (s : real -> Prop) (x : real) : (term363 s x) = (term364 s x).
Proof. exact (fun_ext (fun y : real => @lem5321499 s y x)). Qed.
Lemma lem5321501 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5321502 (s : real -> Prop) (x : real) : (term360 s x) = (term365 s x).
Proof. exact (MK_COMB (@lem5321501) (@lem5321500 s x)). Qed.
Lemma lem5321555 (s : real -> Prop) (x : real) : (term330 s x) = (term365 s x).
Proof. exact (TRANS (@lem5321495 s x) (@lem5321502 s x)). Qed.
Lemma lem5321556 (s : real -> Prop) (x : real) (h1 : term330 s x) : term365 s x.
Proof. exact (EQ_MP (@lem5321555 s x) (@lem5321484 s x h1)). Qed.
Lemma lem5321562 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (h1). Qed.
Lemma lem5321568 (s : real -> Prop) (x : real) (y : real) : (term328 s x y) = (term328 s x y).
Proof. exact (eq_refl (term328 s x y)). Qed.
Lemma lem5321569 (s : real -> Prop) (y : real) : (term354 s y) = (term354 s y).
Proof. exact (fun_ext (fun x : real => @lem5321568 s x y)). Qed.
Lemma lem5321570 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5321571 (s : real -> Prop) (y : real) : (term327 s y) = (term327 s y).
Proof. exact (MK_COMB (@lem5321570) (@lem5321569 s y)). Qed.
Lemma lem5321573 (y : real) (t : real -> Prop) : (term366 y t) = (term366 y t).
Proof. exact (eq_refl (term366 y t)). Qed.
Lemma lem5321574 (t : real -> Prop) (s : real -> Prop) (y : real) : (term367 t s y) = (term367 t s y).
Proof. exact (MK_COMB (@lem5321573 y t) (@lem5321571 s y)). Qed.
Lemma lem5321575 (t : real -> Prop) (s : real -> Prop) (y : real) : (term355 t s y) = (term367 t s y).
Proof. exact (@lem17265 (@IN real y t) (term327 s y)). Qed.
Lemma lem5321576 (t : real -> Prop) (s : real -> Prop) (y : real) : (term355 t s y) = (term367 t s y).
Proof. exact (TRANS (@lem5321575 t s y) (@lem5321574 t s y)). Qed.
Lemma lem5321577 (t : real -> Prop) (s : real -> Prop) : (term356 t s) = (term368 t s).
Proof. exact (fun_ext (fun y : real => @lem5321576 t s y)). Qed.
Lemma lem5321578 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5321579 (t : real -> Prop) (s : real -> Prop) : (term10 t s) = (term369 t s).
Proof. exact (MK_COMB (@lem5321578) (@lem5321577 t s)). Qed.
Lemma lem5321678 {A : Type'} (P : Prop) (Q : A -> Prop) : (term370 A P Q) = (term371 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5321679 (P : Prop) (Q : real -> Prop) : (term372 P Q) = (term373 P Q).
Proof. exact (@lem5321678 real P Q). Qed.
Lemma lem5321680 (t : real -> Prop) (s : real -> Prop) (y : real) : (term374 t s y) = (term375 t s y).
Proof. exact (@lem5321679 (term376 y t) (term354 s y)). Qed.
Lemma lem5321681 (s : real -> Prop) (x : real) (y : real) : (term361 s y x) = (term328 s x y).
Proof. exact (eq_refl (term361 s y x)). Qed.
Lemma lem5321682 (s : real -> Prop) (y : real) : (term377 s y) = (term354 s y).
Proof. exact (fun_ext (fun x : real => @lem5321681 s x y)). Qed.
Lemma lem5321683 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5321684 (s : real -> Prop) (y : real) : (term378 s y) = (term327 s y).
Proof. exact (MK_COMB (@lem5321683) (@lem5321682 s y)). Qed.
Lemma lem5321685 (y : real) (t : real -> Prop) : (term366 y t) = (term366 y t).
Proof. exact (eq_refl (term366 y t)). Qed.
Lemma lem5321686 (t : real -> Prop) (s : real -> Prop) (y : real) : (term374 t s y) = (term367 t s y).
Proof. exact (MK_COMB (@lem5321685 y t) (@lem5321684 s y)). Qed.
Lemma lem5321687 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5321688 (t : real -> Prop) (s : real -> Prop) (y : real) : (term379 t s y) = (term380 t s y).
Proof. exact (MK_COMB (@lem5321687) (@lem5321686 t s y)). Qed.
Lemma lem5321689 (s : real -> Prop) (x : real) (y : real) : (term361 s y x) = (term328 s x y).
Proof. exact (eq_refl (term361 s y x)). Qed.
Lemma lem5321690 (y : real) (t : real -> Prop) : (term366 y t) = (term366 y t).
Proof. exact (eq_refl (term366 y t)). Qed.
Lemma lem5321691 (t : real -> Prop) (s : real -> Prop) (x : real) (y : real) : (term381 t s y x) = (term382 t s x y).
Proof. exact (MK_COMB (@lem5321690 y t) (@lem5321689 s x y)). Qed.
Lemma lem5321692 (t : real -> Prop) (s : real -> Prop) (y : real) : (term383 t s y) = (term384 t s y).
Proof. exact (fun_ext (fun x : real => @lem5321691 t s x y)). Qed.
Lemma lem5321693 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5321694 (t : real -> Prop) (s : real -> Prop) (y : real) : (term375 t s y) = (term385 t s y).
Proof. exact (MK_COMB (@lem5321693) (@lem5321692 t s y)). Qed.
Lemma lem5321695 (t : real -> Prop) (s : real -> Prop) (y : real) : ((term374 t s y) = (term375 t s y)) = ((term367 t s y) = (term385 t s y)).
Proof. exact (MK_COMB (@lem5321688 t s y) (@lem5321694 t s y)). Qed.
Lemma lem5321696 (t : real -> Prop) (s : real -> Prop) (y : real) : (term367 t s y) = (term385 t s y).
Proof. exact (EQ_MP (@lem5321695 t s y) (@lem5321680 t s y)). Qed.
Lemma lem5321697 (t : real -> Prop) (s : real -> Prop) : (term368 t s) = (term386 t s).
Proof. exact (fun_ext (fun y : real => @lem5321696 t s y)). Qed.
Lemma lem5321698 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5321699 (t : real -> Prop) (s : real -> Prop) : (term369 t s) = (term387 t s).
Proof. exact (MK_COMB (@lem5321698) (@lem5321697 t s)). Qed.
Lemma lem5321701 {A B : Type'} (P : type1413 A B) : (term388 A B P) = (term389 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5321702 (P : type1626) : (term390 P) = (term391 P).
Proof. exact (@lem5321701 real real P). Qed.
Lemma lem5321703 (t : real -> Prop) (s : real -> Prop) : (term392 t s) = (term393 t s).
Proof. exact (@lem5321702 (term394 t s)). Qed.
Lemma lem5321704 (t : real -> Prop) (s : real -> Prop) (y : real) : (term395 t s y) = (term384 t s y).
Proof. exact (eq_refl (term395 t s y)). Qed.
Lemma lem5321705 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5321706 (t : real -> Prop) (s : real -> Prop) (y : real) (x : real) : (term396 t s y x) = (term397 t s y x).
Proof. exact (MK_COMB (@lem5321704 t s y) (@lem5321705 x)). Qed.
Lemma lem5321707 (t : real -> Prop) (s : real -> Prop) (x : real) (y : real) : (term397 t s y x) = (term382 t s x y).
Proof. exact (eq_refl (term397 t s y x)). Qed.
Lemma lem5321708 (t : real -> Prop) (s : real -> Prop) (x : real) (y : real) : (term396 t s y x) = (term382 t s x y).
Proof. exact (TRANS (@lem5321706 t s y x) (@lem5321707 t s x y)). Qed.
Lemma lem5321709 (t : real -> Prop) (s : real -> Prop) (y : real) : (term398 t s y) = (term384 t s y).
Proof. exact (fun_ext (fun x : real => @lem5321708 t s x y)). Qed.
Lemma lem5321710 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5321711 (t : real -> Prop) (s : real -> Prop) (y : real) : (term399 t s y) = (term385 t s y).
Proof. exact (MK_COMB (@lem5321710) (@lem5321709 t s y)). Qed.
Lemma lem5321712 (t : real -> Prop) (s : real -> Prop) : (term400 t s) = (term386 t s).
Proof. exact (fun_ext (fun y : real => @lem5321711 t s y)). Qed.
Lemma lem5321713 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5321714 (t : real -> Prop) (s : real -> Prop) : (term392 t s) = (term387 t s).
Proof. exact (MK_COMB (@lem5321713) (@lem5321712 t s)). Qed.
Lemma lem5321715 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5321716 (t : real -> Prop) (s : real -> Prop) : (term401 t s) = (term402 t s).
Proof. exact (MK_COMB (@lem5321715) (@lem5321714 t s)). Qed.
Lemma lem5321717 (t : real -> Prop) (s : real -> Prop) (y : real) : (term395 t s y) = (term384 t s y).
Proof. exact (eq_refl (term395 t s y)). Qed.
Lemma lem5321718 (x : real -> real) (y : real) : (x y) = (x y).
Proof. exact (eq_refl (x y)). Qed.
Lemma lem5321719 (t : real -> Prop) (s : real -> Prop) (x : real -> real) (y : real) : (term403 t s x y) = (term404 t s x y).
Proof. exact (MK_COMB (@lem5321717 t s y) (@lem5321718 x y)). Qed.
Lemma lem5321720 (t : real -> Prop) (s : real -> Prop) (x : real -> real) (y : real) : (term404 t s x y) = (term405 t s x y).
Proof. exact (eq_refl (term404 t s x y)). Qed.
Lemma lem5321721 (t : real -> Prop) (s : real -> Prop) (x : real -> real) (y : real) : (term403 t s x y) = (term405 t s x y).
Proof. exact (TRANS (@lem5321719 t s x y) (@lem5321720 t s x y)). Qed.
Lemma lem5321722 (t : real -> Prop) (s : real -> Prop) (x : real -> real) : (term406 t s x) = (term407 t s x).
Proof. exact (fun_ext (fun y : real => @lem5321721 t s x y)). Qed.
Lemma lem5321723 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5321724 (t : real -> Prop) (s : real -> Prop) (x : real -> real) : (term408 t s x) = (term409 t s x).
Proof. exact (MK_COMB (@lem5321723) (@lem5321722 t s x)). Qed.
Lemma lem5321725 (t : real -> Prop) (s : real -> Prop) : (term410 t s) = (term411 t s).
Proof. exact (fun_ext (fun x : real -> real => @lem5321724 t s x)). Qed.
Lemma lem5321726 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5321727 (t : real -> Prop) (s : real -> Prop) : (term393 t s) = (term412 t s).
Proof. exact (MK_COMB (@lem5321726) (@lem5321725 t s)). Qed.
Lemma lem5321728 (t : real -> Prop) (s : real -> Prop) : ((term392 t s) = (term393 t s)) = ((term387 t s) = (term412 t s)).
Proof. exact (MK_COMB (@lem5321716 t s) (@lem5321727 t s)). Qed.
Lemma lem5321729 (t : real -> Prop) (s : real -> Prop) : (term387 t s) = (term412 t s).
Proof. exact (EQ_MP (@lem5321728 t s) (@lem5321703 t s)). Qed.
Lemma lem5321731 (t : real -> Prop) (s : real -> Prop) : (term369 t s) = (term412 t s).
Proof. exact (TRANS (@lem5321699 t s) (@lem5321729 t s)). Qed.
Lemma lem5321732 (t : real -> Prop) (s : real -> Prop) : (term10 t s) = (term412 t s).
Proof. exact (TRANS (@lem5321579 t s) (@lem5321731 t s)). Qed.
Lemma lem5321733 (t : real -> Prop) (s : real -> Prop) (h1 : term10 t s) : term412 t s.
Proof. exact (EQ_MP (@lem5321732 t s) (@lem5321486 t s h1)). Qed.
Lemma lem5321734 (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term409 t s x') : term409 t s x'.
Proof. exact (h1). Qed.
Lemma lem5321751 (s : real -> Prop) (y : real) (x : real) : (term358 s y x) = (term358 s y x).
Proof. exact (eq_refl (term358 s y x)). Qed.
Lemma lem5321752 (s : real -> Prop) (x : real) : (term364 s x) = (term364 s x).
Proof. exact (fun_ext (fun y : real => @lem5321751 s y x)). Qed.
Lemma lem5321753 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5321754 (s : real -> Prop) (x : real) : (term365 s x) = (term365 s x).
Proof. exact (MK_COMB (@lem5321753) (@lem5321752 s x)). Qed.
Lemma lem5321755 (s : real -> Prop) (x : real) (h1 : term330 s x) : term365 s x.
Proof. exact (EQ_MP (@lem5321754 s x) (@lem5321556 s x h1)). Qed.
Lemma lem5321761 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (h1). Qed.
Lemma lem5321788 (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (y : real) : (term405 t s x' y) = (term405 t s x' y).
Proof. exact (eq_refl (term405 t s x' y)). Qed.
Lemma lem5321789 (t : real -> Prop) (s : real -> Prop) (x' : real -> real) : (term407 t s x') = (term407 t s x').
Proof. exact (fun_ext (fun y : real => @lem5321788 t s x' y)). Qed.
Lemma lem5321790 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5321791 (t : real -> Prop) (s : real -> Prop) (x' : real -> real) : (term409 t s x') = (term409 t s x').
Proof. exact (MK_COMB (@lem5321790) (@lem5321789 t s x')). Qed.
Lemma lem5321792 (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term409 t s x') : term409 t s x'.
Proof. exact (EQ_MP (@lem5321791 t s x') (@lem5321734 t s x' h1)). Qed.
Lemma lem5321800 (s : real -> Prop) (y : real) (x : real) : (term358 s y x) = (term358 s y x).
Proof. exact (eq_refl (term358 s y x)). Qed.
Lemma lem5321801 (s : real -> Prop) (x : real) : (term364 s x) = (term364 s x).
Proof. exact (fun_ext (fun y : real => @lem5321800 s y x)). Qed.
Lemma lem5321802 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5321804 (s : real -> Prop) (x : real) : (term365 s x) = (term365 s x).
Proof. exact (MK_COMB (@lem5321802) (@lem5321801 s x)). Qed.
Lemma lem5321805 (s : real -> Prop) (x : real) (h1 : term330 s x) : term365 s x.
Proof. exact (EQ_MP (@lem5321804 s x) (@lem5321755 s x h1)). Qed.
Lemma lem5321809 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (h1). Qed.
Lemma lem5321827 (s : real -> Prop) (t : real -> Prop) (x' : real -> real) (y : real) : (term405 t s x' y) = (term413 s t x' y).
Proof. exact (@lem19490 (term414 x' y s) (term376 y t) (term415 x' y)). Qed.
Lemma lem5321828 (s : real -> Prop) (t : real -> Prop) (x' : real -> real) : (term407 t s x') = (term416 s t x').
Proof. exact (fun_ext (fun y : real => @lem5321827 s t x' y)). Qed.
Lemma lem5321829 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5321831 (s : real -> Prop) (t : real -> Prop) (x' : real -> real) : (term409 t s x') = (term417 s t x').
Proof. exact (MK_COMB (@lem5321829) (@lem5321828 s t x')). Qed.
Lemma lem5321832 (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term409 t s x') : term417 s t x'.
Proof. exact (EQ_MP (@lem5321831 s t x') (@lem5321792 t s x' h1)). Qed.
Lemma lem5321833 (_69688 : real) (s : real -> Prop) (x : real) (h1 : term330 s x) : term418 s x _69688.
Proof. exact (@lem5321805 s x h1 _69688). Qed.
Lemma lem5321834 (s : real -> Prop) (_69688 : real) (x : real) : (term418 s x _69688) = (term358 s _69688 x).
Proof. exact (eq_refl (term418 s x _69688)). Qed.
Lemma lem5321836 (_69689 : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term409 t s x') : term419 s t x' _69689.
Proof. exact (@lem5321832 t s x' h1 _69689). Qed.
Lemma lem5321837 (s : real -> Prop) (t : real -> Prop) (x' : real -> real) (_69689 : real) : (term419 s t x' _69689) = (term413 s t x' _69689).
Proof. exact (eq_refl (term419 s t x' _69689)). Qed.
Lemma lem5321838 (_69689 : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term409 t s x') : term413 s t x' _69689.
Proof. exact (EQ_MP (@lem5321837 s t x' _69689) (@lem5321836 _69689 t s x' h1)). Qed.
Lemma lem5321846 (_69688 : real) (s : real -> Prop) (x : real) (h1 : term330 s x) : term358 s _69688 x.
Proof. exact (EQ_MP (@lem5321834 s _69688 x) (@lem5321833 _69688 s x h1)). Qed.
Lemma lem5321848 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (h1). Qed.
Lemma lem5321854 (_69689 : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term409 t s x') : term420 t x' _69689 s.
Proof. exact (proj1 (@lem5321838 _69689 t s x' h1)). Qed.
Lemma lem5321860 (_69689 : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term409 t s x') : term421 t x' _69689.
Proof. exact (proj2 (@lem5321838 _69689 t s x' h1)). Qed.
Lemma lem5321862 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (h1). Qed.
Lemma lem5321863 (x : real) (t : real -> Prop) (h1 : @IN real x t) : term422 x t.
Proof. exact (fun h0 : term376 x t => @lem5321862 x t h1). Qed.
Lemma lem5321865 (p : Prop) : (term423 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5321866 (x : real) (t : real -> Prop) : (term422 x t) = (@IN real x t).
Proof. exact (@lem5321865 (@IN real x t)). Qed.
Lemma lem5321867 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (EQ_MP (@lem5321866 x t) (@lem5321863 x t h1)). Qed.
Lemma lem5321873 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5321874 (x' : real -> real) (s : real -> Prop) (_69689 : real) (t : real -> Prop) : (term420 t x' _69689 s) = (term424 x' s _69689 t).
Proof. exact (@lem5321873 (term414 x' _69689 s) (term376 _69689 t)). Qed.
Lemma lem5321880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5321881 (x' : real -> real) (s : real -> Prop) (_69689 : real) (t : real -> Prop) : (term425 t x' _69689 s) = (term426 x' s _69689 t).
Proof. exact (MK_COMB (@lem5321880) (@lem5321874 x' s _69689 t)). Qed.
Lemma lem5321887 (x' : real -> real) (s : real -> Prop) (_69689 : real) (t : real -> Prop) : (term424 x' s _69689 t) = (term424 x' s _69689 t).
Proof. exact (eq_refl (term424 x' s _69689 t)). Qed.
Lemma lem5321888 (x' : real -> real) (s : real -> Prop) (_69689 : real) (t : real -> Prop) : ((term420 t x' _69689 s) = (term424 x' s _69689 t)) = ((term424 x' s _69689 t) = (term424 x' s _69689 t)).
Proof. exact (MK_COMB (@lem5321881 x' s _69689 t) (@lem5321887 x' s _69689 t)). Qed.
Lemma lem5321890 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5321891 (x : Prop) : (x = x) = True.
Proof. exact (@lem5321890 Prop x). Qed.
Lemma lem5321892 (x' : real -> real) (s : real -> Prop) (_69689 : real) (t : real -> Prop) : ((term424 x' s _69689 t) = (term424 x' s _69689 t)) = True.
Proof. exact (@lem5321891 (term424 x' s _69689 t)). Qed.
Lemma lem5321893 (x' : real -> real) (s : real -> Prop) (_69689 : real) (t : real -> Prop) : ((term420 t x' _69689 s) = (term424 x' s _69689 t)) = True.
Proof. exact (TRANS (@lem5321888 x' s _69689 t) (@lem5321892 x' s _69689 t)). Qed.
Lemma lem5321894 (x' : real -> real) (s : real -> Prop) (_69689 : real) (t : real -> Prop) : True = ((term420 t x' _69689 s) = (term424 x' s _69689 t)).
Proof. exact (SYM (@lem5321893 x' s _69689 t)). Qed.
Lemma lem5321895 (x' : real -> real) (s : real -> Prop) (_69689 : real) (t : real -> Prop) : (term420 t x' _69689 s) = (term424 x' s _69689 t).
Proof. exact (EQ_MP (@lem5321894 x' s _69689 t) (@lem0)). Qed.
Lemma lem5321896 (_69689 : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term409 t s x') : term424 x' s _69689 t.
Proof. exact (EQ_MP (@lem5321895 x' s _69689 t) (@lem5321854 _69689 t s x' h1)). Qed.
Lemma lem5321898 (b : Prop) (a : Prop) : (a \/ b) = (term427 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5321899 (t : real -> Prop) (x' : real -> real) (_69689 : real) (s : real -> Prop) : (term424 x' s _69689 t) = (term428 t x' _69689 s).
Proof. exact (@lem5321898 (term376 _69689 t) (term414 x' _69689 s)). Qed.
Lemma lem5321901 (a : Prop) : (term429 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5321902 (_69689 : real) (t : real -> Prop) : (term430 _69689 t) = (@IN real _69689 t).
Proof. exact (@lem5321901 (@IN real _69689 t)). Qed.
Lemma lem5321903 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5321904 (_69689 : real) (t : real -> Prop) : (term431 _69689 t) = (term337 _69689 t).
Proof. exact (MK_COMB (@lem5321903) (@lem5321902 _69689 t)). Qed.
Lemma lem5321905 (x' : real -> real) (_69689 : real) (s : real -> Prop) : (term414 x' _69689 s) = (term414 x' _69689 s).
Proof. exact (eq_refl (term414 x' _69689 s)). Qed.
Lemma lem5321906 (t : real -> Prop) (x' : real -> real) (_69689 : real) (s : real -> Prop) : (term428 t x' _69689 s) = (term432 t x' _69689 s).
Proof. exact (MK_COMB (@lem5321904 _69689 t) (@lem5321905 x' _69689 s)). Qed.
Lemma lem5321907 (t : real -> Prop) (x' : real -> real) (_69689 : real) (s : real -> Prop) : (term424 x' s _69689 t) = (term432 t x' _69689 s).
Proof. exact (TRANS (@lem5321899 t x' _69689 s) (@lem5321906 t x' _69689 s)). Qed.
Lemma lem5321910 (_69689 : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term409 t s x') : term432 t x' _69689 s.
Proof. exact (EQ_MP (@lem5321907 t x' _69689 s) (@lem5321896 _69689 t s x' h1)). Qed.
Lemma lem5321911 (x : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term409 t s x') : term432 t x' x s.
Proof. exact (@lem5321910 x t s x' h1). Qed.
Lemma lem5321914 (s : real -> Prop) (x' : real -> real) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : @IN real x t) : term414 x' x s.
Proof. exact (@lem5321911 x t s x' h1 (@lem5321867 x t h2)). Qed.
Lemma lem5321915 (s : real -> Prop) (x' : real -> real) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : @IN real x t) : term433 x' x s.
Proof. exact (fun h0 : term434 x' x s => @lem5321914 s x' x t h1 h2). Qed.
Lemma lem5321917 (p : Prop) : (term423 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5321918 (x' : real -> real) (x : real) (s : real -> Prop) : (term433 x' x s) = (term414 x' x s).
Proof. exact (@lem5321917 (term414 x' x s)). Qed.
Lemma lem5321919 (s : real -> Prop) (x' : real -> real) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : @IN real x t) : term414 x' x s.
Proof. exact (EQ_MP (@lem5321918 x' x s) (@lem5321915 s x' x t h1 h2)). Qed.
Lemma lem5321921 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (h1). Qed.
Lemma lem5321922 (x : real) (t : real -> Prop) (h1 : @IN real x t) : term422 x t.
Proof. exact (fun h0 : term376 x t => @lem5321921 x t h1). Qed.
Lemma lem5321924 (p : Prop) : (term423 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5321925 (x : real) (t : real -> Prop) : (term422 x t) = (@IN real x t).
Proof. exact (@lem5321924 (@IN real x t)). Qed.
Lemma lem5321926 (x : real) (t : real -> Prop) (h1 : @IN real x t) : @IN real x t.
Proof. exact (EQ_MP (@lem5321925 x t) (@lem5321922 x t h1)). Qed.
Lemma lem5321932 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5321933 (x' : real -> real) (_69689 : real) (t : real -> Prop) : (term421 t x' _69689) = (term435 x' _69689 t).
Proof. exact (@lem5321932 (term415 x' _69689) (term376 _69689 t)). Qed.
Lemma lem5321939 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5321940 (x' : real -> real) (_69689 : real) (t : real -> Prop) : (term436 t x' _69689) = (term437 x' _69689 t).
Proof. exact (MK_COMB (@lem5321939) (@lem5321933 x' _69689 t)). Qed.
Lemma lem5321946 (x' : real -> real) (_69689 : real) (t : real -> Prop) : (term435 x' _69689 t) = (term435 x' _69689 t).
Proof. exact (eq_refl (term435 x' _69689 t)). Qed.
Lemma lem5321947 (x' : real -> real) (_69689 : real) (t : real -> Prop) : ((term421 t x' _69689) = (term435 x' _69689 t)) = ((term435 x' _69689 t) = (term435 x' _69689 t)).
Proof. exact (MK_COMB (@lem5321940 x' _69689 t) (@lem5321946 x' _69689 t)). Qed.
Lemma lem5321949 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5321950 (x : Prop) : (x = x) = True.
Proof. exact (@lem5321949 Prop x). Qed.
Lemma lem5321951 (x' : real -> real) (_69689 : real) (t : real -> Prop) : ((term435 x' _69689 t) = (term435 x' _69689 t)) = True.
Proof. exact (@lem5321950 (term435 x' _69689 t)). Qed.
Lemma lem5321952 (x' : real -> real) (_69689 : real) (t : real -> Prop) : ((term421 t x' _69689) = (term435 x' _69689 t)) = True.
Proof. exact (TRANS (@lem5321947 x' _69689 t) (@lem5321951 x' _69689 t)). Qed.
Lemma lem5321953 (x' : real -> real) (_69689 : real) (t : real -> Prop) : True = ((term421 t x' _69689) = (term435 x' _69689 t)).
Proof. exact (SYM (@lem5321952 x' _69689 t)). Qed.
Lemma lem5321954 (x' : real -> real) (_69689 : real) (t : real -> Prop) : (term421 t x' _69689) = (term435 x' _69689 t).
Proof. exact (EQ_MP (@lem5321953 x' _69689 t) (@lem0)). Qed.
Lemma lem5321955 (_69689 : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term409 t s x') : term435 x' _69689 t.
Proof. exact (EQ_MP (@lem5321954 x' _69689 t) (@lem5321860 _69689 t s x' h1)). Qed.
Lemma lem5321957 (b : Prop) (a : Prop) : (a \/ b) = (term427 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5321958 (t : real -> Prop) (x' : real -> real) (_69689 : real) : (term435 x' _69689 t) = (term438 t x' _69689).
Proof. exact (@lem5321957 (term376 _69689 t) (term415 x' _69689)). Qed.
Lemma lem5321960 (a : Prop) : (term429 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5321961 (_69689 : real) (t : real -> Prop) : (term430 _69689 t) = (@IN real _69689 t).
Proof. exact (@lem5321960 (@IN real _69689 t)). Qed.
Lemma lem5321962 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5321963 (_69689 : real) (t : real -> Prop) : (term431 _69689 t) = (term337 _69689 t).
Proof. exact (MK_COMB (@lem5321962) (@lem5321961 _69689 t)). Qed.
Lemma lem5321964 (x' : real -> real) (_69689 : real) : (term415 x' _69689) = (term415 x' _69689).
Proof. exact (eq_refl (term415 x' _69689)). Qed.
Lemma lem5321965 (t : real -> Prop) (x' : real -> real) (_69689 : real) : (term438 t x' _69689) = (term439 t x' _69689).
Proof. exact (MK_COMB (@lem5321963 _69689 t) (@lem5321964 x' _69689)). Qed.
Lemma lem5321966 (t : real -> Prop) (x' : real -> real) (_69689 : real) : (term435 x' _69689 t) = (term439 t x' _69689).
Proof. exact (TRANS (@lem5321958 t x' _69689) (@lem5321965 t x' _69689)). Qed.
Lemma lem5321969 (_69689 : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term409 t s x') : term439 t x' _69689.
Proof. exact (EQ_MP (@lem5321966 t x' _69689) (@lem5321955 _69689 t s x' h1)). Qed.
Lemma lem5321970 (x : real) (t : real -> Prop) (s : real -> Prop) (x' : real -> real) (h1 : term409 t s x') : term439 t x' x.
Proof. exact (@lem5321969 x t s x' h1). Qed.
Lemma lem5321973 (s : real -> Prop) (x' : real -> real) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : @IN real x t) : term415 x' x.
Proof. exact (@lem5321970 x t s x' h1 (@lem5321926 x t h2)). Qed.
Lemma lem5321974 (s : real -> Prop) (x' : real -> real) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : @IN real x t) : term440 x' x.
Proof. exact (fun h0 : term441 x' x => @lem5321973 s x' x t h1 h2). Qed.
Lemma lem5321976 (p : Prop) : (term423 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5321977 (x' : real -> real) (x : real) : (term440 x' x) = (term415 x' x).
Proof. exact (@lem5321976 (term415 x' x)). Qed.
Lemma lem5321978 (s : real -> Prop) (x' : real -> real) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : @IN real x t) : term415 x' x.
Proof. exact (EQ_MP (@lem5321977 x' x) (@lem5321974 s x' x t h1 h2)). Qed.
Lemma lem5321980 (a : Prop) (b : Prop) : (term442 a b) = (term443 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5321981 (s : real -> Prop) (_69688 : real) (x : real) : (term358 s _69688 x) = (term357 s _69688 x).
Proof. exact (@lem5321980 (@IN real _69688 s) (real_le _69688 x)). Qed.
Lemma lem5321983 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5321984 (s : real -> Prop) (_69688 : real) (x : real) : (term357 s _69688 x) = (term444 s _69688 x).
Proof. exact (@lem5321983 (term328 s _69688 x)). Qed.
Lemma lem5321985 (s : real -> Prop) (_69688 : real) (x : real) : (term358 s _69688 x) = (term444 s _69688 x).
Proof. exact (TRANS (@lem5321981 s _69688 x) (@lem5321984 s _69688 x)). Qed.
Lemma lem5321987 (s : real -> Prop) (x' : real -> real) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : @IN real x t) : term445 s x' x.
Proof. exact (conj (@lem5321919 s x' x t h1 h2) (@lem5321978 s x' x t h1 h2)). Qed.
Lemma lem5321989 (_69688 : real) (s : real -> Prop) (x : real) (h1 : term330 s x) : term444 s _69688 x.
Proof. exact (EQ_MP (@lem5321985 s _69688 x) (@lem5321846 _69688 s x h1)). Qed.
Lemma lem5321990 (x' : real -> real) (s : real -> Prop) (x : real) (h1 : term330 s x) : term446 s x' x.
Proof. exact (@lem5321989 (x' x) s x h1). Qed.
Lemma lem5321993 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : term330 s x) (h3 : @IN real x t) : False.
Proof. exact (@lem5321990 x' s x h2 (@lem5321987 s x' x t h1 h3)). Qed.
Lemma lem5321994 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : term330 s x) (h3 : @IN real x t) : term447.
Proof. exact (fun h0 : ~ False => @lem5321993 x' s x t h1 h2 h3). Qed.
Lemma lem5321996 (p : Prop) : (term423 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5321997 : term447 = False.
Proof. exact (@lem5321996 False). Qed.
Lemma lem5321998 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : term330 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5321997) (@lem5321994 x' s x t h1 h2 h3)). Qed.
Lemma lem5321999 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : term330 s x) (h3 : @IN real x t) : (@IN real x t) = False.
Proof. exact (prop_ext (fun h4 : @IN real x t => @lem5321998 x' s x t h1 h2 h3) (fun h4 : False => @lem5321848 x t h3)). Qed.
Lemma lem5322000 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : term330 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5321999 x' s x t h1 h2 h3) (@lem5321848 x t h3)). Qed.
Lemma lem5322001 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : term330 s x) (h3 : @IN real x t) : (@IN real x t) = False.
Proof. exact (prop_ext (fun h4 : @IN real x t => @lem5322000 x' s x t h1 h2 h3) (fun h4 : False => @lem5321809 x t h3)). Qed.
Lemma lem5322002 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : term330 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5322001 x' s x t h1 h2 h3) (@lem5321809 x t h3)). Qed.
Lemma lem5322003 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : term330 s x) (h3 : @IN real x t) : (@IN real x t) = False.
Proof. exact (prop_ext (fun h4 : @IN real x t => @lem5322002 x' s x t h1 h2 h3) (fun h4 : False => @lem5321809 x t h3)). Qed.
Lemma lem5322004 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : term330 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5322003 x' s x t h1 h2 h3) (@lem5321809 x t h3)). Qed.
Lemma lem5322005 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : term330 s x) (h3 : @IN real x t) : (term409 t s x') = False.
Proof. exact (prop_ext (fun h4 : term409 t s x' => @lem5322004 x' s x t h1 h2 h3) (fun h4 : False => @lem5321792 t s x' h1)). Qed.
Lemma lem5322006 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : term330 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5322005 x' s x t h1 h2 h3) (@lem5321792 t s x' h1)). Qed.
Lemma lem5322007 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : term330 s x) (h3 : @IN real x t) : (@IN real x t) = False.
Proof. exact (prop_ext (fun h4 : @IN real x t => @lem5322006 x' s x t h1 h2 h3) (fun h4 : False => @lem5321761 x t h3)). Qed.
Lemma lem5322008 (x' : real -> real) (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term409 t s x') (h2 : term330 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5322007 x' s x t h1 h2 h3) (@lem5321761 x t h3)). Qed.
Lemma lem5322009 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term330 s x) (h3 : @IN real x t) : False.
Proof. exact (ex_elim (@lem5321733 t s h1) (fun x' : real -> real => fun h0 : term411 t s x' => @lem5322008 x' s x t h0 h2 h3)). Qed.
Lemma lem5322010 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term330 s x) (h3 : @IN real x t) : (@IN real x t) = False.
Proof. exact (prop_ext (fun h4 : @IN real x t => @lem5322009 s x t h1 h2 h3) (fun h4 : False => @lem5321562 x t h3)). Qed.
Lemma lem5322011 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term330 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5322010 s x t h1 h2 h3) (@lem5321562 x t h3)). Qed.
Lemma lem5322012 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term330 s x) (h2 : @IN real x t) : term335 t s.
Proof. exact (fun h0 : term10 t s => @lem5322011 s x t h0 h1 h2). Qed.
Lemma lem5322013 (t : real -> Prop) (s : real -> Prop) : (term335 t s) = (term336 t s).
Proof. exact (@lem69 (term10 t s)). Qed.
Lemma lem5322014 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term330 s x) (h2 : @IN real x t) : term336 t s.
Proof. exact (EQ_MP (@lem5322013 t s) (@lem5322012 s x t h1 h2)). Qed.
Lemma lem5322015 (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term330 s x) : term339 x t s.
Proof. exact (fun h0 : @IN real x t => @lem5322014 s x t h1 h0). Qed.
Lemma lem5322016 (x : real) (t : real -> Prop) (s : real -> Prop) : term341 x t s.
Proof. exact (fun h0 : term330 s x => @lem5322015 t s x h0). Qed.
Lemma lem5322021 (t : real -> Prop) (s : real -> Prop) : term345 t s.
Proof. exact (fun x : real => @lem5322016 x t s). Qed.
Lemma lem5322026 (s : real -> Prop) : term349 s.
Proof. exact (fun t : real -> Prop => @lem5322021 t s). Qed.
Lemma lem5322031 : term353.
Proof. exact (fun s : real -> Prop => @lem5322026 s). Qed.
Lemma lem5322032 : term352.
Proof. exact (EQ_MP (@lem5321483) (@lem5322031)). Qed.
Lemma lem5322033 (s : real -> Prop) : term448 s.
Proof. exact (@lem5322032 s). Qed.
Lemma lem5322034 (s : real -> Prop) : (term448 s) = (term348 s).
Proof. exact (eq_refl (term448 s)). Qed.
Lemma lem5322035 (s : real -> Prop) : term348 s.
Proof. exact (EQ_MP (@lem5322034 s) (@lem5322033 s)). Qed.
Lemma lem5322036 (s : real -> Prop) (t : real -> Prop) : term449 s t.
Proof. exact (@lem5322035 s t). Qed.
Lemma lem5322037 (t : real -> Prop) (s : real -> Prop) : (term449 s t) = (term344 t s).
Proof. exact (eq_refl (term449 s t)). Qed.
Lemma lem5322038 (t : real -> Prop) (s : real -> Prop) : term344 t s.
Proof. exact (EQ_MP (@lem5322037 t s) (@lem5322036 s t)). Qed.
Lemma lem5322039 (t : real -> Prop) (s : real -> Prop) (x : real) : term450 t s x.
Proof. exact (@lem5322038 t s x). Qed.
Lemma lem5322040 (x : real) (t : real -> Prop) (s : real -> Prop) : (term450 t s x) = (term331 x t s).
Proof. exact (eq_refl (term450 t s x)). Qed.
Lemma lem5322041 (x : real) (t : real -> Prop) (s : real -> Prop) : term331 x t s.
Proof. exact (EQ_MP (@lem5322040 x t s) (@lem5322039 t s x)). Qed.
Lemma lem5322043 (x : real) (t : real -> Prop) (s : real -> Prop) : term331 x t s.
Proof. exact (@lem5321232 x t s (@lem5322041 x t s)). Qed.
Lemma lem5322044 (t : real -> Prop) (s : real -> Prop) (x : real) (h1 : term330 s x) : term338 x t s.
Proof. exact (@lem5322043 x t s (@lem5321217 s x h1)). Qed.
Lemma lem5322045 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term330 s x) (h2 : @IN real x t) : term335 t s.
Proof. exact (@lem5322044 t s x h1 (@lem5321198 x t h2)). Qed.
Lemma lem5322046 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term330 s x) (h3 : @IN real x t) : False.
Proof. exact (@lem5322045 s x t h2 h3 (@lem5319422 t s h1)). Qed.
Lemma lem5322047 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term330 s x) (h3 : @IN real x t) : (term10 t s) = False.
Proof. exact (prop_ext (fun h4 : term10 t s => @lem5322046 s x t h1 h2 h3) (fun h4 : False => @lem5319422 t s h1)). Qed.
Lemma lem5322048 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term330 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5322047 s x t h1 h2 h3) (@lem5319422 t s h1)). Qed.
Lemma lem5322049 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term330 s x) (h3 : @IN real x t) : (@IN real x t) = False.
Proof. exact (prop_ext (fun h4 : @IN real x t => @lem5322048 s x t h1 h2 h3) (fun h4 : False => @lem5321198 x t h3)). Qed.
Lemma lem5322050 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term330 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5322049 s x t h1 h2 h3) (@lem5321198 x t h3)). Qed.
Lemma lem5322051 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term330 s x) (h3 : @IN real x t) : (term330 s x) = False.
Proof. exact (prop_ext (fun h4 : term330 s x => @lem5322050 s x t h1 h2 h3) (fun h4 : False => @lem5321217 s x h2)). Qed.
Lemma lem5322052 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : term330 s x) (h3 : @IN real x t) : False.
Proof. exact (EQ_MP (@lem5322051 s x t h1 h2 h3) (@lem5321217 s x h2)). Qed.
Lemma lem5322053 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : @IN real x t) : term329 s x.
Proof. exact (fun h0 : term330 s x => @lem5322052 s x t h1 h0 h2). Qed.
Lemma lem5322054 (s : real -> Prop) (x : real) (t : real -> Prop) (h1 : term10 t s) (h2 : @IN real x t) : term327 s x.
Proof. exact (EQ_MP (@lem5321216 s x) (@lem5322053 s x t h1 h2)). Qed.
Lemma lem5322055 (y : real) (s : real -> Prop) (l : real) (h1 : term13 s l) : term451 s l y.
Proof. exact (@lem5319454 s l h1 y). Qed.
Lemma lem5322056 (s : real -> Prop) (l : real) (y : real) : (term451 s l y) = (term452 s l y).
Proof. exact (eq_refl (term451 s l y)). Qed.
Lemma lem5322057 (y : real) (s : real -> Prop) (l : real) (h1 : term13 s l) : term452 s l y.
Proof. exact (EQ_MP (@lem5322056 s l y) (@lem5322055 y s l h1)). Qed.
Lemma lem5322109 (y : real) (s : real -> Prop) : (@IN real y s) = ((@IN real y s) = True).
Proof. exact (@lem7 (@IN real y s)). Qed.
Lemma lem5322114 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem5322115 (s : real -> Prop) (l : real) (y : real) : (term453 s l y) = (term454 s l y).
Proof. exact (@lem5322114 (term452 s l y)). Qed.
Lemma lem5322119 (y : real) (s : real -> Prop) (h1 : @IN real y s) : (@IN real y s) = True.
Proof. exact (EQ_MP (@lem5322109 y s) (@lem5321202 y s h1)). Qed.
Lemma lem5322120 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5322121 (y : real) (s : real -> Prop) (h1 : @IN real y s) : (term337 y s) = (imp True).
Proof. exact (MK_COMB (@lem5322120) (@lem5322119 y s h1)). Qed.
Lemma lem5322122 (l : real) (y : real) : (real_le l y) = (real_le l y).
Proof. exact (eq_refl (real_le l y)). Qed.
Lemma lem5322123 (l : real) (y : real) (s : real -> Prop) (h1 : @IN real y s) : (term452 s l y) = (term455 l y).
Proof. exact (MK_COMB (@lem5322121 y s h1) (@lem5322122 l y)). Qed.
Lemma lem5322125 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5322126 (l : real) (y : real) : (term455 l y) = (real_le l y).
Proof. exact (@lem5322125 (real_le l y)). Qed.
Lemma lem5322127 (l : real) (y : real) (s : real -> Prop) (h1 : @IN real y s) : (term452 s l y) = (real_le l y).
Proof. exact (TRANS (@lem5322123 l y s h1) (@lem5322126 l y)). Qed.
Lemma lem5322128 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5322129 (l : real) (y : real) (s : real -> Prop) (h1 : @IN real y s) : (term454 s l y) = (term3 l y).
Proof. exact (MK_COMB (@lem5322128) (@lem5322127 l y s h1)). Qed.
Lemma lem5322130 (l : real) (y : real) (s : real -> Prop) (h1 : @IN real y s) : (term453 s l y) = (term3 l y).
Proof. exact (TRANS (@lem5322115 s l y) (@lem5322129 l y s h1)). Qed.
Lemma lem5322131 (l : real) (y : real) (s : real -> Prop) (h1 : @IN real y s) : (term3 l y) = (term453 s l y).
Proof. exact (SYM (@lem5322130 l y s h1)). Qed.
Lemma lem5322165 (l : real) (y : real) : (term456 l y) = (real_le l y).
Proof. exact (@lem16933 (real_le l y)). Qed.
Lemma lem5322167 (y : real) (x : real) : (term457 y x) = (term457 y x).
Proof. exact (eq_refl (term457 y x)). Qed.
Lemma lem5322168 (x : real) (l : real) (y : real) : (term458 x l y) = (term459 x l y).
Proof. exact (MK_COMB (@lem5322167 y x) (@lem5322165 l y)). Qed.
Lemma lem5322169 (x : real) (l : real) (y : real) : (term460 x l y) = (term458 x l y).
Proof. exact (@lem17362 (real_le y x) (term3 l y)). Qed.
Lemma lem5322170 (x : real) (l : real) (y : real) : (term460 x l y) = (term459 x l y).
Proof. exact (TRANS (@lem5322169 x l y) (@lem5322168 x l y)). Qed.
Lemma lem5322172 (y : real) (s : real -> Prop) : (term461 y s) = (term461 y s).
Proof. exact (eq_refl (term461 y s)). Qed.
Lemma lem5322173 (s : real -> Prop) (x : real) (l : real) (y : real) : (term462 s x l y) = (term463 s x l y).
Proof. exact (MK_COMB (@lem5322172 y s) (@lem5322170 x l y)). Qed.
Lemma lem5322174 (s : real -> Prop) (x : real) (l : real) (y : real) : (term464 s x l y) = (term462 s x l y).
Proof. exact (@lem17362 (@IN real y s) (term465 x l y)). Qed.
Lemma lem5322175 (s : real -> Prop) (x : real) (l : real) (y : real) : (term464 s x l y) = (term463 s x l y).
Proof. exact (TRANS (@lem5322174 s x l y) (@lem5322173 s x l y)). Qed.
Lemma lem5322177 (x : real) (c : real) : (term23 x c) = (term23 x c).
Proof. exact (eq_refl (term23 x c)). Qed.
Lemma lem5322178 (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term466 c s x l y) = (term467 c s x l y).
Proof. exact (MK_COMB (@lem5322177 x c) (@lem5322175 s x l y)). Qed.
Lemma lem5322179 (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term468 c s x l y) = (term466 c s x l y).
Proof. exact (@lem17362 (real_lt x c) (term469 s x l y)). Qed.
Lemma lem5322180 (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term468 c s x l y) = (term467 c s x l y).
Proof. exact (TRANS (@lem5322179 c s x l y) (@lem5322178 c s x l y)). Qed.
Lemma lem5322182 (x : real) (t : real -> Prop) : (term461 x t) = (term461 x t).
Proof. exact (eq_refl (term461 x t)). Qed.
Lemma lem5322183 (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term470 t c s x l y) = (term471 t c s x l y).
Proof. exact (MK_COMB (@lem5322182 x t) (@lem5322180 c s x l y)). Qed.
Lemma lem5322184 (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term472 t c s x l y) = (term470 t c s x l y).
Proof. exact (@lem17362 (@IN real x t) (term473 c s x l y)). Qed.
Lemma lem5322185 (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term472 t c s x l y) = (term471 t c s x l y).
Proof. exact (TRANS (@lem5322184 t c s x l y) (@lem5322183 t c s x l y)). Qed.
Lemma lem5322187 (c : real) (l : real) : (term23 c l) = (term23 c l).
Proof. exact (eq_refl (term23 c l)). Qed.
Lemma lem5322188 (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term474 t c s x l y) = (term475 t c s x l y).
Proof. exact (MK_COMB (@lem5322187 c l) (@lem5322185 t c s x l y)). Qed.
Lemma lem5322189 (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term476 t c s x l y) = (term474 t c s x l y).
Proof. exact (@lem17362 (real_lt c l) (term477 t c s x l y)). Qed.
Lemma lem5322190 (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term476 t c s x l y) = (term475 t c s x l y).
Proof. exact (TRANS (@lem5322189 t c s x l y) (@lem5322188 t c s x l y)). Qed.
Lemma lem5322192 (m : real) (c : real) : (term23 m c) = (term23 m c).
Proof. exact (eq_refl (term23 m c)). Qed.
Lemma lem5322193 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term478 m t c s x l y) = (term479 m t c s x l y).
Proof. exact (MK_COMB (@lem5322192 m c) (@lem5322190 t c s x l y)). Qed.
Lemma lem5322194 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term480 m t c s x l y) = (term478 m t c s x l y).
Proof. exact (@lem17362 (real_lt m c) (term481 t c s x l y)). Qed.
Lemma lem5322195 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term480 m t c s x l y) = (term479 m t c s x l y).
Proof. exact (TRANS (@lem5322194 m t c s x l y) (@lem5322193 m t c s x l y)). Qed.
Lemma lem5322197 (m : real) (l : real) : (term23 m l) = (term23 m l).
Proof. exact (eq_refl (term23 m l)). Qed.
Lemma lem5322198 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term482 m t c s x l y) = (term483 m t c s x l y).
Proof. exact (MK_COMB (@lem5322197 m l) (@lem5322195 m t c s x l y)). Qed.
Lemma lem5322199 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term484 m t c s x l y) = (term482 m t c s x l y).
Proof. exact (@lem17362 (real_lt m l) (term485 m t c s x l y)). Qed.
Lemma lem5322200 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term484 m t c s x l y) = (term483 m t c s x l y).
Proof. exact (TRANS (@lem5322199 m t c s x l y) (@lem5322198 m t c s x l y)). Qed.
Lemma lem5322202 (t : real -> Prop) : (term28 t) = (term28 t).
Proof. exact (eq_refl (term28 t)). Qed.
Lemma lem5322203 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term486 m t c s x l y) = (term487 m t c s x l y).
Proof. exact (MK_COMB (@lem5322202 t) (@lem5322200 m t c s x l y)). Qed.
Lemma lem5322204 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term488 m t c s x l y) = (term486 m t c s x l y).
Proof. exact (@lem17362 (term12 t) (term489 m t c s x l y)). Qed.
Lemma lem5322205 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term488 m t c s x l y) = (term487 m t c s x l y).
Proof. exact (TRANS (@lem5322204 m t c s x l y) (@lem5322203 m t c s x l y)). Qed.
Lemma lem5322207 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5322208 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term490 m t c s x l y) = (term491 m t c s x l y).
Proof. exact (MK_COMB (@lem5322207 s) (@lem5322205 m t c s x l y)). Qed.
Lemma lem5322209 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term492 m t c s x l y) = (term490 m t c s x l y).
Proof. exact (@lem17362 (term12 s) (term493 m t c s x l y)). Qed.
Lemma lem5322253 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term492 m t c s x l y) = (term491 m t c s x l y).
Proof. exact (TRANS (@lem5322209 m t c s x l y) (@lem5322208 m t c s x l y)). Qed.
Lemma lem5322256 (l : real) (m : real) : (real_lt m l) = (term37 l m).
Proof. exact (@lem1988285 l m). Qed.
Lemma lem5322269 (l : real) (m : real) : (real_sub l m) = (term38 l m).
Proof. exact (@lem1982792 l m). Qed.
Lemma lem5322270 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5322271 (l : real) (m : real) : (term39 l m) = (term40 l m).
Proof. exact (MK_COMB (@lem5322270) (@lem5322269 l m)). Qed.
Lemma lem5322272 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5322273 (l : real) (m : real) : (term37 l m) = (term42 l m).
Proof. exact (MK_COMB (@lem5322271 l m) (@lem5322272)). Qed.
Lemma lem5322274 (l : real) (m : real) : (real_lt m l) = (term42 l m).
Proof. exact (TRANS (@lem5322256 l m) (@lem5322273 l m)). Qed.
Lemma lem5322275 (c : real) (m : real) : (real_lt m c) = (term37 c m).
Proof. exact (@lem1988285 c m). Qed.
Lemma lem5322288 (c : real) (m : real) : (real_sub c m) = (term38 c m).
Proof. exact (@lem1982792 c m). Qed.
Lemma lem5322289 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5322290 (c : real) (m : real) : (term39 c m) = (term40 c m).
Proof. exact (MK_COMB (@lem5322289) (@lem5322288 c m)). Qed.
Lemma lem5322291 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5322292 (c : real) (m : real) : (term37 c m) = (term42 c m).
Proof. exact (MK_COMB (@lem5322290 c m) (@lem5322291)). Qed.
Lemma lem5322293 (c : real) (m : real) : (real_lt m c) = (term42 c m).
Proof. exact (TRANS (@lem5322275 c m) (@lem5322292 c m)). Qed.
Lemma lem5322294 (l : real) (c : real) : (real_lt c l) = (term37 l c).
Proof. exact (@lem1988285 l c). Qed.
Lemma lem5322300 (l : real) (c : real) : (real_sub l c) = (term38 l c).
Proof. exact (@lem1982792 l c). Qed.
Lemma lem5322305 (c : real) (l : real) : (term38 l c) = (term494 c l).
Proof. exact (@lem1982761 (term150 c) l). Qed.
Lemma lem5322307 (c : real) (l : real) : (real_sub l c) = (term494 c l).
Proof. exact (TRANS (@lem5322300 l c) (@lem5322305 c l)). Qed.
Lemma lem5322308 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5322309 (c : real) (l : real) : (term39 l c) = (term495 c l).
Proof. exact (MK_COMB (@lem5322308) (@lem5322307 c l)). Qed.
Lemma lem5322310 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5322311 (c : real) (l : real) : (term37 l c) = (term496 c l).
Proof. exact (MK_COMB (@lem5322309 c l) (@lem5322310)). Qed.
Lemma lem5322312 (c : real) (l : real) : (real_lt c l) = (term496 c l).
Proof. exact (TRANS (@lem5322294 l c) (@lem5322311 c l)). Qed.
Lemma lem5322314 (c : real) (x : real) : (real_lt x c) = (term37 c x).
Proof. exact (@lem1988285 c x). Qed.
Lemma lem5322327 (c : real) (x : real) : (real_sub c x) = (term38 c x).
Proof. exact (@lem1982792 c x). Qed.
Lemma lem5322328 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5322329 (c : real) (x : real) : (term39 c x) = (term40 c x).
Proof. exact (MK_COMB (@lem5322328) (@lem5322327 c x)). Qed.
Lemma lem5322330 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5322331 (c : real) (x : real) : (term37 c x) = (term42 c x).
Proof. exact (MK_COMB (@lem5322329 c x) (@lem5322330)). Qed.
Lemma lem5322332 (c : real) (x : real) : (real_lt x c) = (term42 c x).
Proof. exact (TRANS (@lem5322314 c x) (@lem5322331 c x)). Qed.
Lemma lem5322334 (x : real) (y : real) : (real_le y x) = (term497 x y).
Proof. exact (@lem1988287 x y). Qed.
Lemma lem5322347 (x : real) (y : real) : (real_sub x y) = (term38 x y).
Proof. exact (@lem1982792 x y). Qed.
Lemma lem5322348 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5322349 (x : real) (y : real) : (term498 x y) = (term499 x y).
Proof. exact (MK_COMB (@lem5322348) (@lem5322347 x y)). Qed.
Lemma lem5322350 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5322351 (x : real) (y : real) : (term497 x y) = (term500 x y).
Proof. exact (MK_COMB (@lem5322349 x y) (@lem5322350)). Qed.
Lemma lem5322352 (x : real) (y : real) : (real_le y x) = (term500 x y).
Proof. exact (TRANS (@lem5322334 x y) (@lem5322351 x y)). Qed.
Lemma lem5322353 (y : real) (l : real) : (real_le l y) = (term497 y l).
Proof. exact (@lem1988287 y l). Qed.
Lemma lem5322359 (y : real) (l : real) : (real_sub y l) = (term38 y l).
Proof. exact (@lem1982792 y l). Qed.
Lemma lem5322364 (l : real) (y : real) : (term38 y l) = (term494 l y).
Proof. exact (@lem1982761 (term150 l) y). Qed.
Lemma lem5322366 (l : real) (y : real) : (real_sub y l) = (term494 l y).
Proof. exact (TRANS (@lem5322359 y l) (@lem5322364 l y)). Qed.
Lemma lem5322367 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5322368 (l : real) (y : real) : (term498 y l) = (term501 l y).
Proof. exact (MK_COMB (@lem5322367) (@lem5322366 l y)). Qed.
Lemma lem5322369 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5322370 (l : real) (y : real) : (term497 y l) = (term502 l y).
Proof. exact (MK_COMB (@lem5322368 l y) (@lem5322369)). Qed.
Lemma lem5322371 (l : real) (y : real) : (real_le l y) = (term502 l y).
Proof. exact (TRANS (@lem5322353 y l) (@lem5322370 l y)). Qed.
Lemma lem5322372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5322373 (x : real) (y : real) : (term457 y x) = (term503 x y).
Proof. exact (MK_COMB (@lem5322372) (@lem5322352 x y)). Qed.
Lemma lem5322374 (x : real) (l : real) (y : real) : (term459 x l y) = (term504 x l y).
Proof. exact (MK_COMB (@lem5322373 x y) (@lem5322371 l y)). Qed.
Lemma lem5322376 (y : real) (s : real -> Prop) : (term461 y s) = (term461 y s).
Proof. exact (eq_refl (term461 y s)). Qed.
Lemma lem5322377 (s : real -> Prop) (x : real) (l : real) (y : real) : (term463 s x l y) = (term505 s x l y).
Proof. exact (MK_COMB (@lem5322376 y s) (@lem5322374 x l y)). Qed.
Lemma lem5322378 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5322379 (c : real) (x : real) : (term23 x c) = (term179 c x).
Proof. exact (MK_COMB (@lem5322378) (@lem5322332 c x)). Qed.
Lemma lem5322380 (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term467 c s x l y) = (term506 c s x l y).
Proof. exact (MK_COMB (@lem5322379 c x) (@lem5322377 s x l y)). Qed.
Lemma lem5322382 (x : real) (t : real -> Prop) : (term461 x t) = (term461 x t).
Proof. exact (eq_refl (term461 x t)). Qed.
Lemma lem5322383 (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term471 t c s x l y) = (term507 t c s x l y).
Proof. exact (MK_COMB (@lem5322382 x t) (@lem5322380 c s x l y)). Qed.
Lemma lem5322384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5322385 (c : real) (l : real) : (term23 c l) = (term508 c l).
Proof. exact (MK_COMB (@lem5322384) (@lem5322312 c l)). Qed.
Lemma lem5322386 (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term475 t c s x l y) = (term509 t c s x l y).
Proof. exact (MK_COMB (@lem5322385 c l) (@lem5322383 t c s x l y)). Qed.
Lemma lem5322387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5322388 (c : real) (m : real) : (term23 m c) = (term179 c m).
Proof. exact (MK_COMB (@lem5322387) (@lem5322293 c m)). Qed.
Lemma lem5322389 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term479 m t c s x l y) = (term510 m t c s x l y).
Proof. exact (MK_COMB (@lem5322388 c m) (@lem5322386 t c s x l y)). Qed.
Lemma lem5322390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5322391 (l : real) (m : real) : (term23 m l) = (term179 l m).
Proof. exact (MK_COMB (@lem5322390) (@lem5322274 l m)). Qed.
Lemma lem5322392 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term483 m t c s x l y) = (term511 m t c s x l y).
Proof. exact (MK_COMB (@lem5322391 l m) (@lem5322389 m t c s x l y)). Qed.
Lemma lem5322394 (t : real -> Prop) : (term28 t) = (term28 t).
Proof. exact (eq_refl (term28 t)). Qed.
Lemma lem5322395 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term487 m t c s x l y) = (term512 m t c s x l y).
Proof. exact (MK_COMB (@lem5322394 t) (@lem5322392 m t c s x l y)). Qed.
Lemma lem5322397 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5322398 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term491 m t c s x l y) = (term513 m t c s x l y).
Proof. exact (MK_COMB (@lem5322397 s) (@lem5322395 m t c s x l y)). Qed.
Lemma lem5322461 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : (term492 m t c s x l y) = (term513 m t c s x l y).
Proof. exact (TRANS (@lem5322253 m t c s x l y) (@lem5322398 m t c s x l y)). Qed.
Lemma lem5322465 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term513 m t c s x l y.
Proof. exact (h1). Qed.
Lemma lem5322466 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term512 m t c s x l y.
Proof. exact (proj2 (@lem5322465 m t c s x l y h1)). Qed.
Lemma lem5322468 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term511 m t c s x l y.
Proof. exact (proj2 (@lem5322466 m t c s x l y h1)). Qed.
Lemma lem5322470 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term510 m t c s x l y.
Proof. exact (proj2 (@lem5322468 m t c s x l y h1)). Qed.
Lemma lem5322472 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term509 t c s x l y.
Proof. exact (proj2 (@lem5322470 m t c s x l y h1)). Qed.
Lemma lem5322474 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term507 t c s x l y.
Proof. exact (proj2 (@lem5322472 m t c s x l y h1)). Qed.
Lemma lem5322475 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term496 c l.
Proof. exact (proj1 (@lem5322472 m t c s x l y h1)). Qed.
Lemma lem5322476 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term506 c s x l y.
Proof. exact (proj2 (@lem5322474 m t c s x l y h1)). Qed.
Lemma lem5322478 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term505 s x l y.
Proof. exact (proj2 (@lem5322476 m t c s x l y h1)). Qed.
Lemma lem5322479 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term42 c x.
Proof. exact (proj1 (@lem5322476 m t c s x l y h1)). Qed.
Lemma lem5322480 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term504 x l y.
Proof. exact (proj2 (@lem5322478 m t c s x l y h1)). Qed.
Lemma lem5322482 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term502 l y.
Proof. exact (proj2 (@lem5322480 m t c s x l y h1)). Qed.
Lemma lem5322483 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term500 x y.
Proof. exact (proj1 (@lem5322480 m t c s x l y h1)). Qed.
Lemma lem5322485 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5322486 : term191 = term115.
Proof. exact (@lem5322485 term41 term76). Qed.
Lemma lem5322488 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5322489 : term76 = term105.
Proof. exact (@lem5322488 term70). Qed.
Lemma lem5322491 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5322492 : term41 = term192.
Proof. exact (@lem5322491 (NUMERAL 0)). Qed.
Lemma lem5322493 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5322494 : term193 = term194.
Proof. exact (MK_COMB (@lem5322493) (@lem5322492)). Qed.
Lemma lem5322495 : term115 = term195.
Proof. exact (MK_COMB (@lem5322494) (@lem5322489)). Qed.
Lemma lem5322496 : term196.
Proof. exact (@lem1980255 term41 term76 term76 term76). Qed.
Lemma lem5322498 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322499 : term115 = term116.
Proof. exact (@lem5322498 (NUMERAL 0) term70). Qed.
Lemma lem5322500 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322501 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322502 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322501 h1) (fun h1 : term116 = True => @lem5322500)). Qed.
Lemma lem5322503 : term116 = True.
Proof. exact (EQ_MP (@lem5322502) (@lem5322500)). Qed.
Lemma lem5322504 : term115 = True.
Proof. exact (TRANS (@lem5322499) (@lem5322503)). Qed.
Lemma lem5322505 : True = term115.
Proof. exact (SYM (@lem5322504)). Qed.
Lemma lem5322506 : term115.
Proof. exact (EQ_MP (@lem5322505) (@lem0)). Qed.
Lemma lem5322507 : term197.
Proof. exact (@lem5322496 (@lem5322506)). Qed.
Lemma lem5322509 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322510 : term115 = term116.
Proof. exact (@lem5322509 (NUMERAL 0) term70). Qed.
Lemma lem5322511 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322512 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322513 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322512 h1) (fun h1 : term116 = True => @lem5322511)). Qed.
Lemma lem5322514 : term116 = True.
Proof. exact (EQ_MP (@lem5322513) (@lem5322511)). Qed.
Lemma lem5322515 : term115 = True.
Proof. exact (TRANS (@lem5322510) (@lem5322514)). Qed.
Lemma lem5322516 : True = term115.
Proof. exact (SYM (@lem5322515)). Qed.
Lemma lem5322517 : term115.
Proof. exact (EQ_MP (@lem5322516) (@lem0)). Qed.
Lemma lem5322518 : term195 = term198.
Proof. exact (@lem5322507 (@lem5322517)). Qed.
Lemma lem5322520 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5322521 : term163 = term90.
Proof. exact (@lem5322520 term70 term70). Qed.
Lemma lem5322522 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5322523 : term89 = term70.
Proof. exact (EQ_MP (@lem5322522) (@lem940073)). Qed.
Lemma lem5322524 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5322525 : term90 = term76.
Proof. exact (MK_COMB (@lem5322524) (@lem5322523)). Qed.
Lemma lem5322526 : term163 = term76.
Proof. exact (TRANS (@lem5322521) (@lem5322525)). Qed.
Lemma lem5322528 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5322529 : term200 = term41.
Proof. exact (@lem5322528 term70). Qed.
Lemma lem5322530 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5322531 : term201 = term193.
Proof. exact (MK_COMB (@lem5322530) (@lem5322529)). Qed.
Lemma lem5322532 : term198 = term115.
Proof. exact (MK_COMB (@lem5322531) (@lem5322526)). Qed.
Lemma lem5322534 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322535 : term115 = term116.
Proof. exact (@lem5322534 (NUMERAL 0) term70). Qed.
Lemma lem5322536 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322537 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322538 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322537 h1) (fun h1 : term116 = True => @lem5322536)). Qed.
Lemma lem5322539 : term116 = True.
Proof. exact (EQ_MP (@lem5322538) (@lem5322536)). Qed.
Lemma lem5322540 : term115 = True.
Proof. exact (TRANS (@lem5322535) (@lem5322539)). Qed.
Lemma lem5322541 : term198 = True.
Proof. exact (TRANS (@lem5322532) (@lem5322540)). Qed.
Lemma lem5322542 : term195 = True.
Proof. exact (TRANS (@lem5322518) (@lem5322541)). Qed.
Lemma lem5322543 : term115 = True.
Proof. exact (TRANS (@lem5322495) (@lem5322542)). Qed.
Lemma lem5322544 : term191 = True.
Proof. exact (TRANS (@lem5322486) (@lem5322543)). Qed.
Lemma lem5322545 : True = term191.
Proof. exact (SYM (@lem5322544)). Qed.
Lemma lem5322546 : term191.
Proof. exact (EQ_MP (@lem5322545) (@lem0)). Qed.
Lemma lem5322547 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term514 x y.
Proof. exact (conj (@lem5322546) (@lem5322483 m t c s x l y h1)). Qed.
Lemma lem5322549 (x : real) (y : real) : term203 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5322550 (x : real) (y : real) : term515 x y.
Proof. exact (@lem5322549 term76 (term38 x y)). Qed.
Lemma lem5322551 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term516 x y.
Proof. exact (@lem5322550 x y (@lem5322547 m t c s x l y h1)). Qed.
Lemma lem5322552 (x : real) (y : real) : (term517 x y) = (term38 x y).
Proof. exact (@lem1982733 (term38 x y)). Qed.
Lemma lem5322553 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5322554 (x : real) (y : real) : (term518 x y) = (term499 x y).
Proof. exact (MK_COMB (@lem5322553) (@lem5322552 x y)). Qed.
Lemma lem5322555 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5322556 (x : real) (y : real) : (term516 x y) = (term500 x y).
Proof. exact (MK_COMB (@lem5322554 x y) (@lem5322555)). Qed.
Lemma lem5322557 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term500 x y.
Proof. exact (EQ_MP (@lem5322556 x y) (@lem5322551 m t c s x l y h1)). Qed.
Lemma lem5322559 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5322560 : term191 = term115.
Proof. exact (@lem5322559 term41 term76). Qed.
Lemma lem5322562 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5322563 : term76 = term105.
Proof. exact (@lem5322562 term70). Qed.
Lemma lem5322565 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5322566 : term41 = term192.
Proof. exact (@lem5322565 (NUMERAL 0)). Qed.
Lemma lem5322567 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5322568 : term193 = term194.
Proof. exact (MK_COMB (@lem5322567) (@lem5322566)). Qed.
Lemma lem5322569 : term115 = term195.
Proof. exact (MK_COMB (@lem5322568) (@lem5322563)). Qed.
Lemma lem5322570 : term196.
Proof. exact (@lem1980255 term41 term76 term76 term76). Qed.
Lemma lem5322572 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322573 : term115 = term116.
Proof. exact (@lem5322572 (NUMERAL 0) term70). Qed.
Lemma lem5322574 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322575 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322576 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322575 h1) (fun h1 : term116 = True => @lem5322574)). Qed.
Lemma lem5322577 : term116 = True.
Proof. exact (EQ_MP (@lem5322576) (@lem5322574)). Qed.
Lemma lem5322578 : term115 = True.
Proof. exact (TRANS (@lem5322573) (@lem5322577)). Qed.
Lemma lem5322579 : True = term115.
Proof. exact (SYM (@lem5322578)). Qed.
Lemma lem5322580 : term115.
Proof. exact (EQ_MP (@lem5322579) (@lem0)). Qed.
Lemma lem5322581 : term197.
Proof. exact (@lem5322570 (@lem5322580)). Qed.
Lemma lem5322583 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322584 : term115 = term116.
Proof. exact (@lem5322583 (NUMERAL 0) term70). Qed.
Lemma lem5322585 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322586 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322587 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322586 h1) (fun h1 : term116 = True => @lem5322585)). Qed.
Lemma lem5322588 : term116 = True.
Proof. exact (EQ_MP (@lem5322587) (@lem5322585)). Qed.
Lemma lem5322589 : term115 = True.
Proof. exact (TRANS (@lem5322584) (@lem5322588)). Qed.
Lemma lem5322590 : True = term115.
Proof. exact (SYM (@lem5322589)). Qed.
Lemma lem5322591 : term115.
Proof. exact (EQ_MP (@lem5322590) (@lem0)). Qed.
Lemma lem5322592 : term195 = term198.
Proof. exact (@lem5322581 (@lem5322591)). Qed.
Lemma lem5322594 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5322595 : term163 = term90.
Proof. exact (@lem5322594 term70 term70). Qed.
Lemma lem5322596 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5322597 : term89 = term70.
Proof. exact (EQ_MP (@lem5322596) (@lem940073)). Qed.
Lemma lem5322598 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5322599 : term90 = term76.
Proof. exact (MK_COMB (@lem5322598) (@lem5322597)). Qed.
Lemma lem5322600 : term163 = term76.
Proof. exact (TRANS (@lem5322595) (@lem5322599)). Qed.
Lemma lem5322602 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5322603 : term200 = term41.
Proof. exact (@lem5322602 term70). Qed.
Lemma lem5322604 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5322605 : term201 = term193.
Proof. exact (MK_COMB (@lem5322604) (@lem5322603)). Qed.
Lemma lem5322606 : term198 = term115.
Proof. exact (MK_COMB (@lem5322605) (@lem5322600)). Qed.
Lemma lem5322608 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322609 : term115 = term116.
Proof. exact (@lem5322608 (NUMERAL 0) term70). Qed.
Lemma lem5322610 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322611 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322612 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322611 h1) (fun h1 : term116 = True => @lem5322610)). Qed.
Lemma lem5322613 : term116 = True.
Proof. exact (EQ_MP (@lem5322612) (@lem5322610)). Qed.
Lemma lem5322614 : term115 = True.
Proof. exact (TRANS (@lem5322609) (@lem5322613)). Qed.
Lemma lem5322615 : term198 = True.
Proof. exact (TRANS (@lem5322606) (@lem5322614)). Qed.
Lemma lem5322616 : term195 = True.
Proof. exact (TRANS (@lem5322592) (@lem5322615)). Qed.
Lemma lem5322617 : term115 = True.
Proof. exact (TRANS (@lem5322569) (@lem5322616)). Qed.
Lemma lem5322618 : term191 = True.
Proof. exact (TRANS (@lem5322560) (@lem5322617)). Qed.
Lemma lem5322619 : True = term191.
Proof. exact (SYM (@lem5322618)). Qed.
Lemma lem5322620 : term191.
Proof. exact (EQ_MP (@lem5322619) (@lem0)). Qed.
Lemma lem5322621 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term519 c x.
Proof. exact (conj (@lem5322620) (@lem5322479 m t c s x l y h1)). Qed.
Lemma lem5322623 (x : real) (y : real) : term217 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5322624 (c : real) (x : real) : term520 c x.
Proof. exact (@lem5322623 term76 (term38 c x)). Qed.
Lemma lem5322625 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term521 c x.
Proof. exact (@lem5322624 c x (@lem5322621 m t c s x l y h1)). Qed.
Lemma lem5322626 (c : real) (x : real) : (term517 c x) = (term38 c x).
Proof. exact (@lem1982733 (term38 c x)). Qed.
Lemma lem5322627 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5322628 (c : real) (x : real) : (term522 c x) = (term40 c x).
Proof. exact (MK_COMB (@lem5322627) (@lem5322626 c x)). Qed.
Lemma lem5322629 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5322630 (c : real) (x : real) : (term521 c x) = (term42 c x).
Proof. exact (MK_COMB (@lem5322628 c x) (@lem5322629)). Qed.
Lemma lem5322631 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term42 c x.
Proof. exact (EQ_MP (@lem5322630 c x) (@lem5322625 m t c s x l y h1)). Qed.
Lemma lem5322633 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5322634 : term191 = term115.
Proof. exact (@lem5322633 term41 term76). Qed.
Lemma lem5322636 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5322637 : term76 = term105.
Proof. exact (@lem5322636 term70). Qed.
Lemma lem5322639 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5322640 : term41 = term192.
Proof. exact (@lem5322639 (NUMERAL 0)). Qed.
Lemma lem5322641 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5322642 : term193 = term194.
Proof. exact (MK_COMB (@lem5322641) (@lem5322640)). Qed.
Lemma lem5322643 : term115 = term195.
Proof. exact (MK_COMB (@lem5322642) (@lem5322637)). Qed.
Lemma lem5322644 : term196.
Proof. exact (@lem1980255 term41 term76 term76 term76). Qed.
Lemma lem5322646 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322647 : term115 = term116.
Proof. exact (@lem5322646 (NUMERAL 0) term70). Qed.
Lemma lem5322648 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322649 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322650 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322649 h1) (fun h1 : term116 = True => @lem5322648)). Qed.
Lemma lem5322651 : term116 = True.
Proof. exact (EQ_MP (@lem5322650) (@lem5322648)). Qed.
Lemma lem5322652 : term115 = True.
Proof. exact (TRANS (@lem5322647) (@lem5322651)). Qed.
Lemma lem5322653 : True = term115.
Proof. exact (SYM (@lem5322652)). Qed.
Lemma lem5322654 : term115.
Proof. exact (EQ_MP (@lem5322653) (@lem0)). Qed.
Lemma lem5322655 : term197.
Proof. exact (@lem5322644 (@lem5322654)). Qed.
Lemma lem5322657 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322658 : term115 = term116.
Proof. exact (@lem5322657 (NUMERAL 0) term70). Qed.
Lemma lem5322659 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322660 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322661 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322660 h1) (fun h1 : term116 = True => @lem5322659)). Qed.
Lemma lem5322662 : term116 = True.
Proof. exact (EQ_MP (@lem5322661) (@lem5322659)). Qed.
Lemma lem5322663 : term115 = True.
Proof. exact (TRANS (@lem5322658) (@lem5322662)). Qed.
Lemma lem5322664 : True = term115.
Proof. exact (SYM (@lem5322663)). Qed.
Lemma lem5322665 : term115.
Proof. exact (EQ_MP (@lem5322664) (@lem0)). Qed.
Lemma lem5322666 : term195 = term198.
Proof. exact (@lem5322655 (@lem5322665)). Qed.
Lemma lem5322668 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5322669 : term163 = term90.
Proof. exact (@lem5322668 term70 term70). Qed.
Lemma lem5322670 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5322671 : term89 = term70.
Proof. exact (EQ_MP (@lem5322670) (@lem940073)). Qed.
Lemma lem5322672 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5322673 : term90 = term76.
Proof. exact (MK_COMB (@lem5322672) (@lem5322671)). Qed.
Lemma lem5322674 : term163 = term76.
Proof. exact (TRANS (@lem5322669) (@lem5322673)). Qed.
Lemma lem5322676 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5322677 : term200 = term41.
Proof. exact (@lem5322676 term70). Qed.
Lemma lem5322678 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5322679 : term201 = term193.
Proof. exact (MK_COMB (@lem5322678) (@lem5322677)). Qed.
Lemma lem5322680 : term198 = term115.
Proof. exact (MK_COMB (@lem5322679) (@lem5322674)). Qed.
Lemma lem5322682 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322683 : term115 = term116.
Proof. exact (@lem5322682 (NUMERAL 0) term70). Qed.
Lemma lem5322684 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322685 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322686 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322685 h1) (fun h1 : term116 = True => @lem5322684)). Qed.
Lemma lem5322687 : term116 = True.
Proof. exact (EQ_MP (@lem5322686) (@lem5322684)). Qed.
Lemma lem5322688 : term115 = True.
Proof. exact (TRANS (@lem5322683) (@lem5322687)). Qed.
Lemma lem5322689 : term198 = True.
Proof. exact (TRANS (@lem5322680) (@lem5322688)). Qed.
Lemma lem5322690 : term195 = True.
Proof. exact (TRANS (@lem5322666) (@lem5322689)). Qed.
Lemma lem5322691 : term115 = True.
Proof. exact (TRANS (@lem5322643) (@lem5322690)). Qed.
Lemma lem5322692 : term191 = True.
Proof. exact (TRANS (@lem5322634) (@lem5322691)). Qed.
Lemma lem5322693 : True = term191.
Proof. exact (SYM (@lem5322692)). Qed.
Lemma lem5322694 : term191.
Proof. exact (EQ_MP (@lem5322693) (@lem0)). Qed.
Lemma lem5322695 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term523 l y.
Proof. exact (conj (@lem5322694) (@lem5322482 m t c s x l y h1)). Qed.
Lemma lem5322697 (x : real) (y : real) : term203 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5322698 (l : real) (y : real) : term524 l y.
Proof. exact (@lem5322697 term76 (term494 l y)). Qed.
Lemma lem5322699 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term525 l y.
Proof. exact (@lem5322698 l y (@lem5322695 m t c s x l y h1)). Qed.
Lemma lem5322700 (l : real) (y : real) : (term526 l y) = (term494 l y).
Proof. exact (@lem1982733 (term494 l y)). Qed.
Lemma lem5322701 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5322702 (l : real) (y : real) : (term527 l y) = (term501 l y).
Proof. exact (MK_COMB (@lem5322701) (@lem5322700 l y)). Qed.
Lemma lem5322703 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5322704 (l : real) (y : real) : (term525 l y) = (term502 l y).
Proof. exact (MK_COMB (@lem5322702 l y) (@lem5322703)). Qed.
Lemma lem5322705 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term502 l y.
Proof. exact (EQ_MP (@lem5322704 l y) (@lem5322699 m t c s x l y h1)). Qed.
Lemma lem5322707 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5322708 : term191 = term115.
Proof. exact (@lem5322707 term41 term76). Qed.
Lemma lem5322710 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5322711 : term76 = term105.
Proof. exact (@lem5322710 term70). Qed.
Lemma lem5322713 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5322714 : term41 = term192.
Proof. exact (@lem5322713 (NUMERAL 0)). Qed.
Lemma lem5322715 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5322716 : term193 = term194.
Proof. exact (MK_COMB (@lem5322715) (@lem5322714)). Qed.
Lemma lem5322717 : term115 = term195.
Proof. exact (MK_COMB (@lem5322716) (@lem5322711)). Qed.
Lemma lem5322718 : term196.
Proof. exact (@lem1980255 term41 term76 term76 term76). Qed.
Lemma lem5322720 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322721 : term115 = term116.
Proof. exact (@lem5322720 (NUMERAL 0) term70). Qed.
Lemma lem5322722 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322723 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322724 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322723 h1) (fun h1 : term116 = True => @lem5322722)). Qed.
Lemma lem5322725 : term116 = True.
Proof. exact (EQ_MP (@lem5322724) (@lem5322722)). Qed.
Lemma lem5322726 : term115 = True.
Proof. exact (TRANS (@lem5322721) (@lem5322725)). Qed.
Lemma lem5322727 : True = term115.
Proof. exact (SYM (@lem5322726)). Qed.
Lemma lem5322728 : term115.
Proof. exact (EQ_MP (@lem5322727) (@lem0)). Qed.
Lemma lem5322729 : term197.
Proof. exact (@lem5322718 (@lem5322728)). Qed.
Lemma lem5322731 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322732 : term115 = term116.
Proof. exact (@lem5322731 (NUMERAL 0) term70). Qed.
Lemma lem5322733 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322734 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322735 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322734 h1) (fun h1 : term116 = True => @lem5322733)). Qed.
Lemma lem5322736 : term116 = True.
Proof. exact (EQ_MP (@lem5322735) (@lem5322733)). Qed.
Lemma lem5322737 : term115 = True.
Proof. exact (TRANS (@lem5322732) (@lem5322736)). Qed.
Lemma lem5322738 : True = term115.
Proof. exact (SYM (@lem5322737)). Qed.
Lemma lem5322739 : term115.
Proof. exact (EQ_MP (@lem5322738) (@lem0)). Qed.
Lemma lem5322740 : term195 = term198.
Proof. exact (@lem5322729 (@lem5322739)). Qed.
Lemma lem5322742 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5322743 : term163 = term90.
Proof. exact (@lem5322742 term70 term70). Qed.
Lemma lem5322744 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5322745 : term89 = term70.
Proof. exact (EQ_MP (@lem5322744) (@lem940073)). Qed.
Lemma lem5322746 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5322747 : term90 = term76.
Proof. exact (MK_COMB (@lem5322746) (@lem5322745)). Qed.
Lemma lem5322748 : term163 = term76.
Proof. exact (TRANS (@lem5322743) (@lem5322747)). Qed.
Lemma lem5322750 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5322751 : term200 = term41.
Proof. exact (@lem5322750 term70). Qed.
Lemma lem5322752 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5322753 : term201 = term193.
Proof. exact (MK_COMB (@lem5322752) (@lem5322751)). Qed.
Lemma lem5322754 : term198 = term115.
Proof. exact (MK_COMB (@lem5322753) (@lem5322748)). Qed.
Lemma lem5322756 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322757 : term115 = term116.
Proof. exact (@lem5322756 (NUMERAL 0) term70). Qed.
Lemma lem5322758 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322759 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322760 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322759 h1) (fun h1 : term116 = True => @lem5322758)). Qed.
Lemma lem5322761 : term116 = True.
Proof. exact (EQ_MP (@lem5322760) (@lem5322758)). Qed.
Lemma lem5322762 : term115 = True.
Proof. exact (TRANS (@lem5322757) (@lem5322761)). Qed.
Lemma lem5322763 : term198 = True.
Proof. exact (TRANS (@lem5322754) (@lem5322762)). Qed.
Lemma lem5322764 : term195 = True.
Proof. exact (TRANS (@lem5322740) (@lem5322763)). Qed.
Lemma lem5322765 : term115 = True.
Proof. exact (TRANS (@lem5322717) (@lem5322764)). Qed.
Lemma lem5322766 : term191 = True.
Proof. exact (TRANS (@lem5322708) (@lem5322765)). Qed.
Lemma lem5322767 : True = term191.
Proof. exact (SYM (@lem5322766)). Qed.
Lemma lem5322768 : term191.
Proof. exact (EQ_MP (@lem5322767) (@lem0)). Qed.
Lemma lem5322769 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term528 c l.
Proof. exact (conj (@lem5322768) (@lem5322475 m t c s x l y h1)). Qed.
Lemma lem5322771 (x : real) (y : real) : term217 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5322772 (c : real) (l : real) : term529 c l.
Proof. exact (@lem5322771 term76 (term494 c l)). Qed.
Lemma lem5322773 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term530 c l.
Proof. exact (@lem5322772 c l (@lem5322769 m t c s x l y h1)). Qed.
Lemma lem5322774 (c : real) (l : real) : (term526 c l) = (term494 c l).
Proof. exact (@lem1982733 (term494 c l)). Qed.
Lemma lem5322775 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5322776 (c : real) (l : real) : (term531 c l) = (term495 c l).
Proof. exact (MK_COMB (@lem5322775) (@lem5322774 c l)). Qed.
Lemma lem5322777 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5322778 (c : real) (l : real) : (term530 c l) = (term496 c l).
Proof. exact (MK_COMB (@lem5322776 c l) (@lem5322777)). Qed.
Lemma lem5322779 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term496 c l.
Proof. exact (EQ_MP (@lem5322778 c l) (@lem5322773 m t c s x l y h1)). Qed.
Lemma lem5322780 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term532 c l y.
Proof. exact (conj (@lem5322779 m t c s x l y h1) (@lem5322705 m t c s x l y h1)). Qed.
Lemma lem5322782 (x : real) (y : real) : term237 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5322783 (c : real) (l : real) (y : real) : term533 c l y.
Proof. exact (@lem5322782 (term494 c l) (term494 l y)). Qed.
Lemma lem5322784 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term534 c l y.
Proof. exact (@lem5322783 c l y (@lem5322780 m t c s x l y h1)). Qed.
Lemma lem5322785 (c : real) (l : real) (y : real) : (term535 c l y) = (term536 c l y).
Proof. exact (@lem1982755 (term150 c) l (term494 l y)). Qed.
Lemma lem5322786 (l : real) (y : real) : (term537 l y) = (term538 l y).
Proof. exact (@lem1982763 l (term150 l) y). Qed.
Lemma lem5322787 (l : real) : (term539 l) = (term540 l).
Proof. exact (@lem1982715 term64 l). Qed.
Lemma lem5322789 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5322790 : term76 = term105.
Proof. exact (@lem5322789 term70). Qed.
Lemma lem5322792 (x : nat) : (term67 x) = (term68 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5322793 : term64 = term69.
Proof. exact (@lem5322792 term70). Qed.
Lemma lem5322794 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5322795 : term121 = term541.
Proof. exact (MK_COMB (@lem5322794) (@lem5322793)). Qed.
Lemma lem5322796 : term542 = term543.
Proof. exact (MK_COMB (@lem5322795) (@lem5322790)). Qed.
Lemma lem5322797 : term544.
Proof. exact (@lem1981473 term64 term76 term76 term76 term41 term76). Qed.
Lemma lem5322799 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322800 : term115 = term116.
Proof. exact (@lem5322799 (NUMERAL 0) term70). Qed.
Lemma lem5322801 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322802 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322803 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322802 h1) (fun h1 : term116 = True => @lem5322801)). Qed.
Lemma lem5322804 : term116 = True.
Proof. exact (EQ_MP (@lem5322803) (@lem5322801)). Qed.
Lemma lem5322805 : term115 = True.
Proof. exact (TRANS (@lem5322800) (@lem5322804)). Qed.
Lemma lem5322806 : True = term115.
Proof. exact (SYM (@lem5322805)). Qed.
Lemma lem5322807 : term115.
Proof. exact (EQ_MP (@lem5322806) (@lem0)). Qed.
Lemma lem5322808 : term545.
Proof. exact (@lem5322797 (@lem5322807)). Qed.
Lemma lem5322810 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322811 : term115 = term116.
Proof. exact (@lem5322810 (NUMERAL 0) term70). Qed.
Lemma lem5322812 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322813 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322814 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322813 h1) (fun h1 : term116 = True => @lem5322812)). Qed.
Lemma lem5322815 : term116 = True.
Proof. exact (EQ_MP (@lem5322814) (@lem5322812)). Qed.
Lemma lem5322816 : term115 = True.
Proof. exact (TRANS (@lem5322811) (@lem5322815)). Qed.
Lemma lem5322817 : True = term115.
Proof. exact (SYM (@lem5322816)). Qed.
Lemma lem5322818 : term115.
Proof. exact (EQ_MP (@lem5322817) (@lem0)). Qed.
Lemma lem5322819 : term546.
Proof. exact (@lem5322808 (@lem5322818)). Qed.
Lemma lem5322821 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322822 : term115 = term116.
Proof. exact (@lem5322821 (NUMERAL 0) term70). Qed.
Lemma lem5322823 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322824 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322825 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322824 h1) (fun h1 : term116 = True => @lem5322823)). Qed.
Lemma lem5322826 : term116 = True.
Proof. exact (EQ_MP (@lem5322825) (@lem5322823)). Qed.
Lemma lem5322827 : term115 = True.
Proof. exact (TRANS (@lem5322822) (@lem5322826)). Qed.
Lemma lem5322828 : True = term115.
Proof. exact (SYM (@lem5322827)). Qed.
Lemma lem5322829 : term115.
Proof. exact (EQ_MP (@lem5322828) (@lem0)). Qed.
Lemma lem5322830 : term547.
Proof. exact (@lem5322819 (@lem5322829)). Qed.
Lemma lem5322832 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5322833 : term163 = term90.
Proof. exact (@lem5322832 term70 term70). Qed.
Lemma lem5322834 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5322835 : term89 = term70.
Proof. exact (EQ_MP (@lem5322834) (@lem940073)). Qed.
Lemma lem5322836 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5322837 : term90 = term76.
Proof. exact (MK_COMB (@lem5322836) (@lem5322835)). Qed.
Lemma lem5322838 : term163 = term76.
Proof. exact (TRANS (@lem5322833) (@lem5322837)). Qed.
Lemma lem5322840 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5322841 : term86 = term87.
Proof. exact (@lem5322840 term70 term70). Qed.
Lemma lem5322842 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5322843 : term89 = term70.
Proof. exact (EQ_MP (@lem5322842) (@lem940073)). Qed.
Lemma lem5322844 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5322845 : term90 = term76.
Proof. exact (MK_COMB (@lem5322844) (@lem5322843)). Qed.
Lemma lem5322846 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5322847 : term87 = term64.
Proof. exact (MK_COMB (@lem5322846) (@lem5322845)). Qed.
Lemma lem5322848 : term86 = term64.
Proof. exact (TRANS (@lem5322841) (@lem5322847)). Qed.
Lemma lem5322849 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5322850 : term120 = term121.
Proof. exact (MK_COMB (@lem5322849) (@lem5322848)). Qed.
Lemma lem5322851 : term548 = term542.
Proof. exact (MK_COMB (@lem5322850) (@lem5322838)). Qed.
Lemma lem5322853 (m : nat) : (term281 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5322854 : term542 = term41.
Proof. exact (@lem5322853 term70). Qed.
Lemma lem5322855 : term548 = term41.
Proof. exact (TRANS (@lem5322851) (@lem5322854)). Qed.
Lemma lem5322856 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5322857 : term549 = term254.
Proof. exact (MK_COMB (@lem5322856) (@lem5322855)). Qed.
Lemma lem5322858 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem5322859 : term550 = term200.
Proof. exact (MK_COMB (@lem5322857) (@lem5322858)). Qed.
Lemma lem5322861 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5322862 : term200 = term41.
Proof. exact (@lem5322861 term70). Qed.
Lemma lem5322863 : term550 = term41.
Proof. exact (TRANS (@lem5322859) (@lem5322862)). Qed.
Lemma lem5322865 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5322866 : term163 = term90.
Proof. exact (@lem5322865 term70 term70). Qed.
Lemma lem5322867 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5322868 : term89 = term70.
Proof. exact (EQ_MP (@lem5322867) (@lem940073)). Qed.
Lemma lem5322869 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5322870 : term90 = term76.
Proof. exact (MK_COMB (@lem5322869) (@lem5322868)). Qed.
Lemma lem5322871 : term163 = term76.
Proof. exact (TRANS (@lem5322866) (@lem5322870)). Qed.
Lemma lem5322872 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5322873 : term551 = term200.
Proof. exact (MK_COMB (@lem5322872) (@lem5322871)). Qed.
Lemma lem5322875 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5322876 : term200 = term41.
Proof. exact (@lem5322875 term70). Qed.
Lemma lem5322877 : term551 = term41.
Proof. exact (TRANS (@lem5322873) (@lem5322876)). Qed.
Lemma lem5322878 : term41 = term551.
Proof. exact (SYM (@lem5322877)). Qed.
Lemma lem5322879 : term550 = term551.
Proof. exact (TRANS (@lem5322863) (@lem5322878)). Qed.
Lemma lem5322880 : term543 = term192.
Proof. exact (@lem5322830 (@lem5322879)). Qed.
Lemma lem5322881 : term542 = term192.
Proof. exact (TRANS (@lem5322796) (@lem5322880)). Qed.
Lemma lem5322883 (x : real) : (term266 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5322884 : term192 = term41.
Proof. exact (@lem5322883 term41). Qed.
Lemma lem5322885 : term542 = term41.
Proof. exact (TRANS (@lem5322881) (@lem5322884)). Qed.
Lemma lem5322886 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5322887 : term552 = term254.
Proof. exact (MK_COMB (@lem5322886) (@lem5322885)). Qed.
Lemma lem5322888 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5322889 (l : real) : (term540 l) = (term268 l).
Proof. exact (MK_COMB (@lem5322887) (@lem5322888 l)). Qed.
Lemma lem5322890 (l : real) : (term539 l) = (term268 l).
Proof. exact (TRANS (@lem5322787 l) (@lem5322889 l)). Qed.
Lemma lem5322891 (l : real) : (term268 l) = term41.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5322892 (l : real) : (term539 l) = term41.
Proof. exact (TRANS (@lem5322890 l) (@lem5322891 l)). Qed.
Lemma lem5322893 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5322894 (l : real) : (term553 l) = term270.
Proof. exact (MK_COMB (@lem5322893) (@lem5322892 l)). Qed.
Lemma lem5322895 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5322896 (l : real) (y : real) : (term538 l y) = (term554 y).
Proof. exact (MK_COMB (@lem5322894 l) (@lem5322895 y)). Qed.
Lemma lem5322897 (l : real) (y : real) : (term537 l y) = (term554 y).
Proof. exact (TRANS (@lem5322786 l y) (@lem5322896 l y)). Qed.
Lemma lem5322898 (y : real) : (term554 y) = y.
Proof. exact (@lem1982721 y). Qed.
Lemma lem5322899 (l : real) (y : real) : (term537 l y) = y.
Proof. exact (TRANS (@lem5322897 l y) (@lem5322898 y)). Qed.
Lemma lem5322900 (c : real) : (term555 c) = (term555 c).
Proof. exact (eq_refl (term555 c)). Qed.
Lemma lem5322901 (l : real) (c : real) (y : real) : (term536 c l y) = (term494 c y).
Proof. exact (MK_COMB (@lem5322900 c) (@lem5322899 l y)). Qed.
Lemma lem5322902 (l : real) (c : real) (y : real) : (term535 c l y) = (term494 c y).
Proof. exact (TRANS (@lem5322785 c l y) (@lem5322901 l c y)). Qed.
Lemma lem5322903 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5322904 (l : real) (c : real) (y : real) : (term556 c l y) = (term495 c y).
Proof. exact (MK_COMB (@lem5322903) (@lem5322902 l c y)). Qed.
Lemma lem5322905 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5322906 (l : real) (c : real) (y : real) : (term534 c l y) = (term496 c y).
Proof. exact (MK_COMB (@lem5322904 l c y) (@lem5322905)). Qed.
Lemma lem5322907 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term496 c y.
Proof. exact (EQ_MP (@lem5322906 l c y) (@lem5322784 m t c s x l y h1)). Qed.
Lemma lem5322909 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5322910 : term191 = term115.
Proof. exact (@lem5322909 term41 term76). Qed.
Lemma lem5322912 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5322913 : term76 = term105.
Proof. exact (@lem5322912 term70). Qed.
Lemma lem5322915 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5322916 : term41 = term192.
Proof. exact (@lem5322915 (NUMERAL 0)). Qed.
Lemma lem5322917 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5322918 : term193 = term194.
Proof. exact (MK_COMB (@lem5322917) (@lem5322916)). Qed.
Lemma lem5322919 : term115 = term195.
Proof. exact (MK_COMB (@lem5322918) (@lem5322913)). Qed.
Lemma lem5322920 : term196.
Proof. exact (@lem1980255 term41 term76 term76 term76). Qed.
Lemma lem5322922 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322923 : term115 = term116.
Proof. exact (@lem5322922 (NUMERAL 0) term70). Qed.
Lemma lem5322924 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322925 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322926 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322925 h1) (fun h1 : term116 = True => @lem5322924)). Qed.
Lemma lem5322927 : term116 = True.
Proof. exact (EQ_MP (@lem5322926) (@lem5322924)). Qed.
Lemma lem5322928 : term115 = True.
Proof. exact (TRANS (@lem5322923) (@lem5322927)). Qed.
Lemma lem5322929 : True = term115.
Proof. exact (SYM (@lem5322928)). Qed.
Lemma lem5322930 : term115.
Proof. exact (EQ_MP (@lem5322929) (@lem0)). Qed.
Lemma lem5322931 : term197.
Proof. exact (@lem5322920 (@lem5322930)). Qed.
Lemma lem5322933 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322934 : term115 = term116.
Proof. exact (@lem5322933 (NUMERAL 0) term70). Qed.
Lemma lem5322935 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322936 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322937 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322936 h1) (fun h1 : term116 = True => @lem5322935)). Qed.
Lemma lem5322938 : term116 = True.
Proof. exact (EQ_MP (@lem5322937) (@lem5322935)). Qed.
Lemma lem5322939 : term115 = True.
Proof. exact (TRANS (@lem5322934) (@lem5322938)). Qed.
Lemma lem5322940 : True = term115.
Proof. exact (SYM (@lem5322939)). Qed.
Lemma lem5322941 : term115.
Proof. exact (EQ_MP (@lem5322940) (@lem0)). Qed.
Lemma lem5322942 : term195 = term198.
Proof. exact (@lem5322931 (@lem5322941)). Qed.
Lemma lem5322944 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5322945 : term163 = term90.
Proof. exact (@lem5322944 term70 term70). Qed.
Lemma lem5322946 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5322947 : term89 = term70.
Proof. exact (EQ_MP (@lem5322946) (@lem940073)). Qed.
Lemma lem5322948 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5322949 : term90 = term76.
Proof. exact (MK_COMB (@lem5322948) (@lem5322947)). Qed.
Lemma lem5322950 : term163 = term76.
Proof. exact (TRANS (@lem5322945) (@lem5322949)). Qed.
Lemma lem5322952 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5322953 : term200 = term41.
Proof. exact (@lem5322952 term70). Qed.
Lemma lem5322954 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5322955 : term201 = term193.
Proof. exact (MK_COMB (@lem5322954) (@lem5322953)). Qed.
Lemma lem5322956 : term198 = term115.
Proof. exact (MK_COMB (@lem5322955) (@lem5322950)). Qed.
Lemma lem5322958 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5322959 : term115 = term116.
Proof. exact (@lem5322958 (NUMERAL 0) term70). Qed.
Lemma lem5322960 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5322961 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5322962 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5322961 h1) (fun h1 : term116 = True => @lem5322960)). Qed.
Lemma lem5322963 : term116 = True.
Proof. exact (EQ_MP (@lem5322962) (@lem5322960)). Qed.
Lemma lem5322964 : term115 = True.
Proof. exact (TRANS (@lem5322959) (@lem5322963)). Qed.
Lemma lem5322965 : term198 = True.
Proof. exact (TRANS (@lem5322956) (@lem5322964)). Qed.
Lemma lem5322966 : term195 = True.
Proof. exact (TRANS (@lem5322942) (@lem5322965)). Qed.
Lemma lem5322967 : term115 = True.
Proof. exact (TRANS (@lem5322919) (@lem5322966)). Qed.
Lemma lem5322968 : term191 = True.
Proof. exact (TRANS (@lem5322910) (@lem5322967)). Qed.
Lemma lem5322969 : True = term191.
Proof. exact (SYM (@lem5322968)). Qed.
Lemma lem5322970 : term191.
Proof. exact (EQ_MP (@lem5322969) (@lem0)). Qed.
Lemma lem5322971 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term528 c y.
Proof. exact (conj (@lem5322970) (@lem5322907 m t c s x l y h1)). Qed.
Lemma lem5322973 (x : real) (y : real) : term217 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5322974 (c : real) (y : real) : term529 c y.
Proof. exact (@lem5322973 term76 (term494 c y)). Qed.
Lemma lem5322975 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term530 c y.
Proof. exact (@lem5322974 c y (@lem5322971 m t c s x l y h1)). Qed.
Lemma lem5322976 (c : real) (y : real) : (term526 c y) = (term494 c y).
Proof. exact (@lem1982733 (term494 c y)). Qed.
Lemma lem5322977 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5322978 (c : real) (y : real) : (term531 c y) = (term495 c y).
Proof. exact (MK_COMB (@lem5322977) (@lem5322976 c y)). Qed.
Lemma lem5322979 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5322980 (c : real) (y : real) : (term530 c y) = (term496 c y).
Proof. exact (MK_COMB (@lem5322978 c y) (@lem5322979)). Qed.
Lemma lem5322981 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term496 c y.
Proof. exact (EQ_MP (@lem5322980 c y) (@lem5322975 m t c s x l y h1)). Qed.
Lemma lem5322982 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term557 y c x.
Proof. exact (conj (@lem5322981 m t c s x l y h1) (@lem5322631 m t c s x l y h1)). Qed.
Lemma lem5322984 (x : real) (y : real) : term558 x y.
Proof. exact (proj2 (@lem1988348 x y)). Qed.
Lemma lem5322985 (y : real) (c : real) (x : real) : term559 y c x.
Proof. exact (@lem5322984 (term494 c y) (term38 c x)). Qed.
Lemma lem5322986 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term560 y c x.
Proof. exact (@lem5322985 y c x (@lem5322982 m t c s x l y h1)). Qed.
Lemma lem5322987 (c : real) (y : real) (x : real) : (term561 y c x) = (term562 c y x).
Proof. exact (@lem1982753 (term150 c) c y (term150 x)). Qed.
Lemma lem5322988 (c : real) : (term563 c) = (term540 c).
Proof. exact (@lem1982713 term64 c). Qed.
Lemma lem5322990 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5322991 : term76 = term105.
Proof. exact (@lem5322990 term70). Qed.
Lemma lem5322993 (x : nat) : (term67 x) = (term68 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5322994 : term64 = term69.
Proof. exact (@lem5322993 term70). Qed.
Lemma lem5322995 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5322996 : term121 = term541.
Proof. exact (MK_COMB (@lem5322995) (@lem5322994)). Qed.
Lemma lem5322997 : term542 = term543.
Proof. exact (MK_COMB (@lem5322996) (@lem5322991)). Qed.
Lemma lem5322998 : term544.
Proof. exact (@lem1981473 term64 term76 term76 term76 term41 term76). Qed.
Lemma lem5323000 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323001 : term115 = term116.
Proof. exact (@lem5323000 (NUMERAL 0) term70). Qed.
Lemma lem5323002 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5323003 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5323004 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5323003 h1) (fun h1 : term116 = True => @lem5323002)). Qed.
Lemma lem5323005 : term116 = True.
Proof. exact (EQ_MP (@lem5323004) (@lem5323002)). Qed.
Lemma lem5323006 : term115 = True.
Proof. exact (TRANS (@lem5323001) (@lem5323005)). Qed.
Lemma lem5323007 : True = term115.
Proof. exact (SYM (@lem5323006)). Qed.
Lemma lem5323008 : term115.
Proof. exact (EQ_MP (@lem5323007) (@lem0)). Qed.
Lemma lem5323009 : term545.
Proof. exact (@lem5322998 (@lem5323008)). Qed.
Lemma lem5323011 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323012 : term115 = term116.
Proof. exact (@lem5323011 (NUMERAL 0) term70). Qed.
Lemma lem5323013 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5323014 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5323015 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5323014 h1) (fun h1 : term116 = True => @lem5323013)). Qed.
Lemma lem5323016 : term116 = True.
Proof. exact (EQ_MP (@lem5323015) (@lem5323013)). Qed.
Lemma lem5323017 : term115 = True.
Proof. exact (TRANS (@lem5323012) (@lem5323016)). Qed.
Lemma lem5323018 : True = term115.
Proof. exact (SYM (@lem5323017)). Qed.
Lemma lem5323019 : term115.
Proof. exact (EQ_MP (@lem5323018) (@lem0)). Qed.
Lemma lem5323020 : term546.
Proof. exact (@lem5323009 (@lem5323019)). Qed.
Lemma lem5323022 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323023 : term115 = term116.
Proof. exact (@lem5323022 (NUMERAL 0) term70). Qed.
Lemma lem5323024 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5323025 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5323026 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5323025 h1) (fun h1 : term116 = True => @lem5323024)). Qed.
Lemma lem5323027 : term116 = True.
Proof. exact (EQ_MP (@lem5323026) (@lem5323024)). Qed.
Lemma lem5323028 : term115 = True.
Proof. exact (TRANS (@lem5323023) (@lem5323027)). Qed.
Lemma lem5323029 : True = term115.
Proof. exact (SYM (@lem5323028)). Qed.
Lemma lem5323030 : term115.
Proof. exact (EQ_MP (@lem5323029) (@lem0)). Qed.
Lemma lem5323031 : term547.
Proof. exact (@lem5323020 (@lem5323030)). Qed.
Lemma lem5323033 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5323034 : term163 = term90.
Proof. exact (@lem5323033 term70 term70). Qed.
Lemma lem5323035 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5323036 : term89 = term70.
Proof. exact (EQ_MP (@lem5323035) (@lem940073)). Qed.
Lemma lem5323037 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323038 : term90 = term76.
Proof. exact (MK_COMB (@lem5323037) (@lem5323036)). Qed.
Lemma lem5323039 : term163 = term76.
Proof. exact (TRANS (@lem5323034) (@lem5323038)). Qed.
Lemma lem5323041 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5323042 : term86 = term87.
Proof. exact (@lem5323041 term70 term70). Qed.
Lemma lem5323043 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5323044 : term89 = term70.
Proof. exact (EQ_MP (@lem5323043) (@lem940073)). Qed.
Lemma lem5323045 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323046 : term90 = term76.
Proof. exact (MK_COMB (@lem5323045) (@lem5323044)). Qed.
Lemma lem5323047 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5323048 : term87 = term64.
Proof. exact (MK_COMB (@lem5323047) (@lem5323046)). Qed.
Lemma lem5323049 : term86 = term64.
Proof. exact (TRANS (@lem5323042) (@lem5323048)). Qed.
Lemma lem5323050 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5323051 : term120 = term121.
Proof. exact (MK_COMB (@lem5323050) (@lem5323049)). Qed.
Lemma lem5323052 : term548 = term542.
Proof. exact (MK_COMB (@lem5323051) (@lem5323039)). Qed.
Lemma lem5323054 (m : nat) : (term281 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5323055 : term542 = term41.
Proof. exact (@lem5323054 term70). Qed.
Lemma lem5323056 : term548 = term41.
Proof. exact (TRANS (@lem5323052) (@lem5323055)). Qed.
Lemma lem5323057 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5323058 : term549 = term254.
Proof. exact (MK_COMB (@lem5323057) (@lem5323056)). Qed.
Lemma lem5323059 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem5323060 : term550 = term200.
Proof. exact (MK_COMB (@lem5323058) (@lem5323059)). Qed.
Lemma lem5323062 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5323063 : term200 = term41.
Proof. exact (@lem5323062 term70). Qed.
Lemma lem5323064 : term550 = term41.
Proof. exact (TRANS (@lem5323060) (@lem5323063)). Qed.
Lemma lem5323066 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5323067 : term163 = term90.
Proof. exact (@lem5323066 term70 term70). Qed.
Lemma lem5323068 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5323069 : term89 = term70.
Proof. exact (EQ_MP (@lem5323068) (@lem940073)). Qed.
Lemma lem5323070 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323071 : term90 = term76.
Proof. exact (MK_COMB (@lem5323070) (@lem5323069)). Qed.
Lemma lem5323072 : term163 = term76.
Proof. exact (TRANS (@lem5323067) (@lem5323071)). Qed.
Lemma lem5323073 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5323074 : term551 = term200.
Proof. exact (MK_COMB (@lem5323073) (@lem5323072)). Qed.
Lemma lem5323076 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5323077 : term200 = term41.
Proof. exact (@lem5323076 term70). Qed.
Lemma lem5323078 : term551 = term41.
Proof. exact (TRANS (@lem5323074) (@lem5323077)). Qed.
Lemma lem5323079 : term41 = term551.
Proof. exact (SYM (@lem5323078)). Qed.
Lemma lem5323080 : term550 = term551.
Proof. exact (TRANS (@lem5323064) (@lem5323079)). Qed.
Lemma lem5323081 : term543 = term192.
Proof. exact (@lem5323031 (@lem5323080)). Qed.
Lemma lem5323082 : term542 = term192.
Proof. exact (TRANS (@lem5322997) (@lem5323081)). Qed.
Lemma lem5323084 (x : real) : (term266 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5323085 : term192 = term41.
Proof. exact (@lem5323084 term41). Qed.
Lemma lem5323086 : term542 = term41.
Proof. exact (TRANS (@lem5323082) (@lem5323085)). Qed.
Lemma lem5323087 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5323088 : term552 = term254.
Proof. exact (MK_COMB (@lem5323087) (@lem5323086)). Qed.
Lemma lem5323089 (c : real) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem5323090 (c : real) : (term540 c) = (term268 c).
Proof. exact (MK_COMB (@lem5323088) (@lem5323089 c)). Qed.
Lemma lem5323091 (c : real) : (term563 c) = (term268 c).
Proof. exact (TRANS (@lem5322988 c) (@lem5323090 c)). Qed.
Lemma lem5323092 (c : real) : (term268 c) = term41.
Proof. exact (@lem1982719 c). Qed.
Lemma lem5323093 (c : real) : (term563 c) = term41.
Proof. exact (TRANS (@lem5323091 c) (@lem5323092 c)). Qed.
Lemma lem5323094 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5323095 (c : real) : (term564 c) = term270.
Proof. exact (MK_COMB (@lem5323094) (@lem5323093 c)). Qed.
Lemma lem5323096 (x : real) (y : real) : (term38 y x) = (term494 x y).
Proof. exact (@lem1982761 (term150 x) y). Qed.
Lemma lem5323097 (c : real) (x : real) (y : real) : (term562 c y x) = (term565 x y).
Proof. exact (MK_COMB (@lem5323095 c) (@lem5323096 x y)). Qed.
Lemma lem5323098 (c : real) (x : real) (y : real) : (term561 y c x) = (term565 x y).
Proof. exact (TRANS (@lem5322987 c y x) (@lem5323097 c x y)). Qed.
Lemma lem5323099 (x : real) (y : real) : (term565 x y) = (term494 x y).
Proof. exact (@lem1982721 (term494 x y)). Qed.
Lemma lem5323100 (c : real) (x : real) (y : real) : (term561 y c x) = (term494 x y).
Proof. exact (TRANS (@lem5323098 c x y) (@lem5323099 x y)). Qed.
Lemma lem5323101 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5323102 (c : real) (x : real) (y : real) : (term566 y c x) = (term495 x y).
Proof. exact (MK_COMB (@lem5323101) (@lem5323100 c x y)). Qed.
Lemma lem5323103 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5323104 (c : real) (x : real) (y : real) : (term560 y c x) = (term496 x y).
Proof. exact (MK_COMB (@lem5323102 c x y) (@lem5323103)). Qed.
Lemma lem5323105 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term496 x y.
Proof. exact (EQ_MP (@lem5323104 c x y) (@lem5322986 m t c s x l y h1)). Qed.
Lemma lem5323107 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5323108 : term191 = term115.
Proof. exact (@lem5323107 term41 term76). Qed.
Lemma lem5323110 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5323111 : term76 = term105.
Proof. exact (@lem5323110 term70). Qed.
Lemma lem5323113 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5323114 : term41 = term192.
Proof. exact (@lem5323113 (NUMERAL 0)). Qed.
Lemma lem5323115 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5323116 : term193 = term194.
Proof. exact (MK_COMB (@lem5323115) (@lem5323114)). Qed.
Lemma lem5323117 : term115 = term195.
Proof. exact (MK_COMB (@lem5323116) (@lem5323111)). Qed.
Lemma lem5323118 : term196.
Proof. exact (@lem1980255 term41 term76 term76 term76). Qed.
Lemma lem5323120 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323121 : term115 = term116.
Proof. exact (@lem5323120 (NUMERAL 0) term70). Qed.
Lemma lem5323122 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5323123 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5323124 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5323123 h1) (fun h1 : term116 = True => @lem5323122)). Qed.
Lemma lem5323125 : term116 = True.
Proof. exact (EQ_MP (@lem5323124) (@lem5323122)). Qed.
Lemma lem5323126 : term115 = True.
Proof. exact (TRANS (@lem5323121) (@lem5323125)). Qed.
Lemma lem5323127 : True = term115.
Proof. exact (SYM (@lem5323126)). Qed.
Lemma lem5323128 : term115.
Proof. exact (EQ_MP (@lem5323127) (@lem0)). Qed.
Lemma lem5323129 : term197.
Proof. exact (@lem5323118 (@lem5323128)). Qed.
Lemma lem5323131 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323132 : term115 = term116.
Proof. exact (@lem5323131 (NUMERAL 0) term70). Qed.
Lemma lem5323133 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5323134 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5323135 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5323134 h1) (fun h1 : term116 = True => @lem5323133)). Qed.
Lemma lem5323136 : term116 = True.
Proof. exact (EQ_MP (@lem5323135) (@lem5323133)). Qed.
Lemma lem5323137 : term115 = True.
Proof. exact (TRANS (@lem5323132) (@lem5323136)). Qed.
Lemma lem5323138 : True = term115.
Proof. exact (SYM (@lem5323137)). Qed.
Lemma lem5323139 : term115.
Proof. exact (EQ_MP (@lem5323138) (@lem0)). Qed.
Lemma lem5323140 : term195 = term198.
Proof. exact (@lem5323129 (@lem5323139)). Qed.
Lemma lem5323142 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5323143 : term163 = term90.
Proof. exact (@lem5323142 term70 term70). Qed.
Lemma lem5323144 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5323145 : term89 = term70.
Proof. exact (EQ_MP (@lem5323144) (@lem940073)). Qed.
Lemma lem5323146 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323147 : term90 = term76.
Proof. exact (MK_COMB (@lem5323146) (@lem5323145)). Qed.
Lemma lem5323148 : term163 = term76.
Proof. exact (TRANS (@lem5323143) (@lem5323147)). Qed.
Lemma lem5323150 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5323151 : term200 = term41.
Proof. exact (@lem5323150 term70). Qed.
Lemma lem5323152 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5323153 : term201 = term193.
Proof. exact (MK_COMB (@lem5323152) (@lem5323151)). Qed.
Lemma lem5323154 : term198 = term115.
Proof. exact (MK_COMB (@lem5323153) (@lem5323148)). Qed.
Lemma lem5323156 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323157 : term115 = term116.
Proof. exact (@lem5323156 (NUMERAL 0) term70). Qed.
Lemma lem5323158 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5323159 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5323160 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5323159 h1) (fun h1 : term116 = True => @lem5323158)). Qed.
Lemma lem5323161 : term116 = True.
Proof. exact (EQ_MP (@lem5323160) (@lem5323158)). Qed.
Lemma lem5323162 : term115 = True.
Proof. exact (TRANS (@lem5323157) (@lem5323161)). Qed.
Lemma lem5323163 : term198 = True.
Proof. exact (TRANS (@lem5323154) (@lem5323162)). Qed.
Lemma lem5323164 : term195 = True.
Proof. exact (TRANS (@lem5323140) (@lem5323163)). Qed.
Lemma lem5323165 : term115 = True.
Proof. exact (TRANS (@lem5323117) (@lem5323164)). Qed.
Lemma lem5323166 : term191 = True.
Proof. exact (TRANS (@lem5323108) (@lem5323165)). Qed.
Lemma lem5323167 : True = term191.
Proof. exact (SYM (@lem5323166)). Qed.
Lemma lem5323168 : term191.
Proof. exact (EQ_MP (@lem5323167) (@lem0)). Qed.
Lemma lem5323169 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term528 x y.
Proof. exact (conj (@lem5323168) (@lem5323105 m t c s x l y h1)). Qed.
Lemma lem5323171 (x : real) (y : real) : term217 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5323172 (x : real) (y : real) : term529 x y.
Proof. exact (@lem5323171 term76 (term494 x y)). Qed.
Lemma lem5323173 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term530 x y.
Proof. exact (@lem5323172 x y (@lem5323169 m t c s x l y h1)). Qed.
Lemma lem5323174 (x : real) (y : real) : (term526 x y) = (term494 x y).
Proof. exact (@lem1982733 (term494 x y)). Qed.
Lemma lem5323175 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5323176 (x : real) (y : real) : (term531 x y) = (term495 x y).
Proof. exact (MK_COMB (@lem5323175) (@lem5323174 x y)). Qed.
Lemma lem5323177 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5323178 (x : real) (y : real) : (term530 x y) = (term496 x y).
Proof. exact (MK_COMB (@lem5323176 x y) (@lem5323177)). Qed.
Lemma lem5323179 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term496 x y.
Proof. exact (EQ_MP (@lem5323178 x y) (@lem5323173 m t c s x l y h1)). Qed.
Lemma lem5323180 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term567 x y.
Proof. exact (conj (@lem5323179 m t c s x l y h1) (@lem5322557 m t c s x l y h1)). Qed.
Lemma lem5323182 (x : real) (y : real) : term237 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5323183 (x : real) (y : real) : term568 x y.
Proof. exact (@lem5323182 (term494 x y) (term38 x y)). Qed.
Lemma lem5323184 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term569 x y.
Proof. exact (@lem5323183 x y (@lem5323180 m t c s x l y h1)). Qed.
Lemma lem5323185 (x : real) (y : real) : (term570 x y) = (term571 x y).
Proof. exact (@lem1982753 (term150 x) x y (term150 y)). Qed.
Lemma lem5323186 (x : real) : (term563 x) = (term540 x).
Proof. exact (@lem1982713 term64 x). Qed.
Lemma lem5323188 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5323189 : term76 = term105.
Proof. exact (@lem5323188 term70). Qed.
Lemma lem5323191 (x : nat) : (term67 x) = (term68 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5323192 : term64 = term69.
Proof. exact (@lem5323191 term70). Qed.
Lemma lem5323193 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5323194 : term121 = term541.
Proof. exact (MK_COMB (@lem5323193) (@lem5323192)). Qed.
Lemma lem5323195 : term542 = term543.
Proof. exact (MK_COMB (@lem5323194) (@lem5323189)). Qed.
Lemma lem5323196 : term544.
Proof. exact (@lem1981473 term64 term76 term76 term76 term41 term76). Qed.
Lemma lem5323198 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323199 : term115 = term116.
Proof. exact (@lem5323198 (NUMERAL 0) term70). Qed.
Lemma lem5323200 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5323201 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5323202 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5323201 h1) (fun h1 : term116 = True => @lem5323200)). Qed.
Lemma lem5323203 : term116 = True.
Proof. exact (EQ_MP (@lem5323202) (@lem5323200)). Qed.
Lemma lem5323204 : term115 = True.
Proof. exact (TRANS (@lem5323199) (@lem5323203)). Qed.
Lemma lem5323205 : True = term115.
Proof. exact (SYM (@lem5323204)). Qed.
Lemma lem5323206 : term115.
Proof. exact (EQ_MP (@lem5323205) (@lem0)). Qed.
Lemma lem5323207 : term545.
Proof. exact (@lem5323196 (@lem5323206)). Qed.
Lemma lem5323209 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323210 : term115 = term116.
Proof. exact (@lem5323209 (NUMERAL 0) term70). Qed.
Lemma lem5323211 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5323212 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5323213 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5323212 h1) (fun h1 : term116 = True => @lem5323211)). Qed.
Lemma lem5323214 : term116 = True.
Proof. exact (EQ_MP (@lem5323213) (@lem5323211)). Qed.
Lemma lem5323215 : term115 = True.
Proof. exact (TRANS (@lem5323210) (@lem5323214)). Qed.
Lemma lem5323216 : True = term115.
Proof. exact (SYM (@lem5323215)). Qed.
Lemma lem5323217 : term115.
Proof. exact (EQ_MP (@lem5323216) (@lem0)). Qed.
Lemma lem5323218 : term546.
Proof. exact (@lem5323207 (@lem5323217)). Qed.
Lemma lem5323220 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323221 : term115 = term116.
Proof. exact (@lem5323220 (NUMERAL 0) term70). Qed.
Lemma lem5323222 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5323223 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5323224 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5323223 h1) (fun h1 : term116 = True => @lem5323222)). Qed.
Lemma lem5323225 : term116 = True.
Proof. exact (EQ_MP (@lem5323224) (@lem5323222)). Qed.
Lemma lem5323226 : term115 = True.
Proof. exact (TRANS (@lem5323221) (@lem5323225)). Qed.
Lemma lem5323227 : True = term115.
Proof. exact (SYM (@lem5323226)). Qed.
Lemma lem5323228 : term115.
Proof. exact (EQ_MP (@lem5323227) (@lem0)). Qed.
Lemma lem5323229 : term547.
Proof. exact (@lem5323218 (@lem5323228)). Qed.
Lemma lem5323231 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5323232 : term163 = term90.
Proof. exact (@lem5323231 term70 term70). Qed.
Lemma lem5323233 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5323234 : term89 = term70.
Proof. exact (EQ_MP (@lem5323233) (@lem940073)). Qed.
Lemma lem5323235 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323236 : term90 = term76.
Proof. exact (MK_COMB (@lem5323235) (@lem5323234)). Qed.
Lemma lem5323237 : term163 = term76.
Proof. exact (TRANS (@lem5323232) (@lem5323236)). Qed.
Lemma lem5323239 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5323240 : term86 = term87.
Proof. exact (@lem5323239 term70 term70). Qed.
Lemma lem5323241 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5323242 : term89 = term70.
Proof. exact (EQ_MP (@lem5323241) (@lem940073)). Qed.
Lemma lem5323243 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323244 : term90 = term76.
Proof. exact (MK_COMB (@lem5323243) (@lem5323242)). Qed.
Lemma lem5323245 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5323246 : term87 = term64.
Proof. exact (MK_COMB (@lem5323245) (@lem5323244)). Qed.
Lemma lem5323247 : term86 = term64.
Proof. exact (TRANS (@lem5323240) (@lem5323246)). Qed.
Lemma lem5323248 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5323249 : term120 = term121.
Proof. exact (MK_COMB (@lem5323248) (@lem5323247)). Qed.
Lemma lem5323250 : term548 = term542.
Proof. exact (MK_COMB (@lem5323249) (@lem5323237)). Qed.
Lemma lem5323252 (m : nat) : (term281 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5323253 : term542 = term41.
Proof. exact (@lem5323252 term70). Qed.
Lemma lem5323254 : term548 = term41.
Proof. exact (TRANS (@lem5323250) (@lem5323253)). Qed.
Lemma lem5323255 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5323256 : term549 = term254.
Proof. exact (MK_COMB (@lem5323255) (@lem5323254)). Qed.
Lemma lem5323257 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem5323258 : term550 = term200.
Proof. exact (MK_COMB (@lem5323256) (@lem5323257)). Qed.
Lemma lem5323260 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5323261 : term200 = term41.
Proof. exact (@lem5323260 term70). Qed.
Lemma lem5323262 : term550 = term41.
Proof. exact (TRANS (@lem5323258) (@lem5323261)). Qed.
Lemma lem5323264 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5323265 : term163 = term90.
Proof. exact (@lem5323264 term70 term70). Qed.
Lemma lem5323266 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5323267 : term89 = term70.
Proof. exact (EQ_MP (@lem5323266) (@lem940073)). Qed.
Lemma lem5323268 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323269 : term90 = term76.
Proof. exact (MK_COMB (@lem5323268) (@lem5323267)). Qed.
Lemma lem5323270 : term163 = term76.
Proof. exact (TRANS (@lem5323265) (@lem5323269)). Qed.
Lemma lem5323271 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5323272 : term551 = term200.
Proof. exact (MK_COMB (@lem5323271) (@lem5323270)). Qed.
Lemma lem5323274 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5323275 : term200 = term41.
Proof. exact (@lem5323274 term70). Qed.
Lemma lem5323276 : term551 = term41.
Proof. exact (TRANS (@lem5323272) (@lem5323275)). Qed.
Lemma lem5323277 : term41 = term551.
Proof. exact (SYM (@lem5323276)). Qed.
Lemma lem5323278 : term550 = term551.
Proof. exact (TRANS (@lem5323262) (@lem5323277)). Qed.
Lemma lem5323279 : term543 = term192.
Proof. exact (@lem5323229 (@lem5323278)). Qed.
Lemma lem5323280 : term542 = term192.
Proof. exact (TRANS (@lem5323195) (@lem5323279)). Qed.
Lemma lem5323282 (x : real) : (term266 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5323283 : term192 = term41.
Proof. exact (@lem5323282 term41). Qed.
Lemma lem5323284 : term542 = term41.
Proof. exact (TRANS (@lem5323280) (@lem5323283)). Qed.
Lemma lem5323285 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5323286 : term552 = term254.
Proof. exact (MK_COMB (@lem5323285) (@lem5323284)). Qed.
Lemma lem5323287 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5323288 (x : real) : (term540 x) = (term268 x).
Proof. exact (MK_COMB (@lem5323286) (@lem5323287 x)). Qed.
Lemma lem5323289 (x : real) : (term563 x) = (term268 x).
Proof. exact (TRANS (@lem5323186 x) (@lem5323288 x)). Qed.
Lemma lem5323290 (x : real) : (term268 x) = term41.
Proof. exact (@lem1982719 x). Qed.
Lemma lem5323291 (x : real) : (term563 x) = term41.
Proof. exact (TRANS (@lem5323289 x) (@lem5323290 x)). Qed.
Lemma lem5323292 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5323293 (x : real) : (term564 x) = term270.
Proof. exact (MK_COMB (@lem5323292) (@lem5323291 x)). Qed.
Lemma lem5323294 (y : real) : (term539 y) = (term540 y).
Proof. exact (@lem1982715 term64 y). Qed.
Lemma lem5323296 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5323297 : term76 = term105.
Proof. exact (@lem5323296 term70). Qed.
Lemma lem5323299 (x : nat) : (term67 x) = (term68 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5323300 : term64 = term69.
Proof. exact (@lem5323299 term70). Qed.
Lemma lem5323301 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5323302 : term121 = term541.
Proof. exact (MK_COMB (@lem5323301) (@lem5323300)). Qed.
Lemma lem5323303 : term542 = term543.
Proof. exact (MK_COMB (@lem5323302) (@lem5323297)). Qed.
Lemma lem5323304 : term544.
Proof. exact (@lem1981473 term64 term76 term76 term76 term41 term76). Qed.
Lemma lem5323306 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323307 : term115 = term116.
Proof. exact (@lem5323306 (NUMERAL 0) term70). Qed.
Lemma lem5323308 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5323309 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5323310 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5323309 h1) (fun h1 : term116 = True => @lem5323308)). Qed.
Lemma lem5323311 : term116 = True.
Proof. exact (EQ_MP (@lem5323310) (@lem5323308)). Qed.
Lemma lem5323312 : term115 = True.
Proof. exact (TRANS (@lem5323307) (@lem5323311)). Qed.
Lemma lem5323313 : True = term115.
Proof. exact (SYM (@lem5323312)). Qed.
Lemma lem5323314 : term115.
Proof. exact (EQ_MP (@lem5323313) (@lem0)). Qed.
Lemma lem5323315 : term545.
Proof. exact (@lem5323304 (@lem5323314)). Qed.
Lemma lem5323317 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323318 : term115 = term116.
Proof. exact (@lem5323317 (NUMERAL 0) term70). Qed.
Lemma lem5323319 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5323320 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5323321 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5323320 h1) (fun h1 : term116 = True => @lem5323319)). Qed.
Lemma lem5323322 : term116 = True.
Proof. exact (EQ_MP (@lem5323321) (@lem5323319)). Qed.
Lemma lem5323323 : term115 = True.
Proof. exact (TRANS (@lem5323318) (@lem5323322)). Qed.
Lemma lem5323324 : True = term115.
Proof. exact (SYM (@lem5323323)). Qed.
Lemma lem5323325 : term115.
Proof. exact (EQ_MP (@lem5323324) (@lem0)). Qed.
Lemma lem5323326 : term546.
Proof. exact (@lem5323315 (@lem5323325)). Qed.
Lemma lem5323328 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323329 : term115 = term116.
Proof. exact (@lem5323328 (NUMERAL 0) term70). Qed.
Lemma lem5323330 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5323331 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5323332 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5323331 h1) (fun h1 : term116 = True => @lem5323330)). Qed.
Lemma lem5323333 : term116 = True.
Proof. exact (EQ_MP (@lem5323332) (@lem5323330)). Qed.
Lemma lem5323334 : term115 = True.
Proof. exact (TRANS (@lem5323329) (@lem5323333)). Qed.
Lemma lem5323335 : True = term115.
Proof. exact (SYM (@lem5323334)). Qed.
Lemma lem5323336 : term115.
Proof. exact (EQ_MP (@lem5323335) (@lem0)). Qed.
Lemma lem5323337 : term547.
Proof. exact (@lem5323326 (@lem5323336)). Qed.
Lemma lem5323339 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5323340 : term163 = term90.
Proof. exact (@lem5323339 term70 term70). Qed.
Lemma lem5323341 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5323342 : term89 = term70.
Proof. exact (EQ_MP (@lem5323341) (@lem940073)). Qed.
Lemma lem5323343 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323344 : term90 = term76.
Proof. exact (MK_COMB (@lem5323343) (@lem5323342)). Qed.
Lemma lem5323345 : term163 = term76.
Proof. exact (TRANS (@lem5323340) (@lem5323344)). Qed.
Lemma lem5323347 (m : nat) (n : nat) : (term84 m n) = (term85 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5323348 : term86 = term87.
Proof. exact (@lem5323347 term70 term70). Qed.
Lemma lem5323349 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5323350 : term89 = term70.
Proof. exact (EQ_MP (@lem5323349) (@lem940073)). Qed.
Lemma lem5323351 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323352 : term90 = term76.
Proof. exact (MK_COMB (@lem5323351) (@lem5323350)). Qed.
Lemma lem5323353 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5323354 : term87 = term64.
Proof. exact (MK_COMB (@lem5323353) (@lem5323352)). Qed.
Lemma lem5323355 : term86 = term64.
Proof. exact (TRANS (@lem5323348) (@lem5323354)). Qed.
Lemma lem5323356 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5323357 : term120 = term121.
Proof. exact (MK_COMB (@lem5323356) (@lem5323355)). Qed.
Lemma lem5323358 : term548 = term542.
Proof. exact (MK_COMB (@lem5323357) (@lem5323345)). Qed.
Lemma lem5323360 (m : nat) : (term281 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5323361 : term542 = term41.
Proof. exact (@lem5323360 term70). Qed.
Lemma lem5323362 : term548 = term41.
Proof. exact (TRANS (@lem5323358) (@lem5323361)). Qed.
Lemma lem5323363 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5323364 : term549 = term254.
Proof. exact (MK_COMB (@lem5323363) (@lem5323362)). Qed.
Lemma lem5323365 : term76 = term76.
Proof. exact (eq_refl term76). Qed.
Lemma lem5323366 : term550 = term200.
Proof. exact (MK_COMB (@lem5323364) (@lem5323365)). Qed.
Lemma lem5323368 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5323369 : term200 = term41.
Proof. exact (@lem5323368 term70). Qed.
Lemma lem5323370 : term550 = term41.
Proof. exact (TRANS (@lem5323366) (@lem5323369)). Qed.
Lemma lem5323372 (m : nat) (n : nat) : (term77 m n) = (term78 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5323373 : term163 = term90.
Proof. exact (@lem5323372 term70 term70). Qed.
Lemma lem5323374 : (term88 = (BIT1 0)) = (term89 = term70).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5323375 : term89 = term70.
Proof. exact (EQ_MP (@lem5323374) (@lem940073)). Qed.
Lemma lem5323376 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5323377 : term90 = term76.
Proof. exact (MK_COMB (@lem5323376) (@lem5323375)). Qed.
Lemma lem5323378 : term163 = term76.
Proof. exact (TRANS (@lem5323373) (@lem5323377)). Qed.
Lemma lem5323379 : term254 = term254.
Proof. exact (eq_refl term254). Qed.
Lemma lem5323380 : term551 = term200.
Proof. exact (MK_COMB (@lem5323379) (@lem5323378)). Qed.
Lemma lem5323382 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5323383 : term200 = term41.
Proof. exact (@lem5323382 term70). Qed.
Lemma lem5323384 : term551 = term41.
Proof. exact (TRANS (@lem5323380) (@lem5323383)). Qed.
Lemma lem5323385 : term41 = term551.
Proof. exact (SYM (@lem5323384)). Qed.
Lemma lem5323386 : term550 = term551.
Proof. exact (TRANS (@lem5323370) (@lem5323385)). Qed.
Lemma lem5323387 : term543 = term192.
Proof. exact (@lem5323337 (@lem5323386)). Qed.
Lemma lem5323388 : term542 = term192.
Proof. exact (TRANS (@lem5323303) (@lem5323387)). Qed.
Lemma lem5323390 (x : real) : (term266 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5323391 : term192 = term41.
Proof. exact (@lem5323390 term41). Qed.
Lemma lem5323392 : term542 = term41.
Proof. exact (TRANS (@lem5323388) (@lem5323391)). Qed.
Lemma lem5323393 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5323394 : term552 = term254.
Proof. exact (MK_COMB (@lem5323393) (@lem5323392)). Qed.
Lemma lem5323395 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem5323396 (y : real) : (term540 y) = (term268 y).
Proof. exact (MK_COMB (@lem5323394) (@lem5323395 y)). Qed.
Lemma lem5323397 (y : real) : (term539 y) = (term268 y).
Proof. exact (TRANS (@lem5323294 y) (@lem5323396 y)). Qed.
Lemma lem5323398 (y : real) : (term268 y) = term41.
Proof. exact (@lem1982719 y). Qed.
Lemma lem5323399 (y : real) : (term539 y) = term41.
Proof. exact (TRANS (@lem5323397 y) (@lem5323398 y)). Qed.
Lemma lem5323400 (x : real) (y : real) : (term571 x y) = term286.
Proof. exact (MK_COMB (@lem5323293 x) (@lem5323399 y)). Qed.
Lemma lem5323401 (x : real) (y : real) : (term570 x y) = term286.
Proof. exact (TRANS (@lem5323185 x y) (@lem5323400 x y)). Qed.
Lemma lem5323402 : term286 = term41.
Proof. exact (@lem1982721 term41). Qed.
Lemma lem5323403 (x : real) (y : real) : (term570 x y) = term41.
Proof. exact (TRANS (@lem5323401 x y) (@lem5323402)). Qed.
Lemma lem5323404 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5323405 (x : real) (y : real) : (term572 x y) = term288.
Proof. exact (MK_COMB (@lem5323404) (@lem5323403 x y)). Qed.
Lemma lem5323406 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem5323407 (x : real) (y : real) : (term569 x y) = term289.
Proof. exact (MK_COMB (@lem5323405 x y) (@lem5323406)). Qed.
Lemma lem5323408 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term289.
Proof. exact (EQ_MP (@lem5323407 x y) (@lem5323184 m t c s x l y h1)). Qed.
Lemma lem5323410 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5323411 : term289 = term290.
Proof. exact (@lem5323410 term41 term41). Qed.
Lemma lem5323413 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5323414 : term41 = term192.
Proof. exact (@lem5323413 (NUMERAL 0)). Qed.
Lemma lem5323416 (x : nat) : (real_of_num x) = (term104 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5323417 : term41 = term192.
Proof. exact (@lem5323416 (NUMERAL 0)). Qed.
Lemma lem5323418 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5323419 : term193 = term194.
Proof. exact (MK_COMB (@lem5323418) (@lem5323417)). Qed.
Lemma lem5323420 : term290 = term291.
Proof. exact (MK_COMB (@lem5323419) (@lem5323414)). Qed.
Lemma lem5323421 : term292.
Proof. exact (@lem1980255 term41 term76 term41 term76). Qed.
Lemma lem5323423 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323424 : term115 = term116.
Proof. exact (@lem5323423 (NUMERAL 0) term70). Qed.
Lemma lem5323425 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5323426 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5323427 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5323426 h1) (fun h1 : term116 = True => @lem5323425)). Qed.
Lemma lem5323428 : term116 = True.
Proof. exact (EQ_MP (@lem5323427) (@lem5323425)). Qed.
Lemma lem5323429 : term115 = True.
Proof. exact (TRANS (@lem5323424) (@lem5323428)). Qed.
Lemma lem5323430 : True = term115.
Proof. exact (SYM (@lem5323429)). Qed.
Lemma lem5323431 : term115.
Proof. exact (EQ_MP (@lem5323430) (@lem0)). Qed.
Lemma lem5323432 : term293.
Proof. exact (@lem5323421 (@lem5323431)). Qed.
Lemma lem5323434 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323435 : term115 = term116.
Proof. exact (@lem5323434 (NUMERAL 0) term70). Qed.
Lemma lem5323436 : term117 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5323437 (h1 : term117 = (BIT1 0)) : term116 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5323438 : (term117 = (BIT1 0)) = (term116 = True).
Proof. exact (prop_ext (fun h1 : term117 = (BIT1 0) => @lem5323437 h1) (fun h1 : term116 = True => @lem5323436)). Qed.
Lemma lem5323439 : term116 = True.
Proof. exact (EQ_MP (@lem5323438) (@lem5323436)). Qed.
Lemma lem5323440 : term115 = True.
Proof. exact (TRANS (@lem5323435) (@lem5323439)). Qed.
Lemma lem5323441 : True = term115.
Proof. exact (SYM (@lem5323440)). Qed.
Lemma lem5323442 : term115.
Proof. exact (EQ_MP (@lem5323441) (@lem0)). Qed.
Lemma lem5323443 : term291 = term294.
Proof. exact (@lem5323432 (@lem5323442)). Qed.
Lemma lem5323445 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5323446 : term200 = term41.
Proof. exact (@lem5323445 term70). Qed.
Lemma lem5323448 (x : nat) : (term199 x) = term41.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5323449 : term200 = term41.
Proof. exact (@lem5323448 term70). Qed.
Lemma lem5323450 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5323451 : term201 = term193.
Proof. exact (MK_COMB (@lem5323450) (@lem5323449)). Qed.
Lemma lem5323452 : term294 = term290.
Proof. exact (MK_COMB (@lem5323451) (@lem5323446)). Qed.
Lemma lem5323454 (m : nat) (n : nat) : (term110 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5323455 : term290 = term295.
Proof. exact (@lem5323454 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5323456 : term295 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5323457 : term290 = False.
Proof. exact (TRANS (@lem5323455) (@lem5323456)). Qed.
Lemma lem5323458 : term294 = False.
Proof. exact (TRANS (@lem5323452) (@lem5323457)). Qed.
Lemma lem5323459 : term291 = False.
Proof. exact (TRANS (@lem5323443) (@lem5323458)). Qed.
Lemma lem5323460 : term290 = False.
Proof. exact (TRANS (@lem5323420) (@lem5323459)). Qed.
Lemma lem5323461 : term289 = False.
Proof. exact (TRANS (@lem5323411) (@lem5323460)). Qed.
Lemma lem5323462 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : False.
Proof. exact (EQ_MP (@lem5323461) (@lem5323408 m t c s x l y h1)). Qed.
Lemma lem5323464 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : term513 m t c s x l y.
Proof. exact (h1). Qed.
Lemma lem5323465 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : (term513 m t c s x l y) = False.
Proof. exact (prop_ext (fun h2 : term513 m t c s x l y => @lem5323462 m t c s x l y h1) (fun h2 : False => @lem5323464 m t c s x l y h1)). Qed.
Lemma lem5323466 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term513 m t c s x l y) : False.
Proof. exact (EQ_MP (@lem5323465 m t c s x l y h1) (@lem5323464 m t c s x l y h1)). Qed.
Lemma lem5323467 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term492 m t c s x l y) : term492 m t c s x l y.
Proof. exact (h1). Qed.
Lemma lem5323468 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term492 m t c s x l y) : term513 m t c s x l y.
Proof. exact (EQ_MP (@lem5322461 m t c s x l y) (@lem5323467 m t c s x l y h1)). Qed.
Lemma lem5323469 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term492 m t c s x l y) : (term513 m t c s x l y) = False.
Proof. exact (prop_ext (fun h2 : term513 m t c s x l y => @lem5323466 m t c s x l y h2) (fun h2 : False => @lem5323468 m t c s x l y h1)). Qed.
Lemma lem5323470 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) (h1 : term492 m t c s x l y) : False.
Proof. exact (EQ_MP (@lem5323469 m t c s x l y h1) (@lem5323468 m t c s x l y h1)). Qed.
Lemma lem5323471 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : term573 m t c s x l y.
Proof. exact (fun h0 : term492 m t c s x l y => @lem5323470 m t c s x l y h0). Qed.
Lemma lem5323472 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : term574 m t c s x l y.
Proof. exact (@lem1386578 (term575 m t c s x l y)). Qed.
Lemma lem5323475 (m : real) (t : real -> Prop) (c : real) (s : real -> Prop) (x : real) (l : real) (y : real) : term575 m t c s x l y.
Proof. exact (@lem5323472 m t c s x l y (@lem5323471 m t c s x l y)). Qed.
Lemma lem5323476 (m : real) (t : real -> Prop) (c : real) (x : real) (l : real) (y : real) (s : real -> Prop) (h1 : term12 s) : term493 m t c s x l y.
Proof. exact (@lem5323475 m t c s x l y (@lem5319452 s h1)). Qed.
Lemma lem5323477 (m : real) (c : real) (x : real) (l : real) (y : real) (s : real -> Prop) (t : real -> Prop) (h1 : term12 s) (h2 : term12 t) : term489 m t c s x l y.
Proof. exact (@lem5323476 m t c x l y s h1 (@lem5319484 t h2)). Qed.
Lemma lem5323478 (c : real) (x : real) (y : real) (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 l m) : term485 m t c s x l y.
Proof. exact (@lem5323477 m c x l y s t h1 h2 (@lem5319495 l m h3)). Qed.
Lemma lem5323479 (x : real) (y : real) (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (c : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 l m) (h4 : real_lt m c) : term481 t c s x l y.
Proof. exact (@lem5323478 c x y s t l m h1 h2 h3 (@lem5319499 m c h4)). Qed.
Lemma lem5323480 (x : real) (y : real) (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (c : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 l m) (h4 : real_lt c l) (h5 : real_lt m c) : term477 t c s x l y.
Proof. exact (@lem5323479 x y s t l m c h1 h2 h3 h5 (@lem5319498 c l h4)). Qed.
Lemma lem5323481 (y : real) (s : real -> Prop) (x : real) (t : real -> Prop) (l : real) (m : real) (c : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 l m) (h4 : @IN real x t) (h5 : real_lt c l) (h6 : real_lt m c) : term473 c s x l y.
Proof. exact (@lem5323480 x y s t l m c h1 h2 h3 h5 h6 (@lem5321198 x t h4)). Qed.
Lemma lem5323482 (y : real) (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (x : real) (c : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 l m) (h4 : @IN real x t) (h5 : real_lt c l) (h6 : real_lt m c) (h7 : real_lt x c) : term469 s x l y.
Proof. exact (@lem5323481 y s x t l m c h1 h2 h3 h4 h5 h6 (@lem5321197 x c h7)). Qed.
Lemma lem5323483 (t : real -> Prop) (y : real) (s : real -> Prop) (l : real) (m : real) (x : real) (c : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 l m) (h4 : @IN real x t) (h5 : @IN real y s) (h6 : real_lt c l) (h7 : real_lt m c) (h8 : real_lt x c) : term465 x l y.
Proof. exact (@lem5323482 y s t l m x c h1 h2 h3 h4 h6 h7 h8 (@lem5321202 y s h5)). Qed.
Lemma lem5323484 (t : real -> Prop) (s : real -> Prop) (y : real) (l : real) (m : real) (x : real) (c : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 l m) (h4 : @IN real x t) (h5 : @IN real y s) (h6 : real_le y x) (h7 : real_lt c l) (h8 : real_lt m c) (h9 : real_lt x c) : term3 l y.
Proof. exact (@lem5323483 t y s l m x c h1 h2 h3 h4 h5 h7 h8 h9 (@lem5321201 y x h6)). Qed.
Lemma lem5323485 (t : real -> Prop) (s : real -> Prop) (y : real) (l : real) (m : real) (x : real) (c : real) (h1 : term12 s) (h2 : term12 t) (h3 : term3 l m) (h4 : @IN real x t) (h5 : @IN real y s) (h6 : real_le y x) (h7 : real_lt c l) (h8 : real_lt m c) (h9 : real_lt x c) : term453 s l y.
Proof. exact (EQ_MP (@lem5322131 l y s h5) (@lem5323484 t s y l m x c h1 h2 h3 h4 h5 h6 h7 h8 h9)). Qed.
Lemma lem5323486 (t : real -> Prop) (s : real -> Prop) (y : real) (l : real) (m : real) (x : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 l m) (h5 : @IN real x t) (h6 : @IN real y s) (h7 : real_le y x) (h8 : real_lt c l) (h9 : real_lt m c) (h10 : real_lt x c) : False.
Proof. exact (@lem5323485 t s y l m x c h2 h3 h4 h5 h6 h7 h8 h9 h10 (@lem5322057 y s l h1)). Qed.
Lemma lem5323487 (s : real -> Prop) (y : real) (x : real) (h1 : term328 s y x) : real_le y x.
Proof. exact (proj2 (@lem5321200 s y x h1)). Qed.
Lemma lem5323488 (s : real -> Prop) (y : real) (x : real) (h1 : term328 s y x) : @IN real y s.
Proof. exact (proj1 (@lem5321200 s y x h1)). Qed.
Lemma lem5323489 (t : real -> Prop) (s : real -> Prop) (y : real) (l : real) (m : real) (x : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 l m) (h5 : @IN real x t) (h6 : @IN real y s) (h7 : real_le y x) (h8 : real_lt c l) (h9 : real_lt m c) (h10 : real_lt x c) : (real_le y x) = False.
Proof. exact (prop_ext (fun h11 : real_le y x => @lem5323486 t s y l m x c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (fun h11 : False => @lem5321201 y x h7)). Qed.
Lemma lem5323490 (t : real -> Prop) (s : real -> Prop) (y : real) (l : real) (m : real) (x : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 l m) (h5 : @IN real x t) (h6 : @IN real y s) (h7 : real_le y x) (h8 : real_lt c l) (h9 : real_lt m c) (h10 : real_lt x c) : False.
Proof. exact (EQ_MP (@lem5323489 t s y l m x c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem5321201 y x h7)). Qed.
Lemma lem5323491 (t : real -> Prop) (s : real -> Prop) (y : real) (l : real) (m : real) (x : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 l m) (h5 : @IN real x t) (h6 : @IN real y s) (h7 : real_le y x) (h8 : real_lt c l) (h9 : real_lt m c) (h10 : real_lt x c) : (@IN real y s) = False.
Proof. exact (prop_ext (fun h11 : @IN real y s => @lem5323490 t s y l m x c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (fun h11 : False => @lem5321202 y s h6)). Qed.
Lemma lem5323492 (t : real -> Prop) (s : real -> Prop) (y : real) (l : real) (m : real) (x : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 l m) (h5 : @IN real x t) (h6 : @IN real y s) (h7 : real_le y x) (h8 : real_lt c l) (h9 : real_lt m c) (h10 : real_lt x c) : False.
Proof. exact (EQ_MP (@lem5323491 t s y l m x c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem5321202 y s h6)). Qed.
Lemma lem5323493 (t : real -> Prop) (y : real) (s : real -> Prop) (l : real) (m : real) (x : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 l m) (h5 : term328 s y x) (h6 : @IN real x t) (h7 : @IN real y s) (h8 : real_lt c l) (h9 : real_lt m c) (h10 : real_lt x c) : (real_le y x) = False.
Proof. exact (prop_ext (fun h11 : real_le y x => @lem5323492 t s y l m x c h1 h2 h3 h4 h6 h7 h11 h8 h9 h10) (fun h11 : False => @lem5323487 s y x h5)). Qed.
Lemma lem5323494 (t : real -> Prop) (y : real) (s : real -> Prop) (l : real) (m : real) (x : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 l m) (h5 : term328 s y x) (h6 : @IN real x t) (h7 : @IN real y s) (h8 : real_lt c l) (h9 : real_lt m c) (h10 : real_lt x c) : False.
Proof. exact (EQ_MP (@lem5323493 t y s l m x c h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem5323487 s y x h5)). Qed.
Lemma lem5323495 (s : real -> Prop) (y : real) (t : real -> Prop) (l : real) (m : real) (x : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 l m) (h5 : term328 s y x) (h6 : @IN real x t) (h7 : real_lt c l) (h8 : real_lt m c) (h9 : real_lt x c) : (@IN real y s) = False.
Proof. exact (prop_ext (fun h10 : @IN real y s => @lem5323494 t y s l m x c h1 h2 h3 h4 h5 h6 h10 h7 h8 h9) (fun h10 : False => @lem5323488 s y x h5)). Qed.
Lemma lem5323496 (s : real -> Prop) (y : real) (t : real -> Prop) (l : real) (m : real) (x : real) (c : real) (h1 : term13 s l) (h2 : term12 s) (h3 : term12 t) (h4 : term3 l m) (h5 : term328 s y x) (h6 : @IN real x t) (h7 : real_lt c l) (h8 : real_lt m c) (h9 : real_lt x c) : False.
Proof. exact (EQ_MP (@lem5323495 s y t l m x c h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem5323488 s y x h5)). Qed.
Lemma lem5323497 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (x : real) (c : real) (h1 : term13 s l) (h2 : term327 s x) (h3 : term12 s) (h4 : term12 t) (h5 : term3 l m) (h6 : @IN real x t) (h7 : real_lt c l) (h8 : real_lt m c) (h9 : real_lt x c) : False.
Proof. exact (ex_elim (@lem5321199 s x h2) (fun y : real => fun h0 : term354 s x y => @lem5323496 s y t l m x c h1 h3 h4 h5 h0 h6 h7 h8 h9)). Qed.
Lemma lem5323498 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (x : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 l m) (h6 : @IN real x t) (h7 : real_lt c l) (h8 : real_lt m c) (h9 : real_lt x c) : (term327 s x) = False.
Proof. exact (prop_ext (fun h10 : term327 s x => @lem5323497 s t l m x c h1 h10 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem5322054 s x t h2 h6)). Qed.
Lemma lem5323499 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (x : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 l m) (h6 : @IN real x t) (h7 : real_lt c l) (h8 : real_lt m c) (h9 : real_lt x c) : False.
Proof. exact (EQ_MP (@lem5323498 s t l m x c h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem5322054 s x t h2 h6)). Qed.
Lemma lem5323500 (t : real -> Prop) (x : real) (c : real) (h1 : term317 t x c) : real_lt x c.
Proof. exact (proj2 (@lem5321196 t x c h1)). Qed.
Lemma lem5323501 (t : real -> Prop) (x : real) (c : real) (h1 : term317 t x c) : @IN real x t.
Proof. exact (proj1 (@lem5321196 t x c h1)). Qed.
Lemma lem5323502 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (x : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 l m) (h6 : @IN real x t) (h7 : real_lt c l) (h8 : real_lt m c) (h9 : real_lt x c) : (real_lt x c) = False.
Proof. exact (prop_ext (fun h10 : real_lt x c => @lem5323499 s t l m x c h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem5321197 x c h9)). Qed.
Lemma lem5323503 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (x : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 l m) (h6 : @IN real x t) (h7 : real_lt c l) (h8 : real_lt m c) (h9 : real_lt x c) : False.
Proof. exact (EQ_MP (@lem5323502 s t l m x c h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem5321197 x c h9)). Qed.
Lemma lem5323504 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (x : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 l m) (h6 : @IN real x t) (h7 : real_lt c l) (h8 : real_lt m c) (h9 : real_lt x c) : (@IN real x t) = False.
Proof. exact (prop_ext (fun h10 : @IN real x t => @lem5323503 s t l m x c h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem5321198 x t h6)). Qed.
Lemma lem5323505 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (x : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 l m) (h6 : @IN real x t) (h7 : real_lt c l) (h8 : real_lt m c) (h9 : real_lt x c) : False.
Proof. exact (EQ_MP (@lem5323504 s t l m x c h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem5321198 x t h6)). Qed.
Lemma lem5323506 (s : real -> Prop) (x : real) (t : real -> Prop) (l : real) (m : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 l m) (h6 : term317 t x c) (h7 : @IN real x t) (h8 : real_lt c l) (h9 : real_lt m c) : (real_lt x c) = False.
Proof. exact (prop_ext (fun h10 : real_lt x c => @lem5323505 s t l m x c h1 h2 h3 h4 h5 h7 h8 h9 h10) (fun h10 : False => @lem5323500 t x c h6)). Qed.
Lemma lem5323507 (s : real -> Prop) (x : real) (t : real -> Prop) (l : real) (m : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 l m) (h6 : term317 t x c) (h7 : @IN real x t) (h8 : real_lt c l) (h9 : real_lt m c) : False.
Proof. exact (EQ_MP (@lem5323506 s x t l m c h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem5323500 t x c h6)). Qed.
Lemma lem5323508 (s : real -> Prop) (t : real -> Prop) (x : real) (l : real) (m : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 l m) (h6 : term317 t x c) (h7 : real_lt c l) (h8 : real_lt m c) : (@IN real x t) = False.
Proof. exact (prop_ext (fun h9 : @IN real x t => @lem5323507 s x t l m c h1 h2 h3 h4 h5 h6 h9 h7 h8) (fun h9 : False => @lem5323501 t x c h6)). Qed.
Lemma lem5323509 (s : real -> Prop) (t : real -> Prop) (x : real) (l : real) (m : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 l m) (h6 : term317 t x c) (h7 : real_lt c l) (h8 : real_lt m c) : False.
Proof. exact (EQ_MP (@lem5323508 s t x l m c h1 h2 h3 h4 h5 h6 h7 h8) (@lem5323501 t x c h6)). Qed.
Lemma lem5323510 (x : real) (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 l m) (h6 : real_lt c l) (h7 : real_lt m c) : term576 t x c.
Proof. exact (fun h0 : term317 t x c => @lem5323509 s t x l m c h1 h2 h3 h4 h5 h0 h6 h7). Qed.
Lemma lem5323511 (t : real -> Prop) (x : real) (c : real) : (term576 t x c) = (term323 t x c).
Proof. exact (@lem69 (term317 t x c)). Qed.
Lemma lem5323512 (x : real) (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 l m) (h6 : real_lt c l) (h7 : real_lt m c) : term323 t x c.
Proof. exact (EQ_MP (@lem5323511 t x c) (@lem5323510 x s t l m c h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5323518 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 l m) (h6 : real_lt c l) (h7 : real_lt m c) : term326 t c.
Proof. exact (fun x : real => @lem5323512 x s t l m c h1 h2 h3 h4 h5 h6 h7). Qed.
Lemma lem5323519 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term3 l m) (h6 : real_lt c l) (h7 : real_lt m c) : term305 m t c.
Proof. exact (EQ_MP (@lem5321193 t m c h7) (@lem5323518 s t l m c h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem5323520 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 l m) (h7 : real_lt c l) (h8 : real_lt m c) : False.
Proof. exact (@lem5323519 s t l m c h1 h2 h4 h5 h6 h7 h8 (@lem5321080 c m t h3)). Qed.
Lemma lem5323521 (m : real) (c : real) (l : real) (h1 : term18 m c l) : real_lt c l.
Proof. exact (proj2 (@lem5319497 m c l h1)). Qed.
Lemma lem5323522 (m : real) (c : real) (l : real) (h1 : term18 m c l) : real_lt m c.
Proof. exact (proj1 (@lem5319497 m c l h1)). Qed.
Lemma lem5323523 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 l m) (h7 : real_lt c l) (h8 : real_lt m c) : (real_lt c l) = False.
Proof. exact (prop_ext (fun h9 : real_lt c l => @lem5323520 s t l m c h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem5319498 c l h7)). Qed.
Lemma lem5323524 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 l m) (h7 : real_lt c l) (h8 : real_lt m c) : False.
Proof. exact (EQ_MP (@lem5323523 s t l m c h1 h2 h3 h4 h5 h6 h7 h8) (@lem5319498 c l h7)). Qed.
Lemma lem5323525 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 l m) (h7 : real_lt c l) (h8 : real_lt m c) : (real_lt m c) = False.
Proof. exact (prop_ext (fun h9 : real_lt m c => @lem5323524 s t l m c h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem5319499 m c h8)). Qed.
Lemma lem5323526 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 l m) (h7 : real_lt c l) (h8 : real_lt m c) : False.
Proof. exact (EQ_MP (@lem5323525 s t l m c h1 h2 h3 h4 h5 h6 h7 h8) (@lem5319499 m c h8)). Qed.
Lemma lem5323527 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 l m) (h7 : term18 m c l) (h8 : real_lt m c) : (real_lt c l) = False.
Proof. exact (prop_ext (fun h9 : real_lt c l => @lem5323526 s t l m c h1 h2 h3 h4 h5 h6 h9 h8) (fun h9 : False => @lem5323521 m c l h7)). Qed.
Lemma lem5323528 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (c : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 l m) (h7 : term18 m c l) (h8 : real_lt m c) : False.
Proof. exact (EQ_MP (@lem5323527 s t l m c h1 h2 h3 h4 h5 h6 h7 h8) (@lem5323521 m c l h7)). Qed.
Lemma lem5323529 (s : real -> Prop) (t : real -> Prop) (m : real) (c : real) (l : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 l m) (h7 : term18 m c l) : (real_lt m c) = False.
Proof. exact (prop_ext (fun h8 : real_lt m c => @lem5323528 s t l m c h1 h2 h3 h4 h5 h6 h7 h8) (fun h8 : False => @lem5323522 m c l h7)). Qed.
Lemma lem5323530 (s : real -> Prop) (t : real -> Prop) (m : real) (c : real) (l : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 l m) (h7 : term18 m c l) : False.
Proof. exact (EQ_MP (@lem5323529 s t m c l h1 h2 h3 h4 h5 h6 h7) (@lem5323522 m c l h7)). Qed.
Lemma lem5323531 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term17 m l) (h5 : term12 s) (h6 : term12 t) (h7 : term3 l m) : False.
Proof. exact (ex_elim (@lem5319496 m l h4) (fun c : real => fun h0 : term299 m l c => @lem5323530 s t m c l h1 h2 h3 h5 h6 h7 h0)). Qed.
Lemma lem5323532 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 l m) : (term17 m l) = False.
Proof. exact (prop_ext (fun h7 : term17 m l => @lem5323531 s t l m h1 h2 h3 h7 h4 h5 h6) (fun h7 : False => @lem5321077 s t l m h4 h5 h6)). Qed.
Lemma lem5323533 (s : real -> Prop) (t : real -> Prop) (l : real) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) (h6 : term3 l m) : False.
Proof. exact (EQ_MP (@lem5323532 s t l m h1 h2 h3 h4 h5 h6) (@lem5321077 s t l m h4 h5 h6)). Qed.
Lemma lem5323534 (l : real) (m : real) (s : real -> Prop) (t : real -> Prop) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) : term16 l m.
Proof. exact (fun h0 : term3 l m => @lem5323533 s t l m h1 h2 h3 h4 h5 h0). Qed.
Lemma lem5323535 (l : real) (m : real) (s : real -> Prop) (t : real -> Prop) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) : real_le l m.
Proof. exact (EQ_MP (@lem5319490 l m) (@lem5323534 l m s t h1 h2 h3 h4 h5)). Qed.
Lemma lem5323536 (t : real -> Prop) (m : real) (h1 : has_inf t m) : term11 m t.
Proof. exact (proj2 (@lem5319482 t m h1)). Qed.
Lemma lem5323537 (t : real -> Prop) (m : real) (h1 : has_inf t m) : term12 t.
Proof. exact (proj1 (@lem5319482 t m h1)). Qed.
Lemma lem5323538 (m : real) (t : real -> Prop) (h1 : term11 m t) : term14 m t.
Proof. exact (proj2 (@lem5319483 m t h1)). Qed.
Lemma lem5323540 (l : real) (m : real) (s : real -> Prop) (t : real -> Prop) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) : (term14 m t) = (real_le l m).
Proof. exact (prop_ext (fun h6 : term14 m t => @lem5323535 l m s t h1 h2 h3 h4 h5) (fun h6 : real_le l m => @lem5319485 m t h3)). Qed.
Lemma lem5323541 (l : real) (m : real) (s : real -> Prop) (t : real -> Prop) (h1 : term13 s l) (h2 : term10 t s) (h3 : term14 m t) (h4 : term12 s) (h5 : term12 t) : real_le l m.
Proof. exact (EQ_MP (@lem5323540 l m s t h1 h2 h3 h4 h5) (@lem5319485 m t h3)). Qed.
Lemma lem5323542 (l : real) (s : real -> Prop) (m : real) (t : real -> Prop) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term11 m t) : (term14 m t) = (real_le l m).
Proof. exact (prop_ext (fun h6 : term14 m t => @lem5323541 l m s t h1 h2 h6 h3 h4) (fun h6 : real_le l m => @lem5323538 m t h5)). Qed.
Lemma lem5323543 (l : real) (s : real -> Prop) (m : real) (t : real -> Prop) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term11 m t) : real_le l m.
Proof. exact (EQ_MP (@lem5323542 l s m t h1 h2 h3 h4 h5) (@lem5323538 m t h5)). Qed.
Lemma lem5323544 (l : real) (s : real -> Prop) (m : real) (t : real -> Prop) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term11 m t) : (term12 t) = (real_le l m).
Proof. exact (prop_ext (fun h6 : term12 t => @lem5323543 l s m t h1 h2 h3 h4 h5) (fun h6 : real_le l m => @lem5319484 t h4)). Qed.
Lemma lem5323545 (l : real) (s : real -> Prop) (m : real) (t : real -> Prop) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : term11 m t) : real_le l m.
Proof. exact (EQ_MP (@lem5323544 l s m t h1 h2 h3 h4 h5) (@lem5319484 t h4)). Qed.
Lemma lem5323546 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : has_inf t m) : (term11 m t) = (real_le l m).
Proof. exact (prop_ext (fun h6 : term11 m t => @lem5323545 l s m t h1 h2 h3 h4 h6) (fun h6 : real_le l m => @lem5323536 t m h5)). Qed.
Lemma lem5323547 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : term12 t) (h5 : has_inf t m) : real_le l m.
Proof. exact (EQ_MP (@lem5323546 l s t m h1 h2 h3 h4 h5) (@lem5323536 t m h5)). Qed.
Lemma lem5323548 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : has_inf t m) : (term12 t) = (real_le l m).
Proof. exact (prop_ext (fun h5 : term12 t => @lem5323547 l s t m h1 h2 h3 h5 h4) (fun h5 : real_le l m => @lem5323537 t m h4)). Qed.
Lemma lem5323549 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : has_inf t m) : real_le l m.
Proof. exact (EQ_MP (@lem5323548 l s t m h1 h2 h3 h4) (@lem5323537 t m h4)). Qed.
Lemma lem5323550 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term11 l s.
Proof. exact (proj2 (@lem5319450 s l h1)). Qed.
Lemma lem5323551 (s : real -> Prop) (l : real) (h1 : has_inf s l) : term12 s.
Proof. exact (proj1 (@lem5319450 s l h1)). Qed.
Lemma lem5323553 (l : real) (s : real -> Prop) (h1 : term11 l s) : term13 s l.
Proof. exact (proj1 (@lem5319451 l s h1)). Qed.
Lemma lem5323554 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : has_inf t m) : (term13 s l) = (real_le l m).
Proof. exact (prop_ext (fun h5 : term13 s l => @lem5323549 l s t m h1 h2 h3 h4) (fun h5 : real_le l m => @lem5319454 s l h1)). Qed.
Lemma lem5323555 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term13 s l) (h2 : term10 t s) (h3 : term12 s) (h4 : has_inf t m) : real_le l m.
Proof. exact (EQ_MP (@lem5323554 l s t m h1 h2 h3 h4) (@lem5319454 s l h1)). Qed.
Lemma lem5323556 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : term12 s) (h3 : term11 l s) (h4 : has_inf t m) : (term13 s l) = (real_le l m).
Proof. exact (prop_ext (fun h5 : term13 s l => @lem5323555 l s t m h5 h1 h2 h4) (fun h5 : real_le l m => @lem5323553 l s h3)). Qed.
Lemma lem5323557 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : term12 s) (h3 : term11 l s) (h4 : has_inf t m) : real_le l m.
Proof. exact (EQ_MP (@lem5323556 l s t m h1 h2 h3 h4) (@lem5323553 l s h3)). Qed.
Lemma lem5323558 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : term12 s) (h3 : term11 l s) (h4 : has_inf t m) : (term12 s) = (real_le l m).
Proof. exact (prop_ext (fun h5 : term12 s => @lem5323557 l s t m h1 h2 h3 h4) (fun h5 : real_le l m => @lem5319452 s h2)). Qed.
Lemma lem5323559 (l : real) (s : real -> Prop) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : term12 s) (h3 : term11 l s) (h4 : has_inf t m) : real_le l m.
Proof. exact (EQ_MP (@lem5323558 l s t m h1 h2 h3 h4) (@lem5319452 s h2)). Qed.
Lemma lem5323560 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : term12 s) (h3 : has_inf s l) (h4 : has_inf t m) : (term11 l s) = (real_le l m).
Proof. exact (prop_ext (fun h5 : term11 l s => @lem5323559 l s t m h1 h2 h5 h4) (fun h5 : real_le l m => @lem5323550 s l h3)). Qed.
Lemma lem5323561 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : term12 s) (h3 : has_inf s l) (h4 : has_inf t m) : real_le l m.
Proof. exact (EQ_MP (@lem5323560 s l t m h1 h2 h3 h4) (@lem5323550 s l h3)). Qed.
Lemma lem5323562 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : has_inf s l) (h3 : has_inf t m) : (term12 s) = (real_le l m).
Proof. exact (prop_ext (fun h4 : term12 s => @lem5323561 s l t m h1 h4 h2 h3) (fun h4 : real_le l m => @lem5323551 s l h2)). Qed.
Lemma lem5323563 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : has_inf s l) (h3 : has_inf t m) : real_le l m.
Proof. exact (EQ_MP (@lem5323562 s l t m h1 h2 h3) (@lem5323551 s l h2)). Qed.
Lemma lem5323564 (l : real) (m : real) (t : real -> Prop) (s : real -> Prop) (h1 : term8 l m t s) : term9 m t s.
Proof. exact (proj2 (@lem5319419 l m t s h1)). Qed.
Lemma lem5323565 (l : real) (m : real) (t : real -> Prop) (s : real -> Prop) (h1 : term8 l m t s) : has_inf s l.
Proof. exact (proj1 (@lem5319419 l m t s h1)). Qed.
Lemma lem5323566 (m : real) (t : real -> Prop) (s : real -> Prop) (h1 : term9 m t s) : term10 t s.
Proof. exact (proj2 (@lem5319420 m t s h1)). Qed.
Lemma lem5323567 (m : real) (t : real -> Prop) (s : real -> Prop) (h1 : term9 m t s) : has_inf t m.
Proof. exact (proj1 (@lem5319420 m t s h1)). Qed.
Lemma lem5323568 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : has_inf s l) (h3 : has_inf t m) : (term10 t s) = (real_le l m).
Proof. exact (prop_ext (fun h4 : term10 t s => @lem5323563 s l t m h1 h2 h3) (fun h4 : real_le l m => @lem5319422 t s h1)). Qed.
Lemma lem5323569 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : has_inf s l) (h3 : has_inf t m) : real_le l m.
Proof. exact (EQ_MP (@lem5323568 s l t m h1 h2 h3) (@lem5319422 t s h1)). Qed.
Lemma lem5323570 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : has_inf s l) (h3 : has_inf t m) : (has_inf t m) = (real_le l m).
Proof. exact (prop_ext (fun h4 : has_inf t m => @lem5323569 s l t m h1 h2 h3) (fun h4 : real_le l m => @lem5319423 t m h3)). Qed.
Lemma lem5323571 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term10 t s) (h2 : has_inf s l) (h3 : has_inf t m) : real_le l m.
Proof. exact (EQ_MP (@lem5323570 s l t m h1 h2 h3) (@lem5319423 t m h3)). Qed.
Lemma lem5323572 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term9 m t s) (h2 : has_inf s l) (h3 : has_inf t m) : (term10 t s) = (real_le l m).
Proof. exact (prop_ext (fun h4 : term10 t s => @lem5323571 s l t m h4 h2 h3) (fun h4 : real_le l m => @lem5323566 m t s h1)). Qed.
Lemma lem5323573 (s : real -> Prop) (l : real) (t : real -> Prop) (m : real) (h1 : term9 m t s) (h2 : has_inf s l) (h3 : has_inf t m) : real_le l m.
Proof. exact (EQ_MP (@lem5323572 s l t m h1 h2 h3) (@lem5323566 m t s h1)). Qed.
Lemma lem5323574 (m : real) (t : real -> Prop) (s : real -> Prop) (l : real) (h1 : term9 m t s) (h2 : has_inf s l) : (has_inf t m) = (real_le l m).
Proof. exact (prop_ext (fun h3 : has_inf t m => @lem5323573 s l t m h1 h2 h3) (fun h3 : real_le l m => @lem5323567 m t s h1)). Qed.
Lemma lem5323575 (m : real) (t : real -> Prop) (s : real -> Prop) (l : real) (h1 : term9 m t s) (h2 : has_inf s l) : real_le l m.
Proof. exact (EQ_MP (@lem5323574 m t s l h1 h2) (@lem5323567 m t s h1)). Qed.
Lemma lem5323576 (m : real) (t : real -> Prop) (s : real -> Prop) (l : real) (h1 : term9 m t s) (h2 : has_inf s l) : (has_inf s l) = (real_le l m).
Proof. exact (prop_ext (fun h3 : has_inf s l => @lem5323575 m t s l h1 h2) (fun h3 : real_le l m => @lem5319421 s l h2)). Qed.
Lemma lem5323577 (m : real) (t : real -> Prop) (s : real -> Prop) (l : real) (h1 : term9 m t s) (h2 : has_inf s l) : real_le l m.
Proof. exact (EQ_MP (@lem5323576 m t s l h1 h2) (@lem5319421 s l h2)). Qed.
Lemma lem5323578 (m : real) (t : real -> Prop) (s : real -> Prop) (l : real) (h1 : term8 l m t s) (h2 : has_inf s l) : (term9 m t s) = (real_le l m).
Proof. exact (prop_ext (fun h3 : term9 m t s => @lem5323577 m t s l h3 h2) (fun h3 : real_le l m => @lem5323564 l m t s h1)). Qed.
Lemma lem5323579 (m : real) (t : real -> Prop) (s : real -> Prop) (l : real) (h1 : term8 l m t s) (h2 : has_inf s l) : real_le l m.
Proof. exact (EQ_MP (@lem5323578 m t s l h1 h2) (@lem5323564 l m t s h1)). Qed.
Lemma lem5323580 (l : real) (m : real) (t : real -> Prop) (s : real -> Prop) (h1 : term8 l m t s) : (has_inf s l) = (real_le l m).
Proof. exact (prop_ext (fun h2 : has_inf s l => @lem5323579 m t s l h1 h2) (fun h2 : real_le l m => @lem5323565 l m t s h1)). Qed.
Lemma lem5323581 (l : real) (m : real) (t : real -> Prop) (s : real -> Prop) (h1 : term8 l m t s) : real_le l m.
Proof. exact (EQ_MP (@lem5323580 l m t s h1) (@lem5323565 l m t s h1)). Qed.
Lemma lem5323582 (t : real -> Prop) (s : real -> Prop) (l : real) (m : real) : term577 t s l m.
Proof. exact (fun h0 : term8 l m t s => @lem5323581 l m t s h0). Qed.
Lemma lem5323588 (t : real -> Prop) (s : real -> Prop) (l : real) : term578 t s l.
Proof. exact (fun m : real => @lem5323582 t s l m). Qed.
Lemma lem5323594 (t : real -> Prop) (s : real -> Prop) : term579 t s.
Proof. exact (fun l : real => @lem5323588 t s l). Qed.
Lemma lem5323600 (s : real -> Prop) : term580 s.
Proof. exact (fun t : real -> Prop => @lem5323594 t s). Qed.
Lemma lem5323606 : term581.
Proof. exact (fun s : real -> Prop => @lem5323600 s). Qed.
