Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUP_ASCLOSE_term_abbrevs.
Require Import REAL_SUP_BOUNDS_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482680_spec.
Require Import thm1482981_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm19158_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988289_spec.
Require Import thm1988291_spec.
Require Import thm1988297_spec.
Require Import thm1988332_spec.
Require Import thm1988348_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem5166580 (s : real -> Prop) : term0 s.
Proof. exact (@lem5166478 s). Qed.
Lemma lem5166581 (s : real -> Prop) : (term0 s) = (term1 s).
Proof. exact (eq_refl (term0 s)). Qed.
Lemma lem5166582 (s : real -> Prop) : term1 s.
Proof. exact (EQ_MP (@lem5166581 s) (@lem5166580 s)). Qed.
Lemma lem5166583 (s : real -> Prop) (a : real) : term2 s a.
Proof. exact (@lem5166582 s a). Qed.
Lemma lem5166584 (a : real) (s : real -> Prop) : (term2 s a) = (term3 a s).
Proof. exact (eq_refl (term2 s a)). Qed.
Lemma lem5166585 (a : real) (s : real -> Prop) : term3 a s.
Proof. exact (EQ_MP (@lem5166584 a s) (@lem5166583 s a)). Qed.
Lemma lem5166586 (a : real) (s : real -> Prop) (b : real) : term4 a s b.
Proof. exact (@lem5166585 a s b). Qed.
Lemma lem5166587 (a : real) (s : real -> Prop) (b : real) : (term4 a s b) = (term5 a s b).
Proof. exact (eq_refl (term4 a s b)). Qed.
Lemma lem5166588 (a : real) (s : real -> Prop) (b : real) : term5 a s b.
Proof. exact (EQ_MP (@lem5166587 a s b) (@lem5166586 a s b)). Qed.
Lemma lem5166589 (a : real) (s : real -> Prop) (b : real) : (term5 a s b) = ((term5 a s b) = True).
Proof. exact (@lem7 (term5 a s b)). Qed.
Lemma lem5166607 (x : real) (l : real) (e : real) : (term6 x l e) = (term7 x l e).
Proof. exact (@lem17045 (term8 l e x) (term9 x l e)). Qed.
Lemma lem5166613 (x : real) (l : real) (e : real) : (term10 x l e) = (term10 x l e).
Proof. exact (eq_refl (term10 x l e)). Qed.
Lemma lem5166615 (x : real) (l : real) (e : real) : (term11 x l e) = (term11 x l e).
Proof. exact (eq_refl (term11 x l e)). Qed.
Lemma lem5166616 (x : real) (l : real) (e : real) : (term12 x l e) = (term13 x l e).
Proof. exact (MK_COMB (@lem5166615 x l e) (@lem5166607 x l e)). Qed.
Lemma lem5166617 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5166618 (x : real) (l : real) (e : real) : (term14 x l e) = (term15 x l e).
Proof. exact (MK_COMB (@lem5166617) (@lem5166616 x l e)). Qed.
Lemma lem5166619 (x : real) (l : real) (e : real) : (term16 x l e) = (term17 x l e).
Proof. exact (MK_COMB (@lem5166618 x l e) (@lem5166613 x l e)). Qed.
Lemma lem5166620 (x : real) (l : real) (e : real) : (term18 x l e) = (term16 x l e).
Proof. exact (@lem17646 (term19 x l e) (term20 x l e)). Qed.
Lemma lem5166650 (x : real) (l : real) (e : real) : (term18 x l e) = (term17 x l e).
Proof. exact (TRANS (@lem5166620 x l e) (@lem5166619 x l e)). Qed.
Lemma lem5166651 (e : real) (x : real) (l : real) : (term19 x l e) = (term21 e x l).
Proof. exact (@lem1988287 e (term22 x l)). Qed.
Lemma lem5166657 (x : real) (l : real) : (real_sub x l) = (term23 x l).
Proof. exact (@lem1982792 x l). Qed.
Lemma lem5166662 (l : real) (x : real) : (term23 x l) = (term24 l x).
Proof. exact (@lem1982761 (term25 l) x). Qed.
Lemma lem5166664 (l : real) (x : real) : (real_sub x l) = (term24 l x).
Proof. exact (TRANS (@lem5166657 x l) (@lem5166662 l x)). Qed.
Lemma lem5166665 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem5166666 (l : real) (x : real) : (term22 x l) = (term26 l x).
Proof. exact (MK_COMB (@lem5166665) (@lem5166664 l x)). Qed.
Lemma lem5166669 (e : real) : (real_sub e) = (real_sub e).
Proof. exact (eq_refl (real_sub e)). Qed.
Lemma lem5166670 (e : real) (l : real) (x : real) : (term27 e x l) = (term28 e l x).
Proof. exact (MK_COMB (@lem5166669 e) (@lem5166666 l x)). Qed.
Lemma lem5166677 (e : real) (l : real) (x : real) : (term28 e l x) = (term29 e l x).
Proof. exact (@lem1982792 e (term26 l x)). Qed.
Lemma lem5166678 (e : real) (l : real) (x : real) : (term27 e x l) = (term29 e l x).
Proof. exact (TRANS (@lem5166670 e l x) (@lem5166677 e l x)). Qed.
Lemma lem5166679 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5166680 (e : real) (l : real) (x : real) : (term30 e x l) = (term31 e l x).
Proof. exact (MK_COMB (@lem5166679) (@lem5166678 e l x)). Qed.
Lemma lem5166681 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5166682 (e : real) (l : real) (x : real) : (term21 e x l) = (term33 e l x).
Proof. exact (MK_COMB (@lem5166680 e l x) (@lem5166681)). Qed.
Lemma lem5166683 (e : real) (l : real) (x : real) : (term19 x l e) = (term33 e l x).
Proof. exact (TRANS (@lem5166651 e x l) (@lem5166682 e l x)). Qed.
Lemma lem5166684 (l : real) (e : real) (x : real) : (term34 l e x) = (term35 l e x).
Proof. exact (@lem1988297 (real_sub l e) x). Qed.
Lemma lem5166685 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5166691 (l : real) (e : real) : (real_sub l e) = (term23 l e).
Proof. exact (@lem1982792 l e). Qed.
Lemma lem5166696 (e : real) (l : real) : (term23 l e) = (term24 e l).
Proof. exact (@lem1982761 (term25 e) l). Qed.
Lemma lem5166698 (e : real) (l : real) : (real_sub l e) = (term24 e l).
Proof. exact (TRANS (@lem5166691 l e) (@lem5166696 e l)). Qed.
Lemma lem5166699 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5166700 (e : real) (l : real) : (term36 l e) = (term37 e l).
Proof. exact (MK_COMB (@lem5166699) (@lem5166698 e l)). Qed.
Lemma lem5166701 (e : real) (l : real) (x : real) : (term38 l e x) = (term39 e l x).
Proof. exact (MK_COMB (@lem5166700 e l) (@lem5166685 x)). Qed.
Lemma lem5166702 (e : real) (l : real) (x : real) : (term39 e l x) = (term40 e l x).
Proof. exact (@lem1982792 (term24 e l) x). Qed.
Lemma lem5166711 (e : real) (l : real) (x : real) : (term40 e l x) = (term41 e l x).
Proof. exact (@lem1982755 (term25 e) l (term25 x)). Qed.
Lemma lem5166712 (e : real) (l : real) (x : real) : (term39 e l x) = (term41 e l x).
Proof. exact (TRANS (@lem5166702 e l x) (@lem5166711 e l x)). Qed.
Lemma lem5166713 (e : real) (l : real) (x : real) : (term38 l e x) = (term41 e l x).
Proof. exact (TRANS (@lem5166701 e l x) (@lem5166712 e l x)). Qed.
Lemma lem5166714 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5166715 (e : real) (l : real) (x : real) : (term42 l e x) = (term43 e l x).
Proof. exact (MK_COMB (@lem5166714) (@lem5166713 e l x)). Qed.
Lemma lem5166716 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5166717 (e : real) (l : real) (x : real) : (term35 l e x) = (term44 e l x).
Proof. exact (MK_COMB (@lem5166715 e l x) (@lem5166716)). Qed.
Lemma lem5166718 (e : real) (l : real) (x : real) : (term34 l e x) = (term44 e l x).
Proof. exact (TRANS (@lem5166684 l e x) (@lem5166717 e l x)). Qed.
Lemma lem5166719 (x : real) (l : real) (e : real) : (term45 x l e) = (term46 x l e).
Proof. exact (@lem1988297 x (real_add l e)). Qed.
Lemma lem5166726 (e : real) (l : real) : (real_add l e) = (real_add e l).
Proof. exact (@lem1982761 e l). Qed.
Lemma lem5166729 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem5166730 (x : real) (e : real) (l : real) : (term47 x l e) = (term47 x e l).
Proof. exact (MK_COMB (@lem5166729 x) (@lem5166726 e l)). Qed.
Lemma lem5166731 (x : real) (e : real) (l : real) : (term47 x e l) = (term48 x e l).
Proof. exact (@lem1982792 x (real_add e l)). Qed.
Lemma lem5166738 (e : real) (l : real) : (term49 e l) = (term50 e l).
Proof. exact (@lem1982781 e term51 l). Qed.
Lemma lem5166739 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem5166740 (x : real) (e : real) (l : real) : (term48 x e l) = (term52 x e l).
Proof. exact (MK_COMB (@lem5166739 x) (@lem5166738 e l)). Qed.
Lemma lem5166741 (e : real) (x : real) (l : real) : (term52 x e l) = (term41 e x l).
Proof. exact (@lem1982757 (term25 e) x (term25 l)). Qed.
Lemma lem5166742 (l : real) (x : real) : (term23 x l) = (term24 l x).
Proof. exact (@lem1982761 (term25 l) x). Qed.
Lemma lem5166743 (e : real) : (term53 e) = (term53 e).
Proof. exact (eq_refl (term53 e)). Qed.
Lemma lem5166744 (e : real) (l : real) (x : real) : (term41 e x l) = (term54 e l x).
Proof. exact (MK_COMB (@lem5166743 e) (@lem5166742 l x)). Qed.
Lemma lem5166745 (e : real) (l : real) (x : real) : (term52 x e l) = (term54 e l x).
Proof. exact (TRANS (@lem5166741 e x l) (@lem5166744 e l x)). Qed.
Lemma lem5166746 (e : real) (l : real) (x : real) : (term48 x e l) = (term54 e l x).
Proof. exact (TRANS (@lem5166740 x e l) (@lem5166745 e l x)). Qed.
Lemma lem5166747 (e : real) (l : real) (x : real) : (term47 x e l) = (term54 e l x).
Proof. exact (TRANS (@lem5166731 x e l) (@lem5166746 e l x)). Qed.
Lemma lem5166748 (e : real) (l : real) (x : real) : (term47 x l e) = (term54 e l x).
Proof. exact (TRANS (@lem5166730 x e l) (@lem5166747 e l x)). Qed.
Lemma lem5166749 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5166750 (e : real) (l : real) (x : real) : (term55 x l e) = (term56 e l x).
Proof. exact (MK_COMB (@lem5166749) (@lem5166748 e l x)). Qed.
Lemma lem5166751 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5166752 (e : real) (l : real) (x : real) : (term46 x l e) = (term57 e l x).
Proof. exact (MK_COMB (@lem5166750 e l x) (@lem5166751)). Qed.
Lemma lem5166753 (e : real) (l : real) (x : real) : (term45 x l e) = (term57 e l x).
Proof. exact (TRANS (@lem5166719 x l e) (@lem5166752 e l x)). Qed.
Lemma lem5166754 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5166755 (e : real) (l : real) (x : real) : (term58 l e x) = (term59 e l x).
Proof. exact (MK_COMB (@lem5166754) (@lem5166718 e l x)). Qed.
Lemma lem5166756 (e : real) (l : real) (x : real) : (term7 x l e) = (term60 e l x).
Proof. exact (MK_COMB (@lem5166755 e l x) (@lem5166753 e l x)). Qed.
Lemma lem5166757 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5166758 (e : real) (l : real) (x : real) : (term11 x l e) = (term61 e l x).
Proof. exact (MK_COMB (@lem5166757) (@lem5166683 e l x)). Qed.
Lemma lem5166759 (e : real) (l : real) (x : real) : (term13 x l e) = (term62 e l x).
Proof. exact (MK_COMB (@lem5166758 e l x) (@lem5166756 e l x)). Qed.
Lemma lem5166760 (x : real) (l : real) (e : real) : (term63 x l e) = (term64 x l e).
Proof. exact (@lem1988297 (term22 x l) e). Qed.
Lemma lem5166761 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem5166767 (x : real) (l : real) : (real_sub x l) = (term23 x l).
Proof. exact (@lem1982792 x l). Qed.
Lemma lem5166772 (l : real) (x : real) : (term23 x l) = (term24 l x).
Proof. exact (@lem1982761 (term25 l) x). Qed.
Lemma lem5166774 (l : real) (x : real) : (real_sub x l) = (term24 l x).
Proof. exact (TRANS (@lem5166767 x l) (@lem5166772 l x)). Qed.
Lemma lem5166775 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem5166776 (l : real) (x : real) : (term22 x l) = (term26 l x).
Proof. exact (MK_COMB (@lem5166775) (@lem5166774 l x)). Qed.
Lemma lem5166777 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5166778 (l : real) (x : real) : (term65 x l) = (term66 l x).
Proof. exact (MK_COMB (@lem5166777) (@lem5166776 l x)). Qed.
Lemma lem5166779 (l : real) (x : real) (e : real) : (term67 x l e) = (term68 l x e).
Proof. exact (MK_COMB (@lem5166778 l x) (@lem5166761 e)). Qed.
Lemma lem5166780 (l : real) (x : real) (e : real) : (term68 l x e) = (term69 l x e).
Proof. exact (@lem1982792 (term26 l x) e). Qed.
Lemma lem5166785 (e : real) (l : real) (x : real) : (term69 l x e) = (term70 e l x).
Proof. exact (@lem1982761 (term25 e) (term26 l x)). Qed.
Lemma lem5166786 (e : real) (l : real) (x : real) : (term68 l x e) = (term70 e l x).
Proof. exact (TRANS (@lem5166780 l x e) (@lem5166785 e l x)). Qed.
Lemma lem5166787 (e : real) (l : real) (x : real) : (term67 x l e) = (term70 e l x).
Proof. exact (TRANS (@lem5166779 l x e) (@lem5166786 e l x)). Qed.
Lemma lem5166788 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5166789 (e : real) (l : real) (x : real) : (term71 x l e) = (term72 e l x).
Proof. exact (MK_COMB (@lem5166788) (@lem5166787 e l x)). Qed.
Lemma lem5166790 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5166791 (e : real) (l : real) (x : real) : (term64 x l e) = (term73 e l x).
Proof. exact (MK_COMB (@lem5166789 e l x) (@lem5166790)). Qed.
Lemma lem5166792 (e : real) (l : real) (x : real) : (term63 x l e) = (term73 e l x).
Proof. exact (TRANS (@lem5166760 x l e) (@lem5166791 e l x)). Qed.
Lemma lem5166793 (x : real) (l : real) (e : real) : (term8 l e x) = (term74 x l e).
Proof. exact (@lem1988287 x (real_sub l e)). Qed.
Lemma lem5166799 (l : real) (e : real) : (real_sub l e) = (term23 l e).
Proof. exact (@lem1982792 l e). Qed.
Lemma lem5166804 (e : real) (l : real) : (term23 l e) = (term24 e l).
Proof. exact (@lem1982761 (term25 e) l). Qed.
Lemma lem5166806 (e : real) (l : real) : (real_sub l e) = (term24 e l).
Proof. exact (TRANS (@lem5166799 l e) (@lem5166804 e l)). Qed.
Lemma lem5166809 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem5166810 (x : real) (e : real) (l : real) : (term75 x l e) = (term76 x e l).
Proof. exact (MK_COMB (@lem5166809 x) (@lem5166806 e l)). Qed.
Lemma lem5166811 (x : real) (e : real) (l : real) : (term76 x e l) = (term77 x e l).
Proof. exact (@lem1982792 x (term24 e l)). Qed.
Lemma lem5166812 (e : real) (l : real) : (term78 e l) = (term79 e l).
Proof. exact (@lem1982781 (term25 e) term51 l). Qed.
Lemma lem5166813 (l : real) : (term25 l) = (term25 l).
Proof. exact (eq_refl (term25 l)). Qed.
Lemma lem5166814 (e : real) : (term80 e) = (term81 e).
Proof. exact (@lem1982749 term51 term51 e). Qed.
Lemma lem5166816 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5166817 : term51 = term84.
Proof. exact (@lem5166816 term85). Qed.
Lemma lem5166819 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5166820 : term51 = term84.
Proof. exact (@lem5166819 term85). Qed.
Lemma lem5166821 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5166822 : term86 = term87.
Proof. exact (MK_COMB (@lem5166821) (@lem5166820)). Qed.
Lemma lem5166823 : term88 = term89.
Proof. exact (MK_COMB (@lem5166822) (@lem5166817)). Qed.
Lemma lem5166824 : term89 = term90.
Proof. exact (@lem1981613 term51 term51 term91 term91). Qed.
Lemma lem5166826 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5166827 : term94 = term95.
Proof. exact (@lem5166826 term85 term85). Qed.
Lemma lem5166828 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5166829 : term97 = term85.
Proof. exact (EQ_MP (@lem5166828) (@lem940073)). Qed.
Lemma lem5166830 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5166831 : term95 = term91.
Proof. exact (MK_COMB (@lem5166830) (@lem5166829)). Qed.
Lemma lem5166832 : term94 = term91.
Proof. exact (TRANS (@lem5166827) (@lem5166831)). Qed.
Lemma lem5166834 (m : nat) (n : nat) : (term98 m n) = (term93 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5166835 : term88 = term95.
Proof. exact (@lem5166834 term85 term85). Qed.
Lemma lem5166836 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5166837 : term97 = term85.
Proof. exact (EQ_MP (@lem5166836) (@lem940073)). Qed.
Lemma lem5166838 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5166839 : term95 = term91.
Proof. exact (MK_COMB (@lem5166838) (@lem5166837)). Qed.
Lemma lem5166840 : term88 = term91.
Proof. exact (TRANS (@lem5166835) (@lem5166839)). Qed.
Lemma lem5166841 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5166842 : term99 = term100.
Proof. exact (MK_COMB (@lem5166841) (@lem5166840)). Qed.
Lemma lem5166843 : term90 = term101.
Proof. exact (MK_COMB (@lem5166842) (@lem5166832)). Qed.
Lemma lem5166844 : term89 = term101.
Proof. exact (TRANS (@lem5166824) (@lem5166843)). Qed.
Lemma lem5166845 : term88 = term101.
Proof. exact (TRANS (@lem5166823) (@lem5166844)). Qed.
Lemma lem5166847 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5166848 : term101 = term91.
Proof. exact (@lem5166847 term91). Qed.
Lemma lem5166849 : term88 = term91.
Proof. exact (TRANS (@lem5166845) (@lem5166848)). Qed.
Lemma lem5166850 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5166851 : term103 = term104.
Proof. exact (MK_COMB (@lem5166850) (@lem5166849)). Qed.
Lemma lem5166852 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem5166853 (e : real) : (term81 e) = (term105 e).
Proof. exact (MK_COMB (@lem5166851) (@lem5166852 e)). Qed.
Lemma lem5166854 (e : real) : (term80 e) = (term105 e).
Proof. exact (TRANS (@lem5166814 e) (@lem5166853 e)). Qed.
Lemma lem5166855 (e : real) : (term105 e) = e.
Proof. exact (@lem1982709 e). Qed.
Lemma lem5166856 (e : real) : (term80 e) = e.
Proof. exact (TRANS (@lem5166854 e) (@lem5166855 e)). Qed.
Lemma lem5166857 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5166858 (e : real) : (term106 e) = (real_add e).
Proof. exact (MK_COMB (@lem5166857) (@lem5166856 e)). Qed.
Lemma lem5166859 (e : real) (l : real) : (term79 e l) = (term23 e l).
Proof. exact (MK_COMB (@lem5166858 e) (@lem5166813 l)). Qed.
Lemma lem5166860 (e : real) (l : real) : (term78 e l) = (term23 e l).
Proof. exact (TRANS (@lem5166812 e l) (@lem5166859 e l)). Qed.
Lemma lem5166861 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem5166862 (x : real) (e : real) (l : real) : (term77 x e l) = (term107 x e l).
Proof. exact (MK_COMB (@lem5166861 x) (@lem5166860 e l)). Qed.
Lemma lem5166863 (e : real) (x : real) (l : real) : (term107 x e l) = (term107 e x l).
Proof. exact (@lem1982757 e x (term25 l)). Qed.
Lemma lem5166864 (l : real) (x : real) : (term23 x l) = (term24 l x).
Proof. exact (@lem1982761 (term25 l) x). Qed.
Lemma lem5166865 (e : real) : (real_add e) = (real_add e).
Proof. exact (eq_refl (real_add e)). Qed.
Lemma lem5166866 (e : real) (l : real) (x : real) : (term107 e x l) = (term108 e l x).
Proof. exact (MK_COMB (@lem5166865 e) (@lem5166864 l x)). Qed.
Lemma lem5166867 (e : real) (l : real) (x : real) : (term107 x e l) = (term108 e l x).
Proof. exact (TRANS (@lem5166863 e x l) (@lem5166866 e l x)). Qed.
Lemma lem5166868 (e : real) (l : real) (x : real) : (term77 x e l) = (term108 e l x).
Proof. exact (TRANS (@lem5166862 x e l) (@lem5166867 e l x)). Qed.
Lemma lem5166869 (e : real) (l : real) (x : real) : (term76 x e l) = (term108 e l x).
Proof. exact (TRANS (@lem5166811 x e l) (@lem5166868 e l x)). Qed.
Lemma lem5166870 (e : real) (l : real) (x : real) : (term75 x l e) = (term108 e l x).
Proof. exact (TRANS (@lem5166810 x e l) (@lem5166869 e l x)). Qed.
Lemma lem5166871 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5166872 (e : real) (l : real) (x : real) : (term109 x l e) = (term110 e l x).
Proof. exact (MK_COMB (@lem5166871) (@lem5166870 e l x)). Qed.
Lemma lem5166873 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5166874 (e : real) (l : real) (x : real) : (term74 x l e) = (term111 e l x).
Proof. exact (MK_COMB (@lem5166872 e l x) (@lem5166873)). Qed.
Lemma lem5166875 (e : real) (l : real) (x : real) : (term8 l e x) = (term111 e l x).
Proof. exact (TRANS (@lem5166793 x l e) (@lem5166874 e l x)). Qed.
Lemma lem5166876 (l : real) (e : real) (x : real) : (term9 x l e) = (term112 l e x).
Proof. exact (@lem1988287 (real_add l e) x). Qed.
Lemma lem5166877 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5166884 (e : real) (l : real) : (real_add l e) = (real_add e l).
Proof. exact (@lem1982761 e l). Qed.
Lemma lem5166885 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5166886 (e : real) (l : real) : (term113 l e) = (term113 e l).
Proof. exact (MK_COMB (@lem5166885) (@lem5166884 e l)). Qed.
Lemma lem5166887 (e : real) (l : real) (x : real) : (term114 l e x) = (term114 e l x).
Proof. exact (MK_COMB (@lem5166886 e l) (@lem5166877 x)). Qed.
Lemma lem5166888 (e : real) (l : real) (x : real) : (term114 e l x) = (term115 e l x).
Proof. exact (@lem1982792 (real_add e l) x). Qed.
Lemma lem5166897 (e : real) (l : real) (x : real) : (term115 e l x) = (term107 e l x).
Proof. exact (@lem1982755 e l (term25 x)). Qed.
Lemma lem5166898 (e : real) (l : real) (x : real) : (term114 e l x) = (term107 e l x).
Proof. exact (TRANS (@lem5166888 e l x) (@lem5166897 e l x)). Qed.
Lemma lem5166899 (e : real) (l : real) (x : real) : (term114 l e x) = (term107 e l x).
Proof. exact (TRANS (@lem5166887 e l x) (@lem5166898 e l x)). Qed.
Lemma lem5166900 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5166901 (e : real) (l : real) (x : real) : (term116 l e x) = (term117 e l x).
Proof. exact (MK_COMB (@lem5166900) (@lem5166899 e l x)). Qed.
Lemma lem5166902 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5166903 (e : real) (l : real) (x : real) : (term112 l e x) = (term118 e l x).
Proof. exact (MK_COMB (@lem5166901 e l x) (@lem5166902)). Qed.
Lemma lem5166904 (e : real) (l : real) (x : real) : (term9 x l e) = (term118 e l x).
Proof. exact (TRANS (@lem5166876 l e x) (@lem5166903 e l x)). Qed.
Lemma lem5166905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5166906 (e : real) (l : real) (x : real) : (term119 l e x) = (term120 e l x).
Proof. exact (MK_COMB (@lem5166905) (@lem5166875 e l x)). Qed.
Lemma lem5166907 (e : real) (l : real) (x : real) : (term20 x l e) = (term121 e l x).
Proof. exact (MK_COMB (@lem5166906 e l x) (@lem5166904 e l x)). Qed.
Lemma lem5166908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5166909 (e : real) (l : real) (x : real) : (term122 x l e) = (term123 e l x).
Proof. exact (MK_COMB (@lem5166908) (@lem5166792 e l x)). Qed.
Lemma lem5166910 (e : real) (l : real) (x : real) : (term10 x l e) = (term124 e l x).
Proof. exact (MK_COMB (@lem5166909 e l x) (@lem5166907 e l x)). Qed.
Lemma lem5166911 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5166912 (e : real) (l : real) (x : real) : (term15 x l e) = (term125 e l x).
Proof. exact (MK_COMB (@lem5166911) (@lem5166759 e l x)). Qed.
Lemma lem5166913 (e : real) (l : real) (x : real) : (term17 x l e) = (term126 e l x).
Proof. exact (MK_COMB (@lem5166912 e l x) (@lem5166910 e l x)). Qed.
Lemma lem5166920 (e : real) (l : real) (x : real) : (term18 x l e) = (term126 e l x).
Proof. exact (TRANS (@lem5166650 x l e) (@lem5166913 e l x)). Qed.
Lemma lem5166933 (e : real) (l : real) (x : real) : (term124 e l x) = (term124 e l x).
Proof. exact (eq_refl (term124 e l x)). Qed.
Lemma lem5166950 (e : real) (l : real) (x : real) : (term62 e l x) = (term127 e l x).
Proof. exact (@lem19158 (term44 e l x) (term33 e l x) (term57 e l x)). Qed.
Lemma lem5166951 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5166952 (e : real) (l : real) (x : real) : (term125 e l x) = (term128 e l x).
Proof. exact (MK_COMB (@lem5166951) (@lem5166950 e l x)). Qed.
Lemma lem5166953 (e : real) (l : real) (x : real) : (term126 e l x) = (term129 e l x).
Proof. exact (MK_COMB (@lem5166952 e l x) (@lem5166933 e l x)). Qed.
Lemma lem5166954 (e : real) (l : real) (x : real) : (term18 x l e) = (term129 e l x).
Proof. exact (TRANS (@lem5166920 e l x) (@lem5166953 e l x)). Qed.
Lemma lem5166956 (a : real) (x : real) (r : real) : (term130 a x r) = (term131 a x r).
Proof. exact (proj1 (@lem1482680 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem5166957 (e : real) (l : real) (x : real) : (term33 e l x) = (term132 e l x).
Proof. exact (@lem5166956 e (term24 l x) term32). Qed.
Lemma lem5166976 (l : real) (x : real) : (term133 l x) = (term24 l x).
Proof. exact (@lem1982733 (term24 l x)). Qed.
Lemma lem5166979 (e : real) : (real_add e) = (real_add e).
Proof. exact (eq_refl (real_add e)). Qed.
Lemma lem5166982 (e : real) (l : real) (x : real) : (term134 e l x) = (term108 e l x).
Proof. exact (MK_COMB (@lem5166979 e) (@lem5166976 l x)). Qed.
Lemma lem5166983 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5166984 (e : real) (l : real) (x : real) : (term135 e l x) = (term110 e l x).
Proof. exact (MK_COMB (@lem5166983) (@lem5166982 e l x)). Qed.
Lemma lem5166985 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5166986 (e : real) (l : real) (x : real) : (term136 e l x) = (term111 e l x).
Proof. exact (MK_COMB (@lem5166984 e l x) (@lem5166985)). Qed.
Lemma lem5167004 (l : real) (x : real) : (term78 l x) = (term79 l x).
Proof. exact (@lem1982781 (term25 l) term51 x). Qed.
Lemma lem5167005 (x : real) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem5167006 (l : real) : (term80 l) = (term81 l).
Proof. exact (@lem1982749 term51 term51 l). Qed.
Lemma lem5167008 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5167009 : term51 = term84.
Proof. exact (@lem5167008 term85). Qed.
Lemma lem5167011 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5167012 : term51 = term84.
Proof. exact (@lem5167011 term85). Qed.
Lemma lem5167013 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5167014 : term86 = term87.
Proof. exact (MK_COMB (@lem5167013) (@lem5167012)). Qed.
Lemma lem5167015 : term88 = term89.
Proof. exact (MK_COMB (@lem5167014) (@lem5167009)). Qed.
Lemma lem5167016 : term89 = term90.
Proof. exact (@lem1981613 term51 term51 term91 term91). Qed.
Lemma lem5167018 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5167019 : term94 = term95.
Proof. exact (@lem5167018 term85 term85). Qed.
Lemma lem5167020 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167021 : term97 = term85.
Proof. exact (EQ_MP (@lem5167020) (@lem940073)). Qed.
Lemma lem5167022 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167023 : term95 = term91.
Proof. exact (MK_COMB (@lem5167022) (@lem5167021)). Qed.
Lemma lem5167024 : term94 = term91.
Proof. exact (TRANS (@lem5167019) (@lem5167023)). Qed.
Lemma lem5167026 (m : nat) (n : nat) : (term98 m n) = (term93 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5167027 : term88 = term95.
Proof. exact (@lem5167026 term85 term85). Qed.
Lemma lem5167028 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167029 : term97 = term85.
Proof. exact (EQ_MP (@lem5167028) (@lem940073)). Qed.
Lemma lem5167030 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167031 : term95 = term91.
Proof. exact (MK_COMB (@lem5167030) (@lem5167029)). Qed.
Lemma lem5167032 : term88 = term91.
Proof. exact (TRANS (@lem5167027) (@lem5167031)). Qed.
Lemma lem5167033 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5167034 : term99 = term100.
Proof. exact (MK_COMB (@lem5167033) (@lem5167032)). Qed.
Lemma lem5167035 : term90 = term101.
Proof. exact (MK_COMB (@lem5167034) (@lem5167024)). Qed.
Lemma lem5167036 : term89 = term101.
Proof. exact (TRANS (@lem5167016) (@lem5167035)). Qed.
Lemma lem5167037 : term88 = term101.
Proof. exact (TRANS (@lem5167015) (@lem5167036)). Qed.
Lemma lem5167039 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5167040 : term101 = term91.
Proof. exact (@lem5167039 term91). Qed.
Lemma lem5167041 : term88 = term91.
Proof. exact (TRANS (@lem5167037) (@lem5167040)). Qed.
Lemma lem5167042 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5167043 : term103 = term104.
Proof. exact (MK_COMB (@lem5167042) (@lem5167041)). Qed.
Lemma lem5167044 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5167045 (l : real) : (term81 l) = (term105 l).
Proof. exact (MK_COMB (@lem5167043) (@lem5167044 l)). Qed.
Lemma lem5167046 (l : real) : (term80 l) = (term105 l).
Proof. exact (TRANS (@lem5167006 l) (@lem5167045 l)). Qed.
Lemma lem5167047 (l : real) : (term105 l) = l.
Proof. exact (@lem1982709 l). Qed.
Lemma lem5167048 (l : real) : (term80 l) = l.
Proof. exact (TRANS (@lem5167046 l) (@lem5167047 l)). Qed.
Lemma lem5167049 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5167050 (l : real) : (term106 l) = (real_add l).
Proof. exact (MK_COMB (@lem5167049) (@lem5167048 l)). Qed.
Lemma lem5167051 (l : real) (x : real) : (term79 l x) = (term23 l x).
Proof. exact (MK_COMB (@lem5167050 l) (@lem5167005 x)). Qed.
Lemma lem5167053 (l : real) (x : real) : (term78 l x) = (term23 l x).
Proof. exact (TRANS (@lem5167004 l x) (@lem5167051 l x)). Qed.
Lemma lem5167056 (e : real) : (real_add e) = (real_add e).
Proof. exact (eq_refl (real_add e)). Qed.
Lemma lem5167059 (e : real) (l : real) (x : real) : (term77 e l x) = (term107 e l x).
Proof. exact (MK_COMB (@lem5167056 e) (@lem5167053 l x)). Qed.
Lemma lem5167060 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5167061 (e : real) (l : real) (x : real) : (term137 e l x) = (term117 e l x).
Proof. exact (MK_COMB (@lem5167060) (@lem5167059 e l x)). Qed.
Lemma lem5167062 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5167063 (e : real) (l : real) (x : real) : (term138 e l x) = (term118 e l x).
Proof. exact (MK_COMB (@lem5167061 e l x) (@lem5167062)). Qed.
Lemma lem5167064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5167065 (e : real) (l : real) (x : real) : (term139 e l x) = (term140 e l x).
Proof. exact (MK_COMB (@lem5167064) (@lem5167063 e l x)). Qed.
Lemma lem5167066 (e : real) (l : real) (x : real) : (term132 e l x) = (term141 e l x).
Proof. exact (MK_COMB (@lem5167065 e l x) (@lem5166986 e l x)). Qed.
Lemma lem5167067 (e : real) (l : real) (x : real) : (term33 e l x) = (term141 e l x).
Proof. exact (TRANS (@lem5166957 e l x) (@lem5167066 e l x)). Qed.
Lemma lem5167068 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5167069 (e : real) (l : real) (x : real) : (term61 e l x) = (term142 e l x).
Proof. exact (MK_COMB (@lem5167068) (@lem5167067 e l x)). Qed.
Lemma lem5167070 (e : real) (l : real) (x : real) : (term44 e l x) = (term44 e l x).
Proof. exact (eq_refl (term44 e l x)). Qed.
Lemma lem5167073 (e : real) (l : real) (x : real) : (term143 e l x) = (term144 e l x).
Proof. exact (MK_COMB (@lem5167069 e l x) (@lem5167070 e l x)). Qed.
Lemma lem5167075 (a : real) (x : real) (r : real) : (term130 a x r) = (term131 a x r).
Proof. exact (proj1 (@lem1482680 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem5167076 (e : real) (l : real) (x : real) : (term33 e l x) = (term132 e l x).
Proof. exact (@lem5167075 e (term24 l x) term32). Qed.
Lemma lem5167095 (l : real) (x : real) : (term133 l x) = (term24 l x).
Proof. exact (@lem1982733 (term24 l x)). Qed.
Lemma lem5167098 (e : real) : (real_add e) = (real_add e).
Proof. exact (eq_refl (real_add e)). Qed.
Lemma lem5167101 (e : real) (l : real) (x : real) : (term134 e l x) = (term108 e l x).
Proof. exact (MK_COMB (@lem5167098 e) (@lem5167095 l x)). Qed.
Lemma lem5167102 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5167103 (e : real) (l : real) (x : real) : (term135 e l x) = (term110 e l x).
Proof. exact (MK_COMB (@lem5167102) (@lem5167101 e l x)). Qed.
Lemma lem5167104 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5167105 (e : real) (l : real) (x : real) : (term136 e l x) = (term111 e l x).
Proof. exact (MK_COMB (@lem5167103 e l x) (@lem5167104)). Qed.
Lemma lem5167123 (l : real) (x : real) : (term78 l x) = (term79 l x).
Proof. exact (@lem1982781 (term25 l) term51 x). Qed.
Lemma lem5167124 (x : real) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem5167125 (l : real) : (term80 l) = (term81 l).
Proof. exact (@lem1982749 term51 term51 l). Qed.
Lemma lem5167127 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5167128 : term51 = term84.
Proof. exact (@lem5167127 term85). Qed.
Lemma lem5167130 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5167131 : term51 = term84.
Proof. exact (@lem5167130 term85). Qed.
Lemma lem5167132 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5167133 : term86 = term87.
Proof. exact (MK_COMB (@lem5167132) (@lem5167131)). Qed.
Lemma lem5167134 : term88 = term89.
Proof. exact (MK_COMB (@lem5167133) (@lem5167128)). Qed.
Lemma lem5167135 : term89 = term90.
Proof. exact (@lem1981613 term51 term51 term91 term91). Qed.
Lemma lem5167137 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5167138 : term94 = term95.
Proof. exact (@lem5167137 term85 term85). Qed.
Lemma lem5167139 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167140 : term97 = term85.
Proof. exact (EQ_MP (@lem5167139) (@lem940073)). Qed.
Lemma lem5167141 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167142 : term95 = term91.
Proof. exact (MK_COMB (@lem5167141) (@lem5167140)). Qed.
Lemma lem5167143 : term94 = term91.
Proof. exact (TRANS (@lem5167138) (@lem5167142)). Qed.
Lemma lem5167145 (m : nat) (n : nat) : (term98 m n) = (term93 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5167146 : term88 = term95.
Proof. exact (@lem5167145 term85 term85). Qed.
Lemma lem5167147 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167148 : term97 = term85.
Proof. exact (EQ_MP (@lem5167147) (@lem940073)). Qed.
Lemma lem5167149 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167150 : term95 = term91.
Proof. exact (MK_COMB (@lem5167149) (@lem5167148)). Qed.
Lemma lem5167151 : term88 = term91.
Proof. exact (TRANS (@lem5167146) (@lem5167150)). Qed.
Lemma lem5167152 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5167153 : term99 = term100.
Proof. exact (MK_COMB (@lem5167152) (@lem5167151)). Qed.
Lemma lem5167154 : term90 = term101.
Proof. exact (MK_COMB (@lem5167153) (@lem5167143)). Qed.
Lemma lem5167155 : term89 = term101.
Proof. exact (TRANS (@lem5167135) (@lem5167154)). Qed.
Lemma lem5167156 : term88 = term101.
Proof. exact (TRANS (@lem5167134) (@lem5167155)). Qed.
Lemma lem5167158 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5167159 : term101 = term91.
Proof. exact (@lem5167158 term91). Qed.
Lemma lem5167160 : term88 = term91.
Proof. exact (TRANS (@lem5167156) (@lem5167159)). Qed.
Lemma lem5167161 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5167162 : term103 = term104.
Proof. exact (MK_COMB (@lem5167161) (@lem5167160)). Qed.
Lemma lem5167163 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5167164 (l : real) : (term81 l) = (term105 l).
Proof. exact (MK_COMB (@lem5167162) (@lem5167163 l)). Qed.
Lemma lem5167165 (l : real) : (term80 l) = (term105 l).
Proof. exact (TRANS (@lem5167125 l) (@lem5167164 l)). Qed.
Lemma lem5167166 (l : real) : (term105 l) = l.
Proof. exact (@lem1982709 l). Qed.
Lemma lem5167167 (l : real) : (term80 l) = l.
Proof. exact (TRANS (@lem5167165 l) (@lem5167166 l)). Qed.
Lemma lem5167168 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5167169 (l : real) : (term106 l) = (real_add l).
Proof. exact (MK_COMB (@lem5167168) (@lem5167167 l)). Qed.
Lemma lem5167170 (l : real) (x : real) : (term79 l x) = (term23 l x).
Proof. exact (MK_COMB (@lem5167169 l) (@lem5167124 x)). Qed.
Lemma lem5167172 (l : real) (x : real) : (term78 l x) = (term23 l x).
Proof. exact (TRANS (@lem5167123 l x) (@lem5167170 l x)). Qed.
Lemma lem5167175 (e : real) : (real_add e) = (real_add e).
Proof. exact (eq_refl (real_add e)). Qed.
Lemma lem5167178 (e : real) (l : real) (x : real) : (term77 e l x) = (term107 e l x).
Proof. exact (MK_COMB (@lem5167175 e) (@lem5167172 l x)). Qed.
Lemma lem5167179 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5167180 (e : real) (l : real) (x : real) : (term137 e l x) = (term117 e l x).
Proof. exact (MK_COMB (@lem5167179) (@lem5167178 e l x)). Qed.
Lemma lem5167181 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5167182 (e : real) (l : real) (x : real) : (term138 e l x) = (term118 e l x).
Proof. exact (MK_COMB (@lem5167180 e l x) (@lem5167181)). Qed.
Lemma lem5167183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5167184 (e : real) (l : real) (x : real) : (term139 e l x) = (term140 e l x).
Proof. exact (MK_COMB (@lem5167183) (@lem5167182 e l x)). Qed.
Lemma lem5167185 (e : real) (l : real) (x : real) : (term132 e l x) = (term141 e l x).
Proof. exact (MK_COMB (@lem5167184 e l x) (@lem5167105 e l x)). Qed.
Lemma lem5167186 (e : real) (l : real) (x : real) : (term33 e l x) = (term141 e l x).
Proof. exact (TRANS (@lem5167076 e l x) (@lem5167185 e l x)). Qed.
Lemma lem5167187 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5167188 (e : real) (l : real) (x : real) : (term61 e l x) = (term142 e l x).
Proof. exact (MK_COMB (@lem5167187) (@lem5167186 e l x)). Qed.
Lemma lem5167189 (e : real) (l : real) (x : real) : (term57 e l x) = (term57 e l x).
Proof. exact (eq_refl (term57 e l x)). Qed.
Lemma lem5167192 (e : real) (l : real) (x : real) : (term145 e l x) = (term146 e l x).
Proof. exact (MK_COMB (@lem5167188 e l x) (@lem5167189 e l x)). Qed.
Lemma lem5167193 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5167194 (e : real) (l : real) (x : real) : (term147 e l x) = (term148 e l x).
Proof. exact (MK_COMB (@lem5167193) (@lem5167073 e l x)). Qed.
Lemma lem5167195 (e : real) (l : real) (x : real) : (term127 e l x) = (term149 e l x).
Proof. exact (MK_COMB (@lem5167194 e l x) (@lem5167192 e l x)). Qed.
Lemma lem5167197 (e : real) (l : real) (x : real) : (term150 e l x) = (term124 e l x).
Proof. exact (eq_refl (term150 e l x)). Qed.
Lemma lem5167198 (e : real) (l : real) (x : real) : (term124 e l x) = (term150 e l x).
Proof. exact (SYM (@lem5167197 e l x)). Qed.
Lemma lem5167199 (e : real) (l : real) (x : real) : (term150 e l x) = (term151 e l x).
Proof. exact (@lem1482981 (term152 e l x) (term24 l x)). Qed.
Lemma lem5167200 (e : real) (l : real) (x : real) : (term124 e l x) = (term151 e l x).
Proof. exact (TRANS (@lem5167198 e l x) (@lem5167199 e l x)). Qed.
Lemma lem5167201 (e : real) (l : real) (x : real) : (term153 e l x) = (term154 e l x).
Proof. exact (eq_refl (term153 e l x)). Qed.
Lemma lem5167202 (l : real) (x : real) : (term155 l x) = (term155 l x).
Proof. exact (eq_refl (term155 l x)). Qed.
Lemma lem5167203 (e : real) (l : real) (x : real) : (term156 e l x) = (term157 e l x).
Proof. exact (MK_COMB (@lem5167202 l x) (@lem5167201 e l x)). Qed.
Lemma lem5167204 (e : real) (l : real) (x : real) : (term158 e l x) = (term159 e l x).
Proof. exact (eq_refl (term158 e l x)). Qed.
Lemma lem5167205 (l : real) (x : real) : (term160 l x) = (term160 l x).
Proof. exact (eq_refl (term160 l x)). Qed.
Lemma lem5167206 (e : real) (l : real) (x : real) : (term161 e l x) = (term162 e l x).
Proof. exact (MK_COMB (@lem5167205 l x) (@lem5167204 e l x)). Qed.
Lemma lem5167207 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5167208 (e : real) (l : real) (x : real) : (term163 e l x) = (term164 e l x).
Proof. exact (MK_COMB (@lem5167207) (@lem5167206 e l x)). Qed.
Lemma lem5167209 (e : real) (l : real) (x : real) : (term151 e l x) = (term165 e l x).
Proof. exact (MK_COMB (@lem5167208 e l x) (@lem5167203 e l x)). Qed.
Lemma lem5167210 (e : real) (l : real) (x : real) : (term166 e l x) = (term166 e l x).
Proof. exact (eq_refl (term166 e l x)). Qed.
Lemma lem5167211 (e : real) (l : real) (x : real) : ((term124 e l x) = (term151 e l x)) = ((term124 e l x) = (term165 e l x)).
Proof. exact (MK_COMB (@lem5167210 e l x) (@lem5167209 e l x)). Qed.
Lemma lem5167212 (e : real) (l : real) (x : real) : (term124 e l x) = (term165 e l x).
Proof. exact (EQ_MP (@lem5167211 e l x) (@lem5167200 e l x)). Qed.
Lemma lem5167213 (l : real) (x : real) : (term167 l x) = (term168 l x).
Proof. exact (@lem1988291 (term24 l x) term32). Qed.
Lemma lem5167231 (l : real) (x : real) : (term169 l x) = (term170 l x).
Proof. exact (@lem1982792 (term24 l x) term32). Qed.
Lemma lem5167233 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5167234 : term32 = term172.
Proof. exact (@lem5167233 (NUMERAL 0)). Qed.
Lemma lem5167236 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5167237 : term51 = term84.
Proof. exact (@lem5167236 term85). Qed.
Lemma lem5167238 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5167239 : term86 = term87.
Proof. exact (MK_COMB (@lem5167238) (@lem5167237)). Qed.
Lemma lem5167240 : term173 = term174.
Proof. exact (MK_COMB (@lem5167239) (@lem5167234)). Qed.
Lemma lem5167241 : term174 = term175.
Proof. exact (@lem1981613 term51 term32 term91 term91). Qed.
Lemma lem5167243 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5167244 : term94 = term95.
Proof. exact (@lem5167243 term85 term85). Qed.
Lemma lem5167245 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167246 : term97 = term85.
Proof. exact (EQ_MP (@lem5167245) (@lem940073)). Qed.
Lemma lem5167247 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167248 : term95 = term91.
Proof. exact (MK_COMB (@lem5167247) (@lem5167246)). Qed.
Lemma lem5167249 : term94 = term91.
Proof. exact (TRANS (@lem5167244) (@lem5167248)). Qed.
Lemma lem5167251 (x : nat) : (term176 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5167252 : term173 = term32.
Proof. exact (@lem5167251 term85). Qed.
Lemma lem5167253 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5167254 : term177 = term178.
Proof. exact (MK_COMB (@lem5167253) (@lem5167252)). Qed.
Lemma lem5167255 : term175 = term172.
Proof. exact (MK_COMB (@lem5167254) (@lem5167249)). Qed.
Lemma lem5167256 : term174 = term172.
Proof. exact (TRANS (@lem5167241) (@lem5167255)). Qed.
Lemma lem5167257 : term173 = term172.
Proof. exact (TRANS (@lem5167240) (@lem5167256)). Qed.
Lemma lem5167259 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5167260 : term172 = term32.
Proof. exact (@lem5167259 term32). Qed.
Lemma lem5167261 : term173 = term32.
Proof. exact (TRANS (@lem5167257) (@lem5167260)). Qed.
Lemma lem5167262 (l : real) (x : real) : (term179 l x) = (term179 l x).
Proof. exact (eq_refl (term179 l x)). Qed.
Lemma lem5167263 (l : real) (x : real) : (term170 l x) = (term180 l x).
Proof. exact (MK_COMB (@lem5167262 l x) (@lem5167261)). Qed.
Lemma lem5167264 (l : real) (x : real) : (term180 l x) = (term24 l x).
Proof. exact (@lem1982723 (term24 l x)). Qed.
Lemma lem5167265 (l : real) (x : real) : (term170 l x) = (term24 l x).
Proof. exact (TRANS (@lem5167263 l x) (@lem5167264 l x)). Qed.
Lemma lem5167267 (l : real) (x : real) : (term169 l x) = (term24 l x).
Proof. exact (TRANS (@lem5167231 l x) (@lem5167265 l x)). Qed.
Lemma lem5167268 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5167269 (l : real) (x : real) : (term181 l x) = (term182 l x).
Proof. exact (MK_COMB (@lem5167268) (@lem5167267 l x)). Qed.
Lemma lem5167270 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5167271 (l : real) (x : real) : (term168 l x) = (term167 l x).
Proof. exact (MK_COMB (@lem5167269 l x) (@lem5167270)). Qed.
Lemma lem5167272 (l : real) (x : real) : (term167 l x) = (term167 l x).
Proof. exact (TRANS (@lem5167213 l x) (@lem5167271 l x)). Qed.
Lemma lem5167273 (e : real) (l : real) (x : real) : (term57 e l x) = (term183 e l x).
Proof. exact (@lem1988289 (term54 e l x) term32). Qed.
Lemma lem5167303 (e : real) (l : real) (x : real) : (term184 e l x) = (term185 e l x).
Proof. exact (@lem1982792 (term54 e l x) term32). Qed.
Lemma lem5167305 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5167306 : term32 = term172.
Proof. exact (@lem5167305 (NUMERAL 0)). Qed.
Lemma lem5167308 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5167309 : term51 = term84.
Proof. exact (@lem5167308 term85). Qed.
Lemma lem5167310 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5167311 : term86 = term87.
Proof. exact (MK_COMB (@lem5167310) (@lem5167309)). Qed.
Lemma lem5167312 : term173 = term174.
Proof. exact (MK_COMB (@lem5167311) (@lem5167306)). Qed.
Lemma lem5167313 : term174 = term175.
Proof. exact (@lem1981613 term51 term32 term91 term91). Qed.
Lemma lem5167315 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5167316 : term94 = term95.
Proof. exact (@lem5167315 term85 term85). Qed.
Lemma lem5167317 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167318 : term97 = term85.
Proof. exact (EQ_MP (@lem5167317) (@lem940073)). Qed.
Lemma lem5167319 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167320 : term95 = term91.
Proof. exact (MK_COMB (@lem5167319) (@lem5167318)). Qed.
Lemma lem5167321 : term94 = term91.
Proof. exact (TRANS (@lem5167316) (@lem5167320)). Qed.
Lemma lem5167323 (x : nat) : (term176 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5167324 : term173 = term32.
Proof. exact (@lem5167323 term85). Qed.
Lemma lem5167325 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5167326 : term177 = term178.
Proof. exact (MK_COMB (@lem5167325) (@lem5167324)). Qed.
Lemma lem5167327 : term175 = term172.
Proof. exact (MK_COMB (@lem5167326) (@lem5167321)). Qed.
Lemma lem5167328 : term174 = term172.
Proof. exact (TRANS (@lem5167313) (@lem5167327)). Qed.
Lemma lem5167329 : term173 = term172.
Proof. exact (TRANS (@lem5167312) (@lem5167328)). Qed.
Lemma lem5167331 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5167332 : term172 = term32.
Proof. exact (@lem5167331 term32). Qed.
Lemma lem5167333 : term173 = term32.
Proof. exact (TRANS (@lem5167329) (@lem5167332)). Qed.
Lemma lem5167334 (e : real) (l : real) (x : real) : (term186 e l x) = (term186 e l x).
Proof. exact (eq_refl (term186 e l x)). Qed.
Lemma lem5167335 (e : real) (l : real) (x : real) : (term185 e l x) = (term187 e l x).
Proof. exact (MK_COMB (@lem5167334 e l x) (@lem5167333)). Qed.
Lemma lem5167336 (e : real) (l : real) (x : real) : (term187 e l x) = (term54 e l x).
Proof. exact (@lem1982723 (term54 e l x)). Qed.
Lemma lem5167337 (e : real) (l : real) (x : real) : (term185 e l x) = (term54 e l x).
Proof. exact (TRANS (@lem5167335 e l x) (@lem5167336 e l x)). Qed.
Lemma lem5167339 (e : real) (l : real) (x : real) : (term184 e l x) = (term54 e l x).
Proof. exact (TRANS (@lem5167303 e l x) (@lem5167337 e l x)). Qed.
Lemma lem5167340 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5167341 (e : real) (l : real) (x : real) : (term188 e l x) = (term56 e l x).
Proof. exact (MK_COMB (@lem5167340) (@lem5167339 e l x)). Qed.
Lemma lem5167342 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5167343 (e : real) (l : real) (x : real) : (term183 e l x) = (term57 e l x).
Proof. exact (MK_COMB (@lem5167341 e l x) (@lem5167342)). Qed.
Lemma lem5167344 (e : real) (l : real) (x : real) : (term57 e l x) = (term57 e l x).
Proof. exact (TRANS (@lem5167273 e l x) (@lem5167343 e l x)). Qed.
Lemma lem5167345 (e : real) (l : real) (x : real) : (term111 e l x) = (term189 e l x).
Proof. exact (@lem1988291 (term108 e l x) term32). Qed.
Lemma lem5167369 (e : real) (l : real) (x : real) : (term190 e l x) = (term191 e l x).
Proof. exact (@lem1982792 (term108 e l x) term32). Qed.
Lemma lem5167371 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5167372 : term32 = term172.
Proof. exact (@lem5167371 (NUMERAL 0)). Qed.
Lemma lem5167374 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5167375 : term51 = term84.
Proof. exact (@lem5167374 term85). Qed.
Lemma lem5167376 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5167377 : term86 = term87.
Proof. exact (MK_COMB (@lem5167376) (@lem5167375)). Qed.
Lemma lem5167378 : term173 = term174.
Proof. exact (MK_COMB (@lem5167377) (@lem5167372)). Qed.
Lemma lem5167379 : term174 = term175.
Proof. exact (@lem1981613 term51 term32 term91 term91). Qed.
Lemma lem5167381 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5167382 : term94 = term95.
Proof. exact (@lem5167381 term85 term85). Qed.
Lemma lem5167383 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167384 : term97 = term85.
Proof. exact (EQ_MP (@lem5167383) (@lem940073)). Qed.
Lemma lem5167385 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167386 : term95 = term91.
Proof. exact (MK_COMB (@lem5167385) (@lem5167384)). Qed.
Lemma lem5167387 : term94 = term91.
Proof. exact (TRANS (@lem5167382) (@lem5167386)). Qed.
Lemma lem5167389 (x : nat) : (term176 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5167390 : term173 = term32.
Proof. exact (@lem5167389 term85). Qed.
Lemma lem5167391 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5167392 : term177 = term178.
Proof. exact (MK_COMB (@lem5167391) (@lem5167390)). Qed.
Lemma lem5167393 : term175 = term172.
Proof. exact (MK_COMB (@lem5167392) (@lem5167387)). Qed.
Lemma lem5167394 : term174 = term172.
Proof. exact (TRANS (@lem5167379) (@lem5167393)). Qed.
Lemma lem5167395 : term173 = term172.
Proof. exact (TRANS (@lem5167378) (@lem5167394)). Qed.
Lemma lem5167397 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5167398 : term172 = term32.
Proof. exact (@lem5167397 term32). Qed.
Lemma lem5167399 : term173 = term32.
Proof. exact (TRANS (@lem5167395) (@lem5167398)). Qed.
Lemma lem5167400 (e : real) (l : real) (x : real) : (term192 e l x) = (term192 e l x).
Proof. exact (eq_refl (term192 e l x)). Qed.
Lemma lem5167401 (e : real) (l : real) (x : real) : (term191 e l x) = (term193 e l x).
Proof. exact (MK_COMB (@lem5167400 e l x) (@lem5167399)). Qed.
Lemma lem5167402 (e : real) (l : real) (x : real) : (term193 e l x) = (term108 e l x).
Proof. exact (@lem1982723 (term108 e l x)). Qed.
Lemma lem5167403 (e : real) (l : real) (x : real) : (term191 e l x) = (term108 e l x).
Proof. exact (TRANS (@lem5167401 e l x) (@lem5167402 e l x)). Qed.
Lemma lem5167405 (e : real) (l : real) (x : real) : (term190 e l x) = (term108 e l x).
Proof. exact (TRANS (@lem5167369 e l x) (@lem5167403 e l x)). Qed.
Lemma lem5167406 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5167407 (e : real) (l : real) (x : real) : (term194 e l x) = (term110 e l x).
Proof. exact (MK_COMB (@lem5167406) (@lem5167405 e l x)). Qed.
Lemma lem5167408 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5167409 (e : real) (l : real) (x : real) : (term189 e l x) = (term111 e l x).
Proof. exact (MK_COMB (@lem5167407 e l x) (@lem5167408)). Qed.
Lemma lem5167410 (e : real) (l : real) (x : real) : (term111 e l x) = (term111 e l x).
Proof. exact (TRANS (@lem5167345 e l x) (@lem5167409 e l x)). Qed.
Lemma lem5167411 (e : real) (l : real) (x : real) : (term118 e l x) = (term195 e l x).
Proof. exact (@lem1988291 (term107 e l x) term32). Qed.
Lemma lem5167435 (e : real) (l : real) (x : real) : (term196 e l x) = (term197 e l x).
Proof. exact (@lem1982792 (term107 e l x) term32). Qed.
Lemma lem5167437 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5167438 : term32 = term172.
Proof. exact (@lem5167437 (NUMERAL 0)). Qed.
Lemma lem5167440 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5167441 : term51 = term84.
Proof. exact (@lem5167440 term85). Qed.
Lemma lem5167442 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5167443 : term86 = term87.
Proof. exact (MK_COMB (@lem5167442) (@lem5167441)). Qed.
Lemma lem5167444 : term173 = term174.
Proof. exact (MK_COMB (@lem5167443) (@lem5167438)). Qed.
Lemma lem5167445 : term174 = term175.
Proof. exact (@lem1981613 term51 term32 term91 term91). Qed.
Lemma lem5167447 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5167448 : term94 = term95.
Proof. exact (@lem5167447 term85 term85). Qed.
Lemma lem5167449 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167450 : term97 = term85.
Proof. exact (EQ_MP (@lem5167449) (@lem940073)). Qed.
Lemma lem5167451 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167452 : term95 = term91.
Proof. exact (MK_COMB (@lem5167451) (@lem5167450)). Qed.
Lemma lem5167453 : term94 = term91.
Proof. exact (TRANS (@lem5167448) (@lem5167452)). Qed.
Lemma lem5167455 (x : nat) : (term176 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5167456 : term173 = term32.
Proof. exact (@lem5167455 term85). Qed.
Lemma lem5167457 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5167458 : term177 = term178.
Proof. exact (MK_COMB (@lem5167457) (@lem5167456)). Qed.
Lemma lem5167459 : term175 = term172.
Proof. exact (MK_COMB (@lem5167458) (@lem5167453)). Qed.
Lemma lem5167460 : term174 = term172.
Proof. exact (TRANS (@lem5167445) (@lem5167459)). Qed.
Lemma lem5167461 : term173 = term172.
Proof. exact (TRANS (@lem5167444) (@lem5167460)). Qed.
Lemma lem5167463 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5167464 : term172 = term32.
Proof. exact (@lem5167463 term32). Qed.
Lemma lem5167465 : term173 = term32.
Proof. exact (TRANS (@lem5167461) (@lem5167464)). Qed.
Lemma lem5167466 (e : real) (l : real) (x : real) : (term198 e l x) = (term198 e l x).
Proof. exact (eq_refl (term198 e l x)). Qed.
Lemma lem5167467 (e : real) (l : real) (x : real) : (term197 e l x) = (term199 e l x).
Proof. exact (MK_COMB (@lem5167466 e l x) (@lem5167465)). Qed.
Lemma lem5167468 (e : real) (l : real) (x : real) : (term199 e l x) = (term107 e l x).
Proof. exact (@lem1982723 (term107 e l x)). Qed.
Lemma lem5167469 (e : real) (l : real) (x : real) : (term197 e l x) = (term107 e l x).
Proof. exact (TRANS (@lem5167467 e l x) (@lem5167468 e l x)). Qed.
Lemma lem5167471 (e : real) (l : real) (x : real) : (term196 e l x) = (term107 e l x).
Proof. exact (TRANS (@lem5167435 e l x) (@lem5167469 e l x)). Qed.
Lemma lem5167472 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5167473 (e : real) (l : real) (x : real) : (term200 e l x) = (term117 e l x).
Proof. exact (MK_COMB (@lem5167472) (@lem5167471 e l x)). Qed.
Lemma lem5167474 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5167475 (e : real) (l : real) (x : real) : (term195 e l x) = (term118 e l x).
Proof. exact (MK_COMB (@lem5167473 e l x) (@lem5167474)). Qed.
Lemma lem5167476 (e : real) (l : real) (x : real) : (term118 e l x) = (term118 e l x).
Proof. exact (TRANS (@lem5167411 e l x) (@lem5167475 e l x)). Qed.
Lemma lem5167477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5167478 (e : real) (l : real) (x : real) : (term120 e l x) = (term120 e l x).
Proof. exact (MK_COMB (@lem5167477) (@lem5167410 e l x)). Qed.
Lemma lem5167479 (e : real) (l : real) (x : real) : (term121 e l x) = (term121 e l x).
Proof. exact (MK_COMB (@lem5167478 e l x) (@lem5167476 e l x)). Qed.
Lemma lem5167480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5167481 (e : real) (l : real) (x : real) : (term201 e l x) = (term201 e l x).
Proof. exact (MK_COMB (@lem5167480) (@lem5167344 e l x)). Qed.
Lemma lem5167482 (e : real) (l : real) (x : real) : (term159 e l x) = (term159 e l x).
Proof. exact (MK_COMB (@lem5167481 e l x) (@lem5167479 e l x)). Qed.
Lemma lem5167483 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5167484 (l : real) (x : real) : (term160 l x) = (term160 l x).
Proof. exact (MK_COMB (@lem5167483) (@lem5167272 l x)). Qed.
Lemma lem5167485 (e : real) (l : real) (x : real) : (term162 e l x) = (term162 e l x).
Proof. exact (MK_COMB (@lem5167484 l x) (@lem5167482 e l x)). Qed.
Lemma lem5167486 (l : real) (x : real) : (term202 l x) = (term203 l x).
Proof. exact (@lem1988289 term32 (term24 l x)). Qed.
Lemma lem5167504 (l : real) (x : real) : (term204 l x) = (term205 l x).
Proof. exact (@lem1982792 term32 (term24 l x)). Qed.
Lemma lem5167505 (l : real) (x : real) : (term78 l x) = (term79 l x).
Proof. exact (@lem1982781 (term25 l) term51 x). Qed.
Lemma lem5167506 (x : real) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem5167507 (l : real) : (term80 l) = (term81 l).
Proof. exact (@lem1982749 term51 term51 l). Qed.
Lemma lem5167509 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5167510 : term51 = term84.
Proof. exact (@lem5167509 term85). Qed.
Lemma lem5167512 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5167513 : term51 = term84.
Proof. exact (@lem5167512 term85). Qed.
Lemma lem5167514 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5167515 : term86 = term87.
Proof. exact (MK_COMB (@lem5167514) (@lem5167513)). Qed.
Lemma lem5167516 : term88 = term89.
Proof. exact (MK_COMB (@lem5167515) (@lem5167510)). Qed.
Lemma lem5167517 : term89 = term90.
Proof. exact (@lem1981613 term51 term51 term91 term91). Qed.
Lemma lem5167519 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5167520 : term94 = term95.
Proof. exact (@lem5167519 term85 term85). Qed.
Lemma lem5167521 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167522 : term97 = term85.
Proof. exact (EQ_MP (@lem5167521) (@lem940073)). Qed.
Lemma lem5167523 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167524 : term95 = term91.
Proof. exact (MK_COMB (@lem5167523) (@lem5167522)). Qed.
Lemma lem5167525 : term94 = term91.
Proof. exact (TRANS (@lem5167520) (@lem5167524)). Qed.
Lemma lem5167527 (m : nat) (n : nat) : (term98 m n) = (term93 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5167528 : term88 = term95.
Proof. exact (@lem5167527 term85 term85). Qed.
Lemma lem5167529 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167530 : term97 = term85.
Proof. exact (EQ_MP (@lem5167529) (@lem940073)). Qed.
Lemma lem5167531 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167532 : term95 = term91.
Proof. exact (MK_COMB (@lem5167531) (@lem5167530)). Qed.
Lemma lem5167533 : term88 = term91.
Proof. exact (TRANS (@lem5167528) (@lem5167532)). Qed.
Lemma lem5167534 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5167535 : term99 = term100.
Proof. exact (MK_COMB (@lem5167534) (@lem5167533)). Qed.
Lemma lem5167536 : term90 = term101.
Proof. exact (MK_COMB (@lem5167535) (@lem5167525)). Qed.
Lemma lem5167537 : term89 = term101.
Proof. exact (TRANS (@lem5167517) (@lem5167536)). Qed.
Lemma lem5167538 : term88 = term101.
Proof. exact (TRANS (@lem5167516) (@lem5167537)). Qed.
Lemma lem5167540 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5167541 : term101 = term91.
Proof. exact (@lem5167540 term91). Qed.
Lemma lem5167542 : term88 = term91.
Proof. exact (TRANS (@lem5167538) (@lem5167541)). Qed.
Lemma lem5167543 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5167544 : term103 = term104.
Proof. exact (MK_COMB (@lem5167543) (@lem5167542)). Qed.
Lemma lem5167545 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5167546 (l : real) : (term81 l) = (term105 l).
Proof. exact (MK_COMB (@lem5167544) (@lem5167545 l)). Qed.
Lemma lem5167547 (l : real) : (term80 l) = (term105 l).
Proof. exact (TRANS (@lem5167507 l) (@lem5167546 l)). Qed.
Lemma lem5167548 (l : real) : (term105 l) = l.
Proof. exact (@lem1982709 l). Qed.
Lemma lem5167549 (l : real) : (term80 l) = l.
Proof. exact (TRANS (@lem5167547 l) (@lem5167548 l)). Qed.
Lemma lem5167550 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5167551 (l : real) : (term106 l) = (real_add l).
Proof. exact (MK_COMB (@lem5167550) (@lem5167549 l)). Qed.
Lemma lem5167552 (l : real) (x : real) : (term79 l x) = (term23 l x).
Proof. exact (MK_COMB (@lem5167551 l) (@lem5167506 x)). Qed.
Lemma lem5167553 (l : real) (x : real) : (term78 l x) = (term23 l x).
Proof. exact (TRANS (@lem5167505 l x) (@lem5167552 l x)). Qed.
Lemma lem5167554 : term206 = term206.
Proof. exact (eq_refl term206). Qed.
Lemma lem5167555 (l : real) (x : real) : (term205 l x) = (term207 l x).
Proof. exact (MK_COMB (@lem5167554) (@lem5167553 l x)). Qed.
Lemma lem5167556 (l : real) (x : real) : (term207 l x) = (term23 l x).
Proof. exact (@lem1982721 (term23 l x)). Qed.
Lemma lem5167557 (l : real) (x : real) : (term205 l x) = (term23 l x).
Proof. exact (TRANS (@lem5167555 l x) (@lem5167556 l x)). Qed.
Lemma lem5167559 (l : real) (x : real) : (term204 l x) = (term23 l x).
Proof. exact (TRANS (@lem5167504 l x) (@lem5167557 l x)). Qed.
Lemma lem5167560 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5167561 (l : real) (x : real) : (term208 l x) = (term209 l x).
Proof. exact (MK_COMB (@lem5167560) (@lem5167559 l x)). Qed.
Lemma lem5167562 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5167563 (l : real) (x : real) : (term203 l x) = (term210 l x).
Proof. exact (MK_COMB (@lem5167561 l x) (@lem5167562)). Qed.
Lemma lem5167564 (l : real) (x : real) : (term202 l x) = (term210 l x).
Proof. exact (TRANS (@lem5167486 l x) (@lem5167563 l x)). Qed.
Lemma lem5167565 (e : real) (l : real) (x : real) : (term211 e l x) = (term212 e l x).
Proof. exact (@lem1988289 (term213 e l x) term32). Qed.
Lemma lem5167566 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5167582 (l : real) (x : real) : (term214 l x) = (term78 l x).
Proof. exact (@lem1982785 (term24 l x)). Qed.
Lemma lem5167583 (l : real) (x : real) : (term78 l x) = (term79 l x).
Proof. exact (@lem1982781 (term25 l) term51 x). Qed.
Lemma lem5167584 (x : real) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem5167585 (l : real) : (term80 l) = (term81 l).
Proof. exact (@lem1982749 term51 term51 l). Qed.
Lemma lem5167587 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5167588 : term51 = term84.
Proof. exact (@lem5167587 term85). Qed.
Lemma lem5167590 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5167591 : term51 = term84.
Proof. exact (@lem5167590 term85). Qed.
Lemma lem5167592 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5167593 : term86 = term87.
Proof. exact (MK_COMB (@lem5167592) (@lem5167591)). Qed.
Lemma lem5167594 : term88 = term89.
Proof. exact (MK_COMB (@lem5167593) (@lem5167588)). Qed.
Lemma lem5167595 : term89 = term90.
Proof. exact (@lem1981613 term51 term51 term91 term91). Qed.
Lemma lem5167597 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5167598 : term94 = term95.
Proof. exact (@lem5167597 term85 term85). Qed.
Lemma lem5167599 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167600 : term97 = term85.
Proof. exact (EQ_MP (@lem5167599) (@lem940073)). Qed.
Lemma lem5167601 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167602 : term95 = term91.
Proof. exact (MK_COMB (@lem5167601) (@lem5167600)). Qed.
Lemma lem5167603 : term94 = term91.
Proof. exact (TRANS (@lem5167598) (@lem5167602)). Qed.
Lemma lem5167605 (m : nat) (n : nat) : (term98 m n) = (term93 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5167606 : term88 = term95.
Proof. exact (@lem5167605 term85 term85). Qed.
Lemma lem5167607 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167608 : term97 = term85.
Proof. exact (EQ_MP (@lem5167607) (@lem940073)). Qed.
Lemma lem5167609 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167610 : term95 = term91.
Proof. exact (MK_COMB (@lem5167609) (@lem5167608)). Qed.
Lemma lem5167611 : term88 = term91.
Proof. exact (TRANS (@lem5167606) (@lem5167610)). Qed.
Lemma lem5167612 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5167613 : term99 = term100.
Proof. exact (MK_COMB (@lem5167612) (@lem5167611)). Qed.
Lemma lem5167614 : term90 = term101.
Proof. exact (MK_COMB (@lem5167613) (@lem5167603)). Qed.
Lemma lem5167615 : term89 = term101.
Proof. exact (TRANS (@lem5167595) (@lem5167614)). Qed.
Lemma lem5167616 : term88 = term101.
Proof. exact (TRANS (@lem5167594) (@lem5167615)). Qed.
Lemma lem5167618 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5167619 : term101 = term91.
Proof. exact (@lem5167618 term91). Qed.
Lemma lem5167620 : term88 = term91.
Proof. exact (TRANS (@lem5167616) (@lem5167619)). Qed.
Lemma lem5167621 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5167622 : term103 = term104.
Proof. exact (MK_COMB (@lem5167621) (@lem5167620)). Qed.
Lemma lem5167623 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5167624 (l : real) : (term81 l) = (term105 l).
Proof. exact (MK_COMB (@lem5167622) (@lem5167623 l)). Qed.
Lemma lem5167625 (l : real) : (term80 l) = (term105 l).
Proof. exact (TRANS (@lem5167585 l) (@lem5167624 l)). Qed.
Lemma lem5167626 (l : real) : (term105 l) = l.
Proof. exact (@lem1982709 l). Qed.
Lemma lem5167627 (l : real) : (term80 l) = l.
Proof. exact (TRANS (@lem5167625 l) (@lem5167626 l)). Qed.
Lemma lem5167628 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5167629 (l : real) : (term106 l) = (real_add l).
Proof. exact (MK_COMB (@lem5167628) (@lem5167627 l)). Qed.
Lemma lem5167630 (l : real) (x : real) : (term79 l x) = (term23 l x).
Proof. exact (MK_COMB (@lem5167629 l) (@lem5167584 x)). Qed.
Lemma lem5167631 (l : real) (x : real) : (term78 l x) = (term23 l x).
Proof. exact (TRANS (@lem5167583 l x) (@lem5167630 l x)). Qed.
Lemma lem5167633 (l : real) (x : real) : (term214 l x) = (term23 l x).
Proof. exact (TRANS (@lem5167582 l x) (@lem5167631 l x)). Qed.
Lemma lem5167642 (e : real) : (term53 e) = (term53 e).
Proof. exact (eq_refl (term53 e)). Qed.
Lemma lem5167645 (e : real) (l : real) (x : real) : (term213 e l x) = (term41 e l x).
Proof. exact (MK_COMB (@lem5167642 e) (@lem5167633 l x)). Qed.
Lemma lem5167646 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem5167647 (e : real) (l : real) (x : real) : (term215 e l x) = (term216 e l x).
Proof. exact (MK_COMB (@lem5167646) (@lem5167645 e l x)). Qed.
Lemma lem5167648 (e : real) (l : real) (x : real) : (term217 e l x) = (term218 e l x).
Proof. exact (MK_COMB (@lem5167647 e l x) (@lem5167566)). Qed.
Lemma lem5167649 (e : real) (l : real) (x : real) : (term218 e l x) = (term219 e l x).
Proof. exact (@lem1982792 (term41 e l x) term32). Qed.
Lemma lem5167651 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5167652 : term32 = term172.
Proof. exact (@lem5167651 (NUMERAL 0)). Qed.
Lemma lem5167654 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5167655 : term51 = term84.
Proof. exact (@lem5167654 term85). Qed.
Lemma lem5167656 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5167657 : term86 = term87.
Proof. exact (MK_COMB (@lem5167656) (@lem5167655)). Qed.
Lemma lem5167658 : term173 = term174.
Proof. exact (MK_COMB (@lem5167657) (@lem5167652)). Qed.
Lemma lem5167659 : term174 = term175.
Proof. exact (@lem1981613 term51 term32 term91 term91). Qed.
Lemma lem5167661 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5167662 : term94 = term95.
Proof. exact (@lem5167661 term85 term85). Qed.
Lemma lem5167663 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167664 : term97 = term85.
Proof. exact (EQ_MP (@lem5167663) (@lem940073)). Qed.
Lemma lem5167665 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167666 : term95 = term91.
Proof. exact (MK_COMB (@lem5167665) (@lem5167664)). Qed.
Lemma lem5167667 : term94 = term91.
Proof. exact (TRANS (@lem5167662) (@lem5167666)). Qed.
Lemma lem5167669 (x : nat) : (term176 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5167670 : term173 = term32.
Proof. exact (@lem5167669 term85). Qed.
Lemma lem5167671 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5167672 : term177 = term178.
Proof. exact (MK_COMB (@lem5167671) (@lem5167670)). Qed.
Lemma lem5167673 : term175 = term172.
Proof. exact (MK_COMB (@lem5167672) (@lem5167667)). Qed.
Lemma lem5167674 : term174 = term172.
Proof. exact (TRANS (@lem5167659) (@lem5167673)). Qed.
Lemma lem5167675 : term173 = term172.
Proof. exact (TRANS (@lem5167658) (@lem5167674)). Qed.
Lemma lem5167677 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5167678 : term172 = term32.
Proof. exact (@lem5167677 term32). Qed.
Lemma lem5167679 : term173 = term32.
Proof. exact (TRANS (@lem5167675) (@lem5167678)). Qed.
Lemma lem5167680 (e : real) (l : real) (x : real) : (term220 e l x) = (term220 e l x).
Proof. exact (eq_refl (term220 e l x)). Qed.
Lemma lem5167681 (e : real) (l : real) (x : real) : (term219 e l x) = (term221 e l x).
Proof. exact (MK_COMB (@lem5167680 e l x) (@lem5167679)). Qed.
Lemma lem5167682 (e : real) (l : real) (x : real) : (term221 e l x) = (term41 e l x).
Proof. exact (@lem1982723 (term41 e l x)). Qed.
Lemma lem5167683 (e : real) (l : real) (x : real) : (term219 e l x) = (term41 e l x).
Proof. exact (TRANS (@lem5167681 e l x) (@lem5167682 e l x)). Qed.
Lemma lem5167684 (e : real) (l : real) (x : real) : (term218 e l x) = (term41 e l x).
Proof. exact (TRANS (@lem5167649 e l x) (@lem5167683 e l x)). Qed.
Lemma lem5167685 (e : real) (l : real) (x : real) : (term217 e l x) = (term41 e l x).
Proof. exact (TRANS (@lem5167648 e l x) (@lem5167684 e l x)). Qed.
Lemma lem5167686 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5167687 (e : real) (l : real) (x : real) : (term222 e l x) = (term43 e l x).
Proof. exact (MK_COMB (@lem5167686) (@lem5167685 e l x)). Qed.
Lemma lem5167688 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5167689 (e : real) (l : real) (x : real) : (term212 e l x) = (term44 e l x).
Proof. exact (MK_COMB (@lem5167687 e l x) (@lem5167688)). Qed.
Lemma lem5167690 (e : real) (l : real) (x : real) : (term211 e l x) = (term44 e l x).
Proof. exact (TRANS (@lem5167565 e l x) (@lem5167689 e l x)). Qed.
Lemma lem5167691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5167692 (e : real) (l : real) (x : real) : (term120 e l x) = (term120 e l x).
Proof. exact (MK_COMB (@lem5167691) (@lem5167410 e l x)). Qed.
Lemma lem5167693 (e : real) (l : real) (x : real) : (term121 e l x) = (term121 e l x).
Proof. exact (MK_COMB (@lem5167692 e l x) (@lem5167476 e l x)). Qed.
Lemma lem5167694 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5167695 (e : real) (l : real) (x : real) : (term223 e l x) = (term224 e l x).
Proof. exact (MK_COMB (@lem5167694) (@lem5167690 e l x)). Qed.
Lemma lem5167696 (e : real) (l : real) (x : real) : (term154 e l x) = (term225 e l x).
Proof. exact (MK_COMB (@lem5167695 e l x) (@lem5167693 e l x)). Qed.
Lemma lem5167697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5167698 (l : real) (x : real) : (term155 l x) = (term226 l x).
Proof. exact (MK_COMB (@lem5167697) (@lem5167564 l x)). Qed.
Lemma lem5167699 (e : real) (l : real) (x : real) : (term157 e l x) = (term227 e l x).
Proof. exact (MK_COMB (@lem5167698 l x) (@lem5167696 e l x)). Qed.
Lemma lem5167700 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5167701 (e : real) (l : real) (x : real) : (term164 e l x) = (term164 e l x).
Proof. exact (MK_COMB (@lem5167700) (@lem5167485 e l x)). Qed.
Lemma lem5167702 (e : real) (l : real) (x : real) : (term165 e l x) = (term228 e l x).
Proof. exact (MK_COMB (@lem5167701 e l x) (@lem5167699 e l x)). Qed.
Lemma lem5167714 (e : real) (l : real) (x : real) : (term124 e l x) = (term228 e l x).
Proof. exact (TRANS (@lem5167212 e l x) (@lem5167702 e l x)). Qed.
Lemma lem5167715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5167716 (e : real) (l : real) (x : real) : (term128 e l x) = (term229 e l x).
Proof. exact (MK_COMB (@lem5167715) (@lem5167195 e l x)). Qed.
Lemma lem5167717 (e : real) (l : real) (x : real) : (term129 e l x) = (term230 e l x).
Proof. exact (MK_COMB (@lem5167716 e l x) (@lem5167714 e l x)). Qed.
Lemma lem5167718 (e : real) (l : real) (x : real) (h1 : term230 e l x) : term230 e l x.
Proof. exact (h1). Qed.
Lemma lem5167719 (e : real) (l : real) (x : real) (h1 : term149 e l x) : term149 e l x.
Proof. exact (h1). Qed.
Lemma lem5167720 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term144 e l x.
Proof. exact (h1). Qed.
Lemma lem5167721 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term44 e l x.
Proof. exact (proj2 (@lem5167720 e l x h1)). Qed.
Lemma lem5167722 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term141 e l x.
Proof. exact (proj1 (@lem5167720 e l x h1)). Qed.
Lemma lem5167723 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term111 e l x.
Proof. exact (proj2 (@lem5167722 e l x h1)). Qed.
Lemma lem5167726 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5167727 : term231 = term232.
Proof. exact (@lem5167726 term32 term91). Qed.
Lemma lem5167729 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5167730 : term91 = term101.
Proof. exact (@lem5167729 term85). Qed.
Lemma lem5167732 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5167733 : term32 = term172.
Proof. exact (@lem5167732 (NUMERAL 0)). Qed.
Lemma lem5167734 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5167735 : term233 = term234.
Proof. exact (MK_COMB (@lem5167734) (@lem5167733)). Qed.
Lemma lem5167736 : term232 = term235.
Proof. exact (MK_COMB (@lem5167735) (@lem5167730)). Qed.
Lemma lem5167737 : term236.
Proof. exact (@lem1980255 term32 term91 term91 term91). Qed.
Lemma lem5167739 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5167740 : term232 = term238.
Proof. exact (@lem5167739 (NUMERAL 0) term85). Qed.
Lemma lem5167741 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5167742 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5167743 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5167742 h1) (fun h1 : term238 = True => @lem5167741)). Qed.
Lemma lem5167744 : term238 = True.
Proof. exact (EQ_MP (@lem5167743) (@lem5167741)). Qed.
Lemma lem5167745 : term232 = True.
Proof. exact (TRANS (@lem5167740) (@lem5167744)). Qed.
Lemma lem5167746 : True = term232.
Proof. exact (SYM (@lem5167745)). Qed.
Lemma lem5167747 : term232.
Proof. exact (EQ_MP (@lem5167746) (@lem0)). Qed.
Lemma lem5167748 : term240.
Proof. exact (@lem5167737 (@lem5167747)). Qed.
Lemma lem5167750 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5167751 : term232 = term238.
Proof. exact (@lem5167750 (NUMERAL 0) term85). Qed.
Lemma lem5167752 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5167753 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5167754 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5167753 h1) (fun h1 : term238 = True => @lem5167752)). Qed.
Lemma lem5167755 : term238 = True.
Proof. exact (EQ_MP (@lem5167754) (@lem5167752)). Qed.
Lemma lem5167756 : term232 = True.
Proof. exact (TRANS (@lem5167751) (@lem5167755)). Qed.
Lemma lem5167757 : True = term232.
Proof. exact (SYM (@lem5167756)). Qed.
Lemma lem5167758 : term232.
Proof. exact (EQ_MP (@lem5167757) (@lem0)). Qed.
Lemma lem5167759 : term235 = term241.
Proof. exact (@lem5167748 (@lem5167758)). Qed.
Lemma lem5167761 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5167762 : term94 = term95.
Proof. exact (@lem5167761 term85 term85). Qed.
Lemma lem5167763 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167764 : term97 = term85.
Proof. exact (EQ_MP (@lem5167763) (@lem940073)). Qed.
Lemma lem5167765 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167766 : term95 = term91.
Proof. exact (MK_COMB (@lem5167765) (@lem5167764)). Qed.
Lemma lem5167767 : term94 = term91.
Proof. exact (TRANS (@lem5167762) (@lem5167766)). Qed.
Lemma lem5167769 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5167770 : term243 = term32.
Proof. exact (@lem5167769 term85). Qed.
Lemma lem5167771 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5167772 : term244 = term233.
Proof. exact (MK_COMB (@lem5167771) (@lem5167770)). Qed.
Lemma lem5167773 : term241 = term232.
Proof. exact (MK_COMB (@lem5167772) (@lem5167767)). Qed.
Lemma lem5167775 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5167776 : term232 = term238.
Proof. exact (@lem5167775 (NUMERAL 0) term85). Qed.
Lemma lem5167777 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5167778 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5167779 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5167778 h1) (fun h1 : term238 = True => @lem5167777)). Qed.
Lemma lem5167780 : term238 = True.
Proof. exact (EQ_MP (@lem5167779) (@lem5167777)). Qed.
Lemma lem5167781 : term232 = True.
Proof. exact (TRANS (@lem5167776) (@lem5167780)). Qed.
Lemma lem5167782 : term241 = True.
Proof. exact (TRANS (@lem5167773) (@lem5167781)). Qed.
Lemma lem5167783 : term235 = True.
Proof. exact (TRANS (@lem5167759) (@lem5167782)). Qed.
Lemma lem5167784 : term232 = True.
Proof. exact (TRANS (@lem5167736) (@lem5167783)). Qed.
Lemma lem5167785 : term231 = True.
Proof. exact (TRANS (@lem5167727) (@lem5167784)). Qed.
Lemma lem5167786 : True = term231.
Proof. exact (SYM (@lem5167785)). Qed.
Lemma lem5167787 : term231.
Proof. exact (EQ_MP (@lem5167786) (@lem0)). Qed.
Lemma lem5167788 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term245 e l x.
Proof. exact (conj (@lem5167787) (@lem5167723 e l x h1)). Qed.
Lemma lem5167790 (x : real) (y : real) : term246 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5167791 (e : real) (l : real) (x : real) : term247 e l x.
Proof. exact (@lem5167790 term91 (term108 e l x)). Qed.
Lemma lem5167792 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term248 e l x.
Proof. exact (@lem5167791 e l x (@lem5167788 e l x h1)). Qed.
Lemma lem5167793 (e : real) (l : real) (x : real) : (term249 e l x) = (term108 e l x).
Proof. exact (@lem1982733 (term108 e l x)). Qed.
Lemma lem5167794 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5167795 (e : real) (l : real) (x : real) : (term250 e l x) = (term110 e l x).
Proof. exact (MK_COMB (@lem5167794) (@lem5167793 e l x)). Qed.
Lemma lem5167796 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5167797 (e : real) (l : real) (x : real) : (term248 e l x) = (term111 e l x).
Proof. exact (MK_COMB (@lem5167795 e l x) (@lem5167796)). Qed.
Lemma lem5167798 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term111 e l x.
Proof. exact (EQ_MP (@lem5167797 e l x) (@lem5167792 e l x h1)). Qed.
Lemma lem5167800 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5167801 : term231 = term232.
Proof. exact (@lem5167800 term32 term91). Qed.
Lemma lem5167803 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5167804 : term91 = term101.
Proof. exact (@lem5167803 term85). Qed.
Lemma lem5167806 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5167807 : term32 = term172.
Proof. exact (@lem5167806 (NUMERAL 0)). Qed.
Lemma lem5167808 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5167809 : term233 = term234.
Proof. exact (MK_COMB (@lem5167808) (@lem5167807)). Qed.
Lemma lem5167810 : term232 = term235.
Proof. exact (MK_COMB (@lem5167809) (@lem5167804)). Qed.
Lemma lem5167811 : term236.
Proof. exact (@lem1980255 term32 term91 term91 term91). Qed.
Lemma lem5167813 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5167814 : term232 = term238.
Proof. exact (@lem5167813 (NUMERAL 0) term85). Qed.
Lemma lem5167815 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5167816 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5167817 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5167816 h1) (fun h1 : term238 = True => @lem5167815)). Qed.
Lemma lem5167818 : term238 = True.
Proof. exact (EQ_MP (@lem5167817) (@lem5167815)). Qed.
Lemma lem5167819 : term232 = True.
Proof. exact (TRANS (@lem5167814) (@lem5167818)). Qed.
Lemma lem5167820 : True = term232.
Proof. exact (SYM (@lem5167819)). Qed.
Lemma lem5167821 : term232.
Proof. exact (EQ_MP (@lem5167820) (@lem0)). Qed.
Lemma lem5167822 : term240.
Proof. exact (@lem5167811 (@lem5167821)). Qed.
Lemma lem5167824 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5167825 : term232 = term238.
Proof. exact (@lem5167824 (NUMERAL 0) term85). Qed.
Lemma lem5167826 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5167827 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5167828 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5167827 h1) (fun h1 : term238 = True => @lem5167826)). Qed.
Lemma lem5167829 : term238 = True.
Proof. exact (EQ_MP (@lem5167828) (@lem5167826)). Qed.
Lemma lem5167830 : term232 = True.
Proof. exact (TRANS (@lem5167825) (@lem5167829)). Qed.
Lemma lem5167831 : True = term232.
Proof. exact (SYM (@lem5167830)). Qed.
Lemma lem5167832 : term232.
Proof. exact (EQ_MP (@lem5167831) (@lem0)). Qed.
Lemma lem5167833 : term235 = term241.
Proof. exact (@lem5167822 (@lem5167832)). Qed.
Lemma lem5167835 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5167836 : term94 = term95.
Proof. exact (@lem5167835 term85 term85). Qed.
Lemma lem5167837 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167838 : term97 = term85.
Proof. exact (EQ_MP (@lem5167837) (@lem940073)). Qed.
Lemma lem5167839 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167840 : term95 = term91.
Proof. exact (MK_COMB (@lem5167839) (@lem5167838)). Qed.
Lemma lem5167841 : term94 = term91.
Proof. exact (TRANS (@lem5167836) (@lem5167840)). Qed.
Lemma lem5167843 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5167844 : term243 = term32.
Proof. exact (@lem5167843 term85). Qed.
Lemma lem5167845 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5167846 : term244 = term233.
Proof. exact (MK_COMB (@lem5167845) (@lem5167844)). Qed.
Lemma lem5167847 : term241 = term232.
Proof. exact (MK_COMB (@lem5167846) (@lem5167841)). Qed.
Lemma lem5167849 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5167850 : term232 = term238.
Proof. exact (@lem5167849 (NUMERAL 0) term85). Qed.
Lemma lem5167851 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5167852 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5167853 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5167852 h1) (fun h1 : term238 = True => @lem5167851)). Qed.
Lemma lem5167854 : term238 = True.
Proof. exact (EQ_MP (@lem5167853) (@lem5167851)). Qed.
Lemma lem5167855 : term232 = True.
Proof. exact (TRANS (@lem5167850) (@lem5167854)). Qed.
Lemma lem5167856 : term241 = True.
Proof. exact (TRANS (@lem5167847) (@lem5167855)). Qed.
Lemma lem5167857 : term235 = True.
Proof. exact (TRANS (@lem5167833) (@lem5167856)). Qed.
Lemma lem5167858 : term232 = True.
Proof. exact (TRANS (@lem5167810) (@lem5167857)). Qed.
Lemma lem5167859 : term231 = True.
Proof. exact (TRANS (@lem5167801) (@lem5167858)). Qed.
Lemma lem5167860 : True = term231.
Proof. exact (SYM (@lem5167859)). Qed.
Lemma lem5167861 : term231.
Proof. exact (EQ_MP (@lem5167860) (@lem0)). Qed.
Lemma lem5167862 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term251 e l x.
Proof. exact (conj (@lem5167861) (@lem5167721 e l x h1)). Qed.
Lemma lem5167864 (x : real) (y : real) : term252 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5167865 (e : real) (l : real) (x : real) : term253 e l x.
Proof. exact (@lem5167864 term91 (term41 e l x)). Qed.
Lemma lem5167866 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term254 e l x.
Proof. exact (@lem5167865 e l x (@lem5167862 e l x h1)). Qed.
Lemma lem5167867 (e : real) (l : real) (x : real) : (term255 e l x) = (term41 e l x).
Proof. exact (@lem1982733 (term41 e l x)). Qed.
Lemma lem5167868 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5167869 (e : real) (l : real) (x : real) : (term256 e l x) = (term43 e l x).
Proof. exact (MK_COMB (@lem5167868) (@lem5167867 e l x)). Qed.
Lemma lem5167870 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5167871 (e : real) (l : real) (x : real) : (term254 e l x) = (term44 e l x).
Proof. exact (MK_COMB (@lem5167869 e l x) (@lem5167870)). Qed.
Lemma lem5167872 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term44 e l x.
Proof. exact (EQ_MP (@lem5167871 e l x) (@lem5167866 e l x h1)). Qed.
Lemma lem5167873 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term257 e l x.
Proof. exact (conj (@lem5167872 e l x h1) (@lem5167798 e l x h1)). Qed.
Lemma lem5167875 (x : real) (y : real) : term258 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5167876 (e : real) (l : real) (x : real) : term259 e l x.
Proof. exact (@lem5167875 (term41 e l x) (term108 e l x)). Qed.
Lemma lem5167877 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term260 e l x.
Proof. exact (@lem5167876 e l x (@lem5167873 e l x h1)). Qed.
Lemma lem5167878 (e : real) (l : real) (x : real) : (term261 e l x) = (term262 e l x).
Proof. exact (@lem1982753 (term25 e) e (term23 l x) (term24 l x)). Qed.
Lemma lem5167879 (e : real) : (term263 e) = (term264 e).
Proof. exact (@lem1982713 term51 e). Qed.
Lemma lem5167881 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5167882 : term91 = term101.
Proof. exact (@lem5167881 term85). Qed.
Lemma lem5167884 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5167885 : term51 = term84.
Proof. exact (@lem5167884 term85). Qed.
Lemma lem5167886 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5167887 : term265 = term266.
Proof. exact (MK_COMB (@lem5167886) (@lem5167885)). Qed.
Lemma lem5167888 : term267 = term268.
Proof. exact (MK_COMB (@lem5167887) (@lem5167882)). Qed.
Lemma lem5167889 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5167891 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5167892 : term232 = term238.
Proof. exact (@lem5167891 (NUMERAL 0) term85). Qed.
Lemma lem5167893 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5167894 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5167895 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5167894 h1) (fun h1 : term238 = True => @lem5167893)). Qed.
Lemma lem5167896 : term238 = True.
Proof. exact (EQ_MP (@lem5167895) (@lem5167893)). Qed.
Lemma lem5167897 : term232 = True.
Proof. exact (TRANS (@lem5167892) (@lem5167896)). Qed.
Lemma lem5167898 : True = term232.
Proof. exact (SYM (@lem5167897)). Qed.
Lemma lem5167899 : term232.
Proof. exact (EQ_MP (@lem5167898) (@lem0)). Qed.
Lemma lem5167900 : term270.
Proof. exact (@lem5167889 (@lem5167899)). Qed.
Lemma lem5167902 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5167903 : term232 = term238.
Proof. exact (@lem5167902 (NUMERAL 0) term85). Qed.
Lemma lem5167904 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5167905 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5167906 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5167905 h1) (fun h1 : term238 = True => @lem5167904)). Qed.
Lemma lem5167907 : term238 = True.
Proof. exact (EQ_MP (@lem5167906) (@lem5167904)). Qed.
Lemma lem5167908 : term232 = True.
Proof. exact (TRANS (@lem5167903) (@lem5167907)). Qed.
Lemma lem5167909 : True = term232.
Proof. exact (SYM (@lem5167908)). Qed.
Lemma lem5167910 : term232.
Proof. exact (EQ_MP (@lem5167909) (@lem0)). Qed.
Lemma lem5167911 : term271.
Proof. exact (@lem5167900 (@lem5167910)). Qed.
Lemma lem5167913 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5167914 : term232 = term238.
Proof. exact (@lem5167913 (NUMERAL 0) term85). Qed.
Lemma lem5167915 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5167916 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5167917 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5167916 h1) (fun h1 : term238 = True => @lem5167915)). Qed.
Lemma lem5167918 : term238 = True.
Proof. exact (EQ_MP (@lem5167917) (@lem5167915)). Qed.
Lemma lem5167919 : term232 = True.
Proof. exact (TRANS (@lem5167914) (@lem5167918)). Qed.
Lemma lem5167920 : True = term232.
Proof. exact (SYM (@lem5167919)). Qed.
Lemma lem5167921 : term232.
Proof. exact (EQ_MP (@lem5167920) (@lem0)). Qed.
Lemma lem5167922 : term272.
Proof. exact (@lem5167911 (@lem5167921)). Qed.
Lemma lem5167924 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5167925 : term94 = term95.
Proof. exact (@lem5167924 term85 term85). Qed.
Lemma lem5167926 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167927 : term97 = term85.
Proof. exact (EQ_MP (@lem5167926) (@lem940073)). Qed.
Lemma lem5167928 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167929 : term95 = term91.
Proof. exact (MK_COMB (@lem5167928) (@lem5167927)). Qed.
Lemma lem5167930 : term94 = term91.
Proof. exact (TRANS (@lem5167925) (@lem5167929)). Qed.
Lemma lem5167932 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5167933 : term275 = term276.
Proof. exact (@lem5167932 term85 term85). Qed.
Lemma lem5167934 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167935 : term97 = term85.
Proof. exact (EQ_MP (@lem5167934) (@lem940073)). Qed.
Lemma lem5167936 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167937 : term95 = term91.
Proof. exact (MK_COMB (@lem5167936) (@lem5167935)). Qed.
Lemma lem5167938 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5167939 : term276 = term51.
Proof. exact (MK_COMB (@lem5167938) (@lem5167937)). Qed.
Lemma lem5167940 : term275 = term51.
Proof. exact (TRANS (@lem5167933) (@lem5167939)). Qed.
Lemma lem5167941 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5167942 : term277 = term265.
Proof. exact (MK_COMB (@lem5167941) (@lem5167940)). Qed.
Lemma lem5167943 : term278 = term267.
Proof. exact (MK_COMB (@lem5167942) (@lem5167930)). Qed.
Lemma lem5167945 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5167946 : term267 = term32.
Proof. exact (@lem5167945 term85). Qed.
Lemma lem5167947 : term278 = term32.
Proof. exact (TRANS (@lem5167943) (@lem5167946)). Qed.
Lemma lem5167948 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5167949 : term280 = term281.
Proof. exact (MK_COMB (@lem5167948) (@lem5167947)). Qed.
Lemma lem5167950 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5167951 : term282 = term243.
Proof. exact (MK_COMB (@lem5167949) (@lem5167950)). Qed.
Lemma lem5167953 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5167954 : term243 = term32.
Proof. exact (@lem5167953 term85). Qed.
Lemma lem5167955 : term282 = term32.
Proof. exact (TRANS (@lem5167951) (@lem5167954)). Qed.
Lemma lem5167957 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5167958 : term94 = term95.
Proof. exact (@lem5167957 term85 term85). Qed.
Lemma lem5167959 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5167960 : term97 = term85.
Proof. exact (EQ_MP (@lem5167959) (@lem940073)). Qed.
Lemma lem5167961 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5167962 : term95 = term91.
Proof. exact (MK_COMB (@lem5167961) (@lem5167960)). Qed.
Lemma lem5167963 : term94 = term91.
Proof. exact (TRANS (@lem5167958) (@lem5167962)). Qed.
Lemma lem5167964 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5167965 : term283 = term243.
Proof. exact (MK_COMB (@lem5167964) (@lem5167963)). Qed.
Lemma lem5167967 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5167968 : term243 = term32.
Proof. exact (@lem5167967 term85). Qed.
Lemma lem5167969 : term283 = term32.
Proof. exact (TRANS (@lem5167965) (@lem5167968)). Qed.
Lemma lem5167970 : term32 = term283.
Proof. exact (SYM (@lem5167969)). Qed.
Lemma lem5167971 : term282 = term283.
Proof. exact (TRANS (@lem5167955) (@lem5167970)). Qed.
Lemma lem5167972 : term268 = term172.
Proof. exact (@lem5167922 (@lem5167971)). Qed.
Lemma lem5167973 : term267 = term172.
Proof. exact (TRANS (@lem5167888) (@lem5167972)). Qed.
Lemma lem5167975 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5167976 : term172 = term32.
Proof. exact (@lem5167975 term32). Qed.
Lemma lem5167977 : term267 = term32.
Proof. exact (TRANS (@lem5167973) (@lem5167976)). Qed.
Lemma lem5167978 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5167979 : term284 = term281.
Proof. exact (MK_COMB (@lem5167978) (@lem5167977)). Qed.
Lemma lem5167980 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem5167981 (e : real) : (term264 e) = (term285 e).
Proof. exact (MK_COMB (@lem5167979) (@lem5167980 e)). Qed.
Lemma lem5167982 (e : real) : (term263 e) = (term285 e).
Proof. exact (TRANS (@lem5167879 e) (@lem5167981 e)). Qed.
Lemma lem5167983 (e : real) : (term285 e) = term32.
Proof. exact (@lem1982719 e). Qed.
Lemma lem5167984 (e : real) : (term263 e) = term32.
Proof. exact (TRANS (@lem5167982 e) (@lem5167983 e)). Qed.
Lemma lem5167985 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5167986 (e : real) : (term286 e) = term206.
Proof. exact (MK_COMB (@lem5167985) (@lem5167984 e)). Qed.
Lemma lem5167987 (l : real) (x : real) : (term287 l x) = (term288 l x).
Proof. exact (@lem1982753 l (term25 l) (term25 x) x). Qed.
Lemma lem5167988 (l : real) : (term289 l) = (term264 l).
Proof. exact (@lem1982715 term51 l). Qed.
Lemma lem5167990 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5167991 : term91 = term101.
Proof. exact (@lem5167990 term85). Qed.
Lemma lem5167993 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5167994 : term51 = term84.
Proof. exact (@lem5167993 term85). Qed.
Lemma lem5167995 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5167996 : term265 = term266.
Proof. exact (MK_COMB (@lem5167995) (@lem5167994)). Qed.
Lemma lem5167997 : term267 = term268.
Proof. exact (MK_COMB (@lem5167996) (@lem5167991)). Qed.
Lemma lem5167998 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5168000 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168001 : term232 = term238.
Proof. exact (@lem5168000 (NUMERAL 0) term85). Qed.
Lemma lem5168002 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168003 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168004 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168003 h1) (fun h1 : term238 = True => @lem5168002)). Qed.
Lemma lem5168005 : term238 = True.
Proof. exact (EQ_MP (@lem5168004) (@lem5168002)). Qed.
Lemma lem5168006 : term232 = True.
Proof. exact (TRANS (@lem5168001) (@lem5168005)). Qed.
Lemma lem5168007 : True = term232.
Proof. exact (SYM (@lem5168006)). Qed.
Lemma lem5168008 : term232.
Proof. exact (EQ_MP (@lem5168007) (@lem0)). Qed.
Lemma lem5168009 : term270.
Proof. exact (@lem5167998 (@lem5168008)). Qed.
Lemma lem5168011 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168012 : term232 = term238.
Proof. exact (@lem5168011 (NUMERAL 0) term85). Qed.
Lemma lem5168013 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168014 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168015 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168014 h1) (fun h1 : term238 = True => @lem5168013)). Qed.
Lemma lem5168016 : term238 = True.
Proof. exact (EQ_MP (@lem5168015) (@lem5168013)). Qed.
Lemma lem5168017 : term232 = True.
Proof. exact (TRANS (@lem5168012) (@lem5168016)). Qed.
Lemma lem5168018 : True = term232.
Proof. exact (SYM (@lem5168017)). Qed.
Lemma lem5168019 : term232.
Proof. exact (EQ_MP (@lem5168018) (@lem0)). Qed.
Lemma lem5168020 : term271.
Proof. exact (@lem5168009 (@lem5168019)). Qed.
Lemma lem5168022 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168023 : term232 = term238.
Proof. exact (@lem5168022 (NUMERAL 0) term85). Qed.
Lemma lem5168024 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168025 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168026 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168025 h1) (fun h1 : term238 = True => @lem5168024)). Qed.
Lemma lem5168027 : term238 = True.
Proof. exact (EQ_MP (@lem5168026) (@lem5168024)). Qed.
Lemma lem5168028 : term232 = True.
Proof. exact (TRANS (@lem5168023) (@lem5168027)). Qed.
Lemma lem5168029 : True = term232.
Proof. exact (SYM (@lem5168028)). Qed.
Lemma lem5168030 : term232.
Proof. exact (EQ_MP (@lem5168029) (@lem0)). Qed.
Lemma lem5168031 : term272.
Proof. exact (@lem5168020 (@lem5168030)). Qed.
Lemma lem5168033 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5168034 : term94 = term95.
Proof. exact (@lem5168033 term85 term85). Qed.
Lemma lem5168035 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168036 : term97 = term85.
Proof. exact (EQ_MP (@lem5168035) (@lem940073)). Qed.
Lemma lem5168037 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168038 : term95 = term91.
Proof. exact (MK_COMB (@lem5168037) (@lem5168036)). Qed.
Lemma lem5168039 : term94 = term91.
Proof. exact (TRANS (@lem5168034) (@lem5168038)). Qed.
Lemma lem5168041 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5168042 : term275 = term276.
Proof. exact (@lem5168041 term85 term85). Qed.
Lemma lem5168043 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168044 : term97 = term85.
Proof. exact (EQ_MP (@lem5168043) (@lem940073)). Qed.
Lemma lem5168045 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168046 : term95 = term91.
Proof. exact (MK_COMB (@lem5168045) (@lem5168044)). Qed.
Lemma lem5168047 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5168048 : term276 = term51.
Proof. exact (MK_COMB (@lem5168047) (@lem5168046)). Qed.
Lemma lem5168049 : term275 = term51.
Proof. exact (TRANS (@lem5168042) (@lem5168048)). Qed.
Lemma lem5168050 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5168051 : term277 = term265.
Proof. exact (MK_COMB (@lem5168050) (@lem5168049)). Qed.
Lemma lem5168052 : term278 = term267.
Proof. exact (MK_COMB (@lem5168051) (@lem5168039)). Qed.
Lemma lem5168054 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5168055 : term267 = term32.
Proof. exact (@lem5168054 term85). Qed.
Lemma lem5168056 : term278 = term32.
Proof. exact (TRANS (@lem5168052) (@lem5168055)). Qed.
Lemma lem5168057 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5168058 : term280 = term281.
Proof. exact (MK_COMB (@lem5168057) (@lem5168056)). Qed.
Lemma lem5168059 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5168060 : term282 = term243.
Proof. exact (MK_COMB (@lem5168058) (@lem5168059)). Qed.
Lemma lem5168062 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168063 : term243 = term32.
Proof. exact (@lem5168062 term85). Qed.
Lemma lem5168064 : term282 = term32.
Proof. exact (TRANS (@lem5168060) (@lem5168063)). Qed.
Lemma lem5168066 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5168067 : term94 = term95.
Proof. exact (@lem5168066 term85 term85). Qed.
Lemma lem5168068 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168069 : term97 = term85.
Proof. exact (EQ_MP (@lem5168068) (@lem940073)). Qed.
Lemma lem5168070 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168071 : term95 = term91.
Proof. exact (MK_COMB (@lem5168070) (@lem5168069)). Qed.
Lemma lem5168072 : term94 = term91.
Proof. exact (TRANS (@lem5168067) (@lem5168071)). Qed.
Lemma lem5168073 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5168074 : term283 = term243.
Proof. exact (MK_COMB (@lem5168073) (@lem5168072)). Qed.
Lemma lem5168076 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168077 : term243 = term32.
Proof. exact (@lem5168076 term85). Qed.
Lemma lem5168078 : term283 = term32.
Proof. exact (TRANS (@lem5168074) (@lem5168077)). Qed.
Lemma lem5168079 : term32 = term283.
Proof. exact (SYM (@lem5168078)). Qed.
Lemma lem5168080 : term282 = term283.
Proof. exact (TRANS (@lem5168064) (@lem5168079)). Qed.
Lemma lem5168081 : term268 = term172.
Proof. exact (@lem5168031 (@lem5168080)). Qed.
Lemma lem5168082 : term267 = term172.
Proof. exact (TRANS (@lem5167997) (@lem5168081)). Qed.
Lemma lem5168084 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5168085 : term172 = term32.
Proof. exact (@lem5168084 term32). Qed.
Lemma lem5168086 : term267 = term32.
Proof. exact (TRANS (@lem5168082) (@lem5168085)). Qed.
Lemma lem5168087 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5168088 : term284 = term281.
Proof. exact (MK_COMB (@lem5168087) (@lem5168086)). Qed.
Lemma lem5168089 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5168090 (l : real) : (term264 l) = (term285 l).
Proof. exact (MK_COMB (@lem5168088) (@lem5168089 l)). Qed.
Lemma lem5168091 (l : real) : (term289 l) = (term285 l).
Proof. exact (TRANS (@lem5167988 l) (@lem5168090 l)). Qed.
Lemma lem5168092 (l : real) : (term285 l) = term32.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5168093 (l : real) : (term289 l) = term32.
Proof. exact (TRANS (@lem5168091 l) (@lem5168092 l)). Qed.
Lemma lem5168094 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5168095 (l : real) : (term290 l) = term206.
Proof. exact (MK_COMB (@lem5168094) (@lem5168093 l)). Qed.
Lemma lem5168096 (x : real) : (term263 x) = (term264 x).
Proof. exact (@lem1982713 term51 x). Qed.
Lemma lem5168098 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168099 : term91 = term101.
Proof. exact (@lem5168098 term85). Qed.
Lemma lem5168101 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5168102 : term51 = term84.
Proof. exact (@lem5168101 term85). Qed.
Lemma lem5168103 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5168104 : term265 = term266.
Proof. exact (MK_COMB (@lem5168103) (@lem5168102)). Qed.
Lemma lem5168105 : term267 = term268.
Proof. exact (MK_COMB (@lem5168104) (@lem5168099)). Qed.
Lemma lem5168106 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5168108 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168109 : term232 = term238.
Proof. exact (@lem5168108 (NUMERAL 0) term85). Qed.
Lemma lem5168110 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168111 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168112 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168111 h1) (fun h1 : term238 = True => @lem5168110)). Qed.
Lemma lem5168113 : term238 = True.
Proof. exact (EQ_MP (@lem5168112) (@lem5168110)). Qed.
Lemma lem5168114 : term232 = True.
Proof. exact (TRANS (@lem5168109) (@lem5168113)). Qed.
Lemma lem5168115 : True = term232.
Proof. exact (SYM (@lem5168114)). Qed.
Lemma lem5168116 : term232.
Proof. exact (EQ_MP (@lem5168115) (@lem0)). Qed.
Lemma lem5168117 : term270.
Proof. exact (@lem5168106 (@lem5168116)). Qed.
Lemma lem5168119 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168120 : term232 = term238.
Proof. exact (@lem5168119 (NUMERAL 0) term85). Qed.
Lemma lem5168121 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168122 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168123 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168122 h1) (fun h1 : term238 = True => @lem5168121)). Qed.
Lemma lem5168124 : term238 = True.
Proof. exact (EQ_MP (@lem5168123) (@lem5168121)). Qed.
Lemma lem5168125 : term232 = True.
Proof. exact (TRANS (@lem5168120) (@lem5168124)). Qed.
Lemma lem5168126 : True = term232.
Proof. exact (SYM (@lem5168125)). Qed.
Lemma lem5168127 : term232.
Proof. exact (EQ_MP (@lem5168126) (@lem0)). Qed.
Lemma lem5168128 : term271.
Proof. exact (@lem5168117 (@lem5168127)). Qed.
Lemma lem5168130 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168131 : term232 = term238.
Proof. exact (@lem5168130 (NUMERAL 0) term85). Qed.
Lemma lem5168132 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168133 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168134 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168133 h1) (fun h1 : term238 = True => @lem5168132)). Qed.
Lemma lem5168135 : term238 = True.
Proof. exact (EQ_MP (@lem5168134) (@lem5168132)). Qed.
Lemma lem5168136 : term232 = True.
Proof. exact (TRANS (@lem5168131) (@lem5168135)). Qed.
Lemma lem5168137 : True = term232.
Proof. exact (SYM (@lem5168136)). Qed.
Lemma lem5168138 : term232.
Proof. exact (EQ_MP (@lem5168137) (@lem0)). Qed.
Lemma lem5168139 : term272.
Proof. exact (@lem5168128 (@lem5168138)). Qed.
Lemma lem5168141 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5168142 : term94 = term95.
Proof. exact (@lem5168141 term85 term85). Qed.
Lemma lem5168143 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168144 : term97 = term85.
Proof. exact (EQ_MP (@lem5168143) (@lem940073)). Qed.
Lemma lem5168145 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168146 : term95 = term91.
Proof. exact (MK_COMB (@lem5168145) (@lem5168144)). Qed.
Lemma lem5168147 : term94 = term91.
Proof. exact (TRANS (@lem5168142) (@lem5168146)). Qed.
Lemma lem5168149 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5168150 : term275 = term276.
Proof. exact (@lem5168149 term85 term85). Qed.
Lemma lem5168151 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168152 : term97 = term85.
Proof. exact (EQ_MP (@lem5168151) (@lem940073)). Qed.
Lemma lem5168153 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168154 : term95 = term91.
Proof. exact (MK_COMB (@lem5168153) (@lem5168152)). Qed.
Lemma lem5168155 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5168156 : term276 = term51.
Proof. exact (MK_COMB (@lem5168155) (@lem5168154)). Qed.
Lemma lem5168157 : term275 = term51.
Proof. exact (TRANS (@lem5168150) (@lem5168156)). Qed.
Lemma lem5168158 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5168159 : term277 = term265.
Proof. exact (MK_COMB (@lem5168158) (@lem5168157)). Qed.
Lemma lem5168160 : term278 = term267.
Proof. exact (MK_COMB (@lem5168159) (@lem5168147)). Qed.
Lemma lem5168162 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5168163 : term267 = term32.
Proof. exact (@lem5168162 term85). Qed.
Lemma lem5168164 : term278 = term32.
Proof. exact (TRANS (@lem5168160) (@lem5168163)). Qed.
Lemma lem5168165 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5168166 : term280 = term281.
Proof. exact (MK_COMB (@lem5168165) (@lem5168164)). Qed.
Lemma lem5168167 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5168168 : term282 = term243.
Proof. exact (MK_COMB (@lem5168166) (@lem5168167)). Qed.
Lemma lem5168170 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168171 : term243 = term32.
Proof. exact (@lem5168170 term85). Qed.
Lemma lem5168172 : term282 = term32.
Proof. exact (TRANS (@lem5168168) (@lem5168171)). Qed.
Lemma lem5168174 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5168175 : term94 = term95.
Proof. exact (@lem5168174 term85 term85). Qed.
Lemma lem5168176 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168177 : term97 = term85.
Proof. exact (EQ_MP (@lem5168176) (@lem940073)). Qed.
Lemma lem5168178 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168179 : term95 = term91.
Proof. exact (MK_COMB (@lem5168178) (@lem5168177)). Qed.
Lemma lem5168180 : term94 = term91.
Proof. exact (TRANS (@lem5168175) (@lem5168179)). Qed.
Lemma lem5168181 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5168182 : term283 = term243.
Proof. exact (MK_COMB (@lem5168181) (@lem5168180)). Qed.
Lemma lem5168184 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168185 : term243 = term32.
Proof. exact (@lem5168184 term85). Qed.
Lemma lem5168186 : term283 = term32.
Proof. exact (TRANS (@lem5168182) (@lem5168185)). Qed.
Lemma lem5168187 : term32 = term283.
Proof. exact (SYM (@lem5168186)). Qed.
Lemma lem5168188 : term282 = term283.
Proof. exact (TRANS (@lem5168172) (@lem5168187)). Qed.
Lemma lem5168189 : term268 = term172.
Proof. exact (@lem5168139 (@lem5168188)). Qed.
Lemma lem5168190 : term267 = term172.
Proof. exact (TRANS (@lem5168105) (@lem5168189)). Qed.
Lemma lem5168192 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5168193 : term172 = term32.
Proof. exact (@lem5168192 term32). Qed.
Lemma lem5168194 : term267 = term32.
Proof. exact (TRANS (@lem5168190) (@lem5168193)). Qed.
Lemma lem5168195 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5168196 : term284 = term281.
Proof. exact (MK_COMB (@lem5168195) (@lem5168194)). Qed.
Lemma lem5168197 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5168198 (x : real) : (term264 x) = (term285 x).
Proof. exact (MK_COMB (@lem5168196) (@lem5168197 x)). Qed.
Lemma lem5168199 (x : real) : (term263 x) = (term285 x).
Proof. exact (TRANS (@lem5168096 x) (@lem5168198 x)). Qed.
Lemma lem5168200 (x : real) : (term285 x) = term32.
Proof. exact (@lem1982719 x). Qed.
Lemma lem5168201 (x : real) : (term263 x) = term32.
Proof. exact (TRANS (@lem5168199 x) (@lem5168200 x)). Qed.
Lemma lem5168202 (l : real) (x : real) : (term288 l x) = term291.
Proof. exact (MK_COMB (@lem5168095 l) (@lem5168201 x)). Qed.
Lemma lem5168203 (l : real) (x : real) : (term287 l x) = term291.
Proof. exact (TRANS (@lem5167987 l x) (@lem5168202 l x)). Qed.
Lemma lem5168204 : term291 = term32.
Proof. exact (@lem1982721 term32). Qed.
Lemma lem5168205 (l : real) (x : real) : (term287 l x) = term32.
Proof. exact (TRANS (@lem5168203 l x) (@lem5168204)). Qed.
Lemma lem5168206 (e : real) (l : real) (x : real) : (term262 e l x) = term291.
Proof. exact (MK_COMB (@lem5167986 e) (@lem5168205 l x)). Qed.
Lemma lem5168207 (e : real) (l : real) (x : real) : (term261 e l x) = term291.
Proof. exact (TRANS (@lem5167878 e l x) (@lem5168206 e l x)). Qed.
Lemma lem5168208 : term291 = term32.
Proof. exact (@lem1982721 term32). Qed.
Lemma lem5168209 (e : real) (l : real) (x : real) : (term261 e l x) = term32.
Proof. exact (TRANS (@lem5168207 e l x) (@lem5168208)). Qed.
Lemma lem5168210 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5168211 (e : real) (l : real) (x : real) : (term292 e l x) = term293.
Proof. exact (MK_COMB (@lem5168210) (@lem5168209 e l x)). Qed.
Lemma lem5168212 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5168213 (e : real) (l : real) (x : real) : (term260 e l x) = term294.
Proof. exact (MK_COMB (@lem5168211 e l x) (@lem5168212)). Qed.
Lemma lem5168214 (e : real) (l : real) (x : real) (h1 : term144 e l x) : term294.
Proof. exact (EQ_MP (@lem5168213 e l x) (@lem5167877 e l x h1)). Qed.
Lemma lem5168216 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5168217 : term294 = term295.
Proof. exact (@lem5168216 term32 term32). Qed.
Lemma lem5168219 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168220 : term32 = term172.
Proof. exact (@lem5168219 (NUMERAL 0)). Qed.
Lemma lem5168222 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168223 : term32 = term172.
Proof. exact (@lem5168222 (NUMERAL 0)). Qed.
Lemma lem5168224 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5168225 : term233 = term234.
Proof. exact (MK_COMB (@lem5168224) (@lem5168223)). Qed.
Lemma lem5168226 : term295 = term296.
Proof. exact (MK_COMB (@lem5168225) (@lem5168220)). Qed.
Lemma lem5168227 : term297.
Proof. exact (@lem1980255 term32 term91 term32 term91). Qed.
Lemma lem5168229 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168230 : term232 = term238.
Proof. exact (@lem5168229 (NUMERAL 0) term85). Qed.
Lemma lem5168231 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168232 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168233 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168232 h1) (fun h1 : term238 = True => @lem5168231)). Qed.
Lemma lem5168234 : term238 = True.
Proof. exact (EQ_MP (@lem5168233) (@lem5168231)). Qed.
Lemma lem5168235 : term232 = True.
Proof. exact (TRANS (@lem5168230) (@lem5168234)). Qed.
Lemma lem5168236 : True = term232.
Proof. exact (SYM (@lem5168235)). Qed.
Lemma lem5168237 : term232.
Proof. exact (EQ_MP (@lem5168236) (@lem0)). Qed.
Lemma lem5168238 : term298.
Proof. exact (@lem5168227 (@lem5168237)). Qed.
Lemma lem5168240 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168241 : term232 = term238.
Proof. exact (@lem5168240 (NUMERAL 0) term85). Qed.
Lemma lem5168242 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168243 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168244 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168243 h1) (fun h1 : term238 = True => @lem5168242)). Qed.
Lemma lem5168245 : term238 = True.
Proof. exact (EQ_MP (@lem5168244) (@lem5168242)). Qed.
Lemma lem5168246 : term232 = True.
Proof. exact (TRANS (@lem5168241) (@lem5168245)). Qed.
Lemma lem5168247 : True = term232.
Proof. exact (SYM (@lem5168246)). Qed.
Lemma lem5168248 : term232.
Proof. exact (EQ_MP (@lem5168247) (@lem0)). Qed.
Lemma lem5168249 : term296 = term299.
Proof. exact (@lem5168238 (@lem5168248)). Qed.
Lemma lem5168251 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168252 : term243 = term32.
Proof. exact (@lem5168251 term85). Qed.
Lemma lem5168254 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168255 : term243 = term32.
Proof. exact (@lem5168254 term85). Qed.
Lemma lem5168256 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5168257 : term244 = term233.
Proof. exact (MK_COMB (@lem5168256) (@lem5168255)). Qed.
Lemma lem5168258 : term299 = term295.
Proof. exact (MK_COMB (@lem5168257) (@lem5168252)). Qed.
Lemma lem5168260 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168261 : term295 = term300.
Proof. exact (@lem5168260 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5168262 : term300 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5168263 : term295 = False.
Proof. exact (TRANS (@lem5168261) (@lem5168262)). Qed.
Lemma lem5168264 : term299 = False.
Proof. exact (TRANS (@lem5168258) (@lem5168263)). Qed.
Lemma lem5168265 : term296 = False.
Proof. exact (TRANS (@lem5168249) (@lem5168264)). Qed.
Lemma lem5168266 : term295 = False.
Proof. exact (TRANS (@lem5168226) (@lem5168265)). Qed.
Lemma lem5168267 : term294 = False.
Proof. exact (TRANS (@lem5168217) (@lem5168266)). Qed.
Lemma lem5168268 (e : real) (l : real) (x : real) (h1 : term144 e l x) : False.
Proof. exact (EQ_MP (@lem5168267) (@lem5168214 e l x h1)). Qed.
Lemma lem5168269 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term146 e l x.
Proof. exact (h1). Qed.
Lemma lem5168270 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term57 e l x.
Proof. exact (proj2 (@lem5168269 e l x h1)). Qed.
Lemma lem5168271 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term141 e l x.
Proof. exact (proj1 (@lem5168269 e l x h1)). Qed.
Lemma lem5168273 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term118 e l x.
Proof. exact (proj1 (@lem5168271 e l x h1)). Qed.
Lemma lem5168275 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5168276 : term231 = term232.
Proof. exact (@lem5168275 term32 term91). Qed.
Lemma lem5168278 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168279 : term91 = term101.
Proof. exact (@lem5168278 term85). Qed.
Lemma lem5168281 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168282 : term32 = term172.
Proof. exact (@lem5168281 (NUMERAL 0)). Qed.
Lemma lem5168283 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5168284 : term233 = term234.
Proof. exact (MK_COMB (@lem5168283) (@lem5168282)). Qed.
Lemma lem5168285 : term232 = term235.
Proof. exact (MK_COMB (@lem5168284) (@lem5168279)). Qed.
Lemma lem5168286 : term236.
Proof. exact (@lem1980255 term32 term91 term91 term91). Qed.
Lemma lem5168288 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168289 : term232 = term238.
Proof. exact (@lem5168288 (NUMERAL 0) term85). Qed.
Lemma lem5168290 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168291 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168292 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168291 h1) (fun h1 : term238 = True => @lem5168290)). Qed.
Lemma lem5168293 : term238 = True.
Proof. exact (EQ_MP (@lem5168292) (@lem5168290)). Qed.
Lemma lem5168294 : term232 = True.
Proof. exact (TRANS (@lem5168289) (@lem5168293)). Qed.
Lemma lem5168295 : True = term232.
Proof. exact (SYM (@lem5168294)). Qed.
Lemma lem5168296 : term232.
Proof. exact (EQ_MP (@lem5168295) (@lem0)). Qed.
Lemma lem5168297 : term240.
Proof. exact (@lem5168286 (@lem5168296)). Qed.
Lemma lem5168299 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168300 : term232 = term238.
Proof. exact (@lem5168299 (NUMERAL 0) term85). Qed.
Lemma lem5168301 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168302 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168303 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168302 h1) (fun h1 : term238 = True => @lem5168301)). Qed.
Lemma lem5168304 : term238 = True.
Proof. exact (EQ_MP (@lem5168303) (@lem5168301)). Qed.
Lemma lem5168305 : term232 = True.
Proof. exact (TRANS (@lem5168300) (@lem5168304)). Qed.
Lemma lem5168306 : True = term232.
Proof. exact (SYM (@lem5168305)). Qed.
Lemma lem5168307 : term232.
Proof. exact (EQ_MP (@lem5168306) (@lem0)). Qed.
Lemma lem5168308 : term235 = term241.
Proof. exact (@lem5168297 (@lem5168307)). Qed.
Lemma lem5168310 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5168311 : term94 = term95.
Proof. exact (@lem5168310 term85 term85). Qed.
Lemma lem5168312 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168313 : term97 = term85.
Proof. exact (EQ_MP (@lem5168312) (@lem940073)). Qed.
Lemma lem5168314 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168315 : term95 = term91.
Proof. exact (MK_COMB (@lem5168314) (@lem5168313)). Qed.
Lemma lem5168316 : term94 = term91.
Proof. exact (TRANS (@lem5168311) (@lem5168315)). Qed.
Lemma lem5168318 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168319 : term243 = term32.
Proof. exact (@lem5168318 term85). Qed.
Lemma lem5168320 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5168321 : term244 = term233.
Proof. exact (MK_COMB (@lem5168320) (@lem5168319)). Qed.
Lemma lem5168322 : term241 = term232.
Proof. exact (MK_COMB (@lem5168321) (@lem5168316)). Qed.
Lemma lem5168324 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168325 : term232 = term238.
Proof. exact (@lem5168324 (NUMERAL 0) term85). Qed.
Lemma lem5168326 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168327 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168328 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168327 h1) (fun h1 : term238 = True => @lem5168326)). Qed.
Lemma lem5168329 : term238 = True.
Proof. exact (EQ_MP (@lem5168328) (@lem5168326)). Qed.
Lemma lem5168330 : term232 = True.
Proof. exact (TRANS (@lem5168325) (@lem5168329)). Qed.
Lemma lem5168331 : term241 = True.
Proof. exact (TRANS (@lem5168322) (@lem5168330)). Qed.
Lemma lem5168332 : term235 = True.
Proof. exact (TRANS (@lem5168308) (@lem5168331)). Qed.
Lemma lem5168333 : term232 = True.
Proof. exact (TRANS (@lem5168285) (@lem5168332)). Qed.
Lemma lem5168334 : term231 = True.
Proof. exact (TRANS (@lem5168276) (@lem5168333)). Qed.
Lemma lem5168335 : True = term231.
Proof. exact (SYM (@lem5168334)). Qed.
Lemma lem5168336 : term231.
Proof. exact (EQ_MP (@lem5168335) (@lem0)). Qed.
Lemma lem5168337 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term301 e l x.
Proof. exact (conj (@lem5168336) (@lem5168273 e l x h1)). Qed.
Lemma lem5168339 (x : real) (y : real) : term246 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5168340 (e : real) (l : real) (x : real) : term302 e l x.
Proof. exact (@lem5168339 term91 (term107 e l x)). Qed.
Lemma lem5168341 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term303 e l x.
Proof. exact (@lem5168340 e l x (@lem5168337 e l x h1)). Qed.
Lemma lem5168342 (e : real) (l : real) (x : real) : (term304 e l x) = (term107 e l x).
Proof. exact (@lem1982733 (term107 e l x)). Qed.
Lemma lem5168343 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5168344 (e : real) (l : real) (x : real) : (term305 e l x) = (term117 e l x).
Proof. exact (MK_COMB (@lem5168343) (@lem5168342 e l x)). Qed.
Lemma lem5168345 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5168346 (e : real) (l : real) (x : real) : (term303 e l x) = (term118 e l x).
Proof. exact (MK_COMB (@lem5168344 e l x) (@lem5168345)). Qed.
Lemma lem5168347 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term118 e l x.
Proof. exact (EQ_MP (@lem5168346 e l x) (@lem5168341 e l x h1)). Qed.
Lemma lem5168349 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5168350 : term231 = term232.
Proof. exact (@lem5168349 term32 term91). Qed.
Lemma lem5168352 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168353 : term91 = term101.
Proof. exact (@lem5168352 term85). Qed.
Lemma lem5168355 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168356 : term32 = term172.
Proof. exact (@lem5168355 (NUMERAL 0)). Qed.
Lemma lem5168357 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5168358 : term233 = term234.
Proof. exact (MK_COMB (@lem5168357) (@lem5168356)). Qed.
Lemma lem5168359 : term232 = term235.
Proof. exact (MK_COMB (@lem5168358) (@lem5168353)). Qed.
Lemma lem5168360 : term236.
Proof. exact (@lem1980255 term32 term91 term91 term91). Qed.
Lemma lem5168362 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168363 : term232 = term238.
Proof. exact (@lem5168362 (NUMERAL 0) term85). Qed.
Lemma lem5168364 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168365 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168366 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168365 h1) (fun h1 : term238 = True => @lem5168364)). Qed.
Lemma lem5168367 : term238 = True.
Proof. exact (EQ_MP (@lem5168366) (@lem5168364)). Qed.
Lemma lem5168368 : term232 = True.
Proof. exact (TRANS (@lem5168363) (@lem5168367)). Qed.
Lemma lem5168369 : True = term232.
Proof. exact (SYM (@lem5168368)). Qed.
Lemma lem5168370 : term232.
Proof. exact (EQ_MP (@lem5168369) (@lem0)). Qed.
Lemma lem5168371 : term240.
Proof. exact (@lem5168360 (@lem5168370)). Qed.
Lemma lem5168373 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168374 : term232 = term238.
Proof. exact (@lem5168373 (NUMERAL 0) term85). Qed.
Lemma lem5168375 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168376 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168377 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168376 h1) (fun h1 : term238 = True => @lem5168375)). Qed.
Lemma lem5168378 : term238 = True.
Proof. exact (EQ_MP (@lem5168377) (@lem5168375)). Qed.
Lemma lem5168379 : term232 = True.
Proof. exact (TRANS (@lem5168374) (@lem5168378)). Qed.
Lemma lem5168380 : True = term232.
Proof. exact (SYM (@lem5168379)). Qed.
Lemma lem5168381 : term232.
Proof. exact (EQ_MP (@lem5168380) (@lem0)). Qed.
Lemma lem5168382 : term235 = term241.
Proof. exact (@lem5168371 (@lem5168381)). Qed.
Lemma lem5168384 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5168385 : term94 = term95.
Proof. exact (@lem5168384 term85 term85). Qed.
Lemma lem5168386 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168387 : term97 = term85.
Proof. exact (EQ_MP (@lem5168386) (@lem940073)). Qed.
Lemma lem5168388 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168389 : term95 = term91.
Proof. exact (MK_COMB (@lem5168388) (@lem5168387)). Qed.
Lemma lem5168390 : term94 = term91.
Proof. exact (TRANS (@lem5168385) (@lem5168389)). Qed.
Lemma lem5168392 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168393 : term243 = term32.
Proof. exact (@lem5168392 term85). Qed.
Lemma lem5168394 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5168395 : term244 = term233.
Proof. exact (MK_COMB (@lem5168394) (@lem5168393)). Qed.
Lemma lem5168396 : term241 = term232.
Proof. exact (MK_COMB (@lem5168395) (@lem5168390)). Qed.
Lemma lem5168398 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168399 : term232 = term238.
Proof. exact (@lem5168398 (NUMERAL 0) term85). Qed.
Lemma lem5168400 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168401 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168402 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168401 h1) (fun h1 : term238 = True => @lem5168400)). Qed.
Lemma lem5168403 : term238 = True.
Proof. exact (EQ_MP (@lem5168402) (@lem5168400)). Qed.
Lemma lem5168404 : term232 = True.
Proof. exact (TRANS (@lem5168399) (@lem5168403)). Qed.
Lemma lem5168405 : term241 = True.
Proof. exact (TRANS (@lem5168396) (@lem5168404)). Qed.
Lemma lem5168406 : term235 = True.
Proof. exact (TRANS (@lem5168382) (@lem5168405)). Qed.
Lemma lem5168407 : term232 = True.
Proof. exact (TRANS (@lem5168359) (@lem5168406)). Qed.
Lemma lem5168408 : term231 = True.
Proof. exact (TRANS (@lem5168350) (@lem5168407)). Qed.
Lemma lem5168409 : True = term231.
Proof. exact (SYM (@lem5168408)). Qed.
Lemma lem5168410 : term231.
Proof. exact (EQ_MP (@lem5168409) (@lem0)). Qed.
Lemma lem5168411 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term306 e l x.
Proof. exact (conj (@lem5168410) (@lem5168270 e l x h1)). Qed.
Lemma lem5168413 (x : real) (y : real) : term252 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5168414 (e : real) (l : real) (x : real) : term307 e l x.
Proof. exact (@lem5168413 term91 (term54 e l x)). Qed.
Lemma lem5168415 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term308 e l x.
Proof. exact (@lem5168414 e l x (@lem5168411 e l x h1)). Qed.
Lemma lem5168416 (e : real) (l : real) (x : real) : (term309 e l x) = (term54 e l x).
Proof. exact (@lem1982733 (term54 e l x)). Qed.
Lemma lem5168417 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5168418 (e : real) (l : real) (x : real) : (term310 e l x) = (term56 e l x).
Proof. exact (MK_COMB (@lem5168417) (@lem5168416 e l x)). Qed.
Lemma lem5168419 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5168420 (e : real) (l : real) (x : real) : (term308 e l x) = (term57 e l x).
Proof. exact (MK_COMB (@lem5168418 e l x) (@lem5168419)). Qed.
Lemma lem5168421 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term57 e l x.
Proof. exact (EQ_MP (@lem5168420 e l x) (@lem5168415 e l x h1)). Qed.
Lemma lem5168422 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term311 e l x.
Proof. exact (conj (@lem5168421 e l x h1) (@lem5168347 e l x h1)). Qed.
Lemma lem5168424 (x : real) (y : real) : term258 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5168425 (e : real) (l : real) (x : real) : term312 e l x.
Proof. exact (@lem5168424 (term54 e l x) (term107 e l x)). Qed.
Lemma lem5168426 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term313 e l x.
Proof. exact (@lem5168425 e l x (@lem5168422 e l x h1)). Qed.
Lemma lem5168427 (e : real) (l : real) (x : real) : (term314 e l x) = (term315 e l x).
Proof. exact (@lem1982753 (term25 e) e (term24 l x) (term23 l x)). Qed.
Lemma lem5168428 (e : real) : (term263 e) = (term264 e).
Proof. exact (@lem1982713 term51 e). Qed.
Lemma lem5168430 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168431 : term91 = term101.
Proof. exact (@lem5168430 term85). Qed.
Lemma lem5168433 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5168434 : term51 = term84.
Proof. exact (@lem5168433 term85). Qed.
Lemma lem5168435 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5168436 : term265 = term266.
Proof. exact (MK_COMB (@lem5168435) (@lem5168434)). Qed.
Lemma lem5168437 : term267 = term268.
Proof. exact (MK_COMB (@lem5168436) (@lem5168431)). Qed.
Lemma lem5168438 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5168440 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168441 : term232 = term238.
Proof. exact (@lem5168440 (NUMERAL 0) term85). Qed.
Lemma lem5168442 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168443 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168444 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168443 h1) (fun h1 : term238 = True => @lem5168442)). Qed.
Lemma lem5168445 : term238 = True.
Proof. exact (EQ_MP (@lem5168444) (@lem5168442)). Qed.
Lemma lem5168446 : term232 = True.
Proof. exact (TRANS (@lem5168441) (@lem5168445)). Qed.
Lemma lem5168447 : True = term232.
Proof. exact (SYM (@lem5168446)). Qed.
Lemma lem5168448 : term232.
Proof. exact (EQ_MP (@lem5168447) (@lem0)). Qed.
Lemma lem5168449 : term270.
Proof. exact (@lem5168438 (@lem5168448)). Qed.
Lemma lem5168451 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168452 : term232 = term238.
Proof. exact (@lem5168451 (NUMERAL 0) term85). Qed.
Lemma lem5168453 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168454 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168455 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168454 h1) (fun h1 : term238 = True => @lem5168453)). Qed.
Lemma lem5168456 : term238 = True.
Proof. exact (EQ_MP (@lem5168455) (@lem5168453)). Qed.
Lemma lem5168457 : term232 = True.
Proof. exact (TRANS (@lem5168452) (@lem5168456)). Qed.
Lemma lem5168458 : True = term232.
Proof. exact (SYM (@lem5168457)). Qed.
Lemma lem5168459 : term232.
Proof. exact (EQ_MP (@lem5168458) (@lem0)). Qed.
Lemma lem5168460 : term271.
Proof. exact (@lem5168449 (@lem5168459)). Qed.
Lemma lem5168462 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168463 : term232 = term238.
Proof. exact (@lem5168462 (NUMERAL 0) term85). Qed.
Lemma lem5168464 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168465 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168466 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168465 h1) (fun h1 : term238 = True => @lem5168464)). Qed.
Lemma lem5168467 : term238 = True.
Proof. exact (EQ_MP (@lem5168466) (@lem5168464)). Qed.
Lemma lem5168468 : term232 = True.
Proof. exact (TRANS (@lem5168463) (@lem5168467)). Qed.
Lemma lem5168469 : True = term232.
Proof. exact (SYM (@lem5168468)). Qed.
Lemma lem5168470 : term232.
Proof. exact (EQ_MP (@lem5168469) (@lem0)). Qed.
Lemma lem5168471 : term272.
Proof. exact (@lem5168460 (@lem5168470)). Qed.
Lemma lem5168473 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5168474 : term94 = term95.
Proof. exact (@lem5168473 term85 term85). Qed.
Lemma lem5168475 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168476 : term97 = term85.
Proof. exact (EQ_MP (@lem5168475) (@lem940073)). Qed.
Lemma lem5168477 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168478 : term95 = term91.
Proof. exact (MK_COMB (@lem5168477) (@lem5168476)). Qed.
Lemma lem5168479 : term94 = term91.
Proof. exact (TRANS (@lem5168474) (@lem5168478)). Qed.
Lemma lem5168481 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5168482 : term275 = term276.
Proof. exact (@lem5168481 term85 term85). Qed.
Lemma lem5168483 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168484 : term97 = term85.
Proof. exact (EQ_MP (@lem5168483) (@lem940073)). Qed.
Lemma lem5168485 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168486 : term95 = term91.
Proof. exact (MK_COMB (@lem5168485) (@lem5168484)). Qed.
Lemma lem5168487 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5168488 : term276 = term51.
Proof. exact (MK_COMB (@lem5168487) (@lem5168486)). Qed.
Lemma lem5168489 : term275 = term51.
Proof. exact (TRANS (@lem5168482) (@lem5168488)). Qed.
Lemma lem5168490 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5168491 : term277 = term265.
Proof. exact (MK_COMB (@lem5168490) (@lem5168489)). Qed.
Lemma lem5168492 : term278 = term267.
Proof. exact (MK_COMB (@lem5168491) (@lem5168479)). Qed.
Lemma lem5168494 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5168495 : term267 = term32.
Proof. exact (@lem5168494 term85). Qed.
Lemma lem5168496 : term278 = term32.
Proof. exact (TRANS (@lem5168492) (@lem5168495)). Qed.
Lemma lem5168497 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5168498 : term280 = term281.
Proof. exact (MK_COMB (@lem5168497) (@lem5168496)). Qed.
Lemma lem5168499 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5168500 : term282 = term243.
Proof. exact (MK_COMB (@lem5168498) (@lem5168499)). Qed.
Lemma lem5168502 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168503 : term243 = term32.
Proof. exact (@lem5168502 term85). Qed.
Lemma lem5168504 : term282 = term32.
Proof. exact (TRANS (@lem5168500) (@lem5168503)). Qed.
Lemma lem5168506 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5168507 : term94 = term95.
Proof. exact (@lem5168506 term85 term85). Qed.
Lemma lem5168508 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168509 : term97 = term85.
Proof. exact (EQ_MP (@lem5168508) (@lem940073)). Qed.
Lemma lem5168510 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168511 : term95 = term91.
Proof. exact (MK_COMB (@lem5168510) (@lem5168509)). Qed.
Lemma lem5168512 : term94 = term91.
Proof. exact (TRANS (@lem5168507) (@lem5168511)). Qed.
Lemma lem5168513 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5168514 : term283 = term243.
Proof. exact (MK_COMB (@lem5168513) (@lem5168512)). Qed.
Lemma lem5168516 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168517 : term243 = term32.
Proof. exact (@lem5168516 term85). Qed.
Lemma lem5168518 : term283 = term32.
Proof. exact (TRANS (@lem5168514) (@lem5168517)). Qed.
Lemma lem5168519 : term32 = term283.
Proof. exact (SYM (@lem5168518)). Qed.
Lemma lem5168520 : term282 = term283.
Proof. exact (TRANS (@lem5168504) (@lem5168519)). Qed.
Lemma lem5168521 : term268 = term172.
Proof. exact (@lem5168471 (@lem5168520)). Qed.
Lemma lem5168522 : term267 = term172.
Proof. exact (TRANS (@lem5168437) (@lem5168521)). Qed.
Lemma lem5168524 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5168525 : term172 = term32.
Proof. exact (@lem5168524 term32). Qed.
Lemma lem5168526 : term267 = term32.
Proof. exact (TRANS (@lem5168522) (@lem5168525)). Qed.
Lemma lem5168527 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5168528 : term284 = term281.
Proof. exact (MK_COMB (@lem5168527) (@lem5168526)). Qed.
Lemma lem5168529 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem5168530 (e : real) : (term264 e) = (term285 e).
Proof. exact (MK_COMB (@lem5168528) (@lem5168529 e)). Qed.
Lemma lem5168531 (e : real) : (term263 e) = (term285 e).
Proof. exact (TRANS (@lem5168428 e) (@lem5168530 e)). Qed.
Lemma lem5168532 (e : real) : (term285 e) = term32.
Proof. exact (@lem1982719 e). Qed.
Lemma lem5168533 (e : real) : (term263 e) = term32.
Proof. exact (TRANS (@lem5168531 e) (@lem5168532 e)). Qed.
Lemma lem5168534 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5168535 (e : real) : (term286 e) = term206.
Proof. exact (MK_COMB (@lem5168534) (@lem5168533 e)). Qed.
Lemma lem5168536 (l : real) (x : real) : (term316 l x) = (term317 l x).
Proof. exact (@lem1982753 (term25 l) l x (term25 x)). Qed.
Lemma lem5168537 (l : real) : (term263 l) = (term264 l).
Proof. exact (@lem1982713 term51 l). Qed.
Lemma lem5168539 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168540 : term91 = term101.
Proof. exact (@lem5168539 term85). Qed.
Lemma lem5168542 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5168543 : term51 = term84.
Proof. exact (@lem5168542 term85). Qed.
Lemma lem5168544 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5168545 : term265 = term266.
Proof. exact (MK_COMB (@lem5168544) (@lem5168543)). Qed.
Lemma lem5168546 : term267 = term268.
Proof. exact (MK_COMB (@lem5168545) (@lem5168540)). Qed.
Lemma lem5168547 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5168549 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168550 : term232 = term238.
Proof. exact (@lem5168549 (NUMERAL 0) term85). Qed.
Lemma lem5168551 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168552 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168553 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168552 h1) (fun h1 : term238 = True => @lem5168551)). Qed.
Lemma lem5168554 : term238 = True.
Proof. exact (EQ_MP (@lem5168553) (@lem5168551)). Qed.
Lemma lem5168555 : term232 = True.
Proof. exact (TRANS (@lem5168550) (@lem5168554)). Qed.
Lemma lem5168556 : True = term232.
Proof. exact (SYM (@lem5168555)). Qed.
Lemma lem5168557 : term232.
Proof. exact (EQ_MP (@lem5168556) (@lem0)). Qed.
Lemma lem5168558 : term270.
Proof. exact (@lem5168547 (@lem5168557)). Qed.
Lemma lem5168560 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168561 : term232 = term238.
Proof. exact (@lem5168560 (NUMERAL 0) term85). Qed.
Lemma lem5168562 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168563 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168564 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168563 h1) (fun h1 : term238 = True => @lem5168562)). Qed.
Lemma lem5168565 : term238 = True.
Proof. exact (EQ_MP (@lem5168564) (@lem5168562)). Qed.
Lemma lem5168566 : term232 = True.
Proof. exact (TRANS (@lem5168561) (@lem5168565)). Qed.
Lemma lem5168567 : True = term232.
Proof. exact (SYM (@lem5168566)). Qed.
Lemma lem5168568 : term232.
Proof. exact (EQ_MP (@lem5168567) (@lem0)). Qed.
Lemma lem5168569 : term271.
Proof. exact (@lem5168558 (@lem5168568)). Qed.
Lemma lem5168571 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168572 : term232 = term238.
Proof. exact (@lem5168571 (NUMERAL 0) term85). Qed.
Lemma lem5168573 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168574 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168575 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168574 h1) (fun h1 : term238 = True => @lem5168573)). Qed.
Lemma lem5168576 : term238 = True.
Proof. exact (EQ_MP (@lem5168575) (@lem5168573)). Qed.
Lemma lem5168577 : term232 = True.
Proof. exact (TRANS (@lem5168572) (@lem5168576)). Qed.
Lemma lem5168578 : True = term232.
Proof. exact (SYM (@lem5168577)). Qed.
Lemma lem5168579 : term232.
Proof. exact (EQ_MP (@lem5168578) (@lem0)). Qed.
Lemma lem5168580 : term272.
Proof. exact (@lem5168569 (@lem5168579)). Qed.
Lemma lem5168582 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5168583 : term94 = term95.
Proof. exact (@lem5168582 term85 term85). Qed.
Lemma lem5168584 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168585 : term97 = term85.
Proof. exact (EQ_MP (@lem5168584) (@lem940073)). Qed.
Lemma lem5168586 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168587 : term95 = term91.
Proof. exact (MK_COMB (@lem5168586) (@lem5168585)). Qed.
Lemma lem5168588 : term94 = term91.
Proof. exact (TRANS (@lem5168583) (@lem5168587)). Qed.
Lemma lem5168590 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5168591 : term275 = term276.
Proof. exact (@lem5168590 term85 term85). Qed.
Lemma lem5168592 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168593 : term97 = term85.
Proof. exact (EQ_MP (@lem5168592) (@lem940073)). Qed.
Lemma lem5168594 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168595 : term95 = term91.
Proof. exact (MK_COMB (@lem5168594) (@lem5168593)). Qed.
Lemma lem5168596 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5168597 : term276 = term51.
Proof. exact (MK_COMB (@lem5168596) (@lem5168595)). Qed.
Lemma lem5168598 : term275 = term51.
Proof. exact (TRANS (@lem5168591) (@lem5168597)). Qed.
Lemma lem5168599 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5168600 : term277 = term265.
Proof. exact (MK_COMB (@lem5168599) (@lem5168598)). Qed.
Lemma lem5168601 : term278 = term267.
Proof. exact (MK_COMB (@lem5168600) (@lem5168588)). Qed.
Lemma lem5168603 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5168604 : term267 = term32.
Proof. exact (@lem5168603 term85). Qed.
Lemma lem5168605 : term278 = term32.
Proof. exact (TRANS (@lem5168601) (@lem5168604)). Qed.
Lemma lem5168606 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5168607 : term280 = term281.
Proof. exact (MK_COMB (@lem5168606) (@lem5168605)). Qed.
Lemma lem5168608 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5168609 : term282 = term243.
Proof. exact (MK_COMB (@lem5168607) (@lem5168608)). Qed.
Lemma lem5168611 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168612 : term243 = term32.
Proof. exact (@lem5168611 term85). Qed.
Lemma lem5168613 : term282 = term32.
Proof. exact (TRANS (@lem5168609) (@lem5168612)). Qed.
Lemma lem5168615 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5168616 : term94 = term95.
Proof. exact (@lem5168615 term85 term85). Qed.
Lemma lem5168617 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168618 : term97 = term85.
Proof. exact (EQ_MP (@lem5168617) (@lem940073)). Qed.
Lemma lem5168619 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168620 : term95 = term91.
Proof. exact (MK_COMB (@lem5168619) (@lem5168618)). Qed.
Lemma lem5168621 : term94 = term91.
Proof. exact (TRANS (@lem5168616) (@lem5168620)). Qed.
Lemma lem5168622 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5168623 : term283 = term243.
Proof. exact (MK_COMB (@lem5168622) (@lem5168621)). Qed.
Lemma lem5168625 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168626 : term243 = term32.
Proof. exact (@lem5168625 term85). Qed.
Lemma lem5168627 : term283 = term32.
Proof. exact (TRANS (@lem5168623) (@lem5168626)). Qed.
Lemma lem5168628 : term32 = term283.
Proof. exact (SYM (@lem5168627)). Qed.
Lemma lem5168629 : term282 = term283.
Proof. exact (TRANS (@lem5168613) (@lem5168628)). Qed.
Lemma lem5168630 : term268 = term172.
Proof. exact (@lem5168580 (@lem5168629)). Qed.
Lemma lem5168631 : term267 = term172.
Proof. exact (TRANS (@lem5168546) (@lem5168630)). Qed.
Lemma lem5168633 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5168634 : term172 = term32.
Proof. exact (@lem5168633 term32). Qed.
Lemma lem5168635 : term267 = term32.
Proof. exact (TRANS (@lem5168631) (@lem5168634)). Qed.
Lemma lem5168636 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5168637 : term284 = term281.
Proof. exact (MK_COMB (@lem5168636) (@lem5168635)). Qed.
Lemma lem5168638 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5168639 (l : real) : (term264 l) = (term285 l).
Proof. exact (MK_COMB (@lem5168637) (@lem5168638 l)). Qed.
Lemma lem5168640 (l : real) : (term263 l) = (term285 l).
Proof. exact (TRANS (@lem5168537 l) (@lem5168639 l)). Qed.
Lemma lem5168641 (l : real) : (term285 l) = term32.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5168642 (l : real) : (term263 l) = term32.
Proof. exact (TRANS (@lem5168640 l) (@lem5168641 l)). Qed.
Lemma lem5168643 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5168644 (l : real) : (term286 l) = term206.
Proof. exact (MK_COMB (@lem5168643) (@lem5168642 l)). Qed.
Lemma lem5168645 (x : real) : (term289 x) = (term264 x).
Proof. exact (@lem1982715 term51 x). Qed.
Lemma lem5168647 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168648 : term91 = term101.
Proof. exact (@lem5168647 term85). Qed.
Lemma lem5168650 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5168651 : term51 = term84.
Proof. exact (@lem5168650 term85). Qed.
Lemma lem5168652 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5168653 : term265 = term266.
Proof. exact (MK_COMB (@lem5168652) (@lem5168651)). Qed.
Lemma lem5168654 : term267 = term268.
Proof. exact (MK_COMB (@lem5168653) (@lem5168648)). Qed.
Lemma lem5168655 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5168657 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168658 : term232 = term238.
Proof. exact (@lem5168657 (NUMERAL 0) term85). Qed.
Lemma lem5168659 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168660 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168661 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168660 h1) (fun h1 : term238 = True => @lem5168659)). Qed.
Lemma lem5168662 : term238 = True.
Proof. exact (EQ_MP (@lem5168661) (@lem5168659)). Qed.
Lemma lem5168663 : term232 = True.
Proof. exact (TRANS (@lem5168658) (@lem5168662)). Qed.
Lemma lem5168664 : True = term232.
Proof. exact (SYM (@lem5168663)). Qed.
Lemma lem5168665 : term232.
Proof. exact (EQ_MP (@lem5168664) (@lem0)). Qed.
Lemma lem5168666 : term270.
Proof. exact (@lem5168655 (@lem5168665)). Qed.
Lemma lem5168668 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168669 : term232 = term238.
Proof. exact (@lem5168668 (NUMERAL 0) term85). Qed.
Lemma lem5168670 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168671 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168672 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168671 h1) (fun h1 : term238 = True => @lem5168670)). Qed.
Lemma lem5168673 : term238 = True.
Proof. exact (EQ_MP (@lem5168672) (@lem5168670)). Qed.
Lemma lem5168674 : term232 = True.
Proof. exact (TRANS (@lem5168669) (@lem5168673)). Qed.
Lemma lem5168675 : True = term232.
Proof. exact (SYM (@lem5168674)). Qed.
Lemma lem5168676 : term232.
Proof. exact (EQ_MP (@lem5168675) (@lem0)). Qed.
Lemma lem5168677 : term271.
Proof. exact (@lem5168666 (@lem5168676)). Qed.
Lemma lem5168679 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168680 : term232 = term238.
Proof. exact (@lem5168679 (NUMERAL 0) term85). Qed.
Lemma lem5168681 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168682 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168683 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168682 h1) (fun h1 : term238 = True => @lem5168681)). Qed.
Lemma lem5168684 : term238 = True.
Proof. exact (EQ_MP (@lem5168683) (@lem5168681)). Qed.
Lemma lem5168685 : term232 = True.
Proof. exact (TRANS (@lem5168680) (@lem5168684)). Qed.
Lemma lem5168686 : True = term232.
Proof. exact (SYM (@lem5168685)). Qed.
Lemma lem5168687 : term232.
Proof. exact (EQ_MP (@lem5168686) (@lem0)). Qed.
Lemma lem5168688 : term272.
Proof. exact (@lem5168677 (@lem5168687)). Qed.
Lemma lem5168690 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5168691 : term94 = term95.
Proof. exact (@lem5168690 term85 term85). Qed.
Lemma lem5168692 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168693 : term97 = term85.
Proof. exact (EQ_MP (@lem5168692) (@lem940073)). Qed.
Lemma lem5168694 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168695 : term95 = term91.
Proof. exact (MK_COMB (@lem5168694) (@lem5168693)). Qed.
Lemma lem5168696 : term94 = term91.
Proof. exact (TRANS (@lem5168691) (@lem5168695)). Qed.
Lemma lem5168698 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5168699 : term275 = term276.
Proof. exact (@lem5168698 term85 term85). Qed.
Lemma lem5168700 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168701 : term97 = term85.
Proof. exact (EQ_MP (@lem5168700) (@lem940073)). Qed.
Lemma lem5168702 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168703 : term95 = term91.
Proof. exact (MK_COMB (@lem5168702) (@lem5168701)). Qed.
Lemma lem5168704 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5168705 : term276 = term51.
Proof. exact (MK_COMB (@lem5168704) (@lem5168703)). Qed.
Lemma lem5168706 : term275 = term51.
Proof. exact (TRANS (@lem5168699) (@lem5168705)). Qed.
Lemma lem5168707 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5168708 : term277 = term265.
Proof. exact (MK_COMB (@lem5168707) (@lem5168706)). Qed.
Lemma lem5168709 : term278 = term267.
Proof. exact (MK_COMB (@lem5168708) (@lem5168696)). Qed.
Lemma lem5168711 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5168712 : term267 = term32.
Proof. exact (@lem5168711 term85). Qed.
Lemma lem5168713 : term278 = term32.
Proof. exact (TRANS (@lem5168709) (@lem5168712)). Qed.
Lemma lem5168714 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5168715 : term280 = term281.
Proof. exact (MK_COMB (@lem5168714) (@lem5168713)). Qed.
Lemma lem5168716 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5168717 : term282 = term243.
Proof. exact (MK_COMB (@lem5168715) (@lem5168716)). Qed.
Lemma lem5168719 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168720 : term243 = term32.
Proof. exact (@lem5168719 term85). Qed.
Lemma lem5168721 : term282 = term32.
Proof. exact (TRANS (@lem5168717) (@lem5168720)). Qed.
Lemma lem5168723 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5168724 : term94 = term95.
Proof. exact (@lem5168723 term85 term85). Qed.
Lemma lem5168725 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168726 : term97 = term85.
Proof. exact (EQ_MP (@lem5168725) (@lem940073)). Qed.
Lemma lem5168727 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168728 : term95 = term91.
Proof. exact (MK_COMB (@lem5168727) (@lem5168726)). Qed.
Lemma lem5168729 : term94 = term91.
Proof. exact (TRANS (@lem5168724) (@lem5168728)). Qed.
Lemma lem5168730 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5168731 : term283 = term243.
Proof. exact (MK_COMB (@lem5168730) (@lem5168729)). Qed.
Lemma lem5168733 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168734 : term243 = term32.
Proof. exact (@lem5168733 term85). Qed.
Lemma lem5168735 : term283 = term32.
Proof. exact (TRANS (@lem5168731) (@lem5168734)). Qed.
Lemma lem5168736 : term32 = term283.
Proof. exact (SYM (@lem5168735)). Qed.
Lemma lem5168737 : term282 = term283.
Proof. exact (TRANS (@lem5168721) (@lem5168736)). Qed.
Lemma lem5168738 : term268 = term172.
Proof. exact (@lem5168688 (@lem5168737)). Qed.
Lemma lem5168739 : term267 = term172.
Proof. exact (TRANS (@lem5168654) (@lem5168738)). Qed.
Lemma lem5168741 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5168742 : term172 = term32.
Proof. exact (@lem5168741 term32). Qed.
Lemma lem5168743 : term267 = term32.
Proof. exact (TRANS (@lem5168739) (@lem5168742)). Qed.
Lemma lem5168744 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5168745 : term284 = term281.
Proof. exact (MK_COMB (@lem5168744) (@lem5168743)). Qed.
Lemma lem5168746 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5168747 (x : real) : (term264 x) = (term285 x).
Proof. exact (MK_COMB (@lem5168745) (@lem5168746 x)). Qed.
Lemma lem5168748 (x : real) : (term289 x) = (term285 x).
Proof. exact (TRANS (@lem5168645 x) (@lem5168747 x)). Qed.
Lemma lem5168749 (x : real) : (term285 x) = term32.
Proof. exact (@lem1982719 x). Qed.
Lemma lem5168750 (x : real) : (term289 x) = term32.
Proof. exact (TRANS (@lem5168748 x) (@lem5168749 x)). Qed.
Lemma lem5168751 (l : real) (x : real) : (term317 l x) = term291.
Proof. exact (MK_COMB (@lem5168644 l) (@lem5168750 x)). Qed.
Lemma lem5168752 (l : real) (x : real) : (term316 l x) = term291.
Proof. exact (TRANS (@lem5168536 l x) (@lem5168751 l x)). Qed.
Lemma lem5168753 : term291 = term32.
Proof. exact (@lem1982721 term32). Qed.
Lemma lem5168754 (l : real) (x : real) : (term316 l x) = term32.
Proof. exact (TRANS (@lem5168752 l x) (@lem5168753)). Qed.
Lemma lem5168755 (e : real) (l : real) (x : real) : (term315 e l x) = term291.
Proof. exact (MK_COMB (@lem5168535 e) (@lem5168754 l x)). Qed.
Lemma lem5168756 (e : real) (l : real) (x : real) : (term314 e l x) = term291.
Proof. exact (TRANS (@lem5168427 e l x) (@lem5168755 e l x)). Qed.
Lemma lem5168757 : term291 = term32.
Proof. exact (@lem1982721 term32). Qed.
Lemma lem5168758 (e : real) (l : real) (x : real) : (term314 e l x) = term32.
Proof. exact (TRANS (@lem5168756 e l x) (@lem5168757)). Qed.
Lemma lem5168759 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5168760 (e : real) (l : real) (x : real) : (term318 e l x) = term293.
Proof. exact (MK_COMB (@lem5168759) (@lem5168758 e l x)). Qed.
Lemma lem5168761 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5168762 (e : real) (l : real) (x : real) : (term313 e l x) = term294.
Proof. exact (MK_COMB (@lem5168760 e l x) (@lem5168761)). Qed.
Lemma lem5168763 (e : real) (l : real) (x : real) (h1 : term146 e l x) : term294.
Proof. exact (EQ_MP (@lem5168762 e l x) (@lem5168426 e l x h1)). Qed.
Lemma lem5168765 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5168766 : term294 = term295.
Proof. exact (@lem5168765 term32 term32). Qed.
Lemma lem5168768 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168769 : term32 = term172.
Proof. exact (@lem5168768 (NUMERAL 0)). Qed.
Lemma lem5168771 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168772 : term32 = term172.
Proof. exact (@lem5168771 (NUMERAL 0)). Qed.
Lemma lem5168773 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5168774 : term233 = term234.
Proof. exact (MK_COMB (@lem5168773) (@lem5168772)). Qed.
Lemma lem5168775 : term295 = term296.
Proof. exact (MK_COMB (@lem5168774) (@lem5168769)). Qed.
Lemma lem5168776 : term297.
Proof. exact (@lem1980255 term32 term91 term32 term91). Qed.
Lemma lem5168778 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168779 : term232 = term238.
Proof. exact (@lem5168778 (NUMERAL 0) term85). Qed.
Lemma lem5168780 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168781 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168782 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168781 h1) (fun h1 : term238 = True => @lem5168780)). Qed.
Lemma lem5168783 : term238 = True.
Proof. exact (EQ_MP (@lem5168782) (@lem5168780)). Qed.
Lemma lem5168784 : term232 = True.
Proof. exact (TRANS (@lem5168779) (@lem5168783)). Qed.
Lemma lem5168785 : True = term232.
Proof. exact (SYM (@lem5168784)). Qed.
Lemma lem5168786 : term232.
Proof. exact (EQ_MP (@lem5168785) (@lem0)). Qed.
Lemma lem5168787 : term298.
Proof. exact (@lem5168776 (@lem5168786)). Qed.
Lemma lem5168789 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168790 : term232 = term238.
Proof. exact (@lem5168789 (NUMERAL 0) term85). Qed.
Lemma lem5168791 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168792 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168793 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168792 h1) (fun h1 : term238 = True => @lem5168791)). Qed.
Lemma lem5168794 : term238 = True.
Proof. exact (EQ_MP (@lem5168793) (@lem5168791)). Qed.
Lemma lem5168795 : term232 = True.
Proof. exact (TRANS (@lem5168790) (@lem5168794)). Qed.
Lemma lem5168796 : True = term232.
Proof. exact (SYM (@lem5168795)). Qed.
Lemma lem5168797 : term232.
Proof. exact (EQ_MP (@lem5168796) (@lem0)). Qed.
Lemma lem5168798 : term296 = term299.
Proof. exact (@lem5168787 (@lem5168797)). Qed.
Lemma lem5168800 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168801 : term243 = term32.
Proof. exact (@lem5168800 term85). Qed.
Lemma lem5168803 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168804 : term243 = term32.
Proof. exact (@lem5168803 term85). Qed.
Lemma lem5168805 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5168806 : term244 = term233.
Proof. exact (MK_COMB (@lem5168805) (@lem5168804)). Qed.
Lemma lem5168807 : term299 = term295.
Proof. exact (MK_COMB (@lem5168806) (@lem5168801)). Qed.
Lemma lem5168809 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168810 : term295 = term300.
Proof. exact (@lem5168809 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5168811 : term300 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5168812 : term295 = False.
Proof. exact (TRANS (@lem5168810) (@lem5168811)). Qed.
Lemma lem5168813 : term299 = False.
Proof. exact (TRANS (@lem5168807) (@lem5168812)). Qed.
Lemma lem5168814 : term296 = False.
Proof. exact (TRANS (@lem5168798) (@lem5168813)). Qed.
Lemma lem5168815 : term295 = False.
Proof. exact (TRANS (@lem5168775) (@lem5168814)). Qed.
Lemma lem5168816 : term294 = False.
Proof. exact (TRANS (@lem5168766) (@lem5168815)). Qed.
Lemma lem5168817 (e : real) (l : real) (x : real) (h1 : term146 e l x) : False.
Proof. exact (EQ_MP (@lem5168816) (@lem5168763 e l x h1)). Qed.
Lemma lem5168818 (e : real) (l : real) (x : real) (h1 : term149 e l x) : False.
Proof. exact (or_elim (@lem5167719 e l x h1) (fun h0 : term144 e l x => @lem5168268 e l x h0) (fun h0 : term146 e l x => @lem5168817 e l x h0)). Qed.
Lemma lem5168819 (e : real) (l : real) (x : real) (h1 : term228 e l x) : term228 e l x.
Proof. exact (h1). Qed.
Lemma lem5168820 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term162 e l x.
Proof. exact (h1). Qed.
Lemma lem5168821 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term159 e l x.
Proof. exact (proj2 (@lem5168820 e l x h1)). Qed.
Lemma lem5168823 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term121 e l x.
Proof. exact (proj2 (@lem5168821 e l x h1)). Qed.
Lemma lem5168824 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term57 e l x.
Proof. exact (proj1 (@lem5168821 e l x h1)). Qed.
Lemma lem5168825 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term118 e l x.
Proof. exact (proj2 (@lem5168823 e l x h1)). Qed.
Lemma lem5168828 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5168829 : term231 = term232.
Proof. exact (@lem5168828 term32 term91). Qed.
Lemma lem5168831 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168832 : term91 = term101.
Proof. exact (@lem5168831 term85). Qed.
Lemma lem5168834 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168835 : term32 = term172.
Proof. exact (@lem5168834 (NUMERAL 0)). Qed.
Lemma lem5168836 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5168837 : term233 = term234.
Proof. exact (MK_COMB (@lem5168836) (@lem5168835)). Qed.
Lemma lem5168838 : term232 = term235.
Proof. exact (MK_COMB (@lem5168837) (@lem5168832)). Qed.
Lemma lem5168839 : term236.
Proof. exact (@lem1980255 term32 term91 term91 term91). Qed.
Lemma lem5168841 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168842 : term232 = term238.
Proof. exact (@lem5168841 (NUMERAL 0) term85). Qed.
Lemma lem5168843 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168844 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168845 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168844 h1) (fun h1 : term238 = True => @lem5168843)). Qed.
Lemma lem5168846 : term238 = True.
Proof. exact (EQ_MP (@lem5168845) (@lem5168843)). Qed.
Lemma lem5168847 : term232 = True.
Proof. exact (TRANS (@lem5168842) (@lem5168846)). Qed.
Lemma lem5168848 : True = term232.
Proof. exact (SYM (@lem5168847)). Qed.
Lemma lem5168849 : term232.
Proof. exact (EQ_MP (@lem5168848) (@lem0)). Qed.
Lemma lem5168850 : term240.
Proof. exact (@lem5168839 (@lem5168849)). Qed.
Lemma lem5168852 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168853 : term232 = term238.
Proof. exact (@lem5168852 (NUMERAL 0) term85). Qed.
Lemma lem5168854 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168855 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168856 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168855 h1) (fun h1 : term238 = True => @lem5168854)). Qed.
Lemma lem5168857 : term238 = True.
Proof. exact (EQ_MP (@lem5168856) (@lem5168854)). Qed.
Lemma lem5168858 : term232 = True.
Proof. exact (TRANS (@lem5168853) (@lem5168857)). Qed.
Lemma lem5168859 : True = term232.
Proof. exact (SYM (@lem5168858)). Qed.
Lemma lem5168860 : term232.
Proof. exact (EQ_MP (@lem5168859) (@lem0)). Qed.
Lemma lem5168861 : term235 = term241.
Proof. exact (@lem5168850 (@lem5168860)). Qed.
Lemma lem5168863 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5168864 : term94 = term95.
Proof. exact (@lem5168863 term85 term85). Qed.
Lemma lem5168865 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168866 : term97 = term85.
Proof. exact (EQ_MP (@lem5168865) (@lem940073)). Qed.
Lemma lem5168867 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168868 : term95 = term91.
Proof. exact (MK_COMB (@lem5168867) (@lem5168866)). Qed.
Lemma lem5168869 : term94 = term91.
Proof. exact (TRANS (@lem5168864) (@lem5168868)). Qed.
Lemma lem5168871 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168872 : term243 = term32.
Proof. exact (@lem5168871 term85). Qed.
Lemma lem5168873 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5168874 : term244 = term233.
Proof. exact (MK_COMB (@lem5168873) (@lem5168872)). Qed.
Lemma lem5168875 : term241 = term232.
Proof. exact (MK_COMB (@lem5168874) (@lem5168869)). Qed.
Lemma lem5168877 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168878 : term232 = term238.
Proof. exact (@lem5168877 (NUMERAL 0) term85). Qed.
Lemma lem5168879 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168880 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168881 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168880 h1) (fun h1 : term238 = True => @lem5168879)). Qed.
Lemma lem5168882 : term238 = True.
Proof. exact (EQ_MP (@lem5168881) (@lem5168879)). Qed.
Lemma lem5168883 : term232 = True.
Proof. exact (TRANS (@lem5168878) (@lem5168882)). Qed.
Lemma lem5168884 : term241 = True.
Proof. exact (TRANS (@lem5168875) (@lem5168883)). Qed.
Lemma lem5168885 : term235 = True.
Proof. exact (TRANS (@lem5168861) (@lem5168884)). Qed.
Lemma lem5168886 : term232 = True.
Proof. exact (TRANS (@lem5168838) (@lem5168885)). Qed.
Lemma lem5168887 : term231 = True.
Proof. exact (TRANS (@lem5168829) (@lem5168886)). Qed.
Lemma lem5168888 : True = term231.
Proof. exact (SYM (@lem5168887)). Qed.
Lemma lem5168889 : term231.
Proof. exact (EQ_MP (@lem5168888) (@lem0)). Qed.
Lemma lem5168890 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term301 e l x.
Proof. exact (conj (@lem5168889) (@lem5168825 e l x h1)). Qed.
Lemma lem5168892 (x : real) (y : real) : term246 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5168893 (e : real) (l : real) (x : real) : term302 e l x.
Proof. exact (@lem5168892 term91 (term107 e l x)). Qed.
Lemma lem5168894 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term303 e l x.
Proof. exact (@lem5168893 e l x (@lem5168890 e l x h1)). Qed.
Lemma lem5168895 (e : real) (l : real) (x : real) : (term304 e l x) = (term107 e l x).
Proof. exact (@lem1982733 (term107 e l x)). Qed.
Lemma lem5168896 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5168897 (e : real) (l : real) (x : real) : (term305 e l x) = (term117 e l x).
Proof. exact (MK_COMB (@lem5168896) (@lem5168895 e l x)). Qed.
Lemma lem5168898 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5168899 (e : real) (l : real) (x : real) : (term303 e l x) = (term118 e l x).
Proof. exact (MK_COMB (@lem5168897 e l x) (@lem5168898)). Qed.
Lemma lem5168900 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term118 e l x.
Proof. exact (EQ_MP (@lem5168899 e l x) (@lem5168894 e l x h1)). Qed.
Lemma lem5168902 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5168903 : term231 = term232.
Proof. exact (@lem5168902 term32 term91). Qed.
Lemma lem5168905 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168906 : term91 = term101.
Proof. exact (@lem5168905 term85). Qed.
Lemma lem5168908 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168909 : term32 = term172.
Proof. exact (@lem5168908 (NUMERAL 0)). Qed.
Lemma lem5168910 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5168911 : term233 = term234.
Proof. exact (MK_COMB (@lem5168910) (@lem5168909)). Qed.
Lemma lem5168912 : term232 = term235.
Proof. exact (MK_COMB (@lem5168911) (@lem5168906)). Qed.
Lemma lem5168913 : term236.
Proof. exact (@lem1980255 term32 term91 term91 term91). Qed.
Lemma lem5168915 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168916 : term232 = term238.
Proof. exact (@lem5168915 (NUMERAL 0) term85). Qed.
Lemma lem5168917 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168918 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168919 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168918 h1) (fun h1 : term238 = True => @lem5168917)). Qed.
Lemma lem5168920 : term238 = True.
Proof. exact (EQ_MP (@lem5168919) (@lem5168917)). Qed.
Lemma lem5168921 : term232 = True.
Proof. exact (TRANS (@lem5168916) (@lem5168920)). Qed.
Lemma lem5168922 : True = term232.
Proof. exact (SYM (@lem5168921)). Qed.
Lemma lem5168923 : term232.
Proof. exact (EQ_MP (@lem5168922) (@lem0)). Qed.
Lemma lem5168924 : term240.
Proof. exact (@lem5168913 (@lem5168923)). Qed.
Lemma lem5168926 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168927 : term232 = term238.
Proof. exact (@lem5168926 (NUMERAL 0) term85). Qed.
Lemma lem5168928 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168929 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168930 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168929 h1) (fun h1 : term238 = True => @lem5168928)). Qed.
Lemma lem5168931 : term238 = True.
Proof. exact (EQ_MP (@lem5168930) (@lem5168928)). Qed.
Lemma lem5168932 : term232 = True.
Proof. exact (TRANS (@lem5168927) (@lem5168931)). Qed.
Lemma lem5168933 : True = term232.
Proof. exact (SYM (@lem5168932)). Qed.
Lemma lem5168934 : term232.
Proof. exact (EQ_MP (@lem5168933) (@lem0)). Qed.
Lemma lem5168935 : term235 = term241.
Proof. exact (@lem5168924 (@lem5168934)). Qed.
Lemma lem5168937 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5168938 : term94 = term95.
Proof. exact (@lem5168937 term85 term85). Qed.
Lemma lem5168939 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5168940 : term97 = term85.
Proof. exact (EQ_MP (@lem5168939) (@lem940073)). Qed.
Lemma lem5168941 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5168942 : term95 = term91.
Proof. exact (MK_COMB (@lem5168941) (@lem5168940)). Qed.
Lemma lem5168943 : term94 = term91.
Proof. exact (TRANS (@lem5168938) (@lem5168942)). Qed.
Lemma lem5168945 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5168946 : term243 = term32.
Proof. exact (@lem5168945 term85). Qed.
Lemma lem5168947 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5168948 : term244 = term233.
Proof. exact (MK_COMB (@lem5168947) (@lem5168946)). Qed.
Lemma lem5168949 : term241 = term232.
Proof. exact (MK_COMB (@lem5168948) (@lem5168943)). Qed.
Lemma lem5168951 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168952 : term232 = term238.
Proof. exact (@lem5168951 (NUMERAL 0) term85). Qed.
Lemma lem5168953 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168954 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168955 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168954 h1) (fun h1 : term238 = True => @lem5168953)). Qed.
Lemma lem5168956 : term238 = True.
Proof. exact (EQ_MP (@lem5168955) (@lem5168953)). Qed.
Lemma lem5168957 : term232 = True.
Proof. exact (TRANS (@lem5168952) (@lem5168956)). Qed.
Lemma lem5168958 : term241 = True.
Proof. exact (TRANS (@lem5168949) (@lem5168957)). Qed.
Lemma lem5168959 : term235 = True.
Proof. exact (TRANS (@lem5168935) (@lem5168958)). Qed.
Lemma lem5168960 : term232 = True.
Proof. exact (TRANS (@lem5168912) (@lem5168959)). Qed.
Lemma lem5168961 : term231 = True.
Proof. exact (TRANS (@lem5168903) (@lem5168960)). Qed.
Lemma lem5168962 : True = term231.
Proof. exact (SYM (@lem5168961)). Qed.
Lemma lem5168963 : term231.
Proof. exact (EQ_MP (@lem5168962) (@lem0)). Qed.
Lemma lem5168964 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term306 e l x.
Proof. exact (conj (@lem5168963) (@lem5168824 e l x h1)). Qed.
Lemma lem5168966 (x : real) (y : real) : term252 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5168967 (e : real) (l : real) (x : real) : term307 e l x.
Proof. exact (@lem5168966 term91 (term54 e l x)). Qed.
Lemma lem5168968 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term308 e l x.
Proof. exact (@lem5168967 e l x (@lem5168964 e l x h1)). Qed.
Lemma lem5168969 (e : real) (l : real) (x : real) : (term309 e l x) = (term54 e l x).
Proof. exact (@lem1982733 (term54 e l x)). Qed.
Lemma lem5168970 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5168971 (e : real) (l : real) (x : real) : (term310 e l x) = (term56 e l x).
Proof. exact (MK_COMB (@lem5168970) (@lem5168969 e l x)). Qed.
Lemma lem5168972 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5168973 (e : real) (l : real) (x : real) : (term308 e l x) = (term57 e l x).
Proof. exact (MK_COMB (@lem5168971 e l x) (@lem5168972)). Qed.
Lemma lem5168974 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term57 e l x.
Proof. exact (EQ_MP (@lem5168973 e l x) (@lem5168968 e l x h1)). Qed.
Lemma lem5168975 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term311 e l x.
Proof. exact (conj (@lem5168974 e l x h1) (@lem5168900 e l x h1)). Qed.
Lemma lem5168977 (x : real) (y : real) : term258 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5168978 (e : real) (l : real) (x : real) : term312 e l x.
Proof. exact (@lem5168977 (term54 e l x) (term107 e l x)). Qed.
Lemma lem5168979 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term313 e l x.
Proof. exact (@lem5168978 e l x (@lem5168975 e l x h1)). Qed.
Lemma lem5168980 (e : real) (l : real) (x : real) : (term314 e l x) = (term315 e l x).
Proof. exact (@lem1982753 (term25 e) e (term24 l x) (term23 l x)). Qed.
Lemma lem5168981 (e : real) : (term263 e) = (term264 e).
Proof. exact (@lem1982713 term51 e). Qed.
Lemma lem5168983 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5168984 : term91 = term101.
Proof. exact (@lem5168983 term85). Qed.
Lemma lem5168986 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5168987 : term51 = term84.
Proof. exact (@lem5168986 term85). Qed.
Lemma lem5168988 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5168989 : term265 = term266.
Proof. exact (MK_COMB (@lem5168988) (@lem5168987)). Qed.
Lemma lem5168990 : term267 = term268.
Proof. exact (MK_COMB (@lem5168989) (@lem5168984)). Qed.
Lemma lem5168991 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5168993 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5168994 : term232 = term238.
Proof. exact (@lem5168993 (NUMERAL 0) term85). Qed.
Lemma lem5168995 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5168996 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5168997 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5168996 h1) (fun h1 : term238 = True => @lem5168995)). Qed.
Lemma lem5168998 : term238 = True.
Proof. exact (EQ_MP (@lem5168997) (@lem5168995)). Qed.
Lemma lem5168999 : term232 = True.
Proof. exact (TRANS (@lem5168994) (@lem5168998)). Qed.
Lemma lem5169000 : True = term232.
Proof. exact (SYM (@lem5168999)). Qed.
Lemma lem5169001 : term232.
Proof. exact (EQ_MP (@lem5169000) (@lem0)). Qed.
Lemma lem5169002 : term270.
Proof. exact (@lem5168991 (@lem5169001)). Qed.
Lemma lem5169004 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169005 : term232 = term238.
Proof. exact (@lem5169004 (NUMERAL 0) term85). Qed.
Lemma lem5169006 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169007 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169008 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169007 h1) (fun h1 : term238 = True => @lem5169006)). Qed.
Lemma lem5169009 : term238 = True.
Proof. exact (EQ_MP (@lem5169008) (@lem5169006)). Qed.
Lemma lem5169010 : term232 = True.
Proof. exact (TRANS (@lem5169005) (@lem5169009)). Qed.
Lemma lem5169011 : True = term232.
Proof. exact (SYM (@lem5169010)). Qed.
Lemma lem5169012 : term232.
Proof. exact (EQ_MP (@lem5169011) (@lem0)). Qed.
Lemma lem5169013 : term271.
Proof. exact (@lem5169002 (@lem5169012)). Qed.
Lemma lem5169015 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169016 : term232 = term238.
Proof. exact (@lem5169015 (NUMERAL 0) term85). Qed.
Lemma lem5169017 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169018 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169019 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169018 h1) (fun h1 : term238 = True => @lem5169017)). Qed.
Lemma lem5169020 : term238 = True.
Proof. exact (EQ_MP (@lem5169019) (@lem5169017)). Qed.
Lemma lem5169021 : term232 = True.
Proof. exact (TRANS (@lem5169016) (@lem5169020)). Qed.
Lemma lem5169022 : True = term232.
Proof. exact (SYM (@lem5169021)). Qed.
Lemma lem5169023 : term232.
Proof. exact (EQ_MP (@lem5169022) (@lem0)). Qed.
Lemma lem5169024 : term272.
Proof. exact (@lem5169013 (@lem5169023)). Qed.
Lemma lem5169026 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5169027 : term94 = term95.
Proof. exact (@lem5169026 term85 term85). Qed.
Lemma lem5169028 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169029 : term97 = term85.
Proof. exact (EQ_MP (@lem5169028) (@lem940073)). Qed.
Lemma lem5169030 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169031 : term95 = term91.
Proof. exact (MK_COMB (@lem5169030) (@lem5169029)). Qed.
Lemma lem5169032 : term94 = term91.
Proof. exact (TRANS (@lem5169027) (@lem5169031)). Qed.
Lemma lem5169034 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5169035 : term275 = term276.
Proof. exact (@lem5169034 term85 term85). Qed.
Lemma lem5169036 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169037 : term97 = term85.
Proof. exact (EQ_MP (@lem5169036) (@lem940073)). Qed.
Lemma lem5169038 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169039 : term95 = term91.
Proof. exact (MK_COMB (@lem5169038) (@lem5169037)). Qed.
Lemma lem5169040 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5169041 : term276 = term51.
Proof. exact (MK_COMB (@lem5169040) (@lem5169039)). Qed.
Lemma lem5169042 : term275 = term51.
Proof. exact (TRANS (@lem5169035) (@lem5169041)). Qed.
Lemma lem5169043 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5169044 : term277 = term265.
Proof. exact (MK_COMB (@lem5169043) (@lem5169042)). Qed.
Lemma lem5169045 : term278 = term267.
Proof. exact (MK_COMB (@lem5169044) (@lem5169032)). Qed.
Lemma lem5169047 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5169048 : term267 = term32.
Proof. exact (@lem5169047 term85). Qed.
Lemma lem5169049 : term278 = term32.
Proof. exact (TRANS (@lem5169045) (@lem5169048)). Qed.
Lemma lem5169050 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5169051 : term280 = term281.
Proof. exact (MK_COMB (@lem5169050) (@lem5169049)). Qed.
Lemma lem5169052 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5169053 : term282 = term243.
Proof. exact (MK_COMB (@lem5169051) (@lem5169052)). Qed.
Lemma lem5169055 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169056 : term243 = term32.
Proof. exact (@lem5169055 term85). Qed.
Lemma lem5169057 : term282 = term32.
Proof. exact (TRANS (@lem5169053) (@lem5169056)). Qed.
Lemma lem5169059 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5169060 : term94 = term95.
Proof. exact (@lem5169059 term85 term85). Qed.
Lemma lem5169061 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169062 : term97 = term85.
Proof. exact (EQ_MP (@lem5169061) (@lem940073)). Qed.
Lemma lem5169063 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169064 : term95 = term91.
Proof. exact (MK_COMB (@lem5169063) (@lem5169062)). Qed.
Lemma lem5169065 : term94 = term91.
Proof. exact (TRANS (@lem5169060) (@lem5169064)). Qed.
Lemma lem5169066 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5169067 : term283 = term243.
Proof. exact (MK_COMB (@lem5169066) (@lem5169065)). Qed.
Lemma lem5169069 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169070 : term243 = term32.
Proof. exact (@lem5169069 term85). Qed.
Lemma lem5169071 : term283 = term32.
Proof. exact (TRANS (@lem5169067) (@lem5169070)). Qed.
Lemma lem5169072 : term32 = term283.
Proof. exact (SYM (@lem5169071)). Qed.
Lemma lem5169073 : term282 = term283.
Proof. exact (TRANS (@lem5169057) (@lem5169072)). Qed.
Lemma lem5169074 : term268 = term172.
Proof. exact (@lem5169024 (@lem5169073)). Qed.
Lemma lem5169075 : term267 = term172.
Proof. exact (TRANS (@lem5168990) (@lem5169074)). Qed.
Lemma lem5169077 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5169078 : term172 = term32.
Proof. exact (@lem5169077 term32). Qed.
Lemma lem5169079 : term267 = term32.
Proof. exact (TRANS (@lem5169075) (@lem5169078)). Qed.
Lemma lem5169080 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5169081 : term284 = term281.
Proof. exact (MK_COMB (@lem5169080) (@lem5169079)). Qed.
Lemma lem5169082 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem5169083 (e : real) : (term264 e) = (term285 e).
Proof. exact (MK_COMB (@lem5169081) (@lem5169082 e)). Qed.
Lemma lem5169084 (e : real) : (term263 e) = (term285 e).
Proof. exact (TRANS (@lem5168981 e) (@lem5169083 e)). Qed.
Lemma lem5169085 (e : real) : (term285 e) = term32.
Proof. exact (@lem1982719 e). Qed.
Lemma lem5169086 (e : real) : (term263 e) = term32.
Proof. exact (TRANS (@lem5169084 e) (@lem5169085 e)). Qed.
Lemma lem5169087 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5169088 (e : real) : (term286 e) = term206.
Proof. exact (MK_COMB (@lem5169087) (@lem5169086 e)). Qed.
Lemma lem5169089 (l : real) (x : real) : (term316 l x) = (term317 l x).
Proof. exact (@lem1982753 (term25 l) l x (term25 x)). Qed.
Lemma lem5169090 (l : real) : (term263 l) = (term264 l).
Proof. exact (@lem1982713 term51 l). Qed.
Lemma lem5169092 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5169093 : term91 = term101.
Proof. exact (@lem5169092 term85). Qed.
Lemma lem5169095 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5169096 : term51 = term84.
Proof. exact (@lem5169095 term85). Qed.
Lemma lem5169097 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5169098 : term265 = term266.
Proof. exact (MK_COMB (@lem5169097) (@lem5169096)). Qed.
Lemma lem5169099 : term267 = term268.
Proof. exact (MK_COMB (@lem5169098) (@lem5169093)). Qed.
Lemma lem5169100 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5169102 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169103 : term232 = term238.
Proof. exact (@lem5169102 (NUMERAL 0) term85). Qed.
Lemma lem5169104 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169105 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169106 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169105 h1) (fun h1 : term238 = True => @lem5169104)). Qed.
Lemma lem5169107 : term238 = True.
Proof. exact (EQ_MP (@lem5169106) (@lem5169104)). Qed.
Lemma lem5169108 : term232 = True.
Proof. exact (TRANS (@lem5169103) (@lem5169107)). Qed.
Lemma lem5169109 : True = term232.
Proof. exact (SYM (@lem5169108)). Qed.
Lemma lem5169110 : term232.
Proof. exact (EQ_MP (@lem5169109) (@lem0)). Qed.
Lemma lem5169111 : term270.
Proof. exact (@lem5169100 (@lem5169110)). Qed.
Lemma lem5169113 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169114 : term232 = term238.
Proof. exact (@lem5169113 (NUMERAL 0) term85). Qed.
Lemma lem5169115 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169116 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169117 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169116 h1) (fun h1 : term238 = True => @lem5169115)). Qed.
Lemma lem5169118 : term238 = True.
Proof. exact (EQ_MP (@lem5169117) (@lem5169115)). Qed.
Lemma lem5169119 : term232 = True.
Proof. exact (TRANS (@lem5169114) (@lem5169118)). Qed.
Lemma lem5169120 : True = term232.
Proof. exact (SYM (@lem5169119)). Qed.
Lemma lem5169121 : term232.
Proof. exact (EQ_MP (@lem5169120) (@lem0)). Qed.
Lemma lem5169122 : term271.
Proof. exact (@lem5169111 (@lem5169121)). Qed.
Lemma lem5169124 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169125 : term232 = term238.
Proof. exact (@lem5169124 (NUMERAL 0) term85). Qed.
Lemma lem5169126 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169127 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169128 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169127 h1) (fun h1 : term238 = True => @lem5169126)). Qed.
Lemma lem5169129 : term238 = True.
Proof. exact (EQ_MP (@lem5169128) (@lem5169126)). Qed.
Lemma lem5169130 : term232 = True.
Proof. exact (TRANS (@lem5169125) (@lem5169129)). Qed.
Lemma lem5169131 : True = term232.
Proof. exact (SYM (@lem5169130)). Qed.
Lemma lem5169132 : term232.
Proof. exact (EQ_MP (@lem5169131) (@lem0)). Qed.
Lemma lem5169133 : term272.
Proof. exact (@lem5169122 (@lem5169132)). Qed.
Lemma lem5169135 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5169136 : term94 = term95.
Proof. exact (@lem5169135 term85 term85). Qed.
Lemma lem5169137 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169138 : term97 = term85.
Proof. exact (EQ_MP (@lem5169137) (@lem940073)). Qed.
Lemma lem5169139 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169140 : term95 = term91.
Proof. exact (MK_COMB (@lem5169139) (@lem5169138)). Qed.
Lemma lem5169141 : term94 = term91.
Proof. exact (TRANS (@lem5169136) (@lem5169140)). Qed.
Lemma lem5169143 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5169144 : term275 = term276.
Proof. exact (@lem5169143 term85 term85). Qed.
Lemma lem5169145 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169146 : term97 = term85.
Proof. exact (EQ_MP (@lem5169145) (@lem940073)). Qed.
Lemma lem5169147 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169148 : term95 = term91.
Proof. exact (MK_COMB (@lem5169147) (@lem5169146)). Qed.
Lemma lem5169149 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5169150 : term276 = term51.
Proof. exact (MK_COMB (@lem5169149) (@lem5169148)). Qed.
Lemma lem5169151 : term275 = term51.
Proof. exact (TRANS (@lem5169144) (@lem5169150)). Qed.
Lemma lem5169152 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5169153 : term277 = term265.
Proof. exact (MK_COMB (@lem5169152) (@lem5169151)). Qed.
Lemma lem5169154 : term278 = term267.
Proof. exact (MK_COMB (@lem5169153) (@lem5169141)). Qed.
Lemma lem5169156 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5169157 : term267 = term32.
Proof. exact (@lem5169156 term85). Qed.
Lemma lem5169158 : term278 = term32.
Proof. exact (TRANS (@lem5169154) (@lem5169157)). Qed.
Lemma lem5169159 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5169160 : term280 = term281.
Proof. exact (MK_COMB (@lem5169159) (@lem5169158)). Qed.
Lemma lem5169161 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5169162 : term282 = term243.
Proof. exact (MK_COMB (@lem5169160) (@lem5169161)). Qed.
Lemma lem5169164 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169165 : term243 = term32.
Proof. exact (@lem5169164 term85). Qed.
Lemma lem5169166 : term282 = term32.
Proof. exact (TRANS (@lem5169162) (@lem5169165)). Qed.
Lemma lem5169168 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5169169 : term94 = term95.
Proof. exact (@lem5169168 term85 term85). Qed.
Lemma lem5169170 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169171 : term97 = term85.
Proof. exact (EQ_MP (@lem5169170) (@lem940073)). Qed.
Lemma lem5169172 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169173 : term95 = term91.
Proof. exact (MK_COMB (@lem5169172) (@lem5169171)). Qed.
Lemma lem5169174 : term94 = term91.
Proof. exact (TRANS (@lem5169169) (@lem5169173)). Qed.
Lemma lem5169175 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5169176 : term283 = term243.
Proof. exact (MK_COMB (@lem5169175) (@lem5169174)). Qed.
Lemma lem5169178 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169179 : term243 = term32.
Proof. exact (@lem5169178 term85). Qed.
Lemma lem5169180 : term283 = term32.
Proof. exact (TRANS (@lem5169176) (@lem5169179)). Qed.
Lemma lem5169181 : term32 = term283.
Proof. exact (SYM (@lem5169180)). Qed.
Lemma lem5169182 : term282 = term283.
Proof. exact (TRANS (@lem5169166) (@lem5169181)). Qed.
Lemma lem5169183 : term268 = term172.
Proof. exact (@lem5169133 (@lem5169182)). Qed.
Lemma lem5169184 : term267 = term172.
Proof. exact (TRANS (@lem5169099) (@lem5169183)). Qed.
Lemma lem5169186 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5169187 : term172 = term32.
Proof. exact (@lem5169186 term32). Qed.
Lemma lem5169188 : term267 = term32.
Proof. exact (TRANS (@lem5169184) (@lem5169187)). Qed.
Lemma lem5169189 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5169190 : term284 = term281.
Proof. exact (MK_COMB (@lem5169189) (@lem5169188)). Qed.
Lemma lem5169191 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5169192 (l : real) : (term264 l) = (term285 l).
Proof. exact (MK_COMB (@lem5169190) (@lem5169191 l)). Qed.
Lemma lem5169193 (l : real) : (term263 l) = (term285 l).
Proof. exact (TRANS (@lem5169090 l) (@lem5169192 l)). Qed.
Lemma lem5169194 (l : real) : (term285 l) = term32.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5169195 (l : real) : (term263 l) = term32.
Proof. exact (TRANS (@lem5169193 l) (@lem5169194 l)). Qed.
Lemma lem5169196 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5169197 (l : real) : (term286 l) = term206.
Proof. exact (MK_COMB (@lem5169196) (@lem5169195 l)). Qed.
Lemma lem5169198 (x : real) : (term289 x) = (term264 x).
Proof. exact (@lem1982715 term51 x). Qed.
Lemma lem5169200 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5169201 : term91 = term101.
Proof. exact (@lem5169200 term85). Qed.
Lemma lem5169203 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5169204 : term51 = term84.
Proof. exact (@lem5169203 term85). Qed.
Lemma lem5169205 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5169206 : term265 = term266.
Proof. exact (MK_COMB (@lem5169205) (@lem5169204)). Qed.
Lemma lem5169207 : term267 = term268.
Proof. exact (MK_COMB (@lem5169206) (@lem5169201)). Qed.
Lemma lem5169208 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5169210 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169211 : term232 = term238.
Proof. exact (@lem5169210 (NUMERAL 0) term85). Qed.
Lemma lem5169212 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169213 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169214 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169213 h1) (fun h1 : term238 = True => @lem5169212)). Qed.
Lemma lem5169215 : term238 = True.
Proof. exact (EQ_MP (@lem5169214) (@lem5169212)). Qed.
Lemma lem5169216 : term232 = True.
Proof. exact (TRANS (@lem5169211) (@lem5169215)). Qed.
Lemma lem5169217 : True = term232.
Proof. exact (SYM (@lem5169216)). Qed.
Lemma lem5169218 : term232.
Proof. exact (EQ_MP (@lem5169217) (@lem0)). Qed.
Lemma lem5169219 : term270.
Proof. exact (@lem5169208 (@lem5169218)). Qed.
Lemma lem5169221 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169222 : term232 = term238.
Proof. exact (@lem5169221 (NUMERAL 0) term85). Qed.
Lemma lem5169223 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169224 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169225 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169224 h1) (fun h1 : term238 = True => @lem5169223)). Qed.
Lemma lem5169226 : term238 = True.
Proof. exact (EQ_MP (@lem5169225) (@lem5169223)). Qed.
Lemma lem5169227 : term232 = True.
Proof. exact (TRANS (@lem5169222) (@lem5169226)). Qed.
Lemma lem5169228 : True = term232.
Proof. exact (SYM (@lem5169227)). Qed.
Lemma lem5169229 : term232.
Proof. exact (EQ_MP (@lem5169228) (@lem0)). Qed.
Lemma lem5169230 : term271.
Proof. exact (@lem5169219 (@lem5169229)). Qed.
Lemma lem5169232 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169233 : term232 = term238.
Proof. exact (@lem5169232 (NUMERAL 0) term85). Qed.
Lemma lem5169234 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169235 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169236 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169235 h1) (fun h1 : term238 = True => @lem5169234)). Qed.
Lemma lem5169237 : term238 = True.
Proof. exact (EQ_MP (@lem5169236) (@lem5169234)). Qed.
Lemma lem5169238 : term232 = True.
Proof. exact (TRANS (@lem5169233) (@lem5169237)). Qed.
Lemma lem5169239 : True = term232.
Proof. exact (SYM (@lem5169238)). Qed.
Lemma lem5169240 : term232.
Proof. exact (EQ_MP (@lem5169239) (@lem0)). Qed.
Lemma lem5169241 : term272.
Proof. exact (@lem5169230 (@lem5169240)). Qed.
Lemma lem5169243 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5169244 : term94 = term95.
Proof. exact (@lem5169243 term85 term85). Qed.
Lemma lem5169245 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169246 : term97 = term85.
Proof. exact (EQ_MP (@lem5169245) (@lem940073)). Qed.
Lemma lem5169247 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169248 : term95 = term91.
Proof. exact (MK_COMB (@lem5169247) (@lem5169246)). Qed.
Lemma lem5169249 : term94 = term91.
Proof. exact (TRANS (@lem5169244) (@lem5169248)). Qed.
Lemma lem5169251 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5169252 : term275 = term276.
Proof. exact (@lem5169251 term85 term85). Qed.
Lemma lem5169253 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169254 : term97 = term85.
Proof. exact (EQ_MP (@lem5169253) (@lem940073)). Qed.
Lemma lem5169255 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169256 : term95 = term91.
Proof. exact (MK_COMB (@lem5169255) (@lem5169254)). Qed.
Lemma lem5169257 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5169258 : term276 = term51.
Proof. exact (MK_COMB (@lem5169257) (@lem5169256)). Qed.
Lemma lem5169259 : term275 = term51.
Proof. exact (TRANS (@lem5169252) (@lem5169258)). Qed.
Lemma lem5169260 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5169261 : term277 = term265.
Proof. exact (MK_COMB (@lem5169260) (@lem5169259)). Qed.
Lemma lem5169262 : term278 = term267.
Proof. exact (MK_COMB (@lem5169261) (@lem5169249)). Qed.
Lemma lem5169264 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5169265 : term267 = term32.
Proof. exact (@lem5169264 term85). Qed.
Lemma lem5169266 : term278 = term32.
Proof. exact (TRANS (@lem5169262) (@lem5169265)). Qed.
Lemma lem5169267 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5169268 : term280 = term281.
Proof. exact (MK_COMB (@lem5169267) (@lem5169266)). Qed.
Lemma lem5169269 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5169270 : term282 = term243.
Proof. exact (MK_COMB (@lem5169268) (@lem5169269)). Qed.
Lemma lem5169272 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169273 : term243 = term32.
Proof. exact (@lem5169272 term85). Qed.
Lemma lem5169274 : term282 = term32.
Proof. exact (TRANS (@lem5169270) (@lem5169273)). Qed.
Lemma lem5169276 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5169277 : term94 = term95.
Proof. exact (@lem5169276 term85 term85). Qed.
Lemma lem5169278 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169279 : term97 = term85.
Proof. exact (EQ_MP (@lem5169278) (@lem940073)). Qed.
Lemma lem5169280 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169281 : term95 = term91.
Proof. exact (MK_COMB (@lem5169280) (@lem5169279)). Qed.
Lemma lem5169282 : term94 = term91.
Proof. exact (TRANS (@lem5169277) (@lem5169281)). Qed.
Lemma lem5169283 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5169284 : term283 = term243.
Proof. exact (MK_COMB (@lem5169283) (@lem5169282)). Qed.
Lemma lem5169286 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169287 : term243 = term32.
Proof. exact (@lem5169286 term85). Qed.
Lemma lem5169288 : term283 = term32.
Proof. exact (TRANS (@lem5169284) (@lem5169287)). Qed.
Lemma lem5169289 : term32 = term283.
Proof. exact (SYM (@lem5169288)). Qed.
Lemma lem5169290 : term282 = term283.
Proof. exact (TRANS (@lem5169274) (@lem5169289)). Qed.
Lemma lem5169291 : term268 = term172.
Proof. exact (@lem5169241 (@lem5169290)). Qed.
Lemma lem5169292 : term267 = term172.
Proof. exact (TRANS (@lem5169207) (@lem5169291)). Qed.
Lemma lem5169294 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5169295 : term172 = term32.
Proof. exact (@lem5169294 term32). Qed.
Lemma lem5169296 : term267 = term32.
Proof. exact (TRANS (@lem5169292) (@lem5169295)). Qed.
Lemma lem5169297 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5169298 : term284 = term281.
Proof. exact (MK_COMB (@lem5169297) (@lem5169296)). Qed.
Lemma lem5169299 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5169300 (x : real) : (term264 x) = (term285 x).
Proof. exact (MK_COMB (@lem5169298) (@lem5169299 x)). Qed.
Lemma lem5169301 (x : real) : (term289 x) = (term285 x).
Proof. exact (TRANS (@lem5169198 x) (@lem5169300 x)). Qed.
Lemma lem5169302 (x : real) : (term285 x) = term32.
Proof. exact (@lem1982719 x). Qed.
Lemma lem5169303 (x : real) : (term289 x) = term32.
Proof. exact (TRANS (@lem5169301 x) (@lem5169302 x)). Qed.
Lemma lem5169304 (l : real) (x : real) : (term317 l x) = term291.
Proof. exact (MK_COMB (@lem5169197 l) (@lem5169303 x)). Qed.
Lemma lem5169305 (l : real) (x : real) : (term316 l x) = term291.
Proof. exact (TRANS (@lem5169089 l x) (@lem5169304 l x)). Qed.
Lemma lem5169306 : term291 = term32.
Proof. exact (@lem1982721 term32). Qed.
Lemma lem5169307 (l : real) (x : real) : (term316 l x) = term32.
Proof. exact (TRANS (@lem5169305 l x) (@lem5169306)). Qed.
Lemma lem5169308 (e : real) (l : real) (x : real) : (term315 e l x) = term291.
Proof. exact (MK_COMB (@lem5169088 e) (@lem5169307 l x)). Qed.
Lemma lem5169309 (e : real) (l : real) (x : real) : (term314 e l x) = term291.
Proof. exact (TRANS (@lem5168980 e l x) (@lem5169308 e l x)). Qed.
Lemma lem5169310 : term291 = term32.
Proof. exact (@lem1982721 term32). Qed.
Lemma lem5169311 (e : real) (l : real) (x : real) : (term314 e l x) = term32.
Proof. exact (TRANS (@lem5169309 e l x) (@lem5169310)). Qed.
Lemma lem5169312 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5169313 (e : real) (l : real) (x : real) : (term318 e l x) = term293.
Proof. exact (MK_COMB (@lem5169312) (@lem5169311 e l x)). Qed.
Lemma lem5169314 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5169315 (e : real) (l : real) (x : real) : (term313 e l x) = term294.
Proof. exact (MK_COMB (@lem5169313 e l x) (@lem5169314)). Qed.
Lemma lem5169316 (e : real) (l : real) (x : real) (h1 : term162 e l x) : term294.
Proof. exact (EQ_MP (@lem5169315 e l x) (@lem5168979 e l x h1)). Qed.
Lemma lem5169318 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5169319 : term294 = term295.
Proof. exact (@lem5169318 term32 term32). Qed.
Lemma lem5169321 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5169322 : term32 = term172.
Proof. exact (@lem5169321 (NUMERAL 0)). Qed.
Lemma lem5169324 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5169325 : term32 = term172.
Proof. exact (@lem5169324 (NUMERAL 0)). Qed.
Lemma lem5169326 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5169327 : term233 = term234.
Proof. exact (MK_COMB (@lem5169326) (@lem5169325)). Qed.
Lemma lem5169328 : term295 = term296.
Proof. exact (MK_COMB (@lem5169327) (@lem5169322)). Qed.
Lemma lem5169329 : term297.
Proof. exact (@lem1980255 term32 term91 term32 term91). Qed.
Lemma lem5169331 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169332 : term232 = term238.
Proof. exact (@lem5169331 (NUMERAL 0) term85). Qed.
Lemma lem5169333 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169334 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169335 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169334 h1) (fun h1 : term238 = True => @lem5169333)). Qed.
Lemma lem5169336 : term238 = True.
Proof. exact (EQ_MP (@lem5169335) (@lem5169333)). Qed.
Lemma lem5169337 : term232 = True.
Proof. exact (TRANS (@lem5169332) (@lem5169336)). Qed.
Lemma lem5169338 : True = term232.
Proof. exact (SYM (@lem5169337)). Qed.
Lemma lem5169339 : term232.
Proof. exact (EQ_MP (@lem5169338) (@lem0)). Qed.
Lemma lem5169340 : term298.
Proof. exact (@lem5169329 (@lem5169339)). Qed.
Lemma lem5169342 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169343 : term232 = term238.
Proof. exact (@lem5169342 (NUMERAL 0) term85). Qed.
Lemma lem5169344 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169345 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169346 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169345 h1) (fun h1 : term238 = True => @lem5169344)). Qed.
Lemma lem5169347 : term238 = True.
Proof. exact (EQ_MP (@lem5169346) (@lem5169344)). Qed.
Lemma lem5169348 : term232 = True.
Proof. exact (TRANS (@lem5169343) (@lem5169347)). Qed.
Lemma lem5169349 : True = term232.
Proof. exact (SYM (@lem5169348)). Qed.
Lemma lem5169350 : term232.
Proof. exact (EQ_MP (@lem5169349) (@lem0)). Qed.
Lemma lem5169351 : term296 = term299.
Proof. exact (@lem5169340 (@lem5169350)). Qed.
Lemma lem5169353 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169354 : term243 = term32.
Proof. exact (@lem5169353 term85). Qed.
Lemma lem5169356 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169357 : term243 = term32.
Proof. exact (@lem5169356 term85). Qed.
Lemma lem5169358 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5169359 : term244 = term233.
Proof. exact (MK_COMB (@lem5169358) (@lem5169357)). Qed.
Lemma lem5169360 : term299 = term295.
Proof. exact (MK_COMB (@lem5169359) (@lem5169354)). Qed.
Lemma lem5169362 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169363 : term295 = term300.
Proof. exact (@lem5169362 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5169364 : term300 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5169365 : term295 = False.
Proof. exact (TRANS (@lem5169363) (@lem5169364)). Qed.
Lemma lem5169366 : term299 = False.
Proof. exact (TRANS (@lem5169360) (@lem5169365)). Qed.
Lemma lem5169367 : term296 = False.
Proof. exact (TRANS (@lem5169351) (@lem5169366)). Qed.
Lemma lem5169368 : term295 = False.
Proof. exact (TRANS (@lem5169328) (@lem5169367)). Qed.
Lemma lem5169369 : term294 = False.
Proof. exact (TRANS (@lem5169319) (@lem5169368)). Qed.
Lemma lem5169370 (e : real) (l : real) (x : real) (h1 : term162 e l x) : False.
Proof. exact (EQ_MP (@lem5169369) (@lem5169316 e l x h1)). Qed.
Lemma lem5169371 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term227 e l x.
Proof. exact (h1). Qed.
Lemma lem5169372 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term225 e l x.
Proof. exact (proj2 (@lem5169371 e l x h1)). Qed.
Lemma lem5169374 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term121 e l x.
Proof. exact (proj2 (@lem5169372 e l x h1)). Qed.
Lemma lem5169375 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term44 e l x.
Proof. exact (proj1 (@lem5169372 e l x h1)). Qed.
Lemma lem5169377 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term111 e l x.
Proof. exact (proj1 (@lem5169374 e l x h1)). Qed.
Lemma lem5169379 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5169380 : term231 = term232.
Proof. exact (@lem5169379 term32 term91). Qed.
Lemma lem5169382 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5169383 : term91 = term101.
Proof. exact (@lem5169382 term85). Qed.
Lemma lem5169385 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5169386 : term32 = term172.
Proof. exact (@lem5169385 (NUMERAL 0)). Qed.
Lemma lem5169387 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5169388 : term233 = term234.
Proof. exact (MK_COMB (@lem5169387) (@lem5169386)). Qed.
Lemma lem5169389 : term232 = term235.
Proof. exact (MK_COMB (@lem5169388) (@lem5169383)). Qed.
Lemma lem5169390 : term236.
Proof. exact (@lem1980255 term32 term91 term91 term91). Qed.
Lemma lem5169392 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169393 : term232 = term238.
Proof. exact (@lem5169392 (NUMERAL 0) term85). Qed.
Lemma lem5169394 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169395 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169396 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169395 h1) (fun h1 : term238 = True => @lem5169394)). Qed.
Lemma lem5169397 : term238 = True.
Proof. exact (EQ_MP (@lem5169396) (@lem5169394)). Qed.
Lemma lem5169398 : term232 = True.
Proof. exact (TRANS (@lem5169393) (@lem5169397)). Qed.
Lemma lem5169399 : True = term232.
Proof. exact (SYM (@lem5169398)). Qed.
Lemma lem5169400 : term232.
Proof. exact (EQ_MP (@lem5169399) (@lem0)). Qed.
Lemma lem5169401 : term240.
Proof. exact (@lem5169390 (@lem5169400)). Qed.
Lemma lem5169403 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169404 : term232 = term238.
Proof. exact (@lem5169403 (NUMERAL 0) term85). Qed.
Lemma lem5169405 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169406 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169407 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169406 h1) (fun h1 : term238 = True => @lem5169405)). Qed.
Lemma lem5169408 : term238 = True.
Proof. exact (EQ_MP (@lem5169407) (@lem5169405)). Qed.
Lemma lem5169409 : term232 = True.
Proof. exact (TRANS (@lem5169404) (@lem5169408)). Qed.
Lemma lem5169410 : True = term232.
Proof. exact (SYM (@lem5169409)). Qed.
Lemma lem5169411 : term232.
Proof. exact (EQ_MP (@lem5169410) (@lem0)). Qed.
Lemma lem5169412 : term235 = term241.
Proof. exact (@lem5169401 (@lem5169411)). Qed.
Lemma lem5169414 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5169415 : term94 = term95.
Proof. exact (@lem5169414 term85 term85). Qed.
Lemma lem5169416 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169417 : term97 = term85.
Proof. exact (EQ_MP (@lem5169416) (@lem940073)). Qed.
Lemma lem5169418 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169419 : term95 = term91.
Proof. exact (MK_COMB (@lem5169418) (@lem5169417)). Qed.
Lemma lem5169420 : term94 = term91.
Proof. exact (TRANS (@lem5169415) (@lem5169419)). Qed.
Lemma lem5169422 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169423 : term243 = term32.
Proof. exact (@lem5169422 term85). Qed.
Lemma lem5169424 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5169425 : term244 = term233.
Proof. exact (MK_COMB (@lem5169424) (@lem5169423)). Qed.
Lemma lem5169426 : term241 = term232.
Proof. exact (MK_COMB (@lem5169425) (@lem5169420)). Qed.
Lemma lem5169428 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169429 : term232 = term238.
Proof. exact (@lem5169428 (NUMERAL 0) term85). Qed.
Lemma lem5169430 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169431 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169432 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169431 h1) (fun h1 : term238 = True => @lem5169430)). Qed.
Lemma lem5169433 : term238 = True.
Proof. exact (EQ_MP (@lem5169432) (@lem5169430)). Qed.
Lemma lem5169434 : term232 = True.
Proof. exact (TRANS (@lem5169429) (@lem5169433)). Qed.
Lemma lem5169435 : term241 = True.
Proof. exact (TRANS (@lem5169426) (@lem5169434)). Qed.
Lemma lem5169436 : term235 = True.
Proof. exact (TRANS (@lem5169412) (@lem5169435)). Qed.
Lemma lem5169437 : term232 = True.
Proof. exact (TRANS (@lem5169389) (@lem5169436)). Qed.
Lemma lem5169438 : term231 = True.
Proof. exact (TRANS (@lem5169380) (@lem5169437)). Qed.
Lemma lem5169439 : True = term231.
Proof. exact (SYM (@lem5169438)). Qed.
Lemma lem5169440 : term231.
Proof. exact (EQ_MP (@lem5169439) (@lem0)). Qed.
Lemma lem5169441 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term245 e l x.
Proof. exact (conj (@lem5169440) (@lem5169377 e l x h1)). Qed.
Lemma lem5169443 (x : real) (y : real) : term246 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5169444 (e : real) (l : real) (x : real) : term247 e l x.
Proof. exact (@lem5169443 term91 (term108 e l x)). Qed.
Lemma lem5169445 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term248 e l x.
Proof. exact (@lem5169444 e l x (@lem5169441 e l x h1)). Qed.
Lemma lem5169446 (e : real) (l : real) (x : real) : (term249 e l x) = (term108 e l x).
Proof. exact (@lem1982733 (term108 e l x)). Qed.
Lemma lem5169447 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5169448 (e : real) (l : real) (x : real) : (term250 e l x) = (term110 e l x).
Proof. exact (MK_COMB (@lem5169447) (@lem5169446 e l x)). Qed.
Lemma lem5169449 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5169450 (e : real) (l : real) (x : real) : (term248 e l x) = (term111 e l x).
Proof. exact (MK_COMB (@lem5169448 e l x) (@lem5169449)). Qed.
Lemma lem5169451 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term111 e l x.
Proof. exact (EQ_MP (@lem5169450 e l x) (@lem5169445 e l x h1)). Qed.
Lemma lem5169453 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5169454 : term231 = term232.
Proof. exact (@lem5169453 term32 term91). Qed.
Lemma lem5169456 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5169457 : term91 = term101.
Proof. exact (@lem5169456 term85). Qed.
Lemma lem5169459 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5169460 : term32 = term172.
Proof. exact (@lem5169459 (NUMERAL 0)). Qed.
Lemma lem5169461 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5169462 : term233 = term234.
Proof. exact (MK_COMB (@lem5169461) (@lem5169460)). Qed.
Lemma lem5169463 : term232 = term235.
Proof. exact (MK_COMB (@lem5169462) (@lem5169457)). Qed.
Lemma lem5169464 : term236.
Proof. exact (@lem1980255 term32 term91 term91 term91). Qed.
Lemma lem5169466 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169467 : term232 = term238.
Proof. exact (@lem5169466 (NUMERAL 0) term85). Qed.
Lemma lem5169468 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169469 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169470 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169469 h1) (fun h1 : term238 = True => @lem5169468)). Qed.
Lemma lem5169471 : term238 = True.
Proof. exact (EQ_MP (@lem5169470) (@lem5169468)). Qed.
Lemma lem5169472 : term232 = True.
Proof. exact (TRANS (@lem5169467) (@lem5169471)). Qed.
Lemma lem5169473 : True = term232.
Proof. exact (SYM (@lem5169472)). Qed.
Lemma lem5169474 : term232.
Proof. exact (EQ_MP (@lem5169473) (@lem0)). Qed.
Lemma lem5169475 : term240.
Proof. exact (@lem5169464 (@lem5169474)). Qed.
Lemma lem5169477 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169478 : term232 = term238.
Proof. exact (@lem5169477 (NUMERAL 0) term85). Qed.
Lemma lem5169479 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169480 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169481 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169480 h1) (fun h1 : term238 = True => @lem5169479)). Qed.
Lemma lem5169482 : term238 = True.
Proof. exact (EQ_MP (@lem5169481) (@lem5169479)). Qed.
Lemma lem5169483 : term232 = True.
Proof. exact (TRANS (@lem5169478) (@lem5169482)). Qed.
Lemma lem5169484 : True = term232.
Proof. exact (SYM (@lem5169483)). Qed.
Lemma lem5169485 : term232.
Proof. exact (EQ_MP (@lem5169484) (@lem0)). Qed.
Lemma lem5169486 : term235 = term241.
Proof. exact (@lem5169475 (@lem5169485)). Qed.
Lemma lem5169488 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5169489 : term94 = term95.
Proof. exact (@lem5169488 term85 term85). Qed.
Lemma lem5169490 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169491 : term97 = term85.
Proof. exact (EQ_MP (@lem5169490) (@lem940073)). Qed.
Lemma lem5169492 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169493 : term95 = term91.
Proof. exact (MK_COMB (@lem5169492) (@lem5169491)). Qed.
Lemma lem5169494 : term94 = term91.
Proof. exact (TRANS (@lem5169489) (@lem5169493)). Qed.
Lemma lem5169496 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169497 : term243 = term32.
Proof. exact (@lem5169496 term85). Qed.
Lemma lem5169498 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5169499 : term244 = term233.
Proof. exact (MK_COMB (@lem5169498) (@lem5169497)). Qed.
Lemma lem5169500 : term241 = term232.
Proof. exact (MK_COMB (@lem5169499) (@lem5169494)). Qed.
Lemma lem5169502 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169503 : term232 = term238.
Proof. exact (@lem5169502 (NUMERAL 0) term85). Qed.
Lemma lem5169504 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169505 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169506 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169505 h1) (fun h1 : term238 = True => @lem5169504)). Qed.
Lemma lem5169507 : term238 = True.
Proof. exact (EQ_MP (@lem5169506) (@lem5169504)). Qed.
Lemma lem5169508 : term232 = True.
Proof. exact (TRANS (@lem5169503) (@lem5169507)). Qed.
Lemma lem5169509 : term241 = True.
Proof. exact (TRANS (@lem5169500) (@lem5169508)). Qed.
Lemma lem5169510 : term235 = True.
Proof. exact (TRANS (@lem5169486) (@lem5169509)). Qed.
Lemma lem5169511 : term232 = True.
Proof. exact (TRANS (@lem5169463) (@lem5169510)). Qed.
Lemma lem5169512 : term231 = True.
Proof. exact (TRANS (@lem5169454) (@lem5169511)). Qed.
Lemma lem5169513 : True = term231.
Proof. exact (SYM (@lem5169512)). Qed.
Lemma lem5169514 : term231.
Proof. exact (EQ_MP (@lem5169513) (@lem0)). Qed.
Lemma lem5169515 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term251 e l x.
Proof. exact (conj (@lem5169514) (@lem5169375 e l x h1)). Qed.
Lemma lem5169517 (x : real) (y : real) : term252 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem5169518 (e : real) (l : real) (x : real) : term253 e l x.
Proof. exact (@lem5169517 term91 (term41 e l x)). Qed.
Lemma lem5169519 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term254 e l x.
Proof. exact (@lem5169518 e l x (@lem5169515 e l x h1)). Qed.
Lemma lem5169520 (e : real) (l : real) (x : real) : (term255 e l x) = (term41 e l x).
Proof. exact (@lem1982733 (term41 e l x)). Qed.
Lemma lem5169521 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5169522 (e : real) (l : real) (x : real) : (term256 e l x) = (term43 e l x).
Proof. exact (MK_COMB (@lem5169521) (@lem5169520 e l x)). Qed.
Lemma lem5169523 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5169524 (e : real) (l : real) (x : real) : (term254 e l x) = (term44 e l x).
Proof. exact (MK_COMB (@lem5169522 e l x) (@lem5169523)). Qed.
Lemma lem5169525 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term44 e l x.
Proof. exact (EQ_MP (@lem5169524 e l x) (@lem5169519 e l x h1)). Qed.
Lemma lem5169526 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term257 e l x.
Proof. exact (conj (@lem5169525 e l x h1) (@lem5169451 e l x h1)). Qed.
Lemma lem5169528 (x : real) (y : real) : term258 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem5169529 (e : real) (l : real) (x : real) : term259 e l x.
Proof. exact (@lem5169528 (term41 e l x) (term108 e l x)). Qed.
Lemma lem5169530 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term260 e l x.
Proof. exact (@lem5169529 e l x (@lem5169526 e l x h1)). Qed.
Lemma lem5169531 (e : real) (l : real) (x : real) : (term261 e l x) = (term262 e l x).
Proof. exact (@lem1982753 (term25 e) e (term23 l x) (term24 l x)). Qed.
Lemma lem5169532 (e : real) : (term263 e) = (term264 e).
Proof. exact (@lem1982713 term51 e). Qed.
Lemma lem5169534 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5169535 : term91 = term101.
Proof. exact (@lem5169534 term85). Qed.
Lemma lem5169537 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5169538 : term51 = term84.
Proof. exact (@lem5169537 term85). Qed.
Lemma lem5169539 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5169540 : term265 = term266.
Proof. exact (MK_COMB (@lem5169539) (@lem5169538)). Qed.
Lemma lem5169541 : term267 = term268.
Proof. exact (MK_COMB (@lem5169540) (@lem5169535)). Qed.
Lemma lem5169542 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5169544 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169545 : term232 = term238.
Proof. exact (@lem5169544 (NUMERAL 0) term85). Qed.
Lemma lem5169546 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169547 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169548 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169547 h1) (fun h1 : term238 = True => @lem5169546)). Qed.
Lemma lem5169549 : term238 = True.
Proof. exact (EQ_MP (@lem5169548) (@lem5169546)). Qed.
Lemma lem5169550 : term232 = True.
Proof. exact (TRANS (@lem5169545) (@lem5169549)). Qed.
Lemma lem5169551 : True = term232.
Proof. exact (SYM (@lem5169550)). Qed.
Lemma lem5169552 : term232.
Proof. exact (EQ_MP (@lem5169551) (@lem0)). Qed.
Lemma lem5169553 : term270.
Proof. exact (@lem5169542 (@lem5169552)). Qed.
Lemma lem5169555 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169556 : term232 = term238.
Proof. exact (@lem5169555 (NUMERAL 0) term85). Qed.
Lemma lem5169557 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169558 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169559 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169558 h1) (fun h1 : term238 = True => @lem5169557)). Qed.
Lemma lem5169560 : term238 = True.
Proof. exact (EQ_MP (@lem5169559) (@lem5169557)). Qed.
Lemma lem5169561 : term232 = True.
Proof. exact (TRANS (@lem5169556) (@lem5169560)). Qed.
Lemma lem5169562 : True = term232.
Proof. exact (SYM (@lem5169561)). Qed.
Lemma lem5169563 : term232.
Proof. exact (EQ_MP (@lem5169562) (@lem0)). Qed.
Lemma lem5169564 : term271.
Proof. exact (@lem5169553 (@lem5169563)). Qed.
Lemma lem5169566 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169567 : term232 = term238.
Proof. exact (@lem5169566 (NUMERAL 0) term85). Qed.
Lemma lem5169568 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169569 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169570 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169569 h1) (fun h1 : term238 = True => @lem5169568)). Qed.
Lemma lem5169571 : term238 = True.
Proof. exact (EQ_MP (@lem5169570) (@lem5169568)). Qed.
Lemma lem5169572 : term232 = True.
Proof. exact (TRANS (@lem5169567) (@lem5169571)). Qed.
Lemma lem5169573 : True = term232.
Proof. exact (SYM (@lem5169572)). Qed.
Lemma lem5169574 : term232.
Proof. exact (EQ_MP (@lem5169573) (@lem0)). Qed.
Lemma lem5169575 : term272.
Proof. exact (@lem5169564 (@lem5169574)). Qed.
Lemma lem5169577 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5169578 : term94 = term95.
Proof. exact (@lem5169577 term85 term85). Qed.
Lemma lem5169579 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169580 : term97 = term85.
Proof. exact (EQ_MP (@lem5169579) (@lem940073)). Qed.
Lemma lem5169581 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169582 : term95 = term91.
Proof. exact (MK_COMB (@lem5169581) (@lem5169580)). Qed.
Lemma lem5169583 : term94 = term91.
Proof. exact (TRANS (@lem5169578) (@lem5169582)). Qed.
Lemma lem5169585 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5169586 : term275 = term276.
Proof. exact (@lem5169585 term85 term85). Qed.
Lemma lem5169587 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169588 : term97 = term85.
Proof. exact (EQ_MP (@lem5169587) (@lem940073)). Qed.
Lemma lem5169589 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169590 : term95 = term91.
Proof. exact (MK_COMB (@lem5169589) (@lem5169588)). Qed.
Lemma lem5169591 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5169592 : term276 = term51.
Proof. exact (MK_COMB (@lem5169591) (@lem5169590)). Qed.
Lemma lem5169593 : term275 = term51.
Proof. exact (TRANS (@lem5169586) (@lem5169592)). Qed.
Lemma lem5169594 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5169595 : term277 = term265.
Proof. exact (MK_COMB (@lem5169594) (@lem5169593)). Qed.
Lemma lem5169596 : term278 = term267.
Proof. exact (MK_COMB (@lem5169595) (@lem5169583)). Qed.
Lemma lem5169598 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5169599 : term267 = term32.
Proof. exact (@lem5169598 term85). Qed.
Lemma lem5169600 : term278 = term32.
Proof. exact (TRANS (@lem5169596) (@lem5169599)). Qed.
Lemma lem5169601 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5169602 : term280 = term281.
Proof. exact (MK_COMB (@lem5169601) (@lem5169600)). Qed.
Lemma lem5169603 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5169604 : term282 = term243.
Proof. exact (MK_COMB (@lem5169602) (@lem5169603)). Qed.
Lemma lem5169606 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169607 : term243 = term32.
Proof. exact (@lem5169606 term85). Qed.
Lemma lem5169608 : term282 = term32.
Proof. exact (TRANS (@lem5169604) (@lem5169607)). Qed.
Lemma lem5169610 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5169611 : term94 = term95.
Proof. exact (@lem5169610 term85 term85). Qed.
Lemma lem5169612 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169613 : term97 = term85.
Proof. exact (EQ_MP (@lem5169612) (@lem940073)). Qed.
Lemma lem5169614 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169615 : term95 = term91.
Proof. exact (MK_COMB (@lem5169614) (@lem5169613)). Qed.
Lemma lem5169616 : term94 = term91.
Proof. exact (TRANS (@lem5169611) (@lem5169615)). Qed.
Lemma lem5169617 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5169618 : term283 = term243.
Proof. exact (MK_COMB (@lem5169617) (@lem5169616)). Qed.
Lemma lem5169620 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169621 : term243 = term32.
Proof. exact (@lem5169620 term85). Qed.
Lemma lem5169622 : term283 = term32.
Proof. exact (TRANS (@lem5169618) (@lem5169621)). Qed.
Lemma lem5169623 : term32 = term283.
Proof. exact (SYM (@lem5169622)). Qed.
Lemma lem5169624 : term282 = term283.
Proof. exact (TRANS (@lem5169608) (@lem5169623)). Qed.
Lemma lem5169625 : term268 = term172.
Proof. exact (@lem5169575 (@lem5169624)). Qed.
Lemma lem5169626 : term267 = term172.
Proof. exact (TRANS (@lem5169541) (@lem5169625)). Qed.
Lemma lem5169628 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5169629 : term172 = term32.
Proof. exact (@lem5169628 term32). Qed.
Lemma lem5169630 : term267 = term32.
Proof. exact (TRANS (@lem5169626) (@lem5169629)). Qed.
Lemma lem5169631 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5169632 : term284 = term281.
Proof. exact (MK_COMB (@lem5169631) (@lem5169630)). Qed.
Lemma lem5169633 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem5169634 (e : real) : (term264 e) = (term285 e).
Proof. exact (MK_COMB (@lem5169632) (@lem5169633 e)). Qed.
Lemma lem5169635 (e : real) : (term263 e) = (term285 e).
Proof. exact (TRANS (@lem5169532 e) (@lem5169634 e)). Qed.
Lemma lem5169636 (e : real) : (term285 e) = term32.
Proof. exact (@lem1982719 e). Qed.
Lemma lem5169637 (e : real) : (term263 e) = term32.
Proof. exact (TRANS (@lem5169635 e) (@lem5169636 e)). Qed.
Lemma lem5169638 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5169639 (e : real) : (term286 e) = term206.
Proof. exact (MK_COMB (@lem5169638) (@lem5169637 e)). Qed.
Lemma lem5169640 (l : real) (x : real) : (term287 l x) = (term288 l x).
Proof. exact (@lem1982753 l (term25 l) (term25 x) x). Qed.
Lemma lem5169641 (l : real) : (term289 l) = (term264 l).
Proof. exact (@lem1982715 term51 l). Qed.
Lemma lem5169643 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5169644 : term91 = term101.
Proof. exact (@lem5169643 term85). Qed.
Lemma lem5169646 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5169647 : term51 = term84.
Proof. exact (@lem5169646 term85). Qed.
Lemma lem5169648 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5169649 : term265 = term266.
Proof. exact (MK_COMB (@lem5169648) (@lem5169647)). Qed.
Lemma lem5169650 : term267 = term268.
Proof. exact (MK_COMB (@lem5169649) (@lem5169644)). Qed.
Lemma lem5169651 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5169653 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169654 : term232 = term238.
Proof. exact (@lem5169653 (NUMERAL 0) term85). Qed.
Lemma lem5169655 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169656 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169657 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169656 h1) (fun h1 : term238 = True => @lem5169655)). Qed.
Lemma lem5169658 : term238 = True.
Proof. exact (EQ_MP (@lem5169657) (@lem5169655)). Qed.
Lemma lem5169659 : term232 = True.
Proof. exact (TRANS (@lem5169654) (@lem5169658)). Qed.
Lemma lem5169660 : True = term232.
Proof. exact (SYM (@lem5169659)). Qed.
Lemma lem5169661 : term232.
Proof. exact (EQ_MP (@lem5169660) (@lem0)). Qed.
Lemma lem5169662 : term270.
Proof. exact (@lem5169651 (@lem5169661)). Qed.
Lemma lem5169664 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169665 : term232 = term238.
Proof. exact (@lem5169664 (NUMERAL 0) term85). Qed.
Lemma lem5169666 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169667 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169668 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169667 h1) (fun h1 : term238 = True => @lem5169666)). Qed.
Lemma lem5169669 : term238 = True.
Proof. exact (EQ_MP (@lem5169668) (@lem5169666)). Qed.
Lemma lem5169670 : term232 = True.
Proof. exact (TRANS (@lem5169665) (@lem5169669)). Qed.
Lemma lem5169671 : True = term232.
Proof. exact (SYM (@lem5169670)). Qed.
Lemma lem5169672 : term232.
Proof. exact (EQ_MP (@lem5169671) (@lem0)). Qed.
Lemma lem5169673 : term271.
Proof. exact (@lem5169662 (@lem5169672)). Qed.
Lemma lem5169675 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169676 : term232 = term238.
Proof. exact (@lem5169675 (NUMERAL 0) term85). Qed.
Lemma lem5169677 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169678 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169679 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169678 h1) (fun h1 : term238 = True => @lem5169677)). Qed.
Lemma lem5169680 : term238 = True.
Proof. exact (EQ_MP (@lem5169679) (@lem5169677)). Qed.
Lemma lem5169681 : term232 = True.
Proof. exact (TRANS (@lem5169676) (@lem5169680)). Qed.
Lemma lem5169682 : True = term232.
Proof. exact (SYM (@lem5169681)). Qed.
Lemma lem5169683 : term232.
Proof. exact (EQ_MP (@lem5169682) (@lem0)). Qed.
Lemma lem5169684 : term272.
Proof. exact (@lem5169673 (@lem5169683)). Qed.
Lemma lem5169686 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5169687 : term94 = term95.
Proof. exact (@lem5169686 term85 term85). Qed.
Lemma lem5169688 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169689 : term97 = term85.
Proof. exact (EQ_MP (@lem5169688) (@lem940073)). Qed.
Lemma lem5169690 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169691 : term95 = term91.
Proof. exact (MK_COMB (@lem5169690) (@lem5169689)). Qed.
Lemma lem5169692 : term94 = term91.
Proof. exact (TRANS (@lem5169687) (@lem5169691)). Qed.
Lemma lem5169694 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5169695 : term275 = term276.
Proof. exact (@lem5169694 term85 term85). Qed.
Lemma lem5169696 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169697 : term97 = term85.
Proof. exact (EQ_MP (@lem5169696) (@lem940073)). Qed.
Lemma lem5169698 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169699 : term95 = term91.
Proof. exact (MK_COMB (@lem5169698) (@lem5169697)). Qed.
Lemma lem5169700 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5169701 : term276 = term51.
Proof. exact (MK_COMB (@lem5169700) (@lem5169699)). Qed.
Lemma lem5169702 : term275 = term51.
Proof. exact (TRANS (@lem5169695) (@lem5169701)). Qed.
Lemma lem5169703 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5169704 : term277 = term265.
Proof. exact (MK_COMB (@lem5169703) (@lem5169702)). Qed.
Lemma lem5169705 : term278 = term267.
Proof. exact (MK_COMB (@lem5169704) (@lem5169692)). Qed.
Lemma lem5169707 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5169708 : term267 = term32.
Proof. exact (@lem5169707 term85). Qed.
Lemma lem5169709 : term278 = term32.
Proof. exact (TRANS (@lem5169705) (@lem5169708)). Qed.
Lemma lem5169710 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5169711 : term280 = term281.
Proof. exact (MK_COMB (@lem5169710) (@lem5169709)). Qed.
Lemma lem5169712 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5169713 : term282 = term243.
Proof. exact (MK_COMB (@lem5169711) (@lem5169712)). Qed.
Lemma lem5169715 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169716 : term243 = term32.
Proof. exact (@lem5169715 term85). Qed.
Lemma lem5169717 : term282 = term32.
Proof. exact (TRANS (@lem5169713) (@lem5169716)). Qed.
Lemma lem5169719 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5169720 : term94 = term95.
Proof. exact (@lem5169719 term85 term85). Qed.
Lemma lem5169721 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169722 : term97 = term85.
Proof. exact (EQ_MP (@lem5169721) (@lem940073)). Qed.
Lemma lem5169723 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169724 : term95 = term91.
Proof. exact (MK_COMB (@lem5169723) (@lem5169722)). Qed.
Lemma lem5169725 : term94 = term91.
Proof. exact (TRANS (@lem5169720) (@lem5169724)). Qed.
Lemma lem5169726 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5169727 : term283 = term243.
Proof. exact (MK_COMB (@lem5169726) (@lem5169725)). Qed.
Lemma lem5169729 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169730 : term243 = term32.
Proof. exact (@lem5169729 term85). Qed.
Lemma lem5169731 : term283 = term32.
Proof. exact (TRANS (@lem5169727) (@lem5169730)). Qed.
Lemma lem5169732 : term32 = term283.
Proof. exact (SYM (@lem5169731)). Qed.
Lemma lem5169733 : term282 = term283.
Proof. exact (TRANS (@lem5169717) (@lem5169732)). Qed.
Lemma lem5169734 : term268 = term172.
Proof. exact (@lem5169684 (@lem5169733)). Qed.
Lemma lem5169735 : term267 = term172.
Proof. exact (TRANS (@lem5169650) (@lem5169734)). Qed.
Lemma lem5169737 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5169738 : term172 = term32.
Proof. exact (@lem5169737 term32). Qed.
Lemma lem5169739 : term267 = term32.
Proof. exact (TRANS (@lem5169735) (@lem5169738)). Qed.
Lemma lem5169740 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5169741 : term284 = term281.
Proof. exact (MK_COMB (@lem5169740) (@lem5169739)). Qed.
Lemma lem5169742 (l : real) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem5169743 (l : real) : (term264 l) = (term285 l).
Proof. exact (MK_COMB (@lem5169741) (@lem5169742 l)). Qed.
Lemma lem5169744 (l : real) : (term289 l) = (term285 l).
Proof. exact (TRANS (@lem5169641 l) (@lem5169743 l)). Qed.
Lemma lem5169745 (l : real) : (term285 l) = term32.
Proof. exact (@lem1982719 l). Qed.
Lemma lem5169746 (l : real) : (term289 l) = term32.
Proof. exact (TRANS (@lem5169744 l) (@lem5169745 l)). Qed.
Lemma lem5169747 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5169748 (l : real) : (term290 l) = term206.
Proof. exact (MK_COMB (@lem5169747) (@lem5169746 l)). Qed.
Lemma lem5169749 (x : real) : (term263 x) = (term264 x).
Proof. exact (@lem1982713 term51 x). Qed.
Lemma lem5169751 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5169752 : term91 = term101.
Proof. exact (@lem5169751 term85). Qed.
Lemma lem5169754 (x : nat) : (term82 x) = (term83 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5169755 : term51 = term84.
Proof. exact (@lem5169754 term85). Qed.
Lemma lem5169756 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5169757 : term265 = term266.
Proof. exact (MK_COMB (@lem5169756) (@lem5169755)). Qed.
Lemma lem5169758 : term267 = term268.
Proof. exact (MK_COMB (@lem5169757) (@lem5169752)). Qed.
Lemma lem5169759 : term269.
Proof. exact (@lem1981473 term51 term91 term91 term91 term32 term91). Qed.
Lemma lem5169761 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169762 : term232 = term238.
Proof. exact (@lem5169761 (NUMERAL 0) term85). Qed.
Lemma lem5169763 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169764 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169765 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169764 h1) (fun h1 : term238 = True => @lem5169763)). Qed.
Lemma lem5169766 : term238 = True.
Proof. exact (EQ_MP (@lem5169765) (@lem5169763)). Qed.
Lemma lem5169767 : term232 = True.
Proof. exact (TRANS (@lem5169762) (@lem5169766)). Qed.
Lemma lem5169768 : True = term232.
Proof. exact (SYM (@lem5169767)). Qed.
Lemma lem5169769 : term232.
Proof. exact (EQ_MP (@lem5169768) (@lem0)). Qed.
Lemma lem5169770 : term270.
Proof. exact (@lem5169759 (@lem5169769)). Qed.
Lemma lem5169772 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169773 : term232 = term238.
Proof. exact (@lem5169772 (NUMERAL 0) term85). Qed.
Lemma lem5169774 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169775 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169776 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169775 h1) (fun h1 : term238 = True => @lem5169774)). Qed.
Lemma lem5169777 : term238 = True.
Proof. exact (EQ_MP (@lem5169776) (@lem5169774)). Qed.
Lemma lem5169778 : term232 = True.
Proof. exact (TRANS (@lem5169773) (@lem5169777)). Qed.
Lemma lem5169779 : True = term232.
Proof. exact (SYM (@lem5169778)). Qed.
Lemma lem5169780 : term232.
Proof. exact (EQ_MP (@lem5169779) (@lem0)). Qed.
Lemma lem5169781 : term271.
Proof. exact (@lem5169770 (@lem5169780)). Qed.
Lemma lem5169783 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169784 : term232 = term238.
Proof. exact (@lem5169783 (NUMERAL 0) term85). Qed.
Lemma lem5169785 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169786 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169787 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169786 h1) (fun h1 : term238 = True => @lem5169785)). Qed.
Lemma lem5169788 : term238 = True.
Proof. exact (EQ_MP (@lem5169787) (@lem5169785)). Qed.
Lemma lem5169789 : term232 = True.
Proof. exact (TRANS (@lem5169784) (@lem5169788)). Qed.
Lemma lem5169790 : True = term232.
Proof. exact (SYM (@lem5169789)). Qed.
Lemma lem5169791 : term232.
Proof. exact (EQ_MP (@lem5169790) (@lem0)). Qed.
Lemma lem5169792 : term272.
Proof. exact (@lem5169781 (@lem5169791)). Qed.
Lemma lem5169794 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5169795 : term94 = term95.
Proof. exact (@lem5169794 term85 term85). Qed.
Lemma lem5169796 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169797 : term97 = term85.
Proof. exact (EQ_MP (@lem5169796) (@lem940073)). Qed.
Lemma lem5169798 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169799 : term95 = term91.
Proof. exact (MK_COMB (@lem5169798) (@lem5169797)). Qed.
Lemma lem5169800 : term94 = term91.
Proof. exact (TRANS (@lem5169795) (@lem5169799)). Qed.
Lemma lem5169802 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5169803 : term275 = term276.
Proof. exact (@lem5169802 term85 term85). Qed.
Lemma lem5169804 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169805 : term97 = term85.
Proof. exact (EQ_MP (@lem5169804) (@lem940073)). Qed.
Lemma lem5169806 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169807 : term95 = term91.
Proof. exact (MK_COMB (@lem5169806) (@lem5169805)). Qed.
Lemma lem5169808 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5169809 : term276 = term51.
Proof. exact (MK_COMB (@lem5169808) (@lem5169807)). Qed.
Lemma lem5169810 : term275 = term51.
Proof. exact (TRANS (@lem5169803) (@lem5169809)). Qed.
Lemma lem5169811 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5169812 : term277 = term265.
Proof. exact (MK_COMB (@lem5169811) (@lem5169810)). Qed.
Lemma lem5169813 : term278 = term267.
Proof. exact (MK_COMB (@lem5169812) (@lem5169800)). Qed.
Lemma lem5169815 (m : nat) : (term279 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5169816 : term267 = term32.
Proof. exact (@lem5169815 term85). Qed.
Lemma lem5169817 : term278 = term32.
Proof. exact (TRANS (@lem5169813) (@lem5169816)). Qed.
Lemma lem5169818 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5169819 : term280 = term281.
Proof. exact (MK_COMB (@lem5169818) (@lem5169817)). Qed.
Lemma lem5169820 : term91 = term91.
Proof. exact (eq_refl term91). Qed.
Lemma lem5169821 : term282 = term243.
Proof. exact (MK_COMB (@lem5169819) (@lem5169820)). Qed.
Lemma lem5169823 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169824 : term243 = term32.
Proof. exact (@lem5169823 term85). Qed.
Lemma lem5169825 : term282 = term32.
Proof. exact (TRANS (@lem5169821) (@lem5169824)). Qed.
Lemma lem5169827 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5169828 : term94 = term95.
Proof. exact (@lem5169827 term85 term85). Qed.
Lemma lem5169829 : (term96 = (BIT1 0)) = (term97 = term85).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5169830 : term97 = term85.
Proof. exact (EQ_MP (@lem5169829) (@lem940073)). Qed.
Lemma lem5169831 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5169832 : term95 = term91.
Proof. exact (MK_COMB (@lem5169831) (@lem5169830)). Qed.
Lemma lem5169833 : term94 = term91.
Proof. exact (TRANS (@lem5169828) (@lem5169832)). Qed.
Lemma lem5169834 : term281 = term281.
Proof. exact (eq_refl term281). Qed.
Lemma lem5169835 : term283 = term243.
Proof. exact (MK_COMB (@lem5169834) (@lem5169833)). Qed.
Lemma lem5169837 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169838 : term243 = term32.
Proof. exact (@lem5169837 term85). Qed.
Lemma lem5169839 : term283 = term32.
Proof. exact (TRANS (@lem5169835) (@lem5169838)). Qed.
Lemma lem5169840 : term32 = term283.
Proof. exact (SYM (@lem5169839)). Qed.
Lemma lem5169841 : term282 = term283.
Proof. exact (TRANS (@lem5169825) (@lem5169840)). Qed.
Lemma lem5169842 : term268 = term172.
Proof. exact (@lem5169792 (@lem5169841)). Qed.
Lemma lem5169843 : term267 = term172.
Proof. exact (TRANS (@lem5169758) (@lem5169842)). Qed.
Lemma lem5169845 (x : real) : (term102 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5169846 : term172 = term32.
Proof. exact (@lem5169845 term32). Qed.
Lemma lem5169847 : term267 = term32.
Proof. exact (TRANS (@lem5169843) (@lem5169846)). Qed.
Lemma lem5169848 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5169849 : term284 = term281.
Proof. exact (MK_COMB (@lem5169848) (@lem5169847)). Qed.
Lemma lem5169850 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5169851 (x : real) : (term264 x) = (term285 x).
Proof. exact (MK_COMB (@lem5169849) (@lem5169850 x)). Qed.
Lemma lem5169852 (x : real) : (term263 x) = (term285 x).
Proof. exact (TRANS (@lem5169749 x) (@lem5169851 x)). Qed.
Lemma lem5169853 (x : real) : (term285 x) = term32.
Proof. exact (@lem1982719 x). Qed.
Lemma lem5169854 (x : real) : (term263 x) = term32.
Proof. exact (TRANS (@lem5169852 x) (@lem5169853 x)). Qed.
Lemma lem5169855 (l : real) (x : real) : (term288 l x) = term291.
Proof. exact (MK_COMB (@lem5169748 l) (@lem5169854 x)). Qed.
Lemma lem5169856 (l : real) (x : real) : (term287 l x) = term291.
Proof. exact (TRANS (@lem5169640 l x) (@lem5169855 l x)). Qed.
Lemma lem5169857 : term291 = term32.
Proof. exact (@lem1982721 term32). Qed.
Lemma lem5169858 (l : real) (x : real) : (term287 l x) = term32.
Proof. exact (TRANS (@lem5169856 l x) (@lem5169857)). Qed.
Lemma lem5169859 (e : real) (l : real) (x : real) : (term262 e l x) = term291.
Proof. exact (MK_COMB (@lem5169639 e) (@lem5169858 l x)). Qed.
Lemma lem5169860 (e : real) (l : real) (x : real) : (term261 e l x) = term291.
Proof. exact (TRANS (@lem5169531 e l x) (@lem5169859 e l x)). Qed.
Lemma lem5169861 : term291 = term32.
Proof. exact (@lem1982721 term32). Qed.
Lemma lem5169862 (e : real) (l : real) (x : real) : (term261 e l x) = term32.
Proof. exact (TRANS (@lem5169860 e l x) (@lem5169861)). Qed.
Lemma lem5169863 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem5169864 (e : real) (l : real) (x : real) : (term292 e l x) = term293.
Proof. exact (MK_COMB (@lem5169863) (@lem5169862 e l x)). Qed.
Lemma lem5169865 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem5169866 (e : real) (l : real) (x : real) : (term260 e l x) = term294.
Proof. exact (MK_COMB (@lem5169864 e l x) (@lem5169865)). Qed.
Lemma lem5169867 (e : real) (l : real) (x : real) (h1 : term227 e l x) : term294.
Proof. exact (EQ_MP (@lem5169866 e l x) (@lem5169530 e l x h1)). Qed.
Lemma lem5169869 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5169870 : term294 = term295.
Proof. exact (@lem5169869 term32 term32). Qed.
Lemma lem5169872 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5169873 : term32 = term172.
Proof. exact (@lem5169872 (NUMERAL 0)). Qed.
Lemma lem5169875 (x : nat) : (real_of_num x) = (term171 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5169876 : term32 = term172.
Proof. exact (@lem5169875 (NUMERAL 0)). Qed.
Lemma lem5169877 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5169878 : term233 = term234.
Proof. exact (MK_COMB (@lem5169877) (@lem5169876)). Qed.
Lemma lem5169879 : term295 = term296.
Proof. exact (MK_COMB (@lem5169878) (@lem5169873)). Qed.
Lemma lem5169880 : term297.
Proof. exact (@lem1980255 term32 term91 term32 term91). Qed.
Lemma lem5169882 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169883 : term232 = term238.
Proof. exact (@lem5169882 (NUMERAL 0) term85). Qed.
Lemma lem5169884 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169885 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169886 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169885 h1) (fun h1 : term238 = True => @lem5169884)). Qed.
Lemma lem5169887 : term238 = True.
Proof. exact (EQ_MP (@lem5169886) (@lem5169884)). Qed.
Lemma lem5169888 : term232 = True.
Proof. exact (TRANS (@lem5169883) (@lem5169887)). Qed.
Lemma lem5169889 : True = term232.
Proof. exact (SYM (@lem5169888)). Qed.
Lemma lem5169890 : term232.
Proof. exact (EQ_MP (@lem5169889) (@lem0)). Qed.
Lemma lem5169891 : term298.
Proof. exact (@lem5169880 (@lem5169890)). Qed.
Lemma lem5169893 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169894 : term232 = term238.
Proof. exact (@lem5169893 (NUMERAL 0) term85). Qed.
Lemma lem5169895 : term239 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5169896 (h1 : term239 = (BIT1 0)) : term238 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5169897 : (term239 = (BIT1 0)) = (term238 = True).
Proof. exact (prop_ext (fun h1 : term239 = (BIT1 0) => @lem5169896 h1) (fun h1 : term238 = True => @lem5169895)). Qed.
Lemma lem5169898 : term238 = True.
Proof. exact (EQ_MP (@lem5169897) (@lem5169895)). Qed.
Lemma lem5169899 : term232 = True.
Proof. exact (TRANS (@lem5169894) (@lem5169898)). Qed.
Lemma lem5169900 : True = term232.
Proof. exact (SYM (@lem5169899)). Qed.
Lemma lem5169901 : term232.
Proof. exact (EQ_MP (@lem5169900) (@lem0)). Qed.
Lemma lem5169902 : term296 = term299.
Proof. exact (@lem5169891 (@lem5169901)). Qed.
Lemma lem5169904 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169905 : term243 = term32.
Proof. exact (@lem5169904 term85). Qed.
Lemma lem5169907 (x : nat) : (term242 x) = term32.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5169908 : term243 = term32.
Proof. exact (@lem5169907 term85). Qed.
Lemma lem5169909 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5169910 : term244 = term233.
Proof. exact (MK_COMB (@lem5169909) (@lem5169908)). Qed.
Lemma lem5169911 : term299 = term295.
Proof. exact (MK_COMB (@lem5169910) (@lem5169905)). Qed.
Lemma lem5169913 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5169914 : term295 = term300.
Proof. exact (@lem5169913 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem5169915 : term300 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem5169916 : term295 = False.
Proof. exact (TRANS (@lem5169914) (@lem5169915)). Qed.
Lemma lem5169917 : term299 = False.
Proof. exact (TRANS (@lem5169911) (@lem5169916)). Qed.
Lemma lem5169918 : term296 = False.
Proof. exact (TRANS (@lem5169902) (@lem5169917)). Qed.
Lemma lem5169919 : term295 = False.
Proof. exact (TRANS (@lem5169879) (@lem5169918)). Qed.
Lemma lem5169920 : term294 = False.
Proof. exact (TRANS (@lem5169870) (@lem5169919)). Qed.
Lemma lem5169921 (e : real) (l : real) (x : real) (h1 : term227 e l x) : False.
Proof. exact (EQ_MP (@lem5169920) (@lem5169867 e l x h1)). Qed.
Lemma lem5169922 (e : real) (l : real) (x : real) (h1 : term228 e l x) : False.
Proof. exact (or_elim (@lem5168819 e l x h1) (fun h0 : term162 e l x => @lem5169370 e l x h0) (fun h0 : term227 e l x => @lem5169921 e l x h0)). Qed.
Lemma lem5169923 (e : real) (l : real) (x : real) (h1 : term230 e l x) : False.
Proof. exact (or_elim (@lem5167718 e l x h1) (fun h0 : term149 e l x => @lem5168818 e l x h0) (fun h0 : term228 e l x => @lem5169922 e l x h0)). Qed.
Lemma lem5169924 (e : real) (l : real) (x : real) (h1 : term129 e l x) : term129 e l x.
Proof. exact (h1). Qed.
Lemma lem5169925 (e : real) (l : real) (x : real) (h1 : term129 e l x) : term230 e l x.
Proof. exact (EQ_MP (@lem5167717 e l x) (@lem5169924 e l x h1)). Qed.
Lemma lem5169926 (e : real) (l : real) (x : real) (h1 : term129 e l x) : (term230 e l x) = False.
Proof. exact (prop_ext (fun h2 : term230 e l x => @lem5169923 e l x h2) (fun h2 : False => @lem5169925 e l x h1)). Qed.
Lemma lem5169927 (e : real) (l : real) (x : real) (h1 : term129 e l x) : False.
Proof. exact (EQ_MP (@lem5169926 e l x h1) (@lem5169925 e l x h1)). Qed.
Lemma lem5169928 (x : real) (l : real) (e : real) (h1 : term18 x l e) : term18 x l e.
Proof. exact (h1). Qed.
Lemma lem5169929 (x : real) (l : real) (e : real) (h1 : term18 x l e) : term129 e l x.
Proof. exact (EQ_MP (@lem5166954 e l x) (@lem5169928 x l e h1)). Qed.
Lemma lem5169930 (x : real) (l : real) (e : real) (h1 : term18 x l e) : (term129 e l x) = False.
Proof. exact (prop_ext (fun h2 : term129 e l x => @lem5169927 e l x h2) (fun h2 : False => @lem5169929 x l e h1)). Qed.
Lemma lem5169931 (x : real) (l : real) (e : real) (h1 : term18 x l e) : False.
Proof. exact (EQ_MP (@lem5169930 x l e h1) (@lem5169929 x l e h1)). Qed.
Lemma lem5169932 (x : real) (l : real) (e : real) : term319 x l e.
Proof. exact (fun h0 : term18 x l e => @lem5169931 x l e h0). Qed.
Lemma lem5169933 (x : real) (l : real) (e : real) : term320 x l e.
Proof. exact (@lem1386578 ((term19 x l e) = (term20 x l e))). Qed.
Lemma lem5169952 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term321 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5169953 (p : Prop) (q : Prop) (p' : Prop) : term322 p q p'.
Proof. exact (fun q' : Prop => @lem5169952 p q p' q'). Qed.
Lemma lem5169954 (p : Prop) (q : Prop) : term323 p q.
Proof. exact (fun p' : Prop => @lem5169953 p q p'). Qed.
Lemma lem5169955 (s : real -> Prop) (l : real) (e : real) : term324 s l e.
Proof. exact (@lem5169954 (term325 s l e) (term326 s l e)). Qed.
Lemma lem5169956 (s : real -> Prop) (l : real) (e : real) (p' : Prop) : term327 s l e p'.
Proof. exact (@lem5169955 s l e p'). Qed.
Lemma lem5169957 (s : real -> Prop) (l : real) (e : real) (p' : Prop) : (term327 s l e p') = (term328 s l e p').
Proof. exact (eq_refl (term327 s l e p')). Qed.
Lemma lem5169958 (s : real -> Prop) (l : real) (e : real) (p' : Prop) : term328 s l e p'.
Proof. exact (EQ_MP (@lem5169957 s l e p') (@lem5169956 s l e p')). Qed.
Lemma lem5169959 (s : real -> Prop) (l : real) (e : real) (p' : Prop) (q' : Prop) : term329 s l e p' q'.
Proof. exact (@lem5169958 s l e p' q'). Qed.
Lemma lem5169960 (s : real -> Prop) (l : real) (e : real) (p' : Prop) (q' : Prop) : (term329 s l e p' q') = (term330 s l e p' q').
Proof. exact (eq_refl (term329 s l e p' q')). Qed.
Lemma lem5169961 (s : real -> Prop) (l : real) (e : real) (p' : Prop) (q' : Prop) : term330 s l e p' q'.
Proof. exact (EQ_MP (@lem5169960 s l e p' q') (@lem5169959 s l e p' q')). Qed.
Lemma lem5169973 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term321 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5169974 (p : Prop) (q : Prop) (p' : Prop) : term322 p q p'.
Proof. exact (fun q' : Prop => @lem5169973 p q p' q'). Qed.
Lemma lem5169975 (p : Prop) (q : Prop) : term323 p q.
Proof. exact (fun p' : Prop => @lem5169974 p q p'). Qed.
Lemma lem5169976 (s : real -> Prop) (x : real) (l : real) (e : real) : term331 s x l e.
Proof. exact (@lem5169975 (@IN real x s) (term19 x l e)). Qed.
Lemma lem5169977 (s : real -> Prop) (x : real) (l : real) (e : real) (p' : Prop) : term332 s x l e p'.
Proof. exact (@lem5169976 s x l e p'). Qed.
Lemma lem5169978 (s : real -> Prop) (x : real) (l : real) (e : real) (p' : Prop) : (term332 s x l e p') = (term333 s x l e p').
Proof. exact (eq_refl (term332 s x l e p')). Qed.
Lemma lem5169979 (s : real -> Prop) (x : real) (l : real) (e : real) (p' : Prop) : term333 s x l e p'.
Proof. exact (EQ_MP (@lem5169978 s x l e p') (@lem5169977 s x l e p')). Qed.
Lemma lem5169980 (s : real -> Prop) (x : real) (l : real) (e : real) (p' : Prop) (q' : Prop) : term334 s x l e p' q'.
Proof. exact (@lem5169979 s x l e p' q'). Qed.
Lemma lem5169981 (s : real -> Prop) (x : real) (l : real) (e : real) (p' : Prop) (q' : Prop) : (term334 s x l e p' q') = (term335 s x l e p' q').
Proof. exact (eq_refl (term334 s x l e p' q')). Qed.
Lemma lem5169982 (s : real -> Prop) (x : real) (l : real) (e : real) (p' : Prop) (q' : Prop) : term335 s x l e p' q'.
Proof. exact (EQ_MP (@lem5169981 s x l e p' q') (@lem5169980 s x l e p' q')). Qed.
Lemma lem5169983 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5169984 (l : real) (e : real) (x : real) (s : real -> Prop) (q' : Prop) : term336 l e x s q'.
Proof. exact (@lem5169982 s x l e (@IN real x s) q'). Qed.
Lemma lem5169985 (l : real) (e : real) (x : real) (s : real -> Prop) (q' : Prop) : term337 l e x s q'.
Proof. exact (@lem5169984 l e x s q' (@lem5169983 x s)). Qed.
Lemma lem5169990 (x : real) (l : real) (e : real) : (term19 x l e) = (term20 x l e).
Proof. exact (@lem5169933 x l e (@lem5169932 x l e)). Qed.
Lemma lem5169993 (s : real -> Prop) (x : real) (l : real) (e : real) : term338 s x l e.
Proof. exact (fun h0 : @IN real x s => @lem5169990 x l e). Qed.
Lemma lem5169994 (s : real -> Prop) (x : real) (l : real) (e : real) : term339 s x l e.
Proof. exact (@lem5169985 l e x s (term20 x l e)). Qed.
Lemma lem5169995 (s : real -> Prop) (x : real) (l : real) (e : real) : (term340 s x l e) = (term341 s x l e).
Proof. exact (@lem5169994 s x l e (@lem5169993 s x l e)). Qed.
Lemma lem5170023 (s : real -> Prop) (l : real) (e : real) : (term342 s l e) = (term343 s l e).
Proof. exact (fun_ext (fun x : real => @lem5169995 s x l e)). Qed.
Lemma lem5170051 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5170052 (s : real -> Prop) (l : real) (e : real) : (term344 s l e) = (term345 s l e).
Proof. exact (MK_COMB (@lem5170051) (@lem5170023 s l e)). Qed.
Lemma lem5170084 (s : real -> Prop) : (term346 s) = (term346 s).
Proof. exact (eq_refl (term346 s)). Qed.
Lemma lem5170085 (s : real -> Prop) (l : real) (e : real) : (term325 s l e) = (term347 s l e).
Proof. exact (MK_COMB (@lem5170084 s) (@lem5170052 s l e)). Qed.
Lemma lem5170121 (s : real -> Prop) (l : real) (e : real) (q' : Prop) : term348 s l e q'.
Proof. exact (@lem5169961 s l e (term347 s l e) q'). Qed.
Lemma lem5170122 (s : real -> Prop) (l : real) (e : real) (q' : Prop) : term349 s l e q'.
Proof. exact (@lem5170121 s l e q' (@lem5170085 s l e)). Qed.
Lemma lem5170161 (x : real) (l : real) (e : real) : (term19 x l e) = (term20 x l e).
Proof. exact (@lem5169933 x l e (@lem5169932 x l e)). Qed.
Lemma lem5170162 (s : real -> Prop) (l : real) (e : real) : (term326 s l e) = (term350 s l e).
Proof. exact (@lem5170161 (sup s) l e). Qed.
Lemma lem5170175 (s : real -> Prop) (l : real) (e : real) : term351 s l e.
Proof. exact (fun h0 : term347 s l e => @lem5170162 s l e). Qed.
Lemma lem5170176 (s : real -> Prop) (l : real) (e : real) : term352 s l e.
Proof. exact (@lem5170122 s l e (term350 s l e)). Qed.
Lemma lem5170177 (s : real -> Prop) (l : real) (e : real) : (term353 s l e) = (term354 s l e).
Proof. exact (@lem5170176 s l e (@lem5170175 s l e)). Qed.
Lemma lem5170319 (s : real -> Prop) (l : real) : (term355 s l) = (term356 s l).
Proof. exact (fun_ext (fun e : real => @lem5170177 s l e)). Qed.
Lemma lem5170461 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5170462 (s : real -> Prop) (l : real) : (term357 s l) = (term358 s l).
Proof. exact (MK_COMB (@lem5170461) (@lem5170319 s l)). Qed.
Lemma lem5170608 (s : real -> Prop) : (term359 s) = (term360 s).
Proof. exact (fun_ext (fun l : real => @lem5170462 s l)). Qed.
Lemma lem5170754 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5170755 (s : real -> Prop) : (term361 s) = (term362 s).
Proof. exact (MK_COMB (@lem5170754) (@lem5170608 s)). Qed.
Lemma lem5170905 : term363 = term364.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5170755 s)). Qed.
Lemma lem5171055 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5171056 : term365 = term366.
Proof. exact (MK_COMB (@lem5171055) (@lem5170905)). Qed.
Lemma lem5171210 : term366 = term365.
Proof. exact (SYM (@lem5171056)). Qed.
Lemma lem5171224 (a : real) (s : real -> Prop) (b : real) : (term5 a s b) = True.
Proof. exact (EQ_MP (@lem5166589 a s b) (@lem5166588 a s b)). Qed.
Lemma lem5171225 (s : real -> Prop) (l : real) (e : real) : (term354 s l e) = True.
Proof. exact (@lem5171224 (real_sub l e) s (real_add l e)). Qed.
Lemma lem5171226 (s : real -> Prop) (l : real) : (term356 s l) = term367.
Proof. exact (fun_ext (fun e : real => @lem5171225 s l e)). Qed.
Lemma lem5171227 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5171228 (s : real -> Prop) (l : real) : (term358 s l) = term368.
Proof. exact (MK_COMB (@lem5171227) (@lem5171226 s l)). Qed.
Lemma lem5171230 {A : Type'} (t : Prop) : (term369 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5171231 (t : Prop) : (term370 t) = t.
Proof. exact (@lem5171230 real t). Qed.
Lemma lem5171232 : term368 = True.
Proof. exact (@lem5171231 True). Qed.
Lemma lem5171233 (s : real -> Prop) (l : real) : (term358 s l) = True.
Proof. exact (TRANS (@lem5171228 s l) (@lem5171232)). Qed.
Lemma lem5171234 (s : real -> Prop) : (term360 s) = term367.
Proof. exact (fun_ext (fun l : real => @lem5171233 s l)). Qed.
Lemma lem5171235 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5171236 (s : real -> Prop) : (term362 s) = term368.
Proof. exact (MK_COMB (@lem5171235) (@lem5171234 s)). Qed.
Lemma lem5171238 {A : Type'} (t : Prop) : (term369 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5171239 (t : Prop) : (term370 t) = t.
Proof. exact (@lem5171238 real t). Qed.
Lemma lem5171240 : term368 = True.
Proof. exact (@lem5171239 True). Qed.
Lemma lem5171241 (s : real -> Prop) : (term362 s) = True.
Proof. exact (TRANS (@lem5171236 s) (@lem5171240)). Qed.
Lemma lem5171242 : term364 = term371.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5171241 s)). Qed.
Lemma lem5171243 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5171244 : term366 = term372.
Proof. exact (MK_COMB (@lem5171243) (@lem5171242)). Qed.
Lemma lem5171246 {A : Type'} (t : Prop) : (term369 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5171247 (t : Prop) : (term373 t) = t.
Proof. exact (@lem5171246 (real -> Prop) t). Qed.
Lemma lem5171248 : term372 = True.
Proof. exact (@lem5171247 True). Qed.
Lemma lem5171249 : term366 = True.
Proof. exact (TRANS (@lem5171244) (@lem5171248)). Qed.
Lemma lem5171250 : True = term366.
Proof. exact (SYM (@lem5171249)). Qed.
Lemma lem5171251 : term366.
Proof. exact (EQ_MP (@lem5171250) (@lem0)). Qed.
Lemma lem5171252 : term365.
Proof. exact (EQ_MP (@lem5171210) (@lem5171251)). Qed.
