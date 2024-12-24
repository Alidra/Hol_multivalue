Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_LZERO_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483476_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1517644 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1517645 : term2 = term3.
Proof. exact (@lem1517644 term4). Qed.
Lemma lem1517646 (x : real) : (term5 x) = ((term6 x) = (real_neg x)).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1517647 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1517649 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1517647) (@lem1517646 x)). Qed.
Lemma lem1517650 : term9 = term10.
Proof. exact (fun_ext (fun x : real => @lem1517649 x)). Qed.
Lemma lem1517651 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517652 : term3 = term11.
Proof. exact (MK_COMB (@lem1517651) (@lem1517650)). Qed.
Lemma lem1517654 : term2 = term11.
Proof. exact (TRANS (@lem1517645) (@lem1517652)). Qed.
Lemma lem1517657 (x : real) : (term8 x) = (term8 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1517658 : term10 = term10.
Proof. exact (fun_ext (fun x : real => @lem1517657 x)). Qed.
Lemma lem1517659 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517660 : term11 = term11.
Proof. exact (MK_COMB (@lem1517659) (@lem1517658)). Qed.
Lemma lem1517661 : term2 = term11.
Proof. exact (TRANS (@lem1517654) (@lem1517660)). Qed.
Lemma lem1517662 (x : real) : (term8 x) = (term12 x).
Proof. exact (@lem1483554 (term6 x) (real_neg x)). Qed.
Lemma lem1517669 (x : real) : (real_neg x) = (term13 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1517675 (x : real) : (term6 x) = (term14 x).
Proof. exact (@lem1483519 term15 x). Qed.
Lemma lem1517680 (x : real) : (term14 x) = (term13 x).
Proof. exact (@lem1483448 (term13 x)). Qed.
Lemma lem1517682 (x : real) : (term6 x) = (term13 x).
Proof. exact (TRANS (@lem1517675 x) (@lem1517680 x)). Qed.
Lemma lem1517683 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1517684 (x : real) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem1517683) (@lem1517682 x)). Qed.
Lemma lem1517685 (x : real) : (term18 x) = (term19 x).
Proof. exact (MK_COMB (@lem1517684 x) (@lem1517669 x)). Qed.
Lemma lem1517686 (x : real) : (term19 x) = (term20 x).
Proof. exact (@lem1483519 (term13 x) (term13 x)). Qed.
Lemma lem1517687 (x : real) : (term21 x) = (term22 x).
Proof. exact (@lem1483476 term23 term23 x). Qed.
Lemma lem1517689 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1517690 : term26 = term27.
Proof. exact (@lem1517689 term28 term28). Qed.
Lemma lem1517691 : (term29 = (BIT1 0)) = (term30 = term28).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1517692 : term30 = term28.
Proof. exact (EQ_MP (@lem1517691) (@lem940073)). Qed.
Lemma lem1517693 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1517694 : term27 = term31.
Proof. exact (MK_COMB (@lem1517693) (@lem1517692)). Qed.
Lemma lem1517695 : term26 = term31.
Proof. exact (TRANS (@lem1517690) (@lem1517694)). Qed.
Lemma lem1517696 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1517697 : term32 = term33.
Proof. exact (MK_COMB (@lem1517696) (@lem1517695)). Qed.
Lemma lem1517698 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1517699 (x : real) : (term22 x) = (term34 x).
Proof. exact (MK_COMB (@lem1517697) (@lem1517698 x)). Qed.
Lemma lem1517700 (x : real) : (term21 x) = (term34 x).
Proof. exact (TRANS (@lem1517687 x) (@lem1517699 x)). Qed.
Lemma lem1517701 (x : real) : (term34 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1517702 (x : real) : (term21 x) = x.
Proof. exact (TRANS (@lem1517700 x) (@lem1517701 x)). Qed.
Lemma lem1517703 (x : real) : (term35 x) = (term35 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1517704 (x : real) : (term20 x) = (term36 x).
Proof. exact (MK_COMB (@lem1517703 x) (@lem1517702 x)). Qed.
Lemma lem1517705 (x : real) : (term36 x) = (term37 x).
Proof. exact (@lem1483440 term23 x). Qed.
Lemma lem1517707 (m : nat) : (term38 m) = term15.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1517708 : term39 = term15.
Proof. exact (@lem1517707 term28). Qed.
Lemma lem1517709 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1517710 : term40 = term41.
Proof. exact (MK_COMB (@lem1517709) (@lem1517708)). Qed.
Lemma lem1517711 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1517712 (x : real) : (term37 x) = (term42 x).
Proof. exact (MK_COMB (@lem1517710) (@lem1517711 x)). Qed.
Lemma lem1517713 (x : real) : (term36 x) = (term42 x).
Proof. exact (TRANS (@lem1517705 x) (@lem1517712 x)). Qed.
Lemma lem1517714 (x : real) : (term42 x) = term15.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1517715 (x : real) : (term36 x) = term15.
Proof. exact (TRANS (@lem1517713 x) (@lem1517714 x)). Qed.
Lemma lem1517716 (x : real) : (term20 x) = term15.
Proof. exact (TRANS (@lem1517704 x) (@lem1517715 x)). Qed.
Lemma lem1517717 (x : real) : (term19 x) = term15.
Proof. exact (TRANS (@lem1517686 x) (@lem1517716 x)). Qed.
Lemma lem1517718 (x : real) : (term18 x) = term15.
Proof. exact (TRANS (@lem1517685 x) (@lem1517717 x)). Qed.
Lemma lem1517719 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1517720 (x : real) : (term43 x) = term44.
Proof. exact (MK_COMB (@lem1517719) (@lem1517718 x)). Qed.
Lemma lem1517721 : term44 = term45.
Proof. exact (@lem1483512 term15). Qed.
Lemma lem1517723 (x : nat) : (term46 x) = term15.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1517724 : term45 = term15.
Proof. exact (@lem1517723 term28). Qed.
Lemma lem1517725 : term44 = term15.
Proof. exact (TRANS (@lem1517721) (@lem1517724)). Qed.
Lemma lem1517726 (x : real) : (term47 x) = (term47 x).
Proof. exact (eq_refl (term47 x)). Qed.
Lemma lem1517727 (x : real) : ((term43 x) = term44) = ((term43 x) = term15).
Proof. exact (MK_COMB (@lem1517726 x) (@lem1517725)). Qed.
Lemma lem1517728 (x : real) : (term43 x) = term15.
Proof. exact (EQ_MP (@lem1517727 x) (@lem1517720 x)). Qed.
Lemma lem1517729 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1517730 (x : real) : (term48 x) = term49.
Proof. exact (MK_COMB (@lem1517729) (@lem1517728 x)). Qed.
Lemma lem1517731 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1517732 (x : real) : (term50 x) = term51.
Proof. exact (MK_COMB (@lem1517730 x) (@lem1517731)). Qed.
Lemma lem1517733 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1517734 (x : real) : (term52 x) = term49.
Proof. exact (MK_COMB (@lem1517733) (@lem1517718 x)). Qed.
Lemma lem1517735 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem1517736 (x : real) : (term53 x) = term51.
Proof. exact (MK_COMB (@lem1517734 x) (@lem1517735)). Qed.
Lemma lem1517737 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1517738 (x : real) : (term54 x) = term55.
Proof. exact (MK_COMB (@lem1517737) (@lem1517736 x)). Qed.
Lemma lem1517739 (x : real) : (term12 x) = term56.
Proof. exact (MK_COMB (@lem1517738 x) (@lem1517732 x)). Qed.
Lemma lem1517740 (x : real) : (term8 x) = term56.
Proof. exact (TRANS (@lem1517662 x) (@lem1517739 x)). Qed.
Lemma lem1517741 : term10 = term57.
Proof. exact (fun_ext (fun x : real => @lem1517740 x)). Qed.
Lemma lem1517742 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517743 : term11 = term58.
Proof. exact (MK_COMB (@lem1517742) (@lem1517741)). Qed.
Lemma lem1517744 : term2 = term58.
Proof. exact (TRANS (@lem1517661) (@lem1517743)). Qed.
Lemma lem1517746 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term59 A P Q) = (term60 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1517747 (P : real -> Prop) (Q : real -> Prop) : (term61 P Q) = (term62 P Q).
Proof. exact (@lem1517746 real P Q). Qed.
Lemma lem1517748 : term63 = term64.
Proof. exact (@lem1517747 term65 term65). Qed.
Lemma lem1517749 (x : real) : (term66 x) = term51.
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem1517750 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1517751 (x : real) : (term67 x) = term55.
Proof. exact (MK_COMB (@lem1517750) (@lem1517749 x)). Qed.
Lemma lem1517752 (x : real) : (term66 x) = term51.
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem1517753 (x : real) : (term68 x) = term56.
Proof. exact (MK_COMB (@lem1517751 x) (@lem1517752 x)). Qed.
Lemma lem1517754 : term69 = term57.
Proof. exact (fun_ext (fun x : real => @lem1517753 x)). Qed.
Lemma lem1517755 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517756 : term63 = term58.
Proof. exact (MK_COMB (@lem1517755) (@lem1517754)). Qed.
Lemma lem1517757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1517758 : term70 = term71.
Proof. exact (MK_COMB (@lem1517757) (@lem1517756)). Qed.
Lemma lem1517759 (x : real) : (term66 x) = term51.
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem1517760 : term72 = term65.
Proof. exact (fun_ext (fun x : real => @lem1517759 x)). Qed.
Lemma lem1517761 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517762 : term73 = term74.
Proof. exact (MK_COMB (@lem1517761) (@lem1517760)). Qed.
Lemma lem1517763 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1517764 : term75 = term76.
Proof. exact (MK_COMB (@lem1517763) (@lem1517762)). Qed.
Lemma lem1517765 (x : real) : (term66 x) = term51.
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem1517766 : term72 = term65.
Proof. exact (fun_ext (fun x : real => @lem1517765 x)). Qed.
Lemma lem1517767 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1517768 : term73 = term74.
Proof. exact (MK_COMB (@lem1517767) (@lem1517766)). Qed.
Lemma lem1517769 : term64 = term77.
Proof. exact (MK_COMB (@lem1517764) (@lem1517768)). Qed.
Lemma lem1517770 : (term63 = term64) = (term58 = term77).
Proof. exact (MK_COMB (@lem1517758) (@lem1517769)). Qed.
Lemma lem1517771 : term58 = term77.
Proof. exact (EQ_MP (@lem1517770) (@lem1517748)). Qed.
Lemma lem1517773 {A : Type'} (t : Prop) : (term78 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1517774 (t : Prop) : (term79 t) = t.
Proof. exact (@lem1517773 real t). Qed.
Lemma lem1517775 : term74 = term51.
Proof. exact (@lem1517774 term51). Qed.
Lemma lem1517776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1517777 : term76 = term55.
Proof. exact (MK_COMB (@lem1517776) (@lem1517775)). Qed.
Lemma lem1517779 {A : Type'} (t : Prop) : (term78 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem1517780 (t : Prop) : (term79 t) = t.
Proof. exact (@lem1517779 real t). Qed.
Lemma lem1517781 : term74 = term51.
Proof. exact (@lem1517780 term51). Qed.
Lemma lem1517782 : term77 = term56.
Proof. exact (MK_COMB (@lem1517777) (@lem1517781)). Qed.
Lemma lem1517785 : term58 = term56.
Proof. exact (TRANS (@lem1517771) (@lem1517782)). Qed.
Lemma lem1517794 : term2 = term56.
Proof. exact (TRANS (@lem1517744) (@lem1517785)). Qed.
Lemma lem1517804 (h1 : term56) : term56.
Proof. exact (h1). Qed.
Lemma lem1517805 (h1 : term51) : term51.
Proof. exact (h1). Qed.
Lemma lem1517807 (n : nat) (m : nat) : (term80 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1517808 : term51 = term81.
Proof. exact (@lem1517807 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1517809 : term81 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1517810 : term51 = False.
Proof. exact (TRANS (@lem1517808) (@lem1517809)). Qed.
Lemma lem1517811 (h1 : term51) : False.
Proof. exact (EQ_MP (@lem1517810) (@lem1517805 h1)). Qed.
Lemma lem1517812 (h1 : term51) : term51.
Proof. exact (h1). Qed.
Lemma lem1517814 (n : nat) (m : nat) : (term80 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1517815 : term51 = term81.
Proof. exact (@lem1517814 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1517816 : term81 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1517817 : term51 = False.
Proof. exact (TRANS (@lem1517815) (@lem1517816)). Qed.
Lemma lem1517818 (h1 : term51) : False.
Proof. exact (EQ_MP (@lem1517817) (@lem1517812 h1)). Qed.
Lemma lem1517819 (h1 : term56) : False.
Proof. exact (or_elim (@lem1517804 h1) (fun h0 : term51 => @lem1517811 h0) (fun h0 : term51 => @lem1517818 h0)). Qed.
Lemma lem1517821 (h1 : term56) : term56.
Proof. exact (h1). Qed.
Lemma lem1517822 (h1 : term56) : term56 = False.
Proof. exact (prop_ext (fun h2 : term56 => @lem1517819 h1) (fun h2 : False => @lem1517821 h1)). Qed.
Lemma lem1517823 (h1 : term56) : False.
Proof. exact (EQ_MP (@lem1517822 h1) (@lem1517821 h1)). Qed.
Lemma lem1517824 (h1 : term2) : term2.
Proof. exact (h1). Qed.
Lemma lem1517825 (h1 : term2) : term56.
Proof. exact (EQ_MP (@lem1517794) (@lem1517824 h1)). Qed.
Lemma lem1517826 (h1 : term2) : term56 = False.
Proof. exact (prop_ext (fun h2 : term56 => @lem1517823 h2) (fun h2 : False => @lem1517825 h1)). Qed.
Lemma lem1517827 (h1 : term2) : False.
Proof. exact (EQ_MP (@lem1517826 h1) (@lem1517825 h1)). Qed.
Lemma lem1517828 : term82.
Proof. exact (fun h0 : term2 => @lem1517827 h0). Qed.
Lemma lem1517829 : term83.
Proof. exact (@lem1386578 term84). Qed.
Lemma lem1517830 : term84.
Proof. exact (@lem1517829 (@lem1517828)). Qed.
