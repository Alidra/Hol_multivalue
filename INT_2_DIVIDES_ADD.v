Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_2_DIVIDES_ADD_term_abbrevs.
Require Import INT_ADD_REM_spec.
Require Import INT_REM_2_CASES_spec.
Require Import INT_REM_2_DIVIDES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1009824_spec.
Require Import thm1011471_spec.
Require Import thm1011992_spec.
Require Import thm1013352_spec.
Require Import thm1855_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm2403914_spec.
Require Import thm2404231_spec.
Require Import thm2405481_spec.
Require Import thm2405621_spec.
Require Import thm2405758_spec.
Require Import thm2406280_spec.
Require Import thm2406442_spec.
Require Import thm2743639_spec.
Require Import thm706819_spec.
Require Import thm706821_spec.
Require Import thm706883_spec.
Require Import thm706885_spec.
Require Import thm706947_spec.
Require Import thm912739_spec.
Require Import thm912741_spec.
Require Import thm912803_spec.
Require Import thm996238_spec.
Lemma lem2743640 (n : int) : term0 n.
Proof. exact (@lem2716252 n). Qed.
Lemma lem2743641 (n : int) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem2743642 (n : int) : term1 n.
Proof. exact (EQ_MP (@lem2743641 n) (@lem2743640 n)). Qed.
Lemma lem2743645 (m : int) : term0 m.
Proof. exact (@lem2716252 m). Qed.
Lemma lem2743646 (m : int) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2743647 (m : int) : term1 m.
Proof. exact (EQ_MP (@lem2743646 m) (@lem2743645 m)). Qed.
Lemma lem2743653 (m : int) (n : int) (p : int) (h1 : (term2 m n p) = (term3 m n p)) : (term2 m n p) = (term3 m n p).
Proof. exact (h1). Qed.
Lemma lem2743654 (m : int) (n : int) (p : int) (h1 : (term2 m n p) = (term3 m n p)) : (term3 m n p) = (term2 m n p).
Proof. exact (SYM (@lem2743653 m n p h1)). Qed.
Lemma lem2743655 (m : int) (n : int) (p : int) (h1 : (term3 m n p) = (term2 m n p)) : (term3 m n p) = (term2 m n p).
Proof. exact (h1). Qed.
Lemma lem2743656 (m : int) (n : int) (p : int) (h1 : (term3 m n p) = (term2 m n p)) : (term2 m n p) = (term3 m n p).
Proof. exact (SYM (@lem2743655 m n p h1)). Qed.
Lemma lem2743657 (m : int) (n : int) (p : int) : ((term2 m n p) = (term3 m n p)) = ((term3 m n p) = (term2 m n p)).
Proof. exact (prop_ext (fun h1 : (term2 m n p) = (term3 m n p) => @lem2743654 m n p h1) (fun h1 : (term3 m n p) = (term2 m n p) => @lem2743656 m n p h1)). Qed.
Lemma lem2743658 (m : int) (n : int) : (term4 m n) = (term5 m n).
Proof. exact (fun_ext (fun p : int => @lem2743657 m n p)). Qed.
Lemma lem2743659 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2743660 (m : int) (n : int) : (term6 m n) = (term7 m n).
Proof. exact (MK_COMB (@lem2743659) (@lem2743658 m n)). Qed.
Lemma lem2743661 (m : int) : (term8 m) = (term9 m).
Proof. exact (fun_ext (fun n : int => @lem2743660 m n)). Qed.
Lemma lem2743662 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2743663 (m : int) : (term10 m) = (term11 m).
Proof. exact (MK_COMB (@lem2743662) (@lem2743661 m)). Qed.
Lemma lem2743664 : term12 = term13.
Proof. exact (fun_ext (fun m : int => @lem2743663 m)). Qed.
Lemma lem2743665 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2743666 : term14 = term15.
Proof. exact (MK_COMB (@lem2743665) (@lem2743664)). Qed.
Lemma lem2743667 : term15.
Proof. exact (EQ_MP (@lem2743666) (@lem2534337)). Qed.
Lemma lem2743668 (m : int) : term16 m.
Proof. exact (@lem2743667 m). Qed.
Lemma lem2743669 (m : int) : (term16 m) = (term11 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem2743670 (m : int) : term11 m.
Proof. exact (EQ_MP (@lem2743669 m) (@lem2743668 m)). Qed.
Lemma lem2743671 (m : int) (n : int) : term17 m n.
Proof. exact (@lem2743670 m n). Qed.
Lemma lem2743672 (m : int) (n : int) : (term17 m n) = (term7 m n).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem2743673 (m : int) (n : int) : term7 m n.
Proof. exact (EQ_MP (@lem2743672 m n) (@lem2743671 m n)). Qed.
Lemma lem2743674 (m : int) (n : int) (p : int) : term18 m n p.
Proof. exact (@lem2743673 m n p). Qed.
Lemma lem2743675 (m : int) (n : int) (p : int) : (term18 m n p) = ((term3 m n p) = (term2 m n p)).
Proof. exact (eq_refl (term18 m n p)). Qed.
Lemma lem2743679 (n : int) (h1 : ((term19 n) = term20) = (term21 n)) : ((term19 n) = term20) = (term21 n).
Proof. exact (h1). Qed.
Lemma lem2743680 (n : int) (h1 : ((term19 n) = term20) = (term21 n)) : (term21 n) = ((term19 n) = term20).
Proof. exact (SYM (@lem2743679 n h1)). Qed.
Lemma lem2743681 (n : int) (h1 : (term21 n) = ((term19 n) = term20)) : (term21 n) = ((term19 n) = term20).
Proof. exact (h1). Qed.
Lemma lem2743682 (n : int) (h1 : (term21 n) = ((term19 n) = term20)) : ((term19 n) = term20) = (term21 n).
Proof. exact (SYM (@lem2743681 n h1)). Qed.
Lemma lem2743683 (n : int) : (((term19 n) = term20) = (term21 n)) = ((term21 n) = ((term19 n) = term20)).
Proof. exact (prop_ext (fun h1 : ((term19 n) = term20) = (term21 n) => @lem2743680 n h1) (fun h1 : (term21 n) = ((term19 n) = term20) => @lem2743682 n h1)). Qed.
Lemma lem2743684 : term22 = term23.
Proof. exact (fun_ext (fun n : int => @lem2743683 n)). Qed.
Lemma lem2743685 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2743686 : term24 = term25.
Proof. exact (MK_COMB (@lem2743685) (@lem2743684)). Qed.
Lemma lem2743687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2743688 : term26 = term27.
Proof. exact (MK_COMB (@lem2743687) (@lem2743686)). Qed.
Lemma lem2743690 (n : int) (h1 : ((term19 n) = term28) = (term29 n)) : ((term19 n) = term28) = (term29 n).
Proof. exact (h1). Qed.
Lemma lem2743691 (n : int) (h1 : ((term19 n) = term28) = (term29 n)) : (term29 n) = ((term19 n) = term28).
Proof. exact (SYM (@lem2743690 n h1)). Qed.
Lemma lem2743692 (n : int) (h1 : (term29 n) = ((term19 n) = term28)) : (term29 n) = ((term19 n) = term28).
Proof. exact (h1). Qed.
Lemma lem2743693 (n : int) (h1 : (term29 n) = ((term19 n) = term28)) : ((term19 n) = term28) = (term29 n).
Proof. exact (SYM (@lem2743692 n h1)). Qed.
Lemma lem2743694 (n : int) : (((term19 n) = term28) = (term29 n)) = ((term29 n) = ((term19 n) = term28)).
Proof. exact (prop_ext (fun h1 : ((term19 n) = term28) = (term29 n) => @lem2743691 n h1) (fun h1 : (term29 n) = ((term19 n) = term28) => @lem2743693 n h1)). Qed.
Lemma lem2743695 : term30 = term31.
Proof. exact (fun_ext (fun n : int => @lem2743694 n)). Qed.
Lemma lem2743696 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2743697 : term32 = term33.
Proof. exact (MK_COMB (@lem2743696) (@lem2743695)). Qed.
Lemma lem2743698 : term34 = term35.
Proof. exact (MK_COMB (@lem2743688) (@lem2743697)). Qed.
Lemma lem2743699 : term35.
Proof. exact (EQ_MP (@lem2743698) (@lem2725348)). Qed.
Lemma lem2743704 : term25.
Proof. exact (proj1 (@lem2743699)). Qed.
Lemma lem2743705 (n : int) : term36 n.
Proof. exact (@lem2743704 n). Qed.
Lemma lem2743706 (n : int) : (term36 n) = ((term21 n) = ((term19 n) = term20)).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem2743711 (n : int) : (term21 n) = ((term19 n) = term20).
Proof. exact (EQ_MP (@lem2743706 n) (@lem2743705 n)). Qed.
Lemma lem2743712 (m : int) (n : int) : (term37 m n) = ((term38 m n) = term20).
Proof. exact (@lem2743711 (int_add m n)). Qed.
Lemma lem2743715 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2743716 (m : int) (n : int) : (term39 m n) = (term40 m n).
Proof. exact (MK_COMB (@lem2743715) (@lem2743712 m n)). Qed.
Lemma lem2743720 (n : int) : (term21 n) = ((term19 n) = term20).
Proof. exact (EQ_MP (@lem2743706 n) (@lem2743705 n)). Qed.
Lemma lem2743721 (m : int) : (term21 m) = ((term19 m) = term20).
Proof. exact (@lem2743720 m). Qed.
Lemma lem2743724 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2743725 (m : int) : (term41 m) = (term42 m).
Proof. exact (MK_COMB (@lem2743724) (@lem2743721 m)). Qed.
Lemma lem2743727 (n : int) : (term21 n) = ((term19 n) = term20).
Proof. exact (EQ_MP (@lem2743706 n) (@lem2743705 n)). Qed.
Lemma lem2743730 (m : int) (n : int) : ((term21 m) = (term21 n)) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (MK_COMB (@lem2743725 m) (@lem2743727 n)). Qed.
Lemma lem2743733 (m : int) (n : int) : ((term37 m n) = ((term21 m) = (term21 n))) = (((term38 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))).
Proof. exact (MK_COMB (@lem2743716 m n) (@lem2743730 m n)). Qed.
Lemma lem2743736 (m : int) (n : int) : (((term38 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = ((term37 m n) = ((term21 m) = (term21 n))).
Proof. exact (SYM (@lem2743733 m n)). Qed.
Lemma lem2743742 (m : int) (n : int) (p : int) : (term3 m n p) = (term2 m n p).
Proof. exact (EQ_MP (@lem2743675 m n p) (@lem2743674 m n p)). Qed.
Lemma lem2743743 (m : int) (n : int) : (term38 m n) = (term43 m n).
Proof. exact (@lem2743742 m n term44). Qed.
Lemma lem2743744 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2743745 (m : int) (n : int) : (term45 m n) = (term46 m n).
Proof. exact (MK_COMB (@lem2743744) (@lem2743743 m n)). Qed.
Lemma lem2743746 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2743747 (m : int) (n : int) : ((term38 m n) = term20) = ((term43 m n) = term20).
Proof. exact (MK_COMB (@lem2743745 m n) (@lem2743746)). Qed.
Lemma lem2743748 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2743749 (m : int) (n : int) : (term40 m n) = (term47 m n).
Proof. exact (MK_COMB (@lem2743748) (@lem2743747 m n)). Qed.
Lemma lem2743756 (m : int) (n : int) : (((term19 m) = term20) = ((term19 n) = term20)) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (eq_refl (((term19 m) = term20) = ((term19 n) = term20))). Qed.
Lemma lem2743757 (m : int) (n : int) : (((term38 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))).
Proof. exact (MK_COMB (@lem2743749 m n) (@lem2743756 m n)). Qed.
Lemma lem2743758 (m : int) (n : int) : (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = (((term38 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))).
Proof. exact (SYM (@lem2743757 m n)). Qed.
Lemma lem2743764 (m : int) (h1 : (term19 m) = term20) : (term19 m) = term20.
Proof. exact (h1). Qed.
Lemma lem2743765 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2743766 (m : int) (h1 : (term19 m) = term20) : (term48 m) = term49.
Proof. exact (MK_COMB (@lem2743765) (@lem2743764 m h1)). Qed.
Lemma lem2743768 (n : int) (h1 : (term19 n) = term20) : (term19 n) = term20.
Proof. exact (h1). Qed.
Lemma lem2743769 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term50 m n) = term51.
Proof. exact (MK_COMB (@lem2743766 m h1) (@lem2743768 n h2)). Qed.
Lemma lem2743770 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2743771 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term52 m n) = term53.
Proof. exact (MK_COMB (@lem2743770) (@lem2743769 m n h1 h2)). Qed.
Lemma lem2743772 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2743773 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term43 m n) = term54.
Proof. exact (MK_COMB (@lem2743771 m n h1 h2) (@lem2743772)). Qed.
Lemma lem2743774 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2743775 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term46 m n) = term55.
Proof. exact (MK_COMB (@lem2743774) (@lem2743773 m n h1 h2)). Qed.
Lemma lem2743776 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2743777 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : ((term43 m n) = term20) = (term54 = term20).
Proof. exact (MK_COMB (@lem2743775 m n h1 h2) (@lem2743776)). Qed.
Lemma lem2743780 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2743781 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term47 m n) = term56.
Proof. exact (MK_COMB (@lem2743780) (@lem2743777 m n h1 h2)). Qed.
Lemma lem2743787 (m : int) (h1 : (term19 m) = term20) : (term19 m) = term20.
Proof. exact (h1). Qed.
Lemma lem2743788 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2743789 (m : int) (h1 : (term19 m) = term20) : (term57 m) = term58.
Proof. exact (MK_COMB (@lem2743788) (@lem2743787 m h1)). Qed.
Lemma lem2743790 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2743791 (m : int) (h1 : (term19 m) = term20) : ((term19 m) = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2743789 m h1) (@lem2743790)). Qed.
Lemma lem2743793 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2743794 (x : int) : (x = x) = True.
Proof. exact (@lem2743793 int x). Qed.
Lemma lem2743795 : (term20 = term20) = True.
Proof. exact (@lem2743794 term20). Qed.
Lemma lem2743796 (m : int) (h1 : (term19 m) = term20) : ((term19 m) = term20) = True.
Proof. exact (TRANS (@lem2743791 m h1) (@lem2743795)). Qed.
Lemma lem2743797 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2743798 (m : int) (h1 : (term19 m) = term20) : (term42 m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem2743797) (@lem2743796 m h1)). Qed.
Lemma lem2743802 (n : int) (h1 : (term19 n) = term20) : (term19 n) = term20.
Proof. exact (h1). Qed.
Lemma lem2743803 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2743804 (n : int) (h1 : (term19 n) = term20) : (term57 n) = term58.
Proof. exact (MK_COMB (@lem2743803) (@lem2743802 n h1)). Qed.
Lemma lem2743805 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2743806 (n : int) (h1 : (term19 n) = term20) : ((term19 n) = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2743804 n h1) (@lem2743805)). Qed.
Lemma lem2743808 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2743809 (x : int) : (x = x) = True.
Proof. exact (@lem2743808 int x). Qed.
Lemma lem2743810 : (term20 = term20) = True.
Proof. exact (@lem2743809 term20). Qed.
Lemma lem2743811 (n : int) (h1 : (term19 n) = term20) : ((term19 n) = term20) = True.
Proof. exact (TRANS (@lem2743806 n h1) (@lem2743810)). Qed.
Lemma lem2743812 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (((term19 m) = term20) = ((term19 n) = term20)) = (True = True).
Proof. exact (MK_COMB (@lem2743798 m h1) (@lem2743811 n h2)). Qed.
Lemma lem2743814 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem2743815 : (True = True) = True.
Proof. exact (@lem2743814 True). Qed.
Lemma lem2743816 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (((term19 m) = term20) = ((term19 n) = term20)) = True.
Proof. exact (TRANS (@lem2743812 m n h1 h2) (@lem2743815)). Qed.
Lemma lem2743817 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = ((term54 = term20) = True).
Proof. exact (MK_COMB (@lem2743781 m n h1 h2) (@lem2743816 m n h1 h2)). Qed.
Lemma lem2743819 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem2743820 : ((term54 = term20) = True) = (term54 = term20).
Proof. exact (@lem2743819 (term54 = term20)). Qed.
Lemma lem2743823 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = (term54 = term20).
Proof. exact (TRANS (@lem2743817 m n h1 h2) (@lem2743820)). Qed.
Lemma lem2743824 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : (term54 = term20) = (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))).
Proof. exact (SYM (@lem2743823 m n h1 h2)). Qed.
Lemma lem2743830 (m : int) (h1 : (term19 m) = term20) : (term19 m) = term20.
Proof. exact (h1). Qed.
Lemma lem2743831 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2743832 (m : int) (h1 : (term19 m) = term20) : (term48 m) = term49.
Proof. exact (MK_COMB (@lem2743831) (@lem2743830 m h1)). Qed.
Lemma lem2743834 (n : int) (h1 : (term19 n) = term28) : (term19 n) = term28.
Proof. exact (h1). Qed.
Lemma lem2743835 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term50 m n) = term59.
Proof. exact (MK_COMB (@lem2743832 m h1) (@lem2743834 n h2)). Qed.
Lemma lem2743836 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2743837 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term52 m n) = term60.
Proof. exact (MK_COMB (@lem2743836) (@lem2743835 m n h1 h2)). Qed.
Lemma lem2743838 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2743839 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term43 m n) = term61.
Proof. exact (MK_COMB (@lem2743837 m n h1 h2) (@lem2743838)). Qed.
Lemma lem2743840 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2743841 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term46 m n) = term62.
Proof. exact (MK_COMB (@lem2743840) (@lem2743839 m n h1 h2)). Qed.
Lemma lem2743842 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2743843 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : ((term43 m n) = term20) = (term61 = term20).
Proof. exact (MK_COMB (@lem2743841 m n h1 h2) (@lem2743842)). Qed.
Lemma lem2743846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2743847 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (term47 m n) = term63.
Proof. exact (MK_COMB (@lem2743846) (@lem2743843 m n h1 h2)). Qed.
Lemma lem2743853 (m : int) (h1 : (term19 m) = term20) : (term19 m) = term20.
Proof. exact (h1). Qed.
Lemma lem2743854 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2743855 (m : int) (h1 : (term19 m) = term20) : (term57 m) = term58.
Proof. exact (MK_COMB (@lem2743854) (@lem2743853 m h1)). Qed.
Lemma lem2743856 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2743857 (m : int) (h1 : (term19 m) = term20) : ((term19 m) = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2743855 m h1) (@lem2743856)). Qed.
Lemma lem2743859 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2743860 (x : int) : (x = x) = True.
Proof. exact (@lem2743859 int x). Qed.
Lemma lem2743861 : (term20 = term20) = True.
Proof. exact (@lem2743860 term20). Qed.
Lemma lem2743862 (m : int) (h1 : (term19 m) = term20) : ((term19 m) = term20) = True.
Proof. exact (TRANS (@lem2743857 m h1) (@lem2743861)). Qed.
Lemma lem2743863 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2743864 (m : int) (h1 : (term19 m) = term20) : (term42 m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem2743863) (@lem2743862 m h1)). Qed.
Lemma lem2743868 (n : int) (h1 : (term19 n) = term28) : (term19 n) = term28.
Proof. exact (h1). Qed.
Lemma lem2743869 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2743870 (n : int) (h1 : (term19 n) = term28) : (term57 n) = term64.
Proof. exact (MK_COMB (@lem2743869) (@lem2743868 n h1)). Qed.
Lemma lem2743871 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2743872 (n : int) (h1 : (term19 n) = term28) : ((term19 n) = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2743870 n h1) (@lem2743871)). Qed.
Lemma lem2743875 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (((term19 m) = term20) = ((term19 n) = term20)) = (True = (term28 = term20)).
Proof. exact (MK_COMB (@lem2743864 m h1) (@lem2743872 n h2)). Qed.
Lemma lem2743877 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem2743878 : (True = (term28 = term20)) = (term28 = term20).
Proof. exact (@lem2743877 (term28 = term20)). Qed.
Lemma lem2743881 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (((term19 m) = term20) = ((term19 n) = term20)) = (term28 = term20).
Proof. exact (TRANS (@lem2743875 m n h1 h2) (@lem2743878)). Qed.
Lemma lem2743882 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = ((term61 = term20) = (term28 = term20)).
Proof. exact (MK_COMB (@lem2743847 m n h1 h2) (@lem2743881 m n h1 h2)). Qed.
Lemma lem2743885 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : ((term61 = term20) = (term28 = term20)) = (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))).
Proof. exact (SYM (@lem2743882 m n h1 h2)). Qed.
Lemma lem2743891 (m : int) (h1 : (term19 m) = term28) : (term19 m) = term28.
Proof. exact (h1). Qed.
Lemma lem2743892 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2743893 (m : int) (h1 : (term19 m) = term28) : (term48 m) = term65.
Proof. exact (MK_COMB (@lem2743892) (@lem2743891 m h1)). Qed.
Lemma lem2743895 (n : int) (h1 : (term19 n) = term20) : (term19 n) = term20.
Proof. exact (h1). Qed.
Lemma lem2743896 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term50 m n) = term66.
Proof. exact (MK_COMB (@lem2743893 m h1) (@lem2743895 n h2)). Qed.
Lemma lem2743897 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2743898 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term52 m n) = term67.
Proof. exact (MK_COMB (@lem2743897) (@lem2743896 m n h1 h2)). Qed.
Lemma lem2743899 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2743900 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term43 m n) = term68.
Proof. exact (MK_COMB (@lem2743898 m n h1 h2) (@lem2743899)). Qed.
Lemma lem2743901 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2743902 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term46 m n) = term69.
Proof. exact (MK_COMB (@lem2743901) (@lem2743900 m n h1 h2)). Qed.
Lemma lem2743903 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2743904 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : ((term43 m n) = term20) = (term68 = term20).
Proof. exact (MK_COMB (@lem2743902 m n h1 h2) (@lem2743903)). Qed.
Lemma lem2743907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2743908 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (term47 m n) = term70.
Proof. exact (MK_COMB (@lem2743907) (@lem2743904 m n h1 h2)). Qed.
Lemma lem2743914 (m : int) (h1 : (term19 m) = term28) : (term19 m) = term28.
Proof. exact (h1). Qed.
Lemma lem2743915 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2743916 (m : int) (h1 : (term19 m) = term28) : (term57 m) = term64.
Proof. exact (MK_COMB (@lem2743915) (@lem2743914 m h1)). Qed.
Lemma lem2743917 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2743918 (m : int) (h1 : (term19 m) = term28) : ((term19 m) = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2743916 m h1) (@lem2743917)). Qed.
Lemma lem2743921 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2743922 (m : int) (h1 : (term19 m) = term28) : (term42 m) = term71.
Proof. exact (MK_COMB (@lem2743921) (@lem2743918 m h1)). Qed.
Lemma lem2743926 (n : int) (h1 : (term19 n) = term20) : (term19 n) = term20.
Proof. exact (h1). Qed.
Lemma lem2743927 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2743928 (n : int) (h1 : (term19 n) = term20) : (term57 n) = term58.
Proof. exact (MK_COMB (@lem2743927) (@lem2743926 n h1)). Qed.
Lemma lem2743929 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2743930 (n : int) (h1 : (term19 n) = term20) : ((term19 n) = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2743928 n h1) (@lem2743929)). Qed.
Lemma lem2743932 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2743933 (x : int) : (x = x) = True.
Proof. exact (@lem2743932 int x). Qed.
Lemma lem2743934 : (term20 = term20) = True.
Proof. exact (@lem2743933 term20). Qed.
Lemma lem2743935 (n : int) (h1 : (term19 n) = term20) : ((term19 n) = term20) = True.
Proof. exact (TRANS (@lem2743930 n h1) (@lem2743934)). Qed.
Lemma lem2743936 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (((term19 m) = term20) = ((term19 n) = term20)) = ((term28 = term20) = True).
Proof. exact (MK_COMB (@lem2743922 m h1) (@lem2743935 n h2)). Qed.
Lemma lem2743938 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem2743939 : ((term28 = term20) = True) = (term28 = term20).
Proof. exact (@lem2743938 (term28 = term20)). Qed.
Lemma lem2743942 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (((term19 m) = term20) = ((term19 n) = term20)) = (term28 = term20).
Proof. exact (TRANS (@lem2743936 m n h1 h2) (@lem2743939)). Qed.
Lemma lem2743943 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = ((term68 = term20) = (term28 = term20)).
Proof. exact (MK_COMB (@lem2743908 m n h1 h2) (@lem2743942 m n h1 h2)). Qed.
Lemma lem2743946 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : ((term68 = term20) = (term28 = term20)) = (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))).
Proof. exact (SYM (@lem2743943 m n h1 h2)). Qed.
Lemma lem2743952 (m : int) (h1 : (term19 m) = term28) : (term19 m) = term28.
Proof. exact (h1). Qed.
Lemma lem2743953 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2743954 (m : int) (h1 : (term19 m) = term28) : (term48 m) = term65.
Proof. exact (MK_COMB (@lem2743953) (@lem2743952 m h1)). Qed.
Lemma lem2743956 (n : int) (h1 : (term19 n) = term28) : (term19 n) = term28.
Proof. exact (h1). Qed.
Lemma lem2743957 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term50 m n) = term72.
Proof. exact (MK_COMB (@lem2743954 m h1) (@lem2743956 n h2)). Qed.
Lemma lem2743958 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2743959 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term52 m n) = term73.
Proof. exact (MK_COMB (@lem2743958) (@lem2743957 m n h1 h2)). Qed.
Lemma lem2743960 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2743961 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term43 m n) = term74.
Proof. exact (MK_COMB (@lem2743959 m n h1 h2) (@lem2743960)). Qed.
Lemma lem2743962 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2743963 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term46 m n) = term75.
Proof. exact (MK_COMB (@lem2743962) (@lem2743961 m n h1 h2)). Qed.
Lemma lem2743964 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2743965 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : ((term43 m n) = term20) = (term74 = term20).
Proof. exact (MK_COMB (@lem2743963 m n h1 h2) (@lem2743964)). Qed.
Lemma lem2743968 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2743969 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term47 m n) = term76.
Proof. exact (MK_COMB (@lem2743968) (@lem2743965 m n h1 h2)). Qed.
Lemma lem2743975 (m : int) (h1 : (term19 m) = term28) : (term19 m) = term28.
Proof. exact (h1). Qed.
Lemma lem2743976 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2743977 (m : int) (h1 : (term19 m) = term28) : (term57 m) = term64.
Proof. exact (MK_COMB (@lem2743976) (@lem2743975 m h1)). Qed.
Lemma lem2743978 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2743979 (m : int) (h1 : (term19 m) = term28) : ((term19 m) = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2743977 m h1) (@lem2743978)). Qed.
Lemma lem2743982 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2743983 (m : int) (h1 : (term19 m) = term28) : (term42 m) = term71.
Proof. exact (MK_COMB (@lem2743982) (@lem2743979 m h1)). Qed.
Lemma lem2743987 (n : int) (h1 : (term19 n) = term28) : (term19 n) = term28.
Proof. exact (h1). Qed.
Lemma lem2743988 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2743989 (n : int) (h1 : (term19 n) = term28) : (term57 n) = term64.
Proof. exact (MK_COMB (@lem2743988) (@lem2743987 n h1)). Qed.
Lemma lem2743990 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2743991 (n : int) (h1 : (term19 n) = term28) : ((term19 n) = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2743989 n h1) (@lem2743990)). Qed.
Lemma lem2743994 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (((term19 m) = term20) = ((term19 n) = term20)) = ((term28 = term20) = (term28 = term20)).
Proof. exact (MK_COMB (@lem2743983 m h1) (@lem2743991 n h2)). Qed.
Lemma lem2743996 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2743997 (x : Prop) : (x = x) = True.
Proof. exact (@lem2743996 Prop x). Qed.
Lemma lem2743998 : ((term28 = term20) = (term28 = term20)) = True.
Proof. exact (@lem2743997 (term28 = term20)). Qed.
Lemma lem2743999 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (((term19 m) = term20) = ((term19 n) = term20)) = True.
Proof. exact (TRANS (@lem2743994 m n h1 h2) (@lem2743998)). Qed.
Lemma lem2744000 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = ((term74 = term20) = True).
Proof. exact (MK_COMB (@lem2743969 m n h1 h2) (@lem2743999 m n h1 h2)). Qed.
Lemma lem2744002 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem2744003 : ((term74 = term20) = True) = (term74 = term20).
Proof. exact (@lem2744002 (term74 = term20)). Qed.
Lemma lem2744006 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))) = (term74 = term20).
Proof. exact (TRANS (@lem2744000 m n h1 h2) (@lem2744003)). Qed.
Lemma lem2744007 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : (term74 = term20) = (((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20))).
Proof. exact (SYM (@lem2744006 m n h1 h2)). Qed.
Lemma lem2744008 : term51 = term77.
Proof. exact (@lem2406280 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2744009 : (Nat.add 0 0) = 0.
Proof. exact (@lem706819). Qed.
Lemma lem2744010 : ((Nat.add 0 0) = 0) = (term78 = (NUMERAL 0)).
Proof. exact (@lem1006570 0 0 0). Qed.
Lemma lem2744011 : term78 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem2744010) (@lem2744009)). Qed.
Lemma lem2744012 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2744013 : term77 = term20.
Proof. exact (MK_COMB (@lem2744012) (@lem2744011)). Qed.
Lemma lem2744014 : term51 = term20.
Proof. exact (TRANS (@lem2744008) (@lem2744013)). Qed.
Lemma lem2744015 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2744016 : term53 = term79.
Proof. exact (MK_COMB (@lem2744015) (@lem2744014)). Qed.
Lemma lem2744017 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2744018 : term54 = term80.
Proof. exact (MK_COMB (@lem2744016) (@lem2744017)). Qed.
Lemma lem2744019 : term81.
Proof. exact (@lem2743639 term20 term20 term44 term20). Qed.
Lemma lem2744021 (x : nat) : (term82 x) = term20.
Proof. exact (proj1 (@lem2405621 x)). Qed.
Lemma lem2744022 : term83 = term20.
Proof. exact (@lem2744021 term84). Qed.
Lemma lem2744023 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2744024 : term85 = term49.
Proof. exact (MK_COMB (@lem2744023) (@lem2744022)). Qed.
Lemma lem2744025 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744026 : term86 = term51.
Proof. exact (MK_COMB (@lem2744024) (@lem2744025)). Qed.
Lemma lem2744027 : term51 = term77.
Proof. exact (@lem2406280 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2744028 : (Nat.add 0 0) = 0.
Proof. exact (@lem706819). Qed.
Lemma lem2744029 : ((Nat.add 0 0) = 0) = (term78 = (NUMERAL 0)).
Proof. exact (@lem1006570 0 0 0). Qed.
Lemma lem2744030 : term78 = (NUMERAL 0).
Proof. exact (EQ_MP (@lem2744029) (@lem2744028)). Qed.
Lemma lem2744031 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2744032 : term77 = term20.
Proof. exact (MK_COMB (@lem2744031) (@lem2744030)). Qed.
Lemma lem2744033 : term51 = term20.
Proof. exact (TRANS (@lem2744027) (@lem2744032)). Qed.
Lemma lem2744034 : term86 = term20.
Proof. exact (TRANS (@lem2744026) (@lem2744033)). Qed.
Lemma lem2744035 : term87.
Proof. exact (@lem2744019 (@lem2744034)). Qed.
Lemma lem2744037 (m : nat) (n : nat) : (term88 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem2403914 m n)). Qed.
Lemma lem2744038 : term89 = term90.
Proof. exact (@lem2744037 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2744039 : term90 = True.
Proof. exact (@lem1011992 0). Qed.
Lemma lem2744040 : term89 = True.
Proof. exact (TRANS (@lem2744038) (@lem2744039)). Qed.
Lemma lem2744041 : True = term89.
Proof. exact (SYM (@lem2744040)). Qed.
Lemma lem2744042 : term89.
Proof. exact (EQ_MP (@lem2744041) (@lem0)). Qed.
Lemma lem2744043 : term91.
Proof. exact (@lem2744035 (@lem2744042)). Qed.
Lemma lem2744045 (x : nat) : (term92 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem2744046 : term93 = term44.
Proof. exact (@lem2744045 term84). Qed.
Lemma lem2744047 : term94 = term94.
Proof. exact (eq_refl term94). Qed.
Lemma lem2744048 : term95 = term96.
Proof. exact (MK_COMB (@lem2744047) (@lem2744046)). Qed.
Lemma lem2744050 (m : nat) (n : nat) : (term97 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem2404231 m n)). Qed.
Lemma lem2744051 : term96 = term98.
Proof. exact (@lem2744050 (NUMERAL 0) term84). Qed.
Lemma lem2744052 : term99 = term100.
Proof. exact (@lem912803). Qed.
Lemma lem2744053 (h1 : term99 = term100) : term98 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term100 h1). Qed.
Lemma lem2744054 : (term99 = term100) = (term98 = True).
Proof. exact (prop_ext (fun h1 : term99 = term100 => @lem2744053 h1) (fun h1 : term98 = True => @lem2744052)). Qed.
Lemma lem2744055 : term98 = True.
Proof. exact (EQ_MP (@lem2744054) (@lem2744052)). Qed.
Lemma lem2744056 : term96 = True.
Proof. exact (TRANS (@lem2744051) (@lem2744055)). Qed.
Lemma lem2744057 : term95 = True.
Proof. exact (TRANS (@lem2744048) (@lem2744056)). Qed.
Lemma lem2744058 : True = term95.
Proof. exact (SYM (@lem2744057)). Qed.
Lemma lem2744059 : term95.
Proof. exact (EQ_MP (@lem2744058) (@lem0)). Qed.
Lemma lem2744060 : term101.
Proof. exact (@lem2744043 (@lem2744059)). Qed.
Lemma lem2744061 : term80 = term20.
Proof. exact (proj2 (@lem2744060)). Qed.
Lemma lem2744062 : term54 = term20.
Proof. exact (TRANS (@lem2744018) (@lem2744061)). Qed.
Lemma lem2744063 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744064 : term55 = term58.
Proof. exact (MK_COMB (@lem2744063) (@lem2744062)). Qed.
Lemma lem2744065 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744066 : (term54 = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2744064) (@lem2744065)). Qed.
Lemma lem2744068 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2744069 (x : int) : (x = x) = True.
Proof. exact (@lem2744068 int x). Qed.
Lemma lem2744070 : (term20 = term20) = True.
Proof. exact (@lem2744069 term20). Qed.
Lemma lem2744071 : (term54 = term20) = True.
Proof. exact (TRANS (@lem2744066) (@lem2744070)). Qed.
Lemma lem2744072 : True = (term54 = term20).
Proof. exact (SYM (@lem2744071)). Qed.
Lemma lem2744073 : term54 = term20.
Proof. exact (EQ_MP (@lem2744072) (@lem0)). Qed.
Lemma lem2744074 : term59 = term102.
Proof. exact (@lem2406280 (NUMERAL 0) term103). Qed.
Lemma lem2744075 : term104 = (BIT1 0).
Proof. exact (@lem706821). Qed.
Lemma lem2744076 : (term104 = (BIT1 0)) = (term105 = term103).
Proof. exact (@lem1006570 0 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2744077 : term105 = term103.
Proof. exact (EQ_MP (@lem2744076) (@lem2744075)). Qed.
Lemma lem2744078 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2744079 : term102 = term28.
Proof. exact (MK_COMB (@lem2744078) (@lem2744077)). Qed.
Lemma lem2744080 : term59 = term28.
Proof. exact (TRANS (@lem2744074) (@lem2744079)). Qed.
Lemma lem2744081 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2744082 : term60 = term106.
Proof. exact (MK_COMB (@lem2744081) (@lem2744080)). Qed.
Lemma lem2744083 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2744084 : term61 = term107.
Proof. exact (MK_COMB (@lem2744082) (@lem2744083)). Qed.
Lemma lem2744085 : term108.
Proof. exact (@lem2743639 term20 term28 term44 term28). Qed.
Lemma lem2744087 (x : nat) : (term82 x) = term20.
Proof. exact (proj1 (@lem2405621 x)). Qed.
Lemma lem2744088 : term83 = term20.
Proof. exact (@lem2744087 term84). Qed.
Lemma lem2744089 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2744090 : term85 = term49.
Proof. exact (MK_COMB (@lem2744089) (@lem2744088)). Qed.
Lemma lem2744091 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem2744092 : term109 = term59.
Proof. exact (MK_COMB (@lem2744090) (@lem2744091)). Qed.
Lemma lem2744093 : term59 = term102.
Proof. exact (@lem2406280 (NUMERAL 0) term103). Qed.
Lemma lem2744094 : term104 = (BIT1 0).
Proof. exact (@lem706821). Qed.
Lemma lem2744095 : (term104 = (BIT1 0)) = (term105 = term103).
Proof. exact (@lem1006570 0 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2744096 : term105 = term103.
Proof. exact (EQ_MP (@lem2744095) (@lem2744094)). Qed.
Lemma lem2744097 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2744098 : term102 = term28.
Proof. exact (MK_COMB (@lem2744097) (@lem2744096)). Qed.
Lemma lem2744099 : term59 = term28.
Proof. exact (TRANS (@lem2744093) (@lem2744098)). Qed.
Lemma lem2744100 : term109 = term28.
Proof. exact (TRANS (@lem2744092) (@lem2744099)). Qed.
Lemma lem2744101 : term110.
Proof. exact (@lem2744085 (@lem2744100)). Qed.
Lemma lem2744103 (m : nat) (n : nat) : (term88 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem2403914 m n)). Qed.
Lemma lem2744104 : term111 = term112.
Proof. exact (@lem2744103 (NUMERAL 0) term103). Qed.
Lemma lem2744105 : term113 = (BIT1 0).
Proof. exact (@lem706883). Qed.
Lemma lem2744106 (h1 : term113 = (BIT1 0)) : term112 = True.
Proof. exact (@lem1011471 (BIT1 0) 0 (BIT1 0) h1). Qed.
Lemma lem2744107 : (term113 = (BIT1 0)) = (term112 = True).
Proof. exact (prop_ext (fun h1 : term113 = (BIT1 0) => @lem2744106 h1) (fun h1 : term112 = True => @lem2744105)). Qed.
Lemma lem2744108 : term112 = True.
Proof. exact (EQ_MP (@lem2744107) (@lem2744105)). Qed.
Lemma lem2744109 : term111 = True.
Proof. exact (TRANS (@lem2744104) (@lem2744108)). Qed.
Lemma lem2744110 : True = term111.
Proof. exact (SYM (@lem2744109)). Qed.
Lemma lem2744111 : term111.
Proof. exact (EQ_MP (@lem2744110) (@lem0)). Qed.
Lemma lem2744112 : term114.
Proof. exact (@lem2744101 (@lem2744111)). Qed.
Lemma lem2744114 (x : nat) : (term92 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem2744115 : term93 = term44.
Proof. exact (@lem2744114 term84). Qed.
Lemma lem2744116 : term115 = term115.
Proof. exact (eq_refl term115). Qed.
Lemma lem2744117 : term116 = term117.
Proof. exact (MK_COMB (@lem2744116) (@lem2744115)). Qed.
Lemma lem2744119 (m : nat) (n : nat) : (term97 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem2404231 m n)). Qed.
Lemma lem2744120 : term117 = term118.
Proof. exact (@lem2744119 term103 term84). Qed.
Lemma lem2744121 : term119 = term100.
Proof. exact (@lem912741). Qed.
Lemma lem2744122 (h1 : term119 = term100) : term118 = True.
Proof. exact (@lem1009824 0 (BIT1 0) term100 h1). Qed.
Lemma lem2744123 : (term119 = term100) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = term100 => @lem2744122 h1) (fun h1 : term118 = True => @lem2744121)). Qed.
Lemma lem2744124 : term118 = True.
Proof. exact (EQ_MP (@lem2744123) (@lem2744121)). Qed.
Lemma lem2744125 : term117 = True.
Proof. exact (TRANS (@lem2744120) (@lem2744124)). Qed.
Lemma lem2744126 : term116 = True.
Proof. exact (TRANS (@lem2744117) (@lem2744125)). Qed.
Lemma lem2744127 : True = term116.
Proof. exact (SYM (@lem2744126)). Qed.
Lemma lem2744128 : term116.
Proof. exact (EQ_MP (@lem2744127) (@lem0)). Qed.
Lemma lem2744129 : term120.
Proof. exact (@lem2744112 (@lem2744128)). Qed.
Lemma lem2744130 : term107 = term28.
Proof. exact (proj2 (@lem2744129)). Qed.
Lemma lem2744131 : term61 = term28.
Proof. exact (TRANS (@lem2744084) (@lem2744130)). Qed.
Lemma lem2744132 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744133 : term62 = term64.
Proof. exact (MK_COMB (@lem2744132) (@lem2744131)). Qed.
Lemma lem2744134 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744135 : (term61 = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2744133) (@lem2744134)). Qed.
Lemma lem2744139 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (proj1 (@lem2405481 m n)). Qed.
Lemma lem2744140 : (term28 = term20) = (term103 = (NUMERAL 0)).
Proof. exact (@lem2744139 term103 (NUMERAL 0)). Qed.
Lemma lem2744141 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2744142 (h1 : term121 = (BIT1 0)) : (term103 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2744143 : (term121 = (BIT1 0)) = ((term103 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem2744142 h1) (fun h1 : (term103 = (NUMERAL 0)) = False => @lem2744141)). Qed.
Lemma lem2744144 : (term103 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2744143) (@lem2744141)). Qed.
Lemma lem2744145 : (term28 = term20) = False.
Proof. exact (TRANS (@lem2744140) (@lem2744144)). Qed.
Lemma lem2744146 : (term61 = term20) = False.
Proof. exact (TRANS (@lem2744135) (@lem2744145)). Qed.
Lemma lem2744147 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2744148 : term63 = (@eq Prop False).
Proof. exact (MK_COMB (@lem2744147) (@lem2744146)). Qed.
Lemma lem2744152 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (proj1 (@lem2405481 m n)). Qed.
Lemma lem2744153 : (term28 = term20) = (term103 = (NUMERAL 0)).
Proof. exact (@lem2744152 term103 (NUMERAL 0)). Qed.
Lemma lem2744154 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2744155 (h1 : term121 = (BIT1 0)) : (term103 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2744156 : (term121 = (BIT1 0)) = ((term103 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem2744155 h1) (fun h1 : (term103 = (NUMERAL 0)) = False => @lem2744154)). Qed.
Lemma lem2744157 : (term103 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2744156) (@lem2744154)). Qed.
Lemma lem2744158 : (term28 = term20) = False.
Proof. exact (TRANS (@lem2744153) (@lem2744157)). Qed.
Lemma lem2744159 : ((term61 = term20) = (term28 = term20)) = (False = False).
Proof. exact (MK_COMB (@lem2744148) (@lem2744158)). Qed.
Lemma lem2744161 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem2744162 : (False = False) = (~ False).
Proof. exact (@lem2744161 False). Qed.
Lemma lem2744164 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2744165 : (False = False) = True.
Proof. exact (TRANS (@lem2744162) (@lem2744164)). Qed.
Lemma lem2744166 : ((term61 = term20) = (term28 = term20)) = True.
Proof. exact (TRANS (@lem2744159) (@lem2744165)). Qed.
Lemma lem2744167 : True = ((term61 = term20) = (term28 = term20)).
Proof. exact (SYM (@lem2744166)). Qed.
Lemma lem2744168 : (term61 = term20) = (term28 = term20).
Proof. exact (EQ_MP (@lem2744167) (@lem0)). Qed.
Lemma lem2744169 : term66 = term122.
Proof. exact (@lem2406280 term103 (NUMERAL 0)). Qed.
Lemma lem2744170 : term113 = (BIT1 0).
Proof. exact (@lem706883). Qed.
Lemma lem2744171 : (term113 = (BIT1 0)) = (term123 = term103).
Proof. exact (@lem1006570 (BIT1 0) 0 (BIT1 0)). Qed.
Lemma lem2744172 : term123 = term103.
Proof. exact (EQ_MP (@lem2744171) (@lem2744170)). Qed.
Lemma lem2744173 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2744174 : term122 = term28.
Proof. exact (MK_COMB (@lem2744173) (@lem2744172)). Qed.
Lemma lem2744175 : term66 = term28.
Proof. exact (TRANS (@lem2744169) (@lem2744174)). Qed.
Lemma lem2744176 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2744177 : term67 = term106.
Proof. exact (MK_COMB (@lem2744176) (@lem2744175)). Qed.
Lemma lem2744178 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2744179 : term68 = term107.
Proof. exact (MK_COMB (@lem2744177) (@lem2744178)). Qed.
Lemma lem2744180 : term108.
Proof. exact (@lem2743639 term20 term28 term44 term28). Qed.
Lemma lem2744182 (x : nat) : (term82 x) = term20.
Proof. exact (proj1 (@lem2405621 x)). Qed.
Lemma lem2744183 : term83 = term20.
Proof. exact (@lem2744182 term84). Qed.
Lemma lem2744184 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2744185 : term85 = term49.
Proof. exact (MK_COMB (@lem2744184) (@lem2744183)). Qed.
Lemma lem2744186 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem2744187 : term109 = term59.
Proof. exact (MK_COMB (@lem2744185) (@lem2744186)). Qed.
Lemma lem2744188 : term59 = term102.
Proof. exact (@lem2406280 (NUMERAL 0) term103). Qed.
Lemma lem2744189 : term104 = (BIT1 0).
Proof. exact (@lem706821). Qed.
Lemma lem2744190 : (term104 = (BIT1 0)) = (term105 = term103).
Proof. exact (@lem1006570 0 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2744191 : term105 = term103.
Proof. exact (EQ_MP (@lem2744190) (@lem2744189)). Qed.
Lemma lem2744192 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2744193 : term102 = term28.
Proof. exact (MK_COMB (@lem2744192) (@lem2744191)). Qed.
Lemma lem2744194 : term59 = term28.
Proof. exact (TRANS (@lem2744188) (@lem2744193)). Qed.
Lemma lem2744195 : term109 = term28.
Proof. exact (TRANS (@lem2744187) (@lem2744194)). Qed.
Lemma lem2744196 : term110.
Proof. exact (@lem2744180 (@lem2744195)). Qed.
Lemma lem2744198 (m : nat) (n : nat) : (term88 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem2403914 m n)). Qed.
Lemma lem2744199 : term111 = term112.
Proof. exact (@lem2744198 (NUMERAL 0) term103). Qed.
Lemma lem2744200 : term113 = (BIT1 0).
Proof. exact (@lem706883). Qed.
Lemma lem2744201 (h1 : term113 = (BIT1 0)) : term112 = True.
Proof. exact (@lem1011471 (BIT1 0) 0 (BIT1 0) h1). Qed.
Lemma lem2744202 : (term113 = (BIT1 0)) = (term112 = True).
Proof. exact (prop_ext (fun h1 : term113 = (BIT1 0) => @lem2744201 h1) (fun h1 : term112 = True => @lem2744200)). Qed.
Lemma lem2744203 : term112 = True.
Proof. exact (EQ_MP (@lem2744202) (@lem2744200)). Qed.
Lemma lem2744204 : term111 = True.
Proof. exact (TRANS (@lem2744199) (@lem2744203)). Qed.
Lemma lem2744205 : True = term111.
Proof. exact (SYM (@lem2744204)). Qed.
Lemma lem2744206 : term111.
Proof. exact (EQ_MP (@lem2744205) (@lem0)). Qed.
Lemma lem2744207 : term114.
Proof. exact (@lem2744196 (@lem2744206)). Qed.
Lemma lem2744209 (x : nat) : (term92 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem2744210 : term93 = term44.
Proof. exact (@lem2744209 term84). Qed.
Lemma lem2744211 : term115 = term115.
Proof. exact (eq_refl term115). Qed.
Lemma lem2744212 : term116 = term117.
Proof. exact (MK_COMB (@lem2744211) (@lem2744210)). Qed.
Lemma lem2744214 (m : nat) (n : nat) : (term97 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem2404231 m n)). Qed.
Lemma lem2744215 : term117 = term118.
Proof. exact (@lem2744214 term103 term84). Qed.
Lemma lem2744216 : term119 = term100.
Proof. exact (@lem912741). Qed.
Lemma lem2744217 (h1 : term119 = term100) : term118 = True.
Proof. exact (@lem1009824 0 (BIT1 0) term100 h1). Qed.
Lemma lem2744218 : (term119 = term100) = (term118 = True).
Proof. exact (prop_ext (fun h1 : term119 = term100 => @lem2744217 h1) (fun h1 : term118 = True => @lem2744216)). Qed.
Lemma lem2744219 : term118 = True.
Proof. exact (EQ_MP (@lem2744218) (@lem2744216)). Qed.
Lemma lem2744220 : term117 = True.
Proof. exact (TRANS (@lem2744215) (@lem2744219)). Qed.
Lemma lem2744221 : term116 = True.
Proof. exact (TRANS (@lem2744212) (@lem2744220)). Qed.
Lemma lem2744222 : True = term116.
Proof. exact (SYM (@lem2744221)). Qed.
Lemma lem2744223 : term116.
Proof. exact (EQ_MP (@lem2744222) (@lem0)). Qed.
Lemma lem2744224 : term120.
Proof. exact (@lem2744207 (@lem2744223)). Qed.
Lemma lem2744225 : term107 = term28.
Proof. exact (proj2 (@lem2744224)). Qed.
Lemma lem2744226 : term68 = term28.
Proof. exact (TRANS (@lem2744179) (@lem2744225)). Qed.
Lemma lem2744227 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744228 : term69 = term64.
Proof. exact (MK_COMB (@lem2744227) (@lem2744226)). Qed.
Lemma lem2744229 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744230 : (term68 = term20) = (term28 = term20).
Proof. exact (MK_COMB (@lem2744228) (@lem2744229)). Qed.
Lemma lem2744234 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (proj1 (@lem2405481 m n)). Qed.
Lemma lem2744235 : (term28 = term20) = (term103 = (NUMERAL 0)).
Proof. exact (@lem2744234 term103 (NUMERAL 0)). Qed.
Lemma lem2744236 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2744237 (h1 : term121 = (BIT1 0)) : (term103 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2744238 : (term121 = (BIT1 0)) = ((term103 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem2744237 h1) (fun h1 : (term103 = (NUMERAL 0)) = False => @lem2744236)). Qed.
Lemma lem2744239 : (term103 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2744238) (@lem2744236)). Qed.
Lemma lem2744240 : (term28 = term20) = False.
Proof. exact (TRANS (@lem2744235) (@lem2744239)). Qed.
Lemma lem2744241 : (term68 = term20) = False.
Proof. exact (TRANS (@lem2744230) (@lem2744240)). Qed.
Lemma lem2744242 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2744243 : term70 = (@eq Prop False).
Proof. exact (MK_COMB (@lem2744242) (@lem2744241)). Qed.
Lemma lem2744247 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (proj1 (@lem2405481 m n)). Qed.
Lemma lem2744248 : (term28 = term20) = (term103 = (NUMERAL 0)).
Proof. exact (@lem2744247 term103 (NUMERAL 0)). Qed.
Lemma lem2744249 : term121 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2744250 (h1 : term121 = (BIT1 0)) : (term103 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2744251 : (term121 = (BIT1 0)) = ((term103 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term121 = (BIT1 0) => @lem2744250 h1) (fun h1 : (term103 = (NUMERAL 0)) = False => @lem2744249)). Qed.
Lemma lem2744252 : (term103 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2744251) (@lem2744249)). Qed.
Lemma lem2744253 : (term28 = term20) = False.
Proof. exact (TRANS (@lem2744248) (@lem2744252)). Qed.
Lemma lem2744254 : ((term68 = term20) = (term28 = term20)) = (False = False).
Proof. exact (MK_COMB (@lem2744243) (@lem2744253)). Qed.
Lemma lem2744256 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem2744257 : (False = False) = (~ False).
Proof. exact (@lem2744256 False). Qed.
Lemma lem2744259 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2744260 : (False = False) = True.
Proof. exact (TRANS (@lem2744257) (@lem2744259)). Qed.
Lemma lem2744261 : ((term68 = term20) = (term28 = term20)) = True.
Proof. exact (TRANS (@lem2744254) (@lem2744260)). Qed.
Lemma lem2744262 : True = ((term68 = term20) = (term28 = term20)).
Proof. exact (SYM (@lem2744261)). Qed.
Lemma lem2744263 : (term68 = term20) = (term28 = term20).
Proof. exact (EQ_MP (@lem2744262) (@lem0)). Qed.
Lemma lem2744264 : term72 = term124.
Proof. exact (@lem2406280 term103 term103). Qed.
Lemma lem2744265 : term125 = term100.
Proof. exact (@lem706885). Qed.
Lemma lem2744266 : (term125 = term100) = (term126 = term84).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term100). Qed.
Lemma lem2744267 : term126 = term84.
Proof. exact (EQ_MP (@lem2744266) (@lem2744265)). Qed.
Lemma lem2744268 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2744269 : term124 = term44.
Proof. exact (MK_COMB (@lem2744268) (@lem2744267)). Qed.
Lemma lem2744270 : term72 = term44.
Proof. exact (TRANS (@lem2744264) (@lem2744269)). Qed.
Lemma lem2744271 : rem = rem.
Proof. exact (eq_refl rem). Qed.
Lemma lem2744272 : term73 = term127.
Proof. exact (MK_COMB (@lem2744271) (@lem2744270)). Qed.
Lemma lem2744273 : term44 = term44.
Proof. exact (eq_refl term44). Qed.
Lemma lem2744274 : term74 = term128.
Proof. exact (MK_COMB (@lem2744272) (@lem2744273)). Qed.
Lemma lem2744275 : term129.
Proof. exact (@lem2743639 term28 term44 term44 term20). Qed.
Lemma lem2744277 (m : nat) (n : nat) : (term130 m n) = (term131 m n).
Proof. exact (proj1 (@lem2405758 m n)). Qed.
Lemma lem2744278 : term132 = term133.
Proof. exact (@lem2744277 term103 term84). Qed.
Lemma lem2744279 : term134 = term100.
Proof. exact (@lem996238 term100). Qed.
Lemma lem2744280 : (term134 = term100) = (term135 = term84).
Proof. exact (@lem1007663 (BIT1 0) term100 term100). Qed.
Lemma lem2744281 : term135 = term84.
Proof. exact (EQ_MP (@lem2744280) (@lem2744279)). Qed.
Lemma lem2744282 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2744283 : term133 = term44.
Proof. exact (MK_COMB (@lem2744282) (@lem2744281)). Qed.
Lemma lem2744284 : term132 = term44.
Proof. exact (TRANS (@lem2744278) (@lem2744283)). Qed.
Lemma lem2744285 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2744286 : term136 = term137.
Proof. exact (MK_COMB (@lem2744285) (@lem2744284)). Qed.
Lemma lem2744287 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744288 : term138 = term139.
Proof. exact (MK_COMB (@lem2744286) (@lem2744287)). Qed.
Lemma lem2744289 : term139 = term140.
Proof. exact (@lem2406280 term84 (NUMERAL 0)). Qed.
Lemma lem2744290 : term141 = term100.
Proof. exact (@lem706947). Qed.
Lemma lem2744291 : (term141 = term100) = (term142 = term84).
Proof. exact (@lem1006570 term100 0 term100). Qed.
Lemma lem2744292 : term142 = term84.
Proof. exact (EQ_MP (@lem2744291) (@lem2744290)). Qed.
Lemma lem2744293 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2744294 : term140 = term44.
Proof. exact (MK_COMB (@lem2744293) (@lem2744292)). Qed.
Lemma lem2744295 : term139 = term44.
Proof. exact (TRANS (@lem2744289) (@lem2744294)). Qed.
Lemma lem2744296 : term138 = term44.
Proof. exact (TRANS (@lem2744288) (@lem2744295)). Qed.
Lemma lem2744297 : term143.
Proof. exact (@lem2744275 (@lem2744296)). Qed.
Lemma lem2744299 (m : nat) (n : nat) : (term88 m n) = (Peano.le m n).
Proof. exact (proj1 (@lem2403914 m n)). Qed.
Lemma lem2744300 : term89 = term90.
Proof. exact (@lem2744299 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2744301 : term90 = True.
Proof. exact (@lem1011992 0). Qed.
Lemma lem2744302 : term89 = True.
Proof. exact (TRANS (@lem2744300) (@lem2744301)). Qed.
Lemma lem2744303 : True = term89.
Proof. exact (SYM (@lem2744302)). Qed.
Lemma lem2744304 : term89.
Proof. exact (EQ_MP (@lem2744303) (@lem0)). Qed.
Lemma lem2744305 : term144.
Proof. exact (@lem2744297 (@lem2744304)). Qed.
Lemma lem2744307 (x : nat) : (term92 x) = (int_of_num x).
Proof. exact (proj2 (@lem2406442 x)). Qed.
Lemma lem2744308 : term93 = term44.
Proof. exact (@lem2744307 term84). Qed.
Lemma lem2744309 : term94 = term94.
Proof. exact (eq_refl term94). Qed.
Lemma lem2744310 : term95 = term96.
Proof. exact (MK_COMB (@lem2744309) (@lem2744308)). Qed.
Lemma lem2744312 (m : nat) (n : nat) : (term97 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem2404231 m n)). Qed.
Lemma lem2744313 : term96 = term98.
Proof. exact (@lem2744312 (NUMERAL 0) term84). Qed.
Lemma lem2744314 : term99 = term100.
Proof. exact (@lem912803). Qed.
Lemma lem2744315 (h1 : term99 = term100) : term98 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term100 h1). Qed.
Lemma lem2744316 : (term99 = term100) = (term98 = True).
Proof. exact (prop_ext (fun h1 : term99 = term100 => @lem2744315 h1) (fun h1 : term98 = True => @lem2744314)). Qed.
Lemma lem2744317 : term98 = True.
Proof. exact (EQ_MP (@lem2744316) (@lem2744314)). Qed.
Lemma lem2744318 : term96 = True.
Proof. exact (TRANS (@lem2744313) (@lem2744317)). Qed.
Lemma lem2744319 : term95 = True.
Proof. exact (TRANS (@lem2744310) (@lem2744318)). Qed.
Lemma lem2744320 : True = term95.
Proof. exact (SYM (@lem2744319)). Qed.
Lemma lem2744321 : term95.
Proof. exact (EQ_MP (@lem2744320) (@lem0)). Qed.
Lemma lem2744322 : term145.
Proof. exact (@lem2744305 (@lem2744321)). Qed.
Lemma lem2744323 : term128 = term20.
Proof. exact (proj2 (@lem2744322)). Qed.
Lemma lem2744324 : term74 = term20.
Proof. exact (TRANS (@lem2744274) (@lem2744323)). Qed.
Lemma lem2744325 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2744326 : term75 = term58.
Proof. exact (MK_COMB (@lem2744325) (@lem2744324)). Qed.
Lemma lem2744327 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem2744328 : (term74 = term20) = (term20 = term20).
Proof. exact (MK_COMB (@lem2744326) (@lem2744327)). Qed.
Lemma lem2744330 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2744331 (x : int) : (x = x) = True.
Proof. exact (@lem2744330 int x). Qed.
Lemma lem2744332 : (term20 = term20) = True.
Proof. exact (@lem2744331 term20). Qed.
Lemma lem2744333 : (term74 = term20) = True.
Proof. exact (TRANS (@lem2744328) (@lem2744332)). Qed.
Lemma lem2744334 : True = (term74 = term20).
Proof. exact (SYM (@lem2744333)). Qed.
Lemma lem2744335 : term74 = term20.
Proof. exact (EQ_MP (@lem2744334) (@lem0)). Qed.
Lemma lem2744336 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term28) : ((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (EQ_MP (@lem2744007 m n h1 h2) (@lem2744335)). Qed.
Lemma lem2744337 (m : int) (n : int) (h1 : (term19 m) = term28) (h2 : (term19 n) = term20) : ((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (EQ_MP (@lem2743946 m n h1 h2) (@lem2744263)). Qed.
Lemma lem2744338 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term28) : ((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (EQ_MP (@lem2743885 m n h1 h2) (@lem2744168)). Qed.
Lemma lem2744339 (m : int) (n : int) (h1 : (term19 m) = term20) (h2 : (term19 n) = term20) : ((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (EQ_MP (@lem2743824 m n h1 h2) (@lem2744073)). Qed.
Lemma lem2744340 (n : int) (m : int) (h1 : (term19 m) = term28) : ((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (or_elim (@lem2743642 n) (fun h0 : (term19 n) = term20 => @lem2744337 m n h1 h0) (fun h0 : (term19 n) = term28 => @lem2744336 m n h1 h0)). Qed.
Lemma lem2744341 (n : int) (m : int) (h1 : (term19 m) = term20) : ((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (or_elim (@lem2743642 n) (fun h0 : (term19 n) = term20 => @lem2744339 m n h1 h0) (fun h0 : (term19 n) = term28 => @lem2744338 m n h1 h0)). Qed.
Lemma lem2744342 (m : int) (n : int) : ((term43 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (or_elim (@lem2743647 m) (fun h0 : (term19 m) = term20 => @lem2744341 n m h0) (fun h0 : (term19 m) = term28 => @lem2744340 n m h0)). Qed.
Lemma lem2744343 (m : int) (n : int) : ((term38 m n) = term20) = (((term19 m) = term20) = ((term19 n) = term20)).
Proof. exact (EQ_MP (@lem2743758 m n) (@lem2744342 m n)). Qed.
Lemma lem2744344 (m : int) (n : int) : (term37 m n) = ((term21 m) = (term21 n)).
Proof. exact (EQ_MP (@lem2743736 m n) (@lem2744343 m n)). Qed.
Lemma lem2744349 (m : int) : term146 m.
Proof. exact (fun n : int => @lem2744344 m n). Qed.
Lemma lem2744354 : term147.
Proof. exact (fun m : int => @lem2744349 m). Qed.
