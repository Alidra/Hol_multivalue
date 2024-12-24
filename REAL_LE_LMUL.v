Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_LMUL_term_abbrevs.
Require Import REAL_SUB_LDISTRIB_spec.
Require Import REAL_SUB_RZERO_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1340049_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1582671 (y : real) (x : real) (z : real) (h1 : (term0 x y z) = (term1 y x z)) : (term0 x y z) = (term1 y x z).
Proof. exact (h1). Qed.
Lemma lem1582672 (y : real) (x : real) (z : real) (h1 : (term0 x y z) = (term1 y x z)) : (term1 y x z) = (term0 x y z).
Proof. exact (SYM (@lem1582671 y x z h1)). Qed.
Lemma lem1582673 (x : real) (y : real) (z : real) (h1 : (term1 y x z) = (term0 x y z)) : (term1 y x z) = (term0 x y z).
Proof. exact (h1). Qed.
Lemma lem1582674 (x : real) (y : real) (z : real) (h1 : (term1 y x z) = (term0 x y z)) : (term0 x y z) = (term1 y x z).
Proof. exact (SYM (@lem1582673 x y z h1)). Qed.
Lemma lem1582675 (x : real) (y : real) (z : real) : ((term0 x y z) = (term1 y x z)) = ((term1 y x z) = (term0 x y z)).
Proof. exact (prop_ext (fun h1 : (term0 x y z) = (term1 y x z) => @lem1582672 y x z h1) (fun h1 : (term1 y x z) = (term0 x y z) => @lem1582674 x y z h1)). Qed.
Lemma lem1582676 (x : real) (y : real) : (term2 y x) = (term3 x y).
Proof. exact (fun_ext (fun z : real => @lem1582675 x y z)). Qed.
Lemma lem1582677 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1582678 (x : real) (y : real) : (term4 y x) = (term5 x y).
Proof. exact (MK_COMB (@lem1582677) (@lem1582676 x y)). Qed.
Lemma lem1582679 (x : real) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : real => @lem1582678 x y)). Qed.
Lemma lem1582680 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1582681 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1582680) (@lem1582679 x)). Qed.
Lemma lem1582682 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem1582681 x)). Qed.
Lemma lem1582683 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1582684 : term12 = term13.
Proof. exact (MK_COMB (@lem1582683) (@lem1582682)). Qed.
Lemma lem1582685 : term13.
Proof. exact (EQ_MP (@lem1582684) (@lem1526444)). Qed.
Lemma lem1582686 (x : real) : term14 x.
Proof. exact (@lem1340049 x). Qed.
Lemma lem1582687 (x : real) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1582688 (x : real) : term15 x.
Proof. exact (EQ_MP (@lem1582687 x) (@lem1582686 x)). Qed.
Lemma lem1582689 (x : real) (y : real) : term16 x y.
Proof. exact (@lem1582688 x y). Qed.
Lemma lem1582690 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1582691 (x : real) (y : real) : term17 x y.
Proof. exact (EQ_MP (@lem1582690 x y) (@lem1582689 x y)). Qed.
Lemma lem1582692 (x : real) (y : real) : (term17 x y) = ((term17 x y) = True).
Proof. exact (@lem7 (term17 x y)). Qed.
Lemma lem1582694 (x : real) : term18 x.
Proof. exact (@lem1518006 x). Qed.
Lemma lem1582695 (x : real) : (term18 x) = ((term19 x) = x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1582697 (x : real) : term20 x.
Proof. exact (@lem1582685 x). Qed.
Lemma lem1582698 (x : real) : (term20 x) = (term9 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1582699 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1582698 x) (@lem1582697 x)). Qed.
Lemma lem1582700 (x : real) (y : real) : term21 x y.
Proof. exact (@lem1582699 x y). Qed.
Lemma lem1582701 (x : real) (y : real) : (term21 x y) = (term5 x y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1582702 (x : real) (y : real) : term5 x y.
Proof. exact (EQ_MP (@lem1582701 x y) (@lem1582700 x y)). Qed.
Lemma lem1582703 (x : real) (y : real) (z : real) : term22 x y z.
Proof. exact (@lem1582702 x y z). Qed.
Lemma lem1582704 (x : real) (y : real) (z : real) : (term22 x y z) = ((term1 y x z) = (term0 x y z)).
Proof. exact (eq_refl (term22 x y z)). Qed.
Lemma lem1582742 (y : real) (x : real) : (term23 y x) = (term24 y x).
Proof. exact (@lem17646 (real_le x y) (term25 y x)). Qed.
Lemma lem1582743 (y : real) (x : real) : (real_le x y) = (term26 y x).
Proof. exact (@lem1483523 y x). Qed.
Lemma lem1582749 (y : real) (x : real) : (real_sub y x) = (term27 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1582754 (x : real) (y : real) : (term27 y x) = (term28 x y).
Proof. exact (@lem1483488 (term29 x) y). Qed.
Lemma lem1582756 (x : real) (y : real) : (real_sub y x) = (term28 x y).
Proof. exact (TRANS (@lem1582749 y x) (@lem1582754 x y)). Qed.
Lemma lem1582757 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1582758 (x : real) (y : real) : (term30 y x) = (term31 x y).
Proof. exact (MK_COMB (@lem1582757) (@lem1582756 x y)). Qed.
Lemma lem1582759 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1582760 (x : real) (y : real) : (term26 y x) = (term33 x y).
Proof. exact (MK_COMB (@lem1582758 x y) (@lem1582759)). Qed.
Lemma lem1582761 (x : real) (y : real) : (real_le x y) = (term33 x y).
Proof. exact (TRANS (@lem1582743 y x) (@lem1582760 x y)). Qed.
Lemma lem1582762 (y : real) (x : real) : (term34 y x) = (term35 y x).
Proof. exact (@lem1483533 term32 (real_sub y x)). Qed.
Lemma lem1582768 (y : real) (x : real) : (real_sub y x) = (term27 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1582773 (x : real) (y : real) : (term27 y x) = (term28 x y).
Proof. exact (@lem1483488 (term29 x) y). Qed.
Lemma lem1582775 (x : real) (y : real) : (real_sub y x) = (term28 x y).
Proof. exact (TRANS (@lem1582768 y x) (@lem1582773 x y)). Qed.
Lemma lem1582778 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1582779 (x : real) (y : real) : (term37 y x) = (term38 x y).
Proof. exact (MK_COMB (@lem1582778) (@lem1582775 x y)). Qed.
Lemma lem1582780 (x : real) (y : real) : (term38 x y) = (term39 x y).
Proof. exact (@lem1483519 term32 (term28 x y)). Qed.
Lemma lem1582781 (x : real) (y : real) : (term40 x y) = (term41 x y).
Proof. exact (@lem1483508 (term29 x) term42 y). Qed.
Lemma lem1582782 (y : real) : (term29 y) = (term29 y).
Proof. exact (eq_refl (term29 y)). Qed.
Lemma lem1582783 (x : real) : (term43 x) = (term44 x).
Proof. exact (@lem1483476 term42 term42 x). Qed.
Lemma lem1582785 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1582786 : term47 = term48.
Proof. exact (@lem1582785 term49 term49). Qed.
Lemma lem1582787 : (term50 = (BIT1 0)) = (term51 = term49).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1582788 : term51 = term49.
Proof. exact (EQ_MP (@lem1582787) (@lem940073)). Qed.
Lemma lem1582789 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1582790 : term48 = term52.
Proof. exact (MK_COMB (@lem1582789) (@lem1582788)). Qed.
Lemma lem1582791 : term47 = term52.
Proof. exact (TRANS (@lem1582786) (@lem1582790)). Qed.
Lemma lem1582792 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1582793 : term53 = term54.
Proof. exact (MK_COMB (@lem1582792) (@lem1582791)). Qed.
Lemma lem1582794 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1582795 (x : real) : (term44 x) = (term55 x).
Proof. exact (MK_COMB (@lem1582793) (@lem1582794 x)). Qed.
Lemma lem1582796 (x : real) : (term43 x) = (term55 x).
Proof. exact (TRANS (@lem1582783 x) (@lem1582795 x)). Qed.
Lemma lem1582797 (x : real) : (term55 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1582798 (x : real) : (term43 x) = x.
Proof. exact (TRANS (@lem1582796 x) (@lem1582797 x)). Qed.
Lemma lem1582799 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1582800 (x : real) : (term56 x) = (real_add x).
Proof. exact (MK_COMB (@lem1582799) (@lem1582798 x)). Qed.
Lemma lem1582801 (x : real) (y : real) : (term41 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1582800 x) (@lem1582782 y)). Qed.
Lemma lem1582802 (x : real) (y : real) : (term40 x y) = (term27 x y).
Proof. exact (TRANS (@lem1582781 x y) (@lem1582801 x y)). Qed.
Lemma lem1582803 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem1582804 (x : real) (y : real) : (term39 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem1582803) (@lem1582802 x y)). Qed.
Lemma lem1582805 (x : real) (y : real) : (term58 x y) = (term27 x y).
Proof. exact (@lem1483448 (term27 x y)). Qed.
Lemma lem1582806 (x : real) (y : real) : (term39 x y) = (term27 x y).
Proof. exact (TRANS (@lem1582804 x y) (@lem1582805 x y)). Qed.
Lemma lem1582807 (x : real) (y : real) : (term38 x y) = (term27 x y).
Proof. exact (TRANS (@lem1582780 x y) (@lem1582806 x y)). Qed.
Lemma lem1582808 (x : real) (y : real) : (term37 y x) = (term27 x y).
Proof. exact (TRANS (@lem1582779 x y) (@lem1582807 x y)). Qed.
Lemma lem1582809 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1582810 (x : real) (y : real) : (term59 y x) = (term60 x y).
Proof. exact (MK_COMB (@lem1582809) (@lem1582808 x y)). Qed.
Lemma lem1582811 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1582812 (x : real) (y : real) : (term35 y x) = (term61 x y).
Proof. exact (MK_COMB (@lem1582810 x y) (@lem1582811)). Qed.
Lemma lem1582813 (x : real) (y : real) : (term34 y x) = (term61 x y).
Proof. exact (TRANS (@lem1582762 y x) (@lem1582812 x y)). Qed.
Lemma lem1582814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1582815 (x : real) (y : real) : (term62 x y) = (term63 x y).
Proof. exact (MK_COMB (@lem1582814) (@lem1582761 x y)). Qed.
Lemma lem1582816 (x : real) (y : real) : (term64 y x) = (term65 x y).
Proof. exact (MK_COMB (@lem1582815 x y) (@lem1582813 x y)). Qed.
Lemma lem1582817 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (@lem1483533 x y). Qed.
Lemma lem1582830 (x : real) (y : real) : (real_sub x y) = (term27 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1582831 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1582832 (x : real) (y : real) : (term68 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1582831) (@lem1582830 x y)). Qed.
Lemma lem1582833 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1582834 (x : real) (y : real) : (term67 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1582832 x y) (@lem1582833)). Qed.
Lemma lem1582835 (x : real) (y : real) : (term66 x y) = (term61 x y).
Proof. exact (TRANS (@lem1582817 x y) (@lem1582834 x y)). Qed.
Lemma lem1582836 (y : real) (x : real) : (term25 y x) = (term69 y x).
Proof. exact (@lem1483523 (real_sub y x) term32). Qed.
Lemma lem1582837 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1582843 (y : real) (x : real) : (real_sub y x) = (term27 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1582848 (x : real) (y : real) : (term27 y x) = (term28 x y).
Proof. exact (@lem1483488 (term29 x) y). Qed.
Lemma lem1582850 (x : real) (y : real) : (real_sub y x) = (term28 x y).
Proof. exact (TRANS (@lem1582843 y x) (@lem1582848 x y)). Qed.
Lemma lem1582851 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1582852 (x : real) (y : real) : (term70 y x) = (term71 x y).
Proof. exact (MK_COMB (@lem1582851) (@lem1582850 x y)). Qed.
Lemma lem1582853 (x : real) (y : real) : (term72 y x) = (term73 x y).
Proof. exact (MK_COMB (@lem1582852 x y) (@lem1582837)). Qed.
Lemma lem1582854 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (@lem1483519 (term28 x y) term32). Qed.
Lemma lem1582856 (x : nat) : (term75 x) = term32.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1582857 : term76 = term32.
Proof. exact (@lem1582856 term49). Qed.
Lemma lem1582858 (x : real) (y : real) : (term77 x y) = (term77 x y).
Proof. exact (eq_refl (term77 x y)). Qed.
Lemma lem1582859 (x : real) (y : real) : (term74 x y) = (term78 x y).
Proof. exact (MK_COMB (@lem1582858 x y) (@lem1582857)). Qed.
Lemma lem1582860 (x : real) (y : real) : (term78 x y) = (term28 x y).
Proof. exact (@lem1483450 (term28 x y)). Qed.
Lemma lem1582861 (x : real) (y : real) : (term74 x y) = (term28 x y).
Proof. exact (TRANS (@lem1582859 x y) (@lem1582860 x y)). Qed.
Lemma lem1582862 (x : real) (y : real) : (term73 x y) = (term28 x y).
Proof. exact (TRANS (@lem1582854 x y) (@lem1582861 x y)). Qed.
Lemma lem1582863 (x : real) (y : real) : (term72 y x) = (term28 x y).
Proof. exact (TRANS (@lem1582853 x y) (@lem1582862 x y)). Qed.
Lemma lem1582864 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1582865 (x : real) (y : real) : (term79 y x) = (term31 x y).
Proof. exact (MK_COMB (@lem1582864) (@lem1582863 x y)). Qed.
Lemma lem1582866 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1582867 (x : real) (y : real) : (term69 y x) = (term33 x y).
Proof. exact (MK_COMB (@lem1582865 x y) (@lem1582866)). Qed.
Lemma lem1582868 (x : real) (y : real) : (term25 y x) = (term33 x y).
Proof. exact (TRANS (@lem1582836 y x) (@lem1582867 x y)). Qed.
Lemma lem1582869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1582870 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem1582869) (@lem1582835 x y)). Qed.
Lemma lem1582871 (x : real) (y : real) : (term82 y x) = (term83 x y).
Proof. exact (MK_COMB (@lem1582870 x y) (@lem1582868 x y)). Qed.
Lemma lem1582872 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1582873 (x : real) (y : real) : (term84 y x) = (term85 x y).
Proof. exact (MK_COMB (@lem1582872) (@lem1582816 x y)). Qed.
Lemma lem1582874 (x : real) (y : real) : (term24 y x) = (term86 x y).
Proof. exact (MK_COMB (@lem1582873 x y) (@lem1582871 x y)). Qed.
Lemma lem1582899 (x : real) (y : real) : (term23 y x) = (term86 x y).
Proof. exact (TRANS (@lem1582742 y x) (@lem1582874 x y)). Qed.
Lemma lem1582909 (x : real) (y : real) (h1 : term86 x y) : term86 x y.
Proof. exact (h1). Qed.
Lemma lem1582910 (x : real) (y : real) (h1 : term65 x y) : term65 x y.
Proof. exact (h1). Qed.
Lemma lem1582911 (x : real) (y : real) (h1 : term65 x y) : term61 x y.
Proof. exact (proj2 (@lem1582910 x y h1)). Qed.
Lemma lem1582912 (x : real) (y : real) (h1 : term65 x y) : term33 x y.
Proof. exact (proj1 (@lem1582910 x y h1)). Qed.
Lemma lem1582914 (n : nat) (m : nat) : (term87 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1582915 : term88 = term89.
Proof. exact (@lem1582914 (NUMERAL 0) term49). Qed.
Lemma lem1582916 : term90 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1582917 (h1 : term90 = (BIT1 0)) : term89 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1582918 : (term90 = (BIT1 0)) = (term89 = True).
Proof. exact (prop_ext (fun h1 : term90 = (BIT1 0) => @lem1582917 h1) (fun h1 : term89 = True => @lem1582916)). Qed.
Lemma lem1582919 : term89 = True.
Proof. exact (EQ_MP (@lem1582918) (@lem1582916)). Qed.
Lemma lem1582920 : term88 = True.
Proof. exact (TRANS (@lem1582915) (@lem1582919)). Qed.
Lemma lem1582921 : True = term88.
Proof. exact (SYM (@lem1582920)). Qed.
Lemma lem1582922 : term88.
Proof. exact (EQ_MP (@lem1582921) (@lem0)). Qed.
Lemma lem1582923 (x : real) (y : real) (h1 : term65 x y) : term91 x y.
Proof. exact (conj (@lem1582922) (@lem1582912 x y h1)). Qed.
Lemma lem1582925 (x : real) (y : real) : term92 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1582926 (x : real) (y : real) : term93 x y.
Proof. exact (@lem1582925 term52 (term28 x y)). Qed.
Lemma lem1582927 (x : real) (y : real) (h1 : term65 x y) : term94 x y.
Proof. exact (@lem1582926 x y (@lem1582923 x y h1)). Qed.
Lemma lem1582928 (x : real) (y : real) : (term95 x y) = (term28 x y).
Proof. exact (@lem1483460 (term28 x y)). Qed.
Lemma lem1582929 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1582930 (x : real) (y : real) : (term96 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1582929) (@lem1582928 x y)). Qed.
Lemma lem1582931 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1582932 (x : real) (y : real) : (term94 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1582930 x y) (@lem1582931)). Qed.
Lemma lem1582933 (x : real) (y : real) (h1 : term65 x y) : term33 x y.
Proof. exact (EQ_MP (@lem1582932 x y) (@lem1582927 x y h1)). Qed.
Lemma lem1582935 (n : nat) (m : nat) : (term87 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1582936 : term88 = term89.
Proof. exact (@lem1582935 (NUMERAL 0) term49). Qed.
Lemma lem1582937 : term90 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1582938 (h1 : term90 = (BIT1 0)) : term89 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1582939 : (term90 = (BIT1 0)) = (term89 = True).
Proof. exact (prop_ext (fun h1 : term90 = (BIT1 0) => @lem1582938 h1) (fun h1 : term89 = True => @lem1582937)). Qed.
Lemma lem1582940 : term89 = True.
Proof. exact (EQ_MP (@lem1582939) (@lem1582937)). Qed.
Lemma lem1582941 : term88 = True.
Proof. exact (TRANS (@lem1582936) (@lem1582940)). Qed.
Lemma lem1582942 : True = term88.
Proof. exact (SYM (@lem1582941)). Qed.
Lemma lem1582943 : term88.
Proof. exact (EQ_MP (@lem1582942) (@lem0)). Qed.
Lemma lem1582944 (x : real) (y : real) (h1 : term65 x y) : term97 x y.
Proof. exact (conj (@lem1582943) (@lem1582911 x y h1)). Qed.
Lemma lem1582946 (x : real) (y : real) : term98 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1582947 (x : real) (y : real) : term99 x y.
Proof. exact (@lem1582946 term52 (term27 x y)). Qed.
Lemma lem1582948 (x : real) (y : real) (h1 : term65 x y) : term100 x y.
Proof. exact (@lem1582947 x y (@lem1582944 x y h1)). Qed.
Lemma lem1582949 (x : real) (y : real) : (term101 x y) = (term27 x y).
Proof. exact (@lem1483460 (term27 x y)). Qed.
Lemma lem1582950 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1582951 (x : real) (y : real) : (term102 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1582950) (@lem1582949 x y)). Qed.
Lemma lem1582952 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1582953 (x : real) (y : real) : (term100 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1582951 x y) (@lem1582952)). Qed.
Lemma lem1582954 (x : real) (y : real) (h1 : term65 x y) : term61 x y.
Proof. exact (EQ_MP (@lem1582953 x y) (@lem1582948 x y h1)). Qed.
Lemma lem1582955 (x : real) (y : real) (h1 : term65 x y) : term83 x y.
Proof. exact (conj (@lem1582954 x y h1) (@lem1582933 x y h1)). Qed.
Lemma lem1582957 (x : real) (y : real) : term103 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1582958 (x : real) (y : real) : term104 x y.
Proof. exact (@lem1582957 (term27 x y) (term28 x y)). Qed.
Lemma lem1582959 (x : real) (y : real) (h1 : term65 x y) : term105 x y.
Proof. exact (@lem1582958 x y (@lem1582955 x y h1)). Qed.
Lemma lem1582960 (x : real) (y : real) : (term106 x y) = (term107 x y).
Proof. exact (@lem1483480 x (term29 x) (term29 y) y). Qed.
Lemma lem1582961 (x : real) : (term108 x) = (term109 x).
Proof. exact (@lem1483442 term42 x). Qed.
Lemma lem1582963 (m : nat) : (term110 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1582964 : term111 = term32.
Proof. exact (@lem1582963 term49). Qed.
Lemma lem1582965 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1582966 : term112 = term113.
Proof. exact (MK_COMB (@lem1582965) (@lem1582964)). Qed.
Lemma lem1582967 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1582968 (x : real) : (term109 x) = (term114 x).
Proof. exact (MK_COMB (@lem1582966) (@lem1582967 x)). Qed.
Lemma lem1582969 (x : real) : (term108 x) = (term114 x).
Proof. exact (TRANS (@lem1582961 x) (@lem1582968 x)). Qed.
Lemma lem1582970 (x : real) : (term114 x) = term32.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1582971 (x : real) : (term108 x) = term32.
Proof. exact (TRANS (@lem1582969 x) (@lem1582970 x)). Qed.
Lemma lem1582972 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1582973 (x : real) : (term115 x) = term57.
Proof. exact (MK_COMB (@lem1582972) (@lem1582971 x)). Qed.
Lemma lem1582974 (y : real) : (term116 y) = (term109 y).
Proof. exact (@lem1483440 term42 y). Qed.
Lemma lem1582976 (m : nat) : (term110 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1582977 : term111 = term32.
Proof. exact (@lem1582976 term49). Qed.
Lemma lem1582978 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1582979 : term112 = term113.
Proof. exact (MK_COMB (@lem1582978) (@lem1582977)). Qed.
Lemma lem1582980 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1582981 (y : real) : (term109 y) = (term114 y).
Proof. exact (MK_COMB (@lem1582979) (@lem1582980 y)). Qed.
Lemma lem1582982 (y : real) : (term116 y) = (term114 y).
Proof. exact (TRANS (@lem1582974 y) (@lem1582981 y)). Qed.
Lemma lem1582983 (y : real) : (term114 y) = term32.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1582984 (y : real) : (term116 y) = term32.
Proof. exact (TRANS (@lem1582982 y) (@lem1582983 y)). Qed.
Lemma lem1582985 (x : real) (y : real) : (term107 x y) = term117.
Proof. exact (MK_COMB (@lem1582973 x) (@lem1582984 y)). Qed.
Lemma lem1582986 (x : real) (y : real) : (term106 x y) = term117.
Proof. exact (TRANS (@lem1582960 x y) (@lem1582985 x y)). Qed.
Lemma lem1582987 : term117 = term32.
Proof. exact (@lem1483448 term32). Qed.
Lemma lem1582988 (x : real) (y : real) : (term106 x y) = term32.
Proof. exact (TRANS (@lem1582986 x y) (@lem1582987)). Qed.
Lemma lem1582989 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1582990 (x : real) (y : real) : (term118 x y) = term119.
Proof. exact (MK_COMB (@lem1582989) (@lem1582988 x y)). Qed.
Lemma lem1582991 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1582992 (x : real) (y : real) : (term105 x y) = term120.
Proof. exact (MK_COMB (@lem1582990 x y) (@lem1582991)). Qed.
Lemma lem1582993 (x : real) (y : real) (h1 : term65 x y) : term120.
Proof. exact (EQ_MP (@lem1582992 x y) (@lem1582959 x y h1)). Qed.
Lemma lem1582995 (n : nat) (m : nat) : (term87 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1582996 : term120 = term121.
Proof. exact (@lem1582995 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1582997 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1582998 : term120 = False.
Proof. exact (TRANS (@lem1582996) (@lem1582997)). Qed.
Lemma lem1582999 (x : real) (y : real) (h1 : term65 x y) : False.
Proof. exact (EQ_MP (@lem1582998) (@lem1582993 x y h1)). Qed.
Lemma lem1583000 (x : real) (y : real) (h1 : term83 x y) : term83 x y.
Proof. exact (h1). Qed.
Lemma lem1583001 (x : real) (y : real) (h1 : term83 x y) : term33 x y.
Proof. exact (proj2 (@lem1583000 x y h1)). Qed.
Lemma lem1583002 (x : real) (y : real) (h1 : term83 x y) : term61 x y.
Proof. exact (proj1 (@lem1583000 x y h1)). Qed.
Lemma lem1583004 (n : nat) (m : nat) : (term87 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1583005 : term88 = term89.
Proof. exact (@lem1583004 (NUMERAL 0) term49). Qed.
Lemma lem1583006 : term90 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1583007 (h1 : term90 = (BIT1 0)) : term89 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1583008 : (term90 = (BIT1 0)) = (term89 = True).
Proof. exact (prop_ext (fun h1 : term90 = (BIT1 0) => @lem1583007 h1) (fun h1 : term89 = True => @lem1583006)). Qed.
Lemma lem1583009 : term89 = True.
Proof. exact (EQ_MP (@lem1583008) (@lem1583006)). Qed.
Lemma lem1583010 : term88 = True.
Proof. exact (TRANS (@lem1583005) (@lem1583009)). Qed.
Lemma lem1583011 : True = term88.
Proof. exact (SYM (@lem1583010)). Qed.
Lemma lem1583012 : term88.
Proof. exact (EQ_MP (@lem1583011) (@lem0)). Qed.
Lemma lem1583013 (x : real) (y : real) (h1 : term83 x y) : term91 x y.
Proof. exact (conj (@lem1583012) (@lem1583001 x y h1)). Qed.
Lemma lem1583015 (x : real) (y : real) : term92 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1583016 (x : real) (y : real) : term93 x y.
Proof. exact (@lem1583015 term52 (term28 x y)). Qed.
Lemma lem1583017 (x : real) (y : real) (h1 : term83 x y) : term94 x y.
Proof. exact (@lem1583016 x y (@lem1583013 x y h1)). Qed.
Lemma lem1583018 (x : real) (y : real) : (term95 x y) = (term28 x y).
Proof. exact (@lem1483460 (term28 x y)). Qed.
Lemma lem1583019 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1583020 (x : real) (y : real) : (term96 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1583019) (@lem1583018 x y)). Qed.
Lemma lem1583021 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1583022 (x : real) (y : real) : (term94 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1583020 x y) (@lem1583021)). Qed.
Lemma lem1583023 (x : real) (y : real) (h1 : term83 x y) : term33 x y.
Proof. exact (EQ_MP (@lem1583022 x y) (@lem1583017 x y h1)). Qed.
Lemma lem1583025 (n : nat) (m : nat) : (term87 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1583026 : term88 = term89.
Proof. exact (@lem1583025 (NUMERAL 0) term49). Qed.
Lemma lem1583027 : term90 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1583028 (h1 : term90 = (BIT1 0)) : term89 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1583029 : (term90 = (BIT1 0)) = (term89 = True).
Proof. exact (prop_ext (fun h1 : term90 = (BIT1 0) => @lem1583028 h1) (fun h1 : term89 = True => @lem1583027)). Qed.
Lemma lem1583030 : term89 = True.
Proof. exact (EQ_MP (@lem1583029) (@lem1583027)). Qed.
Lemma lem1583031 : term88 = True.
Proof. exact (TRANS (@lem1583026) (@lem1583030)). Qed.
Lemma lem1583032 : True = term88.
Proof. exact (SYM (@lem1583031)). Qed.
Lemma lem1583033 : term88.
Proof. exact (EQ_MP (@lem1583032) (@lem0)). Qed.
Lemma lem1583034 (x : real) (y : real) (h1 : term83 x y) : term97 x y.
Proof. exact (conj (@lem1583033) (@lem1583002 x y h1)). Qed.
Lemma lem1583036 (x : real) (y : real) : term98 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1583037 (x : real) (y : real) : term99 x y.
Proof. exact (@lem1583036 term52 (term27 x y)). Qed.
Lemma lem1583038 (x : real) (y : real) (h1 : term83 x y) : term100 x y.
Proof. exact (@lem1583037 x y (@lem1583034 x y h1)). Qed.
Lemma lem1583039 (x : real) (y : real) : (term101 x y) = (term27 x y).
Proof. exact (@lem1483460 (term27 x y)). Qed.
Lemma lem1583040 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1583041 (x : real) (y : real) : (term102 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1583040) (@lem1583039 x y)). Qed.
Lemma lem1583042 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1583043 (x : real) (y : real) : (term100 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem1583041 x y) (@lem1583042)). Qed.
Lemma lem1583044 (x : real) (y : real) (h1 : term83 x y) : term61 x y.
Proof. exact (EQ_MP (@lem1583043 x y) (@lem1583038 x y h1)). Qed.
Lemma lem1583045 (x : real) (y : real) (h1 : term83 x y) : term83 x y.
Proof. exact (conj (@lem1583044 x y h1) (@lem1583023 x y h1)). Qed.
Lemma lem1583047 (x : real) (y : real) : term103 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1583048 (x : real) (y : real) : term104 x y.
Proof. exact (@lem1583047 (term27 x y) (term28 x y)). Qed.
Lemma lem1583049 (x : real) (y : real) (h1 : term83 x y) : term105 x y.
Proof. exact (@lem1583048 x y (@lem1583045 x y h1)). Qed.
Lemma lem1583050 (x : real) (y : real) : (term106 x y) = (term107 x y).
Proof. exact (@lem1483480 x (term29 x) (term29 y) y). Qed.
Lemma lem1583051 (x : real) : (term108 x) = (term109 x).
Proof. exact (@lem1483442 term42 x). Qed.
Lemma lem1583053 (m : nat) : (term110 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1583054 : term111 = term32.
Proof. exact (@lem1583053 term49). Qed.
Lemma lem1583055 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1583056 : term112 = term113.
Proof. exact (MK_COMB (@lem1583055) (@lem1583054)). Qed.
Lemma lem1583057 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1583058 (x : real) : (term109 x) = (term114 x).
Proof. exact (MK_COMB (@lem1583056) (@lem1583057 x)). Qed.
Lemma lem1583059 (x : real) : (term108 x) = (term114 x).
Proof. exact (TRANS (@lem1583051 x) (@lem1583058 x)). Qed.
Lemma lem1583060 (x : real) : (term114 x) = term32.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1583061 (x : real) : (term108 x) = term32.
Proof. exact (TRANS (@lem1583059 x) (@lem1583060 x)). Qed.
Lemma lem1583062 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1583063 (x : real) : (term115 x) = term57.
Proof. exact (MK_COMB (@lem1583062) (@lem1583061 x)). Qed.
Lemma lem1583064 (y : real) : (term116 y) = (term109 y).
Proof. exact (@lem1483440 term42 y). Qed.
Lemma lem1583066 (m : nat) : (term110 m) = term32.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1583067 : term111 = term32.
Proof. exact (@lem1583066 term49). Qed.
Lemma lem1583068 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1583069 : term112 = term113.
Proof. exact (MK_COMB (@lem1583068) (@lem1583067)). Qed.
Lemma lem1583070 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1583071 (y : real) : (term109 y) = (term114 y).
Proof. exact (MK_COMB (@lem1583069) (@lem1583070 y)). Qed.
Lemma lem1583072 (y : real) : (term116 y) = (term114 y).
Proof. exact (TRANS (@lem1583064 y) (@lem1583071 y)). Qed.
Lemma lem1583073 (y : real) : (term114 y) = term32.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1583074 (y : real) : (term116 y) = term32.
Proof. exact (TRANS (@lem1583072 y) (@lem1583073 y)). Qed.
Lemma lem1583075 (x : real) (y : real) : (term107 x y) = term117.
Proof. exact (MK_COMB (@lem1583063 x) (@lem1583074 y)). Qed.
Lemma lem1583076 (x : real) (y : real) : (term106 x y) = term117.
Proof. exact (TRANS (@lem1583050 x y) (@lem1583075 x y)). Qed.
Lemma lem1583077 : term117 = term32.
Proof. exact (@lem1483448 term32). Qed.
Lemma lem1583078 (x : real) (y : real) : (term106 x y) = term32.
Proof. exact (TRANS (@lem1583076 x y) (@lem1583077)). Qed.
Lemma lem1583079 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1583080 (x : real) (y : real) : (term118 x y) = term119.
Proof. exact (MK_COMB (@lem1583079) (@lem1583078 x y)). Qed.
Lemma lem1583081 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1583082 (x : real) (y : real) : (term105 x y) = term120.
Proof. exact (MK_COMB (@lem1583080 x y) (@lem1583081)). Qed.
Lemma lem1583083 (x : real) (y : real) (h1 : term83 x y) : term120.
Proof. exact (EQ_MP (@lem1583082 x y) (@lem1583049 x y h1)). Qed.
Lemma lem1583085 (n : nat) (m : nat) : (term87 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1583086 : term120 = term121.
Proof. exact (@lem1583085 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1583087 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1583088 : term120 = False.
Proof. exact (TRANS (@lem1583086) (@lem1583087)). Qed.
Lemma lem1583089 (x : real) (y : real) (h1 : term83 x y) : False.
Proof. exact (EQ_MP (@lem1583088) (@lem1583083 x y h1)). Qed.
Lemma lem1583090 (x : real) (y : real) (h1 : term86 x y) : False.
Proof. exact (or_elim (@lem1582909 x y h1) (fun h0 : term65 x y => @lem1582999 x y h0) (fun h0 : term83 x y => @lem1583089 x y h0)). Qed.
Lemma lem1583092 (x : real) (y : real) (h1 : term86 x y) : term86 x y.
Proof. exact (h1). Qed.
Lemma lem1583093 (x : real) (y : real) (h1 : term86 x y) : (term86 x y) = False.
Proof. exact (prop_ext (fun h2 : term86 x y => @lem1583090 x y h1) (fun h2 : False => @lem1583092 x y h1)). Qed.
Lemma lem1583094 (x : real) (y : real) (h1 : term86 x y) : False.
Proof. exact (EQ_MP (@lem1583093 x y h1) (@lem1583092 x y h1)). Qed.
Lemma lem1583095 (y : real) (x : real) (h1 : term23 y x) : term23 y x.
Proof. exact (h1). Qed.
Lemma lem1583096 (y : real) (x : real) (h1 : term23 y x) : term86 x y.
Proof. exact (EQ_MP (@lem1582899 x y) (@lem1583095 y x h1)). Qed.
Lemma lem1583097 (y : real) (x : real) (h1 : term23 y x) : (term86 x y) = False.
Proof. exact (prop_ext (fun h2 : term86 x y => @lem1583094 x y h2) (fun h2 : False => @lem1583096 y x h1)). Qed.
Lemma lem1583098 (y : real) (x : real) (h1 : term23 y x) : False.
Proof. exact (EQ_MP (@lem1583097 y x h1) (@lem1583096 y x h1)). Qed.
Lemma lem1583099 (y : real) (x : real) : term122 y x.
Proof. exact (fun h0 : term23 y x => @lem1583098 y x h0). Qed.
Lemma lem1583100 (y : real) (x : real) : term123 y x.
Proof. exact (@lem1386578 ((real_le x y) = (term25 y x))). Qed.
Lemma lem1583119 (y : real) (x : real) : (real_le x y) = (term25 y x).
Proof. exact (@lem1583100 y x (@lem1583099 y x)). Qed.
Lemma lem1583120 (x : real) : (term124 x) = (term125 x).
Proof. exact (@lem1583119 x term32). Qed.
Lemma lem1583121 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1583122 (x : real) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem1583121) (@lem1583120 x)). Qed.
Lemma lem1583124 (y : real) (x : real) : (real_le x y) = (term25 y x).
Proof. exact (@lem1583100 y x (@lem1583099 y x)). Qed.
Lemma lem1583125 (z : real) (y : real) : (real_le y z) = (term25 z y).
Proof. exact (@lem1583124 z y). Qed.
Lemma lem1583126 (x : real) (z : real) (y : real) : (term128 x y z) = (term129 x z y).
Proof. exact (MK_COMB (@lem1583122 x) (@lem1583125 z y)). Qed.
Lemma lem1583127 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1583128 (x : real) (z : real) (y : real) : (term130 x y z) = (term131 x z y).
Proof. exact (MK_COMB (@lem1583127) (@lem1583126 x z y)). Qed.
Lemma lem1583130 (y : real) (x : real) : (real_le x y) = (term25 y x).
Proof. exact (@lem1583100 y x (@lem1583099 y x)). Qed.
Lemma lem1583131 (z : real) (x : real) (y : real) : (term132 y x z) = (term133 z x y).
Proof. exact (@lem1583130 (real_mul x z) (real_mul x y)). Qed.
Lemma lem1583132 (z : real) (x : real) (y : real) : (term134 y x z) = (term135 z x y).
Proof. exact (MK_COMB (@lem1583128 x z y) (@lem1583131 z x y)). Qed.
Lemma lem1583133 (x : real) (y : real) : (term136 y x) = (term137 x y).
Proof. exact (fun_ext (fun z : real => @lem1583132 z x y)). Qed.
Lemma lem1583134 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583135 (x : real) (y : real) : (term138 y x) = (term139 x y).
Proof. exact (MK_COMB (@lem1583134) (@lem1583133 x y)). Qed.
Lemma lem1583136 (x : real) : (term140 x) = (term141 x).
Proof. exact (fun_ext (fun y : real => @lem1583135 x y)). Qed.
Lemma lem1583137 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583138 (x : real) : (term142 x) = (term143 x).
Proof. exact (MK_COMB (@lem1583137) (@lem1583136 x)). Qed.
Lemma lem1583139 : term144 = term145.
Proof. exact (fun_ext (fun x : real => @lem1583138 x)). Qed.
Lemma lem1583140 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583141 : term146 = term147.
Proof. exact (MK_COMB (@lem1583140) (@lem1583139)). Qed.
Lemma lem1583142 : term147 = term146.
Proof. exact (SYM (@lem1583141)). Qed.
Lemma lem1583160 (x : real) : (term19 x) = x.
Proof. exact (EQ_MP (@lem1582695 x) (@lem1582694 x)). Qed.
Lemma lem1583161 : term148 = term148.
Proof. exact (eq_refl term148). Qed.
Lemma lem1583162 (x : real) : (term125 x) = (term124 x).
Proof. exact (MK_COMB (@lem1583161) (@lem1583160 x)). Qed.
Lemma lem1583163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1583164 (x : real) : (term127 x) = (term126 x).
Proof. exact (MK_COMB (@lem1583163) (@lem1583162 x)). Qed.
Lemma lem1583165 (z : real) (y : real) : (term25 z y) = (term25 z y).
Proof. exact (eq_refl (term25 z y)). Qed.
Lemma lem1583166 (x : real) (z : real) (y : real) : (term129 x z y) = (term149 x z y).
Proof. exact (MK_COMB (@lem1583164 x) (@lem1583165 z y)). Qed.
Lemma lem1583169 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1583170 (x : real) (z : real) (y : real) : (term131 x z y) = (term150 x z y).
Proof. exact (MK_COMB (@lem1583169) (@lem1583166 x z y)). Qed.
Lemma lem1583172 (x : real) (y : real) (z : real) : (term1 y x z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1582704 x y z) (@lem1582703 x y z)). Qed.
Lemma lem1583173 (x : real) (z : real) (y : real) : (term1 z x y) = (term0 x z y).
Proof. exact (@lem1583172 x z y). Qed.
Lemma lem1583174 : term148 = term148.
Proof. exact (eq_refl term148). Qed.
Lemma lem1583175 (x : real) (z : real) (y : real) : (term133 z x y) = (term151 x z y).
Proof. exact (MK_COMB (@lem1583174) (@lem1583173 x z y)). Qed.
Lemma lem1583176 (x : real) (z : real) (y : real) : (term135 z x y) = (term152 x z y).
Proof. exact (MK_COMB (@lem1583170 x z y) (@lem1583175 x z y)). Qed.
Lemma lem1583178 (x : real) (y : real) : (term17 x y) = True.
Proof. exact (EQ_MP (@lem1582692 x y) (@lem1582691 x y)). Qed.
Lemma lem1583179 (x : real) (z : real) (y : real) : (term152 x z y) = True.
Proof. exact (@lem1583178 x (real_sub z y)). Qed.
Lemma lem1583180 (z : real) (x : real) (y : real) : (term135 z x y) = True.
Proof. exact (TRANS (@lem1583176 x z y) (@lem1583179 x z y)). Qed.
Lemma lem1583181 (x : real) (y : real) : (term137 x y) = term153.
Proof. exact (fun_ext (fun z : real => @lem1583180 z x y)). Qed.
Lemma lem1583182 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583183 (x : real) (y : real) : (term139 x y) = term154.
Proof. exact (MK_COMB (@lem1583182) (@lem1583181 x y)). Qed.
Lemma lem1583185 {A : Type'} (t : Prop) : (term155 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1583186 (t : Prop) : (term156 t) = t.
Proof. exact (@lem1583185 real t). Qed.
Lemma lem1583187 : term154 = True.
Proof. exact (@lem1583186 True). Qed.
Lemma lem1583188 (x : real) (y : real) : (term139 x y) = True.
Proof. exact (TRANS (@lem1583183 x y) (@lem1583187)). Qed.
Lemma lem1583189 (x : real) : (term141 x) = term153.
Proof. exact (fun_ext (fun y : real => @lem1583188 x y)). Qed.
Lemma lem1583190 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583191 (x : real) : (term143 x) = term154.
Proof. exact (MK_COMB (@lem1583190) (@lem1583189 x)). Qed.
Lemma lem1583193 {A : Type'} (t : Prop) : (term155 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1583194 (t : Prop) : (term156 t) = t.
Proof. exact (@lem1583193 real t). Qed.
Lemma lem1583195 : term154 = True.
Proof. exact (@lem1583194 True). Qed.
Lemma lem1583196 (x : real) : (term143 x) = True.
Proof. exact (TRANS (@lem1583191 x) (@lem1583195)). Qed.
Lemma lem1583197 : term145 = term153.
Proof. exact (fun_ext (fun x : real => @lem1583196 x)). Qed.
Lemma lem1583198 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1583199 : term147 = term154.
Proof. exact (MK_COMB (@lem1583198) (@lem1583197)). Qed.
Lemma lem1583201 {A : Type'} (t : Prop) : (term155 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1583202 (t : Prop) : (term156 t) = t.
Proof. exact (@lem1583201 real t). Qed.
Lemma lem1583203 : term154 = True.
Proof. exact (@lem1583202 True). Qed.
Lemma lem1583204 : term147 = True.
Proof. exact (TRANS (@lem1583199) (@lem1583203)). Qed.
Lemma lem1583205 : True = term147.
Proof. exact (SYM (@lem1583204)). Qed.
Lemma lem1583206 : term147.
Proof. exact (EQ_MP (@lem1583205) (@lem0)). Qed.
Lemma lem1583207 : term146.
Proof. exact (EQ_MP (@lem1583142) (@lem1583206)). Qed.
