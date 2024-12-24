Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ARCH_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_ARCH_LT_spec.
Require Import REAL_LT_LDIV_EQ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem1699587 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1699588 : term1 = term2.
Proof. exact (@lem1699587 term1). Qed.
Lemma lem1699589 : term2 = term1.
Proof. exact (SYM (@lem1699588)). Qed.
Lemma lem1699590 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1699593 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1699594 : term5.
Proof. exact (fun h0 : term4 => @lem1699593 h0). Qed.
Lemma lem1699595 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1699596 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1699597 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1699595 h2 (@lem1699596 h1)). Qed.
Lemma lem1699598 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1699597 h1 h0). Qed.
Lemma lem1699599 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1699600 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1699598 h1 (@lem1699599 h2)). Qed.
Lemma lem1699601 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1699600 h0 h1). Qed.
Lemma lem1699602 : term7.
Proof. exact (fun h0 : term5 => @lem1699601 h0). Qed.
Lemma lem1699605 : term5.
Proof. exact (@lem1699602 (@lem1699594)). Qed.
Lemma lem1699639 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1699640 : term8 = term9.
Proof. exact (@lem1699639 term10). Qed.
Lemma lem1699649 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1699650 : term12 = term13.
Proof. exact (MK_COMB (@lem1699649) (@lem1699640)). Qed.
Lemma lem1699653 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1699660 : term4 = term15.
Proof. exact (MK_COMB (@lem1699653) (@lem1699650)). Qed.
Lemma lem1699661 (x : real) (n : nat) : (term16 x n) = (term16 x n).
Proof. exact (eq_refl (term16 x n)). Qed.
Lemma lem1699662 (x : real) : (term17 x) = (term17 x).
Proof. exact (fun_ext (fun n : nat => @lem1699661 x n)). Qed.
Lemma lem1699663 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1699664 (x : real) : (term18 x) = (term18 x).
Proof. exact (MK_COMB (@lem1699663) (@lem1699662 x)). Qed.
Lemma lem1699665 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1699664 x)). Qed.
Lemma lem1699666 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699667 : term10 = term10.
Proof. exact (MK_COMB (@lem1699666) (@lem1699665)). Qed.
Lemma lem1699668 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1699669 : term9 = term9.
Proof. exact (MK_COMB (@lem1699668) (@lem1699667)). Qed.
Lemma lem1699678 (x : real) (y : real) (z : real) : (term20 x y z) = (term20 x y z).
Proof. exact (eq_refl (term20 x y z)). Qed.
Lemma lem1699679 (x : real) (y : real) : (term21 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1699678 x y z)). Qed.
Lemma lem1699680 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699681 (x : real) (y : real) : (term22 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1699680) (@lem1699679 x y)). Qed.
Lemma lem1699682 (x : real) : (term23 x) = (term23 x).
Proof. exact (fun_ext (fun y : real => @lem1699681 x y)). Qed.
Lemma lem1699683 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699684 (x : real) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem1699683) (@lem1699682 x)). Qed.
Lemma lem1699685 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem1699684 x)). Qed.
Lemma lem1699686 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699687 : term26 = term26.
Proof. exact (MK_COMB (@lem1699686) (@lem1699685)). Qed.
Lemma lem1699688 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1699689 : term11 = term11.
Proof. exact (MK_COMB (@lem1699688) (@lem1699687)). Qed.
Lemma lem1699690 : term13 = term13.
Proof. exact (MK_COMB (@lem1699689) (@lem1699669)). Qed.
Lemma lem1699691 (y : real) (n : nat) (x : real) : (term27 y n x) = (term27 y n x).
Proof. exact (eq_refl (term27 y n x)). Qed.
Lemma lem1699692 (y : real) (x : real) : (term28 y x) = (term28 y x).
Proof. exact (fun_ext (fun n : nat => @lem1699691 y n x)). Qed.
Lemma lem1699693 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1699694 (y : real) (x : real) : (term29 y x) = (term29 y x).
Proof. exact (MK_COMB (@lem1699693) (@lem1699692 y x)). Qed.
Lemma lem1699695 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1699694 y x)). Qed.
Lemma lem1699696 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699697 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1699696) (@lem1699695 x)). Qed.
Lemma lem1699700 (x : real) : (term32 x) = (term32 x).
Proof. exact (eq_refl (term32 x)). Qed.
Lemma lem1699701 (x : real) : (term33 x) = (term33 x).
Proof. exact (MK_COMB (@lem1699700 x) (@lem1699697 x)). Qed.
Lemma lem1699702 : term34 = term34.
Proof. exact (fun_ext (fun x : real => @lem1699701 x)). Qed.
Lemma lem1699703 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699704 : term1 = term1.
Proof. exact (MK_COMB (@lem1699703) (@lem1699702)). Qed.
Lemma lem1699705 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1699706 : term3 = term3.
Proof. exact (MK_COMB (@lem1699705) (@lem1699704)). Qed.
Lemma lem1699707 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1699708 : term14 = term14.
Proof. exact (MK_COMB (@lem1699707) (@lem1699706)). Qed.
Lemma lem1699709 : term15 = term15.
Proof. exact (MK_COMB (@lem1699708) (@lem1699690)). Qed.
Lemma lem1699768 : term4 = term15.
Proof. exact (TRANS (@lem1699660) (@lem1699709)). Qed.
Lemma lem1699769 : term15 = term4.
Proof. exact (SYM (@lem1699768)). Qed.
Lemma lem1699770 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1699771 (h1 : term26) : term26.
Proof. exact (h1). Qed.
Lemma lem1699772 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1699775 (P : nat -> Prop) : (term35 P) = (term36 P).
Proof. exact (@lem18394 nat P). Qed.
Lemma lem1699776 (y : real) (x : real) : (term37 y x) = (term38 y x).
Proof. exact (@lem1699775 (term28 y x)). Qed.
Lemma lem1699777 (y : real) (n : nat) (x : real) : (term39 y x n) = (term27 y n x).
Proof. exact (eq_refl (term39 y x n)). Qed.
Lemma lem1699778 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1699780 (y : real) (n : nat) (x : real) : (term40 y x n) = (term41 y n x).
Proof. exact (MK_COMB (@lem1699778) (@lem1699777 y n x)). Qed.
Lemma lem1699781 (y : real) (x : real) : (term42 y x) = (term43 y x).
Proof. exact (fun_ext (fun n : nat => @lem1699780 y n x)). Qed.
Lemma lem1699782 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1699783 (y : real) (x : real) : (term38 y x) = (term44 y x).
Proof. exact (MK_COMB (@lem1699782) (@lem1699781 y x)). Qed.
Lemma lem1699784 (y : real) (x : real) : (term37 y x) = (term44 y x).
Proof. exact (TRANS (@lem1699776 y x) (@lem1699783 y x)). Qed.
Lemma lem1699785 (P : real -> Prop) : (term45 P) = (term46 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1699786 (x : real) : (term47 x) = (term48 x).
Proof. exact (@lem1699785 (term30 x)). Qed.
Lemma lem1699787 (y : real) (x : real) : (term49 x y) = (term29 y x).
Proof. exact (eq_refl (term49 x y)). Qed.
Lemma lem1699788 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1699789 (y : real) (x : real) : (term50 x y) = (term37 y x).
Proof. exact (MK_COMB (@lem1699788) (@lem1699787 y x)). Qed.
Lemma lem1699790 (y : real) (x : real) : (term50 x y) = (term44 y x).
Proof. exact (TRANS (@lem1699789 y x) (@lem1699784 y x)). Qed.
Lemma lem1699791 (x : real) : (term51 x) = (term52 x).
Proof. exact (fun_ext (fun y : real => @lem1699790 y x)). Qed.
Lemma lem1699792 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1699793 (x : real) : (term48 x) = (term53 x).
Proof. exact (MK_COMB (@lem1699792) (@lem1699791 x)). Qed.
Lemma lem1699794 (x : real) : (term47 x) = (term53 x).
Proof. exact (TRANS (@lem1699786 x) (@lem1699793 x)). Qed.
Lemma lem1699796 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1699797 (x : real) : (term55 x) = (term56 x).
Proof. exact (MK_COMB (@lem1699796 x) (@lem1699794 x)). Qed.
Lemma lem1699798 (x : real) : (term57 x) = (term55 x).
Proof. exact (@lem17362 (term58 x) (term31 x)). Qed.
Lemma lem1699799 (x : real) : (term57 x) = (term56 x).
Proof. exact (TRANS (@lem1699798 x) (@lem1699797 x)). Qed.
Lemma lem1699800 (P : real -> Prop) : (term45 P) = (term46 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1699801 : term3 = term59.
Proof. exact (@lem1699800 term34). Qed.
Lemma lem1699802 (x : real) : (term60 x) = (term33 x).
Proof. exact (eq_refl (term60 x)). Qed.
Lemma lem1699803 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1699804 (x : real) : (term61 x) = (term57 x).
Proof. exact (MK_COMB (@lem1699803) (@lem1699802 x)). Qed.
Lemma lem1699805 (x : real) : (term61 x) = (term56 x).
Proof. exact (TRANS (@lem1699804 x) (@lem1699799 x)). Qed.
Lemma lem1699806 : term62 = term63.
Proof. exact (fun_ext (fun x : real => @lem1699805 x)). Qed.
Lemma lem1699807 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1699808 : term59 = term64.
Proof. exact (MK_COMB (@lem1699807) (@lem1699806)). Qed.
Lemma lem1699809 : term3 = term64.
Proof. exact (TRANS (@lem1699801) (@lem1699808)). Qed.
Lemma lem1699868 {A : Type'} (P : Prop) (Q : A -> Prop) : (term65 A P Q) = (term66 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1699869 (P : Prop) (Q : real -> Prop) : (term67 P Q) = (term68 P Q).
Proof. exact (@lem1699868 real P Q). Qed.
Lemma lem1699870 (x : real) : (term69 x) = (term70 x).
Proof. exact (@lem1699869 (term58 x) (term52 x)). Qed.
Lemma lem1699871 (y : real) (x : real) : (term71 x y) = (term44 y x).
Proof. exact (eq_refl (term71 x y)). Qed.
Lemma lem1699872 (x : real) : (term72 x) = (term52 x).
Proof. exact (fun_ext (fun y : real => @lem1699871 y x)). Qed.
Lemma lem1699873 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1699874 (x : real) : (term73 x) = (term53 x).
Proof. exact (MK_COMB (@lem1699873) (@lem1699872 x)). Qed.
Lemma lem1699875 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1699876 (x : real) : (term69 x) = (term56 x).
Proof. exact (MK_COMB (@lem1699875 x) (@lem1699874 x)). Qed.
Lemma lem1699877 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1699878 (x : real) : (term74 x) = (term75 x).
Proof. exact (MK_COMB (@lem1699877) (@lem1699876 x)). Qed.
Lemma lem1699879 (y : real) (x : real) : (term71 x y) = (term44 y x).
Proof. exact (eq_refl (term71 x y)). Qed.
Lemma lem1699880 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1699881 (y : real) (x : real) : (term76 x y) = (term77 y x).
Proof. exact (MK_COMB (@lem1699880 x) (@lem1699879 y x)). Qed.
Lemma lem1699882 (x : real) : (term78 x) = (term79 x).
Proof. exact (fun_ext (fun y : real => @lem1699881 y x)). Qed.
Lemma lem1699883 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1699884 (x : real) : (term70 x) = (term80 x).
Proof. exact (MK_COMB (@lem1699883) (@lem1699882 x)). Qed.
Lemma lem1699885 (x : real) : ((term69 x) = (term70 x)) = ((term56 x) = (term80 x)).
Proof. exact (MK_COMB (@lem1699878 x) (@lem1699884 x)). Qed.
Lemma lem1699886 (x : real) : (term56 x) = (term80 x).
Proof. exact (EQ_MP (@lem1699885 x) (@lem1699870 x)). Qed.
Lemma lem1699887 : term63 = term81.
Proof. exact (fun_ext (fun x : real => @lem1699886 x)). Qed.
Lemma lem1699888 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1699890 : term64 = term82.
Proof. exact (MK_COMB (@lem1699888) (@lem1699887)). Qed.
Lemma lem1699891 : term3 = term82.
Proof. exact (TRANS (@lem1699809) (@lem1699890)). Qed.
Lemma lem1699892 (h1 : term3) : term82.
Proof. exact (EQ_MP (@lem1699891) (@lem1699770 h1)). Qed.
Lemma lem1699908 (x : real) (y : real) (z : real) : ((term83 x z y) = (term84 x y z)) = (term85 x y z).
Proof. exact (@lem17784 (term83 x z y) (term84 x y z)). Qed.
Lemma lem1699910 (z : real) : (term86 z) = (term86 z).
Proof. exact (eq_refl (term86 z)). Qed.
Lemma lem1699911 (x : real) (y : real) (z : real) : (term87 x y z) = (term88 x y z).
Proof. exact (MK_COMB (@lem1699910 z) (@lem1699908 x y z)). Qed.
Lemma lem1699912 (x : real) (y : real) (z : real) : (term20 x y z) = (term87 x y z).
Proof. exact (@lem17265 (term58 z) ((term83 x z y) = (term84 x y z))). Qed.
Lemma lem1699913 (x : real) (y : real) (z : real) : (term20 x y z) = (term88 x y z).
Proof. exact (TRANS (@lem1699912 x y z) (@lem1699911 x y z)). Qed.
Lemma lem1699914 (x : real) (y : real) : (term21 x y) = (term89 x y).
Proof. exact (fun_ext (fun z : real => @lem1699913 x y z)). Qed.
Lemma lem1699915 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699916 (x : real) (y : real) : (term22 x y) = (term90 x y).
Proof. exact (MK_COMB (@lem1699915) (@lem1699914 x y)). Qed.
Lemma lem1699917 (x : real) : (term23 x) = (term91 x).
Proof. exact (fun_ext (fun y : real => @lem1699916 x y)). Qed.
Lemma lem1699918 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699919 (x : real) : (term24 x) = (term92 x).
Proof. exact (MK_COMB (@lem1699918) (@lem1699917 x)). Qed.
Lemma lem1699920 : term25 = term93.
Proof. exact (fun_ext (fun x : real => @lem1699919 x)). Qed.
Lemma lem1699921 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699982 : term26 = term94.
Proof. exact (MK_COMB (@lem1699921) (@lem1699920)). Qed.
Lemma lem1699983 (h1 : term26) : term94.
Proof. exact (EQ_MP (@lem1699982) (@lem1699771 h1)). Qed.
Lemma lem1699984 (x : real) (n : nat) : (term16 x n) = (term16 x n).
Proof. exact (eq_refl (term16 x n)). Qed.
Lemma lem1699985 (x : real) : (term17 x) = (term17 x).
Proof. exact (fun_ext (fun n : nat => @lem1699984 x n)). Qed.
Lemma lem1699986 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1699987 (x : real) : (term18 x) = (term18 x).
Proof. exact (MK_COMB (@lem1699986) (@lem1699985 x)). Qed.
Lemma lem1699988 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1699987 x)). Qed.
Lemma lem1699989 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1699990 : term10 = term10.
Proof. exact (MK_COMB (@lem1699989) (@lem1699988)). Qed.
Lemma lem1700001 {A B : Type'} (P : type1413 A B) : (term95 A B P) = (term96 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem1700002 (P : type1622) : (term97 P) = (term98 P).
Proof. exact (@lem1700001 real nat P). Qed.
Lemma lem1700003 : term99 = term100.
Proof. exact (@lem1700002 term101). Qed.
Lemma lem1700004 (x : real) : (term102 x) = (term17 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1700005 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1700006 (x : real) (n : nat) : (term103 x n) = (term104 x n).
Proof. exact (MK_COMB (@lem1700004 x) (@lem1700005 n)). Qed.
Lemma lem1700007 (x : real) (n : nat) : (term104 x n) = (term16 x n).
Proof. exact (eq_refl (term104 x n)). Qed.
Lemma lem1700008 (x : real) (n : nat) : (term103 x n) = (term16 x n).
Proof. exact (TRANS (@lem1700006 x n) (@lem1700007 x n)). Qed.
Lemma lem1700009 (x : real) : (term105 x) = (term17 x).
Proof. exact (fun_ext (fun n : nat => @lem1700008 x n)). Qed.
Lemma lem1700010 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1700011 (x : real) : (term106 x) = (term18 x).
Proof. exact (MK_COMB (@lem1700010) (@lem1700009 x)). Qed.
Lemma lem1700012 : term107 = term19.
Proof. exact (fun_ext (fun x : real => @lem1700011 x)). Qed.
Lemma lem1700013 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700014 : term99 = term10.
Proof. exact (MK_COMB (@lem1700013) (@lem1700012)). Qed.
Lemma lem1700015 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1700016 : term108 = term109.
Proof. exact (MK_COMB (@lem1700015) (@lem1700014)). Qed.
Lemma lem1700017 (x : real) : (term102 x) = (term17 x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem1700018 (n : real -> nat) (x : real) : (n x) = (n x).
Proof. exact (eq_refl (n x)). Qed.
Lemma lem1700019 (n : real -> nat) (x : real) : (term110 n x) = (term111 n x).
Proof. exact (MK_COMB (@lem1700017 x) (@lem1700018 n x)). Qed.
Lemma lem1700020 (n : real -> nat) (x : real) : (term111 n x) = (term112 n x).
Proof. exact (eq_refl (term111 n x)). Qed.
Lemma lem1700021 (n : real -> nat) (x : real) : (term110 n x) = (term112 n x).
Proof. exact (TRANS (@lem1700019 n x) (@lem1700020 n x)). Qed.
Lemma lem1700022 (n : real -> nat) : (term113 n) = (term114 n).
Proof. exact (fun_ext (fun x : real => @lem1700021 n x)). Qed.
Lemma lem1700023 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700024 (n : real -> nat) : (term115 n) = (term116 n).
Proof. exact (MK_COMB (@lem1700023) (@lem1700022 n)). Qed.
Lemma lem1700025 : term117 = term118.
Proof. exact (fun_ext (fun n : real -> nat => @lem1700024 n)). Qed.
Lemma lem1700026 : (@ex (real -> nat)) = (@ex (real -> nat)).
Proof. exact (eq_refl (@ex (real -> nat))). Qed.
Lemma lem1700027 : term100 = term119.
Proof. exact (MK_COMB (@lem1700026) (@lem1700025)). Qed.
Lemma lem1700028 : (term99 = term100) = (term10 = term119).
Proof. exact (MK_COMB (@lem1700016) (@lem1700027)). Qed.
Lemma lem1700030 : term10 = term119.
Proof. exact (EQ_MP (@lem1700028) (@lem1700003)). Qed.
Lemma lem1700031 : term10 = term119.
Proof. exact (TRANS (@lem1699990) (@lem1700030)). Qed.
Lemma lem1700032 (h1 : term10) : term119.
Proof. exact (EQ_MP (@lem1700031) (@lem1699772 h1)). Qed.
Lemma lem1700033 (n : real -> nat) (h1 : term116 n) : term116 n.
Proof. exact (h1). Qed.
Lemma lem1700034 (x : real) (h1 : term80 x) : term80 x.
Proof. exact (h1). Qed.
Lemma lem1700035 (y : real) (x : real) (h1 : term77 y x) : term77 y x.
Proof. exact (h1). Qed.
Lemma lem1700098 (x : real) (y : real) (z : real) : (term88 x y z) = (term88 x y z).
Proof. exact (eq_refl (term88 x y z)). Qed.
Lemma lem1700099 (x : real) (y : real) : (term89 x y) = (term89 x y).
Proof. exact (fun_ext (fun z : real => @lem1700098 x y z)). Qed.
Lemma lem1700100 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700101 (x : real) (y : real) : (term90 x y) = (term90 x y).
Proof. exact (MK_COMB (@lem1700100) (@lem1700099 x y)). Qed.
Lemma lem1700102 (x : real) : (term91 x) = (term91 x).
Proof. exact (fun_ext (fun y : real => @lem1700101 x y)). Qed.
Lemma lem1700103 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700104 (x : real) : (term92 x) = (term92 x).
Proof. exact (MK_COMB (@lem1700103) (@lem1700102 x)). Qed.
Lemma lem1700105 : term93 = term93.
Proof. exact (fun_ext (fun x : real => @lem1700104 x)). Qed.
Lemma lem1700106 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700107 : term94 = term94.
Proof. exact (MK_COMB (@lem1700106) (@lem1700105)). Qed.
Lemma lem1700108 (h1 : term26) : term94.
Proof. exact (EQ_MP (@lem1700107) (@lem1699983 h1)). Qed.
Lemma lem1700117 (n : real -> nat) (x : real) : (term112 n x) = (term112 n x).
Proof. exact (eq_refl (term112 n x)). Qed.
Lemma lem1700118 (n : real -> nat) : (term114 n) = (term114 n).
Proof. exact (fun_ext (fun x : real => @lem1700117 n x)). Qed.
Lemma lem1700119 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700120 (n : real -> nat) : (term116 n) = (term116 n).
Proof. exact (MK_COMB (@lem1700119) (@lem1700118 n)). Qed.
Lemma lem1700121 (n : real -> nat) (h1 : term116 n) : term116 n.
Proof. exact (EQ_MP (@lem1700120 n) (@lem1700033 n h1)). Qed.
Lemma lem1700134 (y : real) (n : nat) (x : real) : (term41 y n x) = (term41 y n x).
Proof. exact (eq_refl (term41 y n x)). Qed.
Lemma lem1700135 (y : real) (x : real) : (term43 y x) = (term43 y x).
Proof. exact (fun_ext (fun n : nat => @lem1700134 y n x)). Qed.
Lemma lem1700136 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1700137 (y : real) (x : real) : (term44 y x) = (term44 y x).
Proof. exact (MK_COMB (@lem1700136) (@lem1700135 y x)). Qed.
Lemma lem1700148 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1700149 (y : real) (x : real) : (term77 y x) = (term77 y x).
Proof. exact (MK_COMB (@lem1700148 x) (@lem1700137 y x)). Qed.
Lemma lem1700150 (y : real) (x : real) (h1 : term77 y x) : term77 y x.
Proof. exact (EQ_MP (@lem1700149 y x) (@lem1700035 y x h1)). Qed.
Lemma lem1700151 (y : real) (x : real) (h1 : term77 y x) : term44 y x.
Proof. exact (proj2 (@lem1700150 y x h1)). Qed.
Lemma lem1700182 (x : real) (y : real) (z : real) : (term88 x y z) = (term120 x y z).
Proof. exact (@lem19490 (term121 x y z) (term122 z) (term123 x y z)). Qed.
Lemma lem1700183 (x : real) (y : real) : (term89 x y) = (term124 x y).
Proof. exact (fun_ext (fun z : real => @lem1700182 x y z)). Qed.
Lemma lem1700184 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700185 (x : real) (y : real) : (term90 x y) = (term125 x y).
Proof. exact (MK_COMB (@lem1700184) (@lem1700183 x y)). Qed.
Lemma lem1700186 (x : real) : (term91 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1700185 x y)). Qed.
Lemma lem1700187 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700188 (x : real) : (term92 x) = (term127 x).
Proof. exact (MK_COMB (@lem1700187) (@lem1700186 x)). Qed.
Lemma lem1700189 : term93 = term128.
Proof. exact (fun_ext (fun x : real => @lem1700188 x)). Qed.
Lemma lem1700190 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700192 : term94 = term129.
Proof. exact (MK_COMB (@lem1700190) (@lem1700189)). Qed.
Lemma lem1700193 (h1 : term26) : term129.
Proof. exact (EQ_MP (@lem1700192) (@lem1700108 h1)). Qed.
Lemma lem1700195 (n : real -> nat) (x : real) : (term112 n x) = (term112 n x).
Proof. exact (eq_refl (term112 n x)). Qed.
Lemma lem1700196 (n : real -> nat) : (term114 n) = (term114 n).
Proof. exact (fun_ext (fun x : real => @lem1700195 n x)). Qed.
Lemma lem1700197 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1700199 (n : real -> nat) : (term116 n) = (term116 n).
Proof. exact (MK_COMB (@lem1700197) (@lem1700196 n)). Qed.
Lemma lem1700200 (n : real -> nat) (h1 : term116 n) : term116 n.
Proof. exact (EQ_MP (@lem1700199 n) (@lem1700121 n h1)). Qed.
Lemma lem1700206 (y : real) (n : nat) (x : real) : (term41 y n x) = (term41 y n x).
Proof. exact (eq_refl (term41 y n x)). Qed.
Lemma lem1700207 (y : real) (x : real) : (term43 y x) = (term43 y x).
Proof. exact (fun_ext (fun n : nat => @lem1700206 y n x)). Qed.
Lemma lem1700208 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1700210 (y : real) (x : real) : (term44 y x) = (term44 y x).
Proof. exact (MK_COMB (@lem1700208) (@lem1700207 y x)). Qed.
Lemma lem1700211 (y : real) (x : real) (h1 : term77 y x) : term44 y x.
Proof. exact (EQ_MP (@lem1700210 y x) (@lem1700151 y x h1)). Qed.
Lemma lem1700212 (_26313 : real) (h1 : term26) : term130 _26313.
Proof. exact (@lem1700193 h1 _26313). Qed.
Lemma lem1700213 (_26313 : real) : (term130 _26313) = (term127 _26313).
Proof. exact (eq_refl (term130 _26313)). Qed.
Lemma lem1700214 (_26313 : real) (h1 : term26) : term127 _26313.
Proof. exact (EQ_MP (@lem1700213 _26313) (@lem1700212 _26313 h1)). Qed.
Lemma lem1700215 (_26313 : real) (_26314 : real) (h1 : term26) : term131 _26313 _26314.
Proof. exact (@lem1700214 _26313 h1 _26314). Qed.
Lemma lem1700216 (_26313 : real) (_26314 : real) : (term131 _26313 _26314) = (term125 _26313 _26314).
Proof. exact (eq_refl (term131 _26313 _26314)). Qed.
Lemma lem1700217 (_26313 : real) (_26314 : real) (h1 : term26) : term125 _26313 _26314.
Proof. exact (EQ_MP (@lem1700216 _26313 _26314) (@lem1700215 _26313 _26314 h1)). Qed.
Lemma lem1700218 (_26313 : real) (_26314 : real) (_26315 : real) (h1 : term26) : term132 _26313 _26314 _26315.
Proof. exact (@lem1700217 _26313 _26314 h1 _26315). Qed.
Lemma lem1700219 (_26313 : real) (_26314 : real) (_26315 : real) : (term132 _26313 _26314 _26315) = (term120 _26313 _26314 _26315).
Proof. exact (eq_refl (term132 _26313 _26314 _26315)). Qed.
Lemma lem1700220 (_26313 : real) (_26314 : real) (_26315 : real) (h1 : term26) : term120 _26313 _26314 _26315.
Proof. exact (EQ_MP (@lem1700219 _26313 _26314 _26315) (@lem1700218 _26313 _26314 _26315 h1)). Qed.
Lemma lem1700221 (_26316 : real) (n : real -> nat) (h1 : term116 n) : term133 n _26316.
Proof. exact (@lem1700200 n h1 _26316). Qed.
Lemma lem1700222 (n : real -> nat) (_26316 : real) : (term133 n _26316) = (term112 n _26316).
Proof. exact (eq_refl (term133 n _26316)). Qed.
Lemma lem1700224 (_26317 : nat) (y : real) (x : real) (h1 : term77 y x) : term134 y x _26317.
Proof. exact (@lem1700211 y x h1 _26317). Qed.
Lemma lem1700225 (y : real) (_26317 : nat) (x : real) : (term134 y x _26317) = (term41 y _26317 x).
Proof. exact (eq_refl (term134 y x _26317)). Qed.
Lemma lem1700234 (_26317 : nat) (y : real) (x : real) (h1 : term77 y x) : term41 y _26317 x.
Proof. exact (EQ_MP (@lem1700225 y _26317 x) (@lem1700224 _26317 y x h1)). Qed.
Lemma lem1700254 (_26313 : real) (_26314 : real) (_26315 : real) (h1 : term26) : term135 _26313 _26314 _26315.
Proof. exact (proj2 (@lem1700220 _26313 _26314 _26315 h1)). Qed.
Lemma lem1700256 (y : real) (x : real) (h1 : term77 y x) : term58 x.
Proof. exact (proj1 (@lem1700150 y x h1)). Qed.
Lemma lem1700257 (y : real) (x : real) (h1 : term77 y x) : term136 x.
Proof. exact (fun h0 : term122 x => @lem1700256 y x h1). Qed.
Lemma lem1700259 (p : Prop) : (term137 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1700260 (x : real) : (term136 x) = (term58 x).
Proof. exact (@lem1700259 (term58 x)). Qed.
Lemma lem1700261 (y : real) (x : real) (h1 : term77 y x) : term58 x.
Proof. exact (EQ_MP (@lem1700260 x) (@lem1700257 y x h1)). Qed.
Lemma lem1700263 (_26316 : real) (n : real -> nat) (h1 : term116 n) : term112 n _26316.
Proof. exact (EQ_MP (@lem1700222 n _26316) (@lem1700221 _26316 n h1)). Qed.
Lemma lem1700264 (y : real) (x : real) (n : real -> nat) (h1 : term116 n) : term138 n y x.
Proof. exact (@lem1700263 (real_div y x) n h1). Qed.
Lemma lem1700265 (y : real) (x : real) (n : real -> nat) (h1 : term116 n) : term139 n y x.
Proof. exact (fun h0 : term140 n y x => @lem1700264 y x n h1). Qed.
Lemma lem1700267 (p : Prop) : (term137 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1700268 (n : real -> nat) (y : real) (x : real) : (term139 n y x) = (term138 n y x).
Proof. exact (@lem1700267 (term138 n y x)). Qed.
Lemma lem1700269 (y : real) (x : real) (n : real -> nat) (h1 : term116 n) : term138 n y x.
Proof. exact (EQ_MP (@lem1700268 n y x) (@lem1700265 y x n h1)). Qed.
Lemma lem1700275 (q : Prop) (p : Prop) (r : Prop) : (term141 p q r) = (term141 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1700276 (_26313 : real) (_26314 : real) (_26315 : real) : (term135 _26313 _26314 _26315) = (term142 _26313 _26314 _26315).
Proof. exact (@lem1700275 (term143 _26313 _26315 _26314) (term122 _26315) (term84 _26313 _26314 _26315)). Qed.
Lemma lem1700290 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1700291 (_26313 : real) (_26314 : real) (_26315 : real) : (term144 _26313 _26314 _26315) = (term145 _26313 _26314 _26315).
Proof. exact (@lem1700290 (term84 _26313 _26314 _26315) (term122 _26315)). Qed.
Lemma lem1700297 (_26313 : real) (_26315 : real) (_26314 : real) : (term146 _26313 _26315 _26314) = (term146 _26313 _26315 _26314).
Proof. exact (eq_refl (term146 _26313 _26315 _26314)). Qed.
Lemma lem1700298 (_26313 : real) (_26314 : real) (_26315 : real) : (term142 _26313 _26314 _26315) = (term147 _26313 _26314 _26315).
Proof. exact (MK_COMB (@lem1700297 _26313 _26315 _26314) (@lem1700291 _26313 _26314 _26315)). Qed.
Lemma lem1700302 (q : Prop) (p : Prop) (r : Prop) : (term141 p q r) = (term141 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1700303 (_26313 : real) (_26314 : real) (_26315 : real) : (term147 _26313 _26314 _26315) = (term148 _26313 _26314 _26315).
Proof. exact (@lem1700302 (term84 _26313 _26314 _26315) (term143 _26313 _26315 _26314) (term122 _26315)). Qed.
Lemma lem1700319 (_26313 : real) (_26314 : real) (_26315 : real) : (term142 _26313 _26314 _26315) = (term148 _26313 _26314 _26315).
Proof. exact (TRANS (@lem1700298 _26313 _26314 _26315) (@lem1700303 _26313 _26314 _26315)). Qed.
Lemma lem1700320 (_26313 : real) (_26314 : real) (_26315 : real) : (term135 _26313 _26314 _26315) = (term148 _26313 _26314 _26315).
Proof. exact (TRANS (@lem1700276 _26313 _26314 _26315) (@lem1700319 _26313 _26314 _26315)). Qed.
Lemma lem1700321 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1700322 (_26313 : real) (_26314 : real) (_26315 : real) : (term149 _26313 _26314 _26315) = (term150 _26313 _26314 _26315).
Proof. exact (MK_COMB (@lem1700321) (@lem1700320 _26313 _26314 _26315)). Qed.
Lemma lem1700336 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1700337 (_26313 : real) (_26314 : real) (_26315 : real) : (term151 _26313 _26315 _26314) = (term152 _26313 _26314 _26315).
Proof. exact (@lem1700336 (term143 _26313 _26315 _26314) (term122 _26315)). Qed.
Lemma lem1700343 (_26313 : real) (_26314 : real) (_26315 : real) : (term153 _26313 _26314 _26315) = (term153 _26313 _26314 _26315).
Proof. exact (eq_refl (term153 _26313 _26314 _26315)). Qed.
Lemma lem1700344 (_26313 : real) (_26314 : real) (_26315 : real) : (term154 _26313 _26315 _26314) = (term148 _26313 _26314 _26315).
Proof. exact (MK_COMB (@lem1700343 _26313 _26314 _26315) (@lem1700337 _26313 _26314 _26315)). Qed.
Lemma lem1700355 (_26313 : real) (_26314 : real) (_26315 : real) : ((term135 _26313 _26314 _26315) = (term154 _26313 _26315 _26314)) = ((term148 _26313 _26314 _26315) = (term148 _26313 _26314 _26315)).
Proof. exact (MK_COMB (@lem1700322 _26313 _26314 _26315) (@lem1700344 _26313 _26314 _26315)). Qed.
Lemma lem1700357 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1700358 (x : Prop) : (x = x) = True.
Proof. exact (@lem1700357 Prop x). Qed.
Lemma lem1700359 (_26313 : real) (_26314 : real) (_26315 : real) : ((term148 _26313 _26314 _26315) = (term148 _26313 _26314 _26315)) = True.
Proof. exact (@lem1700358 (term148 _26313 _26314 _26315)). Qed.
Lemma lem1700360 (_26313 : real) (_26315 : real) (_26314 : real) : ((term135 _26313 _26314 _26315) = (term154 _26313 _26315 _26314)) = True.
Proof. exact (TRANS (@lem1700355 _26313 _26314 _26315) (@lem1700359 _26313 _26314 _26315)). Qed.
Lemma lem1700361 (_26313 : real) (_26315 : real) (_26314 : real) : True = ((term135 _26313 _26314 _26315) = (term154 _26313 _26315 _26314)).
Proof. exact (SYM (@lem1700360 _26313 _26315 _26314)). Qed.
Lemma lem1700362 (_26313 : real) (_26315 : real) (_26314 : real) : (term135 _26313 _26314 _26315) = (term154 _26313 _26315 _26314).
Proof. exact (EQ_MP (@lem1700361 _26313 _26315 _26314) (@lem0)). Qed.
Lemma lem1700363 (_26313 : real) (_26315 : real) (_26314 : real) (h1 : term26) : term154 _26313 _26315 _26314.
Proof. exact (EQ_MP (@lem1700362 _26313 _26315 _26314) (@lem1700254 _26313 _26314 _26315 h1)). Qed.
Lemma lem1700365 (b : Prop) (a : Prop) : (a \/ b) = (term155 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1700366 (_26313 : real) (_26314 : real) (_26315 : real) : (term154 _26313 _26315 _26314) = (term156 _26313 _26314 _26315).
Proof. exact (@lem1700365 (term151 _26313 _26315 _26314) (term84 _26313 _26314 _26315)). Qed.
Lemma lem1700368 (a : Prop) (b : Prop) : (term157 a b) = (term158 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1700369 (_26313 : real) (_26315 : real) (_26314 : real) : (term159 _26313 _26315 _26314) = (term160 _26313 _26315 _26314).
Proof. exact (@lem1700368 (term122 _26315) (term143 _26313 _26315 _26314)). Qed.
Lemma lem1700371 (a : Prop) : (term161 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1700372 (_26315 : real) : (term162 _26315) = (term58 _26315).
Proof. exact (@lem1700371 (term58 _26315)). Qed.
Lemma lem1700373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1700374 (_26315 : real) : (term163 _26315) = (term54 _26315).
Proof. exact (MK_COMB (@lem1700373) (@lem1700372 _26315)). Qed.
Lemma lem1700376 (a : Prop) : (term161 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1700377 (_26313 : real) (_26315 : real) (_26314 : real) : (term164 _26313 _26315 _26314) = (term83 _26313 _26315 _26314).
Proof. exact (@lem1700376 (term83 _26313 _26315 _26314)). Qed.
Lemma lem1700378 (_26313 : real) (_26315 : real) (_26314 : real) : (term160 _26313 _26315 _26314) = (term165 _26313 _26315 _26314).
Proof. exact (MK_COMB (@lem1700374 _26315) (@lem1700377 _26313 _26315 _26314)). Qed.
Lemma lem1700379 (_26313 : real) (_26315 : real) (_26314 : real) : (term159 _26313 _26315 _26314) = (term165 _26313 _26315 _26314).
Proof. exact (TRANS (@lem1700369 _26313 _26315 _26314) (@lem1700378 _26313 _26315 _26314)). Qed.
Lemma lem1700380 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1700381 (_26313 : real) (_26315 : real) (_26314 : real) : (term166 _26313 _26315 _26314) = (term167 _26313 _26315 _26314).
Proof. exact (MK_COMB (@lem1700380) (@lem1700379 _26313 _26315 _26314)). Qed.
Lemma lem1700382 (_26313 : real) (_26314 : real) (_26315 : real) : (term84 _26313 _26314 _26315) = (term84 _26313 _26314 _26315).
Proof. exact (eq_refl (term84 _26313 _26314 _26315)). Qed.
Lemma lem1700383 (_26313 : real) (_26314 : real) (_26315 : real) : (term156 _26313 _26314 _26315) = (term168 _26313 _26314 _26315).
Proof. exact (MK_COMB (@lem1700381 _26313 _26315 _26314) (@lem1700382 _26313 _26314 _26315)). Qed.
Lemma lem1700384 (_26313 : real) (_26314 : real) (_26315 : real) : (term154 _26313 _26315 _26314) = (term168 _26313 _26314 _26315).
Proof. exact (TRANS (@lem1700366 _26313 _26314 _26315) (@lem1700383 _26313 _26314 _26315)). Qed.
Lemma lem1700386 (n : real -> nat) (y : real) (x : real) (h1 : term116 n) (h2 : term77 y x) : term169 n y x.
Proof. exact (conj (@lem1700261 y x h2) (@lem1700269 y x n h1)). Qed.
Lemma lem1700388 (_26313 : real) (_26314 : real) (_26315 : real) (h1 : term26) : term168 _26313 _26314 _26315.
Proof. exact (EQ_MP (@lem1700384 _26313 _26314 _26315) (@lem1700363 _26313 _26315 _26314 h1)). Qed.
Lemma lem1700389 (n : real -> nat) (y : real) (x : real) (h1 : term26) : term170 n y x.
Proof. exact (@lem1700388 y (term171 n y x) x h1). Qed.
Lemma lem1700392 (n : real -> nat) (y : real) (x : real) (h1 : term26) (h2 : term116 n) (h3 : term77 y x) : term172 n y x.
Proof. exact (@lem1700389 n y x h1 (@lem1700386 n y x h2 h3)). Qed.
Lemma lem1700393 (n : real -> nat) (y : real) (x : real) (h1 : term26) (h2 : term116 n) (h3 : term77 y x) : term173 n y x.
Proof. exact (fun h0 : term174 n y x => @lem1700392 n y x h1 h2 h3). Qed.
Lemma lem1700395 (p : Prop) : (term137 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1700396 (n : real -> nat) (y : real) (x : real) : (term173 n y x) = (term172 n y x).
Proof. exact (@lem1700395 (term172 n y x)). Qed.
Lemma lem1700397 (n : real -> nat) (y : real) (x : real) (h1 : term26) (h2 : term116 n) (h3 : term77 y x) : term172 n y x.
Proof. exact (EQ_MP (@lem1700396 n y x) (@lem1700393 n y x h1 h2 h3)). Qed.
Lemma lem1700400 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1700402 (y : real) (_26317 : nat) (x : real) : (term41 y _26317 x) = (term175 y _26317 x).
Proof. exact (@lem1700400 (term27 y _26317 x)). Qed.
Lemma lem1700405 (_26317 : nat) (y : real) (x : real) (h1 : term77 y x) : term175 y _26317 x.
Proof. exact (EQ_MP (@lem1700402 y _26317 x) (@lem1700234 _26317 y x h1)). Qed.
Lemma lem1700406 (n : real -> nat) (y : real) (x : real) (h1 : term77 y x) : term176 n y x.
Proof. exact (@lem1700405 (term177 n y x) y x h1). Qed.
Lemma lem1700409 (n : real -> nat) (y : real) (x : real) (h1 : term26) (h2 : term116 n) (h3 : term77 y x) : False.
Proof. exact (@lem1700406 n y x h3 (@lem1700397 n y x h1 h2 h3)). Qed.
Lemma lem1700410 (n : real -> nat) (y : real) (x : real) (h1 : term26) (h2 : term116 n) (h3 : term77 y x) : term178.
Proof. exact (fun h0 : ~ False => @lem1700409 n y x h1 h2 h3). Qed.
Lemma lem1700412 (p : Prop) : (term137 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1700413 : term178 = False.
Proof. exact (@lem1700412 False). Qed.
Lemma lem1700414 (n : real -> nat) (y : real) (x : real) (h1 : term26) (h2 : term116 n) (h3 : term77 y x) : False.
Proof. exact (EQ_MP (@lem1700413) (@lem1700410 n y x h1 h2 h3)). Qed.
Lemma lem1700415 (n : real -> nat) (y : real) (x : real) (h1 : term26) (h2 : term116 n) (h3 : term77 y x) : (term116 n) = False.
Proof. exact (prop_ext (fun h4 : term116 n => @lem1700414 n y x h1 h2 h3) (fun h4 : False => @lem1700200 n h2)). Qed.
Lemma lem1700416 (n : real -> nat) (y : real) (x : real) (h1 : term26) (h2 : term116 n) (h3 : term77 y x) : False.
Proof. exact (EQ_MP (@lem1700415 n y x h1 h2 h3) (@lem1700200 n h2)). Qed.
Lemma lem1700417 (n : real -> nat) (y : real) (x : real) (h1 : term26) (h2 : term116 n) (h3 : term77 y x) : (term77 y x) = False.
Proof. exact (prop_ext (fun h4 : term77 y x => @lem1700416 n y x h1 h2 h3) (fun h4 : False => @lem1700150 y x h3)). Qed.
Lemma lem1700418 (n : real -> nat) (y : real) (x : real) (h1 : term26) (h2 : term116 n) (h3 : term77 y x) : False.
Proof. exact (EQ_MP (@lem1700417 n y x h1 h2 h3) (@lem1700150 y x h3)). Qed.
Lemma lem1700419 (n : real -> nat) (y : real) (x : real) (h1 : term26) (h2 : term116 n) (h3 : term77 y x) : (term116 n) = False.
Proof. exact (prop_ext (fun h4 : term116 n => @lem1700418 n y x h1 h2 h3) (fun h4 : False => @lem1700121 n h2)). Qed.
Lemma lem1700420 (n : real -> nat) (y : real) (x : real) (h1 : term26) (h2 : term116 n) (h3 : term77 y x) : False.
Proof. exact (EQ_MP (@lem1700419 n y x h1 h2 h3) (@lem1700121 n h2)). Qed.
Lemma lem1700421 (n : real -> nat) (x : real) (h1 : term26) (h2 : term116 n) (h3 : term80 x) : False.
Proof. exact (ex_elim (@lem1700034 x h3) (fun y : real => fun h0 : term79 x y => @lem1700420 n y x h1 h2 h0)). Qed.
Lemma lem1700422 (n : real -> nat) (h1 : term26) (h2 : term116 n) (h3 : term3) : False.
Proof. exact (ex_elim (@lem1699892 h3) (fun x : real => fun h0 : term81 x => @lem1700421 n x h1 h2 h0)). Qed.
Lemma lem1700423 (h1 : term26) (h2 : term10) (h3 : term3) : False.
Proof. exact (ex_elim (@lem1700032 h2) (fun n : real -> nat => fun h0 : term118 n => @lem1700422 n h1 h0 h3)). Qed.
Lemma lem1700424 (h1 : term26) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1700423 h1 h0 h2). Qed.
Lemma lem1700425 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1700426 (h1 : term26) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem1700425) (@lem1700424 h1 h2)). Qed.
Lemma lem1700427 (h1 : term3) : term13.
Proof. exact (fun h0 : term26 => @lem1700426 h0 h1). Qed.
Lemma lem1700428 : term15.
Proof. exact (fun h0 : term3 => @lem1700427 h0). Qed.
Lemma lem1700429 : term4.
Proof. exact (EQ_MP (@lem1699769) (@lem1700428)). Qed.
Lemma lem1700431 : term4.
Proof. exact (@lem1699605 (@lem1700429)). Qed.
Lemma lem1700432 (h1 : term3) : term12.
Proof. exact (@lem1700431 (@lem1699590 h1)). Qed.
Lemma lem1700433 (h1 : term3) : term8.
Proof. exact (@lem1700432 h1 (@lem1629051)). Qed.
Lemma lem1700434 (h1 : term3) : False.
Proof. exact (@lem1700433 h1 (@lem1699575)). Qed.
Lemma lem1700435 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1700434 h1) (fun h2 : False => @lem1699590 h1)). Qed.
Lemma lem1700436 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1700435 h1) (@lem1699590 h1)). Qed.
Lemma lem1700437 : term2.
Proof. exact (fun h0 : term3 => @lem1700436 h0). Qed.
Lemma lem1700438 : term1.
Proof. exact (EQ_MP (@lem1699589) (@lem1700437)). Qed.
