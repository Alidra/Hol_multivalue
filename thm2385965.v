Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2385965_term_abbrevs.
Require Import INT_DIVMOD_EXIST_0_spec.
Require Import SKOLEM_THM_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem2385715 {A B : Type'} (P : type1413 A B) : term0 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem2385716 {A B : Type'} (P : type1413 A B) : (term0 A B P) = ((term1 A B P) = (term2 A B P)).
Proof. exact (eq_refl (term0 A B P)). Qed.
Lemma lem2385723 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem2385716 A B P) (@lem2385715 A B P)). Qed.
Lemma lem2385724 (P : type1550) : (term3 P) = (term4 P).
Proof. exact (@lem2385723 int int P). Qed.
Lemma lem2385725 (m : int) : (term5 m) = (term6 m).
Proof. exact (@lem2385724 (term7 m)). Qed.
Lemma lem2385726 (m : int) (n : int) : (term8 m n) = (term9 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem2385727 (q : int) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem2385728 (m : int) (n : int) (q : int) : (term10 m n q) = (term11 m n q).
Proof. exact (MK_COMB (@lem2385726 m n) (@lem2385727 q)). Qed.
Lemma lem2385729 (m : int) (q : int) (n : int) : (term11 m n q) = (term12 m q n).
Proof. exact (eq_refl (term11 m n q)). Qed.
Lemma lem2385730 (m : int) (q : int) (n : int) : (term10 m n q) = (term12 m q n).
Proof. exact (TRANS (@lem2385728 m n q) (@lem2385729 m q n)). Qed.
Lemma lem2385731 (m : int) (n : int) : (term13 m n) = (term9 m n).
Proof. exact (fun_ext (fun q : int => @lem2385730 m q n)). Qed.
Lemma lem2385732 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2385733 (m : int) (n : int) : (term14 m n) = (term15 m n).
Proof. exact (MK_COMB (@lem2385732) (@lem2385731 m n)). Qed.
Lemma lem2385734 (m : int) : (term16 m) = (term17 m).
Proof. exact (fun_ext (fun n : int => @lem2385733 m n)). Qed.
Lemma lem2385735 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2385736 (m : int) : (term5 m) = (term18 m).
Proof. exact (MK_COMB (@lem2385735) (@lem2385734 m)). Qed.
Lemma lem2385737 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2385738 (m : int) : (term19 m) = (term20 m).
Proof. exact (MK_COMB (@lem2385737) (@lem2385736 m)). Qed.
Lemma lem2385739 (m : int) (n : int) : (term8 m n) = (term9 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem2385740 (q : int -> int) (n : int) : (q n) = (q n).
Proof. exact (eq_refl (q n)). Qed.
Lemma lem2385741 (m : int) (q : int -> int) (n : int) : (term21 m q n) = (term22 m q n).
Proof. exact (MK_COMB (@lem2385739 m n) (@lem2385740 q n)). Qed.
Lemma lem2385742 (m : int) (q : int -> int) (n : int) : (term22 m q n) = (term23 m q n).
Proof. exact (eq_refl (term22 m q n)). Qed.
Lemma lem2385743 (m : int) (q : int -> int) (n : int) : (term21 m q n) = (term23 m q n).
Proof. exact (TRANS (@lem2385741 m q n) (@lem2385742 m q n)). Qed.
Lemma lem2385744 (m : int) (q : int -> int) : (term24 m q) = (term25 m q).
Proof. exact (fun_ext (fun n : int => @lem2385743 m q n)). Qed.
Lemma lem2385745 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2385746 (m : int) (q : int -> int) : (term26 m q) = (term27 m q).
Proof. exact (MK_COMB (@lem2385745) (@lem2385744 m q)). Qed.
Lemma lem2385747 (m : int) : (term28 m) = (term29 m).
Proof. exact (fun_ext (fun q : int -> int => @lem2385746 m q)). Qed.
Lemma lem2385748 : (@ex (int -> int)) = (@ex (int -> int)).
Proof. exact (eq_refl (@ex (int -> int))). Qed.
Lemma lem2385749 (m : int) : (term6 m) = (term30 m).
Proof. exact (MK_COMB (@lem2385748) (@lem2385747 m)). Qed.
Lemma lem2385750 (m : int) : ((term5 m) = (term6 m)) = ((term18 m) = (term30 m)).
Proof. exact (MK_COMB (@lem2385738 m) (@lem2385749 m)). Qed.
Lemma lem2385751 (m : int) : (term18 m) = (term30 m).
Proof. exact (EQ_MP (@lem2385750 m) (@lem2385725 m)). Qed.
Lemma lem2385757 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem2385716 A B P) (@lem2385715 A B P)). Qed.
Lemma lem2385758 (P : type1550) : (term3 P) = (term4 P).
Proof. exact (@lem2385757 int int P). Qed.
Lemma lem2385759 (m : int) (q : int -> int) : (term31 m q) = (term32 m q).
Proof. exact (@lem2385758 (term33 m q)). Qed.
Lemma lem2385760 (m : int) (q : int -> int) (n : int) : (term34 m q n) = (term35 m q n).
Proof. exact (eq_refl (term34 m q n)). Qed.
Lemma lem2385761 (r : int) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem2385762 (m : int) (q : int -> int) (n : int) (r : int) : (term36 m q n r) = (term37 m q n r).
Proof. exact (MK_COMB (@lem2385760 m q n) (@lem2385761 r)). Qed.
Lemma lem2385763 (m : int) (q : int -> int) (n : int) (r : int) : (term37 m q n r) = (term38 m q n r).
Proof. exact (eq_refl (term37 m q n r)). Qed.
Lemma lem2385764 (m : int) (q : int -> int) (n : int) (r : int) : (term36 m q n r) = (term38 m q n r).
Proof. exact (TRANS (@lem2385762 m q n r) (@lem2385763 m q n r)). Qed.
Lemma lem2385765 (m : int) (q : int -> int) (n : int) : (term39 m q n) = (term35 m q n).
Proof. exact (fun_ext (fun r : int => @lem2385764 m q n r)). Qed.
Lemma lem2385766 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2385767 (m : int) (q : int -> int) (n : int) : (term40 m q n) = (term23 m q n).
Proof. exact (MK_COMB (@lem2385766) (@lem2385765 m q n)). Qed.
Lemma lem2385768 (m : int) (q : int -> int) : (term41 m q) = (term25 m q).
Proof. exact (fun_ext (fun n : int => @lem2385767 m q n)). Qed.
Lemma lem2385769 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2385770 (m : int) (q : int -> int) : (term31 m q) = (term27 m q).
Proof. exact (MK_COMB (@lem2385769) (@lem2385768 m q)). Qed.
Lemma lem2385771 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2385772 (m : int) (q : int -> int) : (term42 m q) = (term43 m q).
Proof. exact (MK_COMB (@lem2385771) (@lem2385770 m q)). Qed.
Lemma lem2385773 (m : int) (q : int -> int) (n : int) : (term34 m q n) = (term35 m q n).
Proof. exact (eq_refl (term34 m q n)). Qed.
Lemma lem2385774 (r : int -> int) (n : int) : (r n) = (r n).
Proof. exact (eq_refl (r n)). Qed.
Lemma lem2385775 (m : int) (q : int -> int) (r : int -> int) (n : int) : (term44 m q r n) = (term45 m q r n).
Proof. exact (MK_COMB (@lem2385773 m q n) (@lem2385774 r n)). Qed.
Lemma lem2385776 (m : int) (q : int -> int) (r : int -> int) (n : int) : (term45 m q r n) = (term46 m q r n).
Proof. exact (eq_refl (term45 m q r n)). Qed.
Lemma lem2385777 (m : int) (q : int -> int) (r : int -> int) (n : int) : (term44 m q r n) = (term46 m q r n).
Proof. exact (TRANS (@lem2385775 m q r n) (@lem2385776 m q r n)). Qed.
Lemma lem2385778 (m : int) (q : int -> int) (r : int -> int) : (term47 m q r) = (term48 m q r).
Proof. exact (fun_ext (fun n : int => @lem2385777 m q r n)). Qed.
Lemma lem2385779 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2385780 (m : int) (q : int -> int) (r : int -> int) : (term49 m q r) = (term50 m q r).
Proof. exact (MK_COMB (@lem2385779) (@lem2385778 m q r)). Qed.
Lemma lem2385781 (m : int) (q : int -> int) : (term51 m q) = (term52 m q).
Proof. exact (fun_ext (fun r : int -> int => @lem2385780 m q r)). Qed.
Lemma lem2385782 : (@ex (int -> int)) = (@ex (int -> int)).
Proof. exact (eq_refl (@ex (int -> int))). Qed.
Lemma lem2385783 (m : int) (q : int -> int) : (term32 m q) = (term53 m q).
Proof. exact (MK_COMB (@lem2385782) (@lem2385781 m q)). Qed.
Lemma lem2385784 (m : int) (q : int -> int) : ((term31 m q) = (term32 m q)) = ((term27 m q) = (term53 m q)).
Proof. exact (MK_COMB (@lem2385772 m q) (@lem2385783 m q)). Qed.
Lemma lem2385785 (m : int) (q : int -> int) : (term27 m q) = (term53 m q).
Proof. exact (EQ_MP (@lem2385784 m q) (@lem2385759 m q)). Qed.
Lemma lem2385810 (m : int) : (term29 m) = (term54 m).
Proof. exact (fun_ext (fun q : int -> int => @lem2385785 m q)). Qed.
Lemma lem2385811 : (@ex (int -> int)) = (@ex (int -> int)).
Proof. exact (eq_refl (@ex (int -> int))). Qed.
Lemma lem2385812 (m : int) : (term30 m) = (term55 m).
Proof. exact (MK_COMB (@lem2385811) (@lem2385810 m)). Qed.
Lemma lem2385817 (m : int) : (term18 m) = (term55 m).
Proof. exact (TRANS (@lem2385751 m) (@lem2385812 m)). Qed.
Lemma lem2385818 : term56 = term57.
Proof. exact (fun_ext (fun m : int => @lem2385817 m)). Qed.
Lemma lem2385819 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2385820 : term58 = term59.
Proof. exact (MK_COMB (@lem2385819) (@lem2385818)). Qed.
Lemma lem2385822 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem2385716 A B P) (@lem2385715 A B P)). Qed.
Lemma lem2385823 (P : type1548) : (term60 P) = (term61 P).
Proof. exact (@lem2385822 int (int -> int) P). Qed.
Lemma lem2385824 : term62 = term63.
Proof. exact (@lem2385823 term64). Qed.
Lemma lem2385825 (m : int) : (term65 m) = (term54 m).
Proof. exact (eq_refl (term65 m)). Qed.
Lemma lem2385826 (q : int -> int) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem2385827 (m : int) (q : int -> int) : (term66 m q) = (term67 m q).
Proof. exact (MK_COMB (@lem2385825 m) (@lem2385826 q)). Qed.
Lemma lem2385828 (m : int) (q : int -> int) : (term67 m q) = (term53 m q).
Proof. exact (eq_refl (term67 m q)). Qed.
Lemma lem2385829 (m : int) (q : int -> int) : (term66 m q) = (term53 m q).
Proof. exact (TRANS (@lem2385827 m q) (@lem2385828 m q)). Qed.
Lemma lem2385830 (m : int) : (term68 m) = (term54 m).
Proof. exact (fun_ext (fun q : int -> int => @lem2385829 m q)). Qed.
Lemma lem2385831 : (@ex (int -> int)) = (@ex (int -> int)).
Proof. exact (eq_refl (@ex (int -> int))). Qed.
Lemma lem2385832 (m : int) : (term69 m) = (term55 m).
Proof. exact (MK_COMB (@lem2385831) (@lem2385830 m)). Qed.
Lemma lem2385833 : term70 = term57.
Proof. exact (fun_ext (fun m : int => @lem2385832 m)). Qed.
Lemma lem2385834 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2385835 : term62 = term59.
Proof. exact (MK_COMB (@lem2385834) (@lem2385833)). Qed.
Lemma lem2385836 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2385837 : term71 = term72.
Proof. exact (MK_COMB (@lem2385836) (@lem2385835)). Qed.
Lemma lem2385838 (m : int) : (term65 m) = (term54 m).
Proof. exact (eq_refl (term65 m)). Qed.
Lemma lem2385839 (q : type1551) (m : int) : (q m) = (q m).
Proof. exact (eq_refl (q m)). Qed.
Lemma lem2385840 (q : type1551) (m : int) : (term73 q m) = (term74 q m).
Proof. exact (MK_COMB (@lem2385838 m) (@lem2385839 q m)). Qed.
Lemma lem2385841 (q : type1551) (m : int) : (term74 q m) = (term75 q m).
Proof. exact (eq_refl (term74 q m)). Qed.
Lemma lem2385842 (q : type1551) (m : int) : (term73 q m) = (term75 q m).
Proof. exact (TRANS (@lem2385840 q m) (@lem2385841 q m)). Qed.
Lemma lem2385843 (q : type1551) : (term76 q) = (term77 q).
Proof. exact (fun_ext (fun m : int => @lem2385842 q m)). Qed.
Lemma lem2385844 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2385845 (q : type1551) : (term78 q) = (term79 q).
Proof. exact (MK_COMB (@lem2385844) (@lem2385843 q)). Qed.
Lemma lem2385846 : term80 = term81.
Proof. exact (fun_ext (fun q : type1551 => @lem2385845 q)). Qed.
Lemma lem2385847 : (@ex (int -> int -> int)) = (@ex (int -> int -> int)).
Proof. exact (eq_refl (@ex (int -> int -> int))). Qed.
Lemma lem2385848 : term63 = term82.
Proof. exact (MK_COMB (@lem2385847) (@lem2385846)). Qed.
Lemma lem2385849 : (term62 = term63) = (term59 = term82).
Proof. exact (MK_COMB (@lem2385837) (@lem2385848)). Qed.
Lemma lem2385850 : term59 = term82.
Proof. exact (EQ_MP (@lem2385849) (@lem2385824)). Qed.
Lemma lem2385856 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem2385716 A B P) (@lem2385715 A B P)). Qed.
Lemma lem2385857 (P : type1548) : (term60 P) = (term61 P).
Proof. exact (@lem2385856 int (int -> int) P). Qed.
Lemma lem2385858 (q : type1551) : (term83 q) = (term84 q).
Proof. exact (@lem2385857 (term85 q)). Qed.
Lemma lem2385859 (q : type1551) (m : int) : (term86 q m) = (term87 q m).
Proof. exact (eq_refl (term86 q m)). Qed.
Lemma lem2385860 (r : int -> int) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem2385861 (q : type1551) (m : int) (r : int -> int) : (term88 q m r) = (term89 q m r).
Proof. exact (MK_COMB (@lem2385859 q m) (@lem2385860 r)). Qed.
Lemma lem2385862 (q : type1551) (m : int) (r : int -> int) : (term89 q m r) = (term90 q m r).
Proof. exact (eq_refl (term89 q m r)). Qed.
Lemma lem2385863 (q : type1551) (m : int) (r : int -> int) : (term88 q m r) = (term90 q m r).
Proof. exact (TRANS (@lem2385861 q m r) (@lem2385862 q m r)). Qed.
Lemma lem2385864 (q : type1551) (m : int) : (term91 q m) = (term87 q m).
Proof. exact (fun_ext (fun r : int -> int => @lem2385863 q m r)). Qed.
Lemma lem2385865 : (@ex (int -> int)) = (@ex (int -> int)).
Proof. exact (eq_refl (@ex (int -> int))). Qed.
Lemma lem2385866 (q : type1551) (m : int) : (term92 q m) = (term75 q m).
Proof. exact (MK_COMB (@lem2385865) (@lem2385864 q m)). Qed.
Lemma lem2385867 (q : type1551) : (term93 q) = (term77 q).
Proof. exact (fun_ext (fun m : int => @lem2385866 q m)). Qed.
Lemma lem2385868 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2385869 (q : type1551) : (term83 q) = (term79 q).
Proof. exact (MK_COMB (@lem2385868) (@lem2385867 q)). Qed.
Lemma lem2385870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2385871 (q : type1551) : (term94 q) = (term95 q).
Proof. exact (MK_COMB (@lem2385870) (@lem2385869 q)). Qed.
Lemma lem2385872 (q : type1551) (m : int) : (term86 q m) = (term87 q m).
Proof. exact (eq_refl (term86 q m)). Qed.
Lemma lem2385873 (r : type1551) (m : int) : (r m) = (r m).
Proof. exact (eq_refl (r m)). Qed.
Lemma lem2385874 (q : type1551) (r : type1551) (m : int) : (term96 q r m) = (term97 q r m).
Proof. exact (MK_COMB (@lem2385872 q m) (@lem2385873 r m)). Qed.
Lemma lem2385875 (q : type1551) (r : type1551) (m : int) : (term97 q r m) = (term98 q r m).
Proof. exact (eq_refl (term97 q r m)). Qed.
Lemma lem2385876 (q : type1551) (r : type1551) (m : int) : (term96 q r m) = (term98 q r m).
Proof. exact (TRANS (@lem2385874 q r m) (@lem2385875 q r m)). Qed.
Lemma lem2385877 (q : type1551) (r : type1551) : (term99 q r) = (term100 q r).
Proof. exact (fun_ext (fun m : int => @lem2385876 q r m)). Qed.
Lemma lem2385878 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2385879 (q : type1551) (r : type1551) : (term101 q r) = (term102 q r).
Proof. exact (MK_COMB (@lem2385878) (@lem2385877 q r)). Qed.
Lemma lem2385880 (q : type1551) : (term103 q) = (term104 q).
Proof. exact (fun_ext (fun r : type1551 => @lem2385879 q r)). Qed.
Lemma lem2385881 : (@ex (int -> int -> int)) = (@ex (int -> int -> int)).
Proof. exact (eq_refl (@ex (int -> int -> int))). Qed.
Lemma lem2385882 (q : type1551) : (term84 q) = (term105 q).
Proof. exact (MK_COMB (@lem2385881) (@lem2385880 q)). Qed.
Lemma lem2385883 (q : type1551) : ((term83 q) = (term84 q)) = ((term79 q) = (term105 q)).
Proof. exact (MK_COMB (@lem2385871 q) (@lem2385882 q)). Qed.
Lemma lem2385884 (q : type1551) : (term79 q) = (term105 q).
Proof. exact (EQ_MP (@lem2385883 q) (@lem2385858 q)). Qed.
Lemma lem2385913 : term81 = term106.
Proof. exact (fun_ext (fun q : type1551 => @lem2385884 q)). Qed.
Lemma lem2385914 : (@ex (int -> int -> int)) = (@ex (int -> int -> int)).
Proof. exact (eq_refl (@ex (int -> int -> int))). Qed.
Lemma lem2385915 : term82 = term107.
Proof. exact (MK_COMB (@lem2385914) (@lem2385913)). Qed.
Lemma lem2385920 : term59 = term107.
Proof. exact (TRANS (@lem2385850) (@lem2385915)). Qed.
Lemma lem2385921 : term58 = term107.
Proof. exact (TRANS (@lem2385820) (@lem2385920)). Qed.
Lemma lem2385922 : term107.
Proof. exact (EQ_MP (@lem2385921) (@lem2385714)). Qed.
Lemma lem2385923 : term108.
Proof. exact (fun _29199 : type1674 => @lem2385922). Qed.
Lemma lem2385924 {A B : Type'} (P : type1413 A B) : term0 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem2385925 {A B : Type'} (P : type1413 A B) : (term0 A B P) = ((term1 A B P) = (term2 A B P)).
Proof. exact (eq_refl (term0 A B P)). Qed.
Lemma lem2385928 {A B : Type'} (P : type1413 A B) : (term1 A B P) = (term2 A B P).
Proof. exact (EQ_MP (@lem2385925 A B P) (@lem2385924 A B P)). Qed.
Lemma lem2385929 (P : type1299) : (term109 P) = (term110 P).
Proof. exact (@lem2385928 type1674 type1551 P). Qed.
Lemma lem2385930 : term111 = term112.
Proof. exact (@lem2385929 term113). Qed.
Lemma lem2385931 (_29199 : type1674) : (term114 _29199) = term106.
Proof. exact (eq_refl (term114 _29199)). Qed.
Lemma lem2385932 (q : type1551) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem2385933 (_29199 : type1674) (q : type1551) : (term115 _29199 q) = (term116 q).
Proof. exact (MK_COMB (@lem2385931 _29199) (@lem2385932 q)). Qed.
Lemma lem2385934 (q : type1551) : (term116 q) = (term105 q).
Proof. exact (eq_refl (term116 q)). Qed.
Lemma lem2385935 (_29199 : type1674) (q : type1551) : (term115 _29199 q) = (term105 q).
Proof. exact (TRANS (@lem2385933 _29199 q) (@lem2385934 q)). Qed.
Lemma lem2385936 (_29199 : type1674) : (term117 _29199) = term106.
Proof. exact (fun_ext (fun q : type1551 => @lem2385935 _29199 q)). Qed.
Lemma lem2385937 : (@ex (int -> int -> int)) = (@ex (int -> int -> int)).
Proof. exact (eq_refl (@ex (int -> int -> int))). Qed.
Lemma lem2385938 (_29199 : type1674) : (term118 _29199) = term107.
Proof. exact (MK_COMB (@lem2385937) (@lem2385936 _29199)). Qed.
Lemma lem2385939 : term119 = term120.
Proof. exact (fun_ext (fun _29199 : type1674 => @lem2385938 _29199)). Qed.
Lemma lem2385940 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem2385941 : term111 = term108.
Proof. exact (MK_COMB (@lem2385940) (@lem2385939)). Qed.
Lemma lem2385942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2385943 : term121 = term122.
Proof. exact (MK_COMB (@lem2385942) (@lem2385941)). Qed.
Lemma lem2385944 (_29199 : type1674) : (term114 _29199) = term106.
Proof. exact (eq_refl (term114 _29199)). Qed.
Lemma lem2385945 (q : type1305) (_29199 : type1674) : (q _29199) = (q _29199).
Proof. exact (eq_refl (q _29199)). Qed.
Lemma lem2385946 (q : type1305) (_29199 : type1674) : (term123 q _29199) = (term124 q _29199).
Proof. exact (MK_COMB (@lem2385944 _29199) (@lem2385945 q _29199)). Qed.
Lemma lem2385947 (q : type1305) (_29199 : type1674) : (term124 q _29199) = (term125 q _29199).
Proof. exact (eq_refl (term124 q _29199)). Qed.
Lemma lem2385948 (q : type1305) (_29199 : type1674) : (term123 q _29199) = (term125 q _29199).
Proof. exact (TRANS (@lem2385946 q _29199) (@lem2385947 q _29199)). Qed.
Lemma lem2385949 (q : type1305) : (term126 q) = (term127 q).
Proof. exact (fun_ext (fun _29199 : type1674 => @lem2385948 q _29199)). Qed.
Lemma lem2385950 : (@all (prod nat (prod nat nat))) = (@all (prod nat (prod nat nat))).
Proof. exact (eq_refl (@all (prod nat (prod nat nat)))). Qed.
Lemma lem2385951 (q : type1305) : (term128 q) = (term129 q).
Proof. exact (MK_COMB (@lem2385950) (@lem2385949 q)). Qed.
Lemma lem2385952 : term130 = term131.
Proof. exact (fun_ext (fun q : type1305 => @lem2385951 q)). Qed.
Lemma lem2385953 : (@ex ((prod nat (prod nat nat)) -> int -> int -> int)) = (@ex ((prod nat (prod nat nat)) -> int -> int -> int)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat nat)) -> int -> int -> int))). Qed.
Lemma lem2385954 : term112 = term132.
Proof. exact (MK_COMB (@lem2385953) (@lem2385952)). Qed.
Lemma lem2385955 : (term111 = term112) = (term108 = term132).
Proof. exact (MK_COMB (@lem2385943) (@lem2385954)). Qed.
Lemma lem2385956 : term108 = term132.
Proof. exact (EQ_MP (@lem2385955) (@lem2385930)). Qed.
Lemma lem2385957 : term132.
Proof. exact (EQ_MP (@lem2385956) (@lem2385923)). Qed.
Lemma lem2385959 {A : Type'} : (@ex A) = (term133 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem2385960 : (@ex ((prod nat (prod nat nat)) -> int -> int -> int)) = term134.
Proof. exact (@lem2385959 type1305). Qed.
Lemma lem2385961 : term131 = term131.
Proof. exact (eq_refl term131). Qed.
Lemma lem2385962 : term132 = term135.
Proof. exact (MK_COMB (@lem2385960) (@lem2385961)). Qed.
Lemma lem2385963 : term135 = term136.
Proof. exact (eq_refl term135). Qed.
Lemma lem2385964 : term132 = term136.
Proof. exact (TRANS (@lem2385962) (@lem2385963)). Qed.
Lemma lem2385965 : term136.
Proof. exact (EQ_MP (@lem2385964) (@lem2385957)). Qed.
