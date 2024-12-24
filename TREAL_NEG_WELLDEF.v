Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_NEG_WELLDEF_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import thm0_spec.
Require Import thm1320004_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import treal_eq_spec.
Require Import treal_neg_spec.
Lemma lem1332672 (x : hreal) : term0 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1332673 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1332674 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1332673 x) (@lem1332672 x)). Qed.
Lemma lem1332675 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1332674 x y). Qed.
Lemma lem1332676 (y : hreal) (x : hreal) : (term2 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1332678 (x1 : hreal) : term3 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1332679 (x1 : hreal) : (term3 x1) = (term4 x1).
Proof. exact (eq_refl (term3 x1)). Qed.
Lemma lem1332680 (x1 : hreal) : term4 x1.
Proof. exact (EQ_MP (@lem1332679 x1) (@lem1332678 x1)). Qed.
Lemma lem1332681 (x1 : hreal) (y2 : hreal) : term5 x1 y2.
Proof. exact (@lem1332680 x1 y2). Qed.
Lemma lem1332682 (x1 : hreal) (y2 : hreal) : (term5 x1 y2) = (term6 x1 y2).
Proof. exact (eq_refl (term5 x1 y2)). Qed.
Lemma lem1332683 (x1 : hreal) (y2 : hreal) : term6 x1 y2.
Proof. exact (EQ_MP (@lem1332682 x1 y2) (@lem1332681 x1 y2)). Qed.
Lemma lem1332684 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term7 x1 y2 x2.
Proof. exact (@lem1332683 x1 y2 x2). Qed.
Lemma lem1332685 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term7 x1 y2 x2) = (term8 x1 y2 x2).
Proof. exact (eq_refl (term7 x1 y2 x2)). Qed.
Lemma lem1332686 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term8 x1 y2 x2.
Proof. exact (EQ_MP (@lem1332685 x1 y2 x2) (@lem1332684 x1 y2 x2)). Qed.
Lemma lem1332687 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term9 x1 y2 x2 y1.
Proof. exact (@lem1332686 x1 y2 x2 y1). Qed.
Lemma lem1332688 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term9 x1 y2 x2 y1) = ((term10 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term9 x1 y2 x2 y1)). Qed.
Lemma lem1332690 (y : hreal) : term11 y.
Proof. exact (@lem1323246 y). Qed.
Lemma lem1332691 (y : hreal) : (term11 y) = (term12 y).
Proof. exact (eq_refl (term11 y)). Qed.
Lemma lem1332692 (y : hreal) : term12 y.
Proof. exact (EQ_MP (@lem1332691 y) (@lem1332690 y)). Qed.
Lemma lem1332693 (y : hreal) (x : hreal) : term13 y x.
Proof. exact (@lem1332692 y x). Qed.
Lemma lem1332694 (y : hreal) (x : hreal) : (term13 y x) = ((term14 x y) = (@pair hreal hreal y x)).
Proof. exact (eq_refl (term13 y x)). Qed.
Lemma lem1332696 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term15 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1332697 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term15 _5106 _5107 P) = ((term16 _5106 _5107 P) = (term17 _5106 _5107 P)).
Proof. exact (eq_refl (term15 _5106 _5107 P)). Qed.
Lemma lem1332704 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term16 _5106 _5107 P) = (term17 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1332697 _5106 _5107 P) (@lem1332696 _5106 _5107 P)). Qed.
Lemma lem1332705 (P : type1233) : (term18 P) = (term19 P).
Proof. exact (@lem1332704 hreal hreal P). Qed.
Lemma lem1332706 : term20 = term21.
Proof. exact (@lem1332705 term22). Qed.
Lemma lem1332707 (x1 : prod hreal hreal) : (term23 x1) = (term24 x1).
Proof. exact (eq_refl (term23 x1)). Qed.
Lemma lem1332708 : term25 = term22.
Proof. exact (fun_ext (fun x1 : prod hreal hreal => @lem1332707 x1)). Qed.
Lemma lem1332709 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1332710 : term20 = term26.
Proof. exact (MK_COMB (@lem1332709) (@lem1332708)). Qed.
Lemma lem1332711 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1332712 : term27 = term28.
Proof. exact (MK_COMB (@lem1332711) (@lem1332710)). Qed.
Lemma lem1332713 (p1 : hreal) (p2 : hreal) : (term29 p1 p2) = (term30 p1 p2).
Proof. exact (eq_refl (term29 p1 p2)). Qed.
Lemma lem1332714 (p1 : hreal) : (term31 p1) = (term32 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1332713 p1 p2)). Qed.
Lemma lem1332715 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1332716 (p1 : hreal) : (term33 p1) = (term34 p1).
Proof. exact (MK_COMB (@lem1332715) (@lem1332714 p1)). Qed.
Lemma lem1332717 : term35 = term36.
Proof. exact (fun_ext (fun p1 : hreal => @lem1332716 p1)). Qed.
Lemma lem1332718 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1332719 : term21 = term37.
Proof. exact (MK_COMB (@lem1332718) (@lem1332717)). Qed.
Lemma lem1332720 : (term20 = term21) = (term26 = term37).
Proof. exact (MK_COMB (@lem1332712) (@lem1332719)). Qed.
Lemma lem1332721 : term26 = term37.
Proof. exact (EQ_MP (@lem1332720) (@lem1332706)). Qed.
Lemma lem1332739 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term16 _5106 _5107 P) = (term17 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1332697 _5106 _5107 P) (@lem1332696 _5106 _5107 P)). Qed.
Lemma lem1332740 (P : type1233) : (term18 P) = (term19 P).
Proof. exact (@lem1332739 hreal hreal P). Qed.
Lemma lem1332741 (p1 : hreal) (p2 : hreal) : (term38 p1 p2) = (term39 p1 p2).
Proof. exact (@lem1332740 (term40 p1 p2)). Qed.
Lemma lem1332742 (p1 : hreal) (p2 : hreal) (x2 : prod hreal hreal) : (term41 p1 p2 x2) = (term42 p1 p2 x2).
Proof. exact (eq_refl (term41 p1 p2 x2)). Qed.
Lemma lem1332743 (p1 : hreal) (p2 : hreal) : (term43 p1 p2) = (term40 p1 p2).
Proof. exact (fun_ext (fun x2 : prod hreal hreal => @lem1332742 p1 p2 x2)). Qed.
Lemma lem1332744 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1332745 (p1 : hreal) (p2 : hreal) : (term38 p1 p2) = (term30 p1 p2).
Proof. exact (MK_COMB (@lem1332744) (@lem1332743 p1 p2)). Qed.
Lemma lem1332746 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1332747 (p1 : hreal) (p2 : hreal) : (term44 p1 p2) = (term45 p1 p2).
Proof. exact (MK_COMB (@lem1332746) (@lem1332745 p1 p2)). Qed.
Lemma lem1332748 (p1 : hreal) (p2 : hreal) (p1' : hreal) (p2' : hreal) : (term46 p1 p2 p1' p2') = (term47 p1 p2 p1' p2').
Proof. exact (eq_refl (term46 p1 p2 p1' p2')). Qed.
Lemma lem1332749 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term48 p1 p2 p1') = (term49 p1 p2 p1').
Proof. exact (fun_ext (fun p2' : hreal => @lem1332748 p1 p2 p1' p2')). Qed.
Lemma lem1332750 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1332751 (p1 : hreal) (p2 : hreal) (p1' : hreal) : (term50 p1 p2 p1') = (term51 p1 p2 p1').
Proof. exact (MK_COMB (@lem1332750) (@lem1332749 p1 p2 p1')). Qed.
Lemma lem1332752 (p1 : hreal) (p2 : hreal) : (term52 p1 p2) = (term53 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1332751 p1 p2 p1')). Qed.
Lemma lem1332753 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1332754 (p1 : hreal) (p2 : hreal) : (term39 p1 p2) = (term54 p1 p2).
Proof. exact (MK_COMB (@lem1332753) (@lem1332752 p1 p2)). Qed.
Lemma lem1332755 (p1 : hreal) (p2 : hreal) : ((term38 p1 p2) = (term39 p1 p2)) = ((term30 p1 p2) = (term54 p1 p2)).
Proof. exact (MK_COMB (@lem1332747 p1 p2) (@lem1332754 p1 p2)). Qed.
Lemma lem1332756 (p1 : hreal) (p2 : hreal) : (term30 p1 p2) = (term54 p1 p2).
Proof. exact (EQ_MP (@lem1332755 p1 p2) (@lem1332741 p1 p2)). Qed.
Lemma lem1332772 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term10 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1332688 x1 y2 x2 y1) (@lem1332687 x1 y2 x2 y1)). Qed.
Lemma lem1332773 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term10 p1 p2 p1' p2') = ((hreal_add p1 p2') = (hreal_add p1' p2)).
Proof. exact (@lem1332772 p1 p2' p1' p2). Qed.
Lemma lem1332776 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1332777 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term55 p1 p2 p1' p2') = (term56 p1 p2' p1' p2).
Proof. exact (MK_COMB (@lem1332776) (@lem1332773 p1 p2' p1' p2)). Qed.
Lemma lem1332779 (y : hreal) (x : hreal) : (term14 x y) = (@pair hreal hreal y x).
Proof. exact (EQ_MP (@lem1332694 y x) (@lem1332693 y x)). Qed.
Lemma lem1332780 (p2 : hreal) (p1 : hreal) : (term14 p1 p2) = (@pair hreal hreal p2 p1).
Proof. exact (@lem1332779 p2 p1). Qed.
Lemma lem1332781 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1332782 (p2 : hreal) (p1 : hreal) : (term57 p1 p2) = (term58 p2 p1).
Proof. exact (MK_COMB (@lem1332781) (@lem1332780 p2 p1)). Qed.
Lemma lem1332784 (y : hreal) (x : hreal) : (term14 x y) = (@pair hreal hreal y x).
Proof. exact (EQ_MP (@lem1332694 y x) (@lem1332693 y x)). Qed.
Lemma lem1332785 (p2' : hreal) (p1' : hreal) : (term14 p1' p2') = (@pair hreal hreal p2' p1').
Proof. exact (@lem1332784 p2' p1'). Qed.
Lemma lem1332786 (p2 : hreal) (p1 : hreal) (p2' : hreal) (p1' : hreal) : (term59 p1 p2 p1' p2') = (term10 p2 p1 p2' p1').
Proof. exact (MK_COMB (@lem1332782 p2 p1) (@lem1332785 p2' p1')). Qed.
Lemma lem1332788 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term10 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1332688 x1 y2 x2 y1) (@lem1332687 x1 y2 x2 y1)). Qed.
Lemma lem1332789 (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1 : hreal) : (term10 p2 p1 p2' p1') = ((hreal_add p2 p1') = (hreal_add p2' p1)).
Proof. exact (@lem1332788 p2 p1' p2' p1). Qed.
Lemma lem1332792 (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1 : hreal) : (term59 p1 p2 p1' p2') = ((hreal_add p2 p1') = (hreal_add p2' p1)).
Proof. exact (TRANS (@lem1332786 p2 p1 p2' p1') (@lem1332789 p2 p1' p2' p1)). Qed.
Lemma lem1332793 (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1 : hreal) : (term47 p1 p2 p1' p2') = (term60 p2 p1' p2' p1).
Proof. exact (MK_COMB (@lem1332777 p1 p2' p1' p2) (@lem1332792 p2 p1' p2' p1)). Qed.
Lemma lem1332798 (p2 : hreal) (p1' : hreal) (p1 : hreal) : (term49 p1 p2 p1') = (term61 p2 p1' p1).
Proof. exact (fun_ext (fun p2' : hreal => @lem1332793 p2 p1' p2' p1)). Qed.
Lemma lem1332799 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1332800 (p2 : hreal) (p1' : hreal) (p1 : hreal) : (term51 p1 p2 p1') = (term62 p2 p1' p1).
Proof. exact (MK_COMB (@lem1332799) (@lem1332798 p2 p1' p1)). Qed.
Lemma lem1332807 (p2 : hreal) (p1 : hreal) : (term53 p1 p2) = (term63 p2 p1).
Proof. exact (fun_ext (fun p1' : hreal => @lem1332800 p2 p1' p1)). Qed.
Lemma lem1332808 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1332809 (p2 : hreal) (p1 : hreal) : (term54 p1 p2) = (term64 p2 p1).
Proof. exact (MK_COMB (@lem1332808) (@lem1332807 p2 p1)). Qed.
Lemma lem1332816 (p2 : hreal) (p1 : hreal) : (term30 p1 p2) = (term64 p2 p1).
Proof. exact (TRANS (@lem1332756 p1 p2) (@lem1332809 p2 p1)). Qed.
Lemma lem1332817 (p1 : hreal) : (term32 p1) = (term65 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1332816 p2 p1)). Qed.
Lemma lem1332818 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1332819 (p1 : hreal) : (term34 p1) = (term66 p1).
Proof. exact (MK_COMB (@lem1332818) (@lem1332817 p1)). Qed.
Lemma lem1332826 : term36 = term67.
Proof. exact (fun_ext (fun p1 : hreal => @lem1332819 p1)). Qed.
Lemma lem1332827 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1332828 : term37 = term68.
Proof. exact (MK_COMB (@lem1332827) (@lem1332826)). Qed.
Lemma lem1332835 : term26 = term68.
Proof. exact (TRANS (@lem1332721) (@lem1332828)). Qed.
Lemma lem1332836 : term68 = term26.
Proof. exact (SYM (@lem1332835)). Qed.
Lemma lem1332837 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (hreal_add p1 p2') = (hreal_add p1' p2).
Proof. exact (h1). Qed.
Lemma lem1332841 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1332676 y x) (@lem1332675 x y)). Qed.
Lemma lem1332842 (p1' : hreal) (p2 : hreal) : (hreal_add p2 p1') = (hreal_add p1' p2).
Proof. exact (@lem1332841 p1' p2). Qed.
Lemma lem1332843 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1332844 (p1' : hreal) (p2 : hreal) : (term69 p2 p1') = (term69 p1' p2).
Proof. exact (MK_COMB (@lem1332843) (@lem1332842 p1' p2)). Qed.
Lemma lem1332846 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1332676 y x) (@lem1332675 x y)). Qed.
Lemma lem1332847 (p1 : hreal) (p2' : hreal) : (hreal_add p2' p1) = (hreal_add p1 p2').
Proof. exact (@lem1332846 p1 p2'). Qed.
Lemma lem1332848 (p1' : hreal) (p2 : hreal) (p1 : hreal) (p2' : hreal) : ((hreal_add p2 p1') = (hreal_add p2' p1)) = ((hreal_add p1' p2) = (hreal_add p1 p2')).
Proof. exact (MK_COMB (@lem1332844 p1' p2) (@lem1332847 p1 p2')). Qed.
Lemma lem1332849 (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1 : hreal) : ((hreal_add p1' p2) = (hreal_add p1 p2')) = ((hreal_add p2 p1') = (hreal_add p2' p1)).
Proof. exact (SYM (@lem1332848 p1' p2 p1 p2')). Qed.
Lemma lem1332853 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (hreal_add p1 p2') = (hreal_add p1' p2).
Proof. exact (h1). Qed.
Lemma lem1332854 (p1' : hreal) (p2 : hreal) : (term69 p1' p2) = (term69 p1' p2).
Proof. exact (eq_refl (term69 p1' p2)). Qed.
Lemma lem1332855 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : ((hreal_add p1' p2) = (hreal_add p1 p2')) = ((hreal_add p1' p2) = (hreal_add p1' p2)).
Proof. exact (MK_COMB (@lem1332854 p1' p2) (@lem1332853 p1 p2' p1' p2 h1)). Qed.
Lemma lem1332857 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1332858 (x : hreal) : (x = x) = True.
Proof. exact (@lem1332857 hreal x). Qed.
Lemma lem1332859 (p1' : hreal) (p2 : hreal) : ((hreal_add p1' p2) = (hreal_add p1' p2)) = True.
Proof. exact (@lem1332858 (hreal_add p1' p2)). Qed.
Lemma lem1332860 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : ((hreal_add p1' p2) = (hreal_add p1 p2')) = True.
Proof. exact (TRANS (@lem1332855 p1 p2' p1' p2 h1) (@lem1332859 p1' p2)). Qed.
Lemma lem1332861 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : True = ((hreal_add p1' p2) = (hreal_add p1 p2')).
Proof. exact (SYM (@lem1332860 p1 p2' p1' p2 h1)). Qed.
Lemma lem1332862 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (hreal_add p1' p2) = (hreal_add p1 p2').
Proof. exact (EQ_MP (@lem1332861 p1 p2' p1' p2 h1) (@lem0)). Qed.
Lemma lem1332863 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (hreal_add p2 p1') = (hreal_add p2' p1).
Proof. exact (EQ_MP (@lem1332849 p2 p1' p2' p1) (@lem1332862 p1 p2' p1' p2 h1)). Qed.
Lemma lem1332864 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : ((hreal_add p1 p2') = (hreal_add p1' p2)) = ((hreal_add p2 p1') = (hreal_add p2' p1)).
Proof. exact (prop_ext (fun h2 : (hreal_add p1 p2') = (hreal_add p1' p2) => @lem1332863 p1 p2' p1' p2 h1) (fun h2 : (hreal_add p2 p1') = (hreal_add p2' p1) => @lem1332837 p1 p2' p1' p2 h1)). Qed.
Lemma lem1332865 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) (h1 : (hreal_add p1 p2') = (hreal_add p1' p2)) : (hreal_add p2 p1') = (hreal_add p2' p1).
Proof. exact (EQ_MP (@lem1332864 p1 p2' p1' p2 h1) (@lem1332837 p1 p2' p1' p2 h1)). Qed.
Lemma lem1332866 (p2 : hreal) (p1' : hreal) (p2' : hreal) (p1 : hreal) : term60 p2 p1' p2' p1.
Proof. exact (fun h0 : (hreal_add p1 p2') = (hreal_add p1' p2) => @lem1332865 p1 p2' p1' p2 h0). Qed.
Lemma lem1332871 (p2 : hreal) (p1' : hreal) (p1 : hreal) : term62 p2 p1' p1.
Proof. exact (fun p2' : hreal => @lem1332866 p2 p1' p2' p1). Qed.
Lemma lem1332876 (p2 : hreal) (p1 : hreal) : term64 p2 p1.
Proof. exact (fun p1' : hreal => @lem1332871 p2 p1' p1). Qed.
Lemma lem1332881 (p1 : hreal) : term66 p1.
Proof. exact (fun p2 : hreal => @lem1332876 p2 p1). Qed.
Lemma lem1332886 : term68.
Proof. exact (fun p1 : hreal => @lem1332881 p1). Qed.
Lemma lem1332887 : term26.
Proof. exact (EQ_MP (@lem1332836) (@lem1332886)). Qed.
