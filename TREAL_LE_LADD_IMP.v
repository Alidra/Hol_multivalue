Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_LE_LADD_IMP_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import HREAL_LE_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm1320004_spec.
Require Import thm1320203_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1823_spec.
Require Import treal_add_spec.
Require Import treal_le_spec.
Lemma lem1330692 (x : hreal) (y : hreal) (z : hreal) (h1 : (term0 x y z) = (term1 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (h1). Qed.
Lemma lem1330693 (x : hreal) (y : hreal) (z : hreal) (h1 : (term0 x y z) = (term1 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (SYM (@lem1330692 x y z h1)). Qed.
Lemma lem1330694 (x : hreal) (y : hreal) (z : hreal) (h1 : (term1 x y z) = (term0 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (h1). Qed.
Lemma lem1330695 (x : hreal) (y : hreal) (z : hreal) (h1 : (term1 x y z) = (term0 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (SYM (@lem1330694 x y z h1)). Qed.
Lemma lem1330696 (x : hreal) (y : hreal) (z : hreal) : ((term0 x y z) = (term1 x y z)) = ((term1 x y z) = (term0 x y z)).
Proof. exact (prop_ext (fun h1 : (term0 x y z) = (term1 x y z) => @lem1330693 x y z h1) (fun h1 : (term1 x y z) = (term0 x y z) => @lem1330695 x y z h1)). Qed.
Lemma lem1330697 (x : hreal) (y : hreal) : (term2 x y) = (term3 x y).
Proof. exact (fun_ext (fun z : hreal => @lem1330696 x y z)). Qed.
Lemma lem1330698 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330699 (x : hreal) (y : hreal) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1330698) (@lem1330697 x y)). Qed.
Lemma lem1330700 (x : hreal) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : hreal => @lem1330699 x y)). Qed.
Lemma lem1330701 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330702 (x : hreal) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1330701) (@lem1330700 x)). Qed.
Lemma lem1330703 : term10 = term11.
Proof. exact (fun_ext (fun x : hreal => @lem1330702 x)). Qed.
Lemma lem1330704 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330705 : term12 = term13.
Proof. exact (MK_COMB (@lem1330704) (@lem1330703)). Qed.
Lemma lem1330706 : term13.
Proof. exact (EQ_MP (@lem1330705) (@lem1320203)). Qed.
Lemma lem1330707 (m : hreal) : term14 m.
Proof. exact (@lem1321588 m). Qed.
Lemma lem1330708 (m : hreal) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1330709 (m : hreal) : term15 m.
Proof. exact (EQ_MP (@lem1330708 m) (@lem1330707 m)). Qed.
Lemma lem1330710 (m : hreal) (n : hreal) : term16 m n.
Proof. exact (@lem1330709 m n). Qed.
Lemma lem1330711 (m : hreal) (n : hreal) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1330712 (m : hreal) (n : hreal) : term17 m n.
Proof. exact (EQ_MP (@lem1330711 m n) (@lem1330710 m n)). Qed.
Lemma lem1330713 (m : hreal) (n : hreal) (p : hreal) : term18 m n p.
Proof. exact (@lem1330712 m n p). Qed.
Lemma lem1330714 (m : hreal) (n : hreal) (p : hreal) : (term18 m n p) = ((term19 n m p) = (hreal_le n p)).
Proof. exact (eq_refl (term18 m n p)). Qed.
Lemma lem1330716 (x : hreal) : term20 x.
Proof. exact (@lem1330706 x). Qed.
Lemma lem1330717 (x : hreal) : (term20 x) = (term9 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1330718 (x : hreal) : term9 x.
Proof. exact (EQ_MP (@lem1330717 x) (@lem1330716 x)). Qed.
Lemma lem1330719 (x : hreal) (y : hreal) : term21 x y.
Proof. exact (@lem1330718 x y). Qed.
Lemma lem1330720 (x : hreal) (y : hreal) : (term21 x y) = (term5 x y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1330721 (x : hreal) (y : hreal) : term5 x y.
Proof. exact (EQ_MP (@lem1330720 x y) (@lem1330719 x y)). Qed.
Lemma lem1330722 (x : hreal) (y : hreal) (z : hreal) : term22 x y z.
Proof. exact (@lem1330721 x y z). Qed.
Lemma lem1330723 (x : hreal) (y : hreal) (z : hreal) : (term22 x y z) = ((term1 x y z) = (term0 x y z)).
Proof. exact (eq_refl (term22 x y z)). Qed.
Lemma lem1330725 (x : hreal) : term23 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1330726 (x : hreal) : (term23 x) = (term24 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem1330727 (x : hreal) : term24 x.
Proof. exact (EQ_MP (@lem1330726 x) (@lem1330725 x)). Qed.
Lemma lem1330728 (x : hreal) (y : hreal) : term25 x y.
Proof. exact (@lem1330727 x y). Qed.
Lemma lem1330729 (y : hreal) (x : hreal) : (term25 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem1330734 (x : hreal) (y : hreal) (z : hreal) (h1 : (term0 x y z) = (term1 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (h1). Qed.
Lemma lem1330735 (x : hreal) (y : hreal) (z : hreal) (h1 : (term0 x y z) = (term1 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (SYM (@lem1330734 x y z h1)). Qed.
Lemma lem1330736 (x : hreal) (y : hreal) (z : hreal) (h1 : (term1 x y z) = (term0 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (h1). Qed.
Lemma lem1330737 (x : hreal) (y : hreal) (z : hreal) (h1 : (term1 x y z) = (term0 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (SYM (@lem1330736 x y z h1)). Qed.
Lemma lem1330738 (x : hreal) (y : hreal) (z : hreal) : ((term0 x y z) = (term1 x y z)) = ((term1 x y z) = (term0 x y z)).
Proof. exact (prop_ext (fun h1 : (term0 x y z) = (term1 x y z) => @lem1330735 x y z h1) (fun h1 : (term1 x y z) = (term0 x y z) => @lem1330737 x y z h1)). Qed.
Lemma lem1330739 (x : hreal) (y : hreal) : (term2 x y) = (term3 x y).
Proof. exact (fun_ext (fun z : hreal => @lem1330738 x y z)). Qed.
Lemma lem1330740 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330741 (x : hreal) (y : hreal) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1330740) (@lem1330739 x y)). Qed.
Lemma lem1330742 (x : hreal) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : hreal => @lem1330741 x y)). Qed.
Lemma lem1330743 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330744 (x : hreal) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1330743) (@lem1330742 x)). Qed.
Lemma lem1330745 : term10 = term11.
Proof. exact (fun_ext (fun x : hreal => @lem1330744 x)). Qed.
Lemma lem1330746 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330747 : term12 = term13.
Proof. exact (MK_COMB (@lem1330746) (@lem1330745)). Qed.
Lemma lem1330748 : term13.
Proof. exact (EQ_MP (@lem1330747) (@lem1320203)). Qed.
Lemma lem1330749 (m : hreal) : term14 m.
Proof. exact (@lem1321588 m). Qed.
Lemma lem1330750 (m : hreal) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1330751 (m : hreal) : term15 m.
Proof. exact (EQ_MP (@lem1330750 m) (@lem1330749 m)). Qed.
Lemma lem1330752 (m : hreal) (n : hreal) : term16 m n.
Proof. exact (@lem1330751 m n). Qed.
Lemma lem1330753 (m : hreal) (n : hreal) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1330754 (m : hreal) (n : hreal) : term17 m n.
Proof. exact (EQ_MP (@lem1330753 m n) (@lem1330752 m n)). Qed.
Lemma lem1330755 (m : hreal) (n : hreal) (p : hreal) : term18 m n p.
Proof. exact (@lem1330754 m n p). Qed.
Lemma lem1330756 (m : hreal) (n : hreal) (p : hreal) : (term18 m n p) = ((term19 n m p) = (hreal_le n p)).
Proof. exact (eq_refl (term18 m n p)). Qed.
Lemma lem1330758 (x : hreal) : term20 x.
Proof. exact (@lem1330748 x). Qed.
Lemma lem1330759 (x : hreal) : (term20 x) = (term9 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1330760 (x : hreal) : term9 x.
Proof. exact (EQ_MP (@lem1330759 x) (@lem1330758 x)). Qed.
Lemma lem1330761 (x : hreal) (y : hreal) : term21 x y.
Proof. exact (@lem1330760 x y). Qed.
Lemma lem1330762 (x : hreal) (y : hreal) : (term21 x y) = (term5 x y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1330763 (x : hreal) (y : hreal) : term5 x y.
Proof. exact (EQ_MP (@lem1330762 x y) (@lem1330761 x y)). Qed.
Lemma lem1330764 (x : hreal) (y : hreal) (z : hreal) : term22 x y z.
Proof. exact (@lem1330763 x y z). Qed.
Lemma lem1330765 (x : hreal) (y : hreal) (z : hreal) : (term22 x y z) = ((term1 x y z) = (term0 x y z)).
Proof. exact (eq_refl (term22 x y z)). Qed.
Lemma lem1330767 (x1 : hreal) : term26 x1.
Proof. exact (@lem1323802 x1). Qed.
Lemma lem1330768 (x1 : hreal) : (term26 x1) = (term27 x1).
Proof. exact (eq_refl (term26 x1)). Qed.
Lemma lem1330769 (x1 : hreal) : term27 x1.
Proof. exact (EQ_MP (@lem1330768 x1) (@lem1330767 x1)). Qed.
Lemma lem1330770 (x1 : hreal) (x2 : hreal) : term28 x1 x2.
Proof. exact (@lem1330769 x1 x2). Qed.
Lemma lem1330771 (x1 : hreal) (x2 : hreal) : (term28 x1 x2) = (term29 x1 x2).
Proof. exact (eq_refl (term28 x1 x2)). Qed.
Lemma lem1330772 (x1 : hreal) (x2 : hreal) : term29 x1 x2.
Proof. exact (EQ_MP (@lem1330771 x1 x2) (@lem1330770 x1 x2)). Qed.
Lemma lem1330773 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term30 x1 x2 y1.
Proof. exact (@lem1330772 x1 x2 y1). Qed.
Lemma lem1330774 (x1 : hreal) (x2 : hreal) (y1 : hreal) : (term30 x1 x2 y1) = (term31 x1 x2 y1).
Proof. exact (eq_refl (term30 x1 x2 y1)). Qed.
Lemma lem1330775 (x1 : hreal) (x2 : hreal) (y1 : hreal) : term31 x1 x2 y1.
Proof. exact (EQ_MP (@lem1330774 x1 x2 y1) (@lem1330773 x1 x2 y1)). Qed.
Lemma lem1330776 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : term32 x1 x2 y1 y2.
Proof. exact (@lem1330775 x1 x2 y1 y2). Qed.
Lemma lem1330777 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term32 x1 x2 y1 y2) = ((term33 x1 y1 x2 y2) = (term34 x1 x2 y1 y2)).
Proof. exact (eq_refl (term32 x1 x2 y1 y2)). Qed.
Lemma lem1330779 (x1 : hreal) : term35 x1.
Proof. exact (@lem1324956 x1). Qed.
Lemma lem1330780 (x1 : hreal) : (term35 x1) = (term36 x1).
Proof. exact (eq_refl (term35 x1)). Qed.
Lemma lem1330781 (x1 : hreal) : term36 x1.
Proof. exact (EQ_MP (@lem1330780 x1) (@lem1330779 x1)). Qed.
Lemma lem1330782 (x1 : hreal) (y2 : hreal) : term37 x1 y2.
Proof. exact (@lem1330781 x1 y2). Qed.
Lemma lem1330783 (x1 : hreal) (y2 : hreal) : (term37 x1 y2) = (term38 x1 y2).
Proof. exact (eq_refl (term37 x1 y2)). Qed.
Lemma lem1330784 (x1 : hreal) (y2 : hreal) : term38 x1 y2.
Proof. exact (EQ_MP (@lem1330783 x1 y2) (@lem1330782 x1 y2)). Qed.
Lemma lem1330785 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term39 x1 y2 x2.
Proof. exact (@lem1330784 x1 y2 x2). Qed.
Lemma lem1330786 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term39 x1 y2 x2) = (term40 x1 y2 x2).
Proof. exact (eq_refl (term39 x1 y2 x2)). Qed.
Lemma lem1330787 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term40 x1 y2 x2.
Proof. exact (EQ_MP (@lem1330786 x1 y2 x2) (@lem1330785 x1 y2 x2)). Qed.
Lemma lem1330788 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term41 x1 y2 x2 y1.
Proof. exact (@lem1330787 x1 y2 x2 y1). Qed.
Lemma lem1330789 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term41 x1 y2 x2 y1) = ((term42 x1 y1 x2 y2) = (term43 x1 y2 x2 y1)).
Proof. exact (eq_refl (term41 x1 y2 x2 y1)). Qed.
Lemma lem1330791 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term44 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1330792 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term44 _5106 _5107 P) = ((term45 _5106 _5107 P) = (term46 _5106 _5107 P)).
Proof. exact (eq_refl (term44 _5106 _5107 P)). Qed.
Lemma lem1330799 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term45 _5106 _5107 P) = (term46 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1330792 _5106 _5107 P) (@lem1330791 _5106 _5107 P)). Qed.
Lemma lem1330800 (P : type1233) : (term47 P) = (term48 P).
Proof. exact (@lem1330799 hreal hreal P). Qed.
Lemma lem1330801 : term49 = term50.
Proof. exact (@lem1330800 term51). Qed.
Lemma lem1330802 (x : prod hreal hreal) : (term52 x) = (term53 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1330803 : term54 = term51.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1330802 x)). Qed.
Lemma lem1330804 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1330805 : term49 = term55.
Proof. exact (MK_COMB (@lem1330804) (@lem1330803)). Qed.
Lemma lem1330806 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1330807 : term56 = term57.
Proof. exact (MK_COMB (@lem1330806) (@lem1330805)). Qed.
Lemma lem1330808 (p1 : hreal) (p2 : hreal) : (term58 p1 p2) = (term59 p1 p2).
Proof. exact (eq_refl (term58 p1 p2)). Qed.
Lemma lem1330809 (p1 : hreal) : (term60 p1) = (term61 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1330808 p1 p2)). Qed.
Lemma lem1330810 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330811 (p1 : hreal) : (term62 p1) = (term63 p1).
Proof. exact (MK_COMB (@lem1330810) (@lem1330809 p1)). Qed.
Lemma lem1330812 : term64 = term65.
Proof. exact (fun_ext (fun p1 : hreal => @lem1330811 p1)). Qed.
Lemma lem1330813 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330814 : term50 = term66.
Proof. exact (MK_COMB (@lem1330813) (@lem1330812)). Qed.
Lemma lem1330815 : (term49 = term50) = (term55 = term66).
Proof. exact (MK_COMB (@lem1330807) (@lem1330814)). Qed.
Lemma lem1330816 : term55 = term66.
Proof. exact (EQ_MP (@lem1330815) (@lem1330801)). Qed.
Lemma lem1330834 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term45 _5106 _5107 P) = (term46 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1330792 _5106 _5107 P) (@lem1330791 _5106 _5107 P)). Qed.
Lemma lem1330835 (P : type1233) : (term47 P) = (term48 P).
Proof. exact (@lem1330834 hreal hreal P). Qed.
Lemma lem1330836 (p1 : hreal) (p2 : hreal) : (term67 p1 p2) = (term68 p1 p2).
Proof. exact (@lem1330835 (term69 p1 p2)). Qed.
Lemma lem1330837 (y : prod hreal hreal) (p1 : hreal) (p2 : hreal) : (term70 p1 p2 y) = (term71 y p1 p2).
Proof. exact (eq_refl (term70 p1 p2 y)). Qed.
Lemma lem1330838 (p1 : hreal) (p2 : hreal) : (term72 p1 p2) = (term69 p1 p2).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1330837 y p1 p2)). Qed.
Lemma lem1330839 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1330840 (p1 : hreal) (p2 : hreal) : (term67 p1 p2) = (term59 p1 p2).
Proof. exact (MK_COMB (@lem1330839) (@lem1330838 p1 p2)). Qed.
Lemma lem1330841 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1330842 (p1 : hreal) (p2 : hreal) : (term73 p1 p2) = (term74 p1 p2).
Proof. exact (MK_COMB (@lem1330841) (@lem1330840 p1 p2)). Qed.
Lemma lem1330843 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term75 p1 p2 p1' p2') = (term76 p1' p2' p1 p2).
Proof. exact (eq_refl (term75 p1 p2 p1' p2')). Qed.
Lemma lem1330844 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term77 p1 p2 p1') = (term78 p1' p1 p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1330843 p1' p2' p1 p2)). Qed.
Lemma lem1330845 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330846 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term79 p1 p2 p1') = (term80 p1' p1 p2).
Proof. exact (MK_COMB (@lem1330845) (@lem1330844 p1' p1 p2)). Qed.
Lemma lem1330847 (p1 : hreal) (p2 : hreal) : (term81 p1 p2) = (term82 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1330846 p1' p1 p2)). Qed.
Lemma lem1330848 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330849 (p1 : hreal) (p2 : hreal) : (term68 p1 p2) = (term83 p1 p2).
Proof. exact (MK_COMB (@lem1330848) (@lem1330847 p1 p2)). Qed.
Lemma lem1330850 (p1 : hreal) (p2 : hreal) : ((term67 p1 p2) = (term68 p1 p2)) = ((term59 p1 p2) = (term83 p1 p2)).
Proof. exact (MK_COMB (@lem1330842 p1 p2) (@lem1330849 p1 p2)). Qed.
Lemma lem1330851 (p1 : hreal) (p2 : hreal) : (term59 p1 p2) = (term83 p1 p2).
Proof. exact (EQ_MP (@lem1330850 p1 p2) (@lem1330836 p1 p2)). Qed.
Lemma lem1330869 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term45 _5106 _5107 P) = (term46 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1330792 _5106 _5107 P) (@lem1330791 _5106 _5107 P)). Qed.
Lemma lem1330870 (P : type1233) : (term47 P) = (term48 P).
Proof. exact (@lem1330869 hreal hreal P). Qed.
Lemma lem1330871 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term84 p1' p2' p1 p2) = (term85 p1' p2' p1 p2).
Proof. exact (@lem1330870 (term86 p1' p2' p1 p2)). Qed.
Lemma lem1330872 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (z : prod hreal hreal) : (term87 p1' p2' p1 p2 z) = (term88 p1' p2' p1 p2 z).
Proof. exact (eq_refl (term87 p1' p2' p1 p2 z)). Qed.
Lemma lem1330873 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term89 p1' p2' p1 p2) = (term86 p1' p2' p1 p2).
Proof. exact (fun_ext (fun z : prod hreal hreal => @lem1330872 p1' p2' p1 p2 z)). Qed.
Lemma lem1330874 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1330875 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term84 p1' p2' p1 p2) = (term76 p1' p2' p1 p2).
Proof. exact (MK_COMB (@lem1330874) (@lem1330873 p1' p2' p1 p2)). Qed.
Lemma lem1330876 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1330877 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term90 p1' p2' p1 p2) = (term91 p1' p2' p1 p2).
Proof. exact (MK_COMB (@lem1330876) (@lem1330875 p1' p2' p1 p2)). Qed.
Lemma lem1330878 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) (p2'' : hreal) : (term92 p1' p2' p1 p2 p1'' p2'') = (term93 p1' p2' p1 p2 p1'' p2'').
Proof. exact (eq_refl (term92 p1' p2' p1 p2 p1'' p2'')). Qed.
Lemma lem1330879 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term94 p1' p2' p1 p2 p1'') = (term95 p1' p2' p1 p2 p1'').
Proof. exact (fun_ext (fun p2'' : hreal => @lem1330878 p1' p2' p1 p2 p1'' p2'')). Qed.
Lemma lem1330880 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330881 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) (p1'' : hreal) : (term96 p1' p2' p1 p2 p1'') = (term97 p1' p2' p1 p2 p1'').
Proof. exact (MK_COMB (@lem1330880) (@lem1330879 p1' p2' p1 p2 p1'')). Qed.
Lemma lem1330882 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term98 p1' p2' p1 p2) = (term99 p1' p2' p1 p2).
Proof. exact (fun_ext (fun p1'' : hreal => @lem1330881 p1' p2' p1 p2 p1'')). Qed.
Lemma lem1330883 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330884 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term85 p1' p2' p1 p2) = (term100 p1' p2' p1 p2).
Proof. exact (MK_COMB (@lem1330883) (@lem1330882 p1' p2' p1 p2)). Qed.
Lemma lem1330885 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : ((term84 p1' p2' p1 p2) = (term85 p1' p2' p1 p2)) = ((term76 p1' p2' p1 p2) = (term100 p1' p2' p1 p2)).
Proof. exact (MK_COMB (@lem1330877 p1' p2' p1 p2) (@lem1330884 p1' p2' p1 p2)). Qed.
Lemma lem1330886 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term76 p1' p2' p1 p2) = (term100 p1' p2' p1 p2).
Proof. exact (EQ_MP (@lem1330885 p1' p2' p1 p2) (@lem1330871 p1' p2' p1 p2)). Qed.
Lemma lem1330902 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term42 x1 y1 x2 y2) = (term43 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1330789 x1 y2 x2 y1) (@lem1330788 x1 y2 x2 y1)). Qed.
Lemma lem1330903 (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) : (term42 p1' p2' p1'' p2'') = (term43 p1' p2'' p1'' p2').
Proof. exact (@lem1330902 p1' p2'' p1'' p2'). Qed.
Lemma lem1330904 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1330905 (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) : (term101 p1' p2' p1'' p2'') = (term102 p1' p2'' p1'' p2').
Proof. exact (MK_COMB (@lem1330904) (@lem1330903 p1' p2'' p1'' p2')). Qed.
Lemma lem1330907 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term33 x1 y1 x2 y2) = (term34 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1330777 x1 x2 y1 y2) (@lem1330776 x1 x2 y1 y2)). Qed.
Lemma lem1330908 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term33 p1 p2 p1' p2') = (term34 p1 p1' p2 p2').
Proof. exact (@lem1330907 p1 p1' p2 p2'). Qed.
Lemma lem1330909 : treal_le = treal_le.
Proof. exact (eq_refl treal_le). Qed.
Lemma lem1330910 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term103 p1 p2 p1' p2') = (term104 p1 p1' p2 p2').
Proof. exact (MK_COMB (@lem1330909) (@lem1330908 p1 p1' p2 p2')). Qed.
Lemma lem1330912 (x1 : hreal) (x2 : hreal) (y1 : hreal) (y2 : hreal) : (term33 x1 y1 x2 y2) = (term34 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1330777 x1 x2 y1 y2) (@lem1330776 x1 x2 y1 y2)). Qed.
Lemma lem1330913 (p1 : hreal) (p1'' : hreal) (p2 : hreal) (p2'' : hreal) : (term33 p1 p2 p1'' p2'') = (term34 p1 p1'' p2 p2'').
Proof. exact (@lem1330912 p1 p1'' p2 p2''). Qed.
Lemma lem1330914 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p1'' : hreal) (p2 : hreal) (p2'' : hreal) : (term105 p1' p2' p1 p2 p1'' p2'') = (term106 p1' p2' p1 p1'' p2 p2'').
Proof. exact (MK_COMB (@lem1330910 p1 p1' p2 p2') (@lem1330913 p1 p1'' p2 p2'')). Qed.
Lemma lem1330916 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term42 x1 y1 x2 y2) = (term43 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1330789 x1 y2 x2 y1) (@lem1330788 x1 y2 x2 y1)). Qed.
Lemma lem1330917 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) : (term106 p1' p2' p1 p1'' p2 p2'') = (term107 p1' p2'' p1 p1'' p2 p2').
Proof. exact (@lem1330916 (hreal_add p1 p1') (hreal_add p2 p2'') (hreal_add p1 p1'') (hreal_add p2 p2')). Qed.
Lemma lem1330918 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) : (term105 p1' p2' p1 p2 p1'' p2'') = (term107 p1' p2'' p1 p1'' p2 p2').
Proof. exact (TRANS (@lem1330914 p1' p2' p1 p1'' p2 p2'') (@lem1330917 p1' p2'' p1 p1'' p2 p2')). Qed.
Lemma lem1330919 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) : (term93 p1' p2' p1 p2 p1'' p2'') = (term108 p1' p2'' p1 p1'' p2 p2').
Proof. exact (MK_COMB (@lem1330905 p1' p2'' p1'' p2') (@lem1330918 p1' p2'' p1 p1'' p2 p2')). Qed.
Lemma lem1330922 (p1' : hreal) (p1 : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) : (term95 p1' p2' p1 p2 p1'') = (term109 p1' p1 p1'' p2 p2').
Proof. exact (fun_ext (fun p2'' : hreal => @lem1330919 p1' p2'' p1 p1'' p2 p2')). Qed.
Lemma lem1330923 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330924 (p1' : hreal) (p1 : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) : (term97 p1' p2' p1 p2 p1'') = (term110 p1' p1 p1'' p2 p2').
Proof. exact (MK_COMB (@lem1330923) (@lem1330922 p1' p1 p1'' p2 p2')). Qed.
Lemma lem1330931 (p1' : hreal) (p1 : hreal) (p2 : hreal) (p2' : hreal) : (term99 p1' p2' p1 p2) = (term111 p1' p1 p2 p2').
Proof. exact (fun_ext (fun p1'' : hreal => @lem1330924 p1' p1 p1'' p2 p2')). Qed.
Lemma lem1330932 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330933 (p1' : hreal) (p1 : hreal) (p2 : hreal) (p2' : hreal) : (term100 p1' p2' p1 p2) = (term112 p1' p1 p2 p2').
Proof. exact (MK_COMB (@lem1330932) (@lem1330931 p1' p1 p2 p2')). Qed.
Lemma lem1330940 (p1' : hreal) (p1 : hreal) (p2 : hreal) (p2' : hreal) : (term76 p1' p2' p1 p2) = (term112 p1' p1 p2 p2').
Proof. exact (TRANS (@lem1330886 p1' p2' p1 p2) (@lem1330933 p1' p1 p2 p2')). Qed.
Lemma lem1330941 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term78 p1' p1 p2) = (term113 p1' p1 p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1330940 p1' p1 p2 p2')). Qed.
Lemma lem1330942 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330943 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term80 p1' p1 p2) = (term114 p1' p1 p2).
Proof. exact (MK_COMB (@lem1330942) (@lem1330941 p1' p1 p2)). Qed.
Lemma lem1330950 (p1 : hreal) (p2 : hreal) : (term82 p1 p2) = (term115 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1330943 p1' p1 p2)). Qed.
Lemma lem1330951 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330952 (p1 : hreal) (p2 : hreal) : (term83 p1 p2) = (term116 p1 p2).
Proof. exact (MK_COMB (@lem1330951) (@lem1330950 p1 p2)). Qed.
Lemma lem1330959 (p1 : hreal) (p2 : hreal) : (term59 p1 p2) = (term116 p1 p2).
Proof. exact (TRANS (@lem1330851 p1 p2) (@lem1330952 p1 p2)). Qed.
Lemma lem1330960 (p1 : hreal) : (term61 p1) = (term117 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1330959 p1 p2)). Qed.
Lemma lem1330961 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330962 (p1 : hreal) : (term63 p1) = (term118 p1).
Proof. exact (MK_COMB (@lem1330961) (@lem1330960 p1)). Qed.
Lemma lem1330969 : term65 = term119.
Proof. exact (fun_ext (fun p1 : hreal => @lem1330962 p1)). Qed.
Lemma lem1330970 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330971 : term66 = term120.
Proof. exact (MK_COMB (@lem1330970) (@lem1330969)). Qed.
Lemma lem1330978 : term55 = term120.
Proof. exact (TRANS (@lem1330816) (@lem1330971)). Qed.
Lemma lem1330979 : term120 = term55.
Proof. exact (SYM (@lem1330978)). Qed.
Lemma lem1331011 (x : hreal) (y : hreal) (z : hreal) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1330765 x y z) (@lem1330764 x y z)). Qed.
Lemma lem1331012 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2'' : hreal) : (term121 p1 p1' p2 p2'') = (term122 p1 p1' p2 p2'').
Proof. exact (@lem1331011 p1 p1' (hreal_add p2 p2'')). Qed.
Lemma lem1331013 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1331014 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2'' : hreal) : (term123 p1 p1' p2 p2'') = (term124 p1 p1' p2 p2'').
Proof. exact (MK_COMB (@lem1331013) (@lem1331012 p1 p1' p2 p2'')). Qed.
Lemma lem1331016 (x : hreal) (y : hreal) (z : hreal) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1330765 x y z) (@lem1330764 x y z)). Qed.
Lemma lem1331017 (p1 : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) : (term121 p1 p1'' p2 p2') = (term122 p1 p1'' p2 p2').
Proof. exact (@lem1331016 p1 p1'' (hreal_add p2 p2')). Qed.
Lemma lem1331018 (p1' : hreal) (p2'' : hreal) (p1 : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) : (term107 p1' p2'' p1 p1'' p2 p2') = (term125 p1' p2'' p1 p1'' p2 p2').
Proof. exact (MK_COMB (@lem1331014 p1 p1' p2 p2'') (@lem1331017 p1 p1'' p2 p2')). Qed.
Lemma lem1331020 (m : hreal) (n : hreal) (p : hreal) : (term19 n m p) = (hreal_le n p).
Proof. exact (EQ_MP (@lem1330756 m n p) (@lem1330755 m n p)). Qed.
Lemma lem1331021 (p1 : hreal) (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) : (term125 p1' p2'' p1 p1'' p2 p2') = (term126 p1' p2'' p1'' p2 p2').
Proof. exact (@lem1331020 p1 (term0 p1' p2 p2'') (term0 p1'' p2 p2')). Qed.
Lemma lem1331024 (p1 : hreal) (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) : (term107 p1' p2'' p1 p1'' p2 p2') = (term126 p1' p2'' p1'' p2 p2').
Proof. exact (TRANS (@lem1331018 p1' p2'' p1 p1'' p2 p2') (@lem1331021 p1 p1' p2'' p1'' p2 p2')). Qed.
Lemma lem1331025 (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2' : hreal) : (term102 p1' p2'' p1'' p2') = (term102 p1' p2'' p1'' p2').
Proof. exact (eq_refl (term102 p1' p2'' p1'' p2')). Qed.
Lemma lem1331026 (p1 : hreal) (p1' : hreal) (p2'' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) : (term108 p1' p2'' p1 p1'' p2 p2') = (term127 p1' p2'' p1'' p2 p2').
Proof. exact (MK_COMB (@lem1331025 p1' p2'' p1'' p2') (@lem1331024 p1 p1' p2'' p1'' p2 p2')). Qed.
Lemma lem1331029 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) : (term109 p1' p1 p1'' p2 p2') = (term128 p1' p1'' p2 p2').
Proof. exact (fun_ext (fun p2'' : hreal => @lem1331026 p1 p1' p2'' p1'' p2 p2')). Qed.
Lemma lem1331030 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331031 (p1 : hreal) (p1' : hreal) (p1'' : hreal) (p2 : hreal) (p2' : hreal) : (term110 p1' p1 p1'' p2 p2') = (term129 p1' p1'' p2 p2').
Proof. exact (MK_COMB (@lem1331030) (@lem1331029 p1 p1' p1'' p2 p2')). Qed.
Lemma lem1331036 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term111 p1' p1 p2 p2') = (term130 p1' p2 p2').
Proof. exact (fun_ext (fun p1'' : hreal => @lem1331031 p1 p1' p1'' p2 p2')). Qed.
Lemma lem1331037 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331038 (p1 : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term112 p1' p1 p2 p2') = (term131 p1' p2 p2').
Proof. exact (MK_COMB (@lem1331037) (@lem1331036 p1 p1' p2 p2')). Qed.
Lemma lem1331043 (p1 : hreal) (p1' : hreal) (p2 : hreal) : (term113 p1' p1 p2) = (term132 p1' p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1331038 p1 p1' p2 p2')). Qed.
Lemma lem1331044 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331045 (p1 : hreal) (p1' : hreal) (p2 : hreal) : (term114 p1' p1 p2) = (term133 p1' p2).
Proof. exact (MK_COMB (@lem1331044) (@lem1331043 p1 p1' p2)). Qed.
Lemma lem1331050 (p1 : hreal) (p2 : hreal) : (term115 p1 p2) = (term134 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1331045 p1 p1' p2)). Qed.
Lemma lem1331051 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331052 (p1 : hreal) (p2 : hreal) : (term116 p1 p2) = (term135 p2).
Proof. exact (MK_COMB (@lem1331051) (@lem1331050 p1 p2)). Qed.
Lemma lem1331057 (p1 : hreal) : (term117 p1) = term136.
Proof. exact (fun_ext (fun p2 : hreal => @lem1331052 p1 p2)). Qed.
Lemma lem1331058 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331059 (p1 : hreal) : (term118 p1) = term137.
Proof. exact (MK_COMB (@lem1331058) (@lem1331057 p1)). Qed.
Lemma lem1331064 : term119 = term138.
Proof. exact (fun_ext (fun p1 : hreal => @lem1331059 p1)). Qed.
Lemma lem1331065 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331066 : term120 = term139.
Proof. exact (MK_COMB (@lem1331065) (@lem1331064)). Qed.
Lemma lem1331068 {A : Type'} (t : Prop) : (term140 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1331069 (t : Prop) : (term141 t) = t.
Proof. exact (@lem1331068 hreal t). Qed.
Lemma lem1331070 : term139 = term137.
Proof. exact (@lem1331069 term137). Qed.
Lemma lem1331097 : term120 = term137.
Proof. exact (TRANS (@lem1331066) (@lem1331070)). Qed.
Lemma lem1331098 : term137 = term120.
Proof. exact (SYM (@lem1331097)). Qed.
Lemma lem1331122 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1330729 y x) (@lem1330728 x y)). Qed.
Lemma lem1331123 (p2'' : hreal) (p1' : hreal) : (hreal_add p1' p2'') = (hreal_add p2'' p1').
Proof. exact (@lem1331122 p2'' p1'). Qed.
Lemma lem1331124 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1331125 (p2'' : hreal) (p1' : hreal) : (term142 p1' p2'') = (term142 p2'' p1').
Proof. exact (MK_COMB (@lem1331124) (@lem1331123 p2'' p1')). Qed.
Lemma lem1331127 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1330729 y x) (@lem1330728 x y)). Qed.
Lemma lem1331128 (p2' : hreal) (p1'' : hreal) : (hreal_add p1'' p2') = (hreal_add p2' p1'').
Proof. exact (@lem1331127 p2' p1''). Qed.
Lemma lem1331129 (p2'' : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term43 p1' p2'' p1'' p2') = (term43 p2'' p1' p2' p1'').
Proof. exact (MK_COMB (@lem1331125 p2'' p1') (@lem1331128 p2' p1'')). Qed.
Lemma lem1331130 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1331131 (p2'' : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term102 p1' p2'' p1'' p2') = (term102 p2'' p1' p2' p1'').
Proof. exact (MK_COMB (@lem1331130) (@lem1331129 p2'' p1' p2' p1'')). Qed.
Lemma lem1331133 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1330729 y x) (@lem1330728 x y)). Qed.
Lemma lem1331134 (p2 : hreal) (p2'' : hreal) (p1' : hreal) : (term0 p1' p2 p2'') = (term1 p2 p2'' p1').
Proof. exact (@lem1331133 (hreal_add p2 p2'') p1'). Qed.
Lemma lem1331135 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1331136 (p2 : hreal) (p2'' : hreal) (p1' : hreal) : (term143 p1' p2 p2'') = (term144 p2 p2'' p1').
Proof. exact (MK_COMB (@lem1331135) (@lem1331134 p2 p2'' p1')). Qed.
Lemma lem1331138 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1330729 y x) (@lem1330728 x y)). Qed.
Lemma lem1331139 (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term0 p1'' p2 p2') = (term1 p2 p2' p1'').
Proof. exact (@lem1331138 (hreal_add p2 p2') p1''). Qed.
Lemma lem1331140 (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term126 p1' p2'' p1'' p2 p2') = (term145 p2'' p1' p2 p2' p1'').
Proof. exact (MK_COMB (@lem1331136 p2 p2'' p1') (@lem1331139 p2 p2' p1'')). Qed.
Lemma lem1331141 (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term127 p1' p2'' p1'' p2 p2') = (term146 p2'' p1' p2 p2' p1'').
Proof. exact (MK_COMB (@lem1331131 p2'' p1' p2' p1'') (@lem1331140 p2'' p1' p2 p2' p1'')). Qed.
Lemma lem1331142 (p1' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term128 p1' p1'' p2 p2') = (term147 p1' p2 p2' p1'').
Proof. exact (fun_ext (fun p2'' : hreal => @lem1331141 p2'' p1' p2 p2' p1'')). Qed.
Lemma lem1331143 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331144 (p1' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term129 p1' p1'' p2 p2') = (term148 p1' p2 p2' p1'').
Proof. exact (MK_COMB (@lem1331143) (@lem1331142 p1' p2 p2' p1'')). Qed.
Lemma lem1331145 (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term130 p1' p2 p2') = (term149 p1' p2 p2').
Proof. exact (fun_ext (fun p1'' : hreal => @lem1331144 p1' p2 p2' p1'')). Qed.
Lemma lem1331146 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331147 (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term131 p1' p2 p2') = (term150 p1' p2 p2').
Proof. exact (MK_COMB (@lem1331146) (@lem1331145 p1' p2 p2')). Qed.
Lemma lem1331148 (p1' : hreal) (p2 : hreal) : (term132 p1' p2) = (term151 p1' p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1331147 p1' p2 p2')). Qed.
Lemma lem1331149 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331150 (p1' : hreal) (p2 : hreal) : (term133 p1' p2) = (term152 p1' p2).
Proof. exact (MK_COMB (@lem1331149) (@lem1331148 p1' p2)). Qed.
Lemma lem1331151 (p2 : hreal) : (term134 p2) = (term153 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1331150 p1' p2)). Qed.
Lemma lem1331152 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331153 (p2 : hreal) : (term135 p2) = (term154 p2).
Proof. exact (MK_COMB (@lem1331152) (@lem1331151 p2)). Qed.
Lemma lem1331154 : term136 = term155.
Proof. exact (fun_ext (fun p2 : hreal => @lem1331153 p2)). Qed.
Lemma lem1331155 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331156 : term137 = term156.
Proof. exact (MK_COMB (@lem1331155) (@lem1331154)). Qed.
Lemma lem1331157 : term156 = term137.
Proof. exact (SYM (@lem1331156)). Qed.
Lemma lem1331185 (x : hreal) (y : hreal) (z : hreal) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1330723 x y z) (@lem1330722 x y z)). Qed.
Lemma lem1331186 (p2 : hreal) (p2'' : hreal) (p1' : hreal) : (term1 p2 p2'' p1') = (term0 p2 p2'' p1').
Proof. exact (@lem1331185 p2 p2'' p1'). Qed.
Lemma lem1331187 : hreal_le = hreal_le.
Proof. exact (eq_refl hreal_le). Qed.
Lemma lem1331188 (p2 : hreal) (p2'' : hreal) (p1' : hreal) : (term144 p2 p2'' p1') = (term143 p2 p2'' p1').
Proof. exact (MK_COMB (@lem1331187) (@lem1331186 p2 p2'' p1')). Qed.
Lemma lem1331190 (x : hreal) (y : hreal) (z : hreal) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1330723 x y z) (@lem1330722 x y z)). Qed.
Lemma lem1331191 (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term1 p2 p2' p1'') = (term0 p2 p2' p1'').
Proof. exact (@lem1331190 p2 p2' p1''). Qed.
Lemma lem1331192 (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term145 p2'' p1' p2 p2' p1'') = (term157 p2'' p1' p2 p2' p1'').
Proof. exact (MK_COMB (@lem1331188 p2 p2'' p1') (@lem1331191 p2 p2' p1'')). Qed.
Lemma lem1331194 (m : hreal) (n : hreal) (p : hreal) : (term19 n m p) = (hreal_le n p).
Proof. exact (EQ_MP (@lem1330714 m n p) (@lem1330713 m n p)). Qed.
Lemma lem1331195 (p2 : hreal) (p2'' : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term157 p2'' p1' p2 p2' p1'') = (term43 p2'' p1' p2' p1'').
Proof. exact (@lem1331194 p2 (hreal_add p2'' p1') (hreal_add p2' p1'')). Qed.
Lemma lem1331198 (p2 : hreal) (p2'' : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term145 p2'' p1' p2 p2' p1'') = (term43 p2'' p1' p2' p1'').
Proof. exact (TRANS (@lem1331192 p2'' p1' p2 p2' p1'') (@lem1331195 p2 p2'' p1' p2' p1'')). Qed.
Lemma lem1331199 (p2'' : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term102 p2'' p1' p2' p1'') = (term102 p2'' p1' p2' p1'').
Proof. exact (eq_refl (term102 p2'' p1' p2' p1'')). Qed.
Lemma lem1331200 (p2 : hreal) (p2'' : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term146 p2'' p1' p2 p2' p1'') = (term158 p2'' p1' p2' p1'').
Proof. exact (MK_COMB (@lem1331199 p2'' p1' p2' p1'') (@lem1331198 p2 p2'' p1' p2' p1'')). Qed.
Lemma lem1331202 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1331203 (p2'' : hreal) (p1' : hreal) (p2' : hreal) (p1'' : hreal) : (term158 p2'' p1' p2' p1'') = True.
Proof. exact (@lem1331202 (term43 p2'' p1' p2' p1'')). Qed.
Lemma lem1331204 (p2'' : hreal) (p1' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term146 p2'' p1' p2 p2' p1'') = True.
Proof. exact (TRANS (@lem1331200 p2 p2'' p1' p2' p1'') (@lem1331203 p2'' p1' p2' p1'')). Qed.
Lemma lem1331205 (p1' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term147 p1' p2 p2' p1'') = term159.
Proof. exact (fun_ext (fun p2'' : hreal => @lem1331204 p2'' p1' p2 p2' p1'')). Qed.
Lemma lem1331206 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331207 (p1' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term148 p1' p2 p2' p1'') = term160.
Proof. exact (MK_COMB (@lem1331206) (@lem1331205 p1' p2 p2' p1'')). Qed.
Lemma lem1331209 {A : Type'} (t : Prop) : (term140 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1331210 (t : Prop) : (term141 t) = t.
Proof. exact (@lem1331209 hreal t). Qed.
Lemma lem1331211 : term160 = True.
Proof. exact (@lem1331210 True). Qed.
Lemma lem1331212 (p1' : hreal) (p2 : hreal) (p2' : hreal) (p1'' : hreal) : (term148 p1' p2 p2' p1'') = True.
Proof. exact (TRANS (@lem1331207 p1' p2 p2' p1'') (@lem1331211)). Qed.
Lemma lem1331213 (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term149 p1' p2 p2') = term159.
Proof. exact (fun_ext (fun p1'' : hreal => @lem1331212 p1' p2 p2' p1'')). Qed.
Lemma lem1331214 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331215 (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term150 p1' p2 p2') = term160.
Proof. exact (MK_COMB (@lem1331214) (@lem1331213 p1' p2 p2')). Qed.
Lemma lem1331217 {A : Type'} (t : Prop) : (term140 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1331218 (t : Prop) : (term141 t) = t.
Proof. exact (@lem1331217 hreal t). Qed.
Lemma lem1331219 : term160 = True.
Proof. exact (@lem1331218 True). Qed.
Lemma lem1331220 (p1' : hreal) (p2 : hreal) (p2' : hreal) : (term150 p1' p2 p2') = True.
Proof. exact (TRANS (@lem1331215 p1' p2 p2') (@lem1331219)). Qed.
Lemma lem1331221 (p1' : hreal) (p2 : hreal) : (term151 p1' p2) = term159.
Proof. exact (fun_ext (fun p2' : hreal => @lem1331220 p1' p2 p2')). Qed.
Lemma lem1331222 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331223 (p1' : hreal) (p2 : hreal) : (term152 p1' p2) = term160.
Proof. exact (MK_COMB (@lem1331222) (@lem1331221 p1' p2)). Qed.
Lemma lem1331225 {A : Type'} (t : Prop) : (term140 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1331226 (t : Prop) : (term141 t) = t.
Proof. exact (@lem1331225 hreal t). Qed.
Lemma lem1331227 : term160 = True.
Proof. exact (@lem1331226 True). Qed.
Lemma lem1331228 (p1' : hreal) (p2 : hreal) : (term152 p1' p2) = True.
Proof. exact (TRANS (@lem1331223 p1' p2) (@lem1331227)). Qed.
Lemma lem1331229 (p2 : hreal) : (term153 p2) = term159.
Proof. exact (fun_ext (fun p1' : hreal => @lem1331228 p1' p2)). Qed.
Lemma lem1331230 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331231 (p2 : hreal) : (term154 p2) = term160.
Proof. exact (MK_COMB (@lem1331230) (@lem1331229 p2)). Qed.
Lemma lem1331233 {A : Type'} (t : Prop) : (term140 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1331234 (t : Prop) : (term141 t) = t.
Proof. exact (@lem1331233 hreal t). Qed.
Lemma lem1331235 : term160 = True.
Proof. exact (@lem1331234 True). Qed.
Lemma lem1331236 (p2 : hreal) : (term154 p2) = True.
Proof. exact (TRANS (@lem1331231 p2) (@lem1331235)). Qed.
Lemma lem1331237 : term155 = term159.
Proof. exact (fun_ext (fun p2 : hreal => @lem1331236 p2)). Qed.
Lemma lem1331238 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331239 : term156 = term160.
Proof. exact (MK_COMB (@lem1331238) (@lem1331237)). Qed.
Lemma lem1331241 {A : Type'} (t : Prop) : (term140 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1331242 (t : Prop) : (term141 t) = t.
Proof. exact (@lem1331241 hreal t). Qed.
Lemma lem1331243 : term160 = True.
Proof. exact (@lem1331242 True). Qed.
Lemma lem1331244 : term156 = True.
Proof. exact (TRANS (@lem1331239) (@lem1331243)). Qed.
Lemma lem1331245 : True = term156.
Proof. exact (SYM (@lem1331244)). Qed.
Lemma lem1331246 : term156.
Proof. exact (EQ_MP (@lem1331245) (@lem0)). Qed.
Lemma lem1331247 : term137.
Proof. exact (EQ_MP (@lem1331157) (@lem1331246)). Qed.
Lemma lem1331248 : term120.
Proof. exact (EQ_MP (@lem1331098) (@lem1331247)). Qed.
Lemma lem1331249 : term55.
Proof. exact (EQ_MP (@lem1330979) (@lem1331248)). Qed.
