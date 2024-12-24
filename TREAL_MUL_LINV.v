Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_MUL_LINV_term_abbrevs.
Require Import COND_CLAUSES_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import HREAL_ADD_RID_spec.
Require Import HREAL_MUL_LZERO_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1319496_spec.
Require Import thm1319802_spec.
Require Import thm1320004_spec.
Require Import thm1320277_spec.
Require Import thm1321091_spec.
Require Import thm1321192_spec.
Require Import thm13473_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Require Import thm9396_spec.
Require Import treal_eq_spec.
Require Import treal_inv_spec.
Require Import treal_mul_spec.
Require Import treal_of_num_spec.
Lemma lem1331750 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1331751 (x : hreal) (h1 : term0) : term1 x.
Proof. exact (@lem1331750 h1 x). Qed.
Lemma lem1331752 (x : hreal) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1331753 (x : hreal) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1331752 x) (@lem1331751 x h1)). Qed.
Lemma lem1331754 (x : hreal) (h1 : term3 x) : term3 x.
Proof. exact (h1). Qed.
Lemma lem1331755 (x : hreal) (h1 : term0) (h2 : term3 x) : (term4 x) = term5.
Proof. exact (@lem1331753 x h1 (@lem1331754 x h2)). Qed.
Lemma lem1331756 (x : hreal) (h1 : term3 x) : term6 x.
Proof. exact (fun h0 : term0 => @lem1331755 x h0 h1). Qed.
Lemma lem1331757 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1331758 (x : hreal) (h1 : term0) (h2 : term3 x) : (term4 x) = term5.
Proof. exact (@lem1331756 x h2 (@lem1331757 h1)). Qed.
Lemma lem1331759 (x : hreal) (h1 : term0) : term2 x.
Proof. exact (fun h0 : term3 x => @lem1331758 x h1 h0). Qed.
Lemma lem1331760 (h1 : term0) : term0.
Proof. exact (fun x : hreal => @lem1331759 x h1). Qed.
Lemma lem1331761 : term7.
Proof. exact (fun h0 : term0 => @lem1331760 h0). Qed.
Lemma lem1331762 : term0.
Proof. exact (@lem1331761 (@lem1321192)). Qed.
Lemma lem1331763 (x : hreal) : term1 x.
Proof. exact (@lem1331762 x). Qed.
Lemma lem1331764 (x : hreal) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1331766 (x : hreal) : term8 x.
Proof. exact (@lem1320004 x). Qed.
Lemma lem1331767 (x : hreal) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1331768 (x : hreal) : term9 x.
Proof. exact (EQ_MP (@lem1331767 x) (@lem1331766 x)). Qed.
Lemma lem1331769 (x : hreal) (y : hreal) : term10 x y.
Proof. exact (@lem1331768 x y). Qed.
Lemma lem1331770 (y : hreal) (x : hreal) : (term10 x y) = ((hreal_add x y) = (hreal_add y x)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1331772 (x : hreal) : term11 x.
Proof. exact (@lem1321091 x). Qed.
Lemma lem1331773 (x : hreal) : (term11 x) = (term12 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1331774 (x : hreal) : term12 x.
Proof. exact (EQ_MP (@lem1331773 x) (@lem1331772 x)). Qed.
Lemma lem1331775 (x : hreal) (y : hreal) : term13 x y.
Proof. exact (@lem1331774 x y). Qed.
Lemma lem1331776 (y : hreal) (x : hreal) : (term13 x y) = (term14 y x).
Proof. exact (eq_refl (term13 x y)). Qed.
Lemma lem1331777 (y : hreal) (x : hreal) : term14 y x.
Proof. exact (EQ_MP (@lem1331776 y x) (@lem1331775 x y)). Qed.
Lemma lem1331778 (y : hreal) (x : hreal) (z : hreal) : term15 y x z.
Proof. exact (@lem1331777 y x z). Qed.
Lemma lem1331779 (y : hreal) (x : hreal) (z : hreal) : (term15 y x z) = ((term16 x y z) = (term17 y x z)).
Proof. exact (eq_refl (term15 y x z)). Qed.
Lemma lem1331781 (x : hreal) : term18 x.
Proof. exact (@lem1319802 x). Qed.
Lemma lem1331782 (x : hreal) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1331783 (x : hreal) : term19 x.
Proof. exact (EQ_MP (@lem1331782 x) (@lem1331781 x)). Qed.
Lemma lem1331784 (x : hreal) (y : hreal) : term20 x y.
Proof. exact (@lem1331783 x y). Qed.
Lemma lem1331785 (y : hreal) (x : hreal) : (term20 x y) = (term21 y x).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1331787 (x : hreal) : term22 x.
Proof. exact (@lem1319496 x). Qed.
Lemma lem1331788 (x : hreal) : (term22 x) = (term23 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1331789 (x : hreal) : term23 x.
Proof. exact (EQ_MP (@lem1331788 x) (@lem1331787 x)). Qed.
Lemma lem1331790 (x : hreal) (y : hreal) : term24 x y.
Proof. exact (@lem1331789 x y). Qed.
Lemma lem1331791 (y : hreal) (x : hreal) : (term24 x y) = (term25 y x).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1331792 (y : hreal) (x : hreal) : term25 y x.
Proof. exact (EQ_MP (@lem1331791 y x) (@lem1331790 x y)). Qed.
Lemma lem1331793 (x : hreal) (y : hreal) (h1 : hreal_le x y) : hreal_le x y.
Proof. exact (h1). Qed.
Lemma lem1331794 (y : hreal) (x : hreal) (h1 : hreal_le y x) : hreal_le y x.
Proof. exact (h1). Qed.
Lemma lem1331798 (m : hreal) : term26 m.
Proof. exact (@lem1321875 m). Qed.
Lemma lem1331799 (m : hreal) : (term26 m) = ((term27 m) = term28).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem1331801 (n : hreal) : term29 n.
Proof. exact (@lem1321694 n). Qed.
Lemma lem1331802 (n : hreal) : (term29 n) = ((term30 n) = n).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem1331804 (x : hreal) : term31 x.
Proof. exact (@lem1320277 x). Qed.
Lemma lem1331805 (x : hreal) : (term31 x) = ((term32 x) = x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1331807 (x1 : hreal) : term33 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1331808 (x1 : hreal) : (term33 x1) = (term34 x1).
Proof. exact (eq_refl (term33 x1)). Qed.
Lemma lem1331809 (x1 : hreal) : term34 x1.
Proof. exact (EQ_MP (@lem1331808 x1) (@lem1331807 x1)). Qed.
Lemma lem1331810 (x1 : hreal) (y2 : hreal) : term35 x1 y2.
Proof. exact (@lem1331809 x1 y2). Qed.
Lemma lem1331811 (x1 : hreal) (y2 : hreal) : (term35 x1 y2) = (term36 x1 y2).
Proof. exact (eq_refl (term35 x1 y2)). Qed.
Lemma lem1331812 (x1 : hreal) (y2 : hreal) : term36 x1 y2.
Proof. exact (EQ_MP (@lem1331811 x1 y2) (@lem1331810 x1 y2)). Qed.
Lemma lem1331813 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term37 x1 y2 x2.
Proof. exact (@lem1331812 x1 y2 x2). Qed.
Lemma lem1331814 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term37 x1 y2 x2) = (term38 x1 y2 x2).
Proof. exact (eq_refl (term37 x1 y2 x2)). Qed.
Lemma lem1331815 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term38 x1 y2 x2.
Proof. exact (EQ_MP (@lem1331814 x1 y2 x2) (@lem1331813 x1 y2 x2)). Qed.
Lemma lem1331816 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term39 x1 y2 x2 y1.
Proof. exact (@lem1331815 x1 y2 x2 y1). Qed.
Lemma lem1331817 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term39 x1 y2 x2 y1) = ((term40 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term39 x1 y2 x2 y1)). Qed.
Lemma lem1331819 (x1 : hreal) : term41 x1.
Proof. exact (@lem1324372 x1). Qed.
Lemma lem1331820 (x1 : hreal) : (term41 x1) = (term42 x1).
Proof. exact (eq_refl (term41 x1)). Qed.
Lemma lem1331821 (x1 : hreal) : term42 x1.
Proof. exact (EQ_MP (@lem1331820 x1) (@lem1331819 x1)). Qed.
Lemma lem1331822 (x1 : hreal) (y2 : hreal) : term43 x1 y2.
Proof. exact (@lem1331821 x1 y2). Qed.
Lemma lem1331823 (x1 : hreal) (y2 : hreal) : (term43 x1 y2) = (term44 x1 y2).
Proof. exact (eq_refl (term43 x1 y2)). Qed.
Lemma lem1331824 (x1 : hreal) (y2 : hreal) : term44 x1 y2.
Proof. exact (EQ_MP (@lem1331823 x1 y2) (@lem1331822 x1 y2)). Qed.
Lemma lem1331825 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term45 x1 y2 y1.
Proof. exact (@lem1331824 x1 y2 y1). Qed.
Lemma lem1331826 (x1 : hreal) (y2 : hreal) (y1 : hreal) : (term45 x1 y2 y1) = (term46 x1 y2 y1).
Proof. exact (eq_refl (term45 x1 y2 y1)). Qed.
Lemma lem1331827 (x1 : hreal) (y2 : hreal) (y1 : hreal) : term46 x1 y2 y1.
Proof. exact (EQ_MP (@lem1331826 x1 y2 y1) (@lem1331825 x1 y2 y1)). Qed.
Lemma lem1331828 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : term47 x1 y2 y1 x2.
Proof. exact (@lem1331827 x1 y2 y1 x2). Qed.
Lemma lem1331829 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term47 x1 y2 y1 x2) = ((term48 x1 y1 x2 y2) = (term49 x1 y2 y1 x2)).
Proof. exact (eq_refl (term47 x1 y2 y1 x2)). Qed.
Lemma lem1331831 (n : hreal) : term29 n.
Proof. exact (@lem1321694 n). Qed.
Lemma lem1331832 (n : hreal) : (term29 n) = ((term30 n) = n).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem1331834 (x : hreal) : term31 x.
Proof. exact (@lem1320277 x). Qed.
Lemma lem1331835 (x : hreal) : (term31 x) = ((term32 x) = x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem1331837 (y : hreal) : term50 y.
Proof. exact (@lem1325510 y). Qed.
Lemma lem1331838 (y : hreal) : (term50 y) = (term51 y).
Proof. exact (eq_refl (term50 y)). Qed.
Lemma lem1331839 (y : hreal) : term51 y.
Proof. exact (EQ_MP (@lem1331838 y) (@lem1331837 y)). Qed.
Lemma lem1331840 (y : hreal) (x : hreal) : term52 y x.
Proof. exact (@lem1331839 y x). Qed.
Lemma lem1331841 (y : hreal) (x : hreal) : (term52 y x) = ((term53 x y) = (term54 y x)).
Proof. exact (eq_refl (term52 y x)). Qed.
Lemma lem1331855 (n : nat) : term55 n.
Proof. exact (@lem1322742 n). Qed.
Lemma lem1331856 (n : nat) : (term55 n) = ((treal_of_num n) = (term56 n)).
Proof. exact (eq_refl (term55 n)). Qed.
Lemma lem1331858 (x1 : hreal) : term33 x1.
Proof. exact (@lem1326116 x1). Qed.
Lemma lem1331859 (x1 : hreal) : (term33 x1) = (term34 x1).
Proof. exact (eq_refl (term33 x1)). Qed.
Lemma lem1331860 (x1 : hreal) : term34 x1.
Proof. exact (EQ_MP (@lem1331859 x1) (@lem1331858 x1)). Qed.
Lemma lem1331861 (x1 : hreal) (y2 : hreal) : term35 x1 y2.
Proof. exact (@lem1331860 x1 y2). Qed.
Lemma lem1331862 (x1 : hreal) (y2 : hreal) : (term35 x1 y2) = (term36 x1 y2).
Proof. exact (eq_refl (term35 x1 y2)). Qed.
Lemma lem1331863 (x1 : hreal) (y2 : hreal) : term36 x1 y2.
Proof. exact (EQ_MP (@lem1331862 x1 y2) (@lem1331861 x1 y2)). Qed.
Lemma lem1331864 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term37 x1 y2 x2.
Proof. exact (@lem1331863 x1 y2 x2). Qed.
Lemma lem1331865 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term37 x1 y2 x2) = (term38 x1 y2 x2).
Proof. exact (eq_refl (term37 x1 y2 x2)). Qed.
Lemma lem1331866 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term38 x1 y2 x2.
Proof. exact (EQ_MP (@lem1331865 x1 y2 x2) (@lem1331864 x1 y2 x2)). Qed.
Lemma lem1331867 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term39 x1 y2 x2 y1.
Proof. exact (@lem1331866 x1 y2 x2 y1). Qed.
Lemma lem1331868 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term39 x1 y2 x2 y1) = ((term40 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1))).
Proof. exact (eq_refl (term39 x1 y2 x2 y1)). Qed.
Lemma lem1331870 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term57 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1331871 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term57 _5106 _5107 P) = ((term58 _5106 _5107 P) = (term59 _5106 _5107 P)).
Proof. exact (eq_refl (term57 _5106 _5107 P)). Qed.
Lemma lem1331878 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term58 _5106 _5107 P) = (term59 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1331871 _5106 _5107 P) (@lem1331870 _5106 _5107 P)). Qed.
Lemma lem1331879 (P : type1233) : (term60 P) = (term61 P).
Proof. exact (@lem1331878 hreal hreal P). Qed.
Lemma lem1331880 : term62 = term63.
Proof. exact (@lem1331879 term64). Qed.
Lemma lem1331881 (x : prod hreal hreal) : (term65 x) = (term66 x).
Proof. exact (eq_refl (term65 x)). Qed.
Lemma lem1331882 : term67 = term64.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1331881 x)). Qed.
Lemma lem1331883 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1331884 : term62 = term68.
Proof. exact (MK_COMB (@lem1331883) (@lem1331882)). Qed.
Lemma lem1331885 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1331886 : term69 = term70.
Proof. exact (MK_COMB (@lem1331885) (@lem1331884)). Qed.
Lemma lem1331887 (p1 : hreal) (p2 : hreal) : (term71 p1 p2) = (term72 p1 p2).
Proof. exact (eq_refl (term71 p1 p2)). Qed.
Lemma lem1331888 (p1 : hreal) : (term73 p1) = (term74 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1331887 p1 p2)). Qed.
Lemma lem1331889 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331890 (p1 : hreal) : (term75 p1) = (term76 p1).
Proof. exact (MK_COMB (@lem1331889) (@lem1331888 p1)). Qed.
Lemma lem1331891 : term77 = term78.
Proof. exact (fun_ext (fun p1 : hreal => @lem1331890 p1)). Qed.
Lemma lem1331892 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1331893 : term63 = term79.
Proof. exact (MK_COMB (@lem1331892) (@lem1331891)). Qed.
Lemma lem1331894 : (term62 = term63) = (term68 = term79).
Proof. exact (MK_COMB (@lem1331886) (@lem1331893)). Qed.
Lemma lem1331895 : term68 = term79.
Proof. exact (EQ_MP (@lem1331894) (@lem1331880)). Qed.
Lemma lem1331910 : term79 = term68.
Proof. exact (SYM (@lem1331895)). Qed.
Lemma lem1331912 (n : nat) : (treal_of_num n) = (term56 n).
Proof. exact (EQ_MP (@lem1331856 n) (@lem1331855 n)). Qed.
Lemma lem1331913 : term80 = term81.
Proof. exact (@lem1331912 (NUMERAL 0)). Qed.
Lemma lem1331914 (x : hreal) (y : hreal) : (term82 x y) = (term82 x y).
Proof. exact (eq_refl (term82 x y)). Qed.
Lemma lem1331915 (x : hreal) (y : hreal) : (term83 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1331914 x y) (@lem1331913)). Qed.
Lemma lem1331917 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term40 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1331868 x1 y2 x2 y1) (@lem1331867 x1 y2 x2 y1)). Qed.
Lemma lem1331918 (x : hreal) (y : hreal) : (term84 x y) = ((term30 x) = (term32 y)).
Proof. exact (@lem1331917 x term28 term28 y). Qed.
Lemma lem1331919 (x : hreal) (y : hreal) : (term83 x y) = ((term30 x) = (term32 y)).
Proof. exact (TRANS (@lem1331915 x y) (@lem1331918 x y)). Qed.
Lemma lem1331920 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1331921 (x : hreal) (y : hreal) : (term85 x y) = (term86 x y).
Proof. exact (MK_COMB (@lem1331920) (@lem1331919 x y)). Qed.
Lemma lem1331922 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1331923 (x : hreal) (y : hreal) : (term87 x y) = (term88 x y).
Proof. exact (MK_COMB (@lem1331922) (@lem1331921 x y)). Qed.
Lemma lem1331925 (y : hreal) (x : hreal) : (term53 x y) = (term54 y x).
Proof. exact (EQ_MP (@lem1331841 y x) (@lem1331840 y x)). Qed.
Lemma lem1331926 : treal_mul = treal_mul.
Proof. exact (eq_refl treal_mul). Qed.
Lemma lem1331927 (y : hreal) (x : hreal) : (term89 x y) = (term90 y x).
Proof. exact (MK_COMB (@lem1331926) (@lem1331925 y x)). Qed.
Lemma lem1331928 (x : hreal) (y : hreal) : (@pair hreal hreal x y) = (@pair hreal hreal x y).
Proof. exact (eq_refl (@pair hreal hreal x y)). Qed.
Lemma lem1331929 (x : hreal) (y : hreal) : (term91 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem1331927 y x) (@lem1331928 x y)). Qed.
Lemma lem1331930 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1331931 (x : hreal) (y : hreal) : (term93 x y) = (term94 x y).
Proof. exact (MK_COMB (@lem1331930) (@lem1331929 x y)). Qed.
Lemma lem1331933 (n : nat) : (treal_of_num n) = (term56 n).
Proof. exact (EQ_MP (@lem1331856 n) (@lem1331855 n)). Qed.
Lemma lem1331934 : term95 = term96.
Proof. exact (@lem1331933 term97). Qed.
Lemma lem1331935 (x : hreal) (y : hreal) : (term98 x y) = (term99 x y).
Proof. exact (MK_COMB (@lem1331931 x y) (@lem1331934)). Qed.
Lemma lem1331936 (x : hreal) (y : hreal) : (term72 x y) = (term100 x y).
Proof. exact (MK_COMB (@lem1331923 x y) (@lem1331935 x y)). Qed.
Lemma lem1331937 (x : hreal) (y : hreal) : (term100 x y) = (term72 x y).
Proof. exact (SYM (@lem1331936 x y)). Qed.
Lemma lem1331939 (n : hreal) : (term30 n) = n.
Proof. exact (EQ_MP (@lem1331832 n) (@lem1331831 n)). Qed.
Lemma lem1331940 (x : hreal) : (term30 x) = x.
Proof. exact (@lem1331939 x). Qed.
Lemma lem1331941 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1331942 (x : hreal) : (term101 x) = (@eq hreal x).
Proof. exact (MK_COMB (@lem1331941) (@lem1331940 x)). Qed.
Lemma lem1331944 (x : hreal) : (term32 x) = x.
Proof. exact (EQ_MP (@lem1331835 x) (@lem1331834 x)). Qed.
Lemma lem1331945 (y : hreal) : (term32 y) = y.
Proof. exact (@lem1331944 y). Qed.
Lemma lem1331946 (x : hreal) (y : hreal) : ((term30 x) = (term32 y)) = (x = y).
Proof. exact (MK_COMB (@lem1331942 x) (@lem1331945 y)). Qed.
Lemma lem1331947 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1331948 (x : hreal) (y : hreal) : (term86 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1331947) (@lem1331946 x y)). Qed.
Lemma lem1331949 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1331950 (x : hreal) (y : hreal) : (term88 x y) = (term103 x y).
Proof. exact (MK_COMB (@lem1331949) (@lem1331948 x y)). Qed.
Lemma lem1331951 (x : hreal) (y : hreal) : (term99 x y) = (term99 x y).
Proof. exact (eq_refl (term99 x y)). Qed.
Lemma lem1331952 (x : hreal) (y : hreal) : (term100 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1331950 x y) (@lem1331951 x y)). Qed.
Lemma lem1331953 (x : hreal) (y : hreal) : (term104 x y) = (term100 x y).
Proof. exact (SYM (@lem1331952 x y)). Qed.
Lemma lem1331954 (x : hreal) (y : hreal) (h1 : term102 x y) : term102 x y.
Proof. exact (h1). Qed.
Lemma lem1331955 {A : Type'} (t1 : A) : term105 A t1.
Proof. exact (@lem12647 A t1). Qed.
Lemma lem1331956 {A : Type'} (t1 : A) : (term105 A t1) = (term106 A t1).
Proof. exact (eq_refl (term105 A t1)). Qed.
Lemma lem1331957 {A : Type'} (t1 : A) : term106 A t1.
Proof. exact (EQ_MP (@lem1331956 A t1) (@lem1331955 A t1)). Qed.
Lemma lem1331958 {A : Type'} (t1 : A) (t2 : A) : term107 A t1 t2.
Proof. exact (@lem1331957 A t1 t2). Qed.
Lemma lem1331959 {A : Type'} (t1 : A) (t2 : A) : (term107 A t1 t2) = (term108 A t1 t2).
Proof. exact (eq_refl (term107 A t1 t2)). Qed.
Lemma lem1331960 {A : Type'} (t1 : A) (t2 : A) : term108 A t1 t2.
Proof. exact (EQ_MP (@lem1331959 A t1 t2) (@lem1331958 A t1 t2)). Qed.
Lemma lem1331963 (x : hreal) (y : hreal) : term109 x y.
Proof. exact (@lem82 (x = y)). Qed.
Lemma lem1331977 (x : hreal) (y : hreal) (h1 : term102 x y) : (x = y) = False.
Proof. exact (@lem1331963 x y (@lem1331954 x y h1)). Qed.
Lemma lem1331978 : (@COND (prod hreal hreal)) = (@COND (prod hreal hreal)).
Proof. exact (eq_refl (@COND (prod hreal hreal))). Qed.
Lemma lem1331979 (x : hreal) (y : hreal) (h1 : term102 x y) : (term110 x y) = (@COND (prod hreal hreal) False).
Proof. exact (MK_COMB (@lem1331978) (@lem1331977 x y h1)). Qed.
Lemma lem1331980 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem1331981 (x : hreal) (y : hreal) (h1 : term102 x y) : (term111 x y) = term112.
Proof. exact (MK_COMB (@lem1331979 x y h1) (@lem1331980)). Qed.
Lemma lem1331982 (y : hreal) (x : hreal) : (term113 y x) = (term113 y x).
Proof. exact (eq_refl (term113 y x)). Qed.
Lemma lem1331983 (x : hreal) (y : hreal) (h1 : term102 x y) : (term54 y x) = (term114 y x).
Proof. exact (MK_COMB (@lem1331981 x y h1) (@lem1331982 y x)). Qed.
Lemma lem1331985 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem1331960 A t1 t2)). Qed.
Lemma lem1331986 (t1 : prod hreal hreal) (t2 : prod hreal hreal) : (@COND (prod hreal hreal) False t1 t2) = t2.
Proof. exact (@lem1331985 (prod hreal hreal) t1 t2). Qed.
Lemma lem1331987 (y : hreal) (x : hreal) : (term114 y x) = (term113 y x).
Proof. exact (@lem1331986 term81 (term113 y x)). Qed.
Lemma lem1331988 (x : hreal) (y : hreal) (h1 : term102 x y) : (term54 y x) = (term113 y x).
Proof. exact (TRANS (@lem1331983 x y h1) (@lem1331987 y x)). Qed.
Lemma lem1331989 : treal_mul = treal_mul.
Proof. exact (eq_refl treal_mul). Qed.
Lemma lem1331990 (x : hreal) (y : hreal) (h1 : term102 x y) : (term90 y x) = (term115 y x).
Proof. exact (MK_COMB (@lem1331989) (@lem1331988 x y h1)). Qed.
Lemma lem1331991 (x : hreal) (y : hreal) : (@pair hreal hreal x y) = (@pair hreal hreal x y).
Proof. exact (eq_refl (@pair hreal hreal x y)). Qed.
Lemma lem1331992 (x : hreal) (y : hreal) (h1 : term102 x y) : (term92 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1331990 x y h1) (@lem1331991 x y)). Qed.
Lemma lem1331993 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1331994 (x : hreal) (y : hreal) (h1 : term102 x y) : (term94 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem1331993) (@lem1331992 x y h1)). Qed.
Lemma lem1331995 : term96 = term96.
Proof. exact (eq_refl term96). Qed.
Lemma lem1331996 (x : hreal) (y : hreal) (h1 : term102 x y) : (term99 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem1331994 x y h1) (@lem1331995)). Qed.
Lemma lem1331997 (x : hreal) (y : hreal) (h1 : term102 x y) : (term118 x y) = (term99 x y).
Proof. exact (SYM (@lem1331996 x y h1)). Qed.
Lemma lem1331998 (_474 : prod hreal hreal) (_475 : Prop) (_476 : type1233) (_477 : prod hreal hreal) : (term119 _476 _475 _474 _477) = (term120 _474 _475 _476 _477).
Proof. exact (@lem13473 (prod hreal hreal) _474 _475 _476 _477). Qed.
Lemma lem1331999 (_474 : prod hreal hreal) (_475 : Prop) (x : hreal) (y : hreal) (_477 : prod hreal hreal) : (term121 x y _475 _474 _477) = (term122 _474 _475 x y _477).
Proof. exact (@lem1331998 _474 _475 (term123 x y) _477). Qed.
Lemma lem1332000 (y : hreal) (x : hreal) : (term124 y x) = (term125 y x).
Proof. exact (@lem1331999 (term126 x y) (hreal_le y x) x y (term127 y x)). Qed.
Lemma lem1332001 (x : hreal) (y : hreal) : (term128 y x) = (term129 x y).
Proof. exact (eq_refl (term128 y x)). Qed.
Lemma lem1332002 (y : hreal) (x : hreal) : (term130 y x) = (term130 y x).
Proof. exact (eq_refl (term130 y x)). Qed.
Lemma lem1332003 (x : hreal) (y : hreal) : (term131 y x) = (term132 x y).
Proof. exact (MK_COMB (@lem1332002 y x) (@lem1332001 x y)). Qed.
Lemma lem1332004 (x : hreal) (y : hreal) : (term133 x y) = (term134 x y).
Proof. exact (eq_refl (term133 x y)). Qed.
Lemma lem1332005 (y : hreal) (x : hreal) : (term135 y x) = (term135 y x).
Proof. exact (eq_refl (term135 y x)). Qed.
Lemma lem1332006 (x : hreal) (y : hreal) : (term136 x y) = (term137 x y).
Proof. exact (MK_COMB (@lem1332005 y x) (@lem1332004 x y)). Qed.
Lemma lem1332007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1332008 (x : hreal) (y : hreal) : (term138 x y) = (term139 x y).
Proof. exact (MK_COMB (@lem1332007) (@lem1332006 x y)). Qed.
Lemma lem1332009 (x : hreal) (y : hreal) : (term125 y x) = (term140 x y).
Proof. exact (MK_COMB (@lem1332008 x y) (@lem1332003 x y)). Qed.
Lemma lem1332010 (x : hreal) (y : hreal) : (term124 y x) = (term118 x y).
Proof. exact (eq_refl (term124 y x)). Qed.
Lemma lem1332011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1332012 (x : hreal) (y : hreal) : (term141 y x) = (term142 x y).
Proof. exact (MK_COMB (@lem1332011) (@lem1332010 x y)). Qed.
Lemma lem1332013 (x : hreal) (y : hreal) : ((term124 y x) = (term125 y x)) = ((term118 x y) = (term140 x y)).
Proof. exact (MK_COMB (@lem1332012 x y) (@lem1332009 x y)). Qed.
Lemma lem1332014 (x : hreal) (y : hreal) : (term118 x y) = (term140 x y).
Proof. exact (EQ_MP (@lem1332013 x y) (@lem1332000 y x)). Qed.
Lemma lem1332015 (x : hreal) (y : hreal) : (term140 x y) = (term118 x y).
Proof. exact (SYM (@lem1332014 x y)). Qed.
Lemma lem1332016 (y : hreal) (x : hreal) (h1 : hreal_le y x) : hreal_le y x.
Proof. exact (h1). Qed.
Lemma lem1332033 (y : hreal) (x : hreal) (h1 : term143 y x) : term143 y x.
Proof. exact (h1). Qed.
Lemma lem1332051 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term48 x1 y1 x2 y2) = (term49 x1 y2 y1 x2).
Proof. exact (EQ_MP (@lem1331829 x1 y2 y1 x2) (@lem1331828 x1 y2 y1 x2)). Qed.
Lemma lem1332052 (y : hreal) (x : hreal) : (term144 x y) = (term145 y x).
Proof. exact (@lem1332051 (term146 x y) y term28 x). Qed.
Lemma lem1332053 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1332054 (y : hreal) (x : hreal) : (term147 x y) = (term148 y x).
Proof. exact (MK_COMB (@lem1332053) (@lem1332052 y x)). Qed.
Lemma lem1332055 : term96 = term96.
Proof. exact (eq_refl term96). Qed.
Lemma lem1332056 (y : hreal) (x : hreal) : (term134 x y) = (term149 y x).
Proof. exact (MK_COMB (@lem1332054 y x) (@lem1332055)). Qed.
Lemma lem1332058 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term40 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1331817 x1 y2 x2 y1) (@lem1331816 x1 y2 x2 y1)). Qed.
Lemma lem1332059 (y : hreal) (x : hreal) : (term149 y x) = ((term150 x y) = (term151 y x)).
Proof. exact (@lem1332058 (term152 x y) term28 term5 (term153 y x)). Qed.
Lemma lem1332060 (y : hreal) (x : hreal) : (term134 x y) = ((term150 x y) = (term151 y x)).
Proof. exact (TRANS (@lem1332056 y x) (@lem1332059 y x)). Qed.
Lemma lem1332061 (x : hreal) (y : hreal) : ((term150 x y) = (term151 y x)) = (term134 x y).
Proof. exact (SYM (@lem1332060 y x)). Qed.
Lemma lem1332063 (x1 : hreal) (y2 : hreal) (y1 : hreal) (x2 : hreal) : (term48 x1 y1 x2 y2) = (term49 x1 y2 y1 x2).
Proof. exact (EQ_MP (@lem1331829 x1 y2 y1 x2) (@lem1331828 x1 y2 y1 x2)). Qed.
Lemma lem1332064 (y : hreal) (x : hreal) : (term154 x y) = (term155 y x).
Proof. exact (@lem1332063 term28 y (term146 y x) x). Qed.
Lemma lem1332065 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1332066 (y : hreal) (x : hreal) : (term156 x y) = (term157 y x).
Proof. exact (MK_COMB (@lem1332065) (@lem1332064 y x)). Qed.
Lemma lem1332067 : term96 = term96.
Proof. exact (eq_refl term96). Qed.
Lemma lem1332068 (y : hreal) (x : hreal) : (term129 x y) = (term158 y x).
Proof. exact (MK_COMB (@lem1332066 y x) (@lem1332067)). Qed.
Lemma lem1332070 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term40 x1 y1 x2 y2) = ((hreal_add x1 y2) = (hreal_add x2 y1)).
Proof. exact (EQ_MP (@lem1331817 x1 y2 x2 y1) (@lem1331816 x1 y2 x2 y1)). Qed.
Lemma lem1332071 (y : hreal) (x : hreal) : (term158 y x) = ((term159 x y) = (term160 y x)).
Proof. exact (@lem1332070 (term161 x y) term28 term5 (term162 y x)). Qed.
Lemma lem1332072 (y : hreal) (x : hreal) : (term129 x y) = ((term159 x y) = (term160 y x)).
Proof. exact (TRANS (@lem1332068 y x) (@lem1332071 y x)). Qed.
Lemma lem1332073 (x : hreal) (y : hreal) : ((term159 x y) = (term160 y x)) = (term129 x y).
Proof. exact (SYM (@lem1332072 y x)). Qed.
Lemma lem1332077 (n : hreal) : (term30 n) = n.
Proof. exact (EQ_MP (@lem1331802 n) (@lem1331801 n)). Qed.
Lemma lem1332078 (x : hreal) (y : hreal) : (term150 x y) = (term152 x y).
Proof. exact (@lem1332077 (term152 x y)). Qed.
Lemma lem1332084 (m : hreal) : (term27 m) = term28.
Proof. exact (EQ_MP (@lem1331799 m) (@lem1331798 m)). Qed.
Lemma lem1332085 (y : hreal) : (term27 y) = term28.
Proof. exact (@lem1332084 y). Qed.
Lemma lem1332086 (y : hreal) (x : hreal) : (term163 y x) = (term163 y x).
Proof. exact (eq_refl (term163 y x)). Qed.
Lemma lem1332087 (y : hreal) (x : hreal) : (term152 x y) = (term164 y x).
Proof. exact (MK_COMB (@lem1332086 y x) (@lem1332085 y)). Qed.
Lemma lem1332089 (n : hreal) : (term30 n) = n.
Proof. exact (EQ_MP (@lem1331802 n) (@lem1331801 n)). Qed.
Lemma lem1332090 (y : hreal) (x : hreal) : (term164 y x) = (term165 y x).
Proof. exact (@lem1332089 (term165 y x)). Qed.
Lemma lem1332095 (y : hreal) (x : hreal) : (term152 x y) = (term165 y x).
Proof. exact (TRANS (@lem1332087 y x) (@lem1332090 y x)). Qed.
Lemma lem1332096 (y : hreal) (x : hreal) : (term150 x y) = (term165 y x).
Proof. exact (TRANS (@lem1332078 x y) (@lem1332095 y x)). Qed.
Lemma lem1332097 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1332098 (y : hreal) (x : hreal) : (term166 x y) = (term167 y x).
Proof. exact (MK_COMB (@lem1332097) (@lem1332096 y x)). Qed.
Lemma lem1332104 (m : hreal) : (term27 m) = term28.
Proof. exact (EQ_MP (@lem1331799 m) (@lem1331798 m)). Qed.
Lemma lem1332105 (x : hreal) : (term27 x) = term28.
Proof. exact (@lem1332104 x). Qed.
Lemma lem1332106 (x : hreal) (y : hreal) : (term168 x y) = (term168 x y).
Proof. exact (eq_refl (term168 x y)). Qed.
Lemma lem1332107 (x : hreal) (y : hreal) : (term153 y x) = (term169 x y).
Proof. exact (MK_COMB (@lem1332106 x y) (@lem1332105 x)). Qed.
Lemma lem1332109 (n : hreal) : (term30 n) = n.
Proof. exact (EQ_MP (@lem1331802 n) (@lem1331801 n)). Qed.
Lemma lem1332110 (x : hreal) (y : hreal) : (term169 x y) = (term170 x y).
Proof. exact (@lem1332109 (term170 x y)). Qed.
Lemma lem1332115 (x : hreal) (y : hreal) : (term153 y x) = (term170 x y).
Proof. exact (TRANS (@lem1332107 x y) (@lem1332110 x y)). Qed.
Lemma lem1332116 : term171 = term171.
Proof. exact (eq_refl term171). Qed.
Lemma lem1332117 (x : hreal) (y : hreal) : (term151 y x) = (term172 x y).
Proof. exact (MK_COMB (@lem1332116) (@lem1332115 x y)). Qed.
Lemma lem1332118 (x : hreal) (y : hreal) : ((term150 x y) = (term151 y x)) = ((term165 y x) = (term172 x y)).
Proof. exact (MK_COMB (@lem1332098 y x) (@lem1332117 x y)). Qed.
Lemma lem1332121 (y : hreal) (x : hreal) : ((term165 y x) = (term172 x y)) = ((term150 x y) = (term151 y x)).
Proof. exact (SYM (@lem1332118 x y)). Qed.
Lemma lem1332125 (n : hreal) : (term30 n) = n.
Proof. exact (EQ_MP (@lem1331802 n) (@lem1331801 n)). Qed.
Lemma lem1332126 (x : hreal) (y : hreal) : (term159 x y) = (term161 x y).
Proof. exact (@lem1332125 (term161 x y)). Qed.
Lemma lem1332128 (m : hreal) : (term27 m) = term28.
Proof. exact (EQ_MP (@lem1331799 m) (@lem1331798 m)). Qed.
Lemma lem1332129 (x : hreal) : (term27 x) = term28.
Proof. exact (@lem1332128 x). Qed.
Lemma lem1332130 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1332131 (x : hreal) : (term173 x) = term174.
Proof. exact (MK_COMB (@lem1332130) (@lem1332129 x)). Qed.
Lemma lem1332136 (x : hreal) (y : hreal) : (term165 x y) = (term165 x y).
Proof. exact (eq_refl (term165 x y)). Qed.
Lemma lem1332137 (x : hreal) (y : hreal) : (term161 x y) = (term175 x y).
Proof. exact (MK_COMB (@lem1332131 x) (@lem1332136 x y)). Qed.
Lemma lem1332139 (x : hreal) : (term32 x) = x.
Proof. exact (EQ_MP (@lem1331805 x) (@lem1331804 x)). Qed.
Lemma lem1332140 (x : hreal) (y : hreal) : (term175 x y) = (term165 x y).
Proof. exact (@lem1332139 (term165 x y)). Qed.
Lemma lem1332145 (x : hreal) (y : hreal) : (term161 x y) = (term165 x y).
Proof. exact (TRANS (@lem1332137 x y) (@lem1332140 x y)). Qed.
Lemma lem1332146 (x : hreal) (y : hreal) : (term159 x y) = (term165 x y).
Proof. exact (TRANS (@lem1332126 x y) (@lem1332145 x y)). Qed.
Lemma lem1332147 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1332148 (x : hreal) (y : hreal) : (term176 x y) = (term167 x y).
Proof. exact (MK_COMB (@lem1332147) (@lem1332146 x y)). Qed.
Lemma lem1332150 (m : hreal) : (term27 m) = term28.
Proof. exact (EQ_MP (@lem1331799 m) (@lem1331798 m)). Qed.
Lemma lem1332151 (y : hreal) : (term27 y) = term28.
Proof. exact (@lem1332150 y). Qed.
Lemma lem1332152 : hreal_add = hreal_add.
Proof. exact (eq_refl hreal_add). Qed.
Lemma lem1332153 (y : hreal) : (term173 y) = term174.
Proof. exact (MK_COMB (@lem1332152) (@lem1332151 y)). Qed.
Lemma lem1332158 (y : hreal) (x : hreal) : (term170 y x) = (term170 y x).
Proof. exact (eq_refl (term170 y x)). Qed.
Lemma lem1332159 (y : hreal) (x : hreal) : (term162 y x) = (term177 y x).
Proof. exact (MK_COMB (@lem1332153 y) (@lem1332158 y x)). Qed.
Lemma lem1332161 (x : hreal) : (term32 x) = x.
Proof. exact (EQ_MP (@lem1331805 x) (@lem1331804 x)). Qed.
Lemma lem1332162 (y : hreal) (x : hreal) : (term177 y x) = (term170 y x).
Proof. exact (@lem1332161 (term170 y x)). Qed.
Lemma lem1332167 (y : hreal) (x : hreal) : (term162 y x) = (term170 y x).
Proof. exact (TRANS (@lem1332159 y x) (@lem1332162 y x)). Qed.
Lemma lem1332168 : term171 = term171.
Proof. exact (eq_refl term171). Qed.
Lemma lem1332169 (y : hreal) (x : hreal) : (term160 y x) = (term172 y x).
Proof. exact (MK_COMB (@lem1332168) (@lem1332167 y x)). Qed.
Lemma lem1332170 (y : hreal) (x : hreal) : ((term159 x y) = (term160 y x)) = ((term165 x y) = (term172 y x)).
Proof. exact (MK_COMB (@lem1332148 x y) (@lem1332169 y x)). Qed.
Lemma lem1332173 (y : hreal) (x : hreal) : ((term165 x y) = (term172 y x)) = ((term159 x y) = (term160 y x)).
Proof. exact (SYM (@lem1332170 y x)). Qed.
Lemma lem1332216 (y : hreal) (x : hreal) : term178 y x.
Proof. exact (@lem82 (hreal_le y x)). Qed.
Lemma lem1332221 (y : hreal) (x : hreal) (h1 : term143 y x) : (hreal_le y x) = False.
Proof. exact (@lem1332216 y x (@lem1332033 y x h1)). Qed.
Lemma lem1332222 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1332223 (y : hreal) (x : hreal) (h1 : term143 y x) : (term135 y x) = (imp False).
Proof. exact (MK_COMB (@lem1332222) (@lem1332221 y x h1)). Qed.
Lemma lem1332234 (y : hreal) (x : hreal) : ((term165 x y) = (term172 y x)) = ((term165 x y) = (term172 y x)).
Proof. exact (eq_refl ((term165 x y) = (term172 y x))). Qed.
Lemma lem1332235 (y : hreal) (x : hreal) (h1 : term143 y x) : (term179 y x) = (term180 y x).
Proof. exact (MK_COMB (@lem1332223 y x h1) (@lem1332234 y x)). Qed.
Lemma lem1332237 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1332238 (y : hreal) (x : hreal) : (term180 y x) = True.
Proof. exact (@lem1332237 ((term165 x y) = (term172 y x))). Qed.
Lemma lem1332239 (y : hreal) (x : hreal) (h1 : term143 y x) : (term179 y x) = True.
Proof. exact (TRANS (@lem1332235 y x h1) (@lem1332238 y x)). Qed.
Lemma lem1332240 (y : hreal) (x : hreal) (h1 : term143 y x) : True = (term179 y x).
Proof. exact (SYM (@lem1332239 y x h1)). Qed.
Lemma lem1332241 (y : hreal) (x : hreal) (h1 : term143 y x) : term179 y x.
Proof. exact (EQ_MP (@lem1332240 y x h1) (@lem0)). Qed.
Lemma lem1332242 (x : hreal) (y : hreal) (h1 : hreal_le x y) : hreal_le x y.
Proof. exact (h1). Qed.
Lemma lem1332244 (y : hreal) (x : hreal) : term21 y x.
Proof. exact (EQ_MP (@lem1331785 y x) (@lem1331784 x y)). Qed.
Lemma lem1332245 (x : hreal) (y : hreal) : term21 x y.
Proof. exact (@lem1332244 x y). Qed.
Lemma lem1332246 (y : hreal) (x : hreal) (h1 : hreal_le y x) : term181 x y.
Proof. exact (@lem1332245 x y (@lem1332016 y x h1)). Qed.
Lemma lem1332248 (y : hreal) (x : hreal) : term21 y x.
Proof. exact (EQ_MP (@lem1331785 y x) (@lem1331784 x y)). Qed.
Lemma lem1332249 (x : hreal) (y : hreal) (h1 : hreal_le x y) : term181 y x.
Proof. exact (@lem1332248 y x (@lem1332242 x y h1)). Qed.
Lemma lem1332250 (x : hreal) (y : hreal) (h1 : term181 x y) : term181 x y.
Proof. exact (h1). Qed.
Lemma lem1332251 (P : hreal -> Prop) : term182 P.
Proof. exact (@lem9396 hreal P). Qed.
Lemma lem1332252 (x : hreal) (y : hreal) : term183 x y.
Proof. exact (@lem1332251 (term184 x y)). Qed.
Lemma lem1332253 (x : hreal) (y : hreal) (h1 : term181 x y) : term185 x y.
Proof. exact (@lem1332252 x y (@lem1332250 x y h1)). Qed.
Lemma lem1332254 (x : hreal) (y : hreal) : (term185 x y) = (x = (term186 x y)).
Proof. exact (eq_refl (term185 x y)). Qed.
Lemma lem1332255 (x : hreal) (y : hreal) (h1 : term181 x y) : x = (term186 x y).
Proof. exact (EQ_MP (@lem1332254 x y) (@lem1332253 x y h1)). Qed.
Lemma lem1332256 (y : hreal) (x : hreal) (h1 : term181 y x) : term181 y x.
Proof. exact (h1). Qed.
Lemma lem1332257 (P : hreal -> Prop) : term182 P.
Proof. exact (@lem9396 hreal P). Qed.
Lemma lem1332258 (y : hreal) (x : hreal) : term183 y x.
Proof. exact (@lem1332257 (term184 y x)). Qed.
Lemma lem1332259 (y : hreal) (x : hreal) (h1 : term181 y x) : term185 y x.
Proof. exact (@lem1332258 y x (@lem1332256 y x h1)). Qed.
Lemma lem1332260 (y : hreal) (x : hreal) : (term185 y x) = (y = (term186 y x)).
Proof. exact (eq_refl (term185 y x)). Qed.
Lemma lem1332261 (y : hreal) (x : hreal) (h1 : term181 y x) : y = (term186 y x).
Proof. exact (EQ_MP (@lem1332260 y x) (@lem1332259 y x h1)). Qed.
Lemma lem1332262 (x : hreal) (y : hreal) (h1 : x = (term186 x y)) : x = (term186 x y).
Proof. exact (h1). Qed.
Lemma lem1332263 (x : hreal) (y : hreal) (h1 : x = (term186 x y)) : (term186 x y) = x.
Proof. exact (SYM (@lem1332262 x y h1)). Qed.
Lemma lem1332265 (x : hreal) (y : hreal) (h1 : x = (term186 x y)) : x = (term186 x y).
Proof. exact (h1). Qed.
Lemma lem1332266 (x : hreal) (y : hreal) : (term187 x y) = (term187 x y).
Proof. exact (eq_refl (term187 x y)). Qed.
Lemma lem1332267 (x : hreal) (y : hreal) (h1 : x = (term186 x y)) : (term165 y x) = (term188 x y).
Proof. exact (MK_COMB (@lem1332266 x y) (@lem1332265 x y h1)). Qed.
Lemma lem1332268 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1332269 (x : hreal) (y : hreal) (h1 : x = (term186 x y)) : (term167 y x) = (term189 x y).
Proof. exact (MK_COMB (@lem1332268) (@lem1332267 x y h1)). Qed.
Lemma lem1332270 (x : hreal) (y : hreal) : (term172 x y) = (term172 x y).
Proof. exact (eq_refl (term172 x y)). Qed.
Lemma lem1332271 (x : hreal) (y : hreal) (h1 : x = (term186 x y)) : ((term165 y x) = (term172 x y)) = ((term188 x y) = (term172 x y)).
Proof. exact (MK_COMB (@lem1332269 x y h1) (@lem1332270 x y)). Qed.
Lemma lem1332272 (x : hreal) (y : hreal) (h1 : x = (term186 x y)) : ((term188 x y) = (term172 x y)) = ((term165 y x) = (term172 x y)).
Proof. exact (SYM (@lem1332271 x y h1)). Qed.
Lemma lem1332273 (y : hreal) (x : hreal) (h1 : y = (term186 y x)) : y = (term186 y x).
Proof. exact (h1). Qed.
Lemma lem1332274 (y : hreal) (x : hreal) (h1 : y = (term186 y x)) : (term186 y x) = y.
Proof. exact (SYM (@lem1332273 y x h1)). Qed.
Lemma lem1332276 (y : hreal) (x : hreal) (h1 : y = (term186 y x)) : y = (term186 y x).
Proof. exact (h1). Qed.
Lemma lem1332277 (y : hreal) (x : hreal) : (term187 y x) = (term187 y x).
Proof. exact (eq_refl (term187 y x)). Qed.
Lemma lem1332278 (y : hreal) (x : hreal) (h1 : y = (term186 y x)) : (term165 x y) = (term188 y x).
Proof. exact (MK_COMB (@lem1332277 y x) (@lem1332276 y x h1)). Qed.
Lemma lem1332279 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1332280 (y : hreal) (x : hreal) (h1 : y = (term186 y x)) : (term167 x y) = (term189 y x).
Proof. exact (MK_COMB (@lem1332279) (@lem1332278 y x h1)). Qed.
Lemma lem1332281 (y : hreal) (x : hreal) : (term172 y x) = (term172 y x).
Proof. exact (eq_refl (term172 y x)). Qed.
Lemma lem1332282 (y : hreal) (x : hreal) (h1 : y = (term186 y x)) : ((term165 x y) = (term172 y x)) = ((term188 y x) = (term172 y x)).
Proof. exact (MK_COMB (@lem1332280 y x h1) (@lem1332281 y x)). Qed.
Lemma lem1332283 (y : hreal) (x : hreal) (h1 : y = (term186 y x)) : ((term188 y x) = (term172 y x)) = ((term165 x y) = (term172 y x)).
Proof. exact (SYM (@lem1332282 y x h1)). Qed.
Lemma lem1332287 (y : hreal) (x : hreal) (z : hreal) : (term16 x y z) = (term17 y x z).
Proof. exact (EQ_MP (@lem1331779 y x z) (@lem1331778 y x z)). Qed.
Lemma lem1332288 (x : hreal) (y : hreal) : (term188 x y) = (term190 x y).
Proof. exact (@lem1332287 y (term146 x y) (term191 x y)). Qed.
Lemma lem1332301 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1332302 (x : hreal) (y : hreal) : (term189 x y) = (term192 x y).
Proof. exact (MK_COMB (@lem1332301) (@lem1332288 x y)). Qed.
Lemma lem1332307 (x : hreal) (y : hreal) : (term172 x y) = (term172 x y).
Proof. exact (eq_refl (term172 x y)). Qed.
Lemma lem1332308 (x : hreal) (y : hreal) : ((term188 x y) = (term172 x y)) = ((term190 x y) = (term172 x y)).
Proof. exact (MK_COMB (@lem1332302 x y) (@lem1332307 x y)). Qed.
Lemma lem1332311 (x : hreal) (y : hreal) : ((term190 x y) = (term172 x y)) = ((term188 x y) = (term172 x y)).
Proof. exact (SYM (@lem1332308 x y)). Qed.
Lemma lem1332315 (y : hreal) (x : hreal) (z : hreal) : (term16 x y z) = (term17 y x z).
Proof. exact (EQ_MP (@lem1331779 y x z) (@lem1331778 y x z)). Qed.
Lemma lem1332316 (y : hreal) (x : hreal) : (term188 y x) = (term190 y x).
Proof. exact (@lem1332315 x (term146 y x) (term191 y x)). Qed.
Lemma lem1332329 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1332330 (y : hreal) (x : hreal) : (term189 y x) = (term192 y x).
Proof. exact (MK_COMB (@lem1332329) (@lem1332316 y x)). Qed.
Lemma lem1332335 (y : hreal) (x : hreal) : (term172 y x) = (term172 y x).
Proof. exact (eq_refl (term172 y x)). Qed.
Lemma lem1332336 (y : hreal) (x : hreal) : ((term188 y x) = (term172 y x)) = ((term190 y x) = (term172 y x)).
Proof. exact (MK_COMB (@lem1332330 y x) (@lem1332335 y x)). Qed.
Lemma lem1332339 (y : hreal) (x : hreal) : ((term190 y x) = (term172 y x)) = ((term188 y x) = (term172 y x)).
Proof. exact (SYM (@lem1332336 y x)). Qed.
Lemma lem1332341 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1331770 y x) (@lem1331769 x y)). Qed.
Lemma lem1332342 (x : hreal) (y : hreal) : (term172 x y) = (term193 x y).
Proof. exact (@lem1332341 (term170 x y) term5). Qed.
Lemma lem1332343 (x : hreal) (y : hreal) : (term192 x y) = (term192 x y).
Proof. exact (eq_refl (term192 x y)). Qed.
Lemma lem1332344 (x : hreal) (y : hreal) : ((term190 x y) = (term172 x y)) = ((term190 x y) = (term193 x y)).
Proof. exact (MK_COMB (@lem1332343 x y) (@lem1332342 x y)). Qed.
Lemma lem1332345 (x : hreal) (y : hreal) : ((term190 x y) = (term193 x y)) = ((term190 x y) = (term172 x y)).
Proof. exact (SYM (@lem1332344 x y)). Qed.
Lemma lem1332347 (y : hreal) (x : hreal) : (hreal_add x y) = (hreal_add y x).
Proof. exact (EQ_MP (@lem1331770 y x) (@lem1331769 x y)). Qed.
Lemma lem1332348 (y : hreal) (x : hreal) : (term172 y x) = (term193 y x).
Proof. exact (@lem1332347 (term170 y x) term5). Qed.
Lemma lem1332349 (y : hreal) (x : hreal) : (term192 y x) = (term192 y x).
Proof. exact (eq_refl (term192 y x)). Qed.
Lemma lem1332350 (y : hreal) (x : hreal) : ((term190 y x) = (term172 y x)) = ((term190 y x) = (term193 y x)).
Proof. exact (MK_COMB (@lem1332349 y x) (@lem1332348 y x)). Qed.
Lemma lem1332351 (y : hreal) (x : hreal) : ((term190 y x) = (term193 y x)) = ((term190 y x) = (term172 y x)).
Proof. exact (SYM (@lem1332350 y x)). Qed.
Lemma lem1332352 (x : hreal) (y : hreal) : (term168 x y) = (term168 x y).
Proof. exact (eq_refl (term168 x y)). Qed.
Lemma lem1332353 (y : hreal) (x : hreal) : (term168 y x) = (term168 y x).
Proof. exact (eq_refl (term168 y x)). Qed.
Lemma lem1332355 (x : hreal) : term2 x.
Proof. exact (EQ_MP (@lem1331764 x) (@lem1331763 x)). Qed.
Lemma lem1332356 (x : hreal) (y : hreal) : term194 x y.
Proof. exact (@lem1332355 (term191 x y)). Qed.
Lemma lem1332358 (x : hreal) : term2 x.
Proof. exact (EQ_MP (@lem1331764 x) (@lem1331763 x)). Qed.
Lemma lem1332359 (y : hreal) (x : hreal) : term194 y x.
Proof. exact (@lem1332358 (term191 y x)). Qed.
Lemma lem1332360 (x : hreal) (y : hreal) (h1 : (term191 x y) = term28) : (term191 x y) = term28.
Proof. exact (h1). Qed.
Lemma lem1332388 (x : hreal) (y : hreal) (h1 : term102 x y) : term102 x y.
Proof. exact (h1). Qed.
Lemma lem1332403 (y : hreal) (x : hreal) : (term195 y x) = (term195 y x).
Proof. exact (eq_refl (term195 y x)). Qed.
Lemma lem1332404 (x : hreal) (y : hreal) (h1 : (term191 x y) = term28) : (term196 x y) = (term197 y x).
Proof. exact (MK_COMB (@lem1332403 y x) (@lem1332360 x y h1)). Qed.
Lemma lem1332405 (y : hreal) (x : hreal) : (term197 y x) = ((term30 y) = x).
Proof. exact (eq_refl (term197 y x)). Qed.
Lemma lem1332406 (x : hreal) (y : hreal) : (term198 x y) = (term198 x y).
Proof. exact (eq_refl (term198 x y)). Qed.
Lemma lem1332407 (y : hreal) (x : hreal) : ((term196 x y) = (term197 y x)) = ((term196 x y) = ((term30 y) = x)).
Proof. exact (MK_COMB (@lem1332406 x y) (@lem1332405 y x)). Qed.
Lemma lem1332408 (y : hreal) (x : hreal) : (term196 x y) = ((term186 x y) = x).
Proof. exact (eq_refl (term196 x y)). Qed.
Lemma lem1332409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1332410 (y : hreal) (x : hreal) : (term198 x y) = (term199 y x).
Proof. exact (MK_COMB (@lem1332409) (@lem1332408 y x)). Qed.
Lemma lem1332411 (y : hreal) (x : hreal) : ((term30 y) = x) = ((term30 y) = x).
Proof. exact (eq_refl ((term30 y) = x)). Qed.
Lemma lem1332412 (y : hreal) (x : hreal) : ((term196 x y) = ((term30 y) = x)) = (((term186 x y) = x) = ((term30 y) = x)).
Proof. exact (MK_COMB (@lem1332410 y x) (@lem1332411 y x)). Qed.
Lemma lem1332413 (y : hreal) (x : hreal) : ((term196 x y) = (term197 y x)) = (((term186 x y) = x) = ((term30 y) = x)).
Proof. exact (TRANS (@lem1332407 y x) (@lem1332412 y x)). Qed.
Lemma lem1332414 (x : hreal) (y : hreal) (h1 : (term191 x y) = term28) : ((term186 x y) = x) = ((term30 y) = x).
Proof. exact (EQ_MP (@lem1332413 y x) (@lem1332404 x y h1)). Qed.
Lemma lem1332415 (x : hreal) (y : hreal) (h1 : x = (term186 x y)) (h2 : (term191 x y) = term28) : (term30 y) = x.
Proof. exact (EQ_MP (@lem1332414 x y h2) (@lem1332263 x y h1)). Qed.
Lemma lem1332416 (y : hreal) (x : hreal) (h1 : (term191 y x) = term28) : (term191 y x) = term28.
Proof. exact (h1). Qed.
Lemma lem1332444 (x : hreal) (y : hreal) (h1 : term102 x y) : term102 x y.
Proof. exact (h1). Qed.
Lemma lem1332473 (x : hreal) (y : hreal) : (term195 x y) = (term195 x y).
Proof. exact (eq_refl (term195 x y)). Qed.
Lemma lem1332474 (y : hreal) (x : hreal) (h1 : (term191 y x) = term28) : (term196 y x) = (term197 x y).
Proof. exact (MK_COMB (@lem1332473 x y) (@lem1332416 y x h1)). Qed.
Lemma lem1332475 (x : hreal) (y : hreal) : (term197 x y) = ((term30 x) = y).
Proof. exact (eq_refl (term197 x y)). Qed.
Lemma lem1332476 (y : hreal) (x : hreal) : (term198 y x) = (term198 y x).
Proof. exact (eq_refl (term198 y x)). Qed.
Lemma lem1332477 (x : hreal) (y : hreal) : ((term196 y x) = (term197 x y)) = ((term196 y x) = ((term30 x) = y)).
Proof. exact (MK_COMB (@lem1332476 y x) (@lem1332475 x y)). Qed.
Lemma lem1332478 (x : hreal) (y : hreal) : (term196 y x) = ((term186 y x) = y).
Proof. exact (eq_refl (term196 y x)). Qed.
Lemma lem1332479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1332480 (x : hreal) (y : hreal) : (term198 y x) = (term199 x y).
Proof. exact (MK_COMB (@lem1332479) (@lem1332478 x y)). Qed.
Lemma lem1332481 (x : hreal) (y : hreal) : ((term30 x) = y) = ((term30 x) = y).
Proof. exact (eq_refl ((term30 x) = y)). Qed.
Lemma lem1332482 (x : hreal) (y : hreal) : ((term196 y x) = ((term30 x) = y)) = (((term186 y x) = y) = ((term30 x) = y)).
Proof. exact (MK_COMB (@lem1332480 x y) (@lem1332481 x y)). Qed.
Lemma lem1332483 (x : hreal) (y : hreal) : ((term196 y x) = (term197 x y)) = (((term186 y x) = y) = ((term30 x) = y)).
Proof. exact (TRANS (@lem1332477 x y) (@lem1332482 x y)). Qed.
Lemma lem1332484 (y : hreal) (x : hreal) (h1 : (term191 y x) = term28) : ((term186 y x) = y) = ((term30 x) = y).
Proof. exact (EQ_MP (@lem1332483 x y) (@lem1332474 y x h1)). Qed.
Lemma lem1332485 (y : hreal) (x : hreal) (h1 : y = (term186 y x)) (h2 : (term191 y x) = term28) : (term30 x) = y.
Proof. exact (EQ_MP (@lem1332484 y x h2) (@lem1332274 y x h1)). Qed.
Lemma lem1332486 (n : hreal) : term29 n.
Proof. exact (@lem1321694 n). Qed.
Lemma lem1332487 (n : hreal) : (term29 n) = ((term30 n) = n).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem1332492 (x : hreal) (y : hreal) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1332493 (x : hreal) (y : hreal) (h1 : x = y) : y = x.
Proof. exact (SYM (@lem1332492 x y h1)). Qed.
Lemma lem1332494 (y : hreal) (x : hreal) (h1 : y = x) : y = x.
Proof. exact (h1). Qed.
Lemma lem1332495 (y : hreal) (x : hreal) (h1 : y = x) : x = y.
Proof. exact (SYM (@lem1332494 y x h1)). Qed.
Lemma lem1332496 (y : hreal) (x : hreal) : (x = y) = (y = x).
Proof. exact (prop_ext (fun h1 : x = y => @lem1332493 x y h1) (fun h1 : y = x => @lem1332495 y x h1)). Qed.
Lemma lem1332497 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1332498 (y : hreal) (x : hreal) : (term102 x y) = (term102 y x).
Proof. exact (MK_COMB (@lem1332497) (@lem1332496 y x)). Qed.
Lemma lem1332499 (x : hreal) (y : hreal) (h1 : term102 x y) : term102 y x.
Proof. exact (EQ_MP (@lem1332498 y x) (@lem1332388 x y h1)). Qed.
Lemma lem1332500 (y : hreal) (x : hreal) : term109 y x.
Proof. exact (@lem82 (y = x)). Qed.
Lemma lem1332507 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1332508 (y : hreal) (x : hreal) : (term200 y x) = (term201 y x).
Proof. exact (@lem1332507 ((term30 y) = x)). Qed.
Lemma lem1332512 (n : hreal) : (term30 n) = n.
Proof. exact (EQ_MP (@lem1332487 n) (@lem1332486 n)). Qed.
Lemma lem1332513 (y : hreal) : (term30 y) = y.
Proof. exact (@lem1332512 y). Qed.
Lemma lem1332514 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1332515 (y : hreal) : (term101 y) = (@eq hreal y).
Proof. exact (MK_COMB (@lem1332514) (@lem1332513 y)). Qed.
Lemma lem1332516 (x : hreal) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1332517 (y : hreal) (x : hreal) : ((term30 y) = x) = (y = x).
Proof. exact (MK_COMB (@lem1332515 y) (@lem1332516 x)). Qed.
Lemma lem1332519 (x : hreal) (y : hreal) (h1 : term102 x y) : (y = x) = False.
Proof. exact (@lem1332500 y x (@lem1332499 x y h1)). Qed.
Lemma lem1332520 (x : hreal) (y : hreal) (h1 : term102 x y) : ((term30 y) = x) = False.
Proof. exact (TRANS (@lem1332517 y x) (@lem1332519 x y h1)). Qed.
Lemma lem1332521 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1332522 (x : hreal) (y : hreal) (h1 : term102 x y) : (term201 y x) = (~ False).
Proof. exact (MK_COMB (@lem1332521) (@lem1332520 x y h1)). Qed.
Lemma lem1332524 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1332525 (x : hreal) (y : hreal) (h1 : term102 x y) : (term201 y x) = True.
Proof. exact (TRANS (@lem1332522 x y h1) (@lem1332524)). Qed.
Lemma lem1332526 (x : hreal) (y : hreal) (h1 : term102 x y) : (term200 y x) = True.
Proof. exact (TRANS (@lem1332508 y x) (@lem1332525 x y h1)). Qed.
Lemma lem1332527 (x : hreal) (y : hreal) (h1 : term102 x y) : True = (term200 y x).
Proof. exact (SYM (@lem1332526 x y h1)). Qed.
Lemma lem1332528 (x : hreal) (y : hreal) (h1 : term102 x y) : term200 y x.
Proof. exact (EQ_MP (@lem1332527 x y h1) (@lem0)). Qed.
Lemma lem1332529 (n : hreal) : term29 n.
Proof. exact (@lem1321694 n). Qed.
Lemma lem1332530 (n : hreal) : (term29 n) = ((term30 n) = n).
Proof. exact (eq_refl (term29 n)). Qed.
Lemma lem1332532 (x : hreal) (y : hreal) : term109 x y.
Proof. exact (@lem82 (x = y)). Qed.
Lemma lem1332552 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1332553 (x : hreal) (y : hreal) : (term200 x y) = (term201 x y).
Proof. exact (@lem1332552 ((term30 x) = y)). Qed.
Lemma lem1332557 (n : hreal) : (term30 n) = n.
Proof. exact (EQ_MP (@lem1332530 n) (@lem1332529 n)). Qed.
Lemma lem1332558 (x : hreal) : (term30 x) = x.
Proof. exact (@lem1332557 x). Qed.
Lemma lem1332559 : (@eq hreal) = (@eq hreal).
Proof. exact (eq_refl (@eq hreal)). Qed.
Lemma lem1332560 (x : hreal) : (term101 x) = (@eq hreal x).
Proof. exact (MK_COMB (@lem1332559) (@lem1332558 x)). Qed.
Lemma lem1332561 (y : hreal) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1332562 (x : hreal) (y : hreal) : ((term30 x) = y) = (x = y).
Proof. exact (MK_COMB (@lem1332560 x) (@lem1332561 y)). Qed.
Lemma lem1332564 (x : hreal) (y : hreal) (h1 : term102 x y) : (x = y) = False.
Proof. exact (@lem1332532 x y (@lem1332444 x y h1)). Qed.
Lemma lem1332565 (x : hreal) (y : hreal) (h1 : term102 x y) : ((term30 x) = y) = False.
Proof. exact (TRANS (@lem1332562 x y) (@lem1332564 x y h1)). Qed.
Lemma lem1332566 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1332567 (x : hreal) (y : hreal) (h1 : term102 x y) : (term201 x y) = (~ False).
Proof. exact (MK_COMB (@lem1332566) (@lem1332565 x y h1)). Qed.
Lemma lem1332569 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1332570 (x : hreal) (y : hreal) (h1 : term102 x y) : (term201 x y) = True.
Proof. exact (TRANS (@lem1332567 x y h1) (@lem1332569)). Qed.
Lemma lem1332571 (x : hreal) (y : hreal) (h1 : term102 x y) : (term200 x y) = True.
Proof. exact (TRANS (@lem1332553 x y) (@lem1332570 x y h1)). Qed.
Lemma lem1332572 (x : hreal) (y : hreal) (h1 : term102 x y) : True = (term200 x y).
Proof. exact (SYM (@lem1332571 x y h1)). Qed.
Lemma lem1332573 (x : hreal) (y : hreal) (h1 : term102 x y) : term200 x y.
Proof. exact (EQ_MP (@lem1332572 x y h1) (@lem0)). Qed.
Lemma lem1332574 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : y = (term186 y x)) (h3 : (term191 y x) = term28) : False.
Proof. exact (@lem1332573 x y h1 (@lem1332485 y x h2 h3)). Qed.
Lemma lem1332575 (x : hreal) (y : hreal) (h1 : term102 x y) (h2 : x = (term186 x y)) (h3 : (term191 x y) = term28) : False.
Proof. exact (@lem1332528 x y h1 (@lem1332415 x y h2 h3)). Qed.
Lemma lem1332576 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : y = (term186 y x)) (h3 : (term191 y x) = term28) : (term102 x y) = False.
Proof. exact (prop_ext (fun h4 : term102 x y => @lem1332574 y x h1 h2 h3) (fun h4 : False => @lem1332444 x y h1)). Qed.
Lemma lem1332578 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : y = (term186 y x)) (h3 : (term191 y x) = term28) : False.
Proof. exact (EQ_MP (@lem1332576 y x h1 h2 h3) (@lem1332444 x y h1)). Qed.
Lemma lem1332579 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : y = (term186 y x)) : term202 y x.
Proof. exact (fun h0 : (term191 y x) = term28 => @lem1332578 y x h1 h2 h0). Qed.
Lemma lem1332580 (y : hreal) (x : hreal) : (term202 y x) = (term203 y x).
Proof. exact (@lem69 ((term191 y x) = term28)). Qed.
Lemma lem1332581 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : y = (term186 y x)) : term203 y x.
Proof. exact (EQ_MP (@lem1332580 y x) (@lem1332579 y x h1 h2)). Qed.
Lemma lem1332582 (x : hreal) (y : hreal) (h1 : term102 x y) (h2 : x = (term186 x y)) (h3 : (term191 x y) = term28) : (term102 x y) = False.
Proof. exact (prop_ext (fun h4 : term102 x y => @lem1332575 x y h1 h2 h3) (fun h4 : False => @lem1332388 x y h1)). Qed.
Lemma lem1332584 (x : hreal) (y : hreal) (h1 : term102 x y) (h2 : x = (term186 x y)) (h3 : (term191 x y) = term28) : False.
Proof. exact (EQ_MP (@lem1332582 x y h1 h2 h3) (@lem1332388 x y h1)). Qed.
Lemma lem1332585 (x : hreal) (y : hreal) (h1 : term102 x y) (h2 : x = (term186 x y)) : term202 x y.
Proof. exact (fun h0 : (term191 x y) = term28 => @lem1332584 x y h1 h2 h0). Qed.
Lemma lem1332586 (x : hreal) (y : hreal) : (term202 x y) = (term203 x y).
Proof. exact (@lem69 ((term191 x y) = term28)). Qed.
Lemma lem1332587 (x : hreal) (y : hreal) (h1 : term102 x y) (h2 : x = (term186 x y)) : term203 x y.
Proof. exact (EQ_MP (@lem1332586 x y) (@lem1332585 x y h1 h2)). Qed.
Lemma lem1332588 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : y = (term186 y x)) : (term204 y x) = term5.
Proof. exact (@lem1332359 y x (@lem1332581 y x h1 h2)). Qed.
Lemma lem1332589 (x : hreal) (y : hreal) (h1 : term102 x y) (h2 : x = (term186 x y)) : (term204 x y) = term5.
Proof. exact (@lem1332356 x y (@lem1332587 x y h1 h2)). Qed.
Lemma lem1332590 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : y = (term186 y x)) : (term190 y x) = (term193 y x).
Proof. exact (MK_COMB (@lem1332353 y x) (@lem1332588 y x h1 h2)). Qed.
Lemma lem1332591 (x : hreal) (y : hreal) (h1 : term102 x y) (h2 : x = (term186 x y)) : (term190 x y) = (term193 x y).
Proof. exact (MK_COMB (@lem1332352 x y) (@lem1332589 x y h1 h2)). Qed.
Lemma lem1332592 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : y = (term186 y x)) : (term190 y x) = (term172 y x).
Proof. exact (EQ_MP (@lem1332351 y x) (@lem1332590 y x h1 h2)). Qed.
Lemma lem1332593 (x : hreal) (y : hreal) (h1 : term102 x y) (h2 : x = (term186 x y)) : (term190 x y) = (term172 x y).
Proof. exact (EQ_MP (@lem1332345 x y) (@lem1332591 x y h1 h2)). Qed.
Lemma lem1332594 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : y = (term186 y x)) : (term188 y x) = (term172 y x).
Proof. exact (EQ_MP (@lem1332339 y x) (@lem1332592 y x h1 h2)). Qed.
Lemma lem1332595 (x : hreal) (y : hreal) (h1 : term102 x y) (h2 : x = (term186 x y)) : (term188 x y) = (term172 x y).
Proof. exact (EQ_MP (@lem1332311 x y) (@lem1332593 x y h1 h2)). Qed.
Lemma lem1332596 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : y = (term186 y x)) : (term165 x y) = (term172 y x).
Proof. exact (EQ_MP (@lem1332283 y x h2) (@lem1332594 y x h1 h2)). Qed.
Lemma lem1332597 (x : hreal) (y : hreal) (h1 : term102 x y) : term205 y x.
Proof. exact (fun h0 : y = (term186 y x) => @lem1332596 y x h1 h0). Qed.
Lemma lem1332598 (x : hreal) (y : hreal) (h1 : term102 x y) (h2 : x = (term186 x y)) : (term165 y x) = (term172 x y).
Proof. exact (EQ_MP (@lem1332272 x y h2) (@lem1332595 x y h1 h2)). Qed.
Lemma lem1332599 (x : hreal) (y : hreal) (h1 : term102 x y) : term205 x y.
Proof. exact (fun h0 : x = (term186 x y) => @lem1332598 x y h1 h0). Qed.
Lemma lem1332600 (x : hreal) (y : hreal) (h1 : term181 y x) (h2 : term102 x y) : (term165 x y) = (term172 y x).
Proof. exact (@lem1332597 x y h2 (@lem1332261 y x h1)). Qed.
Lemma lem1332601 (x : hreal) (y : hreal) (h1 : term102 x y) : term206 y x.
Proof. exact (fun h0 : term181 y x => @lem1332600 x y h0 h1). Qed.
Lemma lem1332602 (x : hreal) (y : hreal) (h1 : term181 x y) (h2 : term102 x y) : (term165 y x) = (term172 x y).
Proof. exact (@lem1332599 x y h2 (@lem1332255 x y h1)). Qed.
Lemma lem1332603 (x : hreal) (y : hreal) (h1 : term102 x y) : term206 x y.
Proof. exact (fun h0 : term181 x y => @lem1332602 x y h0 h1). Qed.
Lemma lem1332604 (x : hreal) (y : hreal) (h1 : term102 x y) (h2 : hreal_le x y) : (term165 x y) = (term172 y x).
Proof. exact (@lem1332601 x y h1 (@lem1332249 x y h2)). Qed.
Lemma lem1332605 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : hreal_le y x) : (term165 y x) = (term172 x y).
Proof. exact (@lem1332603 x y h1 (@lem1332246 y x h2)). Qed.
Lemma lem1332607 (x : hreal) (y : hreal) (h1 : term102 x y) : term207 y x.
Proof. exact (fun h0 : hreal_le x y => @lem1332604 x y h1 h0). Qed.
Lemma lem1332608 (y : hreal) (x : hreal) (h1 : term143 y x) (h2 : hreal_le y x) : (term165 x y) = (term172 y x).
Proof. exact (@lem1332241 y x h1 (@lem1331794 y x h2)). Qed.
Lemma lem1332609 (x : hreal) (y : hreal) (h1 : term102 x y) (h2 : hreal_le x y) : (term165 x y) = (term172 y x).
Proof. exact (@lem1332607 x y h1 (@lem1331793 x y h2)). Qed.
Lemma lem1332610 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : term143 y x) : (term165 x y) = (term172 y x).
Proof. exact (or_elim (@lem1331792 y x) (fun h0 : hreal_le x y => @lem1332609 x y h1 h0) (fun h0 : hreal_le y x => @lem1332608 y x h2 h0)). Qed.
Lemma lem1332611 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : term143 y x) : (term159 x y) = (term160 y x).
Proof. exact (EQ_MP (@lem1332173 y x) (@lem1332610 y x h1 h2)). Qed.
Lemma lem1332612 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : hreal_le y x) : (term150 x y) = (term151 y x).
Proof. exact (EQ_MP (@lem1332121 y x) (@lem1332605 y x h1 h2)). Qed.
Lemma lem1332615 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : term143 y x) : term129 x y.
Proof. exact (EQ_MP (@lem1332073 x y) (@lem1332611 y x h1 h2)). Qed.
Lemma lem1332616 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : term143 y x) : (term143 y x) = (term129 x y).
Proof. exact (prop_ext (fun h3 : term143 y x => @lem1332615 y x h1 h2) (fun h3 : term129 x y => @lem1332033 y x h2)). Qed.
Lemma lem1332617 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : term143 y x) : term129 x y.
Proof. exact (EQ_MP (@lem1332616 y x h1 h2) (@lem1332033 y x h2)). Qed.
Lemma lem1332618 (x : hreal) (y : hreal) (h1 : term102 x y) : term132 x y.
Proof. exact (fun h0 : term143 y x => @lem1332617 y x h1 h0). Qed.
Lemma lem1332619 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : hreal_le y x) : term134 x y.
Proof. exact (EQ_MP (@lem1332061 x y) (@lem1332612 y x h1 h2)). Qed.
Lemma lem1332620 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : hreal_le y x) : (hreal_le y x) = (term134 x y).
Proof. exact (prop_ext (fun h3 : hreal_le y x => @lem1332619 y x h1 h2) (fun h3 : term134 x y => @lem1332016 y x h2)). Qed.
Lemma lem1332621 (y : hreal) (x : hreal) (h1 : term102 x y) (h2 : hreal_le y x) : term134 x y.
Proof. exact (EQ_MP (@lem1332620 y x h1 h2) (@lem1332016 y x h2)). Qed.
Lemma lem1332622 (x : hreal) (y : hreal) (h1 : term102 x y) : term137 x y.
Proof. exact (fun h0 : hreal_le y x => @lem1332621 y x h1 h0). Qed.
Lemma lem1332623 (x : hreal) (y : hreal) (h1 : term102 x y) : term140 x y.
Proof. exact (conj (@lem1332622 x y h1) (@lem1332618 x y h1)). Qed.
Lemma lem1332624 (x : hreal) (y : hreal) (h1 : term102 x y) : term118 x y.
Proof. exact (EQ_MP (@lem1332015 x y) (@lem1332623 x y h1)). Qed.
Lemma lem1332625 (x : hreal) (y : hreal) (h1 : term102 x y) : term99 x y.
Proof. exact (EQ_MP (@lem1331997 x y h1) (@lem1332624 x y h1)). Qed.
Lemma lem1332626 (x : hreal) (y : hreal) : term104 x y.
Proof. exact (fun h0 : term102 x y => @lem1332625 x y h0). Qed.
Lemma lem1332627 (x : hreal) (y : hreal) : term100 x y.
Proof. exact (EQ_MP (@lem1331953 x y) (@lem1332626 x y)). Qed.
Lemma lem1332628 (x : hreal) (y : hreal) : term72 x y.
Proof. exact (EQ_MP (@lem1331937 x y) (@lem1332627 x y)). Qed.
Lemma lem1332633 (x : hreal) : term76 x.
Proof. exact (fun y : hreal => @lem1332628 x y). Qed.
Lemma lem1332638 : term79.
Proof. exact (fun x : hreal => @lem1332633 x). Qed.
Lemma lem1332639 : term68.
Proof. exact (EQ_MP (@lem1331910) (@lem1332638)). Qed.
