Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_term_abbrevs.
Require Import ADD_AC_spec.
Require Import BOUNDS_NOTZERO_spec.
Require Import DIST_REFL_spec.
Require Import DIST_SYM_spec.
Require Import EQ_IMP_LE_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_ADD2_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_TRANS_spec.
Require Import MULT_ASSOC_spec.
Require Import NADD_CAUCHY_spec.
Require Import NADD_DIST_spec.
Require Import NADD_MULTIPLICATIVE_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import is_nadd_spec.
Require Import nadd_mul_spec.
Require Import thm0_spec.
Require Import thm1259719_spec.
Require Import thm1262760_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm272809_spec.
Require Import thm7_spec.
Lemma lem1276767 (n : nat) (m : nat) (p : nat) : term0 n m p.
Proof. exact (proj2 (@lem79120 n m p)). Qed.
Lemma lem1276771 (m : nat) : term1 m.
Proof. exact (@lem82357 m). Qed.
Lemma lem1276772 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem1276773 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem1276772 m) (@lem1276771 m)). Qed.
Lemma lem1276774 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem1276773 m n). Qed.
Lemma lem1276775 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem1276776 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem1276775 m n) (@lem1276774 m n)). Qed.
Lemma lem1276777 (m : nat) (n : nat) (p : nat) : term5 m n p.
Proof. exact (@lem1276776 m n p). Qed.
Lemma lem1276778 (m : nat) (n : nat) (p : nat) : (term5 m n p) = ((term6 m n p) = (term7 m n p)).
Proof. exact (eq_refl (term5 m n p)). Qed.
Lemma lem1276780 (m : nat) : term8 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1276781 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem1276782 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem1276781 m) (@lem1276780 m)). Qed.
Lemma lem1276783 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem1276782 m n). Qed.
Lemma lem1276784 (m : nat) (n : nat) : (term10 m n) = (term11 m n).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem1276785 (m : nat) (n : nat) : term11 m n.
Proof. exact (EQ_MP (@lem1276784 m n) (@lem1276783 m n)). Qed.
Lemma lem1276786 (m : nat) (n : nat) (p : nat) : term12 m n p.
Proof. exact (@lem1276785 m n p). Qed.
Lemma lem1276787 (m : nat) (n : nat) (p : nat) : (term12 m n p) = ((term13 m n p) = (term14 m n p)).
Proof. exact (eq_refl (term12 m n p)). Qed.
Lemma lem1276789 (m : nat) : term15 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1276790 (m : nat) : (term15 m) = (term16 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem1276791 (m : nat) : term16 m.
Proof. exact (EQ_MP (@lem1276790 m) (@lem1276789 m)). Qed.
Lemma lem1276792 (m : nat) (n : nat) : term17 m n.
Proof. exact (@lem1276791 m n). Qed.
Lemma lem1276793 (n : nat) (m : nat) : (term17 m n) = (term18 n m).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem1276794 (n : nat) (m : nat) : term18 n m.
Proof. exact (EQ_MP (@lem1276793 n m) (@lem1276792 m n)). Qed.
Lemma lem1276795 (n : nat) (m : nat) (p : nat) : term19 n m p.
Proof. exact (@lem1276794 n m p). Qed.
Lemma lem1276796 (n : nat) (m : nat) (p : nat) : (term19 n m p) = ((term20 m n p) = (term21 n m p)).
Proof. exact (eq_refl (term19 n m p)). Qed.
Lemma lem1276798 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1276799 (m : nat) (h1 : term22) : term23 m.
Proof. exact (@lem1276798 h1 m). Qed.
Lemma lem1276800 (m : nat) : (term23 m) = (term24 m).
Proof. exact (eq_refl (term23 m)). Qed.
Lemma lem1276801 (m : nat) (h1 : term22) : term24 m.
Proof. exact (EQ_MP (@lem1276800 m) (@lem1276799 m h1)). Qed.
Lemma lem1276802 (m : nat) (n : nat) (h1 : term22) : term25 m n.
Proof. exact (@lem1276801 m h1 n). Qed.
Lemma lem1276803 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem1276804 (m : nat) (n : nat) (h1 : term22) : term26 m n.
Proof. exact (EQ_MP (@lem1276803 m n) (@lem1276802 m n h1)). Qed.
Lemma lem1276805 (m : nat) (n : nat) (h1 : m = n) : m = n.
Proof. exact (h1). Qed.
Lemma lem1276806 (m : nat) (n : nat) (h1 : term22) (h2 : m = n) : Peano.le m n.
Proof. exact (@lem1276804 m n h1 (@lem1276805 m n h2)). Qed.
Lemma lem1276807 (m : nat) (n : nat) (h1 : m = n) : term27 m n.
Proof. exact (fun h0 : term22 => @lem1276806 m n h0 h1). Qed.
Lemma lem1276808 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1276809 (m : nat) (n : nat) (h1 : term22) (h2 : m = n) : Peano.le m n.
Proof. exact (@lem1276807 m n h2 (@lem1276808 h1)). Qed.
Lemma lem1276810 (m : nat) (n : nat) (h1 : term22) : term26 m n.
Proof. exact (fun h0 : m = n => @lem1276809 m n h1 h0). Qed.
Lemma lem1276811 (m : nat) (h1 : term22) : term24 m.
Proof. exact (fun n : nat => @lem1276810 m n h1). Qed.
Lemma lem1276812 (h1 : term22) : term22.
Proof. exact (fun m : nat => @lem1276811 m h1). Qed.
Lemma lem1276813 : term28.
Proof. exact (fun h0 : term22 => @lem1276812 h0). Qed.
Lemma lem1276814 : term22.
Proof. exact (@lem1276813 (@lem98471)). Qed.
Lemma lem1276815 (m : nat) : term23 m.
Proof. exact (@lem1276814 m). Qed.
Lemma lem1276816 (m : nat) : (term23 m) = (term24 m).
Proof. exact (eq_refl (term23 m)). Qed.
Lemma lem1276817 (m : nat) : term24 m.
Proof. exact (EQ_MP (@lem1276816 m) (@lem1276815 m)). Qed.
Lemma lem1276818 (m : nat) (n : nat) : term25 m n.
Proof. exact (@lem1276817 m n). Qed.
Lemma lem1276819 (m : nat) (n : nat) : (term25 m n) = (term26 m n).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem1276821 (h1 : term29) : term29.
Proof. exact (h1). Qed.
Lemma lem1276822 (m : nat) (h1 : term29) : term30 m.
Proof. exact (@lem1276821 h1 m). Qed.
Lemma lem1276823 (m : nat) : (term30 m) = (term31 m).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem1276824 (m : nat) (h1 : term29) : term31 m.
Proof. exact (EQ_MP (@lem1276823 m) (@lem1276822 m h1)). Qed.
Lemma lem1276825 (m : nat) (n : nat) (h1 : term29) : term32 m n.
Proof. exact (@lem1276824 m h1 n). Qed.
Lemma lem1276826 (n : nat) (m : nat) : (term32 m n) = (term33 n m).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem1276827 (n : nat) (m : nat) (h1 : term29) : term33 n m.
Proof. exact (EQ_MP (@lem1276826 n m) (@lem1276825 m n h1)). Qed.
Lemma lem1276828 (n : nat) (m : nat) (p : nat) (h1 : term29) : term34 n m p.
Proof. exact (@lem1276827 n m h1 p). Qed.
Lemma lem1276829 (n : nat) (m : nat) (p : nat) : (term34 n m p) = (term35 n m p).
Proof. exact (eq_refl (term34 n m p)). Qed.
Lemma lem1276830 (n : nat) (m : nat) (p : nat) (h1 : term29) : term35 n m p.
Proof. exact (EQ_MP (@lem1276829 n m p) (@lem1276828 n m p h1)). Qed.
Lemma lem1276831 (m : nat) (n : nat) (p : nat) (h1 : term36 m n p) : term36 m n p.
Proof. exact (h1). Qed.
Lemma lem1276832 (m : nat) (n : nat) (p : nat) (h1 : term29) (h2 : term36 m n p) : Peano.le m p.
Proof. exact (@lem1276830 n m p h1 (@lem1276831 m n p h2)). Qed.
Lemma lem1276833 (m : nat) (n : nat) (p : nat) (h1 : term36 m n p) : term37 m p.
Proof. exact (fun h0 : term29 => @lem1276832 m n p h0 h1). Qed.
Lemma lem1276834 (m : nat) (p : nat) (h1 : term38 m p) : term38 m p.
Proof. exact (h1). Qed.
Lemma lem1276835 (m : nat) (p : nat) (h1 : term38 m p) : term37 m p.
Proof. exact (ex_elim (@lem1276834 m p h1) (fun n : nat => fun h0 : term39 m p n => @lem1276833 m n p h0)). Qed.
Lemma lem1276836 (h1 : term29) : term29.
Proof. exact (h1). Qed.
Lemma lem1276837 (m : nat) (p : nat) (h1 : term29) (h2 : term38 m p) : Peano.le m p.
Proof. exact (@lem1276835 m p h2 (@lem1276836 h1)). Qed.
Lemma lem1276838 (m : nat) (p : nat) (h1 : term29) : term40 m p.
Proof. exact (fun h0 : term38 m p => @lem1276837 m p h1 h0). Qed.
Lemma lem1276839 (m : nat) (h1 : term29) : term41 m.
Proof. exact (fun p : nat => @lem1276838 m p h1). Qed.
Lemma lem1276840 (h1 : term29) : term42.
Proof. exact (fun m : nat => @lem1276839 m h1). Qed.
Lemma lem1276841 : term43.
Proof. exact (fun h0 : term29 => @lem1276840 h0). Qed.
Lemma lem1276842 : term42.
Proof. exact (@lem1276841 (@lem93743)). Qed.
Lemma lem1276843 (m : nat) : term44 m.
Proof. exact (@lem1276842 m). Qed.
Lemma lem1276844 (m : nat) : (term44 m) = (term41 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem1276845 (m : nat) : term41 m.
Proof. exact (EQ_MP (@lem1276844 m) (@lem1276843 m)). Qed.
Lemma lem1276846 (m : nat) (p : nat) : term45 m p.
Proof. exact (@lem1276845 m p). Qed.
Lemma lem1276847 (m : nat) (p : nat) : (term45 m p) = (term40 m p).
Proof. exact (eq_refl (term45 m p)). Qed.
Lemma lem1276849 (m : nat) : term46 m.
Proof. exact (@lem1244997 m). Qed.
Lemma lem1276850 (m : nat) : (term46 m) = (term47 m).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem1276851 (m : nat) : term47 m.
Proof. exact (EQ_MP (@lem1276850 m) (@lem1276849 m)). Qed.
Lemma lem1276852 (m : nat) (n : nat) : term48 m n.
Proof. exact (@lem1276851 m n). Qed.
Lemma lem1276853 (n : nat) (m : nat) : (term48 m n) = ((term49 m n) = (term49 n m)).
Proof. exact (eq_refl (term48 m n)). Qed.
Lemma lem1276855 (h1 : term50) : term50.
Proof. exact (h1). Qed.
Lemma lem1276856 (m : nat) (h1 : term50) : term51 m.
Proof. exact (@lem1276855 h1 m). Qed.
Lemma lem1276857 (m : nat) : (term51 m) = (term52 m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem1276858 (m : nat) (h1 : term50) : term52 m.
Proof. exact (EQ_MP (@lem1276857 m) (@lem1276856 m h1)). Qed.
Lemma lem1276859 (m : nat) (n : nat) (h1 : term50) : term53 m n.
Proof. exact (@lem1276858 m h1 n). Qed.
Lemma lem1276860 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (eq_refl (term53 m n)). Qed.
Lemma lem1276861 (m : nat) (n : nat) (h1 : term50) : term54 m n.
Proof. exact (EQ_MP (@lem1276860 m n) (@lem1276859 m n h1)). Qed.
Lemma lem1276862 (m : nat) (n : nat) (p : nat) (h1 : term50) : term55 m n p.
Proof. exact (@lem1276861 m n h1 p). Qed.
Lemma lem1276863 (m : nat) (n : nat) (p : nat) : (term55 m n p) = (term56 m n p).
Proof. exact (eq_refl (term55 m n p)). Qed.
Lemma lem1276864 (m : nat) (n : nat) (p : nat) (h1 : term50) : term56 m n p.
Proof. exact (EQ_MP (@lem1276863 m n p) (@lem1276862 m n p h1)). Qed.
Lemma lem1276865 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term50) : term57 m n p q.
Proof. exact (@lem1276864 m n p h1 q). Qed.
Lemma lem1276866 (m : nat) (n : nat) (p : nat) (q : nat) : (term57 m n p q) = (term58 m n p q).
Proof. exact (eq_refl (term57 m n p q)). Qed.
Lemma lem1276867 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term50) : term58 m n p q.
Proof. exact (EQ_MP (@lem1276866 m n p q) (@lem1276865 m n p q h1)). Qed.
Lemma lem1276868 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term59 m p n q) : term59 m p n q.
Proof. exact (h1). Qed.
Lemma lem1276869 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term50) (h2 : term59 m p n q) : term60 m n p q.
Proof. exact (@lem1276867 m n p q h1 (@lem1276868 m p n q h2)). Qed.
Lemma lem1276870 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term59 m p n q) : term61 m n p q.
Proof. exact (fun h0 : term50 => @lem1276869 m p n q h0 h1). Qed.
Lemma lem1276871 (h1 : term50) : term50.
Proof. exact (h1). Qed.
Lemma lem1276872 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term50) (h2 : term59 m p n q) : term60 m n p q.
Proof. exact (@lem1276870 m p n q h2 (@lem1276871 h1)). Qed.
Lemma lem1276873 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term50) : term58 m n p q.
Proof. exact (fun h0 : term59 m p n q => @lem1276872 m p n q h1 h0). Qed.
Lemma lem1276874 (m : nat) (n : nat) (p : nat) (h1 : term50) : term56 m n p.
Proof. exact (fun q : nat => @lem1276873 m n p q h1). Qed.
Lemma lem1276875 (m : nat) (n : nat) (h1 : term50) : term54 m n.
Proof. exact (fun p : nat => @lem1276874 m n p h1). Qed.
Lemma lem1276876 (m : nat) (h1 : term50) : term52 m.
Proof. exact (fun n : nat => @lem1276875 m n h1). Qed.
Lemma lem1276877 (h1 : term50) : term50.
Proof. exact (fun m : nat => @lem1276876 m h1). Qed.
Lemma lem1276878 : term62.
Proof. exact (fun h0 : term50 => @lem1276877 h0). Qed.
Lemma lem1276879 : term50.
Proof. exact (@lem1276878 (@lem101399)). Qed.
Lemma lem1276880 (m : nat) : term51 m.
Proof. exact (@lem1276879 m). Qed.
Lemma lem1276881 (m : nat) : (term51 m) = (term52 m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem1276882 (m : nat) : term52 m.
Proof. exact (EQ_MP (@lem1276881 m) (@lem1276880 m)). Qed.
Lemma lem1276883 (m : nat) (n : nat) : term53 m n.
Proof. exact (@lem1276882 m n). Qed.
Lemma lem1276884 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (eq_refl (term53 m n)). Qed.
Lemma lem1276885 (m : nat) (n : nat) : term54 m n.
Proof. exact (EQ_MP (@lem1276884 m n) (@lem1276883 m n)). Qed.
Lemma lem1276886 (m : nat) (n : nat) (p : nat) : term55 m n p.
Proof. exact (@lem1276885 m n p). Qed.
Lemma lem1276887 (m : nat) (n : nat) (p : nat) : (term55 m n p) = (term56 m n p).
Proof. exact (eq_refl (term55 m n p)). Qed.
Lemma lem1276888 (m : nat) (n : nat) (p : nat) : term56 m n p.
Proof. exact (EQ_MP (@lem1276887 m n p) (@lem1276886 m n p)). Qed.
Lemma lem1276889 (m : nat) (n : nat) (p : nat) (q : nat) : term57 m n p q.
Proof. exact (@lem1276888 m n p q). Qed.
Lemma lem1276890 (m : nat) (n : nat) (p : nat) (q : nat) : (term57 m n p q) = (term58 m n p q).
Proof. exact (eq_refl (term57 m n p q)). Qed.
Lemma lem1276892 (m : nat) : term63 m.
Proof. exact (@lem1259719 m). Qed.
Lemma lem1276893 (m : nat) : (term63 m) = (term64 m).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem1276894 (m : nat) : term64 m.
Proof. exact (EQ_MP (@lem1276893 m) (@lem1276892 m)). Qed.
Lemma lem1276895 (m : nat) (n : nat) : term65 m n.
Proof. exact (@lem1276894 m n). Qed.
Lemma lem1276896 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem1276897 (m : nat) (n : nat) : term66 m n.
Proof. exact (EQ_MP (@lem1276896 m n) (@lem1276895 m n)). Qed.
Lemma lem1276898 (m : nat) (n : nat) (p : nat) : term67 m n p.
Proof. exact (@lem1276897 m n p). Qed.
Lemma lem1276899 (m : nat) (n : nat) (p : nat) : (term67 m n p) = (term68 m n p).
Proof. exact (eq_refl (term67 m n p)). Qed.
Lemma lem1276900 (m : nat) (n : nat) (p : nat) : term68 m n p.
Proof. exact (EQ_MP (@lem1276899 m n p) (@lem1276898 m n p)). Qed.
Lemma lem1276901 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem1276902 (m : nat) (h1 : term69) : term70 m.
Proof. exact (@lem1276901 h1 m). Qed.
Lemma lem1276903 (m : nat) : (term70 m) = (term71 m).
Proof. exact (eq_refl (term70 m)). Qed.
Lemma lem1276904 (m : nat) (h1 : term69) : term71 m.
Proof. exact (EQ_MP (@lem1276903 m) (@lem1276902 m h1)). Qed.
Lemma lem1276905 (m : nat) (n : nat) (h1 : term69) : term72 m n.
Proof. exact (@lem1276904 m h1 n). Qed.
Lemma lem1276906 (n : nat) (m : nat) : (term72 m n) = (term73 n m).
Proof. exact (eq_refl (term72 m n)). Qed.
Lemma lem1276907 (n : nat) (m : nat) (h1 : term69) : term73 n m.
Proof. exact (EQ_MP (@lem1276906 n m) (@lem1276905 m n h1)). Qed.
Lemma lem1276908 (n : nat) (m : nat) (p : nat) (h1 : term69) : term74 n m p.
Proof. exact (@lem1276907 n m h1 p). Qed.
Lemma lem1276909 (n : nat) (m : nat) (p : nat) : (term74 n m p) = (term75 n m p).
Proof. exact (eq_refl (term74 n m p)). Qed.
Lemma lem1276910 (n : nat) (m : nat) (p : nat) (h1 : term69) : term75 n m p.
Proof. exact (EQ_MP (@lem1276909 n m p) (@lem1276908 n m p h1)). Qed.
Lemma lem1276911 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1276912 (p : nat) (m : nat) (n : nat) (h1 : term69) (h2 : Peano.le m n) : term76 n m p.
Proof. exact (@lem1276910 n m p h1 (@lem1276911 m n h2)). Qed.
Lemma lem1276913 (m : nat) (n : nat) (h1 : term69) (h2 : Peano.le m n) : term77 n m.
Proof. exact (fun p : nat => @lem1276912 p m n h1 h2). Qed.
Lemma lem1276914 (n : nat) (m : nat) (h1 : term69) : term78 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1276913 m n h1 h0). Qed.
Lemma lem1276915 (m : nat) (h1 : term69) : term79 m.
Proof. exact (fun n : nat => @lem1276914 n m h1). Qed.
Lemma lem1276916 (h1 : term69) : term80.
Proof. exact (fun m : nat => @lem1276915 m h1). Qed.
Lemma lem1276917 : term81.
Proof. exact (fun h0 : term69 => @lem1276916 h0). Qed.
Lemma lem1276918 : term80.
Proof. exact (@lem1276917 (@lem272809)). Qed.
Lemma lem1276919 (m : nat) : term82 m.
Proof. exact (@lem1276918 m). Qed.
Lemma lem1276920 (m : nat) : (term82 m) = (term79 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem1276921 (m : nat) : term79 m.
Proof. exact (EQ_MP (@lem1276920 m) (@lem1276919 m)). Qed.
Lemma lem1276922 (m : nat) (n : nat) : term83 m n.
Proof. exact (@lem1276921 m n). Qed.
Lemma lem1276923 (n : nat) (m : nat) : (term83 m n) = (term78 n m).
Proof. exact (eq_refl (term83 m n)). Qed.
Lemma lem1276926 (n : nat) (m : nat) : term78 n m.
Proof. exact (EQ_MP (@lem1276923 n m) (@lem1276922 m n)). Qed.
Lemma lem1276927 (n : nat) (m : nat) (p : nat) : term84 n m p.
Proof. exact (@lem1276926 (term85 m n p) (term49 m p)). Qed.
Lemma lem1276928 (n : nat) (m : nat) (p : nat) : term86 n m p.
Proof. exact (@lem1276927 n m p (@lem1276900 m n p)). Qed.
Lemma lem1276929 (n : nat) (m : nat) : term87 n m.
Proof. exact (fun p : nat => @lem1276928 n m p). Qed.
Lemma lem1276930 (n : nat) : term88 n.
Proof. exact (fun m : nat => @lem1276929 n m). Qed.
Lemma lem1276931 : term89.
Proof. exact (fun n : nat => @lem1276930 n). Qed.
Lemma lem1276932 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem1276933 (n : nat) (h1 : term89) : term90 n.
Proof. exact (@lem1276932 h1 n). Qed.
Lemma lem1276934 (n : nat) : (term90 n) = (term88 n).
Proof. exact (eq_refl (term90 n)). Qed.
Lemma lem1276935 (n : nat) (h1 : term89) : term88 n.
Proof. exact (EQ_MP (@lem1276934 n) (@lem1276933 n h1)). Qed.
Lemma lem1276936 (n : nat) (m : nat) (h1 : term89) : term91 n m.
Proof. exact (@lem1276935 n h1 m). Qed.
Lemma lem1276937 (n : nat) (m : nat) : (term91 n m) = (term87 n m).
Proof. exact (eq_refl (term91 n m)). Qed.
Lemma lem1276938 (n : nat) (m : nat) (h1 : term89) : term87 n m.
Proof. exact (EQ_MP (@lem1276937 n m) (@lem1276936 n m h1)). Qed.
Lemma lem1276939 (n : nat) (m : nat) (p : nat) (h1 : term89) : term92 n m p.
Proof. exact (@lem1276938 n m h1 p). Qed.
Lemma lem1276940 (n : nat) (m : nat) (p : nat) : (term92 n m p) = (term86 n m p).
Proof. exact (eq_refl (term92 n m p)). Qed.
Lemma lem1276941 (n : nat) (m : nat) (p : nat) (h1 : term89) : term86 n m p.
Proof. exact (EQ_MP (@lem1276940 n m p) (@lem1276939 n m p h1)). Qed.
Lemma lem1276942 (n : nat) (m : nat) (p : nat) (p' : nat) (h1 : term89) : term93 n m p p'.
Proof. exact (@lem1276941 n m p h1 p'). Qed.
Lemma lem1276943 (n : nat) (m : nat) (p : nat) (p' : nat) : (term93 n m p p') = (term94 n m p p').
Proof. exact (eq_refl (term93 n m p p')). Qed.
Lemma lem1276944 (n : nat) (m : nat) (p : nat) (p' : nat) (h1 : term89) : term94 n m p p'.
Proof. exact (EQ_MP (@lem1276943 n m p p') (@lem1276942 n m p p' h1)). Qed.
Lemma lem1276945 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term95 m n p p') : term95 m n p p'.
Proof. exact (h1). Qed.
Lemma lem1276946 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term89) (h2 : term95 m n p p') : term96 m p p'.
Proof. exact (@lem1276944 n m p p' h1 (@lem1276945 m n p p' h2)). Qed.
Lemma lem1276947 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term95 m n p p') : term97 m p p'.
Proof. exact (fun h0 : term89 => @lem1276946 m n p p' h0 h1). Qed.
Lemma lem1276948 (m : nat) (p : nat) (p' : nat) (h1 : term98 m p p') : term98 m p p'.
Proof. exact (h1). Qed.
Lemma lem1276949 (m : nat) (p : nat) (p' : nat) (h1 : term98 m p p') : term97 m p p'.
Proof. exact (ex_elim (@lem1276948 m p p' h1) (fun n : nat => fun h0 : term99 m p p' n => @lem1276947 m n p p' h0)). Qed.
Lemma lem1276950 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem1276951 (m : nat) (p : nat) (p' : nat) (h1 : term89) (h2 : term98 m p p') : term96 m p p'.
Proof. exact (@lem1276949 m p p' h2 (@lem1276950 h1)). Qed.
Lemma lem1276952 (m : nat) (p : nat) (p' : nat) (h1 : term89) : term100 m p p'.
Proof. exact (fun h0 : term98 m p p' => @lem1276951 m p p' h1 h0). Qed.
Lemma lem1276953 (m : nat) (p : nat) (h1 : term89) : term101 m p.
Proof. exact (fun p' : nat => @lem1276952 m p p' h1). Qed.
Lemma lem1276954 (m : nat) (h1 : term89) : term102 m.
Proof. exact (fun p : nat => @lem1276953 m p h1). Qed.
Lemma lem1276955 (h1 : term89) : term103.
Proof. exact (fun m : nat => @lem1276954 m h1). Qed.
Lemma lem1276956 : term104.
Proof. exact (fun h0 : term89 => @lem1276955 h0). Qed.
Lemma lem1276957 : term103.
Proof. exact (@lem1276956 (@lem1276931)). Qed.
Lemma lem1276958 (m : nat) : term105 m.
Proof. exact (@lem1276957 m). Qed.
Lemma lem1276959 (m : nat) : (term105 m) = (term102 m).
Proof. exact (eq_refl (term105 m)). Qed.
Lemma lem1276960 (m : nat) : term102 m.
Proof. exact (EQ_MP (@lem1276959 m) (@lem1276958 m)). Qed.
Lemma lem1276961 (m : nat) (p : nat) : term106 m p.
Proof. exact (@lem1276960 m p). Qed.
Lemma lem1276962 (m : nat) (p : nat) : (term106 m p) = (term101 m p).
Proof. exact (eq_refl (term106 m p)). Qed.
Lemma lem1276963 (m : nat) (p : nat) : term101 m p.
Proof. exact (EQ_MP (@lem1276962 m p) (@lem1276961 m p)). Qed.
Lemma lem1276964 (m : nat) (p : nat) (p' : nat) : term107 m p p'.
Proof. exact (@lem1276963 m p p'). Qed.
Lemma lem1276965 (m : nat) (p : nat) (p' : nat) : (term107 m p p') = (term100 m p p').
Proof. exact (eq_refl (term107 m p p')). Qed.
Lemma lem1276967 (m : nat) : term46 m.
Proof. exact (@lem1244997 m). Qed.
Lemma lem1276968 (m : nat) : (term46 m) = (term47 m).
Proof. exact (eq_refl (term46 m)). Qed.
Lemma lem1276969 (m : nat) : term47 m.
Proof. exact (EQ_MP (@lem1276968 m) (@lem1276967 m)). Qed.
Lemma lem1276970 (m : nat) (n : nat) : term48 m n.
Proof. exact (@lem1276969 m n). Qed.
Lemma lem1276971 (n : nat) (m : nat) : (term48 m n) = ((term49 m n) = (term49 n m)).
Proof. exact (eq_refl (term48 m n)). Qed.
Lemma lem1276973 (h1 : term50) : term50.
Proof. exact (h1). Qed.
Lemma lem1276974 (m : nat) (h1 : term50) : term51 m.
Proof. exact (@lem1276973 h1 m). Qed.
Lemma lem1276975 (m : nat) : (term51 m) = (term52 m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem1276976 (m : nat) (h1 : term50) : term52 m.
Proof. exact (EQ_MP (@lem1276975 m) (@lem1276974 m h1)). Qed.
Lemma lem1276977 (m : nat) (n : nat) (h1 : term50) : term53 m n.
Proof. exact (@lem1276976 m h1 n). Qed.
Lemma lem1276978 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (eq_refl (term53 m n)). Qed.
Lemma lem1276979 (m : nat) (n : nat) (h1 : term50) : term54 m n.
Proof. exact (EQ_MP (@lem1276978 m n) (@lem1276977 m n h1)). Qed.
Lemma lem1276980 (m : nat) (n : nat) (p : nat) (h1 : term50) : term55 m n p.
Proof. exact (@lem1276979 m n h1 p). Qed.
Lemma lem1276981 (m : nat) (n : nat) (p : nat) : (term55 m n p) = (term56 m n p).
Proof. exact (eq_refl (term55 m n p)). Qed.
Lemma lem1276982 (m : nat) (n : nat) (p : nat) (h1 : term50) : term56 m n p.
Proof. exact (EQ_MP (@lem1276981 m n p) (@lem1276980 m n p h1)). Qed.
Lemma lem1276983 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term50) : term57 m n p q.
Proof. exact (@lem1276982 m n p h1 q). Qed.
Lemma lem1276984 (m : nat) (n : nat) (p : nat) (q : nat) : (term57 m n p q) = (term58 m n p q).
Proof. exact (eq_refl (term57 m n p q)). Qed.
Lemma lem1276985 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term50) : term58 m n p q.
Proof. exact (EQ_MP (@lem1276984 m n p q) (@lem1276983 m n p q h1)). Qed.
Lemma lem1276986 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term59 m p n q) : term59 m p n q.
Proof. exact (h1). Qed.
Lemma lem1276987 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term50) (h2 : term59 m p n q) : term60 m n p q.
Proof. exact (@lem1276985 m n p q h1 (@lem1276986 m p n q h2)). Qed.
Lemma lem1276988 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term59 m p n q) : term61 m n p q.
Proof. exact (fun h0 : term50 => @lem1276987 m p n q h0 h1). Qed.
Lemma lem1276989 (h1 : term50) : term50.
Proof. exact (h1). Qed.
Lemma lem1276990 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term50) (h2 : term59 m p n q) : term60 m n p q.
Proof. exact (@lem1276988 m p n q h2 (@lem1276989 h1)). Qed.
Lemma lem1276991 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term50) : term58 m n p q.
Proof. exact (fun h0 : term59 m p n q => @lem1276990 m p n q h1 h0). Qed.
Lemma lem1276992 (m : nat) (n : nat) (p : nat) (h1 : term50) : term56 m n p.
Proof. exact (fun q : nat => @lem1276991 m n p q h1). Qed.
Lemma lem1276993 (m : nat) (n : nat) (h1 : term50) : term54 m n.
Proof. exact (fun p : nat => @lem1276992 m n p h1). Qed.
Lemma lem1276994 (m : nat) (h1 : term50) : term52 m.
Proof. exact (fun n : nat => @lem1276993 m n h1). Qed.
Lemma lem1276995 (h1 : term50) : term50.
Proof. exact (fun m : nat => @lem1276994 m h1). Qed.
Lemma lem1276996 : term62.
Proof. exact (fun h0 : term50 => @lem1276995 h0). Qed.
Lemma lem1276997 : term50.
Proof. exact (@lem1276996 (@lem101399)). Qed.
Lemma lem1276998 (m : nat) : term51 m.
Proof. exact (@lem1276997 m). Qed.
Lemma lem1276999 (m : nat) : (term51 m) = (term52 m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem1277000 (m : nat) : term52 m.
Proof. exact (EQ_MP (@lem1276999 m) (@lem1276998 m)). Qed.
Lemma lem1277001 (m : nat) (n : nat) : term53 m n.
Proof. exact (@lem1277000 m n). Qed.
Lemma lem1277002 (m : nat) (n : nat) : (term53 m n) = (term54 m n).
Proof. exact (eq_refl (term53 m n)). Qed.
Lemma lem1277003 (m : nat) (n : nat) : term54 m n.
Proof. exact (EQ_MP (@lem1277002 m n) (@lem1277001 m n)). Qed.
Lemma lem1277004 (m : nat) (n : nat) (p : nat) : term55 m n p.
Proof. exact (@lem1277003 m n p). Qed.
Lemma lem1277005 (m : nat) (n : nat) (p : nat) : (term55 m n p) = (term56 m n p).
Proof. exact (eq_refl (term55 m n p)). Qed.
Lemma lem1277006 (m : nat) (n : nat) (p : nat) : term56 m n p.
Proof. exact (EQ_MP (@lem1277005 m n p) (@lem1277004 m n p)). Qed.
Lemma lem1277007 (m : nat) (n : nat) (p : nat) (q : nat) : term57 m n p q.
Proof. exact (@lem1277006 m n p q). Qed.
Lemma lem1277008 (m : nat) (n : nat) (p : nat) (q : nat) : (term57 m n p q) = (term58 m n p q).
Proof. exact (eq_refl (term57 m n p q)). Qed.
Lemma lem1277010 (m : nat) : term63 m.
Proof. exact (@lem1259719 m). Qed.
Lemma lem1277011 (m : nat) : (term63 m) = (term64 m).
Proof. exact (eq_refl (term63 m)). Qed.
Lemma lem1277012 (m : nat) : term64 m.
Proof. exact (EQ_MP (@lem1277011 m) (@lem1277010 m)). Qed.
Lemma lem1277013 (m : nat) (n : nat) : term65 m n.
Proof. exact (@lem1277012 m n). Qed.
Lemma lem1277014 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem1277015 (m : nat) (n : nat) : term66 m n.
Proof. exact (EQ_MP (@lem1277014 m n) (@lem1277013 m n)). Qed.
Lemma lem1277016 (m : nat) (n : nat) (p : nat) : term67 m n p.
Proof. exact (@lem1277015 m n p). Qed.
Lemma lem1277017 (m : nat) (n : nat) (p : nat) : (term67 m n p) = (term68 m n p).
Proof. exact (eq_refl (term67 m n p)). Qed.
Lemma lem1277018 (m : nat) (n : nat) (p : nat) : term68 m n p.
Proof. exact (EQ_MP (@lem1277017 m n p) (@lem1277016 m n p)). Qed.
Lemma lem1277019 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem1277020 (m : nat) (h1 : term69) : term70 m.
Proof. exact (@lem1277019 h1 m). Qed.
Lemma lem1277021 (m : nat) : (term70 m) = (term71 m).
Proof. exact (eq_refl (term70 m)). Qed.
Lemma lem1277022 (m : nat) (h1 : term69) : term71 m.
Proof. exact (EQ_MP (@lem1277021 m) (@lem1277020 m h1)). Qed.
Lemma lem1277023 (m : nat) (n : nat) (h1 : term69) : term72 m n.
Proof. exact (@lem1277022 m h1 n). Qed.
Lemma lem1277024 (n : nat) (m : nat) : (term72 m n) = (term73 n m).
Proof. exact (eq_refl (term72 m n)). Qed.
Lemma lem1277025 (n : nat) (m : nat) (h1 : term69) : term73 n m.
Proof. exact (EQ_MP (@lem1277024 n m) (@lem1277023 m n h1)). Qed.
Lemma lem1277026 (n : nat) (m : nat) (p : nat) (h1 : term69) : term74 n m p.
Proof. exact (@lem1277025 n m h1 p). Qed.
Lemma lem1277027 (n : nat) (m : nat) (p : nat) : (term74 n m p) = (term75 n m p).
Proof. exact (eq_refl (term74 n m p)). Qed.
Lemma lem1277028 (n : nat) (m : nat) (p : nat) (h1 : term69) : term75 n m p.
Proof. exact (EQ_MP (@lem1277027 n m p) (@lem1277026 n m p h1)). Qed.
Lemma lem1277029 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1277030 (p : nat) (m : nat) (n : nat) (h1 : term69) (h2 : Peano.le m n) : term76 n m p.
Proof. exact (@lem1277028 n m p h1 (@lem1277029 m n h2)). Qed.
Lemma lem1277031 (m : nat) (n : nat) (h1 : term69) (h2 : Peano.le m n) : term77 n m.
Proof. exact (fun p : nat => @lem1277030 p m n h1 h2). Qed.
Lemma lem1277032 (n : nat) (m : nat) (h1 : term69) : term78 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1277031 m n h1 h0). Qed.
Lemma lem1277033 (m : nat) (h1 : term69) : term79 m.
Proof. exact (fun n : nat => @lem1277032 n m h1). Qed.
Lemma lem1277034 (h1 : term69) : term80.
Proof. exact (fun m : nat => @lem1277033 m h1). Qed.
Lemma lem1277035 : term81.
Proof. exact (fun h0 : term69 => @lem1277034 h0). Qed.
Lemma lem1277036 : term80.
Proof. exact (@lem1277035 (@lem272809)). Qed.
Lemma lem1277037 (m : nat) : term82 m.
Proof. exact (@lem1277036 m). Qed.
Lemma lem1277038 (m : nat) : (term82 m) = (term79 m).
Proof. exact (eq_refl (term82 m)). Qed.
Lemma lem1277039 (m : nat) : term79 m.
Proof. exact (EQ_MP (@lem1277038 m) (@lem1277037 m)). Qed.
Lemma lem1277040 (m : nat) (n : nat) : term83 m n.
Proof. exact (@lem1277039 m n). Qed.
Lemma lem1277041 (n : nat) (m : nat) : (term83 m n) = (term78 n m).
Proof. exact (eq_refl (term83 m n)). Qed.
Lemma lem1277044 (n : nat) (m : nat) : term78 n m.
Proof. exact (EQ_MP (@lem1277041 n m) (@lem1277040 m n)). Qed.
Lemma lem1277045 (n : nat) (m : nat) (p : nat) : term84 n m p.
Proof. exact (@lem1277044 (term85 m n p) (term49 m p)). Qed.
Lemma lem1277046 (n : nat) (m : nat) (p : nat) : term86 n m p.
Proof. exact (@lem1277045 n m p (@lem1277018 m n p)). Qed.
Lemma lem1277047 (n : nat) (m : nat) : term87 n m.
Proof. exact (fun p : nat => @lem1277046 n m p). Qed.
Lemma lem1277048 (n : nat) : term88 n.
Proof. exact (fun m : nat => @lem1277047 n m). Qed.
Lemma lem1277049 : term89.
Proof. exact (fun n : nat => @lem1277048 n). Qed.
Lemma lem1277050 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem1277051 (n : nat) (h1 : term89) : term90 n.
Proof. exact (@lem1277050 h1 n). Qed.
Lemma lem1277052 (n : nat) : (term90 n) = (term88 n).
Proof. exact (eq_refl (term90 n)). Qed.
Lemma lem1277053 (n : nat) (h1 : term89) : term88 n.
Proof. exact (EQ_MP (@lem1277052 n) (@lem1277051 n h1)). Qed.
Lemma lem1277054 (n : nat) (m : nat) (h1 : term89) : term91 n m.
Proof. exact (@lem1277053 n h1 m). Qed.
Lemma lem1277055 (n : nat) (m : nat) : (term91 n m) = (term87 n m).
Proof. exact (eq_refl (term91 n m)). Qed.
Lemma lem1277056 (n : nat) (m : nat) (h1 : term89) : term87 n m.
Proof. exact (EQ_MP (@lem1277055 n m) (@lem1277054 n m h1)). Qed.
Lemma lem1277057 (n : nat) (m : nat) (p : nat) (h1 : term89) : term92 n m p.
Proof. exact (@lem1277056 n m h1 p). Qed.
Lemma lem1277058 (n : nat) (m : nat) (p : nat) : (term92 n m p) = (term86 n m p).
Proof. exact (eq_refl (term92 n m p)). Qed.
Lemma lem1277059 (n : nat) (m : nat) (p : nat) (h1 : term89) : term86 n m p.
Proof. exact (EQ_MP (@lem1277058 n m p) (@lem1277057 n m p h1)). Qed.
Lemma lem1277060 (n : nat) (m : nat) (p : nat) (p' : nat) (h1 : term89) : term93 n m p p'.
Proof. exact (@lem1277059 n m p h1 p'). Qed.
Lemma lem1277061 (n : nat) (m : nat) (p : nat) (p' : nat) : (term93 n m p p') = (term94 n m p p').
Proof. exact (eq_refl (term93 n m p p')). Qed.
Lemma lem1277062 (n : nat) (m : nat) (p : nat) (p' : nat) (h1 : term89) : term94 n m p p'.
Proof. exact (EQ_MP (@lem1277061 n m p p') (@lem1277060 n m p p' h1)). Qed.
Lemma lem1277063 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term95 m n p p') : term95 m n p p'.
Proof. exact (h1). Qed.
Lemma lem1277064 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term89) (h2 : term95 m n p p') : term96 m p p'.
Proof. exact (@lem1277062 n m p p' h1 (@lem1277063 m n p p' h2)). Qed.
Lemma lem1277065 (m : nat) (n : nat) (p : nat) (p' : nat) (h1 : term95 m n p p') : term97 m p p'.
Proof. exact (fun h0 : term89 => @lem1277064 m n p p' h0 h1). Qed.
Lemma lem1277066 (m : nat) (p : nat) (p' : nat) (h1 : term98 m p p') : term98 m p p'.
Proof. exact (h1). Qed.
Lemma lem1277067 (m : nat) (p : nat) (p' : nat) (h1 : term98 m p p') : term97 m p p'.
Proof. exact (ex_elim (@lem1277066 m p p' h1) (fun n : nat => fun h0 : term99 m p p' n => @lem1277065 m n p p' h0)). Qed.
Lemma lem1277068 (h1 : term89) : term89.
Proof. exact (h1). Qed.
Lemma lem1277069 (m : nat) (p : nat) (p' : nat) (h1 : term89) (h2 : term98 m p p') : term96 m p p'.
Proof. exact (@lem1277067 m p p' h2 (@lem1277068 h1)). Qed.
Lemma lem1277070 (m : nat) (p : nat) (p' : nat) (h1 : term89) : term100 m p p'.
Proof. exact (fun h0 : term98 m p p' => @lem1277069 m p p' h1 h0). Qed.
Lemma lem1277071 (m : nat) (p : nat) (h1 : term89) : term101 m p.
Proof. exact (fun p' : nat => @lem1277070 m p p' h1). Qed.
Lemma lem1277072 (m : nat) (h1 : term89) : term102 m.
Proof. exact (fun p : nat => @lem1277071 m p h1). Qed.
Lemma lem1277073 (h1 : term89) : term103.
Proof. exact (fun m : nat => @lem1277072 m h1). Qed.
Lemma lem1277074 : term104.
Proof. exact (fun h0 : term89 => @lem1277073 h0). Qed.
Lemma lem1277075 : term103.
Proof. exact (@lem1277074 (@lem1277049)). Qed.
Lemma lem1277076 (m : nat) : term105 m.
Proof. exact (@lem1277075 m). Qed.
Lemma lem1277077 (m : nat) : (term105 m) = (term102 m).
Proof. exact (eq_refl (term105 m)). Qed.
Lemma lem1277078 (m : nat) : term102 m.
Proof. exact (EQ_MP (@lem1277077 m) (@lem1277076 m)). Qed.
Lemma lem1277079 (m : nat) (p : nat) : term106 m p.
Proof. exact (@lem1277078 m p). Qed.
Lemma lem1277080 (m : nat) (p : nat) : (term106 m p) = (term101 m p).
Proof. exact (eq_refl (term106 m p)). Qed.
Lemma lem1277081 (m : nat) (p : nat) : term101 m p.
Proof. exact (EQ_MP (@lem1277080 m p) (@lem1277079 m p)). Qed.
Lemma lem1277082 (m : nat) (p : nat) (p' : nat) : term107 m p p'.
Proof. exact (@lem1277081 m p p'). Qed.
Lemma lem1277083 (m : nat) (p : nat) (p' : nat) : (term107 m p p') = (term100 m p p').
Proof. exact (eq_refl (term107 m p p')). Qed.
Lemma lem1277085 (h1 : term29) : term29.
Proof. exact (h1). Qed.
Lemma lem1277086 (m : nat) (h1 : term29) : term30 m.
Proof. exact (@lem1277085 h1 m). Qed.
Lemma lem1277087 (m : nat) : (term30 m) = (term31 m).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem1277088 (m : nat) (h1 : term29) : term31 m.
Proof. exact (EQ_MP (@lem1277087 m) (@lem1277086 m h1)). Qed.
Lemma lem1277089 (m : nat) (n : nat) (h1 : term29) : term32 m n.
Proof. exact (@lem1277088 m h1 n). Qed.
Lemma lem1277090 (n : nat) (m : nat) : (term32 m n) = (term33 n m).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem1277091 (n : nat) (m : nat) (h1 : term29) : term33 n m.
Proof. exact (EQ_MP (@lem1277090 n m) (@lem1277089 m n h1)). Qed.
Lemma lem1277092 (n : nat) (m : nat) (p : nat) (h1 : term29) : term34 n m p.
Proof. exact (@lem1277091 n m h1 p). Qed.
Lemma lem1277093 (n : nat) (m : nat) (p : nat) : (term34 n m p) = (term35 n m p).
Proof. exact (eq_refl (term34 n m p)). Qed.
Lemma lem1277094 (n : nat) (m : nat) (p : nat) (h1 : term29) : term35 n m p.
Proof. exact (EQ_MP (@lem1277093 n m p) (@lem1277092 n m p h1)). Qed.
Lemma lem1277095 (m : nat) (n : nat) (p : nat) (h1 : term36 m n p) : term36 m n p.
Proof. exact (h1). Qed.
Lemma lem1277096 (m : nat) (n : nat) (p : nat) (h1 : term29) (h2 : term36 m n p) : Peano.le m p.
Proof. exact (@lem1277094 n m p h1 (@lem1277095 m n p h2)). Qed.
Lemma lem1277097 (m : nat) (n : nat) (p : nat) (h1 : term36 m n p) : term37 m p.
Proof. exact (fun h0 : term29 => @lem1277096 m n p h0 h1). Qed.
Lemma lem1277098 (m : nat) (p : nat) (h1 : term38 m p) : term38 m p.
Proof. exact (h1). Qed.
Lemma lem1277099 (m : nat) (p : nat) (h1 : term38 m p) : term37 m p.
Proof. exact (ex_elim (@lem1277098 m p h1) (fun n : nat => fun h0 : term39 m p n => @lem1277097 m n p h0)). Qed.
Lemma lem1277100 (h1 : term29) : term29.
Proof. exact (h1). Qed.
Lemma lem1277101 (m : nat) (p : nat) (h1 : term29) (h2 : term38 m p) : Peano.le m p.
Proof. exact (@lem1277099 m p h2 (@lem1277100 h1)). Qed.
Lemma lem1277102 (m : nat) (p : nat) (h1 : term29) : term40 m p.
Proof. exact (fun h0 : term38 m p => @lem1277101 m p h1 h0). Qed.
Lemma lem1277103 (m : nat) (h1 : term29) : term41 m.
Proof. exact (fun p : nat => @lem1277102 m p h1). Qed.
Lemma lem1277104 (h1 : term29) : term42.
Proof. exact (fun m : nat => @lem1277103 m h1). Qed.
Lemma lem1277105 : term43.
Proof. exact (fun h0 : term29 => @lem1277104 h0). Qed.
Lemma lem1277106 : term42.
Proof. exact (@lem1277105 (@lem93743)). Qed.
Lemma lem1277107 (m : nat) : term44 m.
Proof. exact (@lem1277106 m). Qed.
Lemma lem1277108 (m : nat) : (term44 m) = (term41 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem1277109 (m : nat) : term41 m.
Proof. exact (EQ_MP (@lem1277108 m) (@lem1277107 m)). Qed.
Lemma lem1277110 (m : nat) (p : nat) : term45 m p.
Proof. exact (@lem1277109 m p). Qed.
Lemma lem1277111 (m : nat) (p : nat) : (term45 m p) = (term40 m p).
Proof. exact (eq_refl (term45 m p)). Qed.
Lemma lem1277113 (n : nat) : term108 n.
Proof. exact (@lem1244783 n). Qed.
Lemma lem1277114 (n : nat) : (term108 n) = ((term109 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term108 n)). Qed.
Lemma lem1277150 (h1 : term110) : term110.
Proof. exact (h1). Qed.
Lemma lem1277151 (P : type1606) (h1 : term110) : term111 P.
Proof. exact (@lem1277150 h1 P). Qed.
Lemma lem1277152 (P : type1606) : (term111 P) = (term112 P).
Proof. exact (eq_refl (term111 P)). Qed.
Lemma lem1277153 (P : type1606) (h1 : term110) : term112 P.
Proof. exact (EQ_MP (@lem1277152 P) (@lem1277151 P h1)). Qed.
Lemma lem1277154 (P : type1606) (A : nat) (h1 : term110) : term113 P A.
Proof. exact (@lem1277153 P h1 A). Qed.
Lemma lem1277155 (A : nat) (P : type1606) : (term113 P A) = (term114 A P).
Proof. exact (eq_refl (term113 P A)). Qed.
Lemma lem1277156 (A : nat) (P : type1606) (h1 : term110) : term114 A P.
Proof. exact (EQ_MP (@lem1277155 A P) (@lem1277154 P A h1)). Qed.
Lemma lem1277157 (A : nat) (P : type1606) (B : nat) (h1 : term110) : term115 A P B.
Proof. exact (@lem1277156 A P h1 B). Qed.
Lemma lem1277158 (A : nat) (B : nat) (P : type1606) : (term115 A P B) = (term116 A B P).
Proof. exact (eq_refl (term115 A P B)). Qed.
Lemma lem1277159 (A : nat) (B : nat) (P : type1606) (h1 : term110) : term116 A B P.
Proof. exact (EQ_MP (@lem1277158 A B P) (@lem1277157 A P B h1)). Qed.
Lemma lem1277160 (P : type1606) (A : nat) (B : nat) (h1 : term117 P A B) : term117 P A B.
Proof. exact (h1). Qed.
Lemma lem1277161 (P : type1606) (A : nat) (B : nat) (h1 : term110) (h2 : term117 P A B) : term118 P.
Proof. exact (@lem1277159 A B P h1 (@lem1277160 P A B h2)). Qed.
Lemma lem1277162 (P : type1606) (A : nat) (B : nat) (h1 : term117 P A B) : term119 P.
Proof. exact (fun h0 : term110 => @lem1277161 P A B h0 h1). Qed.
Lemma lem1277163 (P : type1606) (A : nat) (h1 : term120 P A) : term120 P A.
Proof. exact (h1). Qed.
Lemma lem1277164 (P : type1606) (A : nat) (h1 : term120 P A) : term119 P.
Proof. exact (ex_elim (@lem1277163 P A h1) (fun B : nat => fun h0 : term121 P A B => @lem1277162 P A B h0)). Qed.
Lemma lem1277165 (P : type1606) (h1 : term122 P) : term122 P.
Proof. exact (h1). Qed.
Lemma lem1277166 (P : type1606) (h1 : term122 P) : term119 P.
Proof. exact (ex_elim (@lem1277165 P h1) (fun A : nat => fun h0 : term123 P A => @lem1277164 P A h0)). Qed.
Lemma lem1277167 (h1 : term110) : term110.
Proof. exact (h1). Qed.
Lemma lem1277168 (P : type1606) (h1 : term110) (h2 : term122 P) : term118 P.
Proof. exact (@lem1277166 P h2 (@lem1277167 h1)). Qed.
Lemma lem1277169 (P : type1606) (h1 : term110) : term124 P.
Proof. exact (fun h0 : term122 P => @lem1277168 P h1 h0). Qed.
Lemma lem1277170 (h1 : term110) : term125.
Proof. exact (fun P : type1606 => @lem1277169 P h1). Qed.
Lemma lem1277171 : term126.
Proof. exact (fun h0 : term110 => @lem1277170 h0). Qed.
Lemma lem1277172 : term125.
Proof. exact (@lem1277171 (@lem1261658)). Qed.
Lemma lem1277173 (P : type1606) : term127 P.
Proof. exact (@lem1277172 P). Qed.
Lemma lem1277174 (P : type1606) : (term127 P) = (term124 P).
Proof. exact (eq_refl (term127 P)). Qed.
Lemma lem1277176 (x : nadd) : term128 x.
Proof. exact (@lem1264303 x). Qed.
Lemma lem1277177 (x : nadd) : (term128 x) = (term129 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1277178 (x : nadd) : term129 x.
Proof. exact (EQ_MP (@lem1277177 x) (@lem1277176 x)). Qed.
Lemma lem1277179 (x : nadd) (D : nat) (h1 : term130 x D) : term130 x D.
Proof. exact (h1). Qed.
Lemma lem1277180 (x : nadd) : term131 x.
Proof. exact (@lem1267115 x). Qed.
Lemma lem1277181 (x : nadd) : (term131 x) = (term132 x).
Proof. exact (eq_refl (term131 x)). Qed.
Lemma lem1277182 (x : nadd) : term132 x.
Proof. exact (EQ_MP (@lem1277181 x) (@lem1277180 x)). Qed.
Lemma lem1277183 (x : nadd) (C : nat) (h1 : term133 x C) : term133 x C.
Proof. exact (h1). Qed.
Lemma lem1277184 (y : nadd) : term134 y.
Proof. exact (@lem1262851 y). Qed.
Lemma lem1277185 (y : nadd) : (term134 y) = (term135 y).
Proof. exact (eq_refl (term134 y)). Qed.
Lemma lem1277186 (y : nadd) : term135 y.
Proof. exact (EQ_MP (@lem1277185 y) (@lem1277184 y)). Qed.
Lemma lem1277187 (y : nadd) (B : nat) (h1 : term136 y B) : term136 y B.
Proof. exact (h1). Qed.
Lemma lem1277188 (r : nat -> nat) (h1 : (is_nadd r) = ((term137 r) = r)) : (is_nadd r) = ((term137 r) = r).
Proof. exact (h1). Qed.
Lemma lem1277189 (r : nat -> nat) (h1 : (is_nadd r) = ((term137 r) = r)) : ((term137 r) = r) = (is_nadd r).
Proof. exact (SYM (@lem1277188 r h1)). Qed.
Lemma lem1277190 (r : nat -> nat) (h1 : ((term137 r) = r) = (is_nadd r)) : ((term137 r) = r) = (is_nadd r).
Proof. exact (h1). Qed.
Lemma lem1277191 (r : nat -> nat) (h1 : ((term137 r) = r) = (is_nadd r)) : (is_nadd r) = ((term137 r) = r).
Proof. exact (SYM (@lem1277190 r h1)). Qed.
Lemma lem1277192 (r : nat -> nat) : ((is_nadd r) = ((term137 r) = r)) = (((term137 r) = r) = (is_nadd r)).
Proof. exact (prop_ext (fun h1 : (is_nadd r) = ((term137 r) = r) => @lem1277189 r h1) (fun h1 : ((term137 r) = r) = (is_nadd r) => @lem1277191 r h1)). Qed.
Lemma lem1277194 (x : nat -> nat) : term138 x.
Proof. exact (@lem1262615 x). Qed.
Lemma lem1277195 (x : nat -> nat) : (term138 x) = ((is_nadd x) = (term139 x)).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem1277197 (x : nadd) : term140 x.
Proof. exact (@lem1276766 x). Qed.
Lemma lem1277198 (x : nadd) : (term140 x) = (term141 x).
Proof. exact (eq_refl (term140 x)). Qed.
Lemma lem1277199 (x : nadd) : term141 x.
Proof. exact (EQ_MP (@lem1277198 x) (@lem1277197 x)). Qed.
Lemma lem1277200 (x : nadd) (y : nadd) : term142 x y.
Proof. exact (@lem1277199 x y). Qed.
Lemma lem1277201 (x : nadd) (y : nadd) : (term142 x y) = ((nadd_mul x y) = (term143 x y)).
Proof. exact (eq_refl (term142 x y)). Qed.
Lemma lem1277206 (x : nadd) (y : nadd) : (nadd_mul x y) = (term143 x y).
Proof. exact (EQ_MP (@lem1277201 x y) (@lem1277200 x y)). Qed.
Lemma lem1277207 : dest_nadd = dest_nadd.
Proof. exact (eq_refl dest_nadd). Qed.
Lemma lem1277208 (x : nadd) (y : nadd) : (term144 x y) = (term145 x y).
Proof. exact (MK_COMB (@lem1277207) (@lem1277206 x y)). Qed.
Lemma lem1277209 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem1277210 (x : nadd) (y : nadd) : (term146 x y) = (term147 x y).
Proof. exact (MK_COMB (@lem1277209) (@lem1277208 x y)). Qed.
Lemma lem1277211 (x : nadd) (y : nadd) : (term148 x y) = (term148 x y).
Proof. exact (eq_refl (term148 x y)). Qed.
Lemma lem1277212 (x : nadd) (y : nadd) : ((term144 x y) = (term148 x y)) = ((term145 x y) = (term148 x y)).
Proof. exact (MK_COMB (@lem1277210 x y) (@lem1277211 x y)). Qed.
Lemma lem1277214 (r : nat -> nat) : ((term137 r) = r) = (is_nadd r).
Proof. exact (EQ_MP (@lem1277192 r) (@lem1262760 r)). Qed.
Lemma lem1277215 (x : nadd) (y : nadd) : ((term145 x y) = (term148 x y)) = (term149 x y).
Proof. exact (@lem1277214 (term148 x y)). Qed.
Lemma lem1277217 (x : nat -> nat) : (is_nadd x) = (term139 x).
Proof. exact (EQ_MP (@lem1277195 x) (@lem1277194 x)). Qed.
Lemma lem1277218 (x : nadd) (y : nadd) : (term149 x y) = (term150 x y).
Proof. exact (@lem1277217 (term148 x y)). Qed.
Lemma lem1277232 {A B : Type'} (f : A -> B) (y : A) : (term151 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1277233 (f : nat -> nat) (y : nat) : (term152 f y) = (f y).
Proof. exact (@lem1277232 nat nat f y). Qed.
Lemma lem1277234 (x : nadd) (y : nadd) (n : nat) : (term153 x y n) = (term154 x y n).
Proof. exact (@lem1277233 (term148 x y) n). Qed.
Lemma lem1277235 (x : nadd) (y : nadd) (n : nat) : (term154 x y n) = (term155 x y n).
Proof. exact (eq_refl (term154 x y n)). Qed.
Lemma lem1277236 (x : nadd) (y : nadd) : (term156 x y) = (term148 x y).
Proof. exact (fun_ext (fun n : nat => @lem1277235 x y n)). Qed.
Lemma lem1277237 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1277238 (x : nadd) (y : nadd) (n : nat) : (term153 x y n) = (term154 x y n).
Proof. exact (MK_COMB (@lem1277236 x y) (@lem1277237 n)). Qed.
Lemma lem1277239 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1277240 (x : nadd) (y : nadd) (n : nat) : (term157 x y n) = (term158 x y n).
Proof. exact (MK_COMB (@lem1277239) (@lem1277238 x y n)). Qed.
Lemma lem1277241 (x : nadd) (y : nadd) (n : nat) : (term154 x y n) = (term155 x y n).
Proof. exact (eq_refl (term154 x y n)). Qed.
Lemma lem1277242 (x : nadd) (y : nadd) (n : nat) : ((term153 x y n) = (term154 x y n)) = ((term154 x y n) = (term155 x y n)).
Proof. exact (MK_COMB (@lem1277240 x y n) (@lem1277241 x y n)). Qed.
Lemma lem1277243 (x : nadd) (y : nadd) (n : nat) : (term154 x y n) = (term155 x y n).
Proof. exact (EQ_MP (@lem1277242 x y n) (@lem1277234 x y n)). Qed.
Lemma lem1277244 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem1277245 (m : nat) (x : nadd) (y : nadd) (n : nat) : (term159 m x y n) = (term160 m x y n).
Proof. exact (MK_COMB (@lem1277244 m) (@lem1277243 x y n)). Qed.
Lemma lem1277246 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1277247 (m : nat) (x : nadd) (y : nadd) (n : nat) : (term161 m x y n) = (term162 m x y n).
Proof. exact (MK_COMB (@lem1277246) (@lem1277245 m x y n)). Qed.
Lemma lem1277249 {A B : Type'} (f : A -> B) (y : A) : (term151 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1277250 (f : nat -> nat) (y : nat) : (term152 f y) = (f y).
Proof. exact (@lem1277249 nat nat f y). Qed.
Lemma lem1277251 (x : nadd) (y : nadd) (m : nat) : (term153 x y m) = (term154 x y m).
Proof. exact (@lem1277250 (term148 x y) m). Qed.
Lemma lem1277252 (x : nadd) (y : nadd) (n : nat) : (term154 x y n) = (term155 x y n).
Proof. exact (eq_refl (term154 x y n)). Qed.
Lemma lem1277253 (x : nadd) (y : nadd) : (term156 x y) = (term148 x y).
Proof. exact (fun_ext (fun n : nat => @lem1277252 x y n)). Qed.
Lemma lem1277254 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1277255 (x : nadd) (y : nadd) (m : nat) : (term153 x y m) = (term154 x y m).
Proof. exact (MK_COMB (@lem1277253 x y) (@lem1277254 m)). Qed.
Lemma lem1277256 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1277257 (x : nadd) (y : nadd) (m : nat) : (term157 x y m) = (term158 x y m).
Proof. exact (MK_COMB (@lem1277256) (@lem1277255 x y m)). Qed.
Lemma lem1277258 (x : nadd) (y : nadd) (m : nat) : (term154 x y m) = (term155 x y m).
Proof. exact (eq_refl (term154 x y m)). Qed.
Lemma lem1277259 (x : nadd) (y : nadd) (m : nat) : ((term153 x y m) = (term154 x y m)) = ((term154 x y m) = (term155 x y m)).
Proof. exact (MK_COMB (@lem1277257 x y m) (@lem1277258 x y m)). Qed.
Lemma lem1277260 (x : nadd) (y : nadd) (m : nat) : (term154 x y m) = (term155 x y m).
Proof. exact (EQ_MP (@lem1277259 x y m) (@lem1277251 x y m)). Qed.
Lemma lem1277261 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem1277262 (n : nat) (x : nadd) (y : nadd) (m : nat) : (term159 n x y m) = (term160 n x y m).
Proof. exact (MK_COMB (@lem1277261 n) (@lem1277260 x y m)). Qed.
Lemma lem1277263 (n : nat) (x : nadd) (y : nadd) (m : nat) : (term163 n x y m) = (term164 n x y m).
Proof. exact (MK_COMB (@lem1277247 m x y n) (@lem1277262 n x y m)). Qed.
Lemma lem1277264 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1277265 (n : nat) (x : nadd) (y : nadd) (m : nat) : (term165 n x y m) = (term166 n x y m).
Proof. exact (MK_COMB (@lem1277264) (@lem1277263 n x y m)). Qed.
Lemma lem1277266 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1277267 (n : nat) (x : nadd) (y : nadd) (m : nat) : (term167 n x y m) = (term168 n x y m).
Proof. exact (MK_COMB (@lem1277266) (@lem1277265 n x y m)). Qed.
Lemma lem1277268 (B : nat) (m : nat) (n : nat) : (term20 B m n) = (term20 B m n).
Proof. exact (eq_refl (term20 B m n)). Qed.
Lemma lem1277269 (x : nadd) (y : nadd) (B : nat) (m : nat) (n : nat) : (term169 x y B m n) = (term170 x y B m n).
Proof. exact (MK_COMB (@lem1277267 n x y m) (@lem1277268 B m n)). Qed.
Lemma lem1277270 (x : nadd) (y : nadd) (B : nat) (m : nat) : (term171 x y B m) = (term172 x y B m).
Proof. exact (fun_ext (fun n : nat => @lem1277269 x y B m n)). Qed.
Lemma lem1277271 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1277272 (x : nadd) (y : nadd) (B : nat) (m : nat) : (term173 x y B m) = (term174 x y B m).
Proof. exact (MK_COMB (@lem1277271) (@lem1277270 x y B m)). Qed.
Lemma lem1277277 (x : nadd) (y : nadd) (B : nat) : (term175 x y B) = (term176 x y B).
Proof. exact (fun_ext (fun m : nat => @lem1277272 x y B m)). Qed.
Lemma lem1277278 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1277279 (x : nadd) (y : nadd) (B : nat) : (term177 x y B) = (term178 x y B).
Proof. exact (MK_COMB (@lem1277278) (@lem1277277 x y B)). Qed.
Lemma lem1277284 (x : nadd) (y : nadd) : (term179 x y) = (term180 x y).
Proof. exact (fun_ext (fun B : nat => @lem1277279 x y B)). Qed.
Lemma lem1277285 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1277286 (x : nadd) (y : nadd) : (term150 x y) = (term181 x y).
Proof. exact (MK_COMB (@lem1277285) (@lem1277284 x y)). Qed.
Lemma lem1277291 (x : nadd) (y : nadd) : (term149 x y) = (term181 x y).
Proof. exact (TRANS (@lem1277218 x y) (@lem1277286 x y)). Qed.
Lemma lem1277292 (x : nadd) (y : nadd) : ((term145 x y) = (term148 x y)) = (term181 x y).
Proof. exact (TRANS (@lem1277215 x y) (@lem1277291 x y)). Qed.
Lemma lem1277293 (x : nadd) (y : nadd) : ((term144 x y) = (term148 x y)) = (term181 x y).
Proof. exact (TRANS (@lem1277212 x y) (@lem1277292 x y)). Qed.
Lemma lem1277294 (x : nadd) (y : nadd) : (term181 x y) = ((term144 x y) = (term148 x y)).
Proof. exact (SYM (@lem1277293 x y)). Qed.
Lemma lem1277296 (P : type1606) : term124 P.
Proof. exact (EQ_MP (@lem1277174 P) (@lem1277173 P)). Qed.
Lemma lem1277297 (x : nadd) (y : nadd) : term182 x y.
Proof. exact (@lem1277296 (term183 x y)). Qed.
Lemma lem1277298 (x : nadd) (y : nadd) : (term184 x y) = (term185 x y).
Proof. exact (eq_refl (term184 x y)). Qed.
Lemma lem1277299 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1277300 (x : nadd) (y : nadd) : (term186 x y) = (term187 x y).
Proof. exact (MK_COMB (@lem1277298 x y) (@lem1277299)). Qed.
Lemma lem1277301 (x : nadd) (y : nadd) : (term187 x y) = (term188 x y).
Proof. exact (eq_refl (term187 x y)). Qed.
Lemma lem1277302 (x : nadd) (y : nadd) : (term186 x y) = (term188 x y).
Proof. exact (TRANS (@lem1277300 x y) (@lem1277301 x y)). Qed.
Lemma lem1277303 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1277304 (x : nadd) (y : nadd) : (term189 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem1277303) (@lem1277302 x y)). Qed.
Lemma lem1277305 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1277306 (x : nadd) (y : nadd) : ((term186 x y) = (NUMERAL 0)) = ((term188 x y) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1277304 x y) (@lem1277305)). Qed.
Lemma lem1277307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1277308 (x : nadd) (y : nadd) : (term191 x y) = (term192 x y).
Proof. exact (MK_COMB (@lem1277307) (@lem1277306 x y)). Qed.
Lemma lem1277309 (x : nadd) (y : nadd) (m : nat) : (term193 x y m) = (term194 x y m).
Proof. exact (eq_refl (term193 x y m)). Qed.
Lemma lem1277310 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1277311 (x : nadd) (y : nadd) (m : nat) (n : nat) : (term195 x y m n) = (term196 x y m n).
Proof. exact (MK_COMB (@lem1277309 x y m) (@lem1277310 n)). Qed.
Lemma lem1277312 (n : nat) (x : nadd) (y : nadd) (m : nat) : (term196 x y m n) = (term166 n x y m).
Proof. exact (eq_refl (term196 x y m n)). Qed.
Lemma lem1277313 (n : nat) (x : nadd) (y : nadd) (m : nat) : (term195 x y m n) = (term166 n x y m).
Proof. exact (TRANS (@lem1277311 x y m n) (@lem1277312 n x y m)). Qed.
Lemma lem1277314 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1277315 (n : nat) (x : nadd) (y : nadd) (m : nat) : (term197 x y m n) = (term168 n x y m).
Proof. exact (MK_COMB (@lem1277314) (@lem1277313 n x y m)). Qed.
Lemma lem1277316 (A : nat) (m : nat) (n : nat) (B : nat) : (term198 A m n B) = (term198 A m n B).
Proof. exact (eq_refl (term198 A m n B)). Qed.
Lemma lem1277317 (x : nadd) (y : nadd) (A : nat) (m : nat) (n : nat) (B : nat) : (term199 x y A m n B) = (term200 x y A m n B).
Proof. exact (MK_COMB (@lem1277315 n x y m) (@lem1277316 A m n B)). Qed.
Lemma lem1277318 (x : nadd) (y : nadd) (A : nat) (m : nat) (B : nat) : (term201 x y A m B) = (term202 x y A m B).
Proof. exact (fun_ext (fun n : nat => @lem1277317 x y A m n B)). Qed.
Lemma lem1277319 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1277320 (x : nadd) (y : nadd) (A : nat) (m : nat) (B : nat) : (term203 x y A m B) = (term204 x y A m B).
Proof. exact (MK_COMB (@lem1277319) (@lem1277318 x y A m B)). Qed.
Lemma lem1277321 (x : nadd) (y : nadd) (A : nat) (B : nat) : (term205 x y A B) = (term206 x y A B).
Proof. exact (fun_ext (fun m : nat => @lem1277320 x y A m B)). Qed.
Lemma lem1277322 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1277323 (x : nadd) (y : nadd) (A : nat) (B : nat) : (term207 x y A B) = (term208 x y A B).
Proof. exact (MK_COMB (@lem1277322) (@lem1277321 x y A B)). Qed.
Lemma lem1277324 (x : nadd) (y : nadd) (A : nat) (B : nat) : (term209 x y A B) = (term210 x y A B).
Proof. exact (MK_COMB (@lem1277308 x y) (@lem1277323 x y A B)). Qed.
Lemma lem1277325 (x : nadd) (y : nadd) (A : nat) : (term211 x y A) = (term212 x y A).
Proof. exact (fun_ext (fun B : nat => @lem1277324 x y A B)). Qed.
Lemma lem1277326 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1277327 (x : nadd) (y : nadd) (A : nat) : (term213 x y A) = (term214 x y A).
Proof. exact (MK_COMB (@lem1277326) (@lem1277325 x y A)). Qed.
Lemma lem1277328 (x : nadd) (y : nadd) : (term215 x y) = (term216 x y).
Proof. exact (fun_ext (fun A : nat => @lem1277327 x y A)). Qed.
Lemma lem1277329 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1277330 (x : nadd) (y : nadd) : (term217 x y) = (term218 x y).
Proof. exact (MK_COMB (@lem1277329) (@lem1277328 x y)). Qed.
Lemma lem1277331 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1277332 (x : nadd) (y : nadd) : (term219 x y) = (term220 x y).
Proof. exact (MK_COMB (@lem1277331) (@lem1277330 x y)). Qed.
Lemma lem1277333 (x : nadd) (y : nadd) (m : nat) : (term193 x y m) = (term194 x y m).
Proof. exact (eq_refl (term193 x y m)). Qed.
Lemma lem1277334 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1277335 (x : nadd) (y : nadd) (m : nat) (n : nat) : (term195 x y m n) = (term196 x y m n).
Proof. exact (MK_COMB (@lem1277333 x y m) (@lem1277334 n)). Qed.
Lemma lem1277336 (n : nat) (x : nadd) (y : nadd) (m : nat) : (term196 x y m n) = (term166 n x y m).
Proof. exact (eq_refl (term196 x y m n)). Qed.
Lemma lem1277337 (n : nat) (x : nadd) (y : nadd) (m : nat) : (term195 x y m n) = (term166 n x y m).
Proof. exact (TRANS (@lem1277335 x y m n) (@lem1277336 n x y m)). Qed.
Lemma lem1277338 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1277339 (n : nat) (x : nadd) (y : nadd) (m : nat) : (term197 x y m n) = (term168 n x y m).
Proof. exact (MK_COMB (@lem1277338) (@lem1277337 n x y m)). Qed.
Lemma lem1277340 (B : nat) (m : nat) (n : nat) : (term20 B m n) = (term20 B m n).
Proof. exact (eq_refl (term20 B m n)). Qed.
Lemma lem1277341 (x : nadd) (y : nadd) (B : nat) (m : nat) (n : nat) : (term221 x y B m n) = (term170 x y B m n).
Proof. exact (MK_COMB (@lem1277339 n x y m) (@lem1277340 B m n)). Qed.
Lemma lem1277342 (x : nadd) (y : nadd) (B : nat) (m : nat) : (term222 x y B m) = (term172 x y B m).
Proof. exact (fun_ext (fun n : nat => @lem1277341 x y B m n)). Qed.
Lemma lem1277343 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1277344 (x : nadd) (y : nadd) (B : nat) (m : nat) : (term223 x y B m) = (term174 x y B m).
Proof. exact (MK_COMB (@lem1277343) (@lem1277342 x y B m)). Qed.
Lemma lem1277345 (x : nadd) (y : nadd) (B : nat) : (term224 x y B) = (term176 x y B).
Proof. exact (fun_ext (fun m : nat => @lem1277344 x y B m)). Qed.
Lemma lem1277346 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1277347 (x : nadd) (y : nadd) (B : nat) : (term225 x y B) = (term178 x y B).
Proof. exact (MK_COMB (@lem1277346) (@lem1277345 x y B)). Qed.
Lemma lem1277348 (x : nadd) (y : nadd) : (term226 x y) = (term180 x y).
Proof. exact (fun_ext (fun B : nat => @lem1277347 x y B)). Qed.
Lemma lem1277349 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1277350 (x : nadd) (y : nadd) : (term227 x y) = (term181 x y).
Proof. exact (MK_COMB (@lem1277349) (@lem1277348 x y)). Qed.
Lemma lem1277351 (x : nadd) (y : nadd) : (term182 x y) = (term228 x y).
Proof. exact (MK_COMB (@lem1277332 x y) (@lem1277350 x y)). Qed.
Lemma lem1277352 (x : nadd) (y : nadd) : term228 x y.
Proof. exact (EQ_MP (@lem1277351 x y) (@lem1277297 x y)). Qed.
Lemma lem1277366 (n : nat) : (term109 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1277114 n) (@lem1277113 n)). Qed.
Lemma lem1277367 (x : nadd) (y : nadd) : (term188 x y) = (NUMERAL 0).
Proof. exact (@lem1277366 (term229 x y)). Qed.
Lemma lem1277368 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1277369 (x : nadd) (y : nadd) : (term190 x y) = term230.
Proof. exact (MK_COMB (@lem1277368) (@lem1277367 x y)). Qed.
Lemma lem1277370 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1277371 (x : nadd) (y : nadd) : ((term188 x y) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1277369 x y) (@lem1277370)). Qed.
Lemma lem1277373 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1277374 (x : nat) : (x = x) = True.
Proof. exact (@lem1277373 nat x). Qed.
Lemma lem1277375 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1277374 (NUMERAL 0)). Qed.
Lemma lem1277376 (x : nadd) (y : nadd) : ((term188 x y) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1277371 x y) (@lem1277375)). Qed.
Lemma lem1277377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1277378 (x : nadd) (y : nadd) : (term192 x y) = (and True).
Proof. exact (MK_COMB (@lem1277377) (@lem1277376 x y)). Qed.
Lemma lem1277389 (x : nadd) (y : nadd) (A : nat) (B : nat) : (term208 x y A B) = (term208 x y A B).
Proof. exact (eq_refl (term208 x y A B)). Qed.
Lemma lem1277390 (x : nadd) (y : nadd) (A : nat) (B : nat) : (term210 x y A B) = (term231 x y A B).
Proof. exact (MK_COMB (@lem1277378 x y) (@lem1277389 x y A B)). Qed.
Lemma lem1277392 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1277393 (x : nadd) (y : nadd) (A : nat) (B : nat) : (term231 x y A B) = (term208 x y A B).
Proof. exact (@lem1277392 (term208 x y A B)). Qed.
Lemma lem1277404 (x : nadd) (y : nadd) (A : nat) (B : nat) : (term210 x y A B) = (term208 x y A B).
Proof. exact (TRANS (@lem1277390 x y A B) (@lem1277393 x y A B)). Qed.
Lemma lem1277405 (x : nadd) (y : nadd) (A : nat) : (term212 x y A) = (term232 x y A).
Proof. exact (fun_ext (fun B : nat => @lem1277404 x y A B)). Qed.
Lemma lem1277406 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1277407 (x : nadd) (y : nadd) (A : nat) : (term214 x y A) = (term233 x y A).
Proof. exact (MK_COMB (@lem1277406) (@lem1277405 x y A)). Qed.
Lemma lem1277412 (x : nadd) (y : nadd) : (term216 x y) = (term234 x y).
Proof. exact (fun_ext (fun A : nat => @lem1277407 x y A)). Qed.
Lemma lem1277413 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1277414 (x : nadd) (y : nadd) : (term218 x y) = (term235 x y).
Proof. exact (MK_COMB (@lem1277413) (@lem1277412 x y)). Qed.
Lemma lem1277419 (x : nadd) (y : nadd) : (term235 x y) = (term218 x y).
Proof. exact (SYM (@lem1277414 x y)). Qed.
Lemma lem1277421 (m : nat) (p : nat) : term40 m p.
Proof. exact (EQ_MP (@lem1277111 m p) (@lem1277110 m p)). Qed.
Lemma lem1277422 (x : nadd) (y : nadd) (C : nat) (B : nat) (m : nat) (n : nat) (D : nat) : term236 x y C B m n D.
Proof. exact (@lem1277421 (term166 n x y m) (term237 C B m n D)). Qed.
Lemma lem1277424 (m : nat) (p : nat) (p' : nat) : term100 m p p'.
Proof. exact (EQ_MP (@lem1277083 m p p') (@lem1277082 m p p')). Qed.
Lemma lem1277425 (x : nadd) (y : nadd) (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : term238 x y D C B m n.
Proof. exact (@lem1277424 (term160 m x y n) (term160 n x y m) (term239 D C B m n)). Qed.
Lemma lem1277427 (m : nat) (n : nat) (p : nat) (q : nat) : term58 m n p q.
Proof. exact (EQ_MP (@lem1277008 m n p q) (@lem1277007 m n p q)). Qed.
Lemma lem1277428 (x : nadd) (y : nadd) (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : term240 x y D C B m n.
Proof. exact (@lem1277427 (term241 x m y n) (term242 n x y m) (term243 m D) (term244 D C B m n)). Qed.
Lemma lem1277432 (n : nat) (m : nat) : (term49 m n) = (term49 n m).
Proof. exact (EQ_MP (@lem1276971 n m) (@lem1276970 m n)). Qed.
Lemma lem1277433 (m : nat) (x : nadd) (y : nadd) (n : nat) : (term241 x m y n) = (term245 m x y n).
Proof. exact (@lem1277432 (term246 x m y n) (term160 m x y n)). Qed.
Lemma lem1277434 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1277435 (m : nat) (x : nadd) (y : nadd) (n : nat) : (term247 x m y n) = (term248 m x y n).
Proof. exact (MK_COMB (@lem1277434) (@lem1277433 m x y n)). Qed.
Lemma lem1277436 (m : nat) (D : nat) : (term243 m D) = (term243 m D).
Proof. exact (eq_refl (term243 m D)). Qed.
Lemma lem1277437 (x : nadd) (y : nadd) (n : nat) (m : nat) (D : nat) : (term249 x y n m D) = (term250 x y n m D).
Proof. exact (MK_COMB (@lem1277435 m x y n) (@lem1277436 m D)). Qed.
Lemma lem1277438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1277439 (x : nadd) (y : nadd) (n : nat) (m : nat) (D : nat) : (term251 x y n m D) = (term252 x y n m D).
Proof. exact (MK_COMB (@lem1277438) (@lem1277437 x y n m D)). Qed.
Lemma lem1277441 (n : nat) (m : nat) : (term49 m n) = (term49 n m).
Proof. exact (EQ_MP (@lem1276971 n m) (@lem1276970 m n)). Qed.
Lemma lem1277442 (x : nadd) (m : nat) (y : nadd) (n : nat) : (term242 n x y m) = (term253 x m y n).
Proof. exact (@lem1277441 (term160 n x y m) (term246 x m y n)). Qed.
Lemma lem1277443 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1277444 (x : nadd) (m : nat) (y : nadd) (n : nat) : (term254 n x y m) = (term255 x m y n).
Proof. exact (MK_COMB (@lem1277443) (@lem1277442 x m y n)). Qed.
Lemma lem1277445 (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : (term244 D C B m n) = (term244 D C B m n).
Proof. exact (eq_refl (term244 D C B m n)). Qed.
Lemma lem1277446 (x : nadd) (y : nadd) (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : (term256 x y D C B m n) = (term257 x y D C B m n).
Proof. exact (MK_COMB (@lem1277444 x m y n) (@lem1277445 D C B m n)). Qed.
Lemma lem1277447 (x : nadd) (y : nadd) (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : (term258 x y D C B m n) = (term259 x y D C B m n).
Proof. exact (MK_COMB (@lem1277439 x y n m D) (@lem1277446 x y D C B m n)). Qed.
Lemma lem1277448 (x : nadd) (y : nadd) (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : (term259 x y D C B m n) = (term258 x y D C B m n).
Proof. exact (SYM (@lem1277447 x y D C B m n)). Qed.
Lemma lem1277465 (m : nat) (x : nadd) (D : nat) (h1 : term130 x D) : term260 x D m.
Proof. exact (@lem1277179 x D h1 m). Qed.
Lemma lem1277466 (x : nadd) (m : nat) (D : nat) : (term260 x D m) = (term261 x m D).
Proof. exact (eq_refl (term260 x D m)). Qed.
Lemma lem1277467 (m : nat) (x : nadd) (D : nat) (h1 : term130 x D) : term261 x m D.
Proof. exact (EQ_MP (@lem1277466 x m D) (@lem1277465 m x D h1)). Qed.
Lemma lem1277468 (m : nat) (n : nat) (x : nadd) (D : nat) (h1 : term130 x D) : term262 x m D n.
Proof. exact (@lem1277467 m x D h1 n). Qed.
Lemma lem1277469 (x : nadd) (n : nat) (m : nat) (D : nat) : (term262 x m D n) = (term263 x n m D).
Proof. exact (eq_refl (term262 x m D n)). Qed.
Lemma lem1277470 (n : nat) (m : nat) (x : nadd) (D : nat) (h1 : term130 x D) : term263 x n m D.
Proof. exact (EQ_MP (@lem1277469 x n m D) (@lem1277468 m n x D h1)). Qed.
Lemma lem1277471 (x : nadd) (n : nat) (m : nat) (D : nat) : (term263 x n m D) = ((term263 x n m D) = True).
Proof. exact (@lem7 (term263 x n m D)). Qed.
Lemma lem1277476 (n : nat) (m : nat) (x : nadd) (D : nat) (h1 : term130 x D) : (term263 x n m D) = True.
Proof. exact (EQ_MP (@lem1277471 x n m D) (@lem1277470 n m x D h1)). Qed.
Lemma lem1277477 (y : nadd) (n : nat) (m : nat) (x : nadd) (D : nat) (h1 : term130 x D) : (term250 x y n m D) = True.
Proof. exact (@lem1277476 (dest_nadd y n) m x D h1). Qed.
Lemma lem1277478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1277479 (y : nadd) (n : nat) (m : nat) (x : nadd) (D : nat) (h1 : term130 x D) : (term252 x y n m D) = (and True).
Proof. exact (MK_COMB (@lem1277478) (@lem1277477 y n m x D h1)). Qed.
Lemma lem1277480 (x : nadd) (y : nadd) (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : (term257 x y D C B m n) = (term257 x y D C B m n).
Proof. exact (eq_refl (term257 x y D C B m n)). Qed.
Lemma lem1277481 (y : nadd) (C : nat) (B : nat) (m : nat) (n : nat) (x : nadd) (D : nat) (h1 : term130 x D) : (term259 x y D C B m n) = (term264 x y D C B m n).
Proof. exact (MK_COMB (@lem1277479 y n m x D h1) (@lem1277480 x y D C B m n)). Qed.
Lemma lem1277483 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1277484 (x : nadd) (y : nadd) (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : (term264 x y D C B m n) = (term257 x y D C B m n).
Proof. exact (@lem1277483 (term257 x y D C B m n)). Qed.
Lemma lem1277485 (y : nadd) (C : nat) (B : nat) (m : nat) (n : nat) (x : nadd) (D : nat) (h1 : term130 x D) : (term259 x y D C B m n) = (term257 x y D C B m n).
Proof. exact (TRANS (@lem1277481 y C B m n x D h1) (@lem1277484 x y D C B m n)). Qed.
Lemma lem1277486 (y : nadd) (C : nat) (B : nat) (m : nat) (n : nat) (x : nadd) (D : nat) (h1 : term130 x D) : (term257 x y D C B m n) = (term259 x y D C B m n).
Proof. exact (SYM (@lem1277485 y C B m n x D h1)). Qed.
Lemma lem1277488 (m : nat) (p : nat) (p' : nat) : term100 m p p'.
Proof. exact (EQ_MP (@lem1276965 m p p') (@lem1276964 m p p')). Qed.
Lemma lem1277489 (x : nadd) (y : nadd) (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : term265 x y D C B m n.
Proof. exact (@lem1277488 (term160 n x y m) (term246 x m y n) (term244 D C B m n)). Qed.
Lemma lem1277491 (m : nat) (n : nat) (p : nat) (q : nat) : term58 m n p q.
Proof. exact (EQ_MP (@lem1276890 m n p q) (@lem1276889 m n p q)). Qed.
Lemma lem1277492 (x : nadd) (y : nadd) (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : term266 x y D C B m n.
Proof. exact (@lem1277491 (term241 x n y m) (term267 x m y n) (term243 n D) (term268 C B m n)). Qed.
Lemma lem1277496 (n : nat) (m : nat) : (term49 m n) = (term49 n m).
Proof. exact (EQ_MP (@lem1276853 n m) (@lem1276852 m n)). Qed.
Lemma lem1277497 (n : nat) (x : nadd) (y : nadd) (m : nat) : (term241 x n y m) = (term245 n x y m).
Proof. exact (@lem1277496 (term246 x n y m) (term160 n x y m)). Qed.
Lemma lem1277498 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1277499 (n : nat) (x : nadd) (y : nadd) (m : nat) : (term247 x n y m) = (term248 n x y m).
Proof. exact (MK_COMB (@lem1277498) (@lem1277497 n x y m)). Qed.
Lemma lem1277500 (n : nat) (D : nat) : (term243 n D) = (term243 n D).
Proof. exact (eq_refl (term243 n D)). Qed.
Lemma lem1277501 (x : nadd) (y : nadd) (m : nat) (n : nat) (D : nat) : (term249 x y m n D) = (term250 x y m n D).
Proof. exact (MK_COMB (@lem1277499 n x y m) (@lem1277500 n D)). Qed.
Lemma lem1277502 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1277503 (x : nadd) (y : nadd) (m : nat) (n : nat) (D : nat) : (term251 x y m n D) = (term252 x y m n D).
Proof. exact (MK_COMB (@lem1277502) (@lem1277501 x y m n D)). Qed.
Lemma lem1277505 (n : nat) (m : nat) : (term49 m n) = (term49 n m).
Proof. exact (EQ_MP (@lem1276853 n m) (@lem1276852 m n)). Qed.
Lemma lem1277506 (x : nadd) (n : nat) (y : nadd) (m : nat) : (term267 x m y n) = (term267 x n y m).
Proof. exact (@lem1277505 (term246 x m y n) (term246 x n y m)). Qed.
Lemma lem1277507 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1277508 (x : nadd) (n : nat) (y : nadd) (m : nat) : (term269 x m y n) = (term269 x n y m).
Proof. exact (MK_COMB (@lem1277507) (@lem1277506 x n y m)). Qed.
Lemma lem1277509 (C : nat) (B : nat) (m : nat) (n : nat) : (term268 C B m n) = (term268 C B m n).
Proof. exact (eq_refl (term268 C B m n)). Qed.
Lemma lem1277510 (x : nadd) (y : nadd) (C : nat) (B : nat) (m : nat) (n : nat) : (term270 x y C B m n) = (term271 x y C B m n).
Proof. exact (MK_COMB (@lem1277508 x n y m) (@lem1277509 C B m n)). Qed.
Lemma lem1277511 (D : nat) (x : nadd) (y : nadd) (C : nat) (B : nat) (m : nat) (n : nat) : (term272 D x y C B m n) = (term273 D x y C B m n).
Proof. exact (MK_COMB (@lem1277503 x y m n D) (@lem1277510 x y C B m n)). Qed.
Lemma lem1277512 (D : nat) (x : nadd) (y : nadd) (C : nat) (B : nat) (m : nat) (n : nat) : (term273 D x y C B m n) = (term272 D x y C B m n).
Proof. exact (SYM (@lem1277511 D x y C B m n)). Qed.
Lemma lem1277529 (m : nat) (x : nadd) (D : nat) (h1 : term130 x D) : term260 x D m.
Proof. exact (@lem1277179 x D h1 m). Qed.
Lemma lem1277530 (x : nadd) (m : nat) (D : nat) : (term260 x D m) = (term261 x m D).
Proof. exact (eq_refl (term260 x D m)). Qed.
Lemma lem1277531 (m : nat) (x : nadd) (D : nat) (h1 : term130 x D) : term261 x m D.
Proof. exact (EQ_MP (@lem1277530 x m D) (@lem1277529 m x D h1)). Qed.
Lemma lem1277532 (m : nat) (n : nat) (x : nadd) (D : nat) (h1 : term130 x D) : term262 x m D n.
Proof. exact (@lem1277531 m x D h1 n). Qed.
Lemma lem1277533 (x : nadd) (n : nat) (m : nat) (D : nat) : (term262 x m D n) = (term263 x n m D).
Proof. exact (eq_refl (term262 x m D n)). Qed.
Lemma lem1277534 (n : nat) (m : nat) (x : nadd) (D : nat) (h1 : term130 x D) : term263 x n m D.
Proof. exact (EQ_MP (@lem1277533 x n m D) (@lem1277532 m n x D h1)). Qed.
Lemma lem1277535 (x : nadd) (n : nat) (m : nat) (D : nat) : (term263 x n m D) = ((term263 x n m D) = True).
Proof. exact (@lem7 (term263 x n m D)). Qed.
Lemma lem1277540 (n : nat) (m : nat) (x : nadd) (D : nat) (h1 : term130 x D) : (term263 x n m D) = True.
Proof. exact (EQ_MP (@lem1277535 x n m D) (@lem1277534 n m x D h1)). Qed.
Lemma lem1277541 (y : nadd) (m : nat) (n : nat) (x : nadd) (D : nat) (h1 : term130 x D) : (term250 x y m n D) = True.
Proof. exact (@lem1277540 (dest_nadd y m) n x D h1). Qed.
Lemma lem1277542 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1277543 (y : nadd) (m : nat) (n : nat) (x : nadd) (D : nat) (h1 : term130 x D) : (term252 x y m n D) = (and True).
Proof. exact (MK_COMB (@lem1277542) (@lem1277541 y m n x D h1)). Qed.
Lemma lem1277544 (x : nadd) (y : nadd) (C : nat) (B : nat) (m : nat) (n : nat) : (term271 x y C B m n) = (term271 x y C B m n).
Proof. exact (eq_refl (term271 x y C B m n)). Qed.
Lemma lem1277545 (y : nadd) (C : nat) (B : nat) (m : nat) (n : nat) (x : nadd) (D : nat) (h1 : term130 x D) : (term273 D x y C B m n) = (term274 x y C B m n).
Proof. exact (MK_COMB (@lem1277543 y m n x D h1) (@lem1277544 x y C B m n)). Qed.
Lemma lem1277547 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1277548 (x : nadd) (y : nadd) (C : nat) (B : nat) (m : nat) (n : nat) : (term274 x y C B m n) = (term271 x y C B m n).
Proof. exact (@lem1277547 (term271 x y C B m n)). Qed.
Lemma lem1277549 (y : nadd) (C : nat) (B : nat) (m : nat) (n : nat) (x : nadd) (D : nat) (h1 : term130 x D) : (term273 D x y C B m n) = (term271 x y C B m n).
Proof. exact (TRANS (@lem1277545 y C B m n x D h1) (@lem1277548 x y C B m n)). Qed.
Lemma lem1277550 (y : nadd) (C : nat) (B : nat) (m : nat) (n : nat) (x : nadd) (D : nat) (h1 : term130 x D) : (term271 x y C B m n) = (term273 D x y C B m n).
Proof. exact (SYM (@lem1277549 y C B m n x D h1)). Qed.
Lemma lem1277552 (m : nat) (p : nat) : term40 m p.
Proof. exact (EQ_MP (@lem1276847 m p) (@lem1276846 m p)). Qed.
Lemma lem1277553 (x : nadd) (y : nadd) (C : nat) (B : nat) (m : nat) (n : nat) : term275 x y C B m n.
Proof. exact (@lem1277552 (term267 x n y m) (term268 C B m n)). Qed.
Lemma lem1277554 (m : nat) : term276 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem1277555 (m : nat) : (term276 m) = (term277 m).
Proof. exact (eq_refl (term276 m)). Qed.
Lemma lem1277556 (m : nat) : term277 m.
Proof. exact (EQ_MP (@lem1277555 m) (@lem1277554 m)). Qed.
Lemma lem1277557 (m : nat) (n : nat) : term278 m n.
Proof. exact (@lem1277556 m n). Qed.
Lemma lem1277558 (m : nat) (n : nat) : (term278 m n) = (term279 m n).
Proof. exact (eq_refl (term278 m n)). Qed.
Lemma lem1277559 (m : nat) (n : nat) : term279 m n.
Proof. exact (EQ_MP (@lem1277558 m n) (@lem1277557 m n)). Qed.
Lemma lem1277560 (m : nat) (n : nat) (p : nat) : term280 m n p.
Proof. exact (@lem1277559 m n p). Qed.
Lemma lem1277561 (m : nat) (n : nat) (p : nat) : (term280 m n p) = ((term281 n m p) = (term282 m n p)).
Proof. exact (eq_refl (term280 m n p)). Qed.
Lemma lem1277563 (m : nat) (y : nadd) (B : nat) (h1 : term136 y B) : term283 y B m.
Proof. exact (@lem1277187 y B h1 m). Qed.
Lemma lem1277564 (y : nadd) (B : nat) (m : nat) : (term283 y B m) = (term284 y B m).
Proof. exact (eq_refl (term283 y B m)). Qed.
Lemma lem1277565 (m : nat) (y : nadd) (B : nat) (h1 : term136 y B) : term284 y B m.
Proof. exact (EQ_MP (@lem1277564 y B m) (@lem1277563 m y B h1)). Qed.
Lemma lem1277566 (m : nat) (n : nat) (y : nadd) (B : nat) (h1 : term136 y B) : term285 y B m n.
Proof. exact (@lem1277565 m y B h1 n). Qed.
Lemma lem1277567 (y : nadd) (B : nat) (m : nat) (n : nat) : (term285 y B m n) = (term286 y B m n).
Proof. exact (eq_refl (term285 y B m n)). Qed.
Lemma lem1277568 (m : nat) (n : nat) (y : nadd) (B : nat) (h1 : term136 y B) : term286 y B m n.
Proof. exact (EQ_MP (@lem1277567 y B m n) (@lem1277566 m n y B h1)). Qed.
Lemma lem1277569 (y : nadd) (B : nat) (m : nat) (n : nat) : (term286 y B m n) = ((term286 y B m n) = True).
Proof. exact (@lem7 (term286 y B m n)). Qed.
Lemma lem1277571 (m : nat) (x : nadd) (C : nat) (h1 : term133 x C) : term287 x C m.
Proof. exact (@lem1277183 x C h1 m). Qed.
Lemma lem1277572 (x : nadd) (C : nat) (m : nat) : (term287 x C m) = (term288 x C m).
Proof. exact (eq_refl (term287 x C m)). Qed.
Lemma lem1277573 (m : nat) (x : nadd) (C : nat) (h1 : term133 x C) : term288 x C m.
Proof. exact (EQ_MP (@lem1277572 x C m) (@lem1277571 m x C h1)). Qed.
Lemma lem1277574 (m : nat) (n : nat) (x : nadd) (C : nat) (h1 : term133 x C) : term289 x C m n.
Proof. exact (@lem1277573 m x C h1 n). Qed.
Lemma lem1277575 (x : nadd) (C : nat) (m : nat) (n : nat) : (term289 x C m n) = (term290 x C m n).
Proof. exact (eq_refl (term289 x C m n)). Qed.
Lemma lem1277576 (m : nat) (n : nat) (x : nadd) (C : nat) (h1 : term133 x C) : term290 x C m n.
Proof. exact (EQ_MP (@lem1277575 x C m n) (@lem1277574 m n x C h1)). Qed.
Lemma lem1277577 (x : nadd) (C : nat) (m : nat) (n : nat) : (term290 x C m n) = ((term290 x C m n) = True).
Proof. exact (@lem7 (term290 x C m n)). Qed.
Lemma lem1277590 (m : nat) (n : nat) (x : nadd) (C : nat) (h1 : term133 x C) : (term290 x C m n) = True.
Proof. exact (EQ_MP (@lem1277577 x C m n) (@lem1277576 m n x C h1)). Qed.
Lemma lem1277591 (n : nat) (y : nadd) (m : nat) (x : nadd) (C : nat) (h1 : term133 x C) : (term291 x C n y m) = True.
Proof. exact (@lem1277590 (term292 m y n) (term292 n y m) x C h1). Qed.
Lemma lem1277592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1277593 (n : nat) (y : nadd) (m : nat) (x : nadd) (C : nat) (h1 : term133 x C) : (term293 x C n y m) = (and True).
Proof. exact (MK_COMB (@lem1277592) (@lem1277591 n y m x C h1)). Qed.
Lemma lem1277595 (m : nat) (n : nat) (p : nat) : (term281 n m p) = (term282 m n p).
Proof. exact (EQ_MP (@lem1277561 m n p) (@lem1277560 m n p)). Qed.
Lemma lem1277596 (C : nat) (y : nadd) (B : nat) (m : nat) (n : nat) : (term294 y C B m n) = (term295 C y B m n).
Proof. exact (@lem1277595 C (term296 n y m) (term20 B m n)). Qed.
Lemma lem1277602 (m : nat) (n : nat) (y : nadd) (B : nat) (h1 : term136 y B) : (term286 y B m n) = True.
Proof. exact (EQ_MP (@lem1277569 y B m n) (@lem1277568 m n y B h1)). Qed.
Lemma lem1277603 (C : nat) : (term297 C) = (term297 C).
Proof. exact (eq_refl (term297 C)). Qed.
Lemma lem1277604 (m : nat) (n : nat) (C : nat) (y : nadd) (B : nat) (h1 : term136 y B) : (term295 C y B m n) = (term298 C).
Proof. exact (MK_COMB (@lem1277603 C) (@lem1277602 m n y B h1)). Qed.
Lemma lem1277606 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1277607 (C : nat) : (term298 C) = True.
Proof. exact (@lem1277606 (C = (NUMERAL 0))). Qed.
Lemma lem1277608 (C : nat) (m : nat) (n : nat) (y : nadd) (B : nat) (h1 : term136 y B) : (term295 C y B m n) = True.
Proof. exact (TRANS (@lem1277604 m n C y B h1) (@lem1277607 C)). Qed.
Lemma lem1277609 (C : nat) (m : nat) (n : nat) (y : nadd) (B : nat) (h1 : term136 y B) : (term294 y C B m n) = True.
Proof. exact (TRANS (@lem1277596 C y B m n) (@lem1277608 C m n y B h1)). Qed.
Lemma lem1277610 (m : nat) (n : nat) (y : nadd) (B : nat) (x : nadd) (C : nat) (h1 : term136 y B) (h2 : term133 x C) : (term299 x y C B m n) = (True /\ True).
Proof. exact (MK_COMB (@lem1277593 n y m x C h2) (@lem1277609 C m n y B h1)). Qed.
Lemma lem1277612 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1277613 : (True /\ True) = True.
Proof. exact (@lem1277612 True). Qed.
Lemma lem1277614 (m : nat) (n : nat) (y : nadd) (B : nat) (x : nadd) (C : nat) (h1 : term136 y B) (h2 : term133 x C) : (term299 x y C B m n) = True.
Proof. exact (TRANS (@lem1277610 m n y B x C h1 h2) (@lem1277613)). Qed.
Lemma lem1277615 (m : nat) (n : nat) (y : nadd) (B : nat) (x : nadd) (C : nat) (h1 : term136 y B) (h2 : term133 x C) : True = (term299 x y C B m n).
Proof. exact (SYM (@lem1277614 m n y B x C h1 h2)). Qed.
Lemma lem1277616 (m : nat) (n : nat) (y : nadd) (B : nat) (x : nadd) (C : nat) (h1 : term136 y B) (h2 : term133 x C) : term299 x y C B m n.
Proof. exact (EQ_MP (@lem1277615 m n y B x C h1 h2) (@lem0)). Qed.
Lemma lem1277617 (m : nat) (n : nat) (y : nadd) (B : nat) (x : nadd) (C : nat) (h1 : term136 y B) (h2 : term133 x C) : term300 x y C B m n.
Proof. exact (ex_intro (term301 x y C B m n) (term302 C n y m) (@lem1277616 m n y B x C h1 h2)). Qed.
Lemma lem1277618 (m : nat) (n : nat) (y : nadd) (B : nat) (x : nadd) (C : nat) (h1 : term136 y B) (h2 : term133 x C) : term271 x y C B m n.
Proof. exact (@lem1277553 x y C B m n (@lem1277617 m n y B x C h1 h2)). Qed.
Lemma lem1277619 (m : nat) (n : nat) (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term273 D x y C B m n.
Proof. exact (EQ_MP (@lem1277550 y C B m n x D h3) (@lem1277618 m n y B x C h1 h2)). Qed.
Lemma lem1277620 (m : nat) (n : nat) (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term272 D x y C B m n.
Proof. exact (EQ_MP (@lem1277512 D x y C B m n) (@lem1277619 m n y B C x D h1 h2 h3)). Qed.
Lemma lem1277621 (m : nat) (n : nat) (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term303 x y D C B m n.
Proof. exact (@lem1277492 x y D C B m n (@lem1277620 m n y B C x D h1 h2 h3)). Qed.
Lemma lem1277622 (m : nat) (n : nat) (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term304 x y D C B m n.
Proof. exact (ex_intro (term305 x y D C B m n) (term246 x n y m) (@lem1277621 m n y B C x D h1 h2 h3)). Qed.
Lemma lem1277623 (m : nat) (n : nat) (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term257 x y D C B m n.
Proof. exact (@lem1277489 x y D C B m n (@lem1277622 m n y B C x D h1 h2 h3)). Qed.
Lemma lem1277624 (m : nat) (n : nat) (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term259 x y D C B m n.
Proof. exact (EQ_MP (@lem1277486 y C B m n x D h3) (@lem1277623 m n y B C x D h1 h2 h3)). Qed.
Lemma lem1277625 (m : nat) (n : nat) (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term258 x y D C B m n.
Proof. exact (EQ_MP (@lem1277448 x y D C B m n) (@lem1277624 m n y B C x D h1 h2 h3)). Qed.
Lemma lem1277626 (m : nat) (n : nat) (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term306 x y D C B m n.
Proof. exact (@lem1277428 x y D C B m n (@lem1277625 m n y B C x D h1 h2 h3)). Qed.
Lemma lem1277627 (m : nat) (n : nat) (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term307 x y D C B m n.
Proof. exact (ex_intro (term308 x y D C B m n) (term246 x m y n) (@lem1277626 m n y B C x D h1 h2 h3)). Qed.
Lemma lem1277628 (m : nat) (n : nat) (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term309 x y D C B m n.
Proof. exact (@lem1277425 x y D C B m n (@lem1277627 m n y B C x D h1 h2 h3)). Qed.
Lemma lem1277630 (m : nat) (n : nat) : term26 m n.
Proof. exact (EQ_MP (@lem1276819 m n) (@lem1276818 m n)). Qed.
Lemma lem1277631 (C : nat) (B : nat) (m : nat) (n : nat) (D : nat) : term310 C B m n D.
Proof. exact (@lem1277630 (term239 D C B m n) (term237 C B m n D)). Qed.
Lemma lem1277635 (m : nat) (n : nat) (p : nat) : (term311 m n p) = (term312 m n p).
Proof. exact (proj1 (@lem1276767 n m p)). Qed.
Lemma lem1277636 (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : (term239 D C B m n) = (term313 D C B m n).
Proof. exact (@lem1277635 (Nat.mul D m) D (term244 D C B m n)). Qed.
Lemma lem1277638 (n : nat) (m : nat) (p : nat) : (term312 m n p) = (term312 n m p).
Proof. exact (proj2 (@lem1276767 n m p)). Qed.
Lemma lem1277639 (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : (term313 D C B m n) = (term314 D C B m n).
Proof. exact (@lem1277638 D (Nat.mul D m) (term244 D C B m n)). Qed.
Lemma lem1277646 (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : (term239 D C B m n) = (term314 D C B m n).
Proof. exact (TRANS (@lem1277636 D C B m n) (@lem1277639 D C B m n)). Qed.
Lemma lem1277654 (m : nat) (n : nat) (p : nat) : (term311 m n p) = (term312 m n p).
Proof. exact (proj1 (@lem1276767 n m p)). Qed.
Lemma lem1277655 (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : (term244 D C B m n) = (term315 D C B m n).
Proof. exact (@lem1277654 (Nat.mul D n) D (term268 C B m n)). Qed.
Lemma lem1277657 (n : nat) (m : nat) (p : nat) : (term312 m n p) = (term312 n m p).
Proof. exact (proj2 (@lem1276767 n m p)). Qed.
Lemma lem1277658 (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : (term315 D C B m n) = (term316 D C B m n).
Proof. exact (@lem1277657 D (Nat.mul D n) (term268 C B m n)). Qed.
Lemma lem1277665 (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : (term244 D C B m n) = (term316 D C B m n).
Proof. exact (TRANS (@lem1277655 D C B m n) (@lem1277658 D C B m n)). Qed.
Lemma lem1277667 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1277668 (C : nat) (B : nat) (m : nat) (D : nat) (n : nat) : (term317 D C B m n) = (term318 C B m D n).
Proof. exact (@lem1277667 (term268 C B m n) (Nat.mul D n)). Qed.
Lemma lem1277673 (m : nat) (n : nat) (p : nat) : (term6 m n p) = (term7 m n p).
Proof. exact (EQ_MP (@lem1276778 m n p) (@lem1276777 m n p)). Qed.
Lemma lem1277674 (C : nat) (B : nat) (m : nat) (n : nat) : (term268 C B m n) = (term319 C B m n).
Proof. exact (@lem1277673 C B (Nat.add m n)). Qed.
Lemma lem1277676 (n : nat) (m : nat) (p : nat) : (term20 m n p) = (term21 n m p).
Proof. exact (EQ_MP (@lem1276796 n m p) (@lem1276795 n m p)). Qed.
Lemma lem1277677 (m : nat) (C : nat) (B : nat) (n : nat) : (term319 C B m n) = (term320 m C B n).
Proof. exact (@lem1277676 m (Nat.mul C B) n). Qed.
Lemma lem1277681 (m : nat) (C : nat) (B : nat) (n : nat) : (term268 C B m n) = (term320 m C B n).
Proof. exact (TRANS (@lem1277674 C B m n) (@lem1277677 m C B n)). Qed.
Lemma lem1277682 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1277683 (m : nat) (C : nat) (B : nat) (n : nat) : (term321 C B m n) = (term322 m C B n).
Proof. exact (MK_COMB (@lem1277682) (@lem1277681 m C B n)). Qed.
Lemma lem1277684 (D : nat) (n : nat) : (Nat.mul D n) = (Nat.mul D n).
Proof. exact (eq_refl (Nat.mul D n)). Qed.
Lemma lem1277685 (m : nat) (C : nat) (B : nat) (D : nat) (n : nat) : (term318 C B m D n) = (term323 m C B D n).
Proof. exact (MK_COMB (@lem1277683 m C B n) (@lem1277684 D n)). Qed.
Lemma lem1277687 (m : nat) (n : nat) (p : nat) : (term311 m n p) = (term312 m n p).
Proof. exact (proj1 (@lem1276767 n m p)). Qed.
Lemma lem1277688 (m : nat) (C : nat) (B : nat) (D : nat) (n : nat) : (term323 m C B D n) = (term324 m C B D n).
Proof. exact (@lem1277687 (term7 C B m) (term7 C B n) (Nat.mul D n)). Qed.
Lemma lem1277696 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1277697 (D : nat) (C : nat) (B : nat) (n : nat) : (term325 C B D n) = (term326 D C B n).
Proof. exact (@lem1277696 (Nat.mul D n) (term7 C B n)). Qed.
Lemma lem1277701 (C : nat) (B : nat) (m : nat) : (term327 C B m) = (term327 C B m).
Proof. exact (eq_refl (term327 C B m)). Qed.
Lemma lem1277702 (m : nat) (D : nat) (C : nat) (B : nat) (n : nat) : (term324 m C B D n) = (term328 m D C B n).
Proof. exact (MK_COMB (@lem1277701 C B m) (@lem1277697 D C B n)). Qed.
Lemma lem1277704 (n : nat) (m : nat) (p : nat) : (term312 m n p) = (term312 n m p).
Proof. exact (proj2 (@lem1276767 n m p)). Qed.
Lemma lem1277705 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term328 m D C B n) = (term329 D m C B n).
Proof. exact (@lem1277704 (Nat.mul D n) (term7 C B m) (term7 C B n)). Qed.
Lemma lem1277715 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term324 m C B D n) = (term329 D m C B n).
Proof. exact (TRANS (@lem1277702 m D C B n) (@lem1277705 D m C B n)). Qed.
Lemma lem1277716 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term323 m C B D n) = (term329 D m C B n).
Proof. exact (TRANS (@lem1277688 m C B D n) (@lem1277715 D m C B n)). Qed.
Lemma lem1277717 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term318 C B m D n) = (term329 D m C B n).
Proof. exact (TRANS (@lem1277685 m C B D n) (@lem1277716 D m C B n)). Qed.
Lemma lem1277718 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term317 D C B m n) = (term329 D m C B n).
Proof. exact (TRANS (@lem1277668 C B m D n) (@lem1277717 D m C B n)). Qed.
Lemma lem1277719 (D : nat) : (Nat.add D) = (Nat.add D).
Proof. exact (eq_refl (Nat.add D)). Qed.
Lemma lem1277720 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term316 D C B m n) = (term330 D m C B n).
Proof. exact (MK_COMB (@lem1277719 D) (@lem1277718 D m C B n)). Qed.
Lemma lem1277727 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term244 D C B m n) = (term330 D m C B n).
Proof. exact (TRANS (@lem1277665 D C B m n) (@lem1277720 D m C B n)). Qed.
Lemma lem1277728 (D : nat) (m : nat) : (term331 D m) = (term331 D m).
Proof. exact (eq_refl (term331 D m)). Qed.
Lemma lem1277729 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term332 D C B m n) = (term333 D m C B n).
Proof. exact (MK_COMB (@lem1277728 D m) (@lem1277727 D m C B n)). Qed.
Lemma lem1277731 (n : nat) (m : nat) (p : nat) : (term312 m n p) = (term312 n m p).
Proof. exact (proj2 (@lem1276767 n m p)). Qed.
Lemma lem1277732 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term333 D m C B n) = (term334 D m C B n).
Proof. exact (@lem1277731 D (Nat.mul D m) (term329 D m C B n)). Qed.
Lemma lem1277754 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term332 D C B m n) = (term334 D m C B n).
Proof. exact (TRANS (@lem1277729 D m C B n) (@lem1277732 D m C B n)). Qed.
Lemma lem1277755 (D : nat) : (Nat.add D) = (Nat.add D).
Proof. exact (eq_refl (Nat.add D)). Qed.
Lemma lem1277756 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term314 D C B m n) = (term335 D m C B n).
Proof. exact (MK_COMB (@lem1277755 D) (@lem1277754 D m C B n)). Qed.
Lemma lem1277763 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term239 D C B m n) = (term335 D m C B n).
Proof. exact (TRANS (@lem1277646 D C B m n) (@lem1277756 D m C B n)). Qed.
Lemma lem1277764 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1277765 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term336 D C B m n) = (term337 D m C B n).
Proof. exact (MK_COMB (@lem1277764) (@lem1277763 D m C B n)). Qed.
Lemma lem1277767 (n : nat) (m : nat) (p : nat) : (term312 m n p) = (term312 n m p).
Proof. exact (proj2 (@lem1276767 n m p)). Qed.
Lemma lem1277768 (C : nat) (B : nat) (m : nat) (n : nat) (D : nat) : (term237 C B m n D) = (term338 C B m n D).
Proof. exact (@lem1277767 D (term339 D C B m n) D). Qed.
Lemma lem1277776 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1277777 (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : (term340 C B m n D) = (term341 D C B m n).
Proof. exact (@lem1277776 D (term339 D C B m n)). Qed.
Lemma lem1277782 (m : nat) (n : nat) (p : nat) : (term13 m n p) = (term14 m n p).
Proof. exact (EQ_MP (@lem1276787 m n p) (@lem1276786 m n p)). Qed.
Lemma lem1277783 (D : nat) (C : nat) (B : nat) (m : nat) (n : nat) : (term339 D C B m n) = (term342 D C B m n).
Proof. exact (@lem1277782 D (Nat.mul C B) (Nat.add m n)). Qed.
Lemma lem1277788 (n : nat) (m : nat) (p : nat) : (term20 m n p) = (term21 n m p).
Proof. exact (EQ_MP (@lem1276796 n m p) (@lem1276795 n m p)). Qed.
Lemma lem1277789 (m : nat) (D : nat) (n : nat) : (term20 D m n) = (term21 m D n).
Proof. exact (@lem1277788 m D n). Qed.
Lemma lem1277793 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1277794 (m : nat) (D : nat) (n : nat) : (term343 D m n) = (term344 m D n).
Proof. exact (MK_COMB (@lem1277793) (@lem1277789 m D n)). Qed.
Lemma lem1277796 (n : nat) (m : nat) (p : nat) : (term20 m n p) = (term21 n m p).
Proof. exact (EQ_MP (@lem1276796 n m p) (@lem1276795 n m p)). Qed.
Lemma lem1277797 (m : nat) (C : nat) (B : nat) (n : nat) : (term319 C B m n) = (term320 m C B n).
Proof. exact (@lem1277796 m (Nat.mul C B) n). Qed.
Lemma lem1277801 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term342 D C B m n) = (term345 D m C B n).
Proof. exact (MK_COMB (@lem1277794 m D n) (@lem1277797 m C B n)). Qed.
Lemma lem1277803 (m : nat) (n : nat) (p : nat) : (term311 m n p) = (term312 m n p).
Proof. exact (proj1 (@lem1276767 n m p)). Qed.
Lemma lem1277804 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term345 D m C B n) = (term346 D m C B n).
Proof. exact (@lem1277803 (Nat.mul D m) (Nat.mul D n) (term320 m C B n)). Qed.
Lemma lem1277820 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term342 D C B m n) = (term346 D m C B n).
Proof. exact (TRANS (@lem1277801 D m C B n) (@lem1277804 D m C B n)). Qed.
Lemma lem1277821 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term339 D C B m n) = (term346 D m C B n).
Proof. exact (TRANS (@lem1277783 D C B m n) (@lem1277820 D m C B n)). Qed.
Lemma lem1277822 (D : nat) : (Nat.add D) = (Nat.add D).
Proof. exact (eq_refl (Nat.add D)). Qed.
Lemma lem1277823 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term341 D C B m n) = (term334 D m C B n).
Proof. exact (MK_COMB (@lem1277822 D) (@lem1277821 D m C B n)). Qed.
Lemma lem1277830 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term340 C B m n D) = (term334 D m C B n).
Proof. exact (TRANS (@lem1277777 D C B m n) (@lem1277823 D m C B n)). Qed.
Lemma lem1277831 (D : nat) : (Nat.add D) = (Nat.add D).
Proof. exact (eq_refl (Nat.add D)). Qed.
Lemma lem1277832 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term338 C B m n D) = (term335 D m C B n).
Proof. exact (MK_COMB (@lem1277831 D) (@lem1277830 D m C B n)). Qed.
Lemma lem1277839 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : (term237 C B m n D) = (term335 D m C B n).
Proof. exact (TRANS (@lem1277768 C B m n D) (@lem1277832 D m C B n)). Qed.
Lemma lem1277840 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : ((term239 D C B m n) = (term237 C B m n D)) = ((term335 D m C B n) = (term335 D m C B n)).
Proof. exact (MK_COMB (@lem1277765 D m C B n) (@lem1277839 D m C B n)). Qed.
Lemma lem1277842 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1277843 (x : nat) : (x = x) = True.
Proof. exact (@lem1277842 nat x). Qed.
Lemma lem1277844 (D : nat) (m : nat) (C : nat) (B : nat) (n : nat) : ((term335 D m C B n) = (term335 D m C B n)) = True.
Proof. exact (@lem1277843 (term335 D m C B n)). Qed.
Lemma lem1277845 (C : nat) (B : nat) (m : nat) (n : nat) (D : nat) : ((term239 D C B m n) = (term237 C B m n D)) = True.
Proof. exact (TRANS (@lem1277840 D m C B n) (@lem1277844 D m C B n)). Qed.
Lemma lem1277846 (C : nat) (B : nat) (m : nat) (n : nat) (D : nat) : True = ((term239 D C B m n) = (term237 C B m n D)).
Proof. exact (SYM (@lem1277845 C B m n D)). Qed.
Lemma lem1277847 (C : nat) (B : nat) (m : nat) (n : nat) (D : nat) : (term239 D C B m n) = (term237 C B m n D).
Proof. exact (EQ_MP (@lem1277846 C B m n D) (@lem0)). Qed.
Lemma lem1277848 (C : nat) (B : nat) (m : nat) (n : nat) (D : nat) : term347 C B m n D.
Proof. exact (@lem1277631 C B m n D (@lem1277847 C B m n D)). Qed.
Lemma lem1277849 (m : nat) (n : nat) (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term348 x y C B m n D.
Proof. exact (conj (@lem1277628 m n y B C x D h1 h2 h3) (@lem1277848 C B m n D)). Qed.
Lemma lem1277850 (m : nat) (n : nat) (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term349 x y C B m n D.
Proof. exact (ex_intro (term350 x y C B m n D) (term239 D C B m n) (@lem1277849 m n y B C x D h1 h2 h3)). Qed.
Lemma lem1277851 (m : nat) (n : nat) (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term351 x y C B m n D.
Proof. exact (@lem1277422 x y C B m n D (@lem1277850 m n y B C x D h1 h2 h3)). Qed.
Lemma lem1277856 (m : nat) (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term352 x y C B m D.
Proof. exact (fun n : nat => @lem1277851 m n y B C x D h1 h2 h3). Qed.
Lemma lem1277861 (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term353 x y C B D.
Proof. exact (fun m : nat => @lem1277856 m y B C x D h1 h2 h3). Qed.
Lemma lem1277862 (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term354 x y D C B.
Proof. exact (ex_intro (term355 x y D C B) (Nat.add D D) (@lem1277861 y B C x D h1 h2 h3)). Qed.
Lemma lem1277863 (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term235 x y.
Proof. exact (ex_intro (term234 x y) (term356 D C B) (@lem1277862 y B C x D h1 h2 h3)). Qed.
Lemma lem1277864 (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term218 x y.
Proof. exact (EQ_MP (@lem1277419 x y) (@lem1277863 y B C x D h1 h2 h3)). Qed.
Lemma lem1277865 (y : nadd) (B : nat) (C : nat) (x : nadd) (D : nat) (h1 : term136 y B) (h2 : term133 x C) (h3 : term130 x D) : term181 x y.
Proof. exact (@lem1277352 x y (@lem1277864 y B C x D h1 h2 h3)). Qed.
Lemma lem1277866 (y : nadd) (B : nat) (x : nadd) (C : nat) (h1 : term136 y B) (h2 : term133 x C) : term181 x y.
Proof. exact (ex_elim (@lem1277178 x) (fun D : nat => fun h0 : term357 x D => @lem1277865 y B C x D h1 h2 h0)). Qed.
Lemma lem1277867 (x : nadd) (y : nadd) (B : nat) (h1 : term136 y B) : term181 x y.
Proof. exact (ex_elim (@lem1277182 x) (fun C : nat => fun h0 : term358 x C => @lem1277866 y B x C h1 h0)). Qed.
Lemma lem1277868 (x : nadd) (y : nadd) : term181 x y.
Proof. exact (ex_elim (@lem1277186 y) (fun B : nat => fun h0 : term359 y B => @lem1277867 x y B h0)). Qed.
Lemma lem1277869 (x : nadd) (y : nadd) : (term144 x y) = (term148 x y).
Proof. exact (EQ_MP (@lem1277294 x y) (@lem1277868 x y)). Qed.
Lemma lem1277874 (x : nadd) : term360 x.
Proof. exact (fun y : nadd => @lem1277869 x y). Qed.
Lemma lem1277879 : term361.
Proof. exact (fun x : nadd => @lem1277874 x). Qed.
