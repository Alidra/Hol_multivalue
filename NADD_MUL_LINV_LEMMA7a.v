Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_LINV_LEMMA7a_term_abbrevs.
Require Import ADD_AC_spec.
Require Import ADD_ASSOC_spec.
Require Import ADD_CLAUSES_spec.
Require Import DIST_LZERO_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_ADD_spec.
Require Import LE_ADD2_spec.
Require Import LE_ADD_RCANCEL_spec.
Require Import LE_MULT_LCANCEL_spec.
Require Import LE_REFL_spec.
Require Import LE_TRANS_spec.
Require Import MULT_ASSOC_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_SYM_spec.
Require Import NADD_MUL_LINV_LEMMA0_spec.
Require Import REFL_CLAUSE_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1247221_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm89498_spec.
Lemma lem1305781 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem1305782 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem1305781 m n p h1)). Qed.
Lemma lem1305783 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem1305784 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem1305783 m n p h1)). Qed.
Lemma lem1305785 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem1305782 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem1305784 m n p h1)). Qed.
Lemma lem1305786 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem1305785 m n p)). Qed.
Lemma lem1305787 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1305788 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem1305787) (@lem1305786 m n)). Qed.
Lemma lem1305789 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem1305788 m n)). Qed.
Lemma lem1305790 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1305791 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem1305790) (@lem1305789 m)). Qed.
Lemma lem1305792 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem1305791 m)). Qed.
Lemma lem1305793 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1305794 : term12 = term13.
Proof. exact (MK_COMB (@lem1305793) (@lem1305792)). Qed.
Lemma lem1305795 : term13.
Proof. exact (EQ_MP (@lem1305794) (@lem77960)). Qed.
Lemma lem1305796 (m : nat) : term14 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1305797 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1305798 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem1305797 m) (@lem1305796 m)). Qed.
Lemma lem1305799 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem1305798 m n). Qed.
Lemma lem1305800 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1305801 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem1305800 m n) (@lem1305799 m n)). Qed.
Lemma lem1305802 (m : nat) (n : nat) : (term17 m n) = ((term17 m n) = True).
Proof. exact (@lem7 (term17 m n)). Qed.
Lemma lem1305804 (m : nat) : term18 m.
Proof. exact (@lem1305795 m). Qed.
Lemma lem1305805 (m : nat) : (term18 m) = (term9 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1305806 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem1305805 m) (@lem1305804 m)). Qed.
Lemma lem1305807 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem1305806 m n). Qed.
Lemma lem1305808 (m : nat) (n : nat) : (term19 m n) = (term5 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1305809 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem1305808 m n) (@lem1305807 m n)). Qed.
Lemma lem1305810 (m : nat) (n : nat) (p : nat) : term20 m n p.
Proof. exact (@lem1305809 m n p). Qed.
Lemma lem1305811 (m : nat) (n : nat) (p : nat) : (term20 m n p) = ((term1 m n p) = (term0 m n p)).
Proof. exact (eq_refl (term20 m n p)). Qed.
Lemma lem1305813 (m : nat) : term21 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1305814 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1305815 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1305814 m) (@lem1305813 m)). Qed.
Lemma lem1305816 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1305815 m n). Qed.
Lemma lem1305817 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1305818 (m : nat) (n : nat) : term24 m n.
Proof. exact (EQ_MP (@lem1305817 m n) (@lem1305816 m n)). Qed.
Lemma lem1305819 (m : nat) (n : nat) (p : nat) : term25 m n p.
Proof. exact (@lem1305818 m n p). Qed.
Lemma lem1305820 (m : nat) (n : nat) (p : nat) : (term25 m n p) = ((term26 m n p) = (term27 m n p)).
Proof. exact (eq_refl (term25 m n p)). Qed.
Lemma lem1305822 (m : nat) : term28 m.
Proof. exact (@lem100973 m). Qed.
Lemma lem1305823 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1305824 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem1305823 m) (@lem1305822 m)). Qed.
Lemma lem1305825 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem1305824 m n). Qed.
Lemma lem1305826 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem1305827 (m : nat) (n : nat) : term31 m n.
Proof. exact (EQ_MP (@lem1305826 m n) (@lem1305825 m n)). Qed.
Lemma lem1305828 (m : nat) (n : nat) (p : nat) : term32 m n p.
Proof. exact (@lem1305827 m n p). Qed.
Lemma lem1305829 (p : nat) (m : nat) (n : nat) : (term32 m n p) = ((term33 m n p) = (Peano.le m n)).
Proof. exact (eq_refl (term32 m n p)). Qed.
Lemma lem1305831 (m : nat) : term34 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem1305832 (m : nat) : (term34 m) = (term8 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem1305833 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem1305832 m) (@lem1305831 m)). Qed.
Lemma lem1305834 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem1305833 m n). Qed.
Lemma lem1305835 (m : nat) (n : nat) : (term35 m n) = (term4 m n).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem1305836 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem1305835 m n) (@lem1305834 m n)). Qed.
Lemma lem1305837 (m : nat) (n : nat) (p : nat) : term36 m n p.
Proof. exact (@lem1305836 m n p). Qed.
Lemma lem1305838 (m : nat) (n : nat) (p : nat) : (term36 m n p) = ((term0 m n p) = (term1 m n p)).
Proof. exact (eq_refl (term36 m n p)). Qed.
Lemma lem1305840 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem1305841 (m : nat) (h1 : term37) : term38 m.
Proof. exact (@lem1305840 h1 m). Qed.
Lemma lem1305842 (m : nat) : (term38 m) = (term39 m).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem1305843 (m : nat) (h1 : term37) : term39 m.
Proof. exact (EQ_MP (@lem1305842 m) (@lem1305841 m h1)). Qed.
Lemma lem1305844 (m : nat) (n : nat) (h1 : term37) : term40 m n.
Proof. exact (@lem1305843 m h1 n). Qed.
Lemma lem1305845 (n : nat) (m : nat) : (term40 m n) = (term41 n m).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem1305846 (n : nat) (m : nat) (h1 : term37) : term41 n m.
Proof. exact (EQ_MP (@lem1305845 n m) (@lem1305844 m n h1)). Qed.
Lemma lem1305847 (n : nat) (m : nat) (p : nat) (h1 : term37) : term42 n m p.
Proof. exact (@lem1305846 n m h1 p). Qed.
Lemma lem1305848 (n : nat) (m : nat) (p : nat) : (term42 n m p) = (term43 n m p).
Proof. exact (eq_refl (term42 n m p)). Qed.
Lemma lem1305849 (n : nat) (m : nat) (p : nat) (h1 : term37) : term43 n m p.
Proof. exact (EQ_MP (@lem1305848 n m p) (@lem1305847 n m p h1)). Qed.
Lemma lem1305850 (m : nat) (n : nat) (p : nat) (h1 : term44 m n p) : term44 m n p.
Proof. exact (h1). Qed.
Lemma lem1305851 (m : nat) (n : nat) (p : nat) (h1 : term37) (h2 : term44 m n p) : Peano.le m p.
Proof. exact (@lem1305849 n m p h1 (@lem1305850 m n p h2)). Qed.
Lemma lem1305852 (m : nat) (n : nat) (p : nat) (h1 : term44 m n p) : term45 m p.
Proof. exact (fun h0 : term37 => @lem1305851 m n p h0 h1). Qed.
Lemma lem1305853 (m : nat) (p : nat) (h1 : term46 m p) : term46 m p.
Proof. exact (h1). Qed.
Lemma lem1305854 (m : nat) (p : nat) (h1 : term46 m p) : term45 m p.
Proof. exact (ex_elim (@lem1305853 m p h1) (fun n : nat => fun h0 : term47 m p n => @lem1305852 m n p h0)). Qed.
Lemma lem1305855 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem1305856 (m : nat) (p : nat) (h1 : term37) (h2 : term46 m p) : Peano.le m p.
Proof. exact (@lem1305854 m p h2 (@lem1305855 h1)). Qed.
Lemma lem1305857 (m : nat) (p : nat) (h1 : term37) : term48 m p.
Proof. exact (fun h0 : term46 m p => @lem1305856 m p h1 h0). Qed.
Lemma lem1305858 (m : nat) (h1 : term37) : term49 m.
Proof. exact (fun p : nat => @lem1305857 m p h1). Qed.
Lemma lem1305859 (h1 : term37) : term50.
Proof. exact (fun m : nat => @lem1305858 m h1). Qed.
Lemma lem1305860 : term51.
Proof. exact (fun h0 : term37 => @lem1305859 h0). Qed.
Lemma lem1305861 : term50.
Proof. exact (@lem1305860 (@lem93743)). Qed.
Lemma lem1305862 (m : nat) : term52 m.
Proof. exact (@lem1305861 m). Qed.
Lemma lem1305863 (m : nat) : (term52 m) = (term49 m).
Proof. exact (eq_refl (term52 m)). Qed.
Lemma lem1305864 (m : nat) : term49 m.
Proof. exact (EQ_MP (@lem1305863 m) (@lem1305862 m)). Qed.
Lemma lem1305865 (m : nat) (p : nat) : term53 m p.
Proof. exact (@lem1305864 m p). Qed.
Lemma lem1305866 (m : nat) (p : nat) : (term53 m p) = (term48 m p).
Proof. exact (eq_refl (term53 m p)). Qed.
Lemma lem1305868 (m : nat) : term54 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1305869 (m : nat) : (term54 m) = (term55 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem1305870 (m : nat) : term55 m.
Proof. exact (EQ_MP (@lem1305869 m) (@lem1305868 m)). Qed.
Lemma lem1305871 (m : nat) (n : nat) : term56 m n.
Proof. exact (@lem1305870 m n). Qed.
Lemma lem1305872 (n : nat) (m : nat) : (term56 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term56 m n)). Qed.
Lemma lem1305877 (n : nat) (m : nat) (p : nat) (h1 : (term57 m n p) = (term58 n m p)) : (term57 m n p) = (term58 n m p).
Proof. exact (h1). Qed.
Lemma lem1305878 (n : nat) (m : nat) (p : nat) (h1 : (term57 m n p) = (term58 n m p)) : (term58 n m p) = (term57 m n p).
Proof. exact (SYM (@lem1305877 n m p h1)). Qed.
Lemma lem1305879 (m : nat) (n : nat) (p : nat) (h1 : (term58 n m p) = (term57 m n p)) : (term58 n m p) = (term57 m n p).
Proof. exact (h1). Qed.
Lemma lem1305880 (m : nat) (n : nat) (p : nat) (h1 : (term58 n m p) = (term57 m n p)) : (term57 m n p) = (term58 n m p).
Proof. exact (SYM (@lem1305879 m n p h1)). Qed.
Lemma lem1305881 (m : nat) (n : nat) (p : nat) : ((term57 m n p) = (term58 n m p)) = ((term58 n m p) = (term57 m n p)).
Proof. exact (prop_ext (fun h1 : (term57 m n p) = (term58 n m p) => @lem1305878 n m p h1) (fun h1 : (term58 n m p) = (term57 m n p) => @lem1305880 m n p h1)). Qed.
Lemma lem1305882 (m : nat) (n : nat) : (term59 n m) = (term60 m n).
Proof. exact (fun_ext (fun p : nat => @lem1305881 m n p)). Qed.
Lemma lem1305883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1305884 (m : nat) (n : nat) : (term61 n m) = (term62 m n).
Proof. exact (MK_COMB (@lem1305883) (@lem1305882 m n)). Qed.
Lemma lem1305885 (m : nat) : (term63 m) = (term64 m).
Proof. exact (fun_ext (fun n : nat => @lem1305884 m n)). Qed.
Lemma lem1305886 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1305887 (m : nat) : (term65 m) = (term66 m).
Proof. exact (MK_COMB (@lem1305886) (@lem1305885 m)). Qed.
Lemma lem1305888 : term67 = term68.
Proof. exact (fun_ext (fun m : nat => @lem1305887 m)). Qed.
Lemma lem1305889 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1305890 : term69 = term70.
Proof. exact (MK_COMB (@lem1305889) (@lem1305888)). Qed.
Lemma lem1305891 : term70.
Proof. exact (EQ_MP (@lem1305890) (@lem82055)). Qed.
Lemma lem1305895 (m : nat) (n : nat) (p : nat) (h1 : (term71 m n p) = (term72 m n p)) : (term71 m n p) = (term72 m n p).
Proof. exact (h1). Qed.
Lemma lem1305896 (m : nat) (n : nat) (p : nat) (h1 : (term71 m n p) = (term72 m n p)) : (term72 m n p) = (term71 m n p).
Proof. exact (SYM (@lem1305895 m n p h1)). Qed.
Lemma lem1305897 (m : nat) (n : nat) (p : nat) (h1 : (term72 m n p) = (term71 m n p)) : (term72 m n p) = (term71 m n p).
Proof. exact (h1). Qed.
Lemma lem1305898 (m : nat) (n : nat) (p : nat) (h1 : (term72 m n p) = (term71 m n p)) : (term71 m n p) = (term72 m n p).
Proof. exact (SYM (@lem1305897 m n p h1)). Qed.
Lemma lem1305899 (m : nat) (n : nat) (p : nat) : ((term71 m n p) = (term72 m n p)) = ((term72 m n p) = (term71 m n p)).
Proof. exact (prop_ext (fun h1 : (term71 m n p) = (term72 m n p) => @lem1305896 m n p h1) (fun h1 : (term72 m n p) = (term71 m n p) => @lem1305898 m n p h1)). Qed.
Lemma lem1305900 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (fun_ext (fun p : nat => @lem1305899 m n p)). Qed.
Lemma lem1305901 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1305902 (m : nat) (n : nat) : (term75 m n) = (term76 m n).
Proof. exact (MK_COMB (@lem1305901) (@lem1305900 m n)). Qed.
Lemma lem1305903 (m : nat) : (term77 m) = (term78 m).
Proof. exact (fun_ext (fun n : nat => @lem1305902 m n)). Qed.
Lemma lem1305904 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1305905 (m : nat) : (term79 m) = (term80 m).
Proof. exact (MK_COMB (@lem1305904) (@lem1305903 m)). Qed.
Lemma lem1305906 : term81 = term82.
Proof. exact (fun_ext (fun m : nat => @lem1305905 m)). Qed.
Lemma lem1305907 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1305908 : term83 = term84.
Proof. exact (MK_COMB (@lem1305907) (@lem1305906)). Qed.
Lemma lem1305909 : term84.
Proof. exact (EQ_MP (@lem1305908) (@lem82357)). Qed.
Lemma lem1305910 (m : nat) : term85 m.
Proof. exact (@lem1305891 m). Qed.
Lemma lem1305911 (m : nat) : (term85 m) = (term66 m).
Proof. exact (eq_refl (term85 m)). Qed.
Lemma lem1305912 (m : nat) : term66 m.
Proof. exact (EQ_MP (@lem1305911 m) (@lem1305910 m)). Qed.
Lemma lem1305913 (m : nat) (n : nat) : term86 m n.
Proof. exact (@lem1305912 m n). Qed.
Lemma lem1305914 (m : nat) (n : nat) : (term86 m n) = (term62 m n).
Proof. exact (eq_refl (term86 m n)). Qed.
Lemma lem1305915 (m : nat) (n : nat) : term62 m n.
Proof. exact (EQ_MP (@lem1305914 m n) (@lem1305913 m n)). Qed.
Lemma lem1305916 (m : nat) (n : nat) (p : nat) : term87 m n p.
Proof. exact (@lem1305915 m n p). Qed.
Lemma lem1305917 (m : nat) (n : nat) (p : nat) : (term87 m n p) = ((term58 n m p) = (term57 m n p)).
Proof. exact (eq_refl (term87 m n p)). Qed.
Lemma lem1305919 (m : nat) : term88 m.
Proof. exact (@lem1305909 m). Qed.
Lemma lem1305920 (m : nat) : (term88 m) = (term80 m).
Proof. exact (eq_refl (term88 m)). Qed.
Lemma lem1305921 (m : nat) : term80 m.
Proof. exact (EQ_MP (@lem1305920 m) (@lem1305919 m)). Qed.
Lemma lem1305922 (m : nat) (n : nat) : term89 m n.
Proof. exact (@lem1305921 m n). Qed.
Lemma lem1305923 (m : nat) (n : nat) : (term89 m n) = (term76 m n).
Proof. exact (eq_refl (term89 m n)). Qed.
Lemma lem1305924 (m : nat) (n : nat) : term76 m n.
Proof. exact (EQ_MP (@lem1305923 m n) (@lem1305922 m n)). Qed.
Lemma lem1305925 (m : nat) (n : nat) (p : nat) : term90 m n p.
Proof. exact (@lem1305924 m n p). Qed.
Lemma lem1305926 (m : nat) (n : nat) (p : nat) : (term90 m n p) = ((term72 m n p) = (term71 m n p)).
Proof. exact (eq_refl (term90 m n p)). Qed.
Lemma lem1305928 (h1 : term91) : term91.
Proof. exact (h1). Qed.
Lemma lem1305929 (m : nat) (h1 : term91) : term92 m.
Proof. exact (@lem1305928 h1 m). Qed.
Lemma lem1305930 (m : nat) : (term92 m) = (term93 m).
Proof. exact (eq_refl (term92 m)). Qed.
Lemma lem1305931 (m : nat) (h1 : term91) : term93 m.
Proof. exact (EQ_MP (@lem1305930 m) (@lem1305929 m h1)). Qed.
Lemma lem1305932 (m : nat) (n : nat) (h1 : term91) : term94 m n.
Proof. exact (@lem1305931 m h1 n). Qed.
Lemma lem1305933 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (eq_refl (term94 m n)). Qed.
Lemma lem1305934 (m : nat) (n : nat) (h1 : term91) : term95 m n.
Proof. exact (EQ_MP (@lem1305933 m n) (@lem1305932 m n h1)). Qed.
Lemma lem1305935 (m : nat) (n : nat) (p : nat) (h1 : term91) : term96 m n p.
Proof. exact (@lem1305934 m n h1 p). Qed.
Lemma lem1305936 (m : nat) (n : nat) (p : nat) : (term96 m n p) = (term97 m n p).
Proof. exact (eq_refl (term96 m n p)). Qed.
Lemma lem1305937 (m : nat) (n : nat) (p : nat) (h1 : term91) : term97 m n p.
Proof. exact (EQ_MP (@lem1305936 m n p) (@lem1305935 m n p h1)). Qed.
Lemma lem1305938 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term91) : term98 m n p q.
Proof. exact (@lem1305937 m n p h1 q). Qed.
Lemma lem1305939 (m : nat) (n : nat) (p : nat) (q : nat) : (term98 m n p q) = (term99 m n p q).
Proof. exact (eq_refl (term98 m n p q)). Qed.
Lemma lem1305940 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term91) : term99 m n p q.
Proof. exact (EQ_MP (@lem1305939 m n p q) (@lem1305938 m n p q h1)). Qed.
Lemma lem1305941 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term100 m p n q) : term100 m p n q.
Proof. exact (h1). Qed.
Lemma lem1305942 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term91) (h2 : term100 m p n q) : term101 m n p q.
Proof. exact (@lem1305940 m n p q h1 (@lem1305941 m p n q h2)). Qed.
Lemma lem1305943 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term100 m p n q) : term102 m n p q.
Proof. exact (fun h0 : term91 => @lem1305942 m p n q h0 h1). Qed.
Lemma lem1305944 (h1 : term91) : term91.
Proof. exact (h1). Qed.
Lemma lem1305945 (m : nat) (p : nat) (n : nat) (q : nat) (h1 : term91) (h2 : term100 m p n q) : term101 m n p q.
Proof. exact (@lem1305943 m p n q h2 (@lem1305944 h1)). Qed.
Lemma lem1305946 (m : nat) (n : nat) (p : nat) (q : nat) (h1 : term91) : term99 m n p q.
Proof. exact (fun h0 : term100 m p n q => @lem1305945 m p n q h1 h0). Qed.
Lemma lem1305947 (m : nat) (n : nat) (p : nat) (h1 : term91) : term97 m n p.
Proof. exact (fun q : nat => @lem1305946 m n p q h1). Qed.
Lemma lem1305948 (m : nat) (n : nat) (h1 : term91) : term95 m n.
Proof. exact (fun p : nat => @lem1305947 m n p h1). Qed.
Lemma lem1305949 (m : nat) (h1 : term91) : term93 m.
Proof. exact (fun n : nat => @lem1305948 m n h1). Qed.
Lemma lem1305950 (h1 : term91) : term91.
Proof. exact (fun m : nat => @lem1305949 m h1). Qed.
Lemma lem1305951 : term103.
Proof. exact (fun h0 : term91 => @lem1305950 h0). Qed.
Lemma lem1305952 : term91.
Proof. exact (@lem1305951 (@lem101399)). Qed.
Lemma lem1305953 (m : nat) : term92 m.
Proof. exact (@lem1305952 m). Qed.
Lemma lem1305954 (m : nat) : (term92 m) = (term93 m).
Proof. exact (eq_refl (term92 m)). Qed.
Lemma lem1305955 (m : nat) : term93 m.
Proof. exact (EQ_MP (@lem1305954 m) (@lem1305953 m)). Qed.
Lemma lem1305956 (m : nat) (n : nat) : term94 m n.
Proof. exact (@lem1305955 m n). Qed.
Lemma lem1305957 (m : nat) (n : nat) : (term94 m n) = (term95 m n).
Proof. exact (eq_refl (term94 m n)). Qed.
Lemma lem1305958 (m : nat) (n : nat) : term95 m n.
Proof. exact (EQ_MP (@lem1305957 m n) (@lem1305956 m n)). Qed.
Lemma lem1305959 (m : nat) (n : nat) (p : nat) : term96 m n p.
Proof. exact (@lem1305958 m n p). Qed.
Lemma lem1305960 (m : nat) (n : nat) (p : nat) : (term96 m n p) = (term97 m n p).
Proof. exact (eq_refl (term96 m n p)). Qed.
Lemma lem1305961 (m : nat) (n : nat) (p : nat) : term97 m n p.
Proof. exact (EQ_MP (@lem1305960 m n p) (@lem1305959 m n p)). Qed.
Lemma lem1305962 (m : nat) (n : nat) (p : nat) (q : nat) : term98 m n p q.
Proof. exact (@lem1305961 m n p q). Qed.
Lemma lem1305963 (m : nat) (n : nat) (p : nat) (q : nat) : (term98 m n p q) = (term99 m n p q).
Proof. exact (eq_refl (term98 m n p q)). Qed.
Lemma lem1305965 {A : Type'} (x : A) : term104 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem1305966 {A : Type'} (x : A) : (term104 A x) = ((x = x) = True).
Proof. exact (eq_refl (term104 A x)). Qed.
Lemma lem1305968 (n : nat) (m : nat) (p : nat) : term105 n m p.
Proof. exact (proj2 (@lem79120 n m p)). Qed.
Lemma lem1305975 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem1305968 n m p)). Qed.
Lemma lem1305976 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : (term106 a b c d e) = (term107 a b c d e).
Proof. exact (@lem1305975 a (Nat.add b c) (Nat.add d e)). Qed.
Lemma lem1305984 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem1305968 n m p)). Qed.
Lemma lem1305985 (b : nat) (c : nat) (d : nat) (e : nat) : (term108 b c d e) = (term109 b c d e).
Proof. exact (@lem1305984 b c (Nat.add d e)). Qed.
Lemma lem1306001 (a : nat) : (Nat.add a) = (Nat.add a).
Proof. exact (eq_refl (Nat.add a)). Qed.
Lemma lem1306002 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : (term107 a b c d e) = (term110 a b c d e).
Proof. exact (MK_COMB (@lem1306001 a) (@lem1305985 b c d e)). Qed.
Lemma lem1306009 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : (term106 a b c d e) = (term110 a b c d e).
Proof. exact (TRANS (@lem1305976 a b c d e) (@lem1306002 a b c d e)). Qed.
Lemma lem1306010 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1306011 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : (term111 a b c d e) = (term112 a b c d e).
Proof. exact (MK_COMB (@lem1306010) (@lem1306009 a b c d e)). Qed.
Lemma lem1306013 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem1305968 n m p)). Qed.
Lemma lem1306014 (c : nat) (d : nat) (b : nat) (a : nat) (e : nat) : (term113 c d b a e) = (term110 c d b a e).
Proof. exact (@lem1306013 c d (term0 b a e)). Qed.
Lemma lem1306022 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem1305968 n m p)). Qed.
Lemma lem1306023 (b : nat) (d : nat) (a : nat) (e : nat) : (term109 d b a e) = (term109 b d a e).
Proof. exact (@lem1306022 b d (Nat.add a e)). Qed.
Lemma lem1306031 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem1305968 n m p)). Qed.
Lemma lem1306032 (a : nat) (d : nat) (e : nat) : (term0 d a e) = (term0 a d e).
Proof. exact (@lem1306031 a d e). Qed.
Lemma lem1306042 (b : nat) : (Nat.add b) = (Nat.add b).
Proof. exact (eq_refl (Nat.add b)). Qed.
Lemma lem1306043 (b : nat) (a : nat) (d : nat) (e : nat) : (term109 b d a e) = (term109 b a d e).
Proof. exact (MK_COMB (@lem1306042 b) (@lem1306032 a d e)). Qed.
Lemma lem1306045 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem1305968 n m p)). Qed.
Lemma lem1306046 (a : nat) (b : nat) (d : nat) (e : nat) : (term109 b a d e) = (term109 a b d e).
Proof. exact (@lem1306045 a b (Nat.add d e)). Qed.
Lemma lem1306062 (a : nat) (b : nat) (d : nat) (e : nat) : (term109 b d a e) = (term109 a b d e).
Proof. exact (TRANS (@lem1306043 b a d e) (@lem1306046 a b d e)). Qed.
Lemma lem1306063 (a : nat) (b : nat) (d : nat) (e : nat) : (term109 d b a e) = (term109 a b d e).
Proof. exact (TRANS (@lem1306023 b d a e) (@lem1306062 a b d e)). Qed.
Lemma lem1306064 (c : nat) : (Nat.add c) = (Nat.add c).
Proof. exact (eq_refl (Nat.add c)). Qed.
Lemma lem1306065 (c : nat) (a : nat) (b : nat) (d : nat) (e : nat) : (term110 c d b a e) = (term110 c a b d e).
Proof. exact (MK_COMB (@lem1306064 c) (@lem1306063 a b d e)). Qed.
Lemma lem1306067 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem1305968 n m p)). Qed.
Lemma lem1306068 (a : nat) (c : nat) (b : nat) (d : nat) (e : nat) : (term110 c a b d e) = (term110 a c b d e).
Proof. exact (@lem1306067 a c (term0 b d e)). Qed.
Lemma lem1306076 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem1305968 n m p)). Qed.
Lemma lem1306077 (b : nat) (c : nat) (d : nat) (e : nat) : (term109 c b d e) = (term109 b c d e).
Proof. exact (@lem1306076 b c (Nat.add d e)). Qed.
Lemma lem1306093 (a : nat) : (Nat.add a) = (Nat.add a).
Proof. exact (eq_refl (Nat.add a)). Qed.
Lemma lem1306094 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : (term110 a c b d e) = (term110 a b c d e).
Proof. exact (MK_COMB (@lem1306093 a) (@lem1306077 b c d e)). Qed.
Lemma lem1306101 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : (term110 c a b d e) = (term110 a b c d e).
Proof. exact (TRANS (@lem1306068 a c b d e) (@lem1306094 a b c d e)). Qed.
Lemma lem1306102 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : (term110 c d b a e) = (term110 a b c d e).
Proof. exact (TRANS (@lem1306065 c a b d e) (@lem1306101 a b c d e)). Qed.
Lemma lem1306103 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : (term113 c d b a e) = (term110 a b c d e).
Proof. exact (TRANS (@lem1306014 c d b a e) (@lem1306102 a b c d e)). Qed.
Lemma lem1306104 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : ((term106 a b c d e) = (term113 c d b a e)) = ((term110 a b c d e) = (term110 a b c d e)).
Proof. exact (MK_COMB (@lem1306011 a b c d e) (@lem1306103 a b c d e)). Qed.
Lemma lem1306106 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1305966 A x) (@lem1305965 A x)). Qed.
Lemma lem1306107 (x : nat) : (x = x) = True.
Proof. exact (@lem1306106 nat x). Qed.
Lemma lem1306108 (a : nat) (b : nat) (c : nat) (d : nat) (e : nat) : ((term110 a b c d e) = (term110 a b c d e)) = True.
Proof. exact (@lem1306107 (term110 a b c d e)). Qed.
Lemma lem1306109 (c : nat) (d : nat) (b : nat) (a : nat) (e : nat) : ((term106 a b c d e) = (term113 c d b a e)) = True.
Proof. exact (TRANS (@lem1306104 a b c d e) (@lem1306108 a b c d e)). Qed.
Lemma lem1306110 (c : nat) (d : nat) (b : nat) (a : nat) (e : nat) : True = ((term106 a b c d e) = (term113 c d b a e)).
Proof. exact (SYM (@lem1306109 c d b a e)). Qed.
Lemma lem1306112 (m : nat) : term21 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1306113 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1306114 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1306113 m) (@lem1306112 m)). Qed.
Lemma lem1306115 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1306114 m n). Qed.
Lemma lem1306116 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1306117 (m : nat) (n : nat) : term24 m n.
Proof. exact (EQ_MP (@lem1306116 m n) (@lem1306115 m n)). Qed.
Lemma lem1306118 (m : nat) (n : nat) (p : nat) : term25 m n p.
Proof. exact (@lem1306117 m n p). Qed.
Lemma lem1306119 (m : nat) (n : nat) (p : nat) : (term25 m n p) = ((term26 m n p) = (term27 m n p)).
Proof. exact (eq_refl (term25 m n p)). Qed.
Lemma lem1306121 (m : nat) : term114 m.
Proof. exact (@lem1247221 m). Qed.
Lemma lem1306122 (m : nat) : (term114 m) = (term115 m).
Proof. exact (eq_refl (term114 m)). Qed.
Lemma lem1306123 (m : nat) : term115 m.
Proof. exact (EQ_MP (@lem1306122 m) (@lem1306121 m)). Qed.
Lemma lem1306124 (m : nat) (n : nat) : term116 m n.
Proof. exact (@lem1306123 m n). Qed.
Lemma lem1306125 (m : nat) (n : nat) : (term116 m n) = (term117 m n).
Proof. exact (eq_refl (term116 m n)). Qed.
Lemma lem1306126 (m : nat) (n : nat) : term117 m n.
Proof. exact (EQ_MP (@lem1306125 m n) (@lem1306124 m n)). Qed.
Lemma lem1306127 (m : nat) (n : nat) : (term117 m n) = ((term117 m n) = True).
Proof. exact (@lem7 (term117 m n)). Qed.
Lemma lem1306129 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem1306130 (m : nat) (h1 : term37) : term38 m.
Proof. exact (@lem1306129 h1 m). Qed.
Lemma lem1306131 (m : nat) : (term38 m) = (term39 m).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem1306132 (m : nat) (h1 : term37) : term39 m.
Proof. exact (EQ_MP (@lem1306131 m) (@lem1306130 m h1)). Qed.
Lemma lem1306133 (m : nat) (n : nat) (h1 : term37) : term40 m n.
Proof. exact (@lem1306132 m h1 n). Qed.
Lemma lem1306134 (n : nat) (m : nat) : (term40 m n) = (term41 n m).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem1306135 (n : nat) (m : nat) (h1 : term37) : term41 n m.
Proof. exact (EQ_MP (@lem1306134 n m) (@lem1306133 m n h1)). Qed.
Lemma lem1306136 (n : nat) (m : nat) (p : nat) (h1 : term37) : term42 n m p.
Proof. exact (@lem1306135 n m h1 p). Qed.
Lemma lem1306137 (n : nat) (m : nat) (p : nat) : (term42 n m p) = (term43 n m p).
Proof. exact (eq_refl (term42 n m p)). Qed.
Lemma lem1306138 (n : nat) (m : nat) (p : nat) (h1 : term37) : term43 n m p.
Proof. exact (EQ_MP (@lem1306137 n m p) (@lem1306136 n m p h1)). Qed.
Lemma lem1306139 (m : nat) (n : nat) (p : nat) (h1 : term44 m n p) : term44 m n p.
Proof. exact (h1). Qed.
Lemma lem1306140 (m : nat) (n : nat) (p : nat) (h1 : term37) (h2 : term44 m n p) : Peano.le m p.
Proof. exact (@lem1306138 n m p h1 (@lem1306139 m n p h2)). Qed.
Lemma lem1306141 (m : nat) (n : nat) (p : nat) (h1 : term44 m n p) : term45 m p.
Proof. exact (fun h0 : term37 => @lem1306140 m n p h0 h1). Qed.
Lemma lem1306142 (m : nat) (p : nat) (h1 : term46 m p) : term46 m p.
Proof. exact (h1). Qed.
Lemma lem1306143 (m : nat) (p : nat) (h1 : term46 m p) : term45 m p.
Proof. exact (ex_elim (@lem1306142 m p h1) (fun n : nat => fun h0 : term47 m p n => @lem1306141 m n p h0)). Qed.
Lemma lem1306144 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem1306145 (m : nat) (p : nat) (h1 : term37) (h2 : term46 m p) : Peano.le m p.
Proof. exact (@lem1306143 m p h2 (@lem1306144 h1)). Qed.
Lemma lem1306146 (m : nat) (p : nat) (h1 : term37) : term48 m p.
Proof. exact (fun h0 : term46 m p => @lem1306145 m p h1 h0). Qed.
Lemma lem1306147 (m : nat) (h1 : term37) : term49 m.
Proof. exact (fun p : nat => @lem1306146 m p h1). Qed.
Lemma lem1306148 (h1 : term37) : term50.
Proof. exact (fun m : nat => @lem1306147 m h1). Qed.
Lemma lem1306149 : term51.
Proof. exact (fun h0 : term37 => @lem1306148 h0). Qed.
Lemma lem1306150 : term50.
Proof. exact (@lem1306149 (@lem93743)). Qed.
Lemma lem1306151 (m : nat) : term52 m.
Proof. exact (@lem1306150 m). Qed.
Lemma lem1306152 (m : nat) : (term52 m) = (term49 m).
Proof. exact (eq_refl (term52 m)). Qed.
Lemma lem1306153 (m : nat) : term49 m.
Proof. exact (EQ_MP (@lem1306152 m) (@lem1306151 m)). Qed.
Lemma lem1306154 (m : nat) (p : nat) : term53 m p.
Proof. exact (@lem1306153 m p). Qed.
Lemma lem1306155 (m : nat) (p : nat) : (term53 m p) = (term48 m p).
Proof. exact (eq_refl (term53 m p)). Qed.
Lemma lem1306157 : term118.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem1306158 (m : nat) : term119 m.
Proof. exact (@lem1306157 m). Qed.
Lemma lem1306159 (m : nat) : (term119 m) = (term120 m).
Proof. exact (eq_refl (term119 m)). Qed.
Lemma lem1306160 (m : nat) : term120 m.
Proof. exact (EQ_MP (@lem1306159 m) (@lem1306158 m)). Qed.
Lemma lem1306161 (m : nat) (n : nat) : term121 m n.
Proof. exact (@lem1306160 m n). Qed.
Lemma lem1306162 (m : nat) (n : nat) : (term121 m n) = ((term122 m n) = (term123 m n)).
Proof. exact (eq_refl (term121 m n)). Qed.
Lemma lem1306168 (m : nat) : term54 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem1306169 (m : nat) : (term54 m) = (term55 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem1306170 (m : nat) : term55 m.
Proof. exact (EQ_MP (@lem1306169 m) (@lem1306168 m)). Qed.
Lemma lem1306171 (m : nat) (n : nat) : term56 m n.
Proof. exact (@lem1306170 m n). Qed.
Lemma lem1306172 (n : nat) (m : nat) : (term56 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term56 m n)). Qed.
Lemma lem1306174 : term124.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1306190 : term125.
Proof. exact (proj1 (@lem1306174)). Qed.
Lemma lem1306191 (m : nat) : term126 m.
Proof. exact (@lem1306190 m). Qed.
Lemma lem1306192 (m : nat) : (term126 m) = ((term127 m) = m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem1306198 (n : nat) : term128 n.
Proof. exact (@lem1244859 n). Qed.
Lemma lem1306199 (n : nat) : (term128 n) = ((term129 n) = n).
Proof. exact (eq_refl (term128 n)). Qed.
Lemma lem1306231 : term130.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem1306232 (n : nat) : term131 n.
Proof. exact (@lem1306231 n). Qed.
Lemma lem1306233 (n : nat) : (term131 n) = ((term132 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term131 n)). Qed.
Lemma lem1306242 : term133.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem1306243 (m : nat) : term134 m.
Proof. exact (@lem1306242 m). Qed.
Lemma lem1306244 (m : nat) : (term134 m) = ((term135 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term134 m)). Qed.
Lemma lem1306246 (x : nadd) : term136 x.
Proof. exact (@lem1301912 x). Qed.
Lemma lem1306247 (x : nadd) : (term136 x) = (term137 x).
Proof. exact (eq_refl (term136 x)). Qed.
Lemma lem1306249 (x : nadd) (h1 : term138 x) : term138 x.
Proof. exact (h1). Qed.
Lemma lem1306251 (x : nadd) : term137 x.
Proof. exact (EQ_MP (@lem1306247 x) (@lem1306246 x)). Qed.
Lemma lem1306252 (x : nadd) (h1 : term138 x) : term139 x.
Proof. exact (@lem1306251 x (@lem1306249 x h1)). Qed.
Lemma lem1306253 (x : nadd) (h1 : term139 x) : term139 x.
Proof. exact (h1). Qed.
Lemma lem1306254 (x : nadd) (A0 : nat) (h1 : term140 x A0) : term140 x A0.
Proof. exact (h1). Qed.
Lemma lem1306255 (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : term141 x A0 B0.
Proof. exact (h1). Qed.
Lemma lem1306257 (P : nat -> Prop) : term142 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1306258 (x : nadd) : term143 x.
Proof. exact (@lem1306257 (term144 x)). Qed.
Lemma lem1306259 (x : nadd) : (term145 x) = (term146 x).
Proof. exact (eq_refl (term145 x)). Qed.
Lemma lem1306260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1306261 (x : nadd) : (term147 x) = (term148 x).
Proof. exact (MK_COMB (@lem1306260) (@lem1306259 x)). Qed.
Lemma lem1306262 (N : nat) (x : nadd) : (term149 x N) = (term150 N x).
Proof. exact (eq_refl (term149 x N)). Qed.
Lemma lem1306263 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1306264 (N : nat) (x : nadd) : (term151 x N) = (term152 N x).
Proof. exact (MK_COMB (@lem1306263) (@lem1306262 N x)). Qed.
Lemma lem1306265 (N : nat) (x : nadd) : (term153 x N) = (term154 N x).
Proof. exact (eq_refl (term153 x N)). Qed.
Lemma lem1306266 (N : nat) (x : nadd) : (term155 x N) = (term156 N x).
Proof. exact (MK_COMB (@lem1306264 N x) (@lem1306265 N x)). Qed.
Lemma lem1306267 (x : nadd) : (term157 x) = (term158 x).
Proof. exact (fun_ext (fun N : nat => @lem1306266 N x)). Qed.
Lemma lem1306268 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1306269 (x : nadd) : (term159 x) = (term160 x).
Proof. exact (MK_COMB (@lem1306268) (@lem1306267 x)). Qed.
Lemma lem1306270 (x : nadd) : (term161 x) = (term162 x).
Proof. exact (MK_COMB (@lem1306261 x) (@lem1306269 x)). Qed.
Lemma lem1306271 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1306272 (x : nadd) : (term163 x) = (term164 x).
Proof. exact (MK_COMB (@lem1306271) (@lem1306270 x)). Qed.
Lemma lem1306273 (N : nat) (x : nadd) : (term149 x N) = (term150 N x).
Proof. exact (eq_refl (term149 x N)). Qed.
Lemma lem1306274 (x : nadd) : (term165 x) = (term144 x).
Proof. exact (fun_ext (fun N : nat => @lem1306273 N x)). Qed.
Lemma lem1306275 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1306276 (x : nadd) : (term166 x) = (term167 x).
Proof. exact (MK_COMB (@lem1306275) (@lem1306274 x)). Qed.
Lemma lem1306277 (x : nadd) : (term143 x) = (term168 x).
Proof. exact (MK_COMB (@lem1306272 x) (@lem1306276 x)). Qed.
Lemma lem1306278 (x : nadd) : term168 x.
Proof. exact (EQ_MP (@lem1306277 x) (@lem1306258 x)). Qed.
Lemma lem1306279 (N : nat) (x : nadd) (h1 : term150 N x) : term150 N x.
Proof. exact (h1). Qed.
Lemma lem1306283 (m : nat) : (term135 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1306244 m) (@lem1306243 m)). Qed.
Lemma lem1306286 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1306287 (m : nat) : (term169 m) = (term170 m).
Proof. exact (MK_COMB (@lem1306286) (@lem1306283 m)). Qed.
Lemma lem1306288 (m : nat) (x : nadd) (n : nat) : (term171 m x n) = (term171 m x n).
Proof. exact (eq_refl (term171 m x n)). Qed.
Lemma lem1306289 (m : nat) (x : nadd) (n : nat) : (term172 m x n) = (term173 m x n).
Proof. exact (MK_COMB (@lem1306287 m) (@lem1306288 m x n)). Qed.
Lemma lem1306294 (m : nat) (x : nadd) (n : nat) : (term173 m x n) = (term172 m x n).
Proof. exact (SYM (@lem1306289 m x n)). Qed.
Lemma lem1306295 (m : nat) (h1 : m = (NUMERAL 0)) : m = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1306296 (x : nadd) (n : nat) : (term174 x n) = (term174 x n).
Proof. exact (eq_refl (term174 x n)). Qed.
Lemma lem1306297 (x : nadd) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term175 x n m) = (term176 x n).
Proof. exact (MK_COMB (@lem1306296 x n) (@lem1306295 m h1)). Qed.
Lemma lem1306298 (x : nadd) (n : nat) : (term176 x n) = (term177 x n).
Proof. exact (eq_refl (term176 x n)). Qed.
Lemma lem1306299 (x : nadd) (n : nat) (m : nat) : (term178 x n m) = (term178 x n m).
Proof. exact (eq_refl (term178 x n m)). Qed.
Lemma lem1306300 (m : nat) (x : nadd) (n : nat) : ((term175 x n m) = (term176 x n)) = ((term175 x n m) = (term177 x n)).
Proof. exact (MK_COMB (@lem1306299 x n m) (@lem1306298 x n)). Qed.
Lemma lem1306301 (m : nat) (x : nadd) (n : nat) : (term175 x n m) = (term171 m x n).
Proof. exact (eq_refl (term175 x n m)). Qed.
Lemma lem1306302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1306303 (m : nat) (x : nadd) (n : nat) : (term178 x n m) = (term179 m x n).
Proof. exact (MK_COMB (@lem1306302) (@lem1306301 m x n)). Qed.
Lemma lem1306304 (x : nadd) (n : nat) : (term177 x n) = (term177 x n).
Proof. exact (eq_refl (term177 x n)). Qed.
Lemma lem1306305 (m : nat) (x : nadd) (n : nat) : ((term175 x n m) = (term177 x n)) = ((term171 m x n) = (term177 x n)).
Proof. exact (MK_COMB (@lem1306303 m x n) (@lem1306304 x n)). Qed.
Lemma lem1306306 (m : nat) (x : nadd) (n : nat) : ((term175 x n m) = (term176 x n)) = ((term171 m x n) = (term177 x n)).
Proof. exact (TRANS (@lem1306300 m x n) (@lem1306305 m x n)). Qed.
Lemma lem1306307 (x : nadd) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term171 m x n) = (term177 x n).
Proof. exact (EQ_MP (@lem1306306 m x n) (@lem1306297 x n m h1)). Qed.
Lemma lem1306308 (x : nadd) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : (term177 x n) = (term171 m x n).
Proof. exact (SYM (@lem1306307 x n m h1)). Qed.
Lemma lem1306310 (n : nat) : (term132 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1306233 n) (@lem1306232 n)). Qed.
Lemma lem1306311 (x : nadd) (n : nat) : (term180 x n) = (NUMERAL 0).
Proof. exact (@lem1306310 (nadd_rinv x n)). Qed.
Lemma lem1306312 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1306313 (x : nadd) (n : nat) : (term181 x n) = term182.
Proof. exact (MK_COMB (@lem1306312) (@lem1306311 x n)). Qed.
Lemma lem1306314 (n : nat) (x : nadd) : (term183 n x) = (term183 n x).
Proof. exact (eq_refl (term183 n x)). Qed.
Lemma lem1306315 (n : nat) (x : nadd) : (term184 n x) = (term185 n x).
Proof. exact (MK_COMB (@lem1306313 x n) (@lem1306314 n x)). Qed.
Lemma lem1306316 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1306317 (n : nat) (x : nadd) : (term186 n x) = (term187 n x).
Proof. exact (MK_COMB (@lem1306316) (@lem1306315 n x)). Qed.
Lemma lem1306319 (n : nat) : (term129 n) = n.
Proof. exact (EQ_MP (@lem1306199 n) (@lem1306198 n)). Qed.
Lemma lem1306320 (n : nat) (x : nadd) : (term187 n x) = (term183 n x).
Proof. exact (@lem1306319 (term183 n x)). Qed.
Lemma lem1306321 (n : nat) (x : nadd) : (term186 n x) = (term183 n x).
Proof. exact (TRANS (@lem1306317 n x) (@lem1306320 n x)). Qed.
Lemma lem1306322 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1306323 (n : nat) (x : nadd) : (term188 n x) = (term189 n x).
Proof. exact (MK_COMB (@lem1306322) (@lem1306321 n x)). Qed.
Lemma lem1306325 (m : nat) : (term127 m) = m.
Proof. exact (EQ_MP (@lem1306192 m) (@lem1306191 m)). Qed.
Lemma lem1306326 (x : nadd) (n : nat) : (term190 x n) = (term191 x n).
Proof. exact (@lem1306325 (term191 x n)). Qed.
Lemma lem1306327 (x : nadd) (n : nat) : (term177 x n) = (term192 x n).
Proof. exact (MK_COMB (@lem1306323 n x) (@lem1306326 x n)). Qed.
Lemma lem1306328 (x : nadd) (n : nat) : (term192 x n) = (term177 x n).
Proof. exact (SYM (@lem1306327 x n)). Qed.
Lemma lem1306330 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1306172 n m) (@lem1306171 m n)). Qed.
Lemma lem1306331 (n : nat) (x : nadd) : (term191 x n) = (term183 n x).
Proof. exact (@lem1306330 n (term193 x)). Qed.
Lemma lem1306332 (n : nat) (x : nadd) : (term189 n x) = (term189 n x).
Proof. exact (eq_refl (term189 n x)). Qed.
Lemma lem1306333 (n : nat) (x : nadd) : (term192 x n) = (term194 n x).
Proof. exact (MK_COMB (@lem1306332 n x) (@lem1306331 n x)). Qed.
Lemma lem1306334 (x : nadd) (n : nat) : (term194 n x) = (term192 x n).
Proof. exact (SYM (@lem1306333 n x)). Qed.
Lemma lem1306335 (n : nat) : term195 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem1306336 (n : nat) : (term195 n) = (Peano.le n n).
Proof. exact (eq_refl (term195 n)). Qed.
Lemma lem1306339 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem1306336 n) (@lem1306335 n)). Qed.
Lemma lem1306340 (n : nat) (x : nadd) : term194 n x.
Proof. exact (@lem1306339 (term183 n x)). Qed.
Lemma lem1306341 (x : nadd) (n : nat) : term192 x n.
Proof. exact (EQ_MP (@lem1306334 x n) (@lem1306340 n x)). Qed.
Lemma lem1306342 (x : nadd) (n : nat) : term177 x n.
Proof. exact (EQ_MP (@lem1306328 x n) (@lem1306341 x n)). Qed.
Lemma lem1306343 (x : nadd) (n : nat) (m : nat) (h1 : m = (NUMERAL 0)) : term171 m x n.
Proof. exact (EQ_MP (@lem1306308 x n m h1) (@lem1306342 x n)). Qed.
Lemma lem1306344 (m : nat) (x : nadd) (n : nat) : term173 m x n.
Proof. exact (fun h0 : m = (NUMERAL 0) => @lem1306343 x n m h0). Qed.
Lemma lem1306345 (m : nat) (x : nadd) (n : nat) : term172 m x n.
Proof. exact (EQ_MP (@lem1306294 m x n) (@lem1306344 m x n)). Qed.
Lemma lem1306350 (m : nat) (x : nadd) : term196 m x.
Proof. exact (fun n : nat => @lem1306345 m x n). Qed.
Lemma lem1306355 (x : nadd) : term197 x.
Proof. exact (fun m : nat => @lem1306350 m x). Qed.
Lemma lem1306356 (x : nadd) : term198 x.
Proof. exact (ex_intro (term199 x) (NUMERAL 0) (@lem1306355 x)). Qed.
Lemma lem1306357 (x : nadd) : term146 x.
Proof. exact (ex_intro (term200 x) (term193 x) (@lem1306356 x)). Qed.
Lemma lem1306358 (N : nat) (x : nadd) (A : nat) (h1 : term201 N x A) : term201 N x A.
Proof. exact (h1). Qed.
Lemma lem1306359 (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term202 N x A B) : term202 N x A B.
Proof. exact (h1). Qed.
Lemma lem1306363 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (EQ_MP (@lem1306162 m n) (@lem1306161 m n)). Qed.
Lemma lem1306364 (m : nat) (N : nat) : (term122 m N) = (term123 m N).
Proof. exact (@lem1306363 m N). Qed.
Lemma lem1306369 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1306370 (m : nat) (N : nat) : (term203 m N) = (term204 m N).
Proof. exact (MK_COMB (@lem1306369) (@lem1306364 m N)). Qed.
Lemma lem1306371 (m : nat) (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term205 m A x A0 n N B0 B) = (term205 m A x A0 n N B0 B).
Proof. exact (eq_refl (term205 m A x A0 n N B0 B)). Qed.
Lemma lem1306372 (m : nat) (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term206 m A x A0 n N B0 B) = (term207 m A x A0 n N B0 B).
Proof. exact (MK_COMB (@lem1306370 m N) (@lem1306371 m A x A0 n N B0 B)). Qed.
Lemma lem1306375 (m : nat) (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term207 m A x A0 n N B0 B) = (term206 m A x A0 n N B0 B).
Proof. exact (SYM (@lem1306372 m A x A0 n N B0 B)). Qed.
Lemma lem1306376 (m : nat) (N : nat) (h1 : term123 m N) : term123 m N.
Proof. exact (h1). Qed.
Lemma lem1306377 (m : nat) (N : nat) (h1 : m = (S N)) : m = (S N).
Proof. exact (h1). Qed.
Lemma lem1306378 (m : nat) (N : nat) (h1 : Peano.le m N) : Peano.le m N.
Proof. exact (h1). Qed.
Lemma lem1306379 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term208 A x A0 n N B0 B) = (term208 A x A0 n N B0 B).
Proof. exact (eq_refl (term208 A x A0 n N B0 B)). Qed.
Lemma lem1306380 (A : nat) (x : nadd) (A0 : nat) (n : nat) (B0 : nat) (B : nat) (m : nat) (N : nat) (h1 : m = (S N)) : (term209 A x A0 n N B0 B m) = (term210 A x A0 n B0 B N).
Proof. exact (MK_COMB (@lem1306379 A x A0 n N B0 B) (@lem1306377 m N h1)). Qed.
Lemma lem1306381 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term210 A x A0 n B0 B N) = (term211 A x A0 n N B0 B).
Proof. exact (eq_refl (term210 A x A0 n B0 B N)). Qed.
Lemma lem1306382 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) (m : nat) : (term212 A x A0 n N B0 B m) = (term212 A x A0 n N B0 B m).
Proof. exact (eq_refl (term212 A x A0 n N B0 B m)). Qed.
Lemma lem1306383 (m : nat) (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : ((term209 A x A0 n N B0 B m) = (term210 A x A0 n B0 B N)) = ((term209 A x A0 n N B0 B m) = (term211 A x A0 n N B0 B)).
Proof. exact (MK_COMB (@lem1306382 A x A0 n N B0 B m) (@lem1306381 A x A0 n N B0 B)). Qed.
Lemma lem1306384 (m : nat) (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term209 A x A0 n N B0 B m) = (term205 m A x A0 n N B0 B).
Proof. exact (eq_refl (term209 A x A0 n N B0 B m)). Qed.
Lemma lem1306385 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1306386 (m : nat) (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term212 A x A0 n N B0 B m) = (term213 m A x A0 n N B0 B).
Proof. exact (MK_COMB (@lem1306385) (@lem1306384 m A x A0 n N B0 B)). Qed.
Lemma lem1306387 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term211 A x A0 n N B0 B) = (term211 A x A0 n N B0 B).
Proof. exact (eq_refl (term211 A x A0 n N B0 B)). Qed.
Lemma lem1306388 (m : nat) (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : ((term209 A x A0 n N B0 B m) = (term211 A x A0 n N B0 B)) = ((term205 m A x A0 n N B0 B) = (term211 A x A0 n N B0 B)).
Proof. exact (MK_COMB (@lem1306386 m A x A0 n N B0 B) (@lem1306387 A x A0 n N B0 B)). Qed.
Lemma lem1306389 (m : nat) (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : ((term209 A x A0 n N B0 B m) = (term210 A x A0 n B0 B N)) = ((term205 m A x A0 n N B0 B) = (term211 A x A0 n N B0 B)).
Proof. exact (TRANS (@lem1306383 m A x A0 n N B0 B) (@lem1306388 m A x A0 n N B0 B)). Qed.
Lemma lem1306390 (A : nat) (x : nadd) (A0 : nat) (n : nat) (B0 : nat) (B : nat) (m : nat) (N : nat) (h1 : m = (S N)) : (term205 m A x A0 n N B0 B) = (term211 A x A0 n N B0 B).
Proof. exact (EQ_MP (@lem1306389 m A x A0 n N B0 B) (@lem1306380 A x A0 n B0 B m N h1)). Qed.
Lemma lem1306391 (A : nat) (x : nadd) (A0 : nat) (n : nat) (B0 : nat) (B : nat) (m : nat) (N : nat) (h1 : m = (S N)) : (term211 A x A0 n N B0 B) = (term205 m A x A0 n N B0 B).
Proof. exact (SYM (@lem1306390 A x A0 n B0 B m N h1)). Qed.
Lemma lem1306393 (m : nat) (p : nat) : term48 m p.
Proof. exact (EQ_MP (@lem1306155 m p) (@lem1306154 m p)). Qed.
Lemma lem1306394 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : term214 A x A0 n N B0 B.
Proof. exact (@lem1306393 (term215 n x N) (term216 A x A0 n N B0 B)). Qed.
Lemma lem1306398 (m : nat) (n : nat) : (term117 m n) = True.
Proof. exact (EQ_MP (@lem1306127 m n) (@lem1306126 m n)). Qed.
Lemma lem1306399 (n : nat) (x : nadd) (N : nat) : (term217 n x N) = True.
Proof. exact (@lem1306398 (term218 N x n) (term219 n x N)). Qed.
Lemma lem1306400 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1306401 (n : nat) (x : nadd) (N : nat) : (term220 n x N) = (and True).
Proof. exact (MK_COMB (@lem1306400) (@lem1306399 n x N)). Qed.
Lemma lem1306402 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term221 A x A0 n N B0 B) = (term221 A x A0 n N B0 B).
Proof. exact (eq_refl (term221 A x A0 n N B0 B)). Qed.
Lemma lem1306403 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term222 A x A0 n N B0 B) = (term223 A x A0 n N B0 B).
Proof. exact (MK_COMB (@lem1306401 n x N) (@lem1306402 A x A0 n N B0 B)). Qed.
Lemma lem1306405 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1306406 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term223 A x A0 n N B0 B) = (term221 A x A0 n N B0 B).
Proof. exact (@lem1306405 (term221 A x A0 n N B0 B)). Qed.
Lemma lem1306407 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term222 A x A0 n N B0 B) = (term221 A x A0 n N B0 B).
Proof. exact (TRANS (@lem1306403 A x A0 n N B0 B) (@lem1306406 A x A0 n N B0 B)). Qed.
Lemma lem1306408 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term221 A x A0 n N B0 B) = (term222 A x A0 n N B0 B).
Proof. exact (SYM (@lem1306407 A x A0 n N B0 B)). Qed.
Lemma lem1306410 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (EQ_MP (@lem1306119 m n p) (@lem1306118 m n p)). Qed.
Lemma lem1306411 (A : nat) (x : nadd) (N : nat) (A0 : nat) (n : nat) : (term224 A x N A0 n) = (term225 A x N A0 n).
Proof. exact (@lem1306410 A (term226 x N A0) n). Qed.
Lemma lem1306413 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (EQ_MP (@lem1306119 m n p) (@lem1306118 m n p)). Qed.
Lemma lem1306414 (x : nadd) (N : nat) (A0 : nat) (n : nat) : (term227 x N A0 n) = (term228 x N A0 n).
Proof. exact (@lem1306413 (term229 x N) (term230 N A0) n). Qed.
Lemma lem1306415 (A : nat) (n : nat) : (term231 A n) = (term231 A n).
Proof. exact (eq_refl (term231 A n)). Qed.
Lemma lem1306416 (A : nat) (x : nadd) (N : nat) (A0 : nat) (n : nat) : (term225 A x N A0 n) = (term232 A x N A0 n).
Proof. exact (MK_COMB (@lem1306415 A n) (@lem1306414 x N A0 n)). Qed.
Lemma lem1306417 (A : nat) (x : nadd) (N : nat) (A0 : nat) (n : nat) : (term224 A x N A0 n) = (term232 A x N A0 n).
Proof. exact (TRANS (@lem1306411 A x N A0 n) (@lem1306416 A x N A0 n)). Qed.
Lemma lem1306418 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1306419 (A : nat) (x : nadd) (N : nat) (A0 : nat) (n : nat) : (term233 A x N A0 n) = (term234 A x N A0 n).
Proof. exact (MK_COMB (@lem1306418) (@lem1306417 A x N A0 n)). Qed.
Lemma lem1306420 (N : nat) (B0 : nat) (B : nat) : (term235 N B0 B) = (term235 N B0 B).
Proof. exact (eq_refl (term235 N B0 B)). Qed.
Lemma lem1306421 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term216 A x A0 n N B0 B) = (term236 A x A0 n N B0 B).
Proof. exact (MK_COMB (@lem1306419 A x N A0 n) (@lem1306420 N B0 B)). Qed.
Lemma lem1306422 (n : nat) (x : nadd) (N : nat) : (term237 n x N) = (term237 n x N).
Proof. exact (eq_refl (term237 n x N)). Qed.
Lemma lem1306423 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term221 A x A0 n N B0 B) = (term238 A x A0 n N B0 B).
Proof. exact (MK_COMB (@lem1306422 n x N) (@lem1306421 A x A0 n N B0 B)). Qed.
Lemma lem1306424 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term238 A x A0 n N B0 B) = (term221 A x A0 n N B0 B).
Proof. exact (SYM (@lem1306423 A x A0 n N B0 B)). Qed.
Lemma lem1306426 (c : nat) (d : nat) (b : nat) (a : nat) (e : nat) : (term106 a b c d e) = (term113 c d b a e).
Proof. exact (EQ_MP (@lem1306110 c d b a e) (@lem0)). Qed.
Lemma lem1306427 (A0 : nat) (B0 : nat) (x : nadd) (N : nat) (A : nat) (n : nat) (B : nat) : (term236 A x A0 n N B0 B) = (term239 A0 B0 x N A n B).
Proof. exact (@lem1306426 (term240 N A0 n) (term230 N B0) (term241 x N n) (Nat.mul A n) B). Qed.
Lemma lem1306428 (n : nat) (x : nadd) (N : nat) : (term237 n x N) = (term237 n x N).
Proof. exact (eq_refl (term237 n x N)). Qed.
Lemma lem1306429 (A0 : nat) (B0 : nat) (x : nadd) (N : nat) (A : nat) (n : nat) (B : nat) : (term238 A x A0 n N B0 B) = (term242 A0 B0 x N A n B).
Proof. exact (MK_COMB (@lem1306428 n x N) (@lem1306427 A0 B0 x N A n B)). Qed.
Lemma lem1306430 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term242 A0 B0 x N A n B) = (term238 A x A0 n N B0 B).
Proof. exact (SYM (@lem1306429 A0 B0 x N A n B)). Qed.
Lemma lem1306432 (m : nat) (n : nat) (p : nat) (q : nat) : term99 m n p q.
Proof. exact (EQ_MP (@lem1305963 m n p q) (@lem1305962 m n p q)). Qed.
Lemma lem1306433 (A0 : nat) (B0 : nat) (x : nadd) (N : nat) (A : nat) (n : nat) (B : nat) : term243 A0 B0 x N A n B.
Proof. exact (@lem1306432 (term218 N x n) (term219 n x N) (term244 A0 n N B0) (term245 x N A n B)). Qed.
Lemma lem1306437 (m : nat) (n : nat) (p : nat) : (term72 m n p) = (term71 m n p).
Proof. exact (EQ_MP (@lem1305926 m n p) (@lem1305925 m n p)). Qed.
Lemma lem1306438 (N : nat) (A0 : nat) (n : nat) : (term240 N A0 n) = (term246 N A0 n).
Proof. exact (@lem1306437 (S N) A0 n). Qed.
Lemma lem1306439 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1306440 (N : nat) (A0 : nat) (n : nat) : (term247 N A0 n) = (term248 N A0 n).
Proof. exact (MK_COMB (@lem1306439) (@lem1306438 N A0 n)). Qed.
Lemma lem1306441 (N : nat) (B0 : nat) : (term230 N B0) = (term230 N B0).
Proof. exact (eq_refl (term230 N B0)). Qed.
Lemma lem1306442 (A0 : nat) (n : nat) (N : nat) (B0 : nat) : (term244 A0 n N B0) = (term249 A0 n N B0).
Proof. exact (MK_COMB (@lem1306440 N A0 n) (@lem1306441 N B0)). Qed.
Lemma lem1306444 (m : nat) (n : nat) (p : nat) : (term58 n m p) = (term57 m n p).
Proof. exact (EQ_MP (@lem1305917 m n p) (@lem1305916 m n p)). Qed.
Lemma lem1306445 (N : nat) (A0 : nat) (n : nat) (B0 : nat) : (term249 A0 n N B0) = (term250 N A0 n B0).
Proof. exact (@lem1306444 (S N) (Nat.mul A0 n) B0). Qed.
Lemma lem1306446 (N : nat) (A0 : nat) (n : nat) (B0 : nat) : (term244 A0 n N B0) = (term250 N A0 n B0).
Proof. exact (TRANS (@lem1306442 A0 n N B0) (@lem1306445 N A0 n B0)). Qed.
Lemma lem1306447 (N : nat) (x : nadd) (n : nat) : (term251 N x n) = (term251 N x n).
Proof. exact (eq_refl (term251 N x n)). Qed.
Lemma lem1306448 (x : nadd) (N : nat) (A0 : nat) (n : nat) (B0 : nat) : (term252 x A0 n N B0) = (term253 x N A0 n B0).
Proof. exact (MK_COMB (@lem1306447 N x n) (@lem1306446 N A0 n B0)). Qed.
Lemma lem1306449 (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) : (term253 x N A0 n B0) = (term252 x A0 n N B0).
Proof. exact (SYM (@lem1306448 x N A0 n B0)). Qed.
Lemma lem1306450 (m : nat) : term254 m.
Proof. exact (@lem104208 m). Qed.
Lemma lem1306451 (m : nat) : (term254 m) = (term255 m).
Proof. exact (eq_refl (term254 m)). Qed.
Lemma lem1306452 (m : nat) : term255 m.
Proof. exact (EQ_MP (@lem1306451 m) (@lem1306450 m)). Qed.
Lemma lem1306453 (m : nat) (n : nat) : term256 m n.
Proof. exact (@lem1306452 m n). Qed.
Lemma lem1306454 (m : nat) (n : nat) : (term256 m n) = (term257 m n).
Proof. exact (eq_refl (term256 m n)). Qed.
Lemma lem1306455 (m : nat) (n : nat) : term257 m n.
Proof. exact (EQ_MP (@lem1306454 m n) (@lem1306453 m n)). Qed.
Lemma lem1306456 (m : nat) (n : nat) (p : nat) : term258 m n p.
Proof. exact (@lem1306455 m n p). Qed.
Lemma lem1306457 (m : nat) (n : nat) (p : nat) : (term258 m n p) = ((term259 n m p) = (term260 m n p)).
Proof. exact (eq_refl (term258 m n p)). Qed.
Lemma lem1306459 (n : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : term261 x A0 B0 n.
Proof. exact (@lem1306255 x A0 B0 h1 n). Qed.
Lemma lem1306460 (x : nadd) (A0 : nat) (n : nat) (B0 : nat) : (term261 x A0 B0 n) = (term262 x A0 n B0).
Proof. exact (eq_refl (term261 x A0 B0 n)). Qed.
Lemma lem1306461 (n : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : term262 x A0 n B0.
Proof. exact (EQ_MP (@lem1306460 x A0 n B0) (@lem1306459 n x A0 B0 h1)). Qed.
Lemma lem1306462 (x : nadd) (A0 : nat) (n : nat) (B0 : nat) : (term262 x A0 n B0) = ((term262 x A0 n B0) = True).
Proof. exact (@lem7 (term262 x A0 n B0)). Qed.
Lemma lem1306475 (m : nat) (n : nat) (p : nat) : (term259 n m p) = (term260 m n p).
Proof. exact (EQ_MP (@lem1306457 m n p) (@lem1306456 m n p)). Qed.
Lemma lem1306476 (N : nat) (x : nadd) (A0 : nat) (n : nat) (B0 : nat) : (term253 x N A0 n B0) = (term263 N x A0 n B0).
Proof. exact (@lem1306475 (S N) (nadd_rinv x n) (term264 A0 n B0)). Qed.
Lemma lem1306482 (n : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : (term262 x A0 n B0) = True.
Proof. exact (EQ_MP (@lem1306462 x A0 n B0) (@lem1306461 n x A0 B0 h1)). Qed.
Lemma lem1306483 (N : nat) : (term265 N) = (term265 N).
Proof. exact (eq_refl (term265 N)). Qed.
Lemma lem1306484 (n : nat) (N : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : (term263 N x A0 n B0) = (term266 N).
Proof. exact (MK_COMB (@lem1306483 N) (@lem1306482 n x A0 B0 h1)). Qed.
Lemma lem1306486 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem1306487 (N : nat) : (term266 N) = True.
Proof. exact (@lem1306486 ((S N) = (NUMERAL 0))). Qed.
Lemma lem1306488 (N : nat) (n : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : (term263 N x A0 n B0) = True.
Proof. exact (TRANS (@lem1306484 n N x A0 B0 h1) (@lem1306487 N)). Qed.
Lemma lem1306489 (N : nat) (n : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : (term253 x N A0 n B0) = True.
Proof. exact (TRANS (@lem1306476 N x A0 n B0) (@lem1306488 N n x A0 B0 h1)). Qed.
Lemma lem1306490 (N : nat) (n : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : True = (term253 x N A0 n B0).
Proof. exact (SYM (@lem1306489 N n x A0 B0 h1)). Qed.
Lemma lem1306491 (N : nat) (n : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : term253 x N A0 n B0.
Proof. exact (EQ_MP (@lem1306490 N n x A0 B0 h1) (@lem0)). Qed.
Lemma lem1306492 (n : nat) (N : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : term252 x A0 n N B0.
Proof. exact (EQ_MP (@lem1306449 x A0 n N B0) (@lem1306491 N n x A0 B0 h1)). Qed.
Lemma lem1306494 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem1305872 n m) (@lem1305871 m n)). Qed.
Lemma lem1306495 (x : nadd) (N : nat) (n : nat) : (term219 n x N) = (term241 x N n).
Proof. exact (@lem1306494 (term229 x N) n). Qed.
Lemma lem1306496 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1306497 (x : nadd) (N : nat) (n : nat) : (term267 n x N) = (term268 x N n).
Proof. exact (MK_COMB (@lem1306496) (@lem1306495 x N n)). Qed.
Lemma lem1306498 (x : nadd) (N : nat) (A : nat) (n : nat) (B : nat) : (term245 x N A n B) = (term245 x N A n B).
Proof. exact (eq_refl (term245 x N A n B)). Qed.
Lemma lem1306499 (x : nadd) (N : nat) (A : nat) (n : nat) (B : nat) : (term269 x N A n B) = (term270 x N A n B).
Proof. exact (MK_COMB (@lem1306497 x N n) (@lem1306498 x N A n B)). Qed.
Lemma lem1306500 (x : nadd) (N : nat) (A : nat) (n : nat) (B : nat) : (term270 x N A n B) = (term269 x N A n B).
Proof. exact (SYM (@lem1306499 x N A n B)). Qed.
Lemma lem1306501 (m : nat) : term14 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1306502 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1306503 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem1306502 m) (@lem1306501 m)). Qed.
Lemma lem1306504 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem1306503 m n). Qed.
Lemma lem1306505 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1306508 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem1306505 m n) (@lem1306504 m n)). Qed.
Lemma lem1306509 (x : nadd) (N : nat) (A : nat) (n : nat) (B : nat) : term270 x N A n B.
Proof. exact (@lem1306508 (term241 x N n) (term264 A n B)). Qed.
Lemma lem1306510 (x : nadd) (N : nat) (A : nat) (n : nat) (B : nat) : term269 x N A n B.
Proof. exact (EQ_MP (@lem1306500 x N A n B) (@lem1306509 x N A n B)). Qed.
Lemma lem1306511 (N : nat) (A : nat) (n : nat) (B : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : term271 A0 B0 x N A n B.
Proof. exact (conj (@lem1306492 n N x A0 B0 h1) (@lem1306510 x N A n B)). Qed.
Lemma lem1306512 (N : nat) (A : nat) (n : nat) (B : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : term242 A0 B0 x N A n B.
Proof. exact (@lem1306433 A0 B0 x N A n B (@lem1306511 N A n B x A0 B0 h1)). Qed.
Lemma lem1306513 (A : nat) (n : nat) (N : nat) (B : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : term238 A x A0 n N B0 B.
Proof. exact (EQ_MP (@lem1306430 A x A0 n N B0 B) (@lem1306512 N A n B x A0 B0 h1)). Qed.
Lemma lem1306514 (A : nat) (n : nat) (N : nat) (B : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : term221 A x A0 n N B0 B.
Proof. exact (EQ_MP (@lem1306424 A x A0 n N B0 B) (@lem1306513 A n N B x A0 B0 h1)). Qed.
Lemma lem1306515 (A : nat) (n : nat) (N : nat) (B : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : term222 A x A0 n N B0 B.
Proof. exact (EQ_MP (@lem1306408 A x A0 n N B0 B) (@lem1306514 A n N B x A0 B0 h1)). Qed.
Lemma lem1306516 (A : nat) (n : nat) (N : nat) (B : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : term272 A x A0 n N B0 B.
Proof. exact (ex_intro (term273 A x A0 n N B0 B) (term274 n x N) (@lem1306515 A n N B x A0 B0 h1)). Qed.
Lemma lem1306517 (A : nat) (n : nat) (N : nat) (B : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : term211 A x A0 n N B0 B.
Proof. exact (@lem1306394 A x A0 n N B0 B (@lem1306516 A n N B x A0 B0 h1)). Qed.
Lemma lem1306519 (m : nat) (p : nat) : term48 m p.
Proof. exact (EQ_MP (@lem1305866 m p) (@lem1305865 m p)). Qed.
Lemma lem1306520 (m : nat) (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : term275 m A x A0 n N B0 B.
Proof. exact (@lem1306519 (term276 n x m) (term216 A x A0 n N B0 B)). Qed.
Lemma lem1306521 (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term202 N x A B) : term202 N x A B.
Proof. exact (h1). Qed.
Lemma lem1306522 (m : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term202 N x A B) : term277 N x A B m.
Proof. exact (@lem1306521 N x A B h1 m). Qed.
Lemma lem1306523 (N : nat) (x : nadd) (m : nat) (A : nat) (B : nat) : (term277 N x A B m) = (term278 N x m A B).
Proof. exact (eq_refl (term277 N x A B m)). Qed.
Lemma lem1306524 (m : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term202 N x A B) : term278 N x m A B.
Proof. exact (EQ_MP (@lem1306523 N x m A B) (@lem1306522 m N x A B h1)). Qed.
Lemma lem1306525 (m : nat) (n : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term202 N x A B) : term279 N x m A B n.
Proof. exact (@lem1306524 m N x A B h1 n). Qed.
Lemma lem1306526 (N : nat) (x : nadd) (m : nat) (A : nat) (n : nat) (B : nat) : (term279 N x m A B n) = (term280 N x m A n B).
Proof. exact (eq_refl (term279 N x m A B n)). Qed.
Lemma lem1306527 (m : nat) (n : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term202 N x A B) : term280 N x m A n B.
Proof. exact (EQ_MP (@lem1306526 N x m A n B) (@lem1306525 m n N x A B h1)). Qed.
Lemma lem1306528 (m : nat) (N : nat) (h1 : Peano.le m N) : Peano.le m N.
Proof. exact (h1). Qed.
Lemma lem1306529 (n : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term202 N x A B) (h2 : Peano.le m N) : term281 x m A n B.
Proof. exact (@lem1306527 m n N x A B h1 (@lem1306528 m N h2)). Qed.
Lemma lem1306530 (x : nadd) (A : nat) (n : nat) (B : nat) (m : nat) (N : nat) (h1 : Peano.le m N) : term282 N x m A n B.
Proof. exact (fun h0 : term202 N x A B => @lem1306529 n x A B m N h0 h1). Qed.
Lemma lem1306531 (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term202 N x A B) : term202 N x A B.
Proof. exact (h1). Qed.
Lemma lem1306532 (n : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term202 N x A B) (h2 : Peano.le m N) : term281 x m A n B.
Proof. exact (@lem1306530 x A n B m N h2 (@lem1306531 N x A B h1)). Qed.
Lemma lem1306533 (m : nat) (n : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term202 N x A B) : term280 N x m A n B.
Proof. exact (fun h0 : Peano.le m N => @lem1306532 n x A B m N h1 h0). Qed.
Lemma lem1306534 (m : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term202 N x A B) : term278 N x m A B.
Proof. exact (fun n : nat => @lem1306533 m n N x A B h1). Qed.
Lemma lem1306535 (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term202 N x A B) : term202 N x A B.
Proof. exact (fun m : nat => @lem1306534 m N x A B h1). Qed.
Lemma lem1306536 (N : nat) (x : nadd) (A : nat) (B : nat) : term283 N x A B.
Proof. exact (fun h0 : term202 N x A B => @lem1306535 N x A B h0). Qed.
Lemma lem1306537 (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term202 N x A B) : term202 N x A B.
Proof. exact (@lem1306536 N x A B (@lem1306359 N x A B h1)). Qed.
Lemma lem1306538 (m : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term202 N x A B) : term277 N x A B m.
Proof. exact (@lem1306537 N x A B h1 m). Qed.
Lemma lem1306539 (N : nat) (x : nadd) (m : nat) (A : nat) (B : nat) : (term277 N x A B m) = (term278 N x m A B).
Proof. exact (eq_refl (term277 N x A B m)). Qed.
Lemma lem1306540 (m : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term202 N x A B) : term278 N x m A B.
Proof. exact (EQ_MP (@lem1306539 N x m A B) (@lem1306538 m N x A B h1)). Qed.
Lemma lem1306541 (m : nat) (n : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term202 N x A B) : term279 N x m A B n.
Proof. exact (@lem1306540 m N x A B h1 n). Qed.
Lemma lem1306542 (N : nat) (x : nadd) (m : nat) (A : nat) (n : nat) (B : nat) : (term279 N x m A B n) = (term280 N x m A n B).
Proof. exact (eq_refl (term279 N x m A B n)). Qed.
Lemma lem1306545 (m : nat) (n : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term202 N x A B) : term280 N x m A n B.
Proof. exact (EQ_MP (@lem1306542 N x m A n B) (@lem1306541 m n N x A B h1)). Qed.
Lemma lem1306561 (m : nat) (N : nat) : (Peano.le m N) = ((Peano.le m N) = True).
Proof. exact (@lem7 (Peano.le m N)). Qed.
Lemma lem1306564 (m : nat) (N : nat) (h1 : Peano.le m N) : (Peano.le m N) = True.
Proof. exact (EQ_MP (@lem1306561 m N) (@lem1306378 m N h1)). Qed.
Lemma lem1306565 (m : nat) (N : nat) (h1 : Peano.le m N) : True = (Peano.le m N).
Proof. exact (SYM (@lem1306564 m N h1)). Qed.
Lemma lem1306566 (m : nat) (N : nat) (h1 : Peano.le m N) : Peano.le m N.
Proof. exact (EQ_MP (@lem1306565 m N h1) (@lem0)). Qed.
Lemma lem1306567 (n : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term202 N x A B) (h2 : Peano.le m N) : term281 x m A n B.
Proof. exact (@lem1306545 m n N x A B h1 (@lem1306566 m N h2)). Qed.
Lemma lem1306571 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (EQ_MP (@lem1305838 m n p) (@lem1305837 m n p)). Qed.
Lemma lem1306572 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term216 A x A0 n N B0 B) = (term284 A x A0 n N B0 B).
Proof. exact (@lem1306571 (term224 A x N A0 n) (term230 N B0) B). Qed.
Lemma lem1306574 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (EQ_MP (@lem1305838 m n p) (@lem1305837 m n p)). Qed.
Lemma lem1306575 (A : nat) (x : nadd) (N : nat) (A0 : nat) : (term285 A x N A0) = (term286 A x N A0).
Proof. exact (@lem1306574 A (term229 x N) (term230 N A0)). Qed.
Lemma lem1306576 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1306577 (A : nat) (x : nadd) (N : nat) (A0 : nat) : (term287 A x N A0) = (term288 A x N A0).
Proof. exact (MK_COMB (@lem1306576) (@lem1306575 A x N A0)). Qed.
Lemma lem1306578 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1306579 (A : nat) (x : nadd) (N : nat) (A0 : nat) (n : nat) : (term224 A x N A0 n) = (term289 A x N A0 n).
Proof. exact (MK_COMB (@lem1306577 A x N A0) (@lem1306578 n)). Qed.
Lemma lem1306580 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1306581 (A : nat) (x : nadd) (N : nat) (A0 : nat) (n : nat) : (term233 A x N A0 n) = (term290 A x N A0 n).
Proof. exact (MK_COMB (@lem1306580) (@lem1306579 A x N A0 n)). Qed.
Lemma lem1306582 (N : nat) (B0 : nat) : (term230 N B0) = (term230 N B0).
Proof. exact (eq_refl (term230 N B0)). Qed.
Lemma lem1306583 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) : (term291 A x A0 n N B0) = (term292 A x A0 n N B0).
Proof. exact (MK_COMB (@lem1306581 A x N A0 n) (@lem1306582 N B0)). Qed.
Lemma lem1306584 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1306585 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) : (term293 A x A0 n N B0) = (term294 A x A0 n N B0).
Proof. exact (MK_COMB (@lem1306584) (@lem1306583 A x A0 n N B0)). Qed.
Lemma lem1306586 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1306587 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term284 A x A0 n N B0 B) = (term295 A x A0 n N B0 B).
Proof. exact (MK_COMB (@lem1306585 A x A0 n N B0) (@lem1306586 B)). Qed.
Lemma lem1306588 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term216 A x A0 n N B0 B) = (term295 A x A0 n N B0 B).
Proof. exact (TRANS (@lem1306572 A x A0 n N B0 B) (@lem1306587 A x A0 n N B0 B)). Qed.
Lemma lem1306589 (A : nat) (n : nat) (B : nat) : (term296 A n B) = (term296 A n B).
Proof. exact (eq_refl (term296 A n B)). Qed.
Lemma lem1306590 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term297 A x A0 n N B0 B) = (term298 A x A0 n N B0 B).
Proof. exact (MK_COMB (@lem1306589 A n B) (@lem1306588 A x A0 n N B0 B)). Qed.
Lemma lem1306592 (p : nat) (m : nat) (n : nat) : (term33 m n p) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1305829 p m n) (@lem1305828 m n p)). Qed.
Lemma lem1306593 (B : nat) (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) : (term298 A x A0 n N B0 B) = (term299 A x A0 n N B0).
Proof. exact (@lem1306592 B (Nat.mul A n) (term292 A x A0 n N B0)). Qed.
Lemma lem1306594 (B : nat) (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) : (term297 A x A0 n N B0 B) = (term299 A x A0 n N B0).
Proof. exact (TRANS (@lem1306590 A x A0 n N B0 B) (@lem1306593 B A x A0 n N B0)). Qed.
Lemma lem1306595 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : (term299 A x A0 n N B0) = (term297 A x A0 n N B0 B).
Proof. exact (SYM (@lem1306594 B A x A0 n N B0)). Qed.
Lemma lem1306599 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (EQ_MP (@lem1305820 m n p) (@lem1305819 m n p)). Qed.
Lemma lem1306600 (A : nat) (x : nadd) (N : nat) (A0 : nat) (n : nat) : (term289 A x N A0 n) = (term300 A x N A0 n).
Proof. exact (@lem1306599 (term301 A x N) (term230 N A0) n). Qed.
Lemma lem1306602 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (EQ_MP (@lem1305820 m n p) (@lem1305819 m n p)). Qed.
Lemma lem1306603 (A : nat) (x : nadd) (N : nat) (n : nat) : (term302 A x N n) = (term303 A x N n).
Proof. exact (@lem1306602 A (term229 x N) n). Qed.
Lemma lem1306604 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1306605 (A : nat) (x : nadd) (N : nat) (n : nat) : (term304 A x N n) = (term305 A x N n).
Proof. exact (MK_COMB (@lem1306604) (@lem1306603 A x N n)). Qed.
Lemma lem1306606 (N : nat) (A0 : nat) (n : nat) : (term240 N A0 n) = (term240 N A0 n).
Proof. exact (eq_refl (term240 N A0 n)). Qed.
Lemma lem1306607 (A : nat) (x : nadd) (N : nat) (A0 : nat) (n : nat) : (term300 A x N A0 n) = (term306 A x N A0 n).
Proof. exact (MK_COMB (@lem1306605 A x N n) (@lem1306606 N A0 n)). Qed.
Lemma lem1306609 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem1305811 m n p) (@lem1305810 m n p)). Qed.
Lemma lem1306610 (A : nat) (x : nadd) (N : nat) (A0 : nat) (n : nat) : (term306 A x N A0 n) = (term232 A x N A0 n).
Proof. exact (@lem1306609 (Nat.mul A n) (term241 x N n) (term240 N A0 n)). Qed.
Lemma lem1306611 (A : nat) (x : nadd) (N : nat) (A0 : nat) (n : nat) : (term300 A x N A0 n) = (term232 A x N A0 n).
Proof. exact (TRANS (@lem1306607 A x N A0 n) (@lem1306610 A x N A0 n)). Qed.
Lemma lem1306612 (A : nat) (x : nadd) (N : nat) (A0 : nat) (n : nat) : (term289 A x N A0 n) = (term232 A x N A0 n).
Proof. exact (TRANS (@lem1306600 A x N A0 n) (@lem1306611 A x N A0 n)). Qed.
Lemma lem1306613 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1306614 (A : nat) (x : nadd) (N : nat) (A0 : nat) (n : nat) : (term290 A x N A0 n) = (term234 A x N A0 n).
Proof. exact (MK_COMB (@lem1306613) (@lem1306612 A x N A0 n)). Qed.
Lemma lem1306615 (N : nat) (B0 : nat) : (term230 N B0) = (term230 N B0).
Proof. exact (eq_refl (term230 N B0)). Qed.
Lemma lem1306616 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) : (term292 A x A0 n N B0) = (term307 A x A0 n N B0).
Proof. exact (MK_COMB (@lem1306614 A x N A0 n) (@lem1306615 N B0)). Qed.
Lemma lem1306618 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem1305811 m n p) (@lem1305810 m n p)). Qed.
Lemma lem1306619 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) : (term307 A x A0 n N B0) = (term308 A x A0 n N B0).
Proof. exact (@lem1306618 (Nat.mul A n) (term228 x N A0 n) (term230 N B0)). Qed.
Lemma lem1306621 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem1305811 m n p) (@lem1305810 m n p)). Qed.
Lemma lem1306622 (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) : (term309 x A0 n N B0) = (term310 x A0 n N B0).
Proof. exact (@lem1306621 (term241 x N n) (term240 N A0 n) (term230 N B0)). Qed.
Lemma lem1306623 (A : nat) (n : nat) : (term231 A n) = (term231 A n).
Proof. exact (eq_refl (term231 A n)). Qed.
Lemma lem1306624 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) : (term308 A x A0 n N B0) = (term311 A x A0 n N B0).
Proof. exact (MK_COMB (@lem1306623 A n) (@lem1306622 x A0 n N B0)). Qed.
Lemma lem1306625 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) : (term307 A x A0 n N B0) = (term311 A x A0 n N B0).
Proof. exact (TRANS (@lem1306619 A x A0 n N B0) (@lem1306624 A x A0 n N B0)). Qed.
Lemma lem1306626 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) : (term292 A x A0 n N B0) = (term311 A x A0 n N B0).
Proof. exact (TRANS (@lem1306616 A x A0 n N B0) (@lem1306625 A x A0 n N B0)). Qed.
Lemma lem1306627 (A : nat) (n : nat) : (term312 A n) = (term312 A n).
Proof. exact (eq_refl (term312 A n)). Qed.
Lemma lem1306628 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) : (term299 A x A0 n N B0) = (term313 A x A0 n N B0).
Proof. exact (MK_COMB (@lem1306627 A n) (@lem1306626 A x A0 n N B0)). Qed.
Lemma lem1306630 (m : nat) (n : nat) : (term17 m n) = True.
Proof. exact (EQ_MP (@lem1305802 m n) (@lem1305801 m n)). Qed.
Lemma lem1306631 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) : (term313 A x A0 n N B0) = True.
Proof. exact (@lem1306630 (Nat.mul A n) (term310 x A0 n N B0)). Qed.
Lemma lem1306632 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) : (term299 A x A0 n N B0) = True.
Proof. exact (TRANS (@lem1306628 A x A0 n N B0) (@lem1306631 A x A0 n N B0)). Qed.
Lemma lem1306633 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) : True = (term299 A x A0 n N B0).
Proof. exact (SYM (@lem1306632 A x A0 n N B0)). Qed.
Lemma lem1306634 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) : term299 A x A0 n N B0.
Proof. exact (EQ_MP (@lem1306633 A x A0 n N B0) (@lem0)). Qed.
Lemma lem1306635 (A : nat) (x : nadd) (A0 : nat) (n : nat) (N : nat) (B0 : nat) (B : nat) : term297 A x A0 n N B0 B.
Proof. exact (EQ_MP (@lem1306595 A x A0 n N B0 B) (@lem1306634 A x A0 n N B0)). Qed.
Lemma lem1306636 (A0 : nat) (n : nat) (B0 : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term202 N x A B) (h2 : Peano.le m N) : term314 m A x A0 n N B0 B.
Proof. exact (conj (@lem1306567 n x A B m N h1 h2) (@lem1306635 A x A0 n N B0 B)). Qed.
Lemma lem1306637 (A0 : nat) (n : nat) (B0 : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term202 N x A B) (h2 : Peano.le m N) : term315 m A x A0 n N B0 B.
Proof. exact (ex_intro (term316 m A x A0 n N B0 B) (term264 A n B) (@lem1306636 A0 n B0 x A B m N h1 h2)). Qed.
Lemma lem1306638 (A0 : nat) (n : nat) (B0 : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term202 N x A B) (h2 : Peano.le m N) : term205 m A x A0 n N B0 B.
Proof. exact (@lem1306520 m A x A0 n N B0 B (@lem1306637 A0 n B0 x A B m N h1 h2)). Qed.
Lemma lem1306639 (A0 : nat) (n : nat) (B0 : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term202 N x A B) (h2 : Peano.le m N) : (Peano.le m N) = (term205 m A x A0 n N B0 B).
Proof. exact (prop_ext (fun h3 : Peano.le m N => @lem1306638 A0 n B0 x A B m N h1 h2) (fun h3 : term205 m A x A0 n N B0 B => @lem1306378 m N h2)). Qed.
Lemma lem1306640 (A0 : nat) (n : nat) (B0 : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term202 N x A B) (h2 : Peano.le m N) : term205 m A x A0 n N B0 B.
Proof. exact (EQ_MP (@lem1306639 A0 n B0 x A B m N h1 h2) (@lem1306378 m N h2)). Qed.
Lemma lem1306641 (A : nat) (n : nat) (B : nat) (x : nadd) (A0 : nat) (B0 : nat) (m : nat) (N : nat) (h1 : term141 x A0 B0) (h2 : m = (S N)) : term205 m A x A0 n N B0 B.
Proof. exact (EQ_MP (@lem1306391 A x A0 n B0 B m N h2) (@lem1306517 A n N B x A0 B0 h1)). Qed.
Lemma lem1306642 (n : nat) (A : nat) (B : nat) (x : nadd) (A0 : nat) (B0 : nat) (m : nat) (N : nat) (h1 : term202 N x A B) (h2 : term141 x A0 B0) (h3 : term123 m N) : term205 m A x A0 n N B0 B.
Proof. exact (or_elim (@lem1306376 m N h3) (fun h0 : m = (S N) => @lem1306641 A n B x A0 B0 m N h2 h0) (fun h0 : Peano.le m N => @lem1306640 A0 n B0 x A B m N h1 h0)). Qed.
Lemma lem1306643 (m : nat) (n : nat) (N : nat) (A : nat) (B : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term202 N x A B) (h2 : term141 x A0 B0) : term207 m A x A0 n N B0 B.
Proof. exact (fun h0 : term123 m N => @lem1306642 n A B x A0 B0 m N h1 h2 h0). Qed.
Lemma lem1306644 (m : nat) (n : nat) (N : nat) (A : nat) (B : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term202 N x A B) (h2 : term141 x A0 B0) : term206 m A x A0 n N B0 B.
Proof. exact (EQ_MP (@lem1306375 m A x A0 n N B0 B) (@lem1306643 m n N A B x A0 B0 h1 h2)). Qed.
Lemma lem1306649 (m : nat) (N : nat) (A : nat) (B : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term202 N x A B) (h2 : term141 x A0 B0) : term317 m A x A0 N B0 B.
Proof. exact (fun n : nat => @lem1306644 m n N A B x A0 B0 h1 h2). Qed.
Lemma lem1306654 (N : nat) (A : nat) (B : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term202 N x A B) (h2 : term141 x A0 B0) : term318 A x A0 N B0 B.
Proof. exact (fun m : nat => @lem1306649 m N A B x A0 B0 h1 h2). Qed.
Lemma lem1306655 (N : nat) (A : nat) (B : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term202 N x A B) (h2 : term141 x A0 B0) : term319 A x N A0.
Proof. exact (ex_intro (term320 A x N A0) (term235 N B0 B) (@lem1306654 N A B x A0 B0 h1 h2)). Qed.
Lemma lem1306656 (N : nat) (A : nat) (B : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term202 N x A B) (h2 : term141 x A0 B0) : term154 N x.
Proof. exact (ex_intro (term321 N x) (term285 A x N A0) (@lem1306655 N A B x A0 B0 h1 h2)). Qed.
Lemma lem1306657 (A0 : nat) (B0 : nat) (N : nat) (x : nadd) (A : nat) (h1 : term141 x A0 B0) (h2 : term201 N x A) : term154 N x.
Proof. exact (ex_elim (@lem1306358 N x A h2) (fun B : nat => fun h0 : term322 N x A B => @lem1306656 N A B x A0 B0 h0 h1)). Qed.
Lemma lem1306658 (A0 : nat) (B0 : nat) (N : nat) (x : nadd) (h1 : term141 x A0 B0) (h2 : term150 N x) : term154 N x.
Proof. exact (ex_elim (@lem1306279 N x h2) (fun A : nat => fun h0 : term323 N x A => @lem1306657 A0 B0 N x A h1 h0)). Qed.
Lemma lem1306659 (N : nat) (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : term156 N x.
Proof. exact (fun h0 : term150 N x => @lem1306658 A0 B0 N x h1 h0). Qed.
Lemma lem1306664 (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : term160 x.
Proof. exact (fun N : nat => @lem1306659 N x A0 B0 h1). Qed.
Lemma lem1306665 (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : term162 x.
Proof. exact (conj (@lem1306357 x) (@lem1306664 x A0 B0 h1)). Qed.
Lemma lem1306666 (x : nadd) (A0 : nat) (B0 : nat) (h1 : term141 x A0 B0) : term167 x.
Proof. exact (@lem1306278 x (@lem1306665 x A0 B0 h1)). Qed.
Lemma lem1306667 (x : nadd) (A0 : nat) (h1 : term140 x A0) : term167 x.
Proof. exact (ex_elim (@lem1306254 x A0 h1) (fun B0 : nat => fun h0 : term324 x A0 B0 => @lem1306666 x A0 B0 h0)). Qed.
Lemma lem1306668 (x : nadd) (h1 : term139 x) : term167 x.
Proof. exact (ex_elim (@lem1306253 x h1) (fun A0 : nat => fun h0 : term325 x A0 => @lem1306667 x A0 h0)). Qed.
Lemma lem1306669 (x : nadd) : term326 x.
Proof. exact (fun h0 : term139 x => @lem1306668 x h0). Qed.
Lemma lem1306670 (x : nadd) (h1 : term138 x) : term167 x.
Proof. exact (@lem1306669 x (@lem1306252 x h1)). Qed.
Lemma lem1306671 (x : nadd) : term327 x.
Proof. exact (fun h0 : term138 x => @lem1306670 x h0). Qed.
Lemma lem1306676 : term328.
Proof. exact (fun x : nadd => @lem1306671 x). Qed.
