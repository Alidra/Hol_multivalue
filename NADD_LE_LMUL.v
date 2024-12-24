Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_LE_LMUL_term_abbrevs.
Require Import NADD_EQ_IMP_LE_spec.
Require Import NADD_EQ_REFL_spec.
Require Import NADD_EQ_SYM_spec.
Require Import NADD_EQ_TRANS_spec.
Require Import NADD_LDISTRIB_spec.
Require Import NADD_LE_ADD_spec.
Require Import NADD_LE_EXISTS_spec.
Require Import NADD_LE_TRANS_spec.
Require Import NADD_MUL_WELLDEF_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1279764 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1279765 (x : nadd) (h1 : term0) : term1 x.
Proof. exact (@lem1279764 h1 x). Qed.
Lemma lem1279766 (x : nadd) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1279767 (x : nadd) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1279766 x) (@lem1279765 x h1)). Qed.
Lemma lem1279768 (x : nadd) (x' : nadd) (h1 : term0) : term3 x x'.
Proof. exact (@lem1279767 x h1 x'). Qed.
Lemma lem1279769 (x : nadd) (x' : nadd) : (term3 x x') = (term4 x x').
Proof. exact (eq_refl (term3 x x')). Qed.
Lemma lem1279770 (x : nadd) (x' : nadd) (h1 : term0) : term4 x x'.
Proof. exact (EQ_MP (@lem1279769 x x') (@lem1279768 x x' h1)). Qed.
Lemma lem1279771 (x : nadd) (x' : nadd) (y : nadd) (h1 : term0) : term5 x x' y.
Proof. exact (@lem1279770 x x' h1 y). Qed.
Lemma lem1279772 (x : nadd) (y : nadd) (x' : nadd) : (term5 x x' y) = (term6 x y x').
Proof. exact (eq_refl (term5 x x' y)). Qed.
Lemma lem1279773 (x : nadd) (y : nadd) (x' : nadd) (h1 : term0) : term6 x y x'.
Proof. exact (EQ_MP (@lem1279772 x y x') (@lem1279771 x x' y h1)). Qed.
Lemma lem1279774 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : term0) : term7 x y x' y'.
Proof. exact (@lem1279773 x y x' h1 y'). Qed.
Lemma lem1279775 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term7 x y x' y') = (term8 x y x' y').
Proof. exact (eq_refl (term7 x y x' y')). Qed.
Lemma lem1279776 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : term0) : term8 x y x' y'.
Proof. exact (EQ_MP (@lem1279775 x y x' y') (@lem1279774 x y x' y' h1)). Qed.
Lemma lem1279777 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term9 x x' y y') : term9 x x' y y'.
Proof. exact (h1). Qed.
Lemma lem1279778 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term0) (h2 : term9 x x' y y') : term10 x y x' y'.
Proof. exact (@lem1279776 x y x' y' h1 (@lem1279777 x x' y y' h2)). Qed.
Lemma lem1279779 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term9 x x' y y') : term11 x y x' y'.
Proof. exact (fun h0 : term0 => @lem1279778 x x' y y' h0 h1). Qed.
Lemma lem1279780 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1279781 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) (h1 : term0) (h2 : term9 x x' y y') : term10 x y x' y'.
Proof. exact (@lem1279779 x x' y y' h2 (@lem1279780 h1)). Qed.
Lemma lem1279782 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) (h1 : term0) : term8 x y x' y'.
Proof. exact (fun h0 : term9 x x' y y' => @lem1279781 x x' y y' h1 h0). Qed.
Lemma lem1279783 (x : nadd) (y : nadd) (x' : nadd) (h1 : term0) : term6 x y x'.
Proof. exact (fun y' : nadd => @lem1279782 x y x' y' h1). Qed.
Lemma lem1279784 (x : nadd) (y : nadd) (h1 : term0) : term12 x y.
Proof. exact (fun x' : nadd => @lem1279783 x y x' h1). Qed.
Lemma lem1279785 (x : nadd) (h1 : term0) : term13 x.
Proof. exact (fun y : nadd => @lem1279784 x y h1). Qed.
Lemma lem1279786 (h1 : term0) : term14.
Proof. exact (fun x : nadd => @lem1279785 x h1). Qed.
Lemma lem1279787 : term15.
Proof. exact (fun h0 : term0 => @lem1279786 h0). Qed.
Lemma lem1279788 : term14.
Proof. exact (@lem1279787 (@lem1279298)). Qed.
Lemma lem1279789 (x : nadd) : term16 x.
Proof. exact (@lem1279788 x). Qed.
Lemma lem1279790 (x : nadd) : (term16 x) = (term13 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1279791 (x : nadd) : term13 x.
Proof. exact (EQ_MP (@lem1279790 x) (@lem1279789 x)). Qed.
Lemma lem1279792 (x : nadd) (y : nadd) : term17 x y.
Proof. exact (@lem1279791 x y). Qed.
Lemma lem1279793 (x : nadd) (y : nadd) : (term17 x y) = (term12 x y).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1279794 (x : nadd) (y : nadd) : term12 x y.
Proof. exact (EQ_MP (@lem1279793 x y) (@lem1279792 x y)). Qed.
Lemma lem1279795 (x : nadd) (y : nadd) (x' : nadd) : term18 x y x'.
Proof. exact (@lem1279794 x y x'). Qed.
Lemma lem1279796 (x : nadd) (y : nadd) (x' : nadd) : (term18 x y x') = (term6 x y x').
Proof. exact (eq_refl (term18 x y x')). Qed.
Lemma lem1279797 (x : nadd) (y : nadd) (x' : nadd) : term6 x y x'.
Proof. exact (EQ_MP (@lem1279796 x y x') (@lem1279795 x y x')). Qed.
Lemma lem1279798 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term7 x y x' y'.
Proof. exact (@lem1279797 x y x' y'). Qed.
Lemma lem1279799 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term7 x y x' y') = (term8 x y x' y').
Proof. exact (eq_refl (term7 x y x' y')). Qed.
Lemma lem1279801 (x : nadd) : term19 x.
Proof. exact (@lem1278840 x). Qed.
Lemma lem1279802 (x : nadd) : (term19 x) = (term20 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1279803 (x : nadd) : term20 x.
Proof. exact (EQ_MP (@lem1279802 x) (@lem1279801 x)). Qed.
Lemma lem1279804 (x : nadd) (y : nadd) : term21 x y.
Proof. exact (@lem1279803 x y). Qed.
Lemma lem1279805 (y : nadd) (x : nadd) : (term21 x y) = (term22 y x).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1279806 (y : nadd) (x : nadd) : term22 y x.
Proof. exact (EQ_MP (@lem1279805 y x) (@lem1279804 x y)). Qed.
Lemma lem1279807 (y : nadd) (x : nadd) (z : nadd) : term23 y x z.
Proof. exact (@lem1279806 y x z). Qed.
Lemma lem1279808 (y : nadd) (x : nadd) (z : nadd) : (term23 y x z) = (term24 y x z).
Proof. exact (eq_refl (term23 y x z)). Qed.
Lemma lem1279809 (y : nadd) (x : nadd) (z : nadd) : term24 y x z.
Proof. exact (EQ_MP (@lem1279808 y x z) (@lem1279807 y x z)). Qed.
Lemma lem1279810 (y : nadd) (x : nadd) (z : nadd) : (term24 y x z) = ((term24 y x z) = True).
Proof. exact (@lem7 (term24 y x z)). Qed.
Lemma lem1279812 (x : nadd) : term25 x.
Proof. exact (@lem1268060 x). Qed.
Lemma lem1279813 (x : nadd) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1279814 (x : nadd) : term26 x.
Proof. exact (EQ_MP (@lem1279813 x) (@lem1279812 x)). Qed.
Lemma lem1279815 (x : nadd) (y : nadd) : term27 x y.
Proof. exact (@lem1279814 x y). Qed.
Lemma lem1279816 (y : nadd) (x : nadd) : (term27 x y) = ((nadd_eq x y) = (nadd_eq y x)).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1279818 (h1 : term28) : term28.
Proof. exact (h1). Qed.
Lemma lem1279819 (x : nadd) (h1 : term28) : term29 x.
Proof. exact (@lem1279818 h1 x). Qed.
Lemma lem1279820 (x : nadd) : (term29 x) = (term30 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1279821 (x : nadd) (h1 : term28) : term30 x.
Proof. exact (EQ_MP (@lem1279820 x) (@lem1279819 x h1)). Qed.
Lemma lem1279822 (x : nadd) (y : nadd) (h1 : term28) : term31 x y.
Proof. exact (@lem1279821 x h1 y). Qed.
Lemma lem1279823 (y : nadd) (x : nadd) : (term31 x y) = (term32 y x).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1279824 (y : nadd) (x : nadd) (h1 : term28) : term32 y x.
Proof. exact (EQ_MP (@lem1279823 y x) (@lem1279822 x y h1)). Qed.
Lemma lem1279825 (y : nadd) (x : nadd) (z : nadd) (h1 : term28) : term33 y x z.
Proof. exact (@lem1279824 y x h1 z). Qed.
Lemma lem1279826 (y : nadd) (x : nadd) (z : nadd) : (term33 y x z) = (term34 y x z).
Proof. exact (eq_refl (term33 y x z)). Qed.
Lemma lem1279827 (y : nadd) (x : nadd) (z : nadd) (h1 : term28) : term34 y x z.
Proof. exact (EQ_MP (@lem1279826 y x z) (@lem1279825 y x z h1)). Qed.
Lemma lem1279828 (x : nadd) (y : nadd) (z : nadd) (h1 : term35 x y z) : term35 x y z.
Proof. exact (h1). Qed.
Lemma lem1279829 (x : nadd) (y : nadd) (z : nadd) (h1 : term28) (h2 : term35 x y z) : nadd_eq x z.
Proof. exact (@lem1279827 y x z h1 (@lem1279828 x y z h2)). Qed.
Lemma lem1279830 (x : nadd) (y : nadd) (z : nadd) (h1 : term35 x y z) : term36 x z.
Proof. exact (fun h0 : term28 => @lem1279829 x y z h0 h1). Qed.
Lemma lem1279831 (x : nadd) (z : nadd) (h1 : term37 x z) : term37 x z.
Proof. exact (h1). Qed.
Lemma lem1279832 (x : nadd) (z : nadd) (h1 : term37 x z) : term36 x z.
Proof. exact (ex_elim (@lem1279831 x z h1) (fun y : nadd => fun h0 : term38 x z y => @lem1279830 x y z h0)). Qed.
Lemma lem1279833 (h1 : term28) : term28.
Proof. exact (h1). Qed.
Lemma lem1279834 (x : nadd) (z : nadd) (h1 : term28) (h2 : term37 x z) : nadd_eq x z.
Proof. exact (@lem1279832 x z h2 (@lem1279833 h1)). Qed.
Lemma lem1279835 (x : nadd) (z : nadd) (h1 : term28) : term39 x z.
Proof. exact (fun h0 : term37 x z => @lem1279834 x z h1 h0). Qed.
Lemma lem1279836 (x : nadd) (h1 : term28) : term40 x.
Proof. exact (fun z : nadd => @lem1279835 x z h1). Qed.
Lemma lem1279837 (h1 : term28) : term41.
Proof. exact (fun x : nadd => @lem1279836 x h1). Qed.
Lemma lem1279838 : term42.
Proof. exact (fun h0 : term28 => @lem1279837 h0). Qed.
Lemma lem1279839 : term41.
Proof. exact (@lem1279838 (@lem1268295)). Qed.
Lemma lem1279840 (x : nadd) : term43 x.
Proof. exact (@lem1279839 x). Qed.
Lemma lem1279841 (x : nadd) : (term43 x) = (term40 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1279842 (x : nadd) : term40 x.
Proof. exact (EQ_MP (@lem1279841 x) (@lem1279840 x)). Qed.
Lemma lem1279843 (x : nadd) (z : nadd) : term44 x z.
Proof. exact (@lem1279842 x z). Qed.
Lemma lem1279844 (x : nadd) (z : nadd) : (term44 x z) = (term39 x z).
Proof. exact (eq_refl (term44 x z)). Qed.
Lemma lem1279846 (h1 : term45) : term45.
Proof. exact (h1). Qed.
Lemma lem1279847 (x : nadd) (h1 : term45) : term46 x.
Proof. exact (@lem1279846 h1 x). Qed.
Lemma lem1279848 (x : nadd) : (term46 x) = (term47 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1279849 (x : nadd) (h1 : term45) : term47 x.
Proof. exact (EQ_MP (@lem1279848 x) (@lem1279847 x h1)). Qed.
Lemma lem1279850 (x : nadd) (y : nadd) (h1 : term45) : term48 x y.
Proof. exact (@lem1279849 x h1 y). Qed.
Lemma lem1279851 (x : nadd) (y : nadd) : (term48 x y) = (term49 x y).
Proof. exact (eq_refl (term48 x y)). Qed.
Lemma lem1279852 (x : nadd) (y : nadd) (h1 : term45) : term49 x y.
Proof. exact (EQ_MP (@lem1279851 x y) (@lem1279850 x y h1)). Qed.
Lemma lem1279853 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : nadd_eq x y.
Proof. exact (h1). Qed.
Lemma lem1279854 (x : nadd) (y : nadd) (h1 : term45) (h2 : nadd_eq x y) : nadd_le x y.
Proof. exact (@lem1279852 x y h1 (@lem1279853 x y h2)). Qed.
Lemma lem1279855 (x : nadd) (y : nadd) (h1 : nadd_eq x y) : term50 x y.
Proof. exact (fun h0 : term45 => @lem1279854 x y h0 h1). Qed.
Lemma lem1279856 (h1 : term45) : term45.
Proof. exact (h1). Qed.
Lemma lem1279857 (x : nadd) (y : nadd) (h1 : term45) (h2 : nadd_eq x y) : nadd_le x y.
Proof. exact (@lem1279855 x y h2 (@lem1279856 h1)). Qed.
Lemma lem1279858 (x : nadd) (y : nadd) (h1 : term45) : term49 x y.
Proof. exact (fun h0 : nadd_eq x y => @lem1279857 x y h1 h0). Qed.
Lemma lem1279859 (x : nadd) (h1 : term45) : term47 x.
Proof. exact (fun y : nadd => @lem1279858 x y h1). Qed.
Lemma lem1279860 (h1 : term45) : term45.
Proof. exact (fun x : nadd => @lem1279859 x h1). Qed.
Lemma lem1279861 : term51.
Proof. exact (fun h0 : term45 => @lem1279860 h0). Qed.
Lemma lem1279862 : term45.
Proof. exact (@lem1279861 (@lem1279763)). Qed.
Lemma lem1279863 (x : nadd) : term46 x.
Proof. exact (@lem1279862 x). Qed.
Lemma lem1279864 (x : nadd) : (term46 x) = (term47 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1279865 (x : nadd) : term47 x.
Proof. exact (EQ_MP (@lem1279864 x) (@lem1279863 x)). Qed.
Lemma lem1279866 (x : nadd) (y : nadd) : term48 x y.
Proof. exact (@lem1279865 x y). Qed.
Lemma lem1279867 (x : nadd) (y : nadd) : (term48 x y) = (term49 x y).
Proof. exact (eq_refl (term48 x y)). Qed.
Lemma lem1279869 (x : nadd) : term52 x.
Proof. exact (@lem1275082 x). Qed.
Lemma lem1279870 (x : nadd) : (term52 x) = (term53 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1279871 (x : nadd) : term53 x.
Proof. exact (EQ_MP (@lem1279870 x) (@lem1279869 x)). Qed.
Lemma lem1279872 (x : nadd) (y : nadd) : term54 x y.
Proof. exact (@lem1279871 x y). Qed.
Lemma lem1279873 (x : nadd) (y : nadd) : (term54 x y) = (term55 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1279874 (x : nadd) (y : nadd) : term55 x y.
Proof. exact (EQ_MP (@lem1279873 x y) (@lem1279872 x y)). Qed.
Lemma lem1279875 (x : nadd) (y : nadd) : (term55 x y) = ((term55 x y) = True).
Proof. exact (@lem7 (term55 x y)). Qed.
Lemma lem1279877 (h1 : term56) : term56.
Proof. exact (h1). Qed.
Lemma lem1279878 (x : nadd) (h1 : term56) : term57 x.
Proof. exact (@lem1279877 h1 x). Qed.
Lemma lem1279879 (x : nadd) : (term57 x) = (term58 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1279880 (x : nadd) (h1 : term56) : term58 x.
Proof. exact (EQ_MP (@lem1279879 x) (@lem1279878 x h1)). Qed.
Lemma lem1279881 (x : nadd) (y : nadd) (h1 : term56) : term59 x y.
Proof. exact (@lem1279880 x h1 y). Qed.
Lemma lem1279882 (y : nadd) (x : nadd) : (term59 x y) = (term60 y x).
Proof. exact (eq_refl (term59 x y)). Qed.
Lemma lem1279883 (y : nadd) (x : nadd) (h1 : term56) : term60 y x.
Proof. exact (EQ_MP (@lem1279882 y x) (@lem1279881 x y h1)). Qed.
Lemma lem1279884 (y : nadd) (x : nadd) (z : nadd) (h1 : term56) : term61 y x z.
Proof. exact (@lem1279883 y x h1 z). Qed.
Lemma lem1279885 (y : nadd) (x : nadd) (z : nadd) : (term61 y x z) = (term62 y x z).
Proof. exact (eq_refl (term61 y x z)). Qed.
Lemma lem1279886 (y : nadd) (x : nadd) (z : nadd) (h1 : term56) : term62 y x z.
Proof. exact (EQ_MP (@lem1279885 y x z) (@lem1279884 y x z h1)). Qed.
Lemma lem1279887 (x : nadd) (y : nadd) (z : nadd) (h1 : term63 x y z) : term63 x y z.
Proof. exact (h1). Qed.
Lemma lem1279888 (x : nadd) (y : nadd) (z : nadd) (h1 : term56) (h2 : term63 x y z) : nadd_le x z.
Proof. exact (@lem1279886 y x z h1 (@lem1279887 x y z h2)). Qed.
Lemma lem1279889 (x : nadd) (y : nadd) (z : nadd) (h1 : term63 x y z) : term64 x z.
Proof. exact (fun h0 : term56 => @lem1279888 x y z h0 h1). Qed.
Lemma lem1279890 (x : nadd) (z : nadd) (h1 : term65 x z) : term65 x z.
Proof. exact (h1). Qed.
Lemma lem1279891 (x : nadd) (z : nadd) (h1 : term65 x z) : term64 x z.
Proof. exact (ex_elim (@lem1279890 x z h1) (fun y : nadd => fun h0 : term66 x z y => @lem1279889 x y z h0)). Qed.
Lemma lem1279892 (h1 : term56) : term56.
Proof. exact (h1). Qed.
Lemma lem1279893 (x : nadd) (z : nadd) (h1 : term56) (h2 : term65 x z) : nadd_le x z.
Proof. exact (@lem1279891 x z h2 (@lem1279892 h1)). Qed.
Lemma lem1279894 (x : nadd) (z : nadd) (h1 : term56) : term67 x z.
Proof. exact (fun h0 : term65 x z => @lem1279893 x z h1 h0). Qed.
Lemma lem1279895 (x : nadd) (h1 : term56) : term68 x.
Proof. exact (fun z : nadd => @lem1279894 x z h1). Qed.
Lemma lem1279896 (h1 : term56) : term69.
Proof. exact (fun x : nadd => @lem1279895 x h1). Qed.
Lemma lem1279897 : term70.
Proof. exact (fun h0 : term56 => @lem1279896 h0). Qed.
Lemma lem1279898 : term69.
Proof. exact (@lem1279897 (@lem1270880)). Qed.
Lemma lem1279899 (x : nadd) : term71 x.
Proof. exact (@lem1279898 x). Qed.
Lemma lem1279900 (x : nadd) : (term71 x) = (term68 x).
Proof. exact (eq_refl (term71 x)). Qed.
Lemma lem1279901 (x : nadd) : term68 x.
Proof. exact (EQ_MP (@lem1279900 x) (@lem1279899 x)). Qed.
Lemma lem1279902 (x : nadd) (z : nadd) : term72 x z.
Proof. exact (@lem1279901 x z). Qed.
Lemma lem1279903 (x : nadd) (z : nadd) : (term72 x z) = (term67 x z).
Proof. exact (eq_refl (term72 x z)). Qed.
Lemma lem1279905 (x : nadd) : term73 x.
Proof. exact (@lem1276037 x). Qed.
Lemma lem1279906 (x : nadd) : (term73 x) = (term74 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1279907 (x : nadd) : term74 x.
Proof. exact (EQ_MP (@lem1279906 x) (@lem1279905 x)). Qed.
Lemma lem1279908 (x : nadd) (y : nadd) : term75 x y.
Proof. exact (@lem1279907 x y). Qed.
Lemma lem1279909 (y : nadd) (x : nadd) : (term75 x y) = (term76 y x).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem1279911 (y : nadd) (z : nadd) (h1 : nadd_le y z) : nadd_le y z.
Proof. exact (h1). Qed.
Lemma lem1279913 (y : nadd) (x : nadd) : term76 y x.
Proof. exact (EQ_MP (@lem1279909 y x) (@lem1279908 x y)). Qed.
Lemma lem1279914 (z : nadd) (y : nadd) : term76 z y.
Proof. exact (@lem1279913 z y). Qed.
Lemma lem1279915 (y : nadd) (z : nadd) (h1 : nadd_le y z) : term77 z y.
Proof. exact (@lem1279914 z y (@lem1279911 y z h1)). Qed.
Lemma lem1279916 (z : nadd) (y : nadd) (d : nadd) (h1 : term78 z y d) : term78 z y d.
Proof. exact (h1). Qed.
Lemma lem1279918 (x : nadd) (z : nadd) : term67 x z.
Proof. exact (EQ_MP (@lem1279903 x z) (@lem1279902 x z)). Qed.
Lemma lem1279919 (y : nadd) (x : nadd) (z : nadd) : term79 y x z.
Proof. exact (@lem1279918 (nadd_mul x y) (nadd_mul x z)). Qed.
Lemma lem1279923 (x : nadd) (y : nadd) : (term55 x y) = True.
Proof. exact (EQ_MP (@lem1279875 x y) (@lem1279874 x y)). Qed.
Lemma lem1279924 (y : nadd) (x : nadd) (d : nadd) : (term80 y x d) = True.
Proof. exact (@lem1279923 (nadd_mul x y) (nadd_mul x d)). Qed.
Lemma lem1279925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1279926 (y : nadd) (x : nadd) (d : nadd) : (term81 y x d) = (and True).
Proof. exact (MK_COMB (@lem1279925) (@lem1279924 y x d)). Qed.
Lemma lem1279927 (y : nadd) (d : nadd) (x : nadd) (z : nadd) : (term82 y d x z) = (term82 y d x z).
Proof. exact (eq_refl (term82 y d x z)). Qed.
Lemma lem1279928 (y : nadd) (d : nadd) (x : nadd) (z : nadd) : (term83 y d x z) = (term84 y d x z).
Proof. exact (MK_COMB (@lem1279926 y x d) (@lem1279927 y d x z)). Qed.
Lemma lem1279930 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1279931 (y : nadd) (d : nadd) (x : nadd) (z : nadd) : (term84 y d x z) = (term82 y d x z).
Proof. exact (@lem1279930 (term82 y d x z)). Qed.
Lemma lem1279932 (y : nadd) (d : nadd) (x : nadd) (z : nadd) : (term83 y d x z) = (term82 y d x z).
Proof. exact (TRANS (@lem1279928 y d x z) (@lem1279931 y d x z)). Qed.
Lemma lem1279933 (y : nadd) (d : nadd) (x : nadd) (z : nadd) : (term82 y d x z) = (term83 y d x z).
Proof. exact (SYM (@lem1279932 y d x z)). Qed.
Lemma lem1279935 (x : nadd) (y : nadd) : term49 x y.
Proof. exact (EQ_MP (@lem1279867 x y) (@lem1279866 x y)). Qed.
Lemma lem1279936 (y : nadd) (d : nadd) (x : nadd) (z : nadd) : term85 y d x z.
Proof. exact (@lem1279935 (term86 y x d) (nadd_mul x z)). Qed.
Lemma lem1279938 (x : nadd) (z : nadd) : term39 x z.
Proof. exact (EQ_MP (@lem1279844 x z) (@lem1279843 x z)). Qed.
Lemma lem1279939 (y : nadd) (d : nadd) (x : nadd) (z : nadd) : term87 y d x z.
Proof. exact (@lem1279938 (term86 y x d) (nadd_mul x z)). Qed.
Lemma lem1279943 (y : nadd) (x : nadd) : (nadd_eq x y) = (nadd_eq y x).
Proof. exact (EQ_MP (@lem1279816 y x) (@lem1279815 x y)). Qed.
Lemma lem1279944 (y : nadd) (x : nadd) (d : nadd) : (term88 x y d) = (term24 y x d).
Proof. exact (@lem1279943 (term89 x y d) (term86 y x d)). Qed.
Lemma lem1279945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1279946 (y : nadd) (x : nadd) (d : nadd) : (term90 x y d) = (term91 y x d).
Proof. exact (MK_COMB (@lem1279945) (@lem1279944 y x d)). Qed.
Lemma lem1279948 (y : nadd) (x : nadd) : (nadd_eq x y) = (nadd_eq y x).
Proof. exact (EQ_MP (@lem1279816 y x) (@lem1279815 x y)). Qed.
Lemma lem1279949 (z : nadd) (x : nadd) (y : nadd) (d : nadd) : (term92 y d x z) = (term93 z x y d).
Proof. exact (@lem1279948 (nadd_mul x z) (term89 x y d)). Qed.
Lemma lem1279950 (z : nadd) (x : nadd) (y : nadd) (d : nadd) : (term94 y d x z) = (term95 z x y d).
Proof. exact (MK_COMB (@lem1279946 y x d) (@lem1279949 z x y d)). Qed.
Lemma lem1279951 (y : nadd) (d : nadd) (x : nadd) (z : nadd) : (term95 z x y d) = (term94 y d x z).
Proof. exact (SYM (@lem1279950 z x y d)). Qed.
Lemma lem1279955 (y : nadd) (x : nadd) (z : nadd) : (term24 y x z) = True.
Proof. exact (EQ_MP (@lem1279810 y x z) (@lem1279809 y x z)). Qed.
Lemma lem1279956 (y : nadd) (x : nadd) (d : nadd) : (term24 y x d) = True.
Proof. exact (@lem1279955 y x d). Qed.
Lemma lem1279957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1279958 (y : nadd) (x : nadd) (d : nadd) : (term91 y x d) = (and True).
Proof. exact (MK_COMB (@lem1279957) (@lem1279956 y x d)). Qed.
Lemma lem1279959 (z : nadd) (x : nadd) (y : nadd) (d : nadd) : (term93 z x y d) = (term93 z x y d).
Proof. exact (eq_refl (term93 z x y d)). Qed.
Lemma lem1279960 (z : nadd) (x : nadd) (y : nadd) (d : nadd) : (term95 z x y d) = (term96 z x y d).
Proof. exact (MK_COMB (@lem1279958 y x d) (@lem1279959 z x y d)). Qed.
Lemma lem1279962 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1279963 (z : nadd) (x : nadd) (y : nadd) (d : nadd) : (term96 z x y d) = (term93 z x y d).
Proof. exact (@lem1279962 (term93 z x y d)). Qed.
Lemma lem1279964 (z : nadd) (x : nadd) (y : nadd) (d : nadd) : (term95 z x y d) = (term93 z x y d).
Proof. exact (TRANS (@lem1279960 z x y d) (@lem1279963 z x y d)). Qed.
Lemma lem1279965 (z : nadd) (x : nadd) (y : nadd) (d : nadd) : (term93 z x y d) = (term95 z x y d).
Proof. exact (SYM (@lem1279964 z x y d)). Qed.
Lemma lem1279967 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : term8 x y x' y'.
Proof. exact (EQ_MP (@lem1279799 x y x' y') (@lem1279798 x y x' y')). Qed.
Lemma lem1279968 (z : nadd) (x : nadd) (y : nadd) (d : nadd) : term97 z x y d.
Proof. exact (@lem1279967 x z x (nadd_add y d)). Qed.
Lemma lem1279969 (x : nadd) : term98 x.
Proof. exact (@lem1267990 x). Qed.
Lemma lem1279970 (x : nadd) : (term98 x) = (nadd_eq x x).
Proof. exact (eq_refl (term98 x)). Qed.
Lemma lem1279971 (x : nadd) : nadd_eq x x.
Proof. exact (EQ_MP (@lem1279970 x) (@lem1279969 x)). Qed.
Lemma lem1279972 (x : nadd) : (nadd_eq x x) = ((nadd_eq x x) = True).
Proof. exact (@lem7 (nadd_eq x x)). Qed.
Lemma lem1279974 (z : nadd) (y : nadd) (d : nadd) : (term78 z y d) = ((term78 z y d) = True).
Proof. exact (@lem7 (term78 z y d)). Qed.
Lemma lem1279979 (x : nadd) : (nadd_eq x x) = True.
Proof. exact (EQ_MP (@lem1279972 x) (@lem1279971 x)). Qed.
Lemma lem1279980 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1279981 (x : nadd) : (term99 x) = (and True).
Proof. exact (MK_COMB (@lem1279980) (@lem1279979 x)). Qed.
Lemma lem1279983 (z : nadd) (y : nadd) (d : nadd) (h1 : term78 z y d) : (term78 z y d) = True.
Proof. exact (EQ_MP (@lem1279974 z y d) (@lem1279916 z y d h1)). Qed.
Lemma lem1279984 (x : nadd) (z : nadd) (y : nadd) (d : nadd) (h1 : term78 z y d) : (term100 x z y d) = (True /\ True).
Proof. exact (MK_COMB (@lem1279981 x) (@lem1279983 z y d h1)). Qed.
Lemma lem1279986 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1279987 : (True /\ True) = True.
Proof. exact (@lem1279986 True). Qed.
Lemma lem1279988 (x : nadd) (z : nadd) (y : nadd) (d : nadd) (h1 : term78 z y d) : (term100 x z y d) = True.
Proof. exact (TRANS (@lem1279984 x z y d h1) (@lem1279987)). Qed.
Lemma lem1279989 (x : nadd) (z : nadd) (y : nadd) (d : nadd) (h1 : term78 z y d) : True = (term100 x z y d).
Proof. exact (SYM (@lem1279988 x z y d h1)). Qed.
Lemma lem1279990 (x : nadd) (z : nadd) (y : nadd) (d : nadd) (h1 : term78 z y d) : term100 x z y d.
Proof. exact (EQ_MP (@lem1279989 x z y d h1) (@lem0)). Qed.
Lemma lem1279991 (x : nadd) (z : nadd) (y : nadd) (d : nadd) (h1 : term78 z y d) : term93 z x y d.
Proof. exact (@lem1279968 z x y d (@lem1279990 x z y d h1)). Qed.
Lemma lem1279992 (x : nadd) (z : nadd) (y : nadd) (d : nadd) (h1 : term78 z y d) : term95 z x y d.
Proof. exact (EQ_MP (@lem1279965 z x y d) (@lem1279991 x z y d h1)). Qed.
Lemma lem1279993 (x : nadd) (z : nadd) (y : nadd) (d : nadd) (h1 : term78 z y d) : term94 y d x z.
Proof. exact (EQ_MP (@lem1279951 y d x z) (@lem1279992 x z y d h1)). Qed.
Lemma lem1279994 (x : nadd) (z : nadd) (y : nadd) (d : nadd) (h1 : term78 z y d) : term101 y d x z.
Proof. exact (ex_intro (term102 y d x z) (term89 x y d) (@lem1279993 x z y d h1)). Qed.
Lemma lem1279995 (x : nadd) (z : nadd) (y : nadd) (d : nadd) (h1 : term78 z y d) : term103 y d x z.
Proof. exact (@lem1279939 y d x z (@lem1279994 x z y d h1)). Qed.
Lemma lem1279996 (x : nadd) (z : nadd) (y : nadd) (d : nadd) (h1 : term78 z y d) : term82 y d x z.
Proof. exact (@lem1279936 y d x z (@lem1279995 x z y d h1)). Qed.
Lemma lem1279997 (x : nadd) (z : nadd) (y : nadd) (d : nadd) (h1 : term78 z y d) : term83 y d x z.
Proof. exact (EQ_MP (@lem1279933 y d x z) (@lem1279996 x z y d h1)). Qed.
Lemma lem1279998 (x : nadd) (z : nadd) (y : nadd) (d : nadd) (h1 : term78 z y d) : term104 y x z.
Proof. exact (ex_intro (term105 y x z) (term86 y x d) (@lem1279997 x z y d h1)). Qed.
Lemma lem1279999 (x : nadd) (z : nadd) (y : nadd) (d : nadd) (h1 : term78 z y d) : term106 y x z.
Proof. exact (@lem1279919 y x z (@lem1279998 x z y d h1)). Qed.
Lemma lem1280000 (x : nadd) (y : nadd) (z : nadd) (h1 : nadd_le y z) : term106 y x z.
Proof. exact (ex_elim (@lem1279915 y z h1) (fun d : nadd => fun h0 : term107 z y d => @lem1279999 x z y d h0)). Qed.
Lemma lem1280001 (y : nadd) (x : nadd) (z : nadd) : term108 y x z.
Proof. exact (fun h0 : nadd_le y z => @lem1280000 x y z h0). Qed.
Lemma lem1280006 (y : nadd) (x : nadd) : term109 y x.
Proof. exact (fun z : nadd => @lem1280001 y x z). Qed.
Lemma lem1280011 (x : nadd) : term110 x.
Proof. exact (fun y : nadd => @lem1280006 y x). Qed.
Lemma lem1280016 : term111.
Proof. exact (fun x : nadd => @lem1280011 x). Qed.
