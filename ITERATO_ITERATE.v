Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATO_ITERATE_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import CARD_DELETE_spec.
Require Import CARD_EQ_0_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import FINITE_DELETE_spec.
Require Import FINITE_RESTRICT_spec.
Require Import FUN_EQ_THM_spec.
Require Import IMP_CONJ_spec.
Require Import INT_POS_spec.
Require Import IN_DELETE_spec.
Require Import IN_DIFF_spec.
Require Import IN_SING_spec.
Require Import IN_UNIV_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import ITERATE_EXPAND_CASES_spec.
Require Import ITERATE_SUPPORT_spec.
Require Import ITERATO_CLAUSES_EXISTS_spec.
Require Import ITERATO_EXPAND_CASES_spec.
Require Import ITERATO_SUPPORT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import RIGHT_IMP_FORALL_THM_spec.
Require Import num_WF_spec.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032098_spec.
Require Import thm1032781_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm129_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm137_spec.
Require Import thm1386578_spec.
Require Import thm1393126_spec.
Require Import thm1396750_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17500_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm19490_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988330_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
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
Require Import thm21386_spec.
Require Import thm21735_spec.
Require Import thm21736_spec.
Require Import thm2318496_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm892_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem6875695 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem6875696 {_125820 : Type'} (s : _125820 -> Prop) (t : _125820 -> Prop) : (s = t) = (term0 _125820 s t).
Proof. exact (@lem6875695 _125820 s t). Qed.
Lemma lem6875697 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : ((term1 _125820 k i) = k) = (term2 _125820 i k).
Proof. exact (@lem6875696 _125820 (term1 _125820 k i) k). Qed.
Lemma lem6875706 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : (term3 _125820 i k) = (term3 _125820 i k).
Proof. exact (eq_refl (term3 _125820 i k)). Qed.
Lemma lem6875707 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : (term4 _125820 i k) = (term5 _125820 i k).
Proof. exact (MK_COMB (@lem6875706 _125820 i k) (@lem6875697 _125820 i k)). Qed.
Lemma lem6875710 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : (term5 _125820 i k) = (term4 _125820 i k).
Proof. exact (SYM (@lem6875707 _125820 i k)). Qed.
Lemma lem6875714 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6875715 {_125820 : Type'} (P : _125820 -> Prop) (x : _125820) : (@IN _125820 x P) = (P x).
Proof. exact (@lem6875714 _125820 P x). Qed.
Lemma lem6875716 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) : (@IN _125820 i k) = (k i).
Proof. exact (@lem6875715 _125820 k i). Qed.
Lemma lem6875717 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6875718 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) : (term3 _125820 i k) = (term6 _125820 k i).
Proof. exact (MK_COMB (@lem6875717) (@lem6875716 _125820 k i)). Qed.
Lemma lem6875726 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term7 A x y s) = (term8 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem6875727 {_125820 : Type'} (y : _125820) (x : _125820) (s : _125820 -> Prop) : (term7 _125820 x y s) = (term8 _125820 y x s).
Proof. exact (@lem6875726 _125820 y x s). Qed.
Lemma lem6875728 {_125820 : Type'} (x : _125820) (k : _125820 -> Prop) (i : _125820) : (term9 _125820 x k i) = (term10 _125820 x k i).
Proof. exact (@lem6875727 _125820 i x (@DELETE _125820 k i)). Qed.
Lemma lem6875734 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term11 A x s y) = (term12 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem6875735 {_125820 : Type'} (s : _125820 -> Prop) (x : _125820) (y : _125820) : (term11 _125820 x s y) = (term12 _125820 s x y).
Proof. exact (@lem6875734 _125820 s x y). Qed.
Lemma lem6875736 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) : (term11 _125820 x k i) = (term12 _125820 k x i).
Proof. exact (@lem6875735 _125820 k x i). Qed.
Lemma lem6875740 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6875741 {_125820 : Type'} (P : _125820 -> Prop) (x : _125820) : (@IN _125820 x P) = (P x).
Proof. exact (@lem6875740 _125820 P x). Qed.
Lemma lem6875742 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) : (@IN _125820 x k) = (k x).
Proof. exact (@lem6875741 _125820 k x). Qed.
Lemma lem6875743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6875744 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) : (term13 _125820 x k) = (term14 _125820 k x).
Proof. exact (MK_COMB (@lem6875743) (@lem6875742 _125820 k x)). Qed.
Lemma lem6875747 {_125820 : Type'} (x : _125820) (i : _125820) : (term15 _125820 x i) = (term15 _125820 x i).
Proof. exact (eq_refl (term15 _125820 x i)). Qed.
Lemma lem6875748 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) : (term12 _125820 k x i) = (term16 _125820 k x i).
Proof. exact (MK_COMB (@lem6875744 _125820 k x) (@lem6875747 _125820 x i)). Qed.
Lemma lem6875751 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) : (term11 _125820 x k i) = (term16 _125820 k x i).
Proof. exact (TRANS (@lem6875736 _125820 k x i) (@lem6875748 _125820 k x i)). Qed.
Lemma lem6875752 {_125820 : Type'} (x : _125820) (i : _125820) : (term17 _125820 x i) = (term17 _125820 x i).
Proof. exact (eq_refl (term17 _125820 x i)). Qed.
Lemma lem6875753 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) : (term10 _125820 x k i) = (term18 _125820 k x i).
Proof. exact (MK_COMB (@lem6875752 _125820 x i) (@lem6875751 _125820 k x i)). Qed.
Lemma lem6875756 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) : (term9 _125820 x k i) = (term18 _125820 k x i).
Proof. exact (TRANS (@lem6875728 _125820 x k i) (@lem6875753 _125820 k x i)). Qed.
Lemma lem6875757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6875758 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) : (term19 _125820 x k i) = (term20 _125820 k x i).
Proof. exact (MK_COMB (@lem6875757) (@lem6875756 _125820 k x i)). Qed.
Lemma lem6875760 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem6875761 {_125820 : Type'} (P : _125820 -> Prop) (x : _125820) : (@IN _125820 x P) = (P x).
Proof. exact (@lem6875760 _125820 P x). Qed.
Lemma lem6875762 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) : (@IN _125820 x k) = (k x).
Proof. exact (@lem6875761 _125820 k x). Qed.
Lemma lem6875763 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) : ((term9 _125820 x k i) = (@IN _125820 x k)) = ((term18 _125820 k x i) = (k x)).
Proof. exact (MK_COMB (@lem6875758 _125820 k x i) (@lem6875762 _125820 k x)). Qed.
Lemma lem6875766 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : (term21 _125820 i k) = (term22 _125820 i k).
Proof. exact (fun_ext (fun x : _125820 => @lem6875763 _125820 i k x)). Qed.
Lemma lem6875767 {_125820 : Type'} : (@all _125820) = (@all _125820).
Proof. exact (eq_refl (@all _125820)). Qed.
Lemma lem6875768 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : (term2 _125820 i k) = (term23 _125820 i k).
Proof. exact (MK_COMB (@lem6875767 _125820) (@lem6875766 _125820 i k)). Qed.
Lemma lem6875773 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : (term5 _125820 i k) = (term24 _125820 i k).
Proof. exact (MK_COMB (@lem6875718 _125820 k i) (@lem6875768 _125820 i k)). Qed.
Lemma lem6875776 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : (term24 _125820 i k) = (term5 _125820 i k).
Proof. exact (SYM (@lem6875773 _125820 i k)). Qed.
Lemma lem6875778 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6875779 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : (term24 _125820 i k) = (term26 _125820 i k).
Proof. exact (@lem6875778 (term24 _125820 i k)). Qed.
Lemma lem6875780 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : (term26 _125820 i k) = (term24 _125820 i k).
Proof. exact (SYM (@lem6875779 _125820 i k)). Qed.
Lemma lem6875781 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (h1 : term27 _125820 i k) : term27 _125820 i k.
Proof. exact (h1). Qed.
Lemma lem6875784 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (h1 : term26 _125820 i k) : term26 _125820 i k.
Proof. exact (h1). Qed.
Lemma lem6875785 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : term28 _125820 i k.
Proof. exact (fun h0 : term26 _125820 i k => @lem6875784 _125820 i k h0). Qed.
Lemma lem6875786 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (h1 : term28 _125820 i k) : term28 _125820 i k.
Proof. exact (h1). Qed.
Lemma lem6875787 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (h1 : term26 _125820 i k) : term26 _125820 i k.
Proof. exact (h1). Qed.
Lemma lem6875788 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (h1 : term26 _125820 i k) (h2 : term28 _125820 i k) : term26 _125820 i k.
Proof. exact (@lem6875786 _125820 i k h2 (@lem6875787 _125820 i k h1)). Qed.
Lemma lem6875789 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (h1 : term26 _125820 i k) : term29 _125820 i k.
Proof. exact (fun h0 : term28 _125820 i k => @lem6875788 _125820 i k h1 h0). Qed.
Lemma lem6875790 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (h1 : term28 _125820 i k) : term28 _125820 i k.
Proof. exact (h1). Qed.
Lemma lem6875791 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (h1 : term26 _125820 i k) (h2 : term28 _125820 i k) : term26 _125820 i k.
Proof. exact (@lem6875789 _125820 i k h1 (@lem6875790 _125820 i k h2)). Qed.
Lemma lem6875792 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (h1 : term28 _125820 i k) : term28 _125820 i k.
Proof. exact (fun h0 : term26 _125820 i k => @lem6875791 _125820 i k h0 h1). Qed.
Lemma lem6875793 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : term30 _125820 i k.
Proof. exact (fun h0 : term28 _125820 i k => @lem6875792 _125820 i k h0). Qed.
Lemma lem6875796 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : term28 _125820 i k.
Proof. exact (@lem6875793 _125820 i k (@lem6875785 _125820 i k)). Qed.
Lemma lem6875797 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : term28 _125820 i k.
Proof. exact (@lem6875796 _125820 i k). Qed.
Lemma lem6875807 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6875808 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : (term26 _125820 i k) = (term31 _125820 i k).
Proof. exact (@lem6875807 (term27 _125820 i k)). Qed.
Lemma lem6875810 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6875811 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : (term31 _125820 i k) = (term24 _125820 i k).
Proof. exact (@lem6875810 (term24 _125820 i k)). Qed.
Lemma lem6875814 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : (term26 _125820 i k) = (term24 _125820 i k).
Proof. exact (TRANS (@lem6875808 _125820 i k) (@lem6875811 _125820 i k)). Qed.
Lemma lem6875823 {_125820 : Type'} (k : _125820 -> Prop) : (term33 _125820 k) = (term34 _125820 k).
Proof. exact (fun_ext (fun i : _125820 => @lem6875814 _125820 i k)). Qed.
Lemma lem6875824 {_125820 : Type'} : (@all _125820) = (@all _125820).
Proof. exact (eq_refl (@all _125820)). Qed.
Lemma lem6875825 {_125820 : Type'} (k : _125820 -> Prop) : (term35 _125820 k) = (term36 _125820 k).
Proof. exact (MK_COMB (@lem6875824 _125820) (@lem6875823 _125820 k)). Qed.
Lemma lem6875830 {_125820 : Type'} : (term37 _125820) = (term38 _125820).
Proof. exact (fun_ext (fun k : _125820 -> Prop => @lem6875825 _125820 k)). Qed.
Lemma lem6875831 {_125820 : Type'} : (@all (_125820 -> Prop)) = (@all (_125820 -> Prop)).
Proof. exact (eq_refl (@all (_125820 -> Prop))). Qed.
Lemma lem6875840 {_125820 : Type'} : (term39 _125820) = (term40 _125820).
Proof. exact (MK_COMB (@lem6875831 _125820) (@lem6875830 _125820)). Qed.
Lemma lem6875855 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) : ((term18 _125820 k x i) = (k x)) = ((term18 _125820 k x i) = (k x)).
Proof. exact (eq_refl ((term18 _125820 k x i) = (k x))). Qed.
Lemma lem6875856 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : (term22 _125820 i k) = (term22 _125820 i k).
Proof. exact (fun_ext (fun x : _125820 => @lem6875855 _125820 i k x)). Qed.
Lemma lem6875857 {_125820 : Type'} : (@all _125820) = (@all _125820).
Proof. exact (eq_refl (@all _125820)). Qed.
Lemma lem6875858 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : (term23 _125820 i k) = (term23 _125820 i k).
Proof. exact (MK_COMB (@lem6875857 _125820) (@lem6875856 _125820 i k)). Qed.
Lemma lem6875861 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) : (term6 _125820 k i) = (term6 _125820 k i).
Proof. exact (eq_refl (term6 _125820 k i)). Qed.
Lemma lem6875862 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : (term24 _125820 i k) = (term24 _125820 i k).
Proof. exact (MK_COMB (@lem6875861 _125820 k i) (@lem6875858 _125820 i k)). Qed.
Lemma lem6875863 {_125820 : Type'} (k : _125820 -> Prop) : (term34 _125820 k) = (term34 _125820 k).
Proof. exact (fun_ext (fun i : _125820 => @lem6875862 _125820 i k)). Qed.
Lemma lem6875864 {_125820 : Type'} : (@all _125820) = (@all _125820).
Proof. exact (eq_refl (@all _125820)). Qed.
Lemma lem6875865 {_125820 : Type'} (k : _125820 -> Prop) : (term36 _125820 k) = (term36 _125820 k).
Proof. exact (MK_COMB (@lem6875864 _125820) (@lem6875863 _125820 k)). Qed.
Lemma lem6875866 {_125820 : Type'} : (term38 _125820) = (term38 _125820).
Proof. exact (fun_ext (fun k : _125820 -> Prop => @lem6875865 _125820 k)). Qed.
Lemma lem6875867 {_125820 : Type'} : (@all (_125820 -> Prop)) = (@all (_125820 -> Prop)).
Proof. exact (eq_refl (@all (_125820 -> Prop))). Qed.
Lemma lem6875868 {_125820 : Type'} : (term40 _125820) = (term40 _125820).
Proof. exact (MK_COMB (@lem6875867 _125820) (@lem6875866 _125820)). Qed.
Lemma lem6875895 {_125820 : Type'} : (term39 _125820) = (term40 _125820).
Proof. exact (TRANS (@lem6875840 _125820) (@lem6875868 _125820)). Qed.
Lemma lem6875896 {_125820 : Type'} : (term40 _125820) = (term39 _125820).
Proof. exact (SYM (@lem6875895 _125820)). Qed.
Lemma lem6875899 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6875900 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) : ((term18 _125820 k x i) = (k x)) = (term41 _125820 i k x).
Proof. exact (@lem6875899 ((term18 _125820 k x i) = (k x))). Qed.
Lemma lem6875901 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) : (term41 _125820 i k x) = ((term18 _125820 k x i) = (k x)).
Proof. exact (SYM (@lem6875900 _125820 i k x)). Qed.
Lemma lem6875902 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term42 _125820 i k x) : term42 _125820 i k x.
Proof. exact (h1). Qed.
Lemma lem6875908 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) (h1 : k i) : k i.
Proof. exact (h1). Qed.
Lemma lem6875916 {_125820 : Type'} (x : _125820) (i : _125820) : (term43 _125820 x i) = (x = i).
Proof. exact (@lem16933 (x = i)). Qed.
Lemma lem6875918 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) : (term44 _125820 k x) = (term44 _125820 k x).
Proof. exact (eq_refl (term44 _125820 k x)). Qed.
Lemma lem6875919 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) : (term45 _125820 k x i) = (term46 _125820 k x i).
Proof. exact (MK_COMB (@lem6875918 _125820 k x) (@lem6875916 _125820 x i)). Qed.
Lemma lem6875920 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) : (term47 _125820 k x i) = (term45 _125820 k x i).
Proof. exact (@lem17045 (k x) (term15 _125820 x i)). Qed.
Lemma lem6875921 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) : (term47 _125820 k x i) = (term46 _125820 k x i).
Proof. exact (TRANS (@lem6875920 _125820 k x i) (@lem6875919 _125820 k x i)). Qed.
Lemma lem6875926 {_125820 : Type'} (x : _125820) (i : _125820) : (term48 _125820 x i) = (term48 _125820 x i).
Proof. exact (eq_refl (term48 _125820 x i)). Qed.
Lemma lem6875927 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) : (term49 _125820 k x i) = (term50 _125820 k x i).
Proof. exact (MK_COMB (@lem6875926 _125820 x i) (@lem6875921 _125820 k x i)). Qed.
Lemma lem6875928 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) : (term51 _125820 k x i) = (term49 _125820 k x i).
Proof. exact (@lem17160 (x = i) (term16 _125820 k x i)). Qed.
Lemma lem6875929 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) : (term51 _125820 k x i) = (term50 _125820 k x i).
Proof. exact (TRANS (@lem6875928 _125820 k x i) (@lem6875927 _125820 k x i)). Qed.
Lemma lem6875934 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) : (k x) = (k x).
Proof. exact (eq_refl (k x)). Qed.
Lemma lem6875935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6875936 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) : (term52 _125820 k x i) = (term53 _125820 k x i).
Proof. exact (MK_COMB (@lem6875935) (@lem6875929 _125820 k x i)). Qed.
Lemma lem6875937 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) : (term54 _125820 i k x) = (term55 _125820 i k x).
Proof. exact (MK_COMB (@lem6875936 _125820 k x i) (@lem6875934 _125820 k x)). Qed.
Lemma lem6875942 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) : (term56 _125820 i k x) = (term56 _125820 i k x).
Proof. exact (eq_refl (term56 _125820 i k x)). Qed.
Lemma lem6875943 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) : (term57 _125820 i k x) = (term58 _125820 i k x).
Proof. exact (MK_COMB (@lem6875942 _125820 i k x) (@lem6875937 _125820 i k x)). Qed.
Lemma lem6875944 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) : (term42 _125820 i k x) = (term57 _125820 i k x).
Proof. exact (@lem17646 (term18 _125820 k x i) (k x)). Qed.
Lemma lem6875949 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) : (term42 _125820 i k x) = (term58 _125820 i k x).
Proof. exact (TRANS (@lem6875944 _125820 i k x) (@lem6875943 _125820 i k x)). Qed.
Lemma lem6875954 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) (h1 : k i) : k i.
Proof. exact (h1). Qed.
Lemma lem6876016 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term42 _125820 i k x) : term58 _125820 i k x.
Proof. exact (EQ_MP (@lem6875949 _125820 i k x) (@lem6875902 _125820 i k x h1)). Qed.
Lemma lem6876017 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term59 _125820 i k x) : term59 _125820 i k x.
Proof. exact (h1). Qed.
Lemma lem6876018 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term55 _125820 i k x) : term55 _125820 i k x.
Proof. exact (h1). Qed.
Lemma lem6876020 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term59 _125820 i k x) : term18 _125820 k x i.
Proof. exact (proj1 (@lem6876017 _125820 i k x h1)). Qed.
Lemma lem6876022 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term16 _125820 k x i) : term16 _125820 k x i.
Proof. exact (h1). Qed.
Lemma lem6876026 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term55 _125820 i k x) : term50 _125820 k x i.
Proof. exact (proj1 (@lem6876018 _125820 i k x h1)). Qed.
Lemma lem6876027 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term55 _125820 i k x) : term46 _125820 k x i.
Proof. exact (proj2 (@lem6876026 _125820 i k x h1)). Qed.
Lemma lem6876034 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) (h1 : k i) : k i.
Proof. exact (h1). Qed.
Lemma lem6876042 {_125820 : Type'} (x : _125820) (i : _125820) (h1 : x = i) : x = i.
Proof. exact (h1). Qed.
Lemma lem6876074 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (h1 : term60 _125820 k x) : term60 _125820 k x.
Proof. exact (h1). Qed.
Lemma lem6876090 {_125820 : Type'} (x : _125820) (i : _125820) (h1 : x = i) : x = i.
Proof. exact (h1). Qed.
Lemma lem6876092 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) (h1 : k i) : k i.
Proof. exact (h1). Qed.
Lemma lem6876094 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term59 _125820 i k x) : term60 _125820 k x.
Proof. exact (proj2 (@lem6876017 _125820 i k x h1)). Qed.
Lemma lem6876096 {_125820 : Type'} (x : _125820) (i : _125820) (h1 : x = i) : x = i.
Proof. exact (h1). Qed.
Lemma lem6876100 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term59 _125820 i k x) : term60 _125820 k x.
Proof. exact (proj2 (@lem6876017 _125820 i k x h1)). Qed.
Lemma lem6876112 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (h1 : term60 _125820 k x) : term60 _125820 k x.
Proof. exact (h1). Qed.
Lemma lem6876118 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term55 _125820 i k x) : term15 _125820 x i.
Proof. exact (proj1 (@lem6876026 _125820 i k x h1)). Qed.
Lemma lem6876120 {_125820 : Type'} (x : _125820) (i : _125820) (h1 : x = i) : x = i.
Proof. exact (h1). Qed.
Lemma lem6876148 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) (h1 : k i) : k i.
Proof. exact (h1). Qed.
Lemma lem6876149 {_125820 : Type'} (k : _125820 -> Prop) : (term61 _125820 k) = (term61 _125820 k).
Proof. exact (eq_refl (term61 _125820 k)). Qed.
Lemma lem6876150 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : x = i) : (term62 _125820 k x) = (term62 _125820 k i).
Proof. exact (MK_COMB (@lem6876149 _125820 k) (@lem6876096 _125820 x i h1)). Qed.
Lemma lem6876151 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) : (term62 _125820 k i) = (term60 _125820 k i).
Proof. exact (eq_refl (term62 _125820 k i)). Qed.
Lemma lem6876152 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) : (term63 _125820 k x) = (term63 _125820 k x).
Proof. exact (eq_refl (term63 _125820 k x)). Qed.
Lemma lem6876153 {_125820 : Type'} (x : _125820) (k : _125820 -> Prop) (i : _125820) : ((term62 _125820 k x) = (term62 _125820 k i)) = ((term62 _125820 k x) = (term60 _125820 k i)).
Proof. exact (MK_COMB (@lem6876152 _125820 k x) (@lem6876151 _125820 k i)). Qed.
Lemma lem6876154 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) : (term62 _125820 k x) = (term60 _125820 k x).
Proof. exact (eq_refl (term62 _125820 k x)). Qed.
Lemma lem6876155 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6876156 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) : (term63 _125820 k x) = (term64 _125820 k x).
Proof. exact (MK_COMB (@lem6876155) (@lem6876154 _125820 k x)). Qed.
Lemma lem6876157 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) : (term60 _125820 k i) = (term60 _125820 k i).
Proof. exact (eq_refl (term60 _125820 k i)). Qed.
Lemma lem6876158 {_125820 : Type'} (x : _125820) (k : _125820 -> Prop) (i : _125820) : ((term62 _125820 k x) = (term60 _125820 k i)) = ((term60 _125820 k x) = (term60 _125820 k i)).
Proof. exact (MK_COMB (@lem6876156 _125820 k x) (@lem6876157 _125820 k i)). Qed.
Lemma lem6876159 {_125820 : Type'} (x : _125820) (k : _125820 -> Prop) (i : _125820) : ((term62 _125820 k x) = (term62 _125820 k i)) = ((term60 _125820 k x) = (term60 _125820 k i)).
Proof. exact (TRANS (@lem6876153 _125820 x k i) (@lem6876158 _125820 x k i)). Qed.
Lemma lem6876160 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : x = i) : (term60 _125820 k x) = (term60 _125820 k i).
Proof. exact (EQ_MP (@lem6876159 _125820 x k i) (@lem6876150 _125820 k x i h1)). Qed.
Lemma lem6876161 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term59 _125820 i k x) (h2 : x = i) : term60 _125820 k i.
Proof. exact (EQ_MP (@lem6876160 _125820 k x i h2) (@lem6876094 _125820 i k x h1)). Qed.
Lemma lem6876203 {_125820 : Type'} (i : _125820) : (term65 _125820 i) = (term65 _125820 i).
Proof. exact (eq_refl (term65 _125820 i)). Qed.
Lemma lem6876204 {_125820 : Type'} (x : _125820) (i : _125820) (h1 : x = i) : (term66 _125820 i x) = (term67 _125820 i).
Proof. exact (MK_COMB (@lem6876203 _125820 i) (@lem6876120 _125820 x i h1)). Qed.
Lemma lem6876205 {_125820 : Type'} (i : _125820) : (term67 _125820 i) = (term68 _125820 i).
Proof. exact (eq_refl (term67 _125820 i)). Qed.
Lemma lem6876206 {_125820 : Type'} (i : _125820) (x : _125820) : (term69 _125820 i x) = (term69 _125820 i x).
Proof. exact (eq_refl (term69 _125820 i x)). Qed.
Lemma lem6876207 {_125820 : Type'} (x : _125820) (i : _125820) : ((term66 _125820 i x) = (term67 _125820 i)) = ((term66 _125820 i x) = (term68 _125820 i)).
Proof. exact (MK_COMB (@lem6876206 _125820 i x) (@lem6876205 _125820 i)). Qed.
Lemma lem6876208 {_125820 : Type'} (x : _125820) (i : _125820) : (term66 _125820 i x) = (term15 _125820 x i).
Proof. exact (eq_refl (term66 _125820 i x)). Qed.
Lemma lem6876209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6876210 {_125820 : Type'} (x : _125820) (i : _125820) : (term69 _125820 i x) = (term70 _125820 x i).
Proof. exact (MK_COMB (@lem6876209) (@lem6876208 _125820 x i)). Qed.
Lemma lem6876211 {_125820 : Type'} (i : _125820) : (term68 _125820 i) = (term68 _125820 i).
Proof. exact (eq_refl (term68 _125820 i)). Qed.
Lemma lem6876212 {_125820 : Type'} (x : _125820) (i : _125820) : ((term66 _125820 i x) = (term68 _125820 i)) = ((term15 _125820 x i) = (term68 _125820 i)).
Proof. exact (MK_COMB (@lem6876210 _125820 x i) (@lem6876211 _125820 i)). Qed.
Lemma lem6876213 {_125820 : Type'} (x : _125820) (i : _125820) : ((term66 _125820 i x) = (term67 _125820 i)) = ((term15 _125820 x i) = (term68 _125820 i)).
Proof. exact (TRANS (@lem6876207 _125820 x i) (@lem6876212 _125820 x i)). Qed.
Lemma lem6876214 {_125820 : Type'} (x : _125820) (i : _125820) (h1 : x = i) : (term15 _125820 x i) = (term68 _125820 i).
Proof. exact (EQ_MP (@lem6876213 _125820 x i) (@lem6876204 _125820 x i h1)). Qed.
Lemma lem6876215 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term55 _125820 i k x) (h2 : x = i) : term68 _125820 i.
Proof. exact (EQ_MP (@lem6876214 _125820 x i h2) (@lem6876118 _125820 i k x h1)). Qed.
Lemma lem6876217 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) (h1 : k i) : k i.
Proof. exact (h1). Qed.
Lemma lem6876218 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) (h1 : k i) : term71 _125820 k i.
Proof. exact (fun h0 : term60 _125820 k i => @lem6876217 _125820 k i h1). Qed.
Lemma lem6876220 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6876221 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) : (term71 _125820 k i) = (k i).
Proof. exact (@lem6876220 (k i)). Qed.
Lemma lem6876222 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) (h1 : k i) : k i.
Proof. exact (EQ_MP (@lem6876221 _125820 k i) (@lem6876218 _125820 k i h1)). Qed.
Lemma lem6876225 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6876227 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) : (term60 _125820 k i) = (term73 _125820 k i).
Proof. exact (@lem6876225 (k i)). Qed.
Lemma lem6876230 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term59 _125820 i k x) (h2 : x = i) : term73 _125820 k i.
Proof. exact (EQ_MP (@lem6876227 _125820 k i) (@lem6876161 _125820 k x i h1 h2)). Qed.
Lemma lem6876233 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : False.
Proof. exact (@lem6876230 _125820 k x i h2 h3 (@lem6876222 _125820 k i h1)). Qed.
Lemma lem6876234 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : term74.
Proof. exact (fun h0 : ~ False => @lem6876233 _125820 k x i h1 h2 h3). Qed.
Lemma lem6876236 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6876237 : term74 = False.
Proof. exact (@lem6876236 False). Qed.
Lemma lem6876238 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : False.
Proof. exact (EQ_MP (@lem6876237) (@lem6876234 _125820 k x i h1 h2 h3)). Qed.
Lemma lem6876254 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term16 _125820 k x i) : k x.
Proof. exact (proj1 (@lem6876022 _125820 k x i h1)). Qed.
Lemma lem6876255 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term16 _125820 k x i) : term71 _125820 k x.
Proof. exact (fun h0 : term60 _125820 k x => @lem6876254 _125820 k x i h1). Qed.
Lemma lem6876257 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6876258 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) : (term71 _125820 k x) = (k x).
Proof. exact (@lem6876257 (k x)). Qed.
Lemma lem6876259 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term16 _125820 k x i) : k x.
Proof. exact (EQ_MP (@lem6876258 _125820 k x) (@lem6876255 _125820 k x i h1)). Qed.
Lemma lem6876262 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6876264 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) : (term60 _125820 k x) = (term73 _125820 k x).
Proof. exact (@lem6876262 (k x)). Qed.
Lemma lem6876267 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term59 _125820 i k x) : term73 _125820 k x.
Proof. exact (EQ_MP (@lem6876264 _125820 k x) (@lem6876100 _125820 i k x h1)). Qed.
Lemma lem6876270 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term16 _125820 k x i) (h2 : term59 _125820 i k x) : False.
Proof. exact (@lem6876267 _125820 i k x h2 (@lem6876259 _125820 k x i h1)). Qed.
Lemma lem6876271 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term16 _125820 k x i) (h2 : term59 _125820 i k x) : term74.
Proof. exact (fun h0 : ~ False => @lem6876270 _125820 i k x h1 h2). Qed.
Lemma lem6876273 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6876274 : term74 = False.
Proof. exact (@lem6876273 False). Qed.
Lemma lem6876275 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term16 _125820 k x i) (h2 : term59 _125820 i k x) : False.
Proof. exact (EQ_MP (@lem6876274) (@lem6876271 _125820 i k x h1 h2)). Qed.
Lemma lem6876291 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term55 _125820 i k x) : k x.
Proof. exact (proj2 (@lem6876018 _125820 i k x h1)). Qed.
Lemma lem6876292 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term55 _125820 i k x) : term71 _125820 k x.
Proof. exact (fun h0 : term60 _125820 k x => @lem6876291 _125820 i k x h1). Qed.
Lemma lem6876294 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6876295 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) : (term71 _125820 k x) = (k x).
Proof. exact (@lem6876294 (k x)). Qed.
Lemma lem6876296 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term55 _125820 i k x) : k x.
Proof. exact (EQ_MP (@lem6876295 _125820 k x) (@lem6876292 _125820 i k x h1)). Qed.
Lemma lem6876299 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6876301 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) : (term60 _125820 k x) = (term73 _125820 k x).
Proof. exact (@lem6876299 (k x)). Qed.
Lemma lem6876304 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (h1 : term60 _125820 k x) : term73 _125820 k x.
Proof. exact (EQ_MP (@lem6876301 _125820 k x) (@lem6876112 _125820 k x h1)). Qed.
Lemma lem6876307 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term60 _125820 k x) (h2 : term55 _125820 i k x) : False.
Proof. exact (@lem6876304 _125820 k x h1 (@lem6876296 _125820 i k x h2)). Qed.
Lemma lem6876308 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term60 _125820 k x) (h2 : term55 _125820 i k x) : term74.
Proof. exact (fun h0 : ~ False => @lem6876307 _125820 i k x h1 h2). Qed.
Lemma lem6876310 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6876311 : term74 = False.
Proof. exact (@lem6876310 False). Qed.
Lemma lem6876312 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term60 _125820 k x) (h2 : term55 _125820 i k x) : False.
Proof. exact (EQ_MP (@lem6876311) (@lem6876308 _125820 i k x h1 h2)). Qed.
Lemma lem6876328 {_125820 : Type'} (x : _125820) : x = x.
Proof. exact (@lem21386 _125820 x). Qed.
Lemma lem6876329 {_125820 : Type'} (x : _125820) : x = x.
Proof. exact (@lem6876328 _125820 x). Qed.
Lemma lem6876330 {_125820 : Type'} (i : _125820) : i = i.
Proof. exact (@lem6876329 _125820 i). Qed.
Lemma lem6876331 {_125820 : Type'} (i : _125820) : term75 _125820 i.
Proof. exact (fun h0 : term68 _125820 i => @lem6876330 _125820 i). Qed.
Lemma lem6876333 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6876334 {_125820 : Type'} (i : _125820) : (term75 _125820 i) = (i = i).
Proof. exact (@lem6876333 (i = i)). Qed.
Lemma lem6876335 {_125820 : Type'} (i : _125820) : i = i.
Proof. exact (EQ_MP (@lem6876334 _125820 i) (@lem6876331 _125820 i)). Qed.
Lemma lem6876338 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6876340 {_125820 : Type'} (i : _125820) : (term68 _125820 i) = (term76 _125820 i).
Proof. exact (@lem6876338 (i = i)). Qed.
Lemma lem6876343 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term55 _125820 i k x) (h2 : x = i) : term76 _125820 i.
Proof. exact (EQ_MP (@lem6876340 _125820 i) (@lem6876215 _125820 k x i h1 h2)). Qed.
Lemma lem6876346 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term55 _125820 i k x) (h2 : x = i) : False.
Proof. exact (@lem6876343 _125820 k x i h1 h2 (@lem6876335 _125820 i)). Qed.
Lemma lem6876347 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term55 _125820 i k x) (h2 : x = i) : term74.
Proof. exact (fun h0 : ~ False => @lem6876346 _125820 k x i h1 h2). Qed.
Lemma lem6876349 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6876350 : term74 = False.
Proof. exact (@lem6876349 False). Qed.
Lemma lem6876352 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term55 _125820 i k x) (h2 : x = i) : False.
Proof. exact (EQ_MP (@lem6876350) (@lem6876347 _125820 k x i h1 h2)). Qed.
Lemma lem6876353 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : (k i) = False.
Proof. exact (prop_ext (fun h4 : k i => @lem6876238 _125820 k x i h1 h2 h3) (fun h4 : False => @lem6876148 _125820 k i h1)). Qed.
Lemma lem6876355 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : False.
Proof. exact (EQ_MP (@lem6876353 _125820 k x i h1 h2 h3) (@lem6876148 _125820 k i h1)). Qed.
Lemma lem6876356 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term55 _125820 i k x) (h2 : x = i) : (x = i) = False.
Proof. exact (prop_ext (fun h3 : x = i => @lem6876352 _125820 k x i h1 h2) (fun h3 : False => @lem6876120 _125820 x i h2)). Qed.
Lemma lem6876357 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term55 _125820 i k x) (h2 : x = i) : False.
Proof. exact (EQ_MP (@lem6876356 _125820 k x i h1 h2) (@lem6876120 _125820 x i h2)). Qed.
Lemma lem6876358 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term60 _125820 k x) (h2 : term55 _125820 i k x) : (term60 _125820 k x) = False.
Proof. exact (prop_ext (fun h3 : term60 _125820 k x => @lem6876312 _125820 i k x h1 h2) (fun h3 : False => @lem6876112 _125820 k x h1)). Qed.
Lemma lem6876359 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term60 _125820 k x) (h2 : term55 _125820 i k x) : False.
Proof. exact (EQ_MP (@lem6876358 _125820 i k x h1 h2) (@lem6876112 _125820 k x h1)). Qed.
Lemma lem6876360 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : (x = i) = False.
Proof. exact (prop_ext (fun h4 : x = i => @lem6876355 _125820 k x i h1 h2 h3) (fun h4 : False => @lem6876096 _125820 x i h3)). Qed.
Lemma lem6876361 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : False.
Proof. exact (EQ_MP (@lem6876360 _125820 k x i h1 h2 h3) (@lem6876096 _125820 x i h3)). Qed.
Lemma lem6876362 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : (k i) = False.
Proof. exact (prop_ext (fun h4 : k i => @lem6876361 _125820 k x i h1 h2 h3) (fun h4 : False => @lem6876092 _125820 k i h1)). Qed.
Lemma lem6876363 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : False.
Proof. exact (EQ_MP (@lem6876362 _125820 k x i h1 h2 h3) (@lem6876092 _125820 k i h1)). Qed.
Lemma lem6876364 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term55 _125820 i k x) (h2 : x = i) : (x = i) = False.
Proof. exact (prop_ext (fun h3 : x = i => @lem6876357 _125820 k x i h1 h2) (fun h3 : False => @lem6876090 _125820 x i h2)). Qed.
Lemma lem6876365 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term55 _125820 i k x) (h2 : x = i) : False.
Proof. exact (EQ_MP (@lem6876364 _125820 k x i h1 h2) (@lem6876090 _125820 x i h2)). Qed.
Lemma lem6876366 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term60 _125820 k x) (h2 : term55 _125820 i k x) : (term60 _125820 k x) = False.
Proof. exact (prop_ext (fun h3 : term60 _125820 k x => @lem6876359 _125820 i k x h1 h2) (fun h3 : False => @lem6876074 _125820 k x h1)). Qed.
Lemma lem6876367 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term60 _125820 k x) (h2 : term55 _125820 i k x) : False.
Proof. exact (EQ_MP (@lem6876366 _125820 i k x h1 h2) (@lem6876074 _125820 k x h1)). Qed.
Lemma lem6876368 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : (x = i) = False.
Proof. exact (prop_ext (fun h4 : x = i => @lem6876363 _125820 k x i h1 h2 h3) (fun h4 : False => @lem6876042 _125820 x i h3)). Qed.
Lemma lem6876369 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : False.
Proof. exact (EQ_MP (@lem6876368 _125820 k x i h1 h2 h3) (@lem6876042 _125820 x i h3)). Qed.
Lemma lem6876370 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : (k i) = False.
Proof. exact (prop_ext (fun h4 : k i => @lem6876369 _125820 k x i h1 h2 h3) (fun h4 : False => @lem6876034 _125820 k i h1)). Qed.
Lemma lem6876371 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : False.
Proof. exact (EQ_MP (@lem6876370 _125820 k x i h1 h2 h3) (@lem6876034 _125820 k i h1)). Qed.
Lemma lem6876372 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term55 _125820 i k x) (h2 : x = i) : (x = i) = False.
Proof. exact (prop_ext (fun h3 : x = i => @lem6876365 _125820 k x i h1 h2) (fun h3 : False => @lem6876090 _125820 x i h2)). Qed.
Lemma lem6876373 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : term55 _125820 i k x) (h2 : x = i) : False.
Proof. exact (EQ_MP (@lem6876372 _125820 k x i h1 h2) (@lem6876090 _125820 x i h2)). Qed.
Lemma lem6876374 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term60 _125820 k x) (h2 : term55 _125820 i k x) : (term60 _125820 k x) = False.
Proof. exact (prop_ext (fun h3 : term60 _125820 k x => @lem6876367 _125820 i k x h1 h2) (fun h3 : False => @lem6876074 _125820 k x h1)). Qed.
Lemma lem6876375 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term60 _125820 k x) (h2 : term55 _125820 i k x) : False.
Proof. exact (EQ_MP (@lem6876374 _125820 i k x h1 h2) (@lem6876074 _125820 k x h1)). Qed.
Lemma lem6876376 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : (x = i) = False.
Proof. exact (prop_ext (fun h4 : x = i => @lem6876371 _125820 k x i h1 h2 h3) (fun h4 : False => @lem6876042 _125820 x i h3)). Qed.
Lemma lem6876377 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : False.
Proof. exact (EQ_MP (@lem6876376 _125820 k x i h1 h2 h3) (@lem6876042 _125820 x i h3)). Qed.
Lemma lem6876378 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : (k i) = False.
Proof. exact (prop_ext (fun h4 : k i => @lem6876377 _125820 k x i h1 h2 h3) (fun h4 : False => @lem6876034 _125820 k i h1)). Qed.
Lemma lem6876379 {_125820 : Type'} (k : _125820 -> Prop) (x : _125820) (i : _125820) (h1 : k i) (h2 : term59 _125820 i k x) (h3 : x = i) : False.
Proof. exact (EQ_MP (@lem6876378 _125820 k x i h1 h2 h3) (@lem6876034 _125820 k i h1)). Qed.
Lemma lem6876380 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : term55 _125820 i k x) : False.
Proof. exact (or_elim (@lem6876027 _125820 i k x h1) (fun h0 : term60 _125820 k x => @lem6876375 _125820 i k x h0 h1) (fun h0 : x = i => @lem6876373 _125820 k x i h1 h0)). Qed.
Lemma lem6876381 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (x : _125820) (h1 : k i) (h2 : term59 _125820 i k x) : False.
Proof. exact (or_elim (@lem6876020 _125820 i k x h2) (fun h0 : x = i => @lem6876379 _125820 k x i h1 h2 h0) (fun h0 : term16 _125820 k x i => @lem6876275 _125820 i k x h0 h2)). Qed.
Lemma lem6876382 {_125820 : Type'} (x : _125820) (k : _125820 -> Prop) (i : _125820) (h1 : term42 _125820 i k x) (h2 : k i) : False.
Proof. exact (or_elim (@lem6876016 _125820 i k x h1) (fun h0 : term59 _125820 i k x => @lem6876381 _125820 i k x h2 h0) (fun h0 : term55 _125820 i k x => @lem6876380 _125820 i k x h0)). Qed.
Lemma lem6876383 {_125820 : Type'} (x : _125820) (k : _125820 -> Prop) (i : _125820) (h1 : term42 _125820 i k x) (h2 : k i) : (k i) = False.
Proof. exact (prop_ext (fun h3 : k i => @lem6876382 _125820 x k i h1 h2) (fun h3 : False => @lem6875954 _125820 k i h2)). Qed.
Lemma lem6876384 {_125820 : Type'} (x : _125820) (k : _125820 -> Prop) (i : _125820) (h1 : term42 _125820 i k x) (h2 : k i) : False.
Proof. exact (EQ_MP (@lem6876383 _125820 x k i h1 h2) (@lem6875954 _125820 k i h2)). Qed.
Lemma lem6876385 {_125820 : Type'} (x : _125820) (k : _125820 -> Prop) (i : _125820) (h1 : term42 _125820 i k x) (h2 : k i) : (k i) = False.
Proof. exact (prop_ext (fun h3 : k i => @lem6876384 _125820 x k i h1 h2) (fun h3 : False => @lem6875908 _125820 k i h2)). Qed.
Lemma lem6876386 {_125820 : Type'} (x : _125820) (k : _125820 -> Prop) (i : _125820) (h1 : term42 _125820 i k x) (h2 : k i) : False.
Proof. exact (EQ_MP (@lem6876385 _125820 x k i h1 h2) (@lem6875908 _125820 k i h2)). Qed.
Lemma lem6876387 {_125820 : Type'} (x : _125820) (k : _125820 -> Prop) (i : _125820) (h1 : term42 _125820 i k x) (h2 : k i) : (term42 _125820 i k x) = False.
Proof. exact (prop_ext (fun h3 : term42 _125820 i k x => @lem6876386 _125820 x k i h1 h2) (fun h3 : False => @lem6875902 _125820 i k x h1)). Qed.
Lemma lem6876388 {_125820 : Type'} (x : _125820) (k : _125820 -> Prop) (i : _125820) (h1 : term42 _125820 i k x) (h2 : k i) : False.
Proof. exact (EQ_MP (@lem6876387 _125820 x k i h1 h2) (@lem6875902 _125820 i k x h1)). Qed.
Lemma lem6876389 {_125820 : Type'} (x : _125820) (k : _125820 -> Prop) (i : _125820) (h1 : k i) : term41 _125820 i k x.
Proof. exact (fun h0 : term42 _125820 i k x => @lem6876388 _125820 x k i h0 h1). Qed.
Lemma lem6876390 {_125820 : Type'} (x : _125820) (k : _125820 -> Prop) (i : _125820) (h1 : k i) : (term18 _125820 k x i) = (k x).
Proof. exact (EQ_MP (@lem6875901 _125820 i k x) (@lem6876389 _125820 x k i h1)). Qed.
Lemma lem6876395 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) (h1 : k i) : term23 _125820 i k.
Proof. exact (fun x : _125820 => @lem6876390 _125820 x k i h1). Qed.
Lemma lem6876396 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : term24 _125820 i k.
Proof. exact (fun h0 : k i => @lem6876395 _125820 k i h0). Qed.
Lemma lem6876401 {_125820 : Type'} (k : _125820 -> Prop) : term36 _125820 k.
Proof. exact (fun i : _125820 => @lem6876396 _125820 i k). Qed.
Lemma lem6876406 {_125820 : Type'} : term40 _125820.
Proof. exact (fun k : _125820 -> Prop => @lem6876401 _125820 k). Qed.
Lemma lem6876407 {_125820 : Type'} : term39 _125820.
Proof. exact (EQ_MP (@lem6875896 _125820) (@lem6876406 _125820)). Qed.
Lemma lem6876408 {_125820 : Type'} (k : _125820 -> Prop) : term77 _125820 k.
Proof. exact (@lem6876407 _125820 k). Qed.
Lemma lem6876409 {_125820 : Type'} (k : _125820 -> Prop) : (term77 _125820 k) = (term35 _125820 k).
Proof. exact (eq_refl (term77 _125820 k)). Qed.
Lemma lem6876410 {_125820 : Type'} (k : _125820 -> Prop) : term35 _125820 k.
Proof. exact (EQ_MP (@lem6876409 _125820 k) (@lem6876408 _125820 k)). Qed.
Lemma lem6876411 {_125820 : Type'} (k : _125820 -> Prop) (i : _125820) : term78 _125820 k i.
Proof. exact (@lem6876410 _125820 k i). Qed.
Lemma lem6876412 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : (term78 _125820 k i) = (term26 _125820 i k).
Proof. exact (eq_refl (term78 _125820 k i)). Qed.
Lemma lem6876413 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : term26 _125820 i k.
Proof. exact (EQ_MP (@lem6876412 _125820 i k) (@lem6876411 _125820 k i)). Qed.
Lemma lem6876415 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : term26 _125820 i k.
Proof. exact (@lem6875797 _125820 i k (@lem6876413 _125820 i k)). Qed.
Lemma lem6876416 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (h1 : term27 _125820 i k) : False.
Proof. exact (@lem6876415 _125820 i k (@lem6875781 _125820 i k h1)). Qed.
Lemma lem6876417 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (h1 : term27 _125820 i k) : (term27 _125820 i k) = False.
Proof. exact (prop_ext (fun h2 : term27 _125820 i k => @lem6876416 _125820 i k h1) (fun h2 : False => @lem6875781 _125820 i k h1)). Qed.
Lemma lem6876418 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (h1 : term27 _125820 i k) : False.
Proof. exact (EQ_MP (@lem6876417 _125820 i k h1) (@lem6875781 _125820 i k h1)). Qed.
Lemma lem6876419 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : term26 _125820 i k.
Proof. exact (fun h0 : term27 _125820 i k => @lem6876418 _125820 i k h0). Qed.
Lemma lem6876420 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : term24 _125820 i k.
Proof. exact (EQ_MP (@lem6875780 _125820 i k) (@lem6876419 _125820 i k)). Qed.
Lemma lem6876421 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : term5 _125820 i k.
Proof. exact (EQ_MP (@lem6875776 _125820 i k) (@lem6876420 _125820 i k)). Qed.
Lemma lem6876422 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : term4 _125820 i k.
Proof. exact (EQ_MP (@lem6875710 _125820 i k) (@lem6876421 _125820 i k)). Qed.
Lemma lem6876423 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term79 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem6876424 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term79 _120477 _120519 _120521 op) = (term80 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term79 _120477 _120519 _120521 op)). Qed.
Lemma lem6876454 (n : nat) : (term81 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem6876456 (n : nat) : (term82 n) = (term82 n).
Proof. exact (eq_refl (term82 n)). Qed.
Lemma lem6876457 (n : nat) : (term83 n) = (term84 n).
Proof. exact (MK_COMB (@lem6876456 n) (@lem6876454 n)). Qed.
Lemma lem6876462 (n : nat) : (term85 n) = (term85 n).
Proof. exact (eq_refl (term85 n)). Qed.
Lemma lem6876463 (n : nat) : (term86 n) = (term87 n).
Proof. exact (MK_COMB (@lem6876462 n) (@lem6876457 n)). Qed.
Lemma lem6876464 (n : nat) : ((term88 n) = (term89 n)) = (term86 n).
Proof. exact (@lem17500 (term88 n) (term89 n)). Qed.
Lemma lem6876466 (n : nat) : ((term88 n) = (term89 n)) = (term87 n).
Proof. exact (TRANS (@lem6876464 n) (@lem6876463 n)). Qed.
Lemma lem6876467 (n : nat) : (term90 n) = (term91 n).
Proof. exact (@lem1032781 n term92 (term93 n)). Qed.
Lemma lem6876468 (d : nat) (n : nat) : (term94 n d) = (term95 d n).
Proof. exact (eq_refl (term94 n d)). Qed.
Lemma lem6876469 (n : nat) (d : nat) : (term96 n d) = (term96 n d).
Proof. exact (eq_refl (term96 n d)). Qed.
Lemma lem6876470 (d : nat) (n : nat) : (term97 n d) = (term98 d n).
Proof. exact (MK_COMB (@lem6876469 n d) (@lem6876468 d n)). Qed.
Lemma lem6876471 (n : nat) : (term99 n) = (term100 n).
Proof. exact (fun_ext (fun d : nat => @lem6876470 d n)). Qed.
Lemma lem6876472 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6876473 (n : nat) : (term91 n) = (term101 n).
Proof. exact (MK_COMB (@lem6876472) (@lem6876471 n)). Qed.
Lemma lem6876474 (n : nat) : (term90 n) = (term87 n).
Proof. exact (eq_refl (term90 n)). Qed.
Lemma lem6876475 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6876476 (n : nat) : (term102 n) = (term103 n).
Proof. exact (MK_COMB (@lem6876475) (@lem6876474 n)). Qed.
Lemma lem6876477 (n : nat) : ((term90 n) = (term91 n)) = ((term87 n) = (term101 n)).
Proof. exact (MK_COMB (@lem6876476 n) (@lem6876473 n)). Qed.
Lemma lem6876478 (n : nat) : (term87 n) = (term101 n).
Proof. exact (EQ_MP (@lem6876477 n) (@lem6876467 n)). Qed.
Lemma lem6876479 (d : nat) (n : nat) : (term98 d n) = (term98 d n).
Proof. exact (eq_refl (term98 d n)). Qed.
Lemma lem6876480 (n : nat) : (term100 n) = (term100 n).
Proof. exact (fun_ext (fun d : nat => @lem6876479 d n)). Qed.
Lemma lem6876481 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6876482 (n : nat) : (term101 n) = (term101 n).
Proof. exact (MK_COMB (@lem6876481) (@lem6876480 n)). Qed.
Lemma lem6876483 (n : nat) : (term103 n) = (term103 n).
Proof. exact (eq_refl (term103 n)). Qed.
Lemma lem6876484 (n : nat) : ((term87 n) = (term101 n)) = ((term87 n) = (term101 n)).
Proof. exact (MK_COMB (@lem6876483 n) (@lem6876482 n)). Qed.
Lemma lem6876485 (n : nat) : (term87 n) = (term101 n).
Proof. exact (EQ_MP (@lem6876484 n) (@lem6876478 n)). Qed.
Lemma lem6876516 (n : nat) : ((term88 n) = (term89 n)) = (term101 n).
Proof. exact (TRANS (@lem6876466 n) (@lem6876485 n)). Qed.
Lemma lem6876549 (d : nat) (n : nat) : (term95 d n) = (term95 d n).
Proof. exact (eq_refl (term95 d n)). Qed.
Lemma lem6876566 (n : nat) (d : nat) : (term104 n d) = (term104 n d).
Proof. exact (eq_refl (term104 n d)). Qed.
Lemma lem6876573 (d : nat) : (term105 d) = (term106 d).
Proof. exact (@lem1032098 d term92). Qed.
Lemma lem6876576 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem6876577 (n : nat) (d : nat) : (n = (term105 d)) = (n = (term106 d)).
Proof. exact (MK_COMB (@lem6876576 n) (@lem6876573 d)). Qed.
Lemma lem6876578 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6876579 (n : nat) (d : nat) : (term107 n d) = (term108 n d).
Proof. exact (MK_COMB (@lem6876578) (@lem6876577 n d)). Qed.
Lemma lem6876580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6876581 (n : nat) (d : nat) : (term109 n d) = (term110 n d).
Proof. exact (MK_COMB (@lem6876580) (@lem6876579 n d)). Qed.
Lemma lem6876582 (n : nat) (d : nat) : (term111 n d) = (term112 n d).
Proof. exact (MK_COMB (@lem6876581 n d) (@lem6876566 n d)). Qed.
Lemma lem6876583 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6876584 (n : nat) (d : nat) : (term96 n d) = (term113 n d).
Proof. exact (MK_COMB (@lem6876583) (@lem6876582 n d)). Qed.
Lemma lem6876585 (d : nat) (n : nat) : (term98 d n) = (term114 d n).
Proof. exact (MK_COMB (@lem6876584 n d) (@lem6876549 d n)). Qed.
Lemma lem6876586 (n : nat) : (term100 n) = (term115 n).
Proof. exact (fun_ext (fun d : nat => @lem6876585 d n)). Qed.
Lemma lem6876587 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6876588 (n : nat) : (term101 n) = (term116 n).
Proof. exact (MK_COMB (@lem6876587) (@lem6876586 n)). Qed.
Lemma lem6876591 (n : nat) : ((term88 n) = (term89 n)) = (term116 n).
Proof. exact (TRANS (@lem6876516 n) (@lem6876588 n)). Qed.
Lemma lem6876593 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6876594 (n : nat) (d : nat) : (n = (term106 d)) = ((int_of_num n) = (term117 d)).
Proof. exact (@lem6876593 n (term106 d)). Qed.
Lemma lem6876598 (m : nat) (n : nat) : (term118 m n) = (term119 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem6876599 (d : nat) : (term117 d) = (term120 d).
Proof. exact (@lem6876598 d term92). Qed.
Lemma lem6876600 (n : nat) : (term121 n) = (term121 n).
Proof. exact (eq_refl (term121 n)). Qed.
Lemma lem6876601 (n : nat) (d : nat) : ((int_of_num n) = (term117 d)) = ((int_of_num n) = (term120 d)).
Proof. exact (MK_COMB (@lem6876600 n) (@lem6876599 d)). Qed.
Lemma lem6876602 (n : nat) (d : nat) : (n = (term106 d)) = ((int_of_num n) = (term120 d)).
Proof. exact (TRANS (@lem6876594 n d) (@lem6876601 n d)). Qed.
Lemma lem6876603 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6876604 (n : nat) (d : nat) : (term108 n d) = (term122 n d).
Proof. exact (MK_COMB (@lem6876603) (@lem6876602 n d)). Qed.
Lemma lem6876605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6876606 (n : nat) (d : nat) : (term110 n d) = (term123 n d).
Proof. exact (MK_COMB (@lem6876605) (@lem6876604 n d)). Qed.
Lemma lem6876608 (m : nat) (n : nat) : (Peano.lt m n) = (term124 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem6876609 (n : nat) : (term125 n) = (term126 n).
Proof. exact (@lem6876608 n term92). Qed.
Lemma lem6876610 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6876611 (n : nat) : (term127 n) = (term128 n).
Proof. exact (MK_COMB (@lem6876610) (@lem6876609 n)). Qed.
Lemma lem6876612 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6876613 (n : nat) : (term129 n) = (term130 n).
Proof. exact (MK_COMB (@lem6876612) (@lem6876611 n)). Qed.
Lemma lem6876615 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6876616 (d : nat) : (d = (NUMERAL 0)) = ((int_of_num d) = term131).
Proof. exact (@lem6876615 d (NUMERAL 0)). Qed.
Lemma lem6876619 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6876620 (d : nat) : (term89 d) = (term132 d).
Proof. exact (MK_COMB (@lem6876619) (@lem6876616 d)). Qed.
Lemma lem6876621 (n : nat) (d : nat) : (term104 n d) = (term133 n d).
Proof. exact (MK_COMB (@lem6876613 n) (@lem6876620 d)). Qed.
Lemma lem6876622 (n : nat) (d : nat) : (term112 n d) = (term134 n d).
Proof. exact (MK_COMB (@lem6876606 n d) (@lem6876621 n d)). Qed.
Lemma lem6876623 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6876624 (n : nat) (d : nat) : (term113 n d) = (term135 n d).
Proof. exact (MK_COMB (@lem6876623) (@lem6876622 n d)). Qed.
Lemma lem6876626 (m : nat) (n : nat) : (Peano.lt m n) = (term124 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem6876627 (d : nat) (n : nat) : (Peano.lt d n) = (term124 d n).
Proof. exact (@lem6876626 d n). Qed.
Lemma lem6876628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6876629 (d : nat) (n : nat) : (term136 d n) = (term137 d n).
Proof. exact (MK_COMB (@lem6876628) (@lem6876627 d n)). Qed.
Lemma lem6876631 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6876632 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term131).
Proof. exact (@lem6876631 n (NUMERAL 0)). Qed.
Lemma lem6876635 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6876636 (n : nat) : (term89 n) = (term132 n).
Proof. exact (MK_COMB (@lem6876635) (@lem6876632 n)). Qed.
Lemma lem6876637 (d : nat) (n : nat) : (term138 d n) = (term139 d n).
Proof. exact (MK_COMB (@lem6876629 d n) (@lem6876636 n)). Qed.
Lemma lem6876638 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6876639 (d : nat) (n : nat) : (term140 d n) = (term141 d n).
Proof. exact (MK_COMB (@lem6876638) (@lem6876637 d n)). Qed.
Lemma lem6876641 (m : nat) (n : nat) : (Peano.lt m n) = (term124 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem6876642 (d : nat) (n : nat) : (Peano.lt d n) = (term124 d n).
Proof. exact (@lem6876641 d n). Qed.
Lemma lem6876643 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6876644 (d : nat) (n : nat) : (term142 d n) = (term143 d n).
Proof. exact (MK_COMB (@lem6876643) (@lem6876642 d n)). Qed.
Lemma lem6876645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6876646 (d : nat) (n : nat) : (term144 d n) = (term145 d n).
Proof. exact (MK_COMB (@lem6876645) (@lem6876644 d n)). Qed.
Lemma lem6876648 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6876649 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term131).
Proof. exact (@lem6876648 n (NUMERAL 0)). Qed.
Lemma lem6876652 (d : nat) (n : nat) : (term146 d n) = (term147 d n).
Proof. exact (MK_COMB (@lem6876646 d n) (@lem6876649 n)). Qed.
Lemma lem6876653 (d : nat) (n : nat) : (term95 d n) = (term148 d n).
Proof. exact (MK_COMB (@lem6876639 d n) (@lem6876652 d n)). Qed.
Lemma lem6876654 (d : nat) (n : nat) : (term114 d n) = (term149 d n).
Proof. exact (MK_COMB (@lem6876624 n d) (@lem6876653 d n)). Qed.
Lemma lem6876655 (n : nat) : (term115 n) = (term150 n).
Proof. exact (fun_ext (fun d : nat => @lem6876654 d n)). Qed.
Lemma lem6876656 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6876657 (n : nat) : (term116 n) = (term151 n).
Proof. exact (MK_COMB (@lem6876656) (@lem6876655 n)). Qed.
Lemma lem6876658 (n : nat) : ((term88 n) = (term89 n)) = (term151 n).
Proof. exact (TRANS (@lem6876591 n) (@lem6876657 n)). Qed.
Lemma lem6876659 (d : nat) : term152 d.
Proof. exact (@lem2307535 d). Qed.
Lemma lem6876660 (d : nat) : (term152 d) = (term153 d).
Proof. exact (eq_refl (term152 d)). Qed.
Lemma lem6876661 (d : nat) : term153 d.
Proof. exact (EQ_MP (@lem6876660 d) (@lem6876659 d)). Qed.
Lemma lem6876662 (n : nat) : term152 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem6876663 (n : nat) : (term152 n) = (term153 n).
Proof. exact (eq_refl (term152 n)). Qed.
Lemma lem6876664 (n : nat) : term153 n.
Proof. exact (EQ_MP (@lem6876663 n) (@lem6876662 n)). Qed.
Lemma lem6876665 (_91911 : int) (_91912 : int) : (term154 _91911 _91912) = (term155 _91911 _91912).
Proof. exact (@lem2318604 (term155 _91911 _91912)). Qed.
Lemma lem6876691 (_91912 : int) (_91911 : int) : (term156 _91912 _91911) = (_91912 = (term157 _91911)).
Proof. exact (@lem16933 (_91912 = (term157 _91911))). Qed.
Lemma lem6876694 (_91912 : int) : (term158 _91912) = (term159 _91912).
Proof. exact (@lem16933 (term159 _91912)). Qed.
Lemma lem6876697 (_91911 : int) : (term160 _91911) = (_91911 = term131).
Proof. exact (@lem16933 (_91911 = term131)). Qed.
Lemma lem6876698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6876699 (_91912 : int) : (term161 _91912) = (term162 _91912).
Proof. exact (MK_COMB (@lem6876698) (@lem6876694 _91912)). Qed.
Lemma lem6876700 (_91912 : int) (_91911 : int) : (term163 _91912 _91911) = (term164 _91912 _91911).
Proof. exact (MK_COMB (@lem6876699 _91912) (@lem6876697 _91911)). Qed.
Lemma lem6876701 (_91912 : int) (_91911 : int) : (term165 _91912 _91911) = (term163 _91912 _91911).
Proof. exact (@lem17160 (term166 _91912) (term167 _91911)). Qed.
Lemma lem6876702 (_91912 : int) (_91911 : int) : (term165 _91912 _91911) = (term164 _91912 _91911).
Proof. exact (TRANS (@lem6876701 _91912 _91911) (@lem6876700 _91912 _91911)). Qed.
Lemma lem6876703 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6876704 (_91912 : int) (_91911 : int) : (term168 _91912 _91911) = (term169 _91912 _91911).
Proof. exact (MK_COMB (@lem6876703) (@lem6876691 _91912 _91911)). Qed.
Lemma lem6876705 (_91912 : int) (_91911 : int) : (term170 _91912 _91911) = (term171 _91912 _91911).
Proof. exact (MK_COMB (@lem6876704 _91912 _91911) (@lem6876702 _91912 _91911)). Qed.
Lemma lem6876706 (_91912 : int) (_91911 : int) : (term172 _91912 _91911) = (term170 _91912 _91911).
Proof. exact (@lem17045 (term173 _91912 _91911) (term174 _91912 _91911)). Qed.
Lemma lem6876707 (_91912 : int) (_91911 : int) : (term172 _91912 _91911) = (term171 _91912 _91911).
Proof. exact (TRANS (@lem6876706 _91912 _91911) (@lem6876705 _91912 _91911)). Qed.
Lemma lem6876711 (_91912 : int) : (term160 _91912) = (_91912 = term131).
Proof. exact (@lem16933 (_91912 = term131)). Qed.
Lemma lem6876713 (_91911 : int) (_91912 : int) : (term175 _91911 _91912) = (term175 _91911 _91912).
Proof. exact (eq_refl (term175 _91911 _91912)). Qed.
Lemma lem6876714 (_91911 : int) (_91912 : int) : (term176 _91911 _91912) = (term177 _91911 _91912).
Proof. exact (MK_COMB (@lem6876713 _91911 _91912) (@lem6876711 _91912)). Qed.
Lemma lem6876715 (_91911 : int) (_91912 : int) : (term178 _91911 _91912) = (term176 _91911 _91912).
Proof. exact (@lem17045 (int_lt _91911 _91912) (term167 _91912)). Qed.
Lemma lem6876716 (_91911 : int) (_91912 : int) : (term178 _91911 _91912) = (term177 _91911 _91912).
Proof. exact (TRANS (@lem6876715 _91911 _91912) (@lem6876714 _91911 _91912)). Qed.
Lemma lem6876719 (_91911 : int) (_91912 : int) : (term179 _91911 _91912) = (int_lt _91911 _91912).
Proof. exact (@lem16933 (int_lt _91911 _91912)). Qed.
Lemma lem6876720 (_91912 : int) : (term167 _91912) = (term167 _91912).
Proof. exact (eq_refl (term167 _91912)). Qed.
Lemma lem6876721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6876722 (_91911 : int) (_91912 : int) : (term180 _91911 _91912) = (term181 _91911 _91912).
Proof. exact (MK_COMB (@lem6876721) (@lem6876719 _91911 _91912)). Qed.
Lemma lem6876723 (_91911 : int) (_91912 : int) : (term182 _91911 _91912) = (term183 _91911 _91912).
Proof. exact (MK_COMB (@lem6876722 _91911 _91912) (@lem6876720 _91912)). Qed.
Lemma lem6876724 (_91911 : int) (_91912 : int) : (term184 _91911 _91912) = (term182 _91911 _91912).
Proof. exact (@lem17045 (term185 _91911 _91912) (_91912 = term131)). Qed.
Lemma lem6876725 (_91911 : int) (_91912 : int) : (term184 _91911 _91912) = (term183 _91911 _91912).
Proof. exact (TRANS (@lem6876724 _91911 _91912) (@lem6876723 _91911 _91912)). Qed.
Lemma lem6876726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6876727 (_91911 : int) (_91912 : int) : (term186 _91911 _91912) = (term187 _91911 _91912).
Proof. exact (MK_COMB (@lem6876726) (@lem6876716 _91911 _91912)). Qed.
Lemma lem6876728 (_91911 : int) (_91912 : int) : (term188 _91911 _91912) = (term189 _91911 _91912).
Proof. exact (MK_COMB (@lem6876727 _91911 _91912) (@lem6876725 _91911 _91912)). Qed.
Lemma lem6876729 (_91911 : int) (_91912 : int) : (term190 _91911 _91912) = (term188 _91911 _91912).
Proof. exact (@lem17160 (term191 _91911 _91912) (term192 _91911 _91912)). Qed.
Lemma lem6876730 (_91911 : int) (_91912 : int) : (term190 _91911 _91912) = (term189 _91911 _91912).
Proof. exact (TRANS (@lem6876729 _91911 _91912) (@lem6876728 _91911 _91912)). Qed.
Lemma lem6876731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6876732 (_91912 : int) (_91911 : int) : (term193 _91912 _91911) = (term194 _91912 _91911).
Proof. exact (MK_COMB (@lem6876731) (@lem6876707 _91912 _91911)). Qed.
Lemma lem6876733 (_91911 : int) (_91912 : int) : (term195 _91911 _91912) = (term196 _91911 _91912).
Proof. exact (MK_COMB (@lem6876732 _91912 _91911) (@lem6876730 _91911 _91912)). Qed.
Lemma lem6876734 (_91911 : int) (_91912 : int) : (term197 _91911 _91912) = (term195 _91911 _91912).
Proof. exact (@lem17160 (term198 _91912 _91911) (term199 _91911 _91912)). Qed.
Lemma lem6876735 (_91911 : int) (_91912 : int) : (term197 _91911 _91912) = (term196 _91911 _91912).
Proof. exact (TRANS (@lem6876734 _91911 _91912) (@lem6876733 _91911 _91912)). Qed.
Lemma lem6876737 (_91912 : int) : (term200 _91912) = (term200 _91912).
Proof. exact (eq_refl (term200 _91912)). Qed.
Lemma lem6876738 (_91911 : int) (_91912 : int) : (term201 _91911 _91912) = (term202 _91911 _91912).
Proof. exact (MK_COMB (@lem6876737 _91912) (@lem6876735 _91911 _91912)). Qed.
Lemma lem6876739 (_91911 : int) (_91912 : int) : (term203 _91911 _91912) = (term201 _91911 _91912).
Proof. exact (@lem17362 (term204 _91912) (term205 _91911 _91912)). Qed.
Lemma lem6876740 (_91911 : int) (_91912 : int) : (term203 _91911 _91912) = (term202 _91911 _91912).
Proof. exact (TRANS (@lem6876739 _91911 _91912) (@lem6876738 _91911 _91912)). Qed.
Lemma lem6876742 (_91911 : int) : (term200 _91911) = (term200 _91911).
Proof. exact (eq_refl (term200 _91911)). Qed.
Lemma lem6876743 (_91911 : int) (_91912 : int) : (term206 _91911 _91912) = (term207 _91911 _91912).
Proof. exact (MK_COMB (@lem6876742 _91911) (@lem6876740 _91911 _91912)). Qed.
Lemma lem6876744 (_91911 : int) (_91912 : int) : (term208 _91911 _91912) = (term206 _91911 _91912).
Proof. exact (@lem17362 (term204 _91911) (term209 _91911 _91912)). Qed.
Lemma lem6876784 (_91911 : int) (_91912 : int) : (term208 _91911 _91912) = (term207 _91911 _91912).
Proof. exact (TRANS (@lem6876744 _91911 _91912) (@lem6876743 _91911 _91912)). Qed.
Lemma lem6876787 (x : int) (y : int) : (int_le x y) = (term210 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6876788 (_91911 : int) : (term204 _91911) = (term211 _91911).
Proof. exact (@lem6876787 term131 _91911). Qed.
Lemma lem6876790 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6876791 : term213 = term214.
Proof. exact (@lem6876790 (NUMERAL 0)). Qed.
Lemma lem6876792 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6876793 : term215 = term216.
Proof. exact (MK_COMB (@lem6876792) (@lem6876791)). Qed.
Lemma lem6876794 (_91911 : int) : (real_of_int _91911) = (real_of_int _91911).
Proof. exact (eq_refl (real_of_int _91911)). Qed.
Lemma lem6876795 (_91911 : int) : (term211 _91911) = (term217 _91911).
Proof. exact (MK_COMB (@lem6876793) (@lem6876794 _91911)). Qed.
Lemma lem6876797 (_91911 : int) : (term204 _91911) = (term217 _91911).
Proof. exact (TRANS (@lem6876788 _91911) (@lem6876795 _91911)). Qed.
Lemma lem6876800 (x : int) (y : int) : (int_le x y) = (term210 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6876801 (_91912 : int) : (term204 _91912) = (term211 _91912).
Proof. exact (@lem6876800 term131 _91912). Qed.
Lemma lem6876803 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6876804 : term213 = term214.
Proof. exact (@lem6876803 (NUMERAL 0)). Qed.
Lemma lem6876805 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6876806 : term215 = term216.
Proof. exact (MK_COMB (@lem6876805) (@lem6876804)). Qed.
Lemma lem6876807 (_91912 : int) : (real_of_int _91912) = (real_of_int _91912).
Proof. exact (eq_refl (real_of_int _91912)). Qed.
Lemma lem6876808 (_91912 : int) : (term211 _91912) = (term217 _91912).
Proof. exact (MK_COMB (@lem6876806) (@lem6876807 _91912)). Qed.
Lemma lem6876810 (_91912 : int) : (term204 _91912) = (term217 _91912).
Proof. exact (TRANS (@lem6876801 _91912) (@lem6876808 _91912)). Qed.
Lemma lem6876813 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem6876814 (_91912 : int) (_91911 : int) : (_91912 = (term157 _91911)) = ((real_of_int _91912) = (term218 _91911)).
Proof. exact (@lem6876813 _91912 (term157 _91911)). Qed.
Lemma lem6876818 (x : int) (y : int) : (term219 x y) = (term220 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6876819 (_91911 : int) : (term218 _91911) = (term221 _91911).
Proof. exact (@lem6876818 _91911 term222). Qed.
Lemma lem6876821 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6876822 : term223 = term224.
Proof. exact (@lem6876821 term92). Qed.
Lemma lem6876823 (_91911 : int) : (term225 _91911) = (term225 _91911).
Proof. exact (eq_refl (term225 _91911)). Qed.
Lemma lem6876824 (_91911 : int) : (term221 _91911) = (term226 _91911).
Proof. exact (MK_COMB (@lem6876823 _91911) (@lem6876822)). Qed.
Lemma lem6876825 (_91911 : int) : (term218 _91911) = (term226 _91911).
Proof. exact (TRANS (@lem6876819 _91911) (@lem6876824 _91911)). Qed.
Lemma lem6876826 (_91912 : int) : (term227 _91912) = (term227 _91912).
Proof. exact (eq_refl (term227 _91912)). Qed.
Lemma lem6876827 (_91912 : int) (_91911 : int) : ((real_of_int _91912) = (term218 _91911)) = ((real_of_int _91912) = (term226 _91911)).
Proof. exact (MK_COMB (@lem6876826 _91912) (@lem6876825 _91911)). Qed.
Lemma lem6876829 (_91912 : int) (_91911 : int) : (_91912 = (term157 _91911)) = ((real_of_int _91912) = (term226 _91911)).
Proof. exact (TRANS (@lem6876814 _91912 _91911) (@lem6876827 _91912 _91911)). Qed.
Lemma lem6876831 (x : int) (y : int) : (int_lt x y) = (term228 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem6876832 (_91912 : int) : (term159 _91912) = (term229 _91912).
Proof. exact (@lem6876831 _91912 term222). Qed.
Lemma lem6876834 (x : int) (y : int) : (int_le x y) = (term210 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6876835 (_91912 : int) : (term229 _91912) = (term230 _91912).
Proof. exact (@lem6876834 (term157 _91912) term222). Qed.
Lemma lem6876837 (x : int) (y : int) : (term219 x y) = (term220 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6876838 (_91912 : int) : (term218 _91912) = (term221 _91912).
Proof. exact (@lem6876837 _91912 term222). Qed.
Lemma lem6876840 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6876841 : term223 = term224.
Proof. exact (@lem6876840 term92). Qed.
Lemma lem6876842 (_91912 : int) : (term225 _91912) = (term225 _91912).
Proof. exact (eq_refl (term225 _91912)). Qed.
Lemma lem6876843 (_91912 : int) : (term221 _91912) = (term226 _91912).
Proof. exact (MK_COMB (@lem6876842 _91912) (@lem6876841)). Qed.
Lemma lem6876844 (_91912 : int) : (term218 _91912) = (term226 _91912).
Proof. exact (TRANS (@lem6876838 _91912) (@lem6876843 _91912)). Qed.
Lemma lem6876845 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6876846 (_91912 : int) : (term231 _91912) = (term232 _91912).
Proof. exact (MK_COMB (@lem6876845) (@lem6876844 _91912)). Qed.
Lemma lem6876848 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6876849 : term223 = term224.
Proof. exact (@lem6876848 term92). Qed.
Lemma lem6876850 (_91912 : int) : (term230 _91912) = (term233 _91912).
Proof. exact (MK_COMB (@lem6876846 _91912) (@lem6876849)). Qed.
Lemma lem6876851 (_91912 : int) : (term229 _91912) = (term233 _91912).
Proof. exact (TRANS (@lem6876835 _91912) (@lem6876850 _91912)). Qed.
Lemma lem6876852 (_91912 : int) : (term159 _91912) = (term233 _91912).
Proof. exact (TRANS (@lem6876832 _91912) (@lem6876851 _91912)). Qed.
Lemma lem6876855 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem6876856 (_91911 : int) : (_91911 = term131) = ((real_of_int _91911) = term213).
Proof. exact (@lem6876855 _91911 term131). Qed.
Lemma lem6876860 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6876861 : term213 = term214.
Proof. exact (@lem6876860 (NUMERAL 0)). Qed.
Lemma lem6876862 (_91911 : int) : (term227 _91911) = (term227 _91911).
Proof. exact (eq_refl (term227 _91911)). Qed.
Lemma lem6876863 (_91911 : int) : ((real_of_int _91911) = term213) = ((real_of_int _91911) = term214).
Proof. exact (MK_COMB (@lem6876862 _91911) (@lem6876861)). Qed.
Lemma lem6876865 (_91911 : int) : (_91911 = term131) = ((real_of_int _91911) = term214).
Proof. exact (TRANS (@lem6876856 _91911) (@lem6876863 _91911)). Qed.
Lemma lem6876866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6876867 (_91912 : int) : (term162 _91912) = (term234 _91912).
Proof. exact (MK_COMB (@lem6876866) (@lem6876852 _91912)). Qed.
Lemma lem6876868 (_91912 : int) (_91911 : int) : (term164 _91912 _91911) = (term235 _91912 _91911).
Proof. exact (MK_COMB (@lem6876867 _91912) (@lem6876865 _91911)). Qed.
Lemma lem6876869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6876870 (_91912 : int) (_91911 : int) : (term169 _91912 _91911) = (term236 _91912 _91911).
Proof. exact (MK_COMB (@lem6876869) (@lem6876829 _91912 _91911)). Qed.
Lemma lem6876871 (_91912 : int) (_91911 : int) : (term171 _91912 _91911) = (term237 _91912 _91911).
Proof. exact (MK_COMB (@lem6876870 _91912 _91911) (@lem6876868 _91912 _91911)). Qed.
Lemma lem6876873 (y : int) (x : int) : (term185 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem6876874 (_91912 : int) (_91911 : int) : (term185 _91911 _91912) = (int_le _91912 _91911).
Proof. exact (@lem6876873 _91912 _91911). Qed.
Lemma lem6876876 (x : int) (y : int) : (int_le x y) = (term210 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6876877 (_91912 : int) (_91911 : int) : (int_le _91912 _91911) = (term210 _91912 _91911).
Proof. exact (@lem6876876 _91912 _91911). Qed.
Lemma lem6876878 (_91912 : int) (_91911 : int) : (term185 _91911 _91912) = (term210 _91912 _91911).
Proof. exact (TRANS (@lem6876874 _91912 _91911) (@lem6876877 _91912 _91911)). Qed.
Lemma lem6876881 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem6876882 (_91912 : int) : (_91912 = term131) = ((real_of_int _91912) = term213).
Proof. exact (@lem6876881 _91912 term131). Qed.
Lemma lem6876886 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6876887 : term213 = term214.
Proof. exact (@lem6876886 (NUMERAL 0)). Qed.
Lemma lem6876888 (_91912 : int) : (term227 _91912) = (term227 _91912).
Proof. exact (eq_refl (term227 _91912)). Qed.
Lemma lem6876889 (_91912 : int) : ((real_of_int _91912) = term213) = ((real_of_int _91912) = term214).
Proof. exact (MK_COMB (@lem6876888 _91912) (@lem6876887)). Qed.
Lemma lem6876891 (_91912 : int) : (_91912 = term131) = ((real_of_int _91912) = term214).
Proof. exact (TRANS (@lem6876882 _91912) (@lem6876889 _91912)). Qed.
Lemma lem6876892 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6876893 (_91912 : int) (_91911 : int) : (term175 _91911 _91912) = (term238 _91912 _91911).
Proof. exact (MK_COMB (@lem6876892) (@lem6876878 _91912 _91911)). Qed.
Lemma lem6876894 (_91911 : int) (_91912 : int) : (term177 _91911 _91912) = (term239 _91911 _91912).
Proof. exact (MK_COMB (@lem6876893 _91912 _91911) (@lem6876891 _91912)). Qed.
Lemma lem6876896 (x : int) (y : int) : (int_lt x y) = (term228 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem6876897 (_91911 : int) (_91912 : int) : (int_lt _91911 _91912) = (term228 _91911 _91912).
Proof. exact (@lem6876896 _91911 _91912). Qed.
Lemma lem6876899 (x : int) (y : int) : (int_le x y) = (term210 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6876900 (_91911 : int) (_91912 : int) : (term228 _91911 _91912) = (term240 _91911 _91912).
Proof. exact (@lem6876899 (term157 _91911) _91912). Qed.
Lemma lem6876902 (x : int) (y : int) : (term219 x y) = (term220 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6876903 (_91911 : int) : (term218 _91911) = (term221 _91911).
Proof. exact (@lem6876902 _91911 term222). Qed.
Lemma lem6876905 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6876906 : term223 = term224.
Proof. exact (@lem6876905 term92). Qed.
Lemma lem6876907 (_91911 : int) : (term225 _91911) = (term225 _91911).
Proof. exact (eq_refl (term225 _91911)). Qed.
Lemma lem6876908 (_91911 : int) : (term221 _91911) = (term226 _91911).
Proof. exact (MK_COMB (@lem6876907 _91911) (@lem6876906)). Qed.
Lemma lem6876909 (_91911 : int) : (term218 _91911) = (term226 _91911).
Proof. exact (TRANS (@lem6876903 _91911) (@lem6876908 _91911)). Qed.
Lemma lem6876910 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6876911 (_91911 : int) : (term231 _91911) = (term232 _91911).
Proof. exact (MK_COMB (@lem6876910) (@lem6876909 _91911)). Qed.
Lemma lem6876912 (_91912 : int) : (real_of_int _91912) = (real_of_int _91912).
Proof. exact (eq_refl (real_of_int _91912)). Qed.
Lemma lem6876913 (_91911 : int) (_91912 : int) : (term240 _91911 _91912) = (term241 _91911 _91912).
Proof. exact (MK_COMB (@lem6876911 _91911) (@lem6876912 _91912)). Qed.
Lemma lem6876914 (_91911 : int) (_91912 : int) : (term228 _91911 _91912) = (term241 _91911 _91912).
Proof. exact (TRANS (@lem6876900 _91911 _91912) (@lem6876913 _91911 _91912)). Qed.
Lemma lem6876915 (_91911 : int) (_91912 : int) : (int_lt _91911 _91912) = (term241 _91911 _91912).
Proof. exact (TRANS (@lem6876897 _91911 _91912) (@lem6876914 _91911 _91912)). Qed.
Lemma lem6876917 (y : int) (x : int) : (term242 x y) = (term243 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem6876918 (_91912 : int) : (term167 _91912) = (term244 _91912).
Proof. exact (@lem6876917 term131 _91912). Qed.
Lemma lem6876920 (x : int) (y : int) : (int_le x y) = (term210 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6876921 (_91912 : int) : (term245 _91912) = (term246 _91912).
Proof. exact (@lem6876920 (term157 _91912) term131). Qed.
Lemma lem6876923 (x : int) (y : int) : (term219 x y) = (term220 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6876924 (_91912 : int) : (term218 _91912) = (term221 _91912).
Proof. exact (@lem6876923 _91912 term222). Qed.
Lemma lem6876926 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6876927 : term223 = term224.
Proof. exact (@lem6876926 term92). Qed.
Lemma lem6876928 (_91912 : int) : (term225 _91912) = (term225 _91912).
Proof. exact (eq_refl (term225 _91912)). Qed.
Lemma lem6876929 (_91912 : int) : (term221 _91912) = (term226 _91912).
Proof. exact (MK_COMB (@lem6876928 _91912) (@lem6876927)). Qed.
Lemma lem6876930 (_91912 : int) : (term218 _91912) = (term226 _91912).
Proof. exact (TRANS (@lem6876924 _91912) (@lem6876929 _91912)). Qed.
Lemma lem6876931 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6876932 (_91912 : int) : (term231 _91912) = (term232 _91912).
Proof. exact (MK_COMB (@lem6876931) (@lem6876930 _91912)). Qed.
Lemma lem6876934 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6876935 : term213 = term214.
Proof. exact (@lem6876934 (NUMERAL 0)). Qed.
Lemma lem6876936 (_91912 : int) : (term246 _91912) = (term247 _91912).
Proof. exact (MK_COMB (@lem6876932 _91912) (@lem6876935)). Qed.
Lemma lem6876937 (_91912 : int) : (term245 _91912) = (term247 _91912).
Proof. exact (TRANS (@lem6876921 _91912) (@lem6876936 _91912)). Qed.
Lemma lem6876938 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6876939 (_91912 : int) : (term248 _91912) = (term249 _91912).
Proof. exact (MK_COMB (@lem6876938) (@lem6876937 _91912)). Qed.
Lemma lem6876941 (x : int) (y : int) : (int_le x y) = (term210 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6876942 (_91912 : int) : (term250 _91912) = (term251 _91912).
Proof. exact (@lem6876941 term252 _91912). Qed.
Lemma lem6876944 (x : int) (y : int) : (term219 x y) = (term220 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6876945 : term253 = term254.
Proof. exact (@lem6876944 term131 term222). Qed.
Lemma lem6876947 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6876948 : term213 = term214.
Proof. exact (@lem6876947 (NUMERAL 0)). Qed.
Lemma lem6876949 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6876950 : term255 = term256.
Proof. exact (MK_COMB (@lem6876949) (@lem6876948)). Qed.
Lemma lem6876952 (n : nat) : (term212 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6876953 : term223 = term224.
Proof. exact (@lem6876952 term92). Qed.
Lemma lem6876954 : term254 = term257.
Proof. exact (MK_COMB (@lem6876950) (@lem6876953)). Qed.
Lemma lem6876955 : term253 = term257.
Proof. exact (TRANS (@lem6876945) (@lem6876954)). Qed.
Lemma lem6876956 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6876957 : term258 = term259.
Proof. exact (MK_COMB (@lem6876956) (@lem6876955)). Qed.
Lemma lem6876958 (_91912 : int) : (real_of_int _91912) = (real_of_int _91912).
Proof. exact (eq_refl (real_of_int _91912)). Qed.
Lemma lem6876959 (_91912 : int) : (term251 _91912) = (term260 _91912).
Proof. exact (MK_COMB (@lem6876957) (@lem6876958 _91912)). Qed.
Lemma lem6876960 (_91912 : int) : (term250 _91912) = (term260 _91912).
Proof. exact (TRANS (@lem6876942 _91912) (@lem6876959 _91912)). Qed.
Lemma lem6876961 (_91912 : int) : (term244 _91912) = (term261 _91912).
Proof. exact (MK_COMB (@lem6876939 _91912) (@lem6876960 _91912)). Qed.
Lemma lem6876962 (_91912 : int) : (term167 _91912) = (term261 _91912).
Proof. exact (TRANS (@lem6876918 _91912) (@lem6876961 _91912)). Qed.
Lemma lem6876963 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6876964 (_91911 : int) (_91912 : int) : (term181 _91911 _91912) = (term262 _91911 _91912).
Proof. exact (MK_COMB (@lem6876963) (@lem6876915 _91911 _91912)). Qed.
Lemma lem6876965 (_91911 : int) (_91912 : int) : (term183 _91911 _91912) = (term263 _91911 _91912).
Proof. exact (MK_COMB (@lem6876964 _91911 _91912) (@lem6876962 _91912)). Qed.
Lemma lem6876966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6876967 (_91911 : int) (_91912 : int) : (term187 _91911 _91912) = (term264 _91911 _91912).
Proof. exact (MK_COMB (@lem6876966) (@lem6876894 _91911 _91912)). Qed.
Lemma lem6876968 (_91911 : int) (_91912 : int) : (term189 _91911 _91912) = (term265 _91911 _91912).
Proof. exact (MK_COMB (@lem6876967 _91911 _91912) (@lem6876965 _91911 _91912)). Qed.
Lemma lem6876969 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6876970 (_91912 : int) (_91911 : int) : (term194 _91912 _91911) = (term266 _91912 _91911).
Proof. exact (MK_COMB (@lem6876969) (@lem6876871 _91912 _91911)). Qed.
Lemma lem6876971 (_91911 : int) (_91912 : int) : (term196 _91911 _91912) = (term267 _91911 _91912).
Proof. exact (MK_COMB (@lem6876970 _91912 _91911) (@lem6876968 _91911 _91912)). Qed.
Lemma lem6876972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6876973 (_91912 : int) : (term200 _91912) = (term268 _91912).
Proof. exact (MK_COMB (@lem6876972) (@lem6876810 _91912)). Qed.
Lemma lem6876974 (_91911 : int) (_91912 : int) : (term202 _91911 _91912) = (term269 _91911 _91912).
Proof. exact (MK_COMB (@lem6876973 _91912) (@lem6876971 _91911 _91912)). Qed.
Lemma lem6876975 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6876976 (_91911 : int) : (term200 _91911) = (term268 _91911).
Proof. exact (MK_COMB (@lem6876975) (@lem6876797 _91911)). Qed.
Lemma lem6876977 (_91911 : int) (_91912 : int) : (term207 _91911 _91912) = (term270 _91911 _91912).
Proof. exact (MK_COMB (@lem6876976 _91911) (@lem6876974 _91911 _91912)). Qed.
Lemma lem6876978 (_91911 : int) (_91912 : int) : (term208 _91911 _91912) = (term270 _91911 _91912).
Proof. exact (TRANS (@lem6876784 _91911 _91912) (@lem6876977 _91911 _91912)). Qed.
Lemma lem6876982 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6877078 (_91911 : int) (_91912 : int) : (term271 _91911 _91912) = (term270 _91911 _91912).
Proof. exact (@lem6876982 (term270 _91911 _91912)). Qed.
Lemma lem6877079 (_91911 : int) : (term217 _91911) = (term272 _91911).
Proof. exact (@lem1988287 (real_of_int _91911) term214). Qed.
Lemma lem6877085 (_91911 : int) : (term273 _91911) = (term274 _91911).
Proof. exact (@lem1982792 (real_of_int _91911) term214). Qed.
Lemma lem6877087 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6877088 : term214 = term276.
Proof. exact (@lem6877087 (NUMERAL 0)). Qed.
Lemma lem6877090 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6877091 : term279 = term280.
Proof. exact (@lem6877090 term92). Qed.
Lemma lem6877092 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6877093 : term281 = term282.
Proof. exact (MK_COMB (@lem6877092) (@lem6877091)). Qed.
Lemma lem6877094 : term283 = term284.
Proof. exact (MK_COMB (@lem6877093) (@lem6877088)). Qed.
Lemma lem6877095 : term284 = term285.
Proof. exact (@lem1981613 term279 term214 term224 term224). Qed.
Lemma lem6877097 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6877098 : term288 = term289.
Proof. exact (@lem6877097 term92 term92). Qed.
Lemma lem6877099 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877100 : term291 = term92.
Proof. exact (EQ_MP (@lem6877099) (@lem940073)). Qed.
Lemma lem6877101 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877102 : term289 = term224.
Proof. exact (MK_COMB (@lem6877101) (@lem6877100)). Qed.
Lemma lem6877103 : term288 = term224.
Proof. exact (TRANS (@lem6877098) (@lem6877102)). Qed.
Lemma lem6877105 (x : nat) : (term292 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6877106 : term283 = term214.
Proof. exact (@lem6877105 term92). Qed.
Lemma lem6877107 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6877108 : term293 = term294.
Proof. exact (MK_COMB (@lem6877107) (@lem6877106)). Qed.
Lemma lem6877109 : term285 = term276.
Proof. exact (MK_COMB (@lem6877108) (@lem6877103)). Qed.
Lemma lem6877110 : term284 = term276.
Proof. exact (TRANS (@lem6877095) (@lem6877109)). Qed.
Lemma lem6877111 : term283 = term276.
Proof. exact (TRANS (@lem6877094) (@lem6877110)). Qed.
Lemma lem6877113 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6877114 : term276 = term214.
Proof. exact (@lem6877113 term214). Qed.
Lemma lem6877115 : term283 = term214.
Proof. exact (TRANS (@lem6877111) (@lem6877114)). Qed.
Lemma lem6877116 (_91911 : int) : (term225 _91911) = (term225 _91911).
Proof. exact (eq_refl (term225 _91911)). Qed.
Lemma lem6877117 (_91911 : int) : (term274 _91911) = (term296 _91911).
Proof. exact (MK_COMB (@lem6877116 _91911) (@lem6877115)). Qed.
Lemma lem6877118 (_91911 : int) : (term296 _91911) = (real_of_int _91911).
Proof. exact (@lem1982723 (real_of_int _91911)). Qed.
Lemma lem6877119 (_91911 : int) : (term274 _91911) = (real_of_int _91911).
Proof. exact (TRANS (@lem6877117 _91911) (@lem6877118 _91911)). Qed.
Lemma lem6877121 (_91911 : int) : (term273 _91911) = (real_of_int _91911).
Proof. exact (TRANS (@lem6877085 _91911) (@lem6877119 _91911)). Qed.
Lemma lem6877122 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6877123 (_91911 : int) : (term297 _91911) = (term298 _91911).
Proof. exact (MK_COMB (@lem6877122) (@lem6877121 _91911)). Qed.
Lemma lem6877124 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6877125 (_91911 : int) : (term272 _91911) = (term299 _91911).
Proof. exact (MK_COMB (@lem6877123 _91911) (@lem6877124)). Qed.
Lemma lem6877126 (_91911 : int) : (term217 _91911) = (term299 _91911).
Proof. exact (TRANS (@lem6877079 _91911) (@lem6877125 _91911)). Qed.
Lemma lem6877127 (_91912 : int) : (term217 _91912) = (term272 _91912).
Proof. exact (@lem1988287 (real_of_int _91912) term214). Qed.
Lemma lem6877133 (_91912 : int) : (term273 _91912) = (term274 _91912).
Proof. exact (@lem1982792 (real_of_int _91912) term214). Qed.
Lemma lem6877135 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6877136 : term214 = term276.
Proof. exact (@lem6877135 (NUMERAL 0)). Qed.
Lemma lem6877138 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6877139 : term279 = term280.
Proof. exact (@lem6877138 term92). Qed.
Lemma lem6877140 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6877141 : term281 = term282.
Proof. exact (MK_COMB (@lem6877140) (@lem6877139)). Qed.
Lemma lem6877142 : term283 = term284.
Proof. exact (MK_COMB (@lem6877141) (@lem6877136)). Qed.
Lemma lem6877143 : term284 = term285.
Proof. exact (@lem1981613 term279 term214 term224 term224). Qed.
Lemma lem6877145 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6877146 : term288 = term289.
Proof. exact (@lem6877145 term92 term92). Qed.
Lemma lem6877147 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877148 : term291 = term92.
Proof. exact (EQ_MP (@lem6877147) (@lem940073)). Qed.
Lemma lem6877149 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877150 : term289 = term224.
Proof. exact (MK_COMB (@lem6877149) (@lem6877148)). Qed.
Lemma lem6877151 : term288 = term224.
Proof. exact (TRANS (@lem6877146) (@lem6877150)). Qed.
Lemma lem6877153 (x : nat) : (term292 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6877154 : term283 = term214.
Proof. exact (@lem6877153 term92). Qed.
Lemma lem6877155 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6877156 : term293 = term294.
Proof. exact (MK_COMB (@lem6877155) (@lem6877154)). Qed.
Lemma lem6877157 : term285 = term276.
Proof. exact (MK_COMB (@lem6877156) (@lem6877151)). Qed.
Lemma lem6877158 : term284 = term276.
Proof. exact (TRANS (@lem6877143) (@lem6877157)). Qed.
Lemma lem6877159 : term283 = term276.
Proof. exact (TRANS (@lem6877142) (@lem6877158)). Qed.
Lemma lem6877161 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6877162 : term276 = term214.
Proof. exact (@lem6877161 term214). Qed.
Lemma lem6877163 : term283 = term214.
Proof. exact (TRANS (@lem6877159) (@lem6877162)). Qed.
Lemma lem6877164 (_91912 : int) : (term225 _91912) = (term225 _91912).
Proof. exact (eq_refl (term225 _91912)). Qed.
Lemma lem6877165 (_91912 : int) : (term274 _91912) = (term296 _91912).
Proof. exact (MK_COMB (@lem6877164 _91912) (@lem6877163)). Qed.
Lemma lem6877166 (_91912 : int) : (term296 _91912) = (real_of_int _91912).
Proof. exact (@lem1982723 (real_of_int _91912)). Qed.
Lemma lem6877167 (_91912 : int) : (term274 _91912) = (real_of_int _91912).
Proof. exact (TRANS (@lem6877165 _91912) (@lem6877166 _91912)). Qed.
Lemma lem6877169 (_91912 : int) : (term273 _91912) = (real_of_int _91912).
Proof. exact (TRANS (@lem6877133 _91912) (@lem6877167 _91912)). Qed.
Lemma lem6877170 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6877171 (_91912 : int) : (term297 _91912) = (term298 _91912).
Proof. exact (MK_COMB (@lem6877170) (@lem6877169 _91912)). Qed.
Lemma lem6877172 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6877173 (_91912 : int) : (term272 _91912) = (term299 _91912).
Proof. exact (MK_COMB (@lem6877171 _91912) (@lem6877172)). Qed.
Lemma lem6877174 (_91912 : int) : (term217 _91912) = (term299 _91912).
Proof. exact (TRANS (@lem6877127 _91912) (@lem6877173 _91912)). Qed.
Lemma lem6877175 (_91912 : int) (_91911 : int) : ((real_of_int _91912) = (term226 _91911)) = ((term300 _91912 _91911) = term214).
Proof. exact (@lem1988293 (real_of_int _91912) (term226 _91911)). Qed.
Lemma lem6877187 (_91912 : int) (_91911 : int) : (term300 _91912 _91911) = (term301 _91912 _91911).
Proof. exact (@lem1982792 (real_of_int _91912) (term226 _91911)). Qed.
Lemma lem6877188 (_91911 : int) : (term302 _91911) = (term303 _91911).
Proof. exact (@lem1982781 (real_of_int _91911) term279 term224). Qed.
Lemma lem6877190 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6877191 : term224 = term304.
Proof. exact (@lem6877190 term92). Qed.
Lemma lem6877193 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6877194 : term279 = term280.
Proof. exact (@lem6877193 term92). Qed.
Lemma lem6877195 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6877196 : term281 = term282.
Proof. exact (MK_COMB (@lem6877195) (@lem6877194)). Qed.
Lemma lem6877197 : term305 = term306.
Proof. exact (MK_COMB (@lem6877196) (@lem6877191)). Qed.
Lemma lem6877198 : term306 = term307.
Proof. exact (@lem1981613 term279 term224 term224 term224). Qed.
Lemma lem6877200 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6877201 : term288 = term289.
Proof. exact (@lem6877200 term92 term92). Qed.
Lemma lem6877202 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877203 : term291 = term92.
Proof. exact (EQ_MP (@lem6877202) (@lem940073)). Qed.
Lemma lem6877204 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877205 : term289 = term224.
Proof. exact (MK_COMB (@lem6877204) (@lem6877203)). Qed.
Lemma lem6877206 : term288 = term224.
Proof. exact (TRANS (@lem6877201) (@lem6877205)). Qed.
Lemma lem6877208 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6877209 : term305 = term310.
Proof. exact (@lem6877208 term92 term92). Qed.
Lemma lem6877210 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877211 : term291 = term92.
Proof. exact (EQ_MP (@lem6877210) (@lem940073)). Qed.
Lemma lem6877212 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877213 : term289 = term224.
Proof. exact (MK_COMB (@lem6877212) (@lem6877211)). Qed.
Lemma lem6877214 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6877215 : term310 = term279.
Proof. exact (MK_COMB (@lem6877214) (@lem6877213)). Qed.
Lemma lem6877216 : term305 = term279.
Proof. exact (TRANS (@lem6877209) (@lem6877215)). Qed.
Lemma lem6877217 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6877218 : term311 = term312.
Proof. exact (MK_COMB (@lem6877217) (@lem6877216)). Qed.
Lemma lem6877219 : term307 = term280.
Proof. exact (MK_COMB (@lem6877218) (@lem6877206)). Qed.
Lemma lem6877220 : term306 = term280.
Proof. exact (TRANS (@lem6877198) (@lem6877219)). Qed.
Lemma lem6877221 : term305 = term280.
Proof. exact (TRANS (@lem6877197) (@lem6877220)). Qed.
Lemma lem6877223 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6877224 : term280 = term279.
Proof. exact (@lem6877223 term279). Qed.
Lemma lem6877225 : term305 = term279.
Proof. exact (TRANS (@lem6877221) (@lem6877224)). Qed.
Lemma lem6877228 (_91911 : int) : (term313 _91911) = (term313 _91911).
Proof. exact (eq_refl (term313 _91911)). Qed.
Lemma lem6877229 (_91911 : int) : (term303 _91911) = (term314 _91911).
Proof. exact (MK_COMB (@lem6877228 _91911) (@lem6877225)). Qed.
Lemma lem6877230 (_91911 : int) : (term302 _91911) = (term314 _91911).
Proof. exact (TRANS (@lem6877188 _91911) (@lem6877229 _91911)). Qed.
Lemma lem6877231 (_91912 : int) : (term225 _91912) = (term225 _91912).
Proof. exact (eq_refl (term225 _91912)). Qed.
Lemma lem6877232 (_91912 : int) (_91911 : int) : (term301 _91912 _91911) = (term315 _91912 _91911).
Proof. exact (MK_COMB (@lem6877231 _91912) (@lem6877230 _91911)). Qed.
Lemma lem6877237 (_91911 : int) (_91912 : int) : (term315 _91912 _91911) = (term316 _91911 _91912).
Proof. exact (@lem1982757 (term317 _91911) (real_of_int _91912) term279). Qed.
Lemma lem6877238 (_91911 : int) (_91912 : int) : (term301 _91912 _91911) = (term316 _91911 _91912).
Proof. exact (TRANS (@lem6877232 _91912 _91911) (@lem6877237 _91911 _91912)). Qed.
Lemma lem6877240 (_91911 : int) (_91912 : int) : (term300 _91912 _91911) = (term316 _91911 _91912).
Proof. exact (TRANS (@lem6877187 _91912 _91911) (@lem6877238 _91911 _91912)). Qed.
Lemma lem6877241 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6877242 (_91911 : int) (_91912 : int) : (term318 _91912 _91911) = (term319 _91911 _91912).
Proof. exact (MK_COMB (@lem6877241) (@lem6877240 _91911 _91912)). Qed.
Lemma lem6877243 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6877244 (_91911 : int) (_91912 : int) : ((term300 _91912 _91911) = term214) = ((term316 _91911 _91912) = term214).
Proof. exact (MK_COMB (@lem6877242 _91911 _91912) (@lem6877243)). Qed.
Lemma lem6877245 (_91911 : int) (_91912 : int) : ((real_of_int _91912) = (term226 _91911)) = ((term316 _91911 _91912) = term214).
Proof. exact (TRANS (@lem6877175 _91912 _91911) (@lem6877244 _91911 _91912)). Qed.
Lemma lem6877246 (_91912 : int) : (term233 _91912) = (term320 _91912).
Proof. exact (@lem1988287 term224 (term226 _91912)). Qed.
Lemma lem6877258 (_91912 : int) : (term321 _91912) = (term322 _91912).
Proof. exact (@lem1982792 term224 (term226 _91912)). Qed.
Lemma lem6877259 (_91912 : int) : (term302 _91912) = (term303 _91912).
Proof. exact (@lem1982781 (real_of_int _91912) term279 term224). Qed.
Lemma lem6877261 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6877262 : term224 = term304.
Proof. exact (@lem6877261 term92). Qed.
Lemma lem6877264 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6877265 : term279 = term280.
Proof. exact (@lem6877264 term92). Qed.
Lemma lem6877266 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6877267 : term281 = term282.
Proof. exact (MK_COMB (@lem6877266) (@lem6877265)). Qed.
Lemma lem6877268 : term305 = term306.
Proof. exact (MK_COMB (@lem6877267) (@lem6877262)). Qed.
Lemma lem6877269 : term306 = term307.
Proof. exact (@lem1981613 term279 term224 term224 term224). Qed.
Lemma lem6877271 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6877272 : term288 = term289.
Proof. exact (@lem6877271 term92 term92). Qed.
Lemma lem6877273 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877274 : term291 = term92.
Proof. exact (EQ_MP (@lem6877273) (@lem940073)). Qed.
Lemma lem6877275 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877276 : term289 = term224.
Proof. exact (MK_COMB (@lem6877275) (@lem6877274)). Qed.
Lemma lem6877277 : term288 = term224.
Proof. exact (TRANS (@lem6877272) (@lem6877276)). Qed.
Lemma lem6877279 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6877280 : term305 = term310.
Proof. exact (@lem6877279 term92 term92). Qed.
Lemma lem6877281 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877282 : term291 = term92.
Proof. exact (EQ_MP (@lem6877281) (@lem940073)). Qed.
Lemma lem6877283 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877284 : term289 = term224.
Proof. exact (MK_COMB (@lem6877283) (@lem6877282)). Qed.
Lemma lem6877285 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6877286 : term310 = term279.
Proof. exact (MK_COMB (@lem6877285) (@lem6877284)). Qed.
Lemma lem6877287 : term305 = term279.
Proof. exact (TRANS (@lem6877280) (@lem6877286)). Qed.
Lemma lem6877288 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6877289 : term311 = term312.
Proof. exact (MK_COMB (@lem6877288) (@lem6877287)). Qed.
Lemma lem6877290 : term307 = term280.
Proof. exact (MK_COMB (@lem6877289) (@lem6877277)). Qed.
Lemma lem6877291 : term306 = term280.
Proof. exact (TRANS (@lem6877269) (@lem6877290)). Qed.
Lemma lem6877292 : term305 = term280.
Proof. exact (TRANS (@lem6877268) (@lem6877291)). Qed.
Lemma lem6877294 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6877295 : term280 = term279.
Proof. exact (@lem6877294 term279). Qed.
Lemma lem6877296 : term305 = term279.
Proof. exact (TRANS (@lem6877292) (@lem6877295)). Qed.
Lemma lem6877299 (_91912 : int) : (term313 _91912) = (term313 _91912).
Proof. exact (eq_refl (term313 _91912)). Qed.
Lemma lem6877300 (_91912 : int) : (term303 _91912) = (term314 _91912).
Proof. exact (MK_COMB (@lem6877299 _91912) (@lem6877296)). Qed.
Lemma lem6877301 (_91912 : int) : (term302 _91912) = (term314 _91912).
Proof. exact (TRANS (@lem6877259 _91912) (@lem6877300 _91912)). Qed.
Lemma lem6877302 : term323 = term323.
Proof. exact (eq_refl term323). Qed.
Lemma lem6877303 (_91912 : int) : (term322 _91912) = (term324 _91912).
Proof. exact (MK_COMB (@lem6877302) (@lem6877301 _91912)). Qed.
Lemma lem6877304 (_91912 : int) : (term324 _91912) = (term325 _91912).
Proof. exact (@lem1982757 (term317 _91912) term224 term279). Qed.
Lemma lem6877306 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6877307 : term279 = term280.
Proof. exact (@lem6877306 term92). Qed.
Lemma lem6877309 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6877310 : term224 = term304.
Proof. exact (@lem6877309 term92). Qed.
Lemma lem6877311 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6877312 : term323 = term326.
Proof. exact (MK_COMB (@lem6877311) (@lem6877310)). Qed.
Lemma lem6877313 : term327 = term328.
Proof. exact (MK_COMB (@lem6877312) (@lem6877307)). Qed.
Lemma lem6877314 : term329.
Proof. exact (@lem1981473 term224 term224 term279 term224 term214 term224). Qed.
Lemma lem6877316 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6877317 : term331 = term332.
Proof. exact (@lem6877316 (NUMERAL 0) term92). Qed.
Lemma lem6877318 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6877319 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6877320 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6877319 h1) (fun h1 : term332 = True => @lem6877318)). Qed.
Lemma lem6877321 : term332 = True.
Proof. exact (EQ_MP (@lem6877320) (@lem6877318)). Qed.
Lemma lem6877322 : term331 = True.
Proof. exact (TRANS (@lem6877317) (@lem6877321)). Qed.
Lemma lem6877323 : True = term331.
Proof. exact (SYM (@lem6877322)). Qed.
Lemma lem6877324 : term331.
Proof. exact (EQ_MP (@lem6877323) (@lem0)). Qed.
Lemma lem6877325 : term334.
Proof. exact (@lem6877314 (@lem6877324)). Qed.
Lemma lem6877327 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6877328 : term331 = term332.
Proof. exact (@lem6877327 (NUMERAL 0) term92). Qed.
Lemma lem6877329 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6877330 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6877331 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6877330 h1) (fun h1 : term332 = True => @lem6877329)). Qed.
Lemma lem6877332 : term332 = True.
Proof. exact (EQ_MP (@lem6877331) (@lem6877329)). Qed.
Lemma lem6877333 : term331 = True.
Proof. exact (TRANS (@lem6877328) (@lem6877332)). Qed.
Lemma lem6877334 : True = term331.
Proof. exact (SYM (@lem6877333)). Qed.
Lemma lem6877335 : term331.
Proof. exact (EQ_MP (@lem6877334) (@lem0)). Qed.
Lemma lem6877336 : term335.
Proof. exact (@lem6877325 (@lem6877335)). Qed.
Lemma lem6877338 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6877339 : term331 = term332.
Proof. exact (@lem6877338 (NUMERAL 0) term92). Qed.
Lemma lem6877340 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6877341 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6877342 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6877341 h1) (fun h1 : term332 = True => @lem6877340)). Qed.
Lemma lem6877343 : term332 = True.
Proof. exact (EQ_MP (@lem6877342) (@lem6877340)). Qed.
Lemma lem6877344 : term331 = True.
Proof. exact (TRANS (@lem6877339) (@lem6877343)). Qed.
Lemma lem6877345 : True = term331.
Proof. exact (SYM (@lem6877344)). Qed.
Lemma lem6877346 : term331.
Proof. exact (EQ_MP (@lem6877345) (@lem0)). Qed.
Lemma lem6877347 : term336.
Proof. exact (@lem6877336 (@lem6877346)). Qed.
Lemma lem6877349 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6877350 : term305 = term310.
Proof. exact (@lem6877349 term92 term92). Qed.
Lemma lem6877351 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877352 : term291 = term92.
Proof. exact (EQ_MP (@lem6877351) (@lem940073)). Qed.
Lemma lem6877353 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877354 : term289 = term224.
Proof. exact (MK_COMB (@lem6877353) (@lem6877352)). Qed.
Lemma lem6877355 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6877356 : term310 = term279.
Proof. exact (MK_COMB (@lem6877355) (@lem6877354)). Qed.
Lemma lem6877357 : term305 = term279.
Proof. exact (TRANS (@lem6877350) (@lem6877356)). Qed.
Lemma lem6877359 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6877360 : term288 = term289.
Proof. exact (@lem6877359 term92 term92). Qed.
Lemma lem6877361 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877362 : term291 = term92.
Proof. exact (EQ_MP (@lem6877361) (@lem940073)). Qed.
Lemma lem6877363 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877364 : term289 = term224.
Proof. exact (MK_COMB (@lem6877363) (@lem6877362)). Qed.
Lemma lem6877365 : term288 = term224.
Proof. exact (TRANS (@lem6877360) (@lem6877364)). Qed.
Lemma lem6877366 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6877367 : term337 = term323.
Proof. exact (MK_COMB (@lem6877366) (@lem6877365)). Qed.
Lemma lem6877368 : term338 = term327.
Proof. exact (MK_COMB (@lem6877367) (@lem6877357)). Qed.
Lemma lem6877370 (m : nat) : (term339 m) = term214.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem6877371 : term327 = term214.
Proof. exact (@lem6877370 term92). Qed.
Lemma lem6877372 : term338 = term214.
Proof. exact (TRANS (@lem6877368) (@lem6877371)). Qed.
Lemma lem6877373 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6877374 : term340 = term341.
Proof. exact (MK_COMB (@lem6877373) (@lem6877372)). Qed.
Lemma lem6877375 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6877376 : term342 = term343.
Proof. exact (MK_COMB (@lem6877374) (@lem6877375)). Qed.
Lemma lem6877378 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6877379 : term343 = term214.
Proof. exact (@lem6877378 term92). Qed.
Lemma lem6877380 : term342 = term214.
Proof. exact (TRANS (@lem6877376) (@lem6877379)). Qed.
Lemma lem6877382 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6877383 : term288 = term289.
Proof. exact (@lem6877382 term92 term92). Qed.
Lemma lem6877384 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877385 : term291 = term92.
Proof. exact (EQ_MP (@lem6877384) (@lem940073)). Qed.
Lemma lem6877386 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877387 : term289 = term224.
Proof. exact (MK_COMB (@lem6877386) (@lem6877385)). Qed.
Lemma lem6877388 : term288 = term224.
Proof. exact (TRANS (@lem6877383) (@lem6877387)). Qed.
Lemma lem6877389 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6877390 : term345 = term343.
Proof. exact (MK_COMB (@lem6877389) (@lem6877388)). Qed.
Lemma lem6877392 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6877393 : term343 = term214.
Proof. exact (@lem6877392 term92). Qed.
Lemma lem6877394 : term345 = term214.
Proof. exact (TRANS (@lem6877390) (@lem6877393)). Qed.
Lemma lem6877395 : term214 = term345.
Proof. exact (SYM (@lem6877394)). Qed.
Lemma lem6877396 : term342 = term345.
Proof. exact (TRANS (@lem6877380) (@lem6877395)). Qed.
Lemma lem6877397 : term328 = term276.
Proof. exact (@lem6877347 (@lem6877396)). Qed.
Lemma lem6877398 : term327 = term276.
Proof. exact (TRANS (@lem6877313) (@lem6877397)). Qed.
Lemma lem6877400 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6877401 : term276 = term214.
Proof. exact (@lem6877400 term214). Qed.
Lemma lem6877402 : term327 = term214.
Proof. exact (TRANS (@lem6877398) (@lem6877401)). Qed.
Lemma lem6877403 (_91912 : int) : (term313 _91912) = (term313 _91912).
Proof. exact (eq_refl (term313 _91912)). Qed.
Lemma lem6877404 (_91912 : int) : (term325 _91912) = (term346 _91912).
Proof. exact (MK_COMB (@lem6877403 _91912) (@lem6877402)). Qed.
Lemma lem6877405 (_91912 : int) : (term324 _91912) = (term346 _91912).
Proof. exact (TRANS (@lem6877304 _91912) (@lem6877404 _91912)). Qed.
Lemma lem6877406 (_91912 : int) : (term346 _91912) = (term317 _91912).
Proof. exact (@lem1982723 (term317 _91912)). Qed.
Lemma lem6877407 (_91912 : int) : (term324 _91912) = (term317 _91912).
Proof. exact (TRANS (@lem6877405 _91912) (@lem6877406 _91912)). Qed.
Lemma lem6877408 (_91912 : int) : (term322 _91912) = (term317 _91912).
Proof. exact (TRANS (@lem6877303 _91912) (@lem6877407 _91912)). Qed.
Lemma lem6877410 (_91912 : int) : (term321 _91912) = (term317 _91912).
Proof. exact (TRANS (@lem6877258 _91912) (@lem6877408 _91912)). Qed.
Lemma lem6877411 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6877412 (_91912 : int) : (term347 _91912) = (term348 _91912).
Proof. exact (MK_COMB (@lem6877411) (@lem6877410 _91912)). Qed.
Lemma lem6877413 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6877414 (_91912 : int) : (term320 _91912) = (term349 _91912).
Proof. exact (MK_COMB (@lem6877412 _91912) (@lem6877413)). Qed.
Lemma lem6877415 (_91912 : int) : (term233 _91912) = (term349 _91912).
Proof. exact (TRANS (@lem6877246 _91912) (@lem6877414 _91912)). Qed.
Lemma lem6877416 (_91911 : int) : ((real_of_int _91911) = term214) = ((term273 _91911) = term214).
Proof. exact (@lem1988293 (real_of_int _91911) term214). Qed.
Lemma lem6877422 (_91911 : int) : (term273 _91911) = (term274 _91911).
Proof. exact (@lem1982792 (real_of_int _91911) term214). Qed.
Lemma lem6877424 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6877425 : term214 = term276.
Proof. exact (@lem6877424 (NUMERAL 0)). Qed.
Lemma lem6877427 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6877428 : term279 = term280.
Proof. exact (@lem6877427 term92). Qed.
Lemma lem6877429 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6877430 : term281 = term282.
Proof. exact (MK_COMB (@lem6877429) (@lem6877428)). Qed.
Lemma lem6877431 : term283 = term284.
Proof. exact (MK_COMB (@lem6877430) (@lem6877425)). Qed.
Lemma lem6877432 : term284 = term285.
Proof. exact (@lem1981613 term279 term214 term224 term224). Qed.
Lemma lem6877434 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6877435 : term288 = term289.
Proof. exact (@lem6877434 term92 term92). Qed.
Lemma lem6877436 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877437 : term291 = term92.
Proof. exact (EQ_MP (@lem6877436) (@lem940073)). Qed.
Lemma lem6877438 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877439 : term289 = term224.
Proof. exact (MK_COMB (@lem6877438) (@lem6877437)). Qed.
Lemma lem6877440 : term288 = term224.
Proof. exact (TRANS (@lem6877435) (@lem6877439)). Qed.
Lemma lem6877442 (x : nat) : (term292 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6877443 : term283 = term214.
Proof. exact (@lem6877442 term92). Qed.
Lemma lem6877444 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6877445 : term293 = term294.
Proof. exact (MK_COMB (@lem6877444) (@lem6877443)). Qed.
Lemma lem6877446 : term285 = term276.
Proof. exact (MK_COMB (@lem6877445) (@lem6877440)). Qed.
Lemma lem6877447 : term284 = term276.
Proof. exact (TRANS (@lem6877432) (@lem6877446)). Qed.
Lemma lem6877448 : term283 = term276.
Proof. exact (TRANS (@lem6877431) (@lem6877447)). Qed.
Lemma lem6877450 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6877451 : term276 = term214.
Proof. exact (@lem6877450 term214). Qed.
Lemma lem6877452 : term283 = term214.
Proof. exact (TRANS (@lem6877448) (@lem6877451)). Qed.
Lemma lem6877453 (_91911 : int) : (term225 _91911) = (term225 _91911).
Proof. exact (eq_refl (term225 _91911)). Qed.
Lemma lem6877454 (_91911 : int) : (term274 _91911) = (term296 _91911).
Proof. exact (MK_COMB (@lem6877453 _91911) (@lem6877452)). Qed.
Lemma lem6877455 (_91911 : int) : (term296 _91911) = (real_of_int _91911).
Proof. exact (@lem1982723 (real_of_int _91911)). Qed.
Lemma lem6877456 (_91911 : int) : (term274 _91911) = (real_of_int _91911).
Proof. exact (TRANS (@lem6877454 _91911) (@lem6877455 _91911)). Qed.
Lemma lem6877458 (_91911 : int) : (term273 _91911) = (real_of_int _91911).
Proof. exact (TRANS (@lem6877422 _91911) (@lem6877456 _91911)). Qed.
Lemma lem6877459 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6877460 (_91911 : int) : (term350 _91911) = (term227 _91911).
Proof. exact (MK_COMB (@lem6877459) (@lem6877458 _91911)). Qed.
Lemma lem6877461 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6877462 (_91911 : int) : ((term273 _91911) = term214) = ((real_of_int _91911) = term214).
Proof. exact (MK_COMB (@lem6877460 _91911) (@lem6877461)). Qed.
Lemma lem6877463 (_91911 : int) : ((real_of_int _91911) = term214) = ((real_of_int _91911) = term214).
Proof. exact (TRANS (@lem6877416 _91911) (@lem6877462 _91911)). Qed.
Lemma lem6877464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6877465 (_91912 : int) : (term234 _91912) = (term351 _91912).
Proof. exact (MK_COMB (@lem6877464) (@lem6877415 _91912)). Qed.
Lemma lem6877466 (_91912 : int) (_91911 : int) : (term235 _91912 _91911) = (term352 _91912 _91911).
Proof. exact (MK_COMB (@lem6877465 _91912) (@lem6877463 _91911)). Qed.
Lemma lem6877467 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877468 (_91911 : int) (_91912 : int) : (term236 _91912 _91911) = (term353 _91911 _91912).
Proof. exact (MK_COMB (@lem6877467) (@lem6877245 _91911 _91912)). Qed.
Lemma lem6877469 (_91912 : int) (_91911 : int) : (term237 _91912 _91911) = (term354 _91912 _91911).
Proof. exact (MK_COMB (@lem6877468 _91911 _91912) (@lem6877466 _91912 _91911)). Qed.
Lemma lem6877470 (_91911 : int) (_91912 : int) : (term210 _91912 _91911) = (term355 _91911 _91912).
Proof. exact (@lem1988287 (real_of_int _91911) (real_of_int _91912)). Qed.
Lemma lem6877483 (_91911 : int) (_91912 : int) : (term356 _91911 _91912) = (term357 _91911 _91912).
Proof. exact (@lem1982792 (real_of_int _91911) (real_of_int _91912)). Qed.
Lemma lem6877484 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6877485 (_91911 : int) (_91912 : int) : (term358 _91911 _91912) = (term359 _91911 _91912).
Proof. exact (MK_COMB (@lem6877484) (@lem6877483 _91911 _91912)). Qed.
Lemma lem6877486 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6877487 (_91911 : int) (_91912 : int) : (term355 _91911 _91912) = (term360 _91911 _91912).
Proof. exact (MK_COMB (@lem6877485 _91911 _91912) (@lem6877486)). Qed.
Lemma lem6877488 (_91911 : int) (_91912 : int) : (term210 _91912 _91911) = (term360 _91911 _91912).
Proof. exact (TRANS (@lem6877470 _91911 _91912) (@lem6877487 _91911 _91912)). Qed.
Lemma lem6877489 (_91912 : int) : ((real_of_int _91912) = term214) = ((term273 _91912) = term214).
Proof. exact (@lem1988293 (real_of_int _91912) term214). Qed.
Lemma lem6877495 (_91912 : int) : (term273 _91912) = (term274 _91912).
Proof. exact (@lem1982792 (real_of_int _91912) term214). Qed.
Lemma lem6877497 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6877498 : term214 = term276.
Proof. exact (@lem6877497 (NUMERAL 0)). Qed.
Lemma lem6877500 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6877501 : term279 = term280.
Proof. exact (@lem6877500 term92). Qed.
Lemma lem6877502 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6877503 : term281 = term282.
Proof. exact (MK_COMB (@lem6877502) (@lem6877501)). Qed.
Lemma lem6877504 : term283 = term284.
Proof. exact (MK_COMB (@lem6877503) (@lem6877498)). Qed.
Lemma lem6877505 : term284 = term285.
Proof. exact (@lem1981613 term279 term214 term224 term224). Qed.
Lemma lem6877507 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6877508 : term288 = term289.
Proof. exact (@lem6877507 term92 term92). Qed.
Lemma lem6877509 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877510 : term291 = term92.
Proof. exact (EQ_MP (@lem6877509) (@lem940073)). Qed.
Lemma lem6877511 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877512 : term289 = term224.
Proof. exact (MK_COMB (@lem6877511) (@lem6877510)). Qed.
Lemma lem6877513 : term288 = term224.
Proof. exact (TRANS (@lem6877508) (@lem6877512)). Qed.
Lemma lem6877515 (x : nat) : (term292 x) = term214.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6877516 : term283 = term214.
Proof. exact (@lem6877515 term92). Qed.
Lemma lem6877517 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6877518 : term293 = term294.
Proof. exact (MK_COMB (@lem6877517) (@lem6877516)). Qed.
Lemma lem6877519 : term285 = term276.
Proof. exact (MK_COMB (@lem6877518) (@lem6877513)). Qed.
Lemma lem6877520 : term284 = term276.
Proof. exact (TRANS (@lem6877505) (@lem6877519)). Qed.
Lemma lem6877521 : term283 = term276.
Proof. exact (TRANS (@lem6877504) (@lem6877520)). Qed.
Lemma lem6877523 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6877524 : term276 = term214.
Proof. exact (@lem6877523 term214). Qed.
Lemma lem6877525 : term283 = term214.
Proof. exact (TRANS (@lem6877521) (@lem6877524)). Qed.
Lemma lem6877526 (_91912 : int) : (term225 _91912) = (term225 _91912).
Proof. exact (eq_refl (term225 _91912)). Qed.
Lemma lem6877527 (_91912 : int) : (term274 _91912) = (term296 _91912).
Proof. exact (MK_COMB (@lem6877526 _91912) (@lem6877525)). Qed.
Lemma lem6877528 (_91912 : int) : (term296 _91912) = (real_of_int _91912).
Proof. exact (@lem1982723 (real_of_int _91912)). Qed.
Lemma lem6877529 (_91912 : int) : (term274 _91912) = (real_of_int _91912).
Proof. exact (TRANS (@lem6877527 _91912) (@lem6877528 _91912)). Qed.
Lemma lem6877531 (_91912 : int) : (term273 _91912) = (real_of_int _91912).
Proof. exact (TRANS (@lem6877495 _91912) (@lem6877529 _91912)). Qed.
Lemma lem6877532 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6877533 (_91912 : int) : (term350 _91912) = (term227 _91912).
Proof. exact (MK_COMB (@lem6877532) (@lem6877531 _91912)). Qed.
Lemma lem6877534 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6877535 (_91912 : int) : ((term273 _91912) = term214) = ((real_of_int _91912) = term214).
Proof. exact (MK_COMB (@lem6877533 _91912) (@lem6877534)). Qed.
Lemma lem6877536 (_91912 : int) : ((real_of_int _91912) = term214) = ((real_of_int _91912) = term214).
Proof. exact (TRANS (@lem6877489 _91912) (@lem6877535 _91912)). Qed.
Lemma lem6877537 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877538 (_91911 : int) (_91912 : int) : (term238 _91912 _91911) = (term361 _91911 _91912).
Proof. exact (MK_COMB (@lem6877537) (@lem6877488 _91911 _91912)). Qed.
Lemma lem6877539 (_91911 : int) (_91912 : int) : (term239 _91911 _91912) = (term362 _91911 _91912).
Proof. exact (MK_COMB (@lem6877538 _91911 _91912) (@lem6877536 _91912)). Qed.
Lemma lem6877540 (_91912 : int) (_91911 : int) : (term241 _91911 _91912) = (term363 _91912 _91911).
Proof. exact (@lem1988287 (real_of_int _91912) (term226 _91911)). Qed.
Lemma lem6877552 (_91912 : int) (_91911 : int) : (term300 _91912 _91911) = (term301 _91912 _91911).
Proof. exact (@lem1982792 (real_of_int _91912) (term226 _91911)). Qed.
Lemma lem6877553 (_91911 : int) : (term302 _91911) = (term303 _91911).
Proof. exact (@lem1982781 (real_of_int _91911) term279 term224). Qed.
Lemma lem6877555 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6877556 : term224 = term304.
Proof. exact (@lem6877555 term92). Qed.
Lemma lem6877558 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6877559 : term279 = term280.
Proof. exact (@lem6877558 term92). Qed.
Lemma lem6877560 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6877561 : term281 = term282.
Proof. exact (MK_COMB (@lem6877560) (@lem6877559)). Qed.
Lemma lem6877562 : term305 = term306.
Proof. exact (MK_COMB (@lem6877561) (@lem6877556)). Qed.
Lemma lem6877563 : term306 = term307.
Proof. exact (@lem1981613 term279 term224 term224 term224). Qed.
Lemma lem6877565 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6877566 : term288 = term289.
Proof. exact (@lem6877565 term92 term92). Qed.
Lemma lem6877567 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877568 : term291 = term92.
Proof. exact (EQ_MP (@lem6877567) (@lem940073)). Qed.
Lemma lem6877569 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877570 : term289 = term224.
Proof. exact (MK_COMB (@lem6877569) (@lem6877568)). Qed.
Lemma lem6877571 : term288 = term224.
Proof. exact (TRANS (@lem6877566) (@lem6877570)). Qed.
Lemma lem6877573 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6877574 : term305 = term310.
Proof. exact (@lem6877573 term92 term92). Qed.
Lemma lem6877575 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877576 : term291 = term92.
Proof. exact (EQ_MP (@lem6877575) (@lem940073)). Qed.
Lemma lem6877577 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877578 : term289 = term224.
Proof. exact (MK_COMB (@lem6877577) (@lem6877576)). Qed.
Lemma lem6877579 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6877580 : term310 = term279.
Proof. exact (MK_COMB (@lem6877579) (@lem6877578)). Qed.
Lemma lem6877581 : term305 = term279.
Proof. exact (TRANS (@lem6877574) (@lem6877580)). Qed.
Lemma lem6877582 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6877583 : term311 = term312.
Proof. exact (MK_COMB (@lem6877582) (@lem6877581)). Qed.
Lemma lem6877584 : term307 = term280.
Proof. exact (MK_COMB (@lem6877583) (@lem6877571)). Qed.
Lemma lem6877585 : term306 = term280.
Proof. exact (TRANS (@lem6877563) (@lem6877584)). Qed.
Lemma lem6877586 : term305 = term280.
Proof. exact (TRANS (@lem6877562) (@lem6877585)). Qed.
Lemma lem6877588 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6877589 : term280 = term279.
Proof. exact (@lem6877588 term279). Qed.
Lemma lem6877590 : term305 = term279.
Proof. exact (TRANS (@lem6877586) (@lem6877589)). Qed.
Lemma lem6877593 (_91911 : int) : (term313 _91911) = (term313 _91911).
Proof. exact (eq_refl (term313 _91911)). Qed.
Lemma lem6877594 (_91911 : int) : (term303 _91911) = (term314 _91911).
Proof. exact (MK_COMB (@lem6877593 _91911) (@lem6877590)). Qed.
Lemma lem6877595 (_91911 : int) : (term302 _91911) = (term314 _91911).
Proof. exact (TRANS (@lem6877553 _91911) (@lem6877594 _91911)). Qed.
Lemma lem6877596 (_91912 : int) : (term225 _91912) = (term225 _91912).
Proof. exact (eq_refl (term225 _91912)). Qed.
Lemma lem6877597 (_91912 : int) (_91911 : int) : (term301 _91912 _91911) = (term315 _91912 _91911).
Proof. exact (MK_COMB (@lem6877596 _91912) (@lem6877595 _91911)). Qed.
Lemma lem6877602 (_91911 : int) (_91912 : int) : (term315 _91912 _91911) = (term316 _91911 _91912).
Proof. exact (@lem1982757 (term317 _91911) (real_of_int _91912) term279). Qed.
Lemma lem6877603 (_91911 : int) (_91912 : int) : (term301 _91912 _91911) = (term316 _91911 _91912).
Proof. exact (TRANS (@lem6877597 _91912 _91911) (@lem6877602 _91911 _91912)). Qed.
Lemma lem6877605 (_91911 : int) (_91912 : int) : (term300 _91912 _91911) = (term316 _91911 _91912).
Proof. exact (TRANS (@lem6877552 _91912 _91911) (@lem6877603 _91911 _91912)). Qed.
Lemma lem6877606 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6877607 (_91911 : int) (_91912 : int) : (term364 _91912 _91911) = (term365 _91911 _91912).
Proof. exact (MK_COMB (@lem6877606) (@lem6877605 _91911 _91912)). Qed.
Lemma lem6877608 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6877609 (_91911 : int) (_91912 : int) : (term363 _91912 _91911) = (term366 _91911 _91912).
Proof. exact (MK_COMB (@lem6877607 _91911 _91912) (@lem6877608)). Qed.
Lemma lem6877610 (_91911 : int) (_91912 : int) : (term241 _91911 _91912) = (term366 _91911 _91912).
Proof. exact (TRANS (@lem6877540 _91912 _91911) (@lem6877609 _91911 _91912)). Qed.
Lemma lem6877611 (_91912 : int) : (term247 _91912) = (term367 _91912).
Proof. exact (@lem1988287 term214 (term226 _91912)). Qed.
Lemma lem6877623 (_91912 : int) : (term368 _91912) = (term369 _91912).
Proof. exact (@lem1982792 term214 (term226 _91912)). Qed.
Lemma lem6877624 (_91912 : int) : (term302 _91912) = (term303 _91912).
Proof. exact (@lem1982781 (real_of_int _91912) term279 term224). Qed.
Lemma lem6877626 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6877627 : term224 = term304.
Proof. exact (@lem6877626 term92). Qed.
Lemma lem6877629 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6877630 : term279 = term280.
Proof. exact (@lem6877629 term92). Qed.
Lemma lem6877631 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6877632 : term281 = term282.
Proof. exact (MK_COMB (@lem6877631) (@lem6877630)). Qed.
Lemma lem6877633 : term305 = term306.
Proof. exact (MK_COMB (@lem6877632) (@lem6877627)). Qed.
Lemma lem6877634 : term306 = term307.
Proof. exact (@lem1981613 term279 term224 term224 term224). Qed.
Lemma lem6877636 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6877637 : term288 = term289.
Proof. exact (@lem6877636 term92 term92). Qed.
Lemma lem6877638 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877639 : term291 = term92.
Proof. exact (EQ_MP (@lem6877638) (@lem940073)). Qed.
Lemma lem6877640 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877641 : term289 = term224.
Proof. exact (MK_COMB (@lem6877640) (@lem6877639)). Qed.
Lemma lem6877642 : term288 = term224.
Proof. exact (TRANS (@lem6877637) (@lem6877641)). Qed.
Lemma lem6877644 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6877645 : term305 = term310.
Proof. exact (@lem6877644 term92 term92). Qed.
Lemma lem6877646 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877647 : term291 = term92.
Proof. exact (EQ_MP (@lem6877646) (@lem940073)). Qed.
Lemma lem6877648 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877649 : term289 = term224.
Proof. exact (MK_COMB (@lem6877648) (@lem6877647)). Qed.
Lemma lem6877650 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6877651 : term310 = term279.
Proof. exact (MK_COMB (@lem6877650) (@lem6877649)). Qed.
Lemma lem6877652 : term305 = term279.
Proof. exact (TRANS (@lem6877645) (@lem6877651)). Qed.
Lemma lem6877653 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6877654 : term311 = term312.
Proof. exact (MK_COMB (@lem6877653) (@lem6877652)). Qed.
Lemma lem6877655 : term307 = term280.
Proof. exact (MK_COMB (@lem6877654) (@lem6877642)). Qed.
Lemma lem6877656 : term306 = term280.
Proof. exact (TRANS (@lem6877634) (@lem6877655)). Qed.
Lemma lem6877657 : term305 = term280.
Proof. exact (TRANS (@lem6877633) (@lem6877656)). Qed.
Lemma lem6877659 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6877660 : term280 = term279.
Proof. exact (@lem6877659 term279). Qed.
Lemma lem6877661 : term305 = term279.
Proof. exact (TRANS (@lem6877657) (@lem6877660)). Qed.
Lemma lem6877664 (_91912 : int) : (term313 _91912) = (term313 _91912).
Proof. exact (eq_refl (term313 _91912)). Qed.
Lemma lem6877665 (_91912 : int) : (term303 _91912) = (term314 _91912).
Proof. exact (MK_COMB (@lem6877664 _91912) (@lem6877661)). Qed.
Lemma lem6877666 (_91912 : int) : (term302 _91912) = (term314 _91912).
Proof. exact (TRANS (@lem6877624 _91912) (@lem6877665 _91912)). Qed.
Lemma lem6877667 : term256 = term256.
Proof. exact (eq_refl term256). Qed.
Lemma lem6877668 (_91912 : int) : (term369 _91912) = (term370 _91912).
Proof. exact (MK_COMB (@lem6877667) (@lem6877666 _91912)). Qed.
Lemma lem6877669 (_91912 : int) : (term370 _91912) = (term314 _91912).
Proof. exact (@lem1982721 (term314 _91912)). Qed.
Lemma lem6877670 (_91912 : int) : (term369 _91912) = (term314 _91912).
Proof. exact (TRANS (@lem6877668 _91912) (@lem6877669 _91912)). Qed.
Lemma lem6877672 (_91912 : int) : (term368 _91912) = (term314 _91912).
Proof. exact (TRANS (@lem6877623 _91912) (@lem6877670 _91912)). Qed.
Lemma lem6877673 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6877674 (_91912 : int) : (term371 _91912) = (term372 _91912).
Proof. exact (MK_COMB (@lem6877673) (@lem6877672 _91912)). Qed.
Lemma lem6877675 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6877676 (_91912 : int) : (term367 _91912) = (term373 _91912).
Proof. exact (MK_COMB (@lem6877674 _91912) (@lem6877675)). Qed.
Lemma lem6877677 (_91912 : int) : (term247 _91912) = (term373 _91912).
Proof. exact (TRANS (@lem6877611 _91912) (@lem6877676 _91912)). Qed.
Lemma lem6877678 (_91912 : int) : (term260 _91912) = (term374 _91912).
Proof. exact (@lem1988287 (real_of_int _91912) term257). Qed.
Lemma lem6877685 : term257 = term224.
Proof. exact (@lem1982721 term224). Qed.
Lemma lem6877688 (_91912 : int) : (term375 _91912) = (term375 _91912).
Proof. exact (eq_refl (term375 _91912)). Qed.
Lemma lem6877689 (_91912 : int) : (term376 _91912) = (term377 _91912).
Proof. exact (MK_COMB (@lem6877688 _91912) (@lem6877685)). Qed.
Lemma lem6877690 (_91912 : int) : (term377 _91912) = (term378 _91912).
Proof. exact (@lem1982792 (real_of_int _91912) term224). Qed.
Lemma lem6877692 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6877693 : term224 = term304.
Proof. exact (@lem6877692 term92). Qed.
Lemma lem6877695 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6877696 : term279 = term280.
Proof. exact (@lem6877695 term92). Qed.
Lemma lem6877697 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6877698 : term281 = term282.
Proof. exact (MK_COMB (@lem6877697) (@lem6877696)). Qed.
Lemma lem6877699 : term305 = term306.
Proof. exact (MK_COMB (@lem6877698) (@lem6877693)). Qed.
Lemma lem6877700 : term306 = term307.
Proof. exact (@lem1981613 term279 term224 term224 term224). Qed.
Lemma lem6877702 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6877703 : term288 = term289.
Proof. exact (@lem6877702 term92 term92). Qed.
Lemma lem6877704 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877705 : term291 = term92.
Proof. exact (EQ_MP (@lem6877704) (@lem940073)). Qed.
Lemma lem6877706 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877707 : term289 = term224.
Proof. exact (MK_COMB (@lem6877706) (@lem6877705)). Qed.
Lemma lem6877708 : term288 = term224.
Proof. exact (TRANS (@lem6877703) (@lem6877707)). Qed.
Lemma lem6877710 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6877711 : term305 = term310.
Proof. exact (@lem6877710 term92 term92). Qed.
Lemma lem6877712 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6877713 : term291 = term92.
Proof. exact (EQ_MP (@lem6877712) (@lem940073)). Qed.
Lemma lem6877714 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6877715 : term289 = term224.
Proof. exact (MK_COMB (@lem6877714) (@lem6877713)). Qed.
Lemma lem6877716 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6877717 : term310 = term279.
Proof. exact (MK_COMB (@lem6877716) (@lem6877715)). Qed.
Lemma lem6877718 : term305 = term279.
Proof. exact (TRANS (@lem6877711) (@lem6877717)). Qed.
Lemma lem6877719 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6877720 : term311 = term312.
Proof. exact (MK_COMB (@lem6877719) (@lem6877718)). Qed.
Lemma lem6877721 : term307 = term280.
Proof. exact (MK_COMB (@lem6877720) (@lem6877708)). Qed.
Lemma lem6877722 : term306 = term280.
Proof. exact (TRANS (@lem6877700) (@lem6877721)). Qed.
Lemma lem6877723 : term305 = term280.
Proof. exact (TRANS (@lem6877699) (@lem6877722)). Qed.
Lemma lem6877725 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6877726 : term280 = term279.
Proof. exact (@lem6877725 term279). Qed.
Lemma lem6877727 : term305 = term279.
Proof. exact (TRANS (@lem6877723) (@lem6877726)). Qed.
Lemma lem6877728 (_91912 : int) : (term225 _91912) = (term225 _91912).
Proof. exact (eq_refl (term225 _91912)). Qed.
Lemma lem6877731 (_91912 : int) : (term378 _91912) = (term379 _91912).
Proof. exact (MK_COMB (@lem6877728 _91912) (@lem6877727)). Qed.
Lemma lem6877732 (_91912 : int) : (term377 _91912) = (term379 _91912).
Proof. exact (TRANS (@lem6877690 _91912) (@lem6877731 _91912)). Qed.
Lemma lem6877733 (_91912 : int) : (term376 _91912) = (term379 _91912).
Proof. exact (TRANS (@lem6877689 _91912) (@lem6877732 _91912)). Qed.
Lemma lem6877734 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6877735 (_91912 : int) : (term380 _91912) = (term381 _91912).
Proof. exact (MK_COMB (@lem6877734) (@lem6877733 _91912)). Qed.
Lemma lem6877736 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6877737 (_91912 : int) : (term374 _91912) = (term382 _91912).
Proof. exact (MK_COMB (@lem6877735 _91912) (@lem6877736)). Qed.
Lemma lem6877738 (_91912 : int) : (term260 _91912) = (term382 _91912).
Proof. exact (TRANS (@lem6877678 _91912) (@lem6877737 _91912)). Qed.
Lemma lem6877739 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877740 (_91912 : int) : (term249 _91912) = (term383 _91912).
Proof. exact (MK_COMB (@lem6877739) (@lem6877677 _91912)). Qed.
Lemma lem6877741 (_91912 : int) : (term261 _91912) = (term384 _91912).
Proof. exact (MK_COMB (@lem6877740 _91912) (@lem6877738 _91912)). Qed.
Lemma lem6877742 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877743 (_91911 : int) (_91912 : int) : (term262 _91911 _91912) = (term385 _91911 _91912).
Proof. exact (MK_COMB (@lem6877742) (@lem6877610 _91911 _91912)). Qed.
Lemma lem6877744 (_91911 : int) (_91912 : int) : (term263 _91911 _91912) = (term386 _91911 _91912).
Proof. exact (MK_COMB (@lem6877743 _91911 _91912) (@lem6877741 _91912)). Qed.
Lemma lem6877745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6877746 (_91911 : int) (_91912 : int) : (term264 _91911 _91912) = (term387 _91911 _91912).
Proof. exact (MK_COMB (@lem6877745) (@lem6877539 _91911 _91912)). Qed.
Lemma lem6877747 (_91911 : int) (_91912 : int) : (term265 _91911 _91912) = (term388 _91911 _91912).
Proof. exact (MK_COMB (@lem6877746 _91911 _91912) (@lem6877744 _91911 _91912)). Qed.
Lemma lem6877748 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6877749 (_91912 : int) (_91911 : int) : (term266 _91912 _91911) = (term389 _91912 _91911).
Proof. exact (MK_COMB (@lem6877748) (@lem6877469 _91912 _91911)). Qed.
Lemma lem6877750 (_91911 : int) (_91912 : int) : (term267 _91911 _91912) = (term390 _91911 _91912).
Proof. exact (MK_COMB (@lem6877749 _91912 _91911) (@lem6877747 _91911 _91912)). Qed.
Lemma lem6877751 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6877752 (_91912 : int) : (term268 _91912) = (term391 _91912).
Proof. exact (MK_COMB (@lem6877751) (@lem6877174 _91912)). Qed.
Lemma lem6877753 (_91911 : int) (_91912 : int) : (term269 _91911 _91912) = (term392 _91911 _91912).
Proof. exact (MK_COMB (@lem6877752 _91912) (@lem6877750 _91911 _91912)). Qed.
Lemma lem6877754 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6877755 (_91911 : int) : (term268 _91911) = (term391 _91911).
Proof. exact (MK_COMB (@lem6877754) (@lem6877126 _91911)). Qed.
Lemma lem6877756 (_91911 : int) (_91912 : int) : (term270 _91911 _91912) = (term393 _91911 _91912).
Proof. exact (MK_COMB (@lem6877755 _91911) (@lem6877753 _91911 _91912)). Qed.
Lemma lem6877763 (_91911 : int) (_91912 : int) : (term271 _91911 _91912) = (term393 _91911 _91912).
Proof. exact (TRANS (@lem6877078 _91911 _91912) (@lem6877756 _91911 _91912)). Qed.
Lemma lem6877781 (_91911 : int) (_91912 : int) : (term388 _91911 _91912) = (term394 _91911 _91912).
Proof. exact (@lem19158 (term366 _91911 _91912) (term362 _91911 _91912) (term384 _91912)). Qed.
Lemma lem6877782 (_91911 : int) (_91912 : int) : (term395 _91911 _91912) = (term396 _91911 _91912).
Proof. exact (@lem19158 (term373 _91912) (term362 _91911 _91912) (term382 _91912)). Qed.
Lemma lem6877789 (_91911 : int) (_91912 : int) : (term397 _91911 _91912) = (term398 _91911 _91912).
Proof. exact (@lem19367 (term360 _91911 _91912) ((real_of_int _91912) = term214) (term382 _91912)). Qed.
Lemma lem6877796 (_91911 : int) (_91912 : int) : (term399 _91911 _91912) = (term400 _91911 _91912).
Proof. exact (@lem19367 (term360 _91911 _91912) ((real_of_int _91912) = term214) (term373 _91912)). Qed.
Lemma lem6877797 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877798 (_91911 : int) (_91912 : int) : (term401 _91911 _91912) = (term402 _91911 _91912).
Proof. exact (MK_COMB (@lem6877797) (@lem6877796 _91911 _91912)). Qed.
Lemma lem6877799 (_91911 : int) (_91912 : int) : (term396 _91911 _91912) = (term403 _91911 _91912).
Proof. exact (MK_COMB (@lem6877798 _91911 _91912) (@lem6877789 _91911 _91912)). Qed.
Lemma lem6877800 (_91911 : int) (_91912 : int) : (term395 _91911 _91912) = (term403 _91911 _91912).
Proof. exact (TRANS (@lem6877782 _91911 _91912) (@lem6877799 _91911 _91912)). Qed.
Lemma lem6877807 (_91911 : int) (_91912 : int) : (term404 _91911 _91912) = (term405 _91911 _91912).
Proof. exact (@lem19367 (term360 _91911 _91912) ((real_of_int _91912) = term214) (term366 _91911 _91912)). Qed.
Lemma lem6877808 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877809 (_91911 : int) (_91912 : int) : (term406 _91911 _91912) = (term407 _91911 _91912).
Proof. exact (MK_COMB (@lem6877808) (@lem6877807 _91911 _91912)). Qed.
Lemma lem6877810 (_91911 : int) (_91912 : int) : (term394 _91911 _91912) = (term408 _91911 _91912).
Proof. exact (MK_COMB (@lem6877809 _91911 _91912) (@lem6877800 _91911 _91912)). Qed.
Lemma lem6877812 (_91911 : int) (_91912 : int) : (term388 _91911 _91912) = (term408 _91911 _91912).
Proof. exact (TRANS (@lem6877781 _91911 _91912) (@lem6877810 _91911 _91912)). Qed.
Lemma lem6877825 (_91912 : int) (_91911 : int) : (term389 _91912 _91911) = (term389 _91912 _91911).
Proof. exact (eq_refl (term389 _91912 _91911)). Qed.
Lemma lem6877826 (_91911 : int) (_91912 : int) : (term390 _91911 _91912) = (term409 _91911 _91912).
Proof. exact (MK_COMB (@lem6877825 _91912 _91911) (@lem6877812 _91911 _91912)). Qed.
Lemma lem6877827 (_91911 : int) (_91912 : int) : (term409 _91911 _91912) = (term410 _91911 _91912).
Proof. exact (@lem19158 (term405 _91911 _91912) (term354 _91912 _91911) (term403 _91911 _91912)). Qed.
Lemma lem6877828 (_91911 : int) (_91912 : int) : (term411 _91911 _91912) = (term412 _91911 _91912).
Proof. exact (@lem19158 (term400 _91911 _91912) (term354 _91912 _91911) (term398 _91911 _91912)). Qed.
Lemma lem6877829 (_91911 : int) (_91912 : int) : (term413 _91911 _91912) = (term414 _91911 _91912).
Proof. exact (@lem19158 (term415 _91911 _91912) (term354 _91912 _91911) (term416 _91912)). Qed.
Lemma lem6877836 (_91911 : int) (_91912 : int) : (term417 _91911 _91912) = (term418 _91911 _91912).
Proof. exact (@lem19367 ((term316 _91911 _91912) = term214) (term352 _91912 _91911) (term416 _91912)). Qed.
Lemma lem6877843 (_91911 : int) (_91912 : int) : (term419 _91911 _91912) = (term420 _91911 _91912).
Proof. exact (@lem19367 ((term316 _91911 _91912) = term214) (term352 _91912 _91911) (term415 _91911 _91912)). Qed.
Lemma lem6877844 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877845 (_91911 : int) (_91912 : int) : (term421 _91911 _91912) = (term422 _91911 _91912).
Proof. exact (MK_COMB (@lem6877844) (@lem6877843 _91911 _91912)). Qed.
Lemma lem6877846 (_91911 : int) (_91912 : int) : (term414 _91911 _91912) = (term423 _91911 _91912).
Proof. exact (MK_COMB (@lem6877845 _91911 _91912) (@lem6877836 _91911 _91912)). Qed.
Lemma lem6877847 (_91911 : int) (_91912 : int) : (term413 _91911 _91912) = (term423 _91911 _91912).
Proof. exact (TRANS (@lem6877829 _91911 _91912) (@lem6877846 _91911 _91912)). Qed.
Lemma lem6877848 (_91911 : int) (_91912 : int) : (term424 _91911 _91912) = (term425 _91911 _91912).
Proof. exact (@lem19158 (term426 _91911 _91912) (term354 _91912 _91911) (term427 _91912)). Qed.
Lemma lem6877855 (_91911 : int) (_91912 : int) : (term428 _91911 _91912) = (term429 _91911 _91912).
Proof. exact (@lem19367 ((term316 _91911 _91912) = term214) (term352 _91912 _91911) (term427 _91912)). Qed.
Lemma lem6877862 (_91911 : int) (_91912 : int) : (term430 _91911 _91912) = (term431 _91911 _91912).
Proof. exact (@lem19367 ((term316 _91911 _91912) = term214) (term352 _91912 _91911) (term426 _91911 _91912)). Qed.
Lemma lem6877863 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877864 (_91911 : int) (_91912 : int) : (term432 _91911 _91912) = (term433 _91911 _91912).
Proof. exact (MK_COMB (@lem6877863) (@lem6877862 _91911 _91912)). Qed.
Lemma lem6877865 (_91911 : int) (_91912 : int) : (term425 _91911 _91912) = (term434 _91911 _91912).
Proof. exact (MK_COMB (@lem6877864 _91911 _91912) (@lem6877855 _91911 _91912)). Qed.
Lemma lem6877866 (_91911 : int) (_91912 : int) : (term424 _91911 _91912) = (term434 _91911 _91912).
Proof. exact (TRANS (@lem6877848 _91911 _91912) (@lem6877865 _91911 _91912)). Qed.
Lemma lem6877867 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877868 (_91911 : int) (_91912 : int) : (term435 _91911 _91912) = (term436 _91911 _91912).
Proof. exact (MK_COMB (@lem6877867) (@lem6877866 _91911 _91912)). Qed.
Lemma lem6877869 (_91911 : int) (_91912 : int) : (term412 _91911 _91912) = (term437 _91911 _91912).
Proof. exact (MK_COMB (@lem6877868 _91911 _91912) (@lem6877847 _91911 _91912)). Qed.
Lemma lem6877870 (_91911 : int) (_91912 : int) : (term411 _91911 _91912) = (term437 _91911 _91912).
Proof. exact (TRANS (@lem6877828 _91911 _91912) (@lem6877869 _91911 _91912)). Qed.
Lemma lem6877871 (_91911 : int) (_91912 : int) : (term438 _91911 _91912) = (term439 _91911 _91912).
Proof. exact (@lem19158 (term440 _91911 _91912) (term354 _91912 _91911) (term441 _91911 _91912)). Qed.
Lemma lem6877878 (_91911 : int) (_91912 : int) : (term442 _91911 _91912) = (term443 _91911 _91912).
Proof. exact (@lem19367 ((term316 _91911 _91912) = term214) (term352 _91912 _91911) (term441 _91911 _91912)). Qed.
Lemma lem6877885 (_91911 : int) (_91912 : int) : (term444 _91911 _91912) = (term445 _91911 _91912).
Proof. exact (@lem19367 ((term316 _91911 _91912) = term214) (term352 _91912 _91911) (term440 _91911 _91912)). Qed.
Lemma lem6877886 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877887 (_91911 : int) (_91912 : int) : (term446 _91911 _91912) = (term447 _91911 _91912).
Proof. exact (MK_COMB (@lem6877886) (@lem6877885 _91911 _91912)). Qed.
Lemma lem6877888 (_91911 : int) (_91912 : int) : (term439 _91911 _91912) = (term448 _91911 _91912).
Proof. exact (MK_COMB (@lem6877887 _91911 _91912) (@lem6877878 _91911 _91912)). Qed.
Lemma lem6877889 (_91911 : int) (_91912 : int) : (term438 _91911 _91912) = (term448 _91911 _91912).
Proof. exact (TRANS (@lem6877871 _91911 _91912) (@lem6877888 _91911 _91912)). Qed.
Lemma lem6877890 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877891 (_91911 : int) (_91912 : int) : (term449 _91911 _91912) = (term450 _91911 _91912).
Proof. exact (MK_COMB (@lem6877890) (@lem6877889 _91911 _91912)). Qed.
Lemma lem6877892 (_91911 : int) (_91912 : int) : (term410 _91911 _91912) = (term451 _91911 _91912).
Proof. exact (MK_COMB (@lem6877891 _91911 _91912) (@lem6877870 _91911 _91912)). Qed.
Lemma lem6877893 (_91911 : int) (_91912 : int) : (term409 _91911 _91912) = (term451 _91911 _91912).
Proof. exact (TRANS (@lem6877827 _91911 _91912) (@lem6877892 _91911 _91912)). Qed.
Lemma lem6877894 (_91911 : int) (_91912 : int) : (term390 _91911 _91912) = (term451 _91911 _91912).
Proof. exact (TRANS (@lem6877826 _91911 _91912) (@lem6877893 _91911 _91912)). Qed.
Lemma lem6877897 (_91912 : int) : (term391 _91912) = (term391 _91912).
Proof. exact (eq_refl (term391 _91912)). Qed.
Lemma lem6877898 (_91911 : int) (_91912 : int) : (term392 _91911 _91912) = (term452 _91911 _91912).
Proof. exact (MK_COMB (@lem6877897 _91912) (@lem6877894 _91911 _91912)). Qed.
Lemma lem6877899 (_91911 : int) (_91912 : int) : (term452 _91911 _91912) = (term453 _91911 _91912).
Proof. exact (@lem19158 (term448 _91911 _91912) (term299 _91912) (term437 _91911 _91912)). Qed.
Lemma lem6877900 (_91911 : int) (_91912 : int) : (term454 _91911 _91912) = (term455 _91911 _91912).
Proof. exact (@lem19158 (term434 _91911 _91912) (term299 _91912) (term423 _91911 _91912)). Qed.
Lemma lem6877901 (_91911 : int) (_91912 : int) : (term456 _91911 _91912) = (term457 _91911 _91912).
Proof. exact (@lem19158 (term420 _91911 _91912) (term299 _91912) (term418 _91911 _91912)). Qed.
Lemma lem6877908 (_91911 : int) (_91912 : int) : (term458 _91911 _91912) = (term459 _91911 _91912).
Proof. exact (@lem19158 (term460 _91911 _91912) (term299 _91912) (term461 _91911 _91912)). Qed.
Lemma lem6877915 (_91911 : int) (_91912 : int) : (term462 _91911 _91912) = (term463 _91911 _91912).
Proof. exact (@lem19158 (term464 _91911 _91912) (term299 _91912) (term465 _91911 _91912)). Qed.
Lemma lem6877916 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877917 (_91911 : int) (_91912 : int) : (term466 _91911 _91912) = (term467 _91911 _91912).
Proof. exact (MK_COMB (@lem6877916) (@lem6877915 _91911 _91912)). Qed.
Lemma lem6877918 (_91911 : int) (_91912 : int) : (term457 _91911 _91912) = (term468 _91911 _91912).
Proof. exact (MK_COMB (@lem6877917 _91911 _91912) (@lem6877908 _91911 _91912)). Qed.
Lemma lem6877919 (_91911 : int) (_91912 : int) : (term456 _91911 _91912) = (term468 _91911 _91912).
Proof. exact (TRANS (@lem6877901 _91911 _91912) (@lem6877918 _91911 _91912)). Qed.
Lemma lem6877920 (_91911 : int) (_91912 : int) : (term469 _91911 _91912) = (term470 _91911 _91912).
Proof. exact (@lem19158 (term431 _91911 _91912) (term299 _91912) (term429 _91911 _91912)). Qed.
Lemma lem6877927 (_91911 : int) (_91912 : int) : (term471 _91911 _91912) = (term472 _91911 _91912).
Proof. exact (@lem19158 (term473 _91911 _91912) (term299 _91912) (term474 _91911 _91912)). Qed.
Lemma lem6877934 (_91911 : int) (_91912 : int) : (term475 _91911 _91912) = (term476 _91911 _91912).
Proof. exact (@lem19158 (term477 _91911 _91912) (term299 _91912) (term478 _91911 _91912)). Qed.
Lemma lem6877935 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877936 (_91911 : int) (_91912 : int) : (term479 _91911 _91912) = (term480 _91911 _91912).
Proof. exact (MK_COMB (@lem6877935) (@lem6877934 _91911 _91912)). Qed.
Lemma lem6877937 (_91911 : int) (_91912 : int) : (term470 _91911 _91912) = (term481 _91911 _91912).
Proof. exact (MK_COMB (@lem6877936 _91911 _91912) (@lem6877927 _91911 _91912)). Qed.
Lemma lem6877938 (_91911 : int) (_91912 : int) : (term469 _91911 _91912) = (term481 _91911 _91912).
Proof. exact (TRANS (@lem6877920 _91911 _91912) (@lem6877937 _91911 _91912)). Qed.
Lemma lem6877939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877940 (_91911 : int) (_91912 : int) : (term482 _91911 _91912) = (term483 _91911 _91912).
Proof. exact (MK_COMB (@lem6877939) (@lem6877938 _91911 _91912)). Qed.
Lemma lem6877941 (_91911 : int) (_91912 : int) : (term455 _91911 _91912) = (term484 _91911 _91912).
Proof. exact (MK_COMB (@lem6877940 _91911 _91912) (@lem6877919 _91911 _91912)). Qed.
Lemma lem6877942 (_91911 : int) (_91912 : int) : (term454 _91911 _91912) = (term484 _91911 _91912).
Proof. exact (TRANS (@lem6877900 _91911 _91912) (@lem6877941 _91911 _91912)). Qed.
Lemma lem6877943 (_91911 : int) (_91912 : int) : (term485 _91911 _91912) = (term486 _91911 _91912).
Proof. exact (@lem19158 (term445 _91911 _91912) (term299 _91912) (term443 _91911 _91912)). Qed.
Lemma lem6877950 (_91911 : int) (_91912 : int) : (term487 _91911 _91912) = (term488 _91911 _91912).
Proof. exact (@lem19158 (term489 _91911 _91912) (term299 _91912) (term490 _91911 _91912)). Qed.
Lemma lem6877957 (_91911 : int) (_91912 : int) : (term491 _91911 _91912) = (term492 _91911 _91912).
Proof. exact (@lem19158 (term493 _91911 _91912) (term299 _91912) (term494 _91911 _91912)). Qed.
Lemma lem6877958 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877959 (_91911 : int) (_91912 : int) : (term495 _91911 _91912) = (term496 _91911 _91912).
Proof. exact (MK_COMB (@lem6877958) (@lem6877957 _91911 _91912)). Qed.
Lemma lem6877960 (_91911 : int) (_91912 : int) : (term486 _91911 _91912) = (term497 _91911 _91912).
Proof. exact (MK_COMB (@lem6877959 _91911 _91912) (@lem6877950 _91911 _91912)). Qed.
Lemma lem6877961 (_91911 : int) (_91912 : int) : (term485 _91911 _91912) = (term497 _91911 _91912).
Proof. exact (TRANS (@lem6877943 _91911 _91912) (@lem6877960 _91911 _91912)). Qed.
Lemma lem6877962 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877963 (_91911 : int) (_91912 : int) : (term498 _91911 _91912) = (term499 _91911 _91912).
Proof. exact (MK_COMB (@lem6877962) (@lem6877961 _91911 _91912)). Qed.
Lemma lem6877964 (_91911 : int) (_91912 : int) : (term453 _91911 _91912) = (term500 _91911 _91912).
Proof. exact (MK_COMB (@lem6877963 _91911 _91912) (@lem6877942 _91911 _91912)). Qed.
Lemma lem6877965 (_91911 : int) (_91912 : int) : (term452 _91911 _91912) = (term500 _91911 _91912).
Proof. exact (TRANS (@lem6877899 _91911 _91912) (@lem6877964 _91911 _91912)). Qed.
Lemma lem6877966 (_91911 : int) (_91912 : int) : (term392 _91911 _91912) = (term500 _91911 _91912).
Proof. exact (TRANS (@lem6877898 _91911 _91912) (@lem6877965 _91911 _91912)). Qed.
Lemma lem6877969 (_91911 : int) : (term391 _91911) = (term391 _91911).
Proof. exact (eq_refl (term391 _91911)). Qed.
Lemma lem6877970 (_91911 : int) (_91912 : int) : (term393 _91911 _91912) = (term501 _91911 _91912).
Proof. exact (MK_COMB (@lem6877969 _91911) (@lem6877966 _91911 _91912)). Qed.
Lemma lem6877971 (_91911 : int) (_91912 : int) : (term501 _91911 _91912) = (term502 _91911 _91912).
Proof. exact (@lem19158 (term497 _91911 _91912) (term299 _91911) (term484 _91911 _91912)). Qed.
Lemma lem6877972 (_91911 : int) (_91912 : int) : (term503 _91911 _91912) = (term504 _91911 _91912).
Proof. exact (@lem19158 (term481 _91911 _91912) (term299 _91911) (term468 _91911 _91912)). Qed.
Lemma lem6877973 (_91911 : int) (_91912 : int) : (term505 _91911 _91912) = (term506 _91911 _91912).
Proof. exact (@lem19158 (term463 _91911 _91912) (term299 _91911) (term459 _91911 _91912)). Qed.
Lemma lem6877980 (_91911 : int) (_91912 : int) : (term507 _91911 _91912) = (term508 _91911 _91912).
Proof. exact (@lem19158 (term509 _91911 _91912) (term299 _91911) (term510 _91911 _91912)). Qed.
Lemma lem6877987 (_91911 : int) (_91912 : int) : (term511 _91911 _91912) = (term512 _91911 _91912).
Proof. exact (@lem19158 (term513 _91911 _91912) (term299 _91911) (term514 _91911 _91912)). Qed.
Lemma lem6877988 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6877989 (_91911 : int) (_91912 : int) : (term515 _91911 _91912) = (term516 _91911 _91912).
Proof. exact (MK_COMB (@lem6877988) (@lem6877987 _91911 _91912)). Qed.
Lemma lem6877990 (_91911 : int) (_91912 : int) : (term506 _91911 _91912) = (term517 _91911 _91912).
Proof. exact (MK_COMB (@lem6877989 _91911 _91912) (@lem6877980 _91911 _91912)). Qed.
Lemma lem6877991 (_91911 : int) (_91912 : int) : (term505 _91911 _91912) = (term517 _91911 _91912).
Proof. exact (TRANS (@lem6877973 _91911 _91912) (@lem6877990 _91911 _91912)). Qed.
Lemma lem6877992 (_91911 : int) (_91912 : int) : (term518 _91911 _91912) = (term519 _91911 _91912).
Proof. exact (@lem19158 (term476 _91911 _91912) (term299 _91911) (term472 _91911 _91912)). Qed.
Lemma lem6877999 (_91911 : int) (_91912 : int) : (term520 _91911 _91912) = (term521 _91911 _91912).
Proof. exact (@lem19158 (term522 _91911 _91912) (term299 _91911) (term523 _91911 _91912)). Qed.
Lemma lem6878006 (_91911 : int) (_91912 : int) : (term524 _91911 _91912) = (term525 _91911 _91912).
Proof. exact (@lem19158 (term526 _91911 _91912) (term299 _91911) (term527 _91911 _91912)). Qed.
Lemma lem6878007 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6878008 (_91911 : int) (_91912 : int) : (term528 _91911 _91912) = (term529 _91911 _91912).
Proof. exact (MK_COMB (@lem6878007) (@lem6878006 _91911 _91912)). Qed.
Lemma lem6878009 (_91911 : int) (_91912 : int) : (term519 _91911 _91912) = (term530 _91911 _91912).
Proof. exact (MK_COMB (@lem6878008 _91911 _91912) (@lem6877999 _91911 _91912)). Qed.
Lemma lem6878010 (_91911 : int) (_91912 : int) : (term518 _91911 _91912) = (term530 _91911 _91912).
Proof. exact (TRANS (@lem6877992 _91911 _91912) (@lem6878009 _91911 _91912)). Qed.
Lemma lem6878011 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6878012 (_91911 : int) (_91912 : int) : (term531 _91911 _91912) = (term532 _91911 _91912).
Proof. exact (MK_COMB (@lem6878011) (@lem6878010 _91911 _91912)). Qed.
Lemma lem6878013 (_91911 : int) (_91912 : int) : (term504 _91911 _91912) = (term533 _91911 _91912).
Proof. exact (MK_COMB (@lem6878012 _91911 _91912) (@lem6877991 _91911 _91912)). Qed.
Lemma lem6878014 (_91911 : int) (_91912 : int) : (term503 _91911 _91912) = (term533 _91911 _91912).
Proof. exact (TRANS (@lem6877972 _91911 _91912) (@lem6878013 _91911 _91912)). Qed.
Lemma lem6878015 (_91911 : int) (_91912 : int) : (term534 _91911 _91912) = (term535 _91911 _91912).
Proof. exact (@lem19158 (term492 _91911 _91912) (term299 _91911) (term488 _91911 _91912)). Qed.
Lemma lem6878022 (_91911 : int) (_91912 : int) : (term536 _91911 _91912) = (term537 _91911 _91912).
Proof. exact (@lem19158 (term538 _91911 _91912) (term299 _91911) (term539 _91911 _91912)). Qed.
Lemma lem6878029 (_91911 : int) (_91912 : int) : (term540 _91911 _91912) = (term541 _91911 _91912).
Proof. exact (@lem19158 (term542 _91911 _91912) (term299 _91911) (term543 _91911 _91912)). Qed.
Lemma lem6878030 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6878031 (_91911 : int) (_91912 : int) : (term544 _91911 _91912) = (term545 _91911 _91912).
Proof. exact (MK_COMB (@lem6878030) (@lem6878029 _91911 _91912)). Qed.
Lemma lem6878032 (_91911 : int) (_91912 : int) : (term535 _91911 _91912) = (term546 _91911 _91912).
Proof. exact (MK_COMB (@lem6878031 _91911 _91912) (@lem6878022 _91911 _91912)). Qed.
Lemma lem6878033 (_91911 : int) (_91912 : int) : (term534 _91911 _91912) = (term546 _91911 _91912).
Proof. exact (TRANS (@lem6878015 _91911 _91912) (@lem6878032 _91911 _91912)). Qed.
Lemma lem6878034 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6878035 (_91911 : int) (_91912 : int) : (term547 _91911 _91912) = (term548 _91911 _91912).
Proof. exact (MK_COMB (@lem6878034) (@lem6878033 _91911 _91912)). Qed.
Lemma lem6878036 (_91911 : int) (_91912 : int) : (term502 _91911 _91912) = (term549 _91911 _91912).
Proof. exact (MK_COMB (@lem6878035 _91911 _91912) (@lem6878014 _91911 _91912)). Qed.
Lemma lem6878037 (_91911 : int) (_91912 : int) : (term501 _91911 _91912) = (term549 _91911 _91912).
Proof. exact (TRANS (@lem6877971 _91911 _91912) (@lem6878036 _91911 _91912)). Qed.
Lemma lem6878038 (_91911 : int) (_91912 : int) : (term393 _91911 _91912) = (term549 _91911 _91912).
Proof. exact (TRANS (@lem6877970 _91911 _91912) (@lem6878037 _91911 _91912)). Qed.
Lemma lem6878039 (_91911 : int) (_91912 : int) : (term271 _91911 _91912) = (term549 _91911 _91912).
Proof. exact (TRANS (@lem6877763 _91911 _91912) (@lem6878038 _91911 _91912)). Qed.
Lemma lem6878109 (_91911 : int) (_91912 : int) (h1 : term549 _91911 _91912) : term549 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6878110 (_91911 : int) (_91912 : int) (h1 : term546 _91911 _91912) : term546 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6878111 (_91911 : int) (_91912 : int) (h1 : term541 _91911 _91912) : term541 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6878112 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : term550 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6878113 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : term542 _91911 _91912.
Proof. exact (proj2 (@lem6878112 _91911 _91912 h1)). Qed.
Lemma lem6878115 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : term493 _91911 _91912.
Proof. exact (proj2 (@lem6878113 _91911 _91912 h1)). Qed.
Lemma lem6878117 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : term440 _91911 _91912.
Proof. exact (proj2 (@lem6878115 _91911 _91912 h1)). Qed.
Lemma lem6878118 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : (term316 _91911 _91912) = term214.
Proof. exact (proj1 (@lem6878115 _91911 _91912 h1)). Qed.
Lemma lem6878120 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : term360 _91911 _91912.
Proof. exact (proj1 (@lem6878117 _91911 _91912 h1)). Qed.
Lemma lem6878122 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6878123 : term551 = term331.
Proof. exact (@lem6878122 term214 term224). Qed.
Lemma lem6878125 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6878126 : term224 = term304.
Proof. exact (@lem6878125 term92). Qed.
Lemma lem6878128 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6878129 : term214 = term276.
Proof. exact (@lem6878128 (NUMERAL 0)). Qed.
Lemma lem6878130 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6878131 : term552 = term553.
Proof. exact (MK_COMB (@lem6878130) (@lem6878129)). Qed.
Lemma lem6878132 : term331 = term554.
Proof. exact (MK_COMB (@lem6878131) (@lem6878126)). Qed.
Lemma lem6878133 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6878135 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878136 : term331 = term332.
Proof. exact (@lem6878135 (NUMERAL 0) term92). Qed.
Lemma lem6878137 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878138 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878139 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878138 h1) (fun h1 : term332 = True => @lem6878137)). Qed.
Lemma lem6878140 : term332 = True.
Proof. exact (EQ_MP (@lem6878139) (@lem6878137)). Qed.
Lemma lem6878141 : term331 = True.
Proof. exact (TRANS (@lem6878136) (@lem6878140)). Qed.
Lemma lem6878142 : True = term331.
Proof. exact (SYM (@lem6878141)). Qed.
Lemma lem6878143 : term331.
Proof. exact (EQ_MP (@lem6878142) (@lem0)). Qed.
Lemma lem6878144 : term556.
Proof. exact (@lem6878133 (@lem6878143)). Qed.
Lemma lem6878146 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878147 : term331 = term332.
Proof. exact (@lem6878146 (NUMERAL 0) term92). Qed.
Lemma lem6878148 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878149 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878150 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878149 h1) (fun h1 : term332 = True => @lem6878148)). Qed.
Lemma lem6878151 : term332 = True.
Proof. exact (EQ_MP (@lem6878150) (@lem6878148)). Qed.
Lemma lem6878152 : term331 = True.
Proof. exact (TRANS (@lem6878147) (@lem6878151)). Qed.
Lemma lem6878153 : True = term331.
Proof. exact (SYM (@lem6878152)). Qed.
Lemma lem6878154 : term331.
Proof. exact (EQ_MP (@lem6878153) (@lem0)). Qed.
Lemma lem6878155 : term554 = term557.
Proof. exact (@lem6878144 (@lem6878154)). Qed.
Lemma lem6878157 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6878158 : term288 = term289.
Proof. exact (@lem6878157 term92 term92). Qed.
Lemma lem6878159 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878160 : term291 = term92.
Proof. exact (EQ_MP (@lem6878159) (@lem940073)). Qed.
Lemma lem6878161 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878162 : term289 = term224.
Proof. exact (MK_COMB (@lem6878161) (@lem6878160)). Qed.
Lemma lem6878163 : term288 = term224.
Proof. exact (TRANS (@lem6878158) (@lem6878162)). Qed.
Lemma lem6878165 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6878166 : term343 = term214.
Proof. exact (@lem6878165 term92). Qed.
Lemma lem6878167 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6878168 : term558 = term552.
Proof. exact (MK_COMB (@lem6878167) (@lem6878166)). Qed.
Lemma lem6878169 : term557 = term331.
Proof. exact (MK_COMB (@lem6878168) (@lem6878163)). Qed.
Lemma lem6878171 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878172 : term331 = term332.
Proof. exact (@lem6878171 (NUMERAL 0) term92). Qed.
Lemma lem6878173 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878174 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878175 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878174 h1) (fun h1 : term332 = True => @lem6878173)). Qed.
Lemma lem6878176 : term332 = True.
Proof. exact (EQ_MP (@lem6878175) (@lem6878173)). Qed.
Lemma lem6878177 : term331 = True.
Proof. exact (TRANS (@lem6878172) (@lem6878176)). Qed.
Lemma lem6878178 : term557 = True.
Proof. exact (TRANS (@lem6878169) (@lem6878177)). Qed.
Lemma lem6878179 : term554 = True.
Proof. exact (TRANS (@lem6878155) (@lem6878178)). Qed.
Lemma lem6878180 : term331 = True.
Proof. exact (TRANS (@lem6878132) (@lem6878179)). Qed.
Lemma lem6878181 : term551 = True.
Proof. exact (TRANS (@lem6878123) (@lem6878180)). Qed.
Lemma lem6878182 : True = term551.
Proof. exact (SYM (@lem6878181)). Qed.
Lemma lem6878183 : term551.
Proof. exact (EQ_MP (@lem6878182) (@lem0)). Qed.
Lemma lem6878184 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : term559 _91911 _91912.
Proof. exact (conj (@lem6878183) (@lem6878120 _91911 _91912 h1)). Qed.
Lemma lem6878186 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6878187 (_91911 : int) (_91912 : int) : term561 _91911 _91912.
Proof. exact (@lem6878186 term224 (term357 _91911 _91912)). Qed.
Lemma lem6878188 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : term562 _91911 _91912.
Proof. exact (@lem6878187 _91911 _91912 (@lem6878184 _91911 _91912 h1)). Qed.
Lemma lem6878189 (_91911 : int) (_91912 : int) : (term563 _91911 _91912) = (term357 _91911 _91912).
Proof. exact (@lem1982733 (term357 _91911 _91912)). Qed.
Lemma lem6878190 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6878191 (_91911 : int) (_91912 : int) : (term564 _91911 _91912) = (term359 _91911 _91912).
Proof. exact (MK_COMB (@lem6878190) (@lem6878189 _91911 _91912)). Qed.
Lemma lem6878192 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6878193 (_91911 : int) (_91912 : int) : (term562 _91911 _91912) = (term360 _91911 _91912).
Proof. exact (MK_COMB (@lem6878191 _91911 _91912) (@lem6878192)). Qed.
Lemma lem6878194 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : term360 _91911 _91912.
Proof. exact (EQ_MP (@lem6878193 _91911 _91912) (@lem6878188 _91911 _91912 h1)). Qed.
Lemma lem6878196 (y : real) : term565 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6878197 (_91911 : int) (_91912 : int) : term566 _91911 _91912.
Proof. exact (@lem6878196 (term316 _91911 _91912)). Qed.
Lemma lem6878198 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : term567 _91911 _91912.
Proof. exact (@lem6878197 _91911 _91912 (@lem6878118 _91911 _91912 h1)). Qed.
Lemma lem6878199 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : term568 _91911 _91912.
Proof. exact (@lem6878198 _91911 _91912 h1 term224). Qed.
Lemma lem6878200 (_91911 : int) (_91912 : int) : (term568 _91911 _91912) = ((term569 _91911 _91912) = term214).
Proof. exact (eq_refl (term568 _91911 _91912)). Qed.
Lemma lem6878201 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : (term569 _91911 _91912) = term214.
Proof. exact (EQ_MP (@lem6878200 _91911 _91912) (@lem6878199 _91911 _91912 h1)). Qed.
Lemma lem6878202 (_91911 : int) (_91912 : int) : (term569 _91911 _91912) = (term316 _91911 _91912).
Proof. exact (@lem1982733 (term316 _91911 _91912)). Qed.
Lemma lem6878203 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6878204 (_91911 : int) (_91912 : int) : (term570 _91911 _91912) = (term319 _91911 _91912).
Proof. exact (MK_COMB (@lem6878203) (@lem6878202 _91911 _91912)). Qed.
Lemma lem6878205 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6878206 (_91911 : int) (_91912 : int) : ((term569 _91911 _91912) = term214) = ((term316 _91911 _91912) = term214).
Proof. exact (MK_COMB (@lem6878204 _91911 _91912) (@lem6878205)). Qed.
Lemma lem6878207 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : (term316 _91911 _91912) = term214.
Proof. exact (EQ_MP (@lem6878206 _91911 _91912) (@lem6878201 _91911 _91912 h1)). Qed.
Lemma lem6878208 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : term571 _91911 _91912.
Proof. exact (conj (@lem6878207 _91911 _91912 h1) (@lem6878194 _91911 _91912 h1)). Qed.
Lemma lem6878210 (x : real) (y : real) : term572 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6878211 (_91911 : int) (_91912 : int) : term573 _91911 _91912.
Proof. exact (@lem6878210 (term316 _91911 _91912) (term357 _91911 _91912)). Qed.
Lemma lem6878212 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : term574 _91911 _91912.
Proof. exact (@lem6878211 _91911 _91912 (@lem6878208 _91911 _91912 h1)). Qed.
Lemma lem6878213 (_91911 : int) (_91912 : int) : (term575 _91911 _91912) = (term576 _91911 _91912).
Proof. exact (@lem1982753 (term317 _91911) (real_of_int _91911) (term379 _91912) (term317 _91912)). Qed.
Lemma lem6878214 (_91911 : int) : (term577 _91911) = (term578 _91911).
Proof. exact (@lem1982713 term279 (real_of_int _91911)). Qed.
Lemma lem6878216 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6878217 : term224 = term304.
Proof. exact (@lem6878216 term92). Qed.
Lemma lem6878219 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6878220 : term279 = term280.
Proof. exact (@lem6878219 term92). Qed.
Lemma lem6878221 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6878222 : term579 = term580.
Proof. exact (MK_COMB (@lem6878221) (@lem6878220)). Qed.
Lemma lem6878223 : term581 = term582.
Proof. exact (MK_COMB (@lem6878222) (@lem6878217)). Qed.
Lemma lem6878224 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6878226 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878227 : term331 = term332.
Proof. exact (@lem6878226 (NUMERAL 0) term92). Qed.
Lemma lem6878228 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878229 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878230 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878229 h1) (fun h1 : term332 = True => @lem6878228)). Qed.
Lemma lem6878231 : term332 = True.
Proof. exact (EQ_MP (@lem6878230) (@lem6878228)). Qed.
Lemma lem6878232 : term331 = True.
Proof. exact (TRANS (@lem6878227) (@lem6878231)). Qed.
Lemma lem6878233 : True = term331.
Proof. exact (SYM (@lem6878232)). Qed.
Lemma lem6878234 : term331.
Proof. exact (EQ_MP (@lem6878233) (@lem0)). Qed.
Lemma lem6878235 : term584.
Proof. exact (@lem6878224 (@lem6878234)). Qed.
Lemma lem6878237 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878238 : term331 = term332.
Proof. exact (@lem6878237 (NUMERAL 0) term92). Qed.
Lemma lem6878239 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878240 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878241 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878240 h1) (fun h1 : term332 = True => @lem6878239)). Qed.
Lemma lem6878242 : term332 = True.
Proof. exact (EQ_MP (@lem6878241) (@lem6878239)). Qed.
Lemma lem6878243 : term331 = True.
Proof. exact (TRANS (@lem6878238) (@lem6878242)). Qed.
Lemma lem6878244 : True = term331.
Proof. exact (SYM (@lem6878243)). Qed.
Lemma lem6878245 : term331.
Proof. exact (EQ_MP (@lem6878244) (@lem0)). Qed.
Lemma lem6878246 : term585.
Proof. exact (@lem6878235 (@lem6878245)). Qed.
Lemma lem6878248 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878249 : term331 = term332.
Proof. exact (@lem6878248 (NUMERAL 0) term92). Qed.
Lemma lem6878250 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878251 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878252 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878251 h1) (fun h1 : term332 = True => @lem6878250)). Qed.
Lemma lem6878253 : term332 = True.
Proof. exact (EQ_MP (@lem6878252) (@lem6878250)). Qed.
Lemma lem6878254 : term331 = True.
Proof. exact (TRANS (@lem6878249) (@lem6878253)). Qed.
Lemma lem6878255 : True = term331.
Proof. exact (SYM (@lem6878254)). Qed.
Lemma lem6878256 : term331.
Proof. exact (EQ_MP (@lem6878255) (@lem0)). Qed.
Lemma lem6878257 : term586.
Proof. exact (@lem6878246 (@lem6878256)). Qed.
Lemma lem6878259 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6878260 : term288 = term289.
Proof. exact (@lem6878259 term92 term92). Qed.
Lemma lem6878261 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878262 : term291 = term92.
Proof. exact (EQ_MP (@lem6878261) (@lem940073)). Qed.
Lemma lem6878263 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878264 : term289 = term224.
Proof. exact (MK_COMB (@lem6878263) (@lem6878262)). Qed.
Lemma lem6878265 : term288 = term224.
Proof. exact (TRANS (@lem6878260) (@lem6878264)). Qed.
Lemma lem6878267 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6878268 : term305 = term310.
Proof. exact (@lem6878267 term92 term92). Qed.
Lemma lem6878269 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878270 : term291 = term92.
Proof. exact (EQ_MP (@lem6878269) (@lem940073)). Qed.
Lemma lem6878271 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878272 : term289 = term224.
Proof. exact (MK_COMB (@lem6878271) (@lem6878270)). Qed.
Lemma lem6878273 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6878274 : term310 = term279.
Proof. exact (MK_COMB (@lem6878273) (@lem6878272)). Qed.
Lemma lem6878275 : term305 = term279.
Proof. exact (TRANS (@lem6878268) (@lem6878274)). Qed.
Lemma lem6878276 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6878277 : term587 = term579.
Proof. exact (MK_COMB (@lem6878276) (@lem6878275)). Qed.
Lemma lem6878278 : term588 = term581.
Proof. exact (MK_COMB (@lem6878277) (@lem6878265)). Qed.
Lemma lem6878280 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6878281 : term581 = term214.
Proof. exact (@lem6878280 term92). Qed.
Lemma lem6878282 : term588 = term214.
Proof. exact (TRANS (@lem6878278) (@lem6878281)). Qed.
Lemma lem6878283 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6878284 : term590 = term341.
Proof. exact (MK_COMB (@lem6878283) (@lem6878282)). Qed.
Lemma lem6878285 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6878286 : term591 = term343.
Proof. exact (MK_COMB (@lem6878284) (@lem6878285)). Qed.
Lemma lem6878288 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6878289 : term343 = term214.
Proof. exact (@lem6878288 term92). Qed.
Lemma lem6878290 : term591 = term214.
Proof. exact (TRANS (@lem6878286) (@lem6878289)). Qed.
Lemma lem6878292 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6878293 : term288 = term289.
Proof. exact (@lem6878292 term92 term92). Qed.
Lemma lem6878294 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878295 : term291 = term92.
Proof. exact (EQ_MP (@lem6878294) (@lem940073)). Qed.
Lemma lem6878296 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878297 : term289 = term224.
Proof. exact (MK_COMB (@lem6878296) (@lem6878295)). Qed.
Lemma lem6878298 : term288 = term224.
Proof. exact (TRANS (@lem6878293) (@lem6878297)). Qed.
Lemma lem6878299 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6878300 : term345 = term343.
Proof. exact (MK_COMB (@lem6878299) (@lem6878298)). Qed.
Lemma lem6878302 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6878303 : term343 = term214.
Proof. exact (@lem6878302 term92). Qed.
Lemma lem6878304 : term345 = term214.
Proof. exact (TRANS (@lem6878300) (@lem6878303)). Qed.
Lemma lem6878305 : term214 = term345.
Proof. exact (SYM (@lem6878304)). Qed.
Lemma lem6878306 : term591 = term345.
Proof. exact (TRANS (@lem6878290) (@lem6878305)). Qed.
Lemma lem6878307 : term582 = term276.
Proof. exact (@lem6878257 (@lem6878306)). Qed.
Lemma lem6878308 : term581 = term276.
Proof. exact (TRANS (@lem6878223) (@lem6878307)). Qed.
Lemma lem6878310 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6878311 : term276 = term214.
Proof. exact (@lem6878310 term214). Qed.
Lemma lem6878312 : term581 = term214.
Proof. exact (TRANS (@lem6878308) (@lem6878311)). Qed.
Lemma lem6878313 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6878314 : term592 = term341.
Proof. exact (MK_COMB (@lem6878313) (@lem6878312)). Qed.
Lemma lem6878315 (_91911 : int) : (real_of_int _91911) = (real_of_int _91911).
Proof. exact (eq_refl (real_of_int _91911)). Qed.
Lemma lem6878316 (_91911 : int) : (term578 _91911) = (term593 _91911).
Proof. exact (MK_COMB (@lem6878314) (@lem6878315 _91911)). Qed.
Lemma lem6878317 (_91911 : int) : (term577 _91911) = (term593 _91911).
Proof. exact (TRANS (@lem6878214 _91911) (@lem6878316 _91911)). Qed.
Lemma lem6878318 (_91911 : int) : (term593 _91911) = term214.
Proof. exact (@lem1982719 (real_of_int _91911)). Qed.
Lemma lem6878319 (_91911 : int) : (term577 _91911) = term214.
Proof. exact (TRANS (@lem6878317 _91911) (@lem6878318 _91911)). Qed.
Lemma lem6878320 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6878321 (_91911 : int) : (term594 _91911) = term256.
Proof. exact (MK_COMB (@lem6878320) (@lem6878319 _91911)). Qed.
Lemma lem6878322 (_91912 : int) : (term595 _91912) = (term596 _91912).
Proof. exact (@lem1982759 (real_of_int _91912) (term317 _91912) term279). Qed.
Lemma lem6878323 (_91912 : int) : (term597 _91912) = (term578 _91912).
Proof. exact (@lem1982715 term279 (real_of_int _91912)). Qed.
Lemma lem6878325 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6878326 : term224 = term304.
Proof. exact (@lem6878325 term92). Qed.
Lemma lem6878328 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6878329 : term279 = term280.
Proof. exact (@lem6878328 term92). Qed.
Lemma lem6878330 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6878331 : term579 = term580.
Proof. exact (MK_COMB (@lem6878330) (@lem6878329)). Qed.
Lemma lem6878332 : term581 = term582.
Proof. exact (MK_COMB (@lem6878331) (@lem6878326)). Qed.
Lemma lem6878333 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6878335 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878336 : term331 = term332.
Proof. exact (@lem6878335 (NUMERAL 0) term92). Qed.
Lemma lem6878337 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878338 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878339 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878338 h1) (fun h1 : term332 = True => @lem6878337)). Qed.
Lemma lem6878340 : term332 = True.
Proof. exact (EQ_MP (@lem6878339) (@lem6878337)). Qed.
Lemma lem6878341 : term331 = True.
Proof. exact (TRANS (@lem6878336) (@lem6878340)). Qed.
Lemma lem6878342 : True = term331.
Proof. exact (SYM (@lem6878341)). Qed.
Lemma lem6878343 : term331.
Proof. exact (EQ_MP (@lem6878342) (@lem0)). Qed.
Lemma lem6878344 : term584.
Proof. exact (@lem6878333 (@lem6878343)). Qed.
Lemma lem6878346 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878347 : term331 = term332.
Proof. exact (@lem6878346 (NUMERAL 0) term92). Qed.
Lemma lem6878348 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878349 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878350 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878349 h1) (fun h1 : term332 = True => @lem6878348)). Qed.
Lemma lem6878351 : term332 = True.
Proof. exact (EQ_MP (@lem6878350) (@lem6878348)). Qed.
Lemma lem6878352 : term331 = True.
Proof. exact (TRANS (@lem6878347) (@lem6878351)). Qed.
Lemma lem6878353 : True = term331.
Proof. exact (SYM (@lem6878352)). Qed.
Lemma lem6878354 : term331.
Proof. exact (EQ_MP (@lem6878353) (@lem0)). Qed.
Lemma lem6878355 : term585.
Proof. exact (@lem6878344 (@lem6878354)). Qed.
Lemma lem6878357 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878358 : term331 = term332.
Proof. exact (@lem6878357 (NUMERAL 0) term92). Qed.
Lemma lem6878359 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878360 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878361 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878360 h1) (fun h1 : term332 = True => @lem6878359)). Qed.
Lemma lem6878362 : term332 = True.
Proof. exact (EQ_MP (@lem6878361) (@lem6878359)). Qed.
Lemma lem6878363 : term331 = True.
Proof. exact (TRANS (@lem6878358) (@lem6878362)). Qed.
Lemma lem6878364 : True = term331.
Proof. exact (SYM (@lem6878363)). Qed.
Lemma lem6878365 : term331.
Proof. exact (EQ_MP (@lem6878364) (@lem0)). Qed.
Lemma lem6878366 : term586.
Proof. exact (@lem6878355 (@lem6878365)). Qed.
Lemma lem6878368 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6878369 : term288 = term289.
Proof. exact (@lem6878368 term92 term92). Qed.
Lemma lem6878370 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878371 : term291 = term92.
Proof. exact (EQ_MP (@lem6878370) (@lem940073)). Qed.
Lemma lem6878372 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878373 : term289 = term224.
Proof. exact (MK_COMB (@lem6878372) (@lem6878371)). Qed.
Lemma lem6878374 : term288 = term224.
Proof. exact (TRANS (@lem6878369) (@lem6878373)). Qed.
Lemma lem6878376 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6878377 : term305 = term310.
Proof. exact (@lem6878376 term92 term92). Qed.
Lemma lem6878378 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878379 : term291 = term92.
Proof. exact (EQ_MP (@lem6878378) (@lem940073)). Qed.
Lemma lem6878380 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878381 : term289 = term224.
Proof. exact (MK_COMB (@lem6878380) (@lem6878379)). Qed.
Lemma lem6878382 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6878383 : term310 = term279.
Proof. exact (MK_COMB (@lem6878382) (@lem6878381)). Qed.
Lemma lem6878384 : term305 = term279.
Proof. exact (TRANS (@lem6878377) (@lem6878383)). Qed.
Lemma lem6878385 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6878386 : term587 = term579.
Proof. exact (MK_COMB (@lem6878385) (@lem6878384)). Qed.
Lemma lem6878387 : term588 = term581.
Proof. exact (MK_COMB (@lem6878386) (@lem6878374)). Qed.
Lemma lem6878389 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6878390 : term581 = term214.
Proof. exact (@lem6878389 term92). Qed.
Lemma lem6878391 : term588 = term214.
Proof. exact (TRANS (@lem6878387) (@lem6878390)). Qed.
Lemma lem6878392 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6878393 : term590 = term341.
Proof. exact (MK_COMB (@lem6878392) (@lem6878391)). Qed.
Lemma lem6878394 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6878395 : term591 = term343.
Proof. exact (MK_COMB (@lem6878393) (@lem6878394)). Qed.
Lemma lem6878397 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6878398 : term343 = term214.
Proof. exact (@lem6878397 term92). Qed.
Lemma lem6878399 : term591 = term214.
Proof. exact (TRANS (@lem6878395) (@lem6878398)). Qed.
Lemma lem6878401 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6878402 : term288 = term289.
Proof. exact (@lem6878401 term92 term92). Qed.
Lemma lem6878403 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878404 : term291 = term92.
Proof. exact (EQ_MP (@lem6878403) (@lem940073)). Qed.
Lemma lem6878405 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878406 : term289 = term224.
Proof. exact (MK_COMB (@lem6878405) (@lem6878404)). Qed.
Lemma lem6878407 : term288 = term224.
Proof. exact (TRANS (@lem6878402) (@lem6878406)). Qed.
Lemma lem6878408 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6878409 : term345 = term343.
Proof. exact (MK_COMB (@lem6878408) (@lem6878407)). Qed.
Lemma lem6878411 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6878412 : term343 = term214.
Proof. exact (@lem6878411 term92). Qed.
Lemma lem6878413 : term345 = term214.
Proof. exact (TRANS (@lem6878409) (@lem6878412)). Qed.
Lemma lem6878414 : term214 = term345.
Proof. exact (SYM (@lem6878413)). Qed.
Lemma lem6878415 : term591 = term345.
Proof. exact (TRANS (@lem6878399) (@lem6878414)). Qed.
Lemma lem6878416 : term582 = term276.
Proof. exact (@lem6878366 (@lem6878415)). Qed.
Lemma lem6878417 : term581 = term276.
Proof. exact (TRANS (@lem6878332) (@lem6878416)). Qed.
Lemma lem6878419 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6878420 : term276 = term214.
Proof. exact (@lem6878419 term214). Qed.
Lemma lem6878421 : term581 = term214.
Proof. exact (TRANS (@lem6878417) (@lem6878420)). Qed.
Lemma lem6878422 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6878423 : term592 = term341.
Proof. exact (MK_COMB (@lem6878422) (@lem6878421)). Qed.
Lemma lem6878424 (_91912 : int) : (real_of_int _91912) = (real_of_int _91912).
Proof. exact (eq_refl (real_of_int _91912)). Qed.
Lemma lem6878425 (_91912 : int) : (term578 _91912) = (term593 _91912).
Proof. exact (MK_COMB (@lem6878423) (@lem6878424 _91912)). Qed.
Lemma lem6878426 (_91912 : int) : (term597 _91912) = (term593 _91912).
Proof. exact (TRANS (@lem6878323 _91912) (@lem6878425 _91912)). Qed.
Lemma lem6878427 (_91912 : int) : (term593 _91912) = term214.
Proof. exact (@lem1982719 (real_of_int _91912)). Qed.
Lemma lem6878428 (_91912 : int) : (term597 _91912) = term214.
Proof. exact (TRANS (@lem6878426 _91912) (@lem6878427 _91912)). Qed.
Lemma lem6878429 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6878430 (_91912 : int) : (term598 _91912) = term256.
Proof. exact (MK_COMB (@lem6878429) (@lem6878428 _91912)). Qed.
Lemma lem6878431 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem6878432 (_91912 : int) : (term596 _91912) = term599.
Proof. exact (MK_COMB (@lem6878430 _91912) (@lem6878431)). Qed.
Lemma lem6878433 (_91912 : int) : (term595 _91912) = term599.
Proof. exact (TRANS (@lem6878322 _91912) (@lem6878432 _91912)). Qed.
Lemma lem6878434 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6878435 (_91912 : int) : (term595 _91912) = term279.
Proof. exact (TRANS (@lem6878433 _91912) (@lem6878434)). Qed.
Lemma lem6878436 (_91911 : int) (_91912 : int) : (term576 _91911 _91912) = term599.
Proof. exact (MK_COMB (@lem6878321 _91911) (@lem6878435 _91912)). Qed.
Lemma lem6878437 (_91911 : int) (_91912 : int) : (term575 _91911 _91912) = term599.
Proof. exact (TRANS (@lem6878213 _91911 _91912) (@lem6878436 _91911 _91912)). Qed.
Lemma lem6878438 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6878439 (_91911 : int) (_91912 : int) : (term575 _91911 _91912) = term279.
Proof. exact (TRANS (@lem6878437 _91911 _91912) (@lem6878438)). Qed.
Lemma lem6878440 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6878441 (_91911 : int) (_91912 : int) : (term600 _91911 _91912) = term601.
Proof. exact (MK_COMB (@lem6878440) (@lem6878439 _91911 _91912)). Qed.
Lemma lem6878442 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6878443 (_91911 : int) (_91912 : int) : (term574 _91911 _91912) = term602.
Proof. exact (MK_COMB (@lem6878441 _91911 _91912) (@lem6878442)). Qed.
Lemma lem6878444 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : term602.
Proof. exact (EQ_MP (@lem6878443 _91911 _91912) (@lem6878212 _91911 _91912 h1)). Qed.
Lemma lem6878446 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6878447 : term602 = term603.
Proof. exact (@lem6878446 term214 term279). Qed.
Lemma lem6878449 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6878450 : term279 = term280.
Proof. exact (@lem6878449 term92). Qed.
Lemma lem6878452 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6878453 : term214 = term276.
Proof. exact (@lem6878452 (NUMERAL 0)). Qed.
Lemma lem6878454 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6878455 : term216 = term604.
Proof. exact (MK_COMB (@lem6878454) (@lem6878453)). Qed.
Lemma lem6878456 : term603 = term605.
Proof. exact (MK_COMB (@lem6878455) (@lem6878450)). Qed.
Lemma lem6878457 : term606.
Proof. exact (@lem1980026 term214 term224 term279 term224). Qed.
Lemma lem6878459 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878460 : term331 = term332.
Proof. exact (@lem6878459 (NUMERAL 0) term92). Qed.
Lemma lem6878461 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878462 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878463 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878462 h1) (fun h1 : term332 = True => @lem6878461)). Qed.
Lemma lem6878464 : term332 = True.
Proof. exact (EQ_MP (@lem6878463) (@lem6878461)). Qed.
Lemma lem6878465 : term331 = True.
Proof. exact (TRANS (@lem6878460) (@lem6878464)). Qed.
Lemma lem6878466 : True = term331.
Proof. exact (SYM (@lem6878465)). Qed.
Lemma lem6878467 : term331.
Proof. exact (EQ_MP (@lem6878466) (@lem0)). Qed.
Lemma lem6878468 : term607.
Proof. exact (@lem6878457 (@lem6878467)). Qed.
Lemma lem6878470 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878471 : term331 = term332.
Proof. exact (@lem6878470 (NUMERAL 0) term92). Qed.
Lemma lem6878472 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878473 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878474 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878473 h1) (fun h1 : term332 = True => @lem6878472)). Qed.
Lemma lem6878475 : term332 = True.
Proof. exact (EQ_MP (@lem6878474) (@lem6878472)). Qed.
Lemma lem6878476 : term331 = True.
Proof. exact (TRANS (@lem6878471) (@lem6878475)). Qed.
Lemma lem6878477 : True = term331.
Proof. exact (SYM (@lem6878476)). Qed.
Lemma lem6878478 : term331.
Proof. exact (EQ_MP (@lem6878477) (@lem0)). Qed.
Lemma lem6878479 : term605 = term608.
Proof. exact (@lem6878468 (@lem6878478)). Qed.
Lemma lem6878481 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6878482 : term305 = term310.
Proof. exact (@lem6878481 term92 term92). Qed.
Lemma lem6878483 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878484 : term291 = term92.
Proof. exact (EQ_MP (@lem6878483) (@lem940073)). Qed.
Lemma lem6878485 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878486 : term289 = term224.
Proof. exact (MK_COMB (@lem6878485) (@lem6878484)). Qed.
Lemma lem6878487 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6878488 : term310 = term279.
Proof. exact (MK_COMB (@lem6878487) (@lem6878486)). Qed.
Lemma lem6878489 : term305 = term279.
Proof. exact (TRANS (@lem6878482) (@lem6878488)). Qed.
Lemma lem6878491 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6878492 : term343 = term214.
Proof. exact (@lem6878491 term92). Qed.
Lemma lem6878493 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6878494 : term609 = term216.
Proof. exact (MK_COMB (@lem6878493) (@lem6878492)). Qed.
Lemma lem6878495 : term608 = term603.
Proof. exact (MK_COMB (@lem6878494) (@lem6878489)). Qed.
Lemma lem6878497 (m : nat) (n : nat) : (term610 m n) = (term611 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6878498 : term603 = term612.
Proof. exact (@lem6878497 (NUMERAL 0) term92). Qed.
Lemma lem6878499 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878500 (h1 : term333 = (BIT1 0)) : (term92 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6878501 : (term333 = (BIT1 0)) = ((term92 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878500 h1) (fun h1 : (term92 = (NUMERAL 0)) = False => @lem6878499)). Qed.
Lemma lem6878502 : (term92 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6878501) (@lem6878499)). Qed.
Lemma lem6878503 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6878504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6878505 : term613 = (and True).
Proof. exact (MK_COMB (@lem6878504) (@lem6878503)). Qed.
Lemma lem6878506 : term612 = (True /\ False).
Proof. exact (MK_COMB (@lem6878505) (@lem6878502)). Qed.
Lemma lem6878508 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6878509 : term612 = False.
Proof. exact (TRANS (@lem6878506) (@lem6878508)). Qed.
Lemma lem6878510 : term603 = False.
Proof. exact (TRANS (@lem6878498) (@lem6878509)). Qed.
Lemma lem6878511 : term608 = False.
Proof. exact (TRANS (@lem6878495) (@lem6878510)). Qed.
Lemma lem6878512 : term605 = False.
Proof. exact (TRANS (@lem6878479) (@lem6878511)). Qed.
Lemma lem6878513 : term603 = False.
Proof. exact (TRANS (@lem6878456) (@lem6878512)). Qed.
Lemma lem6878514 : term602 = False.
Proof. exact (TRANS (@lem6878447) (@lem6878513)). Qed.
Lemma lem6878515 (_91911 : int) (_91912 : int) (h1 : term550 _91911 _91912) : False.
Proof. exact (EQ_MP (@lem6878514) (@lem6878444 _91911 _91912 h1)). Qed.
Lemma lem6878516 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term614 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6878517 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term543 _91911 _91912.
Proof. exact (proj2 (@lem6878516 _91911 _91912 h1)). Qed.
Lemma lem6878519 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term494 _91911 _91912.
Proof. exact (proj2 (@lem6878517 _91911 _91912 h1)). Qed.
Lemma lem6878521 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term440 _91911 _91912.
Proof. exact (proj2 (@lem6878519 _91911 _91912 h1)). Qed.
Lemma lem6878522 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term352 _91912 _91911.
Proof. exact (proj1 (@lem6878519 _91911 _91912 h1)). Qed.
Lemma lem6878523 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : (real_of_int _91911) = term214.
Proof. exact (proj2 (@lem6878522 _91911 _91912 h1)). Qed.
Lemma lem6878525 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term366 _91911 _91912.
Proof. exact (proj2 (@lem6878521 _91911 _91912 h1)). Qed.
Lemma lem6878526 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term360 _91911 _91912.
Proof. exact (proj1 (@lem6878521 _91911 _91912 h1)). Qed.
Lemma lem6878528 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6878529 : term551 = term331.
Proof. exact (@lem6878528 term214 term224). Qed.
Lemma lem6878531 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6878532 : term224 = term304.
Proof. exact (@lem6878531 term92). Qed.
Lemma lem6878534 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6878535 : term214 = term276.
Proof. exact (@lem6878534 (NUMERAL 0)). Qed.
Lemma lem6878536 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6878537 : term552 = term553.
Proof. exact (MK_COMB (@lem6878536) (@lem6878535)). Qed.
Lemma lem6878538 : term331 = term554.
Proof. exact (MK_COMB (@lem6878537) (@lem6878532)). Qed.
Lemma lem6878539 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6878541 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878542 : term331 = term332.
Proof. exact (@lem6878541 (NUMERAL 0) term92). Qed.
Lemma lem6878543 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878544 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878545 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878544 h1) (fun h1 : term332 = True => @lem6878543)). Qed.
Lemma lem6878546 : term332 = True.
Proof. exact (EQ_MP (@lem6878545) (@lem6878543)). Qed.
Lemma lem6878547 : term331 = True.
Proof. exact (TRANS (@lem6878542) (@lem6878546)). Qed.
Lemma lem6878548 : True = term331.
Proof. exact (SYM (@lem6878547)). Qed.
Lemma lem6878549 : term331.
Proof. exact (EQ_MP (@lem6878548) (@lem0)). Qed.
Lemma lem6878550 : term556.
Proof. exact (@lem6878539 (@lem6878549)). Qed.
Lemma lem6878552 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878553 : term331 = term332.
Proof. exact (@lem6878552 (NUMERAL 0) term92). Qed.
Lemma lem6878554 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878555 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878556 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878555 h1) (fun h1 : term332 = True => @lem6878554)). Qed.
Lemma lem6878557 : term332 = True.
Proof. exact (EQ_MP (@lem6878556) (@lem6878554)). Qed.
Lemma lem6878558 : term331 = True.
Proof. exact (TRANS (@lem6878553) (@lem6878557)). Qed.
Lemma lem6878559 : True = term331.
Proof. exact (SYM (@lem6878558)). Qed.
Lemma lem6878560 : term331.
Proof. exact (EQ_MP (@lem6878559) (@lem0)). Qed.
Lemma lem6878561 : term554 = term557.
Proof. exact (@lem6878550 (@lem6878560)). Qed.
Lemma lem6878563 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6878564 : term288 = term289.
Proof. exact (@lem6878563 term92 term92). Qed.
Lemma lem6878565 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878566 : term291 = term92.
Proof. exact (EQ_MP (@lem6878565) (@lem940073)). Qed.
Lemma lem6878567 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878568 : term289 = term224.
Proof. exact (MK_COMB (@lem6878567) (@lem6878566)). Qed.
Lemma lem6878569 : term288 = term224.
Proof. exact (TRANS (@lem6878564) (@lem6878568)). Qed.
Lemma lem6878571 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6878572 : term343 = term214.
Proof. exact (@lem6878571 term92). Qed.
Lemma lem6878573 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6878574 : term558 = term552.
Proof. exact (MK_COMB (@lem6878573) (@lem6878572)). Qed.
Lemma lem6878575 : term557 = term331.
Proof. exact (MK_COMB (@lem6878574) (@lem6878569)). Qed.
Lemma lem6878577 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878578 : term331 = term332.
Proof. exact (@lem6878577 (NUMERAL 0) term92). Qed.
Lemma lem6878579 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878580 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878581 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878580 h1) (fun h1 : term332 = True => @lem6878579)). Qed.
Lemma lem6878582 : term332 = True.
Proof. exact (EQ_MP (@lem6878581) (@lem6878579)). Qed.
Lemma lem6878583 : term331 = True.
Proof. exact (TRANS (@lem6878578) (@lem6878582)). Qed.
Lemma lem6878584 : term557 = True.
Proof. exact (TRANS (@lem6878575) (@lem6878583)). Qed.
Lemma lem6878585 : term554 = True.
Proof. exact (TRANS (@lem6878561) (@lem6878584)). Qed.
Lemma lem6878586 : term331 = True.
Proof. exact (TRANS (@lem6878538) (@lem6878585)). Qed.
Lemma lem6878587 : term551 = True.
Proof. exact (TRANS (@lem6878529) (@lem6878586)). Qed.
Lemma lem6878588 : True = term551.
Proof. exact (SYM (@lem6878587)). Qed.
Lemma lem6878589 : term551.
Proof. exact (EQ_MP (@lem6878588) (@lem0)). Qed.
Lemma lem6878590 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term615 _91911 _91912.
Proof. exact (conj (@lem6878589) (@lem6878525 _91911 _91912 h1)). Qed.
Lemma lem6878592 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6878593 (_91911 : int) (_91912 : int) : term616 _91911 _91912.
Proof. exact (@lem6878592 term224 (term316 _91911 _91912)). Qed.
Lemma lem6878594 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term617 _91911 _91912.
Proof. exact (@lem6878593 _91911 _91912 (@lem6878590 _91911 _91912 h1)). Qed.
Lemma lem6878595 (_91911 : int) (_91912 : int) : (term569 _91911 _91912) = (term316 _91911 _91912).
Proof. exact (@lem1982733 (term316 _91911 _91912)). Qed.
Lemma lem6878596 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6878597 (_91911 : int) (_91912 : int) : (term618 _91911 _91912) = (term365 _91911 _91912).
Proof. exact (MK_COMB (@lem6878596) (@lem6878595 _91911 _91912)). Qed.
Lemma lem6878598 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6878599 (_91911 : int) (_91912 : int) : (term617 _91911 _91912) = (term366 _91911 _91912).
Proof. exact (MK_COMB (@lem6878597 _91911 _91912) (@lem6878598)). Qed.
Lemma lem6878600 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term366 _91911 _91912.
Proof. exact (EQ_MP (@lem6878599 _91911 _91912) (@lem6878594 _91911 _91912 h1)). Qed.
Lemma lem6878602 (y : real) : term565 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6878603 (_91911 : int) : term619 _91911.
Proof. exact (@lem6878602 (real_of_int _91911)). Qed.
Lemma lem6878604 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term620 _91911.
Proof. exact (@lem6878603 _91911 (@lem6878523 _91911 _91912 h1)). Qed.
Lemma lem6878605 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term621 _91911.
Proof. exact (@lem6878604 _91911 _91912 h1 term224). Qed.
Lemma lem6878606 (_91911 : int) : (term621 _91911) = ((term622 _91911) = term214).
Proof. exact (eq_refl (term621 _91911)). Qed.
Lemma lem6878607 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : (term622 _91911) = term214.
Proof. exact (EQ_MP (@lem6878606 _91911) (@lem6878605 _91911 _91912 h1)). Qed.
Lemma lem6878608 (_91911 : int) : (term622 _91911) = (real_of_int _91911).
Proof. exact (@lem1982733 (real_of_int _91911)). Qed.
Lemma lem6878609 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6878610 (_91911 : int) : (term623 _91911) = (term227 _91911).
Proof. exact (MK_COMB (@lem6878609) (@lem6878608 _91911)). Qed.
Lemma lem6878611 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6878612 (_91911 : int) : ((term622 _91911) = term214) = ((real_of_int _91911) = term214).
Proof. exact (MK_COMB (@lem6878610 _91911) (@lem6878611)). Qed.
Lemma lem6878613 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : (real_of_int _91911) = term214.
Proof. exact (EQ_MP (@lem6878612 _91911) (@lem6878607 _91911 _91912 h1)). Qed.
Lemma lem6878614 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term624 _91911 _91912.
Proof. exact (conj (@lem6878613 _91911 _91912 h1) (@lem6878600 _91911 _91912 h1)). Qed.
Lemma lem6878616 (x : real) (y : real) : term572 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6878617 (_91911 : int) (_91912 : int) : term625 _91911 _91912.
Proof. exact (@lem6878616 (real_of_int _91911) (term316 _91911 _91912)). Qed.
Lemma lem6878618 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term626 _91911 _91912.
Proof. exact (@lem6878617 _91911 _91912 (@lem6878614 _91911 _91912 h1)). Qed.
Lemma lem6878619 (_91911 : int) (_91912 : int) : (term627 _91911 _91912) = (term628 _91911 _91912).
Proof. exact (@lem1982763 (real_of_int _91911) (term317 _91911) (term379 _91912)). Qed.
Lemma lem6878620 (_91911 : int) : (term597 _91911) = (term578 _91911).
Proof. exact (@lem1982715 term279 (real_of_int _91911)). Qed.
Lemma lem6878622 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6878623 : term224 = term304.
Proof. exact (@lem6878622 term92). Qed.
Lemma lem6878625 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6878626 : term279 = term280.
Proof. exact (@lem6878625 term92). Qed.
Lemma lem6878627 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6878628 : term579 = term580.
Proof. exact (MK_COMB (@lem6878627) (@lem6878626)). Qed.
Lemma lem6878629 : term581 = term582.
Proof. exact (MK_COMB (@lem6878628) (@lem6878623)). Qed.
Lemma lem6878630 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6878632 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878633 : term331 = term332.
Proof. exact (@lem6878632 (NUMERAL 0) term92). Qed.
Lemma lem6878634 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878635 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878636 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878635 h1) (fun h1 : term332 = True => @lem6878634)). Qed.
Lemma lem6878637 : term332 = True.
Proof. exact (EQ_MP (@lem6878636) (@lem6878634)). Qed.
Lemma lem6878638 : term331 = True.
Proof. exact (TRANS (@lem6878633) (@lem6878637)). Qed.
Lemma lem6878639 : True = term331.
Proof. exact (SYM (@lem6878638)). Qed.
Lemma lem6878640 : term331.
Proof. exact (EQ_MP (@lem6878639) (@lem0)). Qed.
Lemma lem6878641 : term584.
Proof. exact (@lem6878630 (@lem6878640)). Qed.
Lemma lem6878643 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878644 : term331 = term332.
Proof. exact (@lem6878643 (NUMERAL 0) term92). Qed.
Lemma lem6878645 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878646 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878647 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878646 h1) (fun h1 : term332 = True => @lem6878645)). Qed.
Lemma lem6878648 : term332 = True.
Proof. exact (EQ_MP (@lem6878647) (@lem6878645)). Qed.
Lemma lem6878649 : term331 = True.
Proof. exact (TRANS (@lem6878644) (@lem6878648)). Qed.
Lemma lem6878650 : True = term331.
Proof. exact (SYM (@lem6878649)). Qed.
Lemma lem6878651 : term331.
Proof. exact (EQ_MP (@lem6878650) (@lem0)). Qed.
Lemma lem6878652 : term585.
Proof. exact (@lem6878641 (@lem6878651)). Qed.
Lemma lem6878654 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878655 : term331 = term332.
Proof. exact (@lem6878654 (NUMERAL 0) term92). Qed.
Lemma lem6878656 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878657 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878658 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878657 h1) (fun h1 : term332 = True => @lem6878656)). Qed.
Lemma lem6878659 : term332 = True.
Proof. exact (EQ_MP (@lem6878658) (@lem6878656)). Qed.
Lemma lem6878660 : term331 = True.
Proof. exact (TRANS (@lem6878655) (@lem6878659)). Qed.
Lemma lem6878661 : True = term331.
Proof. exact (SYM (@lem6878660)). Qed.
Lemma lem6878662 : term331.
Proof. exact (EQ_MP (@lem6878661) (@lem0)). Qed.
Lemma lem6878663 : term586.
Proof. exact (@lem6878652 (@lem6878662)). Qed.
Lemma lem6878665 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6878666 : term288 = term289.
Proof. exact (@lem6878665 term92 term92). Qed.
Lemma lem6878667 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878668 : term291 = term92.
Proof. exact (EQ_MP (@lem6878667) (@lem940073)). Qed.
Lemma lem6878669 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878670 : term289 = term224.
Proof. exact (MK_COMB (@lem6878669) (@lem6878668)). Qed.
Lemma lem6878671 : term288 = term224.
Proof. exact (TRANS (@lem6878666) (@lem6878670)). Qed.
Lemma lem6878673 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6878674 : term305 = term310.
Proof. exact (@lem6878673 term92 term92). Qed.
Lemma lem6878675 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878676 : term291 = term92.
Proof. exact (EQ_MP (@lem6878675) (@lem940073)). Qed.
Lemma lem6878677 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878678 : term289 = term224.
Proof. exact (MK_COMB (@lem6878677) (@lem6878676)). Qed.
Lemma lem6878679 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6878680 : term310 = term279.
Proof. exact (MK_COMB (@lem6878679) (@lem6878678)). Qed.
Lemma lem6878681 : term305 = term279.
Proof. exact (TRANS (@lem6878674) (@lem6878680)). Qed.
Lemma lem6878682 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6878683 : term587 = term579.
Proof. exact (MK_COMB (@lem6878682) (@lem6878681)). Qed.
Lemma lem6878684 : term588 = term581.
Proof. exact (MK_COMB (@lem6878683) (@lem6878671)). Qed.
Lemma lem6878686 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6878687 : term581 = term214.
Proof. exact (@lem6878686 term92). Qed.
Lemma lem6878688 : term588 = term214.
Proof. exact (TRANS (@lem6878684) (@lem6878687)). Qed.
Lemma lem6878689 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6878690 : term590 = term341.
Proof. exact (MK_COMB (@lem6878689) (@lem6878688)). Qed.
Lemma lem6878691 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6878692 : term591 = term343.
Proof. exact (MK_COMB (@lem6878690) (@lem6878691)). Qed.
Lemma lem6878694 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6878695 : term343 = term214.
Proof. exact (@lem6878694 term92). Qed.
Lemma lem6878696 : term591 = term214.
Proof. exact (TRANS (@lem6878692) (@lem6878695)). Qed.
Lemma lem6878698 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6878699 : term288 = term289.
Proof. exact (@lem6878698 term92 term92). Qed.
Lemma lem6878700 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878701 : term291 = term92.
Proof. exact (EQ_MP (@lem6878700) (@lem940073)). Qed.
Lemma lem6878702 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878703 : term289 = term224.
Proof. exact (MK_COMB (@lem6878702) (@lem6878701)). Qed.
Lemma lem6878704 : term288 = term224.
Proof. exact (TRANS (@lem6878699) (@lem6878703)). Qed.
Lemma lem6878705 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6878706 : term345 = term343.
Proof. exact (MK_COMB (@lem6878705) (@lem6878704)). Qed.
Lemma lem6878708 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6878709 : term343 = term214.
Proof. exact (@lem6878708 term92). Qed.
Lemma lem6878710 : term345 = term214.
Proof. exact (TRANS (@lem6878706) (@lem6878709)). Qed.
Lemma lem6878711 : term214 = term345.
Proof. exact (SYM (@lem6878710)). Qed.
Lemma lem6878712 : term591 = term345.
Proof. exact (TRANS (@lem6878696) (@lem6878711)). Qed.
Lemma lem6878713 : term582 = term276.
Proof. exact (@lem6878663 (@lem6878712)). Qed.
Lemma lem6878714 : term581 = term276.
Proof. exact (TRANS (@lem6878629) (@lem6878713)). Qed.
Lemma lem6878716 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6878717 : term276 = term214.
Proof. exact (@lem6878716 term214). Qed.
Lemma lem6878718 : term581 = term214.
Proof. exact (TRANS (@lem6878714) (@lem6878717)). Qed.
Lemma lem6878719 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6878720 : term592 = term341.
Proof. exact (MK_COMB (@lem6878719) (@lem6878718)). Qed.
Lemma lem6878721 (_91911 : int) : (real_of_int _91911) = (real_of_int _91911).
Proof. exact (eq_refl (real_of_int _91911)). Qed.
Lemma lem6878722 (_91911 : int) : (term578 _91911) = (term593 _91911).
Proof. exact (MK_COMB (@lem6878720) (@lem6878721 _91911)). Qed.
Lemma lem6878723 (_91911 : int) : (term597 _91911) = (term593 _91911).
Proof. exact (TRANS (@lem6878620 _91911) (@lem6878722 _91911)). Qed.
Lemma lem6878724 (_91911 : int) : (term593 _91911) = term214.
Proof. exact (@lem1982719 (real_of_int _91911)). Qed.
Lemma lem6878725 (_91911 : int) : (term597 _91911) = term214.
Proof. exact (TRANS (@lem6878723 _91911) (@lem6878724 _91911)). Qed.
Lemma lem6878726 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6878727 (_91911 : int) : (term598 _91911) = term256.
Proof. exact (MK_COMB (@lem6878726) (@lem6878725 _91911)). Qed.
Lemma lem6878728 (_91912 : int) : (term379 _91912) = (term379 _91912).
Proof. exact (eq_refl (term379 _91912)). Qed.
Lemma lem6878729 (_91911 : int) (_91912 : int) : (term628 _91911 _91912) = (term629 _91912).
Proof. exact (MK_COMB (@lem6878727 _91911) (@lem6878728 _91912)). Qed.
Lemma lem6878730 (_91911 : int) (_91912 : int) : (term627 _91911 _91912) = (term629 _91912).
Proof. exact (TRANS (@lem6878619 _91911 _91912) (@lem6878729 _91911 _91912)). Qed.
Lemma lem6878731 (_91912 : int) : (term629 _91912) = (term379 _91912).
Proof. exact (@lem1982721 (term379 _91912)). Qed.
Lemma lem6878732 (_91911 : int) (_91912 : int) : (term627 _91911 _91912) = (term379 _91912).
Proof. exact (TRANS (@lem6878730 _91911 _91912) (@lem6878731 _91912)). Qed.
Lemma lem6878733 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6878734 (_91911 : int) (_91912 : int) : (term630 _91911 _91912) = (term381 _91912).
Proof. exact (MK_COMB (@lem6878733) (@lem6878732 _91911 _91912)). Qed.
Lemma lem6878735 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6878736 (_91911 : int) (_91912 : int) : (term626 _91911 _91912) = (term382 _91912).
Proof. exact (MK_COMB (@lem6878734 _91911 _91912) (@lem6878735)). Qed.
Lemma lem6878737 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term382 _91912.
Proof. exact (EQ_MP (@lem6878736 _91911 _91912) (@lem6878618 _91911 _91912 h1)). Qed.
Lemma lem6878739 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6878740 : term551 = term331.
Proof. exact (@lem6878739 term214 term224). Qed.
Lemma lem6878742 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6878743 : term224 = term304.
Proof. exact (@lem6878742 term92). Qed.
Lemma lem6878745 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6878746 : term214 = term276.
Proof. exact (@lem6878745 (NUMERAL 0)). Qed.
Lemma lem6878747 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6878748 : term552 = term553.
Proof. exact (MK_COMB (@lem6878747) (@lem6878746)). Qed.
Lemma lem6878749 : term331 = term554.
Proof. exact (MK_COMB (@lem6878748) (@lem6878743)). Qed.
Lemma lem6878750 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6878752 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878753 : term331 = term332.
Proof. exact (@lem6878752 (NUMERAL 0) term92). Qed.
Lemma lem6878754 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878755 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878756 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878755 h1) (fun h1 : term332 = True => @lem6878754)). Qed.
Lemma lem6878757 : term332 = True.
Proof. exact (EQ_MP (@lem6878756) (@lem6878754)). Qed.
Lemma lem6878758 : term331 = True.
Proof. exact (TRANS (@lem6878753) (@lem6878757)). Qed.
Lemma lem6878759 : True = term331.
Proof. exact (SYM (@lem6878758)). Qed.
Lemma lem6878760 : term331.
Proof. exact (EQ_MP (@lem6878759) (@lem0)). Qed.
Lemma lem6878761 : term556.
Proof. exact (@lem6878750 (@lem6878760)). Qed.
Lemma lem6878763 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878764 : term331 = term332.
Proof. exact (@lem6878763 (NUMERAL 0) term92). Qed.
Lemma lem6878765 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878766 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878767 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878766 h1) (fun h1 : term332 = True => @lem6878765)). Qed.
Lemma lem6878768 : term332 = True.
Proof. exact (EQ_MP (@lem6878767) (@lem6878765)). Qed.
Lemma lem6878769 : term331 = True.
Proof. exact (TRANS (@lem6878764) (@lem6878768)). Qed.
Lemma lem6878770 : True = term331.
Proof. exact (SYM (@lem6878769)). Qed.
Lemma lem6878771 : term331.
Proof. exact (EQ_MP (@lem6878770) (@lem0)). Qed.
Lemma lem6878772 : term554 = term557.
Proof. exact (@lem6878761 (@lem6878771)). Qed.
Lemma lem6878774 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6878775 : term288 = term289.
Proof. exact (@lem6878774 term92 term92). Qed.
Lemma lem6878776 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878777 : term291 = term92.
Proof. exact (EQ_MP (@lem6878776) (@lem940073)). Qed.
Lemma lem6878778 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878779 : term289 = term224.
Proof. exact (MK_COMB (@lem6878778) (@lem6878777)). Qed.
Lemma lem6878780 : term288 = term224.
Proof. exact (TRANS (@lem6878775) (@lem6878779)). Qed.
Lemma lem6878782 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6878783 : term343 = term214.
Proof. exact (@lem6878782 term92). Qed.
Lemma lem6878784 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6878785 : term558 = term552.
Proof. exact (MK_COMB (@lem6878784) (@lem6878783)). Qed.
Lemma lem6878786 : term557 = term331.
Proof. exact (MK_COMB (@lem6878785) (@lem6878780)). Qed.
Lemma lem6878788 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878789 : term331 = term332.
Proof. exact (@lem6878788 (NUMERAL 0) term92). Qed.
Lemma lem6878790 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878791 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878792 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878791 h1) (fun h1 : term332 = True => @lem6878790)). Qed.
Lemma lem6878793 : term332 = True.
Proof. exact (EQ_MP (@lem6878792) (@lem6878790)). Qed.
Lemma lem6878794 : term331 = True.
Proof. exact (TRANS (@lem6878789) (@lem6878793)). Qed.
Lemma lem6878795 : term557 = True.
Proof. exact (TRANS (@lem6878786) (@lem6878794)). Qed.
Lemma lem6878796 : term554 = True.
Proof. exact (TRANS (@lem6878772) (@lem6878795)). Qed.
Lemma lem6878797 : term331 = True.
Proof. exact (TRANS (@lem6878749) (@lem6878796)). Qed.
Lemma lem6878798 : term551 = True.
Proof. exact (TRANS (@lem6878740) (@lem6878797)). Qed.
Lemma lem6878799 : True = term551.
Proof. exact (SYM (@lem6878798)). Qed.
Lemma lem6878800 : term551.
Proof. exact (EQ_MP (@lem6878799) (@lem0)). Qed.
Lemma lem6878801 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term631 _91912.
Proof. exact (conj (@lem6878800) (@lem6878737 _91911 _91912 h1)). Qed.
Lemma lem6878803 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6878804 (_91912 : int) : term632 _91912.
Proof. exact (@lem6878803 term224 (term379 _91912)). Qed.
Lemma lem6878805 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term633 _91912.
Proof. exact (@lem6878804 _91912 (@lem6878801 _91911 _91912 h1)). Qed.
Lemma lem6878806 (_91912 : int) : (term634 _91912) = (term379 _91912).
Proof. exact (@lem1982733 (term379 _91912)). Qed.
Lemma lem6878807 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6878808 (_91912 : int) : (term635 _91912) = (term381 _91912).
Proof. exact (MK_COMB (@lem6878807) (@lem6878806 _91912)). Qed.
Lemma lem6878809 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6878810 (_91912 : int) : (term633 _91912) = (term382 _91912).
Proof. exact (MK_COMB (@lem6878808 _91912) (@lem6878809)). Qed.
Lemma lem6878811 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term382 _91912.
Proof. exact (EQ_MP (@lem6878810 _91912) (@lem6878805 _91911 _91912 h1)). Qed.
Lemma lem6878813 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6878814 : term551 = term331.
Proof. exact (@lem6878813 term214 term224). Qed.
Lemma lem6878816 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6878817 : term224 = term304.
Proof. exact (@lem6878816 term92). Qed.
Lemma lem6878819 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6878820 : term214 = term276.
Proof. exact (@lem6878819 (NUMERAL 0)). Qed.
Lemma lem6878821 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6878822 : term552 = term553.
Proof. exact (MK_COMB (@lem6878821) (@lem6878820)). Qed.
Lemma lem6878823 : term331 = term554.
Proof. exact (MK_COMB (@lem6878822) (@lem6878817)). Qed.
Lemma lem6878824 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6878826 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878827 : term331 = term332.
Proof. exact (@lem6878826 (NUMERAL 0) term92). Qed.
Lemma lem6878828 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878829 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878830 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878829 h1) (fun h1 : term332 = True => @lem6878828)). Qed.
Lemma lem6878831 : term332 = True.
Proof. exact (EQ_MP (@lem6878830) (@lem6878828)). Qed.
Lemma lem6878832 : term331 = True.
Proof. exact (TRANS (@lem6878827) (@lem6878831)). Qed.
Lemma lem6878833 : True = term331.
Proof. exact (SYM (@lem6878832)). Qed.
Lemma lem6878834 : term331.
Proof. exact (EQ_MP (@lem6878833) (@lem0)). Qed.
Lemma lem6878835 : term556.
Proof. exact (@lem6878824 (@lem6878834)). Qed.
Lemma lem6878837 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878838 : term331 = term332.
Proof. exact (@lem6878837 (NUMERAL 0) term92). Qed.
Lemma lem6878839 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878840 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878841 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878840 h1) (fun h1 : term332 = True => @lem6878839)). Qed.
Lemma lem6878842 : term332 = True.
Proof. exact (EQ_MP (@lem6878841) (@lem6878839)). Qed.
Lemma lem6878843 : term331 = True.
Proof. exact (TRANS (@lem6878838) (@lem6878842)). Qed.
Lemma lem6878844 : True = term331.
Proof. exact (SYM (@lem6878843)). Qed.
Lemma lem6878845 : term331.
Proof. exact (EQ_MP (@lem6878844) (@lem0)). Qed.
Lemma lem6878846 : term554 = term557.
Proof. exact (@lem6878835 (@lem6878845)). Qed.
Lemma lem6878848 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6878849 : term288 = term289.
Proof. exact (@lem6878848 term92 term92). Qed.
Lemma lem6878850 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878851 : term291 = term92.
Proof. exact (EQ_MP (@lem6878850) (@lem940073)). Qed.
Lemma lem6878852 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878853 : term289 = term224.
Proof. exact (MK_COMB (@lem6878852) (@lem6878851)). Qed.
Lemma lem6878854 : term288 = term224.
Proof. exact (TRANS (@lem6878849) (@lem6878853)). Qed.
Lemma lem6878856 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6878857 : term343 = term214.
Proof. exact (@lem6878856 term92). Qed.
Lemma lem6878858 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6878859 : term558 = term552.
Proof. exact (MK_COMB (@lem6878858) (@lem6878857)). Qed.
Lemma lem6878860 : term557 = term331.
Proof. exact (MK_COMB (@lem6878859) (@lem6878854)). Qed.
Lemma lem6878862 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878863 : term331 = term332.
Proof. exact (@lem6878862 (NUMERAL 0) term92). Qed.
Lemma lem6878864 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878865 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878866 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878865 h1) (fun h1 : term332 = True => @lem6878864)). Qed.
Lemma lem6878867 : term332 = True.
Proof. exact (EQ_MP (@lem6878866) (@lem6878864)). Qed.
Lemma lem6878868 : term331 = True.
Proof. exact (TRANS (@lem6878863) (@lem6878867)). Qed.
Lemma lem6878869 : term557 = True.
Proof. exact (TRANS (@lem6878860) (@lem6878868)). Qed.
Lemma lem6878870 : term554 = True.
Proof. exact (TRANS (@lem6878846) (@lem6878869)). Qed.
Lemma lem6878871 : term331 = True.
Proof. exact (TRANS (@lem6878823) (@lem6878870)). Qed.
Lemma lem6878872 : term551 = True.
Proof. exact (TRANS (@lem6878814) (@lem6878871)). Qed.
Lemma lem6878873 : True = term551.
Proof. exact (SYM (@lem6878872)). Qed.
Lemma lem6878874 : term551.
Proof. exact (EQ_MP (@lem6878873) (@lem0)). Qed.
Lemma lem6878875 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term559 _91911 _91912.
Proof. exact (conj (@lem6878874) (@lem6878526 _91911 _91912 h1)). Qed.
Lemma lem6878877 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6878878 (_91911 : int) (_91912 : int) : term561 _91911 _91912.
Proof. exact (@lem6878877 term224 (term357 _91911 _91912)). Qed.
Lemma lem6878879 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term562 _91911 _91912.
Proof. exact (@lem6878878 _91911 _91912 (@lem6878875 _91911 _91912 h1)). Qed.
Lemma lem6878880 (_91911 : int) (_91912 : int) : (term563 _91911 _91912) = (term357 _91911 _91912).
Proof. exact (@lem1982733 (term357 _91911 _91912)). Qed.
Lemma lem6878881 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6878882 (_91911 : int) (_91912 : int) : (term564 _91911 _91912) = (term359 _91911 _91912).
Proof. exact (MK_COMB (@lem6878881) (@lem6878880 _91911 _91912)). Qed.
Lemma lem6878883 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6878884 (_91911 : int) (_91912 : int) : (term562 _91911 _91912) = (term360 _91911 _91912).
Proof. exact (MK_COMB (@lem6878882 _91911 _91912) (@lem6878883)). Qed.
Lemma lem6878885 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term360 _91911 _91912.
Proof. exact (EQ_MP (@lem6878884 _91911 _91912) (@lem6878879 _91911 _91912 h1)). Qed.
Lemma lem6878887 (y : real) : term565 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6878888 (_91911 : int) : term619 _91911.
Proof. exact (@lem6878887 (real_of_int _91911)). Qed.
Lemma lem6878889 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term620 _91911.
Proof. exact (@lem6878888 _91911 (@lem6878523 _91911 _91912 h1)). Qed.
Lemma lem6878890 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term636 _91911.
Proof. exact (@lem6878889 _91911 _91912 h1 term279). Qed.
Lemma lem6878891 (_91911 : int) : (term636 _91911) = ((term317 _91911) = term214).
Proof. exact (eq_refl (term636 _91911)). Qed.
Lemma lem6878898 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : (term317 _91911) = term214.
Proof. exact (EQ_MP (@lem6878891 _91911) (@lem6878890 _91911 _91912 h1)). Qed.
Lemma lem6878899 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term637 _91911 _91912.
Proof. exact (conj (@lem6878898 _91911 _91912 h1) (@lem6878885 _91911 _91912 h1)). Qed.
Lemma lem6878901 (x : real) (y : real) : term572 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6878902 (_91911 : int) (_91912 : int) : term638 _91911 _91912.
Proof. exact (@lem6878901 (term317 _91911) (term357 _91911 _91912)). Qed.
Lemma lem6878903 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term639 _91911 _91912.
Proof. exact (@lem6878902 _91911 _91912 (@lem6878899 _91911 _91912 h1)). Qed.
Lemma lem6878904 (_91911 : int) (_91912 : int) : (term640 _91911 _91912) = (term641 _91911 _91912).
Proof. exact (@lem1982763 (term317 _91911) (real_of_int _91911) (term317 _91912)). Qed.
Lemma lem6878905 (_91911 : int) : (term577 _91911) = (term578 _91911).
Proof. exact (@lem1982713 term279 (real_of_int _91911)). Qed.
Lemma lem6878907 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6878908 : term224 = term304.
Proof. exact (@lem6878907 term92). Qed.
Lemma lem6878910 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6878911 : term279 = term280.
Proof. exact (@lem6878910 term92). Qed.
Lemma lem6878912 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6878913 : term579 = term580.
Proof. exact (MK_COMB (@lem6878912) (@lem6878911)). Qed.
Lemma lem6878914 : term581 = term582.
Proof. exact (MK_COMB (@lem6878913) (@lem6878908)). Qed.
Lemma lem6878915 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6878917 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878918 : term331 = term332.
Proof. exact (@lem6878917 (NUMERAL 0) term92). Qed.
Lemma lem6878919 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878920 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878921 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878920 h1) (fun h1 : term332 = True => @lem6878919)). Qed.
Lemma lem6878922 : term332 = True.
Proof. exact (EQ_MP (@lem6878921) (@lem6878919)). Qed.
Lemma lem6878923 : term331 = True.
Proof. exact (TRANS (@lem6878918) (@lem6878922)). Qed.
Lemma lem6878924 : True = term331.
Proof. exact (SYM (@lem6878923)). Qed.
Lemma lem6878925 : term331.
Proof. exact (EQ_MP (@lem6878924) (@lem0)). Qed.
Lemma lem6878926 : term584.
Proof. exact (@lem6878915 (@lem6878925)). Qed.
Lemma lem6878928 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878929 : term331 = term332.
Proof. exact (@lem6878928 (NUMERAL 0) term92). Qed.
Lemma lem6878930 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878931 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878932 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878931 h1) (fun h1 : term332 = True => @lem6878930)). Qed.
Lemma lem6878933 : term332 = True.
Proof. exact (EQ_MP (@lem6878932) (@lem6878930)). Qed.
Lemma lem6878934 : term331 = True.
Proof. exact (TRANS (@lem6878929) (@lem6878933)). Qed.
Lemma lem6878935 : True = term331.
Proof. exact (SYM (@lem6878934)). Qed.
Lemma lem6878936 : term331.
Proof. exact (EQ_MP (@lem6878935) (@lem0)). Qed.
Lemma lem6878937 : term585.
Proof. exact (@lem6878926 (@lem6878936)). Qed.
Lemma lem6878939 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6878940 : term331 = term332.
Proof. exact (@lem6878939 (NUMERAL 0) term92). Qed.
Lemma lem6878941 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6878942 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6878943 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6878942 h1) (fun h1 : term332 = True => @lem6878941)). Qed.
Lemma lem6878944 : term332 = True.
Proof. exact (EQ_MP (@lem6878943) (@lem6878941)). Qed.
Lemma lem6878945 : term331 = True.
Proof. exact (TRANS (@lem6878940) (@lem6878944)). Qed.
Lemma lem6878946 : True = term331.
Proof. exact (SYM (@lem6878945)). Qed.
Lemma lem6878947 : term331.
Proof. exact (EQ_MP (@lem6878946) (@lem0)). Qed.
Lemma lem6878948 : term586.
Proof. exact (@lem6878937 (@lem6878947)). Qed.
Lemma lem6878950 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6878951 : term288 = term289.
Proof. exact (@lem6878950 term92 term92). Qed.
Lemma lem6878952 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878953 : term291 = term92.
Proof. exact (EQ_MP (@lem6878952) (@lem940073)). Qed.
Lemma lem6878954 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878955 : term289 = term224.
Proof. exact (MK_COMB (@lem6878954) (@lem6878953)). Qed.
Lemma lem6878956 : term288 = term224.
Proof. exact (TRANS (@lem6878951) (@lem6878955)). Qed.
Lemma lem6878958 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6878959 : term305 = term310.
Proof. exact (@lem6878958 term92 term92). Qed.
Lemma lem6878960 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878961 : term291 = term92.
Proof. exact (EQ_MP (@lem6878960) (@lem940073)). Qed.
Lemma lem6878962 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878963 : term289 = term224.
Proof. exact (MK_COMB (@lem6878962) (@lem6878961)). Qed.
Lemma lem6878964 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6878965 : term310 = term279.
Proof. exact (MK_COMB (@lem6878964) (@lem6878963)). Qed.
Lemma lem6878966 : term305 = term279.
Proof. exact (TRANS (@lem6878959) (@lem6878965)). Qed.
Lemma lem6878967 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6878968 : term587 = term579.
Proof. exact (MK_COMB (@lem6878967) (@lem6878966)). Qed.
Lemma lem6878969 : term588 = term581.
Proof. exact (MK_COMB (@lem6878968) (@lem6878956)). Qed.
Lemma lem6878971 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6878972 : term581 = term214.
Proof. exact (@lem6878971 term92). Qed.
Lemma lem6878973 : term588 = term214.
Proof. exact (TRANS (@lem6878969) (@lem6878972)). Qed.
Lemma lem6878974 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6878975 : term590 = term341.
Proof. exact (MK_COMB (@lem6878974) (@lem6878973)). Qed.
Lemma lem6878976 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6878977 : term591 = term343.
Proof. exact (MK_COMB (@lem6878975) (@lem6878976)). Qed.
Lemma lem6878979 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6878980 : term343 = term214.
Proof. exact (@lem6878979 term92). Qed.
Lemma lem6878981 : term591 = term214.
Proof. exact (TRANS (@lem6878977) (@lem6878980)). Qed.
Lemma lem6878983 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6878984 : term288 = term289.
Proof. exact (@lem6878983 term92 term92). Qed.
Lemma lem6878985 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6878986 : term291 = term92.
Proof. exact (EQ_MP (@lem6878985) (@lem940073)). Qed.
Lemma lem6878987 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6878988 : term289 = term224.
Proof. exact (MK_COMB (@lem6878987) (@lem6878986)). Qed.
Lemma lem6878989 : term288 = term224.
Proof. exact (TRANS (@lem6878984) (@lem6878988)). Qed.
Lemma lem6878990 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6878991 : term345 = term343.
Proof. exact (MK_COMB (@lem6878990) (@lem6878989)). Qed.
Lemma lem6878993 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6878994 : term343 = term214.
Proof. exact (@lem6878993 term92). Qed.
Lemma lem6878995 : term345 = term214.
Proof. exact (TRANS (@lem6878991) (@lem6878994)). Qed.
Lemma lem6878996 : term214 = term345.
Proof. exact (SYM (@lem6878995)). Qed.
Lemma lem6878997 : term591 = term345.
Proof. exact (TRANS (@lem6878981) (@lem6878996)). Qed.
Lemma lem6878998 : term582 = term276.
Proof. exact (@lem6878948 (@lem6878997)). Qed.
Lemma lem6878999 : term581 = term276.
Proof. exact (TRANS (@lem6878914) (@lem6878998)). Qed.
Lemma lem6879001 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6879002 : term276 = term214.
Proof. exact (@lem6879001 term214). Qed.
Lemma lem6879003 : term581 = term214.
Proof. exact (TRANS (@lem6878999) (@lem6879002)). Qed.
Lemma lem6879004 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6879005 : term592 = term341.
Proof. exact (MK_COMB (@lem6879004) (@lem6879003)). Qed.
Lemma lem6879006 (_91911 : int) : (real_of_int _91911) = (real_of_int _91911).
Proof. exact (eq_refl (real_of_int _91911)). Qed.
Lemma lem6879007 (_91911 : int) : (term578 _91911) = (term593 _91911).
Proof. exact (MK_COMB (@lem6879005) (@lem6879006 _91911)). Qed.
Lemma lem6879008 (_91911 : int) : (term577 _91911) = (term593 _91911).
Proof. exact (TRANS (@lem6878905 _91911) (@lem6879007 _91911)). Qed.
Lemma lem6879009 (_91911 : int) : (term593 _91911) = term214.
Proof. exact (@lem1982719 (real_of_int _91911)). Qed.
Lemma lem6879010 (_91911 : int) : (term577 _91911) = term214.
Proof. exact (TRANS (@lem6879008 _91911) (@lem6879009 _91911)). Qed.
Lemma lem6879011 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6879012 (_91911 : int) : (term594 _91911) = term256.
Proof. exact (MK_COMB (@lem6879011) (@lem6879010 _91911)). Qed.
Lemma lem6879013 (_91912 : int) : (term317 _91912) = (term317 _91912).
Proof. exact (eq_refl (term317 _91912)). Qed.
Lemma lem6879014 (_91911 : int) (_91912 : int) : (term641 _91911 _91912) = (term642 _91912).
Proof. exact (MK_COMB (@lem6879012 _91911) (@lem6879013 _91912)). Qed.
Lemma lem6879015 (_91911 : int) (_91912 : int) : (term640 _91911 _91912) = (term642 _91912).
Proof. exact (TRANS (@lem6878904 _91911 _91912) (@lem6879014 _91911 _91912)). Qed.
Lemma lem6879016 (_91912 : int) : (term642 _91912) = (term317 _91912).
Proof. exact (@lem1982721 (term317 _91912)). Qed.
Lemma lem6879017 (_91911 : int) (_91912 : int) : (term640 _91911 _91912) = (term317 _91912).
Proof. exact (TRANS (@lem6879015 _91911 _91912) (@lem6879016 _91912)). Qed.
Lemma lem6879018 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6879019 (_91911 : int) (_91912 : int) : (term643 _91911 _91912) = (term348 _91912).
Proof. exact (MK_COMB (@lem6879018) (@lem6879017 _91911 _91912)). Qed.
Lemma lem6879020 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6879021 (_91911 : int) (_91912 : int) : (term639 _91911 _91912) = (term349 _91912).
Proof. exact (MK_COMB (@lem6879019 _91911 _91912) (@lem6879020)). Qed.
Lemma lem6879022 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term349 _91912.
Proof. exact (EQ_MP (@lem6879021 _91911 _91912) (@lem6878903 _91911 _91912 h1)). Qed.
Lemma lem6879024 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6879025 : term551 = term331.
Proof. exact (@lem6879024 term214 term224). Qed.
Lemma lem6879027 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6879028 : term224 = term304.
Proof. exact (@lem6879027 term92). Qed.
Lemma lem6879030 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6879031 : term214 = term276.
Proof. exact (@lem6879030 (NUMERAL 0)). Qed.
Lemma lem6879032 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6879033 : term552 = term553.
Proof. exact (MK_COMB (@lem6879032) (@lem6879031)). Qed.
Lemma lem6879034 : term331 = term554.
Proof. exact (MK_COMB (@lem6879033) (@lem6879028)). Qed.
Lemma lem6879035 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6879037 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879038 : term331 = term332.
Proof. exact (@lem6879037 (NUMERAL 0) term92). Qed.
Lemma lem6879039 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879040 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879041 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879040 h1) (fun h1 : term332 = True => @lem6879039)). Qed.
Lemma lem6879042 : term332 = True.
Proof. exact (EQ_MP (@lem6879041) (@lem6879039)). Qed.
Lemma lem6879043 : term331 = True.
Proof. exact (TRANS (@lem6879038) (@lem6879042)). Qed.
Lemma lem6879044 : True = term331.
Proof. exact (SYM (@lem6879043)). Qed.
Lemma lem6879045 : term331.
Proof. exact (EQ_MP (@lem6879044) (@lem0)). Qed.
Lemma lem6879046 : term556.
Proof. exact (@lem6879035 (@lem6879045)). Qed.
Lemma lem6879048 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879049 : term331 = term332.
Proof. exact (@lem6879048 (NUMERAL 0) term92). Qed.
Lemma lem6879050 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879051 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879052 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879051 h1) (fun h1 : term332 = True => @lem6879050)). Qed.
Lemma lem6879053 : term332 = True.
Proof. exact (EQ_MP (@lem6879052) (@lem6879050)). Qed.
Lemma lem6879054 : term331 = True.
Proof. exact (TRANS (@lem6879049) (@lem6879053)). Qed.
Lemma lem6879055 : True = term331.
Proof. exact (SYM (@lem6879054)). Qed.
Lemma lem6879056 : term331.
Proof. exact (EQ_MP (@lem6879055) (@lem0)). Qed.
Lemma lem6879057 : term554 = term557.
Proof. exact (@lem6879046 (@lem6879056)). Qed.
Lemma lem6879059 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6879060 : term288 = term289.
Proof. exact (@lem6879059 term92 term92). Qed.
Lemma lem6879061 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879062 : term291 = term92.
Proof. exact (EQ_MP (@lem6879061) (@lem940073)). Qed.
Lemma lem6879063 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879064 : term289 = term224.
Proof. exact (MK_COMB (@lem6879063) (@lem6879062)). Qed.
Lemma lem6879065 : term288 = term224.
Proof. exact (TRANS (@lem6879060) (@lem6879064)). Qed.
Lemma lem6879067 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6879068 : term343 = term214.
Proof. exact (@lem6879067 term92). Qed.
Lemma lem6879069 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6879070 : term558 = term552.
Proof. exact (MK_COMB (@lem6879069) (@lem6879068)). Qed.
Lemma lem6879071 : term557 = term331.
Proof. exact (MK_COMB (@lem6879070) (@lem6879065)). Qed.
Lemma lem6879073 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879074 : term331 = term332.
Proof. exact (@lem6879073 (NUMERAL 0) term92). Qed.
Lemma lem6879075 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879076 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879077 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879076 h1) (fun h1 : term332 = True => @lem6879075)). Qed.
Lemma lem6879078 : term332 = True.
Proof. exact (EQ_MP (@lem6879077) (@lem6879075)). Qed.
Lemma lem6879079 : term331 = True.
Proof. exact (TRANS (@lem6879074) (@lem6879078)). Qed.
Lemma lem6879080 : term557 = True.
Proof. exact (TRANS (@lem6879071) (@lem6879079)). Qed.
Lemma lem6879081 : term554 = True.
Proof. exact (TRANS (@lem6879057) (@lem6879080)). Qed.
Lemma lem6879082 : term331 = True.
Proof. exact (TRANS (@lem6879034) (@lem6879081)). Qed.
Lemma lem6879083 : term551 = True.
Proof. exact (TRANS (@lem6879025) (@lem6879082)). Qed.
Lemma lem6879084 : True = term551.
Proof. exact (SYM (@lem6879083)). Qed.
Lemma lem6879085 : term551.
Proof. exact (EQ_MP (@lem6879084) (@lem0)). Qed.
Lemma lem6879086 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term644 _91912.
Proof. exact (conj (@lem6879085) (@lem6879022 _91911 _91912 h1)). Qed.
Lemma lem6879088 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6879089 (_91912 : int) : term645 _91912.
Proof. exact (@lem6879088 term224 (term317 _91912)). Qed.
Lemma lem6879090 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term646 _91912.
Proof. exact (@lem6879089 _91912 (@lem6879086 _91911 _91912 h1)). Qed.
Lemma lem6879091 (_91912 : int) : (term647 _91912) = (term317 _91912).
Proof. exact (@lem1982733 (term317 _91912)). Qed.
Lemma lem6879092 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6879093 (_91912 : int) : (term648 _91912) = (term348 _91912).
Proof. exact (MK_COMB (@lem6879092) (@lem6879091 _91912)). Qed.
Lemma lem6879094 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6879095 (_91912 : int) : (term646 _91912) = (term349 _91912).
Proof. exact (MK_COMB (@lem6879093 _91912) (@lem6879094)). Qed.
Lemma lem6879096 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term349 _91912.
Proof. exact (EQ_MP (@lem6879095 _91912) (@lem6879090 _91911 _91912 h1)). Qed.
Lemma lem6879097 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term649 _91912.
Proof. exact (conj (@lem6879096 _91911 _91912 h1) (@lem6878811 _91911 _91912 h1)). Qed.
Lemma lem6879099 (x : real) (y : real) : term650 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6879100 (_91912 : int) : term651 _91912.
Proof. exact (@lem6879099 (term317 _91912) (term379 _91912)). Qed.
Lemma lem6879101 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term652 _91912.
Proof. exact (@lem6879100 _91912 (@lem6879097 _91911 _91912 h1)). Qed.
Lemma lem6879102 (_91912 : int) : (term653 _91912) = (term654 _91912).
Proof. exact (@lem1982763 (term317 _91912) (real_of_int _91912) term279). Qed.
Lemma lem6879103 (_91912 : int) : (term577 _91912) = (term578 _91912).
Proof. exact (@lem1982713 term279 (real_of_int _91912)). Qed.
Lemma lem6879105 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6879106 : term224 = term304.
Proof. exact (@lem6879105 term92). Qed.
Lemma lem6879108 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6879109 : term279 = term280.
Proof. exact (@lem6879108 term92). Qed.
Lemma lem6879110 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6879111 : term579 = term580.
Proof. exact (MK_COMB (@lem6879110) (@lem6879109)). Qed.
Lemma lem6879112 : term581 = term582.
Proof. exact (MK_COMB (@lem6879111) (@lem6879106)). Qed.
Lemma lem6879113 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6879115 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879116 : term331 = term332.
Proof. exact (@lem6879115 (NUMERAL 0) term92). Qed.
Lemma lem6879117 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879118 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879119 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879118 h1) (fun h1 : term332 = True => @lem6879117)). Qed.
Lemma lem6879120 : term332 = True.
Proof. exact (EQ_MP (@lem6879119) (@lem6879117)). Qed.
Lemma lem6879121 : term331 = True.
Proof. exact (TRANS (@lem6879116) (@lem6879120)). Qed.
Lemma lem6879122 : True = term331.
Proof. exact (SYM (@lem6879121)). Qed.
Lemma lem6879123 : term331.
Proof. exact (EQ_MP (@lem6879122) (@lem0)). Qed.
Lemma lem6879124 : term584.
Proof. exact (@lem6879113 (@lem6879123)). Qed.
Lemma lem6879126 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879127 : term331 = term332.
Proof. exact (@lem6879126 (NUMERAL 0) term92). Qed.
Lemma lem6879128 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879129 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879130 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879129 h1) (fun h1 : term332 = True => @lem6879128)). Qed.
Lemma lem6879131 : term332 = True.
Proof. exact (EQ_MP (@lem6879130) (@lem6879128)). Qed.
Lemma lem6879132 : term331 = True.
Proof. exact (TRANS (@lem6879127) (@lem6879131)). Qed.
Lemma lem6879133 : True = term331.
Proof. exact (SYM (@lem6879132)). Qed.
Lemma lem6879134 : term331.
Proof. exact (EQ_MP (@lem6879133) (@lem0)). Qed.
Lemma lem6879135 : term585.
Proof. exact (@lem6879124 (@lem6879134)). Qed.
Lemma lem6879137 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879138 : term331 = term332.
Proof. exact (@lem6879137 (NUMERAL 0) term92). Qed.
Lemma lem6879139 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879140 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879141 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879140 h1) (fun h1 : term332 = True => @lem6879139)). Qed.
Lemma lem6879142 : term332 = True.
Proof. exact (EQ_MP (@lem6879141) (@lem6879139)). Qed.
Lemma lem6879143 : term331 = True.
Proof. exact (TRANS (@lem6879138) (@lem6879142)). Qed.
Lemma lem6879144 : True = term331.
Proof. exact (SYM (@lem6879143)). Qed.
Lemma lem6879145 : term331.
Proof. exact (EQ_MP (@lem6879144) (@lem0)). Qed.
Lemma lem6879146 : term586.
Proof. exact (@lem6879135 (@lem6879145)). Qed.
Lemma lem6879148 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6879149 : term288 = term289.
Proof. exact (@lem6879148 term92 term92). Qed.
Lemma lem6879150 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879151 : term291 = term92.
Proof. exact (EQ_MP (@lem6879150) (@lem940073)). Qed.
Lemma lem6879152 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879153 : term289 = term224.
Proof. exact (MK_COMB (@lem6879152) (@lem6879151)). Qed.
Lemma lem6879154 : term288 = term224.
Proof. exact (TRANS (@lem6879149) (@lem6879153)). Qed.
Lemma lem6879156 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6879157 : term305 = term310.
Proof. exact (@lem6879156 term92 term92). Qed.
Lemma lem6879158 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879159 : term291 = term92.
Proof. exact (EQ_MP (@lem6879158) (@lem940073)). Qed.
Lemma lem6879160 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879161 : term289 = term224.
Proof. exact (MK_COMB (@lem6879160) (@lem6879159)). Qed.
Lemma lem6879162 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6879163 : term310 = term279.
Proof. exact (MK_COMB (@lem6879162) (@lem6879161)). Qed.
Lemma lem6879164 : term305 = term279.
Proof. exact (TRANS (@lem6879157) (@lem6879163)). Qed.
Lemma lem6879165 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6879166 : term587 = term579.
Proof. exact (MK_COMB (@lem6879165) (@lem6879164)). Qed.
Lemma lem6879167 : term588 = term581.
Proof. exact (MK_COMB (@lem6879166) (@lem6879154)). Qed.
Lemma lem6879169 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6879170 : term581 = term214.
Proof. exact (@lem6879169 term92). Qed.
Lemma lem6879171 : term588 = term214.
Proof. exact (TRANS (@lem6879167) (@lem6879170)). Qed.
Lemma lem6879172 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6879173 : term590 = term341.
Proof. exact (MK_COMB (@lem6879172) (@lem6879171)). Qed.
Lemma lem6879174 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6879175 : term591 = term343.
Proof. exact (MK_COMB (@lem6879173) (@lem6879174)). Qed.
Lemma lem6879177 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6879178 : term343 = term214.
Proof. exact (@lem6879177 term92). Qed.
Lemma lem6879179 : term591 = term214.
Proof. exact (TRANS (@lem6879175) (@lem6879178)). Qed.
Lemma lem6879181 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6879182 : term288 = term289.
Proof. exact (@lem6879181 term92 term92). Qed.
Lemma lem6879183 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879184 : term291 = term92.
Proof. exact (EQ_MP (@lem6879183) (@lem940073)). Qed.
Lemma lem6879185 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879186 : term289 = term224.
Proof. exact (MK_COMB (@lem6879185) (@lem6879184)). Qed.
Lemma lem6879187 : term288 = term224.
Proof. exact (TRANS (@lem6879182) (@lem6879186)). Qed.
Lemma lem6879188 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6879189 : term345 = term343.
Proof. exact (MK_COMB (@lem6879188) (@lem6879187)). Qed.
Lemma lem6879191 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6879192 : term343 = term214.
Proof. exact (@lem6879191 term92). Qed.
Lemma lem6879193 : term345 = term214.
Proof. exact (TRANS (@lem6879189) (@lem6879192)). Qed.
Lemma lem6879194 : term214 = term345.
Proof. exact (SYM (@lem6879193)). Qed.
Lemma lem6879195 : term591 = term345.
Proof. exact (TRANS (@lem6879179) (@lem6879194)). Qed.
Lemma lem6879196 : term582 = term276.
Proof. exact (@lem6879146 (@lem6879195)). Qed.
Lemma lem6879197 : term581 = term276.
Proof. exact (TRANS (@lem6879112) (@lem6879196)). Qed.
Lemma lem6879199 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6879200 : term276 = term214.
Proof. exact (@lem6879199 term214). Qed.
Lemma lem6879201 : term581 = term214.
Proof. exact (TRANS (@lem6879197) (@lem6879200)). Qed.
Lemma lem6879202 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6879203 : term592 = term341.
Proof. exact (MK_COMB (@lem6879202) (@lem6879201)). Qed.
Lemma lem6879204 (_91912 : int) : (real_of_int _91912) = (real_of_int _91912).
Proof. exact (eq_refl (real_of_int _91912)). Qed.
Lemma lem6879205 (_91912 : int) : (term578 _91912) = (term593 _91912).
Proof. exact (MK_COMB (@lem6879203) (@lem6879204 _91912)). Qed.
Lemma lem6879206 (_91912 : int) : (term577 _91912) = (term593 _91912).
Proof. exact (TRANS (@lem6879103 _91912) (@lem6879205 _91912)). Qed.
Lemma lem6879207 (_91912 : int) : (term593 _91912) = term214.
Proof. exact (@lem1982719 (real_of_int _91912)). Qed.
Lemma lem6879208 (_91912 : int) : (term577 _91912) = term214.
Proof. exact (TRANS (@lem6879206 _91912) (@lem6879207 _91912)). Qed.
Lemma lem6879209 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6879210 (_91912 : int) : (term594 _91912) = term256.
Proof. exact (MK_COMB (@lem6879209) (@lem6879208 _91912)). Qed.
Lemma lem6879211 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem6879212 (_91912 : int) : (term654 _91912) = term599.
Proof. exact (MK_COMB (@lem6879210 _91912) (@lem6879211)). Qed.
Lemma lem6879213 (_91912 : int) : (term653 _91912) = term599.
Proof. exact (TRANS (@lem6879102 _91912) (@lem6879212 _91912)). Qed.
Lemma lem6879214 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6879215 (_91912 : int) : (term653 _91912) = term279.
Proof. exact (TRANS (@lem6879213 _91912) (@lem6879214)). Qed.
Lemma lem6879216 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6879217 (_91912 : int) : (term655 _91912) = term601.
Proof. exact (MK_COMB (@lem6879216) (@lem6879215 _91912)). Qed.
Lemma lem6879218 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6879219 (_91912 : int) : (term652 _91912) = term602.
Proof. exact (MK_COMB (@lem6879217 _91912) (@lem6879218)). Qed.
Lemma lem6879220 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : term602.
Proof. exact (EQ_MP (@lem6879219 _91912) (@lem6879101 _91911 _91912 h1)). Qed.
Lemma lem6879222 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6879223 : term602 = term603.
Proof. exact (@lem6879222 term214 term279). Qed.
Lemma lem6879225 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6879226 : term279 = term280.
Proof. exact (@lem6879225 term92). Qed.
Lemma lem6879228 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6879229 : term214 = term276.
Proof. exact (@lem6879228 (NUMERAL 0)). Qed.
Lemma lem6879230 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6879231 : term216 = term604.
Proof. exact (MK_COMB (@lem6879230) (@lem6879229)). Qed.
Lemma lem6879232 : term603 = term605.
Proof. exact (MK_COMB (@lem6879231) (@lem6879226)). Qed.
Lemma lem6879233 : term606.
Proof. exact (@lem1980026 term214 term224 term279 term224). Qed.
Lemma lem6879235 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879236 : term331 = term332.
Proof. exact (@lem6879235 (NUMERAL 0) term92). Qed.
Lemma lem6879237 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879238 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879239 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879238 h1) (fun h1 : term332 = True => @lem6879237)). Qed.
Lemma lem6879240 : term332 = True.
Proof. exact (EQ_MP (@lem6879239) (@lem6879237)). Qed.
Lemma lem6879241 : term331 = True.
Proof. exact (TRANS (@lem6879236) (@lem6879240)). Qed.
Lemma lem6879242 : True = term331.
Proof. exact (SYM (@lem6879241)). Qed.
Lemma lem6879243 : term331.
Proof. exact (EQ_MP (@lem6879242) (@lem0)). Qed.
Lemma lem6879244 : term607.
Proof. exact (@lem6879233 (@lem6879243)). Qed.
Lemma lem6879246 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879247 : term331 = term332.
Proof. exact (@lem6879246 (NUMERAL 0) term92). Qed.
Lemma lem6879248 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879249 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879250 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879249 h1) (fun h1 : term332 = True => @lem6879248)). Qed.
Lemma lem6879251 : term332 = True.
Proof. exact (EQ_MP (@lem6879250) (@lem6879248)). Qed.
Lemma lem6879252 : term331 = True.
Proof. exact (TRANS (@lem6879247) (@lem6879251)). Qed.
Lemma lem6879253 : True = term331.
Proof. exact (SYM (@lem6879252)). Qed.
Lemma lem6879254 : term331.
Proof. exact (EQ_MP (@lem6879253) (@lem0)). Qed.
Lemma lem6879255 : term605 = term608.
Proof. exact (@lem6879244 (@lem6879254)). Qed.
Lemma lem6879257 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6879258 : term305 = term310.
Proof. exact (@lem6879257 term92 term92). Qed.
Lemma lem6879259 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879260 : term291 = term92.
Proof. exact (EQ_MP (@lem6879259) (@lem940073)). Qed.
Lemma lem6879261 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879262 : term289 = term224.
Proof. exact (MK_COMB (@lem6879261) (@lem6879260)). Qed.
Lemma lem6879263 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6879264 : term310 = term279.
Proof. exact (MK_COMB (@lem6879263) (@lem6879262)). Qed.
Lemma lem6879265 : term305 = term279.
Proof. exact (TRANS (@lem6879258) (@lem6879264)). Qed.
Lemma lem6879267 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6879268 : term343 = term214.
Proof. exact (@lem6879267 term92). Qed.
Lemma lem6879269 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6879270 : term609 = term216.
Proof. exact (MK_COMB (@lem6879269) (@lem6879268)). Qed.
Lemma lem6879271 : term608 = term603.
Proof. exact (MK_COMB (@lem6879270) (@lem6879265)). Qed.
Lemma lem6879273 (m : nat) (n : nat) : (term610 m n) = (term611 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6879274 : term603 = term612.
Proof. exact (@lem6879273 (NUMERAL 0) term92). Qed.
Lemma lem6879275 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879276 (h1 : term333 = (BIT1 0)) : (term92 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6879277 : (term333 = (BIT1 0)) = ((term92 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879276 h1) (fun h1 : (term92 = (NUMERAL 0)) = False => @lem6879275)). Qed.
Lemma lem6879278 : (term92 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6879277) (@lem6879275)). Qed.
Lemma lem6879279 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6879280 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6879281 : term613 = (and True).
Proof. exact (MK_COMB (@lem6879280) (@lem6879279)). Qed.
Lemma lem6879282 : term612 = (True /\ False).
Proof. exact (MK_COMB (@lem6879281) (@lem6879278)). Qed.
Lemma lem6879284 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6879285 : term612 = False.
Proof. exact (TRANS (@lem6879282) (@lem6879284)). Qed.
Lemma lem6879286 : term603 = False.
Proof. exact (TRANS (@lem6879274) (@lem6879285)). Qed.
Lemma lem6879287 : term608 = False.
Proof. exact (TRANS (@lem6879271) (@lem6879286)). Qed.
Lemma lem6879288 : term605 = False.
Proof. exact (TRANS (@lem6879255) (@lem6879287)). Qed.
Lemma lem6879289 : term603 = False.
Proof. exact (TRANS (@lem6879232) (@lem6879288)). Qed.
Lemma lem6879290 : term602 = False.
Proof. exact (TRANS (@lem6879223) (@lem6879289)). Qed.
Lemma lem6879291 (_91911 : int) (_91912 : int) (h1 : term614 _91911 _91912) : False.
Proof. exact (EQ_MP (@lem6879290) (@lem6879220 _91911 _91912 h1)). Qed.
Lemma lem6879292 (_91911 : int) (_91912 : int) (h1 : term541 _91911 _91912) : False.
Proof. exact (or_elim (@lem6878111 _91911 _91912 h1) (fun h0 : term550 _91911 _91912 => @lem6878515 _91911 _91912 h0) (fun h0 : term614 _91911 _91912 => @lem6879291 _91911 _91912 h0)). Qed.
Lemma lem6879293 (_91911 : int) (_91912 : int) (h1 : term537 _91911 _91912) : term537 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6879294 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term656 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6879295 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term538 _91911 _91912.
Proof. exact (proj2 (@lem6879294 _91911 _91912 h1)). Qed.
Lemma lem6879296 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term299 _91911.
Proof. exact (proj1 (@lem6879294 _91911 _91912 h1)). Qed.
Lemma lem6879297 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term489 _91911 _91912.
Proof. exact (proj2 (@lem6879295 _91911 _91912 h1)). Qed.
Lemma lem6879299 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term441 _91911 _91912.
Proof. exact (proj2 (@lem6879297 _91911 _91912 h1)). Qed.
Lemma lem6879300 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : (term316 _91911 _91912) = term214.
Proof. exact (proj1 (@lem6879297 _91911 _91912 h1)). Qed.
Lemma lem6879302 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : (real_of_int _91912) = term214.
Proof. exact (proj1 (@lem6879299 _91911 _91912 h1)). Qed.
Lemma lem6879304 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6879305 : term551 = term331.
Proof. exact (@lem6879304 term214 term224). Qed.
Lemma lem6879307 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6879308 : term224 = term304.
Proof. exact (@lem6879307 term92). Qed.
Lemma lem6879310 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6879311 : term214 = term276.
Proof. exact (@lem6879310 (NUMERAL 0)). Qed.
Lemma lem6879312 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6879313 : term552 = term553.
Proof. exact (MK_COMB (@lem6879312) (@lem6879311)). Qed.
Lemma lem6879314 : term331 = term554.
Proof. exact (MK_COMB (@lem6879313) (@lem6879308)). Qed.
Lemma lem6879315 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6879317 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879318 : term331 = term332.
Proof. exact (@lem6879317 (NUMERAL 0) term92). Qed.
Lemma lem6879319 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879320 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879321 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879320 h1) (fun h1 : term332 = True => @lem6879319)). Qed.
Lemma lem6879322 : term332 = True.
Proof. exact (EQ_MP (@lem6879321) (@lem6879319)). Qed.
Lemma lem6879323 : term331 = True.
Proof. exact (TRANS (@lem6879318) (@lem6879322)). Qed.
Lemma lem6879324 : True = term331.
Proof. exact (SYM (@lem6879323)). Qed.
Lemma lem6879325 : term331.
Proof. exact (EQ_MP (@lem6879324) (@lem0)). Qed.
Lemma lem6879326 : term556.
Proof. exact (@lem6879315 (@lem6879325)). Qed.
Lemma lem6879328 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879329 : term331 = term332.
Proof. exact (@lem6879328 (NUMERAL 0) term92). Qed.
Lemma lem6879330 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879331 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879332 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879331 h1) (fun h1 : term332 = True => @lem6879330)). Qed.
Lemma lem6879333 : term332 = True.
Proof. exact (EQ_MP (@lem6879332) (@lem6879330)). Qed.
Lemma lem6879334 : term331 = True.
Proof. exact (TRANS (@lem6879329) (@lem6879333)). Qed.
Lemma lem6879335 : True = term331.
Proof. exact (SYM (@lem6879334)). Qed.
Lemma lem6879336 : term331.
Proof. exact (EQ_MP (@lem6879335) (@lem0)). Qed.
Lemma lem6879337 : term554 = term557.
Proof. exact (@lem6879326 (@lem6879336)). Qed.
Lemma lem6879339 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6879340 : term288 = term289.
Proof. exact (@lem6879339 term92 term92). Qed.
Lemma lem6879341 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879342 : term291 = term92.
Proof. exact (EQ_MP (@lem6879341) (@lem940073)). Qed.
Lemma lem6879343 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879344 : term289 = term224.
Proof. exact (MK_COMB (@lem6879343) (@lem6879342)). Qed.
Lemma lem6879345 : term288 = term224.
Proof. exact (TRANS (@lem6879340) (@lem6879344)). Qed.
Lemma lem6879347 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6879348 : term343 = term214.
Proof. exact (@lem6879347 term92). Qed.
Lemma lem6879349 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6879350 : term558 = term552.
Proof. exact (MK_COMB (@lem6879349) (@lem6879348)). Qed.
Lemma lem6879351 : term557 = term331.
Proof. exact (MK_COMB (@lem6879350) (@lem6879345)). Qed.
Lemma lem6879353 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879354 : term331 = term332.
Proof. exact (@lem6879353 (NUMERAL 0) term92). Qed.
Lemma lem6879355 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879356 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879357 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879356 h1) (fun h1 : term332 = True => @lem6879355)). Qed.
Lemma lem6879358 : term332 = True.
Proof. exact (EQ_MP (@lem6879357) (@lem6879355)). Qed.
Lemma lem6879359 : term331 = True.
Proof. exact (TRANS (@lem6879354) (@lem6879358)). Qed.
Lemma lem6879360 : term557 = True.
Proof. exact (TRANS (@lem6879351) (@lem6879359)). Qed.
Lemma lem6879361 : term554 = True.
Proof. exact (TRANS (@lem6879337) (@lem6879360)). Qed.
Lemma lem6879362 : term331 = True.
Proof. exact (TRANS (@lem6879314) (@lem6879361)). Qed.
Lemma lem6879363 : term551 = True.
Proof. exact (TRANS (@lem6879305) (@lem6879362)). Qed.
Lemma lem6879364 : True = term551.
Proof. exact (SYM (@lem6879363)). Qed.
Lemma lem6879365 : term551.
Proof. exact (EQ_MP (@lem6879364) (@lem0)). Qed.
Lemma lem6879366 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term657 _91911.
Proof. exact (conj (@lem6879365) (@lem6879296 _91911 _91912 h1)). Qed.
Lemma lem6879368 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6879369 (_91911 : int) : term658 _91911.
Proof. exact (@lem6879368 term224 (real_of_int _91911)). Qed.
Lemma lem6879370 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term659 _91911.
Proof. exact (@lem6879369 _91911 (@lem6879366 _91911 _91912 h1)). Qed.
Lemma lem6879371 (_91911 : int) : (term622 _91911) = (real_of_int _91911).
Proof. exact (@lem1982733 (real_of_int _91911)). Qed.
Lemma lem6879372 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6879373 (_91911 : int) : (term660 _91911) = (term298 _91911).
Proof. exact (MK_COMB (@lem6879372) (@lem6879371 _91911)). Qed.
Lemma lem6879374 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6879375 (_91911 : int) : (term659 _91911) = (term299 _91911).
Proof. exact (MK_COMB (@lem6879373 _91911) (@lem6879374)). Qed.
Lemma lem6879376 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term299 _91911.
Proof. exact (EQ_MP (@lem6879375 _91911) (@lem6879370 _91911 _91912 h1)). Qed.
Lemma lem6879378 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6879379 : term551 = term331.
Proof. exact (@lem6879378 term214 term224). Qed.
Lemma lem6879381 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6879382 : term224 = term304.
Proof. exact (@lem6879381 term92). Qed.
Lemma lem6879384 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6879385 : term214 = term276.
Proof. exact (@lem6879384 (NUMERAL 0)). Qed.
Lemma lem6879386 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6879387 : term552 = term553.
Proof. exact (MK_COMB (@lem6879386) (@lem6879385)). Qed.
Lemma lem6879388 : term331 = term554.
Proof. exact (MK_COMB (@lem6879387) (@lem6879382)). Qed.
Lemma lem6879389 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6879391 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879392 : term331 = term332.
Proof. exact (@lem6879391 (NUMERAL 0) term92). Qed.
Lemma lem6879393 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879394 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879395 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879394 h1) (fun h1 : term332 = True => @lem6879393)). Qed.
Lemma lem6879396 : term332 = True.
Proof. exact (EQ_MP (@lem6879395) (@lem6879393)). Qed.
Lemma lem6879397 : term331 = True.
Proof. exact (TRANS (@lem6879392) (@lem6879396)). Qed.
Lemma lem6879398 : True = term331.
Proof. exact (SYM (@lem6879397)). Qed.
Lemma lem6879399 : term331.
Proof. exact (EQ_MP (@lem6879398) (@lem0)). Qed.
Lemma lem6879400 : term556.
Proof. exact (@lem6879389 (@lem6879399)). Qed.
Lemma lem6879402 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879403 : term331 = term332.
Proof. exact (@lem6879402 (NUMERAL 0) term92). Qed.
Lemma lem6879404 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879405 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879406 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879405 h1) (fun h1 : term332 = True => @lem6879404)). Qed.
Lemma lem6879407 : term332 = True.
Proof. exact (EQ_MP (@lem6879406) (@lem6879404)). Qed.
Lemma lem6879408 : term331 = True.
Proof. exact (TRANS (@lem6879403) (@lem6879407)). Qed.
Lemma lem6879409 : True = term331.
Proof. exact (SYM (@lem6879408)). Qed.
Lemma lem6879410 : term331.
Proof. exact (EQ_MP (@lem6879409) (@lem0)). Qed.
Lemma lem6879411 : term554 = term557.
Proof. exact (@lem6879400 (@lem6879410)). Qed.
Lemma lem6879413 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6879414 : term288 = term289.
Proof. exact (@lem6879413 term92 term92). Qed.
Lemma lem6879415 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879416 : term291 = term92.
Proof. exact (EQ_MP (@lem6879415) (@lem940073)). Qed.
Lemma lem6879417 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879418 : term289 = term224.
Proof. exact (MK_COMB (@lem6879417) (@lem6879416)). Qed.
Lemma lem6879419 : term288 = term224.
Proof. exact (TRANS (@lem6879414) (@lem6879418)). Qed.
Lemma lem6879421 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6879422 : term343 = term214.
Proof. exact (@lem6879421 term92). Qed.
Lemma lem6879423 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6879424 : term558 = term552.
Proof. exact (MK_COMB (@lem6879423) (@lem6879422)). Qed.
Lemma lem6879425 : term557 = term331.
Proof. exact (MK_COMB (@lem6879424) (@lem6879419)). Qed.
Lemma lem6879427 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879428 : term331 = term332.
Proof. exact (@lem6879427 (NUMERAL 0) term92). Qed.
Lemma lem6879429 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879430 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879431 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879430 h1) (fun h1 : term332 = True => @lem6879429)). Qed.
Lemma lem6879432 : term332 = True.
Proof. exact (EQ_MP (@lem6879431) (@lem6879429)). Qed.
Lemma lem6879433 : term331 = True.
Proof. exact (TRANS (@lem6879428) (@lem6879432)). Qed.
Lemma lem6879434 : term557 = True.
Proof. exact (TRANS (@lem6879425) (@lem6879433)). Qed.
Lemma lem6879435 : term554 = True.
Proof. exact (TRANS (@lem6879411) (@lem6879434)). Qed.
Lemma lem6879436 : term331 = True.
Proof. exact (TRANS (@lem6879388) (@lem6879435)). Qed.
Lemma lem6879437 : term551 = True.
Proof. exact (TRANS (@lem6879379) (@lem6879436)). Qed.
Lemma lem6879438 : True = term551.
Proof. exact (SYM (@lem6879437)). Qed.
Lemma lem6879439 : term551.
Proof. exact (EQ_MP (@lem6879438) (@lem0)). Qed.
Lemma lem6879440 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term661 _91911 _91912.
Proof. exact (conj (@lem6879439) (@lem6879300 _91911 _91912 h1)). Qed.
Lemma lem6879442 (x : real) (y : real) : term662 x y.
Proof. exact (proj1 (@lem1988330 x y)). Qed.
Lemma lem6879443 (_91911 : int) (_91912 : int) : term663 _91911 _91912.
Proof. exact (@lem6879442 term224 (term316 _91911 _91912)). Qed.
Lemma lem6879444 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : (term569 _91911 _91912) = term214.
Proof. exact (@lem6879443 _91911 _91912 (@lem6879440 _91911 _91912 h1)). Qed.
Lemma lem6879445 (_91911 : int) (_91912 : int) : (term569 _91911 _91912) = (term316 _91911 _91912).
Proof. exact (@lem1982733 (term316 _91911 _91912)). Qed.
Lemma lem6879446 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6879447 (_91911 : int) (_91912 : int) : (term570 _91911 _91912) = (term319 _91911 _91912).
Proof. exact (MK_COMB (@lem6879446) (@lem6879445 _91911 _91912)). Qed.
Lemma lem6879448 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6879449 (_91911 : int) (_91912 : int) : ((term569 _91911 _91912) = term214) = ((term316 _91911 _91912) = term214).
Proof. exact (MK_COMB (@lem6879447 _91911 _91912) (@lem6879448)). Qed.
Lemma lem6879450 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : (term316 _91911 _91912) = term214.
Proof. exact (EQ_MP (@lem6879449 _91911 _91912) (@lem6879444 _91911 _91912 h1)). Qed.
Lemma lem6879452 (y : real) : term565 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6879453 (_91912 : int) : term619 _91912.
Proof. exact (@lem6879452 (real_of_int _91912)). Qed.
Lemma lem6879454 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term620 _91912.
Proof. exact (@lem6879453 _91912 (@lem6879302 _91911 _91912 h1)). Qed.
Lemma lem6879455 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term636 _91912.
Proof. exact (@lem6879454 _91911 _91912 h1 term279). Qed.
Lemma lem6879456 (_91912 : int) : (term636 _91912) = ((term317 _91912) = term214).
Proof. exact (eq_refl (term636 _91912)). Qed.
Lemma lem6879463 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : (term317 _91912) = term214.
Proof. exact (EQ_MP (@lem6879456 _91912) (@lem6879455 _91911 _91912 h1)). Qed.
Lemma lem6879464 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term664 _91911 _91912.
Proof. exact (conj (@lem6879463 _91911 _91912 h1) (@lem6879450 _91911 _91912 h1)). Qed.
Lemma lem6879466 (x : real) (y : real) : term665 x y.
Proof. exact (proj1 (@lem1393126 x y)). Qed.
Lemma lem6879467 (_91911 : int) (_91912 : int) : term666 _91911 _91912.
Proof. exact (@lem6879466 (term317 _91912) (term316 _91911 _91912)). Qed.
Lemma lem6879468 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : (term667 _91911 _91912) = term214.
Proof. exact (@lem6879467 _91911 _91912 (@lem6879464 _91911 _91912 h1)). Qed.
Lemma lem6879469 (_91911 : int) (_91912 : int) : (term667 _91911 _91912) = (term668 _91911 _91912).
Proof. exact (@lem1982757 (term317 _91911) (term317 _91912) (term379 _91912)). Qed.
Lemma lem6879470 (_91912 : int) : (term653 _91912) = (term654 _91912).
Proof. exact (@lem1982763 (term317 _91912) (real_of_int _91912) term279). Qed.
Lemma lem6879471 (_91912 : int) : (term577 _91912) = (term578 _91912).
Proof. exact (@lem1982713 term279 (real_of_int _91912)). Qed.
Lemma lem6879473 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6879474 : term224 = term304.
Proof. exact (@lem6879473 term92). Qed.
Lemma lem6879476 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6879477 : term279 = term280.
Proof. exact (@lem6879476 term92). Qed.
Lemma lem6879478 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6879479 : term579 = term580.
Proof. exact (MK_COMB (@lem6879478) (@lem6879477)). Qed.
Lemma lem6879480 : term581 = term582.
Proof. exact (MK_COMB (@lem6879479) (@lem6879474)). Qed.
Lemma lem6879481 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6879483 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879484 : term331 = term332.
Proof. exact (@lem6879483 (NUMERAL 0) term92). Qed.
Lemma lem6879485 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879486 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879487 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879486 h1) (fun h1 : term332 = True => @lem6879485)). Qed.
Lemma lem6879488 : term332 = True.
Proof. exact (EQ_MP (@lem6879487) (@lem6879485)). Qed.
Lemma lem6879489 : term331 = True.
Proof. exact (TRANS (@lem6879484) (@lem6879488)). Qed.
Lemma lem6879490 : True = term331.
Proof. exact (SYM (@lem6879489)). Qed.
Lemma lem6879491 : term331.
Proof. exact (EQ_MP (@lem6879490) (@lem0)). Qed.
Lemma lem6879492 : term584.
Proof. exact (@lem6879481 (@lem6879491)). Qed.
Lemma lem6879494 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879495 : term331 = term332.
Proof. exact (@lem6879494 (NUMERAL 0) term92). Qed.
Lemma lem6879496 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879497 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879498 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879497 h1) (fun h1 : term332 = True => @lem6879496)). Qed.
Lemma lem6879499 : term332 = True.
Proof. exact (EQ_MP (@lem6879498) (@lem6879496)). Qed.
Lemma lem6879500 : term331 = True.
Proof. exact (TRANS (@lem6879495) (@lem6879499)). Qed.
Lemma lem6879501 : True = term331.
Proof. exact (SYM (@lem6879500)). Qed.
Lemma lem6879502 : term331.
Proof. exact (EQ_MP (@lem6879501) (@lem0)). Qed.
Lemma lem6879503 : term585.
Proof. exact (@lem6879492 (@lem6879502)). Qed.
Lemma lem6879505 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879506 : term331 = term332.
Proof. exact (@lem6879505 (NUMERAL 0) term92). Qed.
Lemma lem6879507 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879508 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879509 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879508 h1) (fun h1 : term332 = True => @lem6879507)). Qed.
Lemma lem6879510 : term332 = True.
Proof. exact (EQ_MP (@lem6879509) (@lem6879507)). Qed.
Lemma lem6879511 : term331 = True.
Proof. exact (TRANS (@lem6879506) (@lem6879510)). Qed.
Lemma lem6879512 : True = term331.
Proof. exact (SYM (@lem6879511)). Qed.
Lemma lem6879513 : term331.
Proof. exact (EQ_MP (@lem6879512) (@lem0)). Qed.
Lemma lem6879514 : term586.
Proof. exact (@lem6879503 (@lem6879513)). Qed.
Lemma lem6879516 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6879517 : term288 = term289.
Proof. exact (@lem6879516 term92 term92). Qed.
Lemma lem6879518 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879519 : term291 = term92.
Proof. exact (EQ_MP (@lem6879518) (@lem940073)). Qed.
Lemma lem6879520 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879521 : term289 = term224.
Proof. exact (MK_COMB (@lem6879520) (@lem6879519)). Qed.
Lemma lem6879522 : term288 = term224.
Proof. exact (TRANS (@lem6879517) (@lem6879521)). Qed.
Lemma lem6879524 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6879525 : term305 = term310.
Proof. exact (@lem6879524 term92 term92). Qed.
Lemma lem6879526 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879527 : term291 = term92.
Proof. exact (EQ_MP (@lem6879526) (@lem940073)). Qed.
Lemma lem6879528 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879529 : term289 = term224.
Proof. exact (MK_COMB (@lem6879528) (@lem6879527)). Qed.
Lemma lem6879530 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6879531 : term310 = term279.
Proof. exact (MK_COMB (@lem6879530) (@lem6879529)). Qed.
Lemma lem6879532 : term305 = term279.
Proof. exact (TRANS (@lem6879525) (@lem6879531)). Qed.
Lemma lem6879533 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6879534 : term587 = term579.
Proof. exact (MK_COMB (@lem6879533) (@lem6879532)). Qed.
Lemma lem6879535 : term588 = term581.
Proof. exact (MK_COMB (@lem6879534) (@lem6879522)). Qed.
Lemma lem6879537 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6879538 : term581 = term214.
Proof. exact (@lem6879537 term92). Qed.
Lemma lem6879539 : term588 = term214.
Proof. exact (TRANS (@lem6879535) (@lem6879538)). Qed.
Lemma lem6879540 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6879541 : term590 = term341.
Proof. exact (MK_COMB (@lem6879540) (@lem6879539)). Qed.
Lemma lem6879542 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6879543 : term591 = term343.
Proof. exact (MK_COMB (@lem6879541) (@lem6879542)). Qed.
Lemma lem6879545 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6879546 : term343 = term214.
Proof. exact (@lem6879545 term92). Qed.
Lemma lem6879547 : term591 = term214.
Proof. exact (TRANS (@lem6879543) (@lem6879546)). Qed.
Lemma lem6879549 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6879550 : term288 = term289.
Proof. exact (@lem6879549 term92 term92). Qed.
Lemma lem6879551 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879552 : term291 = term92.
Proof. exact (EQ_MP (@lem6879551) (@lem940073)). Qed.
Lemma lem6879553 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879554 : term289 = term224.
Proof. exact (MK_COMB (@lem6879553) (@lem6879552)). Qed.
Lemma lem6879555 : term288 = term224.
Proof. exact (TRANS (@lem6879550) (@lem6879554)). Qed.
Lemma lem6879556 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6879557 : term345 = term343.
Proof. exact (MK_COMB (@lem6879556) (@lem6879555)). Qed.
Lemma lem6879559 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6879560 : term343 = term214.
Proof. exact (@lem6879559 term92). Qed.
Lemma lem6879561 : term345 = term214.
Proof. exact (TRANS (@lem6879557) (@lem6879560)). Qed.
Lemma lem6879562 : term214 = term345.
Proof. exact (SYM (@lem6879561)). Qed.
Lemma lem6879563 : term591 = term345.
Proof. exact (TRANS (@lem6879547) (@lem6879562)). Qed.
Lemma lem6879564 : term582 = term276.
Proof. exact (@lem6879514 (@lem6879563)). Qed.
Lemma lem6879565 : term581 = term276.
Proof. exact (TRANS (@lem6879480) (@lem6879564)). Qed.
Lemma lem6879567 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6879568 : term276 = term214.
Proof. exact (@lem6879567 term214). Qed.
Lemma lem6879569 : term581 = term214.
Proof. exact (TRANS (@lem6879565) (@lem6879568)). Qed.
Lemma lem6879570 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6879571 : term592 = term341.
Proof. exact (MK_COMB (@lem6879570) (@lem6879569)). Qed.
Lemma lem6879572 (_91912 : int) : (real_of_int _91912) = (real_of_int _91912).
Proof. exact (eq_refl (real_of_int _91912)). Qed.
Lemma lem6879573 (_91912 : int) : (term578 _91912) = (term593 _91912).
Proof. exact (MK_COMB (@lem6879571) (@lem6879572 _91912)). Qed.
Lemma lem6879574 (_91912 : int) : (term577 _91912) = (term593 _91912).
Proof. exact (TRANS (@lem6879471 _91912) (@lem6879573 _91912)). Qed.
Lemma lem6879575 (_91912 : int) : (term593 _91912) = term214.
Proof. exact (@lem1982719 (real_of_int _91912)). Qed.
Lemma lem6879576 (_91912 : int) : (term577 _91912) = term214.
Proof. exact (TRANS (@lem6879574 _91912) (@lem6879575 _91912)). Qed.
Lemma lem6879577 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6879578 (_91912 : int) : (term594 _91912) = term256.
Proof. exact (MK_COMB (@lem6879577) (@lem6879576 _91912)). Qed.
Lemma lem6879579 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem6879580 (_91912 : int) : (term654 _91912) = term599.
Proof. exact (MK_COMB (@lem6879578 _91912) (@lem6879579)). Qed.
Lemma lem6879581 (_91912 : int) : (term653 _91912) = term599.
Proof. exact (TRANS (@lem6879470 _91912) (@lem6879580 _91912)). Qed.
Lemma lem6879582 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6879583 (_91912 : int) : (term653 _91912) = term279.
Proof. exact (TRANS (@lem6879581 _91912) (@lem6879582)). Qed.
Lemma lem6879584 (_91911 : int) : (term313 _91911) = (term313 _91911).
Proof. exact (eq_refl (term313 _91911)). Qed.
Lemma lem6879585 (_91912 : int) (_91911 : int) : (term668 _91911 _91912) = (term314 _91911).
Proof. exact (MK_COMB (@lem6879584 _91911) (@lem6879583 _91912)). Qed.
Lemma lem6879586 (_91912 : int) (_91911 : int) : (term667 _91911 _91912) = (term314 _91911).
Proof. exact (TRANS (@lem6879469 _91911 _91912) (@lem6879585 _91912 _91911)). Qed.
Lemma lem6879587 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6879588 (_91912 : int) (_91911 : int) : (term669 _91911 _91912) = (term670 _91911).
Proof. exact (MK_COMB (@lem6879587) (@lem6879586 _91912 _91911)). Qed.
Lemma lem6879589 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6879590 (_91912 : int) (_91911 : int) : ((term667 _91911 _91912) = term214) = ((term314 _91911) = term214).
Proof. exact (MK_COMB (@lem6879588 _91912 _91911) (@lem6879589)). Qed.
Lemma lem6879591 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : (term314 _91911) = term214.
Proof. exact (EQ_MP (@lem6879590 _91912 _91911) (@lem6879468 _91911 _91912 h1)). Qed.
Lemma lem6879593 (y : real) : term565 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6879594 (_91911 : int) : term671 _91911.
Proof. exact (@lem6879593 (term314 _91911)). Qed.
Lemma lem6879595 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term672 _91911.
Proof. exact (@lem6879594 _91911 (@lem6879591 _91911 _91912 h1)). Qed.
Lemma lem6879596 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term673 _91911.
Proof. exact (@lem6879595 _91911 _91912 h1 term224). Qed.
Lemma lem6879597 (_91911 : int) : (term673 _91911) = ((term674 _91911) = term214).
Proof. exact (eq_refl (term673 _91911)). Qed.
Lemma lem6879598 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : (term674 _91911) = term214.
Proof. exact (EQ_MP (@lem6879597 _91911) (@lem6879596 _91911 _91912 h1)). Qed.
Lemma lem6879599 (_91911 : int) : (term674 _91911) = (term314 _91911).
Proof. exact (@lem1982733 (term314 _91911)). Qed.
Lemma lem6879600 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6879601 (_91911 : int) : (term675 _91911) = (term670 _91911).
Proof. exact (MK_COMB (@lem6879600) (@lem6879599 _91911)). Qed.
Lemma lem6879602 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6879603 (_91911 : int) : ((term674 _91911) = term214) = ((term314 _91911) = term214).
Proof. exact (MK_COMB (@lem6879601 _91911) (@lem6879602)). Qed.
Lemma lem6879604 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : (term314 _91911) = term214.
Proof. exact (EQ_MP (@lem6879603 _91911) (@lem6879598 _91911 _91912 h1)). Qed.
Lemma lem6879605 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term676 _91911.
Proof. exact (conj (@lem6879604 _91911 _91912 h1) (@lem6879376 _91911 _91912 h1)). Qed.
Lemma lem6879607 (x : real) (y : real) : term572 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6879608 (_91911 : int) : term677 _91911.
Proof. exact (@lem6879607 (term314 _91911) (real_of_int _91911)). Qed.
Lemma lem6879609 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term678 _91911.
Proof. exact (@lem6879608 _91911 (@lem6879605 _91911 _91912 h1)). Qed.
Lemma lem6879610 (_91911 : int) : (term679 _91911) = (term654 _91911).
Proof. exact (@lem1982759 (term317 _91911) (real_of_int _91911) term279). Qed.
Lemma lem6879611 (_91911 : int) : (term577 _91911) = (term578 _91911).
Proof. exact (@lem1982713 term279 (real_of_int _91911)). Qed.
Lemma lem6879613 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6879614 : term224 = term304.
Proof. exact (@lem6879613 term92). Qed.
Lemma lem6879616 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6879617 : term279 = term280.
Proof. exact (@lem6879616 term92). Qed.
Lemma lem6879618 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6879619 : term579 = term580.
Proof. exact (MK_COMB (@lem6879618) (@lem6879617)). Qed.
Lemma lem6879620 : term581 = term582.
Proof. exact (MK_COMB (@lem6879619) (@lem6879614)). Qed.
Lemma lem6879621 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6879623 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879624 : term331 = term332.
Proof. exact (@lem6879623 (NUMERAL 0) term92). Qed.
Lemma lem6879625 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879626 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879627 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879626 h1) (fun h1 : term332 = True => @lem6879625)). Qed.
Lemma lem6879628 : term332 = True.
Proof. exact (EQ_MP (@lem6879627) (@lem6879625)). Qed.
Lemma lem6879629 : term331 = True.
Proof. exact (TRANS (@lem6879624) (@lem6879628)). Qed.
Lemma lem6879630 : True = term331.
Proof. exact (SYM (@lem6879629)). Qed.
Lemma lem6879631 : term331.
Proof. exact (EQ_MP (@lem6879630) (@lem0)). Qed.
Lemma lem6879632 : term584.
Proof. exact (@lem6879621 (@lem6879631)). Qed.
Lemma lem6879634 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879635 : term331 = term332.
Proof. exact (@lem6879634 (NUMERAL 0) term92). Qed.
Lemma lem6879636 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879637 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879638 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879637 h1) (fun h1 : term332 = True => @lem6879636)). Qed.
Lemma lem6879639 : term332 = True.
Proof. exact (EQ_MP (@lem6879638) (@lem6879636)). Qed.
Lemma lem6879640 : term331 = True.
Proof. exact (TRANS (@lem6879635) (@lem6879639)). Qed.
Lemma lem6879641 : True = term331.
Proof. exact (SYM (@lem6879640)). Qed.
Lemma lem6879642 : term331.
Proof. exact (EQ_MP (@lem6879641) (@lem0)). Qed.
Lemma lem6879643 : term585.
Proof. exact (@lem6879632 (@lem6879642)). Qed.
Lemma lem6879645 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879646 : term331 = term332.
Proof. exact (@lem6879645 (NUMERAL 0) term92). Qed.
Lemma lem6879647 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879648 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879649 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879648 h1) (fun h1 : term332 = True => @lem6879647)). Qed.
Lemma lem6879650 : term332 = True.
Proof. exact (EQ_MP (@lem6879649) (@lem6879647)). Qed.
Lemma lem6879651 : term331 = True.
Proof. exact (TRANS (@lem6879646) (@lem6879650)). Qed.
Lemma lem6879652 : True = term331.
Proof. exact (SYM (@lem6879651)). Qed.
Lemma lem6879653 : term331.
Proof. exact (EQ_MP (@lem6879652) (@lem0)). Qed.
Lemma lem6879654 : term586.
Proof. exact (@lem6879643 (@lem6879653)). Qed.
Lemma lem6879656 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6879657 : term288 = term289.
Proof. exact (@lem6879656 term92 term92). Qed.
Lemma lem6879658 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879659 : term291 = term92.
Proof. exact (EQ_MP (@lem6879658) (@lem940073)). Qed.
Lemma lem6879660 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879661 : term289 = term224.
Proof. exact (MK_COMB (@lem6879660) (@lem6879659)). Qed.
Lemma lem6879662 : term288 = term224.
Proof. exact (TRANS (@lem6879657) (@lem6879661)). Qed.
Lemma lem6879664 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6879665 : term305 = term310.
Proof. exact (@lem6879664 term92 term92). Qed.
Lemma lem6879666 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879667 : term291 = term92.
Proof. exact (EQ_MP (@lem6879666) (@lem940073)). Qed.
Lemma lem6879668 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879669 : term289 = term224.
Proof. exact (MK_COMB (@lem6879668) (@lem6879667)). Qed.
Lemma lem6879670 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6879671 : term310 = term279.
Proof. exact (MK_COMB (@lem6879670) (@lem6879669)). Qed.
Lemma lem6879672 : term305 = term279.
Proof. exact (TRANS (@lem6879665) (@lem6879671)). Qed.
Lemma lem6879673 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6879674 : term587 = term579.
Proof. exact (MK_COMB (@lem6879673) (@lem6879672)). Qed.
Lemma lem6879675 : term588 = term581.
Proof. exact (MK_COMB (@lem6879674) (@lem6879662)). Qed.
Lemma lem6879677 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6879678 : term581 = term214.
Proof. exact (@lem6879677 term92). Qed.
Lemma lem6879679 : term588 = term214.
Proof. exact (TRANS (@lem6879675) (@lem6879678)). Qed.
Lemma lem6879680 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6879681 : term590 = term341.
Proof. exact (MK_COMB (@lem6879680) (@lem6879679)). Qed.
Lemma lem6879682 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6879683 : term591 = term343.
Proof. exact (MK_COMB (@lem6879681) (@lem6879682)). Qed.
Lemma lem6879685 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6879686 : term343 = term214.
Proof. exact (@lem6879685 term92). Qed.
Lemma lem6879687 : term591 = term214.
Proof. exact (TRANS (@lem6879683) (@lem6879686)). Qed.
Lemma lem6879689 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6879690 : term288 = term289.
Proof. exact (@lem6879689 term92 term92). Qed.
Lemma lem6879691 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879692 : term291 = term92.
Proof. exact (EQ_MP (@lem6879691) (@lem940073)). Qed.
Lemma lem6879693 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879694 : term289 = term224.
Proof. exact (MK_COMB (@lem6879693) (@lem6879692)). Qed.
Lemma lem6879695 : term288 = term224.
Proof. exact (TRANS (@lem6879690) (@lem6879694)). Qed.
Lemma lem6879696 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6879697 : term345 = term343.
Proof. exact (MK_COMB (@lem6879696) (@lem6879695)). Qed.
Lemma lem6879699 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6879700 : term343 = term214.
Proof. exact (@lem6879699 term92). Qed.
Lemma lem6879701 : term345 = term214.
Proof. exact (TRANS (@lem6879697) (@lem6879700)). Qed.
Lemma lem6879702 : term214 = term345.
Proof. exact (SYM (@lem6879701)). Qed.
Lemma lem6879703 : term591 = term345.
Proof. exact (TRANS (@lem6879687) (@lem6879702)). Qed.
Lemma lem6879704 : term582 = term276.
Proof. exact (@lem6879654 (@lem6879703)). Qed.
Lemma lem6879705 : term581 = term276.
Proof. exact (TRANS (@lem6879620) (@lem6879704)). Qed.
Lemma lem6879707 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6879708 : term276 = term214.
Proof. exact (@lem6879707 term214). Qed.
Lemma lem6879709 : term581 = term214.
Proof. exact (TRANS (@lem6879705) (@lem6879708)). Qed.
Lemma lem6879710 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6879711 : term592 = term341.
Proof. exact (MK_COMB (@lem6879710) (@lem6879709)). Qed.
Lemma lem6879712 (_91911 : int) : (real_of_int _91911) = (real_of_int _91911).
Proof. exact (eq_refl (real_of_int _91911)). Qed.
Lemma lem6879713 (_91911 : int) : (term578 _91911) = (term593 _91911).
Proof. exact (MK_COMB (@lem6879711) (@lem6879712 _91911)). Qed.
Lemma lem6879714 (_91911 : int) : (term577 _91911) = (term593 _91911).
Proof. exact (TRANS (@lem6879611 _91911) (@lem6879713 _91911)). Qed.
Lemma lem6879715 (_91911 : int) : (term593 _91911) = term214.
Proof. exact (@lem1982719 (real_of_int _91911)). Qed.
Lemma lem6879716 (_91911 : int) : (term577 _91911) = term214.
Proof. exact (TRANS (@lem6879714 _91911) (@lem6879715 _91911)). Qed.
Lemma lem6879717 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6879718 (_91911 : int) : (term594 _91911) = term256.
Proof. exact (MK_COMB (@lem6879717) (@lem6879716 _91911)). Qed.
Lemma lem6879719 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem6879720 (_91911 : int) : (term654 _91911) = term599.
Proof. exact (MK_COMB (@lem6879718 _91911) (@lem6879719)). Qed.
Lemma lem6879721 (_91911 : int) : (term679 _91911) = term599.
Proof. exact (TRANS (@lem6879610 _91911) (@lem6879720 _91911)). Qed.
Lemma lem6879722 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6879723 (_91911 : int) : (term679 _91911) = term279.
Proof. exact (TRANS (@lem6879721 _91911) (@lem6879722)). Qed.
Lemma lem6879724 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6879725 (_91911 : int) : (term680 _91911) = term601.
Proof. exact (MK_COMB (@lem6879724) (@lem6879723 _91911)). Qed.
Lemma lem6879726 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6879727 (_91911 : int) : (term678 _91911) = term602.
Proof. exact (MK_COMB (@lem6879725 _91911) (@lem6879726)). Qed.
Lemma lem6879728 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : term602.
Proof. exact (EQ_MP (@lem6879727 _91911) (@lem6879609 _91911 _91912 h1)). Qed.
Lemma lem6879730 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6879731 : term602 = term603.
Proof. exact (@lem6879730 term214 term279). Qed.
Lemma lem6879733 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6879734 : term279 = term280.
Proof. exact (@lem6879733 term92). Qed.
Lemma lem6879736 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6879737 : term214 = term276.
Proof. exact (@lem6879736 (NUMERAL 0)). Qed.
Lemma lem6879738 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6879739 : term216 = term604.
Proof. exact (MK_COMB (@lem6879738) (@lem6879737)). Qed.
Lemma lem6879740 : term603 = term605.
Proof. exact (MK_COMB (@lem6879739) (@lem6879734)). Qed.
Lemma lem6879741 : term606.
Proof. exact (@lem1980026 term214 term224 term279 term224). Qed.
Lemma lem6879743 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879744 : term331 = term332.
Proof. exact (@lem6879743 (NUMERAL 0) term92). Qed.
Lemma lem6879745 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879746 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879747 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879746 h1) (fun h1 : term332 = True => @lem6879745)). Qed.
Lemma lem6879748 : term332 = True.
Proof. exact (EQ_MP (@lem6879747) (@lem6879745)). Qed.
Lemma lem6879749 : term331 = True.
Proof. exact (TRANS (@lem6879744) (@lem6879748)). Qed.
Lemma lem6879750 : True = term331.
Proof. exact (SYM (@lem6879749)). Qed.
Lemma lem6879751 : term331.
Proof. exact (EQ_MP (@lem6879750) (@lem0)). Qed.
Lemma lem6879752 : term607.
Proof. exact (@lem6879741 (@lem6879751)). Qed.
Lemma lem6879754 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879755 : term331 = term332.
Proof. exact (@lem6879754 (NUMERAL 0) term92). Qed.
Lemma lem6879756 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879757 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879758 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879757 h1) (fun h1 : term332 = True => @lem6879756)). Qed.
Lemma lem6879759 : term332 = True.
Proof. exact (EQ_MP (@lem6879758) (@lem6879756)). Qed.
Lemma lem6879760 : term331 = True.
Proof. exact (TRANS (@lem6879755) (@lem6879759)). Qed.
Lemma lem6879761 : True = term331.
Proof. exact (SYM (@lem6879760)). Qed.
Lemma lem6879762 : term331.
Proof. exact (EQ_MP (@lem6879761) (@lem0)). Qed.
Lemma lem6879763 : term605 = term608.
Proof. exact (@lem6879752 (@lem6879762)). Qed.
Lemma lem6879765 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6879766 : term305 = term310.
Proof. exact (@lem6879765 term92 term92). Qed.
Lemma lem6879767 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879768 : term291 = term92.
Proof. exact (EQ_MP (@lem6879767) (@lem940073)). Qed.
Lemma lem6879769 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879770 : term289 = term224.
Proof. exact (MK_COMB (@lem6879769) (@lem6879768)). Qed.
Lemma lem6879771 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6879772 : term310 = term279.
Proof. exact (MK_COMB (@lem6879771) (@lem6879770)). Qed.
Lemma lem6879773 : term305 = term279.
Proof. exact (TRANS (@lem6879766) (@lem6879772)). Qed.
Lemma lem6879775 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6879776 : term343 = term214.
Proof. exact (@lem6879775 term92). Qed.
Lemma lem6879777 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6879778 : term609 = term216.
Proof. exact (MK_COMB (@lem6879777) (@lem6879776)). Qed.
Lemma lem6879779 : term608 = term603.
Proof. exact (MK_COMB (@lem6879778) (@lem6879773)). Qed.
Lemma lem6879781 (m : nat) (n : nat) : (term610 m n) = (term611 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6879782 : term603 = term612.
Proof. exact (@lem6879781 (NUMERAL 0) term92). Qed.
Lemma lem6879783 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879784 (h1 : term333 = (BIT1 0)) : (term92 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6879785 : (term333 = (BIT1 0)) = ((term92 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879784 h1) (fun h1 : (term92 = (NUMERAL 0)) = False => @lem6879783)). Qed.
Lemma lem6879786 : (term92 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6879785) (@lem6879783)). Qed.
Lemma lem6879787 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6879788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6879789 : term613 = (and True).
Proof. exact (MK_COMB (@lem6879788) (@lem6879787)). Qed.
Lemma lem6879790 : term612 = (True /\ False).
Proof. exact (MK_COMB (@lem6879789) (@lem6879786)). Qed.
Lemma lem6879792 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6879793 : term612 = False.
Proof. exact (TRANS (@lem6879790) (@lem6879792)). Qed.
Lemma lem6879794 : term603 = False.
Proof. exact (TRANS (@lem6879782) (@lem6879793)). Qed.
Lemma lem6879795 : term608 = False.
Proof. exact (TRANS (@lem6879779) (@lem6879794)). Qed.
Lemma lem6879796 : term605 = False.
Proof. exact (TRANS (@lem6879763) (@lem6879795)). Qed.
Lemma lem6879797 : term603 = False.
Proof. exact (TRANS (@lem6879740) (@lem6879796)). Qed.
Lemma lem6879798 : term602 = False.
Proof. exact (TRANS (@lem6879731) (@lem6879797)). Qed.
Lemma lem6879799 (_91911 : int) (_91912 : int) (h1 : term656 _91911 _91912) : False.
Proof. exact (EQ_MP (@lem6879798) (@lem6879728 _91911 _91912 h1)). Qed.
Lemma lem6879800 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term681 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6879801 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term539 _91911 _91912.
Proof. exact (proj2 (@lem6879800 _91911 _91912 h1)). Qed.
Lemma lem6879803 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term490 _91911 _91912.
Proof. exact (proj2 (@lem6879801 _91911 _91912 h1)). Qed.
Lemma lem6879805 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term441 _91911 _91912.
Proof. exact (proj2 (@lem6879803 _91911 _91912 h1)). Qed.
Lemma lem6879806 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term352 _91912 _91911.
Proof. exact (proj1 (@lem6879803 _91911 _91912 h1)). Qed.
Lemma lem6879807 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : (real_of_int _91911) = term214.
Proof. exact (proj2 (@lem6879806 _91911 _91912 h1)). Qed.
Lemma lem6879809 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term366 _91911 _91912.
Proof. exact (proj2 (@lem6879805 _91911 _91912 h1)). Qed.
Lemma lem6879810 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : (real_of_int _91912) = term214.
Proof. exact (proj1 (@lem6879805 _91911 _91912 h1)). Qed.
Lemma lem6879812 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6879813 : term551 = term331.
Proof. exact (@lem6879812 term214 term224). Qed.
Lemma lem6879815 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6879816 : term224 = term304.
Proof. exact (@lem6879815 term92). Qed.
Lemma lem6879818 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6879819 : term214 = term276.
Proof. exact (@lem6879818 (NUMERAL 0)). Qed.
Lemma lem6879820 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6879821 : term552 = term553.
Proof. exact (MK_COMB (@lem6879820) (@lem6879819)). Qed.
Lemma lem6879822 : term331 = term554.
Proof. exact (MK_COMB (@lem6879821) (@lem6879816)). Qed.
Lemma lem6879823 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6879825 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879826 : term331 = term332.
Proof. exact (@lem6879825 (NUMERAL 0) term92). Qed.
Lemma lem6879827 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879828 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879829 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879828 h1) (fun h1 : term332 = True => @lem6879827)). Qed.
Lemma lem6879830 : term332 = True.
Proof. exact (EQ_MP (@lem6879829) (@lem6879827)). Qed.
Lemma lem6879831 : term331 = True.
Proof. exact (TRANS (@lem6879826) (@lem6879830)). Qed.
Lemma lem6879832 : True = term331.
Proof. exact (SYM (@lem6879831)). Qed.
Lemma lem6879833 : term331.
Proof. exact (EQ_MP (@lem6879832) (@lem0)). Qed.
Lemma lem6879834 : term556.
Proof. exact (@lem6879823 (@lem6879833)). Qed.
Lemma lem6879836 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879837 : term331 = term332.
Proof. exact (@lem6879836 (NUMERAL 0) term92). Qed.
Lemma lem6879838 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879839 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879840 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879839 h1) (fun h1 : term332 = True => @lem6879838)). Qed.
Lemma lem6879841 : term332 = True.
Proof. exact (EQ_MP (@lem6879840) (@lem6879838)). Qed.
Lemma lem6879842 : term331 = True.
Proof. exact (TRANS (@lem6879837) (@lem6879841)). Qed.
Lemma lem6879843 : True = term331.
Proof. exact (SYM (@lem6879842)). Qed.
Lemma lem6879844 : term331.
Proof. exact (EQ_MP (@lem6879843) (@lem0)). Qed.
Lemma lem6879845 : term554 = term557.
Proof. exact (@lem6879834 (@lem6879844)). Qed.
Lemma lem6879847 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6879848 : term288 = term289.
Proof. exact (@lem6879847 term92 term92). Qed.
Lemma lem6879849 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879850 : term291 = term92.
Proof. exact (EQ_MP (@lem6879849) (@lem940073)). Qed.
Lemma lem6879851 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879852 : term289 = term224.
Proof. exact (MK_COMB (@lem6879851) (@lem6879850)). Qed.
Lemma lem6879853 : term288 = term224.
Proof. exact (TRANS (@lem6879848) (@lem6879852)). Qed.
Lemma lem6879855 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6879856 : term343 = term214.
Proof. exact (@lem6879855 term92). Qed.
Lemma lem6879857 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6879858 : term558 = term552.
Proof. exact (MK_COMB (@lem6879857) (@lem6879856)). Qed.
Lemma lem6879859 : term557 = term331.
Proof. exact (MK_COMB (@lem6879858) (@lem6879853)). Qed.
Lemma lem6879861 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879862 : term331 = term332.
Proof. exact (@lem6879861 (NUMERAL 0) term92). Qed.
Lemma lem6879863 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879864 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879865 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879864 h1) (fun h1 : term332 = True => @lem6879863)). Qed.
Lemma lem6879866 : term332 = True.
Proof. exact (EQ_MP (@lem6879865) (@lem6879863)). Qed.
Lemma lem6879867 : term331 = True.
Proof. exact (TRANS (@lem6879862) (@lem6879866)). Qed.
Lemma lem6879868 : term557 = True.
Proof. exact (TRANS (@lem6879859) (@lem6879867)). Qed.
Lemma lem6879869 : term554 = True.
Proof. exact (TRANS (@lem6879845) (@lem6879868)). Qed.
Lemma lem6879870 : term331 = True.
Proof. exact (TRANS (@lem6879822) (@lem6879869)). Qed.
Lemma lem6879871 : term551 = True.
Proof. exact (TRANS (@lem6879813) (@lem6879870)). Qed.
Lemma lem6879872 : True = term551.
Proof. exact (SYM (@lem6879871)). Qed.
Lemma lem6879873 : term551.
Proof. exact (EQ_MP (@lem6879872) (@lem0)). Qed.
Lemma lem6879874 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term615 _91911 _91912.
Proof. exact (conj (@lem6879873) (@lem6879809 _91911 _91912 h1)). Qed.
Lemma lem6879876 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6879877 (_91911 : int) (_91912 : int) : term616 _91911 _91912.
Proof. exact (@lem6879876 term224 (term316 _91911 _91912)). Qed.
Lemma lem6879878 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term617 _91911 _91912.
Proof. exact (@lem6879877 _91911 _91912 (@lem6879874 _91911 _91912 h1)). Qed.
Lemma lem6879879 (_91911 : int) (_91912 : int) : (term569 _91911 _91912) = (term316 _91911 _91912).
Proof. exact (@lem1982733 (term316 _91911 _91912)). Qed.
Lemma lem6879880 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6879881 (_91911 : int) (_91912 : int) : (term618 _91911 _91912) = (term365 _91911 _91912).
Proof. exact (MK_COMB (@lem6879880) (@lem6879879 _91911 _91912)). Qed.
Lemma lem6879882 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6879883 (_91911 : int) (_91912 : int) : (term617 _91911 _91912) = (term366 _91911 _91912).
Proof. exact (MK_COMB (@lem6879881 _91911 _91912) (@lem6879882)). Qed.
Lemma lem6879884 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term366 _91911 _91912.
Proof. exact (EQ_MP (@lem6879883 _91911 _91912) (@lem6879878 _91911 _91912 h1)). Qed.
Lemma lem6879886 (y : real) : term565 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6879887 (_91912 : int) : term619 _91912.
Proof. exact (@lem6879886 (real_of_int _91912)). Qed.
Lemma lem6879888 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term620 _91912.
Proof. exact (@lem6879887 _91912 (@lem6879810 _91911 _91912 h1)). Qed.
Lemma lem6879889 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term636 _91912.
Proof. exact (@lem6879888 _91911 _91912 h1 term279). Qed.
Lemma lem6879890 (_91912 : int) : (term636 _91912) = ((term317 _91912) = term214).
Proof. exact (eq_refl (term636 _91912)). Qed.
Lemma lem6879897 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : (term317 _91912) = term214.
Proof. exact (EQ_MP (@lem6879890 _91912) (@lem6879889 _91911 _91912 h1)). Qed.
Lemma lem6879898 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term682 _91911 _91912.
Proof. exact (conj (@lem6879897 _91911 _91912 h1) (@lem6879884 _91911 _91912 h1)). Qed.
Lemma lem6879900 (x : real) (y : real) : term572 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6879901 (_91911 : int) (_91912 : int) : term683 _91911 _91912.
Proof. exact (@lem6879900 (term317 _91912) (term316 _91911 _91912)). Qed.
Lemma lem6879902 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term684 _91911 _91912.
Proof. exact (@lem6879901 _91911 _91912 (@lem6879898 _91911 _91912 h1)). Qed.
Lemma lem6879903 (_91911 : int) (_91912 : int) : (term667 _91911 _91912) = (term668 _91911 _91912).
Proof. exact (@lem1982757 (term317 _91911) (term317 _91912) (term379 _91912)). Qed.
Lemma lem6879904 (_91912 : int) : (term653 _91912) = (term654 _91912).
Proof. exact (@lem1982763 (term317 _91912) (real_of_int _91912) term279). Qed.
Lemma lem6879905 (_91912 : int) : (term577 _91912) = (term578 _91912).
Proof. exact (@lem1982713 term279 (real_of_int _91912)). Qed.
Lemma lem6879907 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6879908 : term224 = term304.
Proof. exact (@lem6879907 term92). Qed.
Lemma lem6879910 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6879911 : term279 = term280.
Proof. exact (@lem6879910 term92). Qed.
Lemma lem6879912 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6879913 : term579 = term580.
Proof. exact (MK_COMB (@lem6879912) (@lem6879911)). Qed.
Lemma lem6879914 : term581 = term582.
Proof. exact (MK_COMB (@lem6879913) (@lem6879908)). Qed.
Lemma lem6879915 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6879917 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879918 : term331 = term332.
Proof. exact (@lem6879917 (NUMERAL 0) term92). Qed.
Lemma lem6879919 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879920 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879921 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879920 h1) (fun h1 : term332 = True => @lem6879919)). Qed.
Lemma lem6879922 : term332 = True.
Proof. exact (EQ_MP (@lem6879921) (@lem6879919)). Qed.
Lemma lem6879923 : term331 = True.
Proof. exact (TRANS (@lem6879918) (@lem6879922)). Qed.
Lemma lem6879924 : True = term331.
Proof. exact (SYM (@lem6879923)). Qed.
Lemma lem6879925 : term331.
Proof. exact (EQ_MP (@lem6879924) (@lem0)). Qed.
Lemma lem6879926 : term584.
Proof. exact (@lem6879915 (@lem6879925)). Qed.
Lemma lem6879928 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879929 : term331 = term332.
Proof. exact (@lem6879928 (NUMERAL 0) term92). Qed.
Lemma lem6879930 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879931 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879932 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879931 h1) (fun h1 : term332 = True => @lem6879930)). Qed.
Lemma lem6879933 : term332 = True.
Proof. exact (EQ_MP (@lem6879932) (@lem6879930)). Qed.
Lemma lem6879934 : term331 = True.
Proof. exact (TRANS (@lem6879929) (@lem6879933)). Qed.
Lemma lem6879935 : True = term331.
Proof. exact (SYM (@lem6879934)). Qed.
Lemma lem6879936 : term331.
Proof. exact (EQ_MP (@lem6879935) (@lem0)). Qed.
Lemma lem6879937 : term585.
Proof. exact (@lem6879926 (@lem6879936)). Qed.
Lemma lem6879939 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6879940 : term331 = term332.
Proof. exact (@lem6879939 (NUMERAL 0) term92). Qed.
Lemma lem6879941 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6879942 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6879943 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6879942 h1) (fun h1 : term332 = True => @lem6879941)). Qed.
Lemma lem6879944 : term332 = True.
Proof. exact (EQ_MP (@lem6879943) (@lem6879941)). Qed.
Lemma lem6879945 : term331 = True.
Proof. exact (TRANS (@lem6879940) (@lem6879944)). Qed.
Lemma lem6879946 : True = term331.
Proof. exact (SYM (@lem6879945)). Qed.
Lemma lem6879947 : term331.
Proof. exact (EQ_MP (@lem6879946) (@lem0)). Qed.
Lemma lem6879948 : term586.
Proof. exact (@lem6879937 (@lem6879947)). Qed.
Lemma lem6879950 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6879951 : term288 = term289.
Proof. exact (@lem6879950 term92 term92). Qed.
Lemma lem6879952 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879953 : term291 = term92.
Proof. exact (EQ_MP (@lem6879952) (@lem940073)). Qed.
Lemma lem6879954 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879955 : term289 = term224.
Proof. exact (MK_COMB (@lem6879954) (@lem6879953)). Qed.
Lemma lem6879956 : term288 = term224.
Proof. exact (TRANS (@lem6879951) (@lem6879955)). Qed.
Lemma lem6879958 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6879959 : term305 = term310.
Proof. exact (@lem6879958 term92 term92). Qed.
Lemma lem6879960 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879961 : term291 = term92.
Proof. exact (EQ_MP (@lem6879960) (@lem940073)). Qed.
Lemma lem6879962 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879963 : term289 = term224.
Proof. exact (MK_COMB (@lem6879962) (@lem6879961)). Qed.
Lemma lem6879964 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6879965 : term310 = term279.
Proof. exact (MK_COMB (@lem6879964) (@lem6879963)). Qed.
Lemma lem6879966 : term305 = term279.
Proof. exact (TRANS (@lem6879959) (@lem6879965)). Qed.
Lemma lem6879967 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6879968 : term587 = term579.
Proof. exact (MK_COMB (@lem6879967) (@lem6879966)). Qed.
Lemma lem6879969 : term588 = term581.
Proof. exact (MK_COMB (@lem6879968) (@lem6879956)). Qed.
Lemma lem6879971 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6879972 : term581 = term214.
Proof. exact (@lem6879971 term92). Qed.
Lemma lem6879973 : term588 = term214.
Proof. exact (TRANS (@lem6879969) (@lem6879972)). Qed.
Lemma lem6879974 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6879975 : term590 = term341.
Proof. exact (MK_COMB (@lem6879974) (@lem6879973)). Qed.
Lemma lem6879976 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6879977 : term591 = term343.
Proof. exact (MK_COMB (@lem6879975) (@lem6879976)). Qed.
Lemma lem6879979 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6879980 : term343 = term214.
Proof. exact (@lem6879979 term92). Qed.
Lemma lem6879981 : term591 = term214.
Proof. exact (TRANS (@lem6879977) (@lem6879980)). Qed.
Lemma lem6879983 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6879984 : term288 = term289.
Proof. exact (@lem6879983 term92 term92). Qed.
Lemma lem6879985 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6879986 : term291 = term92.
Proof. exact (EQ_MP (@lem6879985) (@lem940073)). Qed.
Lemma lem6879987 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6879988 : term289 = term224.
Proof. exact (MK_COMB (@lem6879987) (@lem6879986)). Qed.
Lemma lem6879989 : term288 = term224.
Proof. exact (TRANS (@lem6879984) (@lem6879988)). Qed.
Lemma lem6879990 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6879991 : term345 = term343.
Proof. exact (MK_COMB (@lem6879990) (@lem6879989)). Qed.
Lemma lem6879993 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6879994 : term343 = term214.
Proof. exact (@lem6879993 term92). Qed.
Lemma lem6879995 : term345 = term214.
Proof. exact (TRANS (@lem6879991) (@lem6879994)). Qed.
Lemma lem6879996 : term214 = term345.
Proof. exact (SYM (@lem6879995)). Qed.
Lemma lem6879997 : term591 = term345.
Proof. exact (TRANS (@lem6879981) (@lem6879996)). Qed.
Lemma lem6879998 : term582 = term276.
Proof. exact (@lem6879948 (@lem6879997)). Qed.
Lemma lem6879999 : term581 = term276.
Proof. exact (TRANS (@lem6879914) (@lem6879998)). Qed.
Lemma lem6880001 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6880002 : term276 = term214.
Proof. exact (@lem6880001 term214). Qed.
Lemma lem6880003 : term581 = term214.
Proof. exact (TRANS (@lem6879999) (@lem6880002)). Qed.
Lemma lem6880004 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6880005 : term592 = term341.
Proof. exact (MK_COMB (@lem6880004) (@lem6880003)). Qed.
Lemma lem6880006 (_91912 : int) : (real_of_int _91912) = (real_of_int _91912).
Proof. exact (eq_refl (real_of_int _91912)). Qed.
Lemma lem6880007 (_91912 : int) : (term578 _91912) = (term593 _91912).
Proof. exact (MK_COMB (@lem6880005) (@lem6880006 _91912)). Qed.
Lemma lem6880008 (_91912 : int) : (term577 _91912) = (term593 _91912).
Proof. exact (TRANS (@lem6879905 _91912) (@lem6880007 _91912)). Qed.
Lemma lem6880009 (_91912 : int) : (term593 _91912) = term214.
Proof. exact (@lem1982719 (real_of_int _91912)). Qed.
Lemma lem6880010 (_91912 : int) : (term577 _91912) = term214.
Proof. exact (TRANS (@lem6880008 _91912) (@lem6880009 _91912)). Qed.
Lemma lem6880011 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6880012 (_91912 : int) : (term594 _91912) = term256.
Proof. exact (MK_COMB (@lem6880011) (@lem6880010 _91912)). Qed.
Lemma lem6880013 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem6880014 (_91912 : int) : (term654 _91912) = term599.
Proof. exact (MK_COMB (@lem6880012 _91912) (@lem6880013)). Qed.
Lemma lem6880015 (_91912 : int) : (term653 _91912) = term599.
Proof. exact (TRANS (@lem6879904 _91912) (@lem6880014 _91912)). Qed.
Lemma lem6880016 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6880017 (_91912 : int) : (term653 _91912) = term279.
Proof. exact (TRANS (@lem6880015 _91912) (@lem6880016)). Qed.
Lemma lem6880018 (_91911 : int) : (term313 _91911) = (term313 _91911).
Proof. exact (eq_refl (term313 _91911)). Qed.
Lemma lem6880019 (_91912 : int) (_91911 : int) : (term668 _91911 _91912) = (term314 _91911).
Proof. exact (MK_COMB (@lem6880018 _91911) (@lem6880017 _91912)). Qed.
Lemma lem6880020 (_91912 : int) (_91911 : int) : (term667 _91911 _91912) = (term314 _91911).
Proof. exact (TRANS (@lem6879903 _91911 _91912) (@lem6880019 _91912 _91911)). Qed.
Lemma lem6880021 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6880022 (_91912 : int) (_91911 : int) : (term685 _91911 _91912) = (term372 _91911).
Proof. exact (MK_COMB (@lem6880021) (@lem6880020 _91912 _91911)). Qed.
Lemma lem6880023 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6880024 (_91912 : int) (_91911 : int) : (term684 _91911 _91912) = (term373 _91911).
Proof. exact (MK_COMB (@lem6880022 _91912 _91911) (@lem6880023)). Qed.
Lemma lem6880025 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term373 _91911.
Proof. exact (EQ_MP (@lem6880024 _91912 _91911) (@lem6879902 _91911 _91912 h1)). Qed.
Lemma lem6880027 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6880028 : term551 = term331.
Proof. exact (@lem6880027 term214 term224). Qed.
Lemma lem6880030 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6880031 : term224 = term304.
Proof. exact (@lem6880030 term92). Qed.
Lemma lem6880033 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6880034 : term214 = term276.
Proof. exact (@lem6880033 (NUMERAL 0)). Qed.
Lemma lem6880035 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6880036 : term552 = term553.
Proof. exact (MK_COMB (@lem6880035) (@lem6880034)). Qed.
Lemma lem6880037 : term331 = term554.
Proof. exact (MK_COMB (@lem6880036) (@lem6880031)). Qed.
Lemma lem6880038 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6880040 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880041 : term331 = term332.
Proof. exact (@lem6880040 (NUMERAL 0) term92). Qed.
Lemma lem6880042 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880043 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880044 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880043 h1) (fun h1 : term332 = True => @lem6880042)). Qed.
Lemma lem6880045 : term332 = True.
Proof. exact (EQ_MP (@lem6880044) (@lem6880042)). Qed.
Lemma lem6880046 : term331 = True.
Proof. exact (TRANS (@lem6880041) (@lem6880045)). Qed.
Lemma lem6880047 : True = term331.
Proof. exact (SYM (@lem6880046)). Qed.
Lemma lem6880048 : term331.
Proof. exact (EQ_MP (@lem6880047) (@lem0)). Qed.
Lemma lem6880049 : term556.
Proof. exact (@lem6880038 (@lem6880048)). Qed.
Lemma lem6880051 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880052 : term331 = term332.
Proof. exact (@lem6880051 (NUMERAL 0) term92). Qed.
Lemma lem6880053 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880054 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880055 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880054 h1) (fun h1 : term332 = True => @lem6880053)). Qed.
Lemma lem6880056 : term332 = True.
Proof. exact (EQ_MP (@lem6880055) (@lem6880053)). Qed.
Lemma lem6880057 : term331 = True.
Proof. exact (TRANS (@lem6880052) (@lem6880056)). Qed.
Lemma lem6880058 : True = term331.
Proof. exact (SYM (@lem6880057)). Qed.
Lemma lem6880059 : term331.
Proof. exact (EQ_MP (@lem6880058) (@lem0)). Qed.
Lemma lem6880060 : term554 = term557.
Proof. exact (@lem6880049 (@lem6880059)). Qed.
Lemma lem6880062 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6880063 : term288 = term289.
Proof. exact (@lem6880062 term92 term92). Qed.
Lemma lem6880064 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880065 : term291 = term92.
Proof. exact (EQ_MP (@lem6880064) (@lem940073)). Qed.
Lemma lem6880066 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880067 : term289 = term224.
Proof. exact (MK_COMB (@lem6880066) (@lem6880065)). Qed.
Lemma lem6880068 : term288 = term224.
Proof. exact (TRANS (@lem6880063) (@lem6880067)). Qed.
Lemma lem6880070 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6880071 : term343 = term214.
Proof. exact (@lem6880070 term92). Qed.
Lemma lem6880072 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6880073 : term558 = term552.
Proof. exact (MK_COMB (@lem6880072) (@lem6880071)). Qed.
Lemma lem6880074 : term557 = term331.
Proof. exact (MK_COMB (@lem6880073) (@lem6880068)). Qed.
Lemma lem6880076 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880077 : term331 = term332.
Proof. exact (@lem6880076 (NUMERAL 0) term92). Qed.
Lemma lem6880078 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880079 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880080 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880079 h1) (fun h1 : term332 = True => @lem6880078)). Qed.
Lemma lem6880081 : term332 = True.
Proof. exact (EQ_MP (@lem6880080) (@lem6880078)). Qed.
Lemma lem6880082 : term331 = True.
Proof. exact (TRANS (@lem6880077) (@lem6880081)). Qed.
Lemma lem6880083 : term557 = True.
Proof. exact (TRANS (@lem6880074) (@lem6880082)). Qed.
Lemma lem6880084 : term554 = True.
Proof. exact (TRANS (@lem6880060) (@lem6880083)). Qed.
Lemma lem6880085 : term331 = True.
Proof. exact (TRANS (@lem6880037) (@lem6880084)). Qed.
Lemma lem6880086 : term551 = True.
Proof. exact (TRANS (@lem6880028) (@lem6880085)). Qed.
Lemma lem6880087 : True = term551.
Proof. exact (SYM (@lem6880086)). Qed.
Lemma lem6880088 : term551.
Proof. exact (EQ_MP (@lem6880087) (@lem0)). Qed.
Lemma lem6880089 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term686 _91911.
Proof. exact (conj (@lem6880088) (@lem6880025 _91911 _91912 h1)). Qed.
Lemma lem6880091 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6880092 (_91911 : int) : term687 _91911.
Proof. exact (@lem6880091 term224 (term314 _91911)). Qed.
Lemma lem6880093 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term688 _91911.
Proof. exact (@lem6880092 _91911 (@lem6880089 _91911 _91912 h1)). Qed.
Lemma lem6880094 (_91911 : int) : (term674 _91911) = (term314 _91911).
Proof. exact (@lem1982733 (term314 _91911)). Qed.
Lemma lem6880095 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6880096 (_91911 : int) : (term689 _91911) = (term372 _91911).
Proof. exact (MK_COMB (@lem6880095) (@lem6880094 _91911)). Qed.
Lemma lem6880097 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6880098 (_91911 : int) : (term688 _91911) = (term373 _91911).
Proof. exact (MK_COMB (@lem6880096 _91911) (@lem6880097)). Qed.
Lemma lem6880099 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term373 _91911.
Proof. exact (EQ_MP (@lem6880098 _91911) (@lem6880093 _91911 _91912 h1)). Qed.
Lemma lem6880101 (y : real) : term565 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6880102 (_91911 : int) : term619 _91911.
Proof. exact (@lem6880101 (real_of_int _91911)). Qed.
Lemma lem6880103 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term620 _91911.
Proof. exact (@lem6880102 _91911 (@lem6879807 _91911 _91912 h1)). Qed.
Lemma lem6880104 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term621 _91911.
Proof. exact (@lem6880103 _91911 _91912 h1 term224). Qed.
Lemma lem6880105 (_91911 : int) : (term621 _91911) = ((term622 _91911) = term214).
Proof. exact (eq_refl (term621 _91911)). Qed.
Lemma lem6880106 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : (term622 _91911) = term214.
Proof. exact (EQ_MP (@lem6880105 _91911) (@lem6880104 _91911 _91912 h1)). Qed.
Lemma lem6880107 (_91911 : int) : (term622 _91911) = (real_of_int _91911).
Proof. exact (@lem1982733 (real_of_int _91911)). Qed.
Lemma lem6880108 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6880109 (_91911 : int) : (term623 _91911) = (term227 _91911).
Proof. exact (MK_COMB (@lem6880108) (@lem6880107 _91911)). Qed.
Lemma lem6880110 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6880111 (_91911 : int) : ((term622 _91911) = term214) = ((real_of_int _91911) = term214).
Proof. exact (MK_COMB (@lem6880109 _91911) (@lem6880110)). Qed.
Lemma lem6880112 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : (real_of_int _91911) = term214.
Proof. exact (EQ_MP (@lem6880111 _91911) (@lem6880106 _91911 _91912 h1)). Qed.
Lemma lem6880113 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term427 _91911.
Proof. exact (conj (@lem6880112 _91911 _91912 h1) (@lem6880099 _91911 _91912 h1)). Qed.
Lemma lem6880115 (x : real) (y : real) : term572 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6880116 (_91911 : int) : term690 _91911.
Proof. exact (@lem6880115 (real_of_int _91911) (term314 _91911)). Qed.
Lemma lem6880117 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term691 _91911.
Proof. exact (@lem6880116 _91911 (@lem6880113 _91911 _91912 h1)). Qed.
Lemma lem6880118 (_91911 : int) : (term692 _91911) = (term596 _91911).
Proof. exact (@lem1982763 (real_of_int _91911) (term317 _91911) term279). Qed.
Lemma lem6880119 (_91911 : int) : (term597 _91911) = (term578 _91911).
Proof. exact (@lem1982715 term279 (real_of_int _91911)). Qed.
Lemma lem6880121 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6880122 : term224 = term304.
Proof. exact (@lem6880121 term92). Qed.
Lemma lem6880124 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6880125 : term279 = term280.
Proof. exact (@lem6880124 term92). Qed.
Lemma lem6880126 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6880127 : term579 = term580.
Proof. exact (MK_COMB (@lem6880126) (@lem6880125)). Qed.
Lemma lem6880128 : term581 = term582.
Proof. exact (MK_COMB (@lem6880127) (@lem6880122)). Qed.
Lemma lem6880129 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6880131 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880132 : term331 = term332.
Proof. exact (@lem6880131 (NUMERAL 0) term92). Qed.
Lemma lem6880133 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880134 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880135 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880134 h1) (fun h1 : term332 = True => @lem6880133)). Qed.
Lemma lem6880136 : term332 = True.
Proof. exact (EQ_MP (@lem6880135) (@lem6880133)). Qed.
Lemma lem6880137 : term331 = True.
Proof. exact (TRANS (@lem6880132) (@lem6880136)). Qed.
Lemma lem6880138 : True = term331.
Proof. exact (SYM (@lem6880137)). Qed.
Lemma lem6880139 : term331.
Proof. exact (EQ_MP (@lem6880138) (@lem0)). Qed.
Lemma lem6880140 : term584.
Proof. exact (@lem6880129 (@lem6880139)). Qed.
Lemma lem6880142 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880143 : term331 = term332.
Proof. exact (@lem6880142 (NUMERAL 0) term92). Qed.
Lemma lem6880144 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880145 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880146 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880145 h1) (fun h1 : term332 = True => @lem6880144)). Qed.
Lemma lem6880147 : term332 = True.
Proof. exact (EQ_MP (@lem6880146) (@lem6880144)). Qed.
Lemma lem6880148 : term331 = True.
Proof. exact (TRANS (@lem6880143) (@lem6880147)). Qed.
Lemma lem6880149 : True = term331.
Proof. exact (SYM (@lem6880148)). Qed.
Lemma lem6880150 : term331.
Proof. exact (EQ_MP (@lem6880149) (@lem0)). Qed.
Lemma lem6880151 : term585.
Proof. exact (@lem6880140 (@lem6880150)). Qed.
Lemma lem6880153 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880154 : term331 = term332.
Proof. exact (@lem6880153 (NUMERAL 0) term92). Qed.
Lemma lem6880155 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880156 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880157 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880156 h1) (fun h1 : term332 = True => @lem6880155)). Qed.
Lemma lem6880158 : term332 = True.
Proof. exact (EQ_MP (@lem6880157) (@lem6880155)). Qed.
Lemma lem6880159 : term331 = True.
Proof. exact (TRANS (@lem6880154) (@lem6880158)). Qed.
Lemma lem6880160 : True = term331.
Proof. exact (SYM (@lem6880159)). Qed.
Lemma lem6880161 : term331.
Proof. exact (EQ_MP (@lem6880160) (@lem0)). Qed.
Lemma lem6880162 : term586.
Proof. exact (@lem6880151 (@lem6880161)). Qed.
Lemma lem6880164 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6880165 : term288 = term289.
Proof. exact (@lem6880164 term92 term92). Qed.
Lemma lem6880166 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880167 : term291 = term92.
Proof. exact (EQ_MP (@lem6880166) (@lem940073)). Qed.
Lemma lem6880168 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880169 : term289 = term224.
Proof. exact (MK_COMB (@lem6880168) (@lem6880167)). Qed.
Lemma lem6880170 : term288 = term224.
Proof. exact (TRANS (@lem6880165) (@lem6880169)). Qed.
Lemma lem6880172 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6880173 : term305 = term310.
Proof. exact (@lem6880172 term92 term92). Qed.
Lemma lem6880174 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880175 : term291 = term92.
Proof. exact (EQ_MP (@lem6880174) (@lem940073)). Qed.
Lemma lem6880176 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880177 : term289 = term224.
Proof. exact (MK_COMB (@lem6880176) (@lem6880175)). Qed.
Lemma lem6880178 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6880179 : term310 = term279.
Proof. exact (MK_COMB (@lem6880178) (@lem6880177)). Qed.
Lemma lem6880180 : term305 = term279.
Proof. exact (TRANS (@lem6880173) (@lem6880179)). Qed.
Lemma lem6880181 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6880182 : term587 = term579.
Proof. exact (MK_COMB (@lem6880181) (@lem6880180)). Qed.
Lemma lem6880183 : term588 = term581.
Proof. exact (MK_COMB (@lem6880182) (@lem6880170)). Qed.
Lemma lem6880185 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6880186 : term581 = term214.
Proof. exact (@lem6880185 term92). Qed.
Lemma lem6880187 : term588 = term214.
Proof. exact (TRANS (@lem6880183) (@lem6880186)). Qed.
Lemma lem6880188 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6880189 : term590 = term341.
Proof. exact (MK_COMB (@lem6880188) (@lem6880187)). Qed.
Lemma lem6880190 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6880191 : term591 = term343.
Proof. exact (MK_COMB (@lem6880189) (@lem6880190)). Qed.
Lemma lem6880193 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6880194 : term343 = term214.
Proof. exact (@lem6880193 term92). Qed.
Lemma lem6880195 : term591 = term214.
Proof. exact (TRANS (@lem6880191) (@lem6880194)). Qed.
Lemma lem6880197 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6880198 : term288 = term289.
Proof. exact (@lem6880197 term92 term92). Qed.
Lemma lem6880199 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880200 : term291 = term92.
Proof. exact (EQ_MP (@lem6880199) (@lem940073)). Qed.
Lemma lem6880201 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880202 : term289 = term224.
Proof. exact (MK_COMB (@lem6880201) (@lem6880200)). Qed.
Lemma lem6880203 : term288 = term224.
Proof. exact (TRANS (@lem6880198) (@lem6880202)). Qed.
Lemma lem6880204 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6880205 : term345 = term343.
Proof. exact (MK_COMB (@lem6880204) (@lem6880203)). Qed.
Lemma lem6880207 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6880208 : term343 = term214.
Proof. exact (@lem6880207 term92). Qed.
Lemma lem6880209 : term345 = term214.
Proof. exact (TRANS (@lem6880205) (@lem6880208)). Qed.
Lemma lem6880210 : term214 = term345.
Proof. exact (SYM (@lem6880209)). Qed.
Lemma lem6880211 : term591 = term345.
Proof. exact (TRANS (@lem6880195) (@lem6880210)). Qed.
Lemma lem6880212 : term582 = term276.
Proof. exact (@lem6880162 (@lem6880211)). Qed.
Lemma lem6880213 : term581 = term276.
Proof. exact (TRANS (@lem6880128) (@lem6880212)). Qed.
Lemma lem6880215 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6880216 : term276 = term214.
Proof. exact (@lem6880215 term214). Qed.
Lemma lem6880217 : term581 = term214.
Proof. exact (TRANS (@lem6880213) (@lem6880216)). Qed.
Lemma lem6880218 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6880219 : term592 = term341.
Proof. exact (MK_COMB (@lem6880218) (@lem6880217)). Qed.
Lemma lem6880220 (_91911 : int) : (real_of_int _91911) = (real_of_int _91911).
Proof. exact (eq_refl (real_of_int _91911)). Qed.
Lemma lem6880221 (_91911 : int) : (term578 _91911) = (term593 _91911).
Proof. exact (MK_COMB (@lem6880219) (@lem6880220 _91911)). Qed.
Lemma lem6880222 (_91911 : int) : (term597 _91911) = (term593 _91911).
Proof. exact (TRANS (@lem6880119 _91911) (@lem6880221 _91911)). Qed.
Lemma lem6880223 (_91911 : int) : (term593 _91911) = term214.
Proof. exact (@lem1982719 (real_of_int _91911)). Qed.
Lemma lem6880224 (_91911 : int) : (term597 _91911) = term214.
Proof. exact (TRANS (@lem6880222 _91911) (@lem6880223 _91911)). Qed.
Lemma lem6880225 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6880226 (_91911 : int) : (term598 _91911) = term256.
Proof. exact (MK_COMB (@lem6880225) (@lem6880224 _91911)). Qed.
Lemma lem6880227 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem6880228 (_91911 : int) : (term596 _91911) = term599.
Proof. exact (MK_COMB (@lem6880226 _91911) (@lem6880227)). Qed.
Lemma lem6880229 (_91911 : int) : (term692 _91911) = term599.
Proof. exact (TRANS (@lem6880118 _91911) (@lem6880228 _91911)). Qed.
Lemma lem6880230 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6880231 (_91911 : int) : (term692 _91911) = term279.
Proof. exact (TRANS (@lem6880229 _91911) (@lem6880230)). Qed.
Lemma lem6880232 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6880233 (_91911 : int) : (term693 _91911) = term601.
Proof. exact (MK_COMB (@lem6880232) (@lem6880231 _91911)). Qed.
Lemma lem6880234 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6880235 (_91911 : int) : (term691 _91911) = term602.
Proof. exact (MK_COMB (@lem6880233 _91911) (@lem6880234)). Qed.
Lemma lem6880236 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : term602.
Proof. exact (EQ_MP (@lem6880235 _91911) (@lem6880117 _91911 _91912 h1)). Qed.
Lemma lem6880238 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6880239 : term602 = term603.
Proof. exact (@lem6880238 term214 term279). Qed.
Lemma lem6880241 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6880242 : term279 = term280.
Proof. exact (@lem6880241 term92). Qed.
Lemma lem6880244 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6880245 : term214 = term276.
Proof. exact (@lem6880244 (NUMERAL 0)). Qed.
Lemma lem6880246 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6880247 : term216 = term604.
Proof. exact (MK_COMB (@lem6880246) (@lem6880245)). Qed.
Lemma lem6880248 : term603 = term605.
Proof. exact (MK_COMB (@lem6880247) (@lem6880242)). Qed.
Lemma lem6880249 : term606.
Proof. exact (@lem1980026 term214 term224 term279 term224). Qed.
Lemma lem6880251 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880252 : term331 = term332.
Proof. exact (@lem6880251 (NUMERAL 0) term92). Qed.
Lemma lem6880253 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880254 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880255 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880254 h1) (fun h1 : term332 = True => @lem6880253)). Qed.
Lemma lem6880256 : term332 = True.
Proof. exact (EQ_MP (@lem6880255) (@lem6880253)). Qed.
Lemma lem6880257 : term331 = True.
Proof. exact (TRANS (@lem6880252) (@lem6880256)). Qed.
Lemma lem6880258 : True = term331.
Proof. exact (SYM (@lem6880257)). Qed.
Lemma lem6880259 : term331.
Proof. exact (EQ_MP (@lem6880258) (@lem0)). Qed.
Lemma lem6880260 : term607.
Proof. exact (@lem6880249 (@lem6880259)). Qed.
Lemma lem6880262 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880263 : term331 = term332.
Proof. exact (@lem6880262 (NUMERAL 0) term92). Qed.
Lemma lem6880264 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880265 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880266 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880265 h1) (fun h1 : term332 = True => @lem6880264)). Qed.
Lemma lem6880267 : term332 = True.
Proof. exact (EQ_MP (@lem6880266) (@lem6880264)). Qed.
Lemma lem6880268 : term331 = True.
Proof. exact (TRANS (@lem6880263) (@lem6880267)). Qed.
Lemma lem6880269 : True = term331.
Proof. exact (SYM (@lem6880268)). Qed.
Lemma lem6880270 : term331.
Proof. exact (EQ_MP (@lem6880269) (@lem0)). Qed.
Lemma lem6880271 : term605 = term608.
Proof. exact (@lem6880260 (@lem6880270)). Qed.
Lemma lem6880273 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6880274 : term305 = term310.
Proof. exact (@lem6880273 term92 term92). Qed.
Lemma lem6880275 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880276 : term291 = term92.
Proof. exact (EQ_MP (@lem6880275) (@lem940073)). Qed.
Lemma lem6880277 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880278 : term289 = term224.
Proof. exact (MK_COMB (@lem6880277) (@lem6880276)). Qed.
Lemma lem6880279 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6880280 : term310 = term279.
Proof. exact (MK_COMB (@lem6880279) (@lem6880278)). Qed.
Lemma lem6880281 : term305 = term279.
Proof. exact (TRANS (@lem6880274) (@lem6880280)). Qed.
Lemma lem6880283 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6880284 : term343 = term214.
Proof. exact (@lem6880283 term92). Qed.
Lemma lem6880285 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6880286 : term609 = term216.
Proof. exact (MK_COMB (@lem6880285) (@lem6880284)). Qed.
Lemma lem6880287 : term608 = term603.
Proof. exact (MK_COMB (@lem6880286) (@lem6880281)). Qed.
Lemma lem6880289 (m : nat) (n : nat) : (term610 m n) = (term611 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6880290 : term603 = term612.
Proof. exact (@lem6880289 (NUMERAL 0) term92). Qed.
Lemma lem6880291 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880292 (h1 : term333 = (BIT1 0)) : (term92 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6880293 : (term333 = (BIT1 0)) = ((term92 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880292 h1) (fun h1 : (term92 = (NUMERAL 0)) = False => @lem6880291)). Qed.
Lemma lem6880294 : (term92 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6880293) (@lem6880291)). Qed.
Lemma lem6880295 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6880296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6880297 : term613 = (and True).
Proof. exact (MK_COMB (@lem6880296) (@lem6880295)). Qed.
Lemma lem6880298 : term612 = (True /\ False).
Proof. exact (MK_COMB (@lem6880297) (@lem6880294)). Qed.
Lemma lem6880300 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6880301 : term612 = False.
Proof. exact (TRANS (@lem6880298) (@lem6880300)). Qed.
Lemma lem6880302 : term603 = False.
Proof. exact (TRANS (@lem6880290) (@lem6880301)). Qed.
Lemma lem6880303 : term608 = False.
Proof. exact (TRANS (@lem6880287) (@lem6880302)). Qed.
Lemma lem6880304 : term605 = False.
Proof. exact (TRANS (@lem6880271) (@lem6880303)). Qed.
Lemma lem6880305 : term603 = False.
Proof. exact (TRANS (@lem6880248) (@lem6880304)). Qed.
Lemma lem6880306 : term602 = False.
Proof. exact (TRANS (@lem6880239) (@lem6880305)). Qed.
Lemma lem6880307 (_91911 : int) (_91912 : int) (h1 : term681 _91911 _91912) : False.
Proof. exact (EQ_MP (@lem6880306) (@lem6880236 _91911 _91912 h1)). Qed.
Lemma lem6880308 (_91911 : int) (_91912 : int) (h1 : term537 _91911 _91912) : False.
Proof. exact (or_elim (@lem6879293 _91911 _91912 h1) (fun h0 : term656 _91911 _91912 => @lem6879799 _91911 _91912 h0) (fun h0 : term681 _91911 _91912 => @lem6880307 _91911 _91912 h0)). Qed.
Lemma lem6880309 (_91911 : int) (_91912 : int) (h1 : term546 _91911 _91912) : False.
Proof. exact (or_elim (@lem6878110 _91911 _91912 h1) (fun h0 : term541 _91911 _91912 => @lem6879292 _91911 _91912 h0) (fun h0 : term537 _91911 _91912 => @lem6880308 _91911 _91912 h0)). Qed.
Lemma lem6880310 (_91911 : int) (_91912 : int) (h1 : term533 _91911 _91912) : term533 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6880311 (_91911 : int) (_91912 : int) (h1 : term530 _91911 _91912) : term530 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6880312 (_91911 : int) (_91912 : int) (h1 : term525 _91911 _91912) : term525 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6880313 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : term694 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6880314 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : term526 _91911 _91912.
Proof. exact (proj2 (@lem6880313 _91911 _91912 h1)). Qed.
Lemma lem6880316 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : term477 _91911 _91912.
Proof. exact (proj2 (@lem6880314 _91911 _91912 h1)). Qed.
Lemma lem6880318 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : term426 _91911 _91912.
Proof. exact (proj2 (@lem6880316 _91911 _91912 h1)). Qed.
Lemma lem6880319 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : (term316 _91911 _91912) = term214.
Proof. exact (proj1 (@lem6880316 _91911 _91912 h1)). Qed.
Lemma lem6880321 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : term360 _91911 _91912.
Proof. exact (proj1 (@lem6880318 _91911 _91912 h1)). Qed.
Lemma lem6880323 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6880324 : term551 = term331.
Proof. exact (@lem6880323 term214 term224). Qed.
Lemma lem6880326 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6880327 : term224 = term304.
Proof. exact (@lem6880326 term92). Qed.
Lemma lem6880329 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6880330 : term214 = term276.
Proof. exact (@lem6880329 (NUMERAL 0)). Qed.
Lemma lem6880331 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6880332 : term552 = term553.
Proof. exact (MK_COMB (@lem6880331) (@lem6880330)). Qed.
Lemma lem6880333 : term331 = term554.
Proof. exact (MK_COMB (@lem6880332) (@lem6880327)). Qed.
Lemma lem6880334 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6880336 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880337 : term331 = term332.
Proof. exact (@lem6880336 (NUMERAL 0) term92). Qed.
Lemma lem6880338 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880339 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880340 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880339 h1) (fun h1 : term332 = True => @lem6880338)). Qed.
Lemma lem6880341 : term332 = True.
Proof. exact (EQ_MP (@lem6880340) (@lem6880338)). Qed.
Lemma lem6880342 : term331 = True.
Proof. exact (TRANS (@lem6880337) (@lem6880341)). Qed.
Lemma lem6880343 : True = term331.
Proof. exact (SYM (@lem6880342)). Qed.
Lemma lem6880344 : term331.
Proof. exact (EQ_MP (@lem6880343) (@lem0)). Qed.
Lemma lem6880345 : term556.
Proof. exact (@lem6880334 (@lem6880344)). Qed.
Lemma lem6880347 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880348 : term331 = term332.
Proof. exact (@lem6880347 (NUMERAL 0) term92). Qed.
Lemma lem6880349 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880350 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880351 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880350 h1) (fun h1 : term332 = True => @lem6880349)). Qed.
Lemma lem6880352 : term332 = True.
Proof. exact (EQ_MP (@lem6880351) (@lem6880349)). Qed.
Lemma lem6880353 : term331 = True.
Proof. exact (TRANS (@lem6880348) (@lem6880352)). Qed.
Lemma lem6880354 : True = term331.
Proof. exact (SYM (@lem6880353)). Qed.
Lemma lem6880355 : term331.
Proof. exact (EQ_MP (@lem6880354) (@lem0)). Qed.
Lemma lem6880356 : term554 = term557.
Proof. exact (@lem6880345 (@lem6880355)). Qed.
Lemma lem6880358 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6880359 : term288 = term289.
Proof. exact (@lem6880358 term92 term92). Qed.
Lemma lem6880360 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880361 : term291 = term92.
Proof. exact (EQ_MP (@lem6880360) (@lem940073)). Qed.
Lemma lem6880362 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880363 : term289 = term224.
Proof. exact (MK_COMB (@lem6880362) (@lem6880361)). Qed.
Lemma lem6880364 : term288 = term224.
Proof. exact (TRANS (@lem6880359) (@lem6880363)). Qed.
Lemma lem6880366 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6880367 : term343 = term214.
Proof. exact (@lem6880366 term92). Qed.
Lemma lem6880368 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6880369 : term558 = term552.
Proof. exact (MK_COMB (@lem6880368) (@lem6880367)). Qed.
Lemma lem6880370 : term557 = term331.
Proof. exact (MK_COMB (@lem6880369) (@lem6880364)). Qed.
Lemma lem6880372 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880373 : term331 = term332.
Proof. exact (@lem6880372 (NUMERAL 0) term92). Qed.
Lemma lem6880374 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880375 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880376 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880375 h1) (fun h1 : term332 = True => @lem6880374)). Qed.
Lemma lem6880377 : term332 = True.
Proof. exact (EQ_MP (@lem6880376) (@lem6880374)). Qed.
Lemma lem6880378 : term331 = True.
Proof. exact (TRANS (@lem6880373) (@lem6880377)). Qed.
Lemma lem6880379 : term557 = True.
Proof. exact (TRANS (@lem6880370) (@lem6880378)). Qed.
Lemma lem6880380 : term554 = True.
Proof. exact (TRANS (@lem6880356) (@lem6880379)). Qed.
Lemma lem6880381 : term331 = True.
Proof. exact (TRANS (@lem6880333) (@lem6880380)). Qed.
Lemma lem6880382 : term551 = True.
Proof. exact (TRANS (@lem6880324) (@lem6880381)). Qed.
Lemma lem6880383 : True = term551.
Proof. exact (SYM (@lem6880382)). Qed.
Lemma lem6880384 : term551.
Proof. exact (EQ_MP (@lem6880383) (@lem0)). Qed.
Lemma lem6880385 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : term559 _91911 _91912.
Proof. exact (conj (@lem6880384) (@lem6880321 _91911 _91912 h1)). Qed.
Lemma lem6880387 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6880388 (_91911 : int) (_91912 : int) : term561 _91911 _91912.
Proof. exact (@lem6880387 term224 (term357 _91911 _91912)). Qed.
Lemma lem6880389 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : term562 _91911 _91912.
Proof. exact (@lem6880388 _91911 _91912 (@lem6880385 _91911 _91912 h1)). Qed.
Lemma lem6880390 (_91911 : int) (_91912 : int) : (term563 _91911 _91912) = (term357 _91911 _91912).
Proof. exact (@lem1982733 (term357 _91911 _91912)). Qed.
Lemma lem6880391 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6880392 (_91911 : int) (_91912 : int) : (term564 _91911 _91912) = (term359 _91911 _91912).
Proof. exact (MK_COMB (@lem6880391) (@lem6880390 _91911 _91912)). Qed.
Lemma lem6880393 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6880394 (_91911 : int) (_91912 : int) : (term562 _91911 _91912) = (term360 _91911 _91912).
Proof. exact (MK_COMB (@lem6880392 _91911 _91912) (@lem6880393)). Qed.
Lemma lem6880395 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : term360 _91911 _91912.
Proof. exact (EQ_MP (@lem6880394 _91911 _91912) (@lem6880389 _91911 _91912 h1)). Qed.
Lemma lem6880397 (y : real) : term565 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6880398 (_91911 : int) (_91912 : int) : term566 _91911 _91912.
Proof. exact (@lem6880397 (term316 _91911 _91912)). Qed.
Lemma lem6880399 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : term567 _91911 _91912.
Proof. exact (@lem6880398 _91911 _91912 (@lem6880319 _91911 _91912 h1)). Qed.
Lemma lem6880400 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : term568 _91911 _91912.
Proof. exact (@lem6880399 _91911 _91912 h1 term224). Qed.
Lemma lem6880401 (_91911 : int) (_91912 : int) : (term568 _91911 _91912) = ((term569 _91911 _91912) = term214).
Proof. exact (eq_refl (term568 _91911 _91912)). Qed.
Lemma lem6880402 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : (term569 _91911 _91912) = term214.
Proof. exact (EQ_MP (@lem6880401 _91911 _91912) (@lem6880400 _91911 _91912 h1)). Qed.
Lemma lem6880403 (_91911 : int) (_91912 : int) : (term569 _91911 _91912) = (term316 _91911 _91912).
Proof. exact (@lem1982733 (term316 _91911 _91912)). Qed.
Lemma lem6880404 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6880405 (_91911 : int) (_91912 : int) : (term570 _91911 _91912) = (term319 _91911 _91912).
Proof. exact (MK_COMB (@lem6880404) (@lem6880403 _91911 _91912)). Qed.
Lemma lem6880406 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6880407 (_91911 : int) (_91912 : int) : ((term569 _91911 _91912) = term214) = ((term316 _91911 _91912) = term214).
Proof. exact (MK_COMB (@lem6880405 _91911 _91912) (@lem6880406)). Qed.
Lemma lem6880408 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : (term316 _91911 _91912) = term214.
Proof. exact (EQ_MP (@lem6880407 _91911 _91912) (@lem6880402 _91911 _91912 h1)). Qed.
Lemma lem6880409 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : term571 _91911 _91912.
Proof. exact (conj (@lem6880408 _91911 _91912 h1) (@lem6880395 _91911 _91912 h1)). Qed.
Lemma lem6880411 (x : real) (y : real) : term572 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6880412 (_91911 : int) (_91912 : int) : term573 _91911 _91912.
Proof. exact (@lem6880411 (term316 _91911 _91912) (term357 _91911 _91912)). Qed.
Lemma lem6880413 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : term574 _91911 _91912.
Proof. exact (@lem6880412 _91911 _91912 (@lem6880409 _91911 _91912 h1)). Qed.
Lemma lem6880414 (_91911 : int) (_91912 : int) : (term575 _91911 _91912) = (term576 _91911 _91912).
Proof. exact (@lem1982753 (term317 _91911) (real_of_int _91911) (term379 _91912) (term317 _91912)). Qed.
Lemma lem6880415 (_91911 : int) : (term577 _91911) = (term578 _91911).
Proof. exact (@lem1982713 term279 (real_of_int _91911)). Qed.
Lemma lem6880417 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6880418 : term224 = term304.
Proof. exact (@lem6880417 term92). Qed.
Lemma lem6880420 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6880421 : term279 = term280.
Proof. exact (@lem6880420 term92). Qed.
Lemma lem6880422 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6880423 : term579 = term580.
Proof. exact (MK_COMB (@lem6880422) (@lem6880421)). Qed.
Lemma lem6880424 : term581 = term582.
Proof. exact (MK_COMB (@lem6880423) (@lem6880418)). Qed.
Lemma lem6880425 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6880427 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880428 : term331 = term332.
Proof. exact (@lem6880427 (NUMERAL 0) term92). Qed.
Lemma lem6880429 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880430 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880431 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880430 h1) (fun h1 : term332 = True => @lem6880429)). Qed.
Lemma lem6880432 : term332 = True.
Proof. exact (EQ_MP (@lem6880431) (@lem6880429)). Qed.
Lemma lem6880433 : term331 = True.
Proof. exact (TRANS (@lem6880428) (@lem6880432)). Qed.
Lemma lem6880434 : True = term331.
Proof. exact (SYM (@lem6880433)). Qed.
Lemma lem6880435 : term331.
Proof. exact (EQ_MP (@lem6880434) (@lem0)). Qed.
Lemma lem6880436 : term584.
Proof. exact (@lem6880425 (@lem6880435)). Qed.
Lemma lem6880438 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880439 : term331 = term332.
Proof. exact (@lem6880438 (NUMERAL 0) term92). Qed.
Lemma lem6880440 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880441 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880442 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880441 h1) (fun h1 : term332 = True => @lem6880440)). Qed.
Lemma lem6880443 : term332 = True.
Proof. exact (EQ_MP (@lem6880442) (@lem6880440)). Qed.
Lemma lem6880444 : term331 = True.
Proof. exact (TRANS (@lem6880439) (@lem6880443)). Qed.
Lemma lem6880445 : True = term331.
Proof. exact (SYM (@lem6880444)). Qed.
Lemma lem6880446 : term331.
Proof. exact (EQ_MP (@lem6880445) (@lem0)). Qed.
Lemma lem6880447 : term585.
Proof. exact (@lem6880436 (@lem6880446)). Qed.
Lemma lem6880449 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880450 : term331 = term332.
Proof. exact (@lem6880449 (NUMERAL 0) term92). Qed.
Lemma lem6880451 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880452 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880453 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880452 h1) (fun h1 : term332 = True => @lem6880451)). Qed.
Lemma lem6880454 : term332 = True.
Proof. exact (EQ_MP (@lem6880453) (@lem6880451)). Qed.
Lemma lem6880455 : term331 = True.
Proof. exact (TRANS (@lem6880450) (@lem6880454)). Qed.
Lemma lem6880456 : True = term331.
Proof. exact (SYM (@lem6880455)). Qed.
Lemma lem6880457 : term331.
Proof. exact (EQ_MP (@lem6880456) (@lem0)). Qed.
Lemma lem6880458 : term586.
Proof. exact (@lem6880447 (@lem6880457)). Qed.
Lemma lem6880460 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6880461 : term288 = term289.
Proof. exact (@lem6880460 term92 term92). Qed.
Lemma lem6880462 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880463 : term291 = term92.
Proof. exact (EQ_MP (@lem6880462) (@lem940073)). Qed.
Lemma lem6880464 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880465 : term289 = term224.
Proof. exact (MK_COMB (@lem6880464) (@lem6880463)). Qed.
Lemma lem6880466 : term288 = term224.
Proof. exact (TRANS (@lem6880461) (@lem6880465)). Qed.
Lemma lem6880468 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6880469 : term305 = term310.
Proof. exact (@lem6880468 term92 term92). Qed.
Lemma lem6880470 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880471 : term291 = term92.
Proof. exact (EQ_MP (@lem6880470) (@lem940073)). Qed.
Lemma lem6880472 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880473 : term289 = term224.
Proof. exact (MK_COMB (@lem6880472) (@lem6880471)). Qed.
Lemma lem6880474 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6880475 : term310 = term279.
Proof. exact (MK_COMB (@lem6880474) (@lem6880473)). Qed.
Lemma lem6880476 : term305 = term279.
Proof. exact (TRANS (@lem6880469) (@lem6880475)). Qed.
Lemma lem6880477 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6880478 : term587 = term579.
Proof. exact (MK_COMB (@lem6880477) (@lem6880476)). Qed.
Lemma lem6880479 : term588 = term581.
Proof. exact (MK_COMB (@lem6880478) (@lem6880466)). Qed.
Lemma lem6880481 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6880482 : term581 = term214.
Proof. exact (@lem6880481 term92). Qed.
Lemma lem6880483 : term588 = term214.
Proof. exact (TRANS (@lem6880479) (@lem6880482)). Qed.
Lemma lem6880484 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6880485 : term590 = term341.
Proof. exact (MK_COMB (@lem6880484) (@lem6880483)). Qed.
Lemma lem6880486 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6880487 : term591 = term343.
Proof. exact (MK_COMB (@lem6880485) (@lem6880486)). Qed.
Lemma lem6880489 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6880490 : term343 = term214.
Proof. exact (@lem6880489 term92). Qed.
Lemma lem6880491 : term591 = term214.
Proof. exact (TRANS (@lem6880487) (@lem6880490)). Qed.
Lemma lem6880493 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6880494 : term288 = term289.
Proof. exact (@lem6880493 term92 term92). Qed.
Lemma lem6880495 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880496 : term291 = term92.
Proof. exact (EQ_MP (@lem6880495) (@lem940073)). Qed.
Lemma lem6880497 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880498 : term289 = term224.
Proof. exact (MK_COMB (@lem6880497) (@lem6880496)). Qed.
Lemma lem6880499 : term288 = term224.
Proof. exact (TRANS (@lem6880494) (@lem6880498)). Qed.
Lemma lem6880500 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6880501 : term345 = term343.
Proof. exact (MK_COMB (@lem6880500) (@lem6880499)). Qed.
Lemma lem6880503 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6880504 : term343 = term214.
Proof. exact (@lem6880503 term92). Qed.
Lemma lem6880505 : term345 = term214.
Proof. exact (TRANS (@lem6880501) (@lem6880504)). Qed.
Lemma lem6880506 : term214 = term345.
Proof. exact (SYM (@lem6880505)). Qed.
Lemma lem6880507 : term591 = term345.
Proof. exact (TRANS (@lem6880491) (@lem6880506)). Qed.
Lemma lem6880508 : term582 = term276.
Proof. exact (@lem6880458 (@lem6880507)). Qed.
Lemma lem6880509 : term581 = term276.
Proof. exact (TRANS (@lem6880424) (@lem6880508)). Qed.
Lemma lem6880511 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6880512 : term276 = term214.
Proof. exact (@lem6880511 term214). Qed.
Lemma lem6880513 : term581 = term214.
Proof. exact (TRANS (@lem6880509) (@lem6880512)). Qed.
Lemma lem6880514 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6880515 : term592 = term341.
Proof. exact (MK_COMB (@lem6880514) (@lem6880513)). Qed.
Lemma lem6880516 (_91911 : int) : (real_of_int _91911) = (real_of_int _91911).
Proof. exact (eq_refl (real_of_int _91911)). Qed.
Lemma lem6880517 (_91911 : int) : (term578 _91911) = (term593 _91911).
Proof. exact (MK_COMB (@lem6880515) (@lem6880516 _91911)). Qed.
Lemma lem6880518 (_91911 : int) : (term577 _91911) = (term593 _91911).
Proof. exact (TRANS (@lem6880415 _91911) (@lem6880517 _91911)). Qed.
Lemma lem6880519 (_91911 : int) : (term593 _91911) = term214.
Proof. exact (@lem1982719 (real_of_int _91911)). Qed.
Lemma lem6880520 (_91911 : int) : (term577 _91911) = term214.
Proof. exact (TRANS (@lem6880518 _91911) (@lem6880519 _91911)). Qed.
Lemma lem6880521 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6880522 (_91911 : int) : (term594 _91911) = term256.
Proof. exact (MK_COMB (@lem6880521) (@lem6880520 _91911)). Qed.
Lemma lem6880523 (_91912 : int) : (term595 _91912) = (term596 _91912).
Proof. exact (@lem1982759 (real_of_int _91912) (term317 _91912) term279). Qed.
Lemma lem6880524 (_91912 : int) : (term597 _91912) = (term578 _91912).
Proof. exact (@lem1982715 term279 (real_of_int _91912)). Qed.
Lemma lem6880526 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6880527 : term224 = term304.
Proof. exact (@lem6880526 term92). Qed.
Lemma lem6880529 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6880530 : term279 = term280.
Proof. exact (@lem6880529 term92). Qed.
Lemma lem6880531 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6880532 : term579 = term580.
Proof. exact (MK_COMB (@lem6880531) (@lem6880530)). Qed.
Lemma lem6880533 : term581 = term582.
Proof. exact (MK_COMB (@lem6880532) (@lem6880527)). Qed.
Lemma lem6880534 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6880536 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880537 : term331 = term332.
Proof. exact (@lem6880536 (NUMERAL 0) term92). Qed.
Lemma lem6880538 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880539 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880540 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880539 h1) (fun h1 : term332 = True => @lem6880538)). Qed.
Lemma lem6880541 : term332 = True.
Proof. exact (EQ_MP (@lem6880540) (@lem6880538)). Qed.
Lemma lem6880542 : term331 = True.
Proof. exact (TRANS (@lem6880537) (@lem6880541)). Qed.
Lemma lem6880543 : True = term331.
Proof. exact (SYM (@lem6880542)). Qed.
Lemma lem6880544 : term331.
Proof. exact (EQ_MP (@lem6880543) (@lem0)). Qed.
Lemma lem6880545 : term584.
Proof. exact (@lem6880534 (@lem6880544)). Qed.
Lemma lem6880547 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880548 : term331 = term332.
Proof. exact (@lem6880547 (NUMERAL 0) term92). Qed.
Lemma lem6880549 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880550 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880551 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880550 h1) (fun h1 : term332 = True => @lem6880549)). Qed.
Lemma lem6880552 : term332 = True.
Proof. exact (EQ_MP (@lem6880551) (@lem6880549)). Qed.
Lemma lem6880553 : term331 = True.
Proof. exact (TRANS (@lem6880548) (@lem6880552)). Qed.
Lemma lem6880554 : True = term331.
Proof. exact (SYM (@lem6880553)). Qed.
Lemma lem6880555 : term331.
Proof. exact (EQ_MP (@lem6880554) (@lem0)). Qed.
Lemma lem6880556 : term585.
Proof. exact (@lem6880545 (@lem6880555)). Qed.
Lemma lem6880558 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880559 : term331 = term332.
Proof. exact (@lem6880558 (NUMERAL 0) term92). Qed.
Lemma lem6880560 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880561 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880562 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880561 h1) (fun h1 : term332 = True => @lem6880560)). Qed.
Lemma lem6880563 : term332 = True.
Proof. exact (EQ_MP (@lem6880562) (@lem6880560)). Qed.
Lemma lem6880564 : term331 = True.
Proof. exact (TRANS (@lem6880559) (@lem6880563)). Qed.
Lemma lem6880565 : True = term331.
Proof. exact (SYM (@lem6880564)). Qed.
Lemma lem6880566 : term331.
Proof. exact (EQ_MP (@lem6880565) (@lem0)). Qed.
Lemma lem6880567 : term586.
Proof. exact (@lem6880556 (@lem6880566)). Qed.
Lemma lem6880569 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6880570 : term288 = term289.
Proof. exact (@lem6880569 term92 term92). Qed.
Lemma lem6880571 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880572 : term291 = term92.
Proof. exact (EQ_MP (@lem6880571) (@lem940073)). Qed.
Lemma lem6880573 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880574 : term289 = term224.
Proof. exact (MK_COMB (@lem6880573) (@lem6880572)). Qed.
Lemma lem6880575 : term288 = term224.
Proof. exact (TRANS (@lem6880570) (@lem6880574)). Qed.
Lemma lem6880577 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6880578 : term305 = term310.
Proof. exact (@lem6880577 term92 term92). Qed.
Lemma lem6880579 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880580 : term291 = term92.
Proof. exact (EQ_MP (@lem6880579) (@lem940073)). Qed.
Lemma lem6880581 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880582 : term289 = term224.
Proof. exact (MK_COMB (@lem6880581) (@lem6880580)). Qed.
Lemma lem6880583 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6880584 : term310 = term279.
Proof. exact (MK_COMB (@lem6880583) (@lem6880582)). Qed.
Lemma lem6880585 : term305 = term279.
Proof. exact (TRANS (@lem6880578) (@lem6880584)). Qed.
Lemma lem6880586 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6880587 : term587 = term579.
Proof. exact (MK_COMB (@lem6880586) (@lem6880585)). Qed.
Lemma lem6880588 : term588 = term581.
Proof. exact (MK_COMB (@lem6880587) (@lem6880575)). Qed.
Lemma lem6880590 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6880591 : term581 = term214.
Proof. exact (@lem6880590 term92). Qed.
Lemma lem6880592 : term588 = term214.
Proof. exact (TRANS (@lem6880588) (@lem6880591)). Qed.
Lemma lem6880593 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6880594 : term590 = term341.
Proof. exact (MK_COMB (@lem6880593) (@lem6880592)). Qed.
Lemma lem6880595 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6880596 : term591 = term343.
Proof. exact (MK_COMB (@lem6880594) (@lem6880595)). Qed.
Lemma lem6880598 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6880599 : term343 = term214.
Proof. exact (@lem6880598 term92). Qed.
Lemma lem6880600 : term591 = term214.
Proof. exact (TRANS (@lem6880596) (@lem6880599)). Qed.
Lemma lem6880602 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6880603 : term288 = term289.
Proof. exact (@lem6880602 term92 term92). Qed.
Lemma lem6880604 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880605 : term291 = term92.
Proof. exact (EQ_MP (@lem6880604) (@lem940073)). Qed.
Lemma lem6880606 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880607 : term289 = term224.
Proof. exact (MK_COMB (@lem6880606) (@lem6880605)). Qed.
Lemma lem6880608 : term288 = term224.
Proof. exact (TRANS (@lem6880603) (@lem6880607)). Qed.
Lemma lem6880609 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6880610 : term345 = term343.
Proof. exact (MK_COMB (@lem6880609) (@lem6880608)). Qed.
Lemma lem6880612 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6880613 : term343 = term214.
Proof. exact (@lem6880612 term92). Qed.
Lemma lem6880614 : term345 = term214.
Proof. exact (TRANS (@lem6880610) (@lem6880613)). Qed.
Lemma lem6880615 : term214 = term345.
Proof. exact (SYM (@lem6880614)). Qed.
Lemma lem6880616 : term591 = term345.
Proof. exact (TRANS (@lem6880600) (@lem6880615)). Qed.
Lemma lem6880617 : term582 = term276.
Proof. exact (@lem6880567 (@lem6880616)). Qed.
Lemma lem6880618 : term581 = term276.
Proof. exact (TRANS (@lem6880533) (@lem6880617)). Qed.
Lemma lem6880620 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6880621 : term276 = term214.
Proof. exact (@lem6880620 term214). Qed.
Lemma lem6880622 : term581 = term214.
Proof. exact (TRANS (@lem6880618) (@lem6880621)). Qed.
Lemma lem6880623 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6880624 : term592 = term341.
Proof. exact (MK_COMB (@lem6880623) (@lem6880622)). Qed.
Lemma lem6880625 (_91912 : int) : (real_of_int _91912) = (real_of_int _91912).
Proof. exact (eq_refl (real_of_int _91912)). Qed.
Lemma lem6880626 (_91912 : int) : (term578 _91912) = (term593 _91912).
Proof. exact (MK_COMB (@lem6880624) (@lem6880625 _91912)). Qed.
Lemma lem6880627 (_91912 : int) : (term597 _91912) = (term593 _91912).
Proof. exact (TRANS (@lem6880524 _91912) (@lem6880626 _91912)). Qed.
Lemma lem6880628 (_91912 : int) : (term593 _91912) = term214.
Proof. exact (@lem1982719 (real_of_int _91912)). Qed.
Lemma lem6880629 (_91912 : int) : (term597 _91912) = term214.
Proof. exact (TRANS (@lem6880627 _91912) (@lem6880628 _91912)). Qed.
Lemma lem6880630 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6880631 (_91912 : int) : (term598 _91912) = term256.
Proof. exact (MK_COMB (@lem6880630) (@lem6880629 _91912)). Qed.
Lemma lem6880632 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem6880633 (_91912 : int) : (term596 _91912) = term599.
Proof. exact (MK_COMB (@lem6880631 _91912) (@lem6880632)). Qed.
Lemma lem6880634 (_91912 : int) : (term595 _91912) = term599.
Proof. exact (TRANS (@lem6880523 _91912) (@lem6880633 _91912)). Qed.
Lemma lem6880635 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6880636 (_91912 : int) : (term595 _91912) = term279.
Proof. exact (TRANS (@lem6880634 _91912) (@lem6880635)). Qed.
Lemma lem6880637 (_91911 : int) (_91912 : int) : (term576 _91911 _91912) = term599.
Proof. exact (MK_COMB (@lem6880522 _91911) (@lem6880636 _91912)). Qed.
Lemma lem6880638 (_91911 : int) (_91912 : int) : (term575 _91911 _91912) = term599.
Proof. exact (TRANS (@lem6880414 _91911 _91912) (@lem6880637 _91911 _91912)). Qed.
Lemma lem6880639 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6880640 (_91911 : int) (_91912 : int) : (term575 _91911 _91912) = term279.
Proof. exact (TRANS (@lem6880638 _91911 _91912) (@lem6880639)). Qed.
Lemma lem6880641 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6880642 (_91911 : int) (_91912 : int) : (term600 _91911 _91912) = term601.
Proof. exact (MK_COMB (@lem6880641) (@lem6880640 _91911 _91912)). Qed.
Lemma lem6880643 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6880644 (_91911 : int) (_91912 : int) : (term574 _91911 _91912) = term602.
Proof. exact (MK_COMB (@lem6880642 _91911 _91912) (@lem6880643)). Qed.
Lemma lem6880645 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : term602.
Proof. exact (EQ_MP (@lem6880644 _91911 _91912) (@lem6880413 _91911 _91912 h1)). Qed.
Lemma lem6880647 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6880648 : term602 = term603.
Proof. exact (@lem6880647 term214 term279). Qed.
Lemma lem6880650 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6880651 : term279 = term280.
Proof. exact (@lem6880650 term92). Qed.
Lemma lem6880653 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6880654 : term214 = term276.
Proof. exact (@lem6880653 (NUMERAL 0)). Qed.
Lemma lem6880655 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6880656 : term216 = term604.
Proof. exact (MK_COMB (@lem6880655) (@lem6880654)). Qed.
Lemma lem6880657 : term603 = term605.
Proof. exact (MK_COMB (@lem6880656) (@lem6880651)). Qed.
Lemma lem6880658 : term606.
Proof. exact (@lem1980026 term214 term224 term279 term224). Qed.
Lemma lem6880660 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880661 : term331 = term332.
Proof. exact (@lem6880660 (NUMERAL 0) term92). Qed.
Lemma lem6880662 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880663 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880664 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880663 h1) (fun h1 : term332 = True => @lem6880662)). Qed.
Lemma lem6880665 : term332 = True.
Proof. exact (EQ_MP (@lem6880664) (@lem6880662)). Qed.
Lemma lem6880666 : term331 = True.
Proof. exact (TRANS (@lem6880661) (@lem6880665)). Qed.
Lemma lem6880667 : True = term331.
Proof. exact (SYM (@lem6880666)). Qed.
Lemma lem6880668 : term331.
Proof. exact (EQ_MP (@lem6880667) (@lem0)). Qed.
Lemma lem6880669 : term607.
Proof. exact (@lem6880658 (@lem6880668)). Qed.
Lemma lem6880671 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880672 : term331 = term332.
Proof. exact (@lem6880671 (NUMERAL 0) term92). Qed.
Lemma lem6880673 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880674 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880675 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880674 h1) (fun h1 : term332 = True => @lem6880673)). Qed.
Lemma lem6880676 : term332 = True.
Proof. exact (EQ_MP (@lem6880675) (@lem6880673)). Qed.
Lemma lem6880677 : term331 = True.
Proof. exact (TRANS (@lem6880672) (@lem6880676)). Qed.
Lemma lem6880678 : True = term331.
Proof. exact (SYM (@lem6880677)). Qed.
Lemma lem6880679 : term331.
Proof. exact (EQ_MP (@lem6880678) (@lem0)). Qed.
Lemma lem6880680 : term605 = term608.
Proof. exact (@lem6880669 (@lem6880679)). Qed.
Lemma lem6880682 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6880683 : term305 = term310.
Proof. exact (@lem6880682 term92 term92). Qed.
Lemma lem6880684 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880685 : term291 = term92.
Proof. exact (EQ_MP (@lem6880684) (@lem940073)). Qed.
Lemma lem6880686 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880687 : term289 = term224.
Proof. exact (MK_COMB (@lem6880686) (@lem6880685)). Qed.
Lemma lem6880688 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6880689 : term310 = term279.
Proof. exact (MK_COMB (@lem6880688) (@lem6880687)). Qed.
Lemma lem6880690 : term305 = term279.
Proof. exact (TRANS (@lem6880683) (@lem6880689)). Qed.
Lemma lem6880692 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6880693 : term343 = term214.
Proof. exact (@lem6880692 term92). Qed.
Lemma lem6880694 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6880695 : term609 = term216.
Proof. exact (MK_COMB (@lem6880694) (@lem6880693)). Qed.
Lemma lem6880696 : term608 = term603.
Proof. exact (MK_COMB (@lem6880695) (@lem6880690)). Qed.
Lemma lem6880698 (m : nat) (n : nat) : (term610 m n) = (term611 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6880699 : term603 = term612.
Proof. exact (@lem6880698 (NUMERAL 0) term92). Qed.
Lemma lem6880700 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880701 (h1 : term333 = (BIT1 0)) : (term92 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6880702 : (term333 = (BIT1 0)) = ((term92 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880701 h1) (fun h1 : (term92 = (NUMERAL 0)) = False => @lem6880700)). Qed.
Lemma lem6880703 : (term92 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6880702) (@lem6880700)). Qed.
Lemma lem6880704 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6880705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6880706 : term613 = (and True).
Proof. exact (MK_COMB (@lem6880705) (@lem6880704)). Qed.
Lemma lem6880707 : term612 = (True /\ False).
Proof. exact (MK_COMB (@lem6880706) (@lem6880703)). Qed.
Lemma lem6880709 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6880710 : term612 = False.
Proof. exact (TRANS (@lem6880707) (@lem6880709)). Qed.
Lemma lem6880711 : term603 = False.
Proof. exact (TRANS (@lem6880699) (@lem6880710)). Qed.
Lemma lem6880712 : term608 = False.
Proof. exact (TRANS (@lem6880696) (@lem6880711)). Qed.
Lemma lem6880713 : term605 = False.
Proof. exact (TRANS (@lem6880680) (@lem6880712)). Qed.
Lemma lem6880714 : term603 = False.
Proof. exact (TRANS (@lem6880657) (@lem6880713)). Qed.
Lemma lem6880715 : term602 = False.
Proof. exact (TRANS (@lem6880648) (@lem6880714)). Qed.
Lemma lem6880716 (_91911 : int) (_91912 : int) (h1 : term694 _91911 _91912) : False.
Proof. exact (EQ_MP (@lem6880715) (@lem6880645 _91911 _91912 h1)). Qed.
Lemma lem6880717 (_91911 : int) (_91912 : int) (h1 : term695 _91911 _91912) : term695 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6880718 (_91911 : int) (_91912 : int) (h1 : term695 _91911 _91912) : term527 _91911 _91912.
Proof. exact (proj2 (@lem6880717 _91911 _91912 h1)). Qed.
Lemma lem6880720 (_91911 : int) (_91912 : int) (h1 : term695 _91911 _91912) : term478 _91911 _91912.
Proof. exact (proj2 (@lem6880718 _91911 _91912 h1)). Qed.
Lemma lem6880721 (_91911 : int) (_91912 : int) (h1 : term695 _91911 _91912) : term299 _91912.
Proof. exact (proj1 (@lem6880718 _91911 _91912 h1)). Qed.
Lemma lem6880722 (_91911 : int) (_91912 : int) (h1 : term695 _91911 _91912) : term426 _91911 _91912.
Proof. exact (proj2 (@lem6880720 _91911 _91912 h1)). Qed.
Lemma lem6880726 (_91911 : int) (_91912 : int) (h1 : term695 _91911 _91912) : term373 _91912.
Proof. exact (proj2 (@lem6880722 _91911 _91912 h1)). Qed.
Lemma lem6880729 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6880730 : term551 = term331.
Proof. exact (@lem6880729 term214 term224). Qed.
Lemma lem6880732 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6880733 : term224 = term304.
Proof. exact (@lem6880732 term92). Qed.
Lemma lem6880735 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6880736 : term214 = term276.
Proof. exact (@lem6880735 (NUMERAL 0)). Qed.
Lemma lem6880737 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6880738 : term552 = term553.
Proof. exact (MK_COMB (@lem6880737) (@lem6880736)). Qed.
Lemma lem6880739 : term331 = term554.
Proof. exact (MK_COMB (@lem6880738) (@lem6880733)). Qed.
Lemma lem6880740 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6880742 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880743 : term331 = term332.
Proof. exact (@lem6880742 (NUMERAL 0) term92). Qed.
Lemma lem6880744 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880745 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880746 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880745 h1) (fun h1 : term332 = True => @lem6880744)). Qed.
Lemma lem6880747 : term332 = True.
Proof. exact (EQ_MP (@lem6880746) (@lem6880744)). Qed.
Lemma lem6880748 : term331 = True.
Proof. exact (TRANS (@lem6880743) (@lem6880747)). Qed.
Lemma lem6880749 : True = term331.
Proof. exact (SYM (@lem6880748)). Qed.
Lemma lem6880750 : term331.
Proof. exact (EQ_MP (@lem6880749) (@lem0)). Qed.
Lemma lem6880751 : term556.
Proof. exact (@lem6880740 (@lem6880750)). Qed.
Lemma lem6880753 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880754 : term331 = term332.
Proof. exact (@lem6880753 (NUMERAL 0) term92). Qed.
Lemma lem6880755 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880756 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880757 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880756 h1) (fun h1 : term332 = True => @lem6880755)). Qed.
Lemma lem6880758 : term332 = True.
Proof. exact (EQ_MP (@lem6880757) (@lem6880755)). Qed.
Lemma lem6880759 : term331 = True.
Proof. exact (TRANS (@lem6880754) (@lem6880758)). Qed.
Lemma lem6880760 : True = term331.
Proof. exact (SYM (@lem6880759)). Qed.
Lemma lem6880761 : term331.
Proof. exact (EQ_MP (@lem6880760) (@lem0)). Qed.
Lemma lem6880762 : term554 = term557.
Proof. exact (@lem6880751 (@lem6880761)). Qed.
Lemma lem6880764 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6880765 : term288 = term289.
Proof. exact (@lem6880764 term92 term92). Qed.
Lemma lem6880766 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880767 : term291 = term92.
Proof. exact (EQ_MP (@lem6880766) (@lem940073)). Qed.
Lemma lem6880768 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880769 : term289 = term224.
Proof. exact (MK_COMB (@lem6880768) (@lem6880767)). Qed.
Lemma lem6880770 : term288 = term224.
Proof. exact (TRANS (@lem6880765) (@lem6880769)). Qed.
Lemma lem6880772 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6880773 : term343 = term214.
Proof. exact (@lem6880772 term92). Qed.
Lemma lem6880774 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6880775 : term558 = term552.
Proof. exact (MK_COMB (@lem6880774) (@lem6880773)). Qed.
Lemma lem6880776 : term557 = term331.
Proof. exact (MK_COMB (@lem6880775) (@lem6880770)). Qed.
Lemma lem6880778 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880779 : term331 = term332.
Proof. exact (@lem6880778 (NUMERAL 0) term92). Qed.
Lemma lem6880780 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880781 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880782 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880781 h1) (fun h1 : term332 = True => @lem6880780)). Qed.
Lemma lem6880783 : term332 = True.
Proof. exact (EQ_MP (@lem6880782) (@lem6880780)). Qed.
Lemma lem6880784 : term331 = True.
Proof. exact (TRANS (@lem6880779) (@lem6880783)). Qed.
Lemma lem6880785 : term557 = True.
Proof. exact (TRANS (@lem6880776) (@lem6880784)). Qed.
Lemma lem6880786 : term554 = True.
Proof. exact (TRANS (@lem6880762) (@lem6880785)). Qed.
Lemma lem6880787 : term331 = True.
Proof. exact (TRANS (@lem6880739) (@lem6880786)). Qed.
Lemma lem6880788 : term551 = True.
Proof. exact (TRANS (@lem6880730) (@lem6880787)). Qed.
Lemma lem6880789 : True = term551.
Proof. exact (SYM (@lem6880788)). Qed.
Lemma lem6880790 : term551.
Proof. exact (EQ_MP (@lem6880789) (@lem0)). Qed.
Lemma lem6880791 (_91911 : int) (_91912 : int) (h1 : term695 _91911 _91912) : term657 _91912.
Proof. exact (conj (@lem6880790) (@lem6880721 _91911 _91912 h1)). Qed.
Lemma lem6880793 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6880794 (_91912 : int) : term658 _91912.
Proof. exact (@lem6880793 term224 (real_of_int _91912)). Qed.
Lemma lem6880795 (_91911 : int) (_91912 : int) (h1 : term695 _91911 _91912) : term659 _91912.
Proof. exact (@lem6880794 _91912 (@lem6880791 _91911 _91912 h1)). Qed.
Lemma lem6880796 (_91912 : int) : (term622 _91912) = (real_of_int _91912).
Proof. exact (@lem1982733 (real_of_int _91912)). Qed.
Lemma lem6880797 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6880798 (_91912 : int) : (term660 _91912) = (term298 _91912).
Proof. exact (MK_COMB (@lem6880797) (@lem6880796 _91912)). Qed.
Lemma lem6880799 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6880800 (_91912 : int) : (term659 _91912) = (term299 _91912).
Proof. exact (MK_COMB (@lem6880798 _91912) (@lem6880799)). Qed.
Lemma lem6880801 (_91911 : int) (_91912 : int) (h1 : term695 _91911 _91912) : term299 _91912.
Proof. exact (EQ_MP (@lem6880800 _91912) (@lem6880795 _91911 _91912 h1)). Qed.
Lemma lem6880803 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6880804 : term551 = term331.
Proof. exact (@lem6880803 term214 term224). Qed.
Lemma lem6880806 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6880807 : term224 = term304.
Proof. exact (@lem6880806 term92). Qed.
Lemma lem6880809 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6880810 : term214 = term276.
Proof. exact (@lem6880809 (NUMERAL 0)). Qed.
Lemma lem6880811 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6880812 : term552 = term553.
Proof. exact (MK_COMB (@lem6880811) (@lem6880810)). Qed.
Lemma lem6880813 : term331 = term554.
Proof. exact (MK_COMB (@lem6880812) (@lem6880807)). Qed.
Lemma lem6880814 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6880816 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880817 : term331 = term332.
Proof. exact (@lem6880816 (NUMERAL 0) term92). Qed.
Lemma lem6880818 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880819 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880820 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880819 h1) (fun h1 : term332 = True => @lem6880818)). Qed.
Lemma lem6880821 : term332 = True.
Proof. exact (EQ_MP (@lem6880820) (@lem6880818)). Qed.
Lemma lem6880822 : term331 = True.
Proof. exact (TRANS (@lem6880817) (@lem6880821)). Qed.
Lemma lem6880823 : True = term331.
Proof. exact (SYM (@lem6880822)). Qed.
Lemma lem6880824 : term331.
Proof. exact (EQ_MP (@lem6880823) (@lem0)). Qed.
Lemma lem6880825 : term556.
Proof. exact (@lem6880814 (@lem6880824)). Qed.
Lemma lem6880827 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880828 : term331 = term332.
Proof. exact (@lem6880827 (NUMERAL 0) term92). Qed.
Lemma lem6880829 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880830 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880831 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880830 h1) (fun h1 : term332 = True => @lem6880829)). Qed.
Lemma lem6880832 : term332 = True.
Proof. exact (EQ_MP (@lem6880831) (@lem6880829)). Qed.
Lemma lem6880833 : term331 = True.
Proof. exact (TRANS (@lem6880828) (@lem6880832)). Qed.
Lemma lem6880834 : True = term331.
Proof. exact (SYM (@lem6880833)). Qed.
Lemma lem6880835 : term331.
Proof. exact (EQ_MP (@lem6880834) (@lem0)). Qed.
Lemma lem6880836 : term554 = term557.
Proof. exact (@lem6880825 (@lem6880835)). Qed.
Lemma lem6880838 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6880839 : term288 = term289.
Proof. exact (@lem6880838 term92 term92). Qed.
Lemma lem6880840 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880841 : term291 = term92.
Proof. exact (EQ_MP (@lem6880840) (@lem940073)). Qed.
Lemma lem6880842 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880843 : term289 = term224.
Proof. exact (MK_COMB (@lem6880842) (@lem6880841)). Qed.
Lemma lem6880844 : term288 = term224.
Proof. exact (TRANS (@lem6880839) (@lem6880843)). Qed.
Lemma lem6880846 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6880847 : term343 = term214.
Proof. exact (@lem6880846 term92). Qed.
Lemma lem6880848 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6880849 : term558 = term552.
Proof. exact (MK_COMB (@lem6880848) (@lem6880847)). Qed.
Lemma lem6880850 : term557 = term331.
Proof. exact (MK_COMB (@lem6880849) (@lem6880844)). Qed.
Lemma lem6880852 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880853 : term331 = term332.
Proof. exact (@lem6880852 (NUMERAL 0) term92). Qed.
Lemma lem6880854 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880855 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880856 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880855 h1) (fun h1 : term332 = True => @lem6880854)). Qed.
Lemma lem6880857 : term332 = True.
Proof. exact (EQ_MP (@lem6880856) (@lem6880854)). Qed.
Lemma lem6880858 : term331 = True.
Proof. exact (TRANS (@lem6880853) (@lem6880857)). Qed.
Lemma lem6880859 : term557 = True.
Proof. exact (TRANS (@lem6880850) (@lem6880858)). Qed.
Lemma lem6880860 : term554 = True.
Proof. exact (TRANS (@lem6880836) (@lem6880859)). Qed.
Lemma lem6880861 : term331 = True.
Proof. exact (TRANS (@lem6880813) (@lem6880860)). Qed.
Lemma lem6880862 : term551 = True.
Proof. exact (TRANS (@lem6880804) (@lem6880861)). Qed.
Lemma lem6880863 : True = term551.
Proof. exact (SYM (@lem6880862)). Qed.
Lemma lem6880864 : term551.
Proof. exact (EQ_MP (@lem6880863) (@lem0)). Qed.
Lemma lem6880865 (_91911 : int) (_91912 : int) (h1 : term695 _91911 _91912) : term686 _91912.
Proof. exact (conj (@lem6880864) (@lem6880726 _91911 _91912 h1)). Qed.
Lemma lem6880867 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6880868 (_91912 : int) : term687 _91912.
Proof. exact (@lem6880867 term224 (term314 _91912)). Qed.
Lemma lem6880869 (_91911 : int) (_91912 : int) (h1 : term695 _91911 _91912) : term688 _91912.
Proof. exact (@lem6880868 _91912 (@lem6880865 _91911 _91912 h1)). Qed.
Lemma lem6880870 (_91912 : int) : (term674 _91912) = (term314 _91912).
Proof. exact (@lem1982733 (term314 _91912)). Qed.
Lemma lem6880871 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6880872 (_91912 : int) : (term689 _91912) = (term372 _91912).
Proof. exact (MK_COMB (@lem6880871) (@lem6880870 _91912)). Qed.
Lemma lem6880873 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6880874 (_91912 : int) : (term688 _91912) = (term373 _91912).
Proof. exact (MK_COMB (@lem6880872 _91912) (@lem6880873)). Qed.
Lemma lem6880875 (_91911 : int) (_91912 : int) (h1 : term695 _91911 _91912) : term373 _91912.
Proof. exact (EQ_MP (@lem6880874 _91912) (@lem6880869 _91911 _91912 h1)). Qed.
Lemma lem6880876 (_91911 : int) (_91912 : int) (h1 : term695 _91911 _91912) : term696 _91912.
Proof. exact (conj (@lem6880875 _91911 _91912 h1) (@lem6880801 _91911 _91912 h1)). Qed.
Lemma lem6880878 (x : real) (y : real) : term650 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6880879 (_91912 : int) : term697 _91912.
Proof. exact (@lem6880878 (term314 _91912) (real_of_int _91912)). Qed.
Lemma lem6880880 (_91911 : int) (_91912 : int) (h1 : term695 _91911 _91912) : term678 _91912.
Proof. exact (@lem6880879 _91912 (@lem6880876 _91911 _91912 h1)). Qed.
Lemma lem6880881 (_91912 : int) : (term679 _91912) = (term654 _91912).
Proof. exact (@lem1982759 (term317 _91912) (real_of_int _91912) term279). Qed.
Lemma lem6880882 (_91912 : int) : (term577 _91912) = (term578 _91912).
Proof. exact (@lem1982713 term279 (real_of_int _91912)). Qed.
Lemma lem6880884 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6880885 : term224 = term304.
Proof. exact (@lem6880884 term92). Qed.
Lemma lem6880887 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6880888 : term279 = term280.
Proof. exact (@lem6880887 term92). Qed.
Lemma lem6880889 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6880890 : term579 = term580.
Proof. exact (MK_COMB (@lem6880889) (@lem6880888)). Qed.
Lemma lem6880891 : term581 = term582.
Proof. exact (MK_COMB (@lem6880890) (@lem6880885)). Qed.
Lemma lem6880892 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6880894 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880895 : term331 = term332.
Proof. exact (@lem6880894 (NUMERAL 0) term92). Qed.
Lemma lem6880896 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880897 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880898 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880897 h1) (fun h1 : term332 = True => @lem6880896)). Qed.
Lemma lem6880899 : term332 = True.
Proof. exact (EQ_MP (@lem6880898) (@lem6880896)). Qed.
Lemma lem6880900 : term331 = True.
Proof. exact (TRANS (@lem6880895) (@lem6880899)). Qed.
Lemma lem6880901 : True = term331.
Proof. exact (SYM (@lem6880900)). Qed.
Lemma lem6880902 : term331.
Proof. exact (EQ_MP (@lem6880901) (@lem0)). Qed.
Lemma lem6880903 : term584.
Proof. exact (@lem6880892 (@lem6880902)). Qed.
Lemma lem6880905 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880906 : term331 = term332.
Proof. exact (@lem6880905 (NUMERAL 0) term92). Qed.
Lemma lem6880907 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880908 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880909 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880908 h1) (fun h1 : term332 = True => @lem6880907)). Qed.
Lemma lem6880910 : term332 = True.
Proof. exact (EQ_MP (@lem6880909) (@lem6880907)). Qed.
Lemma lem6880911 : term331 = True.
Proof. exact (TRANS (@lem6880906) (@lem6880910)). Qed.
Lemma lem6880912 : True = term331.
Proof. exact (SYM (@lem6880911)). Qed.
Lemma lem6880913 : term331.
Proof. exact (EQ_MP (@lem6880912) (@lem0)). Qed.
Lemma lem6880914 : term585.
Proof. exact (@lem6880903 (@lem6880913)). Qed.
Lemma lem6880916 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6880917 : term331 = term332.
Proof. exact (@lem6880916 (NUMERAL 0) term92). Qed.
Lemma lem6880918 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6880919 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6880920 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6880919 h1) (fun h1 : term332 = True => @lem6880918)). Qed.
Lemma lem6880921 : term332 = True.
Proof. exact (EQ_MP (@lem6880920) (@lem6880918)). Qed.
Lemma lem6880922 : term331 = True.
Proof. exact (TRANS (@lem6880917) (@lem6880921)). Qed.
Lemma lem6880923 : True = term331.
Proof. exact (SYM (@lem6880922)). Qed.
Lemma lem6880924 : term331.
Proof. exact (EQ_MP (@lem6880923) (@lem0)). Qed.
Lemma lem6880925 : term586.
Proof. exact (@lem6880914 (@lem6880924)). Qed.
Lemma lem6880927 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6880928 : term288 = term289.
Proof. exact (@lem6880927 term92 term92). Qed.
Lemma lem6880929 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880930 : term291 = term92.
Proof. exact (EQ_MP (@lem6880929) (@lem940073)). Qed.
Lemma lem6880931 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880932 : term289 = term224.
Proof. exact (MK_COMB (@lem6880931) (@lem6880930)). Qed.
Lemma lem6880933 : term288 = term224.
Proof. exact (TRANS (@lem6880928) (@lem6880932)). Qed.
Lemma lem6880935 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6880936 : term305 = term310.
Proof. exact (@lem6880935 term92 term92). Qed.
Lemma lem6880937 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880938 : term291 = term92.
Proof. exact (EQ_MP (@lem6880937) (@lem940073)). Qed.
Lemma lem6880939 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880940 : term289 = term224.
Proof. exact (MK_COMB (@lem6880939) (@lem6880938)). Qed.
Lemma lem6880941 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6880942 : term310 = term279.
Proof. exact (MK_COMB (@lem6880941) (@lem6880940)). Qed.
Lemma lem6880943 : term305 = term279.
Proof. exact (TRANS (@lem6880936) (@lem6880942)). Qed.
Lemma lem6880944 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6880945 : term587 = term579.
Proof. exact (MK_COMB (@lem6880944) (@lem6880943)). Qed.
Lemma lem6880946 : term588 = term581.
Proof. exact (MK_COMB (@lem6880945) (@lem6880933)). Qed.
Lemma lem6880948 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6880949 : term581 = term214.
Proof. exact (@lem6880948 term92). Qed.
Lemma lem6880950 : term588 = term214.
Proof. exact (TRANS (@lem6880946) (@lem6880949)). Qed.
Lemma lem6880951 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6880952 : term590 = term341.
Proof. exact (MK_COMB (@lem6880951) (@lem6880950)). Qed.
Lemma lem6880953 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6880954 : term591 = term343.
Proof. exact (MK_COMB (@lem6880952) (@lem6880953)). Qed.
Lemma lem6880956 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6880957 : term343 = term214.
Proof. exact (@lem6880956 term92). Qed.
Lemma lem6880958 : term591 = term214.
Proof. exact (TRANS (@lem6880954) (@lem6880957)). Qed.
Lemma lem6880960 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6880961 : term288 = term289.
Proof. exact (@lem6880960 term92 term92). Qed.
Lemma lem6880962 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6880963 : term291 = term92.
Proof. exact (EQ_MP (@lem6880962) (@lem940073)). Qed.
Lemma lem6880964 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6880965 : term289 = term224.
Proof. exact (MK_COMB (@lem6880964) (@lem6880963)). Qed.
Lemma lem6880966 : term288 = term224.
Proof. exact (TRANS (@lem6880961) (@lem6880965)). Qed.
Lemma lem6880967 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6880968 : term345 = term343.
Proof. exact (MK_COMB (@lem6880967) (@lem6880966)). Qed.
Lemma lem6880970 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6880971 : term343 = term214.
Proof. exact (@lem6880970 term92). Qed.
Lemma lem6880972 : term345 = term214.
Proof. exact (TRANS (@lem6880968) (@lem6880971)). Qed.
Lemma lem6880973 : term214 = term345.
Proof. exact (SYM (@lem6880972)). Qed.
Lemma lem6880974 : term591 = term345.
Proof. exact (TRANS (@lem6880958) (@lem6880973)). Qed.
Lemma lem6880975 : term582 = term276.
Proof. exact (@lem6880925 (@lem6880974)). Qed.
Lemma lem6880976 : term581 = term276.
Proof. exact (TRANS (@lem6880891) (@lem6880975)). Qed.
Lemma lem6880978 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6880979 : term276 = term214.
Proof. exact (@lem6880978 term214). Qed.
Lemma lem6880980 : term581 = term214.
Proof. exact (TRANS (@lem6880976) (@lem6880979)). Qed.
Lemma lem6880981 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6880982 : term592 = term341.
Proof. exact (MK_COMB (@lem6880981) (@lem6880980)). Qed.
Lemma lem6880983 (_91912 : int) : (real_of_int _91912) = (real_of_int _91912).
Proof. exact (eq_refl (real_of_int _91912)). Qed.
Lemma lem6880984 (_91912 : int) : (term578 _91912) = (term593 _91912).
Proof. exact (MK_COMB (@lem6880982) (@lem6880983 _91912)). Qed.
Lemma lem6880985 (_91912 : int) : (term577 _91912) = (term593 _91912).
Proof. exact (TRANS (@lem6880882 _91912) (@lem6880984 _91912)). Qed.
Lemma lem6880986 (_91912 : int) : (term593 _91912) = term214.
Proof. exact (@lem1982719 (real_of_int _91912)). Qed.
Lemma lem6880987 (_91912 : int) : (term577 _91912) = term214.
Proof. exact (TRANS (@lem6880985 _91912) (@lem6880986 _91912)). Qed.
Lemma lem6880988 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6880989 (_91912 : int) : (term594 _91912) = term256.
Proof. exact (MK_COMB (@lem6880988) (@lem6880987 _91912)). Qed.
Lemma lem6880990 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem6880991 (_91912 : int) : (term654 _91912) = term599.
Proof. exact (MK_COMB (@lem6880989 _91912) (@lem6880990)). Qed.
Lemma lem6880992 (_91912 : int) : (term679 _91912) = term599.
Proof. exact (TRANS (@lem6880881 _91912) (@lem6880991 _91912)). Qed.
Lemma lem6880993 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6880994 (_91912 : int) : (term679 _91912) = term279.
Proof. exact (TRANS (@lem6880992 _91912) (@lem6880993)). Qed.
Lemma lem6880995 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6880996 (_91912 : int) : (term680 _91912) = term601.
Proof. exact (MK_COMB (@lem6880995) (@lem6880994 _91912)). Qed.
Lemma lem6880997 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6880998 (_91912 : int) : (term678 _91912) = term602.
Proof. exact (MK_COMB (@lem6880996 _91912) (@lem6880997)). Qed.
Lemma lem6880999 (_91911 : int) (_91912 : int) (h1 : term695 _91911 _91912) : term602.
Proof. exact (EQ_MP (@lem6880998 _91912) (@lem6880880 _91911 _91912 h1)). Qed.
Lemma lem6881001 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6881002 : term602 = term603.
Proof. exact (@lem6881001 term214 term279). Qed.
Lemma lem6881004 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6881005 : term279 = term280.
Proof. exact (@lem6881004 term92). Qed.
Lemma lem6881007 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6881008 : term214 = term276.
Proof. exact (@lem6881007 (NUMERAL 0)). Qed.
Lemma lem6881009 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6881010 : term216 = term604.
Proof. exact (MK_COMB (@lem6881009) (@lem6881008)). Qed.
Lemma lem6881011 : term603 = term605.
Proof. exact (MK_COMB (@lem6881010) (@lem6881005)). Qed.
Lemma lem6881012 : term606.
Proof. exact (@lem1980026 term214 term224 term279 term224). Qed.
Lemma lem6881014 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881015 : term331 = term332.
Proof. exact (@lem6881014 (NUMERAL 0) term92). Qed.
Lemma lem6881016 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881017 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881018 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881017 h1) (fun h1 : term332 = True => @lem6881016)). Qed.
Lemma lem6881019 : term332 = True.
Proof. exact (EQ_MP (@lem6881018) (@lem6881016)). Qed.
Lemma lem6881020 : term331 = True.
Proof. exact (TRANS (@lem6881015) (@lem6881019)). Qed.
Lemma lem6881021 : True = term331.
Proof. exact (SYM (@lem6881020)). Qed.
Lemma lem6881022 : term331.
Proof. exact (EQ_MP (@lem6881021) (@lem0)). Qed.
Lemma lem6881023 : term607.
Proof. exact (@lem6881012 (@lem6881022)). Qed.
Lemma lem6881025 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881026 : term331 = term332.
Proof. exact (@lem6881025 (NUMERAL 0) term92). Qed.
Lemma lem6881027 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881028 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881029 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881028 h1) (fun h1 : term332 = True => @lem6881027)). Qed.
Lemma lem6881030 : term332 = True.
Proof. exact (EQ_MP (@lem6881029) (@lem6881027)). Qed.
Lemma lem6881031 : term331 = True.
Proof. exact (TRANS (@lem6881026) (@lem6881030)). Qed.
Lemma lem6881032 : True = term331.
Proof. exact (SYM (@lem6881031)). Qed.
Lemma lem6881033 : term331.
Proof. exact (EQ_MP (@lem6881032) (@lem0)). Qed.
Lemma lem6881034 : term605 = term608.
Proof. exact (@lem6881023 (@lem6881033)). Qed.
Lemma lem6881036 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6881037 : term305 = term310.
Proof. exact (@lem6881036 term92 term92). Qed.
Lemma lem6881038 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881039 : term291 = term92.
Proof. exact (EQ_MP (@lem6881038) (@lem940073)). Qed.
Lemma lem6881040 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881041 : term289 = term224.
Proof. exact (MK_COMB (@lem6881040) (@lem6881039)). Qed.
Lemma lem6881042 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6881043 : term310 = term279.
Proof. exact (MK_COMB (@lem6881042) (@lem6881041)). Qed.
Lemma lem6881044 : term305 = term279.
Proof. exact (TRANS (@lem6881037) (@lem6881043)). Qed.
Lemma lem6881046 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6881047 : term343 = term214.
Proof. exact (@lem6881046 term92). Qed.
Lemma lem6881048 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6881049 : term609 = term216.
Proof. exact (MK_COMB (@lem6881048) (@lem6881047)). Qed.
Lemma lem6881050 : term608 = term603.
Proof. exact (MK_COMB (@lem6881049) (@lem6881044)). Qed.
Lemma lem6881052 (m : nat) (n : nat) : (term610 m n) = (term611 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6881053 : term603 = term612.
Proof. exact (@lem6881052 (NUMERAL 0) term92). Qed.
Lemma lem6881054 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881055 (h1 : term333 = (BIT1 0)) : (term92 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6881056 : (term333 = (BIT1 0)) = ((term92 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881055 h1) (fun h1 : (term92 = (NUMERAL 0)) = False => @lem6881054)). Qed.
Lemma lem6881057 : (term92 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6881056) (@lem6881054)). Qed.
Lemma lem6881058 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6881059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6881060 : term613 = (and True).
Proof. exact (MK_COMB (@lem6881059) (@lem6881058)). Qed.
Lemma lem6881061 : term612 = (True /\ False).
Proof. exact (MK_COMB (@lem6881060) (@lem6881057)). Qed.
Lemma lem6881063 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6881064 : term612 = False.
Proof. exact (TRANS (@lem6881061) (@lem6881063)). Qed.
Lemma lem6881065 : term603 = False.
Proof. exact (TRANS (@lem6881053) (@lem6881064)). Qed.
Lemma lem6881066 : term608 = False.
Proof. exact (TRANS (@lem6881050) (@lem6881065)). Qed.
Lemma lem6881067 : term605 = False.
Proof. exact (TRANS (@lem6881034) (@lem6881066)). Qed.
Lemma lem6881068 : term603 = False.
Proof. exact (TRANS (@lem6881011) (@lem6881067)). Qed.
Lemma lem6881069 : term602 = False.
Proof. exact (TRANS (@lem6881002) (@lem6881068)). Qed.
Lemma lem6881070 (_91911 : int) (_91912 : int) (h1 : term695 _91911 _91912) : False.
Proof. exact (EQ_MP (@lem6881069) (@lem6880999 _91911 _91912 h1)). Qed.
Lemma lem6881071 (_91911 : int) (_91912 : int) (h1 : term525 _91911 _91912) : False.
Proof. exact (or_elim (@lem6880312 _91911 _91912 h1) (fun h0 : term694 _91911 _91912 => @lem6880716 _91911 _91912 h0) (fun h0 : term695 _91911 _91912 => @lem6881070 _91911 _91912 h0)). Qed.
Lemma lem6881072 (_91911 : int) (_91912 : int) (h1 : term521 _91911 _91912) : term521 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6881073 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : term698 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6881074 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : term522 _91911 _91912.
Proof. exact (proj2 (@lem6881073 _91911 _91912 h1)). Qed.
Lemma lem6881076 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : term473 _91911 _91912.
Proof. exact (proj2 (@lem6881074 _91911 _91912 h1)). Qed.
Lemma lem6881078 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : term427 _91912.
Proof. exact (proj2 (@lem6881076 _91911 _91912 h1)). Qed.
Lemma lem6881080 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : term373 _91912.
Proof. exact (proj2 (@lem6881078 _91911 _91912 h1)). Qed.
Lemma lem6881081 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : (real_of_int _91912) = term214.
Proof. exact (proj1 (@lem6881078 _91911 _91912 h1)). Qed.
Lemma lem6881083 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6881084 : term551 = term331.
Proof. exact (@lem6881083 term214 term224). Qed.
Lemma lem6881086 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6881087 : term224 = term304.
Proof. exact (@lem6881086 term92). Qed.
Lemma lem6881089 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6881090 : term214 = term276.
Proof. exact (@lem6881089 (NUMERAL 0)). Qed.
Lemma lem6881091 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6881092 : term552 = term553.
Proof. exact (MK_COMB (@lem6881091) (@lem6881090)). Qed.
Lemma lem6881093 : term331 = term554.
Proof. exact (MK_COMB (@lem6881092) (@lem6881087)). Qed.
Lemma lem6881094 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6881096 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881097 : term331 = term332.
Proof. exact (@lem6881096 (NUMERAL 0) term92). Qed.
Lemma lem6881098 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881099 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881100 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881099 h1) (fun h1 : term332 = True => @lem6881098)). Qed.
Lemma lem6881101 : term332 = True.
Proof. exact (EQ_MP (@lem6881100) (@lem6881098)). Qed.
Lemma lem6881102 : term331 = True.
Proof. exact (TRANS (@lem6881097) (@lem6881101)). Qed.
Lemma lem6881103 : True = term331.
Proof. exact (SYM (@lem6881102)). Qed.
Lemma lem6881104 : term331.
Proof. exact (EQ_MP (@lem6881103) (@lem0)). Qed.
Lemma lem6881105 : term556.
Proof. exact (@lem6881094 (@lem6881104)). Qed.
Lemma lem6881107 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881108 : term331 = term332.
Proof. exact (@lem6881107 (NUMERAL 0) term92). Qed.
Lemma lem6881109 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881110 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881111 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881110 h1) (fun h1 : term332 = True => @lem6881109)). Qed.
Lemma lem6881112 : term332 = True.
Proof. exact (EQ_MP (@lem6881111) (@lem6881109)). Qed.
Lemma lem6881113 : term331 = True.
Proof. exact (TRANS (@lem6881108) (@lem6881112)). Qed.
Lemma lem6881114 : True = term331.
Proof. exact (SYM (@lem6881113)). Qed.
Lemma lem6881115 : term331.
Proof. exact (EQ_MP (@lem6881114) (@lem0)). Qed.
Lemma lem6881116 : term554 = term557.
Proof. exact (@lem6881105 (@lem6881115)). Qed.
Lemma lem6881118 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6881119 : term288 = term289.
Proof. exact (@lem6881118 term92 term92). Qed.
Lemma lem6881120 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881121 : term291 = term92.
Proof. exact (EQ_MP (@lem6881120) (@lem940073)). Qed.
Lemma lem6881122 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881123 : term289 = term224.
Proof. exact (MK_COMB (@lem6881122) (@lem6881121)). Qed.
Lemma lem6881124 : term288 = term224.
Proof. exact (TRANS (@lem6881119) (@lem6881123)). Qed.
Lemma lem6881126 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6881127 : term343 = term214.
Proof. exact (@lem6881126 term92). Qed.
Lemma lem6881128 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6881129 : term558 = term552.
Proof. exact (MK_COMB (@lem6881128) (@lem6881127)). Qed.
Lemma lem6881130 : term557 = term331.
Proof. exact (MK_COMB (@lem6881129) (@lem6881124)). Qed.
Lemma lem6881132 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881133 : term331 = term332.
Proof. exact (@lem6881132 (NUMERAL 0) term92). Qed.
Lemma lem6881134 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881135 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881136 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881135 h1) (fun h1 : term332 = True => @lem6881134)). Qed.
Lemma lem6881137 : term332 = True.
Proof. exact (EQ_MP (@lem6881136) (@lem6881134)). Qed.
Lemma lem6881138 : term331 = True.
Proof. exact (TRANS (@lem6881133) (@lem6881137)). Qed.
Lemma lem6881139 : term557 = True.
Proof. exact (TRANS (@lem6881130) (@lem6881138)). Qed.
Lemma lem6881140 : term554 = True.
Proof. exact (TRANS (@lem6881116) (@lem6881139)). Qed.
Lemma lem6881141 : term331 = True.
Proof. exact (TRANS (@lem6881093) (@lem6881140)). Qed.
Lemma lem6881142 : term551 = True.
Proof. exact (TRANS (@lem6881084) (@lem6881141)). Qed.
Lemma lem6881143 : True = term551.
Proof. exact (SYM (@lem6881142)). Qed.
Lemma lem6881144 : term551.
Proof. exact (EQ_MP (@lem6881143) (@lem0)). Qed.
Lemma lem6881145 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : term686 _91912.
Proof. exact (conj (@lem6881144) (@lem6881080 _91911 _91912 h1)). Qed.
Lemma lem6881147 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6881148 (_91912 : int) : term687 _91912.
Proof. exact (@lem6881147 term224 (term314 _91912)). Qed.
Lemma lem6881149 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : term688 _91912.
Proof. exact (@lem6881148 _91912 (@lem6881145 _91911 _91912 h1)). Qed.
Lemma lem6881150 (_91912 : int) : (term674 _91912) = (term314 _91912).
Proof. exact (@lem1982733 (term314 _91912)). Qed.
Lemma lem6881151 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6881152 (_91912 : int) : (term689 _91912) = (term372 _91912).
Proof. exact (MK_COMB (@lem6881151) (@lem6881150 _91912)). Qed.
Lemma lem6881153 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6881154 (_91912 : int) : (term688 _91912) = (term373 _91912).
Proof. exact (MK_COMB (@lem6881152 _91912) (@lem6881153)). Qed.
Lemma lem6881155 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : term373 _91912.
Proof. exact (EQ_MP (@lem6881154 _91912) (@lem6881149 _91911 _91912 h1)). Qed.
Lemma lem6881157 (y : real) : term565 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6881158 (_91912 : int) : term619 _91912.
Proof. exact (@lem6881157 (real_of_int _91912)). Qed.
Lemma lem6881159 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : term620 _91912.
Proof. exact (@lem6881158 _91912 (@lem6881081 _91911 _91912 h1)). Qed.
Lemma lem6881160 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : term621 _91912.
Proof. exact (@lem6881159 _91911 _91912 h1 term224). Qed.
Lemma lem6881161 (_91912 : int) : (term621 _91912) = ((term622 _91912) = term214).
Proof. exact (eq_refl (term621 _91912)). Qed.
Lemma lem6881162 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : (term622 _91912) = term214.
Proof. exact (EQ_MP (@lem6881161 _91912) (@lem6881160 _91911 _91912 h1)). Qed.
Lemma lem6881163 (_91912 : int) : (term622 _91912) = (real_of_int _91912).
Proof. exact (@lem1982733 (real_of_int _91912)). Qed.
Lemma lem6881164 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6881165 (_91912 : int) : (term623 _91912) = (term227 _91912).
Proof. exact (MK_COMB (@lem6881164) (@lem6881163 _91912)). Qed.
Lemma lem6881166 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6881167 (_91912 : int) : ((term622 _91912) = term214) = ((real_of_int _91912) = term214).
Proof. exact (MK_COMB (@lem6881165 _91912) (@lem6881166)). Qed.
Lemma lem6881168 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : (real_of_int _91912) = term214.
Proof. exact (EQ_MP (@lem6881167 _91912) (@lem6881162 _91911 _91912 h1)). Qed.
Lemma lem6881169 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : term427 _91912.
Proof. exact (conj (@lem6881168 _91911 _91912 h1) (@lem6881155 _91911 _91912 h1)). Qed.
Lemma lem6881171 (x : real) (y : real) : term572 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6881172 (_91912 : int) : term690 _91912.
Proof. exact (@lem6881171 (real_of_int _91912) (term314 _91912)). Qed.
Lemma lem6881173 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : term691 _91912.
Proof. exact (@lem6881172 _91912 (@lem6881169 _91911 _91912 h1)). Qed.
Lemma lem6881174 (_91912 : int) : (term692 _91912) = (term596 _91912).
Proof. exact (@lem1982763 (real_of_int _91912) (term317 _91912) term279). Qed.
Lemma lem6881175 (_91912 : int) : (term597 _91912) = (term578 _91912).
Proof. exact (@lem1982715 term279 (real_of_int _91912)). Qed.
Lemma lem6881177 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6881178 : term224 = term304.
Proof. exact (@lem6881177 term92). Qed.
Lemma lem6881180 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6881181 : term279 = term280.
Proof. exact (@lem6881180 term92). Qed.
Lemma lem6881182 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6881183 : term579 = term580.
Proof. exact (MK_COMB (@lem6881182) (@lem6881181)). Qed.
Lemma lem6881184 : term581 = term582.
Proof. exact (MK_COMB (@lem6881183) (@lem6881178)). Qed.
Lemma lem6881185 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6881187 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881188 : term331 = term332.
Proof. exact (@lem6881187 (NUMERAL 0) term92). Qed.
Lemma lem6881189 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881190 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881191 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881190 h1) (fun h1 : term332 = True => @lem6881189)). Qed.
Lemma lem6881192 : term332 = True.
Proof. exact (EQ_MP (@lem6881191) (@lem6881189)). Qed.
Lemma lem6881193 : term331 = True.
Proof. exact (TRANS (@lem6881188) (@lem6881192)). Qed.
Lemma lem6881194 : True = term331.
Proof. exact (SYM (@lem6881193)). Qed.
Lemma lem6881195 : term331.
Proof. exact (EQ_MP (@lem6881194) (@lem0)). Qed.
Lemma lem6881196 : term584.
Proof. exact (@lem6881185 (@lem6881195)). Qed.
Lemma lem6881198 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881199 : term331 = term332.
Proof. exact (@lem6881198 (NUMERAL 0) term92). Qed.
Lemma lem6881200 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881201 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881202 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881201 h1) (fun h1 : term332 = True => @lem6881200)). Qed.
Lemma lem6881203 : term332 = True.
Proof. exact (EQ_MP (@lem6881202) (@lem6881200)). Qed.
Lemma lem6881204 : term331 = True.
Proof. exact (TRANS (@lem6881199) (@lem6881203)). Qed.
Lemma lem6881205 : True = term331.
Proof. exact (SYM (@lem6881204)). Qed.
Lemma lem6881206 : term331.
Proof. exact (EQ_MP (@lem6881205) (@lem0)). Qed.
Lemma lem6881207 : term585.
Proof. exact (@lem6881196 (@lem6881206)). Qed.
Lemma lem6881209 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881210 : term331 = term332.
Proof. exact (@lem6881209 (NUMERAL 0) term92). Qed.
Lemma lem6881211 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881212 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881213 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881212 h1) (fun h1 : term332 = True => @lem6881211)). Qed.
Lemma lem6881214 : term332 = True.
Proof. exact (EQ_MP (@lem6881213) (@lem6881211)). Qed.
Lemma lem6881215 : term331 = True.
Proof. exact (TRANS (@lem6881210) (@lem6881214)). Qed.
Lemma lem6881216 : True = term331.
Proof. exact (SYM (@lem6881215)). Qed.
Lemma lem6881217 : term331.
Proof. exact (EQ_MP (@lem6881216) (@lem0)). Qed.
Lemma lem6881218 : term586.
Proof. exact (@lem6881207 (@lem6881217)). Qed.
Lemma lem6881220 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6881221 : term288 = term289.
Proof. exact (@lem6881220 term92 term92). Qed.
Lemma lem6881222 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881223 : term291 = term92.
Proof. exact (EQ_MP (@lem6881222) (@lem940073)). Qed.
Lemma lem6881224 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881225 : term289 = term224.
Proof. exact (MK_COMB (@lem6881224) (@lem6881223)). Qed.
Lemma lem6881226 : term288 = term224.
Proof. exact (TRANS (@lem6881221) (@lem6881225)). Qed.
Lemma lem6881228 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6881229 : term305 = term310.
Proof. exact (@lem6881228 term92 term92). Qed.
Lemma lem6881230 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881231 : term291 = term92.
Proof. exact (EQ_MP (@lem6881230) (@lem940073)). Qed.
Lemma lem6881232 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881233 : term289 = term224.
Proof. exact (MK_COMB (@lem6881232) (@lem6881231)). Qed.
Lemma lem6881234 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6881235 : term310 = term279.
Proof. exact (MK_COMB (@lem6881234) (@lem6881233)). Qed.
Lemma lem6881236 : term305 = term279.
Proof. exact (TRANS (@lem6881229) (@lem6881235)). Qed.
Lemma lem6881237 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6881238 : term587 = term579.
Proof. exact (MK_COMB (@lem6881237) (@lem6881236)). Qed.
Lemma lem6881239 : term588 = term581.
Proof. exact (MK_COMB (@lem6881238) (@lem6881226)). Qed.
Lemma lem6881241 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6881242 : term581 = term214.
Proof. exact (@lem6881241 term92). Qed.
Lemma lem6881243 : term588 = term214.
Proof. exact (TRANS (@lem6881239) (@lem6881242)). Qed.
Lemma lem6881244 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6881245 : term590 = term341.
Proof. exact (MK_COMB (@lem6881244) (@lem6881243)). Qed.
Lemma lem6881246 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6881247 : term591 = term343.
Proof. exact (MK_COMB (@lem6881245) (@lem6881246)). Qed.
Lemma lem6881249 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6881250 : term343 = term214.
Proof. exact (@lem6881249 term92). Qed.
Lemma lem6881251 : term591 = term214.
Proof. exact (TRANS (@lem6881247) (@lem6881250)). Qed.
Lemma lem6881253 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6881254 : term288 = term289.
Proof. exact (@lem6881253 term92 term92). Qed.
Lemma lem6881255 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881256 : term291 = term92.
Proof. exact (EQ_MP (@lem6881255) (@lem940073)). Qed.
Lemma lem6881257 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881258 : term289 = term224.
Proof. exact (MK_COMB (@lem6881257) (@lem6881256)). Qed.
Lemma lem6881259 : term288 = term224.
Proof. exact (TRANS (@lem6881254) (@lem6881258)). Qed.
Lemma lem6881260 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6881261 : term345 = term343.
Proof. exact (MK_COMB (@lem6881260) (@lem6881259)). Qed.
Lemma lem6881263 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6881264 : term343 = term214.
Proof. exact (@lem6881263 term92). Qed.
Lemma lem6881265 : term345 = term214.
Proof. exact (TRANS (@lem6881261) (@lem6881264)). Qed.
Lemma lem6881266 : term214 = term345.
Proof. exact (SYM (@lem6881265)). Qed.
Lemma lem6881267 : term591 = term345.
Proof. exact (TRANS (@lem6881251) (@lem6881266)). Qed.
Lemma lem6881268 : term582 = term276.
Proof. exact (@lem6881218 (@lem6881267)). Qed.
Lemma lem6881269 : term581 = term276.
Proof. exact (TRANS (@lem6881184) (@lem6881268)). Qed.
Lemma lem6881271 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6881272 : term276 = term214.
Proof. exact (@lem6881271 term214). Qed.
Lemma lem6881273 : term581 = term214.
Proof. exact (TRANS (@lem6881269) (@lem6881272)). Qed.
Lemma lem6881274 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6881275 : term592 = term341.
Proof. exact (MK_COMB (@lem6881274) (@lem6881273)). Qed.
Lemma lem6881276 (_91912 : int) : (real_of_int _91912) = (real_of_int _91912).
Proof. exact (eq_refl (real_of_int _91912)). Qed.
Lemma lem6881277 (_91912 : int) : (term578 _91912) = (term593 _91912).
Proof. exact (MK_COMB (@lem6881275) (@lem6881276 _91912)). Qed.
Lemma lem6881278 (_91912 : int) : (term597 _91912) = (term593 _91912).
Proof. exact (TRANS (@lem6881175 _91912) (@lem6881277 _91912)). Qed.
Lemma lem6881279 (_91912 : int) : (term593 _91912) = term214.
Proof. exact (@lem1982719 (real_of_int _91912)). Qed.
Lemma lem6881280 (_91912 : int) : (term597 _91912) = term214.
Proof. exact (TRANS (@lem6881278 _91912) (@lem6881279 _91912)). Qed.
Lemma lem6881281 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6881282 (_91912 : int) : (term598 _91912) = term256.
Proof. exact (MK_COMB (@lem6881281) (@lem6881280 _91912)). Qed.
Lemma lem6881283 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem6881284 (_91912 : int) : (term596 _91912) = term599.
Proof. exact (MK_COMB (@lem6881282 _91912) (@lem6881283)). Qed.
Lemma lem6881285 (_91912 : int) : (term692 _91912) = term599.
Proof. exact (TRANS (@lem6881174 _91912) (@lem6881284 _91912)). Qed.
Lemma lem6881286 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6881287 (_91912 : int) : (term692 _91912) = term279.
Proof. exact (TRANS (@lem6881285 _91912) (@lem6881286)). Qed.
Lemma lem6881288 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6881289 (_91912 : int) : (term693 _91912) = term601.
Proof. exact (MK_COMB (@lem6881288) (@lem6881287 _91912)). Qed.
Lemma lem6881290 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6881291 (_91912 : int) : (term691 _91912) = term602.
Proof. exact (MK_COMB (@lem6881289 _91912) (@lem6881290)). Qed.
Lemma lem6881292 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : term602.
Proof. exact (EQ_MP (@lem6881291 _91912) (@lem6881173 _91911 _91912 h1)). Qed.
Lemma lem6881294 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6881295 : term602 = term603.
Proof. exact (@lem6881294 term214 term279). Qed.
Lemma lem6881297 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6881298 : term279 = term280.
Proof. exact (@lem6881297 term92). Qed.
Lemma lem6881300 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6881301 : term214 = term276.
Proof. exact (@lem6881300 (NUMERAL 0)). Qed.
Lemma lem6881302 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6881303 : term216 = term604.
Proof. exact (MK_COMB (@lem6881302) (@lem6881301)). Qed.
Lemma lem6881304 : term603 = term605.
Proof. exact (MK_COMB (@lem6881303) (@lem6881298)). Qed.
Lemma lem6881305 : term606.
Proof. exact (@lem1980026 term214 term224 term279 term224). Qed.
Lemma lem6881307 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881308 : term331 = term332.
Proof. exact (@lem6881307 (NUMERAL 0) term92). Qed.
Lemma lem6881309 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881310 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881311 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881310 h1) (fun h1 : term332 = True => @lem6881309)). Qed.
Lemma lem6881312 : term332 = True.
Proof. exact (EQ_MP (@lem6881311) (@lem6881309)). Qed.
Lemma lem6881313 : term331 = True.
Proof. exact (TRANS (@lem6881308) (@lem6881312)). Qed.
Lemma lem6881314 : True = term331.
Proof. exact (SYM (@lem6881313)). Qed.
Lemma lem6881315 : term331.
Proof. exact (EQ_MP (@lem6881314) (@lem0)). Qed.
Lemma lem6881316 : term607.
Proof. exact (@lem6881305 (@lem6881315)). Qed.
Lemma lem6881318 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881319 : term331 = term332.
Proof. exact (@lem6881318 (NUMERAL 0) term92). Qed.
Lemma lem6881320 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881321 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881322 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881321 h1) (fun h1 : term332 = True => @lem6881320)). Qed.
Lemma lem6881323 : term332 = True.
Proof. exact (EQ_MP (@lem6881322) (@lem6881320)). Qed.
Lemma lem6881324 : term331 = True.
Proof. exact (TRANS (@lem6881319) (@lem6881323)). Qed.
Lemma lem6881325 : True = term331.
Proof. exact (SYM (@lem6881324)). Qed.
Lemma lem6881326 : term331.
Proof. exact (EQ_MP (@lem6881325) (@lem0)). Qed.
Lemma lem6881327 : term605 = term608.
Proof. exact (@lem6881316 (@lem6881326)). Qed.
Lemma lem6881329 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6881330 : term305 = term310.
Proof. exact (@lem6881329 term92 term92). Qed.
Lemma lem6881331 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881332 : term291 = term92.
Proof. exact (EQ_MP (@lem6881331) (@lem940073)). Qed.
Lemma lem6881333 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881334 : term289 = term224.
Proof. exact (MK_COMB (@lem6881333) (@lem6881332)). Qed.
Lemma lem6881335 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6881336 : term310 = term279.
Proof. exact (MK_COMB (@lem6881335) (@lem6881334)). Qed.
Lemma lem6881337 : term305 = term279.
Proof. exact (TRANS (@lem6881330) (@lem6881336)). Qed.
Lemma lem6881339 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6881340 : term343 = term214.
Proof. exact (@lem6881339 term92). Qed.
Lemma lem6881341 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6881342 : term609 = term216.
Proof. exact (MK_COMB (@lem6881341) (@lem6881340)). Qed.
Lemma lem6881343 : term608 = term603.
Proof. exact (MK_COMB (@lem6881342) (@lem6881337)). Qed.
Lemma lem6881345 (m : nat) (n : nat) : (term610 m n) = (term611 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6881346 : term603 = term612.
Proof. exact (@lem6881345 (NUMERAL 0) term92). Qed.
Lemma lem6881347 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881348 (h1 : term333 = (BIT1 0)) : (term92 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6881349 : (term333 = (BIT1 0)) = ((term92 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881348 h1) (fun h1 : (term92 = (NUMERAL 0)) = False => @lem6881347)). Qed.
Lemma lem6881350 : (term92 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6881349) (@lem6881347)). Qed.
Lemma lem6881351 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6881352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6881353 : term613 = (and True).
Proof. exact (MK_COMB (@lem6881352) (@lem6881351)). Qed.
Lemma lem6881354 : term612 = (True /\ False).
Proof. exact (MK_COMB (@lem6881353) (@lem6881350)). Qed.
Lemma lem6881356 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6881357 : term612 = False.
Proof. exact (TRANS (@lem6881354) (@lem6881356)). Qed.
Lemma lem6881358 : term603 = False.
Proof. exact (TRANS (@lem6881346) (@lem6881357)). Qed.
Lemma lem6881359 : term608 = False.
Proof. exact (TRANS (@lem6881343) (@lem6881358)). Qed.
Lemma lem6881360 : term605 = False.
Proof. exact (TRANS (@lem6881327) (@lem6881359)). Qed.
Lemma lem6881361 : term603 = False.
Proof. exact (TRANS (@lem6881304) (@lem6881360)). Qed.
Lemma lem6881362 : term602 = False.
Proof. exact (TRANS (@lem6881295) (@lem6881361)). Qed.
Lemma lem6881363 (_91911 : int) (_91912 : int) (h1 : term698 _91911 _91912) : False.
Proof. exact (EQ_MP (@lem6881362) (@lem6881292 _91911 _91912 h1)). Qed.
Lemma lem6881364 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : term699 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6881365 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : term523 _91911 _91912.
Proof. exact (proj2 (@lem6881364 _91911 _91912 h1)). Qed.
Lemma lem6881367 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : term474 _91911 _91912.
Proof. exact (proj2 (@lem6881365 _91911 _91912 h1)). Qed.
Lemma lem6881369 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : term427 _91912.
Proof. exact (proj2 (@lem6881367 _91911 _91912 h1)). Qed.
Lemma lem6881373 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : term373 _91912.
Proof. exact (proj2 (@lem6881369 _91911 _91912 h1)). Qed.
Lemma lem6881374 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : (real_of_int _91912) = term214.
Proof. exact (proj1 (@lem6881369 _91911 _91912 h1)). Qed.
Lemma lem6881376 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6881377 : term551 = term331.
Proof. exact (@lem6881376 term214 term224). Qed.
Lemma lem6881379 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6881380 : term224 = term304.
Proof. exact (@lem6881379 term92). Qed.
Lemma lem6881382 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6881383 : term214 = term276.
Proof. exact (@lem6881382 (NUMERAL 0)). Qed.
Lemma lem6881384 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6881385 : term552 = term553.
Proof. exact (MK_COMB (@lem6881384) (@lem6881383)). Qed.
Lemma lem6881386 : term331 = term554.
Proof. exact (MK_COMB (@lem6881385) (@lem6881380)). Qed.
Lemma lem6881387 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6881389 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881390 : term331 = term332.
Proof. exact (@lem6881389 (NUMERAL 0) term92). Qed.
Lemma lem6881391 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881392 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881393 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881392 h1) (fun h1 : term332 = True => @lem6881391)). Qed.
Lemma lem6881394 : term332 = True.
Proof. exact (EQ_MP (@lem6881393) (@lem6881391)). Qed.
Lemma lem6881395 : term331 = True.
Proof. exact (TRANS (@lem6881390) (@lem6881394)). Qed.
Lemma lem6881396 : True = term331.
Proof. exact (SYM (@lem6881395)). Qed.
Lemma lem6881397 : term331.
Proof. exact (EQ_MP (@lem6881396) (@lem0)). Qed.
Lemma lem6881398 : term556.
Proof. exact (@lem6881387 (@lem6881397)). Qed.
Lemma lem6881400 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881401 : term331 = term332.
Proof. exact (@lem6881400 (NUMERAL 0) term92). Qed.
Lemma lem6881402 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881403 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881404 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881403 h1) (fun h1 : term332 = True => @lem6881402)). Qed.
Lemma lem6881405 : term332 = True.
Proof. exact (EQ_MP (@lem6881404) (@lem6881402)). Qed.
Lemma lem6881406 : term331 = True.
Proof. exact (TRANS (@lem6881401) (@lem6881405)). Qed.
Lemma lem6881407 : True = term331.
Proof. exact (SYM (@lem6881406)). Qed.
Lemma lem6881408 : term331.
Proof. exact (EQ_MP (@lem6881407) (@lem0)). Qed.
Lemma lem6881409 : term554 = term557.
Proof. exact (@lem6881398 (@lem6881408)). Qed.
Lemma lem6881411 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6881412 : term288 = term289.
Proof. exact (@lem6881411 term92 term92). Qed.
Lemma lem6881413 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881414 : term291 = term92.
Proof. exact (EQ_MP (@lem6881413) (@lem940073)). Qed.
Lemma lem6881415 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881416 : term289 = term224.
Proof. exact (MK_COMB (@lem6881415) (@lem6881414)). Qed.
Lemma lem6881417 : term288 = term224.
Proof. exact (TRANS (@lem6881412) (@lem6881416)). Qed.
Lemma lem6881419 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6881420 : term343 = term214.
Proof. exact (@lem6881419 term92). Qed.
Lemma lem6881421 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6881422 : term558 = term552.
Proof. exact (MK_COMB (@lem6881421) (@lem6881420)). Qed.
Lemma lem6881423 : term557 = term331.
Proof. exact (MK_COMB (@lem6881422) (@lem6881417)). Qed.
Lemma lem6881425 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881426 : term331 = term332.
Proof. exact (@lem6881425 (NUMERAL 0) term92). Qed.
Lemma lem6881427 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881428 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881429 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881428 h1) (fun h1 : term332 = True => @lem6881427)). Qed.
Lemma lem6881430 : term332 = True.
Proof. exact (EQ_MP (@lem6881429) (@lem6881427)). Qed.
Lemma lem6881431 : term331 = True.
Proof. exact (TRANS (@lem6881426) (@lem6881430)). Qed.
Lemma lem6881432 : term557 = True.
Proof. exact (TRANS (@lem6881423) (@lem6881431)). Qed.
Lemma lem6881433 : term554 = True.
Proof. exact (TRANS (@lem6881409) (@lem6881432)). Qed.
Lemma lem6881434 : term331 = True.
Proof. exact (TRANS (@lem6881386) (@lem6881433)). Qed.
Lemma lem6881435 : term551 = True.
Proof. exact (TRANS (@lem6881377) (@lem6881434)). Qed.
Lemma lem6881436 : True = term551.
Proof. exact (SYM (@lem6881435)). Qed.
Lemma lem6881437 : term551.
Proof. exact (EQ_MP (@lem6881436) (@lem0)). Qed.
Lemma lem6881438 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : term686 _91912.
Proof. exact (conj (@lem6881437) (@lem6881373 _91911 _91912 h1)). Qed.
Lemma lem6881440 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6881441 (_91912 : int) : term687 _91912.
Proof. exact (@lem6881440 term224 (term314 _91912)). Qed.
Lemma lem6881442 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : term688 _91912.
Proof. exact (@lem6881441 _91912 (@lem6881438 _91911 _91912 h1)). Qed.
Lemma lem6881443 (_91912 : int) : (term674 _91912) = (term314 _91912).
Proof. exact (@lem1982733 (term314 _91912)). Qed.
Lemma lem6881444 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6881445 (_91912 : int) : (term689 _91912) = (term372 _91912).
Proof. exact (MK_COMB (@lem6881444) (@lem6881443 _91912)). Qed.
Lemma lem6881446 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6881447 (_91912 : int) : (term688 _91912) = (term373 _91912).
Proof. exact (MK_COMB (@lem6881445 _91912) (@lem6881446)). Qed.
Lemma lem6881448 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : term373 _91912.
Proof. exact (EQ_MP (@lem6881447 _91912) (@lem6881442 _91911 _91912 h1)). Qed.
Lemma lem6881450 (y : real) : term565 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6881451 (_91912 : int) : term619 _91912.
Proof. exact (@lem6881450 (real_of_int _91912)). Qed.
Lemma lem6881452 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : term620 _91912.
Proof. exact (@lem6881451 _91912 (@lem6881374 _91911 _91912 h1)). Qed.
Lemma lem6881453 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : term621 _91912.
Proof. exact (@lem6881452 _91911 _91912 h1 term224). Qed.
Lemma lem6881454 (_91912 : int) : (term621 _91912) = ((term622 _91912) = term214).
Proof. exact (eq_refl (term621 _91912)). Qed.
Lemma lem6881455 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : (term622 _91912) = term214.
Proof. exact (EQ_MP (@lem6881454 _91912) (@lem6881453 _91911 _91912 h1)). Qed.
Lemma lem6881456 (_91912 : int) : (term622 _91912) = (real_of_int _91912).
Proof. exact (@lem1982733 (real_of_int _91912)). Qed.
Lemma lem6881457 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6881458 (_91912 : int) : (term623 _91912) = (term227 _91912).
Proof. exact (MK_COMB (@lem6881457) (@lem6881456 _91912)). Qed.
Lemma lem6881459 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6881460 (_91912 : int) : ((term622 _91912) = term214) = ((real_of_int _91912) = term214).
Proof. exact (MK_COMB (@lem6881458 _91912) (@lem6881459)). Qed.
Lemma lem6881461 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : (real_of_int _91912) = term214.
Proof. exact (EQ_MP (@lem6881460 _91912) (@lem6881455 _91911 _91912 h1)). Qed.
Lemma lem6881462 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : term427 _91912.
Proof. exact (conj (@lem6881461 _91911 _91912 h1) (@lem6881448 _91911 _91912 h1)). Qed.
Lemma lem6881464 (x : real) (y : real) : term572 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6881465 (_91912 : int) : term690 _91912.
Proof. exact (@lem6881464 (real_of_int _91912) (term314 _91912)). Qed.
Lemma lem6881466 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : term691 _91912.
Proof. exact (@lem6881465 _91912 (@lem6881462 _91911 _91912 h1)). Qed.
Lemma lem6881467 (_91912 : int) : (term692 _91912) = (term596 _91912).
Proof. exact (@lem1982763 (real_of_int _91912) (term317 _91912) term279). Qed.
Lemma lem6881468 (_91912 : int) : (term597 _91912) = (term578 _91912).
Proof. exact (@lem1982715 term279 (real_of_int _91912)). Qed.
Lemma lem6881470 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6881471 : term224 = term304.
Proof. exact (@lem6881470 term92). Qed.
Lemma lem6881473 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6881474 : term279 = term280.
Proof. exact (@lem6881473 term92). Qed.
Lemma lem6881475 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6881476 : term579 = term580.
Proof. exact (MK_COMB (@lem6881475) (@lem6881474)). Qed.
Lemma lem6881477 : term581 = term582.
Proof. exact (MK_COMB (@lem6881476) (@lem6881471)). Qed.
Lemma lem6881478 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6881480 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881481 : term331 = term332.
Proof. exact (@lem6881480 (NUMERAL 0) term92). Qed.
Lemma lem6881482 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881483 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881484 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881483 h1) (fun h1 : term332 = True => @lem6881482)). Qed.
Lemma lem6881485 : term332 = True.
Proof. exact (EQ_MP (@lem6881484) (@lem6881482)). Qed.
Lemma lem6881486 : term331 = True.
Proof. exact (TRANS (@lem6881481) (@lem6881485)). Qed.
Lemma lem6881487 : True = term331.
Proof. exact (SYM (@lem6881486)). Qed.
Lemma lem6881488 : term331.
Proof. exact (EQ_MP (@lem6881487) (@lem0)). Qed.
Lemma lem6881489 : term584.
Proof. exact (@lem6881478 (@lem6881488)). Qed.
Lemma lem6881491 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881492 : term331 = term332.
Proof. exact (@lem6881491 (NUMERAL 0) term92). Qed.
Lemma lem6881493 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881494 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881495 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881494 h1) (fun h1 : term332 = True => @lem6881493)). Qed.
Lemma lem6881496 : term332 = True.
Proof. exact (EQ_MP (@lem6881495) (@lem6881493)). Qed.
Lemma lem6881497 : term331 = True.
Proof. exact (TRANS (@lem6881492) (@lem6881496)). Qed.
Lemma lem6881498 : True = term331.
Proof. exact (SYM (@lem6881497)). Qed.
Lemma lem6881499 : term331.
Proof. exact (EQ_MP (@lem6881498) (@lem0)). Qed.
Lemma lem6881500 : term585.
Proof. exact (@lem6881489 (@lem6881499)). Qed.
Lemma lem6881502 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881503 : term331 = term332.
Proof. exact (@lem6881502 (NUMERAL 0) term92). Qed.
Lemma lem6881504 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881505 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881506 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881505 h1) (fun h1 : term332 = True => @lem6881504)). Qed.
Lemma lem6881507 : term332 = True.
Proof. exact (EQ_MP (@lem6881506) (@lem6881504)). Qed.
Lemma lem6881508 : term331 = True.
Proof. exact (TRANS (@lem6881503) (@lem6881507)). Qed.
Lemma lem6881509 : True = term331.
Proof. exact (SYM (@lem6881508)). Qed.
Lemma lem6881510 : term331.
Proof. exact (EQ_MP (@lem6881509) (@lem0)). Qed.
Lemma lem6881511 : term586.
Proof. exact (@lem6881500 (@lem6881510)). Qed.
Lemma lem6881513 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6881514 : term288 = term289.
Proof. exact (@lem6881513 term92 term92). Qed.
Lemma lem6881515 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881516 : term291 = term92.
Proof. exact (EQ_MP (@lem6881515) (@lem940073)). Qed.
Lemma lem6881517 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881518 : term289 = term224.
Proof. exact (MK_COMB (@lem6881517) (@lem6881516)). Qed.
Lemma lem6881519 : term288 = term224.
Proof. exact (TRANS (@lem6881514) (@lem6881518)). Qed.
Lemma lem6881521 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6881522 : term305 = term310.
Proof. exact (@lem6881521 term92 term92). Qed.
Lemma lem6881523 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881524 : term291 = term92.
Proof. exact (EQ_MP (@lem6881523) (@lem940073)). Qed.
Lemma lem6881525 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881526 : term289 = term224.
Proof. exact (MK_COMB (@lem6881525) (@lem6881524)). Qed.
Lemma lem6881527 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6881528 : term310 = term279.
Proof. exact (MK_COMB (@lem6881527) (@lem6881526)). Qed.
Lemma lem6881529 : term305 = term279.
Proof. exact (TRANS (@lem6881522) (@lem6881528)). Qed.
Lemma lem6881530 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6881531 : term587 = term579.
Proof. exact (MK_COMB (@lem6881530) (@lem6881529)). Qed.
Lemma lem6881532 : term588 = term581.
Proof. exact (MK_COMB (@lem6881531) (@lem6881519)). Qed.
Lemma lem6881534 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6881535 : term581 = term214.
Proof. exact (@lem6881534 term92). Qed.
Lemma lem6881536 : term588 = term214.
Proof. exact (TRANS (@lem6881532) (@lem6881535)). Qed.
Lemma lem6881537 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6881538 : term590 = term341.
Proof. exact (MK_COMB (@lem6881537) (@lem6881536)). Qed.
Lemma lem6881539 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6881540 : term591 = term343.
Proof. exact (MK_COMB (@lem6881538) (@lem6881539)). Qed.
Lemma lem6881542 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6881543 : term343 = term214.
Proof. exact (@lem6881542 term92). Qed.
Lemma lem6881544 : term591 = term214.
Proof. exact (TRANS (@lem6881540) (@lem6881543)). Qed.
Lemma lem6881546 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6881547 : term288 = term289.
Proof. exact (@lem6881546 term92 term92). Qed.
Lemma lem6881548 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881549 : term291 = term92.
Proof. exact (EQ_MP (@lem6881548) (@lem940073)). Qed.
Lemma lem6881550 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881551 : term289 = term224.
Proof. exact (MK_COMB (@lem6881550) (@lem6881549)). Qed.
Lemma lem6881552 : term288 = term224.
Proof. exact (TRANS (@lem6881547) (@lem6881551)). Qed.
Lemma lem6881553 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6881554 : term345 = term343.
Proof. exact (MK_COMB (@lem6881553) (@lem6881552)). Qed.
Lemma lem6881556 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6881557 : term343 = term214.
Proof. exact (@lem6881556 term92). Qed.
Lemma lem6881558 : term345 = term214.
Proof. exact (TRANS (@lem6881554) (@lem6881557)). Qed.
Lemma lem6881559 : term214 = term345.
Proof. exact (SYM (@lem6881558)). Qed.
Lemma lem6881560 : term591 = term345.
Proof. exact (TRANS (@lem6881544) (@lem6881559)). Qed.
Lemma lem6881561 : term582 = term276.
Proof. exact (@lem6881511 (@lem6881560)). Qed.
Lemma lem6881562 : term581 = term276.
Proof. exact (TRANS (@lem6881477) (@lem6881561)). Qed.
Lemma lem6881564 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6881565 : term276 = term214.
Proof. exact (@lem6881564 term214). Qed.
Lemma lem6881566 : term581 = term214.
Proof. exact (TRANS (@lem6881562) (@lem6881565)). Qed.
Lemma lem6881567 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6881568 : term592 = term341.
Proof. exact (MK_COMB (@lem6881567) (@lem6881566)). Qed.
Lemma lem6881569 (_91912 : int) : (real_of_int _91912) = (real_of_int _91912).
Proof. exact (eq_refl (real_of_int _91912)). Qed.
Lemma lem6881570 (_91912 : int) : (term578 _91912) = (term593 _91912).
Proof. exact (MK_COMB (@lem6881568) (@lem6881569 _91912)). Qed.
Lemma lem6881571 (_91912 : int) : (term597 _91912) = (term593 _91912).
Proof. exact (TRANS (@lem6881468 _91912) (@lem6881570 _91912)). Qed.
Lemma lem6881572 (_91912 : int) : (term593 _91912) = term214.
Proof. exact (@lem1982719 (real_of_int _91912)). Qed.
Lemma lem6881573 (_91912 : int) : (term597 _91912) = term214.
Proof. exact (TRANS (@lem6881571 _91912) (@lem6881572 _91912)). Qed.
Lemma lem6881574 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6881575 (_91912 : int) : (term598 _91912) = term256.
Proof. exact (MK_COMB (@lem6881574) (@lem6881573 _91912)). Qed.
Lemma lem6881576 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem6881577 (_91912 : int) : (term596 _91912) = term599.
Proof. exact (MK_COMB (@lem6881575 _91912) (@lem6881576)). Qed.
Lemma lem6881578 (_91912 : int) : (term692 _91912) = term599.
Proof. exact (TRANS (@lem6881467 _91912) (@lem6881577 _91912)). Qed.
Lemma lem6881579 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6881580 (_91912 : int) : (term692 _91912) = term279.
Proof. exact (TRANS (@lem6881578 _91912) (@lem6881579)). Qed.
Lemma lem6881581 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6881582 (_91912 : int) : (term693 _91912) = term601.
Proof. exact (MK_COMB (@lem6881581) (@lem6881580 _91912)). Qed.
Lemma lem6881583 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6881584 (_91912 : int) : (term691 _91912) = term602.
Proof. exact (MK_COMB (@lem6881582 _91912) (@lem6881583)). Qed.
Lemma lem6881585 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : term602.
Proof. exact (EQ_MP (@lem6881584 _91912) (@lem6881466 _91911 _91912 h1)). Qed.
Lemma lem6881587 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6881588 : term602 = term603.
Proof. exact (@lem6881587 term214 term279). Qed.
Lemma lem6881590 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6881591 : term279 = term280.
Proof. exact (@lem6881590 term92). Qed.
Lemma lem6881593 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6881594 : term214 = term276.
Proof. exact (@lem6881593 (NUMERAL 0)). Qed.
Lemma lem6881595 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6881596 : term216 = term604.
Proof. exact (MK_COMB (@lem6881595) (@lem6881594)). Qed.
Lemma lem6881597 : term603 = term605.
Proof. exact (MK_COMB (@lem6881596) (@lem6881591)). Qed.
Lemma lem6881598 : term606.
Proof. exact (@lem1980026 term214 term224 term279 term224). Qed.
Lemma lem6881600 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881601 : term331 = term332.
Proof. exact (@lem6881600 (NUMERAL 0) term92). Qed.
Lemma lem6881602 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881603 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881604 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881603 h1) (fun h1 : term332 = True => @lem6881602)). Qed.
Lemma lem6881605 : term332 = True.
Proof. exact (EQ_MP (@lem6881604) (@lem6881602)). Qed.
Lemma lem6881606 : term331 = True.
Proof. exact (TRANS (@lem6881601) (@lem6881605)). Qed.
Lemma lem6881607 : True = term331.
Proof. exact (SYM (@lem6881606)). Qed.
Lemma lem6881608 : term331.
Proof. exact (EQ_MP (@lem6881607) (@lem0)). Qed.
Lemma lem6881609 : term607.
Proof. exact (@lem6881598 (@lem6881608)). Qed.
Lemma lem6881611 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881612 : term331 = term332.
Proof. exact (@lem6881611 (NUMERAL 0) term92). Qed.
Lemma lem6881613 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881614 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881615 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881614 h1) (fun h1 : term332 = True => @lem6881613)). Qed.
Lemma lem6881616 : term332 = True.
Proof. exact (EQ_MP (@lem6881615) (@lem6881613)). Qed.
Lemma lem6881617 : term331 = True.
Proof. exact (TRANS (@lem6881612) (@lem6881616)). Qed.
Lemma lem6881618 : True = term331.
Proof. exact (SYM (@lem6881617)). Qed.
Lemma lem6881619 : term331.
Proof. exact (EQ_MP (@lem6881618) (@lem0)). Qed.
Lemma lem6881620 : term605 = term608.
Proof. exact (@lem6881609 (@lem6881619)). Qed.
Lemma lem6881622 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6881623 : term305 = term310.
Proof. exact (@lem6881622 term92 term92). Qed.
Lemma lem6881624 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881625 : term291 = term92.
Proof. exact (EQ_MP (@lem6881624) (@lem940073)). Qed.
Lemma lem6881626 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881627 : term289 = term224.
Proof. exact (MK_COMB (@lem6881626) (@lem6881625)). Qed.
Lemma lem6881628 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6881629 : term310 = term279.
Proof. exact (MK_COMB (@lem6881628) (@lem6881627)). Qed.
Lemma lem6881630 : term305 = term279.
Proof. exact (TRANS (@lem6881623) (@lem6881629)). Qed.
Lemma lem6881632 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6881633 : term343 = term214.
Proof. exact (@lem6881632 term92). Qed.
Lemma lem6881634 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6881635 : term609 = term216.
Proof. exact (MK_COMB (@lem6881634) (@lem6881633)). Qed.
Lemma lem6881636 : term608 = term603.
Proof. exact (MK_COMB (@lem6881635) (@lem6881630)). Qed.
Lemma lem6881638 (m : nat) (n : nat) : (term610 m n) = (term611 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6881639 : term603 = term612.
Proof. exact (@lem6881638 (NUMERAL 0) term92). Qed.
Lemma lem6881640 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881641 (h1 : term333 = (BIT1 0)) : (term92 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6881642 : (term333 = (BIT1 0)) = ((term92 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881641 h1) (fun h1 : (term92 = (NUMERAL 0)) = False => @lem6881640)). Qed.
Lemma lem6881643 : (term92 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6881642) (@lem6881640)). Qed.
Lemma lem6881644 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6881645 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6881646 : term613 = (and True).
Proof. exact (MK_COMB (@lem6881645) (@lem6881644)). Qed.
Lemma lem6881647 : term612 = (True /\ False).
Proof. exact (MK_COMB (@lem6881646) (@lem6881643)). Qed.
Lemma lem6881649 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6881650 : term612 = False.
Proof. exact (TRANS (@lem6881647) (@lem6881649)). Qed.
Lemma lem6881651 : term603 = False.
Proof. exact (TRANS (@lem6881639) (@lem6881650)). Qed.
Lemma lem6881652 : term608 = False.
Proof. exact (TRANS (@lem6881636) (@lem6881651)). Qed.
Lemma lem6881653 : term605 = False.
Proof. exact (TRANS (@lem6881620) (@lem6881652)). Qed.
Lemma lem6881654 : term603 = False.
Proof. exact (TRANS (@lem6881597) (@lem6881653)). Qed.
Lemma lem6881655 : term602 = False.
Proof. exact (TRANS (@lem6881588) (@lem6881654)). Qed.
Lemma lem6881656 (_91911 : int) (_91912 : int) (h1 : term699 _91911 _91912) : False.
Proof. exact (EQ_MP (@lem6881655) (@lem6881585 _91911 _91912 h1)). Qed.
Lemma lem6881657 (_91911 : int) (_91912 : int) (h1 : term521 _91911 _91912) : False.
Proof. exact (or_elim (@lem6881072 _91911 _91912 h1) (fun h0 : term698 _91911 _91912 => @lem6881363 _91911 _91912 h0) (fun h0 : term699 _91911 _91912 => @lem6881656 _91911 _91912 h0)). Qed.
Lemma lem6881658 (_91911 : int) (_91912 : int) (h1 : term530 _91911 _91912) : False.
Proof. exact (or_elim (@lem6880311 _91911 _91912 h1) (fun h0 : term525 _91911 _91912 => @lem6881071 _91911 _91912 h0) (fun h0 : term521 _91911 _91912 => @lem6881657 _91911 _91912 h0)). Qed.
Lemma lem6881659 (_91911 : int) (_91912 : int) (h1 : term517 _91911 _91912) : term517 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6881660 (_91911 : int) (_91912 : int) (h1 : term512 _91911 _91912) : term512 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6881661 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : term700 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6881662 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : term513 _91911 _91912.
Proof. exact (proj2 (@lem6881661 _91911 _91912 h1)). Qed.
Lemma lem6881664 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : term464 _91911 _91912.
Proof. exact (proj2 (@lem6881662 _91911 _91912 h1)). Qed.
Lemma lem6881666 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : term415 _91911 _91912.
Proof. exact (proj2 (@lem6881664 _91911 _91912 h1)). Qed.
Lemma lem6881667 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : (term316 _91911 _91912) = term214.
Proof. exact (proj1 (@lem6881664 _91911 _91912 h1)). Qed.
Lemma lem6881669 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : term360 _91911 _91912.
Proof. exact (proj1 (@lem6881666 _91911 _91912 h1)). Qed.
Lemma lem6881671 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6881672 : term551 = term331.
Proof. exact (@lem6881671 term214 term224). Qed.
Lemma lem6881674 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6881675 : term224 = term304.
Proof. exact (@lem6881674 term92). Qed.
Lemma lem6881677 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6881678 : term214 = term276.
Proof. exact (@lem6881677 (NUMERAL 0)). Qed.
Lemma lem6881679 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6881680 : term552 = term553.
Proof. exact (MK_COMB (@lem6881679) (@lem6881678)). Qed.
Lemma lem6881681 : term331 = term554.
Proof. exact (MK_COMB (@lem6881680) (@lem6881675)). Qed.
Lemma lem6881682 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6881684 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881685 : term331 = term332.
Proof. exact (@lem6881684 (NUMERAL 0) term92). Qed.
Lemma lem6881686 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881687 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881688 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881687 h1) (fun h1 : term332 = True => @lem6881686)). Qed.
Lemma lem6881689 : term332 = True.
Proof. exact (EQ_MP (@lem6881688) (@lem6881686)). Qed.
Lemma lem6881690 : term331 = True.
Proof. exact (TRANS (@lem6881685) (@lem6881689)). Qed.
Lemma lem6881691 : True = term331.
Proof. exact (SYM (@lem6881690)). Qed.
Lemma lem6881692 : term331.
Proof. exact (EQ_MP (@lem6881691) (@lem0)). Qed.
Lemma lem6881693 : term556.
Proof. exact (@lem6881682 (@lem6881692)). Qed.
Lemma lem6881695 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881696 : term331 = term332.
Proof. exact (@lem6881695 (NUMERAL 0) term92). Qed.
Lemma lem6881697 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881698 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881699 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881698 h1) (fun h1 : term332 = True => @lem6881697)). Qed.
Lemma lem6881700 : term332 = True.
Proof. exact (EQ_MP (@lem6881699) (@lem6881697)). Qed.
Lemma lem6881701 : term331 = True.
Proof. exact (TRANS (@lem6881696) (@lem6881700)). Qed.
Lemma lem6881702 : True = term331.
Proof. exact (SYM (@lem6881701)). Qed.
Lemma lem6881703 : term331.
Proof. exact (EQ_MP (@lem6881702) (@lem0)). Qed.
Lemma lem6881704 : term554 = term557.
Proof. exact (@lem6881693 (@lem6881703)). Qed.
Lemma lem6881706 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6881707 : term288 = term289.
Proof. exact (@lem6881706 term92 term92). Qed.
Lemma lem6881708 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881709 : term291 = term92.
Proof. exact (EQ_MP (@lem6881708) (@lem940073)). Qed.
Lemma lem6881710 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881711 : term289 = term224.
Proof. exact (MK_COMB (@lem6881710) (@lem6881709)). Qed.
Lemma lem6881712 : term288 = term224.
Proof. exact (TRANS (@lem6881707) (@lem6881711)). Qed.
Lemma lem6881714 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6881715 : term343 = term214.
Proof. exact (@lem6881714 term92). Qed.
Lemma lem6881716 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6881717 : term558 = term552.
Proof. exact (MK_COMB (@lem6881716) (@lem6881715)). Qed.
Lemma lem6881718 : term557 = term331.
Proof. exact (MK_COMB (@lem6881717) (@lem6881712)). Qed.
Lemma lem6881720 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881721 : term331 = term332.
Proof. exact (@lem6881720 (NUMERAL 0) term92). Qed.
Lemma lem6881722 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881723 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881724 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881723 h1) (fun h1 : term332 = True => @lem6881722)). Qed.
Lemma lem6881725 : term332 = True.
Proof. exact (EQ_MP (@lem6881724) (@lem6881722)). Qed.
Lemma lem6881726 : term331 = True.
Proof. exact (TRANS (@lem6881721) (@lem6881725)). Qed.
Lemma lem6881727 : term557 = True.
Proof. exact (TRANS (@lem6881718) (@lem6881726)). Qed.
Lemma lem6881728 : term554 = True.
Proof. exact (TRANS (@lem6881704) (@lem6881727)). Qed.
Lemma lem6881729 : term331 = True.
Proof. exact (TRANS (@lem6881681) (@lem6881728)). Qed.
Lemma lem6881730 : term551 = True.
Proof. exact (TRANS (@lem6881672) (@lem6881729)). Qed.
Lemma lem6881731 : True = term551.
Proof. exact (SYM (@lem6881730)). Qed.
Lemma lem6881732 : term551.
Proof. exact (EQ_MP (@lem6881731) (@lem0)). Qed.
Lemma lem6881733 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : term559 _91911 _91912.
Proof. exact (conj (@lem6881732) (@lem6881669 _91911 _91912 h1)). Qed.
Lemma lem6881735 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6881736 (_91911 : int) (_91912 : int) : term561 _91911 _91912.
Proof. exact (@lem6881735 term224 (term357 _91911 _91912)). Qed.
Lemma lem6881737 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : term562 _91911 _91912.
Proof. exact (@lem6881736 _91911 _91912 (@lem6881733 _91911 _91912 h1)). Qed.
Lemma lem6881738 (_91911 : int) (_91912 : int) : (term563 _91911 _91912) = (term357 _91911 _91912).
Proof. exact (@lem1982733 (term357 _91911 _91912)). Qed.
Lemma lem6881739 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6881740 (_91911 : int) (_91912 : int) : (term564 _91911 _91912) = (term359 _91911 _91912).
Proof. exact (MK_COMB (@lem6881739) (@lem6881738 _91911 _91912)). Qed.
Lemma lem6881741 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6881742 (_91911 : int) (_91912 : int) : (term562 _91911 _91912) = (term360 _91911 _91912).
Proof. exact (MK_COMB (@lem6881740 _91911 _91912) (@lem6881741)). Qed.
Lemma lem6881743 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : term360 _91911 _91912.
Proof. exact (EQ_MP (@lem6881742 _91911 _91912) (@lem6881737 _91911 _91912 h1)). Qed.
Lemma lem6881745 (y : real) : term565 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6881746 (_91911 : int) (_91912 : int) : term566 _91911 _91912.
Proof. exact (@lem6881745 (term316 _91911 _91912)). Qed.
Lemma lem6881747 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : term567 _91911 _91912.
Proof. exact (@lem6881746 _91911 _91912 (@lem6881667 _91911 _91912 h1)). Qed.
Lemma lem6881748 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : term568 _91911 _91912.
Proof. exact (@lem6881747 _91911 _91912 h1 term224). Qed.
Lemma lem6881749 (_91911 : int) (_91912 : int) : (term568 _91911 _91912) = ((term569 _91911 _91912) = term214).
Proof. exact (eq_refl (term568 _91911 _91912)). Qed.
Lemma lem6881750 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : (term569 _91911 _91912) = term214.
Proof. exact (EQ_MP (@lem6881749 _91911 _91912) (@lem6881748 _91911 _91912 h1)). Qed.
Lemma lem6881751 (_91911 : int) (_91912 : int) : (term569 _91911 _91912) = (term316 _91911 _91912).
Proof. exact (@lem1982733 (term316 _91911 _91912)). Qed.
Lemma lem6881752 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem6881753 (_91911 : int) (_91912 : int) : (term570 _91911 _91912) = (term319 _91911 _91912).
Proof. exact (MK_COMB (@lem6881752) (@lem6881751 _91911 _91912)). Qed.
Lemma lem6881754 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6881755 (_91911 : int) (_91912 : int) : ((term569 _91911 _91912) = term214) = ((term316 _91911 _91912) = term214).
Proof. exact (MK_COMB (@lem6881753 _91911 _91912) (@lem6881754)). Qed.
Lemma lem6881756 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : (term316 _91911 _91912) = term214.
Proof. exact (EQ_MP (@lem6881755 _91911 _91912) (@lem6881750 _91911 _91912 h1)). Qed.
Lemma lem6881757 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : term571 _91911 _91912.
Proof. exact (conj (@lem6881756 _91911 _91912 h1) (@lem6881743 _91911 _91912 h1)). Qed.
Lemma lem6881759 (x : real) (y : real) : term572 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6881760 (_91911 : int) (_91912 : int) : term573 _91911 _91912.
Proof. exact (@lem6881759 (term316 _91911 _91912) (term357 _91911 _91912)). Qed.
Lemma lem6881761 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : term574 _91911 _91912.
Proof. exact (@lem6881760 _91911 _91912 (@lem6881757 _91911 _91912 h1)). Qed.
Lemma lem6881762 (_91911 : int) (_91912 : int) : (term575 _91911 _91912) = (term576 _91911 _91912).
Proof. exact (@lem1982753 (term317 _91911) (real_of_int _91911) (term379 _91912) (term317 _91912)). Qed.
Lemma lem6881763 (_91911 : int) : (term577 _91911) = (term578 _91911).
Proof. exact (@lem1982713 term279 (real_of_int _91911)). Qed.
Lemma lem6881765 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6881766 : term224 = term304.
Proof. exact (@lem6881765 term92). Qed.
Lemma lem6881768 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6881769 : term279 = term280.
Proof. exact (@lem6881768 term92). Qed.
Lemma lem6881770 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6881771 : term579 = term580.
Proof. exact (MK_COMB (@lem6881770) (@lem6881769)). Qed.
Lemma lem6881772 : term581 = term582.
Proof. exact (MK_COMB (@lem6881771) (@lem6881766)). Qed.
Lemma lem6881773 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6881775 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881776 : term331 = term332.
Proof. exact (@lem6881775 (NUMERAL 0) term92). Qed.
Lemma lem6881777 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881778 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881779 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881778 h1) (fun h1 : term332 = True => @lem6881777)). Qed.
Lemma lem6881780 : term332 = True.
Proof. exact (EQ_MP (@lem6881779) (@lem6881777)). Qed.
Lemma lem6881781 : term331 = True.
Proof. exact (TRANS (@lem6881776) (@lem6881780)). Qed.
Lemma lem6881782 : True = term331.
Proof. exact (SYM (@lem6881781)). Qed.
Lemma lem6881783 : term331.
Proof. exact (EQ_MP (@lem6881782) (@lem0)). Qed.
Lemma lem6881784 : term584.
Proof. exact (@lem6881773 (@lem6881783)). Qed.
Lemma lem6881786 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881787 : term331 = term332.
Proof. exact (@lem6881786 (NUMERAL 0) term92). Qed.
Lemma lem6881788 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881789 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881790 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881789 h1) (fun h1 : term332 = True => @lem6881788)). Qed.
Lemma lem6881791 : term332 = True.
Proof. exact (EQ_MP (@lem6881790) (@lem6881788)). Qed.
Lemma lem6881792 : term331 = True.
Proof. exact (TRANS (@lem6881787) (@lem6881791)). Qed.
Lemma lem6881793 : True = term331.
Proof. exact (SYM (@lem6881792)). Qed.
Lemma lem6881794 : term331.
Proof. exact (EQ_MP (@lem6881793) (@lem0)). Qed.
Lemma lem6881795 : term585.
Proof. exact (@lem6881784 (@lem6881794)). Qed.
Lemma lem6881797 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881798 : term331 = term332.
Proof. exact (@lem6881797 (NUMERAL 0) term92). Qed.
Lemma lem6881799 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881800 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881801 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881800 h1) (fun h1 : term332 = True => @lem6881799)). Qed.
Lemma lem6881802 : term332 = True.
Proof. exact (EQ_MP (@lem6881801) (@lem6881799)). Qed.
Lemma lem6881803 : term331 = True.
Proof. exact (TRANS (@lem6881798) (@lem6881802)). Qed.
Lemma lem6881804 : True = term331.
Proof. exact (SYM (@lem6881803)). Qed.
Lemma lem6881805 : term331.
Proof. exact (EQ_MP (@lem6881804) (@lem0)). Qed.
Lemma lem6881806 : term586.
Proof. exact (@lem6881795 (@lem6881805)). Qed.
Lemma lem6881808 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6881809 : term288 = term289.
Proof. exact (@lem6881808 term92 term92). Qed.
Lemma lem6881810 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881811 : term291 = term92.
Proof. exact (EQ_MP (@lem6881810) (@lem940073)). Qed.
Lemma lem6881812 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881813 : term289 = term224.
Proof. exact (MK_COMB (@lem6881812) (@lem6881811)). Qed.
Lemma lem6881814 : term288 = term224.
Proof. exact (TRANS (@lem6881809) (@lem6881813)). Qed.
Lemma lem6881816 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6881817 : term305 = term310.
Proof. exact (@lem6881816 term92 term92). Qed.
Lemma lem6881818 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881819 : term291 = term92.
Proof. exact (EQ_MP (@lem6881818) (@lem940073)). Qed.
Lemma lem6881820 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881821 : term289 = term224.
Proof. exact (MK_COMB (@lem6881820) (@lem6881819)). Qed.
Lemma lem6881822 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6881823 : term310 = term279.
Proof. exact (MK_COMB (@lem6881822) (@lem6881821)). Qed.
Lemma lem6881824 : term305 = term279.
Proof. exact (TRANS (@lem6881817) (@lem6881823)). Qed.
Lemma lem6881825 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6881826 : term587 = term579.
Proof. exact (MK_COMB (@lem6881825) (@lem6881824)). Qed.
Lemma lem6881827 : term588 = term581.
Proof. exact (MK_COMB (@lem6881826) (@lem6881814)). Qed.
Lemma lem6881829 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6881830 : term581 = term214.
Proof. exact (@lem6881829 term92). Qed.
Lemma lem6881831 : term588 = term214.
Proof. exact (TRANS (@lem6881827) (@lem6881830)). Qed.
Lemma lem6881832 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6881833 : term590 = term341.
Proof. exact (MK_COMB (@lem6881832) (@lem6881831)). Qed.
Lemma lem6881834 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6881835 : term591 = term343.
Proof. exact (MK_COMB (@lem6881833) (@lem6881834)). Qed.
Lemma lem6881837 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6881838 : term343 = term214.
Proof. exact (@lem6881837 term92). Qed.
Lemma lem6881839 : term591 = term214.
Proof. exact (TRANS (@lem6881835) (@lem6881838)). Qed.
Lemma lem6881841 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6881842 : term288 = term289.
Proof. exact (@lem6881841 term92 term92). Qed.
Lemma lem6881843 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881844 : term291 = term92.
Proof. exact (EQ_MP (@lem6881843) (@lem940073)). Qed.
Lemma lem6881845 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881846 : term289 = term224.
Proof. exact (MK_COMB (@lem6881845) (@lem6881844)). Qed.
Lemma lem6881847 : term288 = term224.
Proof. exact (TRANS (@lem6881842) (@lem6881846)). Qed.
Lemma lem6881848 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6881849 : term345 = term343.
Proof. exact (MK_COMB (@lem6881848) (@lem6881847)). Qed.
Lemma lem6881851 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6881852 : term343 = term214.
Proof. exact (@lem6881851 term92). Qed.
Lemma lem6881853 : term345 = term214.
Proof. exact (TRANS (@lem6881849) (@lem6881852)). Qed.
Lemma lem6881854 : term214 = term345.
Proof. exact (SYM (@lem6881853)). Qed.
Lemma lem6881855 : term591 = term345.
Proof. exact (TRANS (@lem6881839) (@lem6881854)). Qed.
Lemma lem6881856 : term582 = term276.
Proof. exact (@lem6881806 (@lem6881855)). Qed.
Lemma lem6881857 : term581 = term276.
Proof. exact (TRANS (@lem6881772) (@lem6881856)). Qed.
Lemma lem6881859 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6881860 : term276 = term214.
Proof. exact (@lem6881859 term214). Qed.
Lemma lem6881861 : term581 = term214.
Proof. exact (TRANS (@lem6881857) (@lem6881860)). Qed.
Lemma lem6881862 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6881863 : term592 = term341.
Proof. exact (MK_COMB (@lem6881862) (@lem6881861)). Qed.
Lemma lem6881864 (_91911 : int) : (real_of_int _91911) = (real_of_int _91911).
Proof. exact (eq_refl (real_of_int _91911)). Qed.
Lemma lem6881865 (_91911 : int) : (term578 _91911) = (term593 _91911).
Proof. exact (MK_COMB (@lem6881863) (@lem6881864 _91911)). Qed.
Lemma lem6881866 (_91911 : int) : (term577 _91911) = (term593 _91911).
Proof. exact (TRANS (@lem6881763 _91911) (@lem6881865 _91911)). Qed.
Lemma lem6881867 (_91911 : int) : (term593 _91911) = term214.
Proof. exact (@lem1982719 (real_of_int _91911)). Qed.
Lemma lem6881868 (_91911 : int) : (term577 _91911) = term214.
Proof. exact (TRANS (@lem6881866 _91911) (@lem6881867 _91911)). Qed.
Lemma lem6881869 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6881870 (_91911 : int) : (term594 _91911) = term256.
Proof. exact (MK_COMB (@lem6881869) (@lem6881868 _91911)). Qed.
Lemma lem6881871 (_91912 : int) : (term595 _91912) = (term596 _91912).
Proof. exact (@lem1982759 (real_of_int _91912) (term317 _91912) term279). Qed.
Lemma lem6881872 (_91912 : int) : (term597 _91912) = (term578 _91912).
Proof. exact (@lem1982715 term279 (real_of_int _91912)). Qed.
Lemma lem6881874 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6881875 : term224 = term304.
Proof. exact (@lem6881874 term92). Qed.
Lemma lem6881877 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6881878 : term279 = term280.
Proof. exact (@lem6881877 term92). Qed.
Lemma lem6881879 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6881880 : term579 = term580.
Proof. exact (MK_COMB (@lem6881879) (@lem6881878)). Qed.
Lemma lem6881881 : term581 = term582.
Proof. exact (MK_COMB (@lem6881880) (@lem6881875)). Qed.
Lemma lem6881882 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6881884 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881885 : term331 = term332.
Proof. exact (@lem6881884 (NUMERAL 0) term92). Qed.
Lemma lem6881886 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881887 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881888 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881887 h1) (fun h1 : term332 = True => @lem6881886)). Qed.
Lemma lem6881889 : term332 = True.
Proof. exact (EQ_MP (@lem6881888) (@lem6881886)). Qed.
Lemma lem6881890 : term331 = True.
Proof. exact (TRANS (@lem6881885) (@lem6881889)). Qed.
Lemma lem6881891 : True = term331.
Proof. exact (SYM (@lem6881890)). Qed.
Lemma lem6881892 : term331.
Proof. exact (EQ_MP (@lem6881891) (@lem0)). Qed.
Lemma lem6881893 : term584.
Proof. exact (@lem6881882 (@lem6881892)). Qed.
Lemma lem6881895 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881896 : term331 = term332.
Proof. exact (@lem6881895 (NUMERAL 0) term92). Qed.
Lemma lem6881897 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881898 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881899 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881898 h1) (fun h1 : term332 = True => @lem6881897)). Qed.
Lemma lem6881900 : term332 = True.
Proof. exact (EQ_MP (@lem6881899) (@lem6881897)). Qed.
Lemma lem6881901 : term331 = True.
Proof. exact (TRANS (@lem6881896) (@lem6881900)). Qed.
Lemma lem6881902 : True = term331.
Proof. exact (SYM (@lem6881901)). Qed.
Lemma lem6881903 : term331.
Proof. exact (EQ_MP (@lem6881902) (@lem0)). Qed.
Lemma lem6881904 : term585.
Proof. exact (@lem6881893 (@lem6881903)). Qed.
Lemma lem6881906 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6881907 : term331 = term332.
Proof. exact (@lem6881906 (NUMERAL 0) term92). Qed.
Lemma lem6881908 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6881909 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6881910 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6881909 h1) (fun h1 : term332 = True => @lem6881908)). Qed.
Lemma lem6881911 : term332 = True.
Proof. exact (EQ_MP (@lem6881910) (@lem6881908)). Qed.
Lemma lem6881912 : term331 = True.
Proof. exact (TRANS (@lem6881907) (@lem6881911)). Qed.
Lemma lem6881913 : True = term331.
Proof. exact (SYM (@lem6881912)). Qed.
Lemma lem6881914 : term331.
Proof. exact (EQ_MP (@lem6881913) (@lem0)). Qed.
Lemma lem6881915 : term586.
Proof. exact (@lem6881904 (@lem6881914)). Qed.
Lemma lem6881917 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6881918 : term288 = term289.
Proof. exact (@lem6881917 term92 term92). Qed.
Lemma lem6881919 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881920 : term291 = term92.
Proof. exact (EQ_MP (@lem6881919) (@lem940073)). Qed.
Lemma lem6881921 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881922 : term289 = term224.
Proof. exact (MK_COMB (@lem6881921) (@lem6881920)). Qed.
Lemma lem6881923 : term288 = term224.
Proof. exact (TRANS (@lem6881918) (@lem6881922)). Qed.
Lemma lem6881925 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6881926 : term305 = term310.
Proof. exact (@lem6881925 term92 term92). Qed.
Lemma lem6881927 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881928 : term291 = term92.
Proof. exact (EQ_MP (@lem6881927) (@lem940073)). Qed.
Lemma lem6881929 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881930 : term289 = term224.
Proof. exact (MK_COMB (@lem6881929) (@lem6881928)). Qed.
Lemma lem6881931 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6881932 : term310 = term279.
Proof. exact (MK_COMB (@lem6881931) (@lem6881930)). Qed.
Lemma lem6881933 : term305 = term279.
Proof. exact (TRANS (@lem6881926) (@lem6881932)). Qed.
Lemma lem6881934 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6881935 : term587 = term579.
Proof. exact (MK_COMB (@lem6881934) (@lem6881933)). Qed.
Lemma lem6881936 : term588 = term581.
Proof. exact (MK_COMB (@lem6881935) (@lem6881923)). Qed.
Lemma lem6881938 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6881939 : term581 = term214.
Proof. exact (@lem6881938 term92). Qed.
Lemma lem6881940 : term588 = term214.
Proof. exact (TRANS (@lem6881936) (@lem6881939)). Qed.
Lemma lem6881941 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6881942 : term590 = term341.
Proof. exact (MK_COMB (@lem6881941) (@lem6881940)). Qed.
Lemma lem6881943 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6881944 : term591 = term343.
Proof. exact (MK_COMB (@lem6881942) (@lem6881943)). Qed.
Lemma lem6881946 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6881947 : term343 = term214.
Proof. exact (@lem6881946 term92). Qed.
Lemma lem6881948 : term591 = term214.
Proof. exact (TRANS (@lem6881944) (@lem6881947)). Qed.
Lemma lem6881950 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6881951 : term288 = term289.
Proof. exact (@lem6881950 term92 term92). Qed.
Lemma lem6881952 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6881953 : term291 = term92.
Proof. exact (EQ_MP (@lem6881952) (@lem940073)). Qed.
Lemma lem6881954 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6881955 : term289 = term224.
Proof. exact (MK_COMB (@lem6881954) (@lem6881953)). Qed.
Lemma lem6881956 : term288 = term224.
Proof. exact (TRANS (@lem6881951) (@lem6881955)). Qed.
Lemma lem6881957 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6881958 : term345 = term343.
Proof. exact (MK_COMB (@lem6881957) (@lem6881956)). Qed.
Lemma lem6881960 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6881961 : term343 = term214.
Proof. exact (@lem6881960 term92). Qed.
Lemma lem6881962 : term345 = term214.
Proof. exact (TRANS (@lem6881958) (@lem6881961)). Qed.
Lemma lem6881963 : term214 = term345.
Proof. exact (SYM (@lem6881962)). Qed.
Lemma lem6881964 : term591 = term345.
Proof. exact (TRANS (@lem6881948) (@lem6881963)). Qed.
Lemma lem6881965 : term582 = term276.
Proof. exact (@lem6881915 (@lem6881964)). Qed.
Lemma lem6881966 : term581 = term276.
Proof. exact (TRANS (@lem6881881) (@lem6881965)). Qed.
Lemma lem6881968 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6881969 : term276 = term214.
Proof. exact (@lem6881968 term214). Qed.
Lemma lem6881970 : term581 = term214.
Proof. exact (TRANS (@lem6881966) (@lem6881969)). Qed.
Lemma lem6881971 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6881972 : term592 = term341.
Proof. exact (MK_COMB (@lem6881971) (@lem6881970)). Qed.
Lemma lem6881973 (_91912 : int) : (real_of_int _91912) = (real_of_int _91912).
Proof. exact (eq_refl (real_of_int _91912)). Qed.
Lemma lem6881974 (_91912 : int) : (term578 _91912) = (term593 _91912).
Proof. exact (MK_COMB (@lem6881972) (@lem6881973 _91912)). Qed.
Lemma lem6881975 (_91912 : int) : (term597 _91912) = (term593 _91912).
Proof. exact (TRANS (@lem6881872 _91912) (@lem6881974 _91912)). Qed.
Lemma lem6881976 (_91912 : int) : (term593 _91912) = term214.
Proof. exact (@lem1982719 (real_of_int _91912)). Qed.
Lemma lem6881977 (_91912 : int) : (term597 _91912) = term214.
Proof. exact (TRANS (@lem6881975 _91912) (@lem6881976 _91912)). Qed.
Lemma lem6881978 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6881979 (_91912 : int) : (term598 _91912) = term256.
Proof. exact (MK_COMB (@lem6881978) (@lem6881977 _91912)). Qed.
Lemma lem6881980 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem6881981 (_91912 : int) : (term596 _91912) = term599.
Proof. exact (MK_COMB (@lem6881979 _91912) (@lem6881980)). Qed.
Lemma lem6881982 (_91912 : int) : (term595 _91912) = term599.
Proof. exact (TRANS (@lem6881871 _91912) (@lem6881981 _91912)). Qed.
Lemma lem6881983 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6881984 (_91912 : int) : (term595 _91912) = term279.
Proof. exact (TRANS (@lem6881982 _91912) (@lem6881983)). Qed.
Lemma lem6881985 (_91911 : int) (_91912 : int) : (term576 _91911 _91912) = term599.
Proof. exact (MK_COMB (@lem6881870 _91911) (@lem6881984 _91912)). Qed.
Lemma lem6881986 (_91911 : int) (_91912 : int) : (term575 _91911 _91912) = term599.
Proof. exact (TRANS (@lem6881762 _91911 _91912) (@lem6881985 _91911 _91912)). Qed.
Lemma lem6881987 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6881988 (_91911 : int) (_91912 : int) : (term575 _91911 _91912) = term279.
Proof. exact (TRANS (@lem6881986 _91911 _91912) (@lem6881987)). Qed.
Lemma lem6881989 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6881990 (_91911 : int) (_91912 : int) : (term600 _91911 _91912) = term601.
Proof. exact (MK_COMB (@lem6881989) (@lem6881988 _91911 _91912)). Qed.
Lemma lem6881991 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6881992 (_91911 : int) (_91912 : int) : (term574 _91911 _91912) = term602.
Proof. exact (MK_COMB (@lem6881990 _91911 _91912) (@lem6881991)). Qed.
Lemma lem6881993 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : term602.
Proof. exact (EQ_MP (@lem6881992 _91911 _91912) (@lem6881761 _91911 _91912 h1)). Qed.
Lemma lem6881995 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6881996 : term602 = term603.
Proof. exact (@lem6881995 term214 term279). Qed.
Lemma lem6881998 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6881999 : term279 = term280.
Proof. exact (@lem6881998 term92). Qed.
Lemma lem6882001 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6882002 : term214 = term276.
Proof. exact (@lem6882001 (NUMERAL 0)). Qed.
Lemma lem6882003 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6882004 : term216 = term604.
Proof. exact (MK_COMB (@lem6882003) (@lem6882002)). Qed.
Lemma lem6882005 : term603 = term605.
Proof. exact (MK_COMB (@lem6882004) (@lem6881999)). Qed.
Lemma lem6882006 : term606.
Proof. exact (@lem1980026 term214 term224 term279 term224). Qed.
Lemma lem6882008 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882009 : term331 = term332.
Proof. exact (@lem6882008 (NUMERAL 0) term92). Qed.
Lemma lem6882010 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882011 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882012 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882011 h1) (fun h1 : term332 = True => @lem6882010)). Qed.
Lemma lem6882013 : term332 = True.
Proof. exact (EQ_MP (@lem6882012) (@lem6882010)). Qed.
Lemma lem6882014 : term331 = True.
Proof. exact (TRANS (@lem6882009) (@lem6882013)). Qed.
Lemma lem6882015 : True = term331.
Proof. exact (SYM (@lem6882014)). Qed.
Lemma lem6882016 : term331.
Proof. exact (EQ_MP (@lem6882015) (@lem0)). Qed.
Lemma lem6882017 : term607.
Proof. exact (@lem6882006 (@lem6882016)). Qed.
Lemma lem6882019 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882020 : term331 = term332.
Proof. exact (@lem6882019 (NUMERAL 0) term92). Qed.
Lemma lem6882021 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882022 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882023 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882022 h1) (fun h1 : term332 = True => @lem6882021)). Qed.
Lemma lem6882024 : term332 = True.
Proof. exact (EQ_MP (@lem6882023) (@lem6882021)). Qed.
Lemma lem6882025 : term331 = True.
Proof. exact (TRANS (@lem6882020) (@lem6882024)). Qed.
Lemma lem6882026 : True = term331.
Proof. exact (SYM (@lem6882025)). Qed.
Lemma lem6882027 : term331.
Proof. exact (EQ_MP (@lem6882026) (@lem0)). Qed.
Lemma lem6882028 : term605 = term608.
Proof. exact (@lem6882017 (@lem6882027)). Qed.
Lemma lem6882030 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6882031 : term305 = term310.
Proof. exact (@lem6882030 term92 term92). Qed.
Lemma lem6882032 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882033 : term291 = term92.
Proof. exact (EQ_MP (@lem6882032) (@lem940073)). Qed.
Lemma lem6882034 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882035 : term289 = term224.
Proof. exact (MK_COMB (@lem6882034) (@lem6882033)). Qed.
Lemma lem6882036 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6882037 : term310 = term279.
Proof. exact (MK_COMB (@lem6882036) (@lem6882035)). Qed.
Lemma lem6882038 : term305 = term279.
Proof. exact (TRANS (@lem6882031) (@lem6882037)). Qed.
Lemma lem6882040 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6882041 : term343 = term214.
Proof. exact (@lem6882040 term92). Qed.
Lemma lem6882042 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6882043 : term609 = term216.
Proof. exact (MK_COMB (@lem6882042) (@lem6882041)). Qed.
Lemma lem6882044 : term608 = term603.
Proof. exact (MK_COMB (@lem6882043) (@lem6882038)). Qed.
Lemma lem6882046 (m : nat) (n : nat) : (term610 m n) = (term611 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6882047 : term603 = term612.
Proof. exact (@lem6882046 (NUMERAL 0) term92). Qed.
Lemma lem6882048 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882049 (h1 : term333 = (BIT1 0)) : (term92 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6882050 : (term333 = (BIT1 0)) = ((term92 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882049 h1) (fun h1 : (term92 = (NUMERAL 0)) = False => @lem6882048)). Qed.
Lemma lem6882051 : (term92 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6882050) (@lem6882048)). Qed.
Lemma lem6882052 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6882053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6882054 : term613 = (and True).
Proof. exact (MK_COMB (@lem6882053) (@lem6882052)). Qed.
Lemma lem6882055 : term612 = (True /\ False).
Proof. exact (MK_COMB (@lem6882054) (@lem6882051)). Qed.
Lemma lem6882057 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6882058 : term612 = False.
Proof. exact (TRANS (@lem6882055) (@lem6882057)). Qed.
Lemma lem6882059 : term603 = False.
Proof. exact (TRANS (@lem6882047) (@lem6882058)). Qed.
Lemma lem6882060 : term608 = False.
Proof. exact (TRANS (@lem6882044) (@lem6882059)). Qed.
Lemma lem6882061 : term605 = False.
Proof. exact (TRANS (@lem6882028) (@lem6882060)). Qed.
Lemma lem6882062 : term603 = False.
Proof. exact (TRANS (@lem6882005) (@lem6882061)). Qed.
Lemma lem6882063 : term602 = False.
Proof. exact (TRANS (@lem6881996) (@lem6882062)). Qed.
Lemma lem6882064 (_91911 : int) (_91912 : int) (h1 : term700 _91911 _91912) : False.
Proof. exact (EQ_MP (@lem6882063) (@lem6881993 _91911 _91912 h1)). Qed.
Lemma lem6882065 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term701 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6882066 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term514 _91911 _91912.
Proof. exact (proj2 (@lem6882065 _91911 _91912 h1)). Qed.
Lemma lem6882068 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term465 _91911 _91912.
Proof. exact (proj2 (@lem6882066 _91911 _91912 h1)). Qed.
Lemma lem6882070 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term415 _91911 _91912.
Proof. exact (proj2 (@lem6882068 _91911 _91912 h1)). Qed.
Lemma lem6882071 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term352 _91912 _91911.
Proof. exact (proj1 (@lem6882068 _91911 _91912 h1)). Qed.
Lemma lem6882072 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : (real_of_int _91911) = term214.
Proof. exact (proj2 (@lem6882071 _91911 _91912 h1)). Qed.
Lemma lem6882074 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term382 _91912.
Proof. exact (proj2 (@lem6882070 _91911 _91912 h1)). Qed.
Lemma lem6882075 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term360 _91911 _91912.
Proof. exact (proj1 (@lem6882070 _91911 _91912 h1)). Qed.
Lemma lem6882077 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6882078 : term551 = term331.
Proof. exact (@lem6882077 term214 term224). Qed.
Lemma lem6882080 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6882081 : term224 = term304.
Proof. exact (@lem6882080 term92). Qed.
Lemma lem6882083 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6882084 : term214 = term276.
Proof. exact (@lem6882083 (NUMERAL 0)). Qed.
Lemma lem6882085 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6882086 : term552 = term553.
Proof. exact (MK_COMB (@lem6882085) (@lem6882084)). Qed.
Lemma lem6882087 : term331 = term554.
Proof. exact (MK_COMB (@lem6882086) (@lem6882081)). Qed.
Lemma lem6882088 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6882090 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882091 : term331 = term332.
Proof. exact (@lem6882090 (NUMERAL 0) term92). Qed.
Lemma lem6882092 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882093 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882094 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882093 h1) (fun h1 : term332 = True => @lem6882092)). Qed.
Lemma lem6882095 : term332 = True.
Proof. exact (EQ_MP (@lem6882094) (@lem6882092)). Qed.
Lemma lem6882096 : term331 = True.
Proof. exact (TRANS (@lem6882091) (@lem6882095)). Qed.
Lemma lem6882097 : True = term331.
Proof. exact (SYM (@lem6882096)). Qed.
Lemma lem6882098 : term331.
Proof. exact (EQ_MP (@lem6882097) (@lem0)). Qed.
Lemma lem6882099 : term556.
Proof. exact (@lem6882088 (@lem6882098)). Qed.
Lemma lem6882101 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882102 : term331 = term332.
Proof. exact (@lem6882101 (NUMERAL 0) term92). Qed.
Lemma lem6882103 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882104 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882105 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882104 h1) (fun h1 : term332 = True => @lem6882103)). Qed.
Lemma lem6882106 : term332 = True.
Proof. exact (EQ_MP (@lem6882105) (@lem6882103)). Qed.
Lemma lem6882107 : term331 = True.
Proof. exact (TRANS (@lem6882102) (@lem6882106)). Qed.
Lemma lem6882108 : True = term331.
Proof. exact (SYM (@lem6882107)). Qed.
Lemma lem6882109 : term331.
Proof. exact (EQ_MP (@lem6882108) (@lem0)). Qed.
Lemma lem6882110 : term554 = term557.
Proof. exact (@lem6882099 (@lem6882109)). Qed.
Lemma lem6882112 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6882113 : term288 = term289.
Proof. exact (@lem6882112 term92 term92). Qed.
Lemma lem6882114 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882115 : term291 = term92.
Proof. exact (EQ_MP (@lem6882114) (@lem940073)). Qed.
Lemma lem6882116 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882117 : term289 = term224.
Proof. exact (MK_COMB (@lem6882116) (@lem6882115)). Qed.
Lemma lem6882118 : term288 = term224.
Proof. exact (TRANS (@lem6882113) (@lem6882117)). Qed.
Lemma lem6882120 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6882121 : term343 = term214.
Proof. exact (@lem6882120 term92). Qed.
Lemma lem6882122 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6882123 : term558 = term552.
Proof. exact (MK_COMB (@lem6882122) (@lem6882121)). Qed.
Lemma lem6882124 : term557 = term331.
Proof. exact (MK_COMB (@lem6882123) (@lem6882118)). Qed.
Lemma lem6882126 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882127 : term331 = term332.
Proof. exact (@lem6882126 (NUMERAL 0) term92). Qed.
Lemma lem6882128 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882129 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882130 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882129 h1) (fun h1 : term332 = True => @lem6882128)). Qed.
Lemma lem6882131 : term332 = True.
Proof. exact (EQ_MP (@lem6882130) (@lem6882128)). Qed.
Lemma lem6882132 : term331 = True.
Proof. exact (TRANS (@lem6882127) (@lem6882131)). Qed.
Lemma lem6882133 : term557 = True.
Proof. exact (TRANS (@lem6882124) (@lem6882132)). Qed.
Lemma lem6882134 : term554 = True.
Proof. exact (TRANS (@lem6882110) (@lem6882133)). Qed.
Lemma lem6882135 : term331 = True.
Proof. exact (TRANS (@lem6882087) (@lem6882134)). Qed.
Lemma lem6882136 : term551 = True.
Proof. exact (TRANS (@lem6882078) (@lem6882135)). Qed.
Lemma lem6882137 : True = term551.
Proof. exact (SYM (@lem6882136)). Qed.
Lemma lem6882138 : term551.
Proof. exact (EQ_MP (@lem6882137) (@lem0)). Qed.
Lemma lem6882139 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term631 _91912.
Proof. exact (conj (@lem6882138) (@lem6882074 _91911 _91912 h1)). Qed.
Lemma lem6882141 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6882142 (_91912 : int) : term632 _91912.
Proof. exact (@lem6882141 term224 (term379 _91912)). Qed.
Lemma lem6882143 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term633 _91912.
Proof. exact (@lem6882142 _91912 (@lem6882139 _91911 _91912 h1)). Qed.
Lemma lem6882144 (_91912 : int) : (term634 _91912) = (term379 _91912).
Proof. exact (@lem1982733 (term379 _91912)). Qed.
Lemma lem6882145 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6882146 (_91912 : int) : (term635 _91912) = (term381 _91912).
Proof. exact (MK_COMB (@lem6882145) (@lem6882144 _91912)). Qed.
Lemma lem6882147 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6882148 (_91912 : int) : (term633 _91912) = (term382 _91912).
Proof. exact (MK_COMB (@lem6882146 _91912) (@lem6882147)). Qed.
Lemma lem6882149 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term382 _91912.
Proof. exact (EQ_MP (@lem6882148 _91912) (@lem6882143 _91911 _91912 h1)). Qed.
Lemma lem6882151 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6882152 : term551 = term331.
Proof. exact (@lem6882151 term214 term224). Qed.
Lemma lem6882154 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6882155 : term224 = term304.
Proof. exact (@lem6882154 term92). Qed.
Lemma lem6882157 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6882158 : term214 = term276.
Proof. exact (@lem6882157 (NUMERAL 0)). Qed.
Lemma lem6882159 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6882160 : term552 = term553.
Proof. exact (MK_COMB (@lem6882159) (@lem6882158)). Qed.
Lemma lem6882161 : term331 = term554.
Proof. exact (MK_COMB (@lem6882160) (@lem6882155)). Qed.
Lemma lem6882162 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6882164 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882165 : term331 = term332.
Proof. exact (@lem6882164 (NUMERAL 0) term92). Qed.
Lemma lem6882166 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882167 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882168 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882167 h1) (fun h1 : term332 = True => @lem6882166)). Qed.
Lemma lem6882169 : term332 = True.
Proof. exact (EQ_MP (@lem6882168) (@lem6882166)). Qed.
Lemma lem6882170 : term331 = True.
Proof. exact (TRANS (@lem6882165) (@lem6882169)). Qed.
Lemma lem6882171 : True = term331.
Proof. exact (SYM (@lem6882170)). Qed.
Lemma lem6882172 : term331.
Proof. exact (EQ_MP (@lem6882171) (@lem0)). Qed.
Lemma lem6882173 : term556.
Proof. exact (@lem6882162 (@lem6882172)). Qed.
Lemma lem6882175 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882176 : term331 = term332.
Proof. exact (@lem6882175 (NUMERAL 0) term92). Qed.
Lemma lem6882177 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882178 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882179 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882178 h1) (fun h1 : term332 = True => @lem6882177)). Qed.
Lemma lem6882180 : term332 = True.
Proof. exact (EQ_MP (@lem6882179) (@lem6882177)). Qed.
Lemma lem6882181 : term331 = True.
Proof. exact (TRANS (@lem6882176) (@lem6882180)). Qed.
Lemma lem6882182 : True = term331.
Proof. exact (SYM (@lem6882181)). Qed.
Lemma lem6882183 : term331.
Proof. exact (EQ_MP (@lem6882182) (@lem0)). Qed.
Lemma lem6882184 : term554 = term557.
Proof. exact (@lem6882173 (@lem6882183)). Qed.
Lemma lem6882186 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6882187 : term288 = term289.
Proof. exact (@lem6882186 term92 term92). Qed.
Lemma lem6882188 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882189 : term291 = term92.
Proof. exact (EQ_MP (@lem6882188) (@lem940073)). Qed.
Lemma lem6882190 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882191 : term289 = term224.
Proof. exact (MK_COMB (@lem6882190) (@lem6882189)). Qed.
Lemma lem6882192 : term288 = term224.
Proof. exact (TRANS (@lem6882187) (@lem6882191)). Qed.
Lemma lem6882194 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6882195 : term343 = term214.
Proof. exact (@lem6882194 term92). Qed.
Lemma lem6882196 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6882197 : term558 = term552.
Proof. exact (MK_COMB (@lem6882196) (@lem6882195)). Qed.
Lemma lem6882198 : term557 = term331.
Proof. exact (MK_COMB (@lem6882197) (@lem6882192)). Qed.
Lemma lem6882200 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882201 : term331 = term332.
Proof. exact (@lem6882200 (NUMERAL 0) term92). Qed.
Lemma lem6882202 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882203 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882204 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882203 h1) (fun h1 : term332 = True => @lem6882202)). Qed.
Lemma lem6882205 : term332 = True.
Proof. exact (EQ_MP (@lem6882204) (@lem6882202)). Qed.
Lemma lem6882206 : term331 = True.
Proof. exact (TRANS (@lem6882201) (@lem6882205)). Qed.
Lemma lem6882207 : term557 = True.
Proof. exact (TRANS (@lem6882198) (@lem6882206)). Qed.
Lemma lem6882208 : term554 = True.
Proof. exact (TRANS (@lem6882184) (@lem6882207)). Qed.
Lemma lem6882209 : term331 = True.
Proof. exact (TRANS (@lem6882161) (@lem6882208)). Qed.
Lemma lem6882210 : term551 = True.
Proof. exact (TRANS (@lem6882152) (@lem6882209)). Qed.
Lemma lem6882211 : True = term551.
Proof. exact (SYM (@lem6882210)). Qed.
Lemma lem6882212 : term551.
Proof. exact (EQ_MP (@lem6882211) (@lem0)). Qed.
Lemma lem6882213 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term559 _91911 _91912.
Proof. exact (conj (@lem6882212) (@lem6882075 _91911 _91912 h1)). Qed.
Lemma lem6882215 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6882216 (_91911 : int) (_91912 : int) : term561 _91911 _91912.
Proof. exact (@lem6882215 term224 (term357 _91911 _91912)). Qed.
Lemma lem6882217 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term562 _91911 _91912.
Proof. exact (@lem6882216 _91911 _91912 (@lem6882213 _91911 _91912 h1)). Qed.
Lemma lem6882218 (_91911 : int) (_91912 : int) : (term563 _91911 _91912) = (term357 _91911 _91912).
Proof. exact (@lem1982733 (term357 _91911 _91912)). Qed.
Lemma lem6882219 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6882220 (_91911 : int) (_91912 : int) : (term564 _91911 _91912) = (term359 _91911 _91912).
Proof. exact (MK_COMB (@lem6882219) (@lem6882218 _91911 _91912)). Qed.
Lemma lem6882221 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6882222 (_91911 : int) (_91912 : int) : (term562 _91911 _91912) = (term360 _91911 _91912).
Proof. exact (MK_COMB (@lem6882220 _91911 _91912) (@lem6882221)). Qed.
Lemma lem6882223 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term360 _91911 _91912.
Proof. exact (EQ_MP (@lem6882222 _91911 _91912) (@lem6882217 _91911 _91912 h1)). Qed.
Lemma lem6882225 (y : real) : term565 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6882226 (_91911 : int) : term619 _91911.
Proof. exact (@lem6882225 (real_of_int _91911)). Qed.
Lemma lem6882227 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term620 _91911.
Proof. exact (@lem6882226 _91911 (@lem6882072 _91911 _91912 h1)). Qed.
Lemma lem6882228 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term636 _91911.
Proof. exact (@lem6882227 _91911 _91912 h1 term279). Qed.
Lemma lem6882229 (_91911 : int) : (term636 _91911) = ((term317 _91911) = term214).
Proof. exact (eq_refl (term636 _91911)). Qed.
Lemma lem6882236 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : (term317 _91911) = term214.
Proof. exact (EQ_MP (@lem6882229 _91911) (@lem6882228 _91911 _91912 h1)). Qed.
Lemma lem6882237 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term637 _91911 _91912.
Proof. exact (conj (@lem6882236 _91911 _91912 h1) (@lem6882223 _91911 _91912 h1)). Qed.
Lemma lem6882239 (x : real) (y : real) : term572 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6882240 (_91911 : int) (_91912 : int) : term638 _91911 _91912.
Proof. exact (@lem6882239 (term317 _91911) (term357 _91911 _91912)). Qed.
Lemma lem6882241 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term639 _91911 _91912.
Proof. exact (@lem6882240 _91911 _91912 (@lem6882237 _91911 _91912 h1)). Qed.
Lemma lem6882242 (_91911 : int) (_91912 : int) : (term640 _91911 _91912) = (term641 _91911 _91912).
Proof. exact (@lem1982763 (term317 _91911) (real_of_int _91911) (term317 _91912)). Qed.
Lemma lem6882243 (_91911 : int) : (term577 _91911) = (term578 _91911).
Proof. exact (@lem1982713 term279 (real_of_int _91911)). Qed.
Lemma lem6882245 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6882246 : term224 = term304.
Proof. exact (@lem6882245 term92). Qed.
Lemma lem6882248 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6882249 : term279 = term280.
Proof. exact (@lem6882248 term92). Qed.
Lemma lem6882250 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6882251 : term579 = term580.
Proof. exact (MK_COMB (@lem6882250) (@lem6882249)). Qed.
Lemma lem6882252 : term581 = term582.
Proof. exact (MK_COMB (@lem6882251) (@lem6882246)). Qed.
Lemma lem6882253 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6882255 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882256 : term331 = term332.
Proof. exact (@lem6882255 (NUMERAL 0) term92). Qed.
Lemma lem6882257 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882258 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882259 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882258 h1) (fun h1 : term332 = True => @lem6882257)). Qed.
Lemma lem6882260 : term332 = True.
Proof. exact (EQ_MP (@lem6882259) (@lem6882257)). Qed.
Lemma lem6882261 : term331 = True.
Proof. exact (TRANS (@lem6882256) (@lem6882260)). Qed.
Lemma lem6882262 : True = term331.
Proof. exact (SYM (@lem6882261)). Qed.
Lemma lem6882263 : term331.
Proof. exact (EQ_MP (@lem6882262) (@lem0)). Qed.
Lemma lem6882264 : term584.
Proof. exact (@lem6882253 (@lem6882263)). Qed.
Lemma lem6882266 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882267 : term331 = term332.
Proof. exact (@lem6882266 (NUMERAL 0) term92). Qed.
Lemma lem6882268 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882269 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882270 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882269 h1) (fun h1 : term332 = True => @lem6882268)). Qed.
Lemma lem6882271 : term332 = True.
Proof. exact (EQ_MP (@lem6882270) (@lem6882268)). Qed.
Lemma lem6882272 : term331 = True.
Proof. exact (TRANS (@lem6882267) (@lem6882271)). Qed.
Lemma lem6882273 : True = term331.
Proof. exact (SYM (@lem6882272)). Qed.
Lemma lem6882274 : term331.
Proof. exact (EQ_MP (@lem6882273) (@lem0)). Qed.
Lemma lem6882275 : term585.
Proof. exact (@lem6882264 (@lem6882274)). Qed.
Lemma lem6882277 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882278 : term331 = term332.
Proof. exact (@lem6882277 (NUMERAL 0) term92). Qed.
Lemma lem6882279 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882280 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882281 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882280 h1) (fun h1 : term332 = True => @lem6882279)). Qed.
Lemma lem6882282 : term332 = True.
Proof. exact (EQ_MP (@lem6882281) (@lem6882279)). Qed.
Lemma lem6882283 : term331 = True.
Proof. exact (TRANS (@lem6882278) (@lem6882282)). Qed.
Lemma lem6882284 : True = term331.
Proof. exact (SYM (@lem6882283)). Qed.
Lemma lem6882285 : term331.
Proof. exact (EQ_MP (@lem6882284) (@lem0)). Qed.
Lemma lem6882286 : term586.
Proof. exact (@lem6882275 (@lem6882285)). Qed.
Lemma lem6882288 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6882289 : term288 = term289.
Proof. exact (@lem6882288 term92 term92). Qed.
Lemma lem6882290 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882291 : term291 = term92.
Proof. exact (EQ_MP (@lem6882290) (@lem940073)). Qed.
Lemma lem6882292 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882293 : term289 = term224.
Proof. exact (MK_COMB (@lem6882292) (@lem6882291)). Qed.
Lemma lem6882294 : term288 = term224.
Proof. exact (TRANS (@lem6882289) (@lem6882293)). Qed.
Lemma lem6882296 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6882297 : term305 = term310.
Proof. exact (@lem6882296 term92 term92). Qed.
Lemma lem6882298 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882299 : term291 = term92.
Proof. exact (EQ_MP (@lem6882298) (@lem940073)). Qed.
Lemma lem6882300 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882301 : term289 = term224.
Proof. exact (MK_COMB (@lem6882300) (@lem6882299)). Qed.
Lemma lem6882302 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6882303 : term310 = term279.
Proof. exact (MK_COMB (@lem6882302) (@lem6882301)). Qed.
Lemma lem6882304 : term305 = term279.
Proof. exact (TRANS (@lem6882297) (@lem6882303)). Qed.
Lemma lem6882305 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6882306 : term587 = term579.
Proof. exact (MK_COMB (@lem6882305) (@lem6882304)). Qed.
Lemma lem6882307 : term588 = term581.
Proof. exact (MK_COMB (@lem6882306) (@lem6882294)). Qed.
Lemma lem6882309 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6882310 : term581 = term214.
Proof. exact (@lem6882309 term92). Qed.
Lemma lem6882311 : term588 = term214.
Proof. exact (TRANS (@lem6882307) (@lem6882310)). Qed.
Lemma lem6882312 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6882313 : term590 = term341.
Proof. exact (MK_COMB (@lem6882312) (@lem6882311)). Qed.
Lemma lem6882314 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6882315 : term591 = term343.
Proof. exact (MK_COMB (@lem6882313) (@lem6882314)). Qed.
Lemma lem6882317 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6882318 : term343 = term214.
Proof. exact (@lem6882317 term92). Qed.
Lemma lem6882319 : term591 = term214.
Proof. exact (TRANS (@lem6882315) (@lem6882318)). Qed.
Lemma lem6882321 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6882322 : term288 = term289.
Proof. exact (@lem6882321 term92 term92). Qed.
Lemma lem6882323 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882324 : term291 = term92.
Proof. exact (EQ_MP (@lem6882323) (@lem940073)). Qed.
Lemma lem6882325 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882326 : term289 = term224.
Proof. exact (MK_COMB (@lem6882325) (@lem6882324)). Qed.
Lemma lem6882327 : term288 = term224.
Proof. exact (TRANS (@lem6882322) (@lem6882326)). Qed.
Lemma lem6882328 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6882329 : term345 = term343.
Proof. exact (MK_COMB (@lem6882328) (@lem6882327)). Qed.
Lemma lem6882331 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6882332 : term343 = term214.
Proof. exact (@lem6882331 term92). Qed.
Lemma lem6882333 : term345 = term214.
Proof. exact (TRANS (@lem6882329) (@lem6882332)). Qed.
Lemma lem6882334 : term214 = term345.
Proof. exact (SYM (@lem6882333)). Qed.
Lemma lem6882335 : term591 = term345.
Proof. exact (TRANS (@lem6882319) (@lem6882334)). Qed.
Lemma lem6882336 : term582 = term276.
Proof. exact (@lem6882286 (@lem6882335)). Qed.
Lemma lem6882337 : term581 = term276.
Proof. exact (TRANS (@lem6882252) (@lem6882336)). Qed.
Lemma lem6882339 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6882340 : term276 = term214.
Proof. exact (@lem6882339 term214). Qed.
Lemma lem6882341 : term581 = term214.
Proof. exact (TRANS (@lem6882337) (@lem6882340)). Qed.
Lemma lem6882342 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6882343 : term592 = term341.
Proof. exact (MK_COMB (@lem6882342) (@lem6882341)). Qed.
Lemma lem6882344 (_91911 : int) : (real_of_int _91911) = (real_of_int _91911).
Proof. exact (eq_refl (real_of_int _91911)). Qed.
Lemma lem6882345 (_91911 : int) : (term578 _91911) = (term593 _91911).
Proof. exact (MK_COMB (@lem6882343) (@lem6882344 _91911)). Qed.
Lemma lem6882346 (_91911 : int) : (term577 _91911) = (term593 _91911).
Proof. exact (TRANS (@lem6882243 _91911) (@lem6882345 _91911)). Qed.
Lemma lem6882347 (_91911 : int) : (term593 _91911) = term214.
Proof. exact (@lem1982719 (real_of_int _91911)). Qed.
Lemma lem6882348 (_91911 : int) : (term577 _91911) = term214.
Proof. exact (TRANS (@lem6882346 _91911) (@lem6882347 _91911)). Qed.
Lemma lem6882349 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6882350 (_91911 : int) : (term594 _91911) = term256.
Proof. exact (MK_COMB (@lem6882349) (@lem6882348 _91911)). Qed.
Lemma lem6882351 (_91912 : int) : (term317 _91912) = (term317 _91912).
Proof. exact (eq_refl (term317 _91912)). Qed.
Lemma lem6882352 (_91911 : int) (_91912 : int) : (term641 _91911 _91912) = (term642 _91912).
Proof. exact (MK_COMB (@lem6882350 _91911) (@lem6882351 _91912)). Qed.
Lemma lem6882353 (_91911 : int) (_91912 : int) : (term640 _91911 _91912) = (term642 _91912).
Proof. exact (TRANS (@lem6882242 _91911 _91912) (@lem6882352 _91911 _91912)). Qed.
Lemma lem6882354 (_91912 : int) : (term642 _91912) = (term317 _91912).
Proof. exact (@lem1982721 (term317 _91912)). Qed.
Lemma lem6882355 (_91911 : int) (_91912 : int) : (term640 _91911 _91912) = (term317 _91912).
Proof. exact (TRANS (@lem6882353 _91911 _91912) (@lem6882354 _91912)). Qed.
Lemma lem6882356 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6882357 (_91911 : int) (_91912 : int) : (term643 _91911 _91912) = (term348 _91912).
Proof. exact (MK_COMB (@lem6882356) (@lem6882355 _91911 _91912)). Qed.
Lemma lem6882358 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6882359 (_91911 : int) (_91912 : int) : (term639 _91911 _91912) = (term349 _91912).
Proof. exact (MK_COMB (@lem6882357 _91911 _91912) (@lem6882358)). Qed.
Lemma lem6882360 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term349 _91912.
Proof. exact (EQ_MP (@lem6882359 _91911 _91912) (@lem6882241 _91911 _91912 h1)). Qed.
Lemma lem6882362 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6882363 : term551 = term331.
Proof. exact (@lem6882362 term214 term224). Qed.
Lemma lem6882365 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6882366 : term224 = term304.
Proof. exact (@lem6882365 term92). Qed.
Lemma lem6882368 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6882369 : term214 = term276.
Proof. exact (@lem6882368 (NUMERAL 0)). Qed.
Lemma lem6882370 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6882371 : term552 = term553.
Proof. exact (MK_COMB (@lem6882370) (@lem6882369)). Qed.
Lemma lem6882372 : term331 = term554.
Proof. exact (MK_COMB (@lem6882371) (@lem6882366)). Qed.
Lemma lem6882373 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6882375 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882376 : term331 = term332.
Proof. exact (@lem6882375 (NUMERAL 0) term92). Qed.
Lemma lem6882377 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882378 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882379 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882378 h1) (fun h1 : term332 = True => @lem6882377)). Qed.
Lemma lem6882380 : term332 = True.
Proof. exact (EQ_MP (@lem6882379) (@lem6882377)). Qed.
Lemma lem6882381 : term331 = True.
Proof. exact (TRANS (@lem6882376) (@lem6882380)). Qed.
Lemma lem6882382 : True = term331.
Proof. exact (SYM (@lem6882381)). Qed.
Lemma lem6882383 : term331.
Proof. exact (EQ_MP (@lem6882382) (@lem0)). Qed.
Lemma lem6882384 : term556.
Proof. exact (@lem6882373 (@lem6882383)). Qed.
Lemma lem6882386 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882387 : term331 = term332.
Proof. exact (@lem6882386 (NUMERAL 0) term92). Qed.
Lemma lem6882388 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882389 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882390 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882389 h1) (fun h1 : term332 = True => @lem6882388)). Qed.
Lemma lem6882391 : term332 = True.
Proof. exact (EQ_MP (@lem6882390) (@lem6882388)). Qed.
Lemma lem6882392 : term331 = True.
Proof. exact (TRANS (@lem6882387) (@lem6882391)). Qed.
Lemma lem6882393 : True = term331.
Proof. exact (SYM (@lem6882392)). Qed.
Lemma lem6882394 : term331.
Proof. exact (EQ_MP (@lem6882393) (@lem0)). Qed.
Lemma lem6882395 : term554 = term557.
Proof. exact (@lem6882384 (@lem6882394)). Qed.
Lemma lem6882397 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6882398 : term288 = term289.
Proof. exact (@lem6882397 term92 term92). Qed.
Lemma lem6882399 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882400 : term291 = term92.
Proof. exact (EQ_MP (@lem6882399) (@lem940073)). Qed.
Lemma lem6882401 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882402 : term289 = term224.
Proof. exact (MK_COMB (@lem6882401) (@lem6882400)). Qed.
Lemma lem6882403 : term288 = term224.
Proof. exact (TRANS (@lem6882398) (@lem6882402)). Qed.
Lemma lem6882405 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6882406 : term343 = term214.
Proof. exact (@lem6882405 term92). Qed.
Lemma lem6882407 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6882408 : term558 = term552.
Proof. exact (MK_COMB (@lem6882407) (@lem6882406)). Qed.
Lemma lem6882409 : term557 = term331.
Proof. exact (MK_COMB (@lem6882408) (@lem6882403)). Qed.
Lemma lem6882411 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882412 : term331 = term332.
Proof. exact (@lem6882411 (NUMERAL 0) term92). Qed.
Lemma lem6882413 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882414 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882415 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882414 h1) (fun h1 : term332 = True => @lem6882413)). Qed.
Lemma lem6882416 : term332 = True.
Proof. exact (EQ_MP (@lem6882415) (@lem6882413)). Qed.
Lemma lem6882417 : term331 = True.
Proof. exact (TRANS (@lem6882412) (@lem6882416)). Qed.
Lemma lem6882418 : term557 = True.
Proof. exact (TRANS (@lem6882409) (@lem6882417)). Qed.
Lemma lem6882419 : term554 = True.
Proof. exact (TRANS (@lem6882395) (@lem6882418)). Qed.
Lemma lem6882420 : term331 = True.
Proof. exact (TRANS (@lem6882372) (@lem6882419)). Qed.
Lemma lem6882421 : term551 = True.
Proof. exact (TRANS (@lem6882363) (@lem6882420)). Qed.
Lemma lem6882422 : True = term551.
Proof. exact (SYM (@lem6882421)). Qed.
Lemma lem6882423 : term551.
Proof. exact (EQ_MP (@lem6882422) (@lem0)). Qed.
Lemma lem6882424 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term644 _91912.
Proof. exact (conj (@lem6882423) (@lem6882360 _91911 _91912 h1)). Qed.
Lemma lem6882426 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6882427 (_91912 : int) : term645 _91912.
Proof. exact (@lem6882426 term224 (term317 _91912)). Qed.
Lemma lem6882428 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term646 _91912.
Proof. exact (@lem6882427 _91912 (@lem6882424 _91911 _91912 h1)). Qed.
Lemma lem6882429 (_91912 : int) : (term647 _91912) = (term317 _91912).
Proof. exact (@lem1982733 (term317 _91912)). Qed.
Lemma lem6882430 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6882431 (_91912 : int) : (term648 _91912) = (term348 _91912).
Proof. exact (MK_COMB (@lem6882430) (@lem6882429 _91912)). Qed.
Lemma lem6882432 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6882433 (_91912 : int) : (term646 _91912) = (term349 _91912).
Proof. exact (MK_COMB (@lem6882431 _91912) (@lem6882432)). Qed.
Lemma lem6882434 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term349 _91912.
Proof. exact (EQ_MP (@lem6882433 _91912) (@lem6882428 _91911 _91912 h1)). Qed.
Lemma lem6882435 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term649 _91912.
Proof. exact (conj (@lem6882434 _91911 _91912 h1) (@lem6882149 _91911 _91912 h1)). Qed.
Lemma lem6882437 (x : real) (y : real) : term650 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem6882438 (_91912 : int) : term651 _91912.
Proof. exact (@lem6882437 (term317 _91912) (term379 _91912)). Qed.
Lemma lem6882439 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term652 _91912.
Proof. exact (@lem6882438 _91912 (@lem6882435 _91911 _91912 h1)). Qed.
Lemma lem6882440 (_91912 : int) : (term653 _91912) = (term654 _91912).
Proof. exact (@lem1982763 (term317 _91912) (real_of_int _91912) term279). Qed.
Lemma lem6882441 (_91912 : int) : (term577 _91912) = (term578 _91912).
Proof. exact (@lem1982713 term279 (real_of_int _91912)). Qed.
Lemma lem6882443 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6882444 : term224 = term304.
Proof. exact (@lem6882443 term92). Qed.
Lemma lem6882446 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6882447 : term279 = term280.
Proof. exact (@lem6882446 term92). Qed.
Lemma lem6882448 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6882449 : term579 = term580.
Proof. exact (MK_COMB (@lem6882448) (@lem6882447)). Qed.
Lemma lem6882450 : term581 = term582.
Proof. exact (MK_COMB (@lem6882449) (@lem6882444)). Qed.
Lemma lem6882451 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6882453 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882454 : term331 = term332.
Proof. exact (@lem6882453 (NUMERAL 0) term92). Qed.
Lemma lem6882455 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882456 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882457 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882456 h1) (fun h1 : term332 = True => @lem6882455)). Qed.
Lemma lem6882458 : term332 = True.
Proof. exact (EQ_MP (@lem6882457) (@lem6882455)). Qed.
Lemma lem6882459 : term331 = True.
Proof. exact (TRANS (@lem6882454) (@lem6882458)). Qed.
Lemma lem6882460 : True = term331.
Proof. exact (SYM (@lem6882459)). Qed.
Lemma lem6882461 : term331.
Proof. exact (EQ_MP (@lem6882460) (@lem0)). Qed.
Lemma lem6882462 : term584.
Proof. exact (@lem6882451 (@lem6882461)). Qed.
Lemma lem6882464 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882465 : term331 = term332.
Proof. exact (@lem6882464 (NUMERAL 0) term92). Qed.
Lemma lem6882466 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882467 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882468 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882467 h1) (fun h1 : term332 = True => @lem6882466)). Qed.
Lemma lem6882469 : term332 = True.
Proof. exact (EQ_MP (@lem6882468) (@lem6882466)). Qed.
Lemma lem6882470 : term331 = True.
Proof. exact (TRANS (@lem6882465) (@lem6882469)). Qed.
Lemma lem6882471 : True = term331.
Proof. exact (SYM (@lem6882470)). Qed.
Lemma lem6882472 : term331.
Proof. exact (EQ_MP (@lem6882471) (@lem0)). Qed.
Lemma lem6882473 : term585.
Proof. exact (@lem6882462 (@lem6882472)). Qed.
Lemma lem6882475 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882476 : term331 = term332.
Proof. exact (@lem6882475 (NUMERAL 0) term92). Qed.
Lemma lem6882477 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882478 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882479 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882478 h1) (fun h1 : term332 = True => @lem6882477)). Qed.
Lemma lem6882480 : term332 = True.
Proof. exact (EQ_MP (@lem6882479) (@lem6882477)). Qed.
Lemma lem6882481 : term331 = True.
Proof. exact (TRANS (@lem6882476) (@lem6882480)). Qed.
Lemma lem6882482 : True = term331.
Proof. exact (SYM (@lem6882481)). Qed.
Lemma lem6882483 : term331.
Proof. exact (EQ_MP (@lem6882482) (@lem0)). Qed.
Lemma lem6882484 : term586.
Proof. exact (@lem6882473 (@lem6882483)). Qed.
Lemma lem6882486 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6882487 : term288 = term289.
Proof. exact (@lem6882486 term92 term92). Qed.
Lemma lem6882488 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882489 : term291 = term92.
Proof. exact (EQ_MP (@lem6882488) (@lem940073)). Qed.
Lemma lem6882490 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882491 : term289 = term224.
Proof. exact (MK_COMB (@lem6882490) (@lem6882489)). Qed.
Lemma lem6882492 : term288 = term224.
Proof. exact (TRANS (@lem6882487) (@lem6882491)). Qed.
Lemma lem6882494 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6882495 : term305 = term310.
Proof. exact (@lem6882494 term92 term92). Qed.
Lemma lem6882496 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882497 : term291 = term92.
Proof. exact (EQ_MP (@lem6882496) (@lem940073)). Qed.
Lemma lem6882498 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882499 : term289 = term224.
Proof. exact (MK_COMB (@lem6882498) (@lem6882497)). Qed.
Lemma lem6882500 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6882501 : term310 = term279.
Proof. exact (MK_COMB (@lem6882500) (@lem6882499)). Qed.
Lemma lem6882502 : term305 = term279.
Proof. exact (TRANS (@lem6882495) (@lem6882501)). Qed.
Lemma lem6882503 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6882504 : term587 = term579.
Proof. exact (MK_COMB (@lem6882503) (@lem6882502)). Qed.
Lemma lem6882505 : term588 = term581.
Proof. exact (MK_COMB (@lem6882504) (@lem6882492)). Qed.
Lemma lem6882507 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6882508 : term581 = term214.
Proof. exact (@lem6882507 term92). Qed.
Lemma lem6882509 : term588 = term214.
Proof. exact (TRANS (@lem6882505) (@lem6882508)). Qed.
Lemma lem6882510 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6882511 : term590 = term341.
Proof. exact (MK_COMB (@lem6882510) (@lem6882509)). Qed.
Lemma lem6882512 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6882513 : term591 = term343.
Proof. exact (MK_COMB (@lem6882511) (@lem6882512)). Qed.
Lemma lem6882515 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6882516 : term343 = term214.
Proof. exact (@lem6882515 term92). Qed.
Lemma lem6882517 : term591 = term214.
Proof. exact (TRANS (@lem6882513) (@lem6882516)). Qed.
Lemma lem6882519 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6882520 : term288 = term289.
Proof. exact (@lem6882519 term92 term92). Qed.
Lemma lem6882521 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882522 : term291 = term92.
Proof. exact (EQ_MP (@lem6882521) (@lem940073)). Qed.
Lemma lem6882523 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882524 : term289 = term224.
Proof. exact (MK_COMB (@lem6882523) (@lem6882522)). Qed.
Lemma lem6882525 : term288 = term224.
Proof. exact (TRANS (@lem6882520) (@lem6882524)). Qed.
Lemma lem6882526 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6882527 : term345 = term343.
Proof. exact (MK_COMB (@lem6882526) (@lem6882525)). Qed.
Lemma lem6882529 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6882530 : term343 = term214.
Proof. exact (@lem6882529 term92). Qed.
Lemma lem6882531 : term345 = term214.
Proof. exact (TRANS (@lem6882527) (@lem6882530)). Qed.
Lemma lem6882532 : term214 = term345.
Proof. exact (SYM (@lem6882531)). Qed.
Lemma lem6882533 : term591 = term345.
Proof. exact (TRANS (@lem6882517) (@lem6882532)). Qed.
Lemma lem6882534 : term582 = term276.
Proof. exact (@lem6882484 (@lem6882533)). Qed.
Lemma lem6882535 : term581 = term276.
Proof. exact (TRANS (@lem6882450) (@lem6882534)). Qed.
Lemma lem6882537 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6882538 : term276 = term214.
Proof. exact (@lem6882537 term214). Qed.
Lemma lem6882539 : term581 = term214.
Proof. exact (TRANS (@lem6882535) (@lem6882538)). Qed.
Lemma lem6882540 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6882541 : term592 = term341.
Proof. exact (MK_COMB (@lem6882540) (@lem6882539)). Qed.
Lemma lem6882542 (_91912 : int) : (real_of_int _91912) = (real_of_int _91912).
Proof. exact (eq_refl (real_of_int _91912)). Qed.
Lemma lem6882543 (_91912 : int) : (term578 _91912) = (term593 _91912).
Proof. exact (MK_COMB (@lem6882541) (@lem6882542 _91912)). Qed.
Lemma lem6882544 (_91912 : int) : (term577 _91912) = (term593 _91912).
Proof. exact (TRANS (@lem6882441 _91912) (@lem6882543 _91912)). Qed.
Lemma lem6882545 (_91912 : int) : (term593 _91912) = term214.
Proof. exact (@lem1982719 (real_of_int _91912)). Qed.
Lemma lem6882546 (_91912 : int) : (term577 _91912) = term214.
Proof. exact (TRANS (@lem6882544 _91912) (@lem6882545 _91912)). Qed.
Lemma lem6882547 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6882548 (_91912 : int) : (term594 _91912) = term256.
Proof. exact (MK_COMB (@lem6882547) (@lem6882546 _91912)). Qed.
Lemma lem6882549 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem6882550 (_91912 : int) : (term654 _91912) = term599.
Proof. exact (MK_COMB (@lem6882548 _91912) (@lem6882549)). Qed.
Lemma lem6882551 (_91912 : int) : (term653 _91912) = term599.
Proof. exact (TRANS (@lem6882440 _91912) (@lem6882550 _91912)). Qed.
Lemma lem6882552 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6882553 (_91912 : int) : (term653 _91912) = term279.
Proof. exact (TRANS (@lem6882551 _91912) (@lem6882552)). Qed.
Lemma lem6882554 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6882555 (_91912 : int) : (term655 _91912) = term601.
Proof. exact (MK_COMB (@lem6882554) (@lem6882553 _91912)). Qed.
Lemma lem6882556 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6882557 (_91912 : int) : (term652 _91912) = term602.
Proof. exact (MK_COMB (@lem6882555 _91912) (@lem6882556)). Qed.
Lemma lem6882558 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : term602.
Proof. exact (EQ_MP (@lem6882557 _91912) (@lem6882439 _91911 _91912 h1)). Qed.
Lemma lem6882560 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6882561 : term602 = term603.
Proof. exact (@lem6882560 term214 term279). Qed.
Lemma lem6882563 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6882564 : term279 = term280.
Proof. exact (@lem6882563 term92). Qed.
Lemma lem6882566 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6882567 : term214 = term276.
Proof. exact (@lem6882566 (NUMERAL 0)). Qed.
Lemma lem6882568 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6882569 : term216 = term604.
Proof. exact (MK_COMB (@lem6882568) (@lem6882567)). Qed.
Lemma lem6882570 : term603 = term605.
Proof. exact (MK_COMB (@lem6882569) (@lem6882564)). Qed.
Lemma lem6882571 : term606.
Proof. exact (@lem1980026 term214 term224 term279 term224). Qed.
Lemma lem6882573 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882574 : term331 = term332.
Proof. exact (@lem6882573 (NUMERAL 0) term92). Qed.
Lemma lem6882575 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882576 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882577 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882576 h1) (fun h1 : term332 = True => @lem6882575)). Qed.
Lemma lem6882578 : term332 = True.
Proof. exact (EQ_MP (@lem6882577) (@lem6882575)). Qed.
Lemma lem6882579 : term331 = True.
Proof. exact (TRANS (@lem6882574) (@lem6882578)). Qed.
Lemma lem6882580 : True = term331.
Proof. exact (SYM (@lem6882579)). Qed.
Lemma lem6882581 : term331.
Proof. exact (EQ_MP (@lem6882580) (@lem0)). Qed.
Lemma lem6882582 : term607.
Proof. exact (@lem6882571 (@lem6882581)). Qed.
Lemma lem6882584 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882585 : term331 = term332.
Proof. exact (@lem6882584 (NUMERAL 0) term92). Qed.
Lemma lem6882586 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882587 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882588 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882587 h1) (fun h1 : term332 = True => @lem6882586)). Qed.
Lemma lem6882589 : term332 = True.
Proof. exact (EQ_MP (@lem6882588) (@lem6882586)). Qed.
Lemma lem6882590 : term331 = True.
Proof. exact (TRANS (@lem6882585) (@lem6882589)). Qed.
Lemma lem6882591 : True = term331.
Proof. exact (SYM (@lem6882590)). Qed.
Lemma lem6882592 : term331.
Proof. exact (EQ_MP (@lem6882591) (@lem0)). Qed.
Lemma lem6882593 : term605 = term608.
Proof. exact (@lem6882582 (@lem6882592)). Qed.
Lemma lem6882595 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6882596 : term305 = term310.
Proof. exact (@lem6882595 term92 term92). Qed.
Lemma lem6882597 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882598 : term291 = term92.
Proof. exact (EQ_MP (@lem6882597) (@lem940073)). Qed.
Lemma lem6882599 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882600 : term289 = term224.
Proof. exact (MK_COMB (@lem6882599) (@lem6882598)). Qed.
Lemma lem6882601 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6882602 : term310 = term279.
Proof. exact (MK_COMB (@lem6882601) (@lem6882600)). Qed.
Lemma lem6882603 : term305 = term279.
Proof. exact (TRANS (@lem6882596) (@lem6882602)). Qed.
Lemma lem6882605 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6882606 : term343 = term214.
Proof. exact (@lem6882605 term92). Qed.
Lemma lem6882607 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6882608 : term609 = term216.
Proof. exact (MK_COMB (@lem6882607) (@lem6882606)). Qed.
Lemma lem6882609 : term608 = term603.
Proof. exact (MK_COMB (@lem6882608) (@lem6882603)). Qed.
Lemma lem6882611 (m : nat) (n : nat) : (term610 m n) = (term611 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6882612 : term603 = term612.
Proof. exact (@lem6882611 (NUMERAL 0) term92). Qed.
Lemma lem6882613 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882614 (h1 : term333 = (BIT1 0)) : (term92 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6882615 : (term333 = (BIT1 0)) = ((term92 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882614 h1) (fun h1 : (term92 = (NUMERAL 0)) = False => @lem6882613)). Qed.
Lemma lem6882616 : (term92 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6882615) (@lem6882613)). Qed.
Lemma lem6882617 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6882618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6882619 : term613 = (and True).
Proof. exact (MK_COMB (@lem6882618) (@lem6882617)). Qed.
Lemma lem6882620 : term612 = (True /\ False).
Proof. exact (MK_COMB (@lem6882619) (@lem6882616)). Qed.
Lemma lem6882622 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6882623 : term612 = False.
Proof. exact (TRANS (@lem6882620) (@lem6882622)). Qed.
Lemma lem6882624 : term603 = False.
Proof. exact (TRANS (@lem6882612) (@lem6882623)). Qed.
Lemma lem6882625 : term608 = False.
Proof. exact (TRANS (@lem6882609) (@lem6882624)). Qed.
Lemma lem6882626 : term605 = False.
Proof. exact (TRANS (@lem6882593) (@lem6882625)). Qed.
Lemma lem6882627 : term603 = False.
Proof. exact (TRANS (@lem6882570) (@lem6882626)). Qed.
Lemma lem6882628 : term602 = False.
Proof. exact (TRANS (@lem6882561) (@lem6882627)). Qed.
Lemma lem6882629 (_91911 : int) (_91912 : int) (h1 : term701 _91911 _91912) : False.
Proof. exact (EQ_MP (@lem6882628) (@lem6882558 _91911 _91912 h1)). Qed.
Lemma lem6882630 (_91911 : int) (_91912 : int) (h1 : term512 _91911 _91912) : False.
Proof. exact (or_elim (@lem6881660 _91911 _91912 h1) (fun h0 : term700 _91911 _91912 => @lem6882064 _91911 _91912 h0) (fun h0 : term701 _91911 _91912 => @lem6882629 _91911 _91912 h0)). Qed.
Lemma lem6882631 (_91911 : int) (_91912 : int) (h1 : term508 _91911 _91912) : term508 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6882632 (_91911 : int) (_91912 : int) (h1 : term702 _91911 _91912) : term702 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6882633 (_91911 : int) (_91912 : int) (h1 : term702 _91911 _91912) : term509 _91911 _91912.
Proof. exact (proj2 (@lem6882632 _91911 _91912 h1)). Qed.
Lemma lem6882635 (_91911 : int) (_91912 : int) (h1 : term702 _91911 _91912) : term460 _91911 _91912.
Proof. exact (proj2 (@lem6882633 _91911 _91912 h1)). Qed.
Lemma lem6882637 (_91911 : int) (_91912 : int) (h1 : term702 _91911 _91912) : term416 _91912.
Proof. exact (proj2 (@lem6882635 _91911 _91912 h1)). Qed.
Lemma lem6882639 (_91911 : int) (_91912 : int) (h1 : term702 _91911 _91912) : term382 _91912.
Proof. exact (proj2 (@lem6882637 _91911 _91912 h1)). Qed.
Lemma lem6882640 (_91911 : int) (_91912 : int) (h1 : term702 _91911 _91912) : (real_of_int _91912) = term214.
Proof. exact (proj1 (@lem6882637 _91911 _91912 h1)). Qed.
Lemma lem6882642 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6882643 : term551 = term331.
Proof. exact (@lem6882642 term214 term224). Qed.
Lemma lem6882645 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6882646 : term224 = term304.
Proof. exact (@lem6882645 term92). Qed.
Lemma lem6882648 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6882649 : term214 = term276.
Proof. exact (@lem6882648 (NUMERAL 0)). Qed.
Lemma lem6882650 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6882651 : term552 = term553.
Proof. exact (MK_COMB (@lem6882650) (@lem6882649)). Qed.
Lemma lem6882652 : term331 = term554.
Proof. exact (MK_COMB (@lem6882651) (@lem6882646)). Qed.
Lemma lem6882653 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6882655 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882656 : term331 = term332.
Proof. exact (@lem6882655 (NUMERAL 0) term92). Qed.
Lemma lem6882657 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882658 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882659 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882658 h1) (fun h1 : term332 = True => @lem6882657)). Qed.
Lemma lem6882660 : term332 = True.
Proof. exact (EQ_MP (@lem6882659) (@lem6882657)). Qed.
Lemma lem6882661 : term331 = True.
Proof. exact (TRANS (@lem6882656) (@lem6882660)). Qed.
Lemma lem6882662 : True = term331.
Proof. exact (SYM (@lem6882661)). Qed.
Lemma lem6882663 : term331.
Proof. exact (EQ_MP (@lem6882662) (@lem0)). Qed.
Lemma lem6882664 : term556.
Proof. exact (@lem6882653 (@lem6882663)). Qed.
Lemma lem6882666 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882667 : term331 = term332.
Proof. exact (@lem6882666 (NUMERAL 0) term92). Qed.
Lemma lem6882668 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882669 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882670 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882669 h1) (fun h1 : term332 = True => @lem6882668)). Qed.
Lemma lem6882671 : term332 = True.
Proof. exact (EQ_MP (@lem6882670) (@lem6882668)). Qed.
Lemma lem6882672 : term331 = True.
Proof. exact (TRANS (@lem6882667) (@lem6882671)). Qed.
Lemma lem6882673 : True = term331.
Proof. exact (SYM (@lem6882672)). Qed.
Lemma lem6882674 : term331.
Proof. exact (EQ_MP (@lem6882673) (@lem0)). Qed.
Lemma lem6882675 : term554 = term557.
Proof. exact (@lem6882664 (@lem6882674)). Qed.
Lemma lem6882677 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6882678 : term288 = term289.
Proof. exact (@lem6882677 term92 term92). Qed.
Lemma lem6882679 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882680 : term291 = term92.
Proof. exact (EQ_MP (@lem6882679) (@lem940073)). Qed.
Lemma lem6882681 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882682 : term289 = term224.
Proof. exact (MK_COMB (@lem6882681) (@lem6882680)). Qed.
Lemma lem6882683 : term288 = term224.
Proof. exact (TRANS (@lem6882678) (@lem6882682)). Qed.
Lemma lem6882685 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6882686 : term343 = term214.
Proof. exact (@lem6882685 term92). Qed.
Lemma lem6882687 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6882688 : term558 = term552.
Proof. exact (MK_COMB (@lem6882687) (@lem6882686)). Qed.
Lemma lem6882689 : term557 = term331.
Proof. exact (MK_COMB (@lem6882688) (@lem6882683)). Qed.
Lemma lem6882691 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882692 : term331 = term332.
Proof. exact (@lem6882691 (NUMERAL 0) term92). Qed.
Lemma lem6882693 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882694 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882695 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882694 h1) (fun h1 : term332 = True => @lem6882693)). Qed.
Lemma lem6882696 : term332 = True.
Proof. exact (EQ_MP (@lem6882695) (@lem6882693)). Qed.
Lemma lem6882697 : term331 = True.
Proof. exact (TRANS (@lem6882692) (@lem6882696)). Qed.
Lemma lem6882698 : term557 = True.
Proof. exact (TRANS (@lem6882689) (@lem6882697)). Qed.
Lemma lem6882699 : term554 = True.
Proof. exact (TRANS (@lem6882675) (@lem6882698)). Qed.
Lemma lem6882700 : term331 = True.
Proof. exact (TRANS (@lem6882652) (@lem6882699)). Qed.
Lemma lem6882701 : term551 = True.
Proof. exact (TRANS (@lem6882643) (@lem6882700)). Qed.
Lemma lem6882702 : True = term551.
Proof. exact (SYM (@lem6882701)). Qed.
Lemma lem6882703 : term551.
Proof. exact (EQ_MP (@lem6882702) (@lem0)). Qed.
Lemma lem6882704 (_91911 : int) (_91912 : int) (h1 : term702 _91911 _91912) : term631 _91912.
Proof. exact (conj (@lem6882703) (@lem6882639 _91911 _91912 h1)). Qed.
Lemma lem6882706 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6882707 (_91912 : int) : term632 _91912.
Proof. exact (@lem6882706 term224 (term379 _91912)). Qed.
Lemma lem6882708 (_91911 : int) (_91912 : int) (h1 : term702 _91911 _91912) : term633 _91912.
Proof. exact (@lem6882707 _91912 (@lem6882704 _91911 _91912 h1)). Qed.
Lemma lem6882709 (_91912 : int) : (term634 _91912) = (term379 _91912).
Proof. exact (@lem1982733 (term379 _91912)). Qed.
Lemma lem6882710 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6882711 (_91912 : int) : (term635 _91912) = (term381 _91912).
Proof. exact (MK_COMB (@lem6882710) (@lem6882709 _91912)). Qed.
Lemma lem6882712 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6882713 (_91912 : int) : (term633 _91912) = (term382 _91912).
Proof. exact (MK_COMB (@lem6882711 _91912) (@lem6882712)). Qed.
Lemma lem6882714 (_91911 : int) (_91912 : int) (h1 : term702 _91911 _91912) : term382 _91912.
Proof. exact (EQ_MP (@lem6882713 _91912) (@lem6882708 _91911 _91912 h1)). Qed.
Lemma lem6882716 (y : real) : term565 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6882717 (_91912 : int) : term619 _91912.
Proof. exact (@lem6882716 (real_of_int _91912)). Qed.
Lemma lem6882718 (_91911 : int) (_91912 : int) (h1 : term702 _91911 _91912) : term620 _91912.
Proof. exact (@lem6882717 _91912 (@lem6882640 _91911 _91912 h1)). Qed.
Lemma lem6882719 (_91911 : int) (_91912 : int) (h1 : term702 _91911 _91912) : term636 _91912.
Proof. exact (@lem6882718 _91911 _91912 h1 term279). Qed.
Lemma lem6882720 (_91912 : int) : (term636 _91912) = ((term317 _91912) = term214).
Proof. exact (eq_refl (term636 _91912)). Qed.
Lemma lem6882727 (_91911 : int) (_91912 : int) (h1 : term702 _91911 _91912) : (term317 _91912) = term214.
Proof. exact (EQ_MP (@lem6882720 _91912) (@lem6882719 _91911 _91912 h1)). Qed.
Lemma lem6882728 (_91911 : int) (_91912 : int) (h1 : term702 _91911 _91912) : term703 _91912.
Proof. exact (conj (@lem6882727 _91911 _91912 h1) (@lem6882714 _91911 _91912 h1)). Qed.
Lemma lem6882730 (x : real) (y : real) : term572 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6882731 (_91912 : int) : term704 _91912.
Proof. exact (@lem6882730 (term317 _91912) (term379 _91912)). Qed.
Lemma lem6882732 (_91911 : int) (_91912 : int) (h1 : term702 _91911 _91912) : term652 _91912.
Proof. exact (@lem6882731 _91912 (@lem6882728 _91911 _91912 h1)). Qed.
Lemma lem6882733 (_91912 : int) : (term653 _91912) = (term654 _91912).
Proof. exact (@lem1982763 (term317 _91912) (real_of_int _91912) term279). Qed.
Lemma lem6882734 (_91912 : int) : (term577 _91912) = (term578 _91912).
Proof. exact (@lem1982713 term279 (real_of_int _91912)). Qed.
Lemma lem6882736 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6882737 : term224 = term304.
Proof. exact (@lem6882736 term92). Qed.
Lemma lem6882739 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6882740 : term279 = term280.
Proof. exact (@lem6882739 term92). Qed.
Lemma lem6882741 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6882742 : term579 = term580.
Proof. exact (MK_COMB (@lem6882741) (@lem6882740)). Qed.
Lemma lem6882743 : term581 = term582.
Proof. exact (MK_COMB (@lem6882742) (@lem6882737)). Qed.
Lemma lem6882744 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6882746 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882747 : term331 = term332.
Proof. exact (@lem6882746 (NUMERAL 0) term92). Qed.
Lemma lem6882748 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882749 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882750 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882749 h1) (fun h1 : term332 = True => @lem6882748)). Qed.
Lemma lem6882751 : term332 = True.
Proof. exact (EQ_MP (@lem6882750) (@lem6882748)). Qed.
Lemma lem6882752 : term331 = True.
Proof. exact (TRANS (@lem6882747) (@lem6882751)). Qed.
Lemma lem6882753 : True = term331.
Proof. exact (SYM (@lem6882752)). Qed.
Lemma lem6882754 : term331.
Proof. exact (EQ_MP (@lem6882753) (@lem0)). Qed.
Lemma lem6882755 : term584.
Proof. exact (@lem6882744 (@lem6882754)). Qed.
Lemma lem6882757 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882758 : term331 = term332.
Proof. exact (@lem6882757 (NUMERAL 0) term92). Qed.
Lemma lem6882759 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882760 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882761 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882760 h1) (fun h1 : term332 = True => @lem6882759)). Qed.
Lemma lem6882762 : term332 = True.
Proof. exact (EQ_MP (@lem6882761) (@lem6882759)). Qed.
Lemma lem6882763 : term331 = True.
Proof. exact (TRANS (@lem6882758) (@lem6882762)). Qed.
Lemma lem6882764 : True = term331.
Proof. exact (SYM (@lem6882763)). Qed.
Lemma lem6882765 : term331.
Proof. exact (EQ_MP (@lem6882764) (@lem0)). Qed.
Lemma lem6882766 : term585.
Proof. exact (@lem6882755 (@lem6882765)). Qed.
Lemma lem6882768 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882769 : term331 = term332.
Proof. exact (@lem6882768 (NUMERAL 0) term92). Qed.
Lemma lem6882770 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882771 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882772 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882771 h1) (fun h1 : term332 = True => @lem6882770)). Qed.
Lemma lem6882773 : term332 = True.
Proof. exact (EQ_MP (@lem6882772) (@lem6882770)). Qed.
Lemma lem6882774 : term331 = True.
Proof. exact (TRANS (@lem6882769) (@lem6882773)). Qed.
Lemma lem6882775 : True = term331.
Proof. exact (SYM (@lem6882774)). Qed.
Lemma lem6882776 : term331.
Proof. exact (EQ_MP (@lem6882775) (@lem0)). Qed.
Lemma lem6882777 : term586.
Proof. exact (@lem6882766 (@lem6882776)). Qed.
Lemma lem6882779 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6882780 : term288 = term289.
Proof. exact (@lem6882779 term92 term92). Qed.
Lemma lem6882781 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882782 : term291 = term92.
Proof. exact (EQ_MP (@lem6882781) (@lem940073)). Qed.
Lemma lem6882783 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882784 : term289 = term224.
Proof. exact (MK_COMB (@lem6882783) (@lem6882782)). Qed.
Lemma lem6882785 : term288 = term224.
Proof. exact (TRANS (@lem6882780) (@lem6882784)). Qed.
Lemma lem6882787 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6882788 : term305 = term310.
Proof. exact (@lem6882787 term92 term92). Qed.
Lemma lem6882789 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882790 : term291 = term92.
Proof. exact (EQ_MP (@lem6882789) (@lem940073)). Qed.
Lemma lem6882791 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882792 : term289 = term224.
Proof. exact (MK_COMB (@lem6882791) (@lem6882790)). Qed.
Lemma lem6882793 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6882794 : term310 = term279.
Proof. exact (MK_COMB (@lem6882793) (@lem6882792)). Qed.
Lemma lem6882795 : term305 = term279.
Proof. exact (TRANS (@lem6882788) (@lem6882794)). Qed.
Lemma lem6882796 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6882797 : term587 = term579.
Proof. exact (MK_COMB (@lem6882796) (@lem6882795)). Qed.
Lemma lem6882798 : term588 = term581.
Proof. exact (MK_COMB (@lem6882797) (@lem6882785)). Qed.
Lemma lem6882800 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6882801 : term581 = term214.
Proof. exact (@lem6882800 term92). Qed.
Lemma lem6882802 : term588 = term214.
Proof. exact (TRANS (@lem6882798) (@lem6882801)). Qed.
Lemma lem6882803 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6882804 : term590 = term341.
Proof. exact (MK_COMB (@lem6882803) (@lem6882802)). Qed.
Lemma lem6882805 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6882806 : term591 = term343.
Proof. exact (MK_COMB (@lem6882804) (@lem6882805)). Qed.
Lemma lem6882808 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6882809 : term343 = term214.
Proof. exact (@lem6882808 term92). Qed.
Lemma lem6882810 : term591 = term214.
Proof. exact (TRANS (@lem6882806) (@lem6882809)). Qed.
Lemma lem6882812 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6882813 : term288 = term289.
Proof. exact (@lem6882812 term92 term92). Qed.
Lemma lem6882814 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882815 : term291 = term92.
Proof. exact (EQ_MP (@lem6882814) (@lem940073)). Qed.
Lemma lem6882816 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882817 : term289 = term224.
Proof. exact (MK_COMB (@lem6882816) (@lem6882815)). Qed.
Lemma lem6882818 : term288 = term224.
Proof. exact (TRANS (@lem6882813) (@lem6882817)). Qed.
Lemma lem6882819 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6882820 : term345 = term343.
Proof. exact (MK_COMB (@lem6882819) (@lem6882818)). Qed.
Lemma lem6882822 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6882823 : term343 = term214.
Proof. exact (@lem6882822 term92). Qed.
Lemma lem6882824 : term345 = term214.
Proof. exact (TRANS (@lem6882820) (@lem6882823)). Qed.
Lemma lem6882825 : term214 = term345.
Proof. exact (SYM (@lem6882824)). Qed.
Lemma lem6882826 : term591 = term345.
Proof. exact (TRANS (@lem6882810) (@lem6882825)). Qed.
Lemma lem6882827 : term582 = term276.
Proof. exact (@lem6882777 (@lem6882826)). Qed.
Lemma lem6882828 : term581 = term276.
Proof. exact (TRANS (@lem6882743) (@lem6882827)). Qed.
Lemma lem6882830 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6882831 : term276 = term214.
Proof. exact (@lem6882830 term214). Qed.
Lemma lem6882832 : term581 = term214.
Proof. exact (TRANS (@lem6882828) (@lem6882831)). Qed.
Lemma lem6882833 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6882834 : term592 = term341.
Proof. exact (MK_COMB (@lem6882833) (@lem6882832)). Qed.
Lemma lem6882835 (_91912 : int) : (real_of_int _91912) = (real_of_int _91912).
Proof. exact (eq_refl (real_of_int _91912)). Qed.
Lemma lem6882836 (_91912 : int) : (term578 _91912) = (term593 _91912).
Proof. exact (MK_COMB (@lem6882834) (@lem6882835 _91912)). Qed.
Lemma lem6882837 (_91912 : int) : (term577 _91912) = (term593 _91912).
Proof. exact (TRANS (@lem6882734 _91912) (@lem6882836 _91912)). Qed.
Lemma lem6882838 (_91912 : int) : (term593 _91912) = term214.
Proof. exact (@lem1982719 (real_of_int _91912)). Qed.
Lemma lem6882839 (_91912 : int) : (term577 _91912) = term214.
Proof. exact (TRANS (@lem6882837 _91912) (@lem6882838 _91912)). Qed.
Lemma lem6882840 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6882841 (_91912 : int) : (term594 _91912) = term256.
Proof. exact (MK_COMB (@lem6882840) (@lem6882839 _91912)). Qed.
Lemma lem6882842 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem6882843 (_91912 : int) : (term654 _91912) = term599.
Proof. exact (MK_COMB (@lem6882841 _91912) (@lem6882842)). Qed.
Lemma lem6882844 (_91912 : int) : (term653 _91912) = term599.
Proof. exact (TRANS (@lem6882733 _91912) (@lem6882843 _91912)). Qed.
Lemma lem6882845 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6882846 (_91912 : int) : (term653 _91912) = term279.
Proof. exact (TRANS (@lem6882844 _91912) (@lem6882845)). Qed.
Lemma lem6882847 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6882848 (_91912 : int) : (term655 _91912) = term601.
Proof. exact (MK_COMB (@lem6882847) (@lem6882846 _91912)). Qed.
Lemma lem6882849 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6882850 (_91912 : int) : (term652 _91912) = term602.
Proof. exact (MK_COMB (@lem6882848 _91912) (@lem6882849)). Qed.
Lemma lem6882851 (_91911 : int) (_91912 : int) (h1 : term702 _91911 _91912) : term602.
Proof. exact (EQ_MP (@lem6882850 _91912) (@lem6882732 _91911 _91912 h1)). Qed.
Lemma lem6882853 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6882854 : term602 = term603.
Proof. exact (@lem6882853 term214 term279). Qed.
Lemma lem6882856 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6882857 : term279 = term280.
Proof. exact (@lem6882856 term92). Qed.
Lemma lem6882859 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6882860 : term214 = term276.
Proof. exact (@lem6882859 (NUMERAL 0)). Qed.
Lemma lem6882861 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6882862 : term216 = term604.
Proof. exact (MK_COMB (@lem6882861) (@lem6882860)). Qed.
Lemma lem6882863 : term603 = term605.
Proof. exact (MK_COMB (@lem6882862) (@lem6882857)). Qed.
Lemma lem6882864 : term606.
Proof. exact (@lem1980026 term214 term224 term279 term224). Qed.
Lemma lem6882866 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882867 : term331 = term332.
Proof. exact (@lem6882866 (NUMERAL 0) term92). Qed.
Lemma lem6882868 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882869 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882870 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882869 h1) (fun h1 : term332 = True => @lem6882868)). Qed.
Lemma lem6882871 : term332 = True.
Proof. exact (EQ_MP (@lem6882870) (@lem6882868)). Qed.
Lemma lem6882872 : term331 = True.
Proof. exact (TRANS (@lem6882867) (@lem6882871)). Qed.
Lemma lem6882873 : True = term331.
Proof. exact (SYM (@lem6882872)). Qed.
Lemma lem6882874 : term331.
Proof. exact (EQ_MP (@lem6882873) (@lem0)). Qed.
Lemma lem6882875 : term607.
Proof. exact (@lem6882864 (@lem6882874)). Qed.
Lemma lem6882877 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882878 : term331 = term332.
Proof. exact (@lem6882877 (NUMERAL 0) term92). Qed.
Lemma lem6882879 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882880 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882881 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882880 h1) (fun h1 : term332 = True => @lem6882879)). Qed.
Lemma lem6882882 : term332 = True.
Proof. exact (EQ_MP (@lem6882881) (@lem6882879)). Qed.
Lemma lem6882883 : term331 = True.
Proof. exact (TRANS (@lem6882878) (@lem6882882)). Qed.
Lemma lem6882884 : True = term331.
Proof. exact (SYM (@lem6882883)). Qed.
Lemma lem6882885 : term331.
Proof. exact (EQ_MP (@lem6882884) (@lem0)). Qed.
Lemma lem6882886 : term605 = term608.
Proof. exact (@lem6882875 (@lem6882885)). Qed.
Lemma lem6882888 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6882889 : term305 = term310.
Proof. exact (@lem6882888 term92 term92). Qed.
Lemma lem6882890 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882891 : term291 = term92.
Proof. exact (EQ_MP (@lem6882890) (@lem940073)). Qed.
Lemma lem6882892 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882893 : term289 = term224.
Proof. exact (MK_COMB (@lem6882892) (@lem6882891)). Qed.
Lemma lem6882894 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6882895 : term310 = term279.
Proof. exact (MK_COMB (@lem6882894) (@lem6882893)). Qed.
Lemma lem6882896 : term305 = term279.
Proof. exact (TRANS (@lem6882889) (@lem6882895)). Qed.
Lemma lem6882898 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6882899 : term343 = term214.
Proof. exact (@lem6882898 term92). Qed.
Lemma lem6882900 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6882901 : term609 = term216.
Proof. exact (MK_COMB (@lem6882900) (@lem6882899)). Qed.
Lemma lem6882902 : term608 = term603.
Proof. exact (MK_COMB (@lem6882901) (@lem6882896)). Qed.
Lemma lem6882904 (m : nat) (n : nat) : (term610 m n) = (term611 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6882905 : term603 = term612.
Proof. exact (@lem6882904 (NUMERAL 0) term92). Qed.
Lemma lem6882906 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882907 (h1 : term333 = (BIT1 0)) : (term92 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6882908 : (term333 = (BIT1 0)) = ((term92 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882907 h1) (fun h1 : (term92 = (NUMERAL 0)) = False => @lem6882906)). Qed.
Lemma lem6882909 : (term92 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6882908) (@lem6882906)). Qed.
Lemma lem6882910 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6882911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6882912 : term613 = (and True).
Proof. exact (MK_COMB (@lem6882911) (@lem6882910)). Qed.
Lemma lem6882913 : term612 = (True /\ False).
Proof. exact (MK_COMB (@lem6882912) (@lem6882909)). Qed.
Lemma lem6882915 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6882916 : term612 = False.
Proof. exact (TRANS (@lem6882913) (@lem6882915)). Qed.
Lemma lem6882917 : term603 = False.
Proof. exact (TRANS (@lem6882905) (@lem6882916)). Qed.
Lemma lem6882918 : term608 = False.
Proof. exact (TRANS (@lem6882902) (@lem6882917)). Qed.
Lemma lem6882919 : term605 = False.
Proof. exact (TRANS (@lem6882886) (@lem6882918)). Qed.
Lemma lem6882920 : term603 = False.
Proof. exact (TRANS (@lem6882863) (@lem6882919)). Qed.
Lemma lem6882921 : term602 = False.
Proof. exact (TRANS (@lem6882854) (@lem6882920)). Qed.
Lemma lem6882922 (_91911 : int) (_91912 : int) (h1 : term702 _91911 _91912) : False.
Proof. exact (EQ_MP (@lem6882921) (@lem6882851 _91911 _91912 h1)). Qed.
Lemma lem6882923 (_91911 : int) (_91912 : int) (h1 : term705 _91911 _91912) : term705 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6882924 (_91911 : int) (_91912 : int) (h1 : term705 _91911 _91912) : term510 _91911 _91912.
Proof. exact (proj2 (@lem6882923 _91911 _91912 h1)). Qed.
Lemma lem6882926 (_91911 : int) (_91912 : int) (h1 : term705 _91911 _91912) : term461 _91911 _91912.
Proof. exact (proj2 (@lem6882924 _91911 _91912 h1)). Qed.
Lemma lem6882928 (_91911 : int) (_91912 : int) (h1 : term705 _91911 _91912) : term416 _91912.
Proof. exact (proj2 (@lem6882926 _91911 _91912 h1)). Qed.
Lemma lem6882932 (_91911 : int) (_91912 : int) (h1 : term705 _91911 _91912) : term382 _91912.
Proof. exact (proj2 (@lem6882928 _91911 _91912 h1)). Qed.
Lemma lem6882933 (_91911 : int) (_91912 : int) (h1 : term705 _91911 _91912) : (real_of_int _91912) = term214.
Proof. exact (proj1 (@lem6882928 _91911 _91912 h1)). Qed.
Lemma lem6882935 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem6882936 : term551 = term331.
Proof. exact (@lem6882935 term214 term224). Qed.
Lemma lem6882938 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6882939 : term224 = term304.
Proof. exact (@lem6882938 term92). Qed.
Lemma lem6882941 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6882942 : term214 = term276.
Proof. exact (@lem6882941 (NUMERAL 0)). Qed.
Lemma lem6882943 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6882944 : term552 = term553.
Proof. exact (MK_COMB (@lem6882943) (@lem6882942)). Qed.
Lemma lem6882945 : term331 = term554.
Proof. exact (MK_COMB (@lem6882944) (@lem6882939)). Qed.
Lemma lem6882946 : term555.
Proof. exact (@lem1980255 term214 term224 term224 term224). Qed.
Lemma lem6882948 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882949 : term331 = term332.
Proof. exact (@lem6882948 (NUMERAL 0) term92). Qed.
Lemma lem6882950 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882951 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882952 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882951 h1) (fun h1 : term332 = True => @lem6882950)). Qed.
Lemma lem6882953 : term332 = True.
Proof. exact (EQ_MP (@lem6882952) (@lem6882950)). Qed.
Lemma lem6882954 : term331 = True.
Proof. exact (TRANS (@lem6882949) (@lem6882953)). Qed.
Lemma lem6882955 : True = term331.
Proof. exact (SYM (@lem6882954)). Qed.
Lemma lem6882956 : term331.
Proof. exact (EQ_MP (@lem6882955) (@lem0)). Qed.
Lemma lem6882957 : term556.
Proof. exact (@lem6882946 (@lem6882956)). Qed.
Lemma lem6882959 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882960 : term331 = term332.
Proof. exact (@lem6882959 (NUMERAL 0) term92). Qed.
Lemma lem6882961 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882962 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882963 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882962 h1) (fun h1 : term332 = True => @lem6882961)). Qed.
Lemma lem6882964 : term332 = True.
Proof. exact (EQ_MP (@lem6882963) (@lem6882961)). Qed.
Lemma lem6882965 : term331 = True.
Proof. exact (TRANS (@lem6882960) (@lem6882964)). Qed.
Lemma lem6882966 : True = term331.
Proof. exact (SYM (@lem6882965)). Qed.
Lemma lem6882967 : term331.
Proof. exact (EQ_MP (@lem6882966) (@lem0)). Qed.
Lemma lem6882968 : term554 = term557.
Proof. exact (@lem6882957 (@lem6882967)). Qed.
Lemma lem6882970 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6882971 : term288 = term289.
Proof. exact (@lem6882970 term92 term92). Qed.
Lemma lem6882972 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6882973 : term291 = term92.
Proof. exact (EQ_MP (@lem6882972) (@lem940073)). Qed.
Lemma lem6882974 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6882975 : term289 = term224.
Proof. exact (MK_COMB (@lem6882974) (@lem6882973)). Qed.
Lemma lem6882976 : term288 = term224.
Proof. exact (TRANS (@lem6882971) (@lem6882975)). Qed.
Lemma lem6882978 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6882979 : term343 = term214.
Proof. exact (@lem6882978 term92). Qed.
Lemma lem6882980 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem6882981 : term558 = term552.
Proof. exact (MK_COMB (@lem6882980) (@lem6882979)). Qed.
Lemma lem6882982 : term557 = term331.
Proof. exact (MK_COMB (@lem6882981) (@lem6882976)). Qed.
Lemma lem6882984 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6882985 : term331 = term332.
Proof. exact (@lem6882984 (NUMERAL 0) term92). Qed.
Lemma lem6882986 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6882987 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6882988 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6882987 h1) (fun h1 : term332 = True => @lem6882986)). Qed.
Lemma lem6882989 : term332 = True.
Proof. exact (EQ_MP (@lem6882988) (@lem6882986)). Qed.
Lemma lem6882990 : term331 = True.
Proof. exact (TRANS (@lem6882985) (@lem6882989)). Qed.
Lemma lem6882991 : term557 = True.
Proof. exact (TRANS (@lem6882982) (@lem6882990)). Qed.
Lemma lem6882992 : term554 = True.
Proof. exact (TRANS (@lem6882968) (@lem6882991)). Qed.
Lemma lem6882993 : term331 = True.
Proof. exact (TRANS (@lem6882945) (@lem6882992)). Qed.
Lemma lem6882994 : term551 = True.
Proof. exact (TRANS (@lem6882936) (@lem6882993)). Qed.
Lemma lem6882995 : True = term551.
Proof. exact (SYM (@lem6882994)). Qed.
Lemma lem6882996 : term551.
Proof. exact (EQ_MP (@lem6882995) (@lem0)). Qed.
Lemma lem6882997 (_91911 : int) (_91912 : int) (h1 : term705 _91911 _91912) : term631 _91912.
Proof. exact (conj (@lem6882996) (@lem6882932 _91911 _91912 h1)). Qed.
Lemma lem6882999 (x : real) (y : real) : term560 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem6883000 (_91912 : int) : term632 _91912.
Proof. exact (@lem6882999 term224 (term379 _91912)). Qed.
Lemma lem6883001 (_91911 : int) (_91912 : int) (h1 : term705 _91911 _91912) : term633 _91912.
Proof. exact (@lem6883000 _91912 (@lem6882997 _91911 _91912 h1)). Qed.
Lemma lem6883002 (_91912 : int) : (term634 _91912) = (term379 _91912).
Proof. exact (@lem1982733 (term379 _91912)). Qed.
Lemma lem6883003 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6883004 (_91912 : int) : (term635 _91912) = (term381 _91912).
Proof. exact (MK_COMB (@lem6883003) (@lem6883002 _91912)). Qed.
Lemma lem6883005 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6883006 (_91912 : int) : (term633 _91912) = (term382 _91912).
Proof. exact (MK_COMB (@lem6883004 _91912) (@lem6883005)). Qed.
Lemma lem6883007 (_91911 : int) (_91912 : int) (h1 : term705 _91911 _91912) : term382 _91912.
Proof. exact (EQ_MP (@lem6883006 _91912) (@lem6883001 _91911 _91912 h1)). Qed.
Lemma lem6883009 (y : real) : term565 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem6883010 (_91912 : int) : term619 _91912.
Proof. exact (@lem6883009 (real_of_int _91912)). Qed.
Lemma lem6883011 (_91911 : int) (_91912 : int) (h1 : term705 _91911 _91912) : term620 _91912.
Proof. exact (@lem6883010 _91912 (@lem6882933 _91911 _91912 h1)). Qed.
Lemma lem6883012 (_91911 : int) (_91912 : int) (h1 : term705 _91911 _91912) : term636 _91912.
Proof. exact (@lem6883011 _91911 _91912 h1 term279). Qed.
Lemma lem6883013 (_91912 : int) : (term636 _91912) = ((term317 _91912) = term214).
Proof. exact (eq_refl (term636 _91912)). Qed.
Lemma lem6883020 (_91911 : int) (_91912 : int) (h1 : term705 _91911 _91912) : (term317 _91912) = term214.
Proof. exact (EQ_MP (@lem6883013 _91912) (@lem6883012 _91911 _91912 h1)). Qed.
Lemma lem6883021 (_91911 : int) (_91912 : int) (h1 : term705 _91911 _91912) : term703 _91912.
Proof. exact (conj (@lem6883020 _91911 _91912 h1) (@lem6883007 _91911 _91912 h1)). Qed.
Lemma lem6883023 (x : real) (y : real) : term572 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem6883024 (_91912 : int) : term704 _91912.
Proof. exact (@lem6883023 (term317 _91912) (term379 _91912)). Qed.
Lemma lem6883025 (_91911 : int) (_91912 : int) (h1 : term705 _91911 _91912) : term652 _91912.
Proof. exact (@lem6883024 _91912 (@lem6883021 _91911 _91912 h1)). Qed.
Lemma lem6883026 (_91912 : int) : (term653 _91912) = (term654 _91912).
Proof. exact (@lem1982763 (term317 _91912) (real_of_int _91912) term279). Qed.
Lemma lem6883027 (_91912 : int) : (term577 _91912) = (term578 _91912).
Proof. exact (@lem1982713 term279 (real_of_int _91912)). Qed.
Lemma lem6883029 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6883030 : term224 = term304.
Proof. exact (@lem6883029 term92). Qed.
Lemma lem6883032 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6883033 : term279 = term280.
Proof. exact (@lem6883032 term92). Qed.
Lemma lem6883034 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6883035 : term579 = term580.
Proof. exact (MK_COMB (@lem6883034) (@lem6883033)). Qed.
Lemma lem6883036 : term581 = term582.
Proof. exact (MK_COMB (@lem6883035) (@lem6883030)). Qed.
Lemma lem6883037 : term583.
Proof. exact (@lem1981473 term279 term224 term224 term224 term214 term224). Qed.
Lemma lem6883039 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6883040 : term331 = term332.
Proof. exact (@lem6883039 (NUMERAL 0) term92). Qed.
Lemma lem6883041 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6883042 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6883043 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6883042 h1) (fun h1 : term332 = True => @lem6883041)). Qed.
Lemma lem6883044 : term332 = True.
Proof. exact (EQ_MP (@lem6883043) (@lem6883041)). Qed.
Lemma lem6883045 : term331 = True.
Proof. exact (TRANS (@lem6883040) (@lem6883044)). Qed.
Lemma lem6883046 : True = term331.
Proof. exact (SYM (@lem6883045)). Qed.
Lemma lem6883047 : term331.
Proof. exact (EQ_MP (@lem6883046) (@lem0)). Qed.
Lemma lem6883048 : term584.
Proof. exact (@lem6883037 (@lem6883047)). Qed.
Lemma lem6883050 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6883051 : term331 = term332.
Proof. exact (@lem6883050 (NUMERAL 0) term92). Qed.
Lemma lem6883052 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6883053 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6883054 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6883053 h1) (fun h1 : term332 = True => @lem6883052)). Qed.
Lemma lem6883055 : term332 = True.
Proof. exact (EQ_MP (@lem6883054) (@lem6883052)). Qed.
Lemma lem6883056 : term331 = True.
Proof. exact (TRANS (@lem6883051) (@lem6883055)). Qed.
Lemma lem6883057 : True = term331.
Proof. exact (SYM (@lem6883056)). Qed.
Lemma lem6883058 : term331.
Proof. exact (EQ_MP (@lem6883057) (@lem0)). Qed.
Lemma lem6883059 : term585.
Proof. exact (@lem6883048 (@lem6883058)). Qed.
Lemma lem6883061 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6883062 : term331 = term332.
Proof. exact (@lem6883061 (NUMERAL 0) term92). Qed.
Lemma lem6883063 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6883064 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6883065 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6883064 h1) (fun h1 : term332 = True => @lem6883063)). Qed.
Lemma lem6883066 : term332 = True.
Proof. exact (EQ_MP (@lem6883065) (@lem6883063)). Qed.
Lemma lem6883067 : term331 = True.
Proof. exact (TRANS (@lem6883062) (@lem6883066)). Qed.
Lemma lem6883068 : True = term331.
Proof. exact (SYM (@lem6883067)). Qed.
Lemma lem6883069 : term331.
Proof. exact (EQ_MP (@lem6883068) (@lem0)). Qed.
Lemma lem6883070 : term586.
Proof. exact (@lem6883059 (@lem6883069)). Qed.
Lemma lem6883072 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6883073 : term288 = term289.
Proof. exact (@lem6883072 term92 term92). Qed.
Lemma lem6883074 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6883075 : term291 = term92.
Proof. exact (EQ_MP (@lem6883074) (@lem940073)). Qed.
Lemma lem6883076 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6883077 : term289 = term224.
Proof. exact (MK_COMB (@lem6883076) (@lem6883075)). Qed.
Lemma lem6883078 : term288 = term224.
Proof. exact (TRANS (@lem6883073) (@lem6883077)). Qed.
Lemma lem6883080 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6883081 : term305 = term310.
Proof. exact (@lem6883080 term92 term92). Qed.
Lemma lem6883082 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6883083 : term291 = term92.
Proof. exact (EQ_MP (@lem6883082) (@lem940073)). Qed.
Lemma lem6883084 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6883085 : term289 = term224.
Proof. exact (MK_COMB (@lem6883084) (@lem6883083)). Qed.
Lemma lem6883086 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6883087 : term310 = term279.
Proof. exact (MK_COMB (@lem6883086) (@lem6883085)). Qed.
Lemma lem6883088 : term305 = term279.
Proof. exact (TRANS (@lem6883081) (@lem6883087)). Qed.
Lemma lem6883089 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6883090 : term587 = term579.
Proof. exact (MK_COMB (@lem6883089) (@lem6883088)). Qed.
Lemma lem6883091 : term588 = term581.
Proof. exact (MK_COMB (@lem6883090) (@lem6883078)). Qed.
Lemma lem6883093 (m : nat) : (term589 m) = term214.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6883094 : term581 = term214.
Proof. exact (@lem6883093 term92). Qed.
Lemma lem6883095 : term588 = term214.
Proof. exact (TRANS (@lem6883091) (@lem6883094)). Qed.
Lemma lem6883096 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6883097 : term590 = term341.
Proof. exact (MK_COMB (@lem6883096) (@lem6883095)). Qed.
Lemma lem6883098 : term224 = term224.
Proof. exact (eq_refl term224). Qed.
Lemma lem6883099 : term591 = term343.
Proof. exact (MK_COMB (@lem6883097) (@lem6883098)). Qed.
Lemma lem6883101 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6883102 : term343 = term214.
Proof. exact (@lem6883101 term92). Qed.
Lemma lem6883103 : term591 = term214.
Proof. exact (TRANS (@lem6883099) (@lem6883102)). Qed.
Lemma lem6883105 (m : nat) (n : nat) : (term286 m n) = (term287 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6883106 : term288 = term289.
Proof. exact (@lem6883105 term92 term92). Qed.
Lemma lem6883107 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6883108 : term291 = term92.
Proof. exact (EQ_MP (@lem6883107) (@lem940073)). Qed.
Lemma lem6883109 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6883110 : term289 = term224.
Proof. exact (MK_COMB (@lem6883109) (@lem6883108)). Qed.
Lemma lem6883111 : term288 = term224.
Proof. exact (TRANS (@lem6883106) (@lem6883110)). Qed.
Lemma lem6883112 : term341 = term341.
Proof. exact (eq_refl term341). Qed.
Lemma lem6883113 : term345 = term343.
Proof. exact (MK_COMB (@lem6883112) (@lem6883111)). Qed.
Lemma lem6883115 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6883116 : term343 = term214.
Proof. exact (@lem6883115 term92). Qed.
Lemma lem6883117 : term345 = term214.
Proof. exact (TRANS (@lem6883113) (@lem6883116)). Qed.
Lemma lem6883118 : term214 = term345.
Proof. exact (SYM (@lem6883117)). Qed.
Lemma lem6883119 : term591 = term345.
Proof. exact (TRANS (@lem6883103) (@lem6883118)). Qed.
Lemma lem6883120 : term582 = term276.
Proof. exact (@lem6883070 (@lem6883119)). Qed.
Lemma lem6883121 : term581 = term276.
Proof. exact (TRANS (@lem6883036) (@lem6883120)). Qed.
Lemma lem6883123 (x : real) : (term295 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6883124 : term276 = term214.
Proof. exact (@lem6883123 term214). Qed.
Lemma lem6883125 : term581 = term214.
Proof. exact (TRANS (@lem6883121) (@lem6883124)). Qed.
Lemma lem6883126 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6883127 : term592 = term341.
Proof. exact (MK_COMB (@lem6883126) (@lem6883125)). Qed.
Lemma lem6883128 (_91912 : int) : (real_of_int _91912) = (real_of_int _91912).
Proof. exact (eq_refl (real_of_int _91912)). Qed.
Lemma lem6883129 (_91912 : int) : (term578 _91912) = (term593 _91912).
Proof. exact (MK_COMB (@lem6883127) (@lem6883128 _91912)). Qed.
Lemma lem6883130 (_91912 : int) : (term577 _91912) = (term593 _91912).
Proof. exact (TRANS (@lem6883027 _91912) (@lem6883129 _91912)). Qed.
Lemma lem6883131 (_91912 : int) : (term593 _91912) = term214.
Proof. exact (@lem1982719 (real_of_int _91912)). Qed.
Lemma lem6883132 (_91912 : int) : (term577 _91912) = term214.
Proof. exact (TRANS (@lem6883130 _91912) (@lem6883131 _91912)). Qed.
Lemma lem6883133 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6883134 (_91912 : int) : (term594 _91912) = term256.
Proof. exact (MK_COMB (@lem6883133) (@lem6883132 _91912)). Qed.
Lemma lem6883135 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem6883136 (_91912 : int) : (term654 _91912) = term599.
Proof. exact (MK_COMB (@lem6883134 _91912) (@lem6883135)). Qed.
Lemma lem6883137 (_91912 : int) : (term653 _91912) = term599.
Proof. exact (TRANS (@lem6883026 _91912) (@lem6883136 _91912)). Qed.
Lemma lem6883138 : term599 = term279.
Proof. exact (@lem1982721 term279). Qed.
Lemma lem6883139 (_91912 : int) : (term653 _91912) = term279.
Proof. exact (TRANS (@lem6883137 _91912) (@lem6883138)). Qed.
Lemma lem6883140 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6883141 (_91912 : int) : (term655 _91912) = term601.
Proof. exact (MK_COMB (@lem6883140) (@lem6883139 _91912)). Qed.
Lemma lem6883142 : term214 = term214.
Proof. exact (eq_refl term214). Qed.
Lemma lem6883143 (_91912 : int) : (term652 _91912) = term602.
Proof. exact (MK_COMB (@lem6883141 _91912) (@lem6883142)). Qed.
Lemma lem6883144 (_91911 : int) (_91912 : int) (h1 : term705 _91911 _91912) : term602.
Proof. exact (EQ_MP (@lem6883143 _91912) (@lem6883025 _91911 _91912 h1)). Qed.
Lemma lem6883146 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6883147 : term602 = term603.
Proof. exact (@lem6883146 term214 term279). Qed.
Lemma lem6883149 (x : nat) : (term277 x) = (term278 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6883150 : term279 = term280.
Proof. exact (@lem6883149 term92). Qed.
Lemma lem6883152 (x : nat) : (real_of_num x) = (term275 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6883153 : term214 = term276.
Proof. exact (@lem6883152 (NUMERAL 0)). Qed.
Lemma lem6883154 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6883155 : term216 = term604.
Proof. exact (MK_COMB (@lem6883154) (@lem6883153)). Qed.
Lemma lem6883156 : term603 = term605.
Proof. exact (MK_COMB (@lem6883155) (@lem6883150)). Qed.
Lemma lem6883157 : term606.
Proof. exact (@lem1980026 term214 term224 term279 term224). Qed.
Lemma lem6883159 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6883160 : term331 = term332.
Proof. exact (@lem6883159 (NUMERAL 0) term92). Qed.
Lemma lem6883161 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6883162 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6883163 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6883162 h1) (fun h1 : term332 = True => @lem6883161)). Qed.
Lemma lem6883164 : term332 = True.
Proof. exact (EQ_MP (@lem6883163) (@lem6883161)). Qed.
Lemma lem6883165 : term331 = True.
Proof. exact (TRANS (@lem6883160) (@lem6883164)). Qed.
Lemma lem6883166 : True = term331.
Proof. exact (SYM (@lem6883165)). Qed.
Lemma lem6883167 : term331.
Proof. exact (EQ_MP (@lem6883166) (@lem0)). Qed.
Lemma lem6883168 : term607.
Proof. exact (@lem6883157 (@lem6883167)). Qed.
Lemma lem6883170 (m : nat) (n : nat) : (term330 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6883171 : term331 = term332.
Proof. exact (@lem6883170 (NUMERAL 0) term92). Qed.
Lemma lem6883172 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6883173 (h1 : term333 = (BIT1 0)) : term332 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6883174 : (term333 = (BIT1 0)) = (term332 = True).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6883173 h1) (fun h1 : term332 = True => @lem6883172)). Qed.
Lemma lem6883175 : term332 = True.
Proof. exact (EQ_MP (@lem6883174) (@lem6883172)). Qed.
Lemma lem6883176 : term331 = True.
Proof. exact (TRANS (@lem6883171) (@lem6883175)). Qed.
Lemma lem6883177 : True = term331.
Proof. exact (SYM (@lem6883176)). Qed.
Lemma lem6883178 : term331.
Proof. exact (EQ_MP (@lem6883177) (@lem0)). Qed.
Lemma lem6883179 : term605 = term608.
Proof. exact (@lem6883168 (@lem6883178)). Qed.
Lemma lem6883181 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6883182 : term305 = term310.
Proof. exact (@lem6883181 term92 term92). Qed.
Lemma lem6883183 : (term290 = (BIT1 0)) = (term291 = term92).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6883184 : term291 = term92.
Proof. exact (EQ_MP (@lem6883183) (@lem940073)). Qed.
Lemma lem6883185 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6883186 : term289 = term224.
Proof. exact (MK_COMB (@lem6883185) (@lem6883184)). Qed.
Lemma lem6883187 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6883188 : term310 = term279.
Proof. exact (MK_COMB (@lem6883187) (@lem6883186)). Qed.
Lemma lem6883189 : term305 = term279.
Proof. exact (TRANS (@lem6883182) (@lem6883188)). Qed.
Lemma lem6883191 (x : nat) : (term344 x) = term214.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6883192 : term343 = term214.
Proof. exact (@lem6883191 term92). Qed.
Lemma lem6883193 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6883194 : term609 = term216.
Proof. exact (MK_COMB (@lem6883193) (@lem6883192)). Qed.
Lemma lem6883195 : term608 = term603.
Proof. exact (MK_COMB (@lem6883194) (@lem6883189)). Qed.
Lemma lem6883197 (m : nat) (n : nat) : (term610 m n) = (term611 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6883198 : term603 = term612.
Proof. exact (@lem6883197 (NUMERAL 0) term92). Qed.
Lemma lem6883199 : term333 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6883200 (h1 : term333 = (BIT1 0)) : (term92 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6883201 : (term333 = (BIT1 0)) = ((term92 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term333 = (BIT1 0) => @lem6883200 h1) (fun h1 : (term92 = (NUMERAL 0)) = False => @lem6883199)). Qed.
Lemma lem6883202 : (term92 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6883201) (@lem6883199)). Qed.
Lemma lem6883203 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6883204 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6883205 : term613 = (and True).
Proof. exact (MK_COMB (@lem6883204) (@lem6883203)). Qed.
Lemma lem6883206 : term612 = (True /\ False).
Proof. exact (MK_COMB (@lem6883205) (@lem6883202)). Qed.
Lemma lem6883208 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6883209 : term612 = False.
Proof. exact (TRANS (@lem6883206) (@lem6883208)). Qed.
Lemma lem6883210 : term603 = False.
Proof. exact (TRANS (@lem6883198) (@lem6883209)). Qed.
Lemma lem6883211 : term608 = False.
Proof. exact (TRANS (@lem6883195) (@lem6883210)). Qed.
Lemma lem6883212 : term605 = False.
Proof. exact (TRANS (@lem6883179) (@lem6883211)). Qed.
Lemma lem6883213 : term603 = False.
Proof. exact (TRANS (@lem6883156) (@lem6883212)). Qed.
Lemma lem6883214 : term602 = False.
Proof. exact (TRANS (@lem6883147) (@lem6883213)). Qed.
Lemma lem6883215 (_91911 : int) (_91912 : int) (h1 : term705 _91911 _91912) : False.
Proof. exact (EQ_MP (@lem6883214) (@lem6883144 _91911 _91912 h1)). Qed.
Lemma lem6883216 (_91911 : int) (_91912 : int) (h1 : term508 _91911 _91912) : False.
Proof. exact (or_elim (@lem6882631 _91911 _91912 h1) (fun h0 : term702 _91911 _91912 => @lem6882922 _91911 _91912 h0) (fun h0 : term705 _91911 _91912 => @lem6883215 _91911 _91912 h0)). Qed.
Lemma lem6883217 (_91911 : int) (_91912 : int) (h1 : term517 _91911 _91912) : False.
Proof. exact (or_elim (@lem6881659 _91911 _91912 h1) (fun h0 : term512 _91911 _91912 => @lem6882630 _91911 _91912 h0) (fun h0 : term508 _91911 _91912 => @lem6883216 _91911 _91912 h0)). Qed.
Lemma lem6883218 (_91911 : int) (_91912 : int) (h1 : term533 _91911 _91912) : False.
Proof. exact (or_elim (@lem6880310 _91911 _91912 h1) (fun h0 : term530 _91911 _91912 => @lem6881658 _91911 _91912 h0) (fun h0 : term517 _91911 _91912 => @lem6883217 _91911 _91912 h0)). Qed.
Lemma lem6883219 (_91911 : int) (_91912 : int) (h1 : term549 _91911 _91912) : False.
Proof. exact (or_elim (@lem6878109 _91911 _91912 h1) (fun h0 : term546 _91911 _91912 => @lem6880309 _91911 _91912 h0) (fun h0 : term533 _91911 _91912 => @lem6883218 _91911 _91912 h0)). Qed.
Lemma lem6883221 (_91911 : int) (_91912 : int) (h1 : term549 _91911 _91912) : term549 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6883222 (_91911 : int) (_91912 : int) (h1 : term549 _91911 _91912) : (term549 _91911 _91912) = False.
Proof. exact (prop_ext (fun h2 : term549 _91911 _91912 => @lem6883219 _91911 _91912 h1) (fun h2 : False => @lem6883221 _91911 _91912 h1)). Qed.
Lemma lem6883223 (_91911 : int) (_91912 : int) (h1 : term549 _91911 _91912) : False.
Proof. exact (EQ_MP (@lem6883222 _91911 _91912 h1) (@lem6883221 _91911 _91912 h1)). Qed.
Lemma lem6883224 (_91911 : int) (_91912 : int) (h1 : term271 _91911 _91912) : term271 _91911 _91912.
Proof. exact (h1). Qed.
Lemma lem6883225 (_91911 : int) (_91912 : int) (h1 : term271 _91911 _91912) : term549 _91911 _91912.
Proof. exact (EQ_MP (@lem6878039 _91911 _91912) (@lem6883224 _91911 _91912 h1)). Qed.
Lemma lem6883226 (_91911 : int) (_91912 : int) (h1 : term271 _91911 _91912) : (term549 _91911 _91912) = False.
Proof. exact (prop_ext (fun h2 : term549 _91911 _91912 => @lem6883223 _91911 _91912 h2) (fun h2 : False => @lem6883225 _91911 _91912 h1)). Qed.
Lemma lem6883227 (_91911 : int) (_91912 : int) (h1 : term271 _91911 _91912) : False.
Proof. exact (EQ_MP (@lem6883226 _91911 _91912 h1) (@lem6883225 _91911 _91912 h1)). Qed.
Lemma lem6883228 (_91911 : int) (_91912 : int) : term706 _91911 _91912.
Proof. exact (fun h0 : term271 _91911 _91912 => @lem6883227 _91911 _91912 h0). Qed.
Lemma lem6883229 (_91911 : int) (_91912 : int) : term707 _91911 _91912.
Proof. exact (@lem1386578 (term708 _91911 _91912)). Qed.
Lemma lem6883232 (_91911 : int) (_91912 : int) : term708 _91911 _91912.
Proof. exact (@lem6883229 _91911 _91912 (@lem6883228 _91911 _91912)). Qed.
Lemma lem6883233 (_91911 : int) (_91912 : int) : (term270 _91911 _91912) = (term208 _91911 _91912).
Proof. exact (SYM (@lem6876978 _91911 _91912)). Qed.
Lemma lem6883234 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6883235 (_91911 : int) (_91912 : int) : (term708 _91911 _91912) = (term154 _91911 _91912).
Proof. exact (MK_COMB (@lem6883234) (@lem6883233 _91911 _91912)). Qed.
Lemma lem6883236 (_91911 : int) (_91912 : int) : term154 _91911 _91912.
Proof. exact (EQ_MP (@lem6883235 _91911 _91912) (@lem6883232 _91911 _91912)). Qed.
Lemma lem6883237 (_91911 : int) (_91912 : int) : term155 _91911 _91912.
Proof. exact (EQ_MP (@lem6876665 _91911 _91912) (@lem6883236 _91911 _91912)). Qed.
Lemma lem6883238 (d : nat) (n : nat) : term709 d n.
Proof. exact (@lem6883237 (int_of_num d) (int_of_num n)). Qed.
Lemma lem6883239 (d : nat) (n : nat) : term710 d n.
Proof. exact (@lem6883238 d n (@lem6876661 d)). Qed.
Lemma lem6883240 (d : nat) (n : nat) : term149 d n.
Proof. exact (@lem6883239 d n (@lem6876664 n)). Qed.
Lemma lem6883241 (n : nat) : term151 n.
Proof. exact (fun d : nat => @lem6883240 d n). Qed.
Lemma lem6883242 (n : nat) : (term151 n) = ((term88 n) = (term89 n)).
Proof. exact (SYM (@lem6876658 n)). Qed.
Lemma lem6883244 {A : Type'} (x : A) : term711 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem6883245 {A : Type'} (x : A) : (term711 A x) = (term712 A x).
Proof. exact (eq_refl (term711 A x)). Qed.
Lemma lem6883246 {A : Type'} (x : A) : term712 A x.
Proof. exact (EQ_MP (@lem6883245 A x) (@lem6883244 A x)). Qed.
Lemma lem6883247 {A : Type'} (x : A) (y : A) : term713 A x y.
Proof. exact (@lem6883246 A x y). Qed.
Lemma lem6883248 {A : Type'} (x : A) (y : A) : (term713 A x y) = ((term714 A x y) = (x = y)).
Proof. exact (eq_refl (term713 A x y)). Qed.
Lemma lem6883250 {A : Type'} (s : A -> Prop) : term715 A s.
Proof. exact (@lem3205495 A s). Qed.
Lemma lem6883251 {A : Type'} (s : A -> Prop) : (term715 A s) = (term716 A s).
Proof. exact (eq_refl (term715 A s)). Qed.
Lemma lem6883252 {A : Type'} (s : A -> Prop) : term716 A s.
Proof. exact (EQ_MP (@lem6883251 A s) (@lem6883250 A s)). Qed.
Lemma lem6883253 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term717 A s t.
Proof. exact (@lem6883252 A s t). Qed.
Lemma lem6883254 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term717 A s t) = (term718 A s t).
Proof. exact (eq_refl (term717 A s t)). Qed.
Lemma lem6883255 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term718 A s t.
Proof. exact (EQ_MP (@lem6883254 A s t) (@lem6883253 A s t)). Qed.
Lemma lem6883256 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term719 A s t x.
Proof. exact (@lem6883255 A s t x). Qed.
Lemma lem6883257 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term719 A s t x) = ((term720 A x s t) = (term721 A s x t)).
Proof. exact (eq_refl (term719 A s t x)). Qed.
Lemma lem6883259 {A : Type'} (x : A) : term711 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem6883260 {A : Type'} (x : A) : (term711 A x) = (term712 A x).
Proof. exact (eq_refl (term711 A x)). Qed.
Lemma lem6883261 {A : Type'} (x : A) : term712 A x.
Proof. exact (EQ_MP (@lem6883260 A x) (@lem6883259 A x)). Qed.
Lemma lem6883262 {A : Type'} (x : A) (y : A) : term713 A x y.
Proof. exact (@lem6883261 A x y). Qed.
Lemma lem6883263 {A : Type'} (x : A) (y : A) : (term713 A x y) = ((term714 A x y) = (x = y)).
Proof. exact (eq_refl (term713 A x y)). Qed.
Lemma lem6883265 {A : Type'} (s : A -> Prop) : term715 A s.
Proof. exact (@lem3205495 A s). Qed.
Lemma lem6883266 {A : Type'} (s : A -> Prop) : (term715 A s) = (term716 A s).
Proof. exact (eq_refl (term715 A s)). Qed.
Lemma lem6883267 {A : Type'} (s : A -> Prop) : term716 A s.
Proof. exact (EQ_MP (@lem6883266 A s) (@lem6883265 A s)). Qed.
Lemma lem6883268 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term717 A s t.
Proof. exact (@lem6883267 A s t). Qed.
Lemma lem6883269 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term717 A s t) = (term718 A s t).
Proof. exact (eq_refl (term717 A s t)). Qed.
Lemma lem6883270 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term718 A s t.
Proof. exact (EQ_MP (@lem6883269 A s t) (@lem6883268 A s t)). Qed.
Lemma lem6883271 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term719 A s t x.
Proof. exact (@lem6883270 A s t x). Qed.
Lemma lem6883272 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term719 A s t x) = ((term720 A x s t) = (term721 A s x t)).
Proof. exact (eq_refl (term719 A s t x)). Qed.
Lemma lem6883274 {A : Type'} (x : A) : term722 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem6883275 {A : Type'} (x : A) : (term722 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term722 A x)). Qed.
Lemma lem6883276 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem6883275 A x) (@lem6883274 A x)). Qed.
Lemma lem6883277 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem6883279 {A B : Type'} (s : A -> Prop) : term723 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem6883280 {A B : Type'} (s : A -> Prop) : (term723 A B s) = (term724 A B s).
Proof. exact (eq_refl (term723 A B s)). Qed.
Lemma lem6883281 {A B : Type'} (s : A -> Prop) : term724 A B s.
Proof. exact (EQ_MP (@lem6883280 A B s) (@lem6883279 A B s)). Qed.
Lemma lem6883282 {A B : Type'} (s : A -> Prop) (f : A -> B) : term725 A B s f.
Proof. exact (@lem6883281 A B s f). Qed.
Lemma lem6883283 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term725 A B s f) = (term726 A B s f).
Proof. exact (eq_refl (term725 A B s f)). Qed.
Lemma lem6883284 {A B : Type'} (s : A -> Prop) (f : A -> B) : term726 A B s f.
Proof. exact (EQ_MP (@lem6883283 A B s f) (@lem6883282 A B s f)). Qed.
Lemma lem6883285 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term727 A B s f op.
Proof. exact (@lem6883284 A B s f op). Qed.
Lemma lem6883286 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term727 A B s f op) = ((@support A B op f s) = (term728 A B s f op)).
Proof. exact (eq_refl (term727 A B s f op)). Qed.
Lemma lem6883291 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (term729 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) : (term729 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f).
Proof. exact (h1). Qed.
Lemma lem6883292 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (term729 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) : (@iterate _120296 _120308 op s f) = (term729 _120296 _120308 op s f).
Proof. exact (SYM (@lem6883291 _120296 _120308 op s f h1)). Qed.
Lemma lem6883293 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (@iterate _120296 _120308 op s f) = (term729 _120296 _120308 op s f)) : (@iterate _120296 _120308 op s f) = (term729 _120296 _120308 op s f).
Proof. exact (h1). Qed.
Lemma lem6883294 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) (h1 : (@iterate _120296 _120308 op s f) = (term729 _120296 _120308 op s f)) : (term729 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f).
Proof. exact (SYM (@lem6883293 _120296 _120308 op s f h1)). Qed.
Lemma lem6883295 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : ((term729 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f)) = ((@iterate _120296 _120308 op s f) = (term729 _120296 _120308 op s f)).
Proof. exact (prop_ext (fun h1 : (term729 _120296 _120308 op s f) = (@iterate _120296 _120308 op s f) => @lem6883292 _120296 _120308 op s f h1) (fun h1 : (@iterate _120296 _120308 op s f) = (term729 _120296 _120308 op s f) => @lem6883294 _120296 _120308 op s f h1)). Qed.
Lemma lem6883296 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term730 _120296 _120308 op f) = (term731 _120296 _120308 op f).
Proof. exact (fun_ext (fun s : _120308 -> Prop => @lem6883295 _120296 _120308 op s f)). Qed.
Lemma lem6883297 {_120308 : Type'} : (@all (_120308 -> Prop)) = (@all (_120308 -> Prop)).
Proof. exact (eq_refl (@all (_120308 -> Prop))). Qed.
Lemma lem6883298 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term732 _120296 _120308 op f) = (term733 _120296 _120308 op f).
Proof. exact (MK_COMB (@lem6883297 _120308) (@lem6883296 _120296 _120308 op f)). Qed.
Lemma lem6883299 {_120296 _120308 : Type'} (op : type1400 _120296) : (term734 _120296 _120308 op) = (term735 _120296 _120308 op).
Proof. exact (fun_ext (fun f : _120308 -> _120296 => @lem6883298 _120296 _120308 op f)). Qed.
Lemma lem6883300 {_120296 _120308 : Type'} : (@all (_120308 -> _120296)) = (@all (_120308 -> _120296)).
Proof. exact (eq_refl (@all (_120308 -> _120296))). Qed.
Lemma lem6883301 {_120296 _120308 : Type'} (op : type1400 _120296) : (term736 _120296 _120308 op) = (term737 _120296 _120308 op).
Proof. exact (MK_COMB (@lem6883300 _120296 _120308) (@lem6883299 _120296 _120308 op)). Qed.
Lemma lem6883302 {_120296 _120308 : Type'} : (term738 _120296 _120308) = (term739 _120296 _120308).
Proof. exact (fun_ext (fun op : type1400 _120296 => @lem6883301 _120296 _120308 op)). Qed.
Lemma lem6883303 {_120296 : Type'} : (@all (_120296 -> _120296 -> _120296)) = (@all (_120296 -> _120296 -> _120296)).
Proof. exact (eq_refl (@all (_120296 -> _120296 -> _120296))). Qed.
Lemma lem6883304 {_120296 _120308 : Type'} : (term740 _120296 _120308) = (term741 _120296 _120308).
Proof. exact (MK_COMB (@lem6883303 _120296) (@lem6883302 _120296 _120308)). Qed.
Lemma lem6883305 {_120296 _120308 : Type'} : term741 _120296 _120308.
Proof. exact (EQ_MP (@lem6883304 _120296 _120308) (@lem5737860 _120296 _120308)). Qed.
Lemma lem6883312 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (h1 : (term742 A K op ltle k dom neut f) = (@iterato A K dom neut op ltle k f)) : (term742 A K op ltle k dom neut f) = (@iterato A K dom neut op ltle k f).
Proof. exact (h1). Qed.
Lemma lem6883313 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (h1 : (term742 A K op ltle k dom neut f) = (@iterato A K dom neut op ltle k f)) : (@iterato A K dom neut op ltle k f) = (term742 A K op ltle k dom neut f).
Proof. exact (SYM (@lem6883312 A K dom neut op ltle k f h1)). Qed.
Lemma lem6883314 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) (h1 : (@iterato A K dom neut op ltle k f) = (term742 A K op ltle k dom neut f)) : (@iterato A K dom neut op ltle k f) = (term742 A K op ltle k dom neut f).
Proof. exact (h1). Qed.
Lemma lem6883315 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) (h1 : (@iterato A K dom neut op ltle k f) = (term742 A K op ltle k dom neut f)) : (term742 A K op ltle k dom neut f) = (@iterato A K dom neut op ltle k f).
Proof. exact (SYM (@lem6883314 A K op ltle k dom neut f h1)). Qed.
Lemma lem6883316 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : ((term742 A K op ltle k dom neut f) = (@iterato A K dom neut op ltle k f)) = ((@iterato A K dom neut op ltle k f) = (term742 A K op ltle k dom neut f)).
Proof. exact (prop_ext (fun h1 : (term742 A K op ltle k dom neut f) = (@iterato A K dom neut op ltle k f) => @lem6883313 A K dom neut op ltle k f h1) (fun h1 : (@iterato A K dom neut op ltle k f) = (term742 A K op ltle k dom neut f) => @lem6883315 A K op ltle k dom neut f h1)). Qed.
Lemma lem6883317 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : (term743 A K dom neut op ltle k) = (term744 A K op ltle k dom neut).
Proof. exact (fun_ext (fun f : K -> A => @lem6883316 A K op ltle k dom neut f)). Qed.
Lemma lem6883318 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6883319 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : (term745 A K dom neut op ltle k) = (term746 A K op ltle k dom neut).
Proof. exact (MK_COMB (@lem6883318 A K) (@lem6883317 A K op ltle k dom neut)). Qed.
Lemma lem6883320 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : (term747 A K dom neut op ltle) = (term748 A K op ltle dom neut).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6883319 A K op ltle k dom neut)). Qed.
Lemma lem6883321 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6883322 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : (term749 A K dom neut op ltle) = (term750 A K op ltle dom neut).
Proof. exact (MK_COMB (@lem6883321 K) (@lem6883320 A K op ltle dom neut)). Qed.
Lemma lem6883323 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : (term751 A K dom neut op) = (term752 A K op dom neut).
Proof. exact (fun_ext (fun ltle : type1402 K => @lem6883322 A K op ltle dom neut)). Qed.
Lemma lem6883324 {K : Type'} : (@all (K -> K -> Prop)) = (@all (K -> K -> Prop)).
Proof. exact (eq_refl (@all (K -> K -> Prop))). Qed.
Lemma lem6883325 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : (term753 A K dom neut op) = (term754 A K op dom neut).
Proof. exact (MK_COMB (@lem6883324 K) (@lem6883323 A K op dom neut)). Qed.
Lemma lem6883326 {A K : Type'} (dom : A -> Prop) (neut : A) : (term755 A K dom neut) = (term756 A K dom neut).
Proof. exact (fun_ext (fun op : type1400 A => @lem6883325 A K op dom neut)). Qed.
Lemma lem6883327 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem6883328 {A K : Type'} (dom : A -> Prop) (neut : A) : (term757 A K dom neut) = (term758 A K dom neut).
Proof. exact (MK_COMB (@lem6883327 A) (@lem6883326 A K dom neut)). Qed.
Lemma lem6883329 {A K : Type'} (dom : A -> Prop) : (term759 A K dom) = (term760 A K dom).
Proof. exact (fun_ext (fun neut : A => @lem6883328 A K dom neut)). Qed.
Lemma lem6883330 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6883331 {A K : Type'} (dom : A -> Prop) : (term761 A K dom) = (term762 A K dom).
Proof. exact (MK_COMB (@lem6883330 A) (@lem6883329 A K dom)). Qed.
Lemma lem6883332 {A K : Type'} : (term763 A K) = (term764 A K).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6883331 A K dom)). Qed.
Lemma lem6883333 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6883334 {A K : Type'} : (term765 A K) = (term766 A K).
Proof. exact (MK_COMB (@lem6883333 A) (@lem6883332 A K)). Qed.
Lemma lem6883335 {A K : Type'} : term766 A K.
Proof. exact (EQ_MP (@lem6883334 A K) (@lem6449238 A K)). Qed.
Lemma lem6883336 {_120296 _120308 : Type'} (op : type1400 _120296) : term767 _120296 _120308 op.
Proof. exact (@lem6883305 _120296 _120308 op). Qed.
Lemma lem6883337 {_120296 _120308 : Type'} (op : type1400 _120296) : (term767 _120296 _120308 op) = (term737 _120296 _120308 op).
Proof. exact (eq_refl (term767 _120296 _120308 op)). Qed.
Lemma lem6883338 {_120296 _120308 : Type'} (op : type1400 _120296) : term737 _120296 _120308 op.
Proof. exact (EQ_MP (@lem6883337 _120296 _120308 op) (@lem6883336 _120296 _120308 op)). Qed.
Lemma lem6883339 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : term768 _120296 _120308 op f.
Proof. exact (@lem6883338 _120296 _120308 op f). Qed.
Lemma lem6883340 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : (term768 _120296 _120308 op f) = (term733 _120296 _120308 op f).
Proof. exact (eq_refl (term768 _120296 _120308 op f)). Qed.
Lemma lem6883341 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) : term733 _120296 _120308 op f.
Proof. exact (EQ_MP (@lem6883340 _120296 _120308 op f) (@lem6883339 _120296 _120308 op f)). Qed.
Lemma lem6883342 {_120296 _120308 : Type'} (op : type1400 _120296) (f : _120308 -> _120296) (s : _120308 -> Prop) : term769 _120296 _120308 op f s.
Proof. exact (@lem6883341 _120296 _120308 op f s). Qed.
Lemma lem6883343 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (term769 _120296 _120308 op f s) = ((@iterate _120296 _120308 op s f) = (term729 _120296 _120308 op s f)).
Proof. exact (eq_refl (term769 _120296 _120308 op f s)). Qed.
Lemma lem6883345 {A K : Type'} (dom : A -> Prop) : term770 A K dom.
Proof. exact (@lem6883335 A K dom). Qed.
Lemma lem6883346 {A K : Type'} (dom : A -> Prop) : (term770 A K dom) = (term762 A K dom).
Proof. exact (eq_refl (term770 A K dom)). Qed.
Lemma lem6883347 {A K : Type'} (dom : A -> Prop) : term762 A K dom.
Proof. exact (EQ_MP (@lem6883346 A K dom) (@lem6883345 A K dom)). Qed.
Lemma lem6883348 {A K : Type'} (dom : A -> Prop) (neut : A) : term771 A K dom neut.
Proof. exact (@lem6883347 A K dom neut). Qed.
Lemma lem6883349 {A K : Type'} (dom : A -> Prop) (neut : A) : (term771 A K dom neut) = (term758 A K dom neut).
Proof. exact (eq_refl (term771 A K dom neut)). Qed.
Lemma lem6883350 {A K : Type'} (dom : A -> Prop) (neut : A) : term758 A K dom neut.
Proof. exact (EQ_MP (@lem6883349 A K dom neut) (@lem6883348 A K dom neut)). Qed.
Lemma lem6883351 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term772 A K dom neut op.
Proof. exact (@lem6883350 A K dom neut op). Qed.
Lemma lem6883352 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : (term772 A K dom neut op) = (term754 A K op dom neut).
Proof. exact (eq_refl (term772 A K dom neut op)). Qed.
Lemma lem6883353 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : term754 A K op dom neut.
Proof. exact (EQ_MP (@lem6883352 A K op dom neut) (@lem6883351 A K dom neut op)). Qed.
Lemma lem6883354 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) (ltle : type1402 K) : term773 A K op dom neut ltle.
Proof. exact (@lem6883353 A K op dom neut ltle). Qed.
Lemma lem6883355 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : (term773 A K op dom neut ltle) = (term750 A K op ltle dom neut).
Proof. exact (eq_refl (term773 A K op dom neut ltle)). Qed.
Lemma lem6883356 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : term750 A K op ltle dom neut.
Proof. exact (EQ_MP (@lem6883355 A K op ltle dom neut) (@lem6883354 A K op dom neut ltle)). Qed.
Lemma lem6883357 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) (k : K -> Prop) : term774 A K op ltle dom neut k.
Proof. exact (@lem6883356 A K op ltle dom neut k). Qed.
Lemma lem6883358 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : (term774 A K op ltle dom neut k) = (term746 A K op ltle k dom neut).
Proof. exact (eq_refl (term774 A K op ltle dom neut k)). Qed.
Lemma lem6883359 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : term746 A K op ltle k dom neut.
Proof. exact (EQ_MP (@lem6883358 A K op ltle k dom neut) (@lem6883357 A K op ltle dom neut k)). Qed.
Lemma lem6883360 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : term775 A K op ltle k dom neut f.
Proof. exact (@lem6883359 A K op ltle k dom neut f). Qed.
Lemma lem6883361 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (term775 A K op ltle k dom neut f) = ((@iterato A K dom neut op ltle k f) = (term742 A K op ltle k dom neut f)).
Proof. exact (eq_refl (term775 A K op ltle k dom neut f)). Qed.
Lemma lem6883377 (p : Prop) : term776 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem6883378 (p : Prop) : (term776 p) = (term777 p).
Proof. exact (eq_refl (term776 p)). Qed.
Lemma lem6883379 (p : Prop) : term777 p.
Proof. exact (EQ_MP (@lem6883378 p) (@lem6883377 p)). Qed.
Lemma lem6883380 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem6883381 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem6883396 (q : Prop) (r : Prop) : (term778 q r) = (term778 q r).
Proof. exact (eq_refl (term778 q r)). Qed.
Lemma lem6883397 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : (term779 q r p) = (term780 q r).
Proof. exact (MK_COMB (@lem6883396 q r) (@lem6883380 p h1)). Qed.
Lemma lem6883398 (q : Prop) (r : Prop) : (term780 q r) = (term781 q r).
Proof. exact (eq_refl (term780 q r)). Qed.
Lemma lem6883399 (q : Prop) (r : Prop) (p : Prop) : (term782 q r p) = (term782 q r p).
Proof. exact (eq_refl (term782 q r p)). Qed.
Lemma lem6883400 (p : Prop) (q : Prop) (r : Prop) : ((term779 q r p) = (term780 q r)) = ((term779 q r p) = (term781 q r)).
Proof. exact (MK_COMB (@lem6883399 q r p) (@lem6883398 q r)). Qed.
Lemma lem6883401 (p : Prop) (q : Prop) (r : Prop) : (term779 q r p) = (term783 p q r).
Proof. exact (eq_refl (term779 q r p)). Qed.
Lemma lem6883402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6883403 (p : Prop) (q : Prop) (r : Prop) : (term782 q r p) = (term784 p q r).
Proof. exact (MK_COMB (@lem6883402) (@lem6883401 p q r)). Qed.
Lemma lem6883404 (q : Prop) (r : Prop) : (term781 q r) = (term781 q r).
Proof. exact (eq_refl (term781 q r)). Qed.
Lemma lem6883405 (p : Prop) (q : Prop) (r : Prop) : ((term779 q r p) = (term781 q r)) = ((term783 p q r) = (term781 q r)).
Proof. exact (MK_COMB (@lem6883403 p q r) (@lem6883404 q r)). Qed.
Lemma lem6883406 (p : Prop) (q : Prop) (r : Prop) : ((term779 q r p) = (term780 q r)) = ((term783 p q r) = (term781 q r)).
Proof. exact (TRANS (@lem6883400 p q r) (@lem6883405 p q r)). Qed.
Lemma lem6883407 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : (term783 p q r) = (term781 q r).
Proof. exact (EQ_MP (@lem6883406 p q r) (@lem6883397 q r p h1)). Qed.
Lemma lem6883408 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : (term781 q r) = (term783 p q r).
Proof. exact (SYM (@lem6883407 q r p h1)). Qed.
Lemma lem6883409 (q : Prop) (r : Prop) : (term778 q r) = (term778 q r).
Proof. exact (eq_refl (term778 q r)). Qed.
Lemma lem6883410 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : (term779 q r p) = (term785 q r).
Proof. exact (MK_COMB (@lem6883409 q r) (@lem6883381 p h1)). Qed.
Lemma lem6883411 (q : Prop) (r : Prop) : (term785 q r) = (term786 q r).
Proof. exact (eq_refl (term785 q r)). Qed.
Lemma lem6883412 (q : Prop) (r : Prop) (p : Prop) : (term782 q r p) = (term782 q r p).
Proof. exact (eq_refl (term782 q r p)). Qed.
Lemma lem6883413 (p : Prop) (q : Prop) (r : Prop) : ((term779 q r p) = (term785 q r)) = ((term779 q r p) = (term786 q r)).
Proof. exact (MK_COMB (@lem6883412 q r p) (@lem6883411 q r)). Qed.
Lemma lem6883414 (p : Prop) (q : Prop) (r : Prop) : (term779 q r p) = (term783 p q r).
Proof. exact (eq_refl (term779 q r p)). Qed.
Lemma lem6883415 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6883416 (p : Prop) (q : Prop) (r : Prop) : (term782 q r p) = (term784 p q r).
Proof. exact (MK_COMB (@lem6883415) (@lem6883414 p q r)). Qed.
Lemma lem6883417 (q : Prop) (r : Prop) : (term786 q r) = (term786 q r).
Proof. exact (eq_refl (term786 q r)). Qed.
Lemma lem6883418 (p : Prop) (q : Prop) (r : Prop) : ((term779 q r p) = (term786 q r)) = ((term783 p q r) = (term786 q r)).
Proof. exact (MK_COMB (@lem6883416 p q r) (@lem6883417 q r)). Qed.
Lemma lem6883419 (p : Prop) (q : Prop) (r : Prop) : ((term779 q r p) = (term785 q r)) = ((term783 p q r) = (term786 q r)).
Proof. exact (TRANS (@lem6883413 p q r) (@lem6883418 p q r)). Qed.
Lemma lem6883420 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : (term783 p q r) = (term786 q r).
Proof. exact (EQ_MP (@lem6883419 p q r) (@lem6883410 q r p h1)). Qed.
Lemma lem6883421 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : (term786 q r) = (term783 p q r).
Proof. exact (SYM (@lem6883420 q r p h1)). Qed.
Lemma lem6883427 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem6883428 (r : Prop) : (True -> r) = r.
Proof. exact (@lem6883427 r). Qed.
Lemma lem6883429 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6883430 (r : Prop) : (term787 r) = (and r).
Proof. exact (MK_COMB (@lem6883429) (@lem6883428 r)). Qed.
Lemma lem6883433 (q : Prop) (r : Prop) : (q -> r) = (q -> r).
Proof. exact (eq_refl (q -> r)). Qed.
Lemma lem6883434 (q : Prop) (r : Prop) : (term788 q r) = (term789 q r).
Proof. exact (MK_COMB (@lem6883430 r) (@lem6883433 q r)). Qed.
Lemma lem6883437 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6883438 (q : Prop) (r : Prop) : (term790 q r) = (term791 q r).
Proof. exact (MK_COMB (@lem6883437) (@lem6883434 q r)). Qed.
Lemma lem6883444 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem6883445 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6883446 : term792 = (imp False).
Proof. exact (MK_COMB (@lem6883445) (@lem6883444)). Qed.
Lemma lem6883447 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem6883448 (q : Prop) : (term793 q) = (False -> q).
Proof. exact (MK_COMB (@lem6883446) (@lem6883447 q)). Qed.
Lemma lem6883450 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem6883451 (q : Prop) : (False -> q) = True.
Proof. exact (@lem6883450 q). Qed.
Lemma lem6883452 (q : Prop) : (term793 q) = True.
Proof. exact (TRANS (@lem6883448 q) (@lem6883451 q)). Qed.
Lemma lem6883453 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6883454 (q : Prop) : (term794 q) = (imp True).
Proof. exact (MK_COMB (@lem6883453) (@lem6883452 q)). Qed.
Lemma lem6883455 (r : Prop) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem6883456 (q : Prop) (r : Prop) : (term795 q r) = (True -> r).
Proof. exact (MK_COMB (@lem6883454 q) (@lem6883455 r)). Qed.
Lemma lem6883458 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem6883459 (r : Prop) : (True -> r) = r.
Proof. exact (@lem6883458 r). Qed.
Lemma lem6883460 (q : Prop) (r : Prop) : (term795 q r) = r.
Proof. exact (TRANS (@lem6883456 q r) (@lem6883459 r)). Qed.
Lemma lem6883461 (q : Prop) (r : Prop) : (term781 q r) = (term796 q r).
Proof. exact (MK_COMB (@lem6883438 q r) (@lem6883460 q r)). Qed.
Lemma lem6883464 (q : Prop) (r : Prop) : (term796 q r) = (term781 q r).
Proof. exact (SYM (@lem6883461 q r)). Qed.
Lemma lem6883465 (r : Prop) : term776 r.
Proof. exact (@lem9851 r). Qed.
Lemma lem6883466 (r : Prop) : (term776 r) = (term777 r).
Proof. exact (eq_refl (term776 r)). Qed.
Lemma lem6883467 (r : Prop) : term777 r.
Proof. exact (EQ_MP (@lem6883466 r) (@lem6883465 r)). Qed.
Lemma lem6883468 (r : Prop) (h1 : r = True) : r = True.
Proof. exact (h1). Qed.
Lemma lem6883469 (r : Prop) (h1 : r = False) : r = False.
Proof. exact (h1). Qed.
Lemma lem6883478 (q : Prop) : (term797 q) = (term797 q).
Proof. exact (eq_refl (term797 q)). Qed.
Lemma lem6883479 (q : Prop) (r : Prop) (h1 : r = True) : (term798 q r) = (term799 q).
Proof. exact (MK_COMB (@lem6883478 q) (@lem6883468 r h1)). Qed.
Lemma lem6883480 (q : Prop) : (term799 q) = (term800 q).
Proof. exact (eq_refl (term799 q)). Qed.
Lemma lem6883481 (q : Prop) (r : Prop) : (term801 q r) = (term801 q r).
Proof. exact (eq_refl (term801 q r)). Qed.
Lemma lem6883482 (r : Prop) (q : Prop) : ((term798 q r) = (term799 q)) = ((term798 q r) = (term800 q)).
Proof. exact (MK_COMB (@lem6883481 q r) (@lem6883480 q)). Qed.
Lemma lem6883483 (q : Prop) (r : Prop) : (term798 q r) = (term796 q r).
Proof. exact (eq_refl (term798 q r)). Qed.
Lemma lem6883484 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6883485 (q : Prop) (r : Prop) : (term801 q r) = (term802 q r).
Proof. exact (MK_COMB (@lem6883484) (@lem6883483 q r)). Qed.
Lemma lem6883486 (q : Prop) : (term800 q) = (term800 q).
Proof. exact (eq_refl (term800 q)). Qed.
Lemma lem6883487 (r : Prop) (q : Prop) : ((term798 q r) = (term800 q)) = ((term796 q r) = (term800 q)).
Proof. exact (MK_COMB (@lem6883485 q r) (@lem6883486 q)). Qed.
Lemma lem6883488 (r : Prop) (q : Prop) : ((term798 q r) = (term799 q)) = ((term796 q r) = (term800 q)).
Proof. exact (TRANS (@lem6883482 r q) (@lem6883487 r q)). Qed.
Lemma lem6883489 (q : Prop) (r : Prop) (h1 : r = True) : (term796 q r) = (term800 q).
Proof. exact (EQ_MP (@lem6883488 r q) (@lem6883479 q r h1)). Qed.
Lemma lem6883490 (q : Prop) (r : Prop) (h1 : r = True) : (term800 q) = (term796 q r).
Proof. exact (SYM (@lem6883489 q r h1)). Qed.
Lemma lem6883491 (q : Prop) : (term797 q) = (term797 q).
Proof. exact (eq_refl (term797 q)). Qed.
Lemma lem6883492 (q : Prop) (r : Prop) (h1 : r = False) : (term798 q r) = (term803 q).
Proof. exact (MK_COMB (@lem6883491 q) (@lem6883469 r h1)). Qed.
Lemma lem6883493 (q : Prop) : (term803 q) = (term804 q).
Proof. exact (eq_refl (term803 q)). Qed.
Lemma lem6883494 (q : Prop) (r : Prop) : (term801 q r) = (term801 q r).
Proof. exact (eq_refl (term801 q r)). Qed.
Lemma lem6883495 (r : Prop) (q : Prop) : ((term798 q r) = (term803 q)) = ((term798 q r) = (term804 q)).
Proof. exact (MK_COMB (@lem6883494 q r) (@lem6883493 q)). Qed.
Lemma lem6883496 (q : Prop) (r : Prop) : (term798 q r) = (term796 q r).
Proof. exact (eq_refl (term798 q r)). Qed.
Lemma lem6883497 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6883498 (q : Prop) (r : Prop) : (term801 q r) = (term802 q r).
Proof. exact (MK_COMB (@lem6883497) (@lem6883496 q r)). Qed.
Lemma lem6883499 (q : Prop) : (term804 q) = (term804 q).
Proof. exact (eq_refl (term804 q)). Qed.
Lemma lem6883500 (r : Prop) (q : Prop) : ((term798 q r) = (term804 q)) = ((term796 q r) = (term804 q)).
Proof. exact (MK_COMB (@lem6883498 q r) (@lem6883499 q)). Qed.
Lemma lem6883501 (r : Prop) (q : Prop) : ((term798 q r) = (term803 q)) = ((term796 q r) = (term804 q)).
Proof. exact (TRANS (@lem6883495 r q) (@lem6883500 r q)). Qed.
Lemma lem6883502 (q : Prop) (r : Prop) (h1 : r = False) : (term796 q r) = (term804 q).
Proof. exact (EQ_MP (@lem6883501 r q) (@lem6883492 q r h1)). Qed.
Lemma lem6883503 (q : Prop) (r : Prop) (h1 : r = False) : (term804 q) = (term796 q r).
Proof. exact (SYM (@lem6883502 q r h1)). Qed.
Lemma lem6883505 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6883506 (q : Prop) : (term800 q) = True.
Proof. exact (@lem6883505 (term805 q)). Qed.
Lemma lem6883507 (q : Prop) : True = (term800 q).
Proof. exact (SYM (@lem6883506 q)). Qed.
Lemma lem6883508 (q : Prop) : term800 q.
Proof. exact (EQ_MP (@lem6883507 q) (@lem0)). Qed.
Lemma lem6883510 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem6883511 (q : Prop) : (term804 q) = (term806 q).
Proof. exact (@lem6883510 (term807 q)). Qed.
Lemma lem6883513 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem6883514 (q : Prop) : (term807 q) = False.
Proof. exact (@lem6883513 (q -> False)). Qed.
Lemma lem6883515 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6883516 (q : Prop) : (term806 q) = (~ False).
Proof. exact (MK_COMB (@lem6883515) (@lem6883514 q)). Qed.
Lemma lem6883518 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem6883519 (q : Prop) : (term806 q) = True.
Proof. exact (TRANS (@lem6883516 q) (@lem6883518)). Qed.
Lemma lem6883520 (q : Prop) : (term804 q) = True.
Proof. exact (TRANS (@lem6883511 q) (@lem6883519 q)). Qed.
Lemma lem6883521 (q : Prop) : True = (term804 q).
Proof. exact (SYM (@lem6883520 q)). Qed.
Lemma lem6883522 (q : Prop) : term804 q.
Proof. exact (EQ_MP (@lem6883521 q) (@lem0)). Qed.
Lemma lem6883523 (q : Prop) (r : Prop) (h1 : r = False) : term796 q r.
Proof. exact (EQ_MP (@lem6883503 q r h1) (@lem6883522 q)). Qed.
Lemma lem6883524 (q : Prop) (r : Prop) (h1 : r = True) : term796 q r.
Proof. exact (EQ_MP (@lem6883490 q r h1) (@lem6883508 q)). Qed.
Lemma lem6883526 (q : Prop) (r : Prop) : term796 q r.
Proof. exact (or_elim (@lem6883467 r) (fun h0 : r = True => @lem6883524 q r h0) (fun h0 : r = False => @lem6883523 q r h0)). Qed.
Lemma lem6883527 (q : Prop) (r : Prop) : term781 q r.
Proof. exact (EQ_MP (@lem6883464 q r) (@lem6883526 q r)). Qed.
Lemma lem6883533 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem6883534 (r : Prop) : (False -> r) = True.
Proof. exact (@lem6883533 r). Qed.
Lemma lem6883535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6883536 (r : Prop) : (term808 r) = (and True).
Proof. exact (MK_COMB (@lem6883535) (@lem6883534 r)). Qed.
Lemma lem6883539 (q : Prop) (r : Prop) : (q -> r) = (q -> r).
Proof. exact (eq_refl (q -> r)). Qed.
Lemma lem6883540 (q : Prop) (r : Prop) : (term809 q r) = (term810 q r).
Proof. exact (MK_COMB (@lem6883536 r) (@lem6883539 q r)). Qed.
Lemma lem6883542 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6883543 (q : Prop) (r : Prop) : (term810 q r) = (q -> r).
Proof. exact (@lem6883542 (q -> r)). Qed.
Lemma lem6883546 (q : Prop) (r : Prop) : (term809 q r) = (q -> r).
Proof. exact (TRANS (@lem6883540 q r) (@lem6883543 q r)). Qed.
Lemma lem6883547 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6883548 (q : Prop) (r : Prop) : (term811 q r) = (term812 q r).
Proof. exact (MK_COMB (@lem6883547) (@lem6883546 q r)). Qed.
Lemma lem6883554 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem6883555 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6883556 : term813 = (imp True).
Proof. exact (MK_COMB (@lem6883555) (@lem6883554)). Qed.
Lemma lem6883557 (q : Prop) : q = q.
Proof. exact (eq_refl q). Qed.
Lemma lem6883558 (q : Prop) : (term814 q) = (True -> q).
Proof. exact (MK_COMB (@lem6883556) (@lem6883557 q)). Qed.
Lemma lem6883560 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem6883561 (q : Prop) : (True -> q) = q.
Proof. exact (@lem6883560 q). Qed.
Lemma lem6883562 (q : Prop) : (term814 q) = q.
Proof. exact (TRANS (@lem6883558 q) (@lem6883561 q)). Qed.
Lemma lem6883563 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6883564 (q : Prop) : (term815 q) = (imp q).
Proof. exact (MK_COMB (@lem6883563) (@lem6883562 q)). Qed.
Lemma lem6883565 (r : Prop) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem6883566 (q : Prop) (r : Prop) : (term816 q r) = (q -> r).
Proof. exact (MK_COMB (@lem6883564 q) (@lem6883565 r)). Qed.
Lemma lem6883569 (q : Prop) (r : Prop) : (term786 q r) = (term817 q r).
Proof. exact (MK_COMB (@lem6883548 q r) (@lem6883566 q r)). Qed.
Lemma lem6883571 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem6883572 (q : Prop) (r : Prop) : (term817 q r) = True.
Proof. exact (@lem6883571 (q -> r)). Qed.
Lemma lem6883573 (q : Prop) (r : Prop) : (term786 q r) = True.
Proof. exact (TRANS (@lem6883569 q r) (@lem6883572 q r)). Qed.
Lemma lem6883574 (q : Prop) (r : Prop) : True = (term786 q r).
Proof. exact (SYM (@lem6883573 q r)). Qed.
Lemma lem6883575 (q : Prop) (r : Prop) : term786 q r.
Proof. exact (EQ_MP (@lem6883574 q r) (@lem0)). Qed.
Lemma lem6883576 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : term783 p q r.
Proof. exact (EQ_MP (@lem6883421 q r p h1) (@lem6883575 q r)). Qed.
Lemma lem6883577 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : term783 p q r.
Proof. exact (EQ_MP (@lem6883408 q r p h1) (@lem6883527 q r)). Qed.
Lemma lem6883580 (p : Prop) (q : Prop) (r : Prop) : term783 p q r.
Proof. exact (or_elim (@lem6883379 p) (fun h0 : p = True => @lem6883577 q r p h0) (fun h0 : p = False => @lem6883576 q r p h0)). Qed.
Lemma lem6883581 (p : Prop) (q : Prop) (r : Prop) (h1 : term783 p q r) : term783 p q r.
Proof. exact (h1). Qed.
Lemma lem6883582 (p : Prop) (q : Prop) (r : Prop) (h1 : term818 p q r) : term818 p q r.
Proof. exact (h1). Qed.
Lemma lem6883583 (p : Prop) (q : Prop) (r : Prop) (h1 : term818 p q r) (h2 : term783 p q r) : term819 p q r.
Proof. exact (@lem6883581 p q r h2 (@lem6883582 p q r h1)). Qed.
Lemma lem6883584 (p : Prop) (q : Prop) (r : Prop) (h1 : term818 p q r) : term820 p q r.
Proof. exact (fun h0 : term783 p q r => @lem6883583 p q r h1 h0). Qed.
Lemma lem6883585 (p : Prop) (q : Prop) (r : Prop) (h1 : term783 p q r) : term783 p q r.
Proof. exact (h1). Qed.
Lemma lem6883586 (p : Prop) (q : Prop) (r : Prop) (h1 : term818 p q r) (h2 : term783 p q r) : term819 p q r.
Proof. exact (@lem6883584 p q r h1 (@lem6883585 p q r h2)). Qed.
Lemma lem6883587 (p : Prop) (q : Prop) (r : Prop) (h1 : term783 p q r) : term783 p q r.
Proof. exact (fun h0 : term818 p q r => @lem6883586 p q r h0 h1). Qed.
Lemma lem6883588 (p : Prop) (q : Prop) (r : Prop) : term821 p q r.
Proof. exact (fun h0 : term783 p q r => @lem6883587 p q r h0). Qed.
Lemma lem6883590 {A K : Type'} : term822 A K.
Proof. exact (@lem6790065 A K). Qed.
Lemma lem6883591 {A K : Type'} : term823 A K.
Proof. exact (@lem6883590 A K (@UNIV A)). Qed.
Lemma lem6883592 {A K : Type'} : (term823 A K) = (term824 A K).
Proof. exact (eq_refl (term823 A K)). Qed.
Lemma lem6883593 {A K : Type'} : term824 A K.
Proof. exact (EQ_MP (@lem6883592 A K) (@lem6883591 A K)). Qed.
Lemma lem6883594 {A K : Type'} (op : type1400 A) : term825 A K op.
Proof. exact (@lem6883593 A K (@neutral A op)). Qed.
Lemma lem6883595 {A K : Type'} (op : type1400 A) : (term825 A K op) = (term826 A K op).
Proof. exact (eq_refl (term825 A K op)). Qed.
Lemma lem6883596 {A K : Type'} (op : type1400 A) : term826 A K op.
Proof. exact (EQ_MP (@lem6883595 A K op) (@lem6883594 A K op)). Qed.
Lemma lem6883597 {A K : Type'} (op : type1400 A) : term827 A K op.
Proof. exact (@lem6883596 A K op op). Qed.
Lemma lem6883598 {A K : Type'} (op : type1400 A) : (term827 A K op) = (term828 A K op).
Proof. exact (eq_refl (term827 A K op)). Qed.
Lemma lem6883599 {A K : Type'} (op : type1400 A) : term828 A K op.
Proof. exact (EQ_MP (@lem6883598 A K op) (@lem6883597 A K op)). Qed.
Lemma lem6883600 {A K : Type'} (op : type1400 A) (ltle : type1402 K) : term829 A K op ltle.
Proof. exact (@lem6883599 A K op ltle). Qed.
Lemma lem6883601 {A K : Type'} (op : type1400 A) (ltle : type1402 K) : (term829 A K op ltle) = (term830 A K op ltle).
Proof. exact (eq_refl (term829 A K op ltle)). Qed.
Lemma lem6883602 {A K : Type'} (op : type1400 A) (ltle : type1402 K) : term830 A K op ltle.
Proof. exact (EQ_MP (@lem6883601 A K op ltle) (@lem6883600 A K op ltle)). Qed.
Lemma lem6883603 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term831 A K op ltle f.
Proof. exact (@lem6883602 A K op ltle f). Qed.
Lemma lem6883604 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) : (term831 A K op ltle f) = (term832 A K op ltle f).
Proof. exact (eq_refl (term831 A K op ltle f)). Qed.
Lemma lem6883605 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term832 A K op ltle f.
Proof. exact (EQ_MP (@lem6883604 A K op ltle f) (@lem6883603 A K op ltle f)). Qed.
Lemma lem6883606 {K : Type'} (k : K -> Prop) : term833 K k.
Proof. exact (@lem9784 (k = (@EMPTY K))). Qed.
Lemma lem6883607 {K : Type'} (k : K -> Prop) : (term833 K k) = (term834 K k).
Proof. exact (eq_refl (term833 K k)). Qed.
Lemma lem6883608 {K : Type'} (k : K -> Prop) : term834 K k.
Proof. exact (EQ_MP (@lem6883607 K k) (@lem6883606 K k)). Qed.
Lemma lem6883610 {K : Type'} (k : K -> Prop) (h1 : term835 K k) : term835 K k.
Proof. exact (h1). Qed.
Lemma lem6883638 {A : Type'} (P : Prop) : term836 A P.
Proof. exact (@lem6418 A P). Qed.
Lemma lem6883639 {A : Type'} (P : Prop) : (term836 A P) = (term837 A P).
Proof. exact (eq_refl (term836 A P)). Qed.
Lemma lem6883640 {A : Type'} (P : Prop) : term837 A P.
Proof. exact (EQ_MP (@lem6883639 A P) (@lem6883638 A P)). Qed.
Lemma lem6883641 {A : Type'} (P : Prop) (Q : A -> Prop) : term838 A P Q.
Proof. exact (@lem6883640 A P Q). Qed.
Lemma lem6883642 {A : Type'} (P : Prop) (Q : A -> Prop) : (term838 A P Q) = ((term839 A P Q) = (term840 A P Q)).
Proof. exact (eq_refl (term838 A P Q)). Qed.
Lemma lem6883644 (h1 : term841) : term841.
Proof. exact (h1). Qed.
Lemma lem6883645 (P : nat -> Prop) (h1 : term841) : term842 P.
Proof. exact (@lem6883644 h1 P). Qed.
Lemma lem6883646 (P : nat -> Prop) : (term842 P) = (term843 P).
Proof. exact (eq_refl (term842 P)). Qed.
Lemma lem6883647 (P : nat -> Prop) (h1 : term841) : term843 P.
Proof. exact (EQ_MP (@lem6883646 P) (@lem6883645 P h1)). Qed.
Lemma lem6883648 (P : nat -> Prop) (h1 : term844 P) : term844 P.
Proof. exact (h1). Qed.
Lemma lem6883649 (P : nat -> Prop) (h1 : term841) (h2 : term844 P) : term845 P.
Proof. exact (@lem6883647 P h1 (@lem6883648 P h2)). Qed.
Lemma lem6883650 (P : nat -> Prop) (h1 : term844 P) : term846 P.
Proof. exact (fun h0 : term841 => @lem6883649 P h0 h1). Qed.
Lemma lem6883651 (h1 : term841) : term841.
Proof. exact (h1). Qed.
Lemma lem6883652 (P : nat -> Prop) (h1 : term841) (h2 : term844 P) : term845 P.
Proof. exact (@lem6883650 P h2 (@lem6883651 h1)). Qed.
Lemma lem6883653 (P : nat -> Prop) (h1 : term841) : term843 P.
Proof. exact (fun h0 : term844 P => @lem6883652 P h1 h0). Qed.
Lemma lem6883654 (h1 : term841) : term841.
Proof. exact (fun P : nat -> Prop => @lem6883653 P h1). Qed.
Lemma lem6883655 : term847.
Proof. exact (fun h0 : term841 => @lem6883654 h0). Qed.
Lemma lem6883656 : term841.
Proof. exact (@lem6883655 (@lem115780)). Qed.
Lemma lem6883657 (P : nat -> Prop) : term842 P.
Proof. exact (@lem6883656 P). Qed.
Lemma lem6883658 (P : nat -> Prop) : (term842 P) = (term843 P).
Proof. exact (eq_refl (term842 P)). Qed.
Lemma lem6883660 (t1 : Prop) : term848 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem6883661 (t1 : Prop) : (term848 t1) = (term849 t1).
Proof. exact (eq_refl (term848 t1)). Qed.
Lemma lem6883662 (t1 : Prop) : term849 t1.
Proof. exact (EQ_MP (@lem6883661 t1) (@lem6883660 t1)). Qed.
Lemma lem6883663 (t1 : Prop) (t2 : Prop) : term850 t1 t2.
Proof. exact (@lem6883662 t1 t2). Qed.
Lemma lem6883664 (t1 : Prop) (t2 : Prop) : (term850 t1 t2) = (term851 t1 t2).
Proof. exact (eq_refl (term850 t1 t2)). Qed.
Lemma lem6883665 (t1 : Prop) (t2 : Prop) : term851 t1 t2.
Proof. exact (EQ_MP (@lem6883664 t1 t2) (@lem6883663 t1 t2)). Qed.
Lemma lem6883666 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term852 t1 t2 t3.
Proof. exact (@lem6883665 t1 t2 t3). Qed.
Lemma lem6883667 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term852 t1 t2 t3) = ((term853 t1 t2 t3) = (term854 t1 t2 t3)).
Proof. exact (eq_refl (term852 t1 t2 t3)). Qed.
Lemma lem6883668 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term853 t1 t2 t3) = (term854 t1 t2 t3).
Proof. exact (EQ_MP (@lem6883667 t1 t2 t3) (@lem6883666 t1 t2 t3)). Qed.
Lemma lem6883669 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term854 t1 t2 t3) = (term853 t1 t2 t3).
Proof. exact (SYM (@lem6883668 t1 t2 t3)). Qed.
Lemma lem6883671 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6883672 {_125911 : Type'} (P : type686 _125911) : (term855 _125911 P) = (term856 _125911 P).
Proof. exact (@lem6883671 (term855 _125911 P)). Qed.
Lemma lem6883673 {_125911 : Type'} (P : type686 _125911) : (term856 _125911 P) = (term855 _125911 P).
Proof. exact (SYM (@lem6883672 _125911 P)). Qed.
Lemma lem6883674 {_125911 : Type'} (P : type686 _125911) (h1 : term857 _125911 P) : term857 _125911 P.
Proof. exact (h1). Qed.
Lemma lem6883677 {_125911 : Type'} (P : type686 _125911) (h1 : term856 _125911 P) : term856 _125911 P.
Proof. exact (h1). Qed.
Lemma lem6883678 {_125911 : Type'} (P : type686 _125911) : term858 _125911 P.
Proof. exact (fun h0 : term856 _125911 P => @lem6883677 _125911 P h0). Qed.
Lemma lem6883679 {_125911 : Type'} (P : type686 _125911) (h1 : term858 _125911 P) : term858 _125911 P.
Proof. exact (h1). Qed.
Lemma lem6883680 {_125911 : Type'} (P : type686 _125911) (h1 : term856 _125911 P) : term856 _125911 P.
Proof. exact (h1). Qed.
Lemma lem6883681 {_125911 : Type'} (P : type686 _125911) (h1 : term856 _125911 P) (h2 : term858 _125911 P) : term856 _125911 P.
Proof. exact (@lem6883679 _125911 P h2 (@lem6883680 _125911 P h1)). Qed.
Lemma lem6883682 {_125911 : Type'} (P : type686 _125911) (h1 : term856 _125911 P) : term859 _125911 P.
Proof. exact (fun h0 : term858 _125911 P => @lem6883681 _125911 P h1 h0). Qed.
Lemma lem6883683 {_125911 : Type'} (P : type686 _125911) (h1 : term858 _125911 P) : term858 _125911 P.
Proof. exact (h1). Qed.
Lemma lem6883684 {_125911 : Type'} (P : type686 _125911) (h1 : term856 _125911 P) (h2 : term858 _125911 P) : term856 _125911 P.
Proof. exact (@lem6883682 _125911 P h1 (@lem6883683 _125911 P h2)). Qed.
Lemma lem6883685 {_125911 : Type'} (P : type686 _125911) (h1 : term858 _125911 P) : term858 _125911 P.
Proof. exact (fun h0 : term856 _125911 P => @lem6883684 _125911 P h0 h1). Qed.
Lemma lem6883686 {_125911 : Type'} (P : type686 _125911) : term860 _125911 P.
Proof. exact (fun h0 : term858 _125911 P => @lem6883685 _125911 P h0). Qed.
Lemma lem6883689 {_125911 : Type'} (P : type686 _125911) : term858 _125911 P.
Proof. exact (@lem6883686 _125911 P (@lem6883678 _125911 P)). Qed.
Lemma lem6883690 {_125911 : Type'} (P : type686 _125911) : term858 _125911 P.
Proof. exact (@lem6883689 _125911 P). Qed.
Lemma lem6883696 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6883697 {_125911 : Type'} (P : type686 _125911) : (term856 _125911 P) = (term861 _125911 P).
Proof. exact (@lem6883696 (term857 _125911 P)). Qed.
Lemma lem6883699 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6883700 {_125911 : Type'} (P : type686 _125911) : (term861 _125911 P) = (term855 _125911 P).
Proof. exact (@lem6883699 (term855 _125911 P)). Qed.
Lemma lem6883703 {_125911 : Type'} (P : type686 _125911) : (term856 _125911 P) = (term855 _125911 P).
Proof. exact (TRANS (@lem6883697 _125911 P) (@lem6883700 _125911 P)). Qed.
Lemma lem6883722 {_125911 : Type'} : (term862 _125911) = (term863 _125911).
Proof. exact (fun_ext (fun P : type686 _125911 => @lem6883703 _125911 P)). Qed.
Lemma lem6883723 {_125911 : Type'} : (@all ((_125911 -> Prop) -> Prop)) = (@all ((_125911 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_125911 -> Prop) -> Prop))). Qed.
Lemma lem6883732 {_125911 : Type'} : (term864 _125911) = (term865 _125911).
Proof. exact (MK_COMB (@lem6883723 _125911) (@lem6883722 _125911)). Qed.
Lemma lem6883737 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) : (term866 _125911 P k) = (term866 _125911 P k).
Proof. exact (eq_refl (term866 _125911 P k)). Qed.
Lemma lem6883738 {_125911 : Type'} (P : type686 _125911) : (term867 _125911 P) = (term867 _125911 P).
Proof. exact (fun_ext (fun k : _125911 -> Prop => @lem6883737 _125911 P k)). Qed.
Lemma lem6883739 {_125911 : Type'} : (@all (_125911 -> Prop)) = (@all (_125911 -> Prop)).
Proof. exact (eq_refl (@all (_125911 -> Prop))). Qed.
Lemma lem6883740 {_125911 : Type'} (P : type686 _125911) : (term868 _125911 P) = (term868 _125911 P).
Proof. exact (MK_COMB (@lem6883739 _125911) (@lem6883738 _125911 P)). Qed.
Lemma lem6883749 {_125911 : Type'} (n : nat) (P : type686 _125911) (k : _125911 -> Prop) : (term869 _125911 n P k) = (term869 _125911 n P k).
Proof. exact (eq_refl (term869 _125911 n P k)). Qed.
Lemma lem6883750 {_125911 : Type'} (n : nat) (P : type686 _125911) : (term870 _125911 n P) = (term870 _125911 n P).
Proof. exact (fun_ext (fun k : _125911 -> Prop => @lem6883749 _125911 n P k)). Qed.
Lemma lem6883751 {_125911 : Type'} : (@all (_125911 -> Prop)) = (@all (_125911 -> Prop)).
Proof. exact (eq_refl (@all (_125911 -> Prop))). Qed.
Lemma lem6883752 {_125911 : Type'} (n : nat) (P : type686 _125911) : (term871 _125911 n P) = (term871 _125911 n P).
Proof. exact (MK_COMB (@lem6883751 _125911) (@lem6883750 _125911 n P)). Qed.
Lemma lem6883753 {_125911 : Type'} (P : type686 _125911) : (term872 _125911 P) = (term872 _125911 P).
Proof. exact (fun_ext (fun n : nat => @lem6883752 _125911 n P)). Qed.
Lemma lem6883754 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6883755 {_125911 : Type'} (P : type686 _125911) : (term873 _125911 P) = (term873 _125911 P).
Proof. exact (MK_COMB (@lem6883754) (@lem6883753 _125911 P)). Qed.
Lemma lem6883756 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6883757 {_125911 : Type'} (P : type686 _125911) : (term874 _125911 P) = (term874 _125911 P).
Proof. exact (MK_COMB (@lem6883756) (@lem6883755 _125911 P)). Qed.
Lemma lem6883758 {_125911 : Type'} (P : type686 _125911) : (term855 _125911 P) = (term855 _125911 P).
Proof. exact (MK_COMB (@lem6883757 _125911 P) (@lem6883740 _125911 P)). Qed.
Lemma lem6883759 {_125911 : Type'} : (term863 _125911) = (term863 _125911).
Proof. exact (fun_ext (fun P : type686 _125911 => @lem6883758 _125911 P)). Qed.
Lemma lem6883760 {_125911 : Type'} : (@all ((_125911 -> Prop) -> Prop)) = (@all ((_125911 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_125911 -> Prop) -> Prop))). Qed.
Lemma lem6883761 {_125911 : Type'} : (term865 _125911) = (term865 _125911).
Proof. exact (MK_COMB (@lem6883760 _125911) (@lem6883759 _125911)). Qed.
Lemma lem6883796 {_125911 : Type'} : (term864 _125911) = (term865 _125911).
Proof. exact (TRANS (@lem6883732 _125911) (@lem6883761 _125911)). Qed.
Lemma lem6883797 {_125911 : Type'} : (term865 _125911) = (term864 _125911).
Proof. exact (SYM (@lem6883796 _125911)). Qed.
Lemma lem6883798 {_125911 : Type'} (P : type686 _125911) (h1 : term873 _125911 P) : term873 _125911 P.
Proof. exact (h1). Qed.
Lemma lem6883801 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6883802 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) : (P k) = (term875 _125911 P k).
Proof. exact (@lem6883801 (P k)). Qed.
Lemma lem6883803 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) : (term875 _125911 P k) = (P k).
Proof. exact (SYM (@lem6883802 _125911 P k)). Qed.
Lemma lem6883804 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term876 _125911 P k) : term876 _125911 P k.
Proof. exact (h1). Qed.
Lemma lem6883811 {_125911 : Type'} (k : _125911 -> Prop) (n : nat) : (term877 _125911 k n) = (term878 _125911 k n).
Proof. exact (@lem17045 (@FINITE _125911 k) ((@CARD _125911 k) = n)). Qed.
Lemma lem6883812 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) : (P k) = (P k).
Proof. exact (eq_refl (P k)). Qed.
Lemma lem6883813 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6883814 {_125911 : Type'} (k : _125911 -> Prop) (n : nat) : (term879 _125911 k n) = (term880 _125911 k n).
Proof. exact (MK_COMB (@lem6883813) (@lem6883811 _125911 k n)). Qed.
Lemma lem6883815 {_125911 : Type'} (n : nat) (P : type686 _125911) (k : _125911 -> Prop) : (term881 _125911 n P k) = (term882 _125911 n P k).
Proof. exact (MK_COMB (@lem6883814 _125911 k n) (@lem6883812 _125911 P k)). Qed.
Lemma lem6883816 {_125911 : Type'} (n : nat) (P : type686 _125911) (k : _125911 -> Prop) : (term869 _125911 n P k) = (term881 _125911 n P k).
Proof. exact (@lem17265 (term883 _125911 k n) (P k)). Qed.
Lemma lem6883817 {_125911 : Type'} (n : nat) (P : type686 _125911) (k : _125911 -> Prop) : (term869 _125911 n P k) = (term882 _125911 n P k).
Proof. exact (TRANS (@lem6883816 _125911 n P k) (@lem6883815 _125911 n P k)). Qed.
Lemma lem6883818 {_125911 : Type'} (n : nat) (P : type686 _125911) : (term870 _125911 n P) = (term884 _125911 n P).
Proof. exact (fun_ext (fun k : _125911 -> Prop => @lem6883817 _125911 n P k)). Qed.
Lemma lem6883819 {_125911 : Type'} : (@all (_125911 -> Prop)) = (@all (_125911 -> Prop)).
Proof. exact (eq_refl (@all (_125911 -> Prop))). Qed.
Lemma lem6883820 {_125911 : Type'} (n : nat) (P : type686 _125911) : (term871 _125911 n P) = (term885 _125911 n P).
Proof. exact (MK_COMB (@lem6883819 _125911) (@lem6883818 _125911 n P)). Qed.
Lemma lem6883821 {_125911 : Type'} (P : type686 _125911) : (term872 _125911 P) = (term886 _125911 P).
Proof. exact (fun_ext (fun n : nat => @lem6883820 _125911 n P)). Qed.
Lemma lem6883822 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6883863 {_125911 : Type'} (P : type686 _125911) : (term873 _125911 P) = (term887 _125911 P).
Proof. exact (MK_COMB (@lem6883822) (@lem6883821 _125911 P)). Qed.
Lemma lem6883864 {_125911 : Type'} (P : type686 _125911) (h1 : term873 _125911 P) : term887 _125911 P.
Proof. exact (EQ_MP (@lem6883863 _125911 P) (@lem6883798 _125911 P h1)). Qed.
Lemma lem6883870 {_125911 : Type'} (k : _125911 -> Prop) (h1 : @FINITE _125911 k) : @FINITE _125911 k.
Proof. exact (h1). Qed.
Lemma lem6883876 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term876 _125911 P k) : term876 _125911 P k.
Proof. exact (h1). Qed.
Lemma lem6883899 {_125911 : Type'} (n : nat) (P : type686 _125911) (k : _125911 -> Prop) : (term882 _125911 n P k) = (term882 _125911 n P k).
Proof. exact (eq_refl (term882 _125911 n P k)). Qed.
Lemma lem6883900 {_125911 : Type'} (n : nat) (P : type686 _125911) : (term884 _125911 n P) = (term884 _125911 n P).
Proof. exact (fun_ext (fun k : _125911 -> Prop => @lem6883899 _125911 n P k)). Qed.
Lemma lem6883901 {_125911 : Type'} : (@all (_125911 -> Prop)) = (@all (_125911 -> Prop)).
Proof. exact (eq_refl (@all (_125911 -> Prop))). Qed.
Lemma lem6883902 {_125911 : Type'} (n : nat) (P : type686 _125911) : (term885 _125911 n P) = (term885 _125911 n P).
Proof. exact (MK_COMB (@lem6883901 _125911) (@lem6883900 _125911 n P)). Qed.
Lemma lem6883903 {_125911 : Type'} (P : type686 _125911) : (term886 _125911 P) = (term886 _125911 P).
Proof. exact (fun_ext (fun n : nat => @lem6883902 _125911 n P)). Qed.
Lemma lem6883904 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6883905 {_125911 : Type'} (P : type686 _125911) : (term887 _125911 P) = (term887 _125911 P).
Proof. exact (MK_COMB (@lem6883904) (@lem6883903 _125911 P)). Qed.
Lemma lem6883906 {_125911 : Type'} (P : type686 _125911) (h1 : term873 _125911 P) : term887 _125911 P.
Proof. exact (EQ_MP (@lem6883905 _125911 P) (@lem6883864 _125911 P h1)). Qed.
Lemma lem6883910 {_125911 : Type'} (k : _125911 -> Prop) (h1 : @FINITE _125911 k) : @FINITE _125911 k.
Proof. exact (h1). Qed.
Lemma lem6883916 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term876 _125911 P k) : term876 _125911 P k.
Proof. exact (h1). Qed.
Lemma lem6883930 {_125911 : Type'} (n : nat) (P : type686 _125911) (k : _125911 -> Prop) : (term882 _125911 n P k) = (term882 _125911 n P k).
Proof. exact (eq_refl (term882 _125911 n P k)). Qed.
Lemma lem6883931 {_125911 : Type'} (n : nat) (P : type686 _125911) : (term884 _125911 n P) = (term884 _125911 n P).
Proof. exact (fun_ext (fun k : _125911 -> Prop => @lem6883930 _125911 n P k)). Qed.
Lemma lem6883932 {_125911 : Type'} : (@all (_125911 -> Prop)) = (@all (_125911 -> Prop)).
Proof. exact (eq_refl (@all (_125911 -> Prop))). Qed.
Lemma lem6883933 {_125911 : Type'} (n : nat) (P : type686 _125911) : (term885 _125911 n P) = (term885 _125911 n P).
Proof. exact (MK_COMB (@lem6883932 _125911) (@lem6883931 _125911 n P)). Qed.
Lemma lem6883934 {_125911 : Type'} (P : type686 _125911) : (term886 _125911 P) = (term886 _125911 P).
Proof. exact (fun_ext (fun n : nat => @lem6883933 _125911 n P)). Qed.
Lemma lem6883935 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6883937 {_125911 : Type'} (P : type686 _125911) : (term887 _125911 P) = (term887 _125911 P).
Proof. exact (MK_COMB (@lem6883935) (@lem6883934 _125911 P)). Qed.
Lemma lem6883938 {_125911 : Type'} (P : type686 _125911) (h1 : term873 _125911 P) : term887 _125911 P.
Proof. exact (EQ_MP (@lem6883937 _125911 P) (@lem6883906 _125911 P h1)). Qed.
Lemma lem6883942 {_125911 : Type'} (k : _125911 -> Prop) (h1 : @FINITE _125911 k) : @FINITE _125911 k.
Proof. exact (h1). Qed.
Lemma lem6883946 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term876 _125911 P k) : term876 _125911 P k.
Proof. exact (h1). Qed.
Lemma lem6883947 {_125911 : Type'} (_91923 : nat) (P : type686 _125911) (h1 : term873 _125911 P) : term888 _125911 P _91923.
Proof. exact (@lem6883938 _125911 P h1 _91923). Qed.
Lemma lem6883948 {_125911 : Type'} (_91923 : nat) (P : type686 _125911) : (term888 _125911 P _91923) = (term885 _125911 _91923 P).
Proof. exact (eq_refl (term888 _125911 P _91923)). Qed.
Lemma lem6883949 {_125911 : Type'} (_91923 : nat) (P : type686 _125911) (h1 : term873 _125911 P) : term885 _125911 _91923 P.
Proof. exact (EQ_MP (@lem6883948 _125911 _91923 P) (@lem6883947 _125911 _91923 P h1)). Qed.
Lemma lem6883950 {_125911 : Type'} (_91923 : nat) (_91924 : _125911 -> Prop) (P : type686 _125911) (h1 : term873 _125911 P) : term889 _125911 _91923 P _91924.
Proof. exact (@lem6883949 _125911 _91923 P h1 _91924). Qed.
Lemma lem6883951 {_125911 : Type'} (_91923 : nat) (P : type686 _125911) (_91924 : _125911 -> Prop) : (term889 _125911 _91923 P _91924) = (term882 _125911 _91923 P _91924).
Proof. exact (eq_refl (term889 _125911 _91923 P _91924)). Qed.
Lemma lem6883952 {_125911 : Type'} (_91923 : nat) (_91924 : _125911 -> Prop) (P : type686 _125911) (h1 : term873 _125911 P) : term882 _125911 _91923 P _91924.
Proof. exact (EQ_MP (@lem6883951 _125911 _91923 P _91924) (@lem6883950 _125911 _91923 _91924 P h1)). Qed.
Lemma lem6883963 {_125911 : Type'} (_91923 : nat) (P : type686 _125911) (_91924 : _125911 -> Prop) : (term882 _125911 _91923 P _91924) = (term890 _125911 _91923 P _91924).
Proof. exact (@lem6883669 (term891 _125911 _91924) (term892 _125911 _91924 _91923) (P _91924)). Qed.
Lemma lem6883964 {_125911 : Type'} (_91923 : nat) (_91924 : _125911 -> Prop) (P : type686 _125911) (h1 : term873 _125911 P) : term890 _125911 _91923 P _91924.
Proof. exact (EQ_MP (@lem6883963 _125911 _91923 P _91924) (@lem6883952 _125911 _91923 _91924 P h1)). Qed.
Lemma lem6883966 {_125911 : Type'} (k : _125911 -> Prop) (h1 : @FINITE _125911 k) : @FINITE _125911 k.
Proof. exact (h1). Qed.
Lemma lem6883968 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term876 _125911 P k) : term876 _125911 P k.
Proof. exact (h1). Qed.
Lemma lem6884006 {_125911 : Type'} (k : _125911 -> Prop) (h1 : @FINITE _125911 k) : @FINITE _125911 k.
Proof. exact (h1). Qed.
Lemma lem6884007 {_125911 : Type'} (k : _125911 -> Prop) (h1 : @FINITE _125911 k) : term893 _125911 k.
Proof. exact (fun h0 : term891 _125911 k => @lem6884006 _125911 k h1). Qed.
Lemma lem6884009 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6884010 {_125911 : Type'} (k : _125911 -> Prop) : (term893 _125911 k) = (@FINITE _125911 k).
Proof. exact (@lem6884009 (@FINITE _125911 k)). Qed.
Lemma lem6884011 {_125911 : Type'} (k : _125911 -> Prop) (h1 : @FINITE _125911 k) : @FINITE _125911 k.
Proof. exact (EQ_MP (@lem6884010 _125911 k) (@lem6884007 _125911 k h1)). Qed.
Lemma lem6884013 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem6884014 {_125911 : Type'} (k : _125911 -> Prop) : (@CARD _125911 k) = (@CARD _125911 k).
Proof. exact (@lem6884013 (@CARD _125911 k)). Qed.
Lemma lem6884015 {_125911 : Type'} (k : _125911 -> Prop) : term894 _125911 k.
Proof. exact (fun h0 : term895 _125911 k => @lem6884014 _125911 k). Qed.
Lemma lem6884017 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6884018 {_125911 : Type'} (k : _125911 -> Prop) : (term894 _125911 k) = ((@CARD _125911 k) = (@CARD _125911 k)).
Proof. exact (@lem6884017 ((@CARD _125911 k) = (@CARD _125911 k))). Qed.
Lemma lem6884019 {_125911 : Type'} (k : _125911 -> Prop) : (@CARD _125911 k) = (@CARD _125911 k).
Proof. exact (EQ_MP (@lem6884018 _125911 k) (@lem6884015 _125911 k)). Qed.
Lemma lem6884025 (q : Prop) (p : Prop) (r : Prop) : (term853 p q r) = (term853 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6884026 {_125911 : Type'} (_91923 : nat) (P : type686 _125911) (_91924 : _125911 -> Prop) : (term890 _125911 _91923 P _91924) = (term896 _125911 _91923 P _91924).
Proof. exact (@lem6884025 (term892 _125911 _91924 _91923) (term891 _125911 _91924) (P _91924)). Qed.
Lemma lem6884042 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6884043 {_125911 : Type'} (P : type686 _125911) (_91924 : _125911 -> Prop) : (term897 _125911 P _91924) = (term898 _125911 P _91924).
Proof. exact (@lem6884042 (P _91924) (term891 _125911 _91924)). Qed.
Lemma lem6884049 {_125911 : Type'} (_91924 : _125911 -> Prop) (_91923 : nat) : (term899 _125911 _91924 _91923) = (term899 _125911 _91924 _91923).
Proof. exact (eq_refl (term899 _125911 _91924 _91923)). Qed.
Lemma lem6884050 {_125911 : Type'} (_91923 : nat) (P : type686 _125911) (_91924 : _125911 -> Prop) : (term896 _125911 _91923 P _91924) = (term900 _125911 _91923 P _91924).
Proof. exact (MK_COMB (@lem6884049 _125911 _91924 _91923) (@lem6884043 _125911 P _91924)). Qed.
Lemma lem6884054 (q : Prop) (p : Prop) (r : Prop) : (term853 p q r) = (term853 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6884055 {_125911 : Type'} (P : type686 _125911) (_91923 : nat) (_91924 : _125911 -> Prop) : (term900 _125911 _91923 P _91924) = (term901 _125911 P _91923 _91924).
Proof. exact (@lem6884054 (P _91924) (term892 _125911 _91924 _91923) (term891 _125911 _91924)). Qed.
Lemma lem6884073 {_125911 : Type'} (P : type686 _125911) (_91923 : nat) (_91924 : _125911 -> Prop) : (term896 _125911 _91923 P _91924) = (term901 _125911 P _91923 _91924).
Proof. exact (TRANS (@lem6884050 _125911 _91923 P _91924) (@lem6884055 _125911 P _91923 _91924)). Qed.
Lemma lem6884074 {_125911 : Type'} (P : type686 _125911) (_91923 : nat) (_91924 : _125911 -> Prop) : (term890 _125911 _91923 P _91924) = (term901 _125911 P _91923 _91924).
Proof. exact (TRANS (@lem6884026 _125911 _91923 P _91924) (@lem6884073 _125911 P _91923 _91924)). Qed.
Lemma lem6884075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6884076 {_125911 : Type'} (P : type686 _125911) (_91923 : nat) (_91924 : _125911 -> Prop) : (term902 _125911 _91923 P _91924) = (term903 _125911 P _91923 _91924).
Proof. exact (MK_COMB (@lem6884075) (@lem6884074 _125911 P _91923 _91924)). Qed.
Lemma lem6884090 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6884091 {_125911 : Type'} (_91923 : nat) (_91924 : _125911 -> Prop) : (term878 _125911 _91924 _91923) = (term904 _125911 _91923 _91924).
Proof. exact (@lem6884090 (term892 _125911 _91924 _91923) (term891 _125911 _91924)). Qed.
Lemma lem6884099 {_125911 : Type'} (P : type686 _125911) (_91924 : _125911 -> Prop) : (term905 _125911 P _91924) = (term905 _125911 P _91924).
Proof. exact (eq_refl (term905 _125911 P _91924)). Qed.
Lemma lem6884100 {_125911 : Type'} (P : type686 _125911) (_91923 : nat) (_91924 : _125911 -> Prop) : (term906 _125911 P _91924 _91923) = (term901 _125911 P _91923 _91924).
Proof. exact (MK_COMB (@lem6884099 _125911 P _91924) (@lem6884091 _125911 _91923 _91924)). Qed.
Lemma lem6884111 {_125911 : Type'} (P : type686 _125911) (_91923 : nat) (_91924 : _125911 -> Prop) : ((term890 _125911 _91923 P _91924) = (term906 _125911 P _91924 _91923)) = ((term901 _125911 P _91923 _91924) = (term901 _125911 P _91923 _91924)).
Proof. exact (MK_COMB (@lem6884076 _125911 P _91923 _91924) (@lem6884100 _125911 P _91923 _91924)). Qed.
Lemma lem6884113 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6884114 (x : Prop) : (x = x) = True.
Proof. exact (@lem6884113 Prop x). Qed.
Lemma lem6884115 {_125911 : Type'} (P : type686 _125911) (_91923 : nat) (_91924 : _125911 -> Prop) : ((term901 _125911 P _91923 _91924) = (term901 _125911 P _91923 _91924)) = True.
Proof. exact (@lem6884114 (term901 _125911 P _91923 _91924)). Qed.
Lemma lem6884116 {_125911 : Type'} (P : type686 _125911) (_91924 : _125911 -> Prop) (_91923 : nat) : ((term890 _125911 _91923 P _91924) = (term906 _125911 P _91924 _91923)) = True.
Proof. exact (TRANS (@lem6884111 _125911 P _91923 _91924) (@lem6884115 _125911 P _91923 _91924)). Qed.
Lemma lem6884117 {_125911 : Type'} (P : type686 _125911) (_91924 : _125911 -> Prop) (_91923 : nat) : True = ((term890 _125911 _91923 P _91924) = (term906 _125911 P _91924 _91923)).
Proof. exact (SYM (@lem6884116 _125911 P _91924 _91923)). Qed.
Lemma lem6884118 {_125911 : Type'} (P : type686 _125911) (_91924 : _125911 -> Prop) (_91923 : nat) : (term890 _125911 _91923 P _91924) = (term906 _125911 P _91924 _91923).
Proof. exact (EQ_MP (@lem6884117 _125911 P _91924 _91923) (@lem0)). Qed.
Lemma lem6884119 {_125911 : Type'} (_91924 : _125911 -> Prop) (_91923 : nat) (P : type686 _125911) (h1 : term873 _125911 P) : term906 _125911 P _91924 _91923.
Proof. exact (EQ_MP (@lem6884118 _125911 P _91924 _91923) (@lem6883964 _125911 _91923 _91924 P h1)). Qed.
Lemma lem6884121 (b : Prop) (a : Prop) : (a \/ b) = (term907 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6884122 {_125911 : Type'} (_91923 : nat) (P : type686 _125911) (_91924 : _125911 -> Prop) : (term906 _125911 P _91924 _91923) = (term908 _125911 _91923 P _91924).
Proof. exact (@lem6884121 (term878 _125911 _91924 _91923) (P _91924)). Qed.
Lemma lem6884124 (a : Prop) (b : Prop) : (term909 a b) = (term910 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6884125 {_125911 : Type'} (_91924 : _125911 -> Prop) (_91923 : nat) : (term911 _125911 _91924 _91923) = (term912 _125911 _91924 _91923).
Proof. exact (@lem6884124 (term891 _125911 _91924) (term892 _125911 _91924 _91923)). Qed.
Lemma lem6884127 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6884128 {_125911 : Type'} (_91924 : _125911 -> Prop) : (term913 _125911 _91924) = (@FINITE _125911 _91924).
Proof. exact (@lem6884127 (@FINITE _125911 _91924)). Qed.
Lemma lem6884129 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6884130 {_125911 : Type'} (_91924 : _125911 -> Prop) : (term914 _125911 _91924) = (term915 _125911 _91924).
Proof. exact (MK_COMB (@lem6884129) (@lem6884128 _125911 _91924)). Qed.
Lemma lem6884132 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6884133 {_125911 : Type'} (_91924 : _125911 -> Prop) (_91923 : nat) : (term916 _125911 _91924 _91923) = ((@CARD _125911 _91924) = _91923).
Proof. exact (@lem6884132 ((@CARD _125911 _91924) = _91923)). Qed.
Lemma lem6884134 {_125911 : Type'} (_91924 : _125911 -> Prop) (_91923 : nat) : (term912 _125911 _91924 _91923) = (term883 _125911 _91924 _91923).
Proof. exact (MK_COMB (@lem6884130 _125911 _91924) (@lem6884133 _125911 _91924 _91923)). Qed.
Lemma lem6884135 {_125911 : Type'} (_91924 : _125911 -> Prop) (_91923 : nat) : (term911 _125911 _91924 _91923) = (term883 _125911 _91924 _91923).
Proof. exact (TRANS (@lem6884125 _125911 _91924 _91923) (@lem6884134 _125911 _91924 _91923)). Qed.
Lemma lem6884136 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6884137 {_125911 : Type'} (_91924 : _125911 -> Prop) (_91923 : nat) : (term917 _125911 _91924 _91923) = (term918 _125911 _91924 _91923).
Proof. exact (MK_COMB (@lem6884136) (@lem6884135 _125911 _91924 _91923)). Qed.
Lemma lem6884138 {_125911 : Type'} (P : type686 _125911) (_91924 : _125911 -> Prop) : (P _91924) = (P _91924).
Proof. exact (eq_refl (P _91924)). Qed.
Lemma lem6884139 {_125911 : Type'} (_91923 : nat) (P : type686 _125911) (_91924 : _125911 -> Prop) : (term908 _125911 _91923 P _91924) = (term869 _125911 _91923 P _91924).
Proof. exact (MK_COMB (@lem6884137 _125911 _91924 _91923) (@lem6884138 _125911 P _91924)). Qed.
Lemma lem6884140 {_125911 : Type'} (_91923 : nat) (P : type686 _125911) (_91924 : _125911 -> Prop) : (term906 _125911 P _91924 _91923) = (term869 _125911 _91923 P _91924).
Proof. exact (TRANS (@lem6884122 _125911 _91923 P _91924) (@lem6884139 _125911 _91923 P _91924)). Qed.
Lemma lem6884142 {_125911 : Type'} (k : _125911 -> Prop) (h1 : @FINITE _125911 k) : term919 _125911 k.
Proof. exact (conj (@lem6884011 _125911 k h1) (@lem6884019 _125911 k)). Qed.
Lemma lem6884144 {_125911 : Type'} (_91923 : nat) (_91924 : _125911 -> Prop) (P : type686 _125911) (h1 : term873 _125911 P) : term869 _125911 _91923 P _91924.
Proof. exact (EQ_MP (@lem6884140 _125911 _91923 P _91924) (@lem6884119 _125911 _91924 _91923 P h1)). Qed.
Lemma lem6884145 {_125911 : Type'} (_91923 : nat) (_91924 : _125911 -> Prop) (P : type686 _125911) (h1 : term873 _125911 P) : term869 _125911 _91923 P _91924.
Proof. exact (@lem6884144 _125911 _91923 _91924 P h1). Qed.
Lemma lem6884146 {_125911 : Type'} (k : _125911 -> Prop) (P : type686 _125911) (h1 : term873 _125911 P) : term920 _125911 P k.
Proof. exact (@lem6884145 _125911 (@CARD _125911 k) k P h1). Qed.
Lemma lem6884149 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) : P k.
Proof. exact (@lem6884146 _125911 k P h1 (@lem6884142 _125911 k h2)). Qed.
Lemma lem6884150 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) : term921 _125911 P k.
Proof. exact (fun h0 : term876 _125911 P k => @lem6884149 _125911 P k h1 h2). Qed.
Lemma lem6884152 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6884153 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) : (term921 _125911 P k) = (P k).
Proof. exact (@lem6884152 (P k)). Qed.
Lemma lem6884154 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) : P k.
Proof. exact (EQ_MP (@lem6884153 _125911 P k) (@lem6884150 _125911 P k h1 h2)). Qed.
Lemma lem6884157 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6884159 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) : (term876 _125911 P k) = (term922 _125911 P k).
Proof. exact (@lem6884157 (P k)). Qed.
Lemma lem6884162 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term876 _125911 P k) : term922 _125911 P k.
Proof. exact (EQ_MP (@lem6884159 _125911 P k) (@lem6883968 _125911 P k h1)). Qed.
Lemma lem6884165 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : False.
Proof. exact (@lem6884162 _125911 P k h3 (@lem6884154 _125911 P k h1 h2)). Qed.
Lemma lem6884166 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : term74.
Proof. exact (fun h0 : ~ False => @lem6884165 _125911 P k h1 h2 h3). Qed.
Lemma lem6884168 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6884169 : term74 = False.
Proof. exact (@lem6884168 False). Qed.
Lemma lem6884170 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : False.
Proof. exact (EQ_MP (@lem6884169) (@lem6884166 _125911 P k h1 h2 h3)). Qed.
Lemma lem6884171 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : (term876 _125911 P k) = False.
Proof. exact (prop_ext (fun h4 : term876 _125911 P k => @lem6884170 _125911 P k h1 h2 h3) (fun h4 : False => @lem6883968 _125911 P k h3)). Qed.
Lemma lem6884172 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : False.
Proof. exact (EQ_MP (@lem6884171 _125911 P k h1 h2 h3) (@lem6883968 _125911 P k h3)). Qed.
Lemma lem6884173 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : (@FINITE _125911 k) = False.
Proof. exact (prop_ext (fun h4 : @FINITE _125911 k => @lem6884172 _125911 P k h1 h2 h3) (fun h4 : False => @lem6883966 _125911 k h2)). Qed.
Lemma lem6884174 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : False.
Proof. exact (EQ_MP (@lem6884173 _125911 P k h1 h2 h3) (@lem6883966 _125911 k h2)). Qed.
Lemma lem6884175 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : (term876 _125911 P k) = False.
Proof. exact (prop_ext (fun h4 : term876 _125911 P k => @lem6884174 _125911 P k h1 h2 h3) (fun h4 : False => @lem6883946 _125911 P k h3)). Qed.
Lemma lem6884176 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : False.
Proof. exact (EQ_MP (@lem6884175 _125911 P k h1 h2 h3) (@lem6883946 _125911 P k h3)). Qed.
Lemma lem6884177 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : (@FINITE _125911 k) = False.
Proof. exact (prop_ext (fun h4 : @FINITE _125911 k => @lem6884176 _125911 P k h1 h2 h3) (fun h4 : False => @lem6883942 _125911 k h2)). Qed.
Lemma lem6884178 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : False.
Proof. exact (EQ_MP (@lem6884177 _125911 P k h1 h2 h3) (@lem6883942 _125911 k h2)). Qed.
Lemma lem6884179 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : (term876 _125911 P k) = False.
Proof. exact (prop_ext (fun h4 : term876 _125911 P k => @lem6884178 _125911 P k h1 h2 h3) (fun h4 : False => @lem6883946 _125911 P k h3)). Qed.
Lemma lem6884180 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : False.
Proof. exact (EQ_MP (@lem6884179 _125911 P k h1 h2 h3) (@lem6883946 _125911 P k h3)). Qed.
Lemma lem6884181 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : (@FINITE _125911 k) = False.
Proof. exact (prop_ext (fun h4 : @FINITE _125911 k => @lem6884180 _125911 P k h1 h2 h3) (fun h4 : False => @lem6883942 _125911 k h2)). Qed.
Lemma lem6884182 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : False.
Proof. exact (EQ_MP (@lem6884181 _125911 P k h1 h2 h3) (@lem6883942 _125911 k h2)). Qed.
Lemma lem6884183 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : (term876 _125911 P k) = False.
Proof. exact (prop_ext (fun h4 : term876 _125911 P k => @lem6884182 _125911 P k h1 h2 h3) (fun h4 : False => @lem6883916 _125911 P k h3)). Qed.
Lemma lem6884184 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : False.
Proof. exact (EQ_MP (@lem6884183 _125911 P k h1 h2 h3) (@lem6883916 _125911 P k h3)). Qed.
Lemma lem6884185 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : (@FINITE _125911 k) = False.
Proof. exact (prop_ext (fun h4 : @FINITE _125911 k => @lem6884184 _125911 P k h1 h2 h3) (fun h4 : False => @lem6883910 _125911 k h2)). Qed.
Lemma lem6884186 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : False.
Proof. exact (EQ_MP (@lem6884185 _125911 P k h1 h2 h3) (@lem6883910 _125911 k h2)). Qed.
Lemma lem6884187 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : (term876 _125911 P k) = False.
Proof. exact (prop_ext (fun h4 : term876 _125911 P k => @lem6884186 _125911 P k h1 h2 h3) (fun h4 : False => @lem6883876 _125911 P k h3)). Qed.
Lemma lem6884188 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : False.
Proof. exact (EQ_MP (@lem6884187 _125911 P k h1 h2 h3) (@lem6883876 _125911 P k h3)). Qed.
Lemma lem6884189 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : (@FINITE _125911 k) = False.
Proof. exact (prop_ext (fun h4 : @FINITE _125911 k => @lem6884188 _125911 P k h1 h2 h3) (fun h4 : False => @lem6883870 _125911 k h2)). Qed.
Lemma lem6884190 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : False.
Proof. exact (EQ_MP (@lem6884189 _125911 P k h1 h2 h3) (@lem6883870 _125911 k h2)). Qed.
Lemma lem6884191 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : (term876 _125911 P k) = False.
Proof. exact (prop_ext (fun h4 : term876 _125911 P k => @lem6884190 _125911 P k h1 h2 h3) (fun h4 : False => @lem6883804 _125911 P k h3)). Qed.
Lemma lem6884192 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) (h3 : term876 _125911 P k) : False.
Proof. exact (EQ_MP (@lem6884191 _125911 P k h1 h2 h3) (@lem6883804 _125911 P k h3)). Qed.
Lemma lem6884193 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) : term875 _125911 P k.
Proof. exact (fun h0 : term876 _125911 P k => @lem6884192 _125911 P k h1 h2 h0). Qed.
Lemma lem6884194 {_125911 : Type'} (P : type686 _125911) (k : _125911 -> Prop) (h1 : term873 _125911 P) (h2 : @FINITE _125911 k) : P k.
Proof. exact (EQ_MP (@lem6883803 _125911 P k) (@lem6884193 _125911 P k h1 h2)). Qed.
Lemma lem6884195 {_125911 : Type'} (k : _125911 -> Prop) (P : type686 _125911) (h1 : term873 _125911 P) : term866 _125911 P k.
Proof. exact (fun h0 : @FINITE _125911 k => @lem6884194 _125911 P k h1 h0). Qed.
Lemma lem6884200 {_125911 : Type'} (P : type686 _125911) (h1 : term873 _125911 P) : term868 _125911 P.
Proof. exact (fun k : _125911 -> Prop => @lem6884195 _125911 k P h1). Qed.
Lemma lem6884201 {_125911 : Type'} (P : type686 _125911) : term855 _125911 P.
Proof. exact (fun h0 : term873 _125911 P => @lem6884200 _125911 P h0). Qed.
Lemma lem6884206 {_125911 : Type'} : term865 _125911.
Proof. exact (fun P : type686 _125911 => @lem6884201 _125911 P). Qed.
Lemma lem6884207 {_125911 : Type'} : term864 _125911.
Proof. exact (EQ_MP (@lem6883797 _125911) (@lem6884206 _125911)). Qed.
Lemma lem6884208 {_125911 : Type'} (P : type686 _125911) : term923 _125911 P.
Proof. exact (@lem6884207 _125911 P). Qed.
Lemma lem6884209 {_125911 : Type'} (P : type686 _125911) : (term923 _125911 P) = (term856 _125911 P).
Proof. exact (eq_refl (term923 _125911 P)). Qed.
Lemma lem6884210 {_125911 : Type'} (P : type686 _125911) : term856 _125911 P.
Proof. exact (EQ_MP (@lem6884209 _125911 P) (@lem6884208 _125911 P)). Qed.
Lemma lem6884212 {_125911 : Type'} (P : type686 _125911) : term856 _125911 P.
Proof. exact (@lem6883690 _125911 P (@lem6884210 _125911 P)). Qed.
Lemma lem6884213 {_125911 : Type'} (P : type686 _125911) (h1 : term857 _125911 P) : False.
Proof. exact (@lem6884212 _125911 P (@lem6883674 _125911 P h1)). Qed.
Lemma lem6884214 {_125911 : Type'} (P : type686 _125911) (h1 : term857 _125911 P) : (term857 _125911 P) = False.
Proof. exact (prop_ext (fun h2 : term857 _125911 P => @lem6884213 _125911 P h1) (fun h2 : False => @lem6883674 _125911 P h1)). Qed.
Lemma lem6884215 {_125911 : Type'} (P : type686 _125911) (h1 : term857 _125911 P) : False.
Proof. exact (EQ_MP (@lem6884214 _125911 P h1) (@lem6883674 _125911 P h1)). Qed.
Lemma lem6884216 {_125911 : Type'} (P : type686 _125911) : term856 _125911 P.
Proof. exact (fun h0 : term857 _125911 P => @lem6884215 _125911 P h0). Qed.
Lemma lem6884217 {_125911 : Type'} (P : type686 _125911) : term855 _125911 P.
Proof. exact (EQ_MP (@lem6883673 _125911 P) (@lem6884216 _125911 P)). Qed.
Lemma lem6884218 {_125911 : Type'} (P : type686 _125911) (h1 : term855 _125911 P) : term855 _125911 P.
Proof. exact (h1). Qed.
Lemma lem6884219 {_125911 : Type'} (P : type686 _125911) (h1 : term873 _125911 P) : term873 _125911 P.
Proof. exact (h1). Qed.
Lemma lem6884220 {_125911 : Type'} (P : type686 _125911) (h1 : term873 _125911 P) (h2 : term855 _125911 P) : term868 _125911 P.
Proof. exact (@lem6884218 _125911 P h2 (@lem6884219 _125911 P h1)). Qed.
Lemma lem6884221 {_125911 : Type'} (P : type686 _125911) (h1 : term873 _125911 P) : term924 _125911 P.
Proof. exact (fun h0 : term855 _125911 P => @lem6884220 _125911 P h1 h0). Qed.
Lemma lem6884222 {_125911 : Type'} (P : type686 _125911) (h1 : term855 _125911 P) : term855 _125911 P.
Proof. exact (h1). Qed.
Lemma lem6884223 {_125911 : Type'} (P : type686 _125911) (h1 : term873 _125911 P) (h2 : term855 _125911 P) : term868 _125911 P.
Proof. exact (@lem6884221 _125911 P h1 (@lem6884222 _125911 P h2)). Qed.
Lemma lem6884224 {_125911 : Type'} (P : type686 _125911) (h1 : term855 _125911 P) : term855 _125911 P.
Proof. exact (fun h0 : term873 _125911 P => @lem6884223 _125911 P h0 h1). Qed.
Lemma lem6884225 {_125911 : Type'} (P : type686 _125911) : term925 _125911 P.
Proof. exact (fun h0 : term855 _125911 P => @lem6884224 _125911 P h0). Qed.
Lemma lem6884238 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6884239 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) : (term926 _125947 x p y z) = (term927 _125947 x p y z).
Proof. exact (@lem6884238 (term926 _125947 x p y z)). Qed.
Lemma lem6884240 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) : (term927 _125947 x p y z) = (term926 _125947 x p y z).
Proof. exact (SYM (@lem6884239 _125947 x p y z)). Qed.
Lemma lem6884241 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term928 _125947 x p y z) : term928 _125947 x p y z.
Proof. exact (h1). Qed.
Lemma lem6884244 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term927 _125947 x p y z) : term927 _125947 x p y z.
Proof. exact (h1). Qed.
Lemma lem6884245 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) : term929 _125947 x p y z.
Proof. exact (fun h0 : term927 _125947 x p y z => @lem6884244 _125947 x p y z h0). Qed.
Lemma lem6884246 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term929 _125947 x p y z) : term929 _125947 x p y z.
Proof. exact (h1). Qed.
Lemma lem6884247 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term927 _125947 x p y z) : term927 _125947 x p y z.
Proof. exact (h1). Qed.
Lemma lem6884248 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term927 _125947 x p y z) (h2 : term929 _125947 x p y z) : term927 _125947 x p y z.
Proof. exact (@lem6884246 _125947 x p y z h2 (@lem6884247 _125947 x p y z h1)). Qed.
Lemma lem6884249 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term927 _125947 x p y z) : term930 _125947 x p y z.
Proof. exact (fun h0 : term929 _125947 x p y z => @lem6884248 _125947 x p y z h1 h0). Qed.
Lemma lem6884250 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term929 _125947 x p y z) : term929 _125947 x p y z.
Proof. exact (h1). Qed.
Lemma lem6884251 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term927 _125947 x p y z) (h2 : term929 _125947 x p y z) : term927 _125947 x p y z.
Proof. exact (@lem6884249 _125947 x p y z h1 (@lem6884250 _125947 x p y z h2)). Qed.
Lemma lem6884252 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term929 _125947 x p y z) : term929 _125947 x p y z.
Proof. exact (fun h0 : term927 _125947 x p y z => @lem6884251 _125947 x p y z h0 h1). Qed.
Lemma lem6884253 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) : term931 _125947 x p y z.
Proof. exact (fun h0 : term929 _125947 x p y z => @lem6884252 _125947 x p y z h0). Qed.
Lemma lem6884256 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) : term929 _125947 x p y z.
Proof. exact (@lem6884253 _125947 x p y z (@lem6884245 _125947 x p y z)). Qed.
Lemma lem6884257 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) : term929 _125947 x p y z.
Proof. exact (@lem6884256 _125947 x p y z). Qed.
Lemma lem6884275 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6884276 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) : (term927 _125947 x p y z) = (term932 _125947 x p y z).
Proof. exact (@lem6884275 (term928 _125947 x p y z)). Qed.
Lemma lem6884278 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6884279 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) : (term932 _125947 x p y z) = (term926 _125947 x p y z).
Proof. exact (@lem6884278 (term926 _125947 x p y z)). Qed.
Lemma lem6884282 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) : (term927 _125947 x p y z) = (term926 _125947 x p y z).
Proof. exact (TRANS (@lem6884276 _125947 x p y z) (@lem6884279 _125947 x p y z)). Qed.
Lemma lem6884285 {_125947 : Type'} (p : Prop) (y : _125947) (z : _125947) : (term933 _125947 p y z) = (term934 _125947 p y z).
Proof. exact (fun_ext (fun x : _125947 => @lem6884282 _125947 x p y z)). Qed.
Lemma lem6884286 {_125947 : Type'} : (@all _125947) = (@all _125947).
Proof. exact (eq_refl (@all _125947)). Qed.
Lemma lem6884287 {_125947 : Type'} (p : Prop) (y : _125947) (z : _125947) : (term935 _125947 p y z) = (term936 _125947 p y z).
Proof. exact (MK_COMB (@lem6884286 _125947) (@lem6884285 _125947 p y z)). Qed.
Lemma lem6884292 {_125947 : Type'} (y : _125947) (z : _125947) : (term937 _125947 y z) = (term938 _125947 y z).
Proof. exact (fun_ext (fun p : Prop => @lem6884287 _125947 p y z)). Qed.
Lemma lem6884293 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem6884294 {_125947 : Type'} (y : _125947) (z : _125947) : (term939 _125947 y z) = (term940 _125947 y z).
Proof. exact (MK_COMB (@lem6884293) (@lem6884292 _125947 y z)). Qed.
Lemma lem6884299 {_125947 : Type'} (z : _125947) : (term941 _125947 z) = (term942 _125947 z).
Proof. exact (fun_ext (fun y : _125947 => @lem6884294 _125947 y z)). Qed.
Lemma lem6884300 {_125947 : Type'} : (@all _125947) = (@all _125947).
Proof. exact (eq_refl (@all _125947)). Qed.
Lemma lem6884301 {_125947 : Type'} (z : _125947) : (term943 _125947 z) = (term944 _125947 z).
Proof. exact (MK_COMB (@lem6884300 _125947) (@lem6884299 _125947 z)). Qed.
Lemma lem6884306 {_125947 : Type'} : (term945 _125947) = (term946 _125947).
Proof. exact (fun_ext (fun z : _125947 => @lem6884301 _125947 z)). Qed.
Lemma lem6884307 {_125947 : Type'} : (@all _125947) = (@all _125947).
Proof. exact (eq_refl (@all _125947)). Qed.
Lemma lem6884316 {_125947 : Type'} : (term947 _125947) = (term948 _125947).
Proof. exact (MK_COMB (@lem6884307 _125947) (@lem6884306 _125947)). Qed.
Lemma lem6884320 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem6884321 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6884322 (p : Prop) (h1 : p = False) : (imp p) = (imp False).
Proof. exact (MK_COMB (@lem6884321) (@lem6884320 p h1)). Qed.
Lemma lem6884325 {_125947 : Type'} (x : _125947) (y : _125947) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem6884326 {_125947 : Type'} (x : _125947) (y : _125947) (p : Prop) (h1 : p = False) : (term949 _125947 p x y) = (term950 _125947 x y).
Proof. exact (MK_COMB (@lem6884322 p h1) (@lem6884325 _125947 x y)). Qed.
Lemma lem6884328 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem6884329 {_125947 : Type'} (x : _125947) (y : _125947) : (term950 _125947 x y) = True.
Proof. exact (@lem6884328 (x = y)). Qed.
Lemma lem6884330 {_125947 : Type'} (x : _125947) (y : _125947) (p : Prop) (h1 : p = False) : (term949 _125947 p x y) = True.
Proof. exact (TRANS (@lem6884326 _125947 x y p h1) (@lem6884329 _125947 x y)). Qed.
Lemma lem6884331 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6884332 {_125947 : Type'} (x : _125947) (y : _125947) (p : Prop) (h1 : p = False) : (term951 _125947 p x y) = (imp True).
Proof. exact (MK_COMB (@lem6884331) (@lem6884330 _125947 x y p h1)). Qed.
Lemma lem6884334 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem6884335 {_125947 : Type'} : (@COND _125947) = (@COND _125947).
Proof. exact (eq_refl (@COND _125947)). Qed.
Lemma lem6884336 {_125947 : Type'} (p : Prop) (h1 : p = False) : (@COND _125947 p) = (@COND _125947 False).
Proof. exact (MK_COMB (@lem6884335 _125947) (@lem6884334 p h1)). Qed.
Lemma lem6884337 {_125947 : Type'} (x : _125947) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6884338 {_125947 : Type'} (x : _125947) (p : Prop) (h1 : p = False) : (@COND _125947 p x) = (@COND _125947 False x).
Proof. exact (MK_COMB (@lem6884336 _125947 p h1) (@lem6884337 _125947 x)). Qed.
Lemma lem6884339 {_125947 : Type'} (z : _125947) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6884340 {_125947 : Type'} (x : _125947) (z : _125947) (p : Prop) (h1 : p = False) : (@COND _125947 p x z) = (@COND _125947 False x z).
Proof. exact (MK_COMB (@lem6884338 _125947 x p h1) (@lem6884339 _125947 z)). Qed.
Lemma lem6884342 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6884343 {_125947 : Type'} (t1 : _125947) (t2 : _125947) : (@COND _125947 False t1 t2) = t2.
Proof. exact (@lem6884342 _125947 t1 t2). Qed.
Lemma lem6884344 {_125947 : Type'} (x : _125947) (z : _125947) : (@COND _125947 False x z) = z.
Proof. exact (@lem6884343 _125947 x z). Qed.
Lemma lem6884345 {_125947 : Type'} (x : _125947) (z : _125947) (p : Prop) (h1 : p = False) : (@COND _125947 p x z) = z.
Proof. exact (TRANS (@lem6884340 _125947 x z p h1) (@lem6884344 _125947 x z)). Qed.
Lemma lem6884346 {_125947 : Type'} : (@eq _125947) = (@eq _125947).
Proof. exact (eq_refl (@eq _125947)). Qed.
Lemma lem6884347 {_125947 : Type'} (x : _125947) (z : _125947) (p : Prop) (h1 : p = False) : (term952 _125947 p x z) = (@eq _125947 z).
Proof. exact (MK_COMB (@lem6884346 _125947) (@lem6884345 _125947 x z p h1)). Qed.
Lemma lem6884349 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem6884350 {_125947 : Type'} : (@COND _125947) = (@COND _125947).
Proof. exact (eq_refl (@COND _125947)). Qed.
Lemma lem6884351 {_125947 : Type'} (p : Prop) (h1 : p = False) : (@COND _125947 p) = (@COND _125947 False).
Proof. exact (MK_COMB (@lem6884350 _125947) (@lem6884349 p h1)). Qed.
Lemma lem6884352 {_125947 : Type'} (y : _125947) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6884353 {_125947 : Type'} (y : _125947) (p : Prop) (h1 : p = False) : (@COND _125947 p y) = (@COND _125947 False y).
Proof. exact (MK_COMB (@lem6884351 _125947 p h1) (@lem6884352 _125947 y)). Qed.
Lemma lem6884354 {_125947 : Type'} (z : _125947) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6884355 {_125947 : Type'} (y : _125947) (z : _125947) (p : Prop) (h1 : p = False) : (@COND _125947 p y z) = (@COND _125947 False y z).
Proof. exact (MK_COMB (@lem6884353 _125947 y p h1) (@lem6884354 _125947 z)). Qed.
Lemma lem6884357 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6884358 {_125947 : Type'} (t1 : _125947) (t2 : _125947) : (@COND _125947 False t1 t2) = t2.
Proof. exact (@lem6884357 _125947 t1 t2). Qed.
Lemma lem6884359 {_125947 : Type'} (y : _125947) (z : _125947) : (@COND _125947 False y z) = z.
Proof. exact (@lem6884358 _125947 y z). Qed.
Lemma lem6884360 {_125947 : Type'} (y : _125947) (z : _125947) (p : Prop) (h1 : p = False) : (@COND _125947 p y z) = z.
Proof. exact (TRANS (@lem6884355 _125947 y z p h1) (@lem6884359 _125947 y z)). Qed.
Lemma lem6884361 {_125947 : Type'} (x : _125947) (y : _125947) (z : _125947) (p : Prop) (h1 : p = False) : ((@COND _125947 p x z) = (@COND _125947 p y z)) = (z = z).
Proof. exact (MK_COMB (@lem6884347 _125947 x z p h1) (@lem6884360 _125947 y z p h1)). Qed.
Lemma lem6884363 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6884364 {_125947 : Type'} (x : _125947) : (x = x) = True.
Proof. exact (@lem6884363 _125947 x). Qed.
Lemma lem6884365 {_125947 : Type'} (z : _125947) : (z = z) = True.
Proof. exact (@lem6884364 _125947 z). Qed.
Lemma lem6884366 {_125947 : Type'} (x : _125947) (y : _125947) (z : _125947) (p : Prop) (h1 : p = False) : ((@COND _125947 p x z) = (@COND _125947 p y z)) = True.
Proof. exact (TRANS (@lem6884361 _125947 x y z p h1) (@lem6884365 _125947 z)). Qed.
Lemma lem6884367 {_125947 : Type'} (x : _125947) (y : _125947) (z : _125947) (p : Prop) (h1 : p = False) : (term926 _125947 x p y z) = (True -> True).
Proof. exact (MK_COMB (@lem6884332 _125947 x y p h1) (@lem6884366 _125947 x y z p h1)). Qed.
Lemma lem6884369 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem6884370 : (True -> True) = True.
Proof. exact (@lem6884369 True). Qed.
Lemma lem6884371 {_125947 : Type'} (x : _125947) (y : _125947) (z : _125947) (p : Prop) (h1 : p = False) : (term926 _125947 x p y z) = True.
Proof. exact (TRANS (@lem6884367 _125947 x y z p h1) (@lem6884370)). Qed.
Lemma lem6884372 {_125947 : Type'} (y : _125947) (z : _125947) (p : Prop) (h1 : p = False) : (term934 _125947 p y z) = (term953 _125947).
Proof. exact (fun_ext (fun x : _125947 => @lem6884371 _125947 x y z p h1)). Qed.
Lemma lem6884373 {_125947 : Type'} : (@all _125947) = (@all _125947).
Proof. exact (eq_refl (@all _125947)). Qed.
Lemma lem6884374 {_125947 : Type'} (y : _125947) (z : _125947) (p : Prop) (h1 : p = False) : (term936 _125947 p y z) = (term954 _125947).
Proof. exact (MK_COMB (@lem6884373 _125947) (@lem6884372 _125947 y z p h1)). Qed.
Lemma lem6884376 {A : Type'} (t : Prop) : (term955 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6884377 {_125947 : Type'} (t : Prop) : (term955 _125947 t) = t.
Proof. exact (@lem6884376 _125947 t). Qed.
Lemma lem6884378 {_125947 : Type'} : (term954 _125947) = True.
Proof. exact (@lem6884377 _125947 True). Qed.
Lemma lem6884379 {_125947 : Type'} (y : _125947) (z : _125947) (p : Prop) (h1 : p = False) : (term936 _125947 p y z) = True.
Proof. exact (TRANS (@lem6884374 _125947 y z p h1) (@lem6884378 _125947)). Qed.
Lemma lem6884380 {_125947 : Type'} (p : Prop) (y : _125947) (z : _125947) : term956 _125947 p y z.
Proof. exact (fun h0 : p = False => @lem6884379 _125947 y z p h0). Qed.
Lemma lem6884382 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem6884383 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6884384 (p : Prop) (h1 : p = True) : (imp p) = (imp True).
Proof. exact (MK_COMB (@lem6884383) (@lem6884382 p h1)). Qed.
Lemma lem6884387 {_125947 : Type'} (x : _125947) (y : _125947) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem6884388 {_125947 : Type'} (x : _125947) (y : _125947) (p : Prop) (h1 : p = True) : (term949 _125947 p x y) = (term957 _125947 x y).
Proof. exact (MK_COMB (@lem6884384 p h1) (@lem6884387 _125947 x y)). Qed.
Lemma lem6884390 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem6884391 {_125947 : Type'} (x : _125947) (y : _125947) : (term957 _125947 x y) = (x = y).
Proof. exact (@lem6884390 (x = y)). Qed.
Lemma lem6884394 {_125947 : Type'} (x : _125947) (y : _125947) (p : Prop) (h1 : p = True) : (term949 _125947 p x y) = (x = y).
Proof. exact (TRANS (@lem6884388 _125947 x y p h1) (@lem6884391 _125947 x y)). Qed.
Lemma lem6884395 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6884396 {_125947 : Type'} (x : _125947) (y : _125947) (p : Prop) (h1 : p = True) : (term951 _125947 p x y) = (term958 _125947 x y).
Proof. exact (MK_COMB (@lem6884395) (@lem6884394 _125947 x y p h1)). Qed.
Lemma lem6884398 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem6884399 {_125947 : Type'} : (@COND _125947) = (@COND _125947).
Proof. exact (eq_refl (@COND _125947)). Qed.
Lemma lem6884400 {_125947 : Type'} (p : Prop) (h1 : p = True) : (@COND _125947 p) = (@COND _125947 True).
Proof. exact (MK_COMB (@lem6884399 _125947) (@lem6884398 p h1)). Qed.
Lemma lem6884401 {_125947 : Type'} (x : _125947) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6884402 {_125947 : Type'} (x : _125947) (p : Prop) (h1 : p = True) : (@COND _125947 p x) = (@COND _125947 True x).
Proof. exact (MK_COMB (@lem6884400 _125947 p h1) (@lem6884401 _125947 x)). Qed.
Lemma lem6884403 {_125947 : Type'} (z : _125947) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6884404 {_125947 : Type'} (x : _125947) (z : _125947) (p : Prop) (h1 : p = True) : (@COND _125947 p x z) = (@COND _125947 True x z).
Proof. exact (MK_COMB (@lem6884402 _125947 x p h1) (@lem6884403 _125947 z)). Qed.
Lemma lem6884406 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem6884407 {_125947 : Type'} (t2 : _125947) (t1 : _125947) : (@COND _125947 True t1 t2) = t1.
Proof. exact (@lem6884406 _125947 t2 t1). Qed.
Lemma lem6884408 {_125947 : Type'} (z : _125947) (x : _125947) : (@COND _125947 True x z) = x.
Proof. exact (@lem6884407 _125947 z x). Qed.
Lemma lem6884409 {_125947 : Type'} (z : _125947) (x : _125947) (p : Prop) (h1 : p = True) : (@COND _125947 p x z) = x.
Proof. exact (TRANS (@lem6884404 _125947 x z p h1) (@lem6884408 _125947 z x)). Qed.
Lemma lem6884410 {_125947 : Type'} : (@eq _125947) = (@eq _125947).
Proof. exact (eq_refl (@eq _125947)). Qed.
Lemma lem6884411 {_125947 : Type'} (z : _125947) (x : _125947) (p : Prop) (h1 : p = True) : (term952 _125947 p x z) = (@eq _125947 x).
Proof. exact (MK_COMB (@lem6884410 _125947) (@lem6884409 _125947 z x p h1)). Qed.
Lemma lem6884413 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem6884414 {_125947 : Type'} : (@COND _125947) = (@COND _125947).
Proof. exact (eq_refl (@COND _125947)). Qed.
Lemma lem6884415 {_125947 : Type'} (p : Prop) (h1 : p = True) : (@COND _125947 p) = (@COND _125947 True).
Proof. exact (MK_COMB (@lem6884414 _125947) (@lem6884413 p h1)). Qed.
Lemma lem6884416 {_125947 : Type'} (y : _125947) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6884417 {_125947 : Type'} (y : _125947) (p : Prop) (h1 : p = True) : (@COND _125947 p y) = (@COND _125947 True y).
Proof. exact (MK_COMB (@lem6884415 _125947 p h1) (@lem6884416 _125947 y)). Qed.
Lemma lem6884418 {_125947 : Type'} (z : _125947) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem6884419 {_125947 : Type'} (y : _125947) (z : _125947) (p : Prop) (h1 : p = True) : (@COND _125947 p y z) = (@COND _125947 True y z).
Proof. exact (MK_COMB (@lem6884417 _125947 y p h1) (@lem6884418 _125947 z)). Qed.
Lemma lem6884421 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem6884422 {_125947 : Type'} (t2 : _125947) (t1 : _125947) : (@COND _125947 True t1 t2) = t1.
Proof. exact (@lem6884421 _125947 t2 t1). Qed.
Lemma lem6884423 {_125947 : Type'} (z : _125947) (y : _125947) : (@COND _125947 True y z) = y.
Proof. exact (@lem6884422 _125947 z y). Qed.
Lemma lem6884424 {_125947 : Type'} (z : _125947) (y : _125947) (p : Prop) (h1 : p = True) : (@COND _125947 p y z) = y.
Proof. exact (TRANS (@lem6884419 _125947 y z p h1) (@lem6884423 _125947 z y)). Qed.
Lemma lem6884425 {_125947 : Type'} (z : _125947) (x : _125947) (y : _125947) (p : Prop) (h1 : p = True) : ((@COND _125947 p x z) = (@COND _125947 p y z)) = (x = y).
Proof. exact (MK_COMB (@lem6884411 _125947 z x p h1) (@lem6884424 _125947 z y p h1)). Qed.
Lemma lem6884428 {_125947 : Type'} (z : _125947) (x : _125947) (y : _125947) (p : Prop) (h1 : p = True) : (term926 _125947 x p y z) = (term959 _125947 x y).
Proof. exact (MK_COMB (@lem6884396 _125947 x y p h1) (@lem6884425 _125947 z x y p h1)). Qed.
Lemma lem6884432 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem6884433 {_125947 : Type'} (x : _125947) (y : _125947) : (term959 _125947 x y) = True.
Proof. exact (@lem6884432 (x = y)). Qed.
Lemma lem6884434 {_125947 : Type'} (x : _125947) (y : _125947) (z : _125947) (p : Prop) (h1 : p = True) : (term926 _125947 x p y z) = True.
Proof. exact (TRANS (@lem6884428 _125947 z x y p h1) (@lem6884433 _125947 x y)). Qed.
Lemma lem6884435 {_125947 : Type'} (y : _125947) (z : _125947) (p : Prop) (h1 : p = True) : (term934 _125947 p y z) = (term953 _125947).
Proof. exact (fun_ext (fun x : _125947 => @lem6884434 _125947 x y z p h1)). Qed.
Lemma lem6884436 {_125947 : Type'} : (@all _125947) = (@all _125947).
Proof. exact (eq_refl (@all _125947)). Qed.
Lemma lem6884437 {_125947 : Type'} (y : _125947) (z : _125947) (p : Prop) (h1 : p = True) : (term936 _125947 p y z) = (term954 _125947).
Proof. exact (MK_COMB (@lem6884436 _125947) (@lem6884435 _125947 y z p h1)). Qed.
Lemma lem6884439 {A : Type'} (t : Prop) : (term955 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem6884440 {_125947 : Type'} (t : Prop) : (term955 _125947 t) = t.
Proof. exact (@lem6884439 _125947 t). Qed.
Lemma lem6884441 {_125947 : Type'} : (term954 _125947) = True.
Proof. exact (@lem6884440 _125947 True). Qed.
Lemma lem6884442 {_125947 : Type'} (y : _125947) (z : _125947) (p : Prop) (h1 : p = True) : (term936 _125947 p y z) = True.
Proof. exact (TRANS (@lem6884437 _125947 y z p h1) (@lem6884441 _125947)). Qed.
Lemma lem6884443 {_125947 : Type'} (p : Prop) (y : _125947) (z : _125947) : term960 _125947 p y z.
Proof. exact (fun h0 : p = True => @lem6884442 _125947 y z p h0). Qed.
Lemma lem6884444 {_125947 : Type'} (p : Prop) (y : _125947) (z : _125947) : term961 _125947 p y z.
Proof. exact (conj (@lem6884380 _125947 p y z) (@lem6884443 _125947 p y z)). Qed.
Lemma lem6884446 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term962 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem6884447 {_125947 : Type'} (y : _125947) (z : _125947) (p : Prop) : term963 _125947 y z p.
Proof. exact (@lem6884446 (term936 _125947 p y z) True p True). Qed.
Lemma lem6884448 {_125947 : Type'} (y : _125947) (z : _125947) (p : Prop) : (term936 _125947 p y z) = (term964 p).
Proof. exact (@lem6884447 _125947 y z p (@lem6884444 _125947 p y z)). Qed.
Lemma lem6884450 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem6884451 (p : Prop) : (p \/ True) = True.
Proof. exact (@lem6884450 p). Qed.
Lemma lem6884453 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem6884454 (p : Prop) : (term965 p) = True.
Proof. exact (@lem6884453 (~ p)). Qed.
Lemma lem6884455 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6884456 (p : Prop) : (term966 p) = (and True).
Proof. exact (MK_COMB (@lem6884455) (@lem6884454 p)). Qed.
Lemma lem6884457 (p : Prop) : (term964 p) = (True /\ True).
Proof. exact (MK_COMB (@lem6884456 p) (@lem6884451 p)). Qed.
Lemma lem6884459 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6884460 : (True /\ True) = True.
Proof. exact (@lem6884459 True). Qed.
Lemma lem6884461 (p : Prop) : (term964 p) = True.
Proof. exact (TRANS (@lem6884457 p) (@lem6884460)). Qed.
Lemma lem6884466 {_125947 : Type'} (p : Prop) (y : _125947) (z : _125947) : (term936 _125947 p y z) = True.
Proof. exact (TRANS (@lem6884448 _125947 y z p) (@lem6884461 p)). Qed.
Lemma lem6884467 {_125947 : Type'} (y : _125947) (z : _125947) : (term938 _125947 y z) = term967.
Proof. exact (fun_ext (fun p : Prop => @lem6884466 _125947 p y z)). Qed.
Lemma lem6884468 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem6884469 {_125947 : Type'} (y : _125947) (z : _125947) : (term940 _125947 y z) = term968.
Proof. exact (MK_COMB (@lem6884468) (@lem6884467 _125947 y z)). Qed.
Lemma lem6884470 {_125947 : Type'} (z : _125947) : (term942 _125947 z) = (term969 _125947).
Proof. exact (fun_ext (fun y : _125947 => @lem6884469 _125947 y z)). Qed.
Lemma lem6884471 {_125947 : Type'} : (@all _125947) = (@all _125947).
Proof. exact (eq_refl (@all _125947)). Qed.
Lemma lem6884472 {_125947 : Type'} (z : _125947) : (term944 _125947 z) = (term970 _125947).
Proof. exact (MK_COMB (@lem6884471 _125947) (@lem6884470 _125947 z)). Qed.
Lemma lem6884473 {_125947 : Type'} : (term946 _125947) = (term971 _125947).
Proof. exact (fun_ext (fun z : _125947 => @lem6884472 _125947 z)). Qed.
Lemma lem6884474 {_125947 : Type'} : (@all _125947) = (@all _125947).
Proof. exact (eq_refl (@all _125947)). Qed.
Lemma lem6884475 {_125947 : Type'} : (term948 _125947) = (term972 _125947).
Proof. exact (MK_COMB (@lem6884474 _125947) (@lem6884473 _125947)). Qed.
Lemma lem6884476 {_125947 : Type'} : (term947 _125947) = (term972 _125947).
Proof. exact (TRANS (@lem6884316 _125947) (@lem6884475 _125947)). Qed.
Lemma lem6884478 {A : Type'} (t : Prop) : (term955 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem6884479 {_125947 : Type'} (t : Prop) : (term955 _125947 t) = t.
Proof. exact (@lem6884478 _125947 t). Qed.
Lemma lem6884480 {_125947 : Type'} : (term972 _125947) = (term970 _125947).
Proof. exact (@lem6884479 _125947 (term970 _125947)). Qed.
Lemma lem6884482 {A : Type'} (t : Prop) : (term955 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem6884483 {_125947 : Type'} (t : Prop) : (term955 _125947 t) = t.
Proof. exact (@lem6884482 _125947 t). Qed.
Lemma lem6884484 {_125947 : Type'} : (term970 _125947) = term968.
Proof. exact (@lem6884483 _125947 term968). Qed.
Lemma lem6884486 {A : Type'} (t : Prop) : (term955 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem6884487 (t : Prop) : (term973 t) = t.
Proof. exact (@lem6884486 Prop t). Qed.
Lemma lem6884488 : term968 = True.
Proof. exact (@lem6884487 True). Qed.
Lemma lem6884489 {_125947 : Type'} : (term970 _125947) = True.
Proof. exact (TRANS (@lem6884484 _125947) (@lem6884488)). Qed.
Lemma lem6884490 {_125947 : Type'} : (term972 _125947) = True.
Proof. exact (TRANS (@lem6884480 _125947) (@lem6884489 _125947)). Qed.
Lemma lem6884491 {_125947 : Type'} : (term947 _125947) = True.
Proof. exact (TRANS (@lem6884476 _125947) (@lem6884490 _125947)). Qed.
Lemma lem6884492 {_125947 : Type'} : True = (term947 _125947).
Proof. exact (SYM (@lem6884491 _125947)). Qed.
Lemma lem6884493 {_125947 : Type'} : term947 _125947.
Proof. exact (EQ_MP (@lem6884492 _125947) (@lem0)). Qed.
Lemma lem6884494 {_125947 : Type'} (z : _125947) : term974 _125947 z.
Proof. exact (@lem6884493 _125947 z). Qed.
Lemma lem6884495 {_125947 : Type'} (z : _125947) : (term974 _125947 z) = (term943 _125947 z).
Proof. exact (eq_refl (term974 _125947 z)). Qed.
Lemma lem6884496 {_125947 : Type'} (z : _125947) : term943 _125947 z.
Proof. exact (EQ_MP (@lem6884495 _125947 z) (@lem6884494 _125947 z)). Qed.
Lemma lem6884497 {_125947 : Type'} (z : _125947) (y : _125947) : term975 _125947 z y.
Proof. exact (@lem6884496 _125947 z y). Qed.
Lemma lem6884498 {_125947 : Type'} (y : _125947) (z : _125947) : (term975 _125947 z y) = (term939 _125947 y z).
Proof. exact (eq_refl (term975 _125947 z y)). Qed.
Lemma lem6884499 {_125947 : Type'} (y : _125947) (z : _125947) : term939 _125947 y z.
Proof. exact (EQ_MP (@lem6884498 _125947 y z) (@lem6884497 _125947 z y)). Qed.
Lemma lem6884500 {_125947 : Type'} (y : _125947) (z : _125947) (p : Prop) : term976 _125947 y z p.
Proof. exact (@lem6884499 _125947 y z p). Qed.
Lemma lem6884501 {_125947 : Type'} (p : Prop) (y : _125947) (z : _125947) : (term976 _125947 y z p) = (term935 _125947 p y z).
Proof. exact (eq_refl (term976 _125947 y z p)). Qed.
Lemma lem6884502 {_125947 : Type'} (p : Prop) (y : _125947) (z : _125947) : term935 _125947 p y z.
Proof. exact (EQ_MP (@lem6884501 _125947 p y z) (@lem6884500 _125947 y z p)). Qed.
Lemma lem6884503 {_125947 : Type'} (p : Prop) (y : _125947) (z : _125947) (x : _125947) : term977 _125947 p y z x.
Proof. exact (@lem6884502 _125947 p y z x). Qed.
Lemma lem6884504 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) : (term977 _125947 p y z x) = (term927 _125947 x p y z).
Proof. exact (eq_refl (term977 _125947 p y z x)). Qed.
Lemma lem6884505 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) : term927 _125947 x p y z.
Proof. exact (EQ_MP (@lem6884504 _125947 x p y z) (@lem6884503 _125947 p y z x)). Qed.
Lemma lem6884507 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) : term927 _125947 x p y z.
Proof. exact (@lem6884257 _125947 x p y z (@lem6884505 _125947 x p y z)). Qed.
Lemma lem6884508 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term928 _125947 x p y z) : False.
Proof. exact (@lem6884507 _125947 x p y z (@lem6884241 _125947 x p y z h1)). Qed.
Lemma lem6884509 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term928 _125947 x p y z) : (term928 _125947 x p y z) = False.
Proof. exact (prop_ext (fun h2 : term928 _125947 x p y z => @lem6884508 _125947 x p y z h1) (fun h2 : False => @lem6884241 _125947 x p y z h1)). Qed.
Lemma lem6884510 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term928 _125947 x p y z) : False.
Proof. exact (EQ_MP (@lem6884509 _125947 x p y z h1) (@lem6884241 _125947 x p y z h1)). Qed.
Lemma lem6884511 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) : term927 _125947 x p y z.
Proof. exact (fun h0 : term928 _125947 x p y z => @lem6884510 _125947 x p y z h0). Qed.
Lemma lem6884512 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) : term926 _125947 x p y z.
Proof. exact (EQ_MP (@lem6884240 _125947 x p y z) (@lem6884511 _125947 x p y z)). Qed.
Lemma lem6884513 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term926 _125947 x p y z) : term926 _125947 x p y z.
Proof. exact (h1). Qed.
Lemma lem6884514 {_125947 : Type'} (p : Prop) (x : _125947) (y : _125947) (h1 : term949 _125947 p x y) : term949 _125947 p x y.
Proof. exact (h1). Qed.
Lemma lem6884515 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term949 _125947 p x y) (h2 : term926 _125947 x p y z) : (@COND _125947 p x z) = (@COND _125947 p y z).
Proof. exact (@lem6884513 _125947 x p y z h2 (@lem6884514 _125947 p x y h1)). Qed.
Lemma lem6884516 {_125947 : Type'} (z : _125947) (p : Prop) (x : _125947) (y : _125947) (h1 : term949 _125947 p x y) : term978 _125947 x p y z.
Proof. exact (fun h0 : term926 _125947 x p y z => @lem6884515 _125947 x p y z h1 h0). Qed.
Lemma lem6884517 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term926 _125947 x p y z) : term926 _125947 x p y z.
Proof. exact (h1). Qed.
Lemma lem6884518 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term949 _125947 p x y) (h2 : term926 _125947 x p y z) : (@COND _125947 p x z) = (@COND _125947 p y z).
Proof. exact (@lem6884516 _125947 z p x y h1 (@lem6884517 _125947 x p y z h2)). Qed.
Lemma lem6884519 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) (h1 : term926 _125947 x p y z) : term926 _125947 x p y z.
Proof. exact (fun h0 : term949 _125947 p x y => @lem6884518 _125947 x p y z h0 h1). Qed.
Lemma lem6884520 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) : term979 _125947 x p y z.
Proof. exact (fun h0 : term926 _125947 x p y z => @lem6884519 _125947 x p y z h0). Qed.
Lemma lem6884522 {A : Type'} (x : A) : term711 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem6884523 {A : Type'} (x : A) : (term711 A x) = (term712 A x).
Proof. exact (eq_refl (term711 A x)). Qed.
Lemma lem6884524 {A : Type'} (x : A) : term712 A x.
Proof. exact (EQ_MP (@lem6884523 A x) (@lem6884522 A x)). Qed.
Lemma lem6884525 {A : Type'} (x : A) (y : A) : term713 A x y.
Proof. exact (@lem6884524 A x y). Qed.
Lemma lem6884526 {A : Type'} (x : A) (y : A) : (term713 A x y) = ((term714 A x y) = (x = y)).
Proof. exact (eq_refl (term713 A x y)). Qed.
Lemma lem6884528 {A : Type'} (s : A -> Prop) : term715 A s.
Proof. exact (@lem3205495 A s). Qed.
Lemma lem6884529 {A : Type'} (s : A -> Prop) : (term715 A s) = (term716 A s).
Proof. exact (eq_refl (term715 A s)). Qed.
Lemma lem6884530 {A : Type'} (s : A -> Prop) : term716 A s.
Proof. exact (EQ_MP (@lem6884529 A s) (@lem6884528 A s)). Qed.
Lemma lem6884531 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term717 A s t.
Proof. exact (@lem6884530 A s t). Qed.
Lemma lem6884532 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term717 A s t) = (term718 A s t).
Proof. exact (eq_refl (term717 A s t)). Qed.
Lemma lem6884533 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term718 A s t.
Proof. exact (EQ_MP (@lem6884532 A s t) (@lem6884531 A s t)). Qed.
Lemma lem6884534 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term719 A s t x.
Proof. exact (@lem6884533 A s t x). Qed.
Lemma lem6884535 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term719 A s t x) = ((term720 A x s t) = (term721 A s x t)).
Proof. exact (eq_refl (term719 A s t x)). Qed.
Lemma lem6884537 {A : Type'} (x : A) : term722 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem6884538 {A : Type'} (x : A) : (term722 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term722 A x)). Qed.
Lemma lem6884539 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem6884538 A x) (@lem6884537 A x)). Qed.
Lemma lem6884540 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem6884542 {A B : Type'} (s : A -> Prop) : term723 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem6884543 {A B : Type'} (s : A -> Prop) : (term723 A B s) = (term724 A B s).
Proof. exact (eq_refl (term723 A B s)). Qed.
Lemma lem6884544 {A B : Type'} (s : A -> Prop) : term724 A B s.
Proof. exact (EQ_MP (@lem6884543 A B s) (@lem6884542 A B s)). Qed.
Lemma lem6884545 {A B : Type'} (s : A -> Prop) (f : A -> B) : term725 A B s f.
Proof. exact (@lem6884544 A B s f). Qed.
Lemma lem6884546 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term725 A B s f) = (term726 A B s f).
Proof. exact (eq_refl (term725 A B s f)). Qed.
Lemma lem6884547 {A B : Type'} (s : A -> Prop) (f : A -> B) : term726 A B s f.
Proof. exact (EQ_MP (@lem6884546 A B s f) (@lem6884545 A B s f)). Qed.
Lemma lem6884548 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term727 A B s f op.
Proof. exact (@lem6884547 A B s f op). Qed.
Lemma lem6884549 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term727 A B s f op) = ((@support A B op f s) = (term728 A B s f op)).
Proof. exact (eq_refl (term727 A B s f op)). Qed.
Lemma lem6884551 {A K : Type'} (dom : A -> Prop) : term980 A K dom.
Proof. exact (@lem6449478 A K dom). Qed.
Lemma lem6884552 {A K : Type'} (dom : A -> Prop) : (term980 A K dom) = (term981 A K dom).
Proof. exact (eq_refl (term980 A K dom)). Qed.
Lemma lem6884553 {A K : Type'} (dom : A -> Prop) : term981 A K dom.
Proof. exact (EQ_MP (@lem6884552 A K dom) (@lem6884551 A K dom)). Qed.
Lemma lem6884554 {A K : Type'} (dom : A -> Prop) (neut : A) : term982 A K dom neut.
Proof. exact (@lem6884553 A K dom neut). Qed.
Lemma lem6884555 {A K : Type'} (dom : A -> Prop) (neut : A) : (term982 A K dom neut) = (term983 A K dom neut).
Proof. exact (eq_refl (term982 A K dom neut)). Qed.
Lemma lem6884556 {A K : Type'} (dom : A -> Prop) (neut : A) : term983 A K dom neut.
Proof. exact (EQ_MP (@lem6884555 A K dom neut) (@lem6884554 A K dom neut)). Qed.
Lemma lem6884557 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term984 A K dom neut op.
Proof. exact (@lem6884556 A K dom neut op). Qed.
Lemma lem6884558 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : (term984 A K dom neut op) = (term985 A K op dom neut).
Proof. exact (eq_refl (term984 A K dom neut op)). Qed.
Lemma lem6884559 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) : term985 A K op dom neut.
Proof. exact (EQ_MP (@lem6884558 A K op dom neut) (@lem6884557 A K dom neut op)). Qed.
Lemma lem6884560 {A K : Type'} (op : type1400 A) (dom : A -> Prop) (neut : A) (ltle : type1402 K) : term986 A K op dom neut ltle.
Proof. exact (@lem6884559 A K op dom neut ltle). Qed.
Lemma lem6884561 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : (term986 A K op dom neut ltle) = (term987 A K op ltle dom neut).
Proof. exact (eq_refl (term986 A K op dom neut ltle)). Qed.
Lemma lem6884562 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) : term987 A K op ltle dom neut.
Proof. exact (EQ_MP (@lem6884561 A K op ltle dom neut) (@lem6884560 A K op dom neut ltle)). Qed.
Lemma lem6884563 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (dom : A -> Prop) (neut : A) (k : K -> Prop) : term988 A K op ltle dom neut k.
Proof. exact (@lem6884562 A K op ltle dom neut k). Qed.
Lemma lem6884564 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : (term988 A K op ltle dom neut k) = (term989 A K op ltle k dom neut).
Proof. exact (eq_refl (term988 A K op ltle dom neut k)). Qed.
Lemma lem6884565 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) : term989 A K op ltle k dom neut.
Proof. exact (EQ_MP (@lem6884564 A K op ltle k dom neut) (@lem6884563 A K op ltle dom neut k)). Qed.
Lemma lem6884566 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : term990 A K op ltle k dom neut f.
Proof. exact (@lem6884565 A K op ltle k dom neut f). Qed.
Lemma lem6884567 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (term990 A K op ltle k dom neut f) = ((@iterato A K dom neut op ltle k f) = (term991 A K op ltle k dom f neut)).
Proof. exact (eq_refl (term990 A K op ltle k dom neut f)). Qed.
Lemma lem6884569 {_120327 _120333 : Type'} (op : type1400 _120327) : term992 _120327 _120333 op.
Proof. exact (@lem5738118 _120327 _120333 op). Qed.
Lemma lem6884570 {_120327 _120333 : Type'} (op : type1400 _120327) : (term992 _120327 _120333 op) = (term993 _120327 _120333 op).
Proof. exact (eq_refl (term992 _120327 _120333 op)). Qed.
Lemma lem6884571 {_120327 _120333 : Type'} (op : type1400 _120327) : term993 _120327 _120333 op.
Proof. exact (EQ_MP (@lem6884570 _120327 _120333 op) (@lem6884569 _120327 _120333 op)). Qed.
Lemma lem6884572 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) : term994 _120327 _120333 op f.
Proof. exact (@lem6884571 _120327 _120333 op f). Qed.
Lemma lem6884573 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) : (term994 _120327 _120333 op f) = (term995 _120327 _120333 f op).
Proof. exact (eq_refl (term994 _120327 _120333 op f)). Qed.
Lemma lem6884574 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) : term995 _120327 _120333 f op.
Proof. exact (EQ_MP (@lem6884573 _120327 _120333 f op) (@lem6884572 _120327 _120333 op f)). Qed.
Lemma lem6884575 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) (s : _120333 -> Prop) : term996 _120327 _120333 f op s.
Proof. exact (@lem6884574 _120327 _120333 f op s). Qed.
Lemma lem6884576 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) : (term996 _120327 _120333 f op s) = ((@iterate _120327 _120333 op s f) = (term997 _120327 _120333 s f op)).
Proof. exact (eq_refl (term996 _120327 _120333 f op s)). Qed.
Lemma lem6884578 {A B : Type'} (f : A -> B) : term998 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem6884579 {A B : Type'} (f : A -> B) : (term998 A B f) = (term999 A B f).
Proof. exact (eq_refl (term998 A B f)). Qed.
Lemma lem6884580 {A B : Type'} (f : A -> B) : term999 A B f.
Proof. exact (EQ_MP (@lem6884579 A B f) (@lem6884578 A B f)). Qed.
Lemma lem6884581 {A B : Type'} (f : A -> B) (g : A -> B) : term1000 A B f g.
Proof. exact (@lem6884580 A B f g). Qed.
Lemma lem6884582 {A B : Type'} (f : A -> B) (g : A -> B) : (term1000 A B f g) = ((f = g) = (term1001 A B f g)).
Proof. exact (eq_refl (term1000 A B f g)). Qed.
Lemma lem6884584 {A : Type'} (op : type1400 A) (h1 : @monoidal A op) : @monoidal A op.
Proof. exact (h1). Qed.
Lemma lem6884588 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term1001 A B f g).
Proof. exact (EQ_MP (@lem6884582 A B f g) (@lem6884581 A B f g)). Qed.
Lemma lem6884589 {A K : Type'} (f : type854 A K) (g : type854 A K) : (f = g) = (term1002 A K f g).
Proof. exact (@lem6884588 (K -> Prop) (type802 A K) f g). Qed.
Lemma lem6884590 {A K : Type'} (ltle : type1402 K) (op : type1400 A) : ((term1003 A K op ltle) = (@iterate A K op)) = (term1004 A K ltle op).
Proof. exact (@lem6884589 A K (term1003 A K op ltle) (@iterate A K op)). Qed.
Lemma lem6884598 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term1001 A B f g).
Proof. exact (EQ_MP (@lem6884582 A B f g) (@lem6884581 A B f g)). Qed.
Lemma lem6884599 {A K : Type'} (f : type802 A K) (g : type802 A K) : (f = g) = (term1005 A K f g).
Proof. exact (@lem6884598 (K -> A) A f g). Qed.
Lemma lem6884600 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (x : K -> Prop) : ((term1006 A K op ltle x) = (@iterate A K op x)) = (term1007 A K ltle op x).
Proof. exact (@lem6884599 A K (term1006 A K op ltle x) (@iterate A K op x)). Qed.
Lemma lem6884609 {A K : Type'} (ltle : type1402 K) (op : type1400 A) : (term1008 A K ltle op) = (term1009 A K ltle op).
Proof. exact (fun_ext (fun x : K -> Prop => @lem6884600 A K ltle op x)). Qed.
Lemma lem6884610 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6884611 {A K : Type'} (ltle : type1402 K) (op : type1400 A) : (term1004 A K ltle op) = (term1010 A K ltle op).
Proof. exact (MK_COMB (@lem6884610 K) (@lem6884609 A K ltle op)). Qed.
Lemma lem6884616 {A K : Type'} (ltle : type1402 K) (op : type1400 A) : ((term1003 A K op ltle) = (@iterate A K op)) = (term1010 A K ltle op).
Proof. exact (TRANS (@lem6884590 A K ltle op) (@lem6884611 A K ltle op)). Qed.
Lemma lem6884617 {A K : Type'} (ltle : type1402 K) (op : type1400 A) : (term1010 A K ltle op) = ((term1003 A K op ltle) = (@iterate A K op)).
Proof. exact (SYM (@lem6884616 A K ltle op)). Qed.
Lemma lem6884621 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (@iterato A K dom neut op ltle k f) = (term991 A K op ltle k dom f neut).
Proof. exact (EQ_MP (@lem6884567 A K op ltle k dom f neut) (@lem6884566 A K op ltle k dom neut f)). Qed.
Lemma lem6884622 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (f : K -> A) (neut : A) : (@iterato A K dom neut op ltle k f) = (term991 A K op ltle k dom f neut).
Proof. exact (@lem6884621 A K op ltle k dom f neut). Qed.
Lemma lem6884623 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1011 A K op ltle k f) = (term1012 A K ltle k f op).
Proof. exact (@lem6884622 A K op ltle k (@UNIV A) f (@neutral A op)). Qed.
Lemma lem6884624 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6884625 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1013 A K op ltle k f) = (term1014 A K ltle k f op).
Proof. exact (MK_COMB (@lem6884624 A) (@lem6884623 A K ltle k f op)). Qed.
Lemma lem6884627 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) : (@iterate _120327 _120333 op s f) = (term997 _120327 _120333 s f op).
Proof. exact (EQ_MP (@lem6884576 _120327 _120333 s f op) (@lem6884575 _120327 _120333 f op s)). Qed.
Lemma lem6884628 {A K : Type'} (s : K -> Prop) (f : K -> A) (op : type1400 A) : (@iterate A K op s f) = (term997 A K s f op).
Proof. exact (@lem6884627 A K s f op). Qed.
Lemma lem6884629 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (@iterate A K op k f) = (term997 A K k f op).
Proof. exact (@lem6884628 A K k f op). Qed.
Lemma lem6884630 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : ((term1011 A K op ltle k f) = (@iterate A K op k f)) = ((term1012 A K ltle k f op) = (term997 A K k f op)).
Proof. exact (MK_COMB (@lem6884625 A K ltle k f op) (@lem6884629 A K k f op)). Qed.
Lemma lem6884631 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : ((term1012 A K ltle k f op) = (term997 A K k f op)) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (SYM (@lem6884630 A K ltle k f op)). Qed.
Lemma lem6884641 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term720 A x s t) = (term721 A s x t).
Proof. exact (EQ_MP (@lem6884535 A s x t) (@lem6884534 A s t x)). Qed.
Lemma lem6884642 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term720 A x s t) = (term721 A s x t).
Proof. exact (@lem6884641 A s x t). Qed.
Lemma lem6884643 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1015 A K f i op) = (term1016 A K f i op).
Proof. exact (@lem6884642 A (@UNIV A) (f i) (term1017 A op)). Qed.
Lemma lem6884647 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem6884540 A x) (@lem6884539 A x)). Qed.
Lemma lem6884648 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem6884647 A x). Qed.
Lemma lem6884649 {A K : Type'} (f : K -> A) (i : K) : (term1018 A K f i) = True.
Proof. exact (@lem6884648 A (f i)). Qed.
Lemma lem6884650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6884651 {A K : Type'} (f : K -> A) (i : K) : (term1019 A K f i) = (and True).
Proof. exact (MK_COMB (@lem6884650) (@lem6884649 A K f i)). Qed.
Lemma lem6884653 {A : Type'} (x : A) (y : A) : (term714 A x y) = (x = y).
Proof. exact (EQ_MP (@lem6884526 A x y) (@lem6884525 A x y)). Qed.
Lemma lem6884654 {A : Type'} (x : A) (y : A) : (term714 A x y) = (x = y).
Proof. exact (@lem6884653 A x y). Qed.
Lemma lem6884655 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1020 A K f i op) = ((f i) = (@neutral A op)).
Proof. exact (@lem6884654 A (f i) (@neutral A op)). Qed.
Lemma lem6884658 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6884659 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1021 A K f i op) = (term1022 A K f i op).
Proof. exact (MK_COMB (@lem6884658) (@lem6884655 A K f i op)). Qed.
Lemma lem6884660 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1016 A K f i op) = (term1023 A K f i op).
Proof. exact (MK_COMB (@lem6884651 A K f i) (@lem6884659 A K f i op)). Qed.
Lemma lem6884662 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6884663 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1023 A K f i op) = (term1022 A K f i op).
Proof. exact (@lem6884662 (term1022 A K f i op)). Qed.
Lemma lem6884666 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1016 A K f i op) = (term1022 A K f i op).
Proof. exact (TRANS (@lem6884660 A K f i op) (@lem6884663 A K f i op)). Qed.
Lemma lem6884667 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1015 A K f i op) = (term1022 A K f i op).
Proof. exact (TRANS (@lem6884643 A K f i op) (@lem6884666 A K f i op)). Qed.
Lemma lem6884668 {K : Type'} (i : K) (k : K -> Prop) : (term13 K i k) = (term13 K i k).
Proof. exact (eq_refl (term13 K i k)). Qed.
Lemma lem6884669 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) : (term1024 A K k f i op) = (term1025 A K k f i op).
Proof. exact (MK_COMB (@lem6884668 K i k) (@lem6884667 A K f i op)). Qed.
Lemma lem6884672 {K : Type'} (GEN_PVAR_269 : K) : (@SETSPEC K GEN_PVAR_269) = (@SETSPEC K GEN_PVAR_269).
Proof. exact (eq_refl (@SETSPEC K GEN_PVAR_269)). Qed.
Lemma lem6884673 {A K : Type'} (GEN_PVAR_269 : K) (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) : (term1026 A K GEN_PVAR_269 k f i op) = (term1027 A K GEN_PVAR_269 k f i op).
Proof. exact (MK_COMB (@lem6884672 K GEN_PVAR_269) (@lem6884669 A K k f i op)). Qed.
Lemma lem6884674 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6884675 {A K : Type'} (GEN_PVAR_269 : K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (i : K) : (term1028 A K GEN_PVAR_269 k f op i) = (term1029 A K GEN_PVAR_269 k f op i).
Proof. exact (MK_COMB (@lem6884673 A K GEN_PVAR_269 k f i op) (@lem6884674 K i)). Qed.
Lemma lem6884676 {A K : Type'} (GEN_PVAR_269 : K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1030 A K GEN_PVAR_269 k f op) = (term1031 A K GEN_PVAR_269 k f op).
Proof. exact (fun_ext (fun i : K => @lem6884675 A K GEN_PVAR_269 k f op i)). Qed.
Lemma lem6884677 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6884678 {A K : Type'} (GEN_PVAR_269 : K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1032 A K GEN_PVAR_269 k f op) = (term1033 A K GEN_PVAR_269 k f op).
Proof. exact (MK_COMB (@lem6884677 K) (@lem6884676 A K GEN_PVAR_269 k f op)). Qed.
Lemma lem6884683 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1034 A K k f op) = (term1035 A K k f op).
Proof. exact (fun_ext (fun GEN_PVAR_269 : K => @lem6884678 A K GEN_PVAR_269 k f op)). Qed.
Lemma lem6884684 {K : Type'} : (@GSPEC K) = (@GSPEC K).
Proof. exact (eq_refl (@GSPEC K)). Qed.
Lemma lem6884685 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1036 A K k f op) = (term1037 A K k f op).
Proof. exact (MK_COMB (@lem6884684 K) (@lem6884683 A K k f op)). Qed.
Lemma lem6884686 {K : Type'} : (@FINITE K) = (@FINITE K).
Proof. exact (eq_refl (@FINITE K)). Qed.
Lemma lem6884687 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1038 A K k f op) = (term1039 A K k f op).
Proof. exact (MK_COMB (@lem6884686 K) (@lem6884685 A K k f op)). Qed.
Lemma lem6884688 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem6884689 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1040 A K k f op) = (term1041 A K k f op).
Proof. exact (MK_COMB (@lem6884688 A) (@lem6884687 A K k f op)). Qed.
Lemma lem6884697 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term720 A x s t) = (term721 A s x t).
Proof. exact (EQ_MP (@lem6884535 A s x t) (@lem6884534 A s t x)). Qed.
Lemma lem6884698 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term720 A x s t) = (term721 A s x t).
Proof. exact (@lem6884697 A s x t). Qed.
Lemma lem6884699 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1015 A K f i op) = (term1016 A K f i op).
Proof. exact (@lem6884698 A (@UNIV A) (f i) (term1017 A op)). Qed.
Lemma lem6884703 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem6884540 A x) (@lem6884539 A x)). Qed.
Lemma lem6884704 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem6884703 A x). Qed.
Lemma lem6884705 {A K : Type'} (f : K -> A) (i : K) : (term1018 A K f i) = True.
Proof. exact (@lem6884704 A (f i)). Qed.
Lemma lem6884706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6884707 {A K : Type'} (f : K -> A) (i : K) : (term1019 A K f i) = (and True).
Proof. exact (MK_COMB (@lem6884706) (@lem6884705 A K f i)). Qed.
Lemma lem6884709 {A : Type'} (x : A) (y : A) : (term714 A x y) = (x = y).
Proof. exact (EQ_MP (@lem6884526 A x y) (@lem6884525 A x y)). Qed.
Lemma lem6884710 {A : Type'} (x : A) (y : A) : (term714 A x y) = (x = y).
Proof. exact (@lem6884709 A x y). Qed.
Lemma lem6884711 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1020 A K f i op) = ((f i) = (@neutral A op)).
Proof. exact (@lem6884710 A (f i) (@neutral A op)). Qed.
Lemma lem6884714 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6884715 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1021 A K f i op) = (term1022 A K f i op).
Proof. exact (MK_COMB (@lem6884714) (@lem6884711 A K f i op)). Qed.
Lemma lem6884716 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1016 A K f i op) = (term1023 A K f i op).
Proof. exact (MK_COMB (@lem6884707 A K f i) (@lem6884715 A K f i op)). Qed.
Lemma lem6884718 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6884719 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1023 A K f i op) = (term1022 A K f i op).
Proof. exact (@lem6884718 (term1022 A K f i op)). Qed.
Lemma lem6884722 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1016 A K f i op) = (term1022 A K f i op).
Proof. exact (TRANS (@lem6884716 A K f i op) (@lem6884719 A K f i op)). Qed.
Lemma lem6884723 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1015 A K f i op) = (term1022 A K f i op).
Proof. exact (TRANS (@lem6884699 A K f i op) (@lem6884722 A K f i op)). Qed.
Lemma lem6884724 {K : Type'} (i : K) (k : K -> Prop) : (term13 K i k) = (term13 K i k).
Proof. exact (eq_refl (term13 K i k)). Qed.
Lemma lem6884725 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) : (term1024 A K k f i op) = (term1025 A K k f i op).
Proof. exact (MK_COMB (@lem6884724 K i k) (@lem6884723 A K f i op)). Qed.
Lemma lem6884728 {K : Type'} (GEN_PVAR_270 : K) : (@SETSPEC K GEN_PVAR_270) = (@SETSPEC K GEN_PVAR_270).
Proof. exact (eq_refl (@SETSPEC K GEN_PVAR_270)). Qed.
Lemma lem6884729 {A K : Type'} (GEN_PVAR_270 : K) (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) : (term1026 A K GEN_PVAR_270 k f i op) = (term1027 A K GEN_PVAR_270 k f i op).
Proof. exact (MK_COMB (@lem6884728 K GEN_PVAR_270) (@lem6884725 A K k f i op)). Qed.
Lemma lem6884730 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6884731 {A K : Type'} (GEN_PVAR_270 : K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (i : K) : (term1028 A K GEN_PVAR_270 k f op i) = (term1029 A K GEN_PVAR_270 k f op i).
Proof. exact (MK_COMB (@lem6884729 A K GEN_PVAR_270 k f i op) (@lem6884730 K i)). Qed.
Lemma lem6884732 {A K : Type'} (GEN_PVAR_270 : K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1030 A K GEN_PVAR_270 k f op) = (term1031 A K GEN_PVAR_270 k f op).
Proof. exact (fun_ext (fun i : K => @lem6884731 A K GEN_PVAR_270 k f op i)). Qed.
Lemma lem6884733 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6884734 {A K : Type'} (GEN_PVAR_270 : K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1032 A K GEN_PVAR_270 k f op) = (term1033 A K GEN_PVAR_270 k f op).
Proof. exact (MK_COMB (@lem6884733 K) (@lem6884732 A K GEN_PVAR_270 k f op)). Qed.
Lemma lem6884739 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1034 A K k f op) = (term1035 A K k f op).
Proof. exact (fun_ext (fun GEN_PVAR_270 : K => @lem6884734 A K GEN_PVAR_270 k f op)). Qed.
Lemma lem6884740 {K : Type'} : (@GSPEC K) = (@GSPEC K).
Proof. exact (eq_refl (@GSPEC K)). Qed.
Lemma lem6884741 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1036 A K k f op) = (term1037 A K k f op).
Proof. exact (MK_COMB (@lem6884740 K) (@lem6884739 A K k f op)). Qed.
Lemma lem6884742 {A K : Type'} (op : type1400 A) (ltle : type1402 K) : (term1003 A K op ltle) = (term1003 A K op ltle).
Proof. exact (eq_refl (term1003 A K op ltle)). Qed.
Lemma lem6884743 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1042 A K ltle k f op) = (term1043 A K ltle k f op).
Proof. exact (MK_COMB (@lem6884742 A K op ltle) (@lem6884741 A K k f op)). Qed.
Lemma lem6884744 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6884745 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (f : K -> A) : (term1044 A K ltle k op f) = (term1045 A K ltle k op f).
Proof. exact (MK_COMB (@lem6884743 A K ltle k f op) (@lem6884744 A K f)). Qed.
Lemma lem6884746 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (f : K -> A) : (term1046 A K ltle k op f) = (term1047 A K ltle k op f).
Proof. exact (MK_COMB (@lem6884689 A K k f op) (@lem6884745 A K ltle k op f)). Qed.
Lemma lem6884747 {A : Type'} (op : type1400 A) : (@neutral A op) = (@neutral A op).
Proof. exact (eq_refl (@neutral A op)). Qed.
Lemma lem6884748 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1012 A K ltle k f op) = (term1048 A K ltle k f op).
Proof. exact (MK_COMB (@lem6884746 A K ltle k op f) (@lem6884747 A op)). Qed.
Lemma lem6884749 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6884750 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1014 A K ltle k f op) = (term1049 A K ltle k f op).
Proof. exact (MK_COMB (@lem6884749 A) (@lem6884748 A K ltle k f op)). Qed.
Lemma lem6884752 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term728 A B s f op).
Proof. exact (EQ_MP (@lem6884549 A B s f op) (@lem6884548 A B s f op)). Qed.
Lemma lem6884753 {A K : Type'} (s : K -> Prop) (f : K -> A) (op : type1400 A) : (@support K A op f s) = (term1037 A K s f op).
Proof. exact (@lem6884752 K A s f op). Qed.
Lemma lem6884754 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (@support K A op f k) = (term1037 A K k f op).
Proof. exact (@lem6884753 A K k f op). Qed.
Lemma lem6884763 {K : Type'} : (@FINITE K) = (@FINITE K).
Proof. exact (eq_refl (@FINITE K)). Qed.
Lemma lem6884764 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1050 A K op f k) = (term1039 A K k f op).
Proof. exact (MK_COMB (@lem6884763 K) (@lem6884754 A K k f op)). Qed.
Lemma lem6884765 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem6884766 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1051 A K op f k) = (term1041 A K k f op).
Proof. exact (MK_COMB (@lem6884765 A) (@lem6884764 A K k f op)). Qed.
Lemma lem6884768 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term728 A B s f op).
Proof. exact (EQ_MP (@lem6884549 A B s f op) (@lem6884548 A B s f op)). Qed.
Lemma lem6884769 {A K : Type'} (s : K -> Prop) (f : K -> A) (op : type1400 A) : (@support K A op f s) = (term1037 A K s f op).
Proof. exact (@lem6884768 K A s f op). Qed.
Lemma lem6884770 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (@support K A op f k) = (term1037 A K k f op).
Proof. exact (@lem6884769 A K k f op). Qed.
Lemma lem6884779 {A K : Type'} (op : type1400 A) : (@iterate A K op) = (@iterate A K op).
Proof. exact (eq_refl (@iterate A K op)). Qed.
Lemma lem6884780 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1052 A K op f k) = (term1053 A K k f op).
Proof. exact (MK_COMB (@lem6884779 A K op) (@lem6884770 A K k f op)). Qed.
Lemma lem6884781 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6884782 {A K : Type'} (k : K -> Prop) (op : type1400 A) (f : K -> A) : (term729 A K op k f) = (term1054 A K k op f).
Proof. exact (MK_COMB (@lem6884780 A K k f op) (@lem6884781 A K f)). Qed.
Lemma lem6884783 {A K : Type'} (k : K -> Prop) (op : type1400 A) (f : K -> A) : (term1055 A K op k f) = (term1056 A K k op f).
Proof. exact (MK_COMB (@lem6884766 A K k f op) (@lem6884782 A K k op f)). Qed.
Lemma lem6884784 {A : Type'} (op : type1400 A) : (@neutral A op) = (@neutral A op).
Proof. exact (eq_refl (@neutral A op)). Qed.
Lemma lem6884785 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term997 A K k f op) = (term1057 A K k f op).
Proof. exact (MK_COMB (@lem6884783 A K k op f) (@lem6884784 A op)). Qed.
Lemma lem6884786 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : ((term1012 A K ltle k f op) = (term997 A K k f op)) = ((term1048 A K ltle k f op) = (term1057 A K k f op)).
Proof. exact (MK_COMB (@lem6884750 A K ltle k f op) (@lem6884785 A K k f op)). Qed.
Lemma lem6884789 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : ((term1048 A K ltle k f op) = (term1057 A K k f op)) = ((term1012 A K ltle k f op) = (term997 A K k f op)).
Proof. exact (SYM (@lem6884786 A K ltle k f op)). Qed.
Lemma lem6884791 {_125947 : Type'} (x : _125947) (p : Prop) (y : _125947) (z : _125947) : term926 _125947 x p y z.
Proof. exact (@lem6884520 _125947 x p y z (@lem6884512 _125947 x p y z)). Qed.
Lemma lem6884792 {A : Type'} (x : A) (p : Prop) (y : A) (z : A) : term926 A x p y z.
Proof. exact (@lem6884791 A x p y z). Qed.
Lemma lem6884793 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : term1058 A K ltle k f op.
Proof. exact (@lem6884792 A (term1045 A K ltle k op f) (term1039 A K k f op) (term1054 A K k op f) (@neutral A op)). Qed.
Lemma lem6884796 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1059 A K ltle k f op) = (term1059 A K ltle k f op).
Proof. exact (eq_refl (term1059 A K ltle k f op)). Qed.
Lemma lem6884797 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1059 A K ltle k f op) = (term1058 A K ltle k f op).
Proof. exact (eq_refl (term1059 A K ltle k f op)). Qed.
Lemma lem6884798 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1060 A K ltle k f op) = (term1060 A K ltle k f op).
Proof. exact (eq_refl (term1060 A K ltle k f op)). Qed.
Lemma lem6884799 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : ((term1059 A K ltle k f op) = (term1059 A K ltle k f op)) = ((term1059 A K ltle k f op) = (term1058 A K ltle k f op)).
Proof. exact (MK_COMB (@lem6884798 A K ltle k f op) (@lem6884797 A K ltle k f op)). Qed.
Lemma lem6884800 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1059 A K ltle k f op) = (term1058 A K ltle k f op).
Proof. exact (eq_refl (term1059 A K ltle k f op)). Qed.
Lemma lem6884801 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6884802 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1060 A K ltle k f op) = (term1061 A K ltle k f op).
Proof. exact (MK_COMB (@lem6884801) (@lem6884800 A K ltle k f op)). Qed.
Lemma lem6884803 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1058 A K ltle k f op) = (term1058 A K ltle k f op).
Proof. exact (eq_refl (term1058 A K ltle k f op)). Qed.
Lemma lem6884804 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : ((term1059 A K ltle k f op) = (term1058 A K ltle k f op)) = ((term1058 A K ltle k f op) = (term1058 A K ltle k f op)).
Proof. exact (MK_COMB (@lem6884802 A K ltle k f op) (@lem6884803 A K ltle k f op)). Qed.
Lemma lem6884805 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : ((term1059 A K ltle k f op) = (term1059 A K ltle k f op)) = ((term1058 A K ltle k f op) = (term1058 A K ltle k f op)).
Proof. exact (TRANS (@lem6884799 A K ltle k f op) (@lem6884804 A K ltle k f op)). Qed.
Lemma lem6884806 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1058 A K ltle k f op) = (term1058 A K ltle k f op).
Proof. exact (EQ_MP (@lem6884805 A K ltle k f op) (@lem6884796 A K ltle k f op)). Qed.
Lemma lem6884807 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : term1058 A K ltle k f op.
Proof. exact (EQ_MP (@lem6884806 A K ltle k f op) (@lem6884793 A K ltle k f op)). Qed.
Lemma lem6884809 {_125911 : Type'} (P : type686 _125911) : term855 _125911 P.
Proof. exact (@lem6884225 _125911 P (@lem6884217 _125911 P)). Qed.
Lemma lem6884810 {K : Type'} (P : type686 K) : term855 K P.
Proof. exact (@lem6884809 K P). Qed.
Lemma lem6884811 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) : term1062 A K ltle op f.
Proof. exact (@lem6884810 K (term1063 A K ltle op f)). Qed.
Lemma lem6884812 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1064 A K ltle op f k) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (eq_refl (term1064 A K ltle op f k)). Qed.
Lemma lem6884813 {K : Type'} (k : K -> Prop) (n : nat) : (term918 K k n) = (term918 K k n).
Proof. exact (eq_refl (term918 K k n)). Qed.
Lemma lem6884814 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1065 A K n ltle op f k) = (term1066 A K n ltle op k f).
Proof. exact (MK_COMB (@lem6884813 K k n) (@lem6884812 A K ltle op k f)). Qed.
Lemma lem6884815 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1067 A K n ltle op f) = (term1068 A K n ltle op f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6884814 A K n ltle op k f)). Qed.
Lemma lem6884816 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6884817 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1069 A K n ltle op f) = (term1070 A K n ltle op f).
Proof. exact (MK_COMB (@lem6884816 K) (@lem6884815 A K n ltle op f)). Qed.
Lemma lem6884818 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1071 A K ltle op f) = (term1072 A K ltle op f).
Proof. exact (fun_ext (fun n : nat => @lem6884817 A K n ltle op f)). Qed.
Lemma lem6884819 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6884820 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1073 A K ltle op f) = (term1074 A K ltle op f).
Proof. exact (MK_COMB (@lem6884819) (@lem6884818 A K ltle op f)). Qed.
Lemma lem6884821 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6884822 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1075 A K ltle op f) = (term1076 A K ltle op f).
Proof. exact (MK_COMB (@lem6884821) (@lem6884820 A K ltle op f)). Qed.
Lemma lem6884823 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1064 A K ltle op f k) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (eq_refl (term1064 A K ltle op f k)). Qed.
Lemma lem6884824 {K : Type'} (k : K -> Prop) : (term1077 K k) = (term1077 K k).
Proof. exact (eq_refl (term1077 K k)). Qed.
Lemma lem6884825 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1078 A K ltle op f k) = (term1079 A K ltle op k f).
Proof. exact (MK_COMB (@lem6884824 K k) (@lem6884823 A K ltle op k f)). Qed.
Lemma lem6884826 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1080 A K ltle op f) = (term1081 A K ltle op f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6884825 A K ltle op k f)). Qed.
Lemma lem6884827 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6884828 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1082 A K ltle op f) = (term1083 A K ltle op f).
Proof. exact (MK_COMB (@lem6884827 K) (@lem6884826 A K ltle op f)). Qed.
Lemma lem6884829 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1062 A K ltle op f) = (term1084 A K ltle op f).
Proof. exact (MK_COMB (@lem6884822 A K ltle op f) (@lem6884828 A K ltle op f)). Qed.
Lemma lem6884830 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) : term1084 A K ltle op f.
Proof. exact (EQ_MP (@lem6884829 A K ltle op f) (@lem6884811 A K ltle op f)). Qed.
Lemma lem6884850 (P : nat -> Prop) : term843 P.
Proof. exact (EQ_MP (@lem6883658 P) (@lem6883657 P)). Qed.
Lemma lem6884851 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) : term1085 A K ltle op f.
Proof. exact (@lem6884850 (term1072 A K ltle op f)). Qed.
Lemma lem6884852 {A K : Type'} (m : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1086 A K ltle op f m) = (term1070 A K m ltle op f).
Proof. exact (eq_refl (term1086 A K ltle op f m)). Qed.
Lemma lem6884853 (m : nat) (n : nat) : (term1087 m n) = (term1087 m n).
Proof. exact (eq_refl (term1087 m n)). Qed.
Lemma lem6884854 {A K : Type'} (n : nat) (m : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1088 A K n ltle op f m) = (term1089 A K n m ltle op f).
Proof. exact (MK_COMB (@lem6884853 m n) (@lem6884852 A K m ltle op f)). Qed.
Lemma lem6884855 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1090 A K n ltle op f) = (term1091 A K n ltle op f).
Proof. exact (fun_ext (fun m : nat => @lem6884854 A K n m ltle op f)). Qed.
Lemma lem6884856 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6884857 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1092 A K n ltle op f) = (term1093 A K n ltle op f).
Proof. exact (MK_COMB (@lem6884856) (@lem6884855 A K n ltle op f)). Qed.
Lemma lem6884858 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6884859 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1094 A K n ltle op f) = (term1095 A K n ltle op f).
Proof. exact (MK_COMB (@lem6884858) (@lem6884857 A K n ltle op f)). Qed.
Lemma lem6884860 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1086 A K ltle op f n) = (term1070 A K n ltle op f).
Proof. exact (eq_refl (term1086 A K ltle op f n)). Qed.
Lemma lem6884861 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1096 A K ltle op f n) = (term1097 A K n ltle op f).
Proof. exact (MK_COMB (@lem6884859 A K n ltle op f) (@lem6884860 A K n ltle op f)). Qed.
Lemma lem6884862 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1098 A K ltle op f) = (term1099 A K ltle op f).
Proof. exact (fun_ext (fun n : nat => @lem6884861 A K n ltle op f)). Qed.
Lemma lem6884863 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6884864 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1100 A K ltle op f) = (term1101 A K ltle op f).
Proof. exact (MK_COMB (@lem6884863) (@lem6884862 A K ltle op f)). Qed.
Lemma lem6884865 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6884866 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1102 A K ltle op f) = (term1103 A K ltle op f).
Proof. exact (MK_COMB (@lem6884865) (@lem6884864 A K ltle op f)). Qed.
Lemma lem6884867 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1086 A K ltle op f n) = (term1070 A K n ltle op f).
Proof. exact (eq_refl (term1086 A K ltle op f n)). Qed.
Lemma lem6884868 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1104 A K ltle op f) = (term1072 A K ltle op f).
Proof. exact (fun_ext (fun n : nat => @lem6884867 A K n ltle op f)). Qed.
Lemma lem6884869 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6884870 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1105 A K ltle op f) = (term1074 A K ltle op f).
Proof. exact (MK_COMB (@lem6884869) (@lem6884868 A K ltle op f)). Qed.
Lemma lem6884871 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1085 A K ltle op f) = (term1106 A K ltle op f).
Proof. exact (MK_COMB (@lem6884866 A K ltle op f) (@lem6884870 A K ltle op f)). Qed.
Lemma lem6884872 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) : term1106 A K ltle op f.
Proof. exact (EQ_MP (@lem6884871 A K ltle op f) (@lem6884851 A K ltle op f)). Qed.
Lemma lem6884873 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) (h1 : term1093 A K n ltle op f) : term1093 A K n ltle op f.
Proof. exact (h1). Qed.
Lemma lem6884874 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term883 K k n) : term883 K k n.
Proof. exact (h1). Qed.
Lemma lem6884875 {K : Type'} (k : K -> Prop) (n : nat) (h1 : (@CARD K k) = n) : (@CARD K k) = n.
Proof. exact (h1). Qed.
Lemma lem6884876 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : @FINITE K k.
Proof. exact (h1). Qed.
Lemma lem6884878 {A : Type'} (op : type1400 A) (h1 : @monoidal A op) : @monoidal A op.
Proof. exact (h1). Qed.
Lemma lem6884884 {A : Type'} (P : Prop) (Q : A -> Prop) : (term839 A P Q) = (term840 A P Q).
Proof. exact (EQ_MP (@lem6883642 A P Q) (@lem6883641 A P Q)). Qed.
Lemma lem6884885 {K : Type'} (P : Prop) (Q : type686 K) : (term1107 K P Q) = (term1108 K P Q).
Proof. exact (@lem6884884 (K -> Prop) P Q). Qed.
Lemma lem6884886 {A K : Type'} (n : nat) (m : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1109 A K n m ltle op f) = (term1110 A K n m ltle op f).
Proof. exact (@lem6884885 K (Peano.lt m n) (term1068 A K m ltle op f)). Qed.
Lemma lem6884887 {A K : Type'} (m : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1111 A K m ltle op f k) = (term1066 A K m ltle op k f).
Proof. exact (eq_refl (term1111 A K m ltle op f k)). Qed.
Lemma lem6884888 {A K : Type'} (m : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1112 A K m ltle op f) = (term1068 A K m ltle op f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6884887 A K m ltle op k f)). Qed.
Lemma lem6884889 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6884890 {A K : Type'} (m : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1113 A K m ltle op f) = (term1070 A K m ltle op f).
Proof. exact (MK_COMB (@lem6884889 K) (@lem6884888 A K m ltle op f)). Qed.
Lemma lem6884891 (m : nat) (n : nat) : (term1087 m n) = (term1087 m n).
Proof. exact (eq_refl (term1087 m n)). Qed.
Lemma lem6884892 {A K : Type'} (n : nat) (m : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1109 A K n m ltle op f) = (term1089 A K n m ltle op f).
Proof. exact (MK_COMB (@lem6884891 m n) (@lem6884890 A K m ltle op f)). Qed.
Lemma lem6884893 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6884894 {A K : Type'} (n : nat) (m : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1114 A K n m ltle op f) = (term1115 A K n m ltle op f).
Proof. exact (MK_COMB (@lem6884893) (@lem6884892 A K n m ltle op f)). Qed.
Lemma lem6884895 {A K : Type'} (m : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1111 A K m ltle op f k) = (term1066 A K m ltle op k f).
Proof. exact (eq_refl (term1111 A K m ltle op f k)). Qed.
Lemma lem6884896 (m : nat) (n : nat) : (term1087 m n) = (term1087 m n).
Proof. exact (eq_refl (term1087 m n)). Qed.
Lemma lem6884897 {A K : Type'} (n : nat) (m : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1116 A K n m ltle op f k) = (term1117 A K n m ltle op k f).
Proof. exact (MK_COMB (@lem6884896 m n) (@lem6884895 A K m ltle op k f)). Qed.
Lemma lem6884898 {A K : Type'} (n : nat) (m : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1118 A K n m ltle op f) = (term1119 A K n m ltle op f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6884897 A K n m ltle op k f)). Qed.
Lemma lem6884899 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6884900 {A K : Type'} (n : nat) (m : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1110 A K n m ltle op f) = (term1120 A K n m ltle op f).
Proof. exact (MK_COMB (@lem6884899 K) (@lem6884898 A K n m ltle op f)). Qed.
Lemma lem6884901 {A K : Type'} (n : nat) (m : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : ((term1109 A K n m ltle op f) = (term1110 A K n m ltle op f)) = ((term1089 A K n m ltle op f) = (term1120 A K n m ltle op f)).
Proof. exact (MK_COMB (@lem6884894 A K n m ltle op f) (@lem6884900 A K n m ltle op f)). Qed.
Lemma lem6884902 {A K : Type'} (n : nat) (m : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1089 A K n m ltle op f) = (term1120 A K n m ltle op f).
Proof. exact (EQ_MP (@lem6884901 A K n m ltle op f) (@lem6884886 A K n m ltle op f)). Qed.
Lemma lem6884908 (p : Prop) (q : Prop) (r : Prop) : (term1121 p q r) = (term1122 p q r).
Proof. exact (EQ_MP (@lem892 p q r) (@lem887 p q r)). Qed.
Lemma lem6884909 {A K : Type'} (n : nat) (m : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1117 A K n m ltle op k f) = (term1123 A K n m ltle op k f).
Proof. exact (@lem6884908 (Peano.lt m n) (term883 K k m) ((term1011 A K op ltle k f) = (@iterate A K op k f))). Qed.
Lemma lem6884920 {A K : Type'} (n : nat) (m : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1119 A K n m ltle op f) = (term1124 A K n m ltle op f).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6884909 A K n m ltle op k f)). Qed.
Lemma lem6884921 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6884922 {A K : Type'} (n : nat) (m : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1120 A K n m ltle op f) = (term1125 A K n m ltle op f).
Proof. exact (MK_COMB (@lem6884921 K) (@lem6884920 A K n m ltle op f)). Qed.
Lemma lem6884927 {A K : Type'} (n : nat) (m : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1089 A K n m ltle op f) = (term1125 A K n m ltle op f).
Proof. exact (TRANS (@lem6884902 A K n m ltle op f) (@lem6884922 A K n m ltle op f)). Qed.
Lemma lem6884928 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1091 A K n ltle op f) = (term1126 A K n ltle op f).
Proof. exact (fun_ext (fun m : nat => @lem6884927 A K n m ltle op f)). Qed.
Lemma lem6884929 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6884930 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1093 A K n ltle op f) = (term1127 A K n ltle op f).
Proof. exact (MK_COMB (@lem6884929) (@lem6884928 A K n ltle op f)). Qed.
Lemma lem6884935 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) (h1 : term1093 A K n ltle op f) : term1127 A K n ltle op f.
Proof. exact (EQ_MP (@lem6884930 A K n ltle op f) (@lem6884873 A K n ltle op f h1)). Qed.
Lemma lem6884937 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : @FINITE K k.
Proof. exact (h1). Qed.
Lemma lem6884941 {K : Type'} (k : K -> Prop) (n : nat) (h1 : (@CARD K k) = n) : (@CARD K k) = n.
Proof. exact (h1). Qed.
Lemma lem6884942 {A K : Type'} (dom : A -> Prop) : term1128 A K dom.
Proof. exact (@lem6790065 A K dom). Qed.
Lemma lem6884943 {A K : Type'} (dom : A -> Prop) : (term1128 A K dom) = (term1129 A K dom).
Proof. exact (eq_refl (term1128 A K dom)). Qed.
Lemma lem6884944 {A K : Type'} (dom : A -> Prop) : term1129 A K dom.
Proof. exact (EQ_MP (@lem6884943 A K dom) (@lem6884942 A K dom)). Qed.
Lemma lem6884945 {A K : Type'} (dom : A -> Prop) (neut : A) : term1130 A K dom neut.
Proof. exact (@lem6884944 A K dom neut). Qed.
Lemma lem6884946 {A K : Type'} (dom : A -> Prop) (neut : A) : (term1130 A K dom neut) = (term1131 A K dom neut).
Proof. exact (eq_refl (term1130 A K dom neut)). Qed.
Lemma lem6884947 {A K : Type'} (dom : A -> Prop) (neut : A) : term1131 A K dom neut.
Proof. exact (EQ_MP (@lem6884946 A K dom neut) (@lem6884945 A K dom neut)). Qed.
Lemma lem6884948 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term1132 A K dom neut op.
Proof. exact (@lem6884947 A K dom neut op). Qed.
Lemma lem6884949 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : (term1132 A K dom neut op) = (term1133 A K dom neut op).
Proof. exact (eq_refl (term1132 A K dom neut op)). Qed.
Lemma lem6884950 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term1133 A K dom neut op.
Proof. exact (EQ_MP (@lem6884949 A K dom neut op) (@lem6884948 A K dom neut op)). Qed.
Lemma lem6884951 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : term1134 A K dom neut op ltle.
Proof. exact (@lem6884950 A K dom neut op ltle). Qed.
Lemma lem6884952 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : (term1134 A K dom neut op ltle) = (term1135 A K dom neut op ltle).
Proof. exact (eq_refl (term1134 A K dom neut op ltle)). Qed.
Lemma lem6884953 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : term1135 A K dom neut op ltle.
Proof. exact (EQ_MP (@lem6884952 A K dom neut op ltle) (@lem6884951 A K dom neut op ltle)). Qed.
Lemma lem6884954 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term1136 A K dom neut op ltle f.
Proof. exact (@lem6884953 A K dom neut op ltle f). Qed.
Lemma lem6884955 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : (term1136 A K dom neut op ltle f) = (term1137 A K dom neut op ltle f).
Proof. exact (eq_refl (term1136 A K dom neut op ltle f)). Qed.
Lemma lem6884956 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term1137 A K dom neut op ltle f.
Proof. exact (EQ_MP (@lem6884955 A K dom neut op ltle f) (@lem6884954 A K dom neut op ltle f)). Qed.
Lemma lem6884971 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term79 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem6884972 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term79 _120477 _120519 _120521 op) = (term80 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term79 _120477 _120519 _120521 op)). Qed.
Lemma lem6884973 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term80 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6884972 _120477 _120519 _120521 op) (@lem6884971 _120477 _120519 _120521 op)). Qed.
Lemma lem6884974 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem6884975 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term1138 _120477 _120519 _120521 op.
Proof. exact (@lem6884973 _120477 _120519 _120521 op (@lem6884974 _120519 op h1)). Qed.
Lemma lem6884998 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term1139 _120477 _120519 op.
Proof. exact (proj1 (@lem6884975 _120477 _120519 Prop op h1)). Qed.
Lemma lem6884999 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term1140 _120477 _120519 op f.
Proof. exact (@lem6884998 _120477 _120519 op h1 f). Qed.
Lemma lem6885000 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : (term1140 _120477 _120519 op f) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl (term1140 _120477 _120519 op f)). Qed.
Lemma lem6885001 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (EQ_MP (@lem6885000 _120477 _120519 f op) (@lem6884999 _120477 _120519 f op h1)). Qed.
Lemma lem6885007 {A : Type'} (op : type1400 A) : (@monoidal A op) = ((@monoidal A op) = True).
Proof. exact (@lem7 (@monoidal A op)). Qed.
Lemma lem6885107 {K : Type'} (k : K -> Prop) (h1 : k = (@EMPTY K)) : k = (@EMPTY K).
Proof. exact (h1). Qed.
Lemma lem6885108 {A K : Type'} (op : type1400 A) (ltle : type1402 K) : (term1003 A K op ltle) = (term1003 A K op ltle).
Proof. exact (eq_refl (term1003 A K op ltle)). Qed.
Lemma lem6885109 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (h1 : k = (@EMPTY K)) : (term1006 A K op ltle k) = (term1141 A K op ltle).
Proof. exact (MK_COMB (@lem6885108 A K op ltle) (@lem6885107 K k h1)). Qed.
Lemma lem6885110 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6885111 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (k : K -> Prop) (h1 : k = (@EMPTY K)) : (term1011 A K op ltle k f) = (term1142 A K op ltle f).
Proof. exact (MK_COMB (@lem6885109 A K op ltle k h1) (@lem6885110 A K f)). Qed.
Lemma lem6885129 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (neut : A) : (@iterato A K dom neut op ltle (@EMPTY K) f) = neut.
Proof. exact (proj1 (@lem6884956 A K dom neut op ltle f)). Qed.
Lemma lem6885130 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (neut : A) : (@iterato A K dom neut op ltle (@EMPTY K) f) = neut.
Proof. exact (@lem6885129 A K dom op ltle f neut). Qed.
Lemma lem6885131 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) : (term1142 A K op ltle f) = (@neutral A op).
Proof. exact (@lem6885130 A K (@UNIV A) op ltle f (@neutral A op)). Qed.
Lemma lem6885132 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (h1 : k = (@EMPTY K)) : (term1011 A K op ltle k f) = (@neutral A op).
Proof. exact (TRANS (@lem6885111 A K op ltle f k h1) (@lem6885131 A K ltle f op)). Qed.
Lemma lem6885133 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6885134 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (h1 : k = (@EMPTY K)) : (term1013 A K op ltle k f) = (term1143 A op).
Proof. exact (MK_COMB (@lem6885133 A) (@lem6885132 A K ltle f op k h1)). Qed.
Lemma lem6885136 {K : Type'} (k : K -> Prop) (h1 : k = (@EMPTY K)) : k = (@EMPTY K).
Proof. exact (h1). Qed.
Lemma lem6885137 {A K : Type'} (op : type1400 A) : (@iterate A K op) = (@iterate A K op).
Proof. exact (eq_refl (@iterate A K op)). Qed.
Lemma lem6885138 {A K : Type'} (op : type1400 A) (k : K -> Prop) (h1 : k = (@EMPTY K)) : (@iterate A K op k) = (@iterate A K op (@EMPTY K)).
Proof. exact (MK_COMB (@lem6885137 A K op) (@lem6885136 K k h1)). Qed.
Lemma lem6885139 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6885140 {A K : Type'} (op : type1400 A) (f : K -> A) (k : K -> Prop) (h1 : k = (@EMPTY K)) : (@iterate A K op k f) = (@iterate A K op (@EMPTY K) f).
Proof. exact (MK_COMB (@lem6885138 A K op k h1) (@lem6885139 A K f)). Qed.
Lemma lem6885142 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term1144 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6885001 _120477 _120519 f op h0). Qed.
Lemma lem6885143 {A K : Type'} (f : K -> A) (op : type1400 A) : term1145 A K f op.
Proof. exact (@lem6885142 K A f op). Qed.
Lemma lem6885145 {A : Type'} (op : type1400 A) (h1 : @monoidal A op) : (@monoidal A op) = True.
Proof. exact (EQ_MP (@lem6885007 A op) (@lem6884878 A op h1)). Qed.
Lemma lem6885146 {A : Type'} (op : type1400 A) (h1 : @monoidal A op) : True = (@monoidal A op).
Proof. exact (SYM (@lem6885145 A op h1)). Qed.
Lemma lem6885147 {A : Type'} (op : type1400 A) (h1 : @monoidal A op) : @monoidal A op.
Proof. exact (EQ_MP (@lem6885146 A op h1) (@lem0)). Qed.
Lemma lem6885148 {A K : Type'} (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : (@iterate A K op (@EMPTY K) f) = (@neutral A op).
Proof. exact (@lem6885143 A K f op (@lem6885147 A op h1)). Qed.
Lemma lem6885149 {A K : Type'} (f : K -> A) (op : type1400 A) (k : K -> Prop) (h1 : @monoidal A op) (h2 : k = (@EMPTY K)) : (@iterate A K op k f) = (@neutral A op).
Proof. exact (TRANS (@lem6885140 A K op f k h2) (@lem6885148 A K f op h1)). Qed.
Lemma lem6885150 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (h1 : @monoidal A op) (h2 : k = (@EMPTY K)) : ((term1011 A K op ltle k f) = (@iterate A K op k f)) = ((@neutral A op) = (@neutral A op)).
Proof. exact (MK_COMB (@lem6885134 A K ltle f op k h2) (@lem6885149 A K f op k h1 h2)). Qed.
Lemma lem6885152 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6885153 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem6885152 A x). Qed.
Lemma lem6885154 {A : Type'} (op : type1400 A) : ((@neutral A op) = (@neutral A op)) = True.
Proof. exact (@lem6885153 A (@neutral A op)). Qed.
Lemma lem6885155 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (h1 : @monoidal A op) (h2 : k = (@EMPTY K)) : ((term1011 A K op ltle k f) = (@iterate A K op k f)) = True.
Proof. exact (TRANS (@lem6885150 A K ltle f op k h1 h2) (@lem6885154 A op)). Qed.
Lemma lem6885156 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (h1 : @monoidal A op) (h2 : k = (@EMPTY K)) : True = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (SYM (@lem6885155 A K ltle f op k h1 h2)). Qed.
Lemma lem6885157 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (h1 : @monoidal A op) (h2 : k = (@EMPTY K)) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6885156 A K ltle f op k h1 h2) (@lem0)). Qed.
Lemma lem6885337 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (h1 : term832 A K op ltle f) : term832 A K op ltle f.
Proof. exact (h1). Qed.
Lemma lem6885338 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (h1 : term832 A K op ltle f) : term1146 A K op ltle f.
Proof. exact (proj2 (@lem6885337 A K op ltle f h1)). Qed.
Lemma lem6885339 {A K : Type'} (k : K -> Prop) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (h1 : term832 A K op ltle f) : term1147 A K op ltle f k.
Proof. exact (@lem6885338 A K op ltle f h1 k). Qed.
Lemma lem6885340 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term1147 A K op ltle f k) = (term1148 A K op ltle k f).
Proof. exact (eq_refl (term1147 A K op ltle f k)). Qed.
Lemma lem6885341 {A K : Type'} (k : K -> Prop) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (h1 : term832 A K op ltle f) : term1148 A K op ltle k f.
Proof. exact (EQ_MP (@lem6885340 A K op ltle k f) (@lem6885339 A K k op ltle f h1)). Qed.
Lemma lem6885342 {A : Type'} (s : A -> Prop) : term1149 A s.
Proof. exact (@lem3603906 A s). Qed.
Lemma lem6885343 {A : Type'} (s : A -> Prop) : (term1149 A s) = (term1150 A s).
Proof. exact (eq_refl (term1149 A s)). Qed.
Lemma lem6885344 {A : Type'} (s : A -> Prop) : term1150 A s.
Proof. exact (EQ_MP (@lem6885343 A s) (@lem6885342 A s)). Qed.
Lemma lem6885345 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term1151 A s P.
Proof. exact (@lem6885344 A s P). Qed.
Lemma lem6885346 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term1151 A s P) = (term1152 A s P).
Proof. exact (eq_refl (term1151 A s P)). Qed.
Lemma lem6885347 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term1152 A s P.
Proof. exact (EQ_MP (@lem6885346 A s P) (@lem6885345 A s P)). Qed.
Lemma lem6885348 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6885349 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : term1153 A s P.
Proof. exact (@lem6885347 A s P (@lem6885348 A s h1)). Qed.
Lemma lem6885350 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term1153 A s P) = ((term1153 A s P) = True).
Proof. exact (@lem7 (term1153 A s P)). Qed.
Lemma lem6885351 {A : Type'} (P : A -> Prop) (s : A -> Prop) (h1 : @FINITE A s) : (term1153 A s P) = True.
Proof. exact (EQ_MP (@lem6885350 A s P) (@lem6885349 A P s h1)). Qed.
Lemma lem6885398 {K : Type'} (k : K -> Prop) : (@FINITE K k) = ((@FINITE K k) = True).
Proof. exact (@lem7 (@FINITE K k)). Qed.
Lemma lem6885416 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term1154 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6885417 (p : Prop) (q : Prop) (p' : Prop) : term1155 p q p'.
Proof. exact (fun q' : Prop => @lem6885416 p q p' q'). Qed.
Lemma lem6885418 (p : Prop) (q : Prop) : term1156 p q.
Proof. exact (fun p' : Prop => @lem6885417 p q p'). Qed.
Lemma lem6885419 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : term1157 A K ltle op k f.
Proof. exact (@lem6885418 (term1148 A K op ltle k f) ((term1011 A K op ltle k f) = (@iterate A K op k f))). Qed.
Lemma lem6885420 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) : term1158 A K ltle op k f p'.
Proof. exact (@lem6885419 A K ltle op k f p'). Qed.
Lemma lem6885421 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) : (term1158 A K ltle op k f p') = (term1159 A K ltle op k f p').
Proof. exact (eq_refl (term1158 A K ltle op k f p')). Qed.
Lemma lem6885422 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) : term1159 A K ltle op k f p'.
Proof. exact (EQ_MP (@lem6885421 A K ltle op k f p') (@lem6885420 A K ltle op k f p')). Qed.
Lemma lem6885423 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) (q' : Prop) : term1160 A K ltle op k f p' q'.
Proof. exact (@lem6885422 A K ltle op k f p' q'). Qed.
Lemma lem6885424 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) (q' : Prop) : (term1160 A K ltle op k f p' q') = (term1161 A K ltle op k f p' q').
Proof. exact (eq_refl (term1160 A K ltle op k f p' q')). Qed.
Lemma lem6885425 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) (q' : Prop) : term1161 A K ltle op k f p' q'.
Proof. exact (EQ_MP (@lem6885424 A K ltle op k f p' q') (@lem6885423 A K ltle op k f p' q')). Qed.
Lemma lem6885429 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term1154 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6885430 (p : Prop) (q : Prop) (p' : Prop) : term1155 p q p'.
Proof. exact (fun q' : Prop => @lem6885429 p q p' q'). Qed.
Lemma lem6885431 (p : Prop) (q : Prop) : term1156 p q.
Proof. exact (fun p' : Prop => @lem6885430 p q p'). Qed.
Lemma lem6885432 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : term1162 A K op ltle k f.
Proof. exact (@lem6885431 (term1163 A K k f op) (term1164 A K op ltle k f)). Qed.
Lemma lem6885433 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (p' : Prop) : term1165 A K op ltle k f p'.
Proof. exact (@lem6885432 A K op ltle k f p'). Qed.
Lemma lem6885434 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (p' : Prop) : (term1165 A K op ltle k f p') = (term1166 A K op ltle k f p').
Proof. exact (eq_refl (term1165 A K op ltle k f p')). Qed.
Lemma lem6885435 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (p' : Prop) : term1166 A K op ltle k f p'.
Proof. exact (EQ_MP (@lem6885434 A K op ltle k f p') (@lem6885433 A K op ltle k f p')). Qed.
Lemma lem6885436 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (p' : Prop) (q' : Prop) : term1167 A K op ltle k f p' q'.
Proof. exact (@lem6885435 A K op ltle k f p' q'). Qed.
Lemma lem6885437 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (p' : Prop) (q' : Prop) : (term1167 A K op ltle k f p' q') = (term1168 A K op ltle k f p' q').
Proof. exact (eq_refl (term1167 A K op ltle k f p' q')). Qed.
Lemma lem6885438 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (p' : Prop) (q' : Prop) : term1168 A K op ltle k f p' q'.
Proof. exact (EQ_MP (@lem6885437 A K op ltle k f p' q') (@lem6885436 A K op ltle k f p' q')). Qed.
Lemma lem6885442 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term1169 A s P.
Proof. exact (fun h0 : @FINITE A s => @lem6885351 A P s h0). Qed.
Lemma lem6885443 {K : Type'} (s : K -> Prop) (P : K -> Prop) : term1169 K s P.
Proof. exact (@lem6885442 K s P). Qed.
Lemma lem6885444 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : term1170 A K k f op.
Proof. exact (@lem6885443 K k (term1171 A K f op)). Qed.
Lemma lem6885445 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1172 A K f op i) = (term1015 A K f i op).
Proof. exact (eq_refl (term1172 A K f op i)). Qed.
Lemma lem6885446 {K : Type'} (i : K) (k : K -> Prop) : (term13 K i k) = (term13 K i k).
Proof. exact (eq_refl (term13 K i k)). Qed.
Lemma lem6885447 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) : (term1173 A K k f op i) = (term1024 A K k f i op).
Proof. exact (MK_COMB (@lem6885446 K i k) (@lem6885445 A K f i op)). Qed.
Lemma lem6885448 {K : Type'} (GEN_PVAR_274 : K) : (@SETSPEC K GEN_PVAR_274) = (@SETSPEC K GEN_PVAR_274).
Proof. exact (eq_refl (@SETSPEC K GEN_PVAR_274)). Qed.
Lemma lem6885449 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) : (term1174 A K GEN_PVAR_274 k f op i) = (term1026 A K GEN_PVAR_274 k f i op).
Proof. exact (MK_COMB (@lem6885448 K GEN_PVAR_274) (@lem6885447 A K k f i op)). Qed.
Lemma lem6885450 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6885451 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (i : K) : (term1175 A K GEN_PVAR_274 k f op i) = (term1028 A K GEN_PVAR_274 k f op i).
Proof. exact (MK_COMB (@lem6885449 A K GEN_PVAR_274 k f i op) (@lem6885450 K i)). Qed.
Lemma lem6885452 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1176 A K GEN_PVAR_274 k f op) = (term1030 A K GEN_PVAR_274 k f op).
Proof. exact (fun_ext (fun i : K => @lem6885451 A K GEN_PVAR_274 k f op i)). Qed.
Lemma lem6885453 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6885454 {A K : Type'} (GEN_PVAR_274 : K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1177 A K GEN_PVAR_274 k f op) = (term1032 A K GEN_PVAR_274 k f op).
Proof. exact (MK_COMB (@lem6885453 K) (@lem6885452 A K GEN_PVAR_274 k f op)). Qed.
Lemma lem6885455 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1178 A K k f op) = (term1034 A K k f op).
Proof. exact (fun_ext (fun GEN_PVAR_274 : K => @lem6885454 A K GEN_PVAR_274 k f op)). Qed.
Lemma lem6885456 {K : Type'} : (@GSPEC K) = (@GSPEC K).
Proof. exact (eq_refl (@GSPEC K)). Qed.
Lemma lem6885457 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1179 A K k f op) = (term1036 A K k f op).
Proof. exact (MK_COMB (@lem6885456 K) (@lem6885455 A K k f op)). Qed.
Lemma lem6885458 {K : Type'} : (@FINITE K) = (@FINITE K).
Proof. exact (eq_refl (@FINITE K)). Qed.
Lemma lem6885459 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1180 A K k f op) = (term1038 A K k f op).
Proof. exact (MK_COMB (@lem6885458 K) (@lem6885457 A K k f op)). Qed.
Lemma lem6885460 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6885461 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1181 A K k f op) = (term1182 A K k f op).
Proof. exact (MK_COMB (@lem6885460) (@lem6885459 A K k f op)). Qed.
Lemma lem6885462 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem6885463 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : ((term1180 A K k f op) = True) = ((term1038 A K k f op) = True).
Proof. exact (MK_COMB (@lem6885461 A K k f op) (@lem6885462)). Qed.
Lemma lem6885464 {K : Type'} (k : K -> Prop) : (term1077 K k) = (term1077 K k).
Proof. exact (eq_refl (term1077 K k)). Qed.
Lemma lem6885465 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1170 A K k f op) = (term1183 A K k f op).
Proof. exact (MK_COMB (@lem6885464 K k) (@lem6885463 A K k f op)). Qed.
Lemma lem6885466 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : term1183 A K k f op.
Proof. exact (EQ_MP (@lem6885465 A K k f op) (@lem6885444 A K k f op)). Qed.
Lemma lem6885468 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : (@FINITE K k) = True.
Proof. exact (EQ_MP (@lem6885398 K k) (@lem6884937 K k h1)). Qed.
Lemma lem6885469 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : True = (@FINITE K k).
Proof. exact (SYM (@lem6885468 K k h1)). Qed.
Lemma lem6885470 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : @FINITE K k.
Proof. exact (EQ_MP (@lem6885469 K k h1) (@lem0)). Qed.
Lemma lem6885471 {A K : Type'} (f : K -> A) (op : type1400 A) (k : K -> Prop) (h1 : @FINITE K k) : (term1038 A K k f op) = True.
Proof. exact (@lem6885466 A K k f op (@lem6885470 K k h1)). Qed.
Lemma lem6885472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6885473 {A K : Type'} (f : K -> A) (op : type1400 A) (k : K -> Prop) (h1 : @FINITE K k) : (term1184 A K k f op) = (and True).
Proof. exact (MK_COMB (@lem6885472) (@lem6885471 A K f op k h1)). Qed.
Lemma lem6885482 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1185 A K k f op) = (term1185 A K k f op).
Proof. exact (eq_refl (term1185 A K k f op)). Qed.
Lemma lem6885483 {A K : Type'} (f : K -> A) (op : type1400 A) (k : K -> Prop) (h1 : @FINITE K k) : (term1163 A K k f op) = (term1186 A K k f op).
Proof. exact (MK_COMB (@lem6885473 A K f op k h1) (@lem6885482 A K k f op)). Qed.
Lemma lem6885485 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6885486 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1186 A K k f op) = (term1185 A K k f op).
Proof. exact (@lem6885485 (term1185 A K k f op)). Qed.
Lemma lem6885495 {A K : Type'} (f : K -> A) (op : type1400 A) (k : K -> Prop) (h1 : @FINITE K k) : (term1163 A K k f op) = (term1185 A K k f op).
Proof. exact (TRANS (@lem6885483 A K f op k h1) (@lem6885486 A K k f op)). Qed.
Lemma lem6885496 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (q' : Prop) : term1187 A K ltle k f op q'.
Proof. exact (@lem6885438 A K op ltle k f (term1185 A K k f op) q'). Qed.
Lemma lem6885497 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (q' : Prop) (k : K -> Prop) (h1 : @FINITE K k) : term1188 A K ltle k f op q'.
Proof. exact (@lem6885496 A K ltle k f op q' (@lem6885495 A K f op k h1)). Qed.
Lemma lem6885592 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term1164 A K op ltle k f) = (term1164 A K op ltle k f).
Proof. exact (eq_refl (term1164 A K op ltle k f)). Qed.
Lemma lem6885593 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : term1189 A K op ltle k f.
Proof. exact (fun h0 : term1185 A K k f op => @lem6885592 A K op ltle k f). Qed.
Lemma lem6885594 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (k : K -> Prop) (h1 : @FINITE K k) : term1190 A K op ltle k f.
Proof. exact (@lem6885497 A K ltle f op (term1164 A K op ltle k f) k h1). Qed.
Lemma lem6885595 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (k : K -> Prop) (h1 : @FINITE K k) : (term1148 A K op ltle k f) = (term1191 A K op ltle k f).
Proof. exact (@lem6885594 A K op ltle f k h1 (@lem6885593 A K op ltle k f)). Qed.
Lemma lem6885806 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (q' : Prop) : term1192 A K op ltle k f q'.
Proof. exact (@lem6885425 A K ltle op k f (term1191 A K op ltle k f) q'). Qed.
Lemma lem6885807 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (q' : Prop) (k : K -> Prop) (h1 : @FINITE K k) : term1193 A K op ltle k f q'.
Proof. exact (@lem6885806 A K op ltle k f q' (@lem6885595 A K op ltle f k h1)). Qed.
Lemma lem6885874 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : ((term1011 A K op ltle k f) = (@iterate A K op k f)) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (eq_refl ((term1011 A K op ltle k f) = (@iterate A K op k f))). Qed.
Lemma lem6885875 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : term1194 A K ltle op k f.
Proof. exact (fun h0 : term1191 A K op ltle k f => @lem6885874 A K ltle op k f). Qed.
Lemma lem6885876 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) (k : K -> Prop) (h1 : @FINITE K k) : term1195 A K ltle op k f.
Proof. exact (@lem6885807 A K op ltle f ((term1011 A K op ltle k f) = (@iterate A K op k f)) k h1). Qed.
Lemma lem6885877 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) (k : K -> Prop) (h1 : @FINITE K k) : (term1196 A K ltle op k f) = (term1197 A K ltle op k f).
Proof. exact (@lem6885876 A K ltle op f k h1 (@lem6885875 A K ltle op k f)). Qed.
Lemma lem6886440 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) (k : K -> Prop) (h1 : @FINITE K k) : (term1197 A K ltle op k f) = (term1196 A K ltle op k f).
Proof. exact (SYM (@lem6885877 A K ltle op f k h1)). Qed.
Lemma lem6886442 (p : Prop) (q : Prop) (r : Prop) : term783 p q r.
Proof. exact (@lem6883588 p q r (@lem6883580 p q r)). Qed.
Lemma lem6886443 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : term1198 A K ltle op k f.
Proof. exact (@lem6886442 ((term1036 A K k f op) = (@EMPTY K)) (term1164 A K op ltle k f) ((term1011 A K op ltle k f) = (@iterate A K op k f))). Qed.
Lemma lem6886459 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (@iterato A K dom neut op ltle k f) = (term742 A K op ltle k dom neut f).
Proof. exact (EQ_MP (@lem6883361 A K op ltle k dom neut f) (@lem6883360 A K op ltle k dom neut f)). Qed.
Lemma lem6886460 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (f : K -> A) : (@iterato A K dom neut op ltle k f) = (term742 A K op ltle k dom neut f).
Proof. exact (@lem6886459 A K op ltle k dom neut f). Qed.
Lemma lem6886461 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (f : K -> A) : (term1011 A K op ltle k f) = (term1044 A K ltle k op f).
Proof. exact (@lem6886460 A K op ltle k (@UNIV A) (@neutral A op) f). Qed.
Lemma lem6886462 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6886463 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (f : K -> A) : (term1013 A K op ltle k f) = (term1199 A K ltle k op f).
Proof. exact (MK_COMB (@lem6886462 A) (@lem6886461 A K ltle k op f)). Qed.
Lemma lem6886465 {_120296 _120308 : Type'} (op : type1400 _120296) (s : _120308 -> Prop) (f : _120308 -> _120296) : (@iterate _120296 _120308 op s f) = (term729 _120296 _120308 op s f).
Proof. exact (EQ_MP (@lem6883343 _120296 _120308 op s f) (@lem6883342 _120296 _120308 op f s)). Qed.
Lemma lem6886466 {A K : Type'} (op : type1400 A) (s : K -> Prop) (f : K -> A) : (@iterate A K op s f) = (term729 A K op s f).
Proof. exact (@lem6886465 A K op s f). Qed.
Lemma lem6886467 {A K : Type'} (op : type1400 A) (k : K -> Prop) (f : K -> A) : (@iterate A K op k f) = (term729 A K op k f).
Proof. exact (@lem6886466 A K op k f). Qed.
Lemma lem6886468 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : ((term1011 A K op ltle k f) = (@iterate A K op k f)) = ((term1044 A K ltle k op f) = (term729 A K op k f)).
Proof. exact (MK_COMB (@lem6886463 A K ltle k op f) (@lem6886467 A K op k f)). Qed.
Lemma lem6886469 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1200 A K k f op) = (term1200 A K k f op).
Proof. exact (eq_refl (term1200 A K k f op)). Qed.
Lemma lem6886470 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1201 A K ltle op k f) = (term1202 A K ltle op k f).
Proof. exact (MK_COMB (@lem6886469 A K k f op) (@lem6886468 A K ltle op k f)). Qed.
Lemma lem6886471 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1202 A K ltle op k f) = (term1201 A K ltle op k f).
Proof. exact (SYM (@lem6886470 A K ltle op k f)). Qed.
Lemma lem6886485 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term720 A x s t) = (term721 A s x t).
Proof. exact (EQ_MP (@lem6883272 A s x t) (@lem6883271 A s t x)). Qed.
Lemma lem6886486 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term720 A x s t) = (term721 A s x t).
Proof. exact (@lem6886485 A s x t). Qed.
Lemma lem6886487 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1015 A K f i op) = (term1016 A K f i op).
Proof. exact (@lem6886486 A (@UNIV A) (f i) (term1017 A op)). Qed.
Lemma lem6886491 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem6883277 A x) (@lem6883276 A x)). Qed.
Lemma lem6886492 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem6886491 A x). Qed.
Lemma lem6886493 {A K : Type'} (f : K -> A) (i : K) : (term1018 A K f i) = True.
Proof. exact (@lem6886492 A (f i)). Qed.
Lemma lem6886494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6886495 {A K : Type'} (f : K -> A) (i : K) : (term1019 A K f i) = (and True).
Proof. exact (MK_COMB (@lem6886494) (@lem6886493 A K f i)). Qed.
Lemma lem6886497 {A : Type'} (x : A) (y : A) : (term714 A x y) = (x = y).
Proof. exact (EQ_MP (@lem6883263 A x y) (@lem6883262 A x y)). Qed.
Lemma lem6886498 {A : Type'} (x : A) (y : A) : (term714 A x y) = (x = y).
Proof. exact (@lem6886497 A x y). Qed.
Lemma lem6886499 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1020 A K f i op) = ((f i) = (@neutral A op)).
Proof. exact (@lem6886498 A (f i) (@neutral A op)). Qed.
Lemma lem6886502 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6886503 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1021 A K f i op) = (term1022 A K f i op).
Proof. exact (MK_COMB (@lem6886502) (@lem6886499 A K f i op)). Qed.
Lemma lem6886504 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1016 A K f i op) = (term1023 A K f i op).
Proof. exact (MK_COMB (@lem6886495 A K f i) (@lem6886503 A K f i op)). Qed.
Lemma lem6886506 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6886507 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1023 A K f i op) = (term1022 A K f i op).
Proof. exact (@lem6886506 (term1022 A K f i op)). Qed.
Lemma lem6886510 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1016 A K f i op) = (term1022 A K f i op).
Proof. exact (TRANS (@lem6886504 A K f i op) (@lem6886507 A K f i op)). Qed.
Lemma lem6886511 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1015 A K f i op) = (term1022 A K f i op).
Proof. exact (TRANS (@lem6886487 A K f i op) (@lem6886510 A K f i op)). Qed.
Lemma lem6886512 {K : Type'} (i : K) (k : K -> Prop) : (term13 K i k) = (term13 K i k).
Proof. exact (eq_refl (term13 K i k)). Qed.
Lemma lem6886513 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) : (term1024 A K k f i op) = (term1025 A K k f i op).
Proof. exact (MK_COMB (@lem6886512 K i k) (@lem6886511 A K f i op)). Qed.
Lemma lem6886516 {K : Type'} (GEN_PVAR_275 : K) : (@SETSPEC K GEN_PVAR_275) = (@SETSPEC K GEN_PVAR_275).
Proof. exact (eq_refl (@SETSPEC K GEN_PVAR_275)). Qed.
Lemma lem6886517 {A K : Type'} (GEN_PVAR_275 : K) (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) : (term1026 A K GEN_PVAR_275 k f i op) = (term1027 A K GEN_PVAR_275 k f i op).
Proof. exact (MK_COMB (@lem6886516 K GEN_PVAR_275) (@lem6886513 A K k f i op)). Qed.
Lemma lem6886518 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6886519 {A K : Type'} (GEN_PVAR_275 : K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (i : K) : (term1028 A K GEN_PVAR_275 k f op i) = (term1029 A K GEN_PVAR_275 k f op i).
Proof. exact (MK_COMB (@lem6886517 A K GEN_PVAR_275 k f i op) (@lem6886518 K i)). Qed.
Lemma lem6886520 {A K : Type'} (GEN_PVAR_275 : K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1030 A K GEN_PVAR_275 k f op) = (term1031 A K GEN_PVAR_275 k f op).
Proof. exact (fun_ext (fun i : K => @lem6886519 A K GEN_PVAR_275 k f op i)). Qed.
Lemma lem6886521 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6886522 {A K : Type'} (GEN_PVAR_275 : K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1032 A K GEN_PVAR_275 k f op) = (term1033 A K GEN_PVAR_275 k f op).
Proof. exact (MK_COMB (@lem6886521 K) (@lem6886520 A K GEN_PVAR_275 k f op)). Qed.
Lemma lem6886527 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1034 A K k f op) = (term1035 A K k f op).
Proof. exact (fun_ext (fun GEN_PVAR_275 : K => @lem6886522 A K GEN_PVAR_275 k f op)). Qed.
Lemma lem6886528 {K : Type'} : (@GSPEC K) = (@GSPEC K).
Proof. exact (eq_refl (@GSPEC K)). Qed.
Lemma lem6886529 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1036 A K k f op) = (term1037 A K k f op).
Proof. exact (MK_COMB (@lem6886528 K) (@lem6886527 A K k f op)). Qed.
Lemma lem6886530 {K : Type'} : (@eq (K -> Prop)) = (@eq (K -> Prop)).
Proof. exact (eq_refl (@eq (K -> Prop))). Qed.
Lemma lem6886531 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1203 A K k f op) = (term1204 A K k f op).
Proof. exact (MK_COMB (@lem6886530 K) (@lem6886529 A K k f op)). Qed.
Lemma lem6886532 {K : Type'} : (@EMPTY K) = (@EMPTY K).
Proof. exact (eq_refl (@EMPTY K)). Qed.
Lemma lem6886533 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : ((term1036 A K k f op) = (@EMPTY K)) = ((term1037 A K k f op) = (@EMPTY K)).
Proof. exact (MK_COMB (@lem6886531 A K k f op) (@lem6886532 K)). Qed.
Lemma lem6886536 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6886537 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1200 A K k f op) = (term1205 A K k f op).
Proof. exact (MK_COMB (@lem6886536) (@lem6886533 A K k f op)). Qed.
Lemma lem6886547 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term720 A x s t) = (term721 A s x t).
Proof. exact (EQ_MP (@lem6883272 A s x t) (@lem6883271 A s t x)). Qed.
Lemma lem6886548 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term720 A x s t) = (term721 A s x t).
Proof. exact (@lem6886547 A s x t). Qed.
Lemma lem6886549 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1015 A K f i op) = (term1016 A K f i op).
Proof. exact (@lem6886548 A (@UNIV A) (f i) (term1017 A op)). Qed.
Lemma lem6886553 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem6883277 A x) (@lem6883276 A x)). Qed.
Lemma lem6886554 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem6886553 A x). Qed.
Lemma lem6886555 {A K : Type'} (f : K -> A) (i : K) : (term1018 A K f i) = True.
Proof. exact (@lem6886554 A (f i)). Qed.
Lemma lem6886556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6886557 {A K : Type'} (f : K -> A) (i : K) : (term1019 A K f i) = (and True).
Proof. exact (MK_COMB (@lem6886556) (@lem6886555 A K f i)). Qed.
Lemma lem6886559 {A : Type'} (x : A) (y : A) : (term714 A x y) = (x = y).
Proof. exact (EQ_MP (@lem6883263 A x y) (@lem6883262 A x y)). Qed.
Lemma lem6886560 {A : Type'} (x : A) (y : A) : (term714 A x y) = (x = y).
Proof. exact (@lem6886559 A x y). Qed.
Lemma lem6886561 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1020 A K f i op) = ((f i) = (@neutral A op)).
Proof. exact (@lem6886560 A (f i) (@neutral A op)). Qed.
Lemma lem6886564 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6886565 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1021 A K f i op) = (term1022 A K f i op).
Proof. exact (MK_COMB (@lem6886564) (@lem6886561 A K f i op)). Qed.
Lemma lem6886566 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1016 A K f i op) = (term1023 A K f i op).
Proof. exact (MK_COMB (@lem6886557 A K f i) (@lem6886565 A K f i op)). Qed.
Lemma lem6886568 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6886569 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1023 A K f i op) = (term1022 A K f i op).
Proof. exact (@lem6886568 (term1022 A K f i op)). Qed.
Lemma lem6886572 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1016 A K f i op) = (term1022 A K f i op).
Proof. exact (TRANS (@lem6886566 A K f i op) (@lem6886569 A K f i op)). Qed.
Lemma lem6886573 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1015 A K f i op) = (term1022 A K f i op).
Proof. exact (TRANS (@lem6886549 A K f i op) (@lem6886572 A K f i op)). Qed.
Lemma lem6886574 {K : Type'} (i : K) (k : K -> Prop) : (term13 K i k) = (term13 K i k).
Proof. exact (eq_refl (term13 K i k)). Qed.
Lemma lem6886575 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) : (term1024 A K k f i op) = (term1025 A K k f i op).
Proof. exact (MK_COMB (@lem6886574 K i k) (@lem6886573 A K f i op)). Qed.
Lemma lem6886578 {K : Type'} (GEN_PVAR_268 : K) : (@SETSPEC K GEN_PVAR_268) = (@SETSPEC K GEN_PVAR_268).
Proof. exact (eq_refl (@SETSPEC K GEN_PVAR_268)). Qed.
Lemma lem6886579 {A K : Type'} (GEN_PVAR_268 : K) (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) : (term1026 A K GEN_PVAR_268 k f i op) = (term1027 A K GEN_PVAR_268 k f i op).
Proof. exact (MK_COMB (@lem6886578 K GEN_PVAR_268) (@lem6886575 A K k f i op)). Qed.
Lemma lem6886580 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6886581 {A K : Type'} (GEN_PVAR_268 : K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (i : K) : (term1028 A K GEN_PVAR_268 k f op i) = (term1029 A K GEN_PVAR_268 k f op i).
Proof. exact (MK_COMB (@lem6886579 A K GEN_PVAR_268 k f i op) (@lem6886580 K i)). Qed.
Lemma lem6886582 {A K : Type'} (GEN_PVAR_268 : K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1030 A K GEN_PVAR_268 k f op) = (term1031 A K GEN_PVAR_268 k f op).
Proof. exact (fun_ext (fun i : K => @lem6886581 A K GEN_PVAR_268 k f op i)). Qed.
Lemma lem6886583 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6886584 {A K : Type'} (GEN_PVAR_268 : K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1032 A K GEN_PVAR_268 k f op) = (term1033 A K GEN_PVAR_268 k f op).
Proof. exact (MK_COMB (@lem6886583 K) (@lem6886582 A K GEN_PVAR_268 k f op)). Qed.
Lemma lem6886589 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1034 A K k f op) = (term1035 A K k f op).
Proof. exact (fun_ext (fun GEN_PVAR_268 : K => @lem6886584 A K GEN_PVAR_268 k f op)). Qed.
Lemma lem6886590 {K : Type'} : (@GSPEC K) = (@GSPEC K).
Proof. exact (eq_refl (@GSPEC K)). Qed.
Lemma lem6886591 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1036 A K k f op) = (term1037 A K k f op).
Proof. exact (MK_COMB (@lem6886590 K) (@lem6886589 A K k f op)). Qed.
Lemma lem6886592 {A K : Type'} (op : type1400 A) (ltle : type1402 K) : (term1003 A K op ltle) = (term1003 A K op ltle).
Proof. exact (eq_refl (term1003 A K op ltle)). Qed.
Lemma lem6886593 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1042 A K ltle k f op) = (term1043 A K ltle k f op).
Proof. exact (MK_COMB (@lem6886592 A K op ltle) (@lem6886591 A K k f op)). Qed.
Lemma lem6886594 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6886595 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (f : K -> A) : (term1044 A K ltle k op f) = (term1045 A K ltle k op f).
Proof. exact (MK_COMB (@lem6886593 A K ltle k f op) (@lem6886594 A K f)). Qed.
Lemma lem6886596 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6886597 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (f : K -> A) : (term1199 A K ltle k op f) = (term1206 A K ltle k op f).
Proof. exact (MK_COMB (@lem6886596 A) (@lem6886595 A K ltle k op f)). Qed.
Lemma lem6886599 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term728 A B s f op).
Proof. exact (EQ_MP (@lem6883286 A B s f op) (@lem6883285 A B s f op)). Qed.
Lemma lem6886600 {A K : Type'} (s : K -> Prop) (f : K -> A) (op : type1400 A) : (@support K A op f s) = (term1037 A K s f op).
Proof. exact (@lem6886599 K A s f op). Qed.
Lemma lem6886601 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (@support K A op f k) = (term1037 A K k f op).
Proof. exact (@lem6886600 A K k f op). Qed.
Lemma lem6886610 {A K : Type'} (op : type1400 A) : (@iterate A K op) = (@iterate A K op).
Proof. exact (eq_refl (@iterate A K op)). Qed.
Lemma lem6886611 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1052 A K op f k) = (term1053 A K k f op).
Proof. exact (MK_COMB (@lem6886610 A K op) (@lem6886601 A K k f op)). Qed.
Lemma lem6886612 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6886613 {A K : Type'} (k : K -> Prop) (op : type1400 A) (f : K -> A) : (term729 A K op k f) = (term1054 A K k op f).
Proof. exact (MK_COMB (@lem6886611 A K k f op) (@lem6886612 A K f)). Qed.
Lemma lem6886614 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (f : K -> A) : ((term1044 A K ltle k op f) = (term729 A K op k f)) = ((term1045 A K ltle k op f) = (term1054 A K k op f)).
Proof. exact (MK_COMB (@lem6886597 A K ltle k op f) (@lem6886613 A K k op f)). Qed.
Lemma lem6886617 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (f : K -> A) : (term1202 A K ltle op k f) = (term1207 A K ltle k op f).
Proof. exact (MK_COMB (@lem6886537 A K k f op) (@lem6886614 A K ltle k op f)). Qed.
Lemma lem6886622 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1207 A K ltle k op f) = (term1202 A K ltle op k f).
Proof. exact (SYM (@lem6886617 A K ltle k op f)). Qed.
Lemma lem6886623 {A K : Type'} (dom : A -> Prop) : term1128 A K dom.
Proof. exact (@lem6790065 A K dom). Qed.
Lemma lem6886624 {A K : Type'} (dom : A -> Prop) : (term1128 A K dom) = (term1129 A K dom).
Proof. exact (eq_refl (term1128 A K dom)). Qed.
Lemma lem6886625 {A K : Type'} (dom : A -> Prop) : term1129 A K dom.
Proof. exact (EQ_MP (@lem6886624 A K dom) (@lem6886623 A K dom)). Qed.
Lemma lem6886626 {A K : Type'} (dom : A -> Prop) (neut : A) : term1130 A K dom neut.
Proof. exact (@lem6886625 A K dom neut). Qed.
Lemma lem6886627 {A K : Type'} (dom : A -> Prop) (neut : A) : (term1130 A K dom neut) = (term1131 A K dom neut).
Proof. exact (eq_refl (term1130 A K dom neut)). Qed.
Lemma lem6886628 {A K : Type'} (dom : A -> Prop) (neut : A) : term1131 A K dom neut.
Proof. exact (EQ_MP (@lem6886627 A K dom neut) (@lem6886626 A K dom neut)). Qed.
Lemma lem6886629 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term1132 A K dom neut op.
Proof. exact (@lem6886628 A K dom neut op). Qed.
Lemma lem6886630 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : (term1132 A K dom neut op) = (term1133 A K dom neut op).
Proof. exact (eq_refl (term1132 A K dom neut op)). Qed.
Lemma lem6886631 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term1133 A K dom neut op.
Proof. exact (EQ_MP (@lem6886630 A K dom neut op) (@lem6886629 A K dom neut op)). Qed.
Lemma lem6886632 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : term1134 A K dom neut op ltle.
Proof. exact (@lem6886631 A K dom neut op ltle). Qed.
Lemma lem6886633 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : (term1134 A K dom neut op ltle) = (term1135 A K dom neut op ltle).
Proof. exact (eq_refl (term1134 A K dom neut op ltle)). Qed.
Lemma lem6886634 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : term1135 A K dom neut op ltle.
Proof. exact (EQ_MP (@lem6886633 A K dom neut op ltle) (@lem6886632 A K dom neut op ltle)). Qed.
Lemma lem6886635 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term1136 A K dom neut op ltle f.
Proof. exact (@lem6886634 A K dom neut op ltle f). Qed.
Lemma lem6886636 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : (term1136 A K dom neut op ltle f) = (term1137 A K dom neut op ltle f).
Proof. exact (eq_refl (term1136 A K dom neut op ltle f)). Qed.
Lemma lem6886637 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term1137 A K dom neut op ltle f.
Proof. exact (EQ_MP (@lem6886636 A K dom neut op ltle f) (@lem6886635 A K dom neut op ltle f)). Qed.
Lemma lem6886652 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term79 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem6886653 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term79 _120477 _120519 _120521 op) = (term80 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term79 _120477 _120519 _120521 op)). Qed.
Lemma lem6886654 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term80 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6886653 _120477 _120519 _120521 op) (@lem6886652 _120477 _120519 _120521 op)). Qed.
Lemma lem6886655 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem6886656 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term1138 _120477 _120519 _120521 op.
Proof. exact (@lem6886654 _120477 _120519 _120521 op (@lem6886655 _120519 op h1)). Qed.
Lemma lem6886679 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term1139 _120477 _120519 op.
Proof. exact (proj1 (@lem6886656 _120477 _120519 Prop op h1)). Qed.
Lemma lem6886680 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term1140 _120477 _120519 op f.
Proof. exact (@lem6886679 _120477 _120519 op h1 f). Qed.
Lemma lem6886681 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : (term1140 _120477 _120519 op f) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl (term1140 _120477 _120519 op f)). Qed.
Lemma lem6886682 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (EQ_MP (@lem6886681 _120477 _120519 f op) (@lem6886680 _120477 _120519 f op h1)). Qed.
Lemma lem6886688 {A : Type'} (op : type1400 A) : (@monoidal A op) = ((@monoidal A op) = True).
Proof. exact (@lem7 (@monoidal A op)). Qed.
Lemma lem6886749 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term1154 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6886750 (p : Prop) (q : Prop) (p' : Prop) : term1155 p q p'.
Proof. exact (fun q' : Prop => @lem6886749 p q p' q'). Qed.
Lemma lem6886751 (p : Prop) (q : Prop) : term1156 p q.
Proof. exact (fun p' : Prop => @lem6886750 p q p'). Qed.
Lemma lem6886752 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (f : K -> A) : term1208 A K ltle k op f.
Proof. exact (@lem6886751 ((term1037 A K k f op) = (@EMPTY K)) ((term1045 A K ltle k op f) = (term1054 A K k op f))). Qed.
Lemma lem6886753 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (f : K -> A) (p' : Prop) : term1209 A K ltle k op f p'.
Proof. exact (@lem6886752 A K ltle k op f p'). Qed.
Lemma lem6886754 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (f : K -> A) (p' : Prop) : (term1209 A K ltle k op f p') = (term1210 A K ltle k op f p').
Proof. exact (eq_refl (term1209 A K ltle k op f p')). Qed.
Lemma lem6886755 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (f : K -> A) (p' : Prop) : term1210 A K ltle k op f p'.
Proof. exact (EQ_MP (@lem6886754 A K ltle k op f p') (@lem6886753 A K ltle k op f p')). Qed.
Lemma lem6886756 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (f : K -> A) (p' : Prop) (q' : Prop) : term1211 A K ltle k op f p' q'.
Proof. exact (@lem6886755 A K ltle k op f p' q'). Qed.
Lemma lem6886757 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (f : K -> A) (p' : Prop) (q' : Prop) : (term1211 A K ltle k op f p' q') = (term1212 A K ltle k op f p' q').
Proof. exact (eq_refl (term1211 A K ltle k op f p' q')). Qed.
Lemma lem6886758 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (f : K -> A) (p' : Prop) (q' : Prop) : term1212 A K ltle k op f p' q'.
Proof. exact (EQ_MP (@lem6886757 A K ltle k op f p' q') (@lem6886756 A K ltle k op f p' q')). Qed.
Lemma lem6886769 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : ((term1037 A K k f op) = (@EMPTY K)) = ((term1037 A K k f op) = (@EMPTY K)).
Proof. exact (eq_refl ((term1037 A K k f op) = (@EMPTY K))). Qed.
Lemma lem6886770 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (q' : Prop) : term1213 A K ltle k f op q'.
Proof. exact (@lem6886758 A K ltle k op f ((term1037 A K k f op) = (@EMPTY K)) q'). Qed.
Lemma lem6886771 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (q' : Prop) : term1214 A K ltle k f op q'.
Proof. exact (@lem6886770 A K ltle k f op q' (@lem6886769 A K k f op)). Qed.
Lemma lem6886841 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : (term1037 A K k f op) = (@EMPTY K)) : (term1037 A K k f op) = (@EMPTY K).
Proof. exact (h1). Qed.
Lemma lem6886842 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : (term1037 A K k f op) = (@EMPTY K)) : (term1037 A K k f op) = (@EMPTY K).
Proof. exact (@lem6886841 A K k f op h1). Qed.
Lemma lem6886843 {A K : Type'} (op : type1400 A) (ltle : type1402 K) : (term1003 A K op ltle) = (term1003 A K op ltle).
Proof. exact (eq_refl (term1003 A K op ltle)). Qed.
Lemma lem6886844 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : (term1037 A K k f op) = (@EMPTY K)) : (term1043 A K ltle k f op) = (term1141 A K op ltle).
Proof. exact (MK_COMB (@lem6886843 A K op ltle) (@lem6886842 A K k f op h1)). Qed.
Lemma lem6886845 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6886846 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : (term1037 A K k f op) = (@EMPTY K)) : (term1045 A K ltle k op f) = (term1142 A K op ltle f).
Proof. exact (MK_COMB (@lem6886844 A K ltle k f op h1) (@lem6886845 A K f)). Qed.
Lemma lem6886864 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (neut : A) : (@iterato A K dom neut op ltle (@EMPTY K) f) = neut.
Proof. exact (proj1 (@lem6886637 A K dom neut op ltle f)). Qed.
Lemma lem6886865 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (neut : A) : (@iterato A K dom neut op ltle (@EMPTY K) f) = neut.
Proof. exact (@lem6886864 A K dom op ltle f neut). Qed.
Lemma lem6886866 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) : (term1142 A K op ltle f) = (@neutral A op).
Proof. exact (@lem6886865 A K (@UNIV A) op ltle f (@neutral A op)). Qed.
Lemma lem6886867 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : (term1037 A K k f op) = (@EMPTY K)) : (term1045 A K ltle k op f) = (@neutral A op).
Proof. exact (TRANS (@lem6886846 A K ltle k f op h1) (@lem6886866 A K ltle f op)). Qed.
Lemma lem6886868 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6886869 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : (term1037 A K k f op) = (@EMPTY K)) : (term1206 A K ltle k op f) = (term1143 A op).
Proof. exact (MK_COMB (@lem6886868 A) (@lem6886867 A K ltle k f op h1)). Qed.
Lemma lem6886871 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : (term1037 A K k f op) = (@EMPTY K)) : (term1037 A K k f op) = (@EMPTY K).
Proof. exact (h1). Qed.
Lemma lem6886872 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : (term1037 A K k f op) = (@EMPTY K)) : (term1037 A K k f op) = (@EMPTY K).
Proof. exact (@lem6886871 A K k f op h1). Qed.
Lemma lem6886873 {A K : Type'} (op : type1400 A) : (@iterate A K op) = (@iterate A K op).
Proof. exact (eq_refl (@iterate A K op)). Qed.
Lemma lem6886874 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : (term1037 A K k f op) = (@EMPTY K)) : (term1053 A K k f op) = (@iterate A K op (@EMPTY K)).
Proof. exact (MK_COMB (@lem6886873 A K op) (@lem6886872 A K k f op h1)). Qed.
Lemma lem6886875 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6886876 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : (term1037 A K k f op) = (@EMPTY K)) : (term1054 A K k op f) = (@iterate A K op (@EMPTY K) f).
Proof. exact (MK_COMB (@lem6886874 A K k f op h1) (@lem6886875 A K f)). Qed.
Lemma lem6886878 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term1144 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem6886682 _120477 _120519 f op h0). Qed.
Lemma lem6886879 {A K : Type'} (f : K -> A) (op : type1400 A) : term1145 A K f op.
Proof. exact (@lem6886878 K A f op). Qed.
Lemma lem6886881 {A : Type'} (op : type1400 A) (h1 : @monoidal A op) : (@monoidal A op) = True.
Proof. exact (EQ_MP (@lem6886688 A op) (@lem6884878 A op h1)). Qed.
Lemma lem6886882 {A : Type'} (op : type1400 A) (h1 : @monoidal A op) : True = (@monoidal A op).
Proof. exact (SYM (@lem6886881 A op h1)). Qed.
Lemma lem6886883 {A : Type'} (op : type1400 A) (h1 : @monoidal A op) : @monoidal A op.
Proof. exact (EQ_MP (@lem6886882 A op h1) (@lem0)). Qed.
Lemma lem6886884 {A K : Type'} (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : (@iterate A K op (@EMPTY K) f) = (@neutral A op).
Proof. exact (@lem6886879 A K f op (@lem6886883 A op h1)). Qed.
Lemma lem6886885 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) (h2 : (term1037 A K k f op) = (@EMPTY K)) : (term1054 A K k op f) = (@neutral A op).
Proof. exact (TRANS (@lem6886876 A K k f op h2) (@lem6886884 A K f op h1)). Qed.
Lemma lem6886886 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) (h2 : (term1037 A K k f op) = (@EMPTY K)) : ((term1045 A K ltle k op f) = (term1054 A K k op f)) = ((@neutral A op) = (@neutral A op)).
Proof. exact (MK_COMB (@lem6886869 A K ltle k f op h2) (@lem6886885 A K k f op h1 h2)). Qed.
Lemma lem6886888 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6886889 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem6886888 A x). Qed.
Lemma lem6886890 {A : Type'} (op : type1400 A) : ((@neutral A op) = (@neutral A op)) = True.
Proof. exact (@lem6886889 A (@neutral A op)). Qed.
Lemma lem6886891 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) (h2 : (term1037 A K k f op) = (@EMPTY K)) : ((term1045 A K ltle k op f) = (term1054 A K k op f)) = True.
Proof. exact (TRANS (@lem6886886 A K ltle k f op h1 h2) (@lem6886890 A op)). Qed.
Lemma lem6886892 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : term1215 A K ltle k op f.
Proof. exact (fun h0 : (term1037 A K k f op) = (@EMPTY K) => @lem6886891 A K ltle k f op h1 h0). Qed.
Lemma lem6886893 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) : term1216 A K ltle k f op.
Proof. exact (@lem6886771 A K ltle k f op True). Qed.
Lemma lem6886894 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : (term1207 A K ltle k op f) = (term1217 A K k f op).
Proof. exact (@lem6886893 A K ltle k f op (@lem6886892 A K ltle k f op h1)). Qed.
Lemma lem6886898 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6886899 {A K : Type'} (k : K -> Prop) (f : K -> A) (op : type1400 A) : (term1217 A K k f op) = True.
Proof. exact (@lem6886898 ((term1037 A K k f op) = (@EMPTY K))). Qed.
Lemma lem6886900 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : (term1207 A K ltle k op f) = True.
Proof. exact (TRANS (@lem6886894 A K ltle k f op h1) (@lem6886899 A K k f op)). Qed.
Lemma lem6886901 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : True = (term1207 A K ltle k op f).
Proof. exact (SYM (@lem6886900 A K ltle k f op h1)). Qed.
Lemma lem6886902 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : term1207 A K ltle k op f.
Proof. exact (EQ_MP (@lem6886901 A K ltle k f op h1) (@lem0)). Qed.
Lemma lem6886903 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : term1202 A K ltle op k f.
Proof. exact (EQ_MP (@lem6886622 A K ltle op k f) (@lem6886902 A K ltle k f op h1)). Qed.
Lemma lem6886904 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : term1201 A K ltle op k f.
Proof. exact (EQ_MP (@lem6886471 A K ltle op k f) (@lem6886903 A K ltle k f op h1)). Qed.
Lemma lem6886905 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (h1 : term1164 A K op ltle k f) : term1164 A K op ltle k f.
Proof. exact (h1). Qed.
Lemma lem6886906 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) (h1 : term1218 A K op ltle k i f) : term1218 A K op ltle k i f.
Proof. exact (h1). Qed.
Lemma lem6886914 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term720 A x s t) = (term721 A s x t).
Proof. exact (EQ_MP (@lem6883257 A s x t) (@lem6883256 A s t x)). Qed.
Lemma lem6886915 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term720 A x s t) = (term721 A s x t).
Proof. exact (@lem6886914 A s x t). Qed.
Lemma lem6886916 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1015 A K f i op) = (term1016 A K f i op).
Proof. exact (@lem6886915 A (@UNIV A) (f i) (term1017 A op)). Qed.
Lemma lem6886920 {A : Type'} (x : A) (y : A) : (term714 A x y) = (x = y).
Proof. exact (EQ_MP (@lem6883248 A x y) (@lem6883247 A x y)). Qed.
Lemma lem6886921 {A : Type'} (x : A) (y : A) : (term714 A x y) = (x = y).
Proof. exact (@lem6886920 A x y). Qed.
Lemma lem6886922 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1020 A K f i op) = ((f i) = (@neutral A op)).
Proof. exact (@lem6886921 A (f i) (@neutral A op)). Qed.
Lemma lem6886925 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6886926 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1021 A K f i op) = (term1022 A K f i op).
Proof. exact (MK_COMB (@lem6886925) (@lem6886922 A K f i op)). Qed.
Lemma lem6886927 {A K : Type'} (f : K -> A) (i : K) : (term1019 A K f i) = (term1019 A K f i).
Proof. exact (eq_refl (term1019 A K f i)). Qed.
Lemma lem6886928 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1016 A K f i op) = (term1219 A K f i op).
Proof. exact (MK_COMB (@lem6886927 A K f i) (@lem6886926 A K f i op)). Qed.
Lemma lem6886931 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1015 A K f i op) = (term1219 A K f i op).
Proof. exact (TRANS (@lem6886916 A K f i op) (@lem6886928 A K f i op)). Qed.
Lemma lem6886932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6886933 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1220 A K f i op) = (term1221 A K f i op).
Proof. exact (MK_COMB (@lem6886932) (@lem6886931 A K f i op)). Qed.
Lemma lem6886936 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) : ((term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) = ((term1011 A K op ltle k f) = (term1222 A K op ltle k i f)).
Proof. exact (eq_refl ((term1011 A K op ltle k f) = (term1222 A K op ltle k i f))). Qed.
Lemma lem6886937 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) : (term1223 A K op ltle k i f) = (term1224 A K op ltle k i f).
Proof. exact (MK_COMB (@lem6886933 A K f i op) (@lem6886936 A K op ltle k i f)). Qed.
Lemma lem6886940 {K : Type'} (i : K) (k : K -> Prop) : (term13 K i k) = (term13 K i k).
Proof. exact (eq_refl (term13 K i k)). Qed.
Lemma lem6886941 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) : (term1218 A K op ltle k i f) = (term1225 A K op ltle k i f).
Proof. exact (MK_COMB (@lem6886940 K i k) (@lem6886937 A K op ltle k i f)). Qed.
Lemma lem6886944 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6886945 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) : (term1226 A K op ltle k i f) = (term1227 A K op ltle k i f).
Proof. exact (MK_COMB (@lem6886944) (@lem6886941 A K op ltle k i f)). Qed.
Lemma lem6886948 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : ((term1011 A K op ltle k f) = (@iterate A K op k f)) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (eq_refl ((term1011 A K op ltle k f) = (@iterate A K op k f))). Qed.
Lemma lem6886949 {A K : Type'} (i : K) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1228 A K i ltle op k f) = (term1229 A K i ltle op k f).
Proof. exact (MK_COMB (@lem6886945 A K op ltle k i f) (@lem6886948 A K ltle op k f)). Qed.
Lemma lem6886952 {A K : Type'} (i : K) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1229 A K i ltle op k f) = (term1228 A K i ltle op k f).
Proof. exact (SYM (@lem6886949 A K i ltle op k f)). Qed.
Lemma lem6886953 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) (h1 : term1225 A K op ltle k i f) : term1225 A K op ltle k i f.
Proof. exact (h1). Qed.
Lemma lem6886954 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) (h1 : term1224 A K op ltle k i f) : term1224 A K op ltle k i f.
Proof. exact (h1). Qed.
Lemma lem6886955 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (h1). Qed.
Lemma lem6886956 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) (h1 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f).
Proof. exact (h1). Qed.
Lemma lem6886957 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (h1 : term1219 A K f i op) : term1219 A K f i op.
Proof. exact (h1). Qed.
Lemma lem6886958 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (h1 : term1022 A K f i op) : term1022 A K f i op.
Proof. exact (h1). Qed.
Lemma lem6886959 {A K : Type'} (f : K -> A) (i : K) (h1 : term1018 A K f i) : term1018 A K f i.
Proof. exact (h1). Qed.
Lemma lem6886960 {A K : Type'} (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1230 A K op k f) = (term1230 A K op k f).
Proof. exact (eq_refl (term1230 A K op k f)). Qed.
Lemma lem6886961 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) (h1 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) : (term1231 A K op ltle k f) = (term1232 A K op ltle k i f).
Proof. exact (MK_COMB (@lem6886960 A K op k f) (@lem6886956 A K op ltle k i f h1)). Qed.
Lemma lem6886962 {A K : Type'} (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1232 A K op ltle k i f) = ((term1222 A K op ltle k i f) = (@iterate A K op k f)).
Proof. exact (eq_refl (term1232 A K op ltle k i f)). Qed.
Lemma lem6886963 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term1233 A K op ltle k f) = (term1233 A K op ltle k f).
Proof. exact (eq_refl (term1233 A K op ltle k f)). Qed.
Lemma lem6886964 {A K : Type'} (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : ((term1231 A K op ltle k f) = (term1232 A K op ltle k i f)) = ((term1231 A K op ltle k f) = ((term1222 A K op ltle k i f) = (@iterate A K op k f))).
Proof. exact (MK_COMB (@lem6886963 A K op ltle k f) (@lem6886962 A K ltle i op k f)). Qed.
Lemma lem6886965 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1231 A K op ltle k f) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (eq_refl (term1231 A K op ltle k f)). Qed.
Lemma lem6886966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6886967 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1233 A K op ltle k f) = (term1234 A K ltle op k f).
Proof. exact (MK_COMB (@lem6886966) (@lem6886965 A K ltle op k f)). Qed.
Lemma lem6886968 {A K : Type'} (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : ((term1222 A K op ltle k i f) = (@iterate A K op k f)) = ((term1222 A K op ltle k i f) = (@iterate A K op k f)).
Proof. exact (eq_refl ((term1222 A K op ltle k i f) = (@iterate A K op k f))). Qed.
Lemma lem6886969 {A K : Type'} (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : ((term1231 A K op ltle k f) = ((term1222 A K op ltle k i f) = (@iterate A K op k f))) = (((term1011 A K op ltle k f) = (@iterate A K op k f)) = ((term1222 A K op ltle k i f) = (@iterate A K op k f))).
Proof. exact (MK_COMB (@lem6886967 A K ltle op k f) (@lem6886968 A K ltle i op k f)). Qed.
Lemma lem6886970 {A K : Type'} (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : ((term1231 A K op ltle k f) = (term1232 A K op ltle k i f)) = (((term1011 A K op ltle k f) = (@iterate A K op k f)) = ((term1222 A K op ltle k i f) = (@iterate A K op k f))).
Proof. exact (TRANS (@lem6886964 A K ltle i op k f) (@lem6886969 A K ltle i op k f)). Qed.
Lemma lem6886971 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) (h1 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) : ((term1011 A K op ltle k f) = (@iterate A K op k f)) = ((term1222 A K op ltle k i f) = (@iterate A K op k f)).
Proof. exact (EQ_MP (@lem6886970 A K ltle i op k f) (@lem6886961 A K op ltle k i f h1)). Qed.
Lemma lem6886972 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) (h1 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) : ((term1222 A K op ltle k i f) = (@iterate A K op k f)) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (SYM (@lem6886971 A K op ltle k i f h1)). Qed.
Lemma lem6886973 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) (h1 : term1093 A K n ltle op f) : term1235 A K ltle op f n.
Proof. exact (@lem6884935 A K n ltle op f h1 (term1236 n)). Qed.
Lemma lem6886974 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) : (term1235 A K ltle op f n) = (term1237 A K n ltle op f).
Proof. exact (eq_refl (term1235 A K ltle op f n)). Qed.
Lemma lem6886975 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) (h1 : term1093 A K n ltle op f) : term1237 A K n ltle op f.
Proof. exact (EQ_MP (@lem6886974 A K n ltle op f) (@lem6886973 A K n ltle op f h1)). Qed.
Lemma lem6886976 {A K : Type'} (k : K -> Prop) (i : K) (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) (h1 : term1093 A K n ltle op f) : term1238 A K n ltle op f k i.
Proof. exact (@lem6886975 A K n ltle op f h1 (@DELETE K k i)). Qed.
Lemma lem6886977 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : (term1238 A K n ltle op f k i) = (term1239 A K n ltle op k i f).
Proof. exact (eq_refl (term1238 A K n ltle op f k i)). Qed.
Lemma lem6886978 {A K : Type'} (k : K -> Prop) (i : K) (n : nat) (ltle : type1402 K) (op : type1400 A) (f : K -> A) (h1 : term1093 A K n ltle op f) : term1239 A K n ltle op k i f.
Proof. exact (EQ_MP (@lem6886977 A K n ltle op k i f) (@lem6886976 A K k i n ltle op f h1)). Qed.
Lemma lem6886986 (n : nat) : (term88 n) = (term89 n).
Proof. exact (EQ_MP (@lem6883242 n) (@lem6883241 n)). Qed.
Lemma lem6886989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6886990 (n : nat) : (term1240 n) = (term1241 n).
Proof. exact (MK_COMB (@lem6886989) (@lem6886986 n)). Qed.
Lemma lem6886995 {K : Type'} (k : K -> Prop) (i : K) (n : nat) : (term1242 K k i n) = (term1242 K k i n).
Proof. exact (eq_refl (term1242 K k i n)). Qed.
Lemma lem6886996 {K : Type'} (k : K -> Prop) (i : K) (n : nat) : (term1243 K k i n) = (term1244 K k i n).
Proof. exact (MK_COMB (@lem6886990 n) (@lem6886995 K k i n)). Qed.
Lemma lem6886999 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6887000 {K : Type'} (k : K -> Prop) (i : K) (n : nat) : (term1245 K k i n) = (term1246 K k i n).
Proof. exact (MK_COMB (@lem6886999) (@lem6886996 K k i n)). Qed.
Lemma lem6887003 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : ((term1247 A K op ltle k i f) = (term1248 A K op k i f)) = ((term1247 A K op ltle k i f) = (term1248 A K op k i f)).
Proof. exact (eq_refl ((term1247 A K op ltle k i f) = (term1248 A K op k i f))). Qed.
Lemma lem6887004 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : (term1239 A K n ltle op k i f) = (term1249 A K n ltle op k i f).
Proof. exact (MK_COMB (@lem6887000 K k i n) (@lem6887003 A K ltle op k i f)). Qed.
Lemma lem6887007 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6887008 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : (term1250 A K n ltle op k i f) = (term1251 A K n ltle op k i f).
Proof. exact (MK_COMB (@lem6887007) (@lem6887004 A K n ltle op k i f)). Qed.
Lemma lem6887011 {A K : Type'} (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : ((term1222 A K op ltle k i f) = (@iterate A K op k f)) = ((term1222 A K op ltle k i f) = (@iterate A K op k f)).
Proof. exact (eq_refl ((term1222 A K op ltle k i f) = (@iterate A K op k f))). Qed.
Lemma lem6887012 {A K : Type'} (n : nat) (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1252 A K n ltle i op k f) = (term1253 A K n ltle i op k f).
Proof. exact (MK_COMB (@lem6887008 A K n ltle op k i f) (@lem6887011 A K ltle i op k f)). Qed.
Lemma lem6887015 {A K : Type'} (n : nat) (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1253 A K n ltle i op k f) = (term1252 A K n ltle i op k f).
Proof. exact (SYM (@lem6887012 A K n ltle i op k f)). Qed.
Lemma lem6887016 {A : Type'} (x : A) : term1254 A x.
Proof. exact (@lem3845383 A x). Qed.
Lemma lem6887017 {A : Type'} (x : A) : (term1254 A x) = (term1255 A x).
Proof. exact (eq_refl (term1254 A x)). Qed.
Lemma lem6887018 {A : Type'} (x : A) : term1255 A x.
Proof. exact (EQ_MP (@lem6887017 A x) (@lem6887016 A x)). Qed.
Lemma lem6887019 {A : Type'} (x : A) (s : A -> Prop) : term1256 A x s.
Proof. exact (@lem6887018 A x s). Qed.
Lemma lem6887020 {A : Type'} (x : A) (s : A -> Prop) : (term1256 A x s) = (term1257 A x s).
Proof. exact (eq_refl (term1256 A x s)). Qed.
Lemma lem6887021 {A : Type'} (x : A) (s : A -> Prop) : term1257 A x s.
Proof. exact (EQ_MP (@lem6887020 A x s) (@lem6887019 A x s)). Qed.
Lemma lem6887022 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem6887023 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term1258 A s x) = (term1259 A x s).
Proof. exact (@lem6887021 A x s (@lem6887022 A s h1)). Qed.
Lemma lem6887029 {A : Type'} (s : A -> Prop) : term1260 A s.
Proof. exact (@lem3610594 A s). Qed.
Lemma lem6887030 {A : Type'} (s : A -> Prop) : (term1260 A s) = (term1261 A s).
Proof. exact (eq_refl (term1260 A s)). Qed.
Lemma lem6887031 {A : Type'} (s : A -> Prop) : term1261 A s.
Proof. exact (EQ_MP (@lem6887030 A s) (@lem6887029 A s)). Qed.
Lemma lem6887032 {A : Type'} (s : A -> Prop) (x : A) : term1262 A s x.
Proof. exact (@lem6887031 A s x). Qed.
Lemma lem6887033 {A : Type'} (x : A) (s : A -> Prop) : (term1262 A s x) = ((term1263 A s x) = (@FINITE A s)).
Proof. exact (eq_refl (term1262 A s x)). Qed.
Lemma lem6887037 {K : Type'} (k : K -> Prop) : (@FINITE K k) = ((@FINITE K k) = True).
Proof. exact (@lem7 (@FINITE K k)). Qed.
Lemma lem6887052 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = ((@IN K i k) = True).
Proof. exact (@lem7 (@IN K i k)). Qed.
Lemma lem6887072 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term1154 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6887073 (p : Prop) (q : Prop) (p' : Prop) : term1155 p q p'.
Proof. exact (fun q' : Prop => @lem6887072 p q p' q'). Qed.
Lemma lem6887074 (p : Prop) (q : Prop) : term1156 p q.
Proof. exact (fun p' : Prop => @lem6887073 p q p'). Qed.
Lemma lem6887075 {A K : Type'} (n : nat) (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : term1264 A K n ltle i op k f.
Proof. exact (@lem6887074 (term1249 A K n ltle op k i f) ((term1222 A K op ltle k i f) = (@iterate A K op k f))). Qed.
Lemma lem6887076 {A K : Type'} (n : nat) (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) : term1265 A K n ltle i op k f p'.
Proof. exact (@lem6887075 A K n ltle i op k f p'). Qed.
Lemma lem6887077 {A K : Type'} (n : nat) (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) : (term1265 A K n ltle i op k f p') = (term1266 A K n ltle i op k f p').
Proof. exact (eq_refl (term1265 A K n ltle i op k f p')). Qed.
Lemma lem6887078 {A K : Type'} (n : nat) (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) : term1266 A K n ltle i op k f p'.
Proof. exact (EQ_MP (@lem6887077 A K n ltle i op k f p') (@lem6887076 A K n ltle i op k f p')). Qed.
Lemma lem6887079 {A K : Type'} (n : nat) (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) (q' : Prop) : term1267 A K n ltle i op k f p' q'.
Proof. exact (@lem6887078 A K n ltle i op k f p' q'). Qed.
Lemma lem6887080 {A K : Type'} (n : nat) (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) (q' : Prop) : (term1267 A K n ltle i op k f p' q') = (term1268 A K n ltle i op k f p' q').
Proof. exact (eq_refl (term1267 A K n ltle i op k f p' q')). Qed.
Lemma lem6887081 {A K : Type'} (n : nat) (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) (q' : Prop) : term1268 A K n ltle i op k f p' q'.
Proof. exact (EQ_MP (@lem6887080 A K n ltle i op k f p' q') (@lem6887079 A K n ltle i op k f p' q')). Qed.
Lemma lem6887085 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term1154 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6887086 (p : Prop) (q : Prop) (p' : Prop) : term1155 p q p'.
Proof. exact (fun q' : Prop => @lem6887085 p q p' q'). Qed.
Lemma lem6887087 (p : Prop) (q : Prop) : term1156 p q.
Proof. exact (fun p' : Prop => @lem6887086 p q p'). Qed.
Lemma lem6887088 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : term1269 A K n ltle op k i f.
Proof. exact (@lem6887087 (term1244 K k i n) ((term1247 A K op ltle k i f) = (term1248 A K op k i f))). Qed.
Lemma lem6887089 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) (p' : Prop) : term1270 A K n ltle op k i f p'.
Proof. exact (@lem6887088 A K n ltle op k i f p'). Qed.
Lemma lem6887090 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) (p' : Prop) : (term1270 A K n ltle op k i f p') = (term1271 A K n ltle op k i f p').
Proof. exact (eq_refl (term1270 A K n ltle op k i f p')). Qed.
Lemma lem6887091 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) (p' : Prop) : term1271 A K n ltle op k i f p'.
Proof. exact (EQ_MP (@lem6887090 A K n ltle op k i f p') (@lem6887089 A K n ltle op k i f p')). Qed.
Lemma lem6887092 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) (p' : Prop) (q' : Prop) : term1272 A K n ltle op k i f p' q'.
Proof. exact (@lem6887091 A K n ltle op k i f p' q'). Qed.
Lemma lem6887093 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) (p' : Prop) (q' : Prop) : (term1272 A K n ltle op k i f p' q') = (term1273 A K n ltle op k i f p' q').
Proof. exact (eq_refl (term1272 A K n ltle op k i f p' q')). Qed.
Lemma lem6887094 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) (p' : Prop) (q' : Prop) : term1273 A K n ltle op k i f p' q'.
Proof. exact (EQ_MP (@lem6887093 A K n ltle op k i f p' q') (@lem6887092 A K n ltle op k i f p' q')). Qed.
Lemma lem6887102 {A : Type'} (x : A) (s : A -> Prop) : (term1263 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem6887033 A x s) (@lem6887032 A s x)). Qed.
Lemma lem6887103 {K : Type'} (x : K) (s : K -> Prop) : (term1263 K s x) = (@FINITE K s).
Proof. exact (@lem6887102 K x s). Qed.
Lemma lem6887104 {K : Type'} (i : K) (k : K -> Prop) : (term1263 K k i) = (@FINITE K k).
Proof. exact (@lem6887103 K i k). Qed.
Lemma lem6887106 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : (@FINITE K k) = True.
Proof. exact (EQ_MP (@lem6887037 K k) (@lem6884937 K k h1)). Qed.
Lemma lem6887107 {K : Type'} (i : K) (k : K -> Prop) (h1 : @FINITE K k) : (term1263 K k i) = True.
Proof. exact (TRANS (@lem6887104 K i k) (@lem6887106 K k h1)). Qed.
Lemma lem6887108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6887109 {K : Type'} (i : K) (k : K -> Prop) (h1 : @FINITE K k) : (term1274 K k i) = (and True).
Proof. exact (MK_COMB (@lem6887108) (@lem6887107 K i k h1)). Qed.
Lemma lem6887113 {A : Type'} (x : A) (s : A -> Prop) : term1257 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem6887023 A x s h0). Qed.
Lemma lem6887114 {K : Type'} (x : K) (s : K -> Prop) : term1257 K x s.
Proof. exact (@lem6887113 K x s). Qed.
Lemma lem6887115 {K : Type'} (i : K) (k : K -> Prop) : term1257 K i k.
Proof. exact (@lem6887114 K i k). Qed.
Lemma lem6887117 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : (@FINITE K k) = True.
Proof. exact (EQ_MP (@lem6887037 K k) (@lem6884937 K k h1)). Qed.
Lemma lem6887118 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : True = (@FINITE K k).
Proof. exact (SYM (@lem6887117 K k h1)). Qed.
Lemma lem6887119 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : @FINITE K k.
Proof. exact (EQ_MP (@lem6887118 K k h1) (@lem0)). Qed.
Lemma lem6887120 {K : Type'} (i : K) (k : K -> Prop) (h1 : @FINITE K k) : (term1258 K k i) = (term1259 K i k).
Proof. exact (@lem6887115 K i k (@lem6887119 K k h1)). Qed.
Lemma lem6887122 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term1275 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem6887123 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term1276 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem6887122 _2963 g t e g' t' e'). Qed.
Lemma lem6887124 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term1277 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem6887123 _2963 g t e g' t'). Qed.
Lemma lem6887125 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term1278 _2963 g t e.
Proof. exact (fun g' : Prop => @lem6887124 _2963 g t e g'). Qed.
Lemma lem6887126 (g : Prop) (t : nat) (e : nat) : term1279 g t e.
Proof. exact (@lem6887125 nat g t e). Qed.
Lemma lem6887127 {K : Type'} (i : K) (k : K -> Prop) : term1280 K i k.
Proof. exact (@lem6887126 (@IN K i k) (term1281 K k) (@CARD K k)). Qed.
Lemma lem6887128 {K : Type'} (i : K) (k : K -> Prop) (g' : Prop) : term1282 K i k g'.
Proof. exact (@lem6887127 K i k g'). Qed.
Lemma lem6887129 {K : Type'} (i : K) (k : K -> Prop) (g' : Prop) : (term1282 K i k g') = (term1283 K i k g').
Proof. exact (eq_refl (term1282 K i k g')). Qed.
Lemma lem6887130 {K : Type'} (i : K) (k : K -> Prop) (g' : Prop) : term1283 K i k g'.
Proof. exact (EQ_MP (@lem6887129 K i k g') (@lem6887128 K i k g')). Qed.
Lemma lem6887131 {K : Type'} (i : K) (k : K -> Prop) (g' : Prop) (t' : nat) : term1284 K i k g' t'.
Proof. exact (@lem6887130 K i k g' t'). Qed.
Lemma lem6887132 {K : Type'} (i : K) (k : K -> Prop) (g' : Prop) (t' : nat) : (term1284 K i k g' t') = (term1285 K i k g' t').
Proof. exact (eq_refl (term1284 K i k g' t')). Qed.
Lemma lem6887133 {K : Type'} (i : K) (k : K -> Prop) (g' : Prop) (t' : nat) : term1285 K i k g' t'.
Proof. exact (EQ_MP (@lem6887132 K i k g' t') (@lem6887131 K i k g' t')). Qed.
Lemma lem6887134 {K : Type'} (i : K) (k : K -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term1286 K i k g' t' e'.
Proof. exact (@lem6887133 K i k g' t' e'). Qed.
Lemma lem6887135 {K : Type'} (i : K) (k : K -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term1286 K i k g' t' e') = (term1287 K i k g' t' e').
Proof. exact (eq_refl (term1286 K i k g' t' e')). Qed.
Lemma lem6887136 {K : Type'} (i : K) (k : K -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term1287 K i k g' t' e'.
Proof. exact (EQ_MP (@lem6887135 K i k g' t' e') (@lem6887134 K i k g' t' e')). Qed.
Lemma lem6887138 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : (@IN K i k) = True.
Proof. exact (EQ_MP (@lem6887052 K i k) (@lem6886955 K i k h1)). Qed.
Lemma lem6887139 {K : Type'} (i : K) (k : K -> Prop) (t' : nat) (e' : nat) : term1288 K i k t' e'.
Proof. exact (@lem6887136 K i k True t' e'). Qed.
Lemma lem6887140 {K : Type'} (t' : nat) (e' : nat) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term1289 K i k t' e'.
Proof. exact (@lem6887139 K i k t' e' (@lem6887138 K i k h1)). Qed.
Lemma lem6887147 {K : Type'} (k : K -> Prop) (n : nat) (h1 : (@CARD K k) = n) : (@CARD K k) = n.
Proof. exact (h1). Qed.
Lemma lem6887148 : Nat.sub = Nat.sub.
Proof. exact (eq_refl Nat.sub). Qed.
Lemma lem6887149 {K : Type'} (k : K -> Prop) (n : nat) (h1 : (@CARD K k) = n) : (term1290 K k) = (Nat.sub n).
Proof. exact (MK_COMB (@lem6887148) (@lem6887147 K k n h1)). Qed.
Lemma lem6887150 : term92 = term92.
Proof. exact (eq_refl term92). Qed.
Lemma lem6887151 {K : Type'} (k : K -> Prop) (n : nat) (h1 : (@CARD K k) = n) : (term1281 K k) = (term1236 n).
Proof. exact (MK_COMB (@lem6887149 K k n h1) (@lem6887150)). Qed.
Lemma lem6887152 {K : Type'} (k : K -> Prop) (n : nat) (h1 : (@CARD K k) = n) : term1291 K k n.
Proof. exact (fun h0 : True => @lem6887151 K k n h1). Qed.
Lemma lem6887153 {K : Type'} (n : nat) (e' : nat) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term1292 K i k n e'.
Proof. exact (@lem6887140 K (term1236 n) e' i k h1). Qed.
Lemma lem6887154 {K : Type'} (e' : nat) (n : nat) (i : K) (k : K -> Prop) (h1 : (@CARD K k) = n) (h2 : @IN K i k) : term1293 K i k n e'.
Proof. exact (@lem6887153 K n e' i k h2 (@lem6887152 K k n h1)). Qed.
Lemma lem6887159 {K : Type'} (k : K -> Prop) (n : nat) (h1 : (@CARD K k) = n) : (@CARD K k) = n.
Proof. exact (h1). Qed.
Lemma lem6887160 {K : Type'} (k : K -> Prop) (n : nat) (h1 : (@CARD K k) = n) : term1294 K k n.
Proof. exact (fun h0 : ~ True => @lem6887159 K k n h1). Qed.
Lemma lem6887161 {K : Type'} (n : nat) (i : K) (k : K -> Prop) (h1 : (@CARD K k) = n) (h2 : @IN K i k) : term1295 K i k n.
Proof. exact (@lem6887154 K n n i k h1 h2). Qed.
Lemma lem6887162 {K : Type'} (n : nat) (i : K) (k : K -> Prop) (h1 : (@CARD K k) = n) (h2 : @IN K i k) : (term1259 K i k) = (term1296 n).
Proof. exact (@lem6887161 K n i k h1 h2 (@lem6887160 K k n h1)). Qed.
Lemma lem6887164 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem6887165 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem6887164 nat t2 t1). Qed.
Lemma lem6887166 (n : nat) : (term1296 n) = (term1236 n).
Proof. exact (@lem6887165 n (term1236 n)). Qed.
Lemma lem6887167 {K : Type'} (n : nat) (i : K) (k : K -> Prop) (h1 : (@CARD K k) = n) (h2 : @IN K i k) : (term1259 K i k) = (term1236 n).
Proof. exact (TRANS (@lem6887162 K n i k h1 h2) (@lem6887166 n)). Qed.
Lemma lem6887168 {K : Type'} (n : nat) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : (@CARD K k) = n) (h3 : @IN K i k) : (term1258 K k i) = (term1236 n).
Proof. exact (TRANS (@lem6887120 K i k h1) (@lem6887167 K n i k h2 h3)). Qed.
Lemma lem6887169 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6887170 {K : Type'} (n : nat) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : (@CARD K k) = n) (h3 : @IN K i k) : (term1297 K k i) = (term1298 n).
Proof. exact (MK_COMB (@lem6887169) (@lem6887168 K n i k h1 h2 h3)). Qed.
Lemma lem6887171 (n : nat) : (term1236 n) = (term1236 n).
Proof. exact (eq_refl (term1236 n)). Qed.
Lemma lem6887172 {K : Type'} (n : nat) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : (@CARD K k) = n) (h3 : @IN K i k) : ((term1258 K k i) = (term1236 n)) = ((term1236 n) = (term1236 n)).
Proof. exact (MK_COMB (@lem6887170 K n i k h1 h2 h3) (@lem6887171 n)). Qed.
Lemma lem6887174 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6887175 (x : nat) : (x = x) = True.
Proof. exact (@lem6887174 nat x). Qed.
Lemma lem6887176 (n : nat) : ((term1236 n) = (term1236 n)) = True.
Proof. exact (@lem6887175 (term1236 n)). Qed.
Lemma lem6887177 {K : Type'} (n : nat) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : (@CARD K k) = n) (h3 : @IN K i k) : ((term1258 K k i) = (term1236 n)) = True.
Proof. exact (TRANS (@lem6887172 K n i k h1 h2 h3) (@lem6887176 n)). Qed.
Lemma lem6887178 {K : Type'} (n : nat) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : (@CARD K k) = n) (h3 : @IN K i k) : (term1242 K k i n) = (True /\ True).
Proof. exact (MK_COMB (@lem6887109 K i k h1) (@lem6887177 K n i k h1 h2 h3)). Qed.
Lemma lem6887180 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6887181 : (True /\ True) = True.
Proof. exact (@lem6887180 True). Qed.
Lemma lem6887182 {K : Type'} (n : nat) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : (@CARD K k) = n) (h3 : @IN K i k) : (term1242 K k i n) = True.
Proof. exact (TRANS (@lem6887178 K n i k h1 h2 h3) (@lem6887181)). Qed.
Lemma lem6887183 (n : nat) : (term1241 n) = (term1241 n).
Proof. exact (eq_refl (term1241 n)). Qed.
Lemma lem6887184 {K : Type'} (n : nat) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : (@CARD K k) = n) (h3 : @IN K i k) : (term1244 K k i n) = (term1299 n).
Proof. exact (MK_COMB (@lem6887183 n) (@lem6887182 K n i k h1 h2 h3)). Qed.
Lemma lem6887186 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem6887187 (n : nat) : (term1299 n) = (term89 n).
Proof. exact (@lem6887186 (term89 n)). Qed.
Lemma lem6887190 {K : Type'} (n : nat) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : (@CARD K k) = n) (h3 : @IN K i k) : (term1244 K k i n) = (term89 n).
Proof. exact (TRANS (@lem6887184 K n i k h1 h2 h3) (@lem6887187 n)). Qed.
Lemma lem6887191 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) (n : nat) (q' : Prop) : term1300 A K ltle op k i f n q'.
Proof. exact (@lem6887094 A K n ltle op k i f (term89 n) q'). Qed.
Lemma lem6887192 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) (q' : Prop) (n : nat) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : (@CARD K k) = n) (h3 : @IN K i k) : term1301 A K ltle op k i f n q'.
Proof. exact (@lem6887191 A K ltle op k i f n q' (@lem6887190 K n i k h1 h2 h3)). Qed.
Lemma lem6887209 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : ((term1247 A K op ltle k i f) = (term1248 A K op k i f)) = ((term1247 A K op ltle k i f) = (term1248 A K op k i f)).
Proof. exact (eq_refl ((term1247 A K op ltle k i f) = (term1248 A K op k i f))). Qed.
Lemma lem6887210 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : term1302 A K n ltle op k i f.
Proof. exact (fun h0 : term89 n => @lem6887209 A K ltle op k i f). Qed.
Lemma lem6887211 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) (n : nat) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : (@CARD K k) = n) (h3 : @IN K i k) : term1303 A K n ltle op k i f.
Proof. exact (@lem6887192 A K ltle op f ((term1247 A K op ltle k i f) = (term1248 A K op k i f)) n i k h1 h2 h3). Qed.
Lemma lem6887212 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) (n : nat) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : (@CARD K k) = n) (h3 : @IN K i k) : (term1249 A K n ltle op k i f) = (term1304 A K n ltle op k i f).
Proof. exact (@lem6887211 A K ltle op f n i k h1 h2 h3 (@lem6887210 A K n ltle op k i f)). Qed.
Lemma lem6887255 {A K : Type'} (n : nat) (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) (q' : Prop) : term1305 A K n ltle op k i f q'.
Proof. exact (@lem6887081 A K n ltle i op k f (term1304 A K n ltle op k i f) q'). Qed.
Lemma lem6887256 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) (q' : Prop) (n : nat) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : (@CARD K k) = n) (h3 : @IN K i k) : term1306 A K n ltle op k i f q'.
Proof. exact (@lem6887255 A K n ltle op k i f q' (@lem6887212 A K ltle op f n i k h1 h2 h3)). Qed.
Lemma lem6887273 {A K : Type'} (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : ((term1222 A K op ltle k i f) = (@iterate A K op k f)) = ((term1222 A K op ltle k i f) = (@iterate A K op k f)).
Proof. exact (eq_refl ((term1222 A K op ltle k i f) = (@iterate A K op k f))). Qed.
Lemma lem6887274 {A K : Type'} (n : nat) (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : term1307 A K n ltle i op k f.
Proof. exact (fun h0 : term1304 A K n ltle op k i f => @lem6887273 A K ltle i op k f). Qed.
Lemma lem6887275 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) (n : nat) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : (@CARD K k) = n) (h3 : @IN K i k) : term1308 A K n ltle i op k f.
Proof. exact (@lem6887256 A K ltle op f ((term1222 A K op ltle k i f) = (@iterate A K op k f)) n i k h1 h2 h3). Qed.
Lemma lem6887276 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) (n : nat) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : (@CARD K k) = n) (h3 : @IN K i k) : (term1253 A K n ltle i op k f) = (term1309 A K n ltle i op k f).
Proof. exact (@lem6887275 A K ltle op f n i k h1 h2 h3 (@lem6887274 A K n ltle i op k f)). Qed.
Lemma lem6887399 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) (n : nat) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : (@CARD K k) = n) (h3 : @IN K i k) : (term1309 A K n ltle i op k f) = (term1253 A K n ltle i op k f).
Proof. exact (SYM (@lem6887276 A K ltle op f n i k h1 h2 h3)). Qed.
Lemma lem6887401 (p : Prop) (q : Prop) (r : Prop) : term1310 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem6887402 {A K : Type'} (n : nat) (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : term1311 A K n ltle i op k f.
Proof. exact (@lem6887401 (term89 n) ((term1247 A K op ltle k i f) = (term1248 A K op k i f)) ((term1222 A K op ltle k i f) = (@iterate A K op k f))). Qed.
Lemma lem6887403 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem6887404 {K : Type'} : term1312 K.
Proof. exact (@lem3854502 K). Qed.
Lemma lem6887410 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) (h1 : term1313 _99911 A K k f i op n) : term1313 _99911 A K k f i op n.
Proof. exact (h1). Qed.
Lemma lem6887411 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : term1314 _99911 A K k f i op n.
Proof. exact (fun h0 : term1313 _99911 A K k f i op n => @lem6887410 _99911 A K k f i op n h0). Qed.
Lemma lem6887412 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) (h1 : term1314 _99911 A K k f i op n) : term1314 _99911 A K k f i op n.
Proof. exact (h1). Qed.
Lemma lem6887413 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) (h1 : term1313 _99911 A K k f i op n) : term1313 _99911 A K k f i op n.
Proof. exact (h1). Qed.
Lemma lem6887414 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) (h1 : term1313 _99911 A K k f i op n) (h2 : term1314 _99911 A K k f i op n) : term1313 _99911 A K k f i op n.
Proof. exact (@lem6887412 _99911 A K k f i op n h2 (@lem6887413 _99911 A K k f i op n h1)). Qed.
Lemma lem6887415 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) (h1 : term1313 _99911 A K k f i op n) : term1315 _99911 A K k f i op n.
Proof. exact (fun h0 : term1314 _99911 A K k f i op n => @lem6887414 _99911 A K k f i op n h1 h0). Qed.
Lemma lem6887416 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) (h1 : term1314 _99911 A K k f i op n) : term1314 _99911 A K k f i op n.
Proof. exact (h1). Qed.
Lemma lem6887417 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) (h1 : term1313 _99911 A K k f i op n) (h2 : term1314 _99911 A K k f i op n) : term1313 _99911 A K k f i op n.
Proof. exact (@lem6887415 _99911 A K k f i op n h1 (@lem6887416 _99911 A K k f i op n h2)). Qed.
Lemma lem6887418 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) (h1 : term1314 _99911 A K k f i op n) : term1314 _99911 A K k f i op n.
Proof. exact (fun h0 : term1313 _99911 A K k f i op n => @lem6887417 _99911 A K k f i op n h0 h1). Qed.
Lemma lem6887419 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : term1316 _99911 A K k f i op n.
Proof. exact (fun h0 : term1314 _99911 A K k f i op n => @lem6887418 _99911 A K k f i op n h0). Qed.
Lemma lem6887422 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : term1314 _99911 A K k f i op n.
Proof. exact (@lem6887419 _99911 A K k f i op n (@lem6887411 _99911 A K k f i op n)). Qed.
Lemma lem6887423 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : term1314 _99911 A K k f i op n.
Proof. exact (@lem6887422 _99911 A K k f i op n). Qed.
Lemma lem6887469 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6887470 {K : Type'} : (term1317 K) = (term1318 K).
Proof. exact (@lem6887469 (term1312 K)). Qed.
Lemma lem6887477 {_99911 : Type'} : (term1319 _99911) = (term1319 _99911).
Proof. exact (eq_refl (term1319 _99911)). Qed.
Lemma lem6887478 {_99911 K : Type'} : (term1320 _99911 K) = (term1321 _99911 K).
Proof. exact (MK_COMB (@lem6887477 _99911) (@lem6887470 K)). Qed.
Lemma lem6887481 (n : nat) : (term1322 n) = (term1322 n).
Proof. exact (eq_refl (term1322 n)). Qed.
Lemma lem6887482 {_99911 K : Type'} (n : nat) : (term1323 _99911 K n) = (term1324 _99911 K n).
Proof. exact (MK_COMB (@lem6887481 n) (@lem6887478 _99911 K)). Qed.
Lemma lem6887485 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1325 A K f i op) = (term1325 A K f i op).
Proof. exact (eq_refl (term1325 A K f i op)). Qed.
Lemma lem6887486 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1326 _99911 A K f i op n) = (term1327 _99911 A K f i op n).
Proof. exact (MK_COMB (@lem6887485 A K f i op) (@lem6887482 _99911 K n)). Qed.
Lemma lem6887489 {A K : Type'} (f : K -> A) (i : K) : (term1328 A K f i) = (term1328 A K f i).
Proof. exact (eq_refl (term1328 A K f i)). Qed.
Lemma lem6887490 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1329 _99911 A K f i op n) = (term1330 _99911 A K f i op n).
Proof. exact (MK_COMB (@lem6887489 A K f i) (@lem6887486 _99911 A K f i op n)). Qed.
Lemma lem6887493 {K : Type'} (i : K) (k : K -> Prop) : (term3 K i k) = (term3 K i k).
Proof. exact (eq_refl (term3 K i k)). Qed.
Lemma lem6887494 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1331 _99911 A K k f i op n) = (term1332 _99911 A K k f i op n).
Proof. exact (MK_COMB (@lem6887493 K i k) (@lem6887490 _99911 A K f i op n)). Qed.
Lemma lem6887497 {K : Type'} (k : K -> Prop) : (term1333 K k) = (term1333 K k).
Proof. exact (eq_refl (term1333 K k)). Qed.
Lemma lem6887498 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1334 _99911 A K k f i op n) = (term1335 _99911 A K k f i op n).
Proof. exact (MK_COMB (@lem6887497 K k) (@lem6887494 _99911 A K k f i op n)). Qed.
Lemma lem6887501 {K : Type'} (k : K -> Prop) (n : nat) : (term1336 K k n) = (term1336 K k n).
Proof. exact (eq_refl (term1336 K k n)). Qed.
Lemma lem6887502 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1337 _99911 A K k f i op n) = (term1338 _99911 A K k f i op n).
Proof. exact (MK_COMB (@lem6887501 K k n) (@lem6887498 _99911 A K k f i op n)). Qed.
Lemma lem6887505 {K : Type'} (k : K -> Prop) : (term1077 K k) = (term1077 K k).
Proof. exact (eq_refl (term1077 K k)). Qed.
Lemma lem6887506 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1339 _99911 A K k f i op n) = (term1340 _99911 A K k f i op n).
Proof. exact (MK_COMB (@lem6887505 K k) (@lem6887502 _99911 A K k f i op n)). Qed.
Lemma lem6887509 {A : Type'} (op : type1400 A) : (term1341 A op) = (term1341 A op).
Proof. exact (eq_refl (term1341 A op)). Qed.
Lemma lem6887510 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1313 _99911 A K k f i op n) = (term1342 _99911 A K k f i op n).
Proof. exact (MK_COMB (@lem6887509 A op) (@lem6887506 _99911 A K k f i op n)). Qed.
Lemma lem6887513 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1343 _99911 A K f i op n) = (term1344 _99911 A K f i op n).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6887510 _99911 A K k f i op n)). Qed.
Lemma lem6887514 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6887515 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1345 _99911 A K f i op n) = (term1346 _99911 A K f i op n).
Proof. exact (MK_COMB (@lem6887514 K) (@lem6887513 _99911 A K f i op n)). Qed.
Lemma lem6887520 {_99911 A K : Type'} (i : K) (op : type1400 A) (n : nat) : (term1347 _99911 A K i op n) = (term1348 _99911 A K i op n).
Proof. exact (fun_ext (fun f : K -> A => @lem6887515 _99911 A K f i op n)). Qed.
Lemma lem6887521 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6887522 {_99911 A K : Type'} (i : K) (op : type1400 A) (n : nat) : (term1349 _99911 A K i op n) = (term1350 _99911 A K i op n).
Proof. exact (MK_COMB (@lem6887521 A K) (@lem6887520 _99911 A K i op n)). Qed.
Lemma lem6887527 {_99911 A K : Type'} (op : type1400 A) (n : nat) : (term1351 _99911 A K op n) = (term1352 _99911 A K op n).
Proof. exact (fun_ext (fun i : K => @lem6887522 _99911 A K i op n)). Qed.
Lemma lem6887528 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6887529 {_99911 A K : Type'} (op : type1400 A) (n : nat) : (term1353 _99911 A K op n) = (term1354 _99911 A K op n).
Proof. exact (MK_COMB (@lem6887528 K) (@lem6887527 _99911 A K op n)). Qed.
Lemma lem6887534 {_99911 A K : Type'} (n : nat) : (term1355 _99911 A K n) = (term1356 _99911 A K n).
Proof. exact (fun_ext (fun op : type1400 A => @lem6887529 _99911 A K op n)). Qed.
Lemma lem6887535 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem6887536 {_99911 A K : Type'} (n : nat) : (term1357 _99911 A K n) = (term1358 _99911 A K n).
Proof. exact (MK_COMB (@lem6887535 A) (@lem6887534 _99911 A K n)). Qed.
Lemma lem6887541 {_99911 A K : Type'} : (term1359 _99911 A K) = (term1360 _99911 A K).
Proof. exact (fun_ext (fun n : nat => @lem6887536 _99911 A K n)). Qed.
Lemma lem6887542 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6887551 {_99911 A K : Type'} : (term1361 _99911 A K) = (term1362 _99911 A K).
Proof. exact (MK_COMB (@lem6887542) (@lem6887541 _99911 A K)). Qed.
Lemma lem6887560 {K : Type'} (s : K -> Prop) : (term1363 K s) = (term1363 K s).
Proof. exact (eq_refl (term1363 K s)). Qed.
Lemma lem6887561 {K : Type'} : (term1364 K) = (term1364 K).
Proof. exact (fun_ext (fun s : K -> Prop => @lem6887560 K s)). Qed.
Lemma lem6887562 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6887563 {K : Type'} : (term1312 K) = (term1312 K).
Proof. exact (MK_COMB (@lem6887562 K) (@lem6887561 K)). Qed.
Lemma lem6887564 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6887565 {K : Type'} : (term1318 K) = (term1318 K).
Proof. exact (MK_COMB (@lem6887564) (@lem6887563 K)). Qed.
Lemma lem6887574 {_99911 : Type'} (s : _99911 -> Prop) : (term1363 _99911 s) = (term1363 _99911 s).
Proof. exact (eq_refl (term1363 _99911 s)). Qed.
Lemma lem6887575 {_99911 : Type'} : (term1364 _99911) = (term1364 _99911).
Proof. exact (fun_ext (fun s : _99911 -> Prop => @lem6887574 _99911 s)). Qed.
Lemma lem6887576 {_99911 : Type'} : (@all (_99911 -> Prop)) = (@all (_99911 -> Prop)).
Proof. exact (eq_refl (@all (_99911 -> Prop))). Qed.
Lemma lem6887577 {_99911 : Type'} : (term1312 _99911) = (term1312 _99911).
Proof. exact (MK_COMB (@lem6887576 _99911) (@lem6887575 _99911)). Qed.
Lemma lem6887578 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6887579 {_99911 : Type'} : (term1319 _99911) = (term1319 _99911).
Proof. exact (MK_COMB (@lem6887578) (@lem6887577 _99911)). Qed.
Lemma lem6887580 {_99911 K : Type'} : (term1321 _99911 K) = (term1321 _99911 K).
Proof. exact (MK_COMB (@lem6887579 _99911) (@lem6887565 K)). Qed.
Lemma lem6887583 (n : nat) : (term1322 n) = (term1322 n).
Proof. exact (eq_refl (term1322 n)). Qed.
Lemma lem6887584 {_99911 K : Type'} (n : nat) : (term1324 _99911 K n) = (term1324 _99911 K n).
Proof. exact (MK_COMB (@lem6887583 n) (@lem6887580 _99911 K)). Qed.
Lemma lem6887589 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) : (term1325 A K f i op) = (term1325 A K f i op).
Proof. exact (eq_refl (term1325 A K f i op)). Qed.
Lemma lem6887590 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1327 _99911 A K f i op n) = (term1327 _99911 A K f i op n).
Proof. exact (MK_COMB (@lem6887589 A K f i op) (@lem6887584 _99911 K n)). Qed.
Lemma lem6887593 {A K : Type'} (f : K -> A) (i : K) : (term1328 A K f i) = (term1328 A K f i).
Proof. exact (eq_refl (term1328 A K f i)). Qed.
Lemma lem6887594 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1330 _99911 A K f i op n) = (term1330 _99911 A K f i op n).
Proof. exact (MK_COMB (@lem6887593 A K f i) (@lem6887590 _99911 A K f i op n)). Qed.
Lemma lem6887597 {K : Type'} (i : K) (k : K -> Prop) : (term3 K i k) = (term3 K i k).
Proof. exact (eq_refl (term3 K i k)). Qed.
Lemma lem6887598 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1332 _99911 A K k f i op n) = (term1332 _99911 A K k f i op n).
Proof. exact (MK_COMB (@lem6887597 K i k) (@lem6887594 _99911 A K f i op n)). Qed.
Lemma lem6887603 {K : Type'} (k : K -> Prop) : (term1333 K k) = (term1333 K k).
Proof. exact (eq_refl (term1333 K k)). Qed.
Lemma lem6887604 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1335 _99911 A K k f i op n) = (term1335 _99911 A K k f i op n).
Proof. exact (MK_COMB (@lem6887603 K k) (@lem6887598 _99911 A K k f i op n)). Qed.
Lemma lem6887607 {K : Type'} (k : K -> Prop) (n : nat) : (term1336 K k n) = (term1336 K k n).
Proof. exact (eq_refl (term1336 K k n)). Qed.
Lemma lem6887608 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1338 _99911 A K k f i op n) = (term1338 _99911 A K k f i op n).
Proof. exact (MK_COMB (@lem6887607 K k n) (@lem6887604 _99911 A K k f i op n)). Qed.
Lemma lem6887611 {K : Type'} (k : K -> Prop) : (term1077 K k) = (term1077 K k).
Proof. exact (eq_refl (term1077 K k)). Qed.
Lemma lem6887612 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1340 _99911 A K k f i op n) = (term1340 _99911 A K k f i op n).
Proof. exact (MK_COMB (@lem6887611 K k) (@lem6887608 _99911 A K k f i op n)). Qed.
Lemma lem6887615 {A : Type'} (op : type1400 A) : (term1341 A op) = (term1341 A op).
Proof. exact (eq_refl (term1341 A op)). Qed.
Lemma lem6887616 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1342 _99911 A K k f i op n) = (term1342 _99911 A K k f i op n).
Proof. exact (MK_COMB (@lem6887615 A op) (@lem6887612 _99911 A K k f i op n)). Qed.
Lemma lem6887617 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1344 _99911 A K f i op n) = (term1344 _99911 A K f i op n).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6887616 _99911 A K k f i op n)). Qed.
Lemma lem6887618 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6887619 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1346 _99911 A K f i op n) = (term1346 _99911 A K f i op n).
Proof. exact (MK_COMB (@lem6887618 K) (@lem6887617 _99911 A K f i op n)). Qed.
Lemma lem6887620 {_99911 A K : Type'} (i : K) (op : type1400 A) (n : nat) : (term1348 _99911 A K i op n) = (term1348 _99911 A K i op n).
Proof. exact (fun_ext (fun f : K -> A => @lem6887619 _99911 A K f i op n)). Qed.
Lemma lem6887621 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6887622 {_99911 A K : Type'} (i : K) (op : type1400 A) (n : nat) : (term1350 _99911 A K i op n) = (term1350 _99911 A K i op n).
Proof. exact (MK_COMB (@lem6887621 A K) (@lem6887620 _99911 A K i op n)). Qed.
Lemma lem6887623 {_99911 A K : Type'} (op : type1400 A) (n : nat) : (term1352 _99911 A K op n) = (term1352 _99911 A K op n).
Proof. exact (fun_ext (fun i : K => @lem6887622 _99911 A K i op n)). Qed.
Lemma lem6887624 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6887625 {_99911 A K : Type'} (op : type1400 A) (n : nat) : (term1354 _99911 A K op n) = (term1354 _99911 A K op n).
Proof. exact (MK_COMB (@lem6887624 K) (@lem6887623 _99911 A K op n)). Qed.
Lemma lem6887626 {_99911 A K : Type'} (n : nat) : (term1356 _99911 A K n) = (term1356 _99911 A K n).
Proof. exact (fun_ext (fun op : type1400 A => @lem6887625 _99911 A K op n)). Qed.
Lemma lem6887627 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem6887628 {_99911 A K : Type'} (n : nat) : (term1358 _99911 A K n) = (term1358 _99911 A K n).
Proof. exact (MK_COMB (@lem6887627 A) (@lem6887626 _99911 A K n)). Qed.
Lemma lem6887629 {_99911 A K : Type'} : (term1360 _99911 A K) = (term1360 _99911 A K).
Proof. exact (fun_ext (fun n : nat => @lem6887628 _99911 A K n)). Qed.
Lemma lem6887630 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6887631 {_99911 A K : Type'} : (term1362 _99911 A K) = (term1362 _99911 A K).
Proof. exact (MK_COMB (@lem6887630) (@lem6887629 _99911 A K)). Qed.
Lemma lem6887698 {_99911 A K : Type'} : (term1361 _99911 A K) = (term1362 _99911 A K).
Proof. exact (TRANS (@lem6887551 _99911 A K) (@lem6887631 _99911 A K)). Qed.
Lemma lem6887699 {_99911 A K : Type'} : (term1362 _99911 A K) = (term1361 _99911 A K).
Proof. exact (SYM (@lem6887698 _99911 A K)). Qed.
Lemma lem6887709 {K : Type'} (h1 : term1312 K) : term1312 K.
Proof. exact (h1). Qed.
Lemma lem6887721 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : @FINITE K k.
Proof. exact (h1). Qed.
Lemma lem6887727 {K : Type'} (k : K -> Prop) (n : nat) (h1 : (@CARD K k) = n) : (@CARD K k) = n.
Proof. exact (h1). Qed.
Lemma lem6887733 {K : Type'} (k : K -> Prop) (h1 : term835 K k) : term835 K k.
Proof. exact (h1). Qed.
Lemma lem6887757 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem6887850 {K : Type'} (s : K -> Prop) : (((@CARD K s) = (NUMERAL 0)) = (s = (@EMPTY K))) = (term1365 K s).
Proof. exact (@lem17784 ((@CARD K s) = (NUMERAL 0)) (s = (@EMPTY K))). Qed.
Lemma lem6887852 {K : Type'} (s : K -> Prop) : (term1366 K s) = (term1366 K s).
Proof. exact (eq_refl (term1366 K s)). Qed.
Lemma lem6887853 {K : Type'} (s : K -> Prop) : (term1367 K s) = (term1368 K s).
Proof. exact (MK_COMB (@lem6887852 K s) (@lem6887850 K s)). Qed.
Lemma lem6887854 {K : Type'} (s : K -> Prop) : (term1363 K s) = (term1367 K s).
Proof. exact (@lem17265 (@FINITE K s) (((@CARD K s) = (NUMERAL 0)) = (s = (@EMPTY K)))). Qed.
Lemma lem6887855 {K : Type'} (s : K -> Prop) : (term1363 K s) = (term1368 K s).
Proof. exact (TRANS (@lem6887854 K s) (@lem6887853 K s)). Qed.
Lemma lem6887856 {K : Type'} : (term1364 K) = (term1369 K).
Proof. exact (fun_ext (fun s : K -> Prop => @lem6887855 K s)). Qed.
Lemma lem6887857 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6887910 {K : Type'} : (term1312 K) = (term1370 K).
Proof. exact (MK_COMB (@lem6887857 K) (@lem6887856 K)). Qed.
Lemma lem6887911 {K : Type'} (h1 : term1312 K) : term1370 K.
Proof. exact (EQ_MP (@lem6887910 K) (@lem6887709 K h1)). Qed.
Lemma lem6887919 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : @FINITE K k.
Proof. exact (h1). Qed.
Lemma lem6887927 {K : Type'} (k : K -> Prop) (n : nat) (h1 : (@CARD K k) = n) : (@CARD K k) = n.
Proof. exact (h1). Qed.
Lemma lem6887935 {K : Type'} (k : K -> Prop) (h1 : term835 K k) : term835 K k.
Proof. exact (h1). Qed.
Lemma lem6887969 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem6888071 {K : Type'} (s : K -> Prop) : (term1368 K s) = (term1368 K s).
Proof. exact (eq_refl (term1368 K s)). Qed.
Lemma lem6888072 {K : Type'} : (term1369 K) = (term1369 K).
Proof. exact (fun_ext (fun s : K -> Prop => @lem6888071 K s)). Qed.
Lemma lem6888073 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6888074 {K : Type'} : (term1370 K) = (term1370 K).
Proof. exact (MK_COMB (@lem6888073 K) (@lem6888072 K)). Qed.
Lemma lem6888075 {K : Type'} (h1 : term1312 K) : term1370 K.
Proof. exact (EQ_MP (@lem6888074 K) (@lem6887911 K h1)). Qed.
Lemma lem6888083 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : @FINITE K k.
Proof. exact (h1). Qed.
Lemma lem6888087 {K : Type'} (k : K -> Prop) (n : nat) (h1 : (@CARD K k) = n) : (@CARD K k) = n.
Proof. exact (h1). Qed.
Lemma lem6888091 {K : Type'} (k : K -> Prop) (h1 : term835 K k) : term835 K k.
Proof. exact (h1). Qed.
Lemma lem6888107 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem6888172 {K : Type'} (s : K -> Prop) : (term1368 K s) = (term1371 K s).
Proof. exact (@lem19490 (term1372 K s) (term891 K s) (term1373 K s)). Qed.
Lemma lem6888173 {K : Type'} : (term1369 K) = (term1374 K).
Proof. exact (fun_ext (fun s : K -> Prop => @lem6888172 K s)). Qed.
Lemma lem6888174 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6888176 {K : Type'} : (term1370 K) = (term1375 K).
Proof. exact (MK_COMB (@lem6888174 K) (@lem6888173 K)). Qed.
Lemma lem6888177 {K : Type'} (h1 : term1312 K) : term1375 K.
Proof. exact (EQ_MP (@lem6888176 K) (@lem6888075 K h1)). Qed.
Lemma lem6888181 {K : Type'} (_91937 : K -> Prop) (h1 : term1312 K) : term1376 K _91937.
Proof. exact (@lem6888177 K h1 _91937). Qed.
Lemma lem6888182 {K : Type'} (_91937 : K -> Prop) : (term1376 K _91937) = (term1371 K _91937).
Proof. exact (eq_refl (term1376 K _91937)). Qed.
Lemma lem6888183 {K : Type'} (_91937 : K -> Prop) (h1 : term1312 K) : term1371 K _91937.
Proof. exact (EQ_MP (@lem6888182 K _91937) (@lem6888181 K _91937 h1)). Qed.
Lemma lem6888191 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : @FINITE K k.
Proof. exact (h1). Qed.
Lemma lem6888193 {K : Type'} (k : K -> Prop) (n : nat) (h1 : (@CARD K k) = n) : (@CARD K k) = n.
Proof. exact (h1). Qed.
Lemma lem6888195 {K : Type'} (k : K -> Prop) (h1 : term835 K k) : term835 K k.
Proof. exact (h1). Qed.
Lemma lem6888203 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem6888285 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : @FINITE K k.
Proof. exact (h1). Qed.
Lemma lem6888286 {K : Type'} (k : K -> Prop) : (term1377 K k) = (term1377 K k).
Proof. exact (eq_refl (term1377 K k)). Qed.
Lemma lem6888287 {K : Type'} (k : K -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : (term1378 K k n) = (term1379 K k).
Proof. exact (MK_COMB (@lem6888286 K k) (@lem6888203 n h1)). Qed.
Lemma lem6888288 {K : Type'} (k : K -> Prop) : (term1379 K k) = ((@CARD K k) = (NUMERAL 0)).
Proof. exact (eq_refl (term1379 K k)). Qed.
Lemma lem6888289 {K : Type'} (k : K -> Prop) (n : nat) : (term1380 K k n) = (term1380 K k n).
Proof. exact (eq_refl (term1380 K k n)). Qed.
Lemma lem6888290 {K : Type'} (n : nat) (k : K -> Prop) : ((term1378 K k n) = (term1379 K k)) = ((term1378 K k n) = ((@CARD K k) = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem6888289 K k n) (@lem6888288 K k)). Qed.
Lemma lem6888291 {K : Type'} (k : K -> Prop) (n : nat) : (term1378 K k n) = ((@CARD K k) = n).
Proof. exact (eq_refl (term1378 K k n)). Qed.
Lemma lem6888292 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6888293 {K : Type'} (k : K -> Prop) (n : nat) : (term1380 K k n) = (term1381 K k n).
Proof. exact (MK_COMB (@lem6888292) (@lem6888291 K k n)). Qed.
Lemma lem6888294 {K : Type'} (k : K -> Prop) : ((@CARD K k) = (NUMERAL 0)) = ((@CARD K k) = (NUMERAL 0)).
Proof. exact (eq_refl ((@CARD K k) = (NUMERAL 0))). Qed.
Lemma lem6888295 {K : Type'} (n : nat) (k : K -> Prop) : ((term1378 K k n) = ((@CARD K k) = (NUMERAL 0))) = (((@CARD K k) = n) = ((@CARD K k) = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem6888293 K k n) (@lem6888294 K k)). Qed.
Lemma lem6888296 {K : Type'} (n : nat) (k : K -> Prop) : ((term1378 K k n) = (term1379 K k)) = (((@CARD K k) = n) = ((@CARD K k) = (NUMERAL 0))).
Proof. exact (TRANS (@lem6888290 K n k) (@lem6888295 K n k)). Qed.
Lemma lem6888297 {K : Type'} (k : K -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) : ((@CARD K k) = n) = ((@CARD K k) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem6888296 K n k) (@lem6888287 K k n h1)). Qed.
Lemma lem6888312 {K : Type'} (k : K -> Prop) (h1 : term835 K k) : term835 K k.
Proof. exact (h1). Qed.
Lemma lem6888382 {K : Type'} (_91937 : K -> Prop) (h1 : term1312 K) : term1382 K _91937.
Proof. exact (proj2 (@lem6888183 K _91937 h1)). Qed.
Lemma lem6888540 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : @FINITE K k.
Proof. exact (h1). Qed.
Lemma lem6888541 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : term893 K k.
Proof. exact (fun h0 : term891 K k => @lem6888540 K k h1). Qed.
Lemma lem6888543 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6888544 {K : Type'} (k : K -> Prop) : (term893 K k) = (@FINITE K k).
Proof. exact (@lem6888543 (@FINITE K k)). Qed.
Lemma lem6888545 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : @FINITE K k.
Proof. exact (EQ_MP (@lem6888544 K k) (@lem6888541 K k h1)). Qed.
Lemma lem6888547 {K : Type'} (k : K -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) (h2 : (@CARD K k) = n) : (@CARD K k) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6888297 K k n h1) (@lem6888193 K k n h2)). Qed.
Lemma lem6888548 {K : Type'} (k : K -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) (h2 : (@CARD K k) = n) : term1383 K k.
Proof. exact (fun h0 : term1384 K k => @lem6888547 K k n h1 h2). Qed.
Lemma lem6888550 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6888551 {K : Type'} (k : K -> Prop) : (term1383 K k) = ((@CARD K k) = (NUMERAL 0)).
Proof. exact (@lem6888550 ((@CARD K k) = (NUMERAL 0))). Qed.
Lemma lem6888552 {K : Type'} (k : K -> Prop) (n : nat) (h1 : n = (NUMERAL 0)) (h2 : (@CARD K k) = n) : (@CARD K k) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem6888551 K k) (@lem6888548 K k n h1 h2)). Qed.
Lemma lem6888558 (q : Prop) (p : Prop) (r : Prop) : (term853 p q r) = (term853 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6888559 {K : Type'} (_91937 : K -> Prop) : (term1382 K _91937) = (term1385 K _91937).
Proof. exact (@lem6888558 (term1384 K _91937) (term891 K _91937) (_91937 = (@EMPTY K))). Qed.
Lemma lem6888575 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6888576 {K : Type'} (_91937 : K -> Prop) : (term1386 K _91937) = (term1387 K _91937).
Proof. exact (@lem6888575 (_91937 = (@EMPTY K)) (term891 K _91937)). Qed.
Lemma lem6888584 {K : Type'} (_91937 : K -> Prop) : (term1388 K _91937) = (term1388 K _91937).
Proof. exact (eq_refl (term1388 K _91937)). Qed.
Lemma lem6888585 {K : Type'} (_91937 : K -> Prop) : (term1385 K _91937) = (term1389 K _91937).
Proof. exact (MK_COMB (@lem6888584 K _91937) (@lem6888576 K _91937)). Qed.
Lemma lem6888589 (q : Prop) (p : Prop) (r : Prop) : (term853 p q r) = (term853 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6888590 {K : Type'} (_91937 : K -> Prop) : (term1389 K _91937) = (term1390 K _91937).
Proof. exact (@lem6888589 (_91937 = (@EMPTY K)) (term1384 K _91937) (term891 K _91937)). Qed.
Lemma lem6888610 {K : Type'} (_91937 : K -> Prop) : (term1385 K _91937) = (term1390 K _91937).
Proof. exact (TRANS (@lem6888585 K _91937) (@lem6888590 K _91937)). Qed.
Lemma lem6888611 {K : Type'} (_91937 : K -> Prop) : (term1382 K _91937) = (term1390 K _91937).
Proof. exact (TRANS (@lem6888559 K _91937) (@lem6888610 K _91937)). Qed.
Lemma lem6888612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6888613 {K : Type'} (_91937 : K -> Prop) : (term1391 K _91937) = (term1392 K _91937).
Proof. exact (MK_COMB (@lem6888612) (@lem6888611 K _91937)). Qed.
Lemma lem6888629 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6888630 {K : Type'} (_91937 : K -> Prop) : (term1393 K _91937) = (term1394 K _91937).
Proof. exact (@lem6888629 (term1384 K _91937) (term891 K _91937)). Qed.
Lemma lem6888638 {K : Type'} (_91937 : K -> Prop) : (term1395 K _91937) = (term1395 K _91937).
Proof. exact (eq_refl (term1395 K _91937)). Qed.
Lemma lem6888639 {K : Type'} (_91937 : K -> Prop) : (term1396 K _91937) = (term1390 K _91937).
Proof. exact (MK_COMB (@lem6888638 K _91937) (@lem6888630 K _91937)). Qed.
Lemma lem6888650 {K : Type'} (_91937 : K -> Prop) : ((term1382 K _91937) = (term1396 K _91937)) = ((term1390 K _91937) = (term1390 K _91937)).
Proof. exact (MK_COMB (@lem6888613 K _91937) (@lem6888639 K _91937)). Qed.
Lemma lem6888652 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6888653 (x : Prop) : (x = x) = True.
Proof. exact (@lem6888652 Prop x). Qed.
Lemma lem6888654 {K : Type'} (_91937 : K -> Prop) : ((term1390 K _91937) = (term1390 K _91937)) = True.
Proof. exact (@lem6888653 (term1390 K _91937)). Qed.
Lemma lem6888655 {K : Type'} (_91937 : K -> Prop) : ((term1382 K _91937) = (term1396 K _91937)) = True.
Proof. exact (TRANS (@lem6888650 K _91937) (@lem6888654 K _91937)). Qed.
Lemma lem6888656 {K : Type'} (_91937 : K -> Prop) : True = ((term1382 K _91937) = (term1396 K _91937)).
Proof. exact (SYM (@lem6888655 K _91937)). Qed.
Lemma lem6888657 {K : Type'} (_91937 : K -> Prop) : (term1382 K _91937) = (term1396 K _91937).
Proof. exact (EQ_MP (@lem6888656 K _91937) (@lem0)). Qed.
Lemma lem6888658 {K : Type'} (_91937 : K -> Prop) (h1 : term1312 K) : term1396 K _91937.
Proof. exact (EQ_MP (@lem6888657 K _91937) (@lem6888382 K _91937 h1)). Qed.
Lemma lem6888660 (b : Prop) (a : Prop) : (a \/ b) = (term907 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6888661 {K : Type'} (_91937 : K -> Prop) : (term1396 K _91937) = (term1397 K _91937).
Proof. exact (@lem6888660 (term1393 K _91937) (_91937 = (@EMPTY K))). Qed.
Lemma lem6888663 (a : Prop) (b : Prop) : (term909 a b) = (term910 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6888664 {K : Type'} (_91937 : K -> Prop) : (term1398 K _91937) = (term1399 K _91937).
Proof. exact (@lem6888663 (term891 K _91937) (term1384 K _91937)). Qed.
Lemma lem6888666 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6888667 {K : Type'} (_91937 : K -> Prop) : (term913 K _91937) = (@FINITE K _91937).
Proof. exact (@lem6888666 (@FINITE K _91937)). Qed.
Lemma lem6888668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6888669 {K : Type'} (_91937 : K -> Prop) : (term914 K _91937) = (term915 K _91937).
Proof. exact (MK_COMB (@lem6888668) (@lem6888667 K _91937)). Qed.
Lemma lem6888671 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6888672 {K : Type'} (_91937 : K -> Prop) : (term1400 K _91937) = ((@CARD K _91937) = (NUMERAL 0)).
Proof. exact (@lem6888671 ((@CARD K _91937) = (NUMERAL 0))). Qed.
Lemma lem6888673 {K : Type'} (_91937 : K -> Prop) : (term1399 K _91937) = (term1401 K _91937).
Proof. exact (MK_COMB (@lem6888669 K _91937) (@lem6888672 K _91937)). Qed.
Lemma lem6888674 {K : Type'} (_91937 : K -> Prop) : (term1398 K _91937) = (term1401 K _91937).
Proof. exact (TRANS (@lem6888664 K _91937) (@lem6888673 K _91937)). Qed.
Lemma lem6888675 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6888676 {K : Type'} (_91937 : K -> Prop) : (term1402 K _91937) = (term1403 K _91937).
Proof. exact (MK_COMB (@lem6888675) (@lem6888674 K _91937)). Qed.
Lemma lem6888677 {K : Type'} (_91937 : K -> Prop) : (_91937 = (@EMPTY K)) = (_91937 = (@EMPTY K)).
Proof. exact (eq_refl (_91937 = (@EMPTY K))). Qed.
Lemma lem6888678 {K : Type'} (_91937 : K -> Prop) : (term1397 K _91937) = (term1404 K _91937).
Proof. exact (MK_COMB (@lem6888676 K _91937) (@lem6888677 K _91937)). Qed.
Lemma lem6888679 {K : Type'} (_91937 : K -> Prop) : (term1396 K _91937) = (term1404 K _91937).
Proof. exact (TRANS (@lem6888661 K _91937) (@lem6888678 K _91937)). Qed.
Lemma lem6888681 {K : Type'} (k : K -> Prop) (n : nat) (h1 : @FINITE K k) (h2 : n = (NUMERAL 0)) (h3 : (@CARD K k) = n) : term1401 K k.
Proof. exact (conj (@lem6888545 K k h1) (@lem6888552 K k n h2 h3)). Qed.
Lemma lem6888683 {K : Type'} (_91937 : K -> Prop) (h1 : term1312 K) : term1404 K _91937.
Proof. exact (EQ_MP (@lem6888679 K _91937) (@lem6888658 K _91937 h1)). Qed.
Lemma lem6888684 {K : Type'} (_91937 : K -> Prop) (h1 : term1312 K) : term1404 K _91937.
Proof. exact (@lem6888683 K _91937 h1). Qed.
Lemma lem6888685 {K : Type'} (k : K -> Prop) (h1 : term1312 K) : term1404 K k.
Proof. exact (@lem6888684 K k h1). Qed.
Lemma lem6888688 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : n = (NUMERAL 0)) (h4 : (@CARD K k) = n) : k = (@EMPTY K).
Proof. exact (@lem6888685 K k h1 (@lem6888681 K k n h2 h3 h4)). Qed.
Lemma lem6888689 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : n = (NUMERAL 0)) (h4 : (@CARD K k) = n) : term1405 K k.
Proof. exact (fun h0 : term835 K k => @lem6888688 K k n h1 h2 h3 h4). Qed.
Lemma lem6888691 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6888692 {K : Type'} (k : K -> Prop) : (term1405 K k) = (k = (@EMPTY K)).
Proof. exact (@lem6888691 (k = (@EMPTY K))). Qed.
Lemma lem6888693 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : n = (NUMERAL 0)) (h4 : (@CARD K k) = n) : k = (@EMPTY K).
Proof. exact (EQ_MP (@lem6888692 K k) (@lem6888689 K k n h1 h2 h3 h4)). Qed.
Lemma lem6888696 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6888698 {K : Type'} (k : K -> Prop) : (term835 K k) = (term1406 K k).
Proof. exact (@lem6888696 (k = (@EMPTY K))). Qed.
Lemma lem6888701 {K : Type'} (k : K -> Prop) (h1 : term835 K k) : term1406 K k.
Proof. exact (EQ_MP (@lem6888698 K k) (@lem6888312 K k h1)). Qed.
Lemma lem6888704 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (@lem6888701 K k h3 (@lem6888693 K k n h1 h2 h4 h5)). Qed.
Lemma lem6888705 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : term74.
Proof. exact (fun h0 : ~ False => @lem6888704 K k n h1 h2 h3 h4 h5). Qed.
Lemma lem6888707 (p : Prop) : (term72 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6888708 : term74 = False.
Proof. exact (@lem6888707 False). Qed.
Lemma lem6888709 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888708) (@lem6888705 K k n h1 h2 h3 h4 h5)). Qed.
Lemma lem6888710 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (term835 K k) = False.
Proof. exact (prop_ext (fun h6 : term835 K k => @lem6888709 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6888312 K k h3)). Qed.
Lemma lem6888711 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888710 K k n h1 h2 h3 h4 h5) (@lem6888312 K k h3)). Qed.
Lemma lem6888712 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (@FINITE K k) = False.
Proof. exact (prop_ext (fun h6 : @FINITE K k => @lem6888711 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6888285 K k h2)). Qed.
Lemma lem6888714 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888712 K k n h1 h2 h3 h4 h5) (@lem6888285 K k h2)). Qed.
Lemma lem6888715 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : n = (NUMERAL 0) => @lem6888714 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6888203 n h4)). Qed.
Lemma lem6888716 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888715 K k n h1 h2 h3 h4 h5) (@lem6888203 n h4)). Qed.
Lemma lem6888717 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (term835 K k) = False.
Proof. exact (prop_ext (fun h6 : term835 K k => @lem6888716 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6888195 K k h3)). Qed.
Lemma lem6888718 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888717 K k n h1 h2 h3 h4 h5) (@lem6888195 K k h3)). Qed.
Lemma lem6888719 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : ((@CARD K k) = n) = False.
Proof. exact (prop_ext (fun h6 : (@CARD K k) = n => @lem6888718 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6888193 K k n h5)). Qed.
Lemma lem6888720 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888719 K k n h1 h2 h3 h4 h5) (@lem6888193 K k n h5)). Qed.
Lemma lem6888721 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (@FINITE K k) = False.
Proof. exact (prop_ext (fun h6 : @FINITE K k => @lem6888720 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6888191 K k h2)). Qed.
Lemma lem6888722 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888721 K k n h1 h2 h3 h4 h5) (@lem6888191 K k h2)). Qed.
Lemma lem6888723 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : n = (NUMERAL 0) => @lem6888722 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6888107 n h4)). Qed.
Lemma lem6888724 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888723 K k n h1 h2 h3 h4 h5) (@lem6888107 n h4)). Qed.
Lemma lem6888725 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (term835 K k) = False.
Proof. exact (prop_ext (fun h6 : term835 K k => @lem6888724 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6888091 K k h3)). Qed.
Lemma lem6888726 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888725 K k n h1 h2 h3 h4 h5) (@lem6888091 K k h3)). Qed.
Lemma lem6888727 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : ((@CARD K k) = n) = False.
Proof. exact (prop_ext (fun h6 : (@CARD K k) = n => @lem6888726 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6888087 K k n h5)). Qed.
Lemma lem6888728 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888727 K k n h1 h2 h3 h4 h5) (@lem6888087 K k n h5)). Qed.
Lemma lem6888729 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (@FINITE K k) = False.
Proof. exact (prop_ext (fun h6 : @FINITE K k => @lem6888728 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6888083 K k h2)). Qed.
Lemma lem6888730 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888729 K k n h1 h2 h3 h4 h5) (@lem6888083 K k h2)). Qed.
Lemma lem6888731 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : n = (NUMERAL 0) => @lem6888730 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6888107 n h4)). Qed.
Lemma lem6888732 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888731 K k n h1 h2 h3 h4 h5) (@lem6888107 n h4)). Qed.
Lemma lem6888733 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (term835 K k) = False.
Proof. exact (prop_ext (fun h6 : term835 K k => @lem6888732 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6888091 K k h3)). Qed.
Lemma lem6888734 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888733 K k n h1 h2 h3 h4 h5) (@lem6888091 K k h3)). Qed.
Lemma lem6888735 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : ((@CARD K k) = n) = False.
Proof. exact (prop_ext (fun h6 : (@CARD K k) = n => @lem6888734 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6888087 K k n h5)). Qed.
Lemma lem6888736 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888735 K k n h1 h2 h3 h4 h5) (@lem6888087 K k n h5)). Qed.
Lemma lem6888737 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (@FINITE K k) = False.
Proof. exact (prop_ext (fun h6 : @FINITE K k => @lem6888736 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6888083 K k h2)). Qed.
Lemma lem6888738 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888737 K k n h1 h2 h3 h4 h5) (@lem6888083 K k h2)). Qed.
Lemma lem6888739 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : n = (NUMERAL 0) => @lem6888738 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6887969 n h4)). Qed.
Lemma lem6888740 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888739 K k n h1 h2 h3 h4 h5) (@lem6887969 n h4)). Qed.
Lemma lem6888741 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (term835 K k) = False.
Proof. exact (prop_ext (fun h6 : term835 K k => @lem6888740 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6887935 K k h3)). Qed.
Lemma lem6888742 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888741 K k n h1 h2 h3 h4 h5) (@lem6887935 K k h3)). Qed.
Lemma lem6888743 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : ((@CARD K k) = n) = False.
Proof. exact (prop_ext (fun h6 : (@CARD K k) = n => @lem6888742 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6887927 K k n h5)). Qed.
Lemma lem6888744 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888743 K k n h1 h2 h3 h4 h5) (@lem6887927 K k n h5)). Qed.
Lemma lem6888745 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (@FINITE K k) = False.
Proof. exact (prop_ext (fun h6 : @FINITE K k => @lem6888744 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6887919 K k h2)). Qed.
Lemma lem6888746 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888745 K k n h1 h2 h3 h4 h5) (@lem6887919 K k h2)). Qed.
Lemma lem6888747 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : n = (NUMERAL 0) => @lem6888746 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6887757 n h4)). Qed.
Lemma lem6888748 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888747 K k n h1 h2 h3 h4 h5) (@lem6887757 n h4)). Qed.
Lemma lem6888749 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (term835 K k) = False.
Proof. exact (prop_ext (fun h6 : term835 K k => @lem6888748 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6887733 K k h3)). Qed.
Lemma lem6888750 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888749 K k n h1 h2 h3 h4 h5) (@lem6887733 K k h3)). Qed.
Lemma lem6888751 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : ((@CARD K k) = n) = False.
Proof. exact (prop_ext (fun h6 : (@CARD K k) = n => @lem6888750 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6887727 K k n h5)). Qed.
Lemma lem6888752 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888751 K k n h1 h2 h3 h4 h5) (@lem6887727 K k n h5)). Qed.
Lemma lem6888753 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : (@FINITE K k) = False.
Proof. exact (prop_ext (fun h6 : @FINITE K k => @lem6888752 K k n h1 h2 h3 h4 h5) (fun h6 : False => @lem6887721 K k h2)). Qed.
Lemma lem6888754 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term1312 K) (h2 : @FINITE K k) (h3 : term835 K k) (h4 : n = (NUMERAL 0)) (h5 : (@CARD K k) = n) : False.
Proof. exact (EQ_MP (@lem6888753 K k n h1 h2 h3 h4 h5) (@lem6887721 K k h2)). Qed.
Lemma lem6888755 {K : Type'} (k : K -> Prop) (n : nat) (h1 : @FINITE K k) (h2 : term835 K k) (h3 : n = (NUMERAL 0)) (h4 : (@CARD K k) = n) : term1317 K.
Proof. exact (fun h0 : term1312 K => @lem6888754 K k n h0 h1 h2 h3 h4). Qed.
Lemma lem6888756 {K : Type'} : (term1317 K) = (term1318 K).
Proof. exact (@lem69 (term1312 K)). Qed.
Lemma lem6888757 {K : Type'} (k : K -> Prop) (n : nat) (h1 : @FINITE K k) (h2 : term835 K k) (h3 : n = (NUMERAL 0)) (h4 : (@CARD K k) = n) : term1318 K.
Proof. exact (EQ_MP (@lem6888756 K) (@lem6888755 K k n h1 h2 h3 h4)). Qed.
Lemma lem6888758 {_99911 K : Type'} (k : K -> Prop) (n : nat) (h1 : @FINITE K k) (h2 : term835 K k) (h3 : n = (NUMERAL 0)) (h4 : (@CARD K k) = n) : term1321 _99911 K.
Proof. exact (fun h0 : term1312 _99911 => @lem6888757 K k n h1 h2 h3 h4). Qed.
Lemma lem6888759 {_99911 K : Type'} (k : K -> Prop) (n : nat) (h1 : @FINITE K k) (h2 : term835 K k) (h3 : (@CARD K k) = n) : term1324 _99911 K n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem6888758 _99911 K k n h1 h2 h0 h3). Qed.
Lemma lem6888760 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : @FINITE K k) (h2 : term835 K k) (h3 : (@CARD K k) = n) : term1327 _99911 A K f i op n.
Proof. exact (fun h0 : term1022 A K f i op => @lem6888759 _99911 K k n h1 h2 h3). Qed.
Lemma lem6888761 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : @FINITE K k) (h2 : term835 K k) (h3 : (@CARD K k) = n) : term1330 _99911 A K f i op n.
Proof. exact (fun h0 : term1018 A K f i => @lem6888760 _99911 A K f i op k n h1 h2 h3). Qed.
Lemma lem6888762 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : @FINITE K k) (h2 : term835 K k) (h3 : (@CARD K k) = n) : term1332 _99911 A K k f i op n.
Proof. exact (fun h0 : @IN K i k => @lem6888761 _99911 A K f i op k n h1 h2 h3). Qed.
Lemma lem6888763 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : @FINITE K k) (h2 : (@CARD K k) = n) : term1335 _99911 A K k f i op n.
Proof. exact (fun h0 : term835 K k => @lem6888762 _99911 A K f i op k n h1 h0 h2). Qed.
Lemma lem6888764 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (n : nat) (k : K -> Prop) (h1 : @FINITE K k) : term1338 _99911 A K k f i op n.
Proof. exact (fun h0 : (@CARD K k) = n => @lem6888763 _99911 A K f i op k n h1 h0). Qed.
Lemma lem6888765 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : term1340 _99911 A K k f i op n.
Proof. exact (fun h0 : @FINITE K k => @lem6888764 _99911 A K f i op n k h0). Qed.
Lemma lem6888766 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : term1342 _99911 A K k f i op n.
Proof. exact (fun h0 : @monoidal A op => @lem6888765 _99911 A K k f i op n). Qed.
Lemma lem6888771 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (n : nat) : term1346 _99911 A K f i op n.
Proof. exact (fun k : K -> Prop => @lem6888766 _99911 A K k f i op n). Qed.
Lemma lem6888776 {_99911 A K : Type'} (i : K) (op : type1400 A) (n : nat) : term1350 _99911 A K i op n.
Proof. exact (fun f : K -> A => @lem6888771 _99911 A K f i op n). Qed.
Lemma lem6888781 {_99911 A K : Type'} (op : type1400 A) (n : nat) : term1354 _99911 A K op n.
Proof. exact (fun i : K => @lem6888776 _99911 A K i op n). Qed.
Lemma lem6888786 {_99911 A K : Type'} (n : nat) : term1358 _99911 A K n.
Proof. exact (fun op : type1400 A => @lem6888781 _99911 A K op n). Qed.
Lemma lem6888791 {_99911 A K : Type'} : term1362 _99911 A K.
Proof. exact (fun n : nat => @lem6888786 _99911 A K n). Qed.
Lemma lem6888792 {_99911 A K : Type'} : term1361 _99911 A K.
Proof. exact (EQ_MP (@lem6887699 _99911 A K) (@lem6888791 _99911 A K)). Qed.
Lemma lem6888793 {_99911 A K : Type'} (n : nat) : term1407 _99911 A K n.
Proof. exact (@lem6888792 _99911 A K n). Qed.
Lemma lem6888794 {_99911 A K : Type'} (n : nat) : (term1407 _99911 A K n) = (term1357 _99911 A K n).
Proof. exact (eq_refl (term1407 _99911 A K n)). Qed.
Lemma lem6888795 {_99911 A K : Type'} (n : nat) : term1357 _99911 A K n.
Proof. exact (EQ_MP (@lem6888794 _99911 A K n) (@lem6888793 _99911 A K n)). Qed.
Lemma lem6888796 {_99911 A K : Type'} (n : nat) (op : type1400 A) : term1408 _99911 A K n op.
Proof. exact (@lem6888795 _99911 A K n op). Qed.
Lemma lem6888797 {_99911 A K : Type'} (op : type1400 A) (n : nat) : (term1408 _99911 A K n op) = (term1353 _99911 A K op n).
Proof. exact (eq_refl (term1408 _99911 A K n op)). Qed.
Lemma lem6888798 {_99911 A K : Type'} (op : type1400 A) (n : nat) : term1353 _99911 A K op n.
Proof. exact (EQ_MP (@lem6888797 _99911 A K op n) (@lem6888796 _99911 A K n op)). Qed.
Lemma lem6888799 {_99911 A K : Type'} (op : type1400 A) (n : nat) (i : K) : term1409 _99911 A K op n i.
Proof. exact (@lem6888798 _99911 A K op n i). Qed.
Lemma lem6888800 {_99911 A K : Type'} (i : K) (op : type1400 A) (n : nat) : (term1409 _99911 A K op n i) = (term1349 _99911 A K i op n).
Proof. exact (eq_refl (term1409 _99911 A K op n i)). Qed.
Lemma lem6888801 {_99911 A K : Type'} (i : K) (op : type1400 A) (n : nat) : term1349 _99911 A K i op n.
Proof. exact (EQ_MP (@lem6888800 _99911 A K i op n) (@lem6888799 _99911 A K op n i)). Qed.
Lemma lem6888802 {_99911 A K : Type'} (i : K) (op : type1400 A) (n : nat) (f : K -> A) : term1410 _99911 A K i op n f.
Proof. exact (@lem6888801 _99911 A K i op n f). Qed.
Lemma lem6888803 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1410 _99911 A K i op n f) = (term1345 _99911 A K f i op n).
Proof. exact (eq_refl (term1410 _99911 A K i op n f)). Qed.
Lemma lem6888804 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (n : nat) : term1345 _99911 A K f i op n.
Proof. exact (EQ_MP (@lem6888803 _99911 A K f i op n) (@lem6888802 _99911 A K i op n f)). Qed.
Lemma lem6888805 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (n : nat) (k : K -> Prop) : term1411 _99911 A K f i op n k.
Proof. exact (@lem6888804 _99911 A K f i op n k). Qed.
Lemma lem6888806 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : (term1411 _99911 A K f i op n k) = (term1313 _99911 A K k f i op n).
Proof. exact (eq_refl (term1411 _99911 A K f i op n k)). Qed.
Lemma lem6888807 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : term1313 _99911 A K k f i op n.
Proof. exact (EQ_MP (@lem6888806 _99911 A K k f i op n) (@lem6888805 _99911 A K f i op n k)). Qed.
Lemma lem6888809 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (op : type1400 A) (n : nat) : term1313 _99911 A K k f i op n.
Proof. exact (@lem6887423 _99911 A K k f i op n (@lem6888807 _99911 A K k f i op n)). Qed.
Lemma lem6888810 {_99911 A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) (n : nat) (op : type1400 A) (h1 : @monoidal A op) : term1339 _99911 A K k f i op n.
Proof. exact (@lem6888809 _99911 A K k f i op n (@lem6884878 A op h1)). Qed.
Lemma lem6888811 {_99911 A K : Type'} (f : K -> A) (i : K) (n : nat) (k : K -> Prop) (op : type1400 A) (h1 : @FINITE K k) (h2 : @monoidal A op) : term1337 _99911 A K k f i op n.
Proof. exact (@lem6888810 _99911 A K k f i n op h2 (@lem6884937 K k h1)). Qed.
Lemma lem6888812 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : (@CARD K k) = n) : term1334 _99911 A K k f i op n.
Proof. exact (@lem6888811 _99911 A K f i n k op h1 h2 (@lem6884941 K k n h3)). Qed.
Lemma lem6888813 {_99911 A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : term835 K k) (h4 : (@CARD K k) = n) : term1331 _99911 A K k f i op n.
Proof. exact (@lem6888812 _99911 A K f i op k n h1 h2 h4 (@lem6883610 K k h3)). Qed.
Lemma lem6888814 {_99911 A K : Type'} (f : K -> A) (op : type1400 A) (n : nat) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : term835 K k) (h4 : (@CARD K k) = n) (h5 : @IN K i k) : term1329 _99911 A K f i op n.
Proof. exact (@lem6888813 _99911 A K f i op k n h1 h2 h3 h4 (@lem6886955 K i k h5)). Qed.
Lemma lem6888815 {_99911 A K : Type'} (op : type1400 A) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : term835 K k) (h4 : (@CARD K k) = n) (h5 : term1018 A K f i) (h6 : @IN K i k) : term1326 _99911 A K f i op n.
Proof. exact (@lem6888814 _99911 A K f op n i k h1 h2 h3 h4 h6 (@lem6886959 A K f i h5)). Qed.
Lemma lem6888816 {_99911 A K : Type'} (op : type1400 A) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : term1022 A K f i op) (h4 : term835 K k) (h5 : (@CARD K k) = n) (h6 : term1018 A K f i) (h7 : @IN K i k) : term1323 _99911 K n.
Proof. exact (@lem6888815 _99911 A K op n f i k h1 h2 h4 h5 h6 h7 (@lem6886958 A K f i op h3)). Qed.
Lemma lem6888817 {_99911 A K : Type'} (op : type1400 A) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : term1022 A K f i op) (h4 : term835 K k) (h5 : n = (NUMERAL 0)) (h6 : (@CARD K k) = n) (h7 : term1018 A K f i) (h8 : @IN K i k) : term1320 _99911 K.
Proof. exact (@lem6888816 _99911 A K op n f i k h1 h2 h3 h4 h6 h7 h8 (@lem6887403 n h5)). Qed.
Lemma lem6888818 {A K : Type'} (op : type1400 A) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : term1022 A K f i op) (h4 : term835 K k) (h5 : n = (NUMERAL 0)) (h6 : (@CARD K k) = n) (h7 : term1018 A K f i) (h8 : @IN K i k) : term1317 K.
Proof. exact (@lem6888817 Prop A K op n f i k h1 h2 h3 h4 h5 h6 h7 h8 (@lem3854502 Prop)). Qed.
Lemma lem6888819 {A K : Type'} (op : type1400 A) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : term1022 A K f i op) (h4 : term835 K k) (h5 : n = (NUMERAL 0)) (h6 : (@CARD K k) = n) (h7 : term1018 A K f i) (h8 : @IN K i k) : False.
Proof. exact (@lem6888818 A K op n f i k h1 h2 h3 h4 h5 h6 h7 h8 (@lem6887404 K)). Qed.
Lemma lem6888820 {A K : Type'} (op : type1400 A) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : term1022 A K f i op) (h4 : term835 K k) (h5 : n = (NUMERAL 0)) (h6 : (@CARD K k) = n) (h7 : term1018 A K f i) (h8 : @IN K i k) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h9 : n = (NUMERAL 0) => @lem6888819 A K op n f i k h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem6887403 n h5)). Qed.
Lemma lem6888821 {A K : Type'} (op : type1400 A) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : term1022 A K f i op) (h4 : term835 K k) (h5 : n = (NUMERAL 0)) (h6 : (@CARD K k) = n) (h7 : term1018 A K f i) (h8 : @IN K i k) : False.
Proof. exact (EQ_MP (@lem6888820 A K op n f i k h1 h2 h3 h4 h5 h6 h7 h8) (@lem6887403 n h5)). Qed.
Lemma lem6888822 {A K : Type'} (op : type1400 A) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : term1022 A K f i op) (h4 : term835 K k) (h5 : (@CARD K k) = n) (h6 : term1018 A K f i) (h7 : @IN K i k) : term1412 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem6888821 A K op n f i k h1 h2 h3 h4 h0 h5 h6 h7). Qed.
Lemma lem6888823 (n : nat) : (term1412 n) = (term89 n).
Proof. exact (@lem69 (n = (NUMERAL 0))). Qed.
Lemma lem6888824 {A K : Type'} (op : type1400 A) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : term1022 A K f i op) (h4 : term835 K k) (h5 : (@CARD K k) = n) (h6 : term1018 A K f i) (h7 : @IN K i k) : term89 n.
Proof. exact (EQ_MP (@lem6888823 n) (@lem6888822 A K op n f i k h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem6888825 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) (h1 : (term1247 A K op ltle k i f) = (term1248 A K op k i f)) : (term1247 A K op ltle k i f) = (term1248 A K op k i f).
Proof. exact (h1). Qed.
Lemma lem6888826 {A K : Type'} (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1413 A K i op k f) = (term1413 A K i op k f).
Proof. exact (eq_refl (term1413 A K i op k f)). Qed.
Lemma lem6888827 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) (h1 : (term1247 A K op ltle k i f) = (term1248 A K op k i f)) : (term1414 A K op ltle k i f) = (term1415 A K op k i f).
Proof. exact (MK_COMB (@lem6888826 A K i op k f) (@lem6888825 A K ltle op k i f h1)). Qed.
Lemma lem6888828 {A K : Type'} (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1415 A K op k i f) = ((term1416 A K op k i f) = (@iterate A K op k f)).
Proof. exact (eq_refl (term1415 A K op k i f)). Qed.
Lemma lem6888829 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) : (term1417 A K op ltle k i f) = (term1417 A K op ltle k i f).
Proof. exact (eq_refl (term1417 A K op ltle k i f)). Qed.
Lemma lem6888830 {A K : Type'} (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : ((term1414 A K op ltle k i f) = (term1415 A K op k i f)) = ((term1414 A K op ltle k i f) = ((term1416 A K op k i f) = (@iterate A K op k f))).
Proof. exact (MK_COMB (@lem6888829 A K op ltle k i f) (@lem6888828 A K i op k f)). Qed.
Lemma lem6888831 {A K : Type'} (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1414 A K op ltle k i f) = ((term1222 A K op ltle k i f) = (@iterate A K op k f)).
Proof. exact (eq_refl (term1414 A K op ltle k i f)). Qed.
Lemma lem6888832 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6888833 {A K : Type'} (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : (term1417 A K op ltle k i f) = (term1418 A K ltle i op k f).
Proof. exact (MK_COMB (@lem6888832) (@lem6888831 A K ltle i op k f)). Qed.
Lemma lem6888834 {A K : Type'} (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : ((term1416 A K op k i f) = (@iterate A K op k f)) = ((term1416 A K op k i f) = (@iterate A K op k f)).
Proof. exact (eq_refl ((term1416 A K op k i f) = (@iterate A K op k f))). Qed.
Lemma lem6888835 {A K : Type'} (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : ((term1414 A K op ltle k i f) = ((term1416 A K op k i f) = (@iterate A K op k f))) = (((term1222 A K op ltle k i f) = (@iterate A K op k f)) = ((term1416 A K op k i f) = (@iterate A K op k f))).
Proof. exact (MK_COMB (@lem6888833 A K ltle i op k f) (@lem6888834 A K i op k f)). Qed.
Lemma lem6888836 {A K : Type'} (ltle : type1402 K) (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : ((term1414 A K op ltle k i f) = (term1415 A K op k i f)) = (((term1222 A K op ltle k i f) = (@iterate A K op k f)) = ((term1416 A K op k i f) = (@iterate A K op k f))).
Proof. exact (TRANS (@lem6888830 A K ltle i op k f) (@lem6888835 A K ltle i op k f)). Qed.
Lemma lem6888837 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) (h1 : (term1247 A K op ltle k i f) = (term1248 A K op k i f)) : ((term1222 A K op ltle k i f) = (@iterate A K op k f)) = ((term1416 A K op k i f) = (@iterate A K op k f)).
Proof. exact (EQ_MP (@lem6888836 A K ltle i op k f) (@lem6888827 A K ltle op k i f h1)). Qed.
Lemma lem6888838 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) (h1 : (term1247 A K op ltle k i f) = (term1248 A K op k i f)) : ((term1416 A K op k i f) = (@iterate A K op k f)) = ((term1222 A K op ltle k i f) = (@iterate A K op k f)).
Proof. exact (SYM (@lem6888837 A K ltle op k i f h1)). Qed.
Lemma lem6888852 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term80 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem6876424 _120477 _120519 _120521 op) (@lem6876423 _120477 _120519 _120521 op)). Qed.
Lemma lem6888853 {_120477 _120521 A : Type'} (op : type1400 A) : term1419 _120477 _120521 A op.
Proof. exact (@lem6888852 _120477 A _120521 op). Qed.
Lemma lem6888854 {_120477 _120521 A : Type'} (op : type1400 A) (h1 : @monoidal A op) : term1420 _120477 _120521 A op.
Proof. exact (@lem6888853 _120477 _120521 A op (@lem6884878 A op h1)). Qed.
Lemma lem6888855 {_120521 A : Type'} (op : type1400 A) (h1 : @monoidal A op) : term1421 _120521 A op.
Proof. exact (proj2 (@lem6888854 Prop _120521 A op h1)). Qed.
Lemma lem6888856 {A K : Type'} (op : type1400 A) (h1 : @monoidal A op) : term1422 A K op.
Proof. exact (@lem6888855 K A op h1). Qed.
Lemma lem6888857 {A K : Type'} (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : term1423 A K op f.
Proof. exact (@lem6888856 A K op h1 f). Qed.
Lemma lem6888858 {A K : Type'} (op : type1400 A) (f : K -> A) : (term1423 A K op f) = (term1424 A K op f).
Proof. exact (eq_refl (term1423 A K op f)). Qed.
Lemma lem6888859 {A K : Type'} (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : term1424 A K op f.
Proof. exact (EQ_MP (@lem6888858 A K op f) (@lem6888857 A K f op h1)). Qed.
Lemma lem6888860 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (h1 : @monoidal A op) : term1425 A K op f i.
Proof. exact (@lem6888859 A K f op h1 i). Qed.
Lemma lem6888861 {A K : Type'} (i : K) (op : type1400 A) (f : K -> A) : (term1425 A K op f i) = (term1426 A K i op f).
Proof. exact (eq_refl (term1425 A K op f i)). Qed.
Lemma lem6888862 {A K : Type'} (i : K) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : term1426 A K i op f.
Proof. exact (EQ_MP (@lem6888861 A K i op f) (@lem6888860 A K f i op h1)). Qed.
Lemma lem6888863 {A K : Type'} (f : K -> A) (k : K -> Prop) (i : K) (op : type1400 A) (h1 : @monoidal A op) : term1427 A K op f k i.
Proof. exact (@lem6888862 A K i f op h1 (@DELETE K k i)). Qed.
Lemma lem6888864 {A K : Type'} (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : (term1427 A K op f k i) = (term1428 A K op k i f).
Proof. exact (eq_refl (term1427 A K op f k i)). Qed.
Lemma lem6888865 {A K : Type'} (k : K -> Prop) (i : K) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : term1428 A K op k i f.
Proof. exact (EQ_MP (@lem6888864 A K op k i f) (@lem6888863 A K f k i op h1)). Qed.
Lemma lem6888866 {A : Type'} (s : A -> Prop) : term1429 A s.
Proof. exact (@lem3205803 A s). Qed.
Lemma lem6888867 {A : Type'} (s : A -> Prop) : (term1429 A s) = (term1430 A s).
Proof. exact (eq_refl (term1429 A s)). Qed.
Lemma lem6888868 {A : Type'} (s : A -> Prop) : term1430 A s.
Proof. exact (EQ_MP (@lem6888867 A s) (@lem6888866 A s)). Qed.
Lemma lem6888869 {A : Type'} (s : A -> Prop) (x : A) : term1431 A s x.
Proof. exact (@lem6888868 A s x). Qed.
Lemma lem6888870 {A : Type'} (s : A -> Prop) (x : A) : (term1431 A s x) = (term1432 A s x).
Proof. exact (eq_refl (term1431 A s x)). Qed.
Lemma lem6888871 {A : Type'} (s : A -> Prop) (x : A) : term1432 A s x.
Proof. exact (EQ_MP (@lem6888870 A s x) (@lem6888869 A s x)). Qed.
Lemma lem6888872 {A : Type'} (s : A -> Prop) (x : A) (y : A) : term1433 A s x y.
Proof. exact (@lem6888871 A s x y). Qed.
Lemma lem6888873 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term1433 A s x y) = ((term11 A x s y) = (term12 A s x y)).
Proof. exact (eq_refl (term1433 A s x y)). Qed.
Lemma lem6888875 {A : Type'} (s : A -> Prop) : term1260 A s.
Proof. exact (@lem3610594 A s). Qed.
Lemma lem6888876 {A : Type'} (s : A -> Prop) : (term1260 A s) = (term1261 A s).
Proof. exact (eq_refl (term1260 A s)). Qed.
Lemma lem6888877 {A : Type'} (s : A -> Prop) : term1261 A s.
Proof. exact (EQ_MP (@lem6888876 A s) (@lem6888875 A s)). Qed.
Lemma lem6888878 {A : Type'} (s : A -> Prop) (x : A) : term1262 A s x.
Proof. exact (@lem6888877 A s x). Qed.
Lemma lem6888879 {A : Type'} (x : A) (s : A -> Prop) : (term1262 A s x) = ((term1263 A s x) = (@FINITE A s)).
Proof. exact (eq_refl (term1262 A s x)). Qed.
Lemma lem6888881 {K : Type'} (k : K -> Prop) : (@FINITE K k) = ((@FINITE K k) = True).
Proof. exact (@lem7 (@FINITE K k)). Qed.
Lemma lem6888896 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = ((@IN K i k) = True).
Proof. exact (@lem7 (@IN K i k)). Qed.
Lemma lem6888918 {A : Type'} (x : A) (s : A -> Prop) : (term1263 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem6888879 A x s) (@lem6888878 A s x)). Qed.
Lemma lem6888919 {K : Type'} (x : K) (s : K -> Prop) : (term1263 K s x) = (@FINITE K s).
Proof. exact (@lem6888918 K x s). Qed.
Lemma lem6888920 {K : Type'} (i : K) (k : K -> Prop) : (term1263 K k i) = (@FINITE K k).
Proof. exact (@lem6888919 K i k). Qed.
Lemma lem6888922 {K : Type'} (k : K -> Prop) (h1 : @FINITE K k) : (@FINITE K k) = True.
Proof. exact (EQ_MP (@lem6888881 K k) (@lem6884937 K k h1)). Qed.
Lemma lem6888923 {K : Type'} (i : K) (k : K -> Prop) (h1 : @FINITE K k) : (term1263 K k i) = True.
Proof. exact (TRANS (@lem6888920 K i k) (@lem6888922 K k h1)). Qed.
Lemma lem6888924 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6888925 {K : Type'} (i : K) (k : K -> Prop) (h1 : @FINITE K k) : (term1434 K k i) = (imp True).
Proof. exact (MK_COMB (@lem6888924) (@lem6888923 K i k h1)). Qed.
Lemma lem6888929 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term11 A x s y) = (term12 A s x y).
Proof. exact (EQ_MP (@lem6888873 A s x y) (@lem6888872 A s x y)). Qed.
Lemma lem6888930 {K : Type'} (s : K -> Prop) (x : K) (y : K) : (term11 K x s y) = (term12 K s x y).
Proof. exact (@lem6888929 K s x y). Qed.
Lemma lem6888931 {K : Type'} (k : K -> Prop) (i : K) : (term1435 K k i) = (term1436 K k i).
Proof. exact (@lem6888930 K k i i). Qed.
Lemma lem6888935 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : (@IN K i k) = True.
Proof. exact (EQ_MP (@lem6888896 K i k) (@lem6886955 K i k h1)). Qed.
Lemma lem6888936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6888937 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term13 K i k) = (and True).
Proof. exact (MK_COMB (@lem6888936) (@lem6888935 K i k h1)). Qed.
Lemma lem6888939 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6888940 {K : Type'} (x : K) : (x = x) = True.
Proof. exact (@lem6888939 K x). Qed.
Lemma lem6888941 {K : Type'} (i : K) : (i = i) = True.
Proof. exact (@lem6888940 K i). Qed.
Lemma lem6888942 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6888943 {K : Type'} (i : K) : (term68 K i) = (~ True).
Proof. exact (MK_COMB (@lem6888942) (@lem6888941 K i)). Qed.
Lemma lem6888945 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem6888946 {K : Type'} (i : K) : (term68 K i) = False.
Proof. exact (TRANS (@lem6888943 K i) (@lem6888945)). Qed.
Lemma lem6888947 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term1436 K k i) = (True /\ False).
Proof. exact (MK_COMB (@lem6888937 K i k h1) (@lem6888946 K i)). Qed.
Lemma lem6888949 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem6888950 : (True /\ False) = False.
Proof. exact (@lem6888949 False). Qed.
Lemma lem6888951 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term1436 K k i) = False.
Proof. exact (TRANS (@lem6888947 K i k h1) (@lem6888950)). Qed.
Lemma lem6888952 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term1435 K k i) = False.
Proof. exact (TRANS (@lem6888931 K k i) (@lem6888951 K i k h1)). Qed.
Lemma lem6888953 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem6888954 {A K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term1437 A K k i) = (@COND A False).
Proof. exact (MK_COMB (@lem6888953 A) (@lem6888952 K i k h1)). Qed.
Lemma lem6888955 {A K : Type'} (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : (term1248 A K op k i f) = (term1248 A K op k i f).
Proof. exact (eq_refl (term1248 A K op k i f)). Qed.
Lemma lem6888956 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term1438 A K op k i f) = (term1439 A K op k i f).
Proof. exact (MK_COMB (@lem6888954 A K i k h1) (@lem6888955 A K op k i f)). Qed.
Lemma lem6888957 {A K : Type'} (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : (term1416 A K op k i f) = (term1416 A K op k i f).
Proof. exact (eq_refl (term1416 A K op k i f)). Qed.
Lemma lem6888958 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term1440 A K op k i f) = (term1441 A K op k i f).
Proof. exact (MK_COMB (@lem6888956 A K op f i k h1) (@lem6888957 A K op k i f)). Qed.
Lemma lem6888960 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem6888961 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem6888960 A t1 t2). Qed.
Lemma lem6888962 {A K : Type'} (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : (term1441 A K op k i f) = (term1416 A K op k i f).
Proof. exact (@lem6888961 A (term1248 A K op k i f) (term1416 A K op k i f)). Qed.
Lemma lem6888963 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term1440 A K op k i f) = (term1416 A K op k i f).
Proof. exact (TRANS (@lem6888958 A K op f i k h1) (@lem6888962 A K op k i f)). Qed.
Lemma lem6888964 {A K : Type'} (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : (term1442 A K op k i f) = (term1442 A K op k i f).
Proof. exact (eq_refl (term1442 A K op k i f)). Qed.
Lemma lem6888965 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : ((term1443 A K op k i f) = (term1440 A K op k i f)) = ((term1443 A K op k i f) = (term1416 A K op k i f)).
Proof. exact (MK_COMB (@lem6888964 A K op k i f) (@lem6888963 A K op f i k h1)). Qed.
Lemma lem6888968 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @IN K i k) : (term1428 A K op k i f) = (term1444 A K op k i f).
Proof. exact (MK_COMB (@lem6888925 K i k h1) (@lem6888965 A K op f i k h2)). Qed.
Lemma lem6888970 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem6888971 {A K : Type'} (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : (term1444 A K op k i f) = ((term1443 A K op k i f) = (term1416 A K op k i f)).
Proof. exact (@lem6888970 ((term1443 A K op k i f) = (term1416 A K op k i f))). Qed.
Lemma lem6888974 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @IN K i k) : (term1428 A K op k i f) = ((term1443 A K op k i f) = (term1416 A K op k i f)).
Proof. exact (TRANS (@lem6888968 A K op f i k h1 h2) (@lem6888971 A K op k i f)). Qed.
Lemma lem6888975 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6888976 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @IN K i k) : (term1445 A K op k i f) = (term1446 A K op k i f).
Proof. exact (MK_COMB (@lem6888975) (@lem6888974 A K op f i k h1 h2)). Qed.
Lemma lem6888979 {A K : Type'} (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : ((term1416 A K op k i f) = (@iterate A K op k f)) = ((term1416 A K op k i f) = (@iterate A K op k f)).
Proof. exact (eq_refl ((term1416 A K op k i f) = (@iterate A K op k f))). Qed.
Lemma lem6888980 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @IN K i k) : (term1447 A K i op k f) = (term1448 A K i op k f).
Proof. exact (MK_COMB (@lem6888976 A K op f i k h1 h2) (@lem6888979 A K i op k f)). Qed.
Lemma lem6888985 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @IN K i k) : (term1448 A K i op k f) = (term1447 A K i op k f).
Proof. exact (SYM (@lem6888980 A K op f i k h1 h2)). Qed.
Lemma lem6888986 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (h1 : @IN _125820 i k) : @IN _125820 i k.
Proof. exact (h1). Qed.
Lemma lem6888987 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) (h1 : @IN _125820 i k) : (term1 _125820 k i) = k.
Proof. exact (@lem6876422 _125820 i k (@lem6888986 _125820 i k h1)). Qed.
Lemma lem6889008 {K : Type'} (i : K) (k : K -> Prop) : (@IN K i k) = ((@IN K i k) = True).
Proof. exact (@lem7 (@IN K i k)). Qed.
Lemma lem6889030 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term1154 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem6889031 (p : Prop) (q : Prop) (p' : Prop) : term1155 p q p'.
Proof. exact (fun q' : Prop => @lem6889030 p q p' q'). Qed.
Lemma lem6889032 (p : Prop) (q : Prop) : term1156 p q.
Proof. exact (fun p' : Prop => @lem6889031 p q p'). Qed.
Lemma lem6889033 {A K : Type'} (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : term1449 A K i op k f.
Proof. exact (@lem6889032 ((term1443 A K op k i f) = (term1416 A K op k i f)) ((term1416 A K op k i f) = (@iterate A K op k f))). Qed.
Lemma lem6889034 {A K : Type'} (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) : term1450 A K i op k f p'.
Proof. exact (@lem6889033 A K i op k f p'). Qed.
Lemma lem6889035 {A K : Type'} (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) : (term1450 A K i op k f p') = (term1451 A K i op k f p').
Proof. exact (eq_refl (term1450 A K i op k f p')). Qed.
Lemma lem6889036 {A K : Type'} (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) : term1451 A K i op k f p'.
Proof. exact (EQ_MP (@lem6889035 A K i op k f p') (@lem6889034 A K i op k f p')). Qed.
Lemma lem6889037 {A K : Type'} (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) (q' : Prop) : term1452 A K i op k f p' q'.
Proof. exact (@lem6889036 A K i op k f p' q'). Qed.
Lemma lem6889038 {A K : Type'} (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) (q' : Prop) : (term1452 A K i op k f p' q') = (term1453 A K i op k f p' q').
Proof. exact (eq_refl (term1452 A K i op k f p' q')). Qed.
Lemma lem6889039 {A K : Type'} (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) (p' : Prop) (q' : Prop) : term1453 A K i op k f p' q'.
Proof. exact (EQ_MP (@lem6889038 A K i op k f p' q') (@lem6889037 A K i op k f p' q')). Qed.
Lemma lem6889043 {_125820 : Type'} (i : _125820) (k : _125820 -> Prop) : term4 _125820 i k.
Proof. exact (fun h0 : @IN _125820 i k => @lem6888987 _125820 i k h0). Qed.
Lemma lem6889044 {K : Type'} (i : K) (k : K -> Prop) : term4 K i k.
Proof. exact (@lem6889043 K i k). Qed.
Lemma lem6889046 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : (@IN K i k) = True.
Proof. exact (EQ_MP (@lem6889008 K i k) (@lem6886955 K i k h1)). Qed.
Lemma lem6889047 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : True = (@IN K i k).
Proof. exact (SYM (@lem6889046 K i k h1)). Qed.
Lemma lem6889048 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : @IN K i k.
Proof. exact (EQ_MP (@lem6889047 K i k h1) (@lem0)). Qed.
Lemma lem6889049 {K : Type'} (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term1 K k i) = k.
Proof. exact (@lem6889044 K i k (@lem6889048 K i k h1)). Qed.
Lemma lem6889050 {A K : Type'} (op : type1400 A) : (@iterate A K op) = (@iterate A K op).
Proof. exact (eq_refl (@iterate A K op)). Qed.
Lemma lem6889051 {A K : Type'} (op : type1400 A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term1454 A K op k i) = (@iterate A K op k).
Proof. exact (MK_COMB (@lem6889050 A K op) (@lem6889049 K i k h1)). Qed.
Lemma lem6889052 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6889053 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term1443 A K op k i f) = (@iterate A K op k f).
Proof. exact (MK_COMB (@lem6889051 A K op i k h1) (@lem6889052 A K f)). Qed.
Lemma lem6889054 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6889055 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term1442 A K op k i f) = (term1455 A K op k f).
Proof. exact (MK_COMB (@lem6889054 A) (@lem6889053 A K op f i k h1)). Qed.
Lemma lem6889056 {A K : Type'} (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : (term1416 A K op k i f) = (term1416 A K op k i f).
Proof. exact (eq_refl (term1416 A K op k i f)). Qed.
Lemma lem6889057 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : ((term1443 A K op k i f) = (term1416 A K op k i f)) = ((@iterate A K op k f) = (term1416 A K op k i f)).
Proof. exact (MK_COMB (@lem6889055 A K op f i k h1) (@lem6889056 A K op k i f)). Qed.
Lemma lem6889060 {A K : Type'} (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) (q' : Prop) : term1456 A K op k i f q'.
Proof. exact (@lem6889039 A K i op k f ((@iterate A K op k f) = (term1416 A K op k i f)) q'). Qed.
Lemma lem6889061 {A K : Type'} (op : type1400 A) (f : K -> A) (q' : Prop) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term1457 A K op k i f q'.
Proof. exact (@lem6889060 A K op k i f q' (@lem6889057 A K op f i k h1)). Qed.
Lemma lem6889066 {A K : Type'} (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) (h1 : (@iterate A K op k f) = (term1416 A K op k i f)) : (@iterate A K op k f) = (term1416 A K op k i f).
Proof. exact (h1). Qed.
Lemma lem6889067 {A K : Type'} (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : (term1458 A K op k i f) = (term1458 A K op k i f).
Proof. exact (eq_refl (term1458 A K op k i f)). Qed.
Lemma lem6889068 {A K : Type'} (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) (h1 : (@iterate A K op k f) = (term1416 A K op k i f)) : ((term1416 A K op k i f) = (@iterate A K op k f)) = ((term1416 A K op k i f) = (term1416 A K op k i f)).
Proof. exact (MK_COMB (@lem6889067 A K op k i f) (@lem6889066 A K op k i f h1)). Qed.
Lemma lem6889070 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6889071 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem6889070 A x). Qed.
Lemma lem6889072 {A K : Type'} (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : ((term1416 A K op k i f) = (term1416 A K op k i f)) = True.
Proof. exact (@lem6889071 A (term1416 A K op k i f)). Qed.
Lemma lem6889073 {A K : Type'} (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) (h1 : (@iterate A K op k f) = (term1416 A K op k i f)) : ((term1416 A K op k i f) = (@iterate A K op k f)) = True.
Proof. exact (TRANS (@lem6889068 A K op k i f h1) (@lem6889072 A K op k i f)). Qed.
Lemma lem6889074 {A K : Type'} (i : K) (op : type1400 A) (k : K -> Prop) (f : K -> A) : term1459 A K i op k f.
Proof. exact (fun h0 : (@iterate A K op k f) = (term1416 A K op k i f) => @lem6889073 A K op k i f h0). Qed.
Lemma lem6889075 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term1460 A K op k i f.
Proof. exact (@lem6889061 A K op f True i k h1). Qed.
Lemma lem6889076 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term1448 A K i op k f) = (term1461 A K op k i f).
Proof. exact (@lem6889075 A K op f i k h1 (@lem6889074 A K i op k f)). Qed.
Lemma lem6889080 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem6889081 {A K : Type'} (op : type1400 A) (k : K -> Prop) (i : K) (f : K -> A) : (term1461 A K op k i f) = True.
Proof. exact (@lem6889080 ((@iterate A K op k f) = (term1416 A K op k i f))). Qed.
Lemma lem6889082 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : (term1448 A K i op k f) = True.
Proof. exact (TRANS (@lem6889076 A K op f i k h1) (@lem6889081 A K op k i f)). Qed.
Lemma lem6889083 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : True = (term1448 A K i op k f).
Proof. exact (SYM (@lem6889082 A K op f i k h1)). Qed.
Lemma lem6889084 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @IN K i k) : term1448 A K i op k f.
Proof. exact (EQ_MP (@lem6889083 A K op f i k h1) (@lem0)). Qed.
Lemma lem6889085 {A K : Type'} (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @IN K i k) : term1447 A K i op k f.
Proof. exact (EQ_MP (@lem6888985 A K op f i k h1 h2) (@lem6889084 A K op f i k h2)). Qed.
Lemma lem6889086 {A K : Type'} (f : K -> A) (op : type1400 A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : @IN K i k) : (term1416 A K op k i f) = (@iterate A K op k f).
Proof. exact (@lem6889085 A K op f i k h1 h3 (@lem6888865 A K k i f op h2)). Qed.
Lemma lem6889087 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : (term1247 A K op ltle k i f) = (term1248 A K op k i f)) (h4 : @IN K i k) : (term1222 A K op ltle k i f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6888838 A K ltle op k i f h3) (@lem6889086 A K f op i k h1 h2 h4)). Qed.
Lemma lem6889088 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : @IN K i k) : term1462 A K ltle i op k f.
Proof. exact (fun h0 : (term1247 A K op ltle k i f) = (term1248 A K op k i f) => @lem6889087 A K ltle op f i k h1 h2 h0 h3). Qed.
Lemma lem6889089 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : term1022 A K f i op) (h4 : term835 K k) (h5 : (@CARD K k) = n) (h6 : term1018 A K f i) (h7 : @IN K i k) : term1463 A K n ltle i op k f.
Proof. exact (conj (@lem6888824 A K op n f i k h1 h2 h3 h4 h5 h6 h7) (@lem6889088 A K ltle f op i k h1 h2 h7)). Qed.
Lemma lem6889090 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : term1022 A K f i op) (h4 : term835 K k) (h5 : (@CARD K k) = n) (h6 : term1018 A K f i) (h7 : @IN K i k) : term1309 A K n ltle i op k f.
Proof. exact (@lem6887402 A K n ltle i op k f (@lem6889089 A K ltle op n f i k h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem6889091 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : term1022 A K f i op) (h4 : term835 K k) (h5 : (@CARD K k) = n) (h6 : term1018 A K f i) (h7 : @IN K i k) : term1253 A K n ltle i op k f.
Proof. exact (EQ_MP (@lem6887399 A K ltle op f n i k h1 h5 h7) (@lem6889090 A K ltle op n f i k h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem6889092 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : @FINITE K k) (h2 : @monoidal A op) (h3 : term1022 A K f i op) (h4 : term835 K k) (h5 : (@CARD K k) = n) (h6 : term1018 A K f i) (h7 : @IN K i k) : term1252 A K n ltle i op k f.
Proof. exact (EQ_MP (@lem6887015 A K n ltle i op k f) (@lem6889091 A K ltle op n f i k h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem6889093 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term1022 A K f i op) (h5 : term835 K k) (h6 : (@CARD K k) = n) (h7 : term1018 A K f i) (h8 : @IN K i k) : (term1222 A K op ltle k i f) = (@iterate A K op k f).
Proof. exact (@lem6889092 A K ltle op n f i k h2 h3 h4 h5 h6 h7 h8 (@lem6886978 A K k i n ltle op f h1)). Qed.
Lemma lem6889094 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term1022 A K f i op) (h5 : term835 K k) (h6 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) (h7 : (@CARD K k) = n) (h8 : term1018 A K f i) (h9 : @IN K i k) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6886972 A K op ltle k i f h6) (@lem6889093 A K ltle op n f i k h1 h2 h3 h4 h5 h7 h8 h9)). Qed.
Lemma lem6889095 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) (h1 : term1225 A K op ltle k i f) : term1224 A K op ltle k i f.
Proof. exact (proj2 (@lem6886953 A K op ltle k i f h1)). Qed.
Lemma lem6889096 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) (h1 : term1225 A K op ltle k i f) : @IN K i k.
Proof. exact (proj1 (@lem6886953 A K op ltle k i f h1)). Qed.
Lemma lem6889097 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) (h1 : term1224 A K op ltle k i f) : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f).
Proof. exact (proj2 (@lem6886954 A K op ltle k i f h1)). Qed.
Lemma lem6889098 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (i : K) (f : K -> A) (h1 : term1224 A K op ltle k i f) : term1219 A K f i op.
Proof. exact (proj1 (@lem6886954 A K op ltle k i f h1)). Qed.
Lemma lem6889099 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term1022 A K f i op) (h5 : term835 K k) (h6 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) (h7 : (@CARD K k) = n) (h8 : term1018 A K f i) (h9 : @IN K i k) : ((term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h10 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f) => @lem6889094 A K op ltle n f i k h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6886956 A K op ltle k i f h6)). Qed.
Lemma lem6889100 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term1022 A K f i op) (h5 : term835 K k) (h6 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) (h7 : (@CARD K k) = n) (h8 : term1018 A K f i) (h9 : @IN K i k) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889099 A K op ltle n f i k h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem6886956 A K op ltle k i f h6)). Qed.
Lemma lem6889101 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (h1 : term1219 A K f i op) : term1022 A K f i op.
Proof. exact (proj2 (@lem6886957 A K f i op h1)). Qed.
Lemma lem6889102 {A K : Type'} (f : K -> A) (i : K) (op : type1400 A) (h1 : term1219 A K f i op) : term1018 A K f i.
Proof. exact (proj1 (@lem6886957 A K f i op h1)). Qed.
Lemma lem6889103 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term1022 A K f i op) (h5 : term835 K k) (h6 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) (h7 : (@CARD K k) = n) (h8 : term1018 A K f i) (h9 : @IN K i k) : (term1022 A K f i op) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h10 : term1022 A K f i op => @lem6889100 A K op ltle n f i k h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6886958 A K f i op h4)). Qed.
Lemma lem6889104 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term1022 A K f i op) (h5 : term835 K k) (h6 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) (h7 : (@CARD K k) = n) (h8 : term1018 A K f i) (h9 : @IN K i k) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889103 A K op ltle n f i k h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem6886958 A K f i op h4)). Qed.
Lemma lem6889105 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term1022 A K f i op) (h5 : term835 K k) (h6 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) (h7 : (@CARD K k) = n) (h8 : term1018 A K f i) (h9 : @IN K i k) : (term1018 A K f i) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h10 : term1018 A K f i => @lem6889104 A K op ltle n f i k h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6886959 A K f i h8)). Qed.
Lemma lem6889106 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term1022 A K f i op) (h5 : term835 K k) (h6 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) (h7 : (@CARD K k) = n) (h8 : term1018 A K f i) (h9 : @IN K i k) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889105 A K op ltle n f i k h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem6886959 A K f i h8)). Qed.
Lemma lem6889107 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : term1219 A K f i op) (h6 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) (h7 : (@CARD K k) = n) (h8 : term1018 A K f i) (h9 : @IN K i k) : (term1022 A K f i op) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h10 : term1022 A K f i op => @lem6889106 A K op ltle n f i k h1 h2 h3 h10 h4 h6 h7 h8 h9) (fun h10 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6889101 A K f i op h5)). Qed.
Lemma lem6889108 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (n : nat) (f : K -> A) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : term1219 A K f i op) (h6 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) (h7 : (@CARD K k) = n) (h8 : term1018 A K f i) (h9 : @IN K i k) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889107 A K op ltle n f i k h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem6889101 A K f i op h5)). Qed.
Lemma lem6889109 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (n : nat) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : term1219 A K f i op) (h6 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) (h7 : (@CARD K k) = n) (h8 : @IN K i k) : (term1018 A K f i) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h9 : term1018 A K f i => @lem6889108 A K op ltle n f i k h1 h2 h3 h4 h5 h6 h7 h9 h8) (fun h9 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6889102 A K f i op h5)). Qed.
Lemma lem6889110 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (n : nat) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : term1219 A K f i op) (h6 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) (h7 : (@CARD K k) = n) (h8 : @IN K i k) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889109 A K op ltle f n i k h1 h2 h3 h4 h5 h6 h7 h8) (@lem6889102 A K f i op h5)). Qed.
Lemma lem6889111 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (n : nat) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : term1224 A K op ltle k i f) (h6 : term1219 A K f i op) (h7 : (@CARD K k) = n) (h8 : @IN K i k) : ((term1011 A K op ltle k f) = (term1222 A K op ltle k i f)) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h9 : (term1011 A K op ltle k f) = (term1222 A K op ltle k i f) => @lem6889110 A K op ltle f n i k h1 h2 h3 h4 h6 h9 h7 h8) (fun h9 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6889097 A K op ltle k i f h5)). Qed.
Lemma lem6889112 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (n : nat) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : term1224 A K op ltle k i f) (h6 : term1219 A K f i op) (h7 : (@CARD K k) = n) (h8 : @IN K i k) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889111 A K ltle f op n i k h1 h2 h3 h4 h5 h6 h7 h8) (@lem6889097 A K op ltle k i f h5)). Qed.
Lemma lem6889113 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (n : nat) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : term1224 A K op ltle k i f) (h6 : (@CARD K k) = n) (h7 : @IN K i k) : (term1219 A K f i op) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h8 : term1219 A K f i op => @lem6889112 A K ltle f op n i k h1 h2 h3 h4 h5 h8 h6 h7) (fun h8 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6889098 A K op ltle k i f h5)). Qed.
Lemma lem6889114 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (n : nat) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : term1224 A K op ltle k i f) (h6 : (@CARD K k) = n) (h7 : @IN K i k) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889113 A K op ltle f n i k h1 h2 h3 h4 h5 h6 h7) (@lem6889098 A K op ltle k i f h5)). Qed.
Lemma lem6889115 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (n : nat) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : term1224 A K op ltle k i f) (h6 : (@CARD K k) = n) (h7 : @IN K i k) : (@IN K i k) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h8 : @IN K i k => @lem6889114 A K op ltle f n i k h1 h2 h3 h4 h5 h6 h7) (fun h8 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6886955 K i k h7)). Qed.
Lemma lem6889116 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (n : nat) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : term1224 A K op ltle k i f) (h6 : (@CARD K k) = n) (h7 : @IN K i k) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889115 A K op ltle f n i k h1 h2 h3 h4 h5 h6 h7) (@lem6886955 K i k h7)). Qed.
Lemma lem6889117 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (n : nat) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : term1225 A K op ltle k i f) (h6 : (@CARD K k) = n) (h7 : @IN K i k) : (term1224 A K op ltle k i f) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h8 : term1224 A K op ltle k i f => @lem6889116 A K op ltle f n i k h1 h2 h3 h4 h8 h6 h7) (fun h8 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6889095 A K op ltle k i f h5)). Qed.
Lemma lem6889118 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (n : nat) (i : K) (k : K -> Prop) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : term1225 A K op ltle k i f) (h6 : (@CARD K k) = n) (h7 : @IN K i k) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889117 A K op ltle f n i k h1 h2 h3 h4 h5 h6 h7) (@lem6889095 A K op ltle k i f h5)). Qed.
Lemma lem6889119 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (i : K) (f : K -> A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : term1225 A K op ltle k i f) (h6 : (@CARD K k) = n) : (@IN K i k) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h7 : @IN K i k => @lem6889118 A K op ltle f n i k h1 h2 h3 h4 h5 h6 h7) (fun h7 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6889096 A K op ltle k i f h5)). Qed.
Lemma lem6889120 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (i : K) (f : K -> A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : term1225 A K op ltle k i f) (h6 : (@CARD K k) = n) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889119 A K op ltle i f k n h1 h2 h3 h4 h5 h6) (@lem6889096 A K op ltle k i f h5)). Qed.
Lemma lem6889121 {A K : Type'} (i : K) (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : (@CARD K k) = n) : term1229 A K i ltle op k f.
Proof. exact (fun h0 : term1225 A K op ltle k i f => @lem6889120 A K op ltle i f k n h1 h2 h3 h4 h0 h5). Qed.
Lemma lem6889122 {A K : Type'} (i : K) (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : (@CARD K k) = n) : term1228 A K i ltle op k f.
Proof. exact (EQ_MP (@lem6886952 A K i ltle op k f) (@lem6889121 A K i ltle f op k n h1 h2 h3 h4 h5)). Qed.
Lemma lem6889123 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (i : K) (f : K -> A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : term1218 A K op ltle k i f) (h6 : (@CARD K k) = n) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (@lem6889122 A K i ltle f op k n h1 h2 h3 h4 h6 (@lem6886906 A K op ltle k i f h5)). Qed.
Lemma lem6889124 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : term1164 A K op ltle k f) (h3 : @FINITE K k) (h4 : @monoidal A op) (h5 : term835 K k) (h6 : (@CARD K k) = n) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (ex_elim (@lem6886905 A K op ltle k f h2) (fun i : K => fun h0 : term1464 A K op ltle k f i => @lem6889123 A K op ltle i f k n h1 h3 h4 h5 h0 h6)). Qed.
Lemma lem6889125 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : (@CARD K k) = n) : term1465 A K ltle op k f.
Proof. exact (fun h0 : term1164 A K op ltle k f => @lem6889124 A K ltle f op k n h1 h0 h2 h3 h4 h5). Qed.
Lemma lem6889126 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : (@CARD K k) = n) : term1466 A K ltle op k f.
Proof. exact (conj (@lem6886904 A K ltle k f op h3) (@lem6889125 A K ltle f op k n h1 h2 h3 h4 h5)). Qed.
Lemma lem6889127 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : (@CARD K k) = n) : term1197 A K ltle op k f.
Proof. exact (@lem6886443 A K ltle op k f (@lem6889126 A K ltle f op k n h1 h2 h3 h4 h5)). Qed.
Lemma lem6889128 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : (@CARD K k) = n) : term1196 A K ltle op k f.
Proof. exact (EQ_MP (@lem6886440 A K ltle op f k h2) (@lem6889127 A K ltle f op k n h1 h2 h3 h4 h5)). Qed.
Lemma lem6889129 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (f : K -> A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : term832 A K op ltle f) (h6 : (@CARD K k) = n) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (@lem6889128 A K ltle f op k n h1 h2 h3 h4 h6 (@lem6885341 A K k op ltle f h5)). Qed.
Lemma lem6889130 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : (@CARD K k) = n) : term1467 A K ltle op k f.
Proof. exact (fun h0 : term832 A K op ltle f => @lem6889129 A K op ltle f k n h1 h2 h3 h4 h0 h5). Qed.
Lemma lem6889132 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term835 K k) (h5 : (@CARD K k) = n) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (@lem6889130 A K ltle f op k n h1 h2 h3 h4 h5 (@lem6883605 A K op ltle f)). Qed.
Lemma lem6889133 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : (@CARD K k) = n) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (or_elim (@lem6883608 K k) (fun h0 : k = (@EMPTY K) => @lem6885157 A K ltle f op k h3 h0) (fun h0 : term835 K k => @lem6889132 A K ltle f op k n h1 h2 h3 h0 h4)). Qed.
Lemma lem6889134 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : (@CARD K k) = n) : ((@CARD K k) = n) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h5 : (@CARD K k) = n => @lem6889133 A K ltle f op k n h1 h2 h3 h4) (fun h5 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6884941 K k n h4)). Qed.
Lemma lem6889135 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : (@CARD K k) = n) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889134 A K ltle f op k n h1 h2 h3 h4) (@lem6884941 K k n h4)). Qed.
Lemma lem6889136 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : (@CARD K k) = n) : (@FINITE K k) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h5 : @FINITE K k => @lem6889135 A K ltle f op k n h1 h2 h3 h4) (fun h5 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6884937 K k h2)). Qed.
Lemma lem6889137 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : (@CARD K k) = n) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889136 A K ltle f op k n h1 h2 h3 h4) (@lem6884937 K k h2)). Qed.
Lemma lem6889138 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : (@CARD K k) = n) : (@monoidal A op) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h5 : @monoidal A op => @lem6889137 A K ltle f op k n h1 h2 h3 h4) (fun h5 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6884878 A op h3)). Qed.
Lemma lem6889139 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : (@CARD K k) = n) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889138 A K ltle f op k n h1 h2 h3 h4) (@lem6884878 A op h3)). Qed.
Lemma lem6889140 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term883 K k n) : (@CARD K k) = n.
Proof. exact (proj2 (@lem6884874 K k n h1)). Qed.
Lemma lem6889141 {K : Type'} (k : K -> Prop) (n : nat) (h1 : term883 K k n) : @FINITE K k.
Proof. exact (proj1 (@lem6884874 K k n h1)). Qed.
Lemma lem6889142 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : (@CARD K k) = n) : ((@CARD K k) = n) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h5 : (@CARD K k) = n => @lem6889139 A K ltle f op k n h1 h2 h3 h4) (fun h5 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6884875 K k n h4)). Qed.
Lemma lem6889143 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : (@CARD K k) = n) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889142 A K ltle f op k n h1 h2 h3 h4) (@lem6884875 K k n h4)). Qed.
Lemma lem6889144 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : (@CARD K k) = n) : (@FINITE K k) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h5 : @FINITE K k => @lem6889143 A K ltle f op k n h1 h2 h3 h4) (fun h5 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6884876 K k h2)). Qed.
Lemma lem6889145 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : (@CARD K k) = n) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889144 A K ltle f op k n h1 h2 h3 h4) (@lem6884876 K k h2)). Qed.
Lemma lem6889146 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term883 K k n) : ((@CARD K k) = n) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h5 : (@CARD K k) = n => @lem6889145 A K ltle f op k n h1 h2 h3 h5) (fun h5 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6889140 K k n h4)). Qed.
Lemma lem6889147 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @FINITE K k) (h3 : @monoidal A op) (h4 : term883 K k n) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889146 A K ltle f op k n h1 h2 h3 h4) (@lem6889140 K k n h4)). Qed.
Lemma lem6889148 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @monoidal A op) (h3 : term883 K k n) : (@FINITE K k) = ((term1011 A K op ltle k f) = (@iterate A K op k f)).
Proof. exact (prop_ext (fun h4 : @FINITE K k => @lem6889147 A K ltle f op k n h1 h4 h2 h3) (fun h4 : (term1011 A K op ltle k f) = (@iterate A K op k f) => @lem6889141 K k n h3)). Qed.
Lemma lem6889149 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (k : K -> Prop) (n : nat) (h1 : term1093 A K n ltle op f) (h2 : @monoidal A op) (h3 : term883 K k n) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6889148 A K ltle f op k n h1 h2 h3) (@lem6889141 K k n h3)). Qed.
Lemma lem6889150 {A K : Type'} (k : K -> Prop) (n : nat) (ltle : type1402 K) (f : K -> A) (op : type1400 A) (h1 : term1093 A K n ltle op f) (h2 : @monoidal A op) : term1066 A K n ltle op k f.
Proof. exact (fun h0 : term883 K k n => @lem6889149 A K ltle f op k n h1 h2 h0). Qed.
Lemma lem6889155 {A K : Type'} (n : nat) (ltle : type1402 K) (f : K -> A) (op : type1400 A) (h1 : term1093 A K n ltle op f) (h2 : @monoidal A op) : term1070 A K n ltle op f.
Proof. exact (fun k : K -> Prop => @lem6889150 A K k n ltle f op h1 h2). Qed.
Lemma lem6889156 {A K : Type'} (n : nat) (ltle : type1402 K) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : term1097 A K n ltle op f.
Proof. exact (fun h0 : term1093 A K n ltle op f => @lem6889155 A K n ltle f op h0 h1). Qed.
Lemma lem6889161 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : term1101 A K ltle op f.
Proof. exact (fun n : nat => @lem6889156 A K n ltle f op h1). Qed.
Lemma lem6889163 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : term1074 A K ltle op f.
Proof. exact (@lem6884872 A K ltle op f (@lem6889161 A K ltle f op h1)). Qed.
Lemma lem6889164 {A K : Type'} (ltle : type1402 K) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : term1083 A K ltle op f.
Proof. exact (@lem6884830 A K ltle op f (@lem6889163 A K ltle f op h1)). Qed.
Lemma lem6889165 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : term1468 A K ltle k f op.
Proof. exact (@lem6889164 A K ltle f op h1 (term1037 A K k f op)). Qed.
Lemma lem6889166 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (f : K -> A) : (term1468 A K ltle k f op) = (term1469 A K ltle k op f).
Proof. exact (eq_refl (term1468 A K ltle k f op)). Qed.
Lemma lem6889167 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : term1469 A K ltle k op f.
Proof. exact (EQ_MP (@lem6889166 A K ltle k op f) (@lem6889165 A K ltle k f op h1)). Qed.
Lemma lem6889168 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : (term1048 A K ltle k f op) = (term1057 A K k f op).
Proof. exact (@lem6884807 A K ltle k f op (@lem6889167 A K ltle k f op h1)). Qed.
Lemma lem6889169 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : (term1012 A K ltle k f op) = (term997 A K k f op).
Proof. exact (EQ_MP (@lem6884789 A K ltle k f op) (@lem6889168 A K ltle k f op h1)). Qed.
Lemma lem6889170 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (op : type1400 A) (h1 : @monoidal A op) : (term1011 A K op ltle k f) = (@iterate A K op k f).
Proof. exact (EQ_MP (@lem6884631 A K ltle op k f) (@lem6889169 A K ltle k f op h1)). Qed.
Lemma lem6889175 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (op : type1400 A) (h1 : @monoidal A op) : term1007 A K ltle op k.
Proof. exact (fun f : K -> A => @lem6889170 A K ltle k f op h1). Qed.
Lemma lem6889180 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (h1 : @monoidal A op) : term1010 A K ltle op.
Proof. exact (fun k : K -> Prop => @lem6889175 A K ltle k op h1). Qed.
Lemma lem6889181 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (h1 : @monoidal A op) : (term1003 A K op ltle) = (@iterate A K op).
Proof. exact (EQ_MP (@lem6884617 A K ltle op) (@lem6889180 A K ltle op h1)). Qed.
Lemma lem6889182 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (h1 : @monoidal A op) : (@monoidal A op) = ((term1003 A K op ltle) = (@iterate A K op)).
Proof. exact (prop_ext (fun h2 : @monoidal A op => @lem6889181 A K ltle op h1) (fun h2 : (term1003 A K op ltle) = (@iterate A K op) => @lem6884584 A op h1)). Qed.
Lemma lem6889183 {A K : Type'} (ltle : type1402 K) (op : type1400 A) (h1 : @monoidal A op) : (term1003 A K op ltle) = (@iterate A K op).
Proof. exact (EQ_MP (@lem6889182 A K ltle op h1) (@lem6884584 A op h1)). Qed.
Lemma lem6889184 {A K : Type'} (ltle : type1402 K) (op : type1400 A) : term1470 A K ltle op.
Proof. exact (fun h0 : @monoidal A op => @lem6889183 A K ltle op h0). Qed.
Lemma lem6889189 {A K : Type'} (op : type1400 A) : term1471 A K op.
Proof. exact (fun ltle : type1402 K => @lem6889184 A K ltle op). Qed.
Lemma lem6889194 {A K : Type'} : term1472 A K.
Proof. exact (fun op : type1400 A => @lem6889189 A K op). Qed.
