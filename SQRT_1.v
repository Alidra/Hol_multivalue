Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_1_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_POS_spec.
Require Import REAL_POW_2_spec.
Require Import SQRT_UNIQUE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338986_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
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
Require Import thm21385_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem1901742 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1901743 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1901744 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1901743 t1) (@lem1901742 t1)). Qed.
Lemma lem1901745 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1901744 t1 t2). Qed.
Lemma lem1901746 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1901747 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1901746 t1 t2) (@lem1901745 t1 t2)). Qed.
Lemma lem1901748 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1901747 t1 t2 t3). Qed.
Lemma lem1901749 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1901750 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1901749 t1 t2 t3) (@lem1901748 t1 t2 t3)). Qed.
Lemma lem1901751 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1901750 t1 t2 t3)). Qed.
Lemma lem1901753 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1901754 : (term8 = term9) = term10.
Proof. exact (@lem1901753 (term8 = term9)). Qed.
Lemma lem1901755 : term10 = (term8 = term9).
Proof. exact (SYM (@lem1901754)). Qed.
Lemma lem1901756 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1901759 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1901760 : term13.
Proof. exact (fun h0 : term12 => @lem1901759 h0). Qed.
Lemma lem1901761 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1901762 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1901763 (h1 : term12) (h2 : term13) : term12.
Proof. exact (@lem1901761 h2 (@lem1901762 h1)). Qed.
Lemma lem1901764 (h1 : term12) : term14.
Proof. exact (fun h0 : term13 => @lem1901763 h1 h0). Qed.
Lemma lem1901765 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1901766 (h1 : term12) (h2 : term13) : term12.
Proof. exact (@lem1901764 h1 (@lem1901765 h2)). Qed.
Lemma lem1901767 (h1 : term13) : term13.
Proof. exact (fun h0 : term12 => @lem1901766 h0 h1). Qed.
Lemma lem1901768 : term15.
Proof. exact (fun h0 : term13 => @lem1901767 h0). Qed.
Lemma lem1901771 : term13.
Proof. exact (@lem1901768 (@lem1901760)). Qed.
Lemma lem1901793 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1901794 : term16 = term17.
Proof. exact (@lem1901793 term18). Qed.
Lemma lem1901807 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1901808 : term20 = term21.
Proof. exact (MK_COMB (@lem1901807) (@lem1901794)). Qed.
Lemma lem1901811 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1901812 : term23 = term24.
Proof. exact (MK_COMB (@lem1901811) (@lem1901808)). Qed.
Lemma lem1901815 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem1901816 : term26 = term27.
Proof. exact (MK_COMB (@lem1901815) (@lem1901812)). Qed.
Lemma lem1901819 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1901826 : term12 = term29.
Proof. exact (MK_COMB (@lem1901819) (@lem1901816)). Qed.
Lemma lem1901835 (x : real) (y : real) : (term30 x y) = (term30 x y).
Proof. exact (eq_refl (term30 x y)). Qed.
Lemma lem1901836 (x : real) : (term31 x) = (term31 x).
Proof. exact (fun_ext (fun y : real => @lem1901835 x y)). Qed.
Lemma lem1901837 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1901838 (x : real) : (term32 x) = (term32 x).
Proof. exact (MK_COMB (@lem1901837) (@lem1901836 x)). Qed.
Lemma lem1901839 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1901838 x)). Qed.
Lemma lem1901840 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1901841 : term18 = term18.
Proof. exact (MK_COMB (@lem1901840) (@lem1901839)). Qed.
Lemma lem1901842 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1901843 : term17 = term17.
Proof. exact (MK_COMB (@lem1901842) (@lem1901841)). Qed.
Lemma lem1901844 (x : real) : ((term34 x) = (real_mul x x)) = ((term34 x) = (real_mul x x)).
Proof. exact (eq_refl ((term34 x) = (real_mul x x))). Qed.
Lemma lem1901845 : term35 = term35.
Proof. exact (fun_ext (fun x : real => @lem1901844 x)). Qed.
Lemma lem1901846 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1901847 : term36 = term36.
Proof. exact (MK_COMB (@lem1901846) (@lem1901845)). Qed.
Lemma lem1901848 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1901849 : term19 = term19.
Proof. exact (MK_COMB (@lem1901848) (@lem1901847)). Qed.
Lemma lem1901850 : term21 = term21.
Proof. exact (MK_COMB (@lem1901849) (@lem1901843)). Qed.
Lemma lem1901851 (x : real) : ((term37 x) = x) = ((term37 x) = x).
Proof. exact (eq_refl ((term37 x) = x)). Qed.
Lemma lem1901852 : term38 = term38.
Proof. exact (fun_ext (fun x : real => @lem1901851 x)). Qed.
Lemma lem1901853 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1901854 : term39 = term39.
Proof. exact (MK_COMB (@lem1901853) (@lem1901852)). Qed.
Lemma lem1901855 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1901856 : term22 = term22.
Proof. exact (MK_COMB (@lem1901855) (@lem1901854)). Qed.
Lemma lem1901857 : term24 = term24.
Proof. exact (MK_COMB (@lem1901856) (@lem1901850)). Qed.
Lemma lem1901858 (n : nat) : (term40 n) = (term40 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem1901859 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem1901858 n)). Qed.
Lemma lem1901860 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1901861 : term42 = term42.
Proof. exact (MK_COMB (@lem1901860) (@lem1901859)). Qed.
Lemma lem1901862 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1901863 : term25 = term25.
Proof. exact (MK_COMB (@lem1901862) (@lem1901861)). Qed.
Lemma lem1901864 : term27 = term27.
Proof. exact (MK_COMB (@lem1901863) (@lem1901857)). Qed.
Lemma lem1901869 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1901870 : term29 = term29.
Proof. exact (MK_COMB (@lem1901869) (@lem1901864)). Qed.
Lemma lem1901915 : term12 = term29.
Proof. exact (TRANS (@lem1901826) (@lem1901870)). Qed.
Lemma lem1901916 : term29 = term12.
Proof. exact (SYM (@lem1901915)). Qed.
Lemma lem1901918 (h1 : term42) : term42.
Proof. exact (h1). Qed.
Lemma lem1901919 (h1 : term39) : term39.
Proof. exact (h1). Qed.
Lemma lem1901920 (h1 : term36) : term36.
Proof. exact (h1). Qed.
Lemma lem1901921 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem1901927 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1901928 (n : nat) : (term40 n) = (term40 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem1901929 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem1901928 n)). Qed.
Lemma lem1901930 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1901939 : term42 = term42.
Proof. exact (MK_COMB (@lem1901930) (@lem1901929)). Qed.
Lemma lem1901940 (h1 : term42) : term42.
Proof. exact (EQ_MP (@lem1901939) (@lem1901918 h1)). Qed.
Lemma lem1901941 (x : real) : ((term37 x) = x) = ((term37 x) = x).
Proof. exact (eq_refl ((term37 x) = x)). Qed.
Lemma lem1901942 : term38 = term38.
Proof. exact (fun_ext (fun x : real => @lem1901941 x)). Qed.
Lemma lem1901943 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1901952 : term39 = term39.
Proof. exact (MK_COMB (@lem1901943) (@lem1901942)). Qed.
Lemma lem1901953 (h1 : term39) : term39.
Proof. exact (EQ_MP (@lem1901952) (@lem1901919 h1)). Qed.
Lemma lem1901954 (x : real) : ((term34 x) = (real_mul x x)) = ((term34 x) = (real_mul x x)).
Proof. exact (eq_refl ((term34 x) = (real_mul x x))). Qed.
Lemma lem1901955 : term35 = term35.
Proof. exact (fun_ext (fun x : real => @lem1901954 x)). Qed.
Lemma lem1901956 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1901965 : term36 = term36.
Proof. exact (MK_COMB (@lem1901956) (@lem1901955)). Qed.
Lemma lem1901966 (h1 : term36) : term36.
Proof. exact (EQ_MP (@lem1901965) (@lem1901920 h1)). Qed.
Lemma lem1901973 (y : real) (x : real) : (term43 y x) = (term44 y x).
Proof. exact (@lem17045 (term45 y) ((term34 y) = x)). Qed.
Lemma lem1901974 (x : real) (y : real) : ((sqrt x) = y) = ((sqrt x) = y).
Proof. exact (eq_refl ((sqrt x) = y)). Qed.
Lemma lem1901975 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1901976 (y : real) (x : real) : (term46 y x) = (term47 y x).
Proof. exact (MK_COMB (@lem1901975) (@lem1901973 y x)). Qed.
Lemma lem1901977 (x : real) (y : real) : (term48 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem1901976 y x) (@lem1901974 x y)). Qed.
Lemma lem1901978 (x : real) (y : real) : (term30 x y) = (term48 x y).
Proof. exact (@lem17265 (term50 y x) ((sqrt x) = y)). Qed.
Lemma lem1901979 (x : real) (y : real) : (term30 x y) = (term49 x y).
Proof. exact (TRANS (@lem1901978 x y) (@lem1901977 x y)). Qed.
Lemma lem1901980 (x : real) : (term31 x) = (term51 x).
Proof. exact (fun_ext (fun y : real => @lem1901979 x y)). Qed.
Lemma lem1901981 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1901982 (x : real) : (term32 x) = (term52 x).
Proof. exact (MK_COMB (@lem1901981) (@lem1901980 x)). Qed.
Lemma lem1901983 : term33 = term53.
Proof. exact (fun_ext (fun x : real => @lem1901982 x)). Qed.
Lemma lem1901984 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1902041 : term18 = term54.
Proof. exact (MK_COMB (@lem1901984) (@lem1901983)). Qed.
Lemma lem1902042 (h1 : term18) : term54.
Proof. exact (EQ_MP (@lem1902041) (@lem1901921 h1)). Qed.
Lemma lem1902064 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1902075 (n : nat) : (term40 n) = (term40 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem1902076 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem1902075 n)). Qed.
Lemma lem1902077 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1902078 : term42 = term42.
Proof. exact (MK_COMB (@lem1902077) (@lem1902076)). Qed.
Lemma lem1902079 (h1 : term42) : term42.
Proof. exact (EQ_MP (@lem1902078) (@lem1901940 h1)). Qed.
Lemma lem1902094 (x : real) : ((term37 x) = x) = ((term37 x) = x).
Proof. exact (eq_refl ((term37 x) = x)). Qed.
Lemma lem1902095 : term38 = term38.
Proof. exact (fun_ext (fun x : real => @lem1902094 x)). Qed.
Lemma lem1902096 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1902097 : term39 = term39.
Proof. exact (MK_COMB (@lem1902096) (@lem1902095)). Qed.
Lemma lem1902098 (h1 : term39) : term39.
Proof. exact (EQ_MP (@lem1902097) (@lem1901953 h1)). Qed.
Lemma lem1902117 (x : real) : ((term34 x) = (real_mul x x)) = ((term34 x) = (real_mul x x)).
Proof. exact (eq_refl ((term34 x) = (real_mul x x))). Qed.
Lemma lem1902118 : term35 = term35.
Proof. exact (fun_ext (fun x : real => @lem1902117 x)). Qed.
Lemma lem1902119 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1902120 : term36 = term36.
Proof. exact (MK_COMB (@lem1902119) (@lem1902118)). Qed.
Lemma lem1902121 (h1 : term36) : term36.
Proof. exact (EQ_MP (@lem1902120) (@lem1901966 h1)). Qed.
Lemma lem1902162 (x : real) (y : real) : (term49 x y) = (term49 x y).
Proof. exact (eq_refl (term49 x y)). Qed.
Lemma lem1902163 (x : real) : (term51 x) = (term51 x).
Proof. exact (fun_ext (fun y : real => @lem1902162 x y)). Qed.
Lemma lem1902164 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1902165 (x : real) : (term52 x) = (term52 x).
Proof. exact (MK_COMB (@lem1902164) (@lem1902163 x)). Qed.
Lemma lem1902166 : term53 = term53.
Proof. exact (fun_ext (fun x : real => @lem1902165 x)). Qed.
Lemma lem1902167 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1902168 : term54 = term54.
Proof. exact (MK_COMB (@lem1902167) (@lem1902166)). Qed.
Lemma lem1902169 (h1 : term18) : term54.
Proof. exact (EQ_MP (@lem1902168) (@lem1902042 h1)). Qed.
Lemma lem1902173 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1902175 (n : nat) : (term40 n) = (term40 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem1902176 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem1902175 n)). Qed.
Lemma lem1902177 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1902179 : term42 = term42.
Proof. exact (MK_COMB (@lem1902177) (@lem1902176)). Qed.
Lemma lem1902180 (h1 : term42) : term42.
Proof. exact (EQ_MP (@lem1902179) (@lem1902079 h1)). Qed.
Lemma lem1902182 (x : real) : ((term37 x) = x) = ((term37 x) = x).
Proof. exact (eq_refl ((term37 x) = x)). Qed.
Lemma lem1902183 : term38 = term38.
Proof. exact (fun_ext (fun x : real => @lem1902182 x)). Qed.
Lemma lem1902184 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1902186 : term39 = term39.
Proof. exact (MK_COMB (@lem1902184) (@lem1902183)). Qed.
Lemma lem1902187 (h1 : term39) : term39.
Proof. exact (EQ_MP (@lem1902186) (@lem1902098 h1)). Qed.
Lemma lem1902189 (x : real) : ((term34 x) = (real_mul x x)) = ((term34 x) = (real_mul x x)).
Proof. exact (eq_refl ((term34 x) = (real_mul x x))). Qed.
Lemma lem1902190 : term35 = term35.
Proof. exact (fun_ext (fun x : real => @lem1902189 x)). Qed.
Lemma lem1902191 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1902193 : term36 = term36.
Proof. exact (MK_COMB (@lem1902191) (@lem1902190)). Qed.
Lemma lem1902194 (h1 : term36) : term36.
Proof. exact (EQ_MP (@lem1902193) (@lem1902121 h1)). Qed.
Lemma lem1902208 (x : real) (y : real) : (term49 x y) = (term49 x y).
Proof. exact (eq_refl (term49 x y)). Qed.
Lemma lem1902209 (x : real) : (term51 x) = (term51 x).
Proof. exact (fun_ext (fun y : real => @lem1902208 x y)). Qed.
Lemma lem1902210 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1902211 (x : real) : (term52 x) = (term52 x).
Proof. exact (MK_COMB (@lem1902210) (@lem1902209 x)). Qed.
Lemma lem1902212 : term53 = term53.
Proof. exact (fun_ext (fun x : real => @lem1902211 x)). Qed.
Lemma lem1902213 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1902215 : term54 = term54.
Proof. exact (MK_COMB (@lem1902213) (@lem1902212)). Qed.
Lemma lem1902216 (h1 : term18) : term54.
Proof. exact (EQ_MP (@lem1902215) (@lem1902169 h1)). Qed.
Lemma lem1902217 (_27076 : nat) (h1 : term42) : term55 _27076.
Proof. exact (@lem1902180 h1 _27076). Qed.
Lemma lem1902218 (_27076 : nat) : (term55 _27076) = (term40 _27076).
Proof. exact (eq_refl (term55 _27076)). Qed.
Lemma lem1902220 (_27077 : real) (h1 : term39) : term56 _27077.
Proof. exact (@lem1902187 h1 _27077). Qed.
Lemma lem1902221 (_27077 : real) : (term56 _27077) = ((term37 _27077) = _27077).
Proof. exact (eq_refl (term56 _27077)). Qed.
Lemma lem1902223 (_27078 : real) (h1 : term36) : term57 _27078.
Proof. exact (@lem1902194 h1 _27078). Qed.
Lemma lem1902224 (_27078 : real) : (term57 _27078) = ((term34 _27078) = (real_mul _27078 _27078)).
Proof. exact (eq_refl (term57 _27078)). Qed.
Lemma lem1902226 (_27079 : real) (h1 : term18) : term58 _27079.
Proof. exact (@lem1902216 h1 _27079). Qed.
Lemma lem1902227 (_27079 : real) : (term58 _27079) = (term52 _27079).
Proof. exact (eq_refl (term58 _27079)). Qed.
Lemma lem1902228 (_27079 : real) (h1 : term18) : term52 _27079.
Proof. exact (EQ_MP (@lem1902227 _27079) (@lem1902226 _27079 h1)). Qed.
Lemma lem1902229 (_27079 : real) (_27080 : real) (h1 : term18) : term59 _27079 _27080.
Proof. exact (@lem1902228 _27079 h1 _27080). Qed.
Lemma lem1902230 (_27079 : real) (_27080 : real) : (term59 _27079 _27080) = (term49 _27079 _27080).
Proof. exact (eq_refl (term59 _27079 _27080)). Qed.
Lemma lem1902231 (_27079 : real) (_27080 : real) (h1 : term18) : term49 _27079 _27080.
Proof. exact (EQ_MP (@lem1902230 _27079 _27080) (@lem1902229 _27079 _27080 h1)). Qed.
Lemma lem1902233 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1902250 (_27079 : real) (_27080 : real) : (term49 _27079 _27080) = (term60 _27079 _27080).
Proof. exact (@lem1901751 (term61 _27080) (term62 _27080 _27079) ((sqrt _27079) = _27080)). Qed.
Lemma lem1902251 (_27079 : real) (_27080 : real) (h1 : term18) : term60 _27079 _27080.
Proof. exact (EQ_MP (@lem1902250 _27079 _27080) (@lem1902231 _27079 _27080 h1)). Qed.
Lemma lem1902309 : sqrt = sqrt.
Proof. exact (eq_refl sqrt). Qed.
Lemma lem1902310 (_27095 : real) (_27096 : real) (h1 : _27095 = _27096) : _27095 = _27096.
Proof. exact (h1). Qed.
Lemma lem1902311 (_27095 : real) (_27096 : real) (h1 : _27095 = _27096) : (sqrt _27095) = (sqrt _27096).
Proof. exact (MK_COMB (@lem1902309) (@lem1902310 _27095 _27096 h1)). Qed.
Lemma lem1902312 (_27095 : real) (_27096 : real) : term63 _27095 _27096.
Proof. exact (fun h0 : _27095 = _27096 => @lem1902311 _27095 _27096 h0). Qed.
Lemma lem1902314 (a : Prop) (b : Prop) : (a -> b) = (term64 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1902315 (_27095 : real) (_27096 : real) : (term63 _27095 _27096) = (term65 _27095 _27096).
Proof. exact (@lem1902314 (_27095 = _27096) ((sqrt _27095) = (sqrt _27096))). Qed.
Lemma lem1902316 (_27095 : real) (_27096 : real) : term65 _27095 _27096.
Proof. exact (EQ_MP (@lem1902315 _27095 _27096) (@lem1902312 _27095 _27096)). Qed.
Lemma lem1902342 (x : real) (y : real) (z : real) : term66 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1902346 (_27077 : real) (h1 : term39) : (term37 _27077) = _27077.
Proof. exact (EQ_MP (@lem1902221 _27077) (@lem1902220 _27077 h1)). Qed.
Lemma lem1902347 (h1 : term39) : term67 = term9.
Proof. exact (@lem1902346 term9 h1). Qed.
Lemma lem1902348 (h1 : term39) : term68.
Proof. exact (fun h0 : term69 => @lem1902347 h1). Qed.
Lemma lem1902350 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1902351 : term68 = (term67 = term9).
Proof. exact (@lem1902350 (term67 = term9)). Qed.
Lemma lem1902352 (h1 : term39) : term67 = term9.
Proof. exact (EQ_MP (@lem1902351) (@lem1902348 h1)). Qed.
Lemma lem1902358 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1902359 (_27095 : real) (_27096 : real) : (term65 _27095 _27096) = (term71 _27095 _27096).
Proof. exact (@lem1902358 ((sqrt _27095) = (sqrt _27096)) (term72 _27095 _27096)). Qed.
Lemma lem1902369 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1902370 (_27095 : real) (_27096 : real) : (term73 _27095 _27096) = (term74 _27095 _27096).
Proof. exact (MK_COMB (@lem1902369) (@lem1902359 _27095 _27096)). Qed.
Lemma lem1902380 (_27095 : real) (_27096 : real) : (term71 _27095 _27096) = (term71 _27095 _27096).
Proof. exact (eq_refl (term71 _27095 _27096)). Qed.
Lemma lem1902381 (_27095 : real) (_27096 : real) : ((term65 _27095 _27096) = (term71 _27095 _27096)) = ((term71 _27095 _27096) = (term71 _27095 _27096)).
Proof. exact (MK_COMB (@lem1902370 _27095 _27096) (@lem1902380 _27095 _27096)). Qed.
Lemma lem1902383 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1902384 (x : Prop) : (x = x) = True.
Proof. exact (@lem1902383 Prop x). Qed.
Lemma lem1902385 (_27095 : real) (_27096 : real) : ((term71 _27095 _27096) = (term71 _27095 _27096)) = True.
Proof. exact (@lem1902384 (term71 _27095 _27096)). Qed.
Lemma lem1902386 (_27095 : real) (_27096 : real) : ((term65 _27095 _27096) = (term71 _27095 _27096)) = True.
Proof. exact (TRANS (@lem1902381 _27095 _27096) (@lem1902385 _27095 _27096)). Qed.
Lemma lem1902387 (_27095 : real) (_27096 : real) : True = ((term65 _27095 _27096) = (term71 _27095 _27096)).
Proof. exact (SYM (@lem1902386 _27095 _27096)). Qed.
Lemma lem1902388 (_27095 : real) (_27096 : real) : (term65 _27095 _27096) = (term71 _27095 _27096).
Proof. exact (EQ_MP (@lem1902387 _27095 _27096) (@lem0)). Qed.
Lemma lem1902389 (_27095 : real) (_27096 : real) : term71 _27095 _27096.
Proof. exact (EQ_MP (@lem1902388 _27095 _27096) (@lem1902316 _27095 _27096)). Qed.
Lemma lem1902391 (b : Prop) (a : Prop) : (a \/ b) = (term75 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1902392 (_27095 : real) (_27096 : real) : (term71 _27095 _27096) = (term76 _27095 _27096).
Proof. exact (@lem1902391 (term72 _27095 _27096) ((sqrt _27095) = (sqrt _27096))). Qed.
Lemma lem1902394 (a : Prop) : (term77 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1902395 (_27095 : real) (_27096 : real) : (term78 _27095 _27096) = (_27095 = _27096).
Proof. exact (@lem1902394 (_27095 = _27096)). Qed.
Lemma lem1902396 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1902397 (_27095 : real) (_27096 : real) : (term79 _27095 _27096) = (term80 _27095 _27096).
Proof. exact (MK_COMB (@lem1902396) (@lem1902395 _27095 _27096)). Qed.
Lemma lem1902398 (_27095 : real) (_27096 : real) : ((sqrt _27095) = (sqrt _27096)) = ((sqrt _27095) = (sqrt _27096)).
Proof. exact (eq_refl ((sqrt _27095) = (sqrt _27096))). Qed.
Lemma lem1902399 (_27095 : real) (_27096 : real) : (term76 _27095 _27096) = (term63 _27095 _27096).
Proof. exact (MK_COMB (@lem1902397 _27095 _27096) (@lem1902398 _27095 _27096)). Qed.
Lemma lem1902400 (_27095 : real) (_27096 : real) : (term71 _27095 _27096) = (term63 _27095 _27096).
Proof. exact (TRANS (@lem1902392 _27095 _27096) (@lem1902399 _27095 _27096)). Qed.
Lemma lem1902403 (_27095 : real) (_27096 : real) : term63 _27095 _27096.
Proof. exact (EQ_MP (@lem1902400 _27095 _27096) (@lem1902389 _27095 _27096)). Qed.
Lemma lem1902404 : term81.
Proof. exact (@lem1902403 term67 term9). Qed.
Lemma lem1902407 (h1 : term39) : term82 = term8.
Proof. exact (@lem1902404 (@lem1902352 h1)). Qed.
Lemma lem1902408 (h1 : term39) : term83.
Proof. exact (fun h0 : term84 => @lem1902407 h1). Qed.
Lemma lem1902410 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1902411 : term83 = (term82 = term8).
Proof. exact (@lem1902410 (term82 = term8)). Qed.
Lemma lem1902412 (h1 : term39) : term82 = term8.
Proof. exact (EQ_MP (@lem1902411) (@lem1902408 h1)). Qed.
Lemma lem1902414 (_27076 : nat) (h1 : term42) : term40 _27076.
Proof. exact (EQ_MP (@lem1902218 _27076) (@lem1902217 _27076 h1)). Qed.
Lemma lem1902415 (h1 : term42) : term85.
Proof. exact (@lem1902414 term86 h1). Qed.
Lemma lem1902416 (h1 : term42) : term87.
Proof. exact (fun h0 : term88 => @lem1902415 h1). Qed.
Lemma lem1902418 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1902419 : term87 = term85.
Proof. exact (@lem1902418 term85). Qed.
Lemma lem1902420 (h1 : term42) : term85.
Proof. exact (EQ_MP (@lem1902419) (@lem1902416 h1)). Qed.
Lemma lem1902422 (_27078 : real) (h1 : term36) : (term34 _27078) = (real_mul _27078 _27078).
Proof. exact (EQ_MP (@lem1902224 _27078) (@lem1902223 _27078 h1)). Qed.
Lemma lem1902423 (h1 : term36) : term89 = term67.
Proof. exact (@lem1902422 term9 h1). Qed.
Lemma lem1902424 (h1 : term36) : term90.
Proof. exact (fun h0 : term91 => @lem1902423 h1). Qed.
Lemma lem1902426 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1902427 : term90 = (term89 = term67).
Proof. exact (@lem1902426 (term89 = term67)). Qed.
Lemma lem1902428 (h1 : term36) : term89 = term67.
Proof. exact (EQ_MP (@lem1902427) (@lem1902424 h1)). Qed.
Lemma lem1902434 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1902435 (_27079 : real) (_27080 : real) : (term60 _27079 _27080) = (term92 _27079 _27080).
Proof. exact (@lem1902434 (term62 _27080 _27079) (term61 _27080) ((sqrt _27079) = _27080)). Qed.
Lemma lem1902451 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1902452 (_27079 : real) (_27080 : real) : (term93 _27079 _27080) = (term94 _27079 _27080).
Proof. exact (@lem1902451 ((sqrt _27079) = _27080) (term61 _27080)). Qed.
Lemma lem1902460 (_27080 : real) (_27079 : real) : (term95 _27080 _27079) = (term95 _27080 _27079).
Proof. exact (eq_refl (term95 _27080 _27079)). Qed.
Lemma lem1902461 (_27079 : real) (_27080 : real) : (term92 _27079 _27080) = (term96 _27079 _27080).
Proof. exact (MK_COMB (@lem1902460 _27080 _27079) (@lem1902452 _27079 _27080)). Qed.
Lemma lem1902465 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1902466 (_27079 : real) (_27080 : real) : (term96 _27079 _27080) = (term97 _27079 _27080).
Proof. exact (@lem1902465 ((sqrt _27079) = _27080) (term62 _27080 _27079) (term61 _27080)). Qed.
Lemma lem1902486 (_27079 : real) (_27080 : real) : (term92 _27079 _27080) = (term97 _27079 _27080).
Proof. exact (TRANS (@lem1902461 _27079 _27080) (@lem1902466 _27079 _27080)). Qed.
Lemma lem1902487 (_27079 : real) (_27080 : real) : (term60 _27079 _27080) = (term97 _27079 _27080).
Proof. exact (TRANS (@lem1902435 _27079 _27080) (@lem1902486 _27079 _27080)). Qed.
Lemma lem1902488 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1902489 (_27079 : real) (_27080 : real) : (term98 _27079 _27080) = (term99 _27079 _27080).
Proof. exact (MK_COMB (@lem1902488) (@lem1902487 _27079 _27080)). Qed.
Lemma lem1902505 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1902506 (_27079 : real) (_27080 : real) : (term44 _27080 _27079) = (term100 _27079 _27080).
Proof. exact (@lem1902505 (term62 _27080 _27079) (term61 _27080)). Qed.
Lemma lem1902514 (_27079 : real) (_27080 : real) : (term101 _27079 _27080) = (term101 _27079 _27080).
Proof. exact (eq_refl (term101 _27079 _27080)). Qed.
Lemma lem1902515 (_27079 : real) (_27080 : real) : (term102 _27080 _27079) = (term97 _27079 _27080).
Proof. exact (MK_COMB (@lem1902514 _27079 _27080) (@lem1902506 _27079 _27080)). Qed.
Lemma lem1902526 (_27079 : real) (_27080 : real) : ((term60 _27079 _27080) = (term102 _27080 _27079)) = ((term97 _27079 _27080) = (term97 _27079 _27080)).
Proof. exact (MK_COMB (@lem1902489 _27079 _27080) (@lem1902515 _27079 _27080)). Qed.
Lemma lem1902528 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1902529 (x : Prop) : (x = x) = True.
Proof. exact (@lem1902528 Prop x). Qed.
Lemma lem1902530 (_27079 : real) (_27080 : real) : ((term97 _27079 _27080) = (term97 _27079 _27080)) = True.
Proof. exact (@lem1902529 (term97 _27079 _27080)). Qed.
Lemma lem1902531 (_27080 : real) (_27079 : real) : ((term60 _27079 _27080) = (term102 _27080 _27079)) = True.
Proof. exact (TRANS (@lem1902526 _27079 _27080) (@lem1902530 _27079 _27080)). Qed.
Lemma lem1902532 (_27080 : real) (_27079 : real) : True = ((term60 _27079 _27080) = (term102 _27080 _27079)).
Proof. exact (SYM (@lem1902531 _27080 _27079)). Qed.
Lemma lem1902533 (_27080 : real) (_27079 : real) : (term60 _27079 _27080) = (term102 _27080 _27079).
Proof. exact (EQ_MP (@lem1902532 _27080 _27079) (@lem0)). Qed.
Lemma lem1902534 (_27080 : real) (_27079 : real) (h1 : term18) : term102 _27080 _27079.
Proof. exact (EQ_MP (@lem1902533 _27080 _27079) (@lem1902251 _27079 _27080 h1)). Qed.
Lemma lem1902536 (b : Prop) (a : Prop) : (a \/ b) = (term75 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1902537 (_27079 : real) (_27080 : real) : (term102 _27080 _27079) = (term103 _27079 _27080).
Proof. exact (@lem1902536 (term44 _27080 _27079) ((sqrt _27079) = _27080)). Qed.
Lemma lem1902539 (a : Prop) (b : Prop) : (term104 a b) = (term105 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1902540 (_27080 : real) (_27079 : real) : (term106 _27080 _27079) = (term107 _27080 _27079).
Proof. exact (@lem1902539 (term61 _27080) (term62 _27080 _27079)). Qed.
Lemma lem1902542 (a : Prop) : (term77 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1902543 (_27080 : real) : (term108 _27080) = (term45 _27080).
Proof. exact (@lem1902542 (term45 _27080)). Qed.
Lemma lem1902544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1902545 (_27080 : real) : (term109 _27080) = (term110 _27080).
Proof. exact (MK_COMB (@lem1902544) (@lem1902543 _27080)). Qed.
Lemma lem1902547 (a : Prop) : (term77 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1902548 (_27080 : real) (_27079 : real) : (term111 _27080 _27079) = ((term34 _27080) = _27079).
Proof. exact (@lem1902547 ((term34 _27080) = _27079)). Qed.
Lemma lem1902549 (_27080 : real) (_27079 : real) : (term107 _27080 _27079) = (term50 _27080 _27079).
Proof. exact (MK_COMB (@lem1902545 _27080) (@lem1902548 _27080 _27079)). Qed.
Lemma lem1902550 (_27080 : real) (_27079 : real) : (term106 _27080 _27079) = (term50 _27080 _27079).
Proof. exact (TRANS (@lem1902540 _27080 _27079) (@lem1902549 _27080 _27079)). Qed.
Lemma lem1902551 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1902552 (_27080 : real) (_27079 : real) : (term112 _27080 _27079) = (term113 _27080 _27079).
Proof. exact (MK_COMB (@lem1902551) (@lem1902550 _27080 _27079)). Qed.
Lemma lem1902553 (_27079 : real) (_27080 : real) : ((sqrt _27079) = _27080) = ((sqrt _27079) = _27080).
Proof. exact (eq_refl ((sqrt _27079) = _27080)). Qed.
Lemma lem1902554 (_27079 : real) (_27080 : real) : (term103 _27079 _27080) = (term30 _27079 _27080).
Proof. exact (MK_COMB (@lem1902552 _27080 _27079) (@lem1902553 _27079 _27080)). Qed.
Lemma lem1902555 (_27079 : real) (_27080 : real) : (term102 _27080 _27079) = (term30 _27079 _27080).
Proof. exact (TRANS (@lem1902537 _27079 _27080) (@lem1902554 _27079 _27080)). Qed.
Lemma lem1902557 (h1 : term42) (h2 : term36) : term114.
Proof. exact (conj (@lem1902420 h1) (@lem1902428 h2)). Qed.
Lemma lem1902559 (_27079 : real) (_27080 : real) (h1 : term18) : term30 _27079 _27080.
Proof. exact (EQ_MP (@lem1902555 _27079 _27080) (@lem1902534 _27080 _27079 h1)). Qed.
Lemma lem1902560 (h1 : term18) : term115.
Proof. exact (@lem1902559 term67 term9 h1). Qed.
Lemma lem1902563 (h1 : term42) (h2 : term18) (h3 : term36) : term82 = term9.
Proof. exact (@lem1902560 h2 (@lem1902557 h1 h3)). Qed.
Lemma lem1902564 (h1 : term42) (h2 : term18) (h3 : term36) : term116.
Proof. exact (fun h0 : term117 => @lem1902563 h1 h2 h3). Qed.
Lemma lem1902566 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1902567 : term116 = (term82 = term9).
Proof. exact (@lem1902566 (term82 = term9)). Qed.
Lemma lem1902568 (h1 : term42) (h2 : term18) (h3 : term36) : term82 = term9.
Proof. exact (EQ_MP (@lem1902567) (@lem1902564 h1 h2 h3)). Qed.
Lemma lem1902586 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1902587 (y : real) (x : real) (z : real) : (term118 x y z) = (term119 y x z).
Proof. exact (@lem1902586 (y = z) (term72 x z)). Qed.
Lemma lem1902597 (x : real) (y : real) : (term120 x y) = (term120 x y).
Proof. exact (eq_refl (term120 x y)). Qed.
Lemma lem1902598 (y : real) (x : real) (z : real) : (term66 x y z) = (term121 y x z).
Proof. exact (MK_COMB (@lem1902597 x y) (@lem1902587 y x z)). Qed.
Lemma lem1902602 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1902603 (y : real) (x : real) (z : real) : (term121 y x z) = (term122 y x z).
Proof. exact (@lem1902602 (y = z) (term72 x y) (term72 x z)). Qed.
Lemma lem1902625 (y : real) (x : real) (z : real) : (term66 x y z) = (term122 y x z).
Proof. exact (TRANS (@lem1902598 y x z) (@lem1902603 y x z)). Qed.
Lemma lem1902626 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1902627 (y : real) (x : real) (z : real) : (term123 x y z) = (term124 y x z).
Proof. exact (MK_COMB (@lem1902626) (@lem1902625 y x z)). Qed.
Lemma lem1902649 (y : real) (x : real) (z : real) : (term122 y x z) = (term122 y x z).
Proof. exact (eq_refl (term122 y x z)). Qed.
Lemma lem1902650 (y : real) (x : real) (z : real) : ((term66 x y z) = (term122 y x z)) = ((term122 y x z) = (term122 y x z)).
Proof. exact (MK_COMB (@lem1902627 y x z) (@lem1902649 y x z)). Qed.
Lemma lem1902652 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1902653 (x : Prop) : (x = x) = True.
Proof. exact (@lem1902652 Prop x). Qed.
Lemma lem1902654 (y : real) (x : real) (z : real) : ((term122 y x z) = (term122 y x z)) = True.
Proof. exact (@lem1902653 (term122 y x z)). Qed.
Lemma lem1902655 (y : real) (x : real) (z : real) : ((term66 x y z) = (term122 y x z)) = True.
Proof. exact (TRANS (@lem1902650 y x z) (@lem1902654 y x z)). Qed.
Lemma lem1902656 (y : real) (x : real) (z : real) : True = ((term66 x y z) = (term122 y x z)).
Proof. exact (SYM (@lem1902655 y x z)). Qed.
Lemma lem1902657 (y : real) (x : real) (z : real) : (term66 x y z) = (term122 y x z).
Proof. exact (EQ_MP (@lem1902656 y x z) (@lem0)). Qed.
Lemma lem1902658 (y : real) (x : real) (z : real) : term122 y x z.
Proof. exact (EQ_MP (@lem1902657 y x z) (@lem1902342 x y z)). Qed.
Lemma lem1902660 (b : Prop) (a : Prop) : (a \/ b) = (term75 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1902661 (x : real) (y : real) (z : real) : (term122 y x z) = (term125 x y z).
Proof. exact (@lem1902660 (term126 y x z) (y = z)). Qed.
Lemma lem1902663 (a : Prop) (b : Prop) : (term104 a b) = (term105 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1902664 (y : real) (x : real) (z : real) : (term127 y x z) = (term128 y x z).
Proof. exact (@lem1902663 (term72 x y) (term72 x z)). Qed.
Lemma lem1902666 (a : Prop) : (term77 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1902667 (x : real) (y : real) : (term78 x y) = (x = y).
Proof. exact (@lem1902666 (x = y)). Qed.
Lemma lem1902668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1902669 (x : real) (y : real) : (term129 x y) = (term130 x y).
Proof. exact (MK_COMB (@lem1902668) (@lem1902667 x y)). Qed.
Lemma lem1902671 (a : Prop) : (term77 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1902672 (x : real) (z : real) : (term78 x z) = (x = z).
Proof. exact (@lem1902671 (x = z)). Qed.
Lemma lem1902673 (y : real) (x : real) (z : real) : (term128 y x z) = (term131 y x z).
Proof. exact (MK_COMB (@lem1902669 x y) (@lem1902672 x z)). Qed.
Lemma lem1902674 (y : real) (x : real) (z : real) : (term127 y x z) = (term131 y x z).
Proof. exact (TRANS (@lem1902664 y x z) (@lem1902673 y x z)). Qed.
Lemma lem1902675 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1902676 (y : real) (x : real) (z : real) : (term132 y x z) = (term133 y x z).
Proof. exact (MK_COMB (@lem1902675) (@lem1902674 y x z)). Qed.
Lemma lem1902677 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1902678 (x : real) (y : real) (z : real) : (term125 x y z) = (term134 x y z).
Proof. exact (MK_COMB (@lem1902676 y x z) (@lem1902677 y z)). Qed.
Lemma lem1902679 (x : real) (y : real) (z : real) : (term122 y x z) = (term134 x y z).
Proof. exact (TRANS (@lem1902661 x y z) (@lem1902678 x y z)). Qed.
Lemma lem1902681 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) : term135.
Proof. exact (conj (@lem1902412 h3) (@lem1902568 h1 h2 h4)). Qed.
Lemma lem1902683 (x : real) (y : real) (z : real) : term134 x y z.
Proof. exact (EQ_MP (@lem1902679 x y z) (@lem1902658 y x z)). Qed.
Lemma lem1902684 : term136.
Proof. exact (@lem1902683 term82 term8 term9). Qed.
Lemma lem1902687 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) : term8 = term9.
Proof. exact (@lem1902684 (@lem1902681 h1 h2 h3 h4)). Qed.
Lemma lem1902688 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) : term137.
Proof. exact (fun h0 : term11 => @lem1902687 h1 h2 h3 h4). Qed.
Lemma lem1902690 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1902691 : term137 = (term8 = term9).
Proof. exact (@lem1902690 (term8 = term9)). Qed.
Lemma lem1902692 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) : term8 = term9.
Proof. exact (EQ_MP (@lem1902691) (@lem1902688 h1 h2 h3 h4)). Qed.
Lemma lem1902695 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1902697 : term11 = term138.
Proof. exact (@lem1902695 (term8 = term9)). Qed.
Lemma lem1902700 (h1 : term11) : term138.
Proof. exact (EQ_MP (@lem1902697) (@lem1902233 h1)). Qed.
Lemma lem1902703 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (@lem1902700 h5 (@lem1902692 h1 h2 h3 h4)). Qed.
Lemma lem1902704 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term139.
Proof. exact (fun h0 : ~ False => @lem1902703 h1 h2 h3 h4 h5). Qed.
Lemma lem1902706 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1902707 : term139 = False.
Proof. exact (@lem1902706 False). Qed.
Lemma lem1902708 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1902707) (@lem1902704 h1 h2 h3 h4 h5)). Qed.
Lemma lem1902709 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term11 = False.
Proof. exact (prop_ext (fun h6 : term11 => @lem1902708 h1 h2 h3 h4 h5) (fun h6 : False => @lem1902233 h5)). Qed.
Lemma lem1902710 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1902709 h1 h2 h3 h4 h5) (@lem1902233 h5)). Qed.
Lemma lem1902711 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term11 = False.
Proof. exact (prop_ext (fun h6 : term11 => @lem1902710 h1 h2 h3 h4 h5) (fun h6 : False => @lem1902173 h5)). Qed.
Lemma lem1902712 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1902711 h1 h2 h3 h4 h5) (@lem1902173 h5)). Qed.
Lemma lem1902713 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term36 = False.
Proof. exact (prop_ext (fun h6 : term36 => @lem1902712 h1 h2 h3 h4 h5) (fun h6 : False => @lem1902194 h4)). Qed.
Lemma lem1902714 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1902713 h1 h2 h3 h4 h5) (@lem1902194 h4)). Qed.
Lemma lem1902715 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term39 = False.
Proof. exact (prop_ext (fun h6 : term39 => @lem1902714 h1 h2 h3 h4 h5) (fun h6 : False => @lem1902187 h3)). Qed.
Lemma lem1902716 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1902715 h1 h2 h3 h4 h5) (@lem1902187 h3)). Qed.
Lemma lem1902717 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term42 = False.
Proof. exact (prop_ext (fun h6 : term42 => @lem1902716 h1 h2 h3 h4 h5) (fun h6 : False => @lem1902180 h1)). Qed.
Lemma lem1902718 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1902717 h1 h2 h3 h4 h5) (@lem1902180 h1)). Qed.
Lemma lem1902719 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term11 = False.
Proof. exact (prop_ext (fun h6 : term11 => @lem1902718 h1 h2 h3 h4 h5) (fun h6 : False => @lem1902173 h5)). Qed.
Lemma lem1902720 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1902719 h1 h2 h3 h4 h5) (@lem1902173 h5)). Qed.
Lemma lem1902721 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term36 = False.
Proof. exact (prop_ext (fun h6 : term36 => @lem1902720 h1 h2 h3 h4 h5) (fun h6 : False => @lem1902121 h4)). Qed.
Lemma lem1902722 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1902721 h1 h2 h3 h4 h5) (@lem1902121 h4)). Qed.
Lemma lem1902723 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term39 = False.
Proof. exact (prop_ext (fun h6 : term39 => @lem1902722 h1 h2 h3 h4 h5) (fun h6 : False => @lem1902098 h3)). Qed.
Lemma lem1902724 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1902723 h1 h2 h3 h4 h5) (@lem1902098 h3)). Qed.
Lemma lem1902725 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term42 = False.
Proof. exact (prop_ext (fun h6 : term42 => @lem1902724 h1 h2 h3 h4 h5) (fun h6 : False => @lem1902079 h1)). Qed.
Lemma lem1902726 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1902725 h1 h2 h3 h4 h5) (@lem1902079 h1)). Qed.
Lemma lem1902727 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term11 = False.
Proof. exact (prop_ext (fun h6 : term11 => @lem1902726 h1 h2 h3 h4 h5) (fun h6 : False => @lem1902064 h5)). Qed.
Lemma lem1902728 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1902727 h1 h2 h3 h4 h5) (@lem1902064 h5)). Qed.
Lemma lem1902729 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term36 = False.
Proof. exact (prop_ext (fun h6 : term36 => @lem1902728 h1 h2 h3 h4 h5) (fun h6 : False => @lem1901966 h4)). Qed.
Lemma lem1902730 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1902729 h1 h2 h3 h4 h5) (@lem1901966 h4)). Qed.
Lemma lem1902731 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term39 = False.
Proof. exact (prop_ext (fun h6 : term39 => @lem1902730 h1 h2 h3 h4 h5) (fun h6 : False => @lem1901953 h3)). Qed.
Lemma lem1902732 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1902731 h1 h2 h3 h4 h5) (@lem1901953 h3)). Qed.
Lemma lem1902733 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term42 = False.
Proof. exact (prop_ext (fun h6 : term42 => @lem1902732 h1 h2 h3 h4 h5) (fun h6 : False => @lem1901940 h1)). Qed.
Lemma lem1902734 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1902733 h1 h2 h3 h4 h5) (@lem1901940 h1)). Qed.
Lemma lem1902735 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term11 = False.
Proof. exact (prop_ext (fun h6 : term11 => @lem1902734 h1 h2 h3 h4 h5) (fun h6 : False => @lem1901927 h5)). Qed.
Lemma lem1902736 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1902735 h1 h2 h3 h4 h5) (@lem1901927 h5)). Qed.
Lemma lem1902737 (h1 : term42) (h2 : term39) (h3 : term36) (h4 : term11) : term16.
Proof. exact (fun h0 : term18 => @lem1902736 h1 h0 h2 h3 h4). Qed.
Lemma lem1902738 : term16 = term17.
Proof. exact (@lem69 term18). Qed.
Lemma lem1902739 (h1 : term42) (h2 : term39) (h3 : term36) (h4 : term11) : term17.
Proof. exact (EQ_MP (@lem1902738) (@lem1902737 h1 h2 h3 h4)). Qed.
Lemma lem1902740 (h1 : term42) (h2 : term39) (h3 : term11) : term21.
Proof. exact (fun h0 : term36 => @lem1902739 h1 h2 h0 h3). Qed.
Lemma lem1902741 (h1 : term42) (h2 : term11) : term24.
Proof. exact (fun h0 : term39 => @lem1902740 h1 h0 h2). Qed.
Lemma lem1902742 (h1 : term11) : term27.
Proof. exact (fun h0 : term42 => @lem1902741 h0 h1). Qed.
Lemma lem1902743 : term29.
Proof. exact (fun h0 : term11 => @lem1902742 h0). Qed.
Lemma lem1902744 : term12.
Proof. exact (EQ_MP (@lem1901916) (@lem1902743)). Qed.
Lemma lem1902746 : term12.
Proof. exact (@lem1901771 (@lem1902744)). Qed.
Lemma lem1902747 (h1 : term11) : term26.
Proof. exact (@lem1902746 (@lem1901756 h1)). Qed.
Lemma lem1902748 (h1 : term11) : term23.
Proof. exact (@lem1902747 h1 (@lem1384343)). Qed.
Lemma lem1902749 (h1 : term11) : term20.
Proof. exact (@lem1902748 h1 (@lem1338986)). Qed.
Lemma lem1902750 (h1 : term11) : term16.
Proof. exact (@lem1902749 h1 (@lem1383497)). Qed.
Lemma lem1902751 (h1 : term11) : False.
Proof. exact (@lem1902750 h1 (@lem1900060)). Qed.
Lemma lem1902752 (h1 : term11) : term11 = False.
Proof. exact (prop_ext (fun h2 : term11 => @lem1902751 h1) (fun h2 : False => @lem1901756 h1)). Qed.
Lemma lem1902753 (h1 : term11) : False.
Proof. exact (EQ_MP (@lem1902752 h1) (@lem1901756 h1)). Qed.
Lemma lem1902754 : term10.
Proof. exact (fun h0 : term11 => @lem1902753 h0). Qed.
Lemma lem1902755 : term8 = term9.
Proof. exact (EQ_MP (@lem1901755) (@lem1902754)). Qed.
