Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_0_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_POS_spec.
Require Import REAL_POW_2_spec.
Require Import SQRT_UNIQUE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
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
Lemma lem1900730 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1900731 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1900732 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1900731 t1) (@lem1900730 t1)). Qed.
Lemma lem1900733 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1900732 t1 t2). Qed.
Lemma lem1900734 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1900735 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1900734 t1 t2) (@lem1900733 t1 t2)). Qed.
Lemma lem1900736 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1900735 t1 t2 t3). Qed.
Lemma lem1900737 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1900738 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1900737 t1 t2 t3) (@lem1900736 t1 t2 t3)). Qed.
Lemma lem1900739 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1900738 t1 t2 t3)). Qed.
Lemma lem1900741 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1900742 : (term8 = term9) = term10.
Proof. exact (@lem1900741 (term8 = term9)). Qed.
Lemma lem1900743 : term10 = (term8 = term9).
Proof. exact (SYM (@lem1900742)). Qed.
Lemma lem1900744 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1900747 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1900748 : term13.
Proof. exact (fun h0 : term12 => @lem1900747 h0). Qed.
Lemma lem1900749 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1900750 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1900751 (h1 : term12) (h2 : term13) : term12.
Proof. exact (@lem1900749 h2 (@lem1900750 h1)). Qed.
Lemma lem1900752 (h1 : term12) : term14.
Proof. exact (fun h0 : term13 => @lem1900751 h1 h0). Qed.
Lemma lem1900753 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1900754 (h1 : term12) (h2 : term13) : term12.
Proof. exact (@lem1900752 h1 (@lem1900753 h2)). Qed.
Lemma lem1900755 (h1 : term13) : term13.
Proof. exact (fun h0 : term12 => @lem1900754 h0 h1). Qed.
Lemma lem1900756 : term15.
Proof. exact (fun h0 : term13 => @lem1900755 h0). Qed.
Lemma lem1900759 : term13.
Proof. exact (@lem1900756 (@lem1900748)). Qed.
Lemma lem1900781 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1900782 : term16 = term17.
Proof. exact (@lem1900781 term18). Qed.
Lemma lem1900795 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem1900796 : term20 = term21.
Proof. exact (MK_COMB (@lem1900795) (@lem1900782)). Qed.
Lemma lem1900799 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem1900800 : term23 = term24.
Proof. exact (MK_COMB (@lem1900799) (@lem1900796)). Qed.
Lemma lem1900803 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem1900804 : term26 = term27.
Proof. exact (MK_COMB (@lem1900803) (@lem1900800)). Qed.
Lemma lem1900807 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1900814 : term12 = term29.
Proof. exact (MK_COMB (@lem1900807) (@lem1900804)). Qed.
Lemma lem1900823 (x : real) (y : real) : (term30 x y) = (term30 x y).
Proof. exact (eq_refl (term30 x y)). Qed.
Lemma lem1900824 (x : real) : (term31 x) = (term31 x).
Proof. exact (fun_ext (fun y : real => @lem1900823 x y)). Qed.
Lemma lem1900825 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1900826 (x : real) : (term32 x) = (term32 x).
Proof. exact (MK_COMB (@lem1900825) (@lem1900824 x)). Qed.
Lemma lem1900827 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1900826 x)). Qed.
Lemma lem1900828 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1900829 : term18 = term18.
Proof. exact (MK_COMB (@lem1900828) (@lem1900827)). Qed.
Lemma lem1900830 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1900831 : term17 = term17.
Proof. exact (MK_COMB (@lem1900830) (@lem1900829)). Qed.
Lemma lem1900832 (x : real) : ((term34 x) = (real_mul x x)) = ((term34 x) = (real_mul x x)).
Proof. exact (eq_refl ((term34 x) = (real_mul x x))). Qed.
Lemma lem1900833 : term35 = term35.
Proof. exact (fun_ext (fun x : real => @lem1900832 x)). Qed.
Lemma lem1900834 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1900835 : term36 = term36.
Proof. exact (MK_COMB (@lem1900834) (@lem1900833)). Qed.
Lemma lem1900836 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1900837 : term19 = term19.
Proof. exact (MK_COMB (@lem1900836) (@lem1900835)). Qed.
Lemma lem1900838 : term21 = term21.
Proof. exact (MK_COMB (@lem1900837) (@lem1900831)). Qed.
Lemma lem1900839 (x : real) : ((term37 x) = term9) = ((term37 x) = term9).
Proof. exact (eq_refl ((term37 x) = term9)). Qed.
Lemma lem1900840 : term38 = term38.
Proof. exact (fun_ext (fun x : real => @lem1900839 x)). Qed.
Lemma lem1900841 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1900842 : term39 = term39.
Proof. exact (MK_COMB (@lem1900841) (@lem1900840)). Qed.
Lemma lem1900843 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1900844 : term22 = term22.
Proof. exact (MK_COMB (@lem1900843) (@lem1900842)). Qed.
Lemma lem1900845 : term24 = term24.
Proof. exact (MK_COMB (@lem1900844) (@lem1900838)). Qed.
Lemma lem1900846 (n : nat) : (term40 n) = (term40 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem1900847 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem1900846 n)). Qed.
Lemma lem1900848 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1900849 : term42 = term42.
Proof. exact (MK_COMB (@lem1900848) (@lem1900847)). Qed.
Lemma lem1900850 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1900851 : term25 = term25.
Proof. exact (MK_COMB (@lem1900850) (@lem1900849)). Qed.
Lemma lem1900852 : term27 = term27.
Proof. exact (MK_COMB (@lem1900851) (@lem1900845)). Qed.
Lemma lem1900857 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1900858 : term29 = term29.
Proof. exact (MK_COMB (@lem1900857) (@lem1900852)). Qed.
Lemma lem1900903 : term12 = term29.
Proof. exact (TRANS (@lem1900814) (@lem1900858)). Qed.
Lemma lem1900904 : term29 = term12.
Proof. exact (SYM (@lem1900903)). Qed.
Lemma lem1900906 (h1 : term42) : term42.
Proof. exact (h1). Qed.
Lemma lem1900907 (h1 : term39) : term39.
Proof. exact (h1). Qed.
Lemma lem1900908 (h1 : term36) : term36.
Proof. exact (h1). Qed.
Lemma lem1900909 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem1900915 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1900916 (n : nat) : (term40 n) = (term40 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem1900917 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem1900916 n)). Qed.
Lemma lem1900918 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1900927 : term42 = term42.
Proof. exact (MK_COMB (@lem1900918) (@lem1900917)). Qed.
Lemma lem1900928 (h1 : term42) : term42.
Proof. exact (EQ_MP (@lem1900927) (@lem1900906 h1)). Qed.
Lemma lem1900929 (x : real) : ((term37 x) = term9) = ((term37 x) = term9).
Proof. exact (eq_refl ((term37 x) = term9)). Qed.
Lemma lem1900930 : term38 = term38.
Proof. exact (fun_ext (fun x : real => @lem1900929 x)). Qed.
Lemma lem1900931 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1900940 : term39 = term39.
Proof. exact (MK_COMB (@lem1900931) (@lem1900930)). Qed.
Lemma lem1900941 (h1 : term39) : term39.
Proof. exact (EQ_MP (@lem1900940) (@lem1900907 h1)). Qed.
Lemma lem1900942 (x : real) : ((term34 x) = (real_mul x x)) = ((term34 x) = (real_mul x x)).
Proof. exact (eq_refl ((term34 x) = (real_mul x x))). Qed.
Lemma lem1900943 : term35 = term35.
Proof. exact (fun_ext (fun x : real => @lem1900942 x)). Qed.
Lemma lem1900944 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1900953 : term36 = term36.
Proof. exact (MK_COMB (@lem1900944) (@lem1900943)). Qed.
Lemma lem1900954 (h1 : term36) : term36.
Proof. exact (EQ_MP (@lem1900953) (@lem1900908 h1)). Qed.
Lemma lem1900961 (y : real) (x : real) : (term43 y x) = (term44 y x).
Proof. exact (@lem17045 (term45 y) ((term34 y) = x)). Qed.
Lemma lem1900962 (x : real) (y : real) : ((sqrt x) = y) = ((sqrt x) = y).
Proof. exact (eq_refl ((sqrt x) = y)). Qed.
Lemma lem1900963 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1900964 (y : real) (x : real) : (term46 y x) = (term47 y x).
Proof. exact (MK_COMB (@lem1900963) (@lem1900961 y x)). Qed.
Lemma lem1900965 (x : real) (y : real) : (term48 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem1900964 y x) (@lem1900962 x y)). Qed.
Lemma lem1900966 (x : real) (y : real) : (term30 x y) = (term48 x y).
Proof. exact (@lem17265 (term50 y x) ((sqrt x) = y)). Qed.
Lemma lem1900967 (x : real) (y : real) : (term30 x y) = (term49 x y).
Proof. exact (TRANS (@lem1900966 x y) (@lem1900965 x y)). Qed.
Lemma lem1900968 (x : real) : (term31 x) = (term51 x).
Proof. exact (fun_ext (fun y : real => @lem1900967 x y)). Qed.
Lemma lem1900969 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1900970 (x : real) : (term32 x) = (term52 x).
Proof. exact (MK_COMB (@lem1900969) (@lem1900968 x)). Qed.
Lemma lem1900971 : term33 = term53.
Proof. exact (fun_ext (fun x : real => @lem1900970 x)). Qed.
Lemma lem1900972 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1901029 : term18 = term54.
Proof. exact (MK_COMB (@lem1900972) (@lem1900971)). Qed.
Lemma lem1901030 (h1 : term18) : term54.
Proof. exact (EQ_MP (@lem1901029) (@lem1900909 h1)). Qed.
Lemma lem1901048 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1901059 (n : nat) : (term40 n) = (term40 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem1901060 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem1901059 n)). Qed.
Lemma lem1901061 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1901062 : term42 = term42.
Proof. exact (MK_COMB (@lem1901061) (@lem1901060)). Qed.
Lemma lem1901063 (h1 : term42) : term42.
Proof. exact (EQ_MP (@lem1901062) (@lem1900928 h1)). Qed.
Lemma lem1901080 (x : real) : ((term37 x) = term9) = ((term37 x) = term9).
Proof. exact (eq_refl ((term37 x) = term9)). Qed.
Lemma lem1901081 : term38 = term38.
Proof. exact (fun_ext (fun x : real => @lem1901080 x)). Qed.
Lemma lem1901082 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1901083 : term39 = term39.
Proof. exact (MK_COMB (@lem1901082) (@lem1901081)). Qed.
Lemma lem1901084 (h1 : term39) : term39.
Proof. exact (EQ_MP (@lem1901083) (@lem1900941 h1)). Qed.
Lemma lem1901103 (x : real) : ((term34 x) = (real_mul x x)) = ((term34 x) = (real_mul x x)).
Proof. exact (eq_refl ((term34 x) = (real_mul x x))). Qed.
Lemma lem1901104 : term35 = term35.
Proof. exact (fun_ext (fun x : real => @lem1901103 x)). Qed.
Lemma lem1901105 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1901106 : term36 = term36.
Proof. exact (MK_COMB (@lem1901105) (@lem1901104)). Qed.
Lemma lem1901107 (h1 : term36) : term36.
Proof. exact (EQ_MP (@lem1901106) (@lem1900954 h1)). Qed.
Lemma lem1901148 (x : real) (y : real) : (term49 x y) = (term49 x y).
Proof. exact (eq_refl (term49 x y)). Qed.
Lemma lem1901149 (x : real) : (term51 x) = (term51 x).
Proof. exact (fun_ext (fun y : real => @lem1901148 x y)). Qed.
Lemma lem1901150 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1901151 (x : real) : (term52 x) = (term52 x).
Proof. exact (MK_COMB (@lem1901150) (@lem1901149 x)). Qed.
Lemma lem1901152 : term53 = term53.
Proof. exact (fun_ext (fun x : real => @lem1901151 x)). Qed.
Lemma lem1901153 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1901154 : term54 = term54.
Proof. exact (MK_COMB (@lem1901153) (@lem1901152)). Qed.
Lemma lem1901155 (h1 : term18) : term54.
Proof. exact (EQ_MP (@lem1901154) (@lem1901030 h1)). Qed.
Lemma lem1901159 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1901161 (n : nat) : (term40 n) = (term40 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem1901162 : term41 = term41.
Proof. exact (fun_ext (fun n : nat => @lem1901161 n)). Qed.
Lemma lem1901163 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1901165 : term42 = term42.
Proof. exact (MK_COMB (@lem1901163) (@lem1901162)). Qed.
Lemma lem1901166 (h1 : term42) : term42.
Proof. exact (EQ_MP (@lem1901165) (@lem1901063 h1)). Qed.
Lemma lem1901168 (x : real) : ((term37 x) = term9) = ((term37 x) = term9).
Proof. exact (eq_refl ((term37 x) = term9)). Qed.
Lemma lem1901169 : term38 = term38.
Proof. exact (fun_ext (fun x : real => @lem1901168 x)). Qed.
Lemma lem1901170 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1901172 : term39 = term39.
Proof. exact (MK_COMB (@lem1901170) (@lem1901169)). Qed.
Lemma lem1901173 (h1 : term39) : term39.
Proof. exact (EQ_MP (@lem1901172) (@lem1901084 h1)). Qed.
Lemma lem1901175 (x : real) : ((term34 x) = (real_mul x x)) = ((term34 x) = (real_mul x x)).
Proof. exact (eq_refl ((term34 x) = (real_mul x x))). Qed.
Lemma lem1901176 : term35 = term35.
Proof. exact (fun_ext (fun x : real => @lem1901175 x)). Qed.
Lemma lem1901177 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1901179 : term36 = term36.
Proof. exact (MK_COMB (@lem1901177) (@lem1901176)). Qed.
Lemma lem1901180 (h1 : term36) : term36.
Proof. exact (EQ_MP (@lem1901179) (@lem1901107 h1)). Qed.
Lemma lem1901194 (x : real) (y : real) : (term49 x y) = (term49 x y).
Proof. exact (eq_refl (term49 x y)). Qed.
Lemma lem1901195 (x : real) : (term51 x) = (term51 x).
Proof. exact (fun_ext (fun y : real => @lem1901194 x y)). Qed.
Lemma lem1901196 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1901197 (x : real) : (term52 x) = (term52 x).
Proof. exact (MK_COMB (@lem1901196) (@lem1901195 x)). Qed.
Lemma lem1901198 : term53 = term53.
Proof. exact (fun_ext (fun x : real => @lem1901197 x)). Qed.
Lemma lem1901199 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1901201 : term54 = term54.
Proof. exact (MK_COMB (@lem1901199) (@lem1901198)). Qed.
Lemma lem1901202 (h1 : term18) : term54.
Proof. exact (EQ_MP (@lem1901201) (@lem1901155 h1)). Qed.
Lemma lem1901203 (_27049 : nat) (h1 : term42) : term55 _27049.
Proof. exact (@lem1901166 h1 _27049). Qed.
Lemma lem1901204 (_27049 : nat) : (term55 _27049) = (term40 _27049).
Proof. exact (eq_refl (term55 _27049)). Qed.
Lemma lem1901206 (_27050 : real) (h1 : term39) : term56 _27050.
Proof. exact (@lem1901173 h1 _27050). Qed.
Lemma lem1901207 (_27050 : real) : (term56 _27050) = ((term37 _27050) = term9).
Proof. exact (eq_refl (term56 _27050)). Qed.
Lemma lem1901209 (_27051 : real) (h1 : term36) : term57 _27051.
Proof. exact (@lem1901180 h1 _27051). Qed.
Lemma lem1901210 (_27051 : real) : (term57 _27051) = ((term34 _27051) = (real_mul _27051 _27051)).
Proof. exact (eq_refl (term57 _27051)). Qed.
Lemma lem1901212 (_27052 : real) (h1 : term18) : term58 _27052.
Proof. exact (@lem1901202 h1 _27052). Qed.
Lemma lem1901213 (_27052 : real) : (term58 _27052) = (term52 _27052).
Proof. exact (eq_refl (term58 _27052)). Qed.
Lemma lem1901214 (_27052 : real) (h1 : term18) : term52 _27052.
Proof. exact (EQ_MP (@lem1901213 _27052) (@lem1901212 _27052 h1)). Qed.
Lemma lem1901215 (_27052 : real) (_27053 : real) (h1 : term18) : term59 _27052 _27053.
Proof. exact (@lem1901214 _27052 h1 _27053). Qed.
Lemma lem1901216 (_27052 : real) (_27053 : real) : (term59 _27052 _27053) = (term49 _27052 _27053).
Proof. exact (eq_refl (term59 _27052 _27053)). Qed.
Lemma lem1901217 (_27052 : real) (_27053 : real) (h1 : term18) : term49 _27052 _27053.
Proof. exact (EQ_MP (@lem1901216 _27052 _27053) (@lem1901215 _27052 _27053 h1)). Qed.
Lemma lem1901219 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1901236 (_27052 : real) (_27053 : real) : (term49 _27052 _27053) = (term60 _27052 _27053).
Proof. exact (@lem1900739 (term61 _27053) (term62 _27053 _27052) ((sqrt _27052) = _27053)). Qed.
Lemma lem1901237 (_27052 : real) (_27053 : real) (h1 : term18) : term60 _27052 _27053.
Proof. exact (EQ_MP (@lem1901236 _27052 _27053) (@lem1901217 _27052 _27053 h1)). Qed.
Lemma lem1901303 : sqrt = sqrt.
Proof. exact (eq_refl sqrt). Qed.
Lemma lem1901304 (_27070 : real) (_27071 : real) (h1 : _27070 = _27071) : _27070 = _27071.
Proof. exact (h1). Qed.
Lemma lem1901305 (_27070 : real) (_27071 : real) (h1 : _27070 = _27071) : (sqrt _27070) = (sqrt _27071).
Proof. exact (MK_COMB (@lem1901303) (@lem1901304 _27070 _27071 h1)). Qed.
Lemma lem1901306 (_27070 : real) (_27071 : real) : term63 _27070 _27071.
Proof. exact (fun h0 : _27070 = _27071 => @lem1901305 _27070 _27071 h0). Qed.
Lemma lem1901308 (a : Prop) (b : Prop) : (a -> b) = (term64 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1901309 (_27070 : real) (_27071 : real) : (term63 _27070 _27071) = (term65 _27070 _27071).
Proof. exact (@lem1901308 (_27070 = _27071) ((sqrt _27070) = (sqrt _27071))). Qed.
Lemma lem1901310 (_27070 : real) (_27071 : real) : term65 _27070 _27071.
Proof. exact (EQ_MP (@lem1901309 _27070 _27071) (@lem1901306 _27070 _27071)). Qed.
Lemma lem1901328 (x : real) (y : real) (z : real) : term66 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1901332 (_27050 : real) (h1 : term39) : (term37 _27050) = term9.
Proof. exact (EQ_MP (@lem1901207 _27050) (@lem1901206 _27050 h1)). Qed.
Lemma lem1901333 (h1 : term39) : term67 = term9.
Proof. exact (@lem1901332 term9 h1). Qed.
Lemma lem1901334 (h1 : term39) : term68.
Proof. exact (fun h0 : term69 => @lem1901333 h1). Qed.
Lemma lem1901336 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1901337 : term68 = (term67 = term9).
Proof. exact (@lem1901336 (term67 = term9)). Qed.
Lemma lem1901338 (h1 : term39) : term67 = term9.
Proof. exact (EQ_MP (@lem1901337) (@lem1901334 h1)). Qed.
Lemma lem1901344 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1901345 (_27070 : real) (_27071 : real) : (term65 _27070 _27071) = (term71 _27070 _27071).
Proof. exact (@lem1901344 ((sqrt _27070) = (sqrt _27071)) (term72 _27070 _27071)). Qed.
Lemma lem1901355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1901356 (_27070 : real) (_27071 : real) : (term73 _27070 _27071) = (term74 _27070 _27071).
Proof. exact (MK_COMB (@lem1901355) (@lem1901345 _27070 _27071)). Qed.
Lemma lem1901366 (_27070 : real) (_27071 : real) : (term71 _27070 _27071) = (term71 _27070 _27071).
Proof. exact (eq_refl (term71 _27070 _27071)). Qed.
Lemma lem1901367 (_27070 : real) (_27071 : real) : ((term65 _27070 _27071) = (term71 _27070 _27071)) = ((term71 _27070 _27071) = (term71 _27070 _27071)).
Proof. exact (MK_COMB (@lem1901356 _27070 _27071) (@lem1901366 _27070 _27071)). Qed.
Lemma lem1901369 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1901370 (x : Prop) : (x = x) = True.
Proof. exact (@lem1901369 Prop x). Qed.
Lemma lem1901371 (_27070 : real) (_27071 : real) : ((term71 _27070 _27071) = (term71 _27070 _27071)) = True.
Proof. exact (@lem1901370 (term71 _27070 _27071)). Qed.
Lemma lem1901372 (_27070 : real) (_27071 : real) : ((term65 _27070 _27071) = (term71 _27070 _27071)) = True.
Proof. exact (TRANS (@lem1901367 _27070 _27071) (@lem1901371 _27070 _27071)). Qed.
Lemma lem1901373 (_27070 : real) (_27071 : real) : True = ((term65 _27070 _27071) = (term71 _27070 _27071)).
Proof. exact (SYM (@lem1901372 _27070 _27071)). Qed.
Lemma lem1901374 (_27070 : real) (_27071 : real) : (term65 _27070 _27071) = (term71 _27070 _27071).
Proof. exact (EQ_MP (@lem1901373 _27070 _27071) (@lem0)). Qed.
Lemma lem1901375 (_27070 : real) (_27071 : real) : term71 _27070 _27071.
Proof. exact (EQ_MP (@lem1901374 _27070 _27071) (@lem1901310 _27070 _27071)). Qed.
Lemma lem1901377 (b : Prop) (a : Prop) : (a \/ b) = (term75 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1901378 (_27070 : real) (_27071 : real) : (term71 _27070 _27071) = (term76 _27070 _27071).
Proof. exact (@lem1901377 (term72 _27070 _27071) ((sqrt _27070) = (sqrt _27071))). Qed.
Lemma lem1901380 (a : Prop) : (term77 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1901381 (_27070 : real) (_27071 : real) : (term78 _27070 _27071) = (_27070 = _27071).
Proof. exact (@lem1901380 (_27070 = _27071)). Qed.
Lemma lem1901382 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1901383 (_27070 : real) (_27071 : real) : (term79 _27070 _27071) = (term80 _27070 _27071).
Proof. exact (MK_COMB (@lem1901382) (@lem1901381 _27070 _27071)). Qed.
Lemma lem1901384 (_27070 : real) (_27071 : real) : ((sqrt _27070) = (sqrt _27071)) = ((sqrt _27070) = (sqrt _27071)).
Proof. exact (eq_refl ((sqrt _27070) = (sqrt _27071))). Qed.
Lemma lem1901385 (_27070 : real) (_27071 : real) : (term76 _27070 _27071) = (term63 _27070 _27071).
Proof. exact (MK_COMB (@lem1901383 _27070 _27071) (@lem1901384 _27070 _27071)). Qed.
Lemma lem1901386 (_27070 : real) (_27071 : real) : (term71 _27070 _27071) = (term63 _27070 _27071).
Proof. exact (TRANS (@lem1901378 _27070 _27071) (@lem1901385 _27070 _27071)). Qed.
Lemma lem1901389 (_27070 : real) (_27071 : real) : term63 _27070 _27071.
Proof. exact (EQ_MP (@lem1901386 _27070 _27071) (@lem1901375 _27070 _27071)). Qed.
Lemma lem1901390 : term81.
Proof. exact (@lem1901389 term67 term9). Qed.
Lemma lem1901393 (h1 : term39) : term82 = term8.
Proof. exact (@lem1901390 (@lem1901338 h1)). Qed.
Lemma lem1901394 (h1 : term39) : term83.
Proof. exact (fun h0 : term84 => @lem1901393 h1). Qed.
Lemma lem1901396 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1901397 : term83 = (term82 = term8).
Proof. exact (@lem1901396 (term82 = term8)). Qed.
Lemma lem1901398 (h1 : term39) : term82 = term8.
Proof. exact (EQ_MP (@lem1901397) (@lem1901394 h1)). Qed.
Lemma lem1901400 (_27049 : nat) (h1 : term42) : term40 _27049.
Proof. exact (EQ_MP (@lem1901204 _27049) (@lem1901203 _27049 h1)). Qed.
Lemma lem1901401 (h1 : term42) : term85.
Proof. exact (@lem1901400 (NUMERAL 0) h1). Qed.
Lemma lem1901402 (h1 : term42) : term86.
Proof. exact (fun h0 : term87 => @lem1901401 h1). Qed.
Lemma lem1901404 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1901405 : term86 = term85.
Proof. exact (@lem1901404 term85). Qed.
Lemma lem1901406 (h1 : term42) : term85.
Proof. exact (EQ_MP (@lem1901405) (@lem1901402 h1)). Qed.
Lemma lem1901408 (_27051 : real) (h1 : term36) : (term34 _27051) = (real_mul _27051 _27051).
Proof. exact (EQ_MP (@lem1901210 _27051) (@lem1901209 _27051 h1)). Qed.
Lemma lem1901409 (h1 : term36) : term88 = term67.
Proof. exact (@lem1901408 term9 h1). Qed.
Lemma lem1901410 (h1 : term36) : term89.
Proof. exact (fun h0 : term90 => @lem1901409 h1). Qed.
Lemma lem1901412 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1901413 : term89 = (term88 = term67).
Proof. exact (@lem1901412 (term88 = term67)). Qed.
Lemma lem1901414 (h1 : term36) : term88 = term67.
Proof. exact (EQ_MP (@lem1901413) (@lem1901410 h1)). Qed.
Lemma lem1901420 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1901421 (_27052 : real) (_27053 : real) : (term60 _27052 _27053) = (term91 _27052 _27053).
Proof. exact (@lem1901420 (term62 _27053 _27052) (term61 _27053) ((sqrt _27052) = _27053)). Qed.
Lemma lem1901437 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1901438 (_27052 : real) (_27053 : real) : (term92 _27052 _27053) = (term93 _27052 _27053).
Proof. exact (@lem1901437 ((sqrt _27052) = _27053) (term61 _27053)). Qed.
Lemma lem1901446 (_27053 : real) (_27052 : real) : (term94 _27053 _27052) = (term94 _27053 _27052).
Proof. exact (eq_refl (term94 _27053 _27052)). Qed.
Lemma lem1901447 (_27052 : real) (_27053 : real) : (term91 _27052 _27053) = (term95 _27052 _27053).
Proof. exact (MK_COMB (@lem1901446 _27053 _27052) (@lem1901438 _27052 _27053)). Qed.
Lemma lem1901451 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1901452 (_27052 : real) (_27053 : real) : (term95 _27052 _27053) = (term96 _27052 _27053).
Proof. exact (@lem1901451 ((sqrt _27052) = _27053) (term62 _27053 _27052) (term61 _27053)). Qed.
Lemma lem1901472 (_27052 : real) (_27053 : real) : (term91 _27052 _27053) = (term96 _27052 _27053).
Proof. exact (TRANS (@lem1901447 _27052 _27053) (@lem1901452 _27052 _27053)). Qed.
Lemma lem1901473 (_27052 : real) (_27053 : real) : (term60 _27052 _27053) = (term96 _27052 _27053).
Proof. exact (TRANS (@lem1901421 _27052 _27053) (@lem1901472 _27052 _27053)). Qed.
Lemma lem1901474 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1901475 (_27052 : real) (_27053 : real) : (term97 _27052 _27053) = (term98 _27052 _27053).
Proof. exact (MK_COMB (@lem1901474) (@lem1901473 _27052 _27053)). Qed.
Lemma lem1901491 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1901492 (_27052 : real) (_27053 : real) : (term44 _27053 _27052) = (term99 _27052 _27053).
Proof. exact (@lem1901491 (term62 _27053 _27052) (term61 _27053)). Qed.
Lemma lem1901500 (_27052 : real) (_27053 : real) : (term100 _27052 _27053) = (term100 _27052 _27053).
Proof. exact (eq_refl (term100 _27052 _27053)). Qed.
Lemma lem1901501 (_27052 : real) (_27053 : real) : (term101 _27053 _27052) = (term96 _27052 _27053).
Proof. exact (MK_COMB (@lem1901500 _27052 _27053) (@lem1901492 _27052 _27053)). Qed.
Lemma lem1901512 (_27052 : real) (_27053 : real) : ((term60 _27052 _27053) = (term101 _27053 _27052)) = ((term96 _27052 _27053) = (term96 _27052 _27053)).
Proof. exact (MK_COMB (@lem1901475 _27052 _27053) (@lem1901501 _27052 _27053)). Qed.
Lemma lem1901514 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1901515 (x : Prop) : (x = x) = True.
Proof. exact (@lem1901514 Prop x). Qed.
Lemma lem1901516 (_27052 : real) (_27053 : real) : ((term96 _27052 _27053) = (term96 _27052 _27053)) = True.
Proof. exact (@lem1901515 (term96 _27052 _27053)). Qed.
Lemma lem1901517 (_27053 : real) (_27052 : real) : ((term60 _27052 _27053) = (term101 _27053 _27052)) = True.
Proof. exact (TRANS (@lem1901512 _27052 _27053) (@lem1901516 _27052 _27053)). Qed.
Lemma lem1901518 (_27053 : real) (_27052 : real) : True = ((term60 _27052 _27053) = (term101 _27053 _27052)).
Proof. exact (SYM (@lem1901517 _27053 _27052)). Qed.
Lemma lem1901519 (_27053 : real) (_27052 : real) : (term60 _27052 _27053) = (term101 _27053 _27052).
Proof. exact (EQ_MP (@lem1901518 _27053 _27052) (@lem0)). Qed.
Lemma lem1901520 (_27053 : real) (_27052 : real) (h1 : term18) : term101 _27053 _27052.
Proof. exact (EQ_MP (@lem1901519 _27053 _27052) (@lem1901237 _27052 _27053 h1)). Qed.
Lemma lem1901522 (b : Prop) (a : Prop) : (a \/ b) = (term75 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1901523 (_27052 : real) (_27053 : real) : (term101 _27053 _27052) = (term102 _27052 _27053).
Proof. exact (@lem1901522 (term44 _27053 _27052) ((sqrt _27052) = _27053)). Qed.
Lemma lem1901525 (a : Prop) (b : Prop) : (term103 a b) = (term104 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1901526 (_27053 : real) (_27052 : real) : (term105 _27053 _27052) = (term106 _27053 _27052).
Proof. exact (@lem1901525 (term61 _27053) (term62 _27053 _27052)). Qed.
Lemma lem1901528 (a : Prop) : (term77 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1901529 (_27053 : real) : (term107 _27053) = (term45 _27053).
Proof. exact (@lem1901528 (term45 _27053)). Qed.
Lemma lem1901530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1901531 (_27053 : real) : (term108 _27053) = (term109 _27053).
Proof. exact (MK_COMB (@lem1901530) (@lem1901529 _27053)). Qed.
Lemma lem1901533 (a : Prop) : (term77 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1901534 (_27053 : real) (_27052 : real) : (term110 _27053 _27052) = ((term34 _27053) = _27052).
Proof. exact (@lem1901533 ((term34 _27053) = _27052)). Qed.
Lemma lem1901535 (_27053 : real) (_27052 : real) : (term106 _27053 _27052) = (term50 _27053 _27052).
Proof. exact (MK_COMB (@lem1901531 _27053) (@lem1901534 _27053 _27052)). Qed.
Lemma lem1901536 (_27053 : real) (_27052 : real) : (term105 _27053 _27052) = (term50 _27053 _27052).
Proof. exact (TRANS (@lem1901526 _27053 _27052) (@lem1901535 _27053 _27052)). Qed.
Lemma lem1901537 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1901538 (_27053 : real) (_27052 : real) : (term111 _27053 _27052) = (term112 _27053 _27052).
Proof. exact (MK_COMB (@lem1901537) (@lem1901536 _27053 _27052)). Qed.
Lemma lem1901539 (_27052 : real) (_27053 : real) : ((sqrt _27052) = _27053) = ((sqrt _27052) = _27053).
Proof. exact (eq_refl ((sqrt _27052) = _27053)). Qed.
Lemma lem1901540 (_27052 : real) (_27053 : real) : (term102 _27052 _27053) = (term30 _27052 _27053).
Proof. exact (MK_COMB (@lem1901538 _27053 _27052) (@lem1901539 _27052 _27053)). Qed.
Lemma lem1901541 (_27052 : real) (_27053 : real) : (term101 _27053 _27052) = (term30 _27052 _27053).
Proof. exact (TRANS (@lem1901523 _27052 _27053) (@lem1901540 _27052 _27053)). Qed.
Lemma lem1901543 (h1 : term42) (h2 : term36) : term113.
Proof. exact (conj (@lem1901406 h1) (@lem1901414 h2)). Qed.
Lemma lem1901545 (_27052 : real) (_27053 : real) (h1 : term18) : term30 _27052 _27053.
Proof. exact (EQ_MP (@lem1901541 _27052 _27053) (@lem1901520 _27053 _27052 h1)). Qed.
Lemma lem1901546 (h1 : term18) : term114.
Proof. exact (@lem1901545 term67 term9 h1). Qed.
Lemma lem1901549 (h1 : term42) (h2 : term18) (h3 : term36) : term82 = term9.
Proof. exact (@lem1901546 h2 (@lem1901543 h1 h3)). Qed.
Lemma lem1901550 (h1 : term42) (h2 : term18) (h3 : term36) : term115.
Proof. exact (fun h0 : term116 => @lem1901549 h1 h2 h3). Qed.
Lemma lem1901552 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1901553 : term115 = (term82 = term9).
Proof. exact (@lem1901552 (term82 = term9)). Qed.
Lemma lem1901554 (h1 : term42) (h2 : term18) (h3 : term36) : term82 = term9.
Proof. exact (EQ_MP (@lem1901553) (@lem1901550 h1 h2 h3)). Qed.
Lemma lem1901572 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1901573 (y : real) (x : real) (z : real) : (term117 x y z) = (term118 y x z).
Proof. exact (@lem1901572 (y = z) (term72 x z)). Qed.
Lemma lem1901583 (x : real) (y : real) : (term119 x y) = (term119 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1901584 (y : real) (x : real) (z : real) : (term66 x y z) = (term120 y x z).
Proof. exact (MK_COMB (@lem1901583 x y) (@lem1901573 y x z)). Qed.
Lemma lem1901588 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1901589 (y : real) (x : real) (z : real) : (term120 y x z) = (term121 y x z).
Proof. exact (@lem1901588 (y = z) (term72 x y) (term72 x z)). Qed.
Lemma lem1901611 (y : real) (x : real) (z : real) : (term66 x y z) = (term121 y x z).
Proof. exact (TRANS (@lem1901584 y x z) (@lem1901589 y x z)). Qed.
Lemma lem1901612 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1901613 (y : real) (x : real) (z : real) : (term122 x y z) = (term123 y x z).
Proof. exact (MK_COMB (@lem1901612) (@lem1901611 y x z)). Qed.
Lemma lem1901635 (y : real) (x : real) (z : real) : (term121 y x z) = (term121 y x z).
Proof. exact (eq_refl (term121 y x z)). Qed.
Lemma lem1901636 (y : real) (x : real) (z : real) : ((term66 x y z) = (term121 y x z)) = ((term121 y x z) = (term121 y x z)).
Proof. exact (MK_COMB (@lem1901613 y x z) (@lem1901635 y x z)). Qed.
Lemma lem1901638 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1901639 (x : Prop) : (x = x) = True.
Proof. exact (@lem1901638 Prop x). Qed.
Lemma lem1901640 (y : real) (x : real) (z : real) : ((term121 y x z) = (term121 y x z)) = True.
Proof. exact (@lem1901639 (term121 y x z)). Qed.
Lemma lem1901641 (y : real) (x : real) (z : real) : ((term66 x y z) = (term121 y x z)) = True.
Proof. exact (TRANS (@lem1901636 y x z) (@lem1901640 y x z)). Qed.
Lemma lem1901642 (y : real) (x : real) (z : real) : True = ((term66 x y z) = (term121 y x z)).
Proof. exact (SYM (@lem1901641 y x z)). Qed.
Lemma lem1901643 (y : real) (x : real) (z : real) : (term66 x y z) = (term121 y x z).
Proof. exact (EQ_MP (@lem1901642 y x z) (@lem0)). Qed.
Lemma lem1901644 (y : real) (x : real) (z : real) : term121 y x z.
Proof. exact (EQ_MP (@lem1901643 y x z) (@lem1901328 x y z)). Qed.
Lemma lem1901646 (b : Prop) (a : Prop) : (a \/ b) = (term75 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1901647 (x : real) (y : real) (z : real) : (term121 y x z) = (term124 x y z).
Proof. exact (@lem1901646 (term125 y x z) (y = z)). Qed.
Lemma lem1901649 (a : Prop) (b : Prop) : (term103 a b) = (term104 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1901650 (y : real) (x : real) (z : real) : (term126 y x z) = (term127 y x z).
Proof. exact (@lem1901649 (term72 x y) (term72 x z)). Qed.
Lemma lem1901652 (a : Prop) : (term77 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1901653 (x : real) (y : real) : (term78 x y) = (x = y).
Proof. exact (@lem1901652 (x = y)). Qed.
Lemma lem1901654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1901655 (x : real) (y : real) : (term128 x y) = (term129 x y).
Proof. exact (MK_COMB (@lem1901654) (@lem1901653 x y)). Qed.
Lemma lem1901657 (a : Prop) : (term77 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1901658 (x : real) (z : real) : (term78 x z) = (x = z).
Proof. exact (@lem1901657 (x = z)). Qed.
Lemma lem1901659 (y : real) (x : real) (z : real) : (term127 y x z) = (term130 y x z).
Proof. exact (MK_COMB (@lem1901655 x y) (@lem1901658 x z)). Qed.
Lemma lem1901660 (y : real) (x : real) (z : real) : (term126 y x z) = (term130 y x z).
Proof. exact (TRANS (@lem1901650 y x z) (@lem1901659 y x z)). Qed.
Lemma lem1901661 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1901662 (y : real) (x : real) (z : real) : (term131 y x z) = (term132 y x z).
Proof. exact (MK_COMB (@lem1901661) (@lem1901660 y x z)). Qed.
Lemma lem1901663 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1901664 (x : real) (y : real) (z : real) : (term124 x y z) = (term133 x y z).
Proof. exact (MK_COMB (@lem1901662 y x z) (@lem1901663 y z)). Qed.
Lemma lem1901665 (x : real) (y : real) (z : real) : (term121 y x z) = (term133 x y z).
Proof. exact (TRANS (@lem1901647 x y z) (@lem1901664 x y z)). Qed.
Lemma lem1901667 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) : term134.
Proof. exact (conj (@lem1901398 h3) (@lem1901554 h1 h2 h4)). Qed.
Lemma lem1901669 (x : real) (y : real) (z : real) : term133 x y z.
Proof. exact (EQ_MP (@lem1901665 x y z) (@lem1901644 y x z)). Qed.
Lemma lem1901670 : term135.
Proof. exact (@lem1901669 term82 term8 term9). Qed.
Lemma lem1901673 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) : term8 = term9.
Proof. exact (@lem1901670 (@lem1901667 h1 h2 h3 h4)). Qed.
Lemma lem1901674 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) : term136.
Proof. exact (fun h0 : term11 => @lem1901673 h1 h2 h3 h4). Qed.
Lemma lem1901676 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1901677 : term136 = (term8 = term9).
Proof. exact (@lem1901676 (term8 = term9)). Qed.
Lemma lem1901678 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) : term8 = term9.
Proof. exact (EQ_MP (@lem1901677) (@lem1901674 h1 h2 h3 h4)). Qed.
Lemma lem1901681 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1901683 : term11 = term137.
Proof. exact (@lem1901681 (term8 = term9)). Qed.
Lemma lem1901686 (h1 : term11) : term137.
Proof. exact (EQ_MP (@lem1901683) (@lem1901219 h1)). Qed.
Lemma lem1901689 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (@lem1901686 h5 (@lem1901678 h1 h2 h3 h4)). Qed.
Lemma lem1901690 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term138.
Proof. exact (fun h0 : ~ False => @lem1901689 h1 h2 h3 h4 h5). Qed.
Lemma lem1901692 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1901693 : term138 = False.
Proof. exact (@lem1901692 False). Qed.
Lemma lem1901694 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1901693) (@lem1901690 h1 h2 h3 h4 h5)). Qed.
Lemma lem1901695 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term11 = False.
Proof. exact (prop_ext (fun h6 : term11 => @lem1901694 h1 h2 h3 h4 h5) (fun h6 : False => @lem1901219 h5)). Qed.
Lemma lem1901696 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1901695 h1 h2 h3 h4 h5) (@lem1901219 h5)). Qed.
Lemma lem1901697 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term11 = False.
Proof. exact (prop_ext (fun h6 : term11 => @lem1901696 h1 h2 h3 h4 h5) (fun h6 : False => @lem1901159 h5)). Qed.
Lemma lem1901698 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1901697 h1 h2 h3 h4 h5) (@lem1901159 h5)). Qed.
Lemma lem1901699 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term36 = False.
Proof. exact (prop_ext (fun h6 : term36 => @lem1901698 h1 h2 h3 h4 h5) (fun h6 : False => @lem1901180 h4)). Qed.
Lemma lem1901700 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1901699 h1 h2 h3 h4 h5) (@lem1901180 h4)). Qed.
Lemma lem1901701 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term39 = False.
Proof. exact (prop_ext (fun h6 : term39 => @lem1901700 h1 h2 h3 h4 h5) (fun h6 : False => @lem1901173 h3)). Qed.
Lemma lem1901702 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1901701 h1 h2 h3 h4 h5) (@lem1901173 h3)). Qed.
Lemma lem1901703 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term42 = False.
Proof. exact (prop_ext (fun h6 : term42 => @lem1901702 h1 h2 h3 h4 h5) (fun h6 : False => @lem1901166 h1)). Qed.
Lemma lem1901704 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1901703 h1 h2 h3 h4 h5) (@lem1901166 h1)). Qed.
Lemma lem1901705 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term11 = False.
Proof. exact (prop_ext (fun h6 : term11 => @lem1901704 h1 h2 h3 h4 h5) (fun h6 : False => @lem1901159 h5)). Qed.
Lemma lem1901706 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1901705 h1 h2 h3 h4 h5) (@lem1901159 h5)). Qed.
Lemma lem1901707 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term36 = False.
Proof. exact (prop_ext (fun h6 : term36 => @lem1901706 h1 h2 h3 h4 h5) (fun h6 : False => @lem1901107 h4)). Qed.
Lemma lem1901708 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1901707 h1 h2 h3 h4 h5) (@lem1901107 h4)). Qed.
Lemma lem1901709 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term39 = False.
Proof. exact (prop_ext (fun h6 : term39 => @lem1901708 h1 h2 h3 h4 h5) (fun h6 : False => @lem1901084 h3)). Qed.
Lemma lem1901710 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1901709 h1 h2 h3 h4 h5) (@lem1901084 h3)). Qed.
Lemma lem1901711 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term42 = False.
Proof. exact (prop_ext (fun h6 : term42 => @lem1901710 h1 h2 h3 h4 h5) (fun h6 : False => @lem1901063 h1)). Qed.
Lemma lem1901712 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1901711 h1 h2 h3 h4 h5) (@lem1901063 h1)). Qed.
Lemma lem1901713 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term11 = False.
Proof. exact (prop_ext (fun h6 : term11 => @lem1901712 h1 h2 h3 h4 h5) (fun h6 : False => @lem1901048 h5)). Qed.
Lemma lem1901714 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1901713 h1 h2 h3 h4 h5) (@lem1901048 h5)). Qed.
Lemma lem1901715 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term36 = False.
Proof. exact (prop_ext (fun h6 : term36 => @lem1901714 h1 h2 h3 h4 h5) (fun h6 : False => @lem1900954 h4)). Qed.
Lemma lem1901716 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1901715 h1 h2 h3 h4 h5) (@lem1900954 h4)). Qed.
Lemma lem1901717 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term39 = False.
Proof. exact (prop_ext (fun h6 : term39 => @lem1901716 h1 h2 h3 h4 h5) (fun h6 : False => @lem1900941 h3)). Qed.
Lemma lem1901718 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1901717 h1 h2 h3 h4 h5) (@lem1900941 h3)). Qed.
Lemma lem1901719 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term42 = False.
Proof. exact (prop_ext (fun h6 : term42 => @lem1901718 h1 h2 h3 h4 h5) (fun h6 : False => @lem1900928 h1)). Qed.
Lemma lem1901720 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1901719 h1 h2 h3 h4 h5) (@lem1900928 h1)). Qed.
Lemma lem1901721 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : term11 = False.
Proof. exact (prop_ext (fun h6 : term11 => @lem1901720 h1 h2 h3 h4 h5) (fun h6 : False => @lem1900915 h5)). Qed.
Lemma lem1901722 (h1 : term42) (h2 : term18) (h3 : term39) (h4 : term36) (h5 : term11) : False.
Proof. exact (EQ_MP (@lem1901721 h1 h2 h3 h4 h5) (@lem1900915 h5)). Qed.
Lemma lem1901723 (h1 : term42) (h2 : term39) (h3 : term36) (h4 : term11) : term16.
Proof. exact (fun h0 : term18 => @lem1901722 h1 h0 h2 h3 h4). Qed.
Lemma lem1901724 : term16 = term17.
Proof. exact (@lem69 term18). Qed.
Lemma lem1901725 (h1 : term42) (h2 : term39) (h3 : term36) (h4 : term11) : term17.
Proof. exact (EQ_MP (@lem1901724) (@lem1901723 h1 h2 h3 h4)). Qed.
Lemma lem1901726 (h1 : term42) (h2 : term39) (h3 : term11) : term21.
Proof. exact (fun h0 : term36 => @lem1901725 h1 h2 h0 h3). Qed.
Lemma lem1901727 (h1 : term42) (h2 : term11) : term24.
Proof. exact (fun h0 : term39 => @lem1901726 h1 h0 h2). Qed.
Lemma lem1901728 (h1 : term11) : term27.
Proof. exact (fun h0 : term42 => @lem1901727 h0 h1). Qed.
Lemma lem1901729 : term29.
Proof. exact (fun h0 : term11 => @lem1901728 h0). Qed.
Lemma lem1901730 : term12.
Proof. exact (EQ_MP (@lem1900904) (@lem1901729)). Qed.
Lemma lem1901732 : term12.
Proof. exact (@lem1900759 (@lem1901730)). Qed.
Lemma lem1901733 (h1 : term11) : term26.
Proof. exact (@lem1901732 (@lem1900744 h1)). Qed.
Lemma lem1901734 (h1 : term11) : term23.
Proof. exact (@lem1901733 h1 (@lem1384343)). Qed.
Lemma lem1901735 (h1 : term11) : term20.
Proof. exact (@lem1901734 h1 (@lem1357243)). Qed.
Lemma lem1901736 (h1 : term11) : term16.
Proof. exact (@lem1901735 h1 (@lem1383497)). Qed.
Lemma lem1901737 (h1 : term11) : False.
Proof. exact (@lem1901736 h1 (@lem1900060)). Qed.
Lemma lem1901738 (h1 : term11) : term11 = False.
Proof. exact (prop_ext (fun h2 : term11 => @lem1901737 h1) (fun h2 : False => @lem1900744 h1)). Qed.
Lemma lem1901739 (h1 : term11) : False.
Proof. exact (EQ_MP (@lem1901738 h1) (@lem1900744 h1)). Qed.
Lemma lem1901740 : term10.
Proof. exact (fun h0 : term11 => @lem1901739 h0). Qed.
Lemma lem1901741 : term8 = term9.
Proof. exact (EQ_MP (@lem1900743) (@lem1901740)). Qed.
