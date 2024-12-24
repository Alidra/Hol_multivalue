Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_CONVEX_BOUND_GE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_ADD_RDISTRIB_spec.
Require Import REAL_CONVEX_BOUND2_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338986_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18940_spec.
Require Import thm18941_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1682773 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1682774 (u : real) (v : real) (a : real) : (term1 u v a) = (term2 u v a).
Proof. exact (@lem1682773 (term1 u v a)). Qed.
Lemma lem1682775 (u : real) (v : real) (a : real) : (term2 u v a) = (term1 u v a).
Proof. exact (SYM (@lem1682774 u v a)). Qed.
Lemma lem1682776 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term3 u v a.
Proof. exact (h1). Qed.
Lemma lem1682779 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term4 u v a.
Proof. exact (h1). Qed.
Lemma lem1682780 (u : real) (v : real) (a : real) : term5 u v a.
Proof. exact (fun h0 : term4 u v a => @lem1682779 u v a h0). Qed.
Lemma lem1682781 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (h1). Qed.
Lemma lem1682782 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term4 u v a.
Proof. exact (h1). Qed.
Lemma lem1682783 (u : real) (v : real) (a : real) (h1 : term4 u v a) (h2 : term5 u v a) : term4 u v a.
Proof. exact (@lem1682781 u v a h2 (@lem1682782 u v a h1)). Qed.
Lemma lem1682784 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term6 u v a.
Proof. exact (fun h0 : term5 u v a => @lem1682783 u v a h1 h0). Qed.
Lemma lem1682785 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (h1). Qed.
Lemma lem1682786 (u : real) (v : real) (a : real) (h1 : term4 u v a) (h2 : term5 u v a) : term4 u v a.
Proof. exact (@lem1682784 u v a h1 (@lem1682785 u v a h2)). Qed.
Lemma lem1682787 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (fun h0 : term4 u v a => @lem1682786 u v a h0 h1). Qed.
Lemma lem1682788 (u : real) (v : real) (a : real) : term7 u v a.
Proof. exact (fun h0 : term5 u v a => @lem1682787 u v a h0). Qed.
Lemma lem1682791 (u : real) (v : real) (a : real) : term5 u v a.
Proof. exact (@lem1682788 u v a (@lem1682780 u v a)). Qed.
Lemma lem1682823 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1682824 : term8 = term9.
Proof. exact (@lem1682823 term10). Qed.
Lemma lem1682829 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1682830 : term12 = term13.
Proof. exact (MK_COMB (@lem1682829) (@lem1682824)). Qed.
Lemma lem1682833 (u : real) (v : real) (a : real) : (term14 u v a) = (term14 u v a).
Proof. exact (eq_refl (term14 u v a)). Qed.
Lemma lem1682834 (u : real) (v : real) (a : real) : (term4 u v a) = (term15 u v a).
Proof. exact (MK_COMB (@lem1682833 u v a) (@lem1682830)). Qed.
Lemma lem1682837 (v : real) (a : real) : (term16 v a) = (term17 v a).
Proof. exact (fun_ext (fun u : real => @lem1682834 u v a)). Qed.
Lemma lem1682838 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1682839 (v : real) (a : real) : (term18 v a) = (term19 v a).
Proof. exact (MK_COMB (@lem1682838) (@lem1682837 v a)). Qed.
Lemma lem1682844 (a : real) : (term20 a) = (term21 a).
Proof. exact (fun_ext (fun v : real => @lem1682839 v a)). Qed.
Lemma lem1682845 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1682846 (a : real) : (term22 a) = (term23 a).
Proof. exact (MK_COMB (@lem1682845) (@lem1682844 a)). Qed.
Lemma lem1682851 : term24 = term25.
Proof. exact (fun_ext (fun a : real => @lem1682846 a)). Qed.
Lemma lem1682852 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1682861 : term26 = term27.
Proof. exact (MK_COMB (@lem1682852) (@lem1682851)). Qed.
Lemma lem1682862 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1682863 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1682862 x)). Qed.
Lemma lem1682864 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1682865 : term10 = term10.
Proof. exact (MK_COMB (@lem1682864) (@lem1682863)). Qed.
Lemma lem1682866 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1682867 : term9 = term9.
Proof. exact (MK_COMB (@lem1682866) (@lem1682865)). Qed.
Lemma lem1682868 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1682869 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1682868 x y z)). Qed.
Lemma lem1682870 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1682871 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1682870) (@lem1682869 x y)). Qed.
Lemma lem1682872 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1682871 x y)). Qed.
Lemma lem1682873 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1682874 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1682873) (@lem1682872 x)). Qed.
Lemma lem1682875 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1682874 x)). Qed.
Lemma lem1682876 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1682877 : term37 = term37.
Proof. exact (MK_COMB (@lem1682876) (@lem1682875)). Qed.
Lemma lem1682878 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1682879 : term11 = term11.
Proof. exact (MK_COMB (@lem1682878) (@lem1682877)). Qed.
Lemma lem1682880 : term13 = term13.
Proof. exact (MK_COMB (@lem1682879) (@lem1682867)). Qed.
Lemma lem1682889 (u : real) (v : real) (a : real) : (term14 u v a) = (term14 u v a).
Proof. exact (eq_refl (term14 u v a)). Qed.
Lemma lem1682890 (u : real) (v : real) (a : real) : (term15 u v a) = (term15 u v a).
Proof. exact (MK_COMB (@lem1682889 u v a) (@lem1682880)). Qed.
Lemma lem1682891 (v : real) (a : real) : (term17 v a) = (term17 v a).
Proof. exact (fun_ext (fun u : real => @lem1682890 u v a)). Qed.
Lemma lem1682892 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1682893 (v : real) (a : real) : (term19 v a) = (term19 v a).
Proof. exact (MK_COMB (@lem1682892) (@lem1682891 v a)). Qed.
Lemma lem1682894 (a : real) : (term21 a) = (term21 a).
Proof. exact (fun_ext (fun v : real => @lem1682893 v a)). Qed.
Lemma lem1682895 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1682896 (a : real) : (term23 a) = (term23 a).
Proof. exact (MK_COMB (@lem1682895) (@lem1682894 a)). Qed.
Lemma lem1682897 : term25 = term25.
Proof. exact (fun_ext (fun a : real => @lem1682896 a)). Qed.
Lemma lem1682898 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1682899 : term27 = term27.
Proof. exact (MK_COMB (@lem1682898) (@lem1682897)). Qed.
Lemma lem1682950 : term26 = term27.
Proof. exact (TRANS (@lem1682861) (@lem1682899)). Qed.
Lemma lem1682951 : term27 = term26.
Proof. exact (SYM (@lem1682950)). Qed.
Lemma lem1682952 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term3 u v a.
Proof. exact (h1). Qed.
Lemma lem1682953 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem1682954 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1682965 (u : real) (v : real) (a : real) : (term3 u v a) = (term38 u v a).
Proof. exact (@lem17362 ((real_add u v) = term39) ((term31 u v a) = a)). Qed.
Lemma lem1682967 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1682968 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1682967 x y z)). Qed.
Lemma lem1682969 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1682970 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1682969) (@lem1682968 x y)). Qed.
Lemma lem1682971 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1682970 x y)). Qed.
Lemma lem1682972 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1682973 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1682972) (@lem1682971 x)). Qed.
Lemma lem1682974 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1682973 x)). Qed.
Lemma lem1682975 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1682992 : term37 = term37.
Proof. exact (MK_COMB (@lem1682975) (@lem1682974)). Qed.
Lemma lem1682993 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1682992) (@lem1682953 h1)). Qed.
Lemma lem1682994 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1682995 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1682994 x)). Qed.
Lemma lem1682996 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683005 : term10 = term10.
Proof. exact (MK_COMB (@lem1682996) (@lem1682995)). Qed.
Lemma lem1683006 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1683005) (@lem1682954 h1)). Qed.
Lemma lem1683044 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term38 u v a.
Proof. exact (EQ_MP (@lem1682965 u v a) (@lem1682952 u v a h1)). Qed.
Lemma lem1683069 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1683070 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1683069 x y z)). Qed.
Lemma lem1683071 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683072 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1683071) (@lem1683070 x y)). Qed.
Lemma lem1683073 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1683072 x y)). Qed.
Lemma lem1683074 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683075 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1683074) (@lem1683073 x)). Qed.
Lemma lem1683076 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1683075 x)). Qed.
Lemma lem1683077 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683078 : term37 = term37.
Proof. exact (MK_COMB (@lem1683077) (@lem1683076)). Qed.
Lemma lem1683079 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1683078) (@lem1682993 h1)). Qed.
Lemma lem1683094 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1683095 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1683094 x)). Qed.
Lemma lem1683096 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683097 : term10 = term10.
Proof. exact (MK_COMB (@lem1683096) (@lem1683095)). Qed.
Lemma lem1683098 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1683097) (@lem1683006 h1)). Qed.
Lemma lem1683102 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1683103 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1683102 x y z)). Qed.
Lemma lem1683104 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683105 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1683104) (@lem1683103 x y)). Qed.
Lemma lem1683106 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1683105 x y)). Qed.
Lemma lem1683107 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683108 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1683107) (@lem1683106 x)). Qed.
Lemma lem1683109 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1683108 x)). Qed.
Lemma lem1683110 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683112 : term37 = term37.
Proof. exact (MK_COMB (@lem1683110) (@lem1683109)). Qed.
Lemma lem1683113 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1683112) (@lem1683079 h1)). Qed.
Lemma lem1683115 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1683116 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1683115 x)). Qed.
Lemma lem1683117 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683119 : term10 = term10.
Proof. exact (MK_COMB (@lem1683117) (@lem1683116)). Qed.
Lemma lem1683120 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1683119) (@lem1683098 h1)). Qed.
Lemma lem1683129 (_25960 : real) (h1 : term37) : term40 _25960.
Proof. exact (@lem1683113 h1 _25960). Qed.
Lemma lem1683130 (_25960 : real) : (term40 _25960) = (term35 _25960).
Proof. exact (eq_refl (term40 _25960)). Qed.
Lemma lem1683131 (_25960 : real) (h1 : term37) : term35 _25960.
Proof. exact (EQ_MP (@lem1683130 _25960) (@lem1683129 _25960 h1)). Qed.
Lemma lem1683132 (_25960 : real) (_25961 : real) (h1 : term37) : term41 _25960 _25961.
Proof. exact (@lem1683131 _25960 h1 _25961). Qed.
Lemma lem1683133 (_25960 : real) (_25961 : real) : (term41 _25960 _25961) = (term33 _25960 _25961).
Proof. exact (eq_refl (term41 _25960 _25961)). Qed.
Lemma lem1683134 (_25960 : real) (_25961 : real) (h1 : term37) : term33 _25960 _25961.
Proof. exact (EQ_MP (@lem1683133 _25960 _25961) (@lem1683132 _25960 _25961 h1)). Qed.
Lemma lem1683135 (_25960 : real) (_25961 : real) (_25962 : real) (h1 : term37) : term42 _25960 _25961 _25962.
Proof. exact (@lem1683134 _25960 _25961 h1 _25962). Qed.
Lemma lem1683136 (_25960 : real) (_25961 : real) (_25962 : real) : (term42 _25960 _25961 _25962) = ((term30 _25960 _25961 _25962) = (term31 _25960 _25961 _25962)).
Proof. exact (eq_refl (term42 _25960 _25961 _25962)). Qed.
Lemma lem1683138 (_25963 : real) (h1 : term10) : term43 _25963.
Proof. exact (@lem1683120 h1 _25963). Qed.
Lemma lem1683139 (_25963 : real) : (term43 _25963) = ((term28 _25963) = _25963).
Proof. exact (eq_refl (term43 _25963)). Qed.
Lemma lem1683148 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term44 u v a.
Proof. exact (proj2 (@lem1683044 u v a h1)). Qed.
Lemma lem1683173 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1683174 (_25970 : real) (_25972 : real) (h1 : _25970 = _25972) : _25970 = _25972.
Proof. exact (h1). Qed.
Lemma lem1683175 (_25971 : real) (_25973 : real) (h1 : _25971 = _25973) : _25971 = _25973.
Proof. exact (h1). Qed.
Lemma lem1683176 (_25970 : real) (_25972 : real) (h1 : _25970 = _25972) : (real_mul _25970) = (real_mul _25972).
Proof. exact (MK_COMB (@lem1683173) (@lem1683174 _25970 _25972 h1)). Qed.
Lemma lem1683177 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) (h1 : _25970 = _25972) (h2 : _25971 = _25973) : (real_mul _25970 _25971) = (real_mul _25972 _25973).
Proof. exact (MK_COMB (@lem1683176 _25970 _25972 h1) (@lem1683175 _25971 _25973 h2)). Qed.
Lemma lem1683178 (_25971 : real) (_25973 : real) (_25970 : real) (_25972 : real) (h1 : _25970 = _25972) : term45 _25970 _25971 _25972 _25973.
Proof. exact (fun h0 : _25971 = _25973 => @lem1683177 _25970 _25972 _25971 _25973 h1 h0). Qed.
Lemma lem1683180 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1683181 (_25970 : real) (_25971 : real) (_25972 : real) (_25973 : real) : (term45 _25970 _25971 _25972 _25973) = (term47 _25970 _25971 _25972 _25973).
Proof. exact (@lem1683180 (_25971 = _25973) ((real_mul _25970 _25971) = (real_mul _25972 _25973))). Qed.
Lemma lem1683182 (_25971 : real) (_25973 : real) (_25970 : real) (_25972 : real) (h1 : _25970 = _25972) : term47 _25970 _25971 _25972 _25973.
Proof. exact (EQ_MP (@lem1683181 _25970 _25971 _25972 _25973) (@lem1683178 _25971 _25973 _25970 _25972 h1)). Qed.
Lemma lem1683183 (_25970 : real) (_25971 : real) (_25972 : real) (_25973 : real) : term48 _25970 _25971 _25972 _25973.
Proof. exact (fun h0 : _25970 = _25972 => @lem1683182 _25971 _25973 _25970 _25972 h0). Qed.
Lemma lem1683185 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1683186 (_25970 : real) (_25971 : real) (_25972 : real) (_25973 : real) : (term48 _25970 _25971 _25972 _25973) = (term49 _25970 _25971 _25972 _25973).
Proof. exact (@lem1683185 (_25970 = _25972) (term47 _25970 _25971 _25972 _25973)). Qed.
Lemma lem1683187 (_25970 : real) (_25971 : real) (_25972 : real) (_25973 : real) : term49 _25970 _25971 _25972 _25973.
Proof. exact (EQ_MP (@lem1683186 _25970 _25971 _25972 _25973) (@lem1683183 _25970 _25971 _25972 _25973)). Qed.
Lemma lem1683204 (x : real) (y : real) (z : real) : term50 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1683208 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (real_add u v) = term39.
Proof. exact (proj1 (@lem1683044 u v a h1)). Qed.
Lemma lem1683209 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1683208 u v a h1). Qed.
Lemma lem1683211 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1683212 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1683211 ((real_add u v) = term39)). Qed.
Lemma lem1683213 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1683212 u v) (@lem1683209 u v a h1)). Qed.
Lemma lem1683215 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1683216 (a : real) : a = a.
Proof. exact (@lem1683215 a). Qed.
Lemma lem1683217 (a : real) : term54 a.
Proof. exact (fun h0 : term55 a => @lem1683216 a). Qed.
Lemma lem1683219 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1683220 (a : real) : (term54 a) = (a = a).
Proof. exact (@lem1683219 (a = a)). Qed.
Lemma lem1683221 (a : real) : a = a.
Proof. exact (EQ_MP (@lem1683220 a) (@lem1683217 a)). Qed.
Lemma lem1683239 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1683240 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) : (term47 _25970 _25971 _25972 _25973) = (term56 _25970 _25972 _25971 _25973).
Proof. exact (@lem1683239 ((real_mul _25970 _25971) = (real_mul _25972 _25973)) (term57 _25971 _25973)). Qed.
Lemma lem1683250 (_25970 : real) (_25972 : real) : (term58 _25970 _25972) = (term58 _25970 _25972).
Proof. exact (eq_refl (term58 _25970 _25972)). Qed.
Lemma lem1683251 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) : (term49 _25970 _25971 _25972 _25973) = (term59 _25970 _25972 _25971 _25973).
Proof. exact (MK_COMB (@lem1683250 _25970 _25972) (@lem1683240 _25970 _25972 _25971 _25973)). Qed.
Lemma lem1683255 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1683256 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) : (term59 _25970 _25972 _25971 _25973) = (term61 _25970 _25972 _25971 _25973).
Proof. exact (@lem1683255 ((real_mul _25970 _25971) = (real_mul _25972 _25973)) (term57 _25970 _25972) (term57 _25971 _25973)). Qed.
Lemma lem1683278 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) : (term49 _25970 _25971 _25972 _25973) = (term61 _25970 _25972 _25971 _25973).
Proof. exact (TRANS (@lem1683251 _25970 _25972 _25971 _25973) (@lem1683256 _25970 _25972 _25971 _25973)). Qed.
Lemma lem1683279 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1683280 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) : (term62 _25970 _25971 _25972 _25973) = (term63 _25970 _25972 _25971 _25973).
Proof. exact (MK_COMB (@lem1683279) (@lem1683278 _25970 _25972 _25971 _25973)). Qed.
Lemma lem1683302 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) : (term61 _25970 _25972 _25971 _25973) = (term61 _25970 _25972 _25971 _25973).
Proof. exact (eq_refl (term61 _25970 _25972 _25971 _25973)). Qed.
Lemma lem1683303 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) : ((term49 _25970 _25971 _25972 _25973) = (term61 _25970 _25972 _25971 _25973)) = ((term61 _25970 _25972 _25971 _25973) = (term61 _25970 _25972 _25971 _25973)).
Proof. exact (MK_COMB (@lem1683280 _25970 _25972 _25971 _25973) (@lem1683302 _25970 _25972 _25971 _25973)). Qed.
Lemma lem1683305 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1683306 (x : Prop) : (x = x) = True.
Proof. exact (@lem1683305 Prop x). Qed.
Lemma lem1683307 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) : ((term61 _25970 _25972 _25971 _25973) = (term61 _25970 _25972 _25971 _25973)) = True.
Proof. exact (@lem1683306 (term61 _25970 _25972 _25971 _25973)). Qed.
Lemma lem1683308 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) : ((term49 _25970 _25971 _25972 _25973) = (term61 _25970 _25972 _25971 _25973)) = True.
Proof. exact (TRANS (@lem1683303 _25970 _25972 _25971 _25973) (@lem1683307 _25970 _25972 _25971 _25973)). Qed.
Lemma lem1683309 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) : True = ((term49 _25970 _25971 _25972 _25973) = (term61 _25970 _25972 _25971 _25973)).
Proof. exact (SYM (@lem1683308 _25970 _25972 _25971 _25973)). Qed.
Lemma lem1683310 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) : (term49 _25970 _25971 _25972 _25973) = (term61 _25970 _25972 _25971 _25973).
Proof. exact (EQ_MP (@lem1683309 _25970 _25972 _25971 _25973) (@lem0)). Qed.
Lemma lem1683311 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) : term61 _25970 _25972 _25971 _25973.
Proof. exact (EQ_MP (@lem1683310 _25970 _25972 _25971 _25973) (@lem1683187 _25970 _25971 _25972 _25973)). Qed.
Lemma lem1683313 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1683314 (_25970 : real) (_25971 : real) (_25972 : real) (_25973 : real) : (term61 _25970 _25972 _25971 _25973) = (term65 _25970 _25971 _25972 _25973).
Proof. exact (@lem1683313 (term66 _25970 _25972 _25971 _25973) ((real_mul _25970 _25971) = (real_mul _25972 _25973))). Qed.
Lemma lem1683316 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1683317 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) : (term69 _25970 _25972 _25971 _25973) = (term70 _25970 _25972 _25971 _25973).
Proof. exact (@lem1683316 (term57 _25970 _25972) (term57 _25971 _25973)). Qed.
Lemma lem1683319 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1683320 (_25970 : real) (_25972 : real) : (term72 _25970 _25972) = (_25970 = _25972).
Proof. exact (@lem1683319 (_25970 = _25972)). Qed.
Lemma lem1683321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1683322 (_25970 : real) (_25972 : real) : (term73 _25970 _25972) = (term74 _25970 _25972).
Proof. exact (MK_COMB (@lem1683321) (@lem1683320 _25970 _25972)). Qed.
Lemma lem1683324 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1683325 (_25971 : real) (_25973 : real) : (term72 _25971 _25973) = (_25971 = _25973).
Proof. exact (@lem1683324 (_25971 = _25973)). Qed.
Lemma lem1683326 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) : (term70 _25970 _25972 _25971 _25973) = (term75 _25970 _25972 _25971 _25973).
Proof. exact (MK_COMB (@lem1683322 _25970 _25972) (@lem1683325 _25971 _25973)). Qed.
Lemma lem1683327 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) : (term69 _25970 _25972 _25971 _25973) = (term75 _25970 _25972 _25971 _25973).
Proof. exact (TRANS (@lem1683317 _25970 _25972 _25971 _25973) (@lem1683326 _25970 _25972 _25971 _25973)). Qed.
Lemma lem1683328 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1683329 (_25970 : real) (_25972 : real) (_25971 : real) (_25973 : real) : (term76 _25970 _25972 _25971 _25973) = (term77 _25970 _25972 _25971 _25973).
Proof. exact (MK_COMB (@lem1683328) (@lem1683327 _25970 _25972 _25971 _25973)). Qed.
Lemma lem1683330 (_25970 : real) (_25971 : real) (_25972 : real) (_25973 : real) : ((real_mul _25970 _25971) = (real_mul _25972 _25973)) = ((real_mul _25970 _25971) = (real_mul _25972 _25973)).
Proof. exact (eq_refl ((real_mul _25970 _25971) = (real_mul _25972 _25973))). Qed.
Lemma lem1683331 (_25970 : real) (_25971 : real) (_25972 : real) (_25973 : real) : (term65 _25970 _25971 _25972 _25973) = (term78 _25970 _25971 _25972 _25973).
Proof. exact (MK_COMB (@lem1683329 _25970 _25972 _25971 _25973) (@lem1683330 _25970 _25971 _25972 _25973)). Qed.
Lemma lem1683332 (_25970 : real) (_25971 : real) (_25972 : real) (_25973 : real) : (term61 _25970 _25972 _25971 _25973) = (term78 _25970 _25971 _25972 _25973).
Proof. exact (TRANS (@lem1683314 _25970 _25971 _25972 _25973) (@lem1683331 _25970 _25971 _25972 _25973)). Qed.
Lemma lem1683334 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term79 u v a.
Proof. exact (conj (@lem1683213 u v a h1) (@lem1683221 a)). Qed.
Lemma lem1683336 (_25970 : real) (_25971 : real) (_25972 : real) (_25973 : real) : term78 _25970 _25971 _25972 _25973.
Proof. exact (EQ_MP (@lem1683332 _25970 _25971 _25972 _25973) (@lem1683311 _25970 _25972 _25971 _25973)). Qed.
Lemma lem1683337 (u : real) (v : real) (a : real) : term80 u v a.
Proof. exact (@lem1683336 (real_add u v) a term39 a). Qed.
Lemma lem1683340 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term30 u v a) = (term28 a).
Proof. exact (@lem1683337 u v a (@lem1683334 u v a h1)). Qed.
Lemma lem1683341 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term81 u v a.
Proof. exact (fun h0 : term82 u v a => @lem1683340 u v a h1). Qed.
Lemma lem1683343 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1683344 (u : real) (v : real) (a : real) : (term81 u v a) = ((term30 u v a) = (term28 a)).
Proof. exact (@lem1683343 ((term30 u v a) = (term28 a))). Qed.
Lemma lem1683345 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term30 u v a) = (term28 a).
Proof. exact (EQ_MP (@lem1683344 u v a) (@lem1683341 u v a h1)). Qed.
Lemma lem1683347 (_25960 : real) (_25961 : real) (_25962 : real) (h1 : term37) : (term30 _25960 _25961 _25962) = (term31 _25960 _25961 _25962).
Proof. exact (EQ_MP (@lem1683136 _25960 _25961 _25962) (@lem1683135 _25960 _25961 _25962 h1)). Qed.
Lemma lem1683348 (u : real) (v : real) (a : real) (h1 : term37) : (term30 u v a) = (term31 u v a).
Proof. exact (@lem1683347 u v a h1). Qed.
Lemma lem1683349 (u : real) (v : real) (a : real) (h1 : term37) : term83 u v a.
Proof. exact (fun h0 : term84 u v a => @lem1683348 u v a h1). Qed.
Lemma lem1683351 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1683352 (u : real) (v : real) (a : real) : (term83 u v a) = ((term30 u v a) = (term31 u v a)).
Proof. exact (@lem1683351 ((term30 u v a) = (term31 u v a))). Qed.
Lemma lem1683353 (u : real) (v : real) (a : real) (h1 : term37) : (term30 u v a) = (term31 u v a).
Proof. exact (EQ_MP (@lem1683352 u v a) (@lem1683349 u v a h1)). Qed.
Lemma lem1683371 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1683372 (y : real) (x : real) (z : real) : (term85 x y z) = (term86 y x z).
Proof. exact (@lem1683371 (y = z) (term57 x z)). Qed.
Lemma lem1683382 (x : real) (y : real) : (term58 x y) = (term58 x y).
Proof. exact (eq_refl (term58 x y)). Qed.
Lemma lem1683383 (y : real) (x : real) (z : real) : (term50 x y z) = (term87 y x z).
Proof. exact (MK_COMB (@lem1683382 x y) (@lem1683372 y x z)). Qed.
Lemma lem1683387 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1683388 (y : real) (x : real) (z : real) : (term87 y x z) = (term88 y x z).
Proof. exact (@lem1683387 (y = z) (term57 x y) (term57 x z)). Qed.
Lemma lem1683410 (y : real) (x : real) (z : real) : (term50 x y z) = (term88 y x z).
Proof. exact (TRANS (@lem1683383 y x z) (@lem1683388 y x z)). Qed.
Lemma lem1683411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1683412 (y : real) (x : real) (z : real) : (term89 x y z) = (term90 y x z).
Proof. exact (MK_COMB (@lem1683411) (@lem1683410 y x z)). Qed.
Lemma lem1683434 (y : real) (x : real) (z : real) : (term88 y x z) = (term88 y x z).
Proof. exact (eq_refl (term88 y x z)). Qed.
Lemma lem1683435 (y : real) (x : real) (z : real) : ((term50 x y z) = (term88 y x z)) = ((term88 y x z) = (term88 y x z)).
Proof. exact (MK_COMB (@lem1683412 y x z) (@lem1683434 y x z)). Qed.
Lemma lem1683437 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1683438 (x : Prop) : (x = x) = True.
Proof. exact (@lem1683437 Prop x). Qed.
Lemma lem1683439 (y : real) (x : real) (z : real) : ((term88 y x z) = (term88 y x z)) = True.
Proof. exact (@lem1683438 (term88 y x z)). Qed.
Lemma lem1683440 (y : real) (x : real) (z : real) : ((term50 x y z) = (term88 y x z)) = True.
Proof. exact (TRANS (@lem1683435 y x z) (@lem1683439 y x z)). Qed.
Lemma lem1683441 (y : real) (x : real) (z : real) : True = ((term50 x y z) = (term88 y x z)).
Proof. exact (SYM (@lem1683440 y x z)). Qed.
Lemma lem1683442 (y : real) (x : real) (z : real) : (term50 x y z) = (term88 y x z).
Proof. exact (EQ_MP (@lem1683441 y x z) (@lem0)). Qed.
Lemma lem1683443 (y : real) (x : real) (z : real) : term88 y x z.
Proof. exact (EQ_MP (@lem1683442 y x z) (@lem1683204 x y z)). Qed.
Lemma lem1683445 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1683446 (x : real) (y : real) (z : real) : (term88 y x z) = (term91 x y z).
Proof. exact (@lem1683445 (term92 y x z) (y = z)). Qed.
Lemma lem1683448 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1683449 (y : real) (x : real) (z : real) : (term93 y x z) = (term94 y x z).
Proof. exact (@lem1683448 (term57 x y) (term57 x z)). Qed.
Lemma lem1683451 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1683452 (x : real) (y : real) : (term72 x y) = (x = y).
Proof. exact (@lem1683451 (x = y)). Qed.
Lemma lem1683453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1683454 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1683453) (@lem1683452 x y)). Qed.
Lemma lem1683456 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1683457 (x : real) (z : real) : (term72 x z) = (x = z).
Proof. exact (@lem1683456 (x = z)). Qed.
Lemma lem1683458 (y : real) (x : real) (z : real) : (term94 y x z) = (term95 y x z).
Proof. exact (MK_COMB (@lem1683454 x y) (@lem1683457 x z)). Qed.
Lemma lem1683459 (y : real) (x : real) (z : real) : (term93 y x z) = (term95 y x z).
Proof. exact (TRANS (@lem1683449 y x z) (@lem1683458 y x z)). Qed.
Lemma lem1683460 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1683461 (y : real) (x : real) (z : real) : (term96 y x z) = (term97 y x z).
Proof. exact (MK_COMB (@lem1683460) (@lem1683459 y x z)). Qed.
Lemma lem1683462 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1683463 (x : real) (y : real) (z : real) : (term91 x y z) = (term98 x y z).
Proof. exact (MK_COMB (@lem1683461 y x z) (@lem1683462 y z)). Qed.
Lemma lem1683464 (x : real) (y : real) (z : real) : (term88 y x z) = (term98 x y z).
Proof. exact (TRANS (@lem1683446 x y z) (@lem1683463 x y z)). Qed.
Lemma lem1683466 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term99 u v a.
Proof. exact (conj (@lem1683345 u v a h2) (@lem1683353 u v a h1)). Qed.
Lemma lem1683468 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (EQ_MP (@lem1683464 x y z) (@lem1683443 y x z)). Qed.
Lemma lem1683469 (u : real) (v : real) (a : real) : term100 u v a.
Proof. exact (@lem1683468 (term30 u v a) (term28 a) (term31 u v a)). Qed.
Lemma lem1683472 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : (term28 a) = (term31 u v a).
Proof. exact (@lem1683469 u v a (@lem1683466 u v a h1 h2)). Qed.
Lemma lem1683473 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term101 u v a.
Proof. exact (fun h0 : term102 u v a => @lem1683472 u v a h1 h2). Qed.
Lemma lem1683475 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1683476 (u : real) (v : real) (a : real) : (term101 u v a) = ((term28 a) = (term31 u v a)).
Proof. exact (@lem1683475 ((term28 a) = (term31 u v a))). Qed.
Lemma lem1683477 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : (term28 a) = (term31 u v a).
Proof. exact (EQ_MP (@lem1683476 u v a) (@lem1683473 u v a h1 h2)). Qed.
Lemma lem1683479 (_25963 : real) (h1 : term10) : (term28 _25963) = _25963.
Proof. exact (EQ_MP (@lem1683139 _25963) (@lem1683138 _25963 h1)). Qed.
Lemma lem1683480 (a : real) (h1 : term10) : (term28 a) = a.
Proof. exact (@lem1683479 a h1). Qed.
Lemma lem1683481 (a : real) (h1 : term10) : term103 a.
Proof. exact (fun h0 : term104 a => @lem1683480 a h1). Qed.
Lemma lem1683483 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1683484 (a : real) : (term103 a) = ((term28 a) = a).
Proof. exact (@lem1683483 ((term28 a) = a)). Qed.
Lemma lem1683485 (a : real) (h1 : term10) : (term28 a) = a.
Proof. exact (EQ_MP (@lem1683484 a) (@lem1683481 a h1)). Qed.
Lemma lem1683486 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term105 u v a.
Proof. exact (conj (@lem1683477 u v a h1 h3) (@lem1683485 a h2)). Qed.
Lemma lem1683488 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (EQ_MP (@lem1683464 x y z) (@lem1683443 y x z)). Qed.
Lemma lem1683489 (u : real) (v : real) (a : real) : term106 u v a.
Proof. exact (@lem1683488 (term28 a) (term31 u v a) a). Qed.
Lemma lem1683492 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : (term31 u v a) = a.
Proof. exact (@lem1683489 u v a (@lem1683486 u v a h1 h2 h3)). Qed.
Lemma lem1683493 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term107 u v a.
Proof. exact (fun h0 : term44 u v a => @lem1683492 u v a h1 h2 h3). Qed.
Lemma lem1683495 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1683496 (u : real) (v : real) (a : real) : (term107 u v a) = ((term31 u v a) = a).
Proof. exact (@lem1683495 ((term31 u v a) = a)). Qed.
Lemma lem1683497 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : (term31 u v a) = a.
Proof. exact (EQ_MP (@lem1683496 u v a) (@lem1683493 u v a h1 h2 h3)). Qed.
Lemma lem1683500 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1683502 (u : real) (v : real) (a : real) : (term44 u v a) = (term108 u v a).
Proof. exact (@lem1683500 ((term31 u v a) = a)). Qed.
Lemma lem1683505 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term108 u v a.
Proof. exact (EQ_MP (@lem1683502 u v a) (@lem1683148 u v a h1)). Qed.
Lemma lem1683508 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (@lem1683505 u v a h3 (@lem1683497 u v a h1 h2 h3)). Qed.
Lemma lem1683509 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term109.
Proof. exact (fun h0 : ~ False => @lem1683508 u v a h1 h2 h3). Qed.
Lemma lem1683511 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1683512 : term109 = False.
Proof. exact (@lem1683511 False). Qed.
Lemma lem1683513 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1683512) (@lem1683509 u v a h1 h2 h3)). Qed.
Lemma lem1683514 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1683513 u v a h1 h2 h3) (fun h4 : False => @lem1683120 h2)). Qed.
Lemma lem1683515 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1683514 u v a h1 h2 h3) (@lem1683120 h2)). Qed.
Lemma lem1683516 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1683515 u v a h1 h2 h3) (fun h4 : False => @lem1683113 h1)). Qed.
Lemma lem1683517 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1683516 u v a h1 h2 h3) (@lem1683113 h1)). Qed.
Lemma lem1683518 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1683517 u v a h1 h2 h3) (fun h4 : False => @lem1683098 h2)). Qed.
Lemma lem1683519 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1683518 u v a h1 h2 h3) (@lem1683098 h2)). Qed.
Lemma lem1683520 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1683519 u v a h1 h2 h3) (fun h4 : False => @lem1683079 h1)). Qed.
Lemma lem1683521 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1683520 u v a h1 h2 h3) (@lem1683079 h1)). Qed.
Lemma lem1683522 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1683521 u v a h1 h2 h3) (fun h4 : False => @lem1683006 h2)). Qed.
Lemma lem1683523 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1683522 u v a h1 h2 h3) (@lem1683006 h2)). Qed.
Lemma lem1683524 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1683523 u v a h1 h2 h3) (fun h4 : False => @lem1682993 h1)). Qed.
Lemma lem1683525 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1683524 u v a h1 h2 h3) (@lem1682993 h1)). Qed.
Lemma lem1683526 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term8.
Proof. exact (fun h0 : term10 => @lem1683525 u v a h1 h0 h2). Qed.
Lemma lem1683527 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1683528 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term9.
Proof. exact (EQ_MP (@lem1683527) (@lem1683526 u v a h1 h2)). Qed.
Lemma lem1683529 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term13.
Proof. exact (fun h0 : term37 => @lem1683528 u v a h0 h1). Qed.
Lemma lem1683530 (u : real) (v : real) (a : real) : term15 u v a.
Proof. exact (fun h0 : term3 u v a => @lem1683529 u v a h0). Qed.
Lemma lem1683535 (v : real) (a : real) : term19 v a.
Proof. exact (fun u : real => @lem1683530 u v a). Qed.
Lemma lem1683540 (a : real) : term23 a.
Proof. exact (fun v : real => @lem1683535 v a). Qed.
Lemma lem1683545 : term27.
Proof. exact (fun a : real => @lem1683540 a). Qed.
Lemma lem1683546 : term26.
Proof. exact (EQ_MP (@lem1682951) (@lem1683545)). Qed.
Lemma lem1683547 (a : real) : term110 a.
Proof. exact (@lem1683546 a). Qed.
Lemma lem1683548 (a : real) : (term110 a) = (term22 a).
Proof. exact (eq_refl (term110 a)). Qed.
Lemma lem1683549 (a : real) : term22 a.
Proof. exact (EQ_MP (@lem1683548 a) (@lem1683547 a)). Qed.
Lemma lem1683550 (a : real) (v : real) : term111 a v.
Proof. exact (@lem1683549 a v). Qed.
Lemma lem1683551 (v : real) (a : real) : (term111 a v) = (term18 v a).
Proof. exact (eq_refl (term111 a v)). Qed.
Lemma lem1683552 (v : real) (a : real) : term18 v a.
Proof. exact (EQ_MP (@lem1683551 v a) (@lem1683550 a v)). Qed.
Lemma lem1683553 (v : real) (a : real) (u : real) : term112 v a u.
Proof. exact (@lem1683552 v a u). Qed.
Lemma lem1683554 (u : real) (v : real) (a : real) : (term112 v a u) = (term4 u v a).
Proof. exact (eq_refl (term112 v a u)). Qed.
Lemma lem1683555 (u : real) (v : real) (a : real) : term4 u v a.
Proof. exact (EQ_MP (@lem1683554 u v a) (@lem1683553 v a u)). Qed.
Lemma lem1683557 (u : real) (v : real) (a : real) : term4 u v a.
Proof. exact (@lem1682791 u v a (@lem1683555 u v a)). Qed.
Lemma lem1683558 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term12.
Proof. exact (@lem1683557 u v a (@lem1682776 u v a h1)). Qed.
Lemma lem1683559 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term8.
Proof. exact (@lem1683558 u v a h1 (@lem1487144)). Qed.
Lemma lem1683560 (u : real) (v : real) (a : real) (h1 : term3 u v a) : False.
Proof. exact (@lem1683559 u v a h1 (@lem1338986)). Qed.
Lemma lem1683561 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term3 u v a) = False.
Proof. exact (prop_ext (fun h2 : term3 u v a => @lem1683560 u v a h1) (fun h2 : False => @lem1682776 u v a h1)). Qed.
Lemma lem1683562 (u : real) (v : real) (a : real) (h1 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1683561 u v a h1) (@lem1682776 u v a h1)). Qed.
Lemma lem1683563 (u : real) (v : real) (a : real) : term2 u v a.
Proof. exact (fun h0 : term3 u v a => @lem1683562 u v a h0). Qed.
Lemma lem1683564 (u : real) (v : real) (a : real) : term1 u v a.
Proof. exact (EQ_MP (@lem1682775 u v a) (@lem1683563 u v a)). Qed.
Lemma lem1683565 (t1 : Prop) : term113 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1683566 (t1 : Prop) : (term113 t1) = (term114 t1).
Proof. exact (eq_refl (term113 t1)). Qed.
Lemma lem1683567 (t1 : Prop) : term114 t1.
Proof. exact (EQ_MP (@lem1683566 t1) (@lem1683565 t1)). Qed.
Lemma lem1683568 (t1 : Prop) (t2 : Prop) : term115 t1 t2.
Proof. exact (@lem1683567 t1 t2). Qed.
Lemma lem1683569 (t1 : Prop) (t2 : Prop) : (term115 t1 t2) = (term116 t1 t2).
Proof. exact (eq_refl (term115 t1 t2)). Qed.
Lemma lem1683570 (t1 : Prop) (t2 : Prop) : term116 t1 t2.
Proof. exact (EQ_MP (@lem1683569 t1 t2) (@lem1683568 t1 t2)). Qed.
Lemma lem1683571 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term117 t1 t2 t3.
Proof. exact (@lem1683570 t1 t2 t3). Qed.
Lemma lem1683572 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term117 t1 t2 t3) = ((term60 t1 t2 t3) = (term118 t1 t2 t3)).
Proof. exact (eq_refl (term117 t1 t2 t3)). Qed.
Lemma lem1683573 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term60 t1 t2 t3) = (term118 t1 t2 t3).
Proof. exact (EQ_MP (@lem1683572 t1 t2 t3) (@lem1683571 t1 t2 t3)). Qed.
Lemma lem1683574 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term118 t1 t2 t3) = (term60 t1 t2 t3).
Proof. exact (SYM (@lem1683573 t1 t2 t3)). Qed.
Lemma lem1683575 : term119.
Proof. exact (fun b : real => @lem1673888 b). Qed.
Lemma lem1683576 (u : real) (v : real) : term120 u v.
Proof. exact (fun a : real => @lem1683564 u v a). Qed.
Lemma lem1683577 (u : real) : term121 u.
Proof. exact (fun v : real => @lem1683576 u v). Qed.
Lemma lem1683578 : term122.
Proof. exact (fun u : real => @lem1683577 u). Qed.
Lemma lem1683580 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1683581 : term123 = term124.
Proof. exact (@lem1683580 term123). Qed.
Lemma lem1683582 : term124 = term123.
Proof. exact (SYM (@lem1683581)). Qed.
Lemma lem1683583 (h1 : term125) : term125.
Proof. exact (h1). Qed.
Lemma lem1683586 (h1 : term126) : term126.
Proof. exact (h1). Qed.
Lemma lem1683587 : term127.
Proof. exact (fun h0 : term126 => @lem1683586 h0). Qed.
Lemma lem1683588 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem1683589 (h1 : term126) : term126.
Proof. exact (h1). Qed.
Lemma lem1683590 (h1 : term126) (h2 : term127) : term126.
Proof. exact (@lem1683588 h2 (@lem1683589 h1)). Qed.
Lemma lem1683591 (h1 : term126) : term128.
Proof. exact (fun h0 : term127 => @lem1683590 h1 h0). Qed.
Lemma lem1683592 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem1683593 (h1 : term126) (h2 : term127) : term126.
Proof. exact (@lem1683591 h1 (@lem1683592 h2)). Qed.
Lemma lem1683594 (h1 : term127) : term127.
Proof. exact (fun h0 : term126 => @lem1683593 h0 h1). Qed.
Lemma lem1683595 : term129.
Proof. exact (fun h0 : term127 => @lem1683594 h0). Qed.
Lemma lem1683598 : term127.
Proof. exact (@lem1683595 (@lem1683587)). Qed.
Lemma lem1683648 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1683649 : term130 = term131.
Proof. exact (@lem1683648 term119). Qed.
Lemma lem1683684 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem1683685 : term133 = term134.
Proof. exact (MK_COMB (@lem1683684) (@lem1683649)). Qed.
Lemma lem1683688 : term135 = term135.
Proof. exact (eq_refl term135). Qed.
Lemma lem1683695 : term126 = term136.
Proof. exact (MK_COMB (@lem1683688) (@lem1683685)). Qed.
Lemma lem1683716 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term137 x y u a v b).
Proof. exact (eq_refl (term137 x y u a v b)). Qed.
Lemma lem1683717 (x : real) (y : real) (u : real) (a : real) (b : real) : (term138 x y u a b) = (term138 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1683716 x y u a v b)). Qed.
Lemma lem1683718 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683719 (x : real) (y : real) (u : real) (a : real) (b : real) : (term139 x y u a b) = (term139 x y u a b).
Proof. exact (MK_COMB (@lem1683718) (@lem1683717 x y u a b)). Qed.
Lemma lem1683720 (x : real) (y : real) (a : real) (b : real) : (term140 x y a b) = (term140 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1683719 x y u a b)). Qed.
Lemma lem1683721 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683722 (x : real) (y : real) (a : real) (b : real) : (term141 x y a b) = (term141 x y a b).
Proof. exact (MK_COMB (@lem1683721) (@lem1683720 x y a b)). Qed.
Lemma lem1683723 (x : real) (y : real) (b : real) : (term142 x y b) = (term142 x y b).
Proof. exact (fun_ext (fun a : real => @lem1683722 x y a b)). Qed.
Lemma lem1683724 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683725 (x : real) (y : real) (b : real) : (term143 x y b) = (term143 x y b).
Proof. exact (MK_COMB (@lem1683724) (@lem1683723 x y b)). Qed.
Lemma lem1683726 (x : real) (b : real) : (term144 x b) = (term144 x b).
Proof. exact (fun_ext (fun y : real => @lem1683725 x y b)). Qed.
Lemma lem1683727 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683728 (x : real) (b : real) : (term145 x b) = (term145 x b).
Proof. exact (MK_COMB (@lem1683727) (@lem1683726 x b)). Qed.
Lemma lem1683729 (b : real) : (term146 b) = (term146 b).
Proof. exact (fun_ext (fun x : real => @lem1683728 x b)). Qed.
Lemma lem1683730 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683731 (b : real) : (term147 b) = (term147 b).
Proof. exact (MK_COMB (@lem1683730) (@lem1683729 b)). Qed.
Lemma lem1683732 : term148 = term148.
Proof. exact (fun_ext (fun b : real => @lem1683731 b)). Qed.
Lemma lem1683733 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683734 : term119 = term119.
Proof. exact (MK_COMB (@lem1683733) (@lem1683732)). Qed.
Lemma lem1683735 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1683736 : term131 = term131.
Proof. exact (MK_COMB (@lem1683735) (@lem1683734)). Qed.
Lemma lem1683741 (u : real) (v : real) (a : real) : (term1 u v a) = (term1 u v a).
Proof. exact (eq_refl (term1 u v a)). Qed.
Lemma lem1683742 (u : real) (v : real) : (term149 u v) = (term149 u v).
Proof. exact (fun_ext (fun a : real => @lem1683741 u v a)). Qed.
Lemma lem1683743 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683744 (u : real) (v : real) : (term120 u v) = (term120 u v).
Proof. exact (MK_COMB (@lem1683743) (@lem1683742 u v)). Qed.
Lemma lem1683745 (u : real) : (term150 u) = (term150 u).
Proof. exact (fun_ext (fun v : real => @lem1683744 u v)). Qed.
Lemma lem1683746 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683747 (u : real) : (term121 u) = (term121 u).
Proof. exact (MK_COMB (@lem1683746) (@lem1683745 u)). Qed.
Lemma lem1683748 : term151 = term151.
Proof. exact (fun_ext (fun u : real => @lem1683747 u)). Qed.
Lemma lem1683749 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683750 : term122 = term122.
Proof. exact (MK_COMB (@lem1683749) (@lem1683748)). Qed.
Lemma lem1683751 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1683752 : term132 = term132.
Proof. exact (MK_COMB (@lem1683751) (@lem1683750)). Qed.
Lemma lem1683753 : term134 = term134.
Proof. exact (MK_COMB (@lem1683752) (@lem1683736)). Qed.
Lemma lem1683774 (a : real) (u : real) (x : real) (v : real) (y : real) : (term152 a u x v y) = (term152 a u x v y).
Proof. exact (eq_refl (term152 a u x v y)). Qed.
Lemma lem1683775 (a : real) (u : real) (x : real) (y : real) : (term153 a u x y) = (term153 a u x y).
Proof. exact (fun_ext (fun v : real => @lem1683774 a u x v y)). Qed.
Lemma lem1683776 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683777 (a : real) (u : real) (x : real) (y : real) : (term154 a u x y) = (term154 a u x y).
Proof. exact (MK_COMB (@lem1683776) (@lem1683775 a u x y)). Qed.
Lemma lem1683778 (a : real) (x : real) (y : real) : (term155 a x y) = (term155 a x y).
Proof. exact (fun_ext (fun u : real => @lem1683777 a u x y)). Qed.
Lemma lem1683779 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683780 (a : real) (x : real) (y : real) : (term156 a x y) = (term156 a x y).
Proof. exact (MK_COMB (@lem1683779) (@lem1683778 a x y)). Qed.
Lemma lem1683781 (x : real) (y : real) : (term157 x y) = (term157 x y).
Proof. exact (fun_ext (fun a : real => @lem1683780 a x y)). Qed.
Lemma lem1683782 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683783 (x : real) (y : real) : (term158 x y) = (term158 x y).
Proof. exact (MK_COMB (@lem1683782) (@lem1683781 x y)). Qed.
Lemma lem1683784 (x : real) : (term159 x) = (term159 x).
Proof. exact (fun_ext (fun y : real => @lem1683783 x y)). Qed.
Lemma lem1683785 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683786 (x : real) : (term160 x) = (term160 x).
Proof. exact (MK_COMB (@lem1683785) (@lem1683784 x)). Qed.
Lemma lem1683787 : term161 = term161.
Proof. exact (fun_ext (fun x : real => @lem1683786 x)). Qed.
Lemma lem1683788 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1683789 : term123 = term123.
Proof. exact (MK_COMB (@lem1683788) (@lem1683787)). Qed.
Lemma lem1683790 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1683791 : term125 = term125.
Proof. exact (MK_COMB (@lem1683790) (@lem1683789)). Qed.
Lemma lem1683792 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1683793 : term135 = term135.
Proof. exact (MK_COMB (@lem1683792) (@lem1683791)). Qed.
Lemma lem1683794 : term136 = term136.
Proof. exact (MK_COMB (@lem1683793) (@lem1683753)). Qed.
Lemma lem1683907 : term126 = term136.
Proof. exact (TRANS (@lem1683695) (@lem1683794)). Qed.
Lemma lem1683908 : term136 = term126.
Proof. exact (SYM (@lem1683907)). Qed.
Lemma lem1683909 (h1 : term125) : term125.
Proof. exact (h1). Qed.
Lemma lem1683910 (h1 : term122) : term122.
Proof. exact (h1). Qed.
Lemma lem1683911 (h1 : term119) : term119.
Proof. exact (h1). Qed.
Lemma lem1683934 (a : real) (u : real) (x : real) (v : real) (y : real) : (term162 a u x v y) = (term163 a u x v y).
Proof. exact (@lem17362 (term164 x a y u v) (term165 a u x v y)). Qed.
Lemma lem1683935 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1683936 (a : real) (u : real) (x : real) (y : real) : (term168 a u x y) = (term169 a u x y).
Proof. exact (@lem1683935 (term153 a u x y)). Qed.
Lemma lem1683937 (a : real) (u : real) (x : real) (v : real) (y : real) : (term170 a u x y v) = (term152 a u x v y).
Proof. exact (eq_refl (term170 a u x y v)). Qed.
Lemma lem1683938 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1683939 (a : real) (u : real) (x : real) (v : real) (y : real) : (term171 a u x y v) = (term162 a u x v y).
Proof. exact (MK_COMB (@lem1683938) (@lem1683937 a u x v y)). Qed.
Lemma lem1683940 (a : real) (u : real) (x : real) (v : real) (y : real) : (term171 a u x y v) = (term163 a u x v y).
Proof. exact (TRANS (@lem1683939 a u x v y) (@lem1683934 a u x v y)). Qed.
Lemma lem1683941 (a : real) (u : real) (x : real) (y : real) : (term172 a u x y) = (term173 a u x y).
Proof. exact (fun_ext (fun v : real => @lem1683940 a u x v y)). Qed.
Lemma lem1683942 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1683943 (a : real) (u : real) (x : real) (y : real) : (term169 a u x y) = (term174 a u x y).
Proof. exact (MK_COMB (@lem1683942) (@lem1683941 a u x y)). Qed.
Lemma lem1683944 (a : real) (u : real) (x : real) (y : real) : (term168 a u x y) = (term174 a u x y).
Proof. exact (TRANS (@lem1683936 a u x y) (@lem1683943 a u x y)). Qed.
Lemma lem1683945 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1683946 (a : real) (x : real) (y : real) : (term175 a x y) = (term176 a x y).
Proof. exact (@lem1683945 (term155 a x y)). Qed.
Lemma lem1683947 (a : real) (u : real) (x : real) (y : real) : (term177 a x y u) = (term154 a u x y).
Proof. exact (eq_refl (term177 a x y u)). Qed.
Lemma lem1683948 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1683949 (a : real) (u : real) (x : real) (y : real) : (term178 a x y u) = (term168 a u x y).
Proof. exact (MK_COMB (@lem1683948) (@lem1683947 a u x y)). Qed.
Lemma lem1683950 (a : real) (u : real) (x : real) (y : real) : (term178 a x y u) = (term174 a u x y).
Proof. exact (TRANS (@lem1683949 a u x y) (@lem1683944 a u x y)). Qed.
Lemma lem1683951 (a : real) (x : real) (y : real) : (term179 a x y) = (term180 a x y).
Proof. exact (fun_ext (fun u : real => @lem1683950 a u x y)). Qed.
Lemma lem1683952 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1683953 (a : real) (x : real) (y : real) : (term176 a x y) = (term181 a x y).
Proof. exact (MK_COMB (@lem1683952) (@lem1683951 a x y)). Qed.
Lemma lem1683954 (a : real) (x : real) (y : real) : (term175 a x y) = (term181 a x y).
Proof. exact (TRANS (@lem1683946 a x y) (@lem1683953 a x y)). Qed.
Lemma lem1683955 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1683956 (x : real) (y : real) : (term182 x y) = (term183 x y).
Proof. exact (@lem1683955 (term157 x y)). Qed.
Lemma lem1683957 (a : real) (x : real) (y : real) : (term184 x y a) = (term156 a x y).
Proof. exact (eq_refl (term184 x y a)). Qed.
Lemma lem1683958 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1683959 (a : real) (x : real) (y : real) : (term185 x y a) = (term175 a x y).
Proof. exact (MK_COMB (@lem1683958) (@lem1683957 a x y)). Qed.
Lemma lem1683960 (a : real) (x : real) (y : real) : (term185 x y a) = (term181 a x y).
Proof. exact (TRANS (@lem1683959 a x y) (@lem1683954 a x y)). Qed.
Lemma lem1683961 (x : real) (y : real) : (term186 x y) = (term187 x y).
Proof. exact (fun_ext (fun a : real => @lem1683960 a x y)). Qed.
Lemma lem1683962 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1683963 (x : real) (y : real) : (term183 x y) = (term188 x y).
Proof. exact (MK_COMB (@lem1683962) (@lem1683961 x y)). Qed.
Lemma lem1683964 (x : real) (y : real) : (term182 x y) = (term188 x y).
Proof. exact (TRANS (@lem1683956 x y) (@lem1683963 x y)). Qed.
Lemma lem1683965 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1683966 (x : real) : (term189 x) = (term190 x).
Proof. exact (@lem1683965 (term159 x)). Qed.
Lemma lem1683967 (x : real) (y : real) : (term191 x y) = (term158 x y).
Proof. exact (eq_refl (term191 x y)). Qed.
Lemma lem1683968 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1683969 (x : real) (y : real) : (term192 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1683968) (@lem1683967 x y)). Qed.
Lemma lem1683970 (x : real) (y : real) : (term192 x y) = (term188 x y).
Proof. exact (TRANS (@lem1683969 x y) (@lem1683964 x y)). Qed.
Lemma lem1683971 (x : real) : (term193 x) = (term194 x).
Proof. exact (fun_ext (fun y : real => @lem1683970 x y)). Qed.
Lemma lem1683972 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1683973 (x : real) : (term190 x) = (term195 x).
Proof. exact (MK_COMB (@lem1683972) (@lem1683971 x)). Qed.
Lemma lem1683974 (x : real) : (term189 x) = (term195 x).
Proof. exact (TRANS (@lem1683966 x) (@lem1683973 x)). Qed.
Lemma lem1683975 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1683976 : term125 = term196.
Proof. exact (@lem1683975 term161). Qed.
Lemma lem1683977 (x : real) : (term197 x) = (term160 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem1683978 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1683979 (x : real) : (term198 x) = (term189 x).
Proof. exact (MK_COMB (@lem1683978) (@lem1683977 x)). Qed.
Lemma lem1683980 (x : real) : (term198 x) = (term195 x).
Proof. exact (TRANS (@lem1683979 x) (@lem1683974 x)). Qed.
Lemma lem1683981 : term199 = term200.
Proof. exact (fun_ext (fun x : real => @lem1683980 x)). Qed.
Lemma lem1683982 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1683983 : term196 = term201.
Proof. exact (MK_COMB (@lem1683982) (@lem1683981)). Qed.
Lemma lem1684052 : term125 = term201.
Proof. exact (TRANS (@lem1683976) (@lem1683983)). Qed.
Lemma lem1684053 (h1 : term125) : term201.
Proof. exact (EQ_MP (@lem1684052) (@lem1683909 h1)). Qed.
Lemma lem1684060 (u : real) (v : real) (a : real) : (term1 u v a) = (term202 u v a).
Proof. exact (@lem17265 ((real_add u v) = term39) ((term31 u v a) = a)). Qed.
Lemma lem1684061 (u : real) (v : real) : (term149 u v) = (term203 u v).
Proof. exact (fun_ext (fun a : real => @lem1684060 u v a)). Qed.
Lemma lem1684062 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684063 (u : real) (v : real) : (term120 u v) = (term204 u v).
Proof. exact (MK_COMB (@lem1684062) (@lem1684061 u v)). Qed.
Lemma lem1684064 (u : real) : (term150 u) = (term205 u).
Proof. exact (fun_ext (fun v : real => @lem1684063 u v)). Qed.
Lemma lem1684065 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684066 (u : real) : (term121 u) = (term206 u).
Proof. exact (MK_COMB (@lem1684065) (@lem1684064 u)). Qed.
Lemma lem1684067 : term151 = term207.
Proof. exact (fun_ext (fun u : real => @lem1684066 u)). Qed.
Lemma lem1684068 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684069 : term122 = term208.
Proof. exact (MK_COMB (@lem1684068) (@lem1684067)). Qed.
Lemma lem1684079 {A : Type'} (P : Prop) (Q : A -> Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem1684080 (P : Prop) (Q : real -> Prop) : (term211 P Q) = (term212 P Q).
Proof. exact (@lem1684079 real P Q). Qed.
Lemma lem1684081 (u : real) (v : real) : (term213 u v) = (term214 u v).
Proof. exact (@lem1684080 (term52 u v) (term215 u v)). Qed.
Lemma lem1684082 (u : real) (v : real) (a : real) : (term216 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term216 u v a)). Qed.
Lemma lem1684083 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1684084 (u : real) (v : real) (a : real) : (term218 u v a) = (term202 u v a).
Proof. exact (MK_COMB (@lem1684083 u v) (@lem1684082 u v a)). Qed.
Lemma lem1684085 (u : real) (v : real) : (term219 u v) = (term203 u v).
Proof. exact (fun_ext (fun a : real => @lem1684084 u v a)). Qed.
Lemma lem1684086 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684087 (u : real) (v : real) : (term213 u v) = (term204 u v).
Proof. exact (MK_COMB (@lem1684086) (@lem1684085 u v)). Qed.
Lemma lem1684088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1684089 (u : real) (v : real) : (term220 u v) = (term221 u v).
Proof. exact (MK_COMB (@lem1684088) (@lem1684087 u v)). Qed.
Lemma lem1684090 (u : real) (v : real) (a : real) : (term216 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term216 u v a)). Qed.
Lemma lem1684091 (u : real) (v : real) : (term222 u v) = (term215 u v).
Proof. exact (fun_ext (fun a : real => @lem1684090 u v a)). Qed.
Lemma lem1684092 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684093 (u : real) (v : real) : (term223 u v) = (term224 u v).
Proof. exact (MK_COMB (@lem1684092) (@lem1684091 u v)). Qed.
Lemma lem1684094 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1684095 (u : real) (v : real) : (term214 u v) = (term225 u v).
Proof. exact (MK_COMB (@lem1684094 u v) (@lem1684093 u v)). Qed.
Lemma lem1684096 (u : real) (v : real) : ((term213 u v) = (term214 u v)) = ((term204 u v) = (term225 u v)).
Proof. exact (MK_COMB (@lem1684089 u v) (@lem1684095 u v)). Qed.
Lemma lem1684097 (u : real) (v : real) : (term204 u v) = (term225 u v).
Proof. exact (EQ_MP (@lem1684096 u v) (@lem1684081 u v)). Qed.
Lemma lem1684102 (u : real) : (term205 u) = (term226 u).
Proof. exact (fun_ext (fun v : real => @lem1684097 u v)). Qed.
Lemma lem1684103 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684104 (u : real) : (term206 u) = (term227 u).
Proof. exact (MK_COMB (@lem1684103) (@lem1684102 u)). Qed.
Lemma lem1684153 : term207 = term228.
Proof. exact (fun_ext (fun u : real => @lem1684104 u)). Qed.
Lemma lem1684154 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684161 : term208 = term229.
Proof. exact (MK_COMB (@lem1684154) (@lem1684153)). Qed.
Lemma lem1684162 : term122 = term229.
Proof. exact (TRANS (@lem1684069) (@lem1684161)). Qed.
Lemma lem1684163 (h1 : term122) : term229.
Proof. exact (EQ_MP (@lem1684162) (@lem1683910 h1)). Qed.
Lemma lem1684173 (u : real) (v : real) : (term230 u v) = (term231 u v).
Proof. exact (@lem17045 (term232 v) ((real_add u v) = term39)). Qed.
Lemma lem1684175 (u : real) : (term233 u) = (term233 u).
Proof. exact (eq_refl (term233 u)). Qed.
Lemma lem1684176 (u : real) (v : real) : (term234 u v) = (term235 u v).
Proof. exact (MK_COMB (@lem1684175 u) (@lem1684173 u v)). Qed.
Lemma lem1684177 (u : real) (v : real) : (term236 u v) = (term234 u v).
Proof. exact (@lem17045 (term232 u) (term237 u v)). Qed.
Lemma lem1684178 (u : real) (v : real) : (term236 u v) = (term235 u v).
Proof. exact (TRANS (@lem1684177 u v) (@lem1684176 u v)). Qed.
Lemma lem1684180 (y : real) (b : real) : (term238 y b) = (term238 y b).
Proof. exact (eq_refl (term238 y b)). Qed.
Lemma lem1684181 (y : real) (b : real) (u : real) (v : real) : (term239 y b u v) = (term240 y b u v).
Proof. exact (MK_COMB (@lem1684180 y b) (@lem1684178 u v)). Qed.
Lemma lem1684182 (y : real) (b : real) (u : real) (v : real) : (term241 y b u v) = (term239 y b u v).
Proof. exact (@lem17045 (real_le y b) (term242 u v)). Qed.
Lemma lem1684183 (y : real) (b : real) (u : real) (v : real) : (term241 y b u v) = (term240 y b u v).
Proof. exact (TRANS (@lem1684182 y b u v) (@lem1684181 y b u v)). Qed.
Lemma lem1684185 (x : real) (a : real) : (term238 x a) = (term238 x a).
Proof. exact (eq_refl (term238 x a)). Qed.
Lemma lem1684186 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term243 x a y b u v) = (term244 x a y b u v).
Proof. exact (MK_COMB (@lem1684185 x a) (@lem1684183 y b u v)). Qed.
Lemma lem1684187 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term245 x a y b u v) = (term243 x a y b u v).
Proof. exact (@lem17045 (real_le x a) (term246 y b u v)). Qed.
Lemma lem1684188 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term245 x a y b u v) = (term244 x a y b u v).
Proof. exact (TRANS (@lem1684187 x a y b u v) (@lem1684186 x a y b u v)). Qed.
Lemma lem1684189 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term247 x y u a v b) = (term247 x y u a v b).
Proof. exact (eq_refl (term247 x y u a v b)). Qed.
Lemma lem1684190 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1684191 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term248 x a y b u v) = (term249 x a y b u v).
Proof. exact (MK_COMB (@lem1684190) (@lem1684188 x a y b u v)). Qed.
Lemma lem1684192 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term250 x y u a v b) = (term251 x y u a v b).
Proof. exact (MK_COMB (@lem1684191 x a y b u v) (@lem1684189 x y u a v b)). Qed.
Lemma lem1684193 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term250 x y u a v b).
Proof. exact (@lem17265 (term252 x a y b u v) (term247 x y u a v b)). Qed.
Lemma lem1684194 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term251 x y u a v b).
Proof. exact (TRANS (@lem1684193 x y u a v b) (@lem1684192 x y u a v b)). Qed.
Lemma lem1684195 (x : real) (y : real) (u : real) (a : real) (b : real) : (term138 x y u a b) = (term253 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1684194 x y u a v b)). Qed.
Lemma lem1684196 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684197 (x : real) (y : real) (u : real) (a : real) (b : real) : (term139 x y u a b) = (term254 x y u a b).
Proof. exact (MK_COMB (@lem1684196) (@lem1684195 x y u a b)). Qed.
Lemma lem1684198 (x : real) (y : real) (a : real) (b : real) : (term140 x y a b) = (term255 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1684197 x y u a b)). Qed.
Lemma lem1684199 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684200 (x : real) (y : real) (a : real) (b : real) : (term141 x y a b) = (term256 x y a b).
Proof. exact (MK_COMB (@lem1684199) (@lem1684198 x y a b)). Qed.
Lemma lem1684201 (x : real) (y : real) (b : real) : (term142 x y b) = (term257 x y b).
Proof. exact (fun_ext (fun a : real => @lem1684200 x y a b)). Qed.
Lemma lem1684202 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684203 (x : real) (y : real) (b : real) : (term143 x y b) = (term258 x y b).
Proof. exact (MK_COMB (@lem1684202) (@lem1684201 x y b)). Qed.
Lemma lem1684204 (x : real) (b : real) : (term144 x b) = (term259 x b).
Proof. exact (fun_ext (fun y : real => @lem1684203 x y b)). Qed.
Lemma lem1684205 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684206 (x : real) (b : real) : (term145 x b) = (term260 x b).
Proof. exact (MK_COMB (@lem1684205) (@lem1684204 x b)). Qed.
Lemma lem1684207 (b : real) : (term146 b) = (term261 b).
Proof. exact (fun_ext (fun x : real => @lem1684206 x b)). Qed.
Lemma lem1684208 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684209 (b : real) : (term147 b) = (term262 b).
Proof. exact (MK_COMB (@lem1684208) (@lem1684207 b)). Qed.
Lemma lem1684210 : term148 = term263.
Proof. exact (fun_ext (fun b : real => @lem1684209 b)). Qed.
Lemma lem1684211 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684284 : term119 = term264.
Proof. exact (MK_COMB (@lem1684211) (@lem1684210)). Qed.
Lemma lem1684285 (h1 : term119) : term264.
Proof. exact (EQ_MP (@lem1684284) (@lem1683911 h1)). Qed.
Lemma lem1684286 (x : real) (h1 : term195 x) : term195 x.
Proof. exact (h1). Qed.
Lemma lem1684287 (x : real) (y : real) (h1 : term188 x y) : term188 x y.
Proof. exact (h1). Qed.
Lemma lem1684288 (a : real) (x : real) (y : real) (h1 : term181 a x y) : term181 a x y.
Proof. exact (h1). Qed.
Lemma lem1684289 (a : real) (u : real) (x : real) (y : real) (h1 : term174 a u x y) : term174 a u x y.
Proof. exact (h1). Qed.
Lemma lem1684307 (u : real) (v : real) (a : real) : ((term31 u v a) = a) = ((term31 u v a) = a).
Proof. exact (eq_refl ((term31 u v a) = a)). Qed.
Lemma lem1684308 (u : real) (v : real) : (term215 u v) = (term215 u v).
Proof. exact (fun_ext (fun a : real => @lem1684307 u v a)). Qed.
Lemma lem1684309 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684310 (u : real) (v : real) : (term224 u v) = (term224 u v).
Proof. exact (MK_COMB (@lem1684309) (@lem1684308 u v)). Qed.
Lemma lem1684329 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1684330 (u : real) (v : real) : (term225 u v) = (term225 u v).
Proof. exact (MK_COMB (@lem1684329 u v) (@lem1684310 u v)). Qed.
Lemma lem1684331 (u : real) : (term226 u) = (term226 u).
Proof. exact (fun_ext (fun v : real => @lem1684330 u v)). Qed.
Lemma lem1684332 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684333 (u : real) : (term227 u) = (term227 u).
Proof. exact (MK_COMB (@lem1684332) (@lem1684331 u)). Qed.
Lemma lem1684334 : term228 = term228.
Proof. exact (fun_ext (fun u : real => @lem1684333 u)). Qed.
Lemma lem1684335 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684336 : term229 = term229.
Proof. exact (MK_COMB (@lem1684335) (@lem1684334)). Qed.
Lemma lem1684337 (h1 : term122) : term229.
Proof. exact (EQ_MP (@lem1684336) (@lem1684163 h1)). Qed.
Lemma lem1684434 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term251 x y u a v b) = (term251 x y u a v b).
Proof. exact (eq_refl (term251 x y u a v b)). Qed.
Lemma lem1684435 (x : real) (y : real) (u : real) (a : real) (b : real) : (term253 x y u a b) = (term253 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1684434 x y u a v b)). Qed.
Lemma lem1684436 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684437 (x : real) (y : real) (u : real) (a : real) (b : real) : (term254 x y u a b) = (term254 x y u a b).
Proof. exact (MK_COMB (@lem1684436) (@lem1684435 x y u a b)). Qed.
Lemma lem1684438 (x : real) (y : real) (a : real) (b : real) : (term255 x y a b) = (term255 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1684437 x y u a b)). Qed.
Lemma lem1684439 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684440 (x : real) (y : real) (a : real) (b : real) : (term256 x y a b) = (term256 x y a b).
Proof. exact (MK_COMB (@lem1684439) (@lem1684438 x y a b)). Qed.
Lemma lem1684441 (x : real) (y : real) (b : real) : (term257 x y b) = (term257 x y b).
Proof. exact (fun_ext (fun a : real => @lem1684440 x y a b)). Qed.
Lemma lem1684442 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684443 (x : real) (y : real) (b : real) : (term258 x y b) = (term258 x y b).
Proof. exact (MK_COMB (@lem1684442) (@lem1684441 x y b)). Qed.
Lemma lem1684444 (x : real) (b : real) : (term259 x b) = (term259 x b).
Proof. exact (fun_ext (fun y : real => @lem1684443 x y b)). Qed.
Lemma lem1684445 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684446 (x : real) (b : real) : (term260 x b) = (term260 x b).
Proof. exact (MK_COMB (@lem1684445) (@lem1684444 x b)). Qed.
Lemma lem1684447 (b : real) : (term261 b) = (term261 b).
Proof. exact (fun_ext (fun x : real => @lem1684446 x b)). Qed.
Lemma lem1684448 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684449 (b : real) : (term262 b) = (term262 b).
Proof. exact (MK_COMB (@lem1684448) (@lem1684447 b)). Qed.
Lemma lem1684450 : term263 = term263.
Proof. exact (fun_ext (fun b : real => @lem1684449 b)). Qed.
Lemma lem1684451 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684452 : term264 = term264.
Proof. exact (MK_COMB (@lem1684451) (@lem1684450)). Qed.
Lemma lem1684453 (h1 : term119) : term264.
Proof. exact (EQ_MP (@lem1684452) (@lem1684285 h1)). Qed.
Lemma lem1684531 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term163 a u x v y.
Proof. exact (h1). Qed.
Lemma lem1684533 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term164 x a y u v.
Proof. exact (proj1 (@lem1684531 a u x v y h1)). Qed.
Lemma lem1684534 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term246 a y u v.
Proof. exact (proj2 (@lem1684533 a u x v y h1)). Qed.
Lemma lem1684536 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term242 u v.
Proof. exact (proj2 (@lem1684534 a u x v y h1)). Qed.
Lemma lem1684538 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term237 u v.
Proof. exact (proj2 (@lem1684536 a u x v y h1)). Qed.
Lemma lem1684543 {A : Type'} (P : Prop) (Q : A -> Prop) : (term210 A P Q) = (term209 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1684544 (P : Prop) (Q : real -> Prop) : (term212 P Q) = (term211 P Q).
Proof. exact (@lem1684543 real P Q). Qed.
Lemma lem1684545 (u : real) (v : real) : (term214 u v) = (term213 u v).
Proof. exact (@lem1684544 (term52 u v) (term215 u v)). Qed.
Lemma lem1684546 (u : real) (v : real) (a : real) : (term216 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term216 u v a)). Qed.
Lemma lem1684547 (u : real) (v : real) : (term222 u v) = (term215 u v).
Proof. exact (fun_ext (fun a : real => @lem1684546 u v a)). Qed.
Lemma lem1684548 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684549 (u : real) (v : real) : (term223 u v) = (term224 u v).
Proof. exact (MK_COMB (@lem1684548) (@lem1684547 u v)). Qed.
Lemma lem1684550 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1684551 (u : real) (v : real) : (term214 u v) = (term225 u v).
Proof. exact (MK_COMB (@lem1684550 u v) (@lem1684549 u v)). Qed.
Lemma lem1684552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1684553 (u : real) (v : real) : (term265 u v) = (term266 u v).
Proof. exact (MK_COMB (@lem1684552) (@lem1684551 u v)). Qed.
Lemma lem1684554 (u : real) (v : real) (a : real) : (term216 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term216 u v a)). Qed.
Lemma lem1684555 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1684556 (u : real) (v : real) (a : real) : (term218 u v a) = (term202 u v a).
Proof. exact (MK_COMB (@lem1684555 u v) (@lem1684554 u v a)). Qed.
Lemma lem1684557 (u : real) (v : real) : (term219 u v) = (term203 u v).
Proof. exact (fun_ext (fun a : real => @lem1684556 u v a)). Qed.
Lemma lem1684558 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684559 (u : real) (v : real) : (term213 u v) = (term204 u v).
Proof. exact (MK_COMB (@lem1684558) (@lem1684557 u v)). Qed.
Lemma lem1684560 (u : real) (v : real) : ((term214 u v) = (term213 u v)) = ((term225 u v) = (term204 u v)).
Proof. exact (MK_COMB (@lem1684553 u v) (@lem1684559 u v)). Qed.
Lemma lem1684561 (u : real) (v : real) : (term225 u v) = (term204 u v).
Proof. exact (EQ_MP (@lem1684560 u v) (@lem1684545 u v)). Qed.
Lemma lem1684562 (u : real) : (term226 u) = (term205 u).
Proof. exact (fun_ext (fun v : real => @lem1684561 u v)). Qed.
Lemma lem1684563 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684564 (u : real) : (term227 u) = (term206 u).
Proof. exact (MK_COMB (@lem1684563) (@lem1684562 u)). Qed.
Lemma lem1684565 : term228 = term207.
Proof. exact (fun_ext (fun u : real => @lem1684564 u)). Qed.
Lemma lem1684566 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684567 : term229 = term208.
Proof. exact (MK_COMB (@lem1684566) (@lem1684565)). Qed.
Lemma lem1684574 (u : real) (v : real) (a : real) : (term202 u v a) = (term202 u v a).
Proof. exact (eq_refl (term202 u v a)). Qed.
Lemma lem1684575 (u : real) (v : real) : (term203 u v) = (term203 u v).
Proof. exact (fun_ext (fun a : real => @lem1684574 u v a)). Qed.
Lemma lem1684576 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684577 (u : real) (v : real) : (term204 u v) = (term204 u v).
Proof. exact (MK_COMB (@lem1684576) (@lem1684575 u v)). Qed.
Lemma lem1684578 (u : real) : (term205 u) = (term205 u).
Proof. exact (fun_ext (fun v : real => @lem1684577 u v)). Qed.
Lemma lem1684579 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684580 (u : real) : (term206 u) = (term206 u).
Proof. exact (MK_COMB (@lem1684579) (@lem1684578 u)). Qed.
Lemma lem1684581 : term207 = term207.
Proof. exact (fun_ext (fun u : real => @lem1684580 u)). Qed.
Lemma lem1684582 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684583 : term208 = term208.
Proof. exact (MK_COMB (@lem1684582) (@lem1684581)). Qed.
Lemma lem1684584 : term229 = term208.
Proof. exact (TRANS (@lem1684567) (@lem1684583)). Qed.
Lemma lem1684585 (h1 : term122) : term208.
Proof. exact (EQ_MP (@lem1684584) (@lem1684337 h1)). Qed.
Lemma lem1684617 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term251 x y u a v b) = (term251 x y u a v b).
Proof. exact (eq_refl (term251 x y u a v b)). Qed.
Lemma lem1684618 (x : real) (y : real) (u : real) (a : real) (b : real) : (term253 x y u a b) = (term253 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1684617 x y u a v b)). Qed.
Lemma lem1684619 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684620 (x : real) (y : real) (u : real) (a : real) (b : real) : (term254 x y u a b) = (term254 x y u a b).
Proof. exact (MK_COMB (@lem1684619) (@lem1684618 x y u a b)). Qed.
Lemma lem1684621 (x : real) (y : real) (a : real) (b : real) : (term255 x y a b) = (term255 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1684620 x y u a b)). Qed.
Lemma lem1684622 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684623 (x : real) (y : real) (a : real) (b : real) : (term256 x y a b) = (term256 x y a b).
Proof. exact (MK_COMB (@lem1684622) (@lem1684621 x y a b)). Qed.
Lemma lem1684624 (x : real) (y : real) (b : real) : (term257 x y b) = (term257 x y b).
Proof. exact (fun_ext (fun a : real => @lem1684623 x y a b)). Qed.
Lemma lem1684625 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684626 (x : real) (y : real) (b : real) : (term258 x y b) = (term258 x y b).
Proof. exact (MK_COMB (@lem1684625) (@lem1684624 x y b)). Qed.
Lemma lem1684627 (x : real) (b : real) : (term259 x b) = (term259 x b).
Proof. exact (fun_ext (fun y : real => @lem1684626 x y b)). Qed.
Lemma lem1684628 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684629 (x : real) (b : real) : (term260 x b) = (term260 x b).
Proof. exact (MK_COMB (@lem1684628) (@lem1684627 x b)). Qed.
Lemma lem1684630 (b : real) : (term261 b) = (term261 b).
Proof. exact (fun_ext (fun x : real => @lem1684629 x b)). Qed.
Lemma lem1684631 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684632 (b : real) : (term262 b) = (term262 b).
Proof. exact (MK_COMB (@lem1684631) (@lem1684630 b)). Qed.
Lemma lem1684633 : term263 = term263.
Proof. exact (fun_ext (fun b : real => @lem1684632 b)). Qed.
Lemma lem1684634 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1684636 : term264 = term264.
Proof. exact (MK_COMB (@lem1684634) (@lem1684633)). Qed.
Lemma lem1684637 (h1 : term119) : term264.
Proof. exact (EQ_MP (@lem1684636) (@lem1684453 h1)). Qed.
Lemma lem1684662 (_25978 : real) (h1 : term122) : term267 _25978.
Proof. exact (@lem1684585 h1 _25978). Qed.
Lemma lem1684663 (_25978 : real) : (term267 _25978) = (term206 _25978).
Proof. exact (eq_refl (term267 _25978)). Qed.
Lemma lem1684664 (_25978 : real) (h1 : term122) : term206 _25978.
Proof. exact (EQ_MP (@lem1684663 _25978) (@lem1684662 _25978 h1)). Qed.
Lemma lem1684665 (_25978 : real) (_25979 : real) (h1 : term122) : term268 _25978 _25979.
Proof. exact (@lem1684664 _25978 h1 _25979). Qed.
Lemma lem1684666 (_25978 : real) (_25979 : real) : (term268 _25978 _25979) = (term204 _25978 _25979).
Proof. exact (eq_refl (term268 _25978 _25979)). Qed.
Lemma lem1684667 (_25978 : real) (_25979 : real) (h1 : term122) : term204 _25978 _25979.
Proof. exact (EQ_MP (@lem1684666 _25978 _25979) (@lem1684665 _25978 _25979 h1)). Qed.
Lemma lem1684668 (_25978 : real) (_25979 : real) (_25980 : real) (h1 : term122) : term269 _25978 _25979 _25980.
Proof. exact (@lem1684667 _25978 _25979 h1 _25980). Qed.
Lemma lem1684669 (_25978 : real) (_25979 : real) (_25980 : real) : (term269 _25978 _25979 _25980) = (term202 _25978 _25979 _25980).
Proof. exact (eq_refl (term269 _25978 _25979 _25980)). Qed.
Lemma lem1684671 (_25981 : real) (h1 : term119) : term270 _25981.
Proof. exact (@lem1684637 h1 _25981). Qed.
Lemma lem1684672 (_25981 : real) : (term270 _25981) = (term262 _25981).
Proof. exact (eq_refl (term270 _25981)). Qed.
Lemma lem1684673 (_25981 : real) (h1 : term119) : term262 _25981.
Proof. exact (EQ_MP (@lem1684672 _25981) (@lem1684671 _25981 h1)). Qed.
Lemma lem1684674 (_25981 : real) (_25982 : real) (h1 : term119) : term271 _25981 _25982.
Proof. exact (@lem1684673 _25981 h1 _25982). Qed.
Lemma lem1684675 (_25982 : real) (_25981 : real) : (term271 _25981 _25982) = (term260 _25982 _25981).
Proof. exact (eq_refl (term271 _25981 _25982)). Qed.
Lemma lem1684676 (_25982 : real) (_25981 : real) (h1 : term119) : term260 _25982 _25981.
Proof. exact (EQ_MP (@lem1684675 _25982 _25981) (@lem1684674 _25981 _25982 h1)). Qed.
Lemma lem1684677 (_25982 : real) (_25981 : real) (_25983 : real) (h1 : term119) : term272 _25982 _25981 _25983.
Proof. exact (@lem1684676 _25982 _25981 h1 _25983). Qed.
Lemma lem1684678 (_25982 : real) (_25983 : real) (_25981 : real) : (term272 _25982 _25981 _25983) = (term258 _25982 _25983 _25981).
Proof. exact (eq_refl (term272 _25982 _25981 _25983)). Qed.
Lemma lem1684679 (_25982 : real) (_25983 : real) (_25981 : real) (h1 : term119) : term258 _25982 _25983 _25981.
Proof. exact (EQ_MP (@lem1684678 _25982 _25983 _25981) (@lem1684677 _25982 _25981 _25983 h1)). Qed.
Lemma lem1684680 (_25982 : real) (_25983 : real) (_25981 : real) (_25984 : real) (h1 : term119) : term273 _25982 _25983 _25981 _25984.
Proof. exact (@lem1684679 _25982 _25983 _25981 h1 _25984). Qed.
Lemma lem1684681 (_25982 : real) (_25983 : real) (_25984 : real) (_25981 : real) : (term273 _25982 _25983 _25981 _25984) = (term256 _25982 _25983 _25984 _25981).
Proof. exact (eq_refl (term273 _25982 _25983 _25981 _25984)). Qed.
Lemma lem1684682 (_25982 : real) (_25983 : real) (_25984 : real) (_25981 : real) (h1 : term119) : term256 _25982 _25983 _25984 _25981.
Proof. exact (EQ_MP (@lem1684681 _25982 _25983 _25984 _25981) (@lem1684680 _25982 _25983 _25981 _25984 h1)). Qed.
Lemma lem1684683 (_25982 : real) (_25983 : real) (_25984 : real) (_25981 : real) (_25985 : real) (h1 : term119) : term274 _25982 _25983 _25984 _25981 _25985.
Proof. exact (@lem1684682 _25982 _25983 _25984 _25981 h1 _25985). Qed.
Lemma lem1684684 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25981 : real) : (term274 _25982 _25983 _25984 _25981 _25985) = (term254 _25982 _25983 _25985 _25984 _25981).
Proof. exact (eq_refl (term274 _25982 _25983 _25984 _25981 _25985)). Qed.
Lemma lem1684685 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25981 : real) (h1 : term119) : term254 _25982 _25983 _25985 _25984 _25981.
Proof. exact (EQ_MP (@lem1684684 _25982 _25983 _25985 _25984 _25981) (@lem1684683 _25982 _25983 _25984 _25981 _25985 h1)). Qed.
Lemma lem1684686 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25981 : real) (_25986 : real) (h1 : term119) : term275 _25982 _25983 _25985 _25984 _25981 _25986.
Proof. exact (@lem1684685 _25982 _25983 _25985 _25984 _25981 h1 _25986). Qed.
Lemma lem1684687 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term275 _25982 _25983 _25985 _25984 _25981 _25986) = (term251 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (eq_refl (term275 _25982 _25983 _25985 _25984 _25981 _25986)). Qed.
Lemma lem1684688 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) (h1 : term119) : term251 _25982 _25983 _25985 _25984 _25986 _25981.
Proof. exact (EQ_MP (@lem1684687 _25982 _25983 _25985 _25984 _25986 _25981) (@lem1684686 _25982 _25983 _25985 _25984 _25981 _25986 h1)). Qed.
Lemma lem1684694 (_25978 : real) (_25979 : real) (_25980 : real) (h1 : term122) : term202 _25978 _25979 _25980.
Proof. exact (EQ_MP (@lem1684669 _25978 _25979 _25980) (@lem1684668 _25978 _25979 _25980 h1)). Qed.
Lemma lem1684698 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term251 _25982 _25983 _25985 _25984 _25986 _25981) = (term276 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (@lem1683574 (term277 _25982 _25984) (term240 _25983 _25981 _25985 _25986) (term247 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1684699 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term278 _25982 _25983 _25985 _25984 _25986 _25981) = (term279 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (@lem1683574 (term277 _25983 _25981) (term235 _25985 _25986) (term247 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1684700 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term280 _25982 _25983 _25985 _25984 _25986 _25981) = (term281 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (@lem1683574 (term282 _25985) (term231 _25985 _25986) (term247 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1684707 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term283 _25982 _25983 _25985 _25984 _25986 _25981) = (term284 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (@lem1683574 (term282 _25986) (term52 _25985 _25986) (term247 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1684708 (_25985 : real) : (term233 _25985) = (term233 _25985).
Proof. exact (eq_refl (term233 _25985)). Qed.
Lemma lem1684711 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term281 _25982 _25983 _25985 _25984 _25986 _25981) = (term285 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (MK_COMB (@lem1684708 _25985) (@lem1684707 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1684712 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term280 _25982 _25983 _25985 _25984 _25986 _25981) = (term285 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (TRANS (@lem1684700 _25982 _25983 _25985 _25984 _25986 _25981) (@lem1684711 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1684713 (_25983 : real) (_25981 : real) : (term238 _25983 _25981) = (term238 _25983 _25981).
Proof. exact (eq_refl (term238 _25983 _25981)). Qed.
Lemma lem1684716 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term279 _25982 _25983 _25985 _25984 _25986 _25981) = (term286 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (MK_COMB (@lem1684713 _25983 _25981) (@lem1684712 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1684717 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term278 _25982 _25983 _25985 _25984 _25986 _25981) = (term286 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (TRANS (@lem1684699 _25982 _25983 _25985 _25984 _25986 _25981) (@lem1684716 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1684718 (_25982 : real) (_25984 : real) : (term238 _25982 _25984) = (term238 _25982 _25984).
Proof. exact (eq_refl (term238 _25982 _25984)). Qed.
Lemma lem1684721 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term276 _25982 _25983 _25985 _25984 _25986 _25981) = (term287 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (MK_COMB (@lem1684718 _25982 _25984) (@lem1684717 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1684723 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term251 _25982 _25983 _25985 _25984 _25986 _25981) = (term287 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (TRANS (@lem1684698 _25982 _25983 _25985 _25984 _25986 _25981) (@lem1684721 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1684724 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) (h1 : term119) : term287 _25982 _25983 _25985 _25984 _25986 _25981.
Proof. exact (EQ_MP (@lem1684723 _25982 _25983 _25985 _25984 _25986 _25981) (@lem1684688 _25982 _25983 _25985 _25984 _25986 _25981 h1)). Qed.
Lemma lem1684726 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term288 a u x v y.
Proof. exact (proj2 (@lem1684531 a u x v y h1)). Qed.
Lemma lem1684737 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1684738 (_25987 : real) (_25989 : real) (h1 : _25987 = _25989) : _25987 = _25989.
Proof. exact (h1). Qed.
Lemma lem1684739 (_25988 : real) (_25990 : real) (h1 : _25988 = _25990) : _25988 = _25990.
Proof. exact (h1). Qed.
Lemma lem1684740 (_25987 : real) (_25989 : real) (h1 : _25987 = _25989) : (real_le _25987) = (real_le _25989).
Proof. exact (MK_COMB (@lem1684737) (@lem1684738 _25987 _25989 h1)). Qed.
Lemma lem1684741 (_25987 : real) (_25989 : real) (_25988 : real) (_25990 : real) (h1 : _25987 = _25989) (h2 : _25988 = _25990) : (real_le _25987 _25988) = (real_le _25989 _25990).
Proof. exact (MK_COMB (@lem1684740 _25987 _25989 h1) (@lem1684739 _25988 _25990 h2)). Qed.
Lemma lem1684743 (b : Prop) (a : Prop) : term289 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1684744 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : term290 _25989 _25990 _25987 _25988.
Proof. exact (@lem1684743 (real_le _25989 _25990) (real_le _25987 _25988)). Qed.
Lemma lem1684745 (_25987 : real) (_25989 : real) (_25988 : real) (_25990 : real) (h1 : _25987 = _25989) (h2 : _25988 = _25990) : term291 _25989 _25990 _25987 _25988.
Proof. exact (@lem1684744 _25989 _25990 _25987 _25988 (@lem1684741 _25987 _25989 _25988 _25990 h1 h2)). Qed.
Lemma lem1684746 (_25990 : real) (_25988 : real) (_25987 : real) (_25989 : real) (h1 : _25987 = _25989) : term292 _25989 _25990 _25987 _25988.
Proof. exact (fun h0 : _25988 = _25990 => @lem1684745 _25987 _25989 _25988 _25990 h1 h0). Qed.
Lemma lem1684748 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1684749 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : (term292 _25989 _25990 _25987 _25988) = (term293 _25989 _25990 _25987 _25988).
Proof. exact (@lem1684748 (_25988 = _25990) (term291 _25989 _25990 _25987 _25988)). Qed.
Lemma lem1684750 (_25990 : real) (_25988 : real) (_25987 : real) (_25989 : real) (h1 : _25987 = _25989) : term293 _25989 _25990 _25987 _25988.
Proof. exact (EQ_MP (@lem1684749 _25989 _25990 _25987 _25988) (@lem1684746 _25990 _25988 _25987 _25989 h1)). Qed.
Lemma lem1684751 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : term294 _25989 _25990 _25987 _25988.
Proof. exact (fun h0 : _25987 = _25989 => @lem1684750 _25990 _25988 _25987 _25989 h0). Qed.
Lemma lem1684753 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1684754 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : (term294 _25989 _25990 _25987 _25988) = (term295 _25989 _25990 _25987 _25988).
Proof. exact (@lem1684753 (_25987 = _25989) (term293 _25989 _25990 _25987 _25988)). Qed.
Lemma lem1684755 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : term295 _25989 _25990 _25987 _25988.
Proof. exact (EQ_MP (@lem1684754 _25989 _25990 _25987 _25988) (@lem1684751 _25989 _25990 _25987 _25988)). Qed.
Lemma lem1684815 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1684538 a u x v y h1)). Qed.
Lemma lem1684816 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1684815 a u x v y h1). Qed.
Lemma lem1684818 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1684819 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1684818 ((real_add u v) = term39)). Qed.
Lemma lem1684820 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1684819 u v) (@lem1684816 a u x v y h1)). Qed.
Lemma lem1684826 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1684827 (_25980 : real) (_25978 : real) (_25979 : real) : (term202 _25978 _25979 _25980) = (term296 _25980 _25978 _25979).
Proof. exact (@lem1684826 ((term31 _25978 _25979 _25980) = _25980) (term52 _25978 _25979)). Qed.
Lemma lem1684837 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1684838 (_25980 : real) (_25978 : real) (_25979 : real) : (term297 _25978 _25979 _25980) = (term298 _25980 _25978 _25979).
Proof. exact (MK_COMB (@lem1684837) (@lem1684827 _25980 _25978 _25979)). Qed.
Lemma lem1684848 (_25980 : real) (_25978 : real) (_25979 : real) : (term296 _25980 _25978 _25979) = (term296 _25980 _25978 _25979).
Proof. exact (eq_refl (term296 _25980 _25978 _25979)). Qed.
Lemma lem1684849 (_25980 : real) (_25978 : real) (_25979 : real) : ((term202 _25978 _25979 _25980) = (term296 _25980 _25978 _25979)) = ((term296 _25980 _25978 _25979) = (term296 _25980 _25978 _25979)).
Proof. exact (MK_COMB (@lem1684838 _25980 _25978 _25979) (@lem1684848 _25980 _25978 _25979)). Qed.
Lemma lem1684851 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1684852 (x : Prop) : (x = x) = True.
Proof. exact (@lem1684851 Prop x). Qed.
Lemma lem1684853 (_25980 : real) (_25978 : real) (_25979 : real) : ((term296 _25980 _25978 _25979) = (term296 _25980 _25978 _25979)) = True.
Proof. exact (@lem1684852 (term296 _25980 _25978 _25979)). Qed.
Lemma lem1684854 (_25980 : real) (_25978 : real) (_25979 : real) : ((term202 _25978 _25979 _25980) = (term296 _25980 _25978 _25979)) = True.
Proof. exact (TRANS (@lem1684849 _25980 _25978 _25979) (@lem1684853 _25980 _25978 _25979)). Qed.
Lemma lem1684855 (_25980 : real) (_25978 : real) (_25979 : real) : True = ((term202 _25978 _25979 _25980) = (term296 _25980 _25978 _25979)).
Proof. exact (SYM (@lem1684854 _25980 _25978 _25979)). Qed.
Lemma lem1684856 (_25980 : real) (_25978 : real) (_25979 : real) : (term202 _25978 _25979 _25980) = (term296 _25980 _25978 _25979).
Proof. exact (EQ_MP (@lem1684855 _25980 _25978 _25979) (@lem0)). Qed.
Lemma lem1684857 (_25980 : real) (_25978 : real) (_25979 : real) (h1 : term122) : term296 _25980 _25978 _25979.
Proof. exact (EQ_MP (@lem1684856 _25980 _25978 _25979) (@lem1684694 _25978 _25979 _25980 h1)). Qed.
Lemma lem1684859 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1684860 (_25978 : real) (_25979 : real) (_25980 : real) : (term296 _25980 _25978 _25979) = (term299 _25978 _25979 _25980).
Proof. exact (@lem1684859 (term52 _25978 _25979) ((term31 _25978 _25979 _25980) = _25980)). Qed.
Lemma lem1684862 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1684863 (_25978 : real) (_25979 : real) : (term300 _25978 _25979) = ((real_add _25978 _25979) = term39).
Proof. exact (@lem1684862 ((real_add _25978 _25979) = term39)). Qed.
Lemma lem1684864 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1684865 (_25978 : real) (_25979 : real) : (term301 _25978 _25979) = (term302 _25978 _25979).
Proof. exact (MK_COMB (@lem1684864) (@lem1684863 _25978 _25979)). Qed.
Lemma lem1684866 (_25978 : real) (_25979 : real) (_25980 : real) : ((term31 _25978 _25979 _25980) = _25980) = ((term31 _25978 _25979 _25980) = _25980).
Proof. exact (eq_refl ((term31 _25978 _25979 _25980) = _25980)). Qed.
Lemma lem1684867 (_25978 : real) (_25979 : real) (_25980 : real) : (term299 _25978 _25979 _25980) = (term1 _25978 _25979 _25980).
Proof. exact (MK_COMB (@lem1684865 _25978 _25979) (@lem1684866 _25978 _25979 _25980)). Qed.
Lemma lem1684868 (_25978 : real) (_25979 : real) (_25980 : real) : (term296 _25980 _25978 _25979) = (term1 _25978 _25979 _25980).
Proof. exact (TRANS (@lem1684860 _25978 _25979 _25980) (@lem1684867 _25978 _25979 _25980)). Qed.
Lemma lem1684871 (_25978 : real) (_25979 : real) (_25980 : real) (h1 : term122) : term1 _25978 _25979 _25980.
Proof. exact (EQ_MP (@lem1684868 _25978 _25979 _25980) (@lem1684857 _25980 _25978 _25979 h1)). Qed.
Lemma lem1684872 (u : real) (v : real) (_25980 : real) (h1 : term122) : term1 u v _25980.
Proof. exact (@lem1684871 u v _25980 h1). Qed.
Lemma lem1684875 (_25980 : real) (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term122) (h2 : term163 a u x v y) : (term31 u v _25980) = _25980.
Proof. exact (@lem1684872 u v _25980 h1 (@lem1684820 a u x v y h2)). Qed.
Lemma lem1684876 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term122) (h2 : term163 a u x v y) : (term31 u v a) = a.
Proof. exact (@lem1684875 a a u x v y h1 h2). Qed.
Lemma lem1684877 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term122) (h2 : term163 a u x v y) : term107 u v a.
Proof. exact (fun h0 : term44 u v a => @lem1684876 a u x v y h1 h2). Qed.
Lemma lem1684879 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1684880 (u : real) (v : real) (a : real) : (term107 u v a) = ((term31 u v a) = a).
Proof. exact (@lem1684879 ((term31 u v a) = a)). Qed.
Lemma lem1684881 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term122) (h2 : term163 a u x v y) : (term31 u v a) = a.
Proof. exact (EQ_MP (@lem1684880 u v a) (@lem1684877 a u x v y h1 h2)). Qed.
Lemma lem1684883 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1684884 (u : real) (x : real) (v : real) (y : real) : (term303 u x v y) = (term303 u x v y).
Proof. exact (@lem1684883 (term303 u x v y)). Qed.
Lemma lem1684885 (u : real) (x : real) (v : real) (y : real) : term304 u x v y.
Proof. exact (fun h0 : term305 u x v y => @lem1684884 u x v y). Qed.
Lemma lem1684887 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1684888 (u : real) (x : real) (v : real) (y : real) : (term304 u x v y) = ((term303 u x v y) = (term303 u x v y)).
Proof. exact (@lem1684887 ((term303 u x v y) = (term303 u x v y))). Qed.
Lemma lem1684889 (u : real) (x : real) (v : real) (y : real) : (term303 u x v y) = (term303 u x v y).
Proof. exact (EQ_MP (@lem1684888 u x v y) (@lem1684885 u x v y)). Qed.
Lemma lem1684891 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : real_le a x.
Proof. exact (proj1 (@lem1684533 a u x v y h1)). Qed.
Lemma lem1684892 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term306 a x.
Proof. exact (fun h0 : term277 a x => @lem1684891 a u x v y h1). Qed.
Lemma lem1684894 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1684895 (a : real) (x : real) : (term306 a x) = (real_le a x).
Proof. exact (@lem1684894 (real_le a x)). Qed.
Lemma lem1684896 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : real_le a x.
Proof. exact (EQ_MP (@lem1684895 a x) (@lem1684892 a u x v y h1)). Qed.
Lemma lem1684898 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : real_le a y.
Proof. exact (proj1 (@lem1684534 a u x v y h1)). Qed.
Lemma lem1684899 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term306 a y.
Proof. exact (fun h0 : term277 a y => @lem1684898 a u x v y h1). Qed.
Lemma lem1684901 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1684902 (a : real) (y : real) : (term306 a y) = (real_le a y).
Proof. exact (@lem1684901 (real_le a y)). Qed.
Lemma lem1684903 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : real_le a y.
Proof. exact (EQ_MP (@lem1684902 a y) (@lem1684899 a u x v y h1)). Qed.
Lemma lem1684905 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term232 u.
Proof. exact (proj1 (@lem1684536 a u x v y h1)). Qed.
Lemma lem1684906 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term307 u.
Proof. exact (fun h0 : term282 u => @lem1684905 a u x v y h1). Qed.
Lemma lem1684908 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1684909 (u : real) : (term307 u) = (term232 u).
Proof. exact (@lem1684908 (term232 u)). Qed.
Lemma lem1684910 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term232 u.
Proof. exact (EQ_MP (@lem1684909 u) (@lem1684906 a u x v y h1)). Qed.
Lemma lem1684912 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term232 v.
Proof. exact (proj1 (@lem1684538 a u x v y h1)). Qed.
Lemma lem1684913 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term307 v.
Proof. exact (fun h0 : term282 v => @lem1684912 a u x v y h1). Qed.
Lemma lem1684915 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1684916 (v : real) : (term307 v) = (term232 v).
Proof. exact (@lem1684915 (term232 v)). Qed.
Lemma lem1684917 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term232 v.
Proof. exact (EQ_MP (@lem1684916 v) (@lem1684913 a u x v y h1)). Qed.
Lemma lem1684919 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1684538 a u x v y h1)). Qed.
Lemma lem1684920 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1684919 a u x v y h1). Qed.
Lemma lem1684922 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1684923 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1684922 ((real_add u v) = term39)). Qed.
Lemma lem1684924 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1684923 u v) (@lem1684920 a u x v y h1)). Qed.
Lemma lem1684960 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1684961 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term284 _25982 _25983 _25985 _25984 _25986 _25981) = (term308 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (@lem1684960 (term52 _25985 _25986) (term282 _25986) (term247 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1684977 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1684978 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25981 : real) (_25986 : real) : (term309 _25982 _25983 _25985 _25984 _25986 _25981) = (term310 _25982 _25983 _25985 _25984 _25981 _25986).
Proof. exact (@lem1684977 (term247 _25982 _25983 _25985 _25984 _25986 _25981) (term282 _25986)). Qed.
Lemma lem1684984 (_25985 : real) (_25986 : real) : (term217 _25985 _25986) = (term217 _25985 _25986).
Proof. exact (eq_refl (term217 _25985 _25986)). Qed.
Lemma lem1684985 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25981 : real) (_25986 : real) : (term308 _25982 _25983 _25985 _25984 _25986 _25981) = (term311 _25982 _25983 _25985 _25984 _25981 _25986).
Proof. exact (MK_COMB (@lem1684984 _25985 _25986) (@lem1684978 _25982 _25983 _25985 _25984 _25981 _25986)). Qed.
Lemma lem1684989 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1684990 (_25982 : real) (_25983 : real) (_25984 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term311 _25982 _25983 _25985 _25984 _25981 _25986) = (term312 _25982 _25983 _25984 _25981 _25985 _25986).
Proof. exact (@lem1684989 (term247 _25982 _25983 _25985 _25984 _25986 _25981) (term52 _25985 _25986) (term282 _25986)). Qed.
Lemma lem1685008 (_25982 : real) (_25983 : real) (_25984 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term308 _25982 _25983 _25985 _25984 _25986 _25981) = (term312 _25982 _25983 _25984 _25981 _25985 _25986).
Proof. exact (TRANS (@lem1684985 _25982 _25983 _25985 _25984 _25981 _25986) (@lem1684990 _25982 _25983 _25984 _25981 _25985 _25986)). Qed.
Lemma lem1685009 (_25982 : real) (_25983 : real) (_25984 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term284 _25982 _25983 _25985 _25984 _25986 _25981) = (term312 _25982 _25983 _25984 _25981 _25985 _25986).
Proof. exact (TRANS (@lem1684961 _25982 _25983 _25985 _25984 _25986 _25981) (@lem1685008 _25982 _25983 _25984 _25981 _25985 _25986)). Qed.
Lemma lem1685010 (_25985 : real) : (term233 _25985) = (term233 _25985).
Proof. exact (eq_refl (term233 _25985)). Qed.
Lemma lem1685011 (_25982 : real) (_25983 : real) (_25984 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term285 _25982 _25983 _25985 _25984 _25986 _25981) = (term313 _25982 _25983 _25984 _25981 _25985 _25986).
Proof. exact (MK_COMB (@lem1685010 _25985) (@lem1685009 _25982 _25983 _25984 _25981 _25985 _25986)). Qed.
Lemma lem1685015 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1685016 (_25982 : real) (_25983 : real) (_25984 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term313 _25982 _25983 _25984 _25981 _25985 _25986) = (term314 _25982 _25983 _25984 _25981 _25985 _25986).
Proof. exact (@lem1685015 (term247 _25982 _25983 _25985 _25984 _25986 _25981) (term282 _25985) (term315 _25985 _25986)). Qed.
Lemma lem1685030 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1685031 (_25985 : real) (_25986 : real) : (term316 _25985 _25986) = (term317 _25985 _25986).
Proof. exact (@lem1685030 (term52 _25985 _25986) (term282 _25985) (term282 _25986)). Qed.
Lemma lem1685049 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term318 _25982 _25983 _25985 _25984 _25986 _25981) = (term318 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (eq_refl (term318 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1685050 (_25982 : real) (_25983 : real) (_25984 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term314 _25982 _25983 _25984 _25981 _25985 _25986) = (term319 _25982 _25983 _25984 _25981 _25985 _25986).
Proof. exact (MK_COMB (@lem1685049 _25982 _25983 _25985 _25984 _25986 _25981) (@lem1685031 _25985 _25986)). Qed.
Lemma lem1685061 (_25982 : real) (_25983 : real) (_25984 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term313 _25982 _25983 _25984 _25981 _25985 _25986) = (term319 _25982 _25983 _25984 _25981 _25985 _25986).
Proof. exact (TRANS (@lem1685016 _25982 _25983 _25984 _25981 _25985 _25986) (@lem1685050 _25982 _25983 _25984 _25981 _25985 _25986)). Qed.
Lemma lem1685062 (_25982 : real) (_25983 : real) (_25984 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term285 _25982 _25983 _25985 _25984 _25986 _25981) = (term319 _25982 _25983 _25984 _25981 _25985 _25986).
Proof. exact (TRANS (@lem1685011 _25982 _25983 _25984 _25981 _25985 _25986) (@lem1685061 _25982 _25983 _25984 _25981 _25985 _25986)). Qed.
Lemma lem1685063 (_25983 : real) (_25981 : real) : (term238 _25983 _25981) = (term238 _25983 _25981).
Proof. exact (eq_refl (term238 _25983 _25981)). Qed.
Lemma lem1685064 (_25982 : real) (_25983 : real) (_25984 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term286 _25982 _25983 _25985 _25984 _25986 _25981) = (term320 _25982 _25983 _25984 _25981 _25985 _25986).
Proof. exact (MK_COMB (@lem1685063 _25983 _25981) (@lem1685062 _25982 _25983 _25984 _25981 _25985 _25986)). Qed.
Lemma lem1685068 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1685069 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term320 _25982 _25983 _25984 _25981 _25985 _25986) = (term321 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (@lem1685068 (term247 _25982 _25983 _25985 _25984 _25986 _25981) (term277 _25983 _25981) (term317 _25985 _25986)). Qed.
Lemma lem1685083 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1685084 (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term322 _25983 _25981 _25985 _25986) = (term323 _25983 _25981 _25985 _25986).
Proof. exact (@lem1685083 (term52 _25985 _25986) (term277 _25983 _25981) (term324 _25985 _25986)). Qed.
Lemma lem1685112 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term318 _25982 _25983 _25985 _25984 _25986 _25981) = (term318 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (eq_refl (term318 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1685113 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term321 _25982 _25984 _25983 _25981 _25985 _25986) = (term325 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (MK_COMB (@lem1685112 _25982 _25983 _25985 _25984 _25986 _25981) (@lem1685084 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685124 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term320 _25982 _25983 _25984 _25981 _25985 _25986) = (term325 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (TRANS (@lem1685069 _25982 _25984 _25983 _25981 _25985 _25986) (@lem1685113 _25982 _25984 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685125 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term286 _25982 _25983 _25985 _25984 _25986 _25981) = (term325 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (TRANS (@lem1685064 _25982 _25983 _25984 _25981 _25985 _25986) (@lem1685124 _25982 _25984 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685126 (_25982 : real) (_25984 : real) : (term238 _25982 _25984) = (term238 _25982 _25984).
Proof. exact (eq_refl (term238 _25982 _25984)). Qed.
Lemma lem1685127 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term287 _25982 _25983 _25985 _25984 _25986 _25981) = (term326 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (MK_COMB (@lem1685126 _25982 _25984) (@lem1685125 _25982 _25984 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685131 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1685132 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term326 _25982 _25984 _25983 _25981 _25985 _25986) = (term327 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (@lem1685131 (term247 _25982 _25983 _25985 _25984 _25986 _25981) (term277 _25982 _25984) (term323 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685146 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1685147 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term328 _25982 _25984 _25983 _25981 _25985 _25986) = (term329 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (@lem1685146 (term52 _25985 _25986) (term277 _25982 _25984) (term330 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685185 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term318 _25982 _25983 _25985 _25984 _25986 _25981) = (term318 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (eq_refl (term318 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1685186 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term327 _25982 _25984 _25983 _25981 _25985 _25986) = (term331 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (MK_COMB (@lem1685185 _25982 _25983 _25985 _25984 _25986 _25981) (@lem1685147 _25982 _25984 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685197 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term326 _25982 _25984 _25983 _25981 _25985 _25986) = (term331 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (TRANS (@lem1685132 _25982 _25984 _25983 _25981 _25985 _25986) (@lem1685186 _25982 _25984 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685198 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term287 _25982 _25983 _25985 _25984 _25986 _25981) = (term331 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (TRANS (@lem1685127 _25982 _25984 _25983 _25981 _25985 _25986) (@lem1685197 _25982 _25984 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1685200 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term332 _25982 _25983 _25985 _25984 _25986 _25981) = (term333 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (MK_COMB (@lem1685199) (@lem1685198 _25982 _25984 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685244 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1685245 (_25985 : real) (_25986 : real) : (term231 _25985 _25986) = (term315 _25985 _25986).
Proof. exact (@lem1685244 (term52 _25985 _25986) (term282 _25986)). Qed.
Lemma lem1685253 (_25985 : real) : (term233 _25985) = (term233 _25985).
Proof. exact (eq_refl (term233 _25985)). Qed.
Lemma lem1685254 (_25985 : real) (_25986 : real) : (term235 _25985 _25986) = (term316 _25985 _25986).
Proof. exact (MK_COMB (@lem1685253 _25985) (@lem1685245 _25985 _25986)). Qed.
Lemma lem1685258 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1685259 (_25985 : real) (_25986 : real) : (term316 _25985 _25986) = (term317 _25985 _25986).
Proof. exact (@lem1685258 (term52 _25985 _25986) (term282 _25985) (term282 _25986)). Qed.
Lemma lem1685277 (_25985 : real) (_25986 : real) : (term235 _25985 _25986) = (term317 _25985 _25986).
Proof. exact (TRANS (@lem1685254 _25985 _25986) (@lem1685259 _25985 _25986)). Qed.
Lemma lem1685278 (_25983 : real) (_25981 : real) : (term238 _25983 _25981) = (term238 _25983 _25981).
Proof. exact (eq_refl (term238 _25983 _25981)). Qed.
Lemma lem1685279 (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term240 _25983 _25981 _25985 _25986) = (term322 _25983 _25981 _25985 _25986).
Proof. exact (MK_COMB (@lem1685278 _25983 _25981) (@lem1685277 _25985 _25986)). Qed.
Lemma lem1685283 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1685284 (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term322 _25983 _25981 _25985 _25986) = (term323 _25983 _25981 _25985 _25986).
Proof. exact (@lem1685283 (term52 _25985 _25986) (term277 _25983 _25981) (term324 _25985 _25986)). Qed.
Lemma lem1685312 (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term240 _25983 _25981 _25985 _25986) = (term323 _25983 _25981 _25985 _25986).
Proof. exact (TRANS (@lem1685279 _25983 _25981 _25985 _25986) (@lem1685284 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685313 (_25982 : real) (_25984 : real) : (term238 _25982 _25984) = (term238 _25982 _25984).
Proof. exact (eq_refl (term238 _25982 _25984)). Qed.
Lemma lem1685314 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term244 _25982 _25984 _25983 _25981 _25985 _25986) = (term328 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (MK_COMB (@lem1685313 _25982 _25984) (@lem1685312 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685318 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1685319 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term328 _25982 _25984 _25983 _25981 _25985 _25986) = (term329 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (@lem1685318 (term52 _25985 _25986) (term277 _25982 _25984) (term330 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685357 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term244 _25982 _25984 _25983 _25981 _25985 _25986) = (term329 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (TRANS (@lem1685314 _25982 _25984 _25983 _25981 _25985 _25986) (@lem1685319 _25982 _25984 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685358 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term318 _25982 _25983 _25985 _25984 _25986 _25981) = (term318 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (eq_refl (term318 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1685359 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term334 _25982 _25984 _25983 _25981 _25985 _25986) = (term331 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (MK_COMB (@lem1685358 _25982 _25983 _25985 _25984 _25986 _25981) (@lem1685357 _25982 _25984 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685370 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : ((term287 _25982 _25983 _25985 _25984 _25986 _25981) = (term334 _25982 _25984 _25983 _25981 _25985 _25986)) = ((term331 _25982 _25984 _25983 _25981 _25985 _25986) = (term331 _25982 _25984 _25983 _25981 _25985 _25986)).
Proof. exact (MK_COMB (@lem1685200 _25982 _25984 _25983 _25981 _25985 _25986) (@lem1685359 _25982 _25984 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685372 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1685373 (x : Prop) : (x = x) = True.
Proof. exact (@lem1685372 Prop x). Qed.
Lemma lem1685374 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : ((term331 _25982 _25984 _25983 _25981 _25985 _25986) = (term331 _25982 _25984 _25983 _25981 _25985 _25986)) = True.
Proof. exact (@lem1685373 (term331 _25982 _25984 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685375 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : ((term287 _25982 _25983 _25985 _25984 _25986 _25981) = (term334 _25982 _25984 _25983 _25981 _25985 _25986)) = True.
Proof. exact (TRANS (@lem1685370 _25982 _25984 _25983 _25981 _25985 _25986) (@lem1685374 _25982 _25984 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685376 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : True = ((term287 _25982 _25983 _25985 _25984 _25986 _25981) = (term334 _25982 _25984 _25983 _25981 _25985 _25986)).
Proof. exact (SYM (@lem1685375 _25982 _25984 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685377 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term287 _25982 _25983 _25985 _25984 _25986 _25981) = (term334 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (EQ_MP (@lem1685376 _25982 _25984 _25983 _25981 _25985 _25986) (@lem0)). Qed.
Lemma lem1685378 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) (h1 : term119) : term334 _25982 _25984 _25983 _25981 _25985 _25986.
Proof. exact (EQ_MP (@lem1685377 _25982 _25984 _25983 _25981 _25985 _25986) (@lem1684724 _25982 _25983 _25985 _25984 _25986 _25981 h1)). Qed.
Lemma lem1685380 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1685381 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term334 _25982 _25984 _25983 _25981 _25985 _25986) = (term335 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (@lem1685380 (term244 _25982 _25984 _25983 _25981 _25985 _25986) (term247 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1685383 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1685384 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term336 _25982 _25984 _25983 _25981 _25985 _25986) = (term337 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (@lem1685383 (term277 _25982 _25984) (term240 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685386 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1685387 (_25982 : real) (_25984 : real) : (term338 _25982 _25984) = (real_le _25982 _25984).
Proof. exact (@lem1685386 (real_le _25982 _25984)). Qed.
Lemma lem1685388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1685389 (_25982 : real) (_25984 : real) : (term339 _25982 _25984) = (term340 _25982 _25984).
Proof. exact (MK_COMB (@lem1685388) (@lem1685387 _25982 _25984)). Qed.
Lemma lem1685391 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1685392 (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term341 _25983 _25981 _25985 _25986) = (term342 _25983 _25981 _25985 _25986).
Proof. exact (@lem1685391 (term277 _25983 _25981) (term235 _25985 _25986)). Qed.
Lemma lem1685394 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1685395 (_25983 : real) (_25981 : real) : (term338 _25983 _25981) = (real_le _25983 _25981).
Proof. exact (@lem1685394 (real_le _25983 _25981)). Qed.
Lemma lem1685396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1685397 (_25983 : real) (_25981 : real) : (term339 _25983 _25981) = (term340 _25983 _25981).
Proof. exact (MK_COMB (@lem1685396) (@lem1685395 _25983 _25981)). Qed.
Lemma lem1685399 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1685400 (_25985 : real) (_25986 : real) : (term343 _25985 _25986) = (term344 _25985 _25986).
Proof. exact (@lem1685399 (term282 _25985) (term231 _25985 _25986)). Qed.
Lemma lem1685402 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1685403 (_25985 : real) : (term345 _25985) = (term232 _25985).
Proof. exact (@lem1685402 (term232 _25985)). Qed.
Lemma lem1685404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1685405 (_25985 : real) : (term346 _25985) = (term347 _25985).
Proof. exact (MK_COMB (@lem1685404) (@lem1685403 _25985)). Qed.
Lemma lem1685407 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1685408 (_25985 : real) (_25986 : real) : (term348 _25985 _25986) = (term349 _25985 _25986).
Proof. exact (@lem1685407 (term282 _25986) (term52 _25985 _25986)). Qed.
Lemma lem1685410 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1685411 (_25986 : real) : (term345 _25986) = (term232 _25986).
Proof. exact (@lem1685410 (term232 _25986)). Qed.
Lemma lem1685412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1685413 (_25986 : real) : (term346 _25986) = (term347 _25986).
Proof. exact (MK_COMB (@lem1685412) (@lem1685411 _25986)). Qed.
Lemma lem1685415 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1685416 (_25985 : real) (_25986 : real) : (term300 _25985 _25986) = ((real_add _25985 _25986) = term39).
Proof. exact (@lem1685415 ((real_add _25985 _25986) = term39)). Qed.
Lemma lem1685417 (_25985 : real) (_25986 : real) : (term349 _25985 _25986) = (term237 _25985 _25986).
Proof. exact (MK_COMB (@lem1685413 _25986) (@lem1685416 _25985 _25986)). Qed.
Lemma lem1685418 (_25985 : real) (_25986 : real) : (term348 _25985 _25986) = (term237 _25985 _25986).
Proof. exact (TRANS (@lem1685408 _25985 _25986) (@lem1685417 _25985 _25986)). Qed.
Lemma lem1685419 (_25985 : real) (_25986 : real) : (term344 _25985 _25986) = (term242 _25985 _25986).
Proof. exact (MK_COMB (@lem1685405 _25985) (@lem1685418 _25985 _25986)). Qed.
Lemma lem1685420 (_25985 : real) (_25986 : real) : (term343 _25985 _25986) = (term242 _25985 _25986).
Proof. exact (TRANS (@lem1685400 _25985 _25986) (@lem1685419 _25985 _25986)). Qed.
Lemma lem1685421 (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term342 _25983 _25981 _25985 _25986) = (term246 _25983 _25981 _25985 _25986).
Proof. exact (MK_COMB (@lem1685397 _25983 _25981) (@lem1685420 _25985 _25986)). Qed.
Lemma lem1685422 (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term341 _25983 _25981 _25985 _25986) = (term246 _25983 _25981 _25985 _25986).
Proof. exact (TRANS (@lem1685392 _25983 _25981 _25985 _25986) (@lem1685421 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685423 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term337 _25982 _25984 _25983 _25981 _25985 _25986) = (term252 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (MK_COMB (@lem1685389 _25982 _25984) (@lem1685422 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685424 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term336 _25982 _25984 _25983 _25981 _25985 _25986) = (term252 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (TRANS (@lem1685384 _25982 _25984 _25983 _25981 _25985 _25986) (@lem1685423 _25982 _25984 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685425 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1685426 (_25982 : real) (_25984 : real) (_25983 : real) (_25981 : real) (_25985 : real) (_25986 : real) : (term350 _25982 _25984 _25983 _25981 _25985 _25986) = (term351 _25982 _25984 _25983 _25981 _25985 _25986).
Proof. exact (MK_COMB (@lem1685425) (@lem1685424 _25982 _25984 _25983 _25981 _25985 _25986)). Qed.
Lemma lem1685427 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term247 _25982 _25983 _25985 _25984 _25986 _25981) = (term247 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (eq_refl (term247 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1685428 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term335 _25982 _25983 _25985 _25984 _25986 _25981) = (term137 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (MK_COMB (@lem1685426 _25982 _25984 _25983 _25981 _25985 _25986) (@lem1685427 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1685429 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) : (term334 _25982 _25984 _25983 _25981 _25985 _25986) = (term137 _25982 _25983 _25985 _25984 _25986 _25981).
Proof. exact (TRANS (@lem1685381 _25982 _25983 _25985 _25984 _25986 _25981) (@lem1685428 _25982 _25983 _25985 _25984 _25986 _25981)). Qed.
Lemma lem1685431 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term237 u v.
Proof. exact (conj (@lem1684917 a u x v y h1) (@lem1684924 a u x v y h1)). Qed.
Lemma lem1685432 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term242 u v.
Proof. exact (conj (@lem1684910 a u x v y h1) (@lem1685431 a u x v y h1)). Qed.
Lemma lem1685433 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term246 a y u v.
Proof. exact (conj (@lem1684903 a u x v y h1) (@lem1685432 a u x v y h1)). Qed.
Lemma lem1685434 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term164 x a y u v.
Proof. exact (conj (@lem1684896 a u x v y h1) (@lem1685433 a u x v y h1)). Qed.
Lemma lem1685436 (_25982 : real) (_25983 : real) (_25985 : real) (_25984 : real) (_25986 : real) (_25981 : real) (h1 : term119) : term137 _25982 _25983 _25985 _25984 _25986 _25981.
Proof. exact (EQ_MP (@lem1685429 _25982 _25983 _25985 _25984 _25986 _25981) (@lem1685378 _25982 _25984 _25983 _25981 _25985 _25986 h1)). Qed.
Lemma lem1685437 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) : term352 a u x v y.
Proof. exact (@lem1685436 a a u x v y h1). Qed.
Lemma lem1685440 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term163 a u x v y) : term353 a u x v y.
Proof. exact (@lem1685437 a u x v y h1 (@lem1685434 a u x v y h2)). Qed.
Lemma lem1685441 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term163 a u x v y) : term354 a u x v y.
Proof. exact (fun h0 : term355 a u x v y => @lem1685440 a u x v y h1 h2). Qed.
Lemma lem1685443 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1685444 (a : real) (u : real) (x : real) (v : real) (y : real) : (term354 a u x v y) = (term353 a u x v y).
Proof. exact (@lem1685443 (term353 a u x v y)). Qed.
Lemma lem1685445 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term163 a u x v y) : term353 a u x v y.
Proof. exact (EQ_MP (@lem1685444 a u x v y) (@lem1685441 a u x v y h1 h2)). Qed.
Lemma lem1685463 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1685464 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : (term293 _25989 _25990 _25987 _25988) = (term356 _25989 _25990 _25987 _25988).
Proof. exact (@lem1685463 (real_le _25989 _25990) (term57 _25988 _25990) (term277 _25987 _25988)). Qed.
Lemma lem1685482 (_25987 : real) (_25989 : real) : (term58 _25987 _25989) = (term58 _25987 _25989).
Proof. exact (eq_refl (term58 _25987 _25989)). Qed.
Lemma lem1685483 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : (term295 _25989 _25990 _25987 _25988) = (term357 _25989 _25990 _25987 _25988).
Proof. exact (MK_COMB (@lem1685482 _25987 _25989) (@lem1685464 _25989 _25990 _25987 _25988)). Qed.
Lemma lem1685487 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1685488 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : (term357 _25989 _25990 _25987 _25988) = (term358 _25989 _25990 _25987 _25988).
Proof. exact (@lem1685487 (real_le _25989 _25990) (term57 _25987 _25989) (term359 _25990 _25987 _25988)). Qed.
Lemma lem1685518 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : (term295 _25989 _25990 _25987 _25988) = (term358 _25989 _25990 _25987 _25988).
Proof. exact (TRANS (@lem1685483 _25989 _25990 _25987 _25988) (@lem1685488 _25989 _25990 _25987 _25988)). Qed.
Lemma lem1685519 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1685520 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : (term360 _25989 _25990 _25987 _25988) = (term361 _25989 _25990 _25987 _25988).
Proof. exact (MK_COMB (@lem1685519) (@lem1685518 _25989 _25990 _25987 _25988)). Qed.
Lemma lem1685550 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : (term358 _25989 _25990 _25987 _25988) = (term358 _25989 _25990 _25987 _25988).
Proof. exact (eq_refl (term358 _25989 _25990 _25987 _25988)). Qed.
Lemma lem1685551 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : ((term295 _25989 _25990 _25987 _25988) = (term358 _25989 _25990 _25987 _25988)) = ((term358 _25989 _25990 _25987 _25988) = (term358 _25989 _25990 _25987 _25988)).
Proof. exact (MK_COMB (@lem1685520 _25989 _25990 _25987 _25988) (@lem1685550 _25989 _25990 _25987 _25988)). Qed.
Lemma lem1685553 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1685554 (x : Prop) : (x = x) = True.
Proof. exact (@lem1685553 Prop x). Qed.
Lemma lem1685555 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : ((term358 _25989 _25990 _25987 _25988) = (term358 _25989 _25990 _25987 _25988)) = True.
Proof. exact (@lem1685554 (term358 _25989 _25990 _25987 _25988)). Qed.
Lemma lem1685556 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : ((term295 _25989 _25990 _25987 _25988) = (term358 _25989 _25990 _25987 _25988)) = True.
Proof. exact (TRANS (@lem1685551 _25989 _25990 _25987 _25988) (@lem1685555 _25989 _25990 _25987 _25988)). Qed.
Lemma lem1685557 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : True = ((term295 _25989 _25990 _25987 _25988) = (term358 _25989 _25990 _25987 _25988)).
Proof. exact (SYM (@lem1685556 _25989 _25990 _25987 _25988)). Qed.
Lemma lem1685558 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : (term295 _25989 _25990 _25987 _25988) = (term358 _25989 _25990 _25987 _25988).
Proof. exact (EQ_MP (@lem1685557 _25989 _25990 _25987 _25988) (@lem0)). Qed.
Lemma lem1685559 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : term358 _25989 _25990 _25987 _25988.
Proof. exact (EQ_MP (@lem1685558 _25989 _25990 _25987 _25988) (@lem1684755 _25989 _25990 _25987 _25988)). Qed.
Lemma lem1685561 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1685562 (_25987 : real) (_25988 : real) (_25989 : real) (_25990 : real) : (term358 _25989 _25990 _25987 _25988) = (term362 _25987 _25988 _25989 _25990).
Proof. exact (@lem1685561 (term363 _25989 _25990 _25987 _25988) (real_le _25989 _25990)). Qed.
Lemma lem1685564 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1685565 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : (term364 _25989 _25990 _25987 _25988) = (term365 _25989 _25990 _25987 _25988).
Proof. exact (@lem1685564 (term57 _25987 _25989) (term359 _25990 _25987 _25988)). Qed.
Lemma lem1685567 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1685568 (_25987 : real) (_25989 : real) : (term72 _25987 _25989) = (_25987 = _25989).
Proof. exact (@lem1685567 (_25987 = _25989)). Qed.
Lemma lem1685569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1685570 (_25987 : real) (_25989 : real) : (term73 _25987 _25989) = (term74 _25987 _25989).
Proof. exact (MK_COMB (@lem1685569) (@lem1685568 _25987 _25989)). Qed.
Lemma lem1685572 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1685573 (_25990 : real) (_25987 : real) (_25988 : real) : (term366 _25990 _25987 _25988) = (term367 _25990 _25987 _25988).
Proof. exact (@lem1685572 (term57 _25988 _25990) (term277 _25987 _25988)). Qed.
Lemma lem1685575 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1685576 (_25988 : real) (_25990 : real) : (term72 _25988 _25990) = (_25988 = _25990).
Proof. exact (@lem1685575 (_25988 = _25990)). Qed.
Lemma lem1685577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1685578 (_25988 : real) (_25990 : real) : (term73 _25988 _25990) = (term74 _25988 _25990).
Proof. exact (MK_COMB (@lem1685577) (@lem1685576 _25988 _25990)). Qed.
Lemma lem1685580 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1685581 (_25987 : real) (_25988 : real) : (term338 _25987 _25988) = (real_le _25987 _25988).
Proof. exact (@lem1685580 (real_le _25987 _25988)). Qed.
Lemma lem1685582 (_25990 : real) (_25987 : real) (_25988 : real) : (term367 _25990 _25987 _25988) = (term368 _25990 _25987 _25988).
Proof. exact (MK_COMB (@lem1685578 _25988 _25990) (@lem1685581 _25987 _25988)). Qed.
Lemma lem1685583 (_25990 : real) (_25987 : real) (_25988 : real) : (term366 _25990 _25987 _25988) = (term368 _25990 _25987 _25988).
Proof. exact (TRANS (@lem1685573 _25990 _25987 _25988) (@lem1685582 _25990 _25987 _25988)). Qed.
Lemma lem1685584 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : (term365 _25989 _25990 _25987 _25988) = (term369 _25989 _25990 _25987 _25988).
Proof. exact (MK_COMB (@lem1685570 _25987 _25989) (@lem1685583 _25990 _25987 _25988)). Qed.
Lemma lem1685585 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : (term364 _25989 _25990 _25987 _25988) = (term369 _25989 _25990 _25987 _25988).
Proof. exact (TRANS (@lem1685565 _25989 _25990 _25987 _25988) (@lem1685584 _25989 _25990 _25987 _25988)). Qed.
Lemma lem1685586 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1685587 (_25989 : real) (_25990 : real) (_25987 : real) (_25988 : real) : (term370 _25989 _25990 _25987 _25988) = (term371 _25989 _25990 _25987 _25988).
Proof. exact (MK_COMB (@lem1685586) (@lem1685585 _25989 _25990 _25987 _25988)). Qed.
Lemma lem1685588 (_25989 : real) (_25990 : real) : (real_le _25989 _25990) = (real_le _25989 _25990).
Proof. exact (eq_refl (real_le _25989 _25990)). Qed.
Lemma lem1685589 (_25987 : real) (_25988 : real) (_25989 : real) (_25990 : real) : (term362 _25987 _25988 _25989 _25990) = (term372 _25987 _25988 _25989 _25990).
Proof. exact (MK_COMB (@lem1685587 _25989 _25990 _25987 _25988) (@lem1685588 _25989 _25990)). Qed.
Lemma lem1685590 (_25987 : real) (_25988 : real) (_25989 : real) (_25990 : real) : (term358 _25989 _25990 _25987 _25988) = (term372 _25987 _25988 _25989 _25990).
Proof. exact (TRANS (@lem1685562 _25987 _25988 _25989 _25990) (@lem1685589 _25987 _25988 _25989 _25990)). Qed.
Lemma lem1685592 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term163 a u x v y) : term373 a u x v y.
Proof. exact (conj (@lem1684889 u x v y) (@lem1685445 a u x v y h1 h2)). Qed.
Lemma lem1685593 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : term374 a u x v y.
Proof. exact (conj (@lem1684881 a u x v y h2 h3) (@lem1685592 a u x v y h1 h3)). Qed.
Lemma lem1685595 (_25987 : real) (_25988 : real) (_25989 : real) (_25990 : real) : term372 _25987 _25988 _25989 _25990.
Proof. exact (EQ_MP (@lem1685590 _25987 _25988 _25989 _25990) (@lem1685559 _25989 _25990 _25987 _25988)). Qed.
Lemma lem1685596 (a : real) (u : real) (x : real) (v : real) (y : real) : term375 a u x v y.
Proof. exact (@lem1685595 (term31 u v a) (term303 u x v y) a (term303 u x v y)). Qed.
Lemma lem1685599 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : term165 a u x v y.
Proof. exact (@lem1685596 a u x v y (@lem1685593 a u x v y h1 h2 h3)). Qed.
Lemma lem1685600 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : term376 a u x v y.
Proof. exact (fun h0 : term288 a u x v y => @lem1685599 a u x v y h1 h2 h3). Qed.
Lemma lem1685602 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1685603 (a : real) (u : real) (x : real) (v : real) (y : real) : (term376 a u x v y) = (term165 a u x v y).
Proof. exact (@lem1685602 (term165 a u x v y)). Qed.
Lemma lem1685604 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : term165 a u x v y.
Proof. exact (EQ_MP (@lem1685603 a u x v y) (@lem1685600 a u x v y h1 h2 h3)). Qed.
Lemma lem1685607 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1685609 (a : real) (u : real) (x : real) (v : real) (y : real) : (term288 a u x v y) = (term377 a u x v y).
Proof. exact (@lem1685607 (term165 a u x v y)). Qed.
Lemma lem1685612 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term377 a u x v y.
Proof. exact (EQ_MP (@lem1685609 a u x v y) (@lem1684726 a u x v y h1)). Qed.
Lemma lem1685615 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : False.
Proof. exact (@lem1685612 a u x v y h3 (@lem1685604 a u x v y h1 h2 h3)). Qed.
Lemma lem1685616 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : term109.
Proof. exact (fun h0 : ~ False => @lem1685615 a u x v y h1 h2 h3). Qed.
Lemma lem1685618 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1685619 : term109 = False.
Proof. exact (@lem1685618 False). Qed.
Lemma lem1685620 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : False.
Proof. exact (EQ_MP (@lem1685619) (@lem1685616 a u x v y h1 h2 h3)). Qed.
Lemma lem1685621 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : (term163 a u x v y) = False.
Proof. exact (prop_ext (fun h4 : term163 a u x v y => @lem1685620 a u x v y h1 h2 h3) (fun h4 : False => @lem1684531 a u x v y h3)). Qed.
Lemma lem1685622 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : False.
Proof. exact (EQ_MP (@lem1685621 a u x v y h1 h2 h3) (@lem1684531 a u x v y h3)). Qed.
Lemma lem1685623 (a : real) (u : real) (x : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term174 a u x y) : False.
Proof. exact (ex_elim (@lem1684289 a u x y h3) (fun v : real => fun h0 : term173 a u x y v => @lem1685622 a u x v y h1 h2 h0)). Qed.
Lemma lem1685624 (a : real) (x : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term181 a x y) : False.
Proof. exact (ex_elim (@lem1684288 a x y h3) (fun u : real => fun h0 : term180 a x y u => @lem1685623 a u x y h1 h2 h0)). Qed.
Lemma lem1685625 (x : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term188 x y) : False.
Proof. exact (ex_elim (@lem1684287 x y h3) (fun a : real => fun h0 : term187 x y a => @lem1685624 a x y h1 h2 h0)). Qed.
Lemma lem1685626 (x : real) (h1 : term119) (h2 : term122) (h3 : term195 x) : False.
Proof. exact (ex_elim (@lem1684286 x h3) (fun y : real => fun h0 : term194 x y => @lem1685625 x y h1 h2 h0)). Qed.
Lemma lem1685627 (h1 : term119) (h2 : term122) (h3 : term125) : False.
Proof. exact (ex_elim (@lem1684053 h3) (fun x : real => fun h0 : term200 x => @lem1685626 x h1 h2 h0)). Qed.
Lemma lem1685628 (h1 : term122) (h2 : term125) : term130.
Proof. exact (fun h0 : term119 => @lem1685627 h0 h1 h2). Qed.
Lemma lem1685629 : term130 = term131.
Proof. exact (@lem69 term119). Qed.
Lemma lem1685630 (h1 : term122) (h2 : term125) : term131.
Proof. exact (EQ_MP (@lem1685629) (@lem1685628 h1 h2)). Qed.
Lemma lem1685631 (h1 : term125) : term134.
Proof. exact (fun h0 : term122 => @lem1685630 h0 h1). Qed.
Lemma lem1685632 : term136.
Proof. exact (fun h0 : term125 => @lem1685631 h0). Qed.
Lemma lem1685633 : term126.
Proof. exact (EQ_MP (@lem1683908) (@lem1685632)). Qed.
Lemma lem1685635 : term126.
Proof. exact (@lem1683598 (@lem1685633)). Qed.
Lemma lem1685636 (h1 : term125) : term133.
Proof. exact (@lem1685635 (@lem1683583 h1)). Qed.
Lemma lem1685637 (h1 : term125) : term130.
Proof. exact (@lem1685636 h1 (@lem1683578)). Qed.
Lemma lem1685638 (h1 : term125) : False.
Proof. exact (@lem1685637 h1 (@lem1683575)). Qed.
Lemma lem1685639 (h1 : term125) : term125 = False.
Proof. exact (prop_ext (fun h2 : term125 => @lem1685638 h1) (fun h2 : False => @lem1683583 h1)). Qed.
Lemma lem1685640 (h1 : term125) : False.
Proof. exact (EQ_MP (@lem1685639 h1) (@lem1683583 h1)). Qed.
Lemma lem1685641 : term124.
Proof. exact (fun h0 : term125 => @lem1685640 h0). Qed.
Lemma lem1685642 : term123.
Proof. exact (EQ_MP (@lem1683582) (@lem1685641)). Qed.
