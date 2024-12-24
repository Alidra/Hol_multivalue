Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_CONVEX_BOUNDS_LT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_ADD_RDISTRIB_spec.
Require Import REAL_CONVEX_BOUND2_LT_spec.
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
Lemma lem1689762 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1689763 (u : real) (v : real) (a : real) : (term1 u v a) = (term2 u v a).
Proof. exact (@lem1689762 (term1 u v a)). Qed.
Lemma lem1689764 (u : real) (v : real) (a : real) : (term2 u v a) = (term1 u v a).
Proof. exact (SYM (@lem1689763 u v a)). Qed.
Lemma lem1689765 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term3 u v a.
Proof. exact (h1). Qed.
Lemma lem1689768 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term4 u v a.
Proof. exact (h1). Qed.
Lemma lem1689769 (u : real) (v : real) (a : real) : term5 u v a.
Proof. exact (fun h0 : term4 u v a => @lem1689768 u v a h0). Qed.
Lemma lem1689770 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (h1). Qed.
Lemma lem1689771 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term4 u v a.
Proof. exact (h1). Qed.
Lemma lem1689772 (u : real) (v : real) (a : real) (h1 : term4 u v a) (h2 : term5 u v a) : term4 u v a.
Proof. exact (@lem1689770 u v a h2 (@lem1689771 u v a h1)). Qed.
Lemma lem1689773 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term6 u v a.
Proof. exact (fun h0 : term5 u v a => @lem1689772 u v a h1 h0). Qed.
Lemma lem1689774 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (h1). Qed.
Lemma lem1689775 (u : real) (v : real) (a : real) (h1 : term4 u v a) (h2 : term5 u v a) : term4 u v a.
Proof. exact (@lem1689773 u v a h1 (@lem1689774 u v a h2)). Qed.
Lemma lem1689776 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (fun h0 : term4 u v a => @lem1689775 u v a h0 h1). Qed.
Lemma lem1689777 (u : real) (v : real) (a : real) : term7 u v a.
Proof. exact (fun h0 : term5 u v a => @lem1689776 u v a h0). Qed.
Lemma lem1689780 (u : real) (v : real) (a : real) : term5 u v a.
Proof. exact (@lem1689777 u v a (@lem1689769 u v a)). Qed.
Lemma lem1689812 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1689813 : term8 = term9.
Proof. exact (@lem1689812 term10). Qed.
Lemma lem1689818 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1689819 : term12 = term13.
Proof. exact (MK_COMB (@lem1689818) (@lem1689813)). Qed.
Lemma lem1689822 (u : real) (v : real) (a : real) : (term14 u v a) = (term14 u v a).
Proof. exact (eq_refl (term14 u v a)). Qed.
Lemma lem1689823 (u : real) (v : real) (a : real) : (term4 u v a) = (term15 u v a).
Proof. exact (MK_COMB (@lem1689822 u v a) (@lem1689819)). Qed.
Lemma lem1689826 (v : real) (a : real) : (term16 v a) = (term17 v a).
Proof. exact (fun_ext (fun u : real => @lem1689823 u v a)). Qed.
Lemma lem1689827 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1689828 (v : real) (a : real) : (term18 v a) = (term19 v a).
Proof. exact (MK_COMB (@lem1689827) (@lem1689826 v a)). Qed.
Lemma lem1689833 (a : real) : (term20 a) = (term21 a).
Proof. exact (fun_ext (fun v : real => @lem1689828 v a)). Qed.
Lemma lem1689834 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1689835 (a : real) : (term22 a) = (term23 a).
Proof. exact (MK_COMB (@lem1689834) (@lem1689833 a)). Qed.
Lemma lem1689840 : term24 = term25.
Proof. exact (fun_ext (fun a : real => @lem1689835 a)). Qed.
Lemma lem1689841 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1689850 : term26 = term27.
Proof. exact (MK_COMB (@lem1689841) (@lem1689840)). Qed.
Lemma lem1689851 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1689852 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1689851 x)). Qed.
Lemma lem1689853 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1689854 : term10 = term10.
Proof. exact (MK_COMB (@lem1689853) (@lem1689852)). Qed.
Lemma lem1689855 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1689856 : term9 = term9.
Proof. exact (MK_COMB (@lem1689855) (@lem1689854)). Qed.
Lemma lem1689857 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1689858 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1689857 x y z)). Qed.
Lemma lem1689859 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1689860 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1689859) (@lem1689858 x y)). Qed.
Lemma lem1689861 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1689860 x y)). Qed.
Lemma lem1689862 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1689863 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1689862) (@lem1689861 x)). Qed.
Lemma lem1689864 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1689863 x)). Qed.
Lemma lem1689865 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1689866 : term37 = term37.
Proof. exact (MK_COMB (@lem1689865) (@lem1689864)). Qed.
Lemma lem1689867 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1689868 : term11 = term11.
Proof. exact (MK_COMB (@lem1689867) (@lem1689866)). Qed.
Lemma lem1689869 : term13 = term13.
Proof. exact (MK_COMB (@lem1689868) (@lem1689856)). Qed.
Lemma lem1689878 (u : real) (v : real) (a : real) : (term14 u v a) = (term14 u v a).
Proof. exact (eq_refl (term14 u v a)). Qed.
Lemma lem1689879 (u : real) (v : real) (a : real) : (term15 u v a) = (term15 u v a).
Proof. exact (MK_COMB (@lem1689878 u v a) (@lem1689869)). Qed.
Lemma lem1689880 (v : real) (a : real) : (term17 v a) = (term17 v a).
Proof. exact (fun_ext (fun u : real => @lem1689879 u v a)). Qed.
Lemma lem1689881 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1689882 (v : real) (a : real) : (term19 v a) = (term19 v a).
Proof. exact (MK_COMB (@lem1689881) (@lem1689880 v a)). Qed.
Lemma lem1689883 (a : real) : (term21 a) = (term21 a).
Proof. exact (fun_ext (fun v : real => @lem1689882 v a)). Qed.
Lemma lem1689884 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1689885 (a : real) : (term23 a) = (term23 a).
Proof. exact (MK_COMB (@lem1689884) (@lem1689883 a)). Qed.
Lemma lem1689886 : term25 = term25.
Proof. exact (fun_ext (fun a : real => @lem1689885 a)). Qed.
Lemma lem1689887 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1689888 : term27 = term27.
Proof. exact (MK_COMB (@lem1689887) (@lem1689886)). Qed.
Lemma lem1689939 : term26 = term27.
Proof. exact (TRANS (@lem1689850) (@lem1689888)). Qed.
Lemma lem1689940 : term27 = term26.
Proof. exact (SYM (@lem1689939)). Qed.
Lemma lem1689941 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term3 u v a.
Proof. exact (h1). Qed.
Lemma lem1689942 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem1689943 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1689954 (u : real) (v : real) (a : real) : (term3 u v a) = (term38 u v a).
Proof. exact (@lem17362 ((real_add u v) = term39) ((term31 u v a) = a)). Qed.
Lemma lem1689956 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1689957 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1689956 x y z)). Qed.
Lemma lem1689958 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1689959 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1689958) (@lem1689957 x y)). Qed.
Lemma lem1689960 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1689959 x y)). Qed.
Lemma lem1689961 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1689962 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1689961) (@lem1689960 x)). Qed.
Lemma lem1689963 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1689962 x)). Qed.
Lemma lem1689964 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1689981 : term37 = term37.
Proof. exact (MK_COMB (@lem1689964) (@lem1689963)). Qed.
Lemma lem1689982 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1689981) (@lem1689942 h1)). Qed.
Lemma lem1689983 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1689984 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1689983 x)). Qed.
Lemma lem1689985 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1689994 : term10 = term10.
Proof. exact (MK_COMB (@lem1689985) (@lem1689984)). Qed.
Lemma lem1689995 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1689994) (@lem1689943 h1)). Qed.
Lemma lem1690033 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term38 u v a.
Proof. exact (EQ_MP (@lem1689954 u v a) (@lem1689941 u v a h1)). Qed.
Lemma lem1690058 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1690059 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1690058 x y z)). Qed.
Lemma lem1690060 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690061 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1690060) (@lem1690059 x y)). Qed.
Lemma lem1690062 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1690061 x y)). Qed.
Lemma lem1690063 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690064 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1690063) (@lem1690062 x)). Qed.
Lemma lem1690065 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1690064 x)). Qed.
Lemma lem1690066 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690067 : term37 = term37.
Proof. exact (MK_COMB (@lem1690066) (@lem1690065)). Qed.
Lemma lem1690068 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1690067) (@lem1689982 h1)). Qed.
Lemma lem1690083 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1690084 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1690083 x)). Qed.
Lemma lem1690085 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690086 : term10 = term10.
Proof. exact (MK_COMB (@lem1690085) (@lem1690084)). Qed.
Lemma lem1690087 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1690086) (@lem1689995 h1)). Qed.
Lemma lem1690091 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1690092 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1690091 x y z)). Qed.
Lemma lem1690093 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690094 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1690093) (@lem1690092 x y)). Qed.
Lemma lem1690095 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1690094 x y)). Qed.
Lemma lem1690096 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690097 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1690096) (@lem1690095 x)). Qed.
Lemma lem1690098 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1690097 x)). Qed.
Lemma lem1690099 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690101 : term37 = term37.
Proof. exact (MK_COMB (@lem1690099) (@lem1690098)). Qed.
Lemma lem1690102 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1690101) (@lem1690068 h1)). Qed.
Lemma lem1690104 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1690105 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1690104 x)). Qed.
Lemma lem1690106 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690108 : term10 = term10.
Proof. exact (MK_COMB (@lem1690106) (@lem1690105)). Qed.
Lemma lem1690109 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1690108) (@lem1690087 h1)). Qed.
Lemma lem1690118 (_26077 : real) (h1 : term37) : term40 _26077.
Proof. exact (@lem1690102 h1 _26077). Qed.
Lemma lem1690119 (_26077 : real) : (term40 _26077) = (term35 _26077).
Proof. exact (eq_refl (term40 _26077)). Qed.
Lemma lem1690120 (_26077 : real) (h1 : term37) : term35 _26077.
Proof. exact (EQ_MP (@lem1690119 _26077) (@lem1690118 _26077 h1)). Qed.
Lemma lem1690121 (_26077 : real) (_26078 : real) (h1 : term37) : term41 _26077 _26078.
Proof. exact (@lem1690120 _26077 h1 _26078). Qed.
Lemma lem1690122 (_26077 : real) (_26078 : real) : (term41 _26077 _26078) = (term33 _26077 _26078).
Proof. exact (eq_refl (term41 _26077 _26078)). Qed.
Lemma lem1690123 (_26077 : real) (_26078 : real) (h1 : term37) : term33 _26077 _26078.
Proof. exact (EQ_MP (@lem1690122 _26077 _26078) (@lem1690121 _26077 _26078 h1)). Qed.
Lemma lem1690124 (_26077 : real) (_26078 : real) (_26079 : real) (h1 : term37) : term42 _26077 _26078 _26079.
Proof. exact (@lem1690123 _26077 _26078 h1 _26079). Qed.
Lemma lem1690125 (_26077 : real) (_26078 : real) (_26079 : real) : (term42 _26077 _26078 _26079) = ((term30 _26077 _26078 _26079) = (term31 _26077 _26078 _26079)).
Proof. exact (eq_refl (term42 _26077 _26078 _26079)). Qed.
Lemma lem1690127 (_26080 : real) (h1 : term10) : term43 _26080.
Proof. exact (@lem1690109 h1 _26080). Qed.
Lemma lem1690128 (_26080 : real) : (term43 _26080) = ((term28 _26080) = _26080).
Proof. exact (eq_refl (term43 _26080)). Qed.
Lemma lem1690137 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term44 u v a.
Proof. exact (proj2 (@lem1690033 u v a h1)). Qed.
Lemma lem1690162 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1690163 (_26087 : real) (_26089 : real) (h1 : _26087 = _26089) : _26087 = _26089.
Proof. exact (h1). Qed.
Lemma lem1690164 (_26088 : real) (_26090 : real) (h1 : _26088 = _26090) : _26088 = _26090.
Proof. exact (h1). Qed.
Lemma lem1690165 (_26087 : real) (_26089 : real) (h1 : _26087 = _26089) : (real_mul _26087) = (real_mul _26089).
Proof. exact (MK_COMB (@lem1690162) (@lem1690163 _26087 _26089 h1)). Qed.
Lemma lem1690166 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) (h1 : _26087 = _26089) (h2 : _26088 = _26090) : (real_mul _26087 _26088) = (real_mul _26089 _26090).
Proof. exact (MK_COMB (@lem1690165 _26087 _26089 h1) (@lem1690164 _26088 _26090 h2)). Qed.
Lemma lem1690167 (_26088 : real) (_26090 : real) (_26087 : real) (_26089 : real) (h1 : _26087 = _26089) : term45 _26087 _26088 _26089 _26090.
Proof. exact (fun h0 : _26088 = _26090 => @lem1690166 _26087 _26089 _26088 _26090 h1 h0). Qed.
Lemma lem1690169 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1690170 (_26087 : real) (_26088 : real) (_26089 : real) (_26090 : real) : (term45 _26087 _26088 _26089 _26090) = (term47 _26087 _26088 _26089 _26090).
Proof. exact (@lem1690169 (_26088 = _26090) ((real_mul _26087 _26088) = (real_mul _26089 _26090))). Qed.
Lemma lem1690171 (_26088 : real) (_26090 : real) (_26087 : real) (_26089 : real) (h1 : _26087 = _26089) : term47 _26087 _26088 _26089 _26090.
Proof. exact (EQ_MP (@lem1690170 _26087 _26088 _26089 _26090) (@lem1690167 _26088 _26090 _26087 _26089 h1)). Qed.
Lemma lem1690172 (_26087 : real) (_26088 : real) (_26089 : real) (_26090 : real) : term48 _26087 _26088 _26089 _26090.
Proof. exact (fun h0 : _26087 = _26089 => @lem1690171 _26088 _26090 _26087 _26089 h0). Qed.
Lemma lem1690174 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1690175 (_26087 : real) (_26088 : real) (_26089 : real) (_26090 : real) : (term48 _26087 _26088 _26089 _26090) = (term49 _26087 _26088 _26089 _26090).
Proof. exact (@lem1690174 (_26087 = _26089) (term47 _26087 _26088 _26089 _26090)). Qed.
Lemma lem1690176 (_26087 : real) (_26088 : real) (_26089 : real) (_26090 : real) : term49 _26087 _26088 _26089 _26090.
Proof. exact (EQ_MP (@lem1690175 _26087 _26088 _26089 _26090) (@lem1690172 _26087 _26088 _26089 _26090)). Qed.
Lemma lem1690193 (x : real) (y : real) (z : real) : term50 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1690197 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (real_add u v) = term39.
Proof. exact (proj1 (@lem1690033 u v a h1)). Qed.
Lemma lem1690198 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1690197 u v a h1). Qed.
Lemma lem1690200 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1690201 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1690200 ((real_add u v) = term39)). Qed.
Lemma lem1690202 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1690201 u v) (@lem1690198 u v a h1)). Qed.
Lemma lem1690204 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1690205 (a : real) : a = a.
Proof. exact (@lem1690204 a). Qed.
Lemma lem1690206 (a : real) : term54 a.
Proof. exact (fun h0 : term55 a => @lem1690205 a). Qed.
Lemma lem1690208 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1690209 (a : real) : (term54 a) = (a = a).
Proof. exact (@lem1690208 (a = a)). Qed.
Lemma lem1690210 (a : real) : a = a.
Proof. exact (EQ_MP (@lem1690209 a) (@lem1690206 a)). Qed.
Lemma lem1690228 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1690229 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) : (term47 _26087 _26088 _26089 _26090) = (term56 _26087 _26089 _26088 _26090).
Proof. exact (@lem1690228 ((real_mul _26087 _26088) = (real_mul _26089 _26090)) (term57 _26088 _26090)). Qed.
Lemma lem1690239 (_26087 : real) (_26089 : real) : (term58 _26087 _26089) = (term58 _26087 _26089).
Proof. exact (eq_refl (term58 _26087 _26089)). Qed.
Lemma lem1690240 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) : (term49 _26087 _26088 _26089 _26090) = (term59 _26087 _26089 _26088 _26090).
Proof. exact (MK_COMB (@lem1690239 _26087 _26089) (@lem1690229 _26087 _26089 _26088 _26090)). Qed.
Lemma lem1690244 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1690245 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) : (term59 _26087 _26089 _26088 _26090) = (term61 _26087 _26089 _26088 _26090).
Proof. exact (@lem1690244 ((real_mul _26087 _26088) = (real_mul _26089 _26090)) (term57 _26087 _26089) (term57 _26088 _26090)). Qed.
Lemma lem1690267 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) : (term49 _26087 _26088 _26089 _26090) = (term61 _26087 _26089 _26088 _26090).
Proof. exact (TRANS (@lem1690240 _26087 _26089 _26088 _26090) (@lem1690245 _26087 _26089 _26088 _26090)). Qed.
Lemma lem1690268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1690269 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) : (term62 _26087 _26088 _26089 _26090) = (term63 _26087 _26089 _26088 _26090).
Proof. exact (MK_COMB (@lem1690268) (@lem1690267 _26087 _26089 _26088 _26090)). Qed.
Lemma lem1690291 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) : (term61 _26087 _26089 _26088 _26090) = (term61 _26087 _26089 _26088 _26090).
Proof. exact (eq_refl (term61 _26087 _26089 _26088 _26090)). Qed.
Lemma lem1690292 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) : ((term49 _26087 _26088 _26089 _26090) = (term61 _26087 _26089 _26088 _26090)) = ((term61 _26087 _26089 _26088 _26090) = (term61 _26087 _26089 _26088 _26090)).
Proof. exact (MK_COMB (@lem1690269 _26087 _26089 _26088 _26090) (@lem1690291 _26087 _26089 _26088 _26090)). Qed.
Lemma lem1690294 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1690295 (x : Prop) : (x = x) = True.
Proof. exact (@lem1690294 Prop x). Qed.
Lemma lem1690296 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) : ((term61 _26087 _26089 _26088 _26090) = (term61 _26087 _26089 _26088 _26090)) = True.
Proof. exact (@lem1690295 (term61 _26087 _26089 _26088 _26090)). Qed.
Lemma lem1690297 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) : ((term49 _26087 _26088 _26089 _26090) = (term61 _26087 _26089 _26088 _26090)) = True.
Proof. exact (TRANS (@lem1690292 _26087 _26089 _26088 _26090) (@lem1690296 _26087 _26089 _26088 _26090)). Qed.
Lemma lem1690298 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) : True = ((term49 _26087 _26088 _26089 _26090) = (term61 _26087 _26089 _26088 _26090)).
Proof. exact (SYM (@lem1690297 _26087 _26089 _26088 _26090)). Qed.
Lemma lem1690299 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) : (term49 _26087 _26088 _26089 _26090) = (term61 _26087 _26089 _26088 _26090).
Proof. exact (EQ_MP (@lem1690298 _26087 _26089 _26088 _26090) (@lem0)). Qed.
Lemma lem1690300 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) : term61 _26087 _26089 _26088 _26090.
Proof. exact (EQ_MP (@lem1690299 _26087 _26089 _26088 _26090) (@lem1690176 _26087 _26088 _26089 _26090)). Qed.
Lemma lem1690302 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1690303 (_26087 : real) (_26088 : real) (_26089 : real) (_26090 : real) : (term61 _26087 _26089 _26088 _26090) = (term65 _26087 _26088 _26089 _26090).
Proof. exact (@lem1690302 (term66 _26087 _26089 _26088 _26090) ((real_mul _26087 _26088) = (real_mul _26089 _26090))). Qed.
Lemma lem1690305 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1690306 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) : (term69 _26087 _26089 _26088 _26090) = (term70 _26087 _26089 _26088 _26090).
Proof. exact (@lem1690305 (term57 _26087 _26089) (term57 _26088 _26090)). Qed.
Lemma lem1690308 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1690309 (_26087 : real) (_26089 : real) : (term72 _26087 _26089) = (_26087 = _26089).
Proof. exact (@lem1690308 (_26087 = _26089)). Qed.
Lemma lem1690310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1690311 (_26087 : real) (_26089 : real) : (term73 _26087 _26089) = (term74 _26087 _26089).
Proof. exact (MK_COMB (@lem1690310) (@lem1690309 _26087 _26089)). Qed.
Lemma lem1690313 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1690314 (_26088 : real) (_26090 : real) : (term72 _26088 _26090) = (_26088 = _26090).
Proof. exact (@lem1690313 (_26088 = _26090)). Qed.
Lemma lem1690315 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) : (term70 _26087 _26089 _26088 _26090) = (term75 _26087 _26089 _26088 _26090).
Proof. exact (MK_COMB (@lem1690311 _26087 _26089) (@lem1690314 _26088 _26090)). Qed.
Lemma lem1690316 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) : (term69 _26087 _26089 _26088 _26090) = (term75 _26087 _26089 _26088 _26090).
Proof. exact (TRANS (@lem1690306 _26087 _26089 _26088 _26090) (@lem1690315 _26087 _26089 _26088 _26090)). Qed.
Lemma lem1690317 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1690318 (_26087 : real) (_26089 : real) (_26088 : real) (_26090 : real) : (term76 _26087 _26089 _26088 _26090) = (term77 _26087 _26089 _26088 _26090).
Proof. exact (MK_COMB (@lem1690317) (@lem1690316 _26087 _26089 _26088 _26090)). Qed.
Lemma lem1690319 (_26087 : real) (_26088 : real) (_26089 : real) (_26090 : real) : ((real_mul _26087 _26088) = (real_mul _26089 _26090)) = ((real_mul _26087 _26088) = (real_mul _26089 _26090)).
Proof. exact (eq_refl ((real_mul _26087 _26088) = (real_mul _26089 _26090))). Qed.
Lemma lem1690320 (_26087 : real) (_26088 : real) (_26089 : real) (_26090 : real) : (term65 _26087 _26088 _26089 _26090) = (term78 _26087 _26088 _26089 _26090).
Proof. exact (MK_COMB (@lem1690318 _26087 _26089 _26088 _26090) (@lem1690319 _26087 _26088 _26089 _26090)). Qed.
Lemma lem1690321 (_26087 : real) (_26088 : real) (_26089 : real) (_26090 : real) : (term61 _26087 _26089 _26088 _26090) = (term78 _26087 _26088 _26089 _26090).
Proof. exact (TRANS (@lem1690303 _26087 _26088 _26089 _26090) (@lem1690320 _26087 _26088 _26089 _26090)). Qed.
Lemma lem1690323 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term79 u v a.
Proof. exact (conj (@lem1690202 u v a h1) (@lem1690210 a)). Qed.
Lemma lem1690325 (_26087 : real) (_26088 : real) (_26089 : real) (_26090 : real) : term78 _26087 _26088 _26089 _26090.
Proof. exact (EQ_MP (@lem1690321 _26087 _26088 _26089 _26090) (@lem1690300 _26087 _26089 _26088 _26090)). Qed.
Lemma lem1690326 (u : real) (v : real) (a : real) : term80 u v a.
Proof. exact (@lem1690325 (real_add u v) a term39 a). Qed.
Lemma lem1690329 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term30 u v a) = (term28 a).
Proof. exact (@lem1690326 u v a (@lem1690323 u v a h1)). Qed.
Lemma lem1690330 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term81 u v a.
Proof. exact (fun h0 : term82 u v a => @lem1690329 u v a h1). Qed.
Lemma lem1690332 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1690333 (u : real) (v : real) (a : real) : (term81 u v a) = ((term30 u v a) = (term28 a)).
Proof. exact (@lem1690332 ((term30 u v a) = (term28 a))). Qed.
Lemma lem1690334 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term30 u v a) = (term28 a).
Proof. exact (EQ_MP (@lem1690333 u v a) (@lem1690330 u v a h1)). Qed.
Lemma lem1690336 (_26077 : real) (_26078 : real) (_26079 : real) (h1 : term37) : (term30 _26077 _26078 _26079) = (term31 _26077 _26078 _26079).
Proof. exact (EQ_MP (@lem1690125 _26077 _26078 _26079) (@lem1690124 _26077 _26078 _26079 h1)). Qed.
Lemma lem1690337 (u : real) (v : real) (a : real) (h1 : term37) : (term30 u v a) = (term31 u v a).
Proof. exact (@lem1690336 u v a h1). Qed.
Lemma lem1690338 (u : real) (v : real) (a : real) (h1 : term37) : term83 u v a.
Proof. exact (fun h0 : term84 u v a => @lem1690337 u v a h1). Qed.
Lemma lem1690340 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1690341 (u : real) (v : real) (a : real) : (term83 u v a) = ((term30 u v a) = (term31 u v a)).
Proof. exact (@lem1690340 ((term30 u v a) = (term31 u v a))). Qed.
Lemma lem1690342 (u : real) (v : real) (a : real) (h1 : term37) : (term30 u v a) = (term31 u v a).
Proof. exact (EQ_MP (@lem1690341 u v a) (@lem1690338 u v a h1)). Qed.
Lemma lem1690360 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1690361 (y : real) (x : real) (z : real) : (term85 x y z) = (term86 y x z).
Proof. exact (@lem1690360 (y = z) (term57 x z)). Qed.
Lemma lem1690371 (x : real) (y : real) : (term58 x y) = (term58 x y).
Proof. exact (eq_refl (term58 x y)). Qed.
Lemma lem1690372 (y : real) (x : real) (z : real) : (term50 x y z) = (term87 y x z).
Proof. exact (MK_COMB (@lem1690371 x y) (@lem1690361 y x z)). Qed.
Lemma lem1690376 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1690377 (y : real) (x : real) (z : real) : (term87 y x z) = (term88 y x z).
Proof. exact (@lem1690376 (y = z) (term57 x y) (term57 x z)). Qed.
Lemma lem1690399 (y : real) (x : real) (z : real) : (term50 x y z) = (term88 y x z).
Proof. exact (TRANS (@lem1690372 y x z) (@lem1690377 y x z)). Qed.
Lemma lem1690400 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1690401 (y : real) (x : real) (z : real) : (term89 x y z) = (term90 y x z).
Proof. exact (MK_COMB (@lem1690400) (@lem1690399 y x z)). Qed.
Lemma lem1690423 (y : real) (x : real) (z : real) : (term88 y x z) = (term88 y x z).
Proof. exact (eq_refl (term88 y x z)). Qed.
Lemma lem1690424 (y : real) (x : real) (z : real) : ((term50 x y z) = (term88 y x z)) = ((term88 y x z) = (term88 y x z)).
Proof. exact (MK_COMB (@lem1690401 y x z) (@lem1690423 y x z)). Qed.
Lemma lem1690426 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1690427 (x : Prop) : (x = x) = True.
Proof. exact (@lem1690426 Prop x). Qed.
Lemma lem1690428 (y : real) (x : real) (z : real) : ((term88 y x z) = (term88 y x z)) = True.
Proof. exact (@lem1690427 (term88 y x z)). Qed.
Lemma lem1690429 (y : real) (x : real) (z : real) : ((term50 x y z) = (term88 y x z)) = True.
Proof. exact (TRANS (@lem1690424 y x z) (@lem1690428 y x z)). Qed.
Lemma lem1690430 (y : real) (x : real) (z : real) : True = ((term50 x y z) = (term88 y x z)).
Proof. exact (SYM (@lem1690429 y x z)). Qed.
Lemma lem1690431 (y : real) (x : real) (z : real) : (term50 x y z) = (term88 y x z).
Proof. exact (EQ_MP (@lem1690430 y x z) (@lem0)). Qed.
Lemma lem1690432 (y : real) (x : real) (z : real) : term88 y x z.
Proof. exact (EQ_MP (@lem1690431 y x z) (@lem1690193 x y z)). Qed.
Lemma lem1690434 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1690435 (x : real) (y : real) (z : real) : (term88 y x z) = (term91 x y z).
Proof. exact (@lem1690434 (term92 y x z) (y = z)). Qed.
Lemma lem1690437 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1690438 (y : real) (x : real) (z : real) : (term93 y x z) = (term94 y x z).
Proof. exact (@lem1690437 (term57 x y) (term57 x z)). Qed.
Lemma lem1690440 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1690441 (x : real) (y : real) : (term72 x y) = (x = y).
Proof. exact (@lem1690440 (x = y)). Qed.
Lemma lem1690442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1690443 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1690442) (@lem1690441 x y)). Qed.
Lemma lem1690445 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1690446 (x : real) (z : real) : (term72 x z) = (x = z).
Proof. exact (@lem1690445 (x = z)). Qed.
Lemma lem1690447 (y : real) (x : real) (z : real) : (term94 y x z) = (term95 y x z).
Proof. exact (MK_COMB (@lem1690443 x y) (@lem1690446 x z)). Qed.
Lemma lem1690448 (y : real) (x : real) (z : real) : (term93 y x z) = (term95 y x z).
Proof. exact (TRANS (@lem1690438 y x z) (@lem1690447 y x z)). Qed.
Lemma lem1690449 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1690450 (y : real) (x : real) (z : real) : (term96 y x z) = (term97 y x z).
Proof. exact (MK_COMB (@lem1690449) (@lem1690448 y x z)). Qed.
Lemma lem1690451 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1690452 (x : real) (y : real) (z : real) : (term91 x y z) = (term98 x y z).
Proof. exact (MK_COMB (@lem1690450 y x z) (@lem1690451 y z)). Qed.
Lemma lem1690453 (x : real) (y : real) (z : real) : (term88 y x z) = (term98 x y z).
Proof. exact (TRANS (@lem1690435 x y z) (@lem1690452 x y z)). Qed.
Lemma lem1690455 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term99 u v a.
Proof. exact (conj (@lem1690334 u v a h2) (@lem1690342 u v a h1)). Qed.
Lemma lem1690457 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (EQ_MP (@lem1690453 x y z) (@lem1690432 y x z)). Qed.
Lemma lem1690458 (u : real) (v : real) (a : real) : term100 u v a.
Proof. exact (@lem1690457 (term30 u v a) (term28 a) (term31 u v a)). Qed.
Lemma lem1690461 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : (term28 a) = (term31 u v a).
Proof. exact (@lem1690458 u v a (@lem1690455 u v a h1 h2)). Qed.
Lemma lem1690462 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term101 u v a.
Proof. exact (fun h0 : term102 u v a => @lem1690461 u v a h1 h2). Qed.
Lemma lem1690464 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1690465 (u : real) (v : real) (a : real) : (term101 u v a) = ((term28 a) = (term31 u v a)).
Proof. exact (@lem1690464 ((term28 a) = (term31 u v a))). Qed.
Lemma lem1690466 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : (term28 a) = (term31 u v a).
Proof. exact (EQ_MP (@lem1690465 u v a) (@lem1690462 u v a h1 h2)). Qed.
Lemma lem1690468 (_26080 : real) (h1 : term10) : (term28 _26080) = _26080.
Proof. exact (EQ_MP (@lem1690128 _26080) (@lem1690127 _26080 h1)). Qed.
Lemma lem1690469 (a : real) (h1 : term10) : (term28 a) = a.
Proof. exact (@lem1690468 a h1). Qed.
Lemma lem1690470 (a : real) (h1 : term10) : term103 a.
Proof. exact (fun h0 : term104 a => @lem1690469 a h1). Qed.
Lemma lem1690472 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1690473 (a : real) : (term103 a) = ((term28 a) = a).
Proof. exact (@lem1690472 ((term28 a) = a)). Qed.
Lemma lem1690474 (a : real) (h1 : term10) : (term28 a) = a.
Proof. exact (EQ_MP (@lem1690473 a) (@lem1690470 a h1)). Qed.
Lemma lem1690475 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term105 u v a.
Proof. exact (conj (@lem1690466 u v a h1 h3) (@lem1690474 a h2)). Qed.
Lemma lem1690477 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (EQ_MP (@lem1690453 x y z) (@lem1690432 y x z)). Qed.
Lemma lem1690478 (u : real) (v : real) (a : real) : term106 u v a.
Proof. exact (@lem1690477 (term28 a) (term31 u v a) a). Qed.
Lemma lem1690481 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : (term31 u v a) = a.
Proof. exact (@lem1690478 u v a (@lem1690475 u v a h1 h2 h3)). Qed.
Lemma lem1690482 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term107 u v a.
Proof. exact (fun h0 : term44 u v a => @lem1690481 u v a h1 h2 h3). Qed.
Lemma lem1690484 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1690485 (u : real) (v : real) (a : real) : (term107 u v a) = ((term31 u v a) = a).
Proof. exact (@lem1690484 ((term31 u v a) = a)). Qed.
Lemma lem1690486 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : (term31 u v a) = a.
Proof. exact (EQ_MP (@lem1690485 u v a) (@lem1690482 u v a h1 h2 h3)). Qed.
Lemma lem1690489 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1690491 (u : real) (v : real) (a : real) : (term44 u v a) = (term108 u v a).
Proof. exact (@lem1690489 ((term31 u v a) = a)). Qed.
Lemma lem1690494 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term108 u v a.
Proof. exact (EQ_MP (@lem1690491 u v a) (@lem1690137 u v a h1)). Qed.
Lemma lem1690497 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (@lem1690494 u v a h3 (@lem1690486 u v a h1 h2 h3)). Qed.
Lemma lem1690498 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term109.
Proof. exact (fun h0 : ~ False => @lem1690497 u v a h1 h2 h3). Qed.
Lemma lem1690500 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1690501 : term109 = False.
Proof. exact (@lem1690500 False). Qed.
Lemma lem1690502 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1690501) (@lem1690498 u v a h1 h2 h3)). Qed.
Lemma lem1690503 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1690502 u v a h1 h2 h3) (fun h4 : False => @lem1690109 h2)). Qed.
Lemma lem1690504 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1690503 u v a h1 h2 h3) (@lem1690109 h2)). Qed.
Lemma lem1690505 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1690504 u v a h1 h2 h3) (fun h4 : False => @lem1690102 h1)). Qed.
Lemma lem1690506 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1690505 u v a h1 h2 h3) (@lem1690102 h1)). Qed.
Lemma lem1690507 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1690506 u v a h1 h2 h3) (fun h4 : False => @lem1690087 h2)). Qed.
Lemma lem1690508 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1690507 u v a h1 h2 h3) (@lem1690087 h2)). Qed.
Lemma lem1690509 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1690508 u v a h1 h2 h3) (fun h4 : False => @lem1690068 h1)). Qed.
Lemma lem1690510 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1690509 u v a h1 h2 h3) (@lem1690068 h1)). Qed.
Lemma lem1690511 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1690510 u v a h1 h2 h3) (fun h4 : False => @lem1689995 h2)). Qed.
Lemma lem1690512 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1690511 u v a h1 h2 h3) (@lem1689995 h2)). Qed.
Lemma lem1690513 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1690512 u v a h1 h2 h3) (fun h4 : False => @lem1689982 h1)). Qed.
Lemma lem1690514 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1690513 u v a h1 h2 h3) (@lem1689982 h1)). Qed.
Lemma lem1690515 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term8.
Proof. exact (fun h0 : term10 => @lem1690514 u v a h1 h0 h2). Qed.
Lemma lem1690516 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1690517 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term9.
Proof. exact (EQ_MP (@lem1690516) (@lem1690515 u v a h1 h2)). Qed.
Lemma lem1690518 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term13.
Proof. exact (fun h0 : term37 => @lem1690517 u v a h0 h1). Qed.
Lemma lem1690519 (u : real) (v : real) (a : real) : term15 u v a.
Proof. exact (fun h0 : term3 u v a => @lem1690518 u v a h0). Qed.
Lemma lem1690524 (v : real) (a : real) : term19 v a.
Proof. exact (fun u : real => @lem1690519 u v a). Qed.
Lemma lem1690529 (a : real) : term23 a.
Proof. exact (fun v : real => @lem1690524 v a). Qed.
Lemma lem1690534 : term27.
Proof. exact (fun a : real => @lem1690529 a). Qed.
Lemma lem1690535 : term26.
Proof. exact (EQ_MP (@lem1689940) (@lem1690534)). Qed.
Lemma lem1690536 (a : real) : term110 a.
Proof. exact (@lem1690535 a). Qed.
Lemma lem1690537 (a : real) : (term110 a) = (term22 a).
Proof. exact (eq_refl (term110 a)). Qed.
Lemma lem1690538 (a : real) : term22 a.
Proof. exact (EQ_MP (@lem1690537 a) (@lem1690536 a)). Qed.
Lemma lem1690539 (a : real) (v : real) : term111 a v.
Proof. exact (@lem1690538 a v). Qed.
Lemma lem1690540 (v : real) (a : real) : (term111 a v) = (term18 v a).
Proof. exact (eq_refl (term111 a v)). Qed.
Lemma lem1690541 (v : real) (a : real) : term18 v a.
Proof. exact (EQ_MP (@lem1690540 v a) (@lem1690539 a v)). Qed.
Lemma lem1690542 (v : real) (a : real) (u : real) : term112 v a u.
Proof. exact (@lem1690541 v a u). Qed.
Lemma lem1690543 (u : real) (v : real) (a : real) : (term112 v a u) = (term4 u v a).
Proof. exact (eq_refl (term112 v a u)). Qed.
Lemma lem1690544 (u : real) (v : real) (a : real) : term4 u v a.
Proof. exact (EQ_MP (@lem1690543 u v a) (@lem1690542 v a u)). Qed.
Lemma lem1690546 (u : real) (v : real) (a : real) : term4 u v a.
Proof. exact (@lem1689780 u v a (@lem1690544 u v a)). Qed.
Lemma lem1690547 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term12.
Proof. exact (@lem1690546 u v a (@lem1689765 u v a h1)). Qed.
Lemma lem1690548 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term8.
Proof. exact (@lem1690547 u v a h1 (@lem1487144)). Qed.
Lemma lem1690549 (u : real) (v : real) (a : real) (h1 : term3 u v a) : False.
Proof. exact (@lem1690548 u v a h1 (@lem1338986)). Qed.
Lemma lem1690550 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term3 u v a) = False.
Proof. exact (prop_ext (fun h2 : term3 u v a => @lem1690549 u v a h1) (fun h2 : False => @lem1689765 u v a h1)). Qed.
Lemma lem1690551 (u : real) (v : real) (a : real) (h1 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1690550 u v a h1) (@lem1689765 u v a h1)). Qed.
Lemma lem1690552 (u : real) (v : real) (a : real) : term2 u v a.
Proof. exact (fun h0 : term3 u v a => @lem1690551 u v a h0). Qed.
Lemma lem1690553 (u : real) (v : real) (a : real) : term1 u v a.
Proof. exact (EQ_MP (@lem1689764 u v a) (@lem1690552 u v a)). Qed.
Lemma lem1690554 (t1 : Prop) : term113 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1690555 (t1 : Prop) : (term113 t1) = (term114 t1).
Proof. exact (eq_refl (term113 t1)). Qed.
Lemma lem1690556 (t1 : Prop) : term114 t1.
Proof. exact (EQ_MP (@lem1690555 t1) (@lem1690554 t1)). Qed.
Lemma lem1690557 (t1 : Prop) (t2 : Prop) : term115 t1 t2.
Proof. exact (@lem1690556 t1 t2). Qed.
Lemma lem1690558 (t1 : Prop) (t2 : Prop) : (term115 t1 t2) = (term116 t1 t2).
Proof. exact (eq_refl (term115 t1 t2)). Qed.
Lemma lem1690559 (t1 : Prop) (t2 : Prop) : term116 t1 t2.
Proof. exact (EQ_MP (@lem1690558 t1 t2) (@lem1690557 t1 t2)). Qed.
Lemma lem1690560 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term117 t1 t2 t3.
Proof. exact (@lem1690559 t1 t2 t3). Qed.
Lemma lem1690561 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term117 t1 t2 t3) = ((term60 t1 t2 t3) = (term118 t1 t2 t3)).
Proof. exact (eq_refl (term117 t1 t2 t3)). Qed.
Lemma lem1690562 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term60 t1 t2 t3) = (term118 t1 t2 t3).
Proof. exact (EQ_MP (@lem1690561 t1 t2 t3) (@lem1690560 t1 t2 t3)). Qed.
Lemma lem1690563 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term118 t1 t2 t3) = (term60 t1 t2 t3).
Proof. exact (SYM (@lem1690562 t1 t2 t3)). Qed.
Lemma lem1690564 : term119.
Proof. exact (fun b : real => @lem1672514 b). Qed.
Lemma lem1690565 (u : real) (v : real) : term120 u v.
Proof. exact (fun a : real => @lem1690553 u v a). Qed.
Lemma lem1690566 (u : real) : term121 u.
Proof. exact (fun v : real => @lem1690565 u v). Qed.
Lemma lem1690567 : term122.
Proof. exact (fun u : real => @lem1690566 u). Qed.
Lemma lem1690569 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1690570 : term123 = term124.
Proof. exact (@lem1690569 term123). Qed.
Lemma lem1690571 : term124 = term123.
Proof. exact (SYM (@lem1690570)). Qed.
Lemma lem1690572 (h1 : term125) : term125.
Proof. exact (h1). Qed.
Lemma lem1690575 (h1 : term126) : term126.
Proof. exact (h1). Qed.
Lemma lem1690576 : term127.
Proof. exact (fun h0 : term126 => @lem1690575 h0). Qed.
Lemma lem1690577 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem1690578 (h1 : term126) : term126.
Proof. exact (h1). Qed.
Lemma lem1690579 (h1 : term126) (h2 : term127) : term126.
Proof. exact (@lem1690577 h2 (@lem1690578 h1)). Qed.
Lemma lem1690580 (h1 : term126) : term128.
Proof. exact (fun h0 : term127 => @lem1690579 h1 h0). Qed.
Lemma lem1690581 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem1690582 (h1 : term126) (h2 : term127) : term126.
Proof. exact (@lem1690580 h1 (@lem1690581 h2)). Qed.
Lemma lem1690583 (h1 : term127) : term127.
Proof. exact (fun h0 : term126 => @lem1690582 h0 h1). Qed.
Lemma lem1690584 : term129.
Proof. exact (fun h0 : term127 => @lem1690583 h0). Qed.
Lemma lem1690587 : term127.
Proof. exact (@lem1690584 (@lem1690576)). Qed.
Lemma lem1690647 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1690648 : term130 = term131.
Proof. exact (@lem1690647 term119). Qed.
Lemma lem1690683 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem1690684 : term133 = term134.
Proof. exact (MK_COMB (@lem1690683) (@lem1690648)). Qed.
Lemma lem1690687 : term135 = term135.
Proof. exact (eq_refl term135). Qed.
Lemma lem1690694 : term126 = term136.
Proof. exact (MK_COMB (@lem1690687) (@lem1690684)). Qed.
Lemma lem1690715 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term137 x y u a v b).
Proof. exact (eq_refl (term137 x y u a v b)). Qed.
Lemma lem1690716 (x : real) (y : real) (u : real) (a : real) (b : real) : (term138 x y u a b) = (term138 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1690715 x y u a v b)). Qed.
Lemma lem1690717 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690718 (x : real) (y : real) (u : real) (a : real) (b : real) : (term139 x y u a b) = (term139 x y u a b).
Proof. exact (MK_COMB (@lem1690717) (@lem1690716 x y u a b)). Qed.
Lemma lem1690719 (x : real) (y : real) (a : real) (b : real) : (term140 x y a b) = (term140 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1690718 x y u a b)). Qed.
Lemma lem1690720 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690721 (x : real) (y : real) (a : real) (b : real) : (term141 x y a b) = (term141 x y a b).
Proof. exact (MK_COMB (@lem1690720) (@lem1690719 x y a b)). Qed.
Lemma lem1690722 (x : real) (y : real) (b : real) : (term142 x y b) = (term142 x y b).
Proof. exact (fun_ext (fun a : real => @lem1690721 x y a b)). Qed.
Lemma lem1690723 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690724 (x : real) (y : real) (b : real) : (term143 x y b) = (term143 x y b).
Proof. exact (MK_COMB (@lem1690723) (@lem1690722 x y b)). Qed.
Lemma lem1690725 (x : real) (b : real) : (term144 x b) = (term144 x b).
Proof. exact (fun_ext (fun y : real => @lem1690724 x y b)). Qed.
Lemma lem1690726 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690727 (x : real) (b : real) : (term145 x b) = (term145 x b).
Proof. exact (MK_COMB (@lem1690726) (@lem1690725 x b)). Qed.
Lemma lem1690728 (b : real) : (term146 b) = (term146 b).
Proof. exact (fun_ext (fun x : real => @lem1690727 x b)). Qed.
Lemma lem1690729 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690730 (b : real) : (term147 b) = (term147 b).
Proof. exact (MK_COMB (@lem1690729) (@lem1690728 b)). Qed.
Lemma lem1690731 : term148 = term148.
Proof. exact (fun_ext (fun b : real => @lem1690730 b)). Qed.
Lemma lem1690732 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690733 : term119 = term119.
Proof. exact (MK_COMB (@lem1690732) (@lem1690731)). Qed.
Lemma lem1690734 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1690735 : term131 = term131.
Proof. exact (MK_COMB (@lem1690734) (@lem1690733)). Qed.
Lemma lem1690740 (u : real) (v : real) (a : real) : (term1 u v a) = (term1 u v a).
Proof. exact (eq_refl (term1 u v a)). Qed.
Lemma lem1690741 (u : real) (v : real) : (term149 u v) = (term149 u v).
Proof. exact (fun_ext (fun a : real => @lem1690740 u v a)). Qed.
Lemma lem1690742 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690743 (u : real) (v : real) : (term120 u v) = (term120 u v).
Proof. exact (MK_COMB (@lem1690742) (@lem1690741 u v)). Qed.
Lemma lem1690744 (u : real) : (term150 u) = (term150 u).
Proof. exact (fun_ext (fun v : real => @lem1690743 u v)). Qed.
Lemma lem1690745 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690746 (u : real) : (term121 u) = (term121 u).
Proof. exact (MK_COMB (@lem1690745) (@lem1690744 u)). Qed.
Lemma lem1690747 : term151 = term151.
Proof. exact (fun_ext (fun u : real => @lem1690746 u)). Qed.
Lemma lem1690748 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690749 : term122 = term122.
Proof. exact (MK_COMB (@lem1690748) (@lem1690747)). Qed.
Lemma lem1690750 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1690751 : term132 = term132.
Proof. exact (MK_COMB (@lem1690750) (@lem1690749)). Qed.
Lemma lem1690752 : term134 = term134.
Proof. exact (MK_COMB (@lem1690751) (@lem1690735)). Qed.
Lemma lem1690785 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) : (term152 a u x v y b) = (term152 a u x v y b).
Proof. exact (eq_refl (term152 a u x v y b)). Qed.
Lemma lem1690786 (a : real) (u : real) (x : real) (y : real) (b : real) : (term153 a u x y b) = (term153 a u x y b).
Proof. exact (fun_ext (fun v : real => @lem1690785 a u x v y b)). Qed.
Lemma lem1690787 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690788 (a : real) (u : real) (x : real) (y : real) (b : real) : (term154 a u x y b) = (term154 a u x y b).
Proof. exact (MK_COMB (@lem1690787) (@lem1690786 a u x y b)). Qed.
Lemma lem1690789 (a : real) (x : real) (y : real) (b : real) : (term155 a x y b) = (term155 a x y b).
Proof. exact (fun_ext (fun u : real => @lem1690788 a u x y b)). Qed.
Lemma lem1690790 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690791 (a : real) (x : real) (y : real) (b : real) : (term156 a x y b) = (term156 a x y b).
Proof. exact (MK_COMB (@lem1690790) (@lem1690789 a x y b)). Qed.
Lemma lem1690792 (a : real) (x : real) (y : real) : (term157 a x y) = (term157 a x y).
Proof. exact (fun_ext (fun b : real => @lem1690791 a x y b)). Qed.
Lemma lem1690793 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690794 (a : real) (x : real) (y : real) : (term158 a x y) = (term158 a x y).
Proof. exact (MK_COMB (@lem1690793) (@lem1690792 a x y)). Qed.
Lemma lem1690795 (x : real) (y : real) : (term159 x y) = (term159 x y).
Proof. exact (fun_ext (fun a : real => @lem1690794 a x y)). Qed.
Lemma lem1690796 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690797 (x : real) (y : real) : (term160 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1690796) (@lem1690795 x y)). Qed.
Lemma lem1690798 (x : real) : (term161 x) = (term161 x).
Proof. exact (fun_ext (fun y : real => @lem1690797 x y)). Qed.
Lemma lem1690799 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690800 (x : real) : (term162 x) = (term162 x).
Proof. exact (MK_COMB (@lem1690799) (@lem1690798 x)). Qed.
Lemma lem1690801 : term163 = term163.
Proof. exact (fun_ext (fun x : real => @lem1690800 x)). Qed.
Lemma lem1690802 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1690803 : term123 = term123.
Proof. exact (MK_COMB (@lem1690802) (@lem1690801)). Qed.
Lemma lem1690804 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1690805 : term125 = term125.
Proof. exact (MK_COMB (@lem1690804) (@lem1690803)). Qed.
Lemma lem1690806 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1690807 : term135 = term135.
Proof. exact (MK_COMB (@lem1690806) (@lem1690805)). Qed.
Lemma lem1690808 : term136 = term136.
Proof. exact (MK_COMB (@lem1690807) (@lem1690752)). Qed.
Lemma lem1690933 : term126 = term136.
Proof. exact (TRANS (@lem1690694) (@lem1690808)). Qed.
Lemma lem1690934 : term136 = term126.
Proof. exact (SYM (@lem1690933)). Qed.
Lemma lem1690935 (h1 : term125) : term125.
Proof. exact (h1). Qed.
Lemma lem1690936 (h1 : term122) : term122.
Proof. exact (h1). Qed.
Lemma lem1690937 (h1 : term119) : term119.
Proof. exact (h1). Qed.
Lemma lem1690969 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) : (term164 a u x v y b) = (term165 a u x v y b).
Proof. exact (@lem17045 (term166 a u x v y) (term167 u x v y b)). Qed.
Lemma lem1690971 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term168 x a y b u v) = (term168 x a y b u v).
Proof. exact (eq_refl (term168 x a y b u v)). Qed.
Lemma lem1690972 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) : (term169 a u x v y b) = (term170 a u x v y b).
Proof. exact (MK_COMB (@lem1690971 x a y b u v) (@lem1690969 a u x v y b)). Qed.
Lemma lem1690973 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) : (term171 a u x v y b) = (term169 a u x v y b).
Proof. exact (@lem17362 (term172 x a y b u v) (term173 a u x v y b)). Qed.
Lemma lem1690974 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) : (term171 a u x v y b) = (term170 a u x v y b).
Proof. exact (TRANS (@lem1690973 a u x v y b) (@lem1690972 a u x v y b)). Qed.
Lemma lem1690975 (P : real -> Prop) : (term174 P) = (term175 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1690976 (a : real) (u : real) (x : real) (y : real) (b : real) : (term176 a u x y b) = (term177 a u x y b).
Proof. exact (@lem1690975 (term153 a u x y b)). Qed.
Lemma lem1690977 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) : (term178 a u x y b v) = (term152 a u x v y b).
Proof. exact (eq_refl (term178 a u x y b v)). Qed.
Lemma lem1690978 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1690979 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) : (term179 a u x y b v) = (term171 a u x v y b).
Proof. exact (MK_COMB (@lem1690978) (@lem1690977 a u x v y b)). Qed.
Lemma lem1690980 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) : (term179 a u x y b v) = (term170 a u x v y b).
Proof. exact (TRANS (@lem1690979 a u x v y b) (@lem1690974 a u x v y b)). Qed.
Lemma lem1690981 (a : real) (u : real) (x : real) (y : real) (b : real) : (term180 a u x y b) = (term181 a u x y b).
Proof. exact (fun_ext (fun v : real => @lem1690980 a u x v y b)). Qed.
Lemma lem1690982 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1690983 (a : real) (u : real) (x : real) (y : real) (b : real) : (term177 a u x y b) = (term182 a u x y b).
Proof. exact (MK_COMB (@lem1690982) (@lem1690981 a u x y b)). Qed.
Lemma lem1690984 (a : real) (u : real) (x : real) (y : real) (b : real) : (term176 a u x y b) = (term182 a u x y b).
Proof. exact (TRANS (@lem1690976 a u x y b) (@lem1690983 a u x y b)). Qed.
Lemma lem1690985 (P : real -> Prop) : (term174 P) = (term175 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1690986 (a : real) (x : real) (y : real) (b : real) : (term183 a x y b) = (term184 a x y b).
Proof. exact (@lem1690985 (term155 a x y b)). Qed.
Lemma lem1690987 (a : real) (u : real) (x : real) (y : real) (b : real) : (term185 a x y b u) = (term154 a u x y b).
Proof. exact (eq_refl (term185 a x y b u)). Qed.
Lemma lem1690988 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1690989 (a : real) (u : real) (x : real) (y : real) (b : real) : (term186 a x y b u) = (term176 a u x y b).
Proof. exact (MK_COMB (@lem1690988) (@lem1690987 a u x y b)). Qed.
Lemma lem1690990 (a : real) (u : real) (x : real) (y : real) (b : real) : (term186 a x y b u) = (term182 a u x y b).
Proof. exact (TRANS (@lem1690989 a u x y b) (@lem1690984 a u x y b)). Qed.
Lemma lem1690991 (a : real) (x : real) (y : real) (b : real) : (term187 a x y b) = (term188 a x y b).
Proof. exact (fun_ext (fun u : real => @lem1690990 a u x y b)). Qed.
Lemma lem1690992 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1690993 (a : real) (x : real) (y : real) (b : real) : (term184 a x y b) = (term189 a x y b).
Proof. exact (MK_COMB (@lem1690992) (@lem1690991 a x y b)). Qed.
Lemma lem1690994 (a : real) (x : real) (y : real) (b : real) : (term183 a x y b) = (term189 a x y b).
Proof. exact (TRANS (@lem1690986 a x y b) (@lem1690993 a x y b)). Qed.
Lemma lem1690995 (P : real -> Prop) : (term174 P) = (term175 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1690996 (a : real) (x : real) (y : real) : (term190 a x y) = (term191 a x y).
Proof. exact (@lem1690995 (term157 a x y)). Qed.
Lemma lem1690997 (a : real) (x : real) (y : real) (b : real) : (term192 a x y b) = (term156 a x y b).
Proof. exact (eq_refl (term192 a x y b)). Qed.
Lemma lem1690998 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1690999 (a : real) (x : real) (y : real) (b : real) : (term193 a x y b) = (term183 a x y b).
Proof. exact (MK_COMB (@lem1690998) (@lem1690997 a x y b)). Qed.
Lemma lem1691000 (a : real) (x : real) (y : real) (b : real) : (term193 a x y b) = (term189 a x y b).
Proof. exact (TRANS (@lem1690999 a x y b) (@lem1690994 a x y b)). Qed.
Lemma lem1691001 (a : real) (x : real) (y : real) : (term194 a x y) = (term195 a x y).
Proof. exact (fun_ext (fun b : real => @lem1691000 a x y b)). Qed.
Lemma lem1691002 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1691003 (a : real) (x : real) (y : real) : (term191 a x y) = (term196 a x y).
Proof. exact (MK_COMB (@lem1691002) (@lem1691001 a x y)). Qed.
Lemma lem1691004 (a : real) (x : real) (y : real) : (term190 a x y) = (term196 a x y).
Proof. exact (TRANS (@lem1690996 a x y) (@lem1691003 a x y)). Qed.
Lemma lem1691005 (P : real -> Prop) : (term174 P) = (term175 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1691006 (x : real) (y : real) : (term197 x y) = (term198 x y).
Proof. exact (@lem1691005 (term159 x y)). Qed.
Lemma lem1691007 (a : real) (x : real) (y : real) : (term199 x y a) = (term158 a x y).
Proof. exact (eq_refl (term199 x y a)). Qed.
Lemma lem1691008 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1691009 (a : real) (x : real) (y : real) : (term200 x y a) = (term190 a x y).
Proof. exact (MK_COMB (@lem1691008) (@lem1691007 a x y)). Qed.
Lemma lem1691010 (a : real) (x : real) (y : real) : (term200 x y a) = (term196 a x y).
Proof. exact (TRANS (@lem1691009 a x y) (@lem1691004 a x y)). Qed.
Lemma lem1691011 (x : real) (y : real) : (term201 x y) = (term202 x y).
Proof. exact (fun_ext (fun a : real => @lem1691010 a x y)). Qed.
Lemma lem1691012 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1691013 (x : real) (y : real) : (term198 x y) = (term203 x y).
Proof. exact (MK_COMB (@lem1691012) (@lem1691011 x y)). Qed.
Lemma lem1691014 (x : real) (y : real) : (term197 x y) = (term203 x y).
Proof. exact (TRANS (@lem1691006 x y) (@lem1691013 x y)). Qed.
Lemma lem1691015 (P : real -> Prop) : (term174 P) = (term175 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1691016 (x : real) : (term204 x) = (term205 x).
Proof. exact (@lem1691015 (term161 x)). Qed.
Lemma lem1691017 (x : real) (y : real) : (term206 x y) = (term160 x y).
Proof. exact (eq_refl (term206 x y)). Qed.
Lemma lem1691018 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1691019 (x : real) (y : real) : (term207 x y) = (term197 x y).
Proof. exact (MK_COMB (@lem1691018) (@lem1691017 x y)). Qed.
Lemma lem1691020 (x : real) (y : real) : (term207 x y) = (term203 x y).
Proof. exact (TRANS (@lem1691019 x y) (@lem1691014 x y)). Qed.
Lemma lem1691021 (x : real) : (term208 x) = (term209 x).
Proof. exact (fun_ext (fun y : real => @lem1691020 x y)). Qed.
Lemma lem1691022 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1691023 (x : real) : (term205 x) = (term210 x).
Proof. exact (MK_COMB (@lem1691022) (@lem1691021 x)). Qed.
Lemma lem1691024 (x : real) : (term204 x) = (term210 x).
Proof. exact (TRANS (@lem1691016 x) (@lem1691023 x)). Qed.
Lemma lem1691025 (P : real -> Prop) : (term174 P) = (term175 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1691026 : term125 = term211.
Proof. exact (@lem1691025 term163). Qed.
Lemma lem1691027 (x : real) : (term212 x) = (term162 x).
Proof. exact (eq_refl (term212 x)). Qed.
Lemma lem1691028 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1691029 (x : real) : (term213 x) = (term204 x).
Proof. exact (MK_COMB (@lem1691028) (@lem1691027 x)). Qed.
Lemma lem1691030 (x : real) : (term213 x) = (term210 x).
Proof. exact (TRANS (@lem1691029 x) (@lem1691024 x)). Qed.
Lemma lem1691031 : term214 = term215.
Proof. exact (fun_ext (fun x : real => @lem1691030 x)). Qed.
Lemma lem1691032 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1691033 : term211 = term216.
Proof. exact (MK_COMB (@lem1691032) (@lem1691031)). Qed.
Lemma lem1691106 : term125 = term216.
Proof. exact (TRANS (@lem1691026) (@lem1691033)). Qed.
Lemma lem1691107 (h1 : term125) : term216.
Proof. exact (EQ_MP (@lem1691106) (@lem1690935 h1)). Qed.
Lemma lem1691114 (u : real) (v : real) (a : real) : (term1 u v a) = (term217 u v a).
Proof. exact (@lem17265 ((real_add u v) = term39) ((term31 u v a) = a)). Qed.
Lemma lem1691115 (u : real) (v : real) : (term149 u v) = (term218 u v).
Proof. exact (fun_ext (fun a : real => @lem1691114 u v a)). Qed.
Lemma lem1691116 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691117 (u : real) (v : real) : (term120 u v) = (term219 u v).
Proof. exact (MK_COMB (@lem1691116) (@lem1691115 u v)). Qed.
Lemma lem1691118 (u : real) : (term150 u) = (term220 u).
Proof. exact (fun_ext (fun v : real => @lem1691117 u v)). Qed.
Lemma lem1691119 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691120 (u : real) : (term121 u) = (term221 u).
Proof. exact (MK_COMB (@lem1691119) (@lem1691118 u)). Qed.
Lemma lem1691121 : term151 = term222.
Proof. exact (fun_ext (fun u : real => @lem1691120 u)). Qed.
Lemma lem1691122 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691123 : term122 = term223.
Proof. exact (MK_COMB (@lem1691122) (@lem1691121)). Qed.
Lemma lem1691133 {A : Type'} (P : Prop) (Q : A -> Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem1691134 (P : Prop) (Q : real -> Prop) : (term226 P Q) = (term227 P Q).
Proof. exact (@lem1691133 real P Q). Qed.
Lemma lem1691135 (u : real) (v : real) : (term228 u v) = (term229 u v).
Proof. exact (@lem1691134 (term52 u v) (term230 u v)). Qed.
Lemma lem1691136 (u : real) (v : real) (a : real) : (term231 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term231 u v a)). Qed.
Lemma lem1691137 (u : real) (v : real) : (term232 u v) = (term232 u v).
Proof. exact (eq_refl (term232 u v)). Qed.
Lemma lem1691138 (u : real) (v : real) (a : real) : (term233 u v a) = (term217 u v a).
Proof. exact (MK_COMB (@lem1691137 u v) (@lem1691136 u v a)). Qed.
Lemma lem1691139 (u : real) (v : real) : (term234 u v) = (term218 u v).
Proof. exact (fun_ext (fun a : real => @lem1691138 u v a)). Qed.
Lemma lem1691140 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691141 (u : real) (v : real) : (term228 u v) = (term219 u v).
Proof. exact (MK_COMB (@lem1691140) (@lem1691139 u v)). Qed.
Lemma lem1691142 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1691143 (u : real) (v : real) : (term235 u v) = (term236 u v).
Proof. exact (MK_COMB (@lem1691142) (@lem1691141 u v)). Qed.
Lemma lem1691144 (u : real) (v : real) (a : real) : (term231 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term231 u v a)). Qed.
Lemma lem1691145 (u : real) (v : real) : (term237 u v) = (term230 u v).
Proof. exact (fun_ext (fun a : real => @lem1691144 u v a)). Qed.
Lemma lem1691146 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691147 (u : real) (v : real) : (term238 u v) = (term239 u v).
Proof. exact (MK_COMB (@lem1691146) (@lem1691145 u v)). Qed.
Lemma lem1691148 (u : real) (v : real) : (term232 u v) = (term232 u v).
Proof. exact (eq_refl (term232 u v)). Qed.
Lemma lem1691149 (u : real) (v : real) : (term229 u v) = (term240 u v).
Proof. exact (MK_COMB (@lem1691148 u v) (@lem1691147 u v)). Qed.
Lemma lem1691150 (u : real) (v : real) : ((term228 u v) = (term229 u v)) = ((term219 u v) = (term240 u v)).
Proof. exact (MK_COMB (@lem1691143 u v) (@lem1691149 u v)). Qed.
Lemma lem1691151 (u : real) (v : real) : (term219 u v) = (term240 u v).
Proof. exact (EQ_MP (@lem1691150 u v) (@lem1691135 u v)). Qed.
Lemma lem1691156 (u : real) : (term220 u) = (term241 u).
Proof. exact (fun_ext (fun v : real => @lem1691151 u v)). Qed.
Lemma lem1691157 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691158 (u : real) : (term221 u) = (term242 u).
Proof. exact (MK_COMB (@lem1691157) (@lem1691156 u)). Qed.
Lemma lem1691207 : term222 = term243.
Proof. exact (fun_ext (fun u : real => @lem1691158 u)). Qed.
Lemma lem1691208 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691215 : term223 = term244.
Proof. exact (MK_COMB (@lem1691208) (@lem1691207)). Qed.
Lemma lem1691216 : term122 = term244.
Proof. exact (TRANS (@lem1691123) (@lem1691215)). Qed.
Lemma lem1691217 (h1 : term122) : term244.
Proof. exact (EQ_MP (@lem1691216) (@lem1690936 h1)). Qed.
Lemma lem1691227 (u : real) (v : real) : (term245 u v) = (term246 u v).
Proof. exact (@lem17045 (term247 v) ((real_add u v) = term39)). Qed.
Lemma lem1691229 (u : real) : (term248 u) = (term248 u).
Proof. exact (eq_refl (term248 u)). Qed.
Lemma lem1691230 (u : real) (v : real) : (term249 u v) = (term250 u v).
Proof. exact (MK_COMB (@lem1691229 u) (@lem1691227 u v)). Qed.
Lemma lem1691231 (u : real) (v : real) : (term251 u v) = (term249 u v).
Proof. exact (@lem17045 (term247 u) (term252 u v)). Qed.
Lemma lem1691232 (u : real) (v : real) : (term251 u v) = (term250 u v).
Proof. exact (TRANS (@lem1691231 u v) (@lem1691230 u v)). Qed.
Lemma lem1691234 (y : real) (b : real) : (term253 y b) = (term253 y b).
Proof. exact (eq_refl (term253 y b)). Qed.
Lemma lem1691235 (y : real) (b : real) (u : real) (v : real) : (term254 y b u v) = (term255 y b u v).
Proof. exact (MK_COMB (@lem1691234 y b) (@lem1691232 u v)). Qed.
Lemma lem1691236 (y : real) (b : real) (u : real) (v : real) : (term256 y b u v) = (term254 y b u v).
Proof. exact (@lem17045 (real_lt y b) (term257 u v)). Qed.
Lemma lem1691237 (y : real) (b : real) (u : real) (v : real) : (term256 y b u v) = (term255 y b u v).
Proof. exact (TRANS (@lem1691236 y b u v) (@lem1691235 y b u v)). Qed.
Lemma lem1691239 (x : real) (a : real) : (term253 x a) = (term253 x a).
Proof. exact (eq_refl (term253 x a)). Qed.
Lemma lem1691240 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term258 x a y b u v) = (term259 x a y b u v).
Proof. exact (MK_COMB (@lem1691239 x a) (@lem1691237 y b u v)). Qed.
Lemma lem1691241 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term260 x a y b u v) = (term258 x a y b u v).
Proof. exact (@lem17045 (real_lt x a) (term261 y b u v)). Qed.
Lemma lem1691242 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term260 x a y b u v) = (term259 x a y b u v).
Proof. exact (TRANS (@lem1691241 x a y b u v) (@lem1691240 x a y b u v)). Qed.
Lemma lem1691243 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term262 x y u a v b) = (term262 x y u a v b).
Proof. exact (eq_refl (term262 x y u a v b)). Qed.
Lemma lem1691244 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1691245 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term263 x a y b u v) = (term264 x a y b u v).
Proof. exact (MK_COMB (@lem1691244) (@lem1691242 x a y b u v)). Qed.
Lemma lem1691246 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term265 x y u a v b) = (term266 x y u a v b).
Proof. exact (MK_COMB (@lem1691245 x a y b u v) (@lem1691243 x y u a v b)). Qed.
Lemma lem1691247 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term265 x y u a v b).
Proof. exact (@lem17265 (term267 x a y b u v) (term262 x y u a v b)). Qed.
Lemma lem1691248 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term266 x y u a v b).
Proof. exact (TRANS (@lem1691247 x y u a v b) (@lem1691246 x y u a v b)). Qed.
Lemma lem1691249 (x : real) (y : real) (u : real) (a : real) (b : real) : (term138 x y u a b) = (term268 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1691248 x y u a v b)). Qed.
Lemma lem1691250 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691251 (x : real) (y : real) (u : real) (a : real) (b : real) : (term139 x y u a b) = (term269 x y u a b).
Proof. exact (MK_COMB (@lem1691250) (@lem1691249 x y u a b)). Qed.
Lemma lem1691252 (x : real) (y : real) (a : real) (b : real) : (term140 x y a b) = (term270 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1691251 x y u a b)). Qed.
Lemma lem1691253 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691254 (x : real) (y : real) (a : real) (b : real) : (term141 x y a b) = (term271 x y a b).
Proof. exact (MK_COMB (@lem1691253) (@lem1691252 x y a b)). Qed.
Lemma lem1691255 (x : real) (y : real) (b : real) : (term142 x y b) = (term272 x y b).
Proof. exact (fun_ext (fun a : real => @lem1691254 x y a b)). Qed.
Lemma lem1691256 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691257 (x : real) (y : real) (b : real) : (term143 x y b) = (term273 x y b).
Proof. exact (MK_COMB (@lem1691256) (@lem1691255 x y b)). Qed.
Lemma lem1691258 (x : real) (b : real) : (term144 x b) = (term274 x b).
Proof. exact (fun_ext (fun y : real => @lem1691257 x y b)). Qed.
Lemma lem1691259 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691260 (x : real) (b : real) : (term145 x b) = (term275 x b).
Proof. exact (MK_COMB (@lem1691259) (@lem1691258 x b)). Qed.
Lemma lem1691261 (b : real) : (term146 b) = (term276 b).
Proof. exact (fun_ext (fun x : real => @lem1691260 x b)). Qed.
Lemma lem1691262 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691263 (b : real) : (term147 b) = (term277 b).
Proof. exact (MK_COMB (@lem1691262) (@lem1691261 b)). Qed.
Lemma lem1691264 : term148 = term278.
Proof. exact (fun_ext (fun b : real => @lem1691263 b)). Qed.
Lemma lem1691265 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691338 : term119 = term279.
Proof. exact (MK_COMB (@lem1691265) (@lem1691264)). Qed.
Lemma lem1691339 (h1 : term119) : term279.
Proof. exact (EQ_MP (@lem1691338) (@lem1690937 h1)). Qed.
Lemma lem1691340 (x : real) (h1 : term210 x) : term210 x.
Proof. exact (h1). Qed.
Lemma lem1691341 (x : real) (y : real) (h1 : term203 x y) : term203 x y.
Proof. exact (h1). Qed.
Lemma lem1691342 (a : real) (x : real) (y : real) (h1 : term196 a x y) : term196 a x y.
Proof. exact (h1). Qed.
Lemma lem1691343 (a : real) (x : real) (y : real) (b : real) (h1 : term189 a x y b) : term189 a x y b.
Proof. exact (h1). Qed.
Lemma lem1691344 (a : real) (u : real) (x : real) (y : real) (b : real) (h1 : term182 a u x y b) : term182 a u x y b.
Proof. exact (h1). Qed.
Lemma lem1691362 (u : real) (v : real) (a : real) : ((term31 u v a) = a) = ((term31 u v a) = a).
Proof. exact (eq_refl ((term31 u v a) = a)). Qed.
Lemma lem1691363 (u : real) (v : real) : (term230 u v) = (term230 u v).
Proof. exact (fun_ext (fun a : real => @lem1691362 u v a)). Qed.
Lemma lem1691364 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691365 (u : real) (v : real) : (term239 u v) = (term239 u v).
Proof. exact (MK_COMB (@lem1691364) (@lem1691363 u v)). Qed.
Lemma lem1691384 (u : real) (v : real) : (term232 u v) = (term232 u v).
Proof. exact (eq_refl (term232 u v)). Qed.
Lemma lem1691385 (u : real) (v : real) : (term240 u v) = (term240 u v).
Proof. exact (MK_COMB (@lem1691384 u v) (@lem1691365 u v)). Qed.
Lemma lem1691386 (u : real) : (term241 u) = (term241 u).
Proof. exact (fun_ext (fun v : real => @lem1691385 u v)). Qed.
Lemma lem1691387 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691388 (u : real) : (term242 u) = (term242 u).
Proof. exact (MK_COMB (@lem1691387) (@lem1691386 u)). Qed.
Lemma lem1691389 : term243 = term243.
Proof. exact (fun_ext (fun u : real => @lem1691388 u)). Qed.
Lemma lem1691390 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691391 : term244 = term244.
Proof. exact (MK_COMB (@lem1691390) (@lem1691389)). Qed.
Lemma lem1691392 (h1 : term122) : term244.
Proof. exact (EQ_MP (@lem1691391) (@lem1691217 h1)). Qed.
Lemma lem1691489 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term266 x y u a v b) = (term266 x y u a v b).
Proof. exact (eq_refl (term266 x y u a v b)). Qed.
Lemma lem1691490 (x : real) (y : real) (u : real) (a : real) (b : real) : (term268 x y u a b) = (term268 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1691489 x y u a v b)). Qed.
Lemma lem1691491 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691492 (x : real) (y : real) (u : real) (a : real) (b : real) : (term269 x y u a b) = (term269 x y u a b).
Proof. exact (MK_COMB (@lem1691491) (@lem1691490 x y u a b)). Qed.
Lemma lem1691493 (x : real) (y : real) (a : real) (b : real) : (term270 x y a b) = (term270 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1691492 x y u a b)). Qed.
Lemma lem1691494 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691495 (x : real) (y : real) (a : real) (b : real) : (term271 x y a b) = (term271 x y a b).
Proof. exact (MK_COMB (@lem1691494) (@lem1691493 x y a b)). Qed.
Lemma lem1691496 (x : real) (y : real) (b : real) : (term272 x y b) = (term272 x y b).
Proof. exact (fun_ext (fun a : real => @lem1691495 x y a b)). Qed.
Lemma lem1691497 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691498 (x : real) (y : real) (b : real) : (term273 x y b) = (term273 x y b).
Proof. exact (MK_COMB (@lem1691497) (@lem1691496 x y b)). Qed.
Lemma lem1691499 (x : real) (b : real) : (term274 x b) = (term274 x b).
Proof. exact (fun_ext (fun y : real => @lem1691498 x y b)). Qed.
Lemma lem1691500 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691501 (x : real) (b : real) : (term275 x b) = (term275 x b).
Proof. exact (MK_COMB (@lem1691500) (@lem1691499 x b)). Qed.
Lemma lem1691502 (b : real) : (term276 b) = (term276 b).
Proof. exact (fun_ext (fun x : real => @lem1691501 x b)). Qed.
Lemma lem1691503 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691504 (b : real) : (term277 b) = (term277 b).
Proof. exact (MK_COMB (@lem1691503) (@lem1691502 b)). Qed.
Lemma lem1691505 : term278 = term278.
Proof. exact (fun_ext (fun b : real => @lem1691504 b)). Qed.
Lemma lem1691506 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691507 : term279 = term279.
Proof. exact (MK_COMB (@lem1691506) (@lem1691505)). Qed.
Lemma lem1691508 (h1 : term119) : term279.
Proof. exact (EQ_MP (@lem1691507) (@lem1691339 h1)). Qed.
Lemma lem1691624 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term170 a u x v y b.
Proof. exact (h1). Qed.
Lemma lem1691625 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term165 a u x v y b.
Proof. exact (proj2 (@lem1691624 a u x v y b h1)). Qed.
Lemma lem1691626 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term172 x a y b u v.
Proof. exact (proj1 (@lem1691624 a u x v y b h1)). Qed.
Lemma lem1691627 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term280 x a y b u v.
Proof. exact (proj2 (@lem1691626 a u x v y b h1)). Qed.
Lemma lem1691629 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term281 a y b u v.
Proof. exact (proj2 (@lem1691627 a u x v y b h1)). Qed.
Lemma lem1691631 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term261 y b u v.
Proof. exact (proj2 (@lem1691629 a u x v y b h1)). Qed.
Lemma lem1691633 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term257 u v.
Proof. exact (proj2 (@lem1691631 a u x v y b h1)). Qed.
Lemma lem1691635 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term252 u v.
Proof. exact (proj2 (@lem1691633 a u x v y b h1)). Qed.
Lemma lem1691642 {A : Type'} (P : Prop) (Q : A -> Prop) : (term225 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1691643 (P : Prop) (Q : real -> Prop) : (term227 P Q) = (term226 P Q).
Proof. exact (@lem1691642 real P Q). Qed.
Lemma lem1691644 (u : real) (v : real) : (term229 u v) = (term228 u v).
Proof. exact (@lem1691643 (term52 u v) (term230 u v)). Qed.
Lemma lem1691645 (u : real) (v : real) (a : real) : (term231 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term231 u v a)). Qed.
Lemma lem1691646 (u : real) (v : real) : (term237 u v) = (term230 u v).
Proof. exact (fun_ext (fun a : real => @lem1691645 u v a)). Qed.
Lemma lem1691647 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691648 (u : real) (v : real) : (term238 u v) = (term239 u v).
Proof. exact (MK_COMB (@lem1691647) (@lem1691646 u v)). Qed.
Lemma lem1691649 (u : real) (v : real) : (term232 u v) = (term232 u v).
Proof. exact (eq_refl (term232 u v)). Qed.
Lemma lem1691650 (u : real) (v : real) : (term229 u v) = (term240 u v).
Proof. exact (MK_COMB (@lem1691649 u v) (@lem1691648 u v)). Qed.
Lemma lem1691651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1691652 (u : real) (v : real) : (term282 u v) = (term283 u v).
Proof. exact (MK_COMB (@lem1691651) (@lem1691650 u v)). Qed.
Lemma lem1691653 (u : real) (v : real) (a : real) : (term231 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term231 u v a)). Qed.
Lemma lem1691654 (u : real) (v : real) : (term232 u v) = (term232 u v).
Proof. exact (eq_refl (term232 u v)). Qed.
Lemma lem1691655 (u : real) (v : real) (a : real) : (term233 u v a) = (term217 u v a).
Proof. exact (MK_COMB (@lem1691654 u v) (@lem1691653 u v a)). Qed.
Lemma lem1691656 (u : real) (v : real) : (term234 u v) = (term218 u v).
Proof. exact (fun_ext (fun a : real => @lem1691655 u v a)). Qed.
Lemma lem1691657 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691658 (u : real) (v : real) : (term228 u v) = (term219 u v).
Proof. exact (MK_COMB (@lem1691657) (@lem1691656 u v)). Qed.
Lemma lem1691659 (u : real) (v : real) : ((term229 u v) = (term228 u v)) = ((term240 u v) = (term219 u v)).
Proof. exact (MK_COMB (@lem1691652 u v) (@lem1691658 u v)). Qed.
Lemma lem1691660 (u : real) (v : real) : (term240 u v) = (term219 u v).
Proof. exact (EQ_MP (@lem1691659 u v) (@lem1691644 u v)). Qed.
Lemma lem1691661 (u : real) : (term241 u) = (term220 u).
Proof. exact (fun_ext (fun v : real => @lem1691660 u v)). Qed.
Lemma lem1691662 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691663 (u : real) : (term242 u) = (term221 u).
Proof. exact (MK_COMB (@lem1691662) (@lem1691661 u)). Qed.
Lemma lem1691664 : term243 = term222.
Proof. exact (fun_ext (fun u : real => @lem1691663 u)). Qed.
Lemma lem1691665 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691666 : term244 = term223.
Proof. exact (MK_COMB (@lem1691665) (@lem1691664)). Qed.
Lemma lem1691673 (u : real) (v : real) (a : real) : (term217 u v a) = (term217 u v a).
Proof. exact (eq_refl (term217 u v a)). Qed.
Lemma lem1691674 (u : real) (v : real) : (term218 u v) = (term218 u v).
Proof. exact (fun_ext (fun a : real => @lem1691673 u v a)). Qed.
Lemma lem1691675 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691676 (u : real) (v : real) : (term219 u v) = (term219 u v).
Proof. exact (MK_COMB (@lem1691675) (@lem1691674 u v)). Qed.
Lemma lem1691677 (u : real) : (term220 u) = (term220 u).
Proof. exact (fun_ext (fun v : real => @lem1691676 u v)). Qed.
Lemma lem1691678 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691679 (u : real) : (term221 u) = (term221 u).
Proof. exact (MK_COMB (@lem1691678) (@lem1691677 u)). Qed.
Lemma lem1691680 : term222 = term222.
Proof. exact (fun_ext (fun u : real => @lem1691679 u)). Qed.
Lemma lem1691681 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691682 : term223 = term223.
Proof. exact (MK_COMB (@lem1691681) (@lem1691680)). Qed.
Lemma lem1691683 : term244 = term223.
Proof. exact (TRANS (@lem1691666) (@lem1691682)). Qed.
Lemma lem1691684 (h1 : term122) : term223.
Proof. exact (EQ_MP (@lem1691683) (@lem1691392 h1)). Qed.
Lemma lem1691716 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term266 x y u a v b) = (term266 x y u a v b).
Proof. exact (eq_refl (term266 x y u a v b)). Qed.
Lemma lem1691717 (x : real) (y : real) (u : real) (a : real) (b : real) : (term268 x y u a b) = (term268 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1691716 x y u a v b)). Qed.
Lemma lem1691718 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691719 (x : real) (y : real) (u : real) (a : real) (b : real) : (term269 x y u a b) = (term269 x y u a b).
Proof. exact (MK_COMB (@lem1691718) (@lem1691717 x y u a b)). Qed.
Lemma lem1691720 (x : real) (y : real) (a : real) (b : real) : (term270 x y a b) = (term270 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1691719 x y u a b)). Qed.
Lemma lem1691721 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691722 (x : real) (y : real) (a : real) (b : real) : (term271 x y a b) = (term271 x y a b).
Proof. exact (MK_COMB (@lem1691721) (@lem1691720 x y a b)). Qed.
Lemma lem1691723 (x : real) (y : real) (b : real) : (term272 x y b) = (term272 x y b).
Proof. exact (fun_ext (fun a : real => @lem1691722 x y a b)). Qed.
Lemma lem1691724 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691725 (x : real) (y : real) (b : real) : (term273 x y b) = (term273 x y b).
Proof. exact (MK_COMB (@lem1691724) (@lem1691723 x y b)). Qed.
Lemma lem1691726 (x : real) (b : real) : (term274 x b) = (term274 x b).
Proof. exact (fun_ext (fun y : real => @lem1691725 x y b)). Qed.
Lemma lem1691727 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691728 (x : real) (b : real) : (term275 x b) = (term275 x b).
Proof. exact (MK_COMB (@lem1691727) (@lem1691726 x b)). Qed.
Lemma lem1691729 (b : real) : (term276 b) = (term276 b).
Proof. exact (fun_ext (fun x : real => @lem1691728 x b)). Qed.
Lemma lem1691730 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691731 (b : real) : (term277 b) = (term277 b).
Proof. exact (MK_COMB (@lem1691730) (@lem1691729 b)). Qed.
Lemma lem1691732 : term278 = term278.
Proof. exact (fun_ext (fun b : real => @lem1691731 b)). Qed.
Lemma lem1691733 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691735 : term279 = term279.
Proof. exact (MK_COMB (@lem1691733) (@lem1691732)). Qed.
Lemma lem1691736 (h1 : term119) : term279.
Proof. exact (EQ_MP (@lem1691735) (@lem1691508 h1)). Qed.
Lemma lem1691768 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term284 a u x v y) : term284 a u x v y.
Proof. exact (h1). Qed.
Lemma lem1691770 {A : Type'} (P : Prop) (Q : A -> Prop) : (term225 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1691771 (P : Prop) (Q : real -> Prop) : (term227 P Q) = (term226 P Q).
Proof. exact (@lem1691770 real P Q). Qed.
Lemma lem1691772 (u : real) (v : real) : (term229 u v) = (term228 u v).
Proof. exact (@lem1691771 (term52 u v) (term230 u v)). Qed.
Lemma lem1691773 (u : real) (v : real) (a : real) : (term231 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term231 u v a)). Qed.
Lemma lem1691774 (u : real) (v : real) : (term237 u v) = (term230 u v).
Proof. exact (fun_ext (fun a : real => @lem1691773 u v a)). Qed.
Lemma lem1691775 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691776 (u : real) (v : real) : (term238 u v) = (term239 u v).
Proof. exact (MK_COMB (@lem1691775) (@lem1691774 u v)). Qed.
Lemma lem1691777 (u : real) (v : real) : (term232 u v) = (term232 u v).
Proof. exact (eq_refl (term232 u v)). Qed.
Lemma lem1691778 (u : real) (v : real) : (term229 u v) = (term240 u v).
Proof. exact (MK_COMB (@lem1691777 u v) (@lem1691776 u v)). Qed.
Lemma lem1691779 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1691780 (u : real) (v : real) : (term282 u v) = (term283 u v).
Proof. exact (MK_COMB (@lem1691779) (@lem1691778 u v)). Qed.
Lemma lem1691781 (u : real) (v : real) (a : real) : (term231 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term231 u v a)). Qed.
Lemma lem1691782 (u : real) (v : real) : (term232 u v) = (term232 u v).
Proof. exact (eq_refl (term232 u v)). Qed.
Lemma lem1691783 (u : real) (v : real) (a : real) : (term233 u v a) = (term217 u v a).
Proof. exact (MK_COMB (@lem1691782 u v) (@lem1691781 u v a)). Qed.
Lemma lem1691784 (u : real) (v : real) : (term234 u v) = (term218 u v).
Proof. exact (fun_ext (fun a : real => @lem1691783 u v a)). Qed.
Lemma lem1691785 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691786 (u : real) (v : real) : (term228 u v) = (term219 u v).
Proof. exact (MK_COMB (@lem1691785) (@lem1691784 u v)). Qed.
Lemma lem1691787 (u : real) (v : real) : ((term229 u v) = (term228 u v)) = ((term240 u v) = (term219 u v)).
Proof. exact (MK_COMB (@lem1691780 u v) (@lem1691786 u v)). Qed.
Lemma lem1691788 (u : real) (v : real) : (term240 u v) = (term219 u v).
Proof. exact (EQ_MP (@lem1691787 u v) (@lem1691772 u v)). Qed.
Lemma lem1691789 (u : real) : (term241 u) = (term220 u).
Proof. exact (fun_ext (fun v : real => @lem1691788 u v)). Qed.
Lemma lem1691790 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691791 (u : real) : (term242 u) = (term221 u).
Proof. exact (MK_COMB (@lem1691790) (@lem1691789 u)). Qed.
Lemma lem1691792 : term243 = term222.
Proof. exact (fun_ext (fun u : real => @lem1691791 u)). Qed.
Lemma lem1691793 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691794 : term244 = term223.
Proof. exact (MK_COMB (@lem1691793) (@lem1691792)). Qed.
Lemma lem1691801 (u : real) (v : real) (a : real) : (term217 u v a) = (term217 u v a).
Proof. exact (eq_refl (term217 u v a)). Qed.
Lemma lem1691802 (u : real) (v : real) : (term218 u v) = (term218 u v).
Proof. exact (fun_ext (fun a : real => @lem1691801 u v a)). Qed.
Lemma lem1691803 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691804 (u : real) (v : real) : (term219 u v) = (term219 u v).
Proof. exact (MK_COMB (@lem1691803) (@lem1691802 u v)). Qed.
Lemma lem1691805 (u : real) : (term220 u) = (term220 u).
Proof. exact (fun_ext (fun v : real => @lem1691804 u v)). Qed.
Lemma lem1691806 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691807 (u : real) : (term221 u) = (term221 u).
Proof. exact (MK_COMB (@lem1691806) (@lem1691805 u)). Qed.
Lemma lem1691808 : term222 = term222.
Proof. exact (fun_ext (fun u : real => @lem1691807 u)). Qed.
Lemma lem1691809 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691810 : term223 = term223.
Proof. exact (MK_COMB (@lem1691809) (@lem1691808)). Qed.
Lemma lem1691811 : term244 = term223.
Proof. exact (TRANS (@lem1691794) (@lem1691810)). Qed.
Lemma lem1691812 (h1 : term122) : term223.
Proof. exact (EQ_MP (@lem1691811) (@lem1691392 h1)). Qed.
Lemma lem1691844 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term266 x y u a v b) = (term266 x y u a v b).
Proof. exact (eq_refl (term266 x y u a v b)). Qed.
Lemma lem1691845 (x : real) (y : real) (u : real) (a : real) (b : real) : (term268 x y u a b) = (term268 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1691844 x y u a v b)). Qed.
Lemma lem1691846 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691847 (x : real) (y : real) (u : real) (a : real) (b : real) : (term269 x y u a b) = (term269 x y u a b).
Proof. exact (MK_COMB (@lem1691846) (@lem1691845 x y u a b)). Qed.
Lemma lem1691848 (x : real) (y : real) (a : real) (b : real) : (term270 x y a b) = (term270 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1691847 x y u a b)). Qed.
Lemma lem1691849 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691850 (x : real) (y : real) (a : real) (b : real) : (term271 x y a b) = (term271 x y a b).
Proof. exact (MK_COMB (@lem1691849) (@lem1691848 x y a b)). Qed.
Lemma lem1691851 (x : real) (y : real) (b : real) : (term272 x y b) = (term272 x y b).
Proof. exact (fun_ext (fun a : real => @lem1691850 x y a b)). Qed.
Lemma lem1691852 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691853 (x : real) (y : real) (b : real) : (term273 x y b) = (term273 x y b).
Proof. exact (MK_COMB (@lem1691852) (@lem1691851 x y b)). Qed.
Lemma lem1691854 (x : real) (b : real) : (term274 x b) = (term274 x b).
Proof. exact (fun_ext (fun y : real => @lem1691853 x y b)). Qed.
Lemma lem1691855 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691856 (x : real) (b : real) : (term275 x b) = (term275 x b).
Proof. exact (MK_COMB (@lem1691855) (@lem1691854 x b)). Qed.
Lemma lem1691857 (b : real) : (term276 b) = (term276 b).
Proof. exact (fun_ext (fun x : real => @lem1691856 x b)). Qed.
Lemma lem1691858 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691859 (b : real) : (term277 b) = (term277 b).
Proof. exact (MK_COMB (@lem1691858) (@lem1691857 b)). Qed.
Lemma lem1691860 : term278 = term278.
Proof. exact (fun_ext (fun b : real => @lem1691859 b)). Qed.
Lemma lem1691861 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1691863 : term279 = term279.
Proof. exact (MK_COMB (@lem1691861) (@lem1691860)). Qed.
Lemma lem1691864 (h1 : term119) : term279.
Proof. exact (EQ_MP (@lem1691863) (@lem1691508 h1)). Qed.
Lemma lem1691896 (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term285 u x v y b) : term285 u x v y b.
Proof. exact (h1). Qed.
Lemma lem1691897 (_26095 : real) (h1 : term122) : term286 _26095.
Proof. exact (@lem1691684 h1 _26095). Qed.
Lemma lem1691898 (_26095 : real) : (term286 _26095) = (term221 _26095).
Proof. exact (eq_refl (term286 _26095)). Qed.
Lemma lem1691899 (_26095 : real) (h1 : term122) : term221 _26095.
Proof. exact (EQ_MP (@lem1691898 _26095) (@lem1691897 _26095 h1)). Qed.
Lemma lem1691900 (_26095 : real) (_26096 : real) (h1 : term122) : term287 _26095 _26096.
Proof. exact (@lem1691899 _26095 h1 _26096). Qed.
Lemma lem1691901 (_26095 : real) (_26096 : real) : (term287 _26095 _26096) = (term219 _26095 _26096).
Proof. exact (eq_refl (term287 _26095 _26096)). Qed.
Lemma lem1691902 (_26095 : real) (_26096 : real) (h1 : term122) : term219 _26095 _26096.
Proof. exact (EQ_MP (@lem1691901 _26095 _26096) (@lem1691900 _26095 _26096 h1)). Qed.
Lemma lem1691903 (_26095 : real) (_26096 : real) (_26097 : real) (h1 : term122) : term288 _26095 _26096 _26097.
Proof. exact (@lem1691902 _26095 _26096 h1 _26097). Qed.
Lemma lem1691904 (_26095 : real) (_26096 : real) (_26097 : real) : (term288 _26095 _26096 _26097) = (term217 _26095 _26096 _26097).
Proof. exact (eq_refl (term288 _26095 _26096 _26097)). Qed.
Lemma lem1691906 (_26098 : real) (h1 : term119) : term289 _26098.
Proof. exact (@lem1691736 h1 _26098). Qed.
Lemma lem1691907 (_26098 : real) : (term289 _26098) = (term277 _26098).
Proof. exact (eq_refl (term289 _26098)). Qed.
Lemma lem1691908 (_26098 : real) (h1 : term119) : term277 _26098.
Proof. exact (EQ_MP (@lem1691907 _26098) (@lem1691906 _26098 h1)). Qed.
Lemma lem1691909 (_26098 : real) (_26099 : real) (h1 : term119) : term290 _26098 _26099.
Proof. exact (@lem1691908 _26098 h1 _26099). Qed.
Lemma lem1691910 (_26099 : real) (_26098 : real) : (term290 _26098 _26099) = (term275 _26099 _26098).
Proof. exact (eq_refl (term290 _26098 _26099)). Qed.
Lemma lem1691911 (_26099 : real) (_26098 : real) (h1 : term119) : term275 _26099 _26098.
Proof. exact (EQ_MP (@lem1691910 _26099 _26098) (@lem1691909 _26098 _26099 h1)). Qed.
Lemma lem1691912 (_26099 : real) (_26098 : real) (_26100 : real) (h1 : term119) : term291 _26099 _26098 _26100.
Proof. exact (@lem1691911 _26099 _26098 h1 _26100). Qed.
Lemma lem1691913 (_26099 : real) (_26100 : real) (_26098 : real) : (term291 _26099 _26098 _26100) = (term273 _26099 _26100 _26098).
Proof. exact (eq_refl (term291 _26099 _26098 _26100)). Qed.
Lemma lem1691914 (_26099 : real) (_26100 : real) (_26098 : real) (h1 : term119) : term273 _26099 _26100 _26098.
Proof. exact (EQ_MP (@lem1691913 _26099 _26100 _26098) (@lem1691912 _26099 _26098 _26100 h1)). Qed.
Lemma lem1691915 (_26099 : real) (_26100 : real) (_26098 : real) (_26101 : real) (h1 : term119) : term292 _26099 _26100 _26098 _26101.
Proof. exact (@lem1691914 _26099 _26100 _26098 h1 _26101). Qed.
Lemma lem1691916 (_26099 : real) (_26100 : real) (_26101 : real) (_26098 : real) : (term292 _26099 _26100 _26098 _26101) = (term271 _26099 _26100 _26101 _26098).
Proof. exact (eq_refl (term292 _26099 _26100 _26098 _26101)). Qed.
Lemma lem1691917 (_26099 : real) (_26100 : real) (_26101 : real) (_26098 : real) (h1 : term119) : term271 _26099 _26100 _26101 _26098.
Proof. exact (EQ_MP (@lem1691916 _26099 _26100 _26101 _26098) (@lem1691915 _26099 _26100 _26098 _26101 h1)). Qed.
Lemma lem1691918 (_26099 : real) (_26100 : real) (_26101 : real) (_26098 : real) (_26102 : real) (h1 : term119) : term293 _26099 _26100 _26101 _26098 _26102.
Proof. exact (@lem1691917 _26099 _26100 _26101 _26098 h1 _26102). Qed.
Lemma lem1691919 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26098 : real) : (term293 _26099 _26100 _26101 _26098 _26102) = (term269 _26099 _26100 _26102 _26101 _26098).
Proof. exact (eq_refl (term293 _26099 _26100 _26101 _26098 _26102)). Qed.
Lemma lem1691920 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26098 : real) (h1 : term119) : term269 _26099 _26100 _26102 _26101 _26098.
Proof. exact (EQ_MP (@lem1691919 _26099 _26100 _26102 _26101 _26098) (@lem1691918 _26099 _26100 _26101 _26098 _26102 h1)). Qed.
Lemma lem1691921 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26098 : real) (_26103 : real) (h1 : term119) : term294 _26099 _26100 _26102 _26101 _26098 _26103.
Proof. exact (@lem1691920 _26099 _26100 _26102 _26101 _26098 h1 _26103). Qed.
Lemma lem1691922 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term294 _26099 _26100 _26102 _26101 _26098 _26103) = (term266 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (eq_refl (term294 _26099 _26100 _26102 _26101 _26098 _26103)). Qed.
Lemma lem1691923 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) (h1 : term119) : term266 _26099 _26100 _26102 _26101 _26103 _26098.
Proof. exact (EQ_MP (@lem1691922 _26099 _26100 _26102 _26101 _26103 _26098) (@lem1691921 _26099 _26100 _26102 _26101 _26098 _26103 h1)). Qed.
Lemma lem1691924 (_26104 : real) (h1 : term122) : term286 _26104.
Proof. exact (@lem1691812 h1 _26104). Qed.
Lemma lem1691925 (_26104 : real) : (term286 _26104) = (term221 _26104).
Proof. exact (eq_refl (term286 _26104)). Qed.
Lemma lem1691926 (_26104 : real) (h1 : term122) : term221 _26104.
Proof. exact (EQ_MP (@lem1691925 _26104) (@lem1691924 _26104 h1)). Qed.
Lemma lem1691927 (_26104 : real) (_26105 : real) (h1 : term122) : term287 _26104 _26105.
Proof. exact (@lem1691926 _26104 h1 _26105). Qed.
Lemma lem1691928 (_26104 : real) (_26105 : real) : (term287 _26104 _26105) = (term219 _26104 _26105).
Proof. exact (eq_refl (term287 _26104 _26105)). Qed.
Lemma lem1691929 (_26104 : real) (_26105 : real) (h1 : term122) : term219 _26104 _26105.
Proof. exact (EQ_MP (@lem1691928 _26104 _26105) (@lem1691927 _26104 _26105 h1)). Qed.
Lemma lem1691930 (_26104 : real) (_26105 : real) (_26106 : real) (h1 : term122) : term288 _26104 _26105 _26106.
Proof. exact (@lem1691929 _26104 _26105 h1 _26106). Qed.
Lemma lem1691931 (_26104 : real) (_26105 : real) (_26106 : real) : (term288 _26104 _26105 _26106) = (term217 _26104 _26105 _26106).
Proof. exact (eq_refl (term288 _26104 _26105 _26106)). Qed.
Lemma lem1691933 (_26107 : real) (h1 : term119) : term289 _26107.
Proof. exact (@lem1691864 h1 _26107). Qed.
Lemma lem1691934 (_26107 : real) : (term289 _26107) = (term277 _26107).
Proof. exact (eq_refl (term289 _26107)). Qed.
Lemma lem1691935 (_26107 : real) (h1 : term119) : term277 _26107.
Proof. exact (EQ_MP (@lem1691934 _26107) (@lem1691933 _26107 h1)). Qed.
Lemma lem1691936 (_26107 : real) (_26108 : real) (h1 : term119) : term290 _26107 _26108.
Proof. exact (@lem1691935 _26107 h1 _26108). Qed.
Lemma lem1691937 (_26108 : real) (_26107 : real) : (term290 _26107 _26108) = (term275 _26108 _26107).
Proof. exact (eq_refl (term290 _26107 _26108)). Qed.
Lemma lem1691938 (_26108 : real) (_26107 : real) (h1 : term119) : term275 _26108 _26107.
Proof. exact (EQ_MP (@lem1691937 _26108 _26107) (@lem1691936 _26107 _26108 h1)). Qed.
Lemma lem1691939 (_26108 : real) (_26107 : real) (_26109 : real) (h1 : term119) : term291 _26108 _26107 _26109.
Proof. exact (@lem1691938 _26108 _26107 h1 _26109). Qed.
Lemma lem1691940 (_26108 : real) (_26109 : real) (_26107 : real) : (term291 _26108 _26107 _26109) = (term273 _26108 _26109 _26107).
Proof. exact (eq_refl (term291 _26108 _26107 _26109)). Qed.
Lemma lem1691941 (_26108 : real) (_26109 : real) (_26107 : real) (h1 : term119) : term273 _26108 _26109 _26107.
Proof. exact (EQ_MP (@lem1691940 _26108 _26109 _26107) (@lem1691939 _26108 _26107 _26109 h1)). Qed.
Lemma lem1691942 (_26108 : real) (_26109 : real) (_26107 : real) (_26110 : real) (h1 : term119) : term292 _26108 _26109 _26107 _26110.
Proof. exact (@lem1691941 _26108 _26109 _26107 h1 _26110). Qed.
Lemma lem1691943 (_26108 : real) (_26109 : real) (_26110 : real) (_26107 : real) : (term292 _26108 _26109 _26107 _26110) = (term271 _26108 _26109 _26110 _26107).
Proof. exact (eq_refl (term292 _26108 _26109 _26107 _26110)). Qed.
Lemma lem1691944 (_26108 : real) (_26109 : real) (_26110 : real) (_26107 : real) (h1 : term119) : term271 _26108 _26109 _26110 _26107.
Proof. exact (EQ_MP (@lem1691943 _26108 _26109 _26110 _26107) (@lem1691942 _26108 _26109 _26107 _26110 h1)). Qed.
Lemma lem1691945 (_26108 : real) (_26109 : real) (_26110 : real) (_26107 : real) (_26111 : real) (h1 : term119) : term293 _26108 _26109 _26110 _26107 _26111.
Proof. exact (@lem1691944 _26108 _26109 _26110 _26107 h1 _26111). Qed.
Lemma lem1691946 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26107 : real) : (term293 _26108 _26109 _26110 _26107 _26111) = (term269 _26108 _26109 _26111 _26110 _26107).
Proof. exact (eq_refl (term293 _26108 _26109 _26110 _26107 _26111)). Qed.
Lemma lem1691947 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26107 : real) (h1 : term119) : term269 _26108 _26109 _26111 _26110 _26107.
Proof. exact (EQ_MP (@lem1691946 _26108 _26109 _26111 _26110 _26107) (@lem1691945 _26108 _26109 _26110 _26107 _26111 h1)). Qed.
Lemma lem1691948 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26107 : real) (_26112 : real) (h1 : term119) : term294 _26108 _26109 _26111 _26110 _26107 _26112.
Proof. exact (@lem1691947 _26108 _26109 _26111 _26110 _26107 h1 _26112). Qed.
Lemma lem1691949 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term294 _26108 _26109 _26111 _26110 _26107 _26112) = (term266 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (eq_refl (term294 _26108 _26109 _26111 _26110 _26107 _26112)). Qed.
Lemma lem1691950 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) (h1 : term119) : term266 _26108 _26109 _26111 _26110 _26112 _26107.
Proof. exact (EQ_MP (@lem1691949 _26108 _26109 _26111 _26110 _26112 _26107) (@lem1691948 _26108 _26109 _26111 _26110 _26107 _26112 h1)). Qed.
Lemma lem1691956 (_26095 : real) (_26096 : real) (_26097 : real) (h1 : term122) : term217 _26095 _26096 _26097.
Proof. exact (EQ_MP (@lem1691904 _26095 _26096 _26097) (@lem1691903 _26095 _26096 _26097 h1)). Qed.
Lemma lem1691960 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term266 _26099 _26100 _26102 _26101 _26103 _26098) = (term295 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (@lem1690563 (term296 _26099 _26101) (term255 _26100 _26098 _26102 _26103) (term262 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1691961 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term297 _26099 _26100 _26102 _26101 _26103 _26098) = (term298 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (@lem1690563 (term296 _26100 _26098) (term250 _26102 _26103) (term262 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1691962 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term299 _26099 _26100 _26102 _26101 _26103 _26098) = (term300 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (@lem1690563 (term301 _26102) (term246 _26102 _26103) (term262 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1691969 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term302 _26099 _26100 _26102 _26101 _26103 _26098) = (term303 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (@lem1690563 (term301 _26103) (term52 _26102 _26103) (term262 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1691970 (_26102 : real) : (term248 _26102) = (term248 _26102).
Proof. exact (eq_refl (term248 _26102)). Qed.
Lemma lem1691973 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term300 _26099 _26100 _26102 _26101 _26103 _26098) = (term304 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (MK_COMB (@lem1691970 _26102) (@lem1691969 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1691974 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term299 _26099 _26100 _26102 _26101 _26103 _26098) = (term304 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (TRANS (@lem1691962 _26099 _26100 _26102 _26101 _26103 _26098) (@lem1691973 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1691975 (_26100 : real) (_26098 : real) : (term253 _26100 _26098) = (term253 _26100 _26098).
Proof. exact (eq_refl (term253 _26100 _26098)). Qed.
Lemma lem1691978 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term298 _26099 _26100 _26102 _26101 _26103 _26098) = (term305 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (MK_COMB (@lem1691975 _26100 _26098) (@lem1691974 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1691979 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term297 _26099 _26100 _26102 _26101 _26103 _26098) = (term305 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (TRANS (@lem1691961 _26099 _26100 _26102 _26101 _26103 _26098) (@lem1691978 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1691980 (_26099 : real) (_26101 : real) : (term253 _26099 _26101) = (term253 _26099 _26101).
Proof. exact (eq_refl (term253 _26099 _26101)). Qed.
Lemma lem1691983 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term295 _26099 _26100 _26102 _26101 _26103 _26098) = (term306 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (MK_COMB (@lem1691980 _26099 _26101) (@lem1691979 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1691985 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term266 _26099 _26100 _26102 _26101 _26103 _26098) = (term306 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (TRANS (@lem1691960 _26099 _26100 _26102 _26101 _26103 _26098) (@lem1691983 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1691986 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) (h1 : term119) : term306 _26099 _26100 _26102 _26101 _26103 _26098.
Proof. exact (EQ_MP (@lem1691985 _26099 _26100 _26102 _26101 _26103 _26098) (@lem1691923 _26099 _26100 _26102 _26101 _26103 _26098 h1)). Qed.
Lemma lem1692002 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term284 a u x v y) : term284 a u x v y.
Proof. exact (h1). Qed.
Lemma lem1692008 (_26104 : real) (_26105 : real) (_26106 : real) (h1 : term122) : term217 _26104 _26105 _26106.
Proof. exact (EQ_MP (@lem1691931 _26104 _26105 _26106) (@lem1691930 _26104 _26105 _26106 h1)). Qed.
Lemma lem1692012 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term266 _26108 _26109 _26111 _26110 _26112 _26107) = (term295 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (@lem1690563 (term296 _26108 _26110) (term255 _26109 _26107 _26111 _26112) (term262 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1692013 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term297 _26108 _26109 _26111 _26110 _26112 _26107) = (term298 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (@lem1690563 (term296 _26109 _26107) (term250 _26111 _26112) (term262 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1692014 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term299 _26108 _26109 _26111 _26110 _26112 _26107) = (term300 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (@lem1690563 (term301 _26111) (term246 _26111 _26112) (term262 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1692021 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term302 _26108 _26109 _26111 _26110 _26112 _26107) = (term303 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (@lem1690563 (term301 _26112) (term52 _26111 _26112) (term262 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1692022 (_26111 : real) : (term248 _26111) = (term248 _26111).
Proof. exact (eq_refl (term248 _26111)). Qed.
Lemma lem1692025 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term300 _26108 _26109 _26111 _26110 _26112 _26107) = (term304 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (MK_COMB (@lem1692022 _26111) (@lem1692021 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1692026 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term299 _26108 _26109 _26111 _26110 _26112 _26107) = (term304 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (TRANS (@lem1692014 _26108 _26109 _26111 _26110 _26112 _26107) (@lem1692025 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1692027 (_26109 : real) (_26107 : real) : (term253 _26109 _26107) = (term253 _26109 _26107).
Proof. exact (eq_refl (term253 _26109 _26107)). Qed.
Lemma lem1692030 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term298 _26108 _26109 _26111 _26110 _26112 _26107) = (term305 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (MK_COMB (@lem1692027 _26109 _26107) (@lem1692026 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1692031 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term297 _26108 _26109 _26111 _26110 _26112 _26107) = (term305 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (TRANS (@lem1692013 _26108 _26109 _26111 _26110 _26112 _26107) (@lem1692030 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1692032 (_26108 : real) (_26110 : real) : (term253 _26108 _26110) = (term253 _26108 _26110).
Proof. exact (eq_refl (term253 _26108 _26110)). Qed.
Lemma lem1692035 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term295 _26108 _26109 _26111 _26110 _26112 _26107) = (term306 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (MK_COMB (@lem1692032 _26108 _26110) (@lem1692031 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1692037 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term266 _26108 _26109 _26111 _26110 _26112 _26107) = (term306 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (TRANS (@lem1692012 _26108 _26109 _26111 _26110 _26112 _26107) (@lem1692035 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1692038 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) (h1 : term119) : term306 _26108 _26109 _26111 _26110 _26112 _26107.
Proof. exact (EQ_MP (@lem1692037 _26108 _26109 _26111 _26110 _26112 _26107) (@lem1691950 _26108 _26109 _26111 _26110 _26112 _26107 h1)). Qed.
Lemma lem1692054 (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term285 u x v y b) : term285 u x v y b.
Proof. exact (h1). Qed.
Lemma lem1692074 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1692075 (_26117 : real) (_26119 : real) (h1 : _26117 = _26119) : _26117 = _26119.
Proof. exact (h1). Qed.
Lemma lem1692076 (_26118 : real) (_26120 : real) (h1 : _26118 = _26120) : _26118 = _26120.
Proof. exact (h1). Qed.
Lemma lem1692077 (_26117 : real) (_26119 : real) (h1 : _26117 = _26119) : (real_lt _26117) = (real_lt _26119).
Proof. exact (MK_COMB (@lem1692074) (@lem1692075 _26117 _26119 h1)). Qed.
Lemma lem1692078 (_26117 : real) (_26119 : real) (_26118 : real) (_26120 : real) (h1 : _26117 = _26119) (h2 : _26118 = _26120) : (real_lt _26117 _26118) = (real_lt _26119 _26120).
Proof. exact (MK_COMB (@lem1692077 _26117 _26119 h1) (@lem1692076 _26118 _26120 h2)). Qed.
Lemma lem1692080 (b : Prop) (a : Prop) : term307 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1692081 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : term308 _26119 _26120 _26117 _26118.
Proof. exact (@lem1692080 (real_lt _26119 _26120) (real_lt _26117 _26118)). Qed.
Lemma lem1692082 (_26117 : real) (_26119 : real) (_26118 : real) (_26120 : real) (h1 : _26117 = _26119) (h2 : _26118 = _26120) : term309 _26119 _26120 _26117 _26118.
Proof. exact (@lem1692081 _26119 _26120 _26117 _26118 (@lem1692078 _26117 _26119 _26118 _26120 h1 h2)). Qed.
Lemma lem1692083 (_26120 : real) (_26118 : real) (_26117 : real) (_26119 : real) (h1 : _26117 = _26119) : term310 _26119 _26120 _26117 _26118.
Proof. exact (fun h0 : _26118 = _26120 => @lem1692082 _26117 _26119 _26118 _26120 h1 h0). Qed.
Lemma lem1692085 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1692086 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : (term310 _26119 _26120 _26117 _26118) = (term311 _26119 _26120 _26117 _26118).
Proof. exact (@lem1692085 (_26118 = _26120) (term309 _26119 _26120 _26117 _26118)). Qed.
Lemma lem1692087 (_26120 : real) (_26118 : real) (_26117 : real) (_26119 : real) (h1 : _26117 = _26119) : term311 _26119 _26120 _26117 _26118.
Proof. exact (EQ_MP (@lem1692086 _26119 _26120 _26117 _26118) (@lem1692083 _26120 _26118 _26117 _26119 h1)). Qed.
Lemma lem1692088 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : term312 _26119 _26120 _26117 _26118.
Proof. exact (fun h0 : _26117 = _26119 => @lem1692087 _26120 _26118 _26117 _26119 h0). Qed.
Lemma lem1692090 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1692091 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : (term312 _26119 _26120 _26117 _26118) = (term313 _26119 _26120 _26117 _26118).
Proof. exact (@lem1692090 (_26117 = _26119) (term311 _26119 _26120 _26117 _26118)). Qed.
Lemma lem1692092 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : term313 _26119 _26120 _26117 _26118.
Proof. exact (EQ_MP (@lem1692091 _26119 _26120 _26117 _26118) (@lem1692088 _26119 _26120 _26117 _26118)). Qed.
Lemma lem1692152 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1691635 a u x v y b h1)). Qed.
Lemma lem1692153 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1692152 a u x v y b h1). Qed.
Lemma lem1692155 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1692156 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1692155 ((real_add u v) = term39)). Qed.
Lemma lem1692157 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1692156 u v) (@lem1692153 a u x v y b h1)). Qed.
Lemma lem1692163 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1692164 (_26097 : real) (_26095 : real) (_26096 : real) : (term217 _26095 _26096 _26097) = (term314 _26097 _26095 _26096).
Proof. exact (@lem1692163 ((term31 _26095 _26096 _26097) = _26097) (term52 _26095 _26096)). Qed.
Lemma lem1692174 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1692175 (_26097 : real) (_26095 : real) (_26096 : real) : (term315 _26095 _26096 _26097) = (term316 _26097 _26095 _26096).
Proof. exact (MK_COMB (@lem1692174) (@lem1692164 _26097 _26095 _26096)). Qed.
Lemma lem1692185 (_26097 : real) (_26095 : real) (_26096 : real) : (term314 _26097 _26095 _26096) = (term314 _26097 _26095 _26096).
Proof. exact (eq_refl (term314 _26097 _26095 _26096)). Qed.
Lemma lem1692186 (_26097 : real) (_26095 : real) (_26096 : real) : ((term217 _26095 _26096 _26097) = (term314 _26097 _26095 _26096)) = ((term314 _26097 _26095 _26096) = (term314 _26097 _26095 _26096)).
Proof. exact (MK_COMB (@lem1692175 _26097 _26095 _26096) (@lem1692185 _26097 _26095 _26096)). Qed.
Lemma lem1692188 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1692189 (x : Prop) : (x = x) = True.
Proof. exact (@lem1692188 Prop x). Qed.
Lemma lem1692190 (_26097 : real) (_26095 : real) (_26096 : real) : ((term314 _26097 _26095 _26096) = (term314 _26097 _26095 _26096)) = True.
Proof. exact (@lem1692189 (term314 _26097 _26095 _26096)). Qed.
Lemma lem1692191 (_26097 : real) (_26095 : real) (_26096 : real) : ((term217 _26095 _26096 _26097) = (term314 _26097 _26095 _26096)) = True.
Proof. exact (TRANS (@lem1692186 _26097 _26095 _26096) (@lem1692190 _26097 _26095 _26096)). Qed.
Lemma lem1692192 (_26097 : real) (_26095 : real) (_26096 : real) : True = ((term217 _26095 _26096 _26097) = (term314 _26097 _26095 _26096)).
Proof. exact (SYM (@lem1692191 _26097 _26095 _26096)). Qed.
Lemma lem1692193 (_26097 : real) (_26095 : real) (_26096 : real) : (term217 _26095 _26096 _26097) = (term314 _26097 _26095 _26096).
Proof. exact (EQ_MP (@lem1692192 _26097 _26095 _26096) (@lem0)). Qed.
Lemma lem1692194 (_26097 : real) (_26095 : real) (_26096 : real) (h1 : term122) : term314 _26097 _26095 _26096.
Proof. exact (EQ_MP (@lem1692193 _26097 _26095 _26096) (@lem1691956 _26095 _26096 _26097 h1)). Qed.
Lemma lem1692196 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1692197 (_26095 : real) (_26096 : real) (_26097 : real) : (term314 _26097 _26095 _26096) = (term317 _26095 _26096 _26097).
Proof. exact (@lem1692196 (term52 _26095 _26096) ((term31 _26095 _26096 _26097) = _26097)). Qed.
Lemma lem1692199 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1692200 (_26095 : real) (_26096 : real) : (term318 _26095 _26096) = ((real_add _26095 _26096) = term39).
Proof. exact (@lem1692199 ((real_add _26095 _26096) = term39)). Qed.
Lemma lem1692201 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1692202 (_26095 : real) (_26096 : real) : (term319 _26095 _26096) = (term320 _26095 _26096).
Proof. exact (MK_COMB (@lem1692201) (@lem1692200 _26095 _26096)). Qed.
Lemma lem1692203 (_26095 : real) (_26096 : real) (_26097 : real) : ((term31 _26095 _26096 _26097) = _26097) = ((term31 _26095 _26096 _26097) = _26097).
Proof. exact (eq_refl ((term31 _26095 _26096 _26097) = _26097)). Qed.
Lemma lem1692204 (_26095 : real) (_26096 : real) (_26097 : real) : (term317 _26095 _26096 _26097) = (term1 _26095 _26096 _26097).
Proof. exact (MK_COMB (@lem1692202 _26095 _26096) (@lem1692203 _26095 _26096 _26097)). Qed.
Lemma lem1692205 (_26095 : real) (_26096 : real) (_26097 : real) : (term314 _26097 _26095 _26096) = (term1 _26095 _26096 _26097).
Proof. exact (TRANS (@lem1692197 _26095 _26096 _26097) (@lem1692204 _26095 _26096 _26097)). Qed.
Lemma lem1692208 (_26095 : real) (_26096 : real) (_26097 : real) (h1 : term122) : term1 _26095 _26096 _26097.
Proof. exact (EQ_MP (@lem1692205 _26095 _26096 _26097) (@lem1692194 _26097 _26095 _26096 h1)). Qed.
Lemma lem1692209 (u : real) (v : real) (_26097 : real) (h1 : term122) : term1 u v _26097.
Proof. exact (@lem1692208 u v _26097 h1). Qed.
Lemma lem1692212 (_26097 : real) (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term122) (h2 : term170 a u x v y b) : (term31 u v _26097) = _26097.
Proof. exact (@lem1692209 u v _26097 h1 (@lem1692157 a u x v y b h2)). Qed.
Lemma lem1692213 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term122) (h2 : term170 a u x v y b) : (term31 u v a) = a.
Proof. exact (@lem1692212 a a u x v y b h1 h2). Qed.
Lemma lem1692214 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term122) (h2 : term170 a u x v y b) : term107 u v a.
Proof. exact (fun h0 : term44 u v a => @lem1692213 a u x v y b h1 h2). Qed.
Lemma lem1692216 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1692217 (u : real) (v : real) (a : real) : (term107 u v a) = ((term31 u v a) = a).
Proof. exact (@lem1692216 ((term31 u v a) = a)). Qed.
Lemma lem1692218 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term122) (h2 : term170 a u x v y b) : (term31 u v a) = a.
Proof. exact (EQ_MP (@lem1692217 u v a) (@lem1692214 a u x v y b h1 h2)). Qed.
Lemma lem1692220 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1692221 (u : real) (x : real) (v : real) (y : real) : (term321 u x v y) = (term321 u x v y).
Proof. exact (@lem1692220 (term321 u x v y)). Qed.
Lemma lem1692222 (u : real) (x : real) (v : real) (y : real) : term322 u x v y.
Proof. exact (fun h0 : term323 u x v y => @lem1692221 u x v y). Qed.
Lemma lem1692224 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1692225 (u : real) (x : real) (v : real) (y : real) : (term322 u x v y) = ((term321 u x v y) = (term321 u x v y)).
Proof. exact (@lem1692224 ((term321 u x v y) = (term321 u x v y))). Qed.
Lemma lem1692226 (u : real) (x : real) (v : real) (y : real) : (term321 u x v y) = (term321 u x v y).
Proof. exact (EQ_MP (@lem1692225 u x v y) (@lem1692222 u x v y)). Qed.
Lemma lem1692228 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : real_lt a x.
Proof. exact (proj1 (@lem1691626 a u x v y b h1)). Qed.
Lemma lem1692229 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term324 a x.
Proof. exact (fun h0 : term296 a x => @lem1692228 a u x v y b h1). Qed.
Lemma lem1692231 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1692232 (a : real) (x : real) : (term324 a x) = (real_lt a x).
Proof. exact (@lem1692231 (real_lt a x)). Qed.
Lemma lem1692233 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : real_lt a x.
Proof. exact (EQ_MP (@lem1692232 a x) (@lem1692229 a u x v y b h1)). Qed.
Lemma lem1692235 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : real_lt a y.
Proof. exact (proj1 (@lem1691629 a u x v y b h1)). Qed.
Lemma lem1692236 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term324 a y.
Proof. exact (fun h0 : term296 a y => @lem1692235 a u x v y b h1). Qed.
Lemma lem1692238 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1692239 (a : real) (y : real) : (term324 a y) = (real_lt a y).
Proof. exact (@lem1692238 (real_lt a y)). Qed.
Lemma lem1692240 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : real_lt a y.
Proof. exact (EQ_MP (@lem1692239 a y) (@lem1692236 a u x v y b h1)). Qed.
Lemma lem1692242 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term247 u.
Proof. exact (proj1 (@lem1691633 a u x v y b h1)). Qed.
Lemma lem1692243 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term325 u.
Proof. exact (fun h0 : term301 u => @lem1692242 a u x v y b h1). Qed.
Lemma lem1692245 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1692246 (u : real) : (term325 u) = (term247 u).
Proof. exact (@lem1692245 (term247 u)). Qed.
Lemma lem1692247 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term247 u.
Proof. exact (EQ_MP (@lem1692246 u) (@lem1692243 a u x v y b h1)). Qed.
Lemma lem1692249 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term247 v.
Proof. exact (proj1 (@lem1691635 a u x v y b h1)). Qed.
Lemma lem1692250 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term325 v.
Proof. exact (fun h0 : term301 v => @lem1692249 a u x v y b h1). Qed.
Lemma lem1692252 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1692253 (v : real) : (term325 v) = (term247 v).
Proof. exact (@lem1692252 (term247 v)). Qed.
Lemma lem1692254 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term247 v.
Proof. exact (EQ_MP (@lem1692253 v) (@lem1692250 a u x v y b h1)). Qed.
Lemma lem1692256 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1691635 a u x v y b h1)). Qed.
Lemma lem1692257 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1692256 a u x v y b h1). Qed.
Lemma lem1692259 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1692260 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1692259 ((real_add u v) = term39)). Qed.
Lemma lem1692261 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1692260 u v) (@lem1692257 a u x v y b h1)). Qed.
Lemma lem1692277 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692278 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term305 _26099 _26100 _26102 _26101 _26103 _26098) = (term326 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (@lem1692277 (term301 _26102) (term296 _26100 _26098) (term303 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1692292 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692293 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term327 _26099 _26100 _26102 _26101 _26103 _26098) = (term328 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (@lem1692292 (term301 _26103) (term296 _26100 _26098) (term329 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1692307 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692308 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term330 _26099 _26100 _26102 _26101 _26103 _26098) = (term331 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (@lem1692307 (term52 _26102 _26103) (term296 _26100 _26098) (term262 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1692324 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1692325 (_26099 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term332 _26099 _26100 _26102 _26101 _26103 _26098) = (term333 _26099 _26102 _26101 _26103 _26100 _26098).
Proof. exact (@lem1692324 (term262 _26099 _26100 _26102 _26101 _26103 _26098) (term296 _26100 _26098)). Qed.
Lemma lem1692331 (_26102 : real) (_26103 : real) : (term232 _26102 _26103) = (term232 _26102 _26103).
Proof. exact (eq_refl (term232 _26102 _26103)). Qed.
Lemma lem1692332 (_26099 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term331 _26099 _26100 _26102 _26101 _26103 _26098) = (term334 _26099 _26102 _26101 _26103 _26100 _26098).
Proof. exact (MK_COMB (@lem1692331 _26102 _26103) (@lem1692325 _26099 _26102 _26101 _26103 _26100 _26098)). Qed.
Lemma lem1692336 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692337 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term334 _26099 _26102 _26101 _26103 _26100 _26098) = (term335 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (@lem1692336 (term262 _26099 _26100 _26102 _26101 _26103 _26098) (term52 _26102 _26103) (term296 _26100 _26098)). Qed.
Lemma lem1692355 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term331 _26099 _26100 _26102 _26101 _26103 _26098) = (term335 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (TRANS (@lem1692332 _26099 _26102 _26101 _26103 _26100 _26098) (@lem1692337 _26099 _26101 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692356 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term330 _26099 _26100 _26102 _26101 _26103 _26098) = (term335 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (TRANS (@lem1692308 _26099 _26100 _26102 _26101 _26103 _26098) (@lem1692355 _26099 _26101 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692357 (_26103 : real) : (term248 _26103) = (term248 _26103).
Proof. exact (eq_refl (term248 _26103)). Qed.
Lemma lem1692358 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term328 _26099 _26100 _26102 _26101 _26103 _26098) = (term336 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (MK_COMB (@lem1692357 _26103) (@lem1692356 _26099 _26101 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692362 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692363 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term336 _26099 _26101 _26102 _26103 _26100 _26098) = (term337 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (@lem1692362 (term262 _26099 _26100 _26102 _26101 _26103 _26098) (term301 _26103) (term338 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692377 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692378 (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term339 _26102 _26103 _26100 _26098) = (term340 _26102 _26103 _26100 _26098).
Proof. exact (@lem1692377 (term52 _26102 _26103) (term301 _26103) (term296 _26100 _26098)). Qed.
Lemma lem1692396 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term341 _26099 _26100 _26102 _26101 _26103 _26098) = (term341 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (eq_refl (term341 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1692397 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term337 _26099 _26101 _26102 _26103 _26100 _26098) = (term342 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (MK_COMB (@lem1692396 _26099 _26100 _26102 _26101 _26103 _26098) (@lem1692378 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692408 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term336 _26099 _26101 _26102 _26103 _26100 _26098) = (term342 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (TRANS (@lem1692363 _26099 _26101 _26102 _26103 _26100 _26098) (@lem1692397 _26099 _26101 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692409 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term328 _26099 _26100 _26102 _26101 _26103 _26098) = (term342 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (TRANS (@lem1692358 _26099 _26101 _26102 _26103 _26100 _26098) (@lem1692408 _26099 _26101 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692410 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term327 _26099 _26100 _26102 _26101 _26103 _26098) = (term342 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (TRANS (@lem1692293 _26099 _26100 _26102 _26101 _26103 _26098) (@lem1692409 _26099 _26101 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692411 (_26102 : real) : (term248 _26102) = (term248 _26102).
Proof. exact (eq_refl (term248 _26102)). Qed.
Lemma lem1692412 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term326 _26099 _26100 _26102 _26101 _26103 _26098) = (term343 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (MK_COMB (@lem1692411 _26102) (@lem1692410 _26099 _26101 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692416 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692417 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term343 _26099 _26101 _26102 _26103 _26100 _26098) = (term344 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (@lem1692416 (term262 _26099 _26100 _26102 _26101 _26103 _26098) (term301 _26102) (term340 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692431 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692432 (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term345 _26102 _26103 _26100 _26098) = (term346 _26102 _26103 _26100 _26098).
Proof. exact (@lem1692431 (term52 _26102 _26103) (term301 _26102) (term347 _26103 _26100 _26098)). Qed.
Lemma lem1692460 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term341 _26099 _26100 _26102 _26101 _26103 _26098) = (term341 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (eq_refl (term341 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1692461 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term344 _26099 _26101 _26102 _26103 _26100 _26098) = (term348 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (MK_COMB (@lem1692460 _26099 _26100 _26102 _26101 _26103 _26098) (@lem1692432 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692472 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term343 _26099 _26101 _26102 _26103 _26100 _26098) = (term348 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (TRANS (@lem1692417 _26099 _26101 _26102 _26103 _26100 _26098) (@lem1692461 _26099 _26101 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692473 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term326 _26099 _26100 _26102 _26101 _26103 _26098) = (term348 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (TRANS (@lem1692412 _26099 _26101 _26102 _26103 _26100 _26098) (@lem1692472 _26099 _26101 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692474 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term305 _26099 _26100 _26102 _26101 _26103 _26098) = (term348 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (TRANS (@lem1692278 _26099 _26100 _26102 _26101 _26103 _26098) (@lem1692473 _26099 _26101 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692475 (_26099 : real) (_26101 : real) : (term253 _26099 _26101) = (term253 _26099 _26101).
Proof. exact (eq_refl (term253 _26099 _26101)). Qed.
Lemma lem1692476 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term306 _26099 _26100 _26102 _26101 _26103 _26098) = (term349 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (MK_COMB (@lem1692475 _26099 _26101) (@lem1692474 _26099 _26101 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692480 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692481 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term349 _26099 _26101 _26102 _26103 _26100 _26098) = (term350 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (@lem1692480 (term262 _26099 _26100 _26102 _26101 _26103 _26098) (term296 _26099 _26101) (term346 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692495 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692496 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term351 _26099 _26101 _26102 _26103 _26100 _26098) = (term352 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (@lem1692495 (term52 _26102 _26103) (term296 _26099 _26101) (term353 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692512 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692513 (_26102 : real) (_26099 : real) (_26101 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term354 _26099 _26101 _26102 _26103 _26100 _26098) = (term355 _26102 _26099 _26101 _26103 _26100 _26098).
Proof. exact (@lem1692512 (term301 _26102) (term296 _26099 _26101) (term347 _26103 _26100 _26098)). Qed.
Lemma lem1692527 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692528 (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : (term356 _26099 _26101 _26103 _26100 _26098) = (term357 _26103 _26099 _26101 _26100 _26098).
Proof. exact (@lem1692527 (term301 _26103) (term296 _26099 _26101) (term296 _26100 _26098)). Qed.
Lemma lem1692544 (_26102 : real) : (term248 _26102) = (term248 _26102).
Proof. exact (eq_refl (term248 _26102)). Qed.
Lemma lem1692545 (_26102 : real) (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : (term355 _26102 _26099 _26101 _26103 _26100 _26098) = (term358 _26102 _26103 _26099 _26101 _26100 _26098).
Proof. exact (MK_COMB (@lem1692544 _26102) (@lem1692528 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692556 (_26102 : real) (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : (term354 _26099 _26101 _26102 _26103 _26100 _26098) = (term358 _26102 _26103 _26099 _26101 _26100 _26098).
Proof. exact (TRANS (@lem1692513 _26102 _26099 _26101 _26103 _26100 _26098) (@lem1692545 _26102 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692557 (_26102 : real) (_26103 : real) : (term232 _26102 _26103) = (term232 _26102 _26103).
Proof. exact (eq_refl (term232 _26102 _26103)). Qed.
Lemma lem1692558 (_26102 : real) (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : (term352 _26099 _26101 _26102 _26103 _26100 _26098) = (term359 _26102 _26103 _26099 _26101 _26100 _26098).
Proof. exact (MK_COMB (@lem1692557 _26102 _26103) (@lem1692556 _26102 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692569 (_26102 : real) (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : (term351 _26099 _26101 _26102 _26103 _26100 _26098) = (term359 _26102 _26103 _26099 _26101 _26100 _26098).
Proof. exact (TRANS (@lem1692496 _26099 _26101 _26102 _26103 _26100 _26098) (@lem1692558 _26102 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692570 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term341 _26099 _26100 _26102 _26101 _26103 _26098) = (term341 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (eq_refl (term341 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1692571 (_26102 : real) (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : (term350 _26099 _26101 _26102 _26103 _26100 _26098) = (term360 _26102 _26103 _26099 _26101 _26100 _26098).
Proof. exact (MK_COMB (@lem1692570 _26099 _26100 _26102 _26101 _26103 _26098) (@lem1692569 _26102 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692582 (_26102 : real) (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : (term349 _26099 _26101 _26102 _26103 _26100 _26098) = (term360 _26102 _26103 _26099 _26101 _26100 _26098).
Proof. exact (TRANS (@lem1692481 _26099 _26101 _26102 _26103 _26100 _26098) (@lem1692571 _26102 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692583 (_26102 : real) (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : (term306 _26099 _26100 _26102 _26101 _26103 _26098) = (term360 _26102 _26103 _26099 _26101 _26100 _26098).
Proof. exact (TRANS (@lem1692476 _26099 _26101 _26102 _26103 _26100 _26098) (@lem1692582 _26102 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692584 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1692585 (_26102 : real) (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : (term361 _26099 _26100 _26102 _26101 _26103 _26098) = (term362 _26102 _26103 _26099 _26101 _26100 _26098).
Proof. exact (MK_COMB (@lem1692584) (@lem1692583 _26102 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692609 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692610 (_26100 : real) (_26098 : real) (_26102 : real) (_26103 : real) : (term255 _26100 _26098 _26102 _26103) = (term363 _26100 _26098 _26102 _26103).
Proof. exact (@lem1692609 (term301 _26102) (term296 _26100 _26098) (term246 _26102 _26103)). Qed.
Lemma lem1692624 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692625 (_26100 : real) (_26098 : real) (_26102 : real) (_26103 : real) : (term364 _26100 _26098 _26102 _26103) = (term365 _26100 _26098 _26102 _26103).
Proof. exact (@lem1692624 (term301 _26103) (term296 _26100 _26098) (term52 _26102 _26103)). Qed.
Lemma lem1692639 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1692640 (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term366 _26100 _26098 _26102 _26103) = (term338 _26102 _26103 _26100 _26098).
Proof. exact (@lem1692639 (term52 _26102 _26103) (term296 _26100 _26098)). Qed.
Lemma lem1692648 (_26103 : real) : (term248 _26103) = (term248 _26103).
Proof. exact (eq_refl (term248 _26103)). Qed.
Lemma lem1692649 (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term365 _26100 _26098 _26102 _26103) = (term339 _26102 _26103 _26100 _26098).
Proof. exact (MK_COMB (@lem1692648 _26103) (@lem1692640 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692653 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692654 (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term339 _26102 _26103 _26100 _26098) = (term340 _26102 _26103 _26100 _26098).
Proof. exact (@lem1692653 (term52 _26102 _26103) (term301 _26103) (term296 _26100 _26098)). Qed.
Lemma lem1692672 (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term365 _26100 _26098 _26102 _26103) = (term340 _26102 _26103 _26100 _26098).
Proof. exact (TRANS (@lem1692649 _26102 _26103 _26100 _26098) (@lem1692654 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692673 (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term364 _26100 _26098 _26102 _26103) = (term340 _26102 _26103 _26100 _26098).
Proof. exact (TRANS (@lem1692625 _26100 _26098 _26102 _26103) (@lem1692672 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692674 (_26102 : real) : (term248 _26102) = (term248 _26102).
Proof. exact (eq_refl (term248 _26102)). Qed.
Lemma lem1692675 (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term363 _26100 _26098 _26102 _26103) = (term345 _26102 _26103 _26100 _26098).
Proof. exact (MK_COMB (@lem1692674 _26102) (@lem1692673 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692679 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692680 (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term345 _26102 _26103 _26100 _26098) = (term346 _26102 _26103 _26100 _26098).
Proof. exact (@lem1692679 (term52 _26102 _26103) (term301 _26102) (term347 _26103 _26100 _26098)). Qed.
Lemma lem1692708 (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term363 _26100 _26098 _26102 _26103) = (term346 _26102 _26103 _26100 _26098).
Proof. exact (TRANS (@lem1692675 _26102 _26103 _26100 _26098) (@lem1692680 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692709 (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term255 _26100 _26098 _26102 _26103) = (term346 _26102 _26103 _26100 _26098).
Proof. exact (TRANS (@lem1692610 _26100 _26098 _26102 _26103) (@lem1692708 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692710 (_26099 : real) (_26101 : real) : (term253 _26099 _26101) = (term253 _26099 _26101).
Proof. exact (eq_refl (term253 _26099 _26101)). Qed.
Lemma lem1692711 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term259 _26099 _26101 _26100 _26098 _26102 _26103) = (term351 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (MK_COMB (@lem1692710 _26099 _26101) (@lem1692709 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692715 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692716 (_26099 : real) (_26101 : real) (_26102 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term351 _26099 _26101 _26102 _26103 _26100 _26098) = (term352 _26099 _26101 _26102 _26103 _26100 _26098).
Proof. exact (@lem1692715 (term52 _26102 _26103) (term296 _26099 _26101) (term353 _26102 _26103 _26100 _26098)). Qed.
Lemma lem1692732 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692733 (_26102 : real) (_26099 : real) (_26101 : real) (_26103 : real) (_26100 : real) (_26098 : real) : (term354 _26099 _26101 _26102 _26103 _26100 _26098) = (term355 _26102 _26099 _26101 _26103 _26100 _26098).
Proof. exact (@lem1692732 (term301 _26102) (term296 _26099 _26101) (term347 _26103 _26100 _26098)). Qed.
Lemma lem1692747 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692748 (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : (term356 _26099 _26101 _26103 _26100 _26098) = (term357 _26103 _26099 _26101 _26100 _26098).
Proof. exact (@lem1692747 (term301 _26103) (term296 _26099 _26101) (term296 _26100 _26098)). Qed.
Lemma lem1692764 (_26102 : real) : (term248 _26102) = (term248 _26102).
Proof. exact (eq_refl (term248 _26102)). Qed.
Lemma lem1692765 (_26102 : real) (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : (term355 _26102 _26099 _26101 _26103 _26100 _26098) = (term358 _26102 _26103 _26099 _26101 _26100 _26098).
Proof. exact (MK_COMB (@lem1692764 _26102) (@lem1692748 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692776 (_26102 : real) (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : (term354 _26099 _26101 _26102 _26103 _26100 _26098) = (term358 _26102 _26103 _26099 _26101 _26100 _26098).
Proof. exact (TRANS (@lem1692733 _26102 _26099 _26101 _26103 _26100 _26098) (@lem1692765 _26102 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692777 (_26102 : real) (_26103 : real) : (term232 _26102 _26103) = (term232 _26102 _26103).
Proof. exact (eq_refl (term232 _26102 _26103)). Qed.
Lemma lem1692778 (_26102 : real) (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : (term352 _26099 _26101 _26102 _26103 _26100 _26098) = (term359 _26102 _26103 _26099 _26101 _26100 _26098).
Proof. exact (MK_COMB (@lem1692777 _26102 _26103) (@lem1692776 _26102 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692789 (_26102 : real) (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : (term351 _26099 _26101 _26102 _26103 _26100 _26098) = (term359 _26102 _26103 _26099 _26101 _26100 _26098).
Proof. exact (TRANS (@lem1692716 _26099 _26101 _26102 _26103 _26100 _26098) (@lem1692778 _26102 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692790 (_26102 : real) (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : (term259 _26099 _26101 _26100 _26098 _26102 _26103) = (term359 _26102 _26103 _26099 _26101 _26100 _26098).
Proof. exact (TRANS (@lem1692711 _26099 _26101 _26102 _26103 _26100 _26098) (@lem1692789 _26102 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692791 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term341 _26099 _26100 _26102 _26101 _26103 _26098) = (term341 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (eq_refl (term341 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1692792 (_26102 : real) (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : (term367 _26099 _26101 _26100 _26098 _26102 _26103) = (term360 _26102 _26103 _26099 _26101 _26100 _26098).
Proof. exact (MK_COMB (@lem1692791 _26099 _26100 _26102 _26101 _26103 _26098) (@lem1692790 _26102 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692803 (_26102 : real) (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : ((term306 _26099 _26100 _26102 _26101 _26103 _26098) = (term367 _26099 _26101 _26100 _26098 _26102 _26103)) = ((term360 _26102 _26103 _26099 _26101 _26100 _26098) = (term360 _26102 _26103 _26099 _26101 _26100 _26098)).
Proof. exact (MK_COMB (@lem1692585 _26102 _26103 _26099 _26101 _26100 _26098) (@lem1692792 _26102 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692805 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1692806 (x : Prop) : (x = x) = True.
Proof. exact (@lem1692805 Prop x). Qed.
Lemma lem1692807 (_26102 : real) (_26103 : real) (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) : ((term360 _26102 _26103 _26099 _26101 _26100 _26098) = (term360 _26102 _26103 _26099 _26101 _26100 _26098)) = True.
Proof. exact (@lem1692806 (term360 _26102 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692808 (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) (_26102 : real) (_26103 : real) : ((term306 _26099 _26100 _26102 _26101 _26103 _26098) = (term367 _26099 _26101 _26100 _26098 _26102 _26103)) = True.
Proof. exact (TRANS (@lem1692803 _26102 _26103 _26099 _26101 _26100 _26098) (@lem1692807 _26102 _26103 _26099 _26101 _26100 _26098)). Qed.
Lemma lem1692809 (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) (_26102 : real) (_26103 : real) : True = ((term306 _26099 _26100 _26102 _26101 _26103 _26098) = (term367 _26099 _26101 _26100 _26098 _26102 _26103)).
Proof. exact (SYM (@lem1692808 _26099 _26101 _26100 _26098 _26102 _26103)). Qed.
Lemma lem1692810 (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) (_26102 : real) (_26103 : real) : (term306 _26099 _26100 _26102 _26101 _26103 _26098) = (term367 _26099 _26101 _26100 _26098 _26102 _26103).
Proof. exact (EQ_MP (@lem1692809 _26099 _26101 _26100 _26098 _26102 _26103) (@lem0)). Qed.
Lemma lem1692811 (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) (_26102 : real) (_26103 : real) (h1 : term119) : term367 _26099 _26101 _26100 _26098 _26102 _26103.
Proof. exact (EQ_MP (@lem1692810 _26099 _26101 _26100 _26098 _26102 _26103) (@lem1691986 _26099 _26100 _26102 _26101 _26103 _26098 h1)). Qed.
Lemma lem1692813 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1692814 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term367 _26099 _26101 _26100 _26098 _26102 _26103) = (term368 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (@lem1692813 (term259 _26099 _26101 _26100 _26098 _26102 _26103) (term262 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1692816 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1692817 (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) (_26102 : real) (_26103 : real) : (term369 _26099 _26101 _26100 _26098 _26102 _26103) = (term370 _26099 _26101 _26100 _26098 _26102 _26103).
Proof. exact (@lem1692816 (term296 _26099 _26101) (term255 _26100 _26098 _26102 _26103)). Qed.
Lemma lem1692819 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1692820 (_26099 : real) (_26101 : real) : (term371 _26099 _26101) = (real_lt _26099 _26101).
Proof. exact (@lem1692819 (real_lt _26099 _26101)). Qed.
Lemma lem1692821 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1692822 (_26099 : real) (_26101 : real) : (term372 _26099 _26101) = (term373 _26099 _26101).
Proof. exact (MK_COMB (@lem1692821) (@lem1692820 _26099 _26101)). Qed.
Lemma lem1692824 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1692825 (_26100 : real) (_26098 : real) (_26102 : real) (_26103 : real) : (term374 _26100 _26098 _26102 _26103) = (term375 _26100 _26098 _26102 _26103).
Proof. exact (@lem1692824 (term296 _26100 _26098) (term250 _26102 _26103)). Qed.
Lemma lem1692827 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1692828 (_26100 : real) (_26098 : real) : (term371 _26100 _26098) = (real_lt _26100 _26098).
Proof. exact (@lem1692827 (real_lt _26100 _26098)). Qed.
Lemma lem1692829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1692830 (_26100 : real) (_26098 : real) : (term372 _26100 _26098) = (term373 _26100 _26098).
Proof. exact (MK_COMB (@lem1692829) (@lem1692828 _26100 _26098)). Qed.
Lemma lem1692832 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1692833 (_26102 : real) (_26103 : real) : (term376 _26102 _26103) = (term377 _26102 _26103).
Proof. exact (@lem1692832 (term301 _26102) (term246 _26102 _26103)). Qed.
Lemma lem1692835 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1692836 (_26102 : real) : (term378 _26102) = (term247 _26102).
Proof. exact (@lem1692835 (term247 _26102)). Qed.
Lemma lem1692837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1692838 (_26102 : real) : (term379 _26102) = (term380 _26102).
Proof. exact (MK_COMB (@lem1692837) (@lem1692836 _26102)). Qed.
Lemma lem1692840 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1692841 (_26102 : real) (_26103 : real) : (term381 _26102 _26103) = (term382 _26102 _26103).
Proof. exact (@lem1692840 (term301 _26103) (term52 _26102 _26103)). Qed.
Lemma lem1692843 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1692844 (_26103 : real) : (term378 _26103) = (term247 _26103).
Proof. exact (@lem1692843 (term247 _26103)). Qed.
Lemma lem1692845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1692846 (_26103 : real) : (term379 _26103) = (term380 _26103).
Proof. exact (MK_COMB (@lem1692845) (@lem1692844 _26103)). Qed.
Lemma lem1692848 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1692849 (_26102 : real) (_26103 : real) : (term318 _26102 _26103) = ((real_add _26102 _26103) = term39).
Proof. exact (@lem1692848 ((real_add _26102 _26103) = term39)). Qed.
Lemma lem1692850 (_26102 : real) (_26103 : real) : (term382 _26102 _26103) = (term252 _26102 _26103).
Proof. exact (MK_COMB (@lem1692846 _26103) (@lem1692849 _26102 _26103)). Qed.
Lemma lem1692851 (_26102 : real) (_26103 : real) : (term381 _26102 _26103) = (term252 _26102 _26103).
Proof. exact (TRANS (@lem1692841 _26102 _26103) (@lem1692850 _26102 _26103)). Qed.
Lemma lem1692852 (_26102 : real) (_26103 : real) : (term377 _26102 _26103) = (term257 _26102 _26103).
Proof. exact (MK_COMB (@lem1692838 _26102) (@lem1692851 _26102 _26103)). Qed.
Lemma lem1692853 (_26102 : real) (_26103 : real) : (term376 _26102 _26103) = (term257 _26102 _26103).
Proof. exact (TRANS (@lem1692833 _26102 _26103) (@lem1692852 _26102 _26103)). Qed.
Lemma lem1692854 (_26100 : real) (_26098 : real) (_26102 : real) (_26103 : real) : (term375 _26100 _26098 _26102 _26103) = (term261 _26100 _26098 _26102 _26103).
Proof. exact (MK_COMB (@lem1692830 _26100 _26098) (@lem1692853 _26102 _26103)). Qed.
Lemma lem1692855 (_26100 : real) (_26098 : real) (_26102 : real) (_26103 : real) : (term374 _26100 _26098 _26102 _26103) = (term261 _26100 _26098 _26102 _26103).
Proof. exact (TRANS (@lem1692825 _26100 _26098 _26102 _26103) (@lem1692854 _26100 _26098 _26102 _26103)). Qed.
Lemma lem1692856 (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) (_26102 : real) (_26103 : real) : (term370 _26099 _26101 _26100 _26098 _26102 _26103) = (term267 _26099 _26101 _26100 _26098 _26102 _26103).
Proof. exact (MK_COMB (@lem1692822 _26099 _26101) (@lem1692855 _26100 _26098 _26102 _26103)). Qed.
Lemma lem1692857 (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) (_26102 : real) (_26103 : real) : (term369 _26099 _26101 _26100 _26098 _26102 _26103) = (term267 _26099 _26101 _26100 _26098 _26102 _26103).
Proof. exact (TRANS (@lem1692817 _26099 _26101 _26100 _26098 _26102 _26103) (@lem1692856 _26099 _26101 _26100 _26098 _26102 _26103)). Qed.
Lemma lem1692858 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1692859 (_26099 : real) (_26101 : real) (_26100 : real) (_26098 : real) (_26102 : real) (_26103 : real) : (term383 _26099 _26101 _26100 _26098 _26102 _26103) = (term384 _26099 _26101 _26100 _26098 _26102 _26103).
Proof. exact (MK_COMB (@lem1692858) (@lem1692857 _26099 _26101 _26100 _26098 _26102 _26103)). Qed.
Lemma lem1692860 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term262 _26099 _26100 _26102 _26101 _26103 _26098) = (term262 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (eq_refl (term262 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1692861 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term368 _26099 _26100 _26102 _26101 _26103 _26098) = (term137 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (MK_COMB (@lem1692859 _26099 _26101 _26100 _26098 _26102 _26103) (@lem1692860 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1692862 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) : (term367 _26099 _26101 _26100 _26098 _26102 _26103) = (term137 _26099 _26100 _26102 _26101 _26103 _26098).
Proof. exact (TRANS (@lem1692814 _26099 _26100 _26102 _26101 _26103 _26098) (@lem1692861 _26099 _26100 _26102 _26101 _26103 _26098)). Qed.
Lemma lem1692864 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term252 u v.
Proof. exact (conj (@lem1692254 a u x v y b h1) (@lem1692261 a u x v y b h1)). Qed.
Lemma lem1692865 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term257 u v.
Proof. exact (conj (@lem1692247 a u x v y b h1) (@lem1692864 a u x v y b h1)). Qed.
Lemma lem1692866 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term261 a y u v.
Proof. exact (conj (@lem1692240 a u x v y b h1) (@lem1692865 a u x v y b h1)). Qed.
Lemma lem1692867 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term385 x a y u v.
Proof. exact (conj (@lem1692233 a u x v y b h1) (@lem1692866 a u x v y b h1)). Qed.
Lemma lem1692869 (_26099 : real) (_26100 : real) (_26102 : real) (_26101 : real) (_26103 : real) (_26098 : real) (h1 : term119) : term137 _26099 _26100 _26102 _26101 _26103 _26098.
Proof. exact (EQ_MP (@lem1692862 _26099 _26100 _26102 _26101 _26103 _26098) (@lem1692811 _26099 _26101 _26100 _26098 _26102 _26103 h1)). Qed.
Lemma lem1692870 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) : term386 a u x v y.
Proof. exact (@lem1692869 a a u x v y h1). Qed.
Lemma lem1692873 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term170 a u x v y b) : term387 a u x v y.
Proof. exact (@lem1692870 a u x v y h1 (@lem1692867 a u x v y b h2)). Qed.
Lemma lem1692874 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term170 a u x v y b) : term388 a u x v y.
Proof. exact (fun h0 : term389 a u x v y => @lem1692873 a u x v y b h1 h2). Qed.
Lemma lem1692876 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1692877 (a : real) (u : real) (x : real) (v : real) (y : real) : (term388 a u x v y) = (term387 a u x v y).
Proof. exact (@lem1692876 (term387 a u x v y)). Qed.
Lemma lem1692878 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term170 a u x v y b) : term387 a u x v y.
Proof. exact (EQ_MP (@lem1692877 a u x v y) (@lem1692874 a u x v y b h1 h2)). Qed.
Lemma lem1692896 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692897 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : (term311 _26119 _26120 _26117 _26118) = (term390 _26119 _26120 _26117 _26118).
Proof. exact (@lem1692896 (real_lt _26119 _26120) (term57 _26118 _26120) (term296 _26117 _26118)). Qed.
Lemma lem1692915 (_26117 : real) (_26119 : real) : (term58 _26117 _26119) = (term58 _26117 _26119).
Proof. exact (eq_refl (term58 _26117 _26119)). Qed.
Lemma lem1692916 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : (term313 _26119 _26120 _26117 _26118) = (term391 _26119 _26120 _26117 _26118).
Proof. exact (MK_COMB (@lem1692915 _26117 _26119) (@lem1692897 _26119 _26120 _26117 _26118)). Qed.
Lemma lem1692920 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1692921 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : (term391 _26119 _26120 _26117 _26118) = (term392 _26119 _26120 _26117 _26118).
Proof. exact (@lem1692920 (real_lt _26119 _26120) (term57 _26117 _26119) (term393 _26120 _26117 _26118)). Qed.
Lemma lem1692951 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : (term313 _26119 _26120 _26117 _26118) = (term392 _26119 _26120 _26117 _26118).
Proof. exact (TRANS (@lem1692916 _26119 _26120 _26117 _26118) (@lem1692921 _26119 _26120 _26117 _26118)). Qed.
Lemma lem1692952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1692953 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : (term394 _26119 _26120 _26117 _26118) = (term395 _26119 _26120 _26117 _26118).
Proof. exact (MK_COMB (@lem1692952) (@lem1692951 _26119 _26120 _26117 _26118)). Qed.
Lemma lem1692983 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : (term392 _26119 _26120 _26117 _26118) = (term392 _26119 _26120 _26117 _26118).
Proof. exact (eq_refl (term392 _26119 _26120 _26117 _26118)). Qed.
Lemma lem1692984 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : ((term313 _26119 _26120 _26117 _26118) = (term392 _26119 _26120 _26117 _26118)) = ((term392 _26119 _26120 _26117 _26118) = (term392 _26119 _26120 _26117 _26118)).
Proof. exact (MK_COMB (@lem1692953 _26119 _26120 _26117 _26118) (@lem1692983 _26119 _26120 _26117 _26118)). Qed.
Lemma lem1692986 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1692987 (x : Prop) : (x = x) = True.
Proof. exact (@lem1692986 Prop x). Qed.
Lemma lem1692988 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : ((term392 _26119 _26120 _26117 _26118) = (term392 _26119 _26120 _26117 _26118)) = True.
Proof. exact (@lem1692987 (term392 _26119 _26120 _26117 _26118)). Qed.
Lemma lem1692989 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : ((term313 _26119 _26120 _26117 _26118) = (term392 _26119 _26120 _26117 _26118)) = True.
Proof. exact (TRANS (@lem1692984 _26119 _26120 _26117 _26118) (@lem1692988 _26119 _26120 _26117 _26118)). Qed.
Lemma lem1692990 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : True = ((term313 _26119 _26120 _26117 _26118) = (term392 _26119 _26120 _26117 _26118)).
Proof. exact (SYM (@lem1692989 _26119 _26120 _26117 _26118)). Qed.
Lemma lem1692991 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : (term313 _26119 _26120 _26117 _26118) = (term392 _26119 _26120 _26117 _26118).
Proof. exact (EQ_MP (@lem1692990 _26119 _26120 _26117 _26118) (@lem0)). Qed.
Lemma lem1692992 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : term392 _26119 _26120 _26117 _26118.
Proof. exact (EQ_MP (@lem1692991 _26119 _26120 _26117 _26118) (@lem1692092 _26119 _26120 _26117 _26118)). Qed.
Lemma lem1692994 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1692995 (_26117 : real) (_26118 : real) (_26119 : real) (_26120 : real) : (term392 _26119 _26120 _26117 _26118) = (term396 _26117 _26118 _26119 _26120).
Proof. exact (@lem1692994 (term397 _26119 _26120 _26117 _26118) (real_lt _26119 _26120)). Qed.
Lemma lem1692997 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1692998 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : (term398 _26119 _26120 _26117 _26118) = (term399 _26119 _26120 _26117 _26118).
Proof. exact (@lem1692997 (term57 _26117 _26119) (term393 _26120 _26117 _26118)). Qed.
Lemma lem1693000 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1693001 (_26117 : real) (_26119 : real) : (term72 _26117 _26119) = (_26117 = _26119).
Proof. exact (@lem1693000 (_26117 = _26119)). Qed.
Lemma lem1693002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1693003 (_26117 : real) (_26119 : real) : (term73 _26117 _26119) = (term74 _26117 _26119).
Proof. exact (MK_COMB (@lem1693002) (@lem1693001 _26117 _26119)). Qed.
Lemma lem1693005 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1693006 (_26120 : real) (_26117 : real) (_26118 : real) : (term400 _26120 _26117 _26118) = (term401 _26120 _26117 _26118).
Proof. exact (@lem1693005 (term57 _26118 _26120) (term296 _26117 _26118)). Qed.
Lemma lem1693008 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1693009 (_26118 : real) (_26120 : real) : (term72 _26118 _26120) = (_26118 = _26120).
Proof. exact (@lem1693008 (_26118 = _26120)). Qed.
Lemma lem1693010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1693011 (_26118 : real) (_26120 : real) : (term73 _26118 _26120) = (term74 _26118 _26120).
Proof. exact (MK_COMB (@lem1693010) (@lem1693009 _26118 _26120)). Qed.
Lemma lem1693013 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1693014 (_26117 : real) (_26118 : real) : (term371 _26117 _26118) = (real_lt _26117 _26118).
Proof. exact (@lem1693013 (real_lt _26117 _26118)). Qed.
Lemma lem1693015 (_26120 : real) (_26117 : real) (_26118 : real) : (term401 _26120 _26117 _26118) = (term402 _26120 _26117 _26118).
Proof. exact (MK_COMB (@lem1693011 _26118 _26120) (@lem1693014 _26117 _26118)). Qed.
Lemma lem1693016 (_26120 : real) (_26117 : real) (_26118 : real) : (term400 _26120 _26117 _26118) = (term402 _26120 _26117 _26118).
Proof. exact (TRANS (@lem1693006 _26120 _26117 _26118) (@lem1693015 _26120 _26117 _26118)). Qed.
Lemma lem1693017 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : (term399 _26119 _26120 _26117 _26118) = (term403 _26119 _26120 _26117 _26118).
Proof. exact (MK_COMB (@lem1693003 _26117 _26119) (@lem1693016 _26120 _26117 _26118)). Qed.
Lemma lem1693018 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : (term398 _26119 _26120 _26117 _26118) = (term403 _26119 _26120 _26117 _26118).
Proof. exact (TRANS (@lem1692998 _26119 _26120 _26117 _26118) (@lem1693017 _26119 _26120 _26117 _26118)). Qed.
Lemma lem1693019 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1693020 (_26119 : real) (_26120 : real) (_26117 : real) (_26118 : real) : (term404 _26119 _26120 _26117 _26118) = (term405 _26119 _26120 _26117 _26118).
Proof. exact (MK_COMB (@lem1693019) (@lem1693018 _26119 _26120 _26117 _26118)). Qed.
Lemma lem1693021 (_26119 : real) (_26120 : real) : (real_lt _26119 _26120) = (real_lt _26119 _26120).
Proof. exact (eq_refl (real_lt _26119 _26120)). Qed.
Lemma lem1693022 (_26117 : real) (_26118 : real) (_26119 : real) (_26120 : real) : (term396 _26117 _26118 _26119 _26120) = (term406 _26117 _26118 _26119 _26120).
Proof. exact (MK_COMB (@lem1693020 _26119 _26120 _26117 _26118) (@lem1693021 _26119 _26120)). Qed.
Lemma lem1693023 (_26117 : real) (_26118 : real) (_26119 : real) (_26120 : real) : (term392 _26119 _26120 _26117 _26118) = (term406 _26117 _26118 _26119 _26120).
Proof. exact (TRANS (@lem1692995 _26117 _26118 _26119 _26120) (@lem1693022 _26117 _26118 _26119 _26120)). Qed.
Lemma lem1693025 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term170 a u x v y b) : term407 a u x v y.
Proof. exact (conj (@lem1692226 u x v y) (@lem1692878 a u x v y b h1 h2)). Qed.
Lemma lem1693026 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term408 a u x v y.
Proof. exact (conj (@lem1692218 a u x v y b h2 h3) (@lem1693025 a u x v y b h1 h3)). Qed.
Lemma lem1693028 (_26117 : real) (_26118 : real) (_26119 : real) (_26120 : real) : term406 _26117 _26118 _26119 _26120.
Proof. exact (EQ_MP (@lem1693023 _26117 _26118 _26119 _26120) (@lem1692992 _26119 _26120 _26117 _26118)). Qed.
Lemma lem1693029 (a : real) (u : real) (x : real) (v : real) (y : real) : term409 a u x v y.
Proof. exact (@lem1693028 (term31 u v a) (term321 u x v y) a (term321 u x v y)). Qed.
Lemma lem1693032 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term166 a u x v y.
Proof. exact (@lem1693029 a u x v y (@lem1693026 a u x v y b h1 h2 h3)). Qed.
Lemma lem1693033 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term410 a u x v y.
Proof. exact (fun h0 : term284 a u x v y => @lem1693032 a u x v y b h1 h2 h3). Qed.
Lemma lem1693035 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1693036 (a : real) (u : real) (x : real) (v : real) (y : real) : (term410 a u x v y) = (term166 a u x v y).
Proof. exact (@lem1693035 (term166 a u x v y)). Qed.
Lemma lem1693037 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term166 a u x v y.
Proof. exact (EQ_MP (@lem1693036 a u x v y) (@lem1693033 a u x v y b h1 h2 h3)). Qed.
Lemma lem1693040 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1693042 (a : real) (u : real) (x : real) (v : real) (y : real) : (term284 a u x v y) = (term411 a u x v y).
Proof. exact (@lem1693040 (term166 a u x v y)). Qed.
Lemma lem1693045 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term284 a u x v y) : term411 a u x v y.
Proof. exact (EQ_MP (@lem1693042 a u x v y) (@lem1692002 a u x v y h1)). Qed.
Lemma lem1693048 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : False.
Proof. exact (@lem1693045 a u x v y h3 (@lem1693037 a u x v y b h1 h2 h4)). Qed.
Lemma lem1693049 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : term109.
Proof. exact (fun h0 : ~ False => @lem1693048 a u x v y b h1 h2 h3 h4). Qed.
Lemma lem1693051 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1693052 : term109 = False.
Proof. exact (@lem1693051 False). Qed.
Lemma lem1693053 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1693052) (@lem1693049 a u x v y b h1 h2 h3 h4)). Qed.
Lemma lem1693073 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1693074 (_26139 : real) (_26141 : real) (h1 : _26139 = _26141) : _26139 = _26141.
Proof. exact (h1). Qed.
Lemma lem1693075 (_26140 : real) (_26142 : real) (h1 : _26140 = _26142) : _26140 = _26142.
Proof. exact (h1). Qed.
Lemma lem1693076 (_26139 : real) (_26141 : real) (h1 : _26139 = _26141) : (real_lt _26139) = (real_lt _26141).
Proof. exact (MK_COMB (@lem1693073) (@lem1693074 _26139 _26141 h1)). Qed.
Lemma lem1693077 (_26139 : real) (_26141 : real) (_26140 : real) (_26142 : real) (h1 : _26139 = _26141) (h2 : _26140 = _26142) : (real_lt _26139 _26140) = (real_lt _26141 _26142).
Proof. exact (MK_COMB (@lem1693076 _26139 _26141 h1) (@lem1693075 _26140 _26142 h2)). Qed.
Lemma lem1693079 (b : Prop) (a : Prop) : term307 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1693080 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : term308 _26141 _26142 _26139 _26140.
Proof. exact (@lem1693079 (real_lt _26141 _26142) (real_lt _26139 _26140)). Qed.
Lemma lem1693081 (_26139 : real) (_26141 : real) (_26140 : real) (_26142 : real) (h1 : _26139 = _26141) (h2 : _26140 = _26142) : term309 _26141 _26142 _26139 _26140.
Proof. exact (@lem1693080 _26141 _26142 _26139 _26140 (@lem1693077 _26139 _26141 _26140 _26142 h1 h2)). Qed.
Lemma lem1693082 (_26142 : real) (_26140 : real) (_26139 : real) (_26141 : real) (h1 : _26139 = _26141) : term310 _26141 _26142 _26139 _26140.
Proof. exact (fun h0 : _26140 = _26142 => @lem1693081 _26139 _26141 _26140 _26142 h1 h0). Qed.
Lemma lem1693084 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1693085 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : (term310 _26141 _26142 _26139 _26140) = (term311 _26141 _26142 _26139 _26140).
Proof. exact (@lem1693084 (_26140 = _26142) (term309 _26141 _26142 _26139 _26140)). Qed.
Lemma lem1693086 (_26142 : real) (_26140 : real) (_26139 : real) (_26141 : real) (h1 : _26139 = _26141) : term311 _26141 _26142 _26139 _26140.
Proof. exact (EQ_MP (@lem1693085 _26141 _26142 _26139 _26140) (@lem1693082 _26142 _26140 _26139 _26141 h1)). Qed.
Lemma lem1693087 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : term312 _26141 _26142 _26139 _26140.
Proof. exact (fun h0 : _26139 = _26141 => @lem1693086 _26142 _26140 _26139 _26141 h0). Qed.
Lemma lem1693089 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1693090 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : (term312 _26141 _26142 _26139 _26140) = (term313 _26141 _26142 _26139 _26140).
Proof. exact (@lem1693089 (_26139 = _26141) (term311 _26141 _26142 _26139 _26140)). Qed.
Lemma lem1693091 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : term313 _26141 _26142 _26139 _26140.
Proof. exact (EQ_MP (@lem1693090 _26141 _26142 _26139 _26140) (@lem1693087 _26141 _26142 _26139 _26140)). Qed.
Lemma lem1693151 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1693152 (u : real) (x : real) (v : real) (y : real) : (term321 u x v y) = (term321 u x v y).
Proof. exact (@lem1693151 (term321 u x v y)). Qed.
Lemma lem1693153 (u : real) (x : real) (v : real) (y : real) : term322 u x v y.
Proof. exact (fun h0 : term323 u x v y => @lem1693152 u x v y). Qed.
Lemma lem1693155 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1693156 (u : real) (x : real) (v : real) (y : real) : (term322 u x v y) = ((term321 u x v y) = (term321 u x v y)).
Proof. exact (@lem1693155 ((term321 u x v y) = (term321 u x v y))). Qed.
Lemma lem1693157 (u : real) (x : real) (v : real) (y : real) : (term321 u x v y) = (term321 u x v y).
Proof. exact (EQ_MP (@lem1693156 u x v y) (@lem1693153 u x v y)). Qed.
Lemma lem1693159 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1691635 a u x v y b h1)). Qed.
Lemma lem1693160 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1693159 a u x v y b h1). Qed.
Lemma lem1693162 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1693163 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1693162 ((real_add u v) = term39)). Qed.
Lemma lem1693164 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1693163 u v) (@lem1693160 a u x v y b h1)). Qed.
Lemma lem1693170 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1693171 (_26106 : real) (_26104 : real) (_26105 : real) : (term217 _26104 _26105 _26106) = (term314 _26106 _26104 _26105).
Proof. exact (@lem1693170 ((term31 _26104 _26105 _26106) = _26106) (term52 _26104 _26105)). Qed.
Lemma lem1693181 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1693182 (_26106 : real) (_26104 : real) (_26105 : real) : (term315 _26104 _26105 _26106) = (term316 _26106 _26104 _26105).
Proof. exact (MK_COMB (@lem1693181) (@lem1693171 _26106 _26104 _26105)). Qed.
Lemma lem1693192 (_26106 : real) (_26104 : real) (_26105 : real) : (term314 _26106 _26104 _26105) = (term314 _26106 _26104 _26105).
Proof. exact (eq_refl (term314 _26106 _26104 _26105)). Qed.
Lemma lem1693193 (_26106 : real) (_26104 : real) (_26105 : real) : ((term217 _26104 _26105 _26106) = (term314 _26106 _26104 _26105)) = ((term314 _26106 _26104 _26105) = (term314 _26106 _26104 _26105)).
Proof. exact (MK_COMB (@lem1693182 _26106 _26104 _26105) (@lem1693192 _26106 _26104 _26105)). Qed.
Lemma lem1693195 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1693196 (x : Prop) : (x = x) = True.
Proof. exact (@lem1693195 Prop x). Qed.
Lemma lem1693197 (_26106 : real) (_26104 : real) (_26105 : real) : ((term314 _26106 _26104 _26105) = (term314 _26106 _26104 _26105)) = True.
Proof. exact (@lem1693196 (term314 _26106 _26104 _26105)). Qed.
Lemma lem1693198 (_26106 : real) (_26104 : real) (_26105 : real) : ((term217 _26104 _26105 _26106) = (term314 _26106 _26104 _26105)) = True.
Proof. exact (TRANS (@lem1693193 _26106 _26104 _26105) (@lem1693197 _26106 _26104 _26105)). Qed.
Lemma lem1693199 (_26106 : real) (_26104 : real) (_26105 : real) : True = ((term217 _26104 _26105 _26106) = (term314 _26106 _26104 _26105)).
Proof. exact (SYM (@lem1693198 _26106 _26104 _26105)). Qed.
Lemma lem1693200 (_26106 : real) (_26104 : real) (_26105 : real) : (term217 _26104 _26105 _26106) = (term314 _26106 _26104 _26105).
Proof. exact (EQ_MP (@lem1693199 _26106 _26104 _26105) (@lem0)). Qed.
Lemma lem1693201 (_26106 : real) (_26104 : real) (_26105 : real) (h1 : term122) : term314 _26106 _26104 _26105.
Proof. exact (EQ_MP (@lem1693200 _26106 _26104 _26105) (@lem1692008 _26104 _26105 _26106 h1)). Qed.
Lemma lem1693203 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1693204 (_26104 : real) (_26105 : real) (_26106 : real) : (term314 _26106 _26104 _26105) = (term317 _26104 _26105 _26106).
Proof. exact (@lem1693203 (term52 _26104 _26105) ((term31 _26104 _26105 _26106) = _26106)). Qed.
Lemma lem1693206 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1693207 (_26104 : real) (_26105 : real) : (term318 _26104 _26105) = ((real_add _26104 _26105) = term39).
Proof. exact (@lem1693206 ((real_add _26104 _26105) = term39)). Qed.
Lemma lem1693208 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1693209 (_26104 : real) (_26105 : real) : (term319 _26104 _26105) = (term320 _26104 _26105).
Proof. exact (MK_COMB (@lem1693208) (@lem1693207 _26104 _26105)). Qed.
Lemma lem1693210 (_26104 : real) (_26105 : real) (_26106 : real) : ((term31 _26104 _26105 _26106) = _26106) = ((term31 _26104 _26105 _26106) = _26106).
Proof. exact (eq_refl ((term31 _26104 _26105 _26106) = _26106)). Qed.
Lemma lem1693211 (_26104 : real) (_26105 : real) (_26106 : real) : (term317 _26104 _26105 _26106) = (term1 _26104 _26105 _26106).
Proof. exact (MK_COMB (@lem1693209 _26104 _26105) (@lem1693210 _26104 _26105 _26106)). Qed.
Lemma lem1693212 (_26104 : real) (_26105 : real) (_26106 : real) : (term314 _26106 _26104 _26105) = (term1 _26104 _26105 _26106).
Proof. exact (TRANS (@lem1693204 _26104 _26105 _26106) (@lem1693211 _26104 _26105 _26106)). Qed.
Lemma lem1693215 (_26104 : real) (_26105 : real) (_26106 : real) (h1 : term122) : term1 _26104 _26105 _26106.
Proof. exact (EQ_MP (@lem1693212 _26104 _26105 _26106) (@lem1693201 _26106 _26104 _26105 h1)). Qed.
Lemma lem1693216 (u : real) (v : real) (_26106 : real) (h1 : term122) : term1 u v _26106.
Proof. exact (@lem1693215 u v _26106 h1). Qed.
Lemma lem1693219 (_26106 : real) (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term122) (h2 : term170 a u x v y b) : (term31 u v _26106) = _26106.
Proof. exact (@lem1693216 u v _26106 h1 (@lem1693164 a u x v y b h2)). Qed.
Lemma lem1693220 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term122) (h2 : term170 a u x v y b) : (term31 u v b) = b.
Proof. exact (@lem1693219 b a u x v y b h1 h2). Qed.
Lemma lem1693221 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term122) (h2 : term170 a u x v y b) : term107 u v b.
Proof. exact (fun h0 : term44 u v b => @lem1693220 a u x v y b h1 h2). Qed.
Lemma lem1693223 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1693224 (u : real) (v : real) (b : real) : (term107 u v b) = ((term31 u v b) = b).
Proof. exact (@lem1693223 ((term31 u v b) = b)). Qed.
Lemma lem1693225 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term122) (h2 : term170 a u x v y b) : (term31 u v b) = b.
Proof. exact (EQ_MP (@lem1693224 u v b) (@lem1693221 a u x v y b h1 h2)). Qed.
Lemma lem1693227 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : real_lt x b.
Proof. exact (proj1 (@lem1691627 a u x v y b h1)). Qed.
Lemma lem1693228 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term324 x b.
Proof. exact (fun h0 : term296 x b => @lem1693227 a u x v y b h1). Qed.
Lemma lem1693230 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1693231 (x : real) (b : real) : (term324 x b) = (real_lt x b).
Proof. exact (@lem1693230 (real_lt x b)). Qed.
Lemma lem1693232 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : real_lt x b.
Proof. exact (EQ_MP (@lem1693231 x b) (@lem1693228 a u x v y b h1)). Qed.
Lemma lem1693234 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : real_lt y b.
Proof. exact (proj1 (@lem1691631 a u x v y b h1)). Qed.
Lemma lem1693235 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term324 y b.
Proof. exact (fun h0 : term296 y b => @lem1693234 a u x v y b h1). Qed.
Lemma lem1693237 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1693238 (y : real) (b : real) : (term324 y b) = (real_lt y b).
Proof. exact (@lem1693237 (real_lt y b)). Qed.
Lemma lem1693239 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : real_lt y b.
Proof. exact (EQ_MP (@lem1693238 y b) (@lem1693235 a u x v y b h1)). Qed.
Lemma lem1693241 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term247 u.
Proof. exact (proj1 (@lem1691633 a u x v y b h1)). Qed.
Lemma lem1693242 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term325 u.
Proof. exact (fun h0 : term301 u => @lem1693241 a u x v y b h1). Qed.
Lemma lem1693244 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1693245 (u : real) : (term325 u) = (term247 u).
Proof. exact (@lem1693244 (term247 u)). Qed.
Lemma lem1693246 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term247 u.
Proof. exact (EQ_MP (@lem1693245 u) (@lem1693242 a u x v y b h1)). Qed.
Lemma lem1693248 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term247 v.
Proof. exact (proj1 (@lem1691635 a u x v y b h1)). Qed.
Lemma lem1693249 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term325 v.
Proof. exact (fun h0 : term301 v => @lem1693248 a u x v y b h1). Qed.
Lemma lem1693251 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1693252 (v : real) : (term325 v) = (term247 v).
Proof. exact (@lem1693251 (term247 v)). Qed.
Lemma lem1693253 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term247 v.
Proof. exact (EQ_MP (@lem1693252 v) (@lem1693249 a u x v y b h1)). Qed.
Lemma lem1693255 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1691635 a u x v y b h1)). Qed.
Lemma lem1693256 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1693255 a u x v y b h1). Qed.
Lemma lem1693258 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1693259 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1693258 ((real_add u v) = term39)). Qed.
Lemma lem1693260 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1693259 u v) (@lem1693256 a u x v y b h1)). Qed.
Lemma lem1693276 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693277 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term305 _26108 _26109 _26111 _26110 _26112 _26107) = (term326 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (@lem1693276 (term301 _26111) (term296 _26109 _26107) (term303 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1693291 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693292 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term327 _26108 _26109 _26111 _26110 _26112 _26107) = (term328 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (@lem1693291 (term301 _26112) (term296 _26109 _26107) (term329 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1693306 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693307 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term330 _26108 _26109 _26111 _26110 _26112 _26107) = (term331 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (@lem1693306 (term52 _26111 _26112) (term296 _26109 _26107) (term262 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1693323 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1693324 (_26108 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term332 _26108 _26109 _26111 _26110 _26112 _26107) = (term333 _26108 _26111 _26110 _26112 _26109 _26107).
Proof. exact (@lem1693323 (term262 _26108 _26109 _26111 _26110 _26112 _26107) (term296 _26109 _26107)). Qed.
Lemma lem1693330 (_26111 : real) (_26112 : real) : (term232 _26111 _26112) = (term232 _26111 _26112).
Proof. exact (eq_refl (term232 _26111 _26112)). Qed.
Lemma lem1693331 (_26108 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term331 _26108 _26109 _26111 _26110 _26112 _26107) = (term334 _26108 _26111 _26110 _26112 _26109 _26107).
Proof. exact (MK_COMB (@lem1693330 _26111 _26112) (@lem1693324 _26108 _26111 _26110 _26112 _26109 _26107)). Qed.
Lemma lem1693335 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693336 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term334 _26108 _26111 _26110 _26112 _26109 _26107) = (term335 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (@lem1693335 (term262 _26108 _26109 _26111 _26110 _26112 _26107) (term52 _26111 _26112) (term296 _26109 _26107)). Qed.
Lemma lem1693354 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term331 _26108 _26109 _26111 _26110 _26112 _26107) = (term335 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (TRANS (@lem1693331 _26108 _26111 _26110 _26112 _26109 _26107) (@lem1693336 _26108 _26110 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693355 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term330 _26108 _26109 _26111 _26110 _26112 _26107) = (term335 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (TRANS (@lem1693307 _26108 _26109 _26111 _26110 _26112 _26107) (@lem1693354 _26108 _26110 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693356 (_26112 : real) : (term248 _26112) = (term248 _26112).
Proof. exact (eq_refl (term248 _26112)). Qed.
Lemma lem1693357 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term328 _26108 _26109 _26111 _26110 _26112 _26107) = (term336 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (MK_COMB (@lem1693356 _26112) (@lem1693355 _26108 _26110 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693361 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693362 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term336 _26108 _26110 _26111 _26112 _26109 _26107) = (term337 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (@lem1693361 (term262 _26108 _26109 _26111 _26110 _26112 _26107) (term301 _26112) (term338 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693376 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693377 (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term339 _26111 _26112 _26109 _26107) = (term340 _26111 _26112 _26109 _26107).
Proof. exact (@lem1693376 (term52 _26111 _26112) (term301 _26112) (term296 _26109 _26107)). Qed.
Lemma lem1693395 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term341 _26108 _26109 _26111 _26110 _26112 _26107) = (term341 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (eq_refl (term341 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1693396 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term337 _26108 _26110 _26111 _26112 _26109 _26107) = (term342 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (MK_COMB (@lem1693395 _26108 _26109 _26111 _26110 _26112 _26107) (@lem1693377 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693407 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term336 _26108 _26110 _26111 _26112 _26109 _26107) = (term342 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (TRANS (@lem1693362 _26108 _26110 _26111 _26112 _26109 _26107) (@lem1693396 _26108 _26110 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693408 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term328 _26108 _26109 _26111 _26110 _26112 _26107) = (term342 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (TRANS (@lem1693357 _26108 _26110 _26111 _26112 _26109 _26107) (@lem1693407 _26108 _26110 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693409 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term327 _26108 _26109 _26111 _26110 _26112 _26107) = (term342 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (TRANS (@lem1693292 _26108 _26109 _26111 _26110 _26112 _26107) (@lem1693408 _26108 _26110 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693410 (_26111 : real) : (term248 _26111) = (term248 _26111).
Proof. exact (eq_refl (term248 _26111)). Qed.
Lemma lem1693411 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term326 _26108 _26109 _26111 _26110 _26112 _26107) = (term343 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (MK_COMB (@lem1693410 _26111) (@lem1693409 _26108 _26110 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693415 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693416 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term343 _26108 _26110 _26111 _26112 _26109 _26107) = (term344 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (@lem1693415 (term262 _26108 _26109 _26111 _26110 _26112 _26107) (term301 _26111) (term340 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693430 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693431 (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term345 _26111 _26112 _26109 _26107) = (term346 _26111 _26112 _26109 _26107).
Proof. exact (@lem1693430 (term52 _26111 _26112) (term301 _26111) (term347 _26112 _26109 _26107)). Qed.
Lemma lem1693459 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term341 _26108 _26109 _26111 _26110 _26112 _26107) = (term341 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (eq_refl (term341 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1693460 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term344 _26108 _26110 _26111 _26112 _26109 _26107) = (term348 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (MK_COMB (@lem1693459 _26108 _26109 _26111 _26110 _26112 _26107) (@lem1693431 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693471 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term343 _26108 _26110 _26111 _26112 _26109 _26107) = (term348 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (TRANS (@lem1693416 _26108 _26110 _26111 _26112 _26109 _26107) (@lem1693460 _26108 _26110 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693472 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term326 _26108 _26109 _26111 _26110 _26112 _26107) = (term348 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (TRANS (@lem1693411 _26108 _26110 _26111 _26112 _26109 _26107) (@lem1693471 _26108 _26110 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693473 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term305 _26108 _26109 _26111 _26110 _26112 _26107) = (term348 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (TRANS (@lem1693277 _26108 _26109 _26111 _26110 _26112 _26107) (@lem1693472 _26108 _26110 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693474 (_26108 : real) (_26110 : real) : (term253 _26108 _26110) = (term253 _26108 _26110).
Proof. exact (eq_refl (term253 _26108 _26110)). Qed.
Lemma lem1693475 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term306 _26108 _26109 _26111 _26110 _26112 _26107) = (term349 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (MK_COMB (@lem1693474 _26108 _26110) (@lem1693473 _26108 _26110 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693479 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693480 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term349 _26108 _26110 _26111 _26112 _26109 _26107) = (term350 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (@lem1693479 (term262 _26108 _26109 _26111 _26110 _26112 _26107) (term296 _26108 _26110) (term346 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693494 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693495 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term351 _26108 _26110 _26111 _26112 _26109 _26107) = (term352 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (@lem1693494 (term52 _26111 _26112) (term296 _26108 _26110) (term353 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693511 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693512 (_26111 : real) (_26108 : real) (_26110 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term354 _26108 _26110 _26111 _26112 _26109 _26107) = (term355 _26111 _26108 _26110 _26112 _26109 _26107).
Proof. exact (@lem1693511 (term301 _26111) (term296 _26108 _26110) (term347 _26112 _26109 _26107)). Qed.
Lemma lem1693526 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693527 (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : (term356 _26108 _26110 _26112 _26109 _26107) = (term357 _26112 _26108 _26110 _26109 _26107).
Proof. exact (@lem1693526 (term301 _26112) (term296 _26108 _26110) (term296 _26109 _26107)). Qed.
Lemma lem1693543 (_26111 : real) : (term248 _26111) = (term248 _26111).
Proof. exact (eq_refl (term248 _26111)). Qed.
Lemma lem1693544 (_26111 : real) (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : (term355 _26111 _26108 _26110 _26112 _26109 _26107) = (term358 _26111 _26112 _26108 _26110 _26109 _26107).
Proof. exact (MK_COMB (@lem1693543 _26111) (@lem1693527 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693555 (_26111 : real) (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : (term354 _26108 _26110 _26111 _26112 _26109 _26107) = (term358 _26111 _26112 _26108 _26110 _26109 _26107).
Proof. exact (TRANS (@lem1693512 _26111 _26108 _26110 _26112 _26109 _26107) (@lem1693544 _26111 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693556 (_26111 : real) (_26112 : real) : (term232 _26111 _26112) = (term232 _26111 _26112).
Proof. exact (eq_refl (term232 _26111 _26112)). Qed.
Lemma lem1693557 (_26111 : real) (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : (term352 _26108 _26110 _26111 _26112 _26109 _26107) = (term359 _26111 _26112 _26108 _26110 _26109 _26107).
Proof. exact (MK_COMB (@lem1693556 _26111 _26112) (@lem1693555 _26111 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693568 (_26111 : real) (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : (term351 _26108 _26110 _26111 _26112 _26109 _26107) = (term359 _26111 _26112 _26108 _26110 _26109 _26107).
Proof. exact (TRANS (@lem1693495 _26108 _26110 _26111 _26112 _26109 _26107) (@lem1693557 _26111 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693569 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term341 _26108 _26109 _26111 _26110 _26112 _26107) = (term341 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (eq_refl (term341 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1693570 (_26111 : real) (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : (term350 _26108 _26110 _26111 _26112 _26109 _26107) = (term360 _26111 _26112 _26108 _26110 _26109 _26107).
Proof. exact (MK_COMB (@lem1693569 _26108 _26109 _26111 _26110 _26112 _26107) (@lem1693568 _26111 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693581 (_26111 : real) (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : (term349 _26108 _26110 _26111 _26112 _26109 _26107) = (term360 _26111 _26112 _26108 _26110 _26109 _26107).
Proof. exact (TRANS (@lem1693480 _26108 _26110 _26111 _26112 _26109 _26107) (@lem1693570 _26111 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693582 (_26111 : real) (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : (term306 _26108 _26109 _26111 _26110 _26112 _26107) = (term360 _26111 _26112 _26108 _26110 _26109 _26107).
Proof. exact (TRANS (@lem1693475 _26108 _26110 _26111 _26112 _26109 _26107) (@lem1693581 _26111 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1693584 (_26111 : real) (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : (term361 _26108 _26109 _26111 _26110 _26112 _26107) = (term362 _26111 _26112 _26108 _26110 _26109 _26107).
Proof. exact (MK_COMB (@lem1693583) (@lem1693582 _26111 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693608 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693609 (_26109 : real) (_26107 : real) (_26111 : real) (_26112 : real) : (term255 _26109 _26107 _26111 _26112) = (term363 _26109 _26107 _26111 _26112).
Proof. exact (@lem1693608 (term301 _26111) (term296 _26109 _26107) (term246 _26111 _26112)). Qed.
Lemma lem1693623 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693624 (_26109 : real) (_26107 : real) (_26111 : real) (_26112 : real) : (term364 _26109 _26107 _26111 _26112) = (term365 _26109 _26107 _26111 _26112).
Proof. exact (@lem1693623 (term301 _26112) (term296 _26109 _26107) (term52 _26111 _26112)). Qed.
Lemma lem1693638 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1693639 (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term366 _26109 _26107 _26111 _26112) = (term338 _26111 _26112 _26109 _26107).
Proof. exact (@lem1693638 (term52 _26111 _26112) (term296 _26109 _26107)). Qed.
Lemma lem1693647 (_26112 : real) : (term248 _26112) = (term248 _26112).
Proof. exact (eq_refl (term248 _26112)). Qed.
Lemma lem1693648 (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term365 _26109 _26107 _26111 _26112) = (term339 _26111 _26112 _26109 _26107).
Proof. exact (MK_COMB (@lem1693647 _26112) (@lem1693639 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693652 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693653 (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term339 _26111 _26112 _26109 _26107) = (term340 _26111 _26112 _26109 _26107).
Proof. exact (@lem1693652 (term52 _26111 _26112) (term301 _26112) (term296 _26109 _26107)). Qed.
Lemma lem1693671 (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term365 _26109 _26107 _26111 _26112) = (term340 _26111 _26112 _26109 _26107).
Proof. exact (TRANS (@lem1693648 _26111 _26112 _26109 _26107) (@lem1693653 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693672 (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term364 _26109 _26107 _26111 _26112) = (term340 _26111 _26112 _26109 _26107).
Proof. exact (TRANS (@lem1693624 _26109 _26107 _26111 _26112) (@lem1693671 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693673 (_26111 : real) : (term248 _26111) = (term248 _26111).
Proof. exact (eq_refl (term248 _26111)). Qed.
Lemma lem1693674 (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term363 _26109 _26107 _26111 _26112) = (term345 _26111 _26112 _26109 _26107).
Proof. exact (MK_COMB (@lem1693673 _26111) (@lem1693672 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693678 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693679 (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term345 _26111 _26112 _26109 _26107) = (term346 _26111 _26112 _26109 _26107).
Proof. exact (@lem1693678 (term52 _26111 _26112) (term301 _26111) (term347 _26112 _26109 _26107)). Qed.
Lemma lem1693707 (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term363 _26109 _26107 _26111 _26112) = (term346 _26111 _26112 _26109 _26107).
Proof. exact (TRANS (@lem1693674 _26111 _26112 _26109 _26107) (@lem1693679 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693708 (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term255 _26109 _26107 _26111 _26112) = (term346 _26111 _26112 _26109 _26107).
Proof. exact (TRANS (@lem1693609 _26109 _26107 _26111 _26112) (@lem1693707 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693709 (_26108 : real) (_26110 : real) : (term253 _26108 _26110) = (term253 _26108 _26110).
Proof. exact (eq_refl (term253 _26108 _26110)). Qed.
Lemma lem1693710 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term259 _26108 _26110 _26109 _26107 _26111 _26112) = (term351 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (MK_COMB (@lem1693709 _26108 _26110) (@lem1693708 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693714 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693715 (_26108 : real) (_26110 : real) (_26111 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term351 _26108 _26110 _26111 _26112 _26109 _26107) = (term352 _26108 _26110 _26111 _26112 _26109 _26107).
Proof. exact (@lem1693714 (term52 _26111 _26112) (term296 _26108 _26110) (term353 _26111 _26112 _26109 _26107)). Qed.
Lemma lem1693731 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693732 (_26111 : real) (_26108 : real) (_26110 : real) (_26112 : real) (_26109 : real) (_26107 : real) : (term354 _26108 _26110 _26111 _26112 _26109 _26107) = (term355 _26111 _26108 _26110 _26112 _26109 _26107).
Proof. exact (@lem1693731 (term301 _26111) (term296 _26108 _26110) (term347 _26112 _26109 _26107)). Qed.
Lemma lem1693746 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693747 (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : (term356 _26108 _26110 _26112 _26109 _26107) = (term357 _26112 _26108 _26110 _26109 _26107).
Proof. exact (@lem1693746 (term301 _26112) (term296 _26108 _26110) (term296 _26109 _26107)). Qed.
Lemma lem1693763 (_26111 : real) : (term248 _26111) = (term248 _26111).
Proof. exact (eq_refl (term248 _26111)). Qed.
Lemma lem1693764 (_26111 : real) (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : (term355 _26111 _26108 _26110 _26112 _26109 _26107) = (term358 _26111 _26112 _26108 _26110 _26109 _26107).
Proof. exact (MK_COMB (@lem1693763 _26111) (@lem1693747 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693775 (_26111 : real) (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : (term354 _26108 _26110 _26111 _26112 _26109 _26107) = (term358 _26111 _26112 _26108 _26110 _26109 _26107).
Proof. exact (TRANS (@lem1693732 _26111 _26108 _26110 _26112 _26109 _26107) (@lem1693764 _26111 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693776 (_26111 : real) (_26112 : real) : (term232 _26111 _26112) = (term232 _26111 _26112).
Proof. exact (eq_refl (term232 _26111 _26112)). Qed.
Lemma lem1693777 (_26111 : real) (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : (term352 _26108 _26110 _26111 _26112 _26109 _26107) = (term359 _26111 _26112 _26108 _26110 _26109 _26107).
Proof. exact (MK_COMB (@lem1693776 _26111 _26112) (@lem1693775 _26111 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693788 (_26111 : real) (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : (term351 _26108 _26110 _26111 _26112 _26109 _26107) = (term359 _26111 _26112 _26108 _26110 _26109 _26107).
Proof. exact (TRANS (@lem1693715 _26108 _26110 _26111 _26112 _26109 _26107) (@lem1693777 _26111 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693789 (_26111 : real) (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : (term259 _26108 _26110 _26109 _26107 _26111 _26112) = (term359 _26111 _26112 _26108 _26110 _26109 _26107).
Proof. exact (TRANS (@lem1693710 _26108 _26110 _26111 _26112 _26109 _26107) (@lem1693788 _26111 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693790 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term341 _26108 _26109 _26111 _26110 _26112 _26107) = (term341 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (eq_refl (term341 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1693791 (_26111 : real) (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : (term367 _26108 _26110 _26109 _26107 _26111 _26112) = (term360 _26111 _26112 _26108 _26110 _26109 _26107).
Proof. exact (MK_COMB (@lem1693790 _26108 _26109 _26111 _26110 _26112 _26107) (@lem1693789 _26111 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693802 (_26111 : real) (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : ((term306 _26108 _26109 _26111 _26110 _26112 _26107) = (term367 _26108 _26110 _26109 _26107 _26111 _26112)) = ((term360 _26111 _26112 _26108 _26110 _26109 _26107) = (term360 _26111 _26112 _26108 _26110 _26109 _26107)).
Proof. exact (MK_COMB (@lem1693584 _26111 _26112 _26108 _26110 _26109 _26107) (@lem1693791 _26111 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693804 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1693805 (x : Prop) : (x = x) = True.
Proof. exact (@lem1693804 Prop x). Qed.
Lemma lem1693806 (_26111 : real) (_26112 : real) (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) : ((term360 _26111 _26112 _26108 _26110 _26109 _26107) = (term360 _26111 _26112 _26108 _26110 _26109 _26107)) = True.
Proof. exact (@lem1693805 (term360 _26111 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693807 (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) (_26111 : real) (_26112 : real) : ((term306 _26108 _26109 _26111 _26110 _26112 _26107) = (term367 _26108 _26110 _26109 _26107 _26111 _26112)) = True.
Proof. exact (TRANS (@lem1693802 _26111 _26112 _26108 _26110 _26109 _26107) (@lem1693806 _26111 _26112 _26108 _26110 _26109 _26107)). Qed.
Lemma lem1693808 (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) (_26111 : real) (_26112 : real) : True = ((term306 _26108 _26109 _26111 _26110 _26112 _26107) = (term367 _26108 _26110 _26109 _26107 _26111 _26112)).
Proof. exact (SYM (@lem1693807 _26108 _26110 _26109 _26107 _26111 _26112)). Qed.
Lemma lem1693809 (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) (_26111 : real) (_26112 : real) : (term306 _26108 _26109 _26111 _26110 _26112 _26107) = (term367 _26108 _26110 _26109 _26107 _26111 _26112).
Proof. exact (EQ_MP (@lem1693808 _26108 _26110 _26109 _26107 _26111 _26112) (@lem0)). Qed.
Lemma lem1693810 (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) (_26111 : real) (_26112 : real) (h1 : term119) : term367 _26108 _26110 _26109 _26107 _26111 _26112.
Proof. exact (EQ_MP (@lem1693809 _26108 _26110 _26109 _26107 _26111 _26112) (@lem1692038 _26108 _26109 _26111 _26110 _26112 _26107 h1)). Qed.
Lemma lem1693812 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1693813 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term367 _26108 _26110 _26109 _26107 _26111 _26112) = (term368 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (@lem1693812 (term259 _26108 _26110 _26109 _26107 _26111 _26112) (term262 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1693815 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1693816 (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) (_26111 : real) (_26112 : real) : (term369 _26108 _26110 _26109 _26107 _26111 _26112) = (term370 _26108 _26110 _26109 _26107 _26111 _26112).
Proof. exact (@lem1693815 (term296 _26108 _26110) (term255 _26109 _26107 _26111 _26112)). Qed.
Lemma lem1693818 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1693819 (_26108 : real) (_26110 : real) : (term371 _26108 _26110) = (real_lt _26108 _26110).
Proof. exact (@lem1693818 (real_lt _26108 _26110)). Qed.
Lemma lem1693820 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1693821 (_26108 : real) (_26110 : real) : (term372 _26108 _26110) = (term373 _26108 _26110).
Proof. exact (MK_COMB (@lem1693820) (@lem1693819 _26108 _26110)). Qed.
Lemma lem1693823 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1693824 (_26109 : real) (_26107 : real) (_26111 : real) (_26112 : real) : (term374 _26109 _26107 _26111 _26112) = (term375 _26109 _26107 _26111 _26112).
Proof. exact (@lem1693823 (term296 _26109 _26107) (term250 _26111 _26112)). Qed.
Lemma lem1693826 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1693827 (_26109 : real) (_26107 : real) : (term371 _26109 _26107) = (real_lt _26109 _26107).
Proof. exact (@lem1693826 (real_lt _26109 _26107)). Qed.
Lemma lem1693828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1693829 (_26109 : real) (_26107 : real) : (term372 _26109 _26107) = (term373 _26109 _26107).
Proof. exact (MK_COMB (@lem1693828) (@lem1693827 _26109 _26107)). Qed.
Lemma lem1693831 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1693832 (_26111 : real) (_26112 : real) : (term376 _26111 _26112) = (term377 _26111 _26112).
Proof. exact (@lem1693831 (term301 _26111) (term246 _26111 _26112)). Qed.
Lemma lem1693834 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1693835 (_26111 : real) : (term378 _26111) = (term247 _26111).
Proof. exact (@lem1693834 (term247 _26111)). Qed.
Lemma lem1693836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1693837 (_26111 : real) : (term379 _26111) = (term380 _26111).
Proof. exact (MK_COMB (@lem1693836) (@lem1693835 _26111)). Qed.
Lemma lem1693839 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1693840 (_26111 : real) (_26112 : real) : (term381 _26111 _26112) = (term382 _26111 _26112).
Proof. exact (@lem1693839 (term301 _26112) (term52 _26111 _26112)). Qed.
Lemma lem1693842 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1693843 (_26112 : real) : (term378 _26112) = (term247 _26112).
Proof. exact (@lem1693842 (term247 _26112)). Qed.
Lemma lem1693844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1693845 (_26112 : real) : (term379 _26112) = (term380 _26112).
Proof. exact (MK_COMB (@lem1693844) (@lem1693843 _26112)). Qed.
Lemma lem1693847 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1693848 (_26111 : real) (_26112 : real) : (term318 _26111 _26112) = ((real_add _26111 _26112) = term39).
Proof. exact (@lem1693847 ((real_add _26111 _26112) = term39)). Qed.
Lemma lem1693849 (_26111 : real) (_26112 : real) : (term382 _26111 _26112) = (term252 _26111 _26112).
Proof. exact (MK_COMB (@lem1693845 _26112) (@lem1693848 _26111 _26112)). Qed.
Lemma lem1693850 (_26111 : real) (_26112 : real) : (term381 _26111 _26112) = (term252 _26111 _26112).
Proof. exact (TRANS (@lem1693840 _26111 _26112) (@lem1693849 _26111 _26112)). Qed.
Lemma lem1693851 (_26111 : real) (_26112 : real) : (term377 _26111 _26112) = (term257 _26111 _26112).
Proof. exact (MK_COMB (@lem1693837 _26111) (@lem1693850 _26111 _26112)). Qed.
Lemma lem1693852 (_26111 : real) (_26112 : real) : (term376 _26111 _26112) = (term257 _26111 _26112).
Proof. exact (TRANS (@lem1693832 _26111 _26112) (@lem1693851 _26111 _26112)). Qed.
Lemma lem1693853 (_26109 : real) (_26107 : real) (_26111 : real) (_26112 : real) : (term375 _26109 _26107 _26111 _26112) = (term261 _26109 _26107 _26111 _26112).
Proof. exact (MK_COMB (@lem1693829 _26109 _26107) (@lem1693852 _26111 _26112)). Qed.
Lemma lem1693854 (_26109 : real) (_26107 : real) (_26111 : real) (_26112 : real) : (term374 _26109 _26107 _26111 _26112) = (term261 _26109 _26107 _26111 _26112).
Proof. exact (TRANS (@lem1693824 _26109 _26107 _26111 _26112) (@lem1693853 _26109 _26107 _26111 _26112)). Qed.
Lemma lem1693855 (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) (_26111 : real) (_26112 : real) : (term370 _26108 _26110 _26109 _26107 _26111 _26112) = (term267 _26108 _26110 _26109 _26107 _26111 _26112).
Proof. exact (MK_COMB (@lem1693821 _26108 _26110) (@lem1693854 _26109 _26107 _26111 _26112)). Qed.
Lemma lem1693856 (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) (_26111 : real) (_26112 : real) : (term369 _26108 _26110 _26109 _26107 _26111 _26112) = (term267 _26108 _26110 _26109 _26107 _26111 _26112).
Proof. exact (TRANS (@lem1693816 _26108 _26110 _26109 _26107 _26111 _26112) (@lem1693855 _26108 _26110 _26109 _26107 _26111 _26112)). Qed.
Lemma lem1693857 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1693858 (_26108 : real) (_26110 : real) (_26109 : real) (_26107 : real) (_26111 : real) (_26112 : real) : (term383 _26108 _26110 _26109 _26107 _26111 _26112) = (term384 _26108 _26110 _26109 _26107 _26111 _26112).
Proof. exact (MK_COMB (@lem1693857) (@lem1693856 _26108 _26110 _26109 _26107 _26111 _26112)). Qed.
Lemma lem1693859 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term262 _26108 _26109 _26111 _26110 _26112 _26107) = (term262 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (eq_refl (term262 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1693860 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term368 _26108 _26109 _26111 _26110 _26112 _26107) = (term137 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (MK_COMB (@lem1693858 _26108 _26110 _26109 _26107 _26111 _26112) (@lem1693859 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1693861 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) : (term367 _26108 _26110 _26109 _26107 _26111 _26112) = (term137 _26108 _26109 _26111 _26110 _26112 _26107).
Proof. exact (TRANS (@lem1693813 _26108 _26109 _26111 _26110 _26112 _26107) (@lem1693860 _26108 _26109 _26111 _26110 _26112 _26107)). Qed.
Lemma lem1693863 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term252 u v.
Proof. exact (conj (@lem1693253 a u x v y b h1) (@lem1693260 a u x v y b h1)). Qed.
Lemma lem1693864 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term257 u v.
Proof. exact (conj (@lem1693246 a u x v y b h1) (@lem1693863 a u x v y b h1)). Qed.
Lemma lem1693865 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term261 y b u v.
Proof. exact (conj (@lem1693239 a u x v y b h1) (@lem1693864 a u x v y b h1)). Qed.
Lemma lem1693866 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term170 a u x v y b) : term412 x y b u v.
Proof. exact (conj (@lem1693232 a u x v y b h1) (@lem1693865 a u x v y b h1)). Qed.
Lemma lem1693868 (_26108 : real) (_26109 : real) (_26111 : real) (_26110 : real) (_26112 : real) (_26107 : real) (h1 : term119) : term137 _26108 _26109 _26111 _26110 _26112 _26107.
Proof. exact (EQ_MP (@lem1693861 _26108 _26109 _26111 _26110 _26112 _26107) (@lem1693810 _26108 _26110 _26109 _26107 _26111 _26112 h1)). Qed.
Lemma lem1693869 (x : real) (y : real) (u : real) (v : real) (b : real) (h1 : term119) : term413 x y u v b.
Proof. exact (@lem1693868 x y u b v b h1). Qed.
Lemma lem1693872 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term170 a u x v y b) : term414 x y u v b.
Proof. exact (@lem1693869 x y u v b h1 (@lem1693866 a u x v y b h2)). Qed.
Lemma lem1693873 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term170 a u x v y b) : term415 x y u v b.
Proof. exact (fun h0 : term416 x y u v b => @lem1693872 a u x v y b h1 h2). Qed.
Lemma lem1693875 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1693876 (x : real) (y : real) (u : real) (v : real) (b : real) : (term415 x y u v b) = (term414 x y u v b).
Proof. exact (@lem1693875 (term414 x y u v b)). Qed.
Lemma lem1693877 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term170 a u x v y b) : term414 x y u v b.
Proof. exact (EQ_MP (@lem1693876 x y u v b) (@lem1693873 a u x v y b h1 h2)). Qed.
Lemma lem1693895 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693896 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : (term311 _26141 _26142 _26139 _26140) = (term390 _26141 _26142 _26139 _26140).
Proof. exact (@lem1693895 (real_lt _26141 _26142) (term57 _26140 _26142) (term296 _26139 _26140)). Qed.
Lemma lem1693914 (_26139 : real) (_26141 : real) : (term58 _26139 _26141) = (term58 _26139 _26141).
Proof. exact (eq_refl (term58 _26139 _26141)). Qed.
Lemma lem1693915 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : (term313 _26141 _26142 _26139 _26140) = (term391 _26141 _26142 _26139 _26140).
Proof. exact (MK_COMB (@lem1693914 _26139 _26141) (@lem1693896 _26141 _26142 _26139 _26140)). Qed.
Lemma lem1693919 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1693920 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : (term391 _26141 _26142 _26139 _26140) = (term392 _26141 _26142 _26139 _26140).
Proof. exact (@lem1693919 (real_lt _26141 _26142) (term57 _26139 _26141) (term393 _26142 _26139 _26140)). Qed.
Lemma lem1693950 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : (term313 _26141 _26142 _26139 _26140) = (term392 _26141 _26142 _26139 _26140).
Proof. exact (TRANS (@lem1693915 _26141 _26142 _26139 _26140) (@lem1693920 _26141 _26142 _26139 _26140)). Qed.
Lemma lem1693951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1693952 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : (term394 _26141 _26142 _26139 _26140) = (term395 _26141 _26142 _26139 _26140).
Proof. exact (MK_COMB (@lem1693951) (@lem1693950 _26141 _26142 _26139 _26140)). Qed.
Lemma lem1693982 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : (term392 _26141 _26142 _26139 _26140) = (term392 _26141 _26142 _26139 _26140).
Proof. exact (eq_refl (term392 _26141 _26142 _26139 _26140)). Qed.
Lemma lem1693983 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : ((term313 _26141 _26142 _26139 _26140) = (term392 _26141 _26142 _26139 _26140)) = ((term392 _26141 _26142 _26139 _26140) = (term392 _26141 _26142 _26139 _26140)).
Proof. exact (MK_COMB (@lem1693952 _26141 _26142 _26139 _26140) (@lem1693982 _26141 _26142 _26139 _26140)). Qed.
Lemma lem1693985 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1693986 (x : Prop) : (x = x) = True.
Proof. exact (@lem1693985 Prop x). Qed.
Lemma lem1693987 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : ((term392 _26141 _26142 _26139 _26140) = (term392 _26141 _26142 _26139 _26140)) = True.
Proof. exact (@lem1693986 (term392 _26141 _26142 _26139 _26140)). Qed.
Lemma lem1693988 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : ((term313 _26141 _26142 _26139 _26140) = (term392 _26141 _26142 _26139 _26140)) = True.
Proof. exact (TRANS (@lem1693983 _26141 _26142 _26139 _26140) (@lem1693987 _26141 _26142 _26139 _26140)). Qed.
Lemma lem1693989 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : True = ((term313 _26141 _26142 _26139 _26140) = (term392 _26141 _26142 _26139 _26140)).
Proof. exact (SYM (@lem1693988 _26141 _26142 _26139 _26140)). Qed.
Lemma lem1693990 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : (term313 _26141 _26142 _26139 _26140) = (term392 _26141 _26142 _26139 _26140).
Proof. exact (EQ_MP (@lem1693989 _26141 _26142 _26139 _26140) (@lem0)). Qed.
Lemma lem1693991 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : term392 _26141 _26142 _26139 _26140.
Proof. exact (EQ_MP (@lem1693990 _26141 _26142 _26139 _26140) (@lem1693091 _26141 _26142 _26139 _26140)). Qed.
Lemma lem1693993 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1693994 (_26139 : real) (_26140 : real) (_26141 : real) (_26142 : real) : (term392 _26141 _26142 _26139 _26140) = (term396 _26139 _26140 _26141 _26142).
Proof. exact (@lem1693993 (term397 _26141 _26142 _26139 _26140) (real_lt _26141 _26142)). Qed.
Lemma lem1693996 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1693997 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : (term398 _26141 _26142 _26139 _26140) = (term399 _26141 _26142 _26139 _26140).
Proof. exact (@lem1693996 (term57 _26139 _26141) (term393 _26142 _26139 _26140)). Qed.
Lemma lem1693999 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1694000 (_26139 : real) (_26141 : real) : (term72 _26139 _26141) = (_26139 = _26141).
Proof. exact (@lem1693999 (_26139 = _26141)). Qed.
Lemma lem1694001 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1694002 (_26139 : real) (_26141 : real) : (term73 _26139 _26141) = (term74 _26139 _26141).
Proof. exact (MK_COMB (@lem1694001) (@lem1694000 _26139 _26141)). Qed.
Lemma lem1694004 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1694005 (_26142 : real) (_26139 : real) (_26140 : real) : (term400 _26142 _26139 _26140) = (term401 _26142 _26139 _26140).
Proof. exact (@lem1694004 (term57 _26140 _26142) (term296 _26139 _26140)). Qed.
Lemma lem1694007 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1694008 (_26140 : real) (_26142 : real) : (term72 _26140 _26142) = (_26140 = _26142).
Proof. exact (@lem1694007 (_26140 = _26142)). Qed.
Lemma lem1694009 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1694010 (_26140 : real) (_26142 : real) : (term73 _26140 _26142) = (term74 _26140 _26142).
Proof. exact (MK_COMB (@lem1694009) (@lem1694008 _26140 _26142)). Qed.
Lemma lem1694012 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1694013 (_26139 : real) (_26140 : real) : (term371 _26139 _26140) = (real_lt _26139 _26140).
Proof. exact (@lem1694012 (real_lt _26139 _26140)). Qed.
Lemma lem1694014 (_26142 : real) (_26139 : real) (_26140 : real) : (term401 _26142 _26139 _26140) = (term402 _26142 _26139 _26140).
Proof. exact (MK_COMB (@lem1694010 _26140 _26142) (@lem1694013 _26139 _26140)). Qed.
Lemma lem1694015 (_26142 : real) (_26139 : real) (_26140 : real) : (term400 _26142 _26139 _26140) = (term402 _26142 _26139 _26140).
Proof. exact (TRANS (@lem1694005 _26142 _26139 _26140) (@lem1694014 _26142 _26139 _26140)). Qed.
Lemma lem1694016 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : (term399 _26141 _26142 _26139 _26140) = (term403 _26141 _26142 _26139 _26140).
Proof. exact (MK_COMB (@lem1694002 _26139 _26141) (@lem1694015 _26142 _26139 _26140)). Qed.
Lemma lem1694017 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : (term398 _26141 _26142 _26139 _26140) = (term403 _26141 _26142 _26139 _26140).
Proof. exact (TRANS (@lem1693997 _26141 _26142 _26139 _26140) (@lem1694016 _26141 _26142 _26139 _26140)). Qed.
Lemma lem1694018 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1694019 (_26141 : real) (_26142 : real) (_26139 : real) (_26140 : real) : (term404 _26141 _26142 _26139 _26140) = (term405 _26141 _26142 _26139 _26140).
Proof. exact (MK_COMB (@lem1694018) (@lem1694017 _26141 _26142 _26139 _26140)). Qed.
Lemma lem1694020 (_26141 : real) (_26142 : real) : (real_lt _26141 _26142) = (real_lt _26141 _26142).
Proof. exact (eq_refl (real_lt _26141 _26142)). Qed.
Lemma lem1694021 (_26139 : real) (_26140 : real) (_26141 : real) (_26142 : real) : (term396 _26139 _26140 _26141 _26142) = (term406 _26139 _26140 _26141 _26142).
Proof. exact (MK_COMB (@lem1694019 _26141 _26142 _26139 _26140) (@lem1694020 _26141 _26142)). Qed.
Lemma lem1694022 (_26139 : real) (_26140 : real) (_26141 : real) (_26142 : real) : (term392 _26141 _26142 _26139 _26140) = (term406 _26139 _26140 _26141 _26142).
Proof. exact (TRANS (@lem1693994 _26139 _26140 _26141 _26142) (@lem1694021 _26139 _26140 _26141 _26142)). Qed.
Lemma lem1694024 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term417 x y u v b.
Proof. exact (conj (@lem1693225 a u x v y b h2 h3) (@lem1693877 a u x v y b h1 h3)). Qed.
Lemma lem1694025 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term418 x y u v b.
Proof. exact (conj (@lem1693157 u x v y) (@lem1694024 a u x v y b h1 h2 h3)). Qed.
Lemma lem1694027 (_26139 : real) (_26140 : real) (_26141 : real) (_26142 : real) : term406 _26139 _26140 _26141 _26142.
Proof. exact (EQ_MP (@lem1694022 _26139 _26140 _26141 _26142) (@lem1693991 _26141 _26142 _26139 _26140)). Qed.
Lemma lem1694028 (u : real) (x : real) (v : real) (y : real) (b : real) : term419 u x v y b.
Proof. exact (@lem1694027 (term321 u x v y) (term31 u v b) (term321 u x v y) b). Qed.
Lemma lem1694031 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term167 u x v y b.
Proof. exact (@lem1694028 u x v y b (@lem1694025 a u x v y b h1 h2 h3)). Qed.
Lemma lem1694032 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term420 u x v y b.
Proof. exact (fun h0 : term285 u x v y b => @lem1694031 a u x v y b h1 h2 h3). Qed.
Lemma lem1694034 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1694035 (u : real) (x : real) (v : real) (y : real) (b : real) : (term420 u x v y b) = (term167 u x v y b).
Proof. exact (@lem1694034 (term167 u x v y b)). Qed.
Lemma lem1694036 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : term167 u x v y b.
Proof. exact (EQ_MP (@lem1694035 u x v y b) (@lem1694032 a u x v y b h1 h2 h3)). Qed.
Lemma lem1694039 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1694041 (u : real) (x : real) (v : real) (y : real) (b : real) : (term285 u x v y b) = (term421 u x v y b).
Proof. exact (@lem1694039 (term167 u x v y b)). Qed.
Lemma lem1694044 (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term285 u x v y b) : term421 u x v y b.
Proof. exact (EQ_MP (@lem1694041 u x v y b) (@lem1692054 u x v y b h1)). Qed.
Lemma lem1694047 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : False.
Proof. exact (@lem1694044 u x v y b h3 (@lem1694036 a u x v y b h1 h2 h4)). Qed.
Lemma lem1694048 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : term109.
Proof. exact (fun h0 : ~ False => @lem1694047 a u x v y b h1 h2 h3 h4). Qed.
Lemma lem1694050 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1694051 : term109 = False.
Proof. exact (@lem1694050 False). Qed.
Lemma lem1694052 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1694051) (@lem1694048 a u x v y b h1 h2 h3 h4)). Qed.
Lemma lem1694053 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : (term285 u x v y b) = False.
Proof. exact (prop_ext (fun h5 : term285 u x v y b => @lem1694052 a u x v y b h1 h2 h3 h4) (fun h5 : False => @lem1692054 u x v y b h3)). Qed.
Lemma lem1694054 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1694053 a u x v y b h1 h2 h3 h4) (@lem1692054 u x v y b h3)). Qed.
Lemma lem1694055 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : (term284 a u x v y) = False.
Proof. exact (prop_ext (fun h5 : term284 a u x v y => @lem1693053 a u x v y b h1 h2 h3 h4) (fun h5 : False => @lem1692002 a u x v y h3)). Qed.
Lemma lem1694056 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1694055 a u x v y b h1 h2 h3 h4) (@lem1692002 a u x v y h3)). Qed.
Lemma lem1694057 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : (term285 u x v y b) = False.
Proof. exact (prop_ext (fun h5 : term285 u x v y b => @lem1694054 a u x v y b h1 h2 h3 h4) (fun h5 : False => @lem1691896 u x v y b h3)). Qed.
Lemma lem1694058 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1694057 a u x v y b h1 h2 h3 h4) (@lem1691896 u x v y b h3)). Qed.
Lemma lem1694059 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : (term284 a u x v y) = False.
Proof. exact (prop_ext (fun h5 : term284 a u x v y => @lem1694056 a u x v y b h1 h2 h3 h4) (fun h5 : False => @lem1691768 a u x v y h3)). Qed.
Lemma lem1694060 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1694059 a u x v y b h1 h2 h3 h4) (@lem1691768 a u x v y h3)). Qed.
Lemma lem1694061 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : (term285 u x v y b) = False.
Proof. exact (prop_ext (fun h5 : term285 u x v y b => @lem1694058 a u x v y b h1 h2 h3 h4) (fun h5 : False => @lem1691896 u x v y b h3)). Qed.
Lemma lem1694062 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term285 u x v y b) (h4 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1694061 a u x v y b h1 h2 h3 h4) (@lem1691896 u x v y b h3)). Qed.
Lemma lem1694063 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : (term284 a u x v y) = False.
Proof. exact (prop_ext (fun h5 : term284 a u x v y => @lem1694060 a u x v y b h1 h2 h3 h4) (fun h5 : False => @lem1691768 a u x v y h3)). Qed.
Lemma lem1694064 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term284 a u x v y) (h4 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1694063 a u x v y b h1 h2 h3 h4) (@lem1691768 a u x v y h3)). Qed.
Lemma lem1694065 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : False.
Proof. exact (or_elim (@lem1691625 a u x v y b h3) (fun h0 : term284 a u x v y => @lem1694064 a u x v y b h1 h2 h0 h3) (fun h0 : term285 u x v y b => @lem1694062 a u x v y b h1 h2 h0 h3)). Qed.
Lemma lem1694066 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : (term170 a u x v y b) = False.
Proof. exact (prop_ext (fun h4 : term170 a u x v y b => @lem1694065 a u x v y b h1 h2 h3) (fun h4 : False => @lem1691624 a u x v y b h3)). Qed.
Lemma lem1694067 (a : real) (u : real) (x : real) (v : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term170 a u x v y b) : False.
Proof. exact (EQ_MP (@lem1694066 a u x v y b h1 h2 h3) (@lem1691624 a u x v y b h3)). Qed.
Lemma lem1694068 (a : real) (u : real) (x : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term182 a u x y b) : False.
Proof. exact (ex_elim (@lem1691344 a u x y b h3) (fun v : real => fun h0 : term181 a u x y b v => @lem1694067 a u x v y b h1 h2 h0)). Qed.
Lemma lem1694069 (a : real) (x : real) (y : real) (b : real) (h1 : term119) (h2 : term122) (h3 : term189 a x y b) : False.
Proof. exact (ex_elim (@lem1691343 a x y b h3) (fun u : real => fun h0 : term188 a x y b u => @lem1694068 a u x y b h1 h2 h0)). Qed.
Lemma lem1694070 (a : real) (x : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term196 a x y) : False.
Proof. exact (ex_elim (@lem1691342 a x y h3) (fun b : real => fun h0 : term195 a x y b => @lem1694069 a x y b h1 h2 h0)). Qed.
Lemma lem1694071 (x : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term203 x y) : False.
Proof. exact (ex_elim (@lem1691341 x y h3) (fun a : real => fun h0 : term202 x y a => @lem1694070 a x y h1 h2 h0)). Qed.
Lemma lem1694072 (x : real) (h1 : term119) (h2 : term122) (h3 : term210 x) : False.
Proof. exact (ex_elim (@lem1691340 x h3) (fun y : real => fun h0 : term209 x y => @lem1694071 x y h1 h2 h0)). Qed.
Lemma lem1694073 (h1 : term119) (h2 : term122) (h3 : term125) : False.
Proof. exact (ex_elim (@lem1691107 h3) (fun x : real => fun h0 : term215 x => @lem1694072 x h1 h2 h0)). Qed.
Lemma lem1694074 (h1 : term122) (h2 : term125) : term130.
Proof. exact (fun h0 : term119 => @lem1694073 h0 h1 h2). Qed.
Lemma lem1694075 : term130 = term131.
Proof. exact (@lem69 term119). Qed.
Lemma lem1694076 (h1 : term122) (h2 : term125) : term131.
Proof. exact (EQ_MP (@lem1694075) (@lem1694074 h1 h2)). Qed.
Lemma lem1694077 (h1 : term125) : term134.
Proof. exact (fun h0 : term122 => @lem1694076 h0 h1). Qed.
Lemma lem1694078 : term136.
Proof. exact (fun h0 : term125 => @lem1694077 h0). Qed.
Lemma lem1694079 : term126.
Proof. exact (EQ_MP (@lem1690934) (@lem1694078)). Qed.
Lemma lem1694081 : term126.
Proof. exact (@lem1690587 (@lem1694079)). Qed.
Lemma lem1694082 (h1 : term125) : term133.
Proof. exact (@lem1694081 (@lem1690572 h1)). Qed.
Lemma lem1694083 (h1 : term125) : term130.
Proof. exact (@lem1694082 h1 (@lem1690567)). Qed.
Lemma lem1694084 (h1 : term125) : False.
Proof. exact (@lem1694083 h1 (@lem1690564)). Qed.
Lemma lem1694085 (h1 : term125) : term125 = False.
Proof. exact (prop_ext (fun h2 : term125 => @lem1694084 h1) (fun h2 : False => @lem1690572 h1)). Qed.
Lemma lem1694086 (h1 : term125) : False.
Proof. exact (EQ_MP (@lem1694085 h1) (@lem1690572 h1)). Qed.
Lemma lem1694087 : term124.
Proof. exact (fun h0 : term125 => @lem1694086 h0). Qed.
Lemma lem1694088 : term123.
Proof. exact (EQ_MP (@lem1690571) (@lem1694087)). Qed.
