Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_CONVEX_BOUND_GT_term_abbrevs.
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
Lemma lem1679777 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1679778 (u : real) (v : real) (a : real) : (term1 u v a) = (term2 u v a).
Proof. exact (@lem1679777 (term1 u v a)). Qed.
Lemma lem1679779 (u : real) (v : real) (a : real) : (term2 u v a) = (term1 u v a).
Proof. exact (SYM (@lem1679778 u v a)). Qed.
Lemma lem1679780 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term3 u v a.
Proof. exact (h1). Qed.
Lemma lem1679783 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term4 u v a.
Proof. exact (h1). Qed.
Lemma lem1679784 (u : real) (v : real) (a : real) : term5 u v a.
Proof. exact (fun h0 : term4 u v a => @lem1679783 u v a h0). Qed.
Lemma lem1679785 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (h1). Qed.
Lemma lem1679786 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term4 u v a.
Proof. exact (h1). Qed.
Lemma lem1679787 (u : real) (v : real) (a : real) (h1 : term4 u v a) (h2 : term5 u v a) : term4 u v a.
Proof. exact (@lem1679785 u v a h2 (@lem1679786 u v a h1)). Qed.
Lemma lem1679788 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term6 u v a.
Proof. exact (fun h0 : term5 u v a => @lem1679787 u v a h1 h0). Qed.
Lemma lem1679789 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (h1). Qed.
Lemma lem1679790 (u : real) (v : real) (a : real) (h1 : term4 u v a) (h2 : term5 u v a) : term4 u v a.
Proof. exact (@lem1679788 u v a h1 (@lem1679789 u v a h2)). Qed.
Lemma lem1679791 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (fun h0 : term4 u v a => @lem1679790 u v a h0 h1). Qed.
Lemma lem1679792 (u : real) (v : real) (a : real) : term7 u v a.
Proof. exact (fun h0 : term5 u v a => @lem1679791 u v a h0). Qed.
Lemma lem1679795 (u : real) (v : real) (a : real) : term5 u v a.
Proof. exact (@lem1679792 u v a (@lem1679784 u v a)). Qed.
Lemma lem1679827 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1679828 : term8 = term9.
Proof. exact (@lem1679827 term10). Qed.
Lemma lem1679833 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1679834 : term12 = term13.
Proof. exact (MK_COMB (@lem1679833) (@lem1679828)). Qed.
Lemma lem1679837 (u : real) (v : real) (a : real) : (term14 u v a) = (term14 u v a).
Proof. exact (eq_refl (term14 u v a)). Qed.
Lemma lem1679838 (u : real) (v : real) (a : real) : (term4 u v a) = (term15 u v a).
Proof. exact (MK_COMB (@lem1679837 u v a) (@lem1679834)). Qed.
Lemma lem1679841 (v : real) (a : real) : (term16 v a) = (term17 v a).
Proof. exact (fun_ext (fun u : real => @lem1679838 u v a)). Qed.
Lemma lem1679842 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1679843 (v : real) (a : real) : (term18 v a) = (term19 v a).
Proof. exact (MK_COMB (@lem1679842) (@lem1679841 v a)). Qed.
Lemma lem1679848 (a : real) : (term20 a) = (term21 a).
Proof. exact (fun_ext (fun v : real => @lem1679843 v a)). Qed.
Lemma lem1679849 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1679850 (a : real) : (term22 a) = (term23 a).
Proof. exact (MK_COMB (@lem1679849) (@lem1679848 a)). Qed.
Lemma lem1679855 : term24 = term25.
Proof. exact (fun_ext (fun a : real => @lem1679850 a)). Qed.
Lemma lem1679856 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1679865 : term26 = term27.
Proof. exact (MK_COMB (@lem1679856) (@lem1679855)). Qed.
Lemma lem1679866 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1679867 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1679866 x)). Qed.
Lemma lem1679868 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1679869 : term10 = term10.
Proof. exact (MK_COMB (@lem1679868) (@lem1679867)). Qed.
Lemma lem1679870 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1679871 : term9 = term9.
Proof. exact (MK_COMB (@lem1679870) (@lem1679869)). Qed.
Lemma lem1679872 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1679873 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1679872 x y z)). Qed.
Lemma lem1679874 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1679875 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1679874) (@lem1679873 x y)). Qed.
Lemma lem1679876 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1679875 x y)). Qed.
Lemma lem1679877 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1679878 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1679877) (@lem1679876 x)). Qed.
Lemma lem1679879 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1679878 x)). Qed.
Lemma lem1679880 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1679881 : term37 = term37.
Proof. exact (MK_COMB (@lem1679880) (@lem1679879)). Qed.
Lemma lem1679882 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1679883 : term11 = term11.
Proof. exact (MK_COMB (@lem1679882) (@lem1679881)). Qed.
Lemma lem1679884 : term13 = term13.
Proof. exact (MK_COMB (@lem1679883) (@lem1679871)). Qed.
Lemma lem1679893 (u : real) (v : real) (a : real) : (term14 u v a) = (term14 u v a).
Proof. exact (eq_refl (term14 u v a)). Qed.
Lemma lem1679894 (u : real) (v : real) (a : real) : (term15 u v a) = (term15 u v a).
Proof. exact (MK_COMB (@lem1679893 u v a) (@lem1679884)). Qed.
Lemma lem1679895 (v : real) (a : real) : (term17 v a) = (term17 v a).
Proof. exact (fun_ext (fun u : real => @lem1679894 u v a)). Qed.
Lemma lem1679896 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1679897 (v : real) (a : real) : (term19 v a) = (term19 v a).
Proof. exact (MK_COMB (@lem1679896) (@lem1679895 v a)). Qed.
Lemma lem1679898 (a : real) : (term21 a) = (term21 a).
Proof. exact (fun_ext (fun v : real => @lem1679897 v a)). Qed.
Lemma lem1679899 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1679900 (a : real) : (term23 a) = (term23 a).
Proof. exact (MK_COMB (@lem1679899) (@lem1679898 a)). Qed.
Lemma lem1679901 : term25 = term25.
Proof. exact (fun_ext (fun a : real => @lem1679900 a)). Qed.
Lemma lem1679902 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1679903 : term27 = term27.
Proof. exact (MK_COMB (@lem1679902) (@lem1679901)). Qed.
Lemma lem1679954 : term26 = term27.
Proof. exact (TRANS (@lem1679865) (@lem1679903)). Qed.
Lemma lem1679955 : term27 = term26.
Proof. exact (SYM (@lem1679954)). Qed.
Lemma lem1679956 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term3 u v a.
Proof. exact (h1). Qed.
Lemma lem1679957 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem1679958 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1679969 (u : real) (v : real) (a : real) : (term3 u v a) = (term38 u v a).
Proof. exact (@lem17362 ((real_add u v) = term39) ((term31 u v a) = a)). Qed.
Lemma lem1679971 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1679972 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1679971 x y z)). Qed.
Lemma lem1679973 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1679974 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1679973) (@lem1679972 x y)). Qed.
Lemma lem1679975 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1679974 x y)). Qed.
Lemma lem1679976 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1679977 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1679976) (@lem1679975 x)). Qed.
Lemma lem1679978 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1679977 x)). Qed.
Lemma lem1679979 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1679996 : term37 = term37.
Proof. exact (MK_COMB (@lem1679979) (@lem1679978)). Qed.
Lemma lem1679997 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1679996) (@lem1679957 h1)). Qed.
Lemma lem1679998 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1679999 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1679998 x)). Qed.
Lemma lem1680000 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680009 : term10 = term10.
Proof. exact (MK_COMB (@lem1680000) (@lem1679999)). Qed.
Lemma lem1680010 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1680009) (@lem1679958 h1)). Qed.
Lemma lem1680048 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term38 u v a.
Proof. exact (EQ_MP (@lem1679969 u v a) (@lem1679956 u v a h1)). Qed.
Lemma lem1680073 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1680074 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1680073 x y z)). Qed.
Lemma lem1680075 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680076 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1680075) (@lem1680074 x y)). Qed.
Lemma lem1680077 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1680076 x y)). Qed.
Lemma lem1680078 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680079 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1680078) (@lem1680077 x)). Qed.
Lemma lem1680080 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1680079 x)). Qed.
Lemma lem1680081 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680082 : term37 = term37.
Proof. exact (MK_COMB (@lem1680081) (@lem1680080)). Qed.
Lemma lem1680083 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1680082) (@lem1679997 h1)). Qed.
Lemma lem1680098 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1680099 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1680098 x)). Qed.
Lemma lem1680100 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680101 : term10 = term10.
Proof. exact (MK_COMB (@lem1680100) (@lem1680099)). Qed.
Lemma lem1680102 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1680101) (@lem1680010 h1)). Qed.
Lemma lem1680106 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1680107 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1680106 x y z)). Qed.
Lemma lem1680108 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680109 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1680108) (@lem1680107 x y)). Qed.
Lemma lem1680110 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1680109 x y)). Qed.
Lemma lem1680111 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680112 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1680111) (@lem1680110 x)). Qed.
Lemma lem1680113 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1680112 x)). Qed.
Lemma lem1680114 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680116 : term37 = term37.
Proof. exact (MK_COMB (@lem1680114) (@lem1680113)). Qed.
Lemma lem1680117 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1680116) (@lem1680083 h1)). Qed.
Lemma lem1680119 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1680120 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1680119 x)). Qed.
Lemma lem1680121 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680123 : term10 = term10.
Proof. exact (MK_COMB (@lem1680121) (@lem1680120)). Qed.
Lemma lem1680124 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1680123) (@lem1680102 h1)). Qed.
Lemma lem1680133 (_25911 : real) (h1 : term37) : term40 _25911.
Proof. exact (@lem1680117 h1 _25911). Qed.
Lemma lem1680134 (_25911 : real) : (term40 _25911) = (term35 _25911).
Proof. exact (eq_refl (term40 _25911)). Qed.
Lemma lem1680135 (_25911 : real) (h1 : term37) : term35 _25911.
Proof. exact (EQ_MP (@lem1680134 _25911) (@lem1680133 _25911 h1)). Qed.
Lemma lem1680136 (_25911 : real) (_25912 : real) (h1 : term37) : term41 _25911 _25912.
Proof. exact (@lem1680135 _25911 h1 _25912). Qed.
Lemma lem1680137 (_25911 : real) (_25912 : real) : (term41 _25911 _25912) = (term33 _25911 _25912).
Proof. exact (eq_refl (term41 _25911 _25912)). Qed.
Lemma lem1680138 (_25911 : real) (_25912 : real) (h1 : term37) : term33 _25911 _25912.
Proof. exact (EQ_MP (@lem1680137 _25911 _25912) (@lem1680136 _25911 _25912 h1)). Qed.
Lemma lem1680139 (_25911 : real) (_25912 : real) (_25913 : real) (h1 : term37) : term42 _25911 _25912 _25913.
Proof. exact (@lem1680138 _25911 _25912 h1 _25913). Qed.
Lemma lem1680140 (_25911 : real) (_25912 : real) (_25913 : real) : (term42 _25911 _25912 _25913) = ((term30 _25911 _25912 _25913) = (term31 _25911 _25912 _25913)).
Proof. exact (eq_refl (term42 _25911 _25912 _25913)). Qed.
Lemma lem1680142 (_25914 : real) (h1 : term10) : term43 _25914.
Proof. exact (@lem1680124 h1 _25914). Qed.
Lemma lem1680143 (_25914 : real) : (term43 _25914) = ((term28 _25914) = _25914).
Proof. exact (eq_refl (term43 _25914)). Qed.
Lemma lem1680152 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term44 u v a.
Proof. exact (proj2 (@lem1680048 u v a h1)). Qed.
Lemma lem1680177 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1680178 (_25921 : real) (_25923 : real) (h1 : _25921 = _25923) : _25921 = _25923.
Proof. exact (h1). Qed.
Lemma lem1680179 (_25922 : real) (_25924 : real) (h1 : _25922 = _25924) : _25922 = _25924.
Proof. exact (h1). Qed.
Lemma lem1680180 (_25921 : real) (_25923 : real) (h1 : _25921 = _25923) : (real_mul _25921) = (real_mul _25923).
Proof. exact (MK_COMB (@lem1680177) (@lem1680178 _25921 _25923 h1)). Qed.
Lemma lem1680181 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) (h1 : _25921 = _25923) (h2 : _25922 = _25924) : (real_mul _25921 _25922) = (real_mul _25923 _25924).
Proof. exact (MK_COMB (@lem1680180 _25921 _25923 h1) (@lem1680179 _25922 _25924 h2)). Qed.
Lemma lem1680182 (_25922 : real) (_25924 : real) (_25921 : real) (_25923 : real) (h1 : _25921 = _25923) : term45 _25921 _25922 _25923 _25924.
Proof. exact (fun h0 : _25922 = _25924 => @lem1680181 _25921 _25923 _25922 _25924 h1 h0). Qed.
Lemma lem1680184 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1680185 (_25921 : real) (_25922 : real) (_25923 : real) (_25924 : real) : (term45 _25921 _25922 _25923 _25924) = (term47 _25921 _25922 _25923 _25924).
Proof. exact (@lem1680184 (_25922 = _25924) ((real_mul _25921 _25922) = (real_mul _25923 _25924))). Qed.
Lemma lem1680186 (_25922 : real) (_25924 : real) (_25921 : real) (_25923 : real) (h1 : _25921 = _25923) : term47 _25921 _25922 _25923 _25924.
Proof. exact (EQ_MP (@lem1680185 _25921 _25922 _25923 _25924) (@lem1680182 _25922 _25924 _25921 _25923 h1)). Qed.
Lemma lem1680187 (_25921 : real) (_25922 : real) (_25923 : real) (_25924 : real) : term48 _25921 _25922 _25923 _25924.
Proof. exact (fun h0 : _25921 = _25923 => @lem1680186 _25922 _25924 _25921 _25923 h0). Qed.
Lemma lem1680189 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1680190 (_25921 : real) (_25922 : real) (_25923 : real) (_25924 : real) : (term48 _25921 _25922 _25923 _25924) = (term49 _25921 _25922 _25923 _25924).
Proof. exact (@lem1680189 (_25921 = _25923) (term47 _25921 _25922 _25923 _25924)). Qed.
Lemma lem1680191 (_25921 : real) (_25922 : real) (_25923 : real) (_25924 : real) : term49 _25921 _25922 _25923 _25924.
Proof. exact (EQ_MP (@lem1680190 _25921 _25922 _25923 _25924) (@lem1680187 _25921 _25922 _25923 _25924)). Qed.
Lemma lem1680208 (x : real) (y : real) (z : real) : term50 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1680212 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (real_add u v) = term39.
Proof. exact (proj1 (@lem1680048 u v a h1)). Qed.
Lemma lem1680213 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1680212 u v a h1). Qed.
Lemma lem1680215 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1680216 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1680215 ((real_add u v) = term39)). Qed.
Lemma lem1680217 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1680216 u v) (@lem1680213 u v a h1)). Qed.
Lemma lem1680219 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1680220 (a : real) : a = a.
Proof. exact (@lem1680219 a). Qed.
Lemma lem1680221 (a : real) : term54 a.
Proof. exact (fun h0 : term55 a => @lem1680220 a). Qed.
Lemma lem1680223 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1680224 (a : real) : (term54 a) = (a = a).
Proof. exact (@lem1680223 (a = a)). Qed.
Lemma lem1680225 (a : real) : a = a.
Proof. exact (EQ_MP (@lem1680224 a) (@lem1680221 a)). Qed.
Lemma lem1680243 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1680244 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) : (term47 _25921 _25922 _25923 _25924) = (term56 _25921 _25923 _25922 _25924).
Proof. exact (@lem1680243 ((real_mul _25921 _25922) = (real_mul _25923 _25924)) (term57 _25922 _25924)). Qed.
Lemma lem1680254 (_25921 : real) (_25923 : real) : (term58 _25921 _25923) = (term58 _25921 _25923).
Proof. exact (eq_refl (term58 _25921 _25923)). Qed.
Lemma lem1680255 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) : (term49 _25921 _25922 _25923 _25924) = (term59 _25921 _25923 _25922 _25924).
Proof. exact (MK_COMB (@lem1680254 _25921 _25923) (@lem1680244 _25921 _25923 _25922 _25924)). Qed.
Lemma lem1680259 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1680260 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) : (term59 _25921 _25923 _25922 _25924) = (term61 _25921 _25923 _25922 _25924).
Proof. exact (@lem1680259 ((real_mul _25921 _25922) = (real_mul _25923 _25924)) (term57 _25921 _25923) (term57 _25922 _25924)). Qed.
Lemma lem1680282 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) : (term49 _25921 _25922 _25923 _25924) = (term61 _25921 _25923 _25922 _25924).
Proof. exact (TRANS (@lem1680255 _25921 _25923 _25922 _25924) (@lem1680260 _25921 _25923 _25922 _25924)). Qed.
Lemma lem1680283 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1680284 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) : (term62 _25921 _25922 _25923 _25924) = (term63 _25921 _25923 _25922 _25924).
Proof. exact (MK_COMB (@lem1680283) (@lem1680282 _25921 _25923 _25922 _25924)). Qed.
Lemma lem1680306 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) : (term61 _25921 _25923 _25922 _25924) = (term61 _25921 _25923 _25922 _25924).
Proof. exact (eq_refl (term61 _25921 _25923 _25922 _25924)). Qed.
Lemma lem1680307 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) : ((term49 _25921 _25922 _25923 _25924) = (term61 _25921 _25923 _25922 _25924)) = ((term61 _25921 _25923 _25922 _25924) = (term61 _25921 _25923 _25922 _25924)).
Proof. exact (MK_COMB (@lem1680284 _25921 _25923 _25922 _25924) (@lem1680306 _25921 _25923 _25922 _25924)). Qed.
Lemma lem1680309 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1680310 (x : Prop) : (x = x) = True.
Proof. exact (@lem1680309 Prop x). Qed.
Lemma lem1680311 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) : ((term61 _25921 _25923 _25922 _25924) = (term61 _25921 _25923 _25922 _25924)) = True.
Proof. exact (@lem1680310 (term61 _25921 _25923 _25922 _25924)). Qed.
Lemma lem1680312 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) : ((term49 _25921 _25922 _25923 _25924) = (term61 _25921 _25923 _25922 _25924)) = True.
Proof. exact (TRANS (@lem1680307 _25921 _25923 _25922 _25924) (@lem1680311 _25921 _25923 _25922 _25924)). Qed.
Lemma lem1680313 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) : True = ((term49 _25921 _25922 _25923 _25924) = (term61 _25921 _25923 _25922 _25924)).
Proof. exact (SYM (@lem1680312 _25921 _25923 _25922 _25924)). Qed.
Lemma lem1680314 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) : (term49 _25921 _25922 _25923 _25924) = (term61 _25921 _25923 _25922 _25924).
Proof. exact (EQ_MP (@lem1680313 _25921 _25923 _25922 _25924) (@lem0)). Qed.
Lemma lem1680315 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) : term61 _25921 _25923 _25922 _25924.
Proof. exact (EQ_MP (@lem1680314 _25921 _25923 _25922 _25924) (@lem1680191 _25921 _25922 _25923 _25924)). Qed.
Lemma lem1680317 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1680318 (_25921 : real) (_25922 : real) (_25923 : real) (_25924 : real) : (term61 _25921 _25923 _25922 _25924) = (term65 _25921 _25922 _25923 _25924).
Proof. exact (@lem1680317 (term66 _25921 _25923 _25922 _25924) ((real_mul _25921 _25922) = (real_mul _25923 _25924))). Qed.
Lemma lem1680320 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1680321 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) : (term69 _25921 _25923 _25922 _25924) = (term70 _25921 _25923 _25922 _25924).
Proof. exact (@lem1680320 (term57 _25921 _25923) (term57 _25922 _25924)). Qed.
Lemma lem1680323 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1680324 (_25921 : real) (_25923 : real) : (term72 _25921 _25923) = (_25921 = _25923).
Proof. exact (@lem1680323 (_25921 = _25923)). Qed.
Lemma lem1680325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1680326 (_25921 : real) (_25923 : real) : (term73 _25921 _25923) = (term74 _25921 _25923).
Proof. exact (MK_COMB (@lem1680325) (@lem1680324 _25921 _25923)). Qed.
Lemma lem1680328 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1680329 (_25922 : real) (_25924 : real) : (term72 _25922 _25924) = (_25922 = _25924).
Proof. exact (@lem1680328 (_25922 = _25924)). Qed.
Lemma lem1680330 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) : (term70 _25921 _25923 _25922 _25924) = (term75 _25921 _25923 _25922 _25924).
Proof. exact (MK_COMB (@lem1680326 _25921 _25923) (@lem1680329 _25922 _25924)). Qed.
Lemma lem1680331 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) : (term69 _25921 _25923 _25922 _25924) = (term75 _25921 _25923 _25922 _25924).
Proof. exact (TRANS (@lem1680321 _25921 _25923 _25922 _25924) (@lem1680330 _25921 _25923 _25922 _25924)). Qed.
Lemma lem1680332 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1680333 (_25921 : real) (_25923 : real) (_25922 : real) (_25924 : real) : (term76 _25921 _25923 _25922 _25924) = (term77 _25921 _25923 _25922 _25924).
Proof. exact (MK_COMB (@lem1680332) (@lem1680331 _25921 _25923 _25922 _25924)). Qed.
Lemma lem1680334 (_25921 : real) (_25922 : real) (_25923 : real) (_25924 : real) : ((real_mul _25921 _25922) = (real_mul _25923 _25924)) = ((real_mul _25921 _25922) = (real_mul _25923 _25924)).
Proof. exact (eq_refl ((real_mul _25921 _25922) = (real_mul _25923 _25924))). Qed.
Lemma lem1680335 (_25921 : real) (_25922 : real) (_25923 : real) (_25924 : real) : (term65 _25921 _25922 _25923 _25924) = (term78 _25921 _25922 _25923 _25924).
Proof. exact (MK_COMB (@lem1680333 _25921 _25923 _25922 _25924) (@lem1680334 _25921 _25922 _25923 _25924)). Qed.
Lemma lem1680336 (_25921 : real) (_25922 : real) (_25923 : real) (_25924 : real) : (term61 _25921 _25923 _25922 _25924) = (term78 _25921 _25922 _25923 _25924).
Proof. exact (TRANS (@lem1680318 _25921 _25922 _25923 _25924) (@lem1680335 _25921 _25922 _25923 _25924)). Qed.
Lemma lem1680338 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term79 u v a.
Proof. exact (conj (@lem1680217 u v a h1) (@lem1680225 a)). Qed.
Lemma lem1680340 (_25921 : real) (_25922 : real) (_25923 : real) (_25924 : real) : term78 _25921 _25922 _25923 _25924.
Proof. exact (EQ_MP (@lem1680336 _25921 _25922 _25923 _25924) (@lem1680315 _25921 _25923 _25922 _25924)). Qed.
Lemma lem1680341 (u : real) (v : real) (a : real) : term80 u v a.
Proof. exact (@lem1680340 (real_add u v) a term39 a). Qed.
Lemma lem1680344 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term30 u v a) = (term28 a).
Proof. exact (@lem1680341 u v a (@lem1680338 u v a h1)). Qed.
Lemma lem1680345 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term81 u v a.
Proof. exact (fun h0 : term82 u v a => @lem1680344 u v a h1). Qed.
Lemma lem1680347 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1680348 (u : real) (v : real) (a : real) : (term81 u v a) = ((term30 u v a) = (term28 a)).
Proof. exact (@lem1680347 ((term30 u v a) = (term28 a))). Qed.
Lemma lem1680349 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term30 u v a) = (term28 a).
Proof. exact (EQ_MP (@lem1680348 u v a) (@lem1680345 u v a h1)). Qed.
Lemma lem1680351 (_25911 : real) (_25912 : real) (_25913 : real) (h1 : term37) : (term30 _25911 _25912 _25913) = (term31 _25911 _25912 _25913).
Proof. exact (EQ_MP (@lem1680140 _25911 _25912 _25913) (@lem1680139 _25911 _25912 _25913 h1)). Qed.
Lemma lem1680352 (u : real) (v : real) (a : real) (h1 : term37) : (term30 u v a) = (term31 u v a).
Proof. exact (@lem1680351 u v a h1). Qed.
Lemma lem1680353 (u : real) (v : real) (a : real) (h1 : term37) : term83 u v a.
Proof. exact (fun h0 : term84 u v a => @lem1680352 u v a h1). Qed.
Lemma lem1680355 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1680356 (u : real) (v : real) (a : real) : (term83 u v a) = ((term30 u v a) = (term31 u v a)).
Proof. exact (@lem1680355 ((term30 u v a) = (term31 u v a))). Qed.
Lemma lem1680357 (u : real) (v : real) (a : real) (h1 : term37) : (term30 u v a) = (term31 u v a).
Proof. exact (EQ_MP (@lem1680356 u v a) (@lem1680353 u v a h1)). Qed.
Lemma lem1680375 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1680376 (y : real) (x : real) (z : real) : (term85 x y z) = (term86 y x z).
Proof. exact (@lem1680375 (y = z) (term57 x z)). Qed.
Lemma lem1680386 (x : real) (y : real) : (term58 x y) = (term58 x y).
Proof. exact (eq_refl (term58 x y)). Qed.
Lemma lem1680387 (y : real) (x : real) (z : real) : (term50 x y z) = (term87 y x z).
Proof. exact (MK_COMB (@lem1680386 x y) (@lem1680376 y x z)). Qed.
Lemma lem1680391 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1680392 (y : real) (x : real) (z : real) : (term87 y x z) = (term88 y x z).
Proof. exact (@lem1680391 (y = z) (term57 x y) (term57 x z)). Qed.
Lemma lem1680414 (y : real) (x : real) (z : real) : (term50 x y z) = (term88 y x z).
Proof. exact (TRANS (@lem1680387 y x z) (@lem1680392 y x z)). Qed.
Lemma lem1680415 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1680416 (y : real) (x : real) (z : real) : (term89 x y z) = (term90 y x z).
Proof. exact (MK_COMB (@lem1680415) (@lem1680414 y x z)). Qed.
Lemma lem1680438 (y : real) (x : real) (z : real) : (term88 y x z) = (term88 y x z).
Proof. exact (eq_refl (term88 y x z)). Qed.
Lemma lem1680439 (y : real) (x : real) (z : real) : ((term50 x y z) = (term88 y x z)) = ((term88 y x z) = (term88 y x z)).
Proof. exact (MK_COMB (@lem1680416 y x z) (@lem1680438 y x z)). Qed.
Lemma lem1680441 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1680442 (x : Prop) : (x = x) = True.
Proof. exact (@lem1680441 Prop x). Qed.
Lemma lem1680443 (y : real) (x : real) (z : real) : ((term88 y x z) = (term88 y x z)) = True.
Proof. exact (@lem1680442 (term88 y x z)). Qed.
Lemma lem1680444 (y : real) (x : real) (z : real) : ((term50 x y z) = (term88 y x z)) = True.
Proof. exact (TRANS (@lem1680439 y x z) (@lem1680443 y x z)). Qed.
Lemma lem1680445 (y : real) (x : real) (z : real) : True = ((term50 x y z) = (term88 y x z)).
Proof. exact (SYM (@lem1680444 y x z)). Qed.
Lemma lem1680446 (y : real) (x : real) (z : real) : (term50 x y z) = (term88 y x z).
Proof. exact (EQ_MP (@lem1680445 y x z) (@lem0)). Qed.
Lemma lem1680447 (y : real) (x : real) (z : real) : term88 y x z.
Proof. exact (EQ_MP (@lem1680446 y x z) (@lem1680208 x y z)). Qed.
Lemma lem1680449 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1680450 (x : real) (y : real) (z : real) : (term88 y x z) = (term91 x y z).
Proof. exact (@lem1680449 (term92 y x z) (y = z)). Qed.
Lemma lem1680452 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1680453 (y : real) (x : real) (z : real) : (term93 y x z) = (term94 y x z).
Proof. exact (@lem1680452 (term57 x y) (term57 x z)). Qed.
Lemma lem1680455 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1680456 (x : real) (y : real) : (term72 x y) = (x = y).
Proof. exact (@lem1680455 (x = y)). Qed.
Lemma lem1680457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1680458 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1680457) (@lem1680456 x y)). Qed.
Lemma lem1680460 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1680461 (x : real) (z : real) : (term72 x z) = (x = z).
Proof. exact (@lem1680460 (x = z)). Qed.
Lemma lem1680462 (y : real) (x : real) (z : real) : (term94 y x z) = (term95 y x z).
Proof. exact (MK_COMB (@lem1680458 x y) (@lem1680461 x z)). Qed.
Lemma lem1680463 (y : real) (x : real) (z : real) : (term93 y x z) = (term95 y x z).
Proof. exact (TRANS (@lem1680453 y x z) (@lem1680462 y x z)). Qed.
Lemma lem1680464 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1680465 (y : real) (x : real) (z : real) : (term96 y x z) = (term97 y x z).
Proof. exact (MK_COMB (@lem1680464) (@lem1680463 y x z)). Qed.
Lemma lem1680466 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1680467 (x : real) (y : real) (z : real) : (term91 x y z) = (term98 x y z).
Proof. exact (MK_COMB (@lem1680465 y x z) (@lem1680466 y z)). Qed.
Lemma lem1680468 (x : real) (y : real) (z : real) : (term88 y x z) = (term98 x y z).
Proof. exact (TRANS (@lem1680450 x y z) (@lem1680467 x y z)). Qed.
Lemma lem1680470 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term99 u v a.
Proof. exact (conj (@lem1680349 u v a h2) (@lem1680357 u v a h1)). Qed.
Lemma lem1680472 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (EQ_MP (@lem1680468 x y z) (@lem1680447 y x z)). Qed.
Lemma lem1680473 (u : real) (v : real) (a : real) : term100 u v a.
Proof. exact (@lem1680472 (term30 u v a) (term28 a) (term31 u v a)). Qed.
Lemma lem1680476 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : (term28 a) = (term31 u v a).
Proof. exact (@lem1680473 u v a (@lem1680470 u v a h1 h2)). Qed.
Lemma lem1680477 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term101 u v a.
Proof. exact (fun h0 : term102 u v a => @lem1680476 u v a h1 h2). Qed.
Lemma lem1680479 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1680480 (u : real) (v : real) (a : real) : (term101 u v a) = ((term28 a) = (term31 u v a)).
Proof. exact (@lem1680479 ((term28 a) = (term31 u v a))). Qed.
Lemma lem1680481 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : (term28 a) = (term31 u v a).
Proof. exact (EQ_MP (@lem1680480 u v a) (@lem1680477 u v a h1 h2)). Qed.
Lemma lem1680483 (_25914 : real) (h1 : term10) : (term28 _25914) = _25914.
Proof. exact (EQ_MP (@lem1680143 _25914) (@lem1680142 _25914 h1)). Qed.
Lemma lem1680484 (a : real) (h1 : term10) : (term28 a) = a.
Proof. exact (@lem1680483 a h1). Qed.
Lemma lem1680485 (a : real) (h1 : term10) : term103 a.
Proof. exact (fun h0 : term104 a => @lem1680484 a h1). Qed.
Lemma lem1680487 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1680488 (a : real) : (term103 a) = ((term28 a) = a).
Proof. exact (@lem1680487 ((term28 a) = a)). Qed.
Lemma lem1680489 (a : real) (h1 : term10) : (term28 a) = a.
Proof. exact (EQ_MP (@lem1680488 a) (@lem1680485 a h1)). Qed.
Lemma lem1680490 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term105 u v a.
Proof. exact (conj (@lem1680481 u v a h1 h3) (@lem1680489 a h2)). Qed.
Lemma lem1680492 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (EQ_MP (@lem1680468 x y z) (@lem1680447 y x z)). Qed.
Lemma lem1680493 (u : real) (v : real) (a : real) : term106 u v a.
Proof. exact (@lem1680492 (term28 a) (term31 u v a) a). Qed.
Lemma lem1680496 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : (term31 u v a) = a.
Proof. exact (@lem1680493 u v a (@lem1680490 u v a h1 h2 h3)). Qed.
Lemma lem1680497 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term107 u v a.
Proof. exact (fun h0 : term44 u v a => @lem1680496 u v a h1 h2 h3). Qed.
Lemma lem1680499 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1680500 (u : real) (v : real) (a : real) : (term107 u v a) = ((term31 u v a) = a).
Proof. exact (@lem1680499 ((term31 u v a) = a)). Qed.
Lemma lem1680501 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : (term31 u v a) = a.
Proof. exact (EQ_MP (@lem1680500 u v a) (@lem1680497 u v a h1 h2 h3)). Qed.
Lemma lem1680504 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1680506 (u : real) (v : real) (a : real) : (term44 u v a) = (term108 u v a).
Proof. exact (@lem1680504 ((term31 u v a) = a)). Qed.
Lemma lem1680509 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term108 u v a.
Proof. exact (EQ_MP (@lem1680506 u v a) (@lem1680152 u v a h1)). Qed.
Lemma lem1680512 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (@lem1680509 u v a h3 (@lem1680501 u v a h1 h2 h3)). Qed.
Lemma lem1680513 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term109.
Proof. exact (fun h0 : ~ False => @lem1680512 u v a h1 h2 h3). Qed.
Lemma lem1680515 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1680516 : term109 = False.
Proof. exact (@lem1680515 False). Qed.
Lemma lem1680517 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1680516) (@lem1680513 u v a h1 h2 h3)). Qed.
Lemma lem1680518 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1680517 u v a h1 h2 h3) (fun h4 : False => @lem1680124 h2)). Qed.
Lemma lem1680519 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1680518 u v a h1 h2 h3) (@lem1680124 h2)). Qed.
Lemma lem1680520 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1680519 u v a h1 h2 h3) (fun h4 : False => @lem1680117 h1)). Qed.
Lemma lem1680521 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1680520 u v a h1 h2 h3) (@lem1680117 h1)). Qed.
Lemma lem1680522 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1680521 u v a h1 h2 h3) (fun h4 : False => @lem1680102 h2)). Qed.
Lemma lem1680523 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1680522 u v a h1 h2 h3) (@lem1680102 h2)). Qed.
Lemma lem1680524 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1680523 u v a h1 h2 h3) (fun h4 : False => @lem1680083 h1)). Qed.
Lemma lem1680525 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1680524 u v a h1 h2 h3) (@lem1680083 h1)). Qed.
Lemma lem1680526 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1680525 u v a h1 h2 h3) (fun h4 : False => @lem1680010 h2)). Qed.
Lemma lem1680527 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1680526 u v a h1 h2 h3) (@lem1680010 h2)). Qed.
Lemma lem1680528 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1680527 u v a h1 h2 h3) (fun h4 : False => @lem1679997 h1)). Qed.
Lemma lem1680529 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1680528 u v a h1 h2 h3) (@lem1679997 h1)). Qed.
Lemma lem1680530 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term8.
Proof. exact (fun h0 : term10 => @lem1680529 u v a h1 h0 h2). Qed.
Lemma lem1680531 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1680532 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term9.
Proof. exact (EQ_MP (@lem1680531) (@lem1680530 u v a h1 h2)). Qed.
Lemma lem1680533 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term13.
Proof. exact (fun h0 : term37 => @lem1680532 u v a h0 h1). Qed.
Lemma lem1680534 (u : real) (v : real) (a : real) : term15 u v a.
Proof. exact (fun h0 : term3 u v a => @lem1680533 u v a h0). Qed.
Lemma lem1680539 (v : real) (a : real) : term19 v a.
Proof. exact (fun u : real => @lem1680534 u v a). Qed.
Lemma lem1680544 (a : real) : term23 a.
Proof. exact (fun v : real => @lem1680539 v a). Qed.
Lemma lem1680549 : term27.
Proof. exact (fun a : real => @lem1680544 a). Qed.
Lemma lem1680550 : term26.
Proof. exact (EQ_MP (@lem1679955) (@lem1680549)). Qed.
Lemma lem1680551 (a : real) : term110 a.
Proof. exact (@lem1680550 a). Qed.
Lemma lem1680552 (a : real) : (term110 a) = (term22 a).
Proof. exact (eq_refl (term110 a)). Qed.
Lemma lem1680553 (a : real) : term22 a.
Proof. exact (EQ_MP (@lem1680552 a) (@lem1680551 a)). Qed.
Lemma lem1680554 (a : real) (v : real) : term111 a v.
Proof. exact (@lem1680553 a v). Qed.
Lemma lem1680555 (v : real) (a : real) : (term111 a v) = (term18 v a).
Proof. exact (eq_refl (term111 a v)). Qed.
Lemma lem1680556 (v : real) (a : real) : term18 v a.
Proof. exact (EQ_MP (@lem1680555 v a) (@lem1680554 a v)). Qed.
Lemma lem1680557 (v : real) (a : real) (u : real) : term112 v a u.
Proof. exact (@lem1680556 v a u). Qed.
Lemma lem1680558 (u : real) (v : real) (a : real) : (term112 v a u) = (term4 u v a).
Proof. exact (eq_refl (term112 v a u)). Qed.
Lemma lem1680559 (u : real) (v : real) (a : real) : term4 u v a.
Proof. exact (EQ_MP (@lem1680558 u v a) (@lem1680557 v a u)). Qed.
Lemma lem1680561 (u : real) (v : real) (a : real) : term4 u v a.
Proof. exact (@lem1679795 u v a (@lem1680559 u v a)). Qed.
Lemma lem1680562 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term12.
Proof. exact (@lem1680561 u v a (@lem1679780 u v a h1)). Qed.
Lemma lem1680563 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term8.
Proof. exact (@lem1680562 u v a h1 (@lem1487144)). Qed.
Lemma lem1680564 (u : real) (v : real) (a : real) (h1 : term3 u v a) : False.
Proof. exact (@lem1680563 u v a h1 (@lem1338986)). Qed.
Lemma lem1680565 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term3 u v a) = False.
Proof. exact (prop_ext (fun h2 : term3 u v a => @lem1680564 u v a h1) (fun h2 : False => @lem1679780 u v a h1)). Qed.
Lemma lem1680566 (u : real) (v : real) (a : real) (h1 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1680565 u v a h1) (@lem1679780 u v a h1)). Qed.
Lemma lem1680567 (u : real) (v : real) (a : real) : term2 u v a.
Proof. exact (fun h0 : term3 u v a => @lem1680566 u v a h0). Qed.
Lemma lem1680568 (u : real) (v : real) (a : real) : term1 u v a.
Proof. exact (EQ_MP (@lem1679779 u v a) (@lem1680567 u v a)). Qed.
Lemma lem1680569 (t1 : Prop) : term113 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1680570 (t1 : Prop) : (term113 t1) = (term114 t1).
Proof. exact (eq_refl (term113 t1)). Qed.
Lemma lem1680571 (t1 : Prop) : term114 t1.
Proof. exact (EQ_MP (@lem1680570 t1) (@lem1680569 t1)). Qed.
Lemma lem1680572 (t1 : Prop) (t2 : Prop) : term115 t1 t2.
Proof. exact (@lem1680571 t1 t2). Qed.
Lemma lem1680573 (t1 : Prop) (t2 : Prop) : (term115 t1 t2) = (term116 t1 t2).
Proof. exact (eq_refl (term115 t1 t2)). Qed.
Lemma lem1680574 (t1 : Prop) (t2 : Prop) : term116 t1 t2.
Proof. exact (EQ_MP (@lem1680573 t1 t2) (@lem1680572 t1 t2)). Qed.
Lemma lem1680575 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term117 t1 t2 t3.
Proof. exact (@lem1680574 t1 t2 t3). Qed.
Lemma lem1680576 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term117 t1 t2 t3) = ((term60 t1 t2 t3) = (term118 t1 t2 t3)).
Proof. exact (eq_refl (term117 t1 t2 t3)). Qed.
Lemma lem1680577 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term60 t1 t2 t3) = (term118 t1 t2 t3).
Proof. exact (EQ_MP (@lem1680576 t1 t2 t3) (@lem1680575 t1 t2 t3)). Qed.
Lemma lem1680578 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term118 t1 t2 t3) = (term60 t1 t2 t3).
Proof. exact (SYM (@lem1680577 t1 t2 t3)). Qed.
Lemma lem1680579 : term119.
Proof. exact (fun b : real => @lem1672514 b). Qed.
Lemma lem1680580 (u : real) (v : real) : term120 u v.
Proof. exact (fun a : real => @lem1680568 u v a). Qed.
Lemma lem1680581 (u : real) : term121 u.
Proof. exact (fun v : real => @lem1680580 u v). Qed.
Lemma lem1680582 : term122.
Proof. exact (fun u : real => @lem1680581 u). Qed.
Lemma lem1680584 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1680585 : term123 = term124.
Proof. exact (@lem1680584 term123). Qed.
Lemma lem1680586 : term124 = term123.
Proof. exact (SYM (@lem1680585)). Qed.
Lemma lem1680587 (h1 : term125) : term125.
Proof. exact (h1). Qed.
Lemma lem1680590 (h1 : term126) : term126.
Proof. exact (h1). Qed.
Lemma lem1680591 : term127.
Proof. exact (fun h0 : term126 => @lem1680590 h0). Qed.
Lemma lem1680592 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem1680593 (h1 : term126) : term126.
Proof. exact (h1). Qed.
Lemma lem1680594 (h1 : term126) (h2 : term127) : term126.
Proof. exact (@lem1680592 h2 (@lem1680593 h1)). Qed.
Lemma lem1680595 (h1 : term126) : term128.
Proof. exact (fun h0 : term127 => @lem1680594 h1 h0). Qed.
Lemma lem1680596 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem1680597 (h1 : term126) (h2 : term127) : term126.
Proof. exact (@lem1680595 h1 (@lem1680596 h2)). Qed.
Lemma lem1680598 (h1 : term127) : term127.
Proof. exact (fun h0 : term126 => @lem1680597 h0 h1). Qed.
Lemma lem1680599 : term129.
Proof. exact (fun h0 : term127 => @lem1680598 h0). Qed.
Lemma lem1680602 : term127.
Proof. exact (@lem1680599 (@lem1680591)). Qed.
Lemma lem1680652 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1680653 : term130 = term131.
Proof. exact (@lem1680652 term119). Qed.
Lemma lem1680688 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem1680689 : term133 = term134.
Proof. exact (MK_COMB (@lem1680688) (@lem1680653)). Qed.
Lemma lem1680692 : term135 = term135.
Proof. exact (eq_refl term135). Qed.
Lemma lem1680699 : term126 = term136.
Proof. exact (MK_COMB (@lem1680692) (@lem1680689)). Qed.
Lemma lem1680720 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term137 x y u a v b).
Proof. exact (eq_refl (term137 x y u a v b)). Qed.
Lemma lem1680721 (x : real) (y : real) (u : real) (a : real) (b : real) : (term138 x y u a b) = (term138 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1680720 x y u a v b)). Qed.
Lemma lem1680722 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680723 (x : real) (y : real) (u : real) (a : real) (b : real) : (term139 x y u a b) = (term139 x y u a b).
Proof. exact (MK_COMB (@lem1680722) (@lem1680721 x y u a b)). Qed.
Lemma lem1680724 (x : real) (y : real) (a : real) (b : real) : (term140 x y a b) = (term140 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1680723 x y u a b)). Qed.
Lemma lem1680725 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680726 (x : real) (y : real) (a : real) (b : real) : (term141 x y a b) = (term141 x y a b).
Proof. exact (MK_COMB (@lem1680725) (@lem1680724 x y a b)). Qed.
Lemma lem1680727 (x : real) (y : real) (b : real) : (term142 x y b) = (term142 x y b).
Proof. exact (fun_ext (fun a : real => @lem1680726 x y a b)). Qed.
Lemma lem1680728 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680729 (x : real) (y : real) (b : real) : (term143 x y b) = (term143 x y b).
Proof. exact (MK_COMB (@lem1680728) (@lem1680727 x y b)). Qed.
Lemma lem1680730 (x : real) (b : real) : (term144 x b) = (term144 x b).
Proof. exact (fun_ext (fun y : real => @lem1680729 x y b)). Qed.
Lemma lem1680731 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680732 (x : real) (b : real) : (term145 x b) = (term145 x b).
Proof. exact (MK_COMB (@lem1680731) (@lem1680730 x b)). Qed.
Lemma lem1680733 (b : real) : (term146 b) = (term146 b).
Proof. exact (fun_ext (fun x : real => @lem1680732 x b)). Qed.
Lemma lem1680734 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680735 (b : real) : (term147 b) = (term147 b).
Proof. exact (MK_COMB (@lem1680734) (@lem1680733 b)). Qed.
Lemma lem1680736 : term148 = term148.
Proof. exact (fun_ext (fun b : real => @lem1680735 b)). Qed.
Lemma lem1680737 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680738 : term119 = term119.
Proof. exact (MK_COMB (@lem1680737) (@lem1680736)). Qed.
Lemma lem1680739 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1680740 : term131 = term131.
Proof. exact (MK_COMB (@lem1680739) (@lem1680738)). Qed.
Lemma lem1680745 (u : real) (v : real) (a : real) : (term1 u v a) = (term1 u v a).
Proof. exact (eq_refl (term1 u v a)). Qed.
Lemma lem1680746 (u : real) (v : real) : (term149 u v) = (term149 u v).
Proof. exact (fun_ext (fun a : real => @lem1680745 u v a)). Qed.
Lemma lem1680747 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680748 (u : real) (v : real) : (term120 u v) = (term120 u v).
Proof. exact (MK_COMB (@lem1680747) (@lem1680746 u v)). Qed.
Lemma lem1680749 (u : real) : (term150 u) = (term150 u).
Proof. exact (fun_ext (fun v : real => @lem1680748 u v)). Qed.
Lemma lem1680750 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680751 (u : real) : (term121 u) = (term121 u).
Proof. exact (MK_COMB (@lem1680750) (@lem1680749 u)). Qed.
Lemma lem1680752 : term151 = term151.
Proof. exact (fun_ext (fun u : real => @lem1680751 u)). Qed.
Lemma lem1680753 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680754 : term122 = term122.
Proof. exact (MK_COMB (@lem1680753) (@lem1680752)). Qed.
Lemma lem1680755 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1680756 : term132 = term132.
Proof. exact (MK_COMB (@lem1680755) (@lem1680754)). Qed.
Lemma lem1680757 : term134 = term134.
Proof. exact (MK_COMB (@lem1680756) (@lem1680740)). Qed.
Lemma lem1680778 (a : real) (u : real) (x : real) (v : real) (y : real) : (term152 a u x v y) = (term152 a u x v y).
Proof. exact (eq_refl (term152 a u x v y)). Qed.
Lemma lem1680779 (a : real) (u : real) (x : real) (y : real) : (term153 a u x y) = (term153 a u x y).
Proof. exact (fun_ext (fun v : real => @lem1680778 a u x v y)). Qed.
Lemma lem1680780 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680781 (a : real) (u : real) (x : real) (y : real) : (term154 a u x y) = (term154 a u x y).
Proof. exact (MK_COMB (@lem1680780) (@lem1680779 a u x y)). Qed.
Lemma lem1680782 (a : real) (x : real) (y : real) : (term155 a x y) = (term155 a x y).
Proof. exact (fun_ext (fun u : real => @lem1680781 a u x y)). Qed.
Lemma lem1680783 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680784 (a : real) (x : real) (y : real) : (term156 a x y) = (term156 a x y).
Proof. exact (MK_COMB (@lem1680783) (@lem1680782 a x y)). Qed.
Lemma lem1680785 (x : real) (y : real) : (term157 x y) = (term157 x y).
Proof. exact (fun_ext (fun a : real => @lem1680784 a x y)). Qed.
Lemma lem1680786 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680787 (x : real) (y : real) : (term158 x y) = (term158 x y).
Proof. exact (MK_COMB (@lem1680786) (@lem1680785 x y)). Qed.
Lemma lem1680788 (x : real) : (term159 x) = (term159 x).
Proof. exact (fun_ext (fun y : real => @lem1680787 x y)). Qed.
Lemma lem1680789 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680790 (x : real) : (term160 x) = (term160 x).
Proof. exact (MK_COMB (@lem1680789) (@lem1680788 x)). Qed.
Lemma lem1680791 : term161 = term161.
Proof. exact (fun_ext (fun x : real => @lem1680790 x)). Qed.
Lemma lem1680792 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1680793 : term123 = term123.
Proof. exact (MK_COMB (@lem1680792) (@lem1680791)). Qed.
Lemma lem1680794 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1680795 : term125 = term125.
Proof. exact (MK_COMB (@lem1680794) (@lem1680793)). Qed.
Lemma lem1680796 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1680797 : term135 = term135.
Proof. exact (MK_COMB (@lem1680796) (@lem1680795)). Qed.
Lemma lem1680798 : term136 = term136.
Proof. exact (MK_COMB (@lem1680797) (@lem1680757)). Qed.
Lemma lem1680911 : term126 = term136.
Proof. exact (TRANS (@lem1680699) (@lem1680798)). Qed.
Lemma lem1680912 : term136 = term126.
Proof. exact (SYM (@lem1680911)). Qed.
Lemma lem1680913 (h1 : term125) : term125.
Proof. exact (h1). Qed.
Lemma lem1680914 (h1 : term122) : term122.
Proof. exact (h1). Qed.
Lemma lem1680915 (h1 : term119) : term119.
Proof. exact (h1). Qed.
Lemma lem1680938 (a : real) (u : real) (x : real) (v : real) (y : real) : (term162 a u x v y) = (term163 a u x v y).
Proof. exact (@lem17362 (term164 x a y u v) (term165 a u x v y)). Qed.
Lemma lem1680939 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1680940 (a : real) (u : real) (x : real) (y : real) : (term168 a u x y) = (term169 a u x y).
Proof. exact (@lem1680939 (term153 a u x y)). Qed.
Lemma lem1680941 (a : real) (u : real) (x : real) (v : real) (y : real) : (term170 a u x y v) = (term152 a u x v y).
Proof. exact (eq_refl (term170 a u x y v)). Qed.
Lemma lem1680942 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1680943 (a : real) (u : real) (x : real) (v : real) (y : real) : (term171 a u x y v) = (term162 a u x v y).
Proof. exact (MK_COMB (@lem1680942) (@lem1680941 a u x v y)). Qed.
Lemma lem1680944 (a : real) (u : real) (x : real) (v : real) (y : real) : (term171 a u x y v) = (term163 a u x v y).
Proof. exact (TRANS (@lem1680943 a u x v y) (@lem1680938 a u x v y)). Qed.
Lemma lem1680945 (a : real) (u : real) (x : real) (y : real) : (term172 a u x y) = (term173 a u x y).
Proof. exact (fun_ext (fun v : real => @lem1680944 a u x v y)). Qed.
Lemma lem1680946 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1680947 (a : real) (u : real) (x : real) (y : real) : (term169 a u x y) = (term174 a u x y).
Proof. exact (MK_COMB (@lem1680946) (@lem1680945 a u x y)). Qed.
Lemma lem1680948 (a : real) (u : real) (x : real) (y : real) : (term168 a u x y) = (term174 a u x y).
Proof. exact (TRANS (@lem1680940 a u x y) (@lem1680947 a u x y)). Qed.
Lemma lem1680949 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1680950 (a : real) (x : real) (y : real) : (term175 a x y) = (term176 a x y).
Proof. exact (@lem1680949 (term155 a x y)). Qed.
Lemma lem1680951 (a : real) (u : real) (x : real) (y : real) : (term177 a x y u) = (term154 a u x y).
Proof. exact (eq_refl (term177 a x y u)). Qed.
Lemma lem1680952 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1680953 (a : real) (u : real) (x : real) (y : real) : (term178 a x y u) = (term168 a u x y).
Proof. exact (MK_COMB (@lem1680952) (@lem1680951 a u x y)). Qed.
Lemma lem1680954 (a : real) (u : real) (x : real) (y : real) : (term178 a x y u) = (term174 a u x y).
Proof. exact (TRANS (@lem1680953 a u x y) (@lem1680948 a u x y)). Qed.
Lemma lem1680955 (a : real) (x : real) (y : real) : (term179 a x y) = (term180 a x y).
Proof. exact (fun_ext (fun u : real => @lem1680954 a u x y)). Qed.
Lemma lem1680956 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1680957 (a : real) (x : real) (y : real) : (term176 a x y) = (term181 a x y).
Proof. exact (MK_COMB (@lem1680956) (@lem1680955 a x y)). Qed.
Lemma lem1680958 (a : real) (x : real) (y : real) : (term175 a x y) = (term181 a x y).
Proof. exact (TRANS (@lem1680950 a x y) (@lem1680957 a x y)). Qed.
Lemma lem1680959 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1680960 (x : real) (y : real) : (term182 x y) = (term183 x y).
Proof. exact (@lem1680959 (term157 x y)). Qed.
Lemma lem1680961 (a : real) (x : real) (y : real) : (term184 x y a) = (term156 a x y).
Proof. exact (eq_refl (term184 x y a)). Qed.
Lemma lem1680962 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1680963 (a : real) (x : real) (y : real) : (term185 x y a) = (term175 a x y).
Proof. exact (MK_COMB (@lem1680962) (@lem1680961 a x y)). Qed.
Lemma lem1680964 (a : real) (x : real) (y : real) : (term185 x y a) = (term181 a x y).
Proof. exact (TRANS (@lem1680963 a x y) (@lem1680958 a x y)). Qed.
Lemma lem1680965 (x : real) (y : real) : (term186 x y) = (term187 x y).
Proof. exact (fun_ext (fun a : real => @lem1680964 a x y)). Qed.
Lemma lem1680966 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1680967 (x : real) (y : real) : (term183 x y) = (term188 x y).
Proof. exact (MK_COMB (@lem1680966) (@lem1680965 x y)). Qed.
Lemma lem1680968 (x : real) (y : real) : (term182 x y) = (term188 x y).
Proof. exact (TRANS (@lem1680960 x y) (@lem1680967 x y)). Qed.
Lemma lem1680969 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1680970 (x : real) : (term189 x) = (term190 x).
Proof. exact (@lem1680969 (term159 x)). Qed.
Lemma lem1680971 (x : real) (y : real) : (term191 x y) = (term158 x y).
Proof. exact (eq_refl (term191 x y)). Qed.
Lemma lem1680972 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1680973 (x : real) (y : real) : (term192 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1680972) (@lem1680971 x y)). Qed.
Lemma lem1680974 (x : real) (y : real) : (term192 x y) = (term188 x y).
Proof. exact (TRANS (@lem1680973 x y) (@lem1680968 x y)). Qed.
Lemma lem1680975 (x : real) : (term193 x) = (term194 x).
Proof. exact (fun_ext (fun y : real => @lem1680974 x y)). Qed.
Lemma lem1680976 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1680977 (x : real) : (term190 x) = (term195 x).
Proof. exact (MK_COMB (@lem1680976) (@lem1680975 x)). Qed.
Lemma lem1680978 (x : real) : (term189 x) = (term195 x).
Proof. exact (TRANS (@lem1680970 x) (@lem1680977 x)). Qed.
Lemma lem1680979 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1680980 : term125 = term196.
Proof. exact (@lem1680979 term161). Qed.
Lemma lem1680981 (x : real) : (term197 x) = (term160 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem1680982 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1680983 (x : real) : (term198 x) = (term189 x).
Proof. exact (MK_COMB (@lem1680982) (@lem1680981 x)). Qed.
Lemma lem1680984 (x : real) : (term198 x) = (term195 x).
Proof. exact (TRANS (@lem1680983 x) (@lem1680978 x)). Qed.
Lemma lem1680985 : term199 = term200.
Proof. exact (fun_ext (fun x : real => @lem1680984 x)). Qed.
Lemma lem1680986 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1680987 : term196 = term201.
Proof. exact (MK_COMB (@lem1680986) (@lem1680985)). Qed.
Lemma lem1681056 : term125 = term201.
Proof. exact (TRANS (@lem1680980) (@lem1680987)). Qed.
Lemma lem1681057 (h1 : term125) : term201.
Proof. exact (EQ_MP (@lem1681056) (@lem1680913 h1)). Qed.
Lemma lem1681064 (u : real) (v : real) (a : real) : (term1 u v a) = (term202 u v a).
Proof. exact (@lem17265 ((real_add u v) = term39) ((term31 u v a) = a)). Qed.
Lemma lem1681065 (u : real) (v : real) : (term149 u v) = (term203 u v).
Proof. exact (fun_ext (fun a : real => @lem1681064 u v a)). Qed.
Lemma lem1681066 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681067 (u : real) (v : real) : (term120 u v) = (term204 u v).
Proof. exact (MK_COMB (@lem1681066) (@lem1681065 u v)). Qed.
Lemma lem1681068 (u : real) : (term150 u) = (term205 u).
Proof. exact (fun_ext (fun v : real => @lem1681067 u v)). Qed.
Lemma lem1681069 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681070 (u : real) : (term121 u) = (term206 u).
Proof. exact (MK_COMB (@lem1681069) (@lem1681068 u)). Qed.
Lemma lem1681071 : term151 = term207.
Proof. exact (fun_ext (fun u : real => @lem1681070 u)). Qed.
Lemma lem1681072 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681073 : term122 = term208.
Proof. exact (MK_COMB (@lem1681072) (@lem1681071)). Qed.
Lemma lem1681083 {A : Type'} (P : Prop) (Q : A -> Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem1681084 (P : Prop) (Q : real -> Prop) : (term211 P Q) = (term212 P Q).
Proof. exact (@lem1681083 real P Q). Qed.
Lemma lem1681085 (u : real) (v : real) : (term213 u v) = (term214 u v).
Proof. exact (@lem1681084 (term52 u v) (term215 u v)). Qed.
Lemma lem1681086 (u : real) (v : real) (a : real) : (term216 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term216 u v a)). Qed.
Lemma lem1681087 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1681088 (u : real) (v : real) (a : real) : (term218 u v a) = (term202 u v a).
Proof. exact (MK_COMB (@lem1681087 u v) (@lem1681086 u v a)). Qed.
Lemma lem1681089 (u : real) (v : real) : (term219 u v) = (term203 u v).
Proof. exact (fun_ext (fun a : real => @lem1681088 u v a)). Qed.
Lemma lem1681090 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681091 (u : real) (v : real) : (term213 u v) = (term204 u v).
Proof. exact (MK_COMB (@lem1681090) (@lem1681089 u v)). Qed.
Lemma lem1681092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1681093 (u : real) (v : real) : (term220 u v) = (term221 u v).
Proof. exact (MK_COMB (@lem1681092) (@lem1681091 u v)). Qed.
Lemma lem1681094 (u : real) (v : real) (a : real) : (term216 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term216 u v a)). Qed.
Lemma lem1681095 (u : real) (v : real) : (term222 u v) = (term215 u v).
Proof. exact (fun_ext (fun a : real => @lem1681094 u v a)). Qed.
Lemma lem1681096 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681097 (u : real) (v : real) : (term223 u v) = (term224 u v).
Proof. exact (MK_COMB (@lem1681096) (@lem1681095 u v)). Qed.
Lemma lem1681098 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1681099 (u : real) (v : real) : (term214 u v) = (term225 u v).
Proof. exact (MK_COMB (@lem1681098 u v) (@lem1681097 u v)). Qed.
Lemma lem1681100 (u : real) (v : real) : ((term213 u v) = (term214 u v)) = ((term204 u v) = (term225 u v)).
Proof. exact (MK_COMB (@lem1681093 u v) (@lem1681099 u v)). Qed.
Lemma lem1681101 (u : real) (v : real) : (term204 u v) = (term225 u v).
Proof. exact (EQ_MP (@lem1681100 u v) (@lem1681085 u v)). Qed.
Lemma lem1681106 (u : real) : (term205 u) = (term226 u).
Proof. exact (fun_ext (fun v : real => @lem1681101 u v)). Qed.
Lemma lem1681107 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681108 (u : real) : (term206 u) = (term227 u).
Proof. exact (MK_COMB (@lem1681107) (@lem1681106 u)). Qed.
Lemma lem1681157 : term207 = term228.
Proof. exact (fun_ext (fun u : real => @lem1681108 u)). Qed.
Lemma lem1681158 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681165 : term208 = term229.
Proof. exact (MK_COMB (@lem1681158) (@lem1681157)). Qed.
Lemma lem1681166 : term122 = term229.
Proof. exact (TRANS (@lem1681073) (@lem1681165)). Qed.
Lemma lem1681167 (h1 : term122) : term229.
Proof. exact (EQ_MP (@lem1681166) (@lem1680914 h1)). Qed.
Lemma lem1681177 (u : real) (v : real) : (term230 u v) = (term231 u v).
Proof. exact (@lem17045 (term232 v) ((real_add u v) = term39)). Qed.
Lemma lem1681179 (u : real) : (term233 u) = (term233 u).
Proof. exact (eq_refl (term233 u)). Qed.
Lemma lem1681180 (u : real) (v : real) : (term234 u v) = (term235 u v).
Proof. exact (MK_COMB (@lem1681179 u) (@lem1681177 u v)). Qed.
Lemma lem1681181 (u : real) (v : real) : (term236 u v) = (term234 u v).
Proof. exact (@lem17045 (term232 u) (term237 u v)). Qed.
Lemma lem1681182 (u : real) (v : real) : (term236 u v) = (term235 u v).
Proof. exact (TRANS (@lem1681181 u v) (@lem1681180 u v)). Qed.
Lemma lem1681184 (y : real) (b : real) : (term238 y b) = (term238 y b).
Proof. exact (eq_refl (term238 y b)). Qed.
Lemma lem1681185 (y : real) (b : real) (u : real) (v : real) : (term239 y b u v) = (term240 y b u v).
Proof. exact (MK_COMB (@lem1681184 y b) (@lem1681182 u v)). Qed.
Lemma lem1681186 (y : real) (b : real) (u : real) (v : real) : (term241 y b u v) = (term239 y b u v).
Proof. exact (@lem17045 (real_lt y b) (term242 u v)). Qed.
Lemma lem1681187 (y : real) (b : real) (u : real) (v : real) : (term241 y b u v) = (term240 y b u v).
Proof. exact (TRANS (@lem1681186 y b u v) (@lem1681185 y b u v)). Qed.
Lemma lem1681189 (x : real) (a : real) : (term238 x a) = (term238 x a).
Proof. exact (eq_refl (term238 x a)). Qed.
Lemma lem1681190 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term243 x a y b u v) = (term244 x a y b u v).
Proof. exact (MK_COMB (@lem1681189 x a) (@lem1681187 y b u v)). Qed.
Lemma lem1681191 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term245 x a y b u v) = (term243 x a y b u v).
Proof. exact (@lem17045 (real_lt x a) (term246 y b u v)). Qed.
Lemma lem1681192 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term245 x a y b u v) = (term244 x a y b u v).
Proof. exact (TRANS (@lem1681191 x a y b u v) (@lem1681190 x a y b u v)). Qed.
Lemma lem1681193 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term247 x y u a v b) = (term247 x y u a v b).
Proof. exact (eq_refl (term247 x y u a v b)). Qed.
Lemma lem1681194 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1681195 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term248 x a y b u v) = (term249 x a y b u v).
Proof. exact (MK_COMB (@lem1681194) (@lem1681192 x a y b u v)). Qed.
Lemma lem1681196 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term250 x y u a v b) = (term251 x y u a v b).
Proof. exact (MK_COMB (@lem1681195 x a y b u v) (@lem1681193 x y u a v b)). Qed.
Lemma lem1681197 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term250 x y u a v b).
Proof. exact (@lem17265 (term252 x a y b u v) (term247 x y u a v b)). Qed.
Lemma lem1681198 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term251 x y u a v b).
Proof. exact (TRANS (@lem1681197 x y u a v b) (@lem1681196 x y u a v b)). Qed.
Lemma lem1681199 (x : real) (y : real) (u : real) (a : real) (b : real) : (term138 x y u a b) = (term253 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1681198 x y u a v b)). Qed.
Lemma lem1681200 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681201 (x : real) (y : real) (u : real) (a : real) (b : real) : (term139 x y u a b) = (term254 x y u a b).
Proof. exact (MK_COMB (@lem1681200) (@lem1681199 x y u a b)). Qed.
Lemma lem1681202 (x : real) (y : real) (a : real) (b : real) : (term140 x y a b) = (term255 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1681201 x y u a b)). Qed.
Lemma lem1681203 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681204 (x : real) (y : real) (a : real) (b : real) : (term141 x y a b) = (term256 x y a b).
Proof. exact (MK_COMB (@lem1681203) (@lem1681202 x y a b)). Qed.
Lemma lem1681205 (x : real) (y : real) (b : real) : (term142 x y b) = (term257 x y b).
Proof. exact (fun_ext (fun a : real => @lem1681204 x y a b)). Qed.
Lemma lem1681206 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681207 (x : real) (y : real) (b : real) : (term143 x y b) = (term258 x y b).
Proof. exact (MK_COMB (@lem1681206) (@lem1681205 x y b)). Qed.
Lemma lem1681208 (x : real) (b : real) : (term144 x b) = (term259 x b).
Proof. exact (fun_ext (fun y : real => @lem1681207 x y b)). Qed.
Lemma lem1681209 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681210 (x : real) (b : real) : (term145 x b) = (term260 x b).
Proof. exact (MK_COMB (@lem1681209) (@lem1681208 x b)). Qed.
Lemma lem1681211 (b : real) : (term146 b) = (term261 b).
Proof. exact (fun_ext (fun x : real => @lem1681210 x b)). Qed.
Lemma lem1681212 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681213 (b : real) : (term147 b) = (term262 b).
Proof. exact (MK_COMB (@lem1681212) (@lem1681211 b)). Qed.
Lemma lem1681214 : term148 = term263.
Proof. exact (fun_ext (fun b : real => @lem1681213 b)). Qed.
Lemma lem1681215 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681288 : term119 = term264.
Proof. exact (MK_COMB (@lem1681215) (@lem1681214)). Qed.
Lemma lem1681289 (h1 : term119) : term264.
Proof. exact (EQ_MP (@lem1681288) (@lem1680915 h1)). Qed.
Lemma lem1681290 (x : real) (h1 : term195 x) : term195 x.
Proof. exact (h1). Qed.
Lemma lem1681291 (x : real) (y : real) (h1 : term188 x y) : term188 x y.
Proof. exact (h1). Qed.
Lemma lem1681292 (a : real) (x : real) (y : real) (h1 : term181 a x y) : term181 a x y.
Proof. exact (h1). Qed.
Lemma lem1681293 (a : real) (u : real) (x : real) (y : real) (h1 : term174 a u x y) : term174 a u x y.
Proof. exact (h1). Qed.
Lemma lem1681311 (u : real) (v : real) (a : real) : ((term31 u v a) = a) = ((term31 u v a) = a).
Proof. exact (eq_refl ((term31 u v a) = a)). Qed.
Lemma lem1681312 (u : real) (v : real) : (term215 u v) = (term215 u v).
Proof. exact (fun_ext (fun a : real => @lem1681311 u v a)). Qed.
Lemma lem1681313 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681314 (u : real) (v : real) : (term224 u v) = (term224 u v).
Proof. exact (MK_COMB (@lem1681313) (@lem1681312 u v)). Qed.
Lemma lem1681333 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1681334 (u : real) (v : real) : (term225 u v) = (term225 u v).
Proof. exact (MK_COMB (@lem1681333 u v) (@lem1681314 u v)). Qed.
Lemma lem1681335 (u : real) : (term226 u) = (term226 u).
Proof. exact (fun_ext (fun v : real => @lem1681334 u v)). Qed.
Lemma lem1681336 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681337 (u : real) : (term227 u) = (term227 u).
Proof. exact (MK_COMB (@lem1681336) (@lem1681335 u)). Qed.
Lemma lem1681338 : term228 = term228.
Proof. exact (fun_ext (fun u : real => @lem1681337 u)). Qed.
Lemma lem1681339 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681340 : term229 = term229.
Proof. exact (MK_COMB (@lem1681339) (@lem1681338)). Qed.
Lemma lem1681341 (h1 : term122) : term229.
Proof. exact (EQ_MP (@lem1681340) (@lem1681167 h1)). Qed.
Lemma lem1681438 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term251 x y u a v b) = (term251 x y u a v b).
Proof. exact (eq_refl (term251 x y u a v b)). Qed.
Lemma lem1681439 (x : real) (y : real) (u : real) (a : real) (b : real) : (term253 x y u a b) = (term253 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1681438 x y u a v b)). Qed.
Lemma lem1681440 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681441 (x : real) (y : real) (u : real) (a : real) (b : real) : (term254 x y u a b) = (term254 x y u a b).
Proof. exact (MK_COMB (@lem1681440) (@lem1681439 x y u a b)). Qed.
Lemma lem1681442 (x : real) (y : real) (a : real) (b : real) : (term255 x y a b) = (term255 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1681441 x y u a b)). Qed.
Lemma lem1681443 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681444 (x : real) (y : real) (a : real) (b : real) : (term256 x y a b) = (term256 x y a b).
Proof. exact (MK_COMB (@lem1681443) (@lem1681442 x y a b)). Qed.
Lemma lem1681445 (x : real) (y : real) (b : real) : (term257 x y b) = (term257 x y b).
Proof. exact (fun_ext (fun a : real => @lem1681444 x y a b)). Qed.
Lemma lem1681446 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681447 (x : real) (y : real) (b : real) : (term258 x y b) = (term258 x y b).
Proof. exact (MK_COMB (@lem1681446) (@lem1681445 x y b)). Qed.
Lemma lem1681448 (x : real) (b : real) : (term259 x b) = (term259 x b).
Proof. exact (fun_ext (fun y : real => @lem1681447 x y b)). Qed.
Lemma lem1681449 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681450 (x : real) (b : real) : (term260 x b) = (term260 x b).
Proof. exact (MK_COMB (@lem1681449) (@lem1681448 x b)). Qed.
Lemma lem1681451 (b : real) : (term261 b) = (term261 b).
Proof. exact (fun_ext (fun x : real => @lem1681450 x b)). Qed.
Lemma lem1681452 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681453 (b : real) : (term262 b) = (term262 b).
Proof. exact (MK_COMB (@lem1681452) (@lem1681451 b)). Qed.
Lemma lem1681454 : term263 = term263.
Proof. exact (fun_ext (fun b : real => @lem1681453 b)). Qed.
Lemma lem1681455 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681456 : term264 = term264.
Proof. exact (MK_COMB (@lem1681455) (@lem1681454)). Qed.
Lemma lem1681457 (h1 : term119) : term264.
Proof. exact (EQ_MP (@lem1681456) (@lem1681289 h1)). Qed.
Lemma lem1681535 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term163 a u x v y.
Proof. exact (h1). Qed.
Lemma lem1681537 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term164 x a y u v.
Proof. exact (proj1 (@lem1681535 a u x v y h1)). Qed.
Lemma lem1681538 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term246 a y u v.
Proof. exact (proj2 (@lem1681537 a u x v y h1)). Qed.
Lemma lem1681540 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term242 u v.
Proof. exact (proj2 (@lem1681538 a u x v y h1)). Qed.
Lemma lem1681542 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term237 u v.
Proof. exact (proj2 (@lem1681540 a u x v y h1)). Qed.
Lemma lem1681547 {A : Type'} (P : Prop) (Q : A -> Prop) : (term210 A P Q) = (term209 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1681548 (P : Prop) (Q : real -> Prop) : (term212 P Q) = (term211 P Q).
Proof. exact (@lem1681547 real P Q). Qed.
Lemma lem1681549 (u : real) (v : real) : (term214 u v) = (term213 u v).
Proof. exact (@lem1681548 (term52 u v) (term215 u v)). Qed.
Lemma lem1681550 (u : real) (v : real) (a : real) : (term216 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term216 u v a)). Qed.
Lemma lem1681551 (u : real) (v : real) : (term222 u v) = (term215 u v).
Proof. exact (fun_ext (fun a : real => @lem1681550 u v a)). Qed.
Lemma lem1681552 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681553 (u : real) (v : real) : (term223 u v) = (term224 u v).
Proof. exact (MK_COMB (@lem1681552) (@lem1681551 u v)). Qed.
Lemma lem1681554 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1681555 (u : real) (v : real) : (term214 u v) = (term225 u v).
Proof. exact (MK_COMB (@lem1681554 u v) (@lem1681553 u v)). Qed.
Lemma lem1681556 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1681557 (u : real) (v : real) : (term265 u v) = (term266 u v).
Proof. exact (MK_COMB (@lem1681556) (@lem1681555 u v)). Qed.
Lemma lem1681558 (u : real) (v : real) (a : real) : (term216 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term216 u v a)). Qed.
Lemma lem1681559 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1681560 (u : real) (v : real) (a : real) : (term218 u v a) = (term202 u v a).
Proof. exact (MK_COMB (@lem1681559 u v) (@lem1681558 u v a)). Qed.
Lemma lem1681561 (u : real) (v : real) : (term219 u v) = (term203 u v).
Proof. exact (fun_ext (fun a : real => @lem1681560 u v a)). Qed.
Lemma lem1681562 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681563 (u : real) (v : real) : (term213 u v) = (term204 u v).
Proof. exact (MK_COMB (@lem1681562) (@lem1681561 u v)). Qed.
Lemma lem1681564 (u : real) (v : real) : ((term214 u v) = (term213 u v)) = ((term225 u v) = (term204 u v)).
Proof. exact (MK_COMB (@lem1681557 u v) (@lem1681563 u v)). Qed.
Lemma lem1681565 (u : real) (v : real) : (term225 u v) = (term204 u v).
Proof. exact (EQ_MP (@lem1681564 u v) (@lem1681549 u v)). Qed.
Lemma lem1681566 (u : real) : (term226 u) = (term205 u).
Proof. exact (fun_ext (fun v : real => @lem1681565 u v)). Qed.
Lemma lem1681567 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681568 (u : real) : (term227 u) = (term206 u).
Proof. exact (MK_COMB (@lem1681567) (@lem1681566 u)). Qed.
Lemma lem1681569 : term228 = term207.
Proof. exact (fun_ext (fun u : real => @lem1681568 u)). Qed.
Lemma lem1681570 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681571 : term229 = term208.
Proof. exact (MK_COMB (@lem1681570) (@lem1681569)). Qed.
Lemma lem1681578 (u : real) (v : real) (a : real) : (term202 u v a) = (term202 u v a).
Proof. exact (eq_refl (term202 u v a)). Qed.
Lemma lem1681579 (u : real) (v : real) : (term203 u v) = (term203 u v).
Proof. exact (fun_ext (fun a : real => @lem1681578 u v a)). Qed.
Lemma lem1681580 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681581 (u : real) (v : real) : (term204 u v) = (term204 u v).
Proof. exact (MK_COMB (@lem1681580) (@lem1681579 u v)). Qed.
Lemma lem1681582 (u : real) : (term205 u) = (term205 u).
Proof. exact (fun_ext (fun v : real => @lem1681581 u v)). Qed.
Lemma lem1681583 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681584 (u : real) : (term206 u) = (term206 u).
Proof. exact (MK_COMB (@lem1681583) (@lem1681582 u)). Qed.
Lemma lem1681585 : term207 = term207.
Proof. exact (fun_ext (fun u : real => @lem1681584 u)). Qed.
Lemma lem1681586 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681587 : term208 = term208.
Proof. exact (MK_COMB (@lem1681586) (@lem1681585)). Qed.
Lemma lem1681588 : term229 = term208.
Proof. exact (TRANS (@lem1681571) (@lem1681587)). Qed.
Lemma lem1681589 (h1 : term122) : term208.
Proof. exact (EQ_MP (@lem1681588) (@lem1681341 h1)). Qed.
Lemma lem1681621 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term251 x y u a v b) = (term251 x y u a v b).
Proof. exact (eq_refl (term251 x y u a v b)). Qed.
Lemma lem1681622 (x : real) (y : real) (u : real) (a : real) (b : real) : (term253 x y u a b) = (term253 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1681621 x y u a v b)). Qed.
Lemma lem1681623 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681624 (x : real) (y : real) (u : real) (a : real) (b : real) : (term254 x y u a b) = (term254 x y u a b).
Proof. exact (MK_COMB (@lem1681623) (@lem1681622 x y u a b)). Qed.
Lemma lem1681625 (x : real) (y : real) (a : real) (b : real) : (term255 x y a b) = (term255 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1681624 x y u a b)). Qed.
Lemma lem1681626 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681627 (x : real) (y : real) (a : real) (b : real) : (term256 x y a b) = (term256 x y a b).
Proof. exact (MK_COMB (@lem1681626) (@lem1681625 x y a b)). Qed.
Lemma lem1681628 (x : real) (y : real) (b : real) : (term257 x y b) = (term257 x y b).
Proof. exact (fun_ext (fun a : real => @lem1681627 x y a b)). Qed.
Lemma lem1681629 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681630 (x : real) (y : real) (b : real) : (term258 x y b) = (term258 x y b).
Proof. exact (MK_COMB (@lem1681629) (@lem1681628 x y b)). Qed.
Lemma lem1681631 (x : real) (b : real) : (term259 x b) = (term259 x b).
Proof. exact (fun_ext (fun y : real => @lem1681630 x y b)). Qed.
Lemma lem1681632 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681633 (x : real) (b : real) : (term260 x b) = (term260 x b).
Proof. exact (MK_COMB (@lem1681632) (@lem1681631 x b)). Qed.
Lemma lem1681634 (b : real) : (term261 b) = (term261 b).
Proof. exact (fun_ext (fun x : real => @lem1681633 x b)). Qed.
Lemma lem1681635 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681636 (b : real) : (term262 b) = (term262 b).
Proof. exact (MK_COMB (@lem1681635) (@lem1681634 b)). Qed.
Lemma lem1681637 : term263 = term263.
Proof. exact (fun_ext (fun b : real => @lem1681636 b)). Qed.
Lemma lem1681638 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1681640 : term264 = term264.
Proof. exact (MK_COMB (@lem1681638) (@lem1681637)). Qed.
Lemma lem1681641 (h1 : term119) : term264.
Proof. exact (EQ_MP (@lem1681640) (@lem1681457 h1)). Qed.
Lemma lem1681666 (_25929 : real) (h1 : term122) : term267 _25929.
Proof. exact (@lem1681589 h1 _25929). Qed.
Lemma lem1681667 (_25929 : real) : (term267 _25929) = (term206 _25929).
Proof. exact (eq_refl (term267 _25929)). Qed.
Lemma lem1681668 (_25929 : real) (h1 : term122) : term206 _25929.
Proof. exact (EQ_MP (@lem1681667 _25929) (@lem1681666 _25929 h1)). Qed.
Lemma lem1681669 (_25929 : real) (_25930 : real) (h1 : term122) : term268 _25929 _25930.
Proof. exact (@lem1681668 _25929 h1 _25930). Qed.
Lemma lem1681670 (_25929 : real) (_25930 : real) : (term268 _25929 _25930) = (term204 _25929 _25930).
Proof. exact (eq_refl (term268 _25929 _25930)). Qed.
Lemma lem1681671 (_25929 : real) (_25930 : real) (h1 : term122) : term204 _25929 _25930.
Proof. exact (EQ_MP (@lem1681670 _25929 _25930) (@lem1681669 _25929 _25930 h1)). Qed.
Lemma lem1681672 (_25929 : real) (_25930 : real) (_25931 : real) (h1 : term122) : term269 _25929 _25930 _25931.
Proof. exact (@lem1681671 _25929 _25930 h1 _25931). Qed.
Lemma lem1681673 (_25929 : real) (_25930 : real) (_25931 : real) : (term269 _25929 _25930 _25931) = (term202 _25929 _25930 _25931).
Proof. exact (eq_refl (term269 _25929 _25930 _25931)). Qed.
Lemma lem1681675 (_25932 : real) (h1 : term119) : term270 _25932.
Proof. exact (@lem1681641 h1 _25932). Qed.
Lemma lem1681676 (_25932 : real) : (term270 _25932) = (term262 _25932).
Proof. exact (eq_refl (term270 _25932)). Qed.
Lemma lem1681677 (_25932 : real) (h1 : term119) : term262 _25932.
Proof. exact (EQ_MP (@lem1681676 _25932) (@lem1681675 _25932 h1)). Qed.
Lemma lem1681678 (_25932 : real) (_25933 : real) (h1 : term119) : term271 _25932 _25933.
Proof. exact (@lem1681677 _25932 h1 _25933). Qed.
Lemma lem1681679 (_25933 : real) (_25932 : real) : (term271 _25932 _25933) = (term260 _25933 _25932).
Proof. exact (eq_refl (term271 _25932 _25933)). Qed.
Lemma lem1681680 (_25933 : real) (_25932 : real) (h1 : term119) : term260 _25933 _25932.
Proof. exact (EQ_MP (@lem1681679 _25933 _25932) (@lem1681678 _25932 _25933 h1)). Qed.
Lemma lem1681681 (_25933 : real) (_25932 : real) (_25934 : real) (h1 : term119) : term272 _25933 _25932 _25934.
Proof. exact (@lem1681680 _25933 _25932 h1 _25934). Qed.
Lemma lem1681682 (_25933 : real) (_25934 : real) (_25932 : real) : (term272 _25933 _25932 _25934) = (term258 _25933 _25934 _25932).
Proof. exact (eq_refl (term272 _25933 _25932 _25934)). Qed.
Lemma lem1681683 (_25933 : real) (_25934 : real) (_25932 : real) (h1 : term119) : term258 _25933 _25934 _25932.
Proof. exact (EQ_MP (@lem1681682 _25933 _25934 _25932) (@lem1681681 _25933 _25932 _25934 h1)). Qed.
Lemma lem1681684 (_25933 : real) (_25934 : real) (_25932 : real) (_25935 : real) (h1 : term119) : term273 _25933 _25934 _25932 _25935.
Proof. exact (@lem1681683 _25933 _25934 _25932 h1 _25935). Qed.
Lemma lem1681685 (_25933 : real) (_25934 : real) (_25935 : real) (_25932 : real) : (term273 _25933 _25934 _25932 _25935) = (term256 _25933 _25934 _25935 _25932).
Proof. exact (eq_refl (term273 _25933 _25934 _25932 _25935)). Qed.
Lemma lem1681686 (_25933 : real) (_25934 : real) (_25935 : real) (_25932 : real) (h1 : term119) : term256 _25933 _25934 _25935 _25932.
Proof. exact (EQ_MP (@lem1681685 _25933 _25934 _25935 _25932) (@lem1681684 _25933 _25934 _25932 _25935 h1)). Qed.
Lemma lem1681687 (_25933 : real) (_25934 : real) (_25935 : real) (_25932 : real) (_25936 : real) (h1 : term119) : term274 _25933 _25934 _25935 _25932 _25936.
Proof. exact (@lem1681686 _25933 _25934 _25935 _25932 h1 _25936). Qed.
Lemma lem1681688 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25932 : real) : (term274 _25933 _25934 _25935 _25932 _25936) = (term254 _25933 _25934 _25936 _25935 _25932).
Proof. exact (eq_refl (term274 _25933 _25934 _25935 _25932 _25936)). Qed.
Lemma lem1681689 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25932 : real) (h1 : term119) : term254 _25933 _25934 _25936 _25935 _25932.
Proof. exact (EQ_MP (@lem1681688 _25933 _25934 _25936 _25935 _25932) (@lem1681687 _25933 _25934 _25935 _25932 _25936 h1)). Qed.
Lemma lem1681690 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25932 : real) (_25937 : real) (h1 : term119) : term275 _25933 _25934 _25936 _25935 _25932 _25937.
Proof. exact (@lem1681689 _25933 _25934 _25936 _25935 _25932 h1 _25937). Qed.
Lemma lem1681691 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term275 _25933 _25934 _25936 _25935 _25932 _25937) = (term251 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (eq_refl (term275 _25933 _25934 _25936 _25935 _25932 _25937)). Qed.
Lemma lem1681692 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) (h1 : term119) : term251 _25933 _25934 _25936 _25935 _25937 _25932.
Proof. exact (EQ_MP (@lem1681691 _25933 _25934 _25936 _25935 _25937 _25932) (@lem1681690 _25933 _25934 _25936 _25935 _25932 _25937 h1)). Qed.
Lemma lem1681698 (_25929 : real) (_25930 : real) (_25931 : real) (h1 : term122) : term202 _25929 _25930 _25931.
Proof. exact (EQ_MP (@lem1681673 _25929 _25930 _25931) (@lem1681672 _25929 _25930 _25931 h1)). Qed.
Lemma lem1681702 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term251 _25933 _25934 _25936 _25935 _25937 _25932) = (term276 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (@lem1680578 (term277 _25933 _25935) (term240 _25934 _25932 _25936 _25937) (term247 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1681703 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term278 _25933 _25934 _25936 _25935 _25937 _25932) = (term279 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (@lem1680578 (term277 _25934 _25932) (term235 _25936 _25937) (term247 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1681704 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term280 _25933 _25934 _25936 _25935 _25937 _25932) = (term281 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (@lem1680578 (term282 _25936) (term231 _25936 _25937) (term247 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1681711 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term283 _25933 _25934 _25936 _25935 _25937 _25932) = (term284 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (@lem1680578 (term282 _25937) (term52 _25936 _25937) (term247 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1681712 (_25936 : real) : (term233 _25936) = (term233 _25936).
Proof. exact (eq_refl (term233 _25936)). Qed.
Lemma lem1681715 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term281 _25933 _25934 _25936 _25935 _25937 _25932) = (term285 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (MK_COMB (@lem1681712 _25936) (@lem1681711 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1681716 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term280 _25933 _25934 _25936 _25935 _25937 _25932) = (term285 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (TRANS (@lem1681704 _25933 _25934 _25936 _25935 _25937 _25932) (@lem1681715 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1681717 (_25934 : real) (_25932 : real) : (term238 _25934 _25932) = (term238 _25934 _25932).
Proof. exact (eq_refl (term238 _25934 _25932)). Qed.
Lemma lem1681720 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term279 _25933 _25934 _25936 _25935 _25937 _25932) = (term286 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (MK_COMB (@lem1681717 _25934 _25932) (@lem1681716 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1681721 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term278 _25933 _25934 _25936 _25935 _25937 _25932) = (term286 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (TRANS (@lem1681703 _25933 _25934 _25936 _25935 _25937 _25932) (@lem1681720 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1681722 (_25933 : real) (_25935 : real) : (term238 _25933 _25935) = (term238 _25933 _25935).
Proof. exact (eq_refl (term238 _25933 _25935)). Qed.
Lemma lem1681725 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term276 _25933 _25934 _25936 _25935 _25937 _25932) = (term287 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (MK_COMB (@lem1681722 _25933 _25935) (@lem1681721 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1681727 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term251 _25933 _25934 _25936 _25935 _25937 _25932) = (term287 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (TRANS (@lem1681702 _25933 _25934 _25936 _25935 _25937 _25932) (@lem1681725 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1681728 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) (h1 : term119) : term287 _25933 _25934 _25936 _25935 _25937 _25932.
Proof. exact (EQ_MP (@lem1681727 _25933 _25934 _25936 _25935 _25937 _25932) (@lem1681692 _25933 _25934 _25936 _25935 _25937 _25932 h1)). Qed.
Lemma lem1681730 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term288 a u x v y.
Proof. exact (proj2 (@lem1681535 a u x v y h1)). Qed.
Lemma lem1681760 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1681761 (_25942 : real) (_25944 : real) (h1 : _25942 = _25944) : _25942 = _25944.
Proof. exact (h1). Qed.
Lemma lem1681762 (_25943 : real) (_25945 : real) (h1 : _25943 = _25945) : _25943 = _25945.
Proof. exact (h1). Qed.
Lemma lem1681763 (_25942 : real) (_25944 : real) (h1 : _25942 = _25944) : (real_lt _25942) = (real_lt _25944).
Proof. exact (MK_COMB (@lem1681760) (@lem1681761 _25942 _25944 h1)). Qed.
Lemma lem1681764 (_25942 : real) (_25944 : real) (_25943 : real) (_25945 : real) (h1 : _25942 = _25944) (h2 : _25943 = _25945) : (real_lt _25942 _25943) = (real_lt _25944 _25945).
Proof. exact (MK_COMB (@lem1681763 _25942 _25944 h1) (@lem1681762 _25943 _25945 h2)). Qed.
Lemma lem1681766 (b : Prop) (a : Prop) : term289 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1681767 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : term290 _25944 _25945 _25942 _25943.
Proof. exact (@lem1681766 (real_lt _25944 _25945) (real_lt _25942 _25943)). Qed.
Lemma lem1681768 (_25942 : real) (_25944 : real) (_25943 : real) (_25945 : real) (h1 : _25942 = _25944) (h2 : _25943 = _25945) : term291 _25944 _25945 _25942 _25943.
Proof. exact (@lem1681767 _25944 _25945 _25942 _25943 (@lem1681764 _25942 _25944 _25943 _25945 h1 h2)). Qed.
Lemma lem1681769 (_25945 : real) (_25943 : real) (_25942 : real) (_25944 : real) (h1 : _25942 = _25944) : term292 _25944 _25945 _25942 _25943.
Proof. exact (fun h0 : _25943 = _25945 => @lem1681768 _25942 _25944 _25943 _25945 h1 h0). Qed.
Lemma lem1681771 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1681772 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : (term292 _25944 _25945 _25942 _25943) = (term293 _25944 _25945 _25942 _25943).
Proof. exact (@lem1681771 (_25943 = _25945) (term291 _25944 _25945 _25942 _25943)). Qed.
Lemma lem1681773 (_25945 : real) (_25943 : real) (_25942 : real) (_25944 : real) (h1 : _25942 = _25944) : term293 _25944 _25945 _25942 _25943.
Proof. exact (EQ_MP (@lem1681772 _25944 _25945 _25942 _25943) (@lem1681769 _25945 _25943 _25942 _25944 h1)). Qed.
Lemma lem1681774 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : term294 _25944 _25945 _25942 _25943.
Proof. exact (fun h0 : _25942 = _25944 => @lem1681773 _25945 _25943 _25942 _25944 h0). Qed.
Lemma lem1681776 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1681777 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : (term294 _25944 _25945 _25942 _25943) = (term295 _25944 _25945 _25942 _25943).
Proof. exact (@lem1681776 (_25942 = _25944) (term293 _25944 _25945 _25942 _25943)). Qed.
Lemma lem1681778 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : term295 _25944 _25945 _25942 _25943.
Proof. exact (EQ_MP (@lem1681777 _25944 _25945 _25942 _25943) (@lem1681774 _25944 _25945 _25942 _25943)). Qed.
Lemma lem1681838 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1681542 a u x v y h1)). Qed.
Lemma lem1681839 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1681838 a u x v y h1). Qed.
Lemma lem1681841 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1681842 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1681841 ((real_add u v) = term39)). Qed.
Lemma lem1681843 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1681842 u v) (@lem1681839 a u x v y h1)). Qed.
Lemma lem1681849 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1681850 (_25931 : real) (_25929 : real) (_25930 : real) : (term202 _25929 _25930 _25931) = (term296 _25931 _25929 _25930).
Proof. exact (@lem1681849 ((term31 _25929 _25930 _25931) = _25931) (term52 _25929 _25930)). Qed.
Lemma lem1681860 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1681861 (_25931 : real) (_25929 : real) (_25930 : real) : (term297 _25929 _25930 _25931) = (term298 _25931 _25929 _25930).
Proof. exact (MK_COMB (@lem1681860) (@lem1681850 _25931 _25929 _25930)). Qed.
Lemma lem1681871 (_25931 : real) (_25929 : real) (_25930 : real) : (term296 _25931 _25929 _25930) = (term296 _25931 _25929 _25930).
Proof. exact (eq_refl (term296 _25931 _25929 _25930)). Qed.
Lemma lem1681872 (_25931 : real) (_25929 : real) (_25930 : real) : ((term202 _25929 _25930 _25931) = (term296 _25931 _25929 _25930)) = ((term296 _25931 _25929 _25930) = (term296 _25931 _25929 _25930)).
Proof. exact (MK_COMB (@lem1681861 _25931 _25929 _25930) (@lem1681871 _25931 _25929 _25930)). Qed.
Lemma lem1681874 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1681875 (x : Prop) : (x = x) = True.
Proof. exact (@lem1681874 Prop x). Qed.
Lemma lem1681876 (_25931 : real) (_25929 : real) (_25930 : real) : ((term296 _25931 _25929 _25930) = (term296 _25931 _25929 _25930)) = True.
Proof. exact (@lem1681875 (term296 _25931 _25929 _25930)). Qed.
Lemma lem1681877 (_25931 : real) (_25929 : real) (_25930 : real) : ((term202 _25929 _25930 _25931) = (term296 _25931 _25929 _25930)) = True.
Proof. exact (TRANS (@lem1681872 _25931 _25929 _25930) (@lem1681876 _25931 _25929 _25930)). Qed.
Lemma lem1681878 (_25931 : real) (_25929 : real) (_25930 : real) : True = ((term202 _25929 _25930 _25931) = (term296 _25931 _25929 _25930)).
Proof. exact (SYM (@lem1681877 _25931 _25929 _25930)). Qed.
Lemma lem1681879 (_25931 : real) (_25929 : real) (_25930 : real) : (term202 _25929 _25930 _25931) = (term296 _25931 _25929 _25930).
Proof. exact (EQ_MP (@lem1681878 _25931 _25929 _25930) (@lem0)). Qed.
Lemma lem1681880 (_25931 : real) (_25929 : real) (_25930 : real) (h1 : term122) : term296 _25931 _25929 _25930.
Proof. exact (EQ_MP (@lem1681879 _25931 _25929 _25930) (@lem1681698 _25929 _25930 _25931 h1)). Qed.
Lemma lem1681882 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1681883 (_25929 : real) (_25930 : real) (_25931 : real) : (term296 _25931 _25929 _25930) = (term299 _25929 _25930 _25931).
Proof. exact (@lem1681882 (term52 _25929 _25930) ((term31 _25929 _25930 _25931) = _25931)). Qed.
Lemma lem1681885 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1681886 (_25929 : real) (_25930 : real) : (term300 _25929 _25930) = ((real_add _25929 _25930) = term39).
Proof. exact (@lem1681885 ((real_add _25929 _25930) = term39)). Qed.
Lemma lem1681887 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1681888 (_25929 : real) (_25930 : real) : (term301 _25929 _25930) = (term302 _25929 _25930).
Proof. exact (MK_COMB (@lem1681887) (@lem1681886 _25929 _25930)). Qed.
Lemma lem1681889 (_25929 : real) (_25930 : real) (_25931 : real) : ((term31 _25929 _25930 _25931) = _25931) = ((term31 _25929 _25930 _25931) = _25931).
Proof. exact (eq_refl ((term31 _25929 _25930 _25931) = _25931)). Qed.
Lemma lem1681890 (_25929 : real) (_25930 : real) (_25931 : real) : (term299 _25929 _25930 _25931) = (term1 _25929 _25930 _25931).
Proof. exact (MK_COMB (@lem1681888 _25929 _25930) (@lem1681889 _25929 _25930 _25931)). Qed.
Lemma lem1681891 (_25929 : real) (_25930 : real) (_25931 : real) : (term296 _25931 _25929 _25930) = (term1 _25929 _25930 _25931).
Proof. exact (TRANS (@lem1681883 _25929 _25930 _25931) (@lem1681890 _25929 _25930 _25931)). Qed.
Lemma lem1681894 (_25929 : real) (_25930 : real) (_25931 : real) (h1 : term122) : term1 _25929 _25930 _25931.
Proof. exact (EQ_MP (@lem1681891 _25929 _25930 _25931) (@lem1681880 _25931 _25929 _25930 h1)). Qed.
Lemma lem1681895 (u : real) (v : real) (_25931 : real) (h1 : term122) : term1 u v _25931.
Proof. exact (@lem1681894 u v _25931 h1). Qed.
Lemma lem1681898 (_25931 : real) (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term122) (h2 : term163 a u x v y) : (term31 u v _25931) = _25931.
Proof. exact (@lem1681895 u v _25931 h1 (@lem1681843 a u x v y h2)). Qed.
Lemma lem1681899 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term122) (h2 : term163 a u x v y) : (term31 u v a) = a.
Proof. exact (@lem1681898 a a u x v y h1 h2). Qed.
Lemma lem1681900 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term122) (h2 : term163 a u x v y) : term107 u v a.
Proof. exact (fun h0 : term44 u v a => @lem1681899 a u x v y h1 h2). Qed.
Lemma lem1681902 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1681903 (u : real) (v : real) (a : real) : (term107 u v a) = ((term31 u v a) = a).
Proof. exact (@lem1681902 ((term31 u v a) = a)). Qed.
Lemma lem1681904 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term122) (h2 : term163 a u x v y) : (term31 u v a) = a.
Proof. exact (EQ_MP (@lem1681903 u v a) (@lem1681900 a u x v y h1 h2)). Qed.
Lemma lem1681906 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1681907 (u : real) (x : real) (v : real) (y : real) : (term303 u x v y) = (term303 u x v y).
Proof. exact (@lem1681906 (term303 u x v y)). Qed.
Lemma lem1681908 (u : real) (x : real) (v : real) (y : real) : term304 u x v y.
Proof. exact (fun h0 : term305 u x v y => @lem1681907 u x v y). Qed.
Lemma lem1681910 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1681911 (u : real) (x : real) (v : real) (y : real) : (term304 u x v y) = ((term303 u x v y) = (term303 u x v y)).
Proof. exact (@lem1681910 ((term303 u x v y) = (term303 u x v y))). Qed.
Lemma lem1681912 (u : real) (x : real) (v : real) (y : real) : (term303 u x v y) = (term303 u x v y).
Proof. exact (EQ_MP (@lem1681911 u x v y) (@lem1681908 u x v y)). Qed.
Lemma lem1681914 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : real_lt a x.
Proof. exact (proj1 (@lem1681537 a u x v y h1)). Qed.
Lemma lem1681915 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term306 a x.
Proof. exact (fun h0 : term277 a x => @lem1681914 a u x v y h1). Qed.
Lemma lem1681917 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1681918 (a : real) (x : real) : (term306 a x) = (real_lt a x).
Proof. exact (@lem1681917 (real_lt a x)). Qed.
Lemma lem1681919 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : real_lt a x.
Proof. exact (EQ_MP (@lem1681918 a x) (@lem1681915 a u x v y h1)). Qed.
Lemma lem1681921 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : real_lt a y.
Proof. exact (proj1 (@lem1681538 a u x v y h1)). Qed.
Lemma lem1681922 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term306 a y.
Proof. exact (fun h0 : term277 a y => @lem1681921 a u x v y h1). Qed.
Lemma lem1681924 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1681925 (a : real) (y : real) : (term306 a y) = (real_lt a y).
Proof. exact (@lem1681924 (real_lt a y)). Qed.
Lemma lem1681926 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : real_lt a y.
Proof. exact (EQ_MP (@lem1681925 a y) (@lem1681922 a u x v y h1)). Qed.
Lemma lem1681928 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term232 u.
Proof. exact (proj1 (@lem1681540 a u x v y h1)). Qed.
Lemma lem1681929 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term307 u.
Proof. exact (fun h0 : term282 u => @lem1681928 a u x v y h1). Qed.
Lemma lem1681931 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1681932 (u : real) : (term307 u) = (term232 u).
Proof. exact (@lem1681931 (term232 u)). Qed.
Lemma lem1681933 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term232 u.
Proof. exact (EQ_MP (@lem1681932 u) (@lem1681929 a u x v y h1)). Qed.
Lemma lem1681935 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term232 v.
Proof. exact (proj1 (@lem1681542 a u x v y h1)). Qed.
Lemma lem1681936 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term307 v.
Proof. exact (fun h0 : term282 v => @lem1681935 a u x v y h1). Qed.
Lemma lem1681938 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1681939 (v : real) : (term307 v) = (term232 v).
Proof. exact (@lem1681938 (term232 v)). Qed.
Lemma lem1681940 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term232 v.
Proof. exact (EQ_MP (@lem1681939 v) (@lem1681936 a u x v y h1)). Qed.
Lemma lem1681942 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1681542 a u x v y h1)). Qed.
Lemma lem1681943 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1681942 a u x v y h1). Qed.
Lemma lem1681945 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1681946 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1681945 ((real_add u v) = term39)). Qed.
Lemma lem1681947 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1681946 u v) (@lem1681943 a u x v y h1)). Qed.
Lemma lem1681963 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1681964 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term286 _25933 _25934 _25936 _25935 _25937 _25932) = (term308 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (@lem1681963 (term282 _25936) (term277 _25934 _25932) (term284 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1681978 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1681979 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term309 _25933 _25934 _25936 _25935 _25937 _25932) = (term310 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (@lem1681978 (term282 _25937) (term277 _25934 _25932) (term311 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1681993 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1681994 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term312 _25933 _25934 _25936 _25935 _25937 _25932) = (term313 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (@lem1681993 (term52 _25936 _25937) (term277 _25934 _25932) (term247 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1682010 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1682011 (_25933 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term314 _25933 _25934 _25936 _25935 _25937 _25932) = (term315 _25933 _25936 _25935 _25937 _25934 _25932).
Proof. exact (@lem1682010 (term247 _25933 _25934 _25936 _25935 _25937 _25932) (term277 _25934 _25932)). Qed.
Lemma lem1682017 (_25936 : real) (_25937 : real) : (term217 _25936 _25937) = (term217 _25936 _25937).
Proof. exact (eq_refl (term217 _25936 _25937)). Qed.
Lemma lem1682018 (_25933 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term313 _25933 _25934 _25936 _25935 _25937 _25932) = (term316 _25933 _25936 _25935 _25937 _25934 _25932).
Proof. exact (MK_COMB (@lem1682017 _25936 _25937) (@lem1682011 _25933 _25936 _25935 _25937 _25934 _25932)). Qed.
Lemma lem1682022 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682023 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term316 _25933 _25936 _25935 _25937 _25934 _25932) = (term317 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (@lem1682022 (term247 _25933 _25934 _25936 _25935 _25937 _25932) (term52 _25936 _25937) (term277 _25934 _25932)). Qed.
Lemma lem1682041 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term313 _25933 _25934 _25936 _25935 _25937 _25932) = (term317 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (TRANS (@lem1682018 _25933 _25936 _25935 _25937 _25934 _25932) (@lem1682023 _25933 _25935 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682042 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term312 _25933 _25934 _25936 _25935 _25937 _25932) = (term317 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (TRANS (@lem1681994 _25933 _25934 _25936 _25935 _25937 _25932) (@lem1682041 _25933 _25935 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682043 (_25937 : real) : (term233 _25937) = (term233 _25937).
Proof. exact (eq_refl (term233 _25937)). Qed.
Lemma lem1682044 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term310 _25933 _25934 _25936 _25935 _25937 _25932) = (term318 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (MK_COMB (@lem1682043 _25937) (@lem1682042 _25933 _25935 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682048 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682049 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term318 _25933 _25935 _25936 _25937 _25934 _25932) = (term319 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (@lem1682048 (term247 _25933 _25934 _25936 _25935 _25937 _25932) (term282 _25937) (term320 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682063 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682064 (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term321 _25936 _25937 _25934 _25932) = (term322 _25936 _25937 _25934 _25932).
Proof. exact (@lem1682063 (term52 _25936 _25937) (term282 _25937) (term277 _25934 _25932)). Qed.
Lemma lem1682082 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term323 _25933 _25934 _25936 _25935 _25937 _25932) = (term323 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (eq_refl (term323 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1682083 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term319 _25933 _25935 _25936 _25937 _25934 _25932) = (term324 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (MK_COMB (@lem1682082 _25933 _25934 _25936 _25935 _25937 _25932) (@lem1682064 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682094 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term318 _25933 _25935 _25936 _25937 _25934 _25932) = (term324 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (TRANS (@lem1682049 _25933 _25935 _25936 _25937 _25934 _25932) (@lem1682083 _25933 _25935 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682095 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term310 _25933 _25934 _25936 _25935 _25937 _25932) = (term324 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (TRANS (@lem1682044 _25933 _25935 _25936 _25937 _25934 _25932) (@lem1682094 _25933 _25935 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682096 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term309 _25933 _25934 _25936 _25935 _25937 _25932) = (term324 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (TRANS (@lem1681979 _25933 _25934 _25936 _25935 _25937 _25932) (@lem1682095 _25933 _25935 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682097 (_25936 : real) : (term233 _25936) = (term233 _25936).
Proof. exact (eq_refl (term233 _25936)). Qed.
Lemma lem1682098 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term308 _25933 _25934 _25936 _25935 _25937 _25932) = (term325 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (MK_COMB (@lem1682097 _25936) (@lem1682096 _25933 _25935 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682102 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682103 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term325 _25933 _25935 _25936 _25937 _25934 _25932) = (term326 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (@lem1682102 (term247 _25933 _25934 _25936 _25935 _25937 _25932) (term282 _25936) (term322 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682117 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682118 (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term327 _25936 _25937 _25934 _25932) = (term328 _25936 _25937 _25934 _25932).
Proof. exact (@lem1682117 (term52 _25936 _25937) (term282 _25936) (term329 _25937 _25934 _25932)). Qed.
Lemma lem1682146 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term323 _25933 _25934 _25936 _25935 _25937 _25932) = (term323 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (eq_refl (term323 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1682147 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term326 _25933 _25935 _25936 _25937 _25934 _25932) = (term330 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (MK_COMB (@lem1682146 _25933 _25934 _25936 _25935 _25937 _25932) (@lem1682118 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682158 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term325 _25933 _25935 _25936 _25937 _25934 _25932) = (term330 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (TRANS (@lem1682103 _25933 _25935 _25936 _25937 _25934 _25932) (@lem1682147 _25933 _25935 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682159 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term308 _25933 _25934 _25936 _25935 _25937 _25932) = (term330 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (TRANS (@lem1682098 _25933 _25935 _25936 _25937 _25934 _25932) (@lem1682158 _25933 _25935 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682160 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term286 _25933 _25934 _25936 _25935 _25937 _25932) = (term330 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (TRANS (@lem1681964 _25933 _25934 _25936 _25935 _25937 _25932) (@lem1682159 _25933 _25935 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682161 (_25933 : real) (_25935 : real) : (term238 _25933 _25935) = (term238 _25933 _25935).
Proof. exact (eq_refl (term238 _25933 _25935)). Qed.
Lemma lem1682162 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term287 _25933 _25934 _25936 _25935 _25937 _25932) = (term331 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (MK_COMB (@lem1682161 _25933 _25935) (@lem1682160 _25933 _25935 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682166 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682167 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term331 _25933 _25935 _25936 _25937 _25934 _25932) = (term332 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (@lem1682166 (term247 _25933 _25934 _25936 _25935 _25937 _25932) (term277 _25933 _25935) (term328 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682181 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682182 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term333 _25933 _25935 _25936 _25937 _25934 _25932) = (term334 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (@lem1682181 (term52 _25936 _25937) (term277 _25933 _25935) (term335 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682198 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682199 (_25936 : real) (_25933 : real) (_25935 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term336 _25933 _25935 _25936 _25937 _25934 _25932) = (term337 _25936 _25933 _25935 _25937 _25934 _25932).
Proof. exact (@lem1682198 (term282 _25936) (term277 _25933 _25935) (term329 _25937 _25934 _25932)). Qed.
Lemma lem1682213 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682214 (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : (term338 _25933 _25935 _25937 _25934 _25932) = (term339 _25937 _25933 _25935 _25934 _25932).
Proof. exact (@lem1682213 (term282 _25937) (term277 _25933 _25935) (term277 _25934 _25932)). Qed.
Lemma lem1682230 (_25936 : real) : (term233 _25936) = (term233 _25936).
Proof. exact (eq_refl (term233 _25936)). Qed.
Lemma lem1682231 (_25936 : real) (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : (term337 _25936 _25933 _25935 _25937 _25934 _25932) = (term340 _25936 _25937 _25933 _25935 _25934 _25932).
Proof. exact (MK_COMB (@lem1682230 _25936) (@lem1682214 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682242 (_25936 : real) (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : (term336 _25933 _25935 _25936 _25937 _25934 _25932) = (term340 _25936 _25937 _25933 _25935 _25934 _25932).
Proof. exact (TRANS (@lem1682199 _25936 _25933 _25935 _25937 _25934 _25932) (@lem1682231 _25936 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682243 (_25936 : real) (_25937 : real) : (term217 _25936 _25937) = (term217 _25936 _25937).
Proof. exact (eq_refl (term217 _25936 _25937)). Qed.
Lemma lem1682244 (_25936 : real) (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : (term334 _25933 _25935 _25936 _25937 _25934 _25932) = (term341 _25936 _25937 _25933 _25935 _25934 _25932).
Proof. exact (MK_COMB (@lem1682243 _25936 _25937) (@lem1682242 _25936 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682255 (_25936 : real) (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : (term333 _25933 _25935 _25936 _25937 _25934 _25932) = (term341 _25936 _25937 _25933 _25935 _25934 _25932).
Proof. exact (TRANS (@lem1682182 _25933 _25935 _25936 _25937 _25934 _25932) (@lem1682244 _25936 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682256 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term323 _25933 _25934 _25936 _25935 _25937 _25932) = (term323 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (eq_refl (term323 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1682257 (_25936 : real) (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : (term332 _25933 _25935 _25936 _25937 _25934 _25932) = (term342 _25936 _25937 _25933 _25935 _25934 _25932).
Proof. exact (MK_COMB (@lem1682256 _25933 _25934 _25936 _25935 _25937 _25932) (@lem1682255 _25936 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682268 (_25936 : real) (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : (term331 _25933 _25935 _25936 _25937 _25934 _25932) = (term342 _25936 _25937 _25933 _25935 _25934 _25932).
Proof. exact (TRANS (@lem1682167 _25933 _25935 _25936 _25937 _25934 _25932) (@lem1682257 _25936 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682269 (_25936 : real) (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : (term287 _25933 _25934 _25936 _25935 _25937 _25932) = (term342 _25936 _25937 _25933 _25935 _25934 _25932).
Proof. exact (TRANS (@lem1682162 _25933 _25935 _25936 _25937 _25934 _25932) (@lem1682268 _25936 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682270 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1682271 (_25936 : real) (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : (term343 _25933 _25934 _25936 _25935 _25937 _25932) = (term344 _25936 _25937 _25933 _25935 _25934 _25932).
Proof. exact (MK_COMB (@lem1682270) (@lem1682269 _25936 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682295 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682296 (_25934 : real) (_25932 : real) (_25936 : real) (_25937 : real) : (term240 _25934 _25932 _25936 _25937) = (term345 _25934 _25932 _25936 _25937).
Proof. exact (@lem1682295 (term282 _25936) (term277 _25934 _25932) (term231 _25936 _25937)). Qed.
Lemma lem1682310 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682311 (_25934 : real) (_25932 : real) (_25936 : real) (_25937 : real) : (term346 _25934 _25932 _25936 _25937) = (term347 _25934 _25932 _25936 _25937).
Proof. exact (@lem1682310 (term282 _25937) (term277 _25934 _25932) (term52 _25936 _25937)). Qed.
Lemma lem1682325 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1682326 (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term348 _25934 _25932 _25936 _25937) = (term320 _25936 _25937 _25934 _25932).
Proof. exact (@lem1682325 (term52 _25936 _25937) (term277 _25934 _25932)). Qed.
Lemma lem1682334 (_25937 : real) : (term233 _25937) = (term233 _25937).
Proof. exact (eq_refl (term233 _25937)). Qed.
Lemma lem1682335 (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term347 _25934 _25932 _25936 _25937) = (term321 _25936 _25937 _25934 _25932).
Proof. exact (MK_COMB (@lem1682334 _25937) (@lem1682326 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682339 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682340 (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term321 _25936 _25937 _25934 _25932) = (term322 _25936 _25937 _25934 _25932).
Proof. exact (@lem1682339 (term52 _25936 _25937) (term282 _25937) (term277 _25934 _25932)). Qed.
Lemma lem1682358 (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term347 _25934 _25932 _25936 _25937) = (term322 _25936 _25937 _25934 _25932).
Proof. exact (TRANS (@lem1682335 _25936 _25937 _25934 _25932) (@lem1682340 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682359 (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term346 _25934 _25932 _25936 _25937) = (term322 _25936 _25937 _25934 _25932).
Proof. exact (TRANS (@lem1682311 _25934 _25932 _25936 _25937) (@lem1682358 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682360 (_25936 : real) : (term233 _25936) = (term233 _25936).
Proof. exact (eq_refl (term233 _25936)). Qed.
Lemma lem1682361 (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term345 _25934 _25932 _25936 _25937) = (term327 _25936 _25937 _25934 _25932).
Proof. exact (MK_COMB (@lem1682360 _25936) (@lem1682359 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682365 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682366 (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term327 _25936 _25937 _25934 _25932) = (term328 _25936 _25937 _25934 _25932).
Proof. exact (@lem1682365 (term52 _25936 _25937) (term282 _25936) (term329 _25937 _25934 _25932)). Qed.
Lemma lem1682394 (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term345 _25934 _25932 _25936 _25937) = (term328 _25936 _25937 _25934 _25932).
Proof. exact (TRANS (@lem1682361 _25936 _25937 _25934 _25932) (@lem1682366 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682395 (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term240 _25934 _25932 _25936 _25937) = (term328 _25936 _25937 _25934 _25932).
Proof. exact (TRANS (@lem1682296 _25934 _25932 _25936 _25937) (@lem1682394 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682396 (_25933 : real) (_25935 : real) : (term238 _25933 _25935) = (term238 _25933 _25935).
Proof. exact (eq_refl (term238 _25933 _25935)). Qed.
Lemma lem1682397 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term244 _25933 _25935 _25934 _25932 _25936 _25937) = (term333 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (MK_COMB (@lem1682396 _25933 _25935) (@lem1682395 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682401 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682402 (_25933 : real) (_25935 : real) (_25936 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term333 _25933 _25935 _25936 _25937 _25934 _25932) = (term334 _25933 _25935 _25936 _25937 _25934 _25932).
Proof. exact (@lem1682401 (term52 _25936 _25937) (term277 _25933 _25935) (term335 _25936 _25937 _25934 _25932)). Qed.
Lemma lem1682418 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682419 (_25936 : real) (_25933 : real) (_25935 : real) (_25937 : real) (_25934 : real) (_25932 : real) : (term336 _25933 _25935 _25936 _25937 _25934 _25932) = (term337 _25936 _25933 _25935 _25937 _25934 _25932).
Proof. exact (@lem1682418 (term282 _25936) (term277 _25933 _25935) (term329 _25937 _25934 _25932)). Qed.
Lemma lem1682433 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682434 (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : (term338 _25933 _25935 _25937 _25934 _25932) = (term339 _25937 _25933 _25935 _25934 _25932).
Proof. exact (@lem1682433 (term282 _25937) (term277 _25933 _25935) (term277 _25934 _25932)). Qed.
Lemma lem1682450 (_25936 : real) : (term233 _25936) = (term233 _25936).
Proof. exact (eq_refl (term233 _25936)). Qed.
Lemma lem1682451 (_25936 : real) (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : (term337 _25936 _25933 _25935 _25937 _25934 _25932) = (term340 _25936 _25937 _25933 _25935 _25934 _25932).
Proof. exact (MK_COMB (@lem1682450 _25936) (@lem1682434 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682462 (_25936 : real) (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : (term336 _25933 _25935 _25936 _25937 _25934 _25932) = (term340 _25936 _25937 _25933 _25935 _25934 _25932).
Proof. exact (TRANS (@lem1682419 _25936 _25933 _25935 _25937 _25934 _25932) (@lem1682451 _25936 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682463 (_25936 : real) (_25937 : real) : (term217 _25936 _25937) = (term217 _25936 _25937).
Proof. exact (eq_refl (term217 _25936 _25937)). Qed.
Lemma lem1682464 (_25936 : real) (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : (term334 _25933 _25935 _25936 _25937 _25934 _25932) = (term341 _25936 _25937 _25933 _25935 _25934 _25932).
Proof. exact (MK_COMB (@lem1682463 _25936 _25937) (@lem1682462 _25936 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682475 (_25936 : real) (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : (term333 _25933 _25935 _25936 _25937 _25934 _25932) = (term341 _25936 _25937 _25933 _25935 _25934 _25932).
Proof. exact (TRANS (@lem1682402 _25933 _25935 _25936 _25937 _25934 _25932) (@lem1682464 _25936 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682476 (_25936 : real) (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : (term244 _25933 _25935 _25934 _25932 _25936 _25937) = (term341 _25936 _25937 _25933 _25935 _25934 _25932).
Proof. exact (TRANS (@lem1682397 _25933 _25935 _25936 _25937 _25934 _25932) (@lem1682475 _25936 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682477 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term323 _25933 _25934 _25936 _25935 _25937 _25932) = (term323 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (eq_refl (term323 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1682478 (_25936 : real) (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : (term349 _25933 _25935 _25934 _25932 _25936 _25937) = (term342 _25936 _25937 _25933 _25935 _25934 _25932).
Proof. exact (MK_COMB (@lem1682477 _25933 _25934 _25936 _25935 _25937 _25932) (@lem1682476 _25936 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682489 (_25936 : real) (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : ((term287 _25933 _25934 _25936 _25935 _25937 _25932) = (term349 _25933 _25935 _25934 _25932 _25936 _25937)) = ((term342 _25936 _25937 _25933 _25935 _25934 _25932) = (term342 _25936 _25937 _25933 _25935 _25934 _25932)).
Proof. exact (MK_COMB (@lem1682271 _25936 _25937 _25933 _25935 _25934 _25932) (@lem1682478 _25936 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682491 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1682492 (x : Prop) : (x = x) = True.
Proof. exact (@lem1682491 Prop x). Qed.
Lemma lem1682493 (_25936 : real) (_25937 : real) (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) : ((term342 _25936 _25937 _25933 _25935 _25934 _25932) = (term342 _25936 _25937 _25933 _25935 _25934 _25932)) = True.
Proof. exact (@lem1682492 (term342 _25936 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682494 (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) (_25936 : real) (_25937 : real) : ((term287 _25933 _25934 _25936 _25935 _25937 _25932) = (term349 _25933 _25935 _25934 _25932 _25936 _25937)) = True.
Proof. exact (TRANS (@lem1682489 _25936 _25937 _25933 _25935 _25934 _25932) (@lem1682493 _25936 _25937 _25933 _25935 _25934 _25932)). Qed.
Lemma lem1682495 (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) (_25936 : real) (_25937 : real) : True = ((term287 _25933 _25934 _25936 _25935 _25937 _25932) = (term349 _25933 _25935 _25934 _25932 _25936 _25937)).
Proof. exact (SYM (@lem1682494 _25933 _25935 _25934 _25932 _25936 _25937)). Qed.
Lemma lem1682496 (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) (_25936 : real) (_25937 : real) : (term287 _25933 _25934 _25936 _25935 _25937 _25932) = (term349 _25933 _25935 _25934 _25932 _25936 _25937).
Proof. exact (EQ_MP (@lem1682495 _25933 _25935 _25934 _25932 _25936 _25937) (@lem0)). Qed.
Lemma lem1682497 (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) (_25936 : real) (_25937 : real) (h1 : term119) : term349 _25933 _25935 _25934 _25932 _25936 _25937.
Proof. exact (EQ_MP (@lem1682496 _25933 _25935 _25934 _25932 _25936 _25937) (@lem1681728 _25933 _25934 _25936 _25935 _25937 _25932 h1)). Qed.
Lemma lem1682499 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1682500 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term349 _25933 _25935 _25934 _25932 _25936 _25937) = (term350 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (@lem1682499 (term244 _25933 _25935 _25934 _25932 _25936 _25937) (term247 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1682502 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1682503 (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) (_25936 : real) (_25937 : real) : (term351 _25933 _25935 _25934 _25932 _25936 _25937) = (term352 _25933 _25935 _25934 _25932 _25936 _25937).
Proof. exact (@lem1682502 (term277 _25933 _25935) (term240 _25934 _25932 _25936 _25937)). Qed.
Lemma lem1682505 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1682506 (_25933 : real) (_25935 : real) : (term353 _25933 _25935) = (real_lt _25933 _25935).
Proof. exact (@lem1682505 (real_lt _25933 _25935)). Qed.
Lemma lem1682507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1682508 (_25933 : real) (_25935 : real) : (term354 _25933 _25935) = (term355 _25933 _25935).
Proof. exact (MK_COMB (@lem1682507) (@lem1682506 _25933 _25935)). Qed.
Lemma lem1682510 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1682511 (_25934 : real) (_25932 : real) (_25936 : real) (_25937 : real) : (term356 _25934 _25932 _25936 _25937) = (term357 _25934 _25932 _25936 _25937).
Proof. exact (@lem1682510 (term277 _25934 _25932) (term235 _25936 _25937)). Qed.
Lemma lem1682513 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1682514 (_25934 : real) (_25932 : real) : (term353 _25934 _25932) = (real_lt _25934 _25932).
Proof. exact (@lem1682513 (real_lt _25934 _25932)). Qed.
Lemma lem1682515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1682516 (_25934 : real) (_25932 : real) : (term354 _25934 _25932) = (term355 _25934 _25932).
Proof. exact (MK_COMB (@lem1682515) (@lem1682514 _25934 _25932)). Qed.
Lemma lem1682518 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1682519 (_25936 : real) (_25937 : real) : (term358 _25936 _25937) = (term359 _25936 _25937).
Proof. exact (@lem1682518 (term282 _25936) (term231 _25936 _25937)). Qed.
Lemma lem1682521 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1682522 (_25936 : real) : (term360 _25936) = (term232 _25936).
Proof. exact (@lem1682521 (term232 _25936)). Qed.
Lemma lem1682523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1682524 (_25936 : real) : (term361 _25936) = (term362 _25936).
Proof. exact (MK_COMB (@lem1682523) (@lem1682522 _25936)). Qed.
Lemma lem1682526 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1682527 (_25936 : real) (_25937 : real) : (term363 _25936 _25937) = (term364 _25936 _25937).
Proof. exact (@lem1682526 (term282 _25937) (term52 _25936 _25937)). Qed.
Lemma lem1682529 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1682530 (_25937 : real) : (term360 _25937) = (term232 _25937).
Proof. exact (@lem1682529 (term232 _25937)). Qed.
Lemma lem1682531 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1682532 (_25937 : real) : (term361 _25937) = (term362 _25937).
Proof. exact (MK_COMB (@lem1682531) (@lem1682530 _25937)). Qed.
Lemma lem1682534 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1682535 (_25936 : real) (_25937 : real) : (term300 _25936 _25937) = ((real_add _25936 _25937) = term39).
Proof. exact (@lem1682534 ((real_add _25936 _25937) = term39)). Qed.
Lemma lem1682536 (_25936 : real) (_25937 : real) : (term364 _25936 _25937) = (term237 _25936 _25937).
Proof. exact (MK_COMB (@lem1682532 _25937) (@lem1682535 _25936 _25937)). Qed.
Lemma lem1682537 (_25936 : real) (_25937 : real) : (term363 _25936 _25937) = (term237 _25936 _25937).
Proof. exact (TRANS (@lem1682527 _25936 _25937) (@lem1682536 _25936 _25937)). Qed.
Lemma lem1682538 (_25936 : real) (_25937 : real) : (term359 _25936 _25937) = (term242 _25936 _25937).
Proof. exact (MK_COMB (@lem1682524 _25936) (@lem1682537 _25936 _25937)). Qed.
Lemma lem1682539 (_25936 : real) (_25937 : real) : (term358 _25936 _25937) = (term242 _25936 _25937).
Proof. exact (TRANS (@lem1682519 _25936 _25937) (@lem1682538 _25936 _25937)). Qed.
Lemma lem1682540 (_25934 : real) (_25932 : real) (_25936 : real) (_25937 : real) : (term357 _25934 _25932 _25936 _25937) = (term246 _25934 _25932 _25936 _25937).
Proof. exact (MK_COMB (@lem1682516 _25934 _25932) (@lem1682539 _25936 _25937)). Qed.
Lemma lem1682541 (_25934 : real) (_25932 : real) (_25936 : real) (_25937 : real) : (term356 _25934 _25932 _25936 _25937) = (term246 _25934 _25932 _25936 _25937).
Proof. exact (TRANS (@lem1682511 _25934 _25932 _25936 _25937) (@lem1682540 _25934 _25932 _25936 _25937)). Qed.
Lemma lem1682542 (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) (_25936 : real) (_25937 : real) : (term352 _25933 _25935 _25934 _25932 _25936 _25937) = (term252 _25933 _25935 _25934 _25932 _25936 _25937).
Proof. exact (MK_COMB (@lem1682508 _25933 _25935) (@lem1682541 _25934 _25932 _25936 _25937)). Qed.
Lemma lem1682543 (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) (_25936 : real) (_25937 : real) : (term351 _25933 _25935 _25934 _25932 _25936 _25937) = (term252 _25933 _25935 _25934 _25932 _25936 _25937).
Proof. exact (TRANS (@lem1682503 _25933 _25935 _25934 _25932 _25936 _25937) (@lem1682542 _25933 _25935 _25934 _25932 _25936 _25937)). Qed.
Lemma lem1682544 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1682545 (_25933 : real) (_25935 : real) (_25934 : real) (_25932 : real) (_25936 : real) (_25937 : real) : (term365 _25933 _25935 _25934 _25932 _25936 _25937) = (term366 _25933 _25935 _25934 _25932 _25936 _25937).
Proof. exact (MK_COMB (@lem1682544) (@lem1682543 _25933 _25935 _25934 _25932 _25936 _25937)). Qed.
Lemma lem1682546 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term247 _25933 _25934 _25936 _25935 _25937 _25932) = (term247 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (eq_refl (term247 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1682547 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term350 _25933 _25934 _25936 _25935 _25937 _25932) = (term137 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (MK_COMB (@lem1682545 _25933 _25935 _25934 _25932 _25936 _25937) (@lem1682546 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1682548 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) : (term349 _25933 _25935 _25934 _25932 _25936 _25937) = (term137 _25933 _25934 _25936 _25935 _25937 _25932).
Proof. exact (TRANS (@lem1682500 _25933 _25934 _25936 _25935 _25937 _25932) (@lem1682547 _25933 _25934 _25936 _25935 _25937 _25932)). Qed.
Lemma lem1682550 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term237 u v.
Proof. exact (conj (@lem1681940 a u x v y h1) (@lem1681947 a u x v y h1)). Qed.
Lemma lem1682551 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term242 u v.
Proof. exact (conj (@lem1681933 a u x v y h1) (@lem1682550 a u x v y h1)). Qed.
Lemma lem1682552 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term246 a y u v.
Proof. exact (conj (@lem1681926 a u x v y h1) (@lem1682551 a u x v y h1)). Qed.
Lemma lem1682553 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term164 x a y u v.
Proof. exact (conj (@lem1681919 a u x v y h1) (@lem1682552 a u x v y h1)). Qed.
Lemma lem1682555 (_25933 : real) (_25934 : real) (_25936 : real) (_25935 : real) (_25937 : real) (_25932 : real) (h1 : term119) : term137 _25933 _25934 _25936 _25935 _25937 _25932.
Proof. exact (EQ_MP (@lem1682548 _25933 _25934 _25936 _25935 _25937 _25932) (@lem1682497 _25933 _25935 _25934 _25932 _25936 _25937 h1)). Qed.
Lemma lem1682556 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) : term367 a u x v y.
Proof. exact (@lem1682555 a a u x v y h1). Qed.
Lemma lem1682559 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term163 a u x v y) : term368 a u x v y.
Proof. exact (@lem1682556 a u x v y h1 (@lem1682553 a u x v y h2)). Qed.
Lemma lem1682560 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term163 a u x v y) : term369 a u x v y.
Proof. exact (fun h0 : term370 a u x v y => @lem1682559 a u x v y h1 h2). Qed.
Lemma lem1682562 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1682563 (a : real) (u : real) (x : real) (v : real) (y : real) : (term369 a u x v y) = (term368 a u x v y).
Proof. exact (@lem1682562 (term368 a u x v y)). Qed.
Lemma lem1682564 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term163 a u x v y) : term368 a u x v y.
Proof. exact (EQ_MP (@lem1682563 a u x v y) (@lem1682560 a u x v y h1 h2)). Qed.
Lemma lem1682582 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682583 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : (term293 _25944 _25945 _25942 _25943) = (term371 _25944 _25945 _25942 _25943).
Proof. exact (@lem1682582 (real_lt _25944 _25945) (term57 _25943 _25945) (term277 _25942 _25943)). Qed.
Lemma lem1682601 (_25942 : real) (_25944 : real) : (term58 _25942 _25944) = (term58 _25942 _25944).
Proof. exact (eq_refl (term58 _25942 _25944)). Qed.
Lemma lem1682602 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : (term295 _25944 _25945 _25942 _25943) = (term372 _25944 _25945 _25942 _25943).
Proof. exact (MK_COMB (@lem1682601 _25942 _25944) (@lem1682583 _25944 _25945 _25942 _25943)). Qed.
Lemma lem1682606 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1682607 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : (term372 _25944 _25945 _25942 _25943) = (term373 _25944 _25945 _25942 _25943).
Proof. exact (@lem1682606 (real_lt _25944 _25945) (term57 _25942 _25944) (term374 _25945 _25942 _25943)). Qed.
Lemma lem1682637 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : (term295 _25944 _25945 _25942 _25943) = (term373 _25944 _25945 _25942 _25943).
Proof. exact (TRANS (@lem1682602 _25944 _25945 _25942 _25943) (@lem1682607 _25944 _25945 _25942 _25943)). Qed.
Lemma lem1682638 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1682639 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : (term375 _25944 _25945 _25942 _25943) = (term376 _25944 _25945 _25942 _25943).
Proof. exact (MK_COMB (@lem1682638) (@lem1682637 _25944 _25945 _25942 _25943)). Qed.
Lemma lem1682669 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : (term373 _25944 _25945 _25942 _25943) = (term373 _25944 _25945 _25942 _25943).
Proof. exact (eq_refl (term373 _25944 _25945 _25942 _25943)). Qed.
Lemma lem1682670 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : ((term295 _25944 _25945 _25942 _25943) = (term373 _25944 _25945 _25942 _25943)) = ((term373 _25944 _25945 _25942 _25943) = (term373 _25944 _25945 _25942 _25943)).
Proof. exact (MK_COMB (@lem1682639 _25944 _25945 _25942 _25943) (@lem1682669 _25944 _25945 _25942 _25943)). Qed.
Lemma lem1682672 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1682673 (x : Prop) : (x = x) = True.
Proof. exact (@lem1682672 Prop x). Qed.
Lemma lem1682674 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : ((term373 _25944 _25945 _25942 _25943) = (term373 _25944 _25945 _25942 _25943)) = True.
Proof. exact (@lem1682673 (term373 _25944 _25945 _25942 _25943)). Qed.
Lemma lem1682675 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : ((term295 _25944 _25945 _25942 _25943) = (term373 _25944 _25945 _25942 _25943)) = True.
Proof. exact (TRANS (@lem1682670 _25944 _25945 _25942 _25943) (@lem1682674 _25944 _25945 _25942 _25943)). Qed.
Lemma lem1682676 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : True = ((term295 _25944 _25945 _25942 _25943) = (term373 _25944 _25945 _25942 _25943)).
Proof. exact (SYM (@lem1682675 _25944 _25945 _25942 _25943)). Qed.
Lemma lem1682677 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : (term295 _25944 _25945 _25942 _25943) = (term373 _25944 _25945 _25942 _25943).
Proof. exact (EQ_MP (@lem1682676 _25944 _25945 _25942 _25943) (@lem0)). Qed.
Lemma lem1682678 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : term373 _25944 _25945 _25942 _25943.
Proof. exact (EQ_MP (@lem1682677 _25944 _25945 _25942 _25943) (@lem1681778 _25944 _25945 _25942 _25943)). Qed.
Lemma lem1682680 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1682681 (_25942 : real) (_25943 : real) (_25944 : real) (_25945 : real) : (term373 _25944 _25945 _25942 _25943) = (term377 _25942 _25943 _25944 _25945).
Proof. exact (@lem1682680 (term378 _25944 _25945 _25942 _25943) (real_lt _25944 _25945)). Qed.
Lemma lem1682683 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1682684 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : (term379 _25944 _25945 _25942 _25943) = (term380 _25944 _25945 _25942 _25943).
Proof. exact (@lem1682683 (term57 _25942 _25944) (term374 _25945 _25942 _25943)). Qed.
Lemma lem1682686 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1682687 (_25942 : real) (_25944 : real) : (term72 _25942 _25944) = (_25942 = _25944).
Proof. exact (@lem1682686 (_25942 = _25944)). Qed.
Lemma lem1682688 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1682689 (_25942 : real) (_25944 : real) : (term73 _25942 _25944) = (term74 _25942 _25944).
Proof. exact (MK_COMB (@lem1682688) (@lem1682687 _25942 _25944)). Qed.
Lemma lem1682691 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1682692 (_25945 : real) (_25942 : real) (_25943 : real) : (term381 _25945 _25942 _25943) = (term382 _25945 _25942 _25943).
Proof. exact (@lem1682691 (term57 _25943 _25945) (term277 _25942 _25943)). Qed.
Lemma lem1682694 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1682695 (_25943 : real) (_25945 : real) : (term72 _25943 _25945) = (_25943 = _25945).
Proof. exact (@lem1682694 (_25943 = _25945)). Qed.
Lemma lem1682696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1682697 (_25943 : real) (_25945 : real) : (term73 _25943 _25945) = (term74 _25943 _25945).
Proof. exact (MK_COMB (@lem1682696) (@lem1682695 _25943 _25945)). Qed.
Lemma lem1682699 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1682700 (_25942 : real) (_25943 : real) : (term353 _25942 _25943) = (real_lt _25942 _25943).
Proof. exact (@lem1682699 (real_lt _25942 _25943)). Qed.
Lemma lem1682701 (_25945 : real) (_25942 : real) (_25943 : real) : (term382 _25945 _25942 _25943) = (term383 _25945 _25942 _25943).
Proof. exact (MK_COMB (@lem1682697 _25943 _25945) (@lem1682700 _25942 _25943)). Qed.
Lemma lem1682702 (_25945 : real) (_25942 : real) (_25943 : real) : (term381 _25945 _25942 _25943) = (term383 _25945 _25942 _25943).
Proof. exact (TRANS (@lem1682692 _25945 _25942 _25943) (@lem1682701 _25945 _25942 _25943)). Qed.
Lemma lem1682703 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : (term380 _25944 _25945 _25942 _25943) = (term384 _25944 _25945 _25942 _25943).
Proof. exact (MK_COMB (@lem1682689 _25942 _25944) (@lem1682702 _25945 _25942 _25943)). Qed.
Lemma lem1682704 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : (term379 _25944 _25945 _25942 _25943) = (term384 _25944 _25945 _25942 _25943).
Proof. exact (TRANS (@lem1682684 _25944 _25945 _25942 _25943) (@lem1682703 _25944 _25945 _25942 _25943)). Qed.
Lemma lem1682705 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1682706 (_25944 : real) (_25945 : real) (_25942 : real) (_25943 : real) : (term385 _25944 _25945 _25942 _25943) = (term386 _25944 _25945 _25942 _25943).
Proof. exact (MK_COMB (@lem1682705) (@lem1682704 _25944 _25945 _25942 _25943)). Qed.
Lemma lem1682707 (_25944 : real) (_25945 : real) : (real_lt _25944 _25945) = (real_lt _25944 _25945).
Proof. exact (eq_refl (real_lt _25944 _25945)). Qed.
Lemma lem1682708 (_25942 : real) (_25943 : real) (_25944 : real) (_25945 : real) : (term377 _25942 _25943 _25944 _25945) = (term387 _25942 _25943 _25944 _25945).
Proof. exact (MK_COMB (@lem1682706 _25944 _25945 _25942 _25943) (@lem1682707 _25944 _25945)). Qed.
Lemma lem1682709 (_25942 : real) (_25943 : real) (_25944 : real) (_25945 : real) : (term373 _25944 _25945 _25942 _25943) = (term387 _25942 _25943 _25944 _25945).
Proof. exact (TRANS (@lem1682681 _25942 _25943 _25944 _25945) (@lem1682708 _25942 _25943 _25944 _25945)). Qed.
Lemma lem1682711 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term163 a u x v y) : term388 a u x v y.
Proof. exact (conj (@lem1681912 u x v y) (@lem1682564 a u x v y h1 h2)). Qed.
Lemma lem1682712 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : term389 a u x v y.
Proof. exact (conj (@lem1681904 a u x v y h2 h3) (@lem1682711 a u x v y h1 h3)). Qed.
Lemma lem1682714 (_25942 : real) (_25943 : real) (_25944 : real) (_25945 : real) : term387 _25942 _25943 _25944 _25945.
Proof. exact (EQ_MP (@lem1682709 _25942 _25943 _25944 _25945) (@lem1682678 _25944 _25945 _25942 _25943)). Qed.
Lemma lem1682715 (a : real) (u : real) (x : real) (v : real) (y : real) : term390 a u x v y.
Proof. exact (@lem1682714 (term31 u v a) (term303 u x v y) a (term303 u x v y)). Qed.
Lemma lem1682718 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : term165 a u x v y.
Proof. exact (@lem1682715 a u x v y (@lem1682712 a u x v y h1 h2 h3)). Qed.
Lemma lem1682719 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : term391 a u x v y.
Proof. exact (fun h0 : term288 a u x v y => @lem1682718 a u x v y h1 h2 h3). Qed.
Lemma lem1682721 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1682722 (a : real) (u : real) (x : real) (v : real) (y : real) : (term391 a u x v y) = (term165 a u x v y).
Proof. exact (@lem1682721 (term165 a u x v y)). Qed.
Lemma lem1682723 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : term165 a u x v y.
Proof. exact (EQ_MP (@lem1682722 a u x v y) (@lem1682719 a u x v y h1 h2 h3)). Qed.
Lemma lem1682726 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1682728 (a : real) (u : real) (x : real) (v : real) (y : real) : (term288 a u x v y) = (term392 a u x v y).
Proof. exact (@lem1682726 (term165 a u x v y)). Qed.
Lemma lem1682731 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term163 a u x v y) : term392 a u x v y.
Proof. exact (EQ_MP (@lem1682728 a u x v y) (@lem1681730 a u x v y h1)). Qed.
Lemma lem1682734 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : False.
Proof. exact (@lem1682731 a u x v y h3 (@lem1682723 a u x v y h1 h2 h3)). Qed.
Lemma lem1682735 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : term109.
Proof. exact (fun h0 : ~ False => @lem1682734 a u x v y h1 h2 h3). Qed.
Lemma lem1682737 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1682738 : term109 = False.
Proof. exact (@lem1682737 False). Qed.
Lemma lem1682739 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : False.
Proof. exact (EQ_MP (@lem1682738) (@lem1682735 a u x v y h1 h2 h3)). Qed.
Lemma lem1682740 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : (term163 a u x v y) = False.
Proof. exact (prop_ext (fun h4 : term163 a u x v y => @lem1682739 a u x v y h1 h2 h3) (fun h4 : False => @lem1681535 a u x v y h3)). Qed.
Lemma lem1682741 (a : real) (u : real) (x : real) (v : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term163 a u x v y) : False.
Proof. exact (EQ_MP (@lem1682740 a u x v y h1 h2 h3) (@lem1681535 a u x v y h3)). Qed.
Lemma lem1682742 (a : real) (u : real) (x : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term174 a u x y) : False.
Proof. exact (ex_elim (@lem1681293 a u x y h3) (fun v : real => fun h0 : term173 a u x y v => @lem1682741 a u x v y h1 h2 h0)). Qed.
Lemma lem1682743 (a : real) (x : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term181 a x y) : False.
Proof. exact (ex_elim (@lem1681292 a x y h3) (fun u : real => fun h0 : term180 a x y u => @lem1682742 a u x y h1 h2 h0)). Qed.
Lemma lem1682744 (x : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term188 x y) : False.
Proof. exact (ex_elim (@lem1681291 x y h3) (fun a : real => fun h0 : term187 x y a => @lem1682743 a x y h1 h2 h0)). Qed.
Lemma lem1682745 (x : real) (h1 : term119) (h2 : term122) (h3 : term195 x) : False.
Proof. exact (ex_elim (@lem1681290 x h3) (fun y : real => fun h0 : term194 x y => @lem1682744 x y h1 h2 h0)). Qed.
Lemma lem1682746 (h1 : term119) (h2 : term122) (h3 : term125) : False.
Proof. exact (ex_elim (@lem1681057 h3) (fun x : real => fun h0 : term200 x => @lem1682745 x h1 h2 h0)). Qed.
Lemma lem1682747 (h1 : term122) (h2 : term125) : term130.
Proof. exact (fun h0 : term119 => @lem1682746 h0 h1 h2). Qed.
Lemma lem1682748 : term130 = term131.
Proof. exact (@lem69 term119). Qed.
Lemma lem1682749 (h1 : term122) (h2 : term125) : term131.
Proof. exact (EQ_MP (@lem1682748) (@lem1682747 h1 h2)). Qed.
Lemma lem1682750 (h1 : term125) : term134.
Proof. exact (fun h0 : term122 => @lem1682749 h0 h1). Qed.
Lemma lem1682751 : term136.
Proof. exact (fun h0 : term125 => @lem1682750 h0). Qed.
Lemma lem1682752 : term126.
Proof. exact (EQ_MP (@lem1680912) (@lem1682751)). Qed.
Lemma lem1682754 : term126.
Proof. exact (@lem1680602 (@lem1682752)). Qed.
Lemma lem1682755 (h1 : term125) : term133.
Proof. exact (@lem1682754 (@lem1680587 h1)). Qed.
Lemma lem1682756 (h1 : term125) : term130.
Proof. exact (@lem1682755 h1 (@lem1680582)). Qed.
Lemma lem1682757 (h1 : term125) : False.
Proof. exact (@lem1682756 h1 (@lem1680579)). Qed.
Lemma lem1682758 (h1 : term125) : term125 = False.
Proof. exact (prop_ext (fun h2 : term125 => @lem1682757 h1) (fun h2 : False => @lem1680587 h1)). Qed.
Lemma lem1682759 (h1 : term125) : False.
Proof. exact (EQ_MP (@lem1682758 h1) (@lem1680587 h1)). Qed.
Lemma lem1682760 : term124.
Proof. exact (fun h0 : term125 => @lem1682759 h0). Qed.
Lemma lem1682761 : term123.
Proof. exact (EQ_MP (@lem1680586) (@lem1682760)). Qed.
