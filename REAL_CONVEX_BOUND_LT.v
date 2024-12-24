Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_CONVEX_BOUND_LT_term_abbrevs.
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
Lemma lem1673900 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1673901 (u : real) (v : real) (a : real) : (term1 u v a) = (term2 u v a).
Proof. exact (@lem1673900 (term1 u v a)). Qed.
Lemma lem1673902 (u : real) (v : real) (a : real) : (term2 u v a) = (term1 u v a).
Proof. exact (SYM (@lem1673901 u v a)). Qed.
Lemma lem1673903 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term3 u v a.
Proof. exact (h1). Qed.
Lemma lem1673906 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term4 u v a.
Proof. exact (h1). Qed.
Lemma lem1673907 (u : real) (v : real) (a : real) : term5 u v a.
Proof. exact (fun h0 : term4 u v a => @lem1673906 u v a h0). Qed.
Lemma lem1673908 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (h1). Qed.
Lemma lem1673909 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term4 u v a.
Proof. exact (h1). Qed.
Lemma lem1673910 (u : real) (v : real) (a : real) (h1 : term4 u v a) (h2 : term5 u v a) : term4 u v a.
Proof. exact (@lem1673908 u v a h2 (@lem1673909 u v a h1)). Qed.
Lemma lem1673911 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term6 u v a.
Proof. exact (fun h0 : term5 u v a => @lem1673910 u v a h1 h0). Qed.
Lemma lem1673912 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (h1). Qed.
Lemma lem1673913 (u : real) (v : real) (a : real) (h1 : term4 u v a) (h2 : term5 u v a) : term4 u v a.
Proof. exact (@lem1673911 u v a h1 (@lem1673912 u v a h2)). Qed.
Lemma lem1673914 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (fun h0 : term4 u v a => @lem1673913 u v a h0 h1). Qed.
Lemma lem1673915 (u : real) (v : real) (a : real) : term7 u v a.
Proof. exact (fun h0 : term5 u v a => @lem1673914 u v a h0). Qed.
Lemma lem1673918 (u : real) (v : real) (a : real) : term5 u v a.
Proof. exact (@lem1673915 u v a (@lem1673907 u v a)). Qed.
Lemma lem1673950 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1673951 : term8 = term9.
Proof. exact (@lem1673950 term10). Qed.
Lemma lem1673956 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1673957 : term12 = term13.
Proof. exact (MK_COMB (@lem1673956) (@lem1673951)). Qed.
Lemma lem1673960 (u : real) (v : real) (a : real) : (term14 u v a) = (term14 u v a).
Proof. exact (eq_refl (term14 u v a)). Qed.
Lemma lem1673961 (u : real) (v : real) (a : real) : (term4 u v a) = (term15 u v a).
Proof. exact (MK_COMB (@lem1673960 u v a) (@lem1673957)). Qed.
Lemma lem1673964 (v : real) (a : real) : (term16 v a) = (term17 v a).
Proof. exact (fun_ext (fun u : real => @lem1673961 u v a)). Qed.
Lemma lem1673965 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1673966 (v : real) (a : real) : (term18 v a) = (term19 v a).
Proof. exact (MK_COMB (@lem1673965) (@lem1673964 v a)). Qed.
Lemma lem1673971 (a : real) : (term20 a) = (term21 a).
Proof. exact (fun_ext (fun v : real => @lem1673966 v a)). Qed.
Lemma lem1673972 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1673973 (a : real) : (term22 a) = (term23 a).
Proof. exact (MK_COMB (@lem1673972) (@lem1673971 a)). Qed.
Lemma lem1673978 : term24 = term25.
Proof. exact (fun_ext (fun a : real => @lem1673973 a)). Qed.
Lemma lem1673979 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1673988 : term26 = term27.
Proof. exact (MK_COMB (@lem1673979) (@lem1673978)). Qed.
Lemma lem1673989 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1673990 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1673989 x)). Qed.
Lemma lem1673991 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1673992 : term10 = term10.
Proof. exact (MK_COMB (@lem1673991) (@lem1673990)). Qed.
Lemma lem1673993 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1673994 : term9 = term9.
Proof. exact (MK_COMB (@lem1673993) (@lem1673992)). Qed.
Lemma lem1673995 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1673996 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1673995 x y z)). Qed.
Lemma lem1673997 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1673998 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1673997) (@lem1673996 x y)). Qed.
Lemma lem1673999 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1673998 x y)). Qed.
Lemma lem1674000 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674001 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1674000) (@lem1673999 x)). Qed.
Lemma lem1674002 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1674001 x)). Qed.
Lemma lem1674003 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674004 : term37 = term37.
Proof. exact (MK_COMB (@lem1674003) (@lem1674002)). Qed.
Lemma lem1674005 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1674006 : term11 = term11.
Proof. exact (MK_COMB (@lem1674005) (@lem1674004)). Qed.
Lemma lem1674007 : term13 = term13.
Proof. exact (MK_COMB (@lem1674006) (@lem1673994)). Qed.
Lemma lem1674016 (u : real) (v : real) (a : real) : (term14 u v a) = (term14 u v a).
Proof. exact (eq_refl (term14 u v a)). Qed.
Lemma lem1674017 (u : real) (v : real) (a : real) : (term15 u v a) = (term15 u v a).
Proof. exact (MK_COMB (@lem1674016 u v a) (@lem1674007)). Qed.
Lemma lem1674018 (v : real) (a : real) : (term17 v a) = (term17 v a).
Proof. exact (fun_ext (fun u : real => @lem1674017 u v a)). Qed.
Lemma lem1674019 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674020 (v : real) (a : real) : (term19 v a) = (term19 v a).
Proof. exact (MK_COMB (@lem1674019) (@lem1674018 v a)). Qed.
Lemma lem1674021 (a : real) : (term21 a) = (term21 a).
Proof. exact (fun_ext (fun v : real => @lem1674020 v a)). Qed.
Lemma lem1674022 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674023 (a : real) : (term23 a) = (term23 a).
Proof. exact (MK_COMB (@lem1674022) (@lem1674021 a)). Qed.
Lemma lem1674024 : term25 = term25.
Proof. exact (fun_ext (fun a : real => @lem1674023 a)). Qed.
Lemma lem1674025 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674026 : term27 = term27.
Proof. exact (MK_COMB (@lem1674025) (@lem1674024)). Qed.
Lemma lem1674077 : term26 = term27.
Proof. exact (TRANS (@lem1673988) (@lem1674026)). Qed.
Lemma lem1674078 : term27 = term26.
Proof. exact (SYM (@lem1674077)). Qed.
Lemma lem1674079 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term3 u v a.
Proof. exact (h1). Qed.
Lemma lem1674080 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem1674081 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1674092 (u : real) (v : real) (a : real) : (term3 u v a) = (term38 u v a).
Proof. exact (@lem17362 ((real_add u v) = term39) ((term31 u v a) = a)). Qed.
Lemma lem1674094 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1674095 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1674094 x y z)). Qed.
Lemma lem1674096 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674097 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1674096) (@lem1674095 x y)). Qed.
Lemma lem1674098 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1674097 x y)). Qed.
Lemma lem1674099 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674100 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1674099) (@lem1674098 x)). Qed.
Lemma lem1674101 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1674100 x)). Qed.
Lemma lem1674102 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674119 : term37 = term37.
Proof. exact (MK_COMB (@lem1674102) (@lem1674101)). Qed.
Lemma lem1674120 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1674119) (@lem1674080 h1)). Qed.
Lemma lem1674121 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1674122 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1674121 x)). Qed.
Lemma lem1674123 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674132 : term10 = term10.
Proof. exact (MK_COMB (@lem1674123) (@lem1674122)). Qed.
Lemma lem1674133 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1674132) (@lem1674081 h1)). Qed.
Lemma lem1674171 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term38 u v a.
Proof. exact (EQ_MP (@lem1674092 u v a) (@lem1674079 u v a h1)). Qed.
Lemma lem1674196 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1674197 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1674196 x y z)). Qed.
Lemma lem1674198 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674199 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1674198) (@lem1674197 x y)). Qed.
Lemma lem1674200 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1674199 x y)). Qed.
Lemma lem1674201 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674202 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1674201) (@lem1674200 x)). Qed.
Lemma lem1674203 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1674202 x)). Qed.
Lemma lem1674204 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674205 : term37 = term37.
Proof. exact (MK_COMB (@lem1674204) (@lem1674203)). Qed.
Lemma lem1674206 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1674205) (@lem1674120 h1)). Qed.
Lemma lem1674221 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1674222 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1674221 x)). Qed.
Lemma lem1674223 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674224 : term10 = term10.
Proof. exact (MK_COMB (@lem1674223) (@lem1674222)). Qed.
Lemma lem1674225 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1674224) (@lem1674133 h1)). Qed.
Lemma lem1674229 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1674230 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1674229 x y z)). Qed.
Lemma lem1674231 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674232 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1674231) (@lem1674230 x y)). Qed.
Lemma lem1674233 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1674232 x y)). Qed.
Lemma lem1674234 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674235 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1674234) (@lem1674233 x)). Qed.
Lemma lem1674236 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1674235 x)). Qed.
Lemma lem1674237 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674239 : term37 = term37.
Proof. exact (MK_COMB (@lem1674237) (@lem1674236)). Qed.
Lemma lem1674240 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1674239) (@lem1674206 h1)). Qed.
Lemma lem1674242 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1674243 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1674242 x)). Qed.
Lemma lem1674244 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674246 : term10 = term10.
Proof. exact (MK_COMB (@lem1674244) (@lem1674243)). Qed.
Lemma lem1674247 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1674246) (@lem1674225 h1)). Qed.
Lemma lem1674256 (_25817 : real) (h1 : term37) : term40 _25817.
Proof. exact (@lem1674240 h1 _25817). Qed.
Lemma lem1674257 (_25817 : real) : (term40 _25817) = (term35 _25817).
Proof. exact (eq_refl (term40 _25817)). Qed.
Lemma lem1674258 (_25817 : real) (h1 : term37) : term35 _25817.
Proof. exact (EQ_MP (@lem1674257 _25817) (@lem1674256 _25817 h1)). Qed.
Lemma lem1674259 (_25817 : real) (_25818 : real) (h1 : term37) : term41 _25817 _25818.
Proof. exact (@lem1674258 _25817 h1 _25818). Qed.
Lemma lem1674260 (_25817 : real) (_25818 : real) : (term41 _25817 _25818) = (term33 _25817 _25818).
Proof. exact (eq_refl (term41 _25817 _25818)). Qed.
Lemma lem1674261 (_25817 : real) (_25818 : real) (h1 : term37) : term33 _25817 _25818.
Proof. exact (EQ_MP (@lem1674260 _25817 _25818) (@lem1674259 _25817 _25818 h1)). Qed.
Lemma lem1674262 (_25817 : real) (_25818 : real) (_25819 : real) (h1 : term37) : term42 _25817 _25818 _25819.
Proof. exact (@lem1674261 _25817 _25818 h1 _25819). Qed.
Lemma lem1674263 (_25817 : real) (_25818 : real) (_25819 : real) : (term42 _25817 _25818 _25819) = ((term30 _25817 _25818 _25819) = (term31 _25817 _25818 _25819)).
Proof. exact (eq_refl (term42 _25817 _25818 _25819)). Qed.
Lemma lem1674265 (_25820 : real) (h1 : term10) : term43 _25820.
Proof. exact (@lem1674247 h1 _25820). Qed.
Lemma lem1674266 (_25820 : real) : (term43 _25820) = ((term28 _25820) = _25820).
Proof. exact (eq_refl (term43 _25820)). Qed.
Lemma lem1674275 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term44 u v a.
Proof. exact (proj2 (@lem1674171 u v a h1)). Qed.
Lemma lem1674300 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1674301 (_25827 : real) (_25829 : real) (h1 : _25827 = _25829) : _25827 = _25829.
Proof. exact (h1). Qed.
Lemma lem1674302 (_25828 : real) (_25830 : real) (h1 : _25828 = _25830) : _25828 = _25830.
Proof. exact (h1). Qed.
Lemma lem1674303 (_25827 : real) (_25829 : real) (h1 : _25827 = _25829) : (real_mul _25827) = (real_mul _25829).
Proof. exact (MK_COMB (@lem1674300) (@lem1674301 _25827 _25829 h1)). Qed.
Lemma lem1674304 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) (h1 : _25827 = _25829) (h2 : _25828 = _25830) : (real_mul _25827 _25828) = (real_mul _25829 _25830).
Proof. exact (MK_COMB (@lem1674303 _25827 _25829 h1) (@lem1674302 _25828 _25830 h2)). Qed.
Lemma lem1674305 (_25828 : real) (_25830 : real) (_25827 : real) (_25829 : real) (h1 : _25827 = _25829) : term45 _25827 _25828 _25829 _25830.
Proof. exact (fun h0 : _25828 = _25830 => @lem1674304 _25827 _25829 _25828 _25830 h1 h0). Qed.
Lemma lem1674307 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1674308 (_25827 : real) (_25828 : real) (_25829 : real) (_25830 : real) : (term45 _25827 _25828 _25829 _25830) = (term47 _25827 _25828 _25829 _25830).
Proof. exact (@lem1674307 (_25828 = _25830) ((real_mul _25827 _25828) = (real_mul _25829 _25830))). Qed.
Lemma lem1674309 (_25828 : real) (_25830 : real) (_25827 : real) (_25829 : real) (h1 : _25827 = _25829) : term47 _25827 _25828 _25829 _25830.
Proof. exact (EQ_MP (@lem1674308 _25827 _25828 _25829 _25830) (@lem1674305 _25828 _25830 _25827 _25829 h1)). Qed.
Lemma lem1674310 (_25827 : real) (_25828 : real) (_25829 : real) (_25830 : real) : term48 _25827 _25828 _25829 _25830.
Proof. exact (fun h0 : _25827 = _25829 => @lem1674309 _25828 _25830 _25827 _25829 h0). Qed.
Lemma lem1674312 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1674313 (_25827 : real) (_25828 : real) (_25829 : real) (_25830 : real) : (term48 _25827 _25828 _25829 _25830) = (term49 _25827 _25828 _25829 _25830).
Proof. exact (@lem1674312 (_25827 = _25829) (term47 _25827 _25828 _25829 _25830)). Qed.
Lemma lem1674314 (_25827 : real) (_25828 : real) (_25829 : real) (_25830 : real) : term49 _25827 _25828 _25829 _25830.
Proof. exact (EQ_MP (@lem1674313 _25827 _25828 _25829 _25830) (@lem1674310 _25827 _25828 _25829 _25830)). Qed.
Lemma lem1674331 (x : real) (y : real) (z : real) : term50 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1674335 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (real_add u v) = term39.
Proof. exact (proj1 (@lem1674171 u v a h1)). Qed.
Lemma lem1674336 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1674335 u v a h1). Qed.
Lemma lem1674338 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1674339 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1674338 ((real_add u v) = term39)). Qed.
Lemma lem1674340 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1674339 u v) (@lem1674336 u v a h1)). Qed.
Lemma lem1674342 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1674343 (a : real) : a = a.
Proof. exact (@lem1674342 a). Qed.
Lemma lem1674344 (a : real) : term54 a.
Proof. exact (fun h0 : term55 a => @lem1674343 a). Qed.
Lemma lem1674346 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1674347 (a : real) : (term54 a) = (a = a).
Proof. exact (@lem1674346 (a = a)). Qed.
Lemma lem1674348 (a : real) : a = a.
Proof. exact (EQ_MP (@lem1674347 a) (@lem1674344 a)). Qed.
Lemma lem1674366 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1674367 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) : (term47 _25827 _25828 _25829 _25830) = (term56 _25827 _25829 _25828 _25830).
Proof. exact (@lem1674366 ((real_mul _25827 _25828) = (real_mul _25829 _25830)) (term57 _25828 _25830)). Qed.
Lemma lem1674377 (_25827 : real) (_25829 : real) : (term58 _25827 _25829) = (term58 _25827 _25829).
Proof. exact (eq_refl (term58 _25827 _25829)). Qed.
Lemma lem1674378 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) : (term49 _25827 _25828 _25829 _25830) = (term59 _25827 _25829 _25828 _25830).
Proof. exact (MK_COMB (@lem1674377 _25827 _25829) (@lem1674367 _25827 _25829 _25828 _25830)). Qed.
Lemma lem1674382 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1674383 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) : (term59 _25827 _25829 _25828 _25830) = (term61 _25827 _25829 _25828 _25830).
Proof. exact (@lem1674382 ((real_mul _25827 _25828) = (real_mul _25829 _25830)) (term57 _25827 _25829) (term57 _25828 _25830)). Qed.
Lemma lem1674405 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) : (term49 _25827 _25828 _25829 _25830) = (term61 _25827 _25829 _25828 _25830).
Proof. exact (TRANS (@lem1674378 _25827 _25829 _25828 _25830) (@lem1674383 _25827 _25829 _25828 _25830)). Qed.
Lemma lem1674406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1674407 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) : (term62 _25827 _25828 _25829 _25830) = (term63 _25827 _25829 _25828 _25830).
Proof. exact (MK_COMB (@lem1674406) (@lem1674405 _25827 _25829 _25828 _25830)). Qed.
Lemma lem1674429 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) : (term61 _25827 _25829 _25828 _25830) = (term61 _25827 _25829 _25828 _25830).
Proof. exact (eq_refl (term61 _25827 _25829 _25828 _25830)). Qed.
Lemma lem1674430 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) : ((term49 _25827 _25828 _25829 _25830) = (term61 _25827 _25829 _25828 _25830)) = ((term61 _25827 _25829 _25828 _25830) = (term61 _25827 _25829 _25828 _25830)).
Proof. exact (MK_COMB (@lem1674407 _25827 _25829 _25828 _25830) (@lem1674429 _25827 _25829 _25828 _25830)). Qed.
Lemma lem1674432 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1674433 (x : Prop) : (x = x) = True.
Proof. exact (@lem1674432 Prop x). Qed.
Lemma lem1674434 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) : ((term61 _25827 _25829 _25828 _25830) = (term61 _25827 _25829 _25828 _25830)) = True.
Proof. exact (@lem1674433 (term61 _25827 _25829 _25828 _25830)). Qed.
Lemma lem1674435 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) : ((term49 _25827 _25828 _25829 _25830) = (term61 _25827 _25829 _25828 _25830)) = True.
Proof. exact (TRANS (@lem1674430 _25827 _25829 _25828 _25830) (@lem1674434 _25827 _25829 _25828 _25830)). Qed.
Lemma lem1674436 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) : True = ((term49 _25827 _25828 _25829 _25830) = (term61 _25827 _25829 _25828 _25830)).
Proof. exact (SYM (@lem1674435 _25827 _25829 _25828 _25830)). Qed.
Lemma lem1674437 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) : (term49 _25827 _25828 _25829 _25830) = (term61 _25827 _25829 _25828 _25830).
Proof. exact (EQ_MP (@lem1674436 _25827 _25829 _25828 _25830) (@lem0)). Qed.
Lemma lem1674438 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) : term61 _25827 _25829 _25828 _25830.
Proof. exact (EQ_MP (@lem1674437 _25827 _25829 _25828 _25830) (@lem1674314 _25827 _25828 _25829 _25830)). Qed.
Lemma lem1674440 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1674441 (_25827 : real) (_25828 : real) (_25829 : real) (_25830 : real) : (term61 _25827 _25829 _25828 _25830) = (term65 _25827 _25828 _25829 _25830).
Proof. exact (@lem1674440 (term66 _25827 _25829 _25828 _25830) ((real_mul _25827 _25828) = (real_mul _25829 _25830))). Qed.
Lemma lem1674443 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1674444 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) : (term69 _25827 _25829 _25828 _25830) = (term70 _25827 _25829 _25828 _25830).
Proof. exact (@lem1674443 (term57 _25827 _25829) (term57 _25828 _25830)). Qed.
Lemma lem1674446 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1674447 (_25827 : real) (_25829 : real) : (term72 _25827 _25829) = (_25827 = _25829).
Proof. exact (@lem1674446 (_25827 = _25829)). Qed.
Lemma lem1674448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1674449 (_25827 : real) (_25829 : real) : (term73 _25827 _25829) = (term74 _25827 _25829).
Proof. exact (MK_COMB (@lem1674448) (@lem1674447 _25827 _25829)). Qed.
Lemma lem1674451 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1674452 (_25828 : real) (_25830 : real) : (term72 _25828 _25830) = (_25828 = _25830).
Proof. exact (@lem1674451 (_25828 = _25830)). Qed.
Lemma lem1674453 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) : (term70 _25827 _25829 _25828 _25830) = (term75 _25827 _25829 _25828 _25830).
Proof. exact (MK_COMB (@lem1674449 _25827 _25829) (@lem1674452 _25828 _25830)). Qed.
Lemma lem1674454 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) : (term69 _25827 _25829 _25828 _25830) = (term75 _25827 _25829 _25828 _25830).
Proof. exact (TRANS (@lem1674444 _25827 _25829 _25828 _25830) (@lem1674453 _25827 _25829 _25828 _25830)). Qed.
Lemma lem1674455 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1674456 (_25827 : real) (_25829 : real) (_25828 : real) (_25830 : real) : (term76 _25827 _25829 _25828 _25830) = (term77 _25827 _25829 _25828 _25830).
Proof. exact (MK_COMB (@lem1674455) (@lem1674454 _25827 _25829 _25828 _25830)). Qed.
Lemma lem1674457 (_25827 : real) (_25828 : real) (_25829 : real) (_25830 : real) : ((real_mul _25827 _25828) = (real_mul _25829 _25830)) = ((real_mul _25827 _25828) = (real_mul _25829 _25830)).
Proof. exact (eq_refl ((real_mul _25827 _25828) = (real_mul _25829 _25830))). Qed.
Lemma lem1674458 (_25827 : real) (_25828 : real) (_25829 : real) (_25830 : real) : (term65 _25827 _25828 _25829 _25830) = (term78 _25827 _25828 _25829 _25830).
Proof. exact (MK_COMB (@lem1674456 _25827 _25829 _25828 _25830) (@lem1674457 _25827 _25828 _25829 _25830)). Qed.
Lemma lem1674459 (_25827 : real) (_25828 : real) (_25829 : real) (_25830 : real) : (term61 _25827 _25829 _25828 _25830) = (term78 _25827 _25828 _25829 _25830).
Proof. exact (TRANS (@lem1674441 _25827 _25828 _25829 _25830) (@lem1674458 _25827 _25828 _25829 _25830)). Qed.
Lemma lem1674461 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term79 u v a.
Proof. exact (conj (@lem1674340 u v a h1) (@lem1674348 a)). Qed.
Lemma lem1674463 (_25827 : real) (_25828 : real) (_25829 : real) (_25830 : real) : term78 _25827 _25828 _25829 _25830.
Proof. exact (EQ_MP (@lem1674459 _25827 _25828 _25829 _25830) (@lem1674438 _25827 _25829 _25828 _25830)). Qed.
Lemma lem1674464 (u : real) (v : real) (a : real) : term80 u v a.
Proof. exact (@lem1674463 (real_add u v) a term39 a). Qed.
Lemma lem1674467 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term30 u v a) = (term28 a).
Proof. exact (@lem1674464 u v a (@lem1674461 u v a h1)). Qed.
Lemma lem1674468 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term81 u v a.
Proof. exact (fun h0 : term82 u v a => @lem1674467 u v a h1). Qed.
Lemma lem1674470 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1674471 (u : real) (v : real) (a : real) : (term81 u v a) = ((term30 u v a) = (term28 a)).
Proof. exact (@lem1674470 ((term30 u v a) = (term28 a))). Qed.
Lemma lem1674472 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term30 u v a) = (term28 a).
Proof. exact (EQ_MP (@lem1674471 u v a) (@lem1674468 u v a h1)). Qed.
Lemma lem1674474 (_25817 : real) (_25818 : real) (_25819 : real) (h1 : term37) : (term30 _25817 _25818 _25819) = (term31 _25817 _25818 _25819).
Proof. exact (EQ_MP (@lem1674263 _25817 _25818 _25819) (@lem1674262 _25817 _25818 _25819 h1)). Qed.
Lemma lem1674475 (u : real) (v : real) (a : real) (h1 : term37) : (term30 u v a) = (term31 u v a).
Proof. exact (@lem1674474 u v a h1). Qed.
Lemma lem1674476 (u : real) (v : real) (a : real) (h1 : term37) : term83 u v a.
Proof. exact (fun h0 : term84 u v a => @lem1674475 u v a h1). Qed.
Lemma lem1674478 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1674479 (u : real) (v : real) (a : real) : (term83 u v a) = ((term30 u v a) = (term31 u v a)).
Proof. exact (@lem1674478 ((term30 u v a) = (term31 u v a))). Qed.
Lemma lem1674480 (u : real) (v : real) (a : real) (h1 : term37) : (term30 u v a) = (term31 u v a).
Proof. exact (EQ_MP (@lem1674479 u v a) (@lem1674476 u v a h1)). Qed.
Lemma lem1674498 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1674499 (y : real) (x : real) (z : real) : (term85 x y z) = (term86 y x z).
Proof. exact (@lem1674498 (y = z) (term57 x z)). Qed.
Lemma lem1674509 (x : real) (y : real) : (term58 x y) = (term58 x y).
Proof. exact (eq_refl (term58 x y)). Qed.
Lemma lem1674510 (y : real) (x : real) (z : real) : (term50 x y z) = (term87 y x z).
Proof. exact (MK_COMB (@lem1674509 x y) (@lem1674499 y x z)). Qed.
Lemma lem1674514 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1674515 (y : real) (x : real) (z : real) : (term87 y x z) = (term88 y x z).
Proof. exact (@lem1674514 (y = z) (term57 x y) (term57 x z)). Qed.
Lemma lem1674537 (y : real) (x : real) (z : real) : (term50 x y z) = (term88 y x z).
Proof. exact (TRANS (@lem1674510 y x z) (@lem1674515 y x z)). Qed.
Lemma lem1674538 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1674539 (y : real) (x : real) (z : real) : (term89 x y z) = (term90 y x z).
Proof. exact (MK_COMB (@lem1674538) (@lem1674537 y x z)). Qed.
Lemma lem1674561 (y : real) (x : real) (z : real) : (term88 y x z) = (term88 y x z).
Proof. exact (eq_refl (term88 y x z)). Qed.
Lemma lem1674562 (y : real) (x : real) (z : real) : ((term50 x y z) = (term88 y x z)) = ((term88 y x z) = (term88 y x z)).
Proof. exact (MK_COMB (@lem1674539 y x z) (@lem1674561 y x z)). Qed.
Lemma lem1674564 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1674565 (x : Prop) : (x = x) = True.
Proof. exact (@lem1674564 Prop x). Qed.
Lemma lem1674566 (y : real) (x : real) (z : real) : ((term88 y x z) = (term88 y x z)) = True.
Proof. exact (@lem1674565 (term88 y x z)). Qed.
Lemma lem1674567 (y : real) (x : real) (z : real) : ((term50 x y z) = (term88 y x z)) = True.
Proof. exact (TRANS (@lem1674562 y x z) (@lem1674566 y x z)). Qed.
Lemma lem1674568 (y : real) (x : real) (z : real) : True = ((term50 x y z) = (term88 y x z)).
Proof. exact (SYM (@lem1674567 y x z)). Qed.
Lemma lem1674569 (y : real) (x : real) (z : real) : (term50 x y z) = (term88 y x z).
Proof. exact (EQ_MP (@lem1674568 y x z) (@lem0)). Qed.
Lemma lem1674570 (y : real) (x : real) (z : real) : term88 y x z.
Proof. exact (EQ_MP (@lem1674569 y x z) (@lem1674331 x y z)). Qed.
Lemma lem1674572 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1674573 (x : real) (y : real) (z : real) : (term88 y x z) = (term91 x y z).
Proof. exact (@lem1674572 (term92 y x z) (y = z)). Qed.
Lemma lem1674575 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1674576 (y : real) (x : real) (z : real) : (term93 y x z) = (term94 y x z).
Proof. exact (@lem1674575 (term57 x y) (term57 x z)). Qed.
Lemma lem1674578 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1674579 (x : real) (y : real) : (term72 x y) = (x = y).
Proof. exact (@lem1674578 (x = y)). Qed.
Lemma lem1674580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1674581 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1674580) (@lem1674579 x y)). Qed.
Lemma lem1674583 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1674584 (x : real) (z : real) : (term72 x z) = (x = z).
Proof. exact (@lem1674583 (x = z)). Qed.
Lemma lem1674585 (y : real) (x : real) (z : real) : (term94 y x z) = (term95 y x z).
Proof. exact (MK_COMB (@lem1674581 x y) (@lem1674584 x z)). Qed.
Lemma lem1674586 (y : real) (x : real) (z : real) : (term93 y x z) = (term95 y x z).
Proof. exact (TRANS (@lem1674576 y x z) (@lem1674585 y x z)). Qed.
Lemma lem1674587 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1674588 (y : real) (x : real) (z : real) : (term96 y x z) = (term97 y x z).
Proof. exact (MK_COMB (@lem1674587) (@lem1674586 y x z)). Qed.
Lemma lem1674589 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1674590 (x : real) (y : real) (z : real) : (term91 x y z) = (term98 x y z).
Proof. exact (MK_COMB (@lem1674588 y x z) (@lem1674589 y z)). Qed.
Lemma lem1674591 (x : real) (y : real) (z : real) : (term88 y x z) = (term98 x y z).
Proof. exact (TRANS (@lem1674573 x y z) (@lem1674590 x y z)). Qed.
Lemma lem1674593 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term99 u v a.
Proof. exact (conj (@lem1674472 u v a h2) (@lem1674480 u v a h1)). Qed.
Lemma lem1674595 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (EQ_MP (@lem1674591 x y z) (@lem1674570 y x z)). Qed.
Lemma lem1674596 (u : real) (v : real) (a : real) : term100 u v a.
Proof. exact (@lem1674595 (term30 u v a) (term28 a) (term31 u v a)). Qed.
Lemma lem1674599 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : (term28 a) = (term31 u v a).
Proof. exact (@lem1674596 u v a (@lem1674593 u v a h1 h2)). Qed.
Lemma lem1674600 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term101 u v a.
Proof. exact (fun h0 : term102 u v a => @lem1674599 u v a h1 h2). Qed.
Lemma lem1674602 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1674603 (u : real) (v : real) (a : real) : (term101 u v a) = ((term28 a) = (term31 u v a)).
Proof. exact (@lem1674602 ((term28 a) = (term31 u v a))). Qed.
Lemma lem1674604 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : (term28 a) = (term31 u v a).
Proof. exact (EQ_MP (@lem1674603 u v a) (@lem1674600 u v a h1 h2)). Qed.
Lemma lem1674606 (_25820 : real) (h1 : term10) : (term28 _25820) = _25820.
Proof. exact (EQ_MP (@lem1674266 _25820) (@lem1674265 _25820 h1)). Qed.
Lemma lem1674607 (a : real) (h1 : term10) : (term28 a) = a.
Proof. exact (@lem1674606 a h1). Qed.
Lemma lem1674608 (a : real) (h1 : term10) : term103 a.
Proof. exact (fun h0 : term104 a => @lem1674607 a h1). Qed.
Lemma lem1674610 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1674611 (a : real) : (term103 a) = ((term28 a) = a).
Proof. exact (@lem1674610 ((term28 a) = a)). Qed.
Lemma lem1674612 (a : real) (h1 : term10) : (term28 a) = a.
Proof. exact (EQ_MP (@lem1674611 a) (@lem1674608 a h1)). Qed.
Lemma lem1674613 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term105 u v a.
Proof. exact (conj (@lem1674604 u v a h1 h3) (@lem1674612 a h2)). Qed.
Lemma lem1674615 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (EQ_MP (@lem1674591 x y z) (@lem1674570 y x z)). Qed.
Lemma lem1674616 (u : real) (v : real) (a : real) : term106 u v a.
Proof. exact (@lem1674615 (term28 a) (term31 u v a) a). Qed.
Lemma lem1674619 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : (term31 u v a) = a.
Proof. exact (@lem1674616 u v a (@lem1674613 u v a h1 h2 h3)). Qed.
Lemma lem1674620 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term107 u v a.
Proof. exact (fun h0 : term44 u v a => @lem1674619 u v a h1 h2 h3). Qed.
Lemma lem1674622 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1674623 (u : real) (v : real) (a : real) : (term107 u v a) = ((term31 u v a) = a).
Proof. exact (@lem1674622 ((term31 u v a) = a)). Qed.
Lemma lem1674624 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : (term31 u v a) = a.
Proof. exact (EQ_MP (@lem1674623 u v a) (@lem1674620 u v a h1 h2 h3)). Qed.
Lemma lem1674627 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1674629 (u : real) (v : real) (a : real) : (term44 u v a) = (term108 u v a).
Proof. exact (@lem1674627 ((term31 u v a) = a)). Qed.
Lemma lem1674632 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term108 u v a.
Proof. exact (EQ_MP (@lem1674629 u v a) (@lem1674275 u v a h1)). Qed.
Lemma lem1674635 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (@lem1674632 u v a h3 (@lem1674624 u v a h1 h2 h3)). Qed.
Lemma lem1674636 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term109.
Proof. exact (fun h0 : ~ False => @lem1674635 u v a h1 h2 h3). Qed.
Lemma lem1674638 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1674639 : term109 = False.
Proof. exact (@lem1674638 False). Qed.
Lemma lem1674640 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1674639) (@lem1674636 u v a h1 h2 h3)). Qed.
Lemma lem1674641 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1674640 u v a h1 h2 h3) (fun h4 : False => @lem1674247 h2)). Qed.
Lemma lem1674642 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1674641 u v a h1 h2 h3) (@lem1674247 h2)). Qed.
Lemma lem1674643 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1674642 u v a h1 h2 h3) (fun h4 : False => @lem1674240 h1)). Qed.
Lemma lem1674644 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1674643 u v a h1 h2 h3) (@lem1674240 h1)). Qed.
Lemma lem1674645 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1674644 u v a h1 h2 h3) (fun h4 : False => @lem1674225 h2)). Qed.
Lemma lem1674646 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1674645 u v a h1 h2 h3) (@lem1674225 h2)). Qed.
Lemma lem1674647 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1674646 u v a h1 h2 h3) (fun h4 : False => @lem1674206 h1)). Qed.
Lemma lem1674648 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1674647 u v a h1 h2 h3) (@lem1674206 h1)). Qed.
Lemma lem1674649 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1674648 u v a h1 h2 h3) (fun h4 : False => @lem1674133 h2)). Qed.
Lemma lem1674650 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1674649 u v a h1 h2 h3) (@lem1674133 h2)). Qed.
Lemma lem1674651 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1674650 u v a h1 h2 h3) (fun h4 : False => @lem1674120 h1)). Qed.
Lemma lem1674652 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1674651 u v a h1 h2 h3) (@lem1674120 h1)). Qed.
Lemma lem1674653 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term8.
Proof. exact (fun h0 : term10 => @lem1674652 u v a h1 h0 h2). Qed.
Lemma lem1674654 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1674655 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term9.
Proof. exact (EQ_MP (@lem1674654) (@lem1674653 u v a h1 h2)). Qed.
Lemma lem1674656 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term13.
Proof. exact (fun h0 : term37 => @lem1674655 u v a h0 h1). Qed.
Lemma lem1674657 (u : real) (v : real) (a : real) : term15 u v a.
Proof. exact (fun h0 : term3 u v a => @lem1674656 u v a h0). Qed.
Lemma lem1674662 (v : real) (a : real) : term19 v a.
Proof. exact (fun u : real => @lem1674657 u v a). Qed.
Lemma lem1674667 (a : real) : term23 a.
Proof. exact (fun v : real => @lem1674662 v a). Qed.
Lemma lem1674672 : term27.
Proof. exact (fun a : real => @lem1674667 a). Qed.
Lemma lem1674673 : term26.
Proof. exact (EQ_MP (@lem1674078) (@lem1674672)). Qed.
Lemma lem1674674 (a : real) : term110 a.
Proof. exact (@lem1674673 a). Qed.
Lemma lem1674675 (a : real) : (term110 a) = (term22 a).
Proof. exact (eq_refl (term110 a)). Qed.
Lemma lem1674676 (a : real) : term22 a.
Proof. exact (EQ_MP (@lem1674675 a) (@lem1674674 a)). Qed.
Lemma lem1674677 (a : real) (v : real) : term111 a v.
Proof. exact (@lem1674676 a v). Qed.
Lemma lem1674678 (v : real) (a : real) : (term111 a v) = (term18 v a).
Proof. exact (eq_refl (term111 a v)). Qed.
Lemma lem1674679 (v : real) (a : real) : term18 v a.
Proof. exact (EQ_MP (@lem1674678 v a) (@lem1674677 a v)). Qed.
Lemma lem1674680 (v : real) (a : real) (u : real) : term112 v a u.
Proof. exact (@lem1674679 v a u). Qed.
Lemma lem1674681 (u : real) (v : real) (a : real) : (term112 v a u) = (term4 u v a).
Proof. exact (eq_refl (term112 v a u)). Qed.
Lemma lem1674682 (u : real) (v : real) (a : real) : term4 u v a.
Proof. exact (EQ_MP (@lem1674681 u v a) (@lem1674680 v a u)). Qed.
Lemma lem1674684 (u : real) (v : real) (a : real) : term4 u v a.
Proof. exact (@lem1673918 u v a (@lem1674682 u v a)). Qed.
Lemma lem1674685 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term12.
Proof. exact (@lem1674684 u v a (@lem1673903 u v a h1)). Qed.
Lemma lem1674686 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term8.
Proof. exact (@lem1674685 u v a h1 (@lem1487144)). Qed.
Lemma lem1674687 (u : real) (v : real) (a : real) (h1 : term3 u v a) : False.
Proof. exact (@lem1674686 u v a h1 (@lem1338986)). Qed.
Lemma lem1674688 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term3 u v a) = False.
Proof. exact (prop_ext (fun h2 : term3 u v a => @lem1674687 u v a h1) (fun h2 : False => @lem1673903 u v a h1)). Qed.
Lemma lem1674689 (u : real) (v : real) (a : real) (h1 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1674688 u v a h1) (@lem1673903 u v a h1)). Qed.
Lemma lem1674690 (u : real) (v : real) (a : real) : term2 u v a.
Proof. exact (fun h0 : term3 u v a => @lem1674689 u v a h0). Qed.
Lemma lem1674691 (u : real) (v : real) (a : real) : term1 u v a.
Proof. exact (EQ_MP (@lem1673902 u v a) (@lem1674690 u v a)). Qed.
Lemma lem1674692 (t1 : Prop) : term113 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1674693 (t1 : Prop) : (term113 t1) = (term114 t1).
Proof. exact (eq_refl (term113 t1)). Qed.
Lemma lem1674694 (t1 : Prop) : term114 t1.
Proof. exact (EQ_MP (@lem1674693 t1) (@lem1674692 t1)). Qed.
Lemma lem1674695 (t1 : Prop) (t2 : Prop) : term115 t1 t2.
Proof. exact (@lem1674694 t1 t2). Qed.
Lemma lem1674696 (t1 : Prop) (t2 : Prop) : (term115 t1 t2) = (term116 t1 t2).
Proof. exact (eq_refl (term115 t1 t2)). Qed.
Lemma lem1674697 (t1 : Prop) (t2 : Prop) : term116 t1 t2.
Proof. exact (EQ_MP (@lem1674696 t1 t2) (@lem1674695 t1 t2)). Qed.
Lemma lem1674698 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term117 t1 t2 t3.
Proof. exact (@lem1674697 t1 t2 t3). Qed.
Lemma lem1674699 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term117 t1 t2 t3) = ((term60 t1 t2 t3) = (term118 t1 t2 t3)).
Proof. exact (eq_refl (term117 t1 t2 t3)). Qed.
Lemma lem1674700 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term60 t1 t2 t3) = (term118 t1 t2 t3).
Proof. exact (EQ_MP (@lem1674699 t1 t2 t3) (@lem1674698 t1 t2 t3)). Qed.
Lemma lem1674701 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term118 t1 t2 t3) = (term60 t1 t2 t3).
Proof. exact (SYM (@lem1674700 t1 t2 t3)). Qed.
Lemma lem1674702 : term119.
Proof. exact (fun b : real => @lem1672514 b). Qed.
Lemma lem1674703 (u : real) (v : real) : term120 u v.
Proof. exact (fun a : real => @lem1674691 u v a). Qed.
Lemma lem1674704 (u : real) : term121 u.
Proof. exact (fun v : real => @lem1674703 u v). Qed.
Lemma lem1674705 : term122.
Proof. exact (fun u : real => @lem1674704 u). Qed.
Lemma lem1674707 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1674708 : term123 = term124.
Proof. exact (@lem1674707 term123). Qed.
Lemma lem1674709 : term124 = term123.
Proof. exact (SYM (@lem1674708)). Qed.
Lemma lem1674710 (h1 : term125) : term125.
Proof. exact (h1). Qed.
Lemma lem1674713 (h1 : term126) : term126.
Proof. exact (h1). Qed.
Lemma lem1674714 : term127.
Proof. exact (fun h0 : term126 => @lem1674713 h0). Qed.
Lemma lem1674715 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem1674716 (h1 : term126) : term126.
Proof. exact (h1). Qed.
Lemma lem1674717 (h1 : term126) (h2 : term127) : term126.
Proof. exact (@lem1674715 h2 (@lem1674716 h1)). Qed.
Lemma lem1674718 (h1 : term126) : term128.
Proof. exact (fun h0 : term127 => @lem1674717 h1 h0). Qed.
Lemma lem1674719 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem1674720 (h1 : term126) (h2 : term127) : term126.
Proof. exact (@lem1674718 h1 (@lem1674719 h2)). Qed.
Lemma lem1674721 (h1 : term127) : term127.
Proof. exact (fun h0 : term126 => @lem1674720 h0 h1). Qed.
Lemma lem1674722 : term129.
Proof. exact (fun h0 : term127 => @lem1674721 h0). Qed.
Lemma lem1674725 : term127.
Proof. exact (@lem1674722 (@lem1674714)). Qed.
Lemma lem1674775 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1674776 : term130 = term131.
Proof. exact (@lem1674775 term119). Qed.
Lemma lem1674811 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem1674812 : term133 = term134.
Proof. exact (MK_COMB (@lem1674811) (@lem1674776)). Qed.
Lemma lem1674815 : term135 = term135.
Proof. exact (eq_refl term135). Qed.
Lemma lem1674822 : term126 = term136.
Proof. exact (MK_COMB (@lem1674815) (@lem1674812)). Qed.
Lemma lem1674843 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term137 x y u a v b).
Proof. exact (eq_refl (term137 x y u a v b)). Qed.
Lemma lem1674844 (x : real) (y : real) (u : real) (a : real) (b : real) : (term138 x y u a b) = (term138 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1674843 x y u a v b)). Qed.
Lemma lem1674845 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674846 (x : real) (y : real) (u : real) (a : real) (b : real) : (term139 x y u a b) = (term139 x y u a b).
Proof. exact (MK_COMB (@lem1674845) (@lem1674844 x y u a b)). Qed.
Lemma lem1674847 (x : real) (y : real) (a : real) (b : real) : (term140 x y a b) = (term140 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1674846 x y u a b)). Qed.
Lemma lem1674848 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674849 (x : real) (y : real) (a : real) (b : real) : (term141 x y a b) = (term141 x y a b).
Proof. exact (MK_COMB (@lem1674848) (@lem1674847 x y a b)). Qed.
Lemma lem1674850 (x : real) (y : real) (b : real) : (term142 x y b) = (term142 x y b).
Proof. exact (fun_ext (fun a : real => @lem1674849 x y a b)). Qed.
Lemma lem1674851 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674852 (x : real) (y : real) (b : real) : (term143 x y b) = (term143 x y b).
Proof. exact (MK_COMB (@lem1674851) (@lem1674850 x y b)). Qed.
Lemma lem1674853 (x : real) (b : real) : (term144 x b) = (term144 x b).
Proof. exact (fun_ext (fun y : real => @lem1674852 x y b)). Qed.
Lemma lem1674854 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674855 (x : real) (b : real) : (term145 x b) = (term145 x b).
Proof. exact (MK_COMB (@lem1674854) (@lem1674853 x b)). Qed.
Lemma lem1674856 (b : real) : (term146 b) = (term146 b).
Proof. exact (fun_ext (fun x : real => @lem1674855 x b)). Qed.
Lemma lem1674857 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674858 (b : real) : (term147 b) = (term147 b).
Proof. exact (MK_COMB (@lem1674857) (@lem1674856 b)). Qed.
Lemma lem1674859 : term148 = term148.
Proof. exact (fun_ext (fun b : real => @lem1674858 b)). Qed.
Lemma lem1674860 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674861 : term119 = term119.
Proof. exact (MK_COMB (@lem1674860) (@lem1674859)). Qed.
Lemma lem1674862 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1674863 : term131 = term131.
Proof. exact (MK_COMB (@lem1674862) (@lem1674861)). Qed.
Lemma lem1674868 (u : real) (v : real) (a : real) : (term1 u v a) = (term1 u v a).
Proof. exact (eq_refl (term1 u v a)). Qed.
Lemma lem1674869 (u : real) (v : real) : (term149 u v) = (term149 u v).
Proof. exact (fun_ext (fun a : real => @lem1674868 u v a)). Qed.
Lemma lem1674870 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674871 (u : real) (v : real) : (term120 u v) = (term120 u v).
Proof. exact (MK_COMB (@lem1674870) (@lem1674869 u v)). Qed.
Lemma lem1674872 (u : real) : (term150 u) = (term150 u).
Proof. exact (fun_ext (fun v : real => @lem1674871 u v)). Qed.
Lemma lem1674873 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674874 (u : real) : (term121 u) = (term121 u).
Proof. exact (MK_COMB (@lem1674873) (@lem1674872 u)). Qed.
Lemma lem1674875 : term151 = term151.
Proof. exact (fun_ext (fun u : real => @lem1674874 u)). Qed.
Lemma lem1674876 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674877 : term122 = term122.
Proof. exact (MK_COMB (@lem1674876) (@lem1674875)). Qed.
Lemma lem1674878 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1674879 : term132 = term132.
Proof. exact (MK_COMB (@lem1674878) (@lem1674877)). Qed.
Lemma lem1674880 : term134 = term134.
Proof. exact (MK_COMB (@lem1674879) (@lem1674863)). Qed.
Lemma lem1674901 (u : real) (x : real) (v : real) (y : real) (a : real) : (term152 u x v y a) = (term152 u x v y a).
Proof. exact (eq_refl (term152 u x v y a)). Qed.
Lemma lem1674902 (u : real) (x : real) (y : real) (a : real) : (term153 u x y a) = (term153 u x y a).
Proof. exact (fun_ext (fun v : real => @lem1674901 u x v y a)). Qed.
Lemma lem1674903 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674904 (u : real) (x : real) (y : real) (a : real) : (term154 u x y a) = (term154 u x y a).
Proof. exact (MK_COMB (@lem1674903) (@lem1674902 u x y a)). Qed.
Lemma lem1674905 (x : real) (y : real) (a : real) : (term155 x y a) = (term155 x y a).
Proof. exact (fun_ext (fun u : real => @lem1674904 u x y a)). Qed.
Lemma lem1674906 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674907 (x : real) (y : real) (a : real) : (term156 x y a) = (term156 x y a).
Proof. exact (MK_COMB (@lem1674906) (@lem1674905 x y a)). Qed.
Lemma lem1674908 (x : real) (y : real) : (term157 x y) = (term157 x y).
Proof. exact (fun_ext (fun a : real => @lem1674907 x y a)). Qed.
Lemma lem1674909 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674910 (x : real) (y : real) : (term158 x y) = (term158 x y).
Proof. exact (MK_COMB (@lem1674909) (@lem1674908 x y)). Qed.
Lemma lem1674911 (x : real) : (term159 x) = (term159 x).
Proof. exact (fun_ext (fun y : real => @lem1674910 x y)). Qed.
Lemma lem1674912 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674913 (x : real) : (term160 x) = (term160 x).
Proof. exact (MK_COMB (@lem1674912) (@lem1674911 x)). Qed.
Lemma lem1674914 : term161 = term161.
Proof. exact (fun_ext (fun x : real => @lem1674913 x)). Qed.
Lemma lem1674915 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1674916 : term123 = term123.
Proof. exact (MK_COMB (@lem1674915) (@lem1674914)). Qed.
Lemma lem1674917 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1674918 : term125 = term125.
Proof. exact (MK_COMB (@lem1674917) (@lem1674916)). Qed.
Lemma lem1674919 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1674920 : term135 = term135.
Proof. exact (MK_COMB (@lem1674919) (@lem1674918)). Qed.
Lemma lem1674921 : term136 = term136.
Proof. exact (MK_COMB (@lem1674920) (@lem1674880)). Qed.
Lemma lem1675034 : term126 = term136.
Proof. exact (TRANS (@lem1674822) (@lem1674921)). Qed.
Lemma lem1675035 : term136 = term126.
Proof. exact (SYM (@lem1675034)). Qed.
Lemma lem1675036 (h1 : term125) : term125.
Proof. exact (h1). Qed.
Lemma lem1675037 (h1 : term122) : term122.
Proof. exact (h1). Qed.
Lemma lem1675038 (h1 : term119) : term119.
Proof. exact (h1). Qed.
Lemma lem1675061 (u : real) (x : real) (v : real) (y : real) (a : real) : (term162 u x v y a) = (term163 u x v y a).
Proof. exact (@lem17362 (term164 x y a u v) (term165 u x v y a)). Qed.
Lemma lem1675062 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1675063 (u : real) (x : real) (y : real) (a : real) : (term168 u x y a) = (term169 u x y a).
Proof. exact (@lem1675062 (term153 u x y a)). Qed.
Lemma lem1675064 (u : real) (x : real) (v : real) (y : real) (a : real) : (term170 u x y a v) = (term152 u x v y a).
Proof. exact (eq_refl (term170 u x y a v)). Qed.
Lemma lem1675065 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1675066 (u : real) (x : real) (v : real) (y : real) (a : real) : (term171 u x y a v) = (term162 u x v y a).
Proof. exact (MK_COMB (@lem1675065) (@lem1675064 u x v y a)). Qed.
Lemma lem1675067 (u : real) (x : real) (v : real) (y : real) (a : real) : (term171 u x y a v) = (term163 u x v y a).
Proof. exact (TRANS (@lem1675066 u x v y a) (@lem1675061 u x v y a)). Qed.
Lemma lem1675068 (u : real) (x : real) (y : real) (a : real) : (term172 u x y a) = (term173 u x y a).
Proof. exact (fun_ext (fun v : real => @lem1675067 u x v y a)). Qed.
Lemma lem1675069 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1675070 (u : real) (x : real) (y : real) (a : real) : (term169 u x y a) = (term174 u x y a).
Proof. exact (MK_COMB (@lem1675069) (@lem1675068 u x y a)). Qed.
Lemma lem1675071 (u : real) (x : real) (y : real) (a : real) : (term168 u x y a) = (term174 u x y a).
Proof. exact (TRANS (@lem1675063 u x y a) (@lem1675070 u x y a)). Qed.
Lemma lem1675072 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1675073 (x : real) (y : real) (a : real) : (term175 x y a) = (term176 x y a).
Proof. exact (@lem1675072 (term155 x y a)). Qed.
Lemma lem1675074 (u : real) (x : real) (y : real) (a : real) : (term177 x y a u) = (term154 u x y a).
Proof. exact (eq_refl (term177 x y a u)). Qed.
Lemma lem1675075 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1675076 (u : real) (x : real) (y : real) (a : real) : (term178 x y a u) = (term168 u x y a).
Proof. exact (MK_COMB (@lem1675075) (@lem1675074 u x y a)). Qed.
Lemma lem1675077 (u : real) (x : real) (y : real) (a : real) : (term178 x y a u) = (term174 u x y a).
Proof. exact (TRANS (@lem1675076 u x y a) (@lem1675071 u x y a)). Qed.
Lemma lem1675078 (x : real) (y : real) (a : real) : (term179 x y a) = (term180 x y a).
Proof. exact (fun_ext (fun u : real => @lem1675077 u x y a)). Qed.
Lemma lem1675079 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1675080 (x : real) (y : real) (a : real) : (term176 x y a) = (term181 x y a).
Proof. exact (MK_COMB (@lem1675079) (@lem1675078 x y a)). Qed.
Lemma lem1675081 (x : real) (y : real) (a : real) : (term175 x y a) = (term181 x y a).
Proof. exact (TRANS (@lem1675073 x y a) (@lem1675080 x y a)). Qed.
Lemma lem1675082 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1675083 (x : real) (y : real) : (term182 x y) = (term183 x y).
Proof. exact (@lem1675082 (term157 x y)). Qed.
Lemma lem1675084 (x : real) (y : real) (a : real) : (term184 x y a) = (term156 x y a).
Proof. exact (eq_refl (term184 x y a)). Qed.
Lemma lem1675085 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1675086 (x : real) (y : real) (a : real) : (term185 x y a) = (term175 x y a).
Proof. exact (MK_COMB (@lem1675085) (@lem1675084 x y a)). Qed.
Lemma lem1675087 (x : real) (y : real) (a : real) : (term185 x y a) = (term181 x y a).
Proof. exact (TRANS (@lem1675086 x y a) (@lem1675081 x y a)). Qed.
Lemma lem1675088 (x : real) (y : real) : (term186 x y) = (term187 x y).
Proof. exact (fun_ext (fun a : real => @lem1675087 x y a)). Qed.
Lemma lem1675089 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1675090 (x : real) (y : real) : (term183 x y) = (term188 x y).
Proof. exact (MK_COMB (@lem1675089) (@lem1675088 x y)). Qed.
Lemma lem1675091 (x : real) (y : real) : (term182 x y) = (term188 x y).
Proof. exact (TRANS (@lem1675083 x y) (@lem1675090 x y)). Qed.
Lemma lem1675092 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1675093 (x : real) : (term189 x) = (term190 x).
Proof. exact (@lem1675092 (term159 x)). Qed.
Lemma lem1675094 (x : real) (y : real) : (term191 x y) = (term158 x y).
Proof. exact (eq_refl (term191 x y)). Qed.
Lemma lem1675095 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1675096 (x : real) (y : real) : (term192 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1675095) (@lem1675094 x y)). Qed.
Lemma lem1675097 (x : real) (y : real) : (term192 x y) = (term188 x y).
Proof. exact (TRANS (@lem1675096 x y) (@lem1675091 x y)). Qed.
Lemma lem1675098 (x : real) : (term193 x) = (term194 x).
Proof. exact (fun_ext (fun y : real => @lem1675097 x y)). Qed.
Lemma lem1675099 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1675100 (x : real) : (term190 x) = (term195 x).
Proof. exact (MK_COMB (@lem1675099) (@lem1675098 x)). Qed.
Lemma lem1675101 (x : real) : (term189 x) = (term195 x).
Proof. exact (TRANS (@lem1675093 x) (@lem1675100 x)). Qed.
Lemma lem1675102 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1675103 : term125 = term196.
Proof. exact (@lem1675102 term161). Qed.
Lemma lem1675104 (x : real) : (term197 x) = (term160 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem1675105 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1675106 (x : real) : (term198 x) = (term189 x).
Proof. exact (MK_COMB (@lem1675105) (@lem1675104 x)). Qed.
Lemma lem1675107 (x : real) : (term198 x) = (term195 x).
Proof. exact (TRANS (@lem1675106 x) (@lem1675101 x)). Qed.
Lemma lem1675108 : term199 = term200.
Proof. exact (fun_ext (fun x : real => @lem1675107 x)). Qed.
Lemma lem1675109 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1675110 : term196 = term201.
Proof. exact (MK_COMB (@lem1675109) (@lem1675108)). Qed.
Lemma lem1675179 : term125 = term201.
Proof. exact (TRANS (@lem1675103) (@lem1675110)). Qed.
Lemma lem1675180 (h1 : term125) : term201.
Proof. exact (EQ_MP (@lem1675179) (@lem1675036 h1)). Qed.
Lemma lem1675187 (u : real) (v : real) (a : real) : (term1 u v a) = (term202 u v a).
Proof. exact (@lem17265 ((real_add u v) = term39) ((term31 u v a) = a)). Qed.
Lemma lem1675188 (u : real) (v : real) : (term149 u v) = (term203 u v).
Proof. exact (fun_ext (fun a : real => @lem1675187 u v a)). Qed.
Lemma lem1675189 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675190 (u : real) (v : real) : (term120 u v) = (term204 u v).
Proof. exact (MK_COMB (@lem1675189) (@lem1675188 u v)). Qed.
Lemma lem1675191 (u : real) : (term150 u) = (term205 u).
Proof. exact (fun_ext (fun v : real => @lem1675190 u v)). Qed.
Lemma lem1675192 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675193 (u : real) : (term121 u) = (term206 u).
Proof. exact (MK_COMB (@lem1675192) (@lem1675191 u)). Qed.
Lemma lem1675194 : term151 = term207.
Proof. exact (fun_ext (fun u : real => @lem1675193 u)). Qed.
Lemma lem1675195 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675196 : term122 = term208.
Proof. exact (MK_COMB (@lem1675195) (@lem1675194)). Qed.
Lemma lem1675206 {A : Type'} (P : Prop) (Q : A -> Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem1675207 (P : Prop) (Q : real -> Prop) : (term211 P Q) = (term212 P Q).
Proof. exact (@lem1675206 real P Q). Qed.
Lemma lem1675208 (u : real) (v : real) : (term213 u v) = (term214 u v).
Proof. exact (@lem1675207 (term52 u v) (term215 u v)). Qed.
Lemma lem1675209 (u : real) (v : real) (a : real) : (term216 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term216 u v a)). Qed.
Lemma lem1675210 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1675211 (u : real) (v : real) (a : real) : (term218 u v a) = (term202 u v a).
Proof. exact (MK_COMB (@lem1675210 u v) (@lem1675209 u v a)). Qed.
Lemma lem1675212 (u : real) (v : real) : (term219 u v) = (term203 u v).
Proof. exact (fun_ext (fun a : real => @lem1675211 u v a)). Qed.
Lemma lem1675213 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675214 (u : real) (v : real) : (term213 u v) = (term204 u v).
Proof. exact (MK_COMB (@lem1675213) (@lem1675212 u v)). Qed.
Lemma lem1675215 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1675216 (u : real) (v : real) : (term220 u v) = (term221 u v).
Proof. exact (MK_COMB (@lem1675215) (@lem1675214 u v)). Qed.
Lemma lem1675217 (u : real) (v : real) (a : real) : (term216 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term216 u v a)). Qed.
Lemma lem1675218 (u : real) (v : real) : (term222 u v) = (term215 u v).
Proof. exact (fun_ext (fun a : real => @lem1675217 u v a)). Qed.
Lemma lem1675219 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675220 (u : real) (v : real) : (term223 u v) = (term224 u v).
Proof. exact (MK_COMB (@lem1675219) (@lem1675218 u v)). Qed.
Lemma lem1675221 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1675222 (u : real) (v : real) : (term214 u v) = (term225 u v).
Proof. exact (MK_COMB (@lem1675221 u v) (@lem1675220 u v)). Qed.
Lemma lem1675223 (u : real) (v : real) : ((term213 u v) = (term214 u v)) = ((term204 u v) = (term225 u v)).
Proof. exact (MK_COMB (@lem1675216 u v) (@lem1675222 u v)). Qed.
Lemma lem1675224 (u : real) (v : real) : (term204 u v) = (term225 u v).
Proof. exact (EQ_MP (@lem1675223 u v) (@lem1675208 u v)). Qed.
Lemma lem1675229 (u : real) : (term205 u) = (term226 u).
Proof. exact (fun_ext (fun v : real => @lem1675224 u v)). Qed.
Lemma lem1675230 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675231 (u : real) : (term206 u) = (term227 u).
Proof. exact (MK_COMB (@lem1675230) (@lem1675229 u)). Qed.
Lemma lem1675280 : term207 = term228.
Proof. exact (fun_ext (fun u : real => @lem1675231 u)). Qed.
Lemma lem1675281 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675288 : term208 = term229.
Proof. exact (MK_COMB (@lem1675281) (@lem1675280)). Qed.
Lemma lem1675289 : term122 = term229.
Proof. exact (TRANS (@lem1675196) (@lem1675288)). Qed.
Lemma lem1675290 (h1 : term122) : term229.
Proof. exact (EQ_MP (@lem1675289) (@lem1675037 h1)). Qed.
Lemma lem1675300 (u : real) (v : real) : (term230 u v) = (term231 u v).
Proof. exact (@lem17045 (term232 v) ((real_add u v) = term39)). Qed.
Lemma lem1675302 (u : real) : (term233 u) = (term233 u).
Proof. exact (eq_refl (term233 u)). Qed.
Lemma lem1675303 (u : real) (v : real) : (term234 u v) = (term235 u v).
Proof. exact (MK_COMB (@lem1675302 u) (@lem1675300 u v)). Qed.
Lemma lem1675304 (u : real) (v : real) : (term236 u v) = (term234 u v).
Proof. exact (@lem17045 (term232 u) (term237 u v)). Qed.
Lemma lem1675305 (u : real) (v : real) : (term236 u v) = (term235 u v).
Proof. exact (TRANS (@lem1675304 u v) (@lem1675303 u v)). Qed.
Lemma lem1675307 (y : real) (b : real) : (term238 y b) = (term238 y b).
Proof. exact (eq_refl (term238 y b)). Qed.
Lemma lem1675308 (y : real) (b : real) (u : real) (v : real) : (term239 y b u v) = (term240 y b u v).
Proof. exact (MK_COMB (@lem1675307 y b) (@lem1675305 u v)). Qed.
Lemma lem1675309 (y : real) (b : real) (u : real) (v : real) : (term241 y b u v) = (term239 y b u v).
Proof. exact (@lem17045 (real_lt y b) (term242 u v)). Qed.
Lemma lem1675310 (y : real) (b : real) (u : real) (v : real) : (term241 y b u v) = (term240 y b u v).
Proof. exact (TRANS (@lem1675309 y b u v) (@lem1675308 y b u v)). Qed.
Lemma lem1675312 (x : real) (a : real) : (term238 x a) = (term238 x a).
Proof. exact (eq_refl (term238 x a)). Qed.
Lemma lem1675313 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term243 x a y b u v) = (term244 x a y b u v).
Proof. exact (MK_COMB (@lem1675312 x a) (@lem1675310 y b u v)). Qed.
Lemma lem1675314 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term245 x a y b u v) = (term243 x a y b u v).
Proof. exact (@lem17045 (real_lt x a) (term246 y b u v)). Qed.
Lemma lem1675315 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term245 x a y b u v) = (term244 x a y b u v).
Proof. exact (TRANS (@lem1675314 x a y b u v) (@lem1675313 x a y b u v)). Qed.
Lemma lem1675316 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term247 x y u a v b) = (term247 x y u a v b).
Proof. exact (eq_refl (term247 x y u a v b)). Qed.
Lemma lem1675317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1675318 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term248 x a y b u v) = (term249 x a y b u v).
Proof. exact (MK_COMB (@lem1675317) (@lem1675315 x a y b u v)). Qed.
Lemma lem1675319 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term250 x y u a v b) = (term251 x y u a v b).
Proof. exact (MK_COMB (@lem1675318 x a y b u v) (@lem1675316 x y u a v b)). Qed.
Lemma lem1675320 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term250 x y u a v b).
Proof. exact (@lem17265 (term252 x a y b u v) (term247 x y u a v b)). Qed.
Lemma lem1675321 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term251 x y u a v b).
Proof. exact (TRANS (@lem1675320 x y u a v b) (@lem1675319 x y u a v b)). Qed.
Lemma lem1675322 (x : real) (y : real) (u : real) (a : real) (b : real) : (term138 x y u a b) = (term253 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1675321 x y u a v b)). Qed.
Lemma lem1675323 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675324 (x : real) (y : real) (u : real) (a : real) (b : real) : (term139 x y u a b) = (term254 x y u a b).
Proof. exact (MK_COMB (@lem1675323) (@lem1675322 x y u a b)). Qed.
Lemma lem1675325 (x : real) (y : real) (a : real) (b : real) : (term140 x y a b) = (term255 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1675324 x y u a b)). Qed.
Lemma lem1675326 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675327 (x : real) (y : real) (a : real) (b : real) : (term141 x y a b) = (term256 x y a b).
Proof. exact (MK_COMB (@lem1675326) (@lem1675325 x y a b)). Qed.
Lemma lem1675328 (x : real) (y : real) (b : real) : (term142 x y b) = (term257 x y b).
Proof. exact (fun_ext (fun a : real => @lem1675327 x y a b)). Qed.
Lemma lem1675329 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675330 (x : real) (y : real) (b : real) : (term143 x y b) = (term258 x y b).
Proof. exact (MK_COMB (@lem1675329) (@lem1675328 x y b)). Qed.
Lemma lem1675331 (x : real) (b : real) : (term144 x b) = (term259 x b).
Proof. exact (fun_ext (fun y : real => @lem1675330 x y b)). Qed.
Lemma lem1675332 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675333 (x : real) (b : real) : (term145 x b) = (term260 x b).
Proof. exact (MK_COMB (@lem1675332) (@lem1675331 x b)). Qed.
Lemma lem1675334 (b : real) : (term146 b) = (term261 b).
Proof. exact (fun_ext (fun x : real => @lem1675333 x b)). Qed.
Lemma lem1675335 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675336 (b : real) : (term147 b) = (term262 b).
Proof. exact (MK_COMB (@lem1675335) (@lem1675334 b)). Qed.
Lemma lem1675337 : term148 = term263.
Proof. exact (fun_ext (fun b : real => @lem1675336 b)). Qed.
Lemma lem1675338 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675411 : term119 = term264.
Proof. exact (MK_COMB (@lem1675338) (@lem1675337)). Qed.
Lemma lem1675412 (h1 : term119) : term264.
Proof. exact (EQ_MP (@lem1675411) (@lem1675038 h1)). Qed.
Lemma lem1675413 (x : real) (h1 : term195 x) : term195 x.
Proof. exact (h1). Qed.
Lemma lem1675414 (x : real) (y : real) (h1 : term188 x y) : term188 x y.
Proof. exact (h1). Qed.
Lemma lem1675415 (x : real) (y : real) (a : real) (h1 : term181 x y a) : term181 x y a.
Proof. exact (h1). Qed.
Lemma lem1675416 (u : real) (x : real) (y : real) (a : real) (h1 : term174 u x y a) : term174 u x y a.
Proof. exact (h1). Qed.
Lemma lem1675434 (u : real) (v : real) (a : real) : ((term31 u v a) = a) = ((term31 u v a) = a).
Proof. exact (eq_refl ((term31 u v a) = a)). Qed.
Lemma lem1675435 (u : real) (v : real) : (term215 u v) = (term215 u v).
Proof. exact (fun_ext (fun a : real => @lem1675434 u v a)). Qed.
Lemma lem1675436 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675437 (u : real) (v : real) : (term224 u v) = (term224 u v).
Proof. exact (MK_COMB (@lem1675436) (@lem1675435 u v)). Qed.
Lemma lem1675456 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1675457 (u : real) (v : real) : (term225 u v) = (term225 u v).
Proof. exact (MK_COMB (@lem1675456 u v) (@lem1675437 u v)). Qed.
Lemma lem1675458 (u : real) : (term226 u) = (term226 u).
Proof. exact (fun_ext (fun v : real => @lem1675457 u v)). Qed.
Lemma lem1675459 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675460 (u : real) : (term227 u) = (term227 u).
Proof. exact (MK_COMB (@lem1675459) (@lem1675458 u)). Qed.
Lemma lem1675461 : term228 = term228.
Proof. exact (fun_ext (fun u : real => @lem1675460 u)). Qed.
Lemma lem1675462 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675463 : term229 = term229.
Proof. exact (MK_COMB (@lem1675462) (@lem1675461)). Qed.
Lemma lem1675464 (h1 : term122) : term229.
Proof. exact (EQ_MP (@lem1675463) (@lem1675290 h1)). Qed.
Lemma lem1675561 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term251 x y u a v b) = (term251 x y u a v b).
Proof. exact (eq_refl (term251 x y u a v b)). Qed.
Lemma lem1675562 (x : real) (y : real) (u : real) (a : real) (b : real) : (term253 x y u a b) = (term253 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1675561 x y u a v b)). Qed.
Lemma lem1675563 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675564 (x : real) (y : real) (u : real) (a : real) (b : real) : (term254 x y u a b) = (term254 x y u a b).
Proof. exact (MK_COMB (@lem1675563) (@lem1675562 x y u a b)). Qed.
Lemma lem1675565 (x : real) (y : real) (a : real) (b : real) : (term255 x y a b) = (term255 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1675564 x y u a b)). Qed.
Lemma lem1675566 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675567 (x : real) (y : real) (a : real) (b : real) : (term256 x y a b) = (term256 x y a b).
Proof. exact (MK_COMB (@lem1675566) (@lem1675565 x y a b)). Qed.
Lemma lem1675568 (x : real) (y : real) (b : real) : (term257 x y b) = (term257 x y b).
Proof. exact (fun_ext (fun a : real => @lem1675567 x y a b)). Qed.
Lemma lem1675569 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675570 (x : real) (y : real) (b : real) : (term258 x y b) = (term258 x y b).
Proof. exact (MK_COMB (@lem1675569) (@lem1675568 x y b)). Qed.
Lemma lem1675571 (x : real) (b : real) : (term259 x b) = (term259 x b).
Proof. exact (fun_ext (fun y : real => @lem1675570 x y b)). Qed.
Lemma lem1675572 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675573 (x : real) (b : real) : (term260 x b) = (term260 x b).
Proof. exact (MK_COMB (@lem1675572) (@lem1675571 x b)). Qed.
Lemma lem1675574 (b : real) : (term261 b) = (term261 b).
Proof. exact (fun_ext (fun x : real => @lem1675573 x b)). Qed.
Lemma lem1675575 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675576 (b : real) : (term262 b) = (term262 b).
Proof. exact (MK_COMB (@lem1675575) (@lem1675574 b)). Qed.
Lemma lem1675577 : term263 = term263.
Proof. exact (fun_ext (fun b : real => @lem1675576 b)). Qed.
Lemma lem1675578 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675579 : term264 = term264.
Proof. exact (MK_COMB (@lem1675578) (@lem1675577)). Qed.
Lemma lem1675580 (h1 : term119) : term264.
Proof. exact (EQ_MP (@lem1675579) (@lem1675412 h1)). Qed.
Lemma lem1675658 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term163 u x v y a.
Proof. exact (h1). Qed.
Lemma lem1675660 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term164 x y a u v.
Proof. exact (proj1 (@lem1675658 u x v y a h1)). Qed.
Lemma lem1675661 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term246 y a u v.
Proof. exact (proj2 (@lem1675660 u x v y a h1)). Qed.
Lemma lem1675663 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term242 u v.
Proof. exact (proj2 (@lem1675661 u x v y a h1)). Qed.
Lemma lem1675665 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term237 u v.
Proof. exact (proj2 (@lem1675663 u x v y a h1)). Qed.
Lemma lem1675670 {A : Type'} (P : Prop) (Q : A -> Prop) : (term210 A P Q) = (term209 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1675671 (P : Prop) (Q : real -> Prop) : (term212 P Q) = (term211 P Q).
Proof. exact (@lem1675670 real P Q). Qed.
Lemma lem1675672 (u : real) (v : real) : (term214 u v) = (term213 u v).
Proof. exact (@lem1675671 (term52 u v) (term215 u v)). Qed.
Lemma lem1675673 (u : real) (v : real) (a : real) : (term216 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term216 u v a)). Qed.
Lemma lem1675674 (u : real) (v : real) : (term222 u v) = (term215 u v).
Proof. exact (fun_ext (fun a : real => @lem1675673 u v a)). Qed.
Lemma lem1675675 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675676 (u : real) (v : real) : (term223 u v) = (term224 u v).
Proof. exact (MK_COMB (@lem1675675) (@lem1675674 u v)). Qed.
Lemma lem1675677 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1675678 (u : real) (v : real) : (term214 u v) = (term225 u v).
Proof. exact (MK_COMB (@lem1675677 u v) (@lem1675676 u v)). Qed.
Lemma lem1675679 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1675680 (u : real) (v : real) : (term265 u v) = (term266 u v).
Proof. exact (MK_COMB (@lem1675679) (@lem1675678 u v)). Qed.
Lemma lem1675681 (u : real) (v : real) (a : real) : (term216 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term216 u v a)). Qed.
Lemma lem1675682 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1675683 (u : real) (v : real) (a : real) : (term218 u v a) = (term202 u v a).
Proof. exact (MK_COMB (@lem1675682 u v) (@lem1675681 u v a)). Qed.
Lemma lem1675684 (u : real) (v : real) : (term219 u v) = (term203 u v).
Proof. exact (fun_ext (fun a : real => @lem1675683 u v a)). Qed.
Lemma lem1675685 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675686 (u : real) (v : real) : (term213 u v) = (term204 u v).
Proof. exact (MK_COMB (@lem1675685) (@lem1675684 u v)). Qed.
Lemma lem1675687 (u : real) (v : real) : ((term214 u v) = (term213 u v)) = ((term225 u v) = (term204 u v)).
Proof. exact (MK_COMB (@lem1675680 u v) (@lem1675686 u v)). Qed.
Lemma lem1675688 (u : real) (v : real) : (term225 u v) = (term204 u v).
Proof. exact (EQ_MP (@lem1675687 u v) (@lem1675672 u v)). Qed.
Lemma lem1675689 (u : real) : (term226 u) = (term205 u).
Proof. exact (fun_ext (fun v : real => @lem1675688 u v)). Qed.
Lemma lem1675690 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675691 (u : real) : (term227 u) = (term206 u).
Proof. exact (MK_COMB (@lem1675690) (@lem1675689 u)). Qed.
Lemma lem1675692 : term228 = term207.
Proof. exact (fun_ext (fun u : real => @lem1675691 u)). Qed.
Lemma lem1675693 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675694 : term229 = term208.
Proof. exact (MK_COMB (@lem1675693) (@lem1675692)). Qed.
Lemma lem1675701 (u : real) (v : real) (a : real) : (term202 u v a) = (term202 u v a).
Proof. exact (eq_refl (term202 u v a)). Qed.
Lemma lem1675702 (u : real) (v : real) : (term203 u v) = (term203 u v).
Proof. exact (fun_ext (fun a : real => @lem1675701 u v a)). Qed.
Lemma lem1675703 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675704 (u : real) (v : real) : (term204 u v) = (term204 u v).
Proof. exact (MK_COMB (@lem1675703) (@lem1675702 u v)). Qed.
Lemma lem1675705 (u : real) : (term205 u) = (term205 u).
Proof. exact (fun_ext (fun v : real => @lem1675704 u v)). Qed.
Lemma lem1675706 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675707 (u : real) : (term206 u) = (term206 u).
Proof. exact (MK_COMB (@lem1675706) (@lem1675705 u)). Qed.
Lemma lem1675708 : term207 = term207.
Proof. exact (fun_ext (fun u : real => @lem1675707 u)). Qed.
Lemma lem1675709 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675710 : term208 = term208.
Proof. exact (MK_COMB (@lem1675709) (@lem1675708)). Qed.
Lemma lem1675711 : term229 = term208.
Proof. exact (TRANS (@lem1675694) (@lem1675710)). Qed.
Lemma lem1675712 (h1 : term122) : term208.
Proof. exact (EQ_MP (@lem1675711) (@lem1675464 h1)). Qed.
Lemma lem1675744 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term251 x y u a v b) = (term251 x y u a v b).
Proof. exact (eq_refl (term251 x y u a v b)). Qed.
Lemma lem1675745 (x : real) (y : real) (u : real) (a : real) (b : real) : (term253 x y u a b) = (term253 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1675744 x y u a v b)). Qed.
Lemma lem1675746 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675747 (x : real) (y : real) (u : real) (a : real) (b : real) : (term254 x y u a b) = (term254 x y u a b).
Proof. exact (MK_COMB (@lem1675746) (@lem1675745 x y u a b)). Qed.
Lemma lem1675748 (x : real) (y : real) (a : real) (b : real) : (term255 x y a b) = (term255 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1675747 x y u a b)). Qed.
Lemma lem1675749 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675750 (x : real) (y : real) (a : real) (b : real) : (term256 x y a b) = (term256 x y a b).
Proof. exact (MK_COMB (@lem1675749) (@lem1675748 x y a b)). Qed.
Lemma lem1675751 (x : real) (y : real) (b : real) : (term257 x y b) = (term257 x y b).
Proof. exact (fun_ext (fun a : real => @lem1675750 x y a b)). Qed.
Lemma lem1675752 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675753 (x : real) (y : real) (b : real) : (term258 x y b) = (term258 x y b).
Proof. exact (MK_COMB (@lem1675752) (@lem1675751 x y b)). Qed.
Lemma lem1675754 (x : real) (b : real) : (term259 x b) = (term259 x b).
Proof. exact (fun_ext (fun y : real => @lem1675753 x y b)). Qed.
Lemma lem1675755 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675756 (x : real) (b : real) : (term260 x b) = (term260 x b).
Proof. exact (MK_COMB (@lem1675755) (@lem1675754 x b)). Qed.
Lemma lem1675757 (b : real) : (term261 b) = (term261 b).
Proof. exact (fun_ext (fun x : real => @lem1675756 x b)). Qed.
Lemma lem1675758 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675759 (b : real) : (term262 b) = (term262 b).
Proof. exact (MK_COMB (@lem1675758) (@lem1675757 b)). Qed.
Lemma lem1675760 : term263 = term263.
Proof. exact (fun_ext (fun b : real => @lem1675759 b)). Qed.
Lemma lem1675761 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1675763 : term264 = term264.
Proof. exact (MK_COMB (@lem1675761) (@lem1675760)). Qed.
Lemma lem1675764 (h1 : term119) : term264.
Proof. exact (EQ_MP (@lem1675763) (@lem1675580 h1)). Qed.
Lemma lem1675789 (_25835 : real) (h1 : term122) : term267 _25835.
Proof. exact (@lem1675712 h1 _25835). Qed.
Lemma lem1675790 (_25835 : real) : (term267 _25835) = (term206 _25835).
Proof. exact (eq_refl (term267 _25835)). Qed.
Lemma lem1675791 (_25835 : real) (h1 : term122) : term206 _25835.
Proof. exact (EQ_MP (@lem1675790 _25835) (@lem1675789 _25835 h1)). Qed.
Lemma lem1675792 (_25835 : real) (_25836 : real) (h1 : term122) : term268 _25835 _25836.
Proof. exact (@lem1675791 _25835 h1 _25836). Qed.
Lemma lem1675793 (_25835 : real) (_25836 : real) : (term268 _25835 _25836) = (term204 _25835 _25836).
Proof. exact (eq_refl (term268 _25835 _25836)). Qed.
Lemma lem1675794 (_25835 : real) (_25836 : real) (h1 : term122) : term204 _25835 _25836.
Proof. exact (EQ_MP (@lem1675793 _25835 _25836) (@lem1675792 _25835 _25836 h1)). Qed.
Lemma lem1675795 (_25835 : real) (_25836 : real) (_25837 : real) (h1 : term122) : term269 _25835 _25836 _25837.
Proof. exact (@lem1675794 _25835 _25836 h1 _25837). Qed.
Lemma lem1675796 (_25835 : real) (_25836 : real) (_25837 : real) : (term269 _25835 _25836 _25837) = (term202 _25835 _25836 _25837).
Proof. exact (eq_refl (term269 _25835 _25836 _25837)). Qed.
Lemma lem1675798 (_25838 : real) (h1 : term119) : term270 _25838.
Proof. exact (@lem1675764 h1 _25838). Qed.
Lemma lem1675799 (_25838 : real) : (term270 _25838) = (term262 _25838).
Proof. exact (eq_refl (term270 _25838)). Qed.
Lemma lem1675800 (_25838 : real) (h1 : term119) : term262 _25838.
Proof. exact (EQ_MP (@lem1675799 _25838) (@lem1675798 _25838 h1)). Qed.
Lemma lem1675801 (_25838 : real) (_25839 : real) (h1 : term119) : term271 _25838 _25839.
Proof. exact (@lem1675800 _25838 h1 _25839). Qed.
Lemma lem1675802 (_25839 : real) (_25838 : real) : (term271 _25838 _25839) = (term260 _25839 _25838).
Proof. exact (eq_refl (term271 _25838 _25839)). Qed.
Lemma lem1675803 (_25839 : real) (_25838 : real) (h1 : term119) : term260 _25839 _25838.
Proof. exact (EQ_MP (@lem1675802 _25839 _25838) (@lem1675801 _25838 _25839 h1)). Qed.
Lemma lem1675804 (_25839 : real) (_25838 : real) (_25840 : real) (h1 : term119) : term272 _25839 _25838 _25840.
Proof. exact (@lem1675803 _25839 _25838 h1 _25840). Qed.
Lemma lem1675805 (_25839 : real) (_25840 : real) (_25838 : real) : (term272 _25839 _25838 _25840) = (term258 _25839 _25840 _25838).
Proof. exact (eq_refl (term272 _25839 _25838 _25840)). Qed.
Lemma lem1675806 (_25839 : real) (_25840 : real) (_25838 : real) (h1 : term119) : term258 _25839 _25840 _25838.
Proof. exact (EQ_MP (@lem1675805 _25839 _25840 _25838) (@lem1675804 _25839 _25838 _25840 h1)). Qed.
Lemma lem1675807 (_25839 : real) (_25840 : real) (_25838 : real) (_25841 : real) (h1 : term119) : term273 _25839 _25840 _25838 _25841.
Proof. exact (@lem1675806 _25839 _25840 _25838 h1 _25841). Qed.
Lemma lem1675808 (_25839 : real) (_25840 : real) (_25841 : real) (_25838 : real) : (term273 _25839 _25840 _25838 _25841) = (term256 _25839 _25840 _25841 _25838).
Proof. exact (eq_refl (term273 _25839 _25840 _25838 _25841)). Qed.
Lemma lem1675809 (_25839 : real) (_25840 : real) (_25841 : real) (_25838 : real) (h1 : term119) : term256 _25839 _25840 _25841 _25838.
Proof. exact (EQ_MP (@lem1675808 _25839 _25840 _25841 _25838) (@lem1675807 _25839 _25840 _25838 _25841 h1)). Qed.
Lemma lem1675810 (_25839 : real) (_25840 : real) (_25841 : real) (_25838 : real) (_25842 : real) (h1 : term119) : term274 _25839 _25840 _25841 _25838 _25842.
Proof. exact (@lem1675809 _25839 _25840 _25841 _25838 h1 _25842). Qed.
Lemma lem1675811 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25838 : real) : (term274 _25839 _25840 _25841 _25838 _25842) = (term254 _25839 _25840 _25842 _25841 _25838).
Proof. exact (eq_refl (term274 _25839 _25840 _25841 _25838 _25842)). Qed.
Lemma lem1675812 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25838 : real) (h1 : term119) : term254 _25839 _25840 _25842 _25841 _25838.
Proof. exact (EQ_MP (@lem1675811 _25839 _25840 _25842 _25841 _25838) (@lem1675810 _25839 _25840 _25841 _25838 _25842 h1)). Qed.
Lemma lem1675813 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25838 : real) (_25843 : real) (h1 : term119) : term275 _25839 _25840 _25842 _25841 _25838 _25843.
Proof. exact (@lem1675812 _25839 _25840 _25842 _25841 _25838 h1 _25843). Qed.
Lemma lem1675814 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term275 _25839 _25840 _25842 _25841 _25838 _25843) = (term251 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (eq_refl (term275 _25839 _25840 _25842 _25841 _25838 _25843)). Qed.
Lemma lem1675815 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) (h1 : term119) : term251 _25839 _25840 _25842 _25841 _25843 _25838.
Proof. exact (EQ_MP (@lem1675814 _25839 _25840 _25842 _25841 _25843 _25838) (@lem1675813 _25839 _25840 _25842 _25841 _25838 _25843 h1)). Qed.
Lemma lem1675821 (_25835 : real) (_25836 : real) (_25837 : real) (h1 : term122) : term202 _25835 _25836 _25837.
Proof. exact (EQ_MP (@lem1675796 _25835 _25836 _25837) (@lem1675795 _25835 _25836 _25837 h1)). Qed.
Lemma lem1675825 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term251 _25839 _25840 _25842 _25841 _25843 _25838) = (term276 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (@lem1674701 (term277 _25839 _25841) (term240 _25840 _25838 _25842 _25843) (term247 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1675826 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term278 _25839 _25840 _25842 _25841 _25843 _25838) = (term279 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (@lem1674701 (term277 _25840 _25838) (term235 _25842 _25843) (term247 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1675827 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term280 _25839 _25840 _25842 _25841 _25843 _25838) = (term281 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (@lem1674701 (term282 _25842) (term231 _25842 _25843) (term247 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1675834 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term283 _25839 _25840 _25842 _25841 _25843 _25838) = (term284 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (@lem1674701 (term282 _25843) (term52 _25842 _25843) (term247 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1675835 (_25842 : real) : (term233 _25842) = (term233 _25842).
Proof. exact (eq_refl (term233 _25842)). Qed.
Lemma lem1675838 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term281 _25839 _25840 _25842 _25841 _25843 _25838) = (term285 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (MK_COMB (@lem1675835 _25842) (@lem1675834 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1675839 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term280 _25839 _25840 _25842 _25841 _25843 _25838) = (term285 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (TRANS (@lem1675827 _25839 _25840 _25842 _25841 _25843 _25838) (@lem1675838 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1675840 (_25840 : real) (_25838 : real) : (term238 _25840 _25838) = (term238 _25840 _25838).
Proof. exact (eq_refl (term238 _25840 _25838)). Qed.
Lemma lem1675843 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term279 _25839 _25840 _25842 _25841 _25843 _25838) = (term286 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (MK_COMB (@lem1675840 _25840 _25838) (@lem1675839 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1675844 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term278 _25839 _25840 _25842 _25841 _25843 _25838) = (term286 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (TRANS (@lem1675826 _25839 _25840 _25842 _25841 _25843 _25838) (@lem1675843 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1675845 (_25839 : real) (_25841 : real) : (term238 _25839 _25841) = (term238 _25839 _25841).
Proof. exact (eq_refl (term238 _25839 _25841)). Qed.
Lemma lem1675848 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term276 _25839 _25840 _25842 _25841 _25843 _25838) = (term287 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (MK_COMB (@lem1675845 _25839 _25841) (@lem1675844 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1675850 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term251 _25839 _25840 _25842 _25841 _25843 _25838) = (term287 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (TRANS (@lem1675825 _25839 _25840 _25842 _25841 _25843 _25838) (@lem1675848 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1675851 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) (h1 : term119) : term287 _25839 _25840 _25842 _25841 _25843 _25838.
Proof. exact (EQ_MP (@lem1675850 _25839 _25840 _25842 _25841 _25843 _25838) (@lem1675815 _25839 _25840 _25842 _25841 _25843 _25838 h1)). Qed.
Lemma lem1675853 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term288 u x v y a.
Proof. exact (proj2 (@lem1675658 u x v y a h1)). Qed.
Lemma lem1675883 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1675884 (_25848 : real) (_25850 : real) (h1 : _25848 = _25850) : _25848 = _25850.
Proof. exact (h1). Qed.
Lemma lem1675885 (_25849 : real) (_25851 : real) (h1 : _25849 = _25851) : _25849 = _25851.
Proof. exact (h1). Qed.
Lemma lem1675886 (_25848 : real) (_25850 : real) (h1 : _25848 = _25850) : (real_lt _25848) = (real_lt _25850).
Proof. exact (MK_COMB (@lem1675883) (@lem1675884 _25848 _25850 h1)). Qed.
Lemma lem1675887 (_25848 : real) (_25850 : real) (_25849 : real) (_25851 : real) (h1 : _25848 = _25850) (h2 : _25849 = _25851) : (real_lt _25848 _25849) = (real_lt _25850 _25851).
Proof. exact (MK_COMB (@lem1675886 _25848 _25850 h1) (@lem1675885 _25849 _25851 h2)). Qed.
Lemma lem1675889 (b : Prop) (a : Prop) : term289 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1675890 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : term290 _25850 _25851 _25848 _25849.
Proof. exact (@lem1675889 (real_lt _25850 _25851) (real_lt _25848 _25849)). Qed.
Lemma lem1675891 (_25848 : real) (_25850 : real) (_25849 : real) (_25851 : real) (h1 : _25848 = _25850) (h2 : _25849 = _25851) : term291 _25850 _25851 _25848 _25849.
Proof. exact (@lem1675890 _25850 _25851 _25848 _25849 (@lem1675887 _25848 _25850 _25849 _25851 h1 h2)). Qed.
Lemma lem1675892 (_25851 : real) (_25849 : real) (_25848 : real) (_25850 : real) (h1 : _25848 = _25850) : term292 _25850 _25851 _25848 _25849.
Proof. exact (fun h0 : _25849 = _25851 => @lem1675891 _25848 _25850 _25849 _25851 h1 h0). Qed.
Lemma lem1675894 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1675895 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : (term292 _25850 _25851 _25848 _25849) = (term293 _25850 _25851 _25848 _25849).
Proof. exact (@lem1675894 (_25849 = _25851) (term291 _25850 _25851 _25848 _25849)). Qed.
Lemma lem1675896 (_25851 : real) (_25849 : real) (_25848 : real) (_25850 : real) (h1 : _25848 = _25850) : term293 _25850 _25851 _25848 _25849.
Proof. exact (EQ_MP (@lem1675895 _25850 _25851 _25848 _25849) (@lem1675892 _25851 _25849 _25848 _25850 h1)). Qed.
Lemma lem1675897 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : term294 _25850 _25851 _25848 _25849.
Proof. exact (fun h0 : _25848 = _25850 => @lem1675896 _25851 _25849 _25848 _25850 h0). Qed.
Lemma lem1675899 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1675900 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : (term294 _25850 _25851 _25848 _25849) = (term295 _25850 _25851 _25848 _25849).
Proof. exact (@lem1675899 (_25848 = _25850) (term293 _25850 _25851 _25848 _25849)). Qed.
Lemma lem1675901 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : term295 _25850 _25851 _25848 _25849.
Proof. exact (EQ_MP (@lem1675900 _25850 _25851 _25848 _25849) (@lem1675897 _25850 _25851 _25848 _25849)). Qed.
Lemma lem1675961 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1675962 (u : real) (x : real) (v : real) (y : real) : (term296 u x v y) = (term296 u x v y).
Proof. exact (@lem1675961 (term296 u x v y)). Qed.
Lemma lem1675963 (u : real) (x : real) (v : real) (y : real) : term297 u x v y.
Proof. exact (fun h0 : term298 u x v y => @lem1675962 u x v y). Qed.
Lemma lem1675965 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1675966 (u : real) (x : real) (v : real) (y : real) : (term297 u x v y) = ((term296 u x v y) = (term296 u x v y)).
Proof. exact (@lem1675965 ((term296 u x v y) = (term296 u x v y))). Qed.
Lemma lem1675967 (u : real) (x : real) (v : real) (y : real) : (term296 u x v y) = (term296 u x v y).
Proof. exact (EQ_MP (@lem1675966 u x v y) (@lem1675963 u x v y)). Qed.
Lemma lem1675969 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1675665 u x v y a h1)). Qed.
Lemma lem1675970 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1675969 u x v y a h1). Qed.
Lemma lem1675972 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1675973 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1675972 ((real_add u v) = term39)). Qed.
Lemma lem1675974 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1675973 u v) (@lem1675970 u x v y a h1)). Qed.
Lemma lem1675980 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1675981 (_25837 : real) (_25835 : real) (_25836 : real) : (term202 _25835 _25836 _25837) = (term299 _25837 _25835 _25836).
Proof. exact (@lem1675980 ((term31 _25835 _25836 _25837) = _25837) (term52 _25835 _25836)). Qed.
Lemma lem1675991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1675992 (_25837 : real) (_25835 : real) (_25836 : real) : (term300 _25835 _25836 _25837) = (term301 _25837 _25835 _25836).
Proof. exact (MK_COMB (@lem1675991) (@lem1675981 _25837 _25835 _25836)). Qed.
Lemma lem1676002 (_25837 : real) (_25835 : real) (_25836 : real) : (term299 _25837 _25835 _25836) = (term299 _25837 _25835 _25836).
Proof. exact (eq_refl (term299 _25837 _25835 _25836)). Qed.
Lemma lem1676003 (_25837 : real) (_25835 : real) (_25836 : real) : ((term202 _25835 _25836 _25837) = (term299 _25837 _25835 _25836)) = ((term299 _25837 _25835 _25836) = (term299 _25837 _25835 _25836)).
Proof. exact (MK_COMB (@lem1675992 _25837 _25835 _25836) (@lem1676002 _25837 _25835 _25836)). Qed.
Lemma lem1676005 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1676006 (x : Prop) : (x = x) = True.
Proof. exact (@lem1676005 Prop x). Qed.
Lemma lem1676007 (_25837 : real) (_25835 : real) (_25836 : real) : ((term299 _25837 _25835 _25836) = (term299 _25837 _25835 _25836)) = True.
Proof. exact (@lem1676006 (term299 _25837 _25835 _25836)). Qed.
Lemma lem1676008 (_25837 : real) (_25835 : real) (_25836 : real) : ((term202 _25835 _25836 _25837) = (term299 _25837 _25835 _25836)) = True.
Proof. exact (TRANS (@lem1676003 _25837 _25835 _25836) (@lem1676007 _25837 _25835 _25836)). Qed.
Lemma lem1676009 (_25837 : real) (_25835 : real) (_25836 : real) : True = ((term202 _25835 _25836 _25837) = (term299 _25837 _25835 _25836)).
Proof. exact (SYM (@lem1676008 _25837 _25835 _25836)). Qed.
Lemma lem1676010 (_25837 : real) (_25835 : real) (_25836 : real) : (term202 _25835 _25836 _25837) = (term299 _25837 _25835 _25836).
Proof. exact (EQ_MP (@lem1676009 _25837 _25835 _25836) (@lem0)). Qed.
Lemma lem1676011 (_25837 : real) (_25835 : real) (_25836 : real) (h1 : term122) : term299 _25837 _25835 _25836.
Proof. exact (EQ_MP (@lem1676010 _25837 _25835 _25836) (@lem1675821 _25835 _25836 _25837 h1)). Qed.
Lemma lem1676013 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1676014 (_25835 : real) (_25836 : real) (_25837 : real) : (term299 _25837 _25835 _25836) = (term302 _25835 _25836 _25837).
Proof. exact (@lem1676013 (term52 _25835 _25836) ((term31 _25835 _25836 _25837) = _25837)). Qed.
Lemma lem1676016 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1676017 (_25835 : real) (_25836 : real) : (term303 _25835 _25836) = ((real_add _25835 _25836) = term39).
Proof. exact (@lem1676016 ((real_add _25835 _25836) = term39)). Qed.
Lemma lem1676018 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1676019 (_25835 : real) (_25836 : real) : (term304 _25835 _25836) = (term305 _25835 _25836).
Proof. exact (MK_COMB (@lem1676018) (@lem1676017 _25835 _25836)). Qed.
Lemma lem1676020 (_25835 : real) (_25836 : real) (_25837 : real) : ((term31 _25835 _25836 _25837) = _25837) = ((term31 _25835 _25836 _25837) = _25837).
Proof. exact (eq_refl ((term31 _25835 _25836 _25837) = _25837)). Qed.
Lemma lem1676021 (_25835 : real) (_25836 : real) (_25837 : real) : (term302 _25835 _25836 _25837) = (term1 _25835 _25836 _25837).
Proof. exact (MK_COMB (@lem1676019 _25835 _25836) (@lem1676020 _25835 _25836 _25837)). Qed.
Lemma lem1676022 (_25835 : real) (_25836 : real) (_25837 : real) : (term299 _25837 _25835 _25836) = (term1 _25835 _25836 _25837).
Proof. exact (TRANS (@lem1676014 _25835 _25836 _25837) (@lem1676021 _25835 _25836 _25837)). Qed.
Lemma lem1676025 (_25835 : real) (_25836 : real) (_25837 : real) (h1 : term122) : term1 _25835 _25836 _25837.
Proof. exact (EQ_MP (@lem1676022 _25835 _25836 _25837) (@lem1676011 _25837 _25835 _25836 h1)). Qed.
Lemma lem1676026 (u : real) (v : real) (_25837 : real) (h1 : term122) : term1 u v _25837.
Proof. exact (@lem1676025 u v _25837 h1). Qed.
Lemma lem1676029 (_25837 : real) (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term122) (h2 : term163 u x v y a) : (term31 u v _25837) = _25837.
Proof. exact (@lem1676026 u v _25837 h1 (@lem1675974 u x v y a h2)). Qed.
Lemma lem1676030 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term122) (h2 : term163 u x v y a) : (term31 u v a) = a.
Proof. exact (@lem1676029 a u x v y a h1 h2). Qed.
Lemma lem1676031 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term122) (h2 : term163 u x v y a) : term107 u v a.
Proof. exact (fun h0 : term44 u v a => @lem1676030 u x v y a h1 h2). Qed.
Lemma lem1676033 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1676034 (u : real) (v : real) (a : real) : (term107 u v a) = ((term31 u v a) = a).
Proof. exact (@lem1676033 ((term31 u v a) = a)). Qed.
Lemma lem1676035 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term122) (h2 : term163 u x v y a) : (term31 u v a) = a.
Proof. exact (EQ_MP (@lem1676034 u v a) (@lem1676031 u x v y a h1 h2)). Qed.
Lemma lem1676037 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : real_lt x a.
Proof. exact (proj1 (@lem1675660 u x v y a h1)). Qed.
Lemma lem1676038 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term306 x a.
Proof. exact (fun h0 : term277 x a => @lem1676037 u x v y a h1). Qed.
Lemma lem1676040 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1676041 (x : real) (a : real) : (term306 x a) = (real_lt x a).
Proof. exact (@lem1676040 (real_lt x a)). Qed.
Lemma lem1676042 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : real_lt x a.
Proof. exact (EQ_MP (@lem1676041 x a) (@lem1676038 u x v y a h1)). Qed.
Lemma lem1676044 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : real_lt y a.
Proof. exact (proj1 (@lem1675661 u x v y a h1)). Qed.
Lemma lem1676045 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term306 y a.
Proof. exact (fun h0 : term277 y a => @lem1676044 u x v y a h1). Qed.
Lemma lem1676047 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1676048 (y : real) (a : real) : (term306 y a) = (real_lt y a).
Proof. exact (@lem1676047 (real_lt y a)). Qed.
Lemma lem1676049 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : real_lt y a.
Proof. exact (EQ_MP (@lem1676048 y a) (@lem1676045 u x v y a h1)). Qed.
Lemma lem1676051 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term232 u.
Proof. exact (proj1 (@lem1675663 u x v y a h1)). Qed.
Lemma lem1676052 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term307 u.
Proof. exact (fun h0 : term282 u => @lem1676051 u x v y a h1). Qed.
Lemma lem1676054 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1676055 (u : real) : (term307 u) = (term232 u).
Proof. exact (@lem1676054 (term232 u)). Qed.
Lemma lem1676056 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term232 u.
Proof. exact (EQ_MP (@lem1676055 u) (@lem1676052 u x v y a h1)). Qed.
Lemma lem1676058 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term232 v.
Proof. exact (proj1 (@lem1675665 u x v y a h1)). Qed.
Lemma lem1676059 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term307 v.
Proof. exact (fun h0 : term282 v => @lem1676058 u x v y a h1). Qed.
Lemma lem1676061 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1676062 (v : real) : (term307 v) = (term232 v).
Proof. exact (@lem1676061 (term232 v)). Qed.
Lemma lem1676063 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term232 v.
Proof. exact (EQ_MP (@lem1676062 v) (@lem1676059 u x v y a h1)). Qed.
Lemma lem1676065 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1675665 u x v y a h1)). Qed.
Lemma lem1676066 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1676065 u x v y a h1). Qed.
Lemma lem1676068 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1676069 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1676068 ((real_add u v) = term39)). Qed.
Lemma lem1676070 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1676069 u v) (@lem1676066 u x v y a h1)). Qed.
Lemma lem1676086 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676087 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term286 _25839 _25840 _25842 _25841 _25843 _25838) = (term308 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (@lem1676086 (term282 _25842) (term277 _25840 _25838) (term284 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1676101 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676102 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term309 _25839 _25840 _25842 _25841 _25843 _25838) = (term310 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (@lem1676101 (term282 _25843) (term277 _25840 _25838) (term311 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1676116 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676117 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term312 _25839 _25840 _25842 _25841 _25843 _25838) = (term313 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (@lem1676116 (term52 _25842 _25843) (term277 _25840 _25838) (term247 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1676133 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1676134 (_25839 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term314 _25839 _25840 _25842 _25841 _25843 _25838) = (term315 _25839 _25842 _25841 _25843 _25840 _25838).
Proof. exact (@lem1676133 (term247 _25839 _25840 _25842 _25841 _25843 _25838) (term277 _25840 _25838)). Qed.
Lemma lem1676140 (_25842 : real) (_25843 : real) : (term217 _25842 _25843) = (term217 _25842 _25843).
Proof. exact (eq_refl (term217 _25842 _25843)). Qed.
Lemma lem1676141 (_25839 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term313 _25839 _25840 _25842 _25841 _25843 _25838) = (term316 _25839 _25842 _25841 _25843 _25840 _25838).
Proof. exact (MK_COMB (@lem1676140 _25842 _25843) (@lem1676134 _25839 _25842 _25841 _25843 _25840 _25838)). Qed.
Lemma lem1676145 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676146 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term316 _25839 _25842 _25841 _25843 _25840 _25838) = (term317 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (@lem1676145 (term247 _25839 _25840 _25842 _25841 _25843 _25838) (term52 _25842 _25843) (term277 _25840 _25838)). Qed.
Lemma lem1676164 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term313 _25839 _25840 _25842 _25841 _25843 _25838) = (term317 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (TRANS (@lem1676141 _25839 _25842 _25841 _25843 _25840 _25838) (@lem1676146 _25839 _25841 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676165 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term312 _25839 _25840 _25842 _25841 _25843 _25838) = (term317 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (TRANS (@lem1676117 _25839 _25840 _25842 _25841 _25843 _25838) (@lem1676164 _25839 _25841 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676166 (_25843 : real) : (term233 _25843) = (term233 _25843).
Proof. exact (eq_refl (term233 _25843)). Qed.
Lemma lem1676167 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term310 _25839 _25840 _25842 _25841 _25843 _25838) = (term318 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (MK_COMB (@lem1676166 _25843) (@lem1676165 _25839 _25841 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676171 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676172 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term318 _25839 _25841 _25842 _25843 _25840 _25838) = (term319 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (@lem1676171 (term247 _25839 _25840 _25842 _25841 _25843 _25838) (term282 _25843) (term320 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676186 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676187 (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term321 _25842 _25843 _25840 _25838) = (term322 _25842 _25843 _25840 _25838).
Proof. exact (@lem1676186 (term52 _25842 _25843) (term282 _25843) (term277 _25840 _25838)). Qed.
Lemma lem1676205 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term323 _25839 _25840 _25842 _25841 _25843 _25838) = (term323 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (eq_refl (term323 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1676206 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term319 _25839 _25841 _25842 _25843 _25840 _25838) = (term324 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (MK_COMB (@lem1676205 _25839 _25840 _25842 _25841 _25843 _25838) (@lem1676187 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676217 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term318 _25839 _25841 _25842 _25843 _25840 _25838) = (term324 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (TRANS (@lem1676172 _25839 _25841 _25842 _25843 _25840 _25838) (@lem1676206 _25839 _25841 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676218 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term310 _25839 _25840 _25842 _25841 _25843 _25838) = (term324 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (TRANS (@lem1676167 _25839 _25841 _25842 _25843 _25840 _25838) (@lem1676217 _25839 _25841 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676219 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term309 _25839 _25840 _25842 _25841 _25843 _25838) = (term324 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (TRANS (@lem1676102 _25839 _25840 _25842 _25841 _25843 _25838) (@lem1676218 _25839 _25841 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676220 (_25842 : real) : (term233 _25842) = (term233 _25842).
Proof. exact (eq_refl (term233 _25842)). Qed.
Lemma lem1676221 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term308 _25839 _25840 _25842 _25841 _25843 _25838) = (term325 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (MK_COMB (@lem1676220 _25842) (@lem1676219 _25839 _25841 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676225 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676226 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term325 _25839 _25841 _25842 _25843 _25840 _25838) = (term326 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (@lem1676225 (term247 _25839 _25840 _25842 _25841 _25843 _25838) (term282 _25842) (term322 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676240 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676241 (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term327 _25842 _25843 _25840 _25838) = (term328 _25842 _25843 _25840 _25838).
Proof. exact (@lem1676240 (term52 _25842 _25843) (term282 _25842) (term329 _25843 _25840 _25838)). Qed.
Lemma lem1676269 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term323 _25839 _25840 _25842 _25841 _25843 _25838) = (term323 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (eq_refl (term323 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1676270 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term326 _25839 _25841 _25842 _25843 _25840 _25838) = (term330 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (MK_COMB (@lem1676269 _25839 _25840 _25842 _25841 _25843 _25838) (@lem1676241 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676281 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term325 _25839 _25841 _25842 _25843 _25840 _25838) = (term330 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (TRANS (@lem1676226 _25839 _25841 _25842 _25843 _25840 _25838) (@lem1676270 _25839 _25841 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676282 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term308 _25839 _25840 _25842 _25841 _25843 _25838) = (term330 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (TRANS (@lem1676221 _25839 _25841 _25842 _25843 _25840 _25838) (@lem1676281 _25839 _25841 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676283 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term286 _25839 _25840 _25842 _25841 _25843 _25838) = (term330 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (TRANS (@lem1676087 _25839 _25840 _25842 _25841 _25843 _25838) (@lem1676282 _25839 _25841 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676284 (_25839 : real) (_25841 : real) : (term238 _25839 _25841) = (term238 _25839 _25841).
Proof. exact (eq_refl (term238 _25839 _25841)). Qed.
Lemma lem1676285 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term287 _25839 _25840 _25842 _25841 _25843 _25838) = (term331 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (MK_COMB (@lem1676284 _25839 _25841) (@lem1676283 _25839 _25841 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676289 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676290 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term331 _25839 _25841 _25842 _25843 _25840 _25838) = (term332 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (@lem1676289 (term247 _25839 _25840 _25842 _25841 _25843 _25838) (term277 _25839 _25841) (term328 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676304 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676305 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term333 _25839 _25841 _25842 _25843 _25840 _25838) = (term334 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (@lem1676304 (term52 _25842 _25843) (term277 _25839 _25841) (term335 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676321 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676322 (_25842 : real) (_25839 : real) (_25841 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term336 _25839 _25841 _25842 _25843 _25840 _25838) = (term337 _25842 _25839 _25841 _25843 _25840 _25838).
Proof. exact (@lem1676321 (term282 _25842) (term277 _25839 _25841) (term329 _25843 _25840 _25838)). Qed.
Lemma lem1676336 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676337 (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : (term338 _25839 _25841 _25843 _25840 _25838) = (term339 _25843 _25839 _25841 _25840 _25838).
Proof. exact (@lem1676336 (term282 _25843) (term277 _25839 _25841) (term277 _25840 _25838)). Qed.
Lemma lem1676353 (_25842 : real) : (term233 _25842) = (term233 _25842).
Proof. exact (eq_refl (term233 _25842)). Qed.
Lemma lem1676354 (_25842 : real) (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : (term337 _25842 _25839 _25841 _25843 _25840 _25838) = (term340 _25842 _25843 _25839 _25841 _25840 _25838).
Proof. exact (MK_COMB (@lem1676353 _25842) (@lem1676337 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676365 (_25842 : real) (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : (term336 _25839 _25841 _25842 _25843 _25840 _25838) = (term340 _25842 _25843 _25839 _25841 _25840 _25838).
Proof. exact (TRANS (@lem1676322 _25842 _25839 _25841 _25843 _25840 _25838) (@lem1676354 _25842 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676366 (_25842 : real) (_25843 : real) : (term217 _25842 _25843) = (term217 _25842 _25843).
Proof. exact (eq_refl (term217 _25842 _25843)). Qed.
Lemma lem1676367 (_25842 : real) (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : (term334 _25839 _25841 _25842 _25843 _25840 _25838) = (term341 _25842 _25843 _25839 _25841 _25840 _25838).
Proof. exact (MK_COMB (@lem1676366 _25842 _25843) (@lem1676365 _25842 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676378 (_25842 : real) (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : (term333 _25839 _25841 _25842 _25843 _25840 _25838) = (term341 _25842 _25843 _25839 _25841 _25840 _25838).
Proof. exact (TRANS (@lem1676305 _25839 _25841 _25842 _25843 _25840 _25838) (@lem1676367 _25842 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676379 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term323 _25839 _25840 _25842 _25841 _25843 _25838) = (term323 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (eq_refl (term323 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1676380 (_25842 : real) (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : (term332 _25839 _25841 _25842 _25843 _25840 _25838) = (term342 _25842 _25843 _25839 _25841 _25840 _25838).
Proof. exact (MK_COMB (@lem1676379 _25839 _25840 _25842 _25841 _25843 _25838) (@lem1676378 _25842 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676391 (_25842 : real) (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : (term331 _25839 _25841 _25842 _25843 _25840 _25838) = (term342 _25842 _25843 _25839 _25841 _25840 _25838).
Proof. exact (TRANS (@lem1676290 _25839 _25841 _25842 _25843 _25840 _25838) (@lem1676380 _25842 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676392 (_25842 : real) (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : (term287 _25839 _25840 _25842 _25841 _25843 _25838) = (term342 _25842 _25843 _25839 _25841 _25840 _25838).
Proof. exact (TRANS (@lem1676285 _25839 _25841 _25842 _25843 _25840 _25838) (@lem1676391 _25842 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1676394 (_25842 : real) (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : (term343 _25839 _25840 _25842 _25841 _25843 _25838) = (term344 _25842 _25843 _25839 _25841 _25840 _25838).
Proof. exact (MK_COMB (@lem1676393) (@lem1676392 _25842 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676418 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676419 (_25840 : real) (_25838 : real) (_25842 : real) (_25843 : real) : (term240 _25840 _25838 _25842 _25843) = (term345 _25840 _25838 _25842 _25843).
Proof. exact (@lem1676418 (term282 _25842) (term277 _25840 _25838) (term231 _25842 _25843)). Qed.
Lemma lem1676433 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676434 (_25840 : real) (_25838 : real) (_25842 : real) (_25843 : real) : (term346 _25840 _25838 _25842 _25843) = (term347 _25840 _25838 _25842 _25843).
Proof. exact (@lem1676433 (term282 _25843) (term277 _25840 _25838) (term52 _25842 _25843)). Qed.
Lemma lem1676448 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1676449 (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term348 _25840 _25838 _25842 _25843) = (term320 _25842 _25843 _25840 _25838).
Proof. exact (@lem1676448 (term52 _25842 _25843) (term277 _25840 _25838)). Qed.
Lemma lem1676457 (_25843 : real) : (term233 _25843) = (term233 _25843).
Proof. exact (eq_refl (term233 _25843)). Qed.
Lemma lem1676458 (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term347 _25840 _25838 _25842 _25843) = (term321 _25842 _25843 _25840 _25838).
Proof. exact (MK_COMB (@lem1676457 _25843) (@lem1676449 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676462 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676463 (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term321 _25842 _25843 _25840 _25838) = (term322 _25842 _25843 _25840 _25838).
Proof. exact (@lem1676462 (term52 _25842 _25843) (term282 _25843) (term277 _25840 _25838)). Qed.
Lemma lem1676481 (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term347 _25840 _25838 _25842 _25843) = (term322 _25842 _25843 _25840 _25838).
Proof. exact (TRANS (@lem1676458 _25842 _25843 _25840 _25838) (@lem1676463 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676482 (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term346 _25840 _25838 _25842 _25843) = (term322 _25842 _25843 _25840 _25838).
Proof. exact (TRANS (@lem1676434 _25840 _25838 _25842 _25843) (@lem1676481 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676483 (_25842 : real) : (term233 _25842) = (term233 _25842).
Proof. exact (eq_refl (term233 _25842)). Qed.
Lemma lem1676484 (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term345 _25840 _25838 _25842 _25843) = (term327 _25842 _25843 _25840 _25838).
Proof. exact (MK_COMB (@lem1676483 _25842) (@lem1676482 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676488 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676489 (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term327 _25842 _25843 _25840 _25838) = (term328 _25842 _25843 _25840 _25838).
Proof. exact (@lem1676488 (term52 _25842 _25843) (term282 _25842) (term329 _25843 _25840 _25838)). Qed.
Lemma lem1676517 (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term345 _25840 _25838 _25842 _25843) = (term328 _25842 _25843 _25840 _25838).
Proof. exact (TRANS (@lem1676484 _25842 _25843 _25840 _25838) (@lem1676489 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676518 (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term240 _25840 _25838 _25842 _25843) = (term328 _25842 _25843 _25840 _25838).
Proof. exact (TRANS (@lem1676419 _25840 _25838 _25842 _25843) (@lem1676517 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676519 (_25839 : real) (_25841 : real) : (term238 _25839 _25841) = (term238 _25839 _25841).
Proof. exact (eq_refl (term238 _25839 _25841)). Qed.
Lemma lem1676520 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term244 _25839 _25841 _25840 _25838 _25842 _25843) = (term333 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (MK_COMB (@lem1676519 _25839 _25841) (@lem1676518 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676524 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676525 (_25839 : real) (_25841 : real) (_25842 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term333 _25839 _25841 _25842 _25843 _25840 _25838) = (term334 _25839 _25841 _25842 _25843 _25840 _25838).
Proof. exact (@lem1676524 (term52 _25842 _25843) (term277 _25839 _25841) (term335 _25842 _25843 _25840 _25838)). Qed.
Lemma lem1676541 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676542 (_25842 : real) (_25839 : real) (_25841 : real) (_25843 : real) (_25840 : real) (_25838 : real) : (term336 _25839 _25841 _25842 _25843 _25840 _25838) = (term337 _25842 _25839 _25841 _25843 _25840 _25838).
Proof. exact (@lem1676541 (term282 _25842) (term277 _25839 _25841) (term329 _25843 _25840 _25838)). Qed.
Lemma lem1676556 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676557 (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : (term338 _25839 _25841 _25843 _25840 _25838) = (term339 _25843 _25839 _25841 _25840 _25838).
Proof. exact (@lem1676556 (term282 _25843) (term277 _25839 _25841) (term277 _25840 _25838)). Qed.
Lemma lem1676573 (_25842 : real) : (term233 _25842) = (term233 _25842).
Proof. exact (eq_refl (term233 _25842)). Qed.
Lemma lem1676574 (_25842 : real) (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : (term337 _25842 _25839 _25841 _25843 _25840 _25838) = (term340 _25842 _25843 _25839 _25841 _25840 _25838).
Proof. exact (MK_COMB (@lem1676573 _25842) (@lem1676557 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676585 (_25842 : real) (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : (term336 _25839 _25841 _25842 _25843 _25840 _25838) = (term340 _25842 _25843 _25839 _25841 _25840 _25838).
Proof. exact (TRANS (@lem1676542 _25842 _25839 _25841 _25843 _25840 _25838) (@lem1676574 _25842 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676586 (_25842 : real) (_25843 : real) : (term217 _25842 _25843) = (term217 _25842 _25843).
Proof. exact (eq_refl (term217 _25842 _25843)). Qed.
Lemma lem1676587 (_25842 : real) (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : (term334 _25839 _25841 _25842 _25843 _25840 _25838) = (term341 _25842 _25843 _25839 _25841 _25840 _25838).
Proof. exact (MK_COMB (@lem1676586 _25842 _25843) (@lem1676585 _25842 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676598 (_25842 : real) (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : (term333 _25839 _25841 _25842 _25843 _25840 _25838) = (term341 _25842 _25843 _25839 _25841 _25840 _25838).
Proof. exact (TRANS (@lem1676525 _25839 _25841 _25842 _25843 _25840 _25838) (@lem1676587 _25842 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676599 (_25842 : real) (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : (term244 _25839 _25841 _25840 _25838 _25842 _25843) = (term341 _25842 _25843 _25839 _25841 _25840 _25838).
Proof. exact (TRANS (@lem1676520 _25839 _25841 _25842 _25843 _25840 _25838) (@lem1676598 _25842 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676600 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term323 _25839 _25840 _25842 _25841 _25843 _25838) = (term323 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (eq_refl (term323 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1676601 (_25842 : real) (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : (term349 _25839 _25841 _25840 _25838 _25842 _25843) = (term342 _25842 _25843 _25839 _25841 _25840 _25838).
Proof. exact (MK_COMB (@lem1676600 _25839 _25840 _25842 _25841 _25843 _25838) (@lem1676599 _25842 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676612 (_25842 : real) (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : ((term287 _25839 _25840 _25842 _25841 _25843 _25838) = (term349 _25839 _25841 _25840 _25838 _25842 _25843)) = ((term342 _25842 _25843 _25839 _25841 _25840 _25838) = (term342 _25842 _25843 _25839 _25841 _25840 _25838)).
Proof. exact (MK_COMB (@lem1676394 _25842 _25843 _25839 _25841 _25840 _25838) (@lem1676601 _25842 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676614 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1676615 (x : Prop) : (x = x) = True.
Proof. exact (@lem1676614 Prop x). Qed.
Lemma lem1676616 (_25842 : real) (_25843 : real) (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) : ((term342 _25842 _25843 _25839 _25841 _25840 _25838) = (term342 _25842 _25843 _25839 _25841 _25840 _25838)) = True.
Proof. exact (@lem1676615 (term342 _25842 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676617 (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) (_25842 : real) (_25843 : real) : ((term287 _25839 _25840 _25842 _25841 _25843 _25838) = (term349 _25839 _25841 _25840 _25838 _25842 _25843)) = True.
Proof. exact (TRANS (@lem1676612 _25842 _25843 _25839 _25841 _25840 _25838) (@lem1676616 _25842 _25843 _25839 _25841 _25840 _25838)). Qed.
Lemma lem1676618 (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) (_25842 : real) (_25843 : real) : True = ((term287 _25839 _25840 _25842 _25841 _25843 _25838) = (term349 _25839 _25841 _25840 _25838 _25842 _25843)).
Proof. exact (SYM (@lem1676617 _25839 _25841 _25840 _25838 _25842 _25843)). Qed.
Lemma lem1676619 (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) (_25842 : real) (_25843 : real) : (term287 _25839 _25840 _25842 _25841 _25843 _25838) = (term349 _25839 _25841 _25840 _25838 _25842 _25843).
Proof. exact (EQ_MP (@lem1676618 _25839 _25841 _25840 _25838 _25842 _25843) (@lem0)). Qed.
Lemma lem1676620 (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) (_25842 : real) (_25843 : real) (h1 : term119) : term349 _25839 _25841 _25840 _25838 _25842 _25843.
Proof. exact (EQ_MP (@lem1676619 _25839 _25841 _25840 _25838 _25842 _25843) (@lem1675851 _25839 _25840 _25842 _25841 _25843 _25838 h1)). Qed.
Lemma lem1676622 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1676623 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term349 _25839 _25841 _25840 _25838 _25842 _25843) = (term350 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (@lem1676622 (term244 _25839 _25841 _25840 _25838 _25842 _25843) (term247 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1676625 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1676626 (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) (_25842 : real) (_25843 : real) : (term351 _25839 _25841 _25840 _25838 _25842 _25843) = (term352 _25839 _25841 _25840 _25838 _25842 _25843).
Proof. exact (@lem1676625 (term277 _25839 _25841) (term240 _25840 _25838 _25842 _25843)). Qed.
Lemma lem1676628 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1676629 (_25839 : real) (_25841 : real) : (term353 _25839 _25841) = (real_lt _25839 _25841).
Proof. exact (@lem1676628 (real_lt _25839 _25841)). Qed.
Lemma lem1676630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1676631 (_25839 : real) (_25841 : real) : (term354 _25839 _25841) = (term355 _25839 _25841).
Proof. exact (MK_COMB (@lem1676630) (@lem1676629 _25839 _25841)). Qed.
Lemma lem1676633 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1676634 (_25840 : real) (_25838 : real) (_25842 : real) (_25843 : real) : (term356 _25840 _25838 _25842 _25843) = (term357 _25840 _25838 _25842 _25843).
Proof. exact (@lem1676633 (term277 _25840 _25838) (term235 _25842 _25843)). Qed.
Lemma lem1676636 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1676637 (_25840 : real) (_25838 : real) : (term353 _25840 _25838) = (real_lt _25840 _25838).
Proof. exact (@lem1676636 (real_lt _25840 _25838)). Qed.
Lemma lem1676638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1676639 (_25840 : real) (_25838 : real) : (term354 _25840 _25838) = (term355 _25840 _25838).
Proof. exact (MK_COMB (@lem1676638) (@lem1676637 _25840 _25838)). Qed.
Lemma lem1676641 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1676642 (_25842 : real) (_25843 : real) : (term358 _25842 _25843) = (term359 _25842 _25843).
Proof. exact (@lem1676641 (term282 _25842) (term231 _25842 _25843)). Qed.
Lemma lem1676644 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1676645 (_25842 : real) : (term360 _25842) = (term232 _25842).
Proof. exact (@lem1676644 (term232 _25842)). Qed.
Lemma lem1676646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1676647 (_25842 : real) : (term361 _25842) = (term362 _25842).
Proof. exact (MK_COMB (@lem1676646) (@lem1676645 _25842)). Qed.
Lemma lem1676649 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1676650 (_25842 : real) (_25843 : real) : (term363 _25842 _25843) = (term364 _25842 _25843).
Proof. exact (@lem1676649 (term282 _25843) (term52 _25842 _25843)). Qed.
Lemma lem1676652 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1676653 (_25843 : real) : (term360 _25843) = (term232 _25843).
Proof. exact (@lem1676652 (term232 _25843)). Qed.
Lemma lem1676654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1676655 (_25843 : real) : (term361 _25843) = (term362 _25843).
Proof. exact (MK_COMB (@lem1676654) (@lem1676653 _25843)). Qed.
Lemma lem1676657 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1676658 (_25842 : real) (_25843 : real) : (term303 _25842 _25843) = ((real_add _25842 _25843) = term39).
Proof. exact (@lem1676657 ((real_add _25842 _25843) = term39)). Qed.
Lemma lem1676659 (_25842 : real) (_25843 : real) : (term364 _25842 _25843) = (term237 _25842 _25843).
Proof. exact (MK_COMB (@lem1676655 _25843) (@lem1676658 _25842 _25843)). Qed.
Lemma lem1676660 (_25842 : real) (_25843 : real) : (term363 _25842 _25843) = (term237 _25842 _25843).
Proof. exact (TRANS (@lem1676650 _25842 _25843) (@lem1676659 _25842 _25843)). Qed.
Lemma lem1676661 (_25842 : real) (_25843 : real) : (term359 _25842 _25843) = (term242 _25842 _25843).
Proof. exact (MK_COMB (@lem1676647 _25842) (@lem1676660 _25842 _25843)). Qed.
Lemma lem1676662 (_25842 : real) (_25843 : real) : (term358 _25842 _25843) = (term242 _25842 _25843).
Proof. exact (TRANS (@lem1676642 _25842 _25843) (@lem1676661 _25842 _25843)). Qed.
Lemma lem1676663 (_25840 : real) (_25838 : real) (_25842 : real) (_25843 : real) : (term357 _25840 _25838 _25842 _25843) = (term246 _25840 _25838 _25842 _25843).
Proof. exact (MK_COMB (@lem1676639 _25840 _25838) (@lem1676662 _25842 _25843)). Qed.
Lemma lem1676664 (_25840 : real) (_25838 : real) (_25842 : real) (_25843 : real) : (term356 _25840 _25838 _25842 _25843) = (term246 _25840 _25838 _25842 _25843).
Proof. exact (TRANS (@lem1676634 _25840 _25838 _25842 _25843) (@lem1676663 _25840 _25838 _25842 _25843)). Qed.
Lemma lem1676665 (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) (_25842 : real) (_25843 : real) : (term352 _25839 _25841 _25840 _25838 _25842 _25843) = (term252 _25839 _25841 _25840 _25838 _25842 _25843).
Proof. exact (MK_COMB (@lem1676631 _25839 _25841) (@lem1676664 _25840 _25838 _25842 _25843)). Qed.
Lemma lem1676666 (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) (_25842 : real) (_25843 : real) : (term351 _25839 _25841 _25840 _25838 _25842 _25843) = (term252 _25839 _25841 _25840 _25838 _25842 _25843).
Proof. exact (TRANS (@lem1676626 _25839 _25841 _25840 _25838 _25842 _25843) (@lem1676665 _25839 _25841 _25840 _25838 _25842 _25843)). Qed.
Lemma lem1676667 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1676668 (_25839 : real) (_25841 : real) (_25840 : real) (_25838 : real) (_25842 : real) (_25843 : real) : (term365 _25839 _25841 _25840 _25838 _25842 _25843) = (term366 _25839 _25841 _25840 _25838 _25842 _25843).
Proof. exact (MK_COMB (@lem1676667) (@lem1676666 _25839 _25841 _25840 _25838 _25842 _25843)). Qed.
Lemma lem1676669 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term247 _25839 _25840 _25842 _25841 _25843 _25838) = (term247 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (eq_refl (term247 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1676670 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term350 _25839 _25840 _25842 _25841 _25843 _25838) = (term137 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (MK_COMB (@lem1676668 _25839 _25841 _25840 _25838 _25842 _25843) (@lem1676669 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1676671 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) : (term349 _25839 _25841 _25840 _25838 _25842 _25843) = (term137 _25839 _25840 _25842 _25841 _25843 _25838).
Proof. exact (TRANS (@lem1676623 _25839 _25840 _25842 _25841 _25843 _25838) (@lem1676670 _25839 _25840 _25842 _25841 _25843 _25838)). Qed.
Lemma lem1676673 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term237 u v.
Proof. exact (conj (@lem1676063 u x v y a h1) (@lem1676070 u x v y a h1)). Qed.
Lemma lem1676674 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term242 u v.
Proof. exact (conj (@lem1676056 u x v y a h1) (@lem1676673 u x v y a h1)). Qed.
Lemma lem1676675 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term246 y a u v.
Proof. exact (conj (@lem1676049 u x v y a h1) (@lem1676674 u x v y a h1)). Qed.
Lemma lem1676676 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term164 x y a u v.
Proof. exact (conj (@lem1676042 u x v y a h1) (@lem1676675 u x v y a h1)). Qed.
Lemma lem1676678 (_25839 : real) (_25840 : real) (_25842 : real) (_25841 : real) (_25843 : real) (_25838 : real) (h1 : term119) : term137 _25839 _25840 _25842 _25841 _25843 _25838.
Proof. exact (EQ_MP (@lem1676671 _25839 _25840 _25842 _25841 _25843 _25838) (@lem1676620 _25839 _25841 _25840 _25838 _25842 _25843 h1)). Qed.
Lemma lem1676679 (x : real) (y : real) (u : real) (v : real) (a : real) (h1 : term119) : term367 x y u v a.
Proof. exact (@lem1676678 x y u a v a h1). Qed.
Lemma lem1676682 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term163 u x v y a) : term368 x y u v a.
Proof. exact (@lem1676679 x y u v a h1 (@lem1676676 u x v y a h2)). Qed.
Lemma lem1676683 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term163 u x v y a) : term369 x y u v a.
Proof. exact (fun h0 : term370 x y u v a => @lem1676682 u x v y a h1 h2). Qed.
Lemma lem1676685 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1676686 (x : real) (y : real) (u : real) (v : real) (a : real) : (term369 x y u v a) = (term368 x y u v a).
Proof. exact (@lem1676685 (term368 x y u v a)). Qed.
Lemma lem1676687 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term163 u x v y a) : term368 x y u v a.
Proof. exact (EQ_MP (@lem1676686 x y u v a) (@lem1676683 u x v y a h1 h2)). Qed.
Lemma lem1676705 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676706 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : (term293 _25850 _25851 _25848 _25849) = (term371 _25850 _25851 _25848 _25849).
Proof. exact (@lem1676705 (real_lt _25850 _25851) (term57 _25849 _25851) (term277 _25848 _25849)). Qed.
Lemma lem1676724 (_25848 : real) (_25850 : real) : (term58 _25848 _25850) = (term58 _25848 _25850).
Proof. exact (eq_refl (term58 _25848 _25850)). Qed.
Lemma lem1676725 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : (term295 _25850 _25851 _25848 _25849) = (term372 _25850 _25851 _25848 _25849).
Proof. exact (MK_COMB (@lem1676724 _25848 _25850) (@lem1676706 _25850 _25851 _25848 _25849)). Qed.
Lemma lem1676729 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1676730 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : (term372 _25850 _25851 _25848 _25849) = (term373 _25850 _25851 _25848 _25849).
Proof. exact (@lem1676729 (real_lt _25850 _25851) (term57 _25848 _25850) (term374 _25851 _25848 _25849)). Qed.
Lemma lem1676760 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : (term295 _25850 _25851 _25848 _25849) = (term373 _25850 _25851 _25848 _25849).
Proof. exact (TRANS (@lem1676725 _25850 _25851 _25848 _25849) (@lem1676730 _25850 _25851 _25848 _25849)). Qed.
Lemma lem1676761 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1676762 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : (term375 _25850 _25851 _25848 _25849) = (term376 _25850 _25851 _25848 _25849).
Proof. exact (MK_COMB (@lem1676761) (@lem1676760 _25850 _25851 _25848 _25849)). Qed.
Lemma lem1676792 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : (term373 _25850 _25851 _25848 _25849) = (term373 _25850 _25851 _25848 _25849).
Proof. exact (eq_refl (term373 _25850 _25851 _25848 _25849)). Qed.
Lemma lem1676793 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : ((term295 _25850 _25851 _25848 _25849) = (term373 _25850 _25851 _25848 _25849)) = ((term373 _25850 _25851 _25848 _25849) = (term373 _25850 _25851 _25848 _25849)).
Proof. exact (MK_COMB (@lem1676762 _25850 _25851 _25848 _25849) (@lem1676792 _25850 _25851 _25848 _25849)). Qed.
Lemma lem1676795 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1676796 (x : Prop) : (x = x) = True.
Proof. exact (@lem1676795 Prop x). Qed.
Lemma lem1676797 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : ((term373 _25850 _25851 _25848 _25849) = (term373 _25850 _25851 _25848 _25849)) = True.
Proof. exact (@lem1676796 (term373 _25850 _25851 _25848 _25849)). Qed.
Lemma lem1676798 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : ((term295 _25850 _25851 _25848 _25849) = (term373 _25850 _25851 _25848 _25849)) = True.
Proof. exact (TRANS (@lem1676793 _25850 _25851 _25848 _25849) (@lem1676797 _25850 _25851 _25848 _25849)). Qed.
Lemma lem1676799 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : True = ((term295 _25850 _25851 _25848 _25849) = (term373 _25850 _25851 _25848 _25849)).
Proof. exact (SYM (@lem1676798 _25850 _25851 _25848 _25849)). Qed.
Lemma lem1676800 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : (term295 _25850 _25851 _25848 _25849) = (term373 _25850 _25851 _25848 _25849).
Proof. exact (EQ_MP (@lem1676799 _25850 _25851 _25848 _25849) (@lem0)). Qed.
Lemma lem1676801 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : term373 _25850 _25851 _25848 _25849.
Proof. exact (EQ_MP (@lem1676800 _25850 _25851 _25848 _25849) (@lem1675901 _25850 _25851 _25848 _25849)). Qed.
Lemma lem1676803 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1676804 (_25848 : real) (_25849 : real) (_25850 : real) (_25851 : real) : (term373 _25850 _25851 _25848 _25849) = (term377 _25848 _25849 _25850 _25851).
Proof. exact (@lem1676803 (term378 _25850 _25851 _25848 _25849) (real_lt _25850 _25851)). Qed.
Lemma lem1676806 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1676807 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : (term379 _25850 _25851 _25848 _25849) = (term380 _25850 _25851 _25848 _25849).
Proof. exact (@lem1676806 (term57 _25848 _25850) (term374 _25851 _25848 _25849)). Qed.
Lemma lem1676809 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1676810 (_25848 : real) (_25850 : real) : (term72 _25848 _25850) = (_25848 = _25850).
Proof. exact (@lem1676809 (_25848 = _25850)). Qed.
Lemma lem1676811 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1676812 (_25848 : real) (_25850 : real) : (term73 _25848 _25850) = (term74 _25848 _25850).
Proof. exact (MK_COMB (@lem1676811) (@lem1676810 _25848 _25850)). Qed.
Lemma lem1676814 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1676815 (_25851 : real) (_25848 : real) (_25849 : real) : (term381 _25851 _25848 _25849) = (term382 _25851 _25848 _25849).
Proof. exact (@lem1676814 (term57 _25849 _25851) (term277 _25848 _25849)). Qed.
Lemma lem1676817 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1676818 (_25849 : real) (_25851 : real) : (term72 _25849 _25851) = (_25849 = _25851).
Proof. exact (@lem1676817 (_25849 = _25851)). Qed.
Lemma lem1676819 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1676820 (_25849 : real) (_25851 : real) : (term73 _25849 _25851) = (term74 _25849 _25851).
Proof. exact (MK_COMB (@lem1676819) (@lem1676818 _25849 _25851)). Qed.
Lemma lem1676822 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1676823 (_25848 : real) (_25849 : real) : (term353 _25848 _25849) = (real_lt _25848 _25849).
Proof. exact (@lem1676822 (real_lt _25848 _25849)). Qed.
Lemma lem1676824 (_25851 : real) (_25848 : real) (_25849 : real) : (term382 _25851 _25848 _25849) = (term383 _25851 _25848 _25849).
Proof. exact (MK_COMB (@lem1676820 _25849 _25851) (@lem1676823 _25848 _25849)). Qed.
Lemma lem1676825 (_25851 : real) (_25848 : real) (_25849 : real) : (term381 _25851 _25848 _25849) = (term383 _25851 _25848 _25849).
Proof. exact (TRANS (@lem1676815 _25851 _25848 _25849) (@lem1676824 _25851 _25848 _25849)). Qed.
Lemma lem1676826 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : (term380 _25850 _25851 _25848 _25849) = (term384 _25850 _25851 _25848 _25849).
Proof. exact (MK_COMB (@lem1676812 _25848 _25850) (@lem1676825 _25851 _25848 _25849)). Qed.
Lemma lem1676827 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : (term379 _25850 _25851 _25848 _25849) = (term384 _25850 _25851 _25848 _25849).
Proof. exact (TRANS (@lem1676807 _25850 _25851 _25848 _25849) (@lem1676826 _25850 _25851 _25848 _25849)). Qed.
Lemma lem1676828 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1676829 (_25850 : real) (_25851 : real) (_25848 : real) (_25849 : real) : (term385 _25850 _25851 _25848 _25849) = (term386 _25850 _25851 _25848 _25849).
Proof. exact (MK_COMB (@lem1676828) (@lem1676827 _25850 _25851 _25848 _25849)). Qed.
Lemma lem1676830 (_25850 : real) (_25851 : real) : (real_lt _25850 _25851) = (real_lt _25850 _25851).
Proof. exact (eq_refl (real_lt _25850 _25851)). Qed.
Lemma lem1676831 (_25848 : real) (_25849 : real) (_25850 : real) (_25851 : real) : (term377 _25848 _25849 _25850 _25851) = (term387 _25848 _25849 _25850 _25851).
Proof. exact (MK_COMB (@lem1676829 _25850 _25851 _25848 _25849) (@lem1676830 _25850 _25851)). Qed.
Lemma lem1676832 (_25848 : real) (_25849 : real) (_25850 : real) (_25851 : real) : (term373 _25850 _25851 _25848 _25849) = (term387 _25848 _25849 _25850 _25851).
Proof. exact (TRANS (@lem1676804 _25848 _25849 _25850 _25851) (@lem1676831 _25848 _25849 _25850 _25851)). Qed.
Lemma lem1676834 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : term388 x y u v a.
Proof. exact (conj (@lem1676035 u x v y a h2 h3) (@lem1676687 u x v y a h1 h3)). Qed.
Lemma lem1676835 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : term389 x y u v a.
Proof. exact (conj (@lem1675967 u x v y) (@lem1676834 u x v y a h1 h2 h3)). Qed.
Lemma lem1676837 (_25848 : real) (_25849 : real) (_25850 : real) (_25851 : real) : term387 _25848 _25849 _25850 _25851.
Proof. exact (EQ_MP (@lem1676832 _25848 _25849 _25850 _25851) (@lem1676801 _25850 _25851 _25848 _25849)). Qed.
Lemma lem1676838 (u : real) (x : real) (v : real) (y : real) (a : real) : term390 u x v y a.
Proof. exact (@lem1676837 (term296 u x v y) (term31 u v a) (term296 u x v y) a). Qed.
Lemma lem1676841 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : term165 u x v y a.
Proof. exact (@lem1676838 u x v y a (@lem1676835 u x v y a h1 h2 h3)). Qed.
Lemma lem1676842 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : term391 u x v y a.
Proof. exact (fun h0 : term288 u x v y a => @lem1676841 u x v y a h1 h2 h3). Qed.
Lemma lem1676844 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1676845 (u : real) (x : real) (v : real) (y : real) (a : real) : (term391 u x v y a) = (term165 u x v y a).
Proof. exact (@lem1676844 (term165 u x v y a)). Qed.
Lemma lem1676846 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : term165 u x v y a.
Proof. exact (EQ_MP (@lem1676845 u x v y a) (@lem1676842 u x v y a h1 h2 h3)). Qed.
Lemma lem1676849 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1676851 (u : real) (x : real) (v : real) (y : real) (a : real) : (term288 u x v y a) = (term392 u x v y a).
Proof. exact (@lem1676849 (term165 u x v y a)). Qed.
Lemma lem1676854 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term392 u x v y a.
Proof. exact (EQ_MP (@lem1676851 u x v y a) (@lem1675853 u x v y a h1)). Qed.
Lemma lem1676857 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : False.
Proof. exact (@lem1676854 u x v y a h3 (@lem1676846 u x v y a h1 h2 h3)). Qed.
Lemma lem1676858 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : term109.
Proof. exact (fun h0 : ~ False => @lem1676857 u x v y a h1 h2 h3). Qed.
Lemma lem1676860 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1676861 : term109 = False.
Proof. exact (@lem1676860 False). Qed.
Lemma lem1676862 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : False.
Proof. exact (EQ_MP (@lem1676861) (@lem1676858 u x v y a h1 h2 h3)). Qed.
Lemma lem1676863 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : (term163 u x v y a) = False.
Proof. exact (prop_ext (fun h4 : term163 u x v y a => @lem1676862 u x v y a h1 h2 h3) (fun h4 : False => @lem1675658 u x v y a h3)). Qed.
Lemma lem1676864 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : False.
Proof. exact (EQ_MP (@lem1676863 u x v y a h1 h2 h3) (@lem1675658 u x v y a h3)). Qed.
Lemma lem1676865 (u : real) (x : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term174 u x y a) : False.
Proof. exact (ex_elim (@lem1675416 u x y a h3) (fun v : real => fun h0 : term173 u x y a v => @lem1676864 u x v y a h1 h2 h0)). Qed.
Lemma lem1676866 (x : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term181 x y a) : False.
Proof. exact (ex_elim (@lem1675415 x y a h3) (fun u : real => fun h0 : term180 x y a u => @lem1676865 u x y a h1 h2 h0)). Qed.
Lemma lem1676867 (x : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term188 x y) : False.
Proof. exact (ex_elim (@lem1675414 x y h3) (fun a : real => fun h0 : term187 x y a => @lem1676866 x y a h1 h2 h0)). Qed.
Lemma lem1676868 (x : real) (h1 : term119) (h2 : term122) (h3 : term195 x) : False.
Proof. exact (ex_elim (@lem1675413 x h3) (fun y : real => fun h0 : term194 x y => @lem1676867 x y h1 h2 h0)). Qed.
Lemma lem1676869 (h1 : term119) (h2 : term122) (h3 : term125) : False.
Proof. exact (ex_elim (@lem1675180 h3) (fun x : real => fun h0 : term200 x => @lem1676868 x h1 h2 h0)). Qed.
Lemma lem1676870 (h1 : term122) (h2 : term125) : term130.
Proof. exact (fun h0 : term119 => @lem1676869 h0 h1 h2). Qed.
Lemma lem1676871 : term130 = term131.
Proof. exact (@lem69 term119). Qed.
Lemma lem1676872 (h1 : term122) (h2 : term125) : term131.
Proof. exact (EQ_MP (@lem1676871) (@lem1676870 h1 h2)). Qed.
Lemma lem1676873 (h1 : term125) : term134.
Proof. exact (fun h0 : term122 => @lem1676872 h0 h1). Qed.
Lemma lem1676874 : term136.
Proof. exact (fun h0 : term125 => @lem1676873 h0). Qed.
Lemma lem1676875 : term126.
Proof. exact (EQ_MP (@lem1675035) (@lem1676874)). Qed.
Lemma lem1676877 : term126.
Proof. exact (@lem1674725 (@lem1676875)). Qed.
Lemma lem1676878 (h1 : term125) : term133.
Proof. exact (@lem1676877 (@lem1674710 h1)). Qed.
Lemma lem1676879 (h1 : term125) : term130.
Proof. exact (@lem1676878 h1 (@lem1674705)). Qed.
Lemma lem1676880 (h1 : term125) : False.
Proof. exact (@lem1676879 h1 (@lem1674702)). Qed.
Lemma lem1676881 (h1 : term125) : term125 = False.
Proof. exact (prop_ext (fun h2 : term125 => @lem1676880 h1) (fun h2 : False => @lem1674710 h1)). Qed.
Lemma lem1676882 (h1 : term125) : False.
Proof. exact (EQ_MP (@lem1676881 h1) (@lem1674710 h1)). Qed.
Lemma lem1676883 : term124.
Proof. exact (fun h0 : term125 => @lem1676882 h0). Qed.
Lemma lem1676884 : term123.
Proof. exact (EQ_MP (@lem1674709) (@lem1676883)). Qed.
