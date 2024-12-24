Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_CONVEX_BOUND_LE_term_abbrevs.
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
Lemma lem1676896 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1676897 (u : real) (v : real) (a : real) : (term1 u v a) = (term2 u v a).
Proof. exact (@lem1676896 (term1 u v a)). Qed.
Lemma lem1676898 (u : real) (v : real) (a : real) : (term2 u v a) = (term1 u v a).
Proof. exact (SYM (@lem1676897 u v a)). Qed.
Lemma lem1676899 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term3 u v a.
Proof. exact (h1). Qed.
Lemma lem1676902 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term4 u v a.
Proof. exact (h1). Qed.
Lemma lem1676903 (u : real) (v : real) (a : real) : term5 u v a.
Proof. exact (fun h0 : term4 u v a => @lem1676902 u v a h0). Qed.
Lemma lem1676904 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (h1). Qed.
Lemma lem1676905 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term4 u v a.
Proof. exact (h1). Qed.
Lemma lem1676906 (u : real) (v : real) (a : real) (h1 : term4 u v a) (h2 : term5 u v a) : term4 u v a.
Proof. exact (@lem1676904 u v a h2 (@lem1676905 u v a h1)). Qed.
Lemma lem1676907 (u : real) (v : real) (a : real) (h1 : term4 u v a) : term6 u v a.
Proof. exact (fun h0 : term5 u v a => @lem1676906 u v a h1 h0). Qed.
Lemma lem1676908 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (h1). Qed.
Lemma lem1676909 (u : real) (v : real) (a : real) (h1 : term4 u v a) (h2 : term5 u v a) : term4 u v a.
Proof. exact (@lem1676907 u v a h1 (@lem1676908 u v a h2)). Qed.
Lemma lem1676910 (u : real) (v : real) (a : real) (h1 : term5 u v a) : term5 u v a.
Proof. exact (fun h0 : term4 u v a => @lem1676909 u v a h0 h1). Qed.
Lemma lem1676911 (u : real) (v : real) (a : real) : term7 u v a.
Proof. exact (fun h0 : term5 u v a => @lem1676910 u v a h0). Qed.
Lemma lem1676914 (u : real) (v : real) (a : real) : term5 u v a.
Proof. exact (@lem1676911 u v a (@lem1676903 u v a)). Qed.
Lemma lem1676946 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1676947 : term8 = term9.
Proof. exact (@lem1676946 term10). Qed.
Lemma lem1676952 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1676953 : term12 = term13.
Proof. exact (MK_COMB (@lem1676952) (@lem1676947)). Qed.
Lemma lem1676956 (u : real) (v : real) (a : real) : (term14 u v a) = (term14 u v a).
Proof. exact (eq_refl (term14 u v a)). Qed.
Lemma lem1676957 (u : real) (v : real) (a : real) : (term4 u v a) = (term15 u v a).
Proof. exact (MK_COMB (@lem1676956 u v a) (@lem1676953)). Qed.
Lemma lem1676960 (v : real) (a : real) : (term16 v a) = (term17 v a).
Proof. exact (fun_ext (fun u : real => @lem1676957 u v a)). Qed.
Lemma lem1676961 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1676962 (v : real) (a : real) : (term18 v a) = (term19 v a).
Proof. exact (MK_COMB (@lem1676961) (@lem1676960 v a)). Qed.
Lemma lem1676967 (a : real) : (term20 a) = (term21 a).
Proof. exact (fun_ext (fun v : real => @lem1676962 v a)). Qed.
Lemma lem1676968 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1676969 (a : real) : (term22 a) = (term23 a).
Proof. exact (MK_COMB (@lem1676968) (@lem1676967 a)). Qed.
Lemma lem1676974 : term24 = term25.
Proof. exact (fun_ext (fun a : real => @lem1676969 a)). Qed.
Lemma lem1676975 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1676984 : term26 = term27.
Proof. exact (MK_COMB (@lem1676975) (@lem1676974)). Qed.
Lemma lem1676985 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1676986 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1676985 x)). Qed.
Lemma lem1676987 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1676988 : term10 = term10.
Proof. exact (MK_COMB (@lem1676987) (@lem1676986)). Qed.
Lemma lem1676989 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1676990 : term9 = term9.
Proof. exact (MK_COMB (@lem1676989) (@lem1676988)). Qed.
Lemma lem1676991 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1676992 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1676991 x y z)). Qed.
Lemma lem1676993 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1676994 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1676993) (@lem1676992 x y)). Qed.
Lemma lem1676995 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1676994 x y)). Qed.
Lemma lem1676996 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1676997 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1676996) (@lem1676995 x)). Qed.
Lemma lem1676998 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1676997 x)). Qed.
Lemma lem1676999 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677000 : term37 = term37.
Proof. exact (MK_COMB (@lem1676999) (@lem1676998)). Qed.
Lemma lem1677001 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1677002 : term11 = term11.
Proof. exact (MK_COMB (@lem1677001) (@lem1677000)). Qed.
Lemma lem1677003 : term13 = term13.
Proof. exact (MK_COMB (@lem1677002) (@lem1676990)). Qed.
Lemma lem1677012 (u : real) (v : real) (a : real) : (term14 u v a) = (term14 u v a).
Proof. exact (eq_refl (term14 u v a)). Qed.
Lemma lem1677013 (u : real) (v : real) (a : real) : (term15 u v a) = (term15 u v a).
Proof. exact (MK_COMB (@lem1677012 u v a) (@lem1677003)). Qed.
Lemma lem1677014 (v : real) (a : real) : (term17 v a) = (term17 v a).
Proof. exact (fun_ext (fun u : real => @lem1677013 u v a)). Qed.
Lemma lem1677015 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677016 (v : real) (a : real) : (term19 v a) = (term19 v a).
Proof. exact (MK_COMB (@lem1677015) (@lem1677014 v a)). Qed.
Lemma lem1677017 (a : real) : (term21 a) = (term21 a).
Proof. exact (fun_ext (fun v : real => @lem1677016 v a)). Qed.
Lemma lem1677018 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677019 (a : real) : (term23 a) = (term23 a).
Proof. exact (MK_COMB (@lem1677018) (@lem1677017 a)). Qed.
Lemma lem1677020 : term25 = term25.
Proof. exact (fun_ext (fun a : real => @lem1677019 a)). Qed.
Lemma lem1677021 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677022 : term27 = term27.
Proof. exact (MK_COMB (@lem1677021) (@lem1677020)). Qed.
Lemma lem1677073 : term26 = term27.
Proof. exact (TRANS (@lem1676984) (@lem1677022)). Qed.
Lemma lem1677074 : term27 = term26.
Proof. exact (SYM (@lem1677073)). Qed.
Lemma lem1677075 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term3 u v a.
Proof. exact (h1). Qed.
Lemma lem1677076 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem1677077 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1677088 (u : real) (v : real) (a : real) : (term3 u v a) = (term38 u v a).
Proof. exact (@lem17362 ((real_add u v) = term39) ((term31 u v a) = a)). Qed.
Lemma lem1677090 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1677091 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1677090 x y z)). Qed.
Lemma lem1677092 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677093 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1677092) (@lem1677091 x y)). Qed.
Lemma lem1677094 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1677093 x y)). Qed.
Lemma lem1677095 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677096 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1677095) (@lem1677094 x)). Qed.
Lemma lem1677097 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1677096 x)). Qed.
Lemma lem1677098 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677115 : term37 = term37.
Proof. exact (MK_COMB (@lem1677098) (@lem1677097)). Qed.
Lemma lem1677116 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1677115) (@lem1677076 h1)). Qed.
Lemma lem1677117 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1677118 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1677117 x)). Qed.
Lemma lem1677119 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677128 : term10 = term10.
Proof. exact (MK_COMB (@lem1677119) (@lem1677118)). Qed.
Lemma lem1677129 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1677128) (@lem1677077 h1)). Qed.
Lemma lem1677167 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term38 u v a.
Proof. exact (EQ_MP (@lem1677088 u v a) (@lem1677075 u v a h1)). Qed.
Lemma lem1677192 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1677193 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1677192 x y z)). Qed.
Lemma lem1677194 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677195 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1677194) (@lem1677193 x y)). Qed.
Lemma lem1677196 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1677195 x y)). Qed.
Lemma lem1677197 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677198 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1677197) (@lem1677196 x)). Qed.
Lemma lem1677199 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1677198 x)). Qed.
Lemma lem1677200 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677201 : term37 = term37.
Proof. exact (MK_COMB (@lem1677200) (@lem1677199)). Qed.
Lemma lem1677202 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1677201) (@lem1677116 h1)). Qed.
Lemma lem1677217 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1677218 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1677217 x)). Qed.
Lemma lem1677219 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677220 : term10 = term10.
Proof. exact (MK_COMB (@lem1677219) (@lem1677218)). Qed.
Lemma lem1677221 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1677220) (@lem1677129 h1)). Qed.
Lemma lem1677225 (x : real) (y : real) (z : real) : ((term30 x y z) = (term31 x y z)) = ((term30 x y z) = (term31 x y z)).
Proof. exact (eq_refl ((term30 x y z) = (term31 x y z))). Qed.
Lemma lem1677226 (x : real) (y : real) : (term32 x y) = (term32 x y).
Proof. exact (fun_ext (fun z : real => @lem1677225 x y z)). Qed.
Lemma lem1677227 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677228 (x : real) (y : real) : (term33 x y) = (term33 x y).
Proof. exact (MK_COMB (@lem1677227) (@lem1677226 x y)). Qed.
Lemma lem1677229 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1677228 x y)). Qed.
Lemma lem1677230 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677231 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1677230) (@lem1677229 x)). Qed.
Lemma lem1677232 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1677231 x)). Qed.
Lemma lem1677233 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677235 : term37 = term37.
Proof. exact (MK_COMB (@lem1677233) (@lem1677232)). Qed.
Lemma lem1677236 (h1 : term37) : term37.
Proof. exact (EQ_MP (@lem1677235) (@lem1677202 h1)). Qed.
Lemma lem1677238 (x : real) : ((term28 x) = x) = ((term28 x) = x).
Proof. exact (eq_refl ((term28 x) = x)). Qed.
Lemma lem1677239 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1677238 x)). Qed.
Lemma lem1677240 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677242 : term10 = term10.
Proof. exact (MK_COMB (@lem1677240) (@lem1677239)). Qed.
Lemma lem1677243 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1677242) (@lem1677221 h1)). Qed.
Lemma lem1677252 (_25866 : real) (h1 : term37) : term40 _25866.
Proof. exact (@lem1677236 h1 _25866). Qed.
Lemma lem1677253 (_25866 : real) : (term40 _25866) = (term35 _25866).
Proof. exact (eq_refl (term40 _25866)). Qed.
Lemma lem1677254 (_25866 : real) (h1 : term37) : term35 _25866.
Proof. exact (EQ_MP (@lem1677253 _25866) (@lem1677252 _25866 h1)). Qed.
Lemma lem1677255 (_25866 : real) (_25867 : real) (h1 : term37) : term41 _25866 _25867.
Proof. exact (@lem1677254 _25866 h1 _25867). Qed.
Lemma lem1677256 (_25866 : real) (_25867 : real) : (term41 _25866 _25867) = (term33 _25866 _25867).
Proof. exact (eq_refl (term41 _25866 _25867)). Qed.
Lemma lem1677257 (_25866 : real) (_25867 : real) (h1 : term37) : term33 _25866 _25867.
Proof. exact (EQ_MP (@lem1677256 _25866 _25867) (@lem1677255 _25866 _25867 h1)). Qed.
Lemma lem1677258 (_25866 : real) (_25867 : real) (_25868 : real) (h1 : term37) : term42 _25866 _25867 _25868.
Proof. exact (@lem1677257 _25866 _25867 h1 _25868). Qed.
Lemma lem1677259 (_25866 : real) (_25867 : real) (_25868 : real) : (term42 _25866 _25867 _25868) = ((term30 _25866 _25867 _25868) = (term31 _25866 _25867 _25868)).
Proof. exact (eq_refl (term42 _25866 _25867 _25868)). Qed.
Lemma lem1677261 (_25869 : real) (h1 : term10) : term43 _25869.
Proof. exact (@lem1677243 h1 _25869). Qed.
Lemma lem1677262 (_25869 : real) : (term43 _25869) = ((term28 _25869) = _25869).
Proof. exact (eq_refl (term43 _25869)). Qed.
Lemma lem1677271 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term44 u v a.
Proof. exact (proj2 (@lem1677167 u v a h1)). Qed.
Lemma lem1677296 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1677297 (_25876 : real) (_25878 : real) (h1 : _25876 = _25878) : _25876 = _25878.
Proof. exact (h1). Qed.
Lemma lem1677298 (_25877 : real) (_25879 : real) (h1 : _25877 = _25879) : _25877 = _25879.
Proof. exact (h1). Qed.
Lemma lem1677299 (_25876 : real) (_25878 : real) (h1 : _25876 = _25878) : (real_mul _25876) = (real_mul _25878).
Proof. exact (MK_COMB (@lem1677296) (@lem1677297 _25876 _25878 h1)). Qed.
Lemma lem1677300 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) (h1 : _25876 = _25878) (h2 : _25877 = _25879) : (real_mul _25876 _25877) = (real_mul _25878 _25879).
Proof. exact (MK_COMB (@lem1677299 _25876 _25878 h1) (@lem1677298 _25877 _25879 h2)). Qed.
Lemma lem1677301 (_25877 : real) (_25879 : real) (_25876 : real) (_25878 : real) (h1 : _25876 = _25878) : term45 _25876 _25877 _25878 _25879.
Proof. exact (fun h0 : _25877 = _25879 => @lem1677300 _25876 _25878 _25877 _25879 h1 h0). Qed.
Lemma lem1677303 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1677304 (_25876 : real) (_25877 : real) (_25878 : real) (_25879 : real) : (term45 _25876 _25877 _25878 _25879) = (term47 _25876 _25877 _25878 _25879).
Proof. exact (@lem1677303 (_25877 = _25879) ((real_mul _25876 _25877) = (real_mul _25878 _25879))). Qed.
Lemma lem1677305 (_25877 : real) (_25879 : real) (_25876 : real) (_25878 : real) (h1 : _25876 = _25878) : term47 _25876 _25877 _25878 _25879.
Proof. exact (EQ_MP (@lem1677304 _25876 _25877 _25878 _25879) (@lem1677301 _25877 _25879 _25876 _25878 h1)). Qed.
Lemma lem1677306 (_25876 : real) (_25877 : real) (_25878 : real) (_25879 : real) : term48 _25876 _25877 _25878 _25879.
Proof. exact (fun h0 : _25876 = _25878 => @lem1677305 _25877 _25879 _25876 _25878 h0). Qed.
Lemma lem1677308 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1677309 (_25876 : real) (_25877 : real) (_25878 : real) (_25879 : real) : (term48 _25876 _25877 _25878 _25879) = (term49 _25876 _25877 _25878 _25879).
Proof. exact (@lem1677308 (_25876 = _25878) (term47 _25876 _25877 _25878 _25879)). Qed.
Lemma lem1677310 (_25876 : real) (_25877 : real) (_25878 : real) (_25879 : real) : term49 _25876 _25877 _25878 _25879.
Proof. exact (EQ_MP (@lem1677309 _25876 _25877 _25878 _25879) (@lem1677306 _25876 _25877 _25878 _25879)). Qed.
Lemma lem1677327 (x : real) (y : real) (z : real) : term50 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1677331 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (real_add u v) = term39.
Proof. exact (proj1 (@lem1677167 u v a h1)). Qed.
Lemma lem1677332 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1677331 u v a h1). Qed.
Lemma lem1677334 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1677335 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1677334 ((real_add u v) = term39)). Qed.
Lemma lem1677336 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1677335 u v) (@lem1677332 u v a h1)). Qed.
Lemma lem1677338 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1677339 (a : real) : a = a.
Proof. exact (@lem1677338 a). Qed.
Lemma lem1677340 (a : real) : term54 a.
Proof. exact (fun h0 : term55 a => @lem1677339 a). Qed.
Lemma lem1677342 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1677343 (a : real) : (term54 a) = (a = a).
Proof. exact (@lem1677342 (a = a)). Qed.
Lemma lem1677344 (a : real) : a = a.
Proof. exact (EQ_MP (@lem1677343 a) (@lem1677340 a)). Qed.
Lemma lem1677362 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1677363 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) : (term47 _25876 _25877 _25878 _25879) = (term56 _25876 _25878 _25877 _25879).
Proof. exact (@lem1677362 ((real_mul _25876 _25877) = (real_mul _25878 _25879)) (term57 _25877 _25879)). Qed.
Lemma lem1677373 (_25876 : real) (_25878 : real) : (term58 _25876 _25878) = (term58 _25876 _25878).
Proof. exact (eq_refl (term58 _25876 _25878)). Qed.
Lemma lem1677374 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) : (term49 _25876 _25877 _25878 _25879) = (term59 _25876 _25878 _25877 _25879).
Proof. exact (MK_COMB (@lem1677373 _25876 _25878) (@lem1677363 _25876 _25878 _25877 _25879)). Qed.
Lemma lem1677378 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1677379 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) : (term59 _25876 _25878 _25877 _25879) = (term61 _25876 _25878 _25877 _25879).
Proof. exact (@lem1677378 ((real_mul _25876 _25877) = (real_mul _25878 _25879)) (term57 _25876 _25878) (term57 _25877 _25879)). Qed.
Lemma lem1677401 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) : (term49 _25876 _25877 _25878 _25879) = (term61 _25876 _25878 _25877 _25879).
Proof. exact (TRANS (@lem1677374 _25876 _25878 _25877 _25879) (@lem1677379 _25876 _25878 _25877 _25879)). Qed.
Lemma lem1677402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1677403 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) : (term62 _25876 _25877 _25878 _25879) = (term63 _25876 _25878 _25877 _25879).
Proof. exact (MK_COMB (@lem1677402) (@lem1677401 _25876 _25878 _25877 _25879)). Qed.
Lemma lem1677425 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) : (term61 _25876 _25878 _25877 _25879) = (term61 _25876 _25878 _25877 _25879).
Proof. exact (eq_refl (term61 _25876 _25878 _25877 _25879)). Qed.
Lemma lem1677426 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) : ((term49 _25876 _25877 _25878 _25879) = (term61 _25876 _25878 _25877 _25879)) = ((term61 _25876 _25878 _25877 _25879) = (term61 _25876 _25878 _25877 _25879)).
Proof. exact (MK_COMB (@lem1677403 _25876 _25878 _25877 _25879) (@lem1677425 _25876 _25878 _25877 _25879)). Qed.
Lemma lem1677428 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1677429 (x : Prop) : (x = x) = True.
Proof. exact (@lem1677428 Prop x). Qed.
Lemma lem1677430 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) : ((term61 _25876 _25878 _25877 _25879) = (term61 _25876 _25878 _25877 _25879)) = True.
Proof. exact (@lem1677429 (term61 _25876 _25878 _25877 _25879)). Qed.
Lemma lem1677431 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) : ((term49 _25876 _25877 _25878 _25879) = (term61 _25876 _25878 _25877 _25879)) = True.
Proof. exact (TRANS (@lem1677426 _25876 _25878 _25877 _25879) (@lem1677430 _25876 _25878 _25877 _25879)). Qed.
Lemma lem1677432 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) : True = ((term49 _25876 _25877 _25878 _25879) = (term61 _25876 _25878 _25877 _25879)).
Proof. exact (SYM (@lem1677431 _25876 _25878 _25877 _25879)). Qed.
Lemma lem1677433 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) : (term49 _25876 _25877 _25878 _25879) = (term61 _25876 _25878 _25877 _25879).
Proof. exact (EQ_MP (@lem1677432 _25876 _25878 _25877 _25879) (@lem0)). Qed.
Lemma lem1677434 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) : term61 _25876 _25878 _25877 _25879.
Proof. exact (EQ_MP (@lem1677433 _25876 _25878 _25877 _25879) (@lem1677310 _25876 _25877 _25878 _25879)). Qed.
Lemma lem1677436 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1677437 (_25876 : real) (_25877 : real) (_25878 : real) (_25879 : real) : (term61 _25876 _25878 _25877 _25879) = (term65 _25876 _25877 _25878 _25879).
Proof. exact (@lem1677436 (term66 _25876 _25878 _25877 _25879) ((real_mul _25876 _25877) = (real_mul _25878 _25879))). Qed.
Lemma lem1677439 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1677440 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) : (term69 _25876 _25878 _25877 _25879) = (term70 _25876 _25878 _25877 _25879).
Proof. exact (@lem1677439 (term57 _25876 _25878) (term57 _25877 _25879)). Qed.
Lemma lem1677442 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1677443 (_25876 : real) (_25878 : real) : (term72 _25876 _25878) = (_25876 = _25878).
Proof. exact (@lem1677442 (_25876 = _25878)). Qed.
Lemma lem1677444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1677445 (_25876 : real) (_25878 : real) : (term73 _25876 _25878) = (term74 _25876 _25878).
Proof. exact (MK_COMB (@lem1677444) (@lem1677443 _25876 _25878)). Qed.
Lemma lem1677447 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1677448 (_25877 : real) (_25879 : real) : (term72 _25877 _25879) = (_25877 = _25879).
Proof. exact (@lem1677447 (_25877 = _25879)). Qed.
Lemma lem1677449 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) : (term70 _25876 _25878 _25877 _25879) = (term75 _25876 _25878 _25877 _25879).
Proof. exact (MK_COMB (@lem1677445 _25876 _25878) (@lem1677448 _25877 _25879)). Qed.
Lemma lem1677450 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) : (term69 _25876 _25878 _25877 _25879) = (term75 _25876 _25878 _25877 _25879).
Proof. exact (TRANS (@lem1677440 _25876 _25878 _25877 _25879) (@lem1677449 _25876 _25878 _25877 _25879)). Qed.
Lemma lem1677451 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1677452 (_25876 : real) (_25878 : real) (_25877 : real) (_25879 : real) : (term76 _25876 _25878 _25877 _25879) = (term77 _25876 _25878 _25877 _25879).
Proof. exact (MK_COMB (@lem1677451) (@lem1677450 _25876 _25878 _25877 _25879)). Qed.
Lemma lem1677453 (_25876 : real) (_25877 : real) (_25878 : real) (_25879 : real) : ((real_mul _25876 _25877) = (real_mul _25878 _25879)) = ((real_mul _25876 _25877) = (real_mul _25878 _25879)).
Proof. exact (eq_refl ((real_mul _25876 _25877) = (real_mul _25878 _25879))). Qed.
Lemma lem1677454 (_25876 : real) (_25877 : real) (_25878 : real) (_25879 : real) : (term65 _25876 _25877 _25878 _25879) = (term78 _25876 _25877 _25878 _25879).
Proof. exact (MK_COMB (@lem1677452 _25876 _25878 _25877 _25879) (@lem1677453 _25876 _25877 _25878 _25879)). Qed.
Lemma lem1677455 (_25876 : real) (_25877 : real) (_25878 : real) (_25879 : real) : (term61 _25876 _25878 _25877 _25879) = (term78 _25876 _25877 _25878 _25879).
Proof. exact (TRANS (@lem1677437 _25876 _25877 _25878 _25879) (@lem1677454 _25876 _25877 _25878 _25879)). Qed.
Lemma lem1677457 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term79 u v a.
Proof. exact (conj (@lem1677336 u v a h1) (@lem1677344 a)). Qed.
Lemma lem1677459 (_25876 : real) (_25877 : real) (_25878 : real) (_25879 : real) : term78 _25876 _25877 _25878 _25879.
Proof. exact (EQ_MP (@lem1677455 _25876 _25877 _25878 _25879) (@lem1677434 _25876 _25878 _25877 _25879)). Qed.
Lemma lem1677460 (u : real) (v : real) (a : real) : term80 u v a.
Proof. exact (@lem1677459 (real_add u v) a term39 a). Qed.
Lemma lem1677463 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term30 u v a) = (term28 a).
Proof. exact (@lem1677460 u v a (@lem1677457 u v a h1)). Qed.
Lemma lem1677464 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term81 u v a.
Proof. exact (fun h0 : term82 u v a => @lem1677463 u v a h1). Qed.
Lemma lem1677466 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1677467 (u : real) (v : real) (a : real) : (term81 u v a) = ((term30 u v a) = (term28 a)).
Proof. exact (@lem1677466 ((term30 u v a) = (term28 a))). Qed.
Lemma lem1677468 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term30 u v a) = (term28 a).
Proof. exact (EQ_MP (@lem1677467 u v a) (@lem1677464 u v a h1)). Qed.
Lemma lem1677470 (_25866 : real) (_25867 : real) (_25868 : real) (h1 : term37) : (term30 _25866 _25867 _25868) = (term31 _25866 _25867 _25868).
Proof. exact (EQ_MP (@lem1677259 _25866 _25867 _25868) (@lem1677258 _25866 _25867 _25868 h1)). Qed.
Lemma lem1677471 (u : real) (v : real) (a : real) (h1 : term37) : (term30 u v a) = (term31 u v a).
Proof. exact (@lem1677470 u v a h1). Qed.
Lemma lem1677472 (u : real) (v : real) (a : real) (h1 : term37) : term83 u v a.
Proof. exact (fun h0 : term84 u v a => @lem1677471 u v a h1). Qed.
Lemma lem1677474 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1677475 (u : real) (v : real) (a : real) : (term83 u v a) = ((term30 u v a) = (term31 u v a)).
Proof. exact (@lem1677474 ((term30 u v a) = (term31 u v a))). Qed.
Lemma lem1677476 (u : real) (v : real) (a : real) (h1 : term37) : (term30 u v a) = (term31 u v a).
Proof. exact (EQ_MP (@lem1677475 u v a) (@lem1677472 u v a h1)). Qed.
Lemma lem1677494 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1677495 (y : real) (x : real) (z : real) : (term85 x y z) = (term86 y x z).
Proof. exact (@lem1677494 (y = z) (term57 x z)). Qed.
Lemma lem1677505 (x : real) (y : real) : (term58 x y) = (term58 x y).
Proof. exact (eq_refl (term58 x y)). Qed.
Lemma lem1677506 (y : real) (x : real) (z : real) : (term50 x y z) = (term87 y x z).
Proof. exact (MK_COMB (@lem1677505 x y) (@lem1677495 y x z)). Qed.
Lemma lem1677510 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1677511 (y : real) (x : real) (z : real) : (term87 y x z) = (term88 y x z).
Proof. exact (@lem1677510 (y = z) (term57 x y) (term57 x z)). Qed.
Lemma lem1677533 (y : real) (x : real) (z : real) : (term50 x y z) = (term88 y x z).
Proof. exact (TRANS (@lem1677506 y x z) (@lem1677511 y x z)). Qed.
Lemma lem1677534 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1677535 (y : real) (x : real) (z : real) : (term89 x y z) = (term90 y x z).
Proof. exact (MK_COMB (@lem1677534) (@lem1677533 y x z)). Qed.
Lemma lem1677557 (y : real) (x : real) (z : real) : (term88 y x z) = (term88 y x z).
Proof. exact (eq_refl (term88 y x z)). Qed.
Lemma lem1677558 (y : real) (x : real) (z : real) : ((term50 x y z) = (term88 y x z)) = ((term88 y x z) = (term88 y x z)).
Proof. exact (MK_COMB (@lem1677535 y x z) (@lem1677557 y x z)). Qed.
Lemma lem1677560 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1677561 (x : Prop) : (x = x) = True.
Proof. exact (@lem1677560 Prop x). Qed.
Lemma lem1677562 (y : real) (x : real) (z : real) : ((term88 y x z) = (term88 y x z)) = True.
Proof. exact (@lem1677561 (term88 y x z)). Qed.
Lemma lem1677563 (y : real) (x : real) (z : real) : ((term50 x y z) = (term88 y x z)) = True.
Proof. exact (TRANS (@lem1677558 y x z) (@lem1677562 y x z)). Qed.
Lemma lem1677564 (y : real) (x : real) (z : real) : True = ((term50 x y z) = (term88 y x z)).
Proof. exact (SYM (@lem1677563 y x z)). Qed.
Lemma lem1677565 (y : real) (x : real) (z : real) : (term50 x y z) = (term88 y x z).
Proof. exact (EQ_MP (@lem1677564 y x z) (@lem0)). Qed.
Lemma lem1677566 (y : real) (x : real) (z : real) : term88 y x z.
Proof. exact (EQ_MP (@lem1677565 y x z) (@lem1677327 x y z)). Qed.
Lemma lem1677568 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1677569 (x : real) (y : real) (z : real) : (term88 y x z) = (term91 x y z).
Proof. exact (@lem1677568 (term92 y x z) (y = z)). Qed.
Lemma lem1677571 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1677572 (y : real) (x : real) (z : real) : (term93 y x z) = (term94 y x z).
Proof. exact (@lem1677571 (term57 x y) (term57 x z)). Qed.
Lemma lem1677574 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1677575 (x : real) (y : real) : (term72 x y) = (x = y).
Proof. exact (@lem1677574 (x = y)). Qed.
Lemma lem1677576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1677577 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1677576) (@lem1677575 x y)). Qed.
Lemma lem1677579 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1677580 (x : real) (z : real) : (term72 x z) = (x = z).
Proof. exact (@lem1677579 (x = z)). Qed.
Lemma lem1677581 (y : real) (x : real) (z : real) : (term94 y x z) = (term95 y x z).
Proof. exact (MK_COMB (@lem1677577 x y) (@lem1677580 x z)). Qed.
Lemma lem1677582 (y : real) (x : real) (z : real) : (term93 y x z) = (term95 y x z).
Proof. exact (TRANS (@lem1677572 y x z) (@lem1677581 y x z)). Qed.
Lemma lem1677583 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1677584 (y : real) (x : real) (z : real) : (term96 y x z) = (term97 y x z).
Proof. exact (MK_COMB (@lem1677583) (@lem1677582 y x z)). Qed.
Lemma lem1677585 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1677586 (x : real) (y : real) (z : real) : (term91 x y z) = (term98 x y z).
Proof. exact (MK_COMB (@lem1677584 y x z) (@lem1677585 y z)). Qed.
Lemma lem1677587 (x : real) (y : real) (z : real) : (term88 y x z) = (term98 x y z).
Proof. exact (TRANS (@lem1677569 x y z) (@lem1677586 x y z)). Qed.
Lemma lem1677589 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term99 u v a.
Proof. exact (conj (@lem1677468 u v a h2) (@lem1677476 u v a h1)). Qed.
Lemma lem1677591 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (EQ_MP (@lem1677587 x y z) (@lem1677566 y x z)). Qed.
Lemma lem1677592 (u : real) (v : real) (a : real) : term100 u v a.
Proof. exact (@lem1677591 (term30 u v a) (term28 a) (term31 u v a)). Qed.
Lemma lem1677595 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : (term28 a) = (term31 u v a).
Proof. exact (@lem1677592 u v a (@lem1677589 u v a h1 h2)). Qed.
Lemma lem1677596 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term101 u v a.
Proof. exact (fun h0 : term102 u v a => @lem1677595 u v a h1 h2). Qed.
Lemma lem1677598 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1677599 (u : real) (v : real) (a : real) : (term101 u v a) = ((term28 a) = (term31 u v a)).
Proof. exact (@lem1677598 ((term28 a) = (term31 u v a))). Qed.
Lemma lem1677600 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : (term28 a) = (term31 u v a).
Proof. exact (EQ_MP (@lem1677599 u v a) (@lem1677596 u v a h1 h2)). Qed.
Lemma lem1677602 (_25869 : real) (h1 : term10) : (term28 _25869) = _25869.
Proof. exact (EQ_MP (@lem1677262 _25869) (@lem1677261 _25869 h1)). Qed.
Lemma lem1677603 (a : real) (h1 : term10) : (term28 a) = a.
Proof. exact (@lem1677602 a h1). Qed.
Lemma lem1677604 (a : real) (h1 : term10) : term103 a.
Proof. exact (fun h0 : term104 a => @lem1677603 a h1). Qed.
Lemma lem1677606 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1677607 (a : real) : (term103 a) = ((term28 a) = a).
Proof. exact (@lem1677606 ((term28 a) = a)). Qed.
Lemma lem1677608 (a : real) (h1 : term10) : (term28 a) = a.
Proof. exact (EQ_MP (@lem1677607 a) (@lem1677604 a h1)). Qed.
Lemma lem1677609 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term105 u v a.
Proof. exact (conj (@lem1677600 u v a h1 h3) (@lem1677608 a h2)). Qed.
Lemma lem1677611 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (EQ_MP (@lem1677587 x y z) (@lem1677566 y x z)). Qed.
Lemma lem1677612 (u : real) (v : real) (a : real) : term106 u v a.
Proof. exact (@lem1677611 (term28 a) (term31 u v a) a). Qed.
Lemma lem1677615 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : (term31 u v a) = a.
Proof. exact (@lem1677612 u v a (@lem1677609 u v a h1 h2 h3)). Qed.
Lemma lem1677616 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term107 u v a.
Proof. exact (fun h0 : term44 u v a => @lem1677615 u v a h1 h2 h3). Qed.
Lemma lem1677618 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1677619 (u : real) (v : real) (a : real) : (term107 u v a) = ((term31 u v a) = a).
Proof. exact (@lem1677618 ((term31 u v a) = a)). Qed.
Lemma lem1677620 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : (term31 u v a) = a.
Proof. exact (EQ_MP (@lem1677619 u v a) (@lem1677616 u v a h1 h2 h3)). Qed.
Lemma lem1677623 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1677625 (u : real) (v : real) (a : real) : (term44 u v a) = (term108 u v a).
Proof. exact (@lem1677623 ((term31 u v a) = a)). Qed.
Lemma lem1677628 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term108 u v a.
Proof. exact (EQ_MP (@lem1677625 u v a) (@lem1677271 u v a h1)). Qed.
Lemma lem1677631 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (@lem1677628 u v a h3 (@lem1677620 u v a h1 h2 h3)). Qed.
Lemma lem1677632 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term109.
Proof. exact (fun h0 : ~ False => @lem1677631 u v a h1 h2 h3). Qed.
Lemma lem1677634 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1677635 : term109 = False.
Proof. exact (@lem1677634 False). Qed.
Lemma lem1677636 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1677635) (@lem1677632 u v a h1 h2 h3)). Qed.
Lemma lem1677637 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1677636 u v a h1 h2 h3) (fun h4 : False => @lem1677243 h2)). Qed.
Lemma lem1677638 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1677637 u v a h1 h2 h3) (@lem1677243 h2)). Qed.
Lemma lem1677639 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1677638 u v a h1 h2 h3) (fun h4 : False => @lem1677236 h1)). Qed.
Lemma lem1677640 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1677639 u v a h1 h2 h3) (@lem1677236 h1)). Qed.
Lemma lem1677641 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1677640 u v a h1 h2 h3) (fun h4 : False => @lem1677221 h2)). Qed.
Lemma lem1677642 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1677641 u v a h1 h2 h3) (@lem1677221 h2)). Qed.
Lemma lem1677643 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1677642 u v a h1 h2 h3) (fun h4 : False => @lem1677202 h1)). Qed.
Lemma lem1677644 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1677643 u v a h1 h2 h3) (@lem1677202 h1)). Qed.
Lemma lem1677645 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1677644 u v a h1 h2 h3) (fun h4 : False => @lem1677129 h2)). Qed.
Lemma lem1677646 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1677645 u v a h1 h2 h3) (@lem1677129 h2)). Qed.
Lemma lem1677647 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : term37 = False.
Proof. exact (prop_ext (fun h4 : term37 => @lem1677646 u v a h1 h2 h3) (fun h4 : False => @lem1677116 h1)). Qed.
Lemma lem1677648 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term10) (h3 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1677647 u v a h1 h2 h3) (@lem1677116 h1)). Qed.
Lemma lem1677649 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term8.
Proof. exact (fun h0 : term10 => @lem1677648 u v a h1 h0 h2). Qed.
Lemma lem1677650 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1677651 (u : real) (v : real) (a : real) (h1 : term37) (h2 : term3 u v a) : term9.
Proof. exact (EQ_MP (@lem1677650) (@lem1677649 u v a h1 h2)). Qed.
Lemma lem1677652 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term13.
Proof. exact (fun h0 : term37 => @lem1677651 u v a h0 h1). Qed.
Lemma lem1677653 (u : real) (v : real) (a : real) : term15 u v a.
Proof. exact (fun h0 : term3 u v a => @lem1677652 u v a h0). Qed.
Lemma lem1677658 (v : real) (a : real) : term19 v a.
Proof. exact (fun u : real => @lem1677653 u v a). Qed.
Lemma lem1677663 (a : real) : term23 a.
Proof. exact (fun v : real => @lem1677658 v a). Qed.
Lemma lem1677668 : term27.
Proof. exact (fun a : real => @lem1677663 a). Qed.
Lemma lem1677669 : term26.
Proof. exact (EQ_MP (@lem1677074) (@lem1677668)). Qed.
Lemma lem1677670 (a : real) : term110 a.
Proof. exact (@lem1677669 a). Qed.
Lemma lem1677671 (a : real) : (term110 a) = (term22 a).
Proof. exact (eq_refl (term110 a)). Qed.
Lemma lem1677672 (a : real) : term22 a.
Proof. exact (EQ_MP (@lem1677671 a) (@lem1677670 a)). Qed.
Lemma lem1677673 (a : real) (v : real) : term111 a v.
Proof. exact (@lem1677672 a v). Qed.
Lemma lem1677674 (v : real) (a : real) : (term111 a v) = (term18 v a).
Proof. exact (eq_refl (term111 a v)). Qed.
Lemma lem1677675 (v : real) (a : real) : term18 v a.
Proof. exact (EQ_MP (@lem1677674 v a) (@lem1677673 a v)). Qed.
Lemma lem1677676 (v : real) (a : real) (u : real) : term112 v a u.
Proof. exact (@lem1677675 v a u). Qed.
Lemma lem1677677 (u : real) (v : real) (a : real) : (term112 v a u) = (term4 u v a).
Proof. exact (eq_refl (term112 v a u)). Qed.
Lemma lem1677678 (u : real) (v : real) (a : real) : term4 u v a.
Proof. exact (EQ_MP (@lem1677677 u v a) (@lem1677676 v a u)). Qed.
Lemma lem1677680 (u : real) (v : real) (a : real) : term4 u v a.
Proof. exact (@lem1676914 u v a (@lem1677678 u v a)). Qed.
Lemma lem1677681 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term12.
Proof. exact (@lem1677680 u v a (@lem1676899 u v a h1)). Qed.
Lemma lem1677682 (u : real) (v : real) (a : real) (h1 : term3 u v a) : term8.
Proof. exact (@lem1677681 u v a h1 (@lem1487144)). Qed.
Lemma lem1677683 (u : real) (v : real) (a : real) (h1 : term3 u v a) : False.
Proof. exact (@lem1677682 u v a h1 (@lem1338986)). Qed.
Lemma lem1677684 (u : real) (v : real) (a : real) (h1 : term3 u v a) : (term3 u v a) = False.
Proof. exact (prop_ext (fun h2 : term3 u v a => @lem1677683 u v a h1) (fun h2 : False => @lem1676899 u v a h1)). Qed.
Lemma lem1677685 (u : real) (v : real) (a : real) (h1 : term3 u v a) : False.
Proof. exact (EQ_MP (@lem1677684 u v a h1) (@lem1676899 u v a h1)). Qed.
Lemma lem1677686 (u : real) (v : real) (a : real) : term2 u v a.
Proof. exact (fun h0 : term3 u v a => @lem1677685 u v a h0). Qed.
Lemma lem1677687 (u : real) (v : real) (a : real) : term1 u v a.
Proof. exact (EQ_MP (@lem1676898 u v a) (@lem1677686 u v a)). Qed.
Lemma lem1677688 (t1 : Prop) : term113 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1677689 (t1 : Prop) : (term113 t1) = (term114 t1).
Proof. exact (eq_refl (term113 t1)). Qed.
Lemma lem1677690 (t1 : Prop) : term114 t1.
Proof. exact (EQ_MP (@lem1677689 t1) (@lem1677688 t1)). Qed.
Lemma lem1677691 (t1 : Prop) (t2 : Prop) : term115 t1 t2.
Proof. exact (@lem1677690 t1 t2). Qed.
Lemma lem1677692 (t1 : Prop) (t2 : Prop) : (term115 t1 t2) = (term116 t1 t2).
Proof. exact (eq_refl (term115 t1 t2)). Qed.
Lemma lem1677693 (t1 : Prop) (t2 : Prop) : term116 t1 t2.
Proof. exact (EQ_MP (@lem1677692 t1 t2) (@lem1677691 t1 t2)). Qed.
Lemma lem1677694 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term117 t1 t2 t3.
Proof. exact (@lem1677693 t1 t2 t3). Qed.
Lemma lem1677695 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term117 t1 t2 t3) = ((term60 t1 t2 t3) = (term118 t1 t2 t3)).
Proof. exact (eq_refl (term117 t1 t2 t3)). Qed.
Lemma lem1677696 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term60 t1 t2 t3) = (term118 t1 t2 t3).
Proof. exact (EQ_MP (@lem1677695 t1 t2 t3) (@lem1677694 t1 t2 t3)). Qed.
Lemma lem1677697 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term118 t1 t2 t3) = (term60 t1 t2 t3).
Proof. exact (SYM (@lem1677696 t1 t2 t3)). Qed.
Lemma lem1677698 : term119.
Proof. exact (fun b : real => @lem1673888 b). Qed.
Lemma lem1677699 (u : real) (v : real) : term120 u v.
Proof. exact (fun a : real => @lem1677687 u v a). Qed.
Lemma lem1677700 (u : real) : term121 u.
Proof. exact (fun v : real => @lem1677699 u v). Qed.
Lemma lem1677701 : term122.
Proof. exact (fun u : real => @lem1677700 u). Qed.
Lemma lem1677703 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1677704 : term123 = term124.
Proof. exact (@lem1677703 term123). Qed.
Lemma lem1677705 : term124 = term123.
Proof. exact (SYM (@lem1677704)). Qed.
Lemma lem1677706 (h1 : term125) : term125.
Proof. exact (h1). Qed.
Lemma lem1677709 (h1 : term126) : term126.
Proof. exact (h1). Qed.
Lemma lem1677710 : term127.
Proof. exact (fun h0 : term126 => @lem1677709 h0). Qed.
Lemma lem1677711 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem1677712 (h1 : term126) : term126.
Proof. exact (h1). Qed.
Lemma lem1677713 (h1 : term126) (h2 : term127) : term126.
Proof. exact (@lem1677711 h2 (@lem1677712 h1)). Qed.
Lemma lem1677714 (h1 : term126) : term128.
Proof. exact (fun h0 : term127 => @lem1677713 h1 h0). Qed.
Lemma lem1677715 (h1 : term127) : term127.
Proof. exact (h1). Qed.
Lemma lem1677716 (h1 : term126) (h2 : term127) : term126.
Proof. exact (@lem1677714 h1 (@lem1677715 h2)). Qed.
Lemma lem1677717 (h1 : term127) : term127.
Proof. exact (fun h0 : term126 => @lem1677716 h0 h1). Qed.
Lemma lem1677718 : term129.
Proof. exact (fun h0 : term127 => @lem1677717 h0). Qed.
Lemma lem1677721 : term127.
Proof. exact (@lem1677718 (@lem1677710)). Qed.
Lemma lem1677771 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1677772 : term130 = term131.
Proof. exact (@lem1677771 term119). Qed.
Lemma lem1677807 : term132 = term132.
Proof. exact (eq_refl term132). Qed.
Lemma lem1677808 : term133 = term134.
Proof. exact (MK_COMB (@lem1677807) (@lem1677772)). Qed.
Lemma lem1677811 : term135 = term135.
Proof. exact (eq_refl term135). Qed.
Lemma lem1677818 : term126 = term136.
Proof. exact (MK_COMB (@lem1677811) (@lem1677808)). Qed.
Lemma lem1677839 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term137 x y u a v b).
Proof. exact (eq_refl (term137 x y u a v b)). Qed.
Lemma lem1677840 (x : real) (y : real) (u : real) (a : real) (b : real) : (term138 x y u a b) = (term138 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1677839 x y u a v b)). Qed.
Lemma lem1677841 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677842 (x : real) (y : real) (u : real) (a : real) (b : real) : (term139 x y u a b) = (term139 x y u a b).
Proof. exact (MK_COMB (@lem1677841) (@lem1677840 x y u a b)). Qed.
Lemma lem1677843 (x : real) (y : real) (a : real) (b : real) : (term140 x y a b) = (term140 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1677842 x y u a b)). Qed.
Lemma lem1677844 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677845 (x : real) (y : real) (a : real) (b : real) : (term141 x y a b) = (term141 x y a b).
Proof. exact (MK_COMB (@lem1677844) (@lem1677843 x y a b)). Qed.
Lemma lem1677846 (x : real) (y : real) (b : real) : (term142 x y b) = (term142 x y b).
Proof. exact (fun_ext (fun a : real => @lem1677845 x y a b)). Qed.
Lemma lem1677847 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677848 (x : real) (y : real) (b : real) : (term143 x y b) = (term143 x y b).
Proof. exact (MK_COMB (@lem1677847) (@lem1677846 x y b)). Qed.
Lemma lem1677849 (x : real) (b : real) : (term144 x b) = (term144 x b).
Proof. exact (fun_ext (fun y : real => @lem1677848 x y b)). Qed.
Lemma lem1677850 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677851 (x : real) (b : real) : (term145 x b) = (term145 x b).
Proof. exact (MK_COMB (@lem1677850) (@lem1677849 x b)). Qed.
Lemma lem1677852 (b : real) : (term146 b) = (term146 b).
Proof. exact (fun_ext (fun x : real => @lem1677851 x b)). Qed.
Lemma lem1677853 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677854 (b : real) : (term147 b) = (term147 b).
Proof. exact (MK_COMB (@lem1677853) (@lem1677852 b)). Qed.
Lemma lem1677855 : term148 = term148.
Proof. exact (fun_ext (fun b : real => @lem1677854 b)). Qed.
Lemma lem1677856 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677857 : term119 = term119.
Proof. exact (MK_COMB (@lem1677856) (@lem1677855)). Qed.
Lemma lem1677858 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1677859 : term131 = term131.
Proof. exact (MK_COMB (@lem1677858) (@lem1677857)). Qed.
Lemma lem1677864 (u : real) (v : real) (a : real) : (term1 u v a) = (term1 u v a).
Proof. exact (eq_refl (term1 u v a)). Qed.
Lemma lem1677865 (u : real) (v : real) : (term149 u v) = (term149 u v).
Proof. exact (fun_ext (fun a : real => @lem1677864 u v a)). Qed.
Lemma lem1677866 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677867 (u : real) (v : real) : (term120 u v) = (term120 u v).
Proof. exact (MK_COMB (@lem1677866) (@lem1677865 u v)). Qed.
Lemma lem1677868 (u : real) : (term150 u) = (term150 u).
Proof. exact (fun_ext (fun v : real => @lem1677867 u v)). Qed.
Lemma lem1677869 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677870 (u : real) : (term121 u) = (term121 u).
Proof. exact (MK_COMB (@lem1677869) (@lem1677868 u)). Qed.
Lemma lem1677871 : term151 = term151.
Proof. exact (fun_ext (fun u : real => @lem1677870 u)). Qed.
Lemma lem1677872 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677873 : term122 = term122.
Proof. exact (MK_COMB (@lem1677872) (@lem1677871)). Qed.
Lemma lem1677874 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1677875 : term132 = term132.
Proof. exact (MK_COMB (@lem1677874) (@lem1677873)). Qed.
Lemma lem1677876 : term134 = term134.
Proof. exact (MK_COMB (@lem1677875) (@lem1677859)). Qed.
Lemma lem1677897 (u : real) (x : real) (v : real) (y : real) (a : real) : (term152 u x v y a) = (term152 u x v y a).
Proof. exact (eq_refl (term152 u x v y a)). Qed.
Lemma lem1677898 (u : real) (x : real) (y : real) (a : real) : (term153 u x y a) = (term153 u x y a).
Proof. exact (fun_ext (fun v : real => @lem1677897 u x v y a)). Qed.
Lemma lem1677899 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677900 (u : real) (x : real) (y : real) (a : real) : (term154 u x y a) = (term154 u x y a).
Proof. exact (MK_COMB (@lem1677899) (@lem1677898 u x y a)). Qed.
Lemma lem1677901 (x : real) (y : real) (a : real) : (term155 x y a) = (term155 x y a).
Proof. exact (fun_ext (fun u : real => @lem1677900 u x y a)). Qed.
Lemma lem1677902 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677903 (x : real) (y : real) (a : real) : (term156 x y a) = (term156 x y a).
Proof. exact (MK_COMB (@lem1677902) (@lem1677901 x y a)). Qed.
Lemma lem1677904 (x : real) (y : real) : (term157 x y) = (term157 x y).
Proof. exact (fun_ext (fun a : real => @lem1677903 x y a)). Qed.
Lemma lem1677905 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677906 (x : real) (y : real) : (term158 x y) = (term158 x y).
Proof. exact (MK_COMB (@lem1677905) (@lem1677904 x y)). Qed.
Lemma lem1677907 (x : real) : (term159 x) = (term159 x).
Proof. exact (fun_ext (fun y : real => @lem1677906 x y)). Qed.
Lemma lem1677908 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677909 (x : real) : (term160 x) = (term160 x).
Proof. exact (MK_COMB (@lem1677908) (@lem1677907 x)). Qed.
Lemma lem1677910 : term161 = term161.
Proof. exact (fun_ext (fun x : real => @lem1677909 x)). Qed.
Lemma lem1677911 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1677912 : term123 = term123.
Proof. exact (MK_COMB (@lem1677911) (@lem1677910)). Qed.
Lemma lem1677913 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1677914 : term125 = term125.
Proof. exact (MK_COMB (@lem1677913) (@lem1677912)). Qed.
Lemma lem1677915 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1677916 : term135 = term135.
Proof. exact (MK_COMB (@lem1677915) (@lem1677914)). Qed.
Lemma lem1677917 : term136 = term136.
Proof. exact (MK_COMB (@lem1677916) (@lem1677876)). Qed.
Lemma lem1678030 : term126 = term136.
Proof. exact (TRANS (@lem1677818) (@lem1677917)). Qed.
Lemma lem1678031 : term136 = term126.
Proof. exact (SYM (@lem1678030)). Qed.
Lemma lem1678032 (h1 : term125) : term125.
Proof. exact (h1). Qed.
Lemma lem1678033 (h1 : term122) : term122.
Proof. exact (h1). Qed.
Lemma lem1678034 (h1 : term119) : term119.
Proof. exact (h1). Qed.
Lemma lem1678057 (u : real) (x : real) (v : real) (y : real) (a : real) : (term162 u x v y a) = (term163 u x v y a).
Proof. exact (@lem17362 (term164 x y a u v) (term165 u x v y a)). Qed.
Lemma lem1678058 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1678059 (u : real) (x : real) (y : real) (a : real) : (term168 u x y a) = (term169 u x y a).
Proof. exact (@lem1678058 (term153 u x y a)). Qed.
Lemma lem1678060 (u : real) (x : real) (v : real) (y : real) (a : real) : (term170 u x y a v) = (term152 u x v y a).
Proof. exact (eq_refl (term170 u x y a v)). Qed.
Lemma lem1678061 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1678062 (u : real) (x : real) (v : real) (y : real) (a : real) : (term171 u x y a v) = (term162 u x v y a).
Proof. exact (MK_COMB (@lem1678061) (@lem1678060 u x v y a)). Qed.
Lemma lem1678063 (u : real) (x : real) (v : real) (y : real) (a : real) : (term171 u x y a v) = (term163 u x v y a).
Proof. exact (TRANS (@lem1678062 u x v y a) (@lem1678057 u x v y a)). Qed.
Lemma lem1678064 (u : real) (x : real) (y : real) (a : real) : (term172 u x y a) = (term173 u x y a).
Proof. exact (fun_ext (fun v : real => @lem1678063 u x v y a)). Qed.
Lemma lem1678065 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1678066 (u : real) (x : real) (y : real) (a : real) : (term169 u x y a) = (term174 u x y a).
Proof. exact (MK_COMB (@lem1678065) (@lem1678064 u x y a)). Qed.
Lemma lem1678067 (u : real) (x : real) (y : real) (a : real) : (term168 u x y a) = (term174 u x y a).
Proof. exact (TRANS (@lem1678059 u x y a) (@lem1678066 u x y a)). Qed.
Lemma lem1678068 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1678069 (x : real) (y : real) (a : real) : (term175 x y a) = (term176 x y a).
Proof. exact (@lem1678068 (term155 x y a)). Qed.
Lemma lem1678070 (u : real) (x : real) (y : real) (a : real) : (term177 x y a u) = (term154 u x y a).
Proof. exact (eq_refl (term177 x y a u)). Qed.
Lemma lem1678071 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1678072 (u : real) (x : real) (y : real) (a : real) : (term178 x y a u) = (term168 u x y a).
Proof. exact (MK_COMB (@lem1678071) (@lem1678070 u x y a)). Qed.
Lemma lem1678073 (u : real) (x : real) (y : real) (a : real) : (term178 x y a u) = (term174 u x y a).
Proof. exact (TRANS (@lem1678072 u x y a) (@lem1678067 u x y a)). Qed.
Lemma lem1678074 (x : real) (y : real) (a : real) : (term179 x y a) = (term180 x y a).
Proof. exact (fun_ext (fun u : real => @lem1678073 u x y a)). Qed.
Lemma lem1678075 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1678076 (x : real) (y : real) (a : real) : (term176 x y a) = (term181 x y a).
Proof. exact (MK_COMB (@lem1678075) (@lem1678074 x y a)). Qed.
Lemma lem1678077 (x : real) (y : real) (a : real) : (term175 x y a) = (term181 x y a).
Proof. exact (TRANS (@lem1678069 x y a) (@lem1678076 x y a)). Qed.
Lemma lem1678078 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1678079 (x : real) (y : real) : (term182 x y) = (term183 x y).
Proof. exact (@lem1678078 (term157 x y)). Qed.
Lemma lem1678080 (x : real) (y : real) (a : real) : (term184 x y a) = (term156 x y a).
Proof. exact (eq_refl (term184 x y a)). Qed.
Lemma lem1678081 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1678082 (x : real) (y : real) (a : real) : (term185 x y a) = (term175 x y a).
Proof. exact (MK_COMB (@lem1678081) (@lem1678080 x y a)). Qed.
Lemma lem1678083 (x : real) (y : real) (a : real) : (term185 x y a) = (term181 x y a).
Proof. exact (TRANS (@lem1678082 x y a) (@lem1678077 x y a)). Qed.
Lemma lem1678084 (x : real) (y : real) : (term186 x y) = (term187 x y).
Proof. exact (fun_ext (fun a : real => @lem1678083 x y a)). Qed.
Lemma lem1678085 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1678086 (x : real) (y : real) : (term183 x y) = (term188 x y).
Proof. exact (MK_COMB (@lem1678085) (@lem1678084 x y)). Qed.
Lemma lem1678087 (x : real) (y : real) : (term182 x y) = (term188 x y).
Proof. exact (TRANS (@lem1678079 x y) (@lem1678086 x y)). Qed.
Lemma lem1678088 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1678089 (x : real) : (term189 x) = (term190 x).
Proof. exact (@lem1678088 (term159 x)). Qed.
Lemma lem1678090 (x : real) (y : real) : (term191 x y) = (term158 x y).
Proof. exact (eq_refl (term191 x y)). Qed.
Lemma lem1678091 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1678092 (x : real) (y : real) : (term192 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1678091) (@lem1678090 x y)). Qed.
Lemma lem1678093 (x : real) (y : real) : (term192 x y) = (term188 x y).
Proof. exact (TRANS (@lem1678092 x y) (@lem1678087 x y)). Qed.
Lemma lem1678094 (x : real) : (term193 x) = (term194 x).
Proof. exact (fun_ext (fun y : real => @lem1678093 x y)). Qed.
Lemma lem1678095 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1678096 (x : real) : (term190 x) = (term195 x).
Proof. exact (MK_COMB (@lem1678095) (@lem1678094 x)). Qed.
Lemma lem1678097 (x : real) : (term189 x) = (term195 x).
Proof. exact (TRANS (@lem1678089 x) (@lem1678096 x)). Qed.
Lemma lem1678098 (P : real -> Prop) : (term166 P) = (term167 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1678099 : term125 = term196.
Proof. exact (@lem1678098 term161). Qed.
Lemma lem1678100 (x : real) : (term197 x) = (term160 x).
Proof. exact (eq_refl (term197 x)). Qed.
Lemma lem1678101 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1678102 (x : real) : (term198 x) = (term189 x).
Proof. exact (MK_COMB (@lem1678101) (@lem1678100 x)). Qed.
Lemma lem1678103 (x : real) : (term198 x) = (term195 x).
Proof. exact (TRANS (@lem1678102 x) (@lem1678097 x)). Qed.
Lemma lem1678104 : term199 = term200.
Proof. exact (fun_ext (fun x : real => @lem1678103 x)). Qed.
Lemma lem1678105 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1678106 : term196 = term201.
Proof. exact (MK_COMB (@lem1678105) (@lem1678104)). Qed.
Lemma lem1678175 : term125 = term201.
Proof. exact (TRANS (@lem1678099) (@lem1678106)). Qed.
Lemma lem1678176 (h1 : term125) : term201.
Proof. exact (EQ_MP (@lem1678175) (@lem1678032 h1)). Qed.
Lemma lem1678183 (u : real) (v : real) (a : real) : (term1 u v a) = (term202 u v a).
Proof. exact (@lem17265 ((real_add u v) = term39) ((term31 u v a) = a)). Qed.
Lemma lem1678184 (u : real) (v : real) : (term149 u v) = (term203 u v).
Proof. exact (fun_ext (fun a : real => @lem1678183 u v a)). Qed.
Lemma lem1678185 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678186 (u : real) (v : real) : (term120 u v) = (term204 u v).
Proof. exact (MK_COMB (@lem1678185) (@lem1678184 u v)). Qed.
Lemma lem1678187 (u : real) : (term150 u) = (term205 u).
Proof. exact (fun_ext (fun v : real => @lem1678186 u v)). Qed.
Lemma lem1678188 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678189 (u : real) : (term121 u) = (term206 u).
Proof. exact (MK_COMB (@lem1678188) (@lem1678187 u)). Qed.
Lemma lem1678190 : term151 = term207.
Proof. exact (fun_ext (fun u : real => @lem1678189 u)). Qed.
Lemma lem1678191 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678192 : term122 = term208.
Proof. exact (MK_COMB (@lem1678191) (@lem1678190)). Qed.
Lemma lem1678202 {A : Type'} (P : Prop) (Q : A -> Prop) : (term209 A P Q) = (term210 A P Q).
Proof. exact (EQ_MP (@lem18941 A P Q) (@lem18940 A P Q)). Qed.
Lemma lem1678203 (P : Prop) (Q : real -> Prop) : (term211 P Q) = (term212 P Q).
Proof. exact (@lem1678202 real P Q). Qed.
Lemma lem1678204 (u : real) (v : real) : (term213 u v) = (term214 u v).
Proof. exact (@lem1678203 (term52 u v) (term215 u v)). Qed.
Lemma lem1678205 (u : real) (v : real) (a : real) : (term216 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term216 u v a)). Qed.
Lemma lem1678206 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1678207 (u : real) (v : real) (a : real) : (term218 u v a) = (term202 u v a).
Proof. exact (MK_COMB (@lem1678206 u v) (@lem1678205 u v a)). Qed.
Lemma lem1678208 (u : real) (v : real) : (term219 u v) = (term203 u v).
Proof. exact (fun_ext (fun a : real => @lem1678207 u v a)). Qed.
Lemma lem1678209 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678210 (u : real) (v : real) : (term213 u v) = (term204 u v).
Proof. exact (MK_COMB (@lem1678209) (@lem1678208 u v)). Qed.
Lemma lem1678211 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1678212 (u : real) (v : real) : (term220 u v) = (term221 u v).
Proof. exact (MK_COMB (@lem1678211) (@lem1678210 u v)). Qed.
Lemma lem1678213 (u : real) (v : real) (a : real) : (term216 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term216 u v a)). Qed.
Lemma lem1678214 (u : real) (v : real) : (term222 u v) = (term215 u v).
Proof. exact (fun_ext (fun a : real => @lem1678213 u v a)). Qed.
Lemma lem1678215 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678216 (u : real) (v : real) : (term223 u v) = (term224 u v).
Proof. exact (MK_COMB (@lem1678215) (@lem1678214 u v)). Qed.
Lemma lem1678217 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1678218 (u : real) (v : real) : (term214 u v) = (term225 u v).
Proof. exact (MK_COMB (@lem1678217 u v) (@lem1678216 u v)). Qed.
Lemma lem1678219 (u : real) (v : real) : ((term213 u v) = (term214 u v)) = ((term204 u v) = (term225 u v)).
Proof. exact (MK_COMB (@lem1678212 u v) (@lem1678218 u v)). Qed.
Lemma lem1678220 (u : real) (v : real) : (term204 u v) = (term225 u v).
Proof. exact (EQ_MP (@lem1678219 u v) (@lem1678204 u v)). Qed.
Lemma lem1678225 (u : real) : (term205 u) = (term226 u).
Proof. exact (fun_ext (fun v : real => @lem1678220 u v)). Qed.
Lemma lem1678226 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678227 (u : real) : (term206 u) = (term227 u).
Proof. exact (MK_COMB (@lem1678226) (@lem1678225 u)). Qed.
Lemma lem1678276 : term207 = term228.
Proof. exact (fun_ext (fun u : real => @lem1678227 u)). Qed.
Lemma lem1678277 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678284 : term208 = term229.
Proof. exact (MK_COMB (@lem1678277) (@lem1678276)). Qed.
Lemma lem1678285 : term122 = term229.
Proof. exact (TRANS (@lem1678192) (@lem1678284)). Qed.
Lemma lem1678286 (h1 : term122) : term229.
Proof. exact (EQ_MP (@lem1678285) (@lem1678033 h1)). Qed.
Lemma lem1678296 (u : real) (v : real) : (term230 u v) = (term231 u v).
Proof. exact (@lem17045 (term232 v) ((real_add u v) = term39)). Qed.
Lemma lem1678298 (u : real) : (term233 u) = (term233 u).
Proof. exact (eq_refl (term233 u)). Qed.
Lemma lem1678299 (u : real) (v : real) : (term234 u v) = (term235 u v).
Proof. exact (MK_COMB (@lem1678298 u) (@lem1678296 u v)). Qed.
Lemma lem1678300 (u : real) (v : real) : (term236 u v) = (term234 u v).
Proof. exact (@lem17045 (term232 u) (term237 u v)). Qed.
Lemma lem1678301 (u : real) (v : real) : (term236 u v) = (term235 u v).
Proof. exact (TRANS (@lem1678300 u v) (@lem1678299 u v)). Qed.
Lemma lem1678303 (y : real) (b : real) : (term238 y b) = (term238 y b).
Proof. exact (eq_refl (term238 y b)). Qed.
Lemma lem1678304 (y : real) (b : real) (u : real) (v : real) : (term239 y b u v) = (term240 y b u v).
Proof. exact (MK_COMB (@lem1678303 y b) (@lem1678301 u v)). Qed.
Lemma lem1678305 (y : real) (b : real) (u : real) (v : real) : (term241 y b u v) = (term239 y b u v).
Proof. exact (@lem17045 (real_le y b) (term242 u v)). Qed.
Lemma lem1678306 (y : real) (b : real) (u : real) (v : real) : (term241 y b u v) = (term240 y b u v).
Proof. exact (TRANS (@lem1678305 y b u v) (@lem1678304 y b u v)). Qed.
Lemma lem1678308 (x : real) (a : real) : (term238 x a) = (term238 x a).
Proof. exact (eq_refl (term238 x a)). Qed.
Lemma lem1678309 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term243 x a y b u v) = (term244 x a y b u v).
Proof. exact (MK_COMB (@lem1678308 x a) (@lem1678306 y b u v)). Qed.
Lemma lem1678310 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term245 x a y b u v) = (term243 x a y b u v).
Proof. exact (@lem17045 (real_le x a) (term246 y b u v)). Qed.
Lemma lem1678311 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term245 x a y b u v) = (term244 x a y b u v).
Proof. exact (TRANS (@lem1678310 x a y b u v) (@lem1678309 x a y b u v)). Qed.
Lemma lem1678312 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term247 x y u a v b) = (term247 x y u a v b).
Proof. exact (eq_refl (term247 x y u a v b)). Qed.
Lemma lem1678313 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1678314 (x : real) (a : real) (y : real) (b : real) (u : real) (v : real) : (term248 x a y b u v) = (term249 x a y b u v).
Proof. exact (MK_COMB (@lem1678313) (@lem1678311 x a y b u v)). Qed.
Lemma lem1678315 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term250 x y u a v b) = (term251 x y u a v b).
Proof. exact (MK_COMB (@lem1678314 x a y b u v) (@lem1678312 x y u a v b)). Qed.
Lemma lem1678316 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term250 x y u a v b).
Proof. exact (@lem17265 (term252 x a y b u v) (term247 x y u a v b)). Qed.
Lemma lem1678317 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term137 x y u a v b) = (term251 x y u a v b).
Proof. exact (TRANS (@lem1678316 x y u a v b) (@lem1678315 x y u a v b)). Qed.
Lemma lem1678318 (x : real) (y : real) (u : real) (a : real) (b : real) : (term138 x y u a b) = (term253 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1678317 x y u a v b)). Qed.
Lemma lem1678319 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678320 (x : real) (y : real) (u : real) (a : real) (b : real) : (term139 x y u a b) = (term254 x y u a b).
Proof. exact (MK_COMB (@lem1678319) (@lem1678318 x y u a b)). Qed.
Lemma lem1678321 (x : real) (y : real) (a : real) (b : real) : (term140 x y a b) = (term255 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1678320 x y u a b)). Qed.
Lemma lem1678322 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678323 (x : real) (y : real) (a : real) (b : real) : (term141 x y a b) = (term256 x y a b).
Proof. exact (MK_COMB (@lem1678322) (@lem1678321 x y a b)). Qed.
Lemma lem1678324 (x : real) (y : real) (b : real) : (term142 x y b) = (term257 x y b).
Proof. exact (fun_ext (fun a : real => @lem1678323 x y a b)). Qed.
Lemma lem1678325 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678326 (x : real) (y : real) (b : real) : (term143 x y b) = (term258 x y b).
Proof. exact (MK_COMB (@lem1678325) (@lem1678324 x y b)). Qed.
Lemma lem1678327 (x : real) (b : real) : (term144 x b) = (term259 x b).
Proof. exact (fun_ext (fun y : real => @lem1678326 x y b)). Qed.
Lemma lem1678328 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678329 (x : real) (b : real) : (term145 x b) = (term260 x b).
Proof. exact (MK_COMB (@lem1678328) (@lem1678327 x b)). Qed.
Lemma lem1678330 (b : real) : (term146 b) = (term261 b).
Proof. exact (fun_ext (fun x : real => @lem1678329 x b)). Qed.
Lemma lem1678331 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678332 (b : real) : (term147 b) = (term262 b).
Proof. exact (MK_COMB (@lem1678331) (@lem1678330 b)). Qed.
Lemma lem1678333 : term148 = term263.
Proof. exact (fun_ext (fun b : real => @lem1678332 b)). Qed.
Lemma lem1678334 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678407 : term119 = term264.
Proof. exact (MK_COMB (@lem1678334) (@lem1678333)). Qed.
Lemma lem1678408 (h1 : term119) : term264.
Proof. exact (EQ_MP (@lem1678407) (@lem1678034 h1)). Qed.
Lemma lem1678409 (x : real) (h1 : term195 x) : term195 x.
Proof. exact (h1). Qed.
Lemma lem1678410 (x : real) (y : real) (h1 : term188 x y) : term188 x y.
Proof. exact (h1). Qed.
Lemma lem1678411 (x : real) (y : real) (a : real) (h1 : term181 x y a) : term181 x y a.
Proof. exact (h1). Qed.
Lemma lem1678412 (u : real) (x : real) (y : real) (a : real) (h1 : term174 u x y a) : term174 u x y a.
Proof. exact (h1). Qed.
Lemma lem1678430 (u : real) (v : real) (a : real) : ((term31 u v a) = a) = ((term31 u v a) = a).
Proof. exact (eq_refl ((term31 u v a) = a)). Qed.
Lemma lem1678431 (u : real) (v : real) : (term215 u v) = (term215 u v).
Proof. exact (fun_ext (fun a : real => @lem1678430 u v a)). Qed.
Lemma lem1678432 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678433 (u : real) (v : real) : (term224 u v) = (term224 u v).
Proof. exact (MK_COMB (@lem1678432) (@lem1678431 u v)). Qed.
Lemma lem1678452 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1678453 (u : real) (v : real) : (term225 u v) = (term225 u v).
Proof. exact (MK_COMB (@lem1678452 u v) (@lem1678433 u v)). Qed.
Lemma lem1678454 (u : real) : (term226 u) = (term226 u).
Proof. exact (fun_ext (fun v : real => @lem1678453 u v)). Qed.
Lemma lem1678455 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678456 (u : real) : (term227 u) = (term227 u).
Proof. exact (MK_COMB (@lem1678455) (@lem1678454 u)). Qed.
Lemma lem1678457 : term228 = term228.
Proof. exact (fun_ext (fun u : real => @lem1678456 u)). Qed.
Lemma lem1678458 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678459 : term229 = term229.
Proof. exact (MK_COMB (@lem1678458) (@lem1678457)). Qed.
Lemma lem1678460 (h1 : term122) : term229.
Proof. exact (EQ_MP (@lem1678459) (@lem1678286 h1)). Qed.
Lemma lem1678557 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term251 x y u a v b) = (term251 x y u a v b).
Proof. exact (eq_refl (term251 x y u a v b)). Qed.
Lemma lem1678558 (x : real) (y : real) (u : real) (a : real) (b : real) : (term253 x y u a b) = (term253 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1678557 x y u a v b)). Qed.
Lemma lem1678559 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678560 (x : real) (y : real) (u : real) (a : real) (b : real) : (term254 x y u a b) = (term254 x y u a b).
Proof. exact (MK_COMB (@lem1678559) (@lem1678558 x y u a b)). Qed.
Lemma lem1678561 (x : real) (y : real) (a : real) (b : real) : (term255 x y a b) = (term255 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1678560 x y u a b)). Qed.
Lemma lem1678562 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678563 (x : real) (y : real) (a : real) (b : real) : (term256 x y a b) = (term256 x y a b).
Proof. exact (MK_COMB (@lem1678562) (@lem1678561 x y a b)). Qed.
Lemma lem1678564 (x : real) (y : real) (b : real) : (term257 x y b) = (term257 x y b).
Proof. exact (fun_ext (fun a : real => @lem1678563 x y a b)). Qed.
Lemma lem1678565 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678566 (x : real) (y : real) (b : real) : (term258 x y b) = (term258 x y b).
Proof. exact (MK_COMB (@lem1678565) (@lem1678564 x y b)). Qed.
Lemma lem1678567 (x : real) (b : real) : (term259 x b) = (term259 x b).
Proof. exact (fun_ext (fun y : real => @lem1678566 x y b)). Qed.
Lemma lem1678568 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678569 (x : real) (b : real) : (term260 x b) = (term260 x b).
Proof. exact (MK_COMB (@lem1678568) (@lem1678567 x b)). Qed.
Lemma lem1678570 (b : real) : (term261 b) = (term261 b).
Proof. exact (fun_ext (fun x : real => @lem1678569 x b)). Qed.
Lemma lem1678571 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678572 (b : real) : (term262 b) = (term262 b).
Proof. exact (MK_COMB (@lem1678571) (@lem1678570 b)). Qed.
Lemma lem1678573 : term263 = term263.
Proof. exact (fun_ext (fun b : real => @lem1678572 b)). Qed.
Lemma lem1678574 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678575 : term264 = term264.
Proof. exact (MK_COMB (@lem1678574) (@lem1678573)). Qed.
Lemma lem1678576 (h1 : term119) : term264.
Proof. exact (EQ_MP (@lem1678575) (@lem1678408 h1)). Qed.
Lemma lem1678654 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term163 u x v y a.
Proof. exact (h1). Qed.
Lemma lem1678656 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term164 x y a u v.
Proof. exact (proj1 (@lem1678654 u x v y a h1)). Qed.
Lemma lem1678657 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term246 y a u v.
Proof. exact (proj2 (@lem1678656 u x v y a h1)). Qed.
Lemma lem1678659 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term242 u v.
Proof. exact (proj2 (@lem1678657 u x v y a h1)). Qed.
Lemma lem1678661 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term237 u v.
Proof. exact (proj2 (@lem1678659 u x v y a h1)). Qed.
Lemma lem1678666 {A : Type'} (P : Prop) (Q : A -> Prop) : (term210 A P Q) = (term209 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1678667 (P : Prop) (Q : real -> Prop) : (term212 P Q) = (term211 P Q).
Proof. exact (@lem1678666 real P Q). Qed.
Lemma lem1678668 (u : real) (v : real) : (term214 u v) = (term213 u v).
Proof. exact (@lem1678667 (term52 u v) (term215 u v)). Qed.
Lemma lem1678669 (u : real) (v : real) (a : real) : (term216 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term216 u v a)). Qed.
Lemma lem1678670 (u : real) (v : real) : (term222 u v) = (term215 u v).
Proof. exact (fun_ext (fun a : real => @lem1678669 u v a)). Qed.
Lemma lem1678671 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678672 (u : real) (v : real) : (term223 u v) = (term224 u v).
Proof. exact (MK_COMB (@lem1678671) (@lem1678670 u v)). Qed.
Lemma lem1678673 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1678674 (u : real) (v : real) : (term214 u v) = (term225 u v).
Proof. exact (MK_COMB (@lem1678673 u v) (@lem1678672 u v)). Qed.
Lemma lem1678675 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1678676 (u : real) (v : real) : (term265 u v) = (term266 u v).
Proof. exact (MK_COMB (@lem1678675) (@lem1678674 u v)). Qed.
Lemma lem1678677 (u : real) (v : real) (a : real) : (term216 u v a) = ((term31 u v a) = a).
Proof. exact (eq_refl (term216 u v a)). Qed.
Lemma lem1678678 (u : real) (v : real) : (term217 u v) = (term217 u v).
Proof. exact (eq_refl (term217 u v)). Qed.
Lemma lem1678679 (u : real) (v : real) (a : real) : (term218 u v a) = (term202 u v a).
Proof. exact (MK_COMB (@lem1678678 u v) (@lem1678677 u v a)). Qed.
Lemma lem1678680 (u : real) (v : real) : (term219 u v) = (term203 u v).
Proof. exact (fun_ext (fun a : real => @lem1678679 u v a)). Qed.
Lemma lem1678681 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678682 (u : real) (v : real) : (term213 u v) = (term204 u v).
Proof. exact (MK_COMB (@lem1678681) (@lem1678680 u v)). Qed.
Lemma lem1678683 (u : real) (v : real) : ((term214 u v) = (term213 u v)) = ((term225 u v) = (term204 u v)).
Proof. exact (MK_COMB (@lem1678676 u v) (@lem1678682 u v)). Qed.
Lemma lem1678684 (u : real) (v : real) : (term225 u v) = (term204 u v).
Proof. exact (EQ_MP (@lem1678683 u v) (@lem1678668 u v)). Qed.
Lemma lem1678685 (u : real) : (term226 u) = (term205 u).
Proof. exact (fun_ext (fun v : real => @lem1678684 u v)). Qed.
Lemma lem1678686 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678687 (u : real) : (term227 u) = (term206 u).
Proof. exact (MK_COMB (@lem1678686) (@lem1678685 u)). Qed.
Lemma lem1678688 : term228 = term207.
Proof. exact (fun_ext (fun u : real => @lem1678687 u)). Qed.
Lemma lem1678689 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678690 : term229 = term208.
Proof. exact (MK_COMB (@lem1678689) (@lem1678688)). Qed.
Lemma lem1678697 (u : real) (v : real) (a : real) : (term202 u v a) = (term202 u v a).
Proof. exact (eq_refl (term202 u v a)). Qed.
Lemma lem1678698 (u : real) (v : real) : (term203 u v) = (term203 u v).
Proof. exact (fun_ext (fun a : real => @lem1678697 u v a)). Qed.
Lemma lem1678699 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678700 (u : real) (v : real) : (term204 u v) = (term204 u v).
Proof. exact (MK_COMB (@lem1678699) (@lem1678698 u v)). Qed.
Lemma lem1678701 (u : real) : (term205 u) = (term205 u).
Proof. exact (fun_ext (fun v : real => @lem1678700 u v)). Qed.
Lemma lem1678702 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678703 (u : real) : (term206 u) = (term206 u).
Proof. exact (MK_COMB (@lem1678702) (@lem1678701 u)). Qed.
Lemma lem1678704 : term207 = term207.
Proof. exact (fun_ext (fun u : real => @lem1678703 u)). Qed.
Lemma lem1678705 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678706 : term208 = term208.
Proof. exact (MK_COMB (@lem1678705) (@lem1678704)). Qed.
Lemma lem1678707 : term229 = term208.
Proof. exact (TRANS (@lem1678690) (@lem1678706)). Qed.
Lemma lem1678708 (h1 : term122) : term208.
Proof. exact (EQ_MP (@lem1678707) (@lem1678460 h1)). Qed.
Lemma lem1678740 (x : real) (y : real) (u : real) (a : real) (v : real) (b : real) : (term251 x y u a v b) = (term251 x y u a v b).
Proof. exact (eq_refl (term251 x y u a v b)). Qed.
Lemma lem1678741 (x : real) (y : real) (u : real) (a : real) (b : real) : (term253 x y u a b) = (term253 x y u a b).
Proof. exact (fun_ext (fun v : real => @lem1678740 x y u a v b)). Qed.
Lemma lem1678742 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678743 (x : real) (y : real) (u : real) (a : real) (b : real) : (term254 x y u a b) = (term254 x y u a b).
Proof. exact (MK_COMB (@lem1678742) (@lem1678741 x y u a b)). Qed.
Lemma lem1678744 (x : real) (y : real) (a : real) (b : real) : (term255 x y a b) = (term255 x y a b).
Proof. exact (fun_ext (fun u : real => @lem1678743 x y u a b)). Qed.
Lemma lem1678745 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678746 (x : real) (y : real) (a : real) (b : real) : (term256 x y a b) = (term256 x y a b).
Proof. exact (MK_COMB (@lem1678745) (@lem1678744 x y a b)). Qed.
Lemma lem1678747 (x : real) (y : real) (b : real) : (term257 x y b) = (term257 x y b).
Proof. exact (fun_ext (fun a : real => @lem1678746 x y a b)). Qed.
Lemma lem1678748 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678749 (x : real) (y : real) (b : real) : (term258 x y b) = (term258 x y b).
Proof. exact (MK_COMB (@lem1678748) (@lem1678747 x y b)). Qed.
Lemma lem1678750 (x : real) (b : real) : (term259 x b) = (term259 x b).
Proof. exact (fun_ext (fun y : real => @lem1678749 x y b)). Qed.
Lemma lem1678751 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678752 (x : real) (b : real) : (term260 x b) = (term260 x b).
Proof. exact (MK_COMB (@lem1678751) (@lem1678750 x b)). Qed.
Lemma lem1678753 (b : real) : (term261 b) = (term261 b).
Proof. exact (fun_ext (fun x : real => @lem1678752 x b)). Qed.
Lemma lem1678754 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678755 (b : real) : (term262 b) = (term262 b).
Proof. exact (MK_COMB (@lem1678754) (@lem1678753 b)). Qed.
Lemma lem1678756 : term263 = term263.
Proof. exact (fun_ext (fun b : real => @lem1678755 b)). Qed.
Lemma lem1678757 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1678759 : term264 = term264.
Proof. exact (MK_COMB (@lem1678757) (@lem1678756)). Qed.
Lemma lem1678760 (h1 : term119) : term264.
Proof. exact (EQ_MP (@lem1678759) (@lem1678576 h1)). Qed.
Lemma lem1678785 (_25884 : real) (h1 : term122) : term267 _25884.
Proof. exact (@lem1678708 h1 _25884). Qed.
Lemma lem1678786 (_25884 : real) : (term267 _25884) = (term206 _25884).
Proof. exact (eq_refl (term267 _25884)). Qed.
Lemma lem1678787 (_25884 : real) (h1 : term122) : term206 _25884.
Proof. exact (EQ_MP (@lem1678786 _25884) (@lem1678785 _25884 h1)). Qed.
Lemma lem1678788 (_25884 : real) (_25885 : real) (h1 : term122) : term268 _25884 _25885.
Proof. exact (@lem1678787 _25884 h1 _25885). Qed.
Lemma lem1678789 (_25884 : real) (_25885 : real) : (term268 _25884 _25885) = (term204 _25884 _25885).
Proof. exact (eq_refl (term268 _25884 _25885)). Qed.
Lemma lem1678790 (_25884 : real) (_25885 : real) (h1 : term122) : term204 _25884 _25885.
Proof. exact (EQ_MP (@lem1678789 _25884 _25885) (@lem1678788 _25884 _25885 h1)). Qed.
Lemma lem1678791 (_25884 : real) (_25885 : real) (_25886 : real) (h1 : term122) : term269 _25884 _25885 _25886.
Proof. exact (@lem1678790 _25884 _25885 h1 _25886). Qed.
Lemma lem1678792 (_25884 : real) (_25885 : real) (_25886 : real) : (term269 _25884 _25885 _25886) = (term202 _25884 _25885 _25886).
Proof. exact (eq_refl (term269 _25884 _25885 _25886)). Qed.
Lemma lem1678794 (_25887 : real) (h1 : term119) : term270 _25887.
Proof. exact (@lem1678760 h1 _25887). Qed.
Lemma lem1678795 (_25887 : real) : (term270 _25887) = (term262 _25887).
Proof. exact (eq_refl (term270 _25887)). Qed.
Lemma lem1678796 (_25887 : real) (h1 : term119) : term262 _25887.
Proof. exact (EQ_MP (@lem1678795 _25887) (@lem1678794 _25887 h1)). Qed.
Lemma lem1678797 (_25887 : real) (_25888 : real) (h1 : term119) : term271 _25887 _25888.
Proof. exact (@lem1678796 _25887 h1 _25888). Qed.
Lemma lem1678798 (_25888 : real) (_25887 : real) : (term271 _25887 _25888) = (term260 _25888 _25887).
Proof. exact (eq_refl (term271 _25887 _25888)). Qed.
Lemma lem1678799 (_25888 : real) (_25887 : real) (h1 : term119) : term260 _25888 _25887.
Proof. exact (EQ_MP (@lem1678798 _25888 _25887) (@lem1678797 _25887 _25888 h1)). Qed.
Lemma lem1678800 (_25888 : real) (_25887 : real) (_25889 : real) (h1 : term119) : term272 _25888 _25887 _25889.
Proof. exact (@lem1678799 _25888 _25887 h1 _25889). Qed.
Lemma lem1678801 (_25888 : real) (_25889 : real) (_25887 : real) : (term272 _25888 _25887 _25889) = (term258 _25888 _25889 _25887).
Proof. exact (eq_refl (term272 _25888 _25887 _25889)). Qed.
Lemma lem1678802 (_25888 : real) (_25889 : real) (_25887 : real) (h1 : term119) : term258 _25888 _25889 _25887.
Proof. exact (EQ_MP (@lem1678801 _25888 _25889 _25887) (@lem1678800 _25888 _25887 _25889 h1)). Qed.
Lemma lem1678803 (_25888 : real) (_25889 : real) (_25887 : real) (_25890 : real) (h1 : term119) : term273 _25888 _25889 _25887 _25890.
Proof. exact (@lem1678802 _25888 _25889 _25887 h1 _25890). Qed.
Lemma lem1678804 (_25888 : real) (_25889 : real) (_25890 : real) (_25887 : real) : (term273 _25888 _25889 _25887 _25890) = (term256 _25888 _25889 _25890 _25887).
Proof. exact (eq_refl (term273 _25888 _25889 _25887 _25890)). Qed.
Lemma lem1678805 (_25888 : real) (_25889 : real) (_25890 : real) (_25887 : real) (h1 : term119) : term256 _25888 _25889 _25890 _25887.
Proof. exact (EQ_MP (@lem1678804 _25888 _25889 _25890 _25887) (@lem1678803 _25888 _25889 _25887 _25890 h1)). Qed.
Lemma lem1678806 (_25888 : real) (_25889 : real) (_25890 : real) (_25887 : real) (_25891 : real) (h1 : term119) : term274 _25888 _25889 _25890 _25887 _25891.
Proof. exact (@lem1678805 _25888 _25889 _25890 _25887 h1 _25891). Qed.
Lemma lem1678807 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25887 : real) : (term274 _25888 _25889 _25890 _25887 _25891) = (term254 _25888 _25889 _25891 _25890 _25887).
Proof. exact (eq_refl (term274 _25888 _25889 _25890 _25887 _25891)). Qed.
Lemma lem1678808 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25887 : real) (h1 : term119) : term254 _25888 _25889 _25891 _25890 _25887.
Proof. exact (EQ_MP (@lem1678807 _25888 _25889 _25891 _25890 _25887) (@lem1678806 _25888 _25889 _25890 _25887 _25891 h1)). Qed.
Lemma lem1678809 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25887 : real) (_25892 : real) (h1 : term119) : term275 _25888 _25889 _25891 _25890 _25887 _25892.
Proof. exact (@lem1678808 _25888 _25889 _25891 _25890 _25887 h1 _25892). Qed.
Lemma lem1678810 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term275 _25888 _25889 _25891 _25890 _25887 _25892) = (term251 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (eq_refl (term275 _25888 _25889 _25891 _25890 _25887 _25892)). Qed.
Lemma lem1678811 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) (h1 : term119) : term251 _25888 _25889 _25891 _25890 _25892 _25887.
Proof. exact (EQ_MP (@lem1678810 _25888 _25889 _25891 _25890 _25892 _25887) (@lem1678809 _25888 _25889 _25891 _25890 _25887 _25892 h1)). Qed.
Lemma lem1678817 (_25884 : real) (_25885 : real) (_25886 : real) (h1 : term122) : term202 _25884 _25885 _25886.
Proof. exact (EQ_MP (@lem1678792 _25884 _25885 _25886) (@lem1678791 _25884 _25885 _25886 h1)). Qed.
Lemma lem1678821 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term251 _25888 _25889 _25891 _25890 _25892 _25887) = (term276 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (@lem1677697 (term277 _25888 _25890) (term240 _25889 _25887 _25891 _25892) (term247 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1678822 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term278 _25888 _25889 _25891 _25890 _25892 _25887) = (term279 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (@lem1677697 (term277 _25889 _25887) (term235 _25891 _25892) (term247 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1678823 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term280 _25888 _25889 _25891 _25890 _25892 _25887) = (term281 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (@lem1677697 (term282 _25891) (term231 _25891 _25892) (term247 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1678830 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term283 _25888 _25889 _25891 _25890 _25892 _25887) = (term284 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (@lem1677697 (term282 _25892) (term52 _25891 _25892) (term247 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1678831 (_25891 : real) : (term233 _25891) = (term233 _25891).
Proof. exact (eq_refl (term233 _25891)). Qed.
Lemma lem1678834 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term281 _25888 _25889 _25891 _25890 _25892 _25887) = (term285 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (MK_COMB (@lem1678831 _25891) (@lem1678830 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1678835 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term280 _25888 _25889 _25891 _25890 _25892 _25887) = (term285 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (TRANS (@lem1678823 _25888 _25889 _25891 _25890 _25892 _25887) (@lem1678834 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1678836 (_25889 : real) (_25887 : real) : (term238 _25889 _25887) = (term238 _25889 _25887).
Proof. exact (eq_refl (term238 _25889 _25887)). Qed.
Lemma lem1678839 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term279 _25888 _25889 _25891 _25890 _25892 _25887) = (term286 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (MK_COMB (@lem1678836 _25889 _25887) (@lem1678835 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1678840 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term278 _25888 _25889 _25891 _25890 _25892 _25887) = (term286 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (TRANS (@lem1678822 _25888 _25889 _25891 _25890 _25892 _25887) (@lem1678839 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1678841 (_25888 : real) (_25890 : real) : (term238 _25888 _25890) = (term238 _25888 _25890).
Proof. exact (eq_refl (term238 _25888 _25890)). Qed.
Lemma lem1678844 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term276 _25888 _25889 _25891 _25890 _25892 _25887) = (term287 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (MK_COMB (@lem1678841 _25888 _25890) (@lem1678840 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1678846 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term251 _25888 _25889 _25891 _25890 _25892 _25887) = (term287 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (TRANS (@lem1678821 _25888 _25889 _25891 _25890 _25892 _25887) (@lem1678844 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1678847 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) (h1 : term119) : term287 _25888 _25889 _25891 _25890 _25892 _25887.
Proof. exact (EQ_MP (@lem1678846 _25888 _25889 _25891 _25890 _25892 _25887) (@lem1678811 _25888 _25889 _25891 _25890 _25892 _25887 h1)). Qed.
Lemma lem1678849 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term288 u x v y a.
Proof. exact (proj2 (@lem1678654 u x v y a h1)). Qed.
Lemma lem1678860 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1678861 (_25893 : real) (_25895 : real) (h1 : _25893 = _25895) : _25893 = _25895.
Proof. exact (h1). Qed.
Lemma lem1678862 (_25894 : real) (_25896 : real) (h1 : _25894 = _25896) : _25894 = _25896.
Proof. exact (h1). Qed.
Lemma lem1678863 (_25893 : real) (_25895 : real) (h1 : _25893 = _25895) : (real_le _25893) = (real_le _25895).
Proof. exact (MK_COMB (@lem1678860) (@lem1678861 _25893 _25895 h1)). Qed.
Lemma lem1678864 (_25893 : real) (_25895 : real) (_25894 : real) (_25896 : real) (h1 : _25893 = _25895) (h2 : _25894 = _25896) : (real_le _25893 _25894) = (real_le _25895 _25896).
Proof. exact (MK_COMB (@lem1678863 _25893 _25895 h1) (@lem1678862 _25894 _25896 h2)). Qed.
Lemma lem1678866 (b : Prop) (a : Prop) : term289 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1678867 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : term290 _25895 _25896 _25893 _25894.
Proof. exact (@lem1678866 (real_le _25895 _25896) (real_le _25893 _25894)). Qed.
Lemma lem1678868 (_25893 : real) (_25895 : real) (_25894 : real) (_25896 : real) (h1 : _25893 = _25895) (h2 : _25894 = _25896) : term291 _25895 _25896 _25893 _25894.
Proof. exact (@lem1678867 _25895 _25896 _25893 _25894 (@lem1678864 _25893 _25895 _25894 _25896 h1 h2)). Qed.
Lemma lem1678869 (_25896 : real) (_25894 : real) (_25893 : real) (_25895 : real) (h1 : _25893 = _25895) : term292 _25895 _25896 _25893 _25894.
Proof. exact (fun h0 : _25894 = _25896 => @lem1678868 _25893 _25895 _25894 _25896 h1 h0). Qed.
Lemma lem1678871 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1678872 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : (term292 _25895 _25896 _25893 _25894) = (term293 _25895 _25896 _25893 _25894).
Proof. exact (@lem1678871 (_25894 = _25896) (term291 _25895 _25896 _25893 _25894)). Qed.
Lemma lem1678873 (_25896 : real) (_25894 : real) (_25893 : real) (_25895 : real) (h1 : _25893 = _25895) : term293 _25895 _25896 _25893 _25894.
Proof. exact (EQ_MP (@lem1678872 _25895 _25896 _25893 _25894) (@lem1678869 _25896 _25894 _25893 _25895 h1)). Qed.
Lemma lem1678874 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : term294 _25895 _25896 _25893 _25894.
Proof. exact (fun h0 : _25893 = _25895 => @lem1678873 _25896 _25894 _25893 _25895 h0). Qed.
Lemma lem1678876 (a : Prop) (b : Prop) : (a -> b) = (term46 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1678877 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : (term294 _25895 _25896 _25893 _25894) = (term295 _25895 _25896 _25893 _25894).
Proof. exact (@lem1678876 (_25893 = _25895) (term293 _25895 _25896 _25893 _25894)). Qed.
Lemma lem1678878 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : term295 _25895 _25896 _25893 _25894.
Proof. exact (EQ_MP (@lem1678877 _25895 _25896 _25893 _25894) (@lem1678874 _25895 _25896 _25893 _25894)). Qed.
Lemma lem1678938 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1678939 (u : real) (x : real) (v : real) (y : real) : (term296 u x v y) = (term296 u x v y).
Proof. exact (@lem1678938 (term296 u x v y)). Qed.
Lemma lem1678940 (u : real) (x : real) (v : real) (y : real) : term297 u x v y.
Proof. exact (fun h0 : term298 u x v y => @lem1678939 u x v y). Qed.
Lemma lem1678942 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1678943 (u : real) (x : real) (v : real) (y : real) : (term297 u x v y) = ((term296 u x v y) = (term296 u x v y)).
Proof. exact (@lem1678942 ((term296 u x v y) = (term296 u x v y))). Qed.
Lemma lem1678944 (u : real) (x : real) (v : real) (y : real) : (term296 u x v y) = (term296 u x v y).
Proof. exact (EQ_MP (@lem1678943 u x v y) (@lem1678940 u x v y)). Qed.
Lemma lem1678946 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1678661 u x v y a h1)). Qed.
Lemma lem1678947 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1678946 u x v y a h1). Qed.
Lemma lem1678949 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1678950 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1678949 ((real_add u v) = term39)). Qed.
Lemma lem1678951 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1678950 u v) (@lem1678947 u x v y a h1)). Qed.
Lemma lem1678957 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1678958 (_25886 : real) (_25884 : real) (_25885 : real) : (term202 _25884 _25885 _25886) = (term299 _25886 _25884 _25885).
Proof. exact (@lem1678957 ((term31 _25884 _25885 _25886) = _25886) (term52 _25884 _25885)). Qed.
Lemma lem1678968 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1678969 (_25886 : real) (_25884 : real) (_25885 : real) : (term300 _25884 _25885 _25886) = (term301 _25886 _25884 _25885).
Proof. exact (MK_COMB (@lem1678968) (@lem1678958 _25886 _25884 _25885)). Qed.
Lemma lem1678979 (_25886 : real) (_25884 : real) (_25885 : real) : (term299 _25886 _25884 _25885) = (term299 _25886 _25884 _25885).
Proof. exact (eq_refl (term299 _25886 _25884 _25885)). Qed.
Lemma lem1678980 (_25886 : real) (_25884 : real) (_25885 : real) : ((term202 _25884 _25885 _25886) = (term299 _25886 _25884 _25885)) = ((term299 _25886 _25884 _25885) = (term299 _25886 _25884 _25885)).
Proof. exact (MK_COMB (@lem1678969 _25886 _25884 _25885) (@lem1678979 _25886 _25884 _25885)). Qed.
Lemma lem1678982 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1678983 (x : Prop) : (x = x) = True.
Proof. exact (@lem1678982 Prop x). Qed.
Lemma lem1678984 (_25886 : real) (_25884 : real) (_25885 : real) : ((term299 _25886 _25884 _25885) = (term299 _25886 _25884 _25885)) = True.
Proof. exact (@lem1678983 (term299 _25886 _25884 _25885)). Qed.
Lemma lem1678985 (_25886 : real) (_25884 : real) (_25885 : real) : ((term202 _25884 _25885 _25886) = (term299 _25886 _25884 _25885)) = True.
Proof. exact (TRANS (@lem1678980 _25886 _25884 _25885) (@lem1678984 _25886 _25884 _25885)). Qed.
Lemma lem1678986 (_25886 : real) (_25884 : real) (_25885 : real) : True = ((term202 _25884 _25885 _25886) = (term299 _25886 _25884 _25885)).
Proof. exact (SYM (@lem1678985 _25886 _25884 _25885)). Qed.
Lemma lem1678987 (_25886 : real) (_25884 : real) (_25885 : real) : (term202 _25884 _25885 _25886) = (term299 _25886 _25884 _25885).
Proof. exact (EQ_MP (@lem1678986 _25886 _25884 _25885) (@lem0)). Qed.
Lemma lem1678988 (_25886 : real) (_25884 : real) (_25885 : real) (h1 : term122) : term299 _25886 _25884 _25885.
Proof. exact (EQ_MP (@lem1678987 _25886 _25884 _25885) (@lem1678817 _25884 _25885 _25886 h1)). Qed.
Lemma lem1678990 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1678991 (_25884 : real) (_25885 : real) (_25886 : real) : (term299 _25886 _25884 _25885) = (term302 _25884 _25885 _25886).
Proof. exact (@lem1678990 (term52 _25884 _25885) ((term31 _25884 _25885 _25886) = _25886)). Qed.
Lemma lem1678993 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1678994 (_25884 : real) (_25885 : real) : (term303 _25884 _25885) = ((real_add _25884 _25885) = term39).
Proof. exact (@lem1678993 ((real_add _25884 _25885) = term39)). Qed.
Lemma lem1678995 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1678996 (_25884 : real) (_25885 : real) : (term304 _25884 _25885) = (term305 _25884 _25885).
Proof. exact (MK_COMB (@lem1678995) (@lem1678994 _25884 _25885)). Qed.
Lemma lem1678997 (_25884 : real) (_25885 : real) (_25886 : real) : ((term31 _25884 _25885 _25886) = _25886) = ((term31 _25884 _25885 _25886) = _25886).
Proof. exact (eq_refl ((term31 _25884 _25885 _25886) = _25886)). Qed.
Lemma lem1678998 (_25884 : real) (_25885 : real) (_25886 : real) : (term302 _25884 _25885 _25886) = (term1 _25884 _25885 _25886).
Proof. exact (MK_COMB (@lem1678996 _25884 _25885) (@lem1678997 _25884 _25885 _25886)). Qed.
Lemma lem1678999 (_25884 : real) (_25885 : real) (_25886 : real) : (term299 _25886 _25884 _25885) = (term1 _25884 _25885 _25886).
Proof. exact (TRANS (@lem1678991 _25884 _25885 _25886) (@lem1678998 _25884 _25885 _25886)). Qed.
Lemma lem1679002 (_25884 : real) (_25885 : real) (_25886 : real) (h1 : term122) : term1 _25884 _25885 _25886.
Proof. exact (EQ_MP (@lem1678999 _25884 _25885 _25886) (@lem1678988 _25886 _25884 _25885 h1)). Qed.
Lemma lem1679003 (u : real) (v : real) (_25886 : real) (h1 : term122) : term1 u v _25886.
Proof. exact (@lem1679002 u v _25886 h1). Qed.
Lemma lem1679006 (_25886 : real) (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term122) (h2 : term163 u x v y a) : (term31 u v _25886) = _25886.
Proof. exact (@lem1679003 u v _25886 h1 (@lem1678951 u x v y a h2)). Qed.
Lemma lem1679007 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term122) (h2 : term163 u x v y a) : (term31 u v a) = a.
Proof. exact (@lem1679006 a u x v y a h1 h2). Qed.
Lemma lem1679008 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term122) (h2 : term163 u x v y a) : term107 u v a.
Proof. exact (fun h0 : term44 u v a => @lem1679007 u x v y a h1 h2). Qed.
Lemma lem1679010 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1679011 (u : real) (v : real) (a : real) : (term107 u v a) = ((term31 u v a) = a).
Proof. exact (@lem1679010 ((term31 u v a) = a)). Qed.
Lemma lem1679012 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term122) (h2 : term163 u x v y a) : (term31 u v a) = a.
Proof. exact (EQ_MP (@lem1679011 u v a) (@lem1679008 u x v y a h1 h2)). Qed.
Lemma lem1679014 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : real_le x a.
Proof. exact (proj1 (@lem1678656 u x v y a h1)). Qed.
Lemma lem1679015 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term306 x a.
Proof. exact (fun h0 : term277 x a => @lem1679014 u x v y a h1). Qed.
Lemma lem1679017 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1679018 (x : real) (a : real) : (term306 x a) = (real_le x a).
Proof. exact (@lem1679017 (real_le x a)). Qed.
Lemma lem1679019 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : real_le x a.
Proof. exact (EQ_MP (@lem1679018 x a) (@lem1679015 u x v y a h1)). Qed.
Lemma lem1679021 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : real_le y a.
Proof. exact (proj1 (@lem1678657 u x v y a h1)). Qed.
Lemma lem1679022 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term306 y a.
Proof. exact (fun h0 : term277 y a => @lem1679021 u x v y a h1). Qed.
Lemma lem1679024 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1679025 (y : real) (a : real) : (term306 y a) = (real_le y a).
Proof. exact (@lem1679024 (real_le y a)). Qed.
Lemma lem1679026 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : real_le y a.
Proof. exact (EQ_MP (@lem1679025 y a) (@lem1679022 u x v y a h1)). Qed.
Lemma lem1679028 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term232 u.
Proof. exact (proj1 (@lem1678659 u x v y a h1)). Qed.
Lemma lem1679029 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term307 u.
Proof. exact (fun h0 : term282 u => @lem1679028 u x v y a h1). Qed.
Lemma lem1679031 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1679032 (u : real) : (term307 u) = (term232 u).
Proof. exact (@lem1679031 (term232 u)). Qed.
Lemma lem1679033 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term232 u.
Proof. exact (EQ_MP (@lem1679032 u) (@lem1679029 u x v y a h1)). Qed.
Lemma lem1679035 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term232 v.
Proof. exact (proj1 (@lem1678661 u x v y a h1)). Qed.
Lemma lem1679036 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term307 v.
Proof. exact (fun h0 : term282 v => @lem1679035 u x v y a h1). Qed.
Lemma lem1679038 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1679039 (v : real) : (term307 v) = (term232 v).
Proof. exact (@lem1679038 (term232 v)). Qed.
Lemma lem1679040 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term232 v.
Proof. exact (EQ_MP (@lem1679039 v) (@lem1679036 u x v y a h1)). Qed.
Lemma lem1679042 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : (real_add u v) = term39.
Proof. exact (proj2 (@lem1678661 u x v y a h1)). Qed.
Lemma lem1679043 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term51 u v.
Proof. exact (fun h0 : term52 u v => @lem1679042 u x v y a h1). Qed.
Lemma lem1679045 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1679046 (u : real) (v : real) : (term51 u v) = ((real_add u v) = term39).
Proof. exact (@lem1679045 ((real_add u v) = term39)). Qed.
Lemma lem1679047 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : (real_add u v) = term39.
Proof. exact (EQ_MP (@lem1679046 u v) (@lem1679043 u x v y a h1)). Qed.
Lemma lem1679083 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1679084 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term284 _25888 _25889 _25891 _25890 _25892 _25887) = (term308 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (@lem1679083 (term52 _25891 _25892) (term282 _25892) (term247 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1679100 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1679101 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25887 : real) (_25892 : real) : (term309 _25888 _25889 _25891 _25890 _25892 _25887) = (term310 _25888 _25889 _25891 _25890 _25887 _25892).
Proof. exact (@lem1679100 (term247 _25888 _25889 _25891 _25890 _25892 _25887) (term282 _25892)). Qed.
Lemma lem1679107 (_25891 : real) (_25892 : real) : (term217 _25891 _25892) = (term217 _25891 _25892).
Proof. exact (eq_refl (term217 _25891 _25892)). Qed.
Lemma lem1679108 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25887 : real) (_25892 : real) : (term308 _25888 _25889 _25891 _25890 _25892 _25887) = (term311 _25888 _25889 _25891 _25890 _25887 _25892).
Proof. exact (MK_COMB (@lem1679107 _25891 _25892) (@lem1679101 _25888 _25889 _25891 _25890 _25887 _25892)). Qed.
Lemma lem1679112 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1679113 (_25888 : real) (_25889 : real) (_25890 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term311 _25888 _25889 _25891 _25890 _25887 _25892) = (term312 _25888 _25889 _25890 _25887 _25891 _25892).
Proof. exact (@lem1679112 (term247 _25888 _25889 _25891 _25890 _25892 _25887) (term52 _25891 _25892) (term282 _25892)). Qed.
Lemma lem1679131 (_25888 : real) (_25889 : real) (_25890 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term308 _25888 _25889 _25891 _25890 _25892 _25887) = (term312 _25888 _25889 _25890 _25887 _25891 _25892).
Proof. exact (TRANS (@lem1679108 _25888 _25889 _25891 _25890 _25887 _25892) (@lem1679113 _25888 _25889 _25890 _25887 _25891 _25892)). Qed.
Lemma lem1679132 (_25888 : real) (_25889 : real) (_25890 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term284 _25888 _25889 _25891 _25890 _25892 _25887) = (term312 _25888 _25889 _25890 _25887 _25891 _25892).
Proof. exact (TRANS (@lem1679084 _25888 _25889 _25891 _25890 _25892 _25887) (@lem1679131 _25888 _25889 _25890 _25887 _25891 _25892)). Qed.
Lemma lem1679133 (_25891 : real) : (term233 _25891) = (term233 _25891).
Proof. exact (eq_refl (term233 _25891)). Qed.
Lemma lem1679134 (_25888 : real) (_25889 : real) (_25890 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term285 _25888 _25889 _25891 _25890 _25892 _25887) = (term313 _25888 _25889 _25890 _25887 _25891 _25892).
Proof. exact (MK_COMB (@lem1679133 _25891) (@lem1679132 _25888 _25889 _25890 _25887 _25891 _25892)). Qed.
Lemma lem1679138 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1679139 (_25888 : real) (_25889 : real) (_25890 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term313 _25888 _25889 _25890 _25887 _25891 _25892) = (term314 _25888 _25889 _25890 _25887 _25891 _25892).
Proof. exact (@lem1679138 (term247 _25888 _25889 _25891 _25890 _25892 _25887) (term282 _25891) (term315 _25891 _25892)). Qed.
Lemma lem1679153 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1679154 (_25891 : real) (_25892 : real) : (term316 _25891 _25892) = (term317 _25891 _25892).
Proof. exact (@lem1679153 (term52 _25891 _25892) (term282 _25891) (term282 _25892)). Qed.
Lemma lem1679172 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term318 _25888 _25889 _25891 _25890 _25892 _25887) = (term318 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (eq_refl (term318 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1679173 (_25888 : real) (_25889 : real) (_25890 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term314 _25888 _25889 _25890 _25887 _25891 _25892) = (term319 _25888 _25889 _25890 _25887 _25891 _25892).
Proof. exact (MK_COMB (@lem1679172 _25888 _25889 _25891 _25890 _25892 _25887) (@lem1679154 _25891 _25892)). Qed.
Lemma lem1679184 (_25888 : real) (_25889 : real) (_25890 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term313 _25888 _25889 _25890 _25887 _25891 _25892) = (term319 _25888 _25889 _25890 _25887 _25891 _25892).
Proof. exact (TRANS (@lem1679139 _25888 _25889 _25890 _25887 _25891 _25892) (@lem1679173 _25888 _25889 _25890 _25887 _25891 _25892)). Qed.
Lemma lem1679185 (_25888 : real) (_25889 : real) (_25890 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term285 _25888 _25889 _25891 _25890 _25892 _25887) = (term319 _25888 _25889 _25890 _25887 _25891 _25892).
Proof. exact (TRANS (@lem1679134 _25888 _25889 _25890 _25887 _25891 _25892) (@lem1679184 _25888 _25889 _25890 _25887 _25891 _25892)). Qed.
Lemma lem1679186 (_25889 : real) (_25887 : real) : (term238 _25889 _25887) = (term238 _25889 _25887).
Proof. exact (eq_refl (term238 _25889 _25887)). Qed.
Lemma lem1679187 (_25888 : real) (_25889 : real) (_25890 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term286 _25888 _25889 _25891 _25890 _25892 _25887) = (term320 _25888 _25889 _25890 _25887 _25891 _25892).
Proof. exact (MK_COMB (@lem1679186 _25889 _25887) (@lem1679185 _25888 _25889 _25890 _25887 _25891 _25892)). Qed.
Lemma lem1679191 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1679192 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term320 _25888 _25889 _25890 _25887 _25891 _25892) = (term321 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (@lem1679191 (term247 _25888 _25889 _25891 _25890 _25892 _25887) (term277 _25889 _25887) (term317 _25891 _25892)). Qed.
Lemma lem1679206 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1679207 (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term322 _25889 _25887 _25891 _25892) = (term323 _25889 _25887 _25891 _25892).
Proof. exact (@lem1679206 (term52 _25891 _25892) (term277 _25889 _25887) (term324 _25891 _25892)). Qed.
Lemma lem1679235 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term318 _25888 _25889 _25891 _25890 _25892 _25887) = (term318 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (eq_refl (term318 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1679236 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term321 _25888 _25890 _25889 _25887 _25891 _25892) = (term325 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (MK_COMB (@lem1679235 _25888 _25889 _25891 _25890 _25892 _25887) (@lem1679207 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679247 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term320 _25888 _25889 _25890 _25887 _25891 _25892) = (term325 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (TRANS (@lem1679192 _25888 _25890 _25889 _25887 _25891 _25892) (@lem1679236 _25888 _25890 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679248 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term286 _25888 _25889 _25891 _25890 _25892 _25887) = (term325 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (TRANS (@lem1679187 _25888 _25889 _25890 _25887 _25891 _25892) (@lem1679247 _25888 _25890 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679249 (_25888 : real) (_25890 : real) : (term238 _25888 _25890) = (term238 _25888 _25890).
Proof. exact (eq_refl (term238 _25888 _25890)). Qed.
Lemma lem1679250 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term287 _25888 _25889 _25891 _25890 _25892 _25887) = (term326 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (MK_COMB (@lem1679249 _25888 _25890) (@lem1679248 _25888 _25890 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679254 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1679255 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term326 _25888 _25890 _25889 _25887 _25891 _25892) = (term327 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (@lem1679254 (term247 _25888 _25889 _25891 _25890 _25892 _25887) (term277 _25888 _25890) (term323 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679269 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1679270 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term328 _25888 _25890 _25889 _25887 _25891 _25892) = (term329 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (@lem1679269 (term52 _25891 _25892) (term277 _25888 _25890) (term330 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679308 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term318 _25888 _25889 _25891 _25890 _25892 _25887) = (term318 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (eq_refl (term318 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1679309 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term327 _25888 _25890 _25889 _25887 _25891 _25892) = (term331 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (MK_COMB (@lem1679308 _25888 _25889 _25891 _25890 _25892 _25887) (@lem1679270 _25888 _25890 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679320 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term326 _25888 _25890 _25889 _25887 _25891 _25892) = (term331 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (TRANS (@lem1679255 _25888 _25890 _25889 _25887 _25891 _25892) (@lem1679309 _25888 _25890 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679321 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term287 _25888 _25889 _25891 _25890 _25892 _25887) = (term331 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (TRANS (@lem1679250 _25888 _25890 _25889 _25887 _25891 _25892) (@lem1679320 _25888 _25890 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679322 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1679323 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term332 _25888 _25889 _25891 _25890 _25892 _25887) = (term333 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (MK_COMB (@lem1679322) (@lem1679321 _25888 _25890 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679367 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1679368 (_25891 : real) (_25892 : real) : (term231 _25891 _25892) = (term315 _25891 _25892).
Proof. exact (@lem1679367 (term52 _25891 _25892) (term282 _25892)). Qed.
Lemma lem1679376 (_25891 : real) : (term233 _25891) = (term233 _25891).
Proof. exact (eq_refl (term233 _25891)). Qed.
Lemma lem1679377 (_25891 : real) (_25892 : real) : (term235 _25891 _25892) = (term316 _25891 _25892).
Proof. exact (MK_COMB (@lem1679376 _25891) (@lem1679368 _25891 _25892)). Qed.
Lemma lem1679381 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1679382 (_25891 : real) (_25892 : real) : (term316 _25891 _25892) = (term317 _25891 _25892).
Proof. exact (@lem1679381 (term52 _25891 _25892) (term282 _25891) (term282 _25892)). Qed.
Lemma lem1679400 (_25891 : real) (_25892 : real) : (term235 _25891 _25892) = (term317 _25891 _25892).
Proof. exact (TRANS (@lem1679377 _25891 _25892) (@lem1679382 _25891 _25892)). Qed.
Lemma lem1679401 (_25889 : real) (_25887 : real) : (term238 _25889 _25887) = (term238 _25889 _25887).
Proof. exact (eq_refl (term238 _25889 _25887)). Qed.
Lemma lem1679402 (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term240 _25889 _25887 _25891 _25892) = (term322 _25889 _25887 _25891 _25892).
Proof. exact (MK_COMB (@lem1679401 _25889 _25887) (@lem1679400 _25891 _25892)). Qed.
Lemma lem1679406 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1679407 (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term322 _25889 _25887 _25891 _25892) = (term323 _25889 _25887 _25891 _25892).
Proof. exact (@lem1679406 (term52 _25891 _25892) (term277 _25889 _25887) (term324 _25891 _25892)). Qed.
Lemma lem1679435 (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term240 _25889 _25887 _25891 _25892) = (term323 _25889 _25887 _25891 _25892).
Proof. exact (TRANS (@lem1679402 _25889 _25887 _25891 _25892) (@lem1679407 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679436 (_25888 : real) (_25890 : real) : (term238 _25888 _25890) = (term238 _25888 _25890).
Proof. exact (eq_refl (term238 _25888 _25890)). Qed.
Lemma lem1679437 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term244 _25888 _25890 _25889 _25887 _25891 _25892) = (term328 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (MK_COMB (@lem1679436 _25888 _25890) (@lem1679435 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679441 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1679442 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term328 _25888 _25890 _25889 _25887 _25891 _25892) = (term329 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (@lem1679441 (term52 _25891 _25892) (term277 _25888 _25890) (term330 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679480 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term244 _25888 _25890 _25889 _25887 _25891 _25892) = (term329 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (TRANS (@lem1679437 _25888 _25890 _25889 _25887 _25891 _25892) (@lem1679442 _25888 _25890 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679481 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term318 _25888 _25889 _25891 _25890 _25892 _25887) = (term318 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (eq_refl (term318 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1679482 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term334 _25888 _25890 _25889 _25887 _25891 _25892) = (term331 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (MK_COMB (@lem1679481 _25888 _25889 _25891 _25890 _25892 _25887) (@lem1679480 _25888 _25890 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679493 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : ((term287 _25888 _25889 _25891 _25890 _25892 _25887) = (term334 _25888 _25890 _25889 _25887 _25891 _25892)) = ((term331 _25888 _25890 _25889 _25887 _25891 _25892) = (term331 _25888 _25890 _25889 _25887 _25891 _25892)).
Proof. exact (MK_COMB (@lem1679323 _25888 _25890 _25889 _25887 _25891 _25892) (@lem1679482 _25888 _25890 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679495 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1679496 (x : Prop) : (x = x) = True.
Proof. exact (@lem1679495 Prop x). Qed.
Lemma lem1679497 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : ((term331 _25888 _25890 _25889 _25887 _25891 _25892) = (term331 _25888 _25890 _25889 _25887 _25891 _25892)) = True.
Proof. exact (@lem1679496 (term331 _25888 _25890 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679498 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : ((term287 _25888 _25889 _25891 _25890 _25892 _25887) = (term334 _25888 _25890 _25889 _25887 _25891 _25892)) = True.
Proof. exact (TRANS (@lem1679493 _25888 _25890 _25889 _25887 _25891 _25892) (@lem1679497 _25888 _25890 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679499 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : True = ((term287 _25888 _25889 _25891 _25890 _25892 _25887) = (term334 _25888 _25890 _25889 _25887 _25891 _25892)).
Proof. exact (SYM (@lem1679498 _25888 _25890 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679500 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term287 _25888 _25889 _25891 _25890 _25892 _25887) = (term334 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (EQ_MP (@lem1679499 _25888 _25890 _25889 _25887 _25891 _25892) (@lem0)). Qed.
Lemma lem1679501 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) (h1 : term119) : term334 _25888 _25890 _25889 _25887 _25891 _25892.
Proof. exact (EQ_MP (@lem1679500 _25888 _25890 _25889 _25887 _25891 _25892) (@lem1678847 _25888 _25889 _25891 _25890 _25892 _25887 h1)). Qed.
Lemma lem1679503 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1679504 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term334 _25888 _25890 _25889 _25887 _25891 _25892) = (term335 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (@lem1679503 (term244 _25888 _25890 _25889 _25887 _25891 _25892) (term247 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1679506 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1679507 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term336 _25888 _25890 _25889 _25887 _25891 _25892) = (term337 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (@lem1679506 (term277 _25888 _25890) (term240 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679509 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1679510 (_25888 : real) (_25890 : real) : (term338 _25888 _25890) = (real_le _25888 _25890).
Proof. exact (@lem1679509 (real_le _25888 _25890)). Qed.
Lemma lem1679511 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1679512 (_25888 : real) (_25890 : real) : (term339 _25888 _25890) = (term340 _25888 _25890).
Proof. exact (MK_COMB (@lem1679511) (@lem1679510 _25888 _25890)). Qed.
Lemma lem1679514 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1679515 (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term341 _25889 _25887 _25891 _25892) = (term342 _25889 _25887 _25891 _25892).
Proof. exact (@lem1679514 (term277 _25889 _25887) (term235 _25891 _25892)). Qed.
Lemma lem1679517 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1679518 (_25889 : real) (_25887 : real) : (term338 _25889 _25887) = (real_le _25889 _25887).
Proof. exact (@lem1679517 (real_le _25889 _25887)). Qed.
Lemma lem1679519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1679520 (_25889 : real) (_25887 : real) : (term339 _25889 _25887) = (term340 _25889 _25887).
Proof. exact (MK_COMB (@lem1679519) (@lem1679518 _25889 _25887)). Qed.
Lemma lem1679522 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1679523 (_25891 : real) (_25892 : real) : (term343 _25891 _25892) = (term344 _25891 _25892).
Proof. exact (@lem1679522 (term282 _25891) (term231 _25891 _25892)). Qed.
Lemma lem1679525 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1679526 (_25891 : real) : (term345 _25891) = (term232 _25891).
Proof. exact (@lem1679525 (term232 _25891)). Qed.
Lemma lem1679527 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1679528 (_25891 : real) : (term346 _25891) = (term347 _25891).
Proof. exact (MK_COMB (@lem1679527) (@lem1679526 _25891)). Qed.
Lemma lem1679530 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1679531 (_25891 : real) (_25892 : real) : (term348 _25891 _25892) = (term349 _25891 _25892).
Proof. exact (@lem1679530 (term282 _25892) (term52 _25891 _25892)). Qed.
Lemma lem1679533 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1679534 (_25892 : real) : (term345 _25892) = (term232 _25892).
Proof. exact (@lem1679533 (term232 _25892)). Qed.
Lemma lem1679535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1679536 (_25892 : real) : (term346 _25892) = (term347 _25892).
Proof. exact (MK_COMB (@lem1679535) (@lem1679534 _25892)). Qed.
Lemma lem1679538 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1679539 (_25891 : real) (_25892 : real) : (term303 _25891 _25892) = ((real_add _25891 _25892) = term39).
Proof. exact (@lem1679538 ((real_add _25891 _25892) = term39)). Qed.
Lemma lem1679540 (_25891 : real) (_25892 : real) : (term349 _25891 _25892) = (term237 _25891 _25892).
Proof. exact (MK_COMB (@lem1679536 _25892) (@lem1679539 _25891 _25892)). Qed.
Lemma lem1679541 (_25891 : real) (_25892 : real) : (term348 _25891 _25892) = (term237 _25891 _25892).
Proof. exact (TRANS (@lem1679531 _25891 _25892) (@lem1679540 _25891 _25892)). Qed.
Lemma lem1679542 (_25891 : real) (_25892 : real) : (term344 _25891 _25892) = (term242 _25891 _25892).
Proof. exact (MK_COMB (@lem1679528 _25891) (@lem1679541 _25891 _25892)). Qed.
Lemma lem1679543 (_25891 : real) (_25892 : real) : (term343 _25891 _25892) = (term242 _25891 _25892).
Proof. exact (TRANS (@lem1679523 _25891 _25892) (@lem1679542 _25891 _25892)). Qed.
Lemma lem1679544 (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term342 _25889 _25887 _25891 _25892) = (term246 _25889 _25887 _25891 _25892).
Proof. exact (MK_COMB (@lem1679520 _25889 _25887) (@lem1679543 _25891 _25892)). Qed.
Lemma lem1679545 (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term341 _25889 _25887 _25891 _25892) = (term246 _25889 _25887 _25891 _25892).
Proof. exact (TRANS (@lem1679515 _25889 _25887 _25891 _25892) (@lem1679544 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679546 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term337 _25888 _25890 _25889 _25887 _25891 _25892) = (term252 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (MK_COMB (@lem1679512 _25888 _25890) (@lem1679545 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679547 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term336 _25888 _25890 _25889 _25887 _25891 _25892) = (term252 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (TRANS (@lem1679507 _25888 _25890 _25889 _25887 _25891 _25892) (@lem1679546 _25888 _25890 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679548 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1679549 (_25888 : real) (_25890 : real) (_25889 : real) (_25887 : real) (_25891 : real) (_25892 : real) : (term350 _25888 _25890 _25889 _25887 _25891 _25892) = (term351 _25888 _25890 _25889 _25887 _25891 _25892).
Proof. exact (MK_COMB (@lem1679548) (@lem1679547 _25888 _25890 _25889 _25887 _25891 _25892)). Qed.
Lemma lem1679550 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term247 _25888 _25889 _25891 _25890 _25892 _25887) = (term247 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (eq_refl (term247 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1679551 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term335 _25888 _25889 _25891 _25890 _25892 _25887) = (term137 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (MK_COMB (@lem1679549 _25888 _25890 _25889 _25887 _25891 _25892) (@lem1679550 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1679552 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) : (term334 _25888 _25890 _25889 _25887 _25891 _25892) = (term137 _25888 _25889 _25891 _25890 _25892 _25887).
Proof. exact (TRANS (@lem1679504 _25888 _25889 _25891 _25890 _25892 _25887) (@lem1679551 _25888 _25889 _25891 _25890 _25892 _25887)). Qed.
Lemma lem1679554 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term237 u v.
Proof. exact (conj (@lem1679040 u x v y a h1) (@lem1679047 u x v y a h1)). Qed.
Lemma lem1679555 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term242 u v.
Proof. exact (conj (@lem1679033 u x v y a h1) (@lem1679554 u x v y a h1)). Qed.
Lemma lem1679556 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term246 y a u v.
Proof. exact (conj (@lem1679026 u x v y a h1) (@lem1679555 u x v y a h1)). Qed.
Lemma lem1679557 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term164 x y a u v.
Proof. exact (conj (@lem1679019 u x v y a h1) (@lem1679556 u x v y a h1)). Qed.
Lemma lem1679559 (_25888 : real) (_25889 : real) (_25891 : real) (_25890 : real) (_25892 : real) (_25887 : real) (h1 : term119) : term137 _25888 _25889 _25891 _25890 _25892 _25887.
Proof. exact (EQ_MP (@lem1679552 _25888 _25889 _25891 _25890 _25892 _25887) (@lem1679501 _25888 _25890 _25889 _25887 _25891 _25892 h1)). Qed.
Lemma lem1679560 (x : real) (y : real) (u : real) (v : real) (a : real) (h1 : term119) : term352 x y u v a.
Proof. exact (@lem1679559 x y u a v a h1). Qed.
Lemma lem1679563 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term163 u x v y a) : term353 x y u v a.
Proof. exact (@lem1679560 x y u v a h1 (@lem1679557 u x v y a h2)). Qed.
Lemma lem1679564 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term163 u x v y a) : term354 x y u v a.
Proof. exact (fun h0 : term355 x y u v a => @lem1679563 u x v y a h1 h2). Qed.
Lemma lem1679566 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1679567 (x : real) (y : real) (u : real) (v : real) (a : real) : (term354 x y u v a) = (term353 x y u v a).
Proof. exact (@lem1679566 (term353 x y u v a)). Qed.
Lemma lem1679568 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term163 u x v y a) : term353 x y u v a.
Proof. exact (EQ_MP (@lem1679567 x y u v a) (@lem1679564 u x v y a h1 h2)). Qed.
Lemma lem1679586 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1679587 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : (term293 _25895 _25896 _25893 _25894) = (term356 _25895 _25896 _25893 _25894).
Proof. exact (@lem1679586 (real_le _25895 _25896) (term57 _25894 _25896) (term277 _25893 _25894)). Qed.
Lemma lem1679605 (_25893 : real) (_25895 : real) : (term58 _25893 _25895) = (term58 _25893 _25895).
Proof. exact (eq_refl (term58 _25893 _25895)). Qed.
Lemma lem1679606 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : (term295 _25895 _25896 _25893 _25894) = (term357 _25895 _25896 _25893 _25894).
Proof. exact (MK_COMB (@lem1679605 _25893 _25895) (@lem1679587 _25895 _25896 _25893 _25894)). Qed.
Lemma lem1679610 (q : Prop) (p : Prop) (r : Prop) : (term60 p q r) = (term60 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1679611 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : (term357 _25895 _25896 _25893 _25894) = (term358 _25895 _25896 _25893 _25894).
Proof. exact (@lem1679610 (real_le _25895 _25896) (term57 _25893 _25895) (term359 _25896 _25893 _25894)). Qed.
Lemma lem1679641 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : (term295 _25895 _25896 _25893 _25894) = (term358 _25895 _25896 _25893 _25894).
Proof. exact (TRANS (@lem1679606 _25895 _25896 _25893 _25894) (@lem1679611 _25895 _25896 _25893 _25894)). Qed.
Lemma lem1679642 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1679643 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : (term360 _25895 _25896 _25893 _25894) = (term361 _25895 _25896 _25893 _25894).
Proof. exact (MK_COMB (@lem1679642) (@lem1679641 _25895 _25896 _25893 _25894)). Qed.
Lemma lem1679673 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : (term358 _25895 _25896 _25893 _25894) = (term358 _25895 _25896 _25893 _25894).
Proof. exact (eq_refl (term358 _25895 _25896 _25893 _25894)). Qed.
Lemma lem1679674 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : ((term295 _25895 _25896 _25893 _25894) = (term358 _25895 _25896 _25893 _25894)) = ((term358 _25895 _25896 _25893 _25894) = (term358 _25895 _25896 _25893 _25894)).
Proof. exact (MK_COMB (@lem1679643 _25895 _25896 _25893 _25894) (@lem1679673 _25895 _25896 _25893 _25894)). Qed.
Lemma lem1679676 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1679677 (x : Prop) : (x = x) = True.
Proof. exact (@lem1679676 Prop x). Qed.
Lemma lem1679678 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : ((term358 _25895 _25896 _25893 _25894) = (term358 _25895 _25896 _25893 _25894)) = True.
Proof. exact (@lem1679677 (term358 _25895 _25896 _25893 _25894)). Qed.
Lemma lem1679679 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : ((term295 _25895 _25896 _25893 _25894) = (term358 _25895 _25896 _25893 _25894)) = True.
Proof. exact (TRANS (@lem1679674 _25895 _25896 _25893 _25894) (@lem1679678 _25895 _25896 _25893 _25894)). Qed.
Lemma lem1679680 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : True = ((term295 _25895 _25896 _25893 _25894) = (term358 _25895 _25896 _25893 _25894)).
Proof. exact (SYM (@lem1679679 _25895 _25896 _25893 _25894)). Qed.
Lemma lem1679681 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : (term295 _25895 _25896 _25893 _25894) = (term358 _25895 _25896 _25893 _25894).
Proof. exact (EQ_MP (@lem1679680 _25895 _25896 _25893 _25894) (@lem0)). Qed.
Lemma lem1679682 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : term358 _25895 _25896 _25893 _25894.
Proof. exact (EQ_MP (@lem1679681 _25895 _25896 _25893 _25894) (@lem1678878 _25895 _25896 _25893 _25894)). Qed.
Lemma lem1679684 (b : Prop) (a : Prop) : (a \/ b) = (term64 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1679685 (_25893 : real) (_25894 : real) (_25895 : real) (_25896 : real) : (term358 _25895 _25896 _25893 _25894) = (term362 _25893 _25894 _25895 _25896).
Proof. exact (@lem1679684 (term363 _25895 _25896 _25893 _25894) (real_le _25895 _25896)). Qed.
Lemma lem1679687 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1679688 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : (term364 _25895 _25896 _25893 _25894) = (term365 _25895 _25896 _25893 _25894).
Proof. exact (@lem1679687 (term57 _25893 _25895) (term359 _25896 _25893 _25894)). Qed.
Lemma lem1679690 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1679691 (_25893 : real) (_25895 : real) : (term72 _25893 _25895) = (_25893 = _25895).
Proof. exact (@lem1679690 (_25893 = _25895)). Qed.
Lemma lem1679692 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1679693 (_25893 : real) (_25895 : real) : (term73 _25893 _25895) = (term74 _25893 _25895).
Proof. exact (MK_COMB (@lem1679692) (@lem1679691 _25893 _25895)). Qed.
Lemma lem1679695 (a : Prop) (b : Prop) : (term67 a b) = (term68 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1679696 (_25896 : real) (_25893 : real) (_25894 : real) : (term366 _25896 _25893 _25894) = (term367 _25896 _25893 _25894).
Proof. exact (@lem1679695 (term57 _25894 _25896) (term277 _25893 _25894)). Qed.
Lemma lem1679698 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1679699 (_25894 : real) (_25896 : real) : (term72 _25894 _25896) = (_25894 = _25896).
Proof. exact (@lem1679698 (_25894 = _25896)). Qed.
Lemma lem1679700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1679701 (_25894 : real) (_25896 : real) : (term73 _25894 _25896) = (term74 _25894 _25896).
Proof. exact (MK_COMB (@lem1679700) (@lem1679699 _25894 _25896)). Qed.
Lemma lem1679703 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1679704 (_25893 : real) (_25894 : real) : (term338 _25893 _25894) = (real_le _25893 _25894).
Proof. exact (@lem1679703 (real_le _25893 _25894)). Qed.
Lemma lem1679705 (_25896 : real) (_25893 : real) (_25894 : real) : (term367 _25896 _25893 _25894) = (term368 _25896 _25893 _25894).
Proof. exact (MK_COMB (@lem1679701 _25894 _25896) (@lem1679704 _25893 _25894)). Qed.
Lemma lem1679706 (_25896 : real) (_25893 : real) (_25894 : real) : (term366 _25896 _25893 _25894) = (term368 _25896 _25893 _25894).
Proof. exact (TRANS (@lem1679696 _25896 _25893 _25894) (@lem1679705 _25896 _25893 _25894)). Qed.
Lemma lem1679707 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : (term365 _25895 _25896 _25893 _25894) = (term369 _25895 _25896 _25893 _25894).
Proof. exact (MK_COMB (@lem1679693 _25893 _25895) (@lem1679706 _25896 _25893 _25894)). Qed.
Lemma lem1679708 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : (term364 _25895 _25896 _25893 _25894) = (term369 _25895 _25896 _25893 _25894).
Proof. exact (TRANS (@lem1679688 _25895 _25896 _25893 _25894) (@lem1679707 _25895 _25896 _25893 _25894)). Qed.
Lemma lem1679709 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1679710 (_25895 : real) (_25896 : real) (_25893 : real) (_25894 : real) : (term370 _25895 _25896 _25893 _25894) = (term371 _25895 _25896 _25893 _25894).
Proof. exact (MK_COMB (@lem1679709) (@lem1679708 _25895 _25896 _25893 _25894)). Qed.
Lemma lem1679711 (_25895 : real) (_25896 : real) : (real_le _25895 _25896) = (real_le _25895 _25896).
Proof. exact (eq_refl (real_le _25895 _25896)). Qed.
Lemma lem1679712 (_25893 : real) (_25894 : real) (_25895 : real) (_25896 : real) : (term362 _25893 _25894 _25895 _25896) = (term372 _25893 _25894 _25895 _25896).
Proof. exact (MK_COMB (@lem1679710 _25895 _25896 _25893 _25894) (@lem1679711 _25895 _25896)). Qed.
Lemma lem1679713 (_25893 : real) (_25894 : real) (_25895 : real) (_25896 : real) : (term358 _25895 _25896 _25893 _25894) = (term372 _25893 _25894 _25895 _25896).
Proof. exact (TRANS (@lem1679685 _25893 _25894 _25895 _25896) (@lem1679712 _25893 _25894 _25895 _25896)). Qed.
Lemma lem1679715 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : term373 x y u v a.
Proof. exact (conj (@lem1679012 u x v y a h2 h3) (@lem1679568 u x v y a h1 h3)). Qed.
Lemma lem1679716 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : term374 x y u v a.
Proof. exact (conj (@lem1678944 u x v y) (@lem1679715 u x v y a h1 h2 h3)). Qed.
Lemma lem1679718 (_25893 : real) (_25894 : real) (_25895 : real) (_25896 : real) : term372 _25893 _25894 _25895 _25896.
Proof. exact (EQ_MP (@lem1679713 _25893 _25894 _25895 _25896) (@lem1679682 _25895 _25896 _25893 _25894)). Qed.
Lemma lem1679719 (u : real) (x : real) (v : real) (y : real) (a : real) : term375 u x v y a.
Proof. exact (@lem1679718 (term296 u x v y) (term31 u v a) (term296 u x v y) a). Qed.
Lemma lem1679722 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : term165 u x v y a.
Proof. exact (@lem1679719 u x v y a (@lem1679716 u x v y a h1 h2 h3)). Qed.
Lemma lem1679723 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : term376 u x v y a.
Proof. exact (fun h0 : term288 u x v y a => @lem1679722 u x v y a h1 h2 h3). Qed.
Lemma lem1679725 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1679726 (u : real) (x : real) (v : real) (y : real) (a : real) : (term376 u x v y a) = (term165 u x v y a).
Proof. exact (@lem1679725 (term165 u x v y a)). Qed.
Lemma lem1679727 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : term165 u x v y a.
Proof. exact (EQ_MP (@lem1679726 u x v y a) (@lem1679723 u x v y a h1 h2 h3)). Qed.
Lemma lem1679730 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1679732 (u : real) (x : real) (v : real) (y : real) (a : real) : (term288 u x v y a) = (term377 u x v y a).
Proof. exact (@lem1679730 (term165 u x v y a)). Qed.
Lemma lem1679735 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term163 u x v y a) : term377 u x v y a.
Proof. exact (EQ_MP (@lem1679732 u x v y a) (@lem1678849 u x v y a h1)). Qed.
Lemma lem1679738 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : False.
Proof. exact (@lem1679735 u x v y a h3 (@lem1679727 u x v y a h1 h2 h3)). Qed.
Lemma lem1679739 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : term109.
Proof. exact (fun h0 : ~ False => @lem1679738 u x v y a h1 h2 h3). Qed.
Lemma lem1679741 (p : Prop) : (term53 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1679742 : term109 = False.
Proof. exact (@lem1679741 False). Qed.
Lemma lem1679743 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : False.
Proof. exact (EQ_MP (@lem1679742) (@lem1679739 u x v y a h1 h2 h3)). Qed.
Lemma lem1679744 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : (term163 u x v y a) = False.
Proof. exact (prop_ext (fun h4 : term163 u x v y a => @lem1679743 u x v y a h1 h2 h3) (fun h4 : False => @lem1678654 u x v y a h3)). Qed.
Lemma lem1679745 (u : real) (x : real) (v : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term163 u x v y a) : False.
Proof. exact (EQ_MP (@lem1679744 u x v y a h1 h2 h3) (@lem1678654 u x v y a h3)). Qed.
Lemma lem1679746 (u : real) (x : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term174 u x y a) : False.
Proof. exact (ex_elim (@lem1678412 u x y a h3) (fun v : real => fun h0 : term173 u x y a v => @lem1679745 u x v y a h1 h2 h0)). Qed.
Lemma lem1679747 (x : real) (y : real) (a : real) (h1 : term119) (h2 : term122) (h3 : term181 x y a) : False.
Proof. exact (ex_elim (@lem1678411 x y a h3) (fun u : real => fun h0 : term180 x y a u => @lem1679746 u x y a h1 h2 h0)). Qed.
Lemma lem1679748 (x : real) (y : real) (h1 : term119) (h2 : term122) (h3 : term188 x y) : False.
Proof. exact (ex_elim (@lem1678410 x y h3) (fun a : real => fun h0 : term187 x y a => @lem1679747 x y a h1 h2 h0)). Qed.
Lemma lem1679749 (x : real) (h1 : term119) (h2 : term122) (h3 : term195 x) : False.
Proof. exact (ex_elim (@lem1678409 x h3) (fun y : real => fun h0 : term194 x y => @lem1679748 x y h1 h2 h0)). Qed.
Lemma lem1679750 (h1 : term119) (h2 : term122) (h3 : term125) : False.
Proof. exact (ex_elim (@lem1678176 h3) (fun x : real => fun h0 : term200 x => @lem1679749 x h1 h2 h0)). Qed.
Lemma lem1679751 (h1 : term122) (h2 : term125) : term130.
Proof. exact (fun h0 : term119 => @lem1679750 h0 h1 h2). Qed.
Lemma lem1679752 : term130 = term131.
Proof. exact (@lem69 term119). Qed.
Lemma lem1679753 (h1 : term122) (h2 : term125) : term131.
Proof. exact (EQ_MP (@lem1679752) (@lem1679751 h1 h2)). Qed.
Lemma lem1679754 (h1 : term125) : term134.
Proof. exact (fun h0 : term122 => @lem1679753 h0 h1). Qed.
Lemma lem1679755 : term136.
Proof. exact (fun h0 : term125 => @lem1679754 h0). Qed.
Lemma lem1679756 : term126.
Proof. exact (EQ_MP (@lem1678031) (@lem1679755)). Qed.
Lemma lem1679758 : term126.
Proof. exact (@lem1677721 (@lem1679756)). Qed.
Lemma lem1679759 (h1 : term125) : term133.
Proof. exact (@lem1679758 (@lem1677706 h1)). Qed.
Lemma lem1679760 (h1 : term125) : term130.
Proof. exact (@lem1679759 h1 (@lem1677701)). Qed.
Lemma lem1679761 (h1 : term125) : False.
Proof. exact (@lem1679760 h1 (@lem1677698)). Qed.
Lemma lem1679762 (h1 : term125) : term125 = False.
Proof. exact (prop_ext (fun h2 : term125 => @lem1679761 h1) (fun h2 : False => @lem1677706 h1)). Qed.
Lemma lem1679763 (h1 : term125) : False.
Proof. exact (EQ_MP (@lem1679762 h1) (@lem1677706 h1)). Qed.
Lemma lem1679764 : term124.
Proof. exact (fun h0 : term125 => @lem1679763 h0). Qed.
Lemma lem1679765 : term123.
Proof. exact (EQ_MP (@lem1677705) (@lem1679764)). Qed.
