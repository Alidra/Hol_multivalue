Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MUL_LCM_GCD_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INT_MUL_GCD_LCM_spec.
Require Import INT_MUL_SYM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm18392_spec.
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
Require Import thm69_spec.
Lemma lem2811949 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem2811950 : term1 = term2.
Proof. exact (@lem2811949 term1). Qed.
Lemma lem2811951 : term2 = term1.
Proof. exact (SYM (@lem2811950)). Qed.
Lemma lem2811952 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2811955 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2811956 : term5.
Proof. exact (fun h0 : term4 => @lem2811955 h0). Qed.
Lemma lem2811957 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2811958 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem2811959 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2811957 h2 (@lem2811958 h1)). Qed.
Lemma lem2811960 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem2811959 h1 h0). Qed.
Lemma lem2811961 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem2811962 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem2811960 h1 (@lem2811961 h2)). Qed.
Lemma lem2811963 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem2811962 h0 h1). Qed.
Lemma lem2811964 : term7.
Proof. exact (fun h0 : term5 => @lem2811963 h0). Qed.
Lemma lem2811967 : term5.
Proof. exact (@lem2811964 (@lem2811956)). Qed.
Lemma lem2811989 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem2811990 : term8 = term9.
Proof. exact (@lem2811989 term10). Qed.
Lemma lem2811999 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem2812000 : term12 = term13.
Proof. exact (MK_COMB (@lem2811999) (@lem2811990)). Qed.
Lemma lem2812003 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem2812010 : term4 = term15.
Proof. exact (MK_COMB (@lem2812003) (@lem2812000)). Qed.
Lemma lem2812011 (y : int) (x : int) : ((int_mul x y) = (int_mul y x)) = ((int_mul x y) = (int_mul y x)).
Proof. exact (eq_refl ((int_mul x y) = (int_mul y x))). Qed.
Lemma lem2812012 (x : int) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : int => @lem2812011 y x)). Qed.
Lemma lem2812013 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812014 (x : int) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem2812013) (@lem2812012 x)). Qed.
Lemma lem2812015 : term18 = term18.
Proof. exact (fun_ext (fun x : int => @lem2812014 x)). Qed.
Lemma lem2812016 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812017 : term10 = term10.
Proof. exact (MK_COMB (@lem2812016) (@lem2812015)). Qed.
Lemma lem2812018 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2812019 : term9 = term9.
Proof. exact (MK_COMB (@lem2812018) (@lem2812017)). Qed.
Lemma lem2812020 (m : int) (n : int) : ((term19 m n) = (term20 m n)) = ((term19 m n) = (term20 m n)).
Proof. exact (eq_refl ((term19 m n) = (term20 m n))). Qed.
Lemma lem2812021 (m : int) : (term21 m) = (term21 m).
Proof. exact (fun_ext (fun n : int => @lem2812020 m n)). Qed.
Lemma lem2812022 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812023 (m : int) : (term22 m) = (term22 m).
Proof. exact (MK_COMB (@lem2812022) (@lem2812021 m)). Qed.
Lemma lem2812024 : term23 = term23.
Proof. exact (fun_ext (fun m : int => @lem2812023 m)). Qed.
Lemma lem2812025 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812026 : term24 = term24.
Proof. exact (MK_COMB (@lem2812025) (@lem2812024)). Qed.
Lemma lem2812027 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2812028 : term11 = term11.
Proof. exact (MK_COMB (@lem2812027) (@lem2812026)). Qed.
Lemma lem2812029 : term13 = term13.
Proof. exact (MK_COMB (@lem2812028) (@lem2812019)). Qed.
Lemma lem2812030 (m : int) (n : int) : ((term25 m n) = (term20 m n)) = ((term25 m n) = (term20 m n)).
Proof. exact (eq_refl ((term25 m n) = (term20 m n))). Qed.
Lemma lem2812031 (m : int) : (term26 m) = (term26 m).
Proof. exact (fun_ext (fun n : int => @lem2812030 m n)). Qed.
Lemma lem2812032 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812033 (m : int) : (term27 m) = (term27 m).
Proof. exact (MK_COMB (@lem2812032) (@lem2812031 m)). Qed.
Lemma lem2812034 : term28 = term28.
Proof. exact (fun_ext (fun m : int => @lem2812033 m)). Qed.
Lemma lem2812035 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812036 : term1 = term1.
Proof. exact (MK_COMB (@lem2812035) (@lem2812034)). Qed.
Lemma lem2812037 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2812038 : term3 = term3.
Proof. exact (MK_COMB (@lem2812037) (@lem2812036)). Qed.
Lemma lem2812039 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2812040 : term14 = term14.
Proof. exact (MK_COMB (@lem2812039) (@lem2812038)). Qed.
Lemma lem2812041 : term15 = term15.
Proof. exact (MK_COMB (@lem2812040) (@lem2812029)). Qed.
Lemma lem2812084 : term4 = term15.
Proof. exact (TRANS (@lem2812010) (@lem2812041)). Qed.
Lemma lem2812085 : term15 = term4.
Proof. exact (SYM (@lem2812084)). Qed.
Lemma lem2812086 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem2812087 (h1 : term24) : term24.
Proof. exact (h1). Qed.
Lemma lem2812088 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem2812090 (P : int -> Prop) : (term29 P) = (term30 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2812091 (m : int) : (term31 m) = (term32 m).
Proof. exact (@lem2812090 (term26 m)). Qed.
Lemma lem2812092 (m : int) (n : int) : (term33 m n) = ((term25 m n) = (term20 m n)).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem2812093 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2812095 (m : int) (n : int) : (term34 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem2812093) (@lem2812092 m n)). Qed.
Lemma lem2812096 (m : int) : (term36 m) = (term37 m).
Proof. exact (fun_ext (fun n : int => @lem2812095 m n)). Qed.
Lemma lem2812097 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2812098 (m : int) : (term32 m) = (term38 m).
Proof. exact (MK_COMB (@lem2812097) (@lem2812096 m)). Qed.
Lemma lem2812099 (m : int) : (term31 m) = (term38 m).
Proof. exact (TRANS (@lem2812091 m) (@lem2812098 m)). Qed.
Lemma lem2812100 (P : int -> Prop) : (term29 P) = (term30 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2812101 : term3 = term39.
Proof. exact (@lem2812100 term28). Qed.
Lemma lem2812102 (m : int) : (term40 m) = (term27 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem2812103 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2812104 (m : int) : (term41 m) = (term31 m).
Proof. exact (MK_COMB (@lem2812103) (@lem2812102 m)). Qed.
Lemma lem2812105 (m : int) : (term41 m) = (term38 m).
Proof. exact (TRANS (@lem2812104 m) (@lem2812099 m)). Qed.
Lemma lem2812106 : term42 = term43.
Proof. exact (fun_ext (fun m : int => @lem2812105 m)). Qed.
Lemma lem2812107 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2812108 : term39 = term44.
Proof. exact (MK_COMB (@lem2812107) (@lem2812106)). Qed.
Lemma lem2812121 : term3 = term44.
Proof. exact (TRANS (@lem2812101) (@lem2812108)). Qed.
Lemma lem2812122 (h1 : term3) : term44.
Proof. exact (EQ_MP (@lem2812121) (@lem2812086 h1)). Qed.
Lemma lem2812123 (m : int) (n : int) : ((term19 m n) = (term20 m n)) = ((term19 m n) = (term20 m n)).
Proof. exact (eq_refl ((term19 m n) = (term20 m n))). Qed.
Lemma lem2812124 (m : int) : (term21 m) = (term21 m).
Proof. exact (fun_ext (fun n : int => @lem2812123 m n)). Qed.
Lemma lem2812125 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812126 (m : int) : (term22 m) = (term22 m).
Proof. exact (MK_COMB (@lem2812125) (@lem2812124 m)). Qed.
Lemma lem2812127 : term23 = term23.
Proof. exact (fun_ext (fun m : int => @lem2812126 m)). Qed.
Lemma lem2812128 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812141 : term24 = term24.
Proof. exact (MK_COMB (@lem2812128) (@lem2812127)). Qed.
Lemma lem2812142 (h1 : term24) : term24.
Proof. exact (EQ_MP (@lem2812141) (@lem2812087 h1)). Qed.
Lemma lem2812143 (y : int) (x : int) : ((int_mul x y) = (int_mul y x)) = ((int_mul x y) = (int_mul y x)).
Proof. exact (eq_refl ((int_mul x y) = (int_mul y x))). Qed.
Lemma lem2812144 (x : int) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : int => @lem2812143 y x)). Qed.
Lemma lem2812145 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812146 (x : int) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem2812145) (@lem2812144 x)). Qed.
Lemma lem2812147 : term18 = term18.
Proof. exact (fun_ext (fun x : int => @lem2812146 x)). Qed.
Lemma lem2812148 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812161 : term10 = term10.
Proof. exact (MK_COMB (@lem2812148) (@lem2812147)). Qed.
Lemma lem2812162 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem2812161) (@lem2812088 h1)). Qed.
Lemma lem2812163 (m : int) (h1 : term38 m) : term38 m.
Proof. exact (h1). Qed.
Lemma lem2812191 (m : int) (n : int) : ((term19 m n) = (term20 m n)) = ((term19 m n) = (term20 m n)).
Proof. exact (eq_refl ((term19 m n) = (term20 m n))). Qed.
Lemma lem2812192 (m : int) : (term21 m) = (term21 m).
Proof. exact (fun_ext (fun n : int => @lem2812191 m n)). Qed.
Lemma lem2812193 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812194 (m : int) : (term22 m) = (term22 m).
Proof. exact (MK_COMB (@lem2812193) (@lem2812192 m)). Qed.
Lemma lem2812195 : term23 = term23.
Proof. exact (fun_ext (fun m : int => @lem2812194 m)). Qed.
Lemma lem2812196 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812197 : term24 = term24.
Proof. exact (MK_COMB (@lem2812196) (@lem2812195)). Qed.
Lemma lem2812198 (h1 : term24) : term24.
Proof. exact (EQ_MP (@lem2812197) (@lem2812142 h1)). Qed.
Lemma lem2812211 (y : int) (x : int) : ((int_mul x y) = (int_mul y x)) = ((int_mul x y) = (int_mul y x)).
Proof. exact (eq_refl ((int_mul x y) = (int_mul y x))). Qed.
Lemma lem2812212 (x : int) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : int => @lem2812211 y x)). Qed.
Lemma lem2812213 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812214 (x : int) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem2812213) (@lem2812212 x)). Qed.
Lemma lem2812215 : term18 = term18.
Proof. exact (fun_ext (fun x : int => @lem2812214 x)). Qed.
Lemma lem2812216 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812217 : term10 = term10.
Proof. exact (MK_COMB (@lem2812216) (@lem2812215)). Qed.
Lemma lem2812218 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem2812217) (@lem2812162 h1)). Qed.
Lemma lem2812248 (m : int) (n : int) (h1 : term35 m n) : term35 m n.
Proof. exact (h1). Qed.
Lemma lem2812250 (m : int) (n : int) : ((term19 m n) = (term20 m n)) = ((term19 m n) = (term20 m n)).
Proof. exact (eq_refl ((term19 m n) = (term20 m n))). Qed.
Lemma lem2812251 (m : int) : (term21 m) = (term21 m).
Proof. exact (fun_ext (fun n : int => @lem2812250 m n)). Qed.
Lemma lem2812252 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812253 (m : int) : (term22 m) = (term22 m).
Proof. exact (MK_COMB (@lem2812252) (@lem2812251 m)). Qed.
Lemma lem2812254 : term23 = term23.
Proof. exact (fun_ext (fun m : int => @lem2812253 m)). Qed.
Lemma lem2812255 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812257 : term24 = term24.
Proof. exact (MK_COMB (@lem2812255) (@lem2812254)). Qed.
Lemma lem2812258 (h1 : term24) : term24.
Proof. exact (EQ_MP (@lem2812257) (@lem2812198 h1)). Qed.
Lemma lem2812260 (y : int) (x : int) : ((int_mul x y) = (int_mul y x)) = ((int_mul x y) = (int_mul y x)).
Proof. exact (eq_refl ((int_mul x y) = (int_mul y x))). Qed.
Lemma lem2812261 (x : int) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : int => @lem2812260 y x)). Qed.
Lemma lem2812262 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812263 (x : int) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem2812262) (@lem2812261 x)). Qed.
Lemma lem2812264 : term18 = term18.
Proof. exact (fun_ext (fun x : int => @lem2812263 x)). Qed.
Lemma lem2812265 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2812267 : term10 = term10.
Proof. exact (MK_COMB (@lem2812265) (@lem2812264)). Qed.
Lemma lem2812268 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem2812267) (@lem2812218 h1)). Qed.
Lemma lem2812272 (m : int) (n : int) (h1 : term35 m n) : term35 m n.
Proof. exact (h1). Qed.
Lemma lem2812273 (_30967 : int) (h1 : term24) : term45 _30967.
Proof. exact (@lem2812258 h1 _30967). Qed.
Lemma lem2812274 (_30967 : int) : (term45 _30967) = (term22 _30967).
Proof. exact (eq_refl (term45 _30967)). Qed.
Lemma lem2812275 (_30967 : int) (h1 : term24) : term22 _30967.
Proof. exact (EQ_MP (@lem2812274 _30967) (@lem2812273 _30967 h1)). Qed.
Lemma lem2812276 (_30967 : int) (_30968 : int) (h1 : term24) : term46 _30967 _30968.
Proof. exact (@lem2812275 _30967 h1 _30968). Qed.
Lemma lem2812277 (_30967 : int) (_30968 : int) : (term46 _30967 _30968) = ((term19 _30967 _30968) = (term20 _30967 _30968)).
Proof. exact (eq_refl (term46 _30967 _30968)). Qed.
Lemma lem2812279 (_30969 : int) (h1 : term10) : term47 _30969.
Proof. exact (@lem2812268 h1 _30969). Qed.
Lemma lem2812280 (_30969 : int) : (term47 _30969) = (term17 _30969).
Proof. exact (eq_refl (term47 _30969)). Qed.
Lemma lem2812281 (_30969 : int) (h1 : term10) : term17 _30969.
Proof. exact (EQ_MP (@lem2812280 _30969) (@lem2812279 _30969 h1)). Qed.
Lemma lem2812282 (_30969 : int) (_30970 : int) (h1 : term10) : term48 _30969 _30970.
Proof. exact (@lem2812281 _30969 h1 _30970). Qed.
Lemma lem2812283 (_30970 : int) (_30969 : int) : (term48 _30969 _30970) = ((int_mul _30969 _30970) = (int_mul _30970 _30969)).
Proof. exact (eq_refl (term48 _30969 _30970)). Qed.
Lemma lem2812290 (m : int) (n : int) (h1 : term35 m n) : term35 m n.
Proof. exact (h1). Qed.
Lemma lem2812346 (x : int) (y : int) (z : int) : term49 x y z.
Proof. exact (@lem21385 int x y z). Qed.
Lemma lem2812350 (_30970 : int) (_30969 : int) (h1 : term10) : (int_mul _30969 _30970) = (int_mul _30970 _30969).
Proof. exact (EQ_MP (@lem2812283 _30970 _30969) (@lem2812282 _30969 _30970 h1)). Qed.
Lemma lem2812351 (m : int) (n : int) (h1 : term10) : (term19 m n) = (term25 m n).
Proof. exact (@lem2812350 (term50 m n) (term51 m n) h1). Qed.
Lemma lem2812352 (m : int) (n : int) (h1 : term10) : term52 m n.
Proof. exact (fun h0 : term53 m n => @lem2812351 m n h1). Qed.
Lemma lem2812354 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2812355 (m : int) (n : int) : (term52 m n) = ((term19 m n) = (term25 m n)).
Proof. exact (@lem2812354 ((term19 m n) = (term25 m n))). Qed.
Lemma lem2812356 (m : int) (n : int) (h1 : term10) : (term19 m n) = (term25 m n).
Proof. exact (EQ_MP (@lem2812355 m n) (@lem2812352 m n h1)). Qed.
Lemma lem2812358 (_30967 : int) (_30968 : int) (h1 : term24) : (term19 _30967 _30968) = (term20 _30967 _30968).
Proof. exact (EQ_MP (@lem2812277 _30967 _30968) (@lem2812276 _30967 _30968 h1)). Qed.
Lemma lem2812359 (m : int) (n : int) (h1 : term24) : (term19 m n) = (term20 m n).
Proof. exact (@lem2812358 m n h1). Qed.
Lemma lem2812360 (m : int) (n : int) (h1 : term24) : term55 m n.
Proof. exact (fun h0 : term56 m n => @lem2812359 m n h1). Qed.
Lemma lem2812362 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2812363 (m : int) (n : int) : (term55 m n) = ((term19 m n) = (term20 m n)).
Proof. exact (@lem2812362 ((term19 m n) = (term20 m n))). Qed.
Lemma lem2812364 (m : int) (n : int) (h1 : term24) : (term19 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem2812363 m n) (@lem2812360 m n h1)). Qed.
Lemma lem2812382 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem2812383 (y : int) (x : int) (z : int) : (term57 x y z) = (term58 y x z).
Proof. exact (@lem2812382 (y = z) (term59 x z)). Qed.
Lemma lem2812393 (x : int) (y : int) : (term60 x y) = (term60 x y).
Proof. exact (eq_refl (term60 x y)). Qed.
Lemma lem2812394 (y : int) (x : int) (z : int) : (term49 x y z) = (term61 y x z).
Proof. exact (MK_COMB (@lem2812393 x y) (@lem2812383 y x z)). Qed.
Lemma lem2812398 (q : Prop) (p : Prop) (r : Prop) : (term62 p q r) = (term62 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem2812399 (y : int) (x : int) (z : int) : (term61 y x z) = (term63 y x z).
Proof. exact (@lem2812398 (y = z) (term59 x y) (term59 x z)). Qed.
Lemma lem2812421 (y : int) (x : int) (z : int) : (term49 x y z) = (term63 y x z).
Proof. exact (TRANS (@lem2812394 y x z) (@lem2812399 y x z)). Qed.
Lemma lem2812422 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2812423 (y : int) (x : int) (z : int) : (term64 x y z) = (term65 y x z).
Proof. exact (MK_COMB (@lem2812422) (@lem2812421 y x z)). Qed.
Lemma lem2812445 (y : int) (x : int) (z : int) : (term63 y x z) = (term63 y x z).
Proof. exact (eq_refl (term63 y x z)). Qed.
Lemma lem2812446 (y : int) (x : int) (z : int) : ((term49 x y z) = (term63 y x z)) = ((term63 y x z) = (term63 y x z)).
Proof. exact (MK_COMB (@lem2812423 y x z) (@lem2812445 y x z)). Qed.
Lemma lem2812448 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem2812449 (x : Prop) : (x = x) = True.
Proof. exact (@lem2812448 Prop x). Qed.
Lemma lem2812450 (y : int) (x : int) (z : int) : ((term63 y x z) = (term63 y x z)) = True.
Proof. exact (@lem2812449 (term63 y x z)). Qed.
Lemma lem2812451 (y : int) (x : int) (z : int) : ((term49 x y z) = (term63 y x z)) = True.
Proof. exact (TRANS (@lem2812446 y x z) (@lem2812450 y x z)). Qed.
Lemma lem2812452 (y : int) (x : int) (z : int) : True = ((term49 x y z) = (term63 y x z)).
Proof. exact (SYM (@lem2812451 y x z)). Qed.
Lemma lem2812453 (y : int) (x : int) (z : int) : (term49 x y z) = (term63 y x z).
Proof. exact (EQ_MP (@lem2812452 y x z) (@lem0)). Qed.
Lemma lem2812454 (y : int) (x : int) (z : int) : term63 y x z.
Proof. exact (EQ_MP (@lem2812453 y x z) (@lem2812346 x y z)). Qed.
Lemma lem2812456 (b : Prop) (a : Prop) : (a \/ b) = (term66 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem2812457 (x : int) (y : int) (z : int) : (term63 y x z) = (term67 x y z).
Proof. exact (@lem2812456 (term68 y x z) (y = z)). Qed.
Lemma lem2812459 (a : Prop) (b : Prop) : (term69 a b) = (term70 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem2812460 (y : int) (x : int) (z : int) : (term71 y x z) = (term72 y x z).
Proof. exact (@lem2812459 (term59 x y) (term59 x z)). Qed.
Lemma lem2812462 (a : Prop) : (term73 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2812463 (x : int) (y : int) : (term74 x y) = (x = y).
Proof. exact (@lem2812462 (x = y)). Qed.
Lemma lem2812464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2812465 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem2812464) (@lem2812463 x y)). Qed.
Lemma lem2812467 (a : Prop) : (term73 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem2812468 (x : int) (z : int) : (term74 x z) = (x = z).
Proof. exact (@lem2812467 (x = z)). Qed.
Lemma lem2812469 (y : int) (x : int) (z : int) : (term72 y x z) = (term77 y x z).
Proof. exact (MK_COMB (@lem2812465 x y) (@lem2812468 x z)). Qed.
Lemma lem2812470 (y : int) (x : int) (z : int) : (term71 y x z) = (term77 y x z).
Proof. exact (TRANS (@lem2812460 y x z) (@lem2812469 y x z)). Qed.
Lemma lem2812471 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2812472 (y : int) (x : int) (z : int) : (term78 y x z) = (term79 y x z).
Proof. exact (MK_COMB (@lem2812471) (@lem2812470 y x z)). Qed.
Lemma lem2812473 (y : int) (z : int) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem2812474 (x : int) (y : int) (z : int) : (term67 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem2812472 y x z) (@lem2812473 y z)). Qed.
Lemma lem2812475 (x : int) (y : int) (z : int) : (term63 y x z) = (term80 x y z).
Proof. exact (TRANS (@lem2812457 x y z) (@lem2812474 x y z)). Qed.
Lemma lem2812477 (m : int) (n : int) (h1 : term10) (h2 : term24) : term81 m n.
Proof. exact (conj (@lem2812356 m n h1) (@lem2812364 m n h2)). Qed.
Lemma lem2812479 (x : int) (y : int) (z : int) : term80 x y z.
Proof. exact (EQ_MP (@lem2812475 x y z) (@lem2812454 y x z)). Qed.
Lemma lem2812480 (m : int) (n : int) : term82 m n.
Proof. exact (@lem2812479 (term19 m n) (term25 m n) (term20 m n)). Qed.
Lemma lem2812483 (m : int) (n : int) (h1 : term10) (h2 : term24) : (term25 m n) = (term20 m n).
Proof. exact (@lem2812480 m n (@lem2812477 m n h1 h2)). Qed.
Lemma lem2812484 (m : int) (n : int) (h1 : term10) (h2 : term24) : term83 m n.
Proof. exact (fun h0 : term35 m n => @lem2812483 m n h1 h2). Qed.
Lemma lem2812486 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2812487 (m : int) (n : int) : (term83 m n) = ((term25 m n) = (term20 m n)).
Proof. exact (@lem2812486 ((term25 m n) = (term20 m n))). Qed.
Lemma lem2812488 (m : int) (n : int) (h1 : term10) (h2 : term24) : (term25 m n) = (term20 m n).
Proof. exact (EQ_MP (@lem2812487 m n) (@lem2812484 m n h1 h2)). Qed.
Lemma lem2812491 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem2812493 (m : int) (n : int) : (term35 m n) = (term84 m n).
Proof. exact (@lem2812491 ((term25 m n) = (term20 m n))). Qed.
Lemma lem2812496 (m : int) (n : int) (h1 : term35 m n) : term84 m n.
Proof. exact (EQ_MP (@lem2812493 m n) (@lem2812290 m n h1)). Qed.
Lemma lem2812499 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : False.
Proof. exact (@lem2812496 m n h3 (@lem2812488 m n h1 h2)). Qed.
Lemma lem2812500 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : term85.
Proof. exact (fun h0 : ~ False => @lem2812499 m n h1 h2 h3). Qed.
Lemma lem2812502 (p : Prop) : (term54 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem2812503 : term85 = False.
Proof. exact (@lem2812502 False). Qed.
Lemma lem2812504 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : False.
Proof. exact (EQ_MP (@lem2812503) (@lem2812500 m n h1 h2 h3)). Qed.
Lemma lem2812505 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : (term35 m n) = False.
Proof. exact (prop_ext (fun h4 : term35 m n => @lem2812504 m n h1 h2 h3) (fun h4 : False => @lem2812290 m n h3)). Qed.
Lemma lem2812506 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : False.
Proof. exact (EQ_MP (@lem2812505 m n h1 h2 h3) (@lem2812290 m n h3)). Qed.
Lemma lem2812507 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : (term35 m n) = False.
Proof. exact (prop_ext (fun h4 : term35 m n => @lem2812506 m n h1 h2 h3) (fun h4 : False => @lem2812272 m n h3)). Qed.
Lemma lem2812508 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : False.
Proof. exact (EQ_MP (@lem2812507 m n h1 h2 h3) (@lem2812272 m n h3)). Qed.
Lemma lem2812509 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : (term35 m n) = False.
Proof. exact (prop_ext (fun h4 : term35 m n => @lem2812508 m n h1 h2 h3) (fun h4 : False => @lem2812272 m n h3)). Qed.
Lemma lem2812510 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : False.
Proof. exact (EQ_MP (@lem2812509 m n h1 h2 h3) (@lem2812272 m n h3)). Qed.
Lemma lem2812511 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem2812510 m n h1 h2 h3) (fun h4 : False => @lem2812268 h1)). Qed.
Lemma lem2812512 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : False.
Proof. exact (EQ_MP (@lem2812511 m n h1 h2 h3) (@lem2812268 h1)). Qed.
Lemma lem2812513 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : term24 = False.
Proof. exact (prop_ext (fun h4 : term24 => @lem2812512 m n h1 h2 h3) (fun h4 : False => @lem2812258 h2)). Qed.
Lemma lem2812514 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : False.
Proof. exact (EQ_MP (@lem2812513 m n h1 h2 h3) (@lem2812258 h2)). Qed.
Lemma lem2812515 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : (term35 m n) = False.
Proof. exact (prop_ext (fun h4 : term35 m n => @lem2812514 m n h1 h2 h3) (fun h4 : False => @lem2812248 m n h3)). Qed.
Lemma lem2812516 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : False.
Proof. exact (EQ_MP (@lem2812515 m n h1 h2 h3) (@lem2812248 m n h3)). Qed.
Lemma lem2812517 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem2812516 m n h1 h2 h3) (fun h4 : False => @lem2812218 h1)). Qed.
Lemma lem2812518 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : False.
Proof. exact (EQ_MP (@lem2812517 m n h1 h2 h3) (@lem2812218 h1)). Qed.
Lemma lem2812519 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : term24 = False.
Proof. exact (prop_ext (fun h4 : term24 => @lem2812518 m n h1 h2 h3) (fun h4 : False => @lem2812198 h2)). Qed.
Lemma lem2812520 (m : int) (n : int) (h1 : term10) (h2 : term24) (h3 : term35 m n) : False.
Proof. exact (EQ_MP (@lem2812519 m n h1 h2 h3) (@lem2812198 h2)). Qed.
Lemma lem2812521 (m : int) (h1 : term10) (h2 : term24) (h3 : term38 m) : False.
Proof. exact (ex_elim (@lem2812163 m h3) (fun n : int => fun h0 : term37 m n => @lem2812520 m n h1 h2 h0)). Qed.
Lemma lem2812522 (h1 : term10) (h2 : term24) (h3 : term3) : False.
Proof. exact (ex_elim (@lem2812122 h3) (fun m : int => fun h0 : term43 m => @lem2812521 m h1 h2 h0)). Qed.
Lemma lem2812523 (h1 : term10) (h2 : term24) (h3 : term3) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem2812522 h1 h2 h3) (fun h4 : False => @lem2812162 h1)). Qed.
Lemma lem2812524 (h1 : term10) (h2 : term24) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem2812523 h1 h2 h3) (@lem2812162 h1)). Qed.
Lemma lem2812525 (h1 : term10) (h2 : term24) (h3 : term3) : term24 = False.
Proof. exact (prop_ext (fun h4 : term24 => @lem2812524 h1 h2 h3) (fun h4 : False => @lem2812142 h2)). Qed.
Lemma lem2812526 (h1 : term10) (h2 : term24) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem2812525 h1 h2 h3) (@lem2812142 h2)). Qed.
Lemma lem2812527 (h1 : term24) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem2812526 h0 h1 h2). Qed.
Lemma lem2812528 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem2812529 (h1 : term24) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem2812528) (@lem2812527 h1 h2)). Qed.
Lemma lem2812530 (h1 : term3) : term13.
Proof. exact (fun h0 : term24 => @lem2812529 h0 h1). Qed.
Lemma lem2812531 : term15.
Proof. exact (fun h0 : term3 => @lem2812530 h0). Qed.
Lemma lem2812532 : term4.
Proof. exact (EQ_MP (@lem2812085) (@lem2812531)). Qed.
Lemma lem2812534 : term4.
Proof. exact (@lem2811967 (@lem2812532)). Qed.
Lemma lem2812535 (h1 : term3) : term12.
Proof. exact (@lem2812534 (@lem2811952 h1)). Qed.
Lemma lem2812536 (h1 : term3) : term8.
Proof. exact (@lem2812535 h1 (@lem2811937)). Qed.
Lemma lem2812537 (h1 : term3) : False.
Proof. exact (@lem2812536 h1 (@lem2306311)). Qed.
Lemma lem2812538 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem2812537 h1) (fun h2 : False => @lem2811952 h1)). Qed.
Lemma lem2812539 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem2812538 h1) (@lem2811952 h1)). Qed.
Lemma lem2812540 : term2.
Proof. exact (fun h0 : term3 => @lem2812539 h0). Qed.
Lemma lem2812541 : term1.
Proof. exact (EQ_MP (@lem2811951) (@lem2812540)). Qed.
