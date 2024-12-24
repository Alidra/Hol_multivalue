Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_DOWN_term_abbrevs.
Require Import REAL_LT_RCANCEL_IMP_spec.
Require Import REAL_MUL_RID_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1338912_spec.
Require Import thm1340174_spec.
Require Import thm1365105_spec.
Require Import thm1365990_spec.
Require Import thm1366271_spec.
Require Import thm1366971_spec.
Require Import thm1367247_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367767_spec.
Require Import thm1386578_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483456_spec.
Require Import thm1483460_spec.
Require Import thm1483474_spec.
Require Import thm1483476_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483529_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17362_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm996238_spec.
Lemma lem1634067 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (h1). Qed.
Lemma lem1634068 (x : real) (y : real) (z : real) (h1 : (term0 x y z) = (term1 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (SYM (@lem1634067 x y z h1)). Qed.
Lemma lem1634069 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term1 x y z) = (term0 x y z).
Proof. exact (h1). Qed.
Lemma lem1634070 (x : real) (y : real) (z : real) (h1 : (term1 x y z) = (term0 x y z)) : (term0 x y z) = (term1 x y z).
Proof. exact (SYM (@lem1634069 x y z h1)). Qed.
Lemma lem1634071 (x : real) (y : real) (z : real) : ((term0 x y z) = (term1 x y z)) = ((term1 x y z) = (term0 x y z)).
Proof. exact (prop_ext (fun h1 : (term0 x y z) = (term1 x y z) => @lem1634068 x y z h1) (fun h1 : (term1 x y z) = (term0 x y z) => @lem1634070 x y z h1)). Qed.
Lemma lem1634072 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (fun_ext (fun z : real => @lem1634071 x y z)). Qed.
Lemma lem1634073 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1634074 (x : real) (y : real) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1634073) (@lem1634072 x y)). Qed.
Lemma lem1634075 (x : real) : (term6 x) = (term7 x).
Proof. exact (fun_ext (fun y : real => @lem1634074 x y)). Qed.
Lemma lem1634076 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1634077 (x : real) : (term8 x) = (term9 x).
Proof. exact (MK_COMB (@lem1634076) (@lem1634075 x)). Qed.
Lemma lem1634078 : term10 = term11.
Proof. exact (fun_ext (fun x : real => @lem1634077 x)). Qed.
Lemma lem1634079 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1634080 : term12 = term13.
Proof. exact (MK_COMB (@lem1634079) (@lem1634078)). Qed.
Lemma lem1634081 : term13.
Proof. exact (EQ_MP (@lem1634080) (@lem1338912)). Qed.
Lemma lem1634082 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1634083 (x : real) (h1 : term14) : term15 x.
Proof. exact (@lem1634082 h1 x). Qed.
Lemma lem1634084 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1634085 (x : real) (h1 : term14) : term16 x.
Proof. exact (EQ_MP (@lem1634084 x) (@lem1634083 x h1)). Qed.
Lemma lem1634086 (x : real) (y : real) (h1 : term14) : term17 x y.
Proof. exact (@lem1634085 x h1 y). Qed.
Lemma lem1634087 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1634088 (x : real) (y : real) (h1 : term14) : term18 x y.
Proof. exact (EQ_MP (@lem1634087 x y) (@lem1634086 x y h1)). Qed.
Lemma lem1634089 (x : real) (y : real) (z : real) (h1 : term14) : term19 x y z.
Proof. exact (@lem1634088 x y h1 z). Qed.
Lemma lem1634090 (z : real) (x : real) (y : real) : (term19 x y z) = (term20 z x y).
Proof. exact (eq_refl (term19 x y z)). Qed.
Lemma lem1634091 (z : real) (x : real) (y : real) (h1 : term14) : term20 z x y.
Proof. exact (EQ_MP (@lem1634090 z x y) (@lem1634089 x y z h1)). Qed.
Lemma lem1634092 (x : real) (y : real) (z : real) (h1 : term21 x y z) : term21 x y z.
Proof. exact (h1). Qed.
Lemma lem1634093 (x : real) (y : real) (z : real) (h1 : term14) (h2 : term21 x y z) : real_lt x y.
Proof. exact (@lem1634091 z x y h1 (@lem1634092 x y z h2)). Qed.
Lemma lem1634094 (x : real) (y : real) (z : real) (h1 : term21 x y z) : term22 x y.
Proof. exact (fun h0 : term14 => @lem1634093 x y z h0 h1). Qed.
Lemma lem1634095 (x : real) (y : real) (h1 : term23 x y) : term23 x y.
Proof. exact (h1). Qed.
Lemma lem1634096 (x : real) (y : real) (h1 : term23 x y) : term22 x y.
Proof. exact (ex_elim (@lem1634095 x y h1) (fun z : real => fun h0 : term24 x y z => @lem1634094 x y z h0)). Qed.
Lemma lem1634097 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1634098 (x : real) (y : real) (h1 : term14) (h2 : term23 x y) : real_lt x y.
Proof. exact (@lem1634096 x y h2 (@lem1634097 h1)). Qed.
Lemma lem1634099 (x : real) (y : real) (h1 : term14) : term25 x y.
Proof. exact (fun h0 : term23 x y => @lem1634098 x y h1 h0). Qed.
Lemma lem1634100 (x : real) (h1 : term14) : term26 x.
Proof. exact (fun y : real => @lem1634099 x y h1). Qed.
Lemma lem1634101 (h1 : term14) : term27.
Proof. exact (fun x : real => @lem1634100 x h1). Qed.
Lemma lem1634102 : term28.
Proof. exact (fun h0 : term14 => @lem1634101 h0). Qed.
Lemma lem1634103 : term27.
Proof. exact (@lem1634102 (@lem1598629)). Qed.
Lemma lem1634104 (x : real) : term29 x.
Proof. exact (@lem1634103 x). Qed.
Lemma lem1634105 (x : real) : (term29 x) = (term26 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1634106 (x : real) : term26 x.
Proof. exact (EQ_MP (@lem1634105 x) (@lem1634104 x)). Qed.
Lemma lem1634107 (x : real) (y : real) : term30 x y.
Proof. exact (@lem1634106 x y). Qed.
Lemma lem1634108 (x : real) (y : real) : (term30 x y) = (term25 x y).
Proof. exact (eq_refl (term30 x y)). Qed.
Lemma lem1634112 (t : Prop) : (term31 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1634118 : term32 = (term33 = term34).
Proof. exact (@lem1634112 (term33 = term34)). Qed.
Lemma lem1634119 : (term33 = term34) = (term35 = term34).
Proof. exact (@lem1483529 term33 term34). Qed.
Lemma lem1634125 : term35 = term36.
Proof. exact (@lem1483519 term33 term34). Qed.
Lemma lem1634127 (x : nat) : (term37 x) = term34.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1634128 : term38 = term34.
Proof. exact (@lem1634127 term39). Qed.
Lemma lem1634129 : term40 = term40.
Proof. exact (eq_refl term40). Qed.
Lemma lem1634130 : term36 = term41.
Proof. exact (MK_COMB (@lem1634129) (@lem1634128)). Qed.
Lemma lem1634131 : term41 = term33.
Proof. exact (@lem1483450 term33). Qed.
Lemma lem1634132 : term36 = term33.
Proof. exact (TRANS (@lem1634130) (@lem1634131)). Qed.
Lemma lem1634134 : term35 = term33.
Proof. exact (TRANS (@lem1634125) (@lem1634132)). Qed.
Lemma lem1634135 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1634136 : term42 = term43.
Proof. exact (MK_COMB (@lem1634135) (@lem1634134)). Qed.
Lemma lem1634137 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1634138 : (term35 = term34) = (term33 = term34).
Proof. exact (MK_COMB (@lem1634136) (@lem1634137)). Qed.
Lemma lem1634139 : (term33 = term34) = (term33 = term34).
Proof. exact (TRANS (@lem1634119) (@lem1634138)). Qed.
Lemma lem1634148 : term32 = (term33 = term34).
Proof. exact (TRANS (@lem1634118) (@lem1634139)). Qed.
Lemma lem1634152 (h1 : term33 = term34) : term33 = term34.
Proof. exact (h1). Qed.
Lemma lem1634154 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (proj1 (@lem1366971 m n)). Qed.
Lemma lem1634155 : (term33 = term34) = (term44 = (NUMERAL 0)).
Proof. exact (@lem1634154 term44 (NUMERAL 0)). Qed.
Lemma lem1634156 : term45 = term46.
Proof. exact (@lem912803). Qed.
Lemma lem1634157 (h1 : term45 = term46) : (term44 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term46 h1). Qed.
Lemma lem1634158 : (term45 = term46) = ((term44 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term45 = term46 => @lem1634157 h1) (fun h1 : (term44 = (NUMERAL 0)) = False => @lem1634156)). Qed.
Lemma lem1634159 : (term44 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1634158) (@lem1634156)). Qed.
Lemma lem1634160 : (term33 = term34) = False.
Proof. exact (TRANS (@lem1634155) (@lem1634159)). Qed.
Lemma lem1634161 (h1 : term33 = term34) : False.
Proof. exact (EQ_MP (@lem1634160) (@lem1634152 h1)). Qed.
Lemma lem1634163 (h1 : term33 = term34) : term33 = term34.
Proof. exact (h1). Qed.
Lemma lem1634164 (h1 : term33 = term34) : (term33 = term34) = False.
Proof. exact (prop_ext (fun h2 : term33 = term34 => @lem1634161 h1) (fun h2 : False => @lem1634163 h1)). Qed.
Lemma lem1634165 (h1 : term33 = term34) : False.
Proof. exact (EQ_MP (@lem1634164 h1) (@lem1634163 h1)). Qed.
Lemma lem1634166 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem1634167 (h1 : term32) : term33 = term34.
Proof. exact (EQ_MP (@lem1634148) (@lem1634166 h1)). Qed.
Lemma lem1634168 (h1 : term32) : (term33 = term34) = False.
Proof. exact (prop_ext (fun h2 : term33 = term34 => @lem1634165 h2) (fun h2 : False => @lem1634167 h1)). Qed.
Lemma lem1634169 (h1 : term32) : False.
Proof. exact (EQ_MP (@lem1634168 h1) (@lem1634167 h1)). Qed.
Lemma lem1634170 : term47.
Proof. exact (fun h0 : term32 => @lem1634169 h0). Qed.
Lemma lem1634171 : term48.
Proof. exact (@lem1386578 term49). Qed.
Lemma lem1634172 : term49.
Proof. exact (@lem1634171 (@lem1634170)). Qed.
Lemma lem1634173 (x : real) : term50 x.
Proof. exact (@lem1340174 x). Qed.
Lemma lem1634174 (x : real) : (term50 x) = (term51 x).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1634177 (x : real) : term51 x.
Proof. exact (EQ_MP (@lem1634174 x) (@lem1634173 x)). Qed.
Lemma lem1634178 : term52.
Proof. exact (@lem1634177 term33). Qed.
Lemma lem1634189 : term53 = term54.
Proof. exact (@lem1483531 term34 term33). Qed.
Lemma lem1634195 : term55 = term56.
Proof. exact (@lem1483519 term34 term33). Qed.
Lemma lem1634197 (m : nat) (n : nat) : (term57 m n) = (term58 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1634198 : term59 = term60.
Proof. exact (@lem1634197 term39 term44). Qed.
Lemma lem1634199 : term61 = term46.
Proof. exact (@lem996238 term46). Qed.
Lemma lem1634200 : (term61 = term46) = (term62 = term44).
Proof. exact (@lem1007663 (BIT1 0) term46 term46). Qed.
Lemma lem1634201 : term62 = term44.
Proof. exact (EQ_MP (@lem1634200) (@lem1634199)). Qed.
Lemma lem1634202 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1634203 : term63 = term33.
Proof. exact (MK_COMB (@lem1634202) (@lem1634201)). Qed.
Lemma lem1634204 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1634205 : term60 = term64.
Proof. exact (MK_COMB (@lem1634204) (@lem1634203)). Qed.
Lemma lem1634206 : term59 = term64.
Proof. exact (TRANS (@lem1634198) (@lem1634205)). Qed.
Lemma lem1634207 : term65 = term65.
Proof. exact (eq_refl term65). Qed.
Lemma lem1634208 : term56 = term66.
Proof. exact (MK_COMB (@lem1634207) (@lem1634206)). Qed.
Lemma lem1634209 : term66 = term64.
Proof. exact (@lem1483448 term64). Qed.
Lemma lem1634210 : term56 = term64.
Proof. exact (TRANS (@lem1634208) (@lem1634209)). Qed.
Lemma lem1634212 : term55 = term64.
Proof. exact (TRANS (@lem1634195) (@lem1634210)). Qed.
Lemma lem1634213 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1634214 : term67 = term68.
Proof. exact (MK_COMB (@lem1634213) (@lem1634212)). Qed.
Lemma lem1634215 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1634216 : term54 = term69.
Proof. exact (MK_COMB (@lem1634214) (@lem1634215)). Qed.
Lemma lem1634226 : term53 = term69.
Proof. exact (TRANS (@lem1634189) (@lem1634216)). Qed.
Lemma lem1634230 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem1634232 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (proj2 (@lem1365990 m n)). Qed.
Lemma lem1634233 : term69 = term72.
Proof. exact (@lem1634232 term44 (NUMERAL 0)). Qed.
Lemma lem1634234 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem1634235 : term45 = term46.
Proof. exact (@lem912803). Qed.
Lemma lem1634236 (h1 : term45 = term46) : (term44 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term46 h1). Qed.
Lemma lem1634237 : (term45 = term46) = ((term44 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term45 = term46 => @lem1634236 h1) (fun h1 : (term44 = (NUMERAL 0)) = False => @lem1634235)). Qed.
Lemma lem1634238 : (term44 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem1634237) (@lem1634235)). Qed.
Lemma lem1634239 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1634240 : term73 = (and False).
Proof. exact (MK_COMB (@lem1634239) (@lem1634238)). Qed.
Lemma lem1634241 : term72 = (False /\ True).
Proof. exact (MK_COMB (@lem1634240) (@lem1634234)). Qed.
Lemma lem1634243 : (False /\ True) = False.
Proof. exact (proj1 (@lem1365105)). Qed.
Lemma lem1634244 : term72 = False.
Proof. exact (TRANS (@lem1634241) (@lem1634243)). Qed.
Lemma lem1634245 : term69 = False.
Proof. exact (TRANS (@lem1634233) (@lem1634244)). Qed.
Lemma lem1634246 (h1 : term69) : False.
Proof. exact (EQ_MP (@lem1634245) (@lem1634230 h1)). Qed.
Lemma lem1634248 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem1634249 (h1 : term69) : term69 = False.
Proof. exact (prop_ext (fun h2 : term69 => @lem1634246 h1) (fun h2 : False => @lem1634248 h1)). Qed.
Lemma lem1634250 (h1 : term69) : False.
Proof. exact (EQ_MP (@lem1634249 h1) (@lem1634248 h1)). Qed.
Lemma lem1634251 (h1 : term53) : term53.
Proof. exact (h1). Qed.
Lemma lem1634252 (h1 : term53) : term69.
Proof. exact (EQ_MP (@lem1634226) (@lem1634251 h1)). Qed.
Lemma lem1634253 (h1 : term53) : term69 = False.
Proof. exact (prop_ext (fun h2 : term69 => @lem1634250 h2) (fun h2 : False => @lem1634252 h1)). Qed.
Lemma lem1634254 (h1 : term53) : False.
Proof. exact (EQ_MP (@lem1634253 h1) (@lem1634252 h1)). Qed.
Lemma lem1634255 : term74.
Proof. exact (fun h0 : term53 => @lem1634254 h0). Qed.
Lemma lem1634256 : term75.
Proof. exact (@lem1386578 term76). Qed.
Lemma lem1634257 : term76.
Proof. exact (@lem1634256 (@lem1634255)). Qed.
Lemma lem1634258 (d : real) (h1 : term77 d) : term77 d.
Proof. exact (h1). Qed.
Lemma lem1634260 (x : real) (y : real) : term25 x y.
Proof. exact (EQ_MP (@lem1634108 x y) (@lem1634107 x y)). Qed.
Lemma lem1634261 (d : real) : term78 d.
Proof. exact (@lem1634260 term34 (term79 d)). Qed.
Lemma lem1634263 (x : real) (y : real) : term25 x y.
Proof. exact (EQ_MP (@lem1634108 x y) (@lem1634107 x y)). Qed.
Lemma lem1634264 (d : real) : term80 d.
Proof. exact (@lem1634263 (term79 d) d). Qed.
Lemma lem1634265 (x : real) : term81 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem1634266 (x : real) : (term81 x) = ((term82 x) = x).
Proof. exact (eq_refl (term81 x)). Qed.
Lemma lem1634268 (x : real) : term83 x.
Proof. exact (@lem1634081 x). Qed.
Lemma lem1634269 (x : real) : (term83 x) = (term9 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem1634270 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1634269 x) (@lem1634268 x)). Qed.
Lemma lem1634271 (x : real) (y : real) : term84 x y.
Proof. exact (@lem1634270 x y). Qed.
Lemma lem1634272 (x : real) (y : real) : (term84 x y) = (term5 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1634273 (x : real) (y : real) : term5 x y.
Proof. exact (EQ_MP (@lem1634272 x y) (@lem1634271 x y)). Qed.
Lemma lem1634274 (x : real) (y : real) (z : real) : term85 x y z.
Proof. exact (@lem1634273 x y z). Qed.
Lemma lem1634275 (x : real) (y : real) (z : real) : (term85 x y z) = ((term1 x y z) = (term0 x y z)).
Proof. exact (eq_refl (term85 x y z)). Qed.
Lemma lem1634277 (x : real) : term86 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1634278 (x : real) : (term86 x) = (term87 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1634279 (x : real) : term87 x.
Proof. exact (EQ_MP (@lem1634278 x) (@lem1634277 x)). Qed.
Lemma lem1634280 (x : real) (y : real) : term88 x y.
Proof. exact (@lem1634279 x y). Qed.
Lemma lem1634281 (x : real) (y : real) : (term88 x y) = ((real_div x y) = (term89 x y)).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1634285 : term76 = (term76 = True).
Proof. exact (@lem7 term76). Qed.
Lemma lem1634290 : term76 = True.
Proof. exact (EQ_MP (@lem1634285) (@lem1634257)). Qed.
Lemma lem1634291 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1634292 : term90 = (and True).
Proof. exact (MK_COMB (@lem1634291) (@lem1634290)). Qed.
Lemma lem1634294 (x : real) (y : real) : (real_div x y) = (term89 x y).
Proof. exact (EQ_MP (@lem1634281 x y) (@lem1634280 x y)). Qed.
Lemma lem1634295 (d : real) : (term79 d) = (term91 d).
Proof. exact (@lem1634294 d term33). Qed.
Lemma lem1634296 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1634297 (d : real) : (term92 d) = (term93 d).
Proof. exact (MK_COMB (@lem1634296) (@lem1634295 d)). Qed.
Lemma lem1634298 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1634299 (d : real) : (term94 d) = (term95 d).
Proof. exact (MK_COMB (@lem1634297 d) (@lem1634298)). Qed.
Lemma lem1634301 (x : real) (y : real) (z : real) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1634275 x y z) (@lem1634274 x y z)). Qed.
Lemma lem1634302 (d : real) : (term95 d) = (term96 d).
Proof. exact (@lem1634301 d term97 term33). Qed.
Lemma lem1634304 : term98 = term99.
Proof. exact (@lem1634178 (@lem1634172)). Qed.
Lemma lem1634305 (d : real) : (real_mul d) = (real_mul d).
Proof. exact (eq_refl (real_mul d)). Qed.
Lemma lem1634306 (d : real) : (term96 d) = (term82 d).
Proof. exact (MK_COMB (@lem1634305 d) (@lem1634304)). Qed.
Lemma lem1634308 (x : real) : (term82 x) = x.
Proof. exact (EQ_MP (@lem1634266 x) (@lem1634265 x)). Qed.
Lemma lem1634309 (d : real) : (term82 d) = d.
Proof. exact (@lem1634308 d). Qed.
Lemma lem1634310 (d : real) : (term96 d) = d.
Proof. exact (TRANS (@lem1634306 d) (@lem1634309 d)). Qed.
Lemma lem1634311 (d : real) : (term95 d) = d.
Proof. exact (TRANS (@lem1634302 d) (@lem1634310 d)). Qed.
Lemma lem1634312 (d : real) : (term94 d) = d.
Proof. exact (TRANS (@lem1634299 d) (@lem1634311 d)). Qed.
Lemma lem1634313 : term100 = term100.
Proof. exact (eq_refl term100). Qed.
Lemma lem1634314 (d : real) : (term101 d) = (term102 d).
Proof. exact (MK_COMB (@lem1634313) (@lem1634312 d)). Qed.
Lemma lem1634315 (d : real) : (term103 d) = (term104 d).
Proof. exact (MK_COMB (@lem1634292) (@lem1634314 d)). Qed.
Lemma lem1634317 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1634318 (d : real) : (term104 d) = (term102 d).
Proof. exact (@lem1634317 (term102 d)). Qed.
Lemma lem1634319 (d : real) : (term103 d) = (term102 d).
Proof. exact (TRANS (@lem1634315 d) (@lem1634318 d)). Qed.
Lemma lem1634320 (d : real) : (term102 d) = (term103 d).
Proof. exact (SYM (@lem1634319 d)). Qed.
Lemma lem1634321 (x : real) : term81 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem1634322 (x : real) : (term81 x) = ((term82 x) = x).
Proof. exact (eq_refl (term81 x)). Qed.
Lemma lem1634324 (x : real) : term83 x.
Proof. exact (@lem1634081 x). Qed.
Lemma lem1634325 (x : real) : (term83 x) = (term9 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem1634326 (x : real) : term9 x.
Proof. exact (EQ_MP (@lem1634325 x) (@lem1634324 x)). Qed.
Lemma lem1634327 (x : real) (y : real) : term84 x y.
Proof. exact (@lem1634326 x y). Qed.
Lemma lem1634328 (x : real) (y : real) : (term84 x y) = (term5 x y).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem1634329 (x : real) (y : real) : term5 x y.
Proof. exact (EQ_MP (@lem1634328 x y) (@lem1634327 x y)). Qed.
Lemma lem1634330 (x : real) (y : real) (z : real) : term85 x y z.
Proof. exact (@lem1634329 x y z). Qed.
Lemma lem1634331 (x : real) (y : real) (z : real) : (term85 x y z) = ((term1 x y z) = (term0 x y z)).
Proof. exact (eq_refl (term85 x y z)). Qed.
Lemma lem1634333 (x : real) : term86 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1634334 (x : real) : (term86 x) = (term87 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1634335 (x : real) : term87 x.
Proof. exact (EQ_MP (@lem1634334 x) (@lem1634333 x)). Qed.
Lemma lem1634336 (x : real) (y : real) : term88 x y.
Proof. exact (@lem1634335 x y). Qed.
Lemma lem1634337 (x : real) (y : real) : (term88 x y) = ((real_div x y) = (term89 x y)).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1634341 : term76 = (term76 = True).
Proof. exact (@lem7 term76). Qed.
Lemma lem1634346 : term76 = True.
Proof. exact (EQ_MP (@lem1634341) (@lem1634257)). Qed.
Lemma lem1634347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1634348 : term90 = (and True).
Proof. exact (MK_COMB (@lem1634347) (@lem1634346)). Qed.
Lemma lem1634350 (x : real) (y : real) : (real_div x y) = (term89 x y).
Proof. exact (EQ_MP (@lem1634337 x y) (@lem1634336 x y)). Qed.
Lemma lem1634351 (d : real) : (term79 d) = (term91 d).
Proof. exact (@lem1634350 d term33). Qed.
Lemma lem1634352 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1634353 (d : real) : (term92 d) = (term93 d).
Proof. exact (MK_COMB (@lem1634352) (@lem1634351 d)). Qed.
Lemma lem1634354 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1634355 (d : real) : (term94 d) = (term95 d).
Proof. exact (MK_COMB (@lem1634353 d) (@lem1634354)). Qed.
Lemma lem1634357 (x : real) (y : real) (z : real) : (term1 x y z) = (term0 x y z).
Proof. exact (EQ_MP (@lem1634331 x y z) (@lem1634330 x y z)). Qed.
Lemma lem1634358 (d : real) : (term95 d) = (term96 d).
Proof. exact (@lem1634357 d term97 term33). Qed.
Lemma lem1634360 : term98 = term99.
Proof. exact (@lem1634178 (@lem1634172)). Qed.
Lemma lem1634361 (d : real) : (real_mul d) = (real_mul d).
Proof. exact (eq_refl (real_mul d)). Qed.
Lemma lem1634362 (d : real) : (term96 d) = (term82 d).
Proof. exact (MK_COMB (@lem1634361 d) (@lem1634360)). Qed.
Lemma lem1634364 (x : real) : (term82 x) = x.
Proof. exact (EQ_MP (@lem1634322 x) (@lem1634321 x)). Qed.
Lemma lem1634365 (d : real) : (term82 d) = d.
Proof. exact (@lem1634364 d). Qed.
Lemma lem1634366 (d : real) : (term96 d) = d.
Proof. exact (TRANS (@lem1634362 d) (@lem1634365 d)). Qed.
Lemma lem1634367 (d : real) : (term95 d) = d.
Proof. exact (TRANS (@lem1634358 d) (@lem1634366 d)). Qed.
Lemma lem1634368 (d : real) : (term94 d) = d.
Proof. exact (TRANS (@lem1634355 d) (@lem1634367 d)). Qed.
Lemma lem1634369 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1634370 (d : real) : (term105 d) = (real_lt d).
Proof. exact (MK_COMB (@lem1634369) (@lem1634368 d)). Qed.
Lemma lem1634371 (d : real) : (term106 d) = (term106 d).
Proof. exact (eq_refl (term106 d)). Qed.
Lemma lem1634372 (d : real) : (term107 d) = (term108 d).
Proof. exact (MK_COMB (@lem1634370 d) (@lem1634371 d)). Qed.
Lemma lem1634373 (d : real) : (term109 d) = (term110 d).
Proof. exact (MK_COMB (@lem1634348) (@lem1634372 d)). Qed.
Lemma lem1634375 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1634376 (d : real) : (term110 d) = (term108 d).
Proof. exact (@lem1634375 (term108 d)). Qed.
Lemma lem1634377 (d : real) : (term109 d) = (term108 d).
Proof. exact (TRANS (@lem1634373 d) (@lem1634376 d)). Qed.
Lemma lem1634378 (d : real) : (term108 d) = (term109 d).
Proof. exact (SYM (@lem1634377 d)). Qed.
Lemma lem1634399 (d : real) : (term111 d) = (term112 d).
Proof. exact (@lem17362 (term77 d) (term102 d)). Qed.
Lemma lem1634400 (d : real) : (term77 d) = (term113 d).
Proof. exact (@lem1483521 d term34). Qed.
Lemma lem1634406 (d : real) : (term114 d) = (term115 d).
Proof. exact (@lem1483519 d term34). Qed.
Lemma lem1634408 (x : nat) : (term37 x) = term34.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1634409 : term38 = term34.
Proof. exact (@lem1634408 term39). Qed.
Lemma lem1634410 (d : real) : (real_add d) = (real_add d).
Proof. exact (eq_refl (real_add d)). Qed.
Lemma lem1634411 (d : real) : (term115 d) = (term116 d).
Proof. exact (MK_COMB (@lem1634410 d) (@lem1634409)). Qed.
Lemma lem1634412 (d : real) : (term116 d) = d.
Proof. exact (@lem1483450 d). Qed.
Lemma lem1634413 (d : real) : (term115 d) = d.
Proof. exact (TRANS (@lem1634411 d) (@lem1634412 d)). Qed.
Lemma lem1634415 (d : real) : (term114 d) = d.
Proof. exact (TRANS (@lem1634406 d) (@lem1634413 d)). Qed.
Lemma lem1634416 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1634417 (d : real) : (term117 d) = (real_gt d).
Proof. exact (MK_COMB (@lem1634416) (@lem1634415 d)). Qed.
Lemma lem1634418 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1634419 (d : real) : (term113 d) = (term118 d).
Proof. exact (MK_COMB (@lem1634417 d) (@lem1634418)). Qed.
Lemma lem1634420 (d : real) : (term77 d) = (term118 d).
Proof. exact (TRANS (@lem1634400 d) (@lem1634419 d)). Qed.
Lemma lem1634421 (d : real) : (term119 d) = (term120 d).
Proof. exact (@lem1483531 term121 d). Qed.
Lemma lem1634422 (d : real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1634429 : term121 = term34.
Proof. exact (@lem1483456 term33). Qed.
Lemma lem1634430 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1634431 : term122 = term123.
Proof. exact (MK_COMB (@lem1634430) (@lem1634429)). Qed.
Lemma lem1634432 (d : real) : (term124 d) = (term125 d).
Proof. exact (MK_COMB (@lem1634431) (@lem1634422 d)). Qed.
Lemma lem1634433 (d : real) : (term125 d) = (term126 d).
Proof. exact (@lem1483519 term34 d). Qed.
Lemma lem1634438 (d : real) : (term126 d) = (term127 d).
Proof. exact (@lem1483448 (term127 d)). Qed.
Lemma lem1634439 (d : real) : (term125 d) = (term127 d).
Proof. exact (TRANS (@lem1634433 d) (@lem1634438 d)). Qed.
Lemma lem1634440 (d : real) : (term124 d) = (term127 d).
Proof. exact (TRANS (@lem1634432 d) (@lem1634439 d)). Qed.
Lemma lem1634441 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1634442 (d : real) : (term128 d) = (term129 d).
Proof. exact (MK_COMB (@lem1634441) (@lem1634440 d)). Qed.
Lemma lem1634443 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1634444 (d : real) : (term120 d) = (term130 d).
Proof. exact (MK_COMB (@lem1634442 d) (@lem1634443)). Qed.
Lemma lem1634445 (d : real) : (term119 d) = (term130 d).
Proof. exact (TRANS (@lem1634421 d) (@lem1634444 d)). Qed.
Lemma lem1634446 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1634447 (d : real) : (term131 d) = (term132 d).
Proof. exact (MK_COMB (@lem1634446) (@lem1634420 d)). Qed.
Lemma lem1634448 (d : real) : (term112 d) = (term133 d).
Proof. exact (MK_COMB (@lem1634447 d) (@lem1634445 d)). Qed.
Lemma lem1634463 (d : real) : (term111 d) = (term133 d).
Proof. exact (TRANS (@lem1634399 d) (@lem1634448 d)). Qed.
Lemma lem1634467 (d : real) (h1 : term133 d) : term133 d.
Proof. exact (h1). Qed.
Lemma lem1634468 (d : real) (h1 : term133 d) : term130 d.
Proof. exact (proj2 (@lem1634467 d h1)). Qed.
Lemma lem1634469 (d : real) (h1 : term133 d) : term118 d.
Proof. exact (proj1 (@lem1634467 d h1)). Qed.
Lemma lem1634471 (n : nat) (m : nat) : (term134 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1634472 : term135 = term136.
Proof. exact (@lem1634471 (NUMERAL 0) term39). Qed.
Lemma lem1634473 : term137 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1634474 (h1 : term137 = (BIT1 0)) : term136 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1634475 : (term137 = (BIT1 0)) = (term136 = True).
Proof. exact (prop_ext (fun h1 : term137 = (BIT1 0) => @lem1634474 h1) (fun h1 : term136 = True => @lem1634473)). Qed.
Lemma lem1634476 : term136 = True.
Proof. exact (EQ_MP (@lem1634475) (@lem1634473)). Qed.
Lemma lem1634477 : term135 = True.
Proof. exact (TRANS (@lem1634472) (@lem1634476)). Qed.
Lemma lem1634478 : True = term135.
Proof. exact (SYM (@lem1634477)). Qed.
Lemma lem1634479 : term135.
Proof. exact (EQ_MP (@lem1634478) (@lem0)). Qed.
Lemma lem1634480 (d : real) (h1 : term133 d) : term138 d.
Proof. exact (conj (@lem1634479) (@lem1634468 d h1)). Qed.
Lemma lem1634482 (x : real) (y : real) : term139 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1634483 (d : real) : term140 d.
Proof. exact (@lem1634482 term99 (term127 d)). Qed.
Lemma lem1634484 (d : real) (h1 : term133 d) : term141 d.
Proof. exact (@lem1634483 d (@lem1634480 d h1)). Qed.
Lemma lem1634485 (d : real) : (term142 d) = (term127 d).
Proof. exact (@lem1483460 (term127 d)). Qed.
Lemma lem1634486 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1634487 (d : real) : (term143 d) = (term129 d).
Proof. exact (MK_COMB (@lem1634486) (@lem1634485 d)). Qed.
Lemma lem1634488 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1634489 (d : real) : (term141 d) = (term130 d).
Proof. exact (MK_COMB (@lem1634487 d) (@lem1634488)). Qed.
Lemma lem1634490 (d : real) (h1 : term133 d) : term130 d.
Proof. exact (EQ_MP (@lem1634489 d) (@lem1634484 d h1)). Qed.
Lemma lem1634492 (n : nat) (m : nat) : (term134 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1634493 : term135 = term136.
Proof. exact (@lem1634492 (NUMERAL 0) term39). Qed.
Lemma lem1634494 : term137 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1634495 (h1 : term137 = (BIT1 0)) : term136 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1634496 : (term137 = (BIT1 0)) = (term136 = True).
Proof. exact (prop_ext (fun h1 : term137 = (BIT1 0) => @lem1634495 h1) (fun h1 : term136 = True => @lem1634494)). Qed.
Lemma lem1634497 : term136 = True.
Proof. exact (EQ_MP (@lem1634496) (@lem1634494)). Qed.
Lemma lem1634498 : term135 = True.
Proof. exact (TRANS (@lem1634493) (@lem1634497)). Qed.
Lemma lem1634499 : True = term135.
Proof. exact (SYM (@lem1634498)). Qed.
Lemma lem1634500 : term135.
Proof. exact (EQ_MP (@lem1634499) (@lem0)). Qed.
Lemma lem1634501 (d : real) (h1 : term133 d) : term144 d.
Proof. exact (conj (@lem1634500) (@lem1634469 d h1)). Qed.
Lemma lem1634503 (x : real) (y : real) : term145 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1634504 (d : real) : term146 d.
Proof. exact (@lem1634503 term99 d). Qed.
Lemma lem1634505 (d : real) (h1 : term133 d) : term147 d.
Proof. exact (@lem1634504 d (@lem1634501 d h1)). Qed.
Lemma lem1634506 (d : real) : (term148 d) = d.
Proof. exact (@lem1483460 d). Qed.
Lemma lem1634507 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1634508 (d : real) : (term149 d) = (real_gt d).
Proof. exact (MK_COMB (@lem1634507) (@lem1634506 d)). Qed.
Lemma lem1634509 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1634510 (d : real) : (term147 d) = (term118 d).
Proof. exact (MK_COMB (@lem1634508 d) (@lem1634509)). Qed.
Lemma lem1634511 (d : real) (h1 : term133 d) : term118 d.
Proof. exact (EQ_MP (@lem1634510 d) (@lem1634505 d h1)). Qed.
Lemma lem1634512 (d : real) (h1 : term133 d) : term133 d.
Proof. exact (conj (@lem1634511 d h1) (@lem1634490 d h1)). Qed.
Lemma lem1634514 (x : real) (y : real) : term150 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1634515 (d : real) : term151 d.
Proof. exact (@lem1634514 d (term127 d)). Qed.
Lemma lem1634516 (d : real) (h1 : term133 d) : term152 d.
Proof. exact (@lem1634515 d (@lem1634512 d h1)). Qed.
Lemma lem1634517 (d : real) : (term153 d) = (term154 d).
Proof. exact (@lem1483442 term155 d). Qed.
Lemma lem1634519 (m : nat) : (term156 m) = term34.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1634520 : term157 = term34.
Proof. exact (@lem1634519 term39). Qed.
Lemma lem1634521 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1634522 : term158 = term159.
Proof. exact (MK_COMB (@lem1634521) (@lem1634520)). Qed.
Lemma lem1634523 (d : real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1634524 (d : real) : (term154 d) = (term160 d).
Proof. exact (MK_COMB (@lem1634522) (@lem1634523 d)). Qed.
Lemma lem1634525 (d : real) : (term153 d) = (term160 d).
Proof. exact (TRANS (@lem1634517 d) (@lem1634524 d)). Qed.
Lemma lem1634526 (d : real) : (term160 d) = term34.
Proof. exact (@lem1483446 d). Qed.
Lemma lem1634527 (d : real) : (term153 d) = term34.
Proof. exact (TRANS (@lem1634525 d) (@lem1634526 d)). Qed.
Lemma lem1634528 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1634529 (d : real) : (term161 d) = term162.
Proof. exact (MK_COMB (@lem1634528) (@lem1634527 d)). Qed.
Lemma lem1634530 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1634531 (d : real) : (term152 d) = term163.
Proof. exact (MK_COMB (@lem1634529 d) (@lem1634530)). Qed.
Lemma lem1634532 (d : real) (h1 : term133 d) : term163.
Proof. exact (EQ_MP (@lem1634531 d) (@lem1634516 d h1)). Qed.
Lemma lem1634534 (n : nat) (m : nat) : (term134 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1634535 : term163 = term164.
Proof. exact (@lem1634534 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1634536 : term164 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1634537 : term163 = False.
Proof. exact (TRANS (@lem1634535) (@lem1634536)). Qed.
Lemma lem1634538 (d : real) (h1 : term133 d) : False.
Proof. exact (EQ_MP (@lem1634537) (@lem1634532 d h1)). Qed.
Lemma lem1634540 (d : real) (h1 : term133 d) : term133 d.
Proof. exact (h1). Qed.
Lemma lem1634541 (d : real) (h1 : term133 d) : (term133 d) = False.
Proof. exact (prop_ext (fun h2 : term133 d => @lem1634538 d h1) (fun h2 : False => @lem1634540 d h1)). Qed.
Lemma lem1634542 (d : real) (h1 : term133 d) : False.
Proof. exact (EQ_MP (@lem1634541 d h1) (@lem1634540 d h1)). Qed.
Lemma lem1634543 (d : real) (h1 : term111 d) : term111 d.
Proof. exact (h1). Qed.
Lemma lem1634544 (d : real) (h1 : term111 d) : term133 d.
Proof. exact (EQ_MP (@lem1634463 d) (@lem1634543 d h1)). Qed.
Lemma lem1634545 (d : real) (h1 : term111 d) : (term133 d) = False.
Proof. exact (prop_ext (fun h2 : term133 d => @lem1634542 d h2) (fun h2 : False => @lem1634544 d h1)). Qed.
Lemma lem1634546 (d : real) (h1 : term111 d) : False.
Proof. exact (EQ_MP (@lem1634545 d h1) (@lem1634544 d h1)). Qed.
Lemma lem1634547 (d : real) : term165 d.
Proof. exact (fun h0 : term111 d => @lem1634546 d h0). Qed.
Lemma lem1634548 (d : real) : term166 d.
Proof. exact (@lem1386578 (term167 d)). Qed.
Lemma lem1634549 (d : real) : term167 d.
Proof. exact (@lem1634548 d (@lem1634547 d)). Qed.
Lemma lem1634570 (d : real) : (term168 d) = (term169 d).
Proof. exact (@lem17362 (term77 d) (term108 d)). Qed.
Lemma lem1634571 (d : real) : (term77 d) = (term113 d).
Proof. exact (@lem1483521 d term34). Qed.
Lemma lem1634577 (d : real) : (term114 d) = (term115 d).
Proof. exact (@lem1483519 d term34). Qed.
Lemma lem1634579 (x : nat) : (term37 x) = term34.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1634580 : term38 = term34.
Proof. exact (@lem1634579 term39). Qed.
Lemma lem1634581 (d : real) : (real_add d) = (real_add d).
Proof. exact (eq_refl (real_add d)). Qed.
Lemma lem1634582 (d : real) : (term115 d) = (term116 d).
Proof. exact (MK_COMB (@lem1634581 d) (@lem1634580)). Qed.
Lemma lem1634583 (d : real) : (term116 d) = d.
Proof. exact (@lem1483450 d). Qed.
Lemma lem1634584 (d : real) : (term115 d) = d.
Proof. exact (TRANS (@lem1634582 d) (@lem1634583 d)). Qed.
Lemma lem1634586 (d : real) : (term114 d) = d.
Proof. exact (TRANS (@lem1634577 d) (@lem1634584 d)). Qed.
Lemma lem1634587 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1634588 (d : real) : (term117 d) = (real_gt d).
Proof. exact (MK_COMB (@lem1634587) (@lem1634586 d)). Qed.
Lemma lem1634589 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1634590 (d : real) : (term113 d) = (term118 d).
Proof. exact (MK_COMB (@lem1634588 d) (@lem1634589)). Qed.
Lemma lem1634591 (d : real) : (term77 d) = (term118 d).
Proof. exact (TRANS (@lem1634571 d) (@lem1634590 d)). Qed.
Lemma lem1634592 (d : real) : (term170 d) = (term171 d).
Proof. exact (@lem1483531 d (term106 d)). Qed.
Lemma lem1634599 (d : real) : (term106 d) = (term172 d).
Proof. exact (@lem1483474 term33 d). Qed.
Lemma lem1634602 (d : real) : (real_sub d) = (real_sub d).
Proof. exact (eq_refl (real_sub d)). Qed.
Lemma lem1634603 (d : real) : (term173 d) = (term174 d).
Proof. exact (MK_COMB (@lem1634602 d) (@lem1634599 d)). Qed.
Lemma lem1634604 (d : real) : (term174 d) = (term175 d).
Proof. exact (@lem1483519 d (term172 d)). Qed.
Lemma lem1634605 (d : real) : (term176 d) = (term177 d).
Proof. exact (@lem1483476 term155 term33 d). Qed.
Lemma lem1634607 (m : nat) (n : nat) : (term57 m n) = (term58 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1634608 : term59 = term60.
Proof. exact (@lem1634607 term39 term44). Qed.
Lemma lem1634609 : term61 = term46.
Proof. exact (@lem996238 term46). Qed.
Lemma lem1634610 : (term61 = term46) = (term62 = term44).
Proof. exact (@lem1007663 (BIT1 0) term46 term46). Qed.
Lemma lem1634611 : term62 = term44.
Proof. exact (EQ_MP (@lem1634610) (@lem1634609)). Qed.
Lemma lem1634612 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1634613 : term63 = term33.
Proof. exact (MK_COMB (@lem1634612) (@lem1634611)). Qed.
Lemma lem1634614 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1634615 : term60 = term64.
Proof. exact (MK_COMB (@lem1634614) (@lem1634613)). Qed.
Lemma lem1634616 : term59 = term64.
Proof. exact (TRANS (@lem1634608) (@lem1634615)). Qed.
Lemma lem1634617 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1634618 : term178 = term179.
Proof. exact (MK_COMB (@lem1634617) (@lem1634616)). Qed.
Lemma lem1634619 (d : real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1634620 (d : real) : (term177 d) = (term180 d).
Proof. exact (MK_COMB (@lem1634618) (@lem1634619 d)). Qed.
Lemma lem1634621 (d : real) : (term176 d) = (term180 d).
Proof. exact (TRANS (@lem1634605 d) (@lem1634620 d)). Qed.
Lemma lem1634622 (d : real) : (real_add d) = (real_add d).
Proof. exact (eq_refl (real_add d)). Qed.
Lemma lem1634623 (d : real) : (term175 d) = (term181 d).
Proof. exact (MK_COMB (@lem1634622 d) (@lem1634621 d)). Qed.
Lemma lem1634624 (d : real) : (term181 d) = (term182 d).
Proof. exact (@lem1483442 term64 d). Qed.
Lemma lem1634627 : term183 = term155.
Proof. exact (@lem1367767 term39 term39). Qed.
Lemma lem1634628 : term184 = term46.
Proof. exact (@lem706885). Qed.
Lemma lem1634629 : (term184 = term46) = (term185 = term44).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term46). Qed.
Lemma lem1634630 : term185 = term44.
Proof. exact (EQ_MP (@lem1634629) (@lem1634628)). Qed.
Lemma lem1634631 : term44 = term185.
Proof. exact (SYM (@lem1634630)). Qed.
Lemma lem1634632 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1634633 : term33 = term186.
Proof. exact (MK_COMB (@lem1634632) (@lem1634631)). Qed.
Lemma lem1634634 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1634635 : term64 = term187.
Proof. exact (MK_COMB (@lem1634634) (@lem1634633)). Qed.
Lemma lem1634636 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1634637 : term188 = term189.
Proof. exact (MK_COMB (@lem1634636) (@lem1634635)). Qed.
Lemma lem1634638 : term99 = term99.
Proof. exact (eq_refl term99). Qed.
Lemma lem1634639 : term190 = term183.
Proof. exact (MK_COMB (@lem1634637) (@lem1634638)). Qed.
Lemma lem1634640 : term190 = term155.
Proof. exact (TRANS (@lem1634639) (@lem1634627)). Qed.
Lemma lem1634641 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1634642 : term191 = term192.
Proof. exact (MK_COMB (@lem1634641) (@lem1634640)). Qed.
Lemma lem1634643 (d : real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1634644 (d : real) : (term182 d) = (term127 d).
Proof. exact (MK_COMB (@lem1634642) (@lem1634643 d)). Qed.
Lemma lem1634645 (d : real) : (term181 d) = (term127 d).
Proof. exact (TRANS (@lem1634624 d) (@lem1634644 d)). Qed.
Lemma lem1634646 (d : real) : (term175 d) = (term127 d).
Proof. exact (TRANS (@lem1634623 d) (@lem1634645 d)). Qed.
Lemma lem1634647 (d : real) : (term174 d) = (term127 d).
Proof. exact (TRANS (@lem1634604 d) (@lem1634646 d)). Qed.
Lemma lem1634648 (d : real) : (term173 d) = (term127 d).
Proof. exact (TRANS (@lem1634603 d) (@lem1634647 d)). Qed.
Lemma lem1634649 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1634650 (d : real) : (term193 d) = (term129 d).
Proof. exact (MK_COMB (@lem1634649) (@lem1634648 d)). Qed.
Lemma lem1634651 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1634652 (d : real) : (term171 d) = (term130 d).
Proof. exact (MK_COMB (@lem1634650 d) (@lem1634651)). Qed.
Lemma lem1634653 (d : real) : (term170 d) = (term130 d).
Proof. exact (TRANS (@lem1634592 d) (@lem1634652 d)). Qed.
Lemma lem1634654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1634655 (d : real) : (term131 d) = (term132 d).
Proof. exact (MK_COMB (@lem1634654) (@lem1634591 d)). Qed.
Lemma lem1634656 (d : real) : (term169 d) = (term133 d).
Proof. exact (MK_COMB (@lem1634655 d) (@lem1634653 d)). Qed.
Lemma lem1634671 (d : real) : (term168 d) = (term133 d).
Proof. exact (TRANS (@lem1634570 d) (@lem1634656 d)). Qed.
Lemma lem1634675 (d : real) (h1 : term133 d) : term133 d.
Proof. exact (h1). Qed.
Lemma lem1634676 (d : real) (h1 : term133 d) : term130 d.
Proof. exact (proj2 (@lem1634675 d h1)). Qed.
Lemma lem1634677 (d : real) (h1 : term133 d) : term118 d.
Proof. exact (proj1 (@lem1634675 d h1)). Qed.
Lemma lem1634679 (n : nat) (m : nat) : (term134 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1634680 : term135 = term136.
Proof. exact (@lem1634679 (NUMERAL 0) term39). Qed.
Lemma lem1634681 : term137 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1634682 (h1 : term137 = (BIT1 0)) : term136 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1634683 : (term137 = (BIT1 0)) = (term136 = True).
Proof. exact (prop_ext (fun h1 : term137 = (BIT1 0) => @lem1634682 h1) (fun h1 : term136 = True => @lem1634681)). Qed.
Lemma lem1634684 : term136 = True.
Proof. exact (EQ_MP (@lem1634683) (@lem1634681)). Qed.
Lemma lem1634685 : term135 = True.
Proof. exact (TRANS (@lem1634680) (@lem1634684)). Qed.
Lemma lem1634686 : True = term135.
Proof. exact (SYM (@lem1634685)). Qed.
Lemma lem1634687 : term135.
Proof. exact (EQ_MP (@lem1634686) (@lem0)). Qed.
Lemma lem1634688 (d : real) (h1 : term133 d) : term138 d.
Proof. exact (conj (@lem1634687) (@lem1634676 d h1)). Qed.
Lemma lem1634690 (x : real) (y : real) : term139 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1634691 (d : real) : term140 d.
Proof. exact (@lem1634690 term99 (term127 d)). Qed.
Lemma lem1634692 (d : real) (h1 : term133 d) : term141 d.
Proof. exact (@lem1634691 d (@lem1634688 d h1)). Qed.
Lemma lem1634693 (d : real) : (term142 d) = (term127 d).
Proof. exact (@lem1483460 (term127 d)). Qed.
Lemma lem1634694 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1634695 (d : real) : (term143 d) = (term129 d).
Proof. exact (MK_COMB (@lem1634694) (@lem1634693 d)). Qed.
Lemma lem1634696 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1634697 (d : real) : (term141 d) = (term130 d).
Proof. exact (MK_COMB (@lem1634695 d) (@lem1634696)). Qed.
Lemma lem1634698 (d : real) (h1 : term133 d) : term130 d.
Proof. exact (EQ_MP (@lem1634697 d) (@lem1634692 d h1)). Qed.
Lemma lem1634700 (n : nat) (m : nat) : (term134 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1634701 : term135 = term136.
Proof. exact (@lem1634700 (NUMERAL 0) term39). Qed.
Lemma lem1634702 : term137 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1634703 (h1 : term137 = (BIT1 0)) : term136 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1634704 : (term137 = (BIT1 0)) = (term136 = True).
Proof. exact (prop_ext (fun h1 : term137 = (BIT1 0) => @lem1634703 h1) (fun h1 : term136 = True => @lem1634702)). Qed.
Lemma lem1634705 : term136 = True.
Proof. exact (EQ_MP (@lem1634704) (@lem1634702)). Qed.
Lemma lem1634706 : term135 = True.
Proof. exact (TRANS (@lem1634701) (@lem1634705)). Qed.
Lemma lem1634707 : True = term135.
Proof. exact (SYM (@lem1634706)). Qed.
Lemma lem1634708 : term135.
Proof. exact (EQ_MP (@lem1634707) (@lem0)). Qed.
Lemma lem1634709 (d : real) (h1 : term133 d) : term144 d.
Proof. exact (conj (@lem1634708) (@lem1634677 d h1)). Qed.
Lemma lem1634711 (x : real) (y : real) : term145 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1634712 (d : real) : term146 d.
Proof. exact (@lem1634711 term99 d). Qed.
Lemma lem1634713 (d : real) (h1 : term133 d) : term147 d.
Proof. exact (@lem1634712 d (@lem1634709 d h1)). Qed.
Lemma lem1634714 (d : real) : (term148 d) = d.
Proof. exact (@lem1483460 d). Qed.
Lemma lem1634715 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1634716 (d : real) : (term149 d) = (real_gt d).
Proof. exact (MK_COMB (@lem1634715) (@lem1634714 d)). Qed.
Lemma lem1634717 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1634718 (d : real) : (term147 d) = (term118 d).
Proof. exact (MK_COMB (@lem1634716 d) (@lem1634717)). Qed.
Lemma lem1634719 (d : real) (h1 : term133 d) : term118 d.
Proof. exact (EQ_MP (@lem1634718 d) (@lem1634713 d h1)). Qed.
Lemma lem1634720 (d : real) (h1 : term133 d) : term133 d.
Proof. exact (conj (@lem1634719 d h1) (@lem1634698 d h1)). Qed.
Lemma lem1634722 (x : real) (y : real) : term150 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1634723 (d : real) : term151 d.
Proof. exact (@lem1634722 d (term127 d)). Qed.
Lemma lem1634724 (d : real) (h1 : term133 d) : term152 d.
Proof. exact (@lem1634723 d (@lem1634720 d h1)). Qed.
Lemma lem1634725 (d : real) : (term153 d) = (term154 d).
Proof. exact (@lem1483442 term155 d). Qed.
Lemma lem1634727 (m : nat) : (term156 m) = term34.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1634728 : term157 = term34.
Proof. exact (@lem1634727 term39). Qed.
Lemma lem1634729 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1634730 : term158 = term159.
Proof. exact (MK_COMB (@lem1634729) (@lem1634728)). Qed.
Lemma lem1634731 (d : real) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem1634732 (d : real) : (term154 d) = (term160 d).
Proof. exact (MK_COMB (@lem1634730) (@lem1634731 d)). Qed.
Lemma lem1634733 (d : real) : (term153 d) = (term160 d).
Proof. exact (TRANS (@lem1634725 d) (@lem1634732 d)). Qed.
Lemma lem1634734 (d : real) : (term160 d) = term34.
Proof. exact (@lem1483446 d). Qed.
Lemma lem1634735 (d : real) : (term153 d) = term34.
Proof. exact (TRANS (@lem1634733 d) (@lem1634734 d)). Qed.
Lemma lem1634736 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1634737 (d : real) : (term161 d) = term162.
Proof. exact (MK_COMB (@lem1634736) (@lem1634735 d)). Qed.
Lemma lem1634738 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1634739 (d : real) : (term152 d) = term163.
Proof. exact (MK_COMB (@lem1634737 d) (@lem1634738)). Qed.
Lemma lem1634740 (d : real) (h1 : term133 d) : term163.
Proof. exact (EQ_MP (@lem1634739 d) (@lem1634724 d h1)). Qed.
Lemma lem1634742 (n : nat) (m : nat) : (term134 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1634743 : term163 = term164.
Proof. exact (@lem1634742 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1634744 : term164 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1634745 : term163 = False.
Proof. exact (TRANS (@lem1634743) (@lem1634744)). Qed.
Lemma lem1634746 (d : real) (h1 : term133 d) : False.
Proof. exact (EQ_MP (@lem1634745) (@lem1634740 d h1)). Qed.
Lemma lem1634748 (d : real) (h1 : term133 d) : term133 d.
Proof. exact (h1). Qed.
Lemma lem1634749 (d : real) (h1 : term133 d) : (term133 d) = False.
Proof. exact (prop_ext (fun h2 : term133 d => @lem1634746 d h1) (fun h2 : False => @lem1634748 d h1)). Qed.
Lemma lem1634750 (d : real) (h1 : term133 d) : False.
Proof. exact (EQ_MP (@lem1634749 d h1) (@lem1634748 d h1)). Qed.
Lemma lem1634751 (d : real) (h1 : term168 d) : term168 d.
Proof. exact (h1). Qed.
Lemma lem1634752 (d : real) (h1 : term168 d) : term133 d.
Proof. exact (EQ_MP (@lem1634671 d) (@lem1634751 d h1)). Qed.
Lemma lem1634753 (d : real) (h1 : term168 d) : (term133 d) = False.
Proof. exact (prop_ext (fun h2 : term133 d => @lem1634750 d h2) (fun h2 : False => @lem1634752 d h1)). Qed.
Lemma lem1634754 (d : real) (h1 : term168 d) : False.
Proof. exact (EQ_MP (@lem1634753 d h1) (@lem1634752 d h1)). Qed.
Lemma lem1634755 (d : real) : term194 d.
Proof. exact (fun h0 : term168 d => @lem1634754 d h0). Qed.
Lemma lem1634756 (d : real) : term195 d.
Proof. exact (@lem1386578 (term196 d)). Qed.
Lemma lem1634757 (d : real) : term196 d.
Proof. exact (@lem1634756 d (@lem1634755 d)). Qed.
Lemma lem1634758 (d : real) (h1 : term77 d) : term108 d.
Proof. exact (@lem1634757 d (@lem1634258 d h1)). Qed.
Lemma lem1634759 (d : real) (h1 : term77 d) : term102 d.
Proof. exact (@lem1634549 d (@lem1634258 d h1)). Qed.
Lemma lem1634760 (d : real) (h1 : term77 d) : term109 d.
Proof. exact (EQ_MP (@lem1634378 d) (@lem1634758 d h1)). Qed.
Lemma lem1634761 (d : real) (h1 : term77 d) : term103 d.
Proof. exact (EQ_MP (@lem1634320 d) (@lem1634759 d h1)). Qed.
Lemma lem1634762 (d : real) (h1 : term77 d) : term197 d.
Proof. exact (ex_intro (term198 d) term33 (@lem1634760 d h1)). Qed.
Lemma lem1634763 (d : real) (h1 : term77 d) : term199 d.
Proof. exact (ex_intro (term200 d) term33 (@lem1634761 d h1)). Qed.
Lemma lem1634764 (d : real) (h1 : term77 d) : term201 d.
Proof. exact (@lem1634264 d (@lem1634762 d h1)). Qed.
Lemma lem1634765 (d : real) (h1 : term77 d) : term202 d.
Proof. exact (@lem1634261 d (@lem1634763 d h1)). Qed.
Lemma lem1634766 (d : real) (h1 : term77 d) : term203 d.
Proof. exact (conj (@lem1634765 d h1) (@lem1634764 d h1)). Qed.
Lemma lem1634767 (d : real) (h1 : term77 d) : term204 d.
Proof. exact (ex_intro (term205 d) (term79 d) (@lem1634766 d h1)). Qed.
Lemma lem1634768 (d : real) : term206 d.
Proof. exact (fun h0 : term77 d => @lem1634767 d h0). Qed.
Lemma lem1634773 : term207.
Proof. exact (fun d : real => @lem1634768 d). Qed.
