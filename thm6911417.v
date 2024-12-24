Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6911417_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_MUL_RID_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338986_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
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
Require Import thm6910091_spec.
Require Import thm6910092_spec.
Lemma lem6910121 {A : Type'} (P : A -> Prop) (x : A) : term0 A P x.
Proof. exact (EQ_MP (@lem6910092 A P x) (@lem6910091 A P x)). Qed.
Lemma lem6910122 (P : real -> Prop) (x : real) : term1 P x.
Proof. exact (@lem6910121 real P x). Qed.
Lemma lem6910123 : term2.
Proof. exact (@lem6910122 term3 term4). Qed.
Lemma lem6910125 (p : Prop) : p = (term5 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6910126 : term6 = term7.
Proof. exact (@lem6910125 term6). Qed.
Lemma lem6910127 : term7 = term6.
Proof. exact (SYM (@lem6910126)). Qed.
Lemma lem6910128 (h1 : term8) : term8.
Proof. exact (h1). Qed.
Lemma lem6910131 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem6910132 : term10.
Proof. exact (fun h0 : term9 => @lem6910131 h0). Qed.
Lemma lem6910133 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem6910134 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem6910135 (h1 : term9) (h2 : term10) : term9.
Proof. exact (@lem6910133 h2 (@lem6910134 h1)). Qed.
Lemma lem6910136 (h1 : term9) : term11.
Proof. exact (fun h0 : term10 => @lem6910135 h1 h0). Qed.
Lemma lem6910137 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem6910138 (h1 : term9) (h2 : term10) : term9.
Proof. exact (@lem6910136 h1 (@lem6910137 h2)). Qed.
Lemma lem6910139 (h1 : term10) : term10.
Proof. exact (fun h0 : term9 => @lem6910138 h0 h1). Qed.
Lemma lem6910140 : term12.
Proof. exact (fun h0 : term10 => @lem6910139 h0). Qed.
Lemma lem6910143 : term10.
Proof. exact (@lem6910140 (@lem6910132)). Qed.
Lemma lem6910151 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term13 A P Q) = (term14 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem6910152 (P : real -> Prop) (Q : real -> Prop) : (term15 P Q) = (term16 P Q).
Proof. exact (@lem6910151 real P Q). Qed.
Lemma lem6910153 (x : real) : (term17 x) = (term18 x).
Proof. exact (@lem6910152 (term19 x) (term20 x)). Qed.
Lemma lem6910154 (x : real) (y : real) : (term21 x y) = ((real_mul x y) = y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem6910155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6910156 (x : real) (y : real) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem6910155) (@lem6910154 x y)). Qed.
Lemma lem6910157 (x : real) (y : real) : (term24 x y) = ((real_mul y x) = y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem6910158 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem6910156 x y) (@lem6910157 x y)). Qed.
Lemma lem6910159 (x : real) : (term27 x) = (term28 x).
Proof. exact (fun_ext (fun y : real => @lem6910158 x y)). Qed.
Lemma lem6910160 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910161 (x : real) : (term17 x) = (term29 x).
Proof. exact (MK_COMB (@lem6910160) (@lem6910159 x)). Qed.
Lemma lem6910162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6910163 (x : real) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem6910162) (@lem6910161 x)). Qed.
Lemma lem6910164 (x : real) (y : real) : (term21 x y) = ((real_mul x y) = y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem6910165 (x : real) : (term32 x) = (term19 x).
Proof. exact (fun_ext (fun y : real => @lem6910164 x y)). Qed.
Lemma lem6910166 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910167 (x : real) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem6910166) (@lem6910165 x)). Qed.
Lemma lem6910168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6910169 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem6910168) (@lem6910167 x)). Qed.
Lemma lem6910170 (x : real) (y : real) : (term24 x y) = ((real_mul y x) = y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem6910171 (x : real) : (term37 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem6910170 x y)). Qed.
Lemma lem6910172 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910173 (x : real) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem6910172) (@lem6910171 x)). Qed.
Lemma lem6910174 (x : real) : (term18 x) = (term40 x).
Proof. exact (MK_COMB (@lem6910169 x) (@lem6910173 x)). Qed.
Lemma lem6910175 (x : real) : ((term17 x) = (term18 x)) = ((term29 x) = (term40 x)).
Proof. exact (MK_COMB (@lem6910163 x) (@lem6910174 x)). Qed.
Lemma lem6910176 (x : real) : (term29 x) = (term40 x).
Proof. exact (EQ_MP (@lem6910175 x) (@lem6910153 x)). Qed.
Lemma lem6910187 : term3 = term41.
Proof. exact (fun_ext (fun x : real => @lem6910176 x)). Qed.
Lemma lem6910188 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem6910189 (y : real) : (term42 y) = (term43 y).
Proof. exact (MK_COMB (@lem6910187) (@lem6910188 y)). Qed.
Lemma lem6910190 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6910191 (y : real) : (term44 y) = (term45 y).
Proof. exact (MK_COMB (@lem6910190) (@lem6910189 y)). Qed.
Lemma lem6910192 (y : real) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6910193 (y : real) : ((term42 y) = (y = term4)) = ((term43 y) = (y = term4)).
Proof. exact (MK_COMB (@lem6910191 y) (@lem6910192 y)). Qed.
Lemma lem6910194 : term46 = term47.
Proof. exact (fun_ext (fun y : real => @lem6910193 y)). Qed.
Lemma lem6910195 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910196 : term6 = term48.
Proof. exact (MK_COMB (@lem6910195) (@lem6910194)). Qed.
Lemma lem6910201 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6910202 : term8 = term49.
Proof. exact (MK_COMB (@lem6910201) (@lem6910196)). Qed.
Lemma lem6910203 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6910204 : term50 = term51.
Proof. exact (MK_COMB (@lem6910203) (@lem6910202)). Qed.
Lemma lem6910212 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6910213 : term52 = term53.
Proof. exact (@lem6910212 term54). Qed.
Lemma lem6910218 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem6910219 : term56 = term57.
Proof. exact (MK_COMB (@lem6910218) (@lem6910213)). Qed.
Lemma lem6910222 : term9 = term58.
Proof. exact (MK_COMB (@lem6910204) (@lem6910219)). Qed.
Lemma lem6910225 (y : real) : (term43 y) = (term40 y).
Proof. exact (eq_refl (term43 y)). Qed.
Lemma lem6910226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6910227 (y : real) : (term45 y) = (term59 y).
Proof. exact (MK_COMB (@lem6910226) (@lem6910225 y)). Qed.
Lemma lem6910228 (y : real) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6910229 (y : real) : ((term43 y) = (y = term4)) = ((term40 y) = (y = term4)).
Proof. exact (MK_COMB (@lem6910227 y) (@lem6910228 y)). Qed.
Lemma lem6910230 : term47 = term60.
Proof. exact (fun_ext (fun y : real => @lem6910229 y)). Qed.
Lemma lem6910231 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910232 : term48 = term61.
Proof. exact (MK_COMB (@lem6910231) (@lem6910230)). Qed.
Lemma lem6910233 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6910234 : term49 = term62.
Proof. exact (MK_COMB (@lem6910233) (@lem6910232)). Qed.
Lemma lem6910235 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6910236 : term51 = term63.
Proof. exact (MK_COMB (@lem6910235) (@lem6910234)). Qed.
Lemma lem6910237 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem6910238 : term58 = term64.
Proof. exact (MK_COMB (@lem6910236) (@lem6910237)). Qed.
Lemma lem6910241 : term9 = term64.
Proof. exact (TRANS (@lem6910222) (@lem6910238)). Qed.
Lemma lem6910242 (x : real) : ((term65 x) = x) = ((term65 x) = x).
Proof. exact (eq_refl ((term65 x) = x)). Qed.
Lemma lem6910243 : term66 = term66.
Proof. exact (fun_ext (fun x : real => @lem6910242 x)). Qed.
Lemma lem6910244 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910245 : term54 = term54.
Proof. exact (MK_COMB (@lem6910244) (@lem6910243)). Qed.
Lemma lem6910246 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6910247 : term53 = term53.
Proof. exact (MK_COMB (@lem6910246) (@lem6910245)). Qed.
Lemma lem6910248 (x : real) : ((term67 x) = x) = ((term67 x) = x).
Proof. exact (eq_refl ((term67 x) = x)). Qed.
Lemma lem6910249 : term68 = term68.
Proof. exact (fun_ext (fun x : real => @lem6910248 x)). Qed.
Lemma lem6910250 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910251 : term69 = term69.
Proof. exact (MK_COMB (@lem6910250) (@lem6910249)). Qed.
Lemma lem6910252 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6910253 : term55 = term55.
Proof. exact (MK_COMB (@lem6910252) (@lem6910251)). Qed.
Lemma lem6910254 : term57 = term57.
Proof. exact (MK_COMB (@lem6910253) (@lem6910247)). Qed.
Lemma lem6910255 (y : real) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6910256 (y : real) (y' : real) : ((real_mul y' y) = y') = ((real_mul y' y) = y').
Proof. exact (eq_refl ((real_mul y' y) = y')). Qed.
Lemma lem6910257 (y : real) : (term20 y) = (term20 y).
Proof. exact (fun_ext (fun y' : real => @lem6910256 y y')). Qed.
Lemma lem6910258 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910259 (y : real) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem6910258) (@lem6910257 y)). Qed.
Lemma lem6910260 (y : real) (y' : real) : ((real_mul y y') = y') = ((real_mul y y') = y').
Proof. exact (eq_refl ((real_mul y y') = y')). Qed.
Lemma lem6910261 (y : real) : (term19 y) = (term19 y).
Proof. exact (fun_ext (fun y' : real => @lem6910260 y y')). Qed.
Lemma lem6910262 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910263 (y : real) : (term34 y) = (term34 y).
Proof. exact (MK_COMB (@lem6910262) (@lem6910261 y)). Qed.
Lemma lem6910264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6910265 (y : real) : (term36 y) = (term36 y).
Proof. exact (MK_COMB (@lem6910264) (@lem6910263 y)). Qed.
Lemma lem6910266 (y : real) : (term40 y) = (term40 y).
Proof. exact (MK_COMB (@lem6910265 y) (@lem6910259 y)). Qed.
Lemma lem6910267 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6910268 (y : real) : (term59 y) = (term59 y).
Proof. exact (MK_COMB (@lem6910267) (@lem6910266 y)). Qed.
Lemma lem6910269 (y : real) : ((term40 y) = (y = term4)) = ((term40 y) = (y = term4)).
Proof. exact (MK_COMB (@lem6910268 y) (@lem6910255 y)). Qed.
Lemma lem6910270 : term60 = term60.
Proof. exact (fun_ext (fun y : real => @lem6910269 y)). Qed.
Lemma lem6910271 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910272 : term61 = term61.
Proof. exact (MK_COMB (@lem6910271) (@lem6910270)). Qed.
Lemma lem6910273 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6910274 : term62 = term62.
Proof. exact (MK_COMB (@lem6910273) (@lem6910272)). Qed.
Lemma lem6910275 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6910276 : term63 = term63.
Proof. exact (MK_COMB (@lem6910275) (@lem6910274)). Qed.
Lemma lem6910277 : term64 = term64.
Proof. exact (MK_COMB (@lem6910276) (@lem6910254)). Qed.
Lemma lem6910316 : term9 = term64.
Proof. exact (TRANS (@lem6910241) (@lem6910277)). Qed.
Lemma lem6910317 : term64 = term9.
Proof. exact (SYM (@lem6910316)). Qed.
Lemma lem6910318 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem6910319 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem6910320 (h1 : term54) : term54.
Proof. exact (h1). Qed.
Lemma lem6910322 (y : real) (y' : real) : ((real_mul y y') = y') = ((real_mul y y') = y').
Proof. exact (eq_refl ((real_mul y y') = y')). Qed.
Lemma lem6910323 (P : real -> Prop) : (term70 P) = (term71 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem6910324 (y : real) : (term72 y) = (term73 y).
Proof. exact (@lem6910323 (term19 y)). Qed.
Lemma lem6910325 (y : real) (y' : real) : (term21 y y') = ((real_mul y y') = y').
Proof. exact (eq_refl (term21 y y')). Qed.
Lemma lem6910326 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6910328 (y : real) (y' : real) : (term74 y y') = (term75 y y').
Proof. exact (MK_COMB (@lem6910326) (@lem6910325 y y')). Qed.
Lemma lem6910329 (y : real) : (term76 y) = (term77 y).
Proof. exact (fun_ext (fun y' : real => @lem6910328 y y')). Qed.
Lemma lem6910330 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910331 (y : real) : (term73 y) = (term78 y).
Proof. exact (MK_COMB (@lem6910330) (@lem6910329 y)). Qed.
Lemma lem6910332 (y : real) : (term72 y) = (term78 y).
Proof. exact (TRANS (@lem6910324 y) (@lem6910331 y)). Qed.
Lemma lem6910333 (y : real) : (term19 y) = (term19 y).
Proof. exact (fun_ext (fun y' : real => @lem6910322 y y')). Qed.
Lemma lem6910334 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910335 (y : real) : (term34 y) = (term34 y).
Proof. exact (MK_COMB (@lem6910334) (@lem6910333 y)). Qed.
Lemma lem6910337 (y : real) (y' : real) : ((real_mul y' y) = y') = ((real_mul y' y) = y').
Proof. exact (eq_refl ((real_mul y' y) = y')). Qed.
Lemma lem6910338 (P : real -> Prop) : (term70 P) = (term71 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem6910339 (y : real) : (term79 y) = (term80 y).
Proof. exact (@lem6910338 (term20 y)). Qed.
Lemma lem6910340 (y : real) (y' : real) : (term24 y y') = ((real_mul y' y) = y').
Proof. exact (eq_refl (term24 y y')). Qed.
Lemma lem6910341 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6910343 (y : real) (y' : real) : (term81 y y') = (term82 y y').
Proof. exact (MK_COMB (@lem6910341) (@lem6910340 y y')). Qed.
Lemma lem6910344 (y : real) : (term83 y) = (term84 y).
Proof. exact (fun_ext (fun y' : real => @lem6910343 y y')). Qed.
Lemma lem6910345 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910346 (y : real) : (term80 y) = (term85 y).
Proof. exact (MK_COMB (@lem6910345) (@lem6910344 y)). Qed.
Lemma lem6910347 (y : real) : (term79 y) = (term85 y).
Proof. exact (TRANS (@lem6910339 y) (@lem6910346 y)). Qed.
Lemma lem6910348 (y : real) : (term20 y) = (term20 y).
Proof. exact (fun_ext (fun y' : real => @lem6910337 y y')). Qed.
Lemma lem6910349 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910350 (y : real) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem6910349) (@lem6910348 y)). Qed.
Lemma lem6910351 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6910352 (y : real) : (term86 y) = (term87 y).
Proof. exact (MK_COMB (@lem6910351) (@lem6910332 y)). Qed.
Lemma lem6910353 (y : real) : (term88 y) = (term89 y).
Proof. exact (MK_COMB (@lem6910352 y) (@lem6910347 y)). Qed.
Lemma lem6910354 (y : real) : (term90 y) = (term88 y).
Proof. exact (@lem17045 (term34 y) (term39 y)). Qed.
Lemma lem6910355 (y : real) : (term90 y) = (term89 y).
Proof. exact (TRANS (@lem6910354 y) (@lem6910353 y)). Qed.
Lemma lem6910356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6910357 (y : real) : (term36 y) = (term36 y).
Proof. exact (MK_COMB (@lem6910356) (@lem6910335 y)). Qed.
Lemma lem6910358 (y : real) : (term40 y) = (term40 y).
Proof. exact (MK_COMB (@lem6910357 y) (@lem6910350 y)). Qed.
Lemma lem6910359 (y : real) : (term91 y) = (term91 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem6910360 (y : real) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6910361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6910362 (y : real) : (term92 y) = (term93 y).
Proof. exact (MK_COMB (@lem6910361) (@lem6910355 y)). Qed.
Lemma lem6910363 (y : real) : (term94 y) = (term95 y).
Proof. exact (MK_COMB (@lem6910362 y) (@lem6910360 y)). Qed.
Lemma lem6910364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6910365 (y : real) : (term96 y) = (term96 y).
Proof. exact (MK_COMB (@lem6910364) (@lem6910358 y)). Qed.
Lemma lem6910366 (y : real) : (term97 y) = (term97 y).
Proof. exact (MK_COMB (@lem6910365 y) (@lem6910359 y)). Qed.
Lemma lem6910367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6910368 (y : real) : (term98 y) = (term98 y).
Proof. exact (MK_COMB (@lem6910367) (@lem6910366 y)). Qed.
Lemma lem6910369 (y : real) : (term99 y) = (term100 y).
Proof. exact (MK_COMB (@lem6910368 y) (@lem6910363 y)). Qed.
Lemma lem6910370 (y : real) : (term101 y) = (term99 y).
Proof. exact (@lem17646 (term40 y) (y = term4)). Qed.
Lemma lem6910371 (y : real) : (term101 y) = (term100 y).
Proof. exact (TRANS (@lem6910370 y) (@lem6910369 y)). Qed.
Lemma lem6910372 (P : real -> Prop) : (term70 P) = (term71 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem6910373 : term62 = term102.
Proof. exact (@lem6910372 term60). Qed.
Lemma lem6910374 (y : real) : (term103 y) = ((term40 y) = (y = term4)).
Proof. exact (eq_refl (term103 y)). Qed.
Lemma lem6910375 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6910376 (y : real) : (term104 y) = (term101 y).
Proof. exact (MK_COMB (@lem6910375) (@lem6910374 y)). Qed.
Lemma lem6910377 (y : real) : (term104 y) = (term100 y).
Proof. exact (TRANS (@lem6910376 y) (@lem6910371 y)). Qed.
Lemma lem6910378 : term105 = term106.
Proof. exact (fun_ext (fun y : real => @lem6910377 y)). Qed.
Lemma lem6910379 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910380 : term102 = term107.
Proof. exact (MK_COMB (@lem6910379) (@lem6910378)). Qed.
Lemma lem6910381 : term62 = term107.
Proof. exact (TRANS (@lem6910373) (@lem6910380)). Qed.
Lemma lem6910383 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem6910384 (P : real -> Prop) (Q : real -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem6910383 real P Q). Qed.
Lemma lem6910385 : term112 = term113.
Proof. exact (@lem6910384 term114 term115). Qed.
Lemma lem6910386 (y : real) : (term116 y) = (term97 y).
Proof. exact (eq_refl (term116 y)). Qed.
Lemma lem6910387 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6910388 (y : real) : (term117 y) = (term98 y).
Proof. exact (MK_COMB (@lem6910387) (@lem6910386 y)). Qed.
Lemma lem6910389 (y : real) : (term118 y) = (term95 y).
Proof. exact (eq_refl (term118 y)). Qed.
Lemma lem6910390 (y : real) : (term119 y) = (term100 y).
Proof. exact (MK_COMB (@lem6910388 y) (@lem6910389 y)). Qed.
Lemma lem6910391 : term120 = term106.
Proof. exact (fun_ext (fun y : real => @lem6910390 y)). Qed.
Lemma lem6910392 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910393 : term112 = term107.
Proof. exact (MK_COMB (@lem6910392) (@lem6910391)). Qed.
Lemma lem6910394 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6910395 : term121 = term122.
Proof. exact (MK_COMB (@lem6910394) (@lem6910393)). Qed.
Lemma lem6910396 (y : real) : (term116 y) = (term97 y).
Proof. exact (eq_refl (term116 y)). Qed.
Lemma lem6910397 : term123 = term114.
Proof. exact (fun_ext (fun y : real => @lem6910396 y)). Qed.
Lemma lem6910398 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910399 : term124 = term125.
Proof. exact (MK_COMB (@lem6910398) (@lem6910397)). Qed.
Lemma lem6910400 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6910401 : term126 = term127.
Proof. exact (MK_COMB (@lem6910400) (@lem6910399)). Qed.
Lemma lem6910402 (y : real) : (term118 y) = (term95 y).
Proof. exact (eq_refl (term118 y)). Qed.
Lemma lem6910403 : term128 = term115.
Proof. exact (fun_ext (fun y : real => @lem6910402 y)). Qed.
Lemma lem6910404 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910405 : term129 = term130.
Proof. exact (MK_COMB (@lem6910404) (@lem6910403)). Qed.
Lemma lem6910406 : term113 = term131.
Proof. exact (MK_COMB (@lem6910401) (@lem6910405)). Qed.
Lemma lem6910407 : (term112 = term113) = (term107 = term131).
Proof. exact (MK_COMB (@lem6910395) (@lem6910406)). Qed.
Lemma lem6910408 : term107 = term131.
Proof. exact (EQ_MP (@lem6910407) (@lem6910385)). Qed.
Lemma lem6910522 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6910523 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term110 P Q).
Proof. exact (@lem6910522 real P Q). Qed.
Lemma lem6910524 (y : real) : (term132 y) = (term133 y).
Proof. exact (@lem6910523 (term77 y) (term84 y)). Qed.
Lemma lem6910525 (y : real) (y' : real) : (term134 y y') = (term75 y y').
Proof. exact (eq_refl (term134 y y')). Qed.
Lemma lem6910526 (y : real) : (term135 y) = (term77 y).
Proof. exact (fun_ext (fun y' : real => @lem6910525 y y')). Qed.
Lemma lem6910527 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910528 (y : real) : (term136 y) = (term78 y).
Proof. exact (MK_COMB (@lem6910527) (@lem6910526 y)). Qed.
Lemma lem6910529 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6910530 (y : real) : (term137 y) = (term87 y).
Proof. exact (MK_COMB (@lem6910529) (@lem6910528 y)). Qed.
Lemma lem6910531 (y : real) (y' : real) : (term138 y y') = (term82 y y').
Proof. exact (eq_refl (term138 y y')). Qed.
Lemma lem6910532 (y : real) : (term139 y) = (term84 y).
Proof. exact (fun_ext (fun y' : real => @lem6910531 y y')). Qed.
Lemma lem6910533 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910534 (y : real) : (term140 y) = (term85 y).
Proof. exact (MK_COMB (@lem6910533) (@lem6910532 y)). Qed.
Lemma lem6910535 (y : real) : (term132 y) = (term89 y).
Proof. exact (MK_COMB (@lem6910530 y) (@lem6910534 y)). Qed.
Lemma lem6910536 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6910537 (y : real) : (term141 y) = (term142 y).
Proof. exact (MK_COMB (@lem6910536) (@lem6910535 y)). Qed.
Lemma lem6910538 (y : real) (y' : real) : (term134 y y') = (term75 y y').
Proof. exact (eq_refl (term134 y y')). Qed.
Lemma lem6910539 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6910540 (y : real) (y' : real) : (term143 y y') = (term144 y y').
Proof. exact (MK_COMB (@lem6910539) (@lem6910538 y y')). Qed.
Lemma lem6910541 (y : real) (y' : real) : (term138 y y') = (term82 y y').
Proof. exact (eq_refl (term138 y y')). Qed.
Lemma lem6910542 (y : real) (y' : real) : (term145 y y') = (term146 y y').
Proof. exact (MK_COMB (@lem6910540 y y') (@lem6910541 y y')). Qed.
Lemma lem6910543 (y : real) : (term147 y) = (term148 y).
Proof. exact (fun_ext (fun y' : real => @lem6910542 y y')). Qed.
Lemma lem6910544 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910545 (y : real) : (term133 y) = (term149 y).
Proof. exact (MK_COMB (@lem6910544) (@lem6910543 y)). Qed.
Lemma lem6910546 (y : real) : ((term132 y) = (term133 y)) = ((term89 y) = (term149 y)).
Proof. exact (MK_COMB (@lem6910537 y) (@lem6910545 y)). Qed.
Lemma lem6910547 (y : real) : (term89 y) = (term149 y).
Proof. exact (EQ_MP (@lem6910546 y) (@lem6910524 y)). Qed.
Lemma lem6910548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6910549 (y : real) : (term93 y) = (term150 y).
Proof. exact (MK_COMB (@lem6910548) (@lem6910547 y)). Qed.
Lemma lem6910550 (y : real) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6910551 (y : real) : (term95 y) = (term151 y).
Proof. exact (MK_COMB (@lem6910549 y) (@lem6910550 y)). Qed.
Lemma lem6910553 {A : Type'} (P : A -> Prop) (Q : Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem6910554 (P : real -> Prop) (Q : Prop) : (term154 P Q) = (term155 P Q).
Proof. exact (@lem6910553 real P Q). Qed.
Lemma lem6910555 (y : real) : (term156 y) = (term157 y).
Proof. exact (@lem6910554 (term148 y) (y = term4)). Qed.
Lemma lem6910556 (y : real) (y' : real) : (term158 y y') = (term146 y y').
Proof. exact (eq_refl (term158 y y')). Qed.
Lemma lem6910557 (y : real) : (term159 y) = (term148 y).
Proof. exact (fun_ext (fun y' : real => @lem6910556 y y')). Qed.
Lemma lem6910558 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910559 (y : real) : (term160 y) = (term149 y).
Proof. exact (MK_COMB (@lem6910558) (@lem6910557 y)). Qed.
Lemma lem6910560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6910561 (y : real) : (term161 y) = (term150 y).
Proof. exact (MK_COMB (@lem6910560) (@lem6910559 y)). Qed.
Lemma lem6910562 (y : real) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6910563 (y : real) : (term156 y) = (term151 y).
Proof. exact (MK_COMB (@lem6910561 y) (@lem6910562 y)). Qed.
Lemma lem6910564 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6910565 (y : real) : (term162 y) = (term163 y).
Proof. exact (MK_COMB (@lem6910564) (@lem6910563 y)). Qed.
Lemma lem6910566 (y : real) (y' : real) : (term158 y y') = (term146 y y').
Proof. exact (eq_refl (term158 y y')). Qed.
Lemma lem6910567 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6910568 (y : real) (y' : real) : (term164 y y') = (term165 y y').
Proof. exact (MK_COMB (@lem6910567) (@lem6910566 y y')). Qed.
Lemma lem6910569 (y : real) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem6910570 (y' : real) (y : real) : (term166 y' y) = (term167 y' y).
Proof. exact (MK_COMB (@lem6910568 y y') (@lem6910569 y)). Qed.
Lemma lem6910571 (y : real) : (term168 y) = (term169 y).
Proof. exact (fun_ext (fun y' : real => @lem6910570 y' y)). Qed.
Lemma lem6910572 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910573 (y : real) : (term157 y) = (term170 y).
Proof. exact (MK_COMB (@lem6910572) (@lem6910571 y)). Qed.
Lemma lem6910574 (y : real) : ((term156 y) = (term157 y)) = ((term151 y) = (term170 y)).
Proof. exact (MK_COMB (@lem6910565 y) (@lem6910573 y)). Qed.
Lemma lem6910575 (y : real) : (term151 y) = (term170 y).
Proof. exact (EQ_MP (@lem6910574 y) (@lem6910555 y)). Qed.
Lemma lem6910576 (y : real) : (term95 y) = (term170 y).
Proof. exact (TRANS (@lem6910551 y) (@lem6910575 y)). Qed.
Lemma lem6910577 : term115 = term171.
Proof. exact (fun_ext (fun y : real => @lem6910576 y)). Qed.
Lemma lem6910578 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910579 : term130 = term172.
Proof. exact (MK_COMB (@lem6910578) (@lem6910577)). Qed.
Lemma lem6910580 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem6910581 : term131 = term173.
Proof. exact (MK_COMB (@lem6910580) (@lem6910579)). Qed.
Lemma lem6910583 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6910584 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term110 P Q).
Proof. exact (@lem6910583 real P Q). Qed.
Lemma lem6910585 : term174 = term175.
Proof. exact (@lem6910584 term114 term171). Qed.
Lemma lem6910586 (y : real) : (term116 y) = (term97 y).
Proof. exact (eq_refl (term116 y)). Qed.
Lemma lem6910587 : term123 = term114.
Proof. exact (fun_ext (fun y : real => @lem6910586 y)). Qed.
Lemma lem6910588 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910589 : term124 = term125.
Proof. exact (MK_COMB (@lem6910588) (@lem6910587)). Qed.
Lemma lem6910590 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6910591 : term126 = term127.
Proof. exact (MK_COMB (@lem6910590) (@lem6910589)). Qed.
Lemma lem6910592 (y : real) : (term176 y) = (term170 y).
Proof. exact (eq_refl (term176 y)). Qed.
Lemma lem6910593 : term177 = term171.
Proof. exact (fun_ext (fun y : real => @lem6910592 y)). Qed.
Lemma lem6910594 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910595 : term178 = term172.
Proof. exact (MK_COMB (@lem6910594) (@lem6910593)). Qed.
Lemma lem6910596 : term174 = term173.
Proof. exact (MK_COMB (@lem6910591) (@lem6910595)). Qed.
Lemma lem6910597 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6910598 : term179 = term180.
Proof. exact (MK_COMB (@lem6910597) (@lem6910596)). Qed.
Lemma lem6910599 (y : real) : (term116 y) = (term97 y).
Proof. exact (eq_refl (term116 y)). Qed.
Lemma lem6910600 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6910601 (y : real) : (term117 y) = (term98 y).
Proof. exact (MK_COMB (@lem6910600) (@lem6910599 y)). Qed.
Lemma lem6910602 (y : real) : (term176 y) = (term170 y).
Proof. exact (eq_refl (term176 y)). Qed.
Lemma lem6910603 (y : real) : (term181 y) = (term182 y).
Proof. exact (MK_COMB (@lem6910601 y) (@lem6910602 y)). Qed.
Lemma lem6910604 : term183 = term184.
Proof. exact (fun_ext (fun y : real => @lem6910603 y)). Qed.
Lemma lem6910605 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910606 : term175 = term185.
Proof. exact (MK_COMB (@lem6910605) (@lem6910604)). Qed.
Lemma lem6910607 : (term174 = term175) = (term173 = term185).
Proof. exact (MK_COMB (@lem6910598) (@lem6910606)). Qed.
Lemma lem6910608 : term173 = term185.
Proof. exact (EQ_MP (@lem6910607) (@lem6910585)). Qed.
Lemma lem6910610 {A : Type'} (P : Prop) (Q : A -> Prop) : (term186 A P Q) = (term187 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6910611 (P : Prop) (Q : real -> Prop) : (term188 P Q) = (term189 P Q).
Proof. exact (@lem6910610 real P Q). Qed.
Lemma lem6910612 (y : real) : (term190 y) = (term191 y).
Proof. exact (@lem6910611 (term97 y) (term169 y)). Qed.
Lemma lem6910613 (y' : real) (y : real) : (term192 y y') = (term167 y' y).
Proof. exact (eq_refl (term192 y y')). Qed.
Lemma lem6910614 (y : real) : (term193 y) = (term169 y).
Proof. exact (fun_ext (fun y' : real => @lem6910613 y' y)). Qed.
Lemma lem6910615 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910616 (y : real) : (term194 y) = (term170 y).
Proof. exact (MK_COMB (@lem6910615) (@lem6910614 y)). Qed.
Lemma lem6910617 (y : real) : (term98 y) = (term98 y).
Proof. exact (eq_refl (term98 y)). Qed.
Lemma lem6910618 (y : real) : (term190 y) = (term182 y).
Proof. exact (MK_COMB (@lem6910617 y) (@lem6910616 y)). Qed.
Lemma lem6910619 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6910620 (y : real) : (term195 y) = (term196 y).
Proof. exact (MK_COMB (@lem6910619) (@lem6910618 y)). Qed.
Lemma lem6910621 (y' : real) (y : real) : (term192 y y') = (term167 y' y).
Proof. exact (eq_refl (term192 y y')). Qed.
Lemma lem6910622 (y : real) : (term98 y) = (term98 y).
Proof. exact (eq_refl (term98 y)). Qed.
Lemma lem6910623 (y' : real) (y : real) : (term197 y y') = (term198 y' y).
Proof. exact (MK_COMB (@lem6910622 y) (@lem6910621 y' y)). Qed.
Lemma lem6910624 (y : real) : (term199 y) = (term200 y).
Proof. exact (fun_ext (fun y' : real => @lem6910623 y' y)). Qed.
Lemma lem6910625 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910626 (y : real) : (term191 y) = (term201 y).
Proof. exact (MK_COMB (@lem6910625) (@lem6910624 y)). Qed.
Lemma lem6910627 (y : real) : ((term190 y) = (term191 y)) = ((term182 y) = (term201 y)).
Proof. exact (MK_COMB (@lem6910620 y) (@lem6910626 y)). Qed.
Lemma lem6910628 (y : real) : (term182 y) = (term201 y).
Proof. exact (EQ_MP (@lem6910627 y) (@lem6910612 y)). Qed.
Lemma lem6910629 : term184 = term202.
Proof. exact (fun_ext (fun y : real => @lem6910628 y)). Qed.
Lemma lem6910630 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem6910631 : term185 = term203.
Proof. exact (MK_COMB (@lem6910630) (@lem6910629)). Qed.
Lemma lem6910632 : term173 = term203.
Proof. exact (TRANS (@lem6910608) (@lem6910631)). Qed.
Lemma lem6910633 : term131 = term203.
Proof. exact (TRANS (@lem6910581) (@lem6910632)). Qed.
Lemma lem6910634 : term107 = term203.
Proof. exact (TRANS (@lem6910408) (@lem6910633)). Qed.
Lemma lem6910635 : term62 = term203.
Proof. exact (TRANS (@lem6910381) (@lem6910634)). Qed.
Lemma lem6910636 (h1 : term62) : term203.
Proof. exact (EQ_MP (@lem6910635) (@lem6910318 h1)). Qed.
Lemma lem6910637 (x : real) : ((term67 x) = x) = ((term67 x) = x).
Proof. exact (eq_refl ((term67 x) = x)). Qed.
Lemma lem6910638 : term68 = term68.
Proof. exact (fun_ext (fun x : real => @lem6910637 x)). Qed.
Lemma lem6910639 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910648 : term69 = term69.
Proof. exact (MK_COMB (@lem6910639) (@lem6910638)). Qed.
Lemma lem6910649 (h1 : term69) : term69.
Proof. exact (EQ_MP (@lem6910648) (@lem6910319 h1)). Qed.
Lemma lem6910650 (x : real) : ((term65 x) = x) = ((term65 x) = x).
Proof. exact (eq_refl ((term65 x) = x)). Qed.
Lemma lem6910651 : term66 = term66.
Proof. exact (fun_ext (fun x : real => @lem6910650 x)). Qed.
Lemma lem6910652 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910661 : term54 = term54.
Proof. exact (MK_COMB (@lem6910652) (@lem6910651)). Qed.
Lemma lem6910662 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem6910661) (@lem6910320 h1)). Qed.
Lemma lem6910663 (y : real) (h1 : term201 y) : term201 y.
Proof. exact (h1). Qed.
Lemma lem6910664 (y' : real) (y : real) (h1 : term198 y' y) : term198 y' y.
Proof. exact (h1). Qed.
Lemma lem6910679 (x : real) : ((term67 x) = x) = ((term67 x) = x).
Proof. exact (eq_refl ((term67 x) = x)). Qed.
Lemma lem6910680 : term68 = term68.
Proof. exact (fun_ext (fun x : real => @lem6910679 x)). Qed.
Lemma lem6910681 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910682 : term69 = term69.
Proof. exact (MK_COMB (@lem6910681) (@lem6910680)). Qed.
Lemma lem6910683 (h1 : term69) : term69.
Proof. exact (EQ_MP (@lem6910682) (@lem6910649 h1)). Qed.
Lemma lem6910698 (x : real) : ((term65 x) = x) = ((term65 x) = x).
Proof. exact (eq_refl ((term65 x) = x)). Qed.
Lemma lem6910699 : term66 = term66.
Proof. exact (fun_ext (fun x : real => @lem6910698 x)). Qed.
Lemma lem6910700 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910701 : term54 = term54.
Proof. exact (MK_COMB (@lem6910700) (@lem6910699)). Qed.
Lemma lem6910702 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem6910701) (@lem6910662 h1)). Qed.
Lemma lem6910741 (y' : real) (y : real) : (term167 y' y) = (term167 y' y).
Proof. exact (eq_refl (term167 y' y)). Qed.
Lemma lem6910754 (y : real) : (term91 y) = (term91 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem6910763 (y : real) (y' : real) : ((real_mul y' y) = y') = ((real_mul y' y) = y').
Proof. exact (eq_refl ((real_mul y' y) = y')). Qed.
Lemma lem6910764 (y : real) : (term20 y) = (term20 y).
Proof. exact (fun_ext (fun y' : real => @lem6910763 y y')). Qed.
Lemma lem6910765 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910766 (y : real) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem6910765) (@lem6910764 y)). Qed.
Lemma lem6910775 (y : real) (y' : real) : ((real_mul y y') = y') = ((real_mul y y') = y').
Proof. exact (eq_refl ((real_mul y y') = y')). Qed.
Lemma lem6910776 (y : real) : (term19 y) = (term19 y).
Proof. exact (fun_ext (fun y' : real => @lem6910775 y y')). Qed.
Lemma lem6910777 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910778 (y : real) : (term34 y) = (term34 y).
Proof. exact (MK_COMB (@lem6910777) (@lem6910776 y)). Qed.
Lemma lem6910779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6910780 (y : real) : (term36 y) = (term36 y).
Proof. exact (MK_COMB (@lem6910779) (@lem6910778 y)). Qed.
Lemma lem6910781 (y : real) : (term40 y) = (term40 y).
Proof. exact (MK_COMB (@lem6910780 y) (@lem6910766 y)). Qed.
Lemma lem6910782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6910783 (y : real) : (term96 y) = (term96 y).
Proof. exact (MK_COMB (@lem6910782) (@lem6910781 y)). Qed.
Lemma lem6910784 (y : real) : (term97 y) = (term97 y).
Proof. exact (MK_COMB (@lem6910783 y) (@lem6910754 y)). Qed.
Lemma lem6910785 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6910786 (y : real) : (term98 y) = (term98 y).
Proof. exact (MK_COMB (@lem6910785) (@lem6910784 y)). Qed.
Lemma lem6910787 (y' : real) (y : real) : (term198 y' y) = (term198 y' y).
Proof. exact (MK_COMB (@lem6910786 y) (@lem6910741 y' y)). Qed.
Lemma lem6910788 (y' : real) (y : real) (h1 : term198 y' y) : term198 y' y.
Proof. exact (EQ_MP (@lem6910787 y' y) (@lem6910664 y' y h1)). Qed.
Lemma lem6910789 (y : real) (h1 : term97 y) : term97 y.
Proof. exact (h1). Qed.
Lemma lem6910790 (y' : real) (y : real) (h1 : term167 y' y) : term167 y' y.
Proof. exact (h1). Qed.
Lemma lem6910792 (y : real) (h1 : term97 y) : term40 y.
Proof. exact (proj1 (@lem6910789 y h1)). Qed.
Lemma lem6910793 (y : real) (h1 : term97 y) : term39 y.
Proof. exact (proj2 (@lem6910792 y h1)). Qed.
Lemma lem6910796 (y' : real) (y : real) (h1 : term167 y' y) : term146 y y'.
Proof. exact (proj1 (@lem6910790 y' y h1)). Qed.
Lemma lem6910807 (x : real) : ((term65 x) = x) = ((term65 x) = x).
Proof. exact (eq_refl ((term65 x) = x)). Qed.
Lemma lem6910808 : term66 = term66.
Proof. exact (fun_ext (fun x : real => @lem6910807 x)). Qed.
Lemma lem6910809 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910811 : term54 = term54.
Proof. exact (MK_COMB (@lem6910809) (@lem6910808)). Qed.
Lemma lem6910812 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem6910811) (@lem6910702 h1)). Qed.
Lemma lem6910825 (y : real) (y' : real) : ((real_mul y' y) = y') = ((real_mul y' y) = y').
Proof. exact (eq_refl ((real_mul y' y) = y')). Qed.
Lemma lem6910826 (y : real) : (term20 y) = (term20 y).
Proof. exact (fun_ext (fun y' : real => @lem6910825 y y')). Qed.
Lemma lem6910827 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910829 (y : real) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem6910827) (@lem6910826 y)). Qed.
Lemma lem6910830 (y : real) (h1 : term97 y) : term39 y.
Proof. exact (EQ_MP (@lem6910829 y) (@lem6910793 y h1)). Qed.
Lemma lem6910839 (x : real) : ((term65 x) = x) = ((term65 x) = x).
Proof. exact (eq_refl ((term65 x) = x)). Qed.
Lemma lem6910840 : term66 = term66.
Proof. exact (fun_ext (fun x : real => @lem6910839 x)). Qed.
Lemma lem6910841 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910843 : term54 = term54.
Proof. exact (MK_COMB (@lem6910841) (@lem6910840)). Qed.
Lemma lem6910844 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem6910843) (@lem6910702 h1)). Qed.
Lemma lem6910852 (y : real) (y' : real) (h1 : term75 y y') : term75 y y'.
Proof. exact (h1). Qed.
Lemma lem6910854 (x : real) : ((term67 x) = x) = ((term67 x) = x).
Proof. exact (eq_refl ((term67 x) = x)). Qed.
Lemma lem6910855 : term68 = term68.
Proof. exact (fun_ext (fun x : real => @lem6910854 x)). Qed.
Lemma lem6910856 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem6910858 : term69 = term69.
Proof. exact (MK_COMB (@lem6910856) (@lem6910855)). Qed.
Lemma lem6910859 (h1 : term69) : term69.
Proof. exact (EQ_MP (@lem6910858) (@lem6910683 h1)). Qed.
Lemma lem6910874 (y : real) (y' : real) (h1 : term82 y y') : term82 y y'.
Proof. exact (h1). Qed.
Lemma lem6910878 (_92223 : real) (h1 : term54) : term204 _92223.
Proof. exact (@lem6910812 h1 _92223). Qed.
Lemma lem6910879 (_92223 : real) : (term204 _92223) = ((term65 _92223) = _92223).
Proof. exact (eq_refl (term204 _92223)). Qed.
Lemma lem6910884 (_92225 : real) (y : real) (h1 : term97 y) : term24 y _92225.
Proof. exact (@lem6910830 y h1 _92225). Qed.
Lemma lem6910885 (y : real) (_92225 : real) : (term24 y _92225) = ((real_mul _92225 y) = _92225).
Proof. exact (eq_refl (term24 y _92225)). Qed.
Lemma lem6910890 (_92227 : real) (h1 : term54) : term204 _92227.
Proof. exact (@lem6910844 h1 _92227). Qed.
Lemma lem6910891 (_92227 : real) : (term204 _92227) = ((term65 _92227) = _92227).
Proof. exact (eq_refl (term204 _92227)). Qed.
Lemma lem6910893 (_92228 : real) (h1 : term69) : term205 _92228.
Proof. exact (@lem6910859 h1 _92228). Qed.
Lemma lem6910894 (_92228 : real) : (term205 _92228) = ((term67 _92228) = _92228).
Proof. exact (eq_refl (term205 _92228)). Qed.
Lemma lem6910904 (y : real) (h1 : term97 y) : term91 y.
Proof. exact (proj2 (@lem6910789 y h1)). Qed.
Lemma lem6910914 (y' : real) (y : real) (h1 : term167 y' y) : y = term4.
Proof. exact (proj2 (@lem6910790 y' y h1)). Qed.
Lemma lem6910916 (y : real) (y' : real) (h1 : term75 y y') : term75 y y'.
Proof. exact (h1). Qed.
Lemma lem6910922 (y' : real) (y : real) (h1 : term167 y' y) : y = term4.
Proof. exact (proj2 (@lem6910790 y' y h1)). Qed.
Lemma lem6910924 (y : real) (y' : real) (h1 : term82 y y') : term82 y y'.
Proof. exact (h1). Qed.
Lemma lem6910967 (y' : real) : (term206 y') = (term206 y').
Proof. exact (eq_refl (term206 y')). Qed.
Lemma lem6910968 (y' : real) (y : real) (h1 : term167 y' y) : (term207 y' y) = (term208 y').
Proof. exact (MK_COMB (@lem6910967 y') (@lem6910914 y' y h1)). Qed.
Lemma lem6910969 (y' : real) : (term208 y') = (term209 y').
Proof. exact (eq_refl (term208 y')). Qed.
Lemma lem6910970 (y' : real) (y : real) : (term210 y' y) = (term210 y' y).
Proof. exact (eq_refl (term210 y' y)). Qed.
Lemma lem6910971 (y : real) (y' : real) : ((term207 y' y) = (term208 y')) = ((term207 y' y) = (term209 y')).
Proof. exact (MK_COMB (@lem6910970 y' y) (@lem6910969 y')). Qed.
Lemma lem6910972 (y : real) (y' : real) : (term207 y' y) = (term75 y y').
Proof. exact (eq_refl (term207 y' y)). Qed.
Lemma lem6910973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6910974 (y : real) (y' : real) : (term210 y' y) = (term211 y y').
Proof. exact (MK_COMB (@lem6910973) (@lem6910972 y y')). Qed.
Lemma lem6910975 (y' : real) : (term209 y') = (term209 y').
Proof. exact (eq_refl (term209 y')). Qed.
Lemma lem6910976 (y : real) (y' : real) : ((term207 y' y) = (term209 y')) = ((term75 y y') = (term209 y')).
Proof. exact (MK_COMB (@lem6910974 y y') (@lem6910975 y')). Qed.
Lemma lem6910977 (y : real) (y' : real) : ((term207 y' y) = (term208 y')) = ((term75 y y') = (term209 y')).
Proof. exact (TRANS (@lem6910971 y y') (@lem6910976 y y')). Qed.
Lemma lem6910978 (y' : real) (y : real) (h1 : term167 y' y) : (term75 y y') = (term209 y').
Proof. exact (EQ_MP (@lem6910977 y y') (@lem6910968 y' y h1)). Qed.
Lemma lem6910979 (y' : real) (y : real) (h1 : term75 y y') (h2 : term167 y' y) : term209 y'.
Proof. exact (EQ_MP (@lem6910978 y' y h2) (@lem6910916 y y' h1)). Qed.
Lemma lem6911022 (y' : real) : (term212 y') = (term212 y').
Proof. exact (eq_refl (term212 y')). Qed.
Lemma lem6911023 (y' : real) (y : real) (h1 : term167 y' y) : (term213 y' y) = (term214 y').
Proof. exact (MK_COMB (@lem6911022 y') (@lem6910922 y' y h1)). Qed.
Lemma lem6911024 (y' : real) : (term214 y') = (term215 y').
Proof. exact (eq_refl (term214 y')). Qed.
Lemma lem6911025 (y' : real) (y : real) : (term216 y' y) = (term216 y' y).
Proof. exact (eq_refl (term216 y' y)). Qed.
Lemma lem6911026 (y : real) (y' : real) : ((term213 y' y) = (term214 y')) = ((term213 y' y) = (term215 y')).
Proof. exact (MK_COMB (@lem6911025 y' y) (@lem6911024 y')). Qed.
Lemma lem6911027 (y : real) (y' : real) : (term213 y' y) = (term82 y y').
Proof. exact (eq_refl (term213 y' y)). Qed.
Lemma lem6911028 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6911029 (y : real) (y' : real) : (term216 y' y) = (term217 y y').
Proof. exact (MK_COMB (@lem6911028) (@lem6911027 y y')). Qed.
Lemma lem6911030 (y' : real) : (term215 y') = (term215 y').
Proof. exact (eq_refl (term215 y')). Qed.
Lemma lem6911031 (y : real) (y' : real) : ((term213 y' y) = (term215 y')) = ((term82 y y') = (term215 y')).
Proof. exact (MK_COMB (@lem6911029 y y') (@lem6911030 y')). Qed.
Lemma lem6911032 (y : real) (y' : real) : ((term213 y' y) = (term214 y')) = ((term82 y y') = (term215 y')).
Proof. exact (TRANS (@lem6911026 y y') (@lem6911031 y y')). Qed.
Lemma lem6911033 (y' : real) (y : real) (h1 : term167 y' y) : (term82 y y') = (term215 y').
Proof. exact (EQ_MP (@lem6911032 y y') (@lem6911023 y' y h1)). Qed.
Lemma lem6911034 (y' : real) (y : real) (h1 : term82 y y') (h2 : term167 y' y) : term215 y'.
Proof. exact (EQ_MP (@lem6911033 y' y h2) (@lem6910924 y y' h1)). Qed.
Lemma lem6911075 (x : real) (y : real) (z : real) : term218 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem6911079 (_92223 : real) (h1 : term54) : (term65 _92223) = _92223.
Proof. exact (EQ_MP (@lem6910879 _92223) (@lem6910878 _92223 h1)). Qed.
Lemma lem6911080 (y : real) (h1 : term54) : (term65 y) = y.
Proof. exact (@lem6911079 y h1). Qed.
Lemma lem6911081 (y : real) (h1 : term54) : term219 y.
Proof. exact (fun h0 : term209 y => @lem6911080 y h1). Qed.
Lemma lem6911083 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6911084 (y : real) : (term219 y) = ((term65 y) = y).
Proof. exact (@lem6911083 ((term65 y) = y)). Qed.
Lemma lem6911085 (y : real) (h1 : term54) : (term65 y) = y.
Proof. exact (EQ_MP (@lem6911084 y) (@lem6911081 y h1)). Qed.
Lemma lem6911087 (_92225 : real) (y : real) (h1 : term97 y) : (real_mul _92225 y) = _92225.
Proof. exact (EQ_MP (@lem6910885 y _92225) (@lem6910884 _92225 y h1)). Qed.
Lemma lem6911088 (y : real) (h1 : term97 y) : (term65 y) = term4.
Proof. exact (@lem6911087 term4 y h1). Qed.
Lemma lem6911089 (y : real) (h1 : term97 y) : term221 y.
Proof. exact (fun h0 : term222 y => @lem6911088 y h1). Qed.
Lemma lem6911091 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6911092 (y : real) : (term221 y) = ((term65 y) = term4).
Proof. exact (@lem6911091 ((term65 y) = term4)). Qed.
Lemma lem6911093 (y : real) (h1 : term97 y) : (term65 y) = term4.
Proof. exact (EQ_MP (@lem6911092 y) (@lem6911089 y h1)). Qed.
Lemma lem6911111 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6911112 (y : real) (x : real) (z : real) : (term223 x y z) = (term224 y x z).
Proof. exact (@lem6911111 (y = z) (term225 x z)). Qed.
Lemma lem6911122 (x : real) (y : real) : (term226 x y) = (term226 x y).
Proof. exact (eq_refl (term226 x y)). Qed.
Lemma lem6911123 (y : real) (x : real) (z : real) : (term218 x y z) = (term227 y x z).
Proof. exact (MK_COMB (@lem6911122 x y) (@lem6911112 y x z)). Qed.
Lemma lem6911127 (q : Prop) (p : Prop) (r : Prop) : (term228 p q r) = (term228 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem6911128 (y : real) (x : real) (z : real) : (term227 y x z) = (term229 y x z).
Proof. exact (@lem6911127 (y = z) (term225 x y) (term225 x z)). Qed.
Lemma lem6911150 (y : real) (x : real) (z : real) : (term218 x y z) = (term229 y x z).
Proof. exact (TRANS (@lem6911123 y x z) (@lem6911128 y x z)). Qed.
Lemma lem6911151 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6911152 (y : real) (x : real) (z : real) : (term230 x y z) = (term231 y x z).
Proof. exact (MK_COMB (@lem6911151) (@lem6911150 y x z)). Qed.
Lemma lem6911174 (y : real) (x : real) (z : real) : (term229 y x z) = (term229 y x z).
Proof. exact (eq_refl (term229 y x z)). Qed.
Lemma lem6911175 (y : real) (x : real) (z : real) : ((term218 x y z) = (term229 y x z)) = ((term229 y x z) = (term229 y x z)).
Proof. exact (MK_COMB (@lem6911152 y x z) (@lem6911174 y x z)). Qed.
Lemma lem6911177 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6911178 (x : Prop) : (x = x) = True.
Proof. exact (@lem6911177 Prop x). Qed.
Lemma lem6911179 (y : real) (x : real) (z : real) : ((term229 y x z) = (term229 y x z)) = True.
Proof. exact (@lem6911178 (term229 y x z)). Qed.
Lemma lem6911180 (y : real) (x : real) (z : real) : ((term218 x y z) = (term229 y x z)) = True.
Proof. exact (TRANS (@lem6911175 y x z) (@lem6911179 y x z)). Qed.
Lemma lem6911181 (y : real) (x : real) (z : real) : True = ((term218 x y z) = (term229 y x z)).
Proof. exact (SYM (@lem6911180 y x z)). Qed.
Lemma lem6911182 (y : real) (x : real) (z : real) : (term218 x y z) = (term229 y x z).
Proof. exact (EQ_MP (@lem6911181 y x z) (@lem0)). Qed.
Lemma lem6911183 (y : real) (x : real) (z : real) : term229 y x z.
Proof. exact (EQ_MP (@lem6911182 y x z) (@lem6911075 x y z)). Qed.
Lemma lem6911185 (b : Prop) (a : Prop) : (a \/ b) = (term232 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6911186 (x : real) (y : real) (z : real) : (term229 y x z) = (term233 x y z).
Proof. exact (@lem6911185 (term234 y x z) (y = z)). Qed.
Lemma lem6911188 (a : Prop) (b : Prop) : (term235 a b) = (term236 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem6911189 (y : real) (x : real) (z : real) : (term237 y x z) = (term238 y x z).
Proof. exact (@lem6911188 (term225 x y) (term225 x z)). Qed.
Lemma lem6911191 (a : Prop) : (term239 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6911192 (x : real) (y : real) : (term240 x y) = (x = y).
Proof. exact (@lem6911191 (x = y)). Qed.
Lemma lem6911193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6911194 (x : real) (y : real) : (term241 x y) = (term242 x y).
Proof. exact (MK_COMB (@lem6911193) (@lem6911192 x y)). Qed.
Lemma lem6911196 (a : Prop) : (term239 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6911197 (x : real) (z : real) : (term240 x z) = (x = z).
Proof. exact (@lem6911196 (x = z)). Qed.
Lemma lem6911198 (y : real) (x : real) (z : real) : (term238 y x z) = (term243 y x z).
Proof. exact (MK_COMB (@lem6911194 x y) (@lem6911197 x z)). Qed.
Lemma lem6911199 (y : real) (x : real) (z : real) : (term237 y x z) = (term243 y x z).
Proof. exact (TRANS (@lem6911189 y x z) (@lem6911198 y x z)). Qed.
Lemma lem6911200 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6911201 (y : real) (x : real) (z : real) : (term244 y x z) = (term245 y x z).
Proof. exact (MK_COMB (@lem6911200) (@lem6911199 y x z)). Qed.
Lemma lem6911202 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem6911203 (x : real) (y : real) (z : real) : (term233 x y z) = (term246 x y z).
Proof. exact (MK_COMB (@lem6911201 y x z) (@lem6911202 y z)). Qed.
Lemma lem6911204 (x : real) (y : real) (z : real) : (term229 y x z) = (term246 x y z).
Proof. exact (TRANS (@lem6911186 x y z) (@lem6911203 x y z)). Qed.
Lemma lem6911206 (y : real) (h1 : term54) (h2 : term97 y) : term247 y.
Proof. exact (conj (@lem6911085 y h1) (@lem6911093 y h2)). Qed.
Lemma lem6911208 (x : real) (y : real) (z : real) : term246 x y z.
Proof. exact (EQ_MP (@lem6911204 x y z) (@lem6911183 y x z)). Qed.
Lemma lem6911209 (y : real) : term248 y.
Proof. exact (@lem6911208 (term65 y) y term4). Qed.
Lemma lem6911212 (y : real) (h1 : term54) (h2 : term97 y) : y = term4.
Proof. exact (@lem6911209 y (@lem6911206 y h1 h2)). Qed.
Lemma lem6911213 (y : real) (h1 : term54) (h2 : term97 y) : term249 y.
Proof. exact (fun h0 : term91 y => @lem6911212 y h1 h2). Qed.
Lemma lem6911215 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6911216 (y : real) : (term249 y) = (y = term4).
Proof. exact (@lem6911215 (y = term4)). Qed.
Lemma lem6911217 (y : real) (h1 : term54) (h2 : term97 y) : y = term4.
Proof. exact (EQ_MP (@lem6911216 y) (@lem6911213 y h1 h2)). Qed.
Lemma lem6911220 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6911222 (y : real) : (term91 y) = (term250 y).
Proof. exact (@lem6911220 (y = term4)). Qed.
Lemma lem6911225 (y : real) (h1 : term97 y) : term250 y.
Proof. exact (EQ_MP (@lem6911222 y) (@lem6910904 y h1)). Qed.
Lemma lem6911228 (y : real) (h1 : term54) (h2 : term97 y) : False.
Proof. exact (@lem6911225 y h2 (@lem6911217 y h1 h2)). Qed.
Lemma lem6911229 (y : real) (h1 : term54) (h2 : term97 y) : term251.
Proof. exact (fun h0 : ~ False => @lem6911228 y h1 h2). Qed.
Lemma lem6911231 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6911232 : term251 = False.
Proof. exact (@lem6911231 False). Qed.
Lemma lem6911233 (y : real) (h1 : term54) (h2 : term97 y) : False.
Proof. exact (EQ_MP (@lem6911232) (@lem6911229 y h1 h2)). Qed.
Lemma lem6911278 (_92227 : real) (h1 : term54) : (term65 _92227) = _92227.
Proof. exact (EQ_MP (@lem6910891 _92227) (@lem6910890 _92227 h1)). Qed.
Lemma lem6911279 (y' : real) (h1 : term54) : (term65 y') = y'.
Proof. exact (@lem6911278 y' h1). Qed.
Lemma lem6911280 (y' : real) (h1 : term54) : term219 y'.
Proof. exact (fun h0 : term209 y' => @lem6911279 y' h1). Qed.
Lemma lem6911282 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6911283 (y' : real) : (term219 y') = ((term65 y') = y').
Proof. exact (@lem6911282 ((term65 y') = y')). Qed.
Lemma lem6911284 (y' : real) (h1 : term54) : (term65 y') = y'.
Proof. exact (EQ_MP (@lem6911283 y') (@lem6911280 y' h1)). Qed.
Lemma lem6911287 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6911289 (y' : real) : (term209 y') = (term252 y').
Proof. exact (@lem6911287 ((term65 y') = y')). Qed.
Lemma lem6911292 (y' : real) (y : real) (h1 : term75 y y') (h2 : term167 y' y) : term252 y'.
Proof. exact (EQ_MP (@lem6911289 y') (@lem6910979 y' y h1 h2)). Qed.
Lemma lem6911295 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (@lem6911292 y' y h2 h3 (@lem6911284 y' h1)). Qed.
Lemma lem6911296 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : term251.
Proof. exact (fun h0 : ~ False => @lem6911295 y' y h1 h2 h3). Qed.
Lemma lem6911298 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6911299 : term251 = False.
Proof. exact (@lem6911298 False). Qed.
Lemma lem6911345 (_92228 : real) (h1 : term69) : (term67 _92228) = _92228.
Proof. exact (EQ_MP (@lem6910894 _92228) (@lem6910893 _92228 h1)). Qed.
Lemma lem6911346 (y' : real) (h1 : term69) : (term67 y') = y'.
Proof. exact (@lem6911345 y' h1). Qed.
Lemma lem6911347 (y' : real) (h1 : term69) : term253 y'.
Proof. exact (fun h0 : term215 y' => @lem6911346 y' h1). Qed.
Lemma lem6911349 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6911350 (y' : real) : (term253 y') = ((term67 y') = y').
Proof. exact (@lem6911349 ((term67 y') = y')). Qed.
Lemma lem6911351 (y' : real) (h1 : term69) : (term67 y') = y'.
Proof. exact (EQ_MP (@lem6911350 y') (@lem6911347 y' h1)). Qed.
Lemma lem6911354 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6911356 (y' : real) : (term215 y') = (term254 y').
Proof. exact (@lem6911354 ((term67 y') = y')). Qed.
Lemma lem6911359 (y' : real) (y : real) (h1 : term82 y y') (h2 : term167 y' y) : term254 y'.
Proof. exact (EQ_MP (@lem6911356 y') (@lem6911034 y' y h1 h2)). Qed.
Lemma lem6911362 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (@lem6911359 y' y h2 h3 (@lem6911351 y' h1)). Qed.
Lemma lem6911363 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : term251.
Proof. exact (fun h0 : ~ False => @lem6911362 y' y h1 h2 h3). Qed.
Lemma lem6911365 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6911366 : term251 = False.
Proof. exact (@lem6911365 False). Qed.
Lemma lem6911368 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6911366) (@lem6911363 y' y h1 h2 h3)). Qed.
Lemma lem6911369 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6911299) (@lem6911296 y' y h1 h2 h3)). Qed.
Lemma lem6911370 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : (term82 y y') = False.
Proof. exact (prop_ext (fun h4 : term82 y y' => @lem6911368 y' y h1 h2 h3) (fun h4 : False => @lem6910924 y y' h2)). Qed.
Lemma lem6911371 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6911370 y' y h1 h2 h3) (@lem6910924 y y' h2)). Qed.
Lemma lem6911372 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : (term75 y y') = False.
Proof. exact (prop_ext (fun h4 : term75 y y' => @lem6911369 y' y h1 h2 h3) (fun h4 : False => @lem6910916 y y' h2)). Qed.
Lemma lem6911373 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6911372 y' y h1 h2 h3) (@lem6910916 y y' h2)). Qed.
Lemma lem6911374 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : (term82 y y') = False.
Proof. exact (prop_ext (fun h4 : term82 y y' => @lem6911371 y' y h1 h2 h3) (fun h4 : False => @lem6910874 y y' h2)). Qed.
Lemma lem6911375 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6911374 y' y h1 h2 h3) (@lem6910874 y y' h2)). Qed.
Lemma lem6911376 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : (term75 y y') = False.
Proof. exact (prop_ext (fun h4 : term75 y y' => @lem6911373 y' y h1 h2 h3) (fun h4 : False => @lem6910852 y y' h2)). Qed.
Lemma lem6911377 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6911376 y' y h1 h2 h3) (@lem6910852 y y' h2)). Qed.
Lemma lem6911378 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : (term82 y y') = False.
Proof. exact (prop_ext (fun h4 : term82 y y' => @lem6911375 y' y h1 h2 h3) (fun h4 : False => @lem6910874 y y' h2)). Qed.
Lemma lem6911379 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6911378 y' y h1 h2 h3) (@lem6910874 y y' h2)). Qed.
Lemma lem6911380 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : term69 = False.
Proof. exact (prop_ext (fun h4 : term69 => @lem6911379 y' y h1 h2 h3) (fun h4 : False => @lem6910859 h1)). Qed.
Lemma lem6911381 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6911380 y' y h1 h2 h3) (@lem6910859 h1)). Qed.
Lemma lem6911382 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : (term75 y y') = False.
Proof. exact (prop_ext (fun h4 : term75 y y' => @lem6911377 y' y h1 h2 h3) (fun h4 : False => @lem6910852 y y' h2)). Qed.
Lemma lem6911383 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6911382 y' y h1 h2 h3) (@lem6910852 y y' h2)). Qed.
Lemma lem6911384 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : term54 = False.
Proof. exact (prop_ext (fun h4 : term54 => @lem6911383 y' y h1 h2 h3) (fun h4 : False => @lem6910844 h1)). Qed.
Lemma lem6911385 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem6911384 y' y h1 h2 h3) (@lem6910844 h1)). Qed.
Lemma lem6911386 (y : real) (h1 : term54) (h2 : term97 y) : term54 = False.
Proof. exact (prop_ext (fun h3 : term54 => @lem6911233 y h1 h2) (fun h3 : False => @lem6910812 h1)). Qed.
Lemma lem6911387 (y : real) (h1 : term54) (h2 : term97 y) : False.
Proof. exact (EQ_MP (@lem6911386 y h1 h2) (@lem6910812 h1)). Qed.
Lemma lem6911388 (y' : real) (y : real) (h1 : term69) (h2 : term54) (h3 : term167 y' y) : False.
Proof. exact (or_elim (@lem6910796 y' y h3) (fun h0 : term75 y y' => @lem6911385 y' y h2 h0 h3) (fun h0 : term82 y y' => @lem6911381 y' y h1 h0 h3)). Qed.
Lemma lem6911389 (y' : real) (y : real) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : False.
Proof. exact (or_elim (@lem6910788 y' y h3) (fun h0 : term97 y => @lem6911387 y h2 h0) (fun h0 : term167 y' y => @lem6911388 y' y h1 h2 h0)). Qed.
Lemma lem6911390 (y' : real) (y : real) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : (term198 y' y) = False.
Proof. exact (prop_ext (fun h4 : term198 y' y => @lem6911389 y' y h1 h2 h3) (fun h4 : False => @lem6910788 y' y h3)). Qed.
Lemma lem6911391 (y' : real) (y : real) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : False.
Proof. exact (EQ_MP (@lem6911390 y' y h1 h2 h3) (@lem6910788 y' y h3)). Qed.
Lemma lem6911392 (y' : real) (y : real) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : term54 = False.
Proof. exact (prop_ext (fun h4 : term54 => @lem6911391 y' y h1 h2 h3) (fun h4 : False => @lem6910702 h2)). Qed.
Lemma lem6911393 (y' : real) (y : real) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : False.
Proof. exact (EQ_MP (@lem6911392 y' y h1 h2 h3) (@lem6910702 h2)). Qed.
Lemma lem6911394 (y' : real) (y : real) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : term69 = False.
Proof. exact (prop_ext (fun h4 : term69 => @lem6911393 y' y h1 h2 h3) (fun h4 : False => @lem6910683 h1)). Qed.
Lemma lem6911395 (y' : real) (y : real) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : False.
Proof. exact (EQ_MP (@lem6911394 y' y h1 h2 h3) (@lem6910683 h1)). Qed.
Lemma lem6911396 (y : real) (h1 : term69) (h2 : term54) (h3 : term201 y) : False.
Proof. exact (ex_elim (@lem6910663 y h3) (fun y' : real => fun h0 : term200 y y' => @lem6911395 y' y h1 h2 h0)). Qed.
Lemma lem6911397 (h1 : term69) (h2 : term54) (h3 : term62) : False.
Proof. exact (ex_elim (@lem6910636 h3) (fun y : real => fun h0 : term202 y => @lem6911396 y h1 h2 h0)). Qed.
Lemma lem6911398 (h1 : term69) (h2 : term54) (h3 : term62) : term54 = False.
Proof. exact (prop_ext (fun h4 : term54 => @lem6911397 h1 h2 h3) (fun h4 : False => @lem6910662 h2)). Qed.
Lemma lem6911399 (h1 : term69) (h2 : term54) (h3 : term62) : False.
Proof. exact (EQ_MP (@lem6911398 h1 h2 h3) (@lem6910662 h2)). Qed.
Lemma lem6911400 (h1 : term69) (h2 : term54) (h3 : term62) : term69 = False.
Proof. exact (prop_ext (fun h4 : term69 => @lem6911399 h1 h2 h3) (fun h4 : False => @lem6910649 h1)). Qed.
Lemma lem6911401 (h1 : term69) (h2 : term54) (h3 : term62) : False.
Proof. exact (EQ_MP (@lem6911400 h1 h2 h3) (@lem6910649 h1)). Qed.
Lemma lem6911402 (h1 : term69) (h2 : term62) : term52.
Proof. exact (fun h0 : term54 => @lem6911401 h1 h0 h2). Qed.
Lemma lem6911403 : term52 = term53.
Proof. exact (@lem69 term54). Qed.
Lemma lem6911404 (h1 : term69) (h2 : term62) : term53.
Proof. exact (EQ_MP (@lem6911403) (@lem6911402 h1 h2)). Qed.
Lemma lem6911405 (h1 : term62) : term57.
Proof. exact (fun h0 : term69 => @lem6911404 h0 h1). Qed.
Lemma lem6911406 : term64.
Proof. exact (fun h0 : term62 => @lem6911405 h0). Qed.
Lemma lem6911407 : term9.
Proof. exact (EQ_MP (@lem6910317) (@lem6911406)). Qed.
Lemma lem6911409 : term9.
Proof. exact (@lem6910143 (@lem6911407)). Qed.
Lemma lem6911410 (h1 : term8) : term56.
Proof. exact (@lem6911409 (@lem6910128 h1)). Qed.
Lemma lem6911411 (h1 : term8) : term52.
Proof. exact (@lem6911410 h1 (@lem1383409)). Qed.
Lemma lem6911412 (h1 : term8) : False.
Proof. exact (@lem6911411 h1 (@lem1338986)). Qed.
Lemma lem6911413 (h1 : term8) : term8 = False.
Proof. exact (prop_ext (fun h2 : term8 => @lem6911412 h1) (fun h2 : False => @lem6910128 h1)). Qed.
Lemma lem6911414 (h1 : term8) : False.
Proof. exact (EQ_MP (@lem6911413 h1) (@lem6910128 h1)). Qed.
Lemma lem6911415 : term7.
Proof. exact (fun h0 : term8 => @lem6911414 h0). Qed.
Lemma lem6911416 : term6.
Proof. exact (EQ_MP (@lem6910127) (@lem6911415)). Qed.
Lemma lem6911417 : term255 = term4.
Proof. exact (@lem6910123 (@lem6911416)). Qed.
