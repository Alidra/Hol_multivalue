Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_RSQRT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import POW_2_SQRT_spec.
Require Import REAL_LE_SQUARE_spec.
Require Import REAL_POW_2_spec.
Require Import SQRT_MONO_LE_spec.
Require Import SQRT_POS_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339577_spec.
Require Import thm1339697_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1959045 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1959046 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1959047 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1959046 t1) (@lem1959045 t1)). Qed.
Lemma lem1959048 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1959047 t1 t2). Qed.
Lemma lem1959049 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1959050 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1959049 t1 t2) (@lem1959048 t1 t2)). Qed.
Lemma lem1959051 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1959050 t1 t2 t3). Qed.
Lemma lem1959052 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1959053 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1959052 t1 t2 t3) (@lem1959051 t1 t2 t3)). Qed.
Lemma lem1959054 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1959053 t1 t2 t3)). Qed.
Lemma lem1959056 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1959057 : term8 = term9.
Proof. exact (@lem1959056 term8). Qed.
Lemma lem1959058 : term9 = term8.
Proof. exact (SYM (@lem1959057)). Qed.
Lemma lem1959059 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1959062 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1959063 : term12.
Proof. exact (fun h0 : term11 => @lem1959062 h0). Qed.
Lemma lem1959064 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1959065 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1959066 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1959064 h2 (@lem1959065 h1)). Qed.
Lemma lem1959067 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1959066 h1 h0). Qed.
Lemma lem1959068 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1959069 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1959067 h1 (@lem1959068 h2)). Qed.
Lemma lem1959070 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1959069 h0 h1). Qed.
Lemma lem1959071 : term14.
Proof. exact (fun h0 : term12 => @lem1959070 h0). Qed.
Lemma lem1959074 : term12.
Proof. exact (@lem1959071 (@lem1959063)). Qed.
Lemma lem1959146 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1959147 : term15 = term16.
Proof. exact (@lem1959146 term17). Qed.
Lemma lem1959202 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1959203 : term19 = term20.
Proof. exact (MK_COMB (@lem1959202) (@lem1959147)). Qed.
Lemma lem1959206 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1959207 : term22 = term23.
Proof. exact (MK_COMB (@lem1959206) (@lem1959203)). Qed.
Lemma lem1959210 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1959211 : term25 = term26.
Proof. exact (MK_COMB (@lem1959210) (@lem1959207)). Qed.
Lemma lem1959214 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem1959215 : term28 = term29.
Proof. exact (MK_COMB (@lem1959214) (@lem1959211)). Qed.
Lemma lem1959218 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1959219 : term31 = term32.
Proof. exact (MK_COMB (@lem1959218) (@lem1959215)). Qed.
Lemma lem1959222 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1959223 : term34 = term35.
Proof. exact (MK_COMB (@lem1959222) (@lem1959219)). Qed.
Lemma lem1959226 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem1959233 : term11 = term37.
Proof. exact (MK_COMB (@lem1959226) (@lem1959223)). Qed.
Lemma lem1959238 (y : real) (x : real) : (term38 y x) = (term38 y x).
Proof. exact (eq_refl (term38 y x)). Qed.
Lemma lem1959239 (x : real) : (term39 x) = (term39 x).
Proof. exact (fun_ext (fun y : real => @lem1959238 y x)). Qed.
Lemma lem1959240 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959241 (x : real) : (term40 x) = (term40 x).
Proof. exact (MK_COMB (@lem1959240) (@lem1959239 x)). Qed.
Lemma lem1959242 : term41 = term41.
Proof. exact (fun_ext (fun x : real => @lem1959241 x)). Qed.
Lemma lem1959243 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959244 : term17 = term17.
Proof. exact (MK_COMB (@lem1959243) (@lem1959242)). Qed.
Lemma lem1959245 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1959246 : term16 = term16.
Proof. exact (MK_COMB (@lem1959245) (@lem1959244)). Qed.
Lemma lem1959251 (x : real) (y : real) : (term42 x y) = (term42 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1959252 (x : real) : (term43 x) = (term43 x).
Proof. exact (fun_ext (fun y : real => @lem1959251 x y)). Qed.
Lemma lem1959253 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959254 (x : real) : (term44 x) = (term44 x).
Proof. exact (MK_COMB (@lem1959253) (@lem1959252 x)). Qed.
Lemma lem1959255 : term45 = term45.
Proof. exact (fun_ext (fun x : real => @lem1959254 x)). Qed.
Lemma lem1959256 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959257 : term46 = term46.
Proof. exact (MK_COMB (@lem1959256) (@lem1959255)). Qed.
Lemma lem1959258 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1959259 : term18 = term18.
Proof. exact (MK_COMB (@lem1959258) (@lem1959257)). Qed.
Lemma lem1959260 : term20 = term20.
Proof. exact (MK_COMB (@lem1959259) (@lem1959246)). Qed.
Lemma lem1959265 (x : real) : (term47 x) = (term47 x).
Proof. exact (eq_refl (term47 x)). Qed.
Lemma lem1959266 : term48 = term48.
Proof. exact (fun_ext (fun x : real => @lem1959265 x)). Qed.
Lemma lem1959267 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959268 : term49 = term49.
Proof. exact (MK_COMB (@lem1959267) (@lem1959266)). Qed.
Lemma lem1959269 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1959270 : term21 = term21.
Proof. exact (MK_COMB (@lem1959269) (@lem1959268)). Qed.
Lemma lem1959271 : term23 = term23.
Proof. exact (MK_COMB (@lem1959270) (@lem1959260)). Qed.
Lemma lem1959272 (x : real) : ((term50 x) = (real_mul x x)) = ((term50 x) = (real_mul x x)).
Proof. exact (eq_refl ((term50 x) = (real_mul x x))). Qed.
Lemma lem1959273 : term51 = term51.
Proof. exact (fun_ext (fun x : real => @lem1959272 x)). Qed.
Lemma lem1959274 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959275 : term52 = term52.
Proof. exact (MK_COMB (@lem1959274) (@lem1959273)). Qed.
Lemma lem1959276 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1959277 : term24 = term24.
Proof. exact (MK_COMB (@lem1959276) (@lem1959275)). Qed.
Lemma lem1959278 : term26 = term26.
Proof. exact (MK_COMB (@lem1959277) (@lem1959271)). Qed.
Lemma lem1959279 (x : real) : (term53 x) = (term53 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1959280 : term54 = term54.
Proof. exact (fun_ext (fun x : real => @lem1959279 x)). Qed.
Lemma lem1959281 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959282 : term55 = term55.
Proof. exact (MK_COMB (@lem1959281) (@lem1959280)). Qed.
Lemma lem1959283 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1959284 : term27 = term27.
Proof. exact (MK_COMB (@lem1959283) (@lem1959282)). Qed.
Lemma lem1959285 : term29 = term29.
Proof. exact (MK_COMB (@lem1959284) (@lem1959278)). Qed.
Lemma lem1959294 (y : real) (x : real) (z : real) : (term56 y x z) = (term56 y x z).
Proof. exact (eq_refl (term56 y x z)). Qed.
Lemma lem1959295 (y : real) (x : real) : (term57 y x) = (term57 y x).
Proof. exact (fun_ext (fun z : real => @lem1959294 y x z)). Qed.
Lemma lem1959296 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959297 (y : real) (x : real) : (term58 y x) = (term58 y x).
Proof. exact (MK_COMB (@lem1959296) (@lem1959295 y x)). Qed.
Lemma lem1959298 (x : real) : (term59 x) = (term59 x).
Proof. exact (fun_ext (fun y : real => @lem1959297 y x)). Qed.
Lemma lem1959299 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959300 (x : real) : (term60 x) = (term60 x).
Proof. exact (MK_COMB (@lem1959299) (@lem1959298 x)). Qed.
Lemma lem1959301 : term61 = term61.
Proof. exact (fun_ext (fun x : real => @lem1959300 x)). Qed.
Lemma lem1959302 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959303 : term62 = term62.
Proof. exact (MK_COMB (@lem1959302) (@lem1959301)). Qed.
Lemma lem1959304 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1959305 : term30 = term30.
Proof. exact (MK_COMB (@lem1959304) (@lem1959303)). Qed.
Lemma lem1959306 : term32 = term32.
Proof. exact (MK_COMB (@lem1959305) (@lem1959285)). Qed.
Lemma lem1959311 (x : real) : (term63 x) = (term63 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1959312 : term64 = term64.
Proof. exact (fun_ext (fun x : real => @lem1959311 x)). Qed.
Lemma lem1959313 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959314 : term65 = term65.
Proof. exact (MK_COMB (@lem1959313) (@lem1959312)). Qed.
Lemma lem1959315 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1959316 : term33 = term33.
Proof. exact (MK_COMB (@lem1959315) (@lem1959314)). Qed.
Lemma lem1959317 : term35 = term35.
Proof. exact (MK_COMB (@lem1959316) (@lem1959306)). Qed.
Lemma lem1959322 (x : real) (y : real) : (term66 x y) = (term66 x y).
Proof. exact (eq_refl (term66 x y)). Qed.
Lemma lem1959323 (x : real) : (term67 x) = (term67 x).
Proof. exact (fun_ext (fun y : real => @lem1959322 x y)). Qed.
Lemma lem1959324 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959325 (x : real) : (term68 x) = (term68 x).
Proof. exact (MK_COMB (@lem1959324) (@lem1959323 x)). Qed.
Lemma lem1959326 : term69 = term69.
Proof. exact (fun_ext (fun x : real => @lem1959325 x)). Qed.
Lemma lem1959327 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959328 : term8 = term8.
Proof. exact (MK_COMB (@lem1959327) (@lem1959326)). Qed.
Lemma lem1959329 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1959330 : term10 = term10.
Proof. exact (MK_COMB (@lem1959329) (@lem1959328)). Qed.
Lemma lem1959331 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1959332 : term36 = term36.
Proof. exact (MK_COMB (@lem1959331) (@lem1959330)). Qed.
Lemma lem1959333 : term37 = term37.
Proof. exact (MK_COMB (@lem1959332) (@lem1959317)). Qed.
Lemma lem1959442 : term11 = term37.
Proof. exact (TRANS (@lem1959233) (@lem1959333)). Qed.
Lemma lem1959443 : term37 = term11.
Proof. exact (SYM (@lem1959442)). Qed.
Lemma lem1959444 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1959445 (h1 : term65) : term65.
Proof. exact (h1). Qed.
Lemma lem1959446 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem1959447 (h1 : term55) : term55.
Proof. exact (h1). Qed.
Lemma lem1959448 (h1 : term52) : term52.
Proof. exact (h1). Qed.
Lemma lem1959449 (h1 : term49) : term49.
Proof. exact (h1). Qed.
Lemma lem1959450 (h1 : term46) : term46.
Proof. exact (h1). Qed.
Lemma lem1959451 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1959458 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (@lem17362 (term72 x y) (term73 x y)). Qed.
Lemma lem1959459 (P : real -> Prop) : (term74 P) = (term75 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1959460 (x : real) : (term76 x) = (term77 x).
Proof. exact (@lem1959459 (term67 x)). Qed.
Lemma lem1959461 (x : real) (y : real) : (term78 x y) = (term66 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem1959462 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1959463 (x : real) (y : real) : (term79 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem1959462) (@lem1959461 x y)). Qed.
Lemma lem1959464 (x : real) (y : real) : (term79 x y) = (term71 x y).
Proof. exact (TRANS (@lem1959463 x y) (@lem1959458 x y)). Qed.
Lemma lem1959465 (x : real) : (term80 x) = (term81 x).
Proof. exact (fun_ext (fun y : real => @lem1959464 x y)). Qed.
Lemma lem1959466 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1959467 (x : real) : (term77 x) = (term82 x).
Proof. exact (MK_COMB (@lem1959466) (@lem1959465 x)). Qed.
Lemma lem1959468 (x : real) : (term76 x) = (term82 x).
Proof. exact (TRANS (@lem1959460 x) (@lem1959467 x)). Qed.
Lemma lem1959469 (P : real -> Prop) : (term74 P) = (term75 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1959470 : term10 = term83.
Proof. exact (@lem1959469 term69). Qed.
Lemma lem1959471 (x : real) : (term84 x) = (term68 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1959472 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1959473 (x : real) : (term85 x) = (term76 x).
Proof. exact (MK_COMB (@lem1959472) (@lem1959471 x)). Qed.
Lemma lem1959474 (x : real) : (term85 x) = (term82 x).
Proof. exact (TRANS (@lem1959473 x) (@lem1959468 x)). Qed.
Lemma lem1959475 : term86 = term87.
Proof. exact (fun_ext (fun x : real => @lem1959474 x)). Qed.
Lemma lem1959476 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1959477 : term83 = term88.
Proof. exact (MK_COMB (@lem1959476) (@lem1959475)). Qed.
Lemma lem1959534 : term10 = term88.
Proof. exact (TRANS (@lem1959470) (@lem1959477)). Qed.
Lemma lem1959535 (h1 : term10) : term88.
Proof. exact (EQ_MP (@lem1959534) (@lem1959444 h1)). Qed.
Lemma lem1959542 (x : real) : (term63 x) = (term89 x).
Proof. exact (@lem17265 (term90 x) ((term91 x) = x)). Qed.
Lemma lem1959543 : term64 = term92.
Proof. exact (fun_ext (fun x : real => @lem1959542 x)). Qed.
Lemma lem1959544 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959597 : term65 = term93.
Proof. exact (MK_COMB (@lem1959544) (@lem1959543)). Qed.
Lemma lem1959598 (h1 : term65) : term93.
Proof. exact (EQ_MP (@lem1959597) (@lem1959445 h1)). Qed.
Lemma lem1959605 (x : real) (y : real) (z : real) : (term94 x y z) = (term95 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem1959606 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem1959607 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1959608 (x : real) (y : real) (z : real) : (term96 x y z) = (term97 x y z).
Proof. exact (MK_COMB (@lem1959607) (@lem1959605 x y z)). Qed.
Lemma lem1959609 (y : real) (x : real) (z : real) : (term98 y x z) = (term99 y x z).
Proof. exact (MK_COMB (@lem1959608 x y z) (@lem1959606 x z)). Qed.
Lemma lem1959610 (y : real) (x : real) (z : real) : (term56 y x z) = (term98 y x z).
Proof. exact (@lem17265 (term100 x y z) (real_le x z)). Qed.
Lemma lem1959611 (y : real) (x : real) (z : real) : (term56 y x z) = (term99 y x z).
Proof. exact (TRANS (@lem1959610 y x z) (@lem1959609 y x z)). Qed.
Lemma lem1959612 (y : real) (x : real) : (term57 y x) = (term101 y x).
Proof. exact (fun_ext (fun z : real => @lem1959611 y x z)). Qed.
Lemma lem1959613 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959614 (y : real) (x : real) : (term58 y x) = (term102 y x).
Proof. exact (MK_COMB (@lem1959613) (@lem1959612 y x)). Qed.
Lemma lem1959615 (x : real) : (term59 x) = (term103 x).
Proof. exact (fun_ext (fun y : real => @lem1959614 y x)). Qed.
Lemma lem1959616 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959617 (x : real) : (term60 x) = (term104 x).
Proof. exact (MK_COMB (@lem1959616) (@lem1959615 x)). Qed.
Lemma lem1959618 : term61 = term105.
Proof. exact (fun_ext (fun x : real => @lem1959617 x)). Qed.
Lemma lem1959619 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959680 : term62 = term106.
Proof. exact (MK_COMB (@lem1959619) (@lem1959618)). Qed.
Lemma lem1959681 (h1 : term62) : term106.
Proof. exact (EQ_MP (@lem1959680) (@lem1959446 h1)). Qed.
Lemma lem1959682 (x : real) : (term53 x) = (term53 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1959683 : term54 = term54.
Proof. exact (fun_ext (fun x : real => @lem1959682 x)). Qed.
Lemma lem1959684 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959693 : term55 = term55.
Proof. exact (MK_COMB (@lem1959684) (@lem1959683)). Qed.
Lemma lem1959694 (h1 : term55) : term55.
Proof. exact (EQ_MP (@lem1959693) (@lem1959447 h1)). Qed.
Lemma lem1959695 (x : real) : ((term50 x) = (real_mul x x)) = ((term50 x) = (real_mul x x)).
Proof. exact (eq_refl ((term50 x) = (real_mul x x))). Qed.
Lemma lem1959696 : term51 = term51.
Proof. exact (fun_ext (fun x : real => @lem1959695 x)). Qed.
Lemma lem1959697 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959706 : term52 = term52.
Proof. exact (MK_COMB (@lem1959697) (@lem1959696)). Qed.
Lemma lem1959707 (h1 : term52) : term52.
Proof. exact (EQ_MP (@lem1959706) (@lem1959448 h1)). Qed.
Lemma lem1959714 (x : real) : (term47 x) = (term107 x).
Proof. exact (@lem17265 (term90 x) (term108 x)). Qed.
Lemma lem1959715 : term48 = term109.
Proof. exact (fun_ext (fun x : real => @lem1959714 x)). Qed.
Lemma lem1959716 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959769 : term49 = term110.
Proof. exact (MK_COMB (@lem1959716) (@lem1959715)). Qed.
Lemma lem1959770 (h1 : term49) : term110.
Proof. exact (EQ_MP (@lem1959769) (@lem1959449 h1)). Qed.
Lemma lem1959777 (x : real) (y : real) : (term42 x y) = (term111 x y).
Proof. exact (@lem17265 (real_le x y) (term112 x y)). Qed.
Lemma lem1959778 (x : real) : (term43 x) = (term113 x).
Proof. exact (fun_ext (fun y : real => @lem1959777 x y)). Qed.
Lemma lem1959779 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959780 (x : real) : (term44 x) = (term114 x).
Proof. exact (MK_COMB (@lem1959779) (@lem1959778 x)). Qed.
Lemma lem1959781 : term45 = term115.
Proof. exact (fun_ext (fun x : real => @lem1959780 x)). Qed.
Lemma lem1959782 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959839 : term46 = term116.
Proof. exact (MK_COMB (@lem1959782) (@lem1959781)). Qed.
Lemma lem1959840 (h1 : term46) : term116.
Proof. exact (EQ_MP (@lem1959839) (@lem1959450 h1)). Qed.
Lemma lem1959845 (y : real) (x : real) : (term38 y x) = (term38 y x).
Proof. exact (eq_refl (term38 y x)). Qed.
Lemma lem1959846 (x : real) : (term39 x) = (term39 x).
Proof. exact (fun_ext (fun y : real => @lem1959845 y x)). Qed.
Lemma lem1959847 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959848 (x : real) : (term40 x) = (term40 x).
Proof. exact (MK_COMB (@lem1959847) (@lem1959846 x)). Qed.
Lemma lem1959849 : term41 = term41.
Proof. exact (fun_ext (fun x : real => @lem1959848 x)). Qed.
Lemma lem1959850 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959907 : term17 = term17.
Proof. exact (MK_COMB (@lem1959850) (@lem1959849)). Qed.
Lemma lem1959908 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem1959907) (@lem1959451 h1)). Qed.
Lemma lem1959909 (x : real) (h1 : term82 x) : term82 x.
Proof. exact (h1). Qed.
Lemma lem1959941 (x : real) : (term89 x) = (term89 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1959942 : term92 = term92.
Proof. exact (fun_ext (fun x : real => @lem1959941 x)). Qed.
Lemma lem1959943 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959944 : term93 = term93.
Proof. exact (MK_COMB (@lem1959943) (@lem1959942)). Qed.
Lemma lem1959945 (h1 : term65) : term93.
Proof. exact (EQ_MP (@lem1959944) (@lem1959598 h1)). Qed.
Lemma lem1959970 (y : real) (x : real) (z : real) : (term99 y x z) = (term99 y x z).
Proof. exact (eq_refl (term99 y x z)). Qed.
Lemma lem1959971 (y : real) (x : real) : (term101 y x) = (term101 y x).
Proof. exact (fun_ext (fun z : real => @lem1959970 y x z)). Qed.
Lemma lem1959972 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959973 (y : real) (x : real) : (term102 y x) = (term102 y x).
Proof. exact (MK_COMB (@lem1959972) (@lem1959971 y x)). Qed.
Lemma lem1959974 (x : real) : (term103 x) = (term103 x).
Proof. exact (fun_ext (fun y : real => @lem1959973 y x)). Qed.
Lemma lem1959975 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959976 (x : real) : (term104 x) = (term104 x).
Proof. exact (MK_COMB (@lem1959975) (@lem1959974 x)). Qed.
Lemma lem1959977 : term105 = term105.
Proof. exact (fun_ext (fun x : real => @lem1959976 x)). Qed.
Lemma lem1959978 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959979 : term106 = term106.
Proof. exact (MK_COMB (@lem1959978) (@lem1959977)). Qed.
Lemma lem1959980 (h1 : term62) : term106.
Proof. exact (EQ_MP (@lem1959979) (@lem1959681 h1)). Qed.
Lemma lem1959993 (x : real) : (term53 x) = (term53 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1959994 : term54 = term54.
Proof. exact (fun_ext (fun x : real => @lem1959993 x)). Qed.
Lemma lem1959995 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1959996 : term55 = term55.
Proof. exact (MK_COMB (@lem1959995) (@lem1959994)). Qed.
Lemma lem1959997 (h1 : term55) : term55.
Proof. exact (EQ_MP (@lem1959996) (@lem1959694 h1)). Qed.
Lemma lem1960016 (x : real) : ((term50 x) = (real_mul x x)) = ((term50 x) = (real_mul x x)).
Proof. exact (eq_refl ((term50 x) = (real_mul x x))). Qed.
Lemma lem1960017 : term51 = term51.
Proof. exact (fun_ext (fun x : real => @lem1960016 x)). Qed.
Lemma lem1960018 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960019 : term52 = term52.
Proof. exact (MK_COMB (@lem1960018) (@lem1960017)). Qed.
Lemma lem1960020 (h1 : term52) : term52.
Proof. exact (EQ_MP (@lem1960019) (@lem1959707 h1)). Qed.
Lemma lem1960045 (x : real) : (term107 x) = (term107 x).
Proof. exact (eq_refl (term107 x)). Qed.
Lemma lem1960046 : term109 = term109.
Proof. exact (fun_ext (fun x : real => @lem1960045 x)). Qed.
Lemma lem1960047 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960048 : term110 = term110.
Proof. exact (MK_COMB (@lem1960047) (@lem1960046)). Qed.
Lemma lem1960049 (h1 : term49) : term110.
Proof. exact (EQ_MP (@lem1960048) (@lem1959770 h1)). Qed.
Lemma lem1960068 (x : real) (y : real) : (term111 x y) = (term111 x y).
Proof. exact (eq_refl (term111 x y)). Qed.
Lemma lem1960069 (x : real) : (term113 x) = (term113 x).
Proof. exact (fun_ext (fun y : real => @lem1960068 x y)). Qed.
Lemma lem1960070 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960071 (x : real) : (term114 x) = (term114 x).
Proof. exact (MK_COMB (@lem1960070) (@lem1960069 x)). Qed.
Lemma lem1960072 : term115 = term115.
Proof. exact (fun_ext (fun x : real => @lem1960071 x)). Qed.
Lemma lem1960073 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960074 : term116 = term116.
Proof. exact (MK_COMB (@lem1960073) (@lem1960072)). Qed.
Lemma lem1960075 (h1 : term46) : term116.
Proof. exact (EQ_MP (@lem1960074) (@lem1959840 h1)). Qed.
Lemma lem1960088 (y : real) (x : real) : (term38 y x) = (term38 y x).
Proof. exact (eq_refl (term38 y x)). Qed.
Lemma lem1960089 (x : real) : (term39 x) = (term39 x).
Proof. exact (fun_ext (fun y : real => @lem1960088 y x)). Qed.
Lemma lem1960090 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960091 (x : real) : (term40 x) = (term40 x).
Proof. exact (MK_COMB (@lem1960090) (@lem1960089 x)). Qed.
Lemma lem1960092 : term41 = term41.
Proof. exact (fun_ext (fun x : real => @lem1960091 x)). Qed.
Lemma lem1960093 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960094 : term17 = term17.
Proof. exact (MK_COMB (@lem1960093) (@lem1960092)). Qed.
Lemma lem1960095 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem1960094) (@lem1959908 h1)). Qed.
Lemma lem1960123 (x : real) (y : real) (h1 : term71 x y) : term71 x y.
Proof. exact (h1). Qed.
Lemma lem1960133 (x : real) : (term89 x) = (term89 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1960134 : term92 = term92.
Proof. exact (fun_ext (fun x : real => @lem1960133 x)). Qed.
Lemma lem1960135 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960137 : term93 = term93.
Proof. exact (MK_COMB (@lem1960135) (@lem1960134)). Qed.
Lemma lem1960138 (h1 : term65) : term93.
Proof. exact (EQ_MP (@lem1960137) (@lem1959945 h1)). Qed.
Lemma lem1960152 (y : real) (x : real) (z : real) : (term99 y x z) = (term99 y x z).
Proof. exact (eq_refl (term99 y x z)). Qed.
Lemma lem1960153 (y : real) (x : real) : (term101 y x) = (term101 y x).
Proof. exact (fun_ext (fun z : real => @lem1960152 y x z)). Qed.
Lemma lem1960154 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960155 (y : real) (x : real) : (term102 y x) = (term102 y x).
Proof. exact (MK_COMB (@lem1960154) (@lem1960153 y x)). Qed.
Lemma lem1960156 (x : real) : (term103 x) = (term103 x).
Proof. exact (fun_ext (fun y : real => @lem1960155 y x)). Qed.
Lemma lem1960157 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960158 (x : real) : (term104 x) = (term104 x).
Proof. exact (MK_COMB (@lem1960157) (@lem1960156 x)). Qed.
Lemma lem1960159 : term105 = term105.
Proof. exact (fun_ext (fun x : real => @lem1960158 x)). Qed.
Lemma lem1960160 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960162 : term106 = term106.
Proof. exact (MK_COMB (@lem1960160) (@lem1960159)). Qed.
Lemma lem1960163 (h1 : term62) : term106.
Proof. exact (EQ_MP (@lem1960162) (@lem1959980 h1)). Qed.
Lemma lem1960165 (x : real) : (term53 x) = (term53 x).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1960166 : term54 = term54.
Proof. exact (fun_ext (fun x : real => @lem1960165 x)). Qed.
Lemma lem1960167 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960169 : term55 = term55.
Proof. exact (MK_COMB (@lem1960167) (@lem1960166)). Qed.
Lemma lem1960170 (h1 : term55) : term55.
Proof. exact (EQ_MP (@lem1960169) (@lem1959997 h1)). Qed.
Lemma lem1960172 (x : real) : ((term50 x) = (real_mul x x)) = ((term50 x) = (real_mul x x)).
Proof. exact (eq_refl ((term50 x) = (real_mul x x))). Qed.
Lemma lem1960173 : term51 = term51.
Proof. exact (fun_ext (fun x : real => @lem1960172 x)). Qed.
Lemma lem1960174 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960176 : term52 = term52.
Proof. exact (MK_COMB (@lem1960174) (@lem1960173)). Qed.
Lemma lem1960177 (h1 : term52) : term52.
Proof. exact (EQ_MP (@lem1960176) (@lem1960020 h1)). Qed.
Lemma lem1960185 (x : real) : (term107 x) = (term107 x).
Proof. exact (eq_refl (term107 x)). Qed.
Lemma lem1960186 : term109 = term109.
Proof. exact (fun_ext (fun x : real => @lem1960185 x)). Qed.
Lemma lem1960187 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960189 : term110 = term110.
Proof. exact (MK_COMB (@lem1960187) (@lem1960186)). Qed.
Lemma lem1960190 (h1 : term49) : term110.
Proof. exact (EQ_MP (@lem1960189) (@lem1960049 h1)). Qed.
Lemma lem1960198 (x : real) (y : real) : (term111 x y) = (term111 x y).
Proof. exact (eq_refl (term111 x y)). Qed.
Lemma lem1960199 (x : real) : (term113 x) = (term113 x).
Proof. exact (fun_ext (fun y : real => @lem1960198 x y)). Qed.
Lemma lem1960200 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960201 (x : real) : (term114 x) = (term114 x).
Proof. exact (MK_COMB (@lem1960200) (@lem1960199 x)). Qed.
Lemma lem1960202 : term115 = term115.
Proof. exact (fun_ext (fun x : real => @lem1960201 x)). Qed.
Lemma lem1960203 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960205 : term116 = term116.
Proof. exact (MK_COMB (@lem1960203) (@lem1960202)). Qed.
Lemma lem1960206 (h1 : term46) : term116.
Proof. exact (EQ_MP (@lem1960205) (@lem1960075 h1)). Qed.
Lemma lem1960214 (y : real) (x : real) : (term38 y x) = (term38 y x).
Proof. exact (eq_refl (term38 y x)). Qed.
Lemma lem1960215 (x : real) : (term39 x) = (term39 x).
Proof. exact (fun_ext (fun y : real => @lem1960214 y x)). Qed.
Lemma lem1960216 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960217 (x : real) : (term40 x) = (term40 x).
Proof. exact (MK_COMB (@lem1960216) (@lem1960215 x)). Qed.
Lemma lem1960218 : term41 = term41.
Proof. exact (fun_ext (fun x : real => @lem1960217 x)). Qed.
Lemma lem1960219 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1960221 : term17 = term17.
Proof. exact (MK_COMB (@lem1960219) (@lem1960218)). Qed.
Lemma lem1960222 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem1960221) (@lem1960095 h1)). Qed.
Lemma lem1960231 (_27504 : real) (h1 : term65) : term117 _27504.
Proof. exact (@lem1960138 h1 _27504). Qed.
Lemma lem1960232 (_27504 : real) : (term117 _27504) = (term89 _27504).
Proof. exact (eq_refl (term117 _27504)). Qed.
Lemma lem1960234 (_27505 : real) (h1 : term62) : term118 _27505.
Proof. exact (@lem1960163 h1 _27505). Qed.
Lemma lem1960235 (_27505 : real) : (term118 _27505) = (term104 _27505).
Proof. exact (eq_refl (term118 _27505)). Qed.
Lemma lem1960236 (_27505 : real) (h1 : term62) : term104 _27505.
Proof. exact (EQ_MP (@lem1960235 _27505) (@lem1960234 _27505 h1)). Qed.
Lemma lem1960237 (_27505 : real) (_27506 : real) (h1 : term62) : term119 _27505 _27506.
Proof. exact (@lem1960236 _27505 h1 _27506). Qed.
Lemma lem1960238 (_27506 : real) (_27505 : real) : (term119 _27505 _27506) = (term102 _27506 _27505).
Proof. exact (eq_refl (term119 _27505 _27506)). Qed.
Lemma lem1960239 (_27506 : real) (_27505 : real) (h1 : term62) : term102 _27506 _27505.
Proof. exact (EQ_MP (@lem1960238 _27506 _27505) (@lem1960237 _27505 _27506 h1)). Qed.
Lemma lem1960240 (_27506 : real) (_27505 : real) (_27507 : real) (h1 : term62) : term120 _27506 _27505 _27507.
Proof. exact (@lem1960239 _27506 _27505 h1 _27507). Qed.
Lemma lem1960241 (_27506 : real) (_27505 : real) (_27507 : real) : (term120 _27506 _27505 _27507) = (term99 _27506 _27505 _27507).
Proof. exact (eq_refl (term120 _27506 _27505 _27507)). Qed.
Lemma lem1960242 (_27506 : real) (_27505 : real) (_27507 : real) (h1 : term62) : term99 _27506 _27505 _27507.
Proof. exact (EQ_MP (@lem1960241 _27506 _27505 _27507) (@lem1960240 _27506 _27505 _27507 h1)). Qed.
Lemma lem1960243 (_27508 : real) (h1 : term55) : term121 _27508.
Proof. exact (@lem1960170 h1 _27508). Qed.
Lemma lem1960244 (_27508 : real) : (term121 _27508) = (term53 _27508).
Proof. exact (eq_refl (term121 _27508)). Qed.
Lemma lem1960246 (_27509 : real) (h1 : term52) : term122 _27509.
Proof. exact (@lem1960177 h1 _27509). Qed.
Lemma lem1960247 (_27509 : real) : (term122 _27509) = ((term50 _27509) = (real_mul _27509 _27509)).
Proof. exact (eq_refl (term122 _27509)). Qed.
Lemma lem1960249 (_27510 : real) (h1 : term49) : term123 _27510.
Proof. exact (@lem1960190 h1 _27510). Qed.
Lemma lem1960250 (_27510 : real) : (term123 _27510) = (term107 _27510).
Proof. exact (eq_refl (term123 _27510)). Qed.
Lemma lem1960252 (_27511 : real) (h1 : term46) : term124 _27511.
Proof. exact (@lem1960206 h1 _27511). Qed.
Lemma lem1960253 (_27511 : real) : (term124 _27511) = (term114 _27511).
Proof. exact (eq_refl (term124 _27511)). Qed.
Lemma lem1960254 (_27511 : real) (h1 : term46) : term114 _27511.
Proof. exact (EQ_MP (@lem1960253 _27511) (@lem1960252 _27511 h1)). Qed.
Lemma lem1960255 (_27511 : real) (_27512 : real) (h1 : term46) : term125 _27511 _27512.
Proof. exact (@lem1960254 _27511 h1 _27512). Qed.
Lemma lem1960256 (_27511 : real) (_27512 : real) : (term125 _27511 _27512) = (term111 _27511 _27512).
Proof. exact (eq_refl (term125 _27511 _27512)). Qed.
Lemma lem1960258 (_27513 : real) (h1 : term17) : term126 _27513.
Proof. exact (@lem1960222 h1 _27513). Qed.
Lemma lem1960259 (_27513 : real) : (term126 _27513) = (term40 _27513).
Proof. exact (eq_refl (term126 _27513)). Qed.
Lemma lem1960260 (_27513 : real) (h1 : term17) : term40 _27513.
Proof. exact (EQ_MP (@lem1960259 _27513) (@lem1960258 _27513 h1)). Qed.
Lemma lem1960261 (_27513 : real) (_27514 : real) (h1 : term17) : term127 _27513 _27514.
Proof. exact (@lem1960260 _27513 h1 _27514). Qed.
Lemma lem1960262 (_27514 : real) (_27513 : real) : (term127 _27513 _27514) = (term38 _27514 _27513).
Proof. exact (eq_refl (term127 _27513 _27514)). Qed.
Lemma lem1960269 (_27504 : real) (h1 : term65) : term89 _27504.
Proof. exact (EQ_MP (@lem1960232 _27504) (@lem1960231 _27504 h1)). Qed.
Lemma lem1960280 (_27506 : real) (_27505 : real) (_27507 : real) : (term99 _27506 _27505 _27507) = (term128 _27506 _27505 _27507).
Proof. exact (@lem1959054 (term129 _27505 _27506) (term129 _27506 _27507) (real_le _27505 _27507)). Qed.
Lemma lem1960281 (_27506 : real) (_27505 : real) (_27507 : real) (h1 : term62) : term128 _27506 _27505 _27507.
Proof. exact (EQ_MP (@lem1960280 _27506 _27505 _27507) (@lem1960242 _27506 _27505 _27507 h1)). Qed.
Lemma lem1960291 (_27510 : real) (h1 : term49) : term107 _27510.
Proof. exact (EQ_MP (@lem1960250 _27510) (@lem1960249 _27510 h1)). Qed.
Lemma lem1960297 (_27511 : real) (_27512 : real) (h1 : term46) : term111 _27511 _27512.
Proof. exact (EQ_MP (@lem1960256 _27511 _27512) (@lem1960255 _27511 _27512 h1)). Qed.
Lemma lem1960303 (_27514 : real) (_27513 : real) (h1 : term17) : term38 _27514 _27513.
Proof. exact (EQ_MP (@lem1960262 _27514 _27513) (@lem1960261 _27513 _27514 h1)). Qed.
Lemma lem1960307 (x : real) (y : real) (h1 : term71 x y) : term130 x y.
Proof. exact (proj2 (@lem1960123 x y h1)). Qed.
Lemma lem1960308 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1960309 (_27515 : real) (_27517 : real) (h1 : _27515 = _27517) : _27515 = _27517.
Proof. exact (h1). Qed.
Lemma lem1960310 (_27516 : real) (_27518 : real) (h1 : _27516 = _27518) : _27516 = _27518.
Proof. exact (h1). Qed.
Lemma lem1960311 (_27515 : real) (_27517 : real) (h1 : _27515 = _27517) : (real_le _27515) = (real_le _27517).
Proof. exact (MK_COMB (@lem1960308) (@lem1960309 _27515 _27517 h1)). Qed.
Lemma lem1960312 (_27515 : real) (_27517 : real) (_27516 : real) (_27518 : real) (h1 : _27515 = _27517) (h2 : _27516 = _27518) : (real_le _27515 _27516) = (real_le _27517 _27518).
Proof. exact (MK_COMB (@lem1960311 _27515 _27517 h1) (@lem1960310 _27516 _27518 h2)). Qed.
Lemma lem1960314 (b : Prop) (a : Prop) : term131 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1960315 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : term132 _27517 _27518 _27515 _27516.
Proof. exact (@lem1960314 (real_le _27517 _27518) (real_le _27515 _27516)). Qed.
Lemma lem1960316 (_27515 : real) (_27517 : real) (_27516 : real) (_27518 : real) (h1 : _27515 = _27517) (h2 : _27516 = _27518) : term133 _27517 _27518 _27515 _27516.
Proof. exact (@lem1960315 _27517 _27518 _27515 _27516 (@lem1960312 _27515 _27517 _27516 _27518 h1 h2)). Qed.
Lemma lem1960317 (_27518 : real) (_27516 : real) (_27515 : real) (_27517 : real) (h1 : _27515 = _27517) : term134 _27517 _27518 _27515 _27516.
Proof. exact (fun h0 : _27516 = _27518 => @lem1960316 _27515 _27517 _27516 _27518 h1 h0). Qed.
Lemma lem1960319 (a : Prop) (b : Prop) : (a -> b) = (term135 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1960320 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : (term134 _27517 _27518 _27515 _27516) = (term136 _27517 _27518 _27515 _27516).
Proof. exact (@lem1960319 (_27516 = _27518) (term133 _27517 _27518 _27515 _27516)). Qed.
Lemma lem1960321 (_27518 : real) (_27516 : real) (_27515 : real) (_27517 : real) (h1 : _27515 = _27517) : term136 _27517 _27518 _27515 _27516.
Proof. exact (EQ_MP (@lem1960320 _27517 _27518 _27515 _27516) (@lem1960317 _27518 _27516 _27515 _27517 h1)). Qed.
Lemma lem1960322 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : term137 _27517 _27518 _27515 _27516.
Proof. exact (fun h0 : _27515 = _27517 => @lem1960321 _27518 _27516 _27515 _27517 h0). Qed.
Lemma lem1960324 (a : Prop) (b : Prop) : (a -> b) = (term135 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1960325 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : (term137 _27517 _27518 _27515 _27516) = (term138 _27517 _27518 _27515 _27516).
Proof. exact (@lem1960324 (_27515 = _27517) (term136 _27517 _27518 _27515 _27516)). Qed.
Lemma lem1960326 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : term138 _27517 _27518 _27515 _27516.
Proof. exact (EQ_MP (@lem1960325 _27517 _27518 _27515 _27516) (@lem1960322 _27517 _27518 _27515 _27516)). Qed.
Lemma lem1960402 (_27508 : real) (h1 : term55) : term53 _27508.
Proof. exact (EQ_MP (@lem1960244 _27508) (@lem1960243 _27508 h1)). Qed.
Lemma lem1960403 (x : real) (h1 : term55) : term53 x.
Proof. exact (@lem1960402 x h1). Qed.
Lemma lem1960404 (x : real) (h1 : term55) : term139 x.
Proof. exact (fun h0 : term140 x => @lem1960403 x h1). Qed.
Lemma lem1960406 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1960407 (x : real) : (term139 x) = (term53 x).
Proof. exact (@lem1960406 (term53 x)). Qed.
Lemma lem1960408 (x : real) (h1 : term55) : term53 x.
Proof. exact (EQ_MP (@lem1960407 x) (@lem1960404 x h1)). Qed.
Lemma lem1960410 (_27509 : real) (h1 : term52) : (term50 _27509) = (real_mul _27509 _27509).
Proof. exact (EQ_MP (@lem1960247 _27509) (@lem1960246 _27509 h1)). Qed.
Lemma lem1960411 (x : real) (h1 : term52) : (term50 x) = (real_mul x x).
Proof. exact (@lem1960410 x h1). Qed.
Lemma lem1960412 (x : real) (h1 : term52) : term142 x.
Proof. exact (fun h0 : term143 x => @lem1960411 x h1). Qed.
Lemma lem1960414 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1960415 (x : real) : (term142 x) = ((term50 x) = (real_mul x x)).
Proof. exact (@lem1960414 ((term50 x) = (real_mul x x))). Qed.
Lemma lem1960416 (x : real) (h1 : term52) : (term50 x) = (real_mul x x).
Proof. exact (EQ_MP (@lem1960415 x) (@lem1960412 x h1)). Qed.
Lemma lem1960418 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1960419 (y : real) : y = y.
Proof. exact (@lem1960418 y). Qed.
Lemma lem1960420 (y : real) : term144 y.
Proof. exact (fun h0 : term145 y => @lem1960419 y). Qed.
Lemma lem1960422 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1960423 (y : real) : (term144 y) = (y = y).
Proof. exact (@lem1960422 (y = y)). Qed.
Lemma lem1960424 (y : real) : y = y.
Proof. exact (EQ_MP (@lem1960423 y) (@lem1960420 y)). Qed.
Lemma lem1960426 (x : real) (y : real) (h1 : term71 x y) : term72 x y.
Proof. exact (proj1 (@lem1960123 x y h1)). Qed.
Lemma lem1960427 (x : real) (y : real) (h1 : term71 x y) : term146 x y.
Proof. exact (fun h0 : term147 x y => @lem1960426 x y h1). Qed.
Lemma lem1960429 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1960430 (x : real) (y : real) : (term146 x y) = (term72 x y).
Proof. exact (@lem1960429 (term72 x y)). Qed.
Lemma lem1960431 (x : real) (y : real) (h1 : term71 x y) : term72 x y.
Proof. exact (EQ_MP (@lem1960430 x y) (@lem1960427 x y h1)). Qed.
Lemma lem1960449 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1960450 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : (term136 _27517 _27518 _27515 _27516) = (term148 _27517 _27518 _27515 _27516).
Proof. exact (@lem1960449 (real_le _27517 _27518) (term149 _27516 _27518) (term129 _27515 _27516)). Qed.
Lemma lem1960468 (_27515 : real) (_27517 : real) : (term150 _27515 _27517) = (term150 _27515 _27517).
Proof. exact (eq_refl (term150 _27515 _27517)). Qed.
Lemma lem1960469 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : (term138 _27517 _27518 _27515 _27516) = (term151 _27517 _27518 _27515 _27516).
Proof. exact (MK_COMB (@lem1960468 _27515 _27517) (@lem1960450 _27517 _27518 _27515 _27516)). Qed.
Lemma lem1960473 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1960474 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : (term151 _27517 _27518 _27515 _27516) = (term152 _27517 _27518 _27515 _27516).
Proof. exact (@lem1960473 (real_le _27517 _27518) (term149 _27515 _27517) (term153 _27518 _27515 _27516)). Qed.
Lemma lem1960504 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : (term138 _27517 _27518 _27515 _27516) = (term152 _27517 _27518 _27515 _27516).
Proof. exact (TRANS (@lem1960469 _27517 _27518 _27515 _27516) (@lem1960474 _27517 _27518 _27515 _27516)). Qed.
Lemma lem1960505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1960506 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : (term154 _27517 _27518 _27515 _27516) = (term155 _27517 _27518 _27515 _27516).
Proof. exact (MK_COMB (@lem1960505) (@lem1960504 _27517 _27518 _27515 _27516)). Qed.
Lemma lem1960536 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : (term152 _27517 _27518 _27515 _27516) = (term152 _27517 _27518 _27515 _27516).
Proof. exact (eq_refl (term152 _27517 _27518 _27515 _27516)). Qed.
Lemma lem1960537 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : ((term138 _27517 _27518 _27515 _27516) = (term152 _27517 _27518 _27515 _27516)) = ((term152 _27517 _27518 _27515 _27516) = (term152 _27517 _27518 _27515 _27516)).
Proof. exact (MK_COMB (@lem1960506 _27517 _27518 _27515 _27516) (@lem1960536 _27517 _27518 _27515 _27516)). Qed.
Lemma lem1960539 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1960540 (x : Prop) : (x = x) = True.
Proof. exact (@lem1960539 Prop x). Qed.
Lemma lem1960541 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : ((term152 _27517 _27518 _27515 _27516) = (term152 _27517 _27518 _27515 _27516)) = True.
Proof. exact (@lem1960540 (term152 _27517 _27518 _27515 _27516)). Qed.
Lemma lem1960542 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : ((term138 _27517 _27518 _27515 _27516) = (term152 _27517 _27518 _27515 _27516)) = True.
Proof. exact (TRANS (@lem1960537 _27517 _27518 _27515 _27516) (@lem1960541 _27517 _27518 _27515 _27516)). Qed.
Lemma lem1960543 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : True = ((term138 _27517 _27518 _27515 _27516) = (term152 _27517 _27518 _27515 _27516)).
Proof. exact (SYM (@lem1960542 _27517 _27518 _27515 _27516)). Qed.
Lemma lem1960544 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : (term138 _27517 _27518 _27515 _27516) = (term152 _27517 _27518 _27515 _27516).
Proof. exact (EQ_MP (@lem1960543 _27517 _27518 _27515 _27516) (@lem0)). Qed.
Lemma lem1960545 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : term152 _27517 _27518 _27515 _27516.
Proof. exact (EQ_MP (@lem1960544 _27517 _27518 _27515 _27516) (@lem1960326 _27517 _27518 _27515 _27516)). Qed.
Lemma lem1960547 (b : Prop) (a : Prop) : (a \/ b) = (term156 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1960548 (_27515 : real) (_27516 : real) (_27517 : real) (_27518 : real) : (term152 _27517 _27518 _27515 _27516) = (term157 _27515 _27516 _27517 _27518).
Proof. exact (@lem1960547 (term158 _27517 _27518 _27515 _27516) (real_le _27517 _27518)). Qed.
Lemma lem1960550 (a : Prop) (b : Prop) : (term159 a b) = (term160 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1960551 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : (term161 _27517 _27518 _27515 _27516) = (term162 _27517 _27518 _27515 _27516).
Proof. exact (@lem1960550 (term149 _27515 _27517) (term153 _27518 _27515 _27516)). Qed.
Lemma lem1960553 (a : Prop) : (term163 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1960554 (_27515 : real) (_27517 : real) : (term164 _27515 _27517) = (_27515 = _27517).
Proof. exact (@lem1960553 (_27515 = _27517)). Qed.
Lemma lem1960555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1960556 (_27515 : real) (_27517 : real) : (term165 _27515 _27517) = (term166 _27515 _27517).
Proof. exact (MK_COMB (@lem1960555) (@lem1960554 _27515 _27517)). Qed.
Lemma lem1960558 (a : Prop) (b : Prop) : (term159 a b) = (term160 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1960559 (_27518 : real) (_27515 : real) (_27516 : real) : (term167 _27518 _27515 _27516) = (term168 _27518 _27515 _27516).
Proof. exact (@lem1960558 (term149 _27516 _27518) (term129 _27515 _27516)). Qed.
Lemma lem1960561 (a : Prop) : (term163 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1960562 (_27516 : real) (_27518 : real) : (term164 _27516 _27518) = (_27516 = _27518).
Proof. exact (@lem1960561 (_27516 = _27518)). Qed.
Lemma lem1960563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1960564 (_27516 : real) (_27518 : real) : (term165 _27516 _27518) = (term166 _27516 _27518).
Proof. exact (MK_COMB (@lem1960563) (@lem1960562 _27516 _27518)). Qed.
Lemma lem1960566 (a : Prop) : (term163 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1960567 (_27515 : real) (_27516 : real) : (term169 _27515 _27516) = (real_le _27515 _27516).
Proof. exact (@lem1960566 (real_le _27515 _27516)). Qed.
Lemma lem1960568 (_27518 : real) (_27515 : real) (_27516 : real) : (term168 _27518 _27515 _27516) = (term170 _27518 _27515 _27516).
Proof. exact (MK_COMB (@lem1960564 _27516 _27518) (@lem1960567 _27515 _27516)). Qed.
Lemma lem1960569 (_27518 : real) (_27515 : real) (_27516 : real) : (term167 _27518 _27515 _27516) = (term170 _27518 _27515 _27516).
Proof. exact (TRANS (@lem1960559 _27518 _27515 _27516) (@lem1960568 _27518 _27515 _27516)). Qed.
Lemma lem1960570 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : (term162 _27517 _27518 _27515 _27516) = (term171 _27517 _27518 _27515 _27516).
Proof. exact (MK_COMB (@lem1960556 _27515 _27517) (@lem1960569 _27518 _27515 _27516)). Qed.
Lemma lem1960571 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : (term161 _27517 _27518 _27515 _27516) = (term171 _27517 _27518 _27515 _27516).
Proof. exact (TRANS (@lem1960551 _27517 _27518 _27515 _27516) (@lem1960570 _27517 _27518 _27515 _27516)). Qed.
Lemma lem1960572 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1960573 (_27517 : real) (_27518 : real) (_27515 : real) (_27516 : real) : (term172 _27517 _27518 _27515 _27516) = (term173 _27517 _27518 _27515 _27516).
Proof. exact (MK_COMB (@lem1960572) (@lem1960571 _27517 _27518 _27515 _27516)). Qed.
Lemma lem1960574 (_27517 : real) (_27518 : real) : (real_le _27517 _27518) = (real_le _27517 _27518).
Proof. exact (eq_refl (real_le _27517 _27518)). Qed.
Lemma lem1960575 (_27515 : real) (_27516 : real) (_27517 : real) (_27518 : real) : (term157 _27515 _27516 _27517 _27518) = (term174 _27515 _27516 _27517 _27518).
Proof. exact (MK_COMB (@lem1960573 _27517 _27518 _27515 _27516) (@lem1960574 _27517 _27518)). Qed.
Lemma lem1960576 (_27515 : real) (_27516 : real) (_27517 : real) (_27518 : real) : (term152 _27517 _27518 _27515 _27516) = (term174 _27515 _27516 _27517 _27518).
Proof. exact (TRANS (@lem1960548 _27515 _27516 _27517 _27518) (@lem1960575 _27515 _27516 _27517 _27518)). Qed.
Lemma lem1960578 (x : real) (y : real) (h1 : term71 x y) : term175 x y.
Proof. exact (conj (@lem1960424 y) (@lem1960431 x y h1)). Qed.
Lemma lem1960579 (x : real) (y : real) (h1 : term52) (h2 : term71 x y) : term176 x y.
Proof. exact (conj (@lem1960416 x h1) (@lem1960578 x y h2)). Qed.
Lemma lem1960581 (_27515 : real) (_27516 : real) (_27517 : real) (_27518 : real) : term174 _27515 _27516 _27517 _27518.
Proof. exact (EQ_MP (@lem1960576 _27515 _27516 _27517 _27518) (@lem1960545 _27517 _27518 _27515 _27516)). Qed.
Lemma lem1960582 (x : real) (y : real) : term177 x y.
Proof. exact (@lem1960581 (term50 x) y (real_mul x x) y). Qed.
Lemma lem1960585 (x : real) (y : real) (h1 : term52) (h2 : term71 x y) : term178 x y.
Proof. exact (@lem1960582 x y (@lem1960579 x y h1 h2)). Qed.
Lemma lem1960586 (x : real) (y : real) (h1 : term52) (h2 : term71 x y) : term179 x y.
Proof. exact (fun h0 : term180 x y => @lem1960585 x y h1 h2). Qed.
Lemma lem1960588 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1960589 (x : real) (y : real) : (term179 x y) = (term178 x y).
Proof. exact (@lem1960588 (term178 x y)). Qed.
Lemma lem1960590 (x : real) (y : real) (h1 : term52) (h2 : term71 x y) : term178 x y.
Proof. exact (EQ_MP (@lem1960589 x y) (@lem1960586 x y h1 h2)). Qed.
Lemma lem1960606 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1960607 (_27505 : real) (_27506 : real) (_27507 : real) : (term181 _27506 _27505 _27507) = (term182 _27505 _27506 _27507).
Proof. exact (@lem1960606 (real_le _27505 _27507) (term129 _27506 _27507)). Qed.
Lemma lem1960613 (_27505 : real) (_27506 : real) : (term183 _27505 _27506) = (term183 _27505 _27506).
Proof. exact (eq_refl (term183 _27505 _27506)). Qed.
Lemma lem1960614 (_27505 : real) (_27506 : real) (_27507 : real) : (term128 _27506 _27505 _27507) = (term184 _27505 _27506 _27507).
Proof. exact (MK_COMB (@lem1960613 _27505 _27506) (@lem1960607 _27505 _27506 _27507)). Qed.
Lemma lem1960618 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1960619 (_27505 : real) (_27506 : real) (_27507 : real) : (term184 _27505 _27506 _27507) = (term185 _27505 _27506 _27507).
Proof. exact (@lem1960618 (real_le _27505 _27507) (term129 _27505 _27506) (term129 _27506 _27507)). Qed.
Lemma lem1960635 (_27505 : real) (_27506 : real) (_27507 : real) : (term128 _27506 _27505 _27507) = (term185 _27505 _27506 _27507).
Proof. exact (TRANS (@lem1960614 _27505 _27506 _27507) (@lem1960619 _27505 _27506 _27507)). Qed.
Lemma lem1960636 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1960637 (_27505 : real) (_27506 : real) (_27507 : real) : (term186 _27506 _27505 _27507) = (term187 _27505 _27506 _27507).
Proof. exact (MK_COMB (@lem1960636) (@lem1960635 _27505 _27506 _27507)). Qed.
Lemma lem1960653 (_27505 : real) (_27506 : real) (_27507 : real) : (term185 _27505 _27506 _27507) = (term185 _27505 _27506 _27507).
Proof. exact (eq_refl (term185 _27505 _27506 _27507)). Qed.
Lemma lem1960654 (_27505 : real) (_27506 : real) (_27507 : real) : ((term128 _27506 _27505 _27507) = (term185 _27505 _27506 _27507)) = ((term185 _27505 _27506 _27507) = (term185 _27505 _27506 _27507)).
Proof. exact (MK_COMB (@lem1960637 _27505 _27506 _27507) (@lem1960653 _27505 _27506 _27507)). Qed.
Lemma lem1960656 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1960657 (x : Prop) : (x = x) = True.
Proof. exact (@lem1960656 Prop x). Qed.
Lemma lem1960658 (_27505 : real) (_27506 : real) (_27507 : real) : ((term185 _27505 _27506 _27507) = (term185 _27505 _27506 _27507)) = True.
Proof. exact (@lem1960657 (term185 _27505 _27506 _27507)). Qed.
Lemma lem1960659 (_27505 : real) (_27506 : real) (_27507 : real) : ((term128 _27506 _27505 _27507) = (term185 _27505 _27506 _27507)) = True.
Proof. exact (TRANS (@lem1960654 _27505 _27506 _27507) (@lem1960658 _27505 _27506 _27507)). Qed.
Lemma lem1960660 (_27505 : real) (_27506 : real) (_27507 : real) : True = ((term128 _27506 _27505 _27507) = (term185 _27505 _27506 _27507)).
Proof. exact (SYM (@lem1960659 _27505 _27506 _27507)). Qed.
Lemma lem1960661 (_27505 : real) (_27506 : real) (_27507 : real) : (term128 _27506 _27505 _27507) = (term185 _27505 _27506 _27507).
Proof. exact (EQ_MP (@lem1960660 _27505 _27506 _27507) (@lem0)). Qed.
Lemma lem1960662 (_27505 : real) (_27506 : real) (_27507 : real) (h1 : term62) : term185 _27505 _27506 _27507.
Proof. exact (EQ_MP (@lem1960661 _27505 _27506 _27507) (@lem1960281 _27506 _27505 _27507 h1)). Qed.
Lemma lem1960664 (b : Prop) (a : Prop) : (a \/ b) = (term156 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1960665 (_27506 : real) (_27505 : real) (_27507 : real) : (term185 _27505 _27506 _27507) = (term188 _27506 _27505 _27507).
Proof. exact (@lem1960664 (term95 _27505 _27506 _27507) (real_le _27505 _27507)). Qed.
Lemma lem1960667 (a : Prop) (b : Prop) : (term159 a b) = (term160 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1960668 (_27505 : real) (_27506 : real) (_27507 : real) : (term189 _27505 _27506 _27507) = (term190 _27505 _27506 _27507).
Proof. exact (@lem1960667 (term129 _27505 _27506) (term129 _27506 _27507)). Qed.
Lemma lem1960670 (a : Prop) : (term163 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1960671 (_27505 : real) (_27506 : real) : (term169 _27505 _27506) = (real_le _27505 _27506).
Proof. exact (@lem1960670 (real_le _27505 _27506)). Qed.
Lemma lem1960672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1960673 (_27505 : real) (_27506 : real) : (term191 _27505 _27506) = (term192 _27505 _27506).
Proof. exact (MK_COMB (@lem1960672) (@lem1960671 _27505 _27506)). Qed.
Lemma lem1960675 (a : Prop) : (term163 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1960676 (_27506 : real) (_27507 : real) : (term169 _27506 _27507) = (real_le _27506 _27507).
Proof. exact (@lem1960675 (real_le _27506 _27507)). Qed.
Lemma lem1960677 (_27505 : real) (_27506 : real) (_27507 : real) : (term190 _27505 _27506 _27507) = (term100 _27505 _27506 _27507).
Proof. exact (MK_COMB (@lem1960673 _27505 _27506) (@lem1960676 _27506 _27507)). Qed.
Lemma lem1960678 (_27505 : real) (_27506 : real) (_27507 : real) : (term189 _27505 _27506 _27507) = (term100 _27505 _27506 _27507).
Proof. exact (TRANS (@lem1960668 _27505 _27506 _27507) (@lem1960677 _27505 _27506 _27507)). Qed.
Lemma lem1960679 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1960680 (_27505 : real) (_27506 : real) (_27507 : real) : (term193 _27505 _27506 _27507) = (term194 _27505 _27506 _27507).
Proof. exact (MK_COMB (@lem1960679) (@lem1960678 _27505 _27506 _27507)). Qed.
Lemma lem1960681 (_27505 : real) (_27507 : real) : (real_le _27505 _27507) = (real_le _27505 _27507).
Proof. exact (eq_refl (real_le _27505 _27507)). Qed.
Lemma lem1960682 (_27506 : real) (_27505 : real) (_27507 : real) : (term188 _27506 _27505 _27507) = (term56 _27506 _27505 _27507).
Proof. exact (MK_COMB (@lem1960680 _27505 _27506 _27507) (@lem1960681 _27505 _27507)). Qed.
Lemma lem1960683 (_27506 : real) (_27505 : real) (_27507 : real) : (term185 _27505 _27506 _27507) = (term56 _27506 _27505 _27507).
Proof. exact (TRANS (@lem1960665 _27506 _27505 _27507) (@lem1960682 _27506 _27505 _27507)). Qed.
Lemma lem1960685 (x : real) (y : real) (h1 : term52) (h2 : term55) (h3 : term71 x y) : term195 x y.
Proof. exact (conj (@lem1960408 x h2) (@lem1960590 x y h1 h3)). Qed.
Lemma lem1960687 (_27506 : real) (_27505 : real) (_27507 : real) (h1 : term62) : term56 _27506 _27505 _27507.
Proof. exact (EQ_MP (@lem1960683 _27506 _27505 _27507) (@lem1960662 _27505 _27506 _27507 h1)). Qed.
Lemma lem1960688 (x : real) (y : real) (h1 : term62) : term196 x y.
Proof. exact (@lem1960687 (real_mul x x) term197 y h1). Qed.
Lemma lem1960691 (x : real) (y : real) (h1 : term62) (h2 : term52) (h3 : term55) (h4 : term71 x y) : term90 y.
Proof. exact (@lem1960688 x y h1 (@lem1960685 x y h2 h3 h4)). Qed.
Lemma lem1960692 (x : real) (y : real) (h1 : term62) (h2 : term52) (h3 : term55) (h4 : term71 x y) : term198 y.
Proof. exact (fun h0 : term199 y => @lem1960691 x y h1 h2 h3 h4). Qed.
Lemma lem1960694 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1960695 (y : real) : (term198 y) = (term90 y).
Proof. exact (@lem1960694 (term90 y)). Qed.
Lemma lem1960696 (x : real) (y : real) (h1 : term62) (h2 : term52) (h3 : term55) (h4 : term71 x y) : term90 y.
Proof. exact (EQ_MP (@lem1960695 y) (@lem1960692 x y h1 h2 h3 h4)). Qed.
Lemma lem1960702 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1960703 (_27510 : real) : (term107 _27510) = (term200 _27510).
Proof. exact (@lem1960702 (term108 _27510) (term199 _27510)). Qed.
Lemma lem1960709 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1960710 (_27510 : real) : (term201 _27510) = (term202 _27510).
Proof. exact (MK_COMB (@lem1960709) (@lem1960703 _27510)). Qed.
Lemma lem1960716 (_27510 : real) : (term200 _27510) = (term200 _27510).
Proof. exact (eq_refl (term200 _27510)). Qed.
Lemma lem1960717 (_27510 : real) : ((term107 _27510) = (term200 _27510)) = ((term200 _27510) = (term200 _27510)).
Proof. exact (MK_COMB (@lem1960710 _27510) (@lem1960716 _27510)). Qed.
Lemma lem1960719 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1960720 (x : Prop) : (x = x) = True.
Proof. exact (@lem1960719 Prop x). Qed.
Lemma lem1960721 (_27510 : real) : ((term200 _27510) = (term200 _27510)) = True.
Proof. exact (@lem1960720 (term200 _27510)). Qed.
Lemma lem1960722 (_27510 : real) : ((term107 _27510) = (term200 _27510)) = True.
Proof. exact (TRANS (@lem1960717 _27510) (@lem1960721 _27510)). Qed.
Lemma lem1960723 (_27510 : real) : True = ((term107 _27510) = (term200 _27510)).
Proof. exact (SYM (@lem1960722 _27510)). Qed.
Lemma lem1960724 (_27510 : real) : (term107 _27510) = (term200 _27510).
Proof. exact (EQ_MP (@lem1960723 _27510) (@lem0)). Qed.
Lemma lem1960725 (_27510 : real) (h1 : term49) : term200 _27510.
Proof. exact (EQ_MP (@lem1960724 _27510) (@lem1960291 _27510 h1)). Qed.
Lemma lem1960727 (b : Prop) (a : Prop) : (a \/ b) = (term156 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1960728 (_27510 : real) : (term200 _27510) = (term203 _27510).
Proof. exact (@lem1960727 (term199 _27510) (term108 _27510)). Qed.
Lemma lem1960730 (a : Prop) : (term163 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1960731 (_27510 : real) : (term204 _27510) = (term90 _27510).
Proof. exact (@lem1960730 (term90 _27510)). Qed.
Lemma lem1960732 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1960733 (_27510 : real) : (term205 _27510) = (term206 _27510).
Proof. exact (MK_COMB (@lem1960732) (@lem1960731 _27510)). Qed.
Lemma lem1960734 (_27510 : real) : (term108 _27510) = (term108 _27510).
Proof. exact (eq_refl (term108 _27510)). Qed.
Lemma lem1960735 (_27510 : real) : (term203 _27510) = (term47 _27510).
Proof. exact (MK_COMB (@lem1960733 _27510) (@lem1960734 _27510)). Qed.
Lemma lem1960736 (_27510 : real) : (term200 _27510) = (term47 _27510).
Proof. exact (TRANS (@lem1960728 _27510) (@lem1960735 _27510)). Qed.
Lemma lem1960739 (_27510 : real) (h1 : term49) : term47 _27510.
Proof. exact (EQ_MP (@lem1960736 _27510) (@lem1960725 _27510 h1)). Qed.
Lemma lem1960740 (y : real) (h1 : term49) : term47 y.
Proof. exact (@lem1960739 y h1). Qed.
Lemma lem1960743 (x : real) (y : real) (h1 : term62) (h2 : term52) (h3 : term49) (h4 : term55) (h5 : term71 x y) : term108 y.
Proof. exact (@lem1960740 y h3 (@lem1960696 x y h1 h2 h4 h5)). Qed.
Lemma lem1960744 (x : real) (y : real) (h1 : term62) (h2 : term52) (h3 : term49) (h4 : term55) (h5 : term71 x y) : term207 y.
Proof. exact (fun h0 : term208 y => @lem1960743 x y h1 h2 h3 h4 h5). Qed.
Lemma lem1960746 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1960747 (y : real) : (term207 y) = (term108 y).
Proof. exact (@lem1960746 (term108 y)). Qed.
Lemma lem1960748 (x : real) (y : real) (h1 : term62) (h2 : term52) (h3 : term49) (h4 : term55) (h5 : term71 x y) : term108 y.
Proof. exact (EQ_MP (@lem1960747 y) (@lem1960744 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1960751 (x : real) (y : real) (h1 : term130 x y) : term130 x y.
Proof. exact (h1). Qed.
Lemma lem1960752 (x : real) (y : real) (h1 : term130 x y) : term209 x y.
Proof. exact (fun h0 : term73 x y => @lem1960751 x y h1). Qed.
Lemma lem1960754 (p : Prop) : (term210 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1960755 (x : real) (y : real) : (term209 x y) = (term130 x y).
Proof. exact (@lem1960754 (term73 x y)). Qed.
Lemma lem1960756 (x : real) (y : real) (h1 : term130 x y) : term130 x y.
Proof. exact (EQ_MP (@lem1960755 x y) (@lem1960752 x y h1)). Qed.
Lemma lem1960758 (b : Prop) (a : Prop) : (a \/ b) = (term156 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1960759 (_27507 : real) (_27505 : real) (_27506 : real) : (term128 _27506 _27505 _27507) = (term211 _27507 _27505 _27506).
Proof. exact (@lem1960758 (term181 _27506 _27505 _27507) (term129 _27505 _27506)). Qed.
Lemma lem1960761 (a : Prop) (b : Prop) : (term159 a b) = (term160 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1960762 (_27506 : real) (_27505 : real) (_27507 : real) : (term212 _27506 _27505 _27507) = (term213 _27506 _27505 _27507).
Proof. exact (@lem1960761 (term129 _27506 _27507) (real_le _27505 _27507)). Qed.
Lemma lem1960764 (a : Prop) : (term163 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1960765 (_27506 : real) (_27507 : real) : (term169 _27506 _27507) = (real_le _27506 _27507).
Proof. exact (@lem1960764 (real_le _27506 _27507)). Qed.
Lemma lem1960766 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1960767 (_27506 : real) (_27507 : real) : (term191 _27506 _27507) = (term192 _27506 _27507).
Proof. exact (MK_COMB (@lem1960766) (@lem1960765 _27506 _27507)). Qed.
Lemma lem1960768 (_27505 : real) (_27507 : real) : (term129 _27505 _27507) = (term129 _27505 _27507).
Proof. exact (eq_refl (term129 _27505 _27507)). Qed.
Lemma lem1960769 (_27506 : real) (_27505 : real) (_27507 : real) : (term213 _27506 _27505 _27507) = (term214 _27506 _27505 _27507).
Proof. exact (MK_COMB (@lem1960767 _27506 _27507) (@lem1960768 _27505 _27507)). Qed.
Lemma lem1960770 (_27506 : real) (_27505 : real) (_27507 : real) : (term212 _27506 _27505 _27507) = (term214 _27506 _27505 _27507).
Proof. exact (TRANS (@lem1960762 _27506 _27505 _27507) (@lem1960769 _27506 _27505 _27507)). Qed.
Lemma lem1960771 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1960772 (_27506 : real) (_27505 : real) (_27507 : real) : (term215 _27506 _27505 _27507) = (term216 _27506 _27505 _27507).
Proof. exact (MK_COMB (@lem1960771) (@lem1960770 _27506 _27505 _27507)). Qed.
Lemma lem1960773 (_27505 : real) (_27506 : real) : (term129 _27505 _27506) = (term129 _27505 _27506).
Proof. exact (eq_refl (term129 _27505 _27506)). Qed.
Lemma lem1960774 (_27507 : real) (_27505 : real) (_27506 : real) : (term211 _27507 _27505 _27506) = (term217 _27507 _27505 _27506).
Proof. exact (MK_COMB (@lem1960772 _27506 _27505 _27507) (@lem1960773 _27505 _27506)). Qed.
Lemma lem1960775 (_27507 : real) (_27505 : real) (_27506 : real) : (term128 _27506 _27505 _27507) = (term217 _27507 _27505 _27506).
Proof. exact (TRANS (@lem1960759 _27507 _27505 _27506) (@lem1960774 _27507 _27505 _27506)). Qed.
Lemma lem1960777 (x : real) (y : real) (h1 : term62) (h2 : term52) (h3 : term49) (h4 : term55) (h5 : term130 x y) (h6 : term71 x y) : term218 x y.
Proof. exact (conj (@lem1960748 x y h1 h2 h3 h4 h6) (@lem1960756 x y h5)). Qed.
Lemma lem1960779 (_27507 : real) (_27505 : real) (_27506 : real) (h1 : term62) : term217 _27507 _27505 _27506.
Proof. exact (EQ_MP (@lem1960775 _27507 _27505 _27506) (@lem1960281 _27506 _27505 _27507 h1)). Qed.
Lemma lem1960780 (y : real) (x : real) (h1 : term62) : term219 y x.
Proof. exact (@lem1960779 (sqrt y) x term197 h1). Qed.
Lemma lem1960783 (x : real) (y : real) (h1 : term62) (h2 : term52) (h3 : term49) (h4 : term55) (h5 : term130 x y) (h6 : term71 x y) : term220 x.
Proof. exact (@lem1960780 y x h1 (@lem1960777 x y h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1960784 (x : real) (y : real) (h1 : term62) (h2 : term52) (h3 : term49) (h4 : term55) (h5 : term130 x y) (h6 : term71 x y) : term221 x.
Proof. exact (fun h0 : term222 x => @lem1960783 x y h1 h2 h3 h4 h5 h6). Qed.
Lemma lem1960786 (p : Prop) : (term210 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1960787 (x : real) : (term221 x) = (term220 x).
Proof. exact (@lem1960786 (term222 x)). Qed.
Lemma lem1960788 (x : real) (y : real) (h1 : term62) (h2 : term52) (h3 : term49) (h4 : term55) (h5 : term130 x y) (h6 : term71 x y) : term220 x.
Proof. exact (EQ_MP (@lem1960787 x) (@lem1960784 x y h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1960799 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1960800 (_27514 : real) (_27513 : real) : (term38 _27513 _27514) = (term38 _27514 _27513).
Proof. exact (@lem1960799 (real_le _27513 _27514) (real_le _27514 _27513)). Qed.
Lemma lem1960806 (_27514 : real) (_27513 : real) : (term223 _27514 _27513) = (term223 _27514 _27513).
Proof. exact (eq_refl (term223 _27514 _27513)). Qed.
Lemma lem1960807 (_27514 : real) (_27513 : real) : ((term38 _27514 _27513) = (term38 _27513 _27514)) = ((term38 _27514 _27513) = (term38 _27514 _27513)).
Proof. exact (MK_COMB (@lem1960806 _27514 _27513) (@lem1960800 _27514 _27513)). Qed.
Lemma lem1960809 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1960810 (x : Prop) : (x = x) = True.
Proof. exact (@lem1960809 Prop x). Qed.
Lemma lem1960811 (_27514 : real) (_27513 : real) : ((term38 _27514 _27513) = (term38 _27514 _27513)) = True.
Proof. exact (@lem1960810 (term38 _27514 _27513)). Qed.
Lemma lem1960812 (_27513 : real) (_27514 : real) : ((term38 _27514 _27513) = (term38 _27513 _27514)) = True.
Proof. exact (TRANS (@lem1960807 _27514 _27513) (@lem1960811 _27514 _27513)). Qed.
Lemma lem1960813 (_27513 : real) (_27514 : real) : True = ((term38 _27514 _27513) = (term38 _27513 _27514)).
Proof. exact (SYM (@lem1960812 _27513 _27514)). Qed.
Lemma lem1960814 (_27513 : real) (_27514 : real) : (term38 _27514 _27513) = (term38 _27513 _27514).
Proof. exact (EQ_MP (@lem1960813 _27513 _27514) (@lem0)). Qed.
Lemma lem1960815 (_27513 : real) (_27514 : real) (h1 : term17) : term38 _27513 _27514.
Proof. exact (EQ_MP (@lem1960814 _27513 _27514) (@lem1960303 _27514 _27513 h1)). Qed.
Lemma lem1960817 (b : Prop) (a : Prop) : (a \/ b) = (term156 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1960820 (_27514 : real) (_27513 : real) : (term38 _27513 _27514) = (term224 _27514 _27513).
Proof. exact (@lem1960817 (real_le _27513 _27514) (real_le _27514 _27513)). Qed.
Lemma lem1960823 (_27514 : real) (_27513 : real) (h1 : term17) : term224 _27514 _27513.
Proof. exact (EQ_MP (@lem1960820 _27514 _27513) (@lem1960815 _27513 _27514 h1)). Qed.
Lemma lem1960824 (x : real) (h1 : term17) : term225 x.
Proof. exact (@lem1960823 term197 x h1). Qed.
Lemma lem1960827 (x : real) (y : real) (h1 : term62) (h2 : term17) (h3 : term52) (h4 : term49) (h5 : term55) (h6 : term130 x y) (h7 : term71 x y) : term90 x.
Proof. exact (@lem1960824 x h2 (@lem1960788 x y h1 h3 h4 h5 h6 h7)). Qed.
Lemma lem1960828 (x : real) (y : real) (h1 : term62) (h2 : term17) (h3 : term52) (h4 : term49) (h5 : term55) (h6 : term130 x y) (h7 : term71 x y) : term198 x.
Proof. exact (fun h0 : term199 x => @lem1960827 x y h1 h2 h3 h4 h5 h6 h7). Qed.
Lemma lem1960830 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1960831 (x : real) : (term198 x) = (term90 x).
Proof. exact (@lem1960830 (term90 x)). Qed.
Lemma lem1960832 (x : real) (y : real) (h1 : term62) (h2 : term17) (h3 : term52) (h4 : term49) (h5 : term55) (h6 : term130 x y) (h7 : term71 x y) : term90 x.
Proof. exact (EQ_MP (@lem1960831 x) (@lem1960828 x y h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem1960838 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1960839 (_27504 : real) : (term89 _27504) = (term226 _27504).
Proof. exact (@lem1960838 ((term91 _27504) = _27504) (term199 _27504)). Qed.
Lemma lem1960847 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1960848 (_27504 : real) : (term227 _27504) = (term228 _27504).
Proof. exact (MK_COMB (@lem1960847) (@lem1960839 _27504)). Qed.
Lemma lem1960856 (_27504 : real) : (term226 _27504) = (term226 _27504).
Proof. exact (eq_refl (term226 _27504)). Qed.
Lemma lem1960857 (_27504 : real) : ((term89 _27504) = (term226 _27504)) = ((term226 _27504) = (term226 _27504)).
Proof. exact (MK_COMB (@lem1960848 _27504) (@lem1960856 _27504)). Qed.
Lemma lem1960859 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1960860 (x : Prop) : (x = x) = True.
Proof. exact (@lem1960859 Prop x). Qed.
Lemma lem1960861 (_27504 : real) : ((term226 _27504) = (term226 _27504)) = True.
Proof. exact (@lem1960860 (term226 _27504)). Qed.
Lemma lem1960862 (_27504 : real) : ((term89 _27504) = (term226 _27504)) = True.
Proof. exact (TRANS (@lem1960857 _27504) (@lem1960861 _27504)). Qed.
Lemma lem1960863 (_27504 : real) : True = ((term89 _27504) = (term226 _27504)).
Proof. exact (SYM (@lem1960862 _27504)). Qed.
Lemma lem1960864 (_27504 : real) : (term89 _27504) = (term226 _27504).
Proof. exact (EQ_MP (@lem1960863 _27504) (@lem0)). Qed.
Lemma lem1960865 (_27504 : real) (h1 : term65) : term226 _27504.
Proof. exact (EQ_MP (@lem1960864 _27504) (@lem1960269 _27504 h1)). Qed.
Lemma lem1960867 (b : Prop) (a : Prop) : (a \/ b) = (term156 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1960868 (_27504 : real) : (term226 _27504) = (term229 _27504).
Proof. exact (@lem1960867 (term199 _27504) ((term91 _27504) = _27504)). Qed.
Lemma lem1960870 (a : Prop) : (term163 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1960871 (_27504 : real) : (term204 _27504) = (term90 _27504).
Proof. exact (@lem1960870 (term90 _27504)). Qed.
Lemma lem1960872 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1960873 (_27504 : real) : (term205 _27504) = (term206 _27504).
Proof. exact (MK_COMB (@lem1960872) (@lem1960871 _27504)). Qed.
Lemma lem1960874 (_27504 : real) : ((term91 _27504) = _27504) = ((term91 _27504) = _27504).
Proof. exact (eq_refl ((term91 _27504) = _27504)). Qed.
Lemma lem1960875 (_27504 : real) : (term229 _27504) = (term63 _27504).
Proof. exact (MK_COMB (@lem1960873 _27504) (@lem1960874 _27504)). Qed.
Lemma lem1960876 (_27504 : real) : (term226 _27504) = (term63 _27504).
Proof. exact (TRANS (@lem1960868 _27504) (@lem1960875 _27504)). Qed.
Lemma lem1960879 (_27504 : real) (h1 : term65) : term63 _27504.
Proof. exact (EQ_MP (@lem1960876 _27504) (@lem1960865 _27504 h1)). Qed.
Lemma lem1960880 (x : real) (h1 : term65) : term63 x.
Proof. exact (@lem1960879 x h1). Qed.
Lemma lem1960883 (x : real) (y : real) (h1 : term62) (h2 : term17) (h3 : term52) (h4 : term65) (h5 : term49) (h6 : term55) (h7 : term130 x y) (h8 : term71 x y) : (term91 x) = x.
Proof. exact (@lem1960880 x h4 (@lem1960832 x y h1 h2 h3 h5 h6 h7 h8)). Qed.
Lemma lem1960884 (x : real) (y : real) (h1 : term62) (h2 : term17) (h3 : term52) (h4 : term65) (h5 : term49) (h6 : term55) (h7 : term130 x y) (h8 : term71 x y) : term230 x.
Proof. exact (fun h0 : term231 x => @lem1960883 x y h1 h2 h3 h4 h5 h6 h7 h8). Qed.
Lemma lem1960886 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1960887 (x : real) : (term230 x) = ((term91 x) = x).
Proof. exact (@lem1960886 ((term91 x) = x)). Qed.
Lemma lem1960888 (x : real) (y : real) (h1 : term62) (h2 : term17) (h3 : term52) (h4 : term65) (h5 : term49) (h6 : term55) (h7 : term130 x y) (h8 : term71 x y) : (term91 x) = x.
Proof. exact (EQ_MP (@lem1960887 x) (@lem1960884 x y h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem1960890 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1960891 (y : real) : (sqrt y) = (sqrt y).
Proof. exact (@lem1960890 (sqrt y)). Qed.
Lemma lem1960892 (y : real) : term232 y.
Proof. exact (fun h0 : term233 y => @lem1960891 y). Qed.
Lemma lem1960894 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1960895 (y : real) : (term232 y) = ((sqrt y) = (sqrt y)).
Proof. exact (@lem1960894 ((sqrt y) = (sqrt y))). Qed.
Lemma lem1960896 (y : real) : (sqrt y) = (sqrt y).
Proof. exact (EQ_MP (@lem1960895 y) (@lem1960892 y)). Qed.
Lemma lem1960898 (x : real) (y : real) (h1 : term71 x y) : term72 x y.
Proof. exact (proj1 (@lem1960123 x y h1)). Qed.
Lemma lem1960899 (x : real) (y : real) (h1 : term71 x y) : term146 x y.
Proof. exact (fun h0 : term147 x y => @lem1960898 x y h1). Qed.
Lemma lem1960901 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1960902 (x : real) (y : real) : (term146 x y) = (term72 x y).
Proof. exact (@lem1960901 (term72 x y)). Qed.
Lemma lem1960903 (x : real) (y : real) (h1 : term71 x y) : term72 x y.
Proof. exact (EQ_MP (@lem1960902 x y) (@lem1960899 x y h1)). Qed.
Lemma lem1960909 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1960910 (_27511 : real) (_27512 : real) : (term111 _27511 _27512) = (term234 _27511 _27512).
Proof. exact (@lem1960909 (term112 _27511 _27512) (term129 _27511 _27512)). Qed.
Lemma lem1960916 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1960917 (_27511 : real) (_27512 : real) : (term235 _27511 _27512) = (term236 _27511 _27512).
Proof. exact (MK_COMB (@lem1960916) (@lem1960910 _27511 _27512)). Qed.
Lemma lem1960923 (_27511 : real) (_27512 : real) : (term234 _27511 _27512) = (term234 _27511 _27512).
Proof. exact (eq_refl (term234 _27511 _27512)). Qed.
Lemma lem1960924 (_27511 : real) (_27512 : real) : ((term111 _27511 _27512) = (term234 _27511 _27512)) = ((term234 _27511 _27512) = (term234 _27511 _27512)).
Proof. exact (MK_COMB (@lem1960917 _27511 _27512) (@lem1960923 _27511 _27512)). Qed.
Lemma lem1960926 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1960927 (x : Prop) : (x = x) = True.
Proof. exact (@lem1960926 Prop x). Qed.
Lemma lem1960928 (_27511 : real) (_27512 : real) : ((term234 _27511 _27512) = (term234 _27511 _27512)) = True.
Proof. exact (@lem1960927 (term234 _27511 _27512)). Qed.
Lemma lem1960929 (_27511 : real) (_27512 : real) : ((term111 _27511 _27512) = (term234 _27511 _27512)) = True.
Proof. exact (TRANS (@lem1960924 _27511 _27512) (@lem1960928 _27511 _27512)). Qed.
Lemma lem1960930 (_27511 : real) (_27512 : real) : True = ((term111 _27511 _27512) = (term234 _27511 _27512)).
Proof. exact (SYM (@lem1960929 _27511 _27512)). Qed.
Lemma lem1960931 (_27511 : real) (_27512 : real) : (term111 _27511 _27512) = (term234 _27511 _27512).
Proof. exact (EQ_MP (@lem1960930 _27511 _27512) (@lem0)). Qed.
Lemma lem1960932 (_27511 : real) (_27512 : real) (h1 : term46) : term234 _27511 _27512.
Proof. exact (EQ_MP (@lem1960931 _27511 _27512) (@lem1960297 _27511 _27512 h1)). Qed.
Lemma lem1960934 (b : Prop) (a : Prop) : (a \/ b) = (term156 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1960935 (_27511 : real) (_27512 : real) : (term234 _27511 _27512) = (term237 _27511 _27512).
Proof. exact (@lem1960934 (term129 _27511 _27512) (term112 _27511 _27512)). Qed.
Lemma lem1960937 (a : Prop) : (term163 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1960938 (_27511 : real) (_27512 : real) : (term169 _27511 _27512) = (real_le _27511 _27512).
Proof. exact (@lem1960937 (real_le _27511 _27512)). Qed.
Lemma lem1960939 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1960940 (_27511 : real) (_27512 : real) : (term238 _27511 _27512) = (term239 _27511 _27512).
Proof. exact (MK_COMB (@lem1960939) (@lem1960938 _27511 _27512)). Qed.
Lemma lem1960941 (_27511 : real) (_27512 : real) : (term112 _27511 _27512) = (term112 _27511 _27512).
Proof. exact (eq_refl (term112 _27511 _27512)). Qed.
Lemma lem1960942 (_27511 : real) (_27512 : real) : (term237 _27511 _27512) = (term42 _27511 _27512).
Proof. exact (MK_COMB (@lem1960940 _27511 _27512) (@lem1960941 _27511 _27512)). Qed.
Lemma lem1960943 (_27511 : real) (_27512 : real) : (term234 _27511 _27512) = (term42 _27511 _27512).
Proof. exact (TRANS (@lem1960935 _27511 _27512) (@lem1960942 _27511 _27512)). Qed.
Lemma lem1960946 (_27511 : real) (_27512 : real) (h1 : term46) : term42 _27511 _27512.
Proof. exact (EQ_MP (@lem1960943 _27511 _27512) (@lem1960932 _27511 _27512 h1)). Qed.
Lemma lem1960947 (x : real) (y : real) (h1 : term46) : term240 x y.
Proof. exact (@lem1960946 (term50 x) y h1). Qed.
Lemma lem1960950 (x : real) (y : real) (h1 : term46) (h2 : term71 x y) : term241 x y.
Proof. exact (@lem1960947 x y h1 (@lem1960903 x y h2)). Qed.
Lemma lem1960951 (x : real) (y : real) (h1 : term46) (h2 : term71 x y) : term242 x y.
Proof. exact (fun h0 : term243 x y => @lem1960950 x y h1 h2). Qed.
Lemma lem1960953 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1960954 (x : real) (y : real) : (term242 x y) = (term241 x y).
Proof. exact (@lem1960953 (term241 x y)). Qed.
Lemma lem1960955 (x : real) (y : real) (h1 : term46) (h2 : term71 x y) : term241 x y.
Proof. exact (EQ_MP (@lem1960954 x y) (@lem1960951 x y h1 h2)). Qed.
Lemma lem1960956 (x : real) (y : real) (h1 : term46) (h2 : term71 x y) : term244 x y.
Proof. exact (conj (@lem1960896 y) (@lem1960955 x y h1 h2)). Qed.
Lemma lem1960957 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term130 x y) (h9 : term71 x y) : term245 x y.
Proof. exact (conj (@lem1960888 x y h1 h3 h4 h5 h6 h7 h8 h9) (@lem1960956 x y h2 h9)). Qed.
Lemma lem1960959 (_27515 : real) (_27516 : real) (_27517 : real) (_27518 : real) : term174 _27515 _27516 _27517 _27518.
Proof. exact (EQ_MP (@lem1960576 _27515 _27516 _27517 _27518) (@lem1960545 _27517 _27518 _27515 _27516)). Qed.
Lemma lem1960960 (x : real) (y : real) : term246 x y.
Proof. exact (@lem1960959 (term91 x) (sqrt y) x (sqrt y)). Qed.
Lemma lem1960963 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term130 x y) (h9 : term71 x y) : term73 x y.
Proof. exact (@lem1960960 x y (@lem1960957 x y h1 h2 h3 h4 h5 h6 h7 h8 h9)). Qed.
Lemma lem1960964 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : term247 x y.
Proof. exact (fun h0 : term130 x y => @lem1960963 x y h1 h2 h3 h4 h5 h6 h7 h0 h8). Qed.
Lemma lem1960966 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1960967 (x : real) (y : real) : (term247 x y) = (term73 x y).
Proof. exact (@lem1960966 (term73 x y)). Qed.
Lemma lem1960968 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : term73 x y.
Proof. exact (EQ_MP (@lem1960967 x y) (@lem1960964 x y h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem1960971 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1960973 (x : real) (y : real) : (term130 x y) = (term248 x y).
Proof. exact (@lem1960971 (term73 x y)). Qed.
Lemma lem1960976 (x : real) (y : real) (h1 : term71 x y) : term248 x y.
Proof. exact (EQ_MP (@lem1960973 x y) (@lem1960307 x y h1)). Qed.
Lemma lem1960979 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : False.
Proof. exact (@lem1960976 x y h8 (@lem1960968 x y h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem1960980 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : term249.
Proof. exact (fun h0 : ~ False => @lem1960979 x y h1 h2 h3 h4 h5 h6 h7 h8). Qed.
Lemma lem1960982 (p : Prop) : (term141 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1960983 : term249 = False.
Proof. exact (@lem1960982 False). Qed.
Lemma lem1960984 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : False.
Proof. exact (EQ_MP (@lem1960983) (@lem1960980 x y h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem1960985 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : term17 = False.
Proof. exact (prop_ext (fun h9 : term17 => @lem1960984 x y h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1960222 h3)). Qed.
Lemma lem1960986 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : False.
Proof. exact (EQ_MP (@lem1960985 x y h1 h2 h3 h4 h5 h6 h7 h8) (@lem1960222 h3)). Qed.
Lemma lem1960987 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : term52 = False.
Proof. exact (prop_ext (fun h9 : term52 => @lem1960986 x y h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1960177 h4)). Qed.
Lemma lem1960988 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : False.
Proof. exact (EQ_MP (@lem1960987 x y h1 h2 h3 h4 h5 h6 h7 h8) (@lem1960177 h4)). Qed.
Lemma lem1960989 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : term55 = False.
Proof. exact (prop_ext (fun h9 : term55 => @lem1960988 x y h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1960170 h7)). Qed.
Lemma lem1960990 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : False.
Proof. exact (EQ_MP (@lem1960989 x y h1 h2 h3 h4 h5 h6 h7 h8) (@lem1960170 h7)). Qed.
Lemma lem1960991 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : (term71 x y) = False.
Proof. exact (prop_ext (fun h9 : term71 x y => @lem1960990 x y h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1960123 x y h8)). Qed.
Lemma lem1960992 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : False.
Proof. exact (EQ_MP (@lem1960991 x y h1 h2 h3 h4 h5 h6 h7 h8) (@lem1960123 x y h8)). Qed.
Lemma lem1960993 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : term17 = False.
Proof. exact (prop_ext (fun h9 : term17 => @lem1960992 x y h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1960095 h3)). Qed.
Lemma lem1960994 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : False.
Proof. exact (EQ_MP (@lem1960993 x y h1 h2 h3 h4 h5 h6 h7 h8) (@lem1960095 h3)). Qed.
Lemma lem1960995 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : term52 = False.
Proof. exact (prop_ext (fun h9 : term52 => @lem1960994 x y h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1960020 h4)). Qed.
Lemma lem1960996 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : False.
Proof. exact (EQ_MP (@lem1960995 x y h1 h2 h3 h4 h5 h6 h7 h8) (@lem1960020 h4)). Qed.
Lemma lem1960997 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : term55 = False.
Proof. exact (prop_ext (fun h9 : term55 => @lem1960996 x y h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1959997 h7)). Qed.
Lemma lem1960998 (x : real) (y : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term71 x y) : False.
Proof. exact (EQ_MP (@lem1960997 x y h1 h2 h3 h4 h5 h6 h7 h8) (@lem1959997 h7)). Qed.
Lemma lem1960999 (x : real) (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term82 x) : False.
Proof. exact (ex_elim (@lem1959909 x h8) (fun y : real => fun h0 : term81 x y => @lem1960998 x y h1 h2 h3 h4 h5 h6 h7 h0)). Qed.
Lemma lem1961000 (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term10) : False.
Proof. exact (ex_elim (@lem1959535 h8) (fun x : real => fun h0 : term87 x => @lem1960999 x h1 h2 h3 h4 h5 h6 h7 h0)). Qed.
Lemma lem1961001 (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term10) : term17 = False.
Proof. exact (prop_ext (fun h9 : term17 => @lem1961000 h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1959908 h3)). Qed.
Lemma lem1961002 (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term10) : False.
Proof. exact (EQ_MP (@lem1961001 h1 h2 h3 h4 h5 h6 h7 h8) (@lem1959908 h3)). Qed.
Lemma lem1961003 (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term10) : term52 = False.
Proof. exact (prop_ext (fun h9 : term52 => @lem1961002 h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1959707 h4)). Qed.
Lemma lem1961004 (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term10) : False.
Proof. exact (EQ_MP (@lem1961003 h1 h2 h3 h4 h5 h6 h7 h8) (@lem1959707 h4)). Qed.
Lemma lem1961005 (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term10) : term55 = False.
Proof. exact (prop_ext (fun h9 : term55 => @lem1961004 h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : False => @lem1959694 h7)). Qed.
Lemma lem1961006 (h1 : term62) (h2 : term46) (h3 : term17) (h4 : term52) (h5 : term65) (h6 : term49) (h7 : term55) (h8 : term10) : False.
Proof. exact (EQ_MP (@lem1961005 h1 h2 h3 h4 h5 h6 h7 h8) (@lem1959694 h7)). Qed.
Lemma lem1961007 (h1 : term62) (h2 : term46) (h3 : term52) (h4 : term65) (h5 : term49) (h6 : term55) (h7 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1961006 h1 h2 h0 h3 h4 h5 h6 h7). Qed.
Lemma lem1961008 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1961009 (h1 : term62) (h2 : term46) (h3 : term52) (h4 : term65) (h5 : term49) (h6 : term55) (h7 : term10) : term16.
Proof. exact (EQ_MP (@lem1961008) (@lem1961007 h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem1961010 (h1 : term62) (h2 : term52) (h3 : term65) (h4 : term49) (h5 : term55) (h6 : term10) : term20.
Proof. exact (fun h0 : term46 => @lem1961009 h1 h0 h2 h3 h4 h5 h6). Qed.
Lemma lem1961011 (h1 : term62) (h2 : term52) (h3 : term65) (h4 : term55) (h5 : term10) : term23.
Proof. exact (fun h0 : term49 => @lem1961010 h1 h2 h3 h0 h4 h5). Qed.
Lemma lem1961012 (h1 : term62) (h2 : term65) (h3 : term55) (h4 : term10) : term26.
Proof. exact (fun h0 : term52 => @lem1961011 h1 h0 h2 h3 h4). Qed.
Lemma lem1961013 (h1 : term62) (h2 : term65) (h3 : term10) : term29.
Proof. exact (fun h0 : term55 => @lem1961012 h1 h2 h0 h3). Qed.
Lemma lem1961014 (h1 : term65) (h2 : term10) : term32.
Proof. exact (fun h0 : term62 => @lem1961013 h0 h1 h2). Qed.
Lemma lem1961015 (h1 : term10) : term35.
Proof. exact (fun h0 : term65 => @lem1961014 h0 h1). Qed.
Lemma lem1961016 : term37.
Proof. exact (fun h0 : term10 => @lem1961015 h0). Qed.
Lemma lem1961017 : term11.
Proof. exact (EQ_MP (@lem1959443) (@lem1961016)). Qed.
Lemma lem1961019 : term11.
Proof. exact (@lem1959074 (@lem1961017)). Qed.
Lemma lem1961020 (h1 : term10) : term34.
Proof. exact (@lem1961019 (@lem1959059 h1)). Qed.
Lemma lem1961021 (h1 : term10) : term31.
Proof. exact (@lem1961020 h1 (@lem1900729)). Qed.
Lemma lem1961022 (h1 : term10) : term28.
Proof. exact (@lem1961021 h1 (@lem1339577)). Qed.
Lemma lem1961023 (h1 : term10) : term25.
Proof. exact (@lem1961022 h1 (@lem1382902)). Qed.
Lemma lem1961024 (h1 : term10) : term22.
Proof. exact (@lem1961023 h1 (@lem1383497)). Qed.
Lemma lem1961025 (h1 : term10) : term19.
Proof. exact (@lem1961024 h1 (@lem1945292)). Qed.
Lemma lem1961026 (h1 : term10) : term15.
Proof. exact (@lem1961025 h1 (@lem1951675)). Qed.
Lemma lem1961027 (h1 : term10) : False.
Proof. exact (@lem1961026 h1 (@lem1339697)). Qed.
Lemma lem1961028 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1961027 h1) (fun h2 : False => @lem1959059 h1)). Qed.
Lemma lem1961029 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1961028 h1) (@lem1959059 h1)). Qed.
Lemma lem1961030 : term9.
Proof. exact (fun h0 : term10 => @lem1961029 h0). Qed.
Lemma lem1961031 : term8.
Proof. exact (EQ_MP (@lem1959058) (@lem1961030)). Qed.
