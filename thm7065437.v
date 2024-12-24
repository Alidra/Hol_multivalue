Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7065437_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_ADD_RID_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338512_spec.
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
Require Import thm7064143_spec.
Require Import thm7064144_spec.
Lemma lem7064173 {A : Type'} (P : A -> Prop) (x : A) : term0 A P x.
Proof. exact (EQ_MP (@lem7064144 A P x) (@lem7064143 A P x)). Qed.
Lemma lem7064174 (P : real -> Prop) (x : real) : term1 P x.
Proof. exact (@lem7064173 real P x). Qed.
Lemma lem7064175 : term2.
Proof. exact (@lem7064174 term3 term4). Qed.
Lemma lem7064177 (p : Prop) : p = (term5 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7064178 : term6 = term7.
Proof. exact (@lem7064177 term6). Qed.
Lemma lem7064179 : term7 = term6.
Proof. exact (SYM (@lem7064178)). Qed.
Lemma lem7064180 (h1 : term8) : term8.
Proof. exact (h1). Qed.
Lemma lem7064183 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem7064184 : term10.
Proof. exact (fun h0 : term9 => @lem7064183 h0). Qed.
Lemma lem7064185 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7064186 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem7064187 (h1 : term9) (h2 : term10) : term9.
Proof. exact (@lem7064185 h2 (@lem7064186 h1)). Qed.
Lemma lem7064188 (h1 : term9) : term11.
Proof. exact (fun h0 : term10 => @lem7064187 h1 h0). Qed.
Lemma lem7064189 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7064190 (h1 : term9) (h2 : term10) : term9.
Proof. exact (@lem7064188 h1 (@lem7064189 h2)). Qed.
Lemma lem7064191 (h1 : term10) : term10.
Proof. exact (fun h0 : term9 => @lem7064190 h0 h1). Qed.
Lemma lem7064192 : term12.
Proof. exact (fun h0 : term10 => @lem7064191 h0). Qed.
Lemma lem7064195 : term10.
Proof. exact (@lem7064192 (@lem7064184)). Qed.
Lemma lem7064203 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term13 A P Q) = (term14 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem7064204 (P : real -> Prop) (Q : real -> Prop) : (term15 P Q) = (term16 P Q).
Proof. exact (@lem7064203 real P Q). Qed.
Lemma lem7064205 (x : real) : (term17 x) = (term18 x).
Proof. exact (@lem7064204 (term19 x) (term20 x)). Qed.
Lemma lem7064206 (x : real) (y : real) : (term21 x y) = ((real_add x y) = y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem7064207 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7064208 (x : real) (y : real) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem7064207) (@lem7064206 x y)). Qed.
Lemma lem7064209 (x : real) (y : real) : (term24 x y) = ((real_add y x) = y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem7064210 (x : real) (y : real) : (term25 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem7064208 x y) (@lem7064209 x y)). Qed.
Lemma lem7064211 (x : real) : (term27 x) = (term28 x).
Proof. exact (fun_ext (fun y : real => @lem7064210 x y)). Qed.
Lemma lem7064212 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064213 (x : real) : (term17 x) = (term29 x).
Proof. exact (MK_COMB (@lem7064212) (@lem7064211 x)). Qed.
Lemma lem7064214 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7064215 (x : real) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem7064214) (@lem7064213 x)). Qed.
Lemma lem7064216 (x : real) (y : real) : (term21 x y) = ((real_add x y) = y).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem7064217 (x : real) : (term32 x) = (term19 x).
Proof. exact (fun_ext (fun y : real => @lem7064216 x y)). Qed.
Lemma lem7064218 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064219 (x : real) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem7064218) (@lem7064217 x)). Qed.
Lemma lem7064220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7064221 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem7064220) (@lem7064219 x)). Qed.
Lemma lem7064222 (x : real) (y : real) : (term24 x y) = ((real_add y x) = y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem7064223 (x : real) : (term37 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem7064222 x y)). Qed.
Lemma lem7064224 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064225 (x : real) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem7064224) (@lem7064223 x)). Qed.
Lemma lem7064226 (x : real) : (term18 x) = (term40 x).
Proof. exact (MK_COMB (@lem7064221 x) (@lem7064225 x)). Qed.
Lemma lem7064227 (x : real) : ((term17 x) = (term18 x)) = ((term29 x) = (term40 x)).
Proof. exact (MK_COMB (@lem7064215 x) (@lem7064226 x)). Qed.
Lemma lem7064228 (x : real) : (term29 x) = (term40 x).
Proof. exact (EQ_MP (@lem7064227 x) (@lem7064205 x)). Qed.
Lemma lem7064239 : term3 = term41.
Proof. exact (fun_ext (fun x : real => @lem7064228 x)). Qed.
Lemma lem7064240 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7064241 (y : real) : (term42 y) = (term43 y).
Proof. exact (MK_COMB (@lem7064239) (@lem7064240 y)). Qed.
Lemma lem7064242 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7064243 (y : real) : (term44 y) = (term45 y).
Proof. exact (MK_COMB (@lem7064242) (@lem7064241 y)). Qed.
Lemma lem7064244 (y : real) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem7064245 (y : real) : ((term42 y) = (y = term4)) = ((term43 y) = (y = term4)).
Proof. exact (MK_COMB (@lem7064243 y) (@lem7064244 y)). Qed.
Lemma lem7064246 : term46 = term47.
Proof. exact (fun_ext (fun y : real => @lem7064245 y)). Qed.
Lemma lem7064247 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064248 : term6 = term48.
Proof. exact (MK_COMB (@lem7064247) (@lem7064246)). Qed.
Lemma lem7064253 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7064254 : term8 = term49.
Proof. exact (MK_COMB (@lem7064253) (@lem7064248)). Qed.
Lemma lem7064255 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7064256 : term50 = term51.
Proof. exact (MK_COMB (@lem7064255) (@lem7064254)). Qed.
Lemma lem7064264 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7064265 : term52 = term53.
Proof. exact (@lem7064264 term54). Qed.
Lemma lem7064270 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem7064271 : term56 = term57.
Proof. exact (MK_COMB (@lem7064270) (@lem7064265)). Qed.
Lemma lem7064274 : term9 = term58.
Proof. exact (MK_COMB (@lem7064256) (@lem7064271)). Qed.
Lemma lem7064277 (y : real) : (term43 y) = (term40 y).
Proof. exact (eq_refl (term43 y)). Qed.
Lemma lem7064278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7064279 (y : real) : (term45 y) = (term59 y).
Proof. exact (MK_COMB (@lem7064278) (@lem7064277 y)). Qed.
Lemma lem7064280 (y : real) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem7064281 (y : real) : ((term43 y) = (y = term4)) = ((term40 y) = (y = term4)).
Proof. exact (MK_COMB (@lem7064279 y) (@lem7064280 y)). Qed.
Lemma lem7064282 : term47 = term60.
Proof. exact (fun_ext (fun y : real => @lem7064281 y)). Qed.
Lemma lem7064283 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064284 : term48 = term61.
Proof. exact (MK_COMB (@lem7064283) (@lem7064282)). Qed.
Lemma lem7064285 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7064286 : term49 = term62.
Proof. exact (MK_COMB (@lem7064285) (@lem7064284)). Qed.
Lemma lem7064287 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7064288 : term51 = term63.
Proof. exact (MK_COMB (@lem7064287) (@lem7064286)). Qed.
Lemma lem7064289 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem7064290 : term58 = term64.
Proof. exact (MK_COMB (@lem7064288) (@lem7064289)). Qed.
Lemma lem7064293 : term9 = term64.
Proof. exact (TRANS (@lem7064274) (@lem7064290)). Qed.
Lemma lem7064294 (x : real) : ((term65 x) = x) = ((term65 x) = x).
Proof. exact (eq_refl ((term65 x) = x)). Qed.
Lemma lem7064295 : term66 = term66.
Proof. exact (fun_ext (fun x : real => @lem7064294 x)). Qed.
Lemma lem7064296 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064297 : term54 = term54.
Proof. exact (MK_COMB (@lem7064296) (@lem7064295)). Qed.
Lemma lem7064298 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7064299 : term53 = term53.
Proof. exact (MK_COMB (@lem7064298) (@lem7064297)). Qed.
Lemma lem7064300 (x : real) : ((term67 x) = x) = ((term67 x) = x).
Proof. exact (eq_refl ((term67 x) = x)). Qed.
Lemma lem7064301 : term68 = term68.
Proof. exact (fun_ext (fun x : real => @lem7064300 x)). Qed.
Lemma lem7064302 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064303 : term69 = term69.
Proof. exact (MK_COMB (@lem7064302) (@lem7064301)). Qed.
Lemma lem7064304 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7064305 : term55 = term55.
Proof. exact (MK_COMB (@lem7064304) (@lem7064303)). Qed.
Lemma lem7064306 : term57 = term57.
Proof. exact (MK_COMB (@lem7064305) (@lem7064299)). Qed.
Lemma lem7064307 (y : real) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem7064308 (y : real) (y' : real) : ((real_add y' y) = y') = ((real_add y' y) = y').
Proof. exact (eq_refl ((real_add y' y) = y')). Qed.
Lemma lem7064309 (y : real) : (term20 y) = (term20 y).
Proof. exact (fun_ext (fun y' : real => @lem7064308 y y')). Qed.
Lemma lem7064310 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064311 (y : real) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem7064310) (@lem7064309 y)). Qed.
Lemma lem7064312 (y : real) (y' : real) : ((real_add y y') = y') = ((real_add y y') = y').
Proof. exact (eq_refl ((real_add y y') = y')). Qed.
Lemma lem7064313 (y : real) : (term19 y) = (term19 y).
Proof. exact (fun_ext (fun y' : real => @lem7064312 y y')). Qed.
Lemma lem7064314 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064315 (y : real) : (term34 y) = (term34 y).
Proof. exact (MK_COMB (@lem7064314) (@lem7064313 y)). Qed.
Lemma lem7064316 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7064317 (y : real) : (term36 y) = (term36 y).
Proof. exact (MK_COMB (@lem7064316) (@lem7064315 y)). Qed.
Lemma lem7064318 (y : real) : (term40 y) = (term40 y).
Proof. exact (MK_COMB (@lem7064317 y) (@lem7064311 y)). Qed.
Lemma lem7064319 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7064320 (y : real) : (term59 y) = (term59 y).
Proof. exact (MK_COMB (@lem7064319) (@lem7064318 y)). Qed.
Lemma lem7064321 (y : real) : ((term40 y) = (y = term4)) = ((term40 y) = (y = term4)).
Proof. exact (MK_COMB (@lem7064320 y) (@lem7064307 y)). Qed.
Lemma lem7064322 : term60 = term60.
Proof. exact (fun_ext (fun y : real => @lem7064321 y)). Qed.
Lemma lem7064323 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064324 : term61 = term61.
Proof. exact (MK_COMB (@lem7064323) (@lem7064322)). Qed.
Lemma lem7064325 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7064326 : term62 = term62.
Proof. exact (MK_COMB (@lem7064325) (@lem7064324)). Qed.
Lemma lem7064327 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7064328 : term63 = term63.
Proof. exact (MK_COMB (@lem7064327) (@lem7064326)). Qed.
Lemma lem7064329 : term64 = term64.
Proof. exact (MK_COMB (@lem7064328) (@lem7064306)). Qed.
Lemma lem7064368 : term9 = term64.
Proof. exact (TRANS (@lem7064293) (@lem7064329)). Qed.
Lemma lem7064369 : term64 = term9.
Proof. exact (SYM (@lem7064368)). Qed.
Lemma lem7064370 (h1 : term62) : term62.
Proof. exact (h1). Qed.
Lemma lem7064371 (h1 : term69) : term69.
Proof. exact (h1). Qed.
Lemma lem7064372 (h1 : term54) : term54.
Proof. exact (h1). Qed.
Lemma lem7064374 (y : real) (y' : real) : ((real_add y y') = y') = ((real_add y y') = y').
Proof. exact (eq_refl ((real_add y y') = y')). Qed.
Lemma lem7064375 (P : real -> Prop) : (term70 P) = (term71 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7064376 (y : real) : (term72 y) = (term73 y).
Proof. exact (@lem7064375 (term19 y)). Qed.
Lemma lem7064377 (y : real) (y' : real) : (term21 y y') = ((real_add y y') = y').
Proof. exact (eq_refl (term21 y y')). Qed.
Lemma lem7064378 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7064380 (y : real) (y' : real) : (term74 y y') = (term75 y y').
Proof. exact (MK_COMB (@lem7064378) (@lem7064377 y y')). Qed.
Lemma lem7064381 (y : real) : (term76 y) = (term77 y).
Proof. exact (fun_ext (fun y' : real => @lem7064380 y y')). Qed.
Lemma lem7064382 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064383 (y : real) : (term73 y) = (term78 y).
Proof. exact (MK_COMB (@lem7064382) (@lem7064381 y)). Qed.
Lemma lem7064384 (y : real) : (term72 y) = (term78 y).
Proof. exact (TRANS (@lem7064376 y) (@lem7064383 y)). Qed.
Lemma lem7064385 (y : real) : (term19 y) = (term19 y).
Proof. exact (fun_ext (fun y' : real => @lem7064374 y y')). Qed.
Lemma lem7064386 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064387 (y : real) : (term34 y) = (term34 y).
Proof. exact (MK_COMB (@lem7064386) (@lem7064385 y)). Qed.
Lemma lem7064389 (y : real) (y' : real) : ((real_add y' y) = y') = ((real_add y' y) = y').
Proof. exact (eq_refl ((real_add y' y) = y')). Qed.
Lemma lem7064390 (P : real -> Prop) : (term70 P) = (term71 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7064391 (y : real) : (term79 y) = (term80 y).
Proof. exact (@lem7064390 (term20 y)). Qed.
Lemma lem7064392 (y : real) (y' : real) : (term24 y y') = ((real_add y' y) = y').
Proof. exact (eq_refl (term24 y y')). Qed.
Lemma lem7064393 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7064395 (y : real) (y' : real) : (term81 y y') = (term82 y y').
Proof. exact (MK_COMB (@lem7064393) (@lem7064392 y y')). Qed.
Lemma lem7064396 (y : real) : (term83 y) = (term84 y).
Proof. exact (fun_ext (fun y' : real => @lem7064395 y y')). Qed.
Lemma lem7064397 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064398 (y : real) : (term80 y) = (term85 y).
Proof. exact (MK_COMB (@lem7064397) (@lem7064396 y)). Qed.
Lemma lem7064399 (y : real) : (term79 y) = (term85 y).
Proof. exact (TRANS (@lem7064391 y) (@lem7064398 y)). Qed.
Lemma lem7064400 (y : real) : (term20 y) = (term20 y).
Proof. exact (fun_ext (fun y' : real => @lem7064389 y y')). Qed.
Lemma lem7064401 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064402 (y : real) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem7064401) (@lem7064400 y)). Qed.
Lemma lem7064403 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7064404 (y : real) : (term86 y) = (term87 y).
Proof. exact (MK_COMB (@lem7064403) (@lem7064384 y)). Qed.
Lemma lem7064405 (y : real) : (term88 y) = (term89 y).
Proof. exact (MK_COMB (@lem7064404 y) (@lem7064399 y)). Qed.
Lemma lem7064406 (y : real) : (term90 y) = (term88 y).
Proof. exact (@lem17045 (term34 y) (term39 y)). Qed.
Lemma lem7064407 (y : real) : (term90 y) = (term89 y).
Proof. exact (TRANS (@lem7064406 y) (@lem7064405 y)). Qed.
Lemma lem7064408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7064409 (y : real) : (term36 y) = (term36 y).
Proof. exact (MK_COMB (@lem7064408) (@lem7064387 y)). Qed.
Lemma lem7064410 (y : real) : (term40 y) = (term40 y).
Proof. exact (MK_COMB (@lem7064409 y) (@lem7064402 y)). Qed.
Lemma lem7064411 (y : real) : (term91 y) = (term91 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem7064412 (y : real) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem7064413 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7064414 (y : real) : (term92 y) = (term93 y).
Proof. exact (MK_COMB (@lem7064413) (@lem7064407 y)). Qed.
Lemma lem7064415 (y : real) : (term94 y) = (term95 y).
Proof. exact (MK_COMB (@lem7064414 y) (@lem7064412 y)). Qed.
Lemma lem7064416 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7064417 (y : real) : (term96 y) = (term96 y).
Proof. exact (MK_COMB (@lem7064416) (@lem7064410 y)). Qed.
Lemma lem7064418 (y : real) : (term97 y) = (term97 y).
Proof. exact (MK_COMB (@lem7064417 y) (@lem7064411 y)). Qed.
Lemma lem7064419 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7064420 (y : real) : (term98 y) = (term98 y).
Proof. exact (MK_COMB (@lem7064419) (@lem7064418 y)). Qed.
Lemma lem7064421 (y : real) : (term99 y) = (term100 y).
Proof. exact (MK_COMB (@lem7064420 y) (@lem7064415 y)). Qed.
Lemma lem7064422 (y : real) : (term101 y) = (term99 y).
Proof. exact (@lem17646 (term40 y) (y = term4)). Qed.
Lemma lem7064423 (y : real) : (term101 y) = (term100 y).
Proof. exact (TRANS (@lem7064422 y) (@lem7064421 y)). Qed.
Lemma lem7064424 (P : real -> Prop) : (term70 P) = (term71 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7064425 : term62 = term102.
Proof. exact (@lem7064424 term60). Qed.
Lemma lem7064426 (y : real) : (term103 y) = ((term40 y) = (y = term4)).
Proof. exact (eq_refl (term103 y)). Qed.
Lemma lem7064427 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7064428 (y : real) : (term104 y) = (term101 y).
Proof. exact (MK_COMB (@lem7064427) (@lem7064426 y)). Qed.
Lemma lem7064429 (y : real) : (term104 y) = (term100 y).
Proof. exact (TRANS (@lem7064428 y) (@lem7064423 y)). Qed.
Lemma lem7064430 : term105 = term106.
Proof. exact (fun_ext (fun y : real => @lem7064429 y)). Qed.
Lemma lem7064431 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064432 : term102 = term107.
Proof. exact (MK_COMB (@lem7064431) (@lem7064430)). Qed.
Lemma lem7064433 : term62 = term107.
Proof. exact (TRANS (@lem7064425) (@lem7064432)). Qed.
Lemma lem7064435 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem7064436 (P : real -> Prop) (Q : real -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem7064435 real P Q). Qed.
Lemma lem7064437 : term112 = term113.
Proof. exact (@lem7064436 term114 term115). Qed.
Lemma lem7064438 (y : real) : (term116 y) = (term97 y).
Proof. exact (eq_refl (term116 y)). Qed.
Lemma lem7064439 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7064440 (y : real) : (term117 y) = (term98 y).
Proof. exact (MK_COMB (@lem7064439) (@lem7064438 y)). Qed.
Lemma lem7064441 (y : real) : (term118 y) = (term95 y).
Proof. exact (eq_refl (term118 y)). Qed.
Lemma lem7064442 (y : real) : (term119 y) = (term100 y).
Proof. exact (MK_COMB (@lem7064440 y) (@lem7064441 y)). Qed.
Lemma lem7064443 : term120 = term106.
Proof. exact (fun_ext (fun y : real => @lem7064442 y)). Qed.
Lemma lem7064444 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064445 : term112 = term107.
Proof. exact (MK_COMB (@lem7064444) (@lem7064443)). Qed.
Lemma lem7064446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7064447 : term121 = term122.
Proof. exact (MK_COMB (@lem7064446) (@lem7064445)). Qed.
Lemma lem7064448 (y : real) : (term116 y) = (term97 y).
Proof. exact (eq_refl (term116 y)). Qed.
Lemma lem7064449 : term123 = term114.
Proof. exact (fun_ext (fun y : real => @lem7064448 y)). Qed.
Lemma lem7064450 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064451 : term124 = term125.
Proof. exact (MK_COMB (@lem7064450) (@lem7064449)). Qed.
Lemma lem7064452 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7064453 : term126 = term127.
Proof. exact (MK_COMB (@lem7064452) (@lem7064451)). Qed.
Lemma lem7064454 (y : real) : (term118 y) = (term95 y).
Proof. exact (eq_refl (term118 y)). Qed.
Lemma lem7064455 : term128 = term115.
Proof. exact (fun_ext (fun y : real => @lem7064454 y)). Qed.
Lemma lem7064456 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064457 : term129 = term130.
Proof. exact (MK_COMB (@lem7064456) (@lem7064455)). Qed.
Lemma lem7064458 : term113 = term131.
Proof. exact (MK_COMB (@lem7064453) (@lem7064457)). Qed.
Lemma lem7064459 : (term112 = term113) = (term107 = term131).
Proof. exact (MK_COMB (@lem7064447) (@lem7064458)). Qed.
Lemma lem7064460 : term107 = term131.
Proof. exact (EQ_MP (@lem7064459) (@lem7064437)). Qed.
Lemma lem7064574 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7064575 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term110 P Q).
Proof. exact (@lem7064574 real P Q). Qed.
Lemma lem7064576 (y : real) : (term132 y) = (term133 y).
Proof. exact (@lem7064575 (term77 y) (term84 y)). Qed.
Lemma lem7064577 (y : real) (y' : real) : (term134 y y') = (term75 y y').
Proof. exact (eq_refl (term134 y y')). Qed.
Lemma lem7064578 (y : real) : (term135 y) = (term77 y).
Proof. exact (fun_ext (fun y' : real => @lem7064577 y y')). Qed.
Lemma lem7064579 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064580 (y : real) : (term136 y) = (term78 y).
Proof. exact (MK_COMB (@lem7064579) (@lem7064578 y)). Qed.
Lemma lem7064581 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7064582 (y : real) : (term137 y) = (term87 y).
Proof. exact (MK_COMB (@lem7064581) (@lem7064580 y)). Qed.
Lemma lem7064583 (y : real) (y' : real) : (term138 y y') = (term82 y y').
Proof. exact (eq_refl (term138 y y')). Qed.
Lemma lem7064584 (y : real) : (term139 y) = (term84 y).
Proof. exact (fun_ext (fun y' : real => @lem7064583 y y')). Qed.
Lemma lem7064585 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064586 (y : real) : (term140 y) = (term85 y).
Proof. exact (MK_COMB (@lem7064585) (@lem7064584 y)). Qed.
Lemma lem7064587 (y : real) : (term132 y) = (term89 y).
Proof. exact (MK_COMB (@lem7064582 y) (@lem7064586 y)). Qed.
Lemma lem7064588 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7064589 (y : real) : (term141 y) = (term142 y).
Proof. exact (MK_COMB (@lem7064588) (@lem7064587 y)). Qed.
Lemma lem7064590 (y : real) (y' : real) : (term134 y y') = (term75 y y').
Proof. exact (eq_refl (term134 y y')). Qed.
Lemma lem7064591 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7064592 (y : real) (y' : real) : (term143 y y') = (term144 y y').
Proof. exact (MK_COMB (@lem7064591) (@lem7064590 y y')). Qed.
Lemma lem7064593 (y : real) (y' : real) : (term138 y y') = (term82 y y').
Proof. exact (eq_refl (term138 y y')). Qed.
Lemma lem7064594 (y : real) (y' : real) : (term145 y y') = (term146 y y').
Proof. exact (MK_COMB (@lem7064592 y y') (@lem7064593 y y')). Qed.
Lemma lem7064595 (y : real) : (term147 y) = (term148 y).
Proof. exact (fun_ext (fun y' : real => @lem7064594 y y')). Qed.
Lemma lem7064596 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064597 (y : real) : (term133 y) = (term149 y).
Proof. exact (MK_COMB (@lem7064596) (@lem7064595 y)). Qed.
Lemma lem7064598 (y : real) : ((term132 y) = (term133 y)) = ((term89 y) = (term149 y)).
Proof. exact (MK_COMB (@lem7064589 y) (@lem7064597 y)). Qed.
Lemma lem7064599 (y : real) : (term89 y) = (term149 y).
Proof. exact (EQ_MP (@lem7064598 y) (@lem7064576 y)). Qed.
Lemma lem7064600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7064601 (y : real) : (term93 y) = (term150 y).
Proof. exact (MK_COMB (@lem7064600) (@lem7064599 y)). Qed.
Lemma lem7064602 (y : real) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem7064603 (y : real) : (term95 y) = (term151 y).
Proof. exact (MK_COMB (@lem7064601 y) (@lem7064602 y)). Qed.
Lemma lem7064605 {A : Type'} (P : A -> Prop) (Q : Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7064606 (P : real -> Prop) (Q : Prop) : (term154 P Q) = (term155 P Q).
Proof. exact (@lem7064605 real P Q). Qed.
Lemma lem7064607 (y : real) : (term156 y) = (term157 y).
Proof. exact (@lem7064606 (term148 y) (y = term4)). Qed.
Lemma lem7064608 (y : real) (y' : real) : (term158 y y') = (term146 y y').
Proof. exact (eq_refl (term158 y y')). Qed.
Lemma lem7064609 (y : real) : (term159 y) = (term148 y).
Proof. exact (fun_ext (fun y' : real => @lem7064608 y y')). Qed.
Lemma lem7064610 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064611 (y : real) : (term160 y) = (term149 y).
Proof. exact (MK_COMB (@lem7064610) (@lem7064609 y)). Qed.
Lemma lem7064612 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7064613 (y : real) : (term161 y) = (term150 y).
Proof. exact (MK_COMB (@lem7064612) (@lem7064611 y)). Qed.
Lemma lem7064614 (y : real) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem7064615 (y : real) : (term156 y) = (term151 y).
Proof. exact (MK_COMB (@lem7064613 y) (@lem7064614 y)). Qed.
Lemma lem7064616 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7064617 (y : real) : (term162 y) = (term163 y).
Proof. exact (MK_COMB (@lem7064616) (@lem7064615 y)). Qed.
Lemma lem7064618 (y : real) (y' : real) : (term158 y y') = (term146 y y').
Proof. exact (eq_refl (term158 y y')). Qed.
Lemma lem7064619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7064620 (y : real) (y' : real) : (term164 y y') = (term165 y y').
Proof. exact (MK_COMB (@lem7064619) (@lem7064618 y y')). Qed.
Lemma lem7064621 (y : real) : (y = term4) = (y = term4).
Proof. exact (eq_refl (y = term4)). Qed.
Lemma lem7064622 (y' : real) (y : real) : (term166 y' y) = (term167 y' y).
Proof. exact (MK_COMB (@lem7064620 y y') (@lem7064621 y)). Qed.
Lemma lem7064623 (y : real) : (term168 y) = (term169 y).
Proof. exact (fun_ext (fun y' : real => @lem7064622 y' y)). Qed.
Lemma lem7064624 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064625 (y : real) : (term157 y) = (term170 y).
Proof. exact (MK_COMB (@lem7064624) (@lem7064623 y)). Qed.
Lemma lem7064626 (y : real) : ((term156 y) = (term157 y)) = ((term151 y) = (term170 y)).
Proof. exact (MK_COMB (@lem7064617 y) (@lem7064625 y)). Qed.
Lemma lem7064627 (y : real) : (term151 y) = (term170 y).
Proof. exact (EQ_MP (@lem7064626 y) (@lem7064607 y)). Qed.
Lemma lem7064628 (y : real) : (term95 y) = (term170 y).
Proof. exact (TRANS (@lem7064603 y) (@lem7064627 y)). Qed.
Lemma lem7064629 : term115 = term171.
Proof. exact (fun_ext (fun y : real => @lem7064628 y)). Qed.
Lemma lem7064630 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064631 : term130 = term172.
Proof. exact (MK_COMB (@lem7064630) (@lem7064629)). Qed.
Lemma lem7064632 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem7064633 : term131 = term173.
Proof. exact (MK_COMB (@lem7064632) (@lem7064631)). Qed.
Lemma lem7064635 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem7064636 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term110 P Q).
Proof. exact (@lem7064635 real P Q). Qed.
Lemma lem7064637 : term174 = term175.
Proof. exact (@lem7064636 term114 term171). Qed.
Lemma lem7064638 (y : real) : (term116 y) = (term97 y).
Proof. exact (eq_refl (term116 y)). Qed.
Lemma lem7064639 : term123 = term114.
Proof. exact (fun_ext (fun y : real => @lem7064638 y)). Qed.
Lemma lem7064640 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064641 : term124 = term125.
Proof. exact (MK_COMB (@lem7064640) (@lem7064639)). Qed.
Lemma lem7064642 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7064643 : term126 = term127.
Proof. exact (MK_COMB (@lem7064642) (@lem7064641)). Qed.
Lemma lem7064644 (y : real) : (term176 y) = (term170 y).
Proof. exact (eq_refl (term176 y)). Qed.
Lemma lem7064645 : term177 = term171.
Proof. exact (fun_ext (fun y : real => @lem7064644 y)). Qed.
Lemma lem7064646 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064647 : term178 = term172.
Proof. exact (MK_COMB (@lem7064646) (@lem7064645)). Qed.
Lemma lem7064648 : term174 = term173.
Proof. exact (MK_COMB (@lem7064643) (@lem7064647)). Qed.
Lemma lem7064649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7064650 : term179 = term180.
Proof. exact (MK_COMB (@lem7064649) (@lem7064648)). Qed.
Lemma lem7064651 (y : real) : (term116 y) = (term97 y).
Proof. exact (eq_refl (term116 y)). Qed.
Lemma lem7064652 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7064653 (y : real) : (term117 y) = (term98 y).
Proof. exact (MK_COMB (@lem7064652) (@lem7064651 y)). Qed.
Lemma lem7064654 (y : real) : (term176 y) = (term170 y).
Proof. exact (eq_refl (term176 y)). Qed.
Lemma lem7064655 (y : real) : (term181 y) = (term182 y).
Proof. exact (MK_COMB (@lem7064653 y) (@lem7064654 y)). Qed.
Lemma lem7064656 : term183 = term184.
Proof. exact (fun_ext (fun y : real => @lem7064655 y)). Qed.
Lemma lem7064657 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064658 : term175 = term185.
Proof. exact (MK_COMB (@lem7064657) (@lem7064656)). Qed.
Lemma lem7064659 : (term174 = term175) = (term173 = term185).
Proof. exact (MK_COMB (@lem7064650) (@lem7064658)). Qed.
Lemma lem7064660 : term173 = term185.
Proof. exact (EQ_MP (@lem7064659) (@lem7064637)). Qed.
Lemma lem7064662 {A : Type'} (P : Prop) (Q : A -> Prop) : (term186 A P Q) = (term187 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7064663 (P : Prop) (Q : real -> Prop) : (term188 P Q) = (term189 P Q).
Proof. exact (@lem7064662 real P Q). Qed.
Lemma lem7064664 (y : real) : (term190 y) = (term191 y).
Proof. exact (@lem7064663 (term97 y) (term169 y)). Qed.
Lemma lem7064665 (y' : real) (y : real) : (term192 y y') = (term167 y' y).
Proof. exact (eq_refl (term192 y y')). Qed.
Lemma lem7064666 (y : real) : (term193 y) = (term169 y).
Proof. exact (fun_ext (fun y' : real => @lem7064665 y' y)). Qed.
Lemma lem7064667 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064668 (y : real) : (term194 y) = (term170 y).
Proof. exact (MK_COMB (@lem7064667) (@lem7064666 y)). Qed.
Lemma lem7064669 (y : real) : (term98 y) = (term98 y).
Proof. exact (eq_refl (term98 y)). Qed.
Lemma lem7064670 (y : real) : (term190 y) = (term182 y).
Proof. exact (MK_COMB (@lem7064669 y) (@lem7064668 y)). Qed.
Lemma lem7064671 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7064672 (y : real) : (term195 y) = (term196 y).
Proof. exact (MK_COMB (@lem7064671) (@lem7064670 y)). Qed.
Lemma lem7064673 (y' : real) (y : real) : (term192 y y') = (term167 y' y).
Proof. exact (eq_refl (term192 y y')). Qed.
Lemma lem7064674 (y : real) : (term98 y) = (term98 y).
Proof. exact (eq_refl (term98 y)). Qed.
Lemma lem7064675 (y' : real) (y : real) : (term197 y y') = (term198 y' y).
Proof. exact (MK_COMB (@lem7064674 y) (@lem7064673 y' y)). Qed.
Lemma lem7064676 (y : real) : (term199 y) = (term200 y).
Proof. exact (fun_ext (fun y' : real => @lem7064675 y' y)). Qed.
Lemma lem7064677 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064678 (y : real) : (term191 y) = (term201 y).
Proof. exact (MK_COMB (@lem7064677) (@lem7064676 y)). Qed.
Lemma lem7064679 (y : real) : ((term190 y) = (term191 y)) = ((term182 y) = (term201 y)).
Proof. exact (MK_COMB (@lem7064672 y) (@lem7064678 y)). Qed.
Lemma lem7064680 (y : real) : (term182 y) = (term201 y).
Proof. exact (EQ_MP (@lem7064679 y) (@lem7064664 y)). Qed.
Lemma lem7064681 : term184 = term202.
Proof. exact (fun_ext (fun y : real => @lem7064680 y)). Qed.
Lemma lem7064682 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7064683 : term185 = term203.
Proof. exact (MK_COMB (@lem7064682) (@lem7064681)). Qed.
Lemma lem7064684 : term173 = term203.
Proof. exact (TRANS (@lem7064660) (@lem7064683)). Qed.
Lemma lem7064685 : term131 = term203.
Proof. exact (TRANS (@lem7064633) (@lem7064684)). Qed.
Lemma lem7064686 : term107 = term203.
Proof. exact (TRANS (@lem7064460) (@lem7064685)). Qed.
Lemma lem7064687 : term62 = term203.
Proof. exact (TRANS (@lem7064433) (@lem7064686)). Qed.
Lemma lem7064688 (h1 : term62) : term203.
Proof. exact (EQ_MP (@lem7064687) (@lem7064370 h1)). Qed.
Lemma lem7064689 (x : real) : ((term67 x) = x) = ((term67 x) = x).
Proof. exact (eq_refl ((term67 x) = x)). Qed.
Lemma lem7064690 : term68 = term68.
Proof. exact (fun_ext (fun x : real => @lem7064689 x)). Qed.
Lemma lem7064691 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064700 : term69 = term69.
Proof. exact (MK_COMB (@lem7064691) (@lem7064690)). Qed.
Lemma lem7064701 (h1 : term69) : term69.
Proof. exact (EQ_MP (@lem7064700) (@lem7064371 h1)). Qed.
Lemma lem7064702 (x : real) : ((term65 x) = x) = ((term65 x) = x).
Proof. exact (eq_refl ((term65 x) = x)). Qed.
Lemma lem7064703 : term66 = term66.
Proof. exact (fun_ext (fun x : real => @lem7064702 x)). Qed.
Lemma lem7064704 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064713 : term54 = term54.
Proof. exact (MK_COMB (@lem7064704) (@lem7064703)). Qed.
Lemma lem7064714 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem7064713) (@lem7064372 h1)). Qed.
Lemma lem7064715 (y : real) (h1 : term201 y) : term201 y.
Proof. exact (h1). Qed.
Lemma lem7064716 (y' : real) (y : real) (h1 : term198 y' y) : term198 y' y.
Proof. exact (h1). Qed.
Lemma lem7064729 (x : real) : ((term67 x) = x) = ((term67 x) = x).
Proof. exact (eq_refl ((term67 x) = x)). Qed.
Lemma lem7064730 : term68 = term68.
Proof. exact (fun_ext (fun x : real => @lem7064729 x)). Qed.
Lemma lem7064731 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064732 : term69 = term69.
Proof. exact (MK_COMB (@lem7064731) (@lem7064730)). Qed.
Lemma lem7064733 (h1 : term69) : term69.
Proof. exact (EQ_MP (@lem7064732) (@lem7064701 h1)). Qed.
Lemma lem7064746 (x : real) : ((term65 x) = x) = ((term65 x) = x).
Proof. exact (eq_refl ((term65 x) = x)). Qed.
Lemma lem7064747 : term66 = term66.
Proof. exact (fun_ext (fun x : real => @lem7064746 x)). Qed.
Lemma lem7064748 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064749 : term54 = term54.
Proof. exact (MK_COMB (@lem7064748) (@lem7064747)). Qed.
Lemma lem7064750 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem7064749) (@lem7064714 h1)). Qed.
Lemma lem7064787 (y' : real) (y : real) : (term167 y' y) = (term167 y' y).
Proof. exact (eq_refl (term167 y' y)). Qed.
Lemma lem7064798 (y : real) : (term91 y) = (term91 y).
Proof. exact (eq_refl (term91 y)). Qed.
Lemma lem7064807 (y : real) (y' : real) : ((real_add y' y) = y') = ((real_add y' y) = y').
Proof. exact (eq_refl ((real_add y' y) = y')). Qed.
Lemma lem7064808 (y : real) : (term20 y) = (term20 y).
Proof. exact (fun_ext (fun y' : real => @lem7064807 y y')). Qed.
Lemma lem7064809 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064810 (y : real) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem7064809) (@lem7064808 y)). Qed.
Lemma lem7064819 (y : real) (y' : real) : ((real_add y y') = y') = ((real_add y y') = y').
Proof. exact (eq_refl ((real_add y y') = y')). Qed.
Lemma lem7064820 (y : real) : (term19 y) = (term19 y).
Proof. exact (fun_ext (fun y' : real => @lem7064819 y y')). Qed.
Lemma lem7064821 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064822 (y : real) : (term34 y) = (term34 y).
Proof. exact (MK_COMB (@lem7064821) (@lem7064820 y)). Qed.
Lemma lem7064823 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7064824 (y : real) : (term36 y) = (term36 y).
Proof. exact (MK_COMB (@lem7064823) (@lem7064822 y)). Qed.
Lemma lem7064825 (y : real) : (term40 y) = (term40 y).
Proof. exact (MK_COMB (@lem7064824 y) (@lem7064810 y)). Qed.
Lemma lem7064826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7064827 (y : real) : (term96 y) = (term96 y).
Proof. exact (MK_COMB (@lem7064826) (@lem7064825 y)). Qed.
Lemma lem7064828 (y : real) : (term97 y) = (term97 y).
Proof. exact (MK_COMB (@lem7064827 y) (@lem7064798 y)). Qed.
Lemma lem7064829 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7064830 (y : real) : (term98 y) = (term98 y).
Proof. exact (MK_COMB (@lem7064829) (@lem7064828 y)). Qed.
Lemma lem7064831 (y' : real) (y : real) : (term198 y' y) = (term198 y' y).
Proof. exact (MK_COMB (@lem7064830 y) (@lem7064787 y' y)). Qed.
Lemma lem7064832 (y' : real) (y : real) (h1 : term198 y' y) : term198 y' y.
Proof. exact (EQ_MP (@lem7064831 y' y) (@lem7064716 y' y h1)). Qed.
Lemma lem7064833 (y : real) (h1 : term97 y) : term97 y.
Proof. exact (h1). Qed.
Lemma lem7064834 (y' : real) (y : real) (h1 : term167 y' y) : term167 y' y.
Proof. exact (h1). Qed.
Lemma lem7064836 (y : real) (h1 : term97 y) : term40 y.
Proof. exact (proj1 (@lem7064833 y h1)). Qed.
Lemma lem7064837 (y : real) (h1 : term97 y) : term39 y.
Proof. exact (proj2 (@lem7064836 y h1)). Qed.
Lemma lem7064840 (y' : real) (y : real) (h1 : term167 y' y) : term146 y y'.
Proof. exact (proj1 (@lem7064834 y' y h1)). Qed.
Lemma lem7064851 (x : real) : ((term65 x) = x) = ((term65 x) = x).
Proof. exact (eq_refl ((term65 x) = x)). Qed.
Lemma lem7064852 : term66 = term66.
Proof. exact (fun_ext (fun x : real => @lem7064851 x)). Qed.
Lemma lem7064853 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064855 : term54 = term54.
Proof. exact (MK_COMB (@lem7064853) (@lem7064852)). Qed.
Lemma lem7064856 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem7064855) (@lem7064750 h1)). Qed.
Lemma lem7064869 (y : real) (y' : real) : ((real_add y' y) = y') = ((real_add y' y) = y').
Proof. exact (eq_refl ((real_add y' y) = y')). Qed.
Lemma lem7064870 (y : real) : (term20 y) = (term20 y).
Proof. exact (fun_ext (fun y' : real => @lem7064869 y y')). Qed.
Lemma lem7064871 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064873 (y : real) : (term39 y) = (term39 y).
Proof. exact (MK_COMB (@lem7064871) (@lem7064870 y)). Qed.
Lemma lem7064874 (y : real) (h1 : term97 y) : term39 y.
Proof. exact (EQ_MP (@lem7064873 y) (@lem7064837 y h1)). Qed.
Lemma lem7064883 (x : real) : ((term65 x) = x) = ((term65 x) = x).
Proof. exact (eq_refl ((term65 x) = x)). Qed.
Lemma lem7064884 : term66 = term66.
Proof. exact (fun_ext (fun x : real => @lem7064883 x)). Qed.
Lemma lem7064885 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064887 : term54 = term54.
Proof. exact (MK_COMB (@lem7064885) (@lem7064884)). Qed.
Lemma lem7064888 (h1 : term54) : term54.
Proof. exact (EQ_MP (@lem7064887) (@lem7064750 h1)). Qed.
Lemma lem7064896 (y : real) (y' : real) (h1 : term75 y y') : term75 y y'.
Proof. exact (h1). Qed.
Lemma lem7064898 (x : real) : ((term67 x) = x) = ((term67 x) = x).
Proof. exact (eq_refl ((term67 x) = x)). Qed.
Lemma lem7064899 : term68 = term68.
Proof. exact (fun_ext (fun x : real => @lem7064898 x)). Qed.
Lemma lem7064900 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7064902 : term69 = term69.
Proof. exact (MK_COMB (@lem7064900) (@lem7064899)). Qed.
Lemma lem7064903 (h1 : term69) : term69.
Proof. exact (EQ_MP (@lem7064902) (@lem7064733 h1)). Qed.
Lemma lem7064918 (y : real) (y' : real) (h1 : term82 y y') : term82 y y'.
Proof. exact (h1). Qed.
Lemma lem7064922 (_94289 : real) (h1 : term54) : term204 _94289.
Proof. exact (@lem7064856 h1 _94289). Qed.
Lemma lem7064923 (_94289 : real) : (term204 _94289) = ((term65 _94289) = _94289).
Proof. exact (eq_refl (term204 _94289)). Qed.
Lemma lem7064928 (_94291 : real) (y : real) (h1 : term97 y) : term24 y _94291.
Proof. exact (@lem7064874 y h1 _94291). Qed.
Lemma lem7064929 (y : real) (_94291 : real) : (term24 y _94291) = ((real_add _94291 y) = _94291).
Proof. exact (eq_refl (term24 y _94291)). Qed.
Lemma lem7064934 (_94293 : real) (h1 : term54) : term204 _94293.
Proof. exact (@lem7064888 h1 _94293). Qed.
Lemma lem7064935 (_94293 : real) : (term204 _94293) = ((term65 _94293) = _94293).
Proof. exact (eq_refl (term204 _94293)). Qed.
Lemma lem7064937 (_94294 : real) (h1 : term69) : term205 _94294.
Proof. exact (@lem7064903 h1 _94294). Qed.
Lemma lem7064938 (_94294 : real) : (term205 _94294) = ((term67 _94294) = _94294).
Proof. exact (eq_refl (term205 _94294)). Qed.
Lemma lem7064948 (y : real) (h1 : term97 y) : term91 y.
Proof. exact (proj2 (@lem7064833 y h1)). Qed.
Lemma lem7064958 (y' : real) (y : real) (h1 : term167 y' y) : y = term4.
Proof. exact (proj2 (@lem7064834 y' y h1)). Qed.
Lemma lem7064960 (y : real) (y' : real) (h1 : term75 y y') : term75 y y'.
Proof. exact (h1). Qed.
Lemma lem7064966 (y' : real) (y : real) (h1 : term167 y' y) : y = term4.
Proof. exact (proj2 (@lem7064834 y' y h1)). Qed.
Lemma lem7064968 (y : real) (y' : real) (h1 : term82 y y') : term82 y y'.
Proof. exact (h1). Qed.
Lemma lem7065011 (y' : real) : (term206 y') = (term206 y').
Proof. exact (eq_refl (term206 y')). Qed.
Lemma lem7065012 (y' : real) (y : real) (h1 : term167 y' y) : (term207 y' y) = (term208 y').
Proof. exact (MK_COMB (@lem7065011 y') (@lem7064958 y' y h1)). Qed.
Lemma lem7065013 (y' : real) : (term208 y') = (term209 y').
Proof. exact (eq_refl (term208 y')). Qed.
Lemma lem7065014 (y' : real) (y : real) : (term210 y' y) = (term210 y' y).
Proof. exact (eq_refl (term210 y' y)). Qed.
Lemma lem7065015 (y : real) (y' : real) : ((term207 y' y) = (term208 y')) = ((term207 y' y) = (term209 y')).
Proof. exact (MK_COMB (@lem7065014 y' y) (@lem7065013 y')). Qed.
Lemma lem7065016 (y : real) (y' : real) : (term207 y' y) = (term75 y y').
Proof. exact (eq_refl (term207 y' y)). Qed.
Lemma lem7065017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7065018 (y : real) (y' : real) : (term210 y' y) = (term211 y y').
Proof. exact (MK_COMB (@lem7065017) (@lem7065016 y y')). Qed.
Lemma lem7065019 (y' : real) : (term209 y') = (term209 y').
Proof. exact (eq_refl (term209 y')). Qed.
Lemma lem7065020 (y : real) (y' : real) : ((term207 y' y) = (term209 y')) = ((term75 y y') = (term209 y')).
Proof. exact (MK_COMB (@lem7065018 y y') (@lem7065019 y')). Qed.
Lemma lem7065021 (y : real) (y' : real) : ((term207 y' y) = (term208 y')) = ((term75 y y') = (term209 y')).
Proof. exact (TRANS (@lem7065015 y y') (@lem7065020 y y')). Qed.
Lemma lem7065022 (y' : real) (y : real) (h1 : term167 y' y) : (term75 y y') = (term209 y').
Proof. exact (EQ_MP (@lem7065021 y y') (@lem7065012 y' y h1)). Qed.
Lemma lem7065023 (y' : real) (y : real) (h1 : term75 y y') (h2 : term167 y' y) : term209 y'.
Proof. exact (EQ_MP (@lem7065022 y' y h2) (@lem7064960 y y' h1)). Qed.
Lemma lem7065066 (y' : real) : (term212 y') = (term212 y').
Proof. exact (eq_refl (term212 y')). Qed.
Lemma lem7065067 (y' : real) (y : real) (h1 : term167 y' y) : (term213 y' y) = (term214 y').
Proof. exact (MK_COMB (@lem7065066 y') (@lem7064966 y' y h1)). Qed.
Lemma lem7065068 (y' : real) : (term214 y') = (term215 y').
Proof. exact (eq_refl (term214 y')). Qed.
Lemma lem7065069 (y' : real) (y : real) : (term216 y' y) = (term216 y' y).
Proof. exact (eq_refl (term216 y' y)). Qed.
Lemma lem7065070 (y : real) (y' : real) : ((term213 y' y) = (term214 y')) = ((term213 y' y) = (term215 y')).
Proof. exact (MK_COMB (@lem7065069 y' y) (@lem7065068 y')). Qed.
Lemma lem7065071 (y : real) (y' : real) : (term213 y' y) = (term82 y y').
Proof. exact (eq_refl (term213 y' y)). Qed.
Lemma lem7065072 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7065073 (y : real) (y' : real) : (term216 y' y) = (term217 y y').
Proof. exact (MK_COMB (@lem7065072) (@lem7065071 y y')). Qed.
Lemma lem7065074 (y' : real) : (term215 y') = (term215 y').
Proof. exact (eq_refl (term215 y')). Qed.
Lemma lem7065075 (y : real) (y' : real) : ((term213 y' y) = (term215 y')) = ((term82 y y') = (term215 y')).
Proof. exact (MK_COMB (@lem7065073 y y') (@lem7065074 y')). Qed.
Lemma lem7065076 (y : real) (y' : real) : ((term213 y' y) = (term214 y')) = ((term82 y y') = (term215 y')).
Proof. exact (TRANS (@lem7065070 y y') (@lem7065075 y y')). Qed.
Lemma lem7065077 (y' : real) (y : real) (h1 : term167 y' y) : (term82 y y') = (term215 y').
Proof. exact (EQ_MP (@lem7065076 y y') (@lem7065067 y' y h1)). Qed.
Lemma lem7065078 (y' : real) (y : real) (h1 : term82 y y') (h2 : term167 y' y) : term215 y'.
Proof. exact (EQ_MP (@lem7065077 y' y h2) (@lem7064968 y y' h1)). Qed.
Lemma lem7065111 (x : real) (y : real) (z : real) : term218 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem7065115 (_94289 : real) (h1 : term54) : (term65 _94289) = _94289.
Proof. exact (EQ_MP (@lem7064923 _94289) (@lem7064922 _94289 h1)). Qed.
Lemma lem7065116 (y : real) (h1 : term54) : (term65 y) = y.
Proof. exact (@lem7065115 y h1). Qed.
Lemma lem7065117 (y : real) (h1 : term54) : term219 y.
Proof. exact (fun h0 : term209 y => @lem7065116 y h1). Qed.
Lemma lem7065119 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7065120 (y : real) : (term219 y) = ((term65 y) = y).
Proof. exact (@lem7065119 ((term65 y) = y)). Qed.
Lemma lem7065121 (y : real) (h1 : term54) : (term65 y) = y.
Proof. exact (EQ_MP (@lem7065120 y) (@lem7065117 y h1)). Qed.
Lemma lem7065123 (_94291 : real) (y : real) (h1 : term97 y) : (real_add _94291 y) = _94291.
Proof. exact (EQ_MP (@lem7064929 y _94291) (@lem7064928 _94291 y h1)). Qed.
Lemma lem7065124 (y : real) (h1 : term97 y) : (term65 y) = term4.
Proof. exact (@lem7065123 term4 y h1). Qed.
Lemma lem7065125 (y : real) (h1 : term97 y) : term221 y.
Proof. exact (fun h0 : term222 y => @lem7065124 y h1). Qed.
Lemma lem7065127 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7065128 (y : real) : (term221 y) = ((term65 y) = term4).
Proof. exact (@lem7065127 ((term65 y) = term4)). Qed.
Lemma lem7065129 (y : real) (h1 : term97 y) : (term65 y) = term4.
Proof. exact (EQ_MP (@lem7065128 y) (@lem7065125 y h1)). Qed.
Lemma lem7065147 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7065148 (y : real) (x : real) (z : real) : (term223 x y z) = (term224 y x z).
Proof. exact (@lem7065147 (y = z) (term225 x z)). Qed.
Lemma lem7065158 (x : real) (y : real) : (term226 x y) = (term226 x y).
Proof. exact (eq_refl (term226 x y)). Qed.
Lemma lem7065159 (y : real) (x : real) (z : real) : (term218 x y z) = (term227 y x z).
Proof. exact (MK_COMB (@lem7065158 x y) (@lem7065148 y x z)). Qed.
Lemma lem7065163 (q : Prop) (p : Prop) (r : Prop) : (term228 p q r) = (term228 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7065164 (y : real) (x : real) (z : real) : (term227 y x z) = (term229 y x z).
Proof. exact (@lem7065163 (y = z) (term225 x y) (term225 x z)). Qed.
Lemma lem7065186 (y : real) (x : real) (z : real) : (term218 x y z) = (term229 y x z).
Proof. exact (TRANS (@lem7065159 y x z) (@lem7065164 y x z)). Qed.
Lemma lem7065187 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7065188 (y : real) (x : real) (z : real) : (term230 x y z) = (term231 y x z).
Proof. exact (MK_COMB (@lem7065187) (@lem7065186 y x z)). Qed.
Lemma lem7065210 (y : real) (x : real) (z : real) : (term229 y x z) = (term229 y x z).
Proof. exact (eq_refl (term229 y x z)). Qed.
Lemma lem7065211 (y : real) (x : real) (z : real) : ((term218 x y z) = (term229 y x z)) = ((term229 y x z) = (term229 y x z)).
Proof. exact (MK_COMB (@lem7065188 y x z) (@lem7065210 y x z)). Qed.
Lemma lem7065213 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7065214 (x : Prop) : (x = x) = True.
Proof. exact (@lem7065213 Prop x). Qed.
Lemma lem7065215 (y : real) (x : real) (z : real) : ((term229 y x z) = (term229 y x z)) = True.
Proof. exact (@lem7065214 (term229 y x z)). Qed.
Lemma lem7065216 (y : real) (x : real) (z : real) : ((term218 x y z) = (term229 y x z)) = True.
Proof. exact (TRANS (@lem7065211 y x z) (@lem7065215 y x z)). Qed.
Lemma lem7065217 (y : real) (x : real) (z : real) : True = ((term218 x y z) = (term229 y x z)).
Proof. exact (SYM (@lem7065216 y x z)). Qed.
Lemma lem7065218 (y : real) (x : real) (z : real) : (term218 x y z) = (term229 y x z).
Proof. exact (EQ_MP (@lem7065217 y x z) (@lem0)). Qed.
Lemma lem7065219 (y : real) (x : real) (z : real) : term229 y x z.
Proof. exact (EQ_MP (@lem7065218 y x z) (@lem7065111 x y z)). Qed.
Lemma lem7065221 (b : Prop) (a : Prop) : (a \/ b) = (term232 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7065222 (x : real) (y : real) (z : real) : (term229 y x z) = (term233 x y z).
Proof. exact (@lem7065221 (term234 y x z) (y = z)). Qed.
Lemma lem7065224 (a : Prop) (b : Prop) : (term235 a b) = (term236 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7065225 (y : real) (x : real) (z : real) : (term237 y x z) = (term238 y x z).
Proof. exact (@lem7065224 (term225 x y) (term225 x z)). Qed.
Lemma lem7065227 (a : Prop) : (term239 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7065228 (x : real) (y : real) : (term240 x y) = (x = y).
Proof. exact (@lem7065227 (x = y)). Qed.
Lemma lem7065229 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7065230 (x : real) (y : real) : (term241 x y) = (term242 x y).
Proof. exact (MK_COMB (@lem7065229) (@lem7065228 x y)). Qed.
Lemma lem7065232 (a : Prop) : (term239 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7065233 (x : real) (z : real) : (term240 x z) = (x = z).
Proof. exact (@lem7065232 (x = z)). Qed.
Lemma lem7065234 (y : real) (x : real) (z : real) : (term238 y x z) = (term243 y x z).
Proof. exact (MK_COMB (@lem7065230 x y) (@lem7065233 x z)). Qed.
Lemma lem7065235 (y : real) (x : real) (z : real) : (term237 y x z) = (term243 y x z).
Proof. exact (TRANS (@lem7065225 y x z) (@lem7065234 y x z)). Qed.
Lemma lem7065236 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7065237 (y : real) (x : real) (z : real) : (term244 y x z) = (term245 y x z).
Proof. exact (MK_COMB (@lem7065236) (@lem7065235 y x z)). Qed.
Lemma lem7065238 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7065239 (x : real) (y : real) (z : real) : (term233 x y z) = (term246 x y z).
Proof. exact (MK_COMB (@lem7065237 y x z) (@lem7065238 y z)). Qed.
Lemma lem7065240 (x : real) (y : real) (z : real) : (term229 y x z) = (term246 x y z).
Proof. exact (TRANS (@lem7065222 x y z) (@lem7065239 x y z)). Qed.
Lemma lem7065242 (y : real) (h1 : term54) (h2 : term97 y) : term247 y.
Proof. exact (conj (@lem7065121 y h1) (@lem7065129 y h2)). Qed.
Lemma lem7065244 (x : real) (y : real) (z : real) : term246 x y z.
Proof. exact (EQ_MP (@lem7065240 x y z) (@lem7065219 y x z)). Qed.
Lemma lem7065245 (y : real) : term248 y.
Proof. exact (@lem7065244 (term65 y) y term4). Qed.
Lemma lem7065248 (y : real) (h1 : term54) (h2 : term97 y) : y = term4.
Proof. exact (@lem7065245 y (@lem7065242 y h1 h2)). Qed.
Lemma lem7065249 (y : real) (h1 : term54) (h2 : term97 y) : term249 y.
Proof. exact (fun h0 : term91 y => @lem7065248 y h1 h2). Qed.
Lemma lem7065251 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7065252 (y : real) : (term249 y) = (y = term4).
Proof. exact (@lem7065251 (y = term4)). Qed.
Lemma lem7065253 (y : real) (h1 : term54) (h2 : term97 y) : y = term4.
Proof. exact (EQ_MP (@lem7065252 y) (@lem7065249 y h1 h2)). Qed.
Lemma lem7065256 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7065258 (y : real) : (term91 y) = (term250 y).
Proof. exact (@lem7065256 (y = term4)). Qed.
Lemma lem7065261 (y : real) (h1 : term97 y) : term250 y.
Proof. exact (EQ_MP (@lem7065258 y) (@lem7064948 y h1)). Qed.
Lemma lem7065264 (y : real) (h1 : term54) (h2 : term97 y) : False.
Proof. exact (@lem7065261 y h2 (@lem7065253 y h1 h2)). Qed.
Lemma lem7065265 (y : real) (h1 : term54) (h2 : term97 y) : term251.
Proof. exact (fun h0 : ~ False => @lem7065264 y h1 h2). Qed.
Lemma lem7065267 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7065268 : term251 = False.
Proof. exact (@lem7065267 False). Qed.
Lemma lem7065269 (y : real) (h1 : term54) (h2 : term97 y) : False.
Proof. exact (EQ_MP (@lem7065268) (@lem7065265 y h1 h2)). Qed.
Lemma lem7065306 (_94293 : real) (h1 : term54) : (term65 _94293) = _94293.
Proof. exact (EQ_MP (@lem7064935 _94293) (@lem7064934 _94293 h1)). Qed.
Lemma lem7065307 (y' : real) (h1 : term54) : (term65 y') = y'.
Proof. exact (@lem7065306 y' h1). Qed.
Lemma lem7065308 (y' : real) (h1 : term54) : term219 y'.
Proof. exact (fun h0 : term209 y' => @lem7065307 y' h1). Qed.
Lemma lem7065310 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7065311 (y' : real) : (term219 y') = ((term65 y') = y').
Proof. exact (@lem7065310 ((term65 y') = y')). Qed.
Lemma lem7065312 (y' : real) (h1 : term54) : (term65 y') = y'.
Proof. exact (EQ_MP (@lem7065311 y') (@lem7065308 y' h1)). Qed.
Lemma lem7065315 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7065317 (y' : real) : (term209 y') = (term252 y').
Proof. exact (@lem7065315 ((term65 y') = y')). Qed.
Lemma lem7065320 (y' : real) (y : real) (h1 : term75 y y') (h2 : term167 y' y) : term252 y'.
Proof. exact (EQ_MP (@lem7065317 y') (@lem7065023 y' y h1 h2)). Qed.
Lemma lem7065323 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (@lem7065320 y' y h2 h3 (@lem7065312 y' h1)). Qed.
Lemma lem7065324 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : term251.
Proof. exact (fun h0 : ~ False => @lem7065323 y' y h1 h2 h3). Qed.
Lemma lem7065326 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7065327 : term251 = False.
Proof. exact (@lem7065326 False). Qed.
Lemma lem7065365 (_94294 : real) (h1 : term69) : (term67 _94294) = _94294.
Proof. exact (EQ_MP (@lem7064938 _94294) (@lem7064937 _94294 h1)). Qed.
Lemma lem7065366 (y' : real) (h1 : term69) : (term67 y') = y'.
Proof. exact (@lem7065365 y' h1). Qed.
Lemma lem7065367 (y' : real) (h1 : term69) : term253 y'.
Proof. exact (fun h0 : term215 y' => @lem7065366 y' h1). Qed.
Lemma lem7065369 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7065370 (y' : real) : (term253 y') = ((term67 y') = y').
Proof. exact (@lem7065369 ((term67 y') = y')). Qed.
Lemma lem7065371 (y' : real) (h1 : term69) : (term67 y') = y'.
Proof. exact (EQ_MP (@lem7065370 y') (@lem7065367 y' h1)). Qed.
Lemma lem7065374 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7065376 (y' : real) : (term215 y') = (term254 y').
Proof. exact (@lem7065374 ((term67 y') = y')). Qed.
Lemma lem7065379 (y' : real) (y : real) (h1 : term82 y y') (h2 : term167 y' y) : term254 y'.
Proof. exact (EQ_MP (@lem7065376 y') (@lem7065078 y' y h1 h2)). Qed.
Lemma lem7065382 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (@lem7065379 y' y h2 h3 (@lem7065371 y' h1)). Qed.
Lemma lem7065383 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : term251.
Proof. exact (fun h0 : ~ False => @lem7065382 y' y h1 h2 h3). Qed.
Lemma lem7065385 (p : Prop) : (term220 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7065386 : term251 = False.
Proof. exact (@lem7065385 False). Qed.
Lemma lem7065388 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem7065386) (@lem7065383 y' y h1 h2 h3)). Qed.
Lemma lem7065389 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem7065327) (@lem7065324 y' y h1 h2 h3)). Qed.
Lemma lem7065390 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : (term82 y y') = False.
Proof. exact (prop_ext (fun h4 : term82 y y' => @lem7065388 y' y h1 h2 h3) (fun h4 : False => @lem7064968 y y' h2)). Qed.
Lemma lem7065391 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem7065390 y' y h1 h2 h3) (@lem7064968 y y' h2)). Qed.
Lemma lem7065392 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : (term75 y y') = False.
Proof. exact (prop_ext (fun h4 : term75 y y' => @lem7065389 y' y h1 h2 h3) (fun h4 : False => @lem7064960 y y' h2)). Qed.
Lemma lem7065393 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem7065392 y' y h1 h2 h3) (@lem7064960 y y' h2)). Qed.
Lemma lem7065394 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : (term82 y y') = False.
Proof. exact (prop_ext (fun h4 : term82 y y' => @lem7065391 y' y h1 h2 h3) (fun h4 : False => @lem7064918 y y' h2)). Qed.
Lemma lem7065395 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem7065394 y' y h1 h2 h3) (@lem7064918 y y' h2)). Qed.
Lemma lem7065396 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : (term75 y y') = False.
Proof. exact (prop_ext (fun h4 : term75 y y' => @lem7065393 y' y h1 h2 h3) (fun h4 : False => @lem7064896 y y' h2)). Qed.
Lemma lem7065397 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem7065396 y' y h1 h2 h3) (@lem7064896 y y' h2)). Qed.
Lemma lem7065398 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : (term82 y y') = False.
Proof. exact (prop_ext (fun h4 : term82 y y' => @lem7065395 y' y h1 h2 h3) (fun h4 : False => @lem7064918 y y' h2)). Qed.
Lemma lem7065399 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem7065398 y' y h1 h2 h3) (@lem7064918 y y' h2)). Qed.
Lemma lem7065400 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : term69 = False.
Proof. exact (prop_ext (fun h4 : term69 => @lem7065399 y' y h1 h2 h3) (fun h4 : False => @lem7064903 h1)). Qed.
Lemma lem7065401 (y' : real) (y : real) (h1 : term69) (h2 : term82 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem7065400 y' y h1 h2 h3) (@lem7064903 h1)). Qed.
Lemma lem7065402 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : (term75 y y') = False.
Proof. exact (prop_ext (fun h4 : term75 y y' => @lem7065397 y' y h1 h2 h3) (fun h4 : False => @lem7064896 y y' h2)). Qed.
Lemma lem7065403 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem7065402 y' y h1 h2 h3) (@lem7064896 y y' h2)). Qed.
Lemma lem7065404 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : term54 = False.
Proof. exact (prop_ext (fun h4 : term54 => @lem7065403 y' y h1 h2 h3) (fun h4 : False => @lem7064888 h1)). Qed.
Lemma lem7065405 (y' : real) (y : real) (h1 : term54) (h2 : term75 y y') (h3 : term167 y' y) : False.
Proof. exact (EQ_MP (@lem7065404 y' y h1 h2 h3) (@lem7064888 h1)). Qed.
Lemma lem7065406 (y : real) (h1 : term54) (h2 : term97 y) : term54 = False.
Proof. exact (prop_ext (fun h3 : term54 => @lem7065269 y h1 h2) (fun h3 : False => @lem7064856 h1)). Qed.
Lemma lem7065407 (y : real) (h1 : term54) (h2 : term97 y) : False.
Proof. exact (EQ_MP (@lem7065406 y h1 h2) (@lem7064856 h1)). Qed.
Lemma lem7065408 (y' : real) (y : real) (h1 : term69) (h2 : term54) (h3 : term167 y' y) : False.
Proof. exact (or_elim (@lem7064840 y' y h3) (fun h0 : term75 y y' => @lem7065405 y' y h2 h0 h3) (fun h0 : term82 y y' => @lem7065401 y' y h1 h0 h3)). Qed.
Lemma lem7065409 (y' : real) (y : real) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : False.
Proof. exact (or_elim (@lem7064832 y' y h3) (fun h0 : term97 y => @lem7065407 y h2 h0) (fun h0 : term167 y' y => @lem7065408 y' y h1 h2 h0)). Qed.
Lemma lem7065410 (y' : real) (y : real) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : (term198 y' y) = False.
Proof. exact (prop_ext (fun h4 : term198 y' y => @lem7065409 y' y h1 h2 h3) (fun h4 : False => @lem7064832 y' y h3)). Qed.
Lemma lem7065411 (y' : real) (y : real) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : False.
Proof. exact (EQ_MP (@lem7065410 y' y h1 h2 h3) (@lem7064832 y' y h3)). Qed.
Lemma lem7065412 (y' : real) (y : real) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : term54 = False.
Proof. exact (prop_ext (fun h4 : term54 => @lem7065411 y' y h1 h2 h3) (fun h4 : False => @lem7064750 h2)). Qed.
Lemma lem7065413 (y' : real) (y : real) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : False.
Proof. exact (EQ_MP (@lem7065412 y' y h1 h2 h3) (@lem7064750 h2)). Qed.
Lemma lem7065414 (y' : real) (y : real) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : term69 = False.
Proof. exact (prop_ext (fun h4 : term69 => @lem7065413 y' y h1 h2 h3) (fun h4 : False => @lem7064733 h1)). Qed.
Lemma lem7065415 (y' : real) (y : real) (h1 : term69) (h2 : term54) (h3 : term198 y' y) : False.
Proof. exact (EQ_MP (@lem7065414 y' y h1 h2 h3) (@lem7064733 h1)). Qed.
Lemma lem7065416 (y : real) (h1 : term69) (h2 : term54) (h3 : term201 y) : False.
Proof. exact (ex_elim (@lem7064715 y h3) (fun y' : real => fun h0 : term200 y y' => @lem7065415 y' y h1 h2 h0)). Qed.
Lemma lem7065417 (h1 : term69) (h2 : term54) (h3 : term62) : False.
Proof. exact (ex_elim (@lem7064688 h3) (fun y : real => fun h0 : term202 y => @lem7065416 y h1 h2 h0)). Qed.
Lemma lem7065418 (h1 : term69) (h2 : term54) (h3 : term62) : term54 = False.
Proof. exact (prop_ext (fun h4 : term54 => @lem7065417 h1 h2 h3) (fun h4 : False => @lem7064714 h2)). Qed.
Lemma lem7065419 (h1 : term69) (h2 : term54) (h3 : term62) : False.
Proof. exact (EQ_MP (@lem7065418 h1 h2 h3) (@lem7064714 h2)). Qed.
Lemma lem7065420 (h1 : term69) (h2 : term54) (h3 : term62) : term69 = False.
Proof. exact (prop_ext (fun h4 : term69 => @lem7065419 h1 h2 h3) (fun h4 : False => @lem7064701 h1)). Qed.
Lemma lem7065421 (h1 : term69) (h2 : term54) (h3 : term62) : False.
Proof. exact (EQ_MP (@lem7065420 h1 h2 h3) (@lem7064701 h1)). Qed.
Lemma lem7065422 (h1 : term69) (h2 : term62) : term52.
Proof. exact (fun h0 : term54 => @lem7065421 h1 h0 h2). Qed.
Lemma lem7065423 : term52 = term53.
Proof. exact (@lem69 term54). Qed.
Lemma lem7065424 (h1 : term69) (h2 : term62) : term53.
Proof. exact (EQ_MP (@lem7065423) (@lem7065422 h1 h2)). Qed.
Lemma lem7065425 (h1 : term62) : term57.
Proof. exact (fun h0 : term69 => @lem7065424 h0 h1). Qed.
Lemma lem7065426 : term64.
Proof. exact (fun h0 : term62 => @lem7065425 h0). Qed.
Lemma lem7065427 : term9.
Proof. exact (EQ_MP (@lem7064369) (@lem7065426)). Qed.
Lemma lem7065429 : term9.
Proof. exact (@lem7064195 (@lem7065427)). Qed.
Lemma lem7065430 (h1 : term8) : term56.
Proof. exact (@lem7065429 (@lem7064180 h1)). Qed.
Lemma lem7065431 (h1 : term8) : term52.
Proof. exact (@lem7065430 h1 (@lem1361590)). Qed.
Lemma lem7065432 (h1 : term8) : False.
Proof. exact (@lem7065431 h1 (@lem1338512)). Qed.
Lemma lem7065433 (h1 : term8) : term8 = False.
Proof. exact (prop_ext (fun h2 : term8 => @lem7065432 h1) (fun h2 : False => @lem7064180 h1)). Qed.
Lemma lem7065434 (h1 : term8) : False.
Proof. exact (EQ_MP (@lem7065433 h1) (@lem7064180 h1)). Qed.
Lemma lem7065435 : term7.
Proof. exact (fun h0 : term8 => @lem7065434 h0). Qed.
Lemma lem7065436 : term6.
Proof. exact (EQ_MP (@lem7064179) (@lem7065435)). Qed.
Lemma lem7065437 : term255 = term4.
Proof. exact (@lem7064175 (@lem7065436)). Qed.
