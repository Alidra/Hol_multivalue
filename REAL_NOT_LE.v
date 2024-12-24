Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NOT_LE_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483523_spec.
Require Import thm1483531_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm16933_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm912739_spec.
Lemma lem1495229 (x : real) (y : real) : (term0 x y) = (real_le x y).
Proof. exact (@lem16933 (real_le x y)). Qed.
Lemma lem1495231 (y : real) (x : real) : (real_lt y x) = (real_lt y x).
Proof. exact (eq_refl (real_lt y x)). Qed.
Lemma lem1495232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1495233 (x : real) (y : real) : (term1 x y) = (term2 x y).
Proof. exact (MK_COMB (@lem1495232) (@lem1495229 x y)). Qed.
Lemma lem1495234 (y : real) (x : real) : (term3 y x) = (term4 y x).
Proof. exact (MK_COMB (@lem1495233 x y) (@lem1495231 y x)). Qed.
Lemma lem1495239 (y : real) (x : real) : (term5 y x) = (term5 y x).
Proof. exact (eq_refl (term5 y x)). Qed.
Lemma lem1495240 (y : real) (x : real) : (term6 y x) = (term7 y x).
Proof. exact (MK_COMB (@lem1495239 y x) (@lem1495234 y x)). Qed.
Lemma lem1495241 (y : real) (x : real) : (term8 y x) = (term6 y x).
Proof. exact (@lem17646 (term9 x y) (real_lt y x)). Qed.
Lemma lem1495242 (y : real) (x : real) : (term8 y x) = (term7 y x).
Proof. exact (TRANS (@lem1495241 y x) (@lem1495240 y x)). Qed.
Lemma lem1495243 (P : real -> Prop) : (term10 P) = (term11 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1495244 (x : real) : (term12 x) = (term13 x).
Proof. exact (@lem1495243 (term14 x)). Qed.
Lemma lem1495245 (y : real) (x : real) : (term15 x y) = ((term9 x y) = (real_lt y x)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1495246 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1495247 (y : real) (x : real) : (term16 x y) = (term8 y x).
Proof. exact (MK_COMB (@lem1495246) (@lem1495245 y x)). Qed.
Lemma lem1495248 (y : real) (x : real) : (term16 x y) = (term7 y x).
Proof. exact (TRANS (@lem1495247 y x) (@lem1495242 y x)). Qed.
Lemma lem1495249 (x : real) : (term17 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1495248 y x)). Qed.
Lemma lem1495250 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495251 (x : real) : (term13 x) = (term19 x).
Proof. exact (MK_COMB (@lem1495250) (@lem1495249 x)). Qed.
Lemma lem1495252 (x : real) : (term12 x) = (term19 x).
Proof. exact (TRANS (@lem1495244 x) (@lem1495251 x)). Qed.
Lemma lem1495253 (P : real -> Prop) : (term10 P) = (term11 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1495254 : term20 = term21.
Proof. exact (@lem1495253 term22). Qed.
Lemma lem1495255 (x : real) : (term23 x) = (term24 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem1495256 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1495257 (x : real) : (term25 x) = (term12 x).
Proof. exact (MK_COMB (@lem1495256) (@lem1495255 x)). Qed.
Lemma lem1495258 (x : real) : (term25 x) = (term19 x).
Proof. exact (TRANS (@lem1495257 x) (@lem1495252 x)). Qed.
Lemma lem1495259 : term26 = term27.
Proof. exact (fun_ext (fun x : real => @lem1495258 x)). Qed.
Lemma lem1495260 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495261 : term21 = term28.
Proof. exact (MK_COMB (@lem1495260) (@lem1495259)). Qed.
Lemma lem1495263 : term20 = term28.
Proof. exact (TRANS (@lem1495254) (@lem1495261)). Qed.
Lemma lem1495280 (y : real) (x : real) : (term7 y x) = (term7 y x).
Proof. exact (eq_refl (term7 y x)). Qed.
Lemma lem1495281 (x : real) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1495280 y x)). Qed.
Lemma lem1495282 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495283 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem1495282) (@lem1495281 x)). Qed.
Lemma lem1495284 : term27 = term27.
Proof. exact (fun_ext (fun x : real => @lem1495283 x)). Qed.
Lemma lem1495285 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495286 : term28 = term28.
Proof. exact (MK_COMB (@lem1495285) (@lem1495284)). Qed.
Lemma lem1495287 : term20 = term28.
Proof. exact (TRANS (@lem1495263) (@lem1495286)). Qed.
Lemma lem1495288 (x : real) (y : real) : (term9 x y) = (term29 x y).
Proof. exact (@lem1483533 x y). Qed.
Lemma lem1495301 (x : real) (y : real) : (real_sub x y) = (term30 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1495302 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1495303 (x : real) (y : real) : (term31 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem1495302) (@lem1495301 x y)). Qed.
Lemma lem1495304 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1495305 (x : real) (y : real) : (term29 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1495303 x y) (@lem1495304)). Qed.
Lemma lem1495306 (x : real) (y : real) : (term9 x y) = (term34 x y).
Proof. exact (TRANS (@lem1495288 x y) (@lem1495305 x y)). Qed.
Lemma lem1495307 (y : real) (x : real) : (term35 y x) = (term36 y x).
Proof. exact (@lem1483531 y x). Qed.
Lemma lem1495313 (y : real) (x : real) : (real_sub y x) = (term30 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1495318 (x : real) (y : real) : (term30 y x) = (term37 x y).
Proof. exact (@lem1483488 (term38 x) y). Qed.
Lemma lem1495320 (x : real) (y : real) : (real_sub y x) = (term37 x y).
Proof. exact (TRANS (@lem1495313 y x) (@lem1495318 x y)). Qed.
Lemma lem1495321 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1495322 (x : real) (y : real) : (term39 y x) = (term40 x y).
Proof. exact (MK_COMB (@lem1495321) (@lem1495320 x y)). Qed.
Lemma lem1495323 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1495324 (x : real) (y : real) : (term36 y x) = (term41 x y).
Proof. exact (MK_COMB (@lem1495322 x y) (@lem1495323)). Qed.
Lemma lem1495325 (x : real) (y : real) : (term35 y x) = (term41 x y).
Proof. exact (TRANS (@lem1495307 y x) (@lem1495324 x y)). Qed.
Lemma lem1495326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1495327 (x : real) (y : real) : (term42 x y) = (term43 x y).
Proof. exact (MK_COMB (@lem1495326) (@lem1495306 x y)). Qed.
Lemma lem1495328 (x : real) (y : real) : (term44 y x) = (term45 x y).
Proof. exact (MK_COMB (@lem1495327 x y) (@lem1495325 x y)). Qed.
Lemma lem1495329 (y : real) (x : real) : (real_le x y) = (term36 y x).
Proof. exact (@lem1483523 y x). Qed.
Lemma lem1495335 (y : real) (x : real) : (real_sub y x) = (term30 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1495340 (x : real) (y : real) : (term30 y x) = (term37 x y).
Proof. exact (@lem1483488 (term38 x) y). Qed.
Lemma lem1495342 (x : real) (y : real) : (real_sub y x) = (term37 x y).
Proof. exact (TRANS (@lem1495335 y x) (@lem1495340 x y)). Qed.
Lemma lem1495343 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1495344 (x : real) (y : real) : (term39 y x) = (term40 x y).
Proof. exact (MK_COMB (@lem1495343) (@lem1495342 x y)). Qed.
Lemma lem1495345 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1495346 (x : real) (y : real) : (term36 y x) = (term41 x y).
Proof. exact (MK_COMB (@lem1495344 x y) (@lem1495345)). Qed.
Lemma lem1495347 (x : real) (y : real) : (real_le x y) = (term41 x y).
Proof. exact (TRANS (@lem1495329 y x) (@lem1495346 x y)). Qed.
Lemma lem1495348 (x : real) (y : real) : (real_lt y x) = (term29 x y).
Proof. exact (@lem1483521 x y). Qed.
Lemma lem1495361 (x : real) (y : real) : (real_sub x y) = (term30 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1495362 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1495363 (x : real) (y : real) : (term31 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem1495362) (@lem1495361 x y)). Qed.
Lemma lem1495364 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1495365 (x : real) (y : real) : (term29 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1495363 x y) (@lem1495364)). Qed.
Lemma lem1495366 (x : real) (y : real) : (real_lt y x) = (term34 x y).
Proof. exact (TRANS (@lem1495348 x y) (@lem1495365 x y)). Qed.
Lemma lem1495367 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1495368 (x : real) (y : real) : (term2 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem1495367) (@lem1495347 x y)). Qed.
Lemma lem1495369 (x : real) (y : real) : (term4 y x) = (term47 x y).
Proof. exact (MK_COMB (@lem1495368 x y) (@lem1495366 x y)). Qed.
Lemma lem1495370 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1495371 (x : real) (y : real) : (term5 y x) = (term48 x y).
Proof. exact (MK_COMB (@lem1495370) (@lem1495328 x y)). Qed.
Lemma lem1495372 (x : real) (y : real) : (term7 y x) = (term49 x y).
Proof. exact (MK_COMB (@lem1495371 x y) (@lem1495369 x y)). Qed.
Lemma lem1495373 (x : real) : (term18 x) = (term50 x).
Proof. exact (fun_ext (fun y : real => @lem1495372 x y)). Qed.
Lemma lem1495374 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495375 (x : real) : (term19 x) = (term51 x).
Proof. exact (MK_COMB (@lem1495374) (@lem1495373 x)). Qed.
Lemma lem1495376 : term27 = term52.
Proof. exact (fun_ext (fun x : real => @lem1495375 x)). Qed.
Lemma lem1495377 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495378 : term28 = term53.
Proof. exact (MK_COMB (@lem1495377) (@lem1495376)). Qed.
Lemma lem1495379 : term20 = term53.
Proof. exact (TRANS (@lem1495287) (@lem1495378)). Qed.
Lemma lem1495385 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1495386 (P : real -> Prop) (Q : real -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem1495385 real P Q). Qed.
Lemma lem1495387 (x : real) : (term58 x) = (term59 x).
Proof. exact (@lem1495386 (term60 x) (term61 x)). Qed.
Lemma lem1495388 (x : real) (y : real) : (term62 x y) = (term45 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1495389 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1495390 (x : real) (y : real) : (term63 x y) = (term48 x y).
Proof. exact (MK_COMB (@lem1495389) (@lem1495388 x y)). Qed.
Lemma lem1495391 (x : real) (y : real) : (term64 x y) = (term47 x y).
Proof. exact (eq_refl (term64 x y)). Qed.
Lemma lem1495392 (x : real) (y : real) : (term65 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem1495390 x y) (@lem1495391 x y)). Qed.
Lemma lem1495393 (x : real) : (term66 x) = (term50 x).
Proof. exact (fun_ext (fun y : real => @lem1495392 x y)). Qed.
Lemma lem1495394 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495395 (x : real) : (term58 x) = (term51 x).
Proof. exact (MK_COMB (@lem1495394) (@lem1495393 x)). Qed.
Lemma lem1495396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1495397 (x : real) : (term67 x) = (term68 x).
Proof. exact (MK_COMB (@lem1495396) (@lem1495395 x)). Qed.
Lemma lem1495398 (x : real) (y : real) : (term62 x y) = (term45 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1495399 (x : real) : (term69 x) = (term60 x).
Proof. exact (fun_ext (fun y : real => @lem1495398 x y)). Qed.
Lemma lem1495400 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495401 (x : real) : (term70 x) = (term71 x).
Proof. exact (MK_COMB (@lem1495400) (@lem1495399 x)). Qed.
Lemma lem1495402 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1495403 (x : real) : (term72 x) = (term73 x).
Proof. exact (MK_COMB (@lem1495402) (@lem1495401 x)). Qed.
Lemma lem1495404 (x : real) (y : real) : (term64 x y) = (term47 x y).
Proof. exact (eq_refl (term64 x y)). Qed.
Lemma lem1495405 (x : real) : (term74 x) = (term61 x).
Proof. exact (fun_ext (fun y : real => @lem1495404 x y)). Qed.
Lemma lem1495406 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495407 (x : real) : (term75 x) = (term76 x).
Proof. exact (MK_COMB (@lem1495406) (@lem1495405 x)). Qed.
Lemma lem1495408 (x : real) : (term59 x) = (term77 x).
Proof. exact (MK_COMB (@lem1495403 x) (@lem1495407 x)). Qed.
Lemma lem1495409 (x : real) : ((term58 x) = (term59 x)) = ((term51 x) = (term77 x)).
Proof. exact (MK_COMB (@lem1495397 x) (@lem1495408 x)). Qed.
Lemma lem1495410 (x : real) : (term51 x) = (term77 x).
Proof. exact (EQ_MP (@lem1495409 x) (@lem1495387 x)). Qed.
Lemma lem1495507 : term52 = term78.
Proof. exact (fun_ext (fun x : real => @lem1495410 x)). Qed.
Lemma lem1495508 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495509 : term53 = term79.
Proof. exact (MK_COMB (@lem1495508) (@lem1495507)). Qed.
Lemma lem1495511 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1495512 (P : real -> Prop) (Q : real -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem1495511 real P Q). Qed.
Lemma lem1495513 : term80 = term81.
Proof. exact (@lem1495512 term82 term83). Qed.
Lemma lem1495514 (x : real) : (term84 x) = (term71 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1495515 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1495516 (x : real) : (term85 x) = (term73 x).
Proof. exact (MK_COMB (@lem1495515) (@lem1495514 x)). Qed.
Lemma lem1495517 (x : real) : (term86 x) = (term76 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1495518 (x : real) : (term87 x) = (term77 x).
Proof. exact (MK_COMB (@lem1495516 x) (@lem1495517 x)). Qed.
Lemma lem1495519 : term88 = term78.
Proof. exact (fun_ext (fun x : real => @lem1495518 x)). Qed.
Lemma lem1495520 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495521 : term80 = term79.
Proof. exact (MK_COMB (@lem1495520) (@lem1495519)). Qed.
Lemma lem1495522 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1495523 : term89 = term90.
Proof. exact (MK_COMB (@lem1495522) (@lem1495521)). Qed.
Lemma lem1495524 (x : real) : (term84 x) = (term71 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1495525 : term91 = term82.
Proof. exact (fun_ext (fun x : real => @lem1495524 x)). Qed.
Lemma lem1495526 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495527 : term92 = term93.
Proof. exact (MK_COMB (@lem1495526) (@lem1495525)). Qed.
Lemma lem1495528 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1495529 : term94 = term95.
Proof. exact (MK_COMB (@lem1495528) (@lem1495527)). Qed.
Lemma lem1495530 (x : real) : (term86 x) = (term76 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1495531 : term96 = term83.
Proof. exact (fun_ext (fun x : real => @lem1495530 x)). Qed.
Lemma lem1495532 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495533 : term97 = term98.
Proof. exact (MK_COMB (@lem1495532) (@lem1495531)). Qed.
Lemma lem1495534 : term81 = term99.
Proof. exact (MK_COMB (@lem1495529) (@lem1495533)). Qed.
Lemma lem1495535 : (term80 = term81) = (term79 = term99).
Proof. exact (MK_COMB (@lem1495523) (@lem1495534)). Qed.
Lemma lem1495536 : term79 = term99.
Proof. exact (EQ_MP (@lem1495535) (@lem1495513)). Qed.
Lemma lem1495641 : term53 = term99.
Proof. exact (TRANS (@lem1495509) (@lem1495536)). Qed.
Lemma lem1495643 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term54 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1495644 (P : real -> Prop) (Q : real -> Prop) : (term57 P Q) = (term56 P Q).
Proof. exact (@lem1495643 real P Q). Qed.
Lemma lem1495645 : term81 = term80.
Proof. exact (@lem1495644 term82 term83). Qed.
Lemma lem1495646 (x : real) : (term84 x) = (term71 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1495647 : term91 = term82.
Proof. exact (fun_ext (fun x : real => @lem1495646 x)). Qed.
Lemma lem1495648 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495649 : term92 = term93.
Proof. exact (MK_COMB (@lem1495648) (@lem1495647)). Qed.
Lemma lem1495650 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1495651 : term94 = term95.
Proof. exact (MK_COMB (@lem1495650) (@lem1495649)). Qed.
Lemma lem1495652 (x : real) : (term86 x) = (term76 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1495653 : term96 = term83.
Proof. exact (fun_ext (fun x : real => @lem1495652 x)). Qed.
Lemma lem1495654 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495655 : term97 = term98.
Proof. exact (MK_COMB (@lem1495654) (@lem1495653)). Qed.
Lemma lem1495656 : term81 = term99.
Proof. exact (MK_COMB (@lem1495651) (@lem1495655)). Qed.
Lemma lem1495657 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1495658 : term100 = term101.
Proof. exact (MK_COMB (@lem1495657) (@lem1495656)). Qed.
Lemma lem1495659 (x : real) : (term84 x) = (term71 x).
Proof. exact (eq_refl (term84 x)). Qed.
Lemma lem1495660 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1495661 (x : real) : (term85 x) = (term73 x).
Proof. exact (MK_COMB (@lem1495660) (@lem1495659 x)). Qed.
Lemma lem1495662 (x : real) : (term86 x) = (term76 x).
Proof. exact (eq_refl (term86 x)). Qed.
Lemma lem1495663 (x : real) : (term87 x) = (term77 x).
Proof. exact (MK_COMB (@lem1495661 x) (@lem1495662 x)). Qed.
Lemma lem1495664 : term88 = term78.
Proof. exact (fun_ext (fun x : real => @lem1495663 x)). Qed.
Lemma lem1495665 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495666 : term80 = term79.
Proof. exact (MK_COMB (@lem1495665) (@lem1495664)). Qed.
Lemma lem1495667 : (term81 = term80) = (term99 = term79).
Proof. exact (MK_COMB (@lem1495658) (@lem1495666)). Qed.
Lemma lem1495668 : term99 = term79.
Proof. exact (EQ_MP (@lem1495667) (@lem1495645)). Qed.
Lemma lem1495670 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term54 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1495671 (P : real -> Prop) (Q : real -> Prop) : (term57 P Q) = (term56 P Q).
Proof. exact (@lem1495670 real P Q). Qed.
Lemma lem1495672 (x : real) : (term59 x) = (term58 x).
Proof. exact (@lem1495671 (term60 x) (term61 x)). Qed.
Lemma lem1495673 (x : real) (y : real) : (term62 x y) = (term45 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1495674 (x : real) : (term69 x) = (term60 x).
Proof. exact (fun_ext (fun y : real => @lem1495673 x y)). Qed.
Lemma lem1495675 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495676 (x : real) : (term70 x) = (term71 x).
Proof. exact (MK_COMB (@lem1495675) (@lem1495674 x)). Qed.
Lemma lem1495677 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1495678 (x : real) : (term72 x) = (term73 x).
Proof. exact (MK_COMB (@lem1495677) (@lem1495676 x)). Qed.
Lemma lem1495679 (x : real) (y : real) : (term64 x y) = (term47 x y).
Proof. exact (eq_refl (term64 x y)). Qed.
Lemma lem1495680 (x : real) : (term74 x) = (term61 x).
Proof. exact (fun_ext (fun y : real => @lem1495679 x y)). Qed.
Lemma lem1495681 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495682 (x : real) : (term75 x) = (term76 x).
Proof. exact (MK_COMB (@lem1495681) (@lem1495680 x)). Qed.
Lemma lem1495683 (x : real) : (term59 x) = (term77 x).
Proof. exact (MK_COMB (@lem1495678 x) (@lem1495682 x)). Qed.
Lemma lem1495684 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1495685 (x : real) : (term102 x) = (term103 x).
Proof. exact (MK_COMB (@lem1495684) (@lem1495683 x)). Qed.
Lemma lem1495686 (x : real) (y : real) : (term62 x y) = (term45 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1495687 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1495688 (x : real) (y : real) : (term63 x y) = (term48 x y).
Proof. exact (MK_COMB (@lem1495687) (@lem1495686 x y)). Qed.
Lemma lem1495689 (x : real) (y : real) : (term64 x y) = (term47 x y).
Proof. exact (eq_refl (term64 x y)). Qed.
Lemma lem1495690 (x : real) (y : real) : (term65 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem1495688 x y) (@lem1495689 x y)). Qed.
Lemma lem1495691 (x : real) : (term66 x) = (term50 x).
Proof. exact (fun_ext (fun y : real => @lem1495690 x y)). Qed.
Lemma lem1495692 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495693 (x : real) : (term58 x) = (term51 x).
Proof. exact (MK_COMB (@lem1495692) (@lem1495691 x)). Qed.
Lemma lem1495694 (x : real) : ((term59 x) = (term58 x)) = ((term77 x) = (term51 x)).
Proof. exact (MK_COMB (@lem1495685 x) (@lem1495693 x)). Qed.
Lemma lem1495695 (x : real) : (term77 x) = (term51 x).
Proof. exact (EQ_MP (@lem1495694 x) (@lem1495672 x)). Qed.
Lemma lem1495696 : term78 = term52.
Proof. exact (fun_ext (fun x : real => @lem1495695 x)). Qed.
Lemma lem1495697 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495698 : term79 = term53.
Proof. exact (MK_COMB (@lem1495697) (@lem1495696)). Qed.
Lemma lem1495699 : term99 = term53.
Proof. exact (TRANS (@lem1495668) (@lem1495698)). Qed.
Lemma lem1495700 : term53 = term53.
Proof. exact (TRANS (@lem1495641) (@lem1495699)). Qed.
Lemma lem1495703 : term20 = term53.
Proof. exact (TRANS (@lem1495379) (@lem1495700)). Qed.
Lemma lem1495720 (x : real) (y : real) : (term49 x y) = (term49 x y).
Proof. exact (eq_refl (term49 x y)). Qed.
Lemma lem1495721 (x : real) : (term50 x) = (term50 x).
Proof. exact (fun_ext (fun y : real => @lem1495720 x y)). Qed.
Lemma lem1495722 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495723 (x : real) : (term51 x) = (term51 x).
Proof. exact (MK_COMB (@lem1495722) (@lem1495721 x)). Qed.
Lemma lem1495724 : term52 = term52.
Proof. exact (fun_ext (fun x : real => @lem1495723 x)). Qed.
Lemma lem1495725 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1495726 : term53 = term53.
Proof. exact (MK_COMB (@lem1495725) (@lem1495724)). Qed.
Lemma lem1495727 : term20 = term53.
Proof. exact (TRANS (@lem1495703) (@lem1495726)). Qed.
Lemma lem1495737 (x : real) (y : real) (h1 : term49 x y) : term49 x y.
Proof. exact (h1). Qed.
Lemma lem1495738 (x : real) (y : real) (h1 : term45 x y) : term45 x y.
Proof. exact (h1). Qed.
Lemma lem1495739 (x : real) (y : real) (h1 : term45 x y) : term41 x y.
Proof. exact (proj2 (@lem1495738 x y h1)). Qed.
Lemma lem1495740 (x : real) (y : real) (h1 : term45 x y) : term34 x y.
Proof. exact (proj1 (@lem1495738 x y h1)). Qed.
Lemma lem1495742 (n : nat) (m : nat) : (term104 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1495743 : term105 = term106.
Proof. exact (@lem1495742 (NUMERAL 0) term107). Qed.
Lemma lem1495744 : term108 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1495745 (h1 : term108 = (BIT1 0)) : term106 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1495746 : (term108 = (BIT1 0)) = (term106 = True).
Proof. exact (prop_ext (fun h1 : term108 = (BIT1 0) => @lem1495745 h1) (fun h1 : term106 = True => @lem1495744)). Qed.
Lemma lem1495747 : term106 = True.
Proof. exact (EQ_MP (@lem1495746) (@lem1495744)). Qed.
Lemma lem1495748 : term105 = True.
Proof. exact (TRANS (@lem1495743) (@lem1495747)). Qed.
Lemma lem1495749 : True = term105.
Proof. exact (SYM (@lem1495748)). Qed.
Lemma lem1495750 : term105.
Proof. exact (EQ_MP (@lem1495749) (@lem0)). Qed.
Lemma lem1495751 (x : real) (y : real) (h1 : term45 x y) : term109 x y.
Proof. exact (conj (@lem1495750) (@lem1495739 x y h1)). Qed.
Lemma lem1495753 (x : real) (y : real) : term110 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1495754 (x : real) (y : real) : term111 x y.
Proof. exact (@lem1495753 term112 (term37 x y)). Qed.
Lemma lem1495755 (x : real) (y : real) (h1 : term45 x y) : term113 x y.
Proof. exact (@lem1495754 x y (@lem1495751 x y h1)). Qed.
Lemma lem1495756 (x : real) (y : real) : (term114 x y) = (term37 x y).
Proof. exact (@lem1483460 (term37 x y)). Qed.
Lemma lem1495757 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1495758 (x : real) (y : real) : (term115 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1495757) (@lem1495756 x y)). Qed.
Lemma lem1495759 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1495760 (x : real) (y : real) : (term113 x y) = (term41 x y).
Proof. exact (MK_COMB (@lem1495758 x y) (@lem1495759)). Qed.
Lemma lem1495761 (x : real) (y : real) (h1 : term45 x y) : term41 x y.
Proof. exact (EQ_MP (@lem1495760 x y) (@lem1495755 x y h1)). Qed.
Lemma lem1495763 (n : nat) (m : nat) : (term104 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1495764 : term105 = term106.
Proof. exact (@lem1495763 (NUMERAL 0) term107). Qed.
Lemma lem1495765 : term108 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1495766 (h1 : term108 = (BIT1 0)) : term106 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1495767 : (term108 = (BIT1 0)) = (term106 = True).
Proof. exact (prop_ext (fun h1 : term108 = (BIT1 0) => @lem1495766 h1) (fun h1 : term106 = True => @lem1495765)). Qed.
Lemma lem1495768 : term106 = True.
Proof. exact (EQ_MP (@lem1495767) (@lem1495765)). Qed.
Lemma lem1495769 : term105 = True.
Proof. exact (TRANS (@lem1495764) (@lem1495768)). Qed.
Lemma lem1495770 : True = term105.
Proof. exact (SYM (@lem1495769)). Qed.
Lemma lem1495771 : term105.
Proof. exact (EQ_MP (@lem1495770) (@lem0)). Qed.
Lemma lem1495772 (x : real) (y : real) (h1 : term45 x y) : term116 x y.
Proof. exact (conj (@lem1495771) (@lem1495740 x y h1)). Qed.
Lemma lem1495774 (x : real) (y : real) : term117 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1495775 (x : real) (y : real) : term118 x y.
Proof. exact (@lem1495774 term112 (term30 x y)). Qed.
Lemma lem1495776 (x : real) (y : real) (h1 : term45 x y) : term119 x y.
Proof. exact (@lem1495775 x y (@lem1495772 x y h1)). Qed.
Lemma lem1495777 (x : real) (y : real) : (term120 x y) = (term30 x y).
Proof. exact (@lem1483460 (term30 x y)). Qed.
Lemma lem1495778 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1495779 (x : real) (y : real) : (term121 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem1495778) (@lem1495777 x y)). Qed.
Lemma lem1495780 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1495781 (x : real) (y : real) : (term119 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1495779 x y) (@lem1495780)). Qed.
Lemma lem1495782 (x : real) (y : real) (h1 : term45 x y) : term34 x y.
Proof. exact (EQ_MP (@lem1495781 x y) (@lem1495776 x y h1)). Qed.
Lemma lem1495783 (x : real) (y : real) (h1 : term45 x y) : term45 x y.
Proof. exact (conj (@lem1495782 x y h1) (@lem1495761 x y h1)). Qed.
Lemma lem1495785 (x : real) (y : real) : term122 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1495786 (x : real) (y : real) : term123 x y.
Proof. exact (@lem1495785 (term30 x y) (term37 x y)). Qed.
Lemma lem1495787 (x : real) (y : real) (h1 : term45 x y) : term124 x y.
Proof. exact (@lem1495786 x y (@lem1495783 x y h1)). Qed.
Lemma lem1495788 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (@lem1483480 x (term38 x) (term38 y) y). Qed.
Lemma lem1495789 (x : real) : (term127 x) = (term128 x).
Proof. exact (@lem1483442 term129 x). Qed.
Lemma lem1495791 (m : nat) : (term130 m) = term33.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1495792 : term131 = term33.
Proof. exact (@lem1495791 term107). Qed.
Lemma lem1495793 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1495794 : term132 = term133.
Proof. exact (MK_COMB (@lem1495793) (@lem1495792)). Qed.
Lemma lem1495795 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1495796 (x : real) : (term128 x) = (term134 x).
Proof. exact (MK_COMB (@lem1495794) (@lem1495795 x)). Qed.
Lemma lem1495797 (x : real) : (term127 x) = (term134 x).
Proof. exact (TRANS (@lem1495789 x) (@lem1495796 x)). Qed.
Lemma lem1495798 (x : real) : (term134 x) = term33.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1495799 (x : real) : (term127 x) = term33.
Proof. exact (TRANS (@lem1495797 x) (@lem1495798 x)). Qed.
Lemma lem1495800 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1495801 (x : real) : (term135 x) = term136.
Proof. exact (MK_COMB (@lem1495800) (@lem1495799 x)). Qed.
Lemma lem1495802 (y : real) : (term137 y) = (term128 y).
Proof. exact (@lem1483440 term129 y). Qed.
Lemma lem1495804 (m : nat) : (term130 m) = term33.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1495805 : term131 = term33.
Proof. exact (@lem1495804 term107). Qed.
Lemma lem1495806 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1495807 : term132 = term133.
Proof. exact (MK_COMB (@lem1495806) (@lem1495805)). Qed.
Lemma lem1495808 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1495809 (y : real) : (term128 y) = (term134 y).
Proof. exact (MK_COMB (@lem1495807) (@lem1495808 y)). Qed.
Lemma lem1495810 (y : real) : (term137 y) = (term134 y).
Proof. exact (TRANS (@lem1495802 y) (@lem1495809 y)). Qed.
Lemma lem1495811 (y : real) : (term134 y) = term33.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1495812 (y : real) : (term137 y) = term33.
Proof. exact (TRANS (@lem1495810 y) (@lem1495811 y)). Qed.
Lemma lem1495813 (x : real) (y : real) : (term126 x y) = term138.
Proof. exact (MK_COMB (@lem1495801 x) (@lem1495812 y)). Qed.
Lemma lem1495814 (x : real) (y : real) : (term125 x y) = term138.
Proof. exact (TRANS (@lem1495788 x y) (@lem1495813 x y)). Qed.
Lemma lem1495815 : term138 = term33.
Proof. exact (@lem1483448 term33). Qed.
Lemma lem1495816 (x : real) (y : real) : (term125 x y) = term33.
Proof. exact (TRANS (@lem1495814 x y) (@lem1495815)). Qed.
Lemma lem1495817 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1495818 (x : real) (y : real) : (term139 x y) = term140.
Proof. exact (MK_COMB (@lem1495817) (@lem1495816 x y)). Qed.
Lemma lem1495819 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1495820 (x : real) (y : real) : (term124 x y) = term141.
Proof. exact (MK_COMB (@lem1495818 x y) (@lem1495819)). Qed.
Lemma lem1495821 (x : real) (y : real) (h1 : term45 x y) : term141.
Proof. exact (EQ_MP (@lem1495820 x y) (@lem1495787 x y h1)). Qed.
Lemma lem1495823 (n : nat) (m : nat) : (term104 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1495824 : term141 = term142.
Proof. exact (@lem1495823 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1495825 : term142 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1495826 : term141 = False.
Proof. exact (TRANS (@lem1495824) (@lem1495825)). Qed.
Lemma lem1495827 (x : real) (y : real) (h1 : term45 x y) : False.
Proof. exact (EQ_MP (@lem1495826) (@lem1495821 x y h1)). Qed.
Lemma lem1495828 (x : real) (y : real) (h1 : term47 x y) : term47 x y.
Proof. exact (h1). Qed.
Lemma lem1495829 (x : real) (y : real) (h1 : term47 x y) : term34 x y.
Proof. exact (proj2 (@lem1495828 x y h1)). Qed.
Lemma lem1495830 (x : real) (y : real) (h1 : term47 x y) : term41 x y.
Proof. exact (proj1 (@lem1495828 x y h1)). Qed.
Lemma lem1495832 (n : nat) (m : nat) : (term104 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1495833 : term105 = term106.
Proof. exact (@lem1495832 (NUMERAL 0) term107). Qed.
Lemma lem1495834 : term108 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1495835 (h1 : term108 = (BIT1 0)) : term106 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1495836 : (term108 = (BIT1 0)) = (term106 = True).
Proof. exact (prop_ext (fun h1 : term108 = (BIT1 0) => @lem1495835 h1) (fun h1 : term106 = True => @lem1495834)). Qed.
Lemma lem1495837 : term106 = True.
Proof. exact (EQ_MP (@lem1495836) (@lem1495834)). Qed.
Lemma lem1495838 : term105 = True.
Proof. exact (TRANS (@lem1495833) (@lem1495837)). Qed.
Lemma lem1495839 : True = term105.
Proof. exact (SYM (@lem1495838)). Qed.
Lemma lem1495840 : term105.
Proof. exact (EQ_MP (@lem1495839) (@lem0)). Qed.
Lemma lem1495841 (x : real) (y : real) (h1 : term47 x y) : term109 x y.
Proof. exact (conj (@lem1495840) (@lem1495830 x y h1)). Qed.
Lemma lem1495843 (x : real) (y : real) : term110 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1495844 (x : real) (y : real) : term111 x y.
Proof. exact (@lem1495843 term112 (term37 x y)). Qed.
Lemma lem1495845 (x : real) (y : real) (h1 : term47 x y) : term113 x y.
Proof. exact (@lem1495844 x y (@lem1495841 x y h1)). Qed.
Lemma lem1495846 (x : real) (y : real) : (term114 x y) = (term37 x y).
Proof. exact (@lem1483460 (term37 x y)). Qed.
Lemma lem1495847 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1495848 (x : real) (y : real) : (term115 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1495847) (@lem1495846 x y)). Qed.
Lemma lem1495849 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1495850 (x : real) (y : real) : (term113 x y) = (term41 x y).
Proof. exact (MK_COMB (@lem1495848 x y) (@lem1495849)). Qed.
Lemma lem1495851 (x : real) (y : real) (h1 : term47 x y) : term41 x y.
Proof. exact (EQ_MP (@lem1495850 x y) (@lem1495845 x y h1)). Qed.
Lemma lem1495853 (n : nat) (m : nat) : (term104 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1495854 : term105 = term106.
Proof. exact (@lem1495853 (NUMERAL 0) term107). Qed.
Lemma lem1495855 : term108 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1495856 (h1 : term108 = (BIT1 0)) : term106 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1495857 : (term108 = (BIT1 0)) = (term106 = True).
Proof. exact (prop_ext (fun h1 : term108 = (BIT1 0) => @lem1495856 h1) (fun h1 : term106 = True => @lem1495855)). Qed.
Lemma lem1495858 : term106 = True.
Proof. exact (EQ_MP (@lem1495857) (@lem1495855)). Qed.
Lemma lem1495859 : term105 = True.
Proof. exact (TRANS (@lem1495854) (@lem1495858)). Qed.
Lemma lem1495860 : True = term105.
Proof. exact (SYM (@lem1495859)). Qed.
Lemma lem1495861 : term105.
Proof. exact (EQ_MP (@lem1495860) (@lem0)). Qed.
Lemma lem1495862 (x : real) (y : real) (h1 : term47 x y) : term116 x y.
Proof. exact (conj (@lem1495861) (@lem1495829 x y h1)). Qed.
Lemma lem1495864 (x : real) (y : real) : term117 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1495865 (x : real) (y : real) : term118 x y.
Proof. exact (@lem1495864 term112 (term30 x y)). Qed.
Lemma lem1495866 (x : real) (y : real) (h1 : term47 x y) : term119 x y.
Proof. exact (@lem1495865 x y (@lem1495862 x y h1)). Qed.
Lemma lem1495867 (x : real) (y : real) : (term120 x y) = (term30 x y).
Proof. exact (@lem1483460 (term30 x y)). Qed.
Lemma lem1495868 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1495869 (x : real) (y : real) : (term121 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem1495868) (@lem1495867 x y)). Qed.
Lemma lem1495870 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1495871 (x : real) (y : real) : (term119 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1495869 x y) (@lem1495870)). Qed.
Lemma lem1495872 (x : real) (y : real) (h1 : term47 x y) : term34 x y.
Proof. exact (EQ_MP (@lem1495871 x y) (@lem1495866 x y h1)). Qed.
Lemma lem1495873 (x : real) (y : real) (h1 : term47 x y) : term45 x y.
Proof. exact (conj (@lem1495872 x y h1) (@lem1495851 x y h1)). Qed.
Lemma lem1495875 (x : real) (y : real) : term122 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1495876 (x : real) (y : real) : term123 x y.
Proof. exact (@lem1495875 (term30 x y) (term37 x y)). Qed.
Lemma lem1495877 (x : real) (y : real) (h1 : term47 x y) : term124 x y.
Proof. exact (@lem1495876 x y (@lem1495873 x y h1)). Qed.
Lemma lem1495878 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (@lem1483480 x (term38 x) (term38 y) y). Qed.
Lemma lem1495879 (x : real) : (term127 x) = (term128 x).
Proof. exact (@lem1483442 term129 x). Qed.
Lemma lem1495881 (m : nat) : (term130 m) = term33.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1495882 : term131 = term33.
Proof. exact (@lem1495881 term107). Qed.
Lemma lem1495883 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1495884 : term132 = term133.
Proof. exact (MK_COMB (@lem1495883) (@lem1495882)). Qed.
Lemma lem1495885 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1495886 (x : real) : (term128 x) = (term134 x).
Proof. exact (MK_COMB (@lem1495884) (@lem1495885 x)). Qed.
Lemma lem1495887 (x : real) : (term127 x) = (term134 x).
Proof. exact (TRANS (@lem1495879 x) (@lem1495886 x)). Qed.
Lemma lem1495888 (x : real) : (term134 x) = term33.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1495889 (x : real) : (term127 x) = term33.
Proof. exact (TRANS (@lem1495887 x) (@lem1495888 x)). Qed.
Lemma lem1495890 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1495891 (x : real) : (term135 x) = term136.
Proof. exact (MK_COMB (@lem1495890) (@lem1495889 x)). Qed.
Lemma lem1495892 (y : real) : (term137 y) = (term128 y).
Proof. exact (@lem1483440 term129 y). Qed.
Lemma lem1495894 (m : nat) : (term130 m) = term33.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1495895 : term131 = term33.
Proof. exact (@lem1495894 term107). Qed.
Lemma lem1495896 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1495897 : term132 = term133.
Proof. exact (MK_COMB (@lem1495896) (@lem1495895)). Qed.
Lemma lem1495898 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1495899 (y : real) : (term128 y) = (term134 y).
Proof. exact (MK_COMB (@lem1495897) (@lem1495898 y)). Qed.
Lemma lem1495900 (y : real) : (term137 y) = (term134 y).
Proof. exact (TRANS (@lem1495892 y) (@lem1495899 y)). Qed.
Lemma lem1495901 (y : real) : (term134 y) = term33.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1495902 (y : real) : (term137 y) = term33.
Proof. exact (TRANS (@lem1495900 y) (@lem1495901 y)). Qed.
Lemma lem1495903 (x : real) (y : real) : (term126 x y) = term138.
Proof. exact (MK_COMB (@lem1495891 x) (@lem1495902 y)). Qed.
Lemma lem1495904 (x : real) (y : real) : (term125 x y) = term138.
Proof. exact (TRANS (@lem1495878 x y) (@lem1495903 x y)). Qed.
Lemma lem1495905 : term138 = term33.
Proof. exact (@lem1483448 term33). Qed.
Lemma lem1495906 (x : real) (y : real) : (term125 x y) = term33.
Proof. exact (TRANS (@lem1495904 x y) (@lem1495905)). Qed.
Lemma lem1495907 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1495908 (x : real) (y : real) : (term139 x y) = term140.
Proof. exact (MK_COMB (@lem1495907) (@lem1495906 x y)). Qed.
Lemma lem1495909 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1495910 (x : real) (y : real) : (term124 x y) = term141.
Proof. exact (MK_COMB (@lem1495908 x y) (@lem1495909)). Qed.
Lemma lem1495911 (x : real) (y : real) (h1 : term47 x y) : term141.
Proof. exact (EQ_MP (@lem1495910 x y) (@lem1495877 x y h1)). Qed.
Lemma lem1495913 (n : nat) (m : nat) : (term104 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1495914 : term141 = term142.
Proof. exact (@lem1495913 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1495915 : term142 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1495916 : term141 = False.
Proof. exact (TRANS (@lem1495914) (@lem1495915)). Qed.
Lemma lem1495917 (x : real) (y : real) (h1 : term47 x y) : False.
Proof. exact (EQ_MP (@lem1495916) (@lem1495911 x y h1)). Qed.
Lemma lem1495918 (x : real) (y : real) (h1 : term49 x y) : False.
Proof. exact (or_elim (@lem1495737 x y h1) (fun h0 : term45 x y => @lem1495827 x y h0) (fun h0 : term47 x y => @lem1495917 x y h0)). Qed.
Lemma lem1495920 (x : real) (y : real) (h1 : term49 x y) : term49 x y.
Proof. exact (h1). Qed.
Lemma lem1495921 (x : real) (y : real) (h1 : term49 x y) : (term49 x y) = False.
Proof. exact (prop_ext (fun h2 : term49 x y => @lem1495918 x y h1) (fun h2 : False => @lem1495920 x y h1)). Qed.
Lemma lem1495922 (x : real) (y : real) (h1 : term49 x y) : False.
Proof. exact (EQ_MP (@lem1495921 x y h1) (@lem1495920 x y h1)). Qed.
Lemma lem1495923 (x : real) (h1 : term51 x) : term51 x.
Proof. exact (h1). Qed.
Lemma lem1495924 (x : real) (h1 : term51 x) : False.
Proof. exact (ex_elim (@lem1495923 x h1) (fun y : real => fun h0 : term50 x y => @lem1495922 x y h0)). Qed.
Lemma lem1495925 (h1 : term53) : term53.
Proof. exact (h1). Qed.
Lemma lem1495926 (h1 : term53) : False.
Proof. exact (ex_elim (@lem1495925 h1) (fun x : real => fun h0 : term52 x => @lem1495924 x h0)). Qed.
Lemma lem1495927 (h1 : term20) : term20.
Proof. exact (h1). Qed.
Lemma lem1495928 (h1 : term20) : term53.
Proof. exact (EQ_MP (@lem1495727) (@lem1495927 h1)). Qed.
Lemma lem1495929 (h1 : term20) : term53 = False.
Proof. exact (prop_ext (fun h2 : term53 => @lem1495926 h2) (fun h2 : False => @lem1495928 h1)). Qed.
Lemma lem1495930 (h1 : term20) : False.
Proof. exact (EQ_MP (@lem1495929 h1) (@lem1495928 h1)). Qed.
Lemma lem1495931 : term143.
Proof. exact (fun h0 : term20 => @lem1495930 h0). Qed.
Lemma lem1495932 : term144.
Proof. exact (@lem1386578 term145). Qed.
Lemma lem1495933 : term145.
Proof. exact (@lem1495932 (@lem1495931)). Qed.
