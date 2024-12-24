Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LTE_TRANS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339577_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm69_spec.
Lemma lem1369134 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1369135 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1369136 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1369135 t1) (@lem1369134 t1)). Qed.
Lemma lem1369137 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1369136 t1 t2). Qed.
Lemma lem1369138 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1369139 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1369138 t1 t2) (@lem1369137 t1 t2)). Qed.
Lemma lem1369140 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1369139 t1 t2 t3). Qed.
Lemma lem1369141 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1369142 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1369141 t1 t2 t3) (@lem1369140 t1 t2 t3)). Qed.
Lemma lem1369143 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1369142 t1 t2 t3)). Qed.
Lemma lem1369145 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1369146 : term8 = term9.
Proof. exact (@lem1369145 term8). Qed.
Lemma lem1369147 : term9 = term8.
Proof. exact (SYM (@lem1369146)). Qed.
Lemma lem1369148 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1369151 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1369152 : term12.
Proof. exact (fun h0 : term11 => @lem1369151 h0). Qed.
Lemma lem1369153 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1369154 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1369155 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1369153 h2 (@lem1369154 h1)). Qed.
Lemma lem1369156 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1369155 h1 h0). Qed.
Lemma lem1369157 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1369158 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1369156 h1 (@lem1369157 h2)). Qed.
Lemma lem1369159 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1369158 h0 h1). Qed.
Lemma lem1369160 : term14.
Proof. exact (fun h0 : term12 => @lem1369159 h0). Qed.
Lemma lem1369163 : term12.
Proof. exact (@lem1369160 (@lem1369152)). Qed.
Lemma lem1369201 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1369202 : term15 = term16.
Proof. exact (@lem1369201 term17). Qed.
Lemma lem1369211 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1369212 : term19 = term20.
Proof. exact (MK_COMB (@lem1369211) (@lem1369202)). Qed.
Lemma lem1369215 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1369222 : term11 = term22.
Proof. exact (MK_COMB (@lem1369215) (@lem1369212)). Qed.
Lemma lem1369229 (y : real) (x : real) : ((real_lt x y) = (term23 y x)) = ((real_lt x y) = (term23 y x)).
Proof. exact (eq_refl ((real_lt x y) = (term23 y x))). Qed.
Lemma lem1369230 (y : real) : (term24 y) = (term24 y).
Proof. exact (fun_ext (fun x : real => @lem1369229 y x)). Qed.
Lemma lem1369231 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369232 (y : real) : (term25 y) = (term25 y).
Proof. exact (MK_COMB (@lem1369231) (@lem1369230 y)). Qed.
Lemma lem1369233 : term26 = term26.
Proof. exact (fun_ext (fun y : real => @lem1369232 y)). Qed.
Lemma lem1369234 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369235 : term17 = term17.
Proof. exact (MK_COMB (@lem1369234) (@lem1369233)). Qed.
Lemma lem1369236 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1369237 : term16 = term16.
Proof. exact (MK_COMB (@lem1369236) (@lem1369235)). Qed.
Lemma lem1369246 (y : real) (x : real) (z : real) : (term27 y x z) = (term27 y x z).
Proof. exact (eq_refl (term27 y x z)). Qed.
Lemma lem1369247 (y : real) (x : real) : (term28 y x) = (term28 y x).
Proof. exact (fun_ext (fun z : real => @lem1369246 y x z)). Qed.
Lemma lem1369248 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369249 (y : real) (x : real) : (term29 y x) = (term29 y x).
Proof. exact (MK_COMB (@lem1369248) (@lem1369247 y x)). Qed.
Lemma lem1369250 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1369249 y x)). Qed.
Lemma lem1369251 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369252 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1369251) (@lem1369250 x)). Qed.
Lemma lem1369253 : term32 = term32.
Proof. exact (fun_ext (fun x : real => @lem1369252 x)). Qed.
Lemma lem1369254 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369255 : term33 = term33.
Proof. exact (MK_COMB (@lem1369254) (@lem1369253)). Qed.
Lemma lem1369256 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1369257 : term18 = term18.
Proof. exact (MK_COMB (@lem1369256) (@lem1369255)). Qed.
Lemma lem1369258 : term20 = term20.
Proof. exact (MK_COMB (@lem1369257) (@lem1369237)). Qed.
Lemma lem1369267 (y : real) (x : real) (z : real) : (term34 y x z) = (term34 y x z).
Proof. exact (eq_refl (term34 y x z)). Qed.
Lemma lem1369268 (y : real) (x : real) : (term35 y x) = (term35 y x).
Proof. exact (fun_ext (fun z : real => @lem1369267 y x z)). Qed.
Lemma lem1369269 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369270 (y : real) (x : real) : (term36 y x) = (term36 y x).
Proof. exact (MK_COMB (@lem1369269) (@lem1369268 y x)). Qed.
Lemma lem1369271 (x : real) : (term37 x) = (term37 x).
Proof. exact (fun_ext (fun y : real => @lem1369270 y x)). Qed.
Lemma lem1369272 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369273 (x : real) : (term38 x) = (term38 x).
Proof. exact (MK_COMB (@lem1369272) (@lem1369271 x)). Qed.
Lemma lem1369274 : term39 = term39.
Proof. exact (fun_ext (fun x : real => @lem1369273 x)). Qed.
Lemma lem1369275 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369276 : term8 = term8.
Proof. exact (MK_COMB (@lem1369275) (@lem1369274)). Qed.
Lemma lem1369277 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1369278 : term10 = term10.
Proof. exact (MK_COMB (@lem1369277) (@lem1369276)). Qed.
Lemma lem1369279 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1369280 : term21 = term21.
Proof. exact (MK_COMB (@lem1369279) (@lem1369278)). Qed.
Lemma lem1369281 : term22 = term22.
Proof. exact (MK_COMB (@lem1369280) (@lem1369258)). Qed.
Lemma lem1369344 : term11 = term22.
Proof. exact (TRANS (@lem1369222) (@lem1369281)). Qed.
Lemma lem1369345 : term22 = term11.
Proof. exact (SYM (@lem1369344)). Qed.
Lemma lem1369346 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1369347 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1369348 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1369359 (y : real) (x : real) (z : real) : (term40 y x z) = (term41 y x z).
Proof. exact (@lem17362 (term42 x y z) (real_lt x z)). Qed.
Lemma lem1369360 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1369361 (y : real) (x : real) : (term45 y x) = (term46 y x).
Proof. exact (@lem1369360 (term35 y x)). Qed.
Lemma lem1369362 (y : real) (x : real) (z : real) : (term47 y x z) = (term34 y x z).
Proof. exact (eq_refl (term47 y x z)). Qed.
Lemma lem1369363 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1369364 (y : real) (x : real) (z : real) : (term48 y x z) = (term40 y x z).
Proof. exact (MK_COMB (@lem1369363) (@lem1369362 y x z)). Qed.
Lemma lem1369365 (y : real) (x : real) (z : real) : (term48 y x z) = (term41 y x z).
Proof. exact (TRANS (@lem1369364 y x z) (@lem1369359 y x z)). Qed.
Lemma lem1369366 (y : real) (x : real) : (term49 y x) = (term50 y x).
Proof. exact (fun_ext (fun z : real => @lem1369365 y x z)). Qed.
Lemma lem1369367 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1369368 (y : real) (x : real) : (term46 y x) = (term51 y x).
Proof. exact (MK_COMB (@lem1369367) (@lem1369366 y x)). Qed.
Lemma lem1369369 (y : real) (x : real) : (term45 y x) = (term51 y x).
Proof. exact (TRANS (@lem1369361 y x) (@lem1369368 y x)). Qed.
Lemma lem1369370 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1369371 (x : real) : (term52 x) = (term53 x).
Proof. exact (@lem1369370 (term37 x)). Qed.
Lemma lem1369372 (y : real) (x : real) : (term54 x y) = (term36 y x).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1369373 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1369374 (y : real) (x : real) : (term55 x y) = (term45 y x).
Proof. exact (MK_COMB (@lem1369373) (@lem1369372 y x)). Qed.
Lemma lem1369375 (y : real) (x : real) : (term55 x y) = (term51 y x).
Proof. exact (TRANS (@lem1369374 y x) (@lem1369369 y x)). Qed.
Lemma lem1369376 (x : real) : (term56 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1369375 y x)). Qed.
Lemma lem1369377 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1369378 (x : real) : (term53 x) = (term58 x).
Proof. exact (MK_COMB (@lem1369377) (@lem1369376 x)). Qed.
Lemma lem1369379 (x : real) : (term52 x) = (term58 x).
Proof. exact (TRANS (@lem1369371 x) (@lem1369378 x)). Qed.
Lemma lem1369380 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1369381 : term10 = term59.
Proof. exact (@lem1369380 term39). Qed.
Lemma lem1369382 (x : real) : (term60 x) = (term38 x).
Proof. exact (eq_refl (term60 x)). Qed.
Lemma lem1369383 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1369384 (x : real) : (term61 x) = (term52 x).
Proof. exact (MK_COMB (@lem1369383) (@lem1369382 x)). Qed.
Lemma lem1369385 (x : real) : (term61 x) = (term58 x).
Proof. exact (TRANS (@lem1369384 x) (@lem1369379 x)). Qed.
Lemma lem1369386 : term62 = term63.
Proof. exact (fun_ext (fun x : real => @lem1369385 x)). Qed.
Lemma lem1369387 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1369388 : term59 = term64.
Proof. exact (MK_COMB (@lem1369387) (@lem1369386)). Qed.
Lemma lem1369449 : term10 = term64.
Proof. exact (TRANS (@lem1369381) (@lem1369388)). Qed.
Lemma lem1369450 (h1 : term10) : term64.
Proof. exact (EQ_MP (@lem1369449) (@lem1369346 h1)). Qed.
Lemma lem1369457 (x : real) (y : real) (z : real) : (term65 x y z) = (term66 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem1369458 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem1369459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1369460 (x : real) (y : real) (z : real) : (term67 x y z) = (term68 x y z).
Proof. exact (MK_COMB (@lem1369459) (@lem1369457 x y z)). Qed.
Lemma lem1369461 (y : real) (x : real) (z : real) : (term69 y x z) = (term70 y x z).
Proof. exact (MK_COMB (@lem1369460 x y z) (@lem1369458 x z)). Qed.
Lemma lem1369462 (y : real) (x : real) (z : real) : (term27 y x z) = (term69 y x z).
Proof. exact (@lem17265 (term71 x y z) (real_le x z)). Qed.
Lemma lem1369463 (y : real) (x : real) (z : real) : (term27 y x z) = (term70 y x z).
Proof. exact (TRANS (@lem1369462 y x z) (@lem1369461 y x z)). Qed.
Lemma lem1369464 (y : real) (x : real) : (term28 y x) = (term72 y x).
Proof. exact (fun_ext (fun z : real => @lem1369463 y x z)). Qed.
Lemma lem1369465 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369466 (y : real) (x : real) : (term29 y x) = (term73 y x).
Proof. exact (MK_COMB (@lem1369465) (@lem1369464 y x)). Qed.
Lemma lem1369467 (x : real) : (term30 x) = (term74 x).
Proof. exact (fun_ext (fun y : real => @lem1369466 y x)). Qed.
Lemma lem1369468 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369469 (x : real) : (term31 x) = (term75 x).
Proof. exact (MK_COMB (@lem1369468) (@lem1369467 x)). Qed.
Lemma lem1369470 : term32 = term76.
Proof. exact (fun_ext (fun x : real => @lem1369469 x)). Qed.
Lemma lem1369471 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369532 : term33 = term77.
Proof. exact (MK_COMB (@lem1369471) (@lem1369470)). Qed.
Lemma lem1369533 (h1 : term33) : term77.
Proof. exact (EQ_MP (@lem1369532) (@lem1369347 h1)). Qed.
Lemma lem1369539 (y : real) (x : real) : (term78 y x) = (real_le y x).
Proof. exact (@lem16933 (real_le y x)). Qed.
Lemma lem1369542 (y : real) (x : real) : (term79 y x) = (term79 y x).
Proof. exact (eq_refl (term79 y x)). Qed.
Lemma lem1369544 (x : real) (y : real) : (term80 x y) = (term80 x y).
Proof. exact (eq_refl (term80 x y)). Qed.
Lemma lem1369545 (y : real) (x : real) : (term81 y x) = (term82 y x).
Proof. exact (MK_COMB (@lem1369544 x y) (@lem1369539 y x)). Qed.
Lemma lem1369546 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1369547 (y : real) (x : real) : (term83 y x) = (term84 y x).
Proof. exact (MK_COMB (@lem1369546) (@lem1369545 y x)). Qed.
Lemma lem1369548 (y : real) (x : real) : (term85 y x) = (term86 y x).
Proof. exact (MK_COMB (@lem1369547 y x) (@lem1369542 y x)). Qed.
Lemma lem1369549 (y : real) (x : real) : ((real_lt x y) = (term23 y x)) = (term85 y x).
Proof. exact (@lem17784 (real_lt x y) (term23 y x)). Qed.
Lemma lem1369550 (y : real) (x : real) : ((real_lt x y) = (term23 y x)) = (term86 y x).
Proof. exact (TRANS (@lem1369549 y x) (@lem1369548 y x)). Qed.
Lemma lem1369551 (y : real) : (term24 y) = (term87 y).
Proof. exact (fun_ext (fun x : real => @lem1369550 y x)). Qed.
Lemma lem1369552 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369553 (y : real) : (term25 y) = (term88 y).
Proof. exact (MK_COMB (@lem1369552) (@lem1369551 y)). Qed.
Lemma lem1369554 : term26 = term89.
Proof. exact (fun_ext (fun y : real => @lem1369553 y)). Qed.
Lemma lem1369555 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369556 : term17 = term90.
Proof. exact (MK_COMB (@lem1369555) (@lem1369554)). Qed.
Lemma lem1369562 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term91 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1369563 (P : real -> Prop) (Q : real -> Prop) : (term93 P Q) = (term94 P Q).
Proof. exact (@lem1369562 real P Q). Qed.
Lemma lem1369564 (y : real) : (term95 y) = (term96 y).
Proof. exact (@lem1369563 (term97 y) (term98 y)). Qed.
Lemma lem1369565 (y : real) (x : real) : (term99 y x) = (term82 y x).
Proof. exact (eq_refl (term99 y x)). Qed.
Lemma lem1369566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1369567 (y : real) (x : real) : (term100 y x) = (term84 y x).
Proof. exact (MK_COMB (@lem1369566) (@lem1369565 y x)). Qed.
Lemma lem1369568 (y : real) (x : real) : (term101 y x) = (term79 y x).
Proof. exact (eq_refl (term101 y x)). Qed.
Lemma lem1369569 (y : real) (x : real) : (term102 y x) = (term86 y x).
Proof. exact (MK_COMB (@lem1369567 y x) (@lem1369568 y x)). Qed.
Lemma lem1369570 (y : real) : (term103 y) = (term87 y).
Proof. exact (fun_ext (fun x : real => @lem1369569 y x)). Qed.
Lemma lem1369571 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369572 (y : real) : (term95 y) = (term88 y).
Proof. exact (MK_COMB (@lem1369571) (@lem1369570 y)). Qed.
Lemma lem1369573 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1369574 (y : real) : (term104 y) = (term105 y).
Proof. exact (MK_COMB (@lem1369573) (@lem1369572 y)). Qed.
Lemma lem1369575 (y : real) (x : real) : (term99 y x) = (term82 y x).
Proof. exact (eq_refl (term99 y x)). Qed.
Lemma lem1369576 (y : real) : (term106 y) = (term97 y).
Proof. exact (fun_ext (fun x : real => @lem1369575 y x)). Qed.
Lemma lem1369577 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369578 (y : real) : (term107 y) = (term108 y).
Proof. exact (MK_COMB (@lem1369577) (@lem1369576 y)). Qed.
Lemma lem1369579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1369580 (y : real) : (term109 y) = (term110 y).
Proof. exact (MK_COMB (@lem1369579) (@lem1369578 y)). Qed.
Lemma lem1369581 (y : real) (x : real) : (term101 y x) = (term79 y x).
Proof. exact (eq_refl (term101 y x)). Qed.
Lemma lem1369582 (y : real) : (term111 y) = (term98 y).
Proof. exact (fun_ext (fun x : real => @lem1369581 y x)). Qed.
Lemma lem1369583 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369584 (y : real) : (term112 y) = (term113 y).
Proof. exact (MK_COMB (@lem1369583) (@lem1369582 y)). Qed.
Lemma lem1369585 (y : real) : (term96 y) = (term114 y).
Proof. exact (MK_COMB (@lem1369580 y) (@lem1369584 y)). Qed.
Lemma lem1369586 (y : real) : ((term95 y) = (term96 y)) = ((term88 y) = (term114 y)).
Proof. exact (MK_COMB (@lem1369574 y) (@lem1369585 y)). Qed.
Lemma lem1369587 (y : real) : (term88 y) = (term114 y).
Proof. exact (EQ_MP (@lem1369586 y) (@lem1369564 y)). Qed.
Lemma lem1369684 : term89 = term115.
Proof. exact (fun_ext (fun y : real => @lem1369587 y)). Qed.
Lemma lem1369685 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369686 : term90 = term116.
Proof. exact (MK_COMB (@lem1369685) (@lem1369684)). Qed.
Lemma lem1369688 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term91 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1369689 (P : real -> Prop) (Q : real -> Prop) : (term93 P Q) = (term94 P Q).
Proof. exact (@lem1369688 real P Q). Qed.
Lemma lem1369690 : term117 = term118.
Proof. exact (@lem1369689 term119 term120). Qed.
Lemma lem1369691 (y : real) : (term121 y) = (term108 y).
Proof. exact (eq_refl (term121 y)). Qed.
Lemma lem1369692 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1369693 (y : real) : (term122 y) = (term110 y).
Proof. exact (MK_COMB (@lem1369692) (@lem1369691 y)). Qed.
Lemma lem1369694 (y : real) : (term123 y) = (term113 y).
Proof. exact (eq_refl (term123 y)). Qed.
Lemma lem1369695 (y : real) : (term124 y) = (term114 y).
Proof. exact (MK_COMB (@lem1369693 y) (@lem1369694 y)). Qed.
Lemma lem1369696 : term125 = term115.
Proof. exact (fun_ext (fun y : real => @lem1369695 y)). Qed.
Lemma lem1369697 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369698 : term117 = term116.
Proof. exact (MK_COMB (@lem1369697) (@lem1369696)). Qed.
Lemma lem1369699 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1369700 : term126 = term127.
Proof. exact (MK_COMB (@lem1369699) (@lem1369698)). Qed.
Lemma lem1369701 (y : real) : (term121 y) = (term108 y).
Proof. exact (eq_refl (term121 y)). Qed.
Lemma lem1369702 : term128 = term119.
Proof. exact (fun_ext (fun y : real => @lem1369701 y)). Qed.
Lemma lem1369703 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369704 : term129 = term130.
Proof. exact (MK_COMB (@lem1369703) (@lem1369702)). Qed.
Lemma lem1369705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1369706 : term131 = term132.
Proof. exact (MK_COMB (@lem1369705) (@lem1369704)). Qed.
Lemma lem1369707 (y : real) : (term123 y) = (term113 y).
Proof. exact (eq_refl (term123 y)). Qed.
Lemma lem1369708 : term133 = term120.
Proof. exact (fun_ext (fun y : real => @lem1369707 y)). Qed.
Lemma lem1369709 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369710 : term134 = term135.
Proof. exact (MK_COMB (@lem1369709) (@lem1369708)). Qed.
Lemma lem1369711 : term118 = term136.
Proof. exact (MK_COMB (@lem1369706) (@lem1369710)). Qed.
Lemma lem1369712 : (term117 = term118) = (term116 = term136).
Proof. exact (MK_COMB (@lem1369700) (@lem1369711)). Qed.
Lemma lem1369713 : term116 = term136.
Proof. exact (EQ_MP (@lem1369712) (@lem1369690)). Qed.
Lemma lem1369820 : term90 = term136.
Proof. exact (TRANS (@lem1369686) (@lem1369713)). Qed.
Lemma lem1369821 : term17 = term136.
Proof. exact (TRANS (@lem1369556) (@lem1369820)). Qed.
Lemma lem1369822 (h1 : term17) : term136.
Proof. exact (EQ_MP (@lem1369821) (@lem1369348 h1)). Qed.
Lemma lem1369823 (x : real) (h1 : term58 x) : term58 x.
Proof. exact (h1). Qed.
Lemma lem1369824 (y : real) (x : real) (h1 : term51 y x) : term51 y x.
Proof. exact (h1). Qed.
Lemma lem1369850 (y : real) (x : real) (z : real) : (term70 y x z) = (term70 y x z).
Proof. exact (eq_refl (term70 y x z)). Qed.
Lemma lem1369851 (y : real) (x : real) : (term72 y x) = (term72 y x).
Proof. exact (fun_ext (fun z : real => @lem1369850 y x z)). Qed.
Lemma lem1369852 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369853 (y : real) (x : real) : (term73 y x) = (term73 y x).
Proof. exact (MK_COMB (@lem1369852) (@lem1369851 y x)). Qed.
Lemma lem1369854 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : real => @lem1369853 y x)). Qed.
Lemma lem1369855 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369856 (x : real) : (term75 x) = (term75 x).
Proof. exact (MK_COMB (@lem1369855) (@lem1369854 x)). Qed.
Lemma lem1369857 : term76 = term76.
Proof. exact (fun_ext (fun x : real => @lem1369856 x)). Qed.
Lemma lem1369858 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369859 : term77 = term77.
Proof. exact (MK_COMB (@lem1369858) (@lem1369857)). Qed.
Lemma lem1369860 (h1 : term33) : term77.
Proof. exact (EQ_MP (@lem1369859) (@lem1369533 h1)). Qed.
Lemma lem1369877 (y : real) (x : real) : (term79 y x) = (term79 y x).
Proof. exact (eq_refl (term79 y x)). Qed.
Lemma lem1369878 (y : real) : (term98 y) = (term98 y).
Proof. exact (fun_ext (fun x : real => @lem1369877 y x)). Qed.
Lemma lem1369879 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369880 (y : real) : (term113 y) = (term113 y).
Proof. exact (MK_COMB (@lem1369879) (@lem1369878 y)). Qed.
Lemma lem1369881 : term120 = term120.
Proof. exact (fun_ext (fun y : real => @lem1369880 y)). Qed.
Lemma lem1369882 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369883 : term135 = term135.
Proof. exact (MK_COMB (@lem1369882) (@lem1369881)). Qed.
Lemma lem1369896 (y : real) (x : real) : (term82 y x) = (term82 y x).
Proof. exact (eq_refl (term82 y x)). Qed.
Lemma lem1369897 (y : real) : (term97 y) = (term97 y).
Proof. exact (fun_ext (fun x : real => @lem1369896 y x)). Qed.
Lemma lem1369898 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369899 (y : real) : (term108 y) = (term108 y).
Proof. exact (MK_COMB (@lem1369898) (@lem1369897 y)). Qed.
Lemma lem1369900 : term119 = term119.
Proof. exact (fun_ext (fun y : real => @lem1369899 y)). Qed.
Lemma lem1369901 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369902 : term130 = term130.
Proof. exact (MK_COMB (@lem1369901) (@lem1369900)). Qed.
Lemma lem1369903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1369904 : term132 = term132.
Proof. exact (MK_COMB (@lem1369903) (@lem1369902)). Qed.
Lemma lem1369905 : term136 = term136.
Proof. exact (MK_COMB (@lem1369904) (@lem1369883)). Qed.
Lemma lem1369906 (h1 : term17) : term136.
Proof. exact (EQ_MP (@lem1369905) (@lem1369822 h1)). Qed.
Lemma lem1369930 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term41 y x z.
Proof. exact (h1). Qed.
Lemma lem1369932 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term42 x y z.
Proof. exact (proj1 (@lem1369930 y x z h1)). Qed.
Lemma lem1369935 (h1 : term17) : term135.
Proof. exact (proj2 (@lem1369906 h1)). Qed.
Lemma lem1369936 (h1 : term17) : term130.
Proof. exact (proj1 (@lem1369906 h1)). Qed.
Lemma lem1369950 (y : real) (x : real) (z : real) : (term70 y x z) = (term70 y x z).
Proof. exact (eq_refl (term70 y x z)). Qed.
Lemma lem1369951 (y : real) (x : real) : (term72 y x) = (term72 y x).
Proof. exact (fun_ext (fun z : real => @lem1369950 y x z)). Qed.
Lemma lem1369952 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369953 (y : real) (x : real) : (term73 y x) = (term73 y x).
Proof. exact (MK_COMB (@lem1369952) (@lem1369951 y x)). Qed.
Lemma lem1369954 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : real => @lem1369953 y x)). Qed.
Lemma lem1369955 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369956 (x : real) : (term75 x) = (term75 x).
Proof. exact (MK_COMB (@lem1369955) (@lem1369954 x)). Qed.
Lemma lem1369957 : term76 = term76.
Proof. exact (fun_ext (fun x : real => @lem1369956 x)). Qed.
Lemma lem1369958 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369960 : term77 = term77.
Proof. exact (MK_COMB (@lem1369958) (@lem1369957)). Qed.
Lemma lem1369961 (h1 : term33) : term77.
Proof. exact (EQ_MP (@lem1369960) (@lem1369860 h1)). Qed.
Lemma lem1369981 (y : real) (x : real) : (term82 y x) = (term82 y x).
Proof. exact (eq_refl (term82 y x)). Qed.
Lemma lem1369982 (y : real) : (term97 y) = (term97 y).
Proof. exact (fun_ext (fun x : real => @lem1369981 y x)). Qed.
Lemma lem1369983 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369984 (y : real) : (term108 y) = (term108 y).
Proof. exact (MK_COMB (@lem1369983) (@lem1369982 y)). Qed.
Lemma lem1369985 : term119 = term119.
Proof. exact (fun_ext (fun y : real => @lem1369984 y)). Qed.
Lemma lem1369986 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1369988 : term130 = term130.
Proof. exact (MK_COMB (@lem1369986) (@lem1369985)). Qed.
Lemma lem1369989 (h1 : term17) : term130.
Proof. exact (EQ_MP (@lem1369988) (@lem1369936 h1)). Qed.
Lemma lem1369997 (y : real) (x : real) : (term79 y x) = (term79 y x).
Proof. exact (eq_refl (term79 y x)). Qed.
Lemma lem1369998 (y : real) : (term98 y) = (term98 y).
Proof. exact (fun_ext (fun x : real => @lem1369997 y x)). Qed.
Lemma lem1369999 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370000 (y : real) : (term113 y) = (term113 y).
Proof. exact (MK_COMB (@lem1369999) (@lem1369998 y)). Qed.
Lemma lem1370001 : term120 = term120.
Proof. exact (fun_ext (fun y : real => @lem1370000 y)). Qed.
Lemma lem1370002 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370004 : term135 = term135.
Proof. exact (MK_COMB (@lem1370002) (@lem1370001)). Qed.
Lemma lem1370005 (h1 : term17) : term135.
Proof. exact (EQ_MP (@lem1370004) (@lem1369935 h1)). Qed.
Lemma lem1370006 (_24294 : real) (h1 : term33) : term137 _24294.
Proof. exact (@lem1369961 h1 _24294). Qed.
Lemma lem1370007 (_24294 : real) : (term137 _24294) = (term75 _24294).
Proof. exact (eq_refl (term137 _24294)). Qed.
Lemma lem1370008 (_24294 : real) (h1 : term33) : term75 _24294.
Proof. exact (EQ_MP (@lem1370007 _24294) (@lem1370006 _24294 h1)). Qed.
Lemma lem1370009 (_24294 : real) (_24295 : real) (h1 : term33) : term138 _24294 _24295.
Proof. exact (@lem1370008 _24294 h1 _24295). Qed.
Lemma lem1370010 (_24295 : real) (_24294 : real) : (term138 _24294 _24295) = (term73 _24295 _24294).
Proof. exact (eq_refl (term138 _24294 _24295)). Qed.
Lemma lem1370011 (_24295 : real) (_24294 : real) (h1 : term33) : term73 _24295 _24294.
Proof. exact (EQ_MP (@lem1370010 _24295 _24294) (@lem1370009 _24294 _24295 h1)). Qed.
Lemma lem1370012 (_24295 : real) (_24294 : real) (_24296 : real) (h1 : term33) : term139 _24295 _24294 _24296.
Proof. exact (@lem1370011 _24295 _24294 h1 _24296). Qed.
Lemma lem1370013 (_24295 : real) (_24294 : real) (_24296 : real) : (term139 _24295 _24294 _24296) = (term70 _24295 _24294 _24296).
Proof. exact (eq_refl (term139 _24295 _24294 _24296)). Qed.
Lemma lem1370014 (_24295 : real) (_24294 : real) (_24296 : real) (h1 : term33) : term70 _24295 _24294 _24296.
Proof. exact (EQ_MP (@lem1370013 _24295 _24294 _24296) (@lem1370012 _24295 _24294 _24296 h1)). Qed.
Lemma lem1370015 (_24297 : real) (h1 : term17) : term121 _24297.
Proof. exact (@lem1369989 h1 _24297). Qed.
Lemma lem1370016 (_24297 : real) : (term121 _24297) = (term108 _24297).
Proof. exact (eq_refl (term121 _24297)). Qed.
Lemma lem1370017 (_24297 : real) (h1 : term17) : term108 _24297.
Proof. exact (EQ_MP (@lem1370016 _24297) (@lem1370015 _24297 h1)). Qed.
Lemma lem1370018 (_24297 : real) (_24298 : real) (h1 : term17) : term99 _24297 _24298.
Proof. exact (@lem1370017 _24297 h1 _24298). Qed.
Lemma lem1370019 (_24297 : real) (_24298 : real) : (term99 _24297 _24298) = (term82 _24297 _24298).
Proof. exact (eq_refl (term99 _24297 _24298)). Qed.
Lemma lem1370021 (_24299 : real) (h1 : term17) : term123 _24299.
Proof. exact (@lem1370005 h1 _24299). Qed.
Lemma lem1370022 (_24299 : real) : (term123 _24299) = (term113 _24299).
Proof. exact (eq_refl (term123 _24299)). Qed.
Lemma lem1370023 (_24299 : real) (h1 : term17) : term113 _24299.
Proof. exact (EQ_MP (@lem1370022 _24299) (@lem1370021 _24299 h1)). Qed.
Lemma lem1370024 (_24299 : real) (_24300 : real) (h1 : term17) : term101 _24299 _24300.
Proof. exact (@lem1370023 _24299 h1 _24300). Qed.
Lemma lem1370025 (_24299 : real) (_24300 : real) : (term101 _24299 _24300) = (term79 _24299 _24300).
Proof. exact (eq_refl (term101 _24299 _24300)). Qed.
Lemma lem1370037 (_24295 : real) (_24294 : real) (_24296 : real) : (term70 _24295 _24294 _24296) = (term140 _24295 _24294 _24296).
Proof. exact (@lem1369143 (term23 _24294 _24295) (term23 _24295 _24296) (real_le _24294 _24296)). Qed.
Lemma lem1370038 (_24295 : real) (_24294 : real) (_24296 : real) (h1 : term33) : term140 _24295 _24294 _24296.
Proof. exact (EQ_MP (@lem1370037 _24295 _24294 _24296) (@lem1370014 _24295 _24294 _24296 h1)). Qed.
Lemma lem1370040 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term141 x z.
Proof. exact (proj2 (@lem1369930 y x z h1)). Qed.
Lemma lem1370050 (_24297 : real) (_24298 : real) (h1 : term17) : term82 _24297 _24298.
Proof. exact (EQ_MP (@lem1370019 _24297 _24298) (@lem1370018 _24297 _24298 h1)). Qed.
Lemma lem1370056 (_24299 : real) (_24300 : real) (h1 : term17) : term79 _24299 _24300.
Proof. exact (EQ_MP (@lem1370025 _24299 _24300) (@lem1370024 _24299 _24300 h1)). Qed.
Lemma lem1370058 (y : real) (x : real) (z : real) (h1 : term41 y x z) : real_le y z.
Proof. exact (proj2 (@lem1369932 y x z h1)). Qed.
Lemma lem1370059 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term142 y z.
Proof. exact (fun h0 : term23 y z => @lem1370058 y x z h1). Qed.
Lemma lem1370061 (p : Prop) : (term143 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1370062 (y : real) (z : real) : (term142 y z) = (real_le y z).
Proof. exact (@lem1370061 (real_le y z)). Qed.
Lemma lem1370063 (y : real) (x : real) (z : real) (h1 : term41 y x z) : real_le y z.
Proof. exact (EQ_MP (@lem1370062 y z) (@lem1370059 y x z h1)). Qed.
Lemma lem1370065 (y : real) (x : real) (z : real) (h1 : term41 y x z) : real_lt x y.
Proof. exact (proj1 (@lem1369932 y x z h1)). Qed.
Lemma lem1370066 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term144 x y.
Proof. exact (fun h0 : term141 x y => @lem1370065 y x z h1). Qed.
Lemma lem1370068 (p : Prop) : (term143 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1370069 (x : real) (y : real) : (term144 x y) = (real_lt x y).
Proof. exact (@lem1370068 (real_lt x y)). Qed.
Lemma lem1370070 (y : real) (x : real) (z : real) (h1 : term41 y x z) : real_lt x y.
Proof. exact (EQ_MP (@lem1370069 x y) (@lem1370066 y x z h1)). Qed.
Lemma lem1370076 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1370077 (_24300 : real) (_24299 : real) : (term79 _24299 _24300) = (term145 _24300 _24299).
Proof. exact (@lem1370076 (term23 _24299 _24300) (term141 _24300 _24299)). Qed.
Lemma lem1370083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1370084 (_24300 : real) (_24299 : real) : (term146 _24299 _24300) = (term147 _24300 _24299).
Proof. exact (MK_COMB (@lem1370083) (@lem1370077 _24300 _24299)). Qed.
Lemma lem1370090 (_24300 : real) (_24299 : real) : (term145 _24300 _24299) = (term145 _24300 _24299).
Proof. exact (eq_refl (term145 _24300 _24299)). Qed.
Lemma lem1370091 (_24300 : real) (_24299 : real) : ((term79 _24299 _24300) = (term145 _24300 _24299)) = ((term145 _24300 _24299) = (term145 _24300 _24299)).
Proof. exact (MK_COMB (@lem1370084 _24300 _24299) (@lem1370090 _24300 _24299)). Qed.
Lemma lem1370093 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1370094 (x : Prop) : (x = x) = True.
Proof. exact (@lem1370093 Prop x). Qed.
Lemma lem1370095 (_24300 : real) (_24299 : real) : ((term145 _24300 _24299) = (term145 _24300 _24299)) = True.
Proof. exact (@lem1370094 (term145 _24300 _24299)). Qed.
Lemma lem1370096 (_24300 : real) (_24299 : real) : ((term79 _24299 _24300) = (term145 _24300 _24299)) = True.
Proof. exact (TRANS (@lem1370091 _24300 _24299) (@lem1370095 _24300 _24299)). Qed.
Lemma lem1370097 (_24300 : real) (_24299 : real) : True = ((term79 _24299 _24300) = (term145 _24300 _24299)).
Proof. exact (SYM (@lem1370096 _24300 _24299)). Qed.
Lemma lem1370098 (_24300 : real) (_24299 : real) : (term79 _24299 _24300) = (term145 _24300 _24299).
Proof. exact (EQ_MP (@lem1370097 _24300 _24299) (@lem0)). Qed.
Lemma lem1370099 (_24300 : real) (_24299 : real) (h1 : term17) : term145 _24300 _24299.
Proof. exact (EQ_MP (@lem1370098 _24300 _24299) (@lem1370056 _24299 _24300 h1)). Qed.
Lemma lem1370101 (b : Prop) (a : Prop) : (a \/ b) = (term148 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1370102 (_24299 : real) (_24300 : real) : (term145 _24300 _24299) = (term149 _24299 _24300).
Proof. exact (@lem1370101 (term141 _24300 _24299) (term23 _24299 _24300)). Qed.
Lemma lem1370104 (a : Prop) : (term150 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1370105 (_24300 : real) (_24299 : real) : (term151 _24300 _24299) = (real_lt _24300 _24299).
Proof. exact (@lem1370104 (real_lt _24300 _24299)). Qed.
Lemma lem1370106 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1370107 (_24300 : real) (_24299 : real) : (term152 _24300 _24299) = (term153 _24300 _24299).
Proof. exact (MK_COMB (@lem1370106) (@lem1370105 _24300 _24299)). Qed.
Lemma lem1370108 (_24299 : real) (_24300 : real) : (term23 _24299 _24300) = (term23 _24299 _24300).
Proof. exact (eq_refl (term23 _24299 _24300)). Qed.
Lemma lem1370109 (_24299 : real) (_24300 : real) : (term149 _24299 _24300) = (term154 _24299 _24300).
Proof. exact (MK_COMB (@lem1370107 _24300 _24299) (@lem1370108 _24299 _24300)). Qed.
Lemma lem1370110 (_24299 : real) (_24300 : real) : (term145 _24300 _24299) = (term154 _24299 _24300).
Proof. exact (TRANS (@lem1370102 _24299 _24300) (@lem1370109 _24299 _24300)). Qed.
Lemma lem1370113 (_24299 : real) (_24300 : real) (h1 : term17) : term154 _24299 _24300.
Proof. exact (EQ_MP (@lem1370110 _24299 _24300) (@lem1370099 _24300 _24299 h1)). Qed.
Lemma lem1370114 (y : real) (x : real) (h1 : term17) : term154 y x.
Proof. exact (@lem1370113 y x h1). Qed.
Lemma lem1370117 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term41 y x z) : term23 y x.
Proof. exact (@lem1370114 y x h1 (@lem1370070 y x z h2)). Qed.
Lemma lem1370118 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term41 y x z) : term155 y x.
Proof. exact (fun h0 : real_le y x => @lem1370117 y x z h1 h2). Qed.
Lemma lem1370120 (p : Prop) : (term156 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1370121 (y : real) (x : real) : (term155 y x) = (term23 y x).
Proof. exact (@lem1370120 (real_le y x)). Qed.
Lemma lem1370122 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term41 y x z) : term23 y x.
Proof. exact (EQ_MP (@lem1370121 y x) (@lem1370118 y x z h1 h2)). Qed.
Lemma lem1370138 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1370139 (_24294 : real) (_24295 : real) (_24296 : real) : (term157 _24295 _24294 _24296) = (term158 _24294 _24295 _24296).
Proof. exact (@lem1370138 (real_le _24294 _24296) (term23 _24295 _24296)). Qed.
Lemma lem1370145 (_24294 : real) (_24295 : real) : (term159 _24294 _24295) = (term159 _24294 _24295).
Proof. exact (eq_refl (term159 _24294 _24295)). Qed.
Lemma lem1370146 (_24294 : real) (_24295 : real) (_24296 : real) : (term140 _24295 _24294 _24296) = (term160 _24294 _24295 _24296).
Proof. exact (MK_COMB (@lem1370145 _24294 _24295) (@lem1370139 _24294 _24295 _24296)). Qed.
Lemma lem1370150 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1370151 (_24294 : real) (_24295 : real) (_24296 : real) : (term160 _24294 _24295 _24296) = (term161 _24294 _24295 _24296).
Proof. exact (@lem1370150 (real_le _24294 _24296) (term23 _24294 _24295) (term23 _24295 _24296)). Qed.
Lemma lem1370167 (_24294 : real) (_24295 : real) (_24296 : real) : (term140 _24295 _24294 _24296) = (term161 _24294 _24295 _24296).
Proof. exact (TRANS (@lem1370146 _24294 _24295 _24296) (@lem1370151 _24294 _24295 _24296)). Qed.
Lemma lem1370168 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1370169 (_24294 : real) (_24295 : real) (_24296 : real) : (term162 _24295 _24294 _24296) = (term163 _24294 _24295 _24296).
Proof. exact (MK_COMB (@lem1370168) (@lem1370167 _24294 _24295 _24296)). Qed.
Lemma lem1370173 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1370174 (_24295 : real) (_24294 : real) (_24296 : real) : (term164 _24295 _24294 _24296) = (term140 _24295 _24294 _24296).
Proof. exact (@lem1370173 (term23 _24294 _24295) (term23 _24295 _24296) (real_le _24294 _24296)). Qed.
Lemma lem1370188 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1370189 (_24294 : real) (_24295 : real) (_24296 : real) : (term157 _24295 _24294 _24296) = (term158 _24294 _24295 _24296).
Proof. exact (@lem1370188 (real_le _24294 _24296) (term23 _24295 _24296)). Qed.
Lemma lem1370195 (_24294 : real) (_24295 : real) : (term159 _24294 _24295) = (term159 _24294 _24295).
Proof. exact (eq_refl (term159 _24294 _24295)). Qed.
Lemma lem1370196 (_24294 : real) (_24295 : real) (_24296 : real) : (term140 _24295 _24294 _24296) = (term160 _24294 _24295 _24296).
Proof. exact (MK_COMB (@lem1370195 _24294 _24295) (@lem1370189 _24294 _24295 _24296)). Qed.
Lemma lem1370200 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1370201 (_24294 : real) (_24295 : real) (_24296 : real) : (term160 _24294 _24295 _24296) = (term161 _24294 _24295 _24296).
Proof. exact (@lem1370200 (real_le _24294 _24296) (term23 _24294 _24295) (term23 _24295 _24296)). Qed.
Lemma lem1370217 (_24294 : real) (_24295 : real) (_24296 : real) : (term140 _24295 _24294 _24296) = (term161 _24294 _24295 _24296).
Proof. exact (TRANS (@lem1370196 _24294 _24295 _24296) (@lem1370201 _24294 _24295 _24296)). Qed.
Lemma lem1370218 (_24294 : real) (_24295 : real) (_24296 : real) : (term164 _24295 _24294 _24296) = (term161 _24294 _24295 _24296).
Proof. exact (TRANS (@lem1370174 _24295 _24294 _24296) (@lem1370217 _24294 _24295 _24296)). Qed.
Lemma lem1370219 (_24294 : real) (_24295 : real) (_24296 : real) : ((term140 _24295 _24294 _24296) = (term164 _24295 _24294 _24296)) = ((term161 _24294 _24295 _24296) = (term161 _24294 _24295 _24296)).
Proof. exact (MK_COMB (@lem1370169 _24294 _24295 _24296) (@lem1370218 _24294 _24295 _24296)). Qed.
Lemma lem1370221 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1370222 (x : Prop) : (x = x) = True.
Proof. exact (@lem1370221 Prop x). Qed.
Lemma lem1370223 (_24294 : real) (_24295 : real) (_24296 : real) : ((term161 _24294 _24295 _24296) = (term161 _24294 _24295 _24296)) = True.
Proof. exact (@lem1370222 (term161 _24294 _24295 _24296)). Qed.
Lemma lem1370224 (_24295 : real) (_24294 : real) (_24296 : real) : ((term140 _24295 _24294 _24296) = (term164 _24295 _24294 _24296)) = True.
Proof. exact (TRANS (@lem1370219 _24294 _24295 _24296) (@lem1370223 _24294 _24295 _24296)). Qed.
Lemma lem1370225 (_24295 : real) (_24294 : real) (_24296 : real) : True = ((term140 _24295 _24294 _24296) = (term164 _24295 _24294 _24296)).
Proof. exact (SYM (@lem1370224 _24295 _24294 _24296)). Qed.
Lemma lem1370226 (_24295 : real) (_24294 : real) (_24296 : real) : (term140 _24295 _24294 _24296) = (term164 _24295 _24294 _24296).
Proof. exact (EQ_MP (@lem1370225 _24295 _24294 _24296) (@lem0)). Qed.
Lemma lem1370227 (_24295 : real) (_24294 : real) (_24296 : real) (h1 : term33) : term164 _24295 _24294 _24296.
Proof. exact (EQ_MP (@lem1370226 _24295 _24294 _24296) (@lem1370038 _24295 _24294 _24296 h1)). Qed.
Lemma lem1370229 (b : Prop) (a : Prop) : (a \/ b) = (term148 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1370230 (_24294 : real) (_24295 : real) (_24296 : real) : (term164 _24295 _24294 _24296) = (term165 _24294 _24295 _24296).
Proof. exact (@lem1370229 (term166 _24295 _24294 _24296) (term23 _24295 _24296)). Qed.
Lemma lem1370232 (a : Prop) (b : Prop) : (term167 a b) = (term168 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1370233 (_24295 : real) (_24294 : real) (_24296 : real) : (term169 _24295 _24294 _24296) = (term170 _24295 _24294 _24296).
Proof. exact (@lem1370232 (term23 _24294 _24295) (real_le _24294 _24296)). Qed.
Lemma lem1370235 (a : Prop) : (term150 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1370236 (_24294 : real) (_24295 : real) : (term78 _24294 _24295) = (real_le _24294 _24295).
Proof. exact (@lem1370235 (real_le _24294 _24295)). Qed.
Lemma lem1370237 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1370238 (_24294 : real) (_24295 : real) : (term171 _24294 _24295) = (term172 _24294 _24295).
Proof. exact (MK_COMB (@lem1370237) (@lem1370236 _24294 _24295)). Qed.
Lemma lem1370239 (_24294 : real) (_24296 : real) : (term23 _24294 _24296) = (term23 _24294 _24296).
Proof. exact (eq_refl (term23 _24294 _24296)). Qed.
Lemma lem1370240 (_24295 : real) (_24294 : real) (_24296 : real) : (term170 _24295 _24294 _24296) = (term173 _24295 _24294 _24296).
Proof. exact (MK_COMB (@lem1370238 _24294 _24295) (@lem1370239 _24294 _24296)). Qed.
Lemma lem1370241 (_24295 : real) (_24294 : real) (_24296 : real) : (term169 _24295 _24294 _24296) = (term173 _24295 _24294 _24296).
Proof. exact (TRANS (@lem1370233 _24295 _24294 _24296) (@lem1370240 _24295 _24294 _24296)). Qed.
Lemma lem1370242 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1370243 (_24295 : real) (_24294 : real) (_24296 : real) : (term174 _24295 _24294 _24296) = (term175 _24295 _24294 _24296).
Proof. exact (MK_COMB (@lem1370242) (@lem1370241 _24295 _24294 _24296)). Qed.
Lemma lem1370244 (_24295 : real) (_24296 : real) : (term23 _24295 _24296) = (term23 _24295 _24296).
Proof. exact (eq_refl (term23 _24295 _24296)). Qed.
Lemma lem1370245 (_24294 : real) (_24295 : real) (_24296 : real) : (term165 _24294 _24295 _24296) = (term176 _24294 _24295 _24296).
Proof. exact (MK_COMB (@lem1370243 _24295 _24294 _24296) (@lem1370244 _24295 _24296)). Qed.
Lemma lem1370246 (_24294 : real) (_24295 : real) (_24296 : real) : (term164 _24295 _24294 _24296) = (term176 _24294 _24295 _24296).
Proof. exact (TRANS (@lem1370230 _24294 _24295 _24296) (@lem1370245 _24294 _24295 _24296)). Qed.
Lemma lem1370248 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term41 y x z) : term173 z y x.
Proof. exact (conj (@lem1370063 y x z h2) (@lem1370122 y x z h1 h2)). Qed.
Lemma lem1370250 (_24294 : real) (_24295 : real) (_24296 : real) (h1 : term33) : term176 _24294 _24295 _24296.
Proof. exact (EQ_MP (@lem1370246 _24294 _24295 _24296) (@lem1370227 _24295 _24294 _24296 h1)). Qed.
Lemma lem1370251 (y : real) (z : real) (x : real) (h1 : term33) : term176 y z x.
Proof. exact (@lem1370250 y z x h1). Qed.
Lemma lem1370254 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : term23 z x.
Proof. exact (@lem1370251 y z x h1 (@lem1370248 y x z h2 h3)). Qed.
Lemma lem1370255 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : term155 z x.
Proof. exact (fun h0 : real_le z x => @lem1370254 y x z h1 h2 h3). Qed.
Lemma lem1370257 (p : Prop) : (term156 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1370258 (z : real) (x : real) : (term155 z x) = (term23 z x).
Proof. exact (@lem1370257 (real_le z x)). Qed.
Lemma lem1370259 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : term23 z x.
Proof. exact (EQ_MP (@lem1370258 z x) (@lem1370255 y x z h1 h2 h3)). Qed.
Lemma lem1370261 (b : Prop) (a : Prop) : (a \/ b) = (term148 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1370264 (_24298 : real) (_24297 : real) : (term82 _24297 _24298) = (term177 _24298 _24297).
Proof. exact (@lem1370261 (real_le _24297 _24298) (real_lt _24298 _24297)). Qed.
Lemma lem1370267 (_24298 : real) (_24297 : real) (h1 : term17) : term177 _24298 _24297.
Proof. exact (EQ_MP (@lem1370264 _24298 _24297) (@lem1370050 _24297 _24298 h1)). Qed.
Lemma lem1370268 (x : real) (z : real) (h1 : term17) : term177 x z.
Proof. exact (@lem1370267 x z h1). Qed.
Lemma lem1370271 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : real_lt x z.
Proof. exact (@lem1370268 x z h2 (@lem1370259 y x z h1 h2 h3)). Qed.
Lemma lem1370272 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : term144 x z.
Proof. exact (fun h0 : term141 x z => @lem1370271 y x z h1 h2 h3). Qed.
Lemma lem1370274 (p : Prop) : (term143 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1370275 (x : real) (z : real) : (term144 x z) = (real_lt x z).
Proof. exact (@lem1370274 (real_lt x z)). Qed.
Lemma lem1370276 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : real_lt x z.
Proof. exact (EQ_MP (@lem1370275 x z) (@lem1370272 y x z h1 h2 h3)). Qed.
Lemma lem1370279 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1370281 (x : real) (z : real) : (term141 x z) = (term178 x z).
Proof. exact (@lem1370279 (real_lt x z)). Qed.
Lemma lem1370284 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term178 x z.
Proof. exact (EQ_MP (@lem1370281 x z) (@lem1370040 y x z h1)). Qed.
Lemma lem1370287 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : False.
Proof. exact (@lem1370284 y x z h3 (@lem1370276 y x z h1 h2 h3)). Qed.
Lemma lem1370288 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : term179.
Proof. exact (fun h0 : ~ False => @lem1370287 y x z h1 h2 h3). Qed.
Lemma lem1370290 (p : Prop) : (term143 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1370291 : term179 = False.
Proof. exact (@lem1370290 False). Qed.
Lemma lem1370292 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : False.
Proof. exact (EQ_MP (@lem1370291) (@lem1370288 y x z h1 h2 h3)). Qed.
Lemma lem1370293 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : (term41 y x z) = False.
Proof. exact (prop_ext (fun h4 : term41 y x z => @lem1370292 y x z h1 h2 h3) (fun h4 : False => @lem1369930 y x z h3)). Qed.
Lemma lem1370294 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : False.
Proof. exact (EQ_MP (@lem1370293 y x z h1 h2 h3) (@lem1369930 y x z h3)). Qed.
Lemma lem1370295 (y : real) (x : real) (h1 : term33) (h2 : term17) (h3 : term51 y x) : False.
Proof. exact (ex_elim (@lem1369824 y x h3) (fun z : real => fun h0 : term50 y x z => @lem1370294 y x z h1 h2 h0)). Qed.
Lemma lem1370296 (x : real) (h1 : term33) (h2 : term17) (h3 : term58 x) : False.
Proof. exact (ex_elim (@lem1369823 x h3) (fun y : real => fun h0 : term57 x y => @lem1370295 y x h1 h2 h0)). Qed.
Lemma lem1370297 (h1 : term33) (h2 : term17) (h3 : term10) : False.
Proof. exact (ex_elim (@lem1369450 h3) (fun x : real => fun h0 : term63 x => @lem1370296 x h1 h2 h0)). Qed.
Lemma lem1370298 (h1 : term33) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1370297 h1 h0 h2). Qed.
Lemma lem1370299 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1370300 (h1 : term33) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem1370299) (@lem1370298 h1 h2)). Qed.
Lemma lem1370301 (h1 : term10) : term20.
Proof. exact (fun h0 : term33 => @lem1370300 h0 h1). Qed.
Lemma lem1370302 : term22.
Proof. exact (fun h0 : term10 => @lem1370301 h0). Qed.
Lemma lem1370303 : term11.
Proof. exact (EQ_MP (@lem1369345) (@lem1370302)). Qed.
Lemma lem1370305 : term11.
Proof. exact (@lem1369163 (@lem1370303)). Qed.
Lemma lem1370306 (h1 : term10) : term19.
Proof. exact (@lem1370305 (@lem1369148 h1)). Qed.
Lemma lem1370307 (h1 : term10) : term15.
Proof. exact (@lem1370306 h1 (@lem1339577)). Qed.
Lemma lem1370308 (h1 : term10) : False.
Proof. exact (@lem1370307 h1 (@lem1341566)). Qed.
Lemma lem1370309 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1370308 h1) (fun h2 : False => @lem1369148 h1)). Qed.
Lemma lem1370310 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1370309 h1) (@lem1369148 h1)). Qed.
Lemma lem1370311 : term9.
Proof. exact (fun h0 : term10 => @lem1370310 h0). Qed.
Lemma lem1370312 : term8.
Proof. exact (EQ_MP (@lem1369147) (@lem1370311)). Qed.
