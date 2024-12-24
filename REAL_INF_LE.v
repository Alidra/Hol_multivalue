Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INF_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import INF_spec.
Require Import MEMBER_NOT_EMPTY_spec.
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
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18964_spec.
Require Import thm18965_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Lemma lem5266205 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5266206 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5266207 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5266206 t1) (@lem5266205 t1)). Qed.
Lemma lem5266208 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5266207 t1 t2). Qed.
Lemma lem5266209 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5266210 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5266209 t1 t2) (@lem5266208 t1 t2)). Qed.
Lemma lem5266211 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5266210 t1 t2 t3). Qed.
Lemma lem5266212 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5266213 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5266212 t1 t2 t3) (@lem5266211 t1 t2 t3)). Qed.
Lemma lem5266214 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5266213 t1 t2 t3)). Qed.
Lemma lem5266216 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5266217 : term8 = term9.
Proof. exact (@lem5266216 term8). Qed.
Lemma lem5266218 : term9 = term8.
Proof. exact (SYM (@lem5266217)). Qed.
Lemma lem5266219 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5266220 : term11.
Proof. exact (@lem3216368 real). Qed.
Lemma lem5266225 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5266226 : term13.
Proof. exact (fun h0 : term12 => @lem5266225 h0). Qed.
Lemma lem5266227 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem5266228 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5266229 (h1 : term12) (h2 : term13) : term12.
Proof. exact (@lem5266227 h2 (@lem5266228 h1)). Qed.
Lemma lem5266230 (h1 : term12) : term14.
Proof. exact (fun h0 : term13 => @lem5266229 h1 h0). Qed.
Lemma lem5266231 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem5266232 (h1 : term12) (h2 : term13) : term12.
Proof. exact (@lem5266230 h1 (@lem5266231 h2)). Qed.
Lemma lem5266233 (h1 : term13) : term13.
Proof. exact (fun h0 : term12 => @lem5266232 h0 h1). Qed.
Lemma lem5266234 : term15.
Proof. exact (fun h0 : term13 => @lem5266233 h0). Qed.
Lemma lem5266237 : term13.
Proof. exact (@lem5266234 (@lem5266226)). Qed.
Lemma lem5266297 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5266298 : term16 = term17.
Proof. exact (@lem5266297 term18). Qed.
Lemma lem5266337 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem5266338 : term20 = term21.
Proof. exact (MK_COMB (@lem5266337) (@lem5266298)). Qed.
Lemma lem5266341 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem5266342 : term23 = term24.
Proof. exact (MK_COMB (@lem5266341) (@lem5266338)). Qed.
Lemma lem5266345 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem5266352 : term12 = term26.
Proof. exact (MK_COMB (@lem5266345) (@lem5266342)). Qed.
Lemma lem5266353 (b : real) (s : real -> Prop) : (term27 b s) = (term27 b s).
Proof. exact (eq_refl (term27 b s)). Qed.
Lemma lem5266358 (s : real -> Prop) (b : real) (x : real) : (term28 s b x) = (term28 s b x).
Proof. exact (eq_refl (term28 s b x)). Qed.
Lemma lem5266359 (s : real -> Prop) (b : real) : (term29 s b) = (term29 s b).
Proof. exact (fun_ext (fun x : real => @lem5266358 s b x)). Qed.
Lemma lem5266360 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5266361 (s : real -> Prop) (b : real) : (term30 s b) = (term30 s b).
Proof. exact (MK_COMB (@lem5266360) (@lem5266359 s b)). Qed.
Lemma lem5266362 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5266363 (s : real -> Prop) (b : real) : (term31 s b) = (term31 s b).
Proof. exact (MK_COMB (@lem5266362) (@lem5266361 s b)). Qed.
Lemma lem5266364 (b : real) (s : real -> Prop) : (term32 b s) = (term32 b s).
Proof. exact (MK_COMB (@lem5266363 s b) (@lem5266353 b s)). Qed.
Lemma lem5266365 (s : real -> Prop) : (term33 s) = (term33 s).
Proof. exact (fun_ext (fun b : real => @lem5266364 b s)). Qed.
Lemma lem5266366 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5266367 (s : real -> Prop) : (term34 s) = (term34 s).
Proof. exact (MK_COMB (@lem5266366) (@lem5266365 s)). Qed.
Lemma lem5266372 (s : real -> Prop) (x : real) : (term35 s x) = (term35 s x).
Proof. exact (eq_refl (term35 s x)). Qed.
Lemma lem5266373 (s : real -> Prop) : (term36 s) = (term36 s).
Proof. exact (fun_ext (fun x : real => @lem5266372 s x)). Qed.
Lemma lem5266374 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5266375 (s : real -> Prop) : (term37 s) = (term37 s).
Proof. exact (MK_COMB (@lem5266374) (@lem5266373 s)). Qed.
Lemma lem5266376 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5266377 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (MK_COMB (@lem5266376) (@lem5266375 s)). Qed.
Lemma lem5266378 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (MK_COMB (@lem5266377 s) (@lem5266367 s)). Qed.
Lemma lem5266383 (s : real -> Prop) (b : real) (x : real) : (term28 s b x) = (term28 s b x).
Proof. exact (eq_refl (term28 s b x)). Qed.
Lemma lem5266384 (s : real -> Prop) (b : real) : (term29 s b) = (term29 s b).
Proof. exact (fun_ext (fun x : real => @lem5266383 s b x)). Qed.
Lemma lem5266385 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5266386 (s : real -> Prop) (b : real) : (term30 s b) = (term30 s b).
Proof. exact (MK_COMB (@lem5266385) (@lem5266384 s b)). Qed.
Lemma lem5266387 (s : real -> Prop) : (term40 s) = (term40 s).
Proof. exact (fun_ext (fun b : real => @lem5266386 s b)). Qed.
Lemma lem5266388 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5266389 (s : real -> Prop) : (term41 s) = (term41 s).
Proof. exact (MK_COMB (@lem5266388) (@lem5266387 s)). Qed.
Lemma lem5266394 (s : real -> Prop) : (term42 s) = (term42 s).
Proof. exact (eq_refl (term42 s)). Qed.
Lemma lem5266395 (s : real -> Prop) : (term43 s) = (term43 s).
Proof. exact (MK_COMB (@lem5266394 s) (@lem5266389 s)). Qed.
Lemma lem5266396 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5266397 (s : real -> Prop) : (term44 s) = (term44 s).
Proof. exact (MK_COMB (@lem5266396) (@lem5266395 s)). Qed.
Lemma lem5266398 (s : real -> Prop) : (term45 s) = (term45 s).
Proof. exact (MK_COMB (@lem5266397 s) (@lem5266378 s)). Qed.
Lemma lem5266399 : term46 = term46.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5266398 s)). Qed.
Lemma lem5266400 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5266401 : term18 = term18.
Proof. exact (MK_COMB (@lem5266400) (@lem5266399)). Qed.
Lemma lem5266402 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5266403 : term17 = term17.
Proof. exact (MK_COMB (@lem5266402) (@lem5266401)). Qed.
Lemma lem5266406 (s : real -> Prop) : (term47 s) = (term47 s).
Proof. exact (eq_refl (term47 s)). Qed.
Lemma lem5266407 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5266408 (s : real -> Prop) : (term48 s) = (term48 s).
Proof. exact (fun_ext (fun x : real => @lem5266407 x s)). Qed.
Lemma lem5266409 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5266410 (s : real -> Prop) : (term49 s) = (term49 s).
Proof. exact (MK_COMB (@lem5266409) (@lem5266408 s)). Qed.
Lemma lem5266411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5266412 (s : real -> Prop) : (term50 s) = (term50 s).
Proof. exact (MK_COMB (@lem5266411) (@lem5266410 s)). Qed.
Lemma lem5266413 (s : real -> Prop) : ((term49 s) = (term47 s)) = ((term49 s) = (term47 s)).
Proof. exact (MK_COMB (@lem5266412 s) (@lem5266406 s)). Qed.
Lemma lem5266414 : term51 = term51.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5266413 s)). Qed.
Lemma lem5266415 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5266416 : term11 = term11.
Proof. exact (MK_COMB (@lem5266415) (@lem5266414)). Qed.
Lemma lem5266417 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5266418 : term19 = term19.
Proof. exact (MK_COMB (@lem5266417) (@lem5266416)). Qed.
Lemma lem5266419 : term21 = term21.
Proof. exact (MK_COMB (@lem5266418) (@lem5266403)). Qed.
Lemma lem5266428 (y : real) (x : real) (z : real) : (term52 y x z) = (term52 y x z).
Proof. exact (eq_refl (term52 y x z)). Qed.
Lemma lem5266429 (y : real) (x : real) : (term53 y x) = (term53 y x).
Proof. exact (fun_ext (fun z : real => @lem5266428 y x z)). Qed.
Lemma lem5266430 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5266431 (y : real) (x : real) : (term54 y x) = (term54 y x).
Proof. exact (MK_COMB (@lem5266430) (@lem5266429 y x)). Qed.
Lemma lem5266432 (x : real) : (term55 x) = (term55 x).
Proof. exact (fun_ext (fun y : real => @lem5266431 y x)). Qed.
Lemma lem5266433 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5266434 (x : real) : (term56 x) = (term56 x).
Proof. exact (MK_COMB (@lem5266433) (@lem5266432 x)). Qed.
Lemma lem5266435 : term57 = term57.
Proof. exact (fun_ext (fun x : real => @lem5266434 x)). Qed.
Lemma lem5266436 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5266437 : term58 = term58.
Proof. exact (MK_COMB (@lem5266436) (@lem5266435)). Qed.
Lemma lem5266438 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5266439 : term22 = term22.
Proof. exact (MK_COMB (@lem5266438) (@lem5266437)). Qed.
Lemma lem5266440 : term24 = term24.
Proof. exact (MK_COMB (@lem5266439) (@lem5266419)). Qed.
Lemma lem5266441 (s : real -> Prop) (b : real) : (term59 s b) = (term59 s b).
Proof. exact (eq_refl (term59 s b)). Qed.
Lemma lem5266446 (s : real -> Prop) (a : real) (x : real) : (term28 s a x) = (term28 s a x).
Proof. exact (eq_refl (term28 s a x)). Qed.
Lemma lem5266447 (s : real -> Prop) (a : real) : (term29 s a) = (term29 s a).
Proof. exact (fun_ext (fun x : real => @lem5266446 s a x)). Qed.
Lemma lem5266448 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5266449 (s : real -> Prop) (a : real) : (term30 s a) = (term30 s a).
Proof. exact (MK_COMB (@lem5266448) (@lem5266447 s a)). Qed.
Lemma lem5266452 (y : real) (b : real) : (term60 y b) = (term60 y b).
Proof. exact (eq_refl (term60 y b)). Qed.
Lemma lem5266453 (y : real) (b : real) (s : real -> Prop) (a : real) : (term61 y b s a) = (term61 y b s a).
Proof. exact (MK_COMB (@lem5266452 y b) (@lem5266449 s a)). Qed.
Lemma lem5266456 (y : real) (s : real -> Prop) : (term62 y s) = (term62 y s).
Proof. exact (eq_refl (term62 y s)). Qed.
Lemma lem5266457 (y : real) (b : real) (s : real -> Prop) (a : real) : (term63 y b s a) = (term63 y b s a).
Proof. exact (MK_COMB (@lem5266456 y s) (@lem5266453 y b s a)). Qed.
Lemma lem5266458 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5266459 (y : real) (b : real) (s : real -> Prop) (a : real) : (term64 y b s a) = (term64 y b s a).
Proof. exact (MK_COMB (@lem5266458) (@lem5266457 y b s a)). Qed.
Lemma lem5266460 (y : real) (a : real) (s : real -> Prop) (b : real) : (term65 y a s b) = (term65 y a s b).
Proof. exact (MK_COMB (@lem5266459 y b s a) (@lem5266441 s b)). Qed.
Lemma lem5266461 (a : real) (s : real -> Prop) (b : real) : (term66 a s b) = (term66 a s b).
Proof. exact (fun_ext (fun y : real => @lem5266460 y a s b)). Qed.
Lemma lem5266462 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5266463 (a : real) (s : real -> Prop) (b : real) : (term67 a s b) = (term67 a s b).
Proof. exact (MK_COMB (@lem5266462) (@lem5266461 a s b)). Qed.
Lemma lem5266464 (a : real) (s : real -> Prop) : (term68 a s) = (term68 a s).
Proof. exact (fun_ext (fun b : real => @lem5266463 a s b)). Qed.
Lemma lem5266465 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5266466 (a : real) (s : real -> Prop) : (term69 a s) = (term69 a s).
Proof. exact (MK_COMB (@lem5266465) (@lem5266464 a s)). Qed.
Lemma lem5266467 (s : real -> Prop) : (term70 s) = (term70 s).
Proof. exact (fun_ext (fun a : real => @lem5266466 a s)). Qed.
Lemma lem5266468 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5266469 (s : real -> Prop) : (term71 s) = (term71 s).
Proof. exact (MK_COMB (@lem5266468) (@lem5266467 s)). Qed.
Lemma lem5266470 : term72 = term72.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5266469 s)). Qed.
Lemma lem5266471 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5266472 : term8 = term8.
Proof. exact (MK_COMB (@lem5266471) (@lem5266470)). Qed.
Lemma lem5266473 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5266474 : term10 = term10.
Proof. exact (MK_COMB (@lem5266473) (@lem5266472)). Qed.
Lemma lem5266475 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5266476 : term25 = term25.
Proof. exact (MK_COMB (@lem5266475) (@lem5266474)). Qed.
Lemma lem5266477 : term26 = term26.
Proof. exact (MK_COMB (@lem5266476) (@lem5266440)). Qed.
Lemma lem5266608 : term12 = term26.
Proof. exact (TRANS (@lem5266352) (@lem5266477)). Qed.
Lemma lem5266609 : term26 = term12.
Proof. exact (SYM (@lem5266608)). Qed.
Lemma lem5266610 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5266611 (h1 : term58) : term58.
Proof. exact (h1). Qed.
Lemma lem5266612 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5266613 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem5266622 (s : real -> Prop) (a : real) (x : real) : (term28 s a x) = (term73 s a x).
Proof. exact (@lem17265 (@IN real x s) (real_le a x)). Qed.
Lemma lem5266623 (s : real -> Prop) (a : real) : (term29 s a) = (term74 s a).
Proof. exact (fun_ext (fun x : real => @lem5266622 s a x)). Qed.
Lemma lem5266624 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5266625 (s : real -> Prop) (a : real) : (term30 s a) = (term75 s a).
Proof. exact (MK_COMB (@lem5266624) (@lem5266623 s a)). Qed.
Lemma lem5266627 (y : real) (b : real) : (term60 y b) = (term60 y b).
Proof. exact (eq_refl (term60 y b)). Qed.
Lemma lem5266628 (y : real) (b : real) (s : real -> Prop) (a : real) : (term61 y b s a) = (term76 y b s a).
Proof. exact (MK_COMB (@lem5266627 y b) (@lem5266625 s a)). Qed.
Lemma lem5266630 (y : real) (s : real -> Prop) : (term62 y s) = (term62 y s).
Proof. exact (eq_refl (term62 y s)). Qed.
Lemma lem5266631 (y : real) (b : real) (s : real -> Prop) (a : real) : (term63 y b s a) = (term77 y b s a).
Proof. exact (MK_COMB (@lem5266630 y s) (@lem5266628 y b s a)). Qed.
Lemma lem5266632 (s : real -> Prop) (b : real) : (term78 s b) = (term78 s b).
Proof. exact (eq_refl (term78 s b)). Qed.
Lemma lem5266633 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5266634 (y : real) (b : real) (s : real -> Prop) (a : real) : (term79 y b s a) = (term80 y b s a).
Proof. exact (MK_COMB (@lem5266633) (@lem5266631 y b s a)). Qed.
Lemma lem5266635 (y : real) (a : real) (s : real -> Prop) (b : real) : (term81 y a s b) = (term82 y a s b).
Proof. exact (MK_COMB (@lem5266634 y b s a) (@lem5266632 s b)). Qed.
Lemma lem5266636 (y : real) (a : real) (s : real -> Prop) (b : real) : (term83 y a s b) = (term81 y a s b).
Proof. exact (@lem17362 (term63 y b s a) (term59 s b)). Qed.
Lemma lem5266637 (y : real) (a : real) (s : real -> Prop) (b : real) : (term83 y a s b) = (term82 y a s b).
Proof. exact (TRANS (@lem5266636 y a s b) (@lem5266635 y a s b)). Qed.
Lemma lem5266638 (P : real -> Prop) : (term84 P) = (term85 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5266639 (a : real) (s : real -> Prop) (b : real) : (term86 a s b) = (term87 a s b).
Proof. exact (@lem5266638 (term66 a s b)). Qed.
Lemma lem5266640 (y : real) (a : real) (s : real -> Prop) (b : real) : (term88 a s b y) = (term65 y a s b).
Proof. exact (eq_refl (term88 a s b y)). Qed.
Lemma lem5266641 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5266642 (y : real) (a : real) (s : real -> Prop) (b : real) : (term89 a s b y) = (term83 y a s b).
Proof. exact (MK_COMB (@lem5266641) (@lem5266640 y a s b)). Qed.
Lemma lem5266643 (y : real) (a : real) (s : real -> Prop) (b : real) : (term89 a s b y) = (term82 y a s b).
Proof. exact (TRANS (@lem5266642 y a s b) (@lem5266637 y a s b)). Qed.
Lemma lem5266644 (a : real) (s : real -> Prop) (b : real) : (term90 a s b) = (term91 a s b).
Proof. exact (fun_ext (fun y : real => @lem5266643 y a s b)). Qed.
Lemma lem5266645 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5266646 (a : real) (s : real -> Prop) (b : real) : (term87 a s b) = (term92 a s b).
Proof. exact (MK_COMB (@lem5266645) (@lem5266644 a s b)). Qed.
Lemma lem5266647 (a : real) (s : real -> Prop) (b : real) : (term86 a s b) = (term92 a s b).
Proof. exact (TRANS (@lem5266639 a s b) (@lem5266646 a s b)). Qed.
Lemma lem5266648 (P : real -> Prop) : (term84 P) = (term85 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5266649 (a : real) (s : real -> Prop) : (term93 a s) = (term94 a s).
Proof. exact (@lem5266648 (term68 a s)). Qed.
Lemma lem5266650 (a : real) (s : real -> Prop) (b : real) : (term95 a s b) = (term67 a s b).
Proof. exact (eq_refl (term95 a s b)). Qed.
Lemma lem5266651 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5266652 (a : real) (s : real -> Prop) (b : real) : (term96 a s b) = (term86 a s b).
Proof. exact (MK_COMB (@lem5266651) (@lem5266650 a s b)). Qed.
Lemma lem5266653 (a : real) (s : real -> Prop) (b : real) : (term96 a s b) = (term92 a s b).
Proof. exact (TRANS (@lem5266652 a s b) (@lem5266647 a s b)). Qed.
Lemma lem5266654 (a : real) (s : real -> Prop) : (term97 a s) = (term98 a s).
Proof. exact (fun_ext (fun b : real => @lem5266653 a s b)). Qed.
Lemma lem5266655 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5266656 (a : real) (s : real -> Prop) : (term94 a s) = (term99 a s).
Proof. exact (MK_COMB (@lem5266655) (@lem5266654 a s)). Qed.
Lemma lem5266657 (a : real) (s : real -> Prop) : (term93 a s) = (term99 a s).
Proof. exact (TRANS (@lem5266649 a s) (@lem5266656 a s)). Qed.
Lemma lem5266658 (P : real -> Prop) : (term84 P) = (term85 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5266659 (s : real -> Prop) : (term100 s) = (term101 s).
Proof. exact (@lem5266658 (term70 s)). Qed.
Lemma lem5266660 (a : real) (s : real -> Prop) : (term102 s a) = (term69 a s).
Proof. exact (eq_refl (term102 s a)). Qed.
Lemma lem5266661 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5266662 (a : real) (s : real -> Prop) : (term103 s a) = (term93 a s).
Proof. exact (MK_COMB (@lem5266661) (@lem5266660 a s)). Qed.
Lemma lem5266663 (a : real) (s : real -> Prop) : (term103 s a) = (term99 a s).
Proof. exact (TRANS (@lem5266662 a s) (@lem5266657 a s)). Qed.
Lemma lem5266664 (s : real -> Prop) : (term104 s) = (term105 s).
Proof. exact (fun_ext (fun a : real => @lem5266663 a s)). Qed.
Lemma lem5266665 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5266666 (s : real -> Prop) : (term101 s) = (term106 s).
Proof. exact (MK_COMB (@lem5266665) (@lem5266664 s)). Qed.
Lemma lem5266667 (s : real -> Prop) : (term100 s) = (term106 s).
Proof. exact (TRANS (@lem5266659 s) (@lem5266666 s)). Qed.
Lemma lem5266668 (P : type1022) : (term107 P) = (term108 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5266669 : term10 = term109.
Proof. exact (@lem5266668 term72). Qed.
Lemma lem5266670 (s : real -> Prop) : (term110 s) = (term71 s).
Proof. exact (eq_refl (term110 s)). Qed.
Lemma lem5266671 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5266672 (s : real -> Prop) : (term111 s) = (term100 s).
Proof. exact (MK_COMB (@lem5266671) (@lem5266670 s)). Qed.
Lemma lem5266673 (s : real -> Prop) : (term111 s) = (term106 s).
Proof. exact (TRANS (@lem5266672 s) (@lem5266667 s)). Qed.
Lemma lem5266674 : term112 = term113.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5266673 s)). Qed.
Lemma lem5266675 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5266676 : term109 = term114.
Proof. exact (MK_COMB (@lem5266675) (@lem5266674)). Qed.
Lemma lem5266677 : term10 = term114.
Proof. exact (TRANS (@lem5266669) (@lem5266676)). Qed.
Lemma lem5266711 {A : Type'} (P : A -> Prop) (Q : Prop) : (term115 A P Q) = (term116 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem5266712 (P : real -> Prop) (Q : Prop) : (term117 P Q) = (term118 P Q).
Proof. exact (@lem5266711 real P Q). Qed.
Lemma lem5266713 (a : real) (s : real -> Prop) (b : real) : (term119 a s b) = (term120 a s b).
Proof. exact (@lem5266712 (term121 b s a) (term78 s b)). Qed.
Lemma lem5266714 (y : real) (b : real) (s : real -> Prop) (a : real) : (term122 b s a y) = (term77 y b s a).
Proof. exact (eq_refl (term122 b s a y)). Qed.
Lemma lem5266715 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5266716 (y : real) (b : real) (s : real -> Prop) (a : real) : (term123 b s a y) = (term80 y b s a).
Proof. exact (MK_COMB (@lem5266715) (@lem5266714 y b s a)). Qed.
Lemma lem5266717 (s : real -> Prop) (b : real) : (term78 s b) = (term78 s b).
Proof. exact (eq_refl (term78 s b)). Qed.
Lemma lem5266718 (y : real) (a : real) (s : real -> Prop) (b : real) : (term124 a y s b) = (term82 y a s b).
Proof. exact (MK_COMB (@lem5266716 y b s a) (@lem5266717 s b)). Qed.
Lemma lem5266719 (a : real) (s : real -> Prop) (b : real) : (term125 a s b) = (term91 a s b).
Proof. exact (fun_ext (fun y : real => @lem5266718 y a s b)). Qed.
Lemma lem5266720 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5266721 (a : real) (s : real -> Prop) (b : real) : (term119 a s b) = (term92 a s b).
Proof. exact (MK_COMB (@lem5266720) (@lem5266719 a s b)). Qed.
Lemma lem5266722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5266723 (a : real) (s : real -> Prop) (b : real) : (term126 a s b) = (term127 a s b).
Proof. exact (MK_COMB (@lem5266722) (@lem5266721 a s b)). Qed.
Lemma lem5266724 (y : real) (b : real) (s : real -> Prop) (a : real) : (term122 b s a y) = (term77 y b s a).
Proof. exact (eq_refl (term122 b s a y)). Qed.
Lemma lem5266725 (b : real) (s : real -> Prop) (a : real) : (term128 b s a) = (term121 b s a).
Proof. exact (fun_ext (fun y : real => @lem5266724 y b s a)). Qed.
Lemma lem5266726 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5266727 (b : real) (s : real -> Prop) (a : real) : (term129 b s a) = (term130 b s a).
Proof. exact (MK_COMB (@lem5266726) (@lem5266725 b s a)). Qed.
Lemma lem5266728 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5266729 (b : real) (s : real -> Prop) (a : real) : (term131 b s a) = (term132 b s a).
Proof. exact (MK_COMB (@lem5266728) (@lem5266727 b s a)). Qed.
Lemma lem5266730 (s : real -> Prop) (b : real) : (term78 s b) = (term78 s b).
Proof. exact (eq_refl (term78 s b)). Qed.
Lemma lem5266731 (a : real) (s : real -> Prop) (b : real) : (term120 a s b) = (term133 a s b).
Proof. exact (MK_COMB (@lem5266729 b s a) (@lem5266730 s b)). Qed.
Lemma lem5266732 (a : real) (s : real -> Prop) (b : real) : ((term119 a s b) = (term120 a s b)) = ((term92 a s b) = (term133 a s b)).
Proof. exact (MK_COMB (@lem5266723 a s b) (@lem5266731 a s b)). Qed.
Lemma lem5266733 (a : real) (s : real -> Prop) (b : real) : (term92 a s b) = (term133 a s b).
Proof. exact (EQ_MP (@lem5266732 a s b) (@lem5266713 a s b)). Qed.
Lemma lem5266830 (a : real) (s : real -> Prop) : (term98 a s) = (term134 a s).
Proof. exact (fun_ext (fun b : real => @lem5266733 a s b)). Qed.
Lemma lem5266831 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5266832 (a : real) (s : real -> Prop) : (term99 a s) = (term135 a s).
Proof. exact (MK_COMB (@lem5266831) (@lem5266830 a s)). Qed.
Lemma lem5266881 (s : real -> Prop) : (term105 s) = (term136 s).
Proof. exact (fun_ext (fun a : real => @lem5266832 a s)). Qed.
Lemma lem5266882 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5266883 (s : real -> Prop) : (term106 s) = (term137 s).
Proof. exact (MK_COMB (@lem5266882) (@lem5266881 s)). Qed.
Lemma lem5266888 : term113 = term138.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5266883 s)). Qed.
Lemma lem5266889 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5266890 : term114 = term139.
Proof. exact (MK_COMB (@lem5266889) (@lem5266888)). Qed.
Lemma lem5266896 {A : Type'} (P : A -> Prop) (Q : Prop) : (term116 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5266897 (P : real -> Prop) (Q : Prop) : (term118 P Q) = (term117 P Q).
Proof. exact (@lem5266896 real P Q). Qed.
Lemma lem5266898 (a : real) (s : real -> Prop) (b : real) : (term120 a s b) = (term119 a s b).
Proof. exact (@lem5266897 (term121 b s a) (term78 s b)). Qed.
Lemma lem5266899 (y : real) (b : real) (s : real -> Prop) (a : real) : (term122 b s a y) = (term77 y b s a).
Proof. exact (eq_refl (term122 b s a y)). Qed.
Lemma lem5266900 (b : real) (s : real -> Prop) (a : real) : (term128 b s a) = (term121 b s a).
Proof. exact (fun_ext (fun y : real => @lem5266899 y b s a)). Qed.
Lemma lem5266901 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5266902 (b : real) (s : real -> Prop) (a : real) : (term129 b s a) = (term130 b s a).
Proof. exact (MK_COMB (@lem5266901) (@lem5266900 b s a)). Qed.
Lemma lem5266903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5266904 (b : real) (s : real -> Prop) (a : real) : (term131 b s a) = (term132 b s a).
Proof. exact (MK_COMB (@lem5266903) (@lem5266902 b s a)). Qed.
Lemma lem5266905 (s : real -> Prop) (b : real) : (term78 s b) = (term78 s b).
Proof. exact (eq_refl (term78 s b)). Qed.
Lemma lem5266906 (a : real) (s : real -> Prop) (b : real) : (term120 a s b) = (term133 a s b).
Proof. exact (MK_COMB (@lem5266904 b s a) (@lem5266905 s b)). Qed.
Lemma lem5266907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5266908 (a : real) (s : real -> Prop) (b : real) : (term140 a s b) = (term141 a s b).
Proof. exact (MK_COMB (@lem5266907) (@lem5266906 a s b)). Qed.
Lemma lem5266909 (y : real) (b : real) (s : real -> Prop) (a : real) : (term122 b s a y) = (term77 y b s a).
Proof. exact (eq_refl (term122 b s a y)). Qed.
Lemma lem5266910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5266911 (y : real) (b : real) (s : real -> Prop) (a : real) : (term123 b s a y) = (term80 y b s a).
Proof. exact (MK_COMB (@lem5266910) (@lem5266909 y b s a)). Qed.
Lemma lem5266912 (s : real -> Prop) (b : real) : (term78 s b) = (term78 s b).
Proof. exact (eq_refl (term78 s b)). Qed.
Lemma lem5266913 (y : real) (a : real) (s : real -> Prop) (b : real) : (term124 a y s b) = (term82 y a s b).
Proof. exact (MK_COMB (@lem5266911 y b s a) (@lem5266912 s b)). Qed.
Lemma lem5266914 (a : real) (s : real -> Prop) (b : real) : (term125 a s b) = (term91 a s b).
Proof. exact (fun_ext (fun y : real => @lem5266913 y a s b)). Qed.
Lemma lem5266915 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5266916 (a : real) (s : real -> Prop) (b : real) : (term119 a s b) = (term92 a s b).
Proof. exact (MK_COMB (@lem5266915) (@lem5266914 a s b)). Qed.
Lemma lem5266917 (a : real) (s : real -> Prop) (b : real) : ((term120 a s b) = (term119 a s b)) = ((term133 a s b) = (term92 a s b)).
Proof. exact (MK_COMB (@lem5266908 a s b) (@lem5266916 a s b)). Qed.
Lemma lem5266918 (a : real) (s : real -> Prop) (b : real) : (term133 a s b) = (term92 a s b).
Proof. exact (EQ_MP (@lem5266917 a s b) (@lem5266898 a s b)). Qed.
Lemma lem5266919 (a : real) (s : real -> Prop) : (term134 a s) = (term98 a s).
Proof. exact (fun_ext (fun b : real => @lem5266918 a s b)). Qed.
Lemma lem5266920 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5266921 (a : real) (s : real -> Prop) : (term135 a s) = (term99 a s).
Proof. exact (MK_COMB (@lem5266920) (@lem5266919 a s)). Qed.
Lemma lem5266922 (s : real -> Prop) : (term136 s) = (term105 s).
Proof. exact (fun_ext (fun a : real => @lem5266921 a s)). Qed.
Lemma lem5266923 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5266924 (s : real -> Prop) : (term137 s) = (term106 s).
Proof. exact (MK_COMB (@lem5266923) (@lem5266922 s)). Qed.
Lemma lem5266925 : term138 = term113.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5266924 s)). Qed.
Lemma lem5266926 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5266927 : term139 = term114.
Proof. exact (MK_COMB (@lem5266926) (@lem5266925)). Qed.
Lemma lem5266928 : term114 = term114.
Proof. exact (TRANS (@lem5266890) (@lem5266927)). Qed.
Lemma lem5266929 : term10 = term114.
Proof. exact (TRANS (@lem5266677) (@lem5266928)). Qed.
Lemma lem5266930 (h1 : term10) : term114.
Proof. exact (EQ_MP (@lem5266929) (@lem5266610 h1)). Qed.
Lemma lem5266937 (x : real) (y : real) (z : real) : (term142 x y z) = (term143 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem5266938 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem5266939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5266940 (x : real) (y : real) (z : real) : (term144 x y z) = (term145 x y z).
Proof. exact (MK_COMB (@lem5266939) (@lem5266937 x y z)). Qed.
Lemma lem5266941 (y : real) (x : real) (z : real) : (term146 y x z) = (term147 y x z).
Proof. exact (MK_COMB (@lem5266940 x y z) (@lem5266938 x z)). Qed.
Lemma lem5266942 (y : real) (x : real) (z : real) : (term52 y x z) = (term146 y x z).
Proof. exact (@lem17265 (term148 x y z) (real_le x z)). Qed.
Lemma lem5266943 (y : real) (x : real) (z : real) : (term52 y x z) = (term147 y x z).
Proof. exact (TRANS (@lem5266942 y x z) (@lem5266941 y x z)). Qed.
Lemma lem5266944 (y : real) (x : real) : (term53 y x) = (term149 y x).
Proof. exact (fun_ext (fun z : real => @lem5266943 y x z)). Qed.
Lemma lem5266945 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5266946 (y : real) (x : real) : (term54 y x) = (term150 y x).
Proof. exact (MK_COMB (@lem5266945) (@lem5266944 y x)). Qed.
Lemma lem5266947 (x : real) : (term55 x) = (term151 x).
Proof. exact (fun_ext (fun y : real => @lem5266946 y x)). Qed.
Lemma lem5266948 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5266949 (x : real) : (term56 x) = (term152 x).
Proof. exact (MK_COMB (@lem5266948) (@lem5266947 x)). Qed.
Lemma lem5266950 : term57 = term153.
Proof. exact (fun_ext (fun x : real => @lem5266949 x)). Qed.
Lemma lem5266951 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267012 : term58 = term154.
Proof. exact (MK_COMB (@lem5266951) (@lem5266950)). Qed.
Lemma lem5267013 (h1 : term58) : term154.
Proof. exact (EQ_MP (@lem5267012) (@lem5266611 h1)). Qed.
Lemma lem5267015 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5267016 (P : real -> Prop) : (term155 P) = (term156 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5267017 (s : real -> Prop) : (term157 s) = (term158 s).
Proof. exact (@lem5267016 (term48 s)). Qed.
Lemma lem5267018 (x : real) (s : real -> Prop) : (term159 s x) = (@IN real x s).
Proof. exact (eq_refl (term159 s x)). Qed.
Lemma lem5267019 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5267021 (x : real) (s : real -> Prop) : (term160 s x) = (term161 x s).
Proof. exact (MK_COMB (@lem5267019) (@lem5267018 x s)). Qed.
Lemma lem5267022 (s : real -> Prop) : (term162 s) = (term163 s).
Proof. exact (fun_ext (fun x : real => @lem5267021 x s)). Qed.
Lemma lem5267023 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267024 (s : real -> Prop) : (term158 s) = (term164 s).
Proof. exact (MK_COMB (@lem5267023) (@lem5267022 s)). Qed.
Lemma lem5267025 (s : real -> Prop) : (term157 s) = (term164 s).
Proof. exact (TRANS (@lem5267017 s) (@lem5267024 s)). Qed.
Lemma lem5267026 (s : real -> Prop) : (term48 s) = (term48 s).
Proof. exact (fun_ext (fun x : real => @lem5267015 x s)). Qed.
Lemma lem5267027 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5267028 (s : real -> Prop) : (term49 s) = (term49 s).
Proof. exact (MK_COMB (@lem5267027) (@lem5267026 s)). Qed.
Lemma lem5267029 (s : real -> Prop) : (term47 s) = (term47 s).
Proof. exact (eq_refl (term47 s)). Qed.
Lemma lem5267032 (s : real -> Prop) : (term165 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5267033 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5267034 (s : real -> Prop) : (term166 s) = (term167 s).
Proof. exact (MK_COMB (@lem5267033) (@lem5267025 s)). Qed.
Lemma lem5267035 (s : real -> Prop) : (term168 s) = (term169 s).
Proof. exact (MK_COMB (@lem5267034 s) (@lem5267029 s)). Qed.
Lemma lem5267036 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5267037 (s : real -> Prop) : (term170 s) = (term170 s).
Proof. exact (MK_COMB (@lem5267036) (@lem5267028 s)). Qed.
Lemma lem5267038 (s : real -> Prop) : (term171 s) = (term172 s).
Proof. exact (MK_COMB (@lem5267037 s) (@lem5267032 s)). Qed.
Lemma lem5267039 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5267040 (s : real -> Prop) : (term173 s) = (term174 s).
Proof. exact (MK_COMB (@lem5267039) (@lem5267038 s)). Qed.
Lemma lem5267041 (s : real -> Prop) : (term175 s) = (term176 s).
Proof. exact (MK_COMB (@lem5267040 s) (@lem5267035 s)). Qed.
Lemma lem5267042 (s : real -> Prop) : ((term49 s) = (term47 s)) = (term175 s).
Proof. exact (@lem17784 (term49 s) (term47 s)). Qed.
Lemma lem5267043 (s : real -> Prop) : ((term49 s) = (term47 s)) = (term176 s).
Proof. exact (TRANS (@lem5267042 s) (@lem5267041 s)). Qed.
Lemma lem5267044 : term51 = term177.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5267043 s)). Qed.
Lemma lem5267045 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5267046 : term11 = term178.
Proof. exact (MK_COMB (@lem5267045) (@lem5267044)). Qed.
Lemma lem5267048 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term179 A P Q) = (term180 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5267049 (P : type1022) (Q : type1022) : (term181 P Q) = (term182 P Q).
Proof. exact (@lem5267048 (real -> Prop) P Q). Qed.
Lemma lem5267050 : term183 = term184.
Proof. exact (@lem5267049 term185 term186). Qed.
Lemma lem5267051 (s : real -> Prop) : (term187 s) = (term172 s).
Proof. exact (eq_refl (term187 s)). Qed.
Lemma lem5267052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5267053 (s : real -> Prop) : (term188 s) = (term174 s).
Proof. exact (MK_COMB (@lem5267052) (@lem5267051 s)). Qed.
Lemma lem5267054 (s : real -> Prop) : (term189 s) = (term169 s).
Proof. exact (eq_refl (term189 s)). Qed.
Lemma lem5267055 (s : real -> Prop) : (term190 s) = (term176 s).
Proof. exact (MK_COMB (@lem5267053 s) (@lem5267054 s)). Qed.
Lemma lem5267056 : term191 = term177.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5267055 s)). Qed.
Lemma lem5267057 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5267058 : term183 = term178.
Proof. exact (MK_COMB (@lem5267057) (@lem5267056)). Qed.
Lemma lem5267059 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5267060 : term192 = term193.
Proof. exact (MK_COMB (@lem5267059) (@lem5267058)). Qed.
Lemma lem5267061 (s : real -> Prop) : (term187 s) = (term172 s).
Proof. exact (eq_refl (term187 s)). Qed.
Lemma lem5267062 : term194 = term185.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5267061 s)). Qed.
Lemma lem5267063 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5267064 : term195 = term196.
Proof. exact (MK_COMB (@lem5267063) (@lem5267062)). Qed.
Lemma lem5267065 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5267066 : term197 = term198.
Proof. exact (MK_COMB (@lem5267065) (@lem5267064)). Qed.
Lemma lem5267067 (s : real -> Prop) : (term189 s) = (term169 s).
Proof. exact (eq_refl (term189 s)). Qed.
Lemma lem5267068 : term199 = term186.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5267067 s)). Qed.
Lemma lem5267069 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5267070 : term200 = term201.
Proof. exact (MK_COMB (@lem5267069) (@lem5267068)). Qed.
Lemma lem5267071 : term184 = term202.
Proof. exact (MK_COMB (@lem5267066) (@lem5267070)). Qed.
Lemma lem5267072 : (term183 = term184) = (term178 = term202).
Proof. exact (MK_COMB (@lem5267060) (@lem5267071)). Qed.
Lemma lem5267073 : term178 = term202.
Proof. exact (EQ_MP (@lem5267072) (@lem5267050)). Qed.
Lemma lem5267179 {A : Type'} (P : A -> Prop) (Q : Prop) : (term203 A P Q) = (term204 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5267180 (P : real -> Prop) (Q : Prop) : (term205 P Q) = (term206 P Q).
Proof. exact (@lem5267179 real P Q). Qed.
Lemma lem5267181 (s : real -> Prop) : (term207 s) = (term208 s).
Proof. exact (@lem5267180 (term48 s) (s = (@EMPTY real))). Qed.
Lemma lem5267182 (x : real) (s : real -> Prop) : (term159 s x) = (@IN real x s).
Proof. exact (eq_refl (term159 s x)). Qed.
Lemma lem5267183 (s : real -> Prop) : (term209 s) = (term48 s).
Proof. exact (fun_ext (fun x : real => @lem5267182 x s)). Qed.
Lemma lem5267184 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5267185 (s : real -> Prop) : (term210 s) = (term49 s).
Proof. exact (MK_COMB (@lem5267184) (@lem5267183 s)). Qed.
Lemma lem5267186 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5267187 (s : real -> Prop) : (term211 s) = (term170 s).
Proof. exact (MK_COMB (@lem5267186) (@lem5267185 s)). Qed.
Lemma lem5267188 (s : real -> Prop) : (s = (@EMPTY real)) = (s = (@EMPTY real)).
Proof. exact (eq_refl (s = (@EMPTY real))). Qed.
Lemma lem5267189 (s : real -> Prop) : (term207 s) = (term172 s).
Proof. exact (MK_COMB (@lem5267187 s) (@lem5267188 s)). Qed.
Lemma lem5267190 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5267191 (s : real -> Prop) : (term212 s) = (term213 s).
Proof. exact (MK_COMB (@lem5267190) (@lem5267189 s)). Qed.
Lemma lem5267192 (x : real) (s : real -> Prop) : (term159 s x) = (@IN real x s).
Proof. exact (eq_refl (term159 s x)). Qed.
Lemma lem5267193 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5267194 (x : real) (s : real -> Prop) : (term214 s x) = (term215 x s).
Proof. exact (MK_COMB (@lem5267193) (@lem5267192 x s)). Qed.
Lemma lem5267195 (s : real -> Prop) : (s = (@EMPTY real)) = (s = (@EMPTY real)).
Proof. exact (eq_refl (s = (@EMPTY real))). Qed.
Lemma lem5267196 (x : real) (s : real -> Prop) : (term216 x s) = (term217 x s).
Proof. exact (MK_COMB (@lem5267194 x s) (@lem5267195 s)). Qed.
Lemma lem5267197 (s : real -> Prop) : (term218 s) = (term219 s).
Proof. exact (fun_ext (fun x : real => @lem5267196 x s)). Qed.
Lemma lem5267198 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5267199 (s : real -> Prop) : (term208 s) = (term220 s).
Proof. exact (MK_COMB (@lem5267198) (@lem5267197 s)). Qed.
Lemma lem5267200 (s : real -> Prop) : ((term207 s) = (term208 s)) = ((term172 s) = (term220 s)).
Proof. exact (MK_COMB (@lem5267191 s) (@lem5267199 s)). Qed.
Lemma lem5267201 (s : real -> Prop) : (term172 s) = (term220 s).
Proof. exact (EQ_MP (@lem5267200 s) (@lem5267181 s)). Qed.
Lemma lem5267202 : term185 = term221.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5267201 s)). Qed.
Lemma lem5267203 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5267204 : term196 = term222.
Proof. exact (MK_COMB (@lem5267203) (@lem5267202)). Qed.
Lemma lem5267206 {A B : Type'} (P : type1413 A B) : (term223 A B P) = (term224 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5267207 (P : type1020) : (term225 P) = (term226 P).
Proof. exact (@lem5267206 (real -> Prop) real P). Qed.
Lemma lem5267208 : term227 = term228.
Proof. exact (@lem5267207 term229). Qed.
Lemma lem5267209 (s : real -> Prop) : (term230 s) = (term219 s).
Proof. exact (eq_refl (term230 s)). Qed.
Lemma lem5267210 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5267211 (s : real -> Prop) (x : real) : (term231 s x) = (term232 s x).
Proof. exact (MK_COMB (@lem5267209 s) (@lem5267210 x)). Qed.
Lemma lem5267212 (x : real) (s : real -> Prop) : (term232 s x) = (term217 x s).
Proof. exact (eq_refl (term232 s x)). Qed.
Lemma lem5267213 (x : real) (s : real -> Prop) : (term231 s x) = (term217 x s).
Proof. exact (TRANS (@lem5267211 s x) (@lem5267212 x s)). Qed.
Lemma lem5267214 (s : real -> Prop) : (term233 s) = (term219 s).
Proof. exact (fun_ext (fun x : real => @lem5267213 x s)). Qed.
Lemma lem5267215 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5267216 (s : real -> Prop) : (term234 s) = (term220 s).
Proof. exact (MK_COMB (@lem5267215) (@lem5267214 s)). Qed.
Lemma lem5267217 : term235 = term221.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5267216 s)). Qed.
Lemma lem5267218 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5267219 : term227 = term222.
Proof. exact (MK_COMB (@lem5267218) (@lem5267217)). Qed.
Lemma lem5267220 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5267221 : term236 = term237.
Proof. exact (MK_COMB (@lem5267220) (@lem5267219)). Qed.
Lemma lem5267222 (s : real -> Prop) : (term230 s) = (term219 s).
Proof. exact (eq_refl (term230 s)). Qed.
Lemma lem5267223 (x : type1023) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5267224 (x : type1023) (s : real -> Prop) : (term238 x s) = (term239 x s).
Proof. exact (MK_COMB (@lem5267222 s) (@lem5267223 x s)). Qed.
Lemma lem5267225 (x : type1023) (s : real -> Prop) : (term239 x s) = (term240 x s).
Proof. exact (eq_refl (term239 x s)). Qed.
Lemma lem5267226 (x : type1023) (s : real -> Prop) : (term238 x s) = (term240 x s).
Proof. exact (TRANS (@lem5267224 x s) (@lem5267225 x s)). Qed.
Lemma lem5267227 (x : type1023) : (term241 x) = (term242 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5267226 x s)). Qed.
Lemma lem5267228 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5267229 (x : type1023) : (term243 x) = (term244 x).
Proof. exact (MK_COMB (@lem5267228) (@lem5267227 x)). Qed.
Lemma lem5267230 : term245 = term246.
Proof. exact (fun_ext (fun x : type1023 => @lem5267229 x)). Qed.
Lemma lem5267231 : (@ex ((real -> Prop) -> real)) = (@ex ((real -> Prop) -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real))). Qed.
Lemma lem5267232 : term228 = term247.
Proof. exact (MK_COMB (@lem5267231) (@lem5267230)). Qed.
Lemma lem5267233 : (term227 = term228) = (term222 = term247).
Proof. exact (MK_COMB (@lem5267221) (@lem5267232)). Qed.
Lemma lem5267234 : term222 = term247.
Proof. exact (EQ_MP (@lem5267233) (@lem5267208)). Qed.
Lemma lem5267235 : term196 = term247.
Proof. exact (TRANS (@lem5267204) (@lem5267234)). Qed.
Lemma lem5267236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5267237 : term198 = term248.
Proof. exact (MK_COMB (@lem5267236) (@lem5267235)). Qed.
Lemma lem5267238 : term201 = term201.
Proof. exact (eq_refl term201). Qed.
Lemma lem5267239 : term202 = term249.
Proof. exact (MK_COMB (@lem5267237) (@lem5267238)). Qed.
Lemma lem5267241 {A : Type'} (P : A -> Prop) (Q : Prop) : (term116 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5267242 (P : type257) (Q : Prop) : (term250 P Q) = (term251 P Q).
Proof. exact (@lem5267241 type1023 P Q). Qed.
Lemma lem5267243 : term252 = term253.
Proof. exact (@lem5267242 term246 term201). Qed.
Lemma lem5267244 (x : type1023) : (term254 x) = (term244 x).
Proof. exact (eq_refl (term254 x)). Qed.
Lemma lem5267245 : term255 = term246.
Proof. exact (fun_ext (fun x : type1023 => @lem5267244 x)). Qed.
Lemma lem5267246 : (@ex ((real -> Prop) -> real)) = (@ex ((real -> Prop) -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real))). Qed.
Lemma lem5267247 : term256 = term247.
Proof. exact (MK_COMB (@lem5267246) (@lem5267245)). Qed.
Lemma lem5267248 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5267249 : term257 = term248.
Proof. exact (MK_COMB (@lem5267248) (@lem5267247)). Qed.
Lemma lem5267250 : term201 = term201.
Proof. exact (eq_refl term201). Qed.
Lemma lem5267251 : term252 = term249.
Proof. exact (MK_COMB (@lem5267249) (@lem5267250)). Qed.
Lemma lem5267252 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5267253 : term258 = term259.
Proof. exact (MK_COMB (@lem5267252) (@lem5267251)). Qed.
Lemma lem5267254 (x : type1023) : (term254 x) = (term244 x).
Proof. exact (eq_refl (term254 x)). Qed.
Lemma lem5267255 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5267256 (x : type1023) : (term260 x) = (term261 x).
Proof. exact (MK_COMB (@lem5267255) (@lem5267254 x)). Qed.
Lemma lem5267257 : term201 = term201.
Proof. exact (eq_refl term201). Qed.
Lemma lem5267258 (x : type1023) : (term262 x) = (term263 x).
Proof. exact (MK_COMB (@lem5267256 x) (@lem5267257)). Qed.
Lemma lem5267259 : term264 = term265.
Proof. exact (fun_ext (fun x : type1023 => @lem5267258 x)). Qed.
Lemma lem5267260 : (@ex ((real -> Prop) -> real)) = (@ex ((real -> Prop) -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real))). Qed.
Lemma lem5267261 : term253 = term266.
Proof. exact (MK_COMB (@lem5267260) (@lem5267259)). Qed.
Lemma lem5267262 : (term252 = term253) = (term249 = term266).
Proof. exact (MK_COMB (@lem5267253) (@lem5267261)). Qed.
Lemma lem5267263 : term249 = term266.
Proof. exact (EQ_MP (@lem5267262) (@lem5267243)). Qed.
Lemma lem5267264 : term202 = term266.
Proof. exact (TRANS (@lem5267239) (@lem5267263)). Qed.
Lemma lem5267265 : term178 = term266.
Proof. exact (TRANS (@lem5267073) (@lem5267264)). Qed.
Lemma lem5267266 : term11 = term266.
Proof. exact (TRANS (@lem5267046) (@lem5267265)). Qed.
Lemma lem5267267 (h1 : term11) : term266.
Proof. exact (EQ_MP (@lem5267266) (@lem5266612 h1)). Qed.
Lemma lem5267270 (s : real -> Prop) : (term165 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5267277 (s : real -> Prop) (b : real) (x : real) : (term267 s b x) = (term268 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5267278 (P : real -> Prop) : (term84 P) = (term85 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5267279 (s : real -> Prop) (b : real) : (term269 s b) = (term270 s b).
Proof. exact (@lem5267278 (term29 s b)). Qed.
Lemma lem5267280 (s : real -> Prop) (b : real) (x : real) : (term271 s b x) = (term28 s b x).
Proof. exact (eq_refl (term271 s b x)). Qed.
Lemma lem5267281 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5267282 (s : real -> Prop) (b : real) (x : real) : (term272 s b x) = (term267 s b x).
Proof. exact (MK_COMB (@lem5267281) (@lem5267280 s b x)). Qed.
Lemma lem5267283 (s : real -> Prop) (b : real) (x : real) : (term272 s b x) = (term268 s b x).
Proof. exact (TRANS (@lem5267282 s b x) (@lem5267277 s b x)). Qed.
Lemma lem5267284 (s : real -> Prop) (b : real) : (term273 s b) = (term274 s b).
Proof. exact (fun_ext (fun x : real => @lem5267283 s b x)). Qed.
Lemma lem5267285 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5267286 (s : real -> Prop) (b : real) : (term270 s b) = (term275 s b).
Proof. exact (MK_COMB (@lem5267285) (@lem5267284 s b)). Qed.
Lemma lem5267287 (s : real -> Prop) (b : real) : (term269 s b) = (term275 s b).
Proof. exact (TRANS (@lem5267279 s b) (@lem5267286 s b)). Qed.
Lemma lem5267288 (P : real -> Prop) : (term155 P) = (term156 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5267289 (s : real -> Prop) : (term276 s) = (term277 s).
Proof. exact (@lem5267288 (term40 s)). Qed.
Lemma lem5267290 (s : real -> Prop) (b : real) : (term278 s b) = (term30 s b).
Proof. exact (eq_refl (term278 s b)). Qed.
Lemma lem5267291 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5267292 (s : real -> Prop) (b : real) : (term279 s b) = (term269 s b).
Proof. exact (MK_COMB (@lem5267291) (@lem5267290 s b)). Qed.
Lemma lem5267293 (s : real -> Prop) (b : real) : (term279 s b) = (term275 s b).
Proof. exact (TRANS (@lem5267292 s b) (@lem5267287 s b)). Qed.
Lemma lem5267294 (s : real -> Prop) : (term280 s) = (term281 s).
Proof. exact (fun_ext (fun b : real => @lem5267293 s b)). Qed.
Lemma lem5267295 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267296 (s : real -> Prop) : (term277 s) = (term282 s).
Proof. exact (MK_COMB (@lem5267295) (@lem5267294 s)). Qed.
Lemma lem5267297 (s : real -> Prop) : (term276 s) = (term282 s).
Proof. exact (TRANS (@lem5267289 s) (@lem5267296 s)). Qed.
Lemma lem5267298 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5267299 (s : real -> Prop) : (term283 s) = (term284 s).
Proof. exact (MK_COMB (@lem5267298) (@lem5267270 s)). Qed.
Lemma lem5267300 (s : real -> Prop) : (term285 s) = (term286 s).
Proof. exact (MK_COMB (@lem5267299 s) (@lem5267297 s)). Qed.
Lemma lem5267301 (s : real -> Prop) : (term287 s) = (term285 s).
Proof. exact (@lem17045 (term47 s) (term41 s)). Qed.
Lemma lem5267302 (s : real -> Prop) : (term287 s) = (term286 s).
Proof. exact (TRANS (@lem5267301 s) (@lem5267300 s)). Qed.
Lemma lem5267309 (s : real -> Prop) (x : real) : (term35 s x) = (term288 s x).
Proof. exact (@lem17265 (@IN real x s) (term59 s x)). Qed.
Lemma lem5267310 (s : real -> Prop) : (term36 s) = (term289 s).
Proof. exact (fun_ext (fun x : real => @lem5267309 s x)). Qed.
Lemma lem5267311 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267312 (s : real -> Prop) : (term37 s) = (term290 s).
Proof. exact (MK_COMB (@lem5267311) (@lem5267310 s)). Qed.
Lemma lem5267319 (s : real -> Prop) (b : real) (x : real) : (term267 s b x) = (term268 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5267320 (P : real -> Prop) : (term84 P) = (term85 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5267321 (s : real -> Prop) (b : real) : (term269 s b) = (term270 s b).
Proof. exact (@lem5267320 (term29 s b)). Qed.
Lemma lem5267322 (s : real -> Prop) (b : real) (x : real) : (term271 s b x) = (term28 s b x).
Proof. exact (eq_refl (term271 s b x)). Qed.
Lemma lem5267323 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5267324 (s : real -> Prop) (b : real) (x : real) : (term272 s b x) = (term267 s b x).
Proof. exact (MK_COMB (@lem5267323) (@lem5267322 s b x)). Qed.
Lemma lem5267325 (s : real -> Prop) (b : real) (x : real) : (term272 s b x) = (term268 s b x).
Proof. exact (TRANS (@lem5267324 s b x) (@lem5267319 s b x)). Qed.
Lemma lem5267326 (s : real -> Prop) (b : real) : (term273 s b) = (term274 s b).
Proof. exact (fun_ext (fun x : real => @lem5267325 s b x)). Qed.
Lemma lem5267327 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5267328 (s : real -> Prop) (b : real) : (term270 s b) = (term275 s b).
Proof. exact (MK_COMB (@lem5267327) (@lem5267326 s b)). Qed.
Lemma lem5267329 (s : real -> Prop) (b : real) : (term269 s b) = (term275 s b).
Proof. exact (TRANS (@lem5267321 s b) (@lem5267328 s b)). Qed.
Lemma lem5267330 (b : real) (s : real -> Prop) : (term27 b s) = (term27 b s).
Proof. exact (eq_refl (term27 b s)). Qed.
Lemma lem5267331 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5267332 (s : real -> Prop) (b : real) : (term291 s b) = (term292 s b).
Proof. exact (MK_COMB (@lem5267331) (@lem5267329 s b)). Qed.
Lemma lem5267333 (b : real) (s : real -> Prop) : (term293 b s) = (term294 b s).
Proof. exact (MK_COMB (@lem5267332 s b) (@lem5267330 b s)). Qed.
Lemma lem5267334 (b : real) (s : real -> Prop) : (term32 b s) = (term293 b s).
Proof. exact (@lem17265 (term30 s b) (term27 b s)). Qed.
Lemma lem5267335 (b : real) (s : real -> Prop) : (term32 b s) = (term294 b s).
Proof. exact (TRANS (@lem5267334 b s) (@lem5267333 b s)). Qed.
Lemma lem5267336 (s : real -> Prop) : (term33 s) = (term295 s).
Proof. exact (fun_ext (fun b : real => @lem5267335 b s)). Qed.
Lemma lem5267337 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267338 (s : real -> Prop) : (term34 s) = (term296 s).
Proof. exact (MK_COMB (@lem5267337) (@lem5267336 s)). Qed.
Lemma lem5267339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5267340 (s : real -> Prop) : (term38 s) = (term297 s).
Proof. exact (MK_COMB (@lem5267339) (@lem5267312 s)). Qed.
Lemma lem5267341 (s : real -> Prop) : (term39 s) = (term298 s).
Proof. exact (MK_COMB (@lem5267340 s) (@lem5267338 s)). Qed.
Lemma lem5267342 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5267343 (s : real -> Prop) : (term299 s) = (term300 s).
Proof. exact (MK_COMB (@lem5267342) (@lem5267302 s)). Qed.
Lemma lem5267344 (s : real -> Prop) : (term301 s) = (term302 s).
Proof. exact (MK_COMB (@lem5267343 s) (@lem5267341 s)). Qed.
Lemma lem5267345 (s : real -> Prop) : (term45 s) = (term301 s).
Proof. exact (@lem17265 (term43 s) (term39 s)). Qed.
Lemma lem5267346 (s : real -> Prop) : (term45 s) = (term302 s).
Proof. exact (TRANS (@lem5267345 s) (@lem5267344 s)). Qed.
Lemma lem5267347 : term46 = term303.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5267346 s)). Qed.
Lemma lem5267348 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5267349 : term18 = term304.
Proof. exact (MK_COMB (@lem5267348) (@lem5267347)). Qed.
Lemma lem5267596 {A B : Type'} (P : type1413 A B) : (term223 A B P) = (term224 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5267597 (P : type1626) : (term305 P) = (term306 P).
Proof. exact (@lem5267596 real real P). Qed.
Lemma lem5267598 (s : real -> Prop) : (term307 s) = (term308 s).
Proof. exact (@lem5267597 (term309 s)). Qed.
Lemma lem5267599 (s : real -> Prop) (b : real) : (term310 s b) = (term274 s b).
Proof. exact (eq_refl (term310 s b)). Qed.
Lemma lem5267600 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5267601 (s : real -> Prop) (b : real) (x : real) : (term311 s b x) = (term312 s b x).
Proof. exact (MK_COMB (@lem5267599 s b) (@lem5267600 x)). Qed.
Lemma lem5267602 (s : real -> Prop) (b : real) (x : real) : (term312 s b x) = (term268 s b x).
Proof. exact (eq_refl (term312 s b x)). Qed.
Lemma lem5267603 (s : real -> Prop) (b : real) (x : real) : (term311 s b x) = (term268 s b x).
Proof. exact (TRANS (@lem5267601 s b x) (@lem5267602 s b x)). Qed.
Lemma lem5267604 (s : real -> Prop) (b : real) : (term313 s b) = (term274 s b).
Proof. exact (fun_ext (fun x : real => @lem5267603 s b x)). Qed.
Lemma lem5267605 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5267606 (s : real -> Prop) (b : real) : (term314 s b) = (term275 s b).
Proof. exact (MK_COMB (@lem5267605) (@lem5267604 s b)). Qed.
Lemma lem5267607 (s : real -> Prop) : (term315 s) = (term281 s).
Proof. exact (fun_ext (fun b : real => @lem5267606 s b)). Qed.
Lemma lem5267608 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267609 (s : real -> Prop) : (term307 s) = (term282 s).
Proof. exact (MK_COMB (@lem5267608) (@lem5267607 s)). Qed.
Lemma lem5267610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5267611 (s : real -> Prop) : (term316 s) = (term317 s).
Proof. exact (MK_COMB (@lem5267610) (@lem5267609 s)). Qed.
Lemma lem5267612 (s : real -> Prop) (b : real) : (term310 s b) = (term274 s b).
Proof. exact (eq_refl (term310 s b)). Qed.
Lemma lem5267613 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5267614 (s : real -> Prop) (x : real -> real) (b : real) : (term318 s x b) = (term319 s x b).
Proof. exact (MK_COMB (@lem5267612 s b) (@lem5267613 x b)). Qed.
Lemma lem5267615 (s : real -> Prop) (x : real -> real) (b : real) : (term319 s x b) = (term320 s x b).
Proof. exact (eq_refl (term319 s x b)). Qed.
Lemma lem5267616 (s : real -> Prop) (x : real -> real) (b : real) : (term318 s x b) = (term320 s x b).
Proof. exact (TRANS (@lem5267614 s x b) (@lem5267615 s x b)). Qed.
Lemma lem5267617 (s : real -> Prop) (x : real -> real) : (term321 s x) = (term322 s x).
Proof. exact (fun_ext (fun b : real => @lem5267616 s x b)). Qed.
Lemma lem5267618 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267619 (s : real -> Prop) (x : real -> real) : (term323 s x) = (term324 s x).
Proof. exact (MK_COMB (@lem5267618) (@lem5267617 s x)). Qed.
Lemma lem5267620 (s : real -> Prop) : (term325 s) = (term326 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5267619 s x)). Qed.
Lemma lem5267621 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5267622 (s : real -> Prop) : (term308 s) = (term327 s).
Proof. exact (MK_COMB (@lem5267621) (@lem5267620 s)). Qed.
Lemma lem5267623 (s : real -> Prop) : ((term307 s) = (term308 s)) = ((term282 s) = (term327 s)).
Proof. exact (MK_COMB (@lem5267611 s) (@lem5267622 s)). Qed.
Lemma lem5267624 (s : real -> Prop) : (term282 s) = (term327 s).
Proof. exact (EQ_MP (@lem5267623 s) (@lem5267598 s)). Qed.
Lemma lem5267625 (s : real -> Prop) : (term284 s) = (term284 s).
Proof. exact (eq_refl (term284 s)). Qed.
Lemma lem5267626 (s : real -> Prop) : (term286 s) = (term328 s).
Proof. exact (MK_COMB (@lem5267625 s) (@lem5267624 s)). Qed.
Lemma lem5267628 {A : Type'} (P : Prop) (Q : A -> Prop) : (term329 A P Q) = (term330 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5267629 (P : Prop) (Q : type1028) : (term331 P Q) = (term332 P Q).
Proof. exact (@lem5267628 (real -> real) P Q). Qed.
Lemma lem5267630 (s : real -> Prop) : (term333 s) = (term334 s).
Proof. exact (@lem5267629 (s = (@EMPTY real)) (term326 s)). Qed.
Lemma lem5267631 (s : real -> Prop) (x : real -> real) : (term335 s x) = (term324 s x).
Proof. exact (eq_refl (term335 s x)). Qed.
Lemma lem5267632 (s : real -> Prop) : (term336 s) = (term326 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5267631 s x)). Qed.
Lemma lem5267633 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5267634 (s : real -> Prop) : (term337 s) = (term327 s).
Proof. exact (MK_COMB (@lem5267633) (@lem5267632 s)). Qed.
Lemma lem5267635 (s : real -> Prop) : (term284 s) = (term284 s).
Proof. exact (eq_refl (term284 s)). Qed.
Lemma lem5267636 (s : real -> Prop) : (term333 s) = (term328 s).
Proof. exact (MK_COMB (@lem5267635 s) (@lem5267634 s)). Qed.
Lemma lem5267637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5267638 (s : real -> Prop) : (term338 s) = (term339 s).
Proof. exact (MK_COMB (@lem5267637) (@lem5267636 s)). Qed.
Lemma lem5267639 (s : real -> Prop) (x : real -> real) : (term335 s x) = (term324 s x).
Proof. exact (eq_refl (term335 s x)). Qed.
Lemma lem5267640 (s : real -> Prop) : (term284 s) = (term284 s).
Proof. exact (eq_refl (term284 s)). Qed.
Lemma lem5267641 (s : real -> Prop) (x : real -> real) : (term340 s x) = (term341 s x).
Proof. exact (MK_COMB (@lem5267640 s) (@lem5267639 s x)). Qed.
Lemma lem5267642 (s : real -> Prop) : (term342 s) = (term343 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5267641 s x)). Qed.
Lemma lem5267643 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5267644 (s : real -> Prop) : (term334 s) = (term344 s).
Proof. exact (MK_COMB (@lem5267643) (@lem5267642 s)). Qed.
Lemma lem5267645 (s : real -> Prop) : ((term333 s) = (term334 s)) = ((term328 s) = (term344 s)).
Proof. exact (MK_COMB (@lem5267638 s) (@lem5267644 s)). Qed.
Lemma lem5267646 (s : real -> Prop) : (term328 s) = (term344 s).
Proof. exact (EQ_MP (@lem5267645 s) (@lem5267630 s)). Qed.
Lemma lem5267647 (s : real -> Prop) : (term286 s) = (term344 s).
Proof. exact (TRANS (@lem5267626 s) (@lem5267646 s)). Qed.
Lemma lem5267648 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5267649 (s : real -> Prop) : (term300 s) = (term345 s).
Proof. exact (MK_COMB (@lem5267648) (@lem5267647 s)). Qed.
Lemma lem5267651 {A : Type'} (P : A -> Prop) (Q : Prop) : (term203 A P Q) = (term204 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5267652 (P : real -> Prop) (Q : Prop) : (term205 P Q) = (term206 P Q).
Proof. exact (@lem5267651 real P Q). Qed.
Lemma lem5267653 (b : real) (s : real -> Prop) : (term346 b s) = (term347 b s).
Proof. exact (@lem5267652 (term274 s b) (term27 b s)). Qed.
Lemma lem5267654 (s : real -> Prop) (b : real) (x : real) : (term312 s b x) = (term268 s b x).
Proof. exact (eq_refl (term312 s b x)). Qed.
Lemma lem5267655 (s : real -> Prop) (b : real) : (term348 s b) = (term274 s b).
Proof. exact (fun_ext (fun x : real => @lem5267654 s b x)). Qed.
Lemma lem5267656 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5267657 (s : real -> Prop) (b : real) : (term349 s b) = (term275 s b).
Proof. exact (MK_COMB (@lem5267656) (@lem5267655 s b)). Qed.
Lemma lem5267658 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5267659 (s : real -> Prop) (b : real) : (term350 s b) = (term292 s b).
Proof. exact (MK_COMB (@lem5267658) (@lem5267657 s b)). Qed.
Lemma lem5267660 (b : real) (s : real -> Prop) : (term27 b s) = (term27 b s).
Proof. exact (eq_refl (term27 b s)). Qed.
Lemma lem5267661 (b : real) (s : real -> Prop) : (term346 b s) = (term294 b s).
Proof. exact (MK_COMB (@lem5267659 s b) (@lem5267660 b s)). Qed.
Lemma lem5267662 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5267663 (b : real) (s : real -> Prop) : (term351 b s) = (term352 b s).
Proof. exact (MK_COMB (@lem5267662) (@lem5267661 b s)). Qed.
Lemma lem5267664 (s : real -> Prop) (b : real) (x : real) : (term312 s b x) = (term268 s b x).
Proof. exact (eq_refl (term312 s b x)). Qed.
Lemma lem5267665 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5267666 (s : real -> Prop) (b : real) (x : real) : (term353 s b x) = (term354 s b x).
Proof. exact (MK_COMB (@lem5267665) (@lem5267664 s b x)). Qed.
Lemma lem5267667 (b : real) (s : real -> Prop) : (term27 b s) = (term27 b s).
Proof. exact (eq_refl (term27 b s)). Qed.
Lemma lem5267668 (x : real) (b : real) (s : real -> Prop) : (term355 x b s) = (term356 x b s).
Proof. exact (MK_COMB (@lem5267666 s b x) (@lem5267667 b s)). Qed.
Lemma lem5267669 (b : real) (s : real -> Prop) : (term357 b s) = (term358 b s).
Proof. exact (fun_ext (fun x : real => @lem5267668 x b s)). Qed.
Lemma lem5267670 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5267671 (b : real) (s : real -> Prop) : (term347 b s) = (term359 b s).
Proof. exact (MK_COMB (@lem5267670) (@lem5267669 b s)). Qed.
Lemma lem5267672 (b : real) (s : real -> Prop) : ((term346 b s) = (term347 b s)) = ((term294 b s) = (term359 b s)).
Proof. exact (MK_COMB (@lem5267663 b s) (@lem5267671 b s)). Qed.
Lemma lem5267673 (b : real) (s : real -> Prop) : (term294 b s) = (term359 b s).
Proof. exact (EQ_MP (@lem5267672 b s) (@lem5267653 b s)). Qed.
Lemma lem5267674 (s : real -> Prop) : (term295 s) = (term360 s).
Proof. exact (fun_ext (fun b : real => @lem5267673 b s)). Qed.
Lemma lem5267675 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267676 (s : real -> Prop) : (term296 s) = (term361 s).
Proof. exact (MK_COMB (@lem5267675) (@lem5267674 s)). Qed.
Lemma lem5267678 {A B : Type'} (P : type1413 A B) : (term223 A B P) = (term224 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5267679 (P : type1626) : (term305 P) = (term306 P).
Proof. exact (@lem5267678 real real P). Qed.
Lemma lem5267680 (s : real -> Prop) : (term362 s) = (term363 s).
Proof. exact (@lem5267679 (term364 s)). Qed.
Lemma lem5267681 (b : real) (s : real -> Prop) : (term365 s b) = (term358 b s).
Proof. exact (eq_refl (term365 s b)). Qed.
Lemma lem5267682 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5267683 (b : real) (s : real -> Prop) (x : real) : (term366 s b x) = (term367 b s x).
Proof. exact (MK_COMB (@lem5267681 b s) (@lem5267682 x)). Qed.
Lemma lem5267684 (x : real) (b : real) (s : real -> Prop) : (term367 b s x) = (term356 x b s).
Proof. exact (eq_refl (term367 b s x)). Qed.
Lemma lem5267685 (x : real) (b : real) (s : real -> Prop) : (term366 s b x) = (term356 x b s).
Proof. exact (TRANS (@lem5267683 b s x) (@lem5267684 x b s)). Qed.
Lemma lem5267686 (b : real) (s : real -> Prop) : (term368 s b) = (term358 b s).
Proof. exact (fun_ext (fun x : real => @lem5267685 x b s)). Qed.
Lemma lem5267687 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5267688 (b : real) (s : real -> Prop) : (term369 s b) = (term359 b s).
Proof. exact (MK_COMB (@lem5267687) (@lem5267686 b s)). Qed.
Lemma lem5267689 (s : real -> Prop) : (term370 s) = (term360 s).
Proof. exact (fun_ext (fun b : real => @lem5267688 b s)). Qed.
Lemma lem5267690 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267691 (s : real -> Prop) : (term362 s) = (term361 s).
Proof. exact (MK_COMB (@lem5267690) (@lem5267689 s)). Qed.
Lemma lem5267692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5267693 (s : real -> Prop) : (term371 s) = (term372 s).
Proof. exact (MK_COMB (@lem5267692) (@lem5267691 s)). Qed.
Lemma lem5267694 (b : real) (s : real -> Prop) : (term365 s b) = (term358 b s).
Proof. exact (eq_refl (term365 s b)). Qed.
Lemma lem5267695 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5267696 (s : real -> Prop) (x : real -> real) (b : real) : (term373 s x b) = (term374 s x b).
Proof. exact (MK_COMB (@lem5267694 b s) (@lem5267695 x b)). Qed.
Lemma lem5267697 (x : real -> real) (b : real) (s : real -> Prop) : (term374 s x b) = (term375 x b s).
Proof. exact (eq_refl (term374 s x b)). Qed.
Lemma lem5267698 (x : real -> real) (b : real) (s : real -> Prop) : (term373 s x b) = (term375 x b s).
Proof. exact (TRANS (@lem5267696 s x b) (@lem5267697 x b s)). Qed.
Lemma lem5267699 (x : real -> real) (s : real -> Prop) : (term376 s x) = (term377 x s).
Proof. exact (fun_ext (fun b : real => @lem5267698 x b s)). Qed.
Lemma lem5267700 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267701 (x : real -> real) (s : real -> Prop) : (term378 s x) = (term379 x s).
Proof. exact (MK_COMB (@lem5267700) (@lem5267699 x s)). Qed.
Lemma lem5267702 (s : real -> Prop) : (term380 s) = (term381 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5267701 x s)). Qed.
Lemma lem5267703 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5267704 (s : real -> Prop) : (term363 s) = (term382 s).
Proof. exact (MK_COMB (@lem5267703) (@lem5267702 s)). Qed.
Lemma lem5267705 (s : real -> Prop) : ((term362 s) = (term363 s)) = ((term361 s) = (term382 s)).
Proof. exact (MK_COMB (@lem5267693 s) (@lem5267704 s)). Qed.
Lemma lem5267706 (s : real -> Prop) : (term361 s) = (term382 s).
Proof. exact (EQ_MP (@lem5267705 s) (@lem5267680 s)). Qed.
Lemma lem5267707 (s : real -> Prop) : (term296 s) = (term382 s).
Proof. exact (TRANS (@lem5267676 s) (@lem5267706 s)). Qed.
Lemma lem5267708 (s : real -> Prop) : (term297 s) = (term297 s).
Proof. exact (eq_refl (term297 s)). Qed.
Lemma lem5267709 (s : real -> Prop) : (term298 s) = (term383 s).
Proof. exact (MK_COMB (@lem5267708 s) (@lem5267707 s)). Qed.
Lemma lem5267711 {A : Type'} (P : Prop) (Q : A -> Prop) : (term384 A P Q) = (term385 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5267712 (P : Prop) (Q : type1028) : (term386 P Q) = (term387 P Q).
Proof. exact (@lem5267711 (real -> real) P Q). Qed.
Lemma lem5267713 (s : real -> Prop) : (term388 s) = (term389 s).
Proof. exact (@lem5267712 (term290 s) (term381 s)). Qed.
Lemma lem5267714 (x : real -> real) (s : real -> Prop) : (term390 s x) = (term379 x s).
Proof. exact (eq_refl (term390 s x)). Qed.
Lemma lem5267715 (s : real -> Prop) : (term391 s) = (term381 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5267714 x s)). Qed.
Lemma lem5267716 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5267717 (s : real -> Prop) : (term392 s) = (term382 s).
Proof. exact (MK_COMB (@lem5267716) (@lem5267715 s)). Qed.
Lemma lem5267718 (s : real -> Prop) : (term297 s) = (term297 s).
Proof. exact (eq_refl (term297 s)). Qed.
Lemma lem5267719 (s : real -> Prop) : (term388 s) = (term383 s).
Proof. exact (MK_COMB (@lem5267718 s) (@lem5267717 s)). Qed.
Lemma lem5267720 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5267721 (s : real -> Prop) : (term393 s) = (term394 s).
Proof. exact (MK_COMB (@lem5267720) (@lem5267719 s)). Qed.
Lemma lem5267722 (x : real -> real) (s : real -> Prop) : (term390 s x) = (term379 x s).
Proof. exact (eq_refl (term390 s x)). Qed.
Lemma lem5267723 (s : real -> Prop) : (term297 s) = (term297 s).
Proof. exact (eq_refl (term297 s)). Qed.
Lemma lem5267724 (x : real -> real) (s : real -> Prop) : (term395 s x) = (term396 x s).
Proof. exact (MK_COMB (@lem5267723 s) (@lem5267722 x s)). Qed.
Lemma lem5267725 (s : real -> Prop) : (term397 s) = (term398 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5267724 x s)). Qed.
Lemma lem5267726 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5267727 (s : real -> Prop) : (term389 s) = (term399 s).
Proof. exact (MK_COMB (@lem5267726) (@lem5267725 s)). Qed.
Lemma lem5267728 (s : real -> Prop) : ((term388 s) = (term389 s)) = ((term383 s) = (term399 s)).
Proof. exact (MK_COMB (@lem5267721 s) (@lem5267727 s)). Qed.
Lemma lem5267729 (s : real -> Prop) : (term383 s) = (term399 s).
Proof. exact (EQ_MP (@lem5267728 s) (@lem5267713 s)). Qed.
Lemma lem5267730 (s : real -> Prop) : (term298 s) = (term399 s).
Proof. exact (TRANS (@lem5267709 s) (@lem5267729 s)). Qed.
Lemma lem5267731 (s : real -> Prop) : (term302 s) = (term400 s).
Proof. exact (MK_COMB (@lem5267649 s) (@lem5267730 s)). Qed.
Lemma lem5267733 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term401 A P Q) = (term402 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5267734 (P : type1028) (Q : type1028) : (term403 P Q) = (term404 P Q).
Proof. exact (@lem5267733 (real -> real) P Q). Qed.
Lemma lem5267735 (s : real -> Prop) : (term405 s) = (term406 s).
Proof. exact (@lem5267734 (term343 s) (term398 s)). Qed.
Lemma lem5267736 (s : real -> Prop) (x : real -> real) : (term407 s x) = (term341 s x).
Proof. exact (eq_refl (term407 s x)). Qed.
Lemma lem5267737 (s : real -> Prop) : (term408 s) = (term343 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5267736 s x)). Qed.
Lemma lem5267738 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5267739 (s : real -> Prop) : (term409 s) = (term344 s).
Proof. exact (MK_COMB (@lem5267738) (@lem5267737 s)). Qed.
Lemma lem5267740 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5267741 (s : real -> Prop) : (term410 s) = (term345 s).
Proof. exact (MK_COMB (@lem5267740) (@lem5267739 s)). Qed.
Lemma lem5267742 (x : real -> real) (s : real -> Prop) : (term411 s x) = (term396 x s).
Proof. exact (eq_refl (term411 s x)). Qed.
Lemma lem5267743 (s : real -> Prop) : (term412 s) = (term398 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5267742 x s)). Qed.
Lemma lem5267744 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5267745 (s : real -> Prop) : (term413 s) = (term399 s).
Proof. exact (MK_COMB (@lem5267744) (@lem5267743 s)). Qed.
Lemma lem5267746 (s : real -> Prop) : (term405 s) = (term400 s).
Proof. exact (MK_COMB (@lem5267741 s) (@lem5267745 s)). Qed.
Lemma lem5267747 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5267748 (s : real -> Prop) : (term414 s) = (term415 s).
Proof. exact (MK_COMB (@lem5267747) (@lem5267746 s)). Qed.
Lemma lem5267749 (s : real -> Prop) (x : real -> real) : (term407 s x) = (term341 s x).
Proof. exact (eq_refl (term407 s x)). Qed.
Lemma lem5267750 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5267751 (s : real -> Prop) (x : real -> real) : (term416 s x) = (term417 s x).
Proof. exact (MK_COMB (@lem5267750) (@lem5267749 s x)). Qed.
Lemma lem5267752 (x : real -> real) (s : real -> Prop) : (term411 s x) = (term396 x s).
Proof. exact (eq_refl (term411 s x)). Qed.
Lemma lem5267753 (x : real -> real) (s : real -> Prop) : (term418 s x) = (term419 x s).
Proof. exact (MK_COMB (@lem5267751 s x) (@lem5267752 x s)). Qed.
Lemma lem5267754 (s : real -> Prop) : (term420 s) = (term421 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5267753 x s)). Qed.
Lemma lem5267755 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5267756 (s : real -> Prop) : (term406 s) = (term422 s).
Proof. exact (MK_COMB (@lem5267755) (@lem5267754 s)). Qed.
Lemma lem5267757 (s : real -> Prop) : ((term405 s) = (term406 s)) = ((term400 s) = (term422 s)).
Proof. exact (MK_COMB (@lem5267748 s) (@lem5267756 s)). Qed.
Lemma lem5267758 (s : real -> Prop) : (term400 s) = (term422 s).
Proof. exact (EQ_MP (@lem5267757 s) (@lem5267735 s)). Qed.
Lemma lem5267759 (s : real -> Prop) : (term302 s) = (term422 s).
Proof. exact (TRANS (@lem5267731 s) (@lem5267758 s)). Qed.
Lemma lem5267760 : term303 = term423.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5267759 s)). Qed.
Lemma lem5267761 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5267762 : term304 = term424.
Proof. exact (MK_COMB (@lem5267761) (@lem5267760)). Qed.
Lemma lem5267764 {A B : Type'} (P : type1413 A B) : (term223 A B P) = (term224 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5267765 (P : type1017) : (term425 P) = (term426 P).
Proof. exact (@lem5267764 (real -> Prop) (real -> real) P). Qed.
Lemma lem5267766 : term427 = term428.
Proof. exact (@lem5267765 term429). Qed.
Lemma lem5267767 (s : real -> Prop) : (term430 s) = (term421 s).
Proof. exact (eq_refl (term430 s)). Qed.
Lemma lem5267768 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5267769 (s : real -> Prop) (x : real -> real) : (term431 s x) = (term432 s x).
Proof. exact (MK_COMB (@lem5267767 s) (@lem5267768 x)). Qed.
Lemma lem5267770 (x : real -> real) (s : real -> Prop) : (term432 s x) = (term419 x s).
Proof. exact (eq_refl (term432 s x)). Qed.
Lemma lem5267771 (x : real -> real) (s : real -> Prop) : (term431 s x) = (term419 x s).
Proof. exact (TRANS (@lem5267769 s x) (@lem5267770 x s)). Qed.
Lemma lem5267772 (s : real -> Prop) : (term433 s) = (term421 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5267771 x s)). Qed.
Lemma lem5267773 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5267774 (s : real -> Prop) : (term434 s) = (term422 s).
Proof. exact (MK_COMB (@lem5267773) (@lem5267772 s)). Qed.
Lemma lem5267775 : term435 = term423.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5267774 s)). Qed.
Lemma lem5267776 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5267777 : term427 = term424.
Proof. exact (MK_COMB (@lem5267776) (@lem5267775)). Qed.
Lemma lem5267778 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5267779 : term436 = term437.
Proof. exact (MK_COMB (@lem5267778) (@lem5267777)). Qed.
Lemma lem5267780 (s : real -> Prop) : (term430 s) = (term421 s).
Proof. exact (eq_refl (term430 s)). Qed.
Lemma lem5267781 (x : type1021) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5267782 (x : type1021) (s : real -> Prop) : (term438 x s) = (term439 x s).
Proof. exact (MK_COMB (@lem5267780 s) (@lem5267781 x s)). Qed.
Lemma lem5267783 (x : type1021) (s : real -> Prop) : (term439 x s) = (term440 x s).
Proof. exact (eq_refl (term439 x s)). Qed.
Lemma lem5267784 (x : type1021) (s : real -> Prop) : (term438 x s) = (term440 x s).
Proof. exact (TRANS (@lem5267782 x s) (@lem5267783 x s)). Qed.
Lemma lem5267785 (x : type1021) : (term441 x) = (term442 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5267784 x s)). Qed.
Lemma lem5267786 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5267787 (x : type1021) : (term443 x) = (term444 x).
Proof. exact (MK_COMB (@lem5267786) (@lem5267785 x)). Qed.
Lemma lem5267788 : term445 = term446.
Proof. exact (fun_ext (fun x : type1021 => @lem5267787 x)). Qed.
Lemma lem5267789 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5267790 : term428 = term447.
Proof. exact (MK_COMB (@lem5267789) (@lem5267788)). Qed.
Lemma lem5267791 : (term427 = term428) = (term424 = term447).
Proof. exact (MK_COMB (@lem5267779) (@lem5267790)). Qed.
Lemma lem5267792 : term424 = term447.
Proof. exact (EQ_MP (@lem5267791) (@lem5267766)). Qed.
Lemma lem5267794 : term304 = term447.
Proof. exact (TRANS (@lem5267762) (@lem5267792)). Qed.
Lemma lem5267795 : term18 = term447.
Proof. exact (TRANS (@lem5267349) (@lem5267794)). Qed.
Lemma lem5267796 (h1 : term18) : term447.
Proof. exact (EQ_MP (@lem5267795) (@lem5266613 h1)). Qed.
Lemma lem5267797 (x : type1021) (h1 : term444 x) : term444 x.
Proof. exact (h1). Qed.
Lemma lem5267798 (x' : type1023) (h1 : term263 x') : term263 x'.
Proof. exact (h1). Qed.
Lemma lem5267799 (s : real -> Prop) (h1 : term106 s) : term106 s.
Proof. exact (h1). Qed.
Lemma lem5267800 (a : real) (s : real -> Prop) (h1 : term99 a s) : term99 a s.
Proof. exact (h1). Qed.
Lemma lem5267801 (a : real) (s : real -> Prop) (b : real) (h1 : term92 a s b) : term92 a s b.
Proof. exact (h1). Qed.
Lemma lem5267802 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term82 y a s b.
Proof. exact (h1). Qed.
Lemma lem5267827 (y : real) (x : real) (z : real) : (term147 y x z) = (term147 y x z).
Proof. exact (eq_refl (term147 y x z)). Qed.
Lemma lem5267828 (y : real) (x : real) : (term149 y x) = (term149 y x).
Proof. exact (fun_ext (fun z : real => @lem5267827 y x z)). Qed.
Lemma lem5267829 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267830 (y : real) (x : real) : (term150 y x) = (term150 y x).
Proof. exact (MK_COMB (@lem5267829) (@lem5267828 y x)). Qed.
Lemma lem5267831 (x : real) : (term151 x) = (term151 x).
Proof. exact (fun_ext (fun y : real => @lem5267830 y x)). Qed.
Lemma lem5267832 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267833 (x : real) : (term152 x) = (term152 x).
Proof. exact (MK_COMB (@lem5267832) (@lem5267831 x)). Qed.
Lemma lem5267834 : term153 = term153.
Proof. exact (fun_ext (fun x : real => @lem5267833 x)). Qed.
Lemma lem5267835 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267836 : term154 = term154.
Proof. exact (MK_COMB (@lem5267835) (@lem5267834)). Qed.
Lemma lem5267837 (h1 : term58) : term154.
Proof. exact (EQ_MP (@lem5267836) (@lem5267013 h1)). Qed.
Lemma lem5267870 (x : type1021) (b : real) (s : real -> Prop) : (term448 x b s) = (term448 x b s).
Proof. exact (eq_refl (term448 x b s)). Qed.
Lemma lem5267871 (x : type1021) (s : real -> Prop) : (term449 x s) = (term449 x s).
Proof. exact (fun_ext (fun b : real => @lem5267870 x b s)). Qed.
Lemma lem5267872 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267873 (x : type1021) (s : real -> Prop) : (term450 x s) = (term450 x s).
Proof. exact (MK_COMB (@lem5267872) (@lem5267871 x s)). Qed.
Lemma lem5267890 (s : real -> Prop) (x : real) : (term288 s x) = (term288 s x).
Proof. exact (eq_refl (term288 s x)). Qed.
Lemma lem5267891 (s : real -> Prop) : (term289 s) = (term289 s).
Proof. exact (fun_ext (fun x : real => @lem5267890 s x)). Qed.
Lemma lem5267892 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267893 (s : real -> Prop) : (term290 s) = (term290 s).
Proof. exact (MK_COMB (@lem5267892) (@lem5267891 s)). Qed.
Lemma lem5267894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5267895 (s : real -> Prop) : (term297 s) = (term297 s).
Proof. exact (MK_COMB (@lem5267894) (@lem5267893 s)). Qed.
Lemma lem5267896 (x : type1021) (s : real -> Prop) : (term451 x s) = (term451 x s).
Proof. exact (MK_COMB (@lem5267895 s) (@lem5267873 x s)). Qed.
Lemma lem5267919 (x : type1021) (s : real -> Prop) (b : real) : (term452 x s b) = (term452 x s b).
Proof. exact (eq_refl (term452 x s b)). Qed.
Lemma lem5267920 (x : type1021) (s : real -> Prop) : (term453 x s) = (term453 x s).
Proof. exact (fun_ext (fun b : real => @lem5267919 x s b)). Qed.
Lemma lem5267921 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267922 (x : type1021) (s : real -> Prop) : (term454 x s) = (term454 x s).
Proof. exact (MK_COMB (@lem5267921) (@lem5267920 x s)). Qed.
Lemma lem5267929 (s : real -> Prop) : (term284 s) = (term284 s).
Proof. exact (eq_refl (term284 s)). Qed.
Lemma lem5267930 (x : type1021) (s : real -> Prop) : (term455 x s) = (term455 x s).
Proof. exact (MK_COMB (@lem5267929 s) (@lem5267922 x s)). Qed.
Lemma lem5267931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5267932 (x : type1021) (s : real -> Prop) : (term456 x s) = (term456 x s).
Proof. exact (MK_COMB (@lem5267931) (@lem5267930 x s)). Qed.
Lemma lem5267933 (x : type1021) (s : real -> Prop) : (term440 x s) = (term440 x s).
Proof. exact (MK_COMB (@lem5267932 x s) (@lem5267896 x s)). Qed.
Lemma lem5267934 (x : type1021) : (term442 x) = (term442 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5267933 x s)). Qed.
Lemma lem5267935 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5267936 (x : type1021) : (term444 x) = (term444 x).
Proof. exact (MK_COMB (@lem5267935) (@lem5267934 x)). Qed.
Lemma lem5267937 (x : type1021) (h1 : term444 x) : term444 x.
Proof. exact (EQ_MP (@lem5267936 x) (@lem5267797 x h1)). Qed.
Lemma lem5267944 (s : real -> Prop) : (term47 s) = (term47 s).
Proof. exact (eq_refl (term47 s)). Qed.
Lemma lem5267951 (x : real) (s : real -> Prop) : (term161 x s) = (term161 x s).
Proof. exact (eq_refl (term161 x s)). Qed.
Lemma lem5267952 (s : real -> Prop) : (term163 s) = (term163 s).
Proof. exact (fun_ext (fun x : real => @lem5267951 x s)). Qed.
Lemma lem5267953 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5267954 (s : real -> Prop) : (term164 s) = (term164 s).
Proof. exact (MK_COMB (@lem5267953) (@lem5267952 s)). Qed.
Lemma lem5267955 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5267956 (s : real -> Prop) : (term167 s) = (term167 s).
Proof. exact (MK_COMB (@lem5267955) (@lem5267954 s)). Qed.
Lemma lem5267957 (s : real -> Prop) : (term169 s) = (term169 s).
Proof. exact (MK_COMB (@lem5267956 s) (@lem5267944 s)). Qed.
Lemma lem5267958 : term186 = term186.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5267957 s)). Qed.
Lemma lem5267959 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5267960 : term201 = term201.
Proof. exact (MK_COMB (@lem5267959) (@lem5267958)). Qed.
Lemma lem5267975 (x' : type1023) (s : real -> Prop) : (term240 x' s) = (term240 x' s).
Proof. exact (eq_refl (term240 x' s)). Qed.
Lemma lem5267976 (x' : type1023) : (term242 x') = (term242 x').
Proof. exact (fun_ext (fun s : real -> Prop => @lem5267975 x' s)). Qed.
Lemma lem5267977 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5267978 (x' : type1023) : (term244 x') = (term244 x').
Proof. exact (MK_COMB (@lem5267977) (@lem5267976 x')). Qed.
Lemma lem5267979 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5267980 (x' : type1023) : (term261 x') = (term261 x').
Proof. exact (MK_COMB (@lem5267979) (@lem5267978 x')). Qed.
Lemma lem5267981 (x' : type1023) : (term263 x') = (term263 x').
Proof. exact (MK_COMB (@lem5267980 x') (@lem5267960)). Qed.
Lemma lem5267982 (x' : type1023) (h1 : term263 x') : term263 x'.
Proof. exact (EQ_MP (@lem5267981 x') (@lem5267798 x' h1)). Qed.
Lemma lem5267991 (s : real -> Prop) (b : real) : (term78 s b) = (term78 s b).
Proof. exact (eq_refl (term78 s b)). Qed.
Lemma lem5268006 (s : real -> Prop) (a : real) (x : real) : (term73 s a x) = (term73 s a x).
Proof. exact (eq_refl (term73 s a x)). Qed.
Lemma lem5268007 (s : real -> Prop) (a : real) : (term74 s a) = (term74 s a).
Proof. exact (fun_ext (fun x : real => @lem5268006 s a x)). Qed.
Lemma lem5268008 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268009 (s : real -> Prop) (a : real) : (term75 s a) = (term75 s a).
Proof. exact (MK_COMB (@lem5268008) (@lem5268007 s a)). Qed.
Lemma lem5268016 (y : real) (b : real) : (term60 y b) = (term60 y b).
Proof. exact (eq_refl (term60 y b)). Qed.
Lemma lem5268017 (y : real) (b : real) (s : real -> Prop) (a : real) : (term76 y b s a) = (term76 y b s a).
Proof. exact (MK_COMB (@lem5268016 y b) (@lem5268009 s a)). Qed.
Lemma lem5268024 (y : real) (s : real -> Prop) : (term62 y s) = (term62 y s).
Proof. exact (eq_refl (term62 y s)). Qed.
Lemma lem5268025 (y : real) (b : real) (s : real -> Prop) (a : real) : (term77 y b s a) = (term77 y b s a).
Proof. exact (MK_COMB (@lem5268024 y s) (@lem5268017 y b s a)). Qed.
Lemma lem5268026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5268027 (y : real) (b : real) (s : real -> Prop) (a : real) : (term80 y b s a) = (term80 y b s a).
Proof. exact (MK_COMB (@lem5268026) (@lem5268025 y b s a)). Qed.
Lemma lem5268028 (y : real) (a : real) (s : real -> Prop) (b : real) : (term82 y a s b) = (term82 y a s b).
Proof. exact (MK_COMB (@lem5268027 y b s a) (@lem5267991 s b)). Qed.
Lemma lem5268029 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term82 y a s b.
Proof. exact (EQ_MP (@lem5268028 y a s b) (@lem5267802 y a s b h1)). Qed.
Lemma lem5268031 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term77 y b s a.
Proof. exact (proj1 (@lem5268029 y a s b h1)). Qed.
Lemma lem5268032 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term76 y b s a.
Proof. exact (proj2 (@lem5268031 y a s b h1)). Qed.
Lemma lem5268034 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term75 s a.
Proof. exact (proj2 (@lem5268032 y a s b h1)). Qed.
Lemma lem5268036 (x' : type1023) (h1 : term263 x') : term201.
Proof. exact (proj2 (@lem5267982 x' h1)). Qed.
Lemma lem5268051 (y : real) (x : real) (z : real) : (term147 y x z) = (term147 y x z).
Proof. exact (eq_refl (term147 y x z)). Qed.
Lemma lem5268052 (y : real) (x : real) : (term149 y x) = (term149 y x).
Proof. exact (fun_ext (fun z : real => @lem5268051 y x z)). Qed.
Lemma lem5268053 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268054 (y : real) (x : real) : (term150 y x) = (term150 y x).
Proof. exact (MK_COMB (@lem5268053) (@lem5268052 y x)). Qed.
Lemma lem5268055 (x : real) : (term151 x) = (term151 x).
Proof. exact (fun_ext (fun y : real => @lem5268054 y x)). Qed.
Lemma lem5268056 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268057 (x : real) : (term152 x) = (term152 x).
Proof. exact (MK_COMB (@lem5268056) (@lem5268055 x)). Qed.
Lemma lem5268058 : term153 = term153.
Proof. exact (fun_ext (fun x : real => @lem5268057 x)). Qed.
Lemma lem5268059 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268061 : term154 = term154.
Proof. exact (MK_COMB (@lem5268059) (@lem5268058)). Qed.
Lemma lem5268062 (h1 : term58) : term154.
Proof. exact (EQ_MP (@lem5268061) (@lem5267837 h1)). Qed.
Lemma lem5268064 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5268065 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5268064 real P Q). Qed.
Lemma lem5268066 (x : type1021) (s : real -> Prop) : (term461 x s) = (term462 x s).
Proof. exact (@lem5268065 (s = (@EMPTY real)) (term453 x s)). Qed.
Lemma lem5268067 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5268068 (x : type1021) (s : real -> Prop) : (term464 x s) = (term453 x s).
Proof. exact (fun_ext (fun b : real => @lem5268067 x s b)). Qed.
Lemma lem5268069 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268070 (x : type1021) (s : real -> Prop) : (term465 x s) = (term454 x s).
Proof. exact (MK_COMB (@lem5268069) (@lem5268068 x s)). Qed.
Lemma lem5268071 (s : real -> Prop) : (term284 s) = (term284 s).
Proof. exact (eq_refl (term284 s)). Qed.
Lemma lem5268072 (x : type1021) (s : real -> Prop) : (term461 x s) = (term455 x s).
Proof. exact (MK_COMB (@lem5268071 s) (@lem5268070 x s)). Qed.
Lemma lem5268073 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5268074 (x : type1021) (s : real -> Prop) : (term466 x s) = (term467 x s).
Proof. exact (MK_COMB (@lem5268073) (@lem5268072 x s)). Qed.
Lemma lem5268075 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term452 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5268076 (s : real -> Prop) : (term284 s) = (term284 s).
Proof. exact (eq_refl (term284 s)). Qed.
Lemma lem5268077 (x : type1021) (s : real -> Prop) (b : real) : (term468 x s b) = (term469 x s b).
Proof. exact (MK_COMB (@lem5268076 s) (@lem5268075 x s b)). Qed.
Lemma lem5268078 (x : type1021) (s : real -> Prop) : (term470 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5268077 x s b)). Qed.
Lemma lem5268079 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268080 (x : type1021) (s : real -> Prop) : (term462 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5268079) (@lem5268078 x s)). Qed.
Lemma lem5268081 (x : type1021) (s : real -> Prop) : ((term461 x s) = (term462 x s)) = ((term455 x s) = (term472 x s)).
Proof. exact (MK_COMB (@lem5268074 x s) (@lem5268080 x s)). Qed.
Lemma lem5268082 (x : type1021) (s : real -> Prop) : (term455 x s) = (term472 x s).
Proof. exact (EQ_MP (@lem5268081 x s) (@lem5268066 x s)). Qed.
Lemma lem5268083 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5268084 (x : type1021) (s : real -> Prop) : (term456 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5268083) (@lem5268082 x s)). Qed.
Lemma lem5268086 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term180 A P Q) = (term179 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5268087 (P : real -> Prop) (Q : real -> Prop) : (term474 P Q) = (term475 P Q).
Proof. exact (@lem5268086 real P Q). Qed.
Lemma lem5268088 (x : type1021) (s : real -> Prop) : (term476 x s) = (term477 x s).
Proof. exact (@lem5268087 (term289 s) (term449 x s)). Qed.
Lemma lem5268089 (s : real -> Prop) (b : real) : (term478 s b) = (term288 s b).
Proof. exact (eq_refl (term478 s b)). Qed.
Lemma lem5268090 (s : real -> Prop) : (term479 s) = (term289 s).
Proof. exact (fun_ext (fun b : real => @lem5268089 s b)). Qed.
Lemma lem5268091 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268092 (s : real -> Prop) : (term480 s) = (term290 s).
Proof. exact (MK_COMB (@lem5268091) (@lem5268090 s)). Qed.
Lemma lem5268093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5268094 (s : real -> Prop) : (term481 s) = (term297 s).
Proof. exact (MK_COMB (@lem5268093) (@lem5268092 s)). Qed.
Lemma lem5268095 (x : type1021) (b : real) (s : real -> Prop) : (term482 x s b) = (term448 x b s).
Proof. exact (eq_refl (term482 x s b)). Qed.
Lemma lem5268096 (x : type1021) (s : real -> Prop) : (term483 x s) = (term449 x s).
Proof. exact (fun_ext (fun b : real => @lem5268095 x b s)). Qed.
Lemma lem5268097 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268098 (x : type1021) (s : real -> Prop) : (term484 x s) = (term450 x s).
Proof. exact (MK_COMB (@lem5268097) (@lem5268096 x s)). Qed.
Lemma lem5268099 (x : type1021) (s : real -> Prop) : (term476 x s) = (term451 x s).
Proof. exact (MK_COMB (@lem5268094 s) (@lem5268098 x s)). Qed.
Lemma lem5268100 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5268101 (x : type1021) (s : real -> Prop) : (term485 x s) = (term486 x s).
Proof. exact (MK_COMB (@lem5268100) (@lem5268099 x s)). Qed.
Lemma lem5268102 (s : real -> Prop) (b : real) : (term478 s b) = (term288 s b).
Proof. exact (eq_refl (term478 s b)). Qed.
Lemma lem5268103 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5268104 (s : real -> Prop) (b : real) : (term487 s b) = (term488 s b).
Proof. exact (MK_COMB (@lem5268103) (@lem5268102 s b)). Qed.
Lemma lem5268105 (x : type1021) (b : real) (s : real -> Prop) : (term482 x s b) = (term448 x b s).
Proof. exact (eq_refl (term482 x s b)). Qed.
Lemma lem5268106 (x : type1021) (b : real) (s : real -> Prop) : (term489 x s b) = (term490 x b s).
Proof. exact (MK_COMB (@lem5268104 s b) (@lem5268105 x b s)). Qed.
Lemma lem5268107 (x : type1021) (s : real -> Prop) : (term491 x s) = (term492 x s).
Proof. exact (fun_ext (fun b : real => @lem5268106 x b s)). Qed.
Lemma lem5268108 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268109 (x : type1021) (s : real -> Prop) : (term477 x s) = (term493 x s).
Proof. exact (MK_COMB (@lem5268108) (@lem5268107 x s)). Qed.
Lemma lem5268110 (x : type1021) (s : real -> Prop) : ((term476 x s) = (term477 x s)) = ((term451 x s) = (term493 x s)).
Proof. exact (MK_COMB (@lem5268101 x s) (@lem5268109 x s)). Qed.
Lemma lem5268111 (x : type1021) (s : real -> Prop) : (term451 x s) = (term493 x s).
Proof. exact (EQ_MP (@lem5268110 x s) (@lem5268088 x s)). Qed.
Lemma lem5268114 (x : type1021) (s : real -> Prop) : (term494 x s) = (term494 x s).
Proof. exact (eq_refl (term494 x s)). Qed.
Lemma lem5268115 (x : type1021) (s : real -> Prop) : (term494 x s) = ((term451 x s) = (term493 x s)).
Proof. exact (eq_refl (term494 x s)). Qed.
Lemma lem5268116 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5268117 (x : type1021) (s : real -> Prop) : ((term494 x s) = (term494 x s)) = ((term494 x s) = ((term451 x s) = (term493 x s))).
Proof. exact (MK_COMB (@lem5268116 x s) (@lem5268115 x s)). Qed.
Lemma lem5268118 (x : type1021) (s : real -> Prop) : (term494 x s) = ((term451 x s) = (term493 x s)).
Proof. exact (eq_refl (term494 x s)). Qed.
Lemma lem5268119 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5268120 (x : type1021) (s : real -> Prop) : (term495 x s) = (term496 x s).
Proof. exact (MK_COMB (@lem5268119) (@lem5268118 x s)). Qed.
Lemma lem5268121 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term493 x s)) = ((term451 x s) = (term493 x s)).
Proof. exact (eq_refl ((term451 x s) = (term493 x s))). Qed.
Lemma lem5268122 (x : type1021) (s : real -> Prop) : ((term494 x s) = ((term451 x s) = (term493 x s))) = (((term451 x s) = (term493 x s)) = ((term451 x s) = (term493 x s))).
Proof. exact (MK_COMB (@lem5268120 x s) (@lem5268121 x s)). Qed.
Lemma lem5268123 (x : type1021) (s : real -> Prop) : ((term494 x s) = (term494 x s)) = (((term451 x s) = (term493 x s)) = ((term451 x s) = (term493 x s))).
Proof. exact (TRANS (@lem5268117 x s) (@lem5268122 x s)). Qed.
Lemma lem5268124 (x : type1021) (s : real -> Prop) : ((term451 x s) = (term493 x s)) = ((term451 x s) = (term493 x s)).
Proof. exact (EQ_MP (@lem5268123 x s) (@lem5268114 x s)). Qed.
Lemma lem5268125 (x : type1021) (s : real -> Prop) : (term451 x s) = (term493 x s).
Proof. exact (EQ_MP (@lem5268124 x s) (@lem5268111 x s)). Qed.
Lemma lem5268126 (x : type1021) (s : real -> Prop) : (term440 x s) = (term497 x s).
Proof. exact (MK_COMB (@lem5268084 x s) (@lem5268125 x s)). Qed.
Lemma lem5268128 {A : Type'} (P : A -> Prop) (Q : Prop) : (term498 A P Q) = (term499 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5268129 (P : real -> Prop) (Q : Prop) : (term500 P Q) = (term501 P Q).
Proof. exact (@lem5268128 real P Q). Qed.
Lemma lem5268130 (x : type1021) (s : real -> Prop) : (term502 x s) = (term503 x s).
Proof. exact (@lem5268129 (term471 x s) (term493 x s)). Qed.
Lemma lem5268131 (x : type1021) (s : real -> Prop) (b : real) : (term504 x s b) = (term469 x s b).
Proof. exact (eq_refl (term504 x s b)). Qed.
Lemma lem5268132 (x : type1021) (s : real -> Prop) : (term505 x s) = (term471 x s).
Proof. exact (fun_ext (fun b : real => @lem5268131 x s b)). Qed.
Lemma lem5268133 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268134 (x : type1021) (s : real -> Prop) : (term506 x s) = (term472 x s).
Proof. exact (MK_COMB (@lem5268133) (@lem5268132 x s)). Qed.
Lemma lem5268135 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5268136 (x : type1021) (s : real -> Prop) : (term507 x s) = (term473 x s).
Proof. exact (MK_COMB (@lem5268135) (@lem5268134 x s)). Qed.
Lemma lem5268137 (x : type1021) (s : real -> Prop) : (term493 x s) = (term493 x s).
Proof. exact (eq_refl (term493 x s)). Qed.
Lemma lem5268138 (x : type1021) (s : real -> Prop) : (term502 x s) = (term497 x s).
Proof. exact (MK_COMB (@lem5268136 x s) (@lem5268137 x s)). Qed.
Lemma lem5268139 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5268140 (x : type1021) (s : real -> Prop) : (term508 x s) = (term509 x s).
Proof. exact (MK_COMB (@lem5268139) (@lem5268138 x s)). Qed.
Lemma lem5268141 (x : type1021) (s : real -> Prop) (b : real) : (term504 x s b) = (term469 x s b).
Proof. exact (eq_refl (term504 x s b)). Qed.
Lemma lem5268142 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5268143 (x : type1021) (s : real -> Prop) (b : real) : (term510 x s b) = (term511 x s b).
Proof. exact (MK_COMB (@lem5268142) (@lem5268141 x s b)). Qed.
Lemma lem5268144 (x : type1021) (s : real -> Prop) : (term493 x s) = (term493 x s).
Proof. exact (eq_refl (term493 x s)). Qed.
Lemma lem5268145 (b : real) (x : type1021) (s : real -> Prop) : (term512 b x s) = (term513 b x s).
Proof. exact (MK_COMB (@lem5268143 x s b) (@lem5268144 x s)). Qed.
Lemma lem5268146 (x : type1021) (s : real -> Prop) : (term514 x s) = (term515 x s).
Proof. exact (fun_ext (fun b : real => @lem5268145 b x s)). Qed.
Lemma lem5268147 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268148 (x : type1021) (s : real -> Prop) : (term503 x s) = (term516 x s).
Proof. exact (MK_COMB (@lem5268147) (@lem5268146 x s)). Qed.
Lemma lem5268149 (x : type1021) (s : real -> Prop) : ((term502 x s) = (term503 x s)) = ((term497 x s) = (term516 x s)).
Proof. exact (MK_COMB (@lem5268140 x s) (@lem5268148 x s)). Qed.
Lemma lem5268150 (x : type1021) (s : real -> Prop) : (term497 x s) = (term516 x s).
Proof. exact (EQ_MP (@lem5268149 x s) (@lem5268130 x s)). Qed.
Lemma lem5268152 {A : Type'} (P : Prop) (Q : A -> Prop) : (term457 A P Q) = (term458 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5268153 (P : Prop) (Q : real -> Prop) : (term459 P Q) = (term460 P Q).
Proof. exact (@lem5268152 real P Q). Qed.
Lemma lem5268154 (b : real) (x : type1021) (s : real -> Prop) : (term517 b x s) = (term518 b x s).
Proof. exact (@lem5268153 (term469 x s b) (term492 x s)). Qed.
Lemma lem5268155 (x : type1021) (b : real) (s : real -> Prop) : (term519 x s b) = (term490 x b s).
Proof. exact (eq_refl (term519 x s b)). Qed.
Lemma lem5268156 (x : type1021) (s : real -> Prop) : (term520 x s) = (term492 x s).
Proof. exact (fun_ext (fun b : real => @lem5268155 x b s)). Qed.
Lemma lem5268157 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268158 (x : type1021) (s : real -> Prop) : (term521 x s) = (term493 x s).
Proof. exact (MK_COMB (@lem5268157) (@lem5268156 x s)). Qed.
Lemma lem5268159 (x : type1021) (s : real -> Prop) (b : real) : (term511 x s b) = (term511 x s b).
Proof. exact (eq_refl (term511 x s b)). Qed.
Lemma lem5268160 (b : real) (x : type1021) (s : real -> Prop) : (term517 b x s) = (term513 b x s).
Proof. exact (MK_COMB (@lem5268159 x s b) (@lem5268158 x s)). Qed.
Lemma lem5268161 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5268162 (b : real) (x : type1021) (s : real -> Prop) : (term522 b x s) = (term523 b x s).
Proof. exact (MK_COMB (@lem5268161) (@lem5268160 b x s)). Qed.
Lemma lem5268163 (x : type1021) (b' : real) (s : real -> Prop) : (term519 x s b') = (term490 x b' s).
Proof. exact (eq_refl (term519 x s b')). Qed.
Lemma lem5268164 (x : type1021) (s : real -> Prop) (b : real) : (term511 x s b) = (term511 x s b).
Proof. exact (eq_refl (term511 x s b)). Qed.
Lemma lem5268165 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term524 b x s b') = (term525 b x b' s).
Proof. exact (MK_COMB (@lem5268164 x s b) (@lem5268163 x b' s)). Qed.
Lemma lem5268166 (b : real) (x : type1021) (s : real -> Prop) : (term526 b x s) = (term527 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5268165 b x b' s)). Qed.
Lemma lem5268167 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268168 (b : real) (x : type1021) (s : real -> Prop) : (term518 b x s) = (term528 b x s).
Proof. exact (MK_COMB (@lem5268167) (@lem5268166 b x s)). Qed.
Lemma lem5268169 (b : real) (x : type1021) (s : real -> Prop) : ((term517 b x s) = (term518 b x s)) = ((term513 b x s) = (term528 b x s)).
Proof. exact (MK_COMB (@lem5268162 b x s) (@lem5268168 b x s)). Qed.
Lemma lem5268170 (b : real) (x : type1021) (s : real -> Prop) : (term513 b x s) = (term528 b x s).
Proof. exact (EQ_MP (@lem5268169 b x s) (@lem5268154 b x s)). Qed.
Lemma lem5268171 (x : type1021) (s : real -> Prop) : (term515 x s) = (term529 x s).
Proof. exact (fun_ext (fun b : real => @lem5268170 b x s)). Qed.
Lemma lem5268172 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268173 (x : type1021) (s : real -> Prop) : (term516 x s) = (term530 x s).
Proof. exact (MK_COMB (@lem5268172) (@lem5268171 x s)). Qed.
Lemma lem5268174 (x : type1021) (s : real -> Prop) : (term497 x s) = (term530 x s).
Proof. exact (TRANS (@lem5268150 x s) (@lem5268173 x s)). Qed.
Lemma lem5268175 (x : type1021) (s : real -> Prop) : (term440 x s) = (term530 x s).
Proof. exact (TRANS (@lem5268126 x s) (@lem5268174 x s)). Qed.
Lemma lem5268176 (x : type1021) : (term442 x) = (term531 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5268175 x s)). Qed.
Lemma lem5268177 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5268178 (x : type1021) : (term444 x) = (term532 x).
Proof. exact (MK_COMB (@lem5268177) (@lem5268176 x)). Qed.
Lemma lem5268195 (x : type1021) (b' : real) (s : real -> Prop) : (term448 x b' s) = (term533 x b' s).
Proof. exact (@lem19699 (term534 x b' s) (term535 x s b') (term27 b' s)). Qed.
Lemma lem5268204 (s : real -> Prop) (b' : real) : (term488 s b') = (term488 s b').
Proof. exact (eq_refl (term488 s b')). Qed.
Lemma lem5268205 (x : type1021) (b' : real) (s : real -> Prop) : (term490 x b' s) = (term536 x b' s).
Proof. exact (MK_COMB (@lem5268204 s b') (@lem5268195 x b' s)). Qed.
Lemma lem5268222 (x : type1021) (s : real -> Prop) (b : real) : (term469 x s b) = (term537 x s b).
Proof. exact (@lem19490 (term534 x b s) (s = (@EMPTY real)) (term535 x s b)). Qed.
Lemma lem5268223 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5268224 (x : type1021) (s : real -> Prop) (b : real) : (term511 x s b) = (term538 x s b).
Proof. exact (MK_COMB (@lem5268223) (@lem5268222 x s b)). Qed.
Lemma lem5268225 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term525 b x b' s) = (term539 b x b' s).
Proof. exact (MK_COMB (@lem5268224 x s b) (@lem5268205 x b' s)). Qed.
Lemma lem5268226 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term539 b x b' s) = (term540 b x b' s).
Proof. exact (@lem19490 (term288 s b') (term537 x s b) (term533 x b' s)). Qed.
Lemma lem5268227 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term541 b x b' s) = (term542 b x b' s).
Proof. exact (@lem19490 (term543 x b' s) (term537 x s b) (term544 x b' s)). Qed.
Lemma lem5268234 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term545 b x b' s) = (term546 b x b' s).
Proof. exact (@lem19699 (term547 x b s) (term548 x s b) (term544 x b' s)). Qed.
Lemma lem5268241 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term549 b x b' s) = (term550 b x b' s).
Proof. exact (@lem19699 (term547 x b s) (term548 x s b) (term543 x b' s)). Qed.
Lemma lem5268242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5268243 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term551 b x b' s) = (term552 b x b' s).
Proof. exact (MK_COMB (@lem5268242) (@lem5268241 b x b' s)). Qed.
Lemma lem5268244 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term542 b x b' s) = (term553 b x b' s).
Proof. exact (MK_COMB (@lem5268243 b x b' s) (@lem5268234 b x b' s)). Qed.
Lemma lem5268245 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term541 b x b' s) = (term553 b x b' s).
Proof. exact (TRANS (@lem5268227 b x b' s) (@lem5268244 b x b' s)). Qed.
Lemma lem5268252 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term554 x b s b') = (term555 x b s b').
Proof. exact (@lem19699 (term547 x b s) (term548 x s b) (term288 s b')). Qed.
Lemma lem5268253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5268254 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term556 x b s b') = (term557 x b s b').
Proof. exact (MK_COMB (@lem5268253) (@lem5268252 x b s b')). Qed.
Lemma lem5268255 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term540 b x b' s) = (term558 b x b' s).
Proof. exact (MK_COMB (@lem5268254 x b s b') (@lem5268245 b x b' s)). Qed.
Lemma lem5268256 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term539 b x b' s) = (term558 b x b' s).
Proof. exact (TRANS (@lem5268226 b x b' s) (@lem5268255 b x b' s)). Qed.
Lemma lem5268257 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term525 b x b' s) = (term558 b x b' s).
Proof. exact (TRANS (@lem5268225 b x b' s) (@lem5268256 b x b' s)). Qed.
Lemma lem5268258 (b : real) (x : type1021) (s : real -> Prop) : (term527 b x s) = (term559 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5268257 b x b' s)). Qed.
Lemma lem5268259 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268260 (b : real) (x : type1021) (s : real -> Prop) : (term528 b x s) = (term560 b x s).
Proof. exact (MK_COMB (@lem5268259) (@lem5268258 b x s)). Qed.
Lemma lem5268261 (x : type1021) (s : real -> Prop) : (term529 x s) = (term561 x s).
Proof. exact (fun_ext (fun b : real => @lem5268260 b x s)). Qed.
Lemma lem5268262 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268263 (x : type1021) (s : real -> Prop) : (term530 x s) = (term562 x s).
Proof. exact (MK_COMB (@lem5268262) (@lem5268261 x s)). Qed.
Lemma lem5268264 (x : type1021) : (term531 x) = (term563 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5268263 x s)). Qed.
Lemma lem5268265 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5268266 (x : type1021) : (term532 x) = (term564 x).
Proof. exact (MK_COMB (@lem5268265) (@lem5268264 x)). Qed.
Lemma lem5268267 (x : type1021) : (term444 x) = (term564 x).
Proof. exact (TRANS (@lem5268178 x) (@lem5268266 x)). Qed.
Lemma lem5268268 (x : type1021) (h1 : term444 x) : term564 x.
Proof. exact (EQ_MP (@lem5268267 x) (@lem5267937 x h1)). Qed.
Lemma lem5268288 (s : real -> Prop) (a : real) (x : real) : (term73 s a x) = (term73 s a x).
Proof. exact (eq_refl (term73 s a x)). Qed.
Lemma lem5268289 (s : real -> Prop) (a : real) : (term74 s a) = (term74 s a).
Proof. exact (fun_ext (fun x : real => @lem5268288 s a x)). Qed.
Lemma lem5268290 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268292 (s : real -> Prop) (a : real) : (term75 s a) = (term75 s a).
Proof. exact (MK_COMB (@lem5268290) (@lem5268289 s a)). Qed.
Lemma lem5268293 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term75 s a.
Proof. exact (EQ_MP (@lem5268292 s a) (@lem5268034 y a s b h1)). Qed.
Lemma lem5268308 {A : Type'} (P : A -> Prop) (Q : Prop) : (term498 A P Q) = (term499 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5268309 (P : real -> Prop) (Q : Prop) : (term500 P Q) = (term501 P Q).
Proof. exact (@lem5268308 real P Q). Qed.
Lemma lem5268310 (s : real -> Prop) : (term565 s) = (term566 s).
Proof. exact (@lem5268309 (term163 s) (term47 s)). Qed.
Lemma lem5268311 (x : real) (s : real -> Prop) : (term567 s x) = (term161 x s).
Proof. exact (eq_refl (term567 s x)). Qed.
Lemma lem5268312 (s : real -> Prop) : (term568 s) = (term163 s).
Proof. exact (fun_ext (fun x : real => @lem5268311 x s)). Qed.
Lemma lem5268313 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268314 (s : real -> Prop) : (term569 s) = (term164 s).
Proof. exact (MK_COMB (@lem5268313) (@lem5268312 s)). Qed.
Lemma lem5268315 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5268316 (s : real -> Prop) : (term570 s) = (term167 s).
Proof. exact (MK_COMB (@lem5268315) (@lem5268314 s)). Qed.
Lemma lem5268317 (s : real -> Prop) : (term47 s) = (term47 s).
Proof. exact (eq_refl (term47 s)). Qed.
Lemma lem5268318 (s : real -> Prop) : (term565 s) = (term169 s).
Proof. exact (MK_COMB (@lem5268316 s) (@lem5268317 s)). Qed.
Lemma lem5268319 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5268320 (s : real -> Prop) : (term571 s) = (term572 s).
Proof. exact (MK_COMB (@lem5268319) (@lem5268318 s)). Qed.
Lemma lem5268321 (x : real) (s : real -> Prop) : (term567 s x) = (term161 x s).
Proof. exact (eq_refl (term567 s x)). Qed.
Lemma lem5268322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5268323 (x : real) (s : real -> Prop) : (term573 s x) = (term574 x s).
Proof. exact (MK_COMB (@lem5268322) (@lem5268321 x s)). Qed.
Lemma lem5268324 (s : real -> Prop) : (term47 s) = (term47 s).
Proof. exact (eq_refl (term47 s)). Qed.
Lemma lem5268325 (x : real) (s : real -> Prop) : (term575 x s) = (term576 x s).
Proof. exact (MK_COMB (@lem5268323 x s) (@lem5268324 s)). Qed.
Lemma lem5268326 (s : real -> Prop) : (term577 s) = (term578 s).
Proof. exact (fun_ext (fun x : real => @lem5268325 x s)). Qed.
Lemma lem5268327 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268328 (s : real -> Prop) : (term566 s) = (term579 s).
Proof. exact (MK_COMB (@lem5268327) (@lem5268326 s)). Qed.
Lemma lem5268329 (s : real -> Prop) : ((term565 s) = (term566 s)) = ((term169 s) = (term579 s)).
Proof. exact (MK_COMB (@lem5268320 s) (@lem5268328 s)). Qed.
Lemma lem5268330 (s : real -> Prop) : (term169 s) = (term579 s).
Proof. exact (EQ_MP (@lem5268329 s) (@lem5268310 s)). Qed.
Lemma lem5268331 : term186 = term580.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5268330 s)). Qed.
Lemma lem5268332 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5268333 : term201 = term581.
Proof. exact (MK_COMB (@lem5268332) (@lem5268331)). Qed.
Lemma lem5268340 (x : real) (s : real -> Prop) : (term576 x s) = (term576 x s).
Proof. exact (eq_refl (term576 x s)). Qed.
Lemma lem5268341 (s : real -> Prop) : (term578 s) = (term578 s).
Proof. exact (fun_ext (fun x : real => @lem5268340 x s)). Qed.
Lemma lem5268342 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5268343 (s : real -> Prop) : (term579 s) = (term579 s).
Proof. exact (MK_COMB (@lem5268342) (@lem5268341 s)). Qed.
Lemma lem5268344 : term580 = term580.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5268343 s)). Qed.
Lemma lem5268345 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5268346 : term581 = term581.
Proof. exact (MK_COMB (@lem5268345) (@lem5268344)). Qed.
Lemma lem5268347 : term201 = term581.
Proof. exact (TRANS (@lem5268333) (@lem5268346)). Qed.
Lemma lem5268348 (x' : type1023) (h1 : term263 x') : term581.
Proof. exact (EQ_MP (@lem5268347) (@lem5268036 x' h1)). Qed.
Lemma lem5268349 (_68950 : real) (h1 : term58) : term582 _68950.
Proof. exact (@lem5268062 h1 _68950). Qed.
Lemma lem5268350 (_68950 : real) : (term582 _68950) = (term152 _68950).
Proof. exact (eq_refl (term582 _68950)). Qed.
Lemma lem5268351 (_68950 : real) (h1 : term58) : term152 _68950.
Proof. exact (EQ_MP (@lem5268350 _68950) (@lem5268349 _68950 h1)). Qed.
Lemma lem5268352 (_68950 : real) (_68951 : real) (h1 : term58) : term583 _68950 _68951.
Proof. exact (@lem5268351 _68950 h1 _68951). Qed.
Lemma lem5268353 (_68951 : real) (_68950 : real) : (term583 _68950 _68951) = (term150 _68951 _68950).
Proof. exact (eq_refl (term583 _68950 _68951)). Qed.
Lemma lem5268354 (_68951 : real) (_68950 : real) (h1 : term58) : term150 _68951 _68950.
Proof. exact (EQ_MP (@lem5268353 _68951 _68950) (@lem5268352 _68950 _68951 h1)). Qed.
Lemma lem5268355 (_68951 : real) (_68950 : real) (_68952 : real) (h1 : term58) : term584 _68951 _68950 _68952.
Proof. exact (@lem5268354 _68951 _68950 h1 _68952). Qed.
Lemma lem5268356 (_68951 : real) (_68950 : real) (_68952 : real) : (term584 _68951 _68950 _68952) = (term147 _68951 _68950 _68952).
Proof. exact (eq_refl (term584 _68951 _68950 _68952)). Qed.
Lemma lem5268357 (_68951 : real) (_68950 : real) (_68952 : real) (h1 : term58) : term147 _68951 _68950 _68952.
Proof. exact (EQ_MP (@lem5268356 _68951 _68950 _68952) (@lem5268355 _68951 _68950 _68952 h1)). Qed.
Lemma lem5268358 (_68953 : real -> Prop) (x : type1021) (h1 : term444 x) : term585 x _68953.
Proof. exact (@lem5268268 x h1 _68953). Qed.
Lemma lem5268359 (x : type1021) (_68953 : real -> Prop) : (term585 x _68953) = (term562 x _68953).
Proof. exact (eq_refl (term585 x _68953)). Qed.
Lemma lem5268360 (_68953 : real -> Prop) (x : type1021) (h1 : term444 x) : term562 x _68953.
Proof. exact (EQ_MP (@lem5268359 x _68953) (@lem5268358 _68953 x h1)). Qed.
Lemma lem5268361 (_68953 : real -> Prop) (_68954 : real) (x : type1021) (h1 : term444 x) : term586 x _68953 _68954.
Proof. exact (@lem5268360 _68953 x h1 _68954). Qed.
Lemma lem5268362 (_68954 : real) (x : type1021) (_68953 : real -> Prop) : (term586 x _68953 _68954) = (term560 _68954 x _68953).
Proof. exact (eq_refl (term586 x _68953 _68954)). Qed.
Lemma lem5268363 (_68954 : real) (_68953 : real -> Prop) (x : type1021) (h1 : term444 x) : term560 _68954 x _68953.
Proof. exact (EQ_MP (@lem5268362 _68954 x _68953) (@lem5268361 _68953 _68954 x h1)). Qed.
Lemma lem5268364 (_68954 : real) (_68953 : real -> Prop) (_68955 : real) (x : type1021) (h1 : term444 x) : term587 _68954 x _68953 _68955.
Proof. exact (@lem5268363 _68954 _68953 x h1 _68955). Qed.
Lemma lem5268365 (_68954 : real) (x : type1021) (_68955 : real) (_68953 : real -> Prop) : (term587 _68954 x _68953 _68955) = (term558 _68954 x _68955 _68953).
Proof. exact (eq_refl (term587 _68954 x _68953 _68955)). Qed.
Lemma lem5268366 (_68954 : real) (_68955 : real) (_68953 : real -> Prop) (x : type1021) (h1 : term444 x) : term558 _68954 x _68955 _68953.
Proof. exact (EQ_MP (@lem5268365 _68954 x _68955 _68953) (@lem5268364 _68954 _68953 _68955 x h1)). Qed.
Lemma lem5268367 (_68956 : real) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term588 s a _68956.
Proof. exact (@lem5268293 y a s b h1 _68956). Qed.
Lemma lem5268368 (s : real -> Prop) (a : real) (_68956 : real) : (term588 s a _68956) = (term73 s a _68956).
Proof. exact (eq_refl (term588 s a _68956)). Qed.
Lemma lem5268373 (_68958 : real -> Prop) (x' : type1023) (h1 : term263 x') : term589 _68958.
Proof. exact (@lem5268348 x' h1 _68958). Qed.
Lemma lem5268374 (_68958 : real -> Prop) : (term589 _68958) = (term579 _68958).
Proof. exact (eq_refl (term589 _68958)). Qed.
Lemma lem5268375 (_68958 : real -> Prop) (x' : type1023) (h1 : term263 x') : term579 _68958.
Proof. exact (EQ_MP (@lem5268374 _68958) (@lem5268373 _68958 x' h1)). Qed.
Lemma lem5268376 (_68958 : real -> Prop) (_68959 : real) (x' : type1023) (h1 : term263 x') : term590 _68958 _68959.
Proof. exact (@lem5268375 _68958 x' h1 _68959). Qed.
Lemma lem5268377 (_68959 : real) (_68958 : real -> Prop) : (term590 _68958 _68959) = (term576 _68959 _68958).
Proof. exact (eq_refl (term590 _68958 _68959)). Qed.
Lemma lem5268380 (_68954 : real) (_68953 : real -> Prop) (_68955 : real) (x : type1021) (h1 : term444 x) : term555 x _68954 _68953 _68955.
Proof. exact (proj1 (@lem5268366 _68954 _68955 _68953 x h1)). Qed.
Lemma lem5268387 (_68954 : real) (_68953 : real -> Prop) (_68955 : real) (x : type1021) (h1 : term444 x) : term591 x _68954 _68953 _68955.
Proof. exact (proj2 (@lem5268380 _68954 _68953 _68955 x h1)). Qed.
Lemma lem5268388 (_68954 : real) (_68953 : real -> Prop) (_68955 : real) (x : type1021) (h1 : term444 x) : term592 x _68954 _68953 _68955.
Proof. exact (proj1 (@lem5268380 _68954 _68953 _68955 x h1)). Qed.
Lemma lem5268399 (_68951 : real) (_68950 : real) (_68952 : real) : (term147 _68951 _68950 _68952) = (term593 _68951 _68950 _68952).
Proof. exact (@lem5266214 (term594 _68950 _68951) (term594 _68951 _68952) (real_le _68950 _68952)). Qed.
Lemma lem5268400 (_68951 : real) (_68950 : real) (_68952 : real) (h1 : term58) : term593 _68951 _68950 _68952.
Proof. exact (EQ_MP (@lem5268399 _68951 _68950 _68952) (@lem5268357 _68951 _68950 _68952 h1)). Qed.
Lemma lem5268402 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term78 s b.
Proof. exact (proj2 (@lem5268029 y a s b h1)). Qed.
Lemma lem5268412 (_68956 : real) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term73 s a _68956.
Proof. exact (EQ_MP (@lem5268368 s a _68956) (@lem5268367 _68956 y a s b h1)). Qed.
Lemma lem5268424 (_68959 : real) (_68958 : real -> Prop) (x' : type1023) (h1 : term263 x') : term576 _68959 _68958.
Proof. exact (EQ_MP (@lem5268377 _68959 _68958) (@lem5268376 _68958 _68959 x' h1)). Qed.
Lemma lem5268503 (x : type1021) (_68954 : real) (_68953 : real -> Prop) (_68955 : real) : (term592 x _68954 _68953 _68955) = (term595 x _68954 _68953 _68955).
Proof. exact (@lem5266214 (_68953 = (@EMPTY real)) (term534 x _68954 _68953) (term288 _68953 _68955)). Qed.
Lemma lem5268504 (_68954 : real) (_68953 : real -> Prop) (_68955 : real) (x : type1021) (h1 : term444 x) : term595 x _68954 _68953 _68955.
Proof. exact (EQ_MP (@lem5268503 x _68954 _68953 _68955) (@lem5268388 _68954 _68953 _68955 x h1)). Qed.
Lemma lem5268519 (x : type1021) (_68954 : real) (_68953 : real -> Prop) (_68955 : real) : (term591 x _68954 _68953 _68955) = (term596 x _68954 _68953 _68955).
Proof. exact (@lem5266214 (_68953 = (@EMPTY real)) (term535 x _68953 _68954) (term288 _68953 _68955)). Qed.
Lemma lem5268520 (_68954 : real) (_68953 : real -> Prop) (_68955 : real) (x : type1021) (h1 : term444 x) : term596 x _68954 _68953 _68955.
Proof. exact (EQ_MP (@lem5268519 x _68954 _68953 _68955) (@lem5268387 _68954 _68953 _68955 x h1)). Qed.
Lemma lem5268595 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : @IN real y s.
Proof. exact (proj1 (@lem5268031 y a s b h1)). Qed.
Lemma lem5268596 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term597 y s.
Proof. exact (fun h0 : term161 y s => @lem5268595 y a s b h1). Qed.
Lemma lem5268598 (p : Prop) : (term598 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5268599 (y : real) (s : real -> Prop) : (term597 y s) = (@IN real y s).
Proof. exact (@lem5268598 (@IN real y s)). Qed.
Lemma lem5268600 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : @IN real y s.
Proof. exact (EQ_MP (@lem5268599 y s) (@lem5268596 y a s b h1)). Qed.
Lemma lem5268606 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5268607 (_68959 : real) (_68958 : real -> Prop) : (term576 _68959 _68958) = (term599 _68959 _68958).
Proof. exact (@lem5268606 (term47 _68958) (term161 _68959 _68958)). Qed.
Lemma lem5268615 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5268616 (_68959 : real) (_68958 : real -> Prop) : (term600 _68959 _68958) = (term601 _68959 _68958).
Proof. exact (MK_COMB (@lem5268615) (@lem5268607 _68959 _68958)). Qed.
Lemma lem5268624 (_68959 : real) (_68958 : real -> Prop) : (term599 _68959 _68958) = (term599 _68959 _68958).
Proof. exact (eq_refl (term599 _68959 _68958)). Qed.
Lemma lem5268625 (_68959 : real) (_68958 : real -> Prop) : ((term576 _68959 _68958) = (term599 _68959 _68958)) = ((term599 _68959 _68958) = (term599 _68959 _68958)).
Proof. exact (MK_COMB (@lem5268616 _68959 _68958) (@lem5268624 _68959 _68958)). Qed.
Lemma lem5268627 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5268628 (x : Prop) : (x = x) = True.
Proof. exact (@lem5268627 Prop x). Qed.
Lemma lem5268629 (_68959 : real) (_68958 : real -> Prop) : ((term599 _68959 _68958) = (term599 _68959 _68958)) = True.
Proof. exact (@lem5268628 (term599 _68959 _68958)). Qed.
Lemma lem5268630 (_68959 : real) (_68958 : real -> Prop) : ((term576 _68959 _68958) = (term599 _68959 _68958)) = True.
Proof. exact (TRANS (@lem5268625 _68959 _68958) (@lem5268629 _68959 _68958)). Qed.
Lemma lem5268631 (_68959 : real) (_68958 : real -> Prop) : True = ((term576 _68959 _68958) = (term599 _68959 _68958)).
Proof. exact (SYM (@lem5268630 _68959 _68958)). Qed.
Lemma lem5268632 (_68959 : real) (_68958 : real -> Prop) : (term576 _68959 _68958) = (term599 _68959 _68958).
Proof. exact (EQ_MP (@lem5268631 _68959 _68958) (@lem0)). Qed.
Lemma lem5268633 (_68959 : real) (_68958 : real -> Prop) (x' : type1023) (h1 : term263 x') : term599 _68959 _68958.
Proof. exact (EQ_MP (@lem5268632 _68959 _68958) (@lem5268424 _68959 _68958 x' h1)). Qed.
Lemma lem5268635 (b : Prop) (a : Prop) : (a \/ b) = (term602 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5268636 (_68959 : real) (_68958 : real -> Prop) : (term599 _68959 _68958) = (term603 _68959 _68958).
Proof. exact (@lem5268635 (term161 _68959 _68958) (term47 _68958)). Qed.
Lemma lem5268638 (a : Prop) : (term604 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5268639 (_68959 : real) (_68958 : real -> Prop) : (term605 _68959 _68958) = (@IN real _68959 _68958).
Proof. exact (@lem5268638 (@IN real _68959 _68958)). Qed.
Lemma lem5268640 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5268641 (_68959 : real) (_68958 : real -> Prop) : (term606 _68959 _68958) = (term607 _68959 _68958).
Proof. exact (MK_COMB (@lem5268640) (@lem5268639 _68959 _68958)). Qed.
Lemma lem5268642 (_68958 : real -> Prop) : (term47 _68958) = (term47 _68958).
Proof. exact (eq_refl (term47 _68958)). Qed.
Lemma lem5268643 (_68959 : real) (_68958 : real -> Prop) : (term603 _68959 _68958) = (term608 _68959 _68958).
Proof. exact (MK_COMB (@lem5268641 _68959 _68958) (@lem5268642 _68958)). Qed.
Lemma lem5268644 (_68959 : real) (_68958 : real -> Prop) : (term599 _68959 _68958) = (term608 _68959 _68958).
Proof. exact (TRANS (@lem5268636 _68959 _68958) (@lem5268643 _68959 _68958)). Qed.
Lemma lem5268647 (_68959 : real) (_68958 : real -> Prop) (x' : type1023) (h1 : term263 x') : term608 _68959 _68958.
Proof. exact (EQ_MP (@lem5268644 _68959 _68958) (@lem5268633 _68959 _68958 x' h1)). Qed.
Lemma lem5268648 (y : real) (s : real -> Prop) (x' : type1023) (h1 : term263 x') : term608 y s.
Proof. exact (@lem5268647 y s x' h1). Qed.
Lemma lem5268651 (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term263 x') (h2 : term82 y a s b) : term47 s.
Proof. exact (@lem5268648 y s x' h1 (@lem5268600 y a s b h2)). Qed.
Lemma lem5268652 (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term263 x') (h2 : term82 y a s b) : term609 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5268651 x' y a s b h1 h2). Qed.
Lemma lem5268654 (p : Prop) : (term610 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5268655 (s : real -> Prop) : (term609 s) = (term47 s).
Proof. exact (@lem5268654 (s = (@EMPTY real))). Qed.
Lemma lem5268656 (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term263 x') (h2 : term82 y a s b) : term47 s.
Proof. exact (EQ_MP (@lem5268655 s) (@lem5268652 x' y a s b h1 h2)). Qed.
Lemma lem5268658 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : @IN real y s.
Proof. exact (proj1 (@lem5268031 y a s b h1)). Qed.
Lemma lem5268659 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term597 y s.
Proof. exact (fun h0 : term161 y s => @lem5268658 y a s b h1). Qed.
Lemma lem5268661 (p : Prop) : (term598 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5268662 (y : real) (s : real -> Prop) : (term597 y s) = (@IN real y s).
Proof. exact (@lem5268661 (@IN real y s)). Qed.
Lemma lem5268663 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : @IN real y s.
Proof. exact (EQ_MP (@lem5268662 y s) (@lem5268659 y a s b h1)). Qed.
Lemma lem5268665 (_68959 : real) (_68958 : real -> Prop) (x' : type1023) (h1 : term263 x') : term608 _68959 _68958.
Proof. exact (EQ_MP (@lem5268644 _68959 _68958) (@lem5268633 _68959 _68958 x' h1)). Qed.
Lemma lem5268666 (y : real) (s : real -> Prop) (x' : type1023) (h1 : term263 x') : term608 y s.
Proof. exact (@lem5268665 y s x' h1). Qed.
Lemma lem5268669 (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term263 x') (h2 : term82 y a s b) : term47 s.
Proof. exact (@lem5268666 y s x' h1 (@lem5268663 y a s b h2)). Qed.
Lemma lem5268670 (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term263 x') (h2 : term82 y a s b) : term609 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5268669 x' y a s b h1 h2). Qed.
Lemma lem5268672 (p : Prop) : (term610 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5268673 (s : real -> Prop) : (term609 s) = (term47 s).
Proof. exact (@lem5268672 (s = (@EMPTY real))). Qed.
Lemma lem5268674 (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term263 x') (h2 : term82 y a s b) : term47 s.
Proof. exact (EQ_MP (@lem5268673 s) (@lem5268670 x' y a s b h1 h2)). Qed.
Lemma lem5268676 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : @IN real y s.
Proof. exact (proj1 (@lem5268031 y a s b h1)). Qed.
Lemma lem5268677 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term597 y s.
Proof. exact (fun h0 : term161 y s => @lem5268676 y a s b h1). Qed.
Lemma lem5268679 (p : Prop) : (term598 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5268680 (y : real) (s : real -> Prop) : (term597 y s) = (@IN real y s).
Proof. exact (@lem5268679 (@IN real y s)). Qed.
Lemma lem5268681 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : @IN real y s.
Proof. exact (EQ_MP (@lem5268680 y s) (@lem5268677 y a s b h1)). Qed.
Lemma lem5268684 (s : real -> Prop) (y : real) (h1 : term78 s y) : term78 s y.
Proof. exact (h1). Qed.
Lemma lem5268685 (s : real -> Prop) (y : real) (h1 : term78 s y) : term611 s y.
Proof. exact (fun h0 : term59 s y => @lem5268684 s y h1). Qed.
Lemma lem5268687 (p : Prop) : (term610 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5268688 (s : real -> Prop) (y : real) : (term611 s y) = (term78 s y).
Proof. exact (@lem5268687 (term59 s y)). Qed.
Lemma lem5268689 (s : real -> Prop) (y : real) (h1 : term78 s y) : term78 s y.
Proof. exact (EQ_MP (@lem5268688 s y) (@lem5268685 s y h1)). Qed.
Lemma lem5268717 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5268718 (_68955 : real) (_68953 : real -> Prop) : (term288 _68953 _68955) = (term612 _68955 _68953).
Proof. exact (@lem5268717 (term59 _68953 _68955) (term161 _68955 _68953)). Qed.
Lemma lem5268724 (x : type1021) (_68954 : real) (_68953 : real -> Prop) : (term613 x _68954 _68953) = (term613 x _68954 _68953).
Proof. exact (eq_refl (term613 x _68954 _68953)). Qed.
Lemma lem5268725 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : (term614 x _68954 _68953 _68955) = (term615 x _68954 _68955 _68953).
Proof. exact (MK_COMB (@lem5268724 x _68954 _68953) (@lem5268718 _68955 _68953)). Qed.
Lemma lem5268736 (_68953 : real -> Prop) : (term284 _68953) = (term284 _68953).
Proof. exact (eq_refl (term284 _68953)). Qed.
Lemma lem5268737 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : (term595 x _68954 _68953 _68955) = (term616 x _68954 _68955 _68953).
Proof. exact (MK_COMB (@lem5268736 _68953) (@lem5268725 x _68954 _68955 _68953)). Qed.
Lemma lem5268748 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5268749 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : (term617 x _68954 _68953 _68955) = (term618 x _68954 _68955 _68953).
Proof. exact (MK_COMB (@lem5268748) (@lem5268737 x _68954 _68955 _68953)). Qed.
Lemma lem5268753 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5268754 (x : type1021) (_68954 : real) (_68953 : real -> Prop) (_68955 : real) : (term619 x _68954 _68953 _68955) = (term595 x _68954 _68953 _68955).
Proof. exact (@lem5268753 (_68953 = (@EMPTY real)) (term534 x _68954 _68953) (term288 _68953 _68955)). Qed.
Lemma lem5268780 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5268781 (_68955 : real) (_68953 : real -> Prop) : (term288 _68953 _68955) = (term612 _68955 _68953).
Proof. exact (@lem5268780 (term59 _68953 _68955) (term161 _68955 _68953)). Qed.
Lemma lem5268787 (x : type1021) (_68954 : real) (_68953 : real -> Prop) : (term613 x _68954 _68953) = (term613 x _68954 _68953).
Proof. exact (eq_refl (term613 x _68954 _68953)). Qed.
Lemma lem5268788 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : (term614 x _68954 _68953 _68955) = (term615 x _68954 _68955 _68953).
Proof. exact (MK_COMB (@lem5268787 x _68954 _68953) (@lem5268781 _68955 _68953)). Qed.
Lemma lem5268799 (_68953 : real -> Prop) : (term284 _68953) = (term284 _68953).
Proof. exact (eq_refl (term284 _68953)). Qed.
Lemma lem5268800 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : (term595 x _68954 _68953 _68955) = (term616 x _68954 _68955 _68953).
Proof. exact (MK_COMB (@lem5268799 _68953) (@lem5268788 x _68954 _68955 _68953)). Qed.
Lemma lem5268811 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : (term619 x _68954 _68953 _68955) = (term616 x _68954 _68955 _68953).
Proof. exact (TRANS (@lem5268754 x _68954 _68953 _68955) (@lem5268800 x _68954 _68955 _68953)). Qed.
Lemma lem5268812 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : ((term595 x _68954 _68953 _68955) = (term619 x _68954 _68953 _68955)) = ((term616 x _68954 _68955 _68953) = (term616 x _68954 _68955 _68953)).
Proof. exact (MK_COMB (@lem5268749 x _68954 _68955 _68953) (@lem5268811 x _68954 _68955 _68953)). Qed.
Lemma lem5268814 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5268815 (x : Prop) : (x = x) = True.
Proof. exact (@lem5268814 Prop x). Qed.
Lemma lem5268816 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : ((term616 x _68954 _68955 _68953) = (term616 x _68954 _68955 _68953)) = True.
Proof. exact (@lem5268815 (term616 x _68954 _68955 _68953)). Qed.
Lemma lem5268817 (x : type1021) (_68954 : real) (_68953 : real -> Prop) (_68955 : real) : ((term595 x _68954 _68953 _68955) = (term619 x _68954 _68953 _68955)) = True.
Proof. exact (TRANS (@lem5268812 x _68954 _68955 _68953) (@lem5268816 x _68954 _68955 _68953)). Qed.
Lemma lem5268818 (x : type1021) (_68954 : real) (_68953 : real -> Prop) (_68955 : real) : True = ((term595 x _68954 _68953 _68955) = (term619 x _68954 _68953 _68955)).
Proof. exact (SYM (@lem5268817 x _68954 _68953 _68955)). Qed.
Lemma lem5268819 (x : type1021) (_68954 : real) (_68953 : real -> Prop) (_68955 : real) : (term595 x _68954 _68953 _68955) = (term619 x _68954 _68953 _68955).
Proof. exact (EQ_MP (@lem5268818 x _68954 _68953 _68955) (@lem0)). Qed.
Lemma lem5268820 (_68954 : real) (_68953 : real -> Prop) (_68955 : real) (x : type1021) (h1 : term444 x) : term619 x _68954 _68953 _68955.
Proof. exact (EQ_MP (@lem5268819 x _68954 _68953 _68955) (@lem5268504 _68954 _68953 _68955 x h1)). Qed.
Lemma lem5268822 (b : Prop) (a : Prop) : (a \/ b) = (term602 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5268823 (_68955 : real) (x : type1021) (_68954 : real) (_68953 : real -> Prop) : (term619 x _68954 _68953 _68955) = (term620 _68955 x _68954 _68953).
Proof. exact (@lem5268822 (term621 _68953 _68955) (term534 x _68954 _68953)). Qed.
Lemma lem5268825 (a : Prop) (b : Prop) : (term622 a b) = (term623 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5268826 (_68953 : real -> Prop) (_68955 : real) : (term624 _68953 _68955) = (term625 _68953 _68955).
Proof. exact (@lem5268825 (_68953 = (@EMPTY real)) (term288 _68953 _68955)). Qed.
Lemma lem5268828 (a : Prop) (b : Prop) : (term622 a b) = (term623 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5268829 (_68953 : real -> Prop) (_68955 : real) : (term626 _68953 _68955) = (term627 _68953 _68955).
Proof. exact (@lem5268828 (term161 _68955 _68953) (term59 _68953 _68955)). Qed.
Lemma lem5268831 (a : Prop) : (term604 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5268832 (_68955 : real) (_68953 : real -> Prop) : (term605 _68955 _68953) = (@IN real _68955 _68953).
Proof. exact (@lem5268831 (@IN real _68955 _68953)). Qed.
Lemma lem5268833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5268834 (_68955 : real) (_68953 : real -> Prop) : (term628 _68955 _68953) = (term62 _68955 _68953).
Proof. exact (MK_COMB (@lem5268833) (@lem5268832 _68955 _68953)). Qed.
Lemma lem5268835 (_68953 : real -> Prop) (_68955 : real) : (term78 _68953 _68955) = (term78 _68953 _68955).
Proof. exact (eq_refl (term78 _68953 _68955)). Qed.
Lemma lem5268836 (_68953 : real -> Prop) (_68955 : real) : (term627 _68953 _68955) = (term629 _68953 _68955).
Proof. exact (MK_COMB (@lem5268834 _68955 _68953) (@lem5268835 _68953 _68955)). Qed.
Lemma lem5268837 (_68953 : real -> Prop) (_68955 : real) : (term626 _68953 _68955) = (term629 _68953 _68955).
Proof. exact (TRANS (@lem5268829 _68953 _68955) (@lem5268836 _68953 _68955)). Qed.
Lemma lem5268838 (_68953 : real -> Prop) : (term42 _68953) = (term42 _68953).
Proof. exact (eq_refl (term42 _68953)). Qed.
Lemma lem5268839 (_68953 : real -> Prop) (_68955 : real) : (term625 _68953 _68955) = (term630 _68953 _68955).
Proof. exact (MK_COMB (@lem5268838 _68953) (@lem5268837 _68953 _68955)). Qed.
Lemma lem5268840 (_68953 : real -> Prop) (_68955 : real) : (term624 _68953 _68955) = (term630 _68953 _68955).
Proof. exact (TRANS (@lem5268826 _68953 _68955) (@lem5268839 _68953 _68955)). Qed.
Lemma lem5268841 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5268842 (_68953 : real -> Prop) (_68955 : real) : (term631 _68953 _68955) = (term632 _68953 _68955).
Proof. exact (MK_COMB (@lem5268841) (@lem5268840 _68953 _68955)). Qed.
Lemma lem5268843 (x : type1021) (_68954 : real) (_68953 : real -> Prop) : (term534 x _68954 _68953) = (term534 x _68954 _68953).
Proof. exact (eq_refl (term534 x _68954 _68953)). Qed.
Lemma lem5268844 (_68955 : real) (x : type1021) (_68954 : real) (_68953 : real -> Prop) : (term620 _68955 x _68954 _68953) = (term633 _68955 x _68954 _68953).
Proof. exact (MK_COMB (@lem5268842 _68953 _68955) (@lem5268843 x _68954 _68953)). Qed.
Lemma lem5268845 (_68955 : real) (x : type1021) (_68954 : real) (_68953 : real -> Prop) : (term619 x _68954 _68953 _68955) = (term633 _68955 x _68954 _68953).
Proof. exact (TRANS (@lem5268823 _68955 x _68954 _68953) (@lem5268844 _68955 x _68954 _68953)). Qed.
Lemma lem5268847 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term78 s y) (h2 : term82 y a s b) : term629 s y.
Proof. exact (conj (@lem5268681 y a s b h2) (@lem5268689 s y h1)). Qed.
Lemma lem5268848 (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term78 s y) (h2 : term263 x') (h3 : term82 y a s b) : term630 s y.
Proof. exact (conj (@lem5268674 x' y a s b h2 h3) (@lem5268847 y a s b h1 h3)). Qed.
Lemma lem5268850 (_68955 : real) (_68954 : real) (_68953 : real -> Prop) (x : type1021) (h1 : term444 x) : term633 _68955 x _68954 _68953.
Proof. exact (EQ_MP (@lem5268845 _68955 x _68954 _68953) (@lem5268820 _68954 _68953 _68955 x h1)). Qed.
Lemma lem5268851 (y : real) (_68954 : real) (s : real -> Prop) (x : type1021) (h1 : term444 x) : term633 y x _68954 s.
Proof. exact (@lem5268850 y _68954 s x h1). Qed.
Lemma lem5268854 (_68954 : real) (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term78 s y) (h3 : term263 x') (h4 : term82 y a s b) : term534 x _68954 s.
Proof. exact (@lem5268851 y _68954 s x h1 (@lem5268848 x' y a s b h2 h3 h4)). Qed.
Lemma lem5268855 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term78 s y) (h3 : term263 x') (h4 : term82 y a s b) : term534 x a s.
Proof. exact (@lem5268854 a x x' y a s b h1 h2 h3 h4). Qed.
Lemma lem5268856 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term78 s y) (h3 : term263 x') (h4 : term82 y a s b) : term634 x a s.
Proof. exact (fun h0 : term635 x a s => @lem5268855 x x' y a s b h1 h2 h3 h4). Qed.
Lemma lem5268858 (p : Prop) : (term598 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5268859 (x : type1021) (a : real) (s : real -> Prop) : (term634 x a s) = (term534 x a s).
Proof. exact (@lem5268858 (term534 x a s)). Qed.
Lemma lem5268860 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term78 s y) (h3 : term263 x') (h4 : term82 y a s b) : term534 x a s.
Proof. exact (EQ_MP (@lem5268859 x a s) (@lem5268856 x x' y a s b h1 h2 h3 h4)). Qed.
Lemma lem5268866 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5268867 (a : real) (_68956 : real) (s : real -> Prop) : (term73 s a _68956) = (term636 a _68956 s).
Proof. exact (@lem5268866 (real_le a _68956) (term161 _68956 s)). Qed.
Lemma lem5268873 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5268874 (a : real) (_68956 : real) (s : real -> Prop) : (term637 s a _68956) = (term638 a _68956 s).
Proof. exact (MK_COMB (@lem5268873) (@lem5268867 a _68956 s)). Qed.
Lemma lem5268880 (a : real) (_68956 : real) (s : real -> Prop) : (term636 a _68956 s) = (term636 a _68956 s).
Proof. exact (eq_refl (term636 a _68956 s)). Qed.
Lemma lem5268881 (a : real) (_68956 : real) (s : real -> Prop) : ((term73 s a _68956) = (term636 a _68956 s)) = ((term636 a _68956 s) = (term636 a _68956 s)).
Proof. exact (MK_COMB (@lem5268874 a _68956 s) (@lem5268880 a _68956 s)). Qed.
Lemma lem5268883 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5268884 (x : Prop) : (x = x) = True.
Proof. exact (@lem5268883 Prop x). Qed.
Lemma lem5268885 (a : real) (_68956 : real) (s : real -> Prop) : ((term636 a _68956 s) = (term636 a _68956 s)) = True.
Proof. exact (@lem5268884 (term636 a _68956 s)). Qed.
Lemma lem5268886 (a : real) (_68956 : real) (s : real -> Prop) : ((term73 s a _68956) = (term636 a _68956 s)) = True.
Proof. exact (TRANS (@lem5268881 a _68956 s) (@lem5268885 a _68956 s)). Qed.
Lemma lem5268887 (a : real) (_68956 : real) (s : real -> Prop) : True = ((term73 s a _68956) = (term636 a _68956 s)).
Proof. exact (SYM (@lem5268886 a _68956 s)). Qed.
Lemma lem5268888 (a : real) (_68956 : real) (s : real -> Prop) : (term73 s a _68956) = (term636 a _68956 s).
Proof. exact (EQ_MP (@lem5268887 a _68956 s) (@lem0)). Qed.
Lemma lem5268889 (_68956 : real) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term636 a _68956 s.
Proof. exact (EQ_MP (@lem5268888 a _68956 s) (@lem5268412 _68956 y a s b h1)). Qed.
Lemma lem5268891 (b : Prop) (a : Prop) : (a \/ b) = (term602 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5268892 (s : real -> Prop) (a : real) (_68956 : real) : (term636 a _68956 s) = (term639 s a _68956).
Proof. exact (@lem5268891 (term161 _68956 s) (real_le a _68956)). Qed.
Lemma lem5268894 (a : Prop) : (term604 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5268895 (_68956 : real) (s : real -> Prop) : (term605 _68956 s) = (@IN real _68956 s).
Proof. exact (@lem5268894 (@IN real _68956 s)). Qed.
Lemma lem5268896 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5268897 (_68956 : real) (s : real -> Prop) : (term606 _68956 s) = (term607 _68956 s).
Proof. exact (MK_COMB (@lem5268896) (@lem5268895 _68956 s)). Qed.
Lemma lem5268898 (a : real) (_68956 : real) : (real_le a _68956) = (real_le a _68956).
Proof. exact (eq_refl (real_le a _68956)). Qed.
Lemma lem5268899 (s : real -> Prop) (a : real) (_68956 : real) : (term639 s a _68956) = (term28 s a _68956).
Proof. exact (MK_COMB (@lem5268897 _68956 s) (@lem5268898 a _68956)). Qed.
Lemma lem5268900 (s : real -> Prop) (a : real) (_68956 : real) : (term636 a _68956 s) = (term28 s a _68956).
Proof. exact (TRANS (@lem5268892 s a _68956) (@lem5268899 s a _68956)). Qed.
Lemma lem5268903 (_68956 : real) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term28 s a _68956.
Proof. exact (EQ_MP (@lem5268900 s a _68956) (@lem5268889 _68956 y a s b h1)). Qed.
Lemma lem5268904 (x : type1021) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term640 x s a.
Proof. exact (@lem5268903 (x s a) y a s b h1). Qed.
Lemma lem5268907 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term78 s y) (h3 : term263 x') (h4 : term82 y a s b) : term641 x s a.
Proof. exact (@lem5268904 x y a s b h4 (@lem5268860 x x' y a s b h1 h2 h3 h4)). Qed.
Lemma lem5268908 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term78 s y) (h3 : term263 x') (h4 : term82 y a s b) : term642 x s a.
Proof. exact (fun h0 : term535 x s a => @lem5268907 x x' y a s b h1 h2 h3 h4). Qed.
Lemma lem5268910 (p : Prop) : (term598 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5268911 (x : type1021) (s : real -> Prop) (a : real) : (term642 x s a) = (term641 x s a).
Proof. exact (@lem5268910 (term641 x s a)). Qed.
Lemma lem5268912 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term78 s y) (h3 : term263 x') (h4 : term82 y a s b) : term641 x s a.
Proof. exact (EQ_MP (@lem5268911 x s a) (@lem5268908 x x' y a s b h1 h2 h3 h4)). Qed.
Lemma lem5268914 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : @IN real y s.
Proof. exact (proj1 (@lem5268031 y a s b h1)). Qed.
Lemma lem5268915 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term597 y s.
Proof. exact (fun h0 : term161 y s => @lem5268914 y a s b h1). Qed.
Lemma lem5268917 (p : Prop) : (term598 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5268918 (y : real) (s : real -> Prop) : (term597 y s) = (@IN real y s).
Proof. exact (@lem5268917 (@IN real y s)). Qed.
Lemma lem5268919 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : @IN real y s.
Proof. exact (EQ_MP (@lem5268918 y s) (@lem5268915 y a s b h1)). Qed.
Lemma lem5268937 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5268938 (x : type1021) (_68954 : real) (_68953 : real -> Prop) (_68955 : real) : (term643 x _68954 _68953 _68955) = (term644 x _68954 _68953 _68955).
Proof. exact (@lem5268937 (term161 _68955 _68953) (term535 x _68953 _68954) (term59 _68953 _68955)). Qed.
Lemma lem5268952 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5268953 (_68955 : real) (x : type1021) (_68953 : real -> Prop) (_68954 : real) : (term645 x _68954 _68953 _68955) = (term646 _68955 x _68953 _68954).
Proof. exact (@lem5268952 (term59 _68953 _68955) (term535 x _68953 _68954)). Qed.
Lemma lem5268959 (_68955 : real) (_68953 : real -> Prop) : (term574 _68955 _68953) = (term574 _68955 _68953).
Proof. exact (eq_refl (term574 _68955 _68953)). Qed.
Lemma lem5268960 (_68955 : real) (x : type1021) (_68953 : real -> Prop) (_68954 : real) : (term644 x _68954 _68953 _68955) = (term647 _68955 x _68953 _68954).
Proof. exact (MK_COMB (@lem5268959 _68955 _68953) (@lem5268953 _68955 x _68953 _68954)). Qed.
Lemma lem5268964 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5268965 (_68955 : real) (x : type1021) (_68953 : real -> Prop) (_68954 : real) : (term647 _68955 x _68953 _68954) = (term648 _68955 x _68953 _68954).
Proof. exact (@lem5268964 (term59 _68953 _68955) (term161 _68955 _68953) (term535 x _68953 _68954)). Qed.
Lemma lem5268981 (_68955 : real) (x : type1021) (_68953 : real -> Prop) (_68954 : real) : (term644 x _68954 _68953 _68955) = (term648 _68955 x _68953 _68954).
Proof. exact (TRANS (@lem5268960 _68955 x _68953 _68954) (@lem5268965 _68955 x _68953 _68954)). Qed.
Lemma lem5268982 (_68955 : real) (x : type1021) (_68953 : real -> Prop) (_68954 : real) : (term643 x _68954 _68953 _68955) = (term648 _68955 x _68953 _68954).
Proof. exact (TRANS (@lem5268938 x _68954 _68953 _68955) (@lem5268981 _68955 x _68953 _68954)). Qed.
Lemma lem5268983 (_68953 : real -> Prop) : (term284 _68953) = (term284 _68953).
Proof. exact (eq_refl (term284 _68953)). Qed.
Lemma lem5268984 (_68955 : real) (x : type1021) (_68953 : real -> Prop) (_68954 : real) : (term596 x _68954 _68953 _68955) = (term649 _68955 x _68953 _68954).
Proof. exact (MK_COMB (@lem5268983 _68953) (@lem5268982 _68955 x _68953 _68954)). Qed.
Lemma lem5268995 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5268996 (_68955 : real) (x : type1021) (_68953 : real -> Prop) (_68954 : real) : (term650 x _68954 _68953 _68955) = (term651 _68955 x _68953 _68954).
Proof. exact (MK_COMB (@lem5268995) (@lem5268984 _68955 x _68953 _68954)). Qed.
Lemma lem5269000 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5269001 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : (term652 x _68954 _68955 _68953) = (term653 x _68954 _68955 _68953).
Proof. exact (@lem5269000 (_68953 = (@EMPTY real)) (term59 _68953 _68955) (term654 x _68954 _68955 _68953)). Qed.
Lemma lem5269027 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5269028 (_68955 : real) (x : type1021) (_68953 : real -> Prop) (_68954 : real) : (term654 x _68954 _68955 _68953) = (term655 _68955 x _68953 _68954).
Proof. exact (@lem5269027 (term161 _68955 _68953) (term535 x _68953 _68954)). Qed.
Lemma lem5269034 (_68953 : real -> Prop) (_68955 : real) : (term656 _68953 _68955) = (term656 _68953 _68955).
Proof. exact (eq_refl (term656 _68953 _68955)). Qed.
Lemma lem5269035 (_68955 : real) (x : type1021) (_68953 : real -> Prop) (_68954 : real) : (term657 x _68954 _68955 _68953) = (term648 _68955 x _68953 _68954).
Proof. exact (MK_COMB (@lem5269034 _68953 _68955) (@lem5269028 _68955 x _68953 _68954)). Qed.
Lemma lem5269046 (_68953 : real -> Prop) : (term284 _68953) = (term284 _68953).
Proof. exact (eq_refl (term284 _68953)). Qed.
Lemma lem5269047 (_68955 : real) (x : type1021) (_68953 : real -> Prop) (_68954 : real) : (term653 x _68954 _68955 _68953) = (term649 _68955 x _68953 _68954).
Proof. exact (MK_COMB (@lem5269046 _68953) (@lem5269035 _68955 x _68953 _68954)). Qed.
Lemma lem5269058 (_68955 : real) (x : type1021) (_68953 : real -> Prop) (_68954 : real) : (term652 x _68954 _68955 _68953) = (term649 _68955 x _68953 _68954).
Proof. exact (TRANS (@lem5269001 x _68954 _68955 _68953) (@lem5269047 _68955 x _68953 _68954)). Qed.
Lemma lem5269059 (_68955 : real) (x : type1021) (_68953 : real -> Prop) (_68954 : real) : ((term596 x _68954 _68953 _68955) = (term652 x _68954 _68955 _68953)) = ((term649 _68955 x _68953 _68954) = (term649 _68955 x _68953 _68954)).
Proof. exact (MK_COMB (@lem5268996 _68955 x _68953 _68954) (@lem5269058 _68955 x _68953 _68954)). Qed.
Lemma lem5269061 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5269062 (x : Prop) : (x = x) = True.
Proof. exact (@lem5269061 Prop x). Qed.
Lemma lem5269063 (_68955 : real) (x : type1021) (_68953 : real -> Prop) (_68954 : real) : ((term649 _68955 x _68953 _68954) = (term649 _68955 x _68953 _68954)) = True.
Proof. exact (@lem5269062 (term649 _68955 x _68953 _68954)). Qed.
Lemma lem5269064 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : ((term596 x _68954 _68953 _68955) = (term652 x _68954 _68955 _68953)) = True.
Proof. exact (TRANS (@lem5269059 _68955 x _68953 _68954) (@lem5269063 _68955 x _68953 _68954)). Qed.
Lemma lem5269065 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : True = ((term596 x _68954 _68953 _68955) = (term652 x _68954 _68955 _68953)).
Proof. exact (SYM (@lem5269064 x _68954 _68955 _68953)). Qed.
Lemma lem5269066 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : (term596 x _68954 _68953 _68955) = (term652 x _68954 _68955 _68953).
Proof. exact (EQ_MP (@lem5269065 x _68954 _68955 _68953) (@lem0)). Qed.
Lemma lem5269067 (_68954 : real) (_68955 : real) (_68953 : real -> Prop) (x : type1021) (h1 : term444 x) : term652 x _68954 _68955 _68953.
Proof. exact (EQ_MP (@lem5269066 x _68954 _68955 _68953) (@lem5268520 _68954 _68953 _68955 x h1)). Qed.
Lemma lem5269069 (b : Prop) (a : Prop) : (a \/ b) = (term602 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5269070 (x : type1021) (_68954 : real) (_68953 : real -> Prop) (_68955 : real) : (term652 x _68954 _68955 _68953) = (term658 x _68954 _68953 _68955).
Proof. exact (@lem5269069 (term659 x _68954 _68955 _68953) (term59 _68953 _68955)). Qed.
Lemma lem5269072 (a : Prop) (b : Prop) : (term622 a b) = (term623 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5269073 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : (term660 x _68954 _68955 _68953) = (term661 x _68954 _68955 _68953).
Proof. exact (@lem5269072 (_68953 = (@EMPTY real)) (term654 x _68954 _68955 _68953)). Qed.
Lemma lem5269075 (a : Prop) (b : Prop) : (term622 a b) = (term623 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5269076 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : (term662 x _68954 _68955 _68953) = (term663 x _68954 _68955 _68953).
Proof. exact (@lem5269075 (term535 x _68953 _68954) (term161 _68955 _68953)). Qed.
Lemma lem5269078 (a : Prop) : (term604 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5269079 (x : type1021) (_68953 : real -> Prop) (_68954 : real) : (term664 x _68953 _68954) = (term641 x _68953 _68954).
Proof. exact (@lem5269078 (term641 x _68953 _68954)). Qed.
Lemma lem5269080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5269081 (x : type1021) (_68953 : real -> Prop) (_68954 : real) : (term665 x _68953 _68954) = (term666 x _68953 _68954).
Proof. exact (MK_COMB (@lem5269080) (@lem5269079 x _68953 _68954)). Qed.
Lemma lem5269083 (a : Prop) : (term604 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5269084 (_68955 : real) (_68953 : real -> Prop) : (term605 _68955 _68953) = (@IN real _68955 _68953).
Proof. exact (@lem5269083 (@IN real _68955 _68953)). Qed.
Lemma lem5269085 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : (term663 x _68954 _68955 _68953) = (term667 x _68954 _68955 _68953).
Proof. exact (MK_COMB (@lem5269081 x _68953 _68954) (@lem5269084 _68955 _68953)). Qed.
Lemma lem5269086 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : (term662 x _68954 _68955 _68953) = (term667 x _68954 _68955 _68953).
Proof. exact (TRANS (@lem5269076 x _68954 _68955 _68953) (@lem5269085 x _68954 _68955 _68953)). Qed.
Lemma lem5269087 (_68953 : real -> Prop) : (term42 _68953) = (term42 _68953).
Proof. exact (eq_refl (term42 _68953)). Qed.
Lemma lem5269088 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : (term661 x _68954 _68955 _68953) = (term668 x _68954 _68955 _68953).
Proof. exact (MK_COMB (@lem5269087 _68953) (@lem5269086 x _68954 _68955 _68953)). Qed.
Lemma lem5269089 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : (term660 x _68954 _68955 _68953) = (term668 x _68954 _68955 _68953).
Proof. exact (TRANS (@lem5269073 x _68954 _68955 _68953) (@lem5269088 x _68954 _68955 _68953)). Qed.
Lemma lem5269090 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5269091 (x : type1021) (_68954 : real) (_68955 : real) (_68953 : real -> Prop) : (term669 x _68954 _68955 _68953) = (term670 x _68954 _68955 _68953).
Proof. exact (MK_COMB (@lem5269090) (@lem5269089 x _68954 _68955 _68953)). Qed.
Lemma lem5269092 (_68953 : real -> Prop) (_68955 : real) : (term59 _68953 _68955) = (term59 _68953 _68955).
Proof. exact (eq_refl (term59 _68953 _68955)). Qed.
Lemma lem5269093 (x : type1021) (_68954 : real) (_68953 : real -> Prop) (_68955 : real) : (term658 x _68954 _68953 _68955) = (term671 x _68954 _68953 _68955).
Proof. exact (MK_COMB (@lem5269091 x _68954 _68955 _68953) (@lem5269092 _68953 _68955)). Qed.
Lemma lem5269094 (x : type1021) (_68954 : real) (_68953 : real -> Prop) (_68955 : real) : (term652 x _68954 _68955 _68953) = (term671 x _68954 _68953 _68955).
Proof. exact (TRANS (@lem5269070 x _68954 _68953 _68955) (@lem5269093 x _68954 _68953 _68955)). Qed.
Lemma lem5269096 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term78 s y) (h3 : term263 x') (h4 : term82 y a s b) : term667 x a y s.
Proof. exact (conj (@lem5268912 x x' y a s b h1 h2 h3 h4) (@lem5268919 y a s b h4)). Qed.
Lemma lem5269097 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term78 s y) (h3 : term263 x') (h4 : term82 y a s b) : term668 x a y s.
Proof. exact (conj (@lem5268656 x' y a s b h3 h4) (@lem5269096 x x' y a s b h1 h2 h3 h4)). Qed.
Lemma lem5269099 (_68954 : real) (_68953 : real -> Prop) (_68955 : real) (x : type1021) (h1 : term444 x) : term671 x _68954 _68953 _68955.
Proof. exact (EQ_MP (@lem5269094 x _68954 _68953 _68955) (@lem5269067 _68954 _68955 _68953 x h1)). Qed.
Lemma lem5269100 (a : real) (s : real -> Prop) (y : real) (x : type1021) (h1 : term444 x) : term671 x a s y.
Proof. exact (@lem5269099 a s y x h1). Qed.
Lemma lem5269103 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term78 s y) (h3 : term263 x') (h4 : term82 y a s b) : term59 s y.
Proof. exact (@lem5269100 a s y x h1 (@lem5269097 x x' y a s b h1 h2 h3 h4)). Qed.
Lemma lem5269104 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term263 x') (h3 : term82 y a s b) : term672 s y.
Proof. exact (fun h0 : term78 s y => @lem5269103 x x' y a s b h1 h0 h2 h3). Qed.
Lemma lem5269106 (p : Prop) : (term598 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5269107 (s : real -> Prop) (y : real) : (term672 s y) = (term59 s y).
Proof. exact (@lem5269106 (term59 s y)). Qed.
Lemma lem5269108 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term263 x') (h3 : term82 y a s b) : term59 s y.
Proof. exact (EQ_MP (@lem5269107 s y) (@lem5269104 x x' y a s b h1 h2 h3)). Qed.
Lemma lem5269110 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : real_le y b.
Proof. exact (proj1 (@lem5268032 y a s b h1)). Qed.
Lemma lem5269111 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term673 y b.
Proof. exact (fun h0 : term594 y b => @lem5269110 y a s b h1). Qed.
Lemma lem5269113 (p : Prop) : (term598 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5269114 (y : real) (b : real) : (term673 y b) = (real_le y b).
Proof. exact (@lem5269113 (real_le y b)). Qed.
Lemma lem5269115 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : real_le y b.
Proof. exact (EQ_MP (@lem5269114 y b) (@lem5269111 y a s b h1)). Qed.
Lemma lem5269131 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5269132 (_68950 : real) (_68951 : real) (_68952 : real) : (term674 _68951 _68950 _68952) = (term675 _68950 _68951 _68952).
Proof. exact (@lem5269131 (real_le _68950 _68952) (term594 _68951 _68952)). Qed.
Lemma lem5269138 (_68950 : real) (_68951 : real) : (term676 _68950 _68951) = (term676 _68950 _68951).
Proof. exact (eq_refl (term676 _68950 _68951)). Qed.
Lemma lem5269139 (_68950 : real) (_68951 : real) (_68952 : real) : (term593 _68951 _68950 _68952) = (term677 _68950 _68951 _68952).
Proof. exact (MK_COMB (@lem5269138 _68950 _68951) (@lem5269132 _68950 _68951 _68952)). Qed.
Lemma lem5269143 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5269144 (_68950 : real) (_68951 : real) (_68952 : real) : (term677 _68950 _68951 _68952) = (term678 _68950 _68951 _68952).
Proof. exact (@lem5269143 (real_le _68950 _68952) (term594 _68950 _68951) (term594 _68951 _68952)). Qed.
Lemma lem5269160 (_68950 : real) (_68951 : real) (_68952 : real) : (term593 _68951 _68950 _68952) = (term678 _68950 _68951 _68952).
Proof. exact (TRANS (@lem5269139 _68950 _68951 _68952) (@lem5269144 _68950 _68951 _68952)). Qed.
Lemma lem5269161 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5269162 (_68950 : real) (_68951 : real) (_68952 : real) : (term679 _68951 _68950 _68952) = (term680 _68950 _68951 _68952).
Proof. exact (MK_COMB (@lem5269161) (@lem5269160 _68950 _68951 _68952)). Qed.
Lemma lem5269178 (_68950 : real) (_68951 : real) (_68952 : real) : (term678 _68950 _68951 _68952) = (term678 _68950 _68951 _68952).
Proof. exact (eq_refl (term678 _68950 _68951 _68952)). Qed.
Lemma lem5269179 (_68950 : real) (_68951 : real) (_68952 : real) : ((term593 _68951 _68950 _68952) = (term678 _68950 _68951 _68952)) = ((term678 _68950 _68951 _68952) = (term678 _68950 _68951 _68952)).
Proof. exact (MK_COMB (@lem5269162 _68950 _68951 _68952) (@lem5269178 _68950 _68951 _68952)). Qed.
Lemma lem5269181 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5269182 (x : Prop) : (x = x) = True.
Proof. exact (@lem5269181 Prop x). Qed.
Lemma lem5269183 (_68950 : real) (_68951 : real) (_68952 : real) : ((term678 _68950 _68951 _68952) = (term678 _68950 _68951 _68952)) = True.
Proof. exact (@lem5269182 (term678 _68950 _68951 _68952)). Qed.
Lemma lem5269184 (_68950 : real) (_68951 : real) (_68952 : real) : ((term593 _68951 _68950 _68952) = (term678 _68950 _68951 _68952)) = True.
Proof. exact (TRANS (@lem5269179 _68950 _68951 _68952) (@lem5269183 _68950 _68951 _68952)). Qed.
Lemma lem5269185 (_68950 : real) (_68951 : real) (_68952 : real) : True = ((term593 _68951 _68950 _68952) = (term678 _68950 _68951 _68952)).
Proof. exact (SYM (@lem5269184 _68950 _68951 _68952)). Qed.
Lemma lem5269186 (_68950 : real) (_68951 : real) (_68952 : real) : (term593 _68951 _68950 _68952) = (term678 _68950 _68951 _68952).
Proof. exact (EQ_MP (@lem5269185 _68950 _68951 _68952) (@lem0)). Qed.
Lemma lem5269187 (_68950 : real) (_68951 : real) (_68952 : real) (h1 : term58) : term678 _68950 _68951 _68952.
Proof. exact (EQ_MP (@lem5269186 _68950 _68951 _68952) (@lem5268400 _68951 _68950 _68952 h1)). Qed.
Lemma lem5269189 (b : Prop) (a : Prop) : (a \/ b) = (term602 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5269190 (_68951 : real) (_68950 : real) (_68952 : real) : (term678 _68950 _68951 _68952) = (term681 _68951 _68950 _68952).
Proof. exact (@lem5269189 (term143 _68950 _68951 _68952) (real_le _68950 _68952)). Qed.
Lemma lem5269192 (a : Prop) (b : Prop) : (term622 a b) = (term623 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5269193 (_68950 : real) (_68951 : real) (_68952 : real) : (term682 _68950 _68951 _68952) = (term683 _68950 _68951 _68952).
Proof. exact (@lem5269192 (term594 _68950 _68951) (term594 _68951 _68952)). Qed.
Lemma lem5269195 (a : Prop) : (term604 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5269196 (_68950 : real) (_68951 : real) : (term684 _68950 _68951) = (real_le _68950 _68951).
Proof. exact (@lem5269195 (real_le _68950 _68951)). Qed.
Lemma lem5269197 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5269198 (_68950 : real) (_68951 : real) : (term685 _68950 _68951) = (term60 _68950 _68951).
Proof. exact (MK_COMB (@lem5269197) (@lem5269196 _68950 _68951)). Qed.
Lemma lem5269200 (a : Prop) : (term604 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5269201 (_68951 : real) (_68952 : real) : (term684 _68951 _68952) = (real_le _68951 _68952).
Proof. exact (@lem5269200 (real_le _68951 _68952)). Qed.
Lemma lem5269202 (_68950 : real) (_68951 : real) (_68952 : real) : (term683 _68950 _68951 _68952) = (term148 _68950 _68951 _68952).
Proof. exact (MK_COMB (@lem5269198 _68950 _68951) (@lem5269201 _68951 _68952)). Qed.
Lemma lem5269203 (_68950 : real) (_68951 : real) (_68952 : real) : (term682 _68950 _68951 _68952) = (term148 _68950 _68951 _68952).
Proof. exact (TRANS (@lem5269193 _68950 _68951 _68952) (@lem5269202 _68950 _68951 _68952)). Qed.
Lemma lem5269204 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5269205 (_68950 : real) (_68951 : real) (_68952 : real) : (term686 _68950 _68951 _68952) = (term687 _68950 _68951 _68952).
Proof. exact (MK_COMB (@lem5269204) (@lem5269203 _68950 _68951 _68952)). Qed.
Lemma lem5269206 (_68950 : real) (_68952 : real) : (real_le _68950 _68952) = (real_le _68950 _68952).
Proof. exact (eq_refl (real_le _68950 _68952)). Qed.
Lemma lem5269207 (_68951 : real) (_68950 : real) (_68952 : real) : (term681 _68951 _68950 _68952) = (term52 _68951 _68950 _68952).
Proof. exact (MK_COMB (@lem5269205 _68950 _68951 _68952) (@lem5269206 _68950 _68952)). Qed.
Lemma lem5269208 (_68951 : real) (_68950 : real) (_68952 : real) : (term678 _68950 _68951 _68952) = (term52 _68951 _68950 _68952).
Proof. exact (TRANS (@lem5269190 _68951 _68950 _68952) (@lem5269207 _68951 _68950 _68952)). Qed.
Lemma lem5269210 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term263 x') (h3 : term82 y a s b) : term688 s y b.
Proof. exact (conj (@lem5269108 x x' y a s b h1 h2 h3) (@lem5269115 y a s b h3)). Qed.
Lemma lem5269212 (_68951 : real) (_68950 : real) (_68952 : real) (h1 : term58) : term52 _68951 _68950 _68952.
Proof. exact (EQ_MP (@lem5269208 _68951 _68950 _68952) (@lem5269187 _68950 _68951 _68952 h1)). Qed.
Lemma lem5269213 (y : real) (s : real -> Prop) (b : real) (h1 : term58) : term689 y s b.
Proof. exact (@lem5269212 y (inf s) b h1). Qed.
Lemma lem5269216 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term58) (h3 : term263 x') (h4 : term82 y a s b) : term59 s b.
Proof. exact (@lem5269213 y s b h2 (@lem5269210 x x' y a s b h1 h3 h4)). Qed.
Lemma lem5269217 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term58) (h3 : term263 x') (h4 : term82 y a s b) : term672 s b.
Proof. exact (fun h0 : term78 s b => @lem5269216 x x' y a s b h1 h2 h3 h4). Qed.
Lemma lem5269219 (p : Prop) : (term598 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5269220 (s : real -> Prop) (b : real) : (term672 s b) = (term59 s b).
Proof. exact (@lem5269219 (term59 s b)). Qed.
Lemma lem5269221 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term58) (h3 : term263 x') (h4 : term82 y a s b) : term59 s b.
Proof. exact (EQ_MP (@lem5269220 s b) (@lem5269217 x x' y a s b h1 h2 h3 h4)). Qed.
Lemma lem5269224 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5269226 (s : real -> Prop) (b : real) : (term78 s b) = (term690 s b).
Proof. exact (@lem5269224 (term59 s b)). Qed.
Lemma lem5269229 (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term82 y a s b) : term690 s b.
Proof. exact (EQ_MP (@lem5269226 s b) (@lem5268402 y a s b h1)). Qed.
Lemma lem5269232 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term58) (h3 : term263 x') (h4 : term82 y a s b) : False.
Proof. exact (@lem5269229 y a s b h4 (@lem5269221 x x' y a s b h1 h2 h3 h4)). Qed.
Lemma lem5269233 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term58) (h3 : term263 x') (h4 : term82 y a s b) : term691.
Proof. exact (fun h0 : ~ False => @lem5269232 x x' y a s b h1 h2 h3 h4). Qed.
Lemma lem5269235 (p : Prop) : (term598 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5269236 : term691 = False.
Proof. exact (@lem5269235 False). Qed.
Lemma lem5269237 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term58) (h3 : term263 x') (h4 : term82 y a s b) : False.
Proof. exact (EQ_MP (@lem5269236) (@lem5269233 x x' y a s b h1 h2 h3 h4)). Qed.
Lemma lem5269238 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term58) (h3 : term263 x') (h4 : term82 y a s b) : (term82 y a s b) = False.
Proof. exact (prop_ext (fun h5 : term82 y a s b => @lem5269237 x x' y a s b h1 h2 h3 h4) (fun h5 : False => @lem5268029 y a s b h4)). Qed.
Lemma lem5269239 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term58) (h3 : term263 x') (h4 : term82 y a s b) : False.
Proof. exact (EQ_MP (@lem5269238 x x' y a s b h1 h2 h3 h4) (@lem5268029 y a s b h4)). Qed.
Lemma lem5269240 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term58) (h3 : term263 x') (h4 : term82 y a s b) : (term263 x') = False.
Proof. exact (prop_ext (fun h5 : term263 x' => @lem5269239 x x' y a s b h1 h2 h3 h4) (fun h5 : False => @lem5267982 x' h3)). Qed.
Lemma lem5269241 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term58) (h3 : term263 x') (h4 : term82 y a s b) : False.
Proof. exact (EQ_MP (@lem5269240 x x' y a s b h1 h2 h3 h4) (@lem5267982 x' h3)). Qed.
Lemma lem5269242 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term58) (h3 : term263 x') (h4 : term82 y a s b) : (term444 x) = False.
Proof. exact (prop_ext (fun h5 : term444 x => @lem5269241 x x' y a s b h1 h2 h3 h4) (fun h5 : False => @lem5267937 x h1)). Qed.
Lemma lem5269243 (x : type1021) (x' : type1023) (y : real) (a : real) (s : real -> Prop) (b : real) (h1 : term444 x) (h2 : term58) (h3 : term263 x') (h4 : term82 y a s b) : False.
Proof. exact (EQ_MP (@lem5269242 x x' y a s b h1 h2 h3 h4) (@lem5267937 x h1)). Qed.
Lemma lem5269244 (x : type1021) (a : real) (s : real -> Prop) (b : real) (x' : type1023) (h1 : term444 x) (h2 : term58) (h3 : term92 a s b) (h4 : term263 x') : False.
Proof. exact (ex_elim (@lem5267801 a s b h3) (fun y : real => fun h0 : term91 a s b y => @lem5269243 x x' y a s b h1 h2 h4 h0)). Qed.
Lemma lem5269245 (x : type1021) (a : real) (s : real -> Prop) (x' : type1023) (h1 : term444 x) (h2 : term58) (h3 : term99 a s) (h4 : term263 x') : False.
Proof. exact (ex_elim (@lem5267800 a s h3) (fun b : real => fun h0 : term98 a s b => @lem5269244 x a s b x' h1 h2 h0 h4)). Qed.
Lemma lem5269246 (x : type1021) (s : real -> Prop) (x' : type1023) (h1 : term444 x) (h2 : term58) (h3 : term106 s) (h4 : term263 x') : False.
Proof. exact (ex_elim (@lem5267799 s h3) (fun a : real => fun h0 : term105 s a => @lem5269245 x a s x' h1 h2 h0 h4)). Qed.
Lemma lem5269247 (x : type1021) (x' : type1023) (h1 : term444 x) (h2 : term58) (h3 : term10) (h4 : term263 x') : False.
Proof. exact (ex_elim (@lem5266930 h3) (fun s : real -> Prop => fun h0 : term113 s => @lem5269246 x s x' h1 h2 h0 h4)). Qed.
Lemma lem5269248 (x : type1021) (h1 : term11) (h2 : term444 x) (h3 : term58) (h4 : term10) : False.
Proof. exact (ex_elim (@lem5267267 h1) (fun x' : type1023 => fun h0 : term265 x' => @lem5269247 x x' h2 h3 h4 h0)). Qed.
Lemma lem5269249 (h1 : term11) (h2 : term18) (h3 : term58) (h4 : term10) : False.
Proof. exact (ex_elim (@lem5267796 h2) (fun x : type1021 => fun h0 : term446 x => @lem5269248 x h1 h0 h3 h4)). Qed.
Lemma lem5269250 (h1 : term11) (h2 : term58) (h3 : term10) : term16.
Proof. exact (fun h0 : term18 => @lem5269249 h1 h0 h2 h3). Qed.
Lemma lem5269251 : term16 = term17.
Proof. exact (@lem69 term18). Qed.
Lemma lem5269252 (h1 : term11) (h2 : term58) (h3 : term10) : term17.
Proof. exact (EQ_MP (@lem5269251) (@lem5269250 h1 h2 h3)). Qed.
Lemma lem5269253 (h1 : term58) (h2 : term10) : term21.
Proof. exact (fun h0 : term11 => @lem5269252 h0 h1 h2). Qed.
Lemma lem5269254 (h1 : term10) : term24.
Proof. exact (fun h0 : term58 => @lem5269253 h0 h1). Qed.
Lemma lem5269255 : term26.
Proof. exact (fun h0 : term10 => @lem5269254 h0). Qed.
Lemma lem5269256 : term12.
Proof. exact (EQ_MP (@lem5266609) (@lem5269255)). Qed.
Lemma lem5269258 : term12.
Proof. exact (@lem5266237 (@lem5269256)). Qed.
Lemma lem5269259 (h1 : term10) : term23.
Proof. exact (@lem5269258 (@lem5266219 h1)). Qed.
Lemma lem5269260 (h1 : term10) : term20.
Proof. exact (@lem5269259 h1 (@lem1339577)). Qed.
Lemma lem5269261 (h1 : term10) : term16.
Proof. exact (@lem5269260 h1 (@lem5266220)). Qed.
Lemma lem5269262 (h1 : term10) : False.
Proof. exact (@lem5269261 h1 (@lem5214027)). Qed.
Lemma lem5269263 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem5269262 h1) (fun h2 : False => @lem5266219 h1)). Qed.
Lemma lem5269264 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem5269263 h1) (@lem5266219 h1)). Qed.
Lemma lem5269265 : term9.
Proof. exact (fun h0 : term10 => @lem5269264 h0). Qed.
Lemma lem5269266 : term8.
Proof. exact (EQ_MP (@lem5266218) (@lem5269265)). Qed.
