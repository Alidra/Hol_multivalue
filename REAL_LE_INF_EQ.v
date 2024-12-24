Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_INF_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import INF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339577_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
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
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
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
Lemma lem5269267 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5269268 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5269269 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5269268 t1) (@lem5269267 t1)). Qed.
Lemma lem5269270 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5269269 t1 t2). Qed.
Lemma lem5269271 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5269272 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5269271 t1 t2) (@lem5269270 t1 t2)). Qed.
Lemma lem5269273 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5269272 t1 t2 t3). Qed.
Lemma lem5269274 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5269275 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5269274 t1 t2 t3) (@lem5269273 t1 t2 t3)). Qed.
Lemma lem5269276 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5269275 t1 t2 t3)). Qed.
Lemma lem5269278 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5269279 : term8 = term9.
Proof. exact (@lem5269278 term8). Qed.
Lemma lem5269280 : term9 = term8.
Proof. exact (SYM (@lem5269279)). Qed.
Lemma lem5269281 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5269284 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5269285 : term12.
Proof. exact (fun h0 : term11 => @lem5269284 h0). Qed.
Lemma lem5269286 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5269287 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5269288 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5269286 h2 (@lem5269287 h1)). Qed.
Lemma lem5269289 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem5269288 h1 h0). Qed.
Lemma lem5269290 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5269291 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5269289 h1 (@lem5269290 h2)). Qed.
Lemma lem5269292 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem5269291 h0 h1). Qed.
Lemma lem5269293 : term14.
Proof. exact (fun h0 : term12 => @lem5269292 h0). Qed.
Lemma lem5269296 : term12.
Proof. exact (@lem5269293 (@lem5269285)). Qed.
Lemma lem5269346 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5269347 : term15 = term16.
Proof. exact (@lem5269346 term17). Qed.
Lemma lem5269386 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem5269387 : term19 = term20.
Proof. exact (MK_COMB (@lem5269386) (@lem5269347)). Qed.
Lemma lem5269390 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem5269397 : term11 = term22.
Proof. exact (MK_COMB (@lem5269390) (@lem5269387)). Qed.
Lemma lem5269398 (b : real) (s : real -> Prop) : (term23 b s) = (term23 b s).
Proof. exact (eq_refl (term23 b s)). Qed.
Lemma lem5269403 (s : real -> Prop) (b : real) (x : real) : (term24 s b x) = (term24 s b x).
Proof. exact (eq_refl (term24 s b x)). Qed.
Lemma lem5269404 (s : real -> Prop) (b : real) : (term25 s b) = (term25 s b).
Proof. exact (fun_ext (fun x : real => @lem5269403 s b x)). Qed.
Lemma lem5269405 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5269406 (s : real -> Prop) (b : real) : (term26 s b) = (term26 s b).
Proof. exact (MK_COMB (@lem5269405) (@lem5269404 s b)). Qed.
Lemma lem5269407 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5269408 (s : real -> Prop) (b : real) : (term27 s b) = (term27 s b).
Proof. exact (MK_COMB (@lem5269407) (@lem5269406 s b)). Qed.
Lemma lem5269409 (b : real) (s : real -> Prop) : (term28 b s) = (term28 b s).
Proof. exact (MK_COMB (@lem5269408 s b) (@lem5269398 b s)). Qed.
Lemma lem5269410 (s : real -> Prop) : (term29 s) = (term29 s).
Proof. exact (fun_ext (fun b : real => @lem5269409 b s)). Qed.
Lemma lem5269411 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5269412 (s : real -> Prop) : (term30 s) = (term30 s).
Proof. exact (MK_COMB (@lem5269411) (@lem5269410 s)). Qed.
Lemma lem5269417 (s : real -> Prop) (x : real) : (term31 s x) = (term31 s x).
Proof. exact (eq_refl (term31 s x)). Qed.
Lemma lem5269418 (s : real -> Prop) : (term32 s) = (term32 s).
Proof. exact (fun_ext (fun x : real => @lem5269417 s x)). Qed.
Lemma lem5269419 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5269420 (s : real -> Prop) : (term33 s) = (term33 s).
Proof. exact (MK_COMB (@lem5269419) (@lem5269418 s)). Qed.
Lemma lem5269421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5269422 (s : real -> Prop) : (term34 s) = (term34 s).
Proof. exact (MK_COMB (@lem5269421) (@lem5269420 s)). Qed.
Lemma lem5269423 (s : real -> Prop) : (term35 s) = (term35 s).
Proof. exact (MK_COMB (@lem5269422 s) (@lem5269412 s)). Qed.
Lemma lem5269428 (s : real -> Prop) (b : real) (x : real) : (term24 s b x) = (term24 s b x).
Proof. exact (eq_refl (term24 s b x)). Qed.
Lemma lem5269429 (s : real -> Prop) (b : real) : (term25 s b) = (term25 s b).
Proof. exact (fun_ext (fun x : real => @lem5269428 s b x)). Qed.
Lemma lem5269430 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5269431 (s : real -> Prop) (b : real) : (term26 s b) = (term26 s b).
Proof. exact (MK_COMB (@lem5269430) (@lem5269429 s b)). Qed.
Lemma lem5269432 (s : real -> Prop) : (term36 s) = (term36 s).
Proof. exact (fun_ext (fun b : real => @lem5269431 s b)). Qed.
Lemma lem5269433 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5269434 (s : real -> Prop) : (term37 s) = (term37 s).
Proof. exact (MK_COMB (@lem5269433) (@lem5269432 s)). Qed.
Lemma lem5269439 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (eq_refl (term38 s)). Qed.
Lemma lem5269440 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (MK_COMB (@lem5269439 s) (@lem5269434 s)). Qed.
Lemma lem5269441 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5269442 (s : real -> Prop) : (term40 s) = (term40 s).
Proof. exact (MK_COMB (@lem5269441) (@lem5269440 s)). Qed.
Lemma lem5269443 (s : real -> Prop) : (term41 s) = (term41 s).
Proof. exact (MK_COMB (@lem5269442 s) (@lem5269423 s)). Qed.
Lemma lem5269444 : term42 = term42.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5269443 s)). Qed.
Lemma lem5269445 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5269446 : term17 = term17.
Proof. exact (MK_COMB (@lem5269445) (@lem5269444)). Qed.
Lemma lem5269447 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5269448 : term16 = term16.
Proof. exact (MK_COMB (@lem5269447) (@lem5269446)). Qed.
Lemma lem5269457 (y : real) (x : real) (z : real) : (term43 y x z) = (term43 y x z).
Proof. exact (eq_refl (term43 y x z)). Qed.
Lemma lem5269458 (y : real) (x : real) : (term44 y x) = (term44 y x).
Proof. exact (fun_ext (fun z : real => @lem5269457 y x z)). Qed.
Lemma lem5269459 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5269460 (y : real) (x : real) : (term45 y x) = (term45 y x).
Proof. exact (MK_COMB (@lem5269459) (@lem5269458 y x)). Qed.
Lemma lem5269461 (x : real) : (term46 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem5269460 y x)). Qed.
Lemma lem5269462 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5269463 (x : real) : (term47 x) = (term47 x).
Proof. exact (MK_COMB (@lem5269462) (@lem5269461 x)). Qed.
Lemma lem5269464 : term48 = term48.
Proof. exact (fun_ext (fun x : real => @lem5269463 x)). Qed.
Lemma lem5269465 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5269466 : term49 = term49.
Proof. exact (MK_COMB (@lem5269465) (@lem5269464)). Qed.
Lemma lem5269467 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5269468 : term18 = term18.
Proof. exact (MK_COMB (@lem5269467) (@lem5269466)). Qed.
Lemma lem5269469 : term20 = term20.
Proof. exact (MK_COMB (@lem5269468) (@lem5269448)). Qed.
Lemma lem5269474 (s : real -> Prop) (y : real) (x : real) : (term24 s y x) = (term24 s y x).
Proof. exact (eq_refl (term24 s y x)). Qed.
Lemma lem5269475 (s : real -> Prop) (y : real) : (term25 s y) = (term25 s y).
Proof. exact (fun_ext (fun x : real => @lem5269474 s y x)). Qed.
Lemma lem5269476 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5269477 (s : real -> Prop) (y : real) : (term26 s y) = (term26 s y).
Proof. exact (MK_COMB (@lem5269476) (@lem5269475 s y)). Qed.
Lemma lem5269480 (y : real) (s : real -> Prop) : (term50 y s) = (term50 y s).
Proof. exact (eq_refl (term50 y s)). Qed.
Lemma lem5269481 (s : real -> Prop) (y : real) : ((term23 y s) = (term26 s y)) = ((term23 y s) = (term26 s y)).
Proof. exact (MK_COMB (@lem5269480 y s) (@lem5269477 s y)). Qed.
Lemma lem5269486 (s : real -> Prop) (b : real) (x : real) : (term24 s b x) = (term24 s b x).
Proof. exact (eq_refl (term24 s b x)). Qed.
Lemma lem5269487 (s : real -> Prop) (b : real) : (term25 s b) = (term25 s b).
Proof. exact (fun_ext (fun x : real => @lem5269486 s b x)). Qed.
Lemma lem5269488 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5269489 (s : real -> Prop) (b : real) : (term26 s b) = (term26 s b).
Proof. exact (MK_COMB (@lem5269488) (@lem5269487 s b)). Qed.
Lemma lem5269490 (s : real -> Prop) : (term36 s) = (term36 s).
Proof. exact (fun_ext (fun b : real => @lem5269489 s b)). Qed.
Lemma lem5269491 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5269492 (s : real -> Prop) : (term37 s) = (term37 s).
Proof. exact (MK_COMB (@lem5269491) (@lem5269490 s)). Qed.
Lemma lem5269497 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (eq_refl (term38 s)). Qed.
Lemma lem5269498 (s : real -> Prop) : (term39 s) = (term39 s).
Proof. exact (MK_COMB (@lem5269497 s) (@lem5269492 s)). Qed.
Lemma lem5269499 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5269500 (s : real -> Prop) : (term40 s) = (term40 s).
Proof. exact (MK_COMB (@lem5269499) (@lem5269498 s)). Qed.
Lemma lem5269501 (s : real -> Prop) (y : real) : (term51 s y) = (term51 s y).
Proof. exact (MK_COMB (@lem5269500 s) (@lem5269481 s y)). Qed.
Lemma lem5269502 (s : real -> Prop) : (term52 s) = (term52 s).
Proof. exact (fun_ext (fun y : real => @lem5269501 s y)). Qed.
Lemma lem5269503 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5269504 (s : real -> Prop) : (term53 s) = (term53 s).
Proof. exact (MK_COMB (@lem5269503) (@lem5269502 s)). Qed.
Lemma lem5269505 : term54 = term54.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5269504 s)). Qed.
Lemma lem5269506 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5269507 : term8 = term8.
Proof. exact (MK_COMB (@lem5269506) (@lem5269505)). Qed.
Lemma lem5269508 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5269509 : term10 = term10.
Proof. exact (MK_COMB (@lem5269508) (@lem5269507)). Qed.
Lemma lem5269510 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5269511 : term21 = term21.
Proof. exact (MK_COMB (@lem5269510) (@lem5269509)). Qed.
Lemma lem5269512 : term22 = term22.
Proof. exact (MK_COMB (@lem5269511) (@lem5269469)). Qed.
Lemma lem5269629 : term11 = term22.
Proof. exact (TRANS (@lem5269397) (@lem5269512)). Qed.
Lemma lem5269630 : term22 = term11.
Proof. exact (SYM (@lem5269629)). Qed.
Lemma lem5269631 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5269632 (h1 : term49) : term49.
Proof. exact (h1). Qed.
Lemma lem5269633 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem5269641 (s : real -> Prop) (b : real) (x : real) : (term24 s b x) = (term55 s b x).
Proof. exact (@lem17265 (@IN real x s) (real_le b x)). Qed.
Lemma lem5269642 (s : real -> Prop) (b : real) : (term25 s b) = (term56 s b).
Proof. exact (fun_ext (fun x : real => @lem5269641 s b x)). Qed.
Lemma lem5269643 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5269644 (s : real -> Prop) (b : real) : (term26 s b) = (term57 s b).
Proof. exact (MK_COMB (@lem5269643) (@lem5269642 s b)). Qed.
Lemma lem5269645 (s : real -> Prop) : (term36 s) = (term58 s).
Proof. exact (fun_ext (fun b : real => @lem5269644 s b)). Qed.
Lemma lem5269646 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5269647 (s : real -> Prop) : (term37 s) = (term59 s).
Proof. exact (MK_COMB (@lem5269646) (@lem5269645 s)). Qed.
Lemma lem5269649 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (eq_refl (term38 s)). Qed.
Lemma lem5269650 (s : real -> Prop) : (term39 s) = (term60 s).
Proof. exact (MK_COMB (@lem5269649 s) (@lem5269647 s)). Qed.
Lemma lem5269661 (s : real -> Prop) (y : real) (x : real) : (term61 s y x) = (term62 s y x).
Proof. exact (@lem17362 (@IN real x s) (real_le y x)). Qed.
Lemma lem5269666 (s : real -> Prop) (y : real) (x : real) : (term24 s y x) = (term55 s y x).
Proof. exact (@lem17265 (@IN real x s) (real_le y x)). Qed.
Lemma lem5269667 (P : real -> Prop) : (term63 P) = (term64 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5269668 (s : real -> Prop) (y : real) : (term65 s y) = (term66 s y).
Proof. exact (@lem5269667 (term25 s y)). Qed.
Lemma lem5269669 (s : real -> Prop) (y : real) (x : real) : (term67 s y x) = (term24 s y x).
Proof. exact (eq_refl (term67 s y x)). Qed.
Lemma lem5269670 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5269671 (s : real -> Prop) (y : real) (x : real) : (term68 s y x) = (term61 s y x).
Proof. exact (MK_COMB (@lem5269670) (@lem5269669 s y x)). Qed.
Lemma lem5269672 (s : real -> Prop) (y : real) (x : real) : (term68 s y x) = (term62 s y x).
Proof. exact (TRANS (@lem5269671 s y x) (@lem5269661 s y x)). Qed.
Lemma lem5269673 (s : real -> Prop) (y : real) : (term69 s y) = (term70 s y).
Proof. exact (fun_ext (fun x : real => @lem5269672 s y x)). Qed.
Lemma lem5269674 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5269675 (s : real -> Prop) (y : real) : (term66 s y) = (term71 s y).
Proof. exact (MK_COMB (@lem5269674) (@lem5269673 s y)). Qed.
Lemma lem5269676 (s : real -> Prop) (y : real) : (term65 s y) = (term71 s y).
Proof. exact (TRANS (@lem5269668 s y) (@lem5269675 s y)). Qed.
Lemma lem5269677 (s : real -> Prop) (y : real) : (term25 s y) = (term56 s y).
Proof. exact (fun_ext (fun x : real => @lem5269666 s y x)). Qed.
Lemma lem5269678 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5269679 (s : real -> Prop) (y : real) : (term26 s y) = (term57 s y).
Proof. exact (MK_COMB (@lem5269678) (@lem5269677 s y)). Qed.
Lemma lem5269681 (y : real) (s : real -> Prop) : (term72 y s) = (term72 y s).
Proof. exact (eq_refl (term72 y s)). Qed.
Lemma lem5269682 (s : real -> Prop) (y : real) : (term73 s y) = (term74 s y).
Proof. exact (MK_COMB (@lem5269681 y s) (@lem5269679 s y)). Qed.
Lemma lem5269684 (y : real) (s : real -> Prop) : (term75 y s) = (term75 y s).
Proof. exact (eq_refl (term75 y s)). Qed.
Lemma lem5269685 (s : real -> Prop) (y : real) : (term76 s y) = (term77 s y).
Proof. exact (MK_COMB (@lem5269684 y s) (@lem5269676 s y)). Qed.
Lemma lem5269686 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5269687 (s : real -> Prop) (y : real) : (term78 s y) = (term79 s y).
Proof. exact (MK_COMB (@lem5269686) (@lem5269685 s y)). Qed.
Lemma lem5269688 (s : real -> Prop) (y : real) : (term80 s y) = (term81 s y).
Proof. exact (MK_COMB (@lem5269687 s y) (@lem5269682 s y)). Qed.
Lemma lem5269689 (s : real -> Prop) (y : real) : (term82 s y) = (term80 s y).
Proof. exact (@lem17646 (term23 y s) (term26 s y)). Qed.
Lemma lem5269690 (s : real -> Prop) (y : real) : (term82 s y) = (term81 s y).
Proof. exact (TRANS (@lem5269689 s y) (@lem5269688 s y)). Qed.
Lemma lem5269691 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5269692 (s : real -> Prop) : (term83 s) = (term84 s).
Proof. exact (MK_COMB (@lem5269691) (@lem5269650 s)). Qed.
Lemma lem5269693 (s : real -> Prop) (y : real) : (term85 s y) = (term86 s y).
Proof. exact (MK_COMB (@lem5269692 s) (@lem5269690 s y)). Qed.
Lemma lem5269694 (s : real -> Prop) (y : real) : (term87 s y) = (term85 s y).
Proof. exact (@lem17362 (term39 s) ((term23 y s) = (term26 s y))). Qed.
Lemma lem5269695 (s : real -> Prop) (y : real) : (term87 s y) = (term86 s y).
Proof. exact (TRANS (@lem5269694 s y) (@lem5269693 s y)). Qed.
Lemma lem5269696 (P : real -> Prop) : (term63 P) = (term64 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5269697 (s : real -> Prop) : (term88 s) = (term89 s).
Proof. exact (@lem5269696 (term52 s)). Qed.
Lemma lem5269698 (s : real -> Prop) (y : real) : (term90 s y) = (term51 s y).
Proof. exact (eq_refl (term90 s y)). Qed.
Lemma lem5269699 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5269700 (s : real -> Prop) (y : real) : (term91 s y) = (term87 s y).
Proof. exact (MK_COMB (@lem5269699) (@lem5269698 s y)). Qed.
Lemma lem5269701 (s : real -> Prop) (y : real) : (term91 s y) = (term86 s y).
Proof. exact (TRANS (@lem5269700 s y) (@lem5269695 s y)). Qed.
Lemma lem5269702 (s : real -> Prop) : (term92 s) = (term93 s).
Proof. exact (fun_ext (fun y : real => @lem5269701 s y)). Qed.
Lemma lem5269703 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5269704 (s : real -> Prop) : (term89 s) = (term94 s).
Proof. exact (MK_COMB (@lem5269703) (@lem5269702 s)). Qed.
Lemma lem5269705 (s : real -> Prop) : (term88 s) = (term94 s).
Proof. exact (TRANS (@lem5269697 s) (@lem5269704 s)). Qed.
Lemma lem5269706 (P : type1022) : (term95 P) = (term96 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5269707 : term10 = term97.
Proof. exact (@lem5269706 term54). Qed.
Lemma lem5269708 (s : real -> Prop) : (term98 s) = (term53 s).
Proof. exact (eq_refl (term98 s)). Qed.
Lemma lem5269709 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5269710 (s : real -> Prop) : (term99 s) = (term88 s).
Proof. exact (MK_COMB (@lem5269709) (@lem5269708 s)). Qed.
Lemma lem5269711 (s : real -> Prop) : (term99 s) = (term94 s).
Proof. exact (TRANS (@lem5269710 s) (@lem5269705 s)). Qed.
Lemma lem5269712 : term100 = term101.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5269711 s)). Qed.
Lemma lem5269713 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5269714 : term97 = term102.
Proof. exact (MK_COMB (@lem5269713) (@lem5269712)). Qed.
Lemma lem5269715 : term10 = term102.
Proof. exact (TRANS (@lem5269707) (@lem5269714)). Qed.
Lemma lem5269721 {A : Type'} (P : Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem5269722 (P : Prop) (Q : real -> Prop) : (term105 P Q) = (term106 P Q).
Proof. exact (@lem5269721 real P Q). Qed.
Lemma lem5269723 (s : real -> Prop) : (term107 s) = (term108 s).
Proof. exact (@lem5269722 (term60 s) (term109 s)). Qed.
Lemma lem5269724 (s : real -> Prop) (y : real) : (term110 s y) = (term81 s y).
Proof. exact (eq_refl (term110 s y)). Qed.
Lemma lem5269725 (s : real -> Prop) : (term84 s) = (term84 s).
Proof. exact (eq_refl (term84 s)). Qed.
Lemma lem5269726 (s : real -> Prop) (y : real) : (term111 s y) = (term86 s y).
Proof. exact (MK_COMB (@lem5269725 s) (@lem5269724 s y)). Qed.
Lemma lem5269727 (s : real -> Prop) : (term112 s) = (term93 s).
Proof. exact (fun_ext (fun y : real => @lem5269726 s y)). Qed.
Lemma lem5269728 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5269729 (s : real -> Prop) : (term107 s) = (term94 s).
Proof. exact (MK_COMB (@lem5269728) (@lem5269727 s)). Qed.
Lemma lem5269730 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5269731 (s : real -> Prop) : (term113 s) = (term114 s).
Proof. exact (MK_COMB (@lem5269730) (@lem5269729 s)). Qed.
Lemma lem5269732 (s : real -> Prop) (y : real) : (term110 s y) = (term81 s y).
Proof. exact (eq_refl (term110 s y)). Qed.
Lemma lem5269733 (s : real -> Prop) : (term115 s) = (term109 s).
Proof. exact (fun_ext (fun y : real => @lem5269732 s y)). Qed.
Lemma lem5269734 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5269735 (s : real -> Prop) : (term116 s) = (term117 s).
Proof. exact (MK_COMB (@lem5269734) (@lem5269733 s)). Qed.
Lemma lem5269736 (s : real -> Prop) : (term84 s) = (term84 s).
Proof. exact (eq_refl (term84 s)). Qed.
Lemma lem5269737 (s : real -> Prop) : (term108 s) = (term118 s).
Proof. exact (MK_COMB (@lem5269736 s) (@lem5269735 s)). Qed.
Lemma lem5269738 (s : real -> Prop) : ((term107 s) = (term108 s)) = ((term94 s) = (term118 s)).
Proof. exact (MK_COMB (@lem5269731 s) (@lem5269737 s)). Qed.
Lemma lem5269739 (s : real -> Prop) : (term94 s) = (term118 s).
Proof. exact (EQ_MP (@lem5269738 s) (@lem5269723 s)). Qed.
Lemma lem5269793 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term119 A P Q) = (term120 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5269794 (P : real -> Prop) (Q : real -> Prop) : (term121 P Q) = (term122 P Q).
Proof. exact (@lem5269793 real P Q). Qed.
Lemma lem5269795 (s : real -> Prop) : (term123 s) = (term124 s).
Proof. exact (@lem5269794 (term125 s) (term126 s)). Qed.
Lemma lem5269796 (s : real -> Prop) (y : real) : (term127 s y) = (term77 s y).
Proof. exact (eq_refl (term127 s y)). Qed.
Lemma lem5269797 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5269798 (s : real -> Prop) (y : real) : (term128 s y) = (term79 s y).
Proof. exact (MK_COMB (@lem5269797) (@lem5269796 s y)). Qed.
Lemma lem5269799 (s : real -> Prop) (y : real) : (term129 s y) = (term74 s y).
Proof. exact (eq_refl (term129 s y)). Qed.
Lemma lem5269800 (s : real -> Prop) (y : real) : (term130 s y) = (term81 s y).
Proof. exact (MK_COMB (@lem5269798 s y) (@lem5269799 s y)). Qed.
Lemma lem5269801 (s : real -> Prop) : (term131 s) = (term109 s).
Proof. exact (fun_ext (fun y : real => @lem5269800 s y)). Qed.
Lemma lem5269802 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5269803 (s : real -> Prop) : (term123 s) = (term117 s).
Proof. exact (MK_COMB (@lem5269802) (@lem5269801 s)). Qed.
Lemma lem5269804 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5269805 (s : real -> Prop) : (term132 s) = (term133 s).
Proof. exact (MK_COMB (@lem5269804) (@lem5269803 s)). Qed.
Lemma lem5269806 (s : real -> Prop) (y : real) : (term127 s y) = (term77 s y).
Proof. exact (eq_refl (term127 s y)). Qed.
Lemma lem5269807 (s : real -> Prop) : (term134 s) = (term125 s).
Proof. exact (fun_ext (fun y : real => @lem5269806 s y)). Qed.
Lemma lem5269808 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5269809 (s : real -> Prop) : (term135 s) = (term136 s).
Proof. exact (MK_COMB (@lem5269808) (@lem5269807 s)). Qed.
Lemma lem5269810 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5269811 (s : real -> Prop) : (term137 s) = (term138 s).
Proof. exact (MK_COMB (@lem5269810) (@lem5269809 s)). Qed.
Lemma lem5269812 (s : real -> Prop) (y : real) : (term129 s y) = (term74 s y).
Proof. exact (eq_refl (term129 s y)). Qed.
Lemma lem5269813 (s : real -> Prop) : (term139 s) = (term126 s).
Proof. exact (fun_ext (fun y : real => @lem5269812 s y)). Qed.
Lemma lem5269814 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5269815 (s : real -> Prop) : (term140 s) = (term141 s).
Proof. exact (MK_COMB (@lem5269814) (@lem5269813 s)). Qed.
Lemma lem5269816 (s : real -> Prop) : (term124 s) = (term142 s).
Proof. exact (MK_COMB (@lem5269811 s) (@lem5269815 s)). Qed.
Lemma lem5269817 (s : real -> Prop) : ((term123 s) = (term124 s)) = ((term117 s) = (term142 s)).
Proof. exact (MK_COMB (@lem5269805 s) (@lem5269816 s)). Qed.
Lemma lem5269818 (s : real -> Prop) : (term117 s) = (term142 s).
Proof. exact (EQ_MP (@lem5269817 s) (@lem5269795 s)). Qed.
Lemma lem5270011 (s : real -> Prop) : (term84 s) = (term84 s).
Proof. exact (eq_refl (term84 s)). Qed.
Lemma lem5270012 (s : real -> Prop) : (term118 s) = (term143 s).
Proof. exact (MK_COMB (@lem5270011 s) (@lem5269818 s)). Qed.
Lemma lem5270013 (s : real -> Prop) : (term94 s) = (term143 s).
Proof. exact (TRANS (@lem5269739 s) (@lem5270012 s)). Qed.
Lemma lem5270014 : term101 = term144.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5270013 s)). Qed.
Lemma lem5270015 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5270016 : term102 = term145.
Proof. exact (MK_COMB (@lem5270015) (@lem5270014)). Qed.
Lemma lem5270066 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5270067 (P : Prop) (Q : real -> Prop) : (term106 P Q) = (term105 P Q).
Proof. exact (@lem5270066 real P Q). Qed.
Lemma lem5270068 (s : real -> Prop) : (term146 s) = (term147 s).
Proof. exact (@lem5270067 (term148 s) (term58 s)). Qed.
Lemma lem5270069 (s : real -> Prop) (b : real) : (term149 s b) = (term57 s b).
Proof. exact (eq_refl (term149 s b)). Qed.
Lemma lem5270070 (s : real -> Prop) : (term150 s) = (term58 s).
Proof. exact (fun_ext (fun b : real => @lem5270069 s b)). Qed.
Lemma lem5270071 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270072 (s : real -> Prop) : (term151 s) = (term59 s).
Proof. exact (MK_COMB (@lem5270071) (@lem5270070 s)). Qed.
Lemma lem5270073 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (eq_refl (term38 s)). Qed.
Lemma lem5270074 (s : real -> Prop) : (term146 s) = (term60 s).
Proof. exact (MK_COMB (@lem5270073 s) (@lem5270072 s)). Qed.
Lemma lem5270075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5270076 (s : real -> Prop) : (term152 s) = (term153 s).
Proof. exact (MK_COMB (@lem5270075) (@lem5270074 s)). Qed.
Lemma lem5270077 (s : real -> Prop) (b : real) : (term149 s b) = (term57 s b).
Proof. exact (eq_refl (term149 s b)). Qed.
Lemma lem5270078 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (eq_refl (term38 s)). Qed.
Lemma lem5270079 (s : real -> Prop) (b : real) : (term154 s b) = (term155 s b).
Proof. exact (MK_COMB (@lem5270078 s) (@lem5270077 s b)). Qed.
Lemma lem5270080 (s : real -> Prop) : (term156 s) = (term157 s).
Proof. exact (fun_ext (fun b : real => @lem5270079 s b)). Qed.
Lemma lem5270081 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270082 (s : real -> Prop) : (term147 s) = (term158 s).
Proof. exact (MK_COMB (@lem5270081) (@lem5270080 s)). Qed.
Lemma lem5270083 (s : real -> Prop) : ((term146 s) = (term147 s)) = ((term60 s) = (term158 s)).
Proof. exact (MK_COMB (@lem5270076 s) (@lem5270082 s)). Qed.
Lemma lem5270084 (s : real -> Prop) : (term60 s) = (term158 s).
Proof. exact (EQ_MP (@lem5270083 s) (@lem5270068 s)). Qed.
Lemma lem5270085 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5270086 (s : real -> Prop) : (term84 s) = (term159 s).
Proof. exact (MK_COMB (@lem5270085) (@lem5270084 s)). Qed.
Lemma lem5270088 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5270089 (P : Prop) (Q : real -> Prop) : (term106 P Q) = (term105 P Q).
Proof. exact (@lem5270088 real P Q). Qed.
Lemma lem5270090 (s : real -> Prop) (y : real) : (term160 s y) = (term161 s y).
Proof. exact (@lem5270089 (term23 y s) (term70 s y)). Qed.
Lemma lem5270091 (s : real -> Prop) (y : real) (x : real) : (term162 s y x) = (term62 s y x).
Proof. exact (eq_refl (term162 s y x)). Qed.
Lemma lem5270092 (s : real -> Prop) (y : real) : (term163 s y) = (term70 s y).
Proof. exact (fun_ext (fun x : real => @lem5270091 s y x)). Qed.
Lemma lem5270093 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270094 (s : real -> Prop) (y : real) : (term164 s y) = (term71 s y).
Proof. exact (MK_COMB (@lem5270093) (@lem5270092 s y)). Qed.
Lemma lem5270095 (y : real) (s : real -> Prop) : (term75 y s) = (term75 y s).
Proof. exact (eq_refl (term75 y s)). Qed.
Lemma lem5270096 (s : real -> Prop) (y : real) : (term160 s y) = (term77 s y).
Proof. exact (MK_COMB (@lem5270095 y s) (@lem5270094 s y)). Qed.
Lemma lem5270097 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5270098 (s : real -> Prop) (y : real) : (term165 s y) = (term166 s y).
Proof. exact (MK_COMB (@lem5270097) (@lem5270096 s y)). Qed.
Lemma lem5270099 (s : real -> Prop) (y : real) (x : real) : (term162 s y x) = (term62 s y x).
Proof. exact (eq_refl (term162 s y x)). Qed.
Lemma lem5270100 (y : real) (s : real -> Prop) : (term75 y s) = (term75 y s).
Proof. exact (eq_refl (term75 y s)). Qed.
Lemma lem5270101 (s : real -> Prop) (y : real) (x : real) : (term167 s y x) = (term168 s y x).
Proof. exact (MK_COMB (@lem5270100 y s) (@lem5270099 s y x)). Qed.
Lemma lem5270102 (s : real -> Prop) (y : real) : (term169 s y) = (term170 s y).
Proof. exact (fun_ext (fun x : real => @lem5270101 s y x)). Qed.
Lemma lem5270103 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270104 (s : real -> Prop) (y : real) : (term161 s y) = (term171 s y).
Proof. exact (MK_COMB (@lem5270103) (@lem5270102 s y)). Qed.
Lemma lem5270105 (s : real -> Prop) (y : real) : ((term160 s y) = (term161 s y)) = ((term77 s y) = (term171 s y)).
Proof. exact (MK_COMB (@lem5270098 s y) (@lem5270104 s y)). Qed.
Lemma lem5270106 (s : real -> Prop) (y : real) : (term77 s y) = (term171 s y).
Proof. exact (EQ_MP (@lem5270105 s y) (@lem5270090 s y)). Qed.
Lemma lem5270107 (s : real -> Prop) : (term125 s) = (term172 s).
Proof. exact (fun_ext (fun y : real => @lem5270106 s y)). Qed.
Lemma lem5270108 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270109 (s : real -> Prop) : (term136 s) = (term173 s).
Proof. exact (MK_COMB (@lem5270108) (@lem5270107 s)). Qed.
Lemma lem5270110 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5270111 (s : real -> Prop) : (term138 s) = (term174 s).
Proof. exact (MK_COMB (@lem5270110) (@lem5270109 s)). Qed.
Lemma lem5270112 (s : real -> Prop) : (term141 s) = (term141 s).
Proof. exact (eq_refl (term141 s)). Qed.
Lemma lem5270113 (s : real -> Prop) : (term142 s) = (term175 s).
Proof. exact (MK_COMB (@lem5270111 s) (@lem5270112 s)). Qed.
Lemma lem5270115 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term120 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5270116 (P : real -> Prop) (Q : real -> Prop) : (term122 P Q) = (term121 P Q).
Proof. exact (@lem5270115 real P Q). Qed.
Lemma lem5270117 (s : real -> Prop) : (term176 s) = (term177 s).
Proof. exact (@lem5270116 (term172 s) (term126 s)). Qed.
Lemma lem5270118 (s : real -> Prop) (y : real) : (term178 s y) = (term171 s y).
Proof. exact (eq_refl (term178 s y)). Qed.
Lemma lem5270119 (s : real -> Prop) : (term179 s) = (term172 s).
Proof. exact (fun_ext (fun y : real => @lem5270118 s y)). Qed.
Lemma lem5270120 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270121 (s : real -> Prop) : (term180 s) = (term173 s).
Proof. exact (MK_COMB (@lem5270120) (@lem5270119 s)). Qed.
Lemma lem5270122 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5270123 (s : real -> Prop) : (term181 s) = (term174 s).
Proof. exact (MK_COMB (@lem5270122) (@lem5270121 s)). Qed.
Lemma lem5270124 (s : real -> Prop) (y : real) : (term129 s y) = (term74 s y).
Proof. exact (eq_refl (term129 s y)). Qed.
Lemma lem5270125 (s : real -> Prop) : (term139 s) = (term126 s).
Proof. exact (fun_ext (fun y : real => @lem5270124 s y)). Qed.
Lemma lem5270126 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270127 (s : real -> Prop) : (term140 s) = (term141 s).
Proof. exact (MK_COMB (@lem5270126) (@lem5270125 s)). Qed.
Lemma lem5270128 (s : real -> Prop) : (term176 s) = (term175 s).
Proof. exact (MK_COMB (@lem5270123 s) (@lem5270127 s)). Qed.
Lemma lem5270129 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5270130 (s : real -> Prop) : (term182 s) = (term183 s).
Proof. exact (MK_COMB (@lem5270129) (@lem5270128 s)). Qed.
Lemma lem5270131 (s : real -> Prop) (y : real) : (term178 s y) = (term171 s y).
Proof. exact (eq_refl (term178 s y)). Qed.
Lemma lem5270132 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5270133 (s : real -> Prop) (y : real) : (term184 s y) = (term185 s y).
Proof. exact (MK_COMB (@lem5270132) (@lem5270131 s y)). Qed.
Lemma lem5270134 (s : real -> Prop) (y : real) : (term129 s y) = (term74 s y).
Proof. exact (eq_refl (term129 s y)). Qed.
Lemma lem5270135 (s : real -> Prop) (y : real) : (term186 s y) = (term187 s y).
Proof. exact (MK_COMB (@lem5270133 s y) (@lem5270134 s y)). Qed.
Lemma lem5270136 (s : real -> Prop) : (term188 s) = (term189 s).
Proof. exact (fun_ext (fun y : real => @lem5270135 s y)). Qed.
Lemma lem5270137 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270138 (s : real -> Prop) : (term177 s) = (term190 s).
Proof. exact (MK_COMB (@lem5270137) (@lem5270136 s)). Qed.
Lemma lem5270139 (s : real -> Prop) : ((term176 s) = (term177 s)) = ((term175 s) = (term190 s)).
Proof. exact (MK_COMB (@lem5270130 s) (@lem5270138 s)). Qed.
Lemma lem5270140 (s : real -> Prop) : (term175 s) = (term190 s).
Proof. exact (EQ_MP (@lem5270139 s) (@lem5270117 s)). Qed.
Lemma lem5270142 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5270143 (P : real -> Prop) (Q : Prop) : (term193 P Q) = (term194 P Q).
Proof. exact (@lem5270142 real P Q). Qed.
Lemma lem5270144 (s : real -> Prop) (y : real) : (term195 s y) = (term196 s y).
Proof. exact (@lem5270143 (term170 s y) (term74 s y)). Qed.
Lemma lem5270145 (s : real -> Prop) (y : real) (x : real) : (term197 s y x) = (term168 s y x).
Proof. exact (eq_refl (term197 s y x)). Qed.
Lemma lem5270146 (s : real -> Prop) (y : real) : (term198 s y) = (term170 s y).
Proof. exact (fun_ext (fun x : real => @lem5270145 s y x)). Qed.
Lemma lem5270147 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270148 (s : real -> Prop) (y : real) : (term199 s y) = (term171 s y).
Proof. exact (MK_COMB (@lem5270147) (@lem5270146 s y)). Qed.
Lemma lem5270149 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5270150 (s : real -> Prop) (y : real) : (term200 s y) = (term185 s y).
Proof. exact (MK_COMB (@lem5270149) (@lem5270148 s y)). Qed.
Lemma lem5270151 (s : real -> Prop) (y : real) : (term74 s y) = (term74 s y).
Proof. exact (eq_refl (term74 s y)). Qed.
Lemma lem5270152 (s : real -> Prop) (y : real) : (term195 s y) = (term187 s y).
Proof. exact (MK_COMB (@lem5270150 s y) (@lem5270151 s y)). Qed.
Lemma lem5270153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5270154 (s : real -> Prop) (y : real) : (term201 s y) = (term202 s y).
Proof. exact (MK_COMB (@lem5270153) (@lem5270152 s y)). Qed.
Lemma lem5270155 (s : real -> Prop) (y : real) (x : real) : (term197 s y x) = (term168 s y x).
Proof. exact (eq_refl (term197 s y x)). Qed.
Lemma lem5270156 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5270157 (s : real -> Prop) (y : real) (x : real) : (term203 s y x) = (term204 s y x).
Proof. exact (MK_COMB (@lem5270156) (@lem5270155 s y x)). Qed.
Lemma lem5270158 (s : real -> Prop) (y : real) : (term74 s y) = (term74 s y).
Proof. exact (eq_refl (term74 s y)). Qed.
Lemma lem5270159 (x : real) (s : real -> Prop) (y : real) : (term205 x s y) = (term206 x s y).
Proof. exact (MK_COMB (@lem5270157 s y x) (@lem5270158 s y)). Qed.
Lemma lem5270160 (s : real -> Prop) (y : real) : (term207 s y) = (term208 s y).
Proof. exact (fun_ext (fun x : real => @lem5270159 x s y)). Qed.
Lemma lem5270161 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270162 (s : real -> Prop) (y : real) : (term196 s y) = (term209 s y).
Proof. exact (MK_COMB (@lem5270161) (@lem5270160 s y)). Qed.
Lemma lem5270163 (s : real -> Prop) (y : real) : ((term195 s y) = (term196 s y)) = ((term187 s y) = (term209 s y)).
Proof. exact (MK_COMB (@lem5270154 s y) (@lem5270162 s y)). Qed.
Lemma lem5270164 (s : real -> Prop) (y : real) : (term187 s y) = (term209 s y).
Proof. exact (EQ_MP (@lem5270163 s y) (@lem5270144 s y)). Qed.
Lemma lem5270165 (s : real -> Prop) : (term189 s) = (term210 s).
Proof. exact (fun_ext (fun y : real => @lem5270164 s y)). Qed.
Lemma lem5270166 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270167 (s : real -> Prop) : (term190 s) = (term211 s).
Proof. exact (MK_COMB (@lem5270166) (@lem5270165 s)). Qed.
Lemma lem5270168 (s : real -> Prop) : (term175 s) = (term211 s).
Proof. exact (TRANS (@lem5270140 s) (@lem5270167 s)). Qed.
Lemma lem5270169 (s : real -> Prop) : (term142 s) = (term211 s).
Proof. exact (TRANS (@lem5270113 s) (@lem5270168 s)). Qed.
Lemma lem5270170 (s : real -> Prop) : (term143 s) = (term212 s).
Proof. exact (MK_COMB (@lem5270086 s) (@lem5270169 s)). Qed.
Lemma lem5270172 {A : Type'} (P : A -> Prop) (Q : Prop) : (term213 A P Q) = (term214 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5270173 (P : real -> Prop) (Q : Prop) : (term215 P Q) = (term216 P Q).
Proof. exact (@lem5270172 real P Q). Qed.
Lemma lem5270174 (s : real -> Prop) : (term217 s) = (term218 s).
Proof. exact (@lem5270173 (term157 s) (term211 s)). Qed.
Lemma lem5270175 (s : real -> Prop) (b : real) : (term219 s b) = (term155 s b).
Proof. exact (eq_refl (term219 s b)). Qed.
Lemma lem5270176 (s : real -> Prop) : (term220 s) = (term157 s).
Proof. exact (fun_ext (fun b : real => @lem5270175 s b)). Qed.
Lemma lem5270177 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270178 (s : real -> Prop) : (term221 s) = (term158 s).
Proof. exact (MK_COMB (@lem5270177) (@lem5270176 s)). Qed.
Lemma lem5270179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5270180 (s : real -> Prop) : (term222 s) = (term159 s).
Proof. exact (MK_COMB (@lem5270179) (@lem5270178 s)). Qed.
Lemma lem5270181 (s : real -> Prop) : (term211 s) = (term211 s).
Proof. exact (eq_refl (term211 s)). Qed.
Lemma lem5270182 (s : real -> Prop) : (term217 s) = (term212 s).
Proof. exact (MK_COMB (@lem5270180 s) (@lem5270181 s)). Qed.
Lemma lem5270183 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5270184 (s : real -> Prop) : (term223 s) = (term224 s).
Proof. exact (MK_COMB (@lem5270183) (@lem5270182 s)). Qed.
Lemma lem5270185 (s : real -> Prop) (b : real) : (term219 s b) = (term155 s b).
Proof. exact (eq_refl (term219 s b)). Qed.
Lemma lem5270186 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5270187 (s : real -> Prop) (b : real) : (term225 s b) = (term226 s b).
Proof. exact (MK_COMB (@lem5270186) (@lem5270185 s b)). Qed.
Lemma lem5270188 (s : real -> Prop) : (term211 s) = (term211 s).
Proof. exact (eq_refl (term211 s)). Qed.
Lemma lem5270189 (b : real) (s : real -> Prop) : (term227 b s) = (term228 b s).
Proof. exact (MK_COMB (@lem5270187 s b) (@lem5270188 s)). Qed.
Lemma lem5270190 (s : real -> Prop) : (term229 s) = (term230 s).
Proof. exact (fun_ext (fun b : real => @lem5270189 b s)). Qed.
Lemma lem5270191 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270192 (s : real -> Prop) : (term218 s) = (term231 s).
Proof. exact (MK_COMB (@lem5270191) (@lem5270190 s)). Qed.
Lemma lem5270193 (s : real -> Prop) : ((term217 s) = (term218 s)) = ((term212 s) = (term231 s)).
Proof. exact (MK_COMB (@lem5270184 s) (@lem5270192 s)). Qed.
Lemma lem5270194 (s : real -> Prop) : (term212 s) = (term231 s).
Proof. exact (EQ_MP (@lem5270193 s) (@lem5270174 s)). Qed.
Lemma lem5270196 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5270197 (P : Prop) (Q : real -> Prop) : (term106 P Q) = (term105 P Q).
Proof. exact (@lem5270196 real P Q). Qed.
Lemma lem5270198 (b : real) (s : real -> Prop) : (term232 b s) = (term233 b s).
Proof. exact (@lem5270197 (term155 s b) (term210 s)). Qed.
Lemma lem5270199 (s : real -> Prop) (y : real) : (term234 s y) = (term209 s y).
Proof. exact (eq_refl (term234 s y)). Qed.
Lemma lem5270200 (s : real -> Prop) : (term235 s) = (term210 s).
Proof. exact (fun_ext (fun y : real => @lem5270199 s y)). Qed.
Lemma lem5270201 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270202 (s : real -> Prop) : (term236 s) = (term211 s).
Proof. exact (MK_COMB (@lem5270201) (@lem5270200 s)). Qed.
Lemma lem5270203 (s : real -> Prop) (b : real) : (term226 s b) = (term226 s b).
Proof. exact (eq_refl (term226 s b)). Qed.
Lemma lem5270204 (b : real) (s : real -> Prop) : (term232 b s) = (term228 b s).
Proof. exact (MK_COMB (@lem5270203 s b) (@lem5270202 s)). Qed.
Lemma lem5270205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5270206 (b : real) (s : real -> Prop) : (term237 b s) = (term238 b s).
Proof. exact (MK_COMB (@lem5270205) (@lem5270204 b s)). Qed.
Lemma lem5270207 (s : real -> Prop) (y : real) : (term234 s y) = (term209 s y).
Proof. exact (eq_refl (term234 s y)). Qed.
Lemma lem5270208 (s : real -> Prop) (b : real) : (term226 s b) = (term226 s b).
Proof. exact (eq_refl (term226 s b)). Qed.
Lemma lem5270209 (b : real) (s : real -> Prop) (y : real) : (term239 b s y) = (term240 b s y).
Proof. exact (MK_COMB (@lem5270208 s b) (@lem5270207 s y)). Qed.
Lemma lem5270210 (b : real) (s : real -> Prop) : (term241 b s) = (term242 b s).
Proof. exact (fun_ext (fun y : real => @lem5270209 b s y)). Qed.
Lemma lem5270211 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270212 (b : real) (s : real -> Prop) : (term233 b s) = (term243 b s).
Proof. exact (MK_COMB (@lem5270211) (@lem5270210 b s)). Qed.
Lemma lem5270213 (b : real) (s : real -> Prop) : ((term232 b s) = (term233 b s)) = ((term228 b s) = (term243 b s)).
Proof. exact (MK_COMB (@lem5270206 b s) (@lem5270212 b s)). Qed.
Lemma lem5270214 (b : real) (s : real -> Prop) : (term228 b s) = (term243 b s).
Proof. exact (EQ_MP (@lem5270213 b s) (@lem5270198 b s)). Qed.
Lemma lem5270216 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5270217 (P : Prop) (Q : real -> Prop) : (term106 P Q) = (term105 P Q).
Proof. exact (@lem5270216 real P Q). Qed.
Lemma lem5270218 (b : real) (s : real -> Prop) (y : real) : (term244 b s y) = (term245 b s y).
Proof. exact (@lem5270217 (term155 s b) (term208 s y)). Qed.
Lemma lem5270219 (x : real) (s : real -> Prop) (y : real) : (term246 s y x) = (term206 x s y).
Proof. exact (eq_refl (term246 s y x)). Qed.
Lemma lem5270220 (s : real -> Prop) (y : real) : (term247 s y) = (term208 s y).
Proof. exact (fun_ext (fun x : real => @lem5270219 x s y)). Qed.
Lemma lem5270221 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270222 (s : real -> Prop) (y : real) : (term248 s y) = (term209 s y).
Proof. exact (MK_COMB (@lem5270221) (@lem5270220 s y)). Qed.
Lemma lem5270223 (s : real -> Prop) (b : real) : (term226 s b) = (term226 s b).
Proof. exact (eq_refl (term226 s b)). Qed.
Lemma lem5270224 (b : real) (s : real -> Prop) (y : real) : (term244 b s y) = (term240 b s y).
Proof. exact (MK_COMB (@lem5270223 s b) (@lem5270222 s y)). Qed.
Lemma lem5270225 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5270226 (b : real) (s : real -> Prop) (y : real) : (term249 b s y) = (term250 b s y).
Proof. exact (MK_COMB (@lem5270225) (@lem5270224 b s y)). Qed.
Lemma lem5270227 (x : real) (s : real -> Prop) (y : real) : (term246 s y x) = (term206 x s y).
Proof. exact (eq_refl (term246 s y x)). Qed.
Lemma lem5270228 (s : real -> Prop) (b : real) : (term226 s b) = (term226 s b).
Proof. exact (eq_refl (term226 s b)). Qed.
Lemma lem5270229 (b : real) (x : real) (s : real -> Prop) (y : real) : (term251 b s y x) = (term252 b x s y).
Proof. exact (MK_COMB (@lem5270228 s b) (@lem5270227 x s y)). Qed.
Lemma lem5270230 (b : real) (s : real -> Prop) (y : real) : (term253 b s y) = (term254 b s y).
Proof. exact (fun_ext (fun x : real => @lem5270229 b x s y)). Qed.
Lemma lem5270231 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270232 (b : real) (s : real -> Prop) (y : real) : (term245 b s y) = (term255 b s y).
Proof. exact (MK_COMB (@lem5270231) (@lem5270230 b s y)). Qed.
Lemma lem5270233 (b : real) (s : real -> Prop) (y : real) : ((term244 b s y) = (term245 b s y)) = ((term240 b s y) = (term255 b s y)).
Proof. exact (MK_COMB (@lem5270226 b s y) (@lem5270232 b s y)). Qed.
Lemma lem5270234 (b : real) (s : real -> Prop) (y : real) : (term240 b s y) = (term255 b s y).
Proof. exact (EQ_MP (@lem5270233 b s y) (@lem5270218 b s y)). Qed.
Lemma lem5270235 (b : real) (s : real -> Prop) : (term242 b s) = (term256 b s).
Proof. exact (fun_ext (fun y : real => @lem5270234 b s y)). Qed.
Lemma lem5270236 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270237 (b : real) (s : real -> Prop) : (term243 b s) = (term257 b s).
Proof. exact (MK_COMB (@lem5270236) (@lem5270235 b s)). Qed.
Lemma lem5270238 (b : real) (s : real -> Prop) : (term228 b s) = (term257 b s).
Proof. exact (TRANS (@lem5270214 b s) (@lem5270237 b s)). Qed.
Lemma lem5270239 (s : real -> Prop) : (term230 s) = (term258 s).
Proof. exact (fun_ext (fun b : real => @lem5270238 b s)). Qed.
Lemma lem5270240 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270241 (s : real -> Prop) : (term231 s) = (term259 s).
Proof. exact (MK_COMB (@lem5270240) (@lem5270239 s)). Qed.
Lemma lem5270242 (s : real -> Prop) : (term212 s) = (term259 s).
Proof. exact (TRANS (@lem5270194 s) (@lem5270241 s)). Qed.
Lemma lem5270243 (s : real -> Prop) : (term143 s) = (term259 s).
Proof. exact (TRANS (@lem5270170 s) (@lem5270242 s)). Qed.
Lemma lem5270244 : term144 = term260.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5270243 s)). Qed.
Lemma lem5270245 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5270246 : term145 = term261.
Proof. exact (MK_COMB (@lem5270245) (@lem5270244)). Qed.
Lemma lem5270247 : term102 = term261.
Proof. exact (TRANS (@lem5270016) (@lem5270246)). Qed.
Lemma lem5270248 : term10 = term261.
Proof. exact (TRANS (@lem5269715) (@lem5270247)). Qed.
Lemma lem5270249 (h1 : term10) : term261.
Proof. exact (EQ_MP (@lem5270248) (@lem5269631 h1)). Qed.
Lemma lem5270256 (x : real) (y : real) (z : real) : (term262 x y z) = (term263 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem5270257 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem5270258 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5270259 (x : real) (y : real) (z : real) : (term264 x y z) = (term265 x y z).
Proof. exact (MK_COMB (@lem5270258) (@lem5270256 x y z)). Qed.
Lemma lem5270260 (y : real) (x : real) (z : real) : (term266 y x z) = (term267 y x z).
Proof. exact (MK_COMB (@lem5270259 x y z) (@lem5270257 x z)). Qed.
Lemma lem5270261 (y : real) (x : real) (z : real) : (term43 y x z) = (term266 y x z).
Proof. exact (@lem17265 (term268 x y z) (real_le x z)). Qed.
Lemma lem5270262 (y : real) (x : real) (z : real) : (term43 y x z) = (term267 y x z).
Proof. exact (TRANS (@lem5270261 y x z) (@lem5270260 y x z)). Qed.
Lemma lem5270263 (y : real) (x : real) : (term44 y x) = (term269 y x).
Proof. exact (fun_ext (fun z : real => @lem5270262 y x z)). Qed.
Lemma lem5270264 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270265 (y : real) (x : real) : (term45 y x) = (term270 y x).
Proof. exact (MK_COMB (@lem5270264) (@lem5270263 y x)). Qed.
Lemma lem5270266 (x : real) : (term46 x) = (term271 x).
Proof. exact (fun_ext (fun y : real => @lem5270265 y x)). Qed.
Lemma lem5270267 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270268 (x : real) : (term47 x) = (term272 x).
Proof. exact (MK_COMB (@lem5270267) (@lem5270266 x)). Qed.
Lemma lem5270269 : term48 = term273.
Proof. exact (fun_ext (fun x : real => @lem5270268 x)). Qed.
Lemma lem5270270 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270331 : term49 = term274.
Proof. exact (MK_COMB (@lem5270270) (@lem5270269)). Qed.
Lemma lem5270332 (h1 : term49) : term274.
Proof. exact (EQ_MP (@lem5270331) (@lem5269632 h1)). Qed.
Lemma lem5270335 (s : real -> Prop) : (term275 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5270342 (s : real -> Prop) (b : real) (x : real) : (term61 s b x) = (term62 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5270343 (P : real -> Prop) : (term63 P) = (term64 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5270344 (s : real -> Prop) (b : real) : (term65 s b) = (term66 s b).
Proof. exact (@lem5270343 (term25 s b)). Qed.
Lemma lem5270345 (s : real -> Prop) (b : real) (x : real) : (term67 s b x) = (term24 s b x).
Proof. exact (eq_refl (term67 s b x)). Qed.
Lemma lem5270346 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5270347 (s : real -> Prop) (b : real) (x : real) : (term68 s b x) = (term61 s b x).
Proof. exact (MK_COMB (@lem5270346) (@lem5270345 s b x)). Qed.
Lemma lem5270348 (s : real -> Prop) (b : real) (x : real) : (term68 s b x) = (term62 s b x).
Proof. exact (TRANS (@lem5270347 s b x) (@lem5270342 s b x)). Qed.
Lemma lem5270349 (s : real -> Prop) (b : real) : (term69 s b) = (term70 s b).
Proof. exact (fun_ext (fun x : real => @lem5270348 s b x)). Qed.
Lemma lem5270350 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270351 (s : real -> Prop) (b : real) : (term66 s b) = (term71 s b).
Proof. exact (MK_COMB (@lem5270350) (@lem5270349 s b)). Qed.
Lemma lem5270352 (s : real -> Prop) (b : real) : (term65 s b) = (term71 s b).
Proof. exact (TRANS (@lem5270344 s b) (@lem5270351 s b)). Qed.
Lemma lem5270353 (P : real -> Prop) : (term276 P) = (term277 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5270354 (s : real -> Prop) : (term278 s) = (term279 s).
Proof. exact (@lem5270353 (term36 s)). Qed.
Lemma lem5270355 (s : real -> Prop) (b : real) : (term280 s b) = (term26 s b).
Proof. exact (eq_refl (term280 s b)). Qed.
Lemma lem5270356 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5270357 (s : real -> Prop) (b : real) : (term281 s b) = (term65 s b).
Proof. exact (MK_COMB (@lem5270356) (@lem5270355 s b)). Qed.
Lemma lem5270358 (s : real -> Prop) (b : real) : (term281 s b) = (term71 s b).
Proof. exact (TRANS (@lem5270357 s b) (@lem5270352 s b)). Qed.
Lemma lem5270359 (s : real -> Prop) : (term282 s) = (term283 s).
Proof. exact (fun_ext (fun b : real => @lem5270358 s b)). Qed.
Lemma lem5270360 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270361 (s : real -> Prop) : (term279 s) = (term284 s).
Proof. exact (MK_COMB (@lem5270360) (@lem5270359 s)). Qed.
Lemma lem5270362 (s : real -> Prop) : (term278 s) = (term284 s).
Proof. exact (TRANS (@lem5270354 s) (@lem5270361 s)). Qed.
Lemma lem5270363 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5270364 (s : real -> Prop) : (term285 s) = (term286 s).
Proof. exact (MK_COMB (@lem5270363) (@lem5270335 s)). Qed.
Lemma lem5270365 (s : real -> Prop) : (term287 s) = (term288 s).
Proof. exact (MK_COMB (@lem5270364 s) (@lem5270362 s)). Qed.
Lemma lem5270366 (s : real -> Prop) : (term289 s) = (term287 s).
Proof. exact (@lem17045 (term148 s) (term37 s)). Qed.
Lemma lem5270367 (s : real -> Prop) : (term289 s) = (term288 s).
Proof. exact (TRANS (@lem5270366 s) (@lem5270365 s)). Qed.
Lemma lem5270374 (s : real -> Prop) (x : real) : (term31 s x) = (term290 s x).
Proof. exact (@lem17265 (@IN real x s) (term291 s x)). Qed.
Lemma lem5270375 (s : real -> Prop) : (term32 s) = (term292 s).
Proof. exact (fun_ext (fun x : real => @lem5270374 s x)). Qed.
Lemma lem5270376 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270377 (s : real -> Prop) : (term33 s) = (term293 s).
Proof. exact (MK_COMB (@lem5270376) (@lem5270375 s)). Qed.
Lemma lem5270384 (s : real -> Prop) (b : real) (x : real) : (term61 s b x) = (term62 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5270385 (P : real -> Prop) : (term63 P) = (term64 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5270386 (s : real -> Prop) (b : real) : (term65 s b) = (term66 s b).
Proof. exact (@lem5270385 (term25 s b)). Qed.
Lemma lem5270387 (s : real -> Prop) (b : real) (x : real) : (term67 s b x) = (term24 s b x).
Proof. exact (eq_refl (term67 s b x)). Qed.
Lemma lem5270388 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5270389 (s : real -> Prop) (b : real) (x : real) : (term68 s b x) = (term61 s b x).
Proof. exact (MK_COMB (@lem5270388) (@lem5270387 s b x)). Qed.
Lemma lem5270390 (s : real -> Prop) (b : real) (x : real) : (term68 s b x) = (term62 s b x).
Proof. exact (TRANS (@lem5270389 s b x) (@lem5270384 s b x)). Qed.
Lemma lem5270391 (s : real -> Prop) (b : real) : (term69 s b) = (term70 s b).
Proof. exact (fun_ext (fun x : real => @lem5270390 s b x)). Qed.
Lemma lem5270392 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270393 (s : real -> Prop) (b : real) : (term66 s b) = (term71 s b).
Proof. exact (MK_COMB (@lem5270392) (@lem5270391 s b)). Qed.
Lemma lem5270394 (s : real -> Prop) (b : real) : (term65 s b) = (term71 s b).
Proof. exact (TRANS (@lem5270386 s b) (@lem5270393 s b)). Qed.
Lemma lem5270395 (b : real) (s : real -> Prop) : (term23 b s) = (term23 b s).
Proof. exact (eq_refl (term23 b s)). Qed.
Lemma lem5270396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5270397 (s : real -> Prop) (b : real) : (term294 s b) = (term295 s b).
Proof. exact (MK_COMB (@lem5270396) (@lem5270394 s b)). Qed.
Lemma lem5270398 (b : real) (s : real -> Prop) : (term296 b s) = (term297 b s).
Proof. exact (MK_COMB (@lem5270397 s b) (@lem5270395 b s)). Qed.
Lemma lem5270399 (b : real) (s : real -> Prop) : (term28 b s) = (term296 b s).
Proof. exact (@lem17265 (term26 s b) (term23 b s)). Qed.
Lemma lem5270400 (b : real) (s : real -> Prop) : (term28 b s) = (term297 b s).
Proof. exact (TRANS (@lem5270399 b s) (@lem5270398 b s)). Qed.
Lemma lem5270401 (s : real -> Prop) : (term29 s) = (term298 s).
Proof. exact (fun_ext (fun b : real => @lem5270400 b s)). Qed.
Lemma lem5270402 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270403 (s : real -> Prop) : (term30 s) = (term299 s).
Proof. exact (MK_COMB (@lem5270402) (@lem5270401 s)). Qed.
Lemma lem5270404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5270405 (s : real -> Prop) : (term34 s) = (term300 s).
Proof. exact (MK_COMB (@lem5270404) (@lem5270377 s)). Qed.
Lemma lem5270406 (s : real -> Prop) : (term35 s) = (term301 s).
Proof. exact (MK_COMB (@lem5270405 s) (@lem5270403 s)). Qed.
Lemma lem5270407 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5270408 (s : real -> Prop) : (term302 s) = (term303 s).
Proof. exact (MK_COMB (@lem5270407) (@lem5270367 s)). Qed.
Lemma lem5270409 (s : real -> Prop) : (term304 s) = (term305 s).
Proof. exact (MK_COMB (@lem5270408 s) (@lem5270406 s)). Qed.
Lemma lem5270410 (s : real -> Prop) : (term41 s) = (term304 s).
Proof. exact (@lem17265 (term39 s) (term35 s)). Qed.
Lemma lem5270411 (s : real -> Prop) : (term41 s) = (term305 s).
Proof. exact (TRANS (@lem5270410 s) (@lem5270409 s)). Qed.
Lemma lem5270412 : term42 = term306.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5270411 s)). Qed.
Lemma lem5270413 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5270414 : term17 = term307.
Proof. exact (MK_COMB (@lem5270413) (@lem5270412)). Qed.
Lemma lem5270661 {A B : Type'} (P : type1413 A B) : (term308 A B P) = (term309 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5270662 (P : type1626) : (term310 P) = (term311 P).
Proof. exact (@lem5270661 real real P). Qed.
Lemma lem5270663 (s : real -> Prop) : (term312 s) = (term313 s).
Proof. exact (@lem5270662 (term314 s)). Qed.
Lemma lem5270664 (s : real -> Prop) (b : real) : (term315 s b) = (term70 s b).
Proof. exact (eq_refl (term315 s b)). Qed.
Lemma lem5270665 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5270666 (s : real -> Prop) (b : real) (x : real) : (term316 s b x) = (term162 s b x).
Proof. exact (MK_COMB (@lem5270664 s b) (@lem5270665 x)). Qed.
Lemma lem5270667 (s : real -> Prop) (b : real) (x : real) : (term162 s b x) = (term62 s b x).
Proof. exact (eq_refl (term162 s b x)). Qed.
Lemma lem5270668 (s : real -> Prop) (b : real) (x : real) : (term316 s b x) = (term62 s b x).
Proof. exact (TRANS (@lem5270666 s b x) (@lem5270667 s b x)). Qed.
Lemma lem5270669 (s : real -> Prop) (b : real) : (term317 s b) = (term70 s b).
Proof. exact (fun_ext (fun x : real => @lem5270668 s b x)). Qed.
Lemma lem5270670 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270671 (s : real -> Prop) (b : real) : (term318 s b) = (term71 s b).
Proof. exact (MK_COMB (@lem5270670) (@lem5270669 s b)). Qed.
Lemma lem5270672 (s : real -> Prop) : (term319 s) = (term283 s).
Proof. exact (fun_ext (fun b : real => @lem5270671 s b)). Qed.
Lemma lem5270673 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270674 (s : real -> Prop) : (term312 s) = (term284 s).
Proof. exact (MK_COMB (@lem5270673) (@lem5270672 s)). Qed.
Lemma lem5270675 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5270676 (s : real -> Prop) : (term320 s) = (term321 s).
Proof. exact (MK_COMB (@lem5270675) (@lem5270674 s)). Qed.
Lemma lem5270677 (s : real -> Prop) (b : real) : (term315 s b) = (term70 s b).
Proof. exact (eq_refl (term315 s b)). Qed.
Lemma lem5270678 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5270679 (s : real -> Prop) (x : real -> real) (b : real) : (term322 s x b) = (term323 s x b).
Proof. exact (MK_COMB (@lem5270677 s b) (@lem5270678 x b)). Qed.
Lemma lem5270680 (s : real -> Prop) (x : real -> real) (b : real) : (term323 s x b) = (term324 s x b).
Proof. exact (eq_refl (term323 s x b)). Qed.
Lemma lem5270681 (s : real -> Prop) (x : real -> real) (b : real) : (term322 s x b) = (term324 s x b).
Proof. exact (TRANS (@lem5270679 s x b) (@lem5270680 s x b)). Qed.
Lemma lem5270682 (s : real -> Prop) (x : real -> real) : (term325 s x) = (term326 s x).
Proof. exact (fun_ext (fun b : real => @lem5270681 s x b)). Qed.
Lemma lem5270683 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270684 (s : real -> Prop) (x : real -> real) : (term327 s x) = (term328 s x).
Proof. exact (MK_COMB (@lem5270683) (@lem5270682 s x)). Qed.
Lemma lem5270685 (s : real -> Prop) : (term329 s) = (term330 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5270684 s x)). Qed.
Lemma lem5270686 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5270687 (s : real -> Prop) : (term313 s) = (term331 s).
Proof. exact (MK_COMB (@lem5270686) (@lem5270685 s)). Qed.
Lemma lem5270688 (s : real -> Prop) : ((term312 s) = (term313 s)) = ((term284 s) = (term331 s)).
Proof. exact (MK_COMB (@lem5270676 s) (@lem5270687 s)). Qed.
Lemma lem5270689 (s : real -> Prop) : (term284 s) = (term331 s).
Proof. exact (EQ_MP (@lem5270688 s) (@lem5270663 s)). Qed.
Lemma lem5270690 (s : real -> Prop) : (term286 s) = (term286 s).
Proof. exact (eq_refl (term286 s)). Qed.
Lemma lem5270691 (s : real -> Prop) : (term288 s) = (term332 s).
Proof. exact (MK_COMB (@lem5270690 s) (@lem5270689 s)). Qed.
Lemma lem5270693 {A : Type'} (P : Prop) (Q : A -> Prop) : (term333 A P Q) = (term334 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5270694 (P : Prop) (Q : type1028) : (term335 P Q) = (term336 P Q).
Proof. exact (@lem5270693 (real -> real) P Q). Qed.
Lemma lem5270695 (s : real -> Prop) : (term337 s) = (term338 s).
Proof. exact (@lem5270694 (s = (@EMPTY real)) (term330 s)). Qed.
Lemma lem5270696 (s : real -> Prop) (x : real -> real) : (term339 s x) = (term328 s x).
Proof. exact (eq_refl (term339 s x)). Qed.
Lemma lem5270697 (s : real -> Prop) : (term340 s) = (term330 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5270696 s x)). Qed.
Lemma lem5270698 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5270699 (s : real -> Prop) : (term341 s) = (term331 s).
Proof. exact (MK_COMB (@lem5270698) (@lem5270697 s)). Qed.
Lemma lem5270700 (s : real -> Prop) : (term286 s) = (term286 s).
Proof. exact (eq_refl (term286 s)). Qed.
Lemma lem5270701 (s : real -> Prop) : (term337 s) = (term332 s).
Proof. exact (MK_COMB (@lem5270700 s) (@lem5270699 s)). Qed.
Lemma lem5270702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5270703 (s : real -> Prop) : (term342 s) = (term343 s).
Proof. exact (MK_COMB (@lem5270702) (@lem5270701 s)). Qed.
Lemma lem5270704 (s : real -> Prop) (x : real -> real) : (term339 s x) = (term328 s x).
Proof. exact (eq_refl (term339 s x)). Qed.
Lemma lem5270705 (s : real -> Prop) : (term286 s) = (term286 s).
Proof. exact (eq_refl (term286 s)). Qed.
Lemma lem5270706 (s : real -> Prop) (x : real -> real) : (term344 s x) = (term345 s x).
Proof. exact (MK_COMB (@lem5270705 s) (@lem5270704 s x)). Qed.
Lemma lem5270707 (s : real -> Prop) : (term346 s) = (term347 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5270706 s x)). Qed.
Lemma lem5270708 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5270709 (s : real -> Prop) : (term338 s) = (term348 s).
Proof. exact (MK_COMB (@lem5270708) (@lem5270707 s)). Qed.
Lemma lem5270710 (s : real -> Prop) : ((term337 s) = (term338 s)) = ((term332 s) = (term348 s)).
Proof. exact (MK_COMB (@lem5270703 s) (@lem5270709 s)). Qed.
Lemma lem5270711 (s : real -> Prop) : (term332 s) = (term348 s).
Proof. exact (EQ_MP (@lem5270710 s) (@lem5270695 s)). Qed.
Lemma lem5270712 (s : real -> Prop) : (term288 s) = (term348 s).
Proof. exact (TRANS (@lem5270691 s) (@lem5270711 s)). Qed.
Lemma lem5270713 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5270714 (s : real -> Prop) : (term303 s) = (term349 s).
Proof. exact (MK_COMB (@lem5270713) (@lem5270712 s)). Qed.
Lemma lem5270716 {A : Type'} (P : A -> Prop) (Q : Prop) : (term191 A P Q) = (term192 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5270717 (P : real -> Prop) (Q : Prop) : (term193 P Q) = (term194 P Q).
Proof. exact (@lem5270716 real P Q). Qed.
Lemma lem5270718 (b : real) (s : real -> Prop) : (term350 b s) = (term351 b s).
Proof. exact (@lem5270717 (term70 s b) (term23 b s)). Qed.
Lemma lem5270719 (s : real -> Prop) (b : real) (x : real) : (term162 s b x) = (term62 s b x).
Proof. exact (eq_refl (term162 s b x)). Qed.
Lemma lem5270720 (s : real -> Prop) (b : real) : (term163 s b) = (term70 s b).
Proof. exact (fun_ext (fun x : real => @lem5270719 s b x)). Qed.
Lemma lem5270721 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270722 (s : real -> Prop) (b : real) : (term164 s b) = (term71 s b).
Proof. exact (MK_COMB (@lem5270721) (@lem5270720 s b)). Qed.
Lemma lem5270723 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5270724 (s : real -> Prop) (b : real) : (term352 s b) = (term295 s b).
Proof. exact (MK_COMB (@lem5270723) (@lem5270722 s b)). Qed.
Lemma lem5270725 (b : real) (s : real -> Prop) : (term23 b s) = (term23 b s).
Proof. exact (eq_refl (term23 b s)). Qed.
Lemma lem5270726 (b : real) (s : real -> Prop) : (term350 b s) = (term297 b s).
Proof. exact (MK_COMB (@lem5270724 s b) (@lem5270725 b s)). Qed.
Lemma lem5270727 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5270728 (b : real) (s : real -> Prop) : (term353 b s) = (term354 b s).
Proof. exact (MK_COMB (@lem5270727) (@lem5270726 b s)). Qed.
Lemma lem5270729 (s : real -> Prop) (b : real) (x : real) : (term162 s b x) = (term62 s b x).
Proof. exact (eq_refl (term162 s b x)). Qed.
Lemma lem5270730 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5270731 (s : real -> Prop) (b : real) (x : real) : (term355 s b x) = (term356 s b x).
Proof. exact (MK_COMB (@lem5270730) (@lem5270729 s b x)). Qed.
Lemma lem5270732 (b : real) (s : real -> Prop) : (term23 b s) = (term23 b s).
Proof. exact (eq_refl (term23 b s)). Qed.
Lemma lem5270733 (x : real) (b : real) (s : real -> Prop) : (term357 x b s) = (term358 x b s).
Proof. exact (MK_COMB (@lem5270731 s b x) (@lem5270732 b s)). Qed.
Lemma lem5270734 (b : real) (s : real -> Prop) : (term359 b s) = (term360 b s).
Proof. exact (fun_ext (fun x : real => @lem5270733 x b s)). Qed.
Lemma lem5270735 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270736 (b : real) (s : real -> Prop) : (term351 b s) = (term361 b s).
Proof. exact (MK_COMB (@lem5270735) (@lem5270734 b s)). Qed.
Lemma lem5270737 (b : real) (s : real -> Prop) : ((term350 b s) = (term351 b s)) = ((term297 b s) = (term361 b s)).
Proof. exact (MK_COMB (@lem5270728 b s) (@lem5270736 b s)). Qed.
Lemma lem5270738 (b : real) (s : real -> Prop) : (term297 b s) = (term361 b s).
Proof. exact (EQ_MP (@lem5270737 b s) (@lem5270718 b s)). Qed.
Lemma lem5270739 (s : real -> Prop) : (term298 s) = (term362 s).
Proof. exact (fun_ext (fun b : real => @lem5270738 b s)). Qed.
Lemma lem5270740 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270741 (s : real -> Prop) : (term299 s) = (term363 s).
Proof. exact (MK_COMB (@lem5270740) (@lem5270739 s)). Qed.
Lemma lem5270743 {A B : Type'} (P : type1413 A B) : (term308 A B P) = (term309 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5270744 (P : type1626) : (term310 P) = (term311 P).
Proof. exact (@lem5270743 real real P). Qed.
Lemma lem5270745 (s : real -> Prop) : (term364 s) = (term365 s).
Proof. exact (@lem5270744 (term366 s)). Qed.
Lemma lem5270746 (b : real) (s : real -> Prop) : (term367 s b) = (term360 b s).
Proof. exact (eq_refl (term367 s b)). Qed.
Lemma lem5270747 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5270748 (b : real) (s : real -> Prop) (x : real) : (term368 s b x) = (term369 b s x).
Proof. exact (MK_COMB (@lem5270746 b s) (@lem5270747 x)). Qed.
Lemma lem5270749 (x : real) (b : real) (s : real -> Prop) : (term369 b s x) = (term358 x b s).
Proof. exact (eq_refl (term369 b s x)). Qed.
Lemma lem5270750 (x : real) (b : real) (s : real -> Prop) : (term368 s b x) = (term358 x b s).
Proof. exact (TRANS (@lem5270748 b s x) (@lem5270749 x b s)). Qed.
Lemma lem5270751 (b : real) (s : real -> Prop) : (term370 s b) = (term360 b s).
Proof. exact (fun_ext (fun x : real => @lem5270750 x b s)). Qed.
Lemma lem5270752 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5270753 (b : real) (s : real -> Prop) : (term371 s b) = (term361 b s).
Proof. exact (MK_COMB (@lem5270752) (@lem5270751 b s)). Qed.
Lemma lem5270754 (s : real -> Prop) : (term372 s) = (term362 s).
Proof. exact (fun_ext (fun b : real => @lem5270753 b s)). Qed.
Lemma lem5270755 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270756 (s : real -> Prop) : (term364 s) = (term363 s).
Proof. exact (MK_COMB (@lem5270755) (@lem5270754 s)). Qed.
Lemma lem5270757 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5270758 (s : real -> Prop) : (term373 s) = (term374 s).
Proof. exact (MK_COMB (@lem5270757) (@lem5270756 s)). Qed.
Lemma lem5270759 (b : real) (s : real -> Prop) : (term367 s b) = (term360 b s).
Proof. exact (eq_refl (term367 s b)). Qed.
Lemma lem5270760 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5270761 (s : real -> Prop) (x : real -> real) (b : real) : (term375 s x b) = (term376 s x b).
Proof. exact (MK_COMB (@lem5270759 b s) (@lem5270760 x b)). Qed.
Lemma lem5270762 (x : real -> real) (b : real) (s : real -> Prop) : (term376 s x b) = (term377 x b s).
Proof. exact (eq_refl (term376 s x b)). Qed.
Lemma lem5270763 (x : real -> real) (b : real) (s : real -> Prop) : (term375 s x b) = (term377 x b s).
Proof. exact (TRANS (@lem5270761 s x b) (@lem5270762 x b s)). Qed.
Lemma lem5270764 (x : real -> real) (s : real -> Prop) : (term378 s x) = (term379 x s).
Proof. exact (fun_ext (fun b : real => @lem5270763 x b s)). Qed.
Lemma lem5270765 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270766 (x : real -> real) (s : real -> Prop) : (term380 s x) = (term381 x s).
Proof. exact (MK_COMB (@lem5270765) (@lem5270764 x s)). Qed.
Lemma lem5270767 (s : real -> Prop) : (term382 s) = (term383 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5270766 x s)). Qed.
Lemma lem5270768 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5270769 (s : real -> Prop) : (term365 s) = (term384 s).
Proof. exact (MK_COMB (@lem5270768) (@lem5270767 s)). Qed.
Lemma lem5270770 (s : real -> Prop) : ((term364 s) = (term365 s)) = ((term363 s) = (term384 s)).
Proof. exact (MK_COMB (@lem5270758 s) (@lem5270769 s)). Qed.
Lemma lem5270771 (s : real -> Prop) : (term363 s) = (term384 s).
Proof. exact (EQ_MP (@lem5270770 s) (@lem5270745 s)). Qed.
Lemma lem5270772 (s : real -> Prop) : (term299 s) = (term384 s).
Proof. exact (TRANS (@lem5270741 s) (@lem5270771 s)). Qed.
Lemma lem5270773 (s : real -> Prop) : (term300 s) = (term300 s).
Proof. exact (eq_refl (term300 s)). Qed.
Lemma lem5270774 (s : real -> Prop) : (term301 s) = (term385 s).
Proof. exact (MK_COMB (@lem5270773 s) (@lem5270772 s)). Qed.
Lemma lem5270776 {A : Type'} (P : Prop) (Q : A -> Prop) : (term104 A P Q) = (term103 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5270777 (P : Prop) (Q : type1028) : (term386 P Q) = (term387 P Q).
Proof. exact (@lem5270776 (real -> real) P Q). Qed.
Lemma lem5270778 (s : real -> Prop) : (term388 s) = (term389 s).
Proof. exact (@lem5270777 (term293 s) (term383 s)). Qed.
Lemma lem5270779 (x : real -> real) (s : real -> Prop) : (term390 s x) = (term381 x s).
Proof. exact (eq_refl (term390 s x)). Qed.
Lemma lem5270780 (s : real -> Prop) : (term391 s) = (term383 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5270779 x s)). Qed.
Lemma lem5270781 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5270782 (s : real -> Prop) : (term392 s) = (term384 s).
Proof. exact (MK_COMB (@lem5270781) (@lem5270780 s)). Qed.
Lemma lem5270783 (s : real -> Prop) : (term300 s) = (term300 s).
Proof. exact (eq_refl (term300 s)). Qed.
Lemma lem5270784 (s : real -> Prop) : (term388 s) = (term385 s).
Proof. exact (MK_COMB (@lem5270783 s) (@lem5270782 s)). Qed.
Lemma lem5270785 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5270786 (s : real -> Prop) : (term393 s) = (term394 s).
Proof. exact (MK_COMB (@lem5270785) (@lem5270784 s)). Qed.
Lemma lem5270787 (x : real -> real) (s : real -> Prop) : (term390 s x) = (term381 x s).
Proof. exact (eq_refl (term390 s x)). Qed.
Lemma lem5270788 (s : real -> Prop) : (term300 s) = (term300 s).
Proof. exact (eq_refl (term300 s)). Qed.
Lemma lem5270789 (x : real -> real) (s : real -> Prop) : (term395 s x) = (term396 x s).
Proof. exact (MK_COMB (@lem5270788 s) (@lem5270787 x s)). Qed.
Lemma lem5270790 (s : real -> Prop) : (term397 s) = (term398 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5270789 x s)). Qed.
Lemma lem5270791 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5270792 (s : real -> Prop) : (term389 s) = (term399 s).
Proof. exact (MK_COMB (@lem5270791) (@lem5270790 s)). Qed.
Lemma lem5270793 (s : real -> Prop) : ((term388 s) = (term389 s)) = ((term385 s) = (term399 s)).
Proof. exact (MK_COMB (@lem5270786 s) (@lem5270792 s)). Qed.
Lemma lem5270794 (s : real -> Prop) : (term385 s) = (term399 s).
Proof. exact (EQ_MP (@lem5270793 s) (@lem5270778 s)). Qed.
Lemma lem5270795 (s : real -> Prop) : (term301 s) = (term399 s).
Proof. exact (TRANS (@lem5270774 s) (@lem5270794 s)). Qed.
Lemma lem5270796 (s : real -> Prop) : (term305 s) = (term400 s).
Proof. exact (MK_COMB (@lem5270714 s) (@lem5270795 s)). Qed.
Lemma lem5270798 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term120 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5270799 (P : type1028) (Q : type1028) : (term401 P Q) = (term402 P Q).
Proof. exact (@lem5270798 (real -> real) P Q). Qed.
Lemma lem5270800 (s : real -> Prop) : (term403 s) = (term404 s).
Proof. exact (@lem5270799 (term347 s) (term398 s)). Qed.
Lemma lem5270801 (s : real -> Prop) (x : real -> real) : (term405 s x) = (term345 s x).
Proof. exact (eq_refl (term405 s x)). Qed.
Lemma lem5270802 (s : real -> Prop) : (term406 s) = (term347 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5270801 s x)). Qed.
Lemma lem5270803 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5270804 (s : real -> Prop) : (term407 s) = (term348 s).
Proof. exact (MK_COMB (@lem5270803) (@lem5270802 s)). Qed.
Lemma lem5270805 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5270806 (s : real -> Prop) : (term408 s) = (term349 s).
Proof. exact (MK_COMB (@lem5270805) (@lem5270804 s)). Qed.
Lemma lem5270807 (x : real -> real) (s : real -> Prop) : (term409 s x) = (term396 x s).
Proof. exact (eq_refl (term409 s x)). Qed.
Lemma lem5270808 (s : real -> Prop) : (term410 s) = (term398 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5270807 x s)). Qed.
Lemma lem5270809 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5270810 (s : real -> Prop) : (term411 s) = (term399 s).
Proof. exact (MK_COMB (@lem5270809) (@lem5270808 s)). Qed.
Lemma lem5270811 (s : real -> Prop) : (term403 s) = (term400 s).
Proof. exact (MK_COMB (@lem5270806 s) (@lem5270810 s)). Qed.
Lemma lem5270812 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5270813 (s : real -> Prop) : (term412 s) = (term413 s).
Proof. exact (MK_COMB (@lem5270812) (@lem5270811 s)). Qed.
Lemma lem5270814 (s : real -> Prop) (x : real -> real) : (term405 s x) = (term345 s x).
Proof. exact (eq_refl (term405 s x)). Qed.
Lemma lem5270815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5270816 (s : real -> Prop) (x : real -> real) : (term414 s x) = (term415 s x).
Proof. exact (MK_COMB (@lem5270815) (@lem5270814 s x)). Qed.
Lemma lem5270817 (x : real -> real) (s : real -> Prop) : (term409 s x) = (term396 x s).
Proof. exact (eq_refl (term409 s x)). Qed.
Lemma lem5270818 (x : real -> real) (s : real -> Prop) : (term416 s x) = (term417 x s).
Proof. exact (MK_COMB (@lem5270816 s x) (@lem5270817 x s)). Qed.
Lemma lem5270819 (s : real -> Prop) : (term418 s) = (term419 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5270818 x s)). Qed.
Lemma lem5270820 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5270821 (s : real -> Prop) : (term404 s) = (term420 s).
Proof. exact (MK_COMB (@lem5270820) (@lem5270819 s)). Qed.
Lemma lem5270822 (s : real -> Prop) : ((term403 s) = (term404 s)) = ((term400 s) = (term420 s)).
Proof. exact (MK_COMB (@lem5270813 s) (@lem5270821 s)). Qed.
Lemma lem5270823 (s : real -> Prop) : (term400 s) = (term420 s).
Proof. exact (EQ_MP (@lem5270822 s) (@lem5270800 s)). Qed.
Lemma lem5270824 (s : real -> Prop) : (term305 s) = (term420 s).
Proof. exact (TRANS (@lem5270796 s) (@lem5270823 s)). Qed.
Lemma lem5270825 : term306 = term421.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5270824 s)). Qed.
Lemma lem5270826 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5270827 : term307 = term422.
Proof. exact (MK_COMB (@lem5270826) (@lem5270825)). Qed.
Lemma lem5270829 {A B : Type'} (P : type1413 A B) : (term308 A B P) = (term309 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5270830 (P : type1017) : (term423 P) = (term424 P).
Proof. exact (@lem5270829 (real -> Prop) (real -> real) P). Qed.
Lemma lem5270831 : term425 = term426.
Proof. exact (@lem5270830 term427). Qed.
Lemma lem5270832 (s : real -> Prop) : (term428 s) = (term419 s).
Proof. exact (eq_refl (term428 s)). Qed.
Lemma lem5270833 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5270834 (s : real -> Prop) (x : real -> real) : (term429 s x) = (term430 s x).
Proof. exact (MK_COMB (@lem5270832 s) (@lem5270833 x)). Qed.
Lemma lem5270835 (x : real -> real) (s : real -> Prop) : (term430 s x) = (term417 x s).
Proof. exact (eq_refl (term430 s x)). Qed.
Lemma lem5270836 (x : real -> real) (s : real -> Prop) : (term429 s x) = (term417 x s).
Proof. exact (TRANS (@lem5270834 s x) (@lem5270835 x s)). Qed.
Lemma lem5270837 (s : real -> Prop) : (term431 s) = (term419 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5270836 x s)). Qed.
Lemma lem5270838 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5270839 (s : real -> Prop) : (term432 s) = (term420 s).
Proof. exact (MK_COMB (@lem5270838) (@lem5270837 s)). Qed.
Lemma lem5270840 : term433 = term421.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5270839 s)). Qed.
Lemma lem5270841 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5270842 : term425 = term422.
Proof. exact (MK_COMB (@lem5270841) (@lem5270840)). Qed.
Lemma lem5270843 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5270844 : term434 = term435.
Proof. exact (MK_COMB (@lem5270843) (@lem5270842)). Qed.
Lemma lem5270845 (s : real -> Prop) : (term428 s) = (term419 s).
Proof. exact (eq_refl (term428 s)). Qed.
Lemma lem5270846 (x : type1021) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5270847 (x : type1021) (s : real -> Prop) : (term436 x s) = (term437 x s).
Proof. exact (MK_COMB (@lem5270845 s) (@lem5270846 x s)). Qed.
Lemma lem5270848 (x : type1021) (s : real -> Prop) : (term437 x s) = (term438 x s).
Proof. exact (eq_refl (term437 x s)). Qed.
Lemma lem5270849 (x : type1021) (s : real -> Prop) : (term436 x s) = (term438 x s).
Proof. exact (TRANS (@lem5270847 x s) (@lem5270848 x s)). Qed.
Lemma lem5270850 (x : type1021) : (term439 x) = (term440 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5270849 x s)). Qed.
Lemma lem5270851 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5270852 (x : type1021) : (term441 x) = (term442 x).
Proof. exact (MK_COMB (@lem5270851) (@lem5270850 x)). Qed.
Lemma lem5270853 : term443 = term444.
Proof. exact (fun_ext (fun x : type1021 => @lem5270852 x)). Qed.
Lemma lem5270854 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5270855 : term426 = term445.
Proof. exact (MK_COMB (@lem5270854) (@lem5270853)). Qed.
Lemma lem5270856 : (term425 = term426) = (term422 = term445).
Proof. exact (MK_COMB (@lem5270844) (@lem5270855)). Qed.
Lemma lem5270857 : term422 = term445.
Proof. exact (EQ_MP (@lem5270856) (@lem5270831)). Qed.
Lemma lem5270859 : term307 = term445.
Proof. exact (TRANS (@lem5270827) (@lem5270857)). Qed.
Lemma lem5270860 : term17 = term445.
Proof. exact (TRANS (@lem5270414) (@lem5270859)). Qed.
Lemma lem5270861 (h1 : term17) : term445.
Proof. exact (EQ_MP (@lem5270860) (@lem5269633 h1)). Qed.
Lemma lem5270862 (x : type1021) (h1 : term442 x) : term442 x.
Proof. exact (h1). Qed.
Lemma lem5270863 (s : real -> Prop) (h1 : term259 s) : term259 s.
Proof. exact (h1). Qed.
Lemma lem5270864 (b : real) (s : real -> Prop) (h1 : term257 b s) : term257 b s.
Proof. exact (h1). Qed.
Lemma lem5270865 (b : real) (s : real -> Prop) (y : real) (h1 : term255 b s y) : term255 b s y.
Proof. exact (h1). Qed.
Lemma lem5270866 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term252 b x' s y.
Proof. exact (h1). Qed.
Lemma lem5270891 (y : real) (x : real) (z : real) : (term267 y x z) = (term267 y x z).
Proof. exact (eq_refl (term267 y x z)). Qed.
Lemma lem5270892 (y : real) (x : real) : (term269 y x) = (term269 y x).
Proof. exact (fun_ext (fun z : real => @lem5270891 y x z)). Qed.
Lemma lem5270893 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270894 (y : real) (x : real) : (term270 y x) = (term270 y x).
Proof. exact (MK_COMB (@lem5270893) (@lem5270892 y x)). Qed.
Lemma lem5270895 (x : real) : (term271 x) = (term271 x).
Proof. exact (fun_ext (fun y : real => @lem5270894 y x)). Qed.
Lemma lem5270896 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270897 (x : real) : (term272 x) = (term272 x).
Proof. exact (MK_COMB (@lem5270896) (@lem5270895 x)). Qed.
Lemma lem5270898 : term273 = term273.
Proof. exact (fun_ext (fun x : real => @lem5270897 x)). Qed.
Lemma lem5270899 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270900 : term274 = term274.
Proof. exact (MK_COMB (@lem5270899) (@lem5270898)). Qed.
Lemma lem5270901 (h1 : term49) : term274.
Proof. exact (EQ_MP (@lem5270900) (@lem5270332 h1)). Qed.
Lemma lem5270934 (x : type1021) (b : real) (s : real -> Prop) : (term446 x b s) = (term446 x b s).
Proof. exact (eq_refl (term446 x b s)). Qed.
Lemma lem5270935 (x : type1021) (s : real -> Prop) : (term447 x s) = (term447 x s).
Proof. exact (fun_ext (fun b : real => @lem5270934 x b s)). Qed.
Lemma lem5270936 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270937 (x : type1021) (s : real -> Prop) : (term448 x s) = (term448 x s).
Proof. exact (MK_COMB (@lem5270936) (@lem5270935 x s)). Qed.
Lemma lem5270954 (s : real -> Prop) (x : real) : (term290 s x) = (term290 s x).
Proof. exact (eq_refl (term290 s x)). Qed.
Lemma lem5270955 (s : real -> Prop) : (term292 s) = (term292 s).
Proof. exact (fun_ext (fun x : real => @lem5270954 s x)). Qed.
Lemma lem5270956 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270957 (s : real -> Prop) : (term293 s) = (term293 s).
Proof. exact (MK_COMB (@lem5270956) (@lem5270955 s)). Qed.
Lemma lem5270958 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5270959 (s : real -> Prop) : (term300 s) = (term300 s).
Proof. exact (MK_COMB (@lem5270958) (@lem5270957 s)). Qed.
Lemma lem5270960 (x : type1021) (s : real -> Prop) : (term449 x s) = (term449 x s).
Proof. exact (MK_COMB (@lem5270959 s) (@lem5270937 x s)). Qed.
Lemma lem5270983 (x : type1021) (s : real -> Prop) (b : real) : (term450 x s b) = (term450 x s b).
Proof. exact (eq_refl (term450 x s b)). Qed.
Lemma lem5270984 (x : type1021) (s : real -> Prop) : (term451 x s) = (term451 x s).
Proof. exact (fun_ext (fun b : real => @lem5270983 x s b)). Qed.
Lemma lem5270985 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5270986 (x : type1021) (s : real -> Prop) : (term452 x s) = (term452 x s).
Proof. exact (MK_COMB (@lem5270985) (@lem5270984 x s)). Qed.
Lemma lem5270993 (s : real -> Prop) : (term286 s) = (term286 s).
Proof. exact (eq_refl (term286 s)). Qed.
Lemma lem5270994 (x : type1021) (s : real -> Prop) : (term453 x s) = (term453 x s).
Proof. exact (MK_COMB (@lem5270993 s) (@lem5270986 x s)). Qed.
Lemma lem5270995 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5270996 (x : type1021) (s : real -> Prop) : (term454 x s) = (term454 x s).
Proof. exact (MK_COMB (@lem5270995) (@lem5270994 x s)). Qed.
Lemma lem5270997 (x : type1021) (s : real -> Prop) : (term438 x s) = (term438 x s).
Proof. exact (MK_COMB (@lem5270996 x s) (@lem5270960 x s)). Qed.
Lemma lem5270998 (x : type1021) : (term440 x) = (term440 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5270997 x s)). Qed.
Lemma lem5270999 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5271000 (x : type1021) : (term442 x) = (term442 x).
Proof. exact (MK_COMB (@lem5270999) (@lem5270998 x)). Qed.
Lemma lem5271001 (x : type1021) (h1 : term442 x) : term442 x.
Proof. exact (EQ_MP (@lem5271000 x) (@lem5270862 x h1)). Qed.
Lemma lem5271016 (s : real -> Prop) (y : real) (x : real) : (term55 s y x) = (term55 s y x).
Proof. exact (eq_refl (term55 s y x)). Qed.
Lemma lem5271017 (s : real -> Prop) (y : real) : (term56 s y) = (term56 s y).
Proof. exact (fun_ext (fun x : real => @lem5271016 s y x)). Qed.
Lemma lem5271018 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271019 (s : real -> Prop) (y : real) : (term57 s y) = (term57 s y).
Proof. exact (MK_COMB (@lem5271018) (@lem5271017 s y)). Qed.
Lemma lem5271030 (y : real) (s : real -> Prop) : (term72 y s) = (term72 y s).
Proof. exact (eq_refl (term72 y s)). Qed.
Lemma lem5271031 (s : real -> Prop) (y : real) : (term74 s y) = (term74 s y).
Proof. exact (MK_COMB (@lem5271030 y s) (@lem5271019 s y)). Qed.
Lemma lem5271058 (s : real -> Prop) (y : real) (x' : real) : (term204 s y x') = (term204 s y x').
Proof. exact (eq_refl (term204 s y x')). Qed.
Lemma lem5271059 (x' : real) (s : real -> Prop) (y : real) : (term206 x' s y) = (term206 x' s y).
Proof. exact (MK_COMB (@lem5271058 s y x') (@lem5271031 s y)). Qed.
Lemma lem5271074 (s : real -> Prop) (b : real) (x : real) : (term55 s b x) = (term55 s b x).
Proof. exact (eq_refl (term55 s b x)). Qed.
Lemma lem5271075 (s : real -> Prop) (b : real) : (term56 s b) = (term56 s b).
Proof. exact (fun_ext (fun x : real => @lem5271074 s b x)). Qed.
Lemma lem5271076 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271077 (s : real -> Prop) (b : real) : (term57 s b) = (term57 s b).
Proof. exact (MK_COMB (@lem5271076) (@lem5271075 s b)). Qed.
Lemma lem5271086 (s : real -> Prop) : (term38 s) = (term38 s).
Proof. exact (eq_refl (term38 s)). Qed.
Lemma lem5271087 (s : real -> Prop) (b : real) : (term155 s b) = (term155 s b).
Proof. exact (MK_COMB (@lem5271086 s) (@lem5271077 s b)). Qed.
Lemma lem5271088 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5271089 (s : real -> Prop) (b : real) : (term226 s b) = (term226 s b).
Proof. exact (MK_COMB (@lem5271088) (@lem5271087 s b)). Qed.
Lemma lem5271090 (b : real) (x' : real) (s : real -> Prop) (y : real) : (term252 b x' s y) = (term252 b x' s y).
Proof. exact (MK_COMB (@lem5271089 s b) (@lem5271059 x' s y)). Qed.
Lemma lem5271091 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term252 b x' s y.
Proof. exact (EQ_MP (@lem5271090 b x' s y) (@lem5270866 b x' s y h1)). Qed.
Lemma lem5271092 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term206 x' s y.
Proof. exact (proj2 (@lem5271091 b x' s y h1)). Qed.
Lemma lem5271093 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term155 s b.
Proof. exact (proj1 (@lem5271091 b x' s y h1)). Qed.
Lemma lem5271094 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term57 s b.
Proof. exact (proj2 (@lem5271093 b x' s y h1)). Qed.
Lemma lem5271096 (s : real -> Prop) (y : real) (x' : real) (h1 : term168 s y x') : term168 s y x'.
Proof. exact (h1). Qed.
Lemma lem5271097 (s : real -> Prop) (y : real) (h1 : term74 s y) : term74 s y.
Proof. exact (h1). Qed.
Lemma lem5271098 (s : real -> Prop) (y : real) (x' : real) (h1 : term168 s y x') : term62 s y x'.
Proof. exact (proj2 (@lem5271096 s y x' h1)). Qed.
Lemma lem5271102 (s : real -> Prop) (y : real) (h1 : term74 s y) : term57 s y.
Proof. exact (proj2 (@lem5271097 s y h1)). Qed.
Lemma lem5271117 (y : real) (x : real) (z : real) : (term267 y x z) = (term267 y x z).
Proof. exact (eq_refl (term267 y x z)). Qed.
Lemma lem5271118 (y : real) (x : real) : (term269 y x) = (term269 y x).
Proof. exact (fun_ext (fun z : real => @lem5271117 y x z)). Qed.
Lemma lem5271119 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271120 (y : real) (x : real) : (term270 y x) = (term270 y x).
Proof. exact (MK_COMB (@lem5271119) (@lem5271118 y x)). Qed.
Lemma lem5271121 (x : real) : (term271 x) = (term271 x).
Proof. exact (fun_ext (fun y : real => @lem5271120 y x)). Qed.
Lemma lem5271122 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271123 (x : real) : (term272 x) = (term272 x).
Proof. exact (MK_COMB (@lem5271122) (@lem5271121 x)). Qed.
Lemma lem5271124 : term273 = term273.
Proof. exact (fun_ext (fun x : real => @lem5271123 x)). Qed.
Lemma lem5271125 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271127 : term274 = term274.
Proof. exact (MK_COMB (@lem5271125) (@lem5271124)). Qed.
Lemma lem5271128 (h1 : term49) : term274.
Proof. exact (EQ_MP (@lem5271127) (@lem5270901 h1)). Qed.
Lemma lem5271130 {A : Type'} (P : Prop) (Q : A -> Prop) : (term455 A P Q) = (term456 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5271131 (P : Prop) (Q : real -> Prop) : (term457 P Q) = (term458 P Q).
Proof. exact (@lem5271130 real P Q). Qed.
Lemma lem5271132 (x : type1021) (s : real -> Prop) : (term459 x s) = (term460 x s).
Proof. exact (@lem5271131 (s = (@EMPTY real)) (term451 x s)). Qed.
Lemma lem5271133 (x : type1021) (s : real -> Prop) (b : real) : (term461 x s b) = (term450 x s b).
Proof. exact (eq_refl (term461 x s b)). Qed.
Lemma lem5271134 (x : type1021) (s : real -> Prop) : (term462 x s) = (term451 x s).
Proof. exact (fun_ext (fun b : real => @lem5271133 x s b)). Qed.
Lemma lem5271135 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271136 (x : type1021) (s : real -> Prop) : (term463 x s) = (term452 x s).
Proof. exact (MK_COMB (@lem5271135) (@lem5271134 x s)). Qed.
Lemma lem5271137 (s : real -> Prop) : (term286 s) = (term286 s).
Proof. exact (eq_refl (term286 s)). Qed.
Lemma lem5271138 (x : type1021) (s : real -> Prop) : (term459 x s) = (term453 x s).
Proof. exact (MK_COMB (@lem5271137 s) (@lem5271136 x s)). Qed.
Lemma lem5271139 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5271140 (x : type1021) (s : real -> Prop) : (term464 x s) = (term465 x s).
Proof. exact (MK_COMB (@lem5271139) (@lem5271138 x s)). Qed.
Lemma lem5271141 (x : type1021) (s : real -> Prop) (b : real) : (term461 x s b) = (term450 x s b).
Proof. exact (eq_refl (term461 x s b)). Qed.
Lemma lem5271142 (s : real -> Prop) : (term286 s) = (term286 s).
Proof. exact (eq_refl (term286 s)). Qed.
Lemma lem5271143 (x : type1021) (s : real -> Prop) (b : real) : (term466 x s b) = (term467 x s b).
Proof. exact (MK_COMB (@lem5271142 s) (@lem5271141 x s b)). Qed.
Lemma lem5271144 (x : type1021) (s : real -> Prop) : (term468 x s) = (term469 x s).
Proof. exact (fun_ext (fun b : real => @lem5271143 x s b)). Qed.
Lemma lem5271145 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271146 (x : type1021) (s : real -> Prop) : (term460 x s) = (term470 x s).
Proof. exact (MK_COMB (@lem5271145) (@lem5271144 x s)). Qed.
Lemma lem5271147 (x : type1021) (s : real -> Prop) : ((term459 x s) = (term460 x s)) = ((term453 x s) = (term470 x s)).
Proof. exact (MK_COMB (@lem5271140 x s) (@lem5271146 x s)). Qed.
Lemma lem5271148 (x : type1021) (s : real -> Prop) : (term453 x s) = (term470 x s).
Proof. exact (EQ_MP (@lem5271147 x s) (@lem5271132 x s)). Qed.
Lemma lem5271149 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5271150 (x : type1021) (s : real -> Prop) : (term454 x s) = (term471 x s).
Proof. exact (MK_COMB (@lem5271149) (@lem5271148 x s)). Qed.
Lemma lem5271152 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term472 A P Q) = (term473 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5271153 (P : real -> Prop) (Q : real -> Prop) : (term474 P Q) = (term475 P Q).
Proof. exact (@lem5271152 real P Q). Qed.
Lemma lem5271154 (x : type1021) (s : real -> Prop) : (term476 x s) = (term477 x s).
Proof. exact (@lem5271153 (term292 s) (term447 x s)). Qed.
Lemma lem5271155 (s : real -> Prop) (b : real) : (term478 s b) = (term290 s b).
Proof. exact (eq_refl (term478 s b)). Qed.
Lemma lem5271156 (s : real -> Prop) : (term479 s) = (term292 s).
Proof. exact (fun_ext (fun b : real => @lem5271155 s b)). Qed.
Lemma lem5271157 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271158 (s : real -> Prop) : (term480 s) = (term293 s).
Proof. exact (MK_COMB (@lem5271157) (@lem5271156 s)). Qed.
Lemma lem5271159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5271160 (s : real -> Prop) : (term481 s) = (term300 s).
Proof. exact (MK_COMB (@lem5271159) (@lem5271158 s)). Qed.
Lemma lem5271161 (x : type1021) (b : real) (s : real -> Prop) : (term482 x s b) = (term446 x b s).
Proof. exact (eq_refl (term482 x s b)). Qed.
Lemma lem5271162 (x : type1021) (s : real -> Prop) : (term483 x s) = (term447 x s).
Proof. exact (fun_ext (fun b : real => @lem5271161 x b s)). Qed.
Lemma lem5271163 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271164 (x : type1021) (s : real -> Prop) : (term484 x s) = (term448 x s).
Proof. exact (MK_COMB (@lem5271163) (@lem5271162 x s)). Qed.
Lemma lem5271165 (x : type1021) (s : real -> Prop) : (term476 x s) = (term449 x s).
Proof. exact (MK_COMB (@lem5271160 s) (@lem5271164 x s)). Qed.
Lemma lem5271166 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5271167 (x : type1021) (s : real -> Prop) : (term485 x s) = (term486 x s).
Proof. exact (MK_COMB (@lem5271166) (@lem5271165 x s)). Qed.
Lemma lem5271168 (s : real -> Prop) (b : real) : (term478 s b) = (term290 s b).
Proof. exact (eq_refl (term478 s b)). Qed.
Lemma lem5271169 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5271170 (s : real -> Prop) (b : real) : (term487 s b) = (term488 s b).
Proof. exact (MK_COMB (@lem5271169) (@lem5271168 s b)). Qed.
Lemma lem5271171 (x : type1021) (b : real) (s : real -> Prop) : (term482 x s b) = (term446 x b s).
Proof. exact (eq_refl (term482 x s b)). Qed.
Lemma lem5271172 (x : type1021) (b : real) (s : real -> Prop) : (term489 x s b) = (term490 x b s).
Proof. exact (MK_COMB (@lem5271170 s b) (@lem5271171 x b s)). Qed.
Lemma lem5271173 (x : type1021) (s : real -> Prop) : (term491 x s) = (term492 x s).
Proof. exact (fun_ext (fun b : real => @lem5271172 x b s)). Qed.
Lemma lem5271174 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271175 (x : type1021) (s : real -> Prop) : (term477 x s) = (term493 x s).
Proof. exact (MK_COMB (@lem5271174) (@lem5271173 x s)). Qed.
Lemma lem5271176 (x : type1021) (s : real -> Prop) : ((term476 x s) = (term477 x s)) = ((term449 x s) = (term493 x s)).
Proof. exact (MK_COMB (@lem5271167 x s) (@lem5271175 x s)). Qed.
Lemma lem5271177 (x : type1021) (s : real -> Prop) : (term449 x s) = (term493 x s).
Proof. exact (EQ_MP (@lem5271176 x s) (@lem5271154 x s)). Qed.
Lemma lem5271180 (x : type1021) (s : real -> Prop) : (term494 x s) = (term494 x s).
Proof. exact (eq_refl (term494 x s)). Qed.
Lemma lem5271181 (x : type1021) (s : real -> Prop) : (term494 x s) = ((term449 x s) = (term493 x s)).
Proof. exact (eq_refl (term494 x s)). Qed.
Lemma lem5271182 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5271183 (x : type1021) (s : real -> Prop) : ((term494 x s) = (term494 x s)) = ((term494 x s) = ((term449 x s) = (term493 x s))).
Proof. exact (MK_COMB (@lem5271182 x s) (@lem5271181 x s)). Qed.
Lemma lem5271184 (x : type1021) (s : real -> Prop) : (term494 x s) = ((term449 x s) = (term493 x s)).
Proof. exact (eq_refl (term494 x s)). Qed.
Lemma lem5271185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5271186 (x : type1021) (s : real -> Prop) : (term495 x s) = (term496 x s).
Proof. exact (MK_COMB (@lem5271185) (@lem5271184 x s)). Qed.
Lemma lem5271187 (x : type1021) (s : real -> Prop) : ((term449 x s) = (term493 x s)) = ((term449 x s) = (term493 x s)).
Proof. exact (eq_refl ((term449 x s) = (term493 x s))). Qed.
Lemma lem5271188 (x : type1021) (s : real -> Prop) : ((term494 x s) = ((term449 x s) = (term493 x s))) = (((term449 x s) = (term493 x s)) = ((term449 x s) = (term493 x s))).
Proof. exact (MK_COMB (@lem5271186 x s) (@lem5271187 x s)). Qed.
Lemma lem5271189 (x : type1021) (s : real -> Prop) : ((term494 x s) = (term494 x s)) = (((term449 x s) = (term493 x s)) = ((term449 x s) = (term493 x s))).
Proof. exact (TRANS (@lem5271183 x s) (@lem5271188 x s)). Qed.
Lemma lem5271190 (x : type1021) (s : real -> Prop) : ((term449 x s) = (term493 x s)) = ((term449 x s) = (term493 x s)).
Proof. exact (EQ_MP (@lem5271189 x s) (@lem5271180 x s)). Qed.
Lemma lem5271191 (x : type1021) (s : real -> Prop) : (term449 x s) = (term493 x s).
Proof. exact (EQ_MP (@lem5271190 x s) (@lem5271177 x s)). Qed.
Lemma lem5271192 (x : type1021) (s : real -> Prop) : (term438 x s) = (term497 x s).
Proof. exact (MK_COMB (@lem5271150 x s) (@lem5271191 x s)). Qed.
Lemma lem5271194 {A : Type'} (P : A -> Prop) (Q : Prop) : (term498 A P Q) = (term499 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5271195 (P : real -> Prop) (Q : Prop) : (term500 P Q) = (term501 P Q).
Proof. exact (@lem5271194 real P Q). Qed.
Lemma lem5271196 (x : type1021) (s : real -> Prop) : (term502 x s) = (term503 x s).
Proof. exact (@lem5271195 (term469 x s) (term493 x s)). Qed.
Lemma lem5271197 (x : type1021) (s : real -> Prop) (b : real) : (term504 x s b) = (term467 x s b).
Proof. exact (eq_refl (term504 x s b)). Qed.
Lemma lem5271198 (x : type1021) (s : real -> Prop) : (term505 x s) = (term469 x s).
Proof. exact (fun_ext (fun b : real => @lem5271197 x s b)). Qed.
Lemma lem5271199 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271200 (x : type1021) (s : real -> Prop) : (term506 x s) = (term470 x s).
Proof. exact (MK_COMB (@lem5271199) (@lem5271198 x s)). Qed.
Lemma lem5271201 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5271202 (x : type1021) (s : real -> Prop) : (term507 x s) = (term471 x s).
Proof. exact (MK_COMB (@lem5271201) (@lem5271200 x s)). Qed.
Lemma lem5271203 (x : type1021) (s : real -> Prop) : (term493 x s) = (term493 x s).
Proof. exact (eq_refl (term493 x s)). Qed.
Lemma lem5271204 (x : type1021) (s : real -> Prop) : (term502 x s) = (term497 x s).
Proof. exact (MK_COMB (@lem5271202 x s) (@lem5271203 x s)). Qed.
Lemma lem5271205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5271206 (x : type1021) (s : real -> Prop) : (term508 x s) = (term509 x s).
Proof. exact (MK_COMB (@lem5271205) (@lem5271204 x s)). Qed.
Lemma lem5271207 (x : type1021) (s : real -> Prop) (b : real) : (term504 x s b) = (term467 x s b).
Proof. exact (eq_refl (term504 x s b)). Qed.
Lemma lem5271208 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5271209 (x : type1021) (s : real -> Prop) (b : real) : (term510 x s b) = (term511 x s b).
Proof. exact (MK_COMB (@lem5271208) (@lem5271207 x s b)). Qed.
Lemma lem5271210 (x : type1021) (s : real -> Prop) : (term493 x s) = (term493 x s).
Proof. exact (eq_refl (term493 x s)). Qed.
Lemma lem5271211 (b : real) (x : type1021) (s : real -> Prop) : (term512 b x s) = (term513 b x s).
Proof. exact (MK_COMB (@lem5271209 x s b) (@lem5271210 x s)). Qed.
Lemma lem5271212 (x : type1021) (s : real -> Prop) : (term514 x s) = (term515 x s).
Proof. exact (fun_ext (fun b : real => @lem5271211 b x s)). Qed.
Lemma lem5271213 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271214 (x : type1021) (s : real -> Prop) : (term503 x s) = (term516 x s).
Proof. exact (MK_COMB (@lem5271213) (@lem5271212 x s)). Qed.
Lemma lem5271215 (x : type1021) (s : real -> Prop) : ((term502 x s) = (term503 x s)) = ((term497 x s) = (term516 x s)).
Proof. exact (MK_COMB (@lem5271206 x s) (@lem5271214 x s)). Qed.
Lemma lem5271216 (x : type1021) (s : real -> Prop) : (term497 x s) = (term516 x s).
Proof. exact (EQ_MP (@lem5271215 x s) (@lem5271196 x s)). Qed.
Lemma lem5271218 {A : Type'} (P : Prop) (Q : A -> Prop) : (term455 A P Q) = (term456 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5271219 (P : Prop) (Q : real -> Prop) : (term457 P Q) = (term458 P Q).
Proof. exact (@lem5271218 real P Q). Qed.
Lemma lem5271220 (b : real) (x : type1021) (s : real -> Prop) : (term517 b x s) = (term518 b x s).
Proof. exact (@lem5271219 (term467 x s b) (term492 x s)). Qed.
Lemma lem5271221 (x : type1021) (b : real) (s : real -> Prop) : (term519 x s b) = (term490 x b s).
Proof. exact (eq_refl (term519 x s b)). Qed.
Lemma lem5271222 (x : type1021) (s : real -> Prop) : (term520 x s) = (term492 x s).
Proof. exact (fun_ext (fun b : real => @lem5271221 x b s)). Qed.
Lemma lem5271223 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271224 (x : type1021) (s : real -> Prop) : (term521 x s) = (term493 x s).
Proof. exact (MK_COMB (@lem5271223) (@lem5271222 x s)). Qed.
Lemma lem5271225 (x : type1021) (s : real -> Prop) (b : real) : (term511 x s b) = (term511 x s b).
Proof. exact (eq_refl (term511 x s b)). Qed.
Lemma lem5271226 (b : real) (x : type1021) (s : real -> Prop) : (term517 b x s) = (term513 b x s).
Proof. exact (MK_COMB (@lem5271225 x s b) (@lem5271224 x s)). Qed.
Lemma lem5271227 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5271228 (b : real) (x : type1021) (s : real -> Prop) : (term522 b x s) = (term523 b x s).
Proof. exact (MK_COMB (@lem5271227) (@lem5271226 b x s)). Qed.
Lemma lem5271229 (x : type1021) (b' : real) (s : real -> Prop) : (term519 x s b') = (term490 x b' s).
Proof. exact (eq_refl (term519 x s b')). Qed.
Lemma lem5271230 (x : type1021) (s : real -> Prop) (b : real) : (term511 x s b) = (term511 x s b).
Proof. exact (eq_refl (term511 x s b)). Qed.
Lemma lem5271231 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term524 b x s b') = (term525 b x b' s).
Proof. exact (MK_COMB (@lem5271230 x s b) (@lem5271229 x b' s)). Qed.
Lemma lem5271232 (b : real) (x : type1021) (s : real -> Prop) : (term526 b x s) = (term527 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5271231 b x b' s)). Qed.
Lemma lem5271233 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271234 (b : real) (x : type1021) (s : real -> Prop) : (term518 b x s) = (term528 b x s).
Proof. exact (MK_COMB (@lem5271233) (@lem5271232 b x s)). Qed.
Lemma lem5271235 (b : real) (x : type1021) (s : real -> Prop) : ((term517 b x s) = (term518 b x s)) = ((term513 b x s) = (term528 b x s)).
Proof. exact (MK_COMB (@lem5271228 b x s) (@lem5271234 b x s)). Qed.
Lemma lem5271236 (b : real) (x : type1021) (s : real -> Prop) : (term513 b x s) = (term528 b x s).
Proof. exact (EQ_MP (@lem5271235 b x s) (@lem5271220 b x s)). Qed.
Lemma lem5271237 (x : type1021) (s : real -> Prop) : (term515 x s) = (term529 x s).
Proof. exact (fun_ext (fun b : real => @lem5271236 b x s)). Qed.
Lemma lem5271238 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271239 (x : type1021) (s : real -> Prop) : (term516 x s) = (term530 x s).
Proof. exact (MK_COMB (@lem5271238) (@lem5271237 x s)). Qed.
Lemma lem5271240 (x : type1021) (s : real -> Prop) : (term497 x s) = (term530 x s).
Proof. exact (TRANS (@lem5271216 x s) (@lem5271239 x s)). Qed.
Lemma lem5271241 (x : type1021) (s : real -> Prop) : (term438 x s) = (term530 x s).
Proof. exact (TRANS (@lem5271192 x s) (@lem5271240 x s)). Qed.
Lemma lem5271242 (x : type1021) : (term440 x) = (term531 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5271241 x s)). Qed.
Lemma lem5271243 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5271244 (x : type1021) : (term442 x) = (term532 x).
Proof. exact (MK_COMB (@lem5271243) (@lem5271242 x)). Qed.
Lemma lem5271261 (x : type1021) (b' : real) (s : real -> Prop) : (term446 x b' s) = (term533 x b' s).
Proof. exact (@lem19699 (term534 x b' s) (term535 x s b') (term23 b' s)). Qed.
Lemma lem5271270 (s : real -> Prop) (b' : real) : (term488 s b') = (term488 s b').
Proof. exact (eq_refl (term488 s b')). Qed.
Lemma lem5271271 (x : type1021) (b' : real) (s : real -> Prop) : (term490 x b' s) = (term536 x b' s).
Proof. exact (MK_COMB (@lem5271270 s b') (@lem5271261 x b' s)). Qed.
Lemma lem5271288 (x : type1021) (s : real -> Prop) (b : real) : (term467 x s b) = (term537 x s b).
Proof. exact (@lem19490 (term534 x b s) (s = (@EMPTY real)) (term535 x s b)). Qed.
Lemma lem5271289 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5271290 (x : type1021) (s : real -> Prop) (b : real) : (term511 x s b) = (term538 x s b).
Proof. exact (MK_COMB (@lem5271289) (@lem5271288 x s b)). Qed.
Lemma lem5271291 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term525 b x b' s) = (term539 b x b' s).
Proof. exact (MK_COMB (@lem5271290 x s b) (@lem5271271 x b' s)). Qed.
Lemma lem5271292 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term539 b x b' s) = (term540 b x b' s).
Proof. exact (@lem19490 (term290 s b') (term537 x s b) (term533 x b' s)). Qed.
Lemma lem5271293 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term541 b x b' s) = (term542 b x b' s).
Proof. exact (@lem19490 (term543 x b' s) (term537 x s b) (term544 x b' s)). Qed.
Lemma lem5271300 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term545 b x b' s) = (term546 b x b' s).
Proof. exact (@lem19699 (term547 x b s) (term548 x s b) (term544 x b' s)). Qed.
Lemma lem5271307 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term549 b x b' s) = (term550 b x b' s).
Proof. exact (@lem19699 (term547 x b s) (term548 x s b) (term543 x b' s)). Qed.
Lemma lem5271308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5271309 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term551 b x b' s) = (term552 b x b' s).
Proof. exact (MK_COMB (@lem5271308) (@lem5271307 b x b' s)). Qed.
Lemma lem5271310 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term542 b x b' s) = (term553 b x b' s).
Proof. exact (MK_COMB (@lem5271309 b x b' s) (@lem5271300 b x b' s)). Qed.
Lemma lem5271311 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term541 b x b' s) = (term553 b x b' s).
Proof. exact (TRANS (@lem5271293 b x b' s) (@lem5271310 b x b' s)). Qed.
Lemma lem5271318 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term554 x b s b') = (term555 x b s b').
Proof. exact (@lem19699 (term547 x b s) (term548 x s b) (term290 s b')). Qed.
Lemma lem5271319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5271320 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term556 x b s b') = (term557 x b s b').
Proof. exact (MK_COMB (@lem5271319) (@lem5271318 x b s b')). Qed.
Lemma lem5271321 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term540 b x b' s) = (term558 b x b' s).
Proof. exact (MK_COMB (@lem5271320 x b s b') (@lem5271311 b x b' s)). Qed.
Lemma lem5271322 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term539 b x b' s) = (term558 b x b' s).
Proof. exact (TRANS (@lem5271292 b x b' s) (@lem5271321 b x b' s)). Qed.
Lemma lem5271323 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term525 b x b' s) = (term558 b x b' s).
Proof. exact (TRANS (@lem5271291 b x b' s) (@lem5271322 b x b' s)). Qed.
Lemma lem5271324 (b : real) (x : type1021) (s : real -> Prop) : (term527 b x s) = (term559 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5271323 b x b' s)). Qed.
Lemma lem5271325 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271326 (b : real) (x : type1021) (s : real -> Prop) : (term528 b x s) = (term560 b x s).
Proof. exact (MK_COMB (@lem5271325) (@lem5271324 b x s)). Qed.
Lemma lem5271327 (x : type1021) (s : real -> Prop) : (term529 x s) = (term561 x s).
Proof. exact (fun_ext (fun b : real => @lem5271326 b x s)). Qed.
Lemma lem5271328 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271329 (x : type1021) (s : real -> Prop) : (term530 x s) = (term562 x s).
Proof. exact (MK_COMB (@lem5271328) (@lem5271327 x s)). Qed.
Lemma lem5271330 (x : type1021) : (term531 x) = (term563 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5271329 x s)). Qed.
Lemma lem5271331 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5271332 (x : type1021) : (term532 x) = (term564 x).
Proof. exact (MK_COMB (@lem5271331) (@lem5271330 x)). Qed.
Lemma lem5271333 (x : type1021) : (term442 x) = (term564 x).
Proof. exact (TRANS (@lem5271244 x) (@lem5271332 x)). Qed.
Lemma lem5271334 (x : type1021) (h1 : term442 x) : term564 x.
Proof. exact (EQ_MP (@lem5271333 x) (@lem5271001 x h1)). Qed.
Lemma lem5271346 (s : real -> Prop) (b : real) (x : real) : (term55 s b x) = (term55 s b x).
Proof. exact (eq_refl (term55 s b x)). Qed.
Lemma lem5271347 (s : real -> Prop) (b : real) : (term56 s b) = (term56 s b).
Proof. exact (fun_ext (fun x : real => @lem5271346 s b x)). Qed.
Lemma lem5271348 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271350 (s : real -> Prop) (b : real) : (term57 s b) = (term57 s b).
Proof. exact (MK_COMB (@lem5271348) (@lem5271347 s b)). Qed.
Lemma lem5271351 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term57 s b.
Proof. exact (EQ_MP (@lem5271350 s b) (@lem5271094 b x' s y h1)). Qed.
Lemma lem5271390 {A : Type'} (P : Prop) (Q : A -> Prop) : (term455 A P Q) = (term456 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5271391 (P : Prop) (Q : real -> Prop) : (term457 P Q) = (term458 P Q).
Proof. exact (@lem5271390 real P Q). Qed.
Lemma lem5271392 (x : type1021) (s : real -> Prop) : (term459 x s) = (term460 x s).
Proof. exact (@lem5271391 (s = (@EMPTY real)) (term451 x s)). Qed.
Lemma lem5271393 (x : type1021) (s : real -> Prop) (b : real) : (term461 x s b) = (term450 x s b).
Proof. exact (eq_refl (term461 x s b)). Qed.
Lemma lem5271394 (x : type1021) (s : real -> Prop) : (term462 x s) = (term451 x s).
Proof. exact (fun_ext (fun b : real => @lem5271393 x s b)). Qed.
Lemma lem5271395 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271396 (x : type1021) (s : real -> Prop) : (term463 x s) = (term452 x s).
Proof. exact (MK_COMB (@lem5271395) (@lem5271394 x s)). Qed.
Lemma lem5271397 (s : real -> Prop) : (term286 s) = (term286 s).
Proof. exact (eq_refl (term286 s)). Qed.
Lemma lem5271398 (x : type1021) (s : real -> Prop) : (term459 x s) = (term453 x s).
Proof. exact (MK_COMB (@lem5271397 s) (@lem5271396 x s)). Qed.
Lemma lem5271399 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5271400 (x : type1021) (s : real -> Prop) : (term464 x s) = (term465 x s).
Proof. exact (MK_COMB (@lem5271399) (@lem5271398 x s)). Qed.
Lemma lem5271401 (x : type1021) (s : real -> Prop) (b : real) : (term461 x s b) = (term450 x s b).
Proof. exact (eq_refl (term461 x s b)). Qed.
Lemma lem5271402 (s : real -> Prop) : (term286 s) = (term286 s).
Proof. exact (eq_refl (term286 s)). Qed.
Lemma lem5271403 (x : type1021) (s : real -> Prop) (b : real) : (term466 x s b) = (term467 x s b).
Proof. exact (MK_COMB (@lem5271402 s) (@lem5271401 x s b)). Qed.
Lemma lem5271404 (x : type1021) (s : real -> Prop) : (term468 x s) = (term469 x s).
Proof. exact (fun_ext (fun b : real => @lem5271403 x s b)). Qed.
Lemma lem5271405 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271406 (x : type1021) (s : real -> Prop) : (term460 x s) = (term470 x s).
Proof. exact (MK_COMB (@lem5271405) (@lem5271404 x s)). Qed.
Lemma lem5271407 (x : type1021) (s : real -> Prop) : ((term459 x s) = (term460 x s)) = ((term453 x s) = (term470 x s)).
Proof. exact (MK_COMB (@lem5271400 x s) (@lem5271406 x s)). Qed.
Lemma lem5271408 (x : type1021) (s : real -> Prop) : (term453 x s) = (term470 x s).
Proof. exact (EQ_MP (@lem5271407 x s) (@lem5271392 x s)). Qed.
Lemma lem5271409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5271410 (x : type1021) (s : real -> Prop) : (term454 x s) = (term471 x s).
Proof. exact (MK_COMB (@lem5271409) (@lem5271408 x s)). Qed.
Lemma lem5271412 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term472 A P Q) = (term473 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5271413 (P : real -> Prop) (Q : real -> Prop) : (term474 P Q) = (term475 P Q).
Proof. exact (@lem5271412 real P Q). Qed.
Lemma lem5271414 (x : type1021) (s : real -> Prop) : (term476 x s) = (term477 x s).
Proof. exact (@lem5271413 (term292 s) (term447 x s)). Qed.
Lemma lem5271415 (s : real -> Prop) (b : real) : (term478 s b) = (term290 s b).
Proof. exact (eq_refl (term478 s b)). Qed.
Lemma lem5271416 (s : real -> Prop) : (term479 s) = (term292 s).
Proof. exact (fun_ext (fun b : real => @lem5271415 s b)). Qed.
Lemma lem5271417 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271418 (s : real -> Prop) : (term480 s) = (term293 s).
Proof. exact (MK_COMB (@lem5271417) (@lem5271416 s)). Qed.
Lemma lem5271419 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5271420 (s : real -> Prop) : (term481 s) = (term300 s).
Proof. exact (MK_COMB (@lem5271419) (@lem5271418 s)). Qed.
Lemma lem5271421 (x : type1021) (b : real) (s : real -> Prop) : (term482 x s b) = (term446 x b s).
Proof. exact (eq_refl (term482 x s b)). Qed.
Lemma lem5271422 (x : type1021) (s : real -> Prop) : (term483 x s) = (term447 x s).
Proof. exact (fun_ext (fun b : real => @lem5271421 x b s)). Qed.
Lemma lem5271423 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271424 (x : type1021) (s : real -> Prop) : (term484 x s) = (term448 x s).
Proof. exact (MK_COMB (@lem5271423) (@lem5271422 x s)). Qed.
Lemma lem5271425 (x : type1021) (s : real -> Prop) : (term476 x s) = (term449 x s).
Proof. exact (MK_COMB (@lem5271420 s) (@lem5271424 x s)). Qed.
Lemma lem5271426 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5271427 (x : type1021) (s : real -> Prop) : (term485 x s) = (term486 x s).
Proof. exact (MK_COMB (@lem5271426) (@lem5271425 x s)). Qed.
Lemma lem5271428 (s : real -> Prop) (b : real) : (term478 s b) = (term290 s b).
Proof. exact (eq_refl (term478 s b)). Qed.
Lemma lem5271429 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5271430 (s : real -> Prop) (b : real) : (term487 s b) = (term488 s b).
Proof. exact (MK_COMB (@lem5271429) (@lem5271428 s b)). Qed.
Lemma lem5271431 (x : type1021) (b : real) (s : real -> Prop) : (term482 x s b) = (term446 x b s).
Proof. exact (eq_refl (term482 x s b)). Qed.
Lemma lem5271432 (x : type1021) (b : real) (s : real -> Prop) : (term489 x s b) = (term490 x b s).
Proof. exact (MK_COMB (@lem5271430 s b) (@lem5271431 x b s)). Qed.
Lemma lem5271433 (x : type1021) (s : real -> Prop) : (term491 x s) = (term492 x s).
Proof. exact (fun_ext (fun b : real => @lem5271432 x b s)). Qed.
Lemma lem5271434 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271435 (x : type1021) (s : real -> Prop) : (term477 x s) = (term493 x s).
Proof. exact (MK_COMB (@lem5271434) (@lem5271433 x s)). Qed.
Lemma lem5271436 (x : type1021) (s : real -> Prop) : ((term476 x s) = (term477 x s)) = ((term449 x s) = (term493 x s)).
Proof. exact (MK_COMB (@lem5271427 x s) (@lem5271435 x s)). Qed.
Lemma lem5271437 (x : type1021) (s : real -> Prop) : (term449 x s) = (term493 x s).
Proof. exact (EQ_MP (@lem5271436 x s) (@lem5271414 x s)). Qed.
Lemma lem5271440 (x : type1021) (s : real -> Prop) : (term494 x s) = (term494 x s).
Proof. exact (eq_refl (term494 x s)). Qed.
Lemma lem5271441 (x : type1021) (s : real -> Prop) : (term494 x s) = ((term449 x s) = (term493 x s)).
Proof. exact (eq_refl (term494 x s)). Qed.
Lemma lem5271442 (x : type1021) (s : real -> Prop) : (term495 x s) = (term495 x s).
Proof. exact (eq_refl (term495 x s)). Qed.
Lemma lem5271443 (x : type1021) (s : real -> Prop) : ((term494 x s) = (term494 x s)) = ((term494 x s) = ((term449 x s) = (term493 x s))).
Proof. exact (MK_COMB (@lem5271442 x s) (@lem5271441 x s)). Qed.
Lemma lem5271444 (x : type1021) (s : real -> Prop) : (term494 x s) = ((term449 x s) = (term493 x s)).
Proof. exact (eq_refl (term494 x s)). Qed.
Lemma lem5271445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5271446 (x : type1021) (s : real -> Prop) : (term495 x s) = (term496 x s).
Proof. exact (MK_COMB (@lem5271445) (@lem5271444 x s)). Qed.
Lemma lem5271447 (x : type1021) (s : real -> Prop) : ((term449 x s) = (term493 x s)) = ((term449 x s) = (term493 x s)).
Proof. exact (eq_refl ((term449 x s) = (term493 x s))). Qed.
Lemma lem5271448 (x : type1021) (s : real -> Prop) : ((term494 x s) = ((term449 x s) = (term493 x s))) = (((term449 x s) = (term493 x s)) = ((term449 x s) = (term493 x s))).
Proof. exact (MK_COMB (@lem5271446 x s) (@lem5271447 x s)). Qed.
Lemma lem5271449 (x : type1021) (s : real -> Prop) : ((term494 x s) = (term494 x s)) = (((term449 x s) = (term493 x s)) = ((term449 x s) = (term493 x s))).
Proof. exact (TRANS (@lem5271443 x s) (@lem5271448 x s)). Qed.
Lemma lem5271450 (x : type1021) (s : real -> Prop) : ((term449 x s) = (term493 x s)) = ((term449 x s) = (term493 x s)).
Proof. exact (EQ_MP (@lem5271449 x s) (@lem5271440 x s)). Qed.
Lemma lem5271451 (x : type1021) (s : real -> Prop) : (term449 x s) = (term493 x s).
Proof. exact (EQ_MP (@lem5271450 x s) (@lem5271437 x s)). Qed.
Lemma lem5271452 (x : type1021) (s : real -> Prop) : (term438 x s) = (term497 x s).
Proof. exact (MK_COMB (@lem5271410 x s) (@lem5271451 x s)). Qed.
Lemma lem5271454 {A : Type'} (P : A -> Prop) (Q : Prop) : (term498 A P Q) = (term499 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5271455 (P : real -> Prop) (Q : Prop) : (term500 P Q) = (term501 P Q).
Proof. exact (@lem5271454 real P Q). Qed.
Lemma lem5271456 (x : type1021) (s : real -> Prop) : (term502 x s) = (term503 x s).
Proof. exact (@lem5271455 (term469 x s) (term493 x s)). Qed.
Lemma lem5271457 (x : type1021) (s : real -> Prop) (b : real) : (term504 x s b) = (term467 x s b).
Proof. exact (eq_refl (term504 x s b)). Qed.
Lemma lem5271458 (x : type1021) (s : real -> Prop) : (term505 x s) = (term469 x s).
Proof. exact (fun_ext (fun b : real => @lem5271457 x s b)). Qed.
Lemma lem5271459 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271460 (x : type1021) (s : real -> Prop) : (term506 x s) = (term470 x s).
Proof. exact (MK_COMB (@lem5271459) (@lem5271458 x s)). Qed.
Lemma lem5271461 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5271462 (x : type1021) (s : real -> Prop) : (term507 x s) = (term471 x s).
Proof. exact (MK_COMB (@lem5271461) (@lem5271460 x s)). Qed.
Lemma lem5271463 (x : type1021) (s : real -> Prop) : (term493 x s) = (term493 x s).
Proof. exact (eq_refl (term493 x s)). Qed.
Lemma lem5271464 (x : type1021) (s : real -> Prop) : (term502 x s) = (term497 x s).
Proof. exact (MK_COMB (@lem5271462 x s) (@lem5271463 x s)). Qed.
Lemma lem5271465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5271466 (x : type1021) (s : real -> Prop) : (term508 x s) = (term509 x s).
Proof. exact (MK_COMB (@lem5271465) (@lem5271464 x s)). Qed.
Lemma lem5271467 (x : type1021) (s : real -> Prop) (b : real) : (term504 x s b) = (term467 x s b).
Proof. exact (eq_refl (term504 x s b)). Qed.
Lemma lem5271468 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5271469 (x : type1021) (s : real -> Prop) (b : real) : (term510 x s b) = (term511 x s b).
Proof. exact (MK_COMB (@lem5271468) (@lem5271467 x s b)). Qed.
Lemma lem5271470 (x : type1021) (s : real -> Prop) : (term493 x s) = (term493 x s).
Proof. exact (eq_refl (term493 x s)). Qed.
Lemma lem5271471 (b : real) (x : type1021) (s : real -> Prop) : (term512 b x s) = (term513 b x s).
Proof. exact (MK_COMB (@lem5271469 x s b) (@lem5271470 x s)). Qed.
Lemma lem5271472 (x : type1021) (s : real -> Prop) : (term514 x s) = (term515 x s).
Proof. exact (fun_ext (fun b : real => @lem5271471 b x s)). Qed.
Lemma lem5271473 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271474 (x : type1021) (s : real -> Prop) : (term503 x s) = (term516 x s).
Proof. exact (MK_COMB (@lem5271473) (@lem5271472 x s)). Qed.
Lemma lem5271475 (x : type1021) (s : real -> Prop) : ((term502 x s) = (term503 x s)) = ((term497 x s) = (term516 x s)).
Proof. exact (MK_COMB (@lem5271466 x s) (@lem5271474 x s)). Qed.
Lemma lem5271476 (x : type1021) (s : real -> Prop) : (term497 x s) = (term516 x s).
Proof. exact (EQ_MP (@lem5271475 x s) (@lem5271456 x s)). Qed.
Lemma lem5271478 {A : Type'} (P : Prop) (Q : A -> Prop) : (term455 A P Q) = (term456 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5271479 (P : Prop) (Q : real -> Prop) : (term457 P Q) = (term458 P Q).
Proof. exact (@lem5271478 real P Q). Qed.
Lemma lem5271480 (b : real) (x : type1021) (s : real -> Prop) : (term517 b x s) = (term518 b x s).
Proof. exact (@lem5271479 (term467 x s b) (term492 x s)). Qed.
Lemma lem5271481 (x : type1021) (b : real) (s : real -> Prop) : (term519 x s b) = (term490 x b s).
Proof. exact (eq_refl (term519 x s b)). Qed.
Lemma lem5271482 (x : type1021) (s : real -> Prop) : (term520 x s) = (term492 x s).
Proof. exact (fun_ext (fun b : real => @lem5271481 x b s)). Qed.
Lemma lem5271483 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271484 (x : type1021) (s : real -> Prop) : (term521 x s) = (term493 x s).
Proof. exact (MK_COMB (@lem5271483) (@lem5271482 x s)). Qed.
Lemma lem5271485 (x : type1021) (s : real -> Prop) (b : real) : (term511 x s b) = (term511 x s b).
Proof. exact (eq_refl (term511 x s b)). Qed.
Lemma lem5271486 (b : real) (x : type1021) (s : real -> Prop) : (term517 b x s) = (term513 b x s).
Proof. exact (MK_COMB (@lem5271485 x s b) (@lem5271484 x s)). Qed.
Lemma lem5271487 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5271488 (b : real) (x : type1021) (s : real -> Prop) : (term522 b x s) = (term523 b x s).
Proof. exact (MK_COMB (@lem5271487) (@lem5271486 b x s)). Qed.
Lemma lem5271489 (x : type1021) (b' : real) (s : real -> Prop) : (term519 x s b') = (term490 x b' s).
Proof. exact (eq_refl (term519 x s b')). Qed.
Lemma lem5271490 (x : type1021) (s : real -> Prop) (b : real) : (term511 x s b) = (term511 x s b).
Proof. exact (eq_refl (term511 x s b)). Qed.
Lemma lem5271491 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term524 b x s b') = (term525 b x b' s).
Proof. exact (MK_COMB (@lem5271490 x s b) (@lem5271489 x b' s)). Qed.
Lemma lem5271492 (b : real) (x : type1021) (s : real -> Prop) : (term526 b x s) = (term527 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5271491 b x b' s)). Qed.
Lemma lem5271493 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271494 (b : real) (x : type1021) (s : real -> Prop) : (term518 b x s) = (term528 b x s).
Proof. exact (MK_COMB (@lem5271493) (@lem5271492 b x s)). Qed.
Lemma lem5271495 (b : real) (x : type1021) (s : real -> Prop) : ((term517 b x s) = (term518 b x s)) = ((term513 b x s) = (term528 b x s)).
Proof. exact (MK_COMB (@lem5271488 b x s) (@lem5271494 b x s)). Qed.
Lemma lem5271496 (b : real) (x : type1021) (s : real -> Prop) : (term513 b x s) = (term528 b x s).
Proof. exact (EQ_MP (@lem5271495 b x s) (@lem5271480 b x s)). Qed.
Lemma lem5271497 (x : type1021) (s : real -> Prop) : (term515 x s) = (term529 x s).
Proof. exact (fun_ext (fun b : real => @lem5271496 b x s)). Qed.
Lemma lem5271498 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271499 (x : type1021) (s : real -> Prop) : (term516 x s) = (term530 x s).
Proof. exact (MK_COMB (@lem5271498) (@lem5271497 x s)). Qed.
Lemma lem5271500 (x : type1021) (s : real -> Prop) : (term497 x s) = (term530 x s).
Proof. exact (TRANS (@lem5271476 x s) (@lem5271499 x s)). Qed.
Lemma lem5271501 (x : type1021) (s : real -> Prop) : (term438 x s) = (term530 x s).
Proof. exact (TRANS (@lem5271452 x s) (@lem5271500 x s)). Qed.
Lemma lem5271502 (x : type1021) : (term440 x) = (term531 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5271501 x s)). Qed.
Lemma lem5271503 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5271504 (x : type1021) : (term442 x) = (term532 x).
Proof. exact (MK_COMB (@lem5271503) (@lem5271502 x)). Qed.
Lemma lem5271521 (x : type1021) (b' : real) (s : real -> Prop) : (term446 x b' s) = (term533 x b' s).
Proof. exact (@lem19699 (term534 x b' s) (term535 x s b') (term23 b' s)). Qed.
Lemma lem5271530 (s : real -> Prop) (b' : real) : (term488 s b') = (term488 s b').
Proof. exact (eq_refl (term488 s b')). Qed.
Lemma lem5271531 (x : type1021) (b' : real) (s : real -> Prop) : (term490 x b' s) = (term536 x b' s).
Proof. exact (MK_COMB (@lem5271530 s b') (@lem5271521 x b' s)). Qed.
Lemma lem5271548 (x : type1021) (s : real -> Prop) (b : real) : (term467 x s b) = (term537 x s b).
Proof. exact (@lem19490 (term534 x b s) (s = (@EMPTY real)) (term535 x s b)). Qed.
Lemma lem5271549 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5271550 (x : type1021) (s : real -> Prop) (b : real) : (term511 x s b) = (term538 x s b).
Proof. exact (MK_COMB (@lem5271549) (@lem5271548 x s b)). Qed.
Lemma lem5271551 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term525 b x b' s) = (term539 b x b' s).
Proof. exact (MK_COMB (@lem5271550 x s b) (@lem5271531 x b' s)). Qed.
Lemma lem5271552 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term539 b x b' s) = (term540 b x b' s).
Proof. exact (@lem19490 (term290 s b') (term537 x s b) (term533 x b' s)). Qed.
Lemma lem5271553 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term541 b x b' s) = (term542 b x b' s).
Proof. exact (@lem19490 (term543 x b' s) (term537 x s b) (term544 x b' s)). Qed.
Lemma lem5271560 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term545 b x b' s) = (term546 b x b' s).
Proof. exact (@lem19699 (term547 x b s) (term548 x s b) (term544 x b' s)). Qed.
Lemma lem5271567 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term549 b x b' s) = (term550 b x b' s).
Proof. exact (@lem19699 (term547 x b s) (term548 x s b) (term543 x b' s)). Qed.
Lemma lem5271568 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5271569 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term551 b x b' s) = (term552 b x b' s).
Proof. exact (MK_COMB (@lem5271568) (@lem5271567 b x b' s)). Qed.
Lemma lem5271570 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term542 b x b' s) = (term553 b x b' s).
Proof. exact (MK_COMB (@lem5271569 b x b' s) (@lem5271560 b x b' s)). Qed.
Lemma lem5271571 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term541 b x b' s) = (term553 b x b' s).
Proof. exact (TRANS (@lem5271553 b x b' s) (@lem5271570 b x b' s)). Qed.
Lemma lem5271578 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term554 x b s b') = (term555 x b s b').
Proof. exact (@lem19699 (term547 x b s) (term548 x s b) (term290 s b')). Qed.
Lemma lem5271579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5271580 (x : type1021) (b : real) (s : real -> Prop) (b' : real) : (term556 x b s b') = (term557 x b s b').
Proof. exact (MK_COMB (@lem5271579) (@lem5271578 x b s b')). Qed.
Lemma lem5271581 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term540 b x b' s) = (term558 b x b' s).
Proof. exact (MK_COMB (@lem5271580 x b s b') (@lem5271571 b x b' s)). Qed.
Lemma lem5271582 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term539 b x b' s) = (term558 b x b' s).
Proof. exact (TRANS (@lem5271552 b x b' s) (@lem5271581 b x b' s)). Qed.
Lemma lem5271583 (b : real) (x : type1021) (b' : real) (s : real -> Prop) : (term525 b x b' s) = (term558 b x b' s).
Proof. exact (TRANS (@lem5271551 b x b' s) (@lem5271582 b x b' s)). Qed.
Lemma lem5271584 (b : real) (x : type1021) (s : real -> Prop) : (term527 b x s) = (term559 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5271583 b x b' s)). Qed.
Lemma lem5271585 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271586 (b : real) (x : type1021) (s : real -> Prop) : (term528 b x s) = (term560 b x s).
Proof. exact (MK_COMB (@lem5271585) (@lem5271584 b x s)). Qed.
Lemma lem5271587 (x : type1021) (s : real -> Prop) : (term529 x s) = (term561 x s).
Proof. exact (fun_ext (fun b : real => @lem5271586 b x s)). Qed.
Lemma lem5271588 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271589 (x : type1021) (s : real -> Prop) : (term530 x s) = (term562 x s).
Proof. exact (MK_COMB (@lem5271588) (@lem5271587 x s)). Qed.
Lemma lem5271590 (x : type1021) : (term531 x) = (term563 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5271589 x s)). Qed.
Lemma lem5271591 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5271592 (x : type1021) : (term532 x) = (term564 x).
Proof. exact (MK_COMB (@lem5271591) (@lem5271590 x)). Qed.
Lemma lem5271593 (x : type1021) : (term442 x) = (term564 x).
Proof. exact (TRANS (@lem5271504 x) (@lem5271592 x)). Qed.
Lemma lem5271594 (x : type1021) (h1 : term442 x) : term564 x.
Proof. exact (EQ_MP (@lem5271593 x) (@lem5271001 x h1)). Qed.
Lemma lem5271623 (s : real -> Prop) (y : real) (x : real) : (term55 s y x) = (term55 s y x).
Proof. exact (eq_refl (term55 s y x)). Qed.
Lemma lem5271624 (s : real -> Prop) (y : real) : (term56 s y) = (term56 s y).
Proof. exact (fun_ext (fun x : real => @lem5271623 s y x)). Qed.
Lemma lem5271625 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5271627 (s : real -> Prop) (y : real) : (term57 s y) = (term57 s y).
Proof. exact (MK_COMB (@lem5271625) (@lem5271624 s y)). Qed.
Lemma lem5271628 (s : real -> Prop) (y : real) (h1 : term74 s y) : term57 s y.
Proof. exact (EQ_MP (@lem5271627 s y) (@lem5271102 s y h1)). Qed.
Lemma lem5271629 (_68980 : real) (h1 : term49) : term565 _68980.
Proof. exact (@lem5271128 h1 _68980). Qed.
Lemma lem5271630 (_68980 : real) : (term565 _68980) = (term272 _68980).
Proof. exact (eq_refl (term565 _68980)). Qed.
Lemma lem5271631 (_68980 : real) (h1 : term49) : term272 _68980.
Proof. exact (EQ_MP (@lem5271630 _68980) (@lem5271629 _68980 h1)). Qed.
Lemma lem5271632 (_68980 : real) (_68981 : real) (h1 : term49) : term566 _68980 _68981.
Proof. exact (@lem5271631 _68980 h1 _68981). Qed.
Lemma lem5271633 (_68981 : real) (_68980 : real) : (term566 _68980 _68981) = (term270 _68981 _68980).
Proof. exact (eq_refl (term566 _68980 _68981)). Qed.
Lemma lem5271634 (_68981 : real) (_68980 : real) (h1 : term49) : term270 _68981 _68980.
Proof. exact (EQ_MP (@lem5271633 _68981 _68980) (@lem5271632 _68980 _68981 h1)). Qed.
Lemma lem5271635 (_68981 : real) (_68980 : real) (_68982 : real) (h1 : term49) : term567 _68981 _68980 _68982.
Proof. exact (@lem5271634 _68981 _68980 h1 _68982). Qed.
Lemma lem5271636 (_68981 : real) (_68980 : real) (_68982 : real) : (term567 _68981 _68980 _68982) = (term267 _68981 _68980 _68982).
Proof. exact (eq_refl (term567 _68981 _68980 _68982)). Qed.
Lemma lem5271637 (_68981 : real) (_68980 : real) (_68982 : real) (h1 : term49) : term267 _68981 _68980 _68982.
Proof. exact (EQ_MP (@lem5271636 _68981 _68980 _68982) (@lem5271635 _68981 _68980 _68982 h1)). Qed.
Lemma lem5271638 (_68983 : real -> Prop) (x : type1021) (h1 : term442 x) : term568 x _68983.
Proof. exact (@lem5271334 x h1 _68983). Qed.
Lemma lem5271639 (x : type1021) (_68983 : real -> Prop) : (term568 x _68983) = (term562 x _68983).
Proof. exact (eq_refl (term568 x _68983)). Qed.
Lemma lem5271640 (_68983 : real -> Prop) (x : type1021) (h1 : term442 x) : term562 x _68983.
Proof. exact (EQ_MP (@lem5271639 x _68983) (@lem5271638 _68983 x h1)). Qed.
Lemma lem5271641 (_68983 : real -> Prop) (_68984 : real) (x : type1021) (h1 : term442 x) : term569 x _68983 _68984.
Proof. exact (@lem5271640 _68983 x h1 _68984). Qed.
Lemma lem5271642 (_68984 : real) (x : type1021) (_68983 : real -> Prop) : (term569 x _68983 _68984) = (term560 _68984 x _68983).
Proof. exact (eq_refl (term569 x _68983 _68984)). Qed.
Lemma lem5271643 (_68984 : real) (_68983 : real -> Prop) (x : type1021) (h1 : term442 x) : term560 _68984 x _68983.
Proof. exact (EQ_MP (@lem5271642 _68984 x _68983) (@lem5271641 _68983 _68984 x h1)). Qed.
Lemma lem5271644 (_68984 : real) (_68983 : real -> Prop) (_68985 : real) (x : type1021) (h1 : term442 x) : term570 _68984 x _68983 _68985.
Proof. exact (@lem5271643 _68984 _68983 x h1 _68985). Qed.
Lemma lem5271645 (_68984 : real) (x : type1021) (_68985 : real) (_68983 : real -> Prop) : (term570 _68984 x _68983 _68985) = (term558 _68984 x _68985 _68983).
Proof. exact (eq_refl (term570 _68984 x _68983 _68985)). Qed.
Lemma lem5271646 (_68984 : real) (_68985 : real) (_68983 : real -> Prop) (x : type1021) (h1 : term442 x) : term558 _68984 x _68985 _68983.
Proof. exact (EQ_MP (@lem5271645 _68984 x _68985 _68983) (@lem5271644 _68984 _68983 _68985 x h1)). Qed.
Lemma lem5271647 (_68986 : real) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term571 s b _68986.
Proof. exact (@lem5271351 b x' s y h1 _68986). Qed.
Lemma lem5271648 (s : real -> Prop) (b : real) (_68986 : real) : (term571 s b _68986) = (term55 s b _68986).
Proof. exact (eq_refl (term571 s b _68986)). Qed.
Lemma lem5271659 (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term568 x _68990.
Proof. exact (@lem5271594 x h1 _68990). Qed.
Lemma lem5271660 (x : type1021) (_68990 : real -> Prop) : (term568 x _68990) = (term562 x _68990).
Proof. exact (eq_refl (term568 x _68990)). Qed.
Lemma lem5271661 (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term562 x _68990.
Proof. exact (EQ_MP (@lem5271660 x _68990) (@lem5271659 _68990 x h1)). Qed.
Lemma lem5271662 (_68990 : real -> Prop) (_68991 : real) (x : type1021) (h1 : term442 x) : term569 x _68990 _68991.
Proof. exact (@lem5271661 _68990 x h1 _68991). Qed.
Lemma lem5271663 (_68991 : real) (x : type1021) (_68990 : real -> Prop) : (term569 x _68990 _68991) = (term560 _68991 x _68990).
Proof. exact (eq_refl (term569 x _68990 _68991)). Qed.
Lemma lem5271664 (_68991 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term560 _68991 x _68990.
Proof. exact (EQ_MP (@lem5271663 _68991 x _68990) (@lem5271662 _68990 _68991 x h1)). Qed.
Lemma lem5271665 (_68991 : real) (_68990 : real -> Prop) (_68992 : real) (x : type1021) (h1 : term442 x) : term570 _68991 x _68990 _68992.
Proof. exact (@lem5271664 _68991 _68990 x h1 _68992). Qed.
Lemma lem5271666 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term570 _68991 x _68990 _68992) = (term558 _68991 x _68992 _68990).
Proof. exact (eq_refl (term570 _68991 x _68990 _68992)). Qed.
Lemma lem5271667 (_68991 : real) (_68992 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term558 _68991 x _68992 _68990.
Proof. exact (EQ_MP (@lem5271666 _68991 x _68992 _68990) (@lem5271665 _68991 _68990 _68992 x h1)). Qed.
Lemma lem5271671 (_68994 : real) (s : real -> Prop) (y : real) (h1 : term74 s y) : term571 s y _68994.
Proof. exact (@lem5271628 s y h1 _68994). Qed.
Lemma lem5271672 (s : real -> Prop) (y : real) (_68994 : real) : (term571 s y _68994) = (term55 s y _68994).
Proof. exact (eq_refl (term571 s y _68994)). Qed.
Lemma lem5271675 (_68984 : real) (_68983 : real -> Prop) (_68985 : real) (x : type1021) (h1 : term442 x) : term555 x _68984 _68983 _68985.
Proof. exact (proj1 (@lem5271646 _68984 _68985 _68983 x h1)). Qed.
Lemma lem5271682 (_68984 : real) (_68983 : real -> Prop) (_68985 : real) (x : type1021) (h1 : term442 x) : term572 x _68984 _68983 _68985.
Proof. exact (proj2 (@lem5271675 _68984 _68983 _68985 x h1)). Qed.
Lemma lem5271683 (_68984 : real) (_68983 : real -> Prop) (_68985 : real) (x : type1021) (h1 : term442 x) : term573 x _68984 _68983 _68985.
Proof. exact (proj1 (@lem5271675 _68984 _68983 _68985 x h1)). Qed.
Lemma lem5271684 (_68991 : real) (_68992 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term553 _68991 x _68992 _68990.
Proof. exact (proj2 (@lem5271667 _68991 _68992 _68990 x h1)). Qed.
Lemma lem5271686 (_68991 : real) (_68992 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term546 _68991 x _68992 _68990.
Proof. exact (proj2 (@lem5271684 _68991 _68992 _68990 x h1)). Qed.
Lemma lem5271687 (_68991 : real) (_68992 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term550 _68991 x _68992 _68990.
Proof. exact (proj1 (@lem5271684 _68991 _68992 _68990 x h1)). Qed.
Lemma lem5271688 (_68991 : real) (_68992 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term574 _68991 x _68992 _68990.
Proof. exact (proj2 (@lem5271686 _68991 _68992 _68990 x h1)). Qed.
Lemma lem5271690 (_68991 : real) (_68992 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term575 _68991 x _68992 _68990.
Proof. exact (proj2 (@lem5271687 _68991 _68992 _68990 x h1)). Qed.
Lemma lem5271691 (_68991 : real) (_68992 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term576 _68991 x _68992 _68990.
Proof. exact (proj1 (@lem5271687 _68991 _68992 _68990 x h1)). Qed.
Lemma lem5271704 (_68981 : real) (_68980 : real) (_68982 : real) : (term267 _68981 _68980 _68982) = (term577 _68981 _68980 _68982).
Proof. exact (@lem5269276 (term578 _68980 _68981) (term578 _68981 _68982) (real_le _68980 _68982)). Qed.
Lemma lem5271705 (_68981 : real) (_68980 : real) (_68982 : real) (h1 : term49) : term577 _68981 _68980 _68982.
Proof. exact (EQ_MP (@lem5271704 _68981 _68980 _68982) (@lem5271637 _68981 _68980 _68982 h1)). Qed.
Lemma lem5271713 (_68986 : real) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term55 s b _68986.
Proof. exact (EQ_MP (@lem5271648 s b _68986) (@lem5271647 _68986 b x' s y h1)). Qed.
Lemma lem5271719 (s : real -> Prop) (y : real) (x' : real) (h1 : term168 s y x') : term578 y x'.
Proof. exact (proj2 (@lem5271098 s y x' h1)). Qed.
Lemma lem5271798 (x : type1021) (_68984 : real) (_68983 : real -> Prop) (_68985 : real) : (term573 x _68984 _68983 _68985) = (term579 x _68984 _68983 _68985).
Proof. exact (@lem5269276 (_68983 = (@EMPTY real)) (term534 x _68984 _68983) (term290 _68983 _68985)). Qed.
Lemma lem5271799 (_68984 : real) (_68983 : real -> Prop) (_68985 : real) (x : type1021) (h1 : term442 x) : term579 x _68984 _68983 _68985.
Proof. exact (EQ_MP (@lem5271798 x _68984 _68983 _68985) (@lem5271683 _68984 _68983 _68985 x h1)). Qed.
Lemma lem5271814 (x : type1021) (_68984 : real) (_68983 : real -> Prop) (_68985 : real) : (term572 x _68984 _68983 _68985) = (term580 x _68984 _68983 _68985).
Proof. exact (@lem5269276 (_68983 = (@EMPTY real)) (term535 x _68983 _68984) (term290 _68983 _68985)). Qed.
Lemma lem5271815 (_68984 : real) (_68983 : real -> Prop) (_68985 : real) (x : type1021) (h1 : term442 x) : term580 x _68984 _68983 _68985.
Proof. exact (EQ_MP (@lem5271814 x _68984 _68983 _68985) (@lem5271682 _68984 _68983 _68985 x h1)). Qed.
Lemma lem5271837 (s : real -> Prop) (y : real) (h1 : term74 s y) : term581 y s.
Proof. exact (proj1 (@lem5271097 s y h1)). Qed.
Lemma lem5271843 (_68994 : real) (s : real -> Prop) (y : real) (h1 : term74 s y) : term55 s y _68994.
Proof. exact (EQ_MP (@lem5271672 s y _68994) (@lem5271671 _68994 s y h1)). Qed.
Lemma lem5271874 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term574 _68991 x _68992 _68990) = (term582 _68991 x _68992 _68990).
Proof. exact (@lem5269276 (_68990 = (@EMPTY real)) (term535 x _68990 _68991) (term544 x _68992 _68990)). Qed.
Lemma lem5271875 (_68991 : real) (_68992 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term582 _68991 x _68992 _68990.
Proof. exact (EQ_MP (@lem5271874 _68991 x _68992 _68990) (@lem5271688 _68991 _68992 _68990 x h1)). Qed.
Lemma lem5271890 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term576 _68991 x _68992 _68990) = (term583 _68991 x _68992 _68990).
Proof. exact (@lem5269276 (_68990 = (@EMPTY real)) (term534 x _68991 _68990) (term543 x _68992 _68990)). Qed.
Lemma lem5271891 (_68991 : real) (_68992 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term583 _68991 x _68992 _68990.
Proof. exact (EQ_MP (@lem5271890 _68991 x _68992 _68990) (@lem5271691 _68991 _68992 _68990 x h1)). Qed.
Lemma lem5271906 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term575 _68991 x _68992 _68990) = (term584 _68991 x _68992 _68990).
Proof. exact (@lem5269276 (_68990 = (@EMPTY real)) (term535 x _68990 _68991) (term543 x _68992 _68990)). Qed.
Lemma lem5271907 (_68991 : real) (_68992 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term584 _68991 x _68992 _68990.
Proof. exact (EQ_MP (@lem5271906 _68991 x _68992 _68990) (@lem5271690 _68991 _68992 _68990 x h1)). Qed.
Lemma lem5272006 (s : real -> Prop) (y : real) (x' : real) (h1 : term168 s y x') : term23 y s.
Proof. exact (proj1 (@lem5271096 s y x' h1)). Qed.
Lemma lem5272007 (s : real -> Prop) (y : real) (x' : real) (h1 : term168 s y x') : term585 y s.
Proof. exact (fun h0 : term581 y s => @lem5272006 s y x' h1). Qed.
Lemma lem5272009 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5272010 (y : real) (s : real -> Prop) : (term585 y s) = (term23 y s).
Proof. exact (@lem5272009 (term23 y s)). Qed.
Lemma lem5272011 (s : real -> Prop) (y : real) (x' : real) (h1 : term168 s y x') : term23 y s.
Proof. exact (EQ_MP (@lem5272010 y s) (@lem5272007 s y x' h1)). Qed.
Lemma lem5272013 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (proj1 (@lem5271093 b x' s y h1)). Qed.
Lemma lem5272014 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5272013 b x' s y h1). Qed.
Lemma lem5272016 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5272017 (s : real -> Prop) : (term587 s) = (term148 s).
Proof. exact (@lem5272016 (s = (@EMPTY real))). Qed.
Lemma lem5272018 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (EQ_MP (@lem5272017 s) (@lem5272014 b x' s y h1)). Qed.
Lemma lem5272020 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (proj1 (@lem5271093 b x' s y h1)). Qed.
Lemma lem5272021 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5272020 b x' s y h1). Qed.
Lemma lem5272023 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5272024 (s : real -> Prop) : (term587 s) = (term148 s).
Proof. exact (@lem5272023 (s = (@EMPTY real))). Qed.
Lemma lem5272025 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (EQ_MP (@lem5272024 s) (@lem5272021 b x' s y h1)). Qed.
Lemma lem5272027 (s : real -> Prop) (y : real) (x' : real) (h1 : term168 s y x') : @IN real x' s.
Proof. exact (proj1 (@lem5271098 s y x' h1)). Qed.
Lemma lem5272028 (s : real -> Prop) (y : real) (x' : real) (h1 : term168 s y x') : term589 x' s.
Proof. exact (fun h0 : term590 x' s => @lem5272027 s y x' h1). Qed.
Lemma lem5272030 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5272031 (x' : real) (s : real -> Prop) : (term589 x' s) = (@IN real x' s).
Proof. exact (@lem5272030 (@IN real x' s)). Qed.
Lemma lem5272032 (s : real -> Prop) (y : real) (x' : real) (h1 : term168 s y x') : @IN real x' s.
Proof. exact (EQ_MP (@lem5272031 x' s) (@lem5272028 s y x' h1)). Qed.
Lemma lem5272035 (s : real -> Prop) (x' : real) (h1 : term591 s x') : term591 s x'.
Proof. exact (h1). Qed.
Lemma lem5272036 (s : real -> Prop) (x' : real) (h1 : term591 s x') : term592 s x'.
Proof. exact (fun h0 : term291 s x' => @lem5272035 s x' h1). Qed.
Lemma lem5272038 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5272039 (s : real -> Prop) (x' : real) : (term592 s x') = (term591 s x').
Proof. exact (@lem5272038 (term291 s x')). Qed.
Lemma lem5272040 (s : real -> Prop) (x' : real) (h1 : term591 s x') : term591 s x'.
Proof. exact (EQ_MP (@lem5272039 s x') (@lem5272036 s x' h1)). Qed.
Lemma lem5272068 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5272069 (_68985 : real) (_68983 : real -> Prop) : (term290 _68983 _68985) = (term593 _68985 _68983).
Proof. exact (@lem5272068 (term291 _68983 _68985) (term590 _68985 _68983)). Qed.
Lemma lem5272075 (x : type1021) (_68984 : real) (_68983 : real -> Prop) : (term594 x _68984 _68983) = (term594 x _68984 _68983).
Proof. exact (eq_refl (term594 x _68984 _68983)). Qed.
Lemma lem5272076 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : (term595 x _68984 _68983 _68985) = (term596 x _68984 _68985 _68983).
Proof. exact (MK_COMB (@lem5272075 x _68984 _68983) (@lem5272069 _68985 _68983)). Qed.
Lemma lem5272087 (_68983 : real -> Prop) : (term286 _68983) = (term286 _68983).
Proof. exact (eq_refl (term286 _68983)). Qed.
Lemma lem5272088 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : (term579 x _68984 _68983 _68985) = (term597 x _68984 _68985 _68983).
Proof. exact (MK_COMB (@lem5272087 _68983) (@lem5272076 x _68984 _68985 _68983)). Qed.
Lemma lem5272099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5272100 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : (term598 x _68984 _68983 _68985) = (term599 x _68984 _68985 _68983).
Proof. exact (MK_COMB (@lem5272099) (@lem5272088 x _68984 _68985 _68983)). Qed.
Lemma lem5272104 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5272105 (x : type1021) (_68984 : real) (_68983 : real -> Prop) (_68985 : real) : (term600 x _68984 _68983 _68985) = (term579 x _68984 _68983 _68985).
Proof. exact (@lem5272104 (_68983 = (@EMPTY real)) (term534 x _68984 _68983) (term290 _68983 _68985)). Qed.
Lemma lem5272131 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5272132 (_68985 : real) (_68983 : real -> Prop) : (term290 _68983 _68985) = (term593 _68985 _68983).
Proof. exact (@lem5272131 (term291 _68983 _68985) (term590 _68985 _68983)). Qed.
Lemma lem5272138 (x : type1021) (_68984 : real) (_68983 : real -> Prop) : (term594 x _68984 _68983) = (term594 x _68984 _68983).
Proof. exact (eq_refl (term594 x _68984 _68983)). Qed.
Lemma lem5272139 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : (term595 x _68984 _68983 _68985) = (term596 x _68984 _68985 _68983).
Proof. exact (MK_COMB (@lem5272138 x _68984 _68983) (@lem5272132 _68985 _68983)). Qed.
Lemma lem5272150 (_68983 : real -> Prop) : (term286 _68983) = (term286 _68983).
Proof. exact (eq_refl (term286 _68983)). Qed.
Lemma lem5272151 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : (term579 x _68984 _68983 _68985) = (term597 x _68984 _68985 _68983).
Proof. exact (MK_COMB (@lem5272150 _68983) (@lem5272139 x _68984 _68985 _68983)). Qed.
Lemma lem5272162 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : (term600 x _68984 _68983 _68985) = (term597 x _68984 _68985 _68983).
Proof. exact (TRANS (@lem5272105 x _68984 _68983 _68985) (@lem5272151 x _68984 _68985 _68983)). Qed.
Lemma lem5272163 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : ((term579 x _68984 _68983 _68985) = (term600 x _68984 _68983 _68985)) = ((term597 x _68984 _68985 _68983) = (term597 x _68984 _68985 _68983)).
Proof. exact (MK_COMB (@lem5272100 x _68984 _68985 _68983) (@lem5272162 x _68984 _68985 _68983)). Qed.
Lemma lem5272165 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5272166 (x : Prop) : (x = x) = True.
Proof. exact (@lem5272165 Prop x). Qed.
Lemma lem5272167 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : ((term597 x _68984 _68985 _68983) = (term597 x _68984 _68985 _68983)) = True.
Proof. exact (@lem5272166 (term597 x _68984 _68985 _68983)). Qed.
Lemma lem5272168 (x : type1021) (_68984 : real) (_68983 : real -> Prop) (_68985 : real) : ((term579 x _68984 _68983 _68985) = (term600 x _68984 _68983 _68985)) = True.
Proof. exact (TRANS (@lem5272163 x _68984 _68985 _68983) (@lem5272167 x _68984 _68985 _68983)). Qed.
Lemma lem5272169 (x : type1021) (_68984 : real) (_68983 : real -> Prop) (_68985 : real) : True = ((term579 x _68984 _68983 _68985) = (term600 x _68984 _68983 _68985)).
Proof. exact (SYM (@lem5272168 x _68984 _68983 _68985)). Qed.
Lemma lem5272170 (x : type1021) (_68984 : real) (_68983 : real -> Prop) (_68985 : real) : (term579 x _68984 _68983 _68985) = (term600 x _68984 _68983 _68985).
Proof. exact (EQ_MP (@lem5272169 x _68984 _68983 _68985) (@lem0)). Qed.
Lemma lem5272171 (_68984 : real) (_68983 : real -> Prop) (_68985 : real) (x : type1021) (h1 : term442 x) : term600 x _68984 _68983 _68985.
Proof. exact (EQ_MP (@lem5272170 x _68984 _68983 _68985) (@lem5271799 _68984 _68983 _68985 x h1)). Qed.
Lemma lem5272173 (b : Prop) (a : Prop) : (a \/ b) = (term601 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5272174 (_68985 : real) (x : type1021) (_68984 : real) (_68983 : real -> Prop) : (term600 x _68984 _68983 _68985) = (term602 _68985 x _68984 _68983).
Proof. exact (@lem5272173 (term603 _68983 _68985) (term534 x _68984 _68983)). Qed.
Lemma lem5272176 (a : Prop) (b : Prop) : (term604 a b) = (term605 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5272177 (_68983 : real -> Prop) (_68985 : real) : (term606 _68983 _68985) = (term607 _68983 _68985).
Proof. exact (@lem5272176 (_68983 = (@EMPTY real)) (term290 _68983 _68985)). Qed.
Lemma lem5272179 (a : Prop) (b : Prop) : (term604 a b) = (term605 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5272180 (_68983 : real -> Prop) (_68985 : real) : (term608 _68983 _68985) = (term609 _68983 _68985).
Proof. exact (@lem5272179 (term590 _68985 _68983) (term291 _68983 _68985)). Qed.
Lemma lem5272182 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5272183 (_68985 : real) (_68983 : real -> Prop) : (term611 _68985 _68983) = (@IN real _68985 _68983).
Proof. exact (@lem5272182 (@IN real _68985 _68983)). Qed.
Lemma lem5272184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5272185 (_68985 : real) (_68983 : real -> Prop) : (term612 _68985 _68983) = (term613 _68985 _68983).
Proof. exact (MK_COMB (@lem5272184) (@lem5272183 _68985 _68983)). Qed.
Lemma lem5272186 (_68983 : real -> Prop) (_68985 : real) : (term591 _68983 _68985) = (term591 _68983 _68985).
Proof. exact (eq_refl (term591 _68983 _68985)). Qed.
Lemma lem5272187 (_68983 : real -> Prop) (_68985 : real) : (term609 _68983 _68985) = (term614 _68983 _68985).
Proof. exact (MK_COMB (@lem5272185 _68985 _68983) (@lem5272186 _68983 _68985)). Qed.
Lemma lem5272188 (_68983 : real -> Prop) (_68985 : real) : (term608 _68983 _68985) = (term614 _68983 _68985).
Proof. exact (TRANS (@lem5272180 _68983 _68985) (@lem5272187 _68983 _68985)). Qed.
Lemma lem5272189 (_68983 : real -> Prop) : (term38 _68983) = (term38 _68983).
Proof. exact (eq_refl (term38 _68983)). Qed.
Lemma lem5272190 (_68983 : real -> Prop) (_68985 : real) : (term607 _68983 _68985) = (term615 _68983 _68985).
Proof. exact (MK_COMB (@lem5272189 _68983) (@lem5272188 _68983 _68985)). Qed.
Lemma lem5272191 (_68983 : real -> Prop) (_68985 : real) : (term606 _68983 _68985) = (term615 _68983 _68985).
Proof. exact (TRANS (@lem5272177 _68983 _68985) (@lem5272190 _68983 _68985)). Qed.
Lemma lem5272192 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5272193 (_68983 : real -> Prop) (_68985 : real) : (term616 _68983 _68985) = (term617 _68983 _68985).
Proof. exact (MK_COMB (@lem5272192) (@lem5272191 _68983 _68985)). Qed.
Lemma lem5272194 (x : type1021) (_68984 : real) (_68983 : real -> Prop) : (term534 x _68984 _68983) = (term534 x _68984 _68983).
Proof. exact (eq_refl (term534 x _68984 _68983)). Qed.
Lemma lem5272195 (_68985 : real) (x : type1021) (_68984 : real) (_68983 : real -> Prop) : (term602 _68985 x _68984 _68983) = (term618 _68985 x _68984 _68983).
Proof. exact (MK_COMB (@lem5272193 _68983 _68985) (@lem5272194 x _68984 _68983)). Qed.
Lemma lem5272196 (_68985 : real) (x : type1021) (_68984 : real) (_68983 : real -> Prop) : (term600 x _68984 _68983 _68985) = (term618 _68985 x _68984 _68983).
Proof. exact (TRANS (@lem5272174 _68985 x _68984 _68983) (@lem5272195 _68985 x _68984 _68983)). Qed.
Lemma lem5272198 (s : real -> Prop) (y : real) (x' : real) (h1 : term591 s x') (h2 : term168 s y x') : term614 s x'.
Proof. exact (conj (@lem5272032 s y x' h2) (@lem5272040 s x' h1)). Qed.
Lemma lem5272199 (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term591 s x') (h2 : term252 b x' s y) (h3 : term168 s y x') : term615 s x'.
Proof. exact (conj (@lem5272025 b x' s y h2) (@lem5272198 s y x' h1 h3)). Qed.
Lemma lem5272201 (_68985 : real) (_68984 : real) (_68983 : real -> Prop) (x : type1021) (h1 : term442 x) : term618 _68985 x _68984 _68983.
Proof. exact (EQ_MP (@lem5272196 _68985 x _68984 _68983) (@lem5272171 _68984 _68983 _68985 x h1)). Qed.
Lemma lem5272202 (x' : real) (_68984 : real) (s : real -> Prop) (x : type1021) (h1 : term442 x) : term618 x' x _68984 s.
Proof. exact (@lem5272201 x' _68984 s x h1). Qed.
Lemma lem5272205 (_68984 : real) (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term591 s x') (h3 : term252 b x' s y) (h4 : term168 s y x') : term534 x _68984 s.
Proof. exact (@lem5272202 x' _68984 s x h1 (@lem5272199 b s y x' h2 h3 h4)). Qed.
Lemma lem5272206 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term591 s x') (h3 : term252 b x' s y) (h4 : term168 s y x') : term534 x b s.
Proof. exact (@lem5272205 b x b s y x' h1 h2 h3 h4). Qed.
Lemma lem5272207 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term591 s x') (h3 : term252 b x' s y) (h4 : term168 s y x') : term619 x b s.
Proof. exact (fun h0 : term620 x b s => @lem5272206 x b s y x' h1 h2 h3 h4). Qed.
Lemma lem5272209 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5272210 (x : type1021) (b : real) (s : real -> Prop) : (term619 x b s) = (term534 x b s).
Proof. exact (@lem5272209 (term534 x b s)). Qed.
Lemma lem5272211 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term591 s x') (h3 : term252 b x' s y) (h4 : term168 s y x') : term534 x b s.
Proof. exact (EQ_MP (@lem5272210 x b s) (@lem5272207 x b s y x' h1 h2 h3 h4)). Qed.
Lemma lem5272217 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5272218 (b : real) (_68986 : real) (s : real -> Prop) : (term55 s b _68986) = (term621 b _68986 s).
Proof. exact (@lem5272217 (real_le b _68986) (term590 _68986 s)). Qed.
Lemma lem5272224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5272225 (b : real) (_68986 : real) (s : real -> Prop) : (term622 s b _68986) = (term623 b _68986 s).
Proof. exact (MK_COMB (@lem5272224) (@lem5272218 b _68986 s)). Qed.
Lemma lem5272231 (b : real) (_68986 : real) (s : real -> Prop) : (term621 b _68986 s) = (term621 b _68986 s).
Proof. exact (eq_refl (term621 b _68986 s)). Qed.
Lemma lem5272232 (b : real) (_68986 : real) (s : real -> Prop) : ((term55 s b _68986) = (term621 b _68986 s)) = ((term621 b _68986 s) = (term621 b _68986 s)).
Proof. exact (MK_COMB (@lem5272225 b _68986 s) (@lem5272231 b _68986 s)). Qed.
Lemma lem5272234 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5272235 (x : Prop) : (x = x) = True.
Proof. exact (@lem5272234 Prop x). Qed.
Lemma lem5272236 (b : real) (_68986 : real) (s : real -> Prop) : ((term621 b _68986 s) = (term621 b _68986 s)) = True.
Proof. exact (@lem5272235 (term621 b _68986 s)). Qed.
Lemma lem5272237 (b : real) (_68986 : real) (s : real -> Prop) : ((term55 s b _68986) = (term621 b _68986 s)) = True.
Proof. exact (TRANS (@lem5272232 b _68986 s) (@lem5272236 b _68986 s)). Qed.
Lemma lem5272238 (b : real) (_68986 : real) (s : real -> Prop) : True = ((term55 s b _68986) = (term621 b _68986 s)).
Proof. exact (SYM (@lem5272237 b _68986 s)). Qed.
Lemma lem5272239 (b : real) (_68986 : real) (s : real -> Prop) : (term55 s b _68986) = (term621 b _68986 s).
Proof. exact (EQ_MP (@lem5272238 b _68986 s) (@lem0)). Qed.
Lemma lem5272240 (_68986 : real) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term621 b _68986 s.
Proof. exact (EQ_MP (@lem5272239 b _68986 s) (@lem5271713 _68986 b x' s y h1)). Qed.
Lemma lem5272242 (b : Prop) (a : Prop) : (a \/ b) = (term601 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5272243 (s : real -> Prop) (b : real) (_68986 : real) : (term621 b _68986 s) = (term624 s b _68986).
Proof. exact (@lem5272242 (term590 _68986 s) (real_le b _68986)). Qed.
Lemma lem5272245 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5272246 (_68986 : real) (s : real -> Prop) : (term611 _68986 s) = (@IN real _68986 s).
Proof. exact (@lem5272245 (@IN real _68986 s)). Qed.
Lemma lem5272247 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5272248 (_68986 : real) (s : real -> Prop) : (term625 _68986 s) = (term626 _68986 s).
Proof. exact (MK_COMB (@lem5272247) (@lem5272246 _68986 s)). Qed.
Lemma lem5272249 (b : real) (_68986 : real) : (real_le b _68986) = (real_le b _68986).
Proof. exact (eq_refl (real_le b _68986)). Qed.
Lemma lem5272250 (s : real -> Prop) (b : real) (_68986 : real) : (term624 s b _68986) = (term24 s b _68986).
Proof. exact (MK_COMB (@lem5272248 _68986 s) (@lem5272249 b _68986)). Qed.
Lemma lem5272251 (s : real -> Prop) (b : real) (_68986 : real) : (term621 b _68986 s) = (term24 s b _68986).
Proof. exact (TRANS (@lem5272243 s b _68986) (@lem5272250 s b _68986)). Qed.
Lemma lem5272254 (_68986 : real) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term24 s b _68986.
Proof. exact (EQ_MP (@lem5272251 s b _68986) (@lem5272240 _68986 b x' s y h1)). Qed.
Lemma lem5272255 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term627 x s b.
Proof. exact (@lem5272254 (x s b) b x' s y h1). Qed.
Lemma lem5272258 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term591 s x') (h3 : term252 b x' s y) (h4 : term168 s y x') : term628 x s b.
Proof. exact (@lem5272255 x b x' s y h3 (@lem5272211 x b s y x' h1 h2 h3 h4)). Qed.
Lemma lem5272259 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term591 s x') (h3 : term252 b x' s y) (h4 : term168 s y x') : term629 x s b.
Proof. exact (fun h0 : term535 x s b => @lem5272258 x b s y x' h1 h2 h3 h4). Qed.
Lemma lem5272261 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5272262 (x : type1021) (s : real -> Prop) (b : real) : (term629 x s b) = (term628 x s b).
Proof. exact (@lem5272261 (term628 x s b)). Qed.
Lemma lem5272263 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term591 s x') (h3 : term252 b x' s y) (h4 : term168 s y x') : term628 x s b.
Proof. exact (EQ_MP (@lem5272262 x s b) (@lem5272259 x b s y x' h1 h2 h3 h4)). Qed.
Lemma lem5272265 (s : real -> Prop) (y : real) (x' : real) (h1 : term168 s y x') : @IN real x' s.
Proof. exact (proj1 (@lem5271098 s y x' h1)). Qed.
Lemma lem5272266 (s : real -> Prop) (y : real) (x' : real) (h1 : term168 s y x') : term589 x' s.
Proof. exact (fun h0 : term590 x' s => @lem5272265 s y x' h1). Qed.
Lemma lem5272268 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5272269 (x' : real) (s : real -> Prop) : (term589 x' s) = (@IN real x' s).
Proof. exact (@lem5272268 (@IN real x' s)). Qed.
Lemma lem5272270 (s : real -> Prop) (y : real) (x' : real) (h1 : term168 s y x') : @IN real x' s.
Proof. exact (EQ_MP (@lem5272269 x' s) (@lem5272266 s y x' h1)). Qed.
Lemma lem5272288 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5272289 (x : type1021) (_68984 : real) (_68983 : real -> Prop) (_68985 : real) : (term630 x _68984 _68983 _68985) = (term631 x _68984 _68983 _68985).
Proof. exact (@lem5272288 (term590 _68985 _68983) (term535 x _68983 _68984) (term291 _68983 _68985)). Qed.
Lemma lem5272303 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5272304 (_68985 : real) (x : type1021) (_68983 : real -> Prop) (_68984 : real) : (term632 x _68984 _68983 _68985) = (term633 _68985 x _68983 _68984).
Proof. exact (@lem5272303 (term291 _68983 _68985) (term535 x _68983 _68984)). Qed.
Lemma lem5272310 (_68985 : real) (_68983 : real -> Prop) : (term634 _68985 _68983) = (term634 _68985 _68983).
Proof. exact (eq_refl (term634 _68985 _68983)). Qed.
Lemma lem5272311 (_68985 : real) (x : type1021) (_68983 : real -> Prop) (_68984 : real) : (term631 x _68984 _68983 _68985) = (term635 _68985 x _68983 _68984).
Proof. exact (MK_COMB (@lem5272310 _68985 _68983) (@lem5272304 _68985 x _68983 _68984)). Qed.
Lemma lem5272315 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5272316 (_68985 : real) (x : type1021) (_68983 : real -> Prop) (_68984 : real) : (term635 _68985 x _68983 _68984) = (term636 _68985 x _68983 _68984).
Proof. exact (@lem5272315 (term291 _68983 _68985) (term590 _68985 _68983) (term535 x _68983 _68984)). Qed.
Lemma lem5272332 (_68985 : real) (x : type1021) (_68983 : real -> Prop) (_68984 : real) : (term631 x _68984 _68983 _68985) = (term636 _68985 x _68983 _68984).
Proof. exact (TRANS (@lem5272311 _68985 x _68983 _68984) (@lem5272316 _68985 x _68983 _68984)). Qed.
Lemma lem5272333 (_68985 : real) (x : type1021) (_68983 : real -> Prop) (_68984 : real) : (term630 x _68984 _68983 _68985) = (term636 _68985 x _68983 _68984).
Proof. exact (TRANS (@lem5272289 x _68984 _68983 _68985) (@lem5272332 _68985 x _68983 _68984)). Qed.
Lemma lem5272334 (_68983 : real -> Prop) : (term286 _68983) = (term286 _68983).
Proof. exact (eq_refl (term286 _68983)). Qed.
Lemma lem5272335 (_68985 : real) (x : type1021) (_68983 : real -> Prop) (_68984 : real) : (term580 x _68984 _68983 _68985) = (term637 _68985 x _68983 _68984).
Proof. exact (MK_COMB (@lem5272334 _68983) (@lem5272333 _68985 x _68983 _68984)). Qed.
Lemma lem5272346 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5272347 (_68985 : real) (x : type1021) (_68983 : real -> Prop) (_68984 : real) : (term638 x _68984 _68983 _68985) = (term639 _68985 x _68983 _68984).
Proof. exact (MK_COMB (@lem5272346) (@lem5272335 _68985 x _68983 _68984)). Qed.
Lemma lem5272351 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5272352 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : (term640 x _68984 _68985 _68983) = (term641 x _68984 _68985 _68983).
Proof. exact (@lem5272351 (_68983 = (@EMPTY real)) (term291 _68983 _68985) (term642 x _68984 _68985 _68983)). Qed.
Lemma lem5272378 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5272379 (_68985 : real) (x : type1021) (_68983 : real -> Prop) (_68984 : real) : (term642 x _68984 _68985 _68983) = (term643 _68985 x _68983 _68984).
Proof. exact (@lem5272378 (term590 _68985 _68983) (term535 x _68983 _68984)). Qed.
Lemma lem5272385 (_68983 : real -> Prop) (_68985 : real) : (term644 _68983 _68985) = (term644 _68983 _68985).
Proof. exact (eq_refl (term644 _68983 _68985)). Qed.
Lemma lem5272386 (_68985 : real) (x : type1021) (_68983 : real -> Prop) (_68984 : real) : (term645 x _68984 _68985 _68983) = (term636 _68985 x _68983 _68984).
Proof. exact (MK_COMB (@lem5272385 _68983 _68985) (@lem5272379 _68985 x _68983 _68984)). Qed.
Lemma lem5272397 (_68983 : real -> Prop) : (term286 _68983) = (term286 _68983).
Proof. exact (eq_refl (term286 _68983)). Qed.
Lemma lem5272398 (_68985 : real) (x : type1021) (_68983 : real -> Prop) (_68984 : real) : (term641 x _68984 _68985 _68983) = (term637 _68985 x _68983 _68984).
Proof. exact (MK_COMB (@lem5272397 _68983) (@lem5272386 _68985 x _68983 _68984)). Qed.
Lemma lem5272409 (_68985 : real) (x : type1021) (_68983 : real -> Prop) (_68984 : real) : (term640 x _68984 _68985 _68983) = (term637 _68985 x _68983 _68984).
Proof. exact (TRANS (@lem5272352 x _68984 _68985 _68983) (@lem5272398 _68985 x _68983 _68984)). Qed.
Lemma lem5272410 (_68985 : real) (x : type1021) (_68983 : real -> Prop) (_68984 : real) : ((term580 x _68984 _68983 _68985) = (term640 x _68984 _68985 _68983)) = ((term637 _68985 x _68983 _68984) = (term637 _68985 x _68983 _68984)).
Proof. exact (MK_COMB (@lem5272347 _68985 x _68983 _68984) (@lem5272409 _68985 x _68983 _68984)). Qed.
Lemma lem5272412 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5272413 (x : Prop) : (x = x) = True.
Proof. exact (@lem5272412 Prop x). Qed.
Lemma lem5272414 (_68985 : real) (x : type1021) (_68983 : real -> Prop) (_68984 : real) : ((term637 _68985 x _68983 _68984) = (term637 _68985 x _68983 _68984)) = True.
Proof. exact (@lem5272413 (term637 _68985 x _68983 _68984)). Qed.
Lemma lem5272415 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : ((term580 x _68984 _68983 _68985) = (term640 x _68984 _68985 _68983)) = True.
Proof. exact (TRANS (@lem5272410 _68985 x _68983 _68984) (@lem5272414 _68985 x _68983 _68984)). Qed.
Lemma lem5272416 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : True = ((term580 x _68984 _68983 _68985) = (term640 x _68984 _68985 _68983)).
Proof. exact (SYM (@lem5272415 x _68984 _68985 _68983)). Qed.
Lemma lem5272417 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : (term580 x _68984 _68983 _68985) = (term640 x _68984 _68985 _68983).
Proof. exact (EQ_MP (@lem5272416 x _68984 _68985 _68983) (@lem0)). Qed.
Lemma lem5272418 (_68984 : real) (_68985 : real) (_68983 : real -> Prop) (x : type1021) (h1 : term442 x) : term640 x _68984 _68985 _68983.
Proof. exact (EQ_MP (@lem5272417 x _68984 _68985 _68983) (@lem5271815 _68984 _68983 _68985 x h1)). Qed.
Lemma lem5272420 (b : Prop) (a : Prop) : (a \/ b) = (term601 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5272421 (x : type1021) (_68984 : real) (_68983 : real -> Prop) (_68985 : real) : (term640 x _68984 _68985 _68983) = (term646 x _68984 _68983 _68985).
Proof. exact (@lem5272420 (term647 x _68984 _68985 _68983) (term291 _68983 _68985)). Qed.
Lemma lem5272423 (a : Prop) (b : Prop) : (term604 a b) = (term605 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5272424 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : (term648 x _68984 _68985 _68983) = (term649 x _68984 _68985 _68983).
Proof. exact (@lem5272423 (_68983 = (@EMPTY real)) (term642 x _68984 _68985 _68983)). Qed.
Lemma lem5272426 (a : Prop) (b : Prop) : (term604 a b) = (term605 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5272427 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : (term650 x _68984 _68985 _68983) = (term651 x _68984 _68985 _68983).
Proof. exact (@lem5272426 (term535 x _68983 _68984) (term590 _68985 _68983)). Qed.
Lemma lem5272429 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5272430 (x : type1021) (_68983 : real -> Prop) (_68984 : real) : (term652 x _68983 _68984) = (term628 x _68983 _68984).
Proof. exact (@lem5272429 (term628 x _68983 _68984)). Qed.
Lemma lem5272431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5272432 (x : type1021) (_68983 : real -> Prop) (_68984 : real) : (term653 x _68983 _68984) = (term654 x _68983 _68984).
Proof. exact (MK_COMB (@lem5272431) (@lem5272430 x _68983 _68984)). Qed.
Lemma lem5272434 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5272435 (_68985 : real) (_68983 : real -> Prop) : (term611 _68985 _68983) = (@IN real _68985 _68983).
Proof. exact (@lem5272434 (@IN real _68985 _68983)). Qed.
Lemma lem5272436 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : (term651 x _68984 _68985 _68983) = (term655 x _68984 _68985 _68983).
Proof. exact (MK_COMB (@lem5272432 x _68983 _68984) (@lem5272435 _68985 _68983)). Qed.
Lemma lem5272437 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : (term650 x _68984 _68985 _68983) = (term655 x _68984 _68985 _68983).
Proof. exact (TRANS (@lem5272427 x _68984 _68985 _68983) (@lem5272436 x _68984 _68985 _68983)). Qed.
Lemma lem5272438 (_68983 : real -> Prop) : (term38 _68983) = (term38 _68983).
Proof. exact (eq_refl (term38 _68983)). Qed.
Lemma lem5272439 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : (term649 x _68984 _68985 _68983) = (term656 x _68984 _68985 _68983).
Proof. exact (MK_COMB (@lem5272438 _68983) (@lem5272437 x _68984 _68985 _68983)). Qed.
Lemma lem5272440 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : (term648 x _68984 _68985 _68983) = (term656 x _68984 _68985 _68983).
Proof. exact (TRANS (@lem5272424 x _68984 _68985 _68983) (@lem5272439 x _68984 _68985 _68983)). Qed.
Lemma lem5272441 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5272442 (x : type1021) (_68984 : real) (_68985 : real) (_68983 : real -> Prop) : (term657 x _68984 _68985 _68983) = (term658 x _68984 _68985 _68983).
Proof. exact (MK_COMB (@lem5272441) (@lem5272440 x _68984 _68985 _68983)). Qed.
Lemma lem5272443 (_68983 : real -> Prop) (_68985 : real) : (term291 _68983 _68985) = (term291 _68983 _68985).
Proof. exact (eq_refl (term291 _68983 _68985)). Qed.
Lemma lem5272444 (x : type1021) (_68984 : real) (_68983 : real -> Prop) (_68985 : real) : (term646 x _68984 _68983 _68985) = (term659 x _68984 _68983 _68985).
Proof. exact (MK_COMB (@lem5272442 x _68984 _68985 _68983) (@lem5272443 _68983 _68985)). Qed.
Lemma lem5272445 (x : type1021) (_68984 : real) (_68983 : real -> Prop) (_68985 : real) : (term640 x _68984 _68985 _68983) = (term659 x _68984 _68983 _68985).
Proof. exact (TRANS (@lem5272421 x _68984 _68983 _68985) (@lem5272444 x _68984 _68983 _68985)). Qed.
Lemma lem5272447 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term591 s x') (h3 : term252 b x' s y) (h4 : term168 s y x') : term655 x b x' s.
Proof. exact (conj (@lem5272263 x b s y x' h1 h2 h3 h4) (@lem5272270 s y x' h4)). Qed.
Lemma lem5272448 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term591 s x') (h3 : term252 b x' s y) (h4 : term168 s y x') : term656 x b x' s.
Proof. exact (conj (@lem5272018 b x' s y h3) (@lem5272447 x b s y x' h1 h2 h3 h4)). Qed.
Lemma lem5272450 (_68984 : real) (_68983 : real -> Prop) (_68985 : real) (x : type1021) (h1 : term442 x) : term659 x _68984 _68983 _68985.
Proof. exact (EQ_MP (@lem5272445 x _68984 _68983 _68985) (@lem5272418 _68984 _68985 _68983 x h1)). Qed.
Lemma lem5272451 (b : real) (s : real -> Prop) (x' : real) (x : type1021) (h1 : term442 x) : term659 x b s x'.
Proof. exact (@lem5272450 b s x' x h1). Qed.
Lemma lem5272454 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term591 s x') (h3 : term252 b x' s y) (h4 : term168 s y x') : term291 s x'.
Proof. exact (@lem5272451 b s x' x h1 (@lem5272448 x b s y x' h1 h2 h3 h4)). Qed.
Lemma lem5272455 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term252 b x' s y) (h3 : term168 s y x') : term660 s x'.
Proof. exact (fun h0 : term591 s x' => @lem5272454 x b s y x' h1 h0 h2 h3). Qed.
Lemma lem5272457 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5272458 (s : real -> Prop) (x' : real) : (term660 s x') = (term291 s x').
Proof. exact (@lem5272457 (term291 s x')). Qed.
Lemma lem5272459 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term252 b x' s y) (h3 : term168 s y x') : term291 s x'.
Proof. exact (EQ_MP (@lem5272458 s x') (@lem5272455 x b s y x' h1 h2 h3)). Qed.
Lemma lem5272475 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5272476 (_68980 : real) (_68981 : real) (_68982 : real) : (term661 _68981 _68980 _68982) = (term662 _68980 _68981 _68982).
Proof. exact (@lem5272475 (real_le _68980 _68982) (term578 _68981 _68982)). Qed.
Lemma lem5272482 (_68980 : real) (_68981 : real) : (term663 _68980 _68981) = (term663 _68980 _68981).
Proof. exact (eq_refl (term663 _68980 _68981)). Qed.
Lemma lem5272483 (_68980 : real) (_68981 : real) (_68982 : real) : (term577 _68981 _68980 _68982) = (term664 _68980 _68981 _68982).
Proof. exact (MK_COMB (@lem5272482 _68980 _68981) (@lem5272476 _68980 _68981 _68982)). Qed.
Lemma lem5272487 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5272488 (_68980 : real) (_68981 : real) (_68982 : real) : (term664 _68980 _68981 _68982) = (term665 _68980 _68981 _68982).
Proof. exact (@lem5272487 (real_le _68980 _68982) (term578 _68980 _68981) (term578 _68981 _68982)). Qed.
Lemma lem5272504 (_68980 : real) (_68981 : real) (_68982 : real) : (term577 _68981 _68980 _68982) = (term665 _68980 _68981 _68982).
Proof. exact (TRANS (@lem5272483 _68980 _68981 _68982) (@lem5272488 _68980 _68981 _68982)). Qed.
Lemma lem5272505 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5272506 (_68980 : real) (_68981 : real) (_68982 : real) : (term666 _68981 _68980 _68982) = (term667 _68980 _68981 _68982).
Proof. exact (MK_COMB (@lem5272505) (@lem5272504 _68980 _68981 _68982)). Qed.
Lemma lem5272522 (_68980 : real) (_68981 : real) (_68982 : real) : (term665 _68980 _68981 _68982) = (term665 _68980 _68981 _68982).
Proof. exact (eq_refl (term665 _68980 _68981 _68982)). Qed.
Lemma lem5272523 (_68980 : real) (_68981 : real) (_68982 : real) : ((term577 _68981 _68980 _68982) = (term665 _68980 _68981 _68982)) = ((term665 _68980 _68981 _68982) = (term665 _68980 _68981 _68982)).
Proof. exact (MK_COMB (@lem5272506 _68980 _68981 _68982) (@lem5272522 _68980 _68981 _68982)). Qed.
Lemma lem5272525 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5272526 (x : Prop) : (x = x) = True.
Proof. exact (@lem5272525 Prop x). Qed.
Lemma lem5272527 (_68980 : real) (_68981 : real) (_68982 : real) : ((term665 _68980 _68981 _68982) = (term665 _68980 _68981 _68982)) = True.
Proof. exact (@lem5272526 (term665 _68980 _68981 _68982)). Qed.
Lemma lem5272528 (_68980 : real) (_68981 : real) (_68982 : real) : ((term577 _68981 _68980 _68982) = (term665 _68980 _68981 _68982)) = True.
Proof. exact (TRANS (@lem5272523 _68980 _68981 _68982) (@lem5272527 _68980 _68981 _68982)). Qed.
Lemma lem5272529 (_68980 : real) (_68981 : real) (_68982 : real) : True = ((term577 _68981 _68980 _68982) = (term665 _68980 _68981 _68982)).
Proof. exact (SYM (@lem5272528 _68980 _68981 _68982)). Qed.
Lemma lem5272530 (_68980 : real) (_68981 : real) (_68982 : real) : (term577 _68981 _68980 _68982) = (term665 _68980 _68981 _68982).
Proof. exact (EQ_MP (@lem5272529 _68980 _68981 _68982) (@lem0)). Qed.
Lemma lem5272531 (_68980 : real) (_68981 : real) (_68982 : real) (h1 : term49) : term665 _68980 _68981 _68982.
Proof. exact (EQ_MP (@lem5272530 _68980 _68981 _68982) (@lem5271705 _68981 _68980 _68982 h1)). Qed.
Lemma lem5272533 (b : Prop) (a : Prop) : (a \/ b) = (term601 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5272534 (_68981 : real) (_68980 : real) (_68982 : real) : (term665 _68980 _68981 _68982) = (term668 _68981 _68980 _68982).
Proof. exact (@lem5272533 (term263 _68980 _68981 _68982) (real_le _68980 _68982)). Qed.
Lemma lem5272536 (a : Prop) (b : Prop) : (term604 a b) = (term605 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5272537 (_68980 : real) (_68981 : real) (_68982 : real) : (term669 _68980 _68981 _68982) = (term670 _68980 _68981 _68982).
Proof. exact (@lem5272536 (term578 _68980 _68981) (term578 _68981 _68982)). Qed.
Lemma lem5272539 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5272540 (_68980 : real) (_68981 : real) : (term671 _68980 _68981) = (real_le _68980 _68981).
Proof. exact (@lem5272539 (real_le _68980 _68981)). Qed.
Lemma lem5272541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5272542 (_68980 : real) (_68981 : real) : (term672 _68980 _68981) = (term673 _68980 _68981).
Proof. exact (MK_COMB (@lem5272541) (@lem5272540 _68980 _68981)). Qed.
Lemma lem5272544 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5272545 (_68981 : real) (_68982 : real) : (term671 _68981 _68982) = (real_le _68981 _68982).
Proof. exact (@lem5272544 (real_le _68981 _68982)). Qed.
Lemma lem5272546 (_68980 : real) (_68981 : real) (_68982 : real) : (term670 _68980 _68981 _68982) = (term268 _68980 _68981 _68982).
Proof. exact (MK_COMB (@lem5272542 _68980 _68981) (@lem5272545 _68981 _68982)). Qed.
Lemma lem5272547 (_68980 : real) (_68981 : real) (_68982 : real) : (term669 _68980 _68981 _68982) = (term268 _68980 _68981 _68982).
Proof. exact (TRANS (@lem5272537 _68980 _68981 _68982) (@lem5272546 _68980 _68981 _68982)). Qed.
Lemma lem5272548 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5272549 (_68980 : real) (_68981 : real) (_68982 : real) : (term674 _68980 _68981 _68982) = (term675 _68980 _68981 _68982).
Proof. exact (MK_COMB (@lem5272548) (@lem5272547 _68980 _68981 _68982)). Qed.
Lemma lem5272550 (_68980 : real) (_68982 : real) : (real_le _68980 _68982) = (real_le _68980 _68982).
Proof. exact (eq_refl (real_le _68980 _68982)). Qed.
Lemma lem5272551 (_68981 : real) (_68980 : real) (_68982 : real) : (term668 _68981 _68980 _68982) = (term43 _68981 _68980 _68982).
Proof. exact (MK_COMB (@lem5272549 _68980 _68981 _68982) (@lem5272550 _68980 _68982)). Qed.
Lemma lem5272552 (_68981 : real) (_68980 : real) (_68982 : real) : (term665 _68980 _68981 _68982) = (term43 _68981 _68980 _68982).
Proof. exact (TRANS (@lem5272534 _68981 _68980 _68982) (@lem5272551 _68981 _68980 _68982)). Qed.
Lemma lem5272554 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term252 b x' s y) (h3 : term168 s y x') : term676 y s x'.
Proof. exact (conj (@lem5272011 s y x' h3) (@lem5272459 x b s y x' h1 h2 h3)). Qed.
Lemma lem5272556 (_68981 : real) (_68980 : real) (_68982 : real) (h1 : term49) : term43 _68981 _68980 _68982.
Proof. exact (EQ_MP (@lem5272552 _68981 _68980 _68982) (@lem5272531 _68980 _68981 _68982 h1)). Qed.
Lemma lem5272557 (s : real -> Prop) (y : real) (x' : real) (h1 : term49) : term677 s y x'.
Proof. exact (@lem5272556 (inf s) y x' h1). Qed.
Lemma lem5272560 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) (h4 : term168 s y x') : real_le y x'.
Proof. exact (@lem5272557 s y x' h2 (@lem5272554 x b s y x' h1 h3 h4)). Qed.
Lemma lem5272561 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) (h4 : term168 s y x') : term678 y x'.
Proof. exact (fun h0 : term578 y x' => @lem5272560 x b s y x' h1 h2 h3 h4). Qed.
Lemma lem5272563 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5272564 (y : real) (x' : real) : (term678 y x') = (real_le y x').
Proof. exact (@lem5272563 (real_le y x')). Qed.
Lemma lem5272565 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) (h4 : term168 s y x') : real_le y x'.
Proof. exact (EQ_MP (@lem5272564 y x') (@lem5272561 x b s y x' h1 h2 h3 h4)). Qed.
Lemma lem5272568 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5272570 (y : real) (x' : real) : (term578 y x') = (term679 y x').
Proof. exact (@lem5272568 (real_le y x')). Qed.
Lemma lem5272573 (s : real -> Prop) (y : real) (x' : real) (h1 : term168 s y x') : term679 y x'.
Proof. exact (EQ_MP (@lem5272570 y x') (@lem5271719 s y x' h1)). Qed.
Lemma lem5272576 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) (h4 : term168 s y x') : False.
Proof. exact (@lem5272573 s y x' h4 (@lem5272565 x b s y x' h1 h2 h3 h4)). Qed.
Lemma lem5272577 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) (h4 : term168 s y x') : term680.
Proof. exact (fun h0 : ~ False => @lem5272576 x b s y x' h1 h2 h3 h4). Qed.
Lemma lem5272579 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5272580 : term680 = False.
Proof. exact (@lem5272579 False). Qed.
Lemma lem5272581 (x : type1021) (b : real) (s : real -> Prop) (y : real) (x' : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) (h4 : term168 s y x') : False.
Proof. exact (EQ_MP (@lem5272580) (@lem5272577 x b s y x' h1 h2 h3 h4)). Qed.
Lemma lem5272648 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (proj1 (@lem5271093 b x' s y h1)). Qed.
Lemma lem5272649 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5272648 b x' s y h1). Qed.
Lemma lem5272651 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5272652 (s : real -> Prop) : (term587 s) = (term148 s).
Proof. exact (@lem5272651 (s = (@EMPTY real))). Qed.
Lemma lem5272653 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (EQ_MP (@lem5272652 s) (@lem5272649 b x' s y h1)). Qed.
Lemma lem5272655 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (proj1 (@lem5271093 b x' s y h1)). Qed.
Lemma lem5272656 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5272655 b x' s y h1). Qed.
Lemma lem5272658 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5272659 (s : real -> Prop) : (term587 s) = (term148 s).
Proof. exact (@lem5272658 (s = (@EMPTY real))). Qed.
Lemma lem5272660 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (EQ_MP (@lem5272659 s) (@lem5272656 b x' s y h1)). Qed.
Lemma lem5272663 (x : type1021) (y : real) (s : real -> Prop) (h1 : term620 x y s) : term620 x y s.
Proof. exact (h1). Qed.
Lemma lem5272664 (x : type1021) (y : real) (s : real -> Prop) (h1 : term620 x y s) : term681 x y s.
Proof. exact (fun h0 : term534 x y s => @lem5272663 x y s h1). Qed.
Lemma lem5272666 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5272667 (x : type1021) (y : real) (s : real -> Prop) : (term681 x y s) = (term620 x y s).
Proof. exact (@lem5272666 (term534 x y s)). Qed.
Lemma lem5272668 (x : type1021) (y : real) (s : real -> Prop) (h1 : term620 x y s) : term620 x y s.
Proof. exact (EQ_MP (@lem5272667 x y s) (@lem5272664 x y s h1)). Qed.
Lemma lem5272671 (y : real) (s : real -> Prop) (h1 : term581 y s) : term581 y s.
Proof. exact (h1). Qed.
Lemma lem5272672 (y : real) (s : real -> Prop) (h1 : term581 y s) : term682 y s.
Proof. exact (fun h0 : term23 y s => @lem5272671 y s h1). Qed.
Lemma lem5272674 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5272675 (y : real) (s : real -> Prop) : (term682 y s) = (term581 y s).
Proof. exact (@lem5272674 (term23 y s)). Qed.
Lemma lem5272676 (y : real) (s : real -> Prop) (h1 : term581 y s) : term581 y s.
Proof. exact (EQ_MP (@lem5272675 y s) (@lem5272672 y s h1)). Qed.
Lemma lem5272709 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5272710 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term683 x _68991 _68992 _68990) = (term684 x _68991 _68992 _68990).
Proof. exact (@lem5272709 (_68990 = (@EMPTY real)) (term534 x _68992 _68990) (term685 x _68991 _68992 _68990)). Qed.
Lemma lem5272726 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5272727 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term686 x _68991 _68992 _68990) = (term687 _68991 x _68992 _68990).
Proof. exact (@lem5272726 (term534 x _68991 _68990) (term534 x _68992 _68990) (term23 _68992 _68990)). Qed.
Lemma lem5272743 (_68990 : real -> Prop) : (term286 _68990) = (term286 _68990).
Proof. exact (eq_refl (term286 _68990)). Qed.
Lemma lem5272744 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term684 x _68991 _68992 _68990) = (term583 _68991 x _68992 _68990).
Proof. exact (MK_COMB (@lem5272743 _68990) (@lem5272727 _68991 x _68992 _68990)). Qed.
Lemma lem5272755 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term683 x _68991 _68992 _68990) = (term583 _68991 x _68992 _68990).
Proof. exact (TRANS (@lem5272710 x _68991 _68992 _68990) (@lem5272744 _68991 x _68992 _68990)). Qed.
Lemma lem5272756 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term688 _68991 x _68992 _68990) = (term688 _68991 x _68992 _68990).
Proof. exact (eq_refl (term688 _68991 x _68992 _68990)). Qed.
Lemma lem5272757 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : ((term583 _68991 x _68992 _68990) = (term683 x _68991 _68992 _68990)) = ((term583 _68991 x _68992 _68990) = (term583 _68991 x _68992 _68990)).
Proof. exact (MK_COMB (@lem5272756 _68991 x _68992 _68990) (@lem5272755 _68991 x _68992 _68990)). Qed.
Lemma lem5272759 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5272760 (x : Prop) : (x = x) = True.
Proof. exact (@lem5272759 Prop x). Qed.
Lemma lem5272761 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : ((term583 _68991 x _68992 _68990) = (term583 _68991 x _68992 _68990)) = True.
Proof. exact (@lem5272760 (term583 _68991 x _68992 _68990)). Qed.
Lemma lem5272762 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : ((term583 _68991 x _68992 _68990) = (term683 x _68991 _68992 _68990)) = True.
Proof. exact (TRANS (@lem5272757 _68991 x _68992 _68990) (@lem5272761 _68991 x _68992 _68990)). Qed.
Lemma lem5272763 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : True = ((term583 _68991 x _68992 _68990) = (term683 x _68991 _68992 _68990)).
Proof. exact (SYM (@lem5272762 x _68991 _68992 _68990)). Qed.
Lemma lem5272764 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term583 _68991 x _68992 _68990) = (term683 x _68991 _68992 _68990).
Proof. exact (EQ_MP (@lem5272763 x _68991 _68992 _68990) (@lem0)). Qed.
Lemma lem5272765 (_68991 : real) (_68992 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term683 x _68991 _68992 _68990.
Proof. exact (EQ_MP (@lem5272764 x _68991 _68992 _68990) (@lem5271891 _68991 _68992 _68990 x h1)). Qed.
Lemma lem5272767 (b : Prop) (a : Prop) : (a \/ b) = (term601 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5272768 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term683 x _68991 _68992 _68990) = (term689 _68991 x _68992 _68990).
Proof. exact (@lem5272767 (term690 x _68991 _68992 _68990) (term534 x _68992 _68990)). Qed.
Lemma lem5272770 (a : Prop) (b : Prop) : (term604 a b) = (term605 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5272771 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term691 x _68991 _68992 _68990) = (term692 x _68991 _68992 _68990).
Proof. exact (@lem5272770 (_68990 = (@EMPTY real)) (term685 x _68991 _68992 _68990)). Qed.
Lemma lem5272773 (a : Prop) (b : Prop) : (term604 a b) = (term605 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5272774 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term693 x _68991 _68992 _68990) = (term694 x _68991 _68992 _68990).
Proof. exact (@lem5272773 (term534 x _68991 _68990) (term23 _68992 _68990)). Qed.
Lemma lem5272775 (_68990 : real -> Prop) : (term38 _68990) = (term38 _68990).
Proof. exact (eq_refl (term38 _68990)). Qed.
Lemma lem5272776 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term692 x _68991 _68992 _68990) = (term695 x _68991 _68992 _68990).
Proof. exact (MK_COMB (@lem5272775 _68990) (@lem5272774 x _68991 _68992 _68990)). Qed.
Lemma lem5272777 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term691 x _68991 _68992 _68990) = (term695 x _68991 _68992 _68990).
Proof. exact (TRANS (@lem5272771 x _68991 _68992 _68990) (@lem5272776 x _68991 _68992 _68990)). Qed.
Lemma lem5272778 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5272779 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term696 x _68991 _68992 _68990) = (term697 x _68991 _68992 _68990).
Proof. exact (MK_COMB (@lem5272778) (@lem5272777 x _68991 _68992 _68990)). Qed.
Lemma lem5272780 (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term534 x _68992 _68990) = (term534 x _68992 _68990).
Proof. exact (eq_refl (term534 x _68992 _68990)). Qed.
Lemma lem5272781 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term689 _68991 x _68992 _68990) = (term698 _68991 x _68992 _68990).
Proof. exact (MK_COMB (@lem5272779 x _68991 _68992 _68990) (@lem5272780 x _68992 _68990)). Qed.
Lemma lem5272782 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term683 x _68991 _68992 _68990) = (term698 _68991 x _68992 _68990).
Proof. exact (TRANS (@lem5272768 _68991 x _68992 _68990) (@lem5272781 _68991 x _68992 _68990)). Qed.
Lemma lem5272784 (x : type1021) (y : real) (s : real -> Prop) (h1 : term620 x y s) (h2 : term581 y s) : term699 x y s.
Proof. exact (conj (@lem5272668 x y s h1) (@lem5272676 y s h2)). Qed.
Lemma lem5272785 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term620 x y s) (h2 : term581 y s) (h3 : term252 b x' s y) : term700 x y s.
Proof. exact (conj (@lem5272660 b x' s y h3) (@lem5272784 x y s h1 h2)). Qed.
Lemma lem5272787 (_68991 : real) (_68992 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term698 _68991 x _68992 _68990.
Proof. exact (EQ_MP (@lem5272782 _68991 x _68992 _68990) (@lem5272765 _68991 _68992 _68990 x h1)). Qed.
Lemma lem5272788 (y : real) (s : real -> Prop) (x : type1021) (h1 : term442 x) : term701 x y s.
Proof. exact (@lem5272787 y y s x h1). Qed.
Lemma lem5272791 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term620 x y s) (h3 : term581 y s) (h4 : term252 b x' s y) : term534 x y s.
Proof. exact (@lem5272788 y s x h1 (@lem5272785 x b x' s y h2 h3 h4)). Qed.
Lemma lem5272792 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term252 b x' s y) : term619 x y s.
Proof. exact (fun h0 : term620 x y s => @lem5272791 x b x' s y h1 h0 h2 h3). Qed.
Lemma lem5272794 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5272795 (x : type1021) (y : real) (s : real -> Prop) : (term619 x y s) = (term534 x y s).
Proof. exact (@lem5272794 (term534 x y s)). Qed.
Lemma lem5272796 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term252 b x' s y) : term534 x y s.
Proof. exact (EQ_MP (@lem5272795 x y s) (@lem5272792 x b x' s y h1 h2 h3)). Qed.
Lemma lem5272802 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5272803 (y : real) (_68994 : real) (s : real -> Prop) : (term55 s y _68994) = (term621 y _68994 s).
Proof. exact (@lem5272802 (real_le y _68994) (term590 _68994 s)). Qed.
Lemma lem5272809 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5272810 (y : real) (_68994 : real) (s : real -> Prop) : (term622 s y _68994) = (term623 y _68994 s).
Proof. exact (MK_COMB (@lem5272809) (@lem5272803 y _68994 s)). Qed.
Lemma lem5272816 (y : real) (_68994 : real) (s : real -> Prop) : (term621 y _68994 s) = (term621 y _68994 s).
Proof. exact (eq_refl (term621 y _68994 s)). Qed.
Lemma lem5272817 (y : real) (_68994 : real) (s : real -> Prop) : ((term55 s y _68994) = (term621 y _68994 s)) = ((term621 y _68994 s) = (term621 y _68994 s)).
Proof. exact (MK_COMB (@lem5272810 y _68994 s) (@lem5272816 y _68994 s)). Qed.
Lemma lem5272819 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5272820 (x : Prop) : (x = x) = True.
Proof. exact (@lem5272819 Prop x). Qed.
Lemma lem5272821 (y : real) (_68994 : real) (s : real -> Prop) : ((term621 y _68994 s) = (term621 y _68994 s)) = True.
Proof. exact (@lem5272820 (term621 y _68994 s)). Qed.
Lemma lem5272822 (y : real) (_68994 : real) (s : real -> Prop) : ((term55 s y _68994) = (term621 y _68994 s)) = True.
Proof. exact (TRANS (@lem5272817 y _68994 s) (@lem5272821 y _68994 s)). Qed.
Lemma lem5272823 (y : real) (_68994 : real) (s : real -> Prop) : True = ((term55 s y _68994) = (term621 y _68994 s)).
Proof. exact (SYM (@lem5272822 y _68994 s)). Qed.
Lemma lem5272824 (y : real) (_68994 : real) (s : real -> Prop) : (term55 s y _68994) = (term621 y _68994 s).
Proof. exact (EQ_MP (@lem5272823 y _68994 s) (@lem0)). Qed.
Lemma lem5272825 (_68994 : real) (s : real -> Prop) (y : real) (h1 : term74 s y) : term621 y _68994 s.
Proof. exact (EQ_MP (@lem5272824 y _68994 s) (@lem5271843 _68994 s y h1)). Qed.
Lemma lem5272827 (b : Prop) (a : Prop) : (a \/ b) = (term601 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5272828 (s : real -> Prop) (y : real) (_68994 : real) : (term621 y _68994 s) = (term624 s y _68994).
Proof. exact (@lem5272827 (term590 _68994 s) (real_le y _68994)). Qed.
Lemma lem5272830 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5272831 (_68994 : real) (s : real -> Prop) : (term611 _68994 s) = (@IN real _68994 s).
Proof. exact (@lem5272830 (@IN real _68994 s)). Qed.
Lemma lem5272832 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5272833 (_68994 : real) (s : real -> Prop) : (term625 _68994 s) = (term626 _68994 s).
Proof. exact (MK_COMB (@lem5272832) (@lem5272831 _68994 s)). Qed.
Lemma lem5272834 (y : real) (_68994 : real) : (real_le y _68994) = (real_le y _68994).
Proof. exact (eq_refl (real_le y _68994)). Qed.
Lemma lem5272835 (s : real -> Prop) (y : real) (_68994 : real) : (term624 s y _68994) = (term24 s y _68994).
Proof. exact (MK_COMB (@lem5272833 _68994 s) (@lem5272834 y _68994)). Qed.
Lemma lem5272836 (s : real -> Prop) (y : real) (_68994 : real) : (term621 y _68994 s) = (term24 s y _68994).
Proof. exact (TRANS (@lem5272828 s y _68994) (@lem5272835 s y _68994)). Qed.
Lemma lem5272839 (_68994 : real) (s : real -> Prop) (y : real) (h1 : term74 s y) : term24 s y _68994.
Proof. exact (EQ_MP (@lem5272836 s y _68994) (@lem5272825 _68994 s y h1)). Qed.
Lemma lem5272840 (x : type1021) (s : real -> Prop) (y : real) (h1 : term74 s y) : term627 x s y.
Proof. exact (@lem5272839 (x s y) s y h1). Qed.
Lemma lem5272843 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term628 x s y.
Proof. exact (@lem5272840 x s y h3 (@lem5272796 x b x' s y h1 h2 h4)). Qed.
Lemma lem5272844 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term629 x s y.
Proof. exact (fun h0 : term535 x s y => @lem5272843 x b x' s y h1 h2 h3 h4). Qed.
Lemma lem5272846 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5272847 (x : type1021) (s : real -> Prop) (y : real) : (term629 x s y) = (term628 x s y).
Proof. exact (@lem5272846 (term628 x s y)). Qed.
Lemma lem5272848 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term628 x s y.
Proof. exact (EQ_MP (@lem5272847 x s y) (@lem5272844 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5272850 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (proj1 (@lem5271093 b x' s y h1)). Qed.
Lemma lem5272851 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5272850 b x' s y h1). Qed.
Lemma lem5272853 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5272854 (s : real -> Prop) : (term587 s) = (term148 s).
Proof. exact (@lem5272853 (s = (@EMPTY real))). Qed.
Lemma lem5272855 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (EQ_MP (@lem5272854 s) (@lem5272851 b x' s y h1)). Qed.
Lemma lem5272857 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (proj1 (@lem5271093 b x' s y h1)). Qed.
Lemma lem5272858 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term587 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5272857 b x' s y h1). Qed.
Lemma lem5272860 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5272861 (s : real -> Prop) : (term587 s) = (term148 s).
Proof. exact (@lem5272860 (s = (@EMPTY real))). Qed.
Lemma lem5272862 (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term252 b x' s y) : term148 s.
Proof. exact (EQ_MP (@lem5272861 s) (@lem5272858 b x' s y h1)). Qed.
Lemma lem5272865 (x : type1021) (y : real) (s : real -> Prop) (h1 : term620 x y s) : term620 x y s.
Proof. exact (h1). Qed.
Lemma lem5272866 (x : type1021) (y : real) (s : real -> Prop) (h1 : term620 x y s) : term681 x y s.
Proof. exact (fun h0 : term534 x y s => @lem5272865 x y s h1). Qed.
Lemma lem5272868 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5272869 (x : type1021) (y : real) (s : real -> Prop) : (term681 x y s) = (term620 x y s).
Proof. exact (@lem5272868 (term534 x y s)). Qed.
Lemma lem5272870 (x : type1021) (y : real) (s : real -> Prop) (h1 : term620 x y s) : term620 x y s.
Proof. exact (EQ_MP (@lem5272869 x y s) (@lem5272866 x y s h1)). Qed.
Lemma lem5272873 (y : real) (s : real -> Prop) (h1 : term581 y s) : term581 y s.
Proof. exact (h1). Qed.
Lemma lem5272874 (y : real) (s : real -> Prop) (h1 : term581 y s) : term682 y s.
Proof. exact (fun h0 : term23 y s => @lem5272873 y s h1). Qed.
Lemma lem5272876 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5272877 (y : real) (s : real -> Prop) : (term682 y s) = (term581 y s).
Proof. exact (@lem5272876 (term23 y s)). Qed.
Lemma lem5272878 (y : real) (s : real -> Prop) (h1 : term581 y s) : term581 y s.
Proof. exact (EQ_MP (@lem5272877 y s) (@lem5272874 y s h1)). Qed.
Lemma lem5272879 (x : type1021) (y : real) (s : real -> Prop) (h1 : term620 x y s) (h2 : term581 y s) : term699 x y s.
Proof. exact (conj (@lem5272870 x y s h1) (@lem5272878 y s h2)). Qed.
Lemma lem5272880 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term620 x y s) (h2 : term581 y s) (h3 : term252 b x' s y) : term700 x y s.
Proof. exact (conj (@lem5272862 b x' s y h3) (@lem5272879 x y s h1 h2)). Qed.
Lemma lem5272882 (_68991 : real) (_68992 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term698 _68991 x _68992 _68990.
Proof. exact (EQ_MP (@lem5272782 _68991 x _68992 _68990) (@lem5272765 _68991 _68992 _68990 x h1)). Qed.
Lemma lem5272883 (y : real) (s : real -> Prop) (x : type1021) (h1 : term442 x) : term701 x y s.
Proof. exact (@lem5272882 y y s x h1). Qed.
Lemma lem5272886 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term620 x y s) (h3 : term581 y s) (h4 : term252 b x' s y) : term534 x y s.
Proof. exact (@lem5272883 y s x h1 (@lem5272880 x b x' s y h2 h3 h4)). Qed.
Lemma lem5272887 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term252 b x' s y) : term619 x y s.
Proof. exact (fun h0 : term620 x y s => @lem5272886 x b x' s y h1 h0 h2 h3). Qed.
Lemma lem5272889 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5272890 (x : type1021) (y : real) (s : real -> Prop) : (term619 x y s) = (term534 x y s).
Proof. exact (@lem5272889 (term534 x y s)). Qed.
Lemma lem5272891 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term252 b x' s y) : term534 x y s.
Proof. exact (EQ_MP (@lem5272890 x y s) (@lem5272887 x b x' s y h1 h2 h3)). Qed.
Lemma lem5272893 (_68994 : real) (s : real -> Prop) (y : real) (h1 : term74 s y) : term24 s y _68994.
Proof. exact (EQ_MP (@lem5272836 s y _68994) (@lem5272825 _68994 s y h1)). Qed.
Lemma lem5272894 (x : type1021) (s : real -> Prop) (y : real) (h1 : term74 s y) : term627 x s y.
Proof. exact (@lem5272893 (x s y) s y h1). Qed.
Lemma lem5272897 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term628 x s y.
Proof. exact (@lem5272894 x s y h3 (@lem5272891 x b x' s y h1 h2 h4)). Qed.
Lemma lem5272898 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term629 x s y.
Proof. exact (fun h0 : term535 x s y => @lem5272897 x b x' s y h1 h2 h3 h4). Qed.
Lemma lem5272900 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5272901 (x : type1021) (s : real -> Prop) (y : real) : (term629 x s y) = (term628 x s y).
Proof. exact (@lem5272900 (term628 x s y)). Qed.
Lemma lem5272902 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term628 x s y.
Proof. exact (EQ_MP (@lem5272901 x s y) (@lem5272898 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5272905 (y : real) (s : real -> Prop) (h1 : term581 y s) : term581 y s.
Proof. exact (h1). Qed.
Lemma lem5272906 (y : real) (s : real -> Prop) (h1 : term581 y s) : term682 y s.
Proof. exact (fun h0 : term23 y s => @lem5272905 y s h1). Qed.
Lemma lem5272908 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5272909 (y : real) (s : real -> Prop) : (term682 y s) = (term581 y s).
Proof. exact (@lem5272908 (term23 y s)). Qed.
Lemma lem5272910 (y : real) (s : real -> Prop) (h1 : term581 y s) : term581 y s.
Proof. exact (EQ_MP (@lem5272909 y s) (@lem5272906 y s h1)). Qed.
Lemma lem5272938 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5272939 (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term544 x _68992 _68990) = (term702 x _68990 _68992).
Proof. exact (@lem5272938 (term23 _68992 _68990) (term535 x _68990 _68992)). Qed.
Lemma lem5272945 (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term703 x _68990 _68991) = (term703 x _68990 _68991).
Proof. exact (eq_refl (term703 x _68990 _68991)). Qed.
Lemma lem5272946 (_68991 : real) (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term704 _68991 x _68992 _68990) = (term705 _68991 x _68990 _68992).
Proof. exact (MK_COMB (@lem5272945 x _68990 _68991) (@lem5272939 x _68990 _68992)). Qed.
Lemma lem5272950 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5272951 (_68991 : real) (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term705 _68991 x _68990 _68992) = (term706 _68991 x _68990 _68992).
Proof. exact (@lem5272950 (term23 _68992 _68990) (term535 x _68990 _68991) (term535 x _68990 _68992)). Qed.
Lemma lem5272967 (_68991 : real) (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term704 _68991 x _68992 _68990) = (term706 _68991 x _68990 _68992).
Proof. exact (TRANS (@lem5272946 _68991 x _68990 _68992) (@lem5272951 _68991 x _68990 _68992)). Qed.
Lemma lem5272968 (_68990 : real -> Prop) : (term286 _68990) = (term286 _68990).
Proof. exact (eq_refl (term286 _68990)). Qed.
Lemma lem5272969 (_68991 : real) (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term582 _68991 x _68992 _68990) = (term707 _68991 x _68990 _68992).
Proof. exact (MK_COMB (@lem5272968 _68990) (@lem5272967 _68991 x _68990 _68992)). Qed.
Lemma lem5272980 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5272981 (_68991 : real) (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term708 _68991 x _68992 _68990) = (term709 _68991 x _68990 _68992).
Proof. exact (MK_COMB (@lem5272980) (@lem5272969 _68991 x _68990 _68992)). Qed.
Lemma lem5272985 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5272986 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term710 x _68991 _68992 _68990) = (term711 x _68991 _68992 _68990).
Proof. exact (@lem5272985 (_68990 = (@EMPTY real)) (term535 x _68990 _68992) (term712 x _68991 _68992 _68990)). Qed.
Lemma lem5273002 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5273003 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term713 x _68991 _68992 _68990) = (term704 _68991 x _68992 _68990).
Proof. exact (@lem5273002 (term535 x _68990 _68991) (term535 x _68990 _68992) (term23 _68992 _68990)). Qed.
Lemma lem5273017 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5273018 (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term544 x _68992 _68990) = (term702 x _68990 _68992).
Proof. exact (@lem5273017 (term23 _68992 _68990) (term535 x _68990 _68992)). Qed.
Lemma lem5273024 (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term703 x _68990 _68991) = (term703 x _68990 _68991).
Proof. exact (eq_refl (term703 x _68990 _68991)). Qed.
Lemma lem5273025 (_68991 : real) (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term704 _68991 x _68992 _68990) = (term705 _68991 x _68990 _68992).
Proof. exact (MK_COMB (@lem5273024 x _68990 _68991) (@lem5273018 x _68990 _68992)). Qed.
Lemma lem5273029 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5273030 (_68991 : real) (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term705 _68991 x _68990 _68992) = (term706 _68991 x _68990 _68992).
Proof. exact (@lem5273029 (term23 _68992 _68990) (term535 x _68990 _68991) (term535 x _68990 _68992)). Qed.
Lemma lem5273046 (_68991 : real) (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term704 _68991 x _68992 _68990) = (term706 _68991 x _68990 _68992).
Proof. exact (TRANS (@lem5273025 _68991 x _68990 _68992) (@lem5273030 _68991 x _68990 _68992)). Qed.
Lemma lem5273047 (_68991 : real) (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term713 x _68991 _68992 _68990) = (term706 _68991 x _68990 _68992).
Proof. exact (TRANS (@lem5273003 _68991 x _68992 _68990) (@lem5273046 _68991 x _68990 _68992)). Qed.
Lemma lem5273048 (_68990 : real -> Prop) : (term286 _68990) = (term286 _68990).
Proof. exact (eq_refl (term286 _68990)). Qed.
Lemma lem5273049 (_68991 : real) (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term711 x _68991 _68992 _68990) = (term707 _68991 x _68990 _68992).
Proof. exact (MK_COMB (@lem5273048 _68990) (@lem5273047 _68991 x _68990 _68992)). Qed.
Lemma lem5273060 (_68991 : real) (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term710 x _68991 _68992 _68990) = (term707 _68991 x _68990 _68992).
Proof. exact (TRANS (@lem5272986 x _68991 _68992 _68990) (@lem5273049 _68991 x _68990 _68992)). Qed.
Lemma lem5273061 (_68991 : real) (x : type1021) (_68990 : real -> Prop) (_68992 : real) : ((term582 _68991 x _68992 _68990) = (term710 x _68991 _68992 _68990)) = ((term707 _68991 x _68990 _68992) = (term707 _68991 x _68990 _68992)).
Proof. exact (MK_COMB (@lem5272981 _68991 x _68990 _68992) (@lem5273060 _68991 x _68990 _68992)). Qed.
Lemma lem5273063 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5273064 (x : Prop) : (x = x) = True.
Proof. exact (@lem5273063 Prop x). Qed.
Lemma lem5273065 (_68991 : real) (x : type1021) (_68990 : real -> Prop) (_68992 : real) : ((term707 _68991 x _68990 _68992) = (term707 _68991 x _68990 _68992)) = True.
Proof. exact (@lem5273064 (term707 _68991 x _68990 _68992)). Qed.
Lemma lem5273066 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : ((term582 _68991 x _68992 _68990) = (term710 x _68991 _68992 _68990)) = True.
Proof. exact (TRANS (@lem5273061 _68991 x _68990 _68992) (@lem5273065 _68991 x _68990 _68992)). Qed.
Lemma lem5273067 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : True = ((term582 _68991 x _68992 _68990) = (term710 x _68991 _68992 _68990)).
Proof. exact (SYM (@lem5273066 x _68991 _68992 _68990)). Qed.
Lemma lem5273068 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term582 _68991 x _68992 _68990) = (term710 x _68991 _68992 _68990).
Proof. exact (EQ_MP (@lem5273067 x _68991 _68992 _68990) (@lem0)). Qed.
Lemma lem5273069 (_68991 : real) (_68992 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term710 x _68991 _68992 _68990.
Proof. exact (EQ_MP (@lem5273068 x _68991 _68992 _68990) (@lem5271875 _68991 _68992 _68990 x h1)). Qed.
Lemma lem5273071 (b : Prop) (a : Prop) : (a \/ b) = (term601 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5273072 (_68991 : real) (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term710 x _68991 _68992 _68990) = (term714 _68991 x _68990 _68992).
Proof. exact (@lem5273071 (term715 x _68991 _68992 _68990) (term535 x _68990 _68992)). Qed.
Lemma lem5273074 (a : Prop) (b : Prop) : (term604 a b) = (term605 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5273075 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term716 x _68991 _68992 _68990) = (term717 x _68991 _68992 _68990).
Proof. exact (@lem5273074 (_68990 = (@EMPTY real)) (term712 x _68991 _68992 _68990)). Qed.
Lemma lem5273077 (a : Prop) (b : Prop) : (term604 a b) = (term605 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5273078 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term718 x _68991 _68992 _68990) = (term719 x _68991 _68992 _68990).
Proof. exact (@lem5273077 (term535 x _68990 _68991) (term23 _68992 _68990)). Qed.
Lemma lem5273080 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5273081 (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term652 x _68990 _68991) = (term628 x _68990 _68991).
Proof. exact (@lem5273080 (term628 x _68990 _68991)). Qed.
Lemma lem5273082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5273083 (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term653 x _68990 _68991) = (term654 x _68990 _68991).
Proof. exact (MK_COMB (@lem5273082) (@lem5273081 x _68990 _68991)). Qed.
Lemma lem5273084 (_68992 : real) (_68990 : real -> Prop) : (term581 _68992 _68990) = (term581 _68992 _68990).
Proof. exact (eq_refl (term581 _68992 _68990)). Qed.
Lemma lem5273085 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term719 x _68991 _68992 _68990) = (term720 x _68991 _68992 _68990).
Proof. exact (MK_COMB (@lem5273083 x _68990 _68991) (@lem5273084 _68992 _68990)). Qed.
Lemma lem5273086 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term718 x _68991 _68992 _68990) = (term720 x _68991 _68992 _68990).
Proof. exact (TRANS (@lem5273078 x _68991 _68992 _68990) (@lem5273085 x _68991 _68992 _68990)). Qed.
Lemma lem5273087 (_68990 : real -> Prop) : (term38 _68990) = (term38 _68990).
Proof. exact (eq_refl (term38 _68990)). Qed.
Lemma lem5273088 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term717 x _68991 _68992 _68990) = (term721 x _68991 _68992 _68990).
Proof. exact (MK_COMB (@lem5273087 _68990) (@lem5273086 x _68991 _68992 _68990)). Qed.
Lemma lem5273089 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term716 x _68991 _68992 _68990) = (term721 x _68991 _68992 _68990).
Proof. exact (TRANS (@lem5273075 x _68991 _68992 _68990) (@lem5273088 x _68991 _68992 _68990)). Qed.
Lemma lem5273090 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5273091 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term722 x _68991 _68992 _68990) = (term723 x _68991 _68992 _68990).
Proof. exact (MK_COMB (@lem5273090) (@lem5273089 x _68991 _68992 _68990)). Qed.
Lemma lem5273092 (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term535 x _68990 _68992) = (term535 x _68990 _68992).
Proof. exact (eq_refl (term535 x _68990 _68992)). Qed.
Lemma lem5273093 (_68991 : real) (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term714 _68991 x _68990 _68992) = (term724 _68991 x _68990 _68992).
Proof. exact (MK_COMB (@lem5273091 x _68991 _68992 _68990) (@lem5273092 x _68990 _68992)). Qed.
Lemma lem5273094 (_68991 : real) (x : type1021) (_68990 : real -> Prop) (_68992 : real) : (term710 x _68991 _68992 _68990) = (term724 _68991 x _68990 _68992).
Proof. exact (TRANS (@lem5273072 _68991 x _68990 _68992) (@lem5273093 _68991 x _68990 _68992)). Qed.
Lemma lem5273096 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term725 x y s.
Proof. exact (conj (@lem5272902 x b x' s y h1 h2 h3 h4) (@lem5272910 y s h2)). Qed.
Lemma lem5273097 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term726 x y s.
Proof. exact (conj (@lem5272855 b x' s y h4) (@lem5273096 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5273099 (_68991 : real) (_68990 : real -> Prop) (_68992 : real) (x : type1021) (h1 : term442 x) : term724 _68991 x _68990 _68992.
Proof. exact (EQ_MP (@lem5273094 _68991 x _68990 _68992) (@lem5273069 _68991 _68992 _68990 x h1)). Qed.
Lemma lem5273100 (s : real -> Prop) (y : real) (x : type1021) (h1 : term442 x) : term727 x s y.
Proof. exact (@lem5273099 y s y x h1). Qed.
Lemma lem5273103 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term535 x s y.
Proof. exact (@lem5273100 s y x h1 (@lem5273097 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5273104 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term728 x s y.
Proof. exact (fun h0 : term628 x s y => @lem5273103 x b x' s y h1 h2 h3 h4). Qed.
Lemma lem5273106 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5273107 (x : type1021) (s : real -> Prop) (y : real) : (term728 x s y) = (term535 x s y).
Proof. exact (@lem5273106 (term628 x s y)). Qed.
Lemma lem5273108 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term535 x s y.
Proof. exact (EQ_MP (@lem5273107 x s y) (@lem5273104 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5273110 (b : Prop) (a : Prop) : (a \/ b) = (term601 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5273113 (y : real) (_68994 : real) (s : real -> Prop) : (term55 s y _68994) = (term729 y _68994 s).
Proof. exact (@lem5273110 (real_le y _68994) (term590 _68994 s)). Qed.
Lemma lem5273116 (_68994 : real) (s : real -> Prop) (y : real) (h1 : term74 s y) : term729 y _68994 s.
Proof. exact (EQ_MP (@lem5273113 y _68994 s) (@lem5271843 _68994 s y h1)). Qed.
Lemma lem5273117 (x : type1021) (s : real -> Prop) (y : real) (h1 : term74 s y) : term730 x y s.
Proof. exact (@lem5273116 (x s y) s y h1). Qed.
Lemma lem5273120 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term620 x y s.
Proof. exact (@lem5273117 x s y h3 (@lem5273108 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5273121 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term681 x y s.
Proof. exact (fun h0 : term534 x y s => @lem5273120 x b x' s y h1 h2 h3 h4). Qed.
Lemma lem5273123 (p : Prop) : (term588 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5273124 (x : type1021) (y : real) (s : real -> Prop) : (term681 x y s) = (term620 x y s).
Proof. exact (@lem5273123 (term534 x y s)). Qed.
Lemma lem5273125 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term620 x y s.
Proof. exact (EQ_MP (@lem5273124 x y s) (@lem5273121 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5273143 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5273144 (x : type1021) (_68991 : real) (_68992 : real) (_68990 : real -> Prop) : (term731 _68991 x _68992 _68990) = (term732 x _68991 _68992 _68990).
Proof. exact (@lem5273143 (term534 x _68992 _68990) (term535 x _68990 _68991) (term23 _68992 _68990)). Qed.
Lemma lem5273158 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5273159 (_68992 : real) (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term712 x _68991 _68992 _68990) = (term733 _68992 x _68990 _68991).
Proof. exact (@lem5273158 (term23 _68992 _68990) (term535 x _68990 _68991)). Qed.
Lemma lem5273165 (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term594 x _68992 _68990) = (term594 x _68992 _68990).
Proof. exact (eq_refl (term594 x _68992 _68990)). Qed.
Lemma lem5273166 (_68992 : real) (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term732 x _68991 _68992 _68990) = (term734 _68992 x _68990 _68991).
Proof. exact (MK_COMB (@lem5273165 x _68992 _68990) (@lem5273159 _68992 x _68990 _68991)). Qed.
Lemma lem5273177 (_68992 : real) (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term731 _68991 x _68992 _68990) = (term734 _68992 x _68990 _68991).
Proof. exact (TRANS (@lem5273144 x _68991 _68992 _68990) (@lem5273166 _68992 x _68990 _68991)). Qed.
Lemma lem5273178 (_68990 : real -> Prop) : (term286 _68990) = (term286 _68990).
Proof. exact (eq_refl (term286 _68990)). Qed.
Lemma lem5273179 (_68992 : real) (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term584 _68991 x _68992 _68990) = (term735 _68992 x _68990 _68991).
Proof. exact (MK_COMB (@lem5273178 _68990) (@lem5273177 _68992 x _68990 _68991)). Qed.
Lemma lem5273190 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5273191 (_68992 : real) (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term736 _68991 x _68992 _68990) = (term737 _68992 x _68990 _68991).
Proof. exact (MK_COMB (@lem5273190) (@lem5273179 _68992 x _68990 _68991)). Qed.
Lemma lem5273195 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5273196 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term738 _68991 x _68992 _68990) = (term739 _68991 x _68992 _68990).
Proof. exact (@lem5273195 (_68990 = (@EMPTY real)) (term23 _68992 _68990) (term740 _68991 x _68992 _68990)). Qed.
Lemma lem5273222 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5273223 (_68992 : real) (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term740 _68991 x _68992 _68990) = (term741 _68992 x _68990 _68991).
Proof. exact (@lem5273222 (term534 x _68992 _68990) (term535 x _68990 _68991)). Qed.
Lemma lem5273229 (_68992 : real) (_68990 : real -> Prop) : (term742 _68992 _68990) = (term742 _68992 _68990).
Proof. exact (eq_refl (term742 _68992 _68990)). Qed.
Lemma lem5273230 (_68992 : real) (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term743 _68991 x _68992 _68990) = (term744 _68992 x _68990 _68991).
Proof. exact (MK_COMB (@lem5273229 _68992 _68990) (@lem5273223 _68992 x _68990 _68991)). Qed.
Lemma lem5273234 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5273235 (_68992 : real) (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term744 _68992 x _68990 _68991) = (term734 _68992 x _68990 _68991).
Proof. exact (@lem5273234 (term534 x _68992 _68990) (term23 _68992 _68990) (term535 x _68990 _68991)). Qed.
Lemma lem5273251 (_68992 : real) (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term743 _68991 x _68992 _68990) = (term734 _68992 x _68990 _68991).
Proof. exact (TRANS (@lem5273230 _68992 x _68990 _68991) (@lem5273235 _68992 x _68990 _68991)). Qed.
Lemma lem5273252 (_68990 : real -> Prop) : (term286 _68990) = (term286 _68990).
Proof. exact (eq_refl (term286 _68990)). Qed.
Lemma lem5273253 (_68992 : real) (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term739 _68991 x _68992 _68990) = (term735 _68992 x _68990 _68991).
Proof. exact (MK_COMB (@lem5273252 _68990) (@lem5273251 _68992 x _68990 _68991)). Qed.
Lemma lem5273264 (_68992 : real) (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term738 _68991 x _68992 _68990) = (term735 _68992 x _68990 _68991).
Proof. exact (TRANS (@lem5273196 _68991 x _68992 _68990) (@lem5273253 _68992 x _68990 _68991)). Qed.
Lemma lem5273265 (_68992 : real) (x : type1021) (_68990 : real -> Prop) (_68991 : real) : ((term584 _68991 x _68992 _68990) = (term738 _68991 x _68992 _68990)) = ((term735 _68992 x _68990 _68991) = (term735 _68992 x _68990 _68991)).
Proof. exact (MK_COMB (@lem5273191 _68992 x _68990 _68991) (@lem5273264 _68992 x _68990 _68991)). Qed.
Lemma lem5273267 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5273268 (x : Prop) : (x = x) = True.
Proof. exact (@lem5273267 Prop x). Qed.
Lemma lem5273269 (_68992 : real) (x : type1021) (_68990 : real -> Prop) (_68991 : real) : ((term735 _68992 x _68990 _68991) = (term735 _68992 x _68990 _68991)) = True.
Proof. exact (@lem5273268 (term735 _68992 x _68990 _68991)). Qed.
Lemma lem5273270 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : ((term584 _68991 x _68992 _68990) = (term738 _68991 x _68992 _68990)) = True.
Proof. exact (TRANS (@lem5273265 _68992 x _68990 _68991) (@lem5273269 _68992 x _68990 _68991)). Qed.
Lemma lem5273271 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : True = ((term584 _68991 x _68992 _68990) = (term738 _68991 x _68992 _68990)).
Proof. exact (SYM (@lem5273270 _68991 x _68992 _68990)). Qed.
Lemma lem5273272 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term584 _68991 x _68992 _68990) = (term738 _68991 x _68992 _68990).
Proof. exact (EQ_MP (@lem5273271 _68991 x _68992 _68990) (@lem0)). Qed.
Lemma lem5273273 (_68991 : real) (_68992 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term738 _68991 x _68992 _68990.
Proof. exact (EQ_MP (@lem5273272 _68991 x _68992 _68990) (@lem5271907 _68991 _68992 _68990 x h1)). Qed.
Lemma lem5273275 (b : Prop) (a : Prop) : (a \/ b) = (term601 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5273276 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term738 _68991 x _68992 _68990) = (term745 _68991 x _68992 _68990).
Proof. exact (@lem5273275 (term746 _68991 x _68992 _68990) (term23 _68992 _68990)). Qed.
Lemma lem5273278 (a : Prop) (b : Prop) : (term604 a b) = (term605 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5273279 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term747 _68991 x _68992 _68990) = (term748 _68991 x _68992 _68990).
Proof. exact (@lem5273278 (_68990 = (@EMPTY real)) (term740 _68991 x _68992 _68990)). Qed.
Lemma lem5273281 (a : Prop) (b : Prop) : (term604 a b) = (term605 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5273282 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term749 _68991 x _68992 _68990) = (term750 _68991 x _68992 _68990).
Proof. exact (@lem5273281 (term535 x _68990 _68991) (term534 x _68992 _68990)). Qed.
Lemma lem5273284 (a : Prop) : (term610 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5273285 (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term652 x _68990 _68991) = (term628 x _68990 _68991).
Proof. exact (@lem5273284 (term628 x _68990 _68991)). Qed.
Lemma lem5273286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5273287 (x : type1021) (_68990 : real -> Prop) (_68991 : real) : (term653 x _68990 _68991) = (term654 x _68990 _68991).
Proof. exact (MK_COMB (@lem5273286) (@lem5273285 x _68990 _68991)). Qed.
Lemma lem5273288 (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term620 x _68992 _68990) = (term620 x _68992 _68990).
Proof. exact (eq_refl (term620 x _68992 _68990)). Qed.
Lemma lem5273289 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term750 _68991 x _68992 _68990) = (term751 _68991 x _68992 _68990).
Proof. exact (MK_COMB (@lem5273287 x _68990 _68991) (@lem5273288 x _68992 _68990)). Qed.
Lemma lem5273290 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term749 _68991 x _68992 _68990) = (term751 _68991 x _68992 _68990).
Proof. exact (TRANS (@lem5273282 _68991 x _68992 _68990) (@lem5273289 _68991 x _68992 _68990)). Qed.
Lemma lem5273291 (_68990 : real -> Prop) : (term38 _68990) = (term38 _68990).
Proof. exact (eq_refl (term38 _68990)). Qed.
Lemma lem5273292 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term748 _68991 x _68992 _68990) = (term752 _68991 x _68992 _68990).
Proof. exact (MK_COMB (@lem5273291 _68990) (@lem5273290 _68991 x _68992 _68990)). Qed.
Lemma lem5273293 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term747 _68991 x _68992 _68990) = (term752 _68991 x _68992 _68990).
Proof. exact (TRANS (@lem5273279 _68991 x _68992 _68990) (@lem5273292 _68991 x _68992 _68990)). Qed.
Lemma lem5273294 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5273295 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term753 _68991 x _68992 _68990) = (term754 _68991 x _68992 _68990).
Proof. exact (MK_COMB (@lem5273294) (@lem5273293 _68991 x _68992 _68990)). Qed.
Lemma lem5273296 (_68992 : real) (_68990 : real -> Prop) : (term23 _68992 _68990) = (term23 _68992 _68990).
Proof. exact (eq_refl (term23 _68992 _68990)). Qed.
Lemma lem5273297 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term745 _68991 x _68992 _68990) = (term755 _68991 x _68992 _68990).
Proof. exact (MK_COMB (@lem5273295 _68991 x _68992 _68990) (@lem5273296 _68992 _68990)). Qed.
Lemma lem5273298 (_68991 : real) (x : type1021) (_68992 : real) (_68990 : real -> Prop) : (term738 _68991 x _68992 _68990) = (term755 _68991 x _68992 _68990).
Proof. exact (TRANS (@lem5273276 _68991 x _68992 _68990) (@lem5273297 _68991 x _68992 _68990)). Qed.
Lemma lem5273300 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term756 x y s.
Proof. exact (conj (@lem5272848 x b x' s y h1 h2 h3 h4) (@lem5273125 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5273301 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term757 x y s.
Proof. exact (conj (@lem5272653 b x' s y h4) (@lem5273300 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5273303 (_68991 : real) (_68992 : real) (_68990 : real -> Prop) (x : type1021) (h1 : term442 x) : term755 _68991 x _68992 _68990.
Proof. exact (EQ_MP (@lem5273298 _68991 x _68992 _68990) (@lem5273273 _68991 _68992 _68990 x h1)). Qed.
Lemma lem5273304 (y : real) (s : real -> Prop) (x : type1021) (h1 : term442 x) : term758 x y s.
Proof. exact (@lem5273303 y y s x h1). Qed.
Lemma lem5273307 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term581 y s) (h3 : term74 s y) (h4 : term252 b x' s y) : term23 y s.
Proof. exact (@lem5273304 y s x h1 (@lem5273301 x b x' s y h1 h2 h3 h4)). Qed.
Lemma lem5273308 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term74 s y) (h3 : term252 b x' s y) : term585 y s.
Proof. exact (fun h0 : term581 y s => @lem5273307 x b x' s y h1 h0 h2 h3). Qed.
Lemma lem5273310 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5273311 (y : real) (s : real -> Prop) : (term585 y s) = (term23 y s).
Proof. exact (@lem5273310 (term23 y s)). Qed.
Lemma lem5273312 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term74 s y) (h3 : term252 b x' s y) : term23 y s.
Proof. exact (EQ_MP (@lem5273311 y s) (@lem5273308 x b x' s y h1 h2 h3)). Qed.
Lemma lem5273315 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5273317 (y : real) (s : real -> Prop) : (term581 y s) = (term759 y s).
Proof. exact (@lem5273315 (term23 y s)). Qed.
Lemma lem5273320 (s : real -> Prop) (y : real) (h1 : term74 s y) : term759 y s.
Proof. exact (EQ_MP (@lem5273317 y s) (@lem5271837 s y h1)). Qed.
Lemma lem5273323 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term74 s y) (h3 : term252 b x' s y) : False.
Proof. exact (@lem5273320 s y h2 (@lem5273312 x b x' s y h1 h2 h3)). Qed.
Lemma lem5273324 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term74 s y) (h3 : term252 b x' s y) : term680.
Proof. exact (fun h0 : ~ False => @lem5273323 x b x' s y h1 h2 h3). Qed.
Lemma lem5273326 (p : Prop) : (term586 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5273327 : term680 = False.
Proof. exact (@lem5273326 False). Qed.
Lemma lem5273328 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term74 s y) (h3 : term252 b x' s y) : False.
Proof. exact (EQ_MP (@lem5273327) (@lem5273324 x b x' s y h1 h2 h3)). Qed.
Lemma lem5273329 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) : False.
Proof. exact (or_elim (@lem5271092 b x' s y h3) (fun h0 : term168 s y x' => @lem5272581 x b s y x' h1 h2 h3 h0) (fun h0 : term74 s y => @lem5273328 x b x' s y h1 h0 h3)). Qed.
Lemma lem5273330 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) : (term252 b x' s y) = False.
Proof. exact (prop_ext (fun h4 : term252 b x' s y => @lem5273329 x b x' s y h1 h2 h3) (fun h4 : False => @lem5271091 b x' s y h3)). Qed.
Lemma lem5273331 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) : False.
Proof. exact (EQ_MP (@lem5273330 x b x' s y h1 h2 h3) (@lem5271091 b x' s y h3)). Qed.
Lemma lem5273332 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) : (term442 x) = False.
Proof. exact (prop_ext (fun h4 : term442 x => @lem5273331 x b x' s y h1 h2 h3) (fun h4 : False => @lem5271001 x h1)). Qed.
Lemma lem5273333 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term252 b x' s y) : False.
Proof. exact (EQ_MP (@lem5273332 x b x' s y h1 h2 h3) (@lem5271001 x h1)). Qed.
Lemma lem5273334 (x : type1021) (b : real) (s : real -> Prop) (y : real) (h1 : term442 x) (h2 : term49) (h3 : term255 b s y) : False.
Proof. exact (ex_elim (@lem5270865 b s y h3) (fun x' : real => fun h0 : term254 b s y x' => @lem5273333 x b x' s y h1 h2 h0)). Qed.
Lemma lem5273335 (x : type1021) (b : real) (s : real -> Prop) (h1 : term442 x) (h2 : term49) (h3 : term257 b s) : False.
Proof. exact (ex_elim (@lem5270864 b s h3) (fun y : real => fun h0 : term256 b s y => @lem5273334 x b s y h1 h2 h0)). Qed.
Lemma lem5273336 (x : type1021) (s : real -> Prop) (h1 : term442 x) (h2 : term49) (h3 : term259 s) : False.
Proof. exact (ex_elim (@lem5270863 s h3) (fun b : real => fun h0 : term258 s b => @lem5273335 x b s h1 h2 h0)). Qed.
Lemma lem5273337 (x : type1021) (h1 : term442 x) (h2 : term49) (h3 : term10) : False.
Proof. exact (ex_elim (@lem5270249 h3) (fun s : real -> Prop => fun h0 : term260 s => @lem5273336 x s h1 h2 h0)). Qed.
Lemma lem5273338 (h1 : term17) (h2 : term49) (h3 : term10) : False.
Proof. exact (ex_elim (@lem5270861 h1) (fun x : type1021 => fun h0 : term444 x => @lem5273337 x h0 h2 h3)). Qed.
Lemma lem5273339 (h1 : term49) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem5273338 h0 h1 h2). Qed.
Lemma lem5273340 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem5273341 (h1 : term49) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem5273340) (@lem5273339 h1 h2)). Qed.
Lemma lem5273342 (h1 : term10) : term20.
Proof. exact (fun h0 : term49 => @lem5273341 h0 h1). Qed.
Lemma lem5273343 : term22.
Proof. exact (fun h0 : term10 => @lem5273342 h0). Qed.
Lemma lem5273344 : term11.
Proof. exact (EQ_MP (@lem5269630) (@lem5273343)). Qed.
Lemma lem5273346 : term11.
Proof. exact (@lem5269296 (@lem5273344)). Qed.
Lemma lem5273347 (h1 : term10) : term19.
Proof. exact (@lem5273346 (@lem5269281 h1)). Qed.
Lemma lem5273348 (h1 : term10) : term15.
Proof. exact (@lem5273347 h1 (@lem1339577)). Qed.
Lemma lem5273349 (h1 : term10) : False.
Proof. exact (@lem5273348 h1 (@lem5214027)). Qed.
Lemma lem5273350 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem5273349 h1) (fun h2 : False => @lem5269281 h1)). Qed.
Lemma lem5273351 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem5273350 h1) (@lem5269281 h1)). Qed.
Lemma lem5273352 : term9.
Proof. exact (fun h0 : term10 => @lem5273351 h0). Qed.
Lemma lem5273353 : term8.
Proof. exact (EQ_MP (@lem5269280) (@lem5273352)). Qed.
