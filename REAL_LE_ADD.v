Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_ADD_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_ADD_RID_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339577_spec.
Require Import thm1339889_spec.
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
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1372269 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1372270 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1372271 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1372270 t1) (@lem1372269 t1)). Qed.
Lemma lem1372272 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1372271 t1 t2). Qed.
Lemma lem1372273 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1372274 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1372273 t1 t2) (@lem1372272 t1 t2)). Qed.
Lemma lem1372275 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1372274 t1 t2 t3). Qed.
Lemma lem1372276 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1372277 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1372276 t1 t2 t3) (@lem1372275 t1 t2 t3)). Qed.
Lemma lem1372278 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1372277 t1 t2 t3)). Qed.
Lemma lem1372280 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1372281 : term8 = term9.
Proof. exact (@lem1372280 term8). Qed.
Lemma lem1372282 : term9 = term8.
Proof. exact (SYM (@lem1372281)). Qed.
Lemma lem1372283 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1372286 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1372287 : term12.
Proof. exact (fun h0 : term11 => @lem1372286 h0). Qed.
Lemma lem1372288 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1372289 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1372290 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1372288 h2 (@lem1372289 h1)). Qed.
Lemma lem1372291 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1372290 h1 h0). Qed.
Lemma lem1372292 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1372293 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1372291 h1 (@lem1372292 h2)). Qed.
Lemma lem1372294 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1372293 h0 h1). Qed.
Lemma lem1372295 : term14.
Proof. exact (fun h0 : term12 => @lem1372294 h0). Qed.
Lemma lem1372298 : term12.
Proof. exact (@lem1372295 (@lem1372287)). Qed.
Lemma lem1372338 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1372339 : term15 = term16.
Proof. exact (@lem1372338 term17). Qed.
Lemma lem1372354 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1372355 : term19 = term20.
Proof. exact (MK_COMB (@lem1372354) (@lem1372339)). Qed.
Lemma lem1372358 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1372359 : term22 = term23.
Proof. exact (MK_COMB (@lem1372358) (@lem1372355)). Qed.
Lemma lem1372362 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1372369 : term11 = term25.
Proof. exact (MK_COMB (@lem1372362) (@lem1372359)). Qed.
Lemma lem1372374 (y : real) (x : real) (z : real) : (term26 y x z) = (term26 y x z).
Proof. exact (eq_refl (term26 y x z)). Qed.
Lemma lem1372375 (y : real) (x : real) : (term27 y x) = (term27 y x).
Proof. exact (fun_ext (fun z : real => @lem1372374 y x z)). Qed.
Lemma lem1372376 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372377 (y : real) (x : real) : (term28 y x) = (term28 y x).
Proof. exact (MK_COMB (@lem1372376) (@lem1372375 y x)). Qed.
Lemma lem1372378 (x : real) : (term29 x) = (term29 x).
Proof. exact (fun_ext (fun y : real => @lem1372377 y x)). Qed.
Lemma lem1372379 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372380 (x : real) : (term30 x) = (term30 x).
Proof. exact (MK_COMB (@lem1372379) (@lem1372378 x)). Qed.
Lemma lem1372381 : term31 = term31.
Proof. exact (fun_ext (fun x : real => @lem1372380 x)). Qed.
Lemma lem1372382 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372383 : term17 = term17.
Proof. exact (MK_COMB (@lem1372382) (@lem1372381)). Qed.
Lemma lem1372384 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1372385 : term16 = term16.
Proof. exact (MK_COMB (@lem1372384) (@lem1372383)). Qed.
Lemma lem1372386 (x : real) : ((term32 x) = x) = ((term32 x) = x).
Proof. exact (eq_refl ((term32 x) = x)). Qed.
Lemma lem1372387 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1372386 x)). Qed.
Lemma lem1372388 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372389 : term34 = term34.
Proof. exact (MK_COMB (@lem1372388) (@lem1372387)). Qed.
Lemma lem1372390 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1372391 : term18 = term18.
Proof. exact (MK_COMB (@lem1372390) (@lem1372389)). Qed.
Lemma lem1372392 : term20 = term20.
Proof. exact (MK_COMB (@lem1372391) (@lem1372385)). Qed.
Lemma lem1372401 (y : real) (x : real) (z : real) : (term35 y x z) = (term35 y x z).
Proof. exact (eq_refl (term35 y x z)). Qed.
Lemma lem1372402 (y : real) (x : real) : (term36 y x) = (term36 y x).
Proof. exact (fun_ext (fun z : real => @lem1372401 y x z)). Qed.
Lemma lem1372403 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372404 (y : real) (x : real) : (term37 y x) = (term37 y x).
Proof. exact (MK_COMB (@lem1372403) (@lem1372402 y x)). Qed.
Lemma lem1372405 (x : real) : (term38 x) = (term38 x).
Proof. exact (fun_ext (fun y : real => @lem1372404 y x)). Qed.
Lemma lem1372406 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372407 (x : real) : (term39 x) = (term39 x).
Proof. exact (MK_COMB (@lem1372406) (@lem1372405 x)). Qed.
Lemma lem1372408 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1372407 x)). Qed.
Lemma lem1372409 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372410 : term41 = term41.
Proof. exact (MK_COMB (@lem1372409) (@lem1372408)). Qed.
Lemma lem1372411 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1372412 : term21 = term21.
Proof. exact (MK_COMB (@lem1372411) (@lem1372410)). Qed.
Lemma lem1372413 : term23 = term23.
Proof. exact (MK_COMB (@lem1372412) (@lem1372392)). Qed.
Lemma lem1372422 (x : real) (y : real) : (term42 x y) = (term42 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1372423 (x : real) : (term43 x) = (term43 x).
Proof. exact (fun_ext (fun y : real => @lem1372422 x y)). Qed.
Lemma lem1372424 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372425 (x : real) : (term44 x) = (term44 x).
Proof. exact (MK_COMB (@lem1372424) (@lem1372423 x)). Qed.
Lemma lem1372426 : term45 = term45.
Proof. exact (fun_ext (fun x : real => @lem1372425 x)). Qed.
Lemma lem1372427 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372428 : term8 = term8.
Proof. exact (MK_COMB (@lem1372427) (@lem1372426)). Qed.
Lemma lem1372429 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1372430 : term10 = term10.
Proof. exact (MK_COMB (@lem1372429) (@lem1372428)). Qed.
Lemma lem1372431 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1372432 : term24 = term24.
Proof. exact (MK_COMB (@lem1372431) (@lem1372430)). Qed.
Lemma lem1372433 : term25 = term25.
Proof. exact (MK_COMB (@lem1372432) (@lem1372413)). Qed.
Lemma lem1372506 : term11 = term25.
Proof. exact (TRANS (@lem1372369) (@lem1372433)). Qed.
Lemma lem1372507 : term25 = term11.
Proof. exact (SYM (@lem1372506)). Qed.
Lemma lem1372508 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1372509 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem1372510 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem1372511 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1372522 (x : real) (y : real) : (term46 x y) = (term47 x y).
Proof. exact (@lem17362 (term48 x y) (term49 x y)). Qed.
Lemma lem1372523 (P : real -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1372524 (x : real) : (term52 x) = (term53 x).
Proof. exact (@lem1372523 (term43 x)). Qed.
Lemma lem1372525 (x : real) (y : real) : (term54 x y) = (term42 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1372526 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1372527 (x : real) (y : real) : (term55 x y) = (term46 x y).
Proof. exact (MK_COMB (@lem1372526) (@lem1372525 x y)). Qed.
Lemma lem1372528 (x : real) (y : real) : (term55 x y) = (term47 x y).
Proof. exact (TRANS (@lem1372527 x y) (@lem1372522 x y)). Qed.
Lemma lem1372529 (x : real) : (term56 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1372528 x y)). Qed.
Lemma lem1372530 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1372531 (x : real) : (term53 x) = (term58 x).
Proof. exact (MK_COMB (@lem1372530) (@lem1372529 x)). Qed.
Lemma lem1372532 (x : real) : (term52 x) = (term58 x).
Proof. exact (TRANS (@lem1372524 x) (@lem1372531 x)). Qed.
Lemma lem1372533 (P : real -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1372534 : term10 = term59.
Proof. exact (@lem1372533 term45). Qed.
Lemma lem1372535 (x : real) : (term60 x) = (term44 x).
Proof. exact (eq_refl (term60 x)). Qed.
Lemma lem1372536 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1372537 (x : real) : (term61 x) = (term52 x).
Proof. exact (MK_COMB (@lem1372536) (@lem1372535 x)). Qed.
Lemma lem1372538 (x : real) : (term61 x) = (term58 x).
Proof. exact (TRANS (@lem1372537 x) (@lem1372532 x)). Qed.
Lemma lem1372539 : term62 = term63.
Proof. exact (fun_ext (fun x : real => @lem1372538 x)). Qed.
Lemma lem1372540 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1372541 : term59 = term64.
Proof. exact (MK_COMB (@lem1372540) (@lem1372539)). Qed.
Lemma lem1372598 : term10 = term64.
Proof. exact (TRANS (@lem1372534) (@lem1372541)). Qed.
Lemma lem1372599 (h1 : term10) : term64.
Proof. exact (EQ_MP (@lem1372598) (@lem1372508 h1)). Qed.
Lemma lem1372606 (x : real) (y : real) (z : real) : (term65 x y z) = (term66 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem1372607 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem1372608 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1372609 (x : real) (y : real) (z : real) : (term67 x y z) = (term68 x y z).
Proof. exact (MK_COMB (@lem1372608) (@lem1372606 x y z)). Qed.
Lemma lem1372610 (y : real) (x : real) (z : real) : (term69 y x z) = (term70 y x z).
Proof. exact (MK_COMB (@lem1372609 x y z) (@lem1372607 x z)). Qed.
Lemma lem1372611 (y : real) (x : real) (z : real) : (term35 y x z) = (term69 y x z).
Proof. exact (@lem17265 (term71 x y z) (real_le x z)). Qed.
Lemma lem1372612 (y : real) (x : real) (z : real) : (term35 y x z) = (term70 y x z).
Proof. exact (TRANS (@lem1372611 y x z) (@lem1372610 y x z)). Qed.
Lemma lem1372613 (y : real) (x : real) : (term36 y x) = (term72 y x).
Proof. exact (fun_ext (fun z : real => @lem1372612 y x z)). Qed.
Lemma lem1372614 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372615 (y : real) (x : real) : (term37 y x) = (term73 y x).
Proof. exact (MK_COMB (@lem1372614) (@lem1372613 y x)). Qed.
Lemma lem1372616 (x : real) : (term38 x) = (term74 x).
Proof. exact (fun_ext (fun y : real => @lem1372615 y x)). Qed.
Lemma lem1372617 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372618 (x : real) : (term39 x) = (term75 x).
Proof. exact (MK_COMB (@lem1372617) (@lem1372616 x)). Qed.
Lemma lem1372619 : term40 = term76.
Proof. exact (fun_ext (fun x : real => @lem1372618 x)). Qed.
Lemma lem1372620 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372681 : term41 = term77.
Proof. exact (MK_COMB (@lem1372620) (@lem1372619)). Qed.
Lemma lem1372682 (h1 : term41) : term77.
Proof. exact (EQ_MP (@lem1372681) (@lem1372509 h1)). Qed.
Lemma lem1372683 (x : real) : ((term32 x) = x) = ((term32 x) = x).
Proof. exact (eq_refl ((term32 x) = x)). Qed.
Lemma lem1372684 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1372683 x)). Qed.
Lemma lem1372685 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372694 : term34 = term34.
Proof. exact (MK_COMB (@lem1372685) (@lem1372684)). Qed.
Lemma lem1372695 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem1372694) (@lem1372510 h1)). Qed.
Lemma lem1372702 (y : real) (x : real) (z : real) : (term26 y x z) = (term78 y x z).
Proof. exact (@lem17265 (real_le y z) (term79 y x z)). Qed.
Lemma lem1372703 (y : real) (x : real) : (term27 y x) = (term80 y x).
Proof. exact (fun_ext (fun z : real => @lem1372702 y x z)). Qed.
Lemma lem1372704 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372705 (y : real) (x : real) : (term28 y x) = (term81 y x).
Proof. exact (MK_COMB (@lem1372704) (@lem1372703 y x)). Qed.
Lemma lem1372706 (x : real) : (term29 x) = (term82 x).
Proof. exact (fun_ext (fun y : real => @lem1372705 y x)). Qed.
Lemma lem1372707 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372708 (x : real) : (term30 x) = (term83 x).
Proof. exact (MK_COMB (@lem1372707) (@lem1372706 x)). Qed.
Lemma lem1372709 : term31 = term84.
Proof. exact (fun_ext (fun x : real => @lem1372708 x)). Qed.
Lemma lem1372710 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372771 : term17 = term85.
Proof. exact (MK_COMB (@lem1372710) (@lem1372709)). Qed.
Lemma lem1372772 (h1 : term17) : term85.
Proof. exact (EQ_MP (@lem1372771) (@lem1372511 h1)). Qed.
Lemma lem1372773 (x : real) (h1 : term58 x) : term58 x.
Proof. exact (h1). Qed.
Lemma lem1372799 (y : real) (x : real) (z : real) : (term70 y x z) = (term70 y x z).
Proof. exact (eq_refl (term70 y x z)). Qed.
Lemma lem1372800 (y : real) (x : real) : (term72 y x) = (term72 y x).
Proof. exact (fun_ext (fun z : real => @lem1372799 y x z)). Qed.
Lemma lem1372801 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372802 (y : real) (x : real) : (term73 y x) = (term73 y x).
Proof. exact (MK_COMB (@lem1372801) (@lem1372800 y x)). Qed.
Lemma lem1372803 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : real => @lem1372802 y x)). Qed.
Lemma lem1372804 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372805 (x : real) : (term75 x) = (term75 x).
Proof. exact (MK_COMB (@lem1372804) (@lem1372803 x)). Qed.
Lemma lem1372806 : term76 = term76.
Proof. exact (fun_ext (fun x : real => @lem1372805 x)). Qed.
Lemma lem1372807 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372808 : term77 = term77.
Proof. exact (MK_COMB (@lem1372807) (@lem1372806)). Qed.
Lemma lem1372809 (h1 : term41) : term77.
Proof. exact (EQ_MP (@lem1372808) (@lem1372682 h1)). Qed.
Lemma lem1372822 (x : real) : ((term32 x) = x) = ((term32 x) = x).
Proof. exact (eq_refl ((term32 x) = x)). Qed.
Lemma lem1372823 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1372822 x)). Qed.
Lemma lem1372824 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372825 : term34 = term34.
Proof. exact (MK_COMB (@lem1372824) (@lem1372823)). Qed.
Lemma lem1372826 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem1372825) (@lem1372695 h1)). Qed.
Lemma lem1372849 (y : real) (x : real) (z : real) : (term78 y x z) = (term78 y x z).
Proof. exact (eq_refl (term78 y x z)). Qed.
Lemma lem1372850 (y : real) (x : real) : (term80 y x) = (term80 y x).
Proof. exact (fun_ext (fun z : real => @lem1372849 y x z)). Qed.
Lemma lem1372851 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372852 (y : real) (x : real) : (term81 y x) = (term81 y x).
Proof. exact (MK_COMB (@lem1372851) (@lem1372850 y x)). Qed.
Lemma lem1372853 (x : real) : (term82 x) = (term82 x).
Proof. exact (fun_ext (fun y : real => @lem1372852 y x)). Qed.
Lemma lem1372854 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372855 (x : real) : (term83 x) = (term83 x).
Proof. exact (MK_COMB (@lem1372854) (@lem1372853 x)). Qed.
Lemma lem1372856 : term84 = term84.
Proof. exact (fun_ext (fun x : real => @lem1372855 x)). Qed.
Lemma lem1372857 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372858 : term85 = term85.
Proof. exact (MK_COMB (@lem1372857) (@lem1372856)). Qed.
Lemma lem1372859 (h1 : term17) : term85.
Proof. exact (EQ_MP (@lem1372858) (@lem1372772 h1)). Qed.
Lemma lem1372899 (x : real) (y : real) (h1 : term47 x y) : term47 x y.
Proof. exact (h1). Qed.
Lemma lem1372901 (x : real) (y : real) (h1 : term47 x y) : term48 x y.
Proof. exact (proj1 (@lem1372899 x y h1)). Qed.
Lemma lem1372917 (y : real) (x : real) (z : real) : (term70 y x z) = (term70 y x z).
Proof. exact (eq_refl (term70 y x z)). Qed.
Lemma lem1372918 (y : real) (x : real) : (term72 y x) = (term72 y x).
Proof. exact (fun_ext (fun z : real => @lem1372917 y x z)). Qed.
Lemma lem1372919 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372920 (y : real) (x : real) : (term73 y x) = (term73 y x).
Proof. exact (MK_COMB (@lem1372919) (@lem1372918 y x)). Qed.
Lemma lem1372921 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : real => @lem1372920 y x)). Qed.
Lemma lem1372922 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372923 (x : real) : (term75 x) = (term75 x).
Proof. exact (MK_COMB (@lem1372922) (@lem1372921 x)). Qed.
Lemma lem1372924 : term76 = term76.
Proof. exact (fun_ext (fun x : real => @lem1372923 x)). Qed.
Lemma lem1372925 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372927 : term77 = term77.
Proof. exact (MK_COMB (@lem1372925) (@lem1372924)). Qed.
Lemma lem1372928 (h1 : term41) : term77.
Proof. exact (EQ_MP (@lem1372927) (@lem1372809 h1)). Qed.
Lemma lem1372930 (x : real) : ((term32 x) = x) = ((term32 x) = x).
Proof. exact (eq_refl ((term32 x) = x)). Qed.
Lemma lem1372931 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1372930 x)). Qed.
Lemma lem1372932 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372934 : term34 = term34.
Proof. exact (MK_COMB (@lem1372932) (@lem1372931)). Qed.
Lemma lem1372935 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem1372934) (@lem1372826 h1)). Qed.
Lemma lem1372943 (y : real) (x : real) (z : real) : (term78 y x z) = (term78 y x z).
Proof. exact (eq_refl (term78 y x z)). Qed.
Lemma lem1372944 (y : real) (x : real) : (term80 y x) = (term80 y x).
Proof. exact (fun_ext (fun z : real => @lem1372943 y x z)). Qed.
Lemma lem1372945 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372946 (y : real) (x : real) : (term81 y x) = (term81 y x).
Proof. exact (MK_COMB (@lem1372945) (@lem1372944 y x)). Qed.
Lemma lem1372947 (x : real) : (term82 x) = (term82 x).
Proof. exact (fun_ext (fun y : real => @lem1372946 y x)). Qed.
Lemma lem1372948 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372949 (x : real) : (term83 x) = (term83 x).
Proof. exact (MK_COMB (@lem1372948) (@lem1372947 x)). Qed.
Lemma lem1372950 : term84 = term84.
Proof. exact (fun_ext (fun x : real => @lem1372949 x)). Qed.
Lemma lem1372951 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1372953 : term85 = term85.
Proof. exact (MK_COMB (@lem1372951) (@lem1372950)). Qed.
Lemma lem1372954 (h1 : term17) : term85.
Proof. exact (EQ_MP (@lem1372953) (@lem1372859 h1)). Qed.
Lemma lem1372967 (_24313 : real) (h1 : term41) : term86 _24313.
Proof. exact (@lem1372928 h1 _24313). Qed.
Lemma lem1372968 (_24313 : real) : (term86 _24313) = (term75 _24313).
Proof. exact (eq_refl (term86 _24313)). Qed.
Lemma lem1372969 (_24313 : real) (h1 : term41) : term75 _24313.
Proof. exact (EQ_MP (@lem1372968 _24313) (@lem1372967 _24313 h1)). Qed.
Lemma lem1372970 (_24313 : real) (_24314 : real) (h1 : term41) : term87 _24313 _24314.
Proof. exact (@lem1372969 _24313 h1 _24314). Qed.
Lemma lem1372971 (_24314 : real) (_24313 : real) : (term87 _24313 _24314) = (term73 _24314 _24313).
Proof. exact (eq_refl (term87 _24313 _24314)). Qed.
Lemma lem1372972 (_24314 : real) (_24313 : real) (h1 : term41) : term73 _24314 _24313.
Proof. exact (EQ_MP (@lem1372971 _24314 _24313) (@lem1372970 _24313 _24314 h1)). Qed.
Lemma lem1372973 (_24314 : real) (_24313 : real) (_24315 : real) (h1 : term41) : term88 _24314 _24313 _24315.
Proof. exact (@lem1372972 _24314 _24313 h1 _24315). Qed.
Lemma lem1372974 (_24314 : real) (_24313 : real) (_24315 : real) : (term88 _24314 _24313 _24315) = (term70 _24314 _24313 _24315).
Proof. exact (eq_refl (term88 _24314 _24313 _24315)). Qed.
Lemma lem1372975 (_24314 : real) (_24313 : real) (_24315 : real) (h1 : term41) : term70 _24314 _24313 _24315.
Proof. exact (EQ_MP (@lem1372974 _24314 _24313 _24315) (@lem1372973 _24314 _24313 _24315 h1)). Qed.
Lemma lem1372976 (_24316 : real) (h1 : term34) : term89 _24316.
Proof. exact (@lem1372935 h1 _24316). Qed.
Lemma lem1372977 (_24316 : real) : (term89 _24316) = ((term32 _24316) = _24316).
Proof. exact (eq_refl (term89 _24316)). Qed.
Lemma lem1372979 (_24317 : real) (h1 : term17) : term90 _24317.
Proof. exact (@lem1372954 h1 _24317). Qed.
Lemma lem1372980 (_24317 : real) : (term90 _24317) = (term83 _24317).
Proof. exact (eq_refl (term90 _24317)). Qed.
Lemma lem1372981 (_24317 : real) (h1 : term17) : term83 _24317.
Proof. exact (EQ_MP (@lem1372980 _24317) (@lem1372979 _24317 h1)). Qed.
Lemma lem1372982 (_24317 : real) (_24318 : real) (h1 : term17) : term91 _24317 _24318.
Proof. exact (@lem1372981 _24317 h1 _24318). Qed.
Lemma lem1372983 (_24318 : real) (_24317 : real) : (term91 _24317 _24318) = (term81 _24318 _24317).
Proof. exact (eq_refl (term91 _24317 _24318)). Qed.
Lemma lem1372984 (_24318 : real) (_24317 : real) (h1 : term17) : term81 _24318 _24317.
Proof. exact (EQ_MP (@lem1372983 _24318 _24317) (@lem1372982 _24317 _24318 h1)). Qed.
Lemma lem1372985 (_24318 : real) (_24317 : real) (_24319 : real) (h1 : term17) : term92 _24318 _24317 _24319.
Proof. exact (@lem1372984 _24318 _24317 h1 _24319). Qed.
Lemma lem1372986 (_24318 : real) (_24317 : real) (_24319 : real) : (term92 _24318 _24317 _24319) = (term78 _24318 _24317 _24319).
Proof. exact (eq_refl (term92 _24318 _24317 _24319)). Qed.
Lemma lem1372998 (_24314 : real) (_24313 : real) (_24315 : real) : (term70 _24314 _24313 _24315) = (term93 _24314 _24313 _24315).
Proof. exact (@lem1372278 (term94 _24313 _24314) (term94 _24314 _24315) (real_le _24313 _24315)). Qed.
Lemma lem1372999 (_24314 : real) (_24313 : real) (_24315 : real) (h1 : term41) : term93 _24314 _24313 _24315.
Proof. exact (EQ_MP (@lem1372998 _24314 _24313 _24315) (@lem1372975 _24314 _24313 _24315 h1)). Qed.
Lemma lem1373007 (_24318 : real) (_24317 : real) (_24319 : real) (h1 : term17) : term78 _24318 _24317 _24319.
Proof. exact (EQ_MP (@lem1372986 _24318 _24317 _24319) (@lem1372985 _24318 _24317 _24319 h1)). Qed.
Lemma lem1373009 (x : real) (y : real) (h1 : term47 x y) : term95 x y.
Proof. exact (proj2 (@lem1372899 x y h1)). Qed.
Lemma lem1373014 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1373015 (_24320 : real) (_24322 : real) (h1 : _24320 = _24322) : _24320 = _24322.
Proof. exact (h1). Qed.
Lemma lem1373016 (_24321 : real) (_24323 : real) (h1 : _24321 = _24323) : _24321 = _24323.
Proof. exact (h1). Qed.
Lemma lem1373017 (_24320 : real) (_24322 : real) (h1 : _24320 = _24322) : (real_le _24320) = (real_le _24322).
Proof. exact (MK_COMB (@lem1373014) (@lem1373015 _24320 _24322 h1)). Qed.
Lemma lem1373018 (_24320 : real) (_24322 : real) (_24321 : real) (_24323 : real) (h1 : _24320 = _24322) (h2 : _24321 = _24323) : (real_le _24320 _24321) = (real_le _24322 _24323).
Proof. exact (MK_COMB (@lem1373017 _24320 _24322 h1) (@lem1373016 _24321 _24323 h2)). Qed.
Lemma lem1373020 (b : Prop) (a : Prop) : term96 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1373021 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : term97 _24322 _24323 _24320 _24321.
Proof. exact (@lem1373020 (real_le _24322 _24323) (real_le _24320 _24321)). Qed.
Lemma lem1373022 (_24320 : real) (_24322 : real) (_24321 : real) (_24323 : real) (h1 : _24320 = _24322) (h2 : _24321 = _24323) : term98 _24322 _24323 _24320 _24321.
Proof. exact (@lem1373021 _24322 _24323 _24320 _24321 (@lem1373018 _24320 _24322 _24321 _24323 h1 h2)). Qed.
Lemma lem1373023 (_24323 : real) (_24321 : real) (_24320 : real) (_24322 : real) (h1 : _24320 = _24322) : term99 _24322 _24323 _24320 _24321.
Proof. exact (fun h0 : _24321 = _24323 => @lem1373022 _24320 _24322 _24321 _24323 h1 h0). Qed.
Lemma lem1373025 (a : Prop) (b : Prop) : (a -> b) = (term100 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1373026 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : (term99 _24322 _24323 _24320 _24321) = (term101 _24322 _24323 _24320 _24321).
Proof. exact (@lem1373025 (_24321 = _24323) (term98 _24322 _24323 _24320 _24321)). Qed.
Lemma lem1373027 (_24323 : real) (_24321 : real) (_24320 : real) (_24322 : real) (h1 : _24320 = _24322) : term101 _24322 _24323 _24320 _24321.
Proof. exact (EQ_MP (@lem1373026 _24322 _24323 _24320 _24321) (@lem1373023 _24323 _24321 _24320 _24322 h1)). Qed.
Lemma lem1373028 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : term102 _24322 _24323 _24320 _24321.
Proof. exact (fun h0 : _24320 = _24322 => @lem1373027 _24323 _24321 _24320 _24322 h0). Qed.
Lemma lem1373030 (a : Prop) (b : Prop) : (a -> b) = (term100 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1373031 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : (term102 _24322 _24323 _24320 _24321) = (term103 _24322 _24323 _24320 _24321).
Proof. exact (@lem1373030 (_24320 = _24322) (term101 _24322 _24323 _24320 _24321)). Qed.
Lemma lem1373032 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : term103 _24322 _24323 _24320 _24321.
Proof. exact (EQ_MP (@lem1373031 _24322 _24323 _24320 _24321) (@lem1373028 _24322 _24323 _24320 _24321)). Qed.
Lemma lem1373069 (x : real) (y : real) (h1 : term47 x y) : term104 x.
Proof. exact (proj1 (@lem1372901 x y h1)). Qed.
Lemma lem1373070 (x : real) (y : real) (h1 : term47 x y) : term105 x.
Proof. exact (fun h0 : term106 x => @lem1373069 x y h1). Qed.
Lemma lem1373072 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1373073 (x : real) : (term105 x) = (term104 x).
Proof. exact (@lem1373072 (term104 x)). Qed.
Lemma lem1373074 (x : real) (y : real) (h1 : term47 x y) : term104 x.
Proof. exact (EQ_MP (@lem1373073 x) (@lem1373070 x y h1)). Qed.
Lemma lem1373076 (_24316 : real) (h1 : term34) : (term32 _24316) = _24316.
Proof. exact (EQ_MP (@lem1372977 _24316) (@lem1372976 _24316 h1)). Qed.
Lemma lem1373077 (x : real) (h1 : term34) : (term32 x) = x.
Proof. exact (@lem1373076 x h1). Qed.
Lemma lem1373078 (x : real) (h1 : term34) : term108 x.
Proof. exact (fun h0 : term109 x => @lem1373077 x h1). Qed.
Lemma lem1373080 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1373081 (x : real) : (term108 x) = ((term32 x) = x).
Proof. exact (@lem1373080 ((term32 x) = x)). Qed.
Lemma lem1373082 (x : real) (h1 : term34) : (term32 x) = x.
Proof. exact (EQ_MP (@lem1373081 x) (@lem1373078 x h1)). Qed.
Lemma lem1373084 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1373085 (x : real) (y : real) : (real_add x y) = (real_add x y).
Proof. exact (@lem1373084 (real_add x y)). Qed.
Lemma lem1373086 (x : real) (y : real) : term110 x y.
Proof. exact (fun h0 : term111 x y => @lem1373085 x y). Qed.
Lemma lem1373088 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1373089 (x : real) (y : real) : (term110 x y) = ((real_add x y) = (real_add x y)).
Proof. exact (@lem1373088 ((real_add x y) = (real_add x y))). Qed.
Lemma lem1373090 (x : real) (y : real) : (real_add x y) = (real_add x y).
Proof. exact (EQ_MP (@lem1373089 x y) (@lem1373086 x y)). Qed.
Lemma lem1373092 (x : real) (y : real) (h1 : term47 x y) : term104 y.
Proof. exact (proj2 (@lem1372901 x y h1)). Qed.
Lemma lem1373093 (x : real) (y : real) (h1 : term47 x y) : term105 y.
Proof. exact (fun h0 : term106 y => @lem1373092 x y h1). Qed.
Lemma lem1373095 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1373096 (y : real) : (term105 y) = (term104 y).
Proof. exact (@lem1373095 (term104 y)). Qed.
Lemma lem1373097 (x : real) (y : real) (h1 : term47 x y) : term104 y.
Proof. exact (EQ_MP (@lem1373096 y) (@lem1373093 x y h1)). Qed.
Lemma lem1373103 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1373104 (_24317 : real) (_24318 : real) (_24319 : real) : (term78 _24318 _24317 _24319) = (term112 _24317 _24318 _24319).
Proof. exact (@lem1373103 (term79 _24318 _24317 _24319) (term94 _24318 _24319)). Qed.
Lemma lem1373110 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1373111 (_24317 : real) (_24318 : real) (_24319 : real) : (term113 _24318 _24317 _24319) = (term114 _24317 _24318 _24319).
Proof. exact (MK_COMB (@lem1373110) (@lem1373104 _24317 _24318 _24319)). Qed.
Lemma lem1373117 (_24317 : real) (_24318 : real) (_24319 : real) : (term112 _24317 _24318 _24319) = (term112 _24317 _24318 _24319).
Proof. exact (eq_refl (term112 _24317 _24318 _24319)). Qed.
Lemma lem1373118 (_24317 : real) (_24318 : real) (_24319 : real) : ((term78 _24318 _24317 _24319) = (term112 _24317 _24318 _24319)) = ((term112 _24317 _24318 _24319) = (term112 _24317 _24318 _24319)).
Proof. exact (MK_COMB (@lem1373111 _24317 _24318 _24319) (@lem1373117 _24317 _24318 _24319)). Qed.
Lemma lem1373120 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1373121 (x : Prop) : (x = x) = True.
Proof. exact (@lem1373120 Prop x). Qed.
Lemma lem1373122 (_24317 : real) (_24318 : real) (_24319 : real) : ((term112 _24317 _24318 _24319) = (term112 _24317 _24318 _24319)) = True.
Proof. exact (@lem1373121 (term112 _24317 _24318 _24319)). Qed.
Lemma lem1373123 (_24317 : real) (_24318 : real) (_24319 : real) : ((term78 _24318 _24317 _24319) = (term112 _24317 _24318 _24319)) = True.
Proof. exact (TRANS (@lem1373118 _24317 _24318 _24319) (@lem1373122 _24317 _24318 _24319)). Qed.
Lemma lem1373124 (_24317 : real) (_24318 : real) (_24319 : real) : True = ((term78 _24318 _24317 _24319) = (term112 _24317 _24318 _24319)).
Proof. exact (SYM (@lem1373123 _24317 _24318 _24319)). Qed.
Lemma lem1373125 (_24317 : real) (_24318 : real) (_24319 : real) : (term78 _24318 _24317 _24319) = (term112 _24317 _24318 _24319).
Proof. exact (EQ_MP (@lem1373124 _24317 _24318 _24319) (@lem0)). Qed.
Lemma lem1373126 (_24317 : real) (_24318 : real) (_24319 : real) (h1 : term17) : term112 _24317 _24318 _24319.
Proof. exact (EQ_MP (@lem1373125 _24317 _24318 _24319) (@lem1373007 _24318 _24317 _24319 h1)). Qed.
Lemma lem1373128 (b : Prop) (a : Prop) : (a \/ b) = (term115 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1373129 (_24318 : real) (_24317 : real) (_24319 : real) : (term112 _24317 _24318 _24319) = (term116 _24318 _24317 _24319).
Proof. exact (@lem1373128 (term94 _24318 _24319) (term79 _24318 _24317 _24319)). Qed.
Lemma lem1373131 (a : Prop) : (term117 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1373132 (_24318 : real) (_24319 : real) : (term118 _24318 _24319) = (real_le _24318 _24319).
Proof. exact (@lem1373131 (real_le _24318 _24319)). Qed.
Lemma lem1373133 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1373134 (_24318 : real) (_24319 : real) : (term119 _24318 _24319) = (term120 _24318 _24319).
Proof. exact (MK_COMB (@lem1373133) (@lem1373132 _24318 _24319)). Qed.
Lemma lem1373135 (_24318 : real) (_24317 : real) (_24319 : real) : (term79 _24318 _24317 _24319) = (term79 _24318 _24317 _24319).
Proof. exact (eq_refl (term79 _24318 _24317 _24319)). Qed.
Lemma lem1373136 (_24318 : real) (_24317 : real) (_24319 : real) : (term116 _24318 _24317 _24319) = (term26 _24318 _24317 _24319).
Proof. exact (MK_COMB (@lem1373134 _24318 _24319) (@lem1373135 _24318 _24317 _24319)). Qed.
Lemma lem1373137 (_24318 : real) (_24317 : real) (_24319 : real) : (term112 _24317 _24318 _24319) = (term26 _24318 _24317 _24319).
Proof. exact (TRANS (@lem1373129 _24318 _24317 _24319) (@lem1373136 _24318 _24317 _24319)). Qed.
Lemma lem1373140 (_24318 : real) (_24317 : real) (_24319 : real) (h1 : term17) : term26 _24318 _24317 _24319.
Proof. exact (EQ_MP (@lem1373137 _24318 _24317 _24319) (@lem1373126 _24317 _24318 _24319 h1)). Qed.
Lemma lem1373141 (_24317 : real) (y : real) (h1 : term17) : term121 _24317 y.
Proof. exact (@lem1373140 term122 _24317 y h1). Qed.
Lemma lem1373144 (_24317 : real) (x : real) (y : real) (h1 : term17) (h2 : term47 x y) : term123 _24317 y.
Proof. exact (@lem1373141 _24317 y h1 (@lem1373097 x y h2)). Qed.
Lemma lem1373145 (x : real) (y : real) (h1 : term17) (h2 : term47 x y) : term123 x y.
Proof. exact (@lem1373144 x x y h1 h2). Qed.
Lemma lem1373146 (x : real) (y : real) (h1 : term17) (h2 : term47 x y) : term124 x y.
Proof. exact (fun h0 : term125 x y => @lem1373145 x y h1 h2). Qed.
Lemma lem1373148 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1373149 (x : real) (y : real) : (term124 x y) = (term123 x y).
Proof. exact (@lem1373148 (term123 x y)). Qed.
Lemma lem1373150 (x : real) (y : real) (h1 : term17) (h2 : term47 x y) : term123 x y.
Proof. exact (EQ_MP (@lem1373149 x y) (@lem1373146 x y h1 h2)). Qed.
Lemma lem1373168 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1373169 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : (term101 _24322 _24323 _24320 _24321) = (term126 _24322 _24323 _24320 _24321).
Proof. exact (@lem1373168 (real_le _24322 _24323) (term127 _24321 _24323) (term94 _24320 _24321)). Qed.
Lemma lem1373187 (_24320 : real) (_24322 : real) : (term128 _24320 _24322) = (term128 _24320 _24322).
Proof. exact (eq_refl (term128 _24320 _24322)). Qed.
Lemma lem1373188 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : (term103 _24322 _24323 _24320 _24321) = (term129 _24322 _24323 _24320 _24321).
Proof. exact (MK_COMB (@lem1373187 _24320 _24322) (@lem1373169 _24322 _24323 _24320 _24321)). Qed.
Lemma lem1373192 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1373193 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : (term129 _24322 _24323 _24320 _24321) = (term130 _24322 _24323 _24320 _24321).
Proof. exact (@lem1373192 (real_le _24322 _24323) (term127 _24320 _24322) (term131 _24323 _24320 _24321)). Qed.
Lemma lem1373223 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : (term103 _24322 _24323 _24320 _24321) = (term130 _24322 _24323 _24320 _24321).
Proof. exact (TRANS (@lem1373188 _24322 _24323 _24320 _24321) (@lem1373193 _24322 _24323 _24320 _24321)). Qed.
Lemma lem1373224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1373225 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : (term132 _24322 _24323 _24320 _24321) = (term133 _24322 _24323 _24320 _24321).
Proof. exact (MK_COMB (@lem1373224) (@lem1373223 _24322 _24323 _24320 _24321)). Qed.
Lemma lem1373255 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : (term130 _24322 _24323 _24320 _24321) = (term130 _24322 _24323 _24320 _24321).
Proof. exact (eq_refl (term130 _24322 _24323 _24320 _24321)). Qed.
Lemma lem1373256 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : ((term103 _24322 _24323 _24320 _24321) = (term130 _24322 _24323 _24320 _24321)) = ((term130 _24322 _24323 _24320 _24321) = (term130 _24322 _24323 _24320 _24321)).
Proof. exact (MK_COMB (@lem1373225 _24322 _24323 _24320 _24321) (@lem1373255 _24322 _24323 _24320 _24321)). Qed.
Lemma lem1373258 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1373259 (x : Prop) : (x = x) = True.
Proof. exact (@lem1373258 Prop x). Qed.
Lemma lem1373260 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : ((term130 _24322 _24323 _24320 _24321) = (term130 _24322 _24323 _24320 _24321)) = True.
Proof. exact (@lem1373259 (term130 _24322 _24323 _24320 _24321)). Qed.
Lemma lem1373261 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : ((term103 _24322 _24323 _24320 _24321) = (term130 _24322 _24323 _24320 _24321)) = True.
Proof. exact (TRANS (@lem1373256 _24322 _24323 _24320 _24321) (@lem1373260 _24322 _24323 _24320 _24321)). Qed.
Lemma lem1373262 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : True = ((term103 _24322 _24323 _24320 _24321) = (term130 _24322 _24323 _24320 _24321)).
Proof. exact (SYM (@lem1373261 _24322 _24323 _24320 _24321)). Qed.
Lemma lem1373263 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : (term103 _24322 _24323 _24320 _24321) = (term130 _24322 _24323 _24320 _24321).
Proof. exact (EQ_MP (@lem1373262 _24322 _24323 _24320 _24321) (@lem0)). Qed.
Lemma lem1373264 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : term130 _24322 _24323 _24320 _24321.
Proof. exact (EQ_MP (@lem1373263 _24322 _24323 _24320 _24321) (@lem1373032 _24322 _24323 _24320 _24321)). Qed.
Lemma lem1373266 (b : Prop) (a : Prop) : (a \/ b) = (term115 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1373267 (_24320 : real) (_24321 : real) (_24322 : real) (_24323 : real) : (term130 _24322 _24323 _24320 _24321) = (term134 _24320 _24321 _24322 _24323).
Proof. exact (@lem1373266 (term135 _24322 _24323 _24320 _24321) (real_le _24322 _24323)). Qed.
Lemma lem1373269 (a : Prop) (b : Prop) : (term136 a b) = (term137 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1373270 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : (term138 _24322 _24323 _24320 _24321) = (term139 _24322 _24323 _24320 _24321).
Proof. exact (@lem1373269 (term127 _24320 _24322) (term131 _24323 _24320 _24321)). Qed.
Lemma lem1373272 (a : Prop) : (term117 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1373273 (_24320 : real) (_24322 : real) : (term140 _24320 _24322) = (_24320 = _24322).
Proof. exact (@lem1373272 (_24320 = _24322)). Qed.
Lemma lem1373274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1373275 (_24320 : real) (_24322 : real) : (term141 _24320 _24322) = (term142 _24320 _24322).
Proof. exact (MK_COMB (@lem1373274) (@lem1373273 _24320 _24322)). Qed.
Lemma lem1373277 (a : Prop) (b : Prop) : (term136 a b) = (term137 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1373278 (_24323 : real) (_24320 : real) (_24321 : real) : (term143 _24323 _24320 _24321) = (term144 _24323 _24320 _24321).
Proof. exact (@lem1373277 (term127 _24321 _24323) (term94 _24320 _24321)). Qed.
Lemma lem1373280 (a : Prop) : (term117 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1373281 (_24321 : real) (_24323 : real) : (term140 _24321 _24323) = (_24321 = _24323).
Proof. exact (@lem1373280 (_24321 = _24323)). Qed.
Lemma lem1373282 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1373283 (_24321 : real) (_24323 : real) : (term141 _24321 _24323) = (term142 _24321 _24323).
Proof. exact (MK_COMB (@lem1373282) (@lem1373281 _24321 _24323)). Qed.
Lemma lem1373285 (a : Prop) : (term117 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1373286 (_24320 : real) (_24321 : real) : (term118 _24320 _24321) = (real_le _24320 _24321).
Proof. exact (@lem1373285 (real_le _24320 _24321)). Qed.
Lemma lem1373287 (_24323 : real) (_24320 : real) (_24321 : real) : (term144 _24323 _24320 _24321) = (term145 _24323 _24320 _24321).
Proof. exact (MK_COMB (@lem1373283 _24321 _24323) (@lem1373286 _24320 _24321)). Qed.
Lemma lem1373288 (_24323 : real) (_24320 : real) (_24321 : real) : (term143 _24323 _24320 _24321) = (term145 _24323 _24320 _24321).
Proof. exact (TRANS (@lem1373278 _24323 _24320 _24321) (@lem1373287 _24323 _24320 _24321)). Qed.
Lemma lem1373289 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : (term139 _24322 _24323 _24320 _24321) = (term146 _24322 _24323 _24320 _24321).
Proof. exact (MK_COMB (@lem1373275 _24320 _24322) (@lem1373288 _24323 _24320 _24321)). Qed.
Lemma lem1373290 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : (term138 _24322 _24323 _24320 _24321) = (term146 _24322 _24323 _24320 _24321).
Proof. exact (TRANS (@lem1373270 _24322 _24323 _24320 _24321) (@lem1373289 _24322 _24323 _24320 _24321)). Qed.
Lemma lem1373291 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1373292 (_24322 : real) (_24323 : real) (_24320 : real) (_24321 : real) : (term147 _24322 _24323 _24320 _24321) = (term148 _24322 _24323 _24320 _24321).
Proof. exact (MK_COMB (@lem1373291) (@lem1373290 _24322 _24323 _24320 _24321)). Qed.
Lemma lem1373293 (_24322 : real) (_24323 : real) : (real_le _24322 _24323) = (real_le _24322 _24323).
Proof. exact (eq_refl (real_le _24322 _24323)). Qed.
Lemma lem1373294 (_24320 : real) (_24321 : real) (_24322 : real) (_24323 : real) : (term134 _24320 _24321 _24322 _24323) = (term149 _24320 _24321 _24322 _24323).
Proof. exact (MK_COMB (@lem1373292 _24322 _24323 _24320 _24321) (@lem1373293 _24322 _24323)). Qed.
Lemma lem1373295 (_24320 : real) (_24321 : real) (_24322 : real) (_24323 : real) : (term130 _24322 _24323 _24320 _24321) = (term149 _24320 _24321 _24322 _24323).
Proof. exact (TRANS (@lem1373267 _24320 _24321 _24322 _24323) (@lem1373294 _24320 _24321 _24322 _24323)). Qed.
Lemma lem1373297 (x : real) (y : real) (h1 : term17) (h2 : term47 x y) : term150 x y.
Proof. exact (conj (@lem1373090 x y) (@lem1373150 x y h1 h2)). Qed.
Lemma lem1373298 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term47 x y) : term151 x y.
Proof. exact (conj (@lem1373082 x h2) (@lem1373297 x y h1 h3)). Qed.
Lemma lem1373300 (_24320 : real) (_24321 : real) (_24322 : real) (_24323 : real) : term149 _24320 _24321 _24322 _24323.
Proof. exact (EQ_MP (@lem1373295 _24320 _24321 _24322 _24323) (@lem1373264 _24322 _24323 _24320 _24321)). Qed.
Lemma lem1373301 (x : real) (y : real) : term152 x y.
Proof. exact (@lem1373300 (term32 x) (real_add x y) x (real_add x y)). Qed.
Lemma lem1373304 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term47 x y) : term153 x y.
Proof. exact (@lem1373301 x y (@lem1373298 x y h1 h2 h3)). Qed.
Lemma lem1373305 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term47 x y) : term154 x y.
Proof. exact (fun h0 : term155 x y => @lem1373304 x y h1 h2 h3). Qed.
Lemma lem1373307 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1373308 (x : real) (y : real) : (term154 x y) = (term153 x y).
Proof. exact (@lem1373307 (term153 x y)). Qed.
Lemma lem1373309 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term47 x y) : term153 x y.
Proof. exact (EQ_MP (@lem1373308 x y) (@lem1373305 x y h1 h2 h3)). Qed.
Lemma lem1373325 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1373326 (_24313 : real) (_24314 : real) (_24315 : real) : (term156 _24314 _24313 _24315) = (term157 _24313 _24314 _24315).
Proof. exact (@lem1373325 (real_le _24313 _24315) (term94 _24314 _24315)). Qed.
Lemma lem1373332 (_24313 : real) (_24314 : real) : (term158 _24313 _24314) = (term158 _24313 _24314).
Proof. exact (eq_refl (term158 _24313 _24314)). Qed.
Lemma lem1373333 (_24313 : real) (_24314 : real) (_24315 : real) : (term93 _24314 _24313 _24315) = (term159 _24313 _24314 _24315).
Proof. exact (MK_COMB (@lem1373332 _24313 _24314) (@lem1373326 _24313 _24314 _24315)). Qed.
Lemma lem1373337 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1373338 (_24313 : real) (_24314 : real) (_24315 : real) : (term159 _24313 _24314 _24315) = (term160 _24313 _24314 _24315).
Proof. exact (@lem1373337 (real_le _24313 _24315) (term94 _24313 _24314) (term94 _24314 _24315)). Qed.
Lemma lem1373354 (_24313 : real) (_24314 : real) (_24315 : real) : (term93 _24314 _24313 _24315) = (term160 _24313 _24314 _24315).
Proof. exact (TRANS (@lem1373333 _24313 _24314 _24315) (@lem1373338 _24313 _24314 _24315)). Qed.
Lemma lem1373355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1373356 (_24313 : real) (_24314 : real) (_24315 : real) : (term161 _24314 _24313 _24315) = (term162 _24313 _24314 _24315).
Proof. exact (MK_COMB (@lem1373355) (@lem1373354 _24313 _24314 _24315)). Qed.
Lemma lem1373372 (_24313 : real) (_24314 : real) (_24315 : real) : (term160 _24313 _24314 _24315) = (term160 _24313 _24314 _24315).
Proof. exact (eq_refl (term160 _24313 _24314 _24315)). Qed.
Lemma lem1373373 (_24313 : real) (_24314 : real) (_24315 : real) : ((term93 _24314 _24313 _24315) = (term160 _24313 _24314 _24315)) = ((term160 _24313 _24314 _24315) = (term160 _24313 _24314 _24315)).
Proof. exact (MK_COMB (@lem1373356 _24313 _24314 _24315) (@lem1373372 _24313 _24314 _24315)). Qed.
Lemma lem1373375 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1373376 (x : Prop) : (x = x) = True.
Proof. exact (@lem1373375 Prop x). Qed.
Lemma lem1373377 (_24313 : real) (_24314 : real) (_24315 : real) : ((term160 _24313 _24314 _24315) = (term160 _24313 _24314 _24315)) = True.
Proof. exact (@lem1373376 (term160 _24313 _24314 _24315)). Qed.
Lemma lem1373378 (_24313 : real) (_24314 : real) (_24315 : real) : ((term93 _24314 _24313 _24315) = (term160 _24313 _24314 _24315)) = True.
Proof. exact (TRANS (@lem1373373 _24313 _24314 _24315) (@lem1373377 _24313 _24314 _24315)). Qed.
Lemma lem1373379 (_24313 : real) (_24314 : real) (_24315 : real) : True = ((term93 _24314 _24313 _24315) = (term160 _24313 _24314 _24315)).
Proof. exact (SYM (@lem1373378 _24313 _24314 _24315)). Qed.
Lemma lem1373380 (_24313 : real) (_24314 : real) (_24315 : real) : (term93 _24314 _24313 _24315) = (term160 _24313 _24314 _24315).
Proof. exact (EQ_MP (@lem1373379 _24313 _24314 _24315) (@lem0)). Qed.
Lemma lem1373381 (_24313 : real) (_24314 : real) (_24315 : real) (h1 : term41) : term160 _24313 _24314 _24315.
Proof. exact (EQ_MP (@lem1373380 _24313 _24314 _24315) (@lem1372999 _24314 _24313 _24315 h1)). Qed.
Lemma lem1373383 (b : Prop) (a : Prop) : (a \/ b) = (term115 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1373384 (_24314 : real) (_24313 : real) (_24315 : real) : (term160 _24313 _24314 _24315) = (term163 _24314 _24313 _24315).
Proof. exact (@lem1373383 (term66 _24313 _24314 _24315) (real_le _24313 _24315)). Qed.
Lemma lem1373386 (a : Prop) (b : Prop) : (term136 a b) = (term137 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1373387 (_24313 : real) (_24314 : real) (_24315 : real) : (term164 _24313 _24314 _24315) = (term165 _24313 _24314 _24315).
Proof. exact (@lem1373386 (term94 _24313 _24314) (term94 _24314 _24315)). Qed.
Lemma lem1373389 (a : Prop) : (term117 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1373390 (_24313 : real) (_24314 : real) : (term118 _24313 _24314) = (real_le _24313 _24314).
Proof. exact (@lem1373389 (real_le _24313 _24314)). Qed.
Lemma lem1373391 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1373392 (_24313 : real) (_24314 : real) : (term166 _24313 _24314) = (term167 _24313 _24314).
Proof. exact (MK_COMB (@lem1373391) (@lem1373390 _24313 _24314)). Qed.
Lemma lem1373394 (a : Prop) : (term117 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1373395 (_24314 : real) (_24315 : real) : (term118 _24314 _24315) = (real_le _24314 _24315).
Proof. exact (@lem1373394 (real_le _24314 _24315)). Qed.
Lemma lem1373396 (_24313 : real) (_24314 : real) (_24315 : real) : (term165 _24313 _24314 _24315) = (term71 _24313 _24314 _24315).
Proof. exact (MK_COMB (@lem1373392 _24313 _24314) (@lem1373395 _24314 _24315)). Qed.
Lemma lem1373397 (_24313 : real) (_24314 : real) (_24315 : real) : (term164 _24313 _24314 _24315) = (term71 _24313 _24314 _24315).
Proof. exact (TRANS (@lem1373387 _24313 _24314 _24315) (@lem1373396 _24313 _24314 _24315)). Qed.
Lemma lem1373398 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1373399 (_24313 : real) (_24314 : real) (_24315 : real) : (term168 _24313 _24314 _24315) = (term169 _24313 _24314 _24315).
Proof. exact (MK_COMB (@lem1373398) (@lem1373397 _24313 _24314 _24315)). Qed.
Lemma lem1373400 (_24313 : real) (_24315 : real) : (real_le _24313 _24315) = (real_le _24313 _24315).
Proof. exact (eq_refl (real_le _24313 _24315)). Qed.
Lemma lem1373401 (_24314 : real) (_24313 : real) (_24315 : real) : (term163 _24314 _24313 _24315) = (term35 _24314 _24313 _24315).
Proof. exact (MK_COMB (@lem1373399 _24313 _24314 _24315) (@lem1373400 _24313 _24315)). Qed.
Lemma lem1373402 (_24314 : real) (_24313 : real) (_24315 : real) : (term160 _24313 _24314 _24315) = (term35 _24314 _24313 _24315).
Proof. exact (TRANS (@lem1373384 _24314 _24313 _24315) (@lem1373401 _24314 _24313 _24315)). Qed.
Lemma lem1373404 (x : real) (y : real) (h1 : term17) (h2 : term34) (h3 : term47 x y) : term170 x y.
Proof. exact (conj (@lem1373074 x y h3) (@lem1373309 x y h1 h2 h3)). Qed.
Lemma lem1373406 (_24314 : real) (_24313 : real) (_24315 : real) (h1 : term41) : term35 _24314 _24313 _24315.
Proof. exact (EQ_MP (@lem1373402 _24314 _24313 _24315) (@lem1373381 _24313 _24314 _24315 h1)). Qed.
Lemma lem1373407 (x : real) (y : real) (h1 : term41) : term171 x y.
Proof. exact (@lem1373406 x term122 (real_add x y) h1). Qed.
Lemma lem1373410 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : term49 x y.
Proof. exact (@lem1373407 x y h1 (@lem1373404 x y h2 h3 h4)). Qed.
Lemma lem1373411 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : term172 x y.
Proof. exact (fun h0 : term95 x y => @lem1373410 x y h1 h2 h3 h4). Qed.
Lemma lem1373413 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1373414 (x : real) (y : real) : (term172 x y) = (term49 x y).
Proof. exact (@lem1373413 (term49 x y)). Qed.
Lemma lem1373415 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : term49 x y.
Proof. exact (EQ_MP (@lem1373414 x y) (@lem1373411 x y h1 h2 h3 h4)). Qed.
Lemma lem1373418 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1373420 (x : real) (y : real) : (term95 x y) = (term173 x y).
Proof. exact (@lem1373418 (term49 x y)). Qed.
Lemma lem1373423 (x : real) (y : real) (h1 : term47 x y) : term173 x y.
Proof. exact (EQ_MP (@lem1373420 x y) (@lem1373009 x y h1)). Qed.
Lemma lem1373426 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : False.
Proof. exact (@lem1373423 x y h4 (@lem1373415 x y h1 h2 h3 h4)). Qed.
Lemma lem1373427 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : term174.
Proof. exact (fun h0 : ~ False => @lem1373426 x y h1 h2 h3 h4). Qed.
Lemma lem1373429 (p : Prop) : (term107 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1373430 : term174 = False.
Proof. exact (@lem1373429 False). Qed.
Lemma lem1373431 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : False.
Proof. exact (EQ_MP (@lem1373430) (@lem1373427 x y h1 h2 h3 h4)). Qed.
Lemma lem1373432 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : term34 = False.
Proof. exact (prop_ext (fun h5 : term34 => @lem1373431 x y h1 h2 h3 h4) (fun h5 : False => @lem1372935 h3)). Qed.
Lemma lem1373433 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : False.
Proof. exact (EQ_MP (@lem1373432 x y h1 h2 h3 h4) (@lem1372935 h3)). Qed.
Lemma lem1373434 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : (term47 x y) = False.
Proof. exact (prop_ext (fun h5 : term47 x y => @lem1373433 x y h1 h2 h3 h4) (fun h5 : False => @lem1372899 x y h4)). Qed.
Lemma lem1373435 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : False.
Proof. exact (EQ_MP (@lem1373434 x y h1 h2 h3 h4) (@lem1372899 x y h4)). Qed.
Lemma lem1373436 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : term34 = False.
Proof. exact (prop_ext (fun h5 : term34 => @lem1373435 x y h1 h2 h3 h4) (fun h5 : False => @lem1372826 h3)). Qed.
Lemma lem1373437 (x : real) (y : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term47 x y) : False.
Proof. exact (EQ_MP (@lem1373436 x y h1 h2 h3 h4) (@lem1372826 h3)). Qed.
Lemma lem1373438 (x : real) (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term58 x) : False.
Proof. exact (ex_elim (@lem1372773 x h4) (fun y : real => fun h0 : term57 x y => @lem1373437 x y h1 h2 h3 h0)). Qed.
Lemma lem1373439 (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term10) : False.
Proof. exact (ex_elim (@lem1372599 h4) (fun x : real => fun h0 : term63 x => @lem1373438 x h1 h2 h3 h0)). Qed.
Lemma lem1373440 (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term10) : term34 = False.
Proof. exact (prop_ext (fun h5 : term34 => @lem1373439 h1 h2 h3 h4) (fun h5 : False => @lem1372695 h3)). Qed.
Lemma lem1373441 (h1 : term41) (h2 : term17) (h3 : term34) (h4 : term10) : False.
Proof. exact (EQ_MP (@lem1373440 h1 h2 h3 h4) (@lem1372695 h3)). Qed.
Lemma lem1373442 (h1 : term41) (h2 : term34) (h3 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1373441 h1 h0 h2 h3). Qed.
Lemma lem1373443 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1373444 (h1 : term41) (h2 : term34) (h3 : term10) : term16.
Proof. exact (EQ_MP (@lem1373443) (@lem1373442 h1 h2 h3)). Qed.
Lemma lem1373445 (h1 : term41) (h2 : term10) : term20.
Proof. exact (fun h0 : term34 => @lem1373444 h1 h0 h2). Qed.
Lemma lem1373446 (h1 : term10) : term23.
Proof. exact (fun h0 : term41 => @lem1373445 h0 h1). Qed.
Lemma lem1373447 : term25.
Proof. exact (fun h0 : term10 => @lem1373446 h0). Qed.
Lemma lem1373448 : term11.
Proof. exact (EQ_MP (@lem1372507) (@lem1373447)). Qed.
Lemma lem1373450 : term11.
Proof. exact (@lem1372298 (@lem1373448)). Qed.
Lemma lem1373451 (h1 : term10) : term22.
Proof. exact (@lem1373450 (@lem1372283 h1)). Qed.
Lemma lem1373452 (h1 : term10) : term19.
Proof. exact (@lem1373451 h1 (@lem1339577)). Qed.
Lemma lem1373453 (h1 : term10) : term15.
Proof. exact (@lem1373452 h1 (@lem1361590)). Qed.
Lemma lem1373454 (h1 : term10) : False.
Proof. exact (@lem1373453 h1 (@lem1339889)). Qed.
Lemma lem1373455 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1373454 h1) (fun h2 : False => @lem1372283 h1)). Qed.
Lemma lem1373456 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1373455 h1) (@lem1372283 h1)). Qed.
Lemma lem1373457 : term9.
Proof. exact (fun h0 : term10 => @lem1373456 h0). Qed.
Lemma lem1373458 : term8.
Proof. exact (EQ_MP (@lem1372282) (@lem1373457)). Qed.
