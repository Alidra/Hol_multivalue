Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_SUP_FINITE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SUP_FINITE_spec.
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
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19490_spec.
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
Lemma lem5145275 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5145276 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5145277 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5145276 t1) (@lem5145275 t1)). Qed.
Lemma lem5145278 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5145277 t1 t2). Qed.
Lemma lem5145279 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5145280 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5145279 t1 t2) (@lem5145278 t1 t2)). Qed.
Lemma lem5145281 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5145280 t1 t2 t3). Qed.
Lemma lem5145282 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5145283 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5145282 t1 t2 t3) (@lem5145281 t1 t2 t3)). Qed.
Lemma lem5145284 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5145283 t1 t2 t3)). Qed.
Lemma lem5145286 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5145287 : term8 = term9.
Proof. exact (@lem5145286 term8). Qed.
Lemma lem5145288 : term9 = term8.
Proof. exact (SYM (@lem5145287)). Qed.
Lemma lem5145289 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5145292 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5145293 : term12.
Proof. exact (fun h0 : term11 => @lem5145292 h0). Qed.
Lemma lem5145294 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5145295 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5145296 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5145294 h2 (@lem5145295 h1)). Qed.
Lemma lem5145297 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem5145296 h1 h0). Qed.
Lemma lem5145298 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5145299 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5145297 h1 (@lem5145298 h2)). Qed.
Lemma lem5145300 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem5145299 h0 h1). Qed.
Lemma lem5145301 : term14.
Proof. exact (fun h0 : term12 => @lem5145300 h0). Qed.
Lemma lem5145304 : term12.
Proof. exact (@lem5145301 (@lem5145293)). Qed.
Lemma lem5145388 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5145389 : term15 = term16.
Proof. exact (@lem5145388 term17). Qed.
Lemma lem5145406 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem5145407 : term19 = term20.
Proof. exact (MK_COMB (@lem5145406) (@lem5145389)). Qed.
Lemma lem5145410 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem5145417 : term11 = term22.
Proof. exact (MK_COMB (@lem5145410) (@lem5145407)). Qed.
Lemma lem5145422 (x : real) (s : real -> Prop) : (term23 x s) = (term23 x s).
Proof. exact (eq_refl (term23 x s)). Qed.
Lemma lem5145423 (s : real -> Prop) : (term24 s) = (term24 s).
Proof. exact (fun_ext (fun x : real => @lem5145422 x s)). Qed.
Lemma lem5145424 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5145425 (s : real -> Prop) : (term25 s) = (term25 s).
Proof. exact (MK_COMB (@lem5145424) (@lem5145423 s)). Qed.
Lemma lem5145428 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5145429 (s : real -> Prop) : (term27 s) = (term27 s).
Proof. exact (MK_COMB (@lem5145428 s) (@lem5145425 s)). Qed.
Lemma lem5145438 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5145439 (s : real -> Prop) : (term29 s) = (term29 s).
Proof. exact (MK_COMB (@lem5145438 s) (@lem5145429 s)). Qed.
Lemma lem5145440 : term30 = term30.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5145439 s)). Qed.
Lemma lem5145441 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5145442 : term17 = term17.
Proof. exact (MK_COMB (@lem5145441) (@lem5145440)). Qed.
Lemma lem5145443 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5145444 : term16 = term16.
Proof. exact (MK_COMB (@lem5145443) (@lem5145442)). Qed.
Lemma lem5145453 (y : real) (x : real) (z : real) : (term31 y x z) = (term31 y x z).
Proof. exact (eq_refl (term31 y x z)). Qed.
Lemma lem5145454 (y : real) (x : real) : (term32 y x) = (term32 y x).
Proof. exact (fun_ext (fun z : real => @lem5145453 y x z)). Qed.
Lemma lem5145455 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5145456 (y : real) (x : real) : (term33 y x) = (term33 y x).
Proof. exact (MK_COMB (@lem5145455) (@lem5145454 y x)). Qed.
Lemma lem5145457 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem5145456 y x)). Qed.
Lemma lem5145458 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5145459 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem5145458) (@lem5145457 x)). Qed.
Lemma lem5145460 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem5145459 x)). Qed.
Lemma lem5145461 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5145462 : term37 = term37.
Proof. exact (MK_COMB (@lem5145461) (@lem5145460)). Qed.
Lemma lem5145463 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5145464 : term18 = term18.
Proof. exact (MK_COMB (@lem5145463) (@lem5145462)). Qed.
Lemma lem5145465 : term20 = term20.
Proof. exact (MK_COMB (@lem5145464) (@lem5145444)). Qed.
Lemma lem5145470 (s : real -> Prop) (a : real) (x : real) : (term38 s a x) = (term38 s a x).
Proof. exact (eq_refl (term38 s a x)). Qed.
Lemma lem5145471 (s : real -> Prop) (a : real) : (term39 s a) = (term39 s a).
Proof. exact (fun_ext (fun x : real => @lem5145470 s a x)). Qed.
Lemma lem5145472 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5145473 (s : real -> Prop) (a : real) : (term40 s a) = (term40 s a).
Proof. exact (MK_COMB (@lem5145472) (@lem5145471 s a)). Qed.
Lemma lem5145476 (a : real) (s : real -> Prop) : (term41 a s) = (term41 a s).
Proof. exact (eq_refl (term41 a s)). Qed.
Lemma lem5145477 (s : real -> Prop) (a : real) : ((term42 a s) = (term40 s a)) = ((term42 a s) = (term40 s a)).
Proof. exact (MK_COMB (@lem5145476 a s) (@lem5145473 s a)). Qed.
Lemma lem5145486 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5145487 (s : real -> Prop) (a : real) : (term43 s a) = (term43 s a).
Proof. exact (MK_COMB (@lem5145486 s) (@lem5145477 s a)). Qed.
Lemma lem5145488 (s : real -> Prop) : (term44 s) = (term44 s).
Proof. exact (fun_ext (fun a : real => @lem5145487 s a)). Qed.
Lemma lem5145489 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5145490 (s : real -> Prop) : (term45 s) = (term45 s).
Proof. exact (MK_COMB (@lem5145489) (@lem5145488 s)). Qed.
Lemma lem5145491 : term46 = term46.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5145490 s)). Qed.
Lemma lem5145492 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5145493 : term8 = term8.
Proof. exact (MK_COMB (@lem5145492) (@lem5145491)). Qed.
Lemma lem5145494 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5145495 : term10 = term10.
Proof. exact (MK_COMB (@lem5145494) (@lem5145493)). Qed.
Lemma lem5145496 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5145497 : term21 = term21.
Proof. exact (MK_COMB (@lem5145496) (@lem5145495)). Qed.
Lemma lem5145498 : term22 = term22.
Proof. exact (MK_COMB (@lem5145497) (@lem5145465)). Qed.
Lemma lem5145571 : term11 = term22.
Proof. exact (TRANS (@lem5145417) (@lem5145498)). Qed.
Lemma lem5145572 : term22 = term11.
Proof. exact (SYM (@lem5145571)). Qed.
Lemma lem5145573 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5145574 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem5145575 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem5145591 (s : real -> Prop) (a : real) (x : real) : (term47 s a x) = (term48 s a x).
Proof. exact (@lem17045 (@IN real x s) (real_le a x)). Qed.
Lemma lem5145594 (s : real -> Prop) (a : real) (x : real) : (term38 s a x) = (term38 s a x).
Proof. exact (eq_refl (term38 s a x)). Qed.
Lemma lem5145595 (P : real -> Prop) : (term49 P) = (term50 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5145596 (s : real -> Prop) (a : real) : (term51 s a) = (term52 s a).
Proof. exact (@lem5145595 (term39 s a)). Qed.
Lemma lem5145597 (s : real -> Prop) (a : real) (x : real) : (term53 s a x) = (term38 s a x).
Proof. exact (eq_refl (term53 s a x)). Qed.
Lemma lem5145598 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5145599 (s : real -> Prop) (a : real) (x : real) : (term54 s a x) = (term47 s a x).
Proof. exact (MK_COMB (@lem5145598) (@lem5145597 s a x)). Qed.
Lemma lem5145600 (s : real -> Prop) (a : real) (x : real) : (term54 s a x) = (term48 s a x).
Proof. exact (TRANS (@lem5145599 s a x) (@lem5145591 s a x)). Qed.
Lemma lem5145601 (s : real -> Prop) (a : real) : (term55 s a) = (term56 s a).
Proof. exact (fun_ext (fun x : real => @lem5145600 s a x)). Qed.
Lemma lem5145602 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5145603 (s : real -> Prop) (a : real) : (term52 s a) = (term57 s a).
Proof. exact (MK_COMB (@lem5145602) (@lem5145601 s a)). Qed.
Lemma lem5145604 (s : real -> Prop) (a : real) : (term51 s a) = (term57 s a).
Proof. exact (TRANS (@lem5145596 s a) (@lem5145603 s a)). Qed.
Lemma lem5145605 (s : real -> Prop) (a : real) : (term39 s a) = (term39 s a).
Proof. exact (fun_ext (fun x : real => @lem5145594 s a x)). Qed.
Lemma lem5145606 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5145607 (s : real -> Prop) (a : real) : (term40 s a) = (term40 s a).
Proof. exact (MK_COMB (@lem5145606) (@lem5145605 s a)). Qed.
Lemma lem5145609 (a : real) (s : real -> Prop) : (term58 a s) = (term58 a s).
Proof. exact (eq_refl (term58 a s)). Qed.
Lemma lem5145610 (s : real -> Prop) (a : real) : (term59 s a) = (term59 s a).
Proof. exact (MK_COMB (@lem5145609 a s) (@lem5145607 s a)). Qed.
Lemma lem5145612 (a : real) (s : real -> Prop) : (term60 a s) = (term60 a s).
Proof. exact (eq_refl (term60 a s)). Qed.
Lemma lem5145613 (s : real -> Prop) (a : real) : (term61 s a) = (term62 s a).
Proof. exact (MK_COMB (@lem5145612 a s) (@lem5145604 s a)). Qed.
Lemma lem5145614 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5145615 (s : real -> Prop) (a : real) : (term63 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem5145614) (@lem5145613 s a)). Qed.
Lemma lem5145616 (s : real -> Prop) (a : real) : (term65 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem5145615 s a) (@lem5145610 s a)). Qed.
Lemma lem5145617 (s : real -> Prop) (a : real) : (term67 s a) = (term65 s a).
Proof. exact (@lem17646 (term42 a s) (term40 s a)). Qed.
Lemma lem5145618 (s : real -> Prop) (a : real) : (term67 s a) = (term66 s a).
Proof. exact (TRANS (@lem5145617 s a) (@lem5145616 s a)). Qed.
Lemma lem5145620 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5145621 (s : real -> Prop) (a : real) : (term69 s a) = (term70 s a).
Proof. exact (MK_COMB (@lem5145620 s) (@lem5145618 s a)). Qed.
Lemma lem5145622 (s : real -> Prop) (a : real) : (term71 s a) = (term69 s a).
Proof. exact (@lem17362 (term72 s) ((term42 a s) = (term40 s a))). Qed.
Lemma lem5145623 (s : real -> Prop) (a : real) : (term71 s a) = (term70 s a).
Proof. exact (TRANS (@lem5145622 s a) (@lem5145621 s a)). Qed.
Lemma lem5145624 (P : real -> Prop) : (term73 P) = (term74 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5145625 (s : real -> Prop) : (term75 s) = (term76 s).
Proof. exact (@lem5145624 (term44 s)). Qed.
Lemma lem5145626 (s : real -> Prop) (a : real) : (term77 s a) = (term43 s a).
Proof. exact (eq_refl (term77 s a)). Qed.
Lemma lem5145627 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5145628 (s : real -> Prop) (a : real) : (term78 s a) = (term71 s a).
Proof. exact (MK_COMB (@lem5145627) (@lem5145626 s a)). Qed.
Lemma lem5145629 (s : real -> Prop) (a : real) : (term78 s a) = (term70 s a).
Proof. exact (TRANS (@lem5145628 s a) (@lem5145623 s a)). Qed.
Lemma lem5145630 (s : real -> Prop) : (term79 s) = (term80 s).
Proof. exact (fun_ext (fun a : real => @lem5145629 s a)). Qed.
Lemma lem5145631 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5145632 (s : real -> Prop) : (term76 s) = (term81 s).
Proof. exact (MK_COMB (@lem5145631) (@lem5145630 s)). Qed.
Lemma lem5145633 (s : real -> Prop) : (term75 s) = (term81 s).
Proof. exact (TRANS (@lem5145625 s) (@lem5145632 s)). Qed.
Lemma lem5145634 (P : type1022) : (term82 P) = (term83 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5145635 : term10 = term84.
Proof. exact (@lem5145634 term46). Qed.
Lemma lem5145636 (s : real -> Prop) : (term85 s) = (term45 s).
Proof. exact (eq_refl (term85 s)). Qed.
Lemma lem5145637 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5145638 (s : real -> Prop) : (term86 s) = (term75 s).
Proof. exact (MK_COMB (@lem5145637) (@lem5145636 s)). Qed.
Lemma lem5145639 (s : real -> Prop) : (term86 s) = (term81 s).
Proof. exact (TRANS (@lem5145638 s) (@lem5145633 s)). Qed.
Lemma lem5145640 : term87 = term88.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5145639 s)). Qed.
Lemma lem5145641 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5145642 : term84 = term89.
Proof. exact (MK_COMB (@lem5145641) (@lem5145640)). Qed.
Lemma lem5145643 : term10 = term89.
Proof. exact (TRANS (@lem5145635) (@lem5145642)). Qed.
Lemma lem5145649 {A : Type'} (P : Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem5145650 (P : Prop) (Q : real -> Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem5145649 real P Q). Qed.
Lemma lem5145651 (s : real -> Prop) : (term94 s) = (term95 s).
Proof. exact (@lem5145650 (term72 s) (term96 s)). Qed.
Lemma lem5145652 (s : real -> Prop) (a : real) : (term97 s a) = (term66 s a).
Proof. exact (eq_refl (term97 s a)). Qed.
Lemma lem5145653 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5145654 (s : real -> Prop) (a : real) : (term98 s a) = (term70 s a).
Proof. exact (MK_COMB (@lem5145653 s) (@lem5145652 s a)). Qed.
Lemma lem5145655 (s : real -> Prop) : (term99 s) = (term80 s).
Proof. exact (fun_ext (fun a : real => @lem5145654 s a)). Qed.
Lemma lem5145656 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5145657 (s : real -> Prop) : (term94 s) = (term81 s).
Proof. exact (MK_COMB (@lem5145656) (@lem5145655 s)). Qed.
Lemma lem5145658 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5145659 (s : real -> Prop) : (term100 s) = (term101 s).
Proof. exact (MK_COMB (@lem5145658) (@lem5145657 s)). Qed.
Lemma lem5145660 (s : real -> Prop) (a : real) : (term97 s a) = (term66 s a).
Proof. exact (eq_refl (term97 s a)). Qed.
Lemma lem5145661 (s : real -> Prop) : (term102 s) = (term96 s).
Proof. exact (fun_ext (fun a : real => @lem5145660 s a)). Qed.
Lemma lem5145662 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5145663 (s : real -> Prop) : (term103 s) = (term104 s).
Proof. exact (MK_COMB (@lem5145662) (@lem5145661 s)). Qed.
Lemma lem5145664 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5145665 (s : real -> Prop) : (term95 s) = (term105 s).
Proof. exact (MK_COMB (@lem5145664 s) (@lem5145663 s)). Qed.
Lemma lem5145666 (s : real -> Prop) : ((term94 s) = (term95 s)) = ((term81 s) = (term105 s)).
Proof. exact (MK_COMB (@lem5145659 s) (@lem5145665 s)). Qed.
Lemma lem5145667 (s : real -> Prop) : (term81 s) = (term105 s).
Proof. exact (EQ_MP (@lem5145666 s) (@lem5145651 s)). Qed.
Lemma lem5145669 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5145670 (P : real -> Prop) (Q : real -> Prop) : (term108 P Q) = (term109 P Q).
Proof. exact (@lem5145669 real P Q). Qed.
Lemma lem5145671 (s : real -> Prop) : (term110 s) = (term111 s).
Proof. exact (@lem5145670 (term112 s) (term113 s)). Qed.
Lemma lem5145672 (s : real -> Prop) (a : real) : (term114 s a) = (term62 s a).
Proof. exact (eq_refl (term114 s a)). Qed.
Lemma lem5145673 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5145674 (s : real -> Prop) (a : real) : (term115 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem5145673) (@lem5145672 s a)). Qed.
Lemma lem5145675 (s : real -> Prop) (a : real) : (term116 s a) = (term59 s a).
Proof. exact (eq_refl (term116 s a)). Qed.
Lemma lem5145676 (s : real -> Prop) (a : real) : (term117 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem5145674 s a) (@lem5145675 s a)). Qed.
Lemma lem5145677 (s : real -> Prop) : (term118 s) = (term96 s).
Proof. exact (fun_ext (fun a : real => @lem5145676 s a)). Qed.
Lemma lem5145678 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5145679 (s : real -> Prop) : (term110 s) = (term104 s).
Proof. exact (MK_COMB (@lem5145678) (@lem5145677 s)). Qed.
Lemma lem5145680 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5145681 (s : real -> Prop) : (term119 s) = (term120 s).
Proof. exact (MK_COMB (@lem5145680) (@lem5145679 s)). Qed.
Lemma lem5145682 (s : real -> Prop) (a : real) : (term114 s a) = (term62 s a).
Proof. exact (eq_refl (term114 s a)). Qed.
Lemma lem5145683 (s : real -> Prop) : (term121 s) = (term112 s).
Proof. exact (fun_ext (fun a : real => @lem5145682 s a)). Qed.
Lemma lem5145684 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5145685 (s : real -> Prop) : (term122 s) = (term123 s).
Proof. exact (MK_COMB (@lem5145684) (@lem5145683 s)). Qed.
Lemma lem5145686 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5145687 (s : real -> Prop) : (term124 s) = (term125 s).
Proof. exact (MK_COMB (@lem5145686) (@lem5145685 s)). Qed.
Lemma lem5145688 (s : real -> Prop) (a : real) : (term116 s a) = (term59 s a).
Proof. exact (eq_refl (term116 s a)). Qed.
Lemma lem5145689 (s : real -> Prop) : (term126 s) = (term113 s).
Proof. exact (fun_ext (fun a : real => @lem5145688 s a)). Qed.
Lemma lem5145690 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5145691 (s : real -> Prop) : (term127 s) = (term128 s).
Proof. exact (MK_COMB (@lem5145690) (@lem5145689 s)). Qed.
Lemma lem5145692 (s : real -> Prop) : (term111 s) = (term129 s).
Proof. exact (MK_COMB (@lem5145687 s) (@lem5145691 s)). Qed.
Lemma lem5145693 (s : real -> Prop) : ((term110 s) = (term111 s)) = ((term104 s) = (term129 s)).
Proof. exact (MK_COMB (@lem5145681 s) (@lem5145692 s)). Qed.
Lemma lem5145694 (s : real -> Prop) : (term104 s) = (term129 s).
Proof. exact (EQ_MP (@lem5145693 s) (@lem5145671 s)). Qed.
Lemma lem5145887 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5145888 (s : real -> Prop) : (term105 s) = (term130 s).
Proof. exact (MK_COMB (@lem5145887 s) (@lem5145694 s)). Qed.
Lemma lem5145889 (s : real -> Prop) : (term81 s) = (term130 s).
Proof. exact (TRANS (@lem5145667 s) (@lem5145888 s)). Qed.
Lemma lem5145890 : term88 = term131.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5145889 s)). Qed.
Lemma lem5145891 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5145892 : term89 = term132.
Proof. exact (MK_COMB (@lem5145891) (@lem5145890)). Qed.
Lemma lem5145942 {A : Type'} (P : Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5145943 (P : Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem5145942 real P Q). Qed.
Lemma lem5145944 (s : real -> Prop) (a : real) : (term133 s a) = (term134 s a).
Proof. exact (@lem5145943 (term135 a s) (term39 s a)). Qed.
Lemma lem5145945 (s : real -> Prop) (a : real) (x : real) : (term53 s a x) = (term38 s a x).
Proof. exact (eq_refl (term53 s a x)). Qed.
Lemma lem5145946 (s : real -> Prop) (a : real) : (term136 s a) = (term39 s a).
Proof. exact (fun_ext (fun x : real => @lem5145945 s a x)). Qed.
Lemma lem5145947 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5145948 (s : real -> Prop) (a : real) : (term137 s a) = (term40 s a).
Proof. exact (MK_COMB (@lem5145947) (@lem5145946 s a)). Qed.
Lemma lem5145949 (a : real) (s : real -> Prop) : (term58 a s) = (term58 a s).
Proof. exact (eq_refl (term58 a s)). Qed.
Lemma lem5145950 (s : real -> Prop) (a : real) : (term133 s a) = (term59 s a).
Proof. exact (MK_COMB (@lem5145949 a s) (@lem5145948 s a)). Qed.
Lemma lem5145951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5145952 (s : real -> Prop) (a : real) : (term138 s a) = (term139 s a).
Proof. exact (MK_COMB (@lem5145951) (@lem5145950 s a)). Qed.
Lemma lem5145953 (s : real -> Prop) (a : real) (x : real) : (term53 s a x) = (term38 s a x).
Proof. exact (eq_refl (term53 s a x)). Qed.
Lemma lem5145954 (a : real) (s : real -> Prop) : (term58 a s) = (term58 a s).
Proof. exact (eq_refl (term58 a s)). Qed.
Lemma lem5145955 (s : real -> Prop) (a : real) (x : real) : (term140 s a x) = (term141 s a x).
Proof. exact (MK_COMB (@lem5145954 a s) (@lem5145953 s a x)). Qed.
Lemma lem5145956 (s : real -> Prop) (a : real) : (term142 s a) = (term143 s a).
Proof. exact (fun_ext (fun x : real => @lem5145955 s a x)). Qed.
Lemma lem5145957 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5145958 (s : real -> Prop) (a : real) : (term134 s a) = (term144 s a).
Proof. exact (MK_COMB (@lem5145957) (@lem5145956 s a)). Qed.
Lemma lem5145959 (s : real -> Prop) (a : real) : ((term133 s a) = (term134 s a)) = ((term59 s a) = (term144 s a)).
Proof. exact (MK_COMB (@lem5145952 s a) (@lem5145958 s a)). Qed.
Lemma lem5145960 (s : real -> Prop) (a : real) : (term59 s a) = (term144 s a).
Proof. exact (EQ_MP (@lem5145959 s a) (@lem5145944 s a)). Qed.
Lemma lem5145961 (s : real -> Prop) : (term113 s) = (term145 s).
Proof. exact (fun_ext (fun a : real => @lem5145960 s a)). Qed.
Lemma lem5145962 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5145963 (s : real -> Prop) : (term128 s) = (term146 s).
Proof. exact (MK_COMB (@lem5145962) (@lem5145961 s)). Qed.
Lemma lem5145964 (s : real -> Prop) : (term125 s) = (term125 s).
Proof. exact (eq_refl (term125 s)). Qed.
Lemma lem5145965 (s : real -> Prop) : (term129 s) = (term147 s).
Proof. exact (MK_COMB (@lem5145964 s) (@lem5145963 s)). Qed.
Lemma lem5145967 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term107 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5145968 (P : real -> Prop) (Q : real -> Prop) : (term109 P Q) = (term108 P Q).
Proof. exact (@lem5145967 real P Q). Qed.
Lemma lem5145969 (s : real -> Prop) : (term148 s) = (term149 s).
Proof. exact (@lem5145968 (term112 s) (term145 s)). Qed.
Lemma lem5145970 (s : real -> Prop) (a : real) : (term114 s a) = (term62 s a).
Proof. exact (eq_refl (term114 s a)). Qed.
Lemma lem5145971 (s : real -> Prop) : (term121 s) = (term112 s).
Proof. exact (fun_ext (fun a : real => @lem5145970 s a)). Qed.
Lemma lem5145972 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5145973 (s : real -> Prop) : (term122 s) = (term123 s).
Proof. exact (MK_COMB (@lem5145972) (@lem5145971 s)). Qed.
Lemma lem5145974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5145975 (s : real -> Prop) : (term124 s) = (term125 s).
Proof. exact (MK_COMB (@lem5145974) (@lem5145973 s)). Qed.
Lemma lem5145976 (s : real -> Prop) (a : real) : (term150 s a) = (term144 s a).
Proof. exact (eq_refl (term150 s a)). Qed.
Lemma lem5145977 (s : real -> Prop) : (term151 s) = (term145 s).
Proof. exact (fun_ext (fun a : real => @lem5145976 s a)). Qed.
Lemma lem5145978 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5145979 (s : real -> Prop) : (term152 s) = (term146 s).
Proof. exact (MK_COMB (@lem5145978) (@lem5145977 s)). Qed.
Lemma lem5145980 (s : real -> Prop) : (term148 s) = (term147 s).
Proof. exact (MK_COMB (@lem5145975 s) (@lem5145979 s)). Qed.
Lemma lem5145981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5145982 (s : real -> Prop) : (term153 s) = (term154 s).
Proof. exact (MK_COMB (@lem5145981) (@lem5145980 s)). Qed.
Lemma lem5145983 (s : real -> Prop) (a : real) : (term114 s a) = (term62 s a).
Proof. exact (eq_refl (term114 s a)). Qed.
Lemma lem5145984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5145985 (s : real -> Prop) (a : real) : (term115 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem5145984) (@lem5145983 s a)). Qed.
Lemma lem5145986 (s : real -> Prop) (a : real) : (term150 s a) = (term144 s a).
Proof. exact (eq_refl (term150 s a)). Qed.
Lemma lem5145987 (s : real -> Prop) (a : real) : (term155 s a) = (term156 s a).
Proof. exact (MK_COMB (@lem5145985 s a) (@lem5145986 s a)). Qed.
Lemma lem5145988 (s : real -> Prop) : (term157 s) = (term158 s).
Proof. exact (fun_ext (fun a : real => @lem5145987 s a)). Qed.
Lemma lem5145989 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5145990 (s : real -> Prop) : (term149 s) = (term159 s).
Proof. exact (MK_COMB (@lem5145989) (@lem5145988 s)). Qed.
Lemma lem5145991 (s : real -> Prop) : ((term148 s) = (term149 s)) = ((term147 s) = (term159 s)).
Proof. exact (MK_COMB (@lem5145982 s) (@lem5145990 s)). Qed.
Lemma lem5145992 (s : real -> Prop) : (term147 s) = (term159 s).
Proof. exact (EQ_MP (@lem5145991 s) (@lem5145969 s)). Qed.
Lemma lem5145994 {A : Type'} (P : Prop) (Q : A -> Prop) : (term160 A P Q) = (term161 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5145995 (P : Prop) (Q : real -> Prop) : (term162 P Q) = (term163 P Q).
Proof. exact (@lem5145994 real P Q). Qed.
Lemma lem5145996 (s : real -> Prop) (a : real) : (term164 s a) = (term165 s a).
Proof. exact (@lem5145995 (term62 s a) (term143 s a)). Qed.
Lemma lem5145997 (s : real -> Prop) (a : real) (x : real) : (term166 s a x) = (term141 s a x).
Proof. exact (eq_refl (term166 s a x)). Qed.
Lemma lem5145998 (s : real -> Prop) (a : real) : (term167 s a) = (term143 s a).
Proof. exact (fun_ext (fun x : real => @lem5145997 s a x)). Qed.
Lemma lem5145999 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5146000 (s : real -> Prop) (a : real) : (term168 s a) = (term144 s a).
Proof. exact (MK_COMB (@lem5145999) (@lem5145998 s a)). Qed.
Lemma lem5146001 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (eq_refl (term64 s a)). Qed.
Lemma lem5146002 (s : real -> Prop) (a : real) : (term164 s a) = (term156 s a).
Proof. exact (MK_COMB (@lem5146001 s a) (@lem5146000 s a)). Qed.
Lemma lem5146003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5146004 (s : real -> Prop) (a : real) : (term169 s a) = (term170 s a).
Proof. exact (MK_COMB (@lem5146003) (@lem5146002 s a)). Qed.
Lemma lem5146005 (s : real -> Prop) (a : real) (x : real) : (term166 s a x) = (term141 s a x).
Proof. exact (eq_refl (term166 s a x)). Qed.
Lemma lem5146006 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (eq_refl (term64 s a)). Qed.
Lemma lem5146007 (s : real -> Prop) (a : real) (x : real) : (term171 s a x) = (term172 s a x).
Proof. exact (MK_COMB (@lem5146006 s a) (@lem5146005 s a x)). Qed.
Lemma lem5146008 (s : real -> Prop) (a : real) : (term173 s a) = (term174 s a).
Proof. exact (fun_ext (fun x : real => @lem5146007 s a x)). Qed.
Lemma lem5146009 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5146010 (s : real -> Prop) (a : real) : (term165 s a) = (term175 s a).
Proof. exact (MK_COMB (@lem5146009) (@lem5146008 s a)). Qed.
Lemma lem5146011 (s : real -> Prop) (a : real) : ((term164 s a) = (term165 s a)) = ((term156 s a) = (term175 s a)).
Proof. exact (MK_COMB (@lem5146004 s a) (@lem5146010 s a)). Qed.
Lemma lem5146012 (s : real -> Prop) (a : real) : (term156 s a) = (term175 s a).
Proof. exact (EQ_MP (@lem5146011 s a) (@lem5145996 s a)). Qed.
Lemma lem5146013 (s : real -> Prop) : (term158 s) = (term176 s).
Proof. exact (fun_ext (fun a : real => @lem5146012 s a)). Qed.
Lemma lem5146014 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5146015 (s : real -> Prop) : (term159 s) = (term177 s).
Proof. exact (MK_COMB (@lem5146014) (@lem5146013 s)). Qed.
Lemma lem5146016 (s : real -> Prop) : (term147 s) = (term177 s).
Proof. exact (TRANS (@lem5145992 s) (@lem5146015 s)). Qed.
Lemma lem5146017 (s : real -> Prop) : (term129 s) = (term177 s).
Proof. exact (TRANS (@lem5145965 s) (@lem5146016 s)). Qed.
Lemma lem5146018 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5146019 (s : real -> Prop) : (term130 s) = (term178 s).
Proof. exact (MK_COMB (@lem5146018 s) (@lem5146017 s)). Qed.
Lemma lem5146021 {A : Type'} (P : Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5146022 (P : Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem5146021 real P Q). Qed.
Lemma lem5146023 (s : real -> Prop) : (term179 s) = (term180 s).
Proof. exact (@lem5146022 (term72 s) (term176 s)). Qed.
Lemma lem5146024 (s : real -> Prop) (a : real) : (term181 s a) = (term175 s a).
Proof. exact (eq_refl (term181 s a)). Qed.
Lemma lem5146025 (s : real -> Prop) : (term182 s) = (term176 s).
Proof. exact (fun_ext (fun a : real => @lem5146024 s a)). Qed.
Lemma lem5146026 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5146027 (s : real -> Prop) : (term183 s) = (term177 s).
Proof. exact (MK_COMB (@lem5146026) (@lem5146025 s)). Qed.
Lemma lem5146028 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5146029 (s : real -> Prop) : (term179 s) = (term178 s).
Proof. exact (MK_COMB (@lem5146028 s) (@lem5146027 s)). Qed.
Lemma lem5146030 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5146031 (s : real -> Prop) : (term184 s) = (term185 s).
Proof. exact (MK_COMB (@lem5146030) (@lem5146029 s)). Qed.
Lemma lem5146032 (s : real -> Prop) (a : real) : (term181 s a) = (term175 s a).
Proof. exact (eq_refl (term181 s a)). Qed.
Lemma lem5146033 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5146034 (s : real -> Prop) (a : real) : (term186 s a) = (term187 s a).
Proof. exact (MK_COMB (@lem5146033 s) (@lem5146032 s a)). Qed.
Lemma lem5146035 (s : real -> Prop) : (term188 s) = (term189 s).
Proof. exact (fun_ext (fun a : real => @lem5146034 s a)). Qed.
Lemma lem5146036 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5146037 (s : real -> Prop) : (term180 s) = (term190 s).
Proof. exact (MK_COMB (@lem5146036) (@lem5146035 s)). Qed.
Lemma lem5146038 (s : real -> Prop) : ((term179 s) = (term180 s)) = ((term178 s) = (term190 s)).
Proof. exact (MK_COMB (@lem5146031 s) (@lem5146037 s)). Qed.
Lemma lem5146039 (s : real -> Prop) : (term178 s) = (term190 s).
Proof. exact (EQ_MP (@lem5146038 s) (@lem5146023 s)). Qed.
Lemma lem5146041 {A : Type'} (P : Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5146042 (P : Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem5146041 real P Q). Qed.
Lemma lem5146043 (s : real -> Prop) (a : real) : (term191 s a) = (term192 s a).
Proof. exact (@lem5146042 (term72 s) (term174 s a)). Qed.
Lemma lem5146044 (s : real -> Prop) (a : real) (x : real) : (term193 s a x) = (term172 s a x).
Proof. exact (eq_refl (term193 s a x)). Qed.
Lemma lem5146045 (s : real -> Prop) (a : real) : (term194 s a) = (term174 s a).
Proof. exact (fun_ext (fun x : real => @lem5146044 s a x)). Qed.
Lemma lem5146046 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5146047 (s : real -> Prop) (a : real) : (term195 s a) = (term175 s a).
Proof. exact (MK_COMB (@lem5146046) (@lem5146045 s a)). Qed.
Lemma lem5146048 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5146049 (s : real -> Prop) (a : real) : (term191 s a) = (term187 s a).
Proof. exact (MK_COMB (@lem5146048 s) (@lem5146047 s a)). Qed.
Lemma lem5146050 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5146051 (s : real -> Prop) (a : real) : (term196 s a) = (term197 s a).
Proof. exact (MK_COMB (@lem5146050) (@lem5146049 s a)). Qed.
Lemma lem5146052 (s : real -> Prop) (a : real) (x : real) : (term193 s a x) = (term172 s a x).
Proof. exact (eq_refl (term193 s a x)). Qed.
Lemma lem5146053 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5146054 (s : real -> Prop) (a : real) (x : real) : (term198 s a x) = (term199 s a x).
Proof. exact (MK_COMB (@lem5146053 s) (@lem5146052 s a x)). Qed.
Lemma lem5146055 (s : real -> Prop) (a : real) : (term200 s a) = (term201 s a).
Proof. exact (fun_ext (fun x : real => @lem5146054 s a x)). Qed.
Lemma lem5146056 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5146057 (s : real -> Prop) (a : real) : (term192 s a) = (term202 s a).
Proof. exact (MK_COMB (@lem5146056) (@lem5146055 s a)). Qed.
Lemma lem5146058 (s : real -> Prop) (a : real) : ((term191 s a) = (term192 s a)) = ((term187 s a) = (term202 s a)).
Proof. exact (MK_COMB (@lem5146051 s a) (@lem5146057 s a)). Qed.
Lemma lem5146059 (s : real -> Prop) (a : real) : (term187 s a) = (term202 s a).
Proof. exact (EQ_MP (@lem5146058 s a) (@lem5146043 s a)). Qed.
Lemma lem5146060 (s : real -> Prop) : (term189 s) = (term203 s).
Proof. exact (fun_ext (fun a : real => @lem5146059 s a)). Qed.
Lemma lem5146061 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5146062 (s : real -> Prop) : (term190 s) = (term204 s).
Proof. exact (MK_COMB (@lem5146061) (@lem5146060 s)). Qed.
Lemma lem5146063 (s : real -> Prop) : (term178 s) = (term204 s).
Proof. exact (TRANS (@lem5146039 s) (@lem5146062 s)). Qed.
Lemma lem5146064 (s : real -> Prop) : (term130 s) = (term204 s).
Proof. exact (TRANS (@lem5146019 s) (@lem5146063 s)). Qed.
Lemma lem5146065 : term131 = term205.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5146064 s)). Qed.
Lemma lem5146066 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5146067 : term132 = term206.
Proof. exact (MK_COMB (@lem5146066) (@lem5146065)). Qed.
Lemma lem5146068 : term89 = term206.
Proof. exact (TRANS (@lem5145892) (@lem5146067)). Qed.
Lemma lem5146069 : term10 = term206.
Proof. exact (TRANS (@lem5145643) (@lem5146068)). Qed.
Lemma lem5146070 (h1 : term10) : term206.
Proof. exact (EQ_MP (@lem5146069) (@lem5145573 h1)). Qed.
Lemma lem5146077 (x : real) (y : real) (z : real) : (term207 x y z) = (term208 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem5146078 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem5146079 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5146080 (x : real) (y : real) (z : real) : (term209 x y z) = (term210 x y z).
Proof. exact (MK_COMB (@lem5146079) (@lem5146077 x y z)). Qed.
Lemma lem5146081 (y : real) (x : real) (z : real) : (term211 y x z) = (term212 y x z).
Proof. exact (MK_COMB (@lem5146080 x y z) (@lem5146078 x z)). Qed.
Lemma lem5146082 (y : real) (x : real) (z : real) : (term31 y x z) = (term211 y x z).
Proof. exact (@lem17265 (term213 x y z) (real_le x z)). Qed.
Lemma lem5146083 (y : real) (x : real) (z : real) : (term31 y x z) = (term212 y x z).
Proof. exact (TRANS (@lem5146082 y x z) (@lem5146081 y x z)). Qed.
Lemma lem5146084 (y : real) (x : real) : (term32 y x) = (term214 y x).
Proof. exact (fun_ext (fun z : real => @lem5146083 y x z)). Qed.
Lemma lem5146085 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146086 (y : real) (x : real) : (term33 y x) = (term215 y x).
Proof. exact (MK_COMB (@lem5146085) (@lem5146084 y x)). Qed.
Lemma lem5146087 (x : real) : (term34 x) = (term216 x).
Proof. exact (fun_ext (fun y : real => @lem5146086 y x)). Qed.
Lemma lem5146088 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146089 (x : real) : (term35 x) = (term217 x).
Proof. exact (MK_COMB (@lem5146088) (@lem5146087 x)). Qed.
Lemma lem5146090 : term36 = term218.
Proof. exact (fun_ext (fun x : real => @lem5146089 x)). Qed.
Lemma lem5146091 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146152 : term37 = term219.
Proof. exact (MK_COMB (@lem5146091) (@lem5146090)). Qed.
Lemma lem5146153 (h1 : term37) : term219.
Proof. exact (EQ_MP (@lem5146152) (@lem5145574 h1)). Qed.
Lemma lem5146157 (s : real -> Prop) : (term220 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5146159 (s : real -> Prop) : (term221 s) = (term221 s).
Proof. exact (eq_refl (term221 s)). Qed.
Lemma lem5146160 (s : real -> Prop) : (term222 s) = (term223 s).
Proof. exact (MK_COMB (@lem5146159 s) (@lem5146157 s)). Qed.
Lemma lem5146161 (s : real -> Prop) : (term224 s) = (term222 s).
Proof. exact (@lem17045 (@FINITE real s) (term225 s)). Qed.
Lemma lem5146162 (s : real -> Prop) : (term224 s) = (term223 s).
Proof. exact (TRANS (@lem5146161 s) (@lem5146160 s)). Qed.
Lemma lem5146170 (x : real) (s : real -> Prop) : (term23 x s) = (term226 x s).
Proof. exact (@lem17265 (@IN real x s) (term42 x s)). Qed.
Lemma lem5146171 (s : real -> Prop) : (term24 s) = (term227 s).
Proof. exact (fun_ext (fun x : real => @lem5146170 x s)). Qed.
Lemma lem5146172 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146173 (s : real -> Prop) : (term25 s) = (term228 s).
Proof. exact (MK_COMB (@lem5146172) (@lem5146171 s)). Qed.
Lemma lem5146175 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5146176 (s : real -> Prop) : (term27 s) = (term229 s).
Proof. exact (MK_COMB (@lem5146175 s) (@lem5146173 s)). Qed.
Lemma lem5146177 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5146178 (s : real -> Prop) : (term230 s) = (term231 s).
Proof. exact (MK_COMB (@lem5146177) (@lem5146162 s)). Qed.
Lemma lem5146179 (s : real -> Prop) : (term232 s) = (term233 s).
Proof. exact (MK_COMB (@lem5146178 s) (@lem5146176 s)). Qed.
Lemma lem5146180 (s : real -> Prop) : (term29 s) = (term232 s).
Proof. exact (@lem17265 (term72 s) (term27 s)). Qed.
Lemma lem5146181 (s : real -> Prop) : (term29 s) = (term233 s).
Proof. exact (TRANS (@lem5146180 s) (@lem5146179 s)). Qed.
Lemma lem5146182 : term30 = term234.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5146181 s)). Qed.
Lemma lem5146183 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5146284 : term17 = term235.
Proof. exact (MK_COMB (@lem5146183) (@lem5146182)). Qed.
Lemma lem5146285 (h1 : term17) : term235.
Proof. exact (EQ_MP (@lem5146284) (@lem5145575 h1)). Qed.
Lemma lem5146286 (s : real -> Prop) (h1 : term204 s) : term204 s.
Proof. exact (h1). Qed.
Lemma lem5146287 (s : real -> Prop) (a : real) (h1 : term202 s a) : term202 s a.
Proof. exact (h1). Qed.
Lemma lem5146288 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term199 s a x.
Proof. exact (h1). Qed.
Lemma lem5146313 (y : real) (x : real) (z : real) : (term212 y x z) = (term212 y x z).
Proof. exact (eq_refl (term212 y x z)). Qed.
Lemma lem5146314 (y : real) (x : real) : (term214 y x) = (term214 y x).
Proof. exact (fun_ext (fun z : real => @lem5146313 y x z)). Qed.
Lemma lem5146315 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146316 (y : real) (x : real) : (term215 y x) = (term215 y x).
Proof. exact (MK_COMB (@lem5146315) (@lem5146314 y x)). Qed.
Lemma lem5146317 (x : real) : (term216 x) = (term216 x).
Proof. exact (fun_ext (fun y : real => @lem5146316 y x)). Qed.
Lemma lem5146318 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146319 (x : real) : (term217 x) = (term217 x).
Proof. exact (MK_COMB (@lem5146318) (@lem5146317 x)). Qed.
Lemma lem5146320 : term218 = term218.
Proof. exact (fun_ext (fun x : real => @lem5146319 x)). Qed.
Lemma lem5146321 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146322 : term219 = term219.
Proof. exact (MK_COMB (@lem5146321) (@lem5146320)). Qed.
Lemma lem5146323 (h1 : term37) : term219.
Proof. exact (EQ_MP (@lem5146322) (@lem5146153 h1)). Qed.
Lemma lem5146340 (x : real) (s : real -> Prop) : (term226 x s) = (term226 x s).
Proof. exact (eq_refl (term226 x s)). Qed.
Lemma lem5146341 (s : real -> Prop) : (term227 s) = (term227 s).
Proof. exact (fun_ext (fun x : real => @lem5146340 x s)). Qed.
Lemma lem5146342 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146343 (s : real -> Prop) : (term228 s) = (term228 s).
Proof. exact (MK_COMB (@lem5146342) (@lem5146341 s)). Qed.
Lemma lem5146352 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5146353 (s : real -> Prop) : (term229 s) = (term229 s).
Proof. exact (MK_COMB (@lem5146352 s) (@lem5146343 s)). Qed.
Lemma lem5146368 (s : real -> Prop) : (term231 s) = (term231 s).
Proof. exact (eq_refl (term231 s)). Qed.
Lemma lem5146369 (s : real -> Prop) : (term233 s) = (term233 s).
Proof. exact (MK_COMB (@lem5146368 s) (@lem5146353 s)). Qed.
Lemma lem5146370 : term234 = term234.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5146369 s)). Qed.
Lemma lem5146371 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5146372 : term235 = term235.
Proof. exact (MK_COMB (@lem5146371) (@lem5146370)). Qed.
Lemma lem5146373 (h1 : term17) : term235.
Proof. exact (EQ_MP (@lem5146372) (@lem5146285 h1)). Qed.
Lemma lem5146398 (s : real -> Prop) (a : real) (x : real) : (term141 s a x) = (term141 s a x).
Proof. exact (eq_refl (term141 s a x)). Qed.
Lemma lem5146415 (s : real -> Prop) (a : real) (x : real) : (term48 s a x) = (term48 s a x).
Proof. exact (eq_refl (term48 s a x)). Qed.
Lemma lem5146416 (s : real -> Prop) (a : real) : (term56 s a) = (term56 s a).
Proof. exact (fun_ext (fun x : real => @lem5146415 s a x)). Qed.
Lemma lem5146417 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146418 (s : real -> Prop) (a : real) : (term57 s a) = (term57 s a).
Proof. exact (MK_COMB (@lem5146417) (@lem5146416 s a)). Qed.
Lemma lem5146427 (a : real) (s : real -> Prop) : (term60 a s) = (term60 a s).
Proof. exact (eq_refl (term60 a s)). Qed.
Lemma lem5146428 (s : real -> Prop) (a : real) : (term62 s a) = (term62 s a).
Proof. exact (MK_COMB (@lem5146427 a s) (@lem5146418 s a)). Qed.
Lemma lem5146429 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5146430 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem5146429) (@lem5146428 s a)). Qed.
Lemma lem5146431 (s : real -> Prop) (a : real) (x : real) : (term172 s a x) = (term172 s a x).
Proof. exact (MK_COMB (@lem5146430 s a) (@lem5146398 s a x)). Qed.
Lemma lem5146446 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5146447 (s : real -> Prop) (a : real) (x : real) : (term199 s a x) = (term199 s a x).
Proof. exact (MK_COMB (@lem5146446 s) (@lem5146431 s a x)). Qed.
Lemma lem5146448 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term199 s a x.
Proof. exact (EQ_MP (@lem5146447 s a x) (@lem5146288 s a x h1)). Qed.
Lemma lem5146449 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term172 s a x.
Proof. exact (proj2 (@lem5146448 s a x h1)). Qed.
Lemma lem5146450 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term72 s.
Proof. exact (proj1 (@lem5146448 s a x h1)). Qed.
Lemma lem5146453 (s : real -> Prop) (a : real) (h1 : term62 s a) : term62 s a.
Proof. exact (h1). Qed.
Lemma lem5146454 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : term141 s a x.
Proof. exact (h1). Qed.
Lemma lem5146455 (s : real -> Prop) (a : real) (h1 : term62 s a) : term57 s a.
Proof. exact (proj2 (@lem5146453 s a h1)). Qed.
Lemma lem5146457 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : term38 s a x.
Proof. exact (proj2 (@lem5146454 s a x h1)). Qed.
Lemma lem5146487 {A : Type'} (P : Prop) (Q : A -> Prop) : (term236 A P Q) = (term237 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5146488 (P : Prop) (Q : real -> Prop) : (term238 P Q) = (term239 P Q).
Proof. exact (@lem5146487 real P Q). Qed.
Lemma lem5146489 (s : real -> Prop) : (term240 s) = (term241 s).
Proof. exact (@lem5146488 (term242 s) (term227 s)). Qed.
Lemma lem5146490 (x : real) (s : real -> Prop) : (term243 s x) = (term226 x s).
Proof. exact (eq_refl (term243 s x)). Qed.
Lemma lem5146491 (s : real -> Prop) : (term244 s) = (term227 s).
Proof. exact (fun_ext (fun x : real => @lem5146490 x s)). Qed.
Lemma lem5146492 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146493 (s : real -> Prop) : (term245 s) = (term228 s).
Proof. exact (MK_COMB (@lem5146492) (@lem5146491 s)). Qed.
Lemma lem5146494 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5146495 (s : real -> Prop) : (term240 s) = (term229 s).
Proof. exact (MK_COMB (@lem5146494 s) (@lem5146493 s)). Qed.
Lemma lem5146496 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5146497 (s : real -> Prop) : (term246 s) = (term247 s).
Proof. exact (MK_COMB (@lem5146496) (@lem5146495 s)). Qed.
Lemma lem5146498 (x : real) (s : real -> Prop) : (term243 s x) = (term226 x s).
Proof. exact (eq_refl (term243 s x)). Qed.
Lemma lem5146499 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5146500 (x : real) (s : real -> Prop) : (term248 s x) = (term249 x s).
Proof. exact (MK_COMB (@lem5146499 s) (@lem5146498 x s)). Qed.
Lemma lem5146501 (s : real -> Prop) : (term250 s) = (term251 s).
Proof. exact (fun_ext (fun x : real => @lem5146500 x s)). Qed.
Lemma lem5146502 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146503 (s : real -> Prop) : (term241 s) = (term252 s).
Proof. exact (MK_COMB (@lem5146502) (@lem5146501 s)). Qed.
Lemma lem5146504 (s : real -> Prop) : ((term240 s) = (term241 s)) = ((term229 s) = (term252 s)).
Proof. exact (MK_COMB (@lem5146497 s) (@lem5146503 s)). Qed.
Lemma lem5146505 (s : real -> Prop) : (term229 s) = (term252 s).
Proof. exact (EQ_MP (@lem5146504 s) (@lem5146489 s)). Qed.
Lemma lem5146506 (s : real -> Prop) : (term231 s) = (term231 s).
Proof. exact (eq_refl (term231 s)). Qed.
Lemma lem5146507 (s : real -> Prop) : (term233 s) = (term253 s).
Proof. exact (MK_COMB (@lem5146506 s) (@lem5146505 s)). Qed.
Lemma lem5146509 {A : Type'} (P : Prop) (Q : A -> Prop) : (term254 A P Q) = (term255 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5146510 (P : Prop) (Q : real -> Prop) : (term256 P Q) = (term257 P Q).
Proof. exact (@lem5146509 real P Q). Qed.
Lemma lem5146511 (s : real -> Prop) : (term258 s) = (term259 s).
Proof. exact (@lem5146510 (term223 s) (term251 s)). Qed.
Lemma lem5146512 (x : real) (s : real -> Prop) : (term260 s x) = (term249 x s).
Proof. exact (eq_refl (term260 s x)). Qed.
Lemma lem5146513 (s : real -> Prop) : (term261 s) = (term251 s).
Proof. exact (fun_ext (fun x : real => @lem5146512 x s)). Qed.
Lemma lem5146514 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146515 (s : real -> Prop) : (term262 s) = (term252 s).
Proof. exact (MK_COMB (@lem5146514) (@lem5146513 s)). Qed.
Lemma lem5146516 (s : real -> Prop) : (term231 s) = (term231 s).
Proof. exact (eq_refl (term231 s)). Qed.
Lemma lem5146517 (s : real -> Prop) : (term258 s) = (term253 s).
Proof. exact (MK_COMB (@lem5146516 s) (@lem5146515 s)). Qed.
Lemma lem5146518 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5146519 (s : real -> Prop) : (term263 s) = (term264 s).
Proof. exact (MK_COMB (@lem5146518) (@lem5146517 s)). Qed.
Lemma lem5146520 (x : real) (s : real -> Prop) : (term260 s x) = (term249 x s).
Proof. exact (eq_refl (term260 s x)). Qed.
Lemma lem5146521 (s : real -> Prop) : (term231 s) = (term231 s).
Proof. exact (eq_refl (term231 s)). Qed.
Lemma lem5146522 (x : real) (s : real -> Prop) : (term265 s x) = (term266 x s).
Proof. exact (MK_COMB (@lem5146521 s) (@lem5146520 x s)). Qed.
Lemma lem5146523 (s : real -> Prop) : (term267 s) = (term268 s).
Proof. exact (fun_ext (fun x : real => @lem5146522 x s)). Qed.
Lemma lem5146524 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146525 (s : real -> Prop) : (term259 s) = (term269 s).
Proof. exact (MK_COMB (@lem5146524) (@lem5146523 s)). Qed.
Lemma lem5146526 (s : real -> Prop) : ((term258 s) = (term259 s)) = ((term253 s) = (term269 s)).
Proof. exact (MK_COMB (@lem5146519 s) (@lem5146525 s)). Qed.
Lemma lem5146527 (s : real -> Prop) : (term253 s) = (term269 s).
Proof. exact (EQ_MP (@lem5146526 s) (@lem5146511 s)). Qed.
Lemma lem5146528 (s : real -> Prop) : (term233 s) = (term269 s).
Proof. exact (TRANS (@lem5146507 s) (@lem5146527 s)). Qed.
Lemma lem5146529 : term234 = term270.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5146528 s)). Qed.
Lemma lem5146530 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5146531 : term235 = term271.
Proof. exact (MK_COMB (@lem5146530) (@lem5146529)). Qed.
Lemma lem5146560 (x : real) (s : real -> Prop) : (term266 x s) = (term272 x s).
Proof. exact (@lem19490 (term242 s) (term223 s) (term226 x s)). Qed.
Lemma lem5146561 (s : real -> Prop) : (term268 s) = (term273 s).
Proof. exact (fun_ext (fun x : real => @lem5146560 x s)). Qed.
Lemma lem5146562 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146563 (s : real -> Prop) : (term269 s) = (term274 s).
Proof. exact (MK_COMB (@lem5146562) (@lem5146561 s)). Qed.
Lemma lem5146564 : term270 = term275.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5146563 s)). Qed.
Lemma lem5146565 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5146566 : term271 = term276.
Proof. exact (MK_COMB (@lem5146565) (@lem5146564)). Qed.
Lemma lem5146567 : term235 = term276.
Proof. exact (TRANS (@lem5146531) (@lem5146566)). Qed.
Lemma lem5146568 (h1 : term17) : term276.
Proof. exact (EQ_MP (@lem5146567) (@lem5146373 h1)). Qed.
Lemma lem5146588 (s : real -> Prop) (a : real) (x : real) : (term48 s a x) = (term48 s a x).
Proof. exact (eq_refl (term48 s a x)). Qed.
Lemma lem5146589 (s : real -> Prop) (a : real) : (term56 s a) = (term56 s a).
Proof. exact (fun_ext (fun x : real => @lem5146588 s a x)). Qed.
Lemma lem5146590 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146592 (s : real -> Prop) (a : real) : (term57 s a) = (term57 s a).
Proof. exact (MK_COMB (@lem5146590) (@lem5146589 s a)). Qed.
Lemma lem5146593 (s : real -> Prop) (a : real) (h1 : term62 s a) : term57 s a.
Proof. exact (EQ_MP (@lem5146592 s a) (@lem5146455 s a h1)). Qed.
Lemma lem5146607 (y : real) (x : real) (z : real) : (term212 y x z) = (term212 y x z).
Proof. exact (eq_refl (term212 y x z)). Qed.
Lemma lem5146608 (y : real) (x : real) : (term214 y x) = (term214 y x).
Proof. exact (fun_ext (fun z : real => @lem5146607 y x z)). Qed.
Lemma lem5146609 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146610 (y : real) (x : real) : (term215 y x) = (term215 y x).
Proof. exact (MK_COMB (@lem5146609) (@lem5146608 y x)). Qed.
Lemma lem5146611 (x : real) : (term216 x) = (term216 x).
Proof. exact (fun_ext (fun y : real => @lem5146610 y x)). Qed.
Lemma lem5146612 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146613 (x : real) : (term217 x) = (term217 x).
Proof. exact (MK_COMB (@lem5146612) (@lem5146611 x)). Qed.
Lemma lem5146614 : term218 = term218.
Proof. exact (fun_ext (fun x : real => @lem5146613 x)). Qed.
Lemma lem5146615 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146617 : term219 = term219.
Proof. exact (MK_COMB (@lem5146615) (@lem5146614)). Qed.
Lemma lem5146618 (h1 : term37) : term219.
Proof. exact (EQ_MP (@lem5146617) (@lem5146323 h1)). Qed.
Lemma lem5146620 {A : Type'} (P : Prop) (Q : A -> Prop) : (term236 A P Q) = (term237 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5146621 (P : Prop) (Q : real -> Prop) : (term238 P Q) = (term239 P Q).
Proof. exact (@lem5146620 real P Q). Qed.
Lemma lem5146622 (s : real -> Prop) : (term240 s) = (term241 s).
Proof. exact (@lem5146621 (term242 s) (term227 s)). Qed.
Lemma lem5146623 (x : real) (s : real -> Prop) : (term243 s x) = (term226 x s).
Proof. exact (eq_refl (term243 s x)). Qed.
Lemma lem5146624 (s : real -> Prop) : (term244 s) = (term227 s).
Proof. exact (fun_ext (fun x : real => @lem5146623 x s)). Qed.
Lemma lem5146625 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146626 (s : real -> Prop) : (term245 s) = (term228 s).
Proof. exact (MK_COMB (@lem5146625) (@lem5146624 s)). Qed.
Lemma lem5146627 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5146628 (s : real -> Prop) : (term240 s) = (term229 s).
Proof. exact (MK_COMB (@lem5146627 s) (@lem5146626 s)). Qed.
Lemma lem5146629 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5146630 (s : real -> Prop) : (term246 s) = (term247 s).
Proof. exact (MK_COMB (@lem5146629) (@lem5146628 s)). Qed.
Lemma lem5146631 (x : real) (s : real -> Prop) : (term243 s x) = (term226 x s).
Proof. exact (eq_refl (term243 s x)). Qed.
Lemma lem5146632 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5146633 (x : real) (s : real -> Prop) : (term248 s x) = (term249 x s).
Proof. exact (MK_COMB (@lem5146632 s) (@lem5146631 x s)). Qed.
Lemma lem5146634 (s : real -> Prop) : (term250 s) = (term251 s).
Proof. exact (fun_ext (fun x : real => @lem5146633 x s)). Qed.
Lemma lem5146635 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146636 (s : real -> Prop) : (term241 s) = (term252 s).
Proof. exact (MK_COMB (@lem5146635) (@lem5146634 s)). Qed.
Lemma lem5146637 (s : real -> Prop) : ((term240 s) = (term241 s)) = ((term229 s) = (term252 s)).
Proof. exact (MK_COMB (@lem5146630 s) (@lem5146636 s)). Qed.
Lemma lem5146638 (s : real -> Prop) : (term229 s) = (term252 s).
Proof. exact (EQ_MP (@lem5146637 s) (@lem5146622 s)). Qed.
Lemma lem5146639 (s : real -> Prop) : (term231 s) = (term231 s).
Proof. exact (eq_refl (term231 s)). Qed.
Lemma lem5146640 (s : real -> Prop) : (term233 s) = (term253 s).
Proof. exact (MK_COMB (@lem5146639 s) (@lem5146638 s)). Qed.
Lemma lem5146642 {A : Type'} (P : Prop) (Q : A -> Prop) : (term254 A P Q) = (term255 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5146643 (P : Prop) (Q : real -> Prop) : (term256 P Q) = (term257 P Q).
Proof. exact (@lem5146642 real P Q). Qed.
Lemma lem5146644 (s : real -> Prop) : (term258 s) = (term259 s).
Proof. exact (@lem5146643 (term223 s) (term251 s)). Qed.
Lemma lem5146645 (x : real) (s : real -> Prop) : (term260 s x) = (term249 x s).
Proof. exact (eq_refl (term260 s x)). Qed.
Lemma lem5146646 (s : real -> Prop) : (term261 s) = (term251 s).
Proof. exact (fun_ext (fun x : real => @lem5146645 x s)). Qed.
Lemma lem5146647 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146648 (s : real -> Prop) : (term262 s) = (term252 s).
Proof. exact (MK_COMB (@lem5146647) (@lem5146646 s)). Qed.
Lemma lem5146649 (s : real -> Prop) : (term231 s) = (term231 s).
Proof. exact (eq_refl (term231 s)). Qed.
Lemma lem5146650 (s : real -> Prop) : (term258 s) = (term253 s).
Proof. exact (MK_COMB (@lem5146649 s) (@lem5146648 s)). Qed.
Lemma lem5146651 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5146652 (s : real -> Prop) : (term263 s) = (term264 s).
Proof. exact (MK_COMB (@lem5146651) (@lem5146650 s)). Qed.
Lemma lem5146653 (x : real) (s : real -> Prop) : (term260 s x) = (term249 x s).
Proof. exact (eq_refl (term260 s x)). Qed.
Lemma lem5146654 (s : real -> Prop) : (term231 s) = (term231 s).
Proof. exact (eq_refl (term231 s)). Qed.
Lemma lem5146655 (x : real) (s : real -> Prop) : (term265 s x) = (term266 x s).
Proof. exact (MK_COMB (@lem5146654 s) (@lem5146653 x s)). Qed.
Lemma lem5146656 (s : real -> Prop) : (term267 s) = (term268 s).
Proof. exact (fun_ext (fun x : real => @lem5146655 x s)). Qed.
Lemma lem5146657 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146658 (s : real -> Prop) : (term259 s) = (term269 s).
Proof. exact (MK_COMB (@lem5146657) (@lem5146656 s)). Qed.
Lemma lem5146659 (s : real -> Prop) : ((term258 s) = (term259 s)) = ((term253 s) = (term269 s)).
Proof. exact (MK_COMB (@lem5146652 s) (@lem5146658 s)). Qed.
Lemma lem5146660 (s : real -> Prop) : (term253 s) = (term269 s).
Proof. exact (EQ_MP (@lem5146659 s) (@lem5146644 s)). Qed.
Lemma lem5146661 (s : real -> Prop) : (term233 s) = (term269 s).
Proof. exact (TRANS (@lem5146640 s) (@lem5146660 s)). Qed.
Lemma lem5146662 : term234 = term270.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5146661 s)). Qed.
Lemma lem5146663 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5146664 : term235 = term271.
Proof. exact (MK_COMB (@lem5146663) (@lem5146662)). Qed.
Lemma lem5146693 (x : real) (s : real -> Prop) : (term266 x s) = (term272 x s).
Proof. exact (@lem19490 (term242 s) (term223 s) (term226 x s)). Qed.
Lemma lem5146694 (s : real -> Prop) : (term268 s) = (term273 s).
Proof. exact (fun_ext (fun x : real => @lem5146693 x s)). Qed.
Lemma lem5146695 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5146696 (s : real -> Prop) : (term269 s) = (term274 s).
Proof. exact (MK_COMB (@lem5146695) (@lem5146694 s)). Qed.
Lemma lem5146697 : term270 = term275.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5146696 s)). Qed.
Lemma lem5146698 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5146699 : term271 = term276.
Proof. exact (MK_COMB (@lem5146698) (@lem5146697)). Qed.
Lemma lem5146700 : term235 = term276.
Proof. exact (TRANS (@lem5146664) (@lem5146699)). Qed.
Lemma lem5146701 (h1 : term17) : term276.
Proof. exact (EQ_MP (@lem5146700) (@lem5146373 h1)). Qed.
Lemma lem5146731 (_67179 : real -> Prop) (h1 : term17) : term277 _67179.
Proof. exact (@lem5146568 h1 _67179). Qed.
Lemma lem5146732 (_67179 : real -> Prop) : (term277 _67179) = (term274 _67179).
Proof. exact (eq_refl (term277 _67179)). Qed.
Lemma lem5146733 (_67179 : real -> Prop) (h1 : term17) : term274 _67179.
Proof. exact (EQ_MP (@lem5146732 _67179) (@lem5146731 _67179 h1)). Qed.
Lemma lem5146734 (_67179 : real -> Prop) (_67180 : real) (h1 : term17) : term278 _67179 _67180.
Proof. exact (@lem5146733 _67179 h1 _67180). Qed.
Lemma lem5146735 (_67180 : real) (_67179 : real -> Prop) : (term278 _67179 _67180) = (term272 _67180 _67179).
Proof. exact (eq_refl (term278 _67179 _67180)). Qed.
Lemma lem5146736 (_67180 : real) (_67179 : real -> Prop) (h1 : term17) : term272 _67180 _67179.
Proof. exact (EQ_MP (@lem5146735 _67180 _67179) (@lem5146734 _67179 _67180 h1)). Qed.
Lemma lem5146737 (_67181 : real) (s : real -> Prop) (a : real) (h1 : term62 s a) : term279 s a _67181.
Proof. exact (@lem5146593 s a h1 _67181). Qed.
Lemma lem5146738 (s : real -> Prop) (a : real) (_67181 : real) : (term279 s a _67181) = (term48 s a _67181).
Proof. exact (eq_refl (term279 s a _67181)). Qed.
Lemma lem5146740 (_67182 : real) (h1 : term37) : term280 _67182.
Proof. exact (@lem5146618 h1 _67182). Qed.
Lemma lem5146741 (_67182 : real) : (term280 _67182) = (term217 _67182).
Proof. exact (eq_refl (term280 _67182)). Qed.
Lemma lem5146742 (_67182 : real) (h1 : term37) : term217 _67182.
Proof. exact (EQ_MP (@lem5146741 _67182) (@lem5146740 _67182 h1)). Qed.
Lemma lem5146743 (_67182 : real) (_67183 : real) (h1 : term37) : term281 _67182 _67183.
Proof. exact (@lem5146742 _67182 h1 _67183). Qed.
Lemma lem5146744 (_67183 : real) (_67182 : real) : (term281 _67182 _67183) = (term215 _67183 _67182).
Proof. exact (eq_refl (term281 _67182 _67183)). Qed.
Lemma lem5146745 (_67183 : real) (_67182 : real) (h1 : term37) : term215 _67183 _67182.
Proof. exact (EQ_MP (@lem5146744 _67183 _67182) (@lem5146743 _67182 _67183 h1)). Qed.
Lemma lem5146746 (_67183 : real) (_67182 : real) (_67184 : real) (h1 : term37) : term282 _67183 _67182 _67184.
Proof. exact (@lem5146745 _67183 _67182 h1 _67184). Qed.
Lemma lem5146747 (_67183 : real) (_67182 : real) (_67184 : real) : (term282 _67183 _67182 _67184) = (term212 _67183 _67182 _67184).
Proof. exact (eq_refl (term282 _67183 _67182 _67184)). Qed.
Lemma lem5146748 (_67183 : real) (_67182 : real) (_67184 : real) (h1 : term37) : term212 _67183 _67182 _67184.
Proof. exact (EQ_MP (@lem5146747 _67183 _67182 _67184) (@lem5146746 _67183 _67182 _67184 h1)). Qed.
Lemma lem5146749 (_67185 : real -> Prop) (h1 : term17) : term277 _67185.
Proof. exact (@lem5146701 h1 _67185). Qed.
Lemma lem5146750 (_67185 : real -> Prop) : (term277 _67185) = (term274 _67185).
Proof. exact (eq_refl (term277 _67185)). Qed.
Lemma lem5146751 (_67185 : real -> Prop) (h1 : term17) : term274 _67185.
Proof. exact (EQ_MP (@lem5146750 _67185) (@lem5146749 _67185 h1)). Qed.
Lemma lem5146752 (_67185 : real -> Prop) (_67186 : real) (h1 : term17) : term278 _67185 _67186.
Proof. exact (@lem5146751 _67185 h1 _67186). Qed.
Lemma lem5146753 (_67186 : real) (_67185 : real -> Prop) : (term278 _67185 _67186) = (term272 _67186 _67185).
Proof. exact (eq_refl (term278 _67185 _67186)). Qed.
Lemma lem5146754 (_67186 : real) (_67185 : real -> Prop) (h1 : term17) : term272 _67186 _67185.
Proof. exact (EQ_MP (@lem5146753 _67186 _67185) (@lem5146752 _67185 _67186 h1)). Qed.
Lemma lem5146756 (_67179 : real -> Prop) (h1 : term17) : term283 _67179.
Proof. exact (proj1 (@lem5146736 (@el real) _67179 h1)). Qed.
Lemma lem5146757 (_67186 : real) (_67185 : real -> Prop) (h1 : term17) : term284 _67186 _67185.
Proof. exact (proj2 (@lem5146754 _67186 _67185 h1)). Qed.
Lemma lem5146774 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term225 s.
Proof. exact (proj2 (@lem5146450 s a x h1)). Qed.
Lemma lem5146782 (_67181 : real) (s : real -> Prop) (a : real) (h1 : term62 s a) : term48 s a _67181.
Proof. exact (EQ_MP (@lem5146738 s a _67181) (@lem5146737 _67181 s a h1)). Qed.
Lemma lem5146793 (_67179 : real -> Prop) : (term283 _67179) = (term285 _67179).
Proof. exact (@lem5145284 (term286 _67179) (_67179 = (@EMPTY real)) (term242 _67179)). Qed.
Lemma lem5146794 (_67179 : real -> Prop) (h1 : term17) : term285 _67179.
Proof. exact (EQ_MP (@lem5146793 _67179) (@lem5146756 _67179 h1)). Qed.
Lemma lem5146821 (_67183 : real) (_67182 : real) (_67184 : real) : (term212 _67183 _67182 _67184) = (term287 _67183 _67182 _67184).
Proof. exact (@lem5145284 (term288 _67182 _67183) (term288 _67183 _67184) (real_le _67182 _67184)). Qed.
Lemma lem5146822 (_67183 : real) (_67182 : real) (_67184 : real) (h1 : term37) : term287 _67183 _67182 _67184.
Proof. exact (EQ_MP (@lem5146821 _67183 _67182 _67184) (@lem5146748 _67183 _67182 _67184 h1)). Qed.
Lemma lem5146828 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : term135 a s.
Proof. exact (proj1 (@lem5146454 s a x h1)). Qed.
Lemma lem5146859 (_67186 : real) (_67185 : real -> Prop) : (term284 _67186 _67185) = (term289 _67186 _67185).
Proof. exact (@lem5145284 (term286 _67185) (_67185 = (@EMPTY real)) (term226 _67186 _67185)). Qed.
Lemma lem5146860 (_67186 : real) (_67185 : real -> Prop) (h1 : term17) : term289 _67186 _67185.
Proof. exact (EQ_MP (@lem5146859 _67186 _67185) (@lem5146757 _67186 _67185 h1)). Qed.
Lemma lem5146924 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : @FINITE real s.
Proof. exact (proj1 (@lem5146450 s a x h1)). Qed.
Lemma lem5146925 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term290 s.
Proof. exact (fun h0 : term286 s => @lem5146924 s a x h1). Qed.
Lemma lem5146927 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5146928 (s : real -> Prop) : (term290 s) = (@FINITE real s).
Proof. exact (@lem5146927 (@FINITE real s)). Qed.
Lemma lem5146929 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : @FINITE real s.
Proof. exact (EQ_MP (@lem5146928 s) (@lem5146925 s a x h1)). Qed.
Lemma lem5146931 (s : real -> Prop) (a : real) (h1 : term62 s a) : term42 a s.
Proof. exact (proj1 (@lem5146453 s a h1)). Qed.
Lemma lem5146932 (s : real -> Prop) (a : real) (h1 : term62 s a) : term292 a s.
Proof. exact (fun h0 : term135 a s => @lem5146931 s a h1). Qed.
Lemma lem5146934 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5146935 (a : real) (s : real -> Prop) : (term292 a s) = (term42 a s).
Proof. exact (@lem5146934 (term42 a s)). Qed.
Lemma lem5146936 (s : real -> Prop) (a : real) (h1 : term62 s a) : term42 a s.
Proof. exact (EQ_MP (@lem5146935 a s) (@lem5146932 s a h1)). Qed.
Lemma lem5146938 (b : Prop) (a : Prop) : (a \/ b) = (term293 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5146939 (a : real) (_67181 : real) (s : real -> Prop) : (term48 s a _67181) = (term294 a _67181 s).
Proof. exact (@lem5146938 (term288 a _67181) (term295 _67181 s)). Qed.
Lemma lem5146941 (a : Prop) : (term296 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5146942 (a : real) (_67181 : real) : (term297 a _67181) = (real_le a _67181).
Proof. exact (@lem5146941 (real_le a _67181)). Qed.
Lemma lem5146943 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5146944 (a : real) (_67181 : real) : (term298 a _67181) = (term299 a _67181).
Proof. exact (MK_COMB (@lem5146943) (@lem5146942 a _67181)). Qed.
Lemma lem5146945 (_67181 : real) (s : real -> Prop) : (term295 _67181 s) = (term295 _67181 s).
Proof. exact (eq_refl (term295 _67181 s)). Qed.
Lemma lem5146946 (a : real) (_67181 : real) (s : real -> Prop) : (term294 a _67181 s) = (term300 a _67181 s).
Proof. exact (MK_COMB (@lem5146944 a _67181) (@lem5146945 _67181 s)). Qed.
Lemma lem5146947 (a : real) (_67181 : real) (s : real -> Prop) : (term48 s a _67181) = (term300 a _67181 s).
Proof. exact (TRANS (@lem5146939 a _67181 s) (@lem5146946 a _67181 s)). Qed.
Lemma lem5146950 (_67181 : real) (s : real -> Prop) (a : real) (h1 : term62 s a) : term300 a _67181 s.
Proof. exact (EQ_MP (@lem5146947 a _67181 s) (@lem5146782 _67181 s a h1)). Qed.
Lemma lem5146951 (s : real -> Prop) (a : real) (h1 : term62 s a) : term301 a s.
Proof. exact (@lem5146950 (sup s) s a h1). Qed.
Lemma lem5146954 (s : real -> Prop) (a : real) (h1 : term62 s a) : term302 s.
Proof. exact (@lem5146951 s a h1 (@lem5146936 s a h1)). Qed.
Lemma lem5146955 (s : real -> Prop) (a : real) (h1 : term62 s a) : term303 s.
Proof. exact (fun h0 : term242 s => @lem5146954 s a h1). Qed.
Lemma lem5146957 (p : Prop) : (term304 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5146958 (s : real -> Prop) : (term303 s) = (term302 s).
Proof. exact (@lem5146957 (term242 s)). Qed.
Lemma lem5146959 (s : real -> Prop) (a : real) (h1 : term62 s a) : term302 s.
Proof. exact (EQ_MP (@lem5146958 s) (@lem5146955 s a h1)). Qed.
Lemma lem5146965 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5146966 (_67179 : real -> Prop) : (term285 _67179) = (term305 _67179).
Proof. exact (@lem5146965 (_67179 = (@EMPTY real)) (term286 _67179) (term242 _67179)). Qed.
Lemma lem5146982 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5146983 (_67179 : real -> Prop) : (term306 _67179) = (term307 _67179).
Proof. exact (@lem5146982 (term242 _67179) (term286 _67179)). Qed.
Lemma lem5146989 (_67179 : real -> Prop) : (term308 _67179) = (term308 _67179).
Proof. exact (eq_refl (term308 _67179)). Qed.
Lemma lem5146990 (_67179 : real -> Prop) : (term305 _67179) = (term309 _67179).
Proof. exact (MK_COMB (@lem5146989 _67179) (@lem5146983 _67179)). Qed.
Lemma lem5147001 (_67179 : real -> Prop) : (term285 _67179) = (term309 _67179).
Proof. exact (TRANS (@lem5146966 _67179) (@lem5146990 _67179)). Qed.
Lemma lem5147002 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5147003 (_67179 : real -> Prop) : (term310 _67179) = (term311 _67179).
Proof. exact (MK_COMB (@lem5147002) (@lem5147001 _67179)). Qed.
Lemma lem5147019 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5147020 (_67179 : real -> Prop) : (term306 _67179) = (term307 _67179).
Proof. exact (@lem5147019 (term242 _67179) (term286 _67179)). Qed.
Lemma lem5147026 (_67179 : real -> Prop) : (term308 _67179) = (term308 _67179).
Proof. exact (eq_refl (term308 _67179)). Qed.
Lemma lem5147027 (_67179 : real -> Prop) : (term305 _67179) = (term309 _67179).
Proof. exact (MK_COMB (@lem5147026 _67179) (@lem5147020 _67179)). Qed.
Lemma lem5147038 (_67179 : real -> Prop) : ((term285 _67179) = (term305 _67179)) = ((term309 _67179) = (term309 _67179)).
Proof. exact (MK_COMB (@lem5147003 _67179) (@lem5147027 _67179)). Qed.
Lemma lem5147040 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5147041 (x : Prop) : (x = x) = True.
Proof. exact (@lem5147040 Prop x). Qed.
Lemma lem5147042 (_67179 : real -> Prop) : ((term309 _67179) = (term309 _67179)) = True.
Proof. exact (@lem5147041 (term309 _67179)). Qed.
Lemma lem5147043 (_67179 : real -> Prop) : ((term285 _67179) = (term305 _67179)) = True.
Proof. exact (TRANS (@lem5147038 _67179) (@lem5147042 _67179)). Qed.
Lemma lem5147044 (_67179 : real -> Prop) : True = ((term285 _67179) = (term305 _67179)).
Proof. exact (SYM (@lem5147043 _67179)). Qed.
Lemma lem5147045 (_67179 : real -> Prop) : (term285 _67179) = (term305 _67179).
Proof. exact (EQ_MP (@lem5147044 _67179) (@lem0)). Qed.
Lemma lem5147046 (_67179 : real -> Prop) (h1 : term17) : term305 _67179.
Proof. exact (EQ_MP (@lem5147045 _67179) (@lem5146794 _67179 h1)). Qed.
Lemma lem5147048 (b : Prop) (a : Prop) : (a \/ b) = (term293 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5147049 (_67179 : real -> Prop) : (term305 _67179) = (term312 _67179).
Proof. exact (@lem5147048 (term306 _67179) (_67179 = (@EMPTY real))). Qed.
Lemma lem5147051 (a : Prop) (b : Prop) : (term313 a b) = (term314 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5147052 (_67179 : real -> Prop) : (term315 _67179) = (term316 _67179).
Proof. exact (@lem5147051 (term286 _67179) (term242 _67179)). Qed.
Lemma lem5147054 (a : Prop) : (term296 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5147055 (_67179 : real -> Prop) : (term317 _67179) = (@FINITE real _67179).
Proof. exact (@lem5147054 (@FINITE real _67179)). Qed.
Lemma lem5147056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5147057 (_67179 : real -> Prop) : (term318 _67179) = (term319 _67179).
Proof. exact (MK_COMB (@lem5147056) (@lem5147055 _67179)). Qed.
Lemma lem5147058 (_67179 : real -> Prop) : (term302 _67179) = (term302 _67179).
Proof. exact (eq_refl (term302 _67179)). Qed.
Lemma lem5147059 (_67179 : real -> Prop) : (term316 _67179) = (term320 _67179).
Proof. exact (MK_COMB (@lem5147057 _67179) (@lem5147058 _67179)). Qed.
Lemma lem5147060 (_67179 : real -> Prop) : (term315 _67179) = (term320 _67179).
Proof. exact (TRANS (@lem5147052 _67179) (@lem5147059 _67179)). Qed.
Lemma lem5147061 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5147062 (_67179 : real -> Prop) : (term321 _67179) = (term322 _67179).
Proof. exact (MK_COMB (@lem5147061) (@lem5147060 _67179)). Qed.
Lemma lem5147063 (_67179 : real -> Prop) : (_67179 = (@EMPTY real)) = (_67179 = (@EMPTY real)).
Proof. exact (eq_refl (_67179 = (@EMPTY real))). Qed.
Lemma lem5147064 (_67179 : real -> Prop) : (term312 _67179) = (term323 _67179).
Proof. exact (MK_COMB (@lem5147062 _67179) (@lem5147063 _67179)). Qed.
Lemma lem5147065 (_67179 : real -> Prop) : (term305 _67179) = (term323 _67179).
Proof. exact (TRANS (@lem5147049 _67179) (@lem5147064 _67179)). Qed.
Lemma lem5147067 (x : real) (s : real -> Prop) (a : real) (h1 : term199 s a x) (h2 : term62 s a) : term320 s.
Proof. exact (conj (@lem5146929 s a x h1) (@lem5146959 s a h2)). Qed.
Lemma lem5147069 (_67179 : real -> Prop) (h1 : term17) : term323 _67179.
Proof. exact (EQ_MP (@lem5147065 _67179) (@lem5147046 _67179 h1)). Qed.
Lemma lem5147070 (s : real -> Prop) (h1 : term17) : term323 s.
Proof. exact (@lem5147069 s h1). Qed.
Lemma lem5147073 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s a x) (h3 : term62 s a) : s = (@EMPTY real).
Proof. exact (@lem5147070 s h1 (@lem5147067 x s a h2 h3)). Qed.
Lemma lem5147074 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s a x) (h3 : term62 s a) : term324 s.
Proof. exact (fun h0 : term225 s => @lem5147073 x s a h1 h2 h3). Qed.
Lemma lem5147076 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5147077 (s : real -> Prop) : (term324 s) = (s = (@EMPTY real)).
Proof. exact (@lem5147076 (s = (@EMPTY real))). Qed.
Lemma lem5147078 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s a x) (h3 : term62 s a) : s = (@EMPTY real).
Proof. exact (EQ_MP (@lem5147077 s) (@lem5147074 x s a h1 h2 h3)). Qed.
Lemma lem5147081 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5147083 (s : real -> Prop) : (term225 s) = (term325 s).
Proof. exact (@lem5147081 (s = (@EMPTY real))). Qed.
Lemma lem5147086 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term325 s.
Proof. exact (EQ_MP (@lem5147083 s) (@lem5146774 s a x h1)). Qed.
Lemma lem5147089 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s a x) (h3 : term62 s a) : False.
Proof. exact (@lem5147086 s a x h2 (@lem5147078 x s a h1 h2 h3)). Qed.
Lemma lem5147090 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s a x) (h3 : term62 s a) : term326.
Proof. exact (fun h0 : ~ False => @lem5147089 x s a h1 h2 h3). Qed.
Lemma lem5147092 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5147093 : term326 = False.
Proof. exact (@lem5147092 False). Qed.
Lemma lem5147094 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s a x) (h3 : term62 s a) : False.
Proof. exact (EQ_MP (@lem5147093) (@lem5147090 x s a h1 h2 h3)). Qed.
Lemma lem5147158 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : real_le a x.
Proof. exact (proj2 (@lem5146457 s a x h1)). Qed.
Lemma lem5147159 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : term327 a x.
Proof. exact (fun h0 : term288 a x => @lem5147158 s a x h1). Qed.
Lemma lem5147161 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5147162 (a : real) (x : real) : (term327 a x) = (real_le a x).
Proof. exact (@lem5147161 (real_le a x)). Qed.
Lemma lem5147163 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : real_le a x.
Proof. exact (EQ_MP (@lem5147162 a x) (@lem5147159 s a x h1)). Qed.
Lemma lem5147165 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : @FINITE real s.
Proof. exact (proj1 (@lem5146450 s a x h1)). Qed.
Lemma lem5147166 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term290 s.
Proof. exact (fun h0 : term286 s => @lem5147165 s a x h1). Qed.
Lemma lem5147168 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5147169 (s : real -> Prop) : (term290 s) = (@FINITE real s).
Proof. exact (@lem5147168 (@FINITE real s)). Qed.
Lemma lem5147170 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : @FINITE real s.
Proof. exact (EQ_MP (@lem5147169 s) (@lem5147166 s a x h1)). Qed.
Lemma lem5147172 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term225 s.
Proof. exact (proj2 (@lem5146450 s a x h1)). Qed.
Lemma lem5147173 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term328 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5147172 s a x h1). Qed.
Lemma lem5147175 (p : Prop) : (term304 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5147176 (s : real -> Prop) : (term328 s) = (term225 s).
Proof. exact (@lem5147175 (s = (@EMPTY real))). Qed.
Lemma lem5147177 (s : real -> Prop) (a : real) (x : real) (h1 : term199 s a x) : term225 s.
Proof. exact (EQ_MP (@lem5147176 s) (@lem5147173 s a x h1)). Qed.
Lemma lem5147179 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : @IN real x s.
Proof. exact (proj1 (@lem5146457 s a x h1)). Qed.
Lemma lem5147180 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : term329 x s.
Proof. exact (fun h0 : term295 x s => @lem5147179 s a x h1). Qed.
Lemma lem5147182 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5147183 (x : real) (s : real -> Prop) : (term329 x s) = (@IN real x s).
Proof. exact (@lem5147182 (@IN real x s)). Qed.
Lemma lem5147184 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : @IN real x s.
Proof. exact (EQ_MP (@lem5147183 x s) (@lem5147180 s a x h1)). Qed.
Lemma lem5147190 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5147191 (_67186 : real) (_67185 : real -> Prop) : (term289 _67186 _67185) = (term330 _67186 _67185).
Proof. exact (@lem5147190 (_67185 = (@EMPTY real)) (term286 _67185) (term226 _67186 _67185)). Qed.
Lemma lem5147217 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5147218 (_67186 : real) (_67185 : real -> Prop) : (term226 _67186 _67185) = (term331 _67186 _67185).
Proof. exact (@lem5147217 (term42 _67186 _67185) (term295 _67186 _67185)). Qed.
Lemma lem5147224 (_67185 : real -> Prop) : (term221 _67185) = (term221 _67185).
Proof. exact (eq_refl (term221 _67185)). Qed.
Lemma lem5147225 (_67186 : real) (_67185 : real -> Prop) : (term332 _67186 _67185) = (term333 _67186 _67185).
Proof. exact (MK_COMB (@lem5147224 _67185) (@lem5147218 _67186 _67185)). Qed.
Lemma lem5147229 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5147230 (_67186 : real) (_67185 : real -> Prop) : (term333 _67186 _67185) = (term334 _67186 _67185).
Proof. exact (@lem5147229 (term42 _67186 _67185) (term286 _67185) (term295 _67186 _67185)). Qed.
Lemma lem5147246 (_67186 : real) (_67185 : real -> Prop) : (term332 _67186 _67185) = (term334 _67186 _67185).
Proof. exact (TRANS (@lem5147225 _67186 _67185) (@lem5147230 _67186 _67185)). Qed.
Lemma lem5147247 (_67185 : real -> Prop) : (term308 _67185) = (term308 _67185).
Proof. exact (eq_refl (term308 _67185)). Qed.
Lemma lem5147248 (_67186 : real) (_67185 : real -> Prop) : (term330 _67186 _67185) = (term335 _67186 _67185).
Proof. exact (MK_COMB (@lem5147247 _67185) (@lem5147246 _67186 _67185)). Qed.
Lemma lem5147259 (_67186 : real) (_67185 : real -> Prop) : (term289 _67186 _67185) = (term335 _67186 _67185).
Proof. exact (TRANS (@lem5147191 _67186 _67185) (@lem5147248 _67186 _67185)). Qed.
Lemma lem5147260 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5147261 (_67186 : real) (_67185 : real -> Prop) : (term336 _67186 _67185) = (term337 _67186 _67185).
Proof. exact (MK_COMB (@lem5147260) (@lem5147259 _67186 _67185)). Qed.
Lemma lem5147275 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5147276 (_67186 : real) (_67185 : real -> Prop) : (term338 _67186 _67185) = (term339 _67186 _67185).
Proof. exact (@lem5147275 (_67185 = (@EMPTY real)) (term286 _67185) (term295 _67186 _67185)). Qed.
Lemma lem5147294 (_67186 : real) (_67185 : real -> Prop) : (term340 _67186 _67185) = (term340 _67186 _67185).
Proof. exact (eq_refl (term340 _67186 _67185)). Qed.
Lemma lem5147295 (_67186 : real) (_67185 : real -> Prop) : (term341 _67186 _67185) = (term342 _67186 _67185).
Proof. exact (MK_COMB (@lem5147294 _67186 _67185) (@lem5147276 _67186 _67185)). Qed.
Lemma lem5147299 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5147300 (_67186 : real) (_67185 : real -> Prop) : (term342 _67186 _67185) = (term335 _67186 _67185).
Proof. exact (@lem5147299 (_67185 = (@EMPTY real)) (term42 _67186 _67185) (term343 _67186 _67185)). Qed.
Lemma lem5147328 (_67186 : real) (_67185 : real -> Prop) : (term341 _67186 _67185) = (term335 _67186 _67185).
Proof. exact (TRANS (@lem5147295 _67186 _67185) (@lem5147300 _67186 _67185)). Qed.
Lemma lem5147329 (_67186 : real) (_67185 : real -> Prop) : ((term289 _67186 _67185) = (term341 _67186 _67185)) = ((term335 _67186 _67185) = (term335 _67186 _67185)).
Proof. exact (MK_COMB (@lem5147261 _67186 _67185) (@lem5147328 _67186 _67185)). Qed.
Lemma lem5147331 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5147332 (x : Prop) : (x = x) = True.
Proof. exact (@lem5147331 Prop x). Qed.
Lemma lem5147333 (_67186 : real) (_67185 : real -> Prop) : ((term335 _67186 _67185) = (term335 _67186 _67185)) = True.
Proof. exact (@lem5147332 (term335 _67186 _67185)). Qed.
Lemma lem5147334 (_67186 : real) (_67185 : real -> Prop) : ((term289 _67186 _67185) = (term341 _67186 _67185)) = True.
Proof. exact (TRANS (@lem5147329 _67186 _67185) (@lem5147333 _67186 _67185)). Qed.
Lemma lem5147335 (_67186 : real) (_67185 : real -> Prop) : True = ((term289 _67186 _67185) = (term341 _67186 _67185)).
Proof. exact (SYM (@lem5147334 _67186 _67185)). Qed.
Lemma lem5147336 (_67186 : real) (_67185 : real -> Prop) : (term289 _67186 _67185) = (term341 _67186 _67185).
Proof. exact (EQ_MP (@lem5147335 _67186 _67185) (@lem0)). Qed.
Lemma lem5147337 (_67186 : real) (_67185 : real -> Prop) (h1 : term17) : term341 _67186 _67185.
Proof. exact (EQ_MP (@lem5147336 _67186 _67185) (@lem5146860 _67186 _67185 h1)). Qed.
Lemma lem5147339 (b : Prop) (a : Prop) : (a \/ b) = (term293 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5147340 (_67186 : real) (_67185 : real -> Prop) : (term341 _67186 _67185) = (term344 _67186 _67185).
Proof. exact (@lem5147339 (term338 _67186 _67185) (term42 _67186 _67185)). Qed.
Lemma lem5147342 (a : Prop) (b : Prop) : (term313 a b) = (term314 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5147343 (_67186 : real) (_67185 : real -> Prop) : (term345 _67186 _67185) = (term346 _67186 _67185).
Proof. exact (@lem5147342 (term286 _67185) (term347 _67186 _67185)). Qed.
Lemma lem5147345 (a : Prop) : (term296 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5147346 (_67185 : real -> Prop) : (term317 _67185) = (@FINITE real _67185).
Proof. exact (@lem5147345 (@FINITE real _67185)). Qed.
Lemma lem5147347 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5147348 (_67185 : real -> Prop) : (term318 _67185) = (term319 _67185).
Proof. exact (MK_COMB (@lem5147347) (@lem5147346 _67185)). Qed.
Lemma lem5147350 (a : Prop) (b : Prop) : (term313 a b) = (term314 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5147351 (_67186 : real) (_67185 : real -> Prop) : (term348 _67186 _67185) = (term349 _67186 _67185).
Proof. exact (@lem5147350 (_67185 = (@EMPTY real)) (term295 _67186 _67185)). Qed.
Lemma lem5147353 (a : Prop) : (term296 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5147354 (_67186 : real) (_67185 : real -> Prop) : (term350 _67186 _67185) = (@IN real _67186 _67185).
Proof. exact (@lem5147353 (@IN real _67186 _67185)). Qed.
Lemma lem5147355 (_67185 : real -> Prop) : (term351 _67185) = (term351 _67185).
Proof. exact (eq_refl (term351 _67185)). Qed.
Lemma lem5147356 (_67186 : real) (_67185 : real -> Prop) : (term349 _67186 _67185) = (term352 _67186 _67185).
Proof. exact (MK_COMB (@lem5147355 _67185) (@lem5147354 _67186 _67185)). Qed.
Lemma lem5147357 (_67186 : real) (_67185 : real -> Prop) : (term348 _67186 _67185) = (term352 _67186 _67185).
Proof. exact (TRANS (@lem5147351 _67186 _67185) (@lem5147356 _67186 _67185)). Qed.
Lemma lem5147358 (_67186 : real) (_67185 : real -> Prop) : (term346 _67186 _67185) = (term353 _67186 _67185).
Proof. exact (MK_COMB (@lem5147348 _67185) (@lem5147357 _67186 _67185)). Qed.
Lemma lem5147359 (_67186 : real) (_67185 : real -> Prop) : (term345 _67186 _67185) = (term353 _67186 _67185).
Proof. exact (TRANS (@lem5147343 _67186 _67185) (@lem5147358 _67186 _67185)). Qed.
Lemma lem5147360 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5147361 (_67186 : real) (_67185 : real -> Prop) : (term354 _67186 _67185) = (term355 _67186 _67185).
Proof. exact (MK_COMB (@lem5147360) (@lem5147359 _67186 _67185)). Qed.
Lemma lem5147362 (_67186 : real) (_67185 : real -> Prop) : (term42 _67186 _67185) = (term42 _67186 _67185).
Proof. exact (eq_refl (term42 _67186 _67185)). Qed.
Lemma lem5147363 (_67186 : real) (_67185 : real -> Prop) : (term344 _67186 _67185) = (term356 _67186 _67185).
Proof. exact (MK_COMB (@lem5147361 _67186 _67185) (@lem5147362 _67186 _67185)). Qed.
Lemma lem5147364 (_67186 : real) (_67185 : real -> Prop) : (term341 _67186 _67185) = (term356 _67186 _67185).
Proof. exact (TRANS (@lem5147340 _67186 _67185) (@lem5147363 _67186 _67185)). Qed.
Lemma lem5147366 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) (h2 : term199 s a x) : term352 x s.
Proof. exact (conj (@lem5147177 s a x h2) (@lem5147184 s a x h1)). Qed.
Lemma lem5147367 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) (h2 : term199 s a x) : term353 x s.
Proof. exact (conj (@lem5147170 s a x h2) (@lem5147366 s a x h1 h2)). Qed.
Lemma lem5147369 (_67186 : real) (_67185 : real -> Prop) (h1 : term17) : term356 _67186 _67185.
Proof. exact (EQ_MP (@lem5147364 _67186 _67185) (@lem5147337 _67186 _67185 h1)). Qed.
Lemma lem5147370 (x : real) (s : real -> Prop) (h1 : term17) : term356 x s.
Proof. exact (@lem5147369 x s h1). Qed.
Lemma lem5147373 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term141 s a x) (h3 : term199 s a x) : term42 x s.
Proof. exact (@lem5147370 x s h1 (@lem5147367 s a x h2 h3)). Qed.
Lemma lem5147374 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term141 s a x) (h3 : term199 s a x) : term292 x s.
Proof. exact (fun h0 : term135 x s => @lem5147373 s a x h1 h2 h3). Qed.
Lemma lem5147376 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5147377 (x : real) (s : real -> Prop) : (term292 x s) = (term42 x s).
Proof. exact (@lem5147376 (term42 x s)). Qed.
Lemma lem5147378 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term141 s a x) (h3 : term199 s a x) : term42 x s.
Proof. exact (EQ_MP (@lem5147377 x s) (@lem5147374 s a x h1 h2 h3)). Qed.
Lemma lem5147394 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5147395 (_67182 : real) (_67183 : real) (_67184 : real) : (term357 _67183 _67182 _67184) = (term358 _67182 _67183 _67184).
Proof. exact (@lem5147394 (real_le _67182 _67184) (term288 _67183 _67184)). Qed.
Lemma lem5147401 (_67182 : real) (_67183 : real) : (term359 _67182 _67183) = (term359 _67182 _67183).
Proof. exact (eq_refl (term359 _67182 _67183)). Qed.
Lemma lem5147402 (_67182 : real) (_67183 : real) (_67184 : real) : (term287 _67183 _67182 _67184) = (term360 _67182 _67183 _67184).
Proof. exact (MK_COMB (@lem5147401 _67182 _67183) (@lem5147395 _67182 _67183 _67184)). Qed.
Lemma lem5147406 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5147407 (_67182 : real) (_67183 : real) (_67184 : real) : (term360 _67182 _67183 _67184) = (term361 _67182 _67183 _67184).
Proof. exact (@lem5147406 (real_le _67182 _67184) (term288 _67182 _67183) (term288 _67183 _67184)). Qed.
Lemma lem5147423 (_67182 : real) (_67183 : real) (_67184 : real) : (term287 _67183 _67182 _67184) = (term361 _67182 _67183 _67184).
Proof. exact (TRANS (@lem5147402 _67182 _67183 _67184) (@lem5147407 _67182 _67183 _67184)). Qed.
Lemma lem5147424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5147425 (_67182 : real) (_67183 : real) (_67184 : real) : (term362 _67183 _67182 _67184) = (term363 _67182 _67183 _67184).
Proof. exact (MK_COMB (@lem5147424) (@lem5147423 _67182 _67183 _67184)). Qed.
Lemma lem5147441 (_67182 : real) (_67183 : real) (_67184 : real) : (term361 _67182 _67183 _67184) = (term361 _67182 _67183 _67184).
Proof. exact (eq_refl (term361 _67182 _67183 _67184)). Qed.
Lemma lem5147442 (_67182 : real) (_67183 : real) (_67184 : real) : ((term287 _67183 _67182 _67184) = (term361 _67182 _67183 _67184)) = ((term361 _67182 _67183 _67184) = (term361 _67182 _67183 _67184)).
Proof. exact (MK_COMB (@lem5147425 _67182 _67183 _67184) (@lem5147441 _67182 _67183 _67184)). Qed.
Lemma lem5147444 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5147445 (x : Prop) : (x = x) = True.
Proof. exact (@lem5147444 Prop x). Qed.
Lemma lem5147446 (_67182 : real) (_67183 : real) (_67184 : real) : ((term361 _67182 _67183 _67184) = (term361 _67182 _67183 _67184)) = True.
Proof. exact (@lem5147445 (term361 _67182 _67183 _67184)). Qed.
Lemma lem5147447 (_67182 : real) (_67183 : real) (_67184 : real) : ((term287 _67183 _67182 _67184) = (term361 _67182 _67183 _67184)) = True.
Proof. exact (TRANS (@lem5147442 _67182 _67183 _67184) (@lem5147446 _67182 _67183 _67184)). Qed.
Lemma lem5147448 (_67182 : real) (_67183 : real) (_67184 : real) : True = ((term287 _67183 _67182 _67184) = (term361 _67182 _67183 _67184)).
Proof. exact (SYM (@lem5147447 _67182 _67183 _67184)). Qed.
Lemma lem5147449 (_67182 : real) (_67183 : real) (_67184 : real) : (term287 _67183 _67182 _67184) = (term361 _67182 _67183 _67184).
Proof. exact (EQ_MP (@lem5147448 _67182 _67183 _67184) (@lem0)). Qed.
Lemma lem5147450 (_67182 : real) (_67183 : real) (_67184 : real) (h1 : term37) : term361 _67182 _67183 _67184.
Proof. exact (EQ_MP (@lem5147449 _67182 _67183 _67184) (@lem5146822 _67183 _67182 _67184 h1)). Qed.
Lemma lem5147452 (b : Prop) (a : Prop) : (a \/ b) = (term293 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5147453 (_67183 : real) (_67182 : real) (_67184 : real) : (term361 _67182 _67183 _67184) = (term364 _67183 _67182 _67184).
Proof. exact (@lem5147452 (term208 _67182 _67183 _67184) (real_le _67182 _67184)). Qed.
Lemma lem5147455 (a : Prop) (b : Prop) : (term313 a b) = (term314 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5147456 (_67182 : real) (_67183 : real) (_67184 : real) : (term365 _67182 _67183 _67184) = (term366 _67182 _67183 _67184).
Proof. exact (@lem5147455 (term288 _67182 _67183) (term288 _67183 _67184)). Qed.
Lemma lem5147458 (a : Prop) : (term296 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5147459 (_67182 : real) (_67183 : real) : (term297 _67182 _67183) = (real_le _67182 _67183).
Proof. exact (@lem5147458 (real_le _67182 _67183)). Qed.
Lemma lem5147460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5147461 (_67182 : real) (_67183 : real) : (term367 _67182 _67183) = (term368 _67182 _67183).
Proof. exact (MK_COMB (@lem5147460) (@lem5147459 _67182 _67183)). Qed.
Lemma lem5147463 (a : Prop) : (term296 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5147464 (_67183 : real) (_67184 : real) : (term297 _67183 _67184) = (real_le _67183 _67184).
Proof. exact (@lem5147463 (real_le _67183 _67184)). Qed.
Lemma lem5147465 (_67182 : real) (_67183 : real) (_67184 : real) : (term366 _67182 _67183 _67184) = (term213 _67182 _67183 _67184).
Proof. exact (MK_COMB (@lem5147461 _67182 _67183) (@lem5147464 _67183 _67184)). Qed.
Lemma lem5147466 (_67182 : real) (_67183 : real) (_67184 : real) : (term365 _67182 _67183 _67184) = (term213 _67182 _67183 _67184).
Proof. exact (TRANS (@lem5147456 _67182 _67183 _67184) (@lem5147465 _67182 _67183 _67184)). Qed.
Lemma lem5147467 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5147468 (_67182 : real) (_67183 : real) (_67184 : real) : (term369 _67182 _67183 _67184) = (term370 _67182 _67183 _67184).
Proof. exact (MK_COMB (@lem5147467) (@lem5147466 _67182 _67183 _67184)). Qed.
Lemma lem5147469 (_67182 : real) (_67184 : real) : (real_le _67182 _67184) = (real_le _67182 _67184).
Proof. exact (eq_refl (real_le _67182 _67184)). Qed.
Lemma lem5147470 (_67183 : real) (_67182 : real) (_67184 : real) : (term364 _67183 _67182 _67184) = (term31 _67183 _67182 _67184).
Proof. exact (MK_COMB (@lem5147468 _67182 _67183 _67184) (@lem5147469 _67182 _67184)). Qed.
Lemma lem5147471 (_67183 : real) (_67182 : real) (_67184 : real) : (term361 _67182 _67183 _67184) = (term31 _67183 _67182 _67184).
Proof. exact (TRANS (@lem5147453 _67183 _67182 _67184) (@lem5147470 _67183 _67182 _67184)). Qed.
Lemma lem5147473 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term141 s a x) (h3 : term199 s a x) : term371 a x s.
Proof. exact (conj (@lem5147163 s a x h2) (@lem5147378 s a x h1 h2 h3)). Qed.
Lemma lem5147475 (_67183 : real) (_67182 : real) (_67184 : real) (h1 : term37) : term31 _67183 _67182 _67184.
Proof. exact (EQ_MP (@lem5147471 _67183 _67182 _67184) (@lem5147450 _67182 _67183 _67184 h1)). Qed.
Lemma lem5147476 (x : real) (a : real) (s : real -> Prop) (h1 : term37) : term372 x a s.
Proof. exact (@lem5147475 x a (sup s) h1). Qed.
Lemma lem5147479 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term141 s a x) (h4 : term199 s a x) : term42 a s.
Proof. exact (@lem5147476 x a s h2 (@lem5147473 s a x h1 h3 h4)). Qed.
Lemma lem5147480 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term141 s a x) (h4 : term199 s a x) : term292 a s.
Proof. exact (fun h0 : term135 a s => @lem5147479 s a x h1 h2 h3 h4). Qed.
Lemma lem5147482 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5147483 (a : real) (s : real -> Prop) : (term292 a s) = (term42 a s).
Proof. exact (@lem5147482 (term42 a s)). Qed.
Lemma lem5147484 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term141 s a x) (h4 : term199 s a x) : term42 a s.
Proof. exact (EQ_MP (@lem5147483 a s) (@lem5147480 s a x h1 h2 h3 h4)). Qed.
Lemma lem5147487 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5147489 (a : real) (s : real -> Prop) : (term135 a s) = (term373 a s).
Proof. exact (@lem5147487 (term42 a s)). Qed.
Lemma lem5147492 (s : real -> Prop) (a : real) (x : real) (h1 : term141 s a x) : term373 a s.
Proof. exact (EQ_MP (@lem5147489 a s) (@lem5146828 s a x h1)). Qed.
Lemma lem5147495 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term141 s a x) (h4 : term199 s a x) : False.
Proof. exact (@lem5147492 s a x h3 (@lem5147484 s a x h1 h2 h3 h4)). Qed.
Lemma lem5147496 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term141 s a x) (h4 : term199 s a x) : term326.
Proof. exact (fun h0 : ~ False => @lem5147495 s a x h1 h2 h3 h4). Qed.
Lemma lem5147498 (p : Prop) : (term291 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5147499 : term326 = False.
Proof. exact (@lem5147498 False). Qed.
Lemma lem5147500 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term141 s a x) (h4 : term199 s a x) : False.
Proof. exact (EQ_MP (@lem5147499) (@lem5147496 s a x h1 h2 h3 h4)). Qed.
Lemma lem5147501 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term199 s a x) : False.
Proof. exact (or_elim (@lem5146449 s a x h3) (fun h0 : term62 s a => @lem5147094 x s a h1 h3 h0) (fun h0 : term141 s a x => @lem5147500 s a x h1 h2 h0 h3)). Qed.
Lemma lem5147502 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term199 s a x) : (term199 s a x) = False.
Proof. exact (prop_ext (fun h4 : term199 s a x => @lem5147501 s a x h1 h2 h3) (fun h4 : False => @lem5146448 s a x h3)). Qed.
Lemma lem5147503 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term199 s a x) : False.
Proof. exact (EQ_MP (@lem5147502 s a x h1 h2 h3) (@lem5146448 s a x h3)). Qed.
Lemma lem5147504 (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term202 s a) : False.
Proof. exact (ex_elim (@lem5146287 s a h3) (fun x : real => fun h0 : term201 s a x => @lem5147503 s a x h1 h2 h0)). Qed.
Lemma lem5147505 (s : real -> Prop) (h1 : term17) (h2 : term37) (h3 : term204 s) : False.
Proof. exact (ex_elim (@lem5146286 s h3) (fun a : real => fun h0 : term203 s a => @lem5147504 s a h1 h2 h0)). Qed.
Lemma lem5147506 (h1 : term17) (h2 : term37) (h3 : term10) : False.
Proof. exact (ex_elim (@lem5146070 h3) (fun s : real -> Prop => fun h0 : term205 s => @lem5147505 s h1 h2 h0)). Qed.
Lemma lem5147507 (h1 : term37) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem5147506 h0 h1 h2). Qed.
Lemma lem5147508 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem5147509 (h1 : term37) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem5147508) (@lem5147507 h1 h2)). Qed.
Lemma lem5147510 (h1 : term10) : term20.
Proof. exact (fun h0 : term37 => @lem5147509 h0 h1). Qed.
Lemma lem5147511 : term22.
Proof. exact (fun h0 : term10 => @lem5147510 h0). Qed.
Lemma lem5147512 : term11.
Proof. exact (EQ_MP (@lem5145572) (@lem5147511)). Qed.
Lemma lem5147514 : term11.
Proof. exact (@lem5145304 (@lem5147512)). Qed.
Lemma lem5147515 (h1 : term10) : term19.
Proof. exact (@lem5147514 (@lem5145289 h1)). Qed.
Lemma lem5147516 (h1 : term10) : term15.
Proof. exact (@lem5147515 h1 (@lem1339577)). Qed.
Lemma lem5147517 (h1 : term10) : False.
Proof. exact (@lem5147516 h1 (@lem5145274)). Qed.
Lemma lem5147518 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem5147517 h1) (fun h2 : False => @lem5145289 h1)). Qed.
Lemma lem5147519 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem5147518 h1) (@lem5145289 h1)). Qed.
Lemma lem5147520 : term9.
Proof. exact (fun h0 : term10 => @lem5147519 h0). Qed.
Lemma lem5147521 : term8.
Proof. exact (EQ_MP (@lem5145288) (@lem5147520)). Qed.
