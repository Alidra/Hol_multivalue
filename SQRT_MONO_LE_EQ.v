Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_MONO_LE_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_NOT_LT_spec.
Require Import SQRT_MONO_LE_spec.
Require Import SQRT_MONO_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem1953294 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1953295 : term1 = term2.
Proof. exact (@lem1953294 term1). Qed.
Lemma lem1953296 : term2 = term1.
Proof. exact (SYM (@lem1953295)). Qed.
Lemma lem1953297 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1953300 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1953301 : term5.
Proof. exact (fun h0 : term4 => @lem1953300 h0). Qed.
Lemma lem1953302 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1953303 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1953304 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1953302 h2 (@lem1953303 h1)). Qed.
Lemma lem1953305 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1953304 h1 h0). Qed.
Lemma lem1953306 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1953307 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1953305 h1 (@lem1953306 h2)). Qed.
Lemma lem1953308 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1953307 h0 h1). Qed.
Lemma lem1953309 : term7.
Proof. exact (fun h0 : term5 => @lem1953308 h0). Qed.
Lemma lem1953312 : term5.
Proof. exact (@lem1953309 (@lem1953301)). Qed.
Lemma lem1953348 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1953349 : term8 = term9.
Proof. exact (@lem1953348 term10). Qed.
Lemma lem1953358 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1953359 : term12 = term13.
Proof. exact (MK_COMB (@lem1953358) (@lem1953349)). Qed.
Lemma lem1953362 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1953363 : term15 = term16.
Proof. exact (MK_COMB (@lem1953362) (@lem1953359)). Qed.
Lemma lem1953366 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1953373 : term4 = term18.
Proof. exact (MK_COMB (@lem1953366) (@lem1953363)). Qed.
Lemma lem1953380 (y : real) (x : real) : ((term19 x y) = (real_le y x)) = ((term19 x y) = (real_le y x)).
Proof. exact (eq_refl ((term19 x y) = (real_le y x))). Qed.
Lemma lem1953381 (x : real) : (term20 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1953380 y x)). Qed.
Lemma lem1953382 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1953383 (x : real) : (term21 x) = (term21 x).
Proof. exact (MK_COMB (@lem1953382) (@lem1953381 x)). Qed.
Lemma lem1953384 : term22 = term22.
Proof. exact (fun_ext (fun x : real => @lem1953383 x)). Qed.
Lemma lem1953385 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1953386 : term10 = term10.
Proof. exact (MK_COMB (@lem1953385) (@lem1953384)). Qed.
Lemma lem1953387 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1953388 : term9 = term9.
Proof. exact (MK_COMB (@lem1953387) (@lem1953386)). Qed.
Lemma lem1953393 (x : real) (y : real) : (term23 x y) = (term23 x y).
Proof. exact (eq_refl (term23 x y)). Qed.
Lemma lem1953394 (x : real) : (term24 x) = (term24 x).
Proof. exact (fun_ext (fun y : real => @lem1953393 x y)). Qed.
Lemma lem1953395 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1953396 (x : real) : (term25 x) = (term25 x).
Proof. exact (MK_COMB (@lem1953395) (@lem1953394 x)). Qed.
Lemma lem1953397 : term26 = term26.
Proof. exact (fun_ext (fun x : real => @lem1953396 x)). Qed.
Lemma lem1953398 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1953399 : term27 = term27.
Proof. exact (MK_COMB (@lem1953398) (@lem1953397)). Qed.
Lemma lem1953400 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1953401 : term11 = term11.
Proof. exact (MK_COMB (@lem1953400) (@lem1953399)). Qed.
Lemma lem1953402 : term13 = term13.
Proof. exact (MK_COMB (@lem1953401) (@lem1953388)). Qed.
Lemma lem1953407 (x : real) (y : real) : (term28 x y) = (term28 x y).
Proof. exact (eq_refl (term28 x y)). Qed.
Lemma lem1953408 (x : real) : (term29 x) = (term29 x).
Proof. exact (fun_ext (fun y : real => @lem1953407 x y)). Qed.
Lemma lem1953409 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1953410 (x : real) : (term30 x) = (term30 x).
Proof. exact (MK_COMB (@lem1953409) (@lem1953408 x)). Qed.
Lemma lem1953411 : term31 = term31.
Proof. exact (fun_ext (fun x : real => @lem1953410 x)). Qed.
Lemma lem1953412 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1953413 : term32 = term32.
Proof. exact (MK_COMB (@lem1953412) (@lem1953411)). Qed.
Lemma lem1953414 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1953415 : term14 = term14.
Proof. exact (MK_COMB (@lem1953414) (@lem1953413)). Qed.
Lemma lem1953416 : term16 = term16.
Proof. exact (MK_COMB (@lem1953415) (@lem1953402)). Qed.
Lemma lem1953421 (x : real) (y : real) : ((term33 x y) = (real_le x y)) = ((term33 x y) = (real_le x y)).
Proof. exact (eq_refl ((term33 x y) = (real_le x y))). Qed.
Lemma lem1953422 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem1953421 x y)). Qed.
Lemma lem1953423 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1953424 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem1953423) (@lem1953422 x)). Qed.
Lemma lem1953425 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1953424 x)). Qed.
Lemma lem1953426 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1953427 : term1 = term1.
Proof. exact (MK_COMB (@lem1953426) (@lem1953425)). Qed.
Lemma lem1953428 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1953429 : term3 = term3.
Proof. exact (MK_COMB (@lem1953428) (@lem1953427)). Qed.
Lemma lem1953430 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1953431 : term17 = term17.
Proof. exact (MK_COMB (@lem1953430) (@lem1953429)). Qed.
Lemma lem1953432 : term18 = term18.
Proof. exact (MK_COMB (@lem1953431) (@lem1953416)). Qed.
Lemma lem1953493 : term4 = term18.
Proof. exact (TRANS (@lem1953373) (@lem1953432)). Qed.
Lemma lem1953494 : term18 = term4.
Proof. exact (SYM (@lem1953493)). Qed.
Lemma lem1953495 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1953496 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem1953497 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem1953498 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1953513 (x : real) (y : real) : (term37 x y) = (term38 x y).
Proof. exact (@lem17646 (term33 x y) (real_le x y)). Qed.
Lemma lem1953514 (P : real -> Prop) : (term39 P) = (term40 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1953515 (x : real) : (term41 x) = (term42 x).
Proof. exact (@lem1953514 (term34 x)). Qed.
Lemma lem1953516 (x : real) (y : real) : (term43 x y) = ((term33 x y) = (real_le x y)).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem1953517 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1953518 (x : real) (y : real) : (term44 x y) = (term37 x y).
Proof. exact (MK_COMB (@lem1953517) (@lem1953516 x y)). Qed.
Lemma lem1953519 (x : real) (y : real) : (term44 x y) = (term38 x y).
Proof. exact (TRANS (@lem1953518 x y) (@lem1953513 x y)). Qed.
Lemma lem1953520 (x : real) : (term45 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem1953519 x y)). Qed.
Lemma lem1953521 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1953522 (x : real) : (term42 x) = (term47 x).
Proof. exact (MK_COMB (@lem1953521) (@lem1953520 x)). Qed.
Lemma lem1953523 (x : real) : (term41 x) = (term47 x).
Proof. exact (TRANS (@lem1953515 x) (@lem1953522 x)). Qed.
Lemma lem1953524 (P : real -> Prop) : (term39 P) = (term40 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1953525 : term3 = term48.
Proof. exact (@lem1953524 term36). Qed.
Lemma lem1953526 (x : real) : (term49 x) = (term35 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1953527 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1953528 (x : real) : (term50 x) = (term41 x).
Proof. exact (MK_COMB (@lem1953527) (@lem1953526 x)). Qed.
Lemma lem1953529 (x : real) : (term50 x) = (term47 x).
Proof. exact (TRANS (@lem1953528 x) (@lem1953523 x)). Qed.
Lemma lem1953530 : term51 = term52.
Proof. exact (fun_ext (fun x : real => @lem1953529 x)). Qed.
Lemma lem1953531 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1953532 : term48 = term53.
Proof. exact (MK_COMB (@lem1953531) (@lem1953530)). Qed.
Lemma lem1953533 : term3 = term53.
Proof. exact (TRANS (@lem1953525) (@lem1953532)). Qed.
Lemma lem1953539 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1953540 (P : real -> Prop) (Q : real -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem1953539 real P Q). Qed.
Lemma lem1953541 (x : real) : (term58 x) = (term59 x).
Proof. exact (@lem1953540 (term60 x) (term61 x)). Qed.
Lemma lem1953542 (x : real) (y : real) : (term62 x y) = (term63 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1953543 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1953544 (x : real) (y : real) : (term64 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1953543) (@lem1953542 x y)). Qed.
Lemma lem1953545 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (eq_refl (term66 x y)). Qed.
Lemma lem1953546 (x : real) (y : real) : (term68 x y) = (term38 x y).
Proof. exact (MK_COMB (@lem1953544 x y) (@lem1953545 x y)). Qed.
Lemma lem1953547 (x : real) : (term69 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem1953546 x y)). Qed.
Lemma lem1953548 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1953549 (x : real) : (term58 x) = (term47 x).
Proof. exact (MK_COMB (@lem1953548) (@lem1953547 x)). Qed.
Lemma lem1953550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1953551 (x : real) : (term70 x) = (term71 x).
Proof. exact (MK_COMB (@lem1953550) (@lem1953549 x)). Qed.
Lemma lem1953552 (x : real) (y : real) : (term62 x y) = (term63 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1953553 (x : real) : (term72 x) = (term60 x).
Proof. exact (fun_ext (fun y : real => @lem1953552 x y)). Qed.
Lemma lem1953554 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1953555 (x : real) : (term73 x) = (term74 x).
Proof. exact (MK_COMB (@lem1953554) (@lem1953553 x)). Qed.
Lemma lem1953556 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1953557 (x : real) : (term75 x) = (term76 x).
Proof. exact (MK_COMB (@lem1953556) (@lem1953555 x)). Qed.
Lemma lem1953558 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (eq_refl (term66 x y)). Qed.
Lemma lem1953559 (x : real) : (term77 x) = (term61 x).
Proof. exact (fun_ext (fun y : real => @lem1953558 x y)). Qed.
Lemma lem1953560 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1953561 (x : real) : (term78 x) = (term79 x).
Proof. exact (MK_COMB (@lem1953560) (@lem1953559 x)). Qed.
Lemma lem1953562 (x : real) : (term59 x) = (term80 x).
Proof. exact (MK_COMB (@lem1953557 x) (@lem1953561 x)). Qed.
Lemma lem1953563 (x : real) : ((term58 x) = (term59 x)) = ((term47 x) = (term80 x)).
Proof. exact (MK_COMB (@lem1953551 x) (@lem1953562 x)). Qed.
Lemma lem1953564 (x : real) : (term47 x) = (term80 x).
Proof. exact (EQ_MP (@lem1953563 x) (@lem1953541 x)). Qed.
Lemma lem1953661 : term52 = term81.
Proof. exact (fun_ext (fun x : real => @lem1953564 x)). Qed.
Lemma lem1953662 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1953663 : term53 = term82.
Proof. exact (MK_COMB (@lem1953662) (@lem1953661)). Qed.
Lemma lem1953665 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1953666 (P : real -> Prop) (Q : real -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem1953665 real P Q). Qed.
Lemma lem1953667 : term83 = term84.
Proof. exact (@lem1953666 term85 term86). Qed.
Lemma lem1953668 (x : real) : (term87 x) = (term74 x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem1953669 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1953670 (x : real) : (term88 x) = (term76 x).
Proof. exact (MK_COMB (@lem1953669) (@lem1953668 x)). Qed.
Lemma lem1953671 (x : real) : (term89 x) = (term79 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1953672 (x : real) : (term90 x) = (term80 x).
Proof. exact (MK_COMB (@lem1953670 x) (@lem1953671 x)). Qed.
Lemma lem1953673 : term91 = term81.
Proof. exact (fun_ext (fun x : real => @lem1953672 x)). Qed.
Lemma lem1953674 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1953675 : term83 = term82.
Proof. exact (MK_COMB (@lem1953674) (@lem1953673)). Qed.
Lemma lem1953676 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1953677 : term92 = term93.
Proof. exact (MK_COMB (@lem1953676) (@lem1953675)). Qed.
Lemma lem1953678 (x : real) : (term87 x) = (term74 x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem1953679 : term94 = term85.
Proof. exact (fun_ext (fun x : real => @lem1953678 x)). Qed.
Lemma lem1953680 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1953681 : term95 = term96.
Proof. exact (MK_COMB (@lem1953680) (@lem1953679)). Qed.
Lemma lem1953682 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1953683 : term97 = term98.
Proof. exact (MK_COMB (@lem1953682) (@lem1953681)). Qed.
Lemma lem1953684 (x : real) : (term89 x) = (term79 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1953685 : term99 = term86.
Proof. exact (fun_ext (fun x : real => @lem1953684 x)). Qed.
Lemma lem1953686 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1953687 : term100 = term101.
Proof. exact (MK_COMB (@lem1953686) (@lem1953685)). Qed.
Lemma lem1953688 : term84 = term102.
Proof. exact (MK_COMB (@lem1953683) (@lem1953687)). Qed.
Lemma lem1953689 : (term83 = term84) = (term82 = term102).
Proof. exact (MK_COMB (@lem1953677) (@lem1953688)). Qed.
Lemma lem1953690 : term82 = term102.
Proof. exact (EQ_MP (@lem1953689) (@lem1953667)). Qed.
Lemma lem1953795 : term53 = term102.
Proof. exact (TRANS (@lem1953663) (@lem1953690)). Qed.
Lemma lem1953797 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term54 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1953798 (P : real -> Prop) (Q : real -> Prop) : (term57 P Q) = (term56 P Q).
Proof. exact (@lem1953797 real P Q). Qed.
Lemma lem1953799 : term84 = term83.
Proof. exact (@lem1953798 term85 term86). Qed.
Lemma lem1953800 (x : real) : (term87 x) = (term74 x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem1953801 : term94 = term85.
Proof. exact (fun_ext (fun x : real => @lem1953800 x)). Qed.
Lemma lem1953802 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1953803 : term95 = term96.
Proof. exact (MK_COMB (@lem1953802) (@lem1953801)). Qed.
Lemma lem1953804 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1953805 : term97 = term98.
Proof. exact (MK_COMB (@lem1953804) (@lem1953803)). Qed.
Lemma lem1953806 (x : real) : (term89 x) = (term79 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1953807 : term99 = term86.
Proof. exact (fun_ext (fun x : real => @lem1953806 x)). Qed.
Lemma lem1953808 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1953809 : term100 = term101.
Proof. exact (MK_COMB (@lem1953808) (@lem1953807)). Qed.
Lemma lem1953810 : term84 = term102.
Proof. exact (MK_COMB (@lem1953805) (@lem1953809)). Qed.
Lemma lem1953811 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1953812 : term103 = term104.
Proof. exact (MK_COMB (@lem1953811) (@lem1953810)). Qed.
Lemma lem1953813 (x : real) : (term87 x) = (term74 x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem1953814 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1953815 (x : real) : (term88 x) = (term76 x).
Proof. exact (MK_COMB (@lem1953814) (@lem1953813 x)). Qed.
Lemma lem1953816 (x : real) : (term89 x) = (term79 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1953817 (x : real) : (term90 x) = (term80 x).
Proof. exact (MK_COMB (@lem1953815 x) (@lem1953816 x)). Qed.
Lemma lem1953818 : term91 = term81.
Proof. exact (fun_ext (fun x : real => @lem1953817 x)). Qed.
Lemma lem1953819 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1953820 : term83 = term82.
Proof. exact (MK_COMB (@lem1953819) (@lem1953818)). Qed.
Lemma lem1953821 : (term84 = term83) = (term102 = term82).
Proof. exact (MK_COMB (@lem1953812) (@lem1953820)). Qed.
Lemma lem1953822 : term102 = term82.
Proof. exact (EQ_MP (@lem1953821) (@lem1953799)). Qed.
Lemma lem1953824 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term54 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1953825 (P : real -> Prop) (Q : real -> Prop) : (term57 P Q) = (term56 P Q).
Proof. exact (@lem1953824 real P Q). Qed.
Lemma lem1953826 (x : real) : (term59 x) = (term58 x).
Proof. exact (@lem1953825 (term60 x) (term61 x)). Qed.
Lemma lem1953827 (x : real) (y : real) : (term62 x y) = (term63 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1953828 (x : real) : (term72 x) = (term60 x).
Proof. exact (fun_ext (fun y : real => @lem1953827 x y)). Qed.
Lemma lem1953829 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1953830 (x : real) : (term73 x) = (term74 x).
Proof. exact (MK_COMB (@lem1953829) (@lem1953828 x)). Qed.
Lemma lem1953831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1953832 (x : real) : (term75 x) = (term76 x).
Proof. exact (MK_COMB (@lem1953831) (@lem1953830 x)). Qed.
Lemma lem1953833 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (eq_refl (term66 x y)). Qed.
Lemma lem1953834 (x : real) : (term77 x) = (term61 x).
Proof. exact (fun_ext (fun y : real => @lem1953833 x y)). Qed.
Lemma lem1953835 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1953836 (x : real) : (term78 x) = (term79 x).
Proof. exact (MK_COMB (@lem1953835) (@lem1953834 x)). Qed.
Lemma lem1953837 (x : real) : (term59 x) = (term80 x).
Proof. exact (MK_COMB (@lem1953832 x) (@lem1953836 x)). Qed.
Lemma lem1953838 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1953839 (x : real) : (term105 x) = (term106 x).
Proof. exact (MK_COMB (@lem1953838) (@lem1953837 x)). Qed.
Lemma lem1953840 (x : real) (y : real) : (term62 x y) = (term63 x y).
Proof. exact (eq_refl (term62 x y)). Qed.
Lemma lem1953841 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1953842 (x : real) (y : real) : (term64 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1953841) (@lem1953840 x y)). Qed.
Lemma lem1953843 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (eq_refl (term66 x y)). Qed.
Lemma lem1953844 (x : real) (y : real) : (term68 x y) = (term38 x y).
Proof. exact (MK_COMB (@lem1953842 x y) (@lem1953843 x y)). Qed.
Lemma lem1953845 (x : real) : (term69 x) = (term46 x).
Proof. exact (fun_ext (fun y : real => @lem1953844 x y)). Qed.
Lemma lem1953846 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1953847 (x : real) : (term58 x) = (term47 x).
Proof. exact (MK_COMB (@lem1953846) (@lem1953845 x)). Qed.
Lemma lem1953848 (x : real) : ((term59 x) = (term58 x)) = ((term80 x) = (term47 x)).
Proof. exact (MK_COMB (@lem1953839 x) (@lem1953847 x)). Qed.
Lemma lem1953849 (x : real) : (term80 x) = (term47 x).
Proof. exact (EQ_MP (@lem1953848 x) (@lem1953826 x)). Qed.
Lemma lem1953850 : term81 = term52.
Proof. exact (fun_ext (fun x : real => @lem1953849 x)). Qed.
Lemma lem1953851 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1953852 : term82 = term53.
Proof. exact (MK_COMB (@lem1953851) (@lem1953850)). Qed.
Lemma lem1953853 : term102 = term53.
Proof. exact (TRANS (@lem1953822) (@lem1953852)). Qed.
Lemma lem1953854 : term53 = term53.
Proof. exact (TRANS (@lem1953795) (@lem1953853)). Qed.
Lemma lem1953855 : term3 = term53.
Proof. exact (TRANS (@lem1953533) (@lem1953854)). Qed.
Lemma lem1953856 (h1 : term3) : term53.
Proof. exact (EQ_MP (@lem1953855) (@lem1953495 h1)). Qed.
Lemma lem1953863 (x : real) (y : real) : (term28 x y) = (term107 x y).
Proof. exact (@lem17265 (real_le x y) (term33 x y)). Qed.
Lemma lem1953864 (x : real) : (term29 x) = (term108 x).
Proof. exact (fun_ext (fun y : real => @lem1953863 x y)). Qed.
Lemma lem1953865 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1953866 (x : real) : (term30 x) = (term109 x).
Proof. exact (MK_COMB (@lem1953865) (@lem1953864 x)). Qed.
Lemma lem1953867 : term31 = term110.
Proof. exact (fun_ext (fun x : real => @lem1953866 x)). Qed.
Lemma lem1953868 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1953925 : term32 = term111.
Proof. exact (MK_COMB (@lem1953868) (@lem1953867)). Qed.
Lemma lem1953926 (h1 : term32) : term111.
Proof. exact (EQ_MP (@lem1953925) (@lem1953496 h1)). Qed.
Lemma lem1953933 (x : real) (y : real) : (term23 x y) = (term112 x y).
Proof. exact (@lem17265 (real_lt x y) (term113 x y)). Qed.
Lemma lem1953934 (x : real) : (term24 x) = (term114 x).
Proof. exact (fun_ext (fun y : real => @lem1953933 x y)). Qed.
Lemma lem1953935 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1953936 (x : real) : (term25 x) = (term115 x).
Proof. exact (MK_COMB (@lem1953935) (@lem1953934 x)). Qed.
Lemma lem1953937 : term26 = term116.
Proof. exact (fun_ext (fun x : real => @lem1953936 x)). Qed.
Lemma lem1953938 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1953995 : term27 = term117.
Proof. exact (MK_COMB (@lem1953938) (@lem1953937)). Qed.
Lemma lem1953996 (h1 : term27) : term117.
Proof. exact (EQ_MP (@lem1953995) (@lem1953497 h1)). Qed.
Lemma lem1954000 (x : real) (y : real) : (term118 x y) = (real_lt x y).
Proof. exact (@lem16933 (real_lt x y)). Qed.
Lemma lem1954002 (y : real) (x : real) : (real_le y x) = (real_le y x).
Proof. exact (eq_refl (real_le y x)). Qed.
Lemma lem1954003 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1954004 (x : real) (y : real) : (term119 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem1954003) (@lem1954000 x y)). Qed.
Lemma lem1954005 (y : real) (x : real) : (term121 y x) = (term122 y x).
Proof. exact (MK_COMB (@lem1954004 x y) (@lem1954002 y x)). Qed.
Lemma lem1954010 (y : real) (x : real) : (term123 y x) = (term123 y x).
Proof. exact (eq_refl (term123 y x)). Qed.
Lemma lem1954011 (y : real) (x : real) : (term124 y x) = (term125 y x).
Proof. exact (MK_COMB (@lem1954010 y x) (@lem1954005 y x)). Qed.
Lemma lem1954012 (y : real) (x : real) : ((term19 x y) = (real_le y x)) = (term124 y x).
Proof. exact (@lem17784 (term19 x y) (real_le y x)). Qed.
Lemma lem1954013 (y : real) (x : real) : ((term19 x y) = (real_le y x)) = (term125 y x).
Proof. exact (TRANS (@lem1954012 y x) (@lem1954011 y x)). Qed.
Lemma lem1954014 (x : real) : (term20 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1954013 y x)). Qed.
Lemma lem1954015 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954016 (x : real) : (term21 x) = (term127 x).
Proof. exact (MK_COMB (@lem1954015) (@lem1954014 x)). Qed.
Lemma lem1954017 : term22 = term128.
Proof. exact (fun_ext (fun x : real => @lem1954016 x)). Qed.
Lemma lem1954018 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954019 : term10 = term129.
Proof. exact (MK_COMB (@lem1954018) (@lem1954017)). Qed.
Lemma lem1954025 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1954026 (P : real -> Prop) (Q : real -> Prop) : (term132 P Q) = (term133 P Q).
Proof. exact (@lem1954025 real P Q). Qed.
Lemma lem1954027 (x : real) : (term134 x) = (term135 x).
Proof. exact (@lem1954026 (term136 x) (term137 x)). Qed.
Lemma lem1954028 (y : real) (x : real) : (term138 x y) = (term139 y x).
Proof. exact (eq_refl (term138 x y)). Qed.
Lemma lem1954029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1954030 (y : real) (x : real) : (term140 x y) = (term123 y x).
Proof. exact (MK_COMB (@lem1954029) (@lem1954028 y x)). Qed.
Lemma lem1954031 (y : real) (x : real) : (term141 x y) = (term122 y x).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem1954032 (y : real) (x : real) : (term142 x y) = (term125 y x).
Proof. exact (MK_COMB (@lem1954030 y x) (@lem1954031 y x)). Qed.
Lemma lem1954033 (x : real) : (term143 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1954032 y x)). Qed.
Lemma lem1954034 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954035 (x : real) : (term134 x) = (term127 x).
Proof. exact (MK_COMB (@lem1954034) (@lem1954033 x)). Qed.
Lemma lem1954036 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1954037 (x : real) : (term144 x) = (term145 x).
Proof. exact (MK_COMB (@lem1954036) (@lem1954035 x)). Qed.
Lemma lem1954038 (y : real) (x : real) : (term138 x y) = (term139 y x).
Proof. exact (eq_refl (term138 x y)). Qed.
Lemma lem1954039 (x : real) : (term146 x) = (term136 x).
Proof. exact (fun_ext (fun y : real => @lem1954038 y x)). Qed.
Lemma lem1954040 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954041 (x : real) : (term147 x) = (term148 x).
Proof. exact (MK_COMB (@lem1954040) (@lem1954039 x)). Qed.
Lemma lem1954042 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1954043 (x : real) : (term149 x) = (term150 x).
Proof. exact (MK_COMB (@lem1954042) (@lem1954041 x)). Qed.
Lemma lem1954044 (y : real) (x : real) : (term141 x y) = (term122 y x).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem1954045 (x : real) : (term151 x) = (term137 x).
Proof. exact (fun_ext (fun y : real => @lem1954044 y x)). Qed.
Lemma lem1954046 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954047 (x : real) : (term152 x) = (term153 x).
Proof. exact (MK_COMB (@lem1954046) (@lem1954045 x)). Qed.
Lemma lem1954048 (x : real) : (term135 x) = (term154 x).
Proof. exact (MK_COMB (@lem1954043 x) (@lem1954047 x)). Qed.
Lemma lem1954049 (x : real) : ((term134 x) = (term135 x)) = ((term127 x) = (term154 x)).
Proof. exact (MK_COMB (@lem1954037 x) (@lem1954048 x)). Qed.
Lemma lem1954050 (x : real) : (term127 x) = (term154 x).
Proof. exact (EQ_MP (@lem1954049 x) (@lem1954027 x)). Qed.
Lemma lem1954147 : term128 = term155.
Proof. exact (fun_ext (fun x : real => @lem1954050 x)). Qed.
Lemma lem1954148 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954149 : term129 = term156.
Proof. exact (MK_COMB (@lem1954148) (@lem1954147)). Qed.
Lemma lem1954151 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1954152 (P : real -> Prop) (Q : real -> Prop) : (term132 P Q) = (term133 P Q).
Proof. exact (@lem1954151 real P Q). Qed.
Lemma lem1954153 : term157 = term158.
Proof. exact (@lem1954152 term159 term160). Qed.
Lemma lem1954154 (x : real) : (term161 x) = (term148 x).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem1954155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1954156 (x : real) : (term162 x) = (term150 x).
Proof. exact (MK_COMB (@lem1954155) (@lem1954154 x)). Qed.
Lemma lem1954157 (x : real) : (term163 x) = (term153 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem1954158 (x : real) : (term164 x) = (term154 x).
Proof. exact (MK_COMB (@lem1954156 x) (@lem1954157 x)). Qed.
Lemma lem1954159 : term165 = term155.
Proof. exact (fun_ext (fun x : real => @lem1954158 x)). Qed.
Lemma lem1954160 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954161 : term157 = term156.
Proof. exact (MK_COMB (@lem1954160) (@lem1954159)). Qed.
Lemma lem1954162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1954163 : term166 = term167.
Proof. exact (MK_COMB (@lem1954162) (@lem1954161)). Qed.
Lemma lem1954164 (x : real) : (term161 x) = (term148 x).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem1954165 : term168 = term159.
Proof. exact (fun_ext (fun x : real => @lem1954164 x)). Qed.
Lemma lem1954166 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954167 : term169 = term170.
Proof. exact (MK_COMB (@lem1954166) (@lem1954165)). Qed.
Lemma lem1954168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1954169 : term171 = term172.
Proof. exact (MK_COMB (@lem1954168) (@lem1954167)). Qed.
Lemma lem1954170 (x : real) : (term163 x) = (term153 x).
Proof. exact (eq_refl (term163 x)). Qed.
Lemma lem1954171 : term173 = term160.
Proof. exact (fun_ext (fun x : real => @lem1954170 x)). Qed.
Lemma lem1954172 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954173 : term174 = term175.
Proof. exact (MK_COMB (@lem1954172) (@lem1954171)). Qed.
Lemma lem1954174 : term158 = term176.
Proof. exact (MK_COMB (@lem1954169) (@lem1954173)). Qed.
Lemma lem1954175 : (term157 = term158) = (term156 = term176).
Proof. exact (MK_COMB (@lem1954163) (@lem1954174)). Qed.
Lemma lem1954176 : term156 = term176.
Proof. exact (EQ_MP (@lem1954175) (@lem1954153)). Qed.
Lemma lem1954283 : term129 = term176.
Proof. exact (TRANS (@lem1954149) (@lem1954176)). Qed.
Lemma lem1954284 : term10 = term176.
Proof. exact (TRANS (@lem1954019) (@lem1954283)). Qed.
Lemma lem1954285 (h1 : term10) : term176.
Proof. exact (EQ_MP (@lem1954284) (@lem1953498 h1)). Qed.
Lemma lem1954286 (x : real) (h1 : term47 x) : term47 x.
Proof. exact (h1). Qed.
Lemma lem1954306 (x : real) (y : real) : (term107 x y) = (term107 x y).
Proof. exact (eq_refl (term107 x y)). Qed.
Lemma lem1954307 (x : real) : (term108 x) = (term108 x).
Proof. exact (fun_ext (fun y : real => @lem1954306 x y)). Qed.
Lemma lem1954308 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954309 (x : real) : (term109 x) = (term109 x).
Proof. exact (MK_COMB (@lem1954308) (@lem1954307 x)). Qed.
Lemma lem1954310 : term110 = term110.
Proof. exact (fun_ext (fun x : real => @lem1954309 x)). Qed.
Lemma lem1954311 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954312 : term111 = term111.
Proof. exact (MK_COMB (@lem1954311) (@lem1954310)). Qed.
Lemma lem1954313 (h1 : term32) : term111.
Proof. exact (EQ_MP (@lem1954312) (@lem1953926 h1)). Qed.
Lemma lem1954332 (x : real) (y : real) : (term112 x y) = (term112 x y).
Proof. exact (eq_refl (term112 x y)). Qed.
Lemma lem1954333 (x : real) : (term114 x) = (term114 x).
Proof. exact (fun_ext (fun y : real => @lem1954332 x y)). Qed.
Lemma lem1954334 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954335 (x : real) : (term115 x) = (term115 x).
Proof. exact (MK_COMB (@lem1954334) (@lem1954333 x)). Qed.
Lemma lem1954336 : term116 = term116.
Proof. exact (fun_ext (fun x : real => @lem1954335 x)). Qed.
Lemma lem1954337 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954338 : term117 = term117.
Proof. exact (MK_COMB (@lem1954337) (@lem1954336)). Qed.
Lemma lem1954339 (h1 : term27) : term117.
Proof. exact (EQ_MP (@lem1954338) (@lem1953996 h1)). Qed.
Lemma lem1954352 (y : real) (x : real) : (term122 y x) = (term122 y x).
Proof. exact (eq_refl (term122 y x)). Qed.
Lemma lem1954353 (x : real) : (term137 x) = (term137 x).
Proof. exact (fun_ext (fun y : real => @lem1954352 y x)). Qed.
Lemma lem1954354 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954355 (x : real) : (term153 x) = (term153 x).
Proof. exact (MK_COMB (@lem1954354) (@lem1954353 x)). Qed.
Lemma lem1954356 : term160 = term160.
Proof. exact (fun_ext (fun x : real => @lem1954355 x)). Qed.
Lemma lem1954357 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954358 : term175 = term175.
Proof. exact (MK_COMB (@lem1954357) (@lem1954356)). Qed.
Lemma lem1954375 (y : real) (x : real) : (term139 y x) = (term139 y x).
Proof. exact (eq_refl (term139 y x)). Qed.
Lemma lem1954376 (x : real) : (term136 x) = (term136 x).
Proof. exact (fun_ext (fun y : real => @lem1954375 y x)). Qed.
Lemma lem1954377 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954378 (x : real) : (term148 x) = (term148 x).
Proof. exact (MK_COMB (@lem1954377) (@lem1954376 x)). Qed.
Lemma lem1954379 : term159 = term159.
Proof. exact (fun_ext (fun x : real => @lem1954378 x)). Qed.
Lemma lem1954380 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954381 : term170 = term170.
Proof. exact (MK_COMB (@lem1954380) (@lem1954379)). Qed.
Lemma lem1954382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1954383 : term172 = term172.
Proof. exact (MK_COMB (@lem1954382) (@lem1954381)). Qed.
Lemma lem1954384 : term176 = term176.
Proof. exact (MK_COMB (@lem1954383) (@lem1954358)). Qed.
Lemma lem1954385 (h1 : term10) : term176.
Proof. exact (EQ_MP (@lem1954384) (@lem1954285 h1)). Qed.
Lemma lem1954427 (x : real) (y : real) (h1 : term38 x y) : term38 x y.
Proof. exact (h1). Qed.
Lemma lem1954428 (h1 : term10) : term175.
Proof. exact (proj2 (@lem1954385 h1)). Qed.
Lemma lem1954429 (h1 : term10) : term170.
Proof. exact (proj1 (@lem1954385 h1)). Qed.
Lemma lem1954430 (x : real) (y : real) (h1 : term63 x y) : term63 x y.
Proof. exact (h1). Qed.
Lemma lem1954431 (x : real) (y : real) (h1 : term67 x y) : term67 x y.
Proof. exact (h1). Qed.
Lemma lem1954459 (x : real) (y : real) : (term112 x y) = (term112 x y).
Proof. exact (eq_refl (term112 x y)). Qed.
Lemma lem1954460 (x : real) : (term114 x) = (term114 x).
Proof. exact (fun_ext (fun y : real => @lem1954459 x y)). Qed.
Lemma lem1954461 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954462 (x : real) : (term115 x) = (term115 x).
Proof. exact (MK_COMB (@lem1954461) (@lem1954460 x)). Qed.
Lemma lem1954463 : term116 = term116.
Proof. exact (fun_ext (fun x : real => @lem1954462 x)). Qed.
Lemma lem1954464 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954466 : term117 = term117.
Proof. exact (MK_COMB (@lem1954464) (@lem1954463)). Qed.
Lemma lem1954467 (h1 : term27) : term117.
Proof. exact (EQ_MP (@lem1954466) (@lem1954339 h1)). Qed.
Lemma lem1954475 (y : real) (x : real) : (term139 y x) = (term139 y x).
Proof. exact (eq_refl (term139 y x)). Qed.
Lemma lem1954476 (x : real) : (term136 x) = (term136 x).
Proof. exact (fun_ext (fun y : real => @lem1954475 y x)). Qed.
Lemma lem1954477 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954478 (x : real) : (term148 x) = (term148 x).
Proof. exact (MK_COMB (@lem1954477) (@lem1954476 x)). Qed.
Lemma lem1954479 : term159 = term159.
Proof. exact (fun_ext (fun x : real => @lem1954478 x)). Qed.
Lemma lem1954480 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954482 : term170 = term170.
Proof. exact (MK_COMB (@lem1954480) (@lem1954479)). Qed.
Lemma lem1954483 (h1 : term10) : term170.
Proof. exact (EQ_MP (@lem1954482) (@lem1954429 h1)). Qed.
Lemma lem1954491 (y : real) (x : real) : (term122 y x) = (term122 y x).
Proof. exact (eq_refl (term122 y x)). Qed.
Lemma lem1954492 (x : real) : (term137 x) = (term137 x).
Proof. exact (fun_ext (fun y : real => @lem1954491 y x)). Qed.
Lemma lem1954493 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954494 (x : real) : (term153 x) = (term153 x).
Proof. exact (MK_COMB (@lem1954493) (@lem1954492 x)). Qed.
Lemma lem1954495 : term160 = term160.
Proof. exact (fun_ext (fun x : real => @lem1954494 x)). Qed.
Lemma lem1954496 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954498 : term175 = term175.
Proof. exact (MK_COMB (@lem1954496) (@lem1954495)). Qed.
Lemma lem1954499 (h1 : term10) : term175.
Proof. exact (EQ_MP (@lem1954498) (@lem1954428 h1)). Qed.
Lemma lem1954515 (x : real) (y : real) : (term107 x y) = (term107 x y).
Proof. exact (eq_refl (term107 x y)). Qed.
Lemma lem1954516 (x : real) : (term108 x) = (term108 x).
Proof. exact (fun_ext (fun y : real => @lem1954515 x y)). Qed.
Lemma lem1954517 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954518 (x : real) : (term109 x) = (term109 x).
Proof. exact (MK_COMB (@lem1954517) (@lem1954516 x)). Qed.
Lemma lem1954519 : term110 = term110.
Proof. exact (fun_ext (fun x : real => @lem1954518 x)). Qed.
Lemma lem1954520 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954522 : term111 = term111.
Proof. exact (MK_COMB (@lem1954520) (@lem1954519)). Qed.
Lemma lem1954523 (h1 : term32) : term111.
Proof. exact (EQ_MP (@lem1954522) (@lem1954313 h1)). Qed.
Lemma lem1954586 (_27412 : real) (h1 : term27) : term177 _27412.
Proof. exact (@lem1954467 h1 _27412). Qed.
Lemma lem1954587 (_27412 : real) : (term177 _27412) = (term115 _27412).
Proof. exact (eq_refl (term177 _27412)). Qed.
Lemma lem1954588 (_27412 : real) (h1 : term27) : term115 _27412.
Proof. exact (EQ_MP (@lem1954587 _27412) (@lem1954586 _27412 h1)). Qed.
Lemma lem1954589 (_27412 : real) (_27413 : real) (h1 : term27) : term178 _27412 _27413.
Proof. exact (@lem1954588 _27412 h1 _27413). Qed.
Lemma lem1954590 (_27412 : real) (_27413 : real) : (term178 _27412 _27413) = (term112 _27412 _27413).
Proof. exact (eq_refl (term178 _27412 _27413)). Qed.
Lemma lem1954592 (_27414 : real) (h1 : term10) : term161 _27414.
Proof. exact (@lem1954483 h1 _27414). Qed.
Lemma lem1954593 (_27414 : real) : (term161 _27414) = (term148 _27414).
Proof. exact (eq_refl (term161 _27414)). Qed.
Lemma lem1954594 (_27414 : real) (h1 : term10) : term148 _27414.
Proof. exact (EQ_MP (@lem1954593 _27414) (@lem1954592 _27414 h1)). Qed.
Lemma lem1954595 (_27414 : real) (_27415 : real) (h1 : term10) : term138 _27414 _27415.
Proof. exact (@lem1954594 _27414 h1 _27415). Qed.
Lemma lem1954596 (_27415 : real) (_27414 : real) : (term138 _27414 _27415) = (term139 _27415 _27414).
Proof. exact (eq_refl (term138 _27414 _27415)). Qed.
Lemma lem1954598 (_27416 : real) (h1 : term10) : term163 _27416.
Proof. exact (@lem1954499 h1 _27416). Qed.
Lemma lem1954599 (_27416 : real) : (term163 _27416) = (term153 _27416).
Proof. exact (eq_refl (term163 _27416)). Qed.
Lemma lem1954600 (_27416 : real) (h1 : term10) : term153 _27416.
Proof. exact (EQ_MP (@lem1954599 _27416) (@lem1954598 _27416 h1)). Qed.
Lemma lem1954601 (_27416 : real) (_27417 : real) (h1 : term10) : term141 _27416 _27417.
Proof. exact (@lem1954600 _27416 h1 _27417). Qed.
Lemma lem1954602 (_27417 : real) (_27416 : real) : (term141 _27416 _27417) = (term122 _27417 _27416).
Proof. exact (eq_refl (term141 _27416 _27417)). Qed.
Lemma lem1954604 (_27418 : real) (h1 : term32) : term179 _27418.
Proof. exact (@lem1954523 h1 _27418). Qed.
Lemma lem1954605 (_27418 : real) : (term179 _27418) = (term109 _27418).
Proof. exact (eq_refl (term179 _27418)). Qed.
Lemma lem1954606 (_27418 : real) (h1 : term32) : term109 _27418.
Proof. exact (EQ_MP (@lem1954605 _27418) (@lem1954604 _27418 h1)). Qed.
Lemma lem1954607 (_27418 : real) (_27419 : real) (h1 : term32) : term180 _27418 _27419.
Proof. exact (@lem1954606 _27418 h1 _27419). Qed.
Lemma lem1954608 (_27418 : real) (_27419 : real) : (term180 _27418 _27419) = (term107 _27418 _27419).
Proof. exact (eq_refl (term180 _27418 _27419)). Qed.
Lemma lem1954639 (_27412 : real) (_27413 : real) (h1 : term27) : term112 _27412 _27413.
Proof. exact (EQ_MP (@lem1954590 _27412 _27413) (@lem1954589 _27412 _27413 h1)). Qed.
Lemma lem1954645 (_27415 : real) (_27414 : real) (h1 : term10) : term139 _27415 _27414.
Proof. exact (EQ_MP (@lem1954596 _27415 _27414) (@lem1954595 _27414 _27415 h1)). Qed.
Lemma lem1954651 (_27417 : real) (_27416 : real) (h1 : term10) : term122 _27417 _27416.
Proof. exact (EQ_MP (@lem1954602 _27417 _27416) (@lem1954601 _27416 _27417 h1)). Qed.
Lemma lem1954655 (x : real) (y : real) (h1 : term63 x y) : term181 x y.
Proof. exact (proj2 (@lem1954430 x y h1)). Qed.
Lemma lem1954661 (_27418 : real) (_27419 : real) (h1 : term32) : term107 _27418 _27419.
Proof. exact (EQ_MP (@lem1954608 _27418 _27419) (@lem1954607 _27418 _27419 h1)). Qed.
Lemma lem1954681 (x : real) (y : real) (h1 : term67 x y) : term182 x y.
Proof. exact (proj1 (@lem1954431 x y h1)). Qed.
Lemma lem1954685 (x : real) (y : real) (h1 : term63 x y) : term33 x y.
Proof. exact (proj1 (@lem1954430 x y h1)). Qed.
Lemma lem1954686 (x : real) (y : real) (h1 : term63 x y) : term183 x y.
Proof. exact (fun h0 : term182 x y => @lem1954685 x y h1). Qed.
Lemma lem1954688 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1954689 (x : real) (y : real) : (term183 x y) = (term33 x y).
Proof. exact (@lem1954688 (term33 x y)). Qed.
Lemma lem1954690 (x : real) (y : real) (h1 : term63 x y) : term33 x y.
Proof. exact (EQ_MP (@lem1954689 x y) (@lem1954686 x y h1)). Qed.
Lemma lem1954692 (b : Prop) (a : Prop) : (a \/ b) = (term185 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1954693 (_27414 : real) (_27415 : real) : (term139 _27415 _27414) = (term186 _27414 _27415).
Proof. exact (@lem1954692 (term181 _27415 _27414) (term19 _27414 _27415)). Qed.
Lemma lem1954695 (a : Prop) : (term187 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1954696 (_27415 : real) (_27414 : real) : (term188 _27415 _27414) = (real_le _27415 _27414).
Proof. exact (@lem1954695 (real_le _27415 _27414)). Qed.
Lemma lem1954697 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1954698 (_27415 : real) (_27414 : real) : (term189 _27415 _27414) = (term190 _27415 _27414).
Proof. exact (MK_COMB (@lem1954697) (@lem1954696 _27415 _27414)). Qed.
Lemma lem1954699 (_27414 : real) (_27415 : real) : (term19 _27414 _27415) = (term19 _27414 _27415).
Proof. exact (eq_refl (term19 _27414 _27415)). Qed.
Lemma lem1954700 (_27414 : real) (_27415 : real) : (term186 _27414 _27415) = (term191 _27414 _27415).
Proof. exact (MK_COMB (@lem1954698 _27415 _27414) (@lem1954699 _27414 _27415)). Qed.
Lemma lem1954701 (_27414 : real) (_27415 : real) : (term139 _27415 _27414) = (term191 _27414 _27415).
Proof. exact (TRANS (@lem1954693 _27414 _27415) (@lem1954700 _27414 _27415)). Qed.
Lemma lem1954704 (_27414 : real) (_27415 : real) (h1 : term10) : term191 _27414 _27415.
Proof. exact (EQ_MP (@lem1954701 _27414 _27415) (@lem1954645 _27415 _27414 h1)). Qed.
Lemma lem1954705 (y : real) (x : real) (h1 : term10) : term192 y x.
Proof. exact (@lem1954704 (sqrt y) (sqrt x) h1). Qed.
Lemma lem1954708 (x : real) (y : real) (h1 : term10) (h2 : term63 x y) : term193 y x.
Proof. exact (@lem1954705 y x h1 (@lem1954690 x y h2)). Qed.
Lemma lem1954709 (x : real) (y : real) (h1 : term10) (h2 : term63 x y) : term194 y x.
Proof. exact (fun h0 : term113 y x => @lem1954708 x y h1 h2). Qed.
Lemma lem1954711 (p : Prop) : (term195 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1954712 (y : real) (x : real) : (term194 y x) = (term193 y x).
Proof. exact (@lem1954711 (term113 y x)). Qed.
Lemma lem1954713 (x : real) (y : real) (h1 : term10) (h2 : term63 x y) : term193 y x.
Proof. exact (EQ_MP (@lem1954712 y x) (@lem1954709 x y h1 h2)). Qed.
Lemma lem1954715 (b : Prop) (a : Prop) : (a \/ b) = (term185 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1954718 (_27412 : real) (_27413 : real) : (term112 _27412 _27413) = (term196 _27412 _27413).
Proof. exact (@lem1954715 (term113 _27412 _27413) (term19 _27412 _27413)). Qed.
Lemma lem1954721 (_27412 : real) (_27413 : real) (h1 : term27) : term196 _27412 _27413.
Proof. exact (EQ_MP (@lem1954718 _27412 _27413) (@lem1954639 _27412 _27413 h1)). Qed.
Lemma lem1954722 (y : real) (x : real) (h1 : term27) : term196 y x.
Proof. exact (@lem1954721 y x h1). Qed.
Lemma lem1954725 (x : real) (y : real) (h1 : term10) (h2 : term27) (h3 : term63 x y) : term19 y x.
Proof. exact (@lem1954722 y x h2 (@lem1954713 x y h1 h3)). Qed.
Lemma lem1954726 (x : real) (y : real) (h1 : term10) (h2 : term27) (h3 : term63 x y) : term197 y x.
Proof. exact (fun h0 : real_lt y x => @lem1954725 x y h1 h2 h3). Qed.
Lemma lem1954728 (p : Prop) : (term195 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1954729 (y : real) (x : real) : (term197 y x) = (term19 y x).
Proof. exact (@lem1954728 (real_lt y x)). Qed.
Lemma lem1954730 (x : real) (y : real) (h1 : term10) (h2 : term27) (h3 : term63 x y) : term19 y x.
Proof. exact (EQ_MP (@lem1954729 y x) (@lem1954726 x y h1 h2 h3)). Qed.
Lemma lem1954736 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1954737 (_27416 : real) (_27417 : real) : (term122 _27417 _27416) = (term198 _27416 _27417).
Proof. exact (@lem1954736 (real_le _27417 _27416) (real_lt _27416 _27417)). Qed.
Lemma lem1954743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1954744 (_27416 : real) (_27417 : real) : (term199 _27417 _27416) = (term200 _27416 _27417).
Proof. exact (MK_COMB (@lem1954743) (@lem1954737 _27416 _27417)). Qed.
Lemma lem1954750 (_27416 : real) (_27417 : real) : (term198 _27416 _27417) = (term198 _27416 _27417).
Proof. exact (eq_refl (term198 _27416 _27417)). Qed.
Lemma lem1954751 (_27416 : real) (_27417 : real) : ((term122 _27417 _27416) = (term198 _27416 _27417)) = ((term198 _27416 _27417) = (term198 _27416 _27417)).
Proof. exact (MK_COMB (@lem1954744 _27416 _27417) (@lem1954750 _27416 _27417)). Qed.
Lemma lem1954753 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1954754 (x : Prop) : (x = x) = True.
Proof. exact (@lem1954753 Prop x). Qed.
Lemma lem1954755 (_27416 : real) (_27417 : real) : ((term198 _27416 _27417) = (term198 _27416 _27417)) = True.
Proof. exact (@lem1954754 (term198 _27416 _27417)). Qed.
Lemma lem1954756 (_27416 : real) (_27417 : real) : ((term122 _27417 _27416) = (term198 _27416 _27417)) = True.
Proof. exact (TRANS (@lem1954751 _27416 _27417) (@lem1954755 _27416 _27417)). Qed.
Lemma lem1954757 (_27416 : real) (_27417 : real) : True = ((term122 _27417 _27416) = (term198 _27416 _27417)).
Proof. exact (SYM (@lem1954756 _27416 _27417)). Qed.
Lemma lem1954758 (_27416 : real) (_27417 : real) : (term122 _27417 _27416) = (term198 _27416 _27417).
Proof. exact (EQ_MP (@lem1954757 _27416 _27417) (@lem0)). Qed.
Lemma lem1954759 (_27416 : real) (_27417 : real) (h1 : term10) : term198 _27416 _27417.
Proof. exact (EQ_MP (@lem1954758 _27416 _27417) (@lem1954651 _27417 _27416 h1)). Qed.
Lemma lem1954761 (b : Prop) (a : Prop) : (a \/ b) = (term185 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1954764 (_27417 : real) (_27416 : real) : (term198 _27416 _27417) = (term201 _27417 _27416).
Proof. exact (@lem1954761 (real_lt _27416 _27417) (real_le _27417 _27416)). Qed.
Lemma lem1954767 (_27417 : real) (_27416 : real) (h1 : term10) : term201 _27417 _27416.
Proof. exact (EQ_MP (@lem1954764 _27417 _27416) (@lem1954759 _27416 _27417 h1)). Qed.
Lemma lem1954768 (x : real) (y : real) (h1 : term10) : term201 x y.
Proof. exact (@lem1954767 x y h1). Qed.
Lemma lem1954771 (x : real) (y : real) (h1 : term10) (h2 : term27) (h3 : term63 x y) : real_le x y.
Proof. exact (@lem1954768 x y h1 (@lem1954730 x y h1 h2 h3)). Qed.
Lemma lem1954772 (x : real) (y : real) (h1 : term10) (h2 : term27) (h3 : term63 x y) : term202 x y.
Proof. exact (fun h0 : term181 x y => @lem1954771 x y h1 h2 h3). Qed.
Lemma lem1954774 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1954775 (x : real) (y : real) : (term202 x y) = (real_le x y).
Proof. exact (@lem1954774 (real_le x y)). Qed.
Lemma lem1954776 (x : real) (y : real) (h1 : term10) (h2 : term27) (h3 : term63 x y) : real_le x y.
Proof. exact (EQ_MP (@lem1954775 x y) (@lem1954772 x y h1 h2 h3)). Qed.
Lemma lem1954779 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1954781 (x : real) (y : real) : (term181 x y) = (term203 x y).
Proof. exact (@lem1954779 (real_le x y)). Qed.
Lemma lem1954784 (x : real) (y : real) (h1 : term63 x y) : term203 x y.
Proof. exact (EQ_MP (@lem1954781 x y) (@lem1954655 x y h1)). Qed.
Lemma lem1954787 (x : real) (y : real) (h1 : term10) (h2 : term27) (h3 : term63 x y) : False.
Proof. exact (@lem1954784 x y h3 (@lem1954776 x y h1 h2 h3)). Qed.
Lemma lem1954788 (x : real) (y : real) (h1 : term10) (h2 : term27) (h3 : term63 x y) : term204.
Proof. exact (fun h0 : ~ False => @lem1954787 x y h1 h2 h3). Qed.
Lemma lem1954790 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1954791 : term204 = False.
Proof. exact (@lem1954790 False). Qed.
Lemma lem1954792 (x : real) (y : real) (h1 : term10) (h2 : term27) (h3 : term63 x y) : False.
Proof. exact (EQ_MP (@lem1954791) (@lem1954788 x y h1 h2 h3)). Qed.
Lemma lem1954794 (x : real) (y : real) (h1 : term67 x y) : real_le x y.
Proof. exact (proj2 (@lem1954431 x y h1)). Qed.
Lemma lem1954795 (x : real) (y : real) (h1 : term67 x y) : term202 x y.
Proof. exact (fun h0 : term181 x y => @lem1954794 x y h1). Qed.
Lemma lem1954797 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1954798 (x : real) (y : real) : (term202 x y) = (real_le x y).
Proof. exact (@lem1954797 (real_le x y)). Qed.
Lemma lem1954799 (x : real) (y : real) (h1 : term67 x y) : real_le x y.
Proof. exact (EQ_MP (@lem1954798 x y) (@lem1954795 x y h1)). Qed.
Lemma lem1954805 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1954806 (_27418 : real) (_27419 : real) : (term107 _27418 _27419) = (term205 _27418 _27419).
Proof. exact (@lem1954805 (term33 _27418 _27419) (term181 _27418 _27419)). Qed.
Lemma lem1954812 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1954813 (_27418 : real) (_27419 : real) : (term206 _27418 _27419) = (term207 _27418 _27419).
Proof. exact (MK_COMB (@lem1954812) (@lem1954806 _27418 _27419)). Qed.
Lemma lem1954819 (_27418 : real) (_27419 : real) : (term205 _27418 _27419) = (term205 _27418 _27419).
Proof. exact (eq_refl (term205 _27418 _27419)). Qed.
Lemma lem1954820 (_27418 : real) (_27419 : real) : ((term107 _27418 _27419) = (term205 _27418 _27419)) = ((term205 _27418 _27419) = (term205 _27418 _27419)).
Proof. exact (MK_COMB (@lem1954813 _27418 _27419) (@lem1954819 _27418 _27419)). Qed.
Lemma lem1954822 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1954823 (x : Prop) : (x = x) = True.
Proof. exact (@lem1954822 Prop x). Qed.
Lemma lem1954824 (_27418 : real) (_27419 : real) : ((term205 _27418 _27419) = (term205 _27418 _27419)) = True.
Proof. exact (@lem1954823 (term205 _27418 _27419)). Qed.
Lemma lem1954825 (_27418 : real) (_27419 : real) : ((term107 _27418 _27419) = (term205 _27418 _27419)) = True.
Proof. exact (TRANS (@lem1954820 _27418 _27419) (@lem1954824 _27418 _27419)). Qed.
Lemma lem1954826 (_27418 : real) (_27419 : real) : True = ((term107 _27418 _27419) = (term205 _27418 _27419)).
Proof. exact (SYM (@lem1954825 _27418 _27419)). Qed.
Lemma lem1954827 (_27418 : real) (_27419 : real) : (term107 _27418 _27419) = (term205 _27418 _27419).
Proof. exact (EQ_MP (@lem1954826 _27418 _27419) (@lem0)). Qed.
Lemma lem1954828 (_27418 : real) (_27419 : real) (h1 : term32) : term205 _27418 _27419.
Proof. exact (EQ_MP (@lem1954827 _27418 _27419) (@lem1954661 _27418 _27419 h1)). Qed.
Lemma lem1954830 (b : Prop) (a : Prop) : (a \/ b) = (term185 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1954831 (_27418 : real) (_27419 : real) : (term205 _27418 _27419) = (term208 _27418 _27419).
Proof. exact (@lem1954830 (term181 _27418 _27419) (term33 _27418 _27419)). Qed.
Lemma lem1954833 (a : Prop) : (term187 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1954834 (_27418 : real) (_27419 : real) : (term188 _27418 _27419) = (real_le _27418 _27419).
Proof. exact (@lem1954833 (real_le _27418 _27419)). Qed.
Lemma lem1954835 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1954836 (_27418 : real) (_27419 : real) : (term189 _27418 _27419) = (term190 _27418 _27419).
Proof. exact (MK_COMB (@lem1954835) (@lem1954834 _27418 _27419)). Qed.
Lemma lem1954837 (_27418 : real) (_27419 : real) : (term33 _27418 _27419) = (term33 _27418 _27419).
Proof. exact (eq_refl (term33 _27418 _27419)). Qed.
Lemma lem1954838 (_27418 : real) (_27419 : real) : (term208 _27418 _27419) = (term28 _27418 _27419).
Proof. exact (MK_COMB (@lem1954836 _27418 _27419) (@lem1954837 _27418 _27419)). Qed.
Lemma lem1954839 (_27418 : real) (_27419 : real) : (term205 _27418 _27419) = (term28 _27418 _27419).
Proof. exact (TRANS (@lem1954831 _27418 _27419) (@lem1954838 _27418 _27419)). Qed.
Lemma lem1954842 (_27418 : real) (_27419 : real) (h1 : term32) : term28 _27418 _27419.
Proof. exact (EQ_MP (@lem1954839 _27418 _27419) (@lem1954828 _27418 _27419 h1)). Qed.
Lemma lem1954843 (x : real) (y : real) (h1 : term32) : term28 x y.
Proof. exact (@lem1954842 x y h1). Qed.
Lemma lem1954846 (x : real) (y : real) (h1 : term32) (h2 : term67 x y) : term33 x y.
Proof. exact (@lem1954843 x y h1 (@lem1954799 x y h2)). Qed.
Lemma lem1954847 (x : real) (y : real) (h1 : term32) (h2 : term67 x y) : term183 x y.
Proof. exact (fun h0 : term182 x y => @lem1954846 x y h1 h2). Qed.
Lemma lem1954849 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1954850 (x : real) (y : real) : (term183 x y) = (term33 x y).
Proof. exact (@lem1954849 (term33 x y)). Qed.
Lemma lem1954851 (x : real) (y : real) (h1 : term32) (h2 : term67 x y) : term33 x y.
Proof. exact (EQ_MP (@lem1954850 x y) (@lem1954847 x y h1 h2)). Qed.
Lemma lem1954854 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1954856 (x : real) (y : real) : (term182 x y) = (term209 x y).
Proof. exact (@lem1954854 (term33 x y)). Qed.
Lemma lem1954859 (x : real) (y : real) (h1 : term67 x y) : term209 x y.
Proof. exact (EQ_MP (@lem1954856 x y) (@lem1954681 x y h1)). Qed.
Lemma lem1954862 (x : real) (y : real) (h1 : term32) (h2 : term67 x y) : False.
Proof. exact (@lem1954859 x y h2 (@lem1954851 x y h1 h2)). Qed.
Lemma lem1954863 (x : real) (y : real) (h1 : term32) (h2 : term67 x y) : term204.
Proof. exact (fun h0 : ~ False => @lem1954862 x y h1 h2). Qed.
Lemma lem1954865 (p : Prop) : (term184 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1954866 : term204 = False.
Proof. exact (@lem1954865 False). Qed.
Lemma lem1954867 (x : real) (y : real) (h1 : term32) (h2 : term67 x y) : False.
Proof. exact (EQ_MP (@lem1954866) (@lem1954863 x y h1 h2)). Qed.
Lemma lem1954868 (x : real) (y : real) (h1 : term10) (h2 : term32) (h3 : term27) (h4 : term38 x y) : False.
Proof. exact (or_elim (@lem1954427 x y h4) (fun h0 : term63 x y => @lem1954792 x y h1 h3 h0) (fun h0 : term67 x y => @lem1954867 x y h2 h0)). Qed.
Lemma lem1954869 (x : real) (y : real) (h1 : term10) (h2 : term32) (h3 : term27) (h4 : term38 x y) : (term38 x y) = False.
Proof. exact (prop_ext (fun h5 : term38 x y => @lem1954868 x y h1 h2 h3 h4) (fun h5 : False => @lem1954427 x y h4)). Qed.
Lemma lem1954870 (x : real) (y : real) (h1 : term10) (h2 : term32) (h3 : term27) (h4 : term38 x y) : False.
Proof. exact (EQ_MP (@lem1954869 x y h1 h2 h3 h4) (@lem1954427 x y h4)). Qed.
Lemma lem1954871 (x : real) (h1 : term10) (h2 : term32) (h3 : term27) (h4 : term47 x) : False.
Proof. exact (ex_elim (@lem1954286 x h4) (fun y : real => fun h0 : term46 x y => @lem1954870 x y h1 h2 h3 h0)). Qed.
Lemma lem1954872 (h1 : term10) (h2 : term32) (h3 : term27) (h4 : term3) : False.
Proof. exact (ex_elim (@lem1953856 h4) (fun x : real => fun h0 : term52 x => @lem1954871 x h1 h2 h3 h0)). Qed.
Lemma lem1954873 (h1 : term32) (h2 : term27) (h3 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1954872 h0 h1 h2 h3). Qed.
Lemma lem1954874 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1954875 (h1 : term32) (h2 : term27) (h3 : term3) : term9.
Proof. exact (EQ_MP (@lem1954874) (@lem1954873 h1 h2 h3)). Qed.
Lemma lem1954876 (h1 : term32) (h2 : term3) : term13.
Proof. exact (fun h0 : term27 => @lem1954875 h1 h0 h2). Qed.
Lemma lem1954877 (h1 : term3) : term16.
Proof. exact (fun h0 : term32 => @lem1954876 h0 h1). Qed.
Lemma lem1954878 : term18.
Proof. exact (fun h0 : term3 => @lem1954877 h0). Qed.
Lemma lem1954879 : term4.
Proof. exact (EQ_MP (@lem1953494) (@lem1954878)). Qed.
Lemma lem1954881 : term4.
Proof. exact (@lem1953312 (@lem1954879)). Qed.
Lemma lem1954882 (h1 : term3) : term15.
Proof. exact (@lem1954881 (@lem1953297 h1)). Qed.
Lemma lem1954883 (h1 : term3) : term12.
Proof. exact (@lem1954882 h1 (@lem1951675)). Qed.
Lemma lem1954884 (h1 : term3) : term8.
Proof. exact (@lem1954883 h1 (@lem1950431)). Qed.
Lemma lem1954885 (h1 : term3) : False.
Proof. exact (@lem1954884 h1 (@lem1376537)). Qed.
Lemma lem1954886 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1954885 h1) (fun h2 : False => @lem1953297 h1)). Qed.
Lemma lem1954887 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1954886 h1) (@lem1953297 h1)). Qed.
Lemma lem1954888 : term2.
Proof. exact (fun h0 : term3 => @lem1954887 h0). Qed.
Lemma lem1954889 : term1.
Proof. exact (EQ_MP (@lem1953296) (@lem1954888)). Qed.
