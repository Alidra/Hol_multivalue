Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INF_LT_FINITE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import INF_FINITE_spec.
Require Import REAL_LET_TRANS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
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
Lemma lem5229359 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5229360 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5229361 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5229360 t1) (@lem5229359 t1)). Qed.
Lemma lem5229362 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5229361 t1 t2). Qed.
Lemma lem5229363 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5229364 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5229363 t1 t2) (@lem5229362 t1 t2)). Qed.
Lemma lem5229365 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5229364 t1 t2 t3). Qed.
Lemma lem5229366 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5229367 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5229366 t1 t2 t3) (@lem5229365 t1 t2 t3)). Qed.
Lemma lem5229368 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5229367 t1 t2 t3)). Qed.
Lemma lem5229370 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5229371 : term8 = term9.
Proof. exact (@lem5229370 term8). Qed.
Lemma lem5229372 : term9 = term8.
Proof. exact (SYM (@lem5229371)). Qed.
Lemma lem5229373 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5229376 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5229377 : term12.
Proof. exact (fun h0 : term11 => @lem5229376 h0). Qed.
Lemma lem5229378 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5229379 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5229380 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5229378 h2 (@lem5229379 h1)). Qed.
Lemma lem5229381 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem5229380 h1 h0). Qed.
Lemma lem5229382 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5229383 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5229381 h1 (@lem5229382 h2)). Qed.
Lemma lem5229384 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem5229383 h0 h1). Qed.
Lemma lem5229385 : term14.
Proof. exact (fun h0 : term12 => @lem5229384 h0). Qed.
Lemma lem5229388 : term12.
Proof. exact (@lem5229385 (@lem5229377)). Qed.
Lemma lem5229472 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5229473 : term15 = term16.
Proof. exact (@lem5229472 term17). Qed.
Lemma lem5229490 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem5229491 : term19 = term20.
Proof. exact (MK_COMB (@lem5229490) (@lem5229473)). Qed.
Lemma lem5229494 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem5229501 : term11 = term22.
Proof. exact (MK_COMB (@lem5229494) (@lem5229491)). Qed.
Lemma lem5229506 (s : real -> Prop) (x : real) : (term23 s x) = (term23 s x).
Proof. exact (eq_refl (term23 s x)). Qed.
Lemma lem5229507 (s : real -> Prop) : (term24 s) = (term24 s).
Proof. exact (fun_ext (fun x : real => @lem5229506 s x)). Qed.
Lemma lem5229508 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5229509 (s : real -> Prop) : (term25 s) = (term25 s).
Proof. exact (MK_COMB (@lem5229508) (@lem5229507 s)). Qed.
Lemma lem5229512 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5229513 (s : real -> Prop) : (term27 s) = (term27 s).
Proof. exact (MK_COMB (@lem5229512 s) (@lem5229509 s)). Qed.
Lemma lem5229522 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5229523 (s : real -> Prop) : (term29 s) = (term29 s).
Proof. exact (MK_COMB (@lem5229522 s) (@lem5229513 s)). Qed.
Lemma lem5229524 : term30 = term30.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5229523 s)). Qed.
Lemma lem5229525 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5229526 : term17 = term17.
Proof. exact (MK_COMB (@lem5229525) (@lem5229524)). Qed.
Lemma lem5229527 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5229528 : term16 = term16.
Proof. exact (MK_COMB (@lem5229527) (@lem5229526)). Qed.
Lemma lem5229537 (y : real) (x : real) (z : real) : (term31 y x z) = (term31 y x z).
Proof. exact (eq_refl (term31 y x z)). Qed.
Lemma lem5229538 (y : real) (x : real) : (term32 y x) = (term32 y x).
Proof. exact (fun_ext (fun z : real => @lem5229537 y x z)). Qed.
Lemma lem5229539 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5229540 (y : real) (x : real) : (term33 y x) = (term33 y x).
Proof. exact (MK_COMB (@lem5229539) (@lem5229538 y x)). Qed.
Lemma lem5229541 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem5229540 y x)). Qed.
Lemma lem5229542 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5229543 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem5229542) (@lem5229541 x)). Qed.
Lemma lem5229544 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem5229543 x)). Qed.
Lemma lem5229545 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5229546 : term37 = term37.
Proof. exact (MK_COMB (@lem5229545) (@lem5229544)). Qed.
Lemma lem5229547 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5229548 : term18 = term18.
Proof. exact (MK_COMB (@lem5229547) (@lem5229546)). Qed.
Lemma lem5229549 : term20 = term20.
Proof. exact (MK_COMB (@lem5229548) (@lem5229528)). Qed.
Lemma lem5229554 (s : real -> Prop) (x : real) (a : real) : (term38 s x a) = (term38 s x a).
Proof. exact (eq_refl (term38 s x a)). Qed.
Lemma lem5229555 (s : real -> Prop) (a : real) : (term39 s a) = (term39 s a).
Proof. exact (fun_ext (fun x : real => @lem5229554 s x a)). Qed.
Lemma lem5229556 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5229557 (s : real -> Prop) (a : real) : (term40 s a) = (term40 s a).
Proof. exact (MK_COMB (@lem5229556) (@lem5229555 s a)). Qed.
Lemma lem5229560 (s : real -> Prop) (a : real) : (term41 s a) = (term41 s a).
Proof. exact (eq_refl (term41 s a)). Qed.
Lemma lem5229561 (s : real -> Prop) (a : real) : ((term42 s a) = (term40 s a)) = ((term42 s a) = (term40 s a)).
Proof. exact (MK_COMB (@lem5229560 s a) (@lem5229557 s a)). Qed.
Lemma lem5229570 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5229571 (s : real -> Prop) (a : real) : (term43 s a) = (term43 s a).
Proof. exact (MK_COMB (@lem5229570 s) (@lem5229561 s a)). Qed.
Lemma lem5229572 (s : real -> Prop) : (term44 s) = (term44 s).
Proof. exact (fun_ext (fun a : real => @lem5229571 s a)). Qed.
Lemma lem5229573 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5229574 (s : real -> Prop) : (term45 s) = (term45 s).
Proof. exact (MK_COMB (@lem5229573) (@lem5229572 s)). Qed.
Lemma lem5229575 : term46 = term46.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5229574 s)). Qed.
Lemma lem5229576 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5229577 : term8 = term8.
Proof. exact (MK_COMB (@lem5229576) (@lem5229575)). Qed.
Lemma lem5229578 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5229579 : term10 = term10.
Proof. exact (MK_COMB (@lem5229578) (@lem5229577)). Qed.
Lemma lem5229580 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5229581 : term21 = term21.
Proof. exact (MK_COMB (@lem5229580) (@lem5229579)). Qed.
Lemma lem5229582 : term22 = term22.
Proof. exact (MK_COMB (@lem5229581) (@lem5229549)). Qed.
Lemma lem5229655 : term11 = term22.
Proof. exact (TRANS (@lem5229501) (@lem5229582)). Qed.
Lemma lem5229656 : term22 = term11.
Proof. exact (SYM (@lem5229655)). Qed.
Lemma lem5229657 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5229658 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem5229659 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem5229675 (s : real -> Prop) (x : real) (a : real) : (term47 s x a) = (term48 s x a).
Proof. exact (@lem17045 (@IN real x s) (real_lt x a)). Qed.
Lemma lem5229678 (s : real -> Prop) (x : real) (a : real) : (term38 s x a) = (term38 s x a).
Proof. exact (eq_refl (term38 s x a)). Qed.
Lemma lem5229679 (P : real -> Prop) : (term49 P) = (term50 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5229680 (s : real -> Prop) (a : real) : (term51 s a) = (term52 s a).
Proof. exact (@lem5229679 (term39 s a)). Qed.
Lemma lem5229681 (s : real -> Prop) (x : real) (a : real) : (term53 s a x) = (term38 s x a).
Proof. exact (eq_refl (term53 s a x)). Qed.
Lemma lem5229682 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5229683 (s : real -> Prop) (x : real) (a : real) : (term54 s a x) = (term47 s x a).
Proof. exact (MK_COMB (@lem5229682) (@lem5229681 s x a)). Qed.
Lemma lem5229684 (s : real -> Prop) (x : real) (a : real) : (term54 s a x) = (term48 s x a).
Proof. exact (TRANS (@lem5229683 s x a) (@lem5229675 s x a)). Qed.
Lemma lem5229685 (s : real -> Prop) (a : real) : (term55 s a) = (term56 s a).
Proof. exact (fun_ext (fun x : real => @lem5229684 s x a)). Qed.
Lemma lem5229686 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5229687 (s : real -> Prop) (a : real) : (term52 s a) = (term57 s a).
Proof. exact (MK_COMB (@lem5229686) (@lem5229685 s a)). Qed.
Lemma lem5229688 (s : real -> Prop) (a : real) : (term51 s a) = (term57 s a).
Proof. exact (TRANS (@lem5229680 s a) (@lem5229687 s a)). Qed.
Lemma lem5229689 (s : real -> Prop) (a : real) : (term39 s a) = (term39 s a).
Proof. exact (fun_ext (fun x : real => @lem5229678 s x a)). Qed.
Lemma lem5229690 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5229691 (s : real -> Prop) (a : real) : (term40 s a) = (term40 s a).
Proof. exact (MK_COMB (@lem5229690) (@lem5229689 s a)). Qed.
Lemma lem5229693 (s : real -> Prop) (a : real) : (term58 s a) = (term58 s a).
Proof. exact (eq_refl (term58 s a)). Qed.
Lemma lem5229694 (s : real -> Prop) (a : real) : (term59 s a) = (term59 s a).
Proof. exact (MK_COMB (@lem5229693 s a) (@lem5229691 s a)). Qed.
Lemma lem5229696 (s : real -> Prop) (a : real) : (term60 s a) = (term60 s a).
Proof. exact (eq_refl (term60 s a)). Qed.
Lemma lem5229697 (s : real -> Prop) (a : real) : (term61 s a) = (term62 s a).
Proof. exact (MK_COMB (@lem5229696 s a) (@lem5229688 s a)). Qed.
Lemma lem5229698 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5229699 (s : real -> Prop) (a : real) : (term63 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem5229698) (@lem5229697 s a)). Qed.
Lemma lem5229700 (s : real -> Prop) (a : real) : (term65 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem5229699 s a) (@lem5229694 s a)). Qed.
Lemma lem5229701 (s : real -> Prop) (a : real) : (term67 s a) = (term65 s a).
Proof. exact (@lem17646 (term42 s a) (term40 s a)). Qed.
Lemma lem5229702 (s : real -> Prop) (a : real) : (term67 s a) = (term66 s a).
Proof. exact (TRANS (@lem5229701 s a) (@lem5229700 s a)). Qed.
Lemma lem5229704 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5229705 (s : real -> Prop) (a : real) : (term69 s a) = (term70 s a).
Proof. exact (MK_COMB (@lem5229704 s) (@lem5229702 s a)). Qed.
Lemma lem5229706 (s : real -> Prop) (a : real) : (term71 s a) = (term69 s a).
Proof. exact (@lem17362 (term72 s) ((term42 s a) = (term40 s a))). Qed.
Lemma lem5229707 (s : real -> Prop) (a : real) : (term71 s a) = (term70 s a).
Proof. exact (TRANS (@lem5229706 s a) (@lem5229705 s a)). Qed.
Lemma lem5229708 (P : real -> Prop) : (term73 P) = (term74 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5229709 (s : real -> Prop) : (term75 s) = (term76 s).
Proof. exact (@lem5229708 (term44 s)). Qed.
Lemma lem5229710 (s : real -> Prop) (a : real) : (term77 s a) = (term43 s a).
Proof. exact (eq_refl (term77 s a)). Qed.
Lemma lem5229711 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5229712 (s : real -> Prop) (a : real) : (term78 s a) = (term71 s a).
Proof. exact (MK_COMB (@lem5229711) (@lem5229710 s a)). Qed.
Lemma lem5229713 (s : real -> Prop) (a : real) : (term78 s a) = (term70 s a).
Proof. exact (TRANS (@lem5229712 s a) (@lem5229707 s a)). Qed.
Lemma lem5229714 (s : real -> Prop) : (term79 s) = (term80 s).
Proof. exact (fun_ext (fun a : real => @lem5229713 s a)). Qed.
Lemma lem5229715 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5229716 (s : real -> Prop) : (term76 s) = (term81 s).
Proof. exact (MK_COMB (@lem5229715) (@lem5229714 s)). Qed.
Lemma lem5229717 (s : real -> Prop) : (term75 s) = (term81 s).
Proof. exact (TRANS (@lem5229709 s) (@lem5229716 s)). Qed.
Lemma lem5229718 (P : type1022) : (term82 P) = (term83 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5229719 : term10 = term84.
Proof. exact (@lem5229718 term46). Qed.
Lemma lem5229720 (s : real -> Prop) : (term85 s) = (term45 s).
Proof. exact (eq_refl (term85 s)). Qed.
Lemma lem5229721 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5229722 (s : real -> Prop) : (term86 s) = (term75 s).
Proof. exact (MK_COMB (@lem5229721) (@lem5229720 s)). Qed.
Lemma lem5229723 (s : real -> Prop) : (term86 s) = (term81 s).
Proof. exact (TRANS (@lem5229722 s) (@lem5229717 s)). Qed.
Lemma lem5229724 : term87 = term88.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5229723 s)). Qed.
Lemma lem5229725 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5229726 : term84 = term89.
Proof. exact (MK_COMB (@lem5229725) (@lem5229724)). Qed.
Lemma lem5229727 : term10 = term89.
Proof. exact (TRANS (@lem5229719) (@lem5229726)). Qed.
Lemma lem5229733 {A : Type'} (P : Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem5229734 (P : Prop) (Q : real -> Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem5229733 real P Q). Qed.
Lemma lem5229735 (s : real -> Prop) : (term94 s) = (term95 s).
Proof. exact (@lem5229734 (term72 s) (term96 s)). Qed.
Lemma lem5229736 (s : real -> Prop) (a : real) : (term97 s a) = (term66 s a).
Proof. exact (eq_refl (term97 s a)). Qed.
Lemma lem5229737 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5229738 (s : real -> Prop) (a : real) : (term98 s a) = (term70 s a).
Proof. exact (MK_COMB (@lem5229737 s) (@lem5229736 s a)). Qed.
Lemma lem5229739 (s : real -> Prop) : (term99 s) = (term80 s).
Proof. exact (fun_ext (fun a : real => @lem5229738 s a)). Qed.
Lemma lem5229740 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5229741 (s : real -> Prop) : (term94 s) = (term81 s).
Proof. exact (MK_COMB (@lem5229740) (@lem5229739 s)). Qed.
Lemma lem5229742 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5229743 (s : real -> Prop) : (term100 s) = (term101 s).
Proof. exact (MK_COMB (@lem5229742) (@lem5229741 s)). Qed.
Lemma lem5229744 (s : real -> Prop) (a : real) : (term97 s a) = (term66 s a).
Proof. exact (eq_refl (term97 s a)). Qed.
Lemma lem5229745 (s : real -> Prop) : (term102 s) = (term96 s).
Proof. exact (fun_ext (fun a : real => @lem5229744 s a)). Qed.
Lemma lem5229746 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5229747 (s : real -> Prop) : (term103 s) = (term104 s).
Proof. exact (MK_COMB (@lem5229746) (@lem5229745 s)). Qed.
Lemma lem5229748 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5229749 (s : real -> Prop) : (term95 s) = (term105 s).
Proof. exact (MK_COMB (@lem5229748 s) (@lem5229747 s)). Qed.
Lemma lem5229750 (s : real -> Prop) : ((term94 s) = (term95 s)) = ((term81 s) = (term105 s)).
Proof. exact (MK_COMB (@lem5229743 s) (@lem5229749 s)). Qed.
Lemma lem5229751 (s : real -> Prop) : (term81 s) = (term105 s).
Proof. exact (EQ_MP (@lem5229750 s) (@lem5229735 s)). Qed.
Lemma lem5229753 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5229754 (P : real -> Prop) (Q : real -> Prop) : (term108 P Q) = (term109 P Q).
Proof. exact (@lem5229753 real P Q). Qed.
Lemma lem5229755 (s : real -> Prop) : (term110 s) = (term111 s).
Proof. exact (@lem5229754 (term112 s) (term113 s)). Qed.
Lemma lem5229756 (s : real -> Prop) (a : real) : (term114 s a) = (term62 s a).
Proof. exact (eq_refl (term114 s a)). Qed.
Lemma lem5229757 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5229758 (s : real -> Prop) (a : real) : (term115 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem5229757) (@lem5229756 s a)). Qed.
Lemma lem5229759 (s : real -> Prop) (a : real) : (term116 s a) = (term59 s a).
Proof. exact (eq_refl (term116 s a)). Qed.
Lemma lem5229760 (s : real -> Prop) (a : real) : (term117 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem5229758 s a) (@lem5229759 s a)). Qed.
Lemma lem5229761 (s : real -> Prop) : (term118 s) = (term96 s).
Proof. exact (fun_ext (fun a : real => @lem5229760 s a)). Qed.
Lemma lem5229762 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5229763 (s : real -> Prop) : (term110 s) = (term104 s).
Proof. exact (MK_COMB (@lem5229762) (@lem5229761 s)). Qed.
Lemma lem5229764 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5229765 (s : real -> Prop) : (term119 s) = (term120 s).
Proof. exact (MK_COMB (@lem5229764) (@lem5229763 s)). Qed.
Lemma lem5229766 (s : real -> Prop) (a : real) : (term114 s a) = (term62 s a).
Proof. exact (eq_refl (term114 s a)). Qed.
Lemma lem5229767 (s : real -> Prop) : (term121 s) = (term112 s).
Proof. exact (fun_ext (fun a : real => @lem5229766 s a)). Qed.
Lemma lem5229768 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5229769 (s : real -> Prop) : (term122 s) = (term123 s).
Proof. exact (MK_COMB (@lem5229768) (@lem5229767 s)). Qed.
Lemma lem5229770 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5229771 (s : real -> Prop) : (term124 s) = (term125 s).
Proof. exact (MK_COMB (@lem5229770) (@lem5229769 s)). Qed.
Lemma lem5229772 (s : real -> Prop) (a : real) : (term116 s a) = (term59 s a).
Proof. exact (eq_refl (term116 s a)). Qed.
Lemma lem5229773 (s : real -> Prop) : (term126 s) = (term113 s).
Proof. exact (fun_ext (fun a : real => @lem5229772 s a)). Qed.
Lemma lem5229774 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5229775 (s : real -> Prop) : (term127 s) = (term128 s).
Proof. exact (MK_COMB (@lem5229774) (@lem5229773 s)). Qed.
Lemma lem5229776 (s : real -> Prop) : (term111 s) = (term129 s).
Proof. exact (MK_COMB (@lem5229771 s) (@lem5229775 s)). Qed.
Lemma lem5229777 (s : real -> Prop) : ((term110 s) = (term111 s)) = ((term104 s) = (term129 s)).
Proof. exact (MK_COMB (@lem5229765 s) (@lem5229776 s)). Qed.
Lemma lem5229778 (s : real -> Prop) : (term104 s) = (term129 s).
Proof. exact (EQ_MP (@lem5229777 s) (@lem5229755 s)). Qed.
Lemma lem5229971 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5229972 (s : real -> Prop) : (term105 s) = (term130 s).
Proof. exact (MK_COMB (@lem5229971 s) (@lem5229778 s)). Qed.
Lemma lem5229973 (s : real -> Prop) : (term81 s) = (term130 s).
Proof. exact (TRANS (@lem5229751 s) (@lem5229972 s)). Qed.
Lemma lem5229974 : term88 = term131.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5229973 s)). Qed.
Lemma lem5229975 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5229976 : term89 = term132.
Proof. exact (MK_COMB (@lem5229975) (@lem5229974)). Qed.
Lemma lem5230026 {A : Type'} (P : Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5230027 (P : Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem5230026 real P Q). Qed.
Lemma lem5230028 (s : real -> Prop) (a : real) : (term133 s a) = (term134 s a).
Proof. exact (@lem5230027 (term135 s a) (term39 s a)). Qed.
Lemma lem5230029 (s : real -> Prop) (x : real) (a : real) : (term53 s a x) = (term38 s x a).
Proof. exact (eq_refl (term53 s a x)). Qed.
Lemma lem5230030 (s : real -> Prop) (a : real) : (term136 s a) = (term39 s a).
Proof. exact (fun_ext (fun x : real => @lem5230029 s x a)). Qed.
Lemma lem5230031 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5230032 (s : real -> Prop) (a : real) : (term137 s a) = (term40 s a).
Proof. exact (MK_COMB (@lem5230031) (@lem5230030 s a)). Qed.
Lemma lem5230033 (s : real -> Prop) (a : real) : (term58 s a) = (term58 s a).
Proof. exact (eq_refl (term58 s a)). Qed.
Lemma lem5230034 (s : real -> Prop) (a : real) : (term133 s a) = (term59 s a).
Proof. exact (MK_COMB (@lem5230033 s a) (@lem5230032 s a)). Qed.
Lemma lem5230035 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5230036 (s : real -> Prop) (a : real) : (term138 s a) = (term139 s a).
Proof. exact (MK_COMB (@lem5230035) (@lem5230034 s a)). Qed.
Lemma lem5230037 (s : real -> Prop) (x : real) (a : real) : (term53 s a x) = (term38 s x a).
Proof. exact (eq_refl (term53 s a x)). Qed.
Lemma lem5230038 (s : real -> Prop) (a : real) : (term58 s a) = (term58 s a).
Proof. exact (eq_refl (term58 s a)). Qed.
Lemma lem5230039 (s : real -> Prop) (x : real) (a : real) : (term140 s a x) = (term141 s x a).
Proof. exact (MK_COMB (@lem5230038 s a) (@lem5230037 s x a)). Qed.
Lemma lem5230040 (s : real -> Prop) (a : real) : (term142 s a) = (term143 s a).
Proof. exact (fun_ext (fun x : real => @lem5230039 s x a)). Qed.
Lemma lem5230041 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5230042 (s : real -> Prop) (a : real) : (term134 s a) = (term144 s a).
Proof. exact (MK_COMB (@lem5230041) (@lem5230040 s a)). Qed.
Lemma lem5230043 (s : real -> Prop) (a : real) : ((term133 s a) = (term134 s a)) = ((term59 s a) = (term144 s a)).
Proof. exact (MK_COMB (@lem5230036 s a) (@lem5230042 s a)). Qed.
Lemma lem5230044 (s : real -> Prop) (a : real) : (term59 s a) = (term144 s a).
Proof. exact (EQ_MP (@lem5230043 s a) (@lem5230028 s a)). Qed.
Lemma lem5230045 (s : real -> Prop) : (term113 s) = (term145 s).
Proof. exact (fun_ext (fun a : real => @lem5230044 s a)). Qed.
Lemma lem5230046 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5230047 (s : real -> Prop) : (term128 s) = (term146 s).
Proof. exact (MK_COMB (@lem5230046) (@lem5230045 s)). Qed.
Lemma lem5230048 (s : real -> Prop) : (term125 s) = (term125 s).
Proof. exact (eq_refl (term125 s)). Qed.
Lemma lem5230049 (s : real -> Prop) : (term129 s) = (term147 s).
Proof. exact (MK_COMB (@lem5230048 s) (@lem5230047 s)). Qed.
Lemma lem5230051 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term107 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5230052 (P : real -> Prop) (Q : real -> Prop) : (term109 P Q) = (term108 P Q).
Proof. exact (@lem5230051 real P Q). Qed.
Lemma lem5230053 (s : real -> Prop) : (term148 s) = (term149 s).
Proof. exact (@lem5230052 (term112 s) (term145 s)). Qed.
Lemma lem5230054 (s : real -> Prop) (a : real) : (term114 s a) = (term62 s a).
Proof. exact (eq_refl (term114 s a)). Qed.
Lemma lem5230055 (s : real -> Prop) : (term121 s) = (term112 s).
Proof. exact (fun_ext (fun a : real => @lem5230054 s a)). Qed.
Lemma lem5230056 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5230057 (s : real -> Prop) : (term122 s) = (term123 s).
Proof. exact (MK_COMB (@lem5230056) (@lem5230055 s)). Qed.
Lemma lem5230058 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5230059 (s : real -> Prop) : (term124 s) = (term125 s).
Proof. exact (MK_COMB (@lem5230058) (@lem5230057 s)). Qed.
Lemma lem5230060 (s : real -> Prop) (a : real) : (term150 s a) = (term144 s a).
Proof. exact (eq_refl (term150 s a)). Qed.
Lemma lem5230061 (s : real -> Prop) : (term151 s) = (term145 s).
Proof. exact (fun_ext (fun a : real => @lem5230060 s a)). Qed.
Lemma lem5230062 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5230063 (s : real -> Prop) : (term152 s) = (term146 s).
Proof. exact (MK_COMB (@lem5230062) (@lem5230061 s)). Qed.
Lemma lem5230064 (s : real -> Prop) : (term148 s) = (term147 s).
Proof. exact (MK_COMB (@lem5230059 s) (@lem5230063 s)). Qed.
Lemma lem5230065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5230066 (s : real -> Prop) : (term153 s) = (term154 s).
Proof. exact (MK_COMB (@lem5230065) (@lem5230064 s)). Qed.
Lemma lem5230067 (s : real -> Prop) (a : real) : (term114 s a) = (term62 s a).
Proof. exact (eq_refl (term114 s a)). Qed.
Lemma lem5230068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5230069 (s : real -> Prop) (a : real) : (term115 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem5230068) (@lem5230067 s a)). Qed.
Lemma lem5230070 (s : real -> Prop) (a : real) : (term150 s a) = (term144 s a).
Proof. exact (eq_refl (term150 s a)). Qed.
Lemma lem5230071 (s : real -> Prop) (a : real) : (term155 s a) = (term156 s a).
Proof. exact (MK_COMB (@lem5230069 s a) (@lem5230070 s a)). Qed.
Lemma lem5230072 (s : real -> Prop) : (term157 s) = (term158 s).
Proof. exact (fun_ext (fun a : real => @lem5230071 s a)). Qed.
Lemma lem5230073 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5230074 (s : real -> Prop) : (term149 s) = (term159 s).
Proof. exact (MK_COMB (@lem5230073) (@lem5230072 s)). Qed.
Lemma lem5230075 (s : real -> Prop) : ((term148 s) = (term149 s)) = ((term147 s) = (term159 s)).
Proof. exact (MK_COMB (@lem5230066 s) (@lem5230074 s)). Qed.
Lemma lem5230076 (s : real -> Prop) : (term147 s) = (term159 s).
Proof. exact (EQ_MP (@lem5230075 s) (@lem5230053 s)). Qed.
Lemma lem5230078 {A : Type'} (P : Prop) (Q : A -> Prop) : (term160 A P Q) = (term161 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5230079 (P : Prop) (Q : real -> Prop) : (term162 P Q) = (term163 P Q).
Proof. exact (@lem5230078 real P Q). Qed.
Lemma lem5230080 (s : real -> Prop) (a : real) : (term164 s a) = (term165 s a).
Proof. exact (@lem5230079 (term62 s a) (term143 s a)). Qed.
Lemma lem5230081 (s : real -> Prop) (x : real) (a : real) : (term166 s a x) = (term141 s x a).
Proof. exact (eq_refl (term166 s a x)). Qed.
Lemma lem5230082 (s : real -> Prop) (a : real) : (term167 s a) = (term143 s a).
Proof. exact (fun_ext (fun x : real => @lem5230081 s x a)). Qed.
Lemma lem5230083 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5230084 (s : real -> Prop) (a : real) : (term168 s a) = (term144 s a).
Proof. exact (MK_COMB (@lem5230083) (@lem5230082 s a)). Qed.
Lemma lem5230085 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (eq_refl (term64 s a)). Qed.
Lemma lem5230086 (s : real -> Prop) (a : real) : (term164 s a) = (term156 s a).
Proof. exact (MK_COMB (@lem5230085 s a) (@lem5230084 s a)). Qed.
Lemma lem5230087 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5230088 (s : real -> Prop) (a : real) : (term169 s a) = (term170 s a).
Proof. exact (MK_COMB (@lem5230087) (@lem5230086 s a)). Qed.
Lemma lem5230089 (s : real -> Prop) (x : real) (a : real) : (term166 s a x) = (term141 s x a).
Proof. exact (eq_refl (term166 s a x)). Qed.
Lemma lem5230090 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (eq_refl (term64 s a)). Qed.
Lemma lem5230091 (s : real -> Prop) (x : real) (a : real) : (term171 s a x) = (term172 s x a).
Proof. exact (MK_COMB (@lem5230090 s a) (@lem5230089 s x a)). Qed.
Lemma lem5230092 (s : real -> Prop) (a : real) : (term173 s a) = (term174 s a).
Proof. exact (fun_ext (fun x : real => @lem5230091 s x a)). Qed.
Lemma lem5230093 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5230094 (s : real -> Prop) (a : real) : (term165 s a) = (term175 s a).
Proof. exact (MK_COMB (@lem5230093) (@lem5230092 s a)). Qed.
Lemma lem5230095 (s : real -> Prop) (a : real) : ((term164 s a) = (term165 s a)) = ((term156 s a) = (term175 s a)).
Proof. exact (MK_COMB (@lem5230088 s a) (@lem5230094 s a)). Qed.
Lemma lem5230096 (s : real -> Prop) (a : real) : (term156 s a) = (term175 s a).
Proof. exact (EQ_MP (@lem5230095 s a) (@lem5230080 s a)). Qed.
Lemma lem5230097 (s : real -> Prop) : (term158 s) = (term176 s).
Proof. exact (fun_ext (fun a : real => @lem5230096 s a)). Qed.
Lemma lem5230098 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5230099 (s : real -> Prop) : (term159 s) = (term177 s).
Proof. exact (MK_COMB (@lem5230098) (@lem5230097 s)). Qed.
Lemma lem5230100 (s : real -> Prop) : (term147 s) = (term177 s).
Proof. exact (TRANS (@lem5230076 s) (@lem5230099 s)). Qed.
Lemma lem5230101 (s : real -> Prop) : (term129 s) = (term177 s).
Proof. exact (TRANS (@lem5230049 s) (@lem5230100 s)). Qed.
Lemma lem5230102 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5230103 (s : real -> Prop) : (term130 s) = (term178 s).
Proof. exact (MK_COMB (@lem5230102 s) (@lem5230101 s)). Qed.
Lemma lem5230105 {A : Type'} (P : Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5230106 (P : Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem5230105 real P Q). Qed.
Lemma lem5230107 (s : real -> Prop) : (term179 s) = (term180 s).
Proof. exact (@lem5230106 (term72 s) (term176 s)). Qed.
Lemma lem5230108 (s : real -> Prop) (a : real) : (term181 s a) = (term175 s a).
Proof. exact (eq_refl (term181 s a)). Qed.
Lemma lem5230109 (s : real -> Prop) : (term182 s) = (term176 s).
Proof. exact (fun_ext (fun a : real => @lem5230108 s a)). Qed.
Lemma lem5230110 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5230111 (s : real -> Prop) : (term183 s) = (term177 s).
Proof. exact (MK_COMB (@lem5230110) (@lem5230109 s)). Qed.
Lemma lem5230112 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5230113 (s : real -> Prop) : (term179 s) = (term178 s).
Proof. exact (MK_COMB (@lem5230112 s) (@lem5230111 s)). Qed.
Lemma lem5230114 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5230115 (s : real -> Prop) : (term184 s) = (term185 s).
Proof. exact (MK_COMB (@lem5230114) (@lem5230113 s)). Qed.
Lemma lem5230116 (s : real -> Prop) (a : real) : (term181 s a) = (term175 s a).
Proof. exact (eq_refl (term181 s a)). Qed.
Lemma lem5230117 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5230118 (s : real -> Prop) (a : real) : (term186 s a) = (term187 s a).
Proof. exact (MK_COMB (@lem5230117 s) (@lem5230116 s a)). Qed.
Lemma lem5230119 (s : real -> Prop) : (term188 s) = (term189 s).
Proof. exact (fun_ext (fun a : real => @lem5230118 s a)). Qed.
Lemma lem5230120 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5230121 (s : real -> Prop) : (term180 s) = (term190 s).
Proof. exact (MK_COMB (@lem5230120) (@lem5230119 s)). Qed.
Lemma lem5230122 (s : real -> Prop) : ((term179 s) = (term180 s)) = ((term178 s) = (term190 s)).
Proof. exact (MK_COMB (@lem5230115 s) (@lem5230121 s)). Qed.
Lemma lem5230123 (s : real -> Prop) : (term178 s) = (term190 s).
Proof. exact (EQ_MP (@lem5230122 s) (@lem5230107 s)). Qed.
Lemma lem5230125 {A : Type'} (P : Prop) (Q : A -> Prop) : (term91 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5230126 (P : Prop) (Q : real -> Prop) : (term93 P Q) = (term92 P Q).
Proof. exact (@lem5230125 real P Q). Qed.
Lemma lem5230127 (s : real -> Prop) (a : real) : (term191 s a) = (term192 s a).
Proof. exact (@lem5230126 (term72 s) (term174 s a)). Qed.
Lemma lem5230128 (s : real -> Prop) (x : real) (a : real) : (term193 s a x) = (term172 s x a).
Proof. exact (eq_refl (term193 s a x)). Qed.
Lemma lem5230129 (s : real -> Prop) (a : real) : (term194 s a) = (term174 s a).
Proof. exact (fun_ext (fun x : real => @lem5230128 s x a)). Qed.
Lemma lem5230130 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5230131 (s : real -> Prop) (a : real) : (term195 s a) = (term175 s a).
Proof. exact (MK_COMB (@lem5230130) (@lem5230129 s a)). Qed.
Lemma lem5230132 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5230133 (s : real -> Prop) (a : real) : (term191 s a) = (term187 s a).
Proof. exact (MK_COMB (@lem5230132 s) (@lem5230131 s a)). Qed.
Lemma lem5230134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5230135 (s : real -> Prop) (a : real) : (term196 s a) = (term197 s a).
Proof. exact (MK_COMB (@lem5230134) (@lem5230133 s a)). Qed.
Lemma lem5230136 (s : real -> Prop) (x : real) (a : real) : (term193 s a x) = (term172 s x a).
Proof. exact (eq_refl (term193 s a x)). Qed.
Lemma lem5230137 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5230138 (s : real -> Prop) (x : real) (a : real) : (term198 s a x) = (term199 s x a).
Proof. exact (MK_COMB (@lem5230137 s) (@lem5230136 s x a)). Qed.
Lemma lem5230139 (s : real -> Prop) (a : real) : (term200 s a) = (term201 s a).
Proof. exact (fun_ext (fun x : real => @lem5230138 s x a)). Qed.
Lemma lem5230140 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5230141 (s : real -> Prop) (a : real) : (term192 s a) = (term202 s a).
Proof. exact (MK_COMB (@lem5230140) (@lem5230139 s a)). Qed.
Lemma lem5230142 (s : real -> Prop) (a : real) : ((term191 s a) = (term192 s a)) = ((term187 s a) = (term202 s a)).
Proof. exact (MK_COMB (@lem5230135 s a) (@lem5230141 s a)). Qed.
Lemma lem5230143 (s : real -> Prop) (a : real) : (term187 s a) = (term202 s a).
Proof. exact (EQ_MP (@lem5230142 s a) (@lem5230127 s a)). Qed.
Lemma lem5230144 (s : real -> Prop) : (term189 s) = (term203 s).
Proof. exact (fun_ext (fun a : real => @lem5230143 s a)). Qed.
Lemma lem5230145 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5230146 (s : real -> Prop) : (term190 s) = (term204 s).
Proof. exact (MK_COMB (@lem5230145) (@lem5230144 s)). Qed.
Lemma lem5230147 (s : real -> Prop) : (term178 s) = (term204 s).
Proof. exact (TRANS (@lem5230123 s) (@lem5230146 s)). Qed.
Lemma lem5230148 (s : real -> Prop) : (term130 s) = (term204 s).
Proof. exact (TRANS (@lem5230103 s) (@lem5230147 s)). Qed.
Lemma lem5230149 : term131 = term205.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5230148 s)). Qed.
Lemma lem5230150 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5230151 : term132 = term206.
Proof. exact (MK_COMB (@lem5230150) (@lem5230149)). Qed.
Lemma lem5230152 : term89 = term206.
Proof. exact (TRANS (@lem5229976) (@lem5230151)). Qed.
Lemma lem5230153 : term10 = term206.
Proof. exact (TRANS (@lem5229727) (@lem5230152)). Qed.
Lemma lem5230154 (h1 : term10) : term206.
Proof. exact (EQ_MP (@lem5230153) (@lem5229657 h1)). Qed.
Lemma lem5230161 (x : real) (y : real) (z : real) : (term207 x y z) = (term208 x y z).
Proof. exact (@lem17045 (real_le x y) (real_lt y z)). Qed.
Lemma lem5230162 (x : real) (z : real) : (real_lt x z) = (real_lt x z).
Proof. exact (eq_refl (real_lt x z)). Qed.
Lemma lem5230163 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5230164 (x : real) (y : real) (z : real) : (term209 x y z) = (term210 x y z).
Proof. exact (MK_COMB (@lem5230163) (@lem5230161 x y z)). Qed.
Lemma lem5230165 (y : real) (x : real) (z : real) : (term211 y x z) = (term212 y x z).
Proof. exact (MK_COMB (@lem5230164 x y z) (@lem5230162 x z)). Qed.
Lemma lem5230166 (y : real) (x : real) (z : real) : (term31 y x z) = (term211 y x z).
Proof. exact (@lem17265 (term213 x y z) (real_lt x z)). Qed.
Lemma lem5230167 (y : real) (x : real) (z : real) : (term31 y x z) = (term212 y x z).
Proof. exact (TRANS (@lem5230166 y x z) (@lem5230165 y x z)). Qed.
Lemma lem5230168 (y : real) (x : real) : (term32 y x) = (term214 y x).
Proof. exact (fun_ext (fun z : real => @lem5230167 y x z)). Qed.
Lemma lem5230169 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230170 (y : real) (x : real) : (term33 y x) = (term215 y x).
Proof. exact (MK_COMB (@lem5230169) (@lem5230168 y x)). Qed.
Lemma lem5230171 (x : real) : (term34 x) = (term216 x).
Proof. exact (fun_ext (fun y : real => @lem5230170 y x)). Qed.
Lemma lem5230172 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230173 (x : real) : (term35 x) = (term217 x).
Proof. exact (MK_COMB (@lem5230172) (@lem5230171 x)). Qed.
Lemma lem5230174 : term36 = term218.
Proof. exact (fun_ext (fun x : real => @lem5230173 x)). Qed.
Lemma lem5230175 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230236 : term37 = term219.
Proof. exact (MK_COMB (@lem5230175) (@lem5230174)). Qed.
Lemma lem5230237 (h1 : term37) : term219.
Proof. exact (EQ_MP (@lem5230236) (@lem5229658 h1)). Qed.
Lemma lem5230241 (s : real -> Prop) : (term220 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5230243 (s : real -> Prop) : (term221 s) = (term221 s).
Proof. exact (eq_refl (term221 s)). Qed.
Lemma lem5230244 (s : real -> Prop) : (term222 s) = (term223 s).
Proof. exact (MK_COMB (@lem5230243 s) (@lem5230241 s)). Qed.
Lemma lem5230245 (s : real -> Prop) : (term224 s) = (term222 s).
Proof. exact (@lem17045 (@FINITE real s) (term225 s)). Qed.
Lemma lem5230246 (s : real -> Prop) : (term224 s) = (term223 s).
Proof. exact (TRANS (@lem5230245 s) (@lem5230244 s)). Qed.
Lemma lem5230254 (s : real -> Prop) (x : real) : (term23 s x) = (term226 s x).
Proof. exact (@lem17265 (@IN real x s) (term227 s x)). Qed.
Lemma lem5230255 (s : real -> Prop) : (term24 s) = (term228 s).
Proof. exact (fun_ext (fun x : real => @lem5230254 s x)). Qed.
Lemma lem5230256 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230257 (s : real -> Prop) : (term25 s) = (term229 s).
Proof. exact (MK_COMB (@lem5230256) (@lem5230255 s)). Qed.
Lemma lem5230259 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5230260 (s : real -> Prop) : (term27 s) = (term230 s).
Proof. exact (MK_COMB (@lem5230259 s) (@lem5230257 s)). Qed.
Lemma lem5230261 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5230262 (s : real -> Prop) : (term231 s) = (term232 s).
Proof. exact (MK_COMB (@lem5230261) (@lem5230246 s)). Qed.
Lemma lem5230263 (s : real -> Prop) : (term233 s) = (term234 s).
Proof. exact (MK_COMB (@lem5230262 s) (@lem5230260 s)). Qed.
Lemma lem5230264 (s : real -> Prop) : (term29 s) = (term233 s).
Proof. exact (@lem17265 (term72 s) (term27 s)). Qed.
Lemma lem5230265 (s : real -> Prop) : (term29 s) = (term234 s).
Proof. exact (TRANS (@lem5230264 s) (@lem5230263 s)). Qed.
Lemma lem5230266 : term30 = term235.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5230265 s)). Qed.
Lemma lem5230267 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5230368 : term17 = term236.
Proof. exact (MK_COMB (@lem5230267) (@lem5230266)). Qed.
Lemma lem5230369 (h1 : term17) : term236.
Proof. exact (EQ_MP (@lem5230368) (@lem5229659 h1)). Qed.
Lemma lem5230370 (s : real -> Prop) (h1 : term204 s) : term204 s.
Proof. exact (h1). Qed.
Lemma lem5230371 (s : real -> Prop) (a : real) (h1 : term202 s a) : term202 s a.
Proof. exact (h1). Qed.
Lemma lem5230372 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term199 s x a.
Proof. exact (h1). Qed.
Lemma lem5230397 (y : real) (x : real) (z : real) : (term212 y x z) = (term212 y x z).
Proof. exact (eq_refl (term212 y x z)). Qed.
Lemma lem5230398 (y : real) (x : real) : (term214 y x) = (term214 y x).
Proof. exact (fun_ext (fun z : real => @lem5230397 y x z)). Qed.
Lemma lem5230399 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230400 (y : real) (x : real) : (term215 y x) = (term215 y x).
Proof. exact (MK_COMB (@lem5230399) (@lem5230398 y x)). Qed.
Lemma lem5230401 (x : real) : (term216 x) = (term216 x).
Proof. exact (fun_ext (fun y : real => @lem5230400 y x)). Qed.
Lemma lem5230402 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230403 (x : real) : (term217 x) = (term217 x).
Proof. exact (MK_COMB (@lem5230402) (@lem5230401 x)). Qed.
Lemma lem5230404 : term218 = term218.
Proof. exact (fun_ext (fun x : real => @lem5230403 x)). Qed.
Lemma lem5230405 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230406 : term219 = term219.
Proof. exact (MK_COMB (@lem5230405) (@lem5230404)). Qed.
Lemma lem5230407 (h1 : term37) : term219.
Proof. exact (EQ_MP (@lem5230406) (@lem5230237 h1)). Qed.
Lemma lem5230424 (s : real -> Prop) (x : real) : (term226 s x) = (term226 s x).
Proof. exact (eq_refl (term226 s x)). Qed.
Lemma lem5230425 (s : real -> Prop) : (term228 s) = (term228 s).
Proof. exact (fun_ext (fun x : real => @lem5230424 s x)). Qed.
Lemma lem5230426 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230427 (s : real -> Prop) : (term229 s) = (term229 s).
Proof. exact (MK_COMB (@lem5230426) (@lem5230425 s)). Qed.
Lemma lem5230436 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5230437 (s : real -> Prop) : (term230 s) = (term230 s).
Proof. exact (MK_COMB (@lem5230436 s) (@lem5230427 s)). Qed.
Lemma lem5230452 (s : real -> Prop) : (term232 s) = (term232 s).
Proof. exact (eq_refl (term232 s)). Qed.
Lemma lem5230453 (s : real -> Prop) : (term234 s) = (term234 s).
Proof. exact (MK_COMB (@lem5230452 s) (@lem5230437 s)). Qed.
Lemma lem5230454 : term235 = term235.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5230453 s)). Qed.
Lemma lem5230455 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5230456 : term236 = term236.
Proof. exact (MK_COMB (@lem5230455) (@lem5230454)). Qed.
Lemma lem5230457 (h1 : term17) : term236.
Proof. exact (EQ_MP (@lem5230456) (@lem5230369 h1)). Qed.
Lemma lem5230482 (s : real -> Prop) (x : real) (a : real) : (term141 s x a) = (term141 s x a).
Proof. exact (eq_refl (term141 s x a)). Qed.
Lemma lem5230499 (s : real -> Prop) (x : real) (a : real) : (term48 s x a) = (term48 s x a).
Proof. exact (eq_refl (term48 s x a)). Qed.
Lemma lem5230500 (s : real -> Prop) (a : real) : (term56 s a) = (term56 s a).
Proof. exact (fun_ext (fun x : real => @lem5230499 s x a)). Qed.
Lemma lem5230501 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230502 (s : real -> Prop) (a : real) : (term57 s a) = (term57 s a).
Proof. exact (MK_COMB (@lem5230501) (@lem5230500 s a)). Qed.
Lemma lem5230511 (s : real -> Prop) (a : real) : (term60 s a) = (term60 s a).
Proof. exact (eq_refl (term60 s a)). Qed.
Lemma lem5230512 (s : real -> Prop) (a : real) : (term62 s a) = (term62 s a).
Proof. exact (MK_COMB (@lem5230511 s a) (@lem5230502 s a)). Qed.
Lemma lem5230513 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5230514 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (MK_COMB (@lem5230513) (@lem5230512 s a)). Qed.
Lemma lem5230515 (s : real -> Prop) (x : real) (a : real) : (term172 s x a) = (term172 s x a).
Proof. exact (MK_COMB (@lem5230514 s a) (@lem5230482 s x a)). Qed.
Lemma lem5230530 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (eq_refl (term68 s)). Qed.
Lemma lem5230531 (s : real -> Prop) (x : real) (a : real) : (term199 s x a) = (term199 s x a).
Proof. exact (MK_COMB (@lem5230530 s) (@lem5230515 s x a)). Qed.
Lemma lem5230532 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term199 s x a.
Proof. exact (EQ_MP (@lem5230531 s x a) (@lem5230372 s x a h1)). Qed.
Lemma lem5230533 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term172 s x a.
Proof. exact (proj2 (@lem5230532 s x a h1)). Qed.
Lemma lem5230534 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term72 s.
Proof. exact (proj1 (@lem5230532 s x a h1)). Qed.
Lemma lem5230537 (s : real -> Prop) (a : real) (h1 : term62 s a) : term62 s a.
Proof. exact (h1). Qed.
Lemma lem5230538 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : term141 s x a.
Proof. exact (h1). Qed.
Lemma lem5230539 (s : real -> Prop) (a : real) (h1 : term62 s a) : term57 s a.
Proof. exact (proj2 (@lem5230537 s a h1)). Qed.
Lemma lem5230541 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : term38 s x a.
Proof. exact (proj2 (@lem5230538 s x a h1)). Qed.
Lemma lem5230571 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5230572 (P : Prop) (Q : real -> Prop) : (term239 P Q) = (term240 P Q).
Proof. exact (@lem5230571 real P Q). Qed.
Lemma lem5230573 (s : real -> Prop) : (term241 s) = (term242 s).
Proof. exact (@lem5230572 (term243 s) (term228 s)). Qed.
Lemma lem5230574 (s : real -> Prop) (x : real) : (term244 s x) = (term226 s x).
Proof. exact (eq_refl (term244 s x)). Qed.
Lemma lem5230575 (s : real -> Prop) : (term245 s) = (term228 s).
Proof. exact (fun_ext (fun x : real => @lem5230574 s x)). Qed.
Lemma lem5230576 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230577 (s : real -> Prop) : (term246 s) = (term229 s).
Proof. exact (MK_COMB (@lem5230576) (@lem5230575 s)). Qed.
Lemma lem5230578 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5230579 (s : real -> Prop) : (term241 s) = (term230 s).
Proof. exact (MK_COMB (@lem5230578 s) (@lem5230577 s)). Qed.
Lemma lem5230580 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5230581 (s : real -> Prop) : (term247 s) = (term248 s).
Proof. exact (MK_COMB (@lem5230580) (@lem5230579 s)). Qed.
Lemma lem5230582 (s : real -> Prop) (x : real) : (term244 s x) = (term226 s x).
Proof. exact (eq_refl (term244 s x)). Qed.
Lemma lem5230583 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5230584 (s : real -> Prop) (x : real) : (term249 s x) = (term250 s x).
Proof. exact (MK_COMB (@lem5230583 s) (@lem5230582 s x)). Qed.
Lemma lem5230585 (s : real -> Prop) : (term251 s) = (term252 s).
Proof. exact (fun_ext (fun x : real => @lem5230584 s x)). Qed.
Lemma lem5230586 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230587 (s : real -> Prop) : (term242 s) = (term253 s).
Proof. exact (MK_COMB (@lem5230586) (@lem5230585 s)). Qed.
Lemma lem5230588 (s : real -> Prop) : ((term241 s) = (term242 s)) = ((term230 s) = (term253 s)).
Proof. exact (MK_COMB (@lem5230581 s) (@lem5230587 s)). Qed.
Lemma lem5230589 (s : real -> Prop) : (term230 s) = (term253 s).
Proof. exact (EQ_MP (@lem5230588 s) (@lem5230573 s)). Qed.
Lemma lem5230590 (s : real -> Prop) : (term232 s) = (term232 s).
Proof. exact (eq_refl (term232 s)). Qed.
Lemma lem5230591 (s : real -> Prop) : (term234 s) = (term254 s).
Proof. exact (MK_COMB (@lem5230590 s) (@lem5230589 s)). Qed.
Lemma lem5230593 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5230594 (P : Prop) (Q : real -> Prop) : (term257 P Q) = (term258 P Q).
Proof. exact (@lem5230593 real P Q). Qed.
Lemma lem5230595 (s : real -> Prop) : (term259 s) = (term260 s).
Proof. exact (@lem5230594 (term223 s) (term252 s)). Qed.
Lemma lem5230596 (s : real -> Prop) (x : real) : (term261 s x) = (term250 s x).
Proof. exact (eq_refl (term261 s x)). Qed.
Lemma lem5230597 (s : real -> Prop) : (term262 s) = (term252 s).
Proof. exact (fun_ext (fun x : real => @lem5230596 s x)). Qed.
Lemma lem5230598 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230599 (s : real -> Prop) : (term263 s) = (term253 s).
Proof. exact (MK_COMB (@lem5230598) (@lem5230597 s)). Qed.
Lemma lem5230600 (s : real -> Prop) : (term232 s) = (term232 s).
Proof. exact (eq_refl (term232 s)). Qed.
Lemma lem5230601 (s : real -> Prop) : (term259 s) = (term254 s).
Proof. exact (MK_COMB (@lem5230600 s) (@lem5230599 s)). Qed.
Lemma lem5230602 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5230603 (s : real -> Prop) : (term264 s) = (term265 s).
Proof. exact (MK_COMB (@lem5230602) (@lem5230601 s)). Qed.
Lemma lem5230604 (s : real -> Prop) (x : real) : (term261 s x) = (term250 s x).
Proof. exact (eq_refl (term261 s x)). Qed.
Lemma lem5230605 (s : real -> Prop) : (term232 s) = (term232 s).
Proof. exact (eq_refl (term232 s)). Qed.
Lemma lem5230606 (s : real -> Prop) (x : real) : (term266 s x) = (term267 s x).
Proof. exact (MK_COMB (@lem5230605 s) (@lem5230604 s x)). Qed.
Lemma lem5230607 (s : real -> Prop) : (term268 s) = (term269 s).
Proof. exact (fun_ext (fun x : real => @lem5230606 s x)). Qed.
Lemma lem5230608 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230609 (s : real -> Prop) : (term260 s) = (term270 s).
Proof. exact (MK_COMB (@lem5230608) (@lem5230607 s)). Qed.
Lemma lem5230610 (s : real -> Prop) : ((term259 s) = (term260 s)) = ((term254 s) = (term270 s)).
Proof. exact (MK_COMB (@lem5230603 s) (@lem5230609 s)). Qed.
Lemma lem5230611 (s : real -> Prop) : (term254 s) = (term270 s).
Proof. exact (EQ_MP (@lem5230610 s) (@lem5230595 s)). Qed.
Lemma lem5230612 (s : real -> Prop) : (term234 s) = (term270 s).
Proof. exact (TRANS (@lem5230591 s) (@lem5230611 s)). Qed.
Lemma lem5230613 : term235 = term271.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5230612 s)). Qed.
Lemma lem5230614 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5230615 : term236 = term272.
Proof. exact (MK_COMB (@lem5230614) (@lem5230613)). Qed.
Lemma lem5230644 (s : real -> Prop) (x : real) : (term267 s x) = (term273 s x).
Proof. exact (@lem19490 (term243 s) (term223 s) (term226 s x)). Qed.
Lemma lem5230645 (s : real -> Prop) : (term269 s) = (term274 s).
Proof. exact (fun_ext (fun x : real => @lem5230644 s x)). Qed.
Lemma lem5230646 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230647 (s : real -> Prop) : (term270 s) = (term275 s).
Proof. exact (MK_COMB (@lem5230646) (@lem5230645 s)). Qed.
Lemma lem5230648 : term271 = term276.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5230647 s)). Qed.
Lemma lem5230649 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5230650 : term272 = term277.
Proof. exact (MK_COMB (@lem5230649) (@lem5230648)). Qed.
Lemma lem5230651 : term236 = term277.
Proof. exact (TRANS (@lem5230615) (@lem5230650)). Qed.
Lemma lem5230652 (h1 : term17) : term277.
Proof. exact (EQ_MP (@lem5230651) (@lem5230457 h1)). Qed.
Lemma lem5230672 (s : real -> Prop) (x : real) (a : real) : (term48 s x a) = (term48 s x a).
Proof. exact (eq_refl (term48 s x a)). Qed.
Lemma lem5230673 (s : real -> Prop) (a : real) : (term56 s a) = (term56 s a).
Proof. exact (fun_ext (fun x : real => @lem5230672 s x a)). Qed.
Lemma lem5230674 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230676 (s : real -> Prop) (a : real) : (term57 s a) = (term57 s a).
Proof. exact (MK_COMB (@lem5230674) (@lem5230673 s a)). Qed.
Lemma lem5230677 (s : real -> Prop) (a : real) (h1 : term62 s a) : term57 s a.
Proof. exact (EQ_MP (@lem5230676 s a) (@lem5230539 s a h1)). Qed.
Lemma lem5230691 (y : real) (x : real) (z : real) : (term212 y x z) = (term212 y x z).
Proof. exact (eq_refl (term212 y x z)). Qed.
Lemma lem5230692 (y : real) (x : real) : (term214 y x) = (term214 y x).
Proof. exact (fun_ext (fun z : real => @lem5230691 y x z)). Qed.
Lemma lem5230693 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230694 (y : real) (x : real) : (term215 y x) = (term215 y x).
Proof. exact (MK_COMB (@lem5230693) (@lem5230692 y x)). Qed.
Lemma lem5230695 (x : real) : (term216 x) = (term216 x).
Proof. exact (fun_ext (fun y : real => @lem5230694 y x)). Qed.
Lemma lem5230696 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230697 (x : real) : (term217 x) = (term217 x).
Proof. exact (MK_COMB (@lem5230696) (@lem5230695 x)). Qed.
Lemma lem5230698 : term218 = term218.
Proof. exact (fun_ext (fun x : real => @lem5230697 x)). Qed.
Lemma lem5230699 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230701 : term219 = term219.
Proof. exact (MK_COMB (@lem5230699) (@lem5230698)). Qed.
Lemma lem5230702 (h1 : term37) : term219.
Proof. exact (EQ_MP (@lem5230701) (@lem5230407 h1)). Qed.
Lemma lem5230704 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5230705 (P : Prop) (Q : real -> Prop) : (term239 P Q) = (term240 P Q).
Proof. exact (@lem5230704 real P Q). Qed.
Lemma lem5230706 (s : real -> Prop) : (term241 s) = (term242 s).
Proof. exact (@lem5230705 (term243 s) (term228 s)). Qed.
Lemma lem5230707 (s : real -> Prop) (x : real) : (term244 s x) = (term226 s x).
Proof. exact (eq_refl (term244 s x)). Qed.
Lemma lem5230708 (s : real -> Prop) : (term245 s) = (term228 s).
Proof. exact (fun_ext (fun x : real => @lem5230707 s x)). Qed.
Lemma lem5230709 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230710 (s : real -> Prop) : (term246 s) = (term229 s).
Proof. exact (MK_COMB (@lem5230709) (@lem5230708 s)). Qed.
Lemma lem5230711 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5230712 (s : real -> Prop) : (term241 s) = (term230 s).
Proof. exact (MK_COMB (@lem5230711 s) (@lem5230710 s)). Qed.
Lemma lem5230713 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5230714 (s : real -> Prop) : (term247 s) = (term248 s).
Proof. exact (MK_COMB (@lem5230713) (@lem5230712 s)). Qed.
Lemma lem5230715 (s : real -> Prop) (x : real) : (term244 s x) = (term226 s x).
Proof. exact (eq_refl (term244 s x)). Qed.
Lemma lem5230716 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5230717 (s : real -> Prop) (x : real) : (term249 s x) = (term250 s x).
Proof. exact (MK_COMB (@lem5230716 s) (@lem5230715 s x)). Qed.
Lemma lem5230718 (s : real -> Prop) : (term251 s) = (term252 s).
Proof. exact (fun_ext (fun x : real => @lem5230717 s x)). Qed.
Lemma lem5230719 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230720 (s : real -> Prop) : (term242 s) = (term253 s).
Proof. exact (MK_COMB (@lem5230719) (@lem5230718 s)). Qed.
Lemma lem5230721 (s : real -> Prop) : ((term241 s) = (term242 s)) = ((term230 s) = (term253 s)).
Proof. exact (MK_COMB (@lem5230714 s) (@lem5230720 s)). Qed.
Lemma lem5230722 (s : real -> Prop) : (term230 s) = (term253 s).
Proof. exact (EQ_MP (@lem5230721 s) (@lem5230706 s)). Qed.
Lemma lem5230723 (s : real -> Prop) : (term232 s) = (term232 s).
Proof. exact (eq_refl (term232 s)). Qed.
Lemma lem5230724 (s : real -> Prop) : (term234 s) = (term254 s).
Proof. exact (MK_COMB (@lem5230723 s) (@lem5230722 s)). Qed.
Lemma lem5230726 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5230727 (P : Prop) (Q : real -> Prop) : (term257 P Q) = (term258 P Q).
Proof. exact (@lem5230726 real P Q). Qed.
Lemma lem5230728 (s : real -> Prop) : (term259 s) = (term260 s).
Proof. exact (@lem5230727 (term223 s) (term252 s)). Qed.
Lemma lem5230729 (s : real -> Prop) (x : real) : (term261 s x) = (term250 s x).
Proof. exact (eq_refl (term261 s x)). Qed.
Lemma lem5230730 (s : real -> Prop) : (term262 s) = (term252 s).
Proof. exact (fun_ext (fun x : real => @lem5230729 s x)). Qed.
Lemma lem5230731 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230732 (s : real -> Prop) : (term263 s) = (term253 s).
Proof. exact (MK_COMB (@lem5230731) (@lem5230730 s)). Qed.
Lemma lem5230733 (s : real -> Prop) : (term232 s) = (term232 s).
Proof. exact (eq_refl (term232 s)). Qed.
Lemma lem5230734 (s : real -> Prop) : (term259 s) = (term254 s).
Proof. exact (MK_COMB (@lem5230733 s) (@lem5230732 s)). Qed.
Lemma lem5230735 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5230736 (s : real -> Prop) : (term264 s) = (term265 s).
Proof. exact (MK_COMB (@lem5230735) (@lem5230734 s)). Qed.
Lemma lem5230737 (s : real -> Prop) (x : real) : (term261 s x) = (term250 s x).
Proof. exact (eq_refl (term261 s x)). Qed.
Lemma lem5230738 (s : real -> Prop) : (term232 s) = (term232 s).
Proof. exact (eq_refl (term232 s)). Qed.
Lemma lem5230739 (s : real -> Prop) (x : real) : (term266 s x) = (term267 s x).
Proof. exact (MK_COMB (@lem5230738 s) (@lem5230737 s x)). Qed.
Lemma lem5230740 (s : real -> Prop) : (term268 s) = (term269 s).
Proof. exact (fun_ext (fun x : real => @lem5230739 s x)). Qed.
Lemma lem5230741 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230742 (s : real -> Prop) : (term260 s) = (term270 s).
Proof. exact (MK_COMB (@lem5230741) (@lem5230740 s)). Qed.
Lemma lem5230743 (s : real -> Prop) : ((term259 s) = (term260 s)) = ((term254 s) = (term270 s)).
Proof. exact (MK_COMB (@lem5230736 s) (@lem5230742 s)). Qed.
Lemma lem5230744 (s : real -> Prop) : (term254 s) = (term270 s).
Proof. exact (EQ_MP (@lem5230743 s) (@lem5230728 s)). Qed.
Lemma lem5230745 (s : real -> Prop) : (term234 s) = (term270 s).
Proof. exact (TRANS (@lem5230724 s) (@lem5230744 s)). Qed.
Lemma lem5230746 : term235 = term271.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5230745 s)). Qed.
Lemma lem5230747 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5230748 : term236 = term272.
Proof. exact (MK_COMB (@lem5230747) (@lem5230746)). Qed.
Lemma lem5230777 (s : real -> Prop) (x : real) : (term267 s x) = (term273 s x).
Proof. exact (@lem19490 (term243 s) (term223 s) (term226 s x)). Qed.
Lemma lem5230778 (s : real -> Prop) : (term269 s) = (term274 s).
Proof. exact (fun_ext (fun x : real => @lem5230777 s x)). Qed.
Lemma lem5230779 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5230780 (s : real -> Prop) : (term270 s) = (term275 s).
Proof. exact (MK_COMB (@lem5230779) (@lem5230778 s)). Qed.
Lemma lem5230781 : term271 = term276.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5230780 s)). Qed.
Lemma lem5230782 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5230783 : term272 = term277.
Proof. exact (MK_COMB (@lem5230782) (@lem5230781)). Qed.
Lemma lem5230784 : term236 = term277.
Proof. exact (TRANS (@lem5230748) (@lem5230783)). Qed.
Lemma lem5230785 (h1 : term17) : term277.
Proof. exact (EQ_MP (@lem5230784) (@lem5230457 h1)). Qed.
Lemma lem5230815 (_68478 : real -> Prop) (h1 : term17) : term278 _68478.
Proof. exact (@lem5230652 h1 _68478). Qed.
Lemma lem5230816 (_68478 : real -> Prop) : (term278 _68478) = (term275 _68478).
Proof. exact (eq_refl (term278 _68478)). Qed.
Lemma lem5230817 (_68478 : real -> Prop) (h1 : term17) : term275 _68478.
Proof. exact (EQ_MP (@lem5230816 _68478) (@lem5230815 _68478 h1)). Qed.
Lemma lem5230818 (_68478 : real -> Prop) (_68479 : real) (h1 : term17) : term279 _68478 _68479.
Proof. exact (@lem5230817 _68478 h1 _68479). Qed.
Lemma lem5230819 (_68478 : real -> Prop) (_68479 : real) : (term279 _68478 _68479) = (term273 _68478 _68479).
Proof. exact (eq_refl (term279 _68478 _68479)). Qed.
Lemma lem5230820 (_68478 : real -> Prop) (_68479 : real) (h1 : term17) : term273 _68478 _68479.
Proof. exact (EQ_MP (@lem5230819 _68478 _68479) (@lem5230818 _68478 _68479 h1)). Qed.
Lemma lem5230821 (_68480 : real) (s : real -> Prop) (a : real) (h1 : term62 s a) : term280 s a _68480.
Proof. exact (@lem5230677 s a h1 _68480). Qed.
Lemma lem5230822 (s : real -> Prop) (_68480 : real) (a : real) : (term280 s a _68480) = (term48 s _68480 a).
Proof. exact (eq_refl (term280 s a _68480)). Qed.
Lemma lem5230824 (_68481 : real) (h1 : term37) : term281 _68481.
Proof. exact (@lem5230702 h1 _68481). Qed.
Lemma lem5230825 (_68481 : real) : (term281 _68481) = (term217 _68481).
Proof. exact (eq_refl (term281 _68481)). Qed.
Lemma lem5230826 (_68481 : real) (h1 : term37) : term217 _68481.
Proof. exact (EQ_MP (@lem5230825 _68481) (@lem5230824 _68481 h1)). Qed.
Lemma lem5230827 (_68481 : real) (_68482 : real) (h1 : term37) : term282 _68481 _68482.
Proof. exact (@lem5230826 _68481 h1 _68482). Qed.
Lemma lem5230828 (_68482 : real) (_68481 : real) : (term282 _68481 _68482) = (term215 _68482 _68481).
Proof. exact (eq_refl (term282 _68481 _68482)). Qed.
Lemma lem5230829 (_68482 : real) (_68481 : real) (h1 : term37) : term215 _68482 _68481.
Proof. exact (EQ_MP (@lem5230828 _68482 _68481) (@lem5230827 _68481 _68482 h1)). Qed.
Lemma lem5230830 (_68482 : real) (_68481 : real) (_68483 : real) (h1 : term37) : term283 _68482 _68481 _68483.
Proof. exact (@lem5230829 _68482 _68481 h1 _68483). Qed.
Lemma lem5230831 (_68482 : real) (_68481 : real) (_68483 : real) : (term283 _68482 _68481 _68483) = (term212 _68482 _68481 _68483).
Proof. exact (eq_refl (term283 _68482 _68481 _68483)). Qed.
Lemma lem5230832 (_68482 : real) (_68481 : real) (_68483 : real) (h1 : term37) : term212 _68482 _68481 _68483.
Proof. exact (EQ_MP (@lem5230831 _68482 _68481 _68483) (@lem5230830 _68482 _68481 _68483 h1)). Qed.
Lemma lem5230833 (_68484 : real -> Prop) (h1 : term17) : term278 _68484.
Proof. exact (@lem5230785 h1 _68484). Qed.
Lemma lem5230834 (_68484 : real -> Prop) : (term278 _68484) = (term275 _68484).
Proof. exact (eq_refl (term278 _68484)). Qed.
Lemma lem5230835 (_68484 : real -> Prop) (h1 : term17) : term275 _68484.
Proof. exact (EQ_MP (@lem5230834 _68484) (@lem5230833 _68484 h1)). Qed.
Lemma lem5230836 (_68484 : real -> Prop) (_68485 : real) (h1 : term17) : term279 _68484 _68485.
Proof. exact (@lem5230835 _68484 h1 _68485). Qed.
Lemma lem5230837 (_68484 : real -> Prop) (_68485 : real) : (term279 _68484 _68485) = (term273 _68484 _68485).
Proof. exact (eq_refl (term279 _68484 _68485)). Qed.
Lemma lem5230838 (_68484 : real -> Prop) (_68485 : real) (h1 : term17) : term273 _68484 _68485.
Proof. exact (EQ_MP (@lem5230837 _68484 _68485) (@lem5230836 _68484 _68485 h1)). Qed.
Lemma lem5230840 (_68478 : real -> Prop) (h1 : term17) : term284 _68478.
Proof. exact (proj1 (@lem5230820 _68478 (@el real) h1)). Qed.
Lemma lem5230841 (_68484 : real -> Prop) (_68485 : real) (h1 : term17) : term285 _68484 _68485.
Proof. exact (proj2 (@lem5230838 _68484 _68485 h1)). Qed.
Lemma lem5230858 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term225 s.
Proof. exact (proj2 (@lem5230534 s x a h1)). Qed.
Lemma lem5230866 (_68480 : real) (s : real -> Prop) (a : real) (h1 : term62 s a) : term48 s _68480 a.
Proof. exact (EQ_MP (@lem5230822 s _68480 a) (@lem5230821 _68480 s a h1)). Qed.
Lemma lem5230877 (_68478 : real -> Prop) : (term284 _68478) = (term286 _68478).
Proof. exact (@lem5229368 (term287 _68478) (_68478 = (@EMPTY real)) (term243 _68478)). Qed.
Lemma lem5230878 (_68478 : real -> Prop) (h1 : term17) : term286 _68478.
Proof. exact (EQ_MP (@lem5230877 _68478) (@lem5230840 _68478 h1)). Qed.
Lemma lem5230905 (_68482 : real) (_68481 : real) (_68483 : real) : (term212 _68482 _68481 _68483) = (term288 _68482 _68481 _68483).
Proof. exact (@lem5229368 (term289 _68481 _68482) (term290 _68482 _68483) (real_lt _68481 _68483)). Qed.
Lemma lem5230906 (_68482 : real) (_68481 : real) (_68483 : real) (h1 : term37) : term288 _68482 _68481 _68483.
Proof. exact (EQ_MP (@lem5230905 _68482 _68481 _68483) (@lem5230832 _68482 _68481 _68483 h1)). Qed.
Lemma lem5230912 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : term135 s a.
Proof. exact (proj1 (@lem5230538 s x a h1)). Qed.
Lemma lem5230943 (_68484 : real -> Prop) (_68485 : real) : (term285 _68484 _68485) = (term291 _68484 _68485).
Proof. exact (@lem5229368 (term287 _68484) (_68484 = (@EMPTY real)) (term226 _68484 _68485)). Qed.
Lemma lem5230944 (_68484 : real -> Prop) (_68485 : real) (h1 : term17) : term291 _68484 _68485.
Proof. exact (EQ_MP (@lem5230943 _68484 _68485) (@lem5230841 _68484 _68485 h1)). Qed.
Lemma lem5231027 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : @FINITE real s.
Proof. exact (proj1 (@lem5230534 s x a h1)). Qed.
Lemma lem5231028 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term292 s.
Proof. exact (fun h0 : term287 s => @lem5231027 s x a h1). Qed.
Lemma lem5231030 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5231031 (s : real -> Prop) : (term292 s) = (@FINITE real s).
Proof. exact (@lem5231030 (@FINITE real s)). Qed.
Lemma lem5231032 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : @FINITE real s.
Proof. exact (EQ_MP (@lem5231031 s) (@lem5231028 s x a h1)). Qed.
Lemma lem5231034 (s : real -> Prop) (a : real) (h1 : term62 s a) : term42 s a.
Proof. exact (proj1 (@lem5230537 s a h1)). Qed.
Lemma lem5231035 (s : real -> Prop) (a : real) (h1 : term62 s a) : term294 s a.
Proof. exact (fun h0 : term135 s a => @lem5231034 s a h1). Qed.
Lemma lem5231037 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5231038 (s : real -> Prop) (a : real) : (term294 s a) = (term42 s a).
Proof. exact (@lem5231037 (term42 s a)). Qed.
Lemma lem5231039 (s : real -> Prop) (a : real) (h1 : term62 s a) : term42 s a.
Proof. exact (EQ_MP (@lem5231038 s a) (@lem5231035 s a h1)). Qed.
Lemma lem5231041 (b : Prop) (a : Prop) : (a \/ b) = (term295 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5231042 (a : real) (_68480 : real) (s : real -> Prop) : (term48 s _68480 a) = (term296 a _68480 s).
Proof. exact (@lem5231041 (term290 _68480 a) (term297 _68480 s)). Qed.
Lemma lem5231044 (a : Prop) : (term298 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5231045 (_68480 : real) (a : real) : (term299 _68480 a) = (real_lt _68480 a).
Proof. exact (@lem5231044 (real_lt _68480 a)). Qed.
Lemma lem5231046 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5231047 (_68480 : real) (a : real) : (term300 _68480 a) = (term301 _68480 a).
Proof. exact (MK_COMB (@lem5231046) (@lem5231045 _68480 a)). Qed.
Lemma lem5231048 (_68480 : real) (s : real -> Prop) : (term297 _68480 s) = (term297 _68480 s).
Proof. exact (eq_refl (term297 _68480 s)). Qed.
Lemma lem5231049 (a : real) (_68480 : real) (s : real -> Prop) : (term296 a _68480 s) = (term302 a _68480 s).
Proof. exact (MK_COMB (@lem5231047 _68480 a) (@lem5231048 _68480 s)). Qed.
Lemma lem5231050 (a : real) (_68480 : real) (s : real -> Prop) : (term48 s _68480 a) = (term302 a _68480 s).
Proof. exact (TRANS (@lem5231042 a _68480 s) (@lem5231049 a _68480 s)). Qed.
Lemma lem5231053 (_68480 : real) (s : real -> Prop) (a : real) (h1 : term62 s a) : term302 a _68480 s.
Proof. exact (EQ_MP (@lem5231050 a _68480 s) (@lem5230866 _68480 s a h1)). Qed.
Lemma lem5231054 (s : real -> Prop) (a : real) (h1 : term62 s a) : term303 a s.
Proof. exact (@lem5231053 (inf s) s a h1). Qed.
Lemma lem5231057 (s : real -> Prop) (a : real) (h1 : term62 s a) : term304 s.
Proof. exact (@lem5231054 s a h1 (@lem5231039 s a h1)). Qed.
Lemma lem5231058 (s : real -> Prop) (a : real) (h1 : term62 s a) : term305 s.
Proof. exact (fun h0 : term243 s => @lem5231057 s a h1). Qed.
Lemma lem5231060 (p : Prop) : (term306 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5231061 (s : real -> Prop) : (term305 s) = (term304 s).
Proof. exact (@lem5231060 (term243 s)). Qed.
Lemma lem5231062 (s : real -> Prop) (a : real) (h1 : term62 s a) : term304 s.
Proof. exact (EQ_MP (@lem5231061 s) (@lem5231058 s a h1)). Qed.
Lemma lem5231068 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5231069 (_68478 : real -> Prop) : (term286 _68478) = (term307 _68478).
Proof. exact (@lem5231068 (_68478 = (@EMPTY real)) (term287 _68478) (term243 _68478)). Qed.
Lemma lem5231085 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5231086 (_68478 : real -> Prop) : (term308 _68478) = (term309 _68478).
Proof. exact (@lem5231085 (term243 _68478) (term287 _68478)). Qed.
Lemma lem5231092 (_68478 : real -> Prop) : (term310 _68478) = (term310 _68478).
Proof. exact (eq_refl (term310 _68478)). Qed.
Lemma lem5231093 (_68478 : real -> Prop) : (term307 _68478) = (term311 _68478).
Proof. exact (MK_COMB (@lem5231092 _68478) (@lem5231086 _68478)). Qed.
Lemma lem5231104 (_68478 : real -> Prop) : (term286 _68478) = (term311 _68478).
Proof. exact (TRANS (@lem5231069 _68478) (@lem5231093 _68478)). Qed.
Lemma lem5231105 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5231106 (_68478 : real -> Prop) : (term312 _68478) = (term313 _68478).
Proof. exact (MK_COMB (@lem5231105) (@lem5231104 _68478)). Qed.
Lemma lem5231122 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5231123 (_68478 : real -> Prop) : (term308 _68478) = (term309 _68478).
Proof. exact (@lem5231122 (term243 _68478) (term287 _68478)). Qed.
Lemma lem5231129 (_68478 : real -> Prop) : (term310 _68478) = (term310 _68478).
Proof. exact (eq_refl (term310 _68478)). Qed.
Lemma lem5231130 (_68478 : real -> Prop) : (term307 _68478) = (term311 _68478).
Proof. exact (MK_COMB (@lem5231129 _68478) (@lem5231123 _68478)). Qed.
Lemma lem5231141 (_68478 : real -> Prop) : ((term286 _68478) = (term307 _68478)) = ((term311 _68478) = (term311 _68478)).
Proof. exact (MK_COMB (@lem5231106 _68478) (@lem5231130 _68478)). Qed.
Lemma lem5231143 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5231144 (x : Prop) : (x = x) = True.
Proof. exact (@lem5231143 Prop x). Qed.
Lemma lem5231145 (_68478 : real -> Prop) : ((term311 _68478) = (term311 _68478)) = True.
Proof. exact (@lem5231144 (term311 _68478)). Qed.
Lemma lem5231146 (_68478 : real -> Prop) : ((term286 _68478) = (term307 _68478)) = True.
Proof. exact (TRANS (@lem5231141 _68478) (@lem5231145 _68478)). Qed.
Lemma lem5231147 (_68478 : real -> Prop) : True = ((term286 _68478) = (term307 _68478)).
Proof. exact (SYM (@lem5231146 _68478)). Qed.
Lemma lem5231148 (_68478 : real -> Prop) : (term286 _68478) = (term307 _68478).
Proof. exact (EQ_MP (@lem5231147 _68478) (@lem0)). Qed.
Lemma lem5231149 (_68478 : real -> Prop) (h1 : term17) : term307 _68478.
Proof. exact (EQ_MP (@lem5231148 _68478) (@lem5230878 _68478 h1)). Qed.
Lemma lem5231151 (b : Prop) (a : Prop) : (a \/ b) = (term295 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5231152 (_68478 : real -> Prop) : (term307 _68478) = (term314 _68478).
Proof. exact (@lem5231151 (term308 _68478) (_68478 = (@EMPTY real))). Qed.
Lemma lem5231154 (a : Prop) (b : Prop) : (term315 a b) = (term316 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5231155 (_68478 : real -> Prop) : (term317 _68478) = (term318 _68478).
Proof. exact (@lem5231154 (term287 _68478) (term243 _68478)). Qed.
Lemma lem5231157 (a : Prop) : (term298 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5231158 (_68478 : real -> Prop) : (term319 _68478) = (@FINITE real _68478).
Proof. exact (@lem5231157 (@FINITE real _68478)). Qed.
Lemma lem5231159 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5231160 (_68478 : real -> Prop) : (term320 _68478) = (term321 _68478).
Proof. exact (MK_COMB (@lem5231159) (@lem5231158 _68478)). Qed.
Lemma lem5231161 (_68478 : real -> Prop) : (term304 _68478) = (term304 _68478).
Proof. exact (eq_refl (term304 _68478)). Qed.
Lemma lem5231162 (_68478 : real -> Prop) : (term318 _68478) = (term322 _68478).
Proof. exact (MK_COMB (@lem5231160 _68478) (@lem5231161 _68478)). Qed.
Lemma lem5231163 (_68478 : real -> Prop) : (term317 _68478) = (term322 _68478).
Proof. exact (TRANS (@lem5231155 _68478) (@lem5231162 _68478)). Qed.
Lemma lem5231164 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5231165 (_68478 : real -> Prop) : (term323 _68478) = (term324 _68478).
Proof. exact (MK_COMB (@lem5231164) (@lem5231163 _68478)). Qed.
Lemma lem5231166 (_68478 : real -> Prop) : (_68478 = (@EMPTY real)) = (_68478 = (@EMPTY real)).
Proof. exact (eq_refl (_68478 = (@EMPTY real))). Qed.
Lemma lem5231167 (_68478 : real -> Prop) : (term314 _68478) = (term325 _68478).
Proof. exact (MK_COMB (@lem5231165 _68478) (@lem5231166 _68478)). Qed.
Lemma lem5231168 (_68478 : real -> Prop) : (term307 _68478) = (term325 _68478).
Proof. exact (TRANS (@lem5231152 _68478) (@lem5231167 _68478)). Qed.
Lemma lem5231170 (x : real) (s : real -> Prop) (a : real) (h1 : term199 s x a) (h2 : term62 s a) : term322 s.
Proof. exact (conj (@lem5231032 s x a h1) (@lem5231062 s a h2)). Qed.
Lemma lem5231172 (_68478 : real -> Prop) (h1 : term17) : term325 _68478.
Proof. exact (EQ_MP (@lem5231168 _68478) (@lem5231149 _68478 h1)). Qed.
Lemma lem5231173 (s : real -> Prop) (h1 : term17) : term325 s.
Proof. exact (@lem5231172 s h1). Qed.
Lemma lem5231176 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s x a) (h3 : term62 s a) : s = (@EMPTY real).
Proof. exact (@lem5231173 s h1 (@lem5231170 x s a h2 h3)). Qed.
Lemma lem5231177 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s x a) (h3 : term62 s a) : term326 s.
Proof. exact (fun h0 : term225 s => @lem5231176 x s a h1 h2 h3). Qed.
Lemma lem5231179 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5231180 (s : real -> Prop) : (term326 s) = (s = (@EMPTY real)).
Proof. exact (@lem5231179 (s = (@EMPTY real))). Qed.
Lemma lem5231181 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s x a) (h3 : term62 s a) : s = (@EMPTY real).
Proof. exact (EQ_MP (@lem5231180 s) (@lem5231177 x s a h1 h2 h3)). Qed.
Lemma lem5231184 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5231186 (s : real -> Prop) : (term225 s) = (term327 s).
Proof. exact (@lem5231184 (s = (@EMPTY real))). Qed.
Lemma lem5231189 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term327 s.
Proof. exact (EQ_MP (@lem5231186 s) (@lem5230858 s x a h1)). Qed.
Lemma lem5231192 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s x a) (h3 : term62 s a) : False.
Proof. exact (@lem5231189 s x a h2 (@lem5231181 x s a h1 h2 h3)). Qed.
Lemma lem5231193 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s x a) (h3 : term62 s a) : term328.
Proof. exact (fun h0 : ~ False => @lem5231192 x s a h1 h2 h3). Qed.
Lemma lem5231195 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5231196 : term328 = False.
Proof. exact (@lem5231195 False). Qed.
Lemma lem5231197 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term199 s x a) (h3 : term62 s a) : False.
Proof. exact (EQ_MP (@lem5231196) (@lem5231193 x s a h1 h2 h3)). Qed.
Lemma lem5231280 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : @FINITE real s.
Proof. exact (proj1 (@lem5230534 s x a h1)). Qed.
Lemma lem5231281 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term292 s.
Proof. exact (fun h0 : term287 s => @lem5231280 s x a h1). Qed.
Lemma lem5231283 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5231284 (s : real -> Prop) : (term292 s) = (@FINITE real s).
Proof. exact (@lem5231283 (@FINITE real s)). Qed.
Lemma lem5231285 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : @FINITE real s.
Proof. exact (EQ_MP (@lem5231284 s) (@lem5231281 s x a h1)). Qed.
Lemma lem5231287 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term225 s.
Proof. exact (proj2 (@lem5230534 s x a h1)). Qed.
Lemma lem5231288 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term329 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5231287 s x a h1). Qed.
Lemma lem5231290 (p : Prop) : (term306 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5231291 (s : real -> Prop) : (term329 s) = (term225 s).
Proof. exact (@lem5231290 (s = (@EMPTY real))). Qed.
Lemma lem5231292 (s : real -> Prop) (x : real) (a : real) (h1 : term199 s x a) : term225 s.
Proof. exact (EQ_MP (@lem5231291 s) (@lem5231288 s x a h1)). Qed.
Lemma lem5231294 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : @IN real x s.
Proof. exact (proj1 (@lem5230541 s x a h1)). Qed.
Lemma lem5231295 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : term330 x s.
Proof. exact (fun h0 : term297 x s => @lem5231294 s x a h1). Qed.
Lemma lem5231297 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5231298 (x : real) (s : real -> Prop) : (term330 x s) = (@IN real x s).
Proof. exact (@lem5231297 (@IN real x s)). Qed.
Lemma lem5231299 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : @IN real x s.
Proof. exact (EQ_MP (@lem5231298 x s) (@lem5231295 s x a h1)). Qed.
Lemma lem5231305 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5231306 (_68484 : real -> Prop) (_68485 : real) : (term291 _68484 _68485) = (term331 _68484 _68485).
Proof. exact (@lem5231305 (_68484 = (@EMPTY real)) (term287 _68484) (term226 _68484 _68485)). Qed.
Lemma lem5231332 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5231333 (_68485 : real) (_68484 : real -> Prop) : (term226 _68484 _68485) = (term332 _68485 _68484).
Proof. exact (@lem5231332 (term227 _68484 _68485) (term297 _68485 _68484)). Qed.
Lemma lem5231339 (_68484 : real -> Prop) : (term221 _68484) = (term221 _68484).
Proof. exact (eq_refl (term221 _68484)). Qed.
Lemma lem5231340 (_68485 : real) (_68484 : real -> Prop) : (term333 _68484 _68485) = (term334 _68485 _68484).
Proof. exact (MK_COMB (@lem5231339 _68484) (@lem5231333 _68485 _68484)). Qed.
Lemma lem5231344 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5231345 (_68485 : real) (_68484 : real -> Prop) : (term334 _68485 _68484) = (term335 _68485 _68484).
Proof. exact (@lem5231344 (term227 _68484 _68485) (term287 _68484) (term297 _68485 _68484)). Qed.
Lemma lem5231361 (_68485 : real) (_68484 : real -> Prop) : (term333 _68484 _68485) = (term335 _68485 _68484).
Proof. exact (TRANS (@lem5231340 _68485 _68484) (@lem5231345 _68485 _68484)). Qed.
Lemma lem5231362 (_68484 : real -> Prop) : (term310 _68484) = (term310 _68484).
Proof. exact (eq_refl (term310 _68484)). Qed.
Lemma lem5231363 (_68485 : real) (_68484 : real -> Prop) : (term331 _68484 _68485) = (term336 _68485 _68484).
Proof. exact (MK_COMB (@lem5231362 _68484) (@lem5231361 _68485 _68484)). Qed.
Lemma lem5231374 (_68485 : real) (_68484 : real -> Prop) : (term291 _68484 _68485) = (term336 _68485 _68484).
Proof. exact (TRANS (@lem5231306 _68484 _68485) (@lem5231363 _68485 _68484)). Qed.
Lemma lem5231375 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5231376 (_68485 : real) (_68484 : real -> Prop) : (term337 _68484 _68485) = (term338 _68485 _68484).
Proof. exact (MK_COMB (@lem5231375) (@lem5231374 _68485 _68484)). Qed.
Lemma lem5231390 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5231391 (_68485 : real) (_68484 : real -> Prop) : (term339 _68485 _68484) = (term340 _68485 _68484).
Proof. exact (@lem5231390 (_68484 = (@EMPTY real)) (term287 _68484) (term297 _68485 _68484)). Qed.
Lemma lem5231409 (_68484 : real -> Prop) (_68485 : real) : (term341 _68484 _68485) = (term341 _68484 _68485).
Proof. exact (eq_refl (term341 _68484 _68485)). Qed.
Lemma lem5231410 (_68485 : real) (_68484 : real -> Prop) : (term342 _68485 _68484) = (term343 _68485 _68484).
Proof. exact (MK_COMB (@lem5231409 _68484 _68485) (@lem5231391 _68485 _68484)). Qed.
Lemma lem5231414 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5231415 (_68485 : real) (_68484 : real -> Prop) : (term343 _68485 _68484) = (term336 _68485 _68484).
Proof. exact (@lem5231414 (_68484 = (@EMPTY real)) (term227 _68484 _68485) (term344 _68485 _68484)). Qed.
Lemma lem5231443 (_68485 : real) (_68484 : real -> Prop) : (term342 _68485 _68484) = (term336 _68485 _68484).
Proof. exact (TRANS (@lem5231410 _68485 _68484) (@lem5231415 _68485 _68484)). Qed.
Lemma lem5231444 (_68485 : real) (_68484 : real -> Prop) : ((term291 _68484 _68485) = (term342 _68485 _68484)) = ((term336 _68485 _68484) = (term336 _68485 _68484)).
Proof. exact (MK_COMB (@lem5231376 _68485 _68484) (@lem5231443 _68485 _68484)). Qed.
Lemma lem5231446 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5231447 (x : Prop) : (x = x) = True.
Proof. exact (@lem5231446 Prop x). Qed.
Lemma lem5231448 (_68485 : real) (_68484 : real -> Prop) : ((term336 _68485 _68484) = (term336 _68485 _68484)) = True.
Proof. exact (@lem5231447 (term336 _68485 _68484)). Qed.
Lemma lem5231449 (_68485 : real) (_68484 : real -> Prop) : ((term291 _68484 _68485) = (term342 _68485 _68484)) = True.
Proof. exact (TRANS (@lem5231444 _68485 _68484) (@lem5231448 _68485 _68484)). Qed.
Lemma lem5231450 (_68485 : real) (_68484 : real -> Prop) : True = ((term291 _68484 _68485) = (term342 _68485 _68484)).
Proof. exact (SYM (@lem5231449 _68485 _68484)). Qed.
Lemma lem5231451 (_68485 : real) (_68484 : real -> Prop) : (term291 _68484 _68485) = (term342 _68485 _68484).
Proof. exact (EQ_MP (@lem5231450 _68485 _68484) (@lem0)). Qed.
Lemma lem5231452 (_68485 : real) (_68484 : real -> Prop) (h1 : term17) : term342 _68485 _68484.
Proof. exact (EQ_MP (@lem5231451 _68485 _68484) (@lem5230944 _68484 _68485 h1)). Qed.
Lemma lem5231454 (b : Prop) (a : Prop) : (a \/ b) = (term295 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5231455 (_68484 : real -> Prop) (_68485 : real) : (term342 _68485 _68484) = (term345 _68484 _68485).
Proof. exact (@lem5231454 (term339 _68485 _68484) (term227 _68484 _68485)). Qed.
Lemma lem5231457 (a : Prop) (b : Prop) : (term315 a b) = (term316 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5231458 (_68485 : real) (_68484 : real -> Prop) : (term346 _68485 _68484) = (term347 _68485 _68484).
Proof. exact (@lem5231457 (term287 _68484) (term348 _68485 _68484)). Qed.
Lemma lem5231460 (a : Prop) : (term298 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5231461 (_68484 : real -> Prop) : (term319 _68484) = (@FINITE real _68484).
Proof. exact (@lem5231460 (@FINITE real _68484)). Qed.
Lemma lem5231462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5231463 (_68484 : real -> Prop) : (term320 _68484) = (term321 _68484).
Proof. exact (MK_COMB (@lem5231462) (@lem5231461 _68484)). Qed.
Lemma lem5231465 (a : Prop) (b : Prop) : (term315 a b) = (term316 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5231466 (_68485 : real) (_68484 : real -> Prop) : (term349 _68485 _68484) = (term350 _68485 _68484).
Proof. exact (@lem5231465 (_68484 = (@EMPTY real)) (term297 _68485 _68484)). Qed.
Lemma lem5231468 (a : Prop) : (term298 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5231469 (_68485 : real) (_68484 : real -> Prop) : (term351 _68485 _68484) = (@IN real _68485 _68484).
Proof. exact (@lem5231468 (@IN real _68485 _68484)). Qed.
Lemma lem5231470 (_68484 : real -> Prop) : (term352 _68484) = (term352 _68484).
Proof. exact (eq_refl (term352 _68484)). Qed.
Lemma lem5231471 (_68485 : real) (_68484 : real -> Prop) : (term350 _68485 _68484) = (term353 _68485 _68484).
Proof. exact (MK_COMB (@lem5231470 _68484) (@lem5231469 _68485 _68484)). Qed.
Lemma lem5231472 (_68485 : real) (_68484 : real -> Prop) : (term349 _68485 _68484) = (term353 _68485 _68484).
Proof. exact (TRANS (@lem5231466 _68485 _68484) (@lem5231471 _68485 _68484)). Qed.
Lemma lem5231473 (_68485 : real) (_68484 : real -> Prop) : (term347 _68485 _68484) = (term354 _68485 _68484).
Proof. exact (MK_COMB (@lem5231463 _68484) (@lem5231472 _68485 _68484)). Qed.
Lemma lem5231474 (_68485 : real) (_68484 : real -> Prop) : (term346 _68485 _68484) = (term354 _68485 _68484).
Proof. exact (TRANS (@lem5231458 _68485 _68484) (@lem5231473 _68485 _68484)). Qed.
Lemma lem5231475 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5231476 (_68485 : real) (_68484 : real -> Prop) : (term355 _68485 _68484) = (term356 _68485 _68484).
Proof. exact (MK_COMB (@lem5231475) (@lem5231474 _68485 _68484)). Qed.
Lemma lem5231477 (_68484 : real -> Prop) (_68485 : real) : (term227 _68484 _68485) = (term227 _68484 _68485).
Proof. exact (eq_refl (term227 _68484 _68485)). Qed.
Lemma lem5231478 (_68484 : real -> Prop) (_68485 : real) : (term345 _68484 _68485) = (term357 _68484 _68485).
Proof. exact (MK_COMB (@lem5231476 _68485 _68484) (@lem5231477 _68484 _68485)). Qed.
Lemma lem5231479 (_68484 : real -> Prop) (_68485 : real) : (term342 _68485 _68484) = (term357 _68484 _68485).
Proof. exact (TRANS (@lem5231455 _68484 _68485) (@lem5231478 _68484 _68485)). Qed.
Lemma lem5231481 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) (h2 : term199 s x a) : term353 x s.
Proof. exact (conj (@lem5231292 s x a h2) (@lem5231299 s x a h1)). Qed.
Lemma lem5231482 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) (h2 : term199 s x a) : term354 x s.
Proof. exact (conj (@lem5231285 s x a h2) (@lem5231481 s x a h1 h2)). Qed.
Lemma lem5231484 (_68484 : real -> Prop) (_68485 : real) (h1 : term17) : term357 _68484 _68485.
Proof. exact (EQ_MP (@lem5231479 _68484 _68485) (@lem5231452 _68485 _68484 h1)). Qed.
Lemma lem5231485 (s : real -> Prop) (x : real) (h1 : term17) : term357 s x.
Proof. exact (@lem5231484 s x h1). Qed.
Lemma lem5231488 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term141 s x a) (h3 : term199 s x a) : term227 s x.
Proof. exact (@lem5231485 s x h1 (@lem5231482 s x a h2 h3)). Qed.
Lemma lem5231489 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term141 s x a) (h3 : term199 s x a) : term358 s x.
Proof. exact (fun h0 : term359 s x => @lem5231488 s x a h1 h2 h3). Qed.
Lemma lem5231491 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5231492 (s : real -> Prop) (x : real) : (term358 s x) = (term227 s x).
Proof. exact (@lem5231491 (term227 s x)). Qed.
Lemma lem5231493 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term141 s x a) (h3 : term199 s x a) : term227 s x.
Proof. exact (EQ_MP (@lem5231492 s x) (@lem5231489 s x a h1 h2 h3)). Qed.
Lemma lem5231495 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : real_lt x a.
Proof. exact (proj2 (@lem5230541 s x a h1)). Qed.
Lemma lem5231496 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : term360 x a.
Proof. exact (fun h0 : term290 x a => @lem5231495 s x a h1). Qed.
Lemma lem5231498 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5231499 (x : real) (a : real) : (term360 x a) = (real_lt x a).
Proof. exact (@lem5231498 (real_lt x a)). Qed.
Lemma lem5231500 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : real_lt x a.
Proof. exact (EQ_MP (@lem5231499 x a) (@lem5231496 s x a h1)). Qed.
Lemma lem5231516 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5231517 (_68481 : real) (_68482 : real) (_68483 : real) : (term361 _68482 _68481 _68483) = (term362 _68481 _68482 _68483).
Proof. exact (@lem5231516 (real_lt _68481 _68483) (term290 _68482 _68483)). Qed.
Lemma lem5231523 (_68481 : real) (_68482 : real) : (term363 _68481 _68482) = (term363 _68481 _68482).
Proof. exact (eq_refl (term363 _68481 _68482)). Qed.
Lemma lem5231524 (_68481 : real) (_68482 : real) (_68483 : real) : (term288 _68482 _68481 _68483) = (term364 _68481 _68482 _68483).
Proof. exact (MK_COMB (@lem5231523 _68481 _68482) (@lem5231517 _68481 _68482 _68483)). Qed.
Lemma lem5231528 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5231529 (_68481 : real) (_68482 : real) (_68483 : real) : (term364 _68481 _68482 _68483) = (term365 _68481 _68482 _68483).
Proof. exact (@lem5231528 (real_lt _68481 _68483) (term289 _68481 _68482) (term290 _68482 _68483)). Qed.
Lemma lem5231545 (_68481 : real) (_68482 : real) (_68483 : real) : (term288 _68482 _68481 _68483) = (term365 _68481 _68482 _68483).
Proof. exact (TRANS (@lem5231524 _68481 _68482 _68483) (@lem5231529 _68481 _68482 _68483)). Qed.
Lemma lem5231546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5231547 (_68481 : real) (_68482 : real) (_68483 : real) : (term366 _68482 _68481 _68483) = (term367 _68481 _68482 _68483).
Proof. exact (MK_COMB (@lem5231546) (@lem5231545 _68481 _68482 _68483)). Qed.
Lemma lem5231563 (_68481 : real) (_68482 : real) (_68483 : real) : (term365 _68481 _68482 _68483) = (term365 _68481 _68482 _68483).
Proof. exact (eq_refl (term365 _68481 _68482 _68483)). Qed.
Lemma lem5231564 (_68481 : real) (_68482 : real) (_68483 : real) : ((term288 _68482 _68481 _68483) = (term365 _68481 _68482 _68483)) = ((term365 _68481 _68482 _68483) = (term365 _68481 _68482 _68483)).
Proof. exact (MK_COMB (@lem5231547 _68481 _68482 _68483) (@lem5231563 _68481 _68482 _68483)). Qed.
Lemma lem5231566 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5231567 (x : Prop) : (x = x) = True.
Proof. exact (@lem5231566 Prop x). Qed.
Lemma lem5231568 (_68481 : real) (_68482 : real) (_68483 : real) : ((term365 _68481 _68482 _68483) = (term365 _68481 _68482 _68483)) = True.
Proof. exact (@lem5231567 (term365 _68481 _68482 _68483)). Qed.
Lemma lem5231569 (_68481 : real) (_68482 : real) (_68483 : real) : ((term288 _68482 _68481 _68483) = (term365 _68481 _68482 _68483)) = True.
Proof. exact (TRANS (@lem5231564 _68481 _68482 _68483) (@lem5231568 _68481 _68482 _68483)). Qed.
Lemma lem5231570 (_68481 : real) (_68482 : real) (_68483 : real) : True = ((term288 _68482 _68481 _68483) = (term365 _68481 _68482 _68483)).
Proof. exact (SYM (@lem5231569 _68481 _68482 _68483)). Qed.
Lemma lem5231571 (_68481 : real) (_68482 : real) (_68483 : real) : (term288 _68482 _68481 _68483) = (term365 _68481 _68482 _68483).
Proof. exact (EQ_MP (@lem5231570 _68481 _68482 _68483) (@lem0)). Qed.
Lemma lem5231572 (_68481 : real) (_68482 : real) (_68483 : real) (h1 : term37) : term365 _68481 _68482 _68483.
Proof. exact (EQ_MP (@lem5231571 _68481 _68482 _68483) (@lem5230906 _68482 _68481 _68483 h1)). Qed.
Lemma lem5231574 (b : Prop) (a : Prop) : (a \/ b) = (term295 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5231575 (_68482 : real) (_68481 : real) (_68483 : real) : (term365 _68481 _68482 _68483) = (term368 _68482 _68481 _68483).
Proof. exact (@lem5231574 (term208 _68481 _68482 _68483) (real_lt _68481 _68483)). Qed.
Lemma lem5231577 (a : Prop) (b : Prop) : (term315 a b) = (term316 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5231578 (_68481 : real) (_68482 : real) (_68483 : real) : (term369 _68481 _68482 _68483) = (term370 _68481 _68482 _68483).
Proof. exact (@lem5231577 (term289 _68481 _68482) (term290 _68482 _68483)). Qed.
Lemma lem5231580 (a : Prop) : (term298 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5231581 (_68481 : real) (_68482 : real) : (term371 _68481 _68482) = (real_le _68481 _68482).
Proof. exact (@lem5231580 (real_le _68481 _68482)). Qed.
Lemma lem5231582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5231583 (_68481 : real) (_68482 : real) : (term372 _68481 _68482) = (term373 _68481 _68482).
Proof. exact (MK_COMB (@lem5231582) (@lem5231581 _68481 _68482)). Qed.
Lemma lem5231585 (a : Prop) : (term298 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5231586 (_68482 : real) (_68483 : real) : (term299 _68482 _68483) = (real_lt _68482 _68483).
Proof. exact (@lem5231585 (real_lt _68482 _68483)). Qed.
Lemma lem5231587 (_68481 : real) (_68482 : real) (_68483 : real) : (term370 _68481 _68482 _68483) = (term213 _68481 _68482 _68483).
Proof. exact (MK_COMB (@lem5231583 _68481 _68482) (@lem5231586 _68482 _68483)). Qed.
Lemma lem5231588 (_68481 : real) (_68482 : real) (_68483 : real) : (term369 _68481 _68482 _68483) = (term213 _68481 _68482 _68483).
Proof. exact (TRANS (@lem5231578 _68481 _68482 _68483) (@lem5231587 _68481 _68482 _68483)). Qed.
Lemma lem5231589 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5231590 (_68481 : real) (_68482 : real) (_68483 : real) : (term374 _68481 _68482 _68483) = (term375 _68481 _68482 _68483).
Proof. exact (MK_COMB (@lem5231589) (@lem5231588 _68481 _68482 _68483)). Qed.
Lemma lem5231591 (_68481 : real) (_68483 : real) : (real_lt _68481 _68483) = (real_lt _68481 _68483).
Proof. exact (eq_refl (real_lt _68481 _68483)). Qed.
Lemma lem5231592 (_68482 : real) (_68481 : real) (_68483 : real) : (term368 _68482 _68481 _68483) = (term31 _68482 _68481 _68483).
Proof. exact (MK_COMB (@lem5231590 _68481 _68482 _68483) (@lem5231591 _68481 _68483)). Qed.
Lemma lem5231593 (_68482 : real) (_68481 : real) (_68483 : real) : (term365 _68481 _68482 _68483) = (term31 _68482 _68481 _68483).
Proof. exact (TRANS (@lem5231575 _68482 _68481 _68483) (@lem5231592 _68482 _68481 _68483)). Qed.
Lemma lem5231595 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term141 s x a) (h3 : term199 s x a) : term376 s x a.
Proof. exact (conj (@lem5231493 s x a h1 h2 h3) (@lem5231500 s x a h2)). Qed.
Lemma lem5231597 (_68482 : real) (_68481 : real) (_68483 : real) (h1 : term37) : term31 _68482 _68481 _68483.
Proof. exact (EQ_MP (@lem5231593 _68482 _68481 _68483) (@lem5231572 _68481 _68482 _68483 h1)). Qed.
Lemma lem5231598 (x : real) (s : real -> Prop) (a : real) (h1 : term37) : term377 x s a.
Proof. exact (@lem5231597 x (inf s) a h1). Qed.
Lemma lem5231601 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term141 s x a) (h4 : term199 s x a) : term42 s a.
Proof. exact (@lem5231598 x s a h2 (@lem5231595 s x a h1 h3 h4)). Qed.
Lemma lem5231602 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term141 s x a) (h4 : term199 s x a) : term294 s a.
Proof. exact (fun h0 : term135 s a => @lem5231601 s x a h1 h2 h3 h4). Qed.
Lemma lem5231604 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5231605 (s : real -> Prop) (a : real) : (term294 s a) = (term42 s a).
Proof. exact (@lem5231604 (term42 s a)). Qed.
Lemma lem5231606 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term141 s x a) (h4 : term199 s x a) : term42 s a.
Proof. exact (EQ_MP (@lem5231605 s a) (@lem5231602 s x a h1 h2 h3 h4)). Qed.
Lemma lem5231609 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5231611 (s : real -> Prop) (a : real) : (term135 s a) = (term378 s a).
Proof. exact (@lem5231609 (term42 s a)). Qed.
Lemma lem5231614 (s : real -> Prop) (x : real) (a : real) (h1 : term141 s x a) : term378 s a.
Proof. exact (EQ_MP (@lem5231611 s a) (@lem5230912 s x a h1)). Qed.
Lemma lem5231617 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term141 s x a) (h4 : term199 s x a) : False.
Proof. exact (@lem5231614 s x a h3 (@lem5231606 s x a h1 h2 h3 h4)). Qed.
Lemma lem5231618 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term141 s x a) (h4 : term199 s x a) : term328.
Proof. exact (fun h0 : ~ False => @lem5231617 s x a h1 h2 h3 h4). Qed.
Lemma lem5231620 (p : Prop) : (term293 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5231621 : term328 = False.
Proof. exact (@lem5231620 False). Qed.
Lemma lem5231622 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term141 s x a) (h4 : term199 s x a) : False.
Proof. exact (EQ_MP (@lem5231621) (@lem5231618 s x a h1 h2 h3 h4)). Qed.
Lemma lem5231623 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term199 s x a) : False.
Proof. exact (or_elim (@lem5230533 s x a h3) (fun h0 : term62 s a => @lem5231197 x s a h1 h3 h0) (fun h0 : term141 s x a => @lem5231622 s x a h1 h2 h0 h3)). Qed.
Lemma lem5231624 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term199 s x a) : (term199 s x a) = False.
Proof. exact (prop_ext (fun h4 : term199 s x a => @lem5231623 s x a h1 h2 h3) (fun h4 : False => @lem5230532 s x a h3)). Qed.
Lemma lem5231625 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term199 s x a) : False.
Proof. exact (EQ_MP (@lem5231624 s x a h1 h2 h3) (@lem5230532 s x a h3)). Qed.
Lemma lem5231626 (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term202 s a) : False.
Proof. exact (ex_elim (@lem5230371 s a h3) (fun x : real => fun h0 : term201 s a x => @lem5231625 s x a h1 h2 h0)). Qed.
Lemma lem5231627 (s : real -> Prop) (h1 : term17) (h2 : term37) (h3 : term204 s) : False.
Proof. exact (ex_elim (@lem5230370 s h3) (fun a : real => fun h0 : term203 s a => @lem5231626 s a h1 h2 h0)). Qed.
Lemma lem5231628 (h1 : term17) (h2 : term37) (h3 : term10) : False.
Proof. exact (ex_elim (@lem5230154 h3) (fun s : real -> Prop => fun h0 : term205 s => @lem5231627 s h1 h2 h0)). Qed.
Lemma lem5231629 (h1 : term37) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem5231628 h0 h1 h2). Qed.
Lemma lem5231630 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem5231631 (h1 : term37) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem5231630) (@lem5231629 h1 h2)). Qed.
Lemma lem5231632 (h1 : term10) : term20.
Proof. exact (fun h0 : term37 => @lem5231631 h0 h1). Qed.
Lemma lem5231633 : term22.
Proof. exact (fun h0 : term10 => @lem5231632 h0). Qed.
Lemma lem5231634 : term11.
Proof. exact (EQ_MP (@lem5229656) (@lem5231633)). Qed.
Lemma lem5231636 : term11.
Proof. exact (@lem5229388 (@lem5231634)). Qed.
Lemma lem5231637 (h1 : term10) : term19.
Proof. exact (@lem5231636 (@lem5229373 h1)). Qed.
Lemma lem5231638 (h1 : term10) : term15.
Proof. exact (@lem5231637 h1 (@lem1371386)). Qed.
Lemma lem5231639 (h1 : term10) : False.
Proof. exact (@lem5231638 h1 (@lem5222545)). Qed.
Lemma lem5231640 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem5231639 h1) (fun h2 : False => @lem5229373 h1)). Qed.
Lemma lem5231641 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem5231640 h1) (@lem5229373 h1)). Qed.
Lemma lem5231642 : term9.
Proof. exact (fun h0 : term10 => @lem5231641 h0). Qed.
Lemma lem5231643 : term8.
Proof. exact (EQ_MP (@lem5229372) (@lem5231642)). Qed.
