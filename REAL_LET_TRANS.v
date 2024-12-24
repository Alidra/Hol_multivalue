Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LET_TRANS_term_abbrevs.
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
Lemma lem1370313 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1370314 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1370315 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1370314 t1) (@lem1370313 t1)). Qed.
Lemma lem1370316 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1370315 t1 t2). Qed.
Lemma lem1370317 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1370318 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1370317 t1 t2) (@lem1370316 t1 t2)). Qed.
Lemma lem1370319 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1370318 t1 t2 t3). Qed.
Lemma lem1370320 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1370321 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1370320 t1 t2 t3) (@lem1370319 t1 t2 t3)). Qed.
Lemma lem1370322 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1370321 t1 t2 t3)). Qed.
Lemma lem1370324 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1370325 : term8 = term9.
Proof. exact (@lem1370324 term8). Qed.
Lemma lem1370326 : term9 = term8.
Proof. exact (SYM (@lem1370325)). Qed.
Lemma lem1370327 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1370330 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1370331 : term12.
Proof. exact (fun h0 : term11 => @lem1370330 h0). Qed.
Lemma lem1370332 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1370333 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1370334 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1370332 h2 (@lem1370333 h1)). Qed.
Lemma lem1370335 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1370334 h1 h0). Qed.
Lemma lem1370336 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1370337 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1370335 h1 (@lem1370336 h2)). Qed.
Lemma lem1370338 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1370337 h0 h1). Qed.
Lemma lem1370339 : term14.
Proof. exact (fun h0 : term12 => @lem1370338 h0). Qed.
Lemma lem1370342 : term12.
Proof. exact (@lem1370339 (@lem1370331)). Qed.
Lemma lem1370380 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1370381 : term15 = term16.
Proof. exact (@lem1370380 term17). Qed.
Lemma lem1370390 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1370391 : term19 = term20.
Proof. exact (MK_COMB (@lem1370390) (@lem1370381)). Qed.
Lemma lem1370394 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1370401 : term11 = term22.
Proof. exact (MK_COMB (@lem1370394) (@lem1370391)). Qed.
Lemma lem1370408 (y : real) (x : real) : ((real_lt x y) = (term23 y x)) = ((real_lt x y) = (term23 y x)).
Proof. exact (eq_refl ((real_lt x y) = (term23 y x))). Qed.
Lemma lem1370409 (y : real) : (term24 y) = (term24 y).
Proof. exact (fun_ext (fun x : real => @lem1370408 y x)). Qed.
Lemma lem1370410 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370411 (y : real) : (term25 y) = (term25 y).
Proof. exact (MK_COMB (@lem1370410) (@lem1370409 y)). Qed.
Lemma lem1370412 : term26 = term26.
Proof. exact (fun_ext (fun y : real => @lem1370411 y)). Qed.
Lemma lem1370413 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370414 : term17 = term17.
Proof. exact (MK_COMB (@lem1370413) (@lem1370412)). Qed.
Lemma lem1370415 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1370416 : term16 = term16.
Proof. exact (MK_COMB (@lem1370415) (@lem1370414)). Qed.
Lemma lem1370425 (y : real) (x : real) (z : real) : (term27 y x z) = (term27 y x z).
Proof. exact (eq_refl (term27 y x z)). Qed.
Lemma lem1370426 (y : real) (x : real) : (term28 y x) = (term28 y x).
Proof. exact (fun_ext (fun z : real => @lem1370425 y x z)). Qed.
Lemma lem1370427 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370428 (y : real) (x : real) : (term29 y x) = (term29 y x).
Proof. exact (MK_COMB (@lem1370427) (@lem1370426 y x)). Qed.
Lemma lem1370429 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1370428 y x)). Qed.
Lemma lem1370430 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370431 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1370430) (@lem1370429 x)). Qed.
Lemma lem1370432 : term32 = term32.
Proof. exact (fun_ext (fun x : real => @lem1370431 x)). Qed.
Lemma lem1370433 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370434 : term33 = term33.
Proof. exact (MK_COMB (@lem1370433) (@lem1370432)). Qed.
Lemma lem1370435 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1370436 : term18 = term18.
Proof. exact (MK_COMB (@lem1370435) (@lem1370434)). Qed.
Lemma lem1370437 : term20 = term20.
Proof. exact (MK_COMB (@lem1370436) (@lem1370416)). Qed.
Lemma lem1370446 (y : real) (x : real) (z : real) : (term34 y x z) = (term34 y x z).
Proof. exact (eq_refl (term34 y x z)). Qed.
Lemma lem1370447 (y : real) (x : real) : (term35 y x) = (term35 y x).
Proof. exact (fun_ext (fun z : real => @lem1370446 y x z)). Qed.
Lemma lem1370448 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370449 (y : real) (x : real) : (term36 y x) = (term36 y x).
Proof. exact (MK_COMB (@lem1370448) (@lem1370447 y x)). Qed.
Lemma lem1370450 (x : real) : (term37 x) = (term37 x).
Proof. exact (fun_ext (fun y : real => @lem1370449 y x)). Qed.
Lemma lem1370451 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370452 (x : real) : (term38 x) = (term38 x).
Proof. exact (MK_COMB (@lem1370451) (@lem1370450 x)). Qed.
Lemma lem1370453 : term39 = term39.
Proof. exact (fun_ext (fun x : real => @lem1370452 x)). Qed.
Lemma lem1370454 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370455 : term8 = term8.
Proof. exact (MK_COMB (@lem1370454) (@lem1370453)). Qed.
Lemma lem1370456 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1370457 : term10 = term10.
Proof. exact (MK_COMB (@lem1370456) (@lem1370455)). Qed.
Lemma lem1370458 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1370459 : term21 = term21.
Proof. exact (MK_COMB (@lem1370458) (@lem1370457)). Qed.
Lemma lem1370460 : term22 = term22.
Proof. exact (MK_COMB (@lem1370459) (@lem1370437)). Qed.
Lemma lem1370523 : term11 = term22.
Proof. exact (TRANS (@lem1370401) (@lem1370460)). Qed.
Lemma lem1370524 : term22 = term11.
Proof. exact (SYM (@lem1370523)). Qed.
Lemma lem1370525 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1370526 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1370527 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1370538 (y : real) (x : real) (z : real) : (term40 y x z) = (term41 y x z).
Proof. exact (@lem17362 (term42 x y z) (real_lt x z)). Qed.
Lemma lem1370539 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1370540 (y : real) (x : real) : (term45 y x) = (term46 y x).
Proof. exact (@lem1370539 (term35 y x)). Qed.
Lemma lem1370541 (y : real) (x : real) (z : real) : (term47 y x z) = (term34 y x z).
Proof. exact (eq_refl (term47 y x z)). Qed.
Lemma lem1370542 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1370543 (y : real) (x : real) (z : real) : (term48 y x z) = (term40 y x z).
Proof. exact (MK_COMB (@lem1370542) (@lem1370541 y x z)). Qed.
Lemma lem1370544 (y : real) (x : real) (z : real) : (term48 y x z) = (term41 y x z).
Proof. exact (TRANS (@lem1370543 y x z) (@lem1370538 y x z)). Qed.
Lemma lem1370545 (y : real) (x : real) : (term49 y x) = (term50 y x).
Proof. exact (fun_ext (fun z : real => @lem1370544 y x z)). Qed.
Lemma lem1370546 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1370547 (y : real) (x : real) : (term46 y x) = (term51 y x).
Proof. exact (MK_COMB (@lem1370546) (@lem1370545 y x)). Qed.
Lemma lem1370548 (y : real) (x : real) : (term45 y x) = (term51 y x).
Proof. exact (TRANS (@lem1370540 y x) (@lem1370547 y x)). Qed.
Lemma lem1370549 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1370550 (x : real) : (term52 x) = (term53 x).
Proof. exact (@lem1370549 (term37 x)). Qed.
Lemma lem1370551 (y : real) (x : real) : (term54 x y) = (term36 y x).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1370552 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1370553 (y : real) (x : real) : (term55 x y) = (term45 y x).
Proof. exact (MK_COMB (@lem1370552) (@lem1370551 y x)). Qed.
Lemma lem1370554 (y : real) (x : real) : (term55 x y) = (term51 y x).
Proof. exact (TRANS (@lem1370553 y x) (@lem1370548 y x)). Qed.
Lemma lem1370555 (x : real) : (term56 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1370554 y x)). Qed.
Lemma lem1370556 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1370557 (x : real) : (term53 x) = (term58 x).
Proof. exact (MK_COMB (@lem1370556) (@lem1370555 x)). Qed.
Lemma lem1370558 (x : real) : (term52 x) = (term58 x).
Proof. exact (TRANS (@lem1370550 x) (@lem1370557 x)). Qed.
Lemma lem1370559 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1370560 : term10 = term59.
Proof. exact (@lem1370559 term39). Qed.
Lemma lem1370561 (x : real) : (term60 x) = (term38 x).
Proof. exact (eq_refl (term60 x)). Qed.
Lemma lem1370562 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1370563 (x : real) : (term61 x) = (term52 x).
Proof. exact (MK_COMB (@lem1370562) (@lem1370561 x)). Qed.
Lemma lem1370564 (x : real) : (term61 x) = (term58 x).
Proof. exact (TRANS (@lem1370563 x) (@lem1370558 x)). Qed.
Lemma lem1370565 : term62 = term63.
Proof. exact (fun_ext (fun x : real => @lem1370564 x)). Qed.
Lemma lem1370566 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1370567 : term59 = term64.
Proof. exact (MK_COMB (@lem1370566) (@lem1370565)). Qed.
Lemma lem1370628 : term10 = term64.
Proof. exact (TRANS (@lem1370560) (@lem1370567)). Qed.
Lemma lem1370629 (h1 : term10) : term64.
Proof. exact (EQ_MP (@lem1370628) (@lem1370525 h1)). Qed.
Lemma lem1370636 (x : real) (y : real) (z : real) : (term65 x y z) = (term66 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem1370637 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem1370638 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1370639 (x : real) (y : real) (z : real) : (term67 x y z) = (term68 x y z).
Proof. exact (MK_COMB (@lem1370638) (@lem1370636 x y z)). Qed.
Lemma lem1370640 (y : real) (x : real) (z : real) : (term69 y x z) = (term70 y x z).
Proof. exact (MK_COMB (@lem1370639 x y z) (@lem1370637 x z)). Qed.
Lemma lem1370641 (y : real) (x : real) (z : real) : (term27 y x z) = (term69 y x z).
Proof. exact (@lem17265 (term71 x y z) (real_le x z)). Qed.
Lemma lem1370642 (y : real) (x : real) (z : real) : (term27 y x z) = (term70 y x z).
Proof. exact (TRANS (@lem1370641 y x z) (@lem1370640 y x z)). Qed.
Lemma lem1370643 (y : real) (x : real) : (term28 y x) = (term72 y x).
Proof. exact (fun_ext (fun z : real => @lem1370642 y x z)). Qed.
Lemma lem1370644 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370645 (y : real) (x : real) : (term29 y x) = (term73 y x).
Proof. exact (MK_COMB (@lem1370644) (@lem1370643 y x)). Qed.
Lemma lem1370646 (x : real) : (term30 x) = (term74 x).
Proof. exact (fun_ext (fun y : real => @lem1370645 y x)). Qed.
Lemma lem1370647 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370648 (x : real) : (term31 x) = (term75 x).
Proof. exact (MK_COMB (@lem1370647) (@lem1370646 x)). Qed.
Lemma lem1370649 : term32 = term76.
Proof. exact (fun_ext (fun x : real => @lem1370648 x)). Qed.
Lemma lem1370650 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370711 : term33 = term77.
Proof. exact (MK_COMB (@lem1370650) (@lem1370649)). Qed.
Lemma lem1370712 (h1 : term33) : term77.
Proof. exact (EQ_MP (@lem1370711) (@lem1370526 h1)). Qed.
Lemma lem1370718 (y : real) (x : real) : (term78 y x) = (real_le y x).
Proof. exact (@lem16933 (real_le y x)). Qed.
Lemma lem1370721 (y : real) (x : real) : (term79 y x) = (term79 y x).
Proof. exact (eq_refl (term79 y x)). Qed.
Lemma lem1370723 (x : real) (y : real) : (term80 x y) = (term80 x y).
Proof. exact (eq_refl (term80 x y)). Qed.
Lemma lem1370724 (y : real) (x : real) : (term81 y x) = (term82 y x).
Proof. exact (MK_COMB (@lem1370723 x y) (@lem1370718 y x)). Qed.
Lemma lem1370725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1370726 (y : real) (x : real) : (term83 y x) = (term84 y x).
Proof. exact (MK_COMB (@lem1370725) (@lem1370724 y x)). Qed.
Lemma lem1370727 (y : real) (x : real) : (term85 y x) = (term86 y x).
Proof. exact (MK_COMB (@lem1370726 y x) (@lem1370721 y x)). Qed.
Lemma lem1370728 (y : real) (x : real) : ((real_lt x y) = (term23 y x)) = (term85 y x).
Proof. exact (@lem17784 (real_lt x y) (term23 y x)). Qed.
Lemma lem1370729 (y : real) (x : real) : ((real_lt x y) = (term23 y x)) = (term86 y x).
Proof. exact (TRANS (@lem1370728 y x) (@lem1370727 y x)). Qed.
Lemma lem1370730 (y : real) : (term24 y) = (term87 y).
Proof. exact (fun_ext (fun x : real => @lem1370729 y x)). Qed.
Lemma lem1370731 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370732 (y : real) : (term25 y) = (term88 y).
Proof. exact (MK_COMB (@lem1370731) (@lem1370730 y)). Qed.
Lemma lem1370733 : term26 = term89.
Proof. exact (fun_ext (fun y : real => @lem1370732 y)). Qed.
Lemma lem1370734 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370735 : term17 = term90.
Proof. exact (MK_COMB (@lem1370734) (@lem1370733)). Qed.
Lemma lem1370741 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term91 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1370742 (P : real -> Prop) (Q : real -> Prop) : (term93 P Q) = (term94 P Q).
Proof. exact (@lem1370741 real P Q). Qed.
Lemma lem1370743 (y : real) : (term95 y) = (term96 y).
Proof. exact (@lem1370742 (term97 y) (term98 y)). Qed.
Lemma lem1370744 (y : real) (x : real) : (term99 y x) = (term82 y x).
Proof. exact (eq_refl (term99 y x)). Qed.
Lemma lem1370745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1370746 (y : real) (x : real) : (term100 y x) = (term84 y x).
Proof. exact (MK_COMB (@lem1370745) (@lem1370744 y x)). Qed.
Lemma lem1370747 (y : real) (x : real) : (term101 y x) = (term79 y x).
Proof. exact (eq_refl (term101 y x)). Qed.
Lemma lem1370748 (y : real) (x : real) : (term102 y x) = (term86 y x).
Proof. exact (MK_COMB (@lem1370746 y x) (@lem1370747 y x)). Qed.
Lemma lem1370749 (y : real) : (term103 y) = (term87 y).
Proof. exact (fun_ext (fun x : real => @lem1370748 y x)). Qed.
Lemma lem1370750 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370751 (y : real) : (term95 y) = (term88 y).
Proof. exact (MK_COMB (@lem1370750) (@lem1370749 y)). Qed.
Lemma lem1370752 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1370753 (y : real) : (term104 y) = (term105 y).
Proof. exact (MK_COMB (@lem1370752) (@lem1370751 y)). Qed.
Lemma lem1370754 (y : real) (x : real) : (term99 y x) = (term82 y x).
Proof. exact (eq_refl (term99 y x)). Qed.
Lemma lem1370755 (y : real) : (term106 y) = (term97 y).
Proof. exact (fun_ext (fun x : real => @lem1370754 y x)). Qed.
Lemma lem1370756 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370757 (y : real) : (term107 y) = (term108 y).
Proof. exact (MK_COMB (@lem1370756) (@lem1370755 y)). Qed.
Lemma lem1370758 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1370759 (y : real) : (term109 y) = (term110 y).
Proof. exact (MK_COMB (@lem1370758) (@lem1370757 y)). Qed.
Lemma lem1370760 (y : real) (x : real) : (term101 y x) = (term79 y x).
Proof. exact (eq_refl (term101 y x)). Qed.
Lemma lem1370761 (y : real) : (term111 y) = (term98 y).
Proof. exact (fun_ext (fun x : real => @lem1370760 y x)). Qed.
Lemma lem1370762 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370763 (y : real) : (term112 y) = (term113 y).
Proof. exact (MK_COMB (@lem1370762) (@lem1370761 y)). Qed.
Lemma lem1370764 (y : real) : (term96 y) = (term114 y).
Proof. exact (MK_COMB (@lem1370759 y) (@lem1370763 y)). Qed.
Lemma lem1370765 (y : real) : ((term95 y) = (term96 y)) = ((term88 y) = (term114 y)).
Proof. exact (MK_COMB (@lem1370753 y) (@lem1370764 y)). Qed.
Lemma lem1370766 (y : real) : (term88 y) = (term114 y).
Proof. exact (EQ_MP (@lem1370765 y) (@lem1370743 y)). Qed.
Lemma lem1370863 : term89 = term115.
Proof. exact (fun_ext (fun y : real => @lem1370766 y)). Qed.
Lemma lem1370864 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370865 : term90 = term116.
Proof. exact (MK_COMB (@lem1370864) (@lem1370863)). Qed.
Lemma lem1370867 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term91 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1370868 (P : real -> Prop) (Q : real -> Prop) : (term93 P Q) = (term94 P Q).
Proof. exact (@lem1370867 real P Q). Qed.
Lemma lem1370869 : term117 = term118.
Proof. exact (@lem1370868 term119 term120). Qed.
Lemma lem1370870 (y : real) : (term121 y) = (term108 y).
Proof. exact (eq_refl (term121 y)). Qed.
Lemma lem1370871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1370872 (y : real) : (term122 y) = (term110 y).
Proof. exact (MK_COMB (@lem1370871) (@lem1370870 y)). Qed.
Lemma lem1370873 (y : real) : (term123 y) = (term113 y).
Proof. exact (eq_refl (term123 y)). Qed.
Lemma lem1370874 (y : real) : (term124 y) = (term114 y).
Proof. exact (MK_COMB (@lem1370872 y) (@lem1370873 y)). Qed.
Lemma lem1370875 : term125 = term115.
Proof. exact (fun_ext (fun y : real => @lem1370874 y)). Qed.
Lemma lem1370876 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370877 : term117 = term116.
Proof. exact (MK_COMB (@lem1370876) (@lem1370875)). Qed.
Lemma lem1370878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1370879 : term126 = term127.
Proof. exact (MK_COMB (@lem1370878) (@lem1370877)). Qed.
Lemma lem1370880 (y : real) : (term121 y) = (term108 y).
Proof. exact (eq_refl (term121 y)). Qed.
Lemma lem1370881 : term128 = term119.
Proof. exact (fun_ext (fun y : real => @lem1370880 y)). Qed.
Lemma lem1370882 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370883 : term129 = term130.
Proof. exact (MK_COMB (@lem1370882) (@lem1370881)). Qed.
Lemma lem1370884 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1370885 : term131 = term132.
Proof. exact (MK_COMB (@lem1370884) (@lem1370883)). Qed.
Lemma lem1370886 (y : real) : (term123 y) = (term113 y).
Proof. exact (eq_refl (term123 y)). Qed.
Lemma lem1370887 : term133 = term120.
Proof. exact (fun_ext (fun y : real => @lem1370886 y)). Qed.
Lemma lem1370888 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1370889 : term134 = term135.
Proof. exact (MK_COMB (@lem1370888) (@lem1370887)). Qed.
Lemma lem1370890 : term118 = term136.
Proof. exact (MK_COMB (@lem1370885) (@lem1370889)). Qed.
Lemma lem1370891 : (term117 = term118) = (term116 = term136).
Proof. exact (MK_COMB (@lem1370879) (@lem1370890)). Qed.
Lemma lem1370892 : term116 = term136.
Proof. exact (EQ_MP (@lem1370891) (@lem1370869)). Qed.
Lemma lem1370999 : term90 = term136.
Proof. exact (TRANS (@lem1370865) (@lem1370892)). Qed.
Lemma lem1371000 : term17 = term136.
Proof. exact (TRANS (@lem1370735) (@lem1370999)). Qed.
Lemma lem1371001 (h1 : term17) : term136.
Proof. exact (EQ_MP (@lem1371000) (@lem1370527 h1)). Qed.
Lemma lem1371002 (x : real) (h1 : term58 x) : term58 x.
Proof. exact (h1). Qed.
Lemma lem1371003 (y : real) (x : real) (h1 : term51 y x) : term51 y x.
Proof. exact (h1). Qed.
Lemma lem1371029 (y : real) (x : real) (z : real) : (term70 y x z) = (term70 y x z).
Proof. exact (eq_refl (term70 y x z)). Qed.
Lemma lem1371030 (y : real) (x : real) : (term72 y x) = (term72 y x).
Proof. exact (fun_ext (fun z : real => @lem1371029 y x z)). Qed.
Lemma lem1371031 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371032 (y : real) (x : real) : (term73 y x) = (term73 y x).
Proof. exact (MK_COMB (@lem1371031) (@lem1371030 y x)). Qed.
Lemma lem1371033 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : real => @lem1371032 y x)). Qed.
Lemma lem1371034 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371035 (x : real) : (term75 x) = (term75 x).
Proof. exact (MK_COMB (@lem1371034) (@lem1371033 x)). Qed.
Lemma lem1371036 : term76 = term76.
Proof. exact (fun_ext (fun x : real => @lem1371035 x)). Qed.
Lemma lem1371037 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371038 : term77 = term77.
Proof. exact (MK_COMB (@lem1371037) (@lem1371036)). Qed.
Lemma lem1371039 (h1 : term33) : term77.
Proof. exact (EQ_MP (@lem1371038) (@lem1370712 h1)). Qed.
Lemma lem1371056 (y : real) (x : real) : (term79 y x) = (term79 y x).
Proof. exact (eq_refl (term79 y x)). Qed.
Lemma lem1371057 (y : real) : (term98 y) = (term98 y).
Proof. exact (fun_ext (fun x : real => @lem1371056 y x)). Qed.
Lemma lem1371058 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371059 (y : real) : (term113 y) = (term113 y).
Proof. exact (MK_COMB (@lem1371058) (@lem1371057 y)). Qed.
Lemma lem1371060 : term120 = term120.
Proof. exact (fun_ext (fun y : real => @lem1371059 y)). Qed.
Lemma lem1371061 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371062 : term135 = term135.
Proof. exact (MK_COMB (@lem1371061) (@lem1371060)). Qed.
Lemma lem1371075 (y : real) (x : real) : (term82 y x) = (term82 y x).
Proof. exact (eq_refl (term82 y x)). Qed.
Lemma lem1371076 (y : real) : (term97 y) = (term97 y).
Proof. exact (fun_ext (fun x : real => @lem1371075 y x)). Qed.
Lemma lem1371077 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371078 (y : real) : (term108 y) = (term108 y).
Proof. exact (MK_COMB (@lem1371077) (@lem1371076 y)). Qed.
Lemma lem1371079 : term119 = term119.
Proof. exact (fun_ext (fun y : real => @lem1371078 y)). Qed.
Lemma lem1371080 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371081 : term130 = term130.
Proof. exact (MK_COMB (@lem1371080) (@lem1371079)). Qed.
Lemma lem1371082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1371083 : term132 = term132.
Proof. exact (MK_COMB (@lem1371082) (@lem1371081)). Qed.
Lemma lem1371084 : term136 = term136.
Proof. exact (MK_COMB (@lem1371083) (@lem1371062)). Qed.
Lemma lem1371085 (h1 : term17) : term136.
Proof. exact (EQ_MP (@lem1371084) (@lem1371001 h1)). Qed.
Lemma lem1371109 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term41 y x z.
Proof. exact (h1). Qed.
Lemma lem1371111 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term42 x y z.
Proof. exact (proj1 (@lem1371109 y x z h1)). Qed.
Lemma lem1371114 (h1 : term17) : term135.
Proof. exact (proj2 (@lem1371085 h1)). Qed.
Lemma lem1371115 (h1 : term17) : term130.
Proof. exact (proj1 (@lem1371085 h1)). Qed.
Lemma lem1371129 (y : real) (x : real) (z : real) : (term70 y x z) = (term70 y x z).
Proof. exact (eq_refl (term70 y x z)). Qed.
Lemma lem1371130 (y : real) (x : real) : (term72 y x) = (term72 y x).
Proof. exact (fun_ext (fun z : real => @lem1371129 y x z)). Qed.
Lemma lem1371131 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371132 (y : real) (x : real) : (term73 y x) = (term73 y x).
Proof. exact (MK_COMB (@lem1371131) (@lem1371130 y x)). Qed.
Lemma lem1371133 (x : real) : (term74 x) = (term74 x).
Proof. exact (fun_ext (fun y : real => @lem1371132 y x)). Qed.
Lemma lem1371134 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371135 (x : real) : (term75 x) = (term75 x).
Proof. exact (MK_COMB (@lem1371134) (@lem1371133 x)). Qed.
Lemma lem1371136 : term76 = term76.
Proof. exact (fun_ext (fun x : real => @lem1371135 x)). Qed.
Lemma lem1371137 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371139 : term77 = term77.
Proof. exact (MK_COMB (@lem1371137) (@lem1371136)). Qed.
Lemma lem1371140 (h1 : term33) : term77.
Proof. exact (EQ_MP (@lem1371139) (@lem1371039 h1)). Qed.
Lemma lem1371160 (y : real) (x : real) : (term82 y x) = (term82 y x).
Proof. exact (eq_refl (term82 y x)). Qed.
Lemma lem1371161 (y : real) : (term97 y) = (term97 y).
Proof. exact (fun_ext (fun x : real => @lem1371160 y x)). Qed.
Lemma lem1371162 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371163 (y : real) : (term108 y) = (term108 y).
Proof. exact (MK_COMB (@lem1371162) (@lem1371161 y)). Qed.
Lemma lem1371164 : term119 = term119.
Proof. exact (fun_ext (fun y : real => @lem1371163 y)). Qed.
Lemma lem1371165 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371167 : term130 = term130.
Proof. exact (MK_COMB (@lem1371165) (@lem1371164)). Qed.
Lemma lem1371168 (h1 : term17) : term130.
Proof. exact (EQ_MP (@lem1371167) (@lem1371115 h1)). Qed.
Lemma lem1371176 (y : real) (x : real) : (term79 y x) = (term79 y x).
Proof. exact (eq_refl (term79 y x)). Qed.
Lemma lem1371177 (y : real) : (term98 y) = (term98 y).
Proof. exact (fun_ext (fun x : real => @lem1371176 y x)). Qed.
Lemma lem1371178 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371179 (y : real) : (term113 y) = (term113 y).
Proof. exact (MK_COMB (@lem1371178) (@lem1371177 y)). Qed.
Lemma lem1371180 : term120 = term120.
Proof. exact (fun_ext (fun y : real => @lem1371179 y)). Qed.
Lemma lem1371181 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371183 : term135 = term135.
Proof. exact (MK_COMB (@lem1371181) (@lem1371180)). Qed.
Lemma lem1371184 (h1 : term17) : term135.
Proof. exact (EQ_MP (@lem1371183) (@lem1371114 h1)). Qed.
Lemma lem1371185 (_24301 : real) (h1 : term33) : term137 _24301.
Proof. exact (@lem1371140 h1 _24301). Qed.
Lemma lem1371186 (_24301 : real) : (term137 _24301) = (term75 _24301).
Proof. exact (eq_refl (term137 _24301)). Qed.
Lemma lem1371187 (_24301 : real) (h1 : term33) : term75 _24301.
Proof. exact (EQ_MP (@lem1371186 _24301) (@lem1371185 _24301 h1)). Qed.
Lemma lem1371188 (_24301 : real) (_24302 : real) (h1 : term33) : term138 _24301 _24302.
Proof. exact (@lem1371187 _24301 h1 _24302). Qed.
Lemma lem1371189 (_24302 : real) (_24301 : real) : (term138 _24301 _24302) = (term73 _24302 _24301).
Proof. exact (eq_refl (term138 _24301 _24302)). Qed.
Lemma lem1371190 (_24302 : real) (_24301 : real) (h1 : term33) : term73 _24302 _24301.
Proof. exact (EQ_MP (@lem1371189 _24302 _24301) (@lem1371188 _24301 _24302 h1)). Qed.
Lemma lem1371191 (_24302 : real) (_24301 : real) (_24303 : real) (h1 : term33) : term139 _24302 _24301 _24303.
Proof. exact (@lem1371190 _24302 _24301 h1 _24303). Qed.
Lemma lem1371192 (_24302 : real) (_24301 : real) (_24303 : real) : (term139 _24302 _24301 _24303) = (term70 _24302 _24301 _24303).
Proof. exact (eq_refl (term139 _24302 _24301 _24303)). Qed.
Lemma lem1371193 (_24302 : real) (_24301 : real) (_24303 : real) (h1 : term33) : term70 _24302 _24301 _24303.
Proof. exact (EQ_MP (@lem1371192 _24302 _24301 _24303) (@lem1371191 _24302 _24301 _24303 h1)). Qed.
Lemma lem1371194 (_24304 : real) (h1 : term17) : term121 _24304.
Proof. exact (@lem1371168 h1 _24304). Qed.
Lemma lem1371195 (_24304 : real) : (term121 _24304) = (term108 _24304).
Proof. exact (eq_refl (term121 _24304)). Qed.
Lemma lem1371196 (_24304 : real) (h1 : term17) : term108 _24304.
Proof. exact (EQ_MP (@lem1371195 _24304) (@lem1371194 _24304 h1)). Qed.
Lemma lem1371197 (_24304 : real) (_24305 : real) (h1 : term17) : term99 _24304 _24305.
Proof. exact (@lem1371196 _24304 h1 _24305). Qed.
Lemma lem1371198 (_24304 : real) (_24305 : real) : (term99 _24304 _24305) = (term82 _24304 _24305).
Proof. exact (eq_refl (term99 _24304 _24305)). Qed.
Lemma lem1371200 (_24306 : real) (h1 : term17) : term123 _24306.
Proof. exact (@lem1371184 h1 _24306). Qed.
Lemma lem1371201 (_24306 : real) : (term123 _24306) = (term113 _24306).
Proof. exact (eq_refl (term123 _24306)). Qed.
Lemma lem1371202 (_24306 : real) (h1 : term17) : term113 _24306.
Proof. exact (EQ_MP (@lem1371201 _24306) (@lem1371200 _24306 h1)). Qed.
Lemma lem1371203 (_24306 : real) (_24307 : real) (h1 : term17) : term101 _24306 _24307.
Proof. exact (@lem1371202 _24306 h1 _24307). Qed.
Lemma lem1371204 (_24306 : real) (_24307 : real) : (term101 _24306 _24307) = (term79 _24306 _24307).
Proof. exact (eq_refl (term101 _24306 _24307)). Qed.
Lemma lem1371216 (_24302 : real) (_24301 : real) (_24303 : real) : (term70 _24302 _24301 _24303) = (term140 _24302 _24301 _24303).
Proof. exact (@lem1370322 (term23 _24301 _24302) (term23 _24302 _24303) (real_le _24301 _24303)). Qed.
Lemma lem1371217 (_24302 : real) (_24301 : real) (_24303 : real) (h1 : term33) : term140 _24302 _24301 _24303.
Proof. exact (EQ_MP (@lem1371216 _24302 _24301 _24303) (@lem1371193 _24302 _24301 _24303 h1)). Qed.
Lemma lem1371219 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term141 x z.
Proof. exact (proj2 (@lem1371109 y x z h1)). Qed.
Lemma lem1371229 (_24304 : real) (_24305 : real) (h1 : term17) : term82 _24304 _24305.
Proof. exact (EQ_MP (@lem1371198 _24304 _24305) (@lem1371197 _24304 _24305 h1)). Qed.
Lemma lem1371235 (_24306 : real) (_24307 : real) (h1 : term17) : term79 _24306 _24307.
Proof. exact (EQ_MP (@lem1371204 _24306 _24307) (@lem1371203 _24306 _24307 h1)). Qed.
Lemma lem1371237 (y : real) (x : real) (z : real) (h1 : term41 y x z) : real_le x y.
Proof. exact (proj1 (@lem1371111 y x z h1)). Qed.
Lemma lem1371238 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term142 x y.
Proof. exact (fun h0 : term23 x y => @lem1371237 y x z h1). Qed.
Lemma lem1371240 (p : Prop) : (term143 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1371241 (x : real) (y : real) : (term142 x y) = (real_le x y).
Proof. exact (@lem1371240 (real_le x y)). Qed.
Lemma lem1371242 (y : real) (x : real) (z : real) (h1 : term41 y x z) : real_le x y.
Proof. exact (EQ_MP (@lem1371241 x y) (@lem1371238 y x z h1)). Qed.
Lemma lem1371244 (y : real) (x : real) (z : real) (h1 : term41 y x z) : real_lt y z.
Proof. exact (proj2 (@lem1371111 y x z h1)). Qed.
Lemma lem1371245 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term144 y z.
Proof. exact (fun h0 : term141 y z => @lem1371244 y x z h1). Qed.
Lemma lem1371247 (p : Prop) : (term143 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1371248 (y : real) (z : real) : (term144 y z) = (real_lt y z).
Proof. exact (@lem1371247 (real_lt y z)). Qed.
Lemma lem1371249 (y : real) (x : real) (z : real) (h1 : term41 y x z) : real_lt y z.
Proof. exact (EQ_MP (@lem1371248 y z) (@lem1371245 y x z h1)). Qed.
Lemma lem1371255 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1371256 (_24307 : real) (_24306 : real) : (term79 _24306 _24307) = (term145 _24307 _24306).
Proof. exact (@lem1371255 (term23 _24306 _24307) (term141 _24307 _24306)). Qed.
Lemma lem1371262 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1371263 (_24307 : real) (_24306 : real) : (term146 _24306 _24307) = (term147 _24307 _24306).
Proof. exact (MK_COMB (@lem1371262) (@lem1371256 _24307 _24306)). Qed.
Lemma lem1371269 (_24307 : real) (_24306 : real) : (term145 _24307 _24306) = (term145 _24307 _24306).
Proof. exact (eq_refl (term145 _24307 _24306)). Qed.
Lemma lem1371270 (_24307 : real) (_24306 : real) : ((term79 _24306 _24307) = (term145 _24307 _24306)) = ((term145 _24307 _24306) = (term145 _24307 _24306)).
Proof. exact (MK_COMB (@lem1371263 _24307 _24306) (@lem1371269 _24307 _24306)). Qed.
Lemma lem1371272 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1371273 (x : Prop) : (x = x) = True.
Proof. exact (@lem1371272 Prop x). Qed.
Lemma lem1371274 (_24307 : real) (_24306 : real) : ((term145 _24307 _24306) = (term145 _24307 _24306)) = True.
Proof. exact (@lem1371273 (term145 _24307 _24306)). Qed.
Lemma lem1371275 (_24307 : real) (_24306 : real) : ((term79 _24306 _24307) = (term145 _24307 _24306)) = True.
Proof. exact (TRANS (@lem1371270 _24307 _24306) (@lem1371274 _24307 _24306)). Qed.
Lemma lem1371276 (_24307 : real) (_24306 : real) : True = ((term79 _24306 _24307) = (term145 _24307 _24306)).
Proof. exact (SYM (@lem1371275 _24307 _24306)). Qed.
Lemma lem1371277 (_24307 : real) (_24306 : real) : (term79 _24306 _24307) = (term145 _24307 _24306).
Proof. exact (EQ_MP (@lem1371276 _24307 _24306) (@lem0)). Qed.
Lemma lem1371278 (_24307 : real) (_24306 : real) (h1 : term17) : term145 _24307 _24306.
Proof. exact (EQ_MP (@lem1371277 _24307 _24306) (@lem1371235 _24306 _24307 h1)). Qed.
Lemma lem1371280 (b : Prop) (a : Prop) : (a \/ b) = (term148 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1371281 (_24306 : real) (_24307 : real) : (term145 _24307 _24306) = (term149 _24306 _24307).
Proof. exact (@lem1371280 (term141 _24307 _24306) (term23 _24306 _24307)). Qed.
Lemma lem1371283 (a : Prop) : (term150 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1371284 (_24307 : real) (_24306 : real) : (term151 _24307 _24306) = (real_lt _24307 _24306).
Proof. exact (@lem1371283 (real_lt _24307 _24306)). Qed.
Lemma lem1371285 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1371286 (_24307 : real) (_24306 : real) : (term152 _24307 _24306) = (term153 _24307 _24306).
Proof. exact (MK_COMB (@lem1371285) (@lem1371284 _24307 _24306)). Qed.
Lemma lem1371287 (_24306 : real) (_24307 : real) : (term23 _24306 _24307) = (term23 _24306 _24307).
Proof. exact (eq_refl (term23 _24306 _24307)). Qed.
Lemma lem1371288 (_24306 : real) (_24307 : real) : (term149 _24306 _24307) = (term154 _24306 _24307).
Proof. exact (MK_COMB (@lem1371286 _24307 _24306) (@lem1371287 _24306 _24307)). Qed.
Lemma lem1371289 (_24306 : real) (_24307 : real) : (term145 _24307 _24306) = (term154 _24306 _24307).
Proof. exact (TRANS (@lem1371281 _24306 _24307) (@lem1371288 _24306 _24307)). Qed.
Lemma lem1371292 (_24306 : real) (_24307 : real) (h1 : term17) : term154 _24306 _24307.
Proof. exact (EQ_MP (@lem1371289 _24306 _24307) (@lem1371278 _24307 _24306 h1)). Qed.
Lemma lem1371293 (z : real) (y : real) (h1 : term17) : term154 z y.
Proof. exact (@lem1371292 z y h1). Qed.
Lemma lem1371296 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term41 y x z) : term23 z y.
Proof. exact (@lem1371293 z y h1 (@lem1371249 y x z h2)). Qed.
Lemma lem1371297 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term41 y x z) : term155 z y.
Proof. exact (fun h0 : real_le z y => @lem1371296 y x z h1 h2). Qed.
Lemma lem1371299 (p : Prop) : (term156 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1371300 (z : real) (y : real) : (term155 z y) = (term23 z y).
Proof. exact (@lem1371299 (real_le z y)). Qed.
Lemma lem1371301 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term41 y x z) : term23 z y.
Proof. exact (EQ_MP (@lem1371300 z y) (@lem1371297 y x z h1 h2)). Qed.
Lemma lem1371303 (b : Prop) (a : Prop) : (a \/ b) = (term148 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1371304 (_24303 : real) (_24301 : real) (_24302 : real) : (term140 _24302 _24301 _24303) = (term157 _24303 _24301 _24302).
Proof. exact (@lem1371303 (term158 _24302 _24301 _24303) (term23 _24301 _24302)). Qed.
Lemma lem1371306 (a : Prop) (b : Prop) : (term159 a b) = (term160 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1371307 (_24302 : real) (_24301 : real) (_24303 : real) : (term161 _24302 _24301 _24303) = (term162 _24302 _24301 _24303).
Proof. exact (@lem1371306 (term23 _24302 _24303) (real_le _24301 _24303)). Qed.
Lemma lem1371309 (a : Prop) : (term150 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1371310 (_24302 : real) (_24303 : real) : (term78 _24302 _24303) = (real_le _24302 _24303).
Proof. exact (@lem1371309 (real_le _24302 _24303)). Qed.
Lemma lem1371311 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1371312 (_24302 : real) (_24303 : real) : (term163 _24302 _24303) = (term164 _24302 _24303).
Proof. exact (MK_COMB (@lem1371311) (@lem1371310 _24302 _24303)). Qed.
Lemma lem1371313 (_24301 : real) (_24303 : real) : (term23 _24301 _24303) = (term23 _24301 _24303).
Proof. exact (eq_refl (term23 _24301 _24303)). Qed.
Lemma lem1371314 (_24302 : real) (_24301 : real) (_24303 : real) : (term162 _24302 _24301 _24303) = (term165 _24302 _24301 _24303).
Proof. exact (MK_COMB (@lem1371312 _24302 _24303) (@lem1371313 _24301 _24303)). Qed.
Lemma lem1371315 (_24302 : real) (_24301 : real) (_24303 : real) : (term161 _24302 _24301 _24303) = (term165 _24302 _24301 _24303).
Proof. exact (TRANS (@lem1371307 _24302 _24301 _24303) (@lem1371314 _24302 _24301 _24303)). Qed.
Lemma lem1371316 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1371317 (_24302 : real) (_24301 : real) (_24303 : real) : (term166 _24302 _24301 _24303) = (term167 _24302 _24301 _24303).
Proof. exact (MK_COMB (@lem1371316) (@lem1371315 _24302 _24301 _24303)). Qed.
Lemma lem1371318 (_24301 : real) (_24302 : real) : (term23 _24301 _24302) = (term23 _24301 _24302).
Proof. exact (eq_refl (term23 _24301 _24302)). Qed.
Lemma lem1371319 (_24303 : real) (_24301 : real) (_24302 : real) : (term157 _24303 _24301 _24302) = (term168 _24303 _24301 _24302).
Proof. exact (MK_COMB (@lem1371317 _24302 _24301 _24303) (@lem1371318 _24301 _24302)). Qed.
Lemma lem1371320 (_24303 : real) (_24301 : real) (_24302 : real) : (term140 _24302 _24301 _24303) = (term168 _24303 _24301 _24302).
Proof. exact (TRANS (@lem1371304 _24303 _24301 _24302) (@lem1371319 _24303 _24301 _24302)). Qed.
Lemma lem1371322 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term41 y x z) : term165 x z y.
Proof. exact (conj (@lem1371242 y x z h2) (@lem1371301 y x z h1 h2)). Qed.
Lemma lem1371324 (_24303 : real) (_24301 : real) (_24302 : real) (h1 : term33) : term168 _24303 _24301 _24302.
Proof. exact (EQ_MP (@lem1371320 _24303 _24301 _24302) (@lem1371217 _24302 _24301 _24303 h1)). Qed.
Lemma lem1371325 (y : real) (z : real) (x : real) (h1 : term33) : term168 y z x.
Proof. exact (@lem1371324 y z x h1). Qed.
Lemma lem1371328 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : term23 z x.
Proof. exact (@lem1371325 y z x h1 (@lem1371322 y x z h2 h3)). Qed.
Lemma lem1371329 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : term155 z x.
Proof. exact (fun h0 : real_le z x => @lem1371328 y x z h1 h2 h3). Qed.
Lemma lem1371331 (p : Prop) : (term156 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1371332 (z : real) (x : real) : (term155 z x) = (term23 z x).
Proof. exact (@lem1371331 (real_le z x)). Qed.
Lemma lem1371333 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : term23 z x.
Proof. exact (EQ_MP (@lem1371332 z x) (@lem1371329 y x z h1 h2 h3)). Qed.
Lemma lem1371335 (b : Prop) (a : Prop) : (a \/ b) = (term148 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1371338 (_24305 : real) (_24304 : real) : (term82 _24304 _24305) = (term169 _24305 _24304).
Proof. exact (@lem1371335 (real_le _24304 _24305) (real_lt _24305 _24304)). Qed.
Lemma lem1371341 (_24305 : real) (_24304 : real) (h1 : term17) : term169 _24305 _24304.
Proof. exact (EQ_MP (@lem1371338 _24305 _24304) (@lem1371229 _24304 _24305 h1)). Qed.
Lemma lem1371342 (x : real) (z : real) (h1 : term17) : term169 x z.
Proof. exact (@lem1371341 x z h1). Qed.
Lemma lem1371345 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : real_lt x z.
Proof. exact (@lem1371342 x z h2 (@lem1371333 y x z h1 h2 h3)). Qed.
Lemma lem1371346 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : term144 x z.
Proof. exact (fun h0 : term141 x z => @lem1371345 y x z h1 h2 h3). Qed.
Lemma lem1371348 (p : Prop) : (term143 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1371349 (x : real) (z : real) : (term144 x z) = (real_lt x z).
Proof. exact (@lem1371348 (real_lt x z)). Qed.
Lemma lem1371350 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : real_lt x z.
Proof. exact (EQ_MP (@lem1371349 x z) (@lem1371346 y x z h1 h2 h3)). Qed.
Lemma lem1371353 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1371355 (x : real) (z : real) : (term141 x z) = (term170 x z).
Proof. exact (@lem1371353 (real_lt x z)). Qed.
Lemma lem1371358 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term170 x z.
Proof. exact (EQ_MP (@lem1371355 x z) (@lem1371219 y x z h1)). Qed.
Lemma lem1371361 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : False.
Proof. exact (@lem1371358 y x z h3 (@lem1371350 y x z h1 h2 h3)). Qed.
Lemma lem1371362 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : term171.
Proof. exact (fun h0 : ~ False => @lem1371361 y x z h1 h2 h3). Qed.
Lemma lem1371364 (p : Prop) : (term143 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1371365 : term171 = False.
Proof. exact (@lem1371364 False). Qed.
Lemma lem1371366 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : False.
Proof. exact (EQ_MP (@lem1371365) (@lem1371362 y x z h1 h2 h3)). Qed.
Lemma lem1371367 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : (term41 y x z) = False.
Proof. exact (prop_ext (fun h4 : term41 y x z => @lem1371366 y x z h1 h2 h3) (fun h4 : False => @lem1371109 y x z h3)). Qed.
Lemma lem1371368 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term17) (h3 : term41 y x z) : False.
Proof. exact (EQ_MP (@lem1371367 y x z h1 h2 h3) (@lem1371109 y x z h3)). Qed.
Lemma lem1371369 (y : real) (x : real) (h1 : term33) (h2 : term17) (h3 : term51 y x) : False.
Proof. exact (ex_elim (@lem1371003 y x h3) (fun z : real => fun h0 : term50 y x z => @lem1371368 y x z h1 h2 h0)). Qed.
Lemma lem1371370 (x : real) (h1 : term33) (h2 : term17) (h3 : term58 x) : False.
Proof. exact (ex_elim (@lem1371002 x h3) (fun y : real => fun h0 : term57 x y => @lem1371369 y x h1 h2 h0)). Qed.
Lemma lem1371371 (h1 : term33) (h2 : term17) (h3 : term10) : False.
Proof. exact (ex_elim (@lem1370629 h3) (fun x : real => fun h0 : term63 x => @lem1371370 x h1 h2 h0)). Qed.
Lemma lem1371372 (h1 : term33) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1371371 h1 h0 h2). Qed.
Lemma lem1371373 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1371374 (h1 : term33) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem1371373) (@lem1371372 h1 h2)). Qed.
Lemma lem1371375 (h1 : term10) : term20.
Proof. exact (fun h0 : term33 => @lem1371374 h0 h1). Qed.
Lemma lem1371376 : term22.
Proof. exact (fun h0 : term10 => @lem1371375 h0). Qed.
Lemma lem1371377 : term11.
Proof. exact (EQ_MP (@lem1370524) (@lem1371376)). Qed.
Lemma lem1371379 : term11.
Proof. exact (@lem1370342 (@lem1371377)). Qed.
Lemma lem1371380 (h1 : term10) : term19.
Proof. exact (@lem1371379 (@lem1370327 h1)). Qed.
Lemma lem1371381 (h1 : term10) : term15.
Proof. exact (@lem1371380 h1 (@lem1339577)). Qed.
Lemma lem1371382 (h1 : term10) : False.
Proof. exact (@lem1371381 h1 (@lem1341566)). Qed.
Lemma lem1371383 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1371382 h1) (fun h2 : False => @lem1370327 h1)). Qed.
Lemma lem1371384 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1371383 h1) (@lem1370327 h1)). Qed.
Lemma lem1371385 : term9.
Proof. exact (fun h0 : term10 => @lem1371384 h0). Qed.
Lemma lem1371386 : term8.
Proof. exact (EQ_MP (@lem1370326) (@lem1371385)). Qed.
