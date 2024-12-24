Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LTE_ANTISYM_term_abbrevs.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem1373470 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1373471 : term1 = term2.
Proof. exact (@lem1373470 term1). Qed.
Lemma lem1373472 : term2 = term1.
Proof. exact (SYM (@lem1373471)). Qed.
Lemma lem1373473 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1373476 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1373477 : term5.
Proof. exact (fun h0 : term4 => @lem1373476 h0). Qed.
Lemma lem1373478 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1373479 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1373480 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1373478 h2 (@lem1373479 h1)). Qed.
Lemma lem1373481 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1373480 h1 h0). Qed.
Lemma lem1373482 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1373483 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1373481 h1 (@lem1373482 h2)). Qed.
Lemma lem1373484 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1373483 h0 h1). Qed.
Lemma lem1373485 : term7.
Proof. exact (fun h0 : term5 => @lem1373484 h0). Qed.
Lemma lem1373488 : term5.
Proof. exact (@lem1373485 (@lem1373477)). Qed.
Lemma lem1373502 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1373503 : term8 = term9.
Proof. exact (@lem1373502 term10). Qed.
Lemma lem1373512 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1373519 : term4 = term12.
Proof. exact (MK_COMB (@lem1373512) (@lem1373503)). Qed.
Lemma lem1373526 (y : real) (x : real) : ((real_lt x y) = (term13 y x)) = ((real_lt x y) = (term13 y x)).
Proof. exact (eq_refl ((real_lt x y) = (term13 y x))). Qed.
Lemma lem1373527 (y : real) : (term14 y) = (term14 y).
Proof. exact (fun_ext (fun x : real => @lem1373526 y x)). Qed.
Lemma lem1373528 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1373529 (y : real) : (term15 y) = (term15 y).
Proof. exact (MK_COMB (@lem1373528) (@lem1373527 y)). Qed.
Lemma lem1373530 : term16 = term16.
Proof. exact (fun_ext (fun y : real => @lem1373529 y)). Qed.
Lemma lem1373531 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1373532 : term10 = term10.
Proof. exact (MK_COMB (@lem1373531) (@lem1373530)). Qed.
Lemma lem1373533 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1373534 : term9 = term9.
Proof. exact (MK_COMB (@lem1373533) (@lem1373532)). Qed.
Lemma lem1373541 (y : real) (x : real) : (term17 y x) = (term17 y x).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem1373542 (x : real) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1373541 y x)). Qed.
Lemma lem1373543 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1373544 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem1373543) (@lem1373542 x)). Qed.
Lemma lem1373545 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1373544 x)). Qed.
Lemma lem1373546 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1373547 : term1 = term1.
Proof. exact (MK_COMB (@lem1373546) (@lem1373545)). Qed.
Lemma lem1373548 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1373549 : term3 = term3.
Proof. exact (MK_COMB (@lem1373548) (@lem1373547)). Qed.
Lemma lem1373550 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1373551 : term11 = term11.
Proof. exact (MK_COMB (@lem1373550) (@lem1373549)). Qed.
Lemma lem1373552 : term12 = term12.
Proof. exact (MK_COMB (@lem1373551) (@lem1373534)). Qed.
Lemma lem1373583 : term4 = term12.
Proof. exact (TRANS (@lem1373519) (@lem1373552)). Qed.
Lemma lem1373584 : term12 = term4.
Proof. exact (SYM (@lem1373583)). Qed.
Lemma lem1373585 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1373586 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1373593 (y : real) (x : real) : (term21 y x) = (term22 y x).
Proof. exact (@lem16933 (term22 y x)). Qed.
Lemma lem1373594 (P : real -> Prop) : (term23 P) = (term24 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1373595 (x : real) : (term25 x) = (term26 x).
Proof. exact (@lem1373594 (term18 x)). Qed.
Lemma lem1373596 (y : real) (x : real) : (term27 x y) = (term17 y x).
Proof. exact (eq_refl (term27 x y)). Qed.
Lemma lem1373597 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1373598 (y : real) (x : real) : (term28 x y) = (term21 y x).
Proof. exact (MK_COMB (@lem1373597) (@lem1373596 y x)). Qed.
Lemma lem1373599 (y : real) (x : real) : (term28 x y) = (term22 y x).
Proof. exact (TRANS (@lem1373598 y x) (@lem1373593 y x)). Qed.
Lemma lem1373600 (x : real) : (term29 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1373599 y x)). Qed.
Lemma lem1373601 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1373602 (x : real) : (term26 x) = (term31 x).
Proof. exact (MK_COMB (@lem1373601) (@lem1373600 x)). Qed.
Lemma lem1373603 (x : real) : (term25 x) = (term31 x).
Proof. exact (TRANS (@lem1373595 x) (@lem1373602 x)). Qed.
Lemma lem1373604 (P : real -> Prop) : (term23 P) = (term24 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1373605 : term3 = term32.
Proof. exact (@lem1373604 term20). Qed.
Lemma lem1373606 (x : real) : (term33 x) = (term19 x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem1373607 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1373608 (x : real) : (term34 x) = (term25 x).
Proof. exact (MK_COMB (@lem1373607) (@lem1373606 x)). Qed.
Lemma lem1373609 (x : real) : (term34 x) = (term31 x).
Proof. exact (TRANS (@lem1373608 x) (@lem1373603 x)). Qed.
Lemma lem1373610 : term35 = term36.
Proof. exact (fun_ext (fun x : real => @lem1373609 x)). Qed.
Lemma lem1373611 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1373612 : term32 = term37.
Proof. exact (MK_COMB (@lem1373611) (@lem1373610)). Qed.
Lemma lem1373669 : term3 = term37.
Proof. exact (TRANS (@lem1373605) (@lem1373612)). Qed.
Lemma lem1373670 (h1 : term3) : term37.
Proof. exact (EQ_MP (@lem1373669) (@lem1373585 h1)). Qed.
Lemma lem1373676 (y : real) (x : real) : (term38 y x) = (real_le y x).
Proof. exact (@lem16933 (real_le y x)). Qed.
Lemma lem1373679 (y : real) (x : real) : (term39 y x) = (term39 y x).
Proof. exact (eq_refl (term39 y x)). Qed.
Lemma lem1373681 (x : real) (y : real) : (term40 x y) = (term40 x y).
Proof. exact (eq_refl (term40 x y)). Qed.
Lemma lem1373682 (y : real) (x : real) : (term41 y x) = (term42 y x).
Proof. exact (MK_COMB (@lem1373681 x y) (@lem1373676 y x)). Qed.
Lemma lem1373683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1373684 (y : real) (x : real) : (term43 y x) = (term44 y x).
Proof. exact (MK_COMB (@lem1373683) (@lem1373682 y x)). Qed.
Lemma lem1373685 (y : real) (x : real) : (term45 y x) = (term46 y x).
Proof. exact (MK_COMB (@lem1373684 y x) (@lem1373679 y x)). Qed.
Lemma lem1373686 (y : real) (x : real) : ((real_lt x y) = (term13 y x)) = (term45 y x).
Proof. exact (@lem17784 (real_lt x y) (term13 y x)). Qed.
Lemma lem1373687 (y : real) (x : real) : ((real_lt x y) = (term13 y x)) = (term46 y x).
Proof. exact (TRANS (@lem1373686 y x) (@lem1373685 y x)). Qed.
Lemma lem1373688 (y : real) : (term14 y) = (term47 y).
Proof. exact (fun_ext (fun x : real => @lem1373687 y x)). Qed.
Lemma lem1373689 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1373690 (y : real) : (term15 y) = (term48 y).
Proof. exact (MK_COMB (@lem1373689) (@lem1373688 y)). Qed.
Lemma lem1373691 : term16 = term49.
Proof. exact (fun_ext (fun y : real => @lem1373690 y)). Qed.
Lemma lem1373692 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1373693 : term10 = term50.
Proof. exact (MK_COMB (@lem1373692) (@lem1373691)). Qed.
Lemma lem1373699 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term51 A P Q) = (term52 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1373700 (P : real -> Prop) (Q : real -> Prop) : (term53 P Q) = (term54 P Q).
Proof. exact (@lem1373699 real P Q). Qed.
Lemma lem1373701 (y : real) : (term55 y) = (term56 y).
Proof. exact (@lem1373700 (term57 y) (term58 y)). Qed.
Lemma lem1373702 (y : real) (x : real) : (term59 y x) = (term42 y x).
Proof. exact (eq_refl (term59 y x)). Qed.
Lemma lem1373703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1373704 (y : real) (x : real) : (term60 y x) = (term44 y x).
Proof. exact (MK_COMB (@lem1373703) (@lem1373702 y x)). Qed.
Lemma lem1373705 (y : real) (x : real) : (term61 y x) = (term39 y x).
Proof. exact (eq_refl (term61 y x)). Qed.
Lemma lem1373706 (y : real) (x : real) : (term62 y x) = (term46 y x).
Proof. exact (MK_COMB (@lem1373704 y x) (@lem1373705 y x)). Qed.
Lemma lem1373707 (y : real) : (term63 y) = (term47 y).
Proof. exact (fun_ext (fun x : real => @lem1373706 y x)). Qed.
Lemma lem1373708 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1373709 (y : real) : (term55 y) = (term48 y).
Proof. exact (MK_COMB (@lem1373708) (@lem1373707 y)). Qed.
Lemma lem1373710 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1373711 (y : real) : (term64 y) = (term65 y).
Proof. exact (MK_COMB (@lem1373710) (@lem1373709 y)). Qed.
Lemma lem1373712 (y : real) (x : real) : (term59 y x) = (term42 y x).
Proof. exact (eq_refl (term59 y x)). Qed.
Lemma lem1373713 (y : real) : (term66 y) = (term57 y).
Proof. exact (fun_ext (fun x : real => @lem1373712 y x)). Qed.
Lemma lem1373714 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1373715 (y : real) : (term67 y) = (term68 y).
Proof. exact (MK_COMB (@lem1373714) (@lem1373713 y)). Qed.
Lemma lem1373716 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1373717 (y : real) : (term69 y) = (term70 y).
Proof. exact (MK_COMB (@lem1373716) (@lem1373715 y)). Qed.
Lemma lem1373718 (y : real) (x : real) : (term61 y x) = (term39 y x).
Proof. exact (eq_refl (term61 y x)). Qed.
Lemma lem1373719 (y : real) : (term71 y) = (term58 y).
Proof. exact (fun_ext (fun x : real => @lem1373718 y x)). Qed.
Lemma lem1373720 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1373721 (y : real) : (term72 y) = (term73 y).
Proof. exact (MK_COMB (@lem1373720) (@lem1373719 y)). Qed.
Lemma lem1373722 (y : real) : (term56 y) = (term74 y).
Proof. exact (MK_COMB (@lem1373717 y) (@lem1373721 y)). Qed.
Lemma lem1373723 (y : real) : ((term55 y) = (term56 y)) = ((term48 y) = (term74 y)).
Proof. exact (MK_COMB (@lem1373711 y) (@lem1373722 y)). Qed.
Lemma lem1373724 (y : real) : (term48 y) = (term74 y).
Proof. exact (EQ_MP (@lem1373723 y) (@lem1373701 y)). Qed.
Lemma lem1373821 : term49 = term75.
Proof. exact (fun_ext (fun y : real => @lem1373724 y)). Qed.
Lemma lem1373822 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1373823 : term50 = term76.
Proof. exact (MK_COMB (@lem1373822) (@lem1373821)). Qed.
Lemma lem1373825 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term51 A P Q) = (term52 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1373826 (P : real -> Prop) (Q : real -> Prop) : (term53 P Q) = (term54 P Q).
Proof. exact (@lem1373825 real P Q). Qed.
Lemma lem1373827 : term77 = term78.
Proof. exact (@lem1373826 term79 term80). Qed.
Lemma lem1373828 (y : real) : (term81 y) = (term68 y).
Proof. exact (eq_refl (term81 y)). Qed.
Lemma lem1373829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1373830 (y : real) : (term82 y) = (term70 y).
Proof. exact (MK_COMB (@lem1373829) (@lem1373828 y)). Qed.
Lemma lem1373831 (y : real) : (term83 y) = (term73 y).
Proof. exact (eq_refl (term83 y)). Qed.
Lemma lem1373832 (y : real) : (term84 y) = (term74 y).
Proof. exact (MK_COMB (@lem1373830 y) (@lem1373831 y)). Qed.
Lemma lem1373833 : term85 = term75.
Proof. exact (fun_ext (fun y : real => @lem1373832 y)). Qed.
Lemma lem1373834 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1373835 : term77 = term76.
Proof. exact (MK_COMB (@lem1373834) (@lem1373833)). Qed.
Lemma lem1373836 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1373837 : term86 = term87.
Proof. exact (MK_COMB (@lem1373836) (@lem1373835)). Qed.
Lemma lem1373838 (y : real) : (term81 y) = (term68 y).
Proof. exact (eq_refl (term81 y)). Qed.
Lemma lem1373839 : term88 = term79.
Proof. exact (fun_ext (fun y : real => @lem1373838 y)). Qed.
Lemma lem1373840 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1373841 : term89 = term90.
Proof. exact (MK_COMB (@lem1373840) (@lem1373839)). Qed.
Lemma lem1373842 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1373843 : term91 = term92.
Proof. exact (MK_COMB (@lem1373842) (@lem1373841)). Qed.
Lemma lem1373844 (y : real) : (term83 y) = (term73 y).
Proof. exact (eq_refl (term83 y)). Qed.
Lemma lem1373845 : term93 = term80.
Proof. exact (fun_ext (fun y : real => @lem1373844 y)). Qed.
Lemma lem1373846 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1373847 : term94 = term95.
Proof. exact (MK_COMB (@lem1373846) (@lem1373845)). Qed.
Lemma lem1373848 : term78 = term96.
Proof. exact (MK_COMB (@lem1373843) (@lem1373847)). Qed.
Lemma lem1373849 : (term77 = term78) = (term76 = term96).
Proof. exact (MK_COMB (@lem1373837) (@lem1373848)). Qed.
Lemma lem1373850 : term76 = term96.
Proof. exact (EQ_MP (@lem1373849) (@lem1373827)). Qed.
Lemma lem1373957 : term50 = term96.
Proof. exact (TRANS (@lem1373823) (@lem1373850)). Qed.
Lemma lem1373958 : term10 = term96.
Proof. exact (TRANS (@lem1373693) (@lem1373957)). Qed.
Lemma lem1373959 (h1 : term10) : term96.
Proof. exact (EQ_MP (@lem1373958) (@lem1373586 h1)). Qed.
Lemma lem1373960 (x : real) (h1 : term31 x) : term31 x.
Proof. exact (h1). Qed.
Lemma lem1373978 (y : real) (x : real) : (term39 y x) = (term39 y x).
Proof. exact (eq_refl (term39 y x)). Qed.
Lemma lem1373979 (y : real) : (term58 y) = (term58 y).
Proof. exact (fun_ext (fun x : real => @lem1373978 y x)). Qed.
Lemma lem1373980 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1373981 (y : real) : (term73 y) = (term73 y).
Proof. exact (MK_COMB (@lem1373980) (@lem1373979 y)). Qed.
Lemma lem1373982 : term80 = term80.
Proof. exact (fun_ext (fun y : real => @lem1373981 y)). Qed.
Lemma lem1373983 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1373984 : term95 = term95.
Proof. exact (MK_COMB (@lem1373983) (@lem1373982)). Qed.
Lemma lem1373997 (y : real) (x : real) : (term42 y x) = (term42 y x).
Proof. exact (eq_refl (term42 y x)). Qed.
Lemma lem1373998 (y : real) : (term57 y) = (term57 y).
Proof. exact (fun_ext (fun x : real => @lem1373997 y x)). Qed.
Lemma lem1373999 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374000 (y : real) : (term68 y) = (term68 y).
Proof. exact (MK_COMB (@lem1373999) (@lem1373998 y)). Qed.
Lemma lem1374001 : term79 = term79.
Proof. exact (fun_ext (fun y : real => @lem1374000 y)). Qed.
Lemma lem1374002 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374003 : term90 = term90.
Proof. exact (MK_COMB (@lem1374002) (@lem1374001)). Qed.
Lemma lem1374004 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1374005 : term92 = term92.
Proof. exact (MK_COMB (@lem1374004) (@lem1374003)). Qed.
Lemma lem1374006 : term96 = term96.
Proof. exact (MK_COMB (@lem1374005) (@lem1373984)). Qed.
Lemma lem1374007 (h1 : term10) : term96.
Proof. exact (EQ_MP (@lem1374006) (@lem1373959 h1)). Qed.
Lemma lem1374021 (y : real) (x : real) (h1 : term22 y x) : term22 y x.
Proof. exact (h1). Qed.
Lemma lem1374024 (h1 : term10) : term95.
Proof. exact (proj2 (@lem1374007 h1)). Qed.
Lemma lem1374057 (y : real) (x : real) : (term39 y x) = (term39 y x).
Proof. exact (eq_refl (term39 y x)). Qed.
Lemma lem1374058 (y : real) : (term58 y) = (term58 y).
Proof. exact (fun_ext (fun x : real => @lem1374057 y x)). Qed.
Lemma lem1374059 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374060 (y : real) : (term73 y) = (term73 y).
Proof. exact (MK_COMB (@lem1374059) (@lem1374058 y)). Qed.
Lemma lem1374061 : term80 = term80.
Proof. exact (fun_ext (fun y : real => @lem1374060 y)). Qed.
Lemma lem1374062 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374064 : term95 = term95.
Proof. exact (MK_COMB (@lem1374062) (@lem1374061)). Qed.
Lemma lem1374065 (h1 : term10) : term95.
Proof. exact (EQ_MP (@lem1374064) (@lem1374024 h1)). Qed.
Lemma lem1374072 (_24334 : real) (h1 : term10) : term83 _24334.
Proof. exact (@lem1374065 h1 _24334). Qed.
Lemma lem1374073 (_24334 : real) : (term83 _24334) = (term73 _24334).
Proof. exact (eq_refl (term83 _24334)). Qed.
Lemma lem1374074 (_24334 : real) (h1 : term10) : term73 _24334.
Proof. exact (EQ_MP (@lem1374073 _24334) (@lem1374072 _24334 h1)). Qed.
Lemma lem1374075 (_24334 : real) (_24335 : real) (h1 : term10) : term61 _24334 _24335.
Proof. exact (@lem1374074 _24334 h1 _24335). Qed.
Lemma lem1374076 (_24334 : real) (_24335 : real) : (term61 _24334 _24335) = (term39 _24334 _24335).
Proof. exact (eq_refl (term61 _24334 _24335)). Qed.
Lemma lem1374093 (_24334 : real) (_24335 : real) (h1 : term10) : term39 _24334 _24335.
Proof. exact (EQ_MP (@lem1374076 _24334 _24335) (@lem1374075 _24334 _24335 h1)). Qed.
Lemma lem1374095 (y : real) (x : real) (h1 : term22 y x) : real_lt x y.
Proof. exact (proj1 (@lem1374021 y x h1)). Qed.
Lemma lem1374096 (y : real) (x : real) (h1 : term22 y x) : term97 x y.
Proof. exact (fun h0 : term98 x y => @lem1374095 y x h1). Qed.
Lemma lem1374098 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1374099 (x : real) (y : real) : (term97 x y) = (real_lt x y).
Proof. exact (@lem1374098 (real_lt x y)). Qed.
Lemma lem1374100 (y : real) (x : real) (h1 : term22 y x) : real_lt x y.
Proof. exact (EQ_MP (@lem1374099 x y) (@lem1374096 y x h1)). Qed.
Lemma lem1374102 (y : real) (x : real) (h1 : term22 y x) : real_le y x.
Proof. exact (proj2 (@lem1374021 y x h1)). Qed.
Lemma lem1374103 (y : real) (x : real) (h1 : term22 y x) : term100 y x.
Proof. exact (fun h0 : term13 y x => @lem1374102 y x h1). Qed.
Lemma lem1374105 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1374106 (y : real) (x : real) : (term100 y x) = (real_le y x).
Proof. exact (@lem1374105 (real_le y x)). Qed.
Lemma lem1374107 (y : real) (x : real) (h1 : term22 y x) : real_le y x.
Proof. exact (EQ_MP (@lem1374106 y x) (@lem1374103 y x h1)). Qed.
Lemma lem1374109 (a : Prop) (b : Prop) : (term101 a b) = (term102 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem1374110 (_24334 : real) (_24335 : real) : (term39 _24334 _24335) = (term17 _24334 _24335).
Proof. exact (@lem1374109 (real_lt _24335 _24334) (real_le _24334 _24335)). Qed.
Lemma lem1374112 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1374113 (_24334 : real) (_24335 : real) : (term17 _24334 _24335) = (term103 _24334 _24335).
Proof. exact (@lem1374112 (term22 _24334 _24335)). Qed.
Lemma lem1374114 (_24334 : real) (_24335 : real) : (term39 _24334 _24335) = (term103 _24334 _24335).
Proof. exact (TRANS (@lem1374110 _24334 _24335) (@lem1374113 _24334 _24335)). Qed.
Lemma lem1374116 (y : real) (x : real) (h1 : term22 y x) : term22 y x.
Proof. exact (conj (@lem1374100 y x h1) (@lem1374107 y x h1)). Qed.
Lemma lem1374118 (_24334 : real) (_24335 : real) (h1 : term10) : term103 _24334 _24335.
Proof. exact (EQ_MP (@lem1374114 _24334 _24335) (@lem1374093 _24334 _24335 h1)). Qed.
Lemma lem1374119 (y : real) (x : real) (h1 : term10) : term103 y x.
Proof. exact (@lem1374118 y x h1). Qed.
Lemma lem1374122 (y : real) (x : real) (h1 : term10) (h2 : term22 y x) : False.
Proof. exact (@lem1374119 y x h1 (@lem1374116 y x h2)). Qed.
Lemma lem1374123 (y : real) (x : real) (h1 : term10) (h2 : term22 y x) : term104.
Proof. exact (fun h0 : ~ False => @lem1374122 y x h1 h2). Qed.
Lemma lem1374125 (p : Prop) : (term99 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1374126 : term104 = False.
Proof. exact (@lem1374125 False). Qed.
Lemma lem1374127 (y : real) (x : real) (h1 : term10) (h2 : term22 y x) : False.
Proof. exact (EQ_MP (@lem1374126) (@lem1374123 y x h1 h2)). Qed.
Lemma lem1374128 (y : real) (x : real) (h1 : term10) (h2 : term22 y x) : (term22 y x) = False.
Proof. exact (prop_ext (fun h3 : term22 y x => @lem1374127 y x h1 h2) (fun h3 : False => @lem1374021 y x h2)). Qed.
Lemma lem1374129 (y : real) (x : real) (h1 : term10) (h2 : term22 y x) : False.
Proof. exact (EQ_MP (@lem1374128 y x h1 h2) (@lem1374021 y x h2)). Qed.
Lemma lem1374130 (x : real) (h1 : term10) (h2 : term31 x) : False.
Proof. exact (ex_elim (@lem1373960 x h2) (fun y : real => fun h0 : term30 x y => @lem1374129 y x h1 h0)). Qed.
Lemma lem1374131 (h1 : term10) (h2 : term3) : False.
Proof. exact (ex_elim (@lem1373670 h2) (fun x : real => fun h0 : term36 x => @lem1374130 x h1 h0)). Qed.
Lemma lem1374132 (h1 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1374131 h0 h1). Qed.
Lemma lem1374133 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1374134 (h1 : term3) : term9.
Proof. exact (EQ_MP (@lem1374133) (@lem1374132 h1)). Qed.
Lemma lem1374135 : term12.
Proof. exact (fun h0 : term3 => @lem1374134 h0). Qed.
Lemma lem1374136 : term4.
Proof. exact (EQ_MP (@lem1373584) (@lem1374135)). Qed.
Lemma lem1374138 : term4.
Proof. exact (@lem1373488 (@lem1374136)). Qed.
Lemma lem1374139 (h1 : term3) : term8.
Proof. exact (@lem1374138 (@lem1373473 h1)). Qed.
Lemma lem1374140 (h1 : term3) : False.
Proof. exact (@lem1374139 h1 (@lem1341566)). Qed.
Lemma lem1374141 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1374140 h1) (fun h2 : False => @lem1373473 h1)). Qed.
Lemma lem1374142 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1374141 h1) (@lem1373473 h1)). Qed.
Lemma lem1374143 : term2.
Proof. exact (fun h0 : term3 => @lem1374142 h0). Qed.
Lemma lem1374144 : term1.
Proof. exact (EQ_MP (@lem1373472) (@lem1374143)). Qed.
