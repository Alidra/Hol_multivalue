Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_TRANS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_LTE_TRANS_spec.
Require Import REAL_LT_IMP_LE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
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
Require Import thm69_spec.
Lemma lem1371387 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1371388 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1371389 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1371388 t1) (@lem1371387 t1)). Qed.
Lemma lem1371390 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1371389 t1 t2). Qed.
Lemma lem1371391 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1371392 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1371391 t1 t2) (@lem1371390 t1 t2)). Qed.
Lemma lem1371393 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1371392 t1 t2 t3). Qed.
Lemma lem1371394 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1371395 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1371394 t1 t2 t3) (@lem1371393 t1 t2 t3)). Qed.
Lemma lem1371396 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1371395 t1 t2 t3)). Qed.
Lemma lem1371398 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1371399 : term8 = term9.
Proof. exact (@lem1371398 term8). Qed.
Lemma lem1371400 : term9 = term8.
Proof. exact (SYM (@lem1371399)). Qed.
Lemma lem1371401 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1371404 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1371405 : term12.
Proof. exact (fun h0 : term11 => @lem1371404 h0). Qed.
Lemma lem1371406 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1371407 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1371408 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1371406 h2 (@lem1371407 h1)). Qed.
Lemma lem1371409 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1371408 h1 h0). Qed.
Lemma lem1371410 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1371411 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1371409 h1 (@lem1371410 h2)). Qed.
Lemma lem1371412 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1371411 h0 h1). Qed.
Lemma lem1371413 : term14.
Proof. exact (fun h0 : term12 => @lem1371412 h0). Qed.
Lemma lem1371416 : term12.
Proof. exact (@lem1371413 (@lem1371405)). Qed.
Lemma lem1371448 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1371449 : term15 = term16.
Proof. exact (@lem1371448 term17). Qed.
Lemma lem1371466 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1371467 : term19 = term20.
Proof. exact (MK_COMB (@lem1371466) (@lem1371449)). Qed.
Lemma lem1371470 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1371477 : term11 = term22.
Proof. exact (MK_COMB (@lem1371470) (@lem1371467)). Qed.
Lemma lem1371486 (y : real) (x : real) (z : real) : (term23 y x z) = (term23 y x z).
Proof. exact (eq_refl (term23 y x z)). Qed.
Lemma lem1371487 (y : real) (x : real) : (term24 y x) = (term24 y x).
Proof. exact (fun_ext (fun z : real => @lem1371486 y x z)). Qed.
Lemma lem1371488 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371489 (y : real) (x : real) : (term25 y x) = (term25 y x).
Proof. exact (MK_COMB (@lem1371488) (@lem1371487 y x)). Qed.
Lemma lem1371490 (x : real) : (term26 x) = (term26 x).
Proof. exact (fun_ext (fun y : real => @lem1371489 y x)). Qed.
Lemma lem1371491 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371492 (x : real) : (term27 x) = (term27 x).
Proof. exact (MK_COMB (@lem1371491) (@lem1371490 x)). Qed.
Lemma lem1371493 : term28 = term28.
Proof. exact (fun_ext (fun x : real => @lem1371492 x)). Qed.
Lemma lem1371494 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371495 : term17 = term17.
Proof. exact (MK_COMB (@lem1371494) (@lem1371493)). Qed.
Lemma lem1371496 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1371497 : term16 = term16.
Proof. exact (MK_COMB (@lem1371496) (@lem1371495)). Qed.
Lemma lem1371502 (x : real) (y : real) : (term29 x y) = (term29 x y).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem1371503 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1371502 x y)). Qed.
Lemma lem1371504 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371505 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1371504) (@lem1371503 x)). Qed.
Lemma lem1371506 : term32 = term32.
Proof. exact (fun_ext (fun x : real => @lem1371505 x)). Qed.
Lemma lem1371507 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371508 : term33 = term33.
Proof. exact (MK_COMB (@lem1371507) (@lem1371506)). Qed.
Lemma lem1371509 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1371510 : term18 = term18.
Proof. exact (MK_COMB (@lem1371509) (@lem1371508)). Qed.
Lemma lem1371511 : term20 = term20.
Proof. exact (MK_COMB (@lem1371510) (@lem1371497)). Qed.
Lemma lem1371520 (y : real) (x : real) (z : real) : (term34 y x z) = (term34 y x z).
Proof. exact (eq_refl (term34 y x z)). Qed.
Lemma lem1371521 (y : real) (x : real) : (term35 y x) = (term35 y x).
Proof. exact (fun_ext (fun z : real => @lem1371520 y x z)). Qed.
Lemma lem1371522 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371523 (y : real) (x : real) : (term36 y x) = (term36 y x).
Proof. exact (MK_COMB (@lem1371522) (@lem1371521 y x)). Qed.
Lemma lem1371524 (x : real) : (term37 x) = (term37 x).
Proof. exact (fun_ext (fun y : real => @lem1371523 y x)). Qed.
Lemma lem1371525 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371526 (x : real) : (term38 x) = (term38 x).
Proof. exact (MK_COMB (@lem1371525) (@lem1371524 x)). Qed.
Lemma lem1371527 : term39 = term39.
Proof. exact (fun_ext (fun x : real => @lem1371526 x)). Qed.
Lemma lem1371528 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371529 : term8 = term8.
Proof. exact (MK_COMB (@lem1371528) (@lem1371527)). Qed.
Lemma lem1371530 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1371531 : term10 = term10.
Proof. exact (MK_COMB (@lem1371530) (@lem1371529)). Qed.
Lemma lem1371532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1371533 : term21 = term21.
Proof. exact (MK_COMB (@lem1371532) (@lem1371531)). Qed.
Lemma lem1371534 : term22 = term22.
Proof. exact (MK_COMB (@lem1371533) (@lem1371511)). Qed.
Lemma lem1371599 : term11 = term22.
Proof. exact (TRANS (@lem1371477) (@lem1371534)). Qed.
Lemma lem1371600 : term22 = term11.
Proof. exact (SYM (@lem1371599)). Qed.
Lemma lem1371601 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1371602 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1371603 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1371614 (y : real) (x : real) (z : real) : (term40 y x z) = (term41 y x z).
Proof. exact (@lem17362 (term42 x y z) (real_lt x z)). Qed.
Lemma lem1371615 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1371616 (y : real) (x : real) : (term45 y x) = (term46 y x).
Proof. exact (@lem1371615 (term35 y x)). Qed.
Lemma lem1371617 (y : real) (x : real) (z : real) : (term47 y x z) = (term34 y x z).
Proof. exact (eq_refl (term47 y x z)). Qed.
Lemma lem1371618 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1371619 (y : real) (x : real) (z : real) : (term48 y x z) = (term40 y x z).
Proof. exact (MK_COMB (@lem1371618) (@lem1371617 y x z)). Qed.
Lemma lem1371620 (y : real) (x : real) (z : real) : (term48 y x z) = (term41 y x z).
Proof. exact (TRANS (@lem1371619 y x z) (@lem1371614 y x z)). Qed.
Lemma lem1371621 (y : real) (x : real) : (term49 y x) = (term50 y x).
Proof. exact (fun_ext (fun z : real => @lem1371620 y x z)). Qed.
Lemma lem1371622 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1371623 (y : real) (x : real) : (term46 y x) = (term51 y x).
Proof. exact (MK_COMB (@lem1371622) (@lem1371621 y x)). Qed.
Lemma lem1371624 (y : real) (x : real) : (term45 y x) = (term51 y x).
Proof. exact (TRANS (@lem1371616 y x) (@lem1371623 y x)). Qed.
Lemma lem1371625 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1371626 (x : real) : (term52 x) = (term53 x).
Proof. exact (@lem1371625 (term37 x)). Qed.
Lemma lem1371627 (y : real) (x : real) : (term54 x y) = (term36 y x).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem1371628 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1371629 (y : real) (x : real) : (term55 x y) = (term45 y x).
Proof. exact (MK_COMB (@lem1371628) (@lem1371627 y x)). Qed.
Lemma lem1371630 (y : real) (x : real) : (term55 x y) = (term51 y x).
Proof. exact (TRANS (@lem1371629 y x) (@lem1371624 y x)). Qed.
Lemma lem1371631 (x : real) : (term56 x) = (term57 x).
Proof. exact (fun_ext (fun y : real => @lem1371630 y x)). Qed.
Lemma lem1371632 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1371633 (x : real) : (term53 x) = (term58 x).
Proof. exact (MK_COMB (@lem1371632) (@lem1371631 x)). Qed.
Lemma lem1371634 (x : real) : (term52 x) = (term58 x).
Proof. exact (TRANS (@lem1371626 x) (@lem1371633 x)). Qed.
Lemma lem1371635 (P : real -> Prop) : (term43 P) = (term44 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1371636 : term10 = term59.
Proof. exact (@lem1371635 term39). Qed.
Lemma lem1371637 (x : real) : (term60 x) = (term38 x).
Proof. exact (eq_refl (term60 x)). Qed.
Lemma lem1371638 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1371639 (x : real) : (term61 x) = (term52 x).
Proof. exact (MK_COMB (@lem1371638) (@lem1371637 x)). Qed.
Lemma lem1371640 (x : real) : (term61 x) = (term58 x).
Proof. exact (TRANS (@lem1371639 x) (@lem1371634 x)). Qed.
Lemma lem1371641 : term62 = term63.
Proof. exact (fun_ext (fun x : real => @lem1371640 x)). Qed.
Lemma lem1371642 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1371643 : term59 = term64.
Proof. exact (MK_COMB (@lem1371642) (@lem1371641)). Qed.
Lemma lem1371704 : term10 = term64.
Proof. exact (TRANS (@lem1371636) (@lem1371643)). Qed.
Lemma lem1371705 (h1 : term10) : term64.
Proof. exact (EQ_MP (@lem1371704) (@lem1371601 h1)). Qed.
Lemma lem1371712 (x : real) (y : real) : (term29 x y) = (term65 x y).
Proof. exact (@lem17265 (real_lt x y) (real_le x y)). Qed.
Lemma lem1371713 (x : real) : (term30 x) = (term66 x).
Proof. exact (fun_ext (fun y : real => @lem1371712 x y)). Qed.
Lemma lem1371714 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371715 (x : real) : (term31 x) = (term67 x).
Proof. exact (MK_COMB (@lem1371714) (@lem1371713 x)). Qed.
Lemma lem1371716 : term32 = term68.
Proof. exact (fun_ext (fun x : real => @lem1371715 x)). Qed.
Lemma lem1371717 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371774 : term33 = term69.
Proof. exact (MK_COMB (@lem1371717) (@lem1371716)). Qed.
Lemma lem1371775 (h1 : term33) : term69.
Proof. exact (EQ_MP (@lem1371774) (@lem1371602 h1)). Qed.
Lemma lem1371782 (x : real) (y : real) (z : real) : (term70 x y z) = (term71 x y z).
Proof. exact (@lem17045 (real_lt x y) (real_le y z)). Qed.
Lemma lem1371783 (x : real) (z : real) : (real_lt x z) = (real_lt x z).
Proof. exact (eq_refl (real_lt x z)). Qed.
Lemma lem1371784 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1371785 (x : real) (y : real) (z : real) : (term72 x y z) = (term73 x y z).
Proof. exact (MK_COMB (@lem1371784) (@lem1371782 x y z)). Qed.
Lemma lem1371786 (y : real) (x : real) (z : real) : (term74 y x z) = (term75 y x z).
Proof. exact (MK_COMB (@lem1371785 x y z) (@lem1371783 x z)). Qed.
Lemma lem1371787 (y : real) (x : real) (z : real) : (term23 y x z) = (term74 y x z).
Proof. exact (@lem17265 (term76 x y z) (real_lt x z)). Qed.
Lemma lem1371788 (y : real) (x : real) (z : real) : (term23 y x z) = (term75 y x z).
Proof. exact (TRANS (@lem1371787 y x z) (@lem1371786 y x z)). Qed.
Lemma lem1371789 (y : real) (x : real) : (term24 y x) = (term77 y x).
Proof. exact (fun_ext (fun z : real => @lem1371788 y x z)). Qed.
Lemma lem1371790 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371791 (y : real) (x : real) : (term25 y x) = (term78 y x).
Proof. exact (MK_COMB (@lem1371790) (@lem1371789 y x)). Qed.
Lemma lem1371792 (x : real) : (term26 x) = (term79 x).
Proof. exact (fun_ext (fun y : real => @lem1371791 y x)). Qed.
Lemma lem1371793 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371794 (x : real) : (term27 x) = (term80 x).
Proof. exact (MK_COMB (@lem1371793) (@lem1371792 x)). Qed.
Lemma lem1371795 : term28 = term81.
Proof. exact (fun_ext (fun x : real => @lem1371794 x)). Qed.
Lemma lem1371796 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371857 : term17 = term82.
Proof. exact (MK_COMB (@lem1371796) (@lem1371795)). Qed.
Lemma lem1371858 (h1 : term17) : term82.
Proof. exact (EQ_MP (@lem1371857) (@lem1371603 h1)). Qed.
Lemma lem1371859 (x : real) (h1 : term58 x) : term58 x.
Proof. exact (h1). Qed.
Lemma lem1371860 (y : real) (x : real) (h1 : term51 y x) : term51 y x.
Proof. exact (h1). Qed.
Lemma lem1371876 (x : real) (y : real) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1371877 (x : real) : (term66 x) = (term66 x).
Proof. exact (fun_ext (fun y : real => @lem1371876 x y)). Qed.
Lemma lem1371878 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371879 (x : real) : (term67 x) = (term67 x).
Proof. exact (MK_COMB (@lem1371878) (@lem1371877 x)). Qed.
Lemma lem1371880 : term68 = term68.
Proof. exact (fun_ext (fun x : real => @lem1371879 x)). Qed.
Lemma lem1371881 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371882 : term69 = term69.
Proof. exact (MK_COMB (@lem1371881) (@lem1371880)). Qed.
Lemma lem1371883 (h1 : term33) : term69.
Proof. exact (EQ_MP (@lem1371882) (@lem1371775 h1)). Qed.
Lemma lem1371908 (y : real) (x : real) (z : real) : (term75 y x z) = (term75 y x z).
Proof. exact (eq_refl (term75 y x z)). Qed.
Lemma lem1371909 (y : real) (x : real) : (term77 y x) = (term77 y x).
Proof. exact (fun_ext (fun z : real => @lem1371908 y x z)). Qed.
Lemma lem1371910 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371911 (y : real) (x : real) : (term78 y x) = (term78 y x).
Proof. exact (MK_COMB (@lem1371910) (@lem1371909 y x)). Qed.
Lemma lem1371912 (x : real) : (term79 x) = (term79 x).
Proof. exact (fun_ext (fun y : real => @lem1371911 y x)). Qed.
Lemma lem1371913 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371914 (x : real) : (term80 x) = (term80 x).
Proof. exact (MK_COMB (@lem1371913) (@lem1371912 x)). Qed.
Lemma lem1371915 : term81 = term81.
Proof. exact (fun_ext (fun x : real => @lem1371914 x)). Qed.
Lemma lem1371916 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371917 : term82 = term82.
Proof. exact (MK_COMB (@lem1371916) (@lem1371915)). Qed.
Lemma lem1371918 (h1 : term17) : term82.
Proof. exact (EQ_MP (@lem1371917) (@lem1371858 h1)). Qed.
Lemma lem1371942 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term41 y x z.
Proof. exact (h1). Qed.
Lemma lem1371944 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term42 x y z.
Proof. exact (proj1 (@lem1371942 y x z h1)). Qed.
Lemma lem1371954 (x : real) (y : real) : (term65 x y) = (term65 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1371955 (x : real) : (term66 x) = (term66 x).
Proof. exact (fun_ext (fun y : real => @lem1371954 x y)). Qed.
Lemma lem1371956 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371957 (x : real) : (term67 x) = (term67 x).
Proof. exact (MK_COMB (@lem1371956) (@lem1371955 x)). Qed.
Lemma lem1371958 : term68 = term68.
Proof. exact (fun_ext (fun x : real => @lem1371957 x)). Qed.
Lemma lem1371959 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371961 : term69 = term69.
Proof. exact (MK_COMB (@lem1371959) (@lem1371958)). Qed.
Lemma lem1371962 (h1 : term33) : term69.
Proof. exact (EQ_MP (@lem1371961) (@lem1371883 h1)). Qed.
Lemma lem1371976 (y : real) (x : real) (z : real) : (term75 y x z) = (term75 y x z).
Proof. exact (eq_refl (term75 y x z)). Qed.
Lemma lem1371977 (y : real) (x : real) : (term77 y x) = (term77 y x).
Proof. exact (fun_ext (fun z : real => @lem1371976 y x z)). Qed.
Lemma lem1371978 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371979 (y : real) (x : real) : (term78 y x) = (term78 y x).
Proof. exact (MK_COMB (@lem1371978) (@lem1371977 y x)). Qed.
Lemma lem1371980 (x : real) : (term79 x) = (term79 x).
Proof. exact (fun_ext (fun y : real => @lem1371979 y x)). Qed.
Lemma lem1371981 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371982 (x : real) : (term80 x) = (term80 x).
Proof. exact (MK_COMB (@lem1371981) (@lem1371980 x)). Qed.
Lemma lem1371983 : term81 = term81.
Proof. exact (fun_ext (fun x : real => @lem1371982 x)). Qed.
Lemma lem1371984 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1371986 : term82 = term82.
Proof. exact (MK_COMB (@lem1371984) (@lem1371983)). Qed.
Lemma lem1371987 (h1 : term17) : term82.
Proof. exact (EQ_MP (@lem1371986) (@lem1371918 h1)). Qed.
Lemma lem1372000 (_24308 : real) (h1 : term33) : term83 _24308.
Proof. exact (@lem1371962 h1 _24308). Qed.
Lemma lem1372001 (_24308 : real) : (term83 _24308) = (term67 _24308).
Proof. exact (eq_refl (term83 _24308)). Qed.
Lemma lem1372002 (_24308 : real) (h1 : term33) : term67 _24308.
Proof. exact (EQ_MP (@lem1372001 _24308) (@lem1372000 _24308 h1)). Qed.
Lemma lem1372003 (_24308 : real) (_24309 : real) (h1 : term33) : term84 _24308 _24309.
Proof. exact (@lem1372002 _24308 h1 _24309). Qed.
Lemma lem1372004 (_24308 : real) (_24309 : real) : (term84 _24308 _24309) = (term65 _24308 _24309).
Proof. exact (eq_refl (term84 _24308 _24309)). Qed.
Lemma lem1372006 (_24310 : real) (h1 : term17) : term85 _24310.
Proof. exact (@lem1371987 h1 _24310). Qed.
Lemma lem1372007 (_24310 : real) : (term85 _24310) = (term80 _24310).
Proof. exact (eq_refl (term85 _24310)). Qed.
Lemma lem1372008 (_24310 : real) (h1 : term17) : term80 _24310.
Proof. exact (EQ_MP (@lem1372007 _24310) (@lem1372006 _24310 h1)). Qed.
Lemma lem1372009 (_24310 : real) (_24311 : real) (h1 : term17) : term86 _24310 _24311.
Proof. exact (@lem1372008 _24310 h1 _24311). Qed.
Lemma lem1372010 (_24311 : real) (_24310 : real) : (term86 _24310 _24311) = (term78 _24311 _24310).
Proof. exact (eq_refl (term86 _24310 _24311)). Qed.
Lemma lem1372011 (_24311 : real) (_24310 : real) (h1 : term17) : term78 _24311 _24310.
Proof. exact (EQ_MP (@lem1372010 _24311 _24310) (@lem1372009 _24310 _24311 h1)). Qed.
Lemma lem1372012 (_24311 : real) (_24310 : real) (_24312 : real) (h1 : term17) : term87 _24311 _24310 _24312.
Proof. exact (@lem1372011 _24311 _24310 h1 _24312). Qed.
Lemma lem1372013 (_24311 : real) (_24310 : real) (_24312 : real) : (term87 _24311 _24310 _24312) = (term75 _24311 _24310 _24312).
Proof. exact (eq_refl (term87 _24311 _24310 _24312)). Qed.
Lemma lem1372014 (_24311 : real) (_24310 : real) (_24312 : real) (h1 : term17) : term75 _24311 _24310 _24312.
Proof. exact (EQ_MP (@lem1372013 _24311 _24310 _24312) (@lem1372012 _24311 _24310 _24312 h1)). Qed.
Lemma lem1372020 (_24308 : real) (_24309 : real) (h1 : term33) : term65 _24308 _24309.
Proof. exact (EQ_MP (@lem1372004 _24308 _24309) (@lem1372003 _24308 _24309 h1)). Qed.
Lemma lem1372031 (_24311 : real) (_24310 : real) (_24312 : real) : (term75 _24311 _24310 _24312) = (term88 _24311 _24310 _24312).
Proof. exact (@lem1371396 (term89 _24310 _24311) (term90 _24311 _24312) (real_lt _24310 _24312)). Qed.
Lemma lem1372032 (_24311 : real) (_24310 : real) (_24312 : real) (h1 : term17) : term88 _24311 _24310 _24312.
Proof. exact (EQ_MP (@lem1372031 _24311 _24310 _24312) (@lem1372014 _24311 _24310 _24312 h1)). Qed.
Lemma lem1372034 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term89 x z.
Proof. exact (proj2 (@lem1371942 y x z h1)). Qed.
Lemma lem1372040 (y : real) (x : real) (z : real) (h1 : term41 y x z) : real_lt x y.
Proof. exact (proj1 (@lem1371944 y x z h1)). Qed.
Lemma lem1372041 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term91 x y.
Proof. exact (fun h0 : term89 x y => @lem1372040 y x z h1). Qed.
Lemma lem1372043 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1372044 (x : real) (y : real) : (term91 x y) = (real_lt x y).
Proof. exact (@lem1372043 (real_lt x y)). Qed.
Lemma lem1372045 (y : real) (x : real) (z : real) (h1 : term41 y x z) : real_lt x y.
Proof. exact (EQ_MP (@lem1372044 x y) (@lem1372041 y x z h1)). Qed.
Lemma lem1372047 (y : real) (x : real) (z : real) (h1 : term41 y x z) : real_lt y z.
Proof. exact (proj2 (@lem1371944 y x z h1)). Qed.
Lemma lem1372048 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term91 y z.
Proof. exact (fun h0 : term89 y z => @lem1372047 y x z h1). Qed.
Lemma lem1372050 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1372051 (y : real) (z : real) : (term91 y z) = (real_lt y z).
Proof. exact (@lem1372050 (real_lt y z)). Qed.
Lemma lem1372052 (y : real) (x : real) (z : real) (h1 : term41 y x z) : real_lt y z.
Proof. exact (EQ_MP (@lem1372051 y z) (@lem1372048 y x z h1)). Qed.
Lemma lem1372058 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1372059 (_24308 : real) (_24309 : real) : (term65 _24308 _24309) = (term93 _24308 _24309).
Proof. exact (@lem1372058 (real_le _24308 _24309) (term89 _24308 _24309)). Qed.
Lemma lem1372065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1372066 (_24308 : real) (_24309 : real) : (term94 _24308 _24309) = (term95 _24308 _24309).
Proof. exact (MK_COMB (@lem1372065) (@lem1372059 _24308 _24309)). Qed.
Lemma lem1372072 (_24308 : real) (_24309 : real) : (term93 _24308 _24309) = (term93 _24308 _24309).
Proof. exact (eq_refl (term93 _24308 _24309)). Qed.
Lemma lem1372073 (_24308 : real) (_24309 : real) : ((term65 _24308 _24309) = (term93 _24308 _24309)) = ((term93 _24308 _24309) = (term93 _24308 _24309)).
Proof. exact (MK_COMB (@lem1372066 _24308 _24309) (@lem1372072 _24308 _24309)). Qed.
Lemma lem1372075 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1372076 (x : Prop) : (x = x) = True.
Proof. exact (@lem1372075 Prop x). Qed.
Lemma lem1372077 (_24308 : real) (_24309 : real) : ((term93 _24308 _24309) = (term93 _24308 _24309)) = True.
Proof. exact (@lem1372076 (term93 _24308 _24309)). Qed.
Lemma lem1372078 (_24308 : real) (_24309 : real) : ((term65 _24308 _24309) = (term93 _24308 _24309)) = True.
Proof. exact (TRANS (@lem1372073 _24308 _24309) (@lem1372077 _24308 _24309)). Qed.
Lemma lem1372079 (_24308 : real) (_24309 : real) : True = ((term65 _24308 _24309) = (term93 _24308 _24309)).
Proof. exact (SYM (@lem1372078 _24308 _24309)). Qed.
Lemma lem1372080 (_24308 : real) (_24309 : real) : (term65 _24308 _24309) = (term93 _24308 _24309).
Proof. exact (EQ_MP (@lem1372079 _24308 _24309) (@lem0)). Qed.
Lemma lem1372081 (_24308 : real) (_24309 : real) (h1 : term33) : term93 _24308 _24309.
Proof. exact (EQ_MP (@lem1372080 _24308 _24309) (@lem1372020 _24308 _24309 h1)). Qed.
Lemma lem1372083 (b : Prop) (a : Prop) : (a \/ b) = (term96 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1372084 (_24308 : real) (_24309 : real) : (term93 _24308 _24309) = (term97 _24308 _24309).
Proof. exact (@lem1372083 (term89 _24308 _24309) (real_le _24308 _24309)). Qed.
Lemma lem1372086 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1372087 (_24308 : real) (_24309 : real) : (term99 _24308 _24309) = (real_lt _24308 _24309).
Proof. exact (@lem1372086 (real_lt _24308 _24309)). Qed.
Lemma lem1372088 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1372089 (_24308 : real) (_24309 : real) : (term100 _24308 _24309) = (term101 _24308 _24309).
Proof. exact (MK_COMB (@lem1372088) (@lem1372087 _24308 _24309)). Qed.
Lemma lem1372090 (_24308 : real) (_24309 : real) : (real_le _24308 _24309) = (real_le _24308 _24309).
Proof. exact (eq_refl (real_le _24308 _24309)). Qed.
Lemma lem1372091 (_24308 : real) (_24309 : real) : (term97 _24308 _24309) = (term29 _24308 _24309).
Proof. exact (MK_COMB (@lem1372089 _24308 _24309) (@lem1372090 _24308 _24309)). Qed.
Lemma lem1372092 (_24308 : real) (_24309 : real) : (term93 _24308 _24309) = (term29 _24308 _24309).
Proof. exact (TRANS (@lem1372084 _24308 _24309) (@lem1372091 _24308 _24309)). Qed.
Lemma lem1372095 (_24308 : real) (_24309 : real) (h1 : term33) : term29 _24308 _24309.
Proof. exact (EQ_MP (@lem1372092 _24308 _24309) (@lem1372081 _24308 _24309 h1)). Qed.
Lemma lem1372096 (y : real) (z : real) (h1 : term33) : term29 y z.
Proof. exact (@lem1372095 y z h1). Qed.
Lemma lem1372099 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term41 y x z) : real_le y z.
Proof. exact (@lem1372096 y z h1 (@lem1372052 y x z h2)). Qed.
Lemma lem1372100 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term41 y x z) : term102 y z.
Proof. exact (fun h0 : term90 y z => @lem1372099 y x z h1 h2). Qed.
Lemma lem1372102 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1372103 (y : real) (z : real) : (term102 y z) = (real_le y z).
Proof. exact (@lem1372102 (real_le y z)). Qed.
Lemma lem1372104 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term41 y x z) : real_le y z.
Proof. exact (EQ_MP (@lem1372103 y z) (@lem1372100 y x z h1 h2)). Qed.
Lemma lem1372110 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1372111 (_24311 : real) (_24310 : real) (_24312 : real) : (term88 _24311 _24310 _24312) = (term103 _24311 _24310 _24312).
Proof. exact (@lem1372110 (term90 _24311 _24312) (term89 _24310 _24311) (real_lt _24310 _24312)). Qed.
Lemma lem1372125 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1372126 (_24312 : real) (_24310 : real) (_24311 : real) : (term104 _24311 _24310 _24312) = (term105 _24312 _24310 _24311).
Proof. exact (@lem1372125 (real_lt _24310 _24312) (term89 _24310 _24311)). Qed.
Lemma lem1372132 (_24311 : real) (_24312 : real) : (term106 _24311 _24312) = (term106 _24311 _24312).
Proof. exact (eq_refl (term106 _24311 _24312)). Qed.
Lemma lem1372133 (_24312 : real) (_24310 : real) (_24311 : real) : (term103 _24311 _24310 _24312) = (term107 _24312 _24310 _24311).
Proof. exact (MK_COMB (@lem1372132 _24311 _24312) (@lem1372126 _24312 _24310 _24311)). Qed.
Lemma lem1372137 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1372138 (_24312 : real) (_24310 : real) (_24311 : real) : (term107 _24312 _24310 _24311) = (term108 _24312 _24310 _24311).
Proof. exact (@lem1372137 (real_lt _24310 _24312) (term90 _24311 _24312) (term89 _24310 _24311)). Qed.
Lemma lem1372154 (_24312 : real) (_24310 : real) (_24311 : real) : (term103 _24311 _24310 _24312) = (term108 _24312 _24310 _24311).
Proof. exact (TRANS (@lem1372133 _24312 _24310 _24311) (@lem1372138 _24312 _24310 _24311)). Qed.
Lemma lem1372155 (_24312 : real) (_24310 : real) (_24311 : real) : (term88 _24311 _24310 _24312) = (term108 _24312 _24310 _24311).
Proof. exact (TRANS (@lem1372111 _24311 _24310 _24312) (@lem1372154 _24312 _24310 _24311)). Qed.
Lemma lem1372156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1372157 (_24312 : real) (_24310 : real) (_24311 : real) : (term109 _24311 _24310 _24312) = (term110 _24312 _24310 _24311).
Proof. exact (MK_COMB (@lem1372156) (@lem1372155 _24312 _24310 _24311)). Qed.
Lemma lem1372171 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1372172 (_24312 : real) (_24310 : real) (_24311 : real) : (term71 _24310 _24311 _24312) = (term111 _24312 _24310 _24311).
Proof. exact (@lem1372171 (term90 _24311 _24312) (term89 _24310 _24311)). Qed.
Lemma lem1372178 (_24310 : real) (_24312 : real) : (term112 _24310 _24312) = (term112 _24310 _24312).
Proof. exact (eq_refl (term112 _24310 _24312)). Qed.
Lemma lem1372179 (_24312 : real) (_24310 : real) (_24311 : real) : (term113 _24310 _24311 _24312) = (term108 _24312 _24310 _24311).
Proof. exact (MK_COMB (@lem1372178 _24310 _24312) (@lem1372172 _24312 _24310 _24311)). Qed.
Lemma lem1372190 (_24312 : real) (_24310 : real) (_24311 : real) : ((term88 _24311 _24310 _24312) = (term113 _24310 _24311 _24312)) = ((term108 _24312 _24310 _24311) = (term108 _24312 _24310 _24311)).
Proof. exact (MK_COMB (@lem1372157 _24312 _24310 _24311) (@lem1372179 _24312 _24310 _24311)). Qed.
Lemma lem1372192 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1372193 (x : Prop) : (x = x) = True.
Proof. exact (@lem1372192 Prop x). Qed.
Lemma lem1372194 (_24312 : real) (_24310 : real) (_24311 : real) : ((term108 _24312 _24310 _24311) = (term108 _24312 _24310 _24311)) = True.
Proof. exact (@lem1372193 (term108 _24312 _24310 _24311)). Qed.
Lemma lem1372195 (_24310 : real) (_24311 : real) (_24312 : real) : ((term88 _24311 _24310 _24312) = (term113 _24310 _24311 _24312)) = True.
Proof. exact (TRANS (@lem1372190 _24312 _24310 _24311) (@lem1372194 _24312 _24310 _24311)). Qed.
Lemma lem1372196 (_24310 : real) (_24311 : real) (_24312 : real) : True = ((term88 _24311 _24310 _24312) = (term113 _24310 _24311 _24312)).
Proof. exact (SYM (@lem1372195 _24310 _24311 _24312)). Qed.
Lemma lem1372197 (_24310 : real) (_24311 : real) (_24312 : real) : (term88 _24311 _24310 _24312) = (term113 _24310 _24311 _24312).
Proof. exact (EQ_MP (@lem1372196 _24310 _24311 _24312) (@lem0)). Qed.
Lemma lem1372198 (_24310 : real) (_24311 : real) (_24312 : real) (h1 : term17) : term113 _24310 _24311 _24312.
Proof. exact (EQ_MP (@lem1372197 _24310 _24311 _24312) (@lem1372032 _24311 _24310 _24312 h1)). Qed.
Lemma lem1372200 (b : Prop) (a : Prop) : (a \/ b) = (term96 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1372201 (_24311 : real) (_24310 : real) (_24312 : real) : (term113 _24310 _24311 _24312) = (term114 _24311 _24310 _24312).
Proof. exact (@lem1372200 (term71 _24310 _24311 _24312) (real_lt _24310 _24312)). Qed.
Lemma lem1372203 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1372204 (_24310 : real) (_24311 : real) (_24312 : real) : (term117 _24310 _24311 _24312) = (term118 _24310 _24311 _24312).
Proof. exact (@lem1372203 (term89 _24310 _24311) (term90 _24311 _24312)). Qed.
Lemma lem1372206 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1372207 (_24310 : real) (_24311 : real) : (term99 _24310 _24311) = (real_lt _24310 _24311).
Proof. exact (@lem1372206 (real_lt _24310 _24311)). Qed.
Lemma lem1372208 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1372209 (_24310 : real) (_24311 : real) : (term119 _24310 _24311) = (term120 _24310 _24311).
Proof. exact (MK_COMB (@lem1372208) (@lem1372207 _24310 _24311)). Qed.
Lemma lem1372211 (a : Prop) : (term98 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1372212 (_24311 : real) (_24312 : real) : (term121 _24311 _24312) = (real_le _24311 _24312).
Proof. exact (@lem1372211 (real_le _24311 _24312)). Qed.
Lemma lem1372213 (_24310 : real) (_24311 : real) (_24312 : real) : (term118 _24310 _24311 _24312) = (term76 _24310 _24311 _24312).
Proof. exact (MK_COMB (@lem1372209 _24310 _24311) (@lem1372212 _24311 _24312)). Qed.
Lemma lem1372214 (_24310 : real) (_24311 : real) (_24312 : real) : (term117 _24310 _24311 _24312) = (term76 _24310 _24311 _24312).
Proof. exact (TRANS (@lem1372204 _24310 _24311 _24312) (@lem1372213 _24310 _24311 _24312)). Qed.
Lemma lem1372215 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1372216 (_24310 : real) (_24311 : real) (_24312 : real) : (term122 _24310 _24311 _24312) = (term123 _24310 _24311 _24312).
Proof. exact (MK_COMB (@lem1372215) (@lem1372214 _24310 _24311 _24312)). Qed.
Lemma lem1372217 (_24310 : real) (_24312 : real) : (real_lt _24310 _24312) = (real_lt _24310 _24312).
Proof. exact (eq_refl (real_lt _24310 _24312)). Qed.
Lemma lem1372218 (_24311 : real) (_24310 : real) (_24312 : real) : (term114 _24311 _24310 _24312) = (term23 _24311 _24310 _24312).
Proof. exact (MK_COMB (@lem1372216 _24310 _24311 _24312) (@lem1372217 _24310 _24312)). Qed.
Lemma lem1372219 (_24311 : real) (_24310 : real) (_24312 : real) : (term113 _24310 _24311 _24312) = (term23 _24311 _24310 _24312).
Proof. exact (TRANS (@lem1372201 _24311 _24310 _24312) (@lem1372218 _24311 _24310 _24312)). Qed.
Lemma lem1372221 (y : real) (x : real) (z : real) (h1 : term33) (h2 : term41 y x z) : term76 x y z.
Proof. exact (conj (@lem1372045 y x z h2) (@lem1372104 y x z h1 h2)). Qed.
Lemma lem1372223 (_24311 : real) (_24310 : real) (_24312 : real) (h1 : term17) : term23 _24311 _24310 _24312.
Proof. exact (EQ_MP (@lem1372219 _24311 _24310 _24312) (@lem1372198 _24310 _24311 _24312 h1)). Qed.
Lemma lem1372224 (y : real) (x : real) (z : real) (h1 : term17) : term23 y x z.
Proof. exact (@lem1372223 y x z h1). Qed.
Lemma lem1372227 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term33) (h3 : term41 y x z) : real_lt x z.
Proof. exact (@lem1372224 y x z h1 (@lem1372221 y x z h2 h3)). Qed.
Lemma lem1372228 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term33) (h3 : term41 y x z) : term91 x z.
Proof. exact (fun h0 : term89 x z => @lem1372227 y x z h1 h2 h3). Qed.
Lemma lem1372230 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1372231 (x : real) (z : real) : (term91 x z) = (real_lt x z).
Proof. exact (@lem1372230 (real_lt x z)). Qed.
Lemma lem1372232 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term33) (h3 : term41 y x z) : real_lt x z.
Proof. exact (EQ_MP (@lem1372231 x z) (@lem1372228 y x z h1 h2 h3)). Qed.
Lemma lem1372235 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1372237 (x : real) (z : real) : (term89 x z) = (term124 x z).
Proof. exact (@lem1372235 (real_lt x z)). Qed.
Lemma lem1372240 (y : real) (x : real) (z : real) (h1 : term41 y x z) : term124 x z.
Proof. exact (EQ_MP (@lem1372237 x z) (@lem1372034 y x z h1)). Qed.
Lemma lem1372243 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term33) (h3 : term41 y x z) : False.
Proof. exact (@lem1372240 y x z h3 (@lem1372232 y x z h1 h2 h3)). Qed.
Lemma lem1372244 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term33) (h3 : term41 y x z) : term125.
Proof. exact (fun h0 : ~ False => @lem1372243 y x z h1 h2 h3). Qed.
Lemma lem1372246 (p : Prop) : (term92 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1372247 : term125 = False.
Proof. exact (@lem1372246 False). Qed.
Lemma lem1372248 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term33) (h3 : term41 y x z) : False.
Proof. exact (EQ_MP (@lem1372247) (@lem1372244 y x z h1 h2 h3)). Qed.
Lemma lem1372249 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term33) (h3 : term41 y x z) : (term41 y x z) = False.
Proof. exact (prop_ext (fun h4 : term41 y x z => @lem1372248 y x z h1 h2 h3) (fun h4 : False => @lem1371942 y x z h3)). Qed.
Lemma lem1372250 (y : real) (x : real) (z : real) (h1 : term17) (h2 : term33) (h3 : term41 y x z) : False.
Proof. exact (EQ_MP (@lem1372249 y x z h1 h2 h3) (@lem1371942 y x z h3)). Qed.
Lemma lem1372251 (y : real) (x : real) (h1 : term17) (h2 : term33) (h3 : term51 y x) : False.
Proof. exact (ex_elim (@lem1371860 y x h3) (fun z : real => fun h0 : term50 y x z => @lem1372250 y x z h1 h2 h0)). Qed.
Lemma lem1372252 (x : real) (h1 : term17) (h2 : term33) (h3 : term58 x) : False.
Proof. exact (ex_elim (@lem1371859 x h3) (fun y : real => fun h0 : term57 x y => @lem1372251 y x h1 h2 h0)). Qed.
Lemma lem1372253 (h1 : term17) (h2 : term33) (h3 : term10) : False.
Proof. exact (ex_elim (@lem1371705 h3) (fun x : real => fun h0 : term63 x => @lem1372252 x h1 h2 h0)). Qed.
Lemma lem1372254 (h1 : term33) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1372253 h0 h1 h2). Qed.
Lemma lem1372255 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1372256 (h1 : term33) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem1372255) (@lem1372254 h1 h2)). Qed.
Lemma lem1372257 (h1 : term10) : term20.
Proof. exact (fun h0 : term33 => @lem1372256 h0 h1). Qed.
Lemma lem1372258 : term22.
Proof. exact (fun h0 : term10 => @lem1372257 h0). Qed.
Lemma lem1372259 : term11.
Proof. exact (EQ_MP (@lem1371600) (@lem1372258)). Qed.
Lemma lem1372261 : term11.
Proof. exact (@lem1371416 (@lem1372259)). Qed.
Lemma lem1372262 (h1 : term10) : term19.
Proof. exact (@lem1372261 (@lem1371401 h1)). Qed.
Lemma lem1372263 (h1 : term10) : term15.
Proof. exact (@lem1372262 h1 (@lem1369133)). Qed.
Lemma lem1372264 (h1 : term10) : False.
Proof. exact (@lem1372263 h1 (@lem1370312)). Qed.
Lemma lem1372265 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1372264 h1) (fun h2 : False => @lem1371401 h1)). Qed.
Lemma lem1372266 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1372265 h1) (@lem1371401 h1)). Qed.
Lemma lem1372267 : term9.
Proof. exact (fun h0 : term10 => @lem1372266 h0). Qed.
Lemma lem1372268 : term8.
Proof. exact (EQ_MP (@lem1371400) (@lem1372267)). Qed.
