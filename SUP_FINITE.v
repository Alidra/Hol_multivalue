Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUP_FINITE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SUP_spec.
Require Import SUP_FINITE_LEMMA_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339379_spec.
Require Import thm1339697_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem5140311 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5140312 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5140313 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5140312 t1) (@lem5140311 t1)). Qed.
Lemma lem5140314 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5140313 t1 t2). Qed.
Lemma lem5140315 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5140316 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5140315 t1 t2) (@lem5140314 t1 t2)). Qed.
Lemma lem5140317 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5140316 t1 t2 t3). Qed.
Lemma lem5140318 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5140319 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5140318 t1 t2 t3) (@lem5140317 t1 t2 t3)). Qed.
Lemma lem5140320 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5140319 t1 t2 t3)). Qed.
Lemma lem5140321 (s : real -> Prop) : term7 s.
Proof. exact (@lem5140310 s). Qed.
Lemma lem5140322 (s : real -> Prop) : (term7 s) = (term8 s).
Proof. exact (eq_refl (term7 s)). Qed.
Lemma lem5140324 (s : real -> Prop) (h1 : term9 s) : term9 s.
Proof. exact (h1). Qed.
Lemma lem5140326 (s : real -> Prop) : term8 s.
Proof. exact (EQ_MP (@lem5140322 s) (@lem5140321 s)). Qed.
Lemma lem5140327 (s : real -> Prop) (h1 : term9 s) : term10 s.
Proof. exact (@lem5140326 s (@lem5140324 s h1)). Qed.
Lemma lem5140329 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5140330 (s : real -> Prop) : (term12 s) = (term13 s).
Proof. exact (@lem5140329 (term12 s)). Qed.
Lemma lem5140331 (s : real -> Prop) : (term13 s) = (term12 s).
Proof. exact (SYM (@lem5140330 s)). Qed.
Lemma lem5140332 (s : real -> Prop) (h1 : term14 s) : term14 s.
Proof. exact (h1). Qed.
Lemma lem5140335 (s : real -> Prop) (h1 : term15 s) : term15 s.
Proof. exact (h1). Qed.
Lemma lem5140336 (s : real -> Prop) : term16 s.
Proof. exact (fun h0 : term15 s => @lem5140335 s h0). Qed.
Lemma lem5140337 (s : real -> Prop) (h1 : term16 s) : term16 s.
Proof. exact (h1). Qed.
Lemma lem5140338 (s : real -> Prop) (h1 : term15 s) : term15 s.
Proof. exact (h1). Qed.
Lemma lem5140339 (s : real -> Prop) (h1 : term15 s) (h2 : term16 s) : term15 s.
Proof. exact (@lem5140337 s h2 (@lem5140338 s h1)). Qed.
Lemma lem5140340 (s : real -> Prop) (h1 : term15 s) : term17 s.
Proof. exact (fun h0 : term16 s => @lem5140339 s h1 h0). Qed.
Lemma lem5140341 (s : real -> Prop) (h1 : term16 s) : term16 s.
Proof. exact (h1). Qed.
Lemma lem5140342 (s : real -> Prop) (h1 : term15 s) (h2 : term16 s) : term15 s.
Proof. exact (@lem5140340 s h1 (@lem5140341 s h2)). Qed.
Lemma lem5140343 (s : real -> Prop) (h1 : term16 s) : term16 s.
Proof. exact (fun h0 : term15 s => @lem5140342 s h0 h1). Qed.
Lemma lem5140344 (s : real -> Prop) : term18 s.
Proof. exact (fun h0 : term16 s => @lem5140343 s h0). Qed.
Lemma lem5140347 (s : real -> Prop) : term16 s.
Proof. exact (@lem5140344 s (@lem5140336 s)). Qed.
Lemma lem5140521 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5140522 : term19 = term20.
Proof. exact (@lem5140521 term21). Qed.
Lemma lem5140533 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem5140534 : term23 = term24.
Proof. exact (MK_COMB (@lem5140533) (@lem5140522)). Qed.
Lemma lem5140537 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem5140538 : term26 = term27.
Proof. exact (MK_COMB (@lem5140537) (@lem5140534)). Qed.
Lemma lem5140541 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5140542 (s : real -> Prop) : (term29 s) = (term30 s).
Proof. exact (MK_COMB (@lem5140541 s) (@lem5140538)). Qed.
Lemma lem5140545 (s : real -> Prop) : (term31 s) = (term31 s).
Proof. exact (eq_refl (term31 s)). Qed.
Lemma lem5140546 (s : real -> Prop) : (term15 s) = (term32 s).
Proof. exact (MK_COMB (@lem5140545 s) (@lem5140542 s)). Qed.
Lemma lem5140549 : term33 = term34.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5140546 s)). Qed.
Lemma lem5140550 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5140559 : term35 = term36.
Proof. exact (MK_COMB (@lem5140550) (@lem5140549)). Qed.
Lemma lem5140568 (x : real) (y : real) : ((term37 y x) = (x = y)) = ((term37 y x) = (x = y)).
Proof. exact (eq_refl ((term37 y x) = (x = y))). Qed.
Lemma lem5140569 (x : real) : (term38 x) = (term38 x).
Proof. exact (fun_ext (fun y : real => @lem5140568 x y)). Qed.
Lemma lem5140570 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5140571 (x : real) : (term39 x) = (term39 x).
Proof. exact (MK_COMB (@lem5140570) (@lem5140569 x)). Qed.
Lemma lem5140572 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem5140571 x)). Qed.
Lemma lem5140573 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5140574 : term21 = term21.
Proof. exact (MK_COMB (@lem5140573) (@lem5140572)). Qed.
Lemma lem5140575 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5140576 : term20 = term20.
Proof. exact (MK_COMB (@lem5140575) (@lem5140574)). Qed.
Lemma lem5140581 (y : real) (x : real) : (term41 y x) = (term41 y x).
Proof. exact (eq_refl (term41 y x)). Qed.
Lemma lem5140582 (x : real) : (term42 x) = (term42 x).
Proof. exact (fun_ext (fun y : real => @lem5140581 y x)). Qed.
Lemma lem5140583 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5140584 (x : real) : (term43 x) = (term43 x).
Proof. exact (MK_COMB (@lem5140583) (@lem5140582 x)). Qed.
Lemma lem5140585 : term44 = term44.
Proof. exact (fun_ext (fun x : real => @lem5140584 x)). Qed.
Lemma lem5140586 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5140587 : term45 = term45.
Proof. exact (MK_COMB (@lem5140586) (@lem5140585)). Qed.
Lemma lem5140588 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5140589 : term22 = term22.
Proof. exact (MK_COMB (@lem5140588) (@lem5140587)). Qed.
Lemma lem5140590 : term24 = term24.
Proof. exact (MK_COMB (@lem5140589) (@lem5140576)). Qed.
Lemma lem5140591 (s : real -> Prop) (b : real) : (term46 s b) = (term46 s b).
Proof. exact (eq_refl (term46 s b)). Qed.
Lemma lem5140596 (s : real -> Prop) (x : real) (b : real) : (term47 s x b) = (term47 s x b).
Proof. exact (eq_refl (term47 s x b)). Qed.
Lemma lem5140597 (s : real -> Prop) (b : real) : (term48 s b) = (term48 s b).
Proof. exact (fun_ext (fun x : real => @lem5140596 s x b)). Qed.
Lemma lem5140598 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5140599 (s : real -> Prop) (b : real) : (term49 s b) = (term49 s b).
Proof. exact (MK_COMB (@lem5140598) (@lem5140597 s b)). Qed.
Lemma lem5140600 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5140601 (s : real -> Prop) (b : real) : (term50 s b) = (term50 s b).
Proof. exact (MK_COMB (@lem5140600) (@lem5140599 s b)). Qed.
Lemma lem5140602 (s : real -> Prop) (b : real) : (term51 s b) = (term51 s b).
Proof. exact (MK_COMB (@lem5140601 s b) (@lem5140591 s b)). Qed.
Lemma lem5140603 (s : real -> Prop) : (term52 s) = (term52 s).
Proof. exact (fun_ext (fun b : real => @lem5140602 s b)). Qed.
Lemma lem5140604 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5140605 (s : real -> Prop) : (term53 s) = (term53 s).
Proof. exact (MK_COMB (@lem5140604) (@lem5140603 s)). Qed.
Lemma lem5140610 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5140611 (s : real -> Prop) : (term55 s) = (term55 s).
Proof. exact (fun_ext (fun x : real => @lem5140610 x s)). Qed.
Lemma lem5140612 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5140613 (s : real -> Prop) : (term56 s) = (term56 s).
Proof. exact (MK_COMB (@lem5140612) (@lem5140611 s)). Qed.
Lemma lem5140614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5140615 (s : real -> Prop) : (term57 s) = (term57 s).
Proof. exact (MK_COMB (@lem5140614) (@lem5140613 s)). Qed.
Lemma lem5140616 (s : real -> Prop) : (term58 s) = (term58 s).
Proof. exact (MK_COMB (@lem5140615 s) (@lem5140605 s)). Qed.
Lemma lem5140621 (s : real -> Prop) (x : real) (b : real) : (term47 s x b) = (term47 s x b).
Proof. exact (eq_refl (term47 s x b)). Qed.
Lemma lem5140622 (s : real -> Prop) (b : real) : (term48 s b) = (term48 s b).
Proof. exact (fun_ext (fun x : real => @lem5140621 s x b)). Qed.
Lemma lem5140623 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5140624 (s : real -> Prop) (b : real) : (term49 s b) = (term49 s b).
Proof. exact (MK_COMB (@lem5140623) (@lem5140622 s b)). Qed.
Lemma lem5140625 (s : real -> Prop) : (term59 s) = (term59 s).
Proof. exact (fun_ext (fun b : real => @lem5140624 s b)). Qed.
Lemma lem5140626 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5140627 (s : real -> Prop) : (term60 s) = (term60 s).
Proof. exact (MK_COMB (@lem5140626) (@lem5140625 s)). Qed.
Lemma lem5140632 (s : real -> Prop) : (term61 s) = (term61 s).
Proof. exact (eq_refl (term61 s)). Qed.
Lemma lem5140633 (s : real -> Prop) : (term62 s) = (term62 s).
Proof. exact (MK_COMB (@lem5140632 s) (@lem5140627 s)). Qed.
Lemma lem5140634 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5140635 (s : real -> Prop) : (term63 s) = (term63 s).
Proof. exact (MK_COMB (@lem5140634) (@lem5140633 s)). Qed.
Lemma lem5140636 (s : real -> Prop) : (term64 s) = (term64 s).
Proof. exact (MK_COMB (@lem5140635 s) (@lem5140616 s)). Qed.
Lemma lem5140637 : term65 = term65.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5140636 s)). Qed.
Lemma lem5140638 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5140639 : term66 = term66.
Proof. exact (MK_COMB (@lem5140638) (@lem5140637)). Qed.
Lemma lem5140640 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5140641 : term25 = term25.
Proof. exact (MK_COMB (@lem5140640) (@lem5140639)). Qed.
Lemma lem5140642 : term27 = term27.
Proof. exact (MK_COMB (@lem5140641) (@lem5140590)). Qed.
Lemma lem5140647 (x : real) (s : real -> Prop) : (term54 x s) = (term54 x s).
Proof. exact (eq_refl (term54 x s)). Qed.
Lemma lem5140648 (s : real -> Prop) : (term55 s) = (term55 s).
Proof. exact (fun_ext (fun x : real => @lem5140647 x s)). Qed.
Lemma lem5140649 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5140650 (s : real -> Prop) : (term56 s) = (term56 s).
Proof. exact (MK_COMB (@lem5140649) (@lem5140648 s)). Qed.
Lemma lem5140653 (s : real -> Prop) : (term67 s) = (term67 s).
Proof. exact (eq_refl (term67 s)). Qed.
Lemma lem5140654 (s : real -> Prop) : (term68 s) = (term68 s).
Proof. exact (MK_COMB (@lem5140653 s) (@lem5140650 s)). Qed.
Lemma lem5140659 (s : real -> Prop) (x : real) (b : real) : (term47 s x b) = (term47 s x b).
Proof. exact (eq_refl (term47 s x b)). Qed.
Lemma lem5140660 (s : real -> Prop) (b : real) : (term48 s b) = (term48 s b).
Proof. exact (fun_ext (fun x : real => @lem5140659 s x b)). Qed.
Lemma lem5140661 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5140662 (s : real -> Prop) (b : real) : (term49 s b) = (term49 s b).
Proof. exact (MK_COMB (@lem5140661) (@lem5140660 s b)). Qed.
Lemma lem5140665 (b : real) (s : real -> Prop) : (term69 b s) = (term69 b s).
Proof. exact (eq_refl (term69 b s)). Qed.
Lemma lem5140666 (s : real -> Prop) (b : real) : (term70 s b) = (term70 s b).
Proof. exact (MK_COMB (@lem5140665 b s) (@lem5140662 s b)). Qed.
Lemma lem5140667 (s : real -> Prop) : (term71 s) = (term71 s).
Proof. exact (fun_ext (fun b : real => @lem5140666 s b)). Qed.
Lemma lem5140668 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5140669 (s : real -> Prop) : (term10 s) = (term10 s).
Proof. exact (MK_COMB (@lem5140668) (@lem5140667 s)). Qed.
Lemma lem5140670 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5140671 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (MK_COMB (@lem5140670) (@lem5140669 s)). Qed.
Lemma lem5140672 (s : real -> Prop) : (term12 s) = (term12 s).
Proof. exact (MK_COMB (@lem5140671 s) (@lem5140654 s)). Qed.
Lemma lem5140673 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5140674 (s : real -> Prop) : (term14 s) = (term14 s).
Proof. exact (MK_COMB (@lem5140673) (@lem5140672 s)). Qed.
Lemma lem5140675 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5140676 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (MK_COMB (@lem5140675) (@lem5140674 s)). Qed.
Lemma lem5140677 (s : real -> Prop) : (term30 s) = (term30 s).
Proof. exact (MK_COMB (@lem5140676 s) (@lem5140642)). Qed.
Lemma lem5140686 (s : real -> Prop) : (term31 s) = (term31 s).
Proof. exact (eq_refl (term31 s)). Qed.
Lemma lem5140687 (s : real -> Prop) : (term32 s) = (term32 s).
Proof. exact (MK_COMB (@lem5140686 s) (@lem5140677 s)). Qed.
Lemma lem5140688 : term34 = term34.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5140687 s)). Qed.
Lemma lem5140689 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5140690 : term36 = term36.
Proof. exact (MK_COMB (@lem5140689) (@lem5140688)). Qed.
Lemma lem5140815 : term35 = term36.
Proof. exact (TRANS (@lem5140559) (@lem5140690)). Qed.
Lemma lem5140816 : term36 = term35.
Proof. exact (SYM (@lem5140815)). Qed.
Lemma lem5140818 (s : real -> Prop) (h1 : term14 s) : term14 s.
Proof. exact (h1). Qed.
Lemma lem5140819 (h1 : term66) : term66.
Proof. exact (h1). Qed.
Lemma lem5140821 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem5140831 (s : real -> Prop) (h1 : term9 s) : term9 s.
Proof. exact (h1). Qed.
Lemma lem5140839 (s : real -> Prop) (x : real) (b : real) : (term47 s x b) = (term73 s x b).
Proof. exact (@lem17265 (@IN real x s) (real_le x b)). Qed.
Lemma lem5140840 (s : real -> Prop) (b : real) : (term48 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5140839 s x b)). Qed.
Lemma lem5140841 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5140842 (s : real -> Prop) (b : real) : (term49 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5140841) (@lem5140840 s b)). Qed.
Lemma lem5140844 (b : real) (s : real -> Prop) : (term69 b s) = (term69 b s).
Proof. exact (eq_refl (term69 b s)). Qed.
Lemma lem5140845 (s : real -> Prop) (b : real) : (term70 s b) = (term76 s b).
Proof. exact (MK_COMB (@lem5140844 b s) (@lem5140842 s b)). Qed.
Lemma lem5140846 (s : real -> Prop) : (term71 s) = (term77 s).
Proof. exact (fun_ext (fun b : real => @lem5140845 s b)). Qed.
Lemma lem5140847 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5140848 (s : real -> Prop) : (term10 s) = (term78 s).
Proof. exact (MK_COMB (@lem5140847) (@lem5140846 s)). Qed.
Lemma lem5140856 (x : real) (s : real -> Prop) : (term79 x s) = (term80 x s).
Proof. exact (@lem17362 (@IN real x s) (term81 x s)). Qed.
Lemma lem5140857 (P : real -> Prop) : (term82 P) = (term83 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5140858 (s : real -> Prop) : (term84 s) = (term85 s).
Proof. exact (@lem5140857 (term55 s)). Qed.
Lemma lem5140859 (x : real) (s : real -> Prop) : (term86 s x) = (term54 x s).
Proof. exact (eq_refl (term86 s x)). Qed.
Lemma lem5140860 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5140861 (x : real) (s : real -> Prop) : (term87 s x) = (term79 x s).
Proof. exact (MK_COMB (@lem5140860) (@lem5140859 x s)). Qed.
Lemma lem5140862 (x : real) (s : real -> Prop) : (term87 s x) = (term80 x s).
Proof. exact (TRANS (@lem5140861 x s) (@lem5140856 x s)). Qed.
Lemma lem5140863 (s : real -> Prop) : (term88 s) = (term89 s).
Proof. exact (fun_ext (fun x : real => @lem5140862 x s)). Qed.
Lemma lem5140864 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5140865 (s : real -> Prop) : (term85 s) = (term90 s).
Proof. exact (MK_COMB (@lem5140864) (@lem5140863 s)). Qed.
Lemma lem5140866 (s : real -> Prop) : (term84 s) = (term90 s).
Proof. exact (TRANS (@lem5140858 s) (@lem5140865 s)). Qed.
Lemma lem5140868 (s : real -> Prop) : (term91 s) = (term91 s).
Proof. exact (eq_refl (term91 s)). Qed.
Lemma lem5140869 (s : real -> Prop) : (term92 s) = (term93 s).
Proof. exact (MK_COMB (@lem5140868 s) (@lem5140866 s)). Qed.
Lemma lem5140870 (s : real -> Prop) : (term94 s) = (term92 s).
Proof. exact (@lem17045 (term95 s) (term56 s)). Qed.
Lemma lem5140871 (s : real -> Prop) : (term94 s) = (term93 s).
Proof. exact (TRANS (@lem5140870 s) (@lem5140869 s)). Qed.
Lemma lem5140872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5140873 (s : real -> Prop) : (term96 s) = (term97 s).
Proof. exact (MK_COMB (@lem5140872) (@lem5140848 s)). Qed.
Lemma lem5140874 (s : real -> Prop) : (term98 s) = (term99 s).
Proof. exact (MK_COMB (@lem5140873 s) (@lem5140871 s)). Qed.
Lemma lem5140875 (s : real -> Prop) : (term14 s) = (term98 s).
Proof. exact (@lem17362 (term10 s) (term68 s)). Qed.
Lemma lem5140876 (s : real -> Prop) : (term14 s) = (term99 s).
Proof. exact (TRANS (@lem5140875 s) (@lem5140874 s)). Qed.
Lemma lem5141023 {A : Type'} (P : Prop) (Q : A -> Prop) : (term100 A P Q) = (term101 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5141024 (P : Prop) (Q : real -> Prop) : (term102 P Q) = (term103 P Q).
Proof. exact (@lem5141023 real P Q). Qed.
Lemma lem5141025 (s : real -> Prop) : (term104 s) = (term105 s).
Proof. exact (@lem5141024 (term106 s) (term89 s)). Qed.
Lemma lem5141026 (x : real) (s : real -> Prop) : (term107 s x) = (term80 x s).
Proof. exact (eq_refl (term107 s x)). Qed.
Lemma lem5141027 (s : real -> Prop) : (term108 s) = (term89 s).
Proof. exact (fun_ext (fun x : real => @lem5141026 x s)). Qed.
Lemma lem5141028 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5141029 (s : real -> Prop) : (term109 s) = (term90 s).
Proof. exact (MK_COMB (@lem5141028) (@lem5141027 s)). Qed.
Lemma lem5141030 (s : real -> Prop) : (term91 s) = (term91 s).
Proof. exact (eq_refl (term91 s)). Qed.
Lemma lem5141031 (s : real -> Prop) : (term104 s) = (term93 s).
Proof. exact (MK_COMB (@lem5141030 s) (@lem5141029 s)). Qed.
Lemma lem5141032 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5141033 (s : real -> Prop) : (term110 s) = (term111 s).
Proof. exact (MK_COMB (@lem5141032) (@lem5141031 s)). Qed.
Lemma lem5141034 (x : real) (s : real -> Prop) : (term107 s x) = (term80 x s).
Proof. exact (eq_refl (term107 s x)). Qed.
Lemma lem5141035 (s : real -> Prop) : (term91 s) = (term91 s).
Proof. exact (eq_refl (term91 s)). Qed.
Lemma lem5141036 (x : real) (s : real -> Prop) : (term112 s x) = (term113 x s).
Proof. exact (MK_COMB (@lem5141035 s) (@lem5141034 x s)). Qed.
Lemma lem5141037 (s : real -> Prop) : (term114 s) = (term115 s).
Proof. exact (fun_ext (fun x : real => @lem5141036 x s)). Qed.
Lemma lem5141038 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5141039 (s : real -> Prop) : (term105 s) = (term116 s).
Proof. exact (MK_COMB (@lem5141038) (@lem5141037 s)). Qed.
Lemma lem5141040 (s : real -> Prop) : ((term104 s) = (term105 s)) = ((term93 s) = (term116 s)).
Proof. exact (MK_COMB (@lem5141033 s) (@lem5141039 s)). Qed.
Lemma lem5141041 (s : real -> Prop) : (term93 s) = (term116 s).
Proof. exact (EQ_MP (@lem5141040 s) (@lem5141025 s)). Qed.
Lemma lem5141042 (s : real -> Prop) : (term97 s) = (term97 s).
Proof. exact (eq_refl (term97 s)). Qed.
Lemma lem5141043 (s : real -> Prop) : (term99 s) = (term117 s).
Proof. exact (MK_COMB (@lem5141042 s) (@lem5141041 s)). Qed.
Lemma lem5141045 {A : Type'} (P : A -> Prop) (Q : Prop) : (term118 A P Q) = (term119 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5141046 (P : real -> Prop) (Q : Prop) : (term120 P Q) = (term121 P Q).
Proof. exact (@lem5141045 real P Q). Qed.
Lemma lem5141047 (s : real -> Prop) : (term122 s) = (term123 s).
Proof. exact (@lem5141046 (term77 s) (term116 s)). Qed.
Lemma lem5141048 (s : real -> Prop) (b : real) : (term124 s b) = (term76 s b).
Proof. exact (eq_refl (term124 s b)). Qed.
Lemma lem5141049 (s : real -> Prop) : (term125 s) = (term77 s).
Proof. exact (fun_ext (fun b : real => @lem5141048 s b)). Qed.
Lemma lem5141050 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5141051 (s : real -> Prop) : (term126 s) = (term78 s).
Proof. exact (MK_COMB (@lem5141050) (@lem5141049 s)). Qed.
Lemma lem5141052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5141053 (s : real -> Prop) : (term127 s) = (term97 s).
Proof. exact (MK_COMB (@lem5141052) (@lem5141051 s)). Qed.
Lemma lem5141054 (s : real -> Prop) : (term116 s) = (term116 s).
Proof. exact (eq_refl (term116 s)). Qed.
Lemma lem5141055 (s : real -> Prop) : (term122 s) = (term117 s).
Proof. exact (MK_COMB (@lem5141053 s) (@lem5141054 s)). Qed.
Lemma lem5141056 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5141057 (s : real -> Prop) : (term128 s) = (term129 s).
Proof. exact (MK_COMB (@lem5141056) (@lem5141055 s)). Qed.
Lemma lem5141058 (s : real -> Prop) (b : real) : (term124 s b) = (term76 s b).
Proof. exact (eq_refl (term124 s b)). Qed.
Lemma lem5141059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5141060 (s : real -> Prop) (b : real) : (term130 s b) = (term131 s b).
Proof. exact (MK_COMB (@lem5141059) (@lem5141058 s b)). Qed.
Lemma lem5141061 (s : real -> Prop) : (term116 s) = (term116 s).
Proof. exact (eq_refl (term116 s)). Qed.
Lemma lem5141062 (b : real) (s : real -> Prop) : (term132 b s) = (term133 b s).
Proof. exact (MK_COMB (@lem5141060 s b) (@lem5141061 s)). Qed.
Lemma lem5141063 (s : real -> Prop) : (term134 s) = (term135 s).
Proof. exact (fun_ext (fun b : real => @lem5141062 b s)). Qed.
Lemma lem5141064 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5141065 (s : real -> Prop) : (term123 s) = (term136 s).
Proof. exact (MK_COMB (@lem5141064) (@lem5141063 s)). Qed.
Lemma lem5141066 (s : real -> Prop) : ((term122 s) = (term123 s)) = ((term117 s) = (term136 s)).
Proof. exact (MK_COMB (@lem5141057 s) (@lem5141065 s)). Qed.
Lemma lem5141067 (s : real -> Prop) : (term117 s) = (term136 s).
Proof. exact (EQ_MP (@lem5141066 s) (@lem5141047 s)). Qed.
Lemma lem5141069 {A : Type'} (P : Prop) (Q : A -> Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5141070 (P : Prop) (Q : real -> Prop) : (term139 P Q) = (term140 P Q).
Proof. exact (@lem5141069 real P Q). Qed.
Lemma lem5141071 (b : real) (s : real -> Prop) : (term141 b s) = (term142 b s).
Proof. exact (@lem5141070 (term76 s b) (term115 s)). Qed.
Lemma lem5141072 (x : real) (s : real -> Prop) : (term143 s x) = (term113 x s).
Proof. exact (eq_refl (term143 s x)). Qed.
Lemma lem5141073 (s : real -> Prop) : (term144 s) = (term115 s).
Proof. exact (fun_ext (fun x : real => @lem5141072 x s)). Qed.
Lemma lem5141074 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5141075 (s : real -> Prop) : (term145 s) = (term116 s).
Proof. exact (MK_COMB (@lem5141074) (@lem5141073 s)). Qed.
Lemma lem5141076 (s : real -> Prop) (b : real) : (term131 s b) = (term131 s b).
Proof. exact (eq_refl (term131 s b)). Qed.
Lemma lem5141077 (b : real) (s : real -> Prop) : (term141 b s) = (term133 b s).
Proof. exact (MK_COMB (@lem5141076 s b) (@lem5141075 s)). Qed.
Lemma lem5141078 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5141079 (b : real) (s : real -> Prop) : (term146 b s) = (term147 b s).
Proof. exact (MK_COMB (@lem5141078) (@lem5141077 b s)). Qed.
Lemma lem5141080 (x : real) (s : real -> Prop) : (term143 s x) = (term113 x s).
Proof. exact (eq_refl (term143 s x)). Qed.
Lemma lem5141081 (s : real -> Prop) (b : real) : (term131 s b) = (term131 s b).
Proof. exact (eq_refl (term131 s b)). Qed.
Lemma lem5141082 (b : real) (x : real) (s : real -> Prop) : (term148 b s x) = (term149 b x s).
Proof. exact (MK_COMB (@lem5141081 s b) (@lem5141080 x s)). Qed.
Lemma lem5141083 (b : real) (s : real -> Prop) : (term150 b s) = (term151 b s).
Proof. exact (fun_ext (fun x : real => @lem5141082 b x s)). Qed.
Lemma lem5141084 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5141085 (b : real) (s : real -> Prop) : (term142 b s) = (term152 b s).
Proof. exact (MK_COMB (@lem5141084) (@lem5141083 b s)). Qed.
Lemma lem5141086 (b : real) (s : real -> Prop) : ((term141 b s) = (term142 b s)) = ((term133 b s) = (term152 b s)).
Proof. exact (MK_COMB (@lem5141079 b s) (@lem5141085 b s)). Qed.
Lemma lem5141087 (b : real) (s : real -> Prop) : (term133 b s) = (term152 b s).
Proof. exact (EQ_MP (@lem5141086 b s) (@lem5141071 b s)). Qed.
Lemma lem5141088 (s : real -> Prop) : (term135 s) = (term153 s).
Proof. exact (fun_ext (fun b : real => @lem5141087 b s)). Qed.
Lemma lem5141089 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5141090 (s : real -> Prop) : (term136 s) = (term154 s).
Proof. exact (MK_COMB (@lem5141089) (@lem5141088 s)). Qed.
Lemma lem5141091 (s : real -> Prop) : (term117 s) = (term154 s).
Proof. exact (TRANS (@lem5141067 s) (@lem5141090 s)). Qed.
Lemma lem5141093 (s : real -> Prop) : (term99 s) = (term154 s).
Proof. exact (TRANS (@lem5141043 s) (@lem5141091 s)). Qed.
Lemma lem5141094 (s : real -> Prop) : (term14 s) = (term154 s).
Proof. exact (TRANS (@lem5140876 s) (@lem5141093 s)). Qed.
Lemma lem5141095 (s : real -> Prop) (h1 : term14 s) : term154 s.
Proof. exact (EQ_MP (@lem5141094 s) (@lem5140818 s h1)). Qed.
Lemma lem5141098 (s : real -> Prop) : (term155 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5141105 (s : real -> Prop) (x : real) (b : real) : (term156 s x b) = (term157 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5141106 (P : real -> Prop) : (term82 P) = (term83 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5141107 (s : real -> Prop) (b : real) : (term158 s b) = (term159 s b).
Proof. exact (@lem5141106 (term48 s b)). Qed.
Lemma lem5141108 (s : real -> Prop) (x : real) (b : real) : (term160 s b x) = (term47 s x b).
Proof. exact (eq_refl (term160 s b x)). Qed.
Lemma lem5141109 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5141110 (s : real -> Prop) (x : real) (b : real) : (term161 s b x) = (term156 s x b).
Proof. exact (MK_COMB (@lem5141109) (@lem5141108 s x b)). Qed.
Lemma lem5141111 (s : real -> Prop) (x : real) (b : real) : (term161 s b x) = (term157 s x b).
Proof. exact (TRANS (@lem5141110 s x b) (@lem5141105 s x b)). Qed.
Lemma lem5141112 (s : real -> Prop) (b : real) : (term162 s b) = (term163 s b).
Proof. exact (fun_ext (fun x : real => @lem5141111 s x b)). Qed.
Lemma lem5141113 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5141114 (s : real -> Prop) (b : real) : (term159 s b) = (term164 s b).
Proof. exact (MK_COMB (@lem5141113) (@lem5141112 s b)). Qed.
Lemma lem5141115 (s : real -> Prop) (b : real) : (term158 s b) = (term164 s b).
Proof. exact (TRANS (@lem5141107 s b) (@lem5141114 s b)). Qed.
Lemma lem5141116 (P : real -> Prop) : (term165 P) = (term166 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5141117 (s : real -> Prop) : (term167 s) = (term168 s).
Proof. exact (@lem5141116 (term59 s)). Qed.
Lemma lem5141118 (s : real -> Prop) (b : real) : (term169 s b) = (term49 s b).
Proof. exact (eq_refl (term169 s b)). Qed.
Lemma lem5141119 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5141120 (s : real -> Prop) (b : real) : (term170 s b) = (term158 s b).
Proof. exact (MK_COMB (@lem5141119) (@lem5141118 s b)). Qed.
Lemma lem5141121 (s : real -> Prop) (b : real) : (term170 s b) = (term164 s b).
Proof. exact (TRANS (@lem5141120 s b) (@lem5141115 s b)). Qed.
Lemma lem5141122 (s : real -> Prop) : (term171 s) = (term172 s).
Proof. exact (fun_ext (fun b : real => @lem5141121 s b)). Qed.
Lemma lem5141123 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141124 (s : real -> Prop) : (term168 s) = (term173 s).
Proof. exact (MK_COMB (@lem5141123) (@lem5141122 s)). Qed.
Lemma lem5141125 (s : real -> Prop) : (term167 s) = (term173 s).
Proof. exact (TRANS (@lem5141117 s) (@lem5141124 s)). Qed.
Lemma lem5141126 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5141127 (s : real -> Prop) : (term174 s) = (term175 s).
Proof. exact (MK_COMB (@lem5141126) (@lem5141098 s)). Qed.
Lemma lem5141128 (s : real -> Prop) : (term176 s) = (term177 s).
Proof. exact (MK_COMB (@lem5141127 s) (@lem5141125 s)). Qed.
Lemma lem5141129 (s : real -> Prop) : (term178 s) = (term176 s).
Proof. exact (@lem17045 (term179 s) (term60 s)). Qed.
Lemma lem5141130 (s : real -> Prop) : (term178 s) = (term177 s).
Proof. exact (TRANS (@lem5141129 s) (@lem5141128 s)). Qed.
Lemma lem5141137 (x : real) (s : real -> Prop) : (term54 x s) = (term180 x s).
Proof. exact (@lem17265 (@IN real x s) (term81 x s)). Qed.
Lemma lem5141138 (s : real -> Prop) : (term55 s) = (term181 s).
Proof. exact (fun_ext (fun x : real => @lem5141137 x s)). Qed.
Lemma lem5141139 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141140 (s : real -> Prop) : (term56 s) = (term182 s).
Proof. exact (MK_COMB (@lem5141139) (@lem5141138 s)). Qed.
Lemma lem5141147 (s : real -> Prop) (x : real) (b : real) : (term156 s x b) = (term157 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5141148 (P : real -> Prop) : (term82 P) = (term83 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5141149 (s : real -> Prop) (b : real) : (term158 s b) = (term159 s b).
Proof. exact (@lem5141148 (term48 s b)). Qed.
Lemma lem5141150 (s : real -> Prop) (x : real) (b : real) : (term160 s b x) = (term47 s x b).
Proof. exact (eq_refl (term160 s b x)). Qed.
Lemma lem5141151 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5141152 (s : real -> Prop) (x : real) (b : real) : (term161 s b x) = (term156 s x b).
Proof. exact (MK_COMB (@lem5141151) (@lem5141150 s x b)). Qed.
Lemma lem5141153 (s : real -> Prop) (x : real) (b : real) : (term161 s b x) = (term157 s x b).
Proof. exact (TRANS (@lem5141152 s x b) (@lem5141147 s x b)). Qed.
Lemma lem5141154 (s : real -> Prop) (b : real) : (term162 s b) = (term163 s b).
Proof. exact (fun_ext (fun x : real => @lem5141153 s x b)). Qed.
Lemma lem5141155 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5141156 (s : real -> Prop) (b : real) : (term159 s b) = (term164 s b).
Proof. exact (MK_COMB (@lem5141155) (@lem5141154 s b)). Qed.
Lemma lem5141157 (s : real -> Prop) (b : real) : (term158 s b) = (term164 s b).
Proof. exact (TRANS (@lem5141149 s b) (@lem5141156 s b)). Qed.
Lemma lem5141158 (s : real -> Prop) (b : real) : (term46 s b) = (term46 s b).
Proof. exact (eq_refl (term46 s b)). Qed.
Lemma lem5141159 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5141160 (s : real -> Prop) (b : real) : (term183 s b) = (term184 s b).
Proof. exact (MK_COMB (@lem5141159) (@lem5141157 s b)). Qed.
Lemma lem5141161 (s : real -> Prop) (b : real) : (term185 s b) = (term186 s b).
Proof. exact (MK_COMB (@lem5141160 s b) (@lem5141158 s b)). Qed.
Lemma lem5141162 (s : real -> Prop) (b : real) : (term51 s b) = (term185 s b).
Proof. exact (@lem17265 (term49 s b) (term46 s b)). Qed.
Lemma lem5141163 (s : real -> Prop) (b : real) : (term51 s b) = (term186 s b).
Proof. exact (TRANS (@lem5141162 s b) (@lem5141161 s b)). Qed.
Lemma lem5141164 (s : real -> Prop) : (term52 s) = (term187 s).
Proof. exact (fun_ext (fun b : real => @lem5141163 s b)). Qed.
Lemma lem5141165 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141166 (s : real -> Prop) : (term53 s) = (term188 s).
Proof. exact (MK_COMB (@lem5141165) (@lem5141164 s)). Qed.
Lemma lem5141167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5141168 (s : real -> Prop) : (term57 s) = (term189 s).
Proof. exact (MK_COMB (@lem5141167) (@lem5141140 s)). Qed.
Lemma lem5141169 (s : real -> Prop) : (term58 s) = (term190 s).
Proof. exact (MK_COMB (@lem5141168 s) (@lem5141166 s)). Qed.
Lemma lem5141170 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5141171 (s : real -> Prop) : (term191 s) = (term192 s).
Proof. exact (MK_COMB (@lem5141170) (@lem5141130 s)). Qed.
Lemma lem5141172 (s : real -> Prop) : (term193 s) = (term194 s).
Proof. exact (MK_COMB (@lem5141171 s) (@lem5141169 s)). Qed.
Lemma lem5141173 (s : real -> Prop) : (term64 s) = (term193 s).
Proof. exact (@lem17265 (term62 s) (term58 s)). Qed.
Lemma lem5141174 (s : real -> Prop) : (term64 s) = (term194 s).
Proof. exact (TRANS (@lem5141173 s) (@lem5141172 s)). Qed.
Lemma lem5141175 : term65 = term195.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5141174 s)). Qed.
Lemma lem5141176 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5141177 : term66 = term196.
Proof. exact (MK_COMB (@lem5141176) (@lem5141175)). Qed.
Lemma lem5141424 {A B : Type'} (P : type1413 A B) : (term197 A B P) = (term198 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5141425 (P : type1626) : (term199 P) = (term200 P).
Proof. exact (@lem5141424 real real P). Qed.
Lemma lem5141426 (s : real -> Prop) : (term201 s) = (term202 s).
Proof. exact (@lem5141425 (term203 s)). Qed.
Lemma lem5141427 (s : real -> Prop) (b : real) : (term204 s b) = (term163 s b).
Proof. exact (eq_refl (term204 s b)). Qed.
Lemma lem5141428 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5141429 (s : real -> Prop) (b : real) (x : real) : (term205 s b x) = (term206 s b x).
Proof. exact (MK_COMB (@lem5141427 s b) (@lem5141428 x)). Qed.
Lemma lem5141430 (s : real -> Prop) (x : real) (b : real) : (term206 s b x) = (term157 s x b).
Proof. exact (eq_refl (term206 s b x)). Qed.
Lemma lem5141431 (s : real -> Prop) (x : real) (b : real) : (term205 s b x) = (term157 s x b).
Proof. exact (TRANS (@lem5141429 s b x) (@lem5141430 s x b)). Qed.
Lemma lem5141432 (s : real -> Prop) (b : real) : (term207 s b) = (term163 s b).
Proof. exact (fun_ext (fun x : real => @lem5141431 s x b)). Qed.
Lemma lem5141433 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5141434 (s : real -> Prop) (b : real) : (term208 s b) = (term164 s b).
Proof. exact (MK_COMB (@lem5141433) (@lem5141432 s b)). Qed.
Lemma lem5141435 (s : real -> Prop) : (term209 s) = (term172 s).
Proof. exact (fun_ext (fun b : real => @lem5141434 s b)). Qed.
Lemma lem5141436 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141437 (s : real -> Prop) : (term201 s) = (term173 s).
Proof. exact (MK_COMB (@lem5141436) (@lem5141435 s)). Qed.
Lemma lem5141438 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5141439 (s : real -> Prop) : (term210 s) = (term211 s).
Proof. exact (MK_COMB (@lem5141438) (@lem5141437 s)). Qed.
Lemma lem5141440 (s : real -> Prop) (b : real) : (term204 s b) = (term163 s b).
Proof. exact (eq_refl (term204 s b)). Qed.
Lemma lem5141441 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5141442 (s : real -> Prop) (x : real -> real) (b : real) : (term212 s x b) = (term213 s x b).
Proof. exact (MK_COMB (@lem5141440 s b) (@lem5141441 x b)). Qed.
Lemma lem5141443 (s : real -> Prop) (x : real -> real) (b : real) : (term213 s x b) = (term214 s x b).
Proof. exact (eq_refl (term213 s x b)). Qed.
Lemma lem5141444 (s : real -> Prop) (x : real -> real) (b : real) : (term212 s x b) = (term214 s x b).
Proof. exact (TRANS (@lem5141442 s x b) (@lem5141443 s x b)). Qed.
Lemma lem5141445 (s : real -> Prop) (x : real -> real) : (term215 s x) = (term216 s x).
Proof. exact (fun_ext (fun b : real => @lem5141444 s x b)). Qed.
Lemma lem5141446 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141447 (s : real -> Prop) (x : real -> real) : (term217 s x) = (term218 s x).
Proof. exact (MK_COMB (@lem5141446) (@lem5141445 s x)). Qed.
Lemma lem5141448 (s : real -> Prop) : (term219 s) = (term220 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5141447 s x)). Qed.
Lemma lem5141449 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5141450 (s : real -> Prop) : (term202 s) = (term221 s).
Proof. exact (MK_COMB (@lem5141449) (@lem5141448 s)). Qed.
Lemma lem5141451 (s : real -> Prop) : ((term201 s) = (term202 s)) = ((term173 s) = (term221 s)).
Proof. exact (MK_COMB (@lem5141439 s) (@lem5141450 s)). Qed.
Lemma lem5141452 (s : real -> Prop) : (term173 s) = (term221 s).
Proof. exact (EQ_MP (@lem5141451 s) (@lem5141426 s)). Qed.
Lemma lem5141453 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (eq_refl (term175 s)). Qed.
Lemma lem5141454 (s : real -> Prop) : (term177 s) = (term222 s).
Proof. exact (MK_COMB (@lem5141453 s) (@lem5141452 s)). Qed.
Lemma lem5141456 {A : Type'} (P : Prop) (Q : A -> Prop) : (term100 A P Q) = (term101 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5141457 (P : Prop) (Q : type1028) : (term223 P Q) = (term224 P Q).
Proof. exact (@lem5141456 (real -> real) P Q). Qed.
Lemma lem5141458 (s : real -> Prop) : (term225 s) = (term226 s).
Proof. exact (@lem5141457 (s = (@EMPTY real)) (term220 s)). Qed.
Lemma lem5141459 (s : real -> Prop) (x : real -> real) : (term227 s x) = (term218 s x).
Proof. exact (eq_refl (term227 s x)). Qed.
Lemma lem5141460 (s : real -> Prop) : (term228 s) = (term220 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5141459 s x)). Qed.
Lemma lem5141461 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5141462 (s : real -> Prop) : (term229 s) = (term221 s).
Proof. exact (MK_COMB (@lem5141461) (@lem5141460 s)). Qed.
Lemma lem5141463 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (eq_refl (term175 s)). Qed.
Lemma lem5141464 (s : real -> Prop) : (term225 s) = (term222 s).
Proof. exact (MK_COMB (@lem5141463 s) (@lem5141462 s)). Qed.
Lemma lem5141465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5141466 (s : real -> Prop) : (term230 s) = (term231 s).
Proof. exact (MK_COMB (@lem5141465) (@lem5141464 s)). Qed.
Lemma lem5141467 (s : real -> Prop) (x : real -> real) : (term227 s x) = (term218 s x).
Proof. exact (eq_refl (term227 s x)). Qed.
Lemma lem5141468 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (eq_refl (term175 s)). Qed.
Lemma lem5141469 (s : real -> Prop) (x : real -> real) : (term232 s x) = (term233 s x).
Proof. exact (MK_COMB (@lem5141468 s) (@lem5141467 s x)). Qed.
Lemma lem5141470 (s : real -> Prop) : (term234 s) = (term235 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5141469 s x)). Qed.
Lemma lem5141471 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5141472 (s : real -> Prop) : (term226 s) = (term236 s).
Proof. exact (MK_COMB (@lem5141471) (@lem5141470 s)). Qed.
Lemma lem5141473 (s : real -> Prop) : ((term225 s) = (term226 s)) = ((term222 s) = (term236 s)).
Proof. exact (MK_COMB (@lem5141466 s) (@lem5141472 s)). Qed.
Lemma lem5141474 (s : real -> Prop) : (term222 s) = (term236 s).
Proof. exact (EQ_MP (@lem5141473 s) (@lem5141458 s)). Qed.
Lemma lem5141475 (s : real -> Prop) : (term177 s) = (term236 s).
Proof. exact (TRANS (@lem5141454 s) (@lem5141474 s)). Qed.
Lemma lem5141476 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5141477 (s : real -> Prop) : (term192 s) = (term237 s).
Proof. exact (MK_COMB (@lem5141476) (@lem5141475 s)). Qed.
Lemma lem5141479 {A : Type'} (P : A -> Prop) (Q : Prop) : (term238 A P Q) = (term239 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5141480 (P : real -> Prop) (Q : Prop) : (term240 P Q) = (term241 P Q).
Proof. exact (@lem5141479 real P Q). Qed.
Lemma lem5141481 (s : real -> Prop) (b : real) : (term242 s b) = (term243 s b).
Proof. exact (@lem5141480 (term163 s b) (term46 s b)). Qed.
Lemma lem5141482 (s : real -> Prop) (x : real) (b : real) : (term206 s b x) = (term157 s x b).
Proof. exact (eq_refl (term206 s b x)). Qed.
Lemma lem5141483 (s : real -> Prop) (b : real) : (term244 s b) = (term163 s b).
Proof. exact (fun_ext (fun x : real => @lem5141482 s x b)). Qed.
Lemma lem5141484 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5141485 (s : real -> Prop) (b : real) : (term245 s b) = (term164 s b).
Proof. exact (MK_COMB (@lem5141484) (@lem5141483 s b)). Qed.
Lemma lem5141486 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5141487 (s : real -> Prop) (b : real) : (term246 s b) = (term184 s b).
Proof. exact (MK_COMB (@lem5141486) (@lem5141485 s b)). Qed.
Lemma lem5141488 (s : real -> Prop) (b : real) : (term46 s b) = (term46 s b).
Proof. exact (eq_refl (term46 s b)). Qed.
Lemma lem5141489 (s : real -> Prop) (b : real) : (term242 s b) = (term186 s b).
Proof. exact (MK_COMB (@lem5141487 s b) (@lem5141488 s b)). Qed.
Lemma lem5141490 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5141491 (s : real -> Prop) (b : real) : (term247 s b) = (term248 s b).
Proof. exact (MK_COMB (@lem5141490) (@lem5141489 s b)). Qed.
Lemma lem5141492 (s : real -> Prop) (x : real) (b : real) : (term206 s b x) = (term157 s x b).
Proof. exact (eq_refl (term206 s b x)). Qed.
Lemma lem5141493 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5141494 (s : real -> Prop) (x : real) (b : real) : (term249 s b x) = (term250 s x b).
Proof. exact (MK_COMB (@lem5141493) (@lem5141492 s x b)). Qed.
Lemma lem5141495 (s : real -> Prop) (b : real) : (term46 s b) = (term46 s b).
Proof. exact (eq_refl (term46 s b)). Qed.
Lemma lem5141496 (x : real) (s : real -> Prop) (b : real) : (term251 x s b) = (term252 x s b).
Proof. exact (MK_COMB (@lem5141494 s x b) (@lem5141495 s b)). Qed.
Lemma lem5141497 (s : real -> Prop) (b : real) : (term253 s b) = (term254 s b).
Proof. exact (fun_ext (fun x : real => @lem5141496 x s b)). Qed.
Lemma lem5141498 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5141499 (s : real -> Prop) (b : real) : (term243 s b) = (term255 s b).
Proof. exact (MK_COMB (@lem5141498) (@lem5141497 s b)). Qed.
Lemma lem5141500 (s : real -> Prop) (b : real) : ((term242 s b) = (term243 s b)) = ((term186 s b) = (term255 s b)).
Proof. exact (MK_COMB (@lem5141491 s b) (@lem5141499 s b)). Qed.
Lemma lem5141501 (s : real -> Prop) (b : real) : (term186 s b) = (term255 s b).
Proof. exact (EQ_MP (@lem5141500 s b) (@lem5141481 s b)). Qed.
Lemma lem5141502 (s : real -> Prop) : (term187 s) = (term256 s).
Proof. exact (fun_ext (fun b : real => @lem5141501 s b)). Qed.
Lemma lem5141503 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141504 (s : real -> Prop) : (term188 s) = (term257 s).
Proof. exact (MK_COMB (@lem5141503) (@lem5141502 s)). Qed.
Lemma lem5141506 {A B : Type'} (P : type1413 A B) : (term197 A B P) = (term198 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5141507 (P : type1626) : (term199 P) = (term200 P).
Proof. exact (@lem5141506 real real P). Qed.
Lemma lem5141508 (s : real -> Prop) : (term258 s) = (term259 s).
Proof. exact (@lem5141507 (term260 s)). Qed.
Lemma lem5141509 (s : real -> Prop) (b : real) : (term261 s b) = (term254 s b).
Proof. exact (eq_refl (term261 s b)). Qed.
Lemma lem5141510 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5141511 (s : real -> Prop) (b : real) (x : real) : (term262 s b x) = (term263 s b x).
Proof. exact (MK_COMB (@lem5141509 s b) (@lem5141510 x)). Qed.
Lemma lem5141512 (x : real) (s : real -> Prop) (b : real) : (term263 s b x) = (term252 x s b).
Proof. exact (eq_refl (term263 s b x)). Qed.
Lemma lem5141513 (x : real) (s : real -> Prop) (b : real) : (term262 s b x) = (term252 x s b).
Proof. exact (TRANS (@lem5141511 s b x) (@lem5141512 x s b)). Qed.
Lemma lem5141514 (s : real -> Prop) (b : real) : (term264 s b) = (term254 s b).
Proof. exact (fun_ext (fun x : real => @lem5141513 x s b)). Qed.
Lemma lem5141515 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5141516 (s : real -> Prop) (b : real) : (term265 s b) = (term255 s b).
Proof. exact (MK_COMB (@lem5141515) (@lem5141514 s b)). Qed.
Lemma lem5141517 (s : real -> Prop) : (term266 s) = (term256 s).
Proof. exact (fun_ext (fun b : real => @lem5141516 s b)). Qed.
Lemma lem5141518 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141519 (s : real -> Prop) : (term258 s) = (term257 s).
Proof. exact (MK_COMB (@lem5141518) (@lem5141517 s)). Qed.
Lemma lem5141520 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5141521 (s : real -> Prop) : (term267 s) = (term268 s).
Proof. exact (MK_COMB (@lem5141520) (@lem5141519 s)). Qed.
Lemma lem5141522 (s : real -> Prop) (b : real) : (term261 s b) = (term254 s b).
Proof. exact (eq_refl (term261 s b)). Qed.
Lemma lem5141523 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5141524 (s : real -> Prop) (x : real -> real) (b : real) : (term269 s x b) = (term270 s x b).
Proof. exact (MK_COMB (@lem5141522 s b) (@lem5141523 x b)). Qed.
Lemma lem5141525 (x : real -> real) (s : real -> Prop) (b : real) : (term270 s x b) = (term271 x s b).
Proof. exact (eq_refl (term270 s x b)). Qed.
Lemma lem5141526 (x : real -> real) (s : real -> Prop) (b : real) : (term269 s x b) = (term271 x s b).
Proof. exact (TRANS (@lem5141524 s x b) (@lem5141525 x s b)). Qed.
Lemma lem5141527 (x : real -> real) (s : real -> Prop) : (term272 s x) = (term273 x s).
Proof. exact (fun_ext (fun b : real => @lem5141526 x s b)). Qed.
Lemma lem5141528 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141529 (x : real -> real) (s : real -> Prop) : (term274 s x) = (term275 x s).
Proof. exact (MK_COMB (@lem5141528) (@lem5141527 x s)). Qed.
Lemma lem5141530 (s : real -> Prop) : (term276 s) = (term277 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5141529 x s)). Qed.
Lemma lem5141531 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5141532 (s : real -> Prop) : (term259 s) = (term278 s).
Proof. exact (MK_COMB (@lem5141531) (@lem5141530 s)). Qed.
Lemma lem5141533 (s : real -> Prop) : ((term258 s) = (term259 s)) = ((term257 s) = (term278 s)).
Proof. exact (MK_COMB (@lem5141521 s) (@lem5141532 s)). Qed.
Lemma lem5141534 (s : real -> Prop) : (term257 s) = (term278 s).
Proof. exact (EQ_MP (@lem5141533 s) (@lem5141508 s)). Qed.
Lemma lem5141535 (s : real -> Prop) : (term188 s) = (term278 s).
Proof. exact (TRANS (@lem5141504 s) (@lem5141534 s)). Qed.
Lemma lem5141536 (s : real -> Prop) : (term189 s) = (term189 s).
Proof. exact (eq_refl (term189 s)). Qed.
Lemma lem5141537 (s : real -> Prop) : (term190 s) = (term279 s).
Proof. exact (MK_COMB (@lem5141536 s) (@lem5141535 s)). Qed.
Lemma lem5141539 {A : Type'} (P : Prop) (Q : A -> Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5141540 (P : Prop) (Q : type1028) : (term280 P Q) = (term281 P Q).
Proof. exact (@lem5141539 (real -> real) P Q). Qed.
Lemma lem5141541 (s : real -> Prop) : (term282 s) = (term283 s).
Proof. exact (@lem5141540 (term182 s) (term277 s)). Qed.
Lemma lem5141542 (x : real -> real) (s : real -> Prop) : (term284 s x) = (term275 x s).
Proof. exact (eq_refl (term284 s x)). Qed.
Lemma lem5141543 (s : real -> Prop) : (term285 s) = (term277 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5141542 x s)). Qed.
Lemma lem5141544 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5141545 (s : real -> Prop) : (term286 s) = (term278 s).
Proof. exact (MK_COMB (@lem5141544) (@lem5141543 s)). Qed.
Lemma lem5141546 (s : real -> Prop) : (term189 s) = (term189 s).
Proof. exact (eq_refl (term189 s)). Qed.
Lemma lem5141547 (s : real -> Prop) : (term282 s) = (term279 s).
Proof. exact (MK_COMB (@lem5141546 s) (@lem5141545 s)). Qed.
Lemma lem5141548 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5141549 (s : real -> Prop) : (term287 s) = (term288 s).
Proof. exact (MK_COMB (@lem5141548) (@lem5141547 s)). Qed.
Lemma lem5141550 (x : real -> real) (s : real -> Prop) : (term284 s x) = (term275 x s).
Proof. exact (eq_refl (term284 s x)). Qed.
Lemma lem5141551 (s : real -> Prop) : (term189 s) = (term189 s).
Proof. exact (eq_refl (term189 s)). Qed.
Lemma lem5141552 (x : real -> real) (s : real -> Prop) : (term289 s x) = (term290 x s).
Proof. exact (MK_COMB (@lem5141551 s) (@lem5141550 x s)). Qed.
Lemma lem5141553 (s : real -> Prop) : (term291 s) = (term292 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5141552 x s)). Qed.
Lemma lem5141554 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5141555 (s : real -> Prop) : (term283 s) = (term293 s).
Proof. exact (MK_COMB (@lem5141554) (@lem5141553 s)). Qed.
Lemma lem5141556 (s : real -> Prop) : ((term282 s) = (term283 s)) = ((term279 s) = (term293 s)).
Proof. exact (MK_COMB (@lem5141549 s) (@lem5141555 s)). Qed.
Lemma lem5141557 (s : real -> Prop) : (term279 s) = (term293 s).
Proof. exact (EQ_MP (@lem5141556 s) (@lem5141541 s)). Qed.
Lemma lem5141558 (s : real -> Prop) : (term190 s) = (term293 s).
Proof. exact (TRANS (@lem5141537 s) (@lem5141557 s)). Qed.
Lemma lem5141559 (s : real -> Prop) : (term194 s) = (term294 s).
Proof. exact (MK_COMB (@lem5141477 s) (@lem5141558 s)). Qed.
Lemma lem5141561 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term295 A P Q) = (term296 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5141562 (P : type1028) (Q : type1028) : (term297 P Q) = (term298 P Q).
Proof. exact (@lem5141561 (real -> real) P Q). Qed.
Lemma lem5141563 (s : real -> Prop) : (term299 s) = (term300 s).
Proof. exact (@lem5141562 (term235 s) (term292 s)). Qed.
Lemma lem5141564 (s : real -> Prop) (x : real -> real) : (term301 s x) = (term233 s x).
Proof. exact (eq_refl (term301 s x)). Qed.
Lemma lem5141565 (s : real -> Prop) : (term302 s) = (term235 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5141564 s x)). Qed.
Lemma lem5141566 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5141567 (s : real -> Prop) : (term303 s) = (term236 s).
Proof. exact (MK_COMB (@lem5141566) (@lem5141565 s)). Qed.
Lemma lem5141568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5141569 (s : real -> Prop) : (term304 s) = (term237 s).
Proof. exact (MK_COMB (@lem5141568) (@lem5141567 s)). Qed.
Lemma lem5141570 (x : real -> real) (s : real -> Prop) : (term305 s x) = (term290 x s).
Proof. exact (eq_refl (term305 s x)). Qed.
Lemma lem5141571 (s : real -> Prop) : (term306 s) = (term292 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5141570 x s)). Qed.
Lemma lem5141572 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5141573 (s : real -> Prop) : (term307 s) = (term293 s).
Proof. exact (MK_COMB (@lem5141572) (@lem5141571 s)). Qed.
Lemma lem5141574 (s : real -> Prop) : (term299 s) = (term294 s).
Proof. exact (MK_COMB (@lem5141569 s) (@lem5141573 s)). Qed.
Lemma lem5141575 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5141576 (s : real -> Prop) : (term308 s) = (term309 s).
Proof. exact (MK_COMB (@lem5141575) (@lem5141574 s)). Qed.
Lemma lem5141577 (s : real -> Prop) (x : real -> real) : (term301 s x) = (term233 s x).
Proof. exact (eq_refl (term301 s x)). Qed.
Lemma lem5141578 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5141579 (s : real -> Prop) (x : real -> real) : (term310 s x) = (term311 s x).
Proof. exact (MK_COMB (@lem5141578) (@lem5141577 s x)). Qed.
Lemma lem5141580 (x : real -> real) (s : real -> Prop) : (term305 s x) = (term290 x s).
Proof. exact (eq_refl (term305 s x)). Qed.
Lemma lem5141581 (x : real -> real) (s : real -> Prop) : (term312 s x) = (term313 x s).
Proof. exact (MK_COMB (@lem5141579 s x) (@lem5141580 x s)). Qed.
Lemma lem5141582 (s : real -> Prop) : (term314 s) = (term315 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5141581 x s)). Qed.
Lemma lem5141583 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5141584 (s : real -> Prop) : (term300 s) = (term316 s).
Proof. exact (MK_COMB (@lem5141583) (@lem5141582 s)). Qed.
Lemma lem5141585 (s : real -> Prop) : ((term299 s) = (term300 s)) = ((term294 s) = (term316 s)).
Proof. exact (MK_COMB (@lem5141576 s) (@lem5141584 s)). Qed.
Lemma lem5141586 (s : real -> Prop) : (term294 s) = (term316 s).
Proof. exact (EQ_MP (@lem5141585 s) (@lem5141563 s)). Qed.
Lemma lem5141587 (s : real -> Prop) : (term194 s) = (term316 s).
Proof. exact (TRANS (@lem5141559 s) (@lem5141586 s)). Qed.
Lemma lem5141588 : term195 = term317.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5141587 s)). Qed.
Lemma lem5141589 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5141590 : term196 = term318.
Proof. exact (MK_COMB (@lem5141589) (@lem5141588)). Qed.
Lemma lem5141592 {A B : Type'} (P : type1413 A B) : (term197 A B P) = (term198 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5141593 (P : type1017) : (term319 P) = (term320 P).
Proof. exact (@lem5141592 (real -> Prop) (real -> real) P). Qed.
Lemma lem5141594 : term321 = term322.
Proof. exact (@lem5141593 term323). Qed.
Lemma lem5141595 (s : real -> Prop) : (term324 s) = (term315 s).
Proof. exact (eq_refl (term324 s)). Qed.
Lemma lem5141596 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5141597 (s : real -> Prop) (x : real -> real) : (term325 s x) = (term326 s x).
Proof. exact (MK_COMB (@lem5141595 s) (@lem5141596 x)). Qed.
Lemma lem5141598 (x : real -> real) (s : real -> Prop) : (term326 s x) = (term313 x s).
Proof. exact (eq_refl (term326 s x)). Qed.
Lemma lem5141599 (x : real -> real) (s : real -> Prop) : (term325 s x) = (term313 x s).
Proof. exact (TRANS (@lem5141597 s x) (@lem5141598 x s)). Qed.
Lemma lem5141600 (s : real -> Prop) : (term327 s) = (term315 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5141599 x s)). Qed.
Lemma lem5141601 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5141602 (s : real -> Prop) : (term328 s) = (term316 s).
Proof. exact (MK_COMB (@lem5141601) (@lem5141600 s)). Qed.
Lemma lem5141603 : term329 = term317.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5141602 s)). Qed.
Lemma lem5141604 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5141605 : term321 = term318.
Proof. exact (MK_COMB (@lem5141604) (@lem5141603)). Qed.
Lemma lem5141606 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5141607 : term330 = term331.
Proof. exact (MK_COMB (@lem5141606) (@lem5141605)). Qed.
Lemma lem5141608 (s : real -> Prop) : (term324 s) = (term315 s).
Proof. exact (eq_refl (term324 s)). Qed.
Lemma lem5141609 (x : type1021) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5141610 (x : type1021) (s : real -> Prop) : (term332 x s) = (term333 x s).
Proof. exact (MK_COMB (@lem5141608 s) (@lem5141609 x s)). Qed.
Lemma lem5141611 (x : type1021) (s : real -> Prop) : (term333 x s) = (term334 x s).
Proof. exact (eq_refl (term333 x s)). Qed.
Lemma lem5141612 (x : type1021) (s : real -> Prop) : (term332 x s) = (term334 x s).
Proof. exact (TRANS (@lem5141610 x s) (@lem5141611 x s)). Qed.
Lemma lem5141613 (x : type1021) : (term335 x) = (term336 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5141612 x s)). Qed.
Lemma lem5141614 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5141615 (x : type1021) : (term337 x) = (term338 x).
Proof. exact (MK_COMB (@lem5141614) (@lem5141613 x)). Qed.
Lemma lem5141616 : term339 = term340.
Proof. exact (fun_ext (fun x : type1021 => @lem5141615 x)). Qed.
Lemma lem5141617 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5141618 : term322 = term341.
Proof. exact (MK_COMB (@lem5141617) (@lem5141616)). Qed.
Lemma lem5141619 : (term321 = term322) = (term318 = term341).
Proof. exact (MK_COMB (@lem5141607) (@lem5141618)). Qed.
Lemma lem5141620 : term318 = term341.
Proof. exact (EQ_MP (@lem5141619) (@lem5141594)). Qed.
Lemma lem5141622 : term196 = term341.
Proof. exact (TRANS (@lem5141590) (@lem5141620)). Qed.
Lemma lem5141623 : term66 = term341.
Proof. exact (TRANS (@lem5141177) (@lem5141622)). Qed.
Lemma lem5141624 (h1 : term66) : term341.
Proof. exact (EQ_MP (@lem5141623) (@lem5140819 h1)). Qed.
Lemma lem5141701 (y : real) (x : real) : (term342 y x) = (term343 y x).
Proof. exact (@lem17045 (real_le x y) (real_le y x)). Qed.
Lemma lem5141706 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5141707 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5141708 (y : real) (x : real) : (term344 y x) = (term345 y x).
Proof. exact (MK_COMB (@lem5141707) (@lem5141701 y x)). Qed.
Lemma lem5141709 (x : real) (y : real) : (term346 x y) = (term347 x y).
Proof. exact (MK_COMB (@lem5141708 y x) (@lem5141706 x y)). Qed.
Lemma lem5141714 (x : real) (y : real) : (term348 x y) = (term348 x y).
Proof. exact (eq_refl (term348 x y)). Qed.
Lemma lem5141715 (x : real) (y : real) : (term349 x y) = (term350 x y).
Proof. exact (MK_COMB (@lem5141714 x y) (@lem5141709 x y)). Qed.
Lemma lem5141716 (x : real) (y : real) : ((term37 y x) = (x = y)) = (term349 x y).
Proof. exact (@lem17784 (term37 y x) (x = y)). Qed.
Lemma lem5141717 (x : real) (y : real) : ((term37 y x) = (x = y)) = (term350 x y).
Proof. exact (TRANS (@lem5141716 x y) (@lem5141715 x y)). Qed.
Lemma lem5141718 (x : real) : (term38 x) = (term351 x).
Proof. exact (fun_ext (fun y : real => @lem5141717 x y)). Qed.
Lemma lem5141719 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141720 (x : real) : (term39 x) = (term352 x).
Proof. exact (MK_COMB (@lem5141719) (@lem5141718 x)). Qed.
Lemma lem5141721 : term40 = term353.
Proof. exact (fun_ext (fun x : real => @lem5141720 x)). Qed.
Lemma lem5141722 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141723 : term21 = term354.
Proof. exact (MK_COMB (@lem5141722) (@lem5141721)). Qed.
Lemma lem5141729 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term355 A P Q) = (term356 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5141730 (P : real -> Prop) (Q : real -> Prop) : (term357 P Q) = (term358 P Q).
Proof. exact (@lem5141729 real P Q). Qed.
Lemma lem5141731 (x : real) : (term359 x) = (term360 x).
Proof. exact (@lem5141730 (term361 x) (term362 x)). Qed.
Lemma lem5141732 (x : real) (y : real) : (term363 x y) = (term364 x y).
Proof. exact (eq_refl (term363 x y)). Qed.
Lemma lem5141733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5141734 (x : real) (y : real) : (term365 x y) = (term348 x y).
Proof. exact (MK_COMB (@lem5141733) (@lem5141732 x y)). Qed.
Lemma lem5141735 (x : real) (y : real) : (term366 x y) = (term347 x y).
Proof. exact (eq_refl (term366 x y)). Qed.
Lemma lem5141736 (x : real) (y : real) : (term367 x y) = (term350 x y).
Proof. exact (MK_COMB (@lem5141734 x y) (@lem5141735 x y)). Qed.
Lemma lem5141737 (x : real) : (term368 x) = (term351 x).
Proof. exact (fun_ext (fun y : real => @lem5141736 x y)). Qed.
Lemma lem5141738 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141739 (x : real) : (term359 x) = (term352 x).
Proof. exact (MK_COMB (@lem5141738) (@lem5141737 x)). Qed.
Lemma lem5141740 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5141741 (x : real) : (term369 x) = (term370 x).
Proof. exact (MK_COMB (@lem5141740) (@lem5141739 x)). Qed.
Lemma lem5141742 (x : real) (y : real) : (term363 x y) = (term364 x y).
Proof. exact (eq_refl (term363 x y)). Qed.
Lemma lem5141743 (x : real) : (term371 x) = (term361 x).
Proof. exact (fun_ext (fun y : real => @lem5141742 x y)). Qed.
Lemma lem5141744 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141745 (x : real) : (term372 x) = (term373 x).
Proof. exact (MK_COMB (@lem5141744) (@lem5141743 x)). Qed.
Lemma lem5141746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5141747 (x : real) : (term374 x) = (term375 x).
Proof. exact (MK_COMB (@lem5141746) (@lem5141745 x)). Qed.
Lemma lem5141748 (x : real) (y : real) : (term366 x y) = (term347 x y).
Proof. exact (eq_refl (term366 x y)). Qed.
Lemma lem5141749 (x : real) : (term376 x) = (term362 x).
Proof. exact (fun_ext (fun y : real => @lem5141748 x y)). Qed.
Lemma lem5141750 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141751 (x : real) : (term377 x) = (term378 x).
Proof. exact (MK_COMB (@lem5141750) (@lem5141749 x)). Qed.
Lemma lem5141752 (x : real) : (term360 x) = (term379 x).
Proof. exact (MK_COMB (@lem5141747 x) (@lem5141751 x)). Qed.
Lemma lem5141753 (x : real) : ((term359 x) = (term360 x)) = ((term352 x) = (term379 x)).
Proof. exact (MK_COMB (@lem5141741 x) (@lem5141752 x)). Qed.
Lemma lem5141754 (x : real) : (term352 x) = (term379 x).
Proof. exact (EQ_MP (@lem5141753 x) (@lem5141731 x)). Qed.
Lemma lem5141851 : term353 = term380.
Proof. exact (fun_ext (fun x : real => @lem5141754 x)). Qed.
Lemma lem5141852 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141853 : term354 = term381.
Proof. exact (MK_COMB (@lem5141852) (@lem5141851)). Qed.
Lemma lem5141855 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term355 A P Q) = (term356 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem5141856 (P : real -> Prop) (Q : real -> Prop) : (term357 P Q) = (term358 P Q).
Proof. exact (@lem5141855 real P Q). Qed.
Lemma lem5141857 : term382 = term383.
Proof. exact (@lem5141856 term384 term385). Qed.
Lemma lem5141858 (x : real) : (term386 x) = (term373 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem5141859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5141860 (x : real) : (term387 x) = (term375 x).
Proof. exact (MK_COMB (@lem5141859) (@lem5141858 x)). Qed.
Lemma lem5141861 (x : real) : (term388 x) = (term378 x).
Proof. exact (eq_refl (term388 x)). Qed.
Lemma lem5141862 (x : real) : (term389 x) = (term379 x).
Proof. exact (MK_COMB (@lem5141860 x) (@lem5141861 x)). Qed.
Lemma lem5141863 : term390 = term380.
Proof. exact (fun_ext (fun x : real => @lem5141862 x)). Qed.
Lemma lem5141864 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141865 : term382 = term381.
Proof. exact (MK_COMB (@lem5141864) (@lem5141863)). Qed.
Lemma lem5141866 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5141867 : term391 = term392.
Proof. exact (MK_COMB (@lem5141866) (@lem5141865)). Qed.
Lemma lem5141868 (x : real) : (term386 x) = (term373 x).
Proof. exact (eq_refl (term386 x)). Qed.
Lemma lem5141869 : term393 = term384.
Proof. exact (fun_ext (fun x : real => @lem5141868 x)). Qed.
Lemma lem5141870 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141871 : term394 = term395.
Proof. exact (MK_COMB (@lem5141870) (@lem5141869)). Qed.
Lemma lem5141872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5141873 : term396 = term397.
Proof. exact (MK_COMB (@lem5141872) (@lem5141871)). Qed.
Lemma lem5141874 (x : real) : (term388 x) = (term378 x).
Proof. exact (eq_refl (term388 x)). Qed.
Lemma lem5141875 : term398 = term385.
Proof. exact (fun_ext (fun x : real => @lem5141874 x)). Qed.
Lemma lem5141876 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5141877 : term399 = term400.
Proof. exact (MK_COMB (@lem5141876) (@lem5141875)). Qed.
Lemma lem5141878 : term383 = term401.
Proof. exact (MK_COMB (@lem5141873) (@lem5141877)). Qed.
Lemma lem5141879 : (term382 = term383) = (term381 = term401).
Proof. exact (MK_COMB (@lem5141867) (@lem5141878)). Qed.
Lemma lem5141880 : term381 = term401.
Proof. exact (EQ_MP (@lem5141879) (@lem5141857)). Qed.
Lemma lem5141987 : term354 = term401.
Proof. exact (TRANS (@lem5141853) (@lem5141880)). Qed.
Lemma lem5141988 : term21 = term401.
Proof. exact (TRANS (@lem5141723) (@lem5141987)). Qed.
Lemma lem5141989 (h1 : term21) : term401.
Proof. exact (EQ_MP (@lem5141988) (@lem5140821 h1)). Qed.
Lemma lem5141990 (x : type1021) (h1 : term338 x) : term338 x.
Proof. exact (h1). Qed.
Lemma lem5141991 (b : real) (s : real -> Prop) (h1 : term152 b s) : term152 b s.
Proof. exact (h1). Qed.
Lemma lem5141992 (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term149 b x' s.
Proof. exact (h1). Qed.
Lemma lem5142006 (s : real -> Prop) (h1 : term9 s) : term9 s.
Proof. exact (h1). Qed.
Lemma lem5142051 (x : real) (y : real) : (term347 x y) = (term347 x y).
Proof. exact (eq_refl (term347 x y)). Qed.
Lemma lem5142052 (x : real) : (term362 x) = (term362 x).
Proof. exact (fun_ext (fun y : real => @lem5142051 x y)). Qed.
Lemma lem5142053 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142054 (x : real) : (term378 x) = (term378 x).
Proof. exact (MK_COMB (@lem5142053) (@lem5142052 x)). Qed.
Lemma lem5142055 : term385 = term385.
Proof. exact (fun_ext (fun x : real => @lem5142054 x)). Qed.
Lemma lem5142056 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142057 : term400 = term400.
Proof. exact (MK_COMB (@lem5142056) (@lem5142055)). Qed.
Lemma lem5142080 (x : real) (y : real) : (term364 x y) = (term364 x y).
Proof. exact (eq_refl (term364 x y)). Qed.
Lemma lem5142081 (x : real) : (term361 x) = (term361 x).
Proof. exact (fun_ext (fun y : real => @lem5142080 x y)). Qed.
Lemma lem5142082 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142083 (x : real) : (term373 x) = (term373 x).
Proof. exact (MK_COMB (@lem5142082) (@lem5142081 x)). Qed.
Lemma lem5142084 : term384 = term384.
Proof. exact (fun_ext (fun x : real => @lem5142083 x)). Qed.
Lemma lem5142085 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142086 : term395 = term395.
Proof. exact (MK_COMB (@lem5142085) (@lem5142084)). Qed.
Lemma lem5142087 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5142088 : term397 = term397.
Proof. exact (MK_COMB (@lem5142087) (@lem5142086)). Qed.
Lemma lem5142089 : term401 = term401.
Proof. exact (MK_COMB (@lem5142088) (@lem5142057)). Qed.
Lemma lem5142090 (h1 : term21) : term401.
Proof. exact (EQ_MP (@lem5142089) (@lem5141989 h1)). Qed.
Lemma lem5142123 (x : type1021) (s : real -> Prop) (b : real) : (term402 x s b) = (term402 x s b).
Proof. exact (eq_refl (term402 x s b)). Qed.
Lemma lem5142124 (x : type1021) (s : real -> Prop) : (term403 x s) = (term403 x s).
Proof. exact (fun_ext (fun b : real => @lem5142123 x s b)). Qed.
Lemma lem5142125 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142126 (x : type1021) (s : real -> Prop) : (term404 x s) = (term404 x s).
Proof. exact (MK_COMB (@lem5142125) (@lem5142124 x s)). Qed.
Lemma lem5142143 (x : real) (s : real -> Prop) : (term180 x s) = (term180 x s).
Proof. exact (eq_refl (term180 x s)). Qed.
Lemma lem5142144 (s : real -> Prop) : (term181 s) = (term181 s).
Proof. exact (fun_ext (fun x : real => @lem5142143 x s)). Qed.
Lemma lem5142145 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142146 (s : real -> Prop) : (term182 s) = (term182 s).
Proof. exact (MK_COMB (@lem5142145) (@lem5142144 s)). Qed.
Lemma lem5142147 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5142148 (s : real -> Prop) : (term189 s) = (term189 s).
Proof. exact (MK_COMB (@lem5142147) (@lem5142146 s)). Qed.
Lemma lem5142149 (x : type1021) (s : real -> Prop) : (term405 x s) = (term405 x s).
Proof. exact (MK_COMB (@lem5142148 s) (@lem5142126 x s)). Qed.
Lemma lem5142172 (x : type1021) (s : real -> Prop) (b : real) : (term406 x s b) = (term406 x s b).
Proof. exact (eq_refl (term406 x s b)). Qed.
Lemma lem5142173 (x : type1021) (s : real -> Prop) : (term407 x s) = (term407 x s).
Proof. exact (fun_ext (fun b : real => @lem5142172 x s b)). Qed.
Lemma lem5142174 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142175 (x : type1021) (s : real -> Prop) : (term408 x s) = (term408 x s).
Proof. exact (MK_COMB (@lem5142174) (@lem5142173 x s)). Qed.
Lemma lem5142182 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (eq_refl (term175 s)). Qed.
Lemma lem5142183 (x : type1021) (s : real -> Prop) : (term409 x s) = (term409 x s).
Proof. exact (MK_COMB (@lem5142182 s) (@lem5142175 x s)). Qed.
Lemma lem5142184 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5142185 (x : type1021) (s : real -> Prop) : (term410 x s) = (term410 x s).
Proof. exact (MK_COMB (@lem5142184) (@lem5142183 x s)). Qed.
Lemma lem5142186 (x : type1021) (s : real -> Prop) : (term334 x s) = (term334 x s).
Proof. exact (MK_COMB (@lem5142185 x s) (@lem5142149 x s)). Qed.
Lemma lem5142187 (x : type1021) : (term336 x) = (term336 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5142186 x s)). Qed.
Lemma lem5142188 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5142189 (x : type1021) : (term338 x) = (term338 x).
Proof. exact (MK_COMB (@lem5142188) (@lem5142187 x)). Qed.
Lemma lem5142190 (x : type1021) (h1 : term338 x) : term338 x.
Proof. exact (EQ_MP (@lem5142189 x) (@lem5141990 x h1)). Qed.
Lemma lem5142219 (x' : real) (s : real -> Prop) : (term113 x' s) = (term113 x' s).
Proof. exact (eq_refl (term113 x' s)). Qed.
Lemma lem5142234 (s : real -> Prop) (x : real) (b : real) : (term73 s x b) = (term73 s x b).
Proof. exact (eq_refl (term73 s x b)). Qed.
Lemma lem5142235 (s : real -> Prop) (b : real) : (term74 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5142234 s x b)). Qed.
Lemma lem5142236 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142237 (s : real -> Prop) (b : real) : (term75 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5142236) (@lem5142235 s b)). Qed.
Lemma lem5142244 (b : real) (s : real -> Prop) : (term69 b s) = (term69 b s).
Proof. exact (eq_refl (term69 b s)). Qed.
Lemma lem5142245 (s : real -> Prop) (b : real) : (term76 s b) = (term76 s b).
Proof. exact (MK_COMB (@lem5142244 b s) (@lem5142237 s b)). Qed.
Lemma lem5142246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5142247 (s : real -> Prop) (b : real) : (term131 s b) = (term131 s b).
Proof. exact (MK_COMB (@lem5142246) (@lem5142245 s b)). Qed.
Lemma lem5142248 (b : real) (x' : real) (s : real -> Prop) : (term149 b x' s) = (term149 b x' s).
Proof. exact (MK_COMB (@lem5142247 s b) (@lem5142219 x' s)). Qed.
Lemma lem5142249 (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term149 b x' s.
Proof. exact (EQ_MP (@lem5142248 b x' s) (@lem5141992 b x' s h1)). Qed.
Lemma lem5142250 (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term113 x' s.
Proof. exact (proj2 (@lem5142249 b x' s h1)). Qed.
Lemma lem5142251 (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term76 s b.
Proof. exact (proj1 (@lem5142249 b x' s h1)). Qed.
Lemma lem5142252 (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term75 s b.
Proof. exact (proj2 (@lem5142251 b x' s h1)). Qed.
Lemma lem5142254 (h1 : term21) : term400.
Proof. exact (proj2 (@lem5142090 h1)). Qed.
Lemma lem5142259 (x' : real) (s : real -> Prop) (h1 : term80 x' s) : term80 x' s.
Proof. exact (h1). Qed.
Lemma lem5142279 {A : Type'} (P : Prop) (Q : A -> Prop) : (term411 A P Q) = (term412 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5142280 (P : Prop) (Q : real -> Prop) : (term413 P Q) = (term414 P Q).
Proof. exact (@lem5142279 real P Q). Qed.
Lemma lem5142281 (x : type1021) (s : real -> Prop) : (term415 x s) = (term416 x s).
Proof. exact (@lem5142280 (s = (@EMPTY real)) (term407 x s)). Qed.
Lemma lem5142282 (x : type1021) (s : real -> Prop) (b : real) : (term417 x s b) = (term406 x s b).
Proof. exact (eq_refl (term417 x s b)). Qed.
Lemma lem5142283 (x : type1021) (s : real -> Prop) : (term418 x s) = (term407 x s).
Proof. exact (fun_ext (fun b : real => @lem5142282 x s b)). Qed.
Lemma lem5142284 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142285 (x : type1021) (s : real -> Prop) : (term419 x s) = (term408 x s).
Proof. exact (MK_COMB (@lem5142284) (@lem5142283 x s)). Qed.
Lemma lem5142286 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (eq_refl (term175 s)). Qed.
Lemma lem5142287 (x : type1021) (s : real -> Prop) : (term415 x s) = (term409 x s).
Proof. exact (MK_COMB (@lem5142286 s) (@lem5142285 x s)). Qed.
Lemma lem5142288 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5142289 (x : type1021) (s : real -> Prop) : (term420 x s) = (term421 x s).
Proof. exact (MK_COMB (@lem5142288) (@lem5142287 x s)). Qed.
Lemma lem5142290 (x : type1021) (s : real -> Prop) (b : real) : (term417 x s b) = (term406 x s b).
Proof. exact (eq_refl (term417 x s b)). Qed.
Lemma lem5142291 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (eq_refl (term175 s)). Qed.
Lemma lem5142292 (x : type1021) (s : real -> Prop) (b : real) : (term422 x s b) = (term423 x s b).
Proof. exact (MK_COMB (@lem5142291 s) (@lem5142290 x s b)). Qed.
Lemma lem5142293 (x : type1021) (s : real -> Prop) : (term424 x s) = (term425 x s).
Proof. exact (fun_ext (fun b : real => @lem5142292 x s b)). Qed.
Lemma lem5142294 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142295 (x : type1021) (s : real -> Prop) : (term416 x s) = (term426 x s).
Proof. exact (MK_COMB (@lem5142294) (@lem5142293 x s)). Qed.
Lemma lem5142296 (x : type1021) (s : real -> Prop) : ((term415 x s) = (term416 x s)) = ((term409 x s) = (term426 x s)).
Proof. exact (MK_COMB (@lem5142289 x s) (@lem5142295 x s)). Qed.
Lemma lem5142297 (x : type1021) (s : real -> Prop) : (term409 x s) = (term426 x s).
Proof. exact (EQ_MP (@lem5142296 x s) (@lem5142281 x s)). Qed.
Lemma lem5142298 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5142299 (x : type1021) (s : real -> Prop) : (term410 x s) = (term427 x s).
Proof. exact (MK_COMB (@lem5142298) (@lem5142297 x s)). Qed.
Lemma lem5142301 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term356 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5142302 (P : real -> Prop) (Q : real -> Prop) : (term358 P Q) = (term357 P Q).
Proof. exact (@lem5142301 real P Q). Qed.
Lemma lem5142303 (x : type1021) (s : real -> Prop) : (term428 x s) = (term429 x s).
Proof. exact (@lem5142302 (term181 s) (term403 x s)). Qed.
Lemma lem5142304 (b : real) (s : real -> Prop) : (term430 s b) = (term180 b s).
Proof. exact (eq_refl (term430 s b)). Qed.
Lemma lem5142305 (s : real -> Prop) : (term431 s) = (term181 s).
Proof. exact (fun_ext (fun b : real => @lem5142304 b s)). Qed.
Lemma lem5142306 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142307 (s : real -> Prop) : (term432 s) = (term182 s).
Proof. exact (MK_COMB (@lem5142306) (@lem5142305 s)). Qed.
Lemma lem5142308 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5142309 (s : real -> Prop) : (term433 s) = (term189 s).
Proof. exact (MK_COMB (@lem5142308) (@lem5142307 s)). Qed.
Lemma lem5142310 (x : type1021) (s : real -> Prop) (b : real) : (term434 x s b) = (term402 x s b).
Proof. exact (eq_refl (term434 x s b)). Qed.
Lemma lem5142311 (x : type1021) (s : real -> Prop) : (term435 x s) = (term403 x s).
Proof. exact (fun_ext (fun b : real => @lem5142310 x s b)). Qed.
Lemma lem5142312 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142313 (x : type1021) (s : real -> Prop) : (term436 x s) = (term404 x s).
Proof. exact (MK_COMB (@lem5142312) (@lem5142311 x s)). Qed.
Lemma lem5142314 (x : type1021) (s : real -> Prop) : (term428 x s) = (term405 x s).
Proof. exact (MK_COMB (@lem5142309 s) (@lem5142313 x s)). Qed.
Lemma lem5142315 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5142316 (x : type1021) (s : real -> Prop) : (term437 x s) = (term438 x s).
Proof. exact (MK_COMB (@lem5142315) (@lem5142314 x s)). Qed.
Lemma lem5142317 (b : real) (s : real -> Prop) : (term430 s b) = (term180 b s).
Proof. exact (eq_refl (term430 s b)). Qed.
Lemma lem5142318 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5142319 (b : real) (s : real -> Prop) : (term439 s b) = (term440 b s).
Proof. exact (MK_COMB (@lem5142318) (@lem5142317 b s)). Qed.
Lemma lem5142320 (x : type1021) (s : real -> Prop) (b : real) : (term434 x s b) = (term402 x s b).
Proof. exact (eq_refl (term434 x s b)). Qed.
Lemma lem5142321 (x : type1021) (s : real -> Prop) (b : real) : (term441 x s b) = (term442 x s b).
Proof. exact (MK_COMB (@lem5142319 b s) (@lem5142320 x s b)). Qed.
Lemma lem5142322 (x : type1021) (s : real -> Prop) : (term443 x s) = (term444 x s).
Proof. exact (fun_ext (fun b : real => @lem5142321 x s b)). Qed.
Lemma lem5142323 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142324 (x : type1021) (s : real -> Prop) : (term429 x s) = (term445 x s).
Proof. exact (MK_COMB (@lem5142323) (@lem5142322 x s)). Qed.
Lemma lem5142325 (x : type1021) (s : real -> Prop) : ((term428 x s) = (term429 x s)) = ((term405 x s) = (term445 x s)).
Proof. exact (MK_COMB (@lem5142316 x s) (@lem5142324 x s)). Qed.
Lemma lem5142326 (x : type1021) (s : real -> Prop) : (term405 x s) = (term445 x s).
Proof. exact (EQ_MP (@lem5142325 x s) (@lem5142303 x s)). Qed.
Lemma lem5142329 (x : type1021) (s : real -> Prop) : (term446 x s) = (term446 x s).
Proof. exact (eq_refl (term446 x s)). Qed.
Lemma lem5142330 (x : type1021) (s : real -> Prop) : (term446 x s) = ((term405 x s) = (term445 x s)).
Proof. exact (eq_refl (term446 x s)). Qed.
Lemma lem5142331 (x : type1021) (s : real -> Prop) : (term447 x s) = (term447 x s).
Proof. exact (eq_refl (term447 x s)). Qed.
Lemma lem5142332 (x : type1021) (s : real -> Prop) : ((term446 x s) = (term446 x s)) = ((term446 x s) = ((term405 x s) = (term445 x s))).
Proof. exact (MK_COMB (@lem5142331 x s) (@lem5142330 x s)). Qed.
Lemma lem5142333 (x : type1021) (s : real -> Prop) : (term446 x s) = ((term405 x s) = (term445 x s)).
Proof. exact (eq_refl (term446 x s)). Qed.
Lemma lem5142334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5142335 (x : type1021) (s : real -> Prop) : (term447 x s) = (term448 x s).
Proof. exact (MK_COMB (@lem5142334) (@lem5142333 x s)). Qed.
Lemma lem5142336 (x : type1021) (s : real -> Prop) : ((term405 x s) = (term445 x s)) = ((term405 x s) = (term445 x s)).
Proof. exact (eq_refl ((term405 x s) = (term445 x s))). Qed.
Lemma lem5142337 (x : type1021) (s : real -> Prop) : ((term446 x s) = ((term405 x s) = (term445 x s))) = (((term405 x s) = (term445 x s)) = ((term405 x s) = (term445 x s))).
Proof. exact (MK_COMB (@lem5142335 x s) (@lem5142336 x s)). Qed.
Lemma lem5142338 (x : type1021) (s : real -> Prop) : ((term446 x s) = (term446 x s)) = (((term405 x s) = (term445 x s)) = ((term405 x s) = (term445 x s))).
Proof. exact (TRANS (@lem5142332 x s) (@lem5142337 x s)). Qed.
Lemma lem5142339 (x : type1021) (s : real -> Prop) : ((term405 x s) = (term445 x s)) = ((term405 x s) = (term445 x s)).
Proof. exact (EQ_MP (@lem5142338 x s) (@lem5142329 x s)). Qed.
Lemma lem5142340 (x : type1021) (s : real -> Prop) : (term405 x s) = (term445 x s).
Proof. exact (EQ_MP (@lem5142339 x s) (@lem5142326 x s)). Qed.
Lemma lem5142341 (x : type1021) (s : real -> Prop) : (term334 x s) = (term449 x s).
Proof. exact (MK_COMB (@lem5142299 x s) (@lem5142340 x s)). Qed.
Lemma lem5142343 {A : Type'} (P : A -> Prop) (Q : Prop) : (term450 A P Q) = (term451 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5142344 (P : real -> Prop) (Q : Prop) : (term452 P Q) = (term453 P Q).
Proof. exact (@lem5142343 real P Q). Qed.
Lemma lem5142345 (x : type1021) (s : real -> Prop) : (term454 x s) = (term455 x s).
Proof. exact (@lem5142344 (term425 x s) (term445 x s)). Qed.
Lemma lem5142346 (x : type1021) (s : real -> Prop) (b : real) : (term456 x s b) = (term423 x s b).
Proof. exact (eq_refl (term456 x s b)). Qed.
Lemma lem5142347 (x : type1021) (s : real -> Prop) : (term457 x s) = (term425 x s).
Proof. exact (fun_ext (fun b : real => @lem5142346 x s b)). Qed.
Lemma lem5142348 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142349 (x : type1021) (s : real -> Prop) : (term458 x s) = (term426 x s).
Proof. exact (MK_COMB (@lem5142348) (@lem5142347 x s)). Qed.
Lemma lem5142350 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5142351 (x : type1021) (s : real -> Prop) : (term459 x s) = (term427 x s).
Proof. exact (MK_COMB (@lem5142350) (@lem5142349 x s)). Qed.
Lemma lem5142352 (x : type1021) (s : real -> Prop) : (term445 x s) = (term445 x s).
Proof. exact (eq_refl (term445 x s)). Qed.
Lemma lem5142353 (x : type1021) (s : real -> Prop) : (term454 x s) = (term449 x s).
Proof. exact (MK_COMB (@lem5142351 x s) (@lem5142352 x s)). Qed.
Lemma lem5142354 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5142355 (x : type1021) (s : real -> Prop) : (term460 x s) = (term461 x s).
Proof. exact (MK_COMB (@lem5142354) (@lem5142353 x s)). Qed.
Lemma lem5142356 (x : type1021) (s : real -> Prop) (b : real) : (term456 x s b) = (term423 x s b).
Proof. exact (eq_refl (term456 x s b)). Qed.
Lemma lem5142357 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5142358 (x : type1021) (s : real -> Prop) (b : real) : (term462 x s b) = (term463 x s b).
Proof. exact (MK_COMB (@lem5142357) (@lem5142356 x s b)). Qed.
Lemma lem5142359 (x : type1021) (s : real -> Prop) : (term445 x s) = (term445 x s).
Proof. exact (eq_refl (term445 x s)). Qed.
Lemma lem5142360 (b : real) (x : type1021) (s : real -> Prop) : (term464 b x s) = (term465 b x s).
Proof. exact (MK_COMB (@lem5142358 x s b) (@lem5142359 x s)). Qed.
Lemma lem5142361 (x : type1021) (s : real -> Prop) : (term466 x s) = (term467 x s).
Proof. exact (fun_ext (fun b : real => @lem5142360 b x s)). Qed.
Lemma lem5142362 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142363 (x : type1021) (s : real -> Prop) : (term455 x s) = (term468 x s).
Proof. exact (MK_COMB (@lem5142362) (@lem5142361 x s)). Qed.
Lemma lem5142364 (x : type1021) (s : real -> Prop) : ((term454 x s) = (term455 x s)) = ((term449 x s) = (term468 x s)).
Proof. exact (MK_COMB (@lem5142355 x s) (@lem5142363 x s)). Qed.
Lemma lem5142365 (x : type1021) (s : real -> Prop) : (term449 x s) = (term468 x s).
Proof. exact (EQ_MP (@lem5142364 x s) (@lem5142345 x s)). Qed.
Lemma lem5142367 {A : Type'} (P : Prop) (Q : A -> Prop) : (term411 A P Q) = (term412 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5142368 (P : Prop) (Q : real -> Prop) : (term413 P Q) = (term414 P Q).
Proof. exact (@lem5142367 real P Q). Qed.
Lemma lem5142369 (b : real) (x : type1021) (s : real -> Prop) : (term469 b x s) = (term470 b x s).
Proof. exact (@lem5142368 (term423 x s b) (term444 x s)). Qed.
Lemma lem5142370 (x : type1021) (s : real -> Prop) (b : real) : (term471 x s b) = (term442 x s b).
Proof. exact (eq_refl (term471 x s b)). Qed.
Lemma lem5142371 (x : type1021) (s : real -> Prop) : (term472 x s) = (term444 x s).
Proof. exact (fun_ext (fun b : real => @lem5142370 x s b)). Qed.
Lemma lem5142372 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142373 (x : type1021) (s : real -> Prop) : (term473 x s) = (term445 x s).
Proof. exact (MK_COMB (@lem5142372) (@lem5142371 x s)). Qed.
Lemma lem5142374 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term463 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5142375 (b : real) (x : type1021) (s : real -> Prop) : (term469 b x s) = (term465 b x s).
Proof. exact (MK_COMB (@lem5142374 x s b) (@lem5142373 x s)). Qed.
Lemma lem5142376 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5142377 (b : real) (x : type1021) (s : real -> Prop) : (term474 b x s) = (term475 b x s).
Proof. exact (MK_COMB (@lem5142376) (@lem5142375 b x s)). Qed.
Lemma lem5142378 (x : type1021) (s : real -> Prop) (b' : real) : (term471 x s b') = (term442 x s b').
Proof. exact (eq_refl (term471 x s b')). Qed.
Lemma lem5142379 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term463 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5142380 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term476 b x s b') = (term477 b x s b').
Proof. exact (MK_COMB (@lem5142379 x s b) (@lem5142378 x s b')). Qed.
Lemma lem5142381 (b : real) (x : type1021) (s : real -> Prop) : (term478 b x s) = (term479 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5142380 b x s b')). Qed.
Lemma lem5142382 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142383 (b : real) (x : type1021) (s : real -> Prop) : (term470 b x s) = (term480 b x s).
Proof. exact (MK_COMB (@lem5142382) (@lem5142381 b x s)). Qed.
Lemma lem5142384 (b : real) (x : type1021) (s : real -> Prop) : ((term469 b x s) = (term470 b x s)) = ((term465 b x s) = (term480 b x s)).
Proof. exact (MK_COMB (@lem5142377 b x s) (@lem5142383 b x s)). Qed.
Lemma lem5142385 (b : real) (x : type1021) (s : real -> Prop) : (term465 b x s) = (term480 b x s).
Proof. exact (EQ_MP (@lem5142384 b x s) (@lem5142369 b x s)). Qed.
Lemma lem5142386 (x : type1021) (s : real -> Prop) : (term467 x s) = (term481 x s).
Proof. exact (fun_ext (fun b : real => @lem5142385 b x s)). Qed.
Lemma lem5142387 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142388 (x : type1021) (s : real -> Prop) : (term468 x s) = (term482 x s).
Proof. exact (MK_COMB (@lem5142387) (@lem5142386 x s)). Qed.
Lemma lem5142389 (x : type1021) (s : real -> Prop) : (term449 x s) = (term482 x s).
Proof. exact (TRANS (@lem5142365 x s) (@lem5142388 x s)). Qed.
Lemma lem5142390 (x : type1021) (s : real -> Prop) : (term334 x s) = (term482 x s).
Proof. exact (TRANS (@lem5142341 x s) (@lem5142389 x s)). Qed.
Lemma lem5142391 (x : type1021) : (term336 x) = (term483 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5142390 x s)). Qed.
Lemma lem5142392 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5142393 (x : type1021) : (term338 x) = (term484 x).
Proof. exact (MK_COMB (@lem5142392) (@lem5142391 x)). Qed.
Lemma lem5142410 (x : type1021) (s : real -> Prop) (b' : real) : (term402 x s b') = (term485 x s b').
Proof. exact (@lem19699 (term486 x b' s) (term487 x s b') (term46 s b')). Qed.
Lemma lem5142419 (b' : real) (s : real -> Prop) : (term440 b' s) = (term440 b' s).
Proof. exact (eq_refl (term440 b' s)). Qed.
Lemma lem5142420 (x : type1021) (s : real -> Prop) (b' : real) : (term442 x s b') = (term488 x s b').
Proof. exact (MK_COMB (@lem5142419 b' s) (@lem5142410 x s b')). Qed.
Lemma lem5142437 (x : type1021) (s : real -> Prop) (b : real) : (term423 x s b) = (term489 x s b).
Proof. exact (@lem19490 (term486 x b s) (s = (@EMPTY real)) (term487 x s b)). Qed.
Lemma lem5142438 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5142439 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term490 x s b).
Proof. exact (MK_COMB (@lem5142438) (@lem5142437 x s b)). Qed.
Lemma lem5142440 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term477 b x s b') = (term491 b x s b').
Proof. exact (MK_COMB (@lem5142439 x s b) (@lem5142420 x s b')). Qed.
Lemma lem5142441 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term491 b x s b') = (term492 b x s b').
Proof. exact (@lem19490 (term180 b' s) (term489 x s b) (term485 x s b')). Qed.
Lemma lem5142442 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term493 b x s b') = (term494 b x s b').
Proof. exact (@lem19490 (term495 x s b') (term489 x s b) (term496 x s b')). Qed.
Lemma lem5142449 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term497 b x s b') = (term498 b x s b').
Proof. exact (@lem19699 (term499 x b s) (term500 x s b) (term496 x s b')). Qed.
Lemma lem5142456 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term501 b x s b') = (term502 b x s b').
Proof. exact (@lem19699 (term499 x b s) (term500 x s b) (term495 x s b')). Qed.
Lemma lem5142457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5142458 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term503 b x s b') = (term504 b x s b').
Proof. exact (MK_COMB (@lem5142457) (@lem5142456 b x s b')). Qed.
Lemma lem5142459 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term494 b x s b') = (term505 b x s b').
Proof. exact (MK_COMB (@lem5142458 b x s b') (@lem5142449 b x s b')). Qed.
Lemma lem5142460 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term493 b x s b') = (term505 b x s b').
Proof. exact (TRANS (@lem5142442 b x s b') (@lem5142459 b x s b')). Qed.
Lemma lem5142467 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term506 x b b' s) = (term507 x b b' s).
Proof. exact (@lem19699 (term499 x b s) (term500 x s b) (term180 b' s)). Qed.
Lemma lem5142468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5142469 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term508 x b b' s) = (term509 x b b' s).
Proof. exact (MK_COMB (@lem5142468) (@lem5142467 x b b' s)). Qed.
Lemma lem5142470 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term492 b x s b') = (term510 b x s b').
Proof. exact (MK_COMB (@lem5142469 x b b' s) (@lem5142460 b x s b')). Qed.
Lemma lem5142471 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term491 b x s b') = (term510 b x s b').
Proof. exact (TRANS (@lem5142441 b x s b') (@lem5142470 b x s b')). Qed.
Lemma lem5142472 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term477 b x s b') = (term510 b x s b').
Proof. exact (TRANS (@lem5142440 b x s b') (@lem5142471 b x s b')). Qed.
Lemma lem5142473 (b : real) (x : type1021) (s : real -> Prop) : (term479 b x s) = (term511 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5142472 b x s b')). Qed.
Lemma lem5142474 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142475 (b : real) (x : type1021) (s : real -> Prop) : (term480 b x s) = (term512 b x s).
Proof. exact (MK_COMB (@lem5142474) (@lem5142473 b x s)). Qed.
Lemma lem5142476 (x : type1021) (s : real -> Prop) : (term481 x s) = (term513 x s).
Proof. exact (fun_ext (fun b : real => @lem5142475 b x s)). Qed.
Lemma lem5142477 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142478 (x : type1021) (s : real -> Prop) : (term482 x s) = (term514 x s).
Proof. exact (MK_COMB (@lem5142477) (@lem5142476 x s)). Qed.
Lemma lem5142479 (x : type1021) : (term483 x) = (term515 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5142478 x s)). Qed.
Lemma lem5142480 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5142481 (x : type1021) : (term484 x) = (term516 x).
Proof. exact (MK_COMB (@lem5142480) (@lem5142479 x)). Qed.
Lemma lem5142482 (x : type1021) : (term338 x) = (term516 x).
Proof. exact (TRANS (@lem5142393 x) (@lem5142481 x)). Qed.
Lemma lem5142483 (x : type1021) (h1 : term338 x) : term516 x.
Proof. exact (EQ_MP (@lem5142482 x) (@lem5142190 x h1)). Qed.
Lemma lem5142495 (s : real -> Prop) (x : real) (b : real) : (term73 s x b) = (term73 s x b).
Proof. exact (eq_refl (term73 s x b)). Qed.
Lemma lem5142496 (s : real -> Prop) (b : real) : (term74 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5142495 s x b)). Qed.
Lemma lem5142497 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142499 (s : real -> Prop) (b : real) : (term75 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5142497) (@lem5142496 s b)). Qed.
Lemma lem5142500 (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term75 s b.
Proof. exact (EQ_MP (@lem5142499 s b) (@lem5142252 b x' s h1)). Qed.
Lemma lem5142540 (x : real) (y : real) : (term347 x y) = (term347 x y).
Proof. exact (eq_refl (term347 x y)). Qed.
Lemma lem5142541 (x : real) : (term362 x) = (term362 x).
Proof. exact (fun_ext (fun y : real => @lem5142540 x y)). Qed.
Lemma lem5142542 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142543 (x : real) : (term378 x) = (term378 x).
Proof. exact (MK_COMB (@lem5142542) (@lem5142541 x)). Qed.
Lemma lem5142544 : term385 = term385.
Proof. exact (fun_ext (fun x : real => @lem5142543 x)). Qed.
Lemma lem5142545 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142547 : term400 = term400.
Proof. exact (MK_COMB (@lem5142545) (@lem5142544)). Qed.
Lemma lem5142548 (h1 : term21) : term400.
Proof. exact (EQ_MP (@lem5142547) (@lem5142254 h1)). Qed.
Lemma lem5142560 (s : real -> Prop) (h1 : term106 s) : term106 s.
Proof. exact (h1). Qed.
Lemma lem5142578 {A : Type'} (P : Prop) (Q : A -> Prop) : (term411 A P Q) = (term412 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5142579 (P : Prop) (Q : real -> Prop) : (term413 P Q) = (term414 P Q).
Proof. exact (@lem5142578 real P Q). Qed.
Lemma lem5142580 (x : type1021) (s : real -> Prop) : (term415 x s) = (term416 x s).
Proof. exact (@lem5142579 (s = (@EMPTY real)) (term407 x s)). Qed.
Lemma lem5142581 (x : type1021) (s : real -> Prop) (b : real) : (term417 x s b) = (term406 x s b).
Proof. exact (eq_refl (term417 x s b)). Qed.
Lemma lem5142582 (x : type1021) (s : real -> Prop) : (term418 x s) = (term407 x s).
Proof. exact (fun_ext (fun b : real => @lem5142581 x s b)). Qed.
Lemma lem5142583 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142584 (x : type1021) (s : real -> Prop) : (term419 x s) = (term408 x s).
Proof. exact (MK_COMB (@lem5142583) (@lem5142582 x s)). Qed.
Lemma lem5142585 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (eq_refl (term175 s)). Qed.
Lemma lem5142586 (x : type1021) (s : real -> Prop) : (term415 x s) = (term409 x s).
Proof. exact (MK_COMB (@lem5142585 s) (@lem5142584 x s)). Qed.
Lemma lem5142587 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5142588 (x : type1021) (s : real -> Prop) : (term420 x s) = (term421 x s).
Proof. exact (MK_COMB (@lem5142587) (@lem5142586 x s)). Qed.
Lemma lem5142589 (x : type1021) (s : real -> Prop) (b : real) : (term417 x s b) = (term406 x s b).
Proof. exact (eq_refl (term417 x s b)). Qed.
Lemma lem5142590 (s : real -> Prop) : (term175 s) = (term175 s).
Proof. exact (eq_refl (term175 s)). Qed.
Lemma lem5142591 (x : type1021) (s : real -> Prop) (b : real) : (term422 x s b) = (term423 x s b).
Proof. exact (MK_COMB (@lem5142590 s) (@lem5142589 x s b)). Qed.
Lemma lem5142592 (x : type1021) (s : real -> Prop) : (term424 x s) = (term425 x s).
Proof. exact (fun_ext (fun b : real => @lem5142591 x s b)). Qed.
Lemma lem5142593 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142594 (x : type1021) (s : real -> Prop) : (term416 x s) = (term426 x s).
Proof. exact (MK_COMB (@lem5142593) (@lem5142592 x s)). Qed.
Lemma lem5142595 (x : type1021) (s : real -> Prop) : ((term415 x s) = (term416 x s)) = ((term409 x s) = (term426 x s)).
Proof. exact (MK_COMB (@lem5142588 x s) (@lem5142594 x s)). Qed.
Lemma lem5142596 (x : type1021) (s : real -> Prop) : (term409 x s) = (term426 x s).
Proof. exact (EQ_MP (@lem5142595 x s) (@lem5142580 x s)). Qed.
Lemma lem5142597 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5142598 (x : type1021) (s : real -> Prop) : (term410 x s) = (term427 x s).
Proof. exact (MK_COMB (@lem5142597) (@lem5142596 x s)). Qed.
Lemma lem5142600 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term356 A P Q) = (term355 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem5142601 (P : real -> Prop) (Q : real -> Prop) : (term358 P Q) = (term357 P Q).
Proof. exact (@lem5142600 real P Q). Qed.
Lemma lem5142602 (x : type1021) (s : real -> Prop) : (term428 x s) = (term429 x s).
Proof. exact (@lem5142601 (term181 s) (term403 x s)). Qed.
Lemma lem5142603 (b : real) (s : real -> Prop) : (term430 s b) = (term180 b s).
Proof. exact (eq_refl (term430 s b)). Qed.
Lemma lem5142604 (s : real -> Prop) : (term431 s) = (term181 s).
Proof. exact (fun_ext (fun b : real => @lem5142603 b s)). Qed.
Lemma lem5142605 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142606 (s : real -> Prop) : (term432 s) = (term182 s).
Proof. exact (MK_COMB (@lem5142605) (@lem5142604 s)). Qed.
Lemma lem5142607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5142608 (s : real -> Prop) : (term433 s) = (term189 s).
Proof. exact (MK_COMB (@lem5142607) (@lem5142606 s)). Qed.
Lemma lem5142609 (x : type1021) (s : real -> Prop) (b : real) : (term434 x s b) = (term402 x s b).
Proof. exact (eq_refl (term434 x s b)). Qed.
Lemma lem5142610 (x : type1021) (s : real -> Prop) : (term435 x s) = (term403 x s).
Proof. exact (fun_ext (fun b : real => @lem5142609 x s b)). Qed.
Lemma lem5142611 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142612 (x : type1021) (s : real -> Prop) : (term436 x s) = (term404 x s).
Proof. exact (MK_COMB (@lem5142611) (@lem5142610 x s)). Qed.
Lemma lem5142613 (x : type1021) (s : real -> Prop) : (term428 x s) = (term405 x s).
Proof. exact (MK_COMB (@lem5142608 s) (@lem5142612 x s)). Qed.
Lemma lem5142614 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5142615 (x : type1021) (s : real -> Prop) : (term437 x s) = (term438 x s).
Proof. exact (MK_COMB (@lem5142614) (@lem5142613 x s)). Qed.
Lemma lem5142616 (b : real) (s : real -> Prop) : (term430 s b) = (term180 b s).
Proof. exact (eq_refl (term430 s b)). Qed.
Lemma lem5142617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5142618 (b : real) (s : real -> Prop) : (term439 s b) = (term440 b s).
Proof. exact (MK_COMB (@lem5142617) (@lem5142616 b s)). Qed.
Lemma lem5142619 (x : type1021) (s : real -> Prop) (b : real) : (term434 x s b) = (term402 x s b).
Proof. exact (eq_refl (term434 x s b)). Qed.
Lemma lem5142620 (x : type1021) (s : real -> Prop) (b : real) : (term441 x s b) = (term442 x s b).
Proof. exact (MK_COMB (@lem5142618 b s) (@lem5142619 x s b)). Qed.
Lemma lem5142621 (x : type1021) (s : real -> Prop) : (term443 x s) = (term444 x s).
Proof. exact (fun_ext (fun b : real => @lem5142620 x s b)). Qed.
Lemma lem5142622 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142623 (x : type1021) (s : real -> Prop) : (term429 x s) = (term445 x s).
Proof. exact (MK_COMB (@lem5142622) (@lem5142621 x s)). Qed.
Lemma lem5142624 (x : type1021) (s : real -> Prop) : ((term428 x s) = (term429 x s)) = ((term405 x s) = (term445 x s)).
Proof. exact (MK_COMB (@lem5142615 x s) (@lem5142623 x s)). Qed.
Lemma lem5142625 (x : type1021) (s : real -> Prop) : (term405 x s) = (term445 x s).
Proof. exact (EQ_MP (@lem5142624 x s) (@lem5142602 x s)). Qed.
Lemma lem5142628 (x : type1021) (s : real -> Prop) : (term446 x s) = (term446 x s).
Proof. exact (eq_refl (term446 x s)). Qed.
Lemma lem5142629 (x : type1021) (s : real -> Prop) : (term446 x s) = ((term405 x s) = (term445 x s)).
Proof. exact (eq_refl (term446 x s)). Qed.
Lemma lem5142630 (x : type1021) (s : real -> Prop) : (term447 x s) = (term447 x s).
Proof. exact (eq_refl (term447 x s)). Qed.
Lemma lem5142631 (x : type1021) (s : real -> Prop) : ((term446 x s) = (term446 x s)) = ((term446 x s) = ((term405 x s) = (term445 x s))).
Proof. exact (MK_COMB (@lem5142630 x s) (@lem5142629 x s)). Qed.
Lemma lem5142632 (x : type1021) (s : real -> Prop) : (term446 x s) = ((term405 x s) = (term445 x s)).
Proof. exact (eq_refl (term446 x s)). Qed.
Lemma lem5142633 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5142634 (x : type1021) (s : real -> Prop) : (term447 x s) = (term448 x s).
Proof. exact (MK_COMB (@lem5142633) (@lem5142632 x s)). Qed.
Lemma lem5142635 (x : type1021) (s : real -> Prop) : ((term405 x s) = (term445 x s)) = ((term405 x s) = (term445 x s)).
Proof. exact (eq_refl ((term405 x s) = (term445 x s))). Qed.
Lemma lem5142636 (x : type1021) (s : real -> Prop) : ((term446 x s) = ((term405 x s) = (term445 x s))) = (((term405 x s) = (term445 x s)) = ((term405 x s) = (term445 x s))).
Proof. exact (MK_COMB (@lem5142634 x s) (@lem5142635 x s)). Qed.
Lemma lem5142637 (x : type1021) (s : real -> Prop) : ((term446 x s) = (term446 x s)) = (((term405 x s) = (term445 x s)) = ((term405 x s) = (term445 x s))).
Proof. exact (TRANS (@lem5142631 x s) (@lem5142636 x s)). Qed.
Lemma lem5142638 (x : type1021) (s : real -> Prop) : ((term405 x s) = (term445 x s)) = ((term405 x s) = (term445 x s)).
Proof. exact (EQ_MP (@lem5142637 x s) (@lem5142628 x s)). Qed.
Lemma lem5142639 (x : type1021) (s : real -> Prop) : (term405 x s) = (term445 x s).
Proof. exact (EQ_MP (@lem5142638 x s) (@lem5142625 x s)). Qed.
Lemma lem5142640 (x : type1021) (s : real -> Prop) : (term334 x s) = (term449 x s).
Proof. exact (MK_COMB (@lem5142598 x s) (@lem5142639 x s)). Qed.
Lemma lem5142642 {A : Type'} (P : A -> Prop) (Q : Prop) : (term450 A P Q) = (term451 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5142643 (P : real -> Prop) (Q : Prop) : (term452 P Q) = (term453 P Q).
Proof. exact (@lem5142642 real P Q). Qed.
Lemma lem5142644 (x : type1021) (s : real -> Prop) : (term454 x s) = (term455 x s).
Proof. exact (@lem5142643 (term425 x s) (term445 x s)). Qed.
Lemma lem5142645 (x : type1021) (s : real -> Prop) (b : real) : (term456 x s b) = (term423 x s b).
Proof. exact (eq_refl (term456 x s b)). Qed.
Lemma lem5142646 (x : type1021) (s : real -> Prop) : (term457 x s) = (term425 x s).
Proof. exact (fun_ext (fun b : real => @lem5142645 x s b)). Qed.
Lemma lem5142647 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142648 (x : type1021) (s : real -> Prop) : (term458 x s) = (term426 x s).
Proof. exact (MK_COMB (@lem5142647) (@lem5142646 x s)). Qed.
Lemma lem5142649 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5142650 (x : type1021) (s : real -> Prop) : (term459 x s) = (term427 x s).
Proof. exact (MK_COMB (@lem5142649) (@lem5142648 x s)). Qed.
Lemma lem5142651 (x : type1021) (s : real -> Prop) : (term445 x s) = (term445 x s).
Proof. exact (eq_refl (term445 x s)). Qed.
Lemma lem5142652 (x : type1021) (s : real -> Prop) : (term454 x s) = (term449 x s).
Proof. exact (MK_COMB (@lem5142650 x s) (@lem5142651 x s)). Qed.
Lemma lem5142653 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5142654 (x : type1021) (s : real -> Prop) : (term460 x s) = (term461 x s).
Proof. exact (MK_COMB (@lem5142653) (@lem5142652 x s)). Qed.
Lemma lem5142655 (x : type1021) (s : real -> Prop) (b : real) : (term456 x s b) = (term423 x s b).
Proof. exact (eq_refl (term456 x s b)). Qed.
Lemma lem5142656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5142657 (x : type1021) (s : real -> Prop) (b : real) : (term462 x s b) = (term463 x s b).
Proof. exact (MK_COMB (@lem5142656) (@lem5142655 x s b)). Qed.
Lemma lem5142658 (x : type1021) (s : real -> Prop) : (term445 x s) = (term445 x s).
Proof. exact (eq_refl (term445 x s)). Qed.
Lemma lem5142659 (b : real) (x : type1021) (s : real -> Prop) : (term464 b x s) = (term465 b x s).
Proof. exact (MK_COMB (@lem5142657 x s b) (@lem5142658 x s)). Qed.
Lemma lem5142660 (x : type1021) (s : real -> Prop) : (term466 x s) = (term467 x s).
Proof. exact (fun_ext (fun b : real => @lem5142659 b x s)). Qed.
Lemma lem5142661 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142662 (x : type1021) (s : real -> Prop) : (term455 x s) = (term468 x s).
Proof. exact (MK_COMB (@lem5142661) (@lem5142660 x s)). Qed.
Lemma lem5142663 (x : type1021) (s : real -> Prop) : ((term454 x s) = (term455 x s)) = ((term449 x s) = (term468 x s)).
Proof. exact (MK_COMB (@lem5142654 x s) (@lem5142662 x s)). Qed.
Lemma lem5142664 (x : type1021) (s : real -> Prop) : (term449 x s) = (term468 x s).
Proof. exact (EQ_MP (@lem5142663 x s) (@lem5142644 x s)). Qed.
Lemma lem5142666 {A : Type'} (P : Prop) (Q : A -> Prop) : (term411 A P Q) = (term412 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5142667 (P : Prop) (Q : real -> Prop) : (term413 P Q) = (term414 P Q).
Proof. exact (@lem5142666 real P Q). Qed.
Lemma lem5142668 (b : real) (x : type1021) (s : real -> Prop) : (term469 b x s) = (term470 b x s).
Proof. exact (@lem5142667 (term423 x s b) (term444 x s)). Qed.
Lemma lem5142669 (x : type1021) (s : real -> Prop) (b : real) : (term471 x s b) = (term442 x s b).
Proof. exact (eq_refl (term471 x s b)). Qed.
Lemma lem5142670 (x : type1021) (s : real -> Prop) : (term472 x s) = (term444 x s).
Proof. exact (fun_ext (fun b : real => @lem5142669 x s b)). Qed.
Lemma lem5142671 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142672 (x : type1021) (s : real -> Prop) : (term473 x s) = (term445 x s).
Proof. exact (MK_COMB (@lem5142671) (@lem5142670 x s)). Qed.
Lemma lem5142673 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term463 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5142674 (b : real) (x : type1021) (s : real -> Prop) : (term469 b x s) = (term465 b x s).
Proof. exact (MK_COMB (@lem5142673 x s b) (@lem5142672 x s)). Qed.
Lemma lem5142675 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5142676 (b : real) (x : type1021) (s : real -> Prop) : (term474 b x s) = (term475 b x s).
Proof. exact (MK_COMB (@lem5142675) (@lem5142674 b x s)). Qed.
Lemma lem5142677 (x : type1021) (s : real -> Prop) (b' : real) : (term471 x s b') = (term442 x s b').
Proof. exact (eq_refl (term471 x s b')). Qed.
Lemma lem5142678 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term463 x s b).
Proof. exact (eq_refl (term463 x s b)). Qed.
Lemma lem5142679 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term476 b x s b') = (term477 b x s b').
Proof. exact (MK_COMB (@lem5142678 x s b) (@lem5142677 x s b')). Qed.
Lemma lem5142680 (b : real) (x : type1021) (s : real -> Prop) : (term478 b x s) = (term479 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5142679 b x s b')). Qed.
Lemma lem5142681 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142682 (b : real) (x : type1021) (s : real -> Prop) : (term470 b x s) = (term480 b x s).
Proof. exact (MK_COMB (@lem5142681) (@lem5142680 b x s)). Qed.
Lemma lem5142683 (b : real) (x : type1021) (s : real -> Prop) : ((term469 b x s) = (term470 b x s)) = ((term465 b x s) = (term480 b x s)).
Proof. exact (MK_COMB (@lem5142676 b x s) (@lem5142682 b x s)). Qed.
Lemma lem5142684 (b : real) (x : type1021) (s : real -> Prop) : (term465 b x s) = (term480 b x s).
Proof. exact (EQ_MP (@lem5142683 b x s) (@lem5142668 b x s)). Qed.
Lemma lem5142685 (x : type1021) (s : real -> Prop) : (term467 x s) = (term481 x s).
Proof. exact (fun_ext (fun b : real => @lem5142684 b x s)). Qed.
Lemma lem5142686 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142687 (x : type1021) (s : real -> Prop) : (term468 x s) = (term482 x s).
Proof. exact (MK_COMB (@lem5142686) (@lem5142685 x s)). Qed.
Lemma lem5142688 (x : type1021) (s : real -> Prop) : (term449 x s) = (term482 x s).
Proof. exact (TRANS (@lem5142664 x s) (@lem5142687 x s)). Qed.
Lemma lem5142689 (x : type1021) (s : real -> Prop) : (term334 x s) = (term482 x s).
Proof. exact (TRANS (@lem5142640 x s) (@lem5142688 x s)). Qed.
Lemma lem5142690 (x : type1021) : (term336 x) = (term483 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5142689 x s)). Qed.
Lemma lem5142691 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5142692 (x : type1021) : (term338 x) = (term484 x).
Proof. exact (MK_COMB (@lem5142691) (@lem5142690 x)). Qed.
Lemma lem5142709 (x : type1021) (s : real -> Prop) (b' : real) : (term402 x s b') = (term485 x s b').
Proof. exact (@lem19699 (term486 x b' s) (term487 x s b') (term46 s b')). Qed.
Lemma lem5142718 (b' : real) (s : real -> Prop) : (term440 b' s) = (term440 b' s).
Proof. exact (eq_refl (term440 b' s)). Qed.
Lemma lem5142719 (x : type1021) (s : real -> Prop) (b' : real) : (term442 x s b') = (term488 x s b').
Proof. exact (MK_COMB (@lem5142718 b' s) (@lem5142709 x s b')). Qed.
Lemma lem5142736 (x : type1021) (s : real -> Prop) (b : real) : (term423 x s b) = (term489 x s b).
Proof. exact (@lem19490 (term486 x b s) (s = (@EMPTY real)) (term487 x s b)). Qed.
Lemma lem5142737 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5142738 (x : type1021) (s : real -> Prop) (b : real) : (term463 x s b) = (term490 x s b).
Proof. exact (MK_COMB (@lem5142737) (@lem5142736 x s b)). Qed.
Lemma lem5142739 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term477 b x s b') = (term491 b x s b').
Proof. exact (MK_COMB (@lem5142738 x s b) (@lem5142719 x s b')). Qed.
Lemma lem5142740 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term491 b x s b') = (term492 b x s b').
Proof. exact (@lem19490 (term180 b' s) (term489 x s b) (term485 x s b')). Qed.
Lemma lem5142741 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term493 b x s b') = (term494 b x s b').
Proof. exact (@lem19490 (term495 x s b') (term489 x s b) (term496 x s b')). Qed.
Lemma lem5142748 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term497 b x s b') = (term498 b x s b').
Proof. exact (@lem19699 (term499 x b s) (term500 x s b) (term496 x s b')). Qed.
Lemma lem5142755 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term501 b x s b') = (term502 b x s b').
Proof. exact (@lem19699 (term499 x b s) (term500 x s b) (term495 x s b')). Qed.
Lemma lem5142756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5142757 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term503 b x s b') = (term504 b x s b').
Proof. exact (MK_COMB (@lem5142756) (@lem5142755 b x s b')). Qed.
Lemma lem5142758 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term494 b x s b') = (term505 b x s b').
Proof. exact (MK_COMB (@lem5142757 b x s b') (@lem5142748 b x s b')). Qed.
Lemma lem5142759 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term493 b x s b') = (term505 b x s b').
Proof. exact (TRANS (@lem5142741 b x s b') (@lem5142758 b x s b')). Qed.
Lemma lem5142766 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term506 x b b' s) = (term507 x b b' s).
Proof. exact (@lem19699 (term499 x b s) (term500 x s b) (term180 b' s)). Qed.
Lemma lem5142767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5142768 (x : type1021) (b : real) (b' : real) (s : real -> Prop) : (term508 x b b' s) = (term509 x b b' s).
Proof. exact (MK_COMB (@lem5142767) (@lem5142766 x b b' s)). Qed.
Lemma lem5142769 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term492 b x s b') = (term510 b x s b').
Proof. exact (MK_COMB (@lem5142768 x b b' s) (@lem5142759 b x s b')). Qed.
Lemma lem5142770 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term491 b x s b') = (term510 b x s b').
Proof. exact (TRANS (@lem5142740 b x s b') (@lem5142769 b x s b')). Qed.
Lemma lem5142771 (b : real) (x : type1021) (s : real -> Prop) (b' : real) : (term477 b x s b') = (term510 b x s b').
Proof. exact (TRANS (@lem5142739 b x s b') (@lem5142770 b x s b')). Qed.
Lemma lem5142772 (b : real) (x : type1021) (s : real -> Prop) : (term479 b x s) = (term511 b x s).
Proof. exact (fun_ext (fun b' : real => @lem5142771 b x s b')). Qed.
Lemma lem5142773 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142774 (b : real) (x : type1021) (s : real -> Prop) : (term480 b x s) = (term512 b x s).
Proof. exact (MK_COMB (@lem5142773) (@lem5142772 b x s)). Qed.
Lemma lem5142775 (x : type1021) (s : real -> Prop) : (term481 x s) = (term513 x s).
Proof. exact (fun_ext (fun b : real => @lem5142774 b x s)). Qed.
Lemma lem5142776 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142777 (x : type1021) (s : real -> Prop) : (term482 x s) = (term514 x s).
Proof. exact (MK_COMB (@lem5142776) (@lem5142775 x s)). Qed.
Lemma lem5142778 (x : type1021) : (term483 x) = (term515 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5142777 x s)). Qed.
Lemma lem5142779 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5142780 (x : type1021) : (term484 x) = (term516 x).
Proof. exact (MK_COMB (@lem5142779) (@lem5142778 x)). Qed.
Lemma lem5142781 (x : type1021) : (term338 x) = (term516 x).
Proof. exact (TRANS (@lem5142692 x) (@lem5142780 x)). Qed.
Lemma lem5142782 (x : type1021) (h1 : term338 x) : term516 x.
Proof. exact (EQ_MP (@lem5142781 x) (@lem5142190 x h1)). Qed.
Lemma lem5142794 (s : real -> Prop) (x : real) (b : real) : (term73 s x b) = (term73 s x b).
Proof. exact (eq_refl (term73 s x b)). Qed.
Lemma lem5142795 (s : real -> Prop) (b : real) : (term74 s b) = (term74 s b).
Proof. exact (fun_ext (fun x : real => @lem5142794 s x b)). Qed.
Lemma lem5142796 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5142798 (s : real -> Prop) (b : real) : (term75 s b) = (term75 s b).
Proof. exact (MK_COMB (@lem5142796) (@lem5142795 s b)). Qed.
Lemma lem5142799 (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term75 s b.
Proof. exact (EQ_MP (@lem5142798 s b) (@lem5142252 b x' s h1)). Qed.
Lemma lem5142870 (_67126 : real -> Prop) (x : type1021) (h1 : term338 x) : term517 x _67126.
Proof. exact (@lem5142483 x h1 _67126). Qed.
Lemma lem5142871 (x : type1021) (_67126 : real -> Prop) : (term517 x _67126) = (term514 x _67126).
Proof. exact (eq_refl (term517 x _67126)). Qed.
Lemma lem5142872 (_67126 : real -> Prop) (x : type1021) (h1 : term338 x) : term514 x _67126.
Proof. exact (EQ_MP (@lem5142871 x _67126) (@lem5142870 _67126 x h1)). Qed.
Lemma lem5142873 (_67126 : real -> Prop) (_67127 : real) (x : type1021) (h1 : term338 x) : term518 x _67126 _67127.
Proof. exact (@lem5142872 _67126 x h1 _67127). Qed.
Lemma lem5142874 (_67127 : real) (x : type1021) (_67126 : real -> Prop) : (term518 x _67126 _67127) = (term512 _67127 x _67126).
Proof. exact (eq_refl (term518 x _67126 _67127)). Qed.
Lemma lem5142875 (_67127 : real) (_67126 : real -> Prop) (x : type1021) (h1 : term338 x) : term512 _67127 x _67126.
Proof. exact (EQ_MP (@lem5142874 _67127 x _67126) (@lem5142873 _67126 _67127 x h1)). Qed.
Lemma lem5142876 (_67127 : real) (_67126 : real -> Prop) (_67128 : real) (x : type1021) (h1 : term338 x) : term519 _67127 x _67126 _67128.
Proof. exact (@lem5142875 _67127 _67126 x h1 _67128). Qed.
Lemma lem5142877 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term519 _67127 x _67126 _67128) = (term510 _67127 x _67126 _67128).
Proof. exact (eq_refl (term519 _67127 x _67126 _67128)). Qed.
Lemma lem5142878 (_67127 : real) (_67126 : real -> Prop) (_67128 : real) (x : type1021) (h1 : term338 x) : term510 _67127 x _67126 _67128.
Proof. exact (EQ_MP (@lem5142877 _67127 x _67126 _67128) (@lem5142876 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5142879 (_67129 : real) (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term520 s b _67129.
Proof. exact (@lem5142500 b x' s h1 _67129). Qed.
Lemma lem5142880 (s : real -> Prop) (_67129 : real) (b : real) : (term520 s b _67129) = (term73 s _67129 b).
Proof. exact (eq_refl (term520 s b _67129)). Qed.
Lemma lem5142888 (_67132 : real) (h1 : term21) : term388 _67132.
Proof. exact (@lem5142548 h1 _67132). Qed.
Lemma lem5142889 (_67132 : real) : (term388 _67132) = (term378 _67132).
Proof. exact (eq_refl (term388 _67132)). Qed.
Lemma lem5142890 (_67132 : real) (h1 : term21) : term378 _67132.
Proof. exact (EQ_MP (@lem5142889 _67132) (@lem5142888 _67132 h1)). Qed.
Lemma lem5142891 (_67132 : real) (_67133 : real) (h1 : term21) : term366 _67132 _67133.
Proof. exact (@lem5142890 _67132 h1 _67133). Qed.
Lemma lem5142892 (_67132 : real) (_67133 : real) : (term366 _67132 _67133) = (term347 _67132 _67133).
Proof. exact (eq_refl (term366 _67132 _67133)). Qed.
Lemma lem5142893 (_67132 : real) (_67133 : real) (h1 : term21) : term347 _67132 _67133.
Proof. exact (EQ_MP (@lem5142892 _67132 _67133) (@lem5142891 _67132 _67133 h1)). Qed.
Lemma lem5142900 (_67136 : real -> Prop) (x : type1021) (h1 : term338 x) : term517 x _67136.
Proof. exact (@lem5142782 x h1 _67136). Qed.
Lemma lem5142901 (x : type1021) (_67136 : real -> Prop) : (term517 x _67136) = (term514 x _67136).
Proof. exact (eq_refl (term517 x _67136)). Qed.
Lemma lem5142902 (_67136 : real -> Prop) (x : type1021) (h1 : term338 x) : term514 x _67136.
Proof. exact (EQ_MP (@lem5142901 x _67136) (@lem5142900 _67136 x h1)). Qed.
Lemma lem5142903 (_67136 : real -> Prop) (_67137 : real) (x : type1021) (h1 : term338 x) : term518 x _67136 _67137.
Proof. exact (@lem5142902 _67136 x h1 _67137). Qed.
Lemma lem5142904 (_67137 : real) (x : type1021) (_67136 : real -> Prop) : (term518 x _67136 _67137) = (term512 _67137 x _67136).
Proof. exact (eq_refl (term518 x _67136 _67137)). Qed.
Lemma lem5142905 (_67137 : real) (_67136 : real -> Prop) (x : type1021) (h1 : term338 x) : term512 _67137 x _67136.
Proof. exact (EQ_MP (@lem5142904 _67137 x _67136) (@lem5142903 _67136 _67137 x h1)). Qed.
Lemma lem5142906 (_67137 : real) (_67136 : real -> Prop) (_67138 : real) (x : type1021) (h1 : term338 x) : term519 _67137 x _67136 _67138.
Proof. exact (@lem5142905 _67137 _67136 x h1 _67138). Qed.
Lemma lem5142907 (_67137 : real) (x : type1021) (_67136 : real -> Prop) (_67138 : real) : (term519 _67137 x _67136 _67138) = (term510 _67137 x _67136 _67138).
Proof. exact (eq_refl (term519 _67137 x _67136 _67138)). Qed.
Lemma lem5142908 (_67137 : real) (_67136 : real -> Prop) (_67138 : real) (x : type1021) (h1 : term338 x) : term510 _67137 x _67136 _67138.
Proof. exact (EQ_MP (@lem5142907 _67137 x _67136 _67138) (@lem5142906 _67137 _67136 _67138 x h1)). Qed.
Lemma lem5142909 (_67139 : real) (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term520 s b _67139.
Proof. exact (@lem5142799 b x' s h1 _67139). Qed.
Lemma lem5142910 (s : real -> Prop) (_67139 : real) (b : real) : (term520 s b _67139) = (term73 s _67139 b).
Proof. exact (eq_refl (term520 s b _67139)). Qed.
Lemma lem5142926 (_67127 : real) (_67126 : real -> Prop) (_67128 : real) (x : type1021) (h1 : term338 x) : term505 _67127 x _67126 _67128.
Proof. exact (proj2 (@lem5142878 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5142927 (_67127 : real) (_67128 : real) (_67126 : real -> Prop) (x : type1021) (h1 : term338 x) : term507 x _67127 _67128 _67126.
Proof. exact (proj1 (@lem5142878 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5142928 (_67127 : real) (_67126 : real -> Prop) (_67128 : real) (x : type1021) (h1 : term338 x) : term498 _67127 x _67126 _67128.
Proof. exact (proj2 (@lem5142926 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5142929 (_67127 : real) (_67126 : real -> Prop) (_67128 : real) (x : type1021) (h1 : term338 x) : term502 _67127 x _67126 _67128.
Proof. exact (proj1 (@lem5142926 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5142930 (_67127 : real) (_67126 : real -> Prop) (_67128 : real) (x : type1021) (h1 : term338 x) : term521 _67127 x _67126 _67128.
Proof. exact (proj2 (@lem5142928 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5142932 (_67127 : real) (_67126 : real -> Prop) (_67128 : real) (x : type1021) (h1 : term338 x) : term522 _67127 x _67126 _67128.
Proof. exact (proj2 (@lem5142929 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5142933 (_67127 : real) (_67126 : real -> Prop) (_67128 : real) (x : type1021) (h1 : term338 x) : term523 _67127 x _67126 _67128.
Proof. exact (proj1 (@lem5142929 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5142934 (_67127 : real) (_67128 : real) (_67126 : real -> Prop) (x : type1021) (h1 : term338 x) : term524 x _67127 _67128 _67126.
Proof. exact (proj2 (@lem5142927 _67127 _67128 _67126 x h1)). Qed.
Lemma lem5142935 (_67127 : real) (_67128 : real) (_67126 : real -> Prop) (x : type1021) (h1 : term338 x) : term525 x _67127 _67128 _67126.
Proof. exact (proj1 (@lem5142927 _67127 _67128 _67126 x h1)). Qed.
Lemma lem5142939 (_67137 : real) (_67138 : real) (_67136 : real -> Prop) (x : type1021) (h1 : term338 x) : term507 x _67137 _67138 _67136.
Proof. exact (proj1 (@lem5142908 _67137 _67136 _67138 x h1)). Qed.
Lemma lem5142946 (_67137 : real) (_67138 : real) (_67136 : real -> Prop) (x : type1021) (h1 : term338 x) : term524 x _67137 _67138 _67136.
Proof. exact (proj2 (@lem5142939 _67137 _67138 _67136 x h1)). Qed.
Lemma lem5142947 (_67137 : real) (_67138 : real) (_67136 : real -> Prop) (x : type1021) (h1 : term338 x) : term525 x _67137 _67138 _67136.
Proof. exact (proj1 (@lem5142939 _67137 _67138 _67136 x h1)). Qed.
Lemma lem5142961 (_67129 : real) (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term73 s _67129 b.
Proof. exact (EQ_MP (@lem5142880 s _67129 b) (@lem5142879 _67129 b x' s h1)). Qed.
Lemma lem5142972 (_67132 : real) (_67133 : real) : (term347 _67132 _67133) = (term526 _67132 _67133).
Proof. exact (@lem5140320 (term527 _67132 _67133) (term527 _67133 _67132) (_67132 = _67133)). Qed.
Lemma lem5142973 (_67132 : real) (_67133 : real) (h1 : term21) : term526 _67132 _67133.
Proof. exact (EQ_MP (@lem5142972 _67132 _67133) (@lem5142893 _67132 _67133 h1)). Qed.
Lemma lem5142979 (s : real -> Prop) (h1 : term106 s) : term106 s.
Proof. exact (h1). Qed.
Lemma lem5143022 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term521 _67127 x _67126 _67128) = (term528 _67127 x _67126 _67128).
Proof. exact (@lem5140320 (_67126 = (@EMPTY real)) (term487 x _67126 _67127) (term496 x _67126 _67128)). Qed.
Lemma lem5143023 (_67127 : real) (_67126 : real -> Prop) (_67128 : real) (x : type1021) (h1 : term338 x) : term528 _67127 x _67126 _67128.
Proof. exact (EQ_MP (@lem5143022 _67127 x _67126 _67128) (@lem5142930 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5143038 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term523 _67127 x _67126 _67128) = (term529 _67127 x _67126 _67128).
Proof. exact (@lem5140320 (_67126 = (@EMPTY real)) (term486 x _67127 _67126) (term495 x _67126 _67128)). Qed.
Lemma lem5143039 (_67127 : real) (_67126 : real -> Prop) (_67128 : real) (x : type1021) (h1 : term338 x) : term529 _67127 x _67126 _67128.
Proof. exact (EQ_MP (@lem5143038 _67127 x _67126 _67128) (@lem5142933 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5143054 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term522 _67127 x _67126 _67128) = (term530 _67127 x _67126 _67128).
Proof. exact (@lem5140320 (_67126 = (@EMPTY real)) (term487 x _67126 _67127) (term495 x _67126 _67128)). Qed.
Lemma lem5143055 (_67127 : real) (_67126 : real -> Prop) (_67128 : real) (x : type1021) (h1 : term338 x) : term530 _67127 x _67126 _67128.
Proof. exact (EQ_MP (@lem5143054 _67127 x _67126 _67128) (@lem5142932 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5143070 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term525 x _67127 _67128 _67126) = (term531 x _67127 _67128 _67126).
Proof. exact (@lem5140320 (_67126 = (@EMPTY real)) (term486 x _67127 _67126) (term180 _67128 _67126)). Qed.
Lemma lem5143071 (_67127 : real) (_67128 : real) (_67126 : real -> Prop) (x : type1021) (h1 : term338 x) : term531 x _67127 _67128 _67126.
Proof. exact (EQ_MP (@lem5143070 x _67127 _67128 _67126) (@lem5142935 _67127 _67128 _67126 x h1)). Qed.
Lemma lem5143086 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term524 x _67127 _67128 _67126) = (term532 x _67127 _67128 _67126).
Proof. exact (@lem5140320 (_67126 = (@EMPTY real)) (term487 x _67126 _67127) (term180 _67128 _67126)). Qed.
Lemma lem5143087 (_67127 : real) (_67128 : real) (_67126 : real -> Prop) (x : type1021) (h1 : term338 x) : term532 x _67127 _67128 _67126.
Proof. exact (EQ_MP (@lem5143086 x _67127 _67128 _67126) (@lem5142934 _67127 _67128 _67126 x h1)). Qed.
Lemma lem5143101 (_67139 : real) (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term73 s _67139 b.
Proof. exact (EQ_MP (@lem5142910 s _67139 b) (@lem5142909 _67139 b x' s h1)). Qed.
Lemma lem5143121 (x' : real) (s : real -> Prop) (h1 : term80 x' s) : term533 x' s.
Proof. exact (proj2 (@lem5142259 x' s h1)). Qed.
Lemma lem5143212 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term525 x _67137 _67138 _67136) = (term531 x _67137 _67138 _67136).
Proof. exact (@lem5140320 (_67136 = (@EMPTY real)) (term486 x _67137 _67136) (term180 _67138 _67136)). Qed.
Lemma lem5143213 (_67137 : real) (_67138 : real) (_67136 : real -> Prop) (x : type1021) (h1 : term338 x) : term531 x _67137 _67138 _67136.
Proof. exact (EQ_MP (@lem5143212 x _67137 _67138 _67136) (@lem5142947 _67137 _67138 _67136 x h1)). Qed.
Lemma lem5143228 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term524 x _67137 _67138 _67136) = (term532 x _67137 _67138 _67136).
Proof. exact (@lem5140320 (_67136 = (@EMPTY real)) (term487 x _67136 _67137) (term180 _67138 _67136)). Qed.
Lemma lem5143229 (_67137 : real) (_67138 : real) (_67136 : real -> Prop) (x : type1021) (h1 : term338 x) : term532 x _67137 _67138 _67136.
Proof. exact (EQ_MP (@lem5143228 x _67137 _67138 _67136) (@lem5142946 _67137 _67138 _67136 x h1)). Qed.
Lemma lem5143242 : (@IN real) = (@IN real).
Proof. exact (eq_refl (@IN real)). Qed.
Lemma lem5143243 (_67146 : real) (_67148 : real) (h1 : _67146 = _67148) : _67146 = _67148.
Proof. exact (h1). Qed.
Lemma lem5143244 (_67147 : real -> Prop) (_67149 : real -> Prop) (h1 : _67147 = _67149) : _67147 = _67149.
Proof. exact (h1). Qed.
Lemma lem5143245 (_67146 : real) (_67148 : real) (h1 : _67146 = _67148) : (@IN real _67146) = (@IN real _67148).
Proof. exact (MK_COMB (@lem5143242) (@lem5143243 _67146 _67148 h1)). Qed.
Lemma lem5143246 (_67147 : real -> Prop) (_67149 : real -> Prop) (_67146 : real) (_67148 : real) (h1 : _67147 = _67149) (h2 : _67146 = _67148) : (@IN real _67146 _67147) = (@IN real _67148 _67149).
Proof. exact (MK_COMB (@lem5143245 _67146 _67148 h2) (@lem5143244 _67147 _67149 h1)). Qed.
Lemma lem5143248 (b : Prop) (a : Prop) : term534 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem5143249 (_67148 : real) (_67149 : real -> Prop) (_67146 : real) (_67147 : real -> Prop) : term535 _67148 _67149 _67146 _67147.
Proof. exact (@lem5143248 (@IN real _67148 _67149) (@IN real _67146 _67147)). Qed.
Lemma lem5143250 (_67147 : real -> Prop) (_67149 : real -> Prop) (_67146 : real) (_67148 : real) (h1 : _67147 = _67149) (h2 : _67146 = _67148) : term536 _67148 _67149 _67146 _67147.
Proof. exact (@lem5143249 _67148 _67149 _67146 _67147 (@lem5143246 _67147 _67149 _67146 _67148 h1 h2)). Qed.
Lemma lem5143251 (_67148 : real) (_67146 : real) (_67147 : real -> Prop) (_67149 : real -> Prop) (h1 : _67147 = _67149) : term537 _67148 _67149 _67146 _67147.
Proof. exact (fun h0 : _67146 = _67148 => @lem5143250 _67147 _67149 _67146 _67148 h1 h0). Qed.
Lemma lem5143253 (a : Prop) (b : Prop) : (a -> b) = (term538 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5143254 (_67148 : real) (_67149 : real -> Prop) (_67146 : real) (_67147 : real -> Prop) : (term537 _67148 _67149 _67146 _67147) = (term539 _67148 _67149 _67146 _67147).
Proof. exact (@lem5143253 (_67146 = _67148) (term536 _67148 _67149 _67146 _67147)). Qed.
Lemma lem5143255 (_67148 : real) (_67146 : real) (_67147 : real -> Prop) (_67149 : real -> Prop) (h1 : _67147 = _67149) : term539 _67148 _67149 _67146 _67147.
Proof. exact (EQ_MP (@lem5143254 _67148 _67149 _67146 _67147) (@lem5143251 _67148 _67146 _67147 _67149 h1)). Qed.
Lemma lem5143256 (_67148 : real) (_67149 : real -> Prop) (_67146 : real) (_67147 : real -> Prop) : term540 _67148 _67149 _67146 _67147.
Proof. exact (fun h0 : _67147 = _67149 => @lem5143255 _67148 _67146 _67147 _67149 h0). Qed.
Lemma lem5143258 (a : Prop) (b : Prop) : (a -> b) = (term538 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem5143259 (_67148 : real) (_67149 : real -> Prop) (_67146 : real) (_67147 : real -> Prop) : (term540 _67148 _67149 _67146 _67147) = (term541 _67148 _67149 _67146 _67147).
Proof. exact (@lem5143258 (_67147 = _67149) (term539 _67148 _67149 _67146 _67147)). Qed.
Lemma lem5143260 (_67148 : real) (_67149 : real -> Prop) (_67146 : real) (_67147 : real -> Prop) : term541 _67148 _67149 _67146 _67147.
Proof. exact (EQ_MP (@lem5143259 _67148 _67149 _67146 _67147) (@lem5143256 _67148 _67149 _67146 _67147)). Qed.
Lemma lem5143308 (x : real -> Prop) : x = x.
Proof. exact (@lem21386 (real -> Prop) x). Qed.
Lemma lem5143309 (s : real -> Prop) : s = s.
Proof. exact (@lem5143308 s). Qed.
Lemma lem5143310 (s : real -> Prop) : term542 s.
Proof. exact (fun h0 : term543 s => @lem5143309 s). Qed.
Lemma lem5143312 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5143313 (s : real -> Prop) : (term542 s) = (s = s).
Proof. exact (@lem5143312 (s = s)). Qed.
Lemma lem5143314 (s : real -> Prop) : s = s.
Proof. exact (EQ_MP (@lem5143313 s) (@lem5143310 s)). Qed.
Lemma lem5143316 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (proj2 (@lem5142006 s h1)). Qed.
Lemma lem5143317 (s : real -> Prop) (h1 : term9 s) : term545 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5143316 s h1). Qed.
Lemma lem5143319 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5143320 (s : real -> Prop) : (term545 s) = (term179 s).
Proof. exact (@lem5143319 (s = (@EMPTY real))). Qed.
Lemma lem5143321 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (EQ_MP (@lem5143320 s) (@lem5143317 s h1)). Qed.
Lemma lem5143323 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (proj2 (@lem5142006 s h1)). Qed.
Lemma lem5143324 (s : real -> Prop) (h1 : term9 s) : term545 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5143323 s h1). Qed.
Lemma lem5143326 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5143327 (s : real -> Prop) : (term545 s) = (term179 s).
Proof. exact (@lem5143326 (s = (@EMPTY real))). Qed.
Lemma lem5143328 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (EQ_MP (@lem5143327 s) (@lem5143324 s h1)). Qed.
Lemma lem5143330 (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : @IN real b s.
Proof. exact (proj1 (@lem5142251 b x' s h1)). Qed.
Lemma lem5143331 (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term547 b s.
Proof. exact (fun h0 : term548 b s => @lem5143330 b x' s h1). Qed.
Lemma lem5143333 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5143334 (b : real) (s : real -> Prop) : (term547 b s) = (@IN real b s).
Proof. exact (@lem5143333 (@IN real b s)). Qed.
Lemma lem5143335 (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : @IN real b s.
Proof. exact (EQ_MP (@lem5143334 b s) (@lem5143331 b x' s h1)). Qed.
Lemma lem5143338 (b : real) (s : real -> Prop) (h1 : term533 b s) : term533 b s.
Proof. exact (h1). Qed.
Lemma lem5143339 (b : real) (s : real -> Prop) (h1 : term533 b s) : term549 b s.
Proof. exact (fun h0 : term81 b s => @lem5143338 b s h1). Qed.
Lemma lem5143341 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5143342 (b : real) (s : real -> Prop) : (term549 b s) = (term533 b s).
Proof. exact (@lem5143341 (term81 b s)). Qed.
Lemma lem5143343 (b : real) (s : real -> Prop) (h1 : term533 b s) : term533 b s.
Proof. exact (EQ_MP (@lem5143342 b s) (@lem5143339 b s h1)). Qed.
Lemma lem5143371 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5143372 (_67128 : real) (_67126 : real -> Prop) : (term180 _67128 _67126) = (term550 _67128 _67126).
Proof. exact (@lem5143371 (term81 _67128 _67126) (term548 _67128 _67126)). Qed.
Lemma lem5143378 (x : type1021) (_67127 : real) (_67126 : real -> Prop) : (term551 x _67127 _67126) = (term551 x _67127 _67126).
Proof. exact (eq_refl (term551 x _67127 _67126)). Qed.
Lemma lem5143379 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term552 x _67127 _67128 _67126) = (term553 x _67127 _67128 _67126).
Proof. exact (MK_COMB (@lem5143378 x _67127 _67126) (@lem5143372 _67128 _67126)). Qed.
Lemma lem5143390 (_67126 : real -> Prop) : (term175 _67126) = (term175 _67126).
Proof. exact (eq_refl (term175 _67126)). Qed.
Lemma lem5143391 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term531 x _67127 _67128 _67126) = (term554 x _67127 _67128 _67126).
Proof. exact (MK_COMB (@lem5143390 _67126) (@lem5143379 x _67127 _67128 _67126)). Qed.
Lemma lem5143402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5143403 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term555 x _67127 _67128 _67126) = (term556 x _67127 _67128 _67126).
Proof. exact (MK_COMB (@lem5143402) (@lem5143391 x _67127 _67128 _67126)). Qed.
Lemma lem5143407 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5143408 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term557 x _67127 _67128 _67126) = (term531 x _67127 _67128 _67126).
Proof. exact (@lem5143407 (_67126 = (@EMPTY real)) (term486 x _67127 _67126) (term180 _67128 _67126)). Qed.
Lemma lem5143434 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5143435 (_67128 : real) (_67126 : real -> Prop) : (term180 _67128 _67126) = (term550 _67128 _67126).
Proof. exact (@lem5143434 (term81 _67128 _67126) (term548 _67128 _67126)). Qed.
Lemma lem5143441 (x : type1021) (_67127 : real) (_67126 : real -> Prop) : (term551 x _67127 _67126) = (term551 x _67127 _67126).
Proof. exact (eq_refl (term551 x _67127 _67126)). Qed.
Lemma lem5143442 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term552 x _67127 _67128 _67126) = (term553 x _67127 _67128 _67126).
Proof. exact (MK_COMB (@lem5143441 x _67127 _67126) (@lem5143435 _67128 _67126)). Qed.
Lemma lem5143453 (_67126 : real -> Prop) : (term175 _67126) = (term175 _67126).
Proof. exact (eq_refl (term175 _67126)). Qed.
Lemma lem5143454 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term531 x _67127 _67128 _67126) = (term554 x _67127 _67128 _67126).
Proof. exact (MK_COMB (@lem5143453 _67126) (@lem5143442 x _67127 _67128 _67126)). Qed.
Lemma lem5143465 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term557 x _67127 _67128 _67126) = (term554 x _67127 _67128 _67126).
Proof. exact (TRANS (@lem5143408 x _67127 _67128 _67126) (@lem5143454 x _67127 _67128 _67126)). Qed.
Lemma lem5143466 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : ((term531 x _67127 _67128 _67126) = (term557 x _67127 _67128 _67126)) = ((term554 x _67127 _67128 _67126) = (term554 x _67127 _67128 _67126)).
Proof. exact (MK_COMB (@lem5143403 x _67127 _67128 _67126) (@lem5143465 x _67127 _67128 _67126)). Qed.
Lemma lem5143468 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5143469 (x : Prop) : (x = x) = True.
Proof. exact (@lem5143468 Prop x). Qed.
Lemma lem5143470 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : ((term554 x _67127 _67128 _67126) = (term554 x _67127 _67128 _67126)) = True.
Proof. exact (@lem5143469 (term554 x _67127 _67128 _67126)). Qed.
Lemma lem5143471 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : ((term531 x _67127 _67128 _67126) = (term557 x _67127 _67128 _67126)) = True.
Proof. exact (TRANS (@lem5143466 x _67127 _67128 _67126) (@lem5143470 x _67127 _67128 _67126)). Qed.
Lemma lem5143472 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : True = ((term531 x _67127 _67128 _67126) = (term557 x _67127 _67128 _67126)).
Proof. exact (SYM (@lem5143471 x _67127 _67128 _67126)). Qed.
Lemma lem5143473 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term531 x _67127 _67128 _67126) = (term557 x _67127 _67128 _67126).
Proof. exact (EQ_MP (@lem5143472 x _67127 _67128 _67126) (@lem0)). Qed.
Lemma lem5143474 (_67127 : real) (_67128 : real) (_67126 : real -> Prop) (x : type1021) (h1 : term338 x) : term557 x _67127 _67128 _67126.
Proof. exact (EQ_MP (@lem5143473 x _67127 _67128 _67126) (@lem5143071 _67127 _67128 _67126 x h1)). Qed.
Lemma lem5143476 (b : Prop) (a : Prop) : (a \/ b) = (term558 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5143477 (_67128 : real) (x : type1021) (_67127 : real) (_67126 : real -> Prop) : (term557 x _67127 _67128 _67126) = (term559 _67128 x _67127 _67126).
Proof. exact (@lem5143476 (term560 _67128 _67126) (term486 x _67127 _67126)). Qed.
Lemma lem5143479 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5143480 (_67128 : real) (_67126 : real -> Prop) : (term563 _67128 _67126) = (term564 _67128 _67126).
Proof. exact (@lem5143479 (_67126 = (@EMPTY real)) (term180 _67128 _67126)). Qed.
Lemma lem5143482 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5143483 (_67128 : real) (_67126 : real -> Prop) : (term565 _67128 _67126) = (term566 _67128 _67126).
Proof. exact (@lem5143482 (term548 _67128 _67126) (term81 _67128 _67126)). Qed.
Lemma lem5143485 (a : Prop) : (term567 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5143486 (_67128 : real) (_67126 : real -> Prop) : (term568 _67128 _67126) = (@IN real _67128 _67126).
Proof. exact (@lem5143485 (@IN real _67128 _67126)). Qed.
Lemma lem5143487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5143488 (_67128 : real) (_67126 : real -> Prop) : (term569 _67128 _67126) = (term69 _67128 _67126).
Proof. exact (MK_COMB (@lem5143487) (@lem5143486 _67128 _67126)). Qed.
Lemma lem5143489 (_67128 : real) (_67126 : real -> Prop) : (term533 _67128 _67126) = (term533 _67128 _67126).
Proof. exact (eq_refl (term533 _67128 _67126)). Qed.
Lemma lem5143490 (_67128 : real) (_67126 : real -> Prop) : (term566 _67128 _67126) = (term80 _67128 _67126).
Proof. exact (MK_COMB (@lem5143488 _67128 _67126) (@lem5143489 _67128 _67126)). Qed.
Lemma lem5143491 (_67128 : real) (_67126 : real -> Prop) : (term565 _67128 _67126) = (term80 _67128 _67126).
Proof. exact (TRANS (@lem5143483 _67128 _67126) (@lem5143490 _67128 _67126)). Qed.
Lemma lem5143492 (_67126 : real -> Prop) : (term61 _67126) = (term61 _67126).
Proof. exact (eq_refl (term61 _67126)). Qed.
Lemma lem5143493 (_67128 : real) (_67126 : real -> Prop) : (term564 _67128 _67126) = (term570 _67128 _67126).
Proof. exact (MK_COMB (@lem5143492 _67126) (@lem5143491 _67128 _67126)). Qed.
Lemma lem5143494 (_67128 : real) (_67126 : real -> Prop) : (term563 _67128 _67126) = (term570 _67128 _67126).
Proof. exact (TRANS (@lem5143480 _67128 _67126) (@lem5143493 _67128 _67126)). Qed.
Lemma lem5143495 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5143496 (_67128 : real) (_67126 : real -> Prop) : (term571 _67128 _67126) = (term572 _67128 _67126).
Proof. exact (MK_COMB (@lem5143495) (@lem5143494 _67128 _67126)). Qed.
Lemma lem5143497 (x : type1021) (_67127 : real) (_67126 : real -> Prop) : (term486 x _67127 _67126) = (term486 x _67127 _67126).
Proof. exact (eq_refl (term486 x _67127 _67126)). Qed.
Lemma lem5143498 (_67128 : real) (x : type1021) (_67127 : real) (_67126 : real -> Prop) : (term559 _67128 x _67127 _67126) = (term573 _67128 x _67127 _67126).
Proof. exact (MK_COMB (@lem5143496 _67128 _67126) (@lem5143497 x _67127 _67126)). Qed.
Lemma lem5143499 (_67128 : real) (x : type1021) (_67127 : real) (_67126 : real -> Prop) : (term557 x _67127 _67128 _67126) = (term573 _67128 x _67127 _67126).
Proof. exact (TRANS (@lem5143477 _67128 x _67127 _67126) (@lem5143498 _67128 x _67127 _67126)). Qed.
Lemma lem5143501 (b : real) (x' : real) (s : real -> Prop) (h1 : term533 b s) (h2 : term149 b x' s) : term80 b s.
Proof. exact (conj (@lem5143335 b x' s h2) (@lem5143343 b s h1)). Qed.
Lemma lem5143502 (b : real) (x' : real) (s : real -> Prop) (h1 : term533 b s) (h2 : term9 s) (h3 : term149 b x' s) : term570 b s.
Proof. exact (conj (@lem5143328 s h2) (@lem5143501 b x' s h1 h3)). Qed.
Lemma lem5143504 (_67128 : real) (_67127 : real) (_67126 : real -> Prop) (x : type1021) (h1 : term338 x) : term573 _67128 x _67127 _67126.
Proof. exact (EQ_MP (@lem5143499 _67128 x _67127 _67126) (@lem5143474 _67127 _67128 _67126 x h1)). Qed.
Lemma lem5143505 (b : real) (_67127 : real) (s : real -> Prop) (x : type1021) (h1 : term338 x) : term573 b x _67127 s.
Proof. exact (@lem5143504 b _67127 s x h1). Qed.
Lemma lem5143508 (_67127 : real) (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 b s) (h3 : term9 s) (h4 : term149 b x' s) : term486 x _67127 s.
Proof. exact (@lem5143505 b _67127 s x h1 (@lem5143502 b x' s h2 h3 h4)). Qed.
Lemma lem5143509 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 b s) (h3 : term9 s) (h4 : term149 b x' s) : term486 x b s.
Proof. exact (@lem5143508 b x b x' s h1 h2 h3 h4). Qed.
Lemma lem5143510 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 b s) (h3 : term9 s) (h4 : term149 b x' s) : term574 x b s.
Proof. exact (fun h0 : term575 x b s => @lem5143509 x b x' s h1 h2 h3 h4). Qed.
Lemma lem5143512 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5143513 (x : type1021) (b : real) (s : real -> Prop) : (term574 x b s) = (term486 x b s).
Proof. exact (@lem5143512 (term486 x b s)). Qed.
Lemma lem5143514 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 b s) (h3 : term9 s) (h4 : term149 b x' s) : term486 x b s.
Proof. exact (EQ_MP (@lem5143513 x b s) (@lem5143510 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5143520 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5143521 (b : real) (_67129 : real) (s : real -> Prop) : (term73 s _67129 b) = (term576 b _67129 s).
Proof. exact (@lem5143520 (real_le _67129 b) (term548 _67129 s)). Qed.
Lemma lem5143527 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5143528 (b : real) (_67129 : real) (s : real -> Prop) : (term577 s _67129 b) = (term578 b _67129 s).
Proof. exact (MK_COMB (@lem5143527) (@lem5143521 b _67129 s)). Qed.
Lemma lem5143534 (b : real) (_67129 : real) (s : real -> Prop) : (term576 b _67129 s) = (term576 b _67129 s).
Proof. exact (eq_refl (term576 b _67129 s)). Qed.
Lemma lem5143535 (b : real) (_67129 : real) (s : real -> Prop) : ((term73 s _67129 b) = (term576 b _67129 s)) = ((term576 b _67129 s) = (term576 b _67129 s)).
Proof. exact (MK_COMB (@lem5143528 b _67129 s) (@lem5143534 b _67129 s)). Qed.
Lemma lem5143537 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5143538 (x : Prop) : (x = x) = True.
Proof. exact (@lem5143537 Prop x). Qed.
Lemma lem5143539 (b : real) (_67129 : real) (s : real -> Prop) : ((term576 b _67129 s) = (term576 b _67129 s)) = True.
Proof. exact (@lem5143538 (term576 b _67129 s)). Qed.
Lemma lem5143540 (b : real) (_67129 : real) (s : real -> Prop) : ((term73 s _67129 b) = (term576 b _67129 s)) = True.
Proof. exact (TRANS (@lem5143535 b _67129 s) (@lem5143539 b _67129 s)). Qed.
Lemma lem5143541 (b : real) (_67129 : real) (s : real -> Prop) : True = ((term73 s _67129 b) = (term576 b _67129 s)).
Proof. exact (SYM (@lem5143540 b _67129 s)). Qed.
Lemma lem5143542 (b : real) (_67129 : real) (s : real -> Prop) : (term73 s _67129 b) = (term576 b _67129 s).
Proof. exact (EQ_MP (@lem5143541 b _67129 s) (@lem0)). Qed.
Lemma lem5143543 (_67129 : real) (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term576 b _67129 s.
Proof. exact (EQ_MP (@lem5143542 b _67129 s) (@lem5142961 _67129 b x' s h1)). Qed.
Lemma lem5143545 (b : Prop) (a : Prop) : (a \/ b) = (term558 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5143546 (s : real -> Prop) (_67129 : real) (b : real) : (term576 b _67129 s) = (term579 s _67129 b).
Proof. exact (@lem5143545 (term548 _67129 s) (real_le _67129 b)). Qed.
Lemma lem5143548 (a : Prop) : (term567 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5143549 (_67129 : real) (s : real -> Prop) : (term568 _67129 s) = (@IN real _67129 s).
Proof. exact (@lem5143548 (@IN real _67129 s)). Qed.
Lemma lem5143550 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5143551 (_67129 : real) (s : real -> Prop) : (term580 _67129 s) = (term581 _67129 s).
Proof. exact (MK_COMB (@lem5143550) (@lem5143549 _67129 s)). Qed.
Lemma lem5143552 (_67129 : real) (b : real) : (real_le _67129 b) = (real_le _67129 b).
Proof. exact (eq_refl (real_le _67129 b)). Qed.
Lemma lem5143553 (s : real -> Prop) (_67129 : real) (b : real) : (term579 s _67129 b) = (term47 s _67129 b).
Proof. exact (MK_COMB (@lem5143551 _67129 s) (@lem5143552 _67129 b)). Qed.
Lemma lem5143554 (s : real -> Prop) (_67129 : real) (b : real) : (term576 b _67129 s) = (term47 s _67129 b).
Proof. exact (TRANS (@lem5143546 s _67129 b) (@lem5143553 s _67129 b)). Qed.
Lemma lem5143557 (_67129 : real) (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term47 s _67129 b.
Proof. exact (EQ_MP (@lem5143554 s _67129 b) (@lem5143543 _67129 b x' s h1)). Qed.
Lemma lem5143558 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term582 x s b.
Proof. exact (@lem5143557 (x s b) b x' s h1). Qed.
Lemma lem5143561 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 b s) (h3 : term9 s) (h4 : term149 b x' s) : term583 x s b.
Proof. exact (@lem5143558 x b x' s h4 (@lem5143514 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5143562 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 b s) (h3 : term9 s) (h4 : term149 b x' s) : term584 x s b.
Proof. exact (fun h0 : term487 x s b => @lem5143561 x b x' s h1 h2 h3 h4). Qed.
Lemma lem5143564 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5143565 (x : type1021) (s : real -> Prop) (b : real) : (term584 x s b) = (term583 x s b).
Proof. exact (@lem5143564 (term583 x s b)). Qed.
Lemma lem5143566 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 b s) (h3 : term9 s) (h4 : term149 b x' s) : term583 x s b.
Proof. exact (EQ_MP (@lem5143565 x s b) (@lem5143562 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5143568 (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : @IN real b s.
Proof. exact (proj1 (@lem5142251 b x' s h1)). Qed.
Lemma lem5143569 (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term547 b s.
Proof. exact (fun h0 : term548 b s => @lem5143568 b x' s h1). Qed.
Lemma lem5143571 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5143572 (b : real) (s : real -> Prop) : (term547 b s) = (@IN real b s).
Proof. exact (@lem5143571 (@IN real b s)). Qed.
Lemma lem5143573 (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : @IN real b s.
Proof. exact (EQ_MP (@lem5143572 b s) (@lem5143569 b x' s h1)). Qed.
Lemma lem5143591 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5143592 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term585 x _67127 _67128 _67126) = (term586 x _67127 _67128 _67126).
Proof. exact (@lem5143591 (term548 _67128 _67126) (term487 x _67126 _67127) (term81 _67128 _67126)). Qed.
Lemma lem5143606 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5143607 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term587 x _67127 _67128 _67126) = (term588 _67128 x _67126 _67127).
Proof. exact (@lem5143606 (term81 _67128 _67126) (term487 x _67126 _67127)). Qed.
Lemma lem5143613 (_67128 : real) (_67126 : real -> Prop) : (term589 _67128 _67126) = (term589 _67128 _67126).
Proof. exact (eq_refl (term589 _67128 _67126)). Qed.
Lemma lem5143614 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term586 x _67127 _67128 _67126) = (term590 _67128 x _67126 _67127).
Proof. exact (MK_COMB (@lem5143613 _67128 _67126) (@lem5143607 _67128 x _67126 _67127)). Qed.
Lemma lem5143618 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5143619 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term590 _67128 x _67126 _67127) = (term591 _67128 x _67126 _67127).
Proof. exact (@lem5143618 (term81 _67128 _67126) (term548 _67128 _67126) (term487 x _67126 _67127)). Qed.
Lemma lem5143635 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term586 x _67127 _67128 _67126) = (term591 _67128 x _67126 _67127).
Proof. exact (TRANS (@lem5143614 _67128 x _67126 _67127) (@lem5143619 _67128 x _67126 _67127)). Qed.
Lemma lem5143636 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term585 x _67127 _67128 _67126) = (term591 _67128 x _67126 _67127).
Proof. exact (TRANS (@lem5143592 x _67127 _67128 _67126) (@lem5143635 _67128 x _67126 _67127)). Qed.
Lemma lem5143637 (_67126 : real -> Prop) : (term175 _67126) = (term175 _67126).
Proof. exact (eq_refl (term175 _67126)). Qed.
Lemma lem5143638 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term532 x _67127 _67128 _67126) = (term592 _67128 x _67126 _67127).
Proof. exact (MK_COMB (@lem5143637 _67126) (@lem5143636 _67128 x _67126 _67127)). Qed.
Lemma lem5143649 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5143650 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term593 x _67127 _67128 _67126) = (term594 _67128 x _67126 _67127).
Proof. exact (MK_COMB (@lem5143649) (@lem5143638 _67128 x _67126 _67127)). Qed.
Lemma lem5143654 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5143655 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term595 x _67127 _67128 _67126) = (term596 x _67127 _67128 _67126).
Proof. exact (@lem5143654 (_67126 = (@EMPTY real)) (term81 _67128 _67126) (term597 x _67127 _67128 _67126)). Qed.
Lemma lem5143681 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5143682 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term597 x _67127 _67128 _67126) = (term598 _67128 x _67126 _67127).
Proof. exact (@lem5143681 (term548 _67128 _67126) (term487 x _67126 _67127)). Qed.
Lemma lem5143688 (_67128 : real) (_67126 : real -> Prop) : (term599 _67128 _67126) = (term599 _67128 _67126).
Proof. exact (eq_refl (term599 _67128 _67126)). Qed.
Lemma lem5143689 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term600 x _67127 _67128 _67126) = (term591 _67128 x _67126 _67127).
Proof. exact (MK_COMB (@lem5143688 _67128 _67126) (@lem5143682 _67128 x _67126 _67127)). Qed.
Lemma lem5143700 (_67126 : real -> Prop) : (term175 _67126) = (term175 _67126).
Proof. exact (eq_refl (term175 _67126)). Qed.
Lemma lem5143701 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term596 x _67127 _67128 _67126) = (term592 _67128 x _67126 _67127).
Proof. exact (MK_COMB (@lem5143700 _67126) (@lem5143689 _67128 x _67126 _67127)). Qed.
Lemma lem5143712 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term595 x _67127 _67128 _67126) = (term592 _67128 x _67126 _67127).
Proof. exact (TRANS (@lem5143655 x _67127 _67128 _67126) (@lem5143701 _67128 x _67126 _67127)). Qed.
Lemma lem5143713 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : ((term532 x _67127 _67128 _67126) = (term595 x _67127 _67128 _67126)) = ((term592 _67128 x _67126 _67127) = (term592 _67128 x _67126 _67127)).
Proof. exact (MK_COMB (@lem5143650 _67128 x _67126 _67127) (@lem5143712 _67128 x _67126 _67127)). Qed.
Lemma lem5143715 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5143716 (x : Prop) : (x = x) = True.
Proof. exact (@lem5143715 Prop x). Qed.
Lemma lem5143717 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : ((term592 _67128 x _67126 _67127) = (term592 _67128 x _67126 _67127)) = True.
Proof. exact (@lem5143716 (term592 _67128 x _67126 _67127)). Qed.
Lemma lem5143718 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : ((term532 x _67127 _67128 _67126) = (term595 x _67127 _67128 _67126)) = True.
Proof. exact (TRANS (@lem5143713 _67128 x _67126 _67127) (@lem5143717 _67128 x _67126 _67127)). Qed.
Lemma lem5143719 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : True = ((term532 x _67127 _67128 _67126) = (term595 x _67127 _67128 _67126)).
Proof. exact (SYM (@lem5143718 x _67127 _67128 _67126)). Qed.
Lemma lem5143720 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term532 x _67127 _67128 _67126) = (term595 x _67127 _67128 _67126).
Proof. exact (EQ_MP (@lem5143719 x _67127 _67128 _67126) (@lem0)). Qed.
Lemma lem5143721 (_67127 : real) (_67128 : real) (_67126 : real -> Prop) (x : type1021) (h1 : term338 x) : term595 x _67127 _67128 _67126.
Proof. exact (EQ_MP (@lem5143720 x _67127 _67128 _67126) (@lem5143087 _67127 _67128 _67126 x h1)). Qed.
Lemma lem5143723 (b : Prop) (a : Prop) : (a \/ b) = (term558 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5143724 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term595 x _67127 _67128 _67126) = (term601 x _67127 _67128 _67126).
Proof. exact (@lem5143723 (term602 x _67127 _67128 _67126) (term81 _67128 _67126)). Qed.
Lemma lem5143726 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5143727 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term603 x _67127 _67128 _67126) = (term604 x _67127 _67128 _67126).
Proof. exact (@lem5143726 (_67126 = (@EMPTY real)) (term597 x _67127 _67128 _67126)). Qed.
Lemma lem5143729 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5143730 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term605 x _67127 _67128 _67126) = (term606 x _67127 _67128 _67126).
Proof. exact (@lem5143729 (term487 x _67126 _67127) (term548 _67128 _67126)). Qed.
Lemma lem5143732 (a : Prop) : (term567 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5143733 (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term607 x _67126 _67127) = (term583 x _67126 _67127).
Proof. exact (@lem5143732 (term583 x _67126 _67127)). Qed.
Lemma lem5143734 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5143735 (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term608 x _67126 _67127) = (term609 x _67126 _67127).
Proof. exact (MK_COMB (@lem5143734) (@lem5143733 x _67126 _67127)). Qed.
Lemma lem5143737 (a : Prop) : (term567 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5143738 (_67128 : real) (_67126 : real -> Prop) : (term568 _67128 _67126) = (@IN real _67128 _67126).
Proof. exact (@lem5143737 (@IN real _67128 _67126)). Qed.
Lemma lem5143739 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term606 x _67127 _67128 _67126) = (term610 x _67127 _67128 _67126).
Proof. exact (MK_COMB (@lem5143735 x _67126 _67127) (@lem5143738 _67128 _67126)). Qed.
Lemma lem5143740 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term605 x _67127 _67128 _67126) = (term610 x _67127 _67128 _67126).
Proof. exact (TRANS (@lem5143730 x _67127 _67128 _67126) (@lem5143739 x _67127 _67128 _67126)). Qed.
Lemma lem5143741 (_67126 : real -> Prop) : (term61 _67126) = (term61 _67126).
Proof. exact (eq_refl (term61 _67126)). Qed.
Lemma lem5143742 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term604 x _67127 _67128 _67126) = (term611 x _67127 _67128 _67126).
Proof. exact (MK_COMB (@lem5143741 _67126) (@lem5143740 x _67127 _67128 _67126)). Qed.
Lemma lem5143743 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term603 x _67127 _67128 _67126) = (term611 x _67127 _67128 _67126).
Proof. exact (TRANS (@lem5143727 x _67127 _67128 _67126) (@lem5143742 x _67127 _67128 _67126)). Qed.
Lemma lem5143744 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5143745 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term612 x _67127 _67128 _67126) = (term613 x _67127 _67128 _67126).
Proof. exact (MK_COMB (@lem5143744) (@lem5143743 x _67127 _67128 _67126)). Qed.
Lemma lem5143746 (_67128 : real) (_67126 : real -> Prop) : (term81 _67128 _67126) = (term81 _67128 _67126).
Proof. exact (eq_refl (term81 _67128 _67126)). Qed.
Lemma lem5143747 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term601 x _67127 _67128 _67126) = (term614 x _67127 _67128 _67126).
Proof. exact (MK_COMB (@lem5143745 x _67127 _67128 _67126) (@lem5143746 _67128 _67126)). Qed.
Lemma lem5143748 (x : type1021) (_67127 : real) (_67128 : real) (_67126 : real -> Prop) : (term595 x _67127 _67128 _67126) = (term614 x _67127 _67128 _67126).
Proof. exact (TRANS (@lem5143724 x _67127 _67128 _67126) (@lem5143747 x _67127 _67128 _67126)). Qed.
Lemma lem5143750 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 b s) (h3 : term9 s) (h4 : term149 b x' s) : term615 x b s.
Proof. exact (conj (@lem5143566 x b x' s h1 h2 h3 h4) (@lem5143573 b x' s h4)). Qed.
Lemma lem5143751 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 b s) (h3 : term9 s) (h4 : term149 b x' s) : term616 x b s.
Proof. exact (conj (@lem5143321 s h3) (@lem5143750 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5143753 (_67127 : real) (_67128 : real) (_67126 : real -> Prop) (x : type1021) (h1 : term338 x) : term614 x _67127 _67128 _67126.
Proof. exact (EQ_MP (@lem5143748 x _67127 _67128 _67126) (@lem5143721 _67127 _67128 _67126 x h1)). Qed.
Lemma lem5143754 (b : real) (s : real -> Prop) (x : type1021) (h1 : term338 x) : term617 x b s.
Proof. exact (@lem5143753 b b s x h1). Qed.
Lemma lem5143757 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 b s) (h3 : term9 s) (h4 : term149 b x' s) : term81 b s.
Proof. exact (@lem5143754 b s x h1 (@lem5143751 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5143758 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b x' s) : term618 b s.
Proof. exact (fun h0 : term533 b s => @lem5143757 x b x' s h1 h0 h2 h3). Qed.
Lemma lem5143760 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5143761 (b : real) (s : real -> Prop) : (term618 b s) = (term81 b s).
Proof. exact (@lem5143760 (term81 b s)). Qed.
Lemma lem5143762 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b x' s) : term81 b s.
Proof. exact (EQ_MP (@lem5143761 b s) (@lem5143758 x b x' s h1 h2 h3)). Qed.
Lemma lem5143764 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (proj2 (@lem5142006 s h1)). Qed.
Lemma lem5143765 (s : real -> Prop) (h1 : term9 s) : term545 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5143764 s h1). Qed.
Lemma lem5143767 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5143768 (s : real -> Prop) : (term545 s) = (term179 s).
Proof. exact (@lem5143767 (s = (@EMPTY real))). Qed.
Lemma lem5143769 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (EQ_MP (@lem5143768 s) (@lem5143765 s h1)). Qed.
Lemma lem5143771 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (proj2 (@lem5142006 s h1)). Qed.
Lemma lem5143772 (s : real -> Prop) (h1 : term9 s) : term545 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5143771 s h1). Qed.
Lemma lem5143774 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5143775 (s : real -> Prop) : (term545 s) = (term179 s).
Proof. exact (@lem5143774 (s = (@EMPTY real))). Qed.
Lemma lem5143776 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (EQ_MP (@lem5143775 s) (@lem5143772 s h1)). Qed.
Lemma lem5143779 (x : type1021) (b : real) (s : real -> Prop) (h1 : term575 x b s) : term575 x b s.
Proof. exact (h1). Qed.
Lemma lem5143780 (x : type1021) (b : real) (s : real -> Prop) (h1 : term575 x b s) : term619 x b s.
Proof. exact (fun h0 : term486 x b s => @lem5143779 x b s h1). Qed.
Lemma lem5143782 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5143783 (x : type1021) (b : real) (s : real -> Prop) : (term619 x b s) = (term575 x b s).
Proof. exact (@lem5143782 (term486 x b s)). Qed.
Lemma lem5143784 (x : type1021) (b : real) (s : real -> Prop) (h1 : term575 x b s) : term575 x b s.
Proof. exact (EQ_MP (@lem5143783 x b s) (@lem5143780 x b s h1)). Qed.
Lemma lem5143787 (s : real -> Prop) (b : real) (h1 : term620 s b) : term620 s b.
Proof. exact (h1). Qed.
Lemma lem5143788 (s : real -> Prop) (b : real) (h1 : term620 s b) : term621 s b.
Proof. exact (fun h0 : term46 s b => @lem5143787 s b h1). Qed.
Lemma lem5143790 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5143791 (s : real -> Prop) (b : real) : (term621 s b) = (term620 s b).
Proof. exact (@lem5143790 (term46 s b)). Qed.
Lemma lem5143792 (s : real -> Prop) (b : real) (h1 : term620 s b) : term620 s b.
Proof. exact (EQ_MP (@lem5143791 s b) (@lem5143788 s b h1)). Qed.
Lemma lem5143825 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5143826 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term622 x _67127 _67126 _67128) = (term623 x _67127 _67126 _67128).
Proof. exact (@lem5143825 (_67126 = (@EMPTY real)) (term486 x _67128 _67126) (term624 x _67127 _67126 _67128)). Qed.
Lemma lem5143842 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5143843 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term625 x _67127 _67126 _67128) = (term626 _67127 x _67126 _67128).
Proof. exact (@lem5143842 (term486 x _67127 _67126) (term486 x _67128 _67126) (term46 _67126 _67128)). Qed.
Lemma lem5143859 (_67126 : real -> Prop) : (term175 _67126) = (term175 _67126).
Proof. exact (eq_refl (term175 _67126)). Qed.
Lemma lem5143860 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term623 x _67127 _67126 _67128) = (term529 _67127 x _67126 _67128).
Proof. exact (MK_COMB (@lem5143859 _67126) (@lem5143843 _67127 x _67126 _67128)). Qed.
Lemma lem5143871 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term622 x _67127 _67126 _67128) = (term529 _67127 x _67126 _67128).
Proof. exact (TRANS (@lem5143826 x _67127 _67126 _67128) (@lem5143860 _67127 x _67126 _67128)). Qed.
Lemma lem5143872 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term627 _67127 x _67126 _67128) = (term627 _67127 x _67126 _67128).
Proof. exact (eq_refl (term627 _67127 x _67126 _67128)). Qed.
Lemma lem5143873 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : ((term529 _67127 x _67126 _67128) = (term622 x _67127 _67126 _67128)) = ((term529 _67127 x _67126 _67128) = (term529 _67127 x _67126 _67128)).
Proof. exact (MK_COMB (@lem5143872 _67127 x _67126 _67128) (@lem5143871 _67127 x _67126 _67128)). Qed.
Lemma lem5143875 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5143876 (x : Prop) : (x = x) = True.
Proof. exact (@lem5143875 Prop x). Qed.
Lemma lem5143877 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : ((term529 _67127 x _67126 _67128) = (term529 _67127 x _67126 _67128)) = True.
Proof. exact (@lem5143876 (term529 _67127 x _67126 _67128)). Qed.
Lemma lem5143878 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : ((term529 _67127 x _67126 _67128) = (term622 x _67127 _67126 _67128)) = True.
Proof. exact (TRANS (@lem5143873 _67127 x _67126 _67128) (@lem5143877 _67127 x _67126 _67128)). Qed.
Lemma lem5143879 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : True = ((term529 _67127 x _67126 _67128) = (term622 x _67127 _67126 _67128)).
Proof. exact (SYM (@lem5143878 x _67127 _67126 _67128)). Qed.
Lemma lem5143880 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term529 _67127 x _67126 _67128) = (term622 x _67127 _67126 _67128).
Proof. exact (EQ_MP (@lem5143879 x _67127 _67126 _67128) (@lem0)). Qed.
Lemma lem5143881 (_67127 : real) (_67126 : real -> Prop) (_67128 : real) (x : type1021) (h1 : term338 x) : term622 x _67127 _67126 _67128.
Proof. exact (EQ_MP (@lem5143880 x _67127 _67126 _67128) (@lem5143039 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5143883 (b : Prop) (a : Prop) : (a \/ b) = (term558 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5143884 (_67127 : real) (x : type1021) (_67128 : real) (_67126 : real -> Prop) : (term622 x _67127 _67126 _67128) = (term628 _67127 x _67128 _67126).
Proof. exact (@lem5143883 (term629 x _67127 _67126 _67128) (term486 x _67128 _67126)). Qed.
Lemma lem5143886 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5143887 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term630 x _67127 _67126 _67128) = (term631 x _67127 _67126 _67128).
Proof. exact (@lem5143886 (_67126 = (@EMPTY real)) (term624 x _67127 _67126 _67128)). Qed.
Lemma lem5143889 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5143890 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term632 x _67127 _67126 _67128) = (term633 x _67127 _67126 _67128).
Proof. exact (@lem5143889 (term486 x _67127 _67126) (term46 _67126 _67128)). Qed.
Lemma lem5143891 (_67126 : real -> Prop) : (term61 _67126) = (term61 _67126).
Proof. exact (eq_refl (term61 _67126)). Qed.
Lemma lem5143892 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term631 x _67127 _67126 _67128) = (term634 x _67127 _67126 _67128).
Proof. exact (MK_COMB (@lem5143891 _67126) (@lem5143890 x _67127 _67126 _67128)). Qed.
Lemma lem5143893 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term630 x _67127 _67126 _67128) = (term634 x _67127 _67126 _67128).
Proof. exact (TRANS (@lem5143887 x _67127 _67126 _67128) (@lem5143892 x _67127 _67126 _67128)). Qed.
Lemma lem5143894 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5143895 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term635 x _67127 _67126 _67128) = (term636 x _67127 _67126 _67128).
Proof. exact (MK_COMB (@lem5143894) (@lem5143893 x _67127 _67126 _67128)). Qed.
Lemma lem5143896 (x : type1021) (_67128 : real) (_67126 : real -> Prop) : (term486 x _67128 _67126) = (term486 x _67128 _67126).
Proof. exact (eq_refl (term486 x _67128 _67126)). Qed.
Lemma lem5143897 (_67127 : real) (x : type1021) (_67128 : real) (_67126 : real -> Prop) : (term628 _67127 x _67128 _67126) = (term637 _67127 x _67128 _67126).
Proof. exact (MK_COMB (@lem5143895 x _67127 _67126 _67128) (@lem5143896 x _67128 _67126)). Qed.
Lemma lem5143898 (_67127 : real) (x : type1021) (_67128 : real) (_67126 : real -> Prop) : (term622 x _67127 _67126 _67128) = (term637 _67127 x _67128 _67126).
Proof. exact (TRANS (@lem5143884 _67127 x _67128 _67126) (@lem5143897 _67127 x _67128 _67126)). Qed.
Lemma lem5143900 (x : type1021) (s : real -> Prop) (b : real) (h1 : term575 x b s) (h2 : term620 s b) : term638 x s b.
Proof. exact (conj (@lem5143784 x b s h1) (@lem5143792 s b h2)). Qed.
Lemma lem5143901 (x : type1021) (b : real) (s : real -> Prop) (h1 : term575 x b s) (h2 : term620 s b) (h3 : term9 s) : term639 x s b.
Proof. exact (conj (@lem5143776 s h3) (@lem5143900 x s b h1 h2)). Qed.
Lemma lem5143903 (_67127 : real) (_67128 : real) (_67126 : real -> Prop) (x : type1021) (h1 : term338 x) : term637 _67127 x _67128 _67126.
Proof. exact (EQ_MP (@lem5143898 _67127 x _67128 _67126) (@lem5143881 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5143904 (b : real) (s : real -> Prop) (x : type1021) (h1 : term338 x) : term640 x b s.
Proof. exact (@lem5143903 b b s x h1). Qed.
Lemma lem5143907 (x : type1021) (b : real) (s : real -> Prop) (h1 : term338 x) (h2 : term575 x b s) (h3 : term620 s b) (h4 : term9 s) : term486 x b s.
Proof. exact (@lem5143904 b s x h1 (@lem5143901 x b s h2 h3 h4)). Qed.
Lemma lem5143908 (x : type1021) (b : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) : term574 x b s.
Proof. exact (fun h0 : term575 x b s => @lem5143907 x b s h1 h0 h2 h3). Qed.
Lemma lem5143910 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5143911 (x : type1021) (b : real) (s : real -> Prop) : (term574 x b s) = (term486 x b s).
Proof. exact (@lem5143910 (term486 x b s)). Qed.
Lemma lem5143912 (x : type1021) (b : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) : term486 x b s.
Proof. exact (EQ_MP (@lem5143911 x b s) (@lem5143908 x b s h1 h2 h3)). Qed.
Lemma lem5143914 (_67129 : real) (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term47 s _67129 b.
Proof. exact (EQ_MP (@lem5143554 s _67129 b) (@lem5143543 _67129 b x' s h1)). Qed.
Lemma lem5143915 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term582 x s b.
Proof. exact (@lem5143914 (x s b) b x' s h1). Qed.
Lemma lem5143918 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term583 x s b.
Proof. exact (@lem5143915 x b x' s h4 (@lem5143912 x b s h1 h2 h3)). Qed.
Lemma lem5143919 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term584 x s b.
Proof. exact (fun h0 : term487 x s b => @lem5143918 x b x' s h1 h2 h3 h4). Qed.
Lemma lem5143921 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5143922 (x : type1021) (s : real -> Prop) (b : real) : (term584 x s b) = (term583 x s b).
Proof. exact (@lem5143921 (term583 x s b)). Qed.
Lemma lem5143923 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term583 x s b.
Proof. exact (EQ_MP (@lem5143922 x s b) (@lem5143919 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5143925 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (proj2 (@lem5142006 s h1)). Qed.
Lemma lem5143926 (s : real -> Prop) (h1 : term9 s) : term545 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5143925 s h1). Qed.
Lemma lem5143928 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5143929 (s : real -> Prop) : (term545 s) = (term179 s).
Proof. exact (@lem5143928 (s = (@EMPTY real))). Qed.
Lemma lem5143930 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (EQ_MP (@lem5143929 s) (@lem5143926 s h1)). Qed.
Lemma lem5143932 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (proj2 (@lem5142006 s h1)). Qed.
Lemma lem5143933 (s : real -> Prop) (h1 : term9 s) : term545 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5143932 s h1). Qed.
Lemma lem5143935 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5143936 (s : real -> Prop) : (term545 s) = (term179 s).
Proof. exact (@lem5143935 (s = (@EMPTY real))). Qed.
Lemma lem5143937 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (EQ_MP (@lem5143936 s) (@lem5143933 s h1)). Qed.
Lemma lem5143940 (x : type1021) (b : real) (s : real -> Prop) (h1 : term575 x b s) : term575 x b s.
Proof. exact (h1). Qed.
Lemma lem5143941 (x : type1021) (b : real) (s : real -> Prop) (h1 : term575 x b s) : term619 x b s.
Proof. exact (fun h0 : term486 x b s => @lem5143940 x b s h1). Qed.
Lemma lem5143943 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5143944 (x : type1021) (b : real) (s : real -> Prop) : (term619 x b s) = (term575 x b s).
Proof. exact (@lem5143943 (term486 x b s)). Qed.
Lemma lem5143945 (x : type1021) (b : real) (s : real -> Prop) (h1 : term575 x b s) : term575 x b s.
Proof. exact (EQ_MP (@lem5143944 x b s) (@lem5143941 x b s h1)). Qed.
Lemma lem5143948 (s : real -> Prop) (b : real) (h1 : term620 s b) : term620 s b.
Proof. exact (h1). Qed.
Lemma lem5143949 (s : real -> Prop) (b : real) (h1 : term620 s b) : term621 s b.
Proof. exact (fun h0 : term46 s b => @lem5143948 s b h1). Qed.
Lemma lem5143951 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5143952 (s : real -> Prop) (b : real) : (term621 s b) = (term620 s b).
Proof. exact (@lem5143951 (term46 s b)). Qed.
Lemma lem5143953 (s : real -> Prop) (b : real) (h1 : term620 s b) : term620 s b.
Proof. exact (EQ_MP (@lem5143952 s b) (@lem5143949 s b h1)). Qed.
Lemma lem5143954 (x : type1021) (s : real -> Prop) (b : real) (h1 : term575 x b s) (h2 : term620 s b) : term638 x s b.
Proof. exact (conj (@lem5143945 x b s h1) (@lem5143953 s b h2)). Qed.
Lemma lem5143955 (x : type1021) (b : real) (s : real -> Prop) (h1 : term575 x b s) (h2 : term620 s b) (h3 : term9 s) : term639 x s b.
Proof. exact (conj (@lem5143937 s h3) (@lem5143954 x s b h1 h2)). Qed.
Lemma lem5143957 (_67127 : real) (_67128 : real) (_67126 : real -> Prop) (x : type1021) (h1 : term338 x) : term637 _67127 x _67128 _67126.
Proof. exact (EQ_MP (@lem5143898 _67127 x _67128 _67126) (@lem5143881 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5143958 (b : real) (s : real -> Prop) (x : type1021) (h1 : term338 x) : term640 x b s.
Proof. exact (@lem5143957 b b s x h1). Qed.
Lemma lem5143961 (x : type1021) (b : real) (s : real -> Prop) (h1 : term338 x) (h2 : term575 x b s) (h3 : term620 s b) (h4 : term9 s) : term486 x b s.
Proof. exact (@lem5143958 b s x h1 (@lem5143955 x b s h2 h3 h4)). Qed.
Lemma lem5143962 (x : type1021) (b : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) : term574 x b s.
Proof. exact (fun h0 : term575 x b s => @lem5143961 x b s h1 h0 h2 h3). Qed.
Lemma lem5143964 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5143965 (x : type1021) (b : real) (s : real -> Prop) : (term574 x b s) = (term486 x b s).
Proof. exact (@lem5143964 (term486 x b s)). Qed.
Lemma lem5143966 (x : type1021) (b : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) : term486 x b s.
Proof. exact (EQ_MP (@lem5143965 x b s) (@lem5143962 x b s h1 h2 h3)). Qed.
Lemma lem5143968 (_67129 : real) (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term47 s _67129 b.
Proof. exact (EQ_MP (@lem5143554 s _67129 b) (@lem5143543 _67129 b x' s h1)). Qed.
Lemma lem5143969 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term582 x s b.
Proof. exact (@lem5143968 (x s b) b x' s h1). Qed.
Lemma lem5143972 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term583 x s b.
Proof. exact (@lem5143969 x b x' s h4 (@lem5143966 x b s h1 h2 h3)). Qed.
Lemma lem5143973 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term584 x s b.
Proof. exact (fun h0 : term487 x s b => @lem5143972 x b x' s h1 h2 h3 h4). Qed.
Lemma lem5143975 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5143976 (x : type1021) (s : real -> Prop) (b : real) : (term584 x s b) = (term583 x s b).
Proof. exact (@lem5143975 (term583 x s b)). Qed.
Lemma lem5143977 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term583 x s b.
Proof. exact (EQ_MP (@lem5143976 x s b) (@lem5143973 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5143980 (s : real -> Prop) (b : real) (h1 : term620 s b) : term620 s b.
Proof. exact (h1). Qed.
Lemma lem5143981 (s : real -> Prop) (b : real) (h1 : term620 s b) : term621 s b.
Proof. exact (fun h0 : term46 s b => @lem5143980 s b h1). Qed.
Lemma lem5143983 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5143984 (s : real -> Prop) (b : real) : (term621 s b) = (term620 s b).
Proof. exact (@lem5143983 (term46 s b)). Qed.
Lemma lem5143985 (s : real -> Prop) (b : real) (h1 : term620 s b) : term620 s b.
Proof. exact (EQ_MP (@lem5143984 s b) (@lem5143981 s b h1)). Qed.
Lemma lem5144013 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5144014 (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term496 x _67126 _67128) = (term641 x _67126 _67128).
Proof. exact (@lem5144013 (term46 _67126 _67128) (term487 x _67126 _67128)). Qed.
Lemma lem5144020 (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term642 x _67126 _67127) = (term642 x _67126 _67127).
Proof. exact (eq_refl (term642 x _67126 _67127)). Qed.
Lemma lem5144021 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term643 _67127 x _67126 _67128) = (term644 _67127 x _67126 _67128).
Proof. exact (MK_COMB (@lem5144020 x _67126 _67127) (@lem5144014 x _67126 _67128)). Qed.
Lemma lem5144025 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5144026 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term644 _67127 x _67126 _67128) = (term645 _67127 x _67126 _67128).
Proof. exact (@lem5144025 (term46 _67126 _67128) (term487 x _67126 _67127) (term487 x _67126 _67128)). Qed.
Lemma lem5144042 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term643 _67127 x _67126 _67128) = (term645 _67127 x _67126 _67128).
Proof. exact (TRANS (@lem5144021 _67127 x _67126 _67128) (@lem5144026 _67127 x _67126 _67128)). Qed.
Lemma lem5144043 (_67126 : real -> Prop) : (term175 _67126) = (term175 _67126).
Proof. exact (eq_refl (term175 _67126)). Qed.
Lemma lem5144044 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term528 _67127 x _67126 _67128) = (term646 _67127 x _67126 _67128).
Proof. exact (MK_COMB (@lem5144043 _67126) (@lem5144042 _67127 x _67126 _67128)). Qed.
Lemma lem5144055 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5144056 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term647 _67127 x _67126 _67128) = (term648 _67127 x _67126 _67128).
Proof. exact (MK_COMB (@lem5144055) (@lem5144044 _67127 x _67126 _67128)). Qed.
Lemma lem5144060 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5144061 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term649 x _67127 _67126 _67128) = (term650 x _67127 _67126 _67128).
Proof. exact (@lem5144060 (_67126 = (@EMPTY real)) (term487 x _67126 _67128) (term651 x _67127 _67126 _67128)). Qed.
Lemma lem5144077 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5144078 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term652 x _67127 _67126 _67128) = (term643 _67127 x _67126 _67128).
Proof. exact (@lem5144077 (term487 x _67126 _67127) (term487 x _67126 _67128) (term46 _67126 _67128)). Qed.
Lemma lem5144092 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5144093 (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term496 x _67126 _67128) = (term641 x _67126 _67128).
Proof. exact (@lem5144092 (term46 _67126 _67128) (term487 x _67126 _67128)). Qed.
Lemma lem5144099 (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term642 x _67126 _67127) = (term642 x _67126 _67127).
Proof. exact (eq_refl (term642 x _67126 _67127)). Qed.
Lemma lem5144100 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term643 _67127 x _67126 _67128) = (term644 _67127 x _67126 _67128).
Proof. exact (MK_COMB (@lem5144099 x _67126 _67127) (@lem5144093 x _67126 _67128)). Qed.
Lemma lem5144104 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5144105 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term644 _67127 x _67126 _67128) = (term645 _67127 x _67126 _67128).
Proof. exact (@lem5144104 (term46 _67126 _67128) (term487 x _67126 _67127) (term487 x _67126 _67128)). Qed.
Lemma lem5144121 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term643 _67127 x _67126 _67128) = (term645 _67127 x _67126 _67128).
Proof. exact (TRANS (@lem5144100 _67127 x _67126 _67128) (@lem5144105 _67127 x _67126 _67128)). Qed.
Lemma lem5144122 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term652 x _67127 _67126 _67128) = (term645 _67127 x _67126 _67128).
Proof. exact (TRANS (@lem5144078 _67127 x _67126 _67128) (@lem5144121 _67127 x _67126 _67128)). Qed.
Lemma lem5144123 (_67126 : real -> Prop) : (term175 _67126) = (term175 _67126).
Proof. exact (eq_refl (term175 _67126)). Qed.
Lemma lem5144124 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term650 x _67127 _67126 _67128) = (term646 _67127 x _67126 _67128).
Proof. exact (MK_COMB (@lem5144123 _67126) (@lem5144122 _67127 x _67126 _67128)). Qed.
Lemma lem5144135 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term649 x _67127 _67126 _67128) = (term646 _67127 x _67126 _67128).
Proof. exact (TRANS (@lem5144061 x _67127 _67126 _67128) (@lem5144124 _67127 x _67126 _67128)). Qed.
Lemma lem5144136 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : ((term528 _67127 x _67126 _67128) = (term649 x _67127 _67126 _67128)) = ((term646 _67127 x _67126 _67128) = (term646 _67127 x _67126 _67128)).
Proof. exact (MK_COMB (@lem5144056 _67127 x _67126 _67128) (@lem5144135 _67127 x _67126 _67128)). Qed.
Lemma lem5144138 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5144139 (x : Prop) : (x = x) = True.
Proof. exact (@lem5144138 Prop x). Qed.
Lemma lem5144140 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : ((term646 _67127 x _67126 _67128) = (term646 _67127 x _67126 _67128)) = True.
Proof. exact (@lem5144139 (term646 _67127 x _67126 _67128)). Qed.
Lemma lem5144141 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : ((term528 _67127 x _67126 _67128) = (term649 x _67127 _67126 _67128)) = True.
Proof. exact (TRANS (@lem5144136 _67127 x _67126 _67128) (@lem5144140 _67127 x _67126 _67128)). Qed.
Lemma lem5144142 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : True = ((term528 _67127 x _67126 _67128) = (term649 x _67127 _67126 _67128)).
Proof. exact (SYM (@lem5144141 x _67127 _67126 _67128)). Qed.
Lemma lem5144143 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term528 _67127 x _67126 _67128) = (term649 x _67127 _67126 _67128).
Proof. exact (EQ_MP (@lem5144142 x _67127 _67126 _67128) (@lem0)). Qed.
Lemma lem5144144 (_67127 : real) (_67126 : real -> Prop) (_67128 : real) (x : type1021) (h1 : term338 x) : term649 x _67127 _67126 _67128.
Proof. exact (EQ_MP (@lem5144143 x _67127 _67126 _67128) (@lem5143023 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5144146 (b : Prop) (a : Prop) : (a \/ b) = (term558 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5144147 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term649 x _67127 _67126 _67128) = (term653 _67127 x _67126 _67128).
Proof. exact (@lem5144146 (term654 x _67127 _67126 _67128) (term487 x _67126 _67128)). Qed.
Lemma lem5144149 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5144150 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term655 x _67127 _67126 _67128) = (term656 x _67127 _67126 _67128).
Proof. exact (@lem5144149 (_67126 = (@EMPTY real)) (term651 x _67127 _67126 _67128)). Qed.
Lemma lem5144152 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5144153 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term657 x _67127 _67126 _67128) = (term658 x _67127 _67126 _67128).
Proof. exact (@lem5144152 (term487 x _67126 _67127) (term46 _67126 _67128)). Qed.
Lemma lem5144155 (a : Prop) : (term567 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5144156 (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term607 x _67126 _67127) = (term583 x _67126 _67127).
Proof. exact (@lem5144155 (term583 x _67126 _67127)). Qed.
Lemma lem5144157 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5144158 (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term608 x _67126 _67127) = (term609 x _67126 _67127).
Proof. exact (MK_COMB (@lem5144157) (@lem5144156 x _67126 _67127)). Qed.
Lemma lem5144159 (_67126 : real -> Prop) (_67128 : real) : (term620 _67126 _67128) = (term620 _67126 _67128).
Proof. exact (eq_refl (term620 _67126 _67128)). Qed.
Lemma lem5144160 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term658 x _67127 _67126 _67128) = (term659 x _67127 _67126 _67128).
Proof. exact (MK_COMB (@lem5144158 x _67126 _67127) (@lem5144159 _67126 _67128)). Qed.
Lemma lem5144161 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term657 x _67127 _67126 _67128) = (term659 x _67127 _67126 _67128).
Proof. exact (TRANS (@lem5144153 x _67127 _67126 _67128) (@lem5144160 x _67127 _67126 _67128)). Qed.
Lemma lem5144162 (_67126 : real -> Prop) : (term61 _67126) = (term61 _67126).
Proof. exact (eq_refl (term61 _67126)). Qed.
Lemma lem5144163 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term656 x _67127 _67126 _67128) = (term660 x _67127 _67126 _67128).
Proof. exact (MK_COMB (@lem5144162 _67126) (@lem5144161 x _67127 _67126 _67128)). Qed.
Lemma lem5144164 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term655 x _67127 _67126 _67128) = (term660 x _67127 _67126 _67128).
Proof. exact (TRANS (@lem5144150 x _67127 _67126 _67128) (@lem5144163 x _67127 _67126 _67128)). Qed.
Lemma lem5144165 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5144166 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term661 x _67127 _67126 _67128) = (term662 x _67127 _67126 _67128).
Proof. exact (MK_COMB (@lem5144165) (@lem5144164 x _67127 _67126 _67128)). Qed.
Lemma lem5144167 (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term487 x _67126 _67128) = (term487 x _67126 _67128).
Proof. exact (eq_refl (term487 x _67126 _67128)). Qed.
Lemma lem5144168 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term653 _67127 x _67126 _67128) = (term663 _67127 x _67126 _67128).
Proof. exact (MK_COMB (@lem5144166 x _67127 _67126 _67128) (@lem5144167 x _67126 _67128)). Qed.
Lemma lem5144169 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term649 x _67127 _67126 _67128) = (term663 _67127 x _67126 _67128).
Proof. exact (TRANS (@lem5144147 _67127 x _67126 _67128) (@lem5144168 _67127 x _67126 _67128)). Qed.
Lemma lem5144171 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term664 x s b.
Proof. exact (conj (@lem5143977 x b x' s h1 h2 h3 h4) (@lem5143985 s b h2)). Qed.
Lemma lem5144172 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term665 x s b.
Proof. exact (conj (@lem5143930 s h3) (@lem5144171 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5144174 (_67127 : real) (_67126 : real -> Prop) (_67128 : real) (x : type1021) (h1 : term338 x) : term663 _67127 x _67126 _67128.
Proof. exact (EQ_MP (@lem5144169 _67127 x _67126 _67128) (@lem5144144 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5144175 (s : real -> Prop) (b : real) (x : type1021) (h1 : term338 x) : term666 x s b.
Proof. exact (@lem5144174 b s b x h1). Qed.
Lemma lem5144178 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term487 x s b.
Proof. exact (@lem5144175 s b x h1 (@lem5144172 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5144179 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term667 x s b.
Proof. exact (fun h0 : term583 x s b => @lem5144178 x b x' s h1 h2 h3 h4). Qed.
Lemma lem5144181 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5144182 (x : type1021) (s : real -> Prop) (b : real) : (term667 x s b) = (term487 x s b).
Proof. exact (@lem5144181 (term583 x s b)). Qed.
Lemma lem5144183 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term487 x s b.
Proof. exact (EQ_MP (@lem5144182 x s b) (@lem5144179 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5144185 (b : Prop) (a : Prop) : (a \/ b) = (term558 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5144188 (b : real) (_67129 : real) (s : real -> Prop) : (term73 s _67129 b) = (term668 b _67129 s).
Proof. exact (@lem5144185 (real_le _67129 b) (term548 _67129 s)). Qed.
Lemma lem5144191 (_67129 : real) (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term668 b _67129 s.
Proof. exact (EQ_MP (@lem5144188 b _67129 s) (@lem5142961 _67129 b x' s h1)). Qed.
Lemma lem5144192 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term669 x b s.
Proof. exact (@lem5144191 (x s b) b x' s h1). Qed.
Lemma lem5144195 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term575 x b s.
Proof. exact (@lem5144192 x b x' s h4 (@lem5144183 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5144196 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term619 x b s.
Proof. exact (fun h0 : term486 x b s => @lem5144195 x b x' s h1 h2 h3 h4). Qed.
Lemma lem5144198 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5144199 (x : type1021) (b : real) (s : real -> Prop) : (term619 x b s) = (term575 x b s).
Proof. exact (@lem5144198 (term486 x b s)). Qed.
Lemma lem5144200 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term575 x b s.
Proof. exact (EQ_MP (@lem5144199 x b s) (@lem5144196 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5144218 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5144219 (x : type1021) (_67127 : real) (_67126 : real -> Prop) (_67128 : real) : (term670 _67127 x _67126 _67128) = (term671 x _67127 _67126 _67128).
Proof. exact (@lem5144218 (term486 x _67128 _67126) (term487 x _67126 _67127) (term46 _67126 _67128)). Qed.
Lemma lem5144233 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5144234 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term651 x _67127 _67126 _67128) = (term672 _67128 x _67126 _67127).
Proof. exact (@lem5144233 (term46 _67126 _67128) (term487 x _67126 _67127)). Qed.
Lemma lem5144240 (x : type1021) (_67128 : real) (_67126 : real -> Prop) : (term551 x _67128 _67126) = (term551 x _67128 _67126).
Proof. exact (eq_refl (term551 x _67128 _67126)). Qed.
Lemma lem5144241 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term671 x _67127 _67126 _67128) = (term673 _67128 x _67126 _67127).
Proof. exact (MK_COMB (@lem5144240 x _67128 _67126) (@lem5144234 _67128 x _67126 _67127)). Qed.
Lemma lem5144252 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term670 _67127 x _67126 _67128) = (term673 _67128 x _67126 _67127).
Proof. exact (TRANS (@lem5144219 x _67127 _67126 _67128) (@lem5144241 _67128 x _67126 _67127)). Qed.
Lemma lem5144253 (_67126 : real -> Prop) : (term175 _67126) = (term175 _67126).
Proof. exact (eq_refl (term175 _67126)). Qed.
Lemma lem5144254 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term530 _67127 x _67126 _67128) = (term674 _67128 x _67126 _67127).
Proof. exact (MK_COMB (@lem5144253 _67126) (@lem5144252 _67128 x _67126 _67127)). Qed.
Lemma lem5144265 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5144266 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term675 _67127 x _67126 _67128) = (term676 _67128 x _67126 _67127).
Proof. exact (MK_COMB (@lem5144265) (@lem5144254 _67128 x _67126 _67127)). Qed.
Lemma lem5144270 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5144271 (_67127 : real) (x : type1021) (_67128 : real) (_67126 : real -> Prop) : (term677 _67127 x _67128 _67126) = (term678 _67127 x _67128 _67126).
Proof. exact (@lem5144270 (_67126 = (@EMPTY real)) (term46 _67126 _67128) (term679 _67127 x _67128 _67126)). Qed.
Lemma lem5144297 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5144298 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term679 _67127 x _67128 _67126) = (term680 _67128 x _67126 _67127).
Proof. exact (@lem5144297 (term486 x _67128 _67126) (term487 x _67126 _67127)). Qed.
Lemma lem5144304 (_67126 : real -> Prop) (_67128 : real) : (term681 _67126 _67128) = (term681 _67126 _67128).
Proof. exact (eq_refl (term681 _67126 _67128)). Qed.
Lemma lem5144305 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term682 _67127 x _67128 _67126) = (term683 _67128 x _67126 _67127).
Proof. exact (MK_COMB (@lem5144304 _67126 _67128) (@lem5144298 _67128 x _67126 _67127)). Qed.
Lemma lem5144309 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5144310 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term683 _67128 x _67126 _67127) = (term673 _67128 x _67126 _67127).
Proof. exact (@lem5144309 (term486 x _67128 _67126) (term46 _67126 _67128) (term487 x _67126 _67127)). Qed.
Lemma lem5144326 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term682 _67127 x _67128 _67126) = (term673 _67128 x _67126 _67127).
Proof. exact (TRANS (@lem5144305 _67128 x _67126 _67127) (@lem5144310 _67128 x _67126 _67127)). Qed.
Lemma lem5144327 (_67126 : real -> Prop) : (term175 _67126) = (term175 _67126).
Proof. exact (eq_refl (term175 _67126)). Qed.
Lemma lem5144328 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term678 _67127 x _67128 _67126) = (term674 _67128 x _67126 _67127).
Proof. exact (MK_COMB (@lem5144327 _67126) (@lem5144326 _67128 x _67126 _67127)). Qed.
Lemma lem5144339 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term677 _67127 x _67128 _67126) = (term674 _67128 x _67126 _67127).
Proof. exact (TRANS (@lem5144271 _67127 x _67128 _67126) (@lem5144328 _67128 x _67126 _67127)). Qed.
Lemma lem5144340 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : ((term530 _67127 x _67126 _67128) = (term677 _67127 x _67128 _67126)) = ((term674 _67128 x _67126 _67127) = (term674 _67128 x _67126 _67127)).
Proof. exact (MK_COMB (@lem5144266 _67128 x _67126 _67127) (@lem5144339 _67128 x _67126 _67127)). Qed.
Lemma lem5144342 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5144343 (x : Prop) : (x = x) = True.
Proof. exact (@lem5144342 Prop x). Qed.
Lemma lem5144344 (_67128 : real) (x : type1021) (_67126 : real -> Prop) (_67127 : real) : ((term674 _67128 x _67126 _67127) = (term674 _67128 x _67126 _67127)) = True.
Proof. exact (@lem5144343 (term674 _67128 x _67126 _67127)). Qed.
Lemma lem5144345 (_67127 : real) (x : type1021) (_67128 : real) (_67126 : real -> Prop) : ((term530 _67127 x _67126 _67128) = (term677 _67127 x _67128 _67126)) = True.
Proof. exact (TRANS (@lem5144340 _67128 x _67126 _67127) (@lem5144344 _67128 x _67126 _67127)). Qed.
Lemma lem5144346 (_67127 : real) (x : type1021) (_67128 : real) (_67126 : real -> Prop) : True = ((term530 _67127 x _67126 _67128) = (term677 _67127 x _67128 _67126)).
Proof. exact (SYM (@lem5144345 _67127 x _67128 _67126)). Qed.
Lemma lem5144347 (_67127 : real) (x : type1021) (_67128 : real) (_67126 : real -> Prop) : (term530 _67127 x _67126 _67128) = (term677 _67127 x _67128 _67126).
Proof. exact (EQ_MP (@lem5144346 _67127 x _67128 _67126) (@lem0)). Qed.
Lemma lem5144348 (_67127 : real) (_67128 : real) (_67126 : real -> Prop) (x : type1021) (h1 : term338 x) : term677 _67127 x _67128 _67126.
Proof. exact (EQ_MP (@lem5144347 _67127 x _67128 _67126) (@lem5143055 _67127 _67126 _67128 x h1)). Qed.
Lemma lem5144350 (b : Prop) (a : Prop) : (a \/ b) = (term558 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5144351 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term677 _67127 x _67128 _67126) = (term684 _67127 x _67126 _67128).
Proof. exact (@lem5144350 (term685 _67127 x _67128 _67126) (term46 _67126 _67128)). Qed.
Lemma lem5144353 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5144354 (_67127 : real) (x : type1021) (_67128 : real) (_67126 : real -> Prop) : (term686 _67127 x _67128 _67126) = (term687 _67127 x _67128 _67126).
Proof. exact (@lem5144353 (_67126 = (@EMPTY real)) (term679 _67127 x _67128 _67126)). Qed.
Lemma lem5144356 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5144357 (_67127 : real) (x : type1021) (_67128 : real) (_67126 : real -> Prop) : (term688 _67127 x _67128 _67126) = (term689 _67127 x _67128 _67126).
Proof. exact (@lem5144356 (term487 x _67126 _67127) (term486 x _67128 _67126)). Qed.
Lemma lem5144359 (a : Prop) : (term567 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5144360 (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term607 x _67126 _67127) = (term583 x _67126 _67127).
Proof. exact (@lem5144359 (term583 x _67126 _67127)). Qed.
Lemma lem5144361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5144362 (x : type1021) (_67126 : real -> Prop) (_67127 : real) : (term608 x _67126 _67127) = (term609 x _67126 _67127).
Proof. exact (MK_COMB (@lem5144361) (@lem5144360 x _67126 _67127)). Qed.
Lemma lem5144363 (x : type1021) (_67128 : real) (_67126 : real -> Prop) : (term575 x _67128 _67126) = (term575 x _67128 _67126).
Proof. exact (eq_refl (term575 x _67128 _67126)). Qed.
Lemma lem5144364 (_67127 : real) (x : type1021) (_67128 : real) (_67126 : real -> Prop) : (term689 _67127 x _67128 _67126) = (term690 _67127 x _67128 _67126).
Proof. exact (MK_COMB (@lem5144362 x _67126 _67127) (@lem5144363 x _67128 _67126)). Qed.
Lemma lem5144365 (_67127 : real) (x : type1021) (_67128 : real) (_67126 : real -> Prop) : (term688 _67127 x _67128 _67126) = (term690 _67127 x _67128 _67126).
Proof. exact (TRANS (@lem5144357 _67127 x _67128 _67126) (@lem5144364 _67127 x _67128 _67126)). Qed.
Lemma lem5144366 (_67126 : real -> Prop) : (term61 _67126) = (term61 _67126).
Proof. exact (eq_refl (term61 _67126)). Qed.
Lemma lem5144367 (_67127 : real) (x : type1021) (_67128 : real) (_67126 : real -> Prop) : (term687 _67127 x _67128 _67126) = (term691 _67127 x _67128 _67126).
Proof. exact (MK_COMB (@lem5144366 _67126) (@lem5144365 _67127 x _67128 _67126)). Qed.
Lemma lem5144368 (_67127 : real) (x : type1021) (_67128 : real) (_67126 : real -> Prop) : (term686 _67127 x _67128 _67126) = (term691 _67127 x _67128 _67126).
Proof. exact (TRANS (@lem5144354 _67127 x _67128 _67126) (@lem5144367 _67127 x _67128 _67126)). Qed.
Lemma lem5144369 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5144370 (_67127 : real) (x : type1021) (_67128 : real) (_67126 : real -> Prop) : (term692 _67127 x _67128 _67126) = (term693 _67127 x _67128 _67126).
Proof. exact (MK_COMB (@lem5144369) (@lem5144368 _67127 x _67128 _67126)). Qed.
Lemma lem5144371 (_67126 : real -> Prop) (_67128 : real) : (term46 _67126 _67128) = (term46 _67126 _67128).
Proof. exact (eq_refl (term46 _67126 _67128)). Qed.
Lemma lem5144372 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term684 _67127 x _67126 _67128) = (term694 _67127 x _67126 _67128).
Proof. exact (MK_COMB (@lem5144370 _67127 x _67128 _67126) (@lem5144371 _67126 _67128)). Qed.
Lemma lem5144373 (_67127 : real) (x : type1021) (_67126 : real -> Prop) (_67128 : real) : (term677 _67127 x _67128 _67126) = (term694 _67127 x _67126 _67128).
Proof. exact (TRANS (@lem5144351 _67127 x _67126 _67128) (@lem5144372 _67127 x _67126 _67128)). Qed.
Lemma lem5144375 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term695 x b s.
Proof. exact (conj (@lem5143923 x b x' s h1 h2 h3 h4) (@lem5144200 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5144376 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term696 x b s.
Proof. exact (conj (@lem5143769 s h3) (@lem5144375 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5144378 (_67127 : real) (_67126 : real -> Prop) (_67128 : real) (x : type1021) (h1 : term338 x) : term694 _67127 x _67126 _67128.
Proof. exact (EQ_MP (@lem5144373 _67127 x _67126 _67128) (@lem5144348 _67127 _67128 _67126 x h1)). Qed.
Lemma lem5144379 (s : real -> Prop) (b : real) (x : type1021) (h1 : term338 x) : term697 x s b.
Proof. exact (@lem5144378 b s b x h1). Qed.
Lemma lem5144382 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term620 s b) (h3 : term9 s) (h4 : term149 b x' s) : term46 s b.
Proof. exact (@lem5144379 s b x h1 (@lem5144376 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5144383 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b x' s) : term698 s b.
Proof. exact (fun h0 : term620 s b => @lem5144382 x b x' s h1 h0 h2 h3). Qed.
Lemma lem5144385 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5144386 (s : real -> Prop) (b : real) : (term698 s b) = (term46 s b).
Proof. exact (@lem5144385 (term46 s b)). Qed.
Lemma lem5144387 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b x' s) : term46 s b.
Proof. exact (EQ_MP (@lem5144386 s b) (@lem5144383 x b x' s h1 h2 h3)). Qed.
Lemma lem5144403 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5144404 (_67133 : real) (_67132 : real) : (term699 _67132 _67133) = (term700 _67133 _67132).
Proof. exact (@lem5144403 (_67132 = _67133) (term527 _67133 _67132)). Qed.
Lemma lem5144412 (_67132 : real) (_67133 : real) : (term701 _67132 _67133) = (term701 _67132 _67133).
Proof. exact (eq_refl (term701 _67132 _67133)). Qed.
Lemma lem5144413 (_67133 : real) (_67132 : real) : (term526 _67132 _67133) = (term702 _67133 _67132).
Proof. exact (MK_COMB (@lem5144412 _67132 _67133) (@lem5144404 _67133 _67132)). Qed.
Lemma lem5144417 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5144418 (_67133 : real) (_67132 : real) : (term702 _67133 _67132) = (term703 _67133 _67132).
Proof. exact (@lem5144417 (_67132 = _67133) (term527 _67132 _67133) (term527 _67133 _67132)). Qed.
Lemma lem5144436 (_67133 : real) (_67132 : real) : (term526 _67132 _67133) = (term703 _67133 _67132).
Proof. exact (TRANS (@lem5144413 _67133 _67132) (@lem5144418 _67133 _67132)). Qed.
Lemma lem5144437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5144438 (_67133 : real) (_67132 : real) : (term704 _67132 _67133) = (term705 _67133 _67132).
Proof. exact (MK_COMB (@lem5144437) (@lem5144436 _67133 _67132)). Qed.
Lemma lem5144456 (_67133 : real) (_67132 : real) : (term703 _67133 _67132) = (term703 _67133 _67132).
Proof. exact (eq_refl (term703 _67133 _67132)). Qed.
Lemma lem5144457 (_67133 : real) (_67132 : real) : ((term526 _67132 _67133) = (term703 _67133 _67132)) = ((term703 _67133 _67132) = (term703 _67133 _67132)).
Proof. exact (MK_COMB (@lem5144438 _67133 _67132) (@lem5144456 _67133 _67132)). Qed.
Lemma lem5144459 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5144460 (x : Prop) : (x = x) = True.
Proof. exact (@lem5144459 Prop x). Qed.
Lemma lem5144461 (_67133 : real) (_67132 : real) : ((term703 _67133 _67132) = (term703 _67133 _67132)) = True.
Proof. exact (@lem5144460 (term703 _67133 _67132)). Qed.
Lemma lem5144462 (_67133 : real) (_67132 : real) : ((term526 _67132 _67133) = (term703 _67133 _67132)) = True.
Proof. exact (TRANS (@lem5144457 _67133 _67132) (@lem5144461 _67133 _67132)). Qed.
Lemma lem5144463 (_67133 : real) (_67132 : real) : True = ((term526 _67132 _67133) = (term703 _67133 _67132)).
Proof. exact (SYM (@lem5144462 _67133 _67132)). Qed.
Lemma lem5144464 (_67133 : real) (_67132 : real) : (term526 _67132 _67133) = (term703 _67133 _67132).
Proof. exact (EQ_MP (@lem5144463 _67133 _67132) (@lem0)). Qed.
Lemma lem5144465 (_67133 : real) (_67132 : real) (h1 : term21) : term703 _67133 _67132.
Proof. exact (EQ_MP (@lem5144464 _67133 _67132) (@lem5142973 _67132 _67133 h1)). Qed.
Lemma lem5144467 (b : Prop) (a : Prop) : (a \/ b) = (term558 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5144468 (_67132 : real) (_67133 : real) : (term703 _67133 _67132) = (term706 _67132 _67133).
Proof. exact (@lem5144467 (term343 _67133 _67132) (_67132 = _67133)). Qed.
Lemma lem5144470 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5144471 (_67133 : real) (_67132 : real) : (term707 _67133 _67132) = (term708 _67133 _67132).
Proof. exact (@lem5144470 (term527 _67132 _67133) (term527 _67133 _67132)). Qed.
Lemma lem5144473 (a : Prop) : (term567 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5144474 (_67132 : real) (_67133 : real) : (term709 _67132 _67133) = (real_le _67132 _67133).
Proof. exact (@lem5144473 (real_le _67132 _67133)). Qed.
Lemma lem5144475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5144476 (_67132 : real) (_67133 : real) : (term710 _67132 _67133) = (term711 _67132 _67133).
Proof. exact (MK_COMB (@lem5144475) (@lem5144474 _67132 _67133)). Qed.
Lemma lem5144478 (a : Prop) : (term567 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5144479 (_67133 : real) (_67132 : real) : (term709 _67133 _67132) = (real_le _67133 _67132).
Proof. exact (@lem5144478 (real_le _67133 _67132)). Qed.
Lemma lem5144480 (_67133 : real) (_67132 : real) : (term708 _67133 _67132) = (term37 _67133 _67132).
Proof. exact (MK_COMB (@lem5144476 _67132 _67133) (@lem5144479 _67133 _67132)). Qed.
Lemma lem5144481 (_67133 : real) (_67132 : real) : (term707 _67133 _67132) = (term37 _67133 _67132).
Proof. exact (TRANS (@lem5144471 _67133 _67132) (@lem5144480 _67133 _67132)). Qed.
Lemma lem5144482 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5144483 (_67133 : real) (_67132 : real) : (term712 _67133 _67132) = (term713 _67133 _67132).
Proof. exact (MK_COMB (@lem5144482) (@lem5144481 _67133 _67132)). Qed.
Lemma lem5144484 (_67132 : real) (_67133 : real) : (_67132 = _67133) = (_67132 = _67133).
Proof. exact (eq_refl (_67132 = _67133)). Qed.
Lemma lem5144485 (_67132 : real) (_67133 : real) : (term706 _67132 _67133) = (term714 _67132 _67133).
Proof. exact (MK_COMB (@lem5144483 _67133 _67132) (@lem5144484 _67132 _67133)). Qed.
Lemma lem5144486 (_67132 : real) (_67133 : real) : (term703 _67133 _67132) = (term714 _67132 _67133).
Proof. exact (TRANS (@lem5144468 _67132 _67133) (@lem5144485 _67132 _67133)). Qed.
Lemma lem5144488 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b x' s) : term715 s b.
Proof. exact (conj (@lem5143762 x b x' s h1 h2 h3) (@lem5144387 x b x' s h1 h2 h3)). Qed.
Lemma lem5144490 (_67132 : real) (_67133 : real) (h1 : term21) : term714 _67132 _67133.
Proof. exact (EQ_MP (@lem5144486 _67132 _67133) (@lem5144465 _67133 _67132 h1)). Qed.
Lemma lem5144491 (b : real) (s : real -> Prop) (h1 : term21) : term716 b s.
Proof. exact (@lem5144490 b (sup s) h1). Qed.
Lemma lem5144494 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b x' s) : b = (sup s).
Proof. exact (@lem5144491 b s h2 (@lem5144488 x b x' s h1 h3 h4)). Qed.
Lemma lem5144495 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b x' s) : term717 b s.
Proof. exact (fun h0 : term718 b s => @lem5144494 x b x' s h1 h2 h3 h4). Qed.
Lemma lem5144497 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5144498 (b : real) (s : real -> Prop) : (term717 b s) = (b = (sup s)).
Proof. exact (@lem5144497 (b = (sup s))). Qed.
Lemma lem5144499 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b x' s) : b = (sup s).
Proof. exact (EQ_MP (@lem5144498 b s) (@lem5144495 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5144501 (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : @IN real b s.
Proof. exact (proj1 (@lem5142251 b x' s h1)). Qed.
Lemma lem5144502 (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term547 b s.
Proof. exact (fun h0 : term548 b s => @lem5144501 b x' s h1). Qed.
Lemma lem5144504 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5144505 (b : real) (s : real -> Prop) : (term547 b s) = (@IN real b s).
Proof. exact (@lem5144504 (@IN real b s)). Qed.
Lemma lem5144506 (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : @IN real b s.
Proof. exact (EQ_MP (@lem5144505 b s) (@lem5144502 b x' s h1)). Qed.
Lemma lem5144524 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5144525 (_67149 : real -> Prop) (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : (term539 _67148 _67149 _67146 _67147) = (term719 _67149 _67148 _67146 _67147).
Proof. exact (@lem5144524 (@IN real _67148 _67149) (term720 _67146 _67148) (term548 _67146 _67147)). Qed.
Lemma lem5144543 (_67147 : real -> Prop) (_67149 : real -> Prop) : (term721 _67147 _67149) = (term721 _67147 _67149).
Proof. exact (eq_refl (term721 _67147 _67149)). Qed.
Lemma lem5144544 (_67149 : real -> Prop) (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : (term541 _67148 _67149 _67146 _67147) = (term722 _67149 _67148 _67146 _67147).
Proof. exact (MK_COMB (@lem5144543 _67147 _67149) (@lem5144525 _67149 _67148 _67146 _67147)). Qed.
Lemma lem5144548 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5144549 (_67149 : real -> Prop) (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : (term722 _67149 _67148 _67146 _67147) = (term723 _67149 _67148 _67146 _67147).
Proof. exact (@lem5144548 (@IN real _67148 _67149) (term724 _67147 _67149) (term725 _67148 _67146 _67147)). Qed.
Lemma lem5144579 (_67149 : real -> Prop) (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : (term541 _67148 _67149 _67146 _67147) = (term723 _67149 _67148 _67146 _67147).
Proof. exact (TRANS (@lem5144544 _67149 _67148 _67146 _67147) (@lem5144549 _67149 _67148 _67146 _67147)). Qed.
Lemma lem5144580 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5144581 (_67149 : real -> Prop) (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : (term726 _67148 _67149 _67146 _67147) = (term727 _67149 _67148 _67146 _67147).
Proof. exact (MK_COMB (@lem5144580) (@lem5144579 _67149 _67148 _67146 _67147)). Qed.
Lemma lem5144611 (_67149 : real -> Prop) (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : (term723 _67149 _67148 _67146 _67147) = (term723 _67149 _67148 _67146 _67147).
Proof. exact (eq_refl (term723 _67149 _67148 _67146 _67147)). Qed.
Lemma lem5144612 (_67149 : real -> Prop) (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : ((term541 _67148 _67149 _67146 _67147) = (term723 _67149 _67148 _67146 _67147)) = ((term723 _67149 _67148 _67146 _67147) = (term723 _67149 _67148 _67146 _67147)).
Proof. exact (MK_COMB (@lem5144581 _67149 _67148 _67146 _67147) (@lem5144611 _67149 _67148 _67146 _67147)). Qed.
Lemma lem5144614 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5144615 (x : Prop) : (x = x) = True.
Proof. exact (@lem5144614 Prop x). Qed.
Lemma lem5144616 (_67149 : real -> Prop) (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : ((term723 _67149 _67148 _67146 _67147) = (term723 _67149 _67148 _67146 _67147)) = True.
Proof. exact (@lem5144615 (term723 _67149 _67148 _67146 _67147)). Qed.
Lemma lem5144617 (_67149 : real -> Prop) (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : ((term541 _67148 _67149 _67146 _67147) = (term723 _67149 _67148 _67146 _67147)) = True.
Proof. exact (TRANS (@lem5144612 _67149 _67148 _67146 _67147) (@lem5144616 _67149 _67148 _67146 _67147)). Qed.
Lemma lem5144618 (_67149 : real -> Prop) (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : True = ((term541 _67148 _67149 _67146 _67147) = (term723 _67149 _67148 _67146 _67147)).
Proof. exact (SYM (@lem5144617 _67149 _67148 _67146 _67147)). Qed.
Lemma lem5144619 (_67149 : real -> Prop) (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : (term541 _67148 _67149 _67146 _67147) = (term723 _67149 _67148 _67146 _67147).
Proof. exact (EQ_MP (@lem5144618 _67149 _67148 _67146 _67147) (@lem0)). Qed.
Lemma lem5144620 (_67149 : real -> Prop) (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : term723 _67149 _67148 _67146 _67147.
Proof. exact (EQ_MP (@lem5144619 _67149 _67148 _67146 _67147) (@lem5143260 _67148 _67149 _67146 _67147)). Qed.
Lemma lem5144622 (b : Prop) (a : Prop) : (a \/ b) = (term558 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5144623 (_67146 : real) (_67147 : real -> Prop) (_67148 : real) (_67149 : real -> Prop) : (term723 _67149 _67148 _67146 _67147) = (term728 _67146 _67147 _67148 _67149).
Proof. exact (@lem5144622 (term729 _67149 _67148 _67146 _67147) (@IN real _67148 _67149)). Qed.
Lemma lem5144625 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5144626 (_67149 : real -> Prop) (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : (term730 _67149 _67148 _67146 _67147) = (term731 _67149 _67148 _67146 _67147).
Proof. exact (@lem5144625 (term724 _67147 _67149) (term725 _67148 _67146 _67147)). Qed.
Lemma lem5144628 (a : Prop) : (term567 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5144629 (_67147 : real -> Prop) (_67149 : real -> Prop) : (term732 _67147 _67149) = (_67147 = _67149).
Proof. exact (@lem5144628 (_67147 = _67149)). Qed.
Lemma lem5144630 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5144631 (_67147 : real -> Prop) (_67149 : real -> Prop) : (term733 _67147 _67149) = (term734 _67147 _67149).
Proof. exact (MK_COMB (@lem5144630) (@lem5144629 _67147 _67149)). Qed.
Lemma lem5144633 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5144634 (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : (term735 _67148 _67146 _67147) = (term736 _67148 _67146 _67147).
Proof. exact (@lem5144633 (term720 _67146 _67148) (term548 _67146 _67147)). Qed.
Lemma lem5144636 (a : Prop) : (term567 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5144637 (_67146 : real) (_67148 : real) : (term737 _67146 _67148) = (_67146 = _67148).
Proof. exact (@lem5144636 (_67146 = _67148)). Qed.
Lemma lem5144638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5144639 (_67146 : real) (_67148 : real) : (term738 _67146 _67148) = (term739 _67146 _67148).
Proof. exact (MK_COMB (@lem5144638) (@lem5144637 _67146 _67148)). Qed.
Lemma lem5144641 (a : Prop) : (term567 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5144642 (_67146 : real) (_67147 : real -> Prop) : (term568 _67146 _67147) = (@IN real _67146 _67147).
Proof. exact (@lem5144641 (@IN real _67146 _67147)). Qed.
Lemma lem5144643 (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : (term736 _67148 _67146 _67147) = (term740 _67148 _67146 _67147).
Proof. exact (MK_COMB (@lem5144639 _67146 _67148) (@lem5144642 _67146 _67147)). Qed.
Lemma lem5144644 (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : (term735 _67148 _67146 _67147) = (term740 _67148 _67146 _67147).
Proof. exact (TRANS (@lem5144634 _67148 _67146 _67147) (@lem5144643 _67148 _67146 _67147)). Qed.
Lemma lem5144645 (_67149 : real -> Prop) (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : (term731 _67149 _67148 _67146 _67147) = (term741 _67149 _67148 _67146 _67147).
Proof. exact (MK_COMB (@lem5144631 _67147 _67149) (@lem5144644 _67148 _67146 _67147)). Qed.
Lemma lem5144646 (_67149 : real -> Prop) (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : (term730 _67149 _67148 _67146 _67147) = (term741 _67149 _67148 _67146 _67147).
Proof. exact (TRANS (@lem5144626 _67149 _67148 _67146 _67147) (@lem5144645 _67149 _67148 _67146 _67147)). Qed.
Lemma lem5144647 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5144648 (_67149 : real -> Prop) (_67148 : real) (_67146 : real) (_67147 : real -> Prop) : (term742 _67149 _67148 _67146 _67147) = (term743 _67149 _67148 _67146 _67147).
Proof. exact (MK_COMB (@lem5144647) (@lem5144646 _67149 _67148 _67146 _67147)). Qed.
Lemma lem5144649 (_67148 : real) (_67149 : real -> Prop) : (@IN real _67148 _67149) = (@IN real _67148 _67149).
Proof. exact (eq_refl (@IN real _67148 _67149)). Qed.
Lemma lem5144650 (_67146 : real) (_67147 : real -> Prop) (_67148 : real) (_67149 : real -> Prop) : (term728 _67146 _67147 _67148 _67149) = (term744 _67146 _67147 _67148 _67149).
Proof. exact (MK_COMB (@lem5144648 _67149 _67148 _67146 _67147) (@lem5144649 _67148 _67149)). Qed.
Lemma lem5144651 (_67146 : real) (_67147 : real -> Prop) (_67148 : real) (_67149 : real -> Prop) : (term723 _67149 _67148 _67146 _67147) = (term744 _67146 _67147 _67148 _67149).
Proof. exact (TRANS (@lem5144623 _67146 _67147 _67148 _67149) (@lem5144650 _67146 _67147 _67148 _67149)). Qed.
Lemma lem5144653 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b x' s) : term745 b s.
Proof. exact (conj (@lem5144499 x b x' s h1 h2 h3 h4) (@lem5144506 b x' s h4)). Qed.
Lemma lem5144654 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b x' s) : term746 b s.
Proof. exact (conj (@lem5143314 s) (@lem5144653 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5144656 (_67146 : real) (_67147 : real -> Prop) (_67148 : real) (_67149 : real -> Prop) : term744 _67146 _67147 _67148 _67149.
Proof. exact (EQ_MP (@lem5144651 _67146 _67147 _67148 _67149) (@lem5144620 _67149 _67148 _67146 _67147)). Qed.
Lemma lem5144657 (b : real) (s : real -> Prop) : term747 b s.
Proof. exact (@lem5144656 b s (sup s) s). Qed.
Lemma lem5144660 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b x' s) : term95 s.
Proof. exact (@lem5144657 b s (@lem5144654 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5144661 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b x' s) : term748 s.
Proof. exact (fun h0 : term106 s => @lem5144660 x b x' s h1 h2 h3 h4). Qed.
Lemma lem5144663 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5144664 (s : real -> Prop) : (term748 s) = (term95 s).
Proof. exact (@lem5144663 (term95 s)). Qed.
Lemma lem5144665 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b x' s) : term95 s.
Proof. exact (EQ_MP (@lem5144664 s) (@lem5144661 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5144668 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5144670 (s : real -> Prop) : (term106 s) = (term749 s).
Proof. exact (@lem5144668 (term95 s)). Qed.
Lemma lem5144673 (s : real -> Prop) (h1 : term106 s) : term749 s.
Proof. exact (EQ_MP (@lem5144670 s) (@lem5142979 s h1)). Qed.
Lemma lem5144676 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b x' s) : False.
Proof. exact (@lem5144673 s h3 (@lem5144665 x b x' s h1 h2 h4 h5)). Qed.
Lemma lem5144677 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b x' s) : term750.
Proof. exact (fun h0 : ~ False => @lem5144676 x b x' s h1 h2 h3 h4 h5). Qed.
Lemma lem5144679 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5144680 : term750 = False.
Proof. exact (@lem5144679 False). Qed.
Lemma lem5144681 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b x' s) : False.
Proof. exact (EQ_MP (@lem5144680) (@lem5144677 x b x' s h1 h2 h3 h4 h5)). Qed.
Lemma lem5144760 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (proj2 (@lem5142006 s h1)). Qed.
Lemma lem5144761 (s : real -> Prop) (h1 : term9 s) : term545 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5144760 s h1). Qed.
Lemma lem5144763 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5144764 (s : real -> Prop) : (term545 s) = (term179 s).
Proof. exact (@lem5144763 (s = (@EMPTY real))). Qed.
Lemma lem5144765 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (EQ_MP (@lem5144764 s) (@lem5144761 s h1)). Qed.
Lemma lem5144767 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (proj2 (@lem5142006 s h1)). Qed.
Lemma lem5144768 (s : real -> Prop) (h1 : term9 s) : term545 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5144767 s h1). Qed.
Lemma lem5144770 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5144771 (s : real -> Prop) : (term545 s) = (term179 s).
Proof. exact (@lem5144770 (s = (@EMPTY real))). Qed.
Lemma lem5144772 (s : real -> Prop) (h1 : term9 s) : term179 s.
Proof. exact (EQ_MP (@lem5144771 s) (@lem5144768 s h1)). Qed.
Lemma lem5144774 (x' : real) (s : real -> Prop) (h1 : term80 x' s) : @IN real x' s.
Proof. exact (proj1 (@lem5142259 x' s h1)). Qed.
Lemma lem5144775 (x' : real) (s : real -> Prop) (h1 : term80 x' s) : term547 x' s.
Proof. exact (fun h0 : term548 x' s => @lem5144774 x' s h1). Qed.
Lemma lem5144777 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5144778 (x' : real) (s : real -> Prop) : (term547 x' s) = (@IN real x' s).
Proof. exact (@lem5144777 (@IN real x' s)). Qed.
Lemma lem5144779 (x' : real) (s : real -> Prop) (h1 : term80 x' s) : @IN real x' s.
Proof. exact (EQ_MP (@lem5144778 x' s) (@lem5144775 x' s h1)). Qed.
Lemma lem5144782 (x' : real) (s : real -> Prop) (h1 : term533 x' s) : term533 x' s.
Proof. exact (h1). Qed.
Lemma lem5144783 (x' : real) (s : real -> Prop) (h1 : term533 x' s) : term549 x' s.
Proof. exact (fun h0 : term81 x' s => @lem5144782 x' s h1). Qed.
Lemma lem5144785 (p : Prop) : (term546 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5144786 (x' : real) (s : real -> Prop) : (term549 x' s) = (term533 x' s).
Proof. exact (@lem5144785 (term81 x' s)). Qed.
Lemma lem5144787 (x' : real) (s : real -> Prop) (h1 : term533 x' s) : term533 x' s.
Proof. exact (EQ_MP (@lem5144786 x' s) (@lem5144783 x' s h1)). Qed.
Lemma lem5144815 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5144816 (_67138 : real) (_67136 : real -> Prop) : (term180 _67138 _67136) = (term550 _67138 _67136).
Proof. exact (@lem5144815 (term81 _67138 _67136) (term548 _67138 _67136)). Qed.
Lemma lem5144822 (x : type1021) (_67137 : real) (_67136 : real -> Prop) : (term551 x _67137 _67136) = (term551 x _67137 _67136).
Proof. exact (eq_refl (term551 x _67137 _67136)). Qed.
Lemma lem5144823 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term552 x _67137 _67138 _67136) = (term553 x _67137 _67138 _67136).
Proof. exact (MK_COMB (@lem5144822 x _67137 _67136) (@lem5144816 _67138 _67136)). Qed.
Lemma lem5144834 (_67136 : real -> Prop) : (term175 _67136) = (term175 _67136).
Proof. exact (eq_refl (term175 _67136)). Qed.
Lemma lem5144835 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term531 x _67137 _67138 _67136) = (term554 x _67137 _67138 _67136).
Proof. exact (MK_COMB (@lem5144834 _67136) (@lem5144823 x _67137 _67138 _67136)). Qed.
Lemma lem5144846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5144847 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term555 x _67137 _67138 _67136) = (term556 x _67137 _67138 _67136).
Proof. exact (MK_COMB (@lem5144846) (@lem5144835 x _67137 _67138 _67136)). Qed.
Lemma lem5144851 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5144852 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term557 x _67137 _67138 _67136) = (term531 x _67137 _67138 _67136).
Proof. exact (@lem5144851 (_67136 = (@EMPTY real)) (term486 x _67137 _67136) (term180 _67138 _67136)). Qed.
Lemma lem5144878 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5144879 (_67138 : real) (_67136 : real -> Prop) : (term180 _67138 _67136) = (term550 _67138 _67136).
Proof. exact (@lem5144878 (term81 _67138 _67136) (term548 _67138 _67136)). Qed.
Lemma lem5144885 (x : type1021) (_67137 : real) (_67136 : real -> Prop) : (term551 x _67137 _67136) = (term551 x _67137 _67136).
Proof. exact (eq_refl (term551 x _67137 _67136)). Qed.
Lemma lem5144886 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term552 x _67137 _67138 _67136) = (term553 x _67137 _67138 _67136).
Proof. exact (MK_COMB (@lem5144885 x _67137 _67136) (@lem5144879 _67138 _67136)). Qed.
Lemma lem5144897 (_67136 : real -> Prop) : (term175 _67136) = (term175 _67136).
Proof. exact (eq_refl (term175 _67136)). Qed.
Lemma lem5144898 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term531 x _67137 _67138 _67136) = (term554 x _67137 _67138 _67136).
Proof. exact (MK_COMB (@lem5144897 _67136) (@lem5144886 x _67137 _67138 _67136)). Qed.
Lemma lem5144909 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term557 x _67137 _67138 _67136) = (term554 x _67137 _67138 _67136).
Proof. exact (TRANS (@lem5144852 x _67137 _67138 _67136) (@lem5144898 x _67137 _67138 _67136)). Qed.
Lemma lem5144910 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : ((term531 x _67137 _67138 _67136) = (term557 x _67137 _67138 _67136)) = ((term554 x _67137 _67138 _67136) = (term554 x _67137 _67138 _67136)).
Proof. exact (MK_COMB (@lem5144847 x _67137 _67138 _67136) (@lem5144909 x _67137 _67138 _67136)). Qed.
Lemma lem5144912 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5144913 (x : Prop) : (x = x) = True.
Proof. exact (@lem5144912 Prop x). Qed.
Lemma lem5144914 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : ((term554 x _67137 _67138 _67136) = (term554 x _67137 _67138 _67136)) = True.
Proof. exact (@lem5144913 (term554 x _67137 _67138 _67136)). Qed.
Lemma lem5144915 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : ((term531 x _67137 _67138 _67136) = (term557 x _67137 _67138 _67136)) = True.
Proof. exact (TRANS (@lem5144910 x _67137 _67138 _67136) (@lem5144914 x _67137 _67138 _67136)). Qed.
Lemma lem5144916 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : True = ((term531 x _67137 _67138 _67136) = (term557 x _67137 _67138 _67136)).
Proof. exact (SYM (@lem5144915 x _67137 _67138 _67136)). Qed.
Lemma lem5144917 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term531 x _67137 _67138 _67136) = (term557 x _67137 _67138 _67136).
Proof. exact (EQ_MP (@lem5144916 x _67137 _67138 _67136) (@lem0)). Qed.
Lemma lem5144918 (_67137 : real) (_67138 : real) (_67136 : real -> Prop) (x : type1021) (h1 : term338 x) : term557 x _67137 _67138 _67136.
Proof. exact (EQ_MP (@lem5144917 x _67137 _67138 _67136) (@lem5143213 _67137 _67138 _67136 x h1)). Qed.
Lemma lem5144920 (b : Prop) (a : Prop) : (a \/ b) = (term558 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5144921 (_67138 : real) (x : type1021) (_67137 : real) (_67136 : real -> Prop) : (term557 x _67137 _67138 _67136) = (term559 _67138 x _67137 _67136).
Proof. exact (@lem5144920 (term560 _67138 _67136) (term486 x _67137 _67136)). Qed.
Lemma lem5144923 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5144924 (_67138 : real) (_67136 : real -> Prop) : (term563 _67138 _67136) = (term564 _67138 _67136).
Proof. exact (@lem5144923 (_67136 = (@EMPTY real)) (term180 _67138 _67136)). Qed.
Lemma lem5144926 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5144927 (_67138 : real) (_67136 : real -> Prop) : (term565 _67138 _67136) = (term566 _67138 _67136).
Proof. exact (@lem5144926 (term548 _67138 _67136) (term81 _67138 _67136)). Qed.
Lemma lem5144929 (a : Prop) : (term567 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5144930 (_67138 : real) (_67136 : real -> Prop) : (term568 _67138 _67136) = (@IN real _67138 _67136).
Proof. exact (@lem5144929 (@IN real _67138 _67136)). Qed.
Lemma lem5144931 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5144932 (_67138 : real) (_67136 : real -> Prop) : (term569 _67138 _67136) = (term69 _67138 _67136).
Proof. exact (MK_COMB (@lem5144931) (@lem5144930 _67138 _67136)). Qed.
Lemma lem5144933 (_67138 : real) (_67136 : real -> Prop) : (term533 _67138 _67136) = (term533 _67138 _67136).
Proof. exact (eq_refl (term533 _67138 _67136)). Qed.
Lemma lem5144934 (_67138 : real) (_67136 : real -> Prop) : (term566 _67138 _67136) = (term80 _67138 _67136).
Proof. exact (MK_COMB (@lem5144932 _67138 _67136) (@lem5144933 _67138 _67136)). Qed.
Lemma lem5144935 (_67138 : real) (_67136 : real -> Prop) : (term565 _67138 _67136) = (term80 _67138 _67136).
Proof. exact (TRANS (@lem5144927 _67138 _67136) (@lem5144934 _67138 _67136)). Qed.
Lemma lem5144936 (_67136 : real -> Prop) : (term61 _67136) = (term61 _67136).
Proof. exact (eq_refl (term61 _67136)). Qed.
Lemma lem5144937 (_67138 : real) (_67136 : real -> Prop) : (term564 _67138 _67136) = (term570 _67138 _67136).
Proof. exact (MK_COMB (@lem5144936 _67136) (@lem5144935 _67138 _67136)). Qed.
Lemma lem5144938 (_67138 : real) (_67136 : real -> Prop) : (term563 _67138 _67136) = (term570 _67138 _67136).
Proof. exact (TRANS (@lem5144924 _67138 _67136) (@lem5144937 _67138 _67136)). Qed.
Lemma lem5144939 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5144940 (_67138 : real) (_67136 : real -> Prop) : (term571 _67138 _67136) = (term572 _67138 _67136).
Proof. exact (MK_COMB (@lem5144939) (@lem5144938 _67138 _67136)). Qed.
Lemma lem5144941 (x : type1021) (_67137 : real) (_67136 : real -> Prop) : (term486 x _67137 _67136) = (term486 x _67137 _67136).
Proof. exact (eq_refl (term486 x _67137 _67136)). Qed.
Lemma lem5144942 (_67138 : real) (x : type1021) (_67137 : real) (_67136 : real -> Prop) : (term559 _67138 x _67137 _67136) = (term573 _67138 x _67137 _67136).
Proof. exact (MK_COMB (@lem5144940 _67138 _67136) (@lem5144941 x _67137 _67136)). Qed.
Lemma lem5144943 (_67138 : real) (x : type1021) (_67137 : real) (_67136 : real -> Prop) : (term557 x _67137 _67138 _67136) = (term573 _67138 x _67137 _67136).
Proof. exact (TRANS (@lem5144921 _67138 x _67137 _67136) (@lem5144942 _67138 x _67137 _67136)). Qed.
Lemma lem5144945 (x' : real) (s : real -> Prop) (h1 : term533 x' s) (h2 : term80 x' s) : term80 x' s.
Proof. exact (conj (@lem5144779 x' s h2) (@lem5144787 x' s h1)). Qed.
Lemma lem5144946 (x' : real) (s : real -> Prop) (h1 : term533 x' s) (h2 : term9 s) (h3 : term80 x' s) : term570 x' s.
Proof. exact (conj (@lem5144772 s h2) (@lem5144945 x' s h1 h3)). Qed.
Lemma lem5144948 (_67138 : real) (_67137 : real) (_67136 : real -> Prop) (x : type1021) (h1 : term338 x) : term573 _67138 x _67137 _67136.
Proof. exact (EQ_MP (@lem5144943 _67138 x _67137 _67136) (@lem5144918 _67137 _67138 _67136 x h1)). Qed.
Lemma lem5144949 (x' : real) (_67137 : real) (s : real -> Prop) (x : type1021) (h1 : term338 x) : term573 x' x _67137 s.
Proof. exact (@lem5144948 x' _67137 s x h1). Qed.
Lemma lem5144952 (_67137 : real) (x : type1021) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 x' s) (h3 : term9 s) (h4 : term80 x' s) : term486 x _67137 s.
Proof. exact (@lem5144949 x' _67137 s x h1 (@lem5144946 x' s h2 h3 h4)). Qed.
Lemma lem5144953 (b : real) (x : type1021) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 x' s) (h3 : term9 s) (h4 : term80 x' s) : term486 x b s.
Proof. exact (@lem5144952 b x x' s h1 h2 h3 h4). Qed.
Lemma lem5144954 (b : real) (x : type1021) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 x' s) (h3 : term9 s) (h4 : term80 x' s) : term574 x b s.
Proof. exact (fun h0 : term575 x b s => @lem5144953 b x x' s h1 h2 h3 h4). Qed.
Lemma lem5144956 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5144957 (x : type1021) (b : real) (s : real -> Prop) : (term574 x b s) = (term486 x b s).
Proof. exact (@lem5144956 (term486 x b s)). Qed.
Lemma lem5144958 (b : real) (x : type1021) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 x' s) (h3 : term9 s) (h4 : term80 x' s) : term486 x b s.
Proof. exact (EQ_MP (@lem5144957 x b s) (@lem5144954 b x x' s h1 h2 h3 h4)). Qed.
Lemma lem5144964 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5144965 (b : real) (_67139 : real) (s : real -> Prop) : (term73 s _67139 b) = (term576 b _67139 s).
Proof. exact (@lem5144964 (real_le _67139 b) (term548 _67139 s)). Qed.
Lemma lem5144971 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5144972 (b : real) (_67139 : real) (s : real -> Prop) : (term577 s _67139 b) = (term578 b _67139 s).
Proof. exact (MK_COMB (@lem5144971) (@lem5144965 b _67139 s)). Qed.
Lemma lem5144978 (b : real) (_67139 : real) (s : real -> Prop) : (term576 b _67139 s) = (term576 b _67139 s).
Proof. exact (eq_refl (term576 b _67139 s)). Qed.
Lemma lem5144979 (b : real) (_67139 : real) (s : real -> Prop) : ((term73 s _67139 b) = (term576 b _67139 s)) = ((term576 b _67139 s) = (term576 b _67139 s)).
Proof. exact (MK_COMB (@lem5144972 b _67139 s) (@lem5144978 b _67139 s)). Qed.
Lemma lem5144981 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5144982 (x : Prop) : (x = x) = True.
Proof. exact (@lem5144981 Prop x). Qed.
Lemma lem5144983 (b : real) (_67139 : real) (s : real -> Prop) : ((term576 b _67139 s) = (term576 b _67139 s)) = True.
Proof. exact (@lem5144982 (term576 b _67139 s)). Qed.
Lemma lem5144984 (b : real) (_67139 : real) (s : real -> Prop) : ((term73 s _67139 b) = (term576 b _67139 s)) = True.
Proof. exact (TRANS (@lem5144979 b _67139 s) (@lem5144983 b _67139 s)). Qed.
Lemma lem5144985 (b : real) (_67139 : real) (s : real -> Prop) : True = ((term73 s _67139 b) = (term576 b _67139 s)).
Proof. exact (SYM (@lem5144984 b _67139 s)). Qed.
Lemma lem5144986 (b : real) (_67139 : real) (s : real -> Prop) : (term73 s _67139 b) = (term576 b _67139 s).
Proof. exact (EQ_MP (@lem5144985 b _67139 s) (@lem0)). Qed.
Lemma lem5144987 (_67139 : real) (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term576 b _67139 s.
Proof. exact (EQ_MP (@lem5144986 b _67139 s) (@lem5143101 _67139 b x' s h1)). Qed.
Lemma lem5144989 (b : Prop) (a : Prop) : (a \/ b) = (term558 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5144990 (s : real -> Prop) (_67139 : real) (b : real) : (term576 b _67139 s) = (term579 s _67139 b).
Proof. exact (@lem5144989 (term548 _67139 s) (real_le _67139 b)). Qed.
Lemma lem5144992 (a : Prop) : (term567 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5144993 (_67139 : real) (s : real -> Prop) : (term568 _67139 s) = (@IN real _67139 s).
Proof. exact (@lem5144992 (@IN real _67139 s)). Qed.
Lemma lem5144994 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5144995 (_67139 : real) (s : real -> Prop) : (term580 _67139 s) = (term581 _67139 s).
Proof. exact (MK_COMB (@lem5144994) (@lem5144993 _67139 s)). Qed.
Lemma lem5144996 (_67139 : real) (b : real) : (real_le _67139 b) = (real_le _67139 b).
Proof. exact (eq_refl (real_le _67139 b)). Qed.
Lemma lem5144997 (s : real -> Prop) (_67139 : real) (b : real) : (term579 s _67139 b) = (term47 s _67139 b).
Proof. exact (MK_COMB (@lem5144995 _67139 s) (@lem5144996 _67139 b)). Qed.
Lemma lem5144998 (s : real -> Prop) (_67139 : real) (b : real) : (term576 b _67139 s) = (term47 s _67139 b).
Proof. exact (TRANS (@lem5144990 s _67139 b) (@lem5144997 s _67139 b)). Qed.
Lemma lem5145001 (_67139 : real) (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term47 s _67139 b.
Proof. exact (EQ_MP (@lem5144998 s _67139 b) (@lem5144987 _67139 b x' s h1)). Qed.
Lemma lem5145002 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term149 b x' s) : term582 x s b.
Proof. exact (@lem5145001 (x s b) b x' s h1). Qed.
Lemma lem5145005 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 x' s) (h3 : term9 s) (h4 : term149 b x' s) (h5 : term80 x' s) : term583 x s b.
Proof. exact (@lem5145002 x b x' s h4 (@lem5144958 b x x' s h1 h2 h3 h5)). Qed.
Lemma lem5145006 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 x' s) (h3 : term9 s) (h4 : term149 b x' s) (h5 : term80 x' s) : term584 x s b.
Proof. exact (fun h0 : term487 x s b => @lem5145005 x b x' s h1 h2 h3 h4 h5). Qed.
Lemma lem5145008 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5145009 (x : type1021) (s : real -> Prop) (b : real) : (term584 x s b) = (term583 x s b).
Proof. exact (@lem5145008 (term583 x s b)). Qed.
Lemma lem5145010 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 x' s) (h3 : term9 s) (h4 : term149 b x' s) (h5 : term80 x' s) : term583 x s b.
Proof. exact (EQ_MP (@lem5145009 x s b) (@lem5145006 x b x' s h1 h2 h3 h4 h5)). Qed.
Lemma lem5145012 (x' : real) (s : real -> Prop) (h1 : term80 x' s) : @IN real x' s.
Proof. exact (proj1 (@lem5142259 x' s h1)). Qed.
Lemma lem5145013 (x' : real) (s : real -> Prop) (h1 : term80 x' s) : term547 x' s.
Proof. exact (fun h0 : term548 x' s => @lem5145012 x' s h1). Qed.
Lemma lem5145015 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5145016 (x' : real) (s : real -> Prop) : (term547 x' s) = (@IN real x' s).
Proof. exact (@lem5145015 (@IN real x' s)). Qed.
Lemma lem5145017 (x' : real) (s : real -> Prop) (h1 : term80 x' s) : @IN real x' s.
Proof. exact (EQ_MP (@lem5145016 x' s) (@lem5145013 x' s h1)). Qed.
Lemma lem5145035 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5145036 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term585 x _67137 _67138 _67136) = (term586 x _67137 _67138 _67136).
Proof. exact (@lem5145035 (term548 _67138 _67136) (term487 x _67136 _67137) (term81 _67138 _67136)). Qed.
Lemma lem5145050 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5145051 (_67138 : real) (x : type1021) (_67136 : real -> Prop) (_67137 : real) : (term587 x _67137 _67138 _67136) = (term588 _67138 x _67136 _67137).
Proof. exact (@lem5145050 (term81 _67138 _67136) (term487 x _67136 _67137)). Qed.
Lemma lem5145057 (_67138 : real) (_67136 : real -> Prop) : (term589 _67138 _67136) = (term589 _67138 _67136).
Proof. exact (eq_refl (term589 _67138 _67136)). Qed.
Lemma lem5145058 (_67138 : real) (x : type1021) (_67136 : real -> Prop) (_67137 : real) : (term586 x _67137 _67138 _67136) = (term590 _67138 x _67136 _67137).
Proof. exact (MK_COMB (@lem5145057 _67138 _67136) (@lem5145051 _67138 x _67136 _67137)). Qed.
Lemma lem5145062 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5145063 (_67138 : real) (x : type1021) (_67136 : real -> Prop) (_67137 : real) : (term590 _67138 x _67136 _67137) = (term591 _67138 x _67136 _67137).
Proof. exact (@lem5145062 (term81 _67138 _67136) (term548 _67138 _67136) (term487 x _67136 _67137)). Qed.
Lemma lem5145079 (_67138 : real) (x : type1021) (_67136 : real -> Prop) (_67137 : real) : (term586 x _67137 _67138 _67136) = (term591 _67138 x _67136 _67137).
Proof. exact (TRANS (@lem5145058 _67138 x _67136 _67137) (@lem5145063 _67138 x _67136 _67137)). Qed.
Lemma lem5145080 (_67138 : real) (x : type1021) (_67136 : real -> Prop) (_67137 : real) : (term585 x _67137 _67138 _67136) = (term591 _67138 x _67136 _67137).
Proof. exact (TRANS (@lem5145036 x _67137 _67138 _67136) (@lem5145079 _67138 x _67136 _67137)). Qed.
Lemma lem5145081 (_67136 : real -> Prop) : (term175 _67136) = (term175 _67136).
Proof. exact (eq_refl (term175 _67136)). Qed.
Lemma lem5145082 (_67138 : real) (x : type1021) (_67136 : real -> Prop) (_67137 : real) : (term532 x _67137 _67138 _67136) = (term592 _67138 x _67136 _67137).
Proof. exact (MK_COMB (@lem5145081 _67136) (@lem5145080 _67138 x _67136 _67137)). Qed.
Lemma lem5145093 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5145094 (_67138 : real) (x : type1021) (_67136 : real -> Prop) (_67137 : real) : (term593 x _67137 _67138 _67136) = (term594 _67138 x _67136 _67137).
Proof. exact (MK_COMB (@lem5145093) (@lem5145082 _67138 x _67136 _67137)). Qed.
Lemma lem5145098 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5145099 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term595 x _67137 _67138 _67136) = (term596 x _67137 _67138 _67136).
Proof. exact (@lem5145098 (_67136 = (@EMPTY real)) (term81 _67138 _67136) (term597 x _67137 _67138 _67136)). Qed.
Lemma lem5145125 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5145126 (_67138 : real) (x : type1021) (_67136 : real -> Prop) (_67137 : real) : (term597 x _67137 _67138 _67136) = (term598 _67138 x _67136 _67137).
Proof. exact (@lem5145125 (term548 _67138 _67136) (term487 x _67136 _67137)). Qed.
Lemma lem5145132 (_67138 : real) (_67136 : real -> Prop) : (term599 _67138 _67136) = (term599 _67138 _67136).
Proof. exact (eq_refl (term599 _67138 _67136)). Qed.
Lemma lem5145133 (_67138 : real) (x : type1021) (_67136 : real -> Prop) (_67137 : real) : (term600 x _67137 _67138 _67136) = (term591 _67138 x _67136 _67137).
Proof. exact (MK_COMB (@lem5145132 _67138 _67136) (@lem5145126 _67138 x _67136 _67137)). Qed.
Lemma lem5145144 (_67136 : real -> Prop) : (term175 _67136) = (term175 _67136).
Proof. exact (eq_refl (term175 _67136)). Qed.
Lemma lem5145145 (_67138 : real) (x : type1021) (_67136 : real -> Prop) (_67137 : real) : (term596 x _67137 _67138 _67136) = (term592 _67138 x _67136 _67137).
Proof. exact (MK_COMB (@lem5145144 _67136) (@lem5145133 _67138 x _67136 _67137)). Qed.
Lemma lem5145156 (_67138 : real) (x : type1021) (_67136 : real -> Prop) (_67137 : real) : (term595 x _67137 _67138 _67136) = (term592 _67138 x _67136 _67137).
Proof. exact (TRANS (@lem5145099 x _67137 _67138 _67136) (@lem5145145 _67138 x _67136 _67137)). Qed.
Lemma lem5145157 (_67138 : real) (x : type1021) (_67136 : real -> Prop) (_67137 : real) : ((term532 x _67137 _67138 _67136) = (term595 x _67137 _67138 _67136)) = ((term592 _67138 x _67136 _67137) = (term592 _67138 x _67136 _67137)).
Proof. exact (MK_COMB (@lem5145094 _67138 x _67136 _67137) (@lem5145156 _67138 x _67136 _67137)). Qed.
Lemma lem5145159 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5145160 (x : Prop) : (x = x) = True.
Proof. exact (@lem5145159 Prop x). Qed.
Lemma lem5145161 (_67138 : real) (x : type1021) (_67136 : real -> Prop) (_67137 : real) : ((term592 _67138 x _67136 _67137) = (term592 _67138 x _67136 _67137)) = True.
Proof. exact (@lem5145160 (term592 _67138 x _67136 _67137)). Qed.
Lemma lem5145162 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : ((term532 x _67137 _67138 _67136) = (term595 x _67137 _67138 _67136)) = True.
Proof. exact (TRANS (@lem5145157 _67138 x _67136 _67137) (@lem5145161 _67138 x _67136 _67137)). Qed.
Lemma lem5145163 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : True = ((term532 x _67137 _67138 _67136) = (term595 x _67137 _67138 _67136)).
Proof. exact (SYM (@lem5145162 x _67137 _67138 _67136)). Qed.
Lemma lem5145164 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term532 x _67137 _67138 _67136) = (term595 x _67137 _67138 _67136).
Proof. exact (EQ_MP (@lem5145163 x _67137 _67138 _67136) (@lem0)). Qed.
Lemma lem5145165 (_67137 : real) (_67138 : real) (_67136 : real -> Prop) (x : type1021) (h1 : term338 x) : term595 x _67137 _67138 _67136.
Proof. exact (EQ_MP (@lem5145164 x _67137 _67138 _67136) (@lem5143229 _67137 _67138 _67136 x h1)). Qed.
Lemma lem5145167 (b : Prop) (a : Prop) : (a \/ b) = (term558 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5145168 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term595 x _67137 _67138 _67136) = (term601 x _67137 _67138 _67136).
Proof. exact (@lem5145167 (term602 x _67137 _67138 _67136) (term81 _67138 _67136)). Qed.
Lemma lem5145170 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5145171 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term603 x _67137 _67138 _67136) = (term604 x _67137 _67138 _67136).
Proof. exact (@lem5145170 (_67136 = (@EMPTY real)) (term597 x _67137 _67138 _67136)). Qed.
Lemma lem5145173 (a : Prop) (b : Prop) : (term561 a b) = (term562 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5145174 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term605 x _67137 _67138 _67136) = (term606 x _67137 _67138 _67136).
Proof. exact (@lem5145173 (term487 x _67136 _67137) (term548 _67138 _67136)). Qed.
Lemma lem5145176 (a : Prop) : (term567 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5145177 (x : type1021) (_67136 : real -> Prop) (_67137 : real) : (term607 x _67136 _67137) = (term583 x _67136 _67137).
Proof. exact (@lem5145176 (term583 x _67136 _67137)). Qed.
Lemma lem5145178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5145179 (x : type1021) (_67136 : real -> Prop) (_67137 : real) : (term608 x _67136 _67137) = (term609 x _67136 _67137).
Proof. exact (MK_COMB (@lem5145178) (@lem5145177 x _67136 _67137)). Qed.
Lemma lem5145181 (a : Prop) : (term567 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5145182 (_67138 : real) (_67136 : real -> Prop) : (term568 _67138 _67136) = (@IN real _67138 _67136).
Proof. exact (@lem5145181 (@IN real _67138 _67136)). Qed.
Lemma lem5145183 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term606 x _67137 _67138 _67136) = (term610 x _67137 _67138 _67136).
Proof. exact (MK_COMB (@lem5145179 x _67136 _67137) (@lem5145182 _67138 _67136)). Qed.
Lemma lem5145184 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term605 x _67137 _67138 _67136) = (term610 x _67137 _67138 _67136).
Proof. exact (TRANS (@lem5145174 x _67137 _67138 _67136) (@lem5145183 x _67137 _67138 _67136)). Qed.
Lemma lem5145185 (_67136 : real -> Prop) : (term61 _67136) = (term61 _67136).
Proof. exact (eq_refl (term61 _67136)). Qed.
Lemma lem5145186 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term604 x _67137 _67138 _67136) = (term611 x _67137 _67138 _67136).
Proof. exact (MK_COMB (@lem5145185 _67136) (@lem5145184 x _67137 _67138 _67136)). Qed.
Lemma lem5145187 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term603 x _67137 _67138 _67136) = (term611 x _67137 _67138 _67136).
Proof. exact (TRANS (@lem5145171 x _67137 _67138 _67136) (@lem5145186 x _67137 _67138 _67136)). Qed.
Lemma lem5145188 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5145189 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term612 x _67137 _67138 _67136) = (term613 x _67137 _67138 _67136).
Proof. exact (MK_COMB (@lem5145188) (@lem5145187 x _67137 _67138 _67136)). Qed.
Lemma lem5145190 (_67138 : real) (_67136 : real -> Prop) : (term81 _67138 _67136) = (term81 _67138 _67136).
Proof. exact (eq_refl (term81 _67138 _67136)). Qed.
Lemma lem5145191 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term601 x _67137 _67138 _67136) = (term614 x _67137 _67138 _67136).
Proof. exact (MK_COMB (@lem5145189 x _67137 _67138 _67136) (@lem5145190 _67138 _67136)). Qed.
Lemma lem5145192 (x : type1021) (_67137 : real) (_67138 : real) (_67136 : real -> Prop) : (term595 x _67137 _67138 _67136) = (term614 x _67137 _67138 _67136).
Proof. exact (TRANS (@lem5145168 x _67137 _67138 _67136) (@lem5145191 x _67137 _67138 _67136)). Qed.
Lemma lem5145194 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 x' s) (h3 : term9 s) (h4 : term149 b x' s) (h5 : term80 x' s) : term610 x b x' s.
Proof. exact (conj (@lem5145010 x b x' s h1 h2 h3 h4 h5) (@lem5145017 x' s h5)). Qed.
Lemma lem5145195 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 x' s) (h3 : term9 s) (h4 : term149 b x' s) (h5 : term80 x' s) : term611 x b x' s.
Proof. exact (conj (@lem5144765 s h3) (@lem5145194 x b x' s h1 h2 h3 h4 h5)). Qed.
Lemma lem5145197 (_67137 : real) (_67138 : real) (_67136 : real -> Prop) (x : type1021) (h1 : term338 x) : term614 x _67137 _67138 _67136.
Proof. exact (EQ_MP (@lem5145192 x _67137 _67138 _67136) (@lem5145165 _67137 _67138 _67136 x h1)). Qed.
Lemma lem5145198 (b : real) (x' : real) (s : real -> Prop) (x : type1021) (h1 : term338 x) : term614 x b x' s.
Proof. exact (@lem5145197 b x' s x h1). Qed.
Lemma lem5145201 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term533 x' s) (h3 : term9 s) (h4 : term149 b x' s) (h5 : term80 x' s) : term81 x' s.
Proof. exact (@lem5145198 b x' s x h1 (@lem5145195 x b x' s h1 h2 h3 h4 h5)). Qed.
Lemma lem5145202 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b x' s) (h4 : term80 x' s) : term618 x' s.
Proof. exact (fun h0 : term533 x' s => @lem5145201 x b x' s h1 h0 h2 h3 h4). Qed.
Lemma lem5145204 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5145205 (x' : real) (s : real -> Prop) : (term618 x' s) = (term81 x' s).
Proof. exact (@lem5145204 (term81 x' s)). Qed.
Lemma lem5145206 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b x' s) (h4 : term80 x' s) : term81 x' s.
Proof. exact (EQ_MP (@lem5145205 x' s) (@lem5145202 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5145209 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5145211 (x' : real) (s : real -> Prop) : (term533 x' s) = (term751 x' s).
Proof. exact (@lem5145209 (term81 x' s)). Qed.
Lemma lem5145214 (x' : real) (s : real -> Prop) (h1 : term80 x' s) : term751 x' s.
Proof. exact (EQ_MP (@lem5145211 x' s) (@lem5143121 x' s h1)). Qed.
Lemma lem5145217 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b x' s) (h4 : term80 x' s) : False.
Proof. exact (@lem5145214 x' s h4 (@lem5145206 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5145218 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b x' s) (h4 : term80 x' s) : term750.
Proof. exact (fun h0 : ~ False => @lem5145217 x b x' s h1 h2 h3 h4). Qed.
Lemma lem5145220 (p : Prop) : (term544 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5145221 : term750 = False.
Proof. exact (@lem5145220 False). Qed.
Lemma lem5145222 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term9 s) (h3 : term149 b x' s) (h4 : term80 x' s) : False.
Proof. exact (EQ_MP (@lem5145221) (@lem5145218 x b x' s h1 h2 h3 h4)). Qed.
Lemma lem5145223 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b x' s) : (term106 s) = False.
Proof. exact (prop_ext (fun h6 : term106 s => @lem5144681 x b x' s h1 h2 h3 h4 h5) (fun h6 : False => @lem5142979 s h3)). Qed.
Lemma lem5145224 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b x' s) : False.
Proof. exact (EQ_MP (@lem5145223 x b x' s h1 h2 h3 h4 h5) (@lem5142979 s h3)). Qed.
Lemma lem5145225 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b x' s) : (term106 s) = False.
Proof. exact (prop_ext (fun h6 : term106 s => @lem5145224 x b x' s h1 h2 h3 h4 h5) (fun h6 : False => @lem5142560 s h3)). Qed.
Lemma lem5145226 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b x' s) : False.
Proof. exact (EQ_MP (@lem5145225 x b x' s h1 h2 h3 h4 h5) (@lem5142560 s h3)). Qed.
Lemma lem5145227 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b x' s) : (term106 s) = False.
Proof. exact (prop_ext (fun h6 : term106 s => @lem5145226 x b x' s h1 h2 h3 h4 h5) (fun h6 : False => @lem5142560 s h3)). Qed.
Lemma lem5145228 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term106 s) (h4 : term9 s) (h5 : term149 b x' s) : False.
Proof. exact (EQ_MP (@lem5145227 x b x' s h1 h2 h3 h4 h5) (@lem5142560 s h3)). Qed.
Lemma lem5145229 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b x' s) : False.
Proof. exact (or_elim (@lem5142250 b x' s h4) (fun h0 : term106 s => @lem5145228 x b x' s h1 h2 h0 h3 h4) (fun h0 : term80 x' s => @lem5145222 x b x' s h1 h3 h4 h0)). Qed.
Lemma lem5145230 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b x' s) : (term149 b x' s) = False.
Proof. exact (prop_ext (fun h5 : term149 b x' s => @lem5145229 x b x' s h1 h2 h3 h4) (fun h5 : False => @lem5142249 b x' s h4)). Qed.
Lemma lem5145231 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b x' s) : False.
Proof. exact (EQ_MP (@lem5145230 x b x' s h1 h2 h3 h4) (@lem5142249 b x' s h4)). Qed.
Lemma lem5145232 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b x' s) : (term338 x) = False.
Proof. exact (prop_ext (fun h5 : term338 x => @lem5145231 x b x' s h1 h2 h3 h4) (fun h5 : False => @lem5142190 x h1)). Qed.
Lemma lem5145233 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b x' s) : False.
Proof. exact (EQ_MP (@lem5145232 x b x' s h1 h2 h3 h4) (@lem5142190 x h1)). Qed.
Lemma lem5145234 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b x' s) : (term9 s) = False.
Proof. exact (prop_ext (fun h5 : term9 s => @lem5145233 x b x' s h1 h2 h3 h4) (fun h5 : False => @lem5142006 s h3)). Qed.
Lemma lem5145235 (x : type1021) (b : real) (x' : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term9 s) (h4 : term149 b x' s) : False.
Proof. exact (EQ_MP (@lem5145234 x b x' s h1 h2 h3 h4) (@lem5142006 s h3)). Qed.
Lemma lem5145236 (x : type1021) (b : real) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term152 b s) (h4 : term9 s) : False.
Proof. exact (ex_elim (@lem5141991 b s h3) (fun x' : real => fun h0 : term151 b s x' => @lem5145235 x b x' s h1 h2 h4 h0)). Qed.
Lemma lem5145237 (x : type1021) (s : real -> Prop) (h1 : term338 x) (h2 : term21) (h3 : term14 s) (h4 : term9 s) : False.
Proof. exact (ex_elim (@lem5141095 s h3) (fun b : real => fun h0 : term153 s b => @lem5145236 x b s h1 h2 h0 h4)). Qed.
Lemma lem5145238 (s : real -> Prop) (h1 : term66) (h2 : term21) (h3 : term14 s) (h4 : term9 s) : False.
Proof. exact (ex_elim (@lem5141624 h1) (fun x : type1021 => fun h0 : term340 x => @lem5145237 x s h0 h2 h3 h4)). Qed.
Lemma lem5145239 (s : real -> Prop) (h1 : term66) (h2 : term21) (h3 : term14 s) (h4 : term9 s) : (term9 s) = False.
Proof. exact (prop_ext (fun h5 : term9 s => @lem5145238 s h1 h2 h3 h4) (fun h5 : False => @lem5140831 s h4)). Qed.
Lemma lem5145240 (s : real -> Prop) (h1 : term66) (h2 : term21) (h3 : term14 s) (h4 : term9 s) : False.
Proof. exact (EQ_MP (@lem5145239 s h1 h2 h3 h4) (@lem5140831 s h4)). Qed.
Lemma lem5145241 (s : real -> Prop) (h1 : term66) (h2 : term14 s) (h3 : term9 s) : term19.
Proof. exact (fun h0 : term21 => @lem5145240 s h1 h0 h2 h3). Qed.
Lemma lem5145242 : term19 = term20.
Proof. exact (@lem69 term21). Qed.
Lemma lem5145243 (s : real -> Prop) (h1 : term66) (h2 : term14 s) (h3 : term9 s) : term20.
Proof. exact (EQ_MP (@lem5145242) (@lem5145241 s h1 h2 h3)). Qed.
Lemma lem5145244 (s : real -> Prop) (h1 : term66) (h2 : term14 s) (h3 : term9 s) : term24.
Proof. exact (fun h0 : term45 => @lem5145243 s h1 h2 h3). Qed.
Lemma lem5145245 (s : real -> Prop) (h1 : term14 s) (h2 : term9 s) : term27.
Proof. exact (fun h0 : term66 => @lem5145244 s h0 h1 h2). Qed.
Lemma lem5145246 (s : real -> Prop) (h1 : term9 s) : term30 s.
Proof. exact (fun h0 : term14 s => @lem5145245 s h0 h1). Qed.
Lemma lem5145247 (s : real -> Prop) : term32 s.
Proof. exact (fun h0 : term9 s => @lem5145246 s h0). Qed.
Lemma lem5145252 : term36.
Proof. exact (fun s : real -> Prop => @lem5145247 s). Qed.
Lemma lem5145253 : term35.
Proof. exact (EQ_MP (@lem5140816) (@lem5145252)). Qed.
Lemma lem5145254 (s : real -> Prop) : term752 s.
Proof. exact (@lem5145253 s). Qed.
Lemma lem5145255 (s : real -> Prop) : (term752 s) = (term15 s).
Proof. exact (eq_refl (term752 s)). Qed.
Lemma lem5145256 (s : real -> Prop) : term15 s.
Proof. exact (EQ_MP (@lem5145255 s) (@lem5145254 s)). Qed.
Lemma lem5145258 (s : real -> Prop) : term15 s.
Proof. exact (@lem5140347 s (@lem5145256 s)). Qed.
Lemma lem5145259 (s : real -> Prop) (h1 : term9 s) : term29 s.
Proof. exact (@lem5145258 s (@lem5140324 s h1)). Qed.
Lemma lem5145260 (s : real -> Prop) (h1 : term14 s) (h2 : term9 s) : term26.
Proof. exact (@lem5145259 s h2 (@lem5140332 s h1)). Qed.
Lemma lem5145261 (s : real -> Prop) (h1 : term14 s) (h2 : term9 s) : term23.
Proof. exact (@lem5145260 s h1 h2 (@lem5136700)). Qed.
Lemma lem5145262 (s : real -> Prop) (h1 : term14 s) (h2 : term9 s) : term19.
Proof. exact (@lem5145261 s h1 h2 (@lem1339697)). Qed.
Lemma lem5145263 (s : real -> Prop) (h1 : term14 s) (h2 : term9 s) : False.
Proof. exact (@lem5145262 s h1 h2 (@lem1339379)). Qed.
Lemma lem5145264 (s : real -> Prop) (h1 : term14 s) (h2 : term9 s) : (term14 s) = False.
Proof. exact (prop_ext (fun h3 : term14 s => @lem5145263 s h1 h2) (fun h3 : False => @lem5140332 s h1)). Qed.
Lemma lem5145265 (s : real -> Prop) (h1 : term14 s) (h2 : term9 s) : False.
Proof. exact (EQ_MP (@lem5145264 s h1 h2) (@lem5140332 s h1)). Qed.
Lemma lem5145266 (s : real -> Prop) (h1 : term9 s) : term13 s.
Proof. exact (fun h0 : term14 s => @lem5145265 s h0 h1). Qed.
Lemma lem5145267 (s : real -> Prop) (h1 : term9 s) : term12 s.
Proof. exact (EQ_MP (@lem5140331 s) (@lem5145266 s h1)). Qed.
Lemma lem5145268 (s : real -> Prop) (h1 : term9 s) : term68 s.
Proof. exact (@lem5145267 s h1 (@lem5140327 s h1)). Qed.
Lemma lem5145269 (s : real -> Prop) : term753 s.
Proof. exact (fun h0 : term9 s => @lem5145268 s h0). Qed.
Lemma lem5145274 : term754.
Proof. exact (fun s : real -> Prop => @lem5145269 s). Qed.
