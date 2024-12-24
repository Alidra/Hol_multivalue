Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MONOIDAL_INT_ADD_term_abbrevs.
Require Import monoidal_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16451_spec.
Require Import thm16452_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm2841544_spec.
Require Import thm2841585_spec.
Require Import thm2841586_spec.
Require Import thm2841591_spec.
Require Import thm2841592_spec.
Require Import thm2841615_spec.
Require Import thm2841616_spec.
Require Import thm2954598_spec.
Require Import thm6914239_spec.
Require Import thm6915505_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem6915507 {A : Type'} (op : type1400 A) : term0 A op.
Proof. exact (@lem5712802 A op). Qed.
Lemma lem6915508 {A : Type'} (op : type1400 A) : (term0 A op) = ((@monoidal A op) = (term1 A op)).
Proof. exact (eq_refl (term0 A op)). Qed.
Lemma lem6915511 {A : Type'} (op : type1400 A) : (@monoidal A op) = (term1 A op).
Proof. exact (EQ_MP (@lem6915508 A op) (@lem6915507 A op)). Qed.
Lemma lem6915512 (op : type1551) : (@monoidal int op) = (term2 op).
Proof. exact (@lem6915511 int op). Qed.
Lemma lem6915513 : (@monoidal int int_add) = term3.
Proof. exact (@lem6915512 int_add). Qed.
Lemma lem6915549 : (@neutral int int_add) = term4.
Proof. exact (EQ_MP (@lem6914239) (@lem6915505)). Qed.
Lemma lem6915550 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem6915551 : term5 = term6.
Proof. exact (MK_COMB (@lem6915550) (@lem6915549)). Qed.
Lemma lem6915552 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6915553 (x : int) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem6915551) (@lem6915552 x)). Qed.
Lemma lem6915554 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem6915555 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem6915554) (@lem6915553 x)). Qed.
Lemma lem6915556 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6915557 (x : int) : ((term7 x) = x) = ((term8 x) = x).
Proof. exact (MK_COMB (@lem6915555 x) (@lem6915556 x)). Qed.
Lemma lem6915560 : term11 = term12.
Proof. exact (fun_ext (fun x : int => @lem6915557 x)). Qed.
Lemma lem6915561 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem6915562 : term13 = term14.
Proof. exact (MK_COMB (@lem6915561) (@lem6915560)). Qed.
Lemma lem6915567 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem6915568 : term16 = term17.
Proof. exact (MK_COMB (@lem6915567) (@lem6915562)). Qed.
Lemma lem6915571 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem6915572 : term3 = term19.
Proof. exact (MK_COMB (@lem6915571) (@lem6915568)). Qed.
Lemma lem6915575 : (@monoidal int int_add) = term19.
Proof. exact (TRANS (@lem6915513) (@lem6915572)). Qed.
Lemma lem6915576 : term19 = (@monoidal int int_add).
Proof. exact (SYM (@lem6915575)). Qed.
Lemma lem6915577 : term20 = term19.
Proof. exact (@lem2954598 term19). Qed.
Lemma lem6915612 (P : int -> Prop) : (term21 P) = (term22 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem6915613 (x : int) : (term23 x) = (term24 x).
Proof. exact (@lem6915612 (term25 x)). Qed.
Lemma lem6915614 (y : int) (x : int) : (term26 x y) = ((int_add x y) = (int_add y x)).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem6915615 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6915617 (y : int) (x : int) : (term27 x y) = (term28 y x).
Proof. exact (MK_COMB (@lem6915615) (@lem6915614 y x)). Qed.
Lemma lem6915618 (x : int) : (term29 x) = (term30 x).
Proof. exact (fun_ext (fun y : int => @lem6915617 y x)). Qed.
Lemma lem6915619 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915620 (x : int) : (term24 x) = (term31 x).
Proof. exact (MK_COMB (@lem6915619) (@lem6915618 x)). Qed.
Lemma lem6915621 (x : int) : (term23 x) = (term31 x).
Proof. exact (TRANS (@lem6915613 x) (@lem6915620 x)). Qed.
Lemma lem6915622 (P : int -> Prop) : (term21 P) = (term22 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem6915623 : term32 = term33.
Proof. exact (@lem6915622 term34). Qed.
Lemma lem6915624 (x : int) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem6915625 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6915626 (x : int) : (term37 x) = (term23 x).
Proof. exact (MK_COMB (@lem6915625) (@lem6915624 x)). Qed.
Lemma lem6915627 (x : int) : (term37 x) = (term31 x).
Proof. exact (TRANS (@lem6915626 x) (@lem6915621 x)). Qed.
Lemma lem6915628 : term38 = term39.
Proof. exact (fun_ext (fun x : int => @lem6915627 x)). Qed.
Lemma lem6915629 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915630 : term33 = term40.
Proof. exact (MK_COMB (@lem6915629) (@lem6915628)). Qed.
Lemma lem6915631 : term32 = term40.
Proof. exact (TRANS (@lem6915623) (@lem6915630)). Qed.
Lemma lem6915633 (P : int -> Prop) : (term21 P) = (term22 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem6915634 (x : int) (y : int) : (term41 x y) = (term42 x y).
Proof. exact (@lem6915633 (term43 x y)). Qed.
Lemma lem6915635 (x : int) (y : int) (z : int) : (term44 x y z) = ((term45 x y z) = (term46 x y z)).
Proof. exact (eq_refl (term44 x y z)). Qed.
Lemma lem6915636 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6915638 (x : int) (y : int) (z : int) : (term47 x y z) = (term48 x y z).
Proof. exact (MK_COMB (@lem6915636) (@lem6915635 x y z)). Qed.
Lemma lem6915639 (x : int) (y : int) : (term49 x y) = (term50 x y).
Proof. exact (fun_ext (fun z : int => @lem6915638 x y z)). Qed.
Lemma lem6915640 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915641 (x : int) (y : int) : (term42 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem6915640) (@lem6915639 x y)). Qed.
Lemma lem6915642 (x : int) (y : int) : (term41 x y) = (term51 x y).
Proof. exact (TRANS (@lem6915634 x y) (@lem6915641 x y)). Qed.
Lemma lem6915643 (P : int -> Prop) : (term21 P) = (term22 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem6915644 (x : int) : (term52 x) = (term53 x).
Proof. exact (@lem6915643 (term54 x)). Qed.
Lemma lem6915645 (x : int) (y : int) : (term55 x y) = (term56 x y).
Proof. exact (eq_refl (term55 x y)). Qed.
Lemma lem6915646 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6915647 (x : int) (y : int) : (term57 x y) = (term41 x y).
Proof. exact (MK_COMB (@lem6915646) (@lem6915645 x y)). Qed.
Lemma lem6915648 (x : int) (y : int) : (term57 x y) = (term51 x y).
Proof. exact (TRANS (@lem6915647 x y) (@lem6915642 x y)). Qed.
Lemma lem6915649 (x : int) : (term58 x) = (term59 x).
Proof. exact (fun_ext (fun y : int => @lem6915648 x y)). Qed.
Lemma lem6915650 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915651 (x : int) : (term53 x) = (term60 x).
Proof. exact (MK_COMB (@lem6915650) (@lem6915649 x)). Qed.
Lemma lem6915652 (x : int) : (term52 x) = (term60 x).
Proof. exact (TRANS (@lem6915644 x) (@lem6915651 x)). Qed.
Lemma lem6915653 (P : int -> Prop) : (term21 P) = (term22 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem6915654 : term61 = term62.
Proof. exact (@lem6915653 term63). Qed.
Lemma lem6915655 (x : int) : (term64 x) = (term65 x).
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem6915656 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6915657 (x : int) : (term66 x) = (term52 x).
Proof. exact (MK_COMB (@lem6915656) (@lem6915655 x)). Qed.
Lemma lem6915658 (x : int) : (term66 x) = (term60 x).
Proof. exact (TRANS (@lem6915657 x) (@lem6915652 x)). Qed.
Lemma lem6915659 : term67 = term68.
Proof. exact (fun_ext (fun x : int => @lem6915658 x)). Qed.
Lemma lem6915660 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915661 : term62 = term69.
Proof. exact (MK_COMB (@lem6915660) (@lem6915659)). Qed.
Lemma lem6915662 : term61 = term69.
Proof. exact (TRANS (@lem6915654) (@lem6915661)). Qed.
Lemma lem6915664 (P : int -> Prop) : (term21 P) = (term22 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem6915665 : term70 = term71.
Proof. exact (@lem6915664 term12). Qed.
Lemma lem6915666 (x : int) : (term72 x) = ((term8 x) = x).
Proof. exact (eq_refl (term72 x)). Qed.
Lemma lem6915667 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6915669 (x : int) : (term73 x) = (term74 x).
Proof. exact (MK_COMB (@lem6915667) (@lem6915666 x)). Qed.
Lemma lem6915670 : term75 = term76.
Proof. exact (fun_ext (fun x : int => @lem6915669 x)). Qed.
Lemma lem6915671 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915672 : term71 = term77.
Proof. exact (MK_COMB (@lem6915671) (@lem6915670)). Qed.
Lemma lem6915673 : term70 = term77.
Proof. exact (TRANS (@lem6915665) (@lem6915672)). Qed.
Lemma lem6915674 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6915675 : term78 = term79.
Proof. exact (MK_COMB (@lem6915674) (@lem6915662)). Qed.
Lemma lem6915676 : term80 = term81.
Proof. exact (MK_COMB (@lem6915675) (@lem6915673)). Qed.
Lemma lem6915677 : term82 = term80.
Proof. exact (@lem17045 term83 term14). Qed.
Lemma lem6915678 : term82 = term81.
Proof. exact (TRANS (@lem6915677) (@lem6915676)). Qed.
Lemma lem6915679 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6915680 : term84 = term85.
Proof. exact (MK_COMB (@lem6915679) (@lem6915631)). Qed.
Lemma lem6915681 : term86 = term87.
Proof. exact (MK_COMB (@lem6915680) (@lem6915678)). Qed.
Lemma lem6915682 : term88 = term86.
Proof. exact (@lem17045 term89 term17). Qed.
Lemma lem6915684 : term88 = term87.
Proof. exact (TRANS (@lem6915682) (@lem6915681)). Qed.
Lemma lem6915687 (y : int) (x : int) : (term28 y x) = (term28 y x).
Proof. exact (eq_refl (term28 y x)). Qed.
Lemma lem6915688 (x : int) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun y : int => @lem6915687 y x)). Qed.
Lemma lem6915689 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915690 (x : int) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem6915689) (@lem6915688 x)). Qed.
Lemma lem6915691 : term39 = term39.
Proof. exact (fun_ext (fun x : int => @lem6915690 x)). Qed.
Lemma lem6915692 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915693 : term40 = term40.
Proof. exact (MK_COMB (@lem6915692) (@lem6915691)). Qed.
Lemma lem6915696 (x : int) (y : int) (z : int) : (term48 x y z) = (term48 x y z).
Proof. exact (eq_refl (term48 x y z)). Qed.
Lemma lem6915697 (x : int) (y : int) : (term50 x y) = (term50 x y).
Proof. exact (fun_ext (fun z : int => @lem6915696 x y z)). Qed.
Lemma lem6915698 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915699 (x : int) (y : int) : (term51 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem6915698) (@lem6915697 x y)). Qed.
Lemma lem6915700 (x : int) : (term59 x) = (term59 x).
Proof. exact (fun_ext (fun y : int => @lem6915699 x y)). Qed.
Lemma lem6915701 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915702 (x : int) : (term60 x) = (term60 x).
Proof. exact (MK_COMB (@lem6915701) (@lem6915700 x)). Qed.
Lemma lem6915703 : term68 = term68.
Proof. exact (fun_ext (fun x : int => @lem6915702 x)). Qed.
Lemma lem6915704 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915705 : term69 = term69.
Proof. exact (MK_COMB (@lem6915704) (@lem6915703)). Qed.
Lemma lem6915708 (x : int) : (term74 x) = (term74 x).
Proof. exact (eq_refl (term74 x)). Qed.
Lemma lem6915709 : term76 = term76.
Proof. exact (fun_ext (fun x : int => @lem6915708 x)). Qed.
Lemma lem6915710 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915711 : term77 = term77.
Proof. exact (MK_COMB (@lem6915710) (@lem6915709)). Qed.
Lemma lem6915712 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6915713 : term79 = term79.
Proof. exact (MK_COMB (@lem6915712) (@lem6915705)). Qed.
Lemma lem6915714 : term81 = term81.
Proof. exact (MK_COMB (@lem6915713) (@lem6915711)). Qed.
Lemma lem6915715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6915716 : term85 = term85.
Proof. exact (MK_COMB (@lem6915715) (@lem6915693)). Qed.
Lemma lem6915717 : term87 = term87.
Proof. exact (MK_COMB (@lem6915716) (@lem6915714)). Qed.
Lemma lem6915756 : term88 = term87.
Proof. exact (TRANS (@lem6915684) (@lem6915717)). Qed.
Lemma lem6915758 (y : int) (x : int) : (term90 x y) = (term91 y x).
Proof. exact (proj1 (@lem2841544 x y)). Qed.
Lemma lem6915759 (x : int) (y : int) : (term28 y x) = (term92 x y).
Proof. exact (@lem6915758 (int_add y x) (int_add x y)). Qed.
Lemma lem6915761 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem6915762 (y : int) (x : int) : (term94 y x) = (term95 y x).
Proof. exact (@lem6915761 (term96 x y) (int_add y x)). Qed.
Lemma lem6915764 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915765 (x : int) (y : int) : (term99 x y) = (term100 x y).
Proof. exact (@lem6915764 (int_add x y) term101). Qed.
Lemma lem6915767 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915768 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6915769 (x : int) (y : int) : (term102 x y) = (term103 x y).
Proof. exact (MK_COMB (@lem6915768) (@lem6915767 x y)). Qed.
Lemma lem6915771 (n : nat) : (term104 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem6915772 : term105 = term106.
Proof. exact (@lem6915771 term107). Qed.
Lemma lem6915773 (x : int) (y : int) : (term100 x y) = (term108 x y).
Proof. exact (MK_COMB (@lem6915769 x y) (@lem6915772)). Qed.
Lemma lem6915774 (x : int) (y : int) : (term99 x y) = (term108 x y).
Proof. exact (TRANS (@lem6915765 x y) (@lem6915773 x y)). Qed.
Lemma lem6915775 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6915776 (x : int) (y : int) : (term109 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem6915775) (@lem6915774 x y)). Qed.
Lemma lem6915778 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915779 (y : int) (x : int) : (term97 y x) = (term98 y x).
Proof. exact (@lem6915778 y x). Qed.
Lemma lem6915780 (y : int) (x : int) : (term95 y x) = (term111 y x).
Proof. exact (MK_COMB (@lem6915776 x y) (@lem6915779 y x)). Qed.
Lemma lem6915781 (y : int) (x : int) : (term94 y x) = (term111 y x).
Proof. exact (TRANS (@lem6915762 y x) (@lem6915780 y x)). Qed.
Lemma lem6915782 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6915783 (y : int) (x : int) : (term112 y x) = (term113 y x).
Proof. exact (MK_COMB (@lem6915782) (@lem6915781 y x)). Qed.
Lemma lem6915785 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem6915786 (x : int) (y : int) : (term94 x y) = (term95 x y).
Proof. exact (@lem6915785 (term96 y x) (int_add x y)). Qed.
Lemma lem6915788 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915789 (y : int) (x : int) : (term99 y x) = (term100 y x).
Proof. exact (@lem6915788 (int_add y x) term101). Qed.
Lemma lem6915791 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915792 (y : int) (x : int) : (term97 y x) = (term98 y x).
Proof. exact (@lem6915791 y x). Qed.
Lemma lem6915793 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6915794 (y : int) (x : int) : (term102 y x) = (term103 y x).
Proof. exact (MK_COMB (@lem6915793) (@lem6915792 y x)). Qed.
Lemma lem6915796 (n : nat) : (term104 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem6915797 : term105 = term106.
Proof. exact (@lem6915796 term107). Qed.
Lemma lem6915798 (y : int) (x : int) : (term100 y x) = (term108 y x).
Proof. exact (MK_COMB (@lem6915794 y x) (@lem6915797)). Qed.
Lemma lem6915799 (y : int) (x : int) : (term99 y x) = (term108 y x).
Proof. exact (TRANS (@lem6915789 y x) (@lem6915798 y x)). Qed.
Lemma lem6915800 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6915801 (y : int) (x : int) : (term109 y x) = (term110 y x).
Proof. exact (MK_COMB (@lem6915800) (@lem6915799 y x)). Qed.
Lemma lem6915803 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915804 (x : int) (y : int) : (term95 x y) = (term111 x y).
Proof. exact (MK_COMB (@lem6915801 y x) (@lem6915803 x y)). Qed.
Lemma lem6915805 (x : int) (y : int) : (term94 x y) = (term111 x y).
Proof. exact (TRANS (@lem6915786 x y) (@lem6915804 x y)). Qed.
Lemma lem6915806 (x : int) (y : int) : (term92 x y) = (term114 x y).
Proof. exact (MK_COMB (@lem6915783 y x) (@lem6915805 x y)). Qed.
Lemma lem6915807 (x : int) (y : int) : (term28 y x) = (term114 x y).
Proof. exact (TRANS (@lem6915759 x y) (@lem6915806 x y)). Qed.
Lemma lem6915808 (x : int) : (term30 x) = (term115 x).
Proof. exact (fun_ext (fun y : int => @lem6915807 x y)). Qed.
Lemma lem6915809 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915810 (x : int) : (term31 x) = (term116 x).
Proof. exact (MK_COMB (@lem6915809) (@lem6915808 x)). Qed.
Lemma lem6915811 : term39 = term117.
Proof. exact (fun_ext (fun x : int => @lem6915810 x)). Qed.
Lemma lem6915812 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915813 : term40 = term118.
Proof. exact (MK_COMB (@lem6915812) (@lem6915811)). Qed.
Lemma lem6915815 (y : int) (x : int) : (term90 x y) = (term91 y x).
Proof. exact (proj1 (@lem2841544 x y)). Qed.
Lemma lem6915816 (x : int) (y : int) (z : int) : (term48 x y z) = (term119 x y z).
Proof. exact (@lem6915815 (term46 x y z) (term45 x y z)). Qed.
Lemma lem6915818 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem6915819 (x : int) (y : int) (z : int) : (term120 x y z) = (term121 x y z).
Proof. exact (@lem6915818 (term122 x y z) (term46 x y z)). Qed.
Lemma lem6915821 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915822 (x : int) (y : int) (z : int) : (term123 x y z) = (term124 x y z).
Proof. exact (@lem6915821 (term45 x y z) term101). Qed.
Lemma lem6915824 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915825 (x : int) (y : int) (z : int) : (term125 x y z) = (term126 x y z).
Proof. exact (@lem6915824 x (int_add y z)). Qed.
Lemma lem6915827 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915828 (y : int) (z : int) : (term97 y z) = (term98 y z).
Proof. exact (@lem6915827 y z). Qed.
Lemma lem6915829 (x : int) : (term127 x) = (term127 x).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem6915830 (x : int) (y : int) (z : int) : (term126 x y z) = (term128 x y z).
Proof. exact (MK_COMB (@lem6915829 x) (@lem6915828 y z)). Qed.
Lemma lem6915831 (x : int) (y : int) (z : int) : (term125 x y z) = (term128 x y z).
Proof. exact (TRANS (@lem6915825 x y z) (@lem6915830 x y z)). Qed.
Lemma lem6915832 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6915833 (x : int) (y : int) (z : int) : (term129 x y z) = (term130 x y z).
Proof. exact (MK_COMB (@lem6915832) (@lem6915831 x y z)). Qed.
Lemma lem6915835 (n : nat) : (term104 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem6915836 : term105 = term106.
Proof. exact (@lem6915835 term107). Qed.
Lemma lem6915837 (x : int) (y : int) (z : int) : (term124 x y z) = (term131 x y z).
Proof. exact (MK_COMB (@lem6915833 x y z) (@lem6915836)). Qed.
Lemma lem6915838 (x : int) (y : int) (z : int) : (term123 x y z) = (term131 x y z).
Proof. exact (TRANS (@lem6915822 x y z) (@lem6915837 x y z)). Qed.
Lemma lem6915839 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6915840 (x : int) (y : int) (z : int) : (term132 x y z) = (term133 x y z).
Proof. exact (MK_COMB (@lem6915839) (@lem6915838 x y z)). Qed.
Lemma lem6915842 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915843 (x : int) (y : int) (z : int) : (term134 x y z) = (term135 x y z).
Proof. exact (@lem6915842 (int_add x y) z). Qed.
Lemma lem6915845 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915846 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6915847 (x : int) (y : int) : (term102 x y) = (term103 x y).
Proof. exact (MK_COMB (@lem6915846) (@lem6915845 x y)). Qed.
Lemma lem6915848 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem6915849 (x : int) (y : int) (z : int) : (term135 x y z) = (term136 x y z).
Proof. exact (MK_COMB (@lem6915847 x y) (@lem6915848 z)). Qed.
Lemma lem6915850 (x : int) (y : int) (z : int) : (term134 x y z) = (term136 x y z).
Proof. exact (TRANS (@lem6915843 x y z) (@lem6915849 x y z)). Qed.
Lemma lem6915851 (x : int) (y : int) (z : int) : (term121 x y z) = (term137 x y z).
Proof. exact (MK_COMB (@lem6915840 x y z) (@lem6915850 x y z)). Qed.
Lemma lem6915852 (x : int) (y : int) (z : int) : (term120 x y z) = (term137 x y z).
Proof. exact (TRANS (@lem6915819 x y z) (@lem6915851 x y z)). Qed.
Lemma lem6915853 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6915854 (x : int) (y : int) (z : int) : (term138 x y z) = (term139 x y z).
Proof. exact (MK_COMB (@lem6915853) (@lem6915852 x y z)). Qed.
Lemma lem6915856 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem6915857 (x : int) (y : int) (z : int) : (term140 x y z) = (term141 x y z).
Proof. exact (@lem6915856 (term142 x y z) (term45 x y z)). Qed.
Lemma lem6915859 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915860 (x : int) (y : int) (z : int) : (term143 x y z) = (term144 x y z).
Proof. exact (@lem6915859 (term46 x y z) term101). Qed.
Lemma lem6915862 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915863 (x : int) (y : int) (z : int) : (term134 x y z) = (term135 x y z).
Proof. exact (@lem6915862 (int_add x y) z). Qed.
Lemma lem6915865 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915866 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6915867 (x : int) (y : int) : (term102 x y) = (term103 x y).
Proof. exact (MK_COMB (@lem6915866) (@lem6915865 x y)). Qed.
Lemma lem6915868 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem6915869 (x : int) (y : int) (z : int) : (term135 x y z) = (term136 x y z).
Proof. exact (MK_COMB (@lem6915867 x y) (@lem6915868 z)). Qed.
Lemma lem6915870 (x : int) (y : int) (z : int) : (term134 x y z) = (term136 x y z).
Proof. exact (TRANS (@lem6915863 x y z) (@lem6915869 x y z)). Qed.
Lemma lem6915871 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6915872 (x : int) (y : int) (z : int) : (term145 x y z) = (term146 x y z).
Proof. exact (MK_COMB (@lem6915871) (@lem6915870 x y z)). Qed.
Lemma lem6915874 (n : nat) : (term104 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem6915875 : term105 = term106.
Proof. exact (@lem6915874 term107). Qed.
Lemma lem6915876 (x : int) (y : int) (z : int) : (term144 x y z) = (term147 x y z).
Proof. exact (MK_COMB (@lem6915872 x y z) (@lem6915875)). Qed.
Lemma lem6915877 (x : int) (y : int) (z : int) : (term143 x y z) = (term147 x y z).
Proof. exact (TRANS (@lem6915860 x y z) (@lem6915876 x y z)). Qed.
Lemma lem6915878 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6915879 (x : int) (y : int) (z : int) : (term148 x y z) = (term149 x y z).
Proof. exact (MK_COMB (@lem6915878) (@lem6915877 x y z)). Qed.
Lemma lem6915881 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915882 (x : int) (y : int) (z : int) : (term125 x y z) = (term126 x y z).
Proof. exact (@lem6915881 x (int_add y z)). Qed.
Lemma lem6915884 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915885 (y : int) (z : int) : (term97 y z) = (term98 y z).
Proof. exact (@lem6915884 y z). Qed.
Lemma lem6915886 (x : int) : (term127 x) = (term127 x).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem6915887 (x : int) (y : int) (z : int) : (term126 x y z) = (term128 x y z).
Proof. exact (MK_COMB (@lem6915886 x) (@lem6915885 y z)). Qed.
Lemma lem6915888 (x : int) (y : int) (z : int) : (term125 x y z) = (term128 x y z).
Proof. exact (TRANS (@lem6915882 x y z) (@lem6915887 x y z)). Qed.
Lemma lem6915889 (x : int) (y : int) (z : int) : (term141 x y z) = (term150 x y z).
Proof. exact (MK_COMB (@lem6915879 x y z) (@lem6915888 x y z)). Qed.
Lemma lem6915890 (x : int) (y : int) (z : int) : (term140 x y z) = (term150 x y z).
Proof. exact (TRANS (@lem6915857 x y z) (@lem6915889 x y z)). Qed.
Lemma lem6915891 (x : int) (y : int) (z : int) : (term119 x y z) = (term151 x y z).
Proof. exact (MK_COMB (@lem6915854 x y z) (@lem6915890 x y z)). Qed.
Lemma lem6915892 (x : int) (y : int) (z : int) : (term48 x y z) = (term151 x y z).
Proof. exact (TRANS (@lem6915816 x y z) (@lem6915891 x y z)). Qed.
Lemma lem6915893 (x : int) (y : int) : (term50 x y) = (term152 x y).
Proof. exact (fun_ext (fun z : int => @lem6915892 x y z)). Qed.
Lemma lem6915894 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915895 (x : int) (y : int) : (term51 x y) = (term153 x y).
Proof. exact (MK_COMB (@lem6915894) (@lem6915893 x y)). Qed.
Lemma lem6915896 (x : int) : (term59 x) = (term154 x).
Proof. exact (fun_ext (fun y : int => @lem6915895 x y)). Qed.
Lemma lem6915897 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915898 (x : int) : (term60 x) = (term155 x).
Proof. exact (MK_COMB (@lem6915897) (@lem6915896 x)). Qed.
Lemma lem6915899 : term68 = term156.
Proof. exact (fun_ext (fun x : int => @lem6915898 x)). Qed.
Lemma lem6915900 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915901 : term69 = term157.
Proof. exact (MK_COMB (@lem6915900) (@lem6915899)). Qed.
Lemma lem6915903 (y : int) (x : int) : (term90 x y) = (term91 y x).
Proof. exact (proj1 (@lem2841544 x y)). Qed.
Lemma lem6915904 (x : int) : (term74 x) = (term158 x).
Proof. exact (@lem6915903 x (term8 x)). Qed.
Lemma lem6915906 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem6915907 (x : int) : (term159 x) = (term160 x).
Proof. exact (@lem6915906 (term161 x) x). Qed.
Lemma lem6915909 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915910 (x : int) : (term162 x) = (term163 x).
Proof. exact (@lem6915909 (term8 x) term101). Qed.
Lemma lem6915912 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915913 (x : int) : (term164 x) = (term165 x).
Proof. exact (@lem6915912 term4 x). Qed.
Lemma lem6915915 (n : nat) : (term104 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem6915916 : term166 = term167.
Proof. exact (@lem6915915 (NUMERAL 0)). Qed.
Lemma lem6915917 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6915918 : term168 = term169.
Proof. exact (MK_COMB (@lem6915917) (@lem6915916)). Qed.
Lemma lem6915919 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem6915920 (x : int) : (term165 x) = (term170 x).
Proof. exact (MK_COMB (@lem6915918) (@lem6915919 x)). Qed.
Lemma lem6915921 (x : int) : (term164 x) = (term170 x).
Proof. exact (TRANS (@lem6915913 x) (@lem6915920 x)). Qed.
Lemma lem6915922 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6915923 (x : int) : (term171 x) = (term172 x).
Proof. exact (MK_COMB (@lem6915922) (@lem6915921 x)). Qed.
Lemma lem6915925 (n : nat) : (term104 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem6915926 : term105 = term106.
Proof. exact (@lem6915925 term107). Qed.
Lemma lem6915927 (x : int) : (term163 x) = (term173 x).
Proof. exact (MK_COMB (@lem6915923 x) (@lem6915926)). Qed.
Lemma lem6915928 (x : int) : (term162 x) = (term173 x).
Proof. exact (TRANS (@lem6915910 x) (@lem6915927 x)). Qed.
Lemma lem6915929 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6915930 (x : int) : (term174 x) = (term175 x).
Proof. exact (MK_COMB (@lem6915929) (@lem6915928 x)). Qed.
Lemma lem6915931 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem6915932 (x : int) : (term160 x) = (term176 x).
Proof. exact (MK_COMB (@lem6915930 x) (@lem6915931 x)). Qed.
Lemma lem6915933 (x : int) : (term159 x) = (term176 x).
Proof. exact (TRANS (@lem6915907 x) (@lem6915932 x)). Qed.
Lemma lem6915934 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6915935 (x : int) : (term177 x) = (term178 x).
Proof. exact (MK_COMB (@lem6915934) (@lem6915933 x)). Qed.
Lemma lem6915937 (x : int) (y : int) : (int_le x y) = (term93 x y).
Proof. exact (EQ_MP (@lem2841616 x y) (@lem2841615 x y)). Qed.
Lemma lem6915938 (x : int) : (term179 x) = (term180 x).
Proof. exact (@lem6915937 (term181 x) (term8 x)). Qed.
Lemma lem6915940 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915941 (x : int) : (term182 x) = (term183 x).
Proof. exact (@lem6915940 x term101). Qed.
Lemma lem6915943 (n : nat) : (term104 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem6915944 : term105 = term106.
Proof. exact (@lem6915943 term107). Qed.
Lemma lem6915945 (x : int) : (term127 x) = (term127 x).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem6915946 (x : int) : (term183 x) = (term184 x).
Proof. exact (MK_COMB (@lem6915945 x) (@lem6915944)). Qed.
Lemma lem6915947 (x : int) : (term182 x) = (term184 x).
Proof. exact (TRANS (@lem6915941 x) (@lem6915946 x)). Qed.
Lemma lem6915948 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6915949 (x : int) : (term185 x) = (term186 x).
Proof. exact (MK_COMB (@lem6915948) (@lem6915947 x)). Qed.
Lemma lem6915951 (x : int) (y : int) : (term97 x y) = (term98 x y).
Proof. exact (EQ_MP (@lem2841586 x y) (@lem2841585 x y)). Qed.
Lemma lem6915952 (x : int) : (term164 x) = (term165 x).
Proof. exact (@lem6915951 term4 x). Qed.
Lemma lem6915954 (n : nat) : (term104 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2841592 n) (@lem2841591 n)). Qed.
Lemma lem6915955 : term166 = term167.
Proof. exact (@lem6915954 (NUMERAL 0)). Qed.
Lemma lem6915956 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6915957 : term168 = term169.
Proof. exact (MK_COMB (@lem6915956) (@lem6915955)). Qed.
Lemma lem6915958 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem6915959 (x : int) : (term165 x) = (term170 x).
Proof. exact (MK_COMB (@lem6915957) (@lem6915958 x)). Qed.
Lemma lem6915960 (x : int) : (term164 x) = (term170 x).
Proof. exact (TRANS (@lem6915952 x) (@lem6915959 x)). Qed.
Lemma lem6915961 (x : int) : (term180 x) = (term187 x).
Proof. exact (MK_COMB (@lem6915949 x) (@lem6915960 x)). Qed.
Lemma lem6915962 (x : int) : (term179 x) = (term187 x).
Proof. exact (TRANS (@lem6915938 x) (@lem6915961 x)). Qed.
Lemma lem6915963 (x : int) : (term158 x) = (term188 x).
Proof. exact (MK_COMB (@lem6915935 x) (@lem6915962 x)). Qed.
Lemma lem6915964 (x : int) : (term74 x) = (term188 x).
Proof. exact (TRANS (@lem6915904 x) (@lem6915963 x)). Qed.
Lemma lem6915965 : term76 = term189.
Proof. exact (fun_ext (fun x : int => @lem6915964 x)). Qed.
Lemma lem6915966 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915967 : term77 = term190.
Proof. exact (MK_COMB (@lem6915966) (@lem6915965)). Qed.
Lemma lem6915968 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6915969 : term79 = term191.
Proof. exact (MK_COMB (@lem6915968) (@lem6915901)). Qed.
Lemma lem6915970 : term81 = term192.
Proof. exact (MK_COMB (@lem6915969) (@lem6915967)). Qed.
Lemma lem6915971 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6915972 : term85 = term193.
Proof. exact (MK_COMB (@lem6915971) (@lem6915813)). Qed.
Lemma lem6915973 : term87 = term194.
Proof. exact (MK_COMB (@lem6915972) (@lem6915970)). Qed.
Lemma lem6915974 : term88 = term194.
Proof. exact (TRANS (@lem6915756) (@lem6915973)). Qed.
Lemma lem6915978 (t : Prop) : (term195 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6915979 : term196 = term194.
Proof. exact (@lem6915978 term194). Qed.
Lemma lem6915987 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem6915988 (P : int -> Prop) (Q : int -> Prop) : (term199 P Q) = (term200 P Q).
Proof. exact (@lem6915987 int P Q). Qed.
Lemma lem6915989 (x : int) : (term201 x) = (term202 x).
Proof. exact (@lem6915988 (term203 x) (term204 x)). Qed.
Lemma lem6915990 (y : int) (x : int) : (term205 x y) = (term111 y x).
Proof. exact (eq_refl (term205 x y)). Qed.
Lemma lem6915991 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6915992 (y : int) (x : int) : (term206 x y) = (term113 y x).
Proof. exact (MK_COMB (@lem6915991) (@lem6915990 y x)). Qed.
Lemma lem6915993 (x : int) (y : int) : (term207 x y) = (term111 x y).
Proof. exact (eq_refl (term207 x y)). Qed.
Lemma lem6915994 (x : int) (y : int) : (term208 x y) = (term114 x y).
Proof. exact (MK_COMB (@lem6915992 y x) (@lem6915993 x y)). Qed.
Lemma lem6915995 (x : int) : (term209 x) = (term115 x).
Proof. exact (fun_ext (fun y : int => @lem6915994 x y)). Qed.
Lemma lem6915996 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6915997 (x : int) : (term201 x) = (term116 x).
Proof. exact (MK_COMB (@lem6915996) (@lem6915995 x)). Qed.
Lemma lem6915998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6915999 (x : int) : (term210 x) = (term211 x).
Proof. exact (MK_COMB (@lem6915998) (@lem6915997 x)). Qed.
Lemma lem6916000 (y : int) (x : int) : (term205 x y) = (term111 y x).
Proof. exact (eq_refl (term205 x y)). Qed.
Lemma lem6916001 (x : int) : (term212 x) = (term203 x).
Proof. exact (fun_ext (fun y : int => @lem6916000 y x)). Qed.
Lemma lem6916002 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916003 (x : int) : (term213 x) = (term214 x).
Proof. exact (MK_COMB (@lem6916002) (@lem6916001 x)). Qed.
Lemma lem6916004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916005 (x : int) : (term215 x) = (term216 x).
Proof. exact (MK_COMB (@lem6916004) (@lem6916003 x)). Qed.
Lemma lem6916006 (x : int) (y : int) : (term207 x y) = (term111 x y).
Proof. exact (eq_refl (term207 x y)). Qed.
Lemma lem6916007 (x : int) : (term217 x) = (term204 x).
Proof. exact (fun_ext (fun y : int => @lem6916006 x y)). Qed.
Lemma lem6916008 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916009 (x : int) : (term218 x) = (term219 x).
Proof. exact (MK_COMB (@lem6916008) (@lem6916007 x)). Qed.
Lemma lem6916010 (x : int) : (term202 x) = (term220 x).
Proof. exact (MK_COMB (@lem6916005 x) (@lem6916009 x)). Qed.
Lemma lem6916011 (x : int) : ((term201 x) = (term202 x)) = ((term116 x) = (term220 x)).
Proof. exact (MK_COMB (@lem6915999 x) (@lem6916010 x)). Qed.
Lemma lem6916012 (x : int) : (term116 x) = (term220 x).
Proof. exact (EQ_MP (@lem6916011 x) (@lem6915989 x)). Qed.
Lemma lem6916023 : term117 = term221.
Proof. exact (fun_ext (fun x : int => @lem6916012 x)). Qed.
Lemma lem6916024 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916025 : term118 = term222.
Proof. exact (MK_COMB (@lem6916024) (@lem6916023)). Qed.
Lemma lem6916027 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem6916028 (P : int -> Prop) (Q : int -> Prop) : (term199 P Q) = (term200 P Q).
Proof. exact (@lem6916027 int P Q). Qed.
Lemma lem6916029 : term223 = term224.
Proof. exact (@lem6916028 term225 term226). Qed.
Lemma lem6916030 (x : int) : (term227 x) = (term214 x).
Proof. exact (eq_refl (term227 x)). Qed.
Lemma lem6916031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916032 (x : int) : (term228 x) = (term216 x).
Proof. exact (MK_COMB (@lem6916031) (@lem6916030 x)). Qed.
Lemma lem6916033 (x : int) : (term229 x) = (term219 x).
Proof. exact (eq_refl (term229 x)). Qed.
Lemma lem6916034 (x : int) : (term230 x) = (term220 x).
Proof. exact (MK_COMB (@lem6916032 x) (@lem6916033 x)). Qed.
Lemma lem6916035 : term231 = term221.
Proof. exact (fun_ext (fun x : int => @lem6916034 x)). Qed.
Lemma lem6916036 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916037 : term223 = term222.
Proof. exact (MK_COMB (@lem6916036) (@lem6916035)). Qed.
Lemma lem6916038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6916039 : term232 = term233.
Proof. exact (MK_COMB (@lem6916038) (@lem6916037)). Qed.
Lemma lem6916040 (x : int) : (term227 x) = (term214 x).
Proof. exact (eq_refl (term227 x)). Qed.
Lemma lem6916041 : term234 = term225.
Proof. exact (fun_ext (fun x : int => @lem6916040 x)). Qed.
Lemma lem6916042 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916043 : term235 = term236.
Proof. exact (MK_COMB (@lem6916042) (@lem6916041)). Qed.
Lemma lem6916044 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916045 : term237 = term238.
Proof. exact (MK_COMB (@lem6916044) (@lem6916043)). Qed.
Lemma lem6916046 (x : int) : (term229 x) = (term219 x).
Proof. exact (eq_refl (term229 x)). Qed.
Lemma lem6916047 : term239 = term226.
Proof. exact (fun_ext (fun x : int => @lem6916046 x)). Qed.
Lemma lem6916048 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916049 : term240 = term241.
Proof. exact (MK_COMB (@lem6916048) (@lem6916047)). Qed.
Lemma lem6916050 : term224 = term242.
Proof. exact (MK_COMB (@lem6916045) (@lem6916049)). Qed.
Lemma lem6916051 : (term223 = term224) = (term222 = term242).
Proof. exact (MK_COMB (@lem6916039) (@lem6916050)). Qed.
Lemma lem6916052 : term222 = term242.
Proof. exact (EQ_MP (@lem6916051) (@lem6916029)). Qed.
Lemma lem6916071 : term118 = term242.
Proof. exact (TRANS (@lem6916025) (@lem6916052)). Qed.
Lemma lem6916072 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916073 : term193 = term243.
Proof. exact (MK_COMB (@lem6916072) (@lem6916071)). Qed.
Lemma lem6916085 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem6916086 (P : int -> Prop) (Q : int -> Prop) : (term199 P Q) = (term200 P Q).
Proof. exact (@lem6916085 int P Q). Qed.
Lemma lem6916087 (x : int) (y : int) : (term244 x y) = (term245 x y).
Proof. exact (@lem6916086 (term246 x y) (term247 x y)). Qed.
Lemma lem6916088 (x : int) (y : int) (z : int) : (term248 x y z) = (term137 x y z).
Proof. exact (eq_refl (term248 x y z)). Qed.
Lemma lem6916089 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916090 (x : int) (y : int) (z : int) : (term249 x y z) = (term139 x y z).
Proof. exact (MK_COMB (@lem6916089) (@lem6916088 x y z)). Qed.
Lemma lem6916091 (x : int) (y : int) (z : int) : (term250 x y z) = (term150 x y z).
Proof. exact (eq_refl (term250 x y z)). Qed.
Lemma lem6916092 (x : int) (y : int) (z : int) : (term251 x y z) = (term151 x y z).
Proof. exact (MK_COMB (@lem6916090 x y z) (@lem6916091 x y z)). Qed.
Lemma lem6916093 (x : int) (y : int) : (term252 x y) = (term152 x y).
Proof. exact (fun_ext (fun z : int => @lem6916092 x y z)). Qed.
Lemma lem6916094 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916095 (x : int) (y : int) : (term244 x y) = (term153 x y).
Proof. exact (MK_COMB (@lem6916094) (@lem6916093 x y)). Qed.
Lemma lem6916096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6916097 (x : int) (y : int) : (term253 x y) = (term254 x y).
Proof. exact (MK_COMB (@lem6916096) (@lem6916095 x y)). Qed.
Lemma lem6916098 (x : int) (y : int) (z : int) : (term248 x y z) = (term137 x y z).
Proof. exact (eq_refl (term248 x y z)). Qed.
Lemma lem6916099 (x : int) (y : int) : (term255 x y) = (term246 x y).
Proof. exact (fun_ext (fun z : int => @lem6916098 x y z)). Qed.
Lemma lem6916100 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916101 (x : int) (y : int) : (term256 x y) = (term257 x y).
Proof. exact (MK_COMB (@lem6916100) (@lem6916099 x y)). Qed.
Lemma lem6916102 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916103 (x : int) (y : int) : (term258 x y) = (term259 x y).
Proof. exact (MK_COMB (@lem6916102) (@lem6916101 x y)). Qed.
Lemma lem6916104 (x : int) (y : int) (z : int) : (term250 x y z) = (term150 x y z).
Proof. exact (eq_refl (term250 x y z)). Qed.
Lemma lem6916105 (x : int) (y : int) : (term260 x y) = (term247 x y).
Proof. exact (fun_ext (fun z : int => @lem6916104 x y z)). Qed.
Lemma lem6916106 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916107 (x : int) (y : int) : (term261 x y) = (term262 x y).
Proof. exact (MK_COMB (@lem6916106) (@lem6916105 x y)). Qed.
Lemma lem6916108 (x : int) (y : int) : (term245 x y) = (term263 x y).
Proof. exact (MK_COMB (@lem6916103 x y) (@lem6916107 x y)). Qed.
Lemma lem6916109 (x : int) (y : int) : ((term244 x y) = (term245 x y)) = ((term153 x y) = (term263 x y)).
Proof. exact (MK_COMB (@lem6916097 x y) (@lem6916108 x y)). Qed.
Lemma lem6916110 (x : int) (y : int) : (term153 x y) = (term263 x y).
Proof. exact (EQ_MP (@lem6916109 x y) (@lem6916087 x y)). Qed.
Lemma lem6916121 (x : int) : (term154 x) = (term264 x).
Proof. exact (fun_ext (fun y : int => @lem6916110 x y)). Qed.
Lemma lem6916122 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916123 (x : int) : (term155 x) = (term265 x).
Proof. exact (MK_COMB (@lem6916122) (@lem6916121 x)). Qed.
Lemma lem6916125 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem6916126 (P : int -> Prop) (Q : int -> Prop) : (term199 P Q) = (term200 P Q).
Proof. exact (@lem6916125 int P Q). Qed.
Lemma lem6916127 (x : int) : (term266 x) = (term267 x).
Proof. exact (@lem6916126 (term268 x) (term269 x)). Qed.
Lemma lem6916128 (x : int) (y : int) : (term270 x y) = (term257 x y).
Proof. exact (eq_refl (term270 x y)). Qed.
Lemma lem6916129 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916130 (x : int) (y : int) : (term271 x y) = (term259 x y).
Proof. exact (MK_COMB (@lem6916129) (@lem6916128 x y)). Qed.
Lemma lem6916131 (x : int) (y : int) : (term272 x y) = (term262 x y).
Proof. exact (eq_refl (term272 x y)). Qed.
Lemma lem6916132 (x : int) (y : int) : (term273 x y) = (term263 x y).
Proof. exact (MK_COMB (@lem6916130 x y) (@lem6916131 x y)). Qed.
Lemma lem6916133 (x : int) : (term274 x) = (term264 x).
Proof. exact (fun_ext (fun y : int => @lem6916132 x y)). Qed.
Lemma lem6916134 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916135 (x : int) : (term266 x) = (term265 x).
Proof. exact (MK_COMB (@lem6916134) (@lem6916133 x)). Qed.
Lemma lem6916136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6916137 (x : int) : (term275 x) = (term276 x).
Proof. exact (MK_COMB (@lem6916136) (@lem6916135 x)). Qed.
Lemma lem6916138 (x : int) (y : int) : (term270 x y) = (term257 x y).
Proof. exact (eq_refl (term270 x y)). Qed.
Lemma lem6916139 (x : int) : (term277 x) = (term268 x).
Proof. exact (fun_ext (fun y : int => @lem6916138 x y)). Qed.
Lemma lem6916140 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916141 (x : int) : (term278 x) = (term279 x).
Proof. exact (MK_COMB (@lem6916140) (@lem6916139 x)). Qed.
Lemma lem6916142 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916143 (x : int) : (term280 x) = (term281 x).
Proof. exact (MK_COMB (@lem6916142) (@lem6916141 x)). Qed.
Lemma lem6916144 (x : int) (y : int) : (term272 x y) = (term262 x y).
Proof. exact (eq_refl (term272 x y)). Qed.
Lemma lem6916145 (x : int) : (term282 x) = (term269 x).
Proof. exact (fun_ext (fun y : int => @lem6916144 x y)). Qed.
Lemma lem6916146 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916147 (x : int) : (term283 x) = (term284 x).
Proof. exact (MK_COMB (@lem6916146) (@lem6916145 x)). Qed.
Lemma lem6916148 (x : int) : (term267 x) = (term285 x).
Proof. exact (MK_COMB (@lem6916143 x) (@lem6916147 x)). Qed.
Lemma lem6916149 (x : int) : ((term266 x) = (term267 x)) = ((term265 x) = (term285 x)).
Proof. exact (MK_COMB (@lem6916137 x) (@lem6916148 x)). Qed.
Lemma lem6916150 (x : int) : (term265 x) = (term285 x).
Proof. exact (EQ_MP (@lem6916149 x) (@lem6916127 x)). Qed.
Lemma lem6916169 (x : int) : (term155 x) = (term285 x).
Proof. exact (TRANS (@lem6916123 x) (@lem6916150 x)). Qed.
Lemma lem6916170 : term156 = term286.
Proof. exact (fun_ext (fun x : int => @lem6916169 x)). Qed.
Lemma lem6916171 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916172 : term157 = term287.
Proof. exact (MK_COMB (@lem6916171) (@lem6916170)). Qed.
Lemma lem6916174 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem6916175 (P : int -> Prop) (Q : int -> Prop) : (term199 P Q) = (term200 P Q).
Proof. exact (@lem6916174 int P Q). Qed.
Lemma lem6916176 : term288 = term289.
Proof. exact (@lem6916175 term290 term291). Qed.
Lemma lem6916177 (x : int) : (term292 x) = (term279 x).
Proof. exact (eq_refl (term292 x)). Qed.
Lemma lem6916178 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916179 (x : int) : (term293 x) = (term281 x).
Proof. exact (MK_COMB (@lem6916178) (@lem6916177 x)). Qed.
Lemma lem6916180 (x : int) : (term294 x) = (term284 x).
Proof. exact (eq_refl (term294 x)). Qed.
Lemma lem6916181 (x : int) : (term295 x) = (term285 x).
Proof. exact (MK_COMB (@lem6916179 x) (@lem6916180 x)). Qed.
Lemma lem6916182 : term296 = term286.
Proof. exact (fun_ext (fun x : int => @lem6916181 x)). Qed.
Lemma lem6916183 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916184 : term288 = term287.
Proof. exact (MK_COMB (@lem6916183) (@lem6916182)). Qed.
Lemma lem6916185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6916186 : term297 = term298.
Proof. exact (MK_COMB (@lem6916185) (@lem6916184)). Qed.
Lemma lem6916187 (x : int) : (term292 x) = (term279 x).
Proof. exact (eq_refl (term292 x)). Qed.
Lemma lem6916188 : term299 = term290.
Proof. exact (fun_ext (fun x : int => @lem6916187 x)). Qed.
Lemma lem6916189 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916190 : term300 = term301.
Proof. exact (MK_COMB (@lem6916189) (@lem6916188)). Qed.
Lemma lem6916191 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916192 : term302 = term303.
Proof. exact (MK_COMB (@lem6916191) (@lem6916190)). Qed.
Lemma lem6916193 (x : int) : (term294 x) = (term284 x).
Proof. exact (eq_refl (term294 x)). Qed.
Lemma lem6916194 : term304 = term291.
Proof. exact (fun_ext (fun x : int => @lem6916193 x)). Qed.
Lemma lem6916195 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916196 : term305 = term306.
Proof. exact (MK_COMB (@lem6916195) (@lem6916194)). Qed.
Lemma lem6916197 : term289 = term307.
Proof. exact (MK_COMB (@lem6916192) (@lem6916196)). Qed.
Lemma lem6916198 : (term288 = term289) = (term287 = term307).
Proof. exact (MK_COMB (@lem6916186) (@lem6916197)). Qed.
Lemma lem6916199 : term287 = term307.
Proof. exact (EQ_MP (@lem6916198) (@lem6916176)). Qed.
Lemma lem6916226 : term157 = term307.
Proof. exact (TRANS (@lem6916172) (@lem6916199)). Qed.
Lemma lem6916227 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916228 : term191 = term308.
Proof. exact (MK_COMB (@lem6916227) (@lem6916226)). Qed.
Lemma lem6916230 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem6916231 (P : int -> Prop) (Q : int -> Prop) : (term199 P Q) = (term200 P Q).
Proof. exact (@lem6916230 int P Q). Qed.
Lemma lem6916232 : term309 = term310.
Proof. exact (@lem6916231 term311 term312). Qed.
Lemma lem6916233 (x : int) : (term313 x) = (term176 x).
Proof. exact (eq_refl (term313 x)). Qed.
Lemma lem6916234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916235 (x : int) : (term314 x) = (term178 x).
Proof. exact (MK_COMB (@lem6916234) (@lem6916233 x)). Qed.
Lemma lem6916236 (x : int) : (term315 x) = (term187 x).
Proof. exact (eq_refl (term315 x)). Qed.
Lemma lem6916237 (x : int) : (term316 x) = (term188 x).
Proof. exact (MK_COMB (@lem6916235 x) (@lem6916236 x)). Qed.
Lemma lem6916238 : term317 = term189.
Proof. exact (fun_ext (fun x : int => @lem6916237 x)). Qed.
Lemma lem6916239 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916240 : term309 = term190.
Proof. exact (MK_COMB (@lem6916239) (@lem6916238)). Qed.
Lemma lem6916241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6916242 : term318 = term319.
Proof. exact (MK_COMB (@lem6916241) (@lem6916240)). Qed.
Lemma lem6916243 (x : int) : (term313 x) = (term176 x).
Proof. exact (eq_refl (term313 x)). Qed.
Lemma lem6916244 : term320 = term311.
Proof. exact (fun_ext (fun x : int => @lem6916243 x)). Qed.
Lemma lem6916245 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916246 : term321 = term322.
Proof. exact (MK_COMB (@lem6916245) (@lem6916244)). Qed.
Lemma lem6916247 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916248 : term323 = term324.
Proof. exact (MK_COMB (@lem6916247) (@lem6916246)). Qed.
Lemma lem6916249 (x : int) : (term315 x) = (term187 x).
Proof. exact (eq_refl (term315 x)). Qed.
Lemma lem6916250 : term325 = term312.
Proof. exact (fun_ext (fun x : int => @lem6916249 x)). Qed.
Lemma lem6916251 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916252 : term326 = term327.
Proof. exact (MK_COMB (@lem6916251) (@lem6916250)). Qed.
Lemma lem6916253 : term310 = term328.
Proof. exact (MK_COMB (@lem6916248) (@lem6916252)). Qed.
Lemma lem6916254 : (term309 = term310) = (term190 = term328).
Proof. exact (MK_COMB (@lem6916242) (@lem6916253)). Qed.
Lemma lem6916255 : term190 = term328.
Proof. exact (EQ_MP (@lem6916254) (@lem6916232)). Qed.
Lemma lem6916266 : term192 = term329.
Proof. exact (MK_COMB (@lem6916228) (@lem6916255)). Qed.
Lemma lem6916269 : term194 = term330.
Proof. exact (MK_COMB (@lem6916073) (@lem6916266)). Qed.
Lemma lem6916273 : term196 = term330.
Proof. exact (TRANS (@lem6915979) (@lem6916269)). Qed.
Lemma lem6916274 (y : int) (x : int) : (term111 y x) = (term111 y x).
Proof. exact (eq_refl (term111 y x)). Qed.
Lemma lem6916275 (x : int) : (term203 x) = (term203 x).
Proof. exact (fun_ext (fun y : int => @lem6916274 y x)). Qed.
Lemma lem6916276 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916277 (x : int) : (term214 x) = (term214 x).
Proof. exact (MK_COMB (@lem6916276) (@lem6916275 x)). Qed.
Lemma lem6916278 : term225 = term225.
Proof. exact (fun_ext (fun x : int => @lem6916277 x)). Qed.
Lemma lem6916279 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916280 : term236 = term236.
Proof. exact (MK_COMB (@lem6916279) (@lem6916278)). Qed.
Lemma lem6916281 (x : int) (y : int) : (term111 x y) = (term111 x y).
Proof. exact (eq_refl (term111 x y)). Qed.
Lemma lem6916282 (x : int) : (term204 x) = (term204 x).
Proof. exact (fun_ext (fun y : int => @lem6916281 x y)). Qed.
Lemma lem6916283 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916284 (x : int) : (term219 x) = (term219 x).
Proof. exact (MK_COMB (@lem6916283) (@lem6916282 x)). Qed.
Lemma lem6916285 : term226 = term226.
Proof. exact (fun_ext (fun x : int => @lem6916284 x)). Qed.
Lemma lem6916286 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916287 : term241 = term241.
Proof. exact (MK_COMB (@lem6916286) (@lem6916285)). Qed.
Lemma lem6916288 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916289 : term238 = term238.
Proof. exact (MK_COMB (@lem6916288) (@lem6916280)). Qed.
Lemma lem6916290 : term242 = term242.
Proof. exact (MK_COMB (@lem6916289) (@lem6916287)). Qed.
Lemma lem6916291 (x : int) (y : int) (z : int) : (term137 x y z) = (term137 x y z).
Proof. exact (eq_refl (term137 x y z)). Qed.
Lemma lem6916292 (x : int) (y : int) : (term246 x y) = (term246 x y).
Proof. exact (fun_ext (fun z : int => @lem6916291 x y z)). Qed.
Lemma lem6916293 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916294 (x : int) (y : int) : (term257 x y) = (term257 x y).
Proof. exact (MK_COMB (@lem6916293) (@lem6916292 x y)). Qed.
Lemma lem6916295 (x : int) : (term268 x) = (term268 x).
Proof. exact (fun_ext (fun y : int => @lem6916294 x y)). Qed.
Lemma lem6916296 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916297 (x : int) : (term279 x) = (term279 x).
Proof. exact (MK_COMB (@lem6916296) (@lem6916295 x)). Qed.
Lemma lem6916298 : term290 = term290.
Proof. exact (fun_ext (fun x : int => @lem6916297 x)). Qed.
Lemma lem6916299 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916300 : term301 = term301.
Proof. exact (MK_COMB (@lem6916299) (@lem6916298)). Qed.
Lemma lem6916301 (x : int) (y : int) (z : int) : (term150 x y z) = (term150 x y z).
Proof. exact (eq_refl (term150 x y z)). Qed.
Lemma lem6916302 (x : int) (y : int) : (term247 x y) = (term247 x y).
Proof. exact (fun_ext (fun z : int => @lem6916301 x y z)). Qed.
Lemma lem6916303 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916304 (x : int) (y : int) : (term262 x y) = (term262 x y).
Proof. exact (MK_COMB (@lem6916303) (@lem6916302 x y)). Qed.
Lemma lem6916305 (x : int) : (term269 x) = (term269 x).
Proof. exact (fun_ext (fun y : int => @lem6916304 x y)). Qed.
Lemma lem6916306 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916307 (x : int) : (term284 x) = (term284 x).
Proof. exact (MK_COMB (@lem6916306) (@lem6916305 x)). Qed.
Lemma lem6916308 : term291 = term291.
Proof. exact (fun_ext (fun x : int => @lem6916307 x)). Qed.
Lemma lem6916309 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916310 : term306 = term306.
Proof. exact (MK_COMB (@lem6916309) (@lem6916308)). Qed.
Lemma lem6916311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916312 : term303 = term303.
Proof. exact (MK_COMB (@lem6916311) (@lem6916300)). Qed.
Lemma lem6916313 : term307 = term307.
Proof. exact (MK_COMB (@lem6916312) (@lem6916310)). Qed.
Lemma lem6916314 (x : int) : (term176 x) = (term176 x).
Proof. exact (eq_refl (term176 x)). Qed.
Lemma lem6916315 : term311 = term311.
Proof. exact (fun_ext (fun x : int => @lem6916314 x)). Qed.
Lemma lem6916316 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916317 : term322 = term322.
Proof. exact (MK_COMB (@lem6916316) (@lem6916315)). Qed.
Lemma lem6916318 (x : int) : (term187 x) = (term187 x).
Proof. exact (eq_refl (term187 x)). Qed.
Lemma lem6916319 : term312 = term312.
Proof. exact (fun_ext (fun x : int => @lem6916318 x)). Qed.
Lemma lem6916320 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916321 : term327 = term327.
Proof. exact (MK_COMB (@lem6916320) (@lem6916319)). Qed.
Lemma lem6916322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916323 : term324 = term324.
Proof. exact (MK_COMB (@lem6916322) (@lem6916317)). Qed.
Lemma lem6916324 : term328 = term328.
Proof. exact (MK_COMB (@lem6916323) (@lem6916321)). Qed.
Lemma lem6916325 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916326 : term308 = term308.
Proof. exact (MK_COMB (@lem6916325) (@lem6916313)). Qed.
Lemma lem6916327 : term329 = term329.
Proof. exact (MK_COMB (@lem6916326) (@lem6916324)). Qed.
Lemma lem6916328 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916329 : term243 = term243.
Proof. exact (MK_COMB (@lem6916328) (@lem6916290)). Qed.
Lemma lem6916330 : term330 = term330.
Proof. exact (MK_COMB (@lem6916329) (@lem6916327)). Qed.
Lemma lem6916331 : term196 = term330.
Proof. exact (TRANS (@lem6916273) (@lem6916330)). Qed.
Lemma lem6916332 (y : int) (x : int) : (term111 y x) = (term111 y x).
Proof. exact (eq_refl (term111 y x)). Qed.
Lemma lem6916333 (x : int) : (term203 x) = (term203 x).
Proof. exact (fun_ext (fun y : int => @lem6916332 y x)). Qed.
Lemma lem6916334 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916335 (x : int) : (term214 x) = (term214 x).
Proof. exact (MK_COMB (@lem6916334) (@lem6916333 x)). Qed.
Lemma lem6916336 : term225 = term225.
Proof. exact (fun_ext (fun x : int => @lem6916335 x)). Qed.
Lemma lem6916337 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916338 : term236 = term236.
Proof. exact (MK_COMB (@lem6916337) (@lem6916336)). Qed.
Lemma lem6916339 (x : int) (y : int) : (term111 x y) = (term111 x y).
Proof. exact (eq_refl (term111 x y)). Qed.
Lemma lem6916340 (x : int) : (term204 x) = (term204 x).
Proof. exact (fun_ext (fun y : int => @lem6916339 x y)). Qed.
Lemma lem6916341 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916342 (x : int) : (term219 x) = (term219 x).
Proof. exact (MK_COMB (@lem6916341) (@lem6916340 x)). Qed.
Lemma lem6916343 : term226 = term226.
Proof. exact (fun_ext (fun x : int => @lem6916342 x)). Qed.
Lemma lem6916344 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916345 : term241 = term241.
Proof. exact (MK_COMB (@lem6916344) (@lem6916343)). Qed.
Lemma lem6916346 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916347 : term238 = term238.
Proof. exact (MK_COMB (@lem6916346) (@lem6916338)). Qed.
Lemma lem6916348 : term242 = term242.
Proof. exact (MK_COMB (@lem6916347) (@lem6916345)). Qed.
Lemma lem6916349 (x : int) (y : int) (z : int) : (term137 x y z) = (term137 x y z).
Proof. exact (eq_refl (term137 x y z)). Qed.
Lemma lem6916350 (x : int) (y : int) : (term246 x y) = (term246 x y).
Proof. exact (fun_ext (fun z : int => @lem6916349 x y z)). Qed.
Lemma lem6916351 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916352 (x : int) (y : int) : (term257 x y) = (term257 x y).
Proof. exact (MK_COMB (@lem6916351) (@lem6916350 x y)). Qed.
Lemma lem6916353 (x : int) : (term268 x) = (term268 x).
Proof. exact (fun_ext (fun y : int => @lem6916352 x y)). Qed.
Lemma lem6916354 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916355 (x : int) : (term279 x) = (term279 x).
Proof. exact (MK_COMB (@lem6916354) (@lem6916353 x)). Qed.
Lemma lem6916356 : term290 = term290.
Proof. exact (fun_ext (fun x : int => @lem6916355 x)). Qed.
Lemma lem6916357 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916358 : term301 = term301.
Proof. exact (MK_COMB (@lem6916357) (@lem6916356)). Qed.
Lemma lem6916359 (x : int) (y : int) (z : int) : (term150 x y z) = (term150 x y z).
Proof. exact (eq_refl (term150 x y z)). Qed.
Lemma lem6916360 (x : int) (y : int) : (term247 x y) = (term247 x y).
Proof. exact (fun_ext (fun z : int => @lem6916359 x y z)). Qed.
Lemma lem6916361 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916362 (x : int) (y : int) : (term262 x y) = (term262 x y).
Proof. exact (MK_COMB (@lem6916361) (@lem6916360 x y)). Qed.
Lemma lem6916363 (x : int) : (term269 x) = (term269 x).
Proof. exact (fun_ext (fun y : int => @lem6916362 x y)). Qed.
Lemma lem6916364 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916365 (x : int) : (term284 x) = (term284 x).
Proof. exact (MK_COMB (@lem6916364) (@lem6916363 x)). Qed.
Lemma lem6916366 : term291 = term291.
Proof. exact (fun_ext (fun x : int => @lem6916365 x)). Qed.
Lemma lem6916367 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916368 : term306 = term306.
Proof. exact (MK_COMB (@lem6916367) (@lem6916366)). Qed.
Lemma lem6916369 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916370 : term303 = term303.
Proof. exact (MK_COMB (@lem6916369) (@lem6916358)). Qed.
Lemma lem6916371 : term307 = term307.
Proof. exact (MK_COMB (@lem6916370) (@lem6916368)). Qed.
Lemma lem6916372 (x : int) : (term176 x) = (term176 x).
Proof. exact (eq_refl (term176 x)). Qed.
Lemma lem6916373 : term311 = term311.
Proof. exact (fun_ext (fun x : int => @lem6916372 x)). Qed.
Lemma lem6916374 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916375 : term322 = term322.
Proof. exact (MK_COMB (@lem6916374) (@lem6916373)). Qed.
Lemma lem6916376 (x : int) : (term187 x) = (term187 x).
Proof. exact (eq_refl (term187 x)). Qed.
Lemma lem6916377 : term312 = term312.
Proof. exact (fun_ext (fun x : int => @lem6916376 x)). Qed.
Lemma lem6916378 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916379 : term327 = term327.
Proof. exact (MK_COMB (@lem6916378) (@lem6916377)). Qed.
Lemma lem6916380 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916381 : term324 = term324.
Proof. exact (MK_COMB (@lem6916380) (@lem6916375)). Qed.
Lemma lem6916382 : term328 = term328.
Proof. exact (MK_COMB (@lem6916381) (@lem6916379)). Qed.
Lemma lem6916383 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916384 : term308 = term308.
Proof. exact (MK_COMB (@lem6916383) (@lem6916371)). Qed.
Lemma lem6916385 : term329 = term329.
Proof. exact (MK_COMB (@lem6916384) (@lem6916382)). Qed.
Lemma lem6916386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6916387 : term243 = term243.
Proof. exact (MK_COMB (@lem6916386) (@lem6916348)). Qed.
Lemma lem6916388 : term330 = term330.
Proof. exact (MK_COMB (@lem6916387) (@lem6916385)). Qed.
Lemma lem6916389 : term196 = term330.
Proof. exact (TRANS (@lem6916331) (@lem6916388)). Qed.
Lemma lem6916390 (x : int) (y : int) : (term111 y x) = (term331 x y).
Proof. exact (@lem1988287 (term98 y x) (term108 x y)). Qed.
Lemma lem6916407 (x : int) (y : int) : (term108 x y) = (term332 x y).
Proof. exact (@lem1982755 (real_of_int x) (real_of_int y) term106). Qed.
Lemma lem6916414 (x : int) (y : int) : (term98 y x) = (term98 x y).
Proof. exact (@lem1982761 (real_of_int x) (real_of_int y)). Qed.
Lemma lem6916415 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem6916416 (x : int) (y : int) : (term333 y x) = (term333 x y).
Proof. exact (MK_COMB (@lem6916415) (@lem6916414 x y)). Qed.
Lemma lem6916417 (x : int) (y : int) : (term334 x y) = (term335 x y).
Proof. exact (MK_COMB (@lem6916416 x y) (@lem6916407 x y)). Qed.
Lemma lem6916418 (x : int) (y : int) : (term335 x y) = (term336 x y).
Proof. exact (@lem1982792 (term98 x y) (term332 x y)). Qed.
Lemma lem6916419 (x : int) (y : int) : (term337 x y) = (term338 x y).
Proof. exact (@lem1982781 (real_of_int x) term339 (term184 y)). Qed.
Lemma lem6916420 (y : int) : (term340 y) = (term341 y).
Proof. exact (@lem1982781 (real_of_int y) term339 term106). Qed.
Lemma lem6916422 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6916423 : term106 = term343.
Proof. exact (@lem6916422 term107). Qed.
Lemma lem6916425 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6916426 : term339 = term346.
Proof. exact (@lem6916425 term107). Qed.
Lemma lem6916427 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6916428 : term347 = term348.
Proof. exact (MK_COMB (@lem6916427) (@lem6916426)). Qed.
Lemma lem6916429 : term349 = term350.
Proof. exact (MK_COMB (@lem6916428) (@lem6916423)). Qed.
Lemma lem6916430 : term350 = term351.
Proof. exact (@lem1981613 term339 term106 term106 term106). Qed.
Lemma lem6916432 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6916433 : term354 = term355.
Proof. exact (@lem6916432 term107 term107). Qed.
Lemma lem6916434 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6916435 : term357 = term107.
Proof. exact (EQ_MP (@lem6916434) (@lem940073)). Qed.
Lemma lem6916436 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6916437 : term355 = term106.
Proof. exact (MK_COMB (@lem6916436) (@lem6916435)). Qed.
Lemma lem6916438 : term354 = term106.
Proof. exact (TRANS (@lem6916433) (@lem6916437)). Qed.
Lemma lem6916440 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6916441 : term349 = term360.
Proof. exact (@lem6916440 term107 term107). Qed.
Lemma lem6916442 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6916443 : term357 = term107.
Proof. exact (EQ_MP (@lem6916442) (@lem940073)). Qed.
Lemma lem6916444 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6916445 : term355 = term106.
Proof. exact (MK_COMB (@lem6916444) (@lem6916443)). Qed.
Lemma lem6916446 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6916447 : term360 = term339.
Proof. exact (MK_COMB (@lem6916446) (@lem6916445)). Qed.
Lemma lem6916448 : term349 = term339.
Proof. exact (TRANS (@lem6916441) (@lem6916447)). Qed.
Lemma lem6916449 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6916450 : term361 = term362.
Proof. exact (MK_COMB (@lem6916449) (@lem6916448)). Qed.
Lemma lem6916451 : term351 = term346.
Proof. exact (MK_COMB (@lem6916450) (@lem6916438)). Qed.
Lemma lem6916452 : term350 = term346.
Proof. exact (TRANS (@lem6916430) (@lem6916451)). Qed.
Lemma lem6916453 : term349 = term346.
Proof. exact (TRANS (@lem6916429) (@lem6916452)). Qed.
Lemma lem6916455 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6916456 : term346 = term339.
Proof. exact (@lem6916455 term339). Qed.
Lemma lem6916457 : term349 = term339.
Proof. exact (TRANS (@lem6916453) (@lem6916456)). Qed.
Lemma lem6916460 (y : int) : (term364 y) = (term364 y).
Proof. exact (eq_refl (term364 y)). Qed.
Lemma lem6916461 (y : int) : (term341 y) = (term365 y).
Proof. exact (MK_COMB (@lem6916460 y) (@lem6916457)). Qed.
Lemma lem6916462 (y : int) : (term340 y) = (term365 y).
Proof. exact (TRANS (@lem6916420 y) (@lem6916461 y)). Qed.
Lemma lem6916465 (x : int) : (term364 x) = (term364 x).
Proof. exact (eq_refl (term364 x)). Qed.
Lemma lem6916466 (x : int) (y : int) : (term338 x y) = (term366 x y).
Proof. exact (MK_COMB (@lem6916465 x) (@lem6916462 y)). Qed.
Lemma lem6916467 (x : int) (y : int) : (term337 x y) = (term366 x y).
Proof. exact (TRANS (@lem6916419 x y) (@lem6916466 x y)). Qed.
Lemma lem6916468 (x : int) (y : int) : (term103 x y) = (term103 x y).
Proof. exact (eq_refl (term103 x y)). Qed.
Lemma lem6916469 (x : int) (y : int) : (term336 x y) = (term367 x y).
Proof. exact (MK_COMB (@lem6916468 x y) (@lem6916467 x y)). Qed.
Lemma lem6916470 (x : int) (y : int) : (term367 x y) = (term368 x y).
Proof. exact (@lem1982753 (real_of_int x) (term369 x) (real_of_int y) (term365 y)). Qed.
Lemma lem6916471 (x : int) : (term370 x) = (term371 x).
Proof. exact (@lem1982715 term339 (real_of_int x)). Qed.
Lemma lem6916473 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6916474 : term106 = term343.
Proof. exact (@lem6916473 term107). Qed.
Lemma lem6916476 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6916477 : term339 = term346.
Proof. exact (@lem6916476 term107). Qed.
Lemma lem6916478 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6916479 : term372 = term373.
Proof. exact (MK_COMB (@lem6916478) (@lem6916477)). Qed.
Lemma lem6916480 : term374 = term375.
Proof. exact (MK_COMB (@lem6916479) (@lem6916474)). Qed.
Lemma lem6916481 : term376.
Proof. exact (@lem1981473 term339 term106 term106 term106 term167 term106). Qed.
Lemma lem6916483 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6916484 : term378 = term379.
Proof. exact (@lem6916483 (NUMERAL 0) term107). Qed.
Lemma lem6916485 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6916486 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6916487 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6916486 h1) (fun h1 : term379 = True => @lem6916485)). Qed.
Lemma lem6916488 : term379 = True.
Proof. exact (EQ_MP (@lem6916487) (@lem6916485)). Qed.
Lemma lem6916489 : term378 = True.
Proof. exact (TRANS (@lem6916484) (@lem6916488)). Qed.
Lemma lem6916490 : True = term378.
Proof. exact (SYM (@lem6916489)). Qed.
Lemma lem6916491 : term378.
Proof. exact (EQ_MP (@lem6916490) (@lem0)). Qed.
Lemma lem6916492 : term381.
Proof. exact (@lem6916481 (@lem6916491)). Qed.
Lemma lem6916494 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6916495 : term378 = term379.
Proof. exact (@lem6916494 (NUMERAL 0) term107). Qed.
Lemma lem6916496 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6916497 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6916498 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6916497 h1) (fun h1 : term379 = True => @lem6916496)). Qed.
Lemma lem6916499 : term379 = True.
Proof. exact (EQ_MP (@lem6916498) (@lem6916496)). Qed.
Lemma lem6916500 : term378 = True.
Proof. exact (TRANS (@lem6916495) (@lem6916499)). Qed.
Lemma lem6916501 : True = term378.
Proof. exact (SYM (@lem6916500)). Qed.
Lemma lem6916502 : term378.
Proof. exact (EQ_MP (@lem6916501) (@lem0)). Qed.
Lemma lem6916503 : term382.
Proof. exact (@lem6916492 (@lem6916502)). Qed.
Lemma lem6916505 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6916506 : term378 = term379.
Proof. exact (@lem6916505 (NUMERAL 0) term107). Qed.
Lemma lem6916507 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6916508 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6916509 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6916508 h1) (fun h1 : term379 = True => @lem6916507)). Qed.
Lemma lem6916510 : term379 = True.
Proof. exact (EQ_MP (@lem6916509) (@lem6916507)). Qed.
Lemma lem6916511 : term378 = True.
Proof. exact (TRANS (@lem6916506) (@lem6916510)). Qed.
Lemma lem6916512 : True = term378.
Proof. exact (SYM (@lem6916511)). Qed.
Lemma lem6916513 : term378.
Proof. exact (EQ_MP (@lem6916512) (@lem0)). Qed.
Lemma lem6916514 : term383.
Proof. exact (@lem6916503 (@lem6916513)). Qed.
Lemma lem6916516 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6916517 : term354 = term355.
Proof. exact (@lem6916516 term107 term107). Qed.
Lemma lem6916518 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6916519 : term357 = term107.
Proof. exact (EQ_MP (@lem6916518) (@lem940073)). Qed.
Lemma lem6916520 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6916521 : term355 = term106.
Proof. exact (MK_COMB (@lem6916520) (@lem6916519)). Qed.
Lemma lem6916522 : term354 = term106.
Proof. exact (TRANS (@lem6916517) (@lem6916521)). Qed.
Lemma lem6916524 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6916525 : term349 = term360.
Proof. exact (@lem6916524 term107 term107). Qed.
Lemma lem6916526 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6916527 : term357 = term107.
Proof. exact (EQ_MP (@lem6916526) (@lem940073)). Qed.
Lemma lem6916528 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6916529 : term355 = term106.
Proof. exact (MK_COMB (@lem6916528) (@lem6916527)). Qed.
Lemma lem6916530 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6916531 : term360 = term339.
Proof. exact (MK_COMB (@lem6916530) (@lem6916529)). Qed.
Lemma lem6916532 : term349 = term339.
Proof. exact (TRANS (@lem6916525) (@lem6916531)). Qed.
Lemma lem6916533 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6916534 : term384 = term372.
Proof. exact (MK_COMB (@lem6916533) (@lem6916532)). Qed.
Lemma lem6916535 : term385 = term374.
Proof. exact (MK_COMB (@lem6916534) (@lem6916522)). Qed.
Lemma lem6916537 (m : nat) : (term386 m) = term167.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6916538 : term374 = term167.
Proof. exact (@lem6916537 term107). Qed.
Lemma lem6916539 : term385 = term167.
Proof. exact (TRANS (@lem6916535) (@lem6916538)). Qed.
Lemma lem6916540 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6916541 : term387 = term388.
Proof. exact (MK_COMB (@lem6916540) (@lem6916539)). Qed.
Lemma lem6916542 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem6916543 : term389 = term390.
Proof. exact (MK_COMB (@lem6916541) (@lem6916542)). Qed.
Lemma lem6916545 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6916546 : term390 = term167.
Proof. exact (@lem6916545 term107). Qed.
Lemma lem6916547 : term389 = term167.
Proof. exact (TRANS (@lem6916543) (@lem6916546)). Qed.
Lemma lem6916549 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6916550 : term354 = term355.
Proof. exact (@lem6916549 term107 term107). Qed.
Lemma lem6916551 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6916552 : term357 = term107.
Proof. exact (EQ_MP (@lem6916551) (@lem940073)). Qed.
Lemma lem6916553 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6916554 : term355 = term106.
Proof. exact (MK_COMB (@lem6916553) (@lem6916552)). Qed.
Lemma lem6916555 : term354 = term106.
Proof. exact (TRANS (@lem6916550) (@lem6916554)). Qed.
Lemma lem6916556 : term388 = term388.
Proof. exact (eq_refl term388). Qed.
Lemma lem6916557 : term392 = term390.
Proof. exact (MK_COMB (@lem6916556) (@lem6916555)). Qed.
Lemma lem6916559 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6916560 : term390 = term167.
Proof. exact (@lem6916559 term107). Qed.
Lemma lem6916561 : term392 = term167.
Proof. exact (TRANS (@lem6916557) (@lem6916560)). Qed.
Lemma lem6916562 : term167 = term392.
Proof. exact (SYM (@lem6916561)). Qed.
Lemma lem6916563 : term389 = term392.
Proof. exact (TRANS (@lem6916547) (@lem6916562)). Qed.
Lemma lem6916564 : term375 = term393.
Proof. exact (@lem6916514 (@lem6916563)). Qed.
Lemma lem6916565 : term374 = term393.
Proof. exact (TRANS (@lem6916480) (@lem6916564)). Qed.
Lemma lem6916567 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6916568 : term393 = term167.
Proof. exact (@lem6916567 term167). Qed.
Lemma lem6916569 : term374 = term167.
Proof. exact (TRANS (@lem6916565) (@lem6916568)). Qed.
Lemma lem6916570 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6916571 : term394 = term388.
Proof. exact (MK_COMB (@lem6916570) (@lem6916569)). Qed.
Lemma lem6916572 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem6916573 (x : int) : (term371 x) = (term395 x).
Proof. exact (MK_COMB (@lem6916571) (@lem6916572 x)). Qed.
Lemma lem6916574 (x : int) : (term370 x) = (term395 x).
Proof. exact (TRANS (@lem6916471 x) (@lem6916573 x)). Qed.
Lemma lem6916575 (x : int) : (term395 x) = term167.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem6916576 (x : int) : (term370 x) = term167.
Proof. exact (TRANS (@lem6916574 x) (@lem6916575 x)). Qed.
Lemma lem6916577 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6916578 (x : int) : (term396 x) = term169.
Proof. exact (MK_COMB (@lem6916577) (@lem6916576 x)). Qed.
Lemma lem6916579 (y : int) : (term397 y) = (term398 y).
Proof. exact (@lem1982763 (real_of_int y) (term369 y) term339). Qed.
Lemma lem6916580 (y : int) : (term370 y) = (term371 y).
Proof. exact (@lem1982715 term339 (real_of_int y)). Qed.
Lemma lem6916582 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6916583 : term106 = term343.
Proof. exact (@lem6916582 term107). Qed.
Lemma lem6916585 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6916586 : term339 = term346.
Proof. exact (@lem6916585 term107). Qed.
Lemma lem6916587 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6916588 : term372 = term373.
Proof. exact (MK_COMB (@lem6916587) (@lem6916586)). Qed.
Lemma lem6916589 : term374 = term375.
Proof. exact (MK_COMB (@lem6916588) (@lem6916583)). Qed.
Lemma lem6916590 : term376.
Proof. exact (@lem1981473 term339 term106 term106 term106 term167 term106). Qed.
Lemma lem6916592 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6916593 : term378 = term379.
Proof. exact (@lem6916592 (NUMERAL 0) term107). Qed.
Lemma lem6916594 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6916595 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6916596 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6916595 h1) (fun h1 : term379 = True => @lem6916594)). Qed.
Lemma lem6916597 : term379 = True.
Proof. exact (EQ_MP (@lem6916596) (@lem6916594)). Qed.
Lemma lem6916598 : term378 = True.
Proof. exact (TRANS (@lem6916593) (@lem6916597)). Qed.
Lemma lem6916599 : True = term378.
Proof. exact (SYM (@lem6916598)). Qed.
Lemma lem6916600 : term378.
Proof. exact (EQ_MP (@lem6916599) (@lem0)). Qed.
Lemma lem6916601 : term381.
Proof. exact (@lem6916590 (@lem6916600)). Qed.
Lemma lem6916603 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6916604 : term378 = term379.
Proof. exact (@lem6916603 (NUMERAL 0) term107). Qed.
Lemma lem6916605 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6916606 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6916607 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6916606 h1) (fun h1 : term379 = True => @lem6916605)). Qed.
Lemma lem6916608 : term379 = True.
Proof. exact (EQ_MP (@lem6916607) (@lem6916605)). Qed.
Lemma lem6916609 : term378 = True.
Proof. exact (TRANS (@lem6916604) (@lem6916608)). Qed.
Lemma lem6916610 : True = term378.
Proof. exact (SYM (@lem6916609)). Qed.
Lemma lem6916611 : term378.
Proof. exact (EQ_MP (@lem6916610) (@lem0)). Qed.
Lemma lem6916612 : term382.
Proof. exact (@lem6916601 (@lem6916611)). Qed.
Lemma lem6916614 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6916615 : term378 = term379.
Proof. exact (@lem6916614 (NUMERAL 0) term107). Qed.
Lemma lem6916616 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6916617 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6916618 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6916617 h1) (fun h1 : term379 = True => @lem6916616)). Qed.
Lemma lem6916619 : term379 = True.
Proof. exact (EQ_MP (@lem6916618) (@lem6916616)). Qed.
Lemma lem6916620 : term378 = True.
Proof. exact (TRANS (@lem6916615) (@lem6916619)). Qed.
Lemma lem6916621 : True = term378.
Proof. exact (SYM (@lem6916620)). Qed.
Lemma lem6916622 : term378.
Proof. exact (EQ_MP (@lem6916621) (@lem0)). Qed.
Lemma lem6916623 : term383.
Proof. exact (@lem6916612 (@lem6916622)). Qed.
Lemma lem6916625 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6916626 : term354 = term355.
Proof. exact (@lem6916625 term107 term107). Qed.
Lemma lem6916627 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6916628 : term357 = term107.
Proof. exact (EQ_MP (@lem6916627) (@lem940073)). Qed.
Lemma lem6916629 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6916630 : term355 = term106.
Proof. exact (MK_COMB (@lem6916629) (@lem6916628)). Qed.
Lemma lem6916631 : term354 = term106.
Proof. exact (TRANS (@lem6916626) (@lem6916630)). Qed.
Lemma lem6916633 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6916634 : term349 = term360.
Proof. exact (@lem6916633 term107 term107). Qed.
Lemma lem6916635 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6916636 : term357 = term107.
Proof. exact (EQ_MP (@lem6916635) (@lem940073)). Qed.
Lemma lem6916637 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6916638 : term355 = term106.
Proof. exact (MK_COMB (@lem6916637) (@lem6916636)). Qed.
Lemma lem6916639 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6916640 : term360 = term339.
Proof. exact (MK_COMB (@lem6916639) (@lem6916638)). Qed.
Lemma lem6916641 : term349 = term339.
Proof. exact (TRANS (@lem6916634) (@lem6916640)). Qed.
Lemma lem6916642 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6916643 : term384 = term372.
Proof. exact (MK_COMB (@lem6916642) (@lem6916641)). Qed.
Lemma lem6916644 : term385 = term374.
Proof. exact (MK_COMB (@lem6916643) (@lem6916631)). Qed.
Lemma lem6916646 (m : nat) : (term386 m) = term167.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6916647 : term374 = term167.
Proof. exact (@lem6916646 term107). Qed.
Lemma lem6916648 : term385 = term167.
Proof. exact (TRANS (@lem6916644) (@lem6916647)). Qed.
Lemma lem6916649 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6916650 : term387 = term388.
Proof. exact (MK_COMB (@lem6916649) (@lem6916648)). Qed.
Lemma lem6916651 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem6916652 : term389 = term390.
Proof. exact (MK_COMB (@lem6916650) (@lem6916651)). Qed.
Lemma lem6916654 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6916655 : term390 = term167.
Proof. exact (@lem6916654 term107). Qed.
Lemma lem6916656 : term389 = term167.
Proof. exact (TRANS (@lem6916652) (@lem6916655)). Qed.
Lemma lem6916658 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6916659 : term354 = term355.
Proof. exact (@lem6916658 term107 term107). Qed.
Lemma lem6916660 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6916661 : term357 = term107.
Proof. exact (EQ_MP (@lem6916660) (@lem940073)). Qed.
Lemma lem6916662 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6916663 : term355 = term106.
Proof. exact (MK_COMB (@lem6916662) (@lem6916661)). Qed.
Lemma lem6916664 : term354 = term106.
Proof. exact (TRANS (@lem6916659) (@lem6916663)). Qed.
Lemma lem6916665 : term388 = term388.
Proof. exact (eq_refl term388). Qed.
Lemma lem6916666 : term392 = term390.
Proof. exact (MK_COMB (@lem6916665) (@lem6916664)). Qed.
Lemma lem6916668 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6916669 : term390 = term167.
Proof. exact (@lem6916668 term107). Qed.
Lemma lem6916670 : term392 = term167.
Proof. exact (TRANS (@lem6916666) (@lem6916669)). Qed.
Lemma lem6916671 : term167 = term392.
Proof. exact (SYM (@lem6916670)). Qed.
Lemma lem6916672 : term389 = term392.
Proof. exact (TRANS (@lem6916656) (@lem6916671)). Qed.
Lemma lem6916673 : term375 = term393.
Proof. exact (@lem6916623 (@lem6916672)). Qed.
Lemma lem6916674 : term374 = term393.
Proof. exact (TRANS (@lem6916589) (@lem6916673)). Qed.
Lemma lem6916676 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6916677 : term393 = term167.
Proof. exact (@lem6916676 term167). Qed.
Lemma lem6916678 : term374 = term167.
Proof. exact (TRANS (@lem6916674) (@lem6916677)). Qed.
Lemma lem6916679 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6916680 : term394 = term388.
Proof. exact (MK_COMB (@lem6916679) (@lem6916678)). Qed.
Lemma lem6916681 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem6916682 (y : int) : (term371 y) = (term395 y).
Proof. exact (MK_COMB (@lem6916680) (@lem6916681 y)). Qed.
Lemma lem6916683 (y : int) : (term370 y) = (term395 y).
Proof. exact (TRANS (@lem6916580 y) (@lem6916682 y)). Qed.
Lemma lem6916684 (y : int) : (term395 y) = term167.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem6916685 (y : int) : (term370 y) = term167.
Proof. exact (TRANS (@lem6916683 y) (@lem6916684 y)). Qed.
Lemma lem6916686 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6916687 (y : int) : (term396 y) = term169.
Proof. exact (MK_COMB (@lem6916686) (@lem6916685 y)). Qed.
Lemma lem6916688 : term339 = term339.
Proof. exact (eq_refl term339). Qed.
Lemma lem6916689 (y : int) : (term398 y) = term399.
Proof. exact (MK_COMB (@lem6916687 y) (@lem6916688)). Qed.
Lemma lem6916690 (y : int) : (term397 y) = term399.
Proof. exact (TRANS (@lem6916579 y) (@lem6916689 y)). Qed.
Lemma lem6916691 : term399 = term339.
Proof. exact (@lem1982721 term339). Qed.
Lemma lem6916692 (y : int) : (term397 y) = term339.
Proof. exact (TRANS (@lem6916690 y) (@lem6916691)). Qed.
Lemma lem6916693 (x : int) (y : int) : (term368 x y) = term399.
Proof. exact (MK_COMB (@lem6916578 x) (@lem6916692 y)). Qed.
Lemma lem6916694 (x : int) (y : int) : (term367 x y) = term399.
Proof. exact (TRANS (@lem6916470 x y) (@lem6916693 x y)). Qed.
Lemma lem6916695 : term399 = term339.
Proof. exact (@lem1982721 term339). Qed.
Lemma lem6916696 (x : int) (y : int) : (term367 x y) = term339.
Proof. exact (TRANS (@lem6916694 x y) (@lem6916695)). Qed.
Lemma lem6916697 (x : int) (y : int) : (term336 x y) = term339.
Proof. exact (TRANS (@lem6916469 x y) (@lem6916696 x y)). Qed.
Lemma lem6916698 (x : int) (y : int) : (term335 x y) = term339.
Proof. exact (TRANS (@lem6916418 x y) (@lem6916697 x y)). Qed.
Lemma lem6916699 (x : int) (y : int) : (term334 x y) = term339.
Proof. exact (TRANS (@lem6916417 x y) (@lem6916698 x y)). Qed.
Lemma lem6916700 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6916701 (x : int) (y : int) : (term400 x y) = term401.
Proof. exact (MK_COMB (@lem6916700) (@lem6916699 x y)). Qed.
Lemma lem6916702 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem6916703 (x : int) (y : int) : (term331 x y) = term402.
Proof. exact (MK_COMB (@lem6916701 x y) (@lem6916702)). Qed.
Lemma lem6916704 (y : int) (x : int) : (term111 y x) = term402.
Proof. exact (TRANS (@lem6916390 x y) (@lem6916703 x y)). Qed.
Lemma lem6916705 (x : int) : (term203 x) = term403.
Proof. exact (fun_ext (fun y : int => @lem6916704 y x)). Qed.
Lemma lem6916706 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916707 (x : int) : (term214 x) = term404.
Proof. exact (MK_COMB (@lem6916706) (@lem6916705 x)). Qed.
Lemma lem6916708 : term225 = term405.
Proof. exact (fun_ext (fun x : int => @lem6916707 x)). Qed.
Lemma lem6916709 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6916710 : term236 = term406.
Proof. exact (MK_COMB (@lem6916709) (@lem6916708)). Qed.
Lemma lem6916711 (y : int) (x : int) : (term111 x y) = (term331 y x).
Proof. exact (@lem1988287 (term98 x y) (term108 y x)). Qed.
Lemma lem6916712 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem6916719 (x : int) (y : int) : (term98 y x) = (term98 x y).
Proof. exact (@lem1982761 (real_of_int x) (real_of_int y)). Qed.
Lemma lem6916720 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6916721 (x : int) (y : int) : (term103 y x) = (term103 x y).
Proof. exact (MK_COMB (@lem6916720) (@lem6916719 x y)). Qed.
Lemma lem6916722 (x : int) (y : int) : (term108 y x) = (term108 x y).
Proof. exact (MK_COMB (@lem6916721 x y) (@lem6916712)). Qed.
Lemma lem6916727 (x : int) (y : int) : (term108 x y) = (term332 x y).
Proof. exact (@lem1982755 (real_of_int x) (real_of_int y) term106). Qed.
Lemma lem6916728 (x : int) (y : int) : (term108 y x) = (term332 x y).
Proof. exact (TRANS (@lem6916722 x y) (@lem6916727 x y)). Qed.
Lemma lem6916737 (x : int) (y : int) : (term333 x y) = (term333 x y).
Proof. exact (eq_refl (term333 x y)). Qed.
Lemma lem6916738 (x : int) (y : int) : (term334 y x) = (term335 x y).
Proof. exact (MK_COMB (@lem6916737 x y) (@lem6916728 x y)). Qed.
Lemma lem6916739 (x : int) (y : int) : (term335 x y) = (term336 x y).
Proof. exact (@lem1982792 (term98 x y) (term332 x y)). Qed.
Lemma lem6916740 (x : int) (y : int) : (term337 x y) = (term338 x y).
Proof. exact (@lem1982781 (real_of_int x) term339 (term184 y)). Qed.
Lemma lem6916741 (y : int) : (term340 y) = (term341 y).
Proof. exact (@lem1982781 (real_of_int y) term339 term106). Qed.
Lemma lem6916743 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6916744 : term106 = term343.
Proof. exact (@lem6916743 term107). Qed.
Lemma lem6916746 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6916747 : term339 = term346.
Proof. exact (@lem6916746 term107). Qed.
Lemma lem6916748 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6916749 : term347 = term348.
Proof. exact (MK_COMB (@lem6916748) (@lem6916747)). Qed.
Lemma lem6916750 : term349 = term350.
Proof. exact (MK_COMB (@lem6916749) (@lem6916744)). Qed.
Lemma lem6916751 : term350 = term351.
Proof. exact (@lem1981613 term339 term106 term106 term106). Qed.
Lemma lem6916753 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6916754 : term354 = term355.
Proof. exact (@lem6916753 term107 term107). Qed.
Lemma lem6916755 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6916756 : term357 = term107.
Proof. exact (EQ_MP (@lem6916755) (@lem940073)). Qed.
Lemma lem6916757 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6916758 : term355 = term106.
Proof. exact (MK_COMB (@lem6916757) (@lem6916756)). Qed.
Lemma lem6916759 : term354 = term106.
Proof. exact (TRANS (@lem6916754) (@lem6916758)). Qed.
Lemma lem6916761 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6916762 : term349 = term360.
Proof. exact (@lem6916761 term107 term107). Qed.
Lemma lem6916763 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6916764 : term357 = term107.
Proof. exact (EQ_MP (@lem6916763) (@lem940073)). Qed.
Lemma lem6916765 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6916766 : term355 = term106.
Proof. exact (MK_COMB (@lem6916765) (@lem6916764)). Qed.
Lemma lem6916767 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6916768 : term360 = term339.
Proof. exact (MK_COMB (@lem6916767) (@lem6916766)). Qed.
Lemma lem6916769 : term349 = term339.
Proof. exact (TRANS (@lem6916762) (@lem6916768)). Qed.
Lemma lem6916770 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6916771 : term361 = term362.
Proof. exact (MK_COMB (@lem6916770) (@lem6916769)). Qed.
Lemma lem6916772 : term351 = term346.
Proof. exact (MK_COMB (@lem6916771) (@lem6916759)). Qed.
Lemma lem6916773 : term350 = term346.
Proof. exact (TRANS (@lem6916751) (@lem6916772)). Qed.
Lemma lem6916774 : term349 = term346.
Proof. exact (TRANS (@lem6916750) (@lem6916773)). Qed.
Lemma lem6916776 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6916777 : term346 = term339.
Proof. exact (@lem6916776 term339). Qed.
Lemma lem6916778 : term349 = term339.
Proof. exact (TRANS (@lem6916774) (@lem6916777)). Qed.
Lemma lem6916781 (y : int) : (term364 y) = (term364 y).
Proof. exact (eq_refl (term364 y)). Qed.
Lemma lem6916782 (y : int) : (term341 y) = (term365 y).
Proof. exact (MK_COMB (@lem6916781 y) (@lem6916778)). Qed.
Lemma lem6916783 (y : int) : (term340 y) = (term365 y).
Proof. exact (TRANS (@lem6916741 y) (@lem6916782 y)). Qed.
Lemma lem6916786 (x : int) : (term364 x) = (term364 x).
Proof. exact (eq_refl (term364 x)). Qed.
Lemma lem6916787 (x : int) (y : int) : (term338 x y) = (term366 x y).
Proof. exact (MK_COMB (@lem6916786 x) (@lem6916783 y)). Qed.
Lemma lem6916788 (x : int) (y : int) : (term337 x y) = (term366 x y).
Proof. exact (TRANS (@lem6916740 x y) (@lem6916787 x y)). Qed.
Lemma lem6916789 (x : int) (y : int) : (term103 x y) = (term103 x y).
Proof. exact (eq_refl (term103 x y)). Qed.
Lemma lem6916790 (x : int) (y : int) : (term336 x y) = (term367 x y).
Proof. exact (MK_COMB (@lem6916789 x y) (@lem6916788 x y)). Qed.
Lemma lem6916791 (x : int) (y : int) : (term367 x y) = (term368 x y).
Proof. exact (@lem1982753 (real_of_int x) (term369 x) (real_of_int y) (term365 y)). Qed.
Lemma lem6916792 (x : int) : (term370 x) = (term371 x).
Proof. exact (@lem1982715 term339 (real_of_int x)). Qed.
Lemma lem6916794 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6916795 : term106 = term343.
Proof. exact (@lem6916794 term107). Qed.
Lemma lem6916797 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6916798 : term339 = term346.
Proof. exact (@lem6916797 term107). Qed.
Lemma lem6916799 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6916800 : term372 = term373.
Proof. exact (MK_COMB (@lem6916799) (@lem6916798)). Qed.
Lemma lem6916801 : term374 = term375.
Proof. exact (MK_COMB (@lem6916800) (@lem6916795)). Qed.
Lemma lem6916802 : term376.
Proof. exact (@lem1981473 term339 term106 term106 term106 term167 term106). Qed.
Lemma lem6916804 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6916805 : term378 = term379.
Proof. exact (@lem6916804 (NUMERAL 0) term107). Qed.
Lemma lem6916806 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6916807 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6916808 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6916807 h1) (fun h1 : term379 = True => @lem6916806)). Qed.
Lemma lem6916809 : term379 = True.
Proof. exact (EQ_MP (@lem6916808) (@lem6916806)). Qed.
Lemma lem6916810 : term378 = True.
Proof. exact (TRANS (@lem6916805) (@lem6916809)). Qed.
Lemma lem6916811 : True = term378.
Proof. exact (SYM (@lem6916810)). Qed.
Lemma lem6916812 : term378.
Proof. exact (EQ_MP (@lem6916811) (@lem0)). Qed.
Lemma lem6916813 : term381.
Proof. exact (@lem6916802 (@lem6916812)). Qed.
Lemma lem6916815 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6916816 : term378 = term379.
Proof. exact (@lem6916815 (NUMERAL 0) term107). Qed.
Lemma lem6916817 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6916818 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6916819 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6916818 h1) (fun h1 : term379 = True => @lem6916817)). Qed.
Lemma lem6916820 : term379 = True.
Proof. exact (EQ_MP (@lem6916819) (@lem6916817)). Qed.
Lemma lem6916821 : term378 = True.
Proof. exact (TRANS (@lem6916816) (@lem6916820)). Qed.
Lemma lem6916822 : True = term378.
Proof. exact (SYM (@lem6916821)). Qed.
Lemma lem6916823 : term378.
Proof. exact (EQ_MP (@lem6916822) (@lem0)). Qed.
Lemma lem6916824 : term382.
Proof. exact (@lem6916813 (@lem6916823)). Qed.
Lemma lem6916826 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6916827 : term378 = term379.
Proof. exact (@lem6916826 (NUMERAL 0) term107). Qed.
Lemma lem6916828 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6916829 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6916830 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6916829 h1) (fun h1 : term379 = True => @lem6916828)). Qed.
Lemma lem6916831 : term379 = True.
Proof. exact (EQ_MP (@lem6916830) (@lem6916828)). Qed.
Lemma lem6916832 : term378 = True.
Proof. exact (TRANS (@lem6916827) (@lem6916831)). Qed.
Lemma lem6916833 : True = term378.
Proof. exact (SYM (@lem6916832)). Qed.
Lemma lem6916834 : term378.
Proof. exact (EQ_MP (@lem6916833) (@lem0)). Qed.
Lemma lem6916835 : term383.
Proof. exact (@lem6916824 (@lem6916834)). Qed.
Lemma lem6916837 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6916838 : term354 = term355.
Proof. exact (@lem6916837 term107 term107). Qed.
Lemma lem6916839 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6916840 : term357 = term107.
Proof. exact (EQ_MP (@lem6916839) (@lem940073)). Qed.
Lemma lem6916841 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6916842 : term355 = term106.
Proof. exact (MK_COMB (@lem6916841) (@lem6916840)). Qed.
Lemma lem6916843 : term354 = term106.
Proof. exact (TRANS (@lem6916838) (@lem6916842)). Qed.
Lemma lem6916845 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6916846 : term349 = term360.
Proof. exact (@lem6916845 term107 term107). Qed.
Lemma lem6916847 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6916848 : term357 = term107.
Proof. exact (EQ_MP (@lem6916847) (@lem940073)). Qed.
Lemma lem6916849 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6916850 : term355 = term106.
Proof. exact (MK_COMB (@lem6916849) (@lem6916848)). Qed.
Lemma lem6916851 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6916852 : term360 = term339.
Proof. exact (MK_COMB (@lem6916851) (@lem6916850)). Qed.
Lemma lem6916853 : term349 = term339.
Proof. exact (TRANS (@lem6916846) (@lem6916852)). Qed.
Lemma lem6916854 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6916855 : term384 = term372.
Proof. exact (MK_COMB (@lem6916854) (@lem6916853)). Qed.
Lemma lem6916856 : term385 = term374.
Proof. exact (MK_COMB (@lem6916855) (@lem6916843)). Qed.
Lemma lem6916858 (m : nat) : (term386 m) = term167.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6916859 : term374 = term167.
Proof. exact (@lem6916858 term107). Qed.
Lemma lem6916860 : term385 = term167.
Proof. exact (TRANS (@lem6916856) (@lem6916859)). Qed.
Lemma lem6916861 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6916862 : term387 = term388.
Proof. exact (MK_COMB (@lem6916861) (@lem6916860)). Qed.
Lemma lem6916863 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem6916864 : term389 = term390.
Proof. exact (MK_COMB (@lem6916862) (@lem6916863)). Qed.
Lemma lem6916866 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6916867 : term390 = term167.
Proof. exact (@lem6916866 term107). Qed.
Lemma lem6916868 : term389 = term167.
Proof. exact (TRANS (@lem6916864) (@lem6916867)). Qed.
Lemma lem6916870 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6916871 : term354 = term355.
Proof. exact (@lem6916870 term107 term107). Qed.
Lemma lem6916872 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6916873 : term357 = term107.
Proof. exact (EQ_MP (@lem6916872) (@lem940073)). Qed.
Lemma lem6916874 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6916875 : term355 = term106.
Proof. exact (MK_COMB (@lem6916874) (@lem6916873)). Qed.
Lemma lem6916876 : term354 = term106.
Proof. exact (TRANS (@lem6916871) (@lem6916875)). Qed.
Lemma lem6916877 : term388 = term388.
Proof. exact (eq_refl term388). Qed.
Lemma lem6916878 : term392 = term390.
Proof. exact (MK_COMB (@lem6916877) (@lem6916876)). Qed.
Lemma lem6916880 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6916881 : term390 = term167.
Proof. exact (@lem6916880 term107). Qed.
Lemma lem6916882 : term392 = term167.
Proof. exact (TRANS (@lem6916878) (@lem6916881)). Qed.
Lemma lem6916883 : term167 = term392.
Proof. exact (SYM (@lem6916882)). Qed.
Lemma lem6916884 : term389 = term392.
Proof. exact (TRANS (@lem6916868) (@lem6916883)). Qed.
Lemma lem6916885 : term375 = term393.
Proof. exact (@lem6916835 (@lem6916884)). Qed.
Lemma lem6916886 : term374 = term393.
Proof. exact (TRANS (@lem6916801) (@lem6916885)). Qed.
Lemma lem6916888 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6916889 : term393 = term167.
Proof. exact (@lem6916888 term167). Qed.
Lemma lem6916890 : term374 = term167.
Proof. exact (TRANS (@lem6916886) (@lem6916889)). Qed.
Lemma lem6916891 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6916892 : term394 = term388.
Proof. exact (MK_COMB (@lem6916891) (@lem6916890)). Qed.
Lemma lem6916893 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem6916894 (x : int) : (term371 x) = (term395 x).
Proof. exact (MK_COMB (@lem6916892) (@lem6916893 x)). Qed.
Lemma lem6916895 (x : int) : (term370 x) = (term395 x).
Proof. exact (TRANS (@lem6916792 x) (@lem6916894 x)). Qed.
Lemma lem6916896 (x : int) : (term395 x) = term167.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem6916897 (x : int) : (term370 x) = term167.
Proof. exact (TRANS (@lem6916895 x) (@lem6916896 x)). Qed.
Lemma lem6916898 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6916899 (x : int) : (term396 x) = term169.
Proof. exact (MK_COMB (@lem6916898) (@lem6916897 x)). Qed.
Lemma lem6916900 (y : int) : (term397 y) = (term398 y).
Proof. exact (@lem1982763 (real_of_int y) (term369 y) term339). Qed.
Lemma lem6916901 (y : int) : (term370 y) = (term371 y).
Proof. exact (@lem1982715 term339 (real_of_int y)). Qed.
Lemma lem6916903 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6916904 : term106 = term343.
Proof. exact (@lem6916903 term107). Qed.
Lemma lem6916906 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6916907 : term339 = term346.
Proof. exact (@lem6916906 term107). Qed.
Lemma lem6916908 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6916909 : term372 = term373.
Proof. exact (MK_COMB (@lem6916908) (@lem6916907)). Qed.
Lemma lem6916910 : term374 = term375.
Proof. exact (MK_COMB (@lem6916909) (@lem6916904)). Qed.
Lemma lem6916911 : term376.
Proof. exact (@lem1981473 term339 term106 term106 term106 term167 term106). Qed.
Lemma lem6916913 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6916914 : term378 = term379.
Proof. exact (@lem6916913 (NUMERAL 0) term107). Qed.
Lemma lem6916915 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6916916 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6916917 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6916916 h1) (fun h1 : term379 = True => @lem6916915)). Qed.
Lemma lem6916918 : term379 = True.
Proof. exact (EQ_MP (@lem6916917) (@lem6916915)). Qed.
Lemma lem6916919 : term378 = True.
Proof. exact (TRANS (@lem6916914) (@lem6916918)). Qed.
Lemma lem6916920 : True = term378.
Proof. exact (SYM (@lem6916919)). Qed.
Lemma lem6916921 : term378.
Proof. exact (EQ_MP (@lem6916920) (@lem0)). Qed.
Lemma lem6916922 : term381.
Proof. exact (@lem6916911 (@lem6916921)). Qed.
Lemma lem6916924 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6916925 : term378 = term379.
Proof. exact (@lem6916924 (NUMERAL 0) term107). Qed.
Lemma lem6916926 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6916927 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6916928 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6916927 h1) (fun h1 : term379 = True => @lem6916926)). Qed.
Lemma lem6916929 : term379 = True.
Proof. exact (EQ_MP (@lem6916928) (@lem6916926)). Qed.
Lemma lem6916930 : term378 = True.
Proof. exact (TRANS (@lem6916925) (@lem6916929)). Qed.
Lemma lem6916931 : True = term378.
Proof. exact (SYM (@lem6916930)). Qed.
Lemma lem6916932 : term378.
Proof. exact (EQ_MP (@lem6916931) (@lem0)). Qed.
Lemma lem6916933 : term382.
Proof. exact (@lem6916922 (@lem6916932)). Qed.
Lemma lem6916935 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6916936 : term378 = term379.
Proof. exact (@lem6916935 (NUMERAL 0) term107). Qed.
Lemma lem6916937 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6916938 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6916939 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6916938 h1) (fun h1 : term379 = True => @lem6916937)). Qed.
Lemma lem6916940 : term379 = True.
Proof. exact (EQ_MP (@lem6916939) (@lem6916937)). Qed.
Lemma lem6916941 : term378 = True.
Proof. exact (TRANS (@lem6916936) (@lem6916940)). Qed.
Lemma lem6916942 : True = term378.
Proof. exact (SYM (@lem6916941)). Qed.
Lemma lem6916943 : term378.
Proof. exact (EQ_MP (@lem6916942) (@lem0)). Qed.
Lemma lem6916944 : term383.
Proof. exact (@lem6916933 (@lem6916943)). Qed.
Lemma lem6916946 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6916947 : term354 = term355.
Proof. exact (@lem6916946 term107 term107). Qed.
Lemma lem6916948 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6916949 : term357 = term107.
Proof. exact (EQ_MP (@lem6916948) (@lem940073)). Qed.
Lemma lem6916950 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6916951 : term355 = term106.
Proof. exact (MK_COMB (@lem6916950) (@lem6916949)). Qed.
Lemma lem6916952 : term354 = term106.
Proof. exact (TRANS (@lem6916947) (@lem6916951)). Qed.
Lemma lem6916954 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6916955 : term349 = term360.
Proof. exact (@lem6916954 term107 term107). Qed.
Lemma lem6916956 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6916957 : term357 = term107.
Proof. exact (EQ_MP (@lem6916956) (@lem940073)). Qed.
Lemma lem6916958 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6916959 : term355 = term106.
Proof. exact (MK_COMB (@lem6916958) (@lem6916957)). Qed.
Lemma lem6916960 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6916961 : term360 = term339.
Proof. exact (MK_COMB (@lem6916960) (@lem6916959)). Qed.
Lemma lem6916962 : term349 = term339.
Proof. exact (TRANS (@lem6916955) (@lem6916961)). Qed.
Lemma lem6916963 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6916964 : term384 = term372.
Proof. exact (MK_COMB (@lem6916963) (@lem6916962)). Qed.
Lemma lem6916965 : term385 = term374.
Proof. exact (MK_COMB (@lem6916964) (@lem6916952)). Qed.
Lemma lem6916967 (m : nat) : (term386 m) = term167.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6916968 : term374 = term167.
Proof. exact (@lem6916967 term107). Qed.
Lemma lem6916969 : term385 = term167.
Proof. exact (TRANS (@lem6916965) (@lem6916968)). Qed.
Lemma lem6916970 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6916971 : term387 = term388.
Proof. exact (MK_COMB (@lem6916970) (@lem6916969)). Qed.
Lemma lem6916972 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem6916973 : term389 = term390.
Proof. exact (MK_COMB (@lem6916971) (@lem6916972)). Qed.
Lemma lem6916975 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6916976 : term390 = term167.
Proof. exact (@lem6916975 term107). Qed.
Lemma lem6916977 : term389 = term167.
Proof. exact (TRANS (@lem6916973) (@lem6916976)). Qed.
Lemma lem6916979 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6916980 : term354 = term355.
Proof. exact (@lem6916979 term107 term107). Qed.
Lemma lem6916981 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6916982 : term357 = term107.
Proof. exact (EQ_MP (@lem6916981) (@lem940073)). Qed.
Lemma lem6916983 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6916984 : term355 = term106.
Proof. exact (MK_COMB (@lem6916983) (@lem6916982)). Qed.
Lemma lem6916985 : term354 = term106.
Proof. exact (TRANS (@lem6916980) (@lem6916984)). Qed.
Lemma lem6916986 : term388 = term388.
Proof. exact (eq_refl term388). Qed.
Lemma lem6916987 : term392 = term390.
Proof. exact (MK_COMB (@lem6916986) (@lem6916985)). Qed.
Lemma lem6916989 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6916990 : term390 = term167.
Proof. exact (@lem6916989 term107). Qed.
Lemma lem6916991 : term392 = term167.
Proof. exact (TRANS (@lem6916987) (@lem6916990)). Qed.
Lemma lem6916992 : term167 = term392.
Proof. exact (SYM (@lem6916991)). Qed.
Lemma lem6916993 : term389 = term392.
Proof. exact (TRANS (@lem6916977) (@lem6916992)). Qed.
Lemma lem6916994 : term375 = term393.
Proof. exact (@lem6916944 (@lem6916993)). Qed.
Lemma lem6916995 : term374 = term393.
Proof. exact (TRANS (@lem6916910) (@lem6916994)). Qed.
Lemma lem6916997 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6916998 : term393 = term167.
Proof. exact (@lem6916997 term167). Qed.
Lemma lem6916999 : term374 = term167.
Proof. exact (TRANS (@lem6916995) (@lem6916998)). Qed.
Lemma lem6917000 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6917001 : term394 = term388.
Proof. exact (MK_COMB (@lem6917000) (@lem6916999)). Qed.
Lemma lem6917002 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem6917003 (y : int) : (term371 y) = (term395 y).
Proof. exact (MK_COMB (@lem6917001) (@lem6917002 y)). Qed.
Lemma lem6917004 (y : int) : (term370 y) = (term395 y).
Proof. exact (TRANS (@lem6916901 y) (@lem6917003 y)). Qed.
Lemma lem6917005 (y : int) : (term395 y) = term167.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem6917006 (y : int) : (term370 y) = term167.
Proof. exact (TRANS (@lem6917004 y) (@lem6917005 y)). Qed.
Lemma lem6917007 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917008 (y : int) : (term396 y) = term169.
Proof. exact (MK_COMB (@lem6917007) (@lem6917006 y)). Qed.
Lemma lem6917009 : term339 = term339.
Proof. exact (eq_refl term339). Qed.
Lemma lem6917010 (y : int) : (term398 y) = term399.
Proof. exact (MK_COMB (@lem6917008 y) (@lem6917009)). Qed.
Lemma lem6917011 (y : int) : (term397 y) = term399.
Proof. exact (TRANS (@lem6916900 y) (@lem6917010 y)). Qed.
Lemma lem6917012 : term399 = term339.
Proof. exact (@lem1982721 term339). Qed.
Lemma lem6917013 (y : int) : (term397 y) = term339.
Proof. exact (TRANS (@lem6917011 y) (@lem6917012)). Qed.
Lemma lem6917014 (x : int) (y : int) : (term368 x y) = term399.
Proof. exact (MK_COMB (@lem6916899 x) (@lem6917013 y)). Qed.
Lemma lem6917015 (x : int) (y : int) : (term367 x y) = term399.
Proof. exact (TRANS (@lem6916791 x y) (@lem6917014 x y)). Qed.
Lemma lem6917016 : term399 = term339.
Proof. exact (@lem1982721 term339). Qed.
Lemma lem6917017 (x : int) (y : int) : (term367 x y) = term339.
Proof. exact (TRANS (@lem6917015 x y) (@lem6917016)). Qed.
Lemma lem6917018 (x : int) (y : int) : (term336 x y) = term339.
Proof. exact (TRANS (@lem6916790 x y) (@lem6917017 x y)). Qed.
Lemma lem6917019 (x : int) (y : int) : (term335 x y) = term339.
Proof. exact (TRANS (@lem6916739 x y) (@lem6917018 x y)). Qed.
Lemma lem6917020 (y : int) (x : int) : (term334 y x) = term339.
Proof. exact (TRANS (@lem6916738 x y) (@lem6917019 x y)). Qed.
Lemma lem6917021 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6917022 (y : int) (x : int) : (term400 y x) = term401.
Proof. exact (MK_COMB (@lem6917021) (@lem6917020 y x)). Qed.
Lemma lem6917023 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem6917024 (y : int) (x : int) : (term331 y x) = term402.
Proof. exact (MK_COMB (@lem6917022 y x) (@lem6917023)). Qed.
Lemma lem6917025 (x : int) (y : int) : (term111 x y) = term402.
Proof. exact (TRANS (@lem6916711 y x) (@lem6917024 y x)). Qed.
Lemma lem6917026 (x : int) : (term204 x) = term403.
Proof. exact (fun_ext (fun y : int => @lem6917025 x y)). Qed.
Lemma lem6917027 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6917028 (x : int) : (term219 x) = term404.
Proof. exact (MK_COMB (@lem6917027) (@lem6917026 x)). Qed.
Lemma lem6917029 : term226 = term405.
Proof. exact (fun_ext (fun x : int => @lem6917028 x)). Qed.
Lemma lem6917030 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6917031 : term241 = term406.
Proof. exact (MK_COMB (@lem6917030) (@lem6917029)). Qed.
Lemma lem6917032 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6917033 : term238 = term407.
Proof. exact (MK_COMB (@lem6917032) (@lem6916710)). Qed.
Lemma lem6917034 : term242 = term408.
Proof. exact (MK_COMB (@lem6917033) (@lem6917031)). Qed.
Lemma lem6917035 (x : int) (y : int) (z : int) : (term137 x y z) = (term409 x y z).
Proof. exact (@lem1988287 (term136 x y z) (term131 x y z)). Qed.
Lemma lem6917053 (x : int) (y : int) (z : int) : (term131 x y z) = (term410 x y z).
Proof. exact (@lem1982755 (real_of_int x) (term98 y z) term106). Qed.
Lemma lem6917058 (y : int) (z : int) : (term108 y z) = (term332 y z).
Proof. exact (@lem1982755 (real_of_int y) (real_of_int z) term106). Qed.
Lemma lem6917059 (x : int) : (term127 x) = (term127 x).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem6917060 (x : int) (y : int) (z : int) : (term410 x y z) = (term411 x y z).
Proof. exact (MK_COMB (@lem6917059 x) (@lem6917058 y z)). Qed.
Lemma lem6917062 (x : int) (y : int) (z : int) : (term131 x y z) = (term411 x y z).
Proof. exact (TRANS (@lem6917053 x y z) (@lem6917060 x y z)). Qed.
Lemma lem6917079 (x : int) (y : int) (z : int) : (term136 x y z) = (term128 x y z).
Proof. exact (@lem1982755 (real_of_int x) (real_of_int y) (real_of_int z)). Qed.
Lemma lem6917080 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem6917081 (x : int) (y : int) (z : int) : (term412 x y z) = (term413 x y z).
Proof. exact (MK_COMB (@lem6917080) (@lem6917079 x y z)). Qed.
Lemma lem6917082 (x : int) (y : int) (z : int) : (term414 x y z) = (term415 x y z).
Proof. exact (MK_COMB (@lem6917081 x y z) (@lem6917062 x y z)). Qed.
Lemma lem6917083 (x : int) (y : int) (z : int) : (term415 x y z) = (term416 x y z).
Proof. exact (@lem1982792 (term128 x y z) (term411 x y z)). Qed.
Lemma lem6917084 (x : int) (y : int) (z : int) : (term417 x y z) = (term418 x y z).
Proof. exact (@lem1982781 (real_of_int x) term339 (term332 y z)). Qed.
Lemma lem6917085 (y : int) (z : int) : (term337 y z) = (term338 y z).
Proof. exact (@lem1982781 (real_of_int y) term339 (term184 z)). Qed.
Lemma lem6917086 (z : int) : (term340 z) = (term341 z).
Proof. exact (@lem1982781 (real_of_int z) term339 term106). Qed.
Lemma lem6917088 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6917089 : term106 = term343.
Proof. exact (@lem6917088 term107). Qed.
Lemma lem6917091 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6917092 : term339 = term346.
Proof. exact (@lem6917091 term107). Qed.
Lemma lem6917093 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6917094 : term347 = term348.
Proof. exact (MK_COMB (@lem6917093) (@lem6917092)). Qed.
Lemma lem6917095 : term349 = term350.
Proof. exact (MK_COMB (@lem6917094) (@lem6917089)). Qed.
Lemma lem6917096 : term350 = term351.
Proof. exact (@lem1981613 term339 term106 term106 term106). Qed.
Lemma lem6917098 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6917099 : term354 = term355.
Proof. exact (@lem6917098 term107 term107). Qed.
Lemma lem6917100 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917101 : term357 = term107.
Proof. exact (EQ_MP (@lem6917100) (@lem940073)). Qed.
Lemma lem6917102 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917103 : term355 = term106.
Proof. exact (MK_COMB (@lem6917102) (@lem6917101)). Qed.
Lemma lem6917104 : term354 = term106.
Proof. exact (TRANS (@lem6917099) (@lem6917103)). Qed.
Lemma lem6917106 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6917107 : term349 = term360.
Proof. exact (@lem6917106 term107 term107). Qed.
Lemma lem6917108 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917109 : term357 = term107.
Proof. exact (EQ_MP (@lem6917108) (@lem940073)). Qed.
Lemma lem6917110 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917111 : term355 = term106.
Proof. exact (MK_COMB (@lem6917110) (@lem6917109)). Qed.
Lemma lem6917112 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6917113 : term360 = term339.
Proof. exact (MK_COMB (@lem6917112) (@lem6917111)). Qed.
Lemma lem6917114 : term349 = term339.
Proof. exact (TRANS (@lem6917107) (@lem6917113)). Qed.
Lemma lem6917115 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6917116 : term361 = term362.
Proof. exact (MK_COMB (@lem6917115) (@lem6917114)). Qed.
Lemma lem6917117 : term351 = term346.
Proof. exact (MK_COMB (@lem6917116) (@lem6917104)). Qed.
Lemma lem6917118 : term350 = term346.
Proof. exact (TRANS (@lem6917096) (@lem6917117)). Qed.
Lemma lem6917119 : term349 = term346.
Proof. exact (TRANS (@lem6917095) (@lem6917118)). Qed.
Lemma lem6917121 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6917122 : term346 = term339.
Proof. exact (@lem6917121 term339). Qed.
Lemma lem6917123 : term349 = term339.
Proof. exact (TRANS (@lem6917119) (@lem6917122)). Qed.
Lemma lem6917126 (z : int) : (term364 z) = (term364 z).
Proof. exact (eq_refl (term364 z)). Qed.
Lemma lem6917127 (z : int) : (term341 z) = (term365 z).
Proof. exact (MK_COMB (@lem6917126 z) (@lem6917123)). Qed.
Lemma lem6917128 (z : int) : (term340 z) = (term365 z).
Proof. exact (TRANS (@lem6917086 z) (@lem6917127 z)). Qed.
Lemma lem6917131 (y : int) : (term364 y) = (term364 y).
Proof. exact (eq_refl (term364 y)). Qed.
Lemma lem6917132 (y : int) (z : int) : (term338 y z) = (term366 y z).
Proof. exact (MK_COMB (@lem6917131 y) (@lem6917128 z)). Qed.
Lemma lem6917133 (y : int) (z : int) : (term337 y z) = (term366 y z).
Proof. exact (TRANS (@lem6917085 y z) (@lem6917132 y z)). Qed.
Lemma lem6917136 (x : int) : (term364 x) = (term364 x).
Proof. exact (eq_refl (term364 x)). Qed.
Lemma lem6917137 (x : int) (y : int) (z : int) : (term418 x y z) = (term419 x y z).
Proof. exact (MK_COMB (@lem6917136 x) (@lem6917133 y z)). Qed.
Lemma lem6917138 (x : int) (y : int) (z : int) : (term417 x y z) = (term419 x y z).
Proof. exact (TRANS (@lem6917084 x y z) (@lem6917137 x y z)). Qed.
Lemma lem6917139 (x : int) (y : int) (z : int) : (term130 x y z) = (term130 x y z).
Proof. exact (eq_refl (term130 x y z)). Qed.
Lemma lem6917140 (x : int) (y : int) (z : int) : (term416 x y z) = (term420 x y z).
Proof. exact (MK_COMB (@lem6917139 x y z) (@lem6917138 x y z)). Qed.
Lemma lem6917141 (x : int) (y : int) (z : int) : (term420 x y z) = (term421 x y z).
Proof. exact (@lem1982753 (real_of_int x) (term369 x) (term98 y z) (term366 y z)). Qed.
Lemma lem6917142 (x : int) : (term370 x) = (term371 x).
Proof. exact (@lem1982715 term339 (real_of_int x)). Qed.
Lemma lem6917144 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6917145 : term106 = term343.
Proof. exact (@lem6917144 term107). Qed.
Lemma lem6917147 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6917148 : term339 = term346.
Proof. exact (@lem6917147 term107). Qed.
Lemma lem6917149 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917150 : term372 = term373.
Proof. exact (MK_COMB (@lem6917149) (@lem6917148)). Qed.
Lemma lem6917151 : term374 = term375.
Proof. exact (MK_COMB (@lem6917150) (@lem6917145)). Qed.
Lemma lem6917152 : term376.
Proof. exact (@lem1981473 term339 term106 term106 term106 term167 term106). Qed.
Lemma lem6917154 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917155 : term378 = term379.
Proof. exact (@lem6917154 (NUMERAL 0) term107). Qed.
Lemma lem6917156 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917157 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917158 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917157 h1) (fun h1 : term379 = True => @lem6917156)). Qed.
Lemma lem6917159 : term379 = True.
Proof. exact (EQ_MP (@lem6917158) (@lem6917156)). Qed.
Lemma lem6917160 : term378 = True.
Proof. exact (TRANS (@lem6917155) (@lem6917159)). Qed.
Lemma lem6917161 : True = term378.
Proof. exact (SYM (@lem6917160)). Qed.
Lemma lem6917162 : term378.
Proof. exact (EQ_MP (@lem6917161) (@lem0)). Qed.
Lemma lem6917163 : term381.
Proof. exact (@lem6917152 (@lem6917162)). Qed.
Lemma lem6917165 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917166 : term378 = term379.
Proof. exact (@lem6917165 (NUMERAL 0) term107). Qed.
Lemma lem6917167 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917168 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917169 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917168 h1) (fun h1 : term379 = True => @lem6917167)). Qed.
Lemma lem6917170 : term379 = True.
Proof. exact (EQ_MP (@lem6917169) (@lem6917167)). Qed.
Lemma lem6917171 : term378 = True.
Proof. exact (TRANS (@lem6917166) (@lem6917170)). Qed.
Lemma lem6917172 : True = term378.
Proof. exact (SYM (@lem6917171)). Qed.
Lemma lem6917173 : term378.
Proof. exact (EQ_MP (@lem6917172) (@lem0)). Qed.
Lemma lem6917174 : term382.
Proof. exact (@lem6917163 (@lem6917173)). Qed.
Lemma lem6917176 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917177 : term378 = term379.
Proof. exact (@lem6917176 (NUMERAL 0) term107). Qed.
Lemma lem6917178 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917179 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917180 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917179 h1) (fun h1 : term379 = True => @lem6917178)). Qed.
Lemma lem6917181 : term379 = True.
Proof. exact (EQ_MP (@lem6917180) (@lem6917178)). Qed.
Lemma lem6917182 : term378 = True.
Proof. exact (TRANS (@lem6917177) (@lem6917181)). Qed.
Lemma lem6917183 : True = term378.
Proof. exact (SYM (@lem6917182)). Qed.
Lemma lem6917184 : term378.
Proof. exact (EQ_MP (@lem6917183) (@lem0)). Qed.
Lemma lem6917185 : term383.
Proof. exact (@lem6917174 (@lem6917184)). Qed.
Lemma lem6917187 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6917188 : term354 = term355.
Proof. exact (@lem6917187 term107 term107). Qed.
Lemma lem6917189 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917190 : term357 = term107.
Proof. exact (EQ_MP (@lem6917189) (@lem940073)). Qed.
Lemma lem6917191 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917192 : term355 = term106.
Proof. exact (MK_COMB (@lem6917191) (@lem6917190)). Qed.
Lemma lem6917193 : term354 = term106.
Proof. exact (TRANS (@lem6917188) (@lem6917192)). Qed.
Lemma lem6917195 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6917196 : term349 = term360.
Proof. exact (@lem6917195 term107 term107). Qed.
Lemma lem6917197 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917198 : term357 = term107.
Proof. exact (EQ_MP (@lem6917197) (@lem940073)). Qed.
Lemma lem6917199 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917200 : term355 = term106.
Proof. exact (MK_COMB (@lem6917199) (@lem6917198)). Qed.
Lemma lem6917201 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6917202 : term360 = term339.
Proof. exact (MK_COMB (@lem6917201) (@lem6917200)). Qed.
Lemma lem6917203 : term349 = term339.
Proof. exact (TRANS (@lem6917196) (@lem6917202)). Qed.
Lemma lem6917204 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917205 : term384 = term372.
Proof. exact (MK_COMB (@lem6917204) (@lem6917203)). Qed.
Lemma lem6917206 : term385 = term374.
Proof. exact (MK_COMB (@lem6917205) (@lem6917193)). Qed.
Lemma lem6917208 (m : nat) : (term386 m) = term167.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6917209 : term374 = term167.
Proof. exact (@lem6917208 term107). Qed.
Lemma lem6917210 : term385 = term167.
Proof. exact (TRANS (@lem6917206) (@lem6917209)). Qed.
Lemma lem6917211 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6917212 : term387 = term388.
Proof. exact (MK_COMB (@lem6917211) (@lem6917210)). Qed.
Lemma lem6917213 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem6917214 : term389 = term390.
Proof. exact (MK_COMB (@lem6917212) (@lem6917213)). Qed.
Lemma lem6917216 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6917217 : term390 = term167.
Proof. exact (@lem6917216 term107). Qed.
Lemma lem6917218 : term389 = term167.
Proof. exact (TRANS (@lem6917214) (@lem6917217)). Qed.
Lemma lem6917220 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6917221 : term354 = term355.
Proof. exact (@lem6917220 term107 term107). Qed.
Lemma lem6917222 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917223 : term357 = term107.
Proof. exact (EQ_MP (@lem6917222) (@lem940073)). Qed.
Lemma lem6917224 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917225 : term355 = term106.
Proof. exact (MK_COMB (@lem6917224) (@lem6917223)). Qed.
Lemma lem6917226 : term354 = term106.
Proof. exact (TRANS (@lem6917221) (@lem6917225)). Qed.
Lemma lem6917227 : term388 = term388.
Proof. exact (eq_refl term388). Qed.
Lemma lem6917228 : term392 = term390.
Proof. exact (MK_COMB (@lem6917227) (@lem6917226)). Qed.
Lemma lem6917230 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6917231 : term390 = term167.
Proof. exact (@lem6917230 term107). Qed.
Lemma lem6917232 : term392 = term167.
Proof. exact (TRANS (@lem6917228) (@lem6917231)). Qed.
Lemma lem6917233 : term167 = term392.
Proof. exact (SYM (@lem6917232)). Qed.
Lemma lem6917234 : term389 = term392.
Proof. exact (TRANS (@lem6917218) (@lem6917233)). Qed.
Lemma lem6917235 : term375 = term393.
Proof. exact (@lem6917185 (@lem6917234)). Qed.
Lemma lem6917236 : term374 = term393.
Proof. exact (TRANS (@lem6917151) (@lem6917235)). Qed.
Lemma lem6917238 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6917239 : term393 = term167.
Proof. exact (@lem6917238 term167). Qed.
Lemma lem6917240 : term374 = term167.
Proof. exact (TRANS (@lem6917236) (@lem6917239)). Qed.
Lemma lem6917241 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6917242 : term394 = term388.
Proof. exact (MK_COMB (@lem6917241) (@lem6917240)). Qed.
Lemma lem6917243 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem6917244 (x : int) : (term371 x) = (term395 x).
Proof. exact (MK_COMB (@lem6917242) (@lem6917243 x)). Qed.
Lemma lem6917245 (x : int) : (term370 x) = (term395 x).
Proof. exact (TRANS (@lem6917142 x) (@lem6917244 x)). Qed.
Lemma lem6917246 (x : int) : (term395 x) = term167.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem6917247 (x : int) : (term370 x) = term167.
Proof. exact (TRANS (@lem6917245 x) (@lem6917246 x)). Qed.
Lemma lem6917248 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917249 (x : int) : (term396 x) = term169.
Proof. exact (MK_COMB (@lem6917248) (@lem6917247 x)). Qed.
Lemma lem6917250 (y : int) (z : int) : (term367 y z) = (term368 y z).
Proof. exact (@lem1982753 (real_of_int y) (term369 y) (real_of_int z) (term365 z)). Qed.
Lemma lem6917251 (y : int) : (term370 y) = (term371 y).
Proof. exact (@lem1982715 term339 (real_of_int y)). Qed.
Lemma lem6917253 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6917254 : term106 = term343.
Proof. exact (@lem6917253 term107). Qed.
Lemma lem6917256 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6917257 : term339 = term346.
Proof. exact (@lem6917256 term107). Qed.
Lemma lem6917258 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917259 : term372 = term373.
Proof. exact (MK_COMB (@lem6917258) (@lem6917257)). Qed.
Lemma lem6917260 : term374 = term375.
Proof. exact (MK_COMB (@lem6917259) (@lem6917254)). Qed.
Lemma lem6917261 : term376.
Proof. exact (@lem1981473 term339 term106 term106 term106 term167 term106). Qed.
Lemma lem6917263 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917264 : term378 = term379.
Proof. exact (@lem6917263 (NUMERAL 0) term107). Qed.
Lemma lem6917265 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917266 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917267 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917266 h1) (fun h1 : term379 = True => @lem6917265)). Qed.
Lemma lem6917268 : term379 = True.
Proof. exact (EQ_MP (@lem6917267) (@lem6917265)). Qed.
Lemma lem6917269 : term378 = True.
Proof. exact (TRANS (@lem6917264) (@lem6917268)). Qed.
Lemma lem6917270 : True = term378.
Proof. exact (SYM (@lem6917269)). Qed.
Lemma lem6917271 : term378.
Proof. exact (EQ_MP (@lem6917270) (@lem0)). Qed.
Lemma lem6917272 : term381.
Proof. exact (@lem6917261 (@lem6917271)). Qed.
Lemma lem6917274 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917275 : term378 = term379.
Proof. exact (@lem6917274 (NUMERAL 0) term107). Qed.
Lemma lem6917276 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917277 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917278 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917277 h1) (fun h1 : term379 = True => @lem6917276)). Qed.
Lemma lem6917279 : term379 = True.
Proof. exact (EQ_MP (@lem6917278) (@lem6917276)). Qed.
Lemma lem6917280 : term378 = True.
Proof. exact (TRANS (@lem6917275) (@lem6917279)). Qed.
Lemma lem6917281 : True = term378.
Proof. exact (SYM (@lem6917280)). Qed.
Lemma lem6917282 : term378.
Proof. exact (EQ_MP (@lem6917281) (@lem0)). Qed.
Lemma lem6917283 : term382.
Proof. exact (@lem6917272 (@lem6917282)). Qed.
Lemma lem6917285 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917286 : term378 = term379.
Proof. exact (@lem6917285 (NUMERAL 0) term107). Qed.
Lemma lem6917287 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917288 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917289 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917288 h1) (fun h1 : term379 = True => @lem6917287)). Qed.
Lemma lem6917290 : term379 = True.
Proof. exact (EQ_MP (@lem6917289) (@lem6917287)). Qed.
Lemma lem6917291 : term378 = True.
Proof. exact (TRANS (@lem6917286) (@lem6917290)). Qed.
Lemma lem6917292 : True = term378.
Proof. exact (SYM (@lem6917291)). Qed.
Lemma lem6917293 : term378.
Proof. exact (EQ_MP (@lem6917292) (@lem0)). Qed.
Lemma lem6917294 : term383.
Proof. exact (@lem6917283 (@lem6917293)). Qed.
Lemma lem6917296 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6917297 : term354 = term355.
Proof. exact (@lem6917296 term107 term107). Qed.
Lemma lem6917298 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917299 : term357 = term107.
Proof. exact (EQ_MP (@lem6917298) (@lem940073)). Qed.
Lemma lem6917300 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917301 : term355 = term106.
Proof. exact (MK_COMB (@lem6917300) (@lem6917299)). Qed.
Lemma lem6917302 : term354 = term106.
Proof. exact (TRANS (@lem6917297) (@lem6917301)). Qed.
Lemma lem6917304 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6917305 : term349 = term360.
Proof. exact (@lem6917304 term107 term107). Qed.
Lemma lem6917306 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917307 : term357 = term107.
Proof. exact (EQ_MP (@lem6917306) (@lem940073)). Qed.
Lemma lem6917308 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917309 : term355 = term106.
Proof. exact (MK_COMB (@lem6917308) (@lem6917307)). Qed.
Lemma lem6917310 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6917311 : term360 = term339.
Proof. exact (MK_COMB (@lem6917310) (@lem6917309)). Qed.
Lemma lem6917312 : term349 = term339.
Proof. exact (TRANS (@lem6917305) (@lem6917311)). Qed.
Lemma lem6917313 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917314 : term384 = term372.
Proof. exact (MK_COMB (@lem6917313) (@lem6917312)). Qed.
Lemma lem6917315 : term385 = term374.
Proof. exact (MK_COMB (@lem6917314) (@lem6917302)). Qed.
Lemma lem6917317 (m : nat) : (term386 m) = term167.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6917318 : term374 = term167.
Proof. exact (@lem6917317 term107). Qed.
Lemma lem6917319 : term385 = term167.
Proof. exact (TRANS (@lem6917315) (@lem6917318)). Qed.
Lemma lem6917320 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6917321 : term387 = term388.
Proof. exact (MK_COMB (@lem6917320) (@lem6917319)). Qed.
Lemma lem6917322 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem6917323 : term389 = term390.
Proof. exact (MK_COMB (@lem6917321) (@lem6917322)). Qed.
Lemma lem6917325 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6917326 : term390 = term167.
Proof. exact (@lem6917325 term107). Qed.
Lemma lem6917327 : term389 = term167.
Proof. exact (TRANS (@lem6917323) (@lem6917326)). Qed.
Lemma lem6917329 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6917330 : term354 = term355.
Proof. exact (@lem6917329 term107 term107). Qed.
Lemma lem6917331 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917332 : term357 = term107.
Proof. exact (EQ_MP (@lem6917331) (@lem940073)). Qed.
Lemma lem6917333 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917334 : term355 = term106.
Proof. exact (MK_COMB (@lem6917333) (@lem6917332)). Qed.
Lemma lem6917335 : term354 = term106.
Proof. exact (TRANS (@lem6917330) (@lem6917334)). Qed.
Lemma lem6917336 : term388 = term388.
Proof. exact (eq_refl term388). Qed.
Lemma lem6917337 : term392 = term390.
Proof. exact (MK_COMB (@lem6917336) (@lem6917335)). Qed.
Lemma lem6917339 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6917340 : term390 = term167.
Proof. exact (@lem6917339 term107). Qed.
Lemma lem6917341 : term392 = term167.
Proof. exact (TRANS (@lem6917337) (@lem6917340)). Qed.
Lemma lem6917342 : term167 = term392.
Proof. exact (SYM (@lem6917341)). Qed.
Lemma lem6917343 : term389 = term392.
Proof. exact (TRANS (@lem6917327) (@lem6917342)). Qed.
Lemma lem6917344 : term375 = term393.
Proof. exact (@lem6917294 (@lem6917343)). Qed.
Lemma lem6917345 : term374 = term393.
Proof. exact (TRANS (@lem6917260) (@lem6917344)). Qed.
Lemma lem6917347 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6917348 : term393 = term167.
Proof. exact (@lem6917347 term167). Qed.
Lemma lem6917349 : term374 = term167.
Proof. exact (TRANS (@lem6917345) (@lem6917348)). Qed.
Lemma lem6917350 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6917351 : term394 = term388.
Proof. exact (MK_COMB (@lem6917350) (@lem6917349)). Qed.
Lemma lem6917352 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem6917353 (y : int) : (term371 y) = (term395 y).
Proof. exact (MK_COMB (@lem6917351) (@lem6917352 y)). Qed.
Lemma lem6917354 (y : int) : (term370 y) = (term395 y).
Proof. exact (TRANS (@lem6917251 y) (@lem6917353 y)). Qed.
Lemma lem6917355 (y : int) : (term395 y) = term167.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem6917356 (y : int) : (term370 y) = term167.
Proof. exact (TRANS (@lem6917354 y) (@lem6917355 y)). Qed.
Lemma lem6917357 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917358 (y : int) : (term396 y) = term169.
Proof. exact (MK_COMB (@lem6917357) (@lem6917356 y)). Qed.
Lemma lem6917359 (z : int) : (term397 z) = (term398 z).
Proof. exact (@lem1982763 (real_of_int z) (term369 z) term339). Qed.
Lemma lem6917360 (z : int) : (term370 z) = (term371 z).
Proof. exact (@lem1982715 term339 (real_of_int z)). Qed.
Lemma lem6917362 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6917363 : term106 = term343.
Proof. exact (@lem6917362 term107). Qed.
Lemma lem6917365 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6917366 : term339 = term346.
Proof. exact (@lem6917365 term107). Qed.
Lemma lem6917367 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917368 : term372 = term373.
Proof. exact (MK_COMB (@lem6917367) (@lem6917366)). Qed.
Lemma lem6917369 : term374 = term375.
Proof. exact (MK_COMB (@lem6917368) (@lem6917363)). Qed.
Lemma lem6917370 : term376.
Proof. exact (@lem1981473 term339 term106 term106 term106 term167 term106). Qed.
Lemma lem6917372 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917373 : term378 = term379.
Proof. exact (@lem6917372 (NUMERAL 0) term107). Qed.
Lemma lem6917374 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917375 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917376 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917375 h1) (fun h1 : term379 = True => @lem6917374)). Qed.
Lemma lem6917377 : term379 = True.
Proof. exact (EQ_MP (@lem6917376) (@lem6917374)). Qed.
Lemma lem6917378 : term378 = True.
Proof. exact (TRANS (@lem6917373) (@lem6917377)). Qed.
Lemma lem6917379 : True = term378.
Proof. exact (SYM (@lem6917378)). Qed.
Lemma lem6917380 : term378.
Proof. exact (EQ_MP (@lem6917379) (@lem0)). Qed.
Lemma lem6917381 : term381.
Proof. exact (@lem6917370 (@lem6917380)). Qed.
Lemma lem6917383 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917384 : term378 = term379.
Proof. exact (@lem6917383 (NUMERAL 0) term107). Qed.
Lemma lem6917385 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917386 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917387 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917386 h1) (fun h1 : term379 = True => @lem6917385)). Qed.
Lemma lem6917388 : term379 = True.
Proof. exact (EQ_MP (@lem6917387) (@lem6917385)). Qed.
Lemma lem6917389 : term378 = True.
Proof. exact (TRANS (@lem6917384) (@lem6917388)). Qed.
Lemma lem6917390 : True = term378.
Proof. exact (SYM (@lem6917389)). Qed.
Lemma lem6917391 : term378.
Proof. exact (EQ_MP (@lem6917390) (@lem0)). Qed.
Lemma lem6917392 : term382.
Proof. exact (@lem6917381 (@lem6917391)). Qed.
Lemma lem6917394 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917395 : term378 = term379.
Proof. exact (@lem6917394 (NUMERAL 0) term107). Qed.
Lemma lem6917396 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917397 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917398 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917397 h1) (fun h1 : term379 = True => @lem6917396)). Qed.
Lemma lem6917399 : term379 = True.
Proof. exact (EQ_MP (@lem6917398) (@lem6917396)). Qed.
Lemma lem6917400 : term378 = True.
Proof. exact (TRANS (@lem6917395) (@lem6917399)). Qed.
Lemma lem6917401 : True = term378.
Proof. exact (SYM (@lem6917400)). Qed.
Lemma lem6917402 : term378.
Proof. exact (EQ_MP (@lem6917401) (@lem0)). Qed.
Lemma lem6917403 : term383.
Proof. exact (@lem6917392 (@lem6917402)). Qed.
Lemma lem6917405 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6917406 : term354 = term355.
Proof. exact (@lem6917405 term107 term107). Qed.
Lemma lem6917407 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917408 : term357 = term107.
Proof. exact (EQ_MP (@lem6917407) (@lem940073)). Qed.
Lemma lem6917409 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917410 : term355 = term106.
Proof. exact (MK_COMB (@lem6917409) (@lem6917408)). Qed.
Lemma lem6917411 : term354 = term106.
Proof. exact (TRANS (@lem6917406) (@lem6917410)). Qed.
Lemma lem6917413 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6917414 : term349 = term360.
Proof. exact (@lem6917413 term107 term107). Qed.
Lemma lem6917415 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917416 : term357 = term107.
Proof. exact (EQ_MP (@lem6917415) (@lem940073)). Qed.
Lemma lem6917417 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917418 : term355 = term106.
Proof. exact (MK_COMB (@lem6917417) (@lem6917416)). Qed.
Lemma lem6917419 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6917420 : term360 = term339.
Proof. exact (MK_COMB (@lem6917419) (@lem6917418)). Qed.
Lemma lem6917421 : term349 = term339.
Proof. exact (TRANS (@lem6917414) (@lem6917420)). Qed.
Lemma lem6917422 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917423 : term384 = term372.
Proof. exact (MK_COMB (@lem6917422) (@lem6917421)). Qed.
Lemma lem6917424 : term385 = term374.
Proof. exact (MK_COMB (@lem6917423) (@lem6917411)). Qed.
Lemma lem6917426 (m : nat) : (term386 m) = term167.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6917427 : term374 = term167.
Proof. exact (@lem6917426 term107). Qed.
Lemma lem6917428 : term385 = term167.
Proof. exact (TRANS (@lem6917424) (@lem6917427)). Qed.
Lemma lem6917429 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6917430 : term387 = term388.
Proof. exact (MK_COMB (@lem6917429) (@lem6917428)). Qed.
Lemma lem6917431 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem6917432 : term389 = term390.
Proof. exact (MK_COMB (@lem6917430) (@lem6917431)). Qed.
Lemma lem6917434 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6917435 : term390 = term167.
Proof. exact (@lem6917434 term107). Qed.
Lemma lem6917436 : term389 = term167.
Proof. exact (TRANS (@lem6917432) (@lem6917435)). Qed.
Lemma lem6917438 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6917439 : term354 = term355.
Proof. exact (@lem6917438 term107 term107). Qed.
Lemma lem6917440 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917441 : term357 = term107.
Proof. exact (EQ_MP (@lem6917440) (@lem940073)). Qed.
Lemma lem6917442 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917443 : term355 = term106.
Proof. exact (MK_COMB (@lem6917442) (@lem6917441)). Qed.
Lemma lem6917444 : term354 = term106.
Proof. exact (TRANS (@lem6917439) (@lem6917443)). Qed.
Lemma lem6917445 : term388 = term388.
Proof. exact (eq_refl term388). Qed.
Lemma lem6917446 : term392 = term390.
Proof. exact (MK_COMB (@lem6917445) (@lem6917444)). Qed.
Lemma lem6917448 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6917449 : term390 = term167.
Proof. exact (@lem6917448 term107). Qed.
Lemma lem6917450 : term392 = term167.
Proof. exact (TRANS (@lem6917446) (@lem6917449)). Qed.
Lemma lem6917451 : term167 = term392.
Proof. exact (SYM (@lem6917450)). Qed.
Lemma lem6917452 : term389 = term392.
Proof. exact (TRANS (@lem6917436) (@lem6917451)). Qed.
Lemma lem6917453 : term375 = term393.
Proof. exact (@lem6917403 (@lem6917452)). Qed.
Lemma lem6917454 : term374 = term393.
Proof. exact (TRANS (@lem6917369) (@lem6917453)). Qed.
Lemma lem6917456 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6917457 : term393 = term167.
Proof. exact (@lem6917456 term167). Qed.
Lemma lem6917458 : term374 = term167.
Proof. exact (TRANS (@lem6917454) (@lem6917457)). Qed.
Lemma lem6917459 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6917460 : term394 = term388.
Proof. exact (MK_COMB (@lem6917459) (@lem6917458)). Qed.
Lemma lem6917461 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem6917462 (z : int) : (term371 z) = (term395 z).
Proof. exact (MK_COMB (@lem6917460) (@lem6917461 z)). Qed.
Lemma lem6917463 (z : int) : (term370 z) = (term395 z).
Proof. exact (TRANS (@lem6917360 z) (@lem6917462 z)). Qed.
Lemma lem6917464 (z : int) : (term395 z) = term167.
Proof. exact (@lem1982719 (real_of_int z)). Qed.
Lemma lem6917465 (z : int) : (term370 z) = term167.
Proof. exact (TRANS (@lem6917463 z) (@lem6917464 z)). Qed.
Lemma lem6917466 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917467 (z : int) : (term396 z) = term169.
Proof. exact (MK_COMB (@lem6917466) (@lem6917465 z)). Qed.
Lemma lem6917468 : term339 = term339.
Proof. exact (eq_refl term339). Qed.
Lemma lem6917469 (z : int) : (term398 z) = term399.
Proof. exact (MK_COMB (@lem6917467 z) (@lem6917468)). Qed.
Lemma lem6917470 (z : int) : (term397 z) = term399.
Proof. exact (TRANS (@lem6917359 z) (@lem6917469 z)). Qed.
Lemma lem6917471 : term399 = term339.
Proof. exact (@lem1982721 term339). Qed.
Lemma lem6917472 (z : int) : (term397 z) = term339.
Proof. exact (TRANS (@lem6917470 z) (@lem6917471)). Qed.
Lemma lem6917473 (y : int) (z : int) : (term368 y z) = term399.
Proof. exact (MK_COMB (@lem6917358 y) (@lem6917472 z)). Qed.
Lemma lem6917474 (y : int) (z : int) : (term367 y z) = term399.
Proof. exact (TRANS (@lem6917250 y z) (@lem6917473 y z)). Qed.
Lemma lem6917475 : term399 = term339.
Proof. exact (@lem1982721 term339). Qed.
Lemma lem6917476 (y : int) (z : int) : (term367 y z) = term339.
Proof. exact (TRANS (@lem6917474 y z) (@lem6917475)). Qed.
Lemma lem6917477 (x : int) (y : int) (z : int) : (term421 x y z) = term399.
Proof. exact (MK_COMB (@lem6917249 x) (@lem6917476 y z)). Qed.
Lemma lem6917478 (x : int) (y : int) (z : int) : (term420 x y z) = term399.
Proof. exact (TRANS (@lem6917141 x y z) (@lem6917477 x y z)). Qed.
Lemma lem6917479 : term399 = term339.
Proof. exact (@lem1982721 term339). Qed.
Lemma lem6917480 (x : int) (y : int) (z : int) : (term420 x y z) = term339.
Proof. exact (TRANS (@lem6917478 x y z) (@lem6917479)). Qed.
Lemma lem6917481 (x : int) (y : int) (z : int) : (term416 x y z) = term339.
Proof. exact (TRANS (@lem6917140 x y z) (@lem6917480 x y z)). Qed.
Lemma lem6917482 (x : int) (y : int) (z : int) : (term415 x y z) = term339.
Proof. exact (TRANS (@lem6917083 x y z) (@lem6917481 x y z)). Qed.
Lemma lem6917483 (x : int) (y : int) (z : int) : (term414 x y z) = term339.
Proof. exact (TRANS (@lem6917082 x y z) (@lem6917482 x y z)). Qed.
Lemma lem6917484 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6917485 (x : int) (y : int) (z : int) : (term422 x y z) = term401.
Proof. exact (MK_COMB (@lem6917484) (@lem6917483 x y z)). Qed.
Lemma lem6917486 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem6917487 (x : int) (y : int) (z : int) : (term409 x y z) = term402.
Proof. exact (MK_COMB (@lem6917485 x y z) (@lem6917486)). Qed.
Lemma lem6917488 (x : int) (y : int) (z : int) : (term137 x y z) = term402.
Proof. exact (TRANS (@lem6917035 x y z) (@lem6917487 x y z)). Qed.
Lemma lem6917489 (x : int) (y : int) : (term246 x y) = term403.
Proof. exact (fun_ext (fun z : int => @lem6917488 x y z)). Qed.
Lemma lem6917490 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6917491 (x : int) (y : int) : (term257 x y) = term404.
Proof. exact (MK_COMB (@lem6917490) (@lem6917489 x y)). Qed.
Lemma lem6917492 (x : int) : (term268 x) = term405.
Proof. exact (fun_ext (fun y : int => @lem6917491 x y)). Qed.
Lemma lem6917493 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6917494 (x : int) : (term279 x) = term406.
Proof. exact (MK_COMB (@lem6917493) (@lem6917492 x)). Qed.
Lemma lem6917495 : term290 = term423.
Proof. exact (fun_ext (fun x : int => @lem6917494 x)). Qed.
Lemma lem6917496 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6917497 : term301 = term424.
Proof. exact (MK_COMB (@lem6917496) (@lem6917495)). Qed.
Lemma lem6917498 (x : int) (y : int) (z : int) : (term150 x y z) = (term425 x y z).
Proof. exact (@lem1988287 (term128 x y z) (term147 x y z)). Qed.
Lemma lem6917499 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem6917516 (x : int) (y : int) (z : int) : (term136 x y z) = (term128 x y z).
Proof. exact (@lem1982755 (real_of_int x) (real_of_int y) (real_of_int z)). Qed.
Lemma lem6917517 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917518 (x : int) (y : int) (z : int) : (term146 x y z) = (term130 x y z).
Proof. exact (MK_COMB (@lem6917517) (@lem6917516 x y z)). Qed.
Lemma lem6917519 (x : int) (y : int) (z : int) : (term147 x y z) = (term131 x y z).
Proof. exact (MK_COMB (@lem6917518 x y z) (@lem6917499)). Qed.
Lemma lem6917520 (x : int) (y : int) (z : int) : (term131 x y z) = (term410 x y z).
Proof. exact (@lem1982755 (real_of_int x) (term98 y z) term106). Qed.
Lemma lem6917525 (y : int) (z : int) : (term108 y z) = (term332 y z).
Proof. exact (@lem1982755 (real_of_int y) (real_of_int z) term106). Qed.
Lemma lem6917526 (x : int) : (term127 x) = (term127 x).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem6917527 (x : int) (y : int) (z : int) : (term410 x y z) = (term411 x y z).
Proof. exact (MK_COMB (@lem6917526 x) (@lem6917525 y z)). Qed.
Lemma lem6917528 (x : int) (y : int) (z : int) : (term131 x y z) = (term411 x y z).
Proof. exact (TRANS (@lem6917520 x y z) (@lem6917527 x y z)). Qed.
Lemma lem6917529 (x : int) (y : int) (z : int) : (term147 x y z) = (term411 x y z).
Proof. exact (TRANS (@lem6917519 x y z) (@lem6917528 x y z)). Qed.
Lemma lem6917544 (x : int) (y : int) (z : int) : (term413 x y z) = (term413 x y z).
Proof. exact (eq_refl (term413 x y z)). Qed.
Lemma lem6917545 (x : int) (y : int) (z : int) : (term426 x y z) = (term415 x y z).
Proof. exact (MK_COMB (@lem6917544 x y z) (@lem6917529 x y z)). Qed.
Lemma lem6917546 (x : int) (y : int) (z : int) : (term415 x y z) = (term416 x y z).
Proof. exact (@lem1982792 (term128 x y z) (term411 x y z)). Qed.
Lemma lem6917547 (x : int) (y : int) (z : int) : (term417 x y z) = (term418 x y z).
Proof. exact (@lem1982781 (real_of_int x) term339 (term332 y z)). Qed.
Lemma lem6917548 (y : int) (z : int) : (term337 y z) = (term338 y z).
Proof. exact (@lem1982781 (real_of_int y) term339 (term184 z)). Qed.
Lemma lem6917549 (z : int) : (term340 z) = (term341 z).
Proof. exact (@lem1982781 (real_of_int z) term339 term106). Qed.
Lemma lem6917551 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6917552 : term106 = term343.
Proof. exact (@lem6917551 term107). Qed.
Lemma lem6917554 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6917555 : term339 = term346.
Proof. exact (@lem6917554 term107). Qed.
Lemma lem6917556 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6917557 : term347 = term348.
Proof. exact (MK_COMB (@lem6917556) (@lem6917555)). Qed.
Lemma lem6917558 : term349 = term350.
Proof. exact (MK_COMB (@lem6917557) (@lem6917552)). Qed.
Lemma lem6917559 : term350 = term351.
Proof. exact (@lem1981613 term339 term106 term106 term106). Qed.
Lemma lem6917561 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6917562 : term354 = term355.
Proof. exact (@lem6917561 term107 term107). Qed.
Lemma lem6917563 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917564 : term357 = term107.
Proof. exact (EQ_MP (@lem6917563) (@lem940073)). Qed.
Lemma lem6917565 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917566 : term355 = term106.
Proof. exact (MK_COMB (@lem6917565) (@lem6917564)). Qed.
Lemma lem6917567 : term354 = term106.
Proof. exact (TRANS (@lem6917562) (@lem6917566)). Qed.
Lemma lem6917569 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6917570 : term349 = term360.
Proof. exact (@lem6917569 term107 term107). Qed.
Lemma lem6917571 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917572 : term357 = term107.
Proof. exact (EQ_MP (@lem6917571) (@lem940073)). Qed.
Lemma lem6917573 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917574 : term355 = term106.
Proof. exact (MK_COMB (@lem6917573) (@lem6917572)). Qed.
Lemma lem6917575 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6917576 : term360 = term339.
Proof. exact (MK_COMB (@lem6917575) (@lem6917574)). Qed.
Lemma lem6917577 : term349 = term339.
Proof. exact (TRANS (@lem6917570) (@lem6917576)). Qed.
Lemma lem6917578 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6917579 : term361 = term362.
Proof. exact (MK_COMB (@lem6917578) (@lem6917577)). Qed.
Lemma lem6917580 : term351 = term346.
Proof. exact (MK_COMB (@lem6917579) (@lem6917567)). Qed.
Lemma lem6917581 : term350 = term346.
Proof. exact (TRANS (@lem6917559) (@lem6917580)). Qed.
Lemma lem6917582 : term349 = term346.
Proof. exact (TRANS (@lem6917558) (@lem6917581)). Qed.
Lemma lem6917584 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6917585 : term346 = term339.
Proof. exact (@lem6917584 term339). Qed.
Lemma lem6917586 : term349 = term339.
Proof. exact (TRANS (@lem6917582) (@lem6917585)). Qed.
Lemma lem6917589 (z : int) : (term364 z) = (term364 z).
Proof. exact (eq_refl (term364 z)). Qed.
Lemma lem6917590 (z : int) : (term341 z) = (term365 z).
Proof. exact (MK_COMB (@lem6917589 z) (@lem6917586)). Qed.
Lemma lem6917591 (z : int) : (term340 z) = (term365 z).
Proof. exact (TRANS (@lem6917549 z) (@lem6917590 z)). Qed.
Lemma lem6917594 (y : int) : (term364 y) = (term364 y).
Proof. exact (eq_refl (term364 y)). Qed.
Lemma lem6917595 (y : int) (z : int) : (term338 y z) = (term366 y z).
Proof. exact (MK_COMB (@lem6917594 y) (@lem6917591 z)). Qed.
Lemma lem6917596 (y : int) (z : int) : (term337 y z) = (term366 y z).
Proof. exact (TRANS (@lem6917548 y z) (@lem6917595 y z)). Qed.
Lemma lem6917599 (x : int) : (term364 x) = (term364 x).
Proof. exact (eq_refl (term364 x)). Qed.
Lemma lem6917600 (x : int) (y : int) (z : int) : (term418 x y z) = (term419 x y z).
Proof. exact (MK_COMB (@lem6917599 x) (@lem6917596 y z)). Qed.
Lemma lem6917601 (x : int) (y : int) (z : int) : (term417 x y z) = (term419 x y z).
Proof. exact (TRANS (@lem6917547 x y z) (@lem6917600 x y z)). Qed.
Lemma lem6917602 (x : int) (y : int) (z : int) : (term130 x y z) = (term130 x y z).
Proof. exact (eq_refl (term130 x y z)). Qed.
Lemma lem6917603 (x : int) (y : int) (z : int) : (term416 x y z) = (term420 x y z).
Proof. exact (MK_COMB (@lem6917602 x y z) (@lem6917601 x y z)). Qed.
Lemma lem6917604 (x : int) (y : int) (z : int) : (term420 x y z) = (term421 x y z).
Proof. exact (@lem1982753 (real_of_int x) (term369 x) (term98 y z) (term366 y z)). Qed.
Lemma lem6917605 (x : int) : (term370 x) = (term371 x).
Proof. exact (@lem1982715 term339 (real_of_int x)). Qed.
Lemma lem6917607 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6917608 : term106 = term343.
Proof. exact (@lem6917607 term107). Qed.
Lemma lem6917610 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6917611 : term339 = term346.
Proof. exact (@lem6917610 term107). Qed.
Lemma lem6917612 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917613 : term372 = term373.
Proof. exact (MK_COMB (@lem6917612) (@lem6917611)). Qed.
Lemma lem6917614 : term374 = term375.
Proof. exact (MK_COMB (@lem6917613) (@lem6917608)). Qed.
Lemma lem6917615 : term376.
Proof. exact (@lem1981473 term339 term106 term106 term106 term167 term106). Qed.
Lemma lem6917617 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917618 : term378 = term379.
Proof. exact (@lem6917617 (NUMERAL 0) term107). Qed.
Lemma lem6917619 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917620 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917621 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917620 h1) (fun h1 : term379 = True => @lem6917619)). Qed.
Lemma lem6917622 : term379 = True.
Proof. exact (EQ_MP (@lem6917621) (@lem6917619)). Qed.
Lemma lem6917623 : term378 = True.
Proof. exact (TRANS (@lem6917618) (@lem6917622)). Qed.
Lemma lem6917624 : True = term378.
Proof. exact (SYM (@lem6917623)). Qed.
Lemma lem6917625 : term378.
Proof. exact (EQ_MP (@lem6917624) (@lem0)). Qed.
Lemma lem6917626 : term381.
Proof. exact (@lem6917615 (@lem6917625)). Qed.
Lemma lem6917628 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917629 : term378 = term379.
Proof. exact (@lem6917628 (NUMERAL 0) term107). Qed.
Lemma lem6917630 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917631 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917632 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917631 h1) (fun h1 : term379 = True => @lem6917630)). Qed.
Lemma lem6917633 : term379 = True.
Proof. exact (EQ_MP (@lem6917632) (@lem6917630)). Qed.
Lemma lem6917634 : term378 = True.
Proof. exact (TRANS (@lem6917629) (@lem6917633)). Qed.
Lemma lem6917635 : True = term378.
Proof. exact (SYM (@lem6917634)). Qed.
Lemma lem6917636 : term378.
Proof. exact (EQ_MP (@lem6917635) (@lem0)). Qed.
Lemma lem6917637 : term382.
Proof. exact (@lem6917626 (@lem6917636)). Qed.
Lemma lem6917639 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917640 : term378 = term379.
Proof. exact (@lem6917639 (NUMERAL 0) term107). Qed.
Lemma lem6917641 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917642 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917643 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917642 h1) (fun h1 : term379 = True => @lem6917641)). Qed.
Lemma lem6917644 : term379 = True.
Proof. exact (EQ_MP (@lem6917643) (@lem6917641)). Qed.
Lemma lem6917645 : term378 = True.
Proof. exact (TRANS (@lem6917640) (@lem6917644)). Qed.
Lemma lem6917646 : True = term378.
Proof. exact (SYM (@lem6917645)). Qed.
Lemma lem6917647 : term378.
Proof. exact (EQ_MP (@lem6917646) (@lem0)). Qed.
Lemma lem6917648 : term383.
Proof. exact (@lem6917637 (@lem6917647)). Qed.
Lemma lem6917650 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6917651 : term354 = term355.
Proof. exact (@lem6917650 term107 term107). Qed.
Lemma lem6917652 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917653 : term357 = term107.
Proof. exact (EQ_MP (@lem6917652) (@lem940073)). Qed.
Lemma lem6917654 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917655 : term355 = term106.
Proof. exact (MK_COMB (@lem6917654) (@lem6917653)). Qed.
Lemma lem6917656 : term354 = term106.
Proof. exact (TRANS (@lem6917651) (@lem6917655)). Qed.
Lemma lem6917658 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6917659 : term349 = term360.
Proof. exact (@lem6917658 term107 term107). Qed.
Lemma lem6917660 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917661 : term357 = term107.
Proof. exact (EQ_MP (@lem6917660) (@lem940073)). Qed.
Lemma lem6917662 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917663 : term355 = term106.
Proof. exact (MK_COMB (@lem6917662) (@lem6917661)). Qed.
Lemma lem6917664 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6917665 : term360 = term339.
Proof. exact (MK_COMB (@lem6917664) (@lem6917663)). Qed.
Lemma lem6917666 : term349 = term339.
Proof. exact (TRANS (@lem6917659) (@lem6917665)). Qed.
Lemma lem6917667 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917668 : term384 = term372.
Proof. exact (MK_COMB (@lem6917667) (@lem6917666)). Qed.
Lemma lem6917669 : term385 = term374.
Proof. exact (MK_COMB (@lem6917668) (@lem6917656)). Qed.
Lemma lem6917671 (m : nat) : (term386 m) = term167.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6917672 : term374 = term167.
Proof. exact (@lem6917671 term107). Qed.
Lemma lem6917673 : term385 = term167.
Proof. exact (TRANS (@lem6917669) (@lem6917672)). Qed.
Lemma lem6917674 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6917675 : term387 = term388.
Proof. exact (MK_COMB (@lem6917674) (@lem6917673)). Qed.
Lemma lem6917676 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem6917677 : term389 = term390.
Proof. exact (MK_COMB (@lem6917675) (@lem6917676)). Qed.
Lemma lem6917679 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6917680 : term390 = term167.
Proof. exact (@lem6917679 term107). Qed.
Lemma lem6917681 : term389 = term167.
Proof. exact (TRANS (@lem6917677) (@lem6917680)). Qed.
Lemma lem6917683 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6917684 : term354 = term355.
Proof. exact (@lem6917683 term107 term107). Qed.
Lemma lem6917685 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917686 : term357 = term107.
Proof. exact (EQ_MP (@lem6917685) (@lem940073)). Qed.
Lemma lem6917687 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917688 : term355 = term106.
Proof. exact (MK_COMB (@lem6917687) (@lem6917686)). Qed.
Lemma lem6917689 : term354 = term106.
Proof. exact (TRANS (@lem6917684) (@lem6917688)). Qed.
Lemma lem6917690 : term388 = term388.
Proof. exact (eq_refl term388). Qed.
Lemma lem6917691 : term392 = term390.
Proof. exact (MK_COMB (@lem6917690) (@lem6917689)). Qed.
Lemma lem6917693 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6917694 : term390 = term167.
Proof. exact (@lem6917693 term107). Qed.
Lemma lem6917695 : term392 = term167.
Proof. exact (TRANS (@lem6917691) (@lem6917694)). Qed.
Lemma lem6917696 : term167 = term392.
Proof. exact (SYM (@lem6917695)). Qed.
Lemma lem6917697 : term389 = term392.
Proof. exact (TRANS (@lem6917681) (@lem6917696)). Qed.
Lemma lem6917698 : term375 = term393.
Proof. exact (@lem6917648 (@lem6917697)). Qed.
Lemma lem6917699 : term374 = term393.
Proof. exact (TRANS (@lem6917614) (@lem6917698)). Qed.
Lemma lem6917701 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6917702 : term393 = term167.
Proof. exact (@lem6917701 term167). Qed.
Lemma lem6917703 : term374 = term167.
Proof. exact (TRANS (@lem6917699) (@lem6917702)). Qed.
Lemma lem6917704 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6917705 : term394 = term388.
Proof. exact (MK_COMB (@lem6917704) (@lem6917703)). Qed.
Lemma lem6917706 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem6917707 (x : int) : (term371 x) = (term395 x).
Proof. exact (MK_COMB (@lem6917705) (@lem6917706 x)). Qed.
Lemma lem6917708 (x : int) : (term370 x) = (term395 x).
Proof. exact (TRANS (@lem6917605 x) (@lem6917707 x)). Qed.
Lemma lem6917709 (x : int) : (term395 x) = term167.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem6917710 (x : int) : (term370 x) = term167.
Proof. exact (TRANS (@lem6917708 x) (@lem6917709 x)). Qed.
Lemma lem6917711 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917712 (x : int) : (term396 x) = term169.
Proof. exact (MK_COMB (@lem6917711) (@lem6917710 x)). Qed.
Lemma lem6917713 (y : int) (z : int) : (term367 y z) = (term368 y z).
Proof. exact (@lem1982753 (real_of_int y) (term369 y) (real_of_int z) (term365 z)). Qed.
Lemma lem6917714 (y : int) : (term370 y) = (term371 y).
Proof. exact (@lem1982715 term339 (real_of_int y)). Qed.
Lemma lem6917716 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6917717 : term106 = term343.
Proof. exact (@lem6917716 term107). Qed.
Lemma lem6917719 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6917720 : term339 = term346.
Proof. exact (@lem6917719 term107). Qed.
Lemma lem6917721 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917722 : term372 = term373.
Proof. exact (MK_COMB (@lem6917721) (@lem6917720)). Qed.
Lemma lem6917723 : term374 = term375.
Proof. exact (MK_COMB (@lem6917722) (@lem6917717)). Qed.
Lemma lem6917724 : term376.
Proof. exact (@lem1981473 term339 term106 term106 term106 term167 term106). Qed.
Lemma lem6917726 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917727 : term378 = term379.
Proof. exact (@lem6917726 (NUMERAL 0) term107). Qed.
Lemma lem6917728 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917729 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917730 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917729 h1) (fun h1 : term379 = True => @lem6917728)). Qed.
Lemma lem6917731 : term379 = True.
Proof. exact (EQ_MP (@lem6917730) (@lem6917728)). Qed.
Lemma lem6917732 : term378 = True.
Proof. exact (TRANS (@lem6917727) (@lem6917731)). Qed.
Lemma lem6917733 : True = term378.
Proof. exact (SYM (@lem6917732)). Qed.
Lemma lem6917734 : term378.
Proof. exact (EQ_MP (@lem6917733) (@lem0)). Qed.
Lemma lem6917735 : term381.
Proof. exact (@lem6917724 (@lem6917734)). Qed.
Lemma lem6917737 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917738 : term378 = term379.
Proof. exact (@lem6917737 (NUMERAL 0) term107). Qed.
Lemma lem6917739 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917740 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917741 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917740 h1) (fun h1 : term379 = True => @lem6917739)). Qed.
Lemma lem6917742 : term379 = True.
Proof. exact (EQ_MP (@lem6917741) (@lem6917739)). Qed.
Lemma lem6917743 : term378 = True.
Proof. exact (TRANS (@lem6917738) (@lem6917742)). Qed.
Lemma lem6917744 : True = term378.
Proof. exact (SYM (@lem6917743)). Qed.
Lemma lem6917745 : term378.
Proof. exact (EQ_MP (@lem6917744) (@lem0)). Qed.
Lemma lem6917746 : term382.
Proof. exact (@lem6917735 (@lem6917745)). Qed.
Lemma lem6917748 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917749 : term378 = term379.
Proof. exact (@lem6917748 (NUMERAL 0) term107). Qed.
Lemma lem6917750 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917751 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917752 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917751 h1) (fun h1 : term379 = True => @lem6917750)). Qed.
Lemma lem6917753 : term379 = True.
Proof. exact (EQ_MP (@lem6917752) (@lem6917750)). Qed.
Lemma lem6917754 : term378 = True.
Proof. exact (TRANS (@lem6917749) (@lem6917753)). Qed.
Lemma lem6917755 : True = term378.
Proof. exact (SYM (@lem6917754)). Qed.
Lemma lem6917756 : term378.
Proof. exact (EQ_MP (@lem6917755) (@lem0)). Qed.
Lemma lem6917757 : term383.
Proof. exact (@lem6917746 (@lem6917756)). Qed.
Lemma lem6917759 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6917760 : term354 = term355.
Proof. exact (@lem6917759 term107 term107). Qed.
Lemma lem6917761 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917762 : term357 = term107.
Proof. exact (EQ_MP (@lem6917761) (@lem940073)). Qed.
Lemma lem6917763 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917764 : term355 = term106.
Proof. exact (MK_COMB (@lem6917763) (@lem6917762)). Qed.
Lemma lem6917765 : term354 = term106.
Proof. exact (TRANS (@lem6917760) (@lem6917764)). Qed.
Lemma lem6917767 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6917768 : term349 = term360.
Proof. exact (@lem6917767 term107 term107). Qed.
Lemma lem6917769 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917770 : term357 = term107.
Proof. exact (EQ_MP (@lem6917769) (@lem940073)). Qed.
Lemma lem6917771 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917772 : term355 = term106.
Proof. exact (MK_COMB (@lem6917771) (@lem6917770)). Qed.
Lemma lem6917773 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6917774 : term360 = term339.
Proof. exact (MK_COMB (@lem6917773) (@lem6917772)). Qed.
Lemma lem6917775 : term349 = term339.
Proof. exact (TRANS (@lem6917768) (@lem6917774)). Qed.
Lemma lem6917776 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917777 : term384 = term372.
Proof. exact (MK_COMB (@lem6917776) (@lem6917775)). Qed.
Lemma lem6917778 : term385 = term374.
Proof. exact (MK_COMB (@lem6917777) (@lem6917765)). Qed.
Lemma lem6917780 (m : nat) : (term386 m) = term167.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6917781 : term374 = term167.
Proof. exact (@lem6917780 term107). Qed.
Lemma lem6917782 : term385 = term167.
Proof. exact (TRANS (@lem6917778) (@lem6917781)). Qed.
Lemma lem6917783 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6917784 : term387 = term388.
Proof. exact (MK_COMB (@lem6917783) (@lem6917782)). Qed.
Lemma lem6917785 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem6917786 : term389 = term390.
Proof. exact (MK_COMB (@lem6917784) (@lem6917785)). Qed.
Lemma lem6917788 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6917789 : term390 = term167.
Proof. exact (@lem6917788 term107). Qed.
Lemma lem6917790 : term389 = term167.
Proof. exact (TRANS (@lem6917786) (@lem6917789)). Qed.
Lemma lem6917792 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6917793 : term354 = term355.
Proof. exact (@lem6917792 term107 term107). Qed.
Lemma lem6917794 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917795 : term357 = term107.
Proof. exact (EQ_MP (@lem6917794) (@lem940073)). Qed.
Lemma lem6917796 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917797 : term355 = term106.
Proof. exact (MK_COMB (@lem6917796) (@lem6917795)). Qed.
Lemma lem6917798 : term354 = term106.
Proof. exact (TRANS (@lem6917793) (@lem6917797)). Qed.
Lemma lem6917799 : term388 = term388.
Proof. exact (eq_refl term388). Qed.
Lemma lem6917800 : term392 = term390.
Proof. exact (MK_COMB (@lem6917799) (@lem6917798)). Qed.
Lemma lem6917802 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6917803 : term390 = term167.
Proof. exact (@lem6917802 term107). Qed.
Lemma lem6917804 : term392 = term167.
Proof. exact (TRANS (@lem6917800) (@lem6917803)). Qed.
Lemma lem6917805 : term167 = term392.
Proof. exact (SYM (@lem6917804)). Qed.
Lemma lem6917806 : term389 = term392.
Proof. exact (TRANS (@lem6917790) (@lem6917805)). Qed.
Lemma lem6917807 : term375 = term393.
Proof. exact (@lem6917757 (@lem6917806)). Qed.
Lemma lem6917808 : term374 = term393.
Proof. exact (TRANS (@lem6917723) (@lem6917807)). Qed.
Lemma lem6917810 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6917811 : term393 = term167.
Proof. exact (@lem6917810 term167). Qed.
Lemma lem6917812 : term374 = term167.
Proof. exact (TRANS (@lem6917808) (@lem6917811)). Qed.
Lemma lem6917813 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6917814 : term394 = term388.
Proof. exact (MK_COMB (@lem6917813) (@lem6917812)). Qed.
Lemma lem6917815 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem6917816 (y : int) : (term371 y) = (term395 y).
Proof. exact (MK_COMB (@lem6917814) (@lem6917815 y)). Qed.
Lemma lem6917817 (y : int) : (term370 y) = (term395 y).
Proof. exact (TRANS (@lem6917714 y) (@lem6917816 y)). Qed.
Lemma lem6917818 (y : int) : (term395 y) = term167.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem6917819 (y : int) : (term370 y) = term167.
Proof. exact (TRANS (@lem6917817 y) (@lem6917818 y)). Qed.
Lemma lem6917820 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917821 (y : int) : (term396 y) = term169.
Proof. exact (MK_COMB (@lem6917820) (@lem6917819 y)). Qed.
Lemma lem6917822 (z : int) : (term397 z) = (term398 z).
Proof. exact (@lem1982763 (real_of_int z) (term369 z) term339). Qed.
Lemma lem6917823 (z : int) : (term370 z) = (term371 z).
Proof. exact (@lem1982715 term339 (real_of_int z)). Qed.
Lemma lem6917825 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6917826 : term106 = term343.
Proof. exact (@lem6917825 term107). Qed.
Lemma lem6917828 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6917829 : term339 = term346.
Proof. exact (@lem6917828 term107). Qed.
Lemma lem6917830 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917831 : term372 = term373.
Proof. exact (MK_COMB (@lem6917830) (@lem6917829)). Qed.
Lemma lem6917832 : term374 = term375.
Proof. exact (MK_COMB (@lem6917831) (@lem6917826)). Qed.
Lemma lem6917833 : term376.
Proof. exact (@lem1981473 term339 term106 term106 term106 term167 term106). Qed.
Lemma lem6917835 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917836 : term378 = term379.
Proof. exact (@lem6917835 (NUMERAL 0) term107). Qed.
Lemma lem6917837 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917838 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917839 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917838 h1) (fun h1 : term379 = True => @lem6917837)). Qed.
Lemma lem6917840 : term379 = True.
Proof. exact (EQ_MP (@lem6917839) (@lem6917837)). Qed.
Lemma lem6917841 : term378 = True.
Proof. exact (TRANS (@lem6917836) (@lem6917840)). Qed.
Lemma lem6917842 : True = term378.
Proof. exact (SYM (@lem6917841)). Qed.
Lemma lem6917843 : term378.
Proof. exact (EQ_MP (@lem6917842) (@lem0)). Qed.
Lemma lem6917844 : term381.
Proof. exact (@lem6917833 (@lem6917843)). Qed.
Lemma lem6917846 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917847 : term378 = term379.
Proof. exact (@lem6917846 (NUMERAL 0) term107). Qed.
Lemma lem6917848 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917849 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917850 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917849 h1) (fun h1 : term379 = True => @lem6917848)). Qed.
Lemma lem6917851 : term379 = True.
Proof. exact (EQ_MP (@lem6917850) (@lem6917848)). Qed.
Lemma lem6917852 : term378 = True.
Proof. exact (TRANS (@lem6917847) (@lem6917851)). Qed.
Lemma lem6917853 : True = term378.
Proof. exact (SYM (@lem6917852)). Qed.
Lemma lem6917854 : term378.
Proof. exact (EQ_MP (@lem6917853) (@lem0)). Qed.
Lemma lem6917855 : term382.
Proof. exact (@lem6917844 (@lem6917854)). Qed.
Lemma lem6917857 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6917858 : term378 = term379.
Proof. exact (@lem6917857 (NUMERAL 0) term107). Qed.
Lemma lem6917859 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6917860 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6917861 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6917860 h1) (fun h1 : term379 = True => @lem6917859)). Qed.
Lemma lem6917862 : term379 = True.
Proof. exact (EQ_MP (@lem6917861) (@lem6917859)). Qed.
Lemma lem6917863 : term378 = True.
Proof. exact (TRANS (@lem6917858) (@lem6917862)). Qed.
Lemma lem6917864 : True = term378.
Proof. exact (SYM (@lem6917863)). Qed.
Lemma lem6917865 : term378.
Proof. exact (EQ_MP (@lem6917864) (@lem0)). Qed.
Lemma lem6917866 : term383.
Proof. exact (@lem6917855 (@lem6917865)). Qed.
Lemma lem6917868 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6917869 : term354 = term355.
Proof. exact (@lem6917868 term107 term107). Qed.
Lemma lem6917870 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917871 : term357 = term107.
Proof. exact (EQ_MP (@lem6917870) (@lem940073)). Qed.
Lemma lem6917872 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917873 : term355 = term106.
Proof. exact (MK_COMB (@lem6917872) (@lem6917871)). Qed.
Lemma lem6917874 : term354 = term106.
Proof. exact (TRANS (@lem6917869) (@lem6917873)). Qed.
Lemma lem6917876 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6917877 : term349 = term360.
Proof. exact (@lem6917876 term107 term107). Qed.
Lemma lem6917878 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917879 : term357 = term107.
Proof. exact (EQ_MP (@lem6917878) (@lem940073)). Qed.
Lemma lem6917880 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917881 : term355 = term106.
Proof. exact (MK_COMB (@lem6917880) (@lem6917879)). Qed.
Lemma lem6917882 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6917883 : term360 = term339.
Proof. exact (MK_COMB (@lem6917882) (@lem6917881)). Qed.
Lemma lem6917884 : term349 = term339.
Proof. exact (TRANS (@lem6917877) (@lem6917883)). Qed.
Lemma lem6917885 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917886 : term384 = term372.
Proof. exact (MK_COMB (@lem6917885) (@lem6917884)). Qed.
Lemma lem6917887 : term385 = term374.
Proof. exact (MK_COMB (@lem6917886) (@lem6917874)). Qed.
Lemma lem6917889 (m : nat) : (term386 m) = term167.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6917890 : term374 = term167.
Proof. exact (@lem6917889 term107). Qed.
Lemma lem6917891 : term385 = term167.
Proof. exact (TRANS (@lem6917887) (@lem6917890)). Qed.
Lemma lem6917892 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6917893 : term387 = term388.
Proof. exact (MK_COMB (@lem6917892) (@lem6917891)). Qed.
Lemma lem6917894 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem6917895 : term389 = term390.
Proof. exact (MK_COMB (@lem6917893) (@lem6917894)). Qed.
Lemma lem6917897 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6917898 : term390 = term167.
Proof. exact (@lem6917897 term107). Qed.
Lemma lem6917899 : term389 = term167.
Proof. exact (TRANS (@lem6917895) (@lem6917898)). Qed.
Lemma lem6917901 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6917902 : term354 = term355.
Proof. exact (@lem6917901 term107 term107). Qed.
Lemma lem6917903 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917904 : term357 = term107.
Proof. exact (EQ_MP (@lem6917903) (@lem940073)). Qed.
Lemma lem6917905 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6917906 : term355 = term106.
Proof. exact (MK_COMB (@lem6917905) (@lem6917904)). Qed.
Lemma lem6917907 : term354 = term106.
Proof. exact (TRANS (@lem6917902) (@lem6917906)). Qed.
Lemma lem6917908 : term388 = term388.
Proof. exact (eq_refl term388). Qed.
Lemma lem6917909 : term392 = term390.
Proof. exact (MK_COMB (@lem6917908) (@lem6917907)). Qed.
Lemma lem6917911 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6917912 : term390 = term167.
Proof. exact (@lem6917911 term107). Qed.
Lemma lem6917913 : term392 = term167.
Proof. exact (TRANS (@lem6917909) (@lem6917912)). Qed.
Lemma lem6917914 : term167 = term392.
Proof. exact (SYM (@lem6917913)). Qed.
Lemma lem6917915 : term389 = term392.
Proof. exact (TRANS (@lem6917899) (@lem6917914)). Qed.
Lemma lem6917916 : term375 = term393.
Proof. exact (@lem6917866 (@lem6917915)). Qed.
Lemma lem6917917 : term374 = term393.
Proof. exact (TRANS (@lem6917832) (@lem6917916)). Qed.
Lemma lem6917919 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6917920 : term393 = term167.
Proof. exact (@lem6917919 term167). Qed.
Lemma lem6917921 : term374 = term167.
Proof. exact (TRANS (@lem6917917) (@lem6917920)). Qed.
Lemma lem6917922 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6917923 : term394 = term388.
Proof. exact (MK_COMB (@lem6917922) (@lem6917921)). Qed.
Lemma lem6917924 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem6917925 (z : int) : (term371 z) = (term395 z).
Proof. exact (MK_COMB (@lem6917923) (@lem6917924 z)). Qed.
Lemma lem6917926 (z : int) : (term370 z) = (term395 z).
Proof. exact (TRANS (@lem6917823 z) (@lem6917925 z)). Qed.
Lemma lem6917927 (z : int) : (term395 z) = term167.
Proof. exact (@lem1982719 (real_of_int z)). Qed.
Lemma lem6917928 (z : int) : (term370 z) = term167.
Proof. exact (TRANS (@lem6917926 z) (@lem6917927 z)). Qed.
Lemma lem6917929 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917930 (z : int) : (term396 z) = term169.
Proof. exact (MK_COMB (@lem6917929) (@lem6917928 z)). Qed.
Lemma lem6917931 : term339 = term339.
Proof. exact (eq_refl term339). Qed.
Lemma lem6917932 (z : int) : (term398 z) = term399.
Proof. exact (MK_COMB (@lem6917930 z) (@lem6917931)). Qed.
Lemma lem6917933 (z : int) : (term397 z) = term399.
Proof. exact (TRANS (@lem6917822 z) (@lem6917932 z)). Qed.
Lemma lem6917934 : term399 = term339.
Proof. exact (@lem1982721 term339). Qed.
Lemma lem6917935 (z : int) : (term397 z) = term339.
Proof. exact (TRANS (@lem6917933 z) (@lem6917934)). Qed.
Lemma lem6917936 (y : int) (z : int) : (term368 y z) = term399.
Proof. exact (MK_COMB (@lem6917821 y) (@lem6917935 z)). Qed.
Lemma lem6917937 (y : int) (z : int) : (term367 y z) = term399.
Proof. exact (TRANS (@lem6917713 y z) (@lem6917936 y z)). Qed.
Lemma lem6917938 : term399 = term339.
Proof. exact (@lem1982721 term339). Qed.
Lemma lem6917939 (y : int) (z : int) : (term367 y z) = term339.
Proof. exact (TRANS (@lem6917937 y z) (@lem6917938)). Qed.
Lemma lem6917940 (x : int) (y : int) (z : int) : (term421 x y z) = term399.
Proof. exact (MK_COMB (@lem6917712 x) (@lem6917939 y z)). Qed.
Lemma lem6917941 (x : int) (y : int) (z : int) : (term420 x y z) = term399.
Proof. exact (TRANS (@lem6917604 x y z) (@lem6917940 x y z)). Qed.
Lemma lem6917942 : term399 = term339.
Proof. exact (@lem1982721 term339). Qed.
Lemma lem6917943 (x : int) (y : int) (z : int) : (term420 x y z) = term339.
Proof. exact (TRANS (@lem6917941 x y z) (@lem6917942)). Qed.
Lemma lem6917944 (x : int) (y : int) (z : int) : (term416 x y z) = term339.
Proof. exact (TRANS (@lem6917603 x y z) (@lem6917943 x y z)). Qed.
Lemma lem6917945 (x : int) (y : int) (z : int) : (term415 x y z) = term339.
Proof. exact (TRANS (@lem6917546 x y z) (@lem6917944 x y z)). Qed.
Lemma lem6917946 (x : int) (y : int) (z : int) : (term426 x y z) = term339.
Proof. exact (TRANS (@lem6917545 x y z) (@lem6917945 x y z)). Qed.
Lemma lem6917947 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6917948 (x : int) (y : int) (z : int) : (term427 x y z) = term401.
Proof. exact (MK_COMB (@lem6917947) (@lem6917946 x y z)). Qed.
Lemma lem6917949 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem6917950 (x : int) (y : int) (z : int) : (term425 x y z) = term402.
Proof. exact (MK_COMB (@lem6917948 x y z) (@lem6917949)). Qed.
Lemma lem6917951 (x : int) (y : int) (z : int) : (term150 x y z) = term402.
Proof. exact (TRANS (@lem6917498 x y z) (@lem6917950 x y z)). Qed.
Lemma lem6917952 (x : int) (y : int) : (term247 x y) = term403.
Proof. exact (fun_ext (fun z : int => @lem6917951 x y z)). Qed.
Lemma lem6917953 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6917954 (x : int) (y : int) : (term262 x y) = term404.
Proof. exact (MK_COMB (@lem6917953) (@lem6917952 x y)). Qed.
Lemma lem6917955 (x : int) : (term269 x) = term405.
Proof. exact (fun_ext (fun y : int => @lem6917954 x y)). Qed.
Lemma lem6917956 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6917957 (x : int) : (term284 x) = term406.
Proof. exact (MK_COMB (@lem6917956) (@lem6917955 x)). Qed.
Lemma lem6917958 : term291 = term423.
Proof. exact (fun_ext (fun x : int => @lem6917957 x)). Qed.
Lemma lem6917959 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6917960 : term306 = term424.
Proof. exact (MK_COMB (@lem6917959) (@lem6917958)). Qed.
Lemma lem6917961 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6917962 : term303 = term428.
Proof. exact (MK_COMB (@lem6917961) (@lem6917497)). Qed.
Lemma lem6917963 : term307 = term429.
Proof. exact (MK_COMB (@lem6917962) (@lem6917960)). Qed.
Lemma lem6917964 (x : int) : (term176 x) = (term430 x).
Proof. exact (@lem1988287 (real_of_int x) (term173 x)). Qed.
Lemma lem6917965 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem6917972 (x : int) : (term170 x) = (real_of_int x).
Proof. exact (@lem1982721 (real_of_int x)). Qed.
Lemma lem6917973 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6917974 (x : int) : (term172 x) = (term127 x).
Proof. exact (MK_COMB (@lem6917973) (@lem6917972 x)). Qed.
Lemma lem6917977 (x : int) : (term173 x) = (term184 x).
Proof. exact (MK_COMB (@lem6917974 x) (@lem6917965)). Qed.
Lemma lem6917980 (x : int) : (term431 x) = (term431 x).
Proof. exact (eq_refl (term431 x)). Qed.
Lemma lem6917981 (x : int) : (term432 x) = (term433 x).
Proof. exact (MK_COMB (@lem6917980 x) (@lem6917977 x)). Qed.
Lemma lem6917982 (x : int) : (term433 x) = (term434 x).
Proof. exact (@lem1982792 (real_of_int x) (term184 x)). Qed.
Lemma lem6917983 (x : int) : (term340 x) = (term341 x).
Proof. exact (@lem1982781 (real_of_int x) term339 term106). Qed.
Lemma lem6917985 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6917986 : term106 = term343.
Proof. exact (@lem6917985 term107). Qed.
Lemma lem6917988 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6917989 : term339 = term346.
Proof. exact (@lem6917988 term107). Qed.
Lemma lem6917990 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6917991 : term347 = term348.
Proof. exact (MK_COMB (@lem6917990) (@lem6917989)). Qed.
Lemma lem6917992 : term349 = term350.
Proof. exact (MK_COMB (@lem6917991) (@lem6917986)). Qed.
Lemma lem6917993 : term350 = term351.
Proof. exact (@lem1981613 term339 term106 term106 term106). Qed.
Lemma lem6917995 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6917996 : term354 = term355.
Proof. exact (@lem6917995 term107 term107). Qed.
Lemma lem6917997 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6917998 : term357 = term107.
Proof. exact (EQ_MP (@lem6917997) (@lem940073)). Qed.
Lemma lem6917999 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6918000 : term355 = term106.
Proof. exact (MK_COMB (@lem6917999) (@lem6917998)). Qed.
Lemma lem6918001 : term354 = term106.
Proof. exact (TRANS (@lem6917996) (@lem6918000)). Qed.
Lemma lem6918003 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6918004 : term349 = term360.
Proof. exact (@lem6918003 term107 term107). Qed.
Lemma lem6918005 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6918006 : term357 = term107.
Proof. exact (EQ_MP (@lem6918005) (@lem940073)). Qed.
Lemma lem6918007 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6918008 : term355 = term106.
Proof. exact (MK_COMB (@lem6918007) (@lem6918006)). Qed.
Lemma lem6918009 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6918010 : term360 = term339.
Proof. exact (MK_COMB (@lem6918009) (@lem6918008)). Qed.
Lemma lem6918011 : term349 = term339.
Proof. exact (TRANS (@lem6918004) (@lem6918010)). Qed.
Lemma lem6918012 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6918013 : term361 = term362.
Proof. exact (MK_COMB (@lem6918012) (@lem6918011)). Qed.
Lemma lem6918014 : term351 = term346.
Proof. exact (MK_COMB (@lem6918013) (@lem6918001)). Qed.
Lemma lem6918015 : term350 = term346.
Proof. exact (TRANS (@lem6917993) (@lem6918014)). Qed.
Lemma lem6918016 : term349 = term346.
Proof. exact (TRANS (@lem6917992) (@lem6918015)). Qed.
Lemma lem6918018 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6918019 : term346 = term339.
Proof. exact (@lem6918018 term339). Qed.
Lemma lem6918020 : term349 = term339.
Proof. exact (TRANS (@lem6918016) (@lem6918019)). Qed.
Lemma lem6918023 (x : int) : (term364 x) = (term364 x).
Proof. exact (eq_refl (term364 x)). Qed.
Lemma lem6918024 (x : int) : (term341 x) = (term365 x).
Proof. exact (MK_COMB (@lem6918023 x) (@lem6918020)). Qed.
Lemma lem6918025 (x : int) : (term340 x) = (term365 x).
Proof. exact (TRANS (@lem6917983 x) (@lem6918024 x)). Qed.
Lemma lem6918026 (x : int) : (term127 x) = (term127 x).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem6918027 (x : int) : (term434 x) = (term397 x).
Proof. exact (MK_COMB (@lem6918026 x) (@lem6918025 x)). Qed.
Lemma lem6918028 (x : int) : (term397 x) = (term398 x).
Proof. exact (@lem1982763 (real_of_int x) (term369 x) term339). Qed.
Lemma lem6918029 (x : int) : (term370 x) = (term371 x).
Proof. exact (@lem1982715 term339 (real_of_int x)). Qed.
Lemma lem6918031 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6918032 : term106 = term343.
Proof. exact (@lem6918031 term107). Qed.
Lemma lem6918034 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6918035 : term339 = term346.
Proof. exact (@lem6918034 term107). Qed.
Lemma lem6918036 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6918037 : term372 = term373.
Proof. exact (MK_COMB (@lem6918036) (@lem6918035)). Qed.
Lemma lem6918038 : term374 = term375.
Proof. exact (MK_COMB (@lem6918037) (@lem6918032)). Qed.
Lemma lem6918039 : term376.
Proof. exact (@lem1981473 term339 term106 term106 term106 term167 term106). Qed.
Lemma lem6918041 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918042 : term378 = term379.
Proof. exact (@lem6918041 (NUMERAL 0) term107). Qed.
Lemma lem6918043 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918044 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918045 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918044 h1) (fun h1 : term379 = True => @lem6918043)). Qed.
Lemma lem6918046 : term379 = True.
Proof. exact (EQ_MP (@lem6918045) (@lem6918043)). Qed.
Lemma lem6918047 : term378 = True.
Proof. exact (TRANS (@lem6918042) (@lem6918046)). Qed.
Lemma lem6918048 : True = term378.
Proof. exact (SYM (@lem6918047)). Qed.
Lemma lem6918049 : term378.
Proof. exact (EQ_MP (@lem6918048) (@lem0)). Qed.
Lemma lem6918050 : term381.
Proof. exact (@lem6918039 (@lem6918049)). Qed.
Lemma lem6918052 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918053 : term378 = term379.
Proof. exact (@lem6918052 (NUMERAL 0) term107). Qed.
Lemma lem6918054 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918055 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918056 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918055 h1) (fun h1 : term379 = True => @lem6918054)). Qed.
Lemma lem6918057 : term379 = True.
Proof. exact (EQ_MP (@lem6918056) (@lem6918054)). Qed.
Lemma lem6918058 : term378 = True.
Proof. exact (TRANS (@lem6918053) (@lem6918057)). Qed.
Lemma lem6918059 : True = term378.
Proof. exact (SYM (@lem6918058)). Qed.
Lemma lem6918060 : term378.
Proof. exact (EQ_MP (@lem6918059) (@lem0)). Qed.
Lemma lem6918061 : term382.
Proof. exact (@lem6918050 (@lem6918060)). Qed.
Lemma lem6918063 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918064 : term378 = term379.
Proof. exact (@lem6918063 (NUMERAL 0) term107). Qed.
Lemma lem6918065 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918066 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918067 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918066 h1) (fun h1 : term379 = True => @lem6918065)). Qed.
Lemma lem6918068 : term379 = True.
Proof. exact (EQ_MP (@lem6918067) (@lem6918065)). Qed.
Lemma lem6918069 : term378 = True.
Proof. exact (TRANS (@lem6918064) (@lem6918068)). Qed.
Lemma lem6918070 : True = term378.
Proof. exact (SYM (@lem6918069)). Qed.
Lemma lem6918071 : term378.
Proof. exact (EQ_MP (@lem6918070) (@lem0)). Qed.
Lemma lem6918072 : term383.
Proof. exact (@lem6918061 (@lem6918071)). Qed.
Lemma lem6918074 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6918075 : term354 = term355.
Proof. exact (@lem6918074 term107 term107). Qed.
Lemma lem6918076 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6918077 : term357 = term107.
Proof. exact (EQ_MP (@lem6918076) (@lem940073)). Qed.
Lemma lem6918078 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6918079 : term355 = term106.
Proof. exact (MK_COMB (@lem6918078) (@lem6918077)). Qed.
Lemma lem6918080 : term354 = term106.
Proof. exact (TRANS (@lem6918075) (@lem6918079)). Qed.
Lemma lem6918082 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6918083 : term349 = term360.
Proof. exact (@lem6918082 term107 term107). Qed.
Lemma lem6918084 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6918085 : term357 = term107.
Proof. exact (EQ_MP (@lem6918084) (@lem940073)). Qed.
Lemma lem6918086 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6918087 : term355 = term106.
Proof. exact (MK_COMB (@lem6918086) (@lem6918085)). Qed.
Lemma lem6918088 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6918089 : term360 = term339.
Proof. exact (MK_COMB (@lem6918088) (@lem6918087)). Qed.
Lemma lem6918090 : term349 = term339.
Proof. exact (TRANS (@lem6918083) (@lem6918089)). Qed.
Lemma lem6918091 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6918092 : term384 = term372.
Proof. exact (MK_COMB (@lem6918091) (@lem6918090)). Qed.
Lemma lem6918093 : term385 = term374.
Proof. exact (MK_COMB (@lem6918092) (@lem6918080)). Qed.
Lemma lem6918095 (m : nat) : (term386 m) = term167.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6918096 : term374 = term167.
Proof. exact (@lem6918095 term107). Qed.
Lemma lem6918097 : term385 = term167.
Proof. exact (TRANS (@lem6918093) (@lem6918096)). Qed.
Lemma lem6918098 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6918099 : term387 = term388.
Proof. exact (MK_COMB (@lem6918098) (@lem6918097)). Qed.
Lemma lem6918100 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem6918101 : term389 = term390.
Proof. exact (MK_COMB (@lem6918099) (@lem6918100)). Qed.
Lemma lem6918103 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6918104 : term390 = term167.
Proof. exact (@lem6918103 term107). Qed.
Lemma lem6918105 : term389 = term167.
Proof. exact (TRANS (@lem6918101) (@lem6918104)). Qed.
Lemma lem6918107 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6918108 : term354 = term355.
Proof. exact (@lem6918107 term107 term107). Qed.
Lemma lem6918109 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6918110 : term357 = term107.
Proof. exact (EQ_MP (@lem6918109) (@lem940073)). Qed.
Lemma lem6918111 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6918112 : term355 = term106.
Proof. exact (MK_COMB (@lem6918111) (@lem6918110)). Qed.
Lemma lem6918113 : term354 = term106.
Proof. exact (TRANS (@lem6918108) (@lem6918112)). Qed.
Lemma lem6918114 : term388 = term388.
Proof. exact (eq_refl term388). Qed.
Lemma lem6918115 : term392 = term390.
Proof. exact (MK_COMB (@lem6918114) (@lem6918113)). Qed.
Lemma lem6918117 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6918118 : term390 = term167.
Proof. exact (@lem6918117 term107). Qed.
Lemma lem6918119 : term392 = term167.
Proof. exact (TRANS (@lem6918115) (@lem6918118)). Qed.
Lemma lem6918120 : term167 = term392.
Proof. exact (SYM (@lem6918119)). Qed.
Lemma lem6918121 : term389 = term392.
Proof. exact (TRANS (@lem6918105) (@lem6918120)). Qed.
Lemma lem6918122 : term375 = term393.
Proof. exact (@lem6918072 (@lem6918121)). Qed.
Lemma lem6918123 : term374 = term393.
Proof. exact (TRANS (@lem6918038) (@lem6918122)). Qed.
Lemma lem6918125 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6918126 : term393 = term167.
Proof. exact (@lem6918125 term167). Qed.
Lemma lem6918127 : term374 = term167.
Proof. exact (TRANS (@lem6918123) (@lem6918126)). Qed.
Lemma lem6918128 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6918129 : term394 = term388.
Proof. exact (MK_COMB (@lem6918128) (@lem6918127)). Qed.
Lemma lem6918130 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem6918131 (x : int) : (term371 x) = (term395 x).
Proof. exact (MK_COMB (@lem6918129) (@lem6918130 x)). Qed.
Lemma lem6918132 (x : int) : (term370 x) = (term395 x).
Proof. exact (TRANS (@lem6918029 x) (@lem6918131 x)). Qed.
Lemma lem6918133 (x : int) : (term395 x) = term167.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem6918134 (x : int) : (term370 x) = term167.
Proof. exact (TRANS (@lem6918132 x) (@lem6918133 x)). Qed.
Lemma lem6918135 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6918136 (x : int) : (term396 x) = term169.
Proof. exact (MK_COMB (@lem6918135) (@lem6918134 x)). Qed.
Lemma lem6918137 : term339 = term339.
Proof. exact (eq_refl term339). Qed.
Lemma lem6918138 (x : int) : (term398 x) = term399.
Proof. exact (MK_COMB (@lem6918136 x) (@lem6918137)). Qed.
Lemma lem6918139 (x : int) : (term397 x) = term399.
Proof. exact (TRANS (@lem6918028 x) (@lem6918138 x)). Qed.
Lemma lem6918140 : term399 = term339.
Proof. exact (@lem1982721 term339). Qed.
Lemma lem6918141 (x : int) : (term397 x) = term339.
Proof. exact (TRANS (@lem6918139 x) (@lem6918140)). Qed.
Lemma lem6918142 (x : int) : (term434 x) = term339.
Proof. exact (TRANS (@lem6918027 x) (@lem6918141 x)). Qed.
Lemma lem6918143 (x : int) : (term433 x) = term339.
Proof. exact (TRANS (@lem6917982 x) (@lem6918142 x)). Qed.
Lemma lem6918144 (x : int) : (term432 x) = term339.
Proof. exact (TRANS (@lem6917981 x) (@lem6918143 x)). Qed.
Lemma lem6918145 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6918146 (x : int) : (term435 x) = term401.
Proof. exact (MK_COMB (@lem6918145) (@lem6918144 x)). Qed.
Lemma lem6918147 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem6918148 (x : int) : (term430 x) = term402.
Proof. exact (MK_COMB (@lem6918146 x) (@lem6918147)). Qed.
Lemma lem6918149 (x : int) : (term176 x) = term402.
Proof. exact (TRANS (@lem6917964 x) (@lem6918148 x)). Qed.
Lemma lem6918150 : term311 = term403.
Proof. exact (fun_ext (fun x : int => @lem6918149 x)). Qed.
Lemma lem6918151 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6918152 : term322 = term404.
Proof. exact (MK_COMB (@lem6918151) (@lem6918150)). Qed.
Lemma lem6918153 (x : int) : (term187 x) = (term436 x).
Proof. exact (@lem1988287 (term170 x) (term184 x)). Qed.
Lemma lem6918160 (x : int) : (term184 x) = (term184 x).
Proof. exact (eq_refl (term184 x)). Qed.
Lemma lem6918167 (x : int) : (term170 x) = (real_of_int x).
Proof. exact (@lem1982721 (real_of_int x)). Qed.
Lemma lem6918168 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem6918169 (x : int) : (term437 x) = (term431 x).
Proof. exact (MK_COMB (@lem6918168) (@lem6918167 x)). Qed.
Lemma lem6918170 (x : int) : (term438 x) = (term433 x).
Proof. exact (MK_COMB (@lem6918169 x) (@lem6918160 x)). Qed.
Lemma lem6918171 (x : int) : (term433 x) = (term434 x).
Proof. exact (@lem1982792 (real_of_int x) (term184 x)). Qed.
Lemma lem6918172 (x : int) : (term340 x) = (term341 x).
Proof. exact (@lem1982781 (real_of_int x) term339 term106). Qed.
Lemma lem6918174 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6918175 : term106 = term343.
Proof. exact (@lem6918174 term107). Qed.
Lemma lem6918177 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6918178 : term339 = term346.
Proof. exact (@lem6918177 term107). Qed.
Lemma lem6918179 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6918180 : term347 = term348.
Proof. exact (MK_COMB (@lem6918179) (@lem6918178)). Qed.
Lemma lem6918181 : term349 = term350.
Proof. exact (MK_COMB (@lem6918180) (@lem6918175)). Qed.
Lemma lem6918182 : term350 = term351.
Proof. exact (@lem1981613 term339 term106 term106 term106). Qed.
Lemma lem6918184 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6918185 : term354 = term355.
Proof. exact (@lem6918184 term107 term107). Qed.
Lemma lem6918186 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6918187 : term357 = term107.
Proof. exact (EQ_MP (@lem6918186) (@lem940073)). Qed.
Lemma lem6918188 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6918189 : term355 = term106.
Proof. exact (MK_COMB (@lem6918188) (@lem6918187)). Qed.
Lemma lem6918190 : term354 = term106.
Proof. exact (TRANS (@lem6918185) (@lem6918189)). Qed.
Lemma lem6918192 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6918193 : term349 = term360.
Proof. exact (@lem6918192 term107 term107). Qed.
Lemma lem6918194 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6918195 : term357 = term107.
Proof. exact (EQ_MP (@lem6918194) (@lem940073)). Qed.
Lemma lem6918196 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6918197 : term355 = term106.
Proof. exact (MK_COMB (@lem6918196) (@lem6918195)). Qed.
Lemma lem6918198 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6918199 : term360 = term339.
Proof. exact (MK_COMB (@lem6918198) (@lem6918197)). Qed.
Lemma lem6918200 : term349 = term339.
Proof. exact (TRANS (@lem6918193) (@lem6918199)). Qed.
Lemma lem6918201 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6918202 : term361 = term362.
Proof. exact (MK_COMB (@lem6918201) (@lem6918200)). Qed.
Lemma lem6918203 : term351 = term346.
Proof. exact (MK_COMB (@lem6918202) (@lem6918190)). Qed.
Lemma lem6918204 : term350 = term346.
Proof. exact (TRANS (@lem6918182) (@lem6918203)). Qed.
Lemma lem6918205 : term349 = term346.
Proof. exact (TRANS (@lem6918181) (@lem6918204)). Qed.
Lemma lem6918207 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6918208 : term346 = term339.
Proof. exact (@lem6918207 term339). Qed.
Lemma lem6918209 : term349 = term339.
Proof. exact (TRANS (@lem6918205) (@lem6918208)). Qed.
Lemma lem6918212 (x : int) : (term364 x) = (term364 x).
Proof. exact (eq_refl (term364 x)). Qed.
Lemma lem6918213 (x : int) : (term341 x) = (term365 x).
Proof. exact (MK_COMB (@lem6918212 x) (@lem6918209)). Qed.
Lemma lem6918214 (x : int) : (term340 x) = (term365 x).
Proof. exact (TRANS (@lem6918172 x) (@lem6918213 x)). Qed.
Lemma lem6918215 (x : int) : (term127 x) = (term127 x).
Proof. exact (eq_refl (term127 x)). Qed.
Lemma lem6918216 (x : int) : (term434 x) = (term397 x).
Proof. exact (MK_COMB (@lem6918215 x) (@lem6918214 x)). Qed.
Lemma lem6918217 (x : int) : (term397 x) = (term398 x).
Proof. exact (@lem1982763 (real_of_int x) (term369 x) term339). Qed.
Lemma lem6918218 (x : int) : (term370 x) = (term371 x).
Proof. exact (@lem1982715 term339 (real_of_int x)). Qed.
Lemma lem6918220 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6918221 : term106 = term343.
Proof. exact (@lem6918220 term107). Qed.
Lemma lem6918223 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6918224 : term339 = term346.
Proof. exact (@lem6918223 term107). Qed.
Lemma lem6918225 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6918226 : term372 = term373.
Proof. exact (MK_COMB (@lem6918225) (@lem6918224)). Qed.
Lemma lem6918227 : term374 = term375.
Proof. exact (MK_COMB (@lem6918226) (@lem6918221)). Qed.
Lemma lem6918228 : term376.
Proof. exact (@lem1981473 term339 term106 term106 term106 term167 term106). Qed.
Lemma lem6918230 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918231 : term378 = term379.
Proof. exact (@lem6918230 (NUMERAL 0) term107). Qed.
Lemma lem6918232 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918233 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918234 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918233 h1) (fun h1 : term379 = True => @lem6918232)). Qed.
Lemma lem6918235 : term379 = True.
Proof. exact (EQ_MP (@lem6918234) (@lem6918232)). Qed.
Lemma lem6918236 : term378 = True.
Proof. exact (TRANS (@lem6918231) (@lem6918235)). Qed.
Lemma lem6918237 : True = term378.
Proof. exact (SYM (@lem6918236)). Qed.
Lemma lem6918238 : term378.
Proof. exact (EQ_MP (@lem6918237) (@lem0)). Qed.
Lemma lem6918239 : term381.
Proof. exact (@lem6918228 (@lem6918238)). Qed.
Lemma lem6918241 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918242 : term378 = term379.
Proof. exact (@lem6918241 (NUMERAL 0) term107). Qed.
Lemma lem6918243 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918244 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918245 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918244 h1) (fun h1 : term379 = True => @lem6918243)). Qed.
Lemma lem6918246 : term379 = True.
Proof. exact (EQ_MP (@lem6918245) (@lem6918243)). Qed.
Lemma lem6918247 : term378 = True.
Proof. exact (TRANS (@lem6918242) (@lem6918246)). Qed.
Lemma lem6918248 : True = term378.
Proof. exact (SYM (@lem6918247)). Qed.
Lemma lem6918249 : term378.
Proof. exact (EQ_MP (@lem6918248) (@lem0)). Qed.
Lemma lem6918250 : term382.
Proof. exact (@lem6918239 (@lem6918249)). Qed.
Lemma lem6918252 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918253 : term378 = term379.
Proof. exact (@lem6918252 (NUMERAL 0) term107). Qed.
Lemma lem6918254 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918255 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918256 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918255 h1) (fun h1 : term379 = True => @lem6918254)). Qed.
Lemma lem6918257 : term379 = True.
Proof. exact (EQ_MP (@lem6918256) (@lem6918254)). Qed.
Lemma lem6918258 : term378 = True.
Proof. exact (TRANS (@lem6918253) (@lem6918257)). Qed.
Lemma lem6918259 : True = term378.
Proof. exact (SYM (@lem6918258)). Qed.
Lemma lem6918260 : term378.
Proof. exact (EQ_MP (@lem6918259) (@lem0)). Qed.
Lemma lem6918261 : term383.
Proof. exact (@lem6918250 (@lem6918260)). Qed.
Lemma lem6918263 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6918264 : term354 = term355.
Proof. exact (@lem6918263 term107 term107). Qed.
Lemma lem6918265 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6918266 : term357 = term107.
Proof. exact (EQ_MP (@lem6918265) (@lem940073)). Qed.
Lemma lem6918267 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6918268 : term355 = term106.
Proof. exact (MK_COMB (@lem6918267) (@lem6918266)). Qed.
Lemma lem6918269 : term354 = term106.
Proof. exact (TRANS (@lem6918264) (@lem6918268)). Qed.
Lemma lem6918271 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6918272 : term349 = term360.
Proof. exact (@lem6918271 term107 term107). Qed.
Lemma lem6918273 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6918274 : term357 = term107.
Proof. exact (EQ_MP (@lem6918273) (@lem940073)). Qed.
Lemma lem6918275 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6918276 : term355 = term106.
Proof. exact (MK_COMB (@lem6918275) (@lem6918274)). Qed.
Lemma lem6918277 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6918278 : term360 = term339.
Proof. exact (MK_COMB (@lem6918277) (@lem6918276)). Qed.
Lemma lem6918279 : term349 = term339.
Proof. exact (TRANS (@lem6918272) (@lem6918278)). Qed.
Lemma lem6918280 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6918281 : term384 = term372.
Proof. exact (MK_COMB (@lem6918280) (@lem6918279)). Qed.
Lemma lem6918282 : term385 = term374.
Proof. exact (MK_COMB (@lem6918281) (@lem6918269)). Qed.
Lemma lem6918284 (m : nat) : (term386 m) = term167.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6918285 : term374 = term167.
Proof. exact (@lem6918284 term107). Qed.
Lemma lem6918286 : term385 = term167.
Proof. exact (TRANS (@lem6918282) (@lem6918285)). Qed.
Lemma lem6918287 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6918288 : term387 = term388.
Proof. exact (MK_COMB (@lem6918287) (@lem6918286)). Qed.
Lemma lem6918289 : term106 = term106.
Proof. exact (eq_refl term106). Qed.
Lemma lem6918290 : term389 = term390.
Proof. exact (MK_COMB (@lem6918288) (@lem6918289)). Qed.
Lemma lem6918292 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6918293 : term390 = term167.
Proof. exact (@lem6918292 term107). Qed.
Lemma lem6918294 : term389 = term167.
Proof. exact (TRANS (@lem6918290) (@lem6918293)). Qed.
Lemma lem6918296 (m : nat) (n : nat) : (term352 m n) = (term353 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6918297 : term354 = term355.
Proof. exact (@lem6918296 term107 term107). Qed.
Lemma lem6918298 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6918299 : term357 = term107.
Proof. exact (EQ_MP (@lem6918298) (@lem940073)). Qed.
Lemma lem6918300 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6918301 : term355 = term106.
Proof. exact (MK_COMB (@lem6918300) (@lem6918299)). Qed.
Lemma lem6918302 : term354 = term106.
Proof. exact (TRANS (@lem6918297) (@lem6918301)). Qed.
Lemma lem6918303 : term388 = term388.
Proof. exact (eq_refl term388). Qed.
Lemma lem6918304 : term392 = term390.
Proof. exact (MK_COMB (@lem6918303) (@lem6918302)). Qed.
Lemma lem6918306 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6918307 : term390 = term167.
Proof. exact (@lem6918306 term107). Qed.
Lemma lem6918308 : term392 = term167.
Proof. exact (TRANS (@lem6918304) (@lem6918307)). Qed.
Lemma lem6918309 : term167 = term392.
Proof. exact (SYM (@lem6918308)). Qed.
Lemma lem6918310 : term389 = term392.
Proof. exact (TRANS (@lem6918294) (@lem6918309)). Qed.
Lemma lem6918311 : term375 = term393.
Proof. exact (@lem6918261 (@lem6918310)). Qed.
Lemma lem6918312 : term374 = term393.
Proof. exact (TRANS (@lem6918227) (@lem6918311)). Qed.
Lemma lem6918314 (x : real) : (term363 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6918315 : term393 = term167.
Proof. exact (@lem6918314 term167). Qed.
Lemma lem6918316 : term374 = term167.
Proof. exact (TRANS (@lem6918312) (@lem6918315)). Qed.
Lemma lem6918317 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6918318 : term394 = term388.
Proof. exact (MK_COMB (@lem6918317) (@lem6918316)). Qed.
Lemma lem6918319 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem6918320 (x : int) : (term371 x) = (term395 x).
Proof. exact (MK_COMB (@lem6918318) (@lem6918319 x)). Qed.
Lemma lem6918321 (x : int) : (term370 x) = (term395 x).
Proof. exact (TRANS (@lem6918218 x) (@lem6918320 x)). Qed.
Lemma lem6918322 (x : int) : (term395 x) = term167.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem6918323 (x : int) : (term370 x) = term167.
Proof. exact (TRANS (@lem6918321 x) (@lem6918322 x)). Qed.
Lemma lem6918324 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6918325 (x : int) : (term396 x) = term169.
Proof. exact (MK_COMB (@lem6918324) (@lem6918323 x)). Qed.
Lemma lem6918326 : term339 = term339.
Proof. exact (eq_refl term339). Qed.
Lemma lem6918327 (x : int) : (term398 x) = term399.
Proof. exact (MK_COMB (@lem6918325 x) (@lem6918326)). Qed.
Lemma lem6918328 (x : int) : (term397 x) = term399.
Proof. exact (TRANS (@lem6918217 x) (@lem6918327 x)). Qed.
Lemma lem6918329 : term399 = term339.
Proof. exact (@lem1982721 term339). Qed.
Lemma lem6918330 (x : int) : (term397 x) = term339.
Proof. exact (TRANS (@lem6918328 x) (@lem6918329)). Qed.
Lemma lem6918331 (x : int) : (term434 x) = term339.
Proof. exact (TRANS (@lem6918216 x) (@lem6918330 x)). Qed.
Lemma lem6918332 (x : int) : (term433 x) = term339.
Proof. exact (TRANS (@lem6918171 x) (@lem6918331 x)). Qed.
Lemma lem6918333 (x : int) : (term438 x) = term339.
Proof. exact (TRANS (@lem6918170 x) (@lem6918332 x)). Qed.
Lemma lem6918334 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6918335 (x : int) : (term439 x) = term401.
Proof. exact (MK_COMB (@lem6918334) (@lem6918333 x)). Qed.
Lemma lem6918336 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem6918337 (x : int) : (term436 x) = term402.
Proof. exact (MK_COMB (@lem6918335 x) (@lem6918336)). Qed.
Lemma lem6918338 (x : int) : (term187 x) = term402.
Proof. exact (TRANS (@lem6918153 x) (@lem6918337 x)). Qed.
Lemma lem6918339 : term312 = term403.
Proof. exact (fun_ext (fun x : int => @lem6918338 x)). Qed.
Lemma lem6918340 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem6918341 : term327 = term404.
Proof. exact (MK_COMB (@lem6918340) (@lem6918339)). Qed.
Lemma lem6918342 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6918343 : term324 = term440.
Proof. exact (MK_COMB (@lem6918342) (@lem6918152)). Qed.
Lemma lem6918344 : term328 = term441.
Proof. exact (MK_COMB (@lem6918343) (@lem6918341)). Qed.
Lemma lem6918345 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6918346 : term308 = term442.
Proof. exact (MK_COMB (@lem6918345) (@lem6917963)). Qed.
Lemma lem6918347 : term329 = term443.
Proof. exact (MK_COMB (@lem6918346) (@lem6918344)). Qed.
Lemma lem6918348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6918349 : term243 = term444.
Proof. exact (MK_COMB (@lem6918348) (@lem6917034)). Qed.
Lemma lem6918350 : term330 = term445.
Proof. exact (MK_COMB (@lem6918349) (@lem6918347)). Qed.
Lemma lem6918351 : term196 = term445.
Proof. exact (TRANS (@lem6916389) (@lem6918350)). Qed.
Lemma lem6918353 {A : Type'} (t : Prop) : (term446 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6918354 (t : Prop) : (term447 t) = t.
Proof. exact (@lem6918353 int t). Qed.
Lemma lem6918355 : term406 = term404.
Proof. exact (@lem6918354 term404). Qed.
Lemma lem6918357 {A : Type'} (t : Prop) : (term446 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6918358 (t : Prop) : (term447 t) = t.
Proof. exact (@lem6918357 int t). Qed.
Lemma lem6918359 : term404 = term402.
Proof. exact (@lem6918358 term402). Qed.
Lemma lem6918360 : term406 = term402.
Proof. exact (TRANS (@lem6918355) (@lem6918359)). Qed.
Lemma lem6918361 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6918362 : term407 = term448.
Proof. exact (MK_COMB (@lem6918361) (@lem6918360)). Qed.
Lemma lem6918364 {A : Type'} (t : Prop) : (term446 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6918365 (t : Prop) : (term447 t) = t.
Proof. exact (@lem6918364 int t). Qed.
Lemma lem6918366 : term406 = term404.
Proof. exact (@lem6918365 term404). Qed.
Lemma lem6918368 {A : Type'} (t : Prop) : (term446 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6918369 (t : Prop) : (term447 t) = t.
Proof. exact (@lem6918368 int t). Qed.
Lemma lem6918370 : term404 = term402.
Proof. exact (@lem6918369 term402). Qed.
Lemma lem6918371 : term406 = term402.
Proof. exact (TRANS (@lem6918366) (@lem6918370)). Qed.
Lemma lem6918372 : term408 = term449.
Proof. exact (MK_COMB (@lem6918362) (@lem6918371)). Qed.
Lemma lem6918373 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6918374 : term444 = term450.
Proof. exact (MK_COMB (@lem6918373) (@lem6918372)). Qed.
Lemma lem6918376 {A : Type'} (t : Prop) : (term446 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6918377 (t : Prop) : (term447 t) = t.
Proof. exact (@lem6918376 int t). Qed.
Lemma lem6918378 : term424 = term406.
Proof. exact (@lem6918377 term406). Qed.
Lemma lem6918380 {A : Type'} (t : Prop) : (term446 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6918381 (t : Prop) : (term447 t) = t.
Proof. exact (@lem6918380 int t). Qed.
Lemma lem6918382 : term406 = term404.
Proof. exact (@lem6918381 term404). Qed.
Lemma lem6918384 {A : Type'} (t : Prop) : (term446 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6918385 (t : Prop) : (term447 t) = t.
Proof. exact (@lem6918384 int t). Qed.
Lemma lem6918386 : term404 = term402.
Proof. exact (@lem6918385 term402). Qed.
Lemma lem6918387 : term406 = term402.
Proof. exact (TRANS (@lem6918382) (@lem6918386)). Qed.
Lemma lem6918388 : term424 = term402.
Proof. exact (TRANS (@lem6918378) (@lem6918387)). Qed.
Lemma lem6918389 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6918390 : term428 = term448.
Proof. exact (MK_COMB (@lem6918389) (@lem6918388)). Qed.
Lemma lem6918392 {A : Type'} (t : Prop) : (term446 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6918393 (t : Prop) : (term447 t) = t.
Proof. exact (@lem6918392 int t). Qed.
Lemma lem6918394 : term424 = term406.
Proof. exact (@lem6918393 term406). Qed.
Lemma lem6918396 {A : Type'} (t : Prop) : (term446 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6918397 (t : Prop) : (term447 t) = t.
Proof. exact (@lem6918396 int t). Qed.
Lemma lem6918398 : term406 = term404.
Proof. exact (@lem6918397 term404). Qed.
Lemma lem6918400 {A : Type'} (t : Prop) : (term446 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6918401 (t : Prop) : (term447 t) = t.
Proof. exact (@lem6918400 int t). Qed.
Lemma lem6918402 : term404 = term402.
Proof. exact (@lem6918401 term402). Qed.
Lemma lem6918403 : term406 = term402.
Proof. exact (TRANS (@lem6918398) (@lem6918402)). Qed.
Lemma lem6918404 : term424 = term402.
Proof. exact (TRANS (@lem6918394) (@lem6918403)). Qed.
Lemma lem6918405 : term429 = term449.
Proof. exact (MK_COMB (@lem6918390) (@lem6918404)). Qed.
Lemma lem6918406 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6918407 : term442 = term450.
Proof. exact (MK_COMB (@lem6918406) (@lem6918405)). Qed.
Lemma lem6918409 {A : Type'} (t : Prop) : (term446 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6918410 (t : Prop) : (term447 t) = t.
Proof. exact (@lem6918409 int t). Qed.
Lemma lem6918411 : term404 = term402.
Proof. exact (@lem6918410 term402). Qed.
Lemma lem6918412 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6918413 : term440 = term448.
Proof. exact (MK_COMB (@lem6918412) (@lem6918411)). Qed.
Lemma lem6918415 {A : Type'} (t : Prop) : (term446 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem6918416 (t : Prop) : (term447 t) = t.
Proof. exact (@lem6918415 int t). Qed.
Lemma lem6918417 : term404 = term402.
Proof. exact (@lem6918416 term402). Qed.
Lemma lem6918418 : term441 = term449.
Proof. exact (MK_COMB (@lem6918413) (@lem6918417)). Qed.
Lemma lem6918419 : term443 = term451.
Proof. exact (MK_COMB (@lem6918407) (@lem6918418)). Qed.
Lemma lem6918422 : term445 = term452.
Proof. exact (MK_COMB (@lem6918374) (@lem6918419)). Qed.
Lemma lem6918447 : term196 = term452.
Proof. exact (TRANS (@lem6918351) (@lem6918422)). Qed.
Lemma lem6918481 (h1 : term452) : term452.
Proof. exact (h1). Qed.
Lemma lem6918482 (h1 : term449) : term449.
Proof. exact (h1). Qed.
Lemma lem6918483 (h1 : term402) : term402.
Proof. exact (h1). Qed.
Lemma lem6918485 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6918486 : term402 = term453.
Proof. exact (@lem6918485 term167 term339). Qed.
Lemma lem6918488 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6918489 : term339 = term346.
Proof. exact (@lem6918488 term107). Qed.
Lemma lem6918491 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6918492 : term167 = term393.
Proof. exact (@lem6918491 (NUMERAL 0)). Qed.
Lemma lem6918493 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6918494 : term454 = term455.
Proof. exact (MK_COMB (@lem6918493) (@lem6918492)). Qed.
Lemma lem6918495 : term453 = term456.
Proof. exact (MK_COMB (@lem6918494) (@lem6918489)). Qed.
Lemma lem6918496 : term457.
Proof. exact (@lem1980026 term167 term106 term339 term106). Qed.
Lemma lem6918498 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918499 : term378 = term379.
Proof. exact (@lem6918498 (NUMERAL 0) term107). Qed.
Lemma lem6918500 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918501 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918502 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918501 h1) (fun h1 : term379 = True => @lem6918500)). Qed.
Lemma lem6918503 : term379 = True.
Proof. exact (EQ_MP (@lem6918502) (@lem6918500)). Qed.
Lemma lem6918504 : term378 = True.
Proof. exact (TRANS (@lem6918499) (@lem6918503)). Qed.
Lemma lem6918505 : True = term378.
Proof. exact (SYM (@lem6918504)). Qed.
Lemma lem6918506 : term378.
Proof. exact (EQ_MP (@lem6918505) (@lem0)). Qed.
Lemma lem6918507 : term458.
Proof. exact (@lem6918496 (@lem6918506)). Qed.
Lemma lem6918509 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918510 : term378 = term379.
Proof. exact (@lem6918509 (NUMERAL 0) term107). Qed.
Lemma lem6918511 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918512 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918513 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918512 h1) (fun h1 : term379 = True => @lem6918511)). Qed.
Lemma lem6918514 : term379 = True.
Proof. exact (EQ_MP (@lem6918513) (@lem6918511)). Qed.
Lemma lem6918515 : term378 = True.
Proof. exact (TRANS (@lem6918510) (@lem6918514)). Qed.
Lemma lem6918516 : True = term378.
Proof. exact (SYM (@lem6918515)). Qed.
Lemma lem6918517 : term378.
Proof. exact (EQ_MP (@lem6918516) (@lem0)). Qed.
Lemma lem6918518 : term456 = term459.
Proof. exact (@lem6918507 (@lem6918517)). Qed.
Lemma lem6918520 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6918521 : term349 = term360.
Proof. exact (@lem6918520 term107 term107). Qed.
Lemma lem6918522 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6918523 : term357 = term107.
Proof. exact (EQ_MP (@lem6918522) (@lem940073)). Qed.
Lemma lem6918524 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6918525 : term355 = term106.
Proof. exact (MK_COMB (@lem6918524) (@lem6918523)). Qed.
Lemma lem6918526 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6918527 : term360 = term339.
Proof. exact (MK_COMB (@lem6918526) (@lem6918525)). Qed.
Lemma lem6918528 : term349 = term339.
Proof. exact (TRANS (@lem6918521) (@lem6918527)). Qed.
Lemma lem6918530 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6918531 : term390 = term167.
Proof. exact (@lem6918530 term107). Qed.
Lemma lem6918532 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6918533 : term460 = term454.
Proof. exact (MK_COMB (@lem6918532) (@lem6918531)). Qed.
Lemma lem6918534 : term459 = term453.
Proof. exact (MK_COMB (@lem6918533) (@lem6918528)). Qed.
Lemma lem6918536 (m : nat) (n : nat) : (term461 m n) = (term462 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6918537 : term453 = term463.
Proof. exact (@lem6918536 (NUMERAL 0) term107). Qed.
Lemma lem6918538 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918539 (h1 : term380 = (BIT1 0)) : (term107 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6918540 : (term380 = (BIT1 0)) = ((term107 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918539 h1) (fun h1 : (term107 = (NUMERAL 0)) = False => @lem6918538)). Qed.
Lemma lem6918541 : (term107 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6918540) (@lem6918538)). Qed.
Lemma lem6918542 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6918543 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6918544 : term464 = (and True).
Proof. exact (MK_COMB (@lem6918543) (@lem6918542)). Qed.
Lemma lem6918545 : term463 = (True /\ False).
Proof. exact (MK_COMB (@lem6918544) (@lem6918541)). Qed.
Lemma lem6918547 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6918548 : term463 = False.
Proof. exact (TRANS (@lem6918545) (@lem6918547)). Qed.
Lemma lem6918549 : term453 = False.
Proof. exact (TRANS (@lem6918537) (@lem6918548)). Qed.
Lemma lem6918550 : term459 = False.
Proof. exact (TRANS (@lem6918534) (@lem6918549)). Qed.
Lemma lem6918551 : term456 = False.
Proof. exact (TRANS (@lem6918518) (@lem6918550)). Qed.
Lemma lem6918552 : term453 = False.
Proof. exact (TRANS (@lem6918495) (@lem6918551)). Qed.
Lemma lem6918553 : term402 = False.
Proof. exact (TRANS (@lem6918486) (@lem6918552)). Qed.
Lemma lem6918554 (h1 : term402) : False.
Proof. exact (EQ_MP (@lem6918553) (@lem6918483 h1)). Qed.
Lemma lem6918555 (h1 : term402) : term402.
Proof. exact (h1). Qed.
Lemma lem6918557 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6918558 : term402 = term453.
Proof. exact (@lem6918557 term167 term339). Qed.
Lemma lem6918560 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6918561 : term339 = term346.
Proof. exact (@lem6918560 term107). Qed.
Lemma lem6918563 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6918564 : term167 = term393.
Proof. exact (@lem6918563 (NUMERAL 0)). Qed.
Lemma lem6918565 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6918566 : term454 = term455.
Proof. exact (MK_COMB (@lem6918565) (@lem6918564)). Qed.
Lemma lem6918567 : term453 = term456.
Proof. exact (MK_COMB (@lem6918566) (@lem6918561)). Qed.
Lemma lem6918568 : term457.
Proof. exact (@lem1980026 term167 term106 term339 term106). Qed.
Lemma lem6918570 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918571 : term378 = term379.
Proof. exact (@lem6918570 (NUMERAL 0) term107). Qed.
Lemma lem6918572 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918573 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918574 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918573 h1) (fun h1 : term379 = True => @lem6918572)). Qed.
Lemma lem6918575 : term379 = True.
Proof. exact (EQ_MP (@lem6918574) (@lem6918572)). Qed.
Lemma lem6918576 : term378 = True.
Proof. exact (TRANS (@lem6918571) (@lem6918575)). Qed.
Lemma lem6918577 : True = term378.
Proof. exact (SYM (@lem6918576)). Qed.
Lemma lem6918578 : term378.
Proof. exact (EQ_MP (@lem6918577) (@lem0)). Qed.
Lemma lem6918579 : term458.
Proof. exact (@lem6918568 (@lem6918578)). Qed.
Lemma lem6918581 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918582 : term378 = term379.
Proof. exact (@lem6918581 (NUMERAL 0) term107). Qed.
Lemma lem6918583 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918584 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918585 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918584 h1) (fun h1 : term379 = True => @lem6918583)). Qed.
Lemma lem6918586 : term379 = True.
Proof. exact (EQ_MP (@lem6918585) (@lem6918583)). Qed.
Lemma lem6918587 : term378 = True.
Proof. exact (TRANS (@lem6918582) (@lem6918586)). Qed.
Lemma lem6918588 : True = term378.
Proof. exact (SYM (@lem6918587)). Qed.
Lemma lem6918589 : term378.
Proof. exact (EQ_MP (@lem6918588) (@lem0)). Qed.
Lemma lem6918590 : term456 = term459.
Proof. exact (@lem6918579 (@lem6918589)). Qed.
Lemma lem6918592 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6918593 : term349 = term360.
Proof. exact (@lem6918592 term107 term107). Qed.
Lemma lem6918594 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6918595 : term357 = term107.
Proof. exact (EQ_MP (@lem6918594) (@lem940073)). Qed.
Lemma lem6918596 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6918597 : term355 = term106.
Proof. exact (MK_COMB (@lem6918596) (@lem6918595)). Qed.
Lemma lem6918598 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6918599 : term360 = term339.
Proof. exact (MK_COMB (@lem6918598) (@lem6918597)). Qed.
Lemma lem6918600 : term349 = term339.
Proof. exact (TRANS (@lem6918593) (@lem6918599)). Qed.
Lemma lem6918602 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6918603 : term390 = term167.
Proof. exact (@lem6918602 term107). Qed.
Lemma lem6918604 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6918605 : term460 = term454.
Proof. exact (MK_COMB (@lem6918604) (@lem6918603)). Qed.
Lemma lem6918606 : term459 = term453.
Proof. exact (MK_COMB (@lem6918605) (@lem6918600)). Qed.
Lemma lem6918608 (m : nat) (n : nat) : (term461 m n) = (term462 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6918609 : term453 = term463.
Proof. exact (@lem6918608 (NUMERAL 0) term107). Qed.
Lemma lem6918610 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918611 (h1 : term380 = (BIT1 0)) : (term107 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6918612 : (term380 = (BIT1 0)) = ((term107 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918611 h1) (fun h1 : (term107 = (NUMERAL 0)) = False => @lem6918610)). Qed.
Lemma lem6918613 : (term107 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6918612) (@lem6918610)). Qed.
Lemma lem6918614 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6918615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6918616 : term464 = (and True).
Proof. exact (MK_COMB (@lem6918615) (@lem6918614)). Qed.
Lemma lem6918617 : term463 = (True /\ False).
Proof. exact (MK_COMB (@lem6918616) (@lem6918613)). Qed.
Lemma lem6918619 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6918620 : term463 = False.
Proof. exact (TRANS (@lem6918617) (@lem6918619)). Qed.
Lemma lem6918621 : term453 = False.
Proof. exact (TRANS (@lem6918609) (@lem6918620)). Qed.
Lemma lem6918622 : term459 = False.
Proof. exact (TRANS (@lem6918606) (@lem6918621)). Qed.
Lemma lem6918623 : term456 = False.
Proof. exact (TRANS (@lem6918590) (@lem6918622)). Qed.
Lemma lem6918624 : term453 = False.
Proof. exact (TRANS (@lem6918567) (@lem6918623)). Qed.
Lemma lem6918625 : term402 = False.
Proof. exact (TRANS (@lem6918558) (@lem6918624)). Qed.
Lemma lem6918626 (h1 : term402) : False.
Proof. exact (EQ_MP (@lem6918625) (@lem6918555 h1)). Qed.
Lemma lem6918627 (h1 : term449) : False.
Proof. exact (or_elim (@lem6918482 h1) (fun h0 : term402 => @lem6918554 h0) (fun h0 : term402 => @lem6918626 h0)). Qed.
Lemma lem6918628 (h1 : term451) : term451.
Proof. exact (h1). Qed.
Lemma lem6918629 (h1 : term449) : term449.
Proof. exact (h1). Qed.
Lemma lem6918630 (h1 : term402) : term402.
Proof. exact (h1). Qed.
Lemma lem6918632 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6918633 : term402 = term453.
Proof. exact (@lem6918632 term167 term339). Qed.
Lemma lem6918635 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6918636 : term339 = term346.
Proof. exact (@lem6918635 term107). Qed.
Lemma lem6918638 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6918639 : term167 = term393.
Proof. exact (@lem6918638 (NUMERAL 0)). Qed.
Lemma lem6918640 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6918641 : term454 = term455.
Proof. exact (MK_COMB (@lem6918640) (@lem6918639)). Qed.
Lemma lem6918642 : term453 = term456.
Proof. exact (MK_COMB (@lem6918641) (@lem6918636)). Qed.
Lemma lem6918643 : term457.
Proof. exact (@lem1980026 term167 term106 term339 term106). Qed.
Lemma lem6918645 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918646 : term378 = term379.
Proof. exact (@lem6918645 (NUMERAL 0) term107). Qed.
Lemma lem6918647 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918648 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918649 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918648 h1) (fun h1 : term379 = True => @lem6918647)). Qed.
Lemma lem6918650 : term379 = True.
Proof. exact (EQ_MP (@lem6918649) (@lem6918647)). Qed.
Lemma lem6918651 : term378 = True.
Proof. exact (TRANS (@lem6918646) (@lem6918650)). Qed.
Lemma lem6918652 : True = term378.
Proof. exact (SYM (@lem6918651)). Qed.
Lemma lem6918653 : term378.
Proof. exact (EQ_MP (@lem6918652) (@lem0)). Qed.
Lemma lem6918654 : term458.
Proof. exact (@lem6918643 (@lem6918653)). Qed.
Lemma lem6918656 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918657 : term378 = term379.
Proof. exact (@lem6918656 (NUMERAL 0) term107). Qed.
Lemma lem6918658 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918659 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918660 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918659 h1) (fun h1 : term379 = True => @lem6918658)). Qed.
Lemma lem6918661 : term379 = True.
Proof. exact (EQ_MP (@lem6918660) (@lem6918658)). Qed.
Lemma lem6918662 : term378 = True.
Proof. exact (TRANS (@lem6918657) (@lem6918661)). Qed.
Lemma lem6918663 : True = term378.
Proof. exact (SYM (@lem6918662)). Qed.
Lemma lem6918664 : term378.
Proof. exact (EQ_MP (@lem6918663) (@lem0)). Qed.
Lemma lem6918665 : term456 = term459.
Proof. exact (@lem6918654 (@lem6918664)). Qed.
Lemma lem6918667 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6918668 : term349 = term360.
Proof. exact (@lem6918667 term107 term107). Qed.
Lemma lem6918669 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6918670 : term357 = term107.
Proof. exact (EQ_MP (@lem6918669) (@lem940073)). Qed.
Lemma lem6918671 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6918672 : term355 = term106.
Proof. exact (MK_COMB (@lem6918671) (@lem6918670)). Qed.
Lemma lem6918673 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6918674 : term360 = term339.
Proof. exact (MK_COMB (@lem6918673) (@lem6918672)). Qed.
Lemma lem6918675 : term349 = term339.
Proof. exact (TRANS (@lem6918668) (@lem6918674)). Qed.
Lemma lem6918677 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6918678 : term390 = term167.
Proof. exact (@lem6918677 term107). Qed.
Lemma lem6918679 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6918680 : term460 = term454.
Proof. exact (MK_COMB (@lem6918679) (@lem6918678)). Qed.
Lemma lem6918681 : term459 = term453.
Proof. exact (MK_COMB (@lem6918680) (@lem6918675)). Qed.
Lemma lem6918683 (m : nat) (n : nat) : (term461 m n) = (term462 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6918684 : term453 = term463.
Proof. exact (@lem6918683 (NUMERAL 0) term107). Qed.
Lemma lem6918685 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918686 (h1 : term380 = (BIT1 0)) : (term107 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6918687 : (term380 = (BIT1 0)) = ((term107 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918686 h1) (fun h1 : (term107 = (NUMERAL 0)) = False => @lem6918685)). Qed.
Lemma lem6918688 : (term107 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6918687) (@lem6918685)). Qed.
Lemma lem6918689 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6918690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6918691 : term464 = (and True).
Proof. exact (MK_COMB (@lem6918690) (@lem6918689)). Qed.
Lemma lem6918692 : term463 = (True /\ False).
Proof. exact (MK_COMB (@lem6918691) (@lem6918688)). Qed.
Lemma lem6918694 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6918695 : term463 = False.
Proof. exact (TRANS (@lem6918692) (@lem6918694)). Qed.
Lemma lem6918696 : term453 = False.
Proof. exact (TRANS (@lem6918684) (@lem6918695)). Qed.
Lemma lem6918697 : term459 = False.
Proof. exact (TRANS (@lem6918681) (@lem6918696)). Qed.
Lemma lem6918698 : term456 = False.
Proof. exact (TRANS (@lem6918665) (@lem6918697)). Qed.
Lemma lem6918699 : term453 = False.
Proof. exact (TRANS (@lem6918642) (@lem6918698)). Qed.
Lemma lem6918700 : term402 = False.
Proof. exact (TRANS (@lem6918633) (@lem6918699)). Qed.
Lemma lem6918701 (h1 : term402) : False.
Proof. exact (EQ_MP (@lem6918700) (@lem6918630 h1)). Qed.
Lemma lem6918702 (h1 : term402) : term402.
Proof. exact (h1). Qed.
Lemma lem6918704 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6918705 : term402 = term453.
Proof. exact (@lem6918704 term167 term339). Qed.
Lemma lem6918707 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6918708 : term339 = term346.
Proof. exact (@lem6918707 term107). Qed.
Lemma lem6918710 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6918711 : term167 = term393.
Proof. exact (@lem6918710 (NUMERAL 0)). Qed.
Lemma lem6918712 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6918713 : term454 = term455.
Proof. exact (MK_COMB (@lem6918712) (@lem6918711)). Qed.
Lemma lem6918714 : term453 = term456.
Proof. exact (MK_COMB (@lem6918713) (@lem6918708)). Qed.
Lemma lem6918715 : term457.
Proof. exact (@lem1980026 term167 term106 term339 term106). Qed.
Lemma lem6918717 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918718 : term378 = term379.
Proof. exact (@lem6918717 (NUMERAL 0) term107). Qed.
Lemma lem6918719 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918720 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918721 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918720 h1) (fun h1 : term379 = True => @lem6918719)). Qed.
Lemma lem6918722 : term379 = True.
Proof. exact (EQ_MP (@lem6918721) (@lem6918719)). Qed.
Lemma lem6918723 : term378 = True.
Proof. exact (TRANS (@lem6918718) (@lem6918722)). Qed.
Lemma lem6918724 : True = term378.
Proof. exact (SYM (@lem6918723)). Qed.
Lemma lem6918725 : term378.
Proof. exact (EQ_MP (@lem6918724) (@lem0)). Qed.
Lemma lem6918726 : term458.
Proof. exact (@lem6918715 (@lem6918725)). Qed.
Lemma lem6918728 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918729 : term378 = term379.
Proof. exact (@lem6918728 (NUMERAL 0) term107). Qed.
Lemma lem6918730 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918731 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918732 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918731 h1) (fun h1 : term379 = True => @lem6918730)). Qed.
Lemma lem6918733 : term379 = True.
Proof. exact (EQ_MP (@lem6918732) (@lem6918730)). Qed.
Lemma lem6918734 : term378 = True.
Proof. exact (TRANS (@lem6918729) (@lem6918733)). Qed.
Lemma lem6918735 : True = term378.
Proof. exact (SYM (@lem6918734)). Qed.
Lemma lem6918736 : term378.
Proof. exact (EQ_MP (@lem6918735) (@lem0)). Qed.
Lemma lem6918737 : term456 = term459.
Proof. exact (@lem6918726 (@lem6918736)). Qed.
Lemma lem6918739 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6918740 : term349 = term360.
Proof. exact (@lem6918739 term107 term107). Qed.
Lemma lem6918741 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6918742 : term357 = term107.
Proof. exact (EQ_MP (@lem6918741) (@lem940073)). Qed.
Lemma lem6918743 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6918744 : term355 = term106.
Proof. exact (MK_COMB (@lem6918743) (@lem6918742)). Qed.
Lemma lem6918745 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6918746 : term360 = term339.
Proof. exact (MK_COMB (@lem6918745) (@lem6918744)). Qed.
Lemma lem6918747 : term349 = term339.
Proof. exact (TRANS (@lem6918740) (@lem6918746)). Qed.
Lemma lem6918749 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6918750 : term390 = term167.
Proof. exact (@lem6918749 term107). Qed.
Lemma lem6918751 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6918752 : term460 = term454.
Proof. exact (MK_COMB (@lem6918751) (@lem6918750)). Qed.
Lemma lem6918753 : term459 = term453.
Proof. exact (MK_COMB (@lem6918752) (@lem6918747)). Qed.
Lemma lem6918755 (m : nat) (n : nat) : (term461 m n) = (term462 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6918756 : term453 = term463.
Proof. exact (@lem6918755 (NUMERAL 0) term107). Qed.
Lemma lem6918757 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918758 (h1 : term380 = (BIT1 0)) : (term107 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6918759 : (term380 = (BIT1 0)) = ((term107 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918758 h1) (fun h1 : (term107 = (NUMERAL 0)) = False => @lem6918757)). Qed.
Lemma lem6918760 : (term107 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6918759) (@lem6918757)). Qed.
Lemma lem6918761 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6918762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6918763 : term464 = (and True).
Proof. exact (MK_COMB (@lem6918762) (@lem6918761)). Qed.
Lemma lem6918764 : term463 = (True /\ False).
Proof. exact (MK_COMB (@lem6918763) (@lem6918760)). Qed.
Lemma lem6918766 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6918767 : term463 = False.
Proof. exact (TRANS (@lem6918764) (@lem6918766)). Qed.
Lemma lem6918768 : term453 = False.
Proof. exact (TRANS (@lem6918756) (@lem6918767)). Qed.
Lemma lem6918769 : term459 = False.
Proof. exact (TRANS (@lem6918753) (@lem6918768)). Qed.
Lemma lem6918770 : term456 = False.
Proof. exact (TRANS (@lem6918737) (@lem6918769)). Qed.
Lemma lem6918771 : term453 = False.
Proof. exact (TRANS (@lem6918714) (@lem6918770)). Qed.
Lemma lem6918772 : term402 = False.
Proof. exact (TRANS (@lem6918705) (@lem6918771)). Qed.
Lemma lem6918773 (h1 : term402) : False.
Proof. exact (EQ_MP (@lem6918772) (@lem6918702 h1)). Qed.
Lemma lem6918774 (h1 : term449) : False.
Proof. exact (or_elim (@lem6918629 h1) (fun h0 : term402 => @lem6918701 h0) (fun h0 : term402 => @lem6918773 h0)). Qed.
Lemma lem6918775 (h1 : term449) : term449.
Proof. exact (h1). Qed.
Lemma lem6918776 (h1 : term402) : term402.
Proof. exact (h1). Qed.
Lemma lem6918778 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6918779 : term402 = term453.
Proof. exact (@lem6918778 term167 term339). Qed.
Lemma lem6918781 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6918782 : term339 = term346.
Proof. exact (@lem6918781 term107). Qed.
Lemma lem6918784 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6918785 : term167 = term393.
Proof. exact (@lem6918784 (NUMERAL 0)). Qed.
Lemma lem6918786 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6918787 : term454 = term455.
Proof. exact (MK_COMB (@lem6918786) (@lem6918785)). Qed.
Lemma lem6918788 : term453 = term456.
Proof. exact (MK_COMB (@lem6918787) (@lem6918782)). Qed.
Lemma lem6918789 : term457.
Proof. exact (@lem1980026 term167 term106 term339 term106). Qed.
Lemma lem6918791 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918792 : term378 = term379.
Proof. exact (@lem6918791 (NUMERAL 0) term107). Qed.
Lemma lem6918793 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918794 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918795 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918794 h1) (fun h1 : term379 = True => @lem6918793)). Qed.
Lemma lem6918796 : term379 = True.
Proof. exact (EQ_MP (@lem6918795) (@lem6918793)). Qed.
Lemma lem6918797 : term378 = True.
Proof. exact (TRANS (@lem6918792) (@lem6918796)). Qed.
Lemma lem6918798 : True = term378.
Proof. exact (SYM (@lem6918797)). Qed.
Lemma lem6918799 : term378.
Proof. exact (EQ_MP (@lem6918798) (@lem0)). Qed.
Lemma lem6918800 : term458.
Proof. exact (@lem6918789 (@lem6918799)). Qed.
Lemma lem6918802 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918803 : term378 = term379.
Proof. exact (@lem6918802 (NUMERAL 0) term107). Qed.
Lemma lem6918804 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918805 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918806 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918805 h1) (fun h1 : term379 = True => @lem6918804)). Qed.
Lemma lem6918807 : term379 = True.
Proof. exact (EQ_MP (@lem6918806) (@lem6918804)). Qed.
Lemma lem6918808 : term378 = True.
Proof. exact (TRANS (@lem6918803) (@lem6918807)). Qed.
Lemma lem6918809 : True = term378.
Proof. exact (SYM (@lem6918808)). Qed.
Lemma lem6918810 : term378.
Proof. exact (EQ_MP (@lem6918809) (@lem0)). Qed.
Lemma lem6918811 : term456 = term459.
Proof. exact (@lem6918800 (@lem6918810)). Qed.
Lemma lem6918813 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6918814 : term349 = term360.
Proof. exact (@lem6918813 term107 term107). Qed.
Lemma lem6918815 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6918816 : term357 = term107.
Proof. exact (EQ_MP (@lem6918815) (@lem940073)). Qed.
Lemma lem6918817 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6918818 : term355 = term106.
Proof. exact (MK_COMB (@lem6918817) (@lem6918816)). Qed.
Lemma lem6918819 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6918820 : term360 = term339.
Proof. exact (MK_COMB (@lem6918819) (@lem6918818)). Qed.
Lemma lem6918821 : term349 = term339.
Proof. exact (TRANS (@lem6918814) (@lem6918820)). Qed.
Lemma lem6918823 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6918824 : term390 = term167.
Proof. exact (@lem6918823 term107). Qed.
Lemma lem6918825 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6918826 : term460 = term454.
Proof. exact (MK_COMB (@lem6918825) (@lem6918824)). Qed.
Lemma lem6918827 : term459 = term453.
Proof. exact (MK_COMB (@lem6918826) (@lem6918821)). Qed.
Lemma lem6918829 (m : nat) (n : nat) : (term461 m n) = (term462 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6918830 : term453 = term463.
Proof. exact (@lem6918829 (NUMERAL 0) term107). Qed.
Lemma lem6918831 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918832 (h1 : term380 = (BIT1 0)) : (term107 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6918833 : (term380 = (BIT1 0)) = ((term107 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918832 h1) (fun h1 : (term107 = (NUMERAL 0)) = False => @lem6918831)). Qed.
Lemma lem6918834 : (term107 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6918833) (@lem6918831)). Qed.
Lemma lem6918835 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6918836 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6918837 : term464 = (and True).
Proof. exact (MK_COMB (@lem6918836) (@lem6918835)). Qed.
Lemma lem6918838 : term463 = (True /\ False).
Proof. exact (MK_COMB (@lem6918837) (@lem6918834)). Qed.
Lemma lem6918840 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6918841 : term463 = False.
Proof. exact (TRANS (@lem6918838) (@lem6918840)). Qed.
Lemma lem6918842 : term453 = False.
Proof. exact (TRANS (@lem6918830) (@lem6918841)). Qed.
Lemma lem6918843 : term459 = False.
Proof. exact (TRANS (@lem6918827) (@lem6918842)). Qed.
Lemma lem6918844 : term456 = False.
Proof. exact (TRANS (@lem6918811) (@lem6918843)). Qed.
Lemma lem6918845 : term453 = False.
Proof. exact (TRANS (@lem6918788) (@lem6918844)). Qed.
Lemma lem6918846 : term402 = False.
Proof. exact (TRANS (@lem6918779) (@lem6918845)). Qed.
Lemma lem6918847 (h1 : term402) : False.
Proof. exact (EQ_MP (@lem6918846) (@lem6918776 h1)). Qed.
Lemma lem6918848 (h1 : term402) : term402.
Proof. exact (h1). Qed.
Lemma lem6918850 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6918851 : term402 = term453.
Proof. exact (@lem6918850 term167 term339). Qed.
Lemma lem6918853 (x : nat) : (term344 x) = (term345 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6918854 : term339 = term346.
Proof. exact (@lem6918853 term107). Qed.
Lemma lem6918856 (x : nat) : (real_of_num x) = (term342 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6918857 : term167 = term393.
Proof. exact (@lem6918856 (NUMERAL 0)). Qed.
Lemma lem6918858 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6918859 : term454 = term455.
Proof. exact (MK_COMB (@lem6918858) (@lem6918857)). Qed.
Lemma lem6918860 : term453 = term456.
Proof. exact (MK_COMB (@lem6918859) (@lem6918854)). Qed.
Lemma lem6918861 : term457.
Proof. exact (@lem1980026 term167 term106 term339 term106). Qed.
Lemma lem6918863 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918864 : term378 = term379.
Proof. exact (@lem6918863 (NUMERAL 0) term107). Qed.
Lemma lem6918865 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918866 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918867 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918866 h1) (fun h1 : term379 = True => @lem6918865)). Qed.
Lemma lem6918868 : term379 = True.
Proof. exact (EQ_MP (@lem6918867) (@lem6918865)). Qed.
Lemma lem6918869 : term378 = True.
Proof. exact (TRANS (@lem6918864) (@lem6918868)). Qed.
Lemma lem6918870 : True = term378.
Proof. exact (SYM (@lem6918869)). Qed.
Lemma lem6918871 : term378.
Proof. exact (EQ_MP (@lem6918870) (@lem0)). Qed.
Lemma lem6918872 : term458.
Proof. exact (@lem6918861 (@lem6918871)). Qed.
Lemma lem6918874 (m : nat) (n : nat) : (term377 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6918875 : term378 = term379.
Proof. exact (@lem6918874 (NUMERAL 0) term107). Qed.
Lemma lem6918876 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918877 (h1 : term380 = (BIT1 0)) : term379 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6918878 : (term380 = (BIT1 0)) = (term379 = True).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918877 h1) (fun h1 : term379 = True => @lem6918876)). Qed.
Lemma lem6918879 : term379 = True.
Proof. exact (EQ_MP (@lem6918878) (@lem6918876)). Qed.
Lemma lem6918880 : term378 = True.
Proof. exact (TRANS (@lem6918875) (@lem6918879)). Qed.
Lemma lem6918881 : True = term378.
Proof. exact (SYM (@lem6918880)). Qed.
Lemma lem6918882 : term378.
Proof. exact (EQ_MP (@lem6918881) (@lem0)). Qed.
Lemma lem6918883 : term456 = term459.
Proof. exact (@lem6918872 (@lem6918882)). Qed.
Lemma lem6918885 (m : nat) (n : nat) : (term358 m n) = (term359 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6918886 : term349 = term360.
Proof. exact (@lem6918885 term107 term107). Qed.
Lemma lem6918887 : (term356 = (BIT1 0)) = (term357 = term107).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6918888 : term357 = term107.
Proof. exact (EQ_MP (@lem6918887) (@lem940073)). Qed.
Lemma lem6918889 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6918890 : term355 = term106.
Proof. exact (MK_COMB (@lem6918889) (@lem6918888)). Qed.
Lemma lem6918891 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6918892 : term360 = term339.
Proof. exact (MK_COMB (@lem6918891) (@lem6918890)). Qed.
Lemma lem6918893 : term349 = term339.
Proof. exact (TRANS (@lem6918886) (@lem6918892)). Qed.
Lemma lem6918895 (x : nat) : (term391 x) = term167.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6918896 : term390 = term167.
Proof. exact (@lem6918895 term107). Qed.
Lemma lem6918897 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6918898 : term460 = term454.
Proof. exact (MK_COMB (@lem6918897) (@lem6918896)). Qed.
Lemma lem6918899 : term459 = term453.
Proof. exact (MK_COMB (@lem6918898) (@lem6918893)). Qed.
Lemma lem6918901 (m : nat) (n : nat) : (term461 m n) = (term462 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6918902 : term453 = term463.
Proof. exact (@lem6918901 (NUMERAL 0) term107). Qed.
Lemma lem6918903 : term380 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6918904 (h1 : term380 = (BIT1 0)) : (term107 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6918905 : (term380 = (BIT1 0)) = ((term107 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term380 = (BIT1 0) => @lem6918904 h1) (fun h1 : (term107 = (NUMERAL 0)) = False => @lem6918903)). Qed.
Lemma lem6918906 : (term107 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6918905) (@lem6918903)). Qed.
Lemma lem6918907 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6918908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6918909 : term464 = (and True).
Proof. exact (MK_COMB (@lem6918908) (@lem6918907)). Qed.
Lemma lem6918910 : term463 = (True /\ False).
Proof. exact (MK_COMB (@lem6918909) (@lem6918906)). Qed.
Lemma lem6918912 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6918913 : term463 = False.
Proof. exact (TRANS (@lem6918910) (@lem6918912)). Qed.
Lemma lem6918914 : term453 = False.
Proof. exact (TRANS (@lem6918902) (@lem6918913)). Qed.
Lemma lem6918915 : term459 = False.
Proof. exact (TRANS (@lem6918899) (@lem6918914)). Qed.
Lemma lem6918916 : term456 = False.
Proof. exact (TRANS (@lem6918883) (@lem6918915)). Qed.
Lemma lem6918917 : term453 = False.
Proof. exact (TRANS (@lem6918860) (@lem6918916)). Qed.
Lemma lem6918918 : term402 = False.
Proof. exact (TRANS (@lem6918851) (@lem6918917)). Qed.
Lemma lem6918919 (h1 : term402) : False.
Proof. exact (EQ_MP (@lem6918918) (@lem6918848 h1)). Qed.
Lemma lem6918920 (h1 : term449) : False.
Proof. exact (or_elim (@lem6918775 h1) (fun h0 : term402 => @lem6918847 h0) (fun h0 : term402 => @lem6918919 h0)). Qed.
Lemma lem6918921 (h1 : term451) : False.
Proof. exact (or_elim (@lem6918628 h1) (fun h0 : term449 => @lem6918774 h0) (fun h0 : term449 => @lem6918920 h0)). Qed.
Lemma lem6918922 (h1 : term452) : False.
Proof. exact (or_elim (@lem6918481 h1) (fun h0 : term449 => @lem6918627 h0) (fun h0 : term451 => @lem6918921 h0)). Qed.
Lemma lem6918924 (h1 : term452) : term452.
Proof. exact (h1). Qed.
Lemma lem6918925 (h1 : term452) : term452 = False.
Proof. exact (prop_ext (fun h2 : term452 => @lem6918922 h1) (fun h2 : False => @lem6918924 h1)). Qed.
Lemma lem6918926 (h1 : term452) : False.
Proof. exact (EQ_MP (@lem6918925 h1) (@lem6918924 h1)). Qed.
Lemma lem6918927 (h1 : term196) : term196.
Proof. exact (h1). Qed.
Lemma lem6918928 (h1 : term196) : term452.
Proof. exact (EQ_MP (@lem6918447) (@lem6918927 h1)). Qed.
Lemma lem6918929 (h1 : term196) : term452 = False.
Proof. exact (prop_ext (fun h2 : term452 => @lem6918926 h2) (fun h2 : False => @lem6918928 h1)). Qed.
Lemma lem6918930 (h1 : term196) : False.
Proof. exact (EQ_MP (@lem6918929 h1) (@lem6918928 h1)). Qed.
Lemma lem6918931 : term465.
Proof. exact (fun h0 : term196 => @lem6918930 h0). Qed.
Lemma lem6918932 : term466.
Proof. exact (@lem1386578 term467). Qed.
Lemma lem6918935 : term467.
Proof. exact (@lem6918932 (@lem6918931)). Qed.
Lemma lem6918936 : term194 = term88.
Proof. exact (SYM (@lem6915974)). Qed.
Lemma lem6918937 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6918938 : term467 = term20.
Proof. exact (MK_COMB (@lem6918937) (@lem6918936)). Qed.
Lemma lem6918939 : term20.
Proof. exact (EQ_MP (@lem6918938) (@lem6918935)). Qed.
Lemma lem6918940 : term19.
Proof. exact (EQ_MP (@lem6915577) (@lem6918939)). Qed.
Lemma lem6918941 : term19 = (term19 = True).
Proof. exact (@lem7 term19). Qed.
Lemma lem6918942 : term19 = True.
Proof. exact (EQ_MP (@lem6918941) (@lem6918940)). Qed.
Lemma lem6918943 : True = term19.
Proof. exact (SYM (@lem6918942)). Qed.
Lemma lem6918944 : term19.
Proof. exact (EQ_MP (@lem6918943) (@lem0)). Qed.
Lemma lem6918945 : @monoidal int int_add.
Proof. exact (EQ_MP (@lem6915576) (@lem6918944)). Qed.
