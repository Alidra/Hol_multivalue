Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MONOIDAL_REAL_ADD_term_abbrevs.
Require Import monoidal_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm17045_spec.
Require Import thm18392_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980255_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
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
Require Import thm1982781_spec.
Require Import thm1982785_spec.
Require Import thm1982792_spec.
Require Import thm1988318_spec.
Require Import thm7064171_spec.
Require Import thm7065437_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7065439 {A : Type'} (op : type1400 A) : term0 A op.
Proof. exact (@lem5712802 A op). Qed.
Lemma lem7065440 {A : Type'} (op : type1400 A) : (term0 A op) = ((@monoidal A op) = (term1 A op)).
Proof. exact (eq_refl (term0 A op)). Qed.
Lemma lem7065443 {A : Type'} (op : type1400 A) : (@monoidal A op) = (term1 A op).
Proof. exact (EQ_MP (@lem7065440 A op) (@lem7065439 A op)). Qed.
Lemma lem7065444 (op : type1627) : (@monoidal real op) = (term2 op).
Proof. exact (@lem7065443 real op). Qed.
Lemma lem7065445 : (@monoidal real real_add) = term3.
Proof. exact (@lem7065444 real_add). Qed.
Lemma lem7065481 : (@neutral real real_add) = term4.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7065482 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7065483 : term5 = term6.
Proof. exact (MK_COMB (@lem7065482) (@lem7065481)). Qed.
Lemma lem7065484 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7065485 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem7065483) (@lem7065484 x)). Qed.
Lemma lem7065486 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7065487 (x : real) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem7065486) (@lem7065485 x)). Qed.
Lemma lem7065488 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7065489 (x : real) : ((term7 x) = x) = ((term8 x) = x).
Proof. exact (MK_COMB (@lem7065487 x) (@lem7065488 x)). Qed.
Lemma lem7065492 : term11 = term12.
Proof. exact (fun_ext (fun x : real => @lem7065489 x)). Qed.
Lemma lem7065493 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7065494 : term13 = term14.
Proof. exact (MK_COMB (@lem7065493) (@lem7065492)). Qed.
Lemma lem7065499 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem7065500 : term16 = term17.
Proof. exact (MK_COMB (@lem7065499) (@lem7065494)). Qed.
Lemma lem7065503 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem7065504 : term3 = term19.
Proof. exact (MK_COMB (@lem7065503) (@lem7065500)). Qed.
Lemma lem7065507 : (@monoidal real real_add) = term19.
Proof. exact (TRANS (@lem7065445) (@lem7065504)). Qed.
Lemma lem7065508 : term19 = (@monoidal real real_add).
Proof. exact (SYM (@lem7065507)). Qed.
Lemma lem7065542 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7065543 (x : real) : (term22 x) = (term23 x).
Proof. exact (@lem7065542 (term24 x)). Qed.
Lemma lem7065544 (y : real) (x : real) : (term25 x y) = ((real_add x y) = (real_add y x)).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem7065545 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7065547 (y : real) (x : real) : (term26 x y) = (term27 y x).
Proof. exact (MK_COMB (@lem7065545) (@lem7065544 y x)). Qed.
Lemma lem7065548 (x : real) : (term28 x) = (term29 x).
Proof. exact (fun_ext (fun y : real => @lem7065547 y x)). Qed.
Lemma lem7065549 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7065550 (x : real) : (term23 x) = (term30 x).
Proof. exact (MK_COMB (@lem7065549) (@lem7065548 x)). Qed.
Lemma lem7065551 (x : real) : (term22 x) = (term30 x).
Proof. exact (TRANS (@lem7065543 x) (@lem7065550 x)). Qed.
Lemma lem7065552 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7065553 : term31 = term32.
Proof. exact (@lem7065552 term33). Qed.
Lemma lem7065554 (x : real) : (term34 x) = (term35 x).
Proof. exact (eq_refl (term34 x)). Qed.
Lemma lem7065555 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7065556 (x : real) : (term36 x) = (term22 x).
Proof. exact (MK_COMB (@lem7065555) (@lem7065554 x)). Qed.
Lemma lem7065557 (x : real) : (term36 x) = (term30 x).
Proof. exact (TRANS (@lem7065556 x) (@lem7065551 x)). Qed.
Lemma lem7065558 : term37 = term38.
Proof. exact (fun_ext (fun x : real => @lem7065557 x)). Qed.
Lemma lem7065559 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7065560 : term32 = term39.
Proof. exact (MK_COMB (@lem7065559) (@lem7065558)). Qed.
Lemma lem7065561 : term31 = term39.
Proof. exact (TRANS (@lem7065553) (@lem7065560)). Qed.
Lemma lem7065563 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7065564 (x : real) (y : real) : (term40 x y) = (term41 x y).
Proof. exact (@lem7065563 (term42 x y)). Qed.
Lemma lem7065565 (x : real) (y : real) (z : real) : (term43 x y z) = ((term44 x y z) = (term45 x y z)).
Proof. exact (eq_refl (term43 x y z)). Qed.
Lemma lem7065566 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7065568 (x : real) (y : real) (z : real) : (term46 x y z) = (term47 x y z).
Proof. exact (MK_COMB (@lem7065566) (@lem7065565 x y z)). Qed.
Lemma lem7065569 (x : real) (y : real) : (term48 x y) = (term49 x y).
Proof. exact (fun_ext (fun z : real => @lem7065568 x y z)). Qed.
Lemma lem7065570 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7065571 (x : real) (y : real) : (term41 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem7065570) (@lem7065569 x y)). Qed.
Lemma lem7065572 (x : real) (y : real) : (term40 x y) = (term50 x y).
Proof. exact (TRANS (@lem7065564 x y) (@lem7065571 x y)). Qed.
Lemma lem7065573 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7065574 (x : real) : (term51 x) = (term52 x).
Proof. exact (@lem7065573 (term53 x)). Qed.
Lemma lem7065575 (x : real) (y : real) : (term54 x y) = (term55 x y).
Proof. exact (eq_refl (term54 x y)). Qed.
Lemma lem7065576 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7065577 (x : real) (y : real) : (term56 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem7065576) (@lem7065575 x y)). Qed.
Lemma lem7065578 (x : real) (y : real) : (term56 x y) = (term50 x y).
Proof. exact (TRANS (@lem7065577 x y) (@lem7065572 x y)). Qed.
Lemma lem7065579 (x : real) : (term57 x) = (term58 x).
Proof. exact (fun_ext (fun y : real => @lem7065578 x y)). Qed.
Lemma lem7065580 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7065581 (x : real) : (term52 x) = (term59 x).
Proof. exact (MK_COMB (@lem7065580) (@lem7065579 x)). Qed.
Lemma lem7065582 (x : real) : (term51 x) = (term59 x).
Proof. exact (TRANS (@lem7065574 x) (@lem7065581 x)). Qed.
Lemma lem7065583 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7065584 : term60 = term61.
Proof. exact (@lem7065583 term62). Qed.
Lemma lem7065585 (x : real) : (term63 x) = (term64 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem7065586 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7065587 (x : real) : (term65 x) = (term51 x).
Proof. exact (MK_COMB (@lem7065586) (@lem7065585 x)). Qed.
Lemma lem7065588 (x : real) : (term65 x) = (term59 x).
Proof. exact (TRANS (@lem7065587 x) (@lem7065582 x)). Qed.
Lemma lem7065589 : term66 = term67.
Proof. exact (fun_ext (fun x : real => @lem7065588 x)). Qed.
Lemma lem7065590 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7065591 : term61 = term68.
Proof. exact (MK_COMB (@lem7065590) (@lem7065589)). Qed.
Lemma lem7065592 : term60 = term68.
Proof. exact (TRANS (@lem7065584) (@lem7065591)). Qed.
Lemma lem7065594 (P : real -> Prop) : (term20 P) = (term21 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem7065595 : term69 = term70.
Proof. exact (@lem7065594 term12). Qed.
Lemma lem7065596 (x : real) : (term71 x) = ((term8 x) = x).
Proof. exact (eq_refl (term71 x)). Qed.
Lemma lem7065597 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7065599 (x : real) : (term72 x) = (term73 x).
Proof. exact (MK_COMB (@lem7065597) (@lem7065596 x)). Qed.
Lemma lem7065600 : term74 = term75.
Proof. exact (fun_ext (fun x : real => @lem7065599 x)). Qed.
Lemma lem7065601 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7065602 : term70 = term76.
Proof. exact (MK_COMB (@lem7065601) (@lem7065600)). Qed.
Lemma lem7065603 : term69 = term76.
Proof. exact (TRANS (@lem7065595) (@lem7065602)). Qed.
Lemma lem7065604 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7065605 : term77 = term78.
Proof. exact (MK_COMB (@lem7065604) (@lem7065592)). Qed.
Lemma lem7065606 : term79 = term80.
Proof. exact (MK_COMB (@lem7065605) (@lem7065603)). Qed.
Lemma lem7065607 : term81 = term79.
Proof. exact (@lem17045 term82 term14). Qed.
Lemma lem7065608 : term81 = term80.
Proof. exact (TRANS (@lem7065607) (@lem7065606)). Qed.
Lemma lem7065609 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7065610 : term83 = term84.
Proof. exact (MK_COMB (@lem7065609) (@lem7065561)). Qed.
Lemma lem7065611 : term85 = term86.
Proof. exact (MK_COMB (@lem7065610) (@lem7065608)). Qed.
Lemma lem7065612 : term87 = term85.
Proof. exact (@lem17045 term88 term17). Qed.
Lemma lem7065614 : term87 = term86.
Proof. exact (TRANS (@lem7065612) (@lem7065611)). Qed.
Lemma lem7065617 (y : real) (x : real) : (term27 y x) = (term27 y x).
Proof. exact (eq_refl (term27 y x)). Qed.
Lemma lem7065618 (x : real) : (term29 x) = (term29 x).
Proof. exact (fun_ext (fun y : real => @lem7065617 y x)). Qed.
Lemma lem7065619 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7065620 (x : real) : (term30 x) = (term30 x).
Proof. exact (MK_COMB (@lem7065619) (@lem7065618 x)). Qed.
Lemma lem7065621 : term38 = term38.
Proof. exact (fun_ext (fun x : real => @lem7065620 x)). Qed.
Lemma lem7065622 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7065623 : term39 = term39.
Proof. exact (MK_COMB (@lem7065622) (@lem7065621)). Qed.
Lemma lem7065626 (x : real) (y : real) (z : real) : (term47 x y z) = (term47 x y z).
Proof. exact (eq_refl (term47 x y z)). Qed.
Lemma lem7065627 (x : real) (y : real) : (term49 x y) = (term49 x y).
Proof. exact (fun_ext (fun z : real => @lem7065626 x y z)). Qed.
Lemma lem7065628 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7065629 (x : real) (y : real) : (term50 x y) = (term50 x y).
Proof. exact (MK_COMB (@lem7065628) (@lem7065627 x y)). Qed.
Lemma lem7065630 (x : real) : (term58 x) = (term58 x).
Proof. exact (fun_ext (fun y : real => @lem7065629 x y)). Qed.
Lemma lem7065631 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7065632 (x : real) : (term59 x) = (term59 x).
Proof. exact (MK_COMB (@lem7065631) (@lem7065630 x)). Qed.
Lemma lem7065633 : term67 = term67.
Proof. exact (fun_ext (fun x : real => @lem7065632 x)). Qed.
Lemma lem7065634 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7065635 : term68 = term68.
Proof. exact (MK_COMB (@lem7065634) (@lem7065633)). Qed.
Lemma lem7065638 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem7065639 : term75 = term75.
Proof. exact (fun_ext (fun x : real => @lem7065638 x)). Qed.
Lemma lem7065640 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7065641 : term76 = term76.
Proof. exact (MK_COMB (@lem7065640) (@lem7065639)). Qed.
Lemma lem7065642 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7065643 : term78 = term78.
Proof. exact (MK_COMB (@lem7065642) (@lem7065635)). Qed.
Lemma lem7065644 : term80 = term80.
Proof. exact (MK_COMB (@lem7065643) (@lem7065641)). Qed.
Lemma lem7065645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7065646 : term84 = term84.
Proof. exact (MK_COMB (@lem7065645) (@lem7065623)). Qed.
Lemma lem7065647 : term86 = term86.
Proof. exact (MK_COMB (@lem7065646) (@lem7065644)). Qed.
Lemma lem7065648 : term87 = term86.
Proof. exact (TRANS (@lem7065614) (@lem7065647)). Qed.
Lemma lem7065649 (y : real) (x : real) : (term27 y x) = (term89 y x).
Proof. exact (@lem1988318 (real_add x y) (real_add y x)). Qed.
Lemma lem7065656 (x : real) (y : real) : (real_add y x) = (real_add x y).
Proof. exact (@lem1982761 x y). Qed.
Lemma lem7065665 (x : real) (y : real) : (term90 x y) = (term90 x y).
Proof. exact (eq_refl (term90 x y)). Qed.
Lemma lem7065666 (x : real) (y : real) : (term91 y x) = (term92 x y).
Proof. exact (MK_COMB (@lem7065665 x y) (@lem7065656 x y)). Qed.
Lemma lem7065667 (x : real) (y : real) : (term92 x y) = (term93 x y).
Proof. exact (@lem1982792 (real_add x y) (real_add x y)). Qed.
Lemma lem7065674 (x : real) (y : real) : (term94 x y) = (term95 x y).
Proof. exact (@lem1982781 x term96 y). Qed.
Lemma lem7065675 (x : real) (y : real) : (term97 x y) = (term97 x y).
Proof. exact (eq_refl (term97 x y)). Qed.
Lemma lem7065676 (x : real) (y : real) : (term93 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem7065675 x y) (@lem7065674 x y)). Qed.
Lemma lem7065677 (x : real) (y : real) : (term98 x y) = (term99 x y).
Proof. exact (@lem1982753 x (term100 x) y (term100 y)). Qed.
Lemma lem7065678 (x : real) : (term101 x) = (term102 x).
Proof. exact (@lem1982715 term96 x). Qed.
Lemma lem7065680 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7065681 : term104 = term105.
Proof. exact (@lem7065680 term106). Qed.
Lemma lem7065683 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7065684 : term96 = term109.
Proof. exact (@lem7065683 term106). Qed.
Lemma lem7065685 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7065686 : term110 = term111.
Proof. exact (MK_COMB (@lem7065685) (@lem7065684)). Qed.
Lemma lem7065687 : term112 = term113.
Proof. exact (MK_COMB (@lem7065686) (@lem7065681)). Qed.
Lemma lem7065688 : term114.
Proof. exact (@lem1981473 term96 term104 term104 term104 term4 term104). Qed.
Lemma lem7065690 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7065691 : term116 = term117.
Proof. exact (@lem7065690 (NUMERAL 0) term106). Qed.
Lemma lem7065692 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7065693 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7065694 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7065693 h1) (fun h1 : term117 = True => @lem7065692)). Qed.
Lemma lem7065695 : term117 = True.
Proof. exact (EQ_MP (@lem7065694) (@lem7065692)). Qed.
Lemma lem7065696 : term116 = True.
Proof. exact (TRANS (@lem7065691) (@lem7065695)). Qed.
Lemma lem7065697 : True = term116.
Proof. exact (SYM (@lem7065696)). Qed.
Lemma lem7065698 : term116.
Proof. exact (EQ_MP (@lem7065697) (@lem0)). Qed.
Lemma lem7065699 : term119.
Proof. exact (@lem7065688 (@lem7065698)). Qed.
Lemma lem7065701 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7065702 : term116 = term117.
Proof. exact (@lem7065701 (NUMERAL 0) term106). Qed.
Lemma lem7065703 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7065704 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7065705 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7065704 h1) (fun h1 : term117 = True => @lem7065703)). Qed.
Lemma lem7065706 : term117 = True.
Proof. exact (EQ_MP (@lem7065705) (@lem7065703)). Qed.
Lemma lem7065707 : term116 = True.
Proof. exact (TRANS (@lem7065702) (@lem7065706)). Qed.
Lemma lem7065708 : True = term116.
Proof. exact (SYM (@lem7065707)). Qed.
Lemma lem7065709 : term116.
Proof. exact (EQ_MP (@lem7065708) (@lem0)). Qed.
Lemma lem7065710 : term120.
Proof. exact (@lem7065699 (@lem7065709)). Qed.
Lemma lem7065712 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7065713 : term116 = term117.
Proof. exact (@lem7065712 (NUMERAL 0) term106). Qed.
Lemma lem7065714 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7065715 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7065716 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7065715 h1) (fun h1 : term117 = True => @lem7065714)). Qed.
Lemma lem7065717 : term117 = True.
Proof. exact (EQ_MP (@lem7065716) (@lem7065714)). Qed.
Lemma lem7065718 : term116 = True.
Proof. exact (TRANS (@lem7065713) (@lem7065717)). Qed.
Lemma lem7065719 : True = term116.
Proof. exact (SYM (@lem7065718)). Qed.
Lemma lem7065720 : term116.
Proof. exact (EQ_MP (@lem7065719) (@lem0)). Qed.
Lemma lem7065721 : term121.
Proof. exact (@lem7065710 (@lem7065720)). Qed.
Lemma lem7065723 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7065724 : term124 = term125.
Proof. exact (@lem7065723 term106 term106). Qed.
Lemma lem7065725 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7065726 : term127 = term106.
Proof. exact (EQ_MP (@lem7065725) (@lem940073)). Qed.
Lemma lem7065727 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7065728 : term125 = term104.
Proof. exact (MK_COMB (@lem7065727) (@lem7065726)). Qed.
Lemma lem7065729 : term124 = term104.
Proof. exact (TRANS (@lem7065724) (@lem7065728)). Qed.
Lemma lem7065731 (m : nat) (n : nat) : (term128 m n) = (term129 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7065732 : term130 = term131.
Proof. exact (@lem7065731 term106 term106). Qed.
Lemma lem7065733 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7065734 : term127 = term106.
Proof. exact (EQ_MP (@lem7065733) (@lem940073)). Qed.
Lemma lem7065735 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7065736 : term125 = term104.
Proof. exact (MK_COMB (@lem7065735) (@lem7065734)). Qed.
Lemma lem7065737 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7065738 : term131 = term96.
Proof. exact (MK_COMB (@lem7065737) (@lem7065736)). Qed.
Lemma lem7065739 : term130 = term96.
Proof. exact (TRANS (@lem7065732) (@lem7065738)). Qed.
Lemma lem7065740 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7065741 : term132 = term110.
Proof. exact (MK_COMB (@lem7065740) (@lem7065739)). Qed.
Lemma lem7065742 : term133 = term112.
Proof. exact (MK_COMB (@lem7065741) (@lem7065729)). Qed.
Lemma lem7065744 (m : nat) : (term134 m) = term4.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7065745 : term112 = term4.
Proof. exact (@lem7065744 term106). Qed.
Lemma lem7065746 : term133 = term4.
Proof. exact (TRANS (@lem7065742) (@lem7065745)). Qed.
Lemma lem7065747 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7065748 : term135 = term136.
Proof. exact (MK_COMB (@lem7065747) (@lem7065746)). Qed.
Lemma lem7065749 : term104 = term104.
Proof. exact (eq_refl term104). Qed.
Lemma lem7065750 : term137 = term138.
Proof. exact (MK_COMB (@lem7065748) (@lem7065749)). Qed.
Lemma lem7065752 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7065753 : term138 = term4.
Proof. exact (@lem7065752 term106). Qed.
Lemma lem7065754 : term137 = term4.
Proof. exact (TRANS (@lem7065750) (@lem7065753)). Qed.
Lemma lem7065756 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7065757 : term124 = term125.
Proof. exact (@lem7065756 term106 term106). Qed.
Lemma lem7065758 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7065759 : term127 = term106.
Proof. exact (EQ_MP (@lem7065758) (@lem940073)). Qed.
Lemma lem7065760 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7065761 : term125 = term104.
Proof. exact (MK_COMB (@lem7065760) (@lem7065759)). Qed.
Lemma lem7065762 : term124 = term104.
Proof. exact (TRANS (@lem7065757) (@lem7065761)). Qed.
Lemma lem7065763 : term136 = term136.
Proof. exact (eq_refl term136). Qed.
Lemma lem7065764 : term140 = term138.
Proof. exact (MK_COMB (@lem7065763) (@lem7065762)). Qed.
Lemma lem7065766 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7065767 : term138 = term4.
Proof. exact (@lem7065766 term106). Qed.
Lemma lem7065768 : term140 = term4.
Proof. exact (TRANS (@lem7065764) (@lem7065767)). Qed.
Lemma lem7065769 : term4 = term140.
Proof. exact (SYM (@lem7065768)). Qed.
Lemma lem7065770 : term137 = term140.
Proof. exact (TRANS (@lem7065754) (@lem7065769)). Qed.
Lemma lem7065771 : term113 = term141.
Proof. exact (@lem7065721 (@lem7065770)). Qed.
Lemma lem7065772 : term112 = term141.
Proof. exact (TRANS (@lem7065687) (@lem7065771)). Qed.
Lemma lem7065774 (x : real) : (term142 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7065775 : term141 = term4.
Proof. exact (@lem7065774 term4). Qed.
Lemma lem7065776 : term112 = term4.
Proof. exact (TRANS (@lem7065772) (@lem7065775)). Qed.
Lemma lem7065777 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7065778 : term143 = term136.
Proof. exact (MK_COMB (@lem7065777) (@lem7065776)). Qed.
Lemma lem7065779 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7065780 (x : real) : (term102 x) = (term144 x).
Proof. exact (MK_COMB (@lem7065778) (@lem7065779 x)). Qed.
Lemma lem7065781 (x : real) : (term101 x) = (term144 x).
Proof. exact (TRANS (@lem7065678 x) (@lem7065780 x)). Qed.
Lemma lem7065782 (x : real) : (term144 x) = term4.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7065783 (x : real) : (term101 x) = term4.
Proof. exact (TRANS (@lem7065781 x) (@lem7065782 x)). Qed.
Lemma lem7065784 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7065785 (x : real) : (term145 x) = term6.
Proof. exact (MK_COMB (@lem7065784) (@lem7065783 x)). Qed.
Lemma lem7065786 (y : real) : (term101 y) = (term102 y).
Proof. exact (@lem1982715 term96 y). Qed.
Lemma lem7065788 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7065789 : term104 = term105.
Proof. exact (@lem7065788 term106). Qed.
Lemma lem7065791 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7065792 : term96 = term109.
Proof. exact (@lem7065791 term106). Qed.
Lemma lem7065793 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7065794 : term110 = term111.
Proof. exact (MK_COMB (@lem7065793) (@lem7065792)). Qed.
Lemma lem7065795 : term112 = term113.
Proof. exact (MK_COMB (@lem7065794) (@lem7065789)). Qed.
Lemma lem7065796 : term114.
Proof. exact (@lem1981473 term96 term104 term104 term104 term4 term104). Qed.
Lemma lem7065798 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7065799 : term116 = term117.
Proof. exact (@lem7065798 (NUMERAL 0) term106). Qed.
Lemma lem7065800 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7065801 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7065802 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7065801 h1) (fun h1 : term117 = True => @lem7065800)). Qed.
Lemma lem7065803 : term117 = True.
Proof. exact (EQ_MP (@lem7065802) (@lem7065800)). Qed.
Lemma lem7065804 : term116 = True.
Proof. exact (TRANS (@lem7065799) (@lem7065803)). Qed.
Lemma lem7065805 : True = term116.
Proof. exact (SYM (@lem7065804)). Qed.
Lemma lem7065806 : term116.
Proof. exact (EQ_MP (@lem7065805) (@lem0)). Qed.
Lemma lem7065807 : term119.
Proof. exact (@lem7065796 (@lem7065806)). Qed.
Lemma lem7065809 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7065810 : term116 = term117.
Proof. exact (@lem7065809 (NUMERAL 0) term106). Qed.
Lemma lem7065811 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7065812 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7065813 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7065812 h1) (fun h1 : term117 = True => @lem7065811)). Qed.
Lemma lem7065814 : term117 = True.
Proof. exact (EQ_MP (@lem7065813) (@lem7065811)). Qed.
Lemma lem7065815 : term116 = True.
Proof. exact (TRANS (@lem7065810) (@lem7065814)). Qed.
Lemma lem7065816 : True = term116.
Proof. exact (SYM (@lem7065815)). Qed.
Lemma lem7065817 : term116.
Proof. exact (EQ_MP (@lem7065816) (@lem0)). Qed.
Lemma lem7065818 : term120.
Proof. exact (@lem7065807 (@lem7065817)). Qed.
Lemma lem7065820 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7065821 : term116 = term117.
Proof. exact (@lem7065820 (NUMERAL 0) term106). Qed.
Lemma lem7065822 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7065823 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7065824 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7065823 h1) (fun h1 : term117 = True => @lem7065822)). Qed.
Lemma lem7065825 : term117 = True.
Proof. exact (EQ_MP (@lem7065824) (@lem7065822)). Qed.
Lemma lem7065826 : term116 = True.
Proof. exact (TRANS (@lem7065821) (@lem7065825)). Qed.
Lemma lem7065827 : True = term116.
Proof. exact (SYM (@lem7065826)). Qed.
Lemma lem7065828 : term116.
Proof. exact (EQ_MP (@lem7065827) (@lem0)). Qed.
Lemma lem7065829 : term121.
Proof. exact (@lem7065818 (@lem7065828)). Qed.
Lemma lem7065831 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7065832 : term124 = term125.
Proof. exact (@lem7065831 term106 term106). Qed.
Lemma lem7065833 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7065834 : term127 = term106.
Proof. exact (EQ_MP (@lem7065833) (@lem940073)). Qed.
Lemma lem7065835 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7065836 : term125 = term104.
Proof. exact (MK_COMB (@lem7065835) (@lem7065834)). Qed.
Lemma lem7065837 : term124 = term104.
Proof. exact (TRANS (@lem7065832) (@lem7065836)). Qed.
Lemma lem7065839 (m : nat) (n : nat) : (term128 m n) = (term129 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7065840 : term130 = term131.
Proof. exact (@lem7065839 term106 term106). Qed.
Lemma lem7065841 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7065842 : term127 = term106.
Proof. exact (EQ_MP (@lem7065841) (@lem940073)). Qed.
Lemma lem7065843 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7065844 : term125 = term104.
Proof. exact (MK_COMB (@lem7065843) (@lem7065842)). Qed.
Lemma lem7065845 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7065846 : term131 = term96.
Proof. exact (MK_COMB (@lem7065845) (@lem7065844)). Qed.
Lemma lem7065847 : term130 = term96.
Proof. exact (TRANS (@lem7065840) (@lem7065846)). Qed.
Lemma lem7065848 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7065849 : term132 = term110.
Proof. exact (MK_COMB (@lem7065848) (@lem7065847)). Qed.
Lemma lem7065850 : term133 = term112.
Proof. exact (MK_COMB (@lem7065849) (@lem7065837)). Qed.
Lemma lem7065852 (m : nat) : (term134 m) = term4.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7065853 : term112 = term4.
Proof. exact (@lem7065852 term106). Qed.
Lemma lem7065854 : term133 = term4.
Proof. exact (TRANS (@lem7065850) (@lem7065853)). Qed.
Lemma lem7065855 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7065856 : term135 = term136.
Proof. exact (MK_COMB (@lem7065855) (@lem7065854)). Qed.
Lemma lem7065857 : term104 = term104.
Proof. exact (eq_refl term104). Qed.
Lemma lem7065858 : term137 = term138.
Proof. exact (MK_COMB (@lem7065856) (@lem7065857)). Qed.
Lemma lem7065860 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7065861 : term138 = term4.
Proof. exact (@lem7065860 term106). Qed.
Lemma lem7065862 : term137 = term4.
Proof. exact (TRANS (@lem7065858) (@lem7065861)). Qed.
Lemma lem7065864 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7065865 : term124 = term125.
Proof. exact (@lem7065864 term106 term106). Qed.
Lemma lem7065866 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7065867 : term127 = term106.
Proof. exact (EQ_MP (@lem7065866) (@lem940073)). Qed.
Lemma lem7065868 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7065869 : term125 = term104.
Proof. exact (MK_COMB (@lem7065868) (@lem7065867)). Qed.
Lemma lem7065870 : term124 = term104.
Proof. exact (TRANS (@lem7065865) (@lem7065869)). Qed.
Lemma lem7065871 : term136 = term136.
Proof. exact (eq_refl term136). Qed.
Lemma lem7065872 : term140 = term138.
Proof. exact (MK_COMB (@lem7065871) (@lem7065870)). Qed.
Lemma lem7065874 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7065875 : term138 = term4.
Proof. exact (@lem7065874 term106). Qed.
Lemma lem7065876 : term140 = term4.
Proof. exact (TRANS (@lem7065872) (@lem7065875)). Qed.
Lemma lem7065877 : term4 = term140.
Proof. exact (SYM (@lem7065876)). Qed.
Lemma lem7065878 : term137 = term140.
Proof. exact (TRANS (@lem7065862) (@lem7065877)). Qed.
Lemma lem7065879 : term113 = term141.
Proof. exact (@lem7065829 (@lem7065878)). Qed.
Lemma lem7065880 : term112 = term141.
Proof. exact (TRANS (@lem7065795) (@lem7065879)). Qed.
Lemma lem7065882 (x : real) : (term142 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7065883 : term141 = term4.
Proof. exact (@lem7065882 term4). Qed.
Lemma lem7065884 : term112 = term4.
Proof. exact (TRANS (@lem7065880) (@lem7065883)). Qed.
Lemma lem7065885 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7065886 : term143 = term136.
Proof. exact (MK_COMB (@lem7065885) (@lem7065884)). Qed.
Lemma lem7065887 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7065888 (y : real) : (term102 y) = (term144 y).
Proof. exact (MK_COMB (@lem7065886) (@lem7065887 y)). Qed.
Lemma lem7065889 (y : real) : (term101 y) = (term144 y).
Proof. exact (TRANS (@lem7065786 y) (@lem7065888 y)). Qed.
Lemma lem7065890 (y : real) : (term144 y) = term4.
Proof. exact (@lem1982719 y). Qed.
Lemma lem7065891 (y : real) : (term101 y) = term4.
Proof. exact (TRANS (@lem7065889 y) (@lem7065890 y)). Qed.
Lemma lem7065892 (x : real) (y : real) : (term99 x y) = term146.
Proof. exact (MK_COMB (@lem7065785 x) (@lem7065891 y)). Qed.
Lemma lem7065893 (x : real) (y : real) : (term98 x y) = term146.
Proof. exact (TRANS (@lem7065677 x y) (@lem7065892 x y)). Qed.
Lemma lem7065894 : term146 = term4.
Proof. exact (@lem1982721 term4). Qed.
Lemma lem7065895 (x : real) (y : real) : (term98 x y) = term4.
Proof. exact (TRANS (@lem7065893 x y) (@lem7065894)). Qed.
Lemma lem7065896 (x : real) (y : real) : (term93 x y) = term4.
Proof. exact (TRANS (@lem7065676 x y) (@lem7065895 x y)). Qed.
Lemma lem7065897 (x : real) (y : real) : (term92 x y) = term4.
Proof. exact (TRANS (@lem7065667 x y) (@lem7065896 x y)). Qed.
Lemma lem7065898 (y : real) (x : real) : (term91 y x) = term4.
Proof. exact (TRANS (@lem7065666 x y) (@lem7065897 x y)). Qed.
Lemma lem7065899 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7065900 (y : real) (x : real) : (term147 y x) = term148.
Proof. exact (MK_COMB (@lem7065899) (@lem7065898 y x)). Qed.
Lemma lem7065901 : term148 = term149.
Proof. exact (@lem1982785 term4). Qed.
Lemma lem7065903 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7065904 : term4 = term141.
Proof. exact (@lem7065903 (NUMERAL 0)). Qed.
Lemma lem7065906 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7065907 : term96 = term109.
Proof. exact (@lem7065906 term106). Qed.
Lemma lem7065908 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7065909 : term150 = term151.
Proof. exact (MK_COMB (@lem7065908) (@lem7065907)). Qed.
Lemma lem7065910 : term149 = term152.
Proof. exact (MK_COMB (@lem7065909) (@lem7065904)). Qed.
Lemma lem7065911 : term152 = term153.
Proof. exact (@lem1981613 term96 term4 term104 term104). Qed.
Lemma lem7065913 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7065914 : term124 = term125.
Proof. exact (@lem7065913 term106 term106). Qed.
Lemma lem7065915 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7065916 : term127 = term106.
Proof. exact (EQ_MP (@lem7065915) (@lem940073)). Qed.
Lemma lem7065917 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7065918 : term125 = term104.
Proof. exact (MK_COMB (@lem7065917) (@lem7065916)). Qed.
Lemma lem7065919 : term124 = term104.
Proof. exact (TRANS (@lem7065914) (@lem7065918)). Qed.
Lemma lem7065921 (x : nat) : (term154 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7065922 : term149 = term4.
Proof. exact (@lem7065921 term106). Qed.
Lemma lem7065923 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7065924 : term155 = term156.
Proof. exact (MK_COMB (@lem7065923) (@lem7065922)). Qed.
Lemma lem7065925 : term153 = term141.
Proof. exact (MK_COMB (@lem7065924) (@lem7065919)). Qed.
Lemma lem7065926 : term152 = term141.
Proof. exact (TRANS (@lem7065911) (@lem7065925)). Qed.
Lemma lem7065927 : term149 = term141.
Proof. exact (TRANS (@lem7065910) (@lem7065926)). Qed.
Lemma lem7065929 (x : real) : (term142 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7065930 : term141 = term4.
Proof. exact (@lem7065929 term4). Qed.
Lemma lem7065931 : term149 = term4.
Proof. exact (TRANS (@lem7065927) (@lem7065930)). Qed.
Lemma lem7065932 : term148 = term4.
Proof. exact (TRANS (@lem7065901) (@lem7065931)). Qed.
Lemma lem7065933 (y : real) (x : real) : (term157 y x) = (term157 y x).
Proof. exact (eq_refl (term157 y x)). Qed.
Lemma lem7065934 (y : real) (x : real) : ((term147 y x) = term148) = ((term147 y x) = term4).
Proof. exact (MK_COMB (@lem7065933 y x) (@lem7065932)). Qed.
Lemma lem7065935 (y : real) (x : real) : (term147 y x) = term4.
Proof. exact (EQ_MP (@lem7065934 y x) (@lem7065900 y x)). Qed.
Lemma lem7065936 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7065937 (y : real) (x : real) : (term158 y x) = term159.
Proof. exact (MK_COMB (@lem7065936) (@lem7065935 y x)). Qed.
Lemma lem7065938 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem7065939 (y : real) (x : real) : (term160 y x) = term161.
Proof. exact (MK_COMB (@lem7065937 y x) (@lem7065938)). Qed.
Lemma lem7065940 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7065941 (y : real) (x : real) : (term162 y x) = term159.
Proof. exact (MK_COMB (@lem7065940) (@lem7065898 y x)). Qed.
Lemma lem7065942 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem7065943 (y : real) (x : real) : (term163 y x) = term161.
Proof. exact (MK_COMB (@lem7065941 y x) (@lem7065942)). Qed.
Lemma lem7065944 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7065945 (y : real) (x : real) : (term164 y x) = term165.
Proof. exact (MK_COMB (@lem7065944) (@lem7065943 y x)). Qed.
Lemma lem7065946 (y : real) (x : real) : (term89 y x) = term166.
Proof. exact (MK_COMB (@lem7065945 y x) (@lem7065939 y x)). Qed.
Lemma lem7065947 (y : real) (x : real) : (term27 y x) = term166.
Proof. exact (TRANS (@lem7065649 y x) (@lem7065946 y x)). Qed.
Lemma lem7065948 (x : real) : (term29 x) = term167.
Proof. exact (fun_ext (fun y : real => @lem7065947 y x)). Qed.
Lemma lem7065949 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7065950 (x : real) : (term30 x) = term168.
Proof. exact (MK_COMB (@lem7065949) (@lem7065948 x)). Qed.
Lemma lem7065951 : term38 = term169.
Proof. exact (fun_ext (fun x : real => @lem7065950 x)). Qed.
Lemma lem7065952 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7065953 : term39 = term170.
Proof. exact (MK_COMB (@lem7065952) (@lem7065951)). Qed.
Lemma lem7065954 (x : real) (y : real) (z : real) : (term47 x y z) = (term171 x y z).
Proof. exact (@lem1988318 (term44 x y z) (term45 x y z)). Qed.
Lemma lem7065971 (x : real) (y : real) (z : real) : (term45 x y z) = (term44 x y z).
Proof. exact (@lem1982755 x y z). Qed.
Lemma lem7065986 (x : real) (y : real) (z : real) : (term172 x y z) = (term172 x y z).
Proof. exact (eq_refl (term172 x y z)). Qed.
Lemma lem7065987 (x : real) (y : real) (z : real) : (term173 x y z) = (term174 x y z).
Proof. exact (MK_COMB (@lem7065986 x y z) (@lem7065971 x y z)). Qed.
Lemma lem7065988 (x : real) (y : real) (z : real) : (term174 x y z) = (term175 x y z).
Proof. exact (@lem1982792 (term44 x y z) (term44 x y z)). Qed.
Lemma lem7065989 (x : real) (y : real) (z : real) : (term176 x y z) = (term177 x y z).
Proof. exact (@lem1982781 x term96 (real_add y z)). Qed.
Lemma lem7065996 (y : real) (z : real) : (term94 y z) = (term95 y z).
Proof. exact (@lem1982781 y term96 z). Qed.
Lemma lem7065999 (x : real) : (term178 x) = (term178 x).
Proof. exact (eq_refl (term178 x)). Qed.
Lemma lem7066000 (x : real) (y : real) (z : real) : (term177 x y z) = (term179 x y z).
Proof. exact (MK_COMB (@lem7065999 x) (@lem7065996 y z)). Qed.
Lemma lem7066001 (x : real) (y : real) (z : real) : (term176 x y z) = (term179 x y z).
Proof. exact (TRANS (@lem7065989 x y z) (@lem7066000 x y z)). Qed.
Lemma lem7066002 (x : real) (y : real) (z : real) : (term180 x y z) = (term180 x y z).
Proof. exact (eq_refl (term180 x y z)). Qed.
Lemma lem7066003 (x : real) (y : real) (z : real) : (term175 x y z) = (term181 x y z).
Proof. exact (MK_COMB (@lem7066002 x y z) (@lem7066001 x y z)). Qed.
Lemma lem7066004 (x : real) (y : real) (z : real) : (term181 x y z) = (term182 x y z).
Proof. exact (@lem1982753 x (term100 x) (real_add y z) (term95 y z)). Qed.
Lemma lem7066005 (x : real) : (term101 x) = (term102 x).
Proof. exact (@lem1982715 term96 x). Qed.
Lemma lem7066007 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7066008 : term104 = term105.
Proof. exact (@lem7066007 term106). Qed.
Lemma lem7066010 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7066011 : term96 = term109.
Proof. exact (@lem7066010 term106). Qed.
Lemma lem7066012 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7066013 : term110 = term111.
Proof. exact (MK_COMB (@lem7066012) (@lem7066011)). Qed.
Lemma lem7066014 : term112 = term113.
Proof. exact (MK_COMB (@lem7066013) (@lem7066008)). Qed.
Lemma lem7066015 : term114.
Proof. exact (@lem1981473 term96 term104 term104 term104 term4 term104). Qed.
Lemma lem7066017 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066018 : term116 = term117.
Proof. exact (@lem7066017 (NUMERAL 0) term106). Qed.
Lemma lem7066019 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066020 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066021 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066020 h1) (fun h1 : term117 = True => @lem7066019)). Qed.
Lemma lem7066022 : term117 = True.
Proof. exact (EQ_MP (@lem7066021) (@lem7066019)). Qed.
Lemma lem7066023 : term116 = True.
Proof. exact (TRANS (@lem7066018) (@lem7066022)). Qed.
Lemma lem7066024 : True = term116.
Proof. exact (SYM (@lem7066023)). Qed.
Lemma lem7066025 : term116.
Proof. exact (EQ_MP (@lem7066024) (@lem0)). Qed.
Lemma lem7066026 : term119.
Proof. exact (@lem7066015 (@lem7066025)). Qed.
Lemma lem7066028 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066029 : term116 = term117.
Proof. exact (@lem7066028 (NUMERAL 0) term106). Qed.
Lemma lem7066030 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066031 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066032 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066031 h1) (fun h1 : term117 = True => @lem7066030)). Qed.
Lemma lem7066033 : term117 = True.
Proof. exact (EQ_MP (@lem7066032) (@lem7066030)). Qed.
Lemma lem7066034 : term116 = True.
Proof. exact (TRANS (@lem7066029) (@lem7066033)). Qed.
Lemma lem7066035 : True = term116.
Proof. exact (SYM (@lem7066034)). Qed.
Lemma lem7066036 : term116.
Proof. exact (EQ_MP (@lem7066035) (@lem0)). Qed.
Lemma lem7066037 : term120.
Proof. exact (@lem7066026 (@lem7066036)). Qed.
Lemma lem7066039 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066040 : term116 = term117.
Proof. exact (@lem7066039 (NUMERAL 0) term106). Qed.
Lemma lem7066041 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066042 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066043 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066042 h1) (fun h1 : term117 = True => @lem7066041)). Qed.
Lemma lem7066044 : term117 = True.
Proof. exact (EQ_MP (@lem7066043) (@lem7066041)). Qed.
Lemma lem7066045 : term116 = True.
Proof. exact (TRANS (@lem7066040) (@lem7066044)). Qed.
Lemma lem7066046 : True = term116.
Proof. exact (SYM (@lem7066045)). Qed.
Lemma lem7066047 : term116.
Proof. exact (EQ_MP (@lem7066046) (@lem0)). Qed.
Lemma lem7066048 : term121.
Proof. exact (@lem7066037 (@lem7066047)). Qed.
Lemma lem7066050 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7066051 : term124 = term125.
Proof. exact (@lem7066050 term106 term106). Qed.
Lemma lem7066052 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7066053 : term127 = term106.
Proof. exact (EQ_MP (@lem7066052) (@lem940073)). Qed.
Lemma lem7066054 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7066055 : term125 = term104.
Proof. exact (MK_COMB (@lem7066054) (@lem7066053)). Qed.
Lemma lem7066056 : term124 = term104.
Proof. exact (TRANS (@lem7066051) (@lem7066055)). Qed.
Lemma lem7066058 (m : nat) (n : nat) : (term128 m n) = (term129 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7066059 : term130 = term131.
Proof. exact (@lem7066058 term106 term106). Qed.
Lemma lem7066060 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7066061 : term127 = term106.
Proof. exact (EQ_MP (@lem7066060) (@lem940073)). Qed.
Lemma lem7066062 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7066063 : term125 = term104.
Proof. exact (MK_COMB (@lem7066062) (@lem7066061)). Qed.
Lemma lem7066064 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7066065 : term131 = term96.
Proof. exact (MK_COMB (@lem7066064) (@lem7066063)). Qed.
Lemma lem7066066 : term130 = term96.
Proof. exact (TRANS (@lem7066059) (@lem7066065)). Qed.
Lemma lem7066067 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7066068 : term132 = term110.
Proof. exact (MK_COMB (@lem7066067) (@lem7066066)). Qed.
Lemma lem7066069 : term133 = term112.
Proof. exact (MK_COMB (@lem7066068) (@lem7066056)). Qed.
Lemma lem7066071 (m : nat) : (term134 m) = term4.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7066072 : term112 = term4.
Proof. exact (@lem7066071 term106). Qed.
Lemma lem7066073 : term133 = term4.
Proof. exact (TRANS (@lem7066069) (@lem7066072)). Qed.
Lemma lem7066074 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7066075 : term135 = term136.
Proof. exact (MK_COMB (@lem7066074) (@lem7066073)). Qed.
Lemma lem7066076 : term104 = term104.
Proof. exact (eq_refl term104). Qed.
Lemma lem7066077 : term137 = term138.
Proof. exact (MK_COMB (@lem7066075) (@lem7066076)). Qed.
Lemma lem7066079 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7066080 : term138 = term4.
Proof. exact (@lem7066079 term106). Qed.
Lemma lem7066081 : term137 = term4.
Proof. exact (TRANS (@lem7066077) (@lem7066080)). Qed.
Lemma lem7066083 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7066084 : term124 = term125.
Proof. exact (@lem7066083 term106 term106). Qed.
Lemma lem7066085 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7066086 : term127 = term106.
Proof. exact (EQ_MP (@lem7066085) (@lem940073)). Qed.
Lemma lem7066087 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7066088 : term125 = term104.
Proof. exact (MK_COMB (@lem7066087) (@lem7066086)). Qed.
Lemma lem7066089 : term124 = term104.
Proof. exact (TRANS (@lem7066084) (@lem7066088)). Qed.
Lemma lem7066090 : term136 = term136.
Proof. exact (eq_refl term136). Qed.
Lemma lem7066091 : term140 = term138.
Proof. exact (MK_COMB (@lem7066090) (@lem7066089)). Qed.
Lemma lem7066093 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7066094 : term138 = term4.
Proof. exact (@lem7066093 term106). Qed.
Lemma lem7066095 : term140 = term4.
Proof. exact (TRANS (@lem7066091) (@lem7066094)). Qed.
Lemma lem7066096 : term4 = term140.
Proof. exact (SYM (@lem7066095)). Qed.
Lemma lem7066097 : term137 = term140.
Proof. exact (TRANS (@lem7066081) (@lem7066096)). Qed.
Lemma lem7066098 : term113 = term141.
Proof. exact (@lem7066048 (@lem7066097)). Qed.
Lemma lem7066099 : term112 = term141.
Proof. exact (TRANS (@lem7066014) (@lem7066098)). Qed.
Lemma lem7066101 (x : real) : (term142 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7066102 : term141 = term4.
Proof. exact (@lem7066101 term4). Qed.
Lemma lem7066103 : term112 = term4.
Proof. exact (TRANS (@lem7066099) (@lem7066102)). Qed.
Lemma lem7066104 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7066105 : term143 = term136.
Proof. exact (MK_COMB (@lem7066104) (@lem7066103)). Qed.
Lemma lem7066106 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7066107 (x : real) : (term102 x) = (term144 x).
Proof. exact (MK_COMB (@lem7066105) (@lem7066106 x)). Qed.
Lemma lem7066108 (x : real) : (term101 x) = (term144 x).
Proof. exact (TRANS (@lem7066005 x) (@lem7066107 x)). Qed.
Lemma lem7066109 (x : real) : (term144 x) = term4.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7066110 (x : real) : (term101 x) = term4.
Proof. exact (TRANS (@lem7066108 x) (@lem7066109 x)). Qed.
Lemma lem7066111 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7066112 (x : real) : (term145 x) = term6.
Proof. exact (MK_COMB (@lem7066111) (@lem7066110 x)). Qed.
Lemma lem7066113 (y : real) (z : real) : (term98 y z) = (term99 y z).
Proof. exact (@lem1982753 y (term100 y) z (term100 z)). Qed.
Lemma lem7066114 (y : real) : (term101 y) = (term102 y).
Proof. exact (@lem1982715 term96 y). Qed.
Lemma lem7066116 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7066117 : term104 = term105.
Proof. exact (@lem7066116 term106). Qed.
Lemma lem7066119 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7066120 : term96 = term109.
Proof. exact (@lem7066119 term106). Qed.
Lemma lem7066121 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7066122 : term110 = term111.
Proof. exact (MK_COMB (@lem7066121) (@lem7066120)). Qed.
Lemma lem7066123 : term112 = term113.
Proof. exact (MK_COMB (@lem7066122) (@lem7066117)). Qed.
Lemma lem7066124 : term114.
Proof. exact (@lem1981473 term96 term104 term104 term104 term4 term104). Qed.
Lemma lem7066126 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066127 : term116 = term117.
Proof. exact (@lem7066126 (NUMERAL 0) term106). Qed.
Lemma lem7066128 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066129 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066130 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066129 h1) (fun h1 : term117 = True => @lem7066128)). Qed.
Lemma lem7066131 : term117 = True.
Proof. exact (EQ_MP (@lem7066130) (@lem7066128)). Qed.
Lemma lem7066132 : term116 = True.
Proof. exact (TRANS (@lem7066127) (@lem7066131)). Qed.
Lemma lem7066133 : True = term116.
Proof. exact (SYM (@lem7066132)). Qed.
Lemma lem7066134 : term116.
Proof. exact (EQ_MP (@lem7066133) (@lem0)). Qed.
Lemma lem7066135 : term119.
Proof. exact (@lem7066124 (@lem7066134)). Qed.
Lemma lem7066137 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066138 : term116 = term117.
Proof. exact (@lem7066137 (NUMERAL 0) term106). Qed.
Lemma lem7066139 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066140 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066141 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066140 h1) (fun h1 : term117 = True => @lem7066139)). Qed.
Lemma lem7066142 : term117 = True.
Proof. exact (EQ_MP (@lem7066141) (@lem7066139)). Qed.
Lemma lem7066143 : term116 = True.
Proof. exact (TRANS (@lem7066138) (@lem7066142)). Qed.
Lemma lem7066144 : True = term116.
Proof. exact (SYM (@lem7066143)). Qed.
Lemma lem7066145 : term116.
Proof. exact (EQ_MP (@lem7066144) (@lem0)). Qed.
Lemma lem7066146 : term120.
Proof. exact (@lem7066135 (@lem7066145)). Qed.
Lemma lem7066148 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066149 : term116 = term117.
Proof. exact (@lem7066148 (NUMERAL 0) term106). Qed.
Lemma lem7066150 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066151 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066152 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066151 h1) (fun h1 : term117 = True => @lem7066150)). Qed.
Lemma lem7066153 : term117 = True.
Proof. exact (EQ_MP (@lem7066152) (@lem7066150)). Qed.
Lemma lem7066154 : term116 = True.
Proof. exact (TRANS (@lem7066149) (@lem7066153)). Qed.
Lemma lem7066155 : True = term116.
Proof. exact (SYM (@lem7066154)). Qed.
Lemma lem7066156 : term116.
Proof. exact (EQ_MP (@lem7066155) (@lem0)). Qed.
Lemma lem7066157 : term121.
Proof. exact (@lem7066146 (@lem7066156)). Qed.
Lemma lem7066159 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7066160 : term124 = term125.
Proof. exact (@lem7066159 term106 term106). Qed.
Lemma lem7066161 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7066162 : term127 = term106.
Proof. exact (EQ_MP (@lem7066161) (@lem940073)). Qed.
Lemma lem7066163 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7066164 : term125 = term104.
Proof. exact (MK_COMB (@lem7066163) (@lem7066162)). Qed.
Lemma lem7066165 : term124 = term104.
Proof. exact (TRANS (@lem7066160) (@lem7066164)). Qed.
Lemma lem7066167 (m : nat) (n : nat) : (term128 m n) = (term129 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7066168 : term130 = term131.
Proof. exact (@lem7066167 term106 term106). Qed.
Lemma lem7066169 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7066170 : term127 = term106.
Proof. exact (EQ_MP (@lem7066169) (@lem940073)). Qed.
Lemma lem7066171 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7066172 : term125 = term104.
Proof. exact (MK_COMB (@lem7066171) (@lem7066170)). Qed.
Lemma lem7066173 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7066174 : term131 = term96.
Proof. exact (MK_COMB (@lem7066173) (@lem7066172)). Qed.
Lemma lem7066175 : term130 = term96.
Proof. exact (TRANS (@lem7066168) (@lem7066174)). Qed.
Lemma lem7066176 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7066177 : term132 = term110.
Proof. exact (MK_COMB (@lem7066176) (@lem7066175)). Qed.
Lemma lem7066178 : term133 = term112.
Proof. exact (MK_COMB (@lem7066177) (@lem7066165)). Qed.
Lemma lem7066180 (m : nat) : (term134 m) = term4.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7066181 : term112 = term4.
Proof. exact (@lem7066180 term106). Qed.
Lemma lem7066182 : term133 = term4.
Proof. exact (TRANS (@lem7066178) (@lem7066181)). Qed.
Lemma lem7066183 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7066184 : term135 = term136.
Proof. exact (MK_COMB (@lem7066183) (@lem7066182)). Qed.
Lemma lem7066185 : term104 = term104.
Proof. exact (eq_refl term104). Qed.
Lemma lem7066186 : term137 = term138.
Proof. exact (MK_COMB (@lem7066184) (@lem7066185)). Qed.
Lemma lem7066188 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7066189 : term138 = term4.
Proof. exact (@lem7066188 term106). Qed.
Lemma lem7066190 : term137 = term4.
Proof. exact (TRANS (@lem7066186) (@lem7066189)). Qed.
Lemma lem7066192 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7066193 : term124 = term125.
Proof. exact (@lem7066192 term106 term106). Qed.
Lemma lem7066194 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7066195 : term127 = term106.
Proof. exact (EQ_MP (@lem7066194) (@lem940073)). Qed.
Lemma lem7066196 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7066197 : term125 = term104.
Proof. exact (MK_COMB (@lem7066196) (@lem7066195)). Qed.
Lemma lem7066198 : term124 = term104.
Proof. exact (TRANS (@lem7066193) (@lem7066197)). Qed.
Lemma lem7066199 : term136 = term136.
Proof. exact (eq_refl term136). Qed.
Lemma lem7066200 : term140 = term138.
Proof. exact (MK_COMB (@lem7066199) (@lem7066198)). Qed.
Lemma lem7066202 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7066203 : term138 = term4.
Proof. exact (@lem7066202 term106). Qed.
Lemma lem7066204 : term140 = term4.
Proof. exact (TRANS (@lem7066200) (@lem7066203)). Qed.
Lemma lem7066205 : term4 = term140.
Proof. exact (SYM (@lem7066204)). Qed.
Lemma lem7066206 : term137 = term140.
Proof. exact (TRANS (@lem7066190) (@lem7066205)). Qed.
Lemma lem7066207 : term113 = term141.
Proof. exact (@lem7066157 (@lem7066206)). Qed.
Lemma lem7066208 : term112 = term141.
Proof. exact (TRANS (@lem7066123) (@lem7066207)). Qed.
Lemma lem7066210 (x : real) : (term142 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7066211 : term141 = term4.
Proof. exact (@lem7066210 term4). Qed.
Lemma lem7066212 : term112 = term4.
Proof. exact (TRANS (@lem7066208) (@lem7066211)). Qed.
Lemma lem7066213 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7066214 : term143 = term136.
Proof. exact (MK_COMB (@lem7066213) (@lem7066212)). Qed.
Lemma lem7066215 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem7066216 (y : real) : (term102 y) = (term144 y).
Proof. exact (MK_COMB (@lem7066214) (@lem7066215 y)). Qed.
Lemma lem7066217 (y : real) : (term101 y) = (term144 y).
Proof. exact (TRANS (@lem7066114 y) (@lem7066216 y)). Qed.
Lemma lem7066218 (y : real) : (term144 y) = term4.
Proof. exact (@lem1982719 y). Qed.
Lemma lem7066219 (y : real) : (term101 y) = term4.
Proof. exact (TRANS (@lem7066217 y) (@lem7066218 y)). Qed.
Lemma lem7066220 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7066221 (y : real) : (term145 y) = term6.
Proof. exact (MK_COMB (@lem7066220) (@lem7066219 y)). Qed.
Lemma lem7066222 (z : real) : (term101 z) = (term102 z).
Proof. exact (@lem1982715 term96 z). Qed.
Lemma lem7066224 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7066225 : term104 = term105.
Proof. exact (@lem7066224 term106). Qed.
Lemma lem7066227 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7066228 : term96 = term109.
Proof. exact (@lem7066227 term106). Qed.
Lemma lem7066229 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7066230 : term110 = term111.
Proof. exact (MK_COMB (@lem7066229) (@lem7066228)). Qed.
Lemma lem7066231 : term112 = term113.
Proof. exact (MK_COMB (@lem7066230) (@lem7066225)). Qed.
Lemma lem7066232 : term114.
Proof. exact (@lem1981473 term96 term104 term104 term104 term4 term104). Qed.
Lemma lem7066234 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066235 : term116 = term117.
Proof. exact (@lem7066234 (NUMERAL 0) term106). Qed.
Lemma lem7066236 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066237 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066238 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066237 h1) (fun h1 : term117 = True => @lem7066236)). Qed.
Lemma lem7066239 : term117 = True.
Proof. exact (EQ_MP (@lem7066238) (@lem7066236)). Qed.
Lemma lem7066240 : term116 = True.
Proof. exact (TRANS (@lem7066235) (@lem7066239)). Qed.
Lemma lem7066241 : True = term116.
Proof. exact (SYM (@lem7066240)). Qed.
Lemma lem7066242 : term116.
Proof. exact (EQ_MP (@lem7066241) (@lem0)). Qed.
Lemma lem7066243 : term119.
Proof. exact (@lem7066232 (@lem7066242)). Qed.
Lemma lem7066245 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066246 : term116 = term117.
Proof. exact (@lem7066245 (NUMERAL 0) term106). Qed.
Lemma lem7066247 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066248 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066249 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066248 h1) (fun h1 : term117 = True => @lem7066247)). Qed.
Lemma lem7066250 : term117 = True.
Proof. exact (EQ_MP (@lem7066249) (@lem7066247)). Qed.
Lemma lem7066251 : term116 = True.
Proof. exact (TRANS (@lem7066246) (@lem7066250)). Qed.
Lemma lem7066252 : True = term116.
Proof. exact (SYM (@lem7066251)). Qed.
Lemma lem7066253 : term116.
Proof. exact (EQ_MP (@lem7066252) (@lem0)). Qed.
Lemma lem7066254 : term120.
Proof. exact (@lem7066243 (@lem7066253)). Qed.
Lemma lem7066256 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066257 : term116 = term117.
Proof. exact (@lem7066256 (NUMERAL 0) term106). Qed.
Lemma lem7066258 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066259 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066260 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066259 h1) (fun h1 : term117 = True => @lem7066258)). Qed.
Lemma lem7066261 : term117 = True.
Proof. exact (EQ_MP (@lem7066260) (@lem7066258)). Qed.
Lemma lem7066262 : term116 = True.
Proof. exact (TRANS (@lem7066257) (@lem7066261)). Qed.
Lemma lem7066263 : True = term116.
Proof. exact (SYM (@lem7066262)). Qed.
Lemma lem7066264 : term116.
Proof. exact (EQ_MP (@lem7066263) (@lem0)). Qed.
Lemma lem7066265 : term121.
Proof. exact (@lem7066254 (@lem7066264)). Qed.
Lemma lem7066267 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7066268 : term124 = term125.
Proof. exact (@lem7066267 term106 term106). Qed.
Lemma lem7066269 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7066270 : term127 = term106.
Proof. exact (EQ_MP (@lem7066269) (@lem940073)). Qed.
Lemma lem7066271 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7066272 : term125 = term104.
Proof. exact (MK_COMB (@lem7066271) (@lem7066270)). Qed.
Lemma lem7066273 : term124 = term104.
Proof. exact (TRANS (@lem7066268) (@lem7066272)). Qed.
Lemma lem7066275 (m : nat) (n : nat) : (term128 m n) = (term129 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7066276 : term130 = term131.
Proof. exact (@lem7066275 term106 term106). Qed.
Lemma lem7066277 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7066278 : term127 = term106.
Proof. exact (EQ_MP (@lem7066277) (@lem940073)). Qed.
Lemma lem7066279 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7066280 : term125 = term104.
Proof. exact (MK_COMB (@lem7066279) (@lem7066278)). Qed.
Lemma lem7066281 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7066282 : term131 = term96.
Proof. exact (MK_COMB (@lem7066281) (@lem7066280)). Qed.
Lemma lem7066283 : term130 = term96.
Proof. exact (TRANS (@lem7066276) (@lem7066282)). Qed.
Lemma lem7066284 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7066285 : term132 = term110.
Proof. exact (MK_COMB (@lem7066284) (@lem7066283)). Qed.
Lemma lem7066286 : term133 = term112.
Proof. exact (MK_COMB (@lem7066285) (@lem7066273)). Qed.
Lemma lem7066288 (m : nat) : (term134 m) = term4.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7066289 : term112 = term4.
Proof. exact (@lem7066288 term106). Qed.
Lemma lem7066290 : term133 = term4.
Proof. exact (TRANS (@lem7066286) (@lem7066289)). Qed.
Lemma lem7066291 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7066292 : term135 = term136.
Proof. exact (MK_COMB (@lem7066291) (@lem7066290)). Qed.
Lemma lem7066293 : term104 = term104.
Proof. exact (eq_refl term104). Qed.
Lemma lem7066294 : term137 = term138.
Proof. exact (MK_COMB (@lem7066292) (@lem7066293)). Qed.
Lemma lem7066296 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7066297 : term138 = term4.
Proof. exact (@lem7066296 term106). Qed.
Lemma lem7066298 : term137 = term4.
Proof. exact (TRANS (@lem7066294) (@lem7066297)). Qed.
Lemma lem7066300 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7066301 : term124 = term125.
Proof. exact (@lem7066300 term106 term106). Qed.
Lemma lem7066302 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7066303 : term127 = term106.
Proof. exact (EQ_MP (@lem7066302) (@lem940073)). Qed.
Lemma lem7066304 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7066305 : term125 = term104.
Proof. exact (MK_COMB (@lem7066304) (@lem7066303)). Qed.
Lemma lem7066306 : term124 = term104.
Proof. exact (TRANS (@lem7066301) (@lem7066305)). Qed.
Lemma lem7066307 : term136 = term136.
Proof. exact (eq_refl term136). Qed.
Lemma lem7066308 : term140 = term138.
Proof. exact (MK_COMB (@lem7066307) (@lem7066306)). Qed.
Lemma lem7066310 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7066311 : term138 = term4.
Proof. exact (@lem7066310 term106). Qed.
Lemma lem7066312 : term140 = term4.
Proof. exact (TRANS (@lem7066308) (@lem7066311)). Qed.
Lemma lem7066313 : term4 = term140.
Proof. exact (SYM (@lem7066312)). Qed.
Lemma lem7066314 : term137 = term140.
Proof. exact (TRANS (@lem7066298) (@lem7066313)). Qed.
Lemma lem7066315 : term113 = term141.
Proof. exact (@lem7066265 (@lem7066314)). Qed.
Lemma lem7066316 : term112 = term141.
Proof. exact (TRANS (@lem7066231) (@lem7066315)). Qed.
Lemma lem7066318 (x : real) : (term142 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7066319 : term141 = term4.
Proof. exact (@lem7066318 term4). Qed.
Lemma lem7066320 : term112 = term4.
Proof. exact (TRANS (@lem7066316) (@lem7066319)). Qed.
Lemma lem7066321 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7066322 : term143 = term136.
Proof. exact (MK_COMB (@lem7066321) (@lem7066320)). Qed.
Lemma lem7066323 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem7066324 (z : real) : (term102 z) = (term144 z).
Proof. exact (MK_COMB (@lem7066322) (@lem7066323 z)). Qed.
Lemma lem7066325 (z : real) : (term101 z) = (term144 z).
Proof. exact (TRANS (@lem7066222 z) (@lem7066324 z)). Qed.
Lemma lem7066326 (z : real) : (term144 z) = term4.
Proof. exact (@lem1982719 z). Qed.
Lemma lem7066327 (z : real) : (term101 z) = term4.
Proof. exact (TRANS (@lem7066325 z) (@lem7066326 z)). Qed.
Lemma lem7066328 (y : real) (z : real) : (term99 y z) = term146.
Proof. exact (MK_COMB (@lem7066221 y) (@lem7066327 z)). Qed.
Lemma lem7066329 (y : real) (z : real) : (term98 y z) = term146.
Proof. exact (TRANS (@lem7066113 y z) (@lem7066328 y z)). Qed.
Lemma lem7066330 : term146 = term4.
Proof. exact (@lem1982721 term4). Qed.
Lemma lem7066331 (y : real) (z : real) : (term98 y z) = term4.
Proof. exact (TRANS (@lem7066329 y z) (@lem7066330)). Qed.
Lemma lem7066332 (x : real) (y : real) (z : real) : (term182 x y z) = term146.
Proof. exact (MK_COMB (@lem7066112 x) (@lem7066331 y z)). Qed.
Lemma lem7066333 (x : real) (y : real) (z : real) : (term181 x y z) = term146.
Proof. exact (TRANS (@lem7066004 x y z) (@lem7066332 x y z)). Qed.
Lemma lem7066334 : term146 = term4.
Proof. exact (@lem1982721 term4). Qed.
Lemma lem7066335 (x : real) (y : real) (z : real) : (term181 x y z) = term4.
Proof. exact (TRANS (@lem7066333 x y z) (@lem7066334)). Qed.
Lemma lem7066336 (x : real) (y : real) (z : real) : (term175 x y z) = term4.
Proof. exact (TRANS (@lem7066003 x y z) (@lem7066335 x y z)). Qed.
Lemma lem7066337 (x : real) (y : real) (z : real) : (term174 x y z) = term4.
Proof. exact (TRANS (@lem7065988 x y z) (@lem7066336 x y z)). Qed.
Lemma lem7066338 (x : real) (y : real) (z : real) : (term173 x y z) = term4.
Proof. exact (TRANS (@lem7065987 x y z) (@lem7066337 x y z)). Qed.
Lemma lem7066339 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7066340 (x : real) (y : real) (z : real) : (term183 x y z) = term148.
Proof. exact (MK_COMB (@lem7066339) (@lem7066338 x y z)). Qed.
Lemma lem7066341 : term148 = term149.
Proof. exact (@lem1982785 term4). Qed.
Lemma lem7066343 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7066344 : term4 = term141.
Proof. exact (@lem7066343 (NUMERAL 0)). Qed.
Lemma lem7066346 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7066347 : term96 = term109.
Proof. exact (@lem7066346 term106). Qed.
Lemma lem7066348 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7066349 : term150 = term151.
Proof. exact (MK_COMB (@lem7066348) (@lem7066347)). Qed.
Lemma lem7066350 : term149 = term152.
Proof. exact (MK_COMB (@lem7066349) (@lem7066344)). Qed.
Lemma lem7066351 : term152 = term153.
Proof. exact (@lem1981613 term96 term4 term104 term104). Qed.
Lemma lem7066353 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7066354 : term124 = term125.
Proof. exact (@lem7066353 term106 term106). Qed.
Lemma lem7066355 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7066356 : term127 = term106.
Proof. exact (EQ_MP (@lem7066355) (@lem940073)). Qed.
Lemma lem7066357 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7066358 : term125 = term104.
Proof. exact (MK_COMB (@lem7066357) (@lem7066356)). Qed.
Lemma lem7066359 : term124 = term104.
Proof. exact (TRANS (@lem7066354) (@lem7066358)). Qed.
Lemma lem7066361 (x : nat) : (term154 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7066362 : term149 = term4.
Proof. exact (@lem7066361 term106). Qed.
Lemma lem7066363 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7066364 : term155 = term156.
Proof. exact (MK_COMB (@lem7066363) (@lem7066362)). Qed.
Lemma lem7066365 : term153 = term141.
Proof. exact (MK_COMB (@lem7066364) (@lem7066359)). Qed.
Lemma lem7066366 : term152 = term141.
Proof. exact (TRANS (@lem7066351) (@lem7066365)). Qed.
Lemma lem7066367 : term149 = term141.
Proof. exact (TRANS (@lem7066350) (@lem7066366)). Qed.
Lemma lem7066369 (x : real) : (term142 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7066370 : term141 = term4.
Proof. exact (@lem7066369 term4). Qed.
Lemma lem7066371 : term149 = term4.
Proof. exact (TRANS (@lem7066367) (@lem7066370)). Qed.
Lemma lem7066372 : term148 = term4.
Proof. exact (TRANS (@lem7066341) (@lem7066371)). Qed.
Lemma lem7066373 (x : real) (y : real) (z : real) : (term184 x y z) = (term184 x y z).
Proof. exact (eq_refl (term184 x y z)). Qed.
Lemma lem7066374 (x : real) (y : real) (z : real) : ((term183 x y z) = term148) = ((term183 x y z) = term4).
Proof. exact (MK_COMB (@lem7066373 x y z) (@lem7066372)). Qed.
Lemma lem7066375 (x : real) (y : real) (z : real) : (term183 x y z) = term4.
Proof. exact (EQ_MP (@lem7066374 x y z) (@lem7066340 x y z)). Qed.
Lemma lem7066376 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7066377 (x : real) (y : real) (z : real) : (term185 x y z) = term159.
Proof. exact (MK_COMB (@lem7066376) (@lem7066375 x y z)). Qed.
Lemma lem7066378 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem7066379 (x : real) (y : real) (z : real) : (term186 x y z) = term161.
Proof. exact (MK_COMB (@lem7066377 x y z) (@lem7066378)). Qed.
Lemma lem7066380 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7066381 (x : real) (y : real) (z : real) : (term187 x y z) = term159.
Proof. exact (MK_COMB (@lem7066380) (@lem7066338 x y z)). Qed.
Lemma lem7066382 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem7066383 (x : real) (y : real) (z : real) : (term188 x y z) = term161.
Proof. exact (MK_COMB (@lem7066381 x y z) (@lem7066382)). Qed.
Lemma lem7066384 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7066385 (x : real) (y : real) (z : real) : (term189 x y z) = term165.
Proof. exact (MK_COMB (@lem7066384) (@lem7066383 x y z)). Qed.
Lemma lem7066386 (x : real) (y : real) (z : real) : (term171 x y z) = term166.
Proof. exact (MK_COMB (@lem7066385 x y z) (@lem7066379 x y z)). Qed.
Lemma lem7066387 (x : real) (y : real) (z : real) : (term47 x y z) = term166.
Proof. exact (TRANS (@lem7065954 x y z) (@lem7066386 x y z)). Qed.
Lemma lem7066388 (x : real) (y : real) : (term49 x y) = term167.
Proof. exact (fun_ext (fun z : real => @lem7066387 x y z)). Qed.
Lemma lem7066389 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7066390 (x : real) (y : real) : (term50 x y) = term168.
Proof. exact (MK_COMB (@lem7066389) (@lem7066388 x y)). Qed.
Lemma lem7066391 (x : real) : (term58 x) = term169.
Proof. exact (fun_ext (fun y : real => @lem7066390 x y)). Qed.
Lemma lem7066392 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7066393 (x : real) : (term59 x) = term170.
Proof. exact (MK_COMB (@lem7066392) (@lem7066391 x)). Qed.
Lemma lem7066394 : term67 = term190.
Proof. exact (fun_ext (fun x : real => @lem7066393 x)). Qed.
Lemma lem7066395 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7066396 : term68 = term191.
Proof. exact (MK_COMB (@lem7066395) (@lem7066394)). Qed.
Lemma lem7066397 (x : real) : (term73 x) = (term192 x).
Proof. exact (@lem1988318 (term8 x) x). Qed.
Lemma lem7066398 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7066405 (x : real) : (term8 x) = x.
Proof. exact (@lem1982721 x). Qed.
Lemma lem7066406 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7066407 (x : real) : (term193 x) = (real_sub x).
Proof. exact (MK_COMB (@lem7066406) (@lem7066405 x)). Qed.
Lemma lem7066408 (x : real) : (term194 x) = (real_sub x x).
Proof. exact (MK_COMB (@lem7066407 x) (@lem7066398 x)). Qed.
Lemma lem7066409 (x : real) : (real_sub x x) = (term101 x).
Proof. exact (@lem1982792 x x). Qed.
Lemma lem7066413 (x : real) : (term101 x) = (term102 x).
Proof. exact (@lem1982715 term96 x). Qed.
Lemma lem7066415 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7066416 : term104 = term105.
Proof. exact (@lem7066415 term106). Qed.
Lemma lem7066418 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7066419 : term96 = term109.
Proof. exact (@lem7066418 term106). Qed.
Lemma lem7066420 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7066421 : term110 = term111.
Proof. exact (MK_COMB (@lem7066420) (@lem7066419)). Qed.
Lemma lem7066422 : term112 = term113.
Proof. exact (MK_COMB (@lem7066421) (@lem7066416)). Qed.
Lemma lem7066423 : term114.
Proof. exact (@lem1981473 term96 term104 term104 term104 term4 term104). Qed.
Lemma lem7066425 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066426 : term116 = term117.
Proof. exact (@lem7066425 (NUMERAL 0) term106). Qed.
Lemma lem7066427 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066428 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066429 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066428 h1) (fun h1 : term117 = True => @lem7066427)). Qed.
Lemma lem7066430 : term117 = True.
Proof. exact (EQ_MP (@lem7066429) (@lem7066427)). Qed.
Lemma lem7066431 : term116 = True.
Proof. exact (TRANS (@lem7066426) (@lem7066430)). Qed.
Lemma lem7066432 : True = term116.
Proof. exact (SYM (@lem7066431)). Qed.
Lemma lem7066433 : term116.
Proof. exact (EQ_MP (@lem7066432) (@lem0)). Qed.
Lemma lem7066434 : term119.
Proof. exact (@lem7066423 (@lem7066433)). Qed.
Lemma lem7066436 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066437 : term116 = term117.
Proof. exact (@lem7066436 (NUMERAL 0) term106). Qed.
Lemma lem7066438 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066439 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066440 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066439 h1) (fun h1 : term117 = True => @lem7066438)). Qed.
Lemma lem7066441 : term117 = True.
Proof. exact (EQ_MP (@lem7066440) (@lem7066438)). Qed.
Lemma lem7066442 : term116 = True.
Proof. exact (TRANS (@lem7066437) (@lem7066441)). Qed.
Lemma lem7066443 : True = term116.
Proof. exact (SYM (@lem7066442)). Qed.
Lemma lem7066444 : term116.
Proof. exact (EQ_MP (@lem7066443) (@lem0)). Qed.
Lemma lem7066445 : term120.
Proof. exact (@lem7066434 (@lem7066444)). Qed.
Lemma lem7066447 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066448 : term116 = term117.
Proof. exact (@lem7066447 (NUMERAL 0) term106). Qed.
Lemma lem7066449 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066450 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066451 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066450 h1) (fun h1 : term117 = True => @lem7066449)). Qed.
Lemma lem7066452 : term117 = True.
Proof. exact (EQ_MP (@lem7066451) (@lem7066449)). Qed.
Lemma lem7066453 : term116 = True.
Proof. exact (TRANS (@lem7066448) (@lem7066452)). Qed.
Lemma lem7066454 : True = term116.
Proof. exact (SYM (@lem7066453)). Qed.
Lemma lem7066455 : term116.
Proof. exact (EQ_MP (@lem7066454) (@lem0)). Qed.
Lemma lem7066456 : term121.
Proof. exact (@lem7066445 (@lem7066455)). Qed.
Lemma lem7066458 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7066459 : term124 = term125.
Proof. exact (@lem7066458 term106 term106). Qed.
Lemma lem7066460 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7066461 : term127 = term106.
Proof. exact (EQ_MP (@lem7066460) (@lem940073)). Qed.
Lemma lem7066462 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7066463 : term125 = term104.
Proof. exact (MK_COMB (@lem7066462) (@lem7066461)). Qed.
Lemma lem7066464 : term124 = term104.
Proof. exact (TRANS (@lem7066459) (@lem7066463)). Qed.
Lemma lem7066466 (m : nat) (n : nat) : (term128 m n) = (term129 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7066467 : term130 = term131.
Proof. exact (@lem7066466 term106 term106). Qed.
Lemma lem7066468 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7066469 : term127 = term106.
Proof. exact (EQ_MP (@lem7066468) (@lem940073)). Qed.
Lemma lem7066470 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7066471 : term125 = term104.
Proof. exact (MK_COMB (@lem7066470) (@lem7066469)). Qed.
Lemma lem7066472 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7066473 : term131 = term96.
Proof. exact (MK_COMB (@lem7066472) (@lem7066471)). Qed.
Lemma lem7066474 : term130 = term96.
Proof. exact (TRANS (@lem7066467) (@lem7066473)). Qed.
Lemma lem7066475 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7066476 : term132 = term110.
Proof. exact (MK_COMB (@lem7066475) (@lem7066474)). Qed.
Lemma lem7066477 : term133 = term112.
Proof. exact (MK_COMB (@lem7066476) (@lem7066464)). Qed.
Lemma lem7066479 (m : nat) : (term134 m) = term4.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7066480 : term112 = term4.
Proof. exact (@lem7066479 term106). Qed.
Lemma lem7066481 : term133 = term4.
Proof. exact (TRANS (@lem7066477) (@lem7066480)). Qed.
Lemma lem7066482 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7066483 : term135 = term136.
Proof. exact (MK_COMB (@lem7066482) (@lem7066481)). Qed.
Lemma lem7066484 : term104 = term104.
Proof. exact (eq_refl term104). Qed.
Lemma lem7066485 : term137 = term138.
Proof. exact (MK_COMB (@lem7066483) (@lem7066484)). Qed.
Lemma lem7066487 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7066488 : term138 = term4.
Proof. exact (@lem7066487 term106). Qed.
Lemma lem7066489 : term137 = term4.
Proof. exact (TRANS (@lem7066485) (@lem7066488)). Qed.
Lemma lem7066491 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7066492 : term124 = term125.
Proof. exact (@lem7066491 term106 term106). Qed.
Lemma lem7066493 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7066494 : term127 = term106.
Proof. exact (EQ_MP (@lem7066493) (@lem940073)). Qed.
Lemma lem7066495 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7066496 : term125 = term104.
Proof. exact (MK_COMB (@lem7066495) (@lem7066494)). Qed.
Lemma lem7066497 : term124 = term104.
Proof. exact (TRANS (@lem7066492) (@lem7066496)). Qed.
Lemma lem7066498 : term136 = term136.
Proof. exact (eq_refl term136). Qed.
Lemma lem7066499 : term140 = term138.
Proof. exact (MK_COMB (@lem7066498) (@lem7066497)). Qed.
Lemma lem7066501 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7066502 : term138 = term4.
Proof. exact (@lem7066501 term106). Qed.
Lemma lem7066503 : term140 = term4.
Proof. exact (TRANS (@lem7066499) (@lem7066502)). Qed.
Lemma lem7066504 : term4 = term140.
Proof. exact (SYM (@lem7066503)). Qed.
Lemma lem7066505 : term137 = term140.
Proof. exact (TRANS (@lem7066489) (@lem7066504)). Qed.
Lemma lem7066506 : term113 = term141.
Proof. exact (@lem7066456 (@lem7066505)). Qed.
Lemma lem7066507 : term112 = term141.
Proof. exact (TRANS (@lem7066422) (@lem7066506)). Qed.
Lemma lem7066509 (x : real) : (term142 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7066510 : term141 = term4.
Proof. exact (@lem7066509 term4). Qed.
Lemma lem7066511 : term112 = term4.
Proof. exact (TRANS (@lem7066507) (@lem7066510)). Qed.
Lemma lem7066512 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7066513 : term143 = term136.
Proof. exact (MK_COMB (@lem7066512) (@lem7066511)). Qed.
Lemma lem7066514 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7066515 (x : real) : (term102 x) = (term144 x).
Proof. exact (MK_COMB (@lem7066513) (@lem7066514 x)). Qed.
Lemma lem7066516 (x : real) : (term101 x) = (term144 x).
Proof. exact (TRANS (@lem7066413 x) (@lem7066515 x)). Qed.
Lemma lem7066517 (x : real) : (term144 x) = term4.
Proof. exact (@lem1982719 x). Qed.
Lemma lem7066519 (x : real) : (term101 x) = term4.
Proof. exact (TRANS (@lem7066516 x) (@lem7066517 x)). Qed.
Lemma lem7066520 (x : real) : (real_sub x x) = term4.
Proof. exact (TRANS (@lem7066409 x) (@lem7066519 x)). Qed.
Lemma lem7066521 (x : real) : (term194 x) = term4.
Proof. exact (TRANS (@lem7066408 x) (@lem7066520 x)). Qed.
Lemma lem7066522 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7066523 (x : real) : (term195 x) = term148.
Proof. exact (MK_COMB (@lem7066522) (@lem7066521 x)). Qed.
Lemma lem7066524 : term148 = term149.
Proof. exact (@lem1982785 term4). Qed.
Lemma lem7066526 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7066527 : term4 = term141.
Proof. exact (@lem7066526 (NUMERAL 0)). Qed.
Lemma lem7066529 (x : nat) : (term107 x) = (term108 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7066530 : term96 = term109.
Proof. exact (@lem7066529 term106). Qed.
Lemma lem7066531 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7066532 : term150 = term151.
Proof. exact (MK_COMB (@lem7066531) (@lem7066530)). Qed.
Lemma lem7066533 : term149 = term152.
Proof. exact (MK_COMB (@lem7066532) (@lem7066527)). Qed.
Lemma lem7066534 : term152 = term153.
Proof. exact (@lem1981613 term96 term4 term104 term104). Qed.
Lemma lem7066536 (m : nat) (n : nat) : (term122 m n) = (term123 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7066537 : term124 = term125.
Proof. exact (@lem7066536 term106 term106). Qed.
Lemma lem7066538 : (term126 = (BIT1 0)) = (term127 = term106).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7066539 : term127 = term106.
Proof. exact (EQ_MP (@lem7066538) (@lem940073)). Qed.
Lemma lem7066540 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7066541 : term125 = term104.
Proof. exact (MK_COMB (@lem7066540) (@lem7066539)). Qed.
Lemma lem7066542 : term124 = term104.
Proof. exact (TRANS (@lem7066537) (@lem7066541)). Qed.
Lemma lem7066544 (x : nat) : (term154 x) = term4.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7066545 : term149 = term4.
Proof. exact (@lem7066544 term106). Qed.
Lemma lem7066546 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7066547 : term155 = term156.
Proof. exact (MK_COMB (@lem7066546) (@lem7066545)). Qed.
Lemma lem7066548 : term153 = term141.
Proof. exact (MK_COMB (@lem7066547) (@lem7066542)). Qed.
Lemma lem7066549 : term152 = term141.
Proof. exact (TRANS (@lem7066534) (@lem7066548)). Qed.
Lemma lem7066550 : term149 = term141.
Proof. exact (TRANS (@lem7066533) (@lem7066549)). Qed.
Lemma lem7066552 (x : real) : (term142 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7066553 : term141 = term4.
Proof. exact (@lem7066552 term4). Qed.
Lemma lem7066554 : term149 = term4.
Proof. exact (TRANS (@lem7066550) (@lem7066553)). Qed.
Lemma lem7066555 : term148 = term4.
Proof. exact (TRANS (@lem7066524) (@lem7066554)). Qed.
Lemma lem7066556 (x : real) : (term196 x) = (term196 x).
Proof. exact (eq_refl (term196 x)). Qed.
Lemma lem7066557 (x : real) : ((term195 x) = term148) = ((term195 x) = term4).
Proof. exact (MK_COMB (@lem7066556 x) (@lem7066555)). Qed.
Lemma lem7066558 (x : real) : (term195 x) = term4.
Proof. exact (EQ_MP (@lem7066557 x) (@lem7066523 x)). Qed.
Lemma lem7066559 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7066560 (x : real) : (term197 x) = term159.
Proof. exact (MK_COMB (@lem7066559) (@lem7066558 x)). Qed.
Lemma lem7066561 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem7066562 (x : real) : (term198 x) = term161.
Proof. exact (MK_COMB (@lem7066560 x) (@lem7066561)). Qed.
Lemma lem7066563 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7066564 (x : real) : (term199 x) = term159.
Proof. exact (MK_COMB (@lem7066563) (@lem7066521 x)). Qed.
Lemma lem7066565 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem7066566 (x : real) : (term200 x) = term161.
Proof. exact (MK_COMB (@lem7066564 x) (@lem7066565)). Qed.
Lemma lem7066567 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7066568 (x : real) : (term201 x) = term165.
Proof. exact (MK_COMB (@lem7066567) (@lem7066566 x)). Qed.
Lemma lem7066569 (x : real) : (term192 x) = term166.
Proof. exact (MK_COMB (@lem7066568 x) (@lem7066562 x)). Qed.
Lemma lem7066570 (x : real) : (term73 x) = term166.
Proof. exact (TRANS (@lem7066397 x) (@lem7066569 x)). Qed.
Lemma lem7066571 : term75 = term167.
Proof. exact (fun_ext (fun x : real => @lem7066570 x)). Qed.
Lemma lem7066572 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7066573 : term76 = term168.
Proof. exact (MK_COMB (@lem7066572) (@lem7066571)). Qed.
Lemma lem7066574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7066575 : term78 = term202.
Proof. exact (MK_COMB (@lem7066574) (@lem7066396)). Qed.
Lemma lem7066576 : term80 = term203.
Proof. exact (MK_COMB (@lem7066575) (@lem7066573)). Qed.
Lemma lem7066577 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7066578 : term84 = term204.
Proof. exact (MK_COMB (@lem7066577) (@lem7065953)). Qed.
Lemma lem7066579 : term86 = term205.
Proof. exact (MK_COMB (@lem7066578) (@lem7066576)). Qed.
Lemma lem7066580 : term87 = term205.
Proof. exact (TRANS (@lem7065648) (@lem7066579)). Qed.
Lemma lem7066582 {A : Type'} (t : Prop) : (term206 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem7066583 (t : Prop) : (term207 t) = t.
Proof. exact (@lem7066582 real t). Qed.
Lemma lem7066584 : term170 = term168.
Proof. exact (@lem7066583 term168). Qed.
Lemma lem7066586 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term208 A P Q) = (term209 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem7066587 (P : real -> Prop) (Q : real -> Prop) : (term210 P Q) = (term211 P Q).
Proof. exact (@lem7066586 real P Q). Qed.
Lemma lem7066588 : term212 = term213.
Proof. exact (@lem7066587 term214 term214). Qed.
Lemma lem7066589 (y : real) : (term215 y) = term161.
Proof. exact (eq_refl (term215 y)). Qed.
Lemma lem7066590 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7066591 (y : real) : (term216 y) = term165.
Proof. exact (MK_COMB (@lem7066590) (@lem7066589 y)). Qed.
Lemma lem7066592 (y : real) : (term215 y) = term161.
Proof. exact (eq_refl (term215 y)). Qed.
Lemma lem7066593 (y : real) : (term217 y) = term166.
Proof. exact (MK_COMB (@lem7066591 y) (@lem7066592 y)). Qed.
Lemma lem7066594 : term218 = term167.
Proof. exact (fun_ext (fun y : real => @lem7066593 y)). Qed.
Lemma lem7066595 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7066596 : term212 = term168.
Proof. exact (MK_COMB (@lem7066595) (@lem7066594)). Qed.
Lemma lem7066597 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7066598 : term219 = term220.
Proof. exact (MK_COMB (@lem7066597) (@lem7066596)). Qed.
Lemma lem7066599 (y : real) : (term215 y) = term161.
Proof. exact (eq_refl (term215 y)). Qed.
Lemma lem7066600 : term221 = term214.
Proof. exact (fun_ext (fun y : real => @lem7066599 y)). Qed.
Lemma lem7066601 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7066602 : term222 = term223.
Proof. exact (MK_COMB (@lem7066601) (@lem7066600)). Qed.
Lemma lem7066603 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7066604 : term224 = term225.
Proof. exact (MK_COMB (@lem7066603) (@lem7066602)). Qed.
Lemma lem7066605 (y : real) : (term215 y) = term161.
Proof. exact (eq_refl (term215 y)). Qed.
Lemma lem7066606 : term221 = term214.
Proof. exact (fun_ext (fun y : real => @lem7066605 y)). Qed.
Lemma lem7066607 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7066608 : term222 = term223.
Proof. exact (MK_COMB (@lem7066607) (@lem7066606)). Qed.
Lemma lem7066609 : term213 = term226.
Proof. exact (MK_COMB (@lem7066604) (@lem7066608)). Qed.
Lemma lem7066610 : (term212 = term213) = (term168 = term226).
Proof. exact (MK_COMB (@lem7066598) (@lem7066609)). Qed.
Lemma lem7066611 : term168 = term226.
Proof. exact (EQ_MP (@lem7066610) (@lem7066588)). Qed.
Lemma lem7066612 : term170 = term226.
Proof. exact (TRANS (@lem7066584) (@lem7066611)). Qed.
Lemma lem7066614 {A : Type'} (t : Prop) : (term206 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem7066615 (t : Prop) : (term207 t) = t.
Proof. exact (@lem7066614 real t). Qed.
Lemma lem7066616 : term223 = term161.
Proof. exact (@lem7066615 term161). Qed.
Lemma lem7066617 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7066618 : term225 = term165.
Proof. exact (MK_COMB (@lem7066617) (@lem7066616)). Qed.
Lemma lem7066620 {A : Type'} (t : Prop) : (term206 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem7066621 (t : Prop) : (term207 t) = t.
Proof. exact (@lem7066620 real t). Qed.
Lemma lem7066622 : term223 = term161.
Proof. exact (@lem7066621 term161). Qed.
Lemma lem7066623 : term226 = term166.
Proof. exact (MK_COMB (@lem7066618) (@lem7066622)). Qed.
Lemma lem7066624 : term170 = term166.
Proof. exact (TRANS (@lem7066612) (@lem7066623)). Qed.
Lemma lem7066625 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7066626 : term204 = term227.
Proof. exact (MK_COMB (@lem7066625) (@lem7066624)). Qed.
Lemma lem7066628 {A : Type'} (t : Prop) : (term206 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem7066629 (t : Prop) : (term207 t) = t.
Proof. exact (@lem7066628 real t). Qed.
Lemma lem7066630 : term191 = term170.
Proof. exact (@lem7066629 term170). Qed.
Lemma lem7066632 {A : Type'} (t : Prop) : (term206 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem7066633 (t : Prop) : (term207 t) = t.
Proof. exact (@lem7066632 real t). Qed.
Lemma lem7066634 : term170 = term168.
Proof. exact (@lem7066633 term168). Qed.
Lemma lem7066636 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term208 A P Q) = (term209 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem7066637 (P : real -> Prop) (Q : real -> Prop) : (term210 P Q) = (term211 P Q).
Proof. exact (@lem7066636 real P Q). Qed.
Lemma lem7066638 : term212 = term213.
Proof. exact (@lem7066637 term214 term214). Qed.
Lemma lem7066639 (z : real) : (term215 z) = term161.
Proof. exact (eq_refl (term215 z)). Qed.
Lemma lem7066640 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7066641 (z : real) : (term216 z) = term165.
Proof. exact (MK_COMB (@lem7066640) (@lem7066639 z)). Qed.
Lemma lem7066642 (z : real) : (term215 z) = term161.
Proof. exact (eq_refl (term215 z)). Qed.
Lemma lem7066643 (z : real) : (term217 z) = term166.
Proof. exact (MK_COMB (@lem7066641 z) (@lem7066642 z)). Qed.
Lemma lem7066644 : term218 = term167.
Proof. exact (fun_ext (fun z : real => @lem7066643 z)). Qed.
Lemma lem7066645 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7066646 : term212 = term168.
Proof. exact (MK_COMB (@lem7066645) (@lem7066644)). Qed.
Lemma lem7066647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7066648 : term219 = term220.
Proof. exact (MK_COMB (@lem7066647) (@lem7066646)). Qed.
Lemma lem7066649 (z : real) : (term215 z) = term161.
Proof. exact (eq_refl (term215 z)). Qed.
Lemma lem7066650 : term221 = term214.
Proof. exact (fun_ext (fun z : real => @lem7066649 z)). Qed.
Lemma lem7066651 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7066652 : term222 = term223.
Proof. exact (MK_COMB (@lem7066651) (@lem7066650)). Qed.
Lemma lem7066653 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7066654 : term224 = term225.
Proof. exact (MK_COMB (@lem7066653) (@lem7066652)). Qed.
Lemma lem7066655 (z : real) : (term215 z) = term161.
Proof. exact (eq_refl (term215 z)). Qed.
Lemma lem7066656 : term221 = term214.
Proof. exact (fun_ext (fun z : real => @lem7066655 z)). Qed.
Lemma lem7066657 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7066658 : term222 = term223.
Proof. exact (MK_COMB (@lem7066657) (@lem7066656)). Qed.
Lemma lem7066659 : term213 = term226.
Proof. exact (MK_COMB (@lem7066654) (@lem7066658)). Qed.
Lemma lem7066660 : (term212 = term213) = (term168 = term226).
Proof. exact (MK_COMB (@lem7066648) (@lem7066659)). Qed.
Lemma lem7066661 : term168 = term226.
Proof. exact (EQ_MP (@lem7066660) (@lem7066638)). Qed.
Lemma lem7066662 : term170 = term226.
Proof. exact (TRANS (@lem7066634) (@lem7066661)). Qed.
Lemma lem7066663 : term191 = term226.
Proof. exact (TRANS (@lem7066630) (@lem7066662)). Qed.
Lemma lem7066665 {A : Type'} (t : Prop) : (term206 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem7066666 (t : Prop) : (term207 t) = t.
Proof. exact (@lem7066665 real t). Qed.
Lemma lem7066667 : term223 = term161.
Proof. exact (@lem7066666 term161). Qed.
Lemma lem7066668 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7066669 : term225 = term165.
Proof. exact (MK_COMB (@lem7066668) (@lem7066667)). Qed.
Lemma lem7066671 {A : Type'} (t : Prop) : (term206 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem7066672 (t : Prop) : (term207 t) = t.
Proof. exact (@lem7066671 real t). Qed.
Lemma lem7066673 : term223 = term161.
Proof. exact (@lem7066672 term161). Qed.
Lemma lem7066674 : term226 = term166.
Proof. exact (MK_COMB (@lem7066669) (@lem7066673)). Qed.
Lemma lem7066675 : term191 = term166.
Proof. exact (TRANS (@lem7066663) (@lem7066674)). Qed.
Lemma lem7066676 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7066677 : term202 = term227.
Proof. exact (MK_COMB (@lem7066676) (@lem7066675)). Qed.
Lemma lem7066679 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term208 A P Q) = (term209 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem7066680 (P : real -> Prop) (Q : real -> Prop) : (term210 P Q) = (term211 P Q).
Proof. exact (@lem7066679 real P Q). Qed.
Lemma lem7066681 : term212 = term213.
Proof. exact (@lem7066680 term214 term214). Qed.
Lemma lem7066682 (x : real) : (term215 x) = term161.
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem7066683 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7066684 (x : real) : (term216 x) = term165.
Proof. exact (MK_COMB (@lem7066683) (@lem7066682 x)). Qed.
Lemma lem7066685 (x : real) : (term215 x) = term161.
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem7066686 (x : real) : (term217 x) = term166.
Proof. exact (MK_COMB (@lem7066684 x) (@lem7066685 x)). Qed.
Lemma lem7066687 : term218 = term167.
Proof. exact (fun_ext (fun x : real => @lem7066686 x)). Qed.
Lemma lem7066688 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7066689 : term212 = term168.
Proof. exact (MK_COMB (@lem7066688) (@lem7066687)). Qed.
Lemma lem7066690 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7066691 : term219 = term220.
Proof. exact (MK_COMB (@lem7066690) (@lem7066689)). Qed.
Lemma lem7066692 (x : real) : (term215 x) = term161.
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem7066693 : term221 = term214.
Proof. exact (fun_ext (fun x : real => @lem7066692 x)). Qed.
Lemma lem7066694 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7066695 : term222 = term223.
Proof. exact (MK_COMB (@lem7066694) (@lem7066693)). Qed.
Lemma lem7066696 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7066697 : term224 = term225.
Proof. exact (MK_COMB (@lem7066696) (@lem7066695)). Qed.
Lemma lem7066698 (x : real) : (term215 x) = term161.
Proof. exact (eq_refl (term215 x)). Qed.
Lemma lem7066699 : term221 = term214.
Proof. exact (fun_ext (fun x : real => @lem7066698 x)). Qed.
Lemma lem7066700 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem7066701 : term222 = term223.
Proof. exact (MK_COMB (@lem7066700) (@lem7066699)). Qed.
Lemma lem7066702 : term213 = term226.
Proof. exact (MK_COMB (@lem7066697) (@lem7066701)). Qed.
Lemma lem7066703 : (term212 = term213) = (term168 = term226).
Proof. exact (MK_COMB (@lem7066691) (@lem7066702)). Qed.
Lemma lem7066704 : term168 = term226.
Proof. exact (EQ_MP (@lem7066703) (@lem7066681)). Qed.
Lemma lem7066706 {A : Type'} (t : Prop) : (term206 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem7066707 (t : Prop) : (term207 t) = t.
Proof. exact (@lem7066706 real t). Qed.
Lemma lem7066708 : term223 = term161.
Proof. exact (@lem7066707 term161). Qed.
Lemma lem7066709 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7066710 : term225 = term165.
Proof. exact (MK_COMB (@lem7066709) (@lem7066708)). Qed.
Lemma lem7066712 {A : Type'} (t : Prop) : (term206 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem7066713 (t : Prop) : (term207 t) = t.
Proof. exact (@lem7066712 real t). Qed.
Lemma lem7066714 : term223 = term161.
Proof. exact (@lem7066713 term161). Qed.
Lemma lem7066715 : term226 = term166.
Proof. exact (MK_COMB (@lem7066710) (@lem7066714)). Qed.
Lemma lem7066716 : term168 = term166.
Proof. exact (TRANS (@lem7066704) (@lem7066715)). Qed.
Lemma lem7066717 : term203 = term228.
Proof. exact (MK_COMB (@lem7066677) (@lem7066716)). Qed.
Lemma lem7066720 : term205 = term229.
Proof. exact (MK_COMB (@lem7066626) (@lem7066717)). Qed.
Lemma lem7066745 : term87 = term229.
Proof. exact (TRANS (@lem7066580) (@lem7066720)). Qed.
Lemma lem7066779 (h1 : term229) : term229.
Proof. exact (h1). Qed.
Lemma lem7066780 (h1 : term166) : term166.
Proof. exact (h1). Qed.
Lemma lem7066781 (h1 : term161) : term161.
Proof. exact (h1). Qed.
Lemma lem7066783 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7066784 : term161 = term230.
Proof. exact (@lem7066783 term4 term4). Qed.
Lemma lem7066786 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7066787 : term4 = term141.
Proof. exact (@lem7066786 (NUMERAL 0)). Qed.
Lemma lem7066789 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7066790 : term4 = term141.
Proof. exact (@lem7066789 (NUMERAL 0)). Qed.
Lemma lem7066791 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7066792 : term231 = term232.
Proof. exact (MK_COMB (@lem7066791) (@lem7066790)). Qed.
Lemma lem7066793 : term230 = term233.
Proof. exact (MK_COMB (@lem7066792) (@lem7066787)). Qed.
Lemma lem7066794 : term234.
Proof. exact (@lem1980255 term4 term104 term4 term104). Qed.
Lemma lem7066796 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066797 : term116 = term117.
Proof. exact (@lem7066796 (NUMERAL 0) term106). Qed.
Lemma lem7066798 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066799 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066800 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066799 h1) (fun h1 : term117 = True => @lem7066798)). Qed.
Lemma lem7066801 : term117 = True.
Proof. exact (EQ_MP (@lem7066800) (@lem7066798)). Qed.
Lemma lem7066802 : term116 = True.
Proof. exact (TRANS (@lem7066797) (@lem7066801)). Qed.
Lemma lem7066803 : True = term116.
Proof. exact (SYM (@lem7066802)). Qed.
Lemma lem7066804 : term116.
Proof. exact (EQ_MP (@lem7066803) (@lem0)). Qed.
Lemma lem7066805 : term235.
Proof. exact (@lem7066794 (@lem7066804)). Qed.
Lemma lem7066807 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066808 : term116 = term117.
Proof. exact (@lem7066807 (NUMERAL 0) term106). Qed.
Lemma lem7066809 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066810 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066811 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066810 h1) (fun h1 : term117 = True => @lem7066809)). Qed.
Lemma lem7066812 : term117 = True.
Proof. exact (EQ_MP (@lem7066811) (@lem7066809)). Qed.
Lemma lem7066813 : term116 = True.
Proof. exact (TRANS (@lem7066808) (@lem7066812)). Qed.
Lemma lem7066814 : True = term116.
Proof. exact (SYM (@lem7066813)). Qed.
Lemma lem7066815 : term116.
Proof. exact (EQ_MP (@lem7066814) (@lem0)). Qed.
Lemma lem7066816 : term233 = term236.
Proof. exact (@lem7066805 (@lem7066815)). Qed.
Lemma lem7066818 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7066819 : term138 = term4.
Proof. exact (@lem7066818 term106). Qed.
Lemma lem7066821 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7066822 : term138 = term4.
Proof. exact (@lem7066821 term106). Qed.
Lemma lem7066823 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7066824 : term237 = term231.
Proof. exact (MK_COMB (@lem7066823) (@lem7066822)). Qed.
Lemma lem7066825 : term236 = term230.
Proof. exact (MK_COMB (@lem7066824) (@lem7066819)). Qed.
Lemma lem7066827 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066828 : term230 = term238.
Proof. exact (@lem7066827 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7066829 : term238 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7066830 : term230 = False.
Proof. exact (TRANS (@lem7066828) (@lem7066829)). Qed.
Lemma lem7066831 : term236 = False.
Proof. exact (TRANS (@lem7066825) (@lem7066830)). Qed.
Lemma lem7066832 : term233 = False.
Proof. exact (TRANS (@lem7066816) (@lem7066831)). Qed.
Lemma lem7066833 : term230 = False.
Proof. exact (TRANS (@lem7066793) (@lem7066832)). Qed.
Lemma lem7066834 : term161 = False.
Proof. exact (TRANS (@lem7066784) (@lem7066833)). Qed.
Lemma lem7066835 (h1 : term161) : False.
Proof. exact (EQ_MP (@lem7066834) (@lem7066781 h1)). Qed.
Lemma lem7066836 (h1 : term161) : term161.
Proof. exact (h1). Qed.
Lemma lem7066838 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7066839 : term161 = term230.
Proof. exact (@lem7066838 term4 term4). Qed.
Lemma lem7066841 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7066842 : term4 = term141.
Proof. exact (@lem7066841 (NUMERAL 0)). Qed.
Lemma lem7066844 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7066845 : term4 = term141.
Proof. exact (@lem7066844 (NUMERAL 0)). Qed.
Lemma lem7066846 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7066847 : term231 = term232.
Proof. exact (MK_COMB (@lem7066846) (@lem7066845)). Qed.
Lemma lem7066848 : term230 = term233.
Proof. exact (MK_COMB (@lem7066847) (@lem7066842)). Qed.
Lemma lem7066849 : term234.
Proof. exact (@lem1980255 term4 term104 term4 term104). Qed.
Lemma lem7066851 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066852 : term116 = term117.
Proof. exact (@lem7066851 (NUMERAL 0) term106). Qed.
Lemma lem7066853 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066854 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066855 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066854 h1) (fun h1 : term117 = True => @lem7066853)). Qed.
Lemma lem7066856 : term117 = True.
Proof. exact (EQ_MP (@lem7066855) (@lem7066853)). Qed.
Lemma lem7066857 : term116 = True.
Proof. exact (TRANS (@lem7066852) (@lem7066856)). Qed.
Lemma lem7066858 : True = term116.
Proof. exact (SYM (@lem7066857)). Qed.
Lemma lem7066859 : term116.
Proof. exact (EQ_MP (@lem7066858) (@lem0)). Qed.
Lemma lem7066860 : term235.
Proof. exact (@lem7066849 (@lem7066859)). Qed.
Lemma lem7066862 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066863 : term116 = term117.
Proof. exact (@lem7066862 (NUMERAL 0) term106). Qed.
Lemma lem7066864 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066865 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066866 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066865 h1) (fun h1 : term117 = True => @lem7066864)). Qed.
Lemma lem7066867 : term117 = True.
Proof. exact (EQ_MP (@lem7066866) (@lem7066864)). Qed.
Lemma lem7066868 : term116 = True.
Proof. exact (TRANS (@lem7066863) (@lem7066867)). Qed.
Lemma lem7066869 : True = term116.
Proof. exact (SYM (@lem7066868)). Qed.
Lemma lem7066870 : term116.
Proof. exact (EQ_MP (@lem7066869) (@lem0)). Qed.
Lemma lem7066871 : term233 = term236.
Proof. exact (@lem7066860 (@lem7066870)). Qed.
Lemma lem7066873 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7066874 : term138 = term4.
Proof. exact (@lem7066873 term106). Qed.
Lemma lem7066876 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7066877 : term138 = term4.
Proof. exact (@lem7066876 term106). Qed.
Lemma lem7066878 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7066879 : term237 = term231.
Proof. exact (MK_COMB (@lem7066878) (@lem7066877)). Qed.
Lemma lem7066880 : term236 = term230.
Proof. exact (MK_COMB (@lem7066879) (@lem7066874)). Qed.
Lemma lem7066882 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066883 : term230 = term238.
Proof. exact (@lem7066882 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7066884 : term238 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7066885 : term230 = False.
Proof. exact (TRANS (@lem7066883) (@lem7066884)). Qed.
Lemma lem7066886 : term236 = False.
Proof. exact (TRANS (@lem7066880) (@lem7066885)). Qed.
Lemma lem7066887 : term233 = False.
Proof. exact (TRANS (@lem7066871) (@lem7066886)). Qed.
Lemma lem7066888 : term230 = False.
Proof. exact (TRANS (@lem7066848) (@lem7066887)). Qed.
Lemma lem7066889 : term161 = False.
Proof. exact (TRANS (@lem7066839) (@lem7066888)). Qed.
Lemma lem7066890 (h1 : term161) : False.
Proof. exact (EQ_MP (@lem7066889) (@lem7066836 h1)). Qed.
Lemma lem7066891 (h1 : term166) : False.
Proof. exact (or_elim (@lem7066780 h1) (fun h0 : term161 => @lem7066835 h0) (fun h0 : term161 => @lem7066890 h0)). Qed.
Lemma lem7066892 (h1 : term228) : term228.
Proof. exact (h1). Qed.
Lemma lem7066893 (h1 : term166) : term166.
Proof. exact (h1). Qed.
Lemma lem7066894 (h1 : term161) : term161.
Proof. exact (h1). Qed.
Lemma lem7066896 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7066897 : term161 = term230.
Proof. exact (@lem7066896 term4 term4). Qed.
Lemma lem7066899 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7066900 : term4 = term141.
Proof. exact (@lem7066899 (NUMERAL 0)). Qed.
Lemma lem7066902 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7066903 : term4 = term141.
Proof. exact (@lem7066902 (NUMERAL 0)). Qed.
Lemma lem7066904 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7066905 : term231 = term232.
Proof. exact (MK_COMB (@lem7066904) (@lem7066903)). Qed.
Lemma lem7066906 : term230 = term233.
Proof. exact (MK_COMB (@lem7066905) (@lem7066900)). Qed.
Lemma lem7066907 : term234.
Proof. exact (@lem1980255 term4 term104 term4 term104). Qed.
Lemma lem7066909 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066910 : term116 = term117.
Proof. exact (@lem7066909 (NUMERAL 0) term106). Qed.
Lemma lem7066911 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066912 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066913 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066912 h1) (fun h1 : term117 = True => @lem7066911)). Qed.
Lemma lem7066914 : term117 = True.
Proof. exact (EQ_MP (@lem7066913) (@lem7066911)). Qed.
Lemma lem7066915 : term116 = True.
Proof. exact (TRANS (@lem7066910) (@lem7066914)). Qed.
Lemma lem7066916 : True = term116.
Proof. exact (SYM (@lem7066915)). Qed.
Lemma lem7066917 : term116.
Proof. exact (EQ_MP (@lem7066916) (@lem0)). Qed.
Lemma lem7066918 : term235.
Proof. exact (@lem7066907 (@lem7066917)). Qed.
Lemma lem7066920 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066921 : term116 = term117.
Proof. exact (@lem7066920 (NUMERAL 0) term106). Qed.
Lemma lem7066922 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066923 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066924 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066923 h1) (fun h1 : term117 = True => @lem7066922)). Qed.
Lemma lem7066925 : term117 = True.
Proof. exact (EQ_MP (@lem7066924) (@lem7066922)). Qed.
Lemma lem7066926 : term116 = True.
Proof. exact (TRANS (@lem7066921) (@lem7066925)). Qed.
Lemma lem7066927 : True = term116.
Proof. exact (SYM (@lem7066926)). Qed.
Lemma lem7066928 : term116.
Proof. exact (EQ_MP (@lem7066927) (@lem0)). Qed.
Lemma lem7066929 : term233 = term236.
Proof. exact (@lem7066918 (@lem7066928)). Qed.
Lemma lem7066931 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7066932 : term138 = term4.
Proof. exact (@lem7066931 term106). Qed.
Lemma lem7066934 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7066935 : term138 = term4.
Proof. exact (@lem7066934 term106). Qed.
Lemma lem7066936 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7066937 : term237 = term231.
Proof. exact (MK_COMB (@lem7066936) (@lem7066935)). Qed.
Lemma lem7066938 : term236 = term230.
Proof. exact (MK_COMB (@lem7066937) (@lem7066932)). Qed.
Lemma lem7066940 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066941 : term230 = term238.
Proof. exact (@lem7066940 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7066942 : term238 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7066943 : term230 = False.
Proof. exact (TRANS (@lem7066941) (@lem7066942)). Qed.
Lemma lem7066944 : term236 = False.
Proof. exact (TRANS (@lem7066938) (@lem7066943)). Qed.
Lemma lem7066945 : term233 = False.
Proof. exact (TRANS (@lem7066929) (@lem7066944)). Qed.
Lemma lem7066946 : term230 = False.
Proof. exact (TRANS (@lem7066906) (@lem7066945)). Qed.
Lemma lem7066947 : term161 = False.
Proof. exact (TRANS (@lem7066897) (@lem7066946)). Qed.
Lemma lem7066948 (h1 : term161) : False.
Proof. exact (EQ_MP (@lem7066947) (@lem7066894 h1)). Qed.
Lemma lem7066949 (h1 : term161) : term161.
Proof. exact (h1). Qed.
Lemma lem7066951 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7066952 : term161 = term230.
Proof. exact (@lem7066951 term4 term4). Qed.
Lemma lem7066954 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7066955 : term4 = term141.
Proof. exact (@lem7066954 (NUMERAL 0)). Qed.
Lemma lem7066957 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7066958 : term4 = term141.
Proof. exact (@lem7066957 (NUMERAL 0)). Qed.
Lemma lem7066959 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7066960 : term231 = term232.
Proof. exact (MK_COMB (@lem7066959) (@lem7066958)). Qed.
Lemma lem7066961 : term230 = term233.
Proof. exact (MK_COMB (@lem7066960) (@lem7066955)). Qed.
Lemma lem7066962 : term234.
Proof. exact (@lem1980255 term4 term104 term4 term104). Qed.
Lemma lem7066964 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066965 : term116 = term117.
Proof. exact (@lem7066964 (NUMERAL 0) term106). Qed.
Lemma lem7066966 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066967 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066968 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066967 h1) (fun h1 : term117 = True => @lem7066966)). Qed.
Lemma lem7066969 : term117 = True.
Proof. exact (EQ_MP (@lem7066968) (@lem7066966)). Qed.
Lemma lem7066970 : term116 = True.
Proof. exact (TRANS (@lem7066965) (@lem7066969)). Qed.
Lemma lem7066971 : True = term116.
Proof. exact (SYM (@lem7066970)). Qed.
Lemma lem7066972 : term116.
Proof. exact (EQ_MP (@lem7066971) (@lem0)). Qed.
Lemma lem7066973 : term235.
Proof. exact (@lem7066962 (@lem7066972)). Qed.
Lemma lem7066975 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066976 : term116 = term117.
Proof. exact (@lem7066975 (NUMERAL 0) term106). Qed.
Lemma lem7066977 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7066978 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7066979 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7066978 h1) (fun h1 : term117 = True => @lem7066977)). Qed.
Lemma lem7066980 : term117 = True.
Proof. exact (EQ_MP (@lem7066979) (@lem7066977)). Qed.
Lemma lem7066981 : term116 = True.
Proof. exact (TRANS (@lem7066976) (@lem7066980)). Qed.
Lemma lem7066982 : True = term116.
Proof. exact (SYM (@lem7066981)). Qed.
Lemma lem7066983 : term116.
Proof. exact (EQ_MP (@lem7066982) (@lem0)). Qed.
Lemma lem7066984 : term233 = term236.
Proof. exact (@lem7066973 (@lem7066983)). Qed.
Lemma lem7066986 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7066987 : term138 = term4.
Proof. exact (@lem7066986 term106). Qed.
Lemma lem7066989 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7066990 : term138 = term4.
Proof. exact (@lem7066989 term106). Qed.
Lemma lem7066991 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7066992 : term237 = term231.
Proof. exact (MK_COMB (@lem7066991) (@lem7066990)). Qed.
Lemma lem7066993 : term236 = term230.
Proof. exact (MK_COMB (@lem7066992) (@lem7066987)). Qed.
Lemma lem7066995 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7066996 : term230 = term238.
Proof. exact (@lem7066995 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7066997 : term238 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7066998 : term230 = False.
Proof. exact (TRANS (@lem7066996) (@lem7066997)). Qed.
Lemma lem7066999 : term236 = False.
Proof. exact (TRANS (@lem7066993) (@lem7066998)). Qed.
Lemma lem7067000 : term233 = False.
Proof. exact (TRANS (@lem7066984) (@lem7066999)). Qed.
Lemma lem7067001 : term230 = False.
Proof. exact (TRANS (@lem7066961) (@lem7067000)). Qed.
Lemma lem7067002 : term161 = False.
Proof. exact (TRANS (@lem7066952) (@lem7067001)). Qed.
Lemma lem7067003 (h1 : term161) : False.
Proof. exact (EQ_MP (@lem7067002) (@lem7066949 h1)). Qed.
Lemma lem7067004 (h1 : term166) : False.
Proof. exact (or_elim (@lem7066893 h1) (fun h0 : term161 => @lem7066948 h0) (fun h0 : term161 => @lem7067003 h0)). Qed.
Lemma lem7067005 (h1 : term166) : term166.
Proof. exact (h1). Qed.
Lemma lem7067006 (h1 : term161) : term161.
Proof. exact (h1). Qed.
Lemma lem7067008 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7067009 : term161 = term230.
Proof. exact (@lem7067008 term4 term4). Qed.
Lemma lem7067011 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7067012 : term4 = term141.
Proof. exact (@lem7067011 (NUMERAL 0)). Qed.
Lemma lem7067014 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7067015 : term4 = term141.
Proof. exact (@lem7067014 (NUMERAL 0)). Qed.
Lemma lem7067016 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7067017 : term231 = term232.
Proof. exact (MK_COMB (@lem7067016) (@lem7067015)). Qed.
Lemma lem7067018 : term230 = term233.
Proof. exact (MK_COMB (@lem7067017) (@lem7067012)). Qed.
Lemma lem7067019 : term234.
Proof. exact (@lem1980255 term4 term104 term4 term104). Qed.
Lemma lem7067021 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7067022 : term116 = term117.
Proof. exact (@lem7067021 (NUMERAL 0) term106). Qed.
Lemma lem7067023 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7067024 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7067025 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7067024 h1) (fun h1 : term117 = True => @lem7067023)). Qed.
Lemma lem7067026 : term117 = True.
Proof. exact (EQ_MP (@lem7067025) (@lem7067023)). Qed.
Lemma lem7067027 : term116 = True.
Proof. exact (TRANS (@lem7067022) (@lem7067026)). Qed.
Lemma lem7067028 : True = term116.
Proof. exact (SYM (@lem7067027)). Qed.
Lemma lem7067029 : term116.
Proof. exact (EQ_MP (@lem7067028) (@lem0)). Qed.
Lemma lem7067030 : term235.
Proof. exact (@lem7067019 (@lem7067029)). Qed.
Lemma lem7067032 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7067033 : term116 = term117.
Proof. exact (@lem7067032 (NUMERAL 0) term106). Qed.
Lemma lem7067034 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7067035 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7067036 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7067035 h1) (fun h1 : term117 = True => @lem7067034)). Qed.
Lemma lem7067037 : term117 = True.
Proof. exact (EQ_MP (@lem7067036) (@lem7067034)). Qed.
Lemma lem7067038 : term116 = True.
Proof. exact (TRANS (@lem7067033) (@lem7067037)). Qed.
Lemma lem7067039 : True = term116.
Proof. exact (SYM (@lem7067038)). Qed.
Lemma lem7067040 : term116.
Proof. exact (EQ_MP (@lem7067039) (@lem0)). Qed.
Lemma lem7067041 : term233 = term236.
Proof. exact (@lem7067030 (@lem7067040)). Qed.
Lemma lem7067043 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7067044 : term138 = term4.
Proof. exact (@lem7067043 term106). Qed.
Lemma lem7067046 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7067047 : term138 = term4.
Proof. exact (@lem7067046 term106). Qed.
Lemma lem7067048 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7067049 : term237 = term231.
Proof. exact (MK_COMB (@lem7067048) (@lem7067047)). Qed.
Lemma lem7067050 : term236 = term230.
Proof. exact (MK_COMB (@lem7067049) (@lem7067044)). Qed.
Lemma lem7067052 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7067053 : term230 = term238.
Proof. exact (@lem7067052 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7067054 : term238 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7067055 : term230 = False.
Proof. exact (TRANS (@lem7067053) (@lem7067054)). Qed.
Lemma lem7067056 : term236 = False.
Proof. exact (TRANS (@lem7067050) (@lem7067055)). Qed.
Lemma lem7067057 : term233 = False.
Proof. exact (TRANS (@lem7067041) (@lem7067056)). Qed.
Lemma lem7067058 : term230 = False.
Proof. exact (TRANS (@lem7067018) (@lem7067057)). Qed.
Lemma lem7067059 : term161 = False.
Proof. exact (TRANS (@lem7067009) (@lem7067058)). Qed.
Lemma lem7067060 (h1 : term161) : False.
Proof. exact (EQ_MP (@lem7067059) (@lem7067006 h1)). Qed.
Lemma lem7067061 (h1 : term161) : term161.
Proof. exact (h1). Qed.
Lemma lem7067063 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7067064 : term161 = term230.
Proof. exact (@lem7067063 term4 term4). Qed.
Lemma lem7067066 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7067067 : term4 = term141.
Proof. exact (@lem7067066 (NUMERAL 0)). Qed.
Lemma lem7067069 (x : nat) : (real_of_num x) = (term103 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7067070 : term4 = term141.
Proof. exact (@lem7067069 (NUMERAL 0)). Qed.
Lemma lem7067071 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7067072 : term231 = term232.
Proof. exact (MK_COMB (@lem7067071) (@lem7067070)). Qed.
Lemma lem7067073 : term230 = term233.
Proof. exact (MK_COMB (@lem7067072) (@lem7067067)). Qed.
Lemma lem7067074 : term234.
Proof. exact (@lem1980255 term4 term104 term4 term104). Qed.
Lemma lem7067076 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7067077 : term116 = term117.
Proof. exact (@lem7067076 (NUMERAL 0) term106). Qed.
Lemma lem7067078 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7067079 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7067080 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7067079 h1) (fun h1 : term117 = True => @lem7067078)). Qed.
Lemma lem7067081 : term117 = True.
Proof. exact (EQ_MP (@lem7067080) (@lem7067078)). Qed.
Lemma lem7067082 : term116 = True.
Proof. exact (TRANS (@lem7067077) (@lem7067081)). Qed.
Lemma lem7067083 : True = term116.
Proof. exact (SYM (@lem7067082)). Qed.
Lemma lem7067084 : term116.
Proof. exact (EQ_MP (@lem7067083) (@lem0)). Qed.
Lemma lem7067085 : term235.
Proof. exact (@lem7067074 (@lem7067084)). Qed.
Lemma lem7067087 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7067088 : term116 = term117.
Proof. exact (@lem7067087 (NUMERAL 0) term106). Qed.
Lemma lem7067089 : term118 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7067090 (h1 : term118 = (BIT1 0)) : term117 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7067091 : (term118 = (BIT1 0)) = (term117 = True).
Proof. exact (prop_ext (fun h1 : term118 = (BIT1 0) => @lem7067090 h1) (fun h1 : term117 = True => @lem7067089)). Qed.
Lemma lem7067092 : term117 = True.
Proof. exact (EQ_MP (@lem7067091) (@lem7067089)). Qed.
Lemma lem7067093 : term116 = True.
Proof. exact (TRANS (@lem7067088) (@lem7067092)). Qed.
Lemma lem7067094 : True = term116.
Proof. exact (SYM (@lem7067093)). Qed.
Lemma lem7067095 : term116.
Proof. exact (EQ_MP (@lem7067094) (@lem0)). Qed.
Lemma lem7067096 : term233 = term236.
Proof. exact (@lem7067085 (@lem7067095)). Qed.
Lemma lem7067098 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7067099 : term138 = term4.
Proof. exact (@lem7067098 term106). Qed.
Lemma lem7067101 (x : nat) : (term139 x) = term4.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7067102 : term138 = term4.
Proof. exact (@lem7067101 term106). Qed.
Lemma lem7067103 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7067104 : term237 = term231.
Proof. exact (MK_COMB (@lem7067103) (@lem7067102)). Qed.
Lemma lem7067105 : term236 = term230.
Proof. exact (MK_COMB (@lem7067104) (@lem7067099)). Qed.
Lemma lem7067107 (m : nat) (n : nat) : (term115 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7067108 : term230 = term238.
Proof. exact (@lem7067107 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem7067109 : term238 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem7067110 : term230 = False.
Proof. exact (TRANS (@lem7067108) (@lem7067109)). Qed.
Lemma lem7067111 : term236 = False.
Proof. exact (TRANS (@lem7067105) (@lem7067110)). Qed.
Lemma lem7067112 : term233 = False.
Proof. exact (TRANS (@lem7067096) (@lem7067111)). Qed.
Lemma lem7067113 : term230 = False.
Proof. exact (TRANS (@lem7067073) (@lem7067112)). Qed.
Lemma lem7067114 : term161 = False.
Proof. exact (TRANS (@lem7067064) (@lem7067113)). Qed.
Lemma lem7067115 (h1 : term161) : False.
Proof. exact (EQ_MP (@lem7067114) (@lem7067061 h1)). Qed.
Lemma lem7067116 (h1 : term166) : False.
Proof. exact (or_elim (@lem7067005 h1) (fun h0 : term161 => @lem7067060 h0) (fun h0 : term161 => @lem7067115 h0)). Qed.
Lemma lem7067117 (h1 : term228) : False.
Proof. exact (or_elim (@lem7066892 h1) (fun h0 : term166 => @lem7067004 h0) (fun h0 : term166 => @lem7067116 h0)). Qed.
Lemma lem7067118 (h1 : term229) : False.
Proof. exact (or_elim (@lem7066779 h1) (fun h0 : term166 => @lem7066891 h0) (fun h0 : term228 => @lem7067117 h0)). Qed.
Lemma lem7067120 (h1 : term229) : term229.
Proof. exact (h1). Qed.
Lemma lem7067121 (h1 : term229) : term229 = False.
Proof. exact (prop_ext (fun h2 : term229 => @lem7067118 h1) (fun h2 : False => @lem7067120 h1)). Qed.
Lemma lem7067122 (h1 : term229) : False.
Proof. exact (EQ_MP (@lem7067121 h1) (@lem7067120 h1)). Qed.
Lemma lem7067123 (h1 : term87) : term87.
Proof. exact (h1). Qed.
Lemma lem7067124 (h1 : term87) : term229.
Proof. exact (EQ_MP (@lem7066745) (@lem7067123 h1)). Qed.
Lemma lem7067125 (h1 : term87) : term229 = False.
Proof. exact (prop_ext (fun h2 : term229 => @lem7067122 h2) (fun h2 : False => @lem7067124 h1)). Qed.
Lemma lem7067126 (h1 : term87) : False.
Proof. exact (EQ_MP (@lem7067125 h1) (@lem7067124 h1)). Qed.
Lemma lem7067127 : term239.
Proof. exact (fun h0 : term87 => @lem7067126 h0). Qed.
Lemma lem7067128 : term240.
Proof. exact (@lem1386578 term19). Qed.
Lemma lem7067131 : term19.
Proof. exact (@lem7067128 (@lem7067127)). Qed.
Lemma lem7067132 : @monoidal real real_add.
Proof. exact (EQ_MP (@lem7065508) (@lem7067131)). Qed.
