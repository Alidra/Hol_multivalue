Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MIN_term_abbrevs.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm12653_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm1482699_spec.
Require Import thm1483429_spec.
Require Import thm16451_spec.
Require Import thm16452_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm19158_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982757_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988289_spec.
Require Import thm1988291_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm1988348_spec.
Require Import thm20234_spec.
Require Import thm20420_spec.
Require Import thm20421_spec.
Require Import thm2318495_spec.
Require Import thm2318497_spec.
Require Import thm2318505_spec.
Require Import thm2318506_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem2323497 : term0 = term1.
Proof. exact (@lem2318604 term1). Qed.
Lemma lem2323512 (P : int -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2323513 (x : int) : (term4 x) = (term5 x).
Proof. exact (@lem2323512 (term6 x)). Qed.
Lemma lem2323514 (x : int) (y : int) : (term7 x y) = ((int_min x y) = (term8 x y)).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem2323515 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2323517 (x : int) (y : int) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem2323515) (@lem2323514 x y)). Qed.
Lemma lem2323518 (x : int) : (term11 x) = (term12 x).
Proof. exact (fun_ext (fun y : int => @lem2323517 x y)). Qed.
Lemma lem2323519 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2323520 (x : int) : (term5 x) = (term13 x).
Proof. exact (MK_COMB (@lem2323519) (@lem2323518 x)). Qed.
Lemma lem2323521 (x : int) : (term4 x) = (term13 x).
Proof. exact (TRANS (@lem2323513 x) (@lem2323520 x)). Qed.
Lemma lem2323522 (P : int -> Prop) : (term2 P) = (term3 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2323523 : term14 = term15.
Proof. exact (@lem2323522 term16). Qed.
Lemma lem2323524 (x : int) : (term17 x) = (term18 x).
Proof. exact (eq_refl (term17 x)). Qed.
Lemma lem2323525 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2323526 (x : int) : (term19 x) = (term4 x).
Proof. exact (MK_COMB (@lem2323525) (@lem2323524 x)). Qed.
Lemma lem2323527 (x : int) : (term19 x) = (term13 x).
Proof. exact (TRANS (@lem2323526 x) (@lem2323521 x)). Qed.
Lemma lem2323528 : term20 = term21.
Proof. exact (fun_ext (fun x : int => @lem2323527 x)). Qed.
Lemma lem2323529 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2323530 : term15 = term22.
Proof. exact (MK_COMB (@lem2323529) (@lem2323528)). Qed.
Lemma lem2323532 : term14 = term22.
Proof. exact (TRANS (@lem2323523) (@lem2323530)). Qed.
Lemma lem2323536 (x : int) (y : int) (h1 : (int_le x y) = False) : (int_le x y) = False.
Proof. exact (h1). Qed.
Lemma lem2323537 : (@COND int) = (@COND int).
Proof. exact (eq_refl (@COND int)). Qed.
Lemma lem2323538 (x : int) (y : int) (h1 : (int_le x y) = False) : (term23 x y) = (@COND int False).
Proof. exact (MK_COMB (@lem2323537) (@lem2323536 x y h1)). Qed.
Lemma lem2323539 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2323540 (x : int) (y : int) (h1 : (int_le x y) = False) : (term24 y x) = (@COND int False x).
Proof. exact (MK_COMB (@lem2323538 x y h1) (@lem2323539 x)). Qed.
Lemma lem2323541 (y : int) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem2323542 (x : int) (y : int) (h1 : (int_le x y) = False) : (term8 x y) = (@COND int False x y).
Proof. exact (MK_COMB (@lem2323540 x y h1) (@lem2323541 y)). Qed.
Lemma lem2323544 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem2323545 (t1 : int) (t2 : int) : (@COND int False t1 t2) = t2.
Proof. exact (@lem2323544 int t1 t2). Qed.
Lemma lem2323546 (x : int) (y : int) : (@COND int False x y) = y.
Proof. exact (@lem2323545 x y). Qed.
Lemma lem2323547 (x : int) (y : int) (h1 : (int_le x y) = False) : (term8 x y) = y.
Proof. exact (TRANS (@lem2323542 x y h1) (@lem2323546 x y)). Qed.
Lemma lem2323548 (x : int) (y : int) : (term25 x y) = (term25 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem2323549 (x : int) (y : int) (h1 : (int_le x y) = False) : ((int_min x y) = (term8 x y)) = ((int_min x y) = y).
Proof. exact (MK_COMB (@lem2323548 x y) (@lem2323547 x y h1)). Qed.
Lemma lem2323552 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2323553 (x : int) (y : int) (h1 : (int_le x y) = False) : (term10 x y) = (term26 x y).
Proof. exact (MK_COMB (@lem2323552) (@lem2323549 x y h1)). Qed.
Lemma lem2323554 (x : int) (y : int) : term27 x y.
Proof. exact (fun h0 : (int_le x y) = False => @lem2323553 x y h0). Qed.
Lemma lem2323556 (x : int) (y : int) (h1 : (int_le x y) = True) : (int_le x y) = True.
Proof. exact (h1). Qed.
Lemma lem2323557 : (@COND int) = (@COND int).
Proof. exact (eq_refl (@COND int)). Qed.
Lemma lem2323558 (x : int) (y : int) (h1 : (int_le x y) = True) : (term23 x y) = (@COND int True).
Proof. exact (MK_COMB (@lem2323557) (@lem2323556 x y h1)). Qed.
Lemma lem2323559 (x : int) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem2323560 (x : int) (y : int) (h1 : (int_le x y) = True) : (term24 y x) = (@COND int True x).
Proof. exact (MK_COMB (@lem2323558 x y h1) (@lem2323559 x)). Qed.
Lemma lem2323561 (y : int) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem2323562 (x : int) (y : int) (h1 : (int_le x y) = True) : (term8 x y) = (@COND int True x y).
Proof. exact (MK_COMB (@lem2323560 x y h1) (@lem2323561 y)). Qed.
Lemma lem2323564 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem2323565 (t2 : int) (t1 : int) : (@COND int True t1 t2) = t1.
Proof. exact (@lem2323564 int t2 t1). Qed.
Lemma lem2323566 (y : int) (x : int) : (@COND int True x y) = x.
Proof. exact (@lem2323565 y x). Qed.
Lemma lem2323567 (x : int) (y : int) (h1 : (int_le x y) = True) : (term8 x y) = x.
Proof. exact (TRANS (@lem2323562 x y h1) (@lem2323566 y x)). Qed.
Lemma lem2323568 (x : int) (y : int) : (term25 x y) = (term25 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem2323569 (x : int) (y : int) (h1 : (int_le x y) = True) : ((int_min x y) = (term8 x y)) = ((int_min x y) = x).
Proof. exact (MK_COMB (@lem2323568 x y) (@lem2323567 x y h1)). Qed.
Lemma lem2323572 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2323573 (x : int) (y : int) (h1 : (int_le x y) = True) : (term10 x y) = (term28 y x).
Proof. exact (MK_COMB (@lem2323572) (@lem2323569 x y h1)). Qed.
Lemma lem2323574 (y : int) (x : int) : term29 y x.
Proof. exact (fun h0 : (int_le x y) = True => @lem2323573 x y h0). Qed.
Lemma lem2323575 (y : int) (x : int) : term30 y x.
Proof. exact (conj (@lem2323554 x y) (@lem2323574 y x)). Qed.
Lemma lem2323577 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term31 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem2323578 (x : int) (y : int) : term32 x y.
Proof. exact (@lem2323577 (term10 x y) (term28 y x) (int_le x y) (term26 x y)). Qed.
Lemma lem2323615 (x : int) (y : int) : (term10 x y) = (term33 x y).
Proof. exact (@lem2323578 x y (@lem2323575 y x)). Qed.
Lemma lem2323616 (x : int) : (term12 x) = (term34 x).
Proof. exact (fun_ext (fun y : int => @lem2323615 x y)). Qed.
Lemma lem2323617 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2323618 (x : int) : (term13 x) = (term35 x).
Proof. exact (MK_COMB (@lem2323617) (@lem2323616 x)). Qed.
Lemma lem2323619 : term21 = term36.
Proof. exact (fun_ext (fun x : int => @lem2323618 x)). Qed.
Lemma lem2323620 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2323621 : term22 = term37.
Proof. exact (MK_COMB (@lem2323620) (@lem2323619)). Qed.
Lemma lem2323622 : term14 = term37.
Proof. exact (TRANS (@lem2323532) (@lem2323621)). Qed.
Lemma lem2323626 (x : int) (y : int) : (int_le x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2323628 (y : int) (x : int) : (term39 x y) = (term40 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2323629 (x : int) (y : int) : (term28 y x) = (term41 x y).
Proof. exact (@lem2323628 x (int_min x y)). Qed.
Lemma lem2323631 (x : int) (y : int) : (int_le x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2323632 (y : int) (x : int) : (term42 y x) = (term43 y x).
Proof. exact (@lem2323631 (term44 x y) x). Qed.
Lemma lem2323634 (x : int) (y : int) : (term45 x y) = (term46 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2323635 (x : int) (y : int) : (term47 x y) = (term48 x y).
Proof. exact (@lem2323634 (int_min x y) term49). Qed.
Lemma lem2323637 (x : int) (y : int) : (term50 x y) = (term51 x y).
Proof. exact (EQ_MP (@lem2318506 x y) (@lem2318505 x y)). Qed.
Lemma lem2323638 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2323639 (x : int) (y : int) : (term52 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem2323638) (@lem2323637 x y)). Qed.
Lemma lem2323641 (n : nat) : (term54 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2323642 : term55 = term56.
Proof. exact (@lem2323641 term57). Qed.
Lemma lem2323643 (x : int) (y : int) : (term48 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem2323639 x y) (@lem2323642)). Qed.
Lemma lem2323644 (x : int) (y : int) : (term47 x y) = (term58 x y).
Proof. exact (TRANS (@lem2323635 x y) (@lem2323643 x y)). Qed.
Lemma lem2323645 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2323646 (x : int) (y : int) : (term59 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem2323645) (@lem2323644 x y)). Qed.
Lemma lem2323647 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2323648 (y : int) (x : int) : (term43 y x) = (term61 y x).
Proof. exact (MK_COMB (@lem2323646 x y) (@lem2323647 x)). Qed.
Lemma lem2323649 (y : int) (x : int) : (term42 y x) = (term61 y x).
Proof. exact (TRANS (@lem2323632 y x) (@lem2323648 y x)). Qed.
Lemma lem2323650 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2323651 (y : int) (x : int) : (term62 y x) = (term63 y x).
Proof. exact (MK_COMB (@lem2323650) (@lem2323649 y x)). Qed.
Lemma lem2323653 (x : int) (y : int) : (int_le x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2323654 (x : int) (y : int) : (term64 x y) = (term65 x y).
Proof. exact (@lem2323653 (term66 x) (int_min x y)). Qed.
Lemma lem2323656 (x : int) (y : int) : (term45 x y) = (term46 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2323657 (x : int) : (term67 x) = (term68 x).
Proof. exact (@lem2323656 x term49). Qed.
Lemma lem2323659 (n : nat) : (term54 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2323660 : term55 = term56.
Proof. exact (@lem2323659 term57). Qed.
Lemma lem2323661 (x : int) : (term69 x) = (term69 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem2323662 (x : int) : (term68 x) = (term70 x).
Proof. exact (MK_COMB (@lem2323661 x) (@lem2323660)). Qed.
Lemma lem2323663 (x : int) : (term67 x) = (term70 x).
Proof. exact (TRANS (@lem2323657 x) (@lem2323662 x)). Qed.
Lemma lem2323664 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2323665 (x : int) : (term71 x) = (term72 x).
Proof. exact (MK_COMB (@lem2323664) (@lem2323663 x)). Qed.
Lemma lem2323667 (x : int) (y : int) : (term50 x y) = (term51 x y).
Proof. exact (EQ_MP (@lem2318506 x y) (@lem2318505 x y)). Qed.
Lemma lem2323668 (x : int) (y : int) : (term65 x y) = (term73 x y).
Proof. exact (MK_COMB (@lem2323665 x) (@lem2323667 x y)). Qed.
Lemma lem2323669 (x : int) (y : int) : (term64 x y) = (term73 x y).
Proof. exact (TRANS (@lem2323654 x y) (@lem2323668 x y)). Qed.
Lemma lem2323670 (x : int) (y : int) : (term41 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem2323651 y x) (@lem2323669 x y)). Qed.
Lemma lem2323671 (x : int) (y : int) : (term28 y x) = (term74 x y).
Proof. exact (TRANS (@lem2323629 x y) (@lem2323670 x y)). Qed.
Lemma lem2323672 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2323673 (x : int) (y : int) : (term75 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem2323672) (@lem2323626 x y)). Qed.
Lemma lem2323674 (x : int) (y : int) : (term77 y x) = (term78 x y).
Proof. exact (MK_COMB (@lem2323673 x y) (@lem2323671 x y)). Qed.
Lemma lem2323676 (y : int) (x : int) : (term79 x y) = (term80 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2323678 (x : int) (y : int) : (int_le x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2323679 (y : int) (x : int) : (term80 y x) = (term81 y x).
Proof. exact (@lem2323678 (term66 y) x). Qed.
Lemma lem2323681 (x : int) (y : int) : (term45 x y) = (term46 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2323682 (y : int) : (term67 y) = (term68 y).
Proof. exact (@lem2323681 y term49). Qed.
Lemma lem2323684 (n : nat) : (term54 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2323685 : term55 = term56.
Proof. exact (@lem2323684 term57). Qed.
Lemma lem2323686 (y : int) : (term69 y) = (term69 y).
Proof. exact (eq_refl (term69 y)). Qed.
Lemma lem2323687 (y : int) : (term68 y) = (term70 y).
Proof. exact (MK_COMB (@lem2323686 y) (@lem2323685)). Qed.
Lemma lem2323688 (y : int) : (term67 y) = (term70 y).
Proof. exact (TRANS (@lem2323682 y) (@lem2323687 y)). Qed.
Lemma lem2323689 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2323690 (y : int) : (term71 y) = (term72 y).
Proof. exact (MK_COMB (@lem2323689) (@lem2323688 y)). Qed.
Lemma lem2323691 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2323692 (y : int) (x : int) : (term81 y x) = (term82 y x).
Proof. exact (MK_COMB (@lem2323690 y) (@lem2323691 x)). Qed.
Lemma lem2323693 (y : int) (x : int) : (term80 y x) = (term82 y x).
Proof. exact (TRANS (@lem2323679 y x) (@lem2323692 y x)). Qed.
Lemma lem2323694 (y : int) (x : int) : (term79 x y) = (term82 y x).
Proof. exact (TRANS (@lem2323676 y x) (@lem2323693 y x)). Qed.
Lemma lem2323696 (y : int) (x : int) : (term39 x y) = (term40 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2323697 (x : int) (y : int) : (term26 x y) = (term83 x y).
Proof. exact (@lem2323696 y (int_min x y)). Qed.
Lemma lem2323699 (x : int) (y : int) : (int_le x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2323700 (x : int) (y : int) : (term84 x y) = (term85 x y).
Proof. exact (@lem2323699 (term44 x y) y). Qed.
Lemma lem2323702 (x : int) (y : int) : (term45 x y) = (term46 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2323703 (x : int) (y : int) : (term47 x y) = (term48 x y).
Proof. exact (@lem2323702 (int_min x y) term49). Qed.
Lemma lem2323705 (x : int) (y : int) : (term50 x y) = (term51 x y).
Proof. exact (EQ_MP (@lem2318506 x y) (@lem2318505 x y)). Qed.
Lemma lem2323706 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2323707 (x : int) (y : int) : (term52 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem2323706) (@lem2323705 x y)). Qed.
Lemma lem2323709 (n : nat) : (term54 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2323710 : term55 = term56.
Proof. exact (@lem2323709 term57). Qed.
Lemma lem2323711 (x : int) (y : int) : (term48 x y) = (term58 x y).
Proof. exact (MK_COMB (@lem2323707 x y) (@lem2323710)). Qed.
Lemma lem2323712 (x : int) (y : int) : (term47 x y) = (term58 x y).
Proof. exact (TRANS (@lem2323703 x y) (@lem2323711 x y)). Qed.
Lemma lem2323713 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2323714 (x : int) (y : int) : (term59 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem2323713) (@lem2323712 x y)). Qed.
Lemma lem2323715 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2323716 (x : int) (y : int) : (term85 x y) = (term86 x y).
Proof. exact (MK_COMB (@lem2323714 x y) (@lem2323715 y)). Qed.
Lemma lem2323717 (x : int) (y : int) : (term84 x y) = (term86 x y).
Proof. exact (TRANS (@lem2323700 x y) (@lem2323716 x y)). Qed.
Lemma lem2323718 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2323719 (x : int) (y : int) : (term87 x y) = (term88 x y).
Proof. exact (MK_COMB (@lem2323718) (@lem2323717 x y)). Qed.
Lemma lem2323721 (x : int) (y : int) : (int_le x y) = (term38 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2323722 (x : int) (y : int) : (term89 x y) = (term90 x y).
Proof. exact (@lem2323721 (term66 y) (int_min x y)). Qed.
Lemma lem2323724 (x : int) (y : int) : (term45 x y) = (term46 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2323725 (y : int) : (term67 y) = (term68 y).
Proof. exact (@lem2323724 y term49). Qed.
Lemma lem2323727 (n : nat) : (term54 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2323728 : term55 = term56.
Proof. exact (@lem2323727 term57). Qed.
Lemma lem2323729 (y : int) : (term69 y) = (term69 y).
Proof. exact (eq_refl (term69 y)). Qed.
Lemma lem2323730 (y : int) : (term68 y) = (term70 y).
Proof. exact (MK_COMB (@lem2323729 y) (@lem2323728)). Qed.
Lemma lem2323731 (y : int) : (term67 y) = (term70 y).
Proof. exact (TRANS (@lem2323725 y) (@lem2323730 y)). Qed.
Lemma lem2323732 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2323733 (y : int) : (term71 y) = (term72 y).
Proof. exact (MK_COMB (@lem2323732) (@lem2323731 y)). Qed.
Lemma lem2323735 (x : int) (y : int) : (term50 x y) = (term51 x y).
Proof. exact (EQ_MP (@lem2318506 x y) (@lem2318505 x y)). Qed.
Lemma lem2323736 (x : int) (y : int) : (term90 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem2323733 y) (@lem2323735 x y)). Qed.
Lemma lem2323737 (x : int) (y : int) : (term89 x y) = (term91 x y).
Proof. exact (TRANS (@lem2323722 x y) (@lem2323736 x y)). Qed.
Lemma lem2323738 (x : int) (y : int) : (term83 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem2323719 x y) (@lem2323737 x y)). Qed.
Lemma lem2323739 (x : int) (y : int) : (term26 x y) = (term92 x y).
Proof. exact (TRANS (@lem2323697 x y) (@lem2323738 x y)). Qed.
Lemma lem2323740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2323741 (y : int) (x : int) : (term93 x y) = (term94 y x).
Proof. exact (MK_COMB (@lem2323740) (@lem2323694 y x)). Qed.
Lemma lem2323742 (x : int) (y : int) : (term95 x y) = (term96 x y).
Proof. exact (MK_COMB (@lem2323741 y x) (@lem2323739 x y)). Qed.
Lemma lem2323743 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2323744 (x : int) (y : int) : (term97 y x) = (term98 x y).
Proof. exact (MK_COMB (@lem2323743) (@lem2323674 x y)). Qed.
Lemma lem2323745 (x : int) (y : int) : (term33 x y) = (term99 x y).
Proof. exact (MK_COMB (@lem2323744 x y) (@lem2323742 x y)). Qed.
Lemma lem2323746 (x : int) : (term34 x) = (term100 x).
Proof. exact (fun_ext (fun y : int => @lem2323745 x y)). Qed.
Lemma lem2323747 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2323748 (x : int) : (term35 x) = (term101 x).
Proof. exact (MK_COMB (@lem2323747) (@lem2323746 x)). Qed.
Lemma lem2323749 : term36 = term102.
Proof. exact (fun_ext (fun x : int => @lem2323748 x)). Qed.
Lemma lem2323750 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2323751 : term37 = term103.
Proof. exact (MK_COMB (@lem2323750) (@lem2323749)). Qed.
Lemma lem2323752 : term14 = term103.
Proof. exact (TRANS (@lem2323622) (@lem2323751)). Qed.
Lemma lem2323756 (t : Prop) : (term104 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2323757 : term105 = term103.
Proof. exact (@lem2323756 term103). Qed.
Lemma lem2323763 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2323764 (P : int -> Prop) (Q : int -> Prop) : (term108 P Q) = (term109 P Q).
Proof. exact (@lem2323763 int P Q). Qed.
Lemma lem2323765 (x : int) : (term110 x) = (term111 x).
Proof. exact (@lem2323764 (term112 x) (term113 x)). Qed.
Lemma lem2323766 (x : int) (y : int) : (term114 x y) = (term78 x y).
Proof. exact (eq_refl (term114 x y)). Qed.
Lemma lem2323767 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2323768 (x : int) (y : int) : (term115 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem2323767) (@lem2323766 x y)). Qed.
Lemma lem2323769 (x : int) (y : int) : (term116 x y) = (term96 x y).
Proof. exact (eq_refl (term116 x y)). Qed.
Lemma lem2323770 (x : int) (y : int) : (term117 x y) = (term99 x y).
Proof. exact (MK_COMB (@lem2323768 x y) (@lem2323769 x y)). Qed.
Lemma lem2323771 (x : int) : (term118 x) = (term100 x).
Proof. exact (fun_ext (fun y : int => @lem2323770 x y)). Qed.
Lemma lem2323772 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2323773 (x : int) : (term110 x) = (term101 x).
Proof. exact (MK_COMB (@lem2323772) (@lem2323771 x)). Qed.
Lemma lem2323774 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2323775 (x : int) : (term119 x) = (term120 x).
Proof. exact (MK_COMB (@lem2323774) (@lem2323773 x)). Qed.
Lemma lem2323776 (x : int) (y : int) : (term114 x y) = (term78 x y).
Proof. exact (eq_refl (term114 x y)). Qed.
Lemma lem2323777 (x : int) : (term121 x) = (term112 x).
Proof. exact (fun_ext (fun y : int => @lem2323776 x y)). Qed.
Lemma lem2323778 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2323779 (x : int) : (term122 x) = (term123 x).
Proof. exact (MK_COMB (@lem2323778) (@lem2323777 x)). Qed.
Lemma lem2323780 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2323781 (x : int) : (term124 x) = (term125 x).
Proof. exact (MK_COMB (@lem2323780) (@lem2323779 x)). Qed.
Lemma lem2323782 (x : int) (y : int) : (term116 x y) = (term96 x y).
Proof. exact (eq_refl (term116 x y)). Qed.
Lemma lem2323783 (x : int) : (term126 x) = (term113 x).
Proof. exact (fun_ext (fun y : int => @lem2323782 x y)). Qed.
Lemma lem2323784 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2323785 (x : int) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem2323784) (@lem2323783 x)). Qed.
Lemma lem2323786 (x : int) : (term111 x) = (term129 x).
Proof. exact (MK_COMB (@lem2323781 x) (@lem2323785 x)). Qed.
Lemma lem2323787 (x : int) : ((term110 x) = (term111 x)) = ((term101 x) = (term129 x)).
Proof. exact (MK_COMB (@lem2323775 x) (@lem2323786 x)). Qed.
Lemma lem2323788 (x : int) : (term101 x) = (term129 x).
Proof. exact (EQ_MP (@lem2323787 x) (@lem2323765 x)). Qed.
Lemma lem2323895 : term102 = term130.
Proof. exact (fun_ext (fun x : int => @lem2323788 x)). Qed.
Lemma lem2323896 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2323897 : term103 = term131.
Proof. exact (MK_COMB (@lem2323896) (@lem2323895)). Qed.
Lemma lem2323899 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2323900 (P : int -> Prop) (Q : int -> Prop) : (term108 P Q) = (term109 P Q).
Proof. exact (@lem2323899 int P Q). Qed.
Lemma lem2323901 : term132 = term133.
Proof. exact (@lem2323900 term134 term135). Qed.
Lemma lem2323902 (x : int) : (term136 x) = (term123 x).
Proof. exact (eq_refl (term136 x)). Qed.
Lemma lem2323903 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2323904 (x : int) : (term137 x) = (term125 x).
Proof. exact (MK_COMB (@lem2323903) (@lem2323902 x)). Qed.
Lemma lem2323905 (x : int) : (term138 x) = (term128 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem2323906 (x : int) : (term139 x) = (term129 x).
Proof. exact (MK_COMB (@lem2323904 x) (@lem2323905 x)). Qed.
Lemma lem2323907 : term140 = term130.
Proof. exact (fun_ext (fun x : int => @lem2323906 x)). Qed.
Lemma lem2323908 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2323909 : term132 = term131.
Proof. exact (MK_COMB (@lem2323908) (@lem2323907)). Qed.
Lemma lem2323910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2323911 : term141 = term142.
Proof. exact (MK_COMB (@lem2323910) (@lem2323909)). Qed.
Lemma lem2323912 (x : int) : (term136 x) = (term123 x).
Proof. exact (eq_refl (term136 x)). Qed.
Lemma lem2323913 : term143 = term134.
Proof. exact (fun_ext (fun x : int => @lem2323912 x)). Qed.
Lemma lem2323914 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2323915 : term144 = term145.
Proof. exact (MK_COMB (@lem2323914) (@lem2323913)). Qed.
Lemma lem2323916 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2323917 : term146 = term147.
Proof. exact (MK_COMB (@lem2323916) (@lem2323915)). Qed.
Lemma lem2323918 (x : int) : (term138 x) = (term128 x).
Proof. exact (eq_refl (term138 x)). Qed.
Lemma lem2323919 : term148 = term135.
Proof. exact (fun_ext (fun x : int => @lem2323918 x)). Qed.
Lemma lem2323920 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2323921 : term149 = term150.
Proof. exact (MK_COMB (@lem2323920) (@lem2323919)). Qed.
Lemma lem2323922 : term133 = term151.
Proof. exact (MK_COMB (@lem2323917) (@lem2323921)). Qed.
Lemma lem2323923 : (term132 = term133) = (term131 = term151).
Proof. exact (MK_COMB (@lem2323911) (@lem2323922)). Qed.
Lemma lem2323924 : term131 = term151.
Proof. exact (EQ_MP (@lem2323923) (@lem2323901)). Qed.
Lemma lem2324039 : term103 = term151.
Proof. exact (TRANS (@lem2323897) (@lem2323924)). Qed.
Lemma lem2324041 : term105 = term151.
Proof. exact (TRANS (@lem2323757) (@lem2324039)). Qed.
Lemma lem2324050 (x : int) (y : int) : (term78 x y) = (term78 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem2324051 (x : int) : (term112 x) = (term112 x).
Proof. exact (fun_ext (fun y : int => @lem2324050 x y)). Qed.
Lemma lem2324052 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324053 (x : int) : (term123 x) = (term123 x).
Proof. exact (MK_COMB (@lem2324052) (@lem2324051 x)). Qed.
Lemma lem2324054 : term134 = term134.
Proof. exact (fun_ext (fun x : int => @lem2324053 x)). Qed.
Lemma lem2324055 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324056 : term145 = term145.
Proof. exact (MK_COMB (@lem2324055) (@lem2324054)). Qed.
Lemma lem2324065 (x : int) (y : int) : (term96 x y) = (term96 x y).
Proof. exact (eq_refl (term96 x y)). Qed.
Lemma lem2324066 (x : int) : (term113 x) = (term113 x).
Proof. exact (fun_ext (fun y : int => @lem2324065 x y)). Qed.
Lemma lem2324067 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324068 (x : int) : (term128 x) = (term128 x).
Proof. exact (MK_COMB (@lem2324067) (@lem2324066 x)). Qed.
Lemma lem2324069 : term135 = term135.
Proof. exact (fun_ext (fun x : int => @lem2324068 x)). Qed.
Lemma lem2324070 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324071 : term150 = term150.
Proof. exact (MK_COMB (@lem2324070) (@lem2324069)). Qed.
Lemma lem2324072 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2324073 : term147 = term147.
Proof. exact (MK_COMB (@lem2324072) (@lem2324056)). Qed.
Lemma lem2324074 : term151 = term151.
Proof. exact (MK_COMB (@lem2324073) (@lem2324071)). Qed.
Lemma lem2324075 : term105 = term151.
Proof. exact (TRANS (@lem2324041) (@lem2324074)). Qed.
Lemma lem2324084 (x : int) (y : int) : (term78 x y) = (term78 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem2324085 (x : int) : (term112 x) = (term112 x).
Proof. exact (fun_ext (fun y : int => @lem2324084 x y)). Qed.
Lemma lem2324086 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324087 (x : int) : (term123 x) = (term123 x).
Proof. exact (MK_COMB (@lem2324086) (@lem2324085 x)). Qed.
Lemma lem2324088 : term134 = term134.
Proof. exact (fun_ext (fun x : int => @lem2324087 x)). Qed.
Lemma lem2324089 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324090 : term145 = term145.
Proof. exact (MK_COMB (@lem2324089) (@lem2324088)). Qed.
Lemma lem2324099 (x : int) (y : int) : (term96 x y) = (term96 x y).
Proof. exact (eq_refl (term96 x y)). Qed.
Lemma lem2324100 (x : int) : (term113 x) = (term113 x).
Proof. exact (fun_ext (fun y : int => @lem2324099 x y)). Qed.
Lemma lem2324101 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324102 (x : int) : (term128 x) = (term128 x).
Proof. exact (MK_COMB (@lem2324101) (@lem2324100 x)). Qed.
Lemma lem2324103 : term135 = term135.
Proof. exact (fun_ext (fun x : int => @lem2324102 x)). Qed.
Lemma lem2324104 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324105 : term150 = term150.
Proof. exact (MK_COMB (@lem2324104) (@lem2324103)). Qed.
Lemma lem2324106 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2324107 : term147 = term147.
Proof. exact (MK_COMB (@lem2324106) (@lem2324090)). Qed.
Lemma lem2324108 : term151 = term151.
Proof. exact (MK_COMB (@lem2324107) (@lem2324105)). Qed.
Lemma lem2324109 : term105 = term151.
Proof. exact (TRANS (@lem2324075) (@lem2324108)). Qed.
Lemma lem2324110 (y : int) (x : int) : (term38 x y) = (term152 y x).
Proof. exact (@lem1988287 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2324116 (y : int) (x : int) : (term153 y x) = (term154 y x).
Proof. exact (@lem1982792 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2324121 (x : int) (y : int) : (term154 y x) = (term155 x y).
Proof. exact (@lem1982761 (term156 x) (real_of_int y)). Qed.
Lemma lem2324123 (x : int) (y : int) : (term153 y x) = (term155 x y).
Proof. exact (TRANS (@lem2324116 y x) (@lem2324121 x y)). Qed.
Lemma lem2324124 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2324125 (x : int) (y : int) : (term157 y x) = (term158 x y).
Proof. exact (MK_COMB (@lem2324124) (@lem2324123 x y)). Qed.
Lemma lem2324126 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2324127 (x : int) (y : int) : (term152 y x) = (term160 x y).
Proof. exact (MK_COMB (@lem2324125 x y) (@lem2324126)). Qed.
Lemma lem2324128 (x : int) (y : int) : (term38 x y) = (term160 x y).
Proof. exact (TRANS (@lem2324110 y x) (@lem2324127 x y)). Qed.
Lemma lem2324129 (x : int) (y : int) : (term61 y x) = (term161 x y).
Proof. exact (@lem1988287 (real_of_int x) (term58 x y)). Qed.
Lemma lem2324145 (x : int) (y : int) : (term162 x y) = (term163 x y).
Proof. exact (@lem1982792 (real_of_int x) (term58 x y)). Qed.
Lemma lem2324146 (x : int) (y : int) : (term164 x y) = (term165 x y).
Proof. exact (@lem1982781 (term51 x y) term166 term56). Qed.
Lemma lem2324148 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2324149 : term56 = term168.
Proof. exact (@lem2324148 term57). Qed.
Lemma lem2324151 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2324152 : term166 = term171.
Proof. exact (@lem2324151 term57). Qed.
Lemma lem2324153 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2324154 : term172 = term173.
Proof. exact (MK_COMB (@lem2324153) (@lem2324152)). Qed.
Lemma lem2324155 : term174 = term175.
Proof. exact (MK_COMB (@lem2324154) (@lem2324149)). Qed.
Lemma lem2324156 : term175 = term176.
Proof. exact (@lem1981613 term166 term56 term56 term56). Qed.
Lemma lem2324158 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2324159 : term179 = term180.
Proof. exact (@lem2324158 term57 term57). Qed.
Lemma lem2324160 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2324161 : term182 = term57.
Proof. exact (EQ_MP (@lem2324160) (@lem940073)). Qed.
Lemma lem2324162 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2324163 : term180 = term56.
Proof. exact (MK_COMB (@lem2324162) (@lem2324161)). Qed.
Lemma lem2324164 : term179 = term56.
Proof. exact (TRANS (@lem2324159) (@lem2324163)). Qed.
Lemma lem2324166 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2324167 : term174 = term185.
Proof. exact (@lem2324166 term57 term57). Qed.
Lemma lem2324168 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2324169 : term182 = term57.
Proof. exact (EQ_MP (@lem2324168) (@lem940073)). Qed.
Lemma lem2324170 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2324171 : term180 = term56.
Proof. exact (MK_COMB (@lem2324170) (@lem2324169)). Qed.
Lemma lem2324172 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2324173 : term185 = term166.
Proof. exact (MK_COMB (@lem2324172) (@lem2324171)). Qed.
Lemma lem2324174 : term174 = term166.
Proof. exact (TRANS (@lem2324167) (@lem2324173)). Qed.
Lemma lem2324175 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2324176 : term186 = term187.
Proof. exact (MK_COMB (@lem2324175) (@lem2324174)). Qed.
Lemma lem2324177 : term176 = term171.
Proof. exact (MK_COMB (@lem2324176) (@lem2324164)). Qed.
Lemma lem2324178 : term175 = term171.
Proof. exact (TRANS (@lem2324156) (@lem2324177)). Qed.
Lemma lem2324179 : term174 = term171.
Proof. exact (TRANS (@lem2324155) (@lem2324178)). Qed.
Lemma lem2324181 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2324182 : term171 = term166.
Proof. exact (@lem2324181 term166). Qed.
Lemma lem2324183 : term174 = term166.
Proof. exact (TRANS (@lem2324179) (@lem2324182)). Qed.
Lemma lem2324186 (x : int) (y : int) : (term189 x y) = (term189 x y).
Proof. exact (eq_refl (term189 x y)). Qed.
Lemma lem2324187 (x : int) (y : int) : (term165 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem2324186 x y) (@lem2324183)). Qed.
Lemma lem2324188 (x : int) (y : int) : (term164 x y) = (term190 x y).
Proof. exact (TRANS (@lem2324146 x y) (@lem2324187 x y)). Qed.
Lemma lem2324189 (x : int) : (term69 x) = (term69 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem2324192 (x : int) (y : int) : (term163 x y) = (term191 x y).
Proof. exact (MK_COMB (@lem2324189 x) (@lem2324188 x y)). Qed.
Lemma lem2324194 (x : int) (y : int) : (term162 x y) = (term191 x y).
Proof. exact (TRANS (@lem2324145 x y) (@lem2324192 x y)). Qed.
Lemma lem2324195 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2324196 (x : int) (y : int) : (term192 x y) = (term193 x y).
Proof. exact (MK_COMB (@lem2324195) (@lem2324194 x y)). Qed.
Lemma lem2324197 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2324198 (x : int) (y : int) : (term161 x y) = (term194 x y).
Proof. exact (MK_COMB (@lem2324196 x y) (@lem2324197)). Qed.
Lemma lem2324199 (x : int) (y : int) : (term61 y x) = (term194 x y).
Proof. exact (TRANS (@lem2324129 x y) (@lem2324198 x y)). Qed.
Lemma lem2324200 (y : int) (x : int) : (term73 x y) = (term195 y x).
Proof. exact (@lem1988287 (term51 x y) (term70 x)). Qed.
Lemma lem2324216 (y : int) (x : int) : (term196 y x) = (term197 y x).
Proof. exact (@lem1982792 (term51 x y) (term70 x)). Qed.
Lemma lem2324217 (x : int) : (term198 x) = (term199 x).
Proof. exact (@lem1982781 (real_of_int x) term166 term56). Qed.
Lemma lem2324219 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2324220 : term56 = term168.
Proof. exact (@lem2324219 term57). Qed.
Lemma lem2324222 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2324223 : term166 = term171.
Proof. exact (@lem2324222 term57). Qed.
Lemma lem2324224 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2324225 : term172 = term173.
Proof. exact (MK_COMB (@lem2324224) (@lem2324223)). Qed.
Lemma lem2324226 : term174 = term175.
Proof. exact (MK_COMB (@lem2324225) (@lem2324220)). Qed.
Lemma lem2324227 : term175 = term176.
Proof. exact (@lem1981613 term166 term56 term56 term56). Qed.
Lemma lem2324229 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2324230 : term179 = term180.
Proof. exact (@lem2324229 term57 term57). Qed.
Lemma lem2324231 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2324232 : term182 = term57.
Proof. exact (EQ_MP (@lem2324231) (@lem940073)). Qed.
Lemma lem2324233 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2324234 : term180 = term56.
Proof. exact (MK_COMB (@lem2324233) (@lem2324232)). Qed.
Lemma lem2324235 : term179 = term56.
Proof. exact (TRANS (@lem2324230) (@lem2324234)). Qed.
Lemma lem2324237 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2324238 : term174 = term185.
Proof. exact (@lem2324237 term57 term57). Qed.
Lemma lem2324239 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2324240 : term182 = term57.
Proof. exact (EQ_MP (@lem2324239) (@lem940073)). Qed.
Lemma lem2324241 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2324242 : term180 = term56.
Proof. exact (MK_COMB (@lem2324241) (@lem2324240)). Qed.
Lemma lem2324243 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2324244 : term185 = term166.
Proof. exact (MK_COMB (@lem2324243) (@lem2324242)). Qed.
Lemma lem2324245 : term174 = term166.
Proof. exact (TRANS (@lem2324238) (@lem2324244)). Qed.
Lemma lem2324246 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2324247 : term186 = term187.
Proof. exact (MK_COMB (@lem2324246) (@lem2324245)). Qed.
Lemma lem2324248 : term176 = term171.
Proof. exact (MK_COMB (@lem2324247) (@lem2324235)). Qed.
Lemma lem2324249 : term175 = term171.
Proof. exact (TRANS (@lem2324227) (@lem2324248)). Qed.
Lemma lem2324250 : term174 = term171.
Proof. exact (TRANS (@lem2324226) (@lem2324249)). Qed.
Lemma lem2324252 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2324253 : term171 = term166.
Proof. exact (@lem2324252 term166). Qed.
Lemma lem2324254 : term174 = term166.
Proof. exact (TRANS (@lem2324250) (@lem2324253)). Qed.
Lemma lem2324257 (x : int) : (term200 x) = (term200 x).
Proof. exact (eq_refl (term200 x)). Qed.
Lemma lem2324258 (x : int) : (term199 x) = (term201 x).
Proof. exact (MK_COMB (@lem2324257 x) (@lem2324254)). Qed.
Lemma lem2324259 (x : int) : (term198 x) = (term201 x).
Proof. exact (TRANS (@lem2324217 x) (@lem2324258 x)). Qed.
Lemma lem2324260 (x : int) (y : int) : (term53 x y) = (term53 x y).
Proof. exact (eq_refl (term53 x y)). Qed.
Lemma lem2324261 (y : int) (x : int) : (term197 y x) = (term202 y x).
Proof. exact (MK_COMB (@lem2324260 x y) (@lem2324259 x)). Qed.
Lemma lem2324266 (x : int) (y : int) : (term202 y x) = (term203 x y).
Proof. exact (@lem1982757 (term156 x) (term51 x y) term166). Qed.
Lemma lem2324267 (x : int) (y : int) : (term197 y x) = (term203 x y).
Proof. exact (TRANS (@lem2324261 y x) (@lem2324266 x y)). Qed.
Lemma lem2324269 (x : int) (y : int) : (term196 y x) = (term203 x y).
Proof. exact (TRANS (@lem2324216 y x) (@lem2324267 x y)). Qed.
Lemma lem2324270 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2324271 (x : int) (y : int) : (term204 y x) = (term205 x y).
Proof. exact (MK_COMB (@lem2324270) (@lem2324269 x y)). Qed.
Lemma lem2324272 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2324273 (x : int) (y : int) : (term195 y x) = (term206 x y).
Proof. exact (MK_COMB (@lem2324271 x y) (@lem2324272)). Qed.
Lemma lem2324274 (x : int) (y : int) : (term73 x y) = (term206 x y).
Proof. exact (TRANS (@lem2324200 y x) (@lem2324273 x y)). Qed.
Lemma lem2324275 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2324276 (x : int) (y : int) : (term63 y x) = (term207 x y).
Proof. exact (MK_COMB (@lem2324275) (@lem2324199 x y)). Qed.
Lemma lem2324277 (x : int) (y : int) : (term74 x y) = (term208 x y).
Proof. exact (MK_COMB (@lem2324276 x y) (@lem2324274 x y)). Qed.
Lemma lem2324278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2324279 (x : int) (y : int) : (term76 x y) = (term209 x y).
Proof. exact (MK_COMB (@lem2324278) (@lem2324128 x y)). Qed.
Lemma lem2324280 (x : int) (y : int) : (term78 x y) = (term210 x y).
Proof. exact (MK_COMB (@lem2324279 x y) (@lem2324277 x y)). Qed.
Lemma lem2324281 (x : int) : (term112 x) = (term211 x).
Proof. exact (fun_ext (fun y : int => @lem2324280 x y)). Qed.
Lemma lem2324282 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324283 (x : int) : (term123 x) = (term212 x).
Proof. exact (MK_COMB (@lem2324282) (@lem2324281 x)). Qed.
Lemma lem2324284 : term134 = term213.
Proof. exact (fun_ext (fun x : int => @lem2324283 x)). Qed.
Lemma lem2324285 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324286 : term145 = term214.
Proof. exact (MK_COMB (@lem2324285) (@lem2324284)). Qed.
Lemma lem2324287 (x : int) (y : int) : (term82 y x) = (term215 x y).
Proof. exact (@lem1988287 (real_of_int x) (term70 y)). Qed.
Lemma lem2324299 (x : int) (y : int) : (term216 x y) = (term217 x y).
Proof. exact (@lem1982792 (real_of_int x) (term70 y)). Qed.
Lemma lem2324300 (y : int) : (term198 y) = (term199 y).
Proof. exact (@lem1982781 (real_of_int y) term166 term56). Qed.
Lemma lem2324302 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2324303 : term56 = term168.
Proof. exact (@lem2324302 term57). Qed.
Lemma lem2324305 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2324306 : term166 = term171.
Proof. exact (@lem2324305 term57). Qed.
Lemma lem2324307 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2324308 : term172 = term173.
Proof. exact (MK_COMB (@lem2324307) (@lem2324306)). Qed.
Lemma lem2324309 : term174 = term175.
Proof. exact (MK_COMB (@lem2324308) (@lem2324303)). Qed.
Lemma lem2324310 : term175 = term176.
Proof. exact (@lem1981613 term166 term56 term56 term56). Qed.
Lemma lem2324312 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2324313 : term179 = term180.
Proof. exact (@lem2324312 term57 term57). Qed.
Lemma lem2324314 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2324315 : term182 = term57.
Proof. exact (EQ_MP (@lem2324314) (@lem940073)). Qed.
Lemma lem2324316 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2324317 : term180 = term56.
Proof. exact (MK_COMB (@lem2324316) (@lem2324315)). Qed.
Lemma lem2324318 : term179 = term56.
Proof. exact (TRANS (@lem2324313) (@lem2324317)). Qed.
Lemma lem2324320 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2324321 : term174 = term185.
Proof. exact (@lem2324320 term57 term57). Qed.
Lemma lem2324322 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2324323 : term182 = term57.
Proof. exact (EQ_MP (@lem2324322) (@lem940073)). Qed.
Lemma lem2324324 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2324325 : term180 = term56.
Proof. exact (MK_COMB (@lem2324324) (@lem2324323)). Qed.
Lemma lem2324326 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2324327 : term185 = term166.
Proof. exact (MK_COMB (@lem2324326) (@lem2324325)). Qed.
Lemma lem2324328 : term174 = term166.
Proof. exact (TRANS (@lem2324321) (@lem2324327)). Qed.
Lemma lem2324329 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2324330 : term186 = term187.
Proof. exact (MK_COMB (@lem2324329) (@lem2324328)). Qed.
Lemma lem2324331 : term176 = term171.
Proof. exact (MK_COMB (@lem2324330) (@lem2324318)). Qed.
Lemma lem2324332 : term175 = term171.
Proof. exact (TRANS (@lem2324310) (@lem2324331)). Qed.
Lemma lem2324333 : term174 = term171.
Proof. exact (TRANS (@lem2324309) (@lem2324332)). Qed.
Lemma lem2324335 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2324336 : term171 = term166.
Proof. exact (@lem2324335 term166). Qed.
Lemma lem2324337 : term174 = term166.
Proof. exact (TRANS (@lem2324333) (@lem2324336)). Qed.
Lemma lem2324340 (y : int) : (term200 y) = (term200 y).
Proof. exact (eq_refl (term200 y)). Qed.
Lemma lem2324341 (y : int) : (term199 y) = (term201 y).
Proof. exact (MK_COMB (@lem2324340 y) (@lem2324337)). Qed.
Lemma lem2324342 (y : int) : (term198 y) = (term201 y).
Proof. exact (TRANS (@lem2324300 y) (@lem2324341 y)). Qed.
Lemma lem2324343 (x : int) : (term69 x) = (term69 x).
Proof. exact (eq_refl (term69 x)). Qed.
Lemma lem2324346 (x : int) (y : int) : (term217 x y) = (term218 x y).
Proof. exact (MK_COMB (@lem2324343 x) (@lem2324342 y)). Qed.
Lemma lem2324348 (x : int) (y : int) : (term216 x y) = (term218 x y).
Proof. exact (TRANS (@lem2324299 x y) (@lem2324346 x y)). Qed.
Lemma lem2324349 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2324350 (x : int) (y : int) : (term219 x y) = (term220 x y).
Proof. exact (MK_COMB (@lem2324349) (@lem2324348 x y)). Qed.
Lemma lem2324351 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2324352 (x : int) (y : int) : (term215 x y) = (term221 x y).
Proof. exact (MK_COMB (@lem2324350 x y) (@lem2324351)). Qed.
Lemma lem2324353 (x : int) (y : int) : (term82 y x) = (term221 x y).
Proof. exact (TRANS (@lem2324287 x y) (@lem2324352 x y)). Qed.
Lemma lem2324354 (x : int) (y : int) : (term86 x y) = (term222 x y).
Proof. exact (@lem1988287 (real_of_int y) (term58 x y)). Qed.
Lemma lem2324370 (x : int) (y : int) : (term223 x y) = (term224 x y).
Proof. exact (@lem1982792 (real_of_int y) (term58 x y)). Qed.
Lemma lem2324371 (x : int) (y : int) : (term164 x y) = (term165 x y).
Proof. exact (@lem1982781 (term51 x y) term166 term56). Qed.
Lemma lem2324373 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2324374 : term56 = term168.
Proof. exact (@lem2324373 term57). Qed.
Lemma lem2324376 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2324377 : term166 = term171.
Proof. exact (@lem2324376 term57). Qed.
Lemma lem2324378 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2324379 : term172 = term173.
Proof. exact (MK_COMB (@lem2324378) (@lem2324377)). Qed.
Lemma lem2324380 : term174 = term175.
Proof. exact (MK_COMB (@lem2324379) (@lem2324374)). Qed.
Lemma lem2324381 : term175 = term176.
Proof. exact (@lem1981613 term166 term56 term56 term56). Qed.
Lemma lem2324383 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2324384 : term179 = term180.
Proof. exact (@lem2324383 term57 term57). Qed.
Lemma lem2324385 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2324386 : term182 = term57.
Proof. exact (EQ_MP (@lem2324385) (@lem940073)). Qed.
Lemma lem2324387 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2324388 : term180 = term56.
Proof. exact (MK_COMB (@lem2324387) (@lem2324386)). Qed.
Lemma lem2324389 : term179 = term56.
Proof. exact (TRANS (@lem2324384) (@lem2324388)). Qed.
Lemma lem2324391 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2324392 : term174 = term185.
Proof. exact (@lem2324391 term57 term57). Qed.
Lemma lem2324393 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2324394 : term182 = term57.
Proof. exact (EQ_MP (@lem2324393) (@lem940073)). Qed.
Lemma lem2324395 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2324396 : term180 = term56.
Proof. exact (MK_COMB (@lem2324395) (@lem2324394)). Qed.
Lemma lem2324397 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2324398 : term185 = term166.
Proof. exact (MK_COMB (@lem2324397) (@lem2324396)). Qed.
Lemma lem2324399 : term174 = term166.
Proof. exact (TRANS (@lem2324392) (@lem2324398)). Qed.
Lemma lem2324400 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2324401 : term186 = term187.
Proof. exact (MK_COMB (@lem2324400) (@lem2324399)). Qed.
Lemma lem2324402 : term176 = term171.
Proof. exact (MK_COMB (@lem2324401) (@lem2324389)). Qed.
Lemma lem2324403 : term175 = term171.
Proof. exact (TRANS (@lem2324381) (@lem2324402)). Qed.
Lemma lem2324404 : term174 = term171.
Proof. exact (TRANS (@lem2324380) (@lem2324403)). Qed.
Lemma lem2324406 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2324407 : term171 = term166.
Proof. exact (@lem2324406 term166). Qed.
Lemma lem2324408 : term174 = term166.
Proof. exact (TRANS (@lem2324404) (@lem2324407)). Qed.
Lemma lem2324411 (x : int) (y : int) : (term189 x y) = (term189 x y).
Proof. exact (eq_refl (term189 x y)). Qed.
Lemma lem2324412 (x : int) (y : int) : (term165 x y) = (term190 x y).
Proof. exact (MK_COMB (@lem2324411 x y) (@lem2324408)). Qed.
Lemma lem2324413 (x : int) (y : int) : (term164 x y) = (term190 x y).
Proof. exact (TRANS (@lem2324371 x y) (@lem2324412 x y)). Qed.
Lemma lem2324414 (y : int) : (term69 y) = (term69 y).
Proof. exact (eq_refl (term69 y)). Qed.
Lemma lem2324417 (x : int) (y : int) : (term224 x y) = (term225 x y).
Proof. exact (MK_COMB (@lem2324414 y) (@lem2324413 x y)). Qed.
Lemma lem2324419 (x : int) (y : int) : (term223 x y) = (term225 x y).
Proof. exact (TRANS (@lem2324370 x y) (@lem2324417 x y)). Qed.
Lemma lem2324420 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2324421 (x : int) (y : int) : (term226 x y) = (term227 x y).
Proof. exact (MK_COMB (@lem2324420) (@lem2324419 x y)). Qed.
Lemma lem2324422 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2324423 (x : int) (y : int) : (term222 x y) = (term228 x y).
Proof. exact (MK_COMB (@lem2324421 x y) (@lem2324422)). Qed.
Lemma lem2324424 (x : int) (y : int) : (term86 x y) = (term228 x y).
Proof. exact (TRANS (@lem2324354 x y) (@lem2324423 x y)). Qed.
Lemma lem2324425 (x : int) (y : int) : (term91 x y) = (term229 x y).
Proof. exact (@lem1988287 (term51 x y) (term70 y)). Qed.
Lemma lem2324441 (x : int) (y : int) : (term230 x y) = (term231 x y).
Proof. exact (@lem1982792 (term51 x y) (term70 y)). Qed.
Lemma lem2324442 (y : int) : (term198 y) = (term199 y).
Proof. exact (@lem1982781 (real_of_int y) term166 term56). Qed.
Lemma lem2324444 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2324445 : term56 = term168.
Proof. exact (@lem2324444 term57). Qed.
Lemma lem2324447 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2324448 : term166 = term171.
Proof. exact (@lem2324447 term57). Qed.
Lemma lem2324449 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2324450 : term172 = term173.
Proof. exact (MK_COMB (@lem2324449) (@lem2324448)). Qed.
Lemma lem2324451 : term174 = term175.
Proof. exact (MK_COMB (@lem2324450) (@lem2324445)). Qed.
Lemma lem2324452 : term175 = term176.
Proof. exact (@lem1981613 term166 term56 term56 term56). Qed.
Lemma lem2324454 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2324455 : term179 = term180.
Proof. exact (@lem2324454 term57 term57). Qed.
Lemma lem2324456 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2324457 : term182 = term57.
Proof. exact (EQ_MP (@lem2324456) (@lem940073)). Qed.
Lemma lem2324458 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2324459 : term180 = term56.
Proof. exact (MK_COMB (@lem2324458) (@lem2324457)). Qed.
Lemma lem2324460 : term179 = term56.
Proof. exact (TRANS (@lem2324455) (@lem2324459)). Qed.
Lemma lem2324462 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2324463 : term174 = term185.
Proof. exact (@lem2324462 term57 term57). Qed.
Lemma lem2324464 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2324465 : term182 = term57.
Proof. exact (EQ_MP (@lem2324464) (@lem940073)). Qed.
Lemma lem2324466 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2324467 : term180 = term56.
Proof. exact (MK_COMB (@lem2324466) (@lem2324465)). Qed.
Lemma lem2324468 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2324469 : term185 = term166.
Proof. exact (MK_COMB (@lem2324468) (@lem2324467)). Qed.
Lemma lem2324470 : term174 = term166.
Proof. exact (TRANS (@lem2324463) (@lem2324469)). Qed.
Lemma lem2324471 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2324472 : term186 = term187.
Proof. exact (MK_COMB (@lem2324471) (@lem2324470)). Qed.
Lemma lem2324473 : term176 = term171.
Proof. exact (MK_COMB (@lem2324472) (@lem2324460)). Qed.
Lemma lem2324474 : term175 = term171.
Proof. exact (TRANS (@lem2324452) (@lem2324473)). Qed.
Lemma lem2324475 : term174 = term171.
Proof. exact (TRANS (@lem2324451) (@lem2324474)). Qed.
Lemma lem2324477 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2324478 : term171 = term166.
Proof. exact (@lem2324477 term166). Qed.
Lemma lem2324479 : term174 = term166.
Proof. exact (TRANS (@lem2324475) (@lem2324478)). Qed.
Lemma lem2324482 (y : int) : (term200 y) = (term200 y).
Proof. exact (eq_refl (term200 y)). Qed.
Lemma lem2324483 (y : int) : (term199 y) = (term201 y).
Proof. exact (MK_COMB (@lem2324482 y) (@lem2324479)). Qed.
Lemma lem2324484 (y : int) : (term198 y) = (term201 y).
Proof. exact (TRANS (@lem2324442 y) (@lem2324483 y)). Qed.
Lemma lem2324485 (x : int) (y : int) : (term53 x y) = (term53 x y).
Proof. exact (eq_refl (term53 x y)). Qed.
Lemma lem2324486 (x : int) (y : int) : (term231 x y) = (term232 x y).
Proof. exact (MK_COMB (@lem2324485 x y) (@lem2324484 y)). Qed.
Lemma lem2324491 (x : int) (y : int) : (term232 x y) = (term233 x y).
Proof. exact (@lem1982757 (term156 y) (term51 x y) term166). Qed.
Lemma lem2324492 (x : int) (y : int) : (term231 x y) = (term233 x y).
Proof. exact (TRANS (@lem2324486 x y) (@lem2324491 x y)). Qed.
Lemma lem2324494 (x : int) (y : int) : (term230 x y) = (term233 x y).
Proof. exact (TRANS (@lem2324441 x y) (@lem2324492 x y)). Qed.
Lemma lem2324495 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2324496 (x : int) (y : int) : (term234 x y) = (term235 x y).
Proof. exact (MK_COMB (@lem2324495) (@lem2324494 x y)). Qed.
Lemma lem2324497 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2324498 (x : int) (y : int) : (term229 x y) = (term236 x y).
Proof. exact (MK_COMB (@lem2324496 x y) (@lem2324497)). Qed.
Lemma lem2324499 (x : int) (y : int) : (term91 x y) = (term236 x y).
Proof. exact (TRANS (@lem2324425 x y) (@lem2324498 x y)). Qed.
Lemma lem2324500 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2324501 (x : int) (y : int) : (term88 x y) = (term237 x y).
Proof. exact (MK_COMB (@lem2324500) (@lem2324424 x y)). Qed.
Lemma lem2324502 (x : int) (y : int) : (term92 x y) = (term238 x y).
Proof. exact (MK_COMB (@lem2324501 x y) (@lem2324499 x y)). Qed.
Lemma lem2324503 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2324504 (x : int) (y : int) : (term94 y x) = (term239 x y).
Proof. exact (MK_COMB (@lem2324503) (@lem2324353 x y)). Qed.
Lemma lem2324505 (x : int) (y : int) : (term96 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem2324504 x y) (@lem2324502 x y)). Qed.
Lemma lem2324506 (x : int) : (term113 x) = (term241 x).
Proof. exact (fun_ext (fun y : int => @lem2324505 x y)). Qed.
Lemma lem2324507 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324508 (x : int) : (term128 x) = (term242 x).
Proof. exact (MK_COMB (@lem2324507) (@lem2324506 x)). Qed.
Lemma lem2324509 : term135 = term243.
Proof. exact (fun_ext (fun x : int => @lem2324508 x)). Qed.
Lemma lem2324510 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324511 : term150 = term244.
Proof. exact (MK_COMB (@lem2324510) (@lem2324509)). Qed.
Lemma lem2324512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2324513 : term147 = term245.
Proof. exact (MK_COMB (@lem2324512) (@lem2324286)). Qed.
Lemma lem2324514 : term151 = term246.
Proof. exact (MK_COMB (@lem2324513) (@lem2324511)). Qed.
Lemma lem2324515 : term105 = term246.
Proof. exact (TRANS (@lem2324109) (@lem2324514)). Qed.
Lemma lem2324622 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term107 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2324623 (P : int -> Prop) (Q : int -> Prop) : (term109 P Q) = (term108 P Q).
Proof. exact (@lem2324622 int P Q). Qed.
Lemma lem2324624 : term247 = term248.
Proof. exact (@lem2324623 term213 term243). Qed.
Lemma lem2324625 (x : int) : (term249 x) = (term212 x).
Proof. exact (eq_refl (term249 x)). Qed.
Lemma lem2324626 : term250 = term213.
Proof. exact (fun_ext (fun x : int => @lem2324625 x)). Qed.
Lemma lem2324627 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324628 : term251 = term214.
Proof. exact (MK_COMB (@lem2324627) (@lem2324626)). Qed.
Lemma lem2324629 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2324630 : term252 = term245.
Proof. exact (MK_COMB (@lem2324629) (@lem2324628)). Qed.
Lemma lem2324631 (x : int) : (term253 x) = (term242 x).
Proof. exact (eq_refl (term253 x)). Qed.
Lemma lem2324632 : term254 = term243.
Proof. exact (fun_ext (fun x : int => @lem2324631 x)). Qed.
Lemma lem2324633 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324634 : term255 = term244.
Proof. exact (MK_COMB (@lem2324633) (@lem2324632)). Qed.
Lemma lem2324635 : term247 = term246.
Proof. exact (MK_COMB (@lem2324630) (@lem2324634)). Qed.
Lemma lem2324636 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2324637 : term256 = term257.
Proof. exact (MK_COMB (@lem2324636) (@lem2324635)). Qed.
Lemma lem2324638 (x : int) : (term249 x) = (term212 x).
Proof. exact (eq_refl (term249 x)). Qed.
Lemma lem2324639 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2324640 (x : int) : (term258 x) = (term259 x).
Proof. exact (MK_COMB (@lem2324639) (@lem2324638 x)). Qed.
Lemma lem2324641 (x : int) : (term253 x) = (term242 x).
Proof. exact (eq_refl (term253 x)). Qed.
Lemma lem2324642 (x : int) : (term260 x) = (term261 x).
Proof. exact (MK_COMB (@lem2324640 x) (@lem2324641 x)). Qed.
Lemma lem2324643 : term262 = term263.
Proof. exact (fun_ext (fun x : int => @lem2324642 x)). Qed.
Lemma lem2324644 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324645 : term248 = term264.
Proof. exact (MK_COMB (@lem2324644) (@lem2324643)). Qed.
Lemma lem2324646 : (term247 = term248) = (term246 = term264).
Proof. exact (MK_COMB (@lem2324637) (@lem2324645)). Qed.
Lemma lem2324647 : term246 = term264.
Proof. exact (EQ_MP (@lem2324646) (@lem2324624)). Qed.
Lemma lem2324649 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term107 A P Q) = (term106 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem2324650 (P : int -> Prop) (Q : int -> Prop) : (term109 P Q) = (term108 P Q).
Proof. exact (@lem2324649 int P Q). Qed.
Lemma lem2324651 (x : int) : (term265 x) = (term266 x).
Proof. exact (@lem2324650 (term211 x) (term241 x)). Qed.
Lemma lem2324652 (x : int) (y : int) : (term267 x y) = (term210 x y).
Proof. exact (eq_refl (term267 x y)). Qed.
Lemma lem2324653 (x : int) : (term268 x) = (term211 x).
Proof. exact (fun_ext (fun y : int => @lem2324652 x y)). Qed.
Lemma lem2324654 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324655 (x : int) : (term269 x) = (term212 x).
Proof. exact (MK_COMB (@lem2324654) (@lem2324653 x)). Qed.
Lemma lem2324656 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2324657 (x : int) : (term270 x) = (term259 x).
Proof. exact (MK_COMB (@lem2324656) (@lem2324655 x)). Qed.
Lemma lem2324658 (x : int) (y : int) : (term271 x y) = (term240 x y).
Proof. exact (eq_refl (term271 x y)). Qed.
Lemma lem2324659 (x : int) : (term272 x) = (term241 x).
Proof. exact (fun_ext (fun y : int => @lem2324658 x y)). Qed.
Lemma lem2324660 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324661 (x : int) : (term273 x) = (term242 x).
Proof. exact (MK_COMB (@lem2324660) (@lem2324659 x)). Qed.
Lemma lem2324662 (x : int) : (term265 x) = (term261 x).
Proof. exact (MK_COMB (@lem2324657 x) (@lem2324661 x)). Qed.
Lemma lem2324663 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2324664 (x : int) : (term274 x) = (term275 x).
Proof. exact (MK_COMB (@lem2324663) (@lem2324662 x)). Qed.
Lemma lem2324665 (x : int) (y : int) : (term267 x y) = (term210 x y).
Proof. exact (eq_refl (term267 x y)). Qed.
Lemma lem2324666 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2324667 (x : int) (y : int) : (term276 x y) = (term277 x y).
Proof. exact (MK_COMB (@lem2324666) (@lem2324665 x y)). Qed.
Lemma lem2324668 (x : int) (y : int) : (term271 x y) = (term240 x y).
Proof. exact (eq_refl (term271 x y)). Qed.
Lemma lem2324669 (x : int) (y : int) : (term278 x y) = (term279 x y).
Proof. exact (MK_COMB (@lem2324667 x y) (@lem2324668 x y)). Qed.
Lemma lem2324670 (x : int) : (term280 x) = (term281 x).
Proof. exact (fun_ext (fun y : int => @lem2324669 x y)). Qed.
Lemma lem2324671 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324672 (x : int) : (term266 x) = (term282 x).
Proof. exact (MK_COMB (@lem2324671) (@lem2324670 x)). Qed.
Lemma lem2324673 (x : int) : ((term265 x) = (term266 x)) = ((term261 x) = (term282 x)).
Proof. exact (MK_COMB (@lem2324664 x) (@lem2324672 x)). Qed.
Lemma lem2324674 (x : int) : (term261 x) = (term282 x).
Proof. exact (EQ_MP (@lem2324673 x) (@lem2324651 x)). Qed.
Lemma lem2324675 : term263 = term283.
Proof. exact (fun_ext (fun x : int => @lem2324674 x)). Qed.
Lemma lem2324676 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324677 : term264 = term284.
Proof. exact (MK_COMB (@lem2324676) (@lem2324675)). Qed.
Lemma lem2324679 : term246 = term284.
Proof. exact (TRANS (@lem2324647) (@lem2324677)). Qed.
Lemma lem2324682 : term105 = term284.
Proof. exact (TRANS (@lem2324515) (@lem2324679)). Qed.
Lemma lem2324699 (x : int) (y : int) : (term240 x y) = (term285 x y).
Proof. exact (@lem19158 (term228 x y) (term221 x y) (term236 x y)). Qed.
Lemma lem2324716 (x : int) (y : int) : (term210 x y) = (term286 x y).
Proof. exact (@lem19158 (term194 x y) (term160 x y) (term206 x y)). Qed.
Lemma lem2324717 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2324718 (x : int) (y : int) : (term277 x y) = (term287 x y).
Proof. exact (MK_COMB (@lem2324717) (@lem2324716 x y)). Qed.
Lemma lem2324719 (x : int) (y : int) : (term279 x y) = (term288 x y).
Proof. exact (MK_COMB (@lem2324718 x y) (@lem2324699 x y)). Qed.
Lemma lem2324720 (x : int) : (term281 x) = (term289 x).
Proof. exact (fun_ext (fun y : int => @lem2324719 x y)). Qed.
Lemma lem2324721 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324722 (x : int) : (term282 x) = (term290 x).
Proof. exact (MK_COMB (@lem2324721) (@lem2324720 x)). Qed.
Lemma lem2324723 : term283 = term291.
Proof. exact (fun_ext (fun x : int => @lem2324722 x)). Qed.
Lemma lem2324724 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2324725 : term284 = term292.
Proof. exact (MK_COMB (@lem2324724) (@lem2324723)). Qed.
Lemma lem2324726 : term105 = term292.
Proof. exact (TRANS (@lem2324682) (@lem2324725)). Qed.
Lemma lem2324728 (x : int) (y : int) : (term293 x y) = (term294 x y).
Proof. exact (eq_refl (term293 x y)). Qed.
Lemma lem2324729 (x : int) (y : int) : (term294 x y) = (term293 x y).
Proof. exact (SYM (@lem2324728 x y)). Qed.
Lemma lem2324730 (x : int) (y : int) : (term293 x y) = (term295 x y).
Proof. exact (@lem1483429 (real_of_int x) (term296 y x) (real_of_int y)). Qed.
Lemma lem2324731 (x : int) (y : int) : (term294 x y) = (term295 x y).
Proof. exact (TRANS (@lem2324729 x y) (@lem2324730 x y)). Qed.
Lemma lem2324732 (x : int) (y : int) : (term297 x y) = (term298 x y).
Proof. exact (eq_refl (term297 x y)). Qed.
Lemma lem2324733 (x : int) (y : int) : (term299 x y) = (term299 x y).
Proof. exact (eq_refl (term299 x y)). Qed.
Lemma lem2324734 (x : int) (y : int) : (term300 x y) = (term301 x y).
Proof. exact (MK_COMB (@lem2324733 x y) (@lem2324732 x y)). Qed.
Lemma lem2324735 (y : int) (x : int) : (term302 y x) = (term303 y x).
Proof. exact (eq_refl (term302 y x)). Qed.
Lemma lem2324736 (y : int) (x : int) : (term304 y x) = (term304 y x).
Proof. exact (eq_refl (term304 y x)). Qed.
Lemma lem2324737 (y : int) (x : int) : (term305 y x) = (term306 y x).
Proof. exact (MK_COMB (@lem2324736 y x) (@lem2324735 y x)). Qed.
Lemma lem2324738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2324739 (y : int) (x : int) : (term307 y x) = (term308 y x).
Proof. exact (MK_COMB (@lem2324738) (@lem2324737 y x)). Qed.
Lemma lem2324740 (x : int) (y : int) : (term295 x y) = (term309 x y).
Proof. exact (MK_COMB (@lem2324739 y x) (@lem2324734 x y)). Qed.
Lemma lem2324741 (x : int) (y : int) : (term310 x y) = (term310 x y).
Proof. exact (eq_refl (term310 x y)). Qed.
Lemma lem2324742 (x : int) (y : int) : ((term294 x y) = (term295 x y)) = ((term294 x y) = (term309 x y)).
Proof. exact (MK_COMB (@lem2324741 x y) (@lem2324740 x y)). Qed.
Lemma lem2324743 (x : int) (y : int) : (term294 x y) = (term309 x y).
Proof. exact (EQ_MP (@lem2324742 x y) (@lem2324731 x y)). Qed.
Lemma lem2324744 (y : int) (x : int) : (term311 y x) = (term152 y x).
Proof. exact (@lem1988291 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2324750 (y : int) (x : int) : (term153 y x) = (term154 y x).
Proof. exact (@lem1982792 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2324755 (x : int) (y : int) : (term154 y x) = (term155 x y).
Proof. exact (@lem1982761 (term156 x) (real_of_int y)). Qed.
Lemma lem2324757 (x : int) (y : int) : (term153 y x) = (term155 x y).
Proof. exact (TRANS (@lem2324750 y x) (@lem2324755 x y)). Qed.
Lemma lem2324758 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2324759 (x : int) (y : int) : (term157 y x) = (term158 x y).
Proof. exact (MK_COMB (@lem2324758) (@lem2324757 x y)). Qed.
Lemma lem2324760 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2324761 (x : int) (y : int) : (term152 y x) = (term160 x y).
Proof. exact (MK_COMB (@lem2324759 x y) (@lem2324760)). Qed.
Lemma lem2324762 (x : int) (y : int) : (term311 y x) = (term160 x y).
Proof. exact (TRANS (@lem2324744 y x) (@lem2324761 x y)). Qed.
Lemma lem2324763 (x : int) (y : int) : (term160 x y) = (term312 x y).
Proof. exact (@lem1988291 (term155 x y) term159). Qed.
Lemma lem2324781 (x : int) (y : int) : (term313 x y) = (term314 x y).
Proof. exact (@lem1982792 (term155 x y) term159). Qed.
Lemma lem2324783 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2324784 : term159 = term315.
Proof. exact (@lem2324783 (NUMERAL 0)). Qed.
Lemma lem2324786 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2324787 : term166 = term171.
Proof. exact (@lem2324786 term57). Qed.
Lemma lem2324788 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2324789 : term172 = term173.
Proof. exact (MK_COMB (@lem2324788) (@lem2324787)). Qed.
Lemma lem2324790 : term316 = term317.
Proof. exact (MK_COMB (@lem2324789) (@lem2324784)). Qed.
Lemma lem2324791 : term317 = term318.
Proof. exact (@lem1981613 term166 term159 term56 term56). Qed.
Lemma lem2324793 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2324794 : term179 = term180.
Proof. exact (@lem2324793 term57 term57). Qed.
Lemma lem2324795 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2324796 : term182 = term57.
Proof. exact (EQ_MP (@lem2324795) (@lem940073)). Qed.
Lemma lem2324797 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2324798 : term180 = term56.
Proof. exact (MK_COMB (@lem2324797) (@lem2324796)). Qed.
Lemma lem2324799 : term179 = term56.
Proof. exact (TRANS (@lem2324794) (@lem2324798)). Qed.
Lemma lem2324801 (x : nat) : (term319 x) = term159.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2324802 : term316 = term159.
Proof. exact (@lem2324801 term57). Qed.
Lemma lem2324803 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2324804 : term320 = term321.
Proof. exact (MK_COMB (@lem2324803) (@lem2324802)). Qed.
Lemma lem2324805 : term318 = term315.
Proof. exact (MK_COMB (@lem2324804) (@lem2324799)). Qed.
Lemma lem2324806 : term317 = term315.
Proof. exact (TRANS (@lem2324791) (@lem2324805)). Qed.
Lemma lem2324807 : term316 = term315.
Proof. exact (TRANS (@lem2324790) (@lem2324806)). Qed.
Lemma lem2324809 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2324810 : term315 = term159.
Proof. exact (@lem2324809 term159). Qed.
Lemma lem2324811 : term316 = term159.
Proof. exact (TRANS (@lem2324807) (@lem2324810)). Qed.
Lemma lem2324812 (x : int) (y : int) : (term322 x y) = (term322 x y).
Proof. exact (eq_refl (term322 x y)). Qed.
Lemma lem2324813 (x : int) (y : int) : (term314 x y) = (term323 x y).
Proof. exact (MK_COMB (@lem2324812 x y) (@lem2324811)). Qed.
Lemma lem2324814 (x : int) (y : int) : (term323 x y) = (term155 x y).
Proof. exact (@lem1982723 (term155 x y)). Qed.
Lemma lem2324815 (x : int) (y : int) : (term314 x y) = (term155 x y).
Proof. exact (TRANS (@lem2324813 x y) (@lem2324814 x y)). Qed.
Lemma lem2324817 (x : int) (y : int) : (term313 x y) = (term155 x y).
Proof. exact (TRANS (@lem2324781 x y) (@lem2324815 x y)). Qed.
Lemma lem2324818 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2324819 (x : int) (y : int) : (term324 x y) = (term158 x y).
Proof. exact (MK_COMB (@lem2324818) (@lem2324817 x y)). Qed.
Lemma lem2324820 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2324821 (x : int) (y : int) : (term312 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem2324819 x y) (@lem2324820)). Qed.
Lemma lem2324822 (x : int) (y : int) : (term160 x y) = (term160 x y).
Proof. exact (TRANS (@lem2324763 x y) (@lem2324821 x y)). Qed.
Lemma lem2324823 (x : int) : (term325 x) = (term326 x).
Proof. exact (@lem1988291 (term327 x) term159). Qed.
Lemma lem2324824 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2324842 (x : int) : (term327 x) = (term328 x).
Proof. exact (@lem1982763 (real_of_int x) (term156 x) term166). Qed.
Lemma lem2324843 (x : int) : (term329 x) = (term330 x).
Proof. exact (@lem1982715 term166 (real_of_int x)). Qed.
Lemma lem2324845 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2324846 : term56 = term168.
Proof. exact (@lem2324845 term57). Qed.
Lemma lem2324848 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2324849 : term166 = term171.
Proof. exact (@lem2324848 term57). Qed.
Lemma lem2324850 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2324851 : term331 = term332.
Proof. exact (MK_COMB (@lem2324850) (@lem2324849)). Qed.
Lemma lem2324852 : term333 = term334.
Proof. exact (MK_COMB (@lem2324851) (@lem2324846)). Qed.
Lemma lem2324853 : term335.
Proof. exact (@lem1981473 term166 term56 term56 term56 term159 term56). Qed.
Lemma lem2324855 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2324856 : term337 = term338.
Proof. exact (@lem2324855 (NUMERAL 0) term57). Qed.
Lemma lem2324857 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2324858 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2324859 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2324858 h1) (fun h1 : term338 = True => @lem2324857)). Qed.
Lemma lem2324860 : term338 = True.
Proof. exact (EQ_MP (@lem2324859) (@lem2324857)). Qed.
Lemma lem2324861 : term337 = True.
Proof. exact (TRANS (@lem2324856) (@lem2324860)). Qed.
Lemma lem2324862 : True = term337.
Proof. exact (SYM (@lem2324861)). Qed.
Lemma lem2324863 : term337.
Proof. exact (EQ_MP (@lem2324862) (@lem0)). Qed.
Lemma lem2324864 : term340.
Proof. exact (@lem2324853 (@lem2324863)). Qed.
Lemma lem2324866 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2324867 : term337 = term338.
Proof. exact (@lem2324866 (NUMERAL 0) term57). Qed.
Lemma lem2324868 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2324869 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2324870 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2324869 h1) (fun h1 : term338 = True => @lem2324868)). Qed.
Lemma lem2324871 : term338 = True.
Proof. exact (EQ_MP (@lem2324870) (@lem2324868)). Qed.
Lemma lem2324872 : term337 = True.
Proof. exact (TRANS (@lem2324867) (@lem2324871)). Qed.
Lemma lem2324873 : True = term337.
Proof. exact (SYM (@lem2324872)). Qed.
Lemma lem2324874 : term337.
Proof. exact (EQ_MP (@lem2324873) (@lem0)). Qed.
Lemma lem2324875 : term341.
Proof. exact (@lem2324864 (@lem2324874)). Qed.
Lemma lem2324877 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2324878 : term337 = term338.
Proof. exact (@lem2324877 (NUMERAL 0) term57). Qed.
Lemma lem2324879 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2324880 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2324881 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2324880 h1) (fun h1 : term338 = True => @lem2324879)). Qed.
Lemma lem2324882 : term338 = True.
Proof. exact (EQ_MP (@lem2324881) (@lem2324879)). Qed.
Lemma lem2324883 : term337 = True.
Proof. exact (TRANS (@lem2324878) (@lem2324882)). Qed.
Lemma lem2324884 : True = term337.
Proof. exact (SYM (@lem2324883)). Qed.
Lemma lem2324885 : term337.
Proof. exact (EQ_MP (@lem2324884) (@lem0)). Qed.
Lemma lem2324886 : term342.
Proof. exact (@lem2324875 (@lem2324885)). Qed.
Lemma lem2324888 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2324889 : term179 = term180.
Proof. exact (@lem2324888 term57 term57). Qed.
Lemma lem2324890 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2324891 : term182 = term57.
Proof. exact (EQ_MP (@lem2324890) (@lem940073)). Qed.
Lemma lem2324892 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2324893 : term180 = term56.
Proof. exact (MK_COMB (@lem2324892) (@lem2324891)). Qed.
Lemma lem2324894 : term179 = term56.
Proof. exact (TRANS (@lem2324889) (@lem2324893)). Qed.
Lemma lem2324896 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2324897 : term174 = term185.
Proof. exact (@lem2324896 term57 term57). Qed.
Lemma lem2324898 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2324899 : term182 = term57.
Proof. exact (EQ_MP (@lem2324898) (@lem940073)). Qed.
Lemma lem2324900 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2324901 : term180 = term56.
Proof. exact (MK_COMB (@lem2324900) (@lem2324899)). Qed.
Lemma lem2324902 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2324903 : term185 = term166.
Proof. exact (MK_COMB (@lem2324902) (@lem2324901)). Qed.
Lemma lem2324904 : term174 = term166.
Proof. exact (TRANS (@lem2324897) (@lem2324903)). Qed.
Lemma lem2324905 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2324906 : term343 = term331.
Proof. exact (MK_COMB (@lem2324905) (@lem2324904)). Qed.
Lemma lem2324907 : term344 = term333.
Proof. exact (MK_COMB (@lem2324906) (@lem2324894)). Qed.
Lemma lem2324909 (m : nat) : (term345 m) = term159.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2324910 : term333 = term159.
Proof. exact (@lem2324909 term57). Qed.
Lemma lem2324911 : term344 = term159.
Proof. exact (TRANS (@lem2324907) (@lem2324910)). Qed.
Lemma lem2324912 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2324913 : term346 = term347.
Proof. exact (MK_COMB (@lem2324912) (@lem2324911)). Qed.
Lemma lem2324914 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2324915 : term348 = term349.
Proof. exact (MK_COMB (@lem2324913) (@lem2324914)). Qed.
Lemma lem2324917 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2324918 : term349 = term159.
Proof. exact (@lem2324917 term57). Qed.
Lemma lem2324919 : term348 = term159.
Proof. exact (TRANS (@lem2324915) (@lem2324918)). Qed.
Lemma lem2324921 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2324922 : term179 = term180.
Proof. exact (@lem2324921 term57 term57). Qed.
Lemma lem2324923 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2324924 : term182 = term57.
Proof. exact (EQ_MP (@lem2324923) (@lem940073)). Qed.
Lemma lem2324925 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2324926 : term180 = term56.
Proof. exact (MK_COMB (@lem2324925) (@lem2324924)). Qed.
Lemma lem2324927 : term179 = term56.
Proof. exact (TRANS (@lem2324922) (@lem2324926)). Qed.
Lemma lem2324928 : term347 = term347.
Proof. exact (eq_refl term347). Qed.
Lemma lem2324929 : term351 = term349.
Proof. exact (MK_COMB (@lem2324928) (@lem2324927)). Qed.
Lemma lem2324931 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2324932 : term349 = term159.
Proof. exact (@lem2324931 term57). Qed.
Lemma lem2324933 : term351 = term159.
Proof. exact (TRANS (@lem2324929) (@lem2324932)). Qed.
Lemma lem2324934 : term159 = term351.
Proof. exact (SYM (@lem2324933)). Qed.
Lemma lem2324935 : term348 = term351.
Proof. exact (TRANS (@lem2324919) (@lem2324934)). Qed.
Lemma lem2324936 : term334 = term315.
Proof. exact (@lem2324886 (@lem2324935)). Qed.
Lemma lem2324937 : term333 = term315.
Proof. exact (TRANS (@lem2324852) (@lem2324936)). Qed.
Lemma lem2324939 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2324940 : term315 = term159.
Proof. exact (@lem2324939 term159). Qed.
Lemma lem2324941 : term333 = term159.
Proof. exact (TRANS (@lem2324937) (@lem2324940)). Qed.
Lemma lem2324942 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2324943 : term352 = term347.
Proof. exact (MK_COMB (@lem2324942) (@lem2324941)). Qed.
Lemma lem2324944 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2324945 (x : int) : (term330 x) = (term353 x).
Proof. exact (MK_COMB (@lem2324943) (@lem2324944 x)). Qed.
Lemma lem2324946 (x : int) : (term329 x) = (term353 x).
Proof. exact (TRANS (@lem2324843 x) (@lem2324945 x)). Qed.
Lemma lem2324947 (x : int) : (term353 x) = term159.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2324948 (x : int) : (term329 x) = term159.
Proof. exact (TRANS (@lem2324946 x) (@lem2324947 x)). Qed.
Lemma lem2324949 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2324950 (x : int) : (term354 x) = term355.
Proof. exact (MK_COMB (@lem2324949) (@lem2324948 x)). Qed.
Lemma lem2324951 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2324952 (x : int) : (term328 x) = term356.
Proof. exact (MK_COMB (@lem2324950 x) (@lem2324951)). Qed.
Lemma lem2324953 (x : int) : (term327 x) = term356.
Proof. exact (TRANS (@lem2324842 x) (@lem2324952 x)). Qed.
Lemma lem2324954 : term356 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem2324956 (x : int) : (term327 x) = term166.
Proof. exact (TRANS (@lem2324953 x) (@lem2324954)). Qed.
Lemma lem2324957 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2324958 (x : int) : (term357 x) = term358.
Proof. exact (MK_COMB (@lem2324957) (@lem2324956 x)). Qed.
Lemma lem2324959 (x : int) : (term359 x) = term360.
Proof. exact (MK_COMB (@lem2324958 x) (@lem2324824)). Qed.
Lemma lem2324960 : term360 = term361.
Proof. exact (@lem1982792 term166 term159). Qed.
Lemma lem2324962 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2324963 : term159 = term315.
Proof. exact (@lem2324962 (NUMERAL 0)). Qed.
Lemma lem2324965 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2324966 : term166 = term171.
Proof. exact (@lem2324965 term57). Qed.
Lemma lem2324967 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2324968 : term172 = term173.
Proof. exact (MK_COMB (@lem2324967) (@lem2324966)). Qed.
Lemma lem2324969 : term316 = term317.
Proof. exact (MK_COMB (@lem2324968) (@lem2324963)). Qed.
Lemma lem2324970 : term317 = term318.
Proof. exact (@lem1981613 term166 term159 term56 term56). Qed.
Lemma lem2324972 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2324973 : term179 = term180.
Proof. exact (@lem2324972 term57 term57). Qed.
Lemma lem2324974 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2324975 : term182 = term57.
Proof. exact (EQ_MP (@lem2324974) (@lem940073)). Qed.
Lemma lem2324976 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2324977 : term180 = term56.
Proof. exact (MK_COMB (@lem2324976) (@lem2324975)). Qed.
Lemma lem2324978 : term179 = term56.
Proof. exact (TRANS (@lem2324973) (@lem2324977)). Qed.
Lemma lem2324980 (x : nat) : (term319 x) = term159.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2324981 : term316 = term159.
Proof. exact (@lem2324980 term57). Qed.
Lemma lem2324982 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2324983 : term320 = term321.
Proof. exact (MK_COMB (@lem2324982) (@lem2324981)). Qed.
Lemma lem2324984 : term318 = term315.
Proof. exact (MK_COMB (@lem2324983) (@lem2324978)). Qed.
Lemma lem2324985 : term317 = term315.
Proof. exact (TRANS (@lem2324970) (@lem2324984)). Qed.
Lemma lem2324986 : term316 = term315.
Proof. exact (TRANS (@lem2324969) (@lem2324985)). Qed.
Lemma lem2324988 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2324989 : term315 = term159.
Proof. exact (@lem2324988 term159). Qed.
Lemma lem2324990 : term316 = term159.
Proof. exact (TRANS (@lem2324986) (@lem2324989)). Qed.
Lemma lem2324991 : term331 = term331.
Proof. exact (eq_refl term331). Qed.
Lemma lem2324992 : term361 = term362.
Proof. exact (MK_COMB (@lem2324991) (@lem2324990)). Qed.
Lemma lem2324993 : term362 = term166.
Proof. exact (@lem1982723 term166). Qed.
Lemma lem2324994 : term361 = term166.
Proof. exact (TRANS (@lem2324992) (@lem2324993)). Qed.
Lemma lem2324995 : term360 = term166.
Proof. exact (TRANS (@lem2324960) (@lem2324994)). Qed.
Lemma lem2324996 (x : int) : (term359 x) = term166.
Proof. exact (TRANS (@lem2324959 x) (@lem2324995)). Qed.
Lemma lem2324997 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2324998 (x : int) : (term363 x) = term364.
Proof. exact (MK_COMB (@lem2324997) (@lem2324996 x)). Qed.
Lemma lem2324999 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2325000 (x : int) : (term326 x) = term365.
Proof. exact (MK_COMB (@lem2324998 x) (@lem2324999)). Qed.
Lemma lem2325001 (x : int) : (term325 x) = term365.
Proof. exact (TRANS (@lem2324823 x) (@lem2325000 x)). Qed.
Lemma lem2325002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2325003 (x : int) (y : int) : (term209 x y) = (term209 x y).
Proof. exact (MK_COMB (@lem2325002) (@lem2324822 x y)). Qed.
Lemma lem2325004 (x : int) (y : int) : (term303 y x) = (term366 x y).
Proof. exact (MK_COMB (@lem2325003 x y) (@lem2325001 x)). Qed.
Lemma lem2325005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2325006 (x : int) (y : int) : (term304 y x) = (term209 x y).
Proof. exact (MK_COMB (@lem2325005) (@lem2324762 x y)). Qed.
Lemma lem2325007 (x : int) (y : int) : (term306 y x) = (term367 x y).
Proof. exact (MK_COMB (@lem2325006 x y) (@lem2325004 x y)). Qed.
Lemma lem2325008 (x : int) (y : int) : (term368 x y) = (term369 x y).
Proof. exact (@lem1988289 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2325021 (x : int) (y : int) : (term153 x y) = (term154 x y).
Proof. exact (@lem1982792 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2325022 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2325023 (x : int) (y : int) : (term370 x y) = (term371 x y).
Proof. exact (MK_COMB (@lem2325022) (@lem2325021 x y)). Qed.
Lemma lem2325024 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2325025 (x : int) (y : int) : (term369 x y) = (term372 x y).
Proof. exact (MK_COMB (@lem2325023 x y) (@lem2325024)). Qed.
Lemma lem2325026 (x : int) (y : int) : (term368 x y) = (term372 x y).
Proof. exact (TRANS (@lem2325008 x y) (@lem2325025 x y)). Qed.
Lemma lem2325027 (x : int) (y : int) : (term221 x y) = (term373 x y).
Proof. exact (@lem1988291 (term218 x y) term159). Qed.
Lemma lem2325051 (x : int) (y : int) : (term374 x y) = (term375 x y).
Proof. exact (@lem1982792 (term218 x y) term159). Qed.
Lemma lem2325053 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2325054 : term159 = term315.
Proof. exact (@lem2325053 (NUMERAL 0)). Qed.
Lemma lem2325056 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2325057 : term166 = term171.
Proof. exact (@lem2325056 term57). Qed.
Lemma lem2325058 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2325059 : term172 = term173.
Proof. exact (MK_COMB (@lem2325058) (@lem2325057)). Qed.
Lemma lem2325060 : term316 = term317.
Proof. exact (MK_COMB (@lem2325059) (@lem2325054)). Qed.
Lemma lem2325061 : term317 = term318.
Proof. exact (@lem1981613 term166 term159 term56 term56). Qed.
Lemma lem2325063 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2325064 : term179 = term180.
Proof. exact (@lem2325063 term57 term57). Qed.
Lemma lem2325065 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2325066 : term182 = term57.
Proof. exact (EQ_MP (@lem2325065) (@lem940073)). Qed.
Lemma lem2325067 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2325068 : term180 = term56.
Proof. exact (MK_COMB (@lem2325067) (@lem2325066)). Qed.
Lemma lem2325069 : term179 = term56.
Proof. exact (TRANS (@lem2325064) (@lem2325068)). Qed.
Lemma lem2325071 (x : nat) : (term319 x) = term159.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2325072 : term316 = term159.
Proof. exact (@lem2325071 term57). Qed.
Lemma lem2325073 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2325074 : term320 = term321.
Proof. exact (MK_COMB (@lem2325073) (@lem2325072)). Qed.
Lemma lem2325075 : term318 = term315.
Proof. exact (MK_COMB (@lem2325074) (@lem2325069)). Qed.
Lemma lem2325076 : term317 = term315.
Proof. exact (TRANS (@lem2325061) (@lem2325075)). Qed.
Lemma lem2325077 : term316 = term315.
Proof. exact (TRANS (@lem2325060) (@lem2325076)). Qed.
Lemma lem2325079 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2325080 : term315 = term159.
Proof. exact (@lem2325079 term159). Qed.
Lemma lem2325081 : term316 = term159.
Proof. exact (TRANS (@lem2325077) (@lem2325080)). Qed.
Lemma lem2325082 (x : int) (y : int) : (term376 x y) = (term376 x y).
Proof. exact (eq_refl (term376 x y)). Qed.
Lemma lem2325083 (x : int) (y : int) : (term375 x y) = (term377 x y).
Proof. exact (MK_COMB (@lem2325082 x y) (@lem2325081)). Qed.
Lemma lem2325084 (x : int) (y : int) : (term377 x y) = (term218 x y).
Proof. exact (@lem1982723 (term218 x y)). Qed.
Lemma lem2325085 (x : int) (y : int) : (term375 x y) = (term218 x y).
Proof. exact (TRANS (@lem2325083 x y) (@lem2325084 x y)). Qed.
Lemma lem2325087 (x : int) (y : int) : (term374 x y) = (term218 x y).
Proof. exact (TRANS (@lem2325051 x y) (@lem2325085 x y)). Qed.
Lemma lem2325088 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2325089 (x : int) (y : int) : (term378 x y) = (term220 x y).
Proof. exact (MK_COMB (@lem2325088) (@lem2325087 x y)). Qed.
Lemma lem2325090 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2325091 (x : int) (y : int) : (term373 x y) = (term221 x y).
Proof. exact (MK_COMB (@lem2325089 x y) (@lem2325090)). Qed.
Lemma lem2325092 (x : int) (y : int) : (term221 x y) = (term221 x y).
Proof. exact (TRANS (@lem2325027 x y) (@lem2325091 x y)). Qed.
Lemma lem2325093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2325094 (x : int) (y : int) : (term209 x y) = (term209 x y).
Proof. exact (MK_COMB (@lem2325093) (@lem2324822 x y)). Qed.
Lemma lem2325095 (x : int) (y : int) : (term298 x y) = (term298 x y).
Proof. exact (MK_COMB (@lem2325094 x y) (@lem2325092 x y)). Qed.
Lemma lem2325096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2325097 (x : int) (y : int) : (term299 x y) = (term379 x y).
Proof. exact (MK_COMB (@lem2325096) (@lem2325026 x y)). Qed.
Lemma lem2325098 (x : int) (y : int) : (term301 x y) = (term380 x y).
Proof. exact (MK_COMB (@lem2325097 x y) (@lem2325095 x y)). Qed.
Lemma lem2325099 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2325100 (x : int) (y : int) : (term308 y x) = (term381 x y).
Proof. exact (MK_COMB (@lem2325099) (@lem2325007 x y)). Qed.
Lemma lem2325101 (x : int) (y : int) : (term309 x y) = (term382 x y).
Proof. exact (MK_COMB (@lem2325100 x y) (@lem2325098 x y)). Qed.
Lemma lem2325113 (x : int) (y : int) : (term294 x y) = (term382 x y).
Proof. exact (TRANS (@lem2324743 x y) (@lem2325101 x y)). Qed.
Lemma lem2325115 (x : real) (a : real) (y : real) (b : real) (r : real) : (term383 a x y b r) = (term384 x a y b r).
Proof. exact (proj1 (@lem1482699 x a b y (@el real) r)). Qed.
Lemma lem2325116 (x : int) (y : int) : (term206 x y) = (term385 x y).
Proof. exact (@lem2325115 (real_of_int x) (term156 x) (real_of_int y) term166 term159). Qed.
Lemma lem2325139 (x : int) (y : int) : (term386 x y) = (term386 x y).
Proof. exact (eq_refl (term386 x y)). Qed.
Lemma lem2325157 (x : int) : (term387 x) = (term388 x).
Proof. exact (@lem1982763 (term156 x) (real_of_int x) term166). Qed.
Lemma lem2325158 (x : int) : (term389 x) = (term330 x).
Proof. exact (@lem1982713 term166 (real_of_int x)). Qed.
Lemma lem2325160 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2325161 : term56 = term168.
Proof. exact (@lem2325160 term57). Qed.
Lemma lem2325163 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2325164 : term166 = term171.
Proof. exact (@lem2325163 term57). Qed.
Lemma lem2325165 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2325166 : term331 = term332.
Proof. exact (MK_COMB (@lem2325165) (@lem2325164)). Qed.
Lemma lem2325167 : term333 = term334.
Proof. exact (MK_COMB (@lem2325166) (@lem2325161)). Qed.
Lemma lem2325168 : term335.
Proof. exact (@lem1981473 term166 term56 term56 term56 term159 term56). Qed.
Lemma lem2325170 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325171 : term337 = term338.
Proof. exact (@lem2325170 (NUMERAL 0) term57). Qed.
Lemma lem2325172 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325173 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325174 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325173 h1) (fun h1 : term338 = True => @lem2325172)). Qed.
Lemma lem2325175 : term338 = True.
Proof. exact (EQ_MP (@lem2325174) (@lem2325172)). Qed.
Lemma lem2325176 : term337 = True.
Proof. exact (TRANS (@lem2325171) (@lem2325175)). Qed.
Lemma lem2325177 : True = term337.
Proof. exact (SYM (@lem2325176)). Qed.
Lemma lem2325178 : term337.
Proof. exact (EQ_MP (@lem2325177) (@lem0)). Qed.
Lemma lem2325179 : term340.
Proof. exact (@lem2325168 (@lem2325178)). Qed.
Lemma lem2325181 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325182 : term337 = term338.
Proof. exact (@lem2325181 (NUMERAL 0) term57). Qed.
Lemma lem2325183 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325184 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325185 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325184 h1) (fun h1 : term338 = True => @lem2325183)). Qed.
Lemma lem2325186 : term338 = True.
Proof. exact (EQ_MP (@lem2325185) (@lem2325183)). Qed.
Lemma lem2325187 : term337 = True.
Proof. exact (TRANS (@lem2325182) (@lem2325186)). Qed.
Lemma lem2325188 : True = term337.
Proof. exact (SYM (@lem2325187)). Qed.
Lemma lem2325189 : term337.
Proof. exact (EQ_MP (@lem2325188) (@lem0)). Qed.
Lemma lem2325190 : term341.
Proof. exact (@lem2325179 (@lem2325189)). Qed.
Lemma lem2325192 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325193 : term337 = term338.
Proof. exact (@lem2325192 (NUMERAL 0) term57). Qed.
Lemma lem2325194 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325195 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325196 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325195 h1) (fun h1 : term338 = True => @lem2325194)). Qed.
Lemma lem2325197 : term338 = True.
Proof. exact (EQ_MP (@lem2325196) (@lem2325194)). Qed.
Lemma lem2325198 : term337 = True.
Proof. exact (TRANS (@lem2325193) (@lem2325197)). Qed.
Lemma lem2325199 : True = term337.
Proof. exact (SYM (@lem2325198)). Qed.
Lemma lem2325200 : term337.
Proof. exact (EQ_MP (@lem2325199) (@lem0)). Qed.
Lemma lem2325201 : term342.
Proof. exact (@lem2325190 (@lem2325200)). Qed.
Lemma lem2325203 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2325204 : term179 = term180.
Proof. exact (@lem2325203 term57 term57). Qed.
Lemma lem2325205 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2325206 : term182 = term57.
Proof. exact (EQ_MP (@lem2325205) (@lem940073)). Qed.
Lemma lem2325207 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2325208 : term180 = term56.
Proof. exact (MK_COMB (@lem2325207) (@lem2325206)). Qed.
Lemma lem2325209 : term179 = term56.
Proof. exact (TRANS (@lem2325204) (@lem2325208)). Qed.
Lemma lem2325211 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2325212 : term174 = term185.
Proof. exact (@lem2325211 term57 term57). Qed.
Lemma lem2325213 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2325214 : term182 = term57.
Proof. exact (EQ_MP (@lem2325213) (@lem940073)). Qed.
Lemma lem2325215 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2325216 : term180 = term56.
Proof. exact (MK_COMB (@lem2325215) (@lem2325214)). Qed.
Lemma lem2325217 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2325218 : term185 = term166.
Proof. exact (MK_COMB (@lem2325217) (@lem2325216)). Qed.
Lemma lem2325219 : term174 = term166.
Proof. exact (TRANS (@lem2325212) (@lem2325218)). Qed.
Lemma lem2325220 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2325221 : term343 = term331.
Proof. exact (MK_COMB (@lem2325220) (@lem2325219)). Qed.
Lemma lem2325222 : term344 = term333.
Proof. exact (MK_COMB (@lem2325221) (@lem2325209)). Qed.
Lemma lem2325224 (m : nat) : (term345 m) = term159.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2325225 : term333 = term159.
Proof. exact (@lem2325224 term57). Qed.
Lemma lem2325226 : term344 = term159.
Proof. exact (TRANS (@lem2325222) (@lem2325225)). Qed.
Lemma lem2325227 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2325228 : term346 = term347.
Proof. exact (MK_COMB (@lem2325227) (@lem2325226)). Qed.
Lemma lem2325229 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2325230 : term348 = term349.
Proof. exact (MK_COMB (@lem2325228) (@lem2325229)). Qed.
Lemma lem2325232 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2325233 : term349 = term159.
Proof. exact (@lem2325232 term57). Qed.
Lemma lem2325234 : term348 = term159.
Proof. exact (TRANS (@lem2325230) (@lem2325233)). Qed.
Lemma lem2325236 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2325237 : term179 = term180.
Proof. exact (@lem2325236 term57 term57). Qed.
Lemma lem2325238 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2325239 : term182 = term57.
Proof. exact (EQ_MP (@lem2325238) (@lem940073)). Qed.
Lemma lem2325240 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2325241 : term180 = term56.
Proof. exact (MK_COMB (@lem2325240) (@lem2325239)). Qed.
Lemma lem2325242 : term179 = term56.
Proof. exact (TRANS (@lem2325237) (@lem2325241)). Qed.
Lemma lem2325243 : term347 = term347.
Proof. exact (eq_refl term347). Qed.
Lemma lem2325244 : term351 = term349.
Proof. exact (MK_COMB (@lem2325243) (@lem2325242)). Qed.
Lemma lem2325246 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2325247 : term349 = term159.
Proof. exact (@lem2325246 term57). Qed.
Lemma lem2325248 : term351 = term159.
Proof. exact (TRANS (@lem2325244) (@lem2325247)). Qed.
Lemma lem2325249 : term159 = term351.
Proof. exact (SYM (@lem2325248)). Qed.
Lemma lem2325250 : term348 = term351.
Proof. exact (TRANS (@lem2325234) (@lem2325249)). Qed.
Lemma lem2325251 : term334 = term315.
Proof. exact (@lem2325201 (@lem2325250)). Qed.
Lemma lem2325252 : term333 = term315.
Proof. exact (TRANS (@lem2325167) (@lem2325251)). Qed.
Lemma lem2325254 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2325255 : term315 = term159.
Proof. exact (@lem2325254 term159). Qed.
Lemma lem2325256 : term333 = term159.
Proof. exact (TRANS (@lem2325252) (@lem2325255)). Qed.
Lemma lem2325257 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2325258 : term352 = term347.
Proof. exact (MK_COMB (@lem2325257) (@lem2325256)). Qed.
Lemma lem2325259 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2325260 (x : int) : (term330 x) = (term353 x).
Proof. exact (MK_COMB (@lem2325258) (@lem2325259 x)). Qed.
Lemma lem2325261 (x : int) : (term389 x) = (term353 x).
Proof. exact (TRANS (@lem2325158 x) (@lem2325260 x)). Qed.
Lemma lem2325262 (x : int) : (term353 x) = term159.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2325263 (x : int) : (term389 x) = term159.
Proof. exact (TRANS (@lem2325261 x) (@lem2325262 x)). Qed.
Lemma lem2325264 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2325265 (x : int) : (term390 x) = term355.
Proof. exact (MK_COMB (@lem2325264) (@lem2325263 x)). Qed.
Lemma lem2325266 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2325267 (x : int) : (term388 x) = term356.
Proof. exact (MK_COMB (@lem2325265 x) (@lem2325266)). Qed.
Lemma lem2325268 (x : int) : (term387 x) = term356.
Proof. exact (TRANS (@lem2325157 x) (@lem2325267 x)). Qed.
Lemma lem2325269 : term356 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem2325271 (x : int) : (term387 x) = term166.
Proof. exact (TRANS (@lem2325268 x) (@lem2325269)). Qed.
Lemma lem2325272 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2325273 (x : int) : (term391 x) = term364.
Proof. exact (MK_COMB (@lem2325272) (@lem2325271 x)). Qed.
Lemma lem2325274 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2325275 (x : int) : (term392 x) = term365.
Proof. exact (MK_COMB (@lem2325273 x) (@lem2325274)). Qed.
Lemma lem2325276 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2325277 (x : int) : (term393 x) = term394.
Proof. exact (MK_COMB (@lem2325276) (@lem2325275 x)). Qed.
Lemma lem2325278 (x : int) (y : int) : (term385 x y) = (term395 x y).
Proof. exact (MK_COMB (@lem2325277 x) (@lem2325139 x y)). Qed.
Lemma lem2325279 (x : int) (y : int) : (term206 x y) = (term395 x y).
Proof. exact (TRANS (@lem2325116 x y) (@lem2325278 x y)). Qed.
Lemma lem2325280 (x : int) (y : int) : (term209 x y) = (term209 x y).
Proof. exact (eq_refl (term209 x y)). Qed.
Lemma lem2325283 (x : int) (y : int) : (term396 x y) = (term397 x y).
Proof. exact (MK_COMB (@lem2325280 x y) (@lem2325279 x y)). Qed.
Lemma lem2325284 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2325285 (x : int) (y : int) : (term398 x y) = (term399 x y).
Proof. exact (MK_COMB (@lem2325284) (@lem2325113 x y)). Qed.
Lemma lem2325286 (x : int) (y : int) : (term286 x y) = (term400 x y).
Proof. exact (MK_COMB (@lem2325285 x y) (@lem2325283 x y)). Qed.
Lemma lem2325288 (x : int) (y : int) : (term401 x y) = (term402 x y).
Proof. exact (eq_refl (term401 x y)). Qed.
Lemma lem2325289 (x : int) (y : int) : (term402 x y) = (term401 x y).
Proof. exact (SYM (@lem2325288 x y)). Qed.
Lemma lem2325290 (x : int) (y : int) : (term401 x y) = (term403 x y).
Proof. exact (@lem1483429 (real_of_int x) (term404 x y) (real_of_int y)). Qed.
Lemma lem2325291 (x : int) (y : int) : (term402 x y) = (term403 x y).
Proof. exact (TRANS (@lem2325289 x y) (@lem2325290 x y)). Qed.
Lemma lem2325292 (x : int) (y : int) : (term405 x y) = (term406 x y).
Proof. exact (eq_refl (term405 x y)). Qed.
Lemma lem2325293 (x : int) (y : int) : (term299 x y) = (term299 x y).
Proof. exact (eq_refl (term299 x y)). Qed.
Lemma lem2325294 (x : int) (y : int) : (term407 x y) = (term408 x y).
Proof. exact (MK_COMB (@lem2325293 x y) (@lem2325292 x y)). Qed.
Lemma lem2325295 (y : int) (x : int) : (term409 y x) = (term410 y x).
Proof. exact (eq_refl (term409 y x)). Qed.
Lemma lem2325296 (y : int) (x : int) : (term304 y x) = (term304 y x).
Proof. exact (eq_refl (term304 y x)). Qed.
Lemma lem2325297 (y : int) (x : int) : (term411 y x) = (term412 y x).
Proof. exact (MK_COMB (@lem2325296 y x) (@lem2325295 y x)). Qed.
Lemma lem2325298 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2325299 (y : int) (x : int) : (term413 y x) = (term414 y x).
Proof. exact (MK_COMB (@lem2325298) (@lem2325297 y x)). Qed.
Lemma lem2325300 (x : int) (y : int) : (term403 x y) = (term415 x y).
Proof. exact (MK_COMB (@lem2325299 y x) (@lem2325294 x y)). Qed.
Lemma lem2325301 (x : int) (y : int) : (term416 x y) = (term416 x y).
Proof. exact (eq_refl (term416 x y)). Qed.
Lemma lem2325302 (x : int) (y : int) : ((term402 x y) = (term403 x y)) = ((term402 x y) = (term415 x y)).
Proof. exact (MK_COMB (@lem2325301 x y) (@lem2325300 x y)). Qed.
Lemma lem2325303 (x : int) (y : int) : (term402 x y) = (term415 x y).
Proof. exact (EQ_MP (@lem2325302 x y) (@lem2325291 x y)). Qed.
Lemma lem2325304 (y : int) (x : int) : (term221 y x) = (term373 y x).
Proof. exact (@lem1988291 (term218 y x) term159). Qed.
Lemma lem2325305 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2325328 (x : int) (y : int) : (term218 y x) = (term417 x y).
Proof. exact (@lem1982757 (term156 x) (real_of_int y) term166). Qed.
Lemma lem2325329 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2325330 (x : int) (y : int) : (term418 y x) = (term419 x y).
Proof. exact (MK_COMB (@lem2325329) (@lem2325328 x y)). Qed.
Lemma lem2325331 (x : int) (y : int) : (term374 y x) = (term420 x y).
Proof. exact (MK_COMB (@lem2325330 x y) (@lem2325305)). Qed.
Lemma lem2325332 (x : int) (y : int) : (term420 x y) = (term421 x y).
Proof. exact (@lem1982792 (term417 x y) term159). Qed.
Lemma lem2325334 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2325335 : term159 = term315.
Proof. exact (@lem2325334 (NUMERAL 0)). Qed.
Lemma lem2325337 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2325338 : term166 = term171.
Proof. exact (@lem2325337 term57). Qed.
Lemma lem2325339 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2325340 : term172 = term173.
Proof. exact (MK_COMB (@lem2325339) (@lem2325338)). Qed.
Lemma lem2325341 : term316 = term317.
Proof. exact (MK_COMB (@lem2325340) (@lem2325335)). Qed.
Lemma lem2325342 : term317 = term318.
Proof. exact (@lem1981613 term166 term159 term56 term56). Qed.
Lemma lem2325344 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2325345 : term179 = term180.
Proof. exact (@lem2325344 term57 term57). Qed.
Lemma lem2325346 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2325347 : term182 = term57.
Proof. exact (EQ_MP (@lem2325346) (@lem940073)). Qed.
Lemma lem2325348 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2325349 : term180 = term56.
Proof. exact (MK_COMB (@lem2325348) (@lem2325347)). Qed.
Lemma lem2325350 : term179 = term56.
Proof. exact (TRANS (@lem2325345) (@lem2325349)). Qed.
Lemma lem2325352 (x : nat) : (term319 x) = term159.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2325353 : term316 = term159.
Proof. exact (@lem2325352 term57). Qed.
Lemma lem2325354 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2325355 : term320 = term321.
Proof. exact (MK_COMB (@lem2325354) (@lem2325353)). Qed.
Lemma lem2325356 : term318 = term315.
Proof. exact (MK_COMB (@lem2325355) (@lem2325350)). Qed.
Lemma lem2325357 : term317 = term315.
Proof. exact (TRANS (@lem2325342) (@lem2325356)). Qed.
Lemma lem2325358 : term316 = term315.
Proof. exact (TRANS (@lem2325341) (@lem2325357)). Qed.
Lemma lem2325360 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2325361 : term315 = term159.
Proof. exact (@lem2325360 term159). Qed.
Lemma lem2325362 : term316 = term159.
Proof. exact (TRANS (@lem2325358) (@lem2325361)). Qed.
Lemma lem2325363 (x : int) (y : int) : (term422 x y) = (term422 x y).
Proof. exact (eq_refl (term422 x y)). Qed.
Lemma lem2325364 (x : int) (y : int) : (term421 x y) = (term423 x y).
Proof. exact (MK_COMB (@lem2325363 x y) (@lem2325362)). Qed.
Lemma lem2325365 (x : int) (y : int) : (term423 x y) = (term417 x y).
Proof. exact (@lem1982723 (term417 x y)). Qed.
Lemma lem2325366 (x : int) (y : int) : (term421 x y) = (term417 x y).
Proof. exact (TRANS (@lem2325364 x y) (@lem2325365 x y)). Qed.
Lemma lem2325367 (x : int) (y : int) : (term420 x y) = (term417 x y).
Proof. exact (TRANS (@lem2325332 x y) (@lem2325366 x y)). Qed.
Lemma lem2325368 (x : int) (y : int) : (term374 y x) = (term417 x y).
Proof. exact (TRANS (@lem2325331 x y) (@lem2325367 x y)). Qed.
Lemma lem2325369 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2325370 (x : int) (y : int) : (term378 y x) = (term424 x y).
Proof. exact (MK_COMB (@lem2325369) (@lem2325368 x y)). Qed.
Lemma lem2325371 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2325372 (x : int) (y : int) : (term373 y x) = (term386 x y).
Proof. exact (MK_COMB (@lem2325370 x y) (@lem2325371)). Qed.
Lemma lem2325373 (x : int) (y : int) : (term221 y x) = (term386 x y).
Proof. exact (TRANS (@lem2325304 y x) (@lem2325372 x y)). Qed.
Lemma lem2325374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2325375 (x : int) (y : int) : (term239 x y) = (term239 x y).
Proof. exact (MK_COMB (@lem2325374) (@lem2325092 x y)). Qed.
Lemma lem2325376 (x : int) (y : int) : (term410 y x) = (term425 x y).
Proof. exact (MK_COMB (@lem2325375 x y) (@lem2325373 x y)). Qed.
Lemma lem2325377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2325378 (x : int) (y : int) : (term304 y x) = (term209 x y).
Proof. exact (MK_COMB (@lem2325377) (@lem2324762 x y)). Qed.
Lemma lem2325379 (x : int) (y : int) : (term412 y x) = (term426 x y).
Proof. exact (MK_COMB (@lem2325378 x y) (@lem2325376 x y)). Qed.
Lemma lem2325380 (y : int) : (term325 y) = (term326 y).
Proof. exact (@lem1988291 (term327 y) term159). Qed.
Lemma lem2325381 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2325399 (y : int) : (term327 y) = (term328 y).
Proof. exact (@lem1982763 (real_of_int y) (term156 y) term166). Qed.
Lemma lem2325400 (y : int) : (term329 y) = (term330 y).
Proof. exact (@lem1982715 term166 (real_of_int y)). Qed.
Lemma lem2325402 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2325403 : term56 = term168.
Proof. exact (@lem2325402 term57). Qed.
Lemma lem2325405 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2325406 : term166 = term171.
Proof. exact (@lem2325405 term57). Qed.
Lemma lem2325407 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2325408 : term331 = term332.
Proof. exact (MK_COMB (@lem2325407) (@lem2325406)). Qed.
Lemma lem2325409 : term333 = term334.
Proof. exact (MK_COMB (@lem2325408) (@lem2325403)). Qed.
Lemma lem2325410 : term335.
Proof. exact (@lem1981473 term166 term56 term56 term56 term159 term56). Qed.
Lemma lem2325412 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325413 : term337 = term338.
Proof. exact (@lem2325412 (NUMERAL 0) term57). Qed.
Lemma lem2325414 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325415 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325416 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325415 h1) (fun h1 : term338 = True => @lem2325414)). Qed.
Lemma lem2325417 : term338 = True.
Proof. exact (EQ_MP (@lem2325416) (@lem2325414)). Qed.
Lemma lem2325418 : term337 = True.
Proof. exact (TRANS (@lem2325413) (@lem2325417)). Qed.
Lemma lem2325419 : True = term337.
Proof. exact (SYM (@lem2325418)). Qed.
Lemma lem2325420 : term337.
Proof. exact (EQ_MP (@lem2325419) (@lem0)). Qed.
Lemma lem2325421 : term340.
Proof. exact (@lem2325410 (@lem2325420)). Qed.
Lemma lem2325423 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325424 : term337 = term338.
Proof. exact (@lem2325423 (NUMERAL 0) term57). Qed.
Lemma lem2325425 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325426 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325427 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325426 h1) (fun h1 : term338 = True => @lem2325425)). Qed.
Lemma lem2325428 : term338 = True.
Proof. exact (EQ_MP (@lem2325427) (@lem2325425)). Qed.
Lemma lem2325429 : term337 = True.
Proof. exact (TRANS (@lem2325424) (@lem2325428)). Qed.
Lemma lem2325430 : True = term337.
Proof. exact (SYM (@lem2325429)). Qed.
Lemma lem2325431 : term337.
Proof. exact (EQ_MP (@lem2325430) (@lem0)). Qed.
Lemma lem2325432 : term341.
Proof. exact (@lem2325421 (@lem2325431)). Qed.
Lemma lem2325434 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325435 : term337 = term338.
Proof. exact (@lem2325434 (NUMERAL 0) term57). Qed.
Lemma lem2325436 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325437 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325438 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325437 h1) (fun h1 : term338 = True => @lem2325436)). Qed.
Lemma lem2325439 : term338 = True.
Proof. exact (EQ_MP (@lem2325438) (@lem2325436)). Qed.
Lemma lem2325440 : term337 = True.
Proof. exact (TRANS (@lem2325435) (@lem2325439)). Qed.
Lemma lem2325441 : True = term337.
Proof. exact (SYM (@lem2325440)). Qed.
Lemma lem2325442 : term337.
Proof. exact (EQ_MP (@lem2325441) (@lem0)). Qed.
Lemma lem2325443 : term342.
Proof. exact (@lem2325432 (@lem2325442)). Qed.
Lemma lem2325445 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2325446 : term179 = term180.
Proof. exact (@lem2325445 term57 term57). Qed.
Lemma lem2325447 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2325448 : term182 = term57.
Proof. exact (EQ_MP (@lem2325447) (@lem940073)). Qed.
Lemma lem2325449 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2325450 : term180 = term56.
Proof. exact (MK_COMB (@lem2325449) (@lem2325448)). Qed.
Lemma lem2325451 : term179 = term56.
Proof. exact (TRANS (@lem2325446) (@lem2325450)). Qed.
Lemma lem2325453 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2325454 : term174 = term185.
Proof. exact (@lem2325453 term57 term57). Qed.
Lemma lem2325455 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2325456 : term182 = term57.
Proof. exact (EQ_MP (@lem2325455) (@lem940073)). Qed.
Lemma lem2325457 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2325458 : term180 = term56.
Proof. exact (MK_COMB (@lem2325457) (@lem2325456)). Qed.
Lemma lem2325459 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2325460 : term185 = term166.
Proof. exact (MK_COMB (@lem2325459) (@lem2325458)). Qed.
Lemma lem2325461 : term174 = term166.
Proof. exact (TRANS (@lem2325454) (@lem2325460)). Qed.
Lemma lem2325462 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2325463 : term343 = term331.
Proof. exact (MK_COMB (@lem2325462) (@lem2325461)). Qed.
Lemma lem2325464 : term344 = term333.
Proof. exact (MK_COMB (@lem2325463) (@lem2325451)). Qed.
Lemma lem2325466 (m : nat) : (term345 m) = term159.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2325467 : term333 = term159.
Proof. exact (@lem2325466 term57). Qed.
Lemma lem2325468 : term344 = term159.
Proof. exact (TRANS (@lem2325464) (@lem2325467)). Qed.
Lemma lem2325469 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2325470 : term346 = term347.
Proof. exact (MK_COMB (@lem2325469) (@lem2325468)). Qed.
Lemma lem2325471 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2325472 : term348 = term349.
Proof. exact (MK_COMB (@lem2325470) (@lem2325471)). Qed.
Lemma lem2325474 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2325475 : term349 = term159.
Proof. exact (@lem2325474 term57). Qed.
Lemma lem2325476 : term348 = term159.
Proof. exact (TRANS (@lem2325472) (@lem2325475)). Qed.
Lemma lem2325478 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2325479 : term179 = term180.
Proof. exact (@lem2325478 term57 term57). Qed.
Lemma lem2325480 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2325481 : term182 = term57.
Proof. exact (EQ_MP (@lem2325480) (@lem940073)). Qed.
Lemma lem2325482 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2325483 : term180 = term56.
Proof. exact (MK_COMB (@lem2325482) (@lem2325481)). Qed.
Lemma lem2325484 : term179 = term56.
Proof. exact (TRANS (@lem2325479) (@lem2325483)). Qed.
Lemma lem2325485 : term347 = term347.
Proof. exact (eq_refl term347). Qed.
Lemma lem2325486 : term351 = term349.
Proof. exact (MK_COMB (@lem2325485) (@lem2325484)). Qed.
Lemma lem2325488 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2325489 : term349 = term159.
Proof. exact (@lem2325488 term57). Qed.
Lemma lem2325490 : term351 = term159.
Proof. exact (TRANS (@lem2325486) (@lem2325489)). Qed.
Lemma lem2325491 : term159 = term351.
Proof. exact (SYM (@lem2325490)). Qed.
Lemma lem2325492 : term348 = term351.
Proof. exact (TRANS (@lem2325476) (@lem2325491)). Qed.
Lemma lem2325493 : term334 = term315.
Proof. exact (@lem2325443 (@lem2325492)). Qed.
Lemma lem2325494 : term333 = term315.
Proof. exact (TRANS (@lem2325409) (@lem2325493)). Qed.
Lemma lem2325496 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2325497 : term315 = term159.
Proof. exact (@lem2325496 term159). Qed.
Lemma lem2325498 : term333 = term159.
Proof. exact (TRANS (@lem2325494) (@lem2325497)). Qed.
Lemma lem2325499 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2325500 : term352 = term347.
Proof. exact (MK_COMB (@lem2325499) (@lem2325498)). Qed.
Lemma lem2325501 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2325502 (y : int) : (term330 y) = (term353 y).
Proof. exact (MK_COMB (@lem2325500) (@lem2325501 y)). Qed.
Lemma lem2325503 (y : int) : (term329 y) = (term353 y).
Proof. exact (TRANS (@lem2325400 y) (@lem2325502 y)). Qed.
Lemma lem2325504 (y : int) : (term353 y) = term159.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2325505 (y : int) : (term329 y) = term159.
Proof. exact (TRANS (@lem2325503 y) (@lem2325504 y)). Qed.
Lemma lem2325506 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2325507 (y : int) : (term354 y) = term355.
Proof. exact (MK_COMB (@lem2325506) (@lem2325505 y)). Qed.
Lemma lem2325508 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2325509 (y : int) : (term328 y) = term356.
Proof. exact (MK_COMB (@lem2325507 y) (@lem2325508)). Qed.
Lemma lem2325510 (y : int) : (term327 y) = term356.
Proof. exact (TRANS (@lem2325399 y) (@lem2325509 y)). Qed.
Lemma lem2325511 : term356 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem2325513 (y : int) : (term327 y) = term166.
Proof. exact (TRANS (@lem2325510 y) (@lem2325511)). Qed.
Lemma lem2325514 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2325515 (y : int) : (term357 y) = term358.
Proof. exact (MK_COMB (@lem2325514) (@lem2325513 y)). Qed.
Lemma lem2325516 (y : int) : (term359 y) = term360.
Proof. exact (MK_COMB (@lem2325515 y) (@lem2325381)). Qed.
Lemma lem2325517 : term360 = term361.
Proof. exact (@lem1982792 term166 term159). Qed.
Lemma lem2325519 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2325520 : term159 = term315.
Proof. exact (@lem2325519 (NUMERAL 0)). Qed.
Lemma lem2325522 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2325523 : term166 = term171.
Proof. exact (@lem2325522 term57). Qed.
Lemma lem2325524 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2325525 : term172 = term173.
Proof. exact (MK_COMB (@lem2325524) (@lem2325523)). Qed.
Lemma lem2325526 : term316 = term317.
Proof. exact (MK_COMB (@lem2325525) (@lem2325520)). Qed.
Lemma lem2325527 : term317 = term318.
Proof. exact (@lem1981613 term166 term159 term56 term56). Qed.
Lemma lem2325529 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2325530 : term179 = term180.
Proof. exact (@lem2325529 term57 term57). Qed.
Lemma lem2325531 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2325532 : term182 = term57.
Proof. exact (EQ_MP (@lem2325531) (@lem940073)). Qed.
Lemma lem2325533 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2325534 : term180 = term56.
Proof. exact (MK_COMB (@lem2325533) (@lem2325532)). Qed.
Lemma lem2325535 : term179 = term56.
Proof. exact (TRANS (@lem2325530) (@lem2325534)). Qed.
Lemma lem2325537 (x : nat) : (term319 x) = term159.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2325538 : term316 = term159.
Proof. exact (@lem2325537 term57). Qed.
Lemma lem2325539 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2325540 : term320 = term321.
Proof. exact (MK_COMB (@lem2325539) (@lem2325538)). Qed.
Lemma lem2325541 : term318 = term315.
Proof. exact (MK_COMB (@lem2325540) (@lem2325535)). Qed.
Lemma lem2325542 : term317 = term315.
Proof. exact (TRANS (@lem2325527) (@lem2325541)). Qed.
Lemma lem2325543 : term316 = term315.
Proof. exact (TRANS (@lem2325526) (@lem2325542)). Qed.
Lemma lem2325545 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2325546 : term315 = term159.
Proof. exact (@lem2325545 term159). Qed.
Lemma lem2325547 : term316 = term159.
Proof. exact (TRANS (@lem2325543) (@lem2325546)). Qed.
Lemma lem2325548 : term331 = term331.
Proof. exact (eq_refl term331). Qed.
Lemma lem2325549 : term361 = term362.
Proof. exact (MK_COMB (@lem2325548) (@lem2325547)). Qed.
Lemma lem2325550 : term362 = term166.
Proof. exact (@lem1982723 term166). Qed.
Lemma lem2325551 : term361 = term166.
Proof. exact (TRANS (@lem2325549) (@lem2325550)). Qed.
Lemma lem2325552 : term360 = term166.
Proof. exact (TRANS (@lem2325517) (@lem2325551)). Qed.
Lemma lem2325553 (y : int) : (term359 y) = term166.
Proof. exact (TRANS (@lem2325516 y) (@lem2325552)). Qed.
Lemma lem2325554 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2325555 (y : int) : (term363 y) = term364.
Proof. exact (MK_COMB (@lem2325554) (@lem2325553 y)). Qed.
Lemma lem2325556 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2325557 (y : int) : (term326 y) = term365.
Proof. exact (MK_COMB (@lem2325555 y) (@lem2325556)). Qed.
Lemma lem2325558 (y : int) : (term325 y) = term365.
Proof. exact (TRANS (@lem2325380 y) (@lem2325557 y)). Qed.
Lemma lem2325559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2325560 (x : int) (y : int) : (term239 x y) = (term239 x y).
Proof. exact (MK_COMB (@lem2325559) (@lem2325092 x y)). Qed.
Lemma lem2325561 (x : int) (y : int) : (term406 x y) = (term427 x y).
Proof. exact (MK_COMB (@lem2325560 x y) (@lem2325558 y)). Qed.
Lemma lem2325562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2325563 (x : int) (y : int) : (term299 x y) = (term379 x y).
Proof. exact (MK_COMB (@lem2325562) (@lem2325026 x y)). Qed.
Lemma lem2325564 (x : int) (y : int) : (term408 x y) = (term428 x y).
Proof. exact (MK_COMB (@lem2325563 x y) (@lem2325561 x y)). Qed.
Lemma lem2325565 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2325566 (x : int) (y : int) : (term414 y x) = (term429 x y).
Proof. exact (MK_COMB (@lem2325565) (@lem2325379 x y)). Qed.
Lemma lem2325567 (x : int) (y : int) : (term415 x y) = (term430 x y).
Proof. exact (MK_COMB (@lem2325566 x y) (@lem2325564 x y)). Qed.
Lemma lem2325579 (x : int) (y : int) : (term402 x y) = (term430 x y).
Proof. exact (TRANS (@lem2325303 x y) (@lem2325567 x y)). Qed.
Lemma lem2325581 (x : real) (a : real) (y : real) (b : real) (r : real) : (term383 a x y b r) = (term384 x a y b r).
Proof. exact (proj1 (@lem1482699 x a b y (@el real) r)). Qed.
Lemma lem2325582 (x : int) (y : int) : (term236 x y) = (term431 x y).
Proof. exact (@lem2325581 (real_of_int x) (term156 y) (real_of_int y) term166 term159). Qed.
Lemma lem2325600 (y : int) : (term387 y) = (term388 y).
Proof. exact (@lem1982763 (term156 y) (real_of_int y) term166). Qed.
Lemma lem2325601 (y : int) : (term389 y) = (term330 y).
Proof. exact (@lem1982713 term166 (real_of_int y)). Qed.
Lemma lem2325603 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2325604 : term56 = term168.
Proof. exact (@lem2325603 term57). Qed.
Lemma lem2325606 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2325607 : term166 = term171.
Proof. exact (@lem2325606 term57). Qed.
Lemma lem2325608 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2325609 : term331 = term332.
Proof. exact (MK_COMB (@lem2325608) (@lem2325607)). Qed.
Lemma lem2325610 : term333 = term334.
Proof. exact (MK_COMB (@lem2325609) (@lem2325604)). Qed.
Lemma lem2325611 : term335.
Proof. exact (@lem1981473 term166 term56 term56 term56 term159 term56). Qed.
Lemma lem2325613 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325614 : term337 = term338.
Proof. exact (@lem2325613 (NUMERAL 0) term57). Qed.
Lemma lem2325615 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325616 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325617 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325616 h1) (fun h1 : term338 = True => @lem2325615)). Qed.
Lemma lem2325618 : term338 = True.
Proof. exact (EQ_MP (@lem2325617) (@lem2325615)). Qed.
Lemma lem2325619 : term337 = True.
Proof. exact (TRANS (@lem2325614) (@lem2325618)). Qed.
Lemma lem2325620 : True = term337.
Proof. exact (SYM (@lem2325619)). Qed.
Lemma lem2325621 : term337.
Proof. exact (EQ_MP (@lem2325620) (@lem0)). Qed.
Lemma lem2325622 : term340.
Proof. exact (@lem2325611 (@lem2325621)). Qed.
Lemma lem2325624 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325625 : term337 = term338.
Proof. exact (@lem2325624 (NUMERAL 0) term57). Qed.
Lemma lem2325626 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325627 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325628 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325627 h1) (fun h1 : term338 = True => @lem2325626)). Qed.
Lemma lem2325629 : term338 = True.
Proof. exact (EQ_MP (@lem2325628) (@lem2325626)). Qed.
Lemma lem2325630 : term337 = True.
Proof. exact (TRANS (@lem2325625) (@lem2325629)). Qed.
Lemma lem2325631 : True = term337.
Proof. exact (SYM (@lem2325630)). Qed.
Lemma lem2325632 : term337.
Proof. exact (EQ_MP (@lem2325631) (@lem0)). Qed.
Lemma lem2325633 : term341.
Proof. exact (@lem2325622 (@lem2325632)). Qed.
Lemma lem2325635 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325636 : term337 = term338.
Proof. exact (@lem2325635 (NUMERAL 0) term57). Qed.
Lemma lem2325637 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325638 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325639 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325638 h1) (fun h1 : term338 = True => @lem2325637)). Qed.
Lemma lem2325640 : term338 = True.
Proof. exact (EQ_MP (@lem2325639) (@lem2325637)). Qed.
Lemma lem2325641 : term337 = True.
Proof. exact (TRANS (@lem2325636) (@lem2325640)). Qed.
Lemma lem2325642 : True = term337.
Proof. exact (SYM (@lem2325641)). Qed.
Lemma lem2325643 : term337.
Proof. exact (EQ_MP (@lem2325642) (@lem0)). Qed.
Lemma lem2325644 : term342.
Proof. exact (@lem2325633 (@lem2325643)). Qed.
Lemma lem2325646 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2325647 : term179 = term180.
Proof. exact (@lem2325646 term57 term57). Qed.
Lemma lem2325648 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2325649 : term182 = term57.
Proof. exact (EQ_MP (@lem2325648) (@lem940073)). Qed.
Lemma lem2325650 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2325651 : term180 = term56.
Proof. exact (MK_COMB (@lem2325650) (@lem2325649)). Qed.
Lemma lem2325652 : term179 = term56.
Proof. exact (TRANS (@lem2325647) (@lem2325651)). Qed.
Lemma lem2325654 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2325655 : term174 = term185.
Proof. exact (@lem2325654 term57 term57). Qed.
Lemma lem2325656 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2325657 : term182 = term57.
Proof. exact (EQ_MP (@lem2325656) (@lem940073)). Qed.
Lemma lem2325658 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2325659 : term180 = term56.
Proof. exact (MK_COMB (@lem2325658) (@lem2325657)). Qed.
Lemma lem2325660 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2325661 : term185 = term166.
Proof. exact (MK_COMB (@lem2325660) (@lem2325659)). Qed.
Lemma lem2325662 : term174 = term166.
Proof. exact (TRANS (@lem2325655) (@lem2325661)). Qed.
Lemma lem2325663 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2325664 : term343 = term331.
Proof. exact (MK_COMB (@lem2325663) (@lem2325662)). Qed.
Lemma lem2325665 : term344 = term333.
Proof. exact (MK_COMB (@lem2325664) (@lem2325652)). Qed.
Lemma lem2325667 (m : nat) : (term345 m) = term159.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2325668 : term333 = term159.
Proof. exact (@lem2325667 term57). Qed.
Lemma lem2325669 : term344 = term159.
Proof. exact (TRANS (@lem2325665) (@lem2325668)). Qed.
Lemma lem2325670 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2325671 : term346 = term347.
Proof. exact (MK_COMB (@lem2325670) (@lem2325669)). Qed.
Lemma lem2325672 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2325673 : term348 = term349.
Proof. exact (MK_COMB (@lem2325671) (@lem2325672)). Qed.
Lemma lem2325675 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2325676 : term349 = term159.
Proof. exact (@lem2325675 term57). Qed.
Lemma lem2325677 : term348 = term159.
Proof. exact (TRANS (@lem2325673) (@lem2325676)). Qed.
Lemma lem2325679 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2325680 : term179 = term180.
Proof. exact (@lem2325679 term57 term57). Qed.
Lemma lem2325681 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2325682 : term182 = term57.
Proof. exact (EQ_MP (@lem2325681) (@lem940073)). Qed.
Lemma lem2325683 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2325684 : term180 = term56.
Proof. exact (MK_COMB (@lem2325683) (@lem2325682)). Qed.
Lemma lem2325685 : term179 = term56.
Proof. exact (TRANS (@lem2325680) (@lem2325684)). Qed.
Lemma lem2325686 : term347 = term347.
Proof. exact (eq_refl term347). Qed.
Lemma lem2325687 : term351 = term349.
Proof. exact (MK_COMB (@lem2325686) (@lem2325685)). Qed.
Lemma lem2325689 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2325690 : term349 = term159.
Proof. exact (@lem2325689 term57). Qed.
Lemma lem2325691 : term351 = term159.
Proof. exact (TRANS (@lem2325687) (@lem2325690)). Qed.
Lemma lem2325692 : term159 = term351.
Proof. exact (SYM (@lem2325691)). Qed.
Lemma lem2325693 : term348 = term351.
Proof. exact (TRANS (@lem2325677) (@lem2325692)). Qed.
Lemma lem2325694 : term334 = term315.
Proof. exact (@lem2325644 (@lem2325693)). Qed.
Lemma lem2325695 : term333 = term315.
Proof. exact (TRANS (@lem2325610) (@lem2325694)). Qed.
Lemma lem2325697 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2325698 : term315 = term159.
Proof. exact (@lem2325697 term159). Qed.
Lemma lem2325699 : term333 = term159.
Proof. exact (TRANS (@lem2325695) (@lem2325698)). Qed.
Lemma lem2325700 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2325701 : term352 = term347.
Proof. exact (MK_COMB (@lem2325700) (@lem2325699)). Qed.
Lemma lem2325702 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2325703 (y : int) : (term330 y) = (term353 y).
Proof. exact (MK_COMB (@lem2325701) (@lem2325702 y)). Qed.
Lemma lem2325704 (y : int) : (term389 y) = (term353 y).
Proof. exact (TRANS (@lem2325601 y) (@lem2325703 y)). Qed.
Lemma lem2325705 (y : int) : (term353 y) = term159.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2325706 (y : int) : (term389 y) = term159.
Proof. exact (TRANS (@lem2325704 y) (@lem2325705 y)). Qed.
Lemma lem2325707 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2325708 (y : int) : (term390 y) = term355.
Proof. exact (MK_COMB (@lem2325707) (@lem2325706 y)). Qed.
Lemma lem2325709 : term166 = term166.
Proof. exact (eq_refl term166). Qed.
Lemma lem2325710 (y : int) : (term388 y) = term356.
Proof. exact (MK_COMB (@lem2325708 y) (@lem2325709)). Qed.
Lemma lem2325711 (y : int) : (term387 y) = term356.
Proof. exact (TRANS (@lem2325600 y) (@lem2325710 y)). Qed.
Lemma lem2325712 : term356 = term166.
Proof. exact (@lem1982721 term166). Qed.
Lemma lem2325714 (y : int) : (term387 y) = term166.
Proof. exact (TRANS (@lem2325711 y) (@lem2325712)). Qed.
Lemma lem2325715 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2325716 (y : int) : (term391 y) = term364.
Proof. exact (MK_COMB (@lem2325715) (@lem2325714 y)). Qed.
Lemma lem2325717 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2325718 (y : int) : (term392 y) = term365.
Proof. exact (MK_COMB (@lem2325716 y) (@lem2325717)). Qed.
Lemma lem2325741 (x : int) (y : int) : (term417 y x) = (term218 x y).
Proof. exact (@lem1982757 (real_of_int x) (term156 y) term166). Qed.
Lemma lem2325742 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2325743 (x : int) (y : int) : (term424 y x) = (term220 x y).
Proof. exact (MK_COMB (@lem2325742) (@lem2325741 x y)). Qed.
Lemma lem2325744 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2325745 (x : int) (y : int) : (term386 y x) = (term221 x y).
Proof. exact (MK_COMB (@lem2325743 x y) (@lem2325744)). Qed.
Lemma lem2325746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2325747 (x : int) (y : int) : (term432 y x) = (term239 x y).
Proof. exact (MK_COMB (@lem2325746) (@lem2325745 x y)). Qed.
Lemma lem2325748 (x : int) (y : int) : (term431 x y) = (term427 x y).
Proof. exact (MK_COMB (@lem2325747 x y) (@lem2325718 y)). Qed.
Lemma lem2325749 (x : int) (y : int) : (term236 x y) = (term427 x y).
Proof. exact (TRANS (@lem2325582 x y) (@lem2325748 x y)). Qed.
Lemma lem2325750 (x : int) (y : int) : (term239 x y) = (term239 x y).
Proof. exact (eq_refl (term239 x y)). Qed.
Lemma lem2325753 (x : int) (y : int) : (term433 x y) = (term434 x y).
Proof. exact (MK_COMB (@lem2325750 x y) (@lem2325749 x y)). Qed.
Lemma lem2325754 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2325755 (x : int) (y : int) : (term435 x y) = (term436 x y).
Proof. exact (MK_COMB (@lem2325754) (@lem2325579 x y)). Qed.
Lemma lem2325756 (x : int) (y : int) : (term285 x y) = (term437 x y).
Proof. exact (MK_COMB (@lem2325755 x y) (@lem2325753 x y)). Qed.
Lemma lem2325757 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2325758 (x : int) (y : int) : (term287 x y) = (term438 x y).
Proof. exact (MK_COMB (@lem2325757) (@lem2325286 x y)). Qed.
Lemma lem2325759 (x : int) (y : int) : (term288 x y) = (term439 x y).
Proof. exact (MK_COMB (@lem2325758 x y) (@lem2325756 x y)). Qed.
Lemma lem2325760 (x : int) (y : int) (h1 : term439 x y) : term439 x y.
Proof. exact (h1). Qed.
Lemma lem2325761 (x : int) (y : int) (h1 : term400 x y) : term400 x y.
Proof. exact (h1). Qed.
Lemma lem2325762 (x : int) (y : int) (h1 : term382 x y) : term382 x y.
Proof. exact (h1). Qed.
Lemma lem2325763 (x : int) (y : int) (h1 : term367 x y) : term367 x y.
Proof. exact (h1). Qed.
Lemma lem2325764 (x : int) (y : int) (h1 : term367 x y) : term366 x y.
Proof. exact (proj2 (@lem2325763 x y h1)). Qed.
Lemma lem2325766 (x : int) (y : int) (h1 : term367 x y) : term365.
Proof. exact (proj2 (@lem2325764 x y h1)). Qed.
Lemma lem2325769 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2325770 : term365 = term440.
Proof. exact (@lem2325769 term159 term166). Qed.
Lemma lem2325772 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2325773 : term166 = term171.
Proof. exact (@lem2325772 term57). Qed.
Lemma lem2325775 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2325776 : term159 = term315.
Proof. exact (@lem2325775 (NUMERAL 0)). Qed.
Lemma lem2325777 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2325778 : term441 = term442.
Proof. exact (MK_COMB (@lem2325777) (@lem2325776)). Qed.
Lemma lem2325779 : term440 = term443.
Proof. exact (MK_COMB (@lem2325778) (@lem2325773)). Qed.
Lemma lem2325780 : term444.
Proof. exact (@lem1980026 term159 term56 term166 term56). Qed.
Lemma lem2325782 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325783 : term337 = term338.
Proof. exact (@lem2325782 (NUMERAL 0) term57). Qed.
Lemma lem2325784 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325785 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325786 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325785 h1) (fun h1 : term338 = True => @lem2325784)). Qed.
Lemma lem2325787 : term338 = True.
Proof. exact (EQ_MP (@lem2325786) (@lem2325784)). Qed.
Lemma lem2325788 : term337 = True.
Proof. exact (TRANS (@lem2325783) (@lem2325787)). Qed.
Lemma lem2325789 : True = term337.
Proof. exact (SYM (@lem2325788)). Qed.
Lemma lem2325790 : term337.
Proof. exact (EQ_MP (@lem2325789) (@lem0)). Qed.
Lemma lem2325791 : term445.
Proof. exact (@lem2325780 (@lem2325790)). Qed.
Lemma lem2325793 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325794 : term337 = term338.
Proof. exact (@lem2325793 (NUMERAL 0) term57). Qed.
Lemma lem2325795 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325796 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325797 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325796 h1) (fun h1 : term338 = True => @lem2325795)). Qed.
Lemma lem2325798 : term338 = True.
Proof. exact (EQ_MP (@lem2325797) (@lem2325795)). Qed.
Lemma lem2325799 : term337 = True.
Proof. exact (TRANS (@lem2325794) (@lem2325798)). Qed.
Lemma lem2325800 : True = term337.
Proof. exact (SYM (@lem2325799)). Qed.
Lemma lem2325801 : term337.
Proof. exact (EQ_MP (@lem2325800) (@lem0)). Qed.
Lemma lem2325802 : term443 = term446.
Proof. exact (@lem2325791 (@lem2325801)). Qed.
Lemma lem2325804 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2325805 : term174 = term185.
Proof. exact (@lem2325804 term57 term57). Qed.
Lemma lem2325806 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2325807 : term182 = term57.
Proof. exact (EQ_MP (@lem2325806) (@lem940073)). Qed.
Lemma lem2325808 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2325809 : term180 = term56.
Proof. exact (MK_COMB (@lem2325808) (@lem2325807)). Qed.
Lemma lem2325810 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2325811 : term185 = term166.
Proof. exact (MK_COMB (@lem2325810) (@lem2325809)). Qed.
Lemma lem2325812 : term174 = term166.
Proof. exact (TRANS (@lem2325805) (@lem2325811)). Qed.
Lemma lem2325814 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2325815 : term349 = term159.
Proof. exact (@lem2325814 term57). Qed.
Lemma lem2325816 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2325817 : term447 = term441.
Proof. exact (MK_COMB (@lem2325816) (@lem2325815)). Qed.
Lemma lem2325818 : term446 = term440.
Proof. exact (MK_COMB (@lem2325817) (@lem2325812)). Qed.
Lemma lem2325820 (m : nat) (n : nat) : (term448 m n) = (term449 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2325821 : term440 = term450.
Proof. exact (@lem2325820 (NUMERAL 0) term57). Qed.
Lemma lem2325822 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325823 (h1 : term339 = (BIT1 0)) : (term57 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2325824 : (term339 = (BIT1 0)) = ((term57 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325823 h1) (fun h1 : (term57 = (NUMERAL 0)) = False => @lem2325822)). Qed.
Lemma lem2325825 : (term57 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2325824) (@lem2325822)). Qed.
Lemma lem2325826 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2325827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2325828 : term451 = (and True).
Proof. exact (MK_COMB (@lem2325827) (@lem2325826)). Qed.
Lemma lem2325829 : term450 = (True /\ False).
Proof. exact (MK_COMB (@lem2325828) (@lem2325825)). Qed.
Lemma lem2325831 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2325832 : term450 = False.
Proof. exact (TRANS (@lem2325829) (@lem2325831)). Qed.
Lemma lem2325833 : term440 = False.
Proof. exact (TRANS (@lem2325821) (@lem2325832)). Qed.
Lemma lem2325834 : term446 = False.
Proof. exact (TRANS (@lem2325818) (@lem2325833)). Qed.
Lemma lem2325835 : term443 = False.
Proof. exact (TRANS (@lem2325802) (@lem2325834)). Qed.
Lemma lem2325836 : term440 = False.
Proof. exact (TRANS (@lem2325779) (@lem2325835)). Qed.
Lemma lem2325837 : term365 = False.
Proof. exact (TRANS (@lem2325770) (@lem2325836)). Qed.
Lemma lem2325838 (x : int) (y : int) (h1 : term367 x y) : False.
Proof. exact (EQ_MP (@lem2325837) (@lem2325766 x y h1)). Qed.
Lemma lem2325839 (x : int) (y : int) (h1 : term380 x y) : term380 x y.
Proof. exact (h1). Qed.
Lemma lem2325840 (x : int) (y : int) (h1 : term380 x y) : term298 x y.
Proof. exact (proj2 (@lem2325839 x y h1)). Qed.
Lemma lem2325841 (x : int) (y : int) (h1 : term380 x y) : term372 x y.
Proof. exact (proj1 (@lem2325839 x y h1)). Qed.
Lemma lem2325843 (x : int) (y : int) (h1 : term380 x y) : term160 x y.
Proof. exact (proj1 (@lem2325840 x y h1)). Qed.
Lemma lem2325845 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2325846 : term452 = term337.
Proof. exact (@lem2325845 term159 term56). Qed.
Lemma lem2325848 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2325849 : term56 = term168.
Proof. exact (@lem2325848 term57). Qed.
Lemma lem2325851 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2325852 : term159 = term315.
Proof. exact (@lem2325851 (NUMERAL 0)). Qed.
Lemma lem2325853 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2325854 : term453 = term454.
Proof. exact (MK_COMB (@lem2325853) (@lem2325852)). Qed.
Lemma lem2325855 : term337 = term455.
Proof. exact (MK_COMB (@lem2325854) (@lem2325849)). Qed.
Lemma lem2325856 : term456.
Proof. exact (@lem1980255 term159 term56 term56 term56). Qed.
Lemma lem2325858 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325859 : term337 = term338.
Proof. exact (@lem2325858 (NUMERAL 0) term57). Qed.
Lemma lem2325860 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325861 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325862 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325861 h1) (fun h1 : term338 = True => @lem2325860)). Qed.
Lemma lem2325863 : term338 = True.
Proof. exact (EQ_MP (@lem2325862) (@lem2325860)). Qed.
Lemma lem2325864 : term337 = True.
Proof. exact (TRANS (@lem2325859) (@lem2325863)). Qed.
Lemma lem2325865 : True = term337.
Proof. exact (SYM (@lem2325864)). Qed.
Lemma lem2325866 : term337.
Proof. exact (EQ_MP (@lem2325865) (@lem0)). Qed.
Lemma lem2325867 : term457.
Proof. exact (@lem2325856 (@lem2325866)). Qed.
Lemma lem2325869 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325870 : term337 = term338.
Proof. exact (@lem2325869 (NUMERAL 0) term57). Qed.
Lemma lem2325871 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325872 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325873 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325872 h1) (fun h1 : term338 = True => @lem2325871)). Qed.
Lemma lem2325874 : term338 = True.
Proof. exact (EQ_MP (@lem2325873) (@lem2325871)). Qed.
Lemma lem2325875 : term337 = True.
Proof. exact (TRANS (@lem2325870) (@lem2325874)). Qed.
Lemma lem2325876 : True = term337.
Proof. exact (SYM (@lem2325875)). Qed.
Lemma lem2325877 : term337.
Proof. exact (EQ_MP (@lem2325876) (@lem0)). Qed.
Lemma lem2325878 : term455 = term458.
Proof. exact (@lem2325867 (@lem2325877)). Qed.
Lemma lem2325880 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2325881 : term179 = term180.
Proof. exact (@lem2325880 term57 term57). Qed.
Lemma lem2325882 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2325883 : term182 = term57.
Proof. exact (EQ_MP (@lem2325882) (@lem940073)). Qed.
Lemma lem2325884 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2325885 : term180 = term56.
Proof. exact (MK_COMB (@lem2325884) (@lem2325883)). Qed.
Lemma lem2325886 : term179 = term56.
Proof. exact (TRANS (@lem2325881) (@lem2325885)). Qed.
Lemma lem2325888 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2325889 : term349 = term159.
Proof. exact (@lem2325888 term57). Qed.
Lemma lem2325890 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2325891 : term459 = term453.
Proof. exact (MK_COMB (@lem2325890) (@lem2325889)). Qed.
Lemma lem2325892 : term458 = term337.
Proof. exact (MK_COMB (@lem2325891) (@lem2325886)). Qed.
Lemma lem2325894 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325895 : term337 = term338.
Proof. exact (@lem2325894 (NUMERAL 0) term57). Qed.
Lemma lem2325896 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325897 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325898 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325897 h1) (fun h1 : term338 = True => @lem2325896)). Qed.
Lemma lem2325899 : term338 = True.
Proof. exact (EQ_MP (@lem2325898) (@lem2325896)). Qed.
Lemma lem2325900 : term337 = True.
Proof. exact (TRANS (@lem2325895) (@lem2325899)). Qed.
Lemma lem2325901 : term458 = True.
Proof. exact (TRANS (@lem2325892) (@lem2325900)). Qed.
Lemma lem2325902 : term455 = True.
Proof. exact (TRANS (@lem2325878) (@lem2325901)). Qed.
Lemma lem2325903 : term337 = True.
Proof. exact (TRANS (@lem2325855) (@lem2325902)). Qed.
Lemma lem2325904 : term452 = True.
Proof. exact (TRANS (@lem2325846) (@lem2325903)). Qed.
Lemma lem2325905 : True = term452.
Proof. exact (SYM (@lem2325904)). Qed.
Lemma lem2325906 : term452.
Proof. exact (EQ_MP (@lem2325905) (@lem0)). Qed.
Lemma lem2325907 (x : int) (y : int) (h1 : term380 x y) : term460 x y.
Proof. exact (conj (@lem2325906) (@lem2325843 x y h1)). Qed.
Lemma lem2325909 (x : real) (y : real) : term461 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2325910 (x : int) (y : int) : term462 x y.
Proof. exact (@lem2325909 term56 (term155 x y)). Qed.
Lemma lem2325911 (x : int) (y : int) (h1 : term380 x y) : term463 x y.
Proof. exact (@lem2325910 x y (@lem2325907 x y h1)). Qed.
Lemma lem2325912 (x : int) (y : int) : (term464 x y) = (term155 x y).
Proof. exact (@lem1982733 (term155 x y)). Qed.
Lemma lem2325913 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2325914 (x : int) (y : int) : (term465 x y) = (term158 x y).
Proof. exact (MK_COMB (@lem2325913) (@lem2325912 x y)). Qed.
Lemma lem2325915 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2325916 (x : int) (y : int) : (term463 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem2325914 x y) (@lem2325915)). Qed.
Lemma lem2325917 (x : int) (y : int) (h1 : term380 x y) : term160 x y.
Proof. exact (EQ_MP (@lem2325916 x y) (@lem2325911 x y h1)). Qed.
Lemma lem2325919 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2325920 : term452 = term337.
Proof. exact (@lem2325919 term159 term56). Qed.
Lemma lem2325922 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2325923 : term56 = term168.
Proof. exact (@lem2325922 term57). Qed.
Lemma lem2325925 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2325926 : term159 = term315.
Proof. exact (@lem2325925 (NUMERAL 0)). Qed.
Lemma lem2325927 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2325928 : term453 = term454.
Proof. exact (MK_COMB (@lem2325927) (@lem2325926)). Qed.
Lemma lem2325929 : term337 = term455.
Proof. exact (MK_COMB (@lem2325928) (@lem2325923)). Qed.
Lemma lem2325930 : term456.
Proof. exact (@lem1980255 term159 term56 term56 term56). Qed.
Lemma lem2325932 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325933 : term337 = term338.
Proof. exact (@lem2325932 (NUMERAL 0) term57). Qed.
Lemma lem2325934 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325935 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325936 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325935 h1) (fun h1 : term338 = True => @lem2325934)). Qed.
Lemma lem2325937 : term338 = True.
Proof. exact (EQ_MP (@lem2325936) (@lem2325934)). Qed.
Lemma lem2325938 : term337 = True.
Proof. exact (TRANS (@lem2325933) (@lem2325937)). Qed.
Lemma lem2325939 : True = term337.
Proof. exact (SYM (@lem2325938)). Qed.
Lemma lem2325940 : term337.
Proof. exact (EQ_MP (@lem2325939) (@lem0)). Qed.
Lemma lem2325941 : term457.
Proof. exact (@lem2325930 (@lem2325940)). Qed.
Lemma lem2325943 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325944 : term337 = term338.
Proof. exact (@lem2325943 (NUMERAL 0) term57). Qed.
Lemma lem2325945 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325946 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325947 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325946 h1) (fun h1 : term338 = True => @lem2325945)). Qed.
Lemma lem2325948 : term338 = True.
Proof. exact (EQ_MP (@lem2325947) (@lem2325945)). Qed.
Lemma lem2325949 : term337 = True.
Proof. exact (TRANS (@lem2325944) (@lem2325948)). Qed.
Lemma lem2325950 : True = term337.
Proof. exact (SYM (@lem2325949)). Qed.
Lemma lem2325951 : term337.
Proof. exact (EQ_MP (@lem2325950) (@lem0)). Qed.
Lemma lem2325952 : term455 = term458.
Proof. exact (@lem2325941 (@lem2325951)). Qed.
Lemma lem2325954 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2325955 : term179 = term180.
Proof. exact (@lem2325954 term57 term57). Qed.
Lemma lem2325956 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2325957 : term182 = term57.
Proof. exact (EQ_MP (@lem2325956) (@lem940073)). Qed.
Lemma lem2325958 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2325959 : term180 = term56.
Proof. exact (MK_COMB (@lem2325958) (@lem2325957)). Qed.
Lemma lem2325960 : term179 = term56.
Proof. exact (TRANS (@lem2325955) (@lem2325959)). Qed.
Lemma lem2325962 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2325963 : term349 = term159.
Proof. exact (@lem2325962 term57). Qed.
Lemma lem2325964 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2325965 : term459 = term453.
Proof. exact (MK_COMB (@lem2325964) (@lem2325963)). Qed.
Lemma lem2325966 : term458 = term337.
Proof. exact (MK_COMB (@lem2325965) (@lem2325960)). Qed.
Lemma lem2325968 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2325969 : term337 = term338.
Proof. exact (@lem2325968 (NUMERAL 0) term57). Qed.
Lemma lem2325970 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2325971 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2325972 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2325971 h1) (fun h1 : term338 = True => @lem2325970)). Qed.
Lemma lem2325973 : term338 = True.
Proof. exact (EQ_MP (@lem2325972) (@lem2325970)). Qed.
Lemma lem2325974 : term337 = True.
Proof. exact (TRANS (@lem2325969) (@lem2325973)). Qed.
Lemma lem2325975 : term458 = True.
Proof. exact (TRANS (@lem2325966) (@lem2325974)). Qed.
Lemma lem2325976 : term455 = True.
Proof. exact (TRANS (@lem2325952) (@lem2325975)). Qed.
Lemma lem2325977 : term337 = True.
Proof. exact (TRANS (@lem2325929) (@lem2325976)). Qed.
Lemma lem2325978 : term452 = True.
Proof. exact (TRANS (@lem2325920) (@lem2325977)). Qed.
Lemma lem2325979 : True = term452.
Proof. exact (SYM (@lem2325978)). Qed.
Lemma lem2325980 : term452.
Proof. exact (EQ_MP (@lem2325979) (@lem0)). Qed.
Lemma lem2325981 (x : int) (y : int) (h1 : term380 x y) : term466 x y.
Proof. exact (conj (@lem2325980) (@lem2325841 x y h1)). Qed.
Lemma lem2325983 (x : real) (y : real) : term467 x y.
Proof. exact (proj2 (@lem1988332 x y)). Qed.
Lemma lem2325984 (x : int) (y : int) : term468 x y.
Proof. exact (@lem2325983 term56 (term154 x y)). Qed.
Lemma lem2325985 (x : int) (y : int) (h1 : term380 x y) : term469 x y.
Proof. exact (@lem2325984 x y (@lem2325981 x y h1)). Qed.
Lemma lem2325986 (x : int) (y : int) : (term470 x y) = (term154 x y).
Proof. exact (@lem1982733 (term154 x y)). Qed.
Lemma lem2325987 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2325988 (x : int) (y : int) : (term471 x y) = (term371 x y).
Proof. exact (MK_COMB (@lem2325987) (@lem2325986 x y)). Qed.
Lemma lem2325989 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2325990 (x : int) (y : int) : (term469 x y) = (term372 x y).
Proof. exact (MK_COMB (@lem2325988 x y) (@lem2325989)). Qed.
Lemma lem2325991 (x : int) (y : int) (h1 : term380 x y) : term372 x y.
Proof. exact (EQ_MP (@lem2325990 x y) (@lem2325985 x y h1)). Qed.
Lemma lem2325992 (x : int) (y : int) (h1 : term380 x y) : term472 x y.
Proof. exact (conj (@lem2325991 x y h1) (@lem2325917 x y h1)). Qed.
Lemma lem2325994 (x : real) (y : real) : term473 x y.
Proof. exact (proj1 (@lem1988348 x y)). Qed.
Lemma lem2325995 (x : int) (y : int) : term474 x y.
Proof. exact (@lem2325994 (term154 x y) (term155 x y)). Qed.
Lemma lem2325996 (x : int) (y : int) (h1 : term380 x y) : term475 x y.
Proof. exact (@lem2325995 x y (@lem2325992 x y h1)). Qed.
Lemma lem2325997 (x : int) (y : int) : (term476 x y) = (term477 x y).
Proof. exact (@lem1982753 (real_of_int x) (term156 x) (term156 y) (real_of_int y)). Qed.
Lemma lem2325998 (x : int) : (term329 x) = (term330 x).
Proof. exact (@lem1982715 term166 (real_of_int x)). Qed.
Lemma lem2326000 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2326001 : term56 = term168.
Proof. exact (@lem2326000 term57). Qed.
Lemma lem2326003 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2326004 : term166 = term171.
Proof. exact (@lem2326003 term57). Qed.
Lemma lem2326005 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2326006 : term331 = term332.
Proof. exact (MK_COMB (@lem2326005) (@lem2326004)). Qed.
Lemma lem2326007 : term333 = term334.
Proof. exact (MK_COMB (@lem2326006) (@lem2326001)). Qed.
Lemma lem2326008 : term335.
Proof. exact (@lem1981473 term166 term56 term56 term56 term159 term56). Qed.
Lemma lem2326010 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326011 : term337 = term338.
Proof. exact (@lem2326010 (NUMERAL 0) term57). Qed.
Lemma lem2326012 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326013 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326014 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326013 h1) (fun h1 : term338 = True => @lem2326012)). Qed.
Lemma lem2326015 : term338 = True.
Proof. exact (EQ_MP (@lem2326014) (@lem2326012)). Qed.
Lemma lem2326016 : term337 = True.
Proof. exact (TRANS (@lem2326011) (@lem2326015)). Qed.
Lemma lem2326017 : True = term337.
Proof. exact (SYM (@lem2326016)). Qed.
Lemma lem2326018 : term337.
Proof. exact (EQ_MP (@lem2326017) (@lem0)). Qed.
Lemma lem2326019 : term340.
Proof. exact (@lem2326008 (@lem2326018)). Qed.
Lemma lem2326021 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326022 : term337 = term338.
Proof. exact (@lem2326021 (NUMERAL 0) term57). Qed.
Lemma lem2326023 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326024 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326025 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326024 h1) (fun h1 : term338 = True => @lem2326023)). Qed.
Lemma lem2326026 : term338 = True.
Proof. exact (EQ_MP (@lem2326025) (@lem2326023)). Qed.
Lemma lem2326027 : term337 = True.
Proof. exact (TRANS (@lem2326022) (@lem2326026)). Qed.
Lemma lem2326028 : True = term337.
Proof. exact (SYM (@lem2326027)). Qed.
Lemma lem2326029 : term337.
Proof. exact (EQ_MP (@lem2326028) (@lem0)). Qed.
Lemma lem2326030 : term341.
Proof. exact (@lem2326019 (@lem2326029)). Qed.
Lemma lem2326032 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326033 : term337 = term338.
Proof. exact (@lem2326032 (NUMERAL 0) term57). Qed.
Lemma lem2326034 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326035 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326036 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326035 h1) (fun h1 : term338 = True => @lem2326034)). Qed.
Lemma lem2326037 : term338 = True.
Proof. exact (EQ_MP (@lem2326036) (@lem2326034)). Qed.
Lemma lem2326038 : term337 = True.
Proof. exact (TRANS (@lem2326033) (@lem2326037)). Qed.
Lemma lem2326039 : True = term337.
Proof. exact (SYM (@lem2326038)). Qed.
Lemma lem2326040 : term337.
Proof. exact (EQ_MP (@lem2326039) (@lem0)). Qed.
Lemma lem2326041 : term342.
Proof. exact (@lem2326030 (@lem2326040)). Qed.
Lemma lem2326043 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2326044 : term179 = term180.
Proof. exact (@lem2326043 term57 term57). Qed.
Lemma lem2326045 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326046 : term182 = term57.
Proof. exact (EQ_MP (@lem2326045) (@lem940073)). Qed.
Lemma lem2326047 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326048 : term180 = term56.
Proof. exact (MK_COMB (@lem2326047) (@lem2326046)). Qed.
Lemma lem2326049 : term179 = term56.
Proof. exact (TRANS (@lem2326044) (@lem2326048)). Qed.
Lemma lem2326051 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2326052 : term174 = term185.
Proof. exact (@lem2326051 term57 term57). Qed.
Lemma lem2326053 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326054 : term182 = term57.
Proof. exact (EQ_MP (@lem2326053) (@lem940073)). Qed.
Lemma lem2326055 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326056 : term180 = term56.
Proof. exact (MK_COMB (@lem2326055) (@lem2326054)). Qed.
Lemma lem2326057 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2326058 : term185 = term166.
Proof. exact (MK_COMB (@lem2326057) (@lem2326056)). Qed.
Lemma lem2326059 : term174 = term166.
Proof. exact (TRANS (@lem2326052) (@lem2326058)). Qed.
Lemma lem2326060 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2326061 : term343 = term331.
Proof. exact (MK_COMB (@lem2326060) (@lem2326059)). Qed.
Lemma lem2326062 : term344 = term333.
Proof. exact (MK_COMB (@lem2326061) (@lem2326049)). Qed.
Lemma lem2326064 (m : nat) : (term345 m) = term159.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2326065 : term333 = term159.
Proof. exact (@lem2326064 term57). Qed.
Lemma lem2326066 : term344 = term159.
Proof. exact (TRANS (@lem2326062) (@lem2326065)). Qed.
Lemma lem2326067 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2326068 : term346 = term347.
Proof. exact (MK_COMB (@lem2326067) (@lem2326066)). Qed.
Lemma lem2326069 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2326070 : term348 = term349.
Proof. exact (MK_COMB (@lem2326068) (@lem2326069)). Qed.
Lemma lem2326072 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2326073 : term349 = term159.
Proof. exact (@lem2326072 term57). Qed.
Lemma lem2326074 : term348 = term159.
Proof. exact (TRANS (@lem2326070) (@lem2326073)). Qed.
Lemma lem2326076 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2326077 : term179 = term180.
Proof. exact (@lem2326076 term57 term57). Qed.
Lemma lem2326078 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326079 : term182 = term57.
Proof. exact (EQ_MP (@lem2326078) (@lem940073)). Qed.
Lemma lem2326080 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326081 : term180 = term56.
Proof. exact (MK_COMB (@lem2326080) (@lem2326079)). Qed.
Lemma lem2326082 : term179 = term56.
Proof. exact (TRANS (@lem2326077) (@lem2326081)). Qed.
Lemma lem2326083 : term347 = term347.
Proof. exact (eq_refl term347). Qed.
Lemma lem2326084 : term351 = term349.
Proof. exact (MK_COMB (@lem2326083) (@lem2326082)). Qed.
Lemma lem2326086 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2326087 : term349 = term159.
Proof. exact (@lem2326086 term57). Qed.
Lemma lem2326088 : term351 = term159.
Proof. exact (TRANS (@lem2326084) (@lem2326087)). Qed.
Lemma lem2326089 : term159 = term351.
Proof. exact (SYM (@lem2326088)). Qed.
Lemma lem2326090 : term348 = term351.
Proof. exact (TRANS (@lem2326074) (@lem2326089)). Qed.
Lemma lem2326091 : term334 = term315.
Proof. exact (@lem2326041 (@lem2326090)). Qed.
Lemma lem2326092 : term333 = term315.
Proof. exact (TRANS (@lem2326007) (@lem2326091)). Qed.
Lemma lem2326094 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2326095 : term315 = term159.
Proof. exact (@lem2326094 term159). Qed.
Lemma lem2326096 : term333 = term159.
Proof. exact (TRANS (@lem2326092) (@lem2326095)). Qed.
Lemma lem2326097 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2326098 : term352 = term347.
Proof. exact (MK_COMB (@lem2326097) (@lem2326096)). Qed.
Lemma lem2326099 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2326100 (x : int) : (term330 x) = (term353 x).
Proof. exact (MK_COMB (@lem2326098) (@lem2326099 x)). Qed.
Lemma lem2326101 (x : int) : (term329 x) = (term353 x).
Proof. exact (TRANS (@lem2325998 x) (@lem2326100 x)). Qed.
Lemma lem2326102 (x : int) : (term353 x) = term159.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2326103 (x : int) : (term329 x) = term159.
Proof. exact (TRANS (@lem2326101 x) (@lem2326102 x)). Qed.
Lemma lem2326104 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2326105 (x : int) : (term354 x) = term355.
Proof. exact (MK_COMB (@lem2326104) (@lem2326103 x)). Qed.
Lemma lem2326106 (y : int) : (term389 y) = (term330 y).
Proof. exact (@lem1982713 term166 (real_of_int y)). Qed.
Lemma lem2326108 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2326109 : term56 = term168.
Proof. exact (@lem2326108 term57). Qed.
Lemma lem2326111 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2326112 : term166 = term171.
Proof. exact (@lem2326111 term57). Qed.
Lemma lem2326113 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2326114 : term331 = term332.
Proof. exact (MK_COMB (@lem2326113) (@lem2326112)). Qed.
Lemma lem2326115 : term333 = term334.
Proof. exact (MK_COMB (@lem2326114) (@lem2326109)). Qed.
Lemma lem2326116 : term335.
Proof. exact (@lem1981473 term166 term56 term56 term56 term159 term56). Qed.
Lemma lem2326118 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326119 : term337 = term338.
Proof. exact (@lem2326118 (NUMERAL 0) term57). Qed.
Lemma lem2326120 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326121 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326122 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326121 h1) (fun h1 : term338 = True => @lem2326120)). Qed.
Lemma lem2326123 : term338 = True.
Proof. exact (EQ_MP (@lem2326122) (@lem2326120)). Qed.
Lemma lem2326124 : term337 = True.
Proof. exact (TRANS (@lem2326119) (@lem2326123)). Qed.
Lemma lem2326125 : True = term337.
Proof. exact (SYM (@lem2326124)). Qed.
Lemma lem2326126 : term337.
Proof. exact (EQ_MP (@lem2326125) (@lem0)). Qed.
Lemma lem2326127 : term340.
Proof. exact (@lem2326116 (@lem2326126)). Qed.
Lemma lem2326129 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326130 : term337 = term338.
Proof. exact (@lem2326129 (NUMERAL 0) term57). Qed.
Lemma lem2326131 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326132 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326133 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326132 h1) (fun h1 : term338 = True => @lem2326131)). Qed.
Lemma lem2326134 : term338 = True.
Proof. exact (EQ_MP (@lem2326133) (@lem2326131)). Qed.
Lemma lem2326135 : term337 = True.
Proof. exact (TRANS (@lem2326130) (@lem2326134)). Qed.
Lemma lem2326136 : True = term337.
Proof. exact (SYM (@lem2326135)). Qed.
Lemma lem2326137 : term337.
Proof. exact (EQ_MP (@lem2326136) (@lem0)). Qed.
Lemma lem2326138 : term341.
Proof. exact (@lem2326127 (@lem2326137)). Qed.
Lemma lem2326140 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326141 : term337 = term338.
Proof. exact (@lem2326140 (NUMERAL 0) term57). Qed.
Lemma lem2326142 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326143 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326144 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326143 h1) (fun h1 : term338 = True => @lem2326142)). Qed.
Lemma lem2326145 : term338 = True.
Proof. exact (EQ_MP (@lem2326144) (@lem2326142)). Qed.
Lemma lem2326146 : term337 = True.
Proof. exact (TRANS (@lem2326141) (@lem2326145)). Qed.
Lemma lem2326147 : True = term337.
Proof. exact (SYM (@lem2326146)). Qed.
Lemma lem2326148 : term337.
Proof. exact (EQ_MP (@lem2326147) (@lem0)). Qed.
Lemma lem2326149 : term342.
Proof. exact (@lem2326138 (@lem2326148)). Qed.
Lemma lem2326151 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2326152 : term179 = term180.
Proof. exact (@lem2326151 term57 term57). Qed.
Lemma lem2326153 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326154 : term182 = term57.
Proof. exact (EQ_MP (@lem2326153) (@lem940073)). Qed.
Lemma lem2326155 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326156 : term180 = term56.
Proof. exact (MK_COMB (@lem2326155) (@lem2326154)). Qed.
Lemma lem2326157 : term179 = term56.
Proof. exact (TRANS (@lem2326152) (@lem2326156)). Qed.
Lemma lem2326159 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2326160 : term174 = term185.
Proof. exact (@lem2326159 term57 term57). Qed.
Lemma lem2326161 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326162 : term182 = term57.
Proof. exact (EQ_MP (@lem2326161) (@lem940073)). Qed.
Lemma lem2326163 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326164 : term180 = term56.
Proof. exact (MK_COMB (@lem2326163) (@lem2326162)). Qed.
Lemma lem2326165 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2326166 : term185 = term166.
Proof. exact (MK_COMB (@lem2326165) (@lem2326164)). Qed.
Lemma lem2326167 : term174 = term166.
Proof. exact (TRANS (@lem2326160) (@lem2326166)). Qed.
Lemma lem2326168 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2326169 : term343 = term331.
Proof. exact (MK_COMB (@lem2326168) (@lem2326167)). Qed.
Lemma lem2326170 : term344 = term333.
Proof. exact (MK_COMB (@lem2326169) (@lem2326157)). Qed.
Lemma lem2326172 (m : nat) : (term345 m) = term159.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2326173 : term333 = term159.
Proof. exact (@lem2326172 term57). Qed.
Lemma lem2326174 : term344 = term159.
Proof. exact (TRANS (@lem2326170) (@lem2326173)). Qed.
Lemma lem2326175 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2326176 : term346 = term347.
Proof. exact (MK_COMB (@lem2326175) (@lem2326174)). Qed.
Lemma lem2326177 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2326178 : term348 = term349.
Proof. exact (MK_COMB (@lem2326176) (@lem2326177)). Qed.
Lemma lem2326180 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2326181 : term349 = term159.
Proof. exact (@lem2326180 term57). Qed.
Lemma lem2326182 : term348 = term159.
Proof. exact (TRANS (@lem2326178) (@lem2326181)). Qed.
Lemma lem2326184 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2326185 : term179 = term180.
Proof. exact (@lem2326184 term57 term57). Qed.
Lemma lem2326186 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326187 : term182 = term57.
Proof. exact (EQ_MP (@lem2326186) (@lem940073)). Qed.
Lemma lem2326188 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326189 : term180 = term56.
Proof. exact (MK_COMB (@lem2326188) (@lem2326187)). Qed.
Lemma lem2326190 : term179 = term56.
Proof. exact (TRANS (@lem2326185) (@lem2326189)). Qed.
Lemma lem2326191 : term347 = term347.
Proof. exact (eq_refl term347). Qed.
Lemma lem2326192 : term351 = term349.
Proof. exact (MK_COMB (@lem2326191) (@lem2326190)). Qed.
Lemma lem2326194 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2326195 : term349 = term159.
Proof. exact (@lem2326194 term57). Qed.
Lemma lem2326196 : term351 = term159.
Proof. exact (TRANS (@lem2326192) (@lem2326195)). Qed.
Lemma lem2326197 : term159 = term351.
Proof. exact (SYM (@lem2326196)). Qed.
Lemma lem2326198 : term348 = term351.
Proof. exact (TRANS (@lem2326182) (@lem2326197)). Qed.
Lemma lem2326199 : term334 = term315.
Proof. exact (@lem2326149 (@lem2326198)). Qed.
Lemma lem2326200 : term333 = term315.
Proof. exact (TRANS (@lem2326115) (@lem2326199)). Qed.
Lemma lem2326202 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2326203 : term315 = term159.
Proof. exact (@lem2326202 term159). Qed.
Lemma lem2326204 : term333 = term159.
Proof. exact (TRANS (@lem2326200) (@lem2326203)). Qed.
Lemma lem2326205 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2326206 : term352 = term347.
Proof. exact (MK_COMB (@lem2326205) (@lem2326204)). Qed.
Lemma lem2326207 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2326208 (y : int) : (term330 y) = (term353 y).
Proof. exact (MK_COMB (@lem2326206) (@lem2326207 y)). Qed.
Lemma lem2326209 (y : int) : (term389 y) = (term353 y).
Proof. exact (TRANS (@lem2326106 y) (@lem2326208 y)). Qed.
Lemma lem2326210 (y : int) : (term353 y) = term159.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2326211 (y : int) : (term389 y) = term159.
Proof. exact (TRANS (@lem2326209 y) (@lem2326210 y)). Qed.
Lemma lem2326212 (x : int) (y : int) : (term477 x y) = term478.
Proof. exact (MK_COMB (@lem2326105 x) (@lem2326211 y)). Qed.
Lemma lem2326213 (x : int) (y : int) : (term476 x y) = term478.
Proof. exact (TRANS (@lem2325997 x y) (@lem2326212 x y)). Qed.
Lemma lem2326214 : term478 = term159.
Proof. exact (@lem1982721 term159). Qed.
Lemma lem2326215 (x : int) (y : int) : (term476 x y) = term159.
Proof. exact (TRANS (@lem2326213 x y) (@lem2326214)). Qed.
Lemma lem2326216 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem2326217 (x : int) (y : int) : (term479 x y) = term480.
Proof. exact (MK_COMB (@lem2326216) (@lem2326215 x y)). Qed.
Lemma lem2326218 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2326219 (x : int) (y : int) : (term475 x y) = term481.
Proof. exact (MK_COMB (@lem2326217 x y) (@lem2326218)). Qed.
Lemma lem2326220 (x : int) (y : int) (h1 : term380 x y) : term481.
Proof. exact (EQ_MP (@lem2326219 x y) (@lem2325996 x y h1)). Qed.
Lemma lem2326222 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2326223 : term481 = term482.
Proof. exact (@lem2326222 term159 term159). Qed.
Lemma lem2326225 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2326226 : term159 = term315.
Proof. exact (@lem2326225 (NUMERAL 0)). Qed.
Lemma lem2326228 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2326229 : term159 = term315.
Proof. exact (@lem2326228 (NUMERAL 0)). Qed.
Lemma lem2326230 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2326231 : term453 = term454.
Proof. exact (MK_COMB (@lem2326230) (@lem2326229)). Qed.
Lemma lem2326232 : term482 = term483.
Proof. exact (MK_COMB (@lem2326231) (@lem2326226)). Qed.
Lemma lem2326233 : term484.
Proof. exact (@lem1980255 term159 term56 term159 term56). Qed.
Lemma lem2326235 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326236 : term337 = term338.
Proof. exact (@lem2326235 (NUMERAL 0) term57). Qed.
Lemma lem2326237 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326238 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326239 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326238 h1) (fun h1 : term338 = True => @lem2326237)). Qed.
Lemma lem2326240 : term338 = True.
Proof. exact (EQ_MP (@lem2326239) (@lem2326237)). Qed.
Lemma lem2326241 : term337 = True.
Proof. exact (TRANS (@lem2326236) (@lem2326240)). Qed.
Lemma lem2326242 : True = term337.
Proof. exact (SYM (@lem2326241)). Qed.
Lemma lem2326243 : term337.
Proof. exact (EQ_MP (@lem2326242) (@lem0)). Qed.
Lemma lem2326244 : term485.
Proof. exact (@lem2326233 (@lem2326243)). Qed.
Lemma lem2326246 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326247 : term337 = term338.
Proof. exact (@lem2326246 (NUMERAL 0) term57). Qed.
Lemma lem2326248 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326249 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326250 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326249 h1) (fun h1 : term338 = True => @lem2326248)). Qed.
Lemma lem2326251 : term338 = True.
Proof. exact (EQ_MP (@lem2326250) (@lem2326248)). Qed.
Lemma lem2326252 : term337 = True.
Proof. exact (TRANS (@lem2326247) (@lem2326251)). Qed.
Lemma lem2326253 : True = term337.
Proof. exact (SYM (@lem2326252)). Qed.
Lemma lem2326254 : term337.
Proof. exact (EQ_MP (@lem2326253) (@lem0)). Qed.
Lemma lem2326255 : term483 = term486.
Proof. exact (@lem2326244 (@lem2326254)). Qed.
Lemma lem2326257 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2326258 : term349 = term159.
Proof. exact (@lem2326257 term57). Qed.
Lemma lem2326260 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2326261 : term349 = term159.
Proof. exact (@lem2326260 term57). Qed.
Lemma lem2326262 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2326263 : term459 = term453.
Proof. exact (MK_COMB (@lem2326262) (@lem2326261)). Qed.
Lemma lem2326264 : term486 = term482.
Proof. exact (MK_COMB (@lem2326263) (@lem2326258)). Qed.
Lemma lem2326266 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326267 : term482 = term487.
Proof. exact (@lem2326266 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem2326268 : term487 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem2326269 : term482 = False.
Proof. exact (TRANS (@lem2326267) (@lem2326268)). Qed.
Lemma lem2326270 : term486 = False.
Proof. exact (TRANS (@lem2326264) (@lem2326269)). Qed.
Lemma lem2326271 : term483 = False.
Proof. exact (TRANS (@lem2326255) (@lem2326270)). Qed.
Lemma lem2326272 : term482 = False.
Proof. exact (TRANS (@lem2326232) (@lem2326271)). Qed.
Lemma lem2326273 : term481 = False.
Proof. exact (TRANS (@lem2326223) (@lem2326272)). Qed.
Lemma lem2326274 (x : int) (y : int) (h1 : term380 x y) : False.
Proof. exact (EQ_MP (@lem2326273) (@lem2326220 x y h1)). Qed.
Lemma lem2326275 (x : int) (y : int) (h1 : term382 x y) : False.
Proof. exact (or_elim (@lem2325762 x y h1) (fun h0 : term367 x y => @lem2325838 x y h0) (fun h0 : term380 x y => @lem2326274 x y h0)). Qed.
Lemma lem2326276 (x : int) (y : int) (h1 : term397 x y) : term397 x y.
Proof. exact (h1). Qed.
Lemma lem2326277 (x : int) (y : int) (h1 : term397 x y) : term395 x y.
Proof. exact (proj2 (@lem2326276 x y h1)). Qed.
Lemma lem2326280 (x : int) (y : int) (h1 : term397 x y) : term365.
Proof. exact (proj1 (@lem2326277 x y h1)). Qed.
Lemma lem2326282 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2326283 : term365 = term440.
Proof. exact (@lem2326282 term159 term166). Qed.
Lemma lem2326285 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2326286 : term166 = term171.
Proof. exact (@lem2326285 term57). Qed.
Lemma lem2326288 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2326289 : term159 = term315.
Proof. exact (@lem2326288 (NUMERAL 0)). Qed.
Lemma lem2326290 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2326291 : term441 = term442.
Proof. exact (MK_COMB (@lem2326290) (@lem2326289)). Qed.
Lemma lem2326292 : term440 = term443.
Proof. exact (MK_COMB (@lem2326291) (@lem2326286)). Qed.
Lemma lem2326293 : term444.
Proof. exact (@lem1980026 term159 term56 term166 term56). Qed.
Lemma lem2326295 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326296 : term337 = term338.
Proof. exact (@lem2326295 (NUMERAL 0) term57). Qed.
Lemma lem2326297 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326298 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326299 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326298 h1) (fun h1 : term338 = True => @lem2326297)). Qed.
Lemma lem2326300 : term338 = True.
Proof. exact (EQ_MP (@lem2326299) (@lem2326297)). Qed.
Lemma lem2326301 : term337 = True.
Proof. exact (TRANS (@lem2326296) (@lem2326300)). Qed.
Lemma lem2326302 : True = term337.
Proof. exact (SYM (@lem2326301)). Qed.
Lemma lem2326303 : term337.
Proof. exact (EQ_MP (@lem2326302) (@lem0)). Qed.
Lemma lem2326304 : term445.
Proof. exact (@lem2326293 (@lem2326303)). Qed.
Lemma lem2326306 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326307 : term337 = term338.
Proof. exact (@lem2326306 (NUMERAL 0) term57). Qed.
Lemma lem2326308 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326309 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326310 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326309 h1) (fun h1 : term338 = True => @lem2326308)). Qed.
Lemma lem2326311 : term338 = True.
Proof. exact (EQ_MP (@lem2326310) (@lem2326308)). Qed.
Lemma lem2326312 : term337 = True.
Proof. exact (TRANS (@lem2326307) (@lem2326311)). Qed.
Lemma lem2326313 : True = term337.
Proof. exact (SYM (@lem2326312)). Qed.
Lemma lem2326314 : term337.
Proof. exact (EQ_MP (@lem2326313) (@lem0)). Qed.
Lemma lem2326315 : term443 = term446.
Proof. exact (@lem2326304 (@lem2326314)). Qed.
Lemma lem2326317 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2326318 : term174 = term185.
Proof. exact (@lem2326317 term57 term57). Qed.
Lemma lem2326319 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326320 : term182 = term57.
Proof. exact (EQ_MP (@lem2326319) (@lem940073)). Qed.
Lemma lem2326321 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326322 : term180 = term56.
Proof. exact (MK_COMB (@lem2326321) (@lem2326320)). Qed.
Lemma lem2326323 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2326324 : term185 = term166.
Proof. exact (MK_COMB (@lem2326323) (@lem2326322)). Qed.
Lemma lem2326325 : term174 = term166.
Proof. exact (TRANS (@lem2326318) (@lem2326324)). Qed.
Lemma lem2326327 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2326328 : term349 = term159.
Proof. exact (@lem2326327 term57). Qed.
Lemma lem2326329 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2326330 : term447 = term441.
Proof. exact (MK_COMB (@lem2326329) (@lem2326328)). Qed.
Lemma lem2326331 : term446 = term440.
Proof. exact (MK_COMB (@lem2326330) (@lem2326325)). Qed.
Lemma lem2326333 (m : nat) (n : nat) : (term448 m n) = (term449 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2326334 : term440 = term450.
Proof. exact (@lem2326333 (NUMERAL 0) term57). Qed.
Lemma lem2326335 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326336 (h1 : term339 = (BIT1 0)) : (term57 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2326337 : (term339 = (BIT1 0)) = ((term57 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326336 h1) (fun h1 : (term57 = (NUMERAL 0)) = False => @lem2326335)). Qed.
Lemma lem2326338 : (term57 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2326337) (@lem2326335)). Qed.
Lemma lem2326339 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2326340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2326341 : term451 = (and True).
Proof. exact (MK_COMB (@lem2326340) (@lem2326339)). Qed.
Lemma lem2326342 : term450 = (True /\ False).
Proof. exact (MK_COMB (@lem2326341) (@lem2326338)). Qed.
Lemma lem2326344 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2326345 : term450 = False.
Proof. exact (TRANS (@lem2326342) (@lem2326344)). Qed.
Lemma lem2326346 : term440 = False.
Proof. exact (TRANS (@lem2326334) (@lem2326345)). Qed.
Lemma lem2326347 : term446 = False.
Proof. exact (TRANS (@lem2326331) (@lem2326346)). Qed.
Lemma lem2326348 : term443 = False.
Proof. exact (TRANS (@lem2326315) (@lem2326347)). Qed.
Lemma lem2326349 : term440 = False.
Proof. exact (TRANS (@lem2326292) (@lem2326348)). Qed.
Lemma lem2326350 : term365 = False.
Proof. exact (TRANS (@lem2326283) (@lem2326349)). Qed.
Lemma lem2326351 (x : int) (y : int) (h1 : term397 x y) : False.
Proof. exact (EQ_MP (@lem2326350) (@lem2326280 x y h1)). Qed.
Lemma lem2326352 (x : int) (y : int) (h1 : term400 x y) : False.
Proof. exact (or_elim (@lem2325761 x y h1) (fun h0 : term382 x y => @lem2326275 x y h0) (fun h0 : term397 x y => @lem2326351 x y h0)). Qed.
Lemma lem2326353 (x : int) (y : int) (h1 : term437 x y) : term437 x y.
Proof. exact (h1). Qed.
Lemma lem2326354 (x : int) (y : int) (h1 : term430 x y) : term430 x y.
Proof. exact (h1). Qed.
Lemma lem2326355 (x : int) (y : int) (h1 : term426 x y) : term426 x y.
Proof. exact (h1). Qed.
Lemma lem2326356 (x : int) (y : int) (h1 : term426 x y) : term425 x y.
Proof. exact (proj2 (@lem2326355 x y h1)). Qed.
Lemma lem2326358 (x : int) (y : int) (h1 : term426 x y) : term386 x y.
Proof. exact (proj2 (@lem2326356 x y h1)). Qed.
Lemma lem2326359 (x : int) (y : int) (h1 : term426 x y) : term221 x y.
Proof. exact (proj1 (@lem2326356 x y h1)). Qed.
Lemma lem2326361 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2326362 : term452 = term337.
Proof. exact (@lem2326361 term159 term56). Qed.
Lemma lem2326364 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2326365 : term56 = term168.
Proof. exact (@lem2326364 term57). Qed.
Lemma lem2326367 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2326368 : term159 = term315.
Proof. exact (@lem2326367 (NUMERAL 0)). Qed.
Lemma lem2326369 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2326370 : term453 = term454.
Proof. exact (MK_COMB (@lem2326369) (@lem2326368)). Qed.
Lemma lem2326371 : term337 = term455.
Proof. exact (MK_COMB (@lem2326370) (@lem2326365)). Qed.
Lemma lem2326372 : term456.
Proof. exact (@lem1980255 term159 term56 term56 term56). Qed.
Lemma lem2326374 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326375 : term337 = term338.
Proof. exact (@lem2326374 (NUMERAL 0) term57). Qed.
Lemma lem2326376 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326377 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326378 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326377 h1) (fun h1 : term338 = True => @lem2326376)). Qed.
Lemma lem2326379 : term338 = True.
Proof. exact (EQ_MP (@lem2326378) (@lem2326376)). Qed.
Lemma lem2326380 : term337 = True.
Proof. exact (TRANS (@lem2326375) (@lem2326379)). Qed.
Lemma lem2326381 : True = term337.
Proof. exact (SYM (@lem2326380)). Qed.
Lemma lem2326382 : term337.
Proof. exact (EQ_MP (@lem2326381) (@lem0)). Qed.
Lemma lem2326383 : term457.
Proof. exact (@lem2326372 (@lem2326382)). Qed.
Lemma lem2326385 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326386 : term337 = term338.
Proof. exact (@lem2326385 (NUMERAL 0) term57). Qed.
Lemma lem2326387 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326388 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326389 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326388 h1) (fun h1 : term338 = True => @lem2326387)). Qed.
Lemma lem2326390 : term338 = True.
Proof. exact (EQ_MP (@lem2326389) (@lem2326387)). Qed.
Lemma lem2326391 : term337 = True.
Proof. exact (TRANS (@lem2326386) (@lem2326390)). Qed.
Lemma lem2326392 : True = term337.
Proof. exact (SYM (@lem2326391)). Qed.
Lemma lem2326393 : term337.
Proof. exact (EQ_MP (@lem2326392) (@lem0)). Qed.
Lemma lem2326394 : term455 = term458.
Proof. exact (@lem2326383 (@lem2326393)). Qed.
Lemma lem2326396 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2326397 : term179 = term180.
Proof. exact (@lem2326396 term57 term57). Qed.
Lemma lem2326398 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326399 : term182 = term57.
Proof. exact (EQ_MP (@lem2326398) (@lem940073)). Qed.
Lemma lem2326400 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326401 : term180 = term56.
Proof. exact (MK_COMB (@lem2326400) (@lem2326399)). Qed.
Lemma lem2326402 : term179 = term56.
Proof. exact (TRANS (@lem2326397) (@lem2326401)). Qed.
Lemma lem2326404 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2326405 : term349 = term159.
Proof. exact (@lem2326404 term57). Qed.
Lemma lem2326406 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2326407 : term459 = term453.
Proof. exact (MK_COMB (@lem2326406) (@lem2326405)). Qed.
Lemma lem2326408 : term458 = term337.
Proof. exact (MK_COMB (@lem2326407) (@lem2326402)). Qed.
Lemma lem2326410 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326411 : term337 = term338.
Proof. exact (@lem2326410 (NUMERAL 0) term57). Qed.
Lemma lem2326412 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326413 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326414 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326413 h1) (fun h1 : term338 = True => @lem2326412)). Qed.
Lemma lem2326415 : term338 = True.
Proof. exact (EQ_MP (@lem2326414) (@lem2326412)). Qed.
Lemma lem2326416 : term337 = True.
Proof. exact (TRANS (@lem2326411) (@lem2326415)). Qed.
Lemma lem2326417 : term458 = True.
Proof. exact (TRANS (@lem2326408) (@lem2326416)). Qed.
Lemma lem2326418 : term455 = True.
Proof. exact (TRANS (@lem2326394) (@lem2326417)). Qed.
Lemma lem2326419 : term337 = True.
Proof. exact (TRANS (@lem2326371) (@lem2326418)). Qed.
Lemma lem2326420 : term452 = True.
Proof. exact (TRANS (@lem2326362) (@lem2326419)). Qed.
Lemma lem2326421 : True = term452.
Proof. exact (SYM (@lem2326420)). Qed.
Lemma lem2326422 : term452.
Proof. exact (EQ_MP (@lem2326421) (@lem0)). Qed.
Lemma lem2326423 (x : int) (y : int) (h1 : term426 x y) : term488 x y.
Proof. exact (conj (@lem2326422) (@lem2326358 x y h1)). Qed.
Lemma lem2326425 (x : real) (y : real) : term461 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2326426 (x : int) (y : int) : term489 x y.
Proof. exact (@lem2326425 term56 (term417 x y)). Qed.
Lemma lem2326427 (x : int) (y : int) (h1 : term426 x y) : term490 x y.
Proof. exact (@lem2326426 x y (@lem2326423 x y h1)). Qed.
Lemma lem2326428 (x : int) (y : int) : (term491 x y) = (term417 x y).
Proof. exact (@lem1982733 (term417 x y)). Qed.
Lemma lem2326429 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2326430 (x : int) (y : int) : (term492 x y) = (term424 x y).
Proof. exact (MK_COMB (@lem2326429) (@lem2326428 x y)). Qed.
Lemma lem2326431 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2326432 (x : int) (y : int) : (term490 x y) = (term386 x y).
Proof. exact (MK_COMB (@lem2326430 x y) (@lem2326431)). Qed.
Lemma lem2326433 (x : int) (y : int) (h1 : term426 x y) : term386 x y.
Proof. exact (EQ_MP (@lem2326432 x y) (@lem2326427 x y h1)). Qed.
Lemma lem2326435 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2326436 : term452 = term337.
Proof. exact (@lem2326435 term159 term56). Qed.
Lemma lem2326438 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2326439 : term56 = term168.
Proof. exact (@lem2326438 term57). Qed.
Lemma lem2326441 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2326442 : term159 = term315.
Proof. exact (@lem2326441 (NUMERAL 0)). Qed.
Lemma lem2326443 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2326444 : term453 = term454.
Proof. exact (MK_COMB (@lem2326443) (@lem2326442)). Qed.
Lemma lem2326445 : term337 = term455.
Proof. exact (MK_COMB (@lem2326444) (@lem2326439)). Qed.
Lemma lem2326446 : term456.
Proof. exact (@lem1980255 term159 term56 term56 term56). Qed.
Lemma lem2326448 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326449 : term337 = term338.
Proof. exact (@lem2326448 (NUMERAL 0) term57). Qed.
Lemma lem2326450 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326451 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326452 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326451 h1) (fun h1 : term338 = True => @lem2326450)). Qed.
Lemma lem2326453 : term338 = True.
Proof. exact (EQ_MP (@lem2326452) (@lem2326450)). Qed.
Lemma lem2326454 : term337 = True.
Proof. exact (TRANS (@lem2326449) (@lem2326453)). Qed.
Lemma lem2326455 : True = term337.
Proof. exact (SYM (@lem2326454)). Qed.
Lemma lem2326456 : term337.
Proof. exact (EQ_MP (@lem2326455) (@lem0)). Qed.
Lemma lem2326457 : term457.
Proof. exact (@lem2326446 (@lem2326456)). Qed.
Lemma lem2326459 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326460 : term337 = term338.
Proof. exact (@lem2326459 (NUMERAL 0) term57). Qed.
Lemma lem2326461 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326462 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326463 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326462 h1) (fun h1 : term338 = True => @lem2326461)). Qed.
Lemma lem2326464 : term338 = True.
Proof. exact (EQ_MP (@lem2326463) (@lem2326461)). Qed.
Lemma lem2326465 : term337 = True.
Proof. exact (TRANS (@lem2326460) (@lem2326464)). Qed.
Lemma lem2326466 : True = term337.
Proof. exact (SYM (@lem2326465)). Qed.
Lemma lem2326467 : term337.
Proof. exact (EQ_MP (@lem2326466) (@lem0)). Qed.
Lemma lem2326468 : term455 = term458.
Proof. exact (@lem2326457 (@lem2326467)). Qed.
Lemma lem2326470 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2326471 : term179 = term180.
Proof. exact (@lem2326470 term57 term57). Qed.
Lemma lem2326472 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326473 : term182 = term57.
Proof. exact (EQ_MP (@lem2326472) (@lem940073)). Qed.
Lemma lem2326474 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326475 : term180 = term56.
Proof. exact (MK_COMB (@lem2326474) (@lem2326473)). Qed.
Lemma lem2326476 : term179 = term56.
Proof. exact (TRANS (@lem2326471) (@lem2326475)). Qed.
Lemma lem2326478 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2326479 : term349 = term159.
Proof. exact (@lem2326478 term57). Qed.
Lemma lem2326480 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2326481 : term459 = term453.
Proof. exact (MK_COMB (@lem2326480) (@lem2326479)). Qed.
Lemma lem2326482 : term458 = term337.
Proof. exact (MK_COMB (@lem2326481) (@lem2326476)). Qed.
Lemma lem2326484 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326485 : term337 = term338.
Proof. exact (@lem2326484 (NUMERAL 0) term57). Qed.
Lemma lem2326486 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326487 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326488 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326487 h1) (fun h1 : term338 = True => @lem2326486)). Qed.
Lemma lem2326489 : term338 = True.
Proof. exact (EQ_MP (@lem2326488) (@lem2326486)). Qed.
Lemma lem2326490 : term337 = True.
Proof. exact (TRANS (@lem2326485) (@lem2326489)). Qed.
Lemma lem2326491 : term458 = True.
Proof. exact (TRANS (@lem2326482) (@lem2326490)). Qed.
Lemma lem2326492 : term455 = True.
Proof. exact (TRANS (@lem2326468) (@lem2326491)). Qed.
Lemma lem2326493 : term337 = True.
Proof. exact (TRANS (@lem2326445) (@lem2326492)). Qed.
Lemma lem2326494 : term452 = True.
Proof. exact (TRANS (@lem2326436) (@lem2326493)). Qed.
Lemma lem2326495 : True = term452.
Proof. exact (SYM (@lem2326494)). Qed.
Lemma lem2326496 : term452.
Proof. exact (EQ_MP (@lem2326495) (@lem0)). Qed.
Lemma lem2326497 (x : int) (y : int) (h1 : term426 x y) : term493 x y.
Proof. exact (conj (@lem2326496) (@lem2326359 x y h1)). Qed.
Lemma lem2326499 (x : real) (y : real) : term461 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2326500 (x : int) (y : int) : term494 x y.
Proof. exact (@lem2326499 term56 (term218 x y)). Qed.
Lemma lem2326501 (x : int) (y : int) (h1 : term426 x y) : term495 x y.
Proof. exact (@lem2326500 x y (@lem2326497 x y h1)). Qed.
Lemma lem2326502 (x : int) (y : int) : (term496 x y) = (term218 x y).
Proof. exact (@lem1982733 (term218 x y)). Qed.
Lemma lem2326503 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2326504 (x : int) (y : int) : (term497 x y) = (term220 x y).
Proof. exact (MK_COMB (@lem2326503) (@lem2326502 x y)). Qed.
Lemma lem2326505 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2326506 (x : int) (y : int) : (term495 x y) = (term221 x y).
Proof. exact (MK_COMB (@lem2326504 x y) (@lem2326505)). Qed.
Lemma lem2326507 (x : int) (y : int) (h1 : term426 x y) : term221 x y.
Proof. exact (EQ_MP (@lem2326506 x y) (@lem2326501 x y h1)). Qed.
Lemma lem2326508 (x : int) (y : int) (h1 : term426 x y) : term425 x y.
Proof. exact (conj (@lem2326507 x y h1) (@lem2326433 x y h1)). Qed.
Lemma lem2326510 (x : real) (y : real) : term498 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2326511 (x : int) (y : int) : term499 x y.
Proof. exact (@lem2326510 (term218 x y) (term417 x y)). Qed.
Lemma lem2326512 (x : int) (y : int) (h1 : term426 x y) : term500 x y.
Proof. exact (@lem2326511 x y (@lem2326508 x y h1)). Qed.
Lemma lem2326513 (x : int) (y : int) : (term501 x y) = (term502 x y).
Proof. exact (@lem1982753 (real_of_int x) (term156 x) (term201 y) (term503 y)). Qed.
Lemma lem2326514 (x : int) : (term329 x) = (term330 x).
Proof. exact (@lem1982715 term166 (real_of_int x)). Qed.
Lemma lem2326516 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2326517 : term56 = term168.
Proof. exact (@lem2326516 term57). Qed.
Lemma lem2326519 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2326520 : term166 = term171.
Proof. exact (@lem2326519 term57). Qed.
Lemma lem2326521 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2326522 : term331 = term332.
Proof. exact (MK_COMB (@lem2326521) (@lem2326520)). Qed.
Lemma lem2326523 : term333 = term334.
Proof. exact (MK_COMB (@lem2326522) (@lem2326517)). Qed.
Lemma lem2326524 : term335.
Proof. exact (@lem1981473 term166 term56 term56 term56 term159 term56). Qed.
Lemma lem2326526 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326527 : term337 = term338.
Proof. exact (@lem2326526 (NUMERAL 0) term57). Qed.
Lemma lem2326528 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326529 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326530 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326529 h1) (fun h1 : term338 = True => @lem2326528)). Qed.
Lemma lem2326531 : term338 = True.
Proof. exact (EQ_MP (@lem2326530) (@lem2326528)). Qed.
Lemma lem2326532 : term337 = True.
Proof. exact (TRANS (@lem2326527) (@lem2326531)). Qed.
Lemma lem2326533 : True = term337.
Proof. exact (SYM (@lem2326532)). Qed.
Lemma lem2326534 : term337.
Proof. exact (EQ_MP (@lem2326533) (@lem0)). Qed.
Lemma lem2326535 : term340.
Proof. exact (@lem2326524 (@lem2326534)). Qed.
Lemma lem2326537 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326538 : term337 = term338.
Proof. exact (@lem2326537 (NUMERAL 0) term57). Qed.
Lemma lem2326539 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326540 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326541 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326540 h1) (fun h1 : term338 = True => @lem2326539)). Qed.
Lemma lem2326542 : term338 = True.
Proof. exact (EQ_MP (@lem2326541) (@lem2326539)). Qed.
Lemma lem2326543 : term337 = True.
Proof. exact (TRANS (@lem2326538) (@lem2326542)). Qed.
Lemma lem2326544 : True = term337.
Proof. exact (SYM (@lem2326543)). Qed.
Lemma lem2326545 : term337.
Proof. exact (EQ_MP (@lem2326544) (@lem0)). Qed.
Lemma lem2326546 : term341.
Proof. exact (@lem2326535 (@lem2326545)). Qed.
Lemma lem2326548 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326549 : term337 = term338.
Proof. exact (@lem2326548 (NUMERAL 0) term57). Qed.
Lemma lem2326550 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326551 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326552 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326551 h1) (fun h1 : term338 = True => @lem2326550)). Qed.
Lemma lem2326553 : term338 = True.
Proof. exact (EQ_MP (@lem2326552) (@lem2326550)). Qed.
Lemma lem2326554 : term337 = True.
Proof. exact (TRANS (@lem2326549) (@lem2326553)). Qed.
Lemma lem2326555 : True = term337.
Proof. exact (SYM (@lem2326554)). Qed.
Lemma lem2326556 : term337.
Proof. exact (EQ_MP (@lem2326555) (@lem0)). Qed.
Lemma lem2326557 : term342.
Proof. exact (@lem2326546 (@lem2326556)). Qed.
Lemma lem2326559 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2326560 : term179 = term180.
Proof. exact (@lem2326559 term57 term57). Qed.
Lemma lem2326561 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326562 : term182 = term57.
Proof. exact (EQ_MP (@lem2326561) (@lem940073)). Qed.
Lemma lem2326563 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326564 : term180 = term56.
Proof. exact (MK_COMB (@lem2326563) (@lem2326562)). Qed.
Lemma lem2326565 : term179 = term56.
Proof. exact (TRANS (@lem2326560) (@lem2326564)). Qed.
Lemma lem2326567 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2326568 : term174 = term185.
Proof. exact (@lem2326567 term57 term57). Qed.
Lemma lem2326569 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326570 : term182 = term57.
Proof. exact (EQ_MP (@lem2326569) (@lem940073)). Qed.
Lemma lem2326571 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326572 : term180 = term56.
Proof. exact (MK_COMB (@lem2326571) (@lem2326570)). Qed.
Lemma lem2326573 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2326574 : term185 = term166.
Proof. exact (MK_COMB (@lem2326573) (@lem2326572)). Qed.
Lemma lem2326575 : term174 = term166.
Proof. exact (TRANS (@lem2326568) (@lem2326574)). Qed.
Lemma lem2326576 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2326577 : term343 = term331.
Proof. exact (MK_COMB (@lem2326576) (@lem2326575)). Qed.
Lemma lem2326578 : term344 = term333.
Proof. exact (MK_COMB (@lem2326577) (@lem2326565)). Qed.
Lemma lem2326580 (m : nat) : (term345 m) = term159.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2326581 : term333 = term159.
Proof. exact (@lem2326580 term57). Qed.
Lemma lem2326582 : term344 = term159.
Proof. exact (TRANS (@lem2326578) (@lem2326581)). Qed.
Lemma lem2326583 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2326584 : term346 = term347.
Proof. exact (MK_COMB (@lem2326583) (@lem2326582)). Qed.
Lemma lem2326585 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2326586 : term348 = term349.
Proof. exact (MK_COMB (@lem2326584) (@lem2326585)). Qed.
Lemma lem2326588 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2326589 : term349 = term159.
Proof. exact (@lem2326588 term57). Qed.
Lemma lem2326590 : term348 = term159.
Proof. exact (TRANS (@lem2326586) (@lem2326589)). Qed.
Lemma lem2326592 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2326593 : term179 = term180.
Proof. exact (@lem2326592 term57 term57). Qed.
Lemma lem2326594 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326595 : term182 = term57.
Proof. exact (EQ_MP (@lem2326594) (@lem940073)). Qed.
Lemma lem2326596 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326597 : term180 = term56.
Proof. exact (MK_COMB (@lem2326596) (@lem2326595)). Qed.
Lemma lem2326598 : term179 = term56.
Proof. exact (TRANS (@lem2326593) (@lem2326597)). Qed.
Lemma lem2326599 : term347 = term347.
Proof. exact (eq_refl term347). Qed.
Lemma lem2326600 : term351 = term349.
Proof. exact (MK_COMB (@lem2326599) (@lem2326598)). Qed.
Lemma lem2326602 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2326603 : term349 = term159.
Proof. exact (@lem2326602 term57). Qed.
Lemma lem2326604 : term351 = term159.
Proof. exact (TRANS (@lem2326600) (@lem2326603)). Qed.
Lemma lem2326605 : term159 = term351.
Proof. exact (SYM (@lem2326604)). Qed.
Lemma lem2326606 : term348 = term351.
Proof. exact (TRANS (@lem2326590) (@lem2326605)). Qed.
Lemma lem2326607 : term334 = term315.
Proof. exact (@lem2326557 (@lem2326606)). Qed.
Lemma lem2326608 : term333 = term315.
Proof. exact (TRANS (@lem2326523) (@lem2326607)). Qed.
Lemma lem2326610 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2326611 : term315 = term159.
Proof. exact (@lem2326610 term159). Qed.
Lemma lem2326612 : term333 = term159.
Proof. exact (TRANS (@lem2326608) (@lem2326611)). Qed.
Lemma lem2326613 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2326614 : term352 = term347.
Proof. exact (MK_COMB (@lem2326613) (@lem2326612)). Qed.
Lemma lem2326615 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2326616 (x : int) : (term330 x) = (term353 x).
Proof. exact (MK_COMB (@lem2326614) (@lem2326615 x)). Qed.
Lemma lem2326617 (x : int) : (term329 x) = (term353 x).
Proof. exact (TRANS (@lem2326514 x) (@lem2326616 x)). Qed.
Lemma lem2326618 (x : int) : (term353 x) = term159.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2326619 (x : int) : (term329 x) = term159.
Proof. exact (TRANS (@lem2326617 x) (@lem2326618 x)). Qed.
Lemma lem2326620 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2326621 (x : int) : (term354 x) = term355.
Proof. exact (MK_COMB (@lem2326620) (@lem2326619 x)). Qed.
Lemma lem2326622 (y : int) : (term504 y) = (term505 y).
Proof. exact (@lem1982753 (term156 y) (real_of_int y) term166 term166). Qed.
Lemma lem2326623 (y : int) : (term389 y) = (term330 y).
Proof. exact (@lem1982713 term166 (real_of_int y)). Qed.
Lemma lem2326625 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2326626 : term56 = term168.
Proof. exact (@lem2326625 term57). Qed.
Lemma lem2326628 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2326629 : term166 = term171.
Proof. exact (@lem2326628 term57). Qed.
Lemma lem2326630 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2326631 : term331 = term332.
Proof. exact (MK_COMB (@lem2326630) (@lem2326629)). Qed.
Lemma lem2326632 : term333 = term334.
Proof. exact (MK_COMB (@lem2326631) (@lem2326626)). Qed.
Lemma lem2326633 : term335.
Proof. exact (@lem1981473 term166 term56 term56 term56 term159 term56). Qed.
Lemma lem2326635 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326636 : term337 = term338.
Proof. exact (@lem2326635 (NUMERAL 0) term57). Qed.
Lemma lem2326637 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326638 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326639 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326638 h1) (fun h1 : term338 = True => @lem2326637)). Qed.
Lemma lem2326640 : term338 = True.
Proof. exact (EQ_MP (@lem2326639) (@lem2326637)). Qed.
Lemma lem2326641 : term337 = True.
Proof. exact (TRANS (@lem2326636) (@lem2326640)). Qed.
Lemma lem2326642 : True = term337.
Proof. exact (SYM (@lem2326641)). Qed.
Lemma lem2326643 : term337.
Proof. exact (EQ_MP (@lem2326642) (@lem0)). Qed.
Lemma lem2326644 : term340.
Proof. exact (@lem2326633 (@lem2326643)). Qed.
Lemma lem2326646 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326647 : term337 = term338.
Proof. exact (@lem2326646 (NUMERAL 0) term57). Qed.
Lemma lem2326648 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326649 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326650 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326649 h1) (fun h1 : term338 = True => @lem2326648)). Qed.
Lemma lem2326651 : term338 = True.
Proof. exact (EQ_MP (@lem2326650) (@lem2326648)). Qed.
Lemma lem2326652 : term337 = True.
Proof. exact (TRANS (@lem2326647) (@lem2326651)). Qed.
Lemma lem2326653 : True = term337.
Proof. exact (SYM (@lem2326652)). Qed.
Lemma lem2326654 : term337.
Proof. exact (EQ_MP (@lem2326653) (@lem0)). Qed.
Lemma lem2326655 : term341.
Proof. exact (@lem2326644 (@lem2326654)). Qed.
Lemma lem2326657 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326658 : term337 = term338.
Proof. exact (@lem2326657 (NUMERAL 0) term57). Qed.
Lemma lem2326659 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326660 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326661 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326660 h1) (fun h1 : term338 = True => @lem2326659)). Qed.
Lemma lem2326662 : term338 = True.
Proof. exact (EQ_MP (@lem2326661) (@lem2326659)). Qed.
Lemma lem2326663 : term337 = True.
Proof. exact (TRANS (@lem2326658) (@lem2326662)). Qed.
Lemma lem2326664 : True = term337.
Proof. exact (SYM (@lem2326663)). Qed.
Lemma lem2326665 : term337.
Proof. exact (EQ_MP (@lem2326664) (@lem0)). Qed.
Lemma lem2326666 : term342.
Proof. exact (@lem2326655 (@lem2326665)). Qed.
Lemma lem2326668 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2326669 : term179 = term180.
Proof. exact (@lem2326668 term57 term57). Qed.
Lemma lem2326670 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326671 : term182 = term57.
Proof. exact (EQ_MP (@lem2326670) (@lem940073)). Qed.
Lemma lem2326672 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326673 : term180 = term56.
Proof. exact (MK_COMB (@lem2326672) (@lem2326671)). Qed.
Lemma lem2326674 : term179 = term56.
Proof. exact (TRANS (@lem2326669) (@lem2326673)). Qed.
Lemma lem2326676 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2326677 : term174 = term185.
Proof. exact (@lem2326676 term57 term57). Qed.
Lemma lem2326678 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326679 : term182 = term57.
Proof. exact (EQ_MP (@lem2326678) (@lem940073)). Qed.
Lemma lem2326680 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326681 : term180 = term56.
Proof. exact (MK_COMB (@lem2326680) (@lem2326679)). Qed.
Lemma lem2326682 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2326683 : term185 = term166.
Proof. exact (MK_COMB (@lem2326682) (@lem2326681)). Qed.
Lemma lem2326684 : term174 = term166.
Proof. exact (TRANS (@lem2326677) (@lem2326683)). Qed.
Lemma lem2326685 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2326686 : term343 = term331.
Proof. exact (MK_COMB (@lem2326685) (@lem2326684)). Qed.
Lemma lem2326687 : term344 = term333.
Proof. exact (MK_COMB (@lem2326686) (@lem2326674)). Qed.
Lemma lem2326689 (m : nat) : (term345 m) = term159.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2326690 : term333 = term159.
Proof. exact (@lem2326689 term57). Qed.
Lemma lem2326691 : term344 = term159.
Proof. exact (TRANS (@lem2326687) (@lem2326690)). Qed.
Lemma lem2326692 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2326693 : term346 = term347.
Proof. exact (MK_COMB (@lem2326692) (@lem2326691)). Qed.
Lemma lem2326694 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2326695 : term348 = term349.
Proof. exact (MK_COMB (@lem2326693) (@lem2326694)). Qed.
Lemma lem2326697 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2326698 : term349 = term159.
Proof. exact (@lem2326697 term57). Qed.
Lemma lem2326699 : term348 = term159.
Proof. exact (TRANS (@lem2326695) (@lem2326698)). Qed.
Lemma lem2326701 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2326702 : term179 = term180.
Proof. exact (@lem2326701 term57 term57). Qed.
Lemma lem2326703 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326704 : term182 = term57.
Proof. exact (EQ_MP (@lem2326703) (@lem940073)). Qed.
Lemma lem2326705 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326706 : term180 = term56.
Proof. exact (MK_COMB (@lem2326705) (@lem2326704)). Qed.
Lemma lem2326707 : term179 = term56.
Proof. exact (TRANS (@lem2326702) (@lem2326706)). Qed.
Lemma lem2326708 : term347 = term347.
Proof. exact (eq_refl term347). Qed.
Lemma lem2326709 : term351 = term349.
Proof. exact (MK_COMB (@lem2326708) (@lem2326707)). Qed.
Lemma lem2326711 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2326712 : term349 = term159.
Proof. exact (@lem2326711 term57). Qed.
Lemma lem2326713 : term351 = term159.
Proof. exact (TRANS (@lem2326709) (@lem2326712)). Qed.
Lemma lem2326714 : term159 = term351.
Proof. exact (SYM (@lem2326713)). Qed.
Lemma lem2326715 : term348 = term351.
Proof. exact (TRANS (@lem2326699) (@lem2326714)). Qed.
Lemma lem2326716 : term334 = term315.
Proof. exact (@lem2326666 (@lem2326715)). Qed.
Lemma lem2326717 : term333 = term315.
Proof. exact (TRANS (@lem2326632) (@lem2326716)). Qed.
Lemma lem2326719 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2326720 : term315 = term159.
Proof. exact (@lem2326719 term159). Qed.
Lemma lem2326721 : term333 = term159.
Proof. exact (TRANS (@lem2326717) (@lem2326720)). Qed.
Lemma lem2326722 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2326723 : term352 = term347.
Proof. exact (MK_COMB (@lem2326722) (@lem2326721)). Qed.
Lemma lem2326724 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2326725 (y : int) : (term330 y) = (term353 y).
Proof. exact (MK_COMB (@lem2326723) (@lem2326724 y)). Qed.
Lemma lem2326726 (y : int) : (term389 y) = (term353 y).
Proof. exact (TRANS (@lem2326623 y) (@lem2326725 y)). Qed.
Lemma lem2326727 (y : int) : (term353 y) = term159.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2326728 (y : int) : (term389 y) = term159.
Proof. exact (TRANS (@lem2326726 y) (@lem2326727 y)). Qed.
Lemma lem2326729 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2326730 (y : int) : (term390 y) = term355.
Proof. exact (MK_COMB (@lem2326729) (@lem2326728 y)). Qed.
Lemma lem2326732 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2326733 : term166 = term171.
Proof. exact (@lem2326732 term57). Qed.
Lemma lem2326735 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2326736 : term166 = term171.
Proof. exact (@lem2326735 term57). Qed.
Lemma lem2326737 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2326738 : term331 = term332.
Proof. exact (MK_COMB (@lem2326737) (@lem2326736)). Qed.
Lemma lem2326739 : term506 = term507.
Proof. exact (MK_COMB (@lem2326738) (@lem2326733)). Qed.
Lemma lem2326740 : term508.
Proof. exact (@lem1981473 term166 term56 term166 term56 term509 term56). Qed.
Lemma lem2326742 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326743 : term337 = term338.
Proof. exact (@lem2326742 (NUMERAL 0) term57). Qed.
Lemma lem2326744 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326745 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326746 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326745 h1) (fun h1 : term338 = True => @lem2326744)). Qed.
Lemma lem2326747 : term338 = True.
Proof. exact (EQ_MP (@lem2326746) (@lem2326744)). Qed.
Lemma lem2326748 : term337 = True.
Proof. exact (TRANS (@lem2326743) (@lem2326747)). Qed.
Lemma lem2326749 : True = term337.
Proof. exact (SYM (@lem2326748)). Qed.
Lemma lem2326750 : term337.
Proof. exact (EQ_MP (@lem2326749) (@lem0)). Qed.
Lemma lem2326751 : term510.
Proof. exact (@lem2326740 (@lem2326750)). Qed.
Lemma lem2326753 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326754 : term337 = term338.
Proof. exact (@lem2326753 (NUMERAL 0) term57). Qed.
Lemma lem2326755 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326756 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326757 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326756 h1) (fun h1 : term338 = True => @lem2326755)). Qed.
Lemma lem2326758 : term338 = True.
Proof. exact (EQ_MP (@lem2326757) (@lem2326755)). Qed.
Lemma lem2326759 : term337 = True.
Proof. exact (TRANS (@lem2326754) (@lem2326758)). Qed.
Lemma lem2326760 : True = term337.
Proof. exact (SYM (@lem2326759)). Qed.
Lemma lem2326761 : term337.
Proof. exact (EQ_MP (@lem2326760) (@lem0)). Qed.
Lemma lem2326762 : term511.
Proof. exact (@lem2326751 (@lem2326761)). Qed.
Lemma lem2326764 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326765 : term337 = term338.
Proof. exact (@lem2326764 (NUMERAL 0) term57). Qed.
Lemma lem2326766 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326767 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326768 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326767 h1) (fun h1 : term338 = True => @lem2326766)). Qed.
Lemma lem2326769 : term338 = True.
Proof. exact (EQ_MP (@lem2326768) (@lem2326766)). Qed.
Lemma lem2326770 : term337 = True.
Proof. exact (TRANS (@lem2326765) (@lem2326769)). Qed.
Lemma lem2326771 : True = term337.
Proof. exact (SYM (@lem2326770)). Qed.
Lemma lem2326772 : term337.
Proof. exact (EQ_MP (@lem2326771) (@lem0)). Qed.
Lemma lem2326773 : term512.
Proof. exact (@lem2326762 (@lem2326772)). Qed.
Lemma lem2326775 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2326776 : term174 = term185.
Proof. exact (@lem2326775 term57 term57). Qed.
Lemma lem2326777 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326778 : term182 = term57.
Proof. exact (EQ_MP (@lem2326777) (@lem940073)). Qed.
Lemma lem2326779 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326780 : term180 = term56.
Proof. exact (MK_COMB (@lem2326779) (@lem2326778)). Qed.
Lemma lem2326781 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2326782 : term185 = term166.
Proof. exact (MK_COMB (@lem2326781) (@lem2326780)). Qed.
Lemma lem2326783 : term174 = term166.
Proof. exact (TRANS (@lem2326776) (@lem2326782)). Qed.
Lemma lem2326785 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2326786 : term174 = term185.
Proof. exact (@lem2326785 term57 term57). Qed.
Lemma lem2326787 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326788 : term182 = term57.
Proof. exact (EQ_MP (@lem2326787) (@lem940073)). Qed.
Lemma lem2326789 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326790 : term180 = term56.
Proof. exact (MK_COMB (@lem2326789) (@lem2326788)). Qed.
Lemma lem2326791 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2326792 : term185 = term166.
Proof. exact (MK_COMB (@lem2326791) (@lem2326790)). Qed.
Lemma lem2326793 : term174 = term166.
Proof. exact (TRANS (@lem2326786) (@lem2326792)). Qed.
Lemma lem2326794 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2326795 : term343 = term331.
Proof. exact (MK_COMB (@lem2326794) (@lem2326793)). Qed.
Lemma lem2326796 : term513 = term506.
Proof. exact (MK_COMB (@lem2326795) (@lem2326783)). Qed.
Lemma lem2326797 : term506 = term514.
Proof. exact (@lem1367763 term57 term57). Qed.
Lemma lem2326798 : term515 = term516.
Proof. exact (@lem706885). Qed.
Lemma lem2326799 : (term515 = term516) = (term517 = term518).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term516). Qed.
Lemma lem2326800 : term517 = term518.
Proof. exact (EQ_MP (@lem2326799) (@lem2326798)). Qed.
Lemma lem2326801 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326802 : term519 = term520.
Proof. exact (MK_COMB (@lem2326801) (@lem2326800)). Qed.
Lemma lem2326803 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2326804 : term514 = term509.
Proof. exact (MK_COMB (@lem2326803) (@lem2326802)). Qed.
Lemma lem2326805 : term506 = term509.
Proof. exact (TRANS (@lem2326797) (@lem2326804)). Qed.
Lemma lem2326806 : term513 = term509.
Proof. exact (TRANS (@lem2326796) (@lem2326805)). Qed.
Lemma lem2326807 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2326808 : term521 = term522.
Proof. exact (MK_COMB (@lem2326807) (@lem2326806)). Qed.
Lemma lem2326809 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem2326810 : term523 = term524.
Proof. exact (MK_COMB (@lem2326808) (@lem2326809)). Qed.
Lemma lem2326812 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2326813 : term524 = term525.
Proof. exact (@lem2326812 term518 term57). Qed.
Lemma lem2326814 : term526 = term516.
Proof. exact (@lem996237 term516). Qed.
Lemma lem2326815 : (term526 = term516) = (term527 = term518).
Proof. exact (@lem1007663 term516 (BIT1 0) term516). Qed.
Lemma lem2326816 : term527 = term518.
Proof. exact (EQ_MP (@lem2326815) (@lem2326814)). Qed.
Lemma lem2326817 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326818 : term528 = term520.
Proof. exact (MK_COMB (@lem2326817) (@lem2326816)). Qed.
Lemma lem2326819 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2326820 : term525 = term509.
Proof. exact (MK_COMB (@lem2326819) (@lem2326818)). Qed.
Lemma lem2326821 : term524 = term509.
Proof. exact (TRANS (@lem2326813) (@lem2326820)). Qed.
Lemma lem2326822 : term523 = term509.
Proof. exact (TRANS (@lem2326810) (@lem2326821)). Qed.
Lemma lem2326824 (m : nat) (n : nat) : (term177 m n) = (term178 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2326825 : term179 = term180.
Proof. exact (@lem2326824 term57 term57). Qed.
Lemma lem2326826 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326827 : term182 = term57.
Proof. exact (EQ_MP (@lem2326826) (@lem940073)). Qed.
Lemma lem2326828 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326829 : term180 = term56.
Proof. exact (MK_COMB (@lem2326828) (@lem2326827)). Qed.
Lemma lem2326830 : term179 = term56.
Proof. exact (TRANS (@lem2326825) (@lem2326829)). Qed.
Lemma lem2326831 : term522 = term522.
Proof. exact (eq_refl term522). Qed.
Lemma lem2326832 : term529 = term524.
Proof. exact (MK_COMB (@lem2326831) (@lem2326830)). Qed.
Lemma lem2326834 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2326835 : term524 = term525.
Proof. exact (@lem2326834 term518 term57). Qed.
Lemma lem2326836 : term526 = term516.
Proof. exact (@lem996237 term516). Qed.
Lemma lem2326837 : (term526 = term516) = (term527 = term518).
Proof. exact (@lem1007663 term516 (BIT1 0) term516). Qed.
Lemma lem2326838 : term527 = term518.
Proof. exact (EQ_MP (@lem2326837) (@lem2326836)). Qed.
Lemma lem2326839 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326840 : term528 = term520.
Proof. exact (MK_COMB (@lem2326839) (@lem2326838)). Qed.
Lemma lem2326841 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2326842 : term525 = term509.
Proof. exact (MK_COMB (@lem2326841) (@lem2326840)). Qed.
Lemma lem2326843 : term524 = term509.
Proof. exact (TRANS (@lem2326835) (@lem2326842)). Qed.
Lemma lem2326844 : term529 = term509.
Proof. exact (TRANS (@lem2326832) (@lem2326843)). Qed.
Lemma lem2326845 : term509 = term529.
Proof. exact (SYM (@lem2326844)). Qed.
Lemma lem2326846 : term523 = term529.
Proof. exact (TRANS (@lem2326822) (@lem2326845)). Qed.
Lemma lem2326847 : term507 = term530.
Proof. exact (@lem2326773 (@lem2326846)). Qed.
Lemma lem2326848 : term506 = term530.
Proof. exact (TRANS (@lem2326739) (@lem2326847)). Qed.
Lemma lem2326850 (x : real) : (term188 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2326851 : term530 = term509.
Proof. exact (@lem2326850 term509). Qed.
Lemma lem2326852 : term506 = term509.
Proof. exact (TRANS (@lem2326848) (@lem2326851)). Qed.
Lemma lem2326853 (y : int) : (term505 y) = term531.
Proof. exact (MK_COMB (@lem2326730 y) (@lem2326852)). Qed.
Lemma lem2326854 (y : int) : (term504 y) = term531.
Proof. exact (TRANS (@lem2326622 y) (@lem2326853 y)). Qed.
Lemma lem2326855 : term531 = term509.
Proof. exact (@lem1982721 term509). Qed.
Lemma lem2326856 (y : int) : (term504 y) = term509.
Proof. exact (TRANS (@lem2326854 y) (@lem2326855)). Qed.
Lemma lem2326857 (x : int) (y : int) : (term502 x y) = term531.
Proof. exact (MK_COMB (@lem2326621 x) (@lem2326856 y)). Qed.
Lemma lem2326858 (x : int) (y : int) : (term501 x y) = term531.
Proof. exact (TRANS (@lem2326513 x y) (@lem2326857 x y)). Qed.
Lemma lem2326859 : term531 = term509.
Proof. exact (@lem1982721 term509). Qed.
Lemma lem2326860 (x : int) (y : int) : (term501 x y) = term509.
Proof. exact (TRANS (@lem2326858 x y) (@lem2326859)). Qed.
Lemma lem2326861 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2326862 (x : int) (y : int) : (term532 x y) = term533.
Proof. exact (MK_COMB (@lem2326861) (@lem2326860 x y)). Qed.
Lemma lem2326863 : term159 = term159.
Proof. exact (eq_refl term159). Qed.
Lemma lem2326864 (x : int) (y : int) : (term500 x y) = term534.
Proof. exact (MK_COMB (@lem2326862 x y) (@lem2326863)). Qed.
Lemma lem2326865 (x : int) (y : int) (h1 : term426 x y) : term534.
Proof. exact (EQ_MP (@lem2326864 x y) (@lem2326512 x y h1)). Qed.
Lemma lem2326867 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2326868 : term534 = term535.
Proof. exact (@lem2326867 term159 term509). Qed.
Lemma lem2326870 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2326871 : term509 = term530.
Proof. exact (@lem2326870 term518). Qed.
Lemma lem2326873 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2326874 : term159 = term315.
Proof. exact (@lem2326873 (NUMERAL 0)). Qed.
Lemma lem2326875 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2326876 : term441 = term442.
Proof. exact (MK_COMB (@lem2326875) (@lem2326874)). Qed.
Lemma lem2326877 : term535 = term536.
Proof. exact (MK_COMB (@lem2326876) (@lem2326871)). Qed.
Lemma lem2326878 : term537.
Proof. exact (@lem1980026 term159 term56 term509 term56). Qed.
Lemma lem2326880 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326881 : term337 = term338.
Proof. exact (@lem2326880 (NUMERAL 0) term57). Qed.
Lemma lem2326882 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326883 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326884 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326883 h1) (fun h1 : term338 = True => @lem2326882)). Qed.
Lemma lem2326885 : term338 = True.
Proof. exact (EQ_MP (@lem2326884) (@lem2326882)). Qed.
Lemma lem2326886 : term337 = True.
Proof. exact (TRANS (@lem2326881) (@lem2326885)). Qed.
Lemma lem2326887 : True = term337.
Proof. exact (SYM (@lem2326886)). Qed.
Lemma lem2326888 : term337.
Proof. exact (EQ_MP (@lem2326887) (@lem0)). Qed.
Lemma lem2326889 : term538.
Proof. exact (@lem2326878 (@lem2326888)). Qed.
Lemma lem2326891 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326892 : term337 = term338.
Proof. exact (@lem2326891 (NUMERAL 0) term57). Qed.
Lemma lem2326893 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326894 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326895 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326894 h1) (fun h1 : term338 = True => @lem2326893)). Qed.
Lemma lem2326896 : term338 = True.
Proof. exact (EQ_MP (@lem2326895) (@lem2326893)). Qed.
Lemma lem2326897 : term337 = True.
Proof. exact (TRANS (@lem2326892) (@lem2326896)). Qed.
Lemma lem2326898 : True = term337.
Proof. exact (SYM (@lem2326897)). Qed.
Lemma lem2326899 : term337.
Proof. exact (EQ_MP (@lem2326898) (@lem0)). Qed.
Lemma lem2326900 : term536 = term539.
Proof. exact (@lem2326889 (@lem2326899)). Qed.
Lemma lem2326902 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2326903 : term524 = term525.
Proof. exact (@lem2326902 term518 term57). Qed.
Lemma lem2326904 : term526 = term516.
Proof. exact (@lem996237 term516). Qed.
Lemma lem2326905 : (term526 = term516) = (term527 = term518).
Proof. exact (@lem1007663 term516 (BIT1 0) term516). Qed.
Lemma lem2326906 : term527 = term518.
Proof. exact (EQ_MP (@lem2326905) (@lem2326904)). Qed.
Lemma lem2326907 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326908 : term528 = term520.
Proof. exact (MK_COMB (@lem2326907) (@lem2326906)). Qed.
Lemma lem2326909 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2326910 : term525 = term509.
Proof. exact (MK_COMB (@lem2326909) (@lem2326908)). Qed.
Lemma lem2326911 : term524 = term509.
Proof. exact (TRANS (@lem2326903) (@lem2326910)). Qed.
Lemma lem2326913 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2326914 : term349 = term159.
Proof. exact (@lem2326913 term57). Qed.
Lemma lem2326915 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2326916 : term447 = term441.
Proof. exact (MK_COMB (@lem2326915) (@lem2326914)). Qed.
Lemma lem2326917 : term539 = term535.
Proof. exact (MK_COMB (@lem2326916) (@lem2326911)). Qed.
Lemma lem2326919 (m : nat) (n : nat) : (term448 m n) = (term449 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2326920 : term535 = term540.
Proof. exact (@lem2326919 (NUMERAL 0) term518). Qed.
Lemma lem2326921 : term541 = term516.
Proof. exact (@lem912803). Qed.
Lemma lem2326922 (h1 : term541 = term516) : (term518 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term516 h1). Qed.
Lemma lem2326923 : (term541 = term516) = ((term518 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term541 = term516 => @lem2326922 h1) (fun h1 : (term518 = (NUMERAL 0)) = False => @lem2326921)). Qed.
Lemma lem2326924 : (term518 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2326923) (@lem2326921)). Qed.
Lemma lem2326925 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2326926 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2326927 : term451 = (and True).
Proof. exact (MK_COMB (@lem2326926) (@lem2326925)). Qed.
Lemma lem2326928 : term540 = (True /\ False).
Proof. exact (MK_COMB (@lem2326927) (@lem2326924)). Qed.
Lemma lem2326930 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2326931 : term540 = False.
Proof. exact (TRANS (@lem2326928) (@lem2326930)). Qed.
Lemma lem2326932 : term535 = False.
Proof. exact (TRANS (@lem2326920) (@lem2326931)). Qed.
Lemma lem2326933 : term539 = False.
Proof. exact (TRANS (@lem2326917) (@lem2326932)). Qed.
Lemma lem2326934 : term536 = False.
Proof. exact (TRANS (@lem2326900) (@lem2326933)). Qed.
Lemma lem2326935 : term535 = False.
Proof. exact (TRANS (@lem2326877) (@lem2326934)). Qed.
Lemma lem2326936 : term534 = False.
Proof. exact (TRANS (@lem2326868) (@lem2326935)). Qed.
Lemma lem2326937 (x : int) (y : int) (h1 : term426 x y) : False.
Proof. exact (EQ_MP (@lem2326936) (@lem2326865 x y h1)). Qed.
Lemma lem2326938 (x : int) (y : int) (h1 : term428 x y) : term428 x y.
Proof. exact (h1). Qed.
Lemma lem2326939 (x : int) (y : int) (h1 : term428 x y) : term427 x y.
Proof. exact (proj2 (@lem2326938 x y h1)). Qed.
Lemma lem2326941 (x : int) (y : int) (h1 : term428 x y) : term365.
Proof. exact (proj2 (@lem2326939 x y h1)). Qed.
Lemma lem2326944 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2326945 : term365 = term440.
Proof. exact (@lem2326944 term159 term166). Qed.
Lemma lem2326947 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2326948 : term166 = term171.
Proof. exact (@lem2326947 term57). Qed.
Lemma lem2326950 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2326951 : term159 = term315.
Proof. exact (@lem2326950 (NUMERAL 0)). Qed.
Lemma lem2326952 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2326953 : term441 = term442.
Proof. exact (MK_COMB (@lem2326952) (@lem2326951)). Qed.
Lemma lem2326954 : term440 = term443.
Proof. exact (MK_COMB (@lem2326953) (@lem2326948)). Qed.
Lemma lem2326955 : term444.
Proof. exact (@lem1980026 term159 term56 term166 term56). Qed.
Lemma lem2326957 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326958 : term337 = term338.
Proof. exact (@lem2326957 (NUMERAL 0) term57). Qed.
Lemma lem2326959 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326960 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326961 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326960 h1) (fun h1 : term338 = True => @lem2326959)). Qed.
Lemma lem2326962 : term338 = True.
Proof. exact (EQ_MP (@lem2326961) (@lem2326959)). Qed.
Lemma lem2326963 : term337 = True.
Proof. exact (TRANS (@lem2326958) (@lem2326962)). Qed.
Lemma lem2326964 : True = term337.
Proof. exact (SYM (@lem2326963)). Qed.
Lemma lem2326965 : term337.
Proof. exact (EQ_MP (@lem2326964) (@lem0)). Qed.
Lemma lem2326966 : term445.
Proof. exact (@lem2326955 (@lem2326965)). Qed.
Lemma lem2326968 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2326969 : term337 = term338.
Proof. exact (@lem2326968 (NUMERAL 0) term57). Qed.
Lemma lem2326970 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326971 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2326972 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326971 h1) (fun h1 : term338 = True => @lem2326970)). Qed.
Lemma lem2326973 : term338 = True.
Proof. exact (EQ_MP (@lem2326972) (@lem2326970)). Qed.
Lemma lem2326974 : term337 = True.
Proof. exact (TRANS (@lem2326969) (@lem2326973)). Qed.
Lemma lem2326975 : True = term337.
Proof. exact (SYM (@lem2326974)). Qed.
Lemma lem2326976 : term337.
Proof. exact (EQ_MP (@lem2326975) (@lem0)). Qed.
Lemma lem2326977 : term443 = term446.
Proof. exact (@lem2326966 (@lem2326976)). Qed.
Lemma lem2326979 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2326980 : term174 = term185.
Proof. exact (@lem2326979 term57 term57). Qed.
Lemma lem2326981 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2326982 : term182 = term57.
Proof. exact (EQ_MP (@lem2326981) (@lem940073)). Qed.
Lemma lem2326983 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2326984 : term180 = term56.
Proof. exact (MK_COMB (@lem2326983) (@lem2326982)). Qed.
Lemma lem2326985 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2326986 : term185 = term166.
Proof. exact (MK_COMB (@lem2326985) (@lem2326984)). Qed.
Lemma lem2326987 : term174 = term166.
Proof. exact (TRANS (@lem2326980) (@lem2326986)). Qed.
Lemma lem2326989 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2326990 : term349 = term159.
Proof. exact (@lem2326989 term57). Qed.
Lemma lem2326991 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2326992 : term447 = term441.
Proof. exact (MK_COMB (@lem2326991) (@lem2326990)). Qed.
Lemma lem2326993 : term446 = term440.
Proof. exact (MK_COMB (@lem2326992) (@lem2326987)). Qed.
Lemma lem2326995 (m : nat) (n : nat) : (term448 m n) = (term449 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2326996 : term440 = term450.
Proof. exact (@lem2326995 (NUMERAL 0) term57). Qed.
Lemma lem2326997 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2326998 (h1 : term339 = (BIT1 0)) : (term57 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2326999 : (term339 = (BIT1 0)) = ((term57 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2326998 h1) (fun h1 : (term57 = (NUMERAL 0)) = False => @lem2326997)). Qed.
Lemma lem2327000 : (term57 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2326999) (@lem2326997)). Qed.
Lemma lem2327001 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2327002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2327003 : term451 = (and True).
Proof. exact (MK_COMB (@lem2327002) (@lem2327001)). Qed.
Lemma lem2327004 : term450 = (True /\ False).
Proof. exact (MK_COMB (@lem2327003) (@lem2327000)). Qed.
Lemma lem2327006 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2327007 : term450 = False.
Proof. exact (TRANS (@lem2327004) (@lem2327006)). Qed.
Lemma lem2327008 : term440 = False.
Proof. exact (TRANS (@lem2326996) (@lem2327007)). Qed.
Lemma lem2327009 : term446 = False.
Proof. exact (TRANS (@lem2326993) (@lem2327008)). Qed.
Lemma lem2327010 : term443 = False.
Proof. exact (TRANS (@lem2326977) (@lem2327009)). Qed.
Lemma lem2327011 : term440 = False.
Proof. exact (TRANS (@lem2326954) (@lem2327010)). Qed.
Lemma lem2327012 : term365 = False.
Proof. exact (TRANS (@lem2326945) (@lem2327011)). Qed.
Lemma lem2327013 (x : int) (y : int) (h1 : term428 x y) : False.
Proof. exact (EQ_MP (@lem2327012) (@lem2326941 x y h1)). Qed.
Lemma lem2327014 (x : int) (y : int) (h1 : term430 x y) : False.
Proof. exact (or_elim (@lem2326354 x y h1) (fun h0 : term426 x y => @lem2326937 x y h0) (fun h0 : term428 x y => @lem2327013 x y h0)). Qed.
Lemma lem2327015 (x : int) (y : int) (h1 : term434 x y) : term434 x y.
Proof. exact (h1). Qed.
Lemma lem2327016 (x : int) (y : int) (h1 : term434 x y) : term427 x y.
Proof. exact (proj2 (@lem2327015 x y h1)). Qed.
Lemma lem2327018 (x : int) (y : int) (h1 : term434 x y) : term365.
Proof. exact (proj2 (@lem2327016 x y h1)). Qed.
Lemma lem2327021 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2327022 : term365 = term440.
Proof. exact (@lem2327021 term159 term166). Qed.
Lemma lem2327024 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2327025 : term166 = term171.
Proof. exact (@lem2327024 term57). Qed.
Lemma lem2327027 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2327028 : term159 = term315.
Proof. exact (@lem2327027 (NUMERAL 0)). Qed.
Lemma lem2327029 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2327030 : term441 = term442.
Proof. exact (MK_COMB (@lem2327029) (@lem2327028)). Qed.
Lemma lem2327031 : term440 = term443.
Proof. exact (MK_COMB (@lem2327030) (@lem2327025)). Qed.
Lemma lem2327032 : term444.
Proof. exact (@lem1980026 term159 term56 term166 term56). Qed.
Lemma lem2327034 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2327035 : term337 = term338.
Proof. exact (@lem2327034 (NUMERAL 0) term57). Qed.
Lemma lem2327036 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2327037 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2327038 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2327037 h1) (fun h1 : term338 = True => @lem2327036)). Qed.
Lemma lem2327039 : term338 = True.
Proof. exact (EQ_MP (@lem2327038) (@lem2327036)). Qed.
Lemma lem2327040 : term337 = True.
Proof. exact (TRANS (@lem2327035) (@lem2327039)). Qed.
Lemma lem2327041 : True = term337.
Proof. exact (SYM (@lem2327040)). Qed.
Lemma lem2327042 : term337.
Proof. exact (EQ_MP (@lem2327041) (@lem0)). Qed.
Lemma lem2327043 : term445.
Proof. exact (@lem2327032 (@lem2327042)). Qed.
Lemma lem2327045 (m : nat) (n : nat) : (term336 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2327046 : term337 = term338.
Proof. exact (@lem2327045 (NUMERAL 0) term57). Qed.
Lemma lem2327047 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2327048 (h1 : term339 = (BIT1 0)) : term338 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2327049 : (term339 = (BIT1 0)) = (term338 = True).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2327048 h1) (fun h1 : term338 = True => @lem2327047)). Qed.
Lemma lem2327050 : term338 = True.
Proof. exact (EQ_MP (@lem2327049) (@lem2327047)). Qed.
Lemma lem2327051 : term337 = True.
Proof. exact (TRANS (@lem2327046) (@lem2327050)). Qed.
Lemma lem2327052 : True = term337.
Proof. exact (SYM (@lem2327051)). Qed.
Lemma lem2327053 : term337.
Proof. exact (EQ_MP (@lem2327052) (@lem0)). Qed.
Lemma lem2327054 : term443 = term446.
Proof. exact (@lem2327043 (@lem2327053)). Qed.
Lemma lem2327056 (m : nat) (n : nat) : (term183 m n) = (term184 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2327057 : term174 = term185.
Proof. exact (@lem2327056 term57 term57). Qed.
Lemma lem2327058 : (term181 = (BIT1 0)) = (term182 = term57).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2327059 : term182 = term57.
Proof. exact (EQ_MP (@lem2327058) (@lem940073)). Qed.
Lemma lem2327060 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2327061 : term180 = term56.
Proof. exact (MK_COMB (@lem2327060) (@lem2327059)). Qed.
Lemma lem2327062 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2327063 : term185 = term166.
Proof. exact (MK_COMB (@lem2327062) (@lem2327061)). Qed.
Lemma lem2327064 : term174 = term166.
Proof. exact (TRANS (@lem2327057) (@lem2327063)). Qed.
Lemma lem2327066 (x : nat) : (term350 x) = term159.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2327067 : term349 = term159.
Proof. exact (@lem2327066 term57). Qed.
Lemma lem2327068 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2327069 : term447 = term441.
Proof. exact (MK_COMB (@lem2327068) (@lem2327067)). Qed.
Lemma lem2327070 : term446 = term440.
Proof. exact (MK_COMB (@lem2327069) (@lem2327064)). Qed.
Lemma lem2327072 (m : nat) (n : nat) : (term448 m n) = (term449 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2327073 : term440 = term450.
Proof. exact (@lem2327072 (NUMERAL 0) term57). Qed.
Lemma lem2327074 : term339 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2327075 (h1 : term339 = (BIT1 0)) : (term57 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2327076 : (term339 = (BIT1 0)) = ((term57 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term339 = (BIT1 0) => @lem2327075 h1) (fun h1 : (term57 = (NUMERAL 0)) = False => @lem2327074)). Qed.
Lemma lem2327077 : (term57 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2327076) (@lem2327074)). Qed.
Lemma lem2327078 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2327079 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2327080 : term451 = (and True).
Proof. exact (MK_COMB (@lem2327079) (@lem2327078)). Qed.
Lemma lem2327081 : term450 = (True /\ False).
Proof. exact (MK_COMB (@lem2327080) (@lem2327077)). Qed.
Lemma lem2327083 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2327084 : term450 = False.
Proof. exact (TRANS (@lem2327081) (@lem2327083)). Qed.
Lemma lem2327085 : term440 = False.
Proof. exact (TRANS (@lem2327073) (@lem2327084)). Qed.
Lemma lem2327086 : term446 = False.
Proof. exact (TRANS (@lem2327070) (@lem2327085)). Qed.
Lemma lem2327087 : term443 = False.
Proof. exact (TRANS (@lem2327054) (@lem2327086)). Qed.
Lemma lem2327088 : term440 = False.
Proof. exact (TRANS (@lem2327031) (@lem2327087)). Qed.
Lemma lem2327089 : term365 = False.
Proof. exact (TRANS (@lem2327022) (@lem2327088)). Qed.
Lemma lem2327090 (x : int) (y : int) (h1 : term434 x y) : False.
Proof. exact (EQ_MP (@lem2327089) (@lem2327018 x y h1)). Qed.
Lemma lem2327091 (x : int) (y : int) (h1 : term437 x y) : False.
Proof. exact (or_elim (@lem2326353 x y h1) (fun h0 : term430 x y => @lem2327014 x y h0) (fun h0 : term434 x y => @lem2327090 x y h0)). Qed.
Lemma lem2327092 (x : int) (y : int) (h1 : term439 x y) : False.
Proof. exact (or_elim (@lem2325760 x y h1) (fun h0 : term400 x y => @lem2326352 x y h0) (fun h0 : term437 x y => @lem2327091 x y h0)). Qed.
Lemma lem2327093 (x : int) (y : int) (h1 : term288 x y) : term288 x y.
Proof. exact (h1). Qed.
Lemma lem2327094 (x : int) (y : int) (h1 : term288 x y) : term439 x y.
Proof. exact (EQ_MP (@lem2325759 x y) (@lem2327093 x y h1)). Qed.
Lemma lem2327095 (x : int) (y : int) (h1 : term288 x y) : (term439 x y) = False.
Proof. exact (prop_ext (fun h2 : term439 x y => @lem2327092 x y h2) (fun h2 : False => @lem2327094 x y h1)). Qed.
Lemma lem2327096 (x : int) (y : int) (h1 : term288 x y) : False.
Proof. exact (EQ_MP (@lem2327095 x y h1) (@lem2327094 x y h1)). Qed.
Lemma lem2327097 (x : int) (h1 : term290 x) : term290 x.
Proof. exact (h1). Qed.
Lemma lem2327098 (x : int) (h1 : term290 x) : False.
Proof. exact (ex_elim (@lem2327097 x h1) (fun y : int => fun h0 : term289 x y => @lem2327096 x y h0)). Qed.
Lemma lem2327099 (h1 : term292) : term292.
Proof. exact (h1). Qed.
Lemma lem2327100 (h1 : term292) : False.
Proof. exact (ex_elim (@lem2327099 h1) (fun x : int => fun h0 : term291 x => @lem2327098 x h0)). Qed.
Lemma lem2327101 (h1 : term105) : term105.
Proof. exact (h1). Qed.
Lemma lem2327102 (h1 : term105) : term292.
Proof. exact (EQ_MP (@lem2324726) (@lem2327101 h1)). Qed.
Lemma lem2327103 (h1 : term105) : term292 = False.
Proof. exact (prop_ext (fun h2 : term292 => @lem2327100 h2) (fun h2 : False => @lem2327102 h1)). Qed.
Lemma lem2327104 (h1 : term105) : False.
Proof. exact (EQ_MP (@lem2327103 h1) (@lem2327102 h1)). Qed.
Lemma lem2327105 : term542.
Proof. exact (fun h0 : term105 => @lem2327104 h0). Qed.
Lemma lem2327106 : term543.
Proof. exact (@lem1386578 term544). Qed.
Lemma lem2327109 : term544.
Proof. exact (@lem2327106 (@lem2327105)). Qed.
Lemma lem2327110 : term103 = term14.
Proof. exact (SYM (@lem2323752)). Qed.
Lemma lem2327111 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2327112 : term544 = term0.
Proof. exact (MK_COMB (@lem2327111) (@lem2327110)). Qed.
Lemma lem2327113 : term0.
Proof. exact (EQ_MP (@lem2327112) (@lem2327109)). Qed.
Lemma lem2327114 : term1.
Proof. exact (EQ_MP (@lem2323497) (@lem2327113)). Qed.
